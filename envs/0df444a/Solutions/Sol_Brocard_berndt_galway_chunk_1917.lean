-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1917
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:08:57.773695+00:00
-- url     : https://prove2.me/submissions/42d30810-d369-4a51-94fa-53b177e36378

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 344604316 ≤ n < 344784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 344605566 1250 344604316 344604341
    0x60603061b050903030d02031f1212031e0c050f0c0601170a150f1b08090120031308040305030f0d1104080c09071808060f1f1415040801020d 62
    0xa04003c410004250789001d00c0200c800c4030755001004c0348201614038130280c1c80c000702c10b40e91645140c4a19100e501000d04660803107290900075142d2165900034010070688002150032231141214109043c4094403800c0340100601004012120a00b92004c00506044000764002e000e254900015145400d100c42c00504d540d8010030010400512b0710071100042030f0311040d0210f200350381070510000400b9102001ca41c0c01940002d00140b040d000180e403441401900000c100210b80c0004400d180340d40b41080c070080325030400008800003003520403000e4071303401280300d04c3c142502c0b40d661514661120801104d1801c011480e4088000180100b020309480300016a040c9880c15464581e82d2030100c801c18450140040000c1d00c0c00e1085282801050f01a6250b0141d159280c3c1c2c066100c000a03a04003000c2002c0b10000745500751480c04544440000c801400d48623450294004c3c1850002c0760f0396075002d2119840055076140f150b000d840a41412000141d179040c1c0c45c400e540464443d001e112 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 344606816 1250 344605566 344605577
    0x4080c090702030c0a03030b010512011205010c050a0e130608070e0a0e010605060901030f0f05160305010e0f06100e060406171f09180203010207030509241b0a060603061b 75
    0x860402d407011405454091b498203000c10601104401660103004401240d00880c84080000400f62030381d0188102c0390f0301501c0204040c4000440032240e80c0b00700c040380310100d0b41003210510141095580030100c8a202c1600203141b503200e0141d1030502c60f1507405145841210024070100a5052141c03844240c03100008000e86442c0502041240c090090b055052650b642c41c2140b5030b0070580c210858140d0f410b4020895803a0041b00c2c4074410300d1841550700040c2c03610001141d40c00150b203510b405220b980e8418016a0b46030b20404c100300540118410401c180c00100ca1001d441c0c05000e0070141403507441c0d4091103100700306404601c6800421000b10305402a50143c0b1050040c00000103480851401044400c060090440034000700803000750503600c00100a404d25038814041d02034420115184c0401c41f02e204003000c0704100c0c60b0a90310007003408001903030f03503809640240d0031022502d42c182d94600b04076440e040300700e805039441564004c2e2100100800035540c0814001d20740b45c0d41c20321 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 344608066 1250 344606816 344606827
    0x90309060503010e0a05061c06020315040509120a02030403050a0312050f060d060b042306090106020a030f0e0a18060801060b0a021e03070209090d02010515030606010c150204080c09070203 83
    0x4138102840058415048942e0b1400490b0392600ca00440550300c07809100c000c1c104a26518000c0020f602c100c0342c0c0c4010707800429480e1600d20705801224001c201401c01010204421501c461b0380c1c0c0e014441072015444100300002c001041070243c042030300d001c1d0311003079003558100c0c01181c03c0e0340d402000702d20201c051804026169940c50003183d810340d0440c00024130b404a0802103801009030140c40300b6a0588182a8000502c50428044c4680303820340d08500181da85020030b913a00c0341e242c00000d020680104a841d903284c80340c50382d00c52014004040d2844140d4840740c1c031034207a5000d199228100e4a2352010b2044d0003007401110010032110fa10503141c081c010000075121804508008042040a0450001400c0400c01e954640e50000d026a0203400c040740510380d14003001c400103001d5400c200000d022481000c1c884400c5c1c0c1030142c0500036560b0b8850044504c10381c400c1040f10f01c100c92004030070080d4050310140000c1c01401000300f0a561500c410043d02e00c0c4020103010456104010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 344609316 1250 344608066 344608079
    0x9110616110a0f0801020702040b0306061507051203070e040509070807030212070b0412110307060c141c0c02030c0906180709080102120a140906010b09030a06050103050109030906050301 82
    0x1040c0186400c51180c4100912000c0002d241c40702580c0080046440c50b0b002007903080040d8010444980308580810030910700200381511030074102c0e407140c1d101160802801e420240702c00180340c150302c2003082d071b100d60440507800415500140e0303200b0001010b114000c0050b0405200300b40e000b401031001030030101c0c504800d4980c5c0d1807007404024050300b03040c0a441c0b41c0c8802042003001401c09801142c3d2555110a1146020b01c14400c003903d490b00710a61101c868200440c00708143d404a5807110303001441600d81b08a0840403840300c610600c109603807002450501007020481e20b5207070f558907084103801d004040c0b421a080311303024412189013060203207560720781c0707581c1d40014404a840646940c41e0482134401080d00e070300a0106500001e8044141c2c030040e10024030030403104504000401c40d14500b0100300200301d40700d022070352003a40103020300301c0c0e1000170780686800102151190180c1e942c070001920070a0303008a4050391a508030408041d00018840054411860518195072410320f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 344610566 1250 344609316 344609347
    0x507051003020c0a05030c0706030c08150105120106120f0b0f09060a03080313030809030913020309010f061401020607050304030807200105070210060504060e06090a02090a0603091106 81
    0x109280c85095401000844240650140c9104440440558200c1e2802c0d08120341c582c1d101c0d40e118400c40c0a00c41011920324000d200380c008248d500d81e25030800765210124800c640d503501018505100d170900c06001400603180600d07010b405143e45807105100c80100000580b40704c50310149c0114108a422440c3e03440385814140c00d45405ca54101498880b0804103d083c09150005455420000200140441c2c812000041c4a10a0303481410b0b0340d0381c0e80d401ca500da003e0a65400e910070684220200c0b400c00070380203540c006001c1e038000034640182c400c002c0110b0320f0640c40b1220030043c108980b480340d80c040c49595401851b40c20320a06d9841c01c0d6400401200c0024508001e01c40e20062204401b140b622514040103d5200204541d0030034000107907586241080d050b0003541003500c0480d0340c0c2032a0013803c0440e131001028070903a0f01c815040040301e000c010400502c3c280d0030701c01a0190b03038500d0011002044c035924002014001c8d414041c0e11112400d816501400040100f034071208001c0303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 344611816 1250 344610566 344610569
    0x3060308070b220506101a120a0b030a03021e0703020913030516081b1f051302221a060d0c0e03032205091005010807030908030a0203010302090907030507 68
    0x59444942d0fa00d0301c010b040c40002c0c0c80f120306aa596080020310410a0019001c1d01550005500340c0c0c240b692461610001c0010120000e41c1032014001c01d80c0107c607568880e50000d8604901140900250703000c01d2800c0c0c0242426001a4020001050119110921400020b2403803020b409181e045030085605004041c0c003a01044006000100515200b03000740d91541800c80000f452191150034001c0082d04006000410300d0503048a80d40d4079a400070314844a5520120545012000c9030030f118020800140784c400590804107200300141d40e58007804078071040401008501401320003200b4100d030030641e081d100552010328443e640766034440a4a100b00341411000c6440c4250400c102c40c00d03100c0e0015240c00d403201251804070210ba6801e00440709203051b540310101c2e030f9141c08204a06070f00365655421365034016403d101652040c41081d40c0403115090103e48106644c0d00d60f0b2950b40129070000c41c0550100041c03003185440d505841d0856001e0340100900b40c2180c0300c0e144c592015 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 344613066 1250 344611816 344611823
    0x9140412020a0c030606150305040308062106070903051501050a090e030702040e060a27060c11240114010206150a0b03040f1b21021203031f060306030807 68
    0x80912462880c0c82000b82c0408a80d201e401000f505507240340c903a0103002d203406001c422440034500002007600c40e214141c402c82c1c241c2e03500b5900703840391014000c82e0321081d4003500036a04220150000c0840801001c0c1c0100c0301503440341601491420214108215807000541d0241d501004210319510307401d4407412303a103807000006403110f021300d003051840c0301d2407030300030342207410f220181c030360044046070f02441303000030340d0b802d0000521004a80008100010081c0781c034601000400c8046801640003070030900e55410114101c2c40e81c01440c51412030481811507503880c02c501c80c28030540301001c2c80f41c014004030b50900c00188041001039140c41000342126252031504c4100c4240d41c1e1601c542100511462107055907a007010304080e100b00301681d0701500c0052080341e600520390b017440201c0e802c0300d2410040581007082d194585110074800c44080e07034002010300081ca03410405200031400303601e4052030700149146441da4180c03250398030351288042c1440d2503001c00200300000115818540d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 344614316 1250 344613066 344613083
    0x151503070b1c060e090c040e0c0d1106040503030304080a3b03010b06040906030b06011e0806010519080f0c0a051b0f0d051809060a121104180c091404 66
    0x419101500801040e48401d61405041e814851030000104050f0129002545e05200c6a5012207408e40e4a000d022866504109000340540109800f610410f040e101c0c02803c19190aa941001902e150416101510441c45c0081d45a01c8160400c061001403a15100a070780140340f5200c9030032507002100d024030015080021400f031b6540e1b0a42c09590f0b103010041000d500c541e01c0746003080003094075000484000d401c80c03002c60510740c040e801c0300400c00260611511344600c203c0c02210403603006012607061013070611400480c51204052504020319a80d2507104503c3d0000c0d800219141c05440d0004459080204a0001c0d030710004484030800c0b1a1614014070a80e0500c0b6403400000d00008e1290b405003a041d595501c2d40b08000348a015104548010745445407070810550b0241601c1413075004204202c01c12001620007404412035000701c10002c0f0034482c140114060ba2901c009c2d048000d554054a44104145190882e0280508400802400000340d00451000b2400780c0043c1c10140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 344615566 1250 344614316 344614357
    0x307020708031b060a05010f12060605040504140c15190903020406090509160803190e030d0e120327210601180207110402160203151503070b 62
    0x600802484004211010460355203240d225190366401e0f0700c0f84000d20490007044007044200d800c074010b2034142e82160038150f9010345000804255091030180032200d180d11350300005120f685500c0703440d10032801031500c4403c1c105000c0e000c1c0e0601c03a00015052046a580025140d0308506030b0030365280c1c0f0b210248031201c00d03100201c161f444001e00e510003940203003841c5011500c6030341900928099040c060840d910450040010ba480158900507951140d00074805590100072149201c0800c0905050a020004004012900703121801d0580300200317001c3e100d401daa0341018041a408a19020040c500b0000c011401011000400b02800d9075082c0c61006604c01c1c3e69a42100c20b81c00310507402e84c05d980080c4000d0a51613580910035405012408848650020314900803100200e80c030260185000b803803141084000d410020002000441d8100094010f03102000700320780340068041800c1413454800c1445d91110005040d941c00b0f074101460800280070050141c0e46101c0c1070143c1e4103202c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 344616816 1250 344615566 344615581
    0x1508042003010b090a0906200a050d0209031006031106041a03151309120f12091b0b0d150503100209130c0e03060a0501080d030f02122805190203 64
    0x6003007503c0d180c0c1c0d00c98204801c1c4120050554421007220344106000e0080d0005040c2071390103c003c3c18001920007100300b1800117114840e074024800200c180d8001410185024003080c6041c0d10281a542c0c0641c0c1e0381c03020300611a04041c1c020103404222801480c1c1410289483d164410100c4980001d40c004008180d044108600011100c0300150440300b1407a50131b085000070b4444803a0a8070002d00fa00c0030103558510441e001741140415440d02000d104130302401e0001402607074810340c5d185c0c2c000100f500951b850344840e540213000064802c0d84400400e111001190500300d5180d015000e44002001a510003103000f500e0718809100050b1616800d030301141041c030b00d6190b0100518507100c1c940d030722541c0050080c01000d03010b404403003850392980c1019013201c500380926182c03507200c0d22040c0d6119100303030040c3e0200d00a0300c10240c10496500d030080f02c45682546c0c0301e1215100101d000b007890000c03480040d1107130401c41050243d1b00f82801007403030001c15282d0041d0600e07000800101d60 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 344618066 1250 344616816 344616821
    0x30b0f040606080730082106010c03050304030810080102030a021b03040806040b0406020c03032502071a070c0b04060309050d020102070f0803041b061d011416051504050304150804200301 82
    0x146c000740e0b00382d078403410020001c0c0d80354140360030020038001d44004a6502e5110b400c25031b500c00c1e030684a0a185445985040d6201c0c0303001042d044400c0c111510200e0311090a0014500418100d503001d41c850160400b01940a40d84800c008056401030004000c0e1031400105940c00c90340244c4030002c20384440c20f00e14041e115000c0600c0b11840004140441e84107044411901c9802c1a140d0100241e4480c008a0310f84521380b04071120410b00701e01034060201248020001c00d40304030304001000355140f07031118103908158050300109603618140001d002050129008105c0144001c5140c02e0b0165154140490311080180c1510000b10001c0d0402c00c4080c8000b09150040880c1c1080300d0f034980e801003820020142010f00c03c031500c3d86480d0594050142d08100c4042c0d484628101025030400707071450011710405030b0b514810b40b48840050a103507000240034a01038006156101d04003039405c07101010003c1000d04005540c81000045502c8000c04190070301450080c7c5020225000002d01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 344619316 1250 344618066 344618159
    0xe0102041d19021b03070803040b061c110111070e06030f030a0f0c0212030c0a020423010b030601170403050d0c14030a0c020c040218090a060501021510030b0f0406060807 75
    0x40313038403002460509201c050307009144910712030310150190703556560501c00804102c002c1c8401e00070b00c2150240002e02000c44c000b52802040c0742541040804032038540c500130040d07105007070303d00c1e407081800603030b0500384000210503003070400840c50300d0880c240050215140040f01010001484d80c00c0046507506861940c40b000340360112902d82d4018aa0181ca90341c1602c4206d01c52854500c0300c02d40843d40c10741000c1c4842005981706850ba10380f613400a00c580c4000d0013541040010b038413040d2071445d0005c3e00b5000c1ca000e582d4880d100c20040d56000100c480041080d800c1c4018600300c401c043c10604103d80c0d02420b0341e1000314042000d5007003a480c104090303040947c800e001049a171505503450f90245445402215903c01c01d49070088001d0407602a4000e2174010b8210101d00103481d00b00800c07440d0071035440019070100715580c2d00c03507440d1a2010380f0400c041000005c140f01c24088079000d40740280002c04041c01d03429181100481c40d103401c04d9855101402c0c0c0c0c004e180b4040744600c5000030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 344620566 1250 344619316 344619367
    0x102090d031d060a030b040e1f05130f0b0703050f060d02100908030c0c15031e04110409031d01030c0504170118050705090709060804110607060e0102041d1902 70
    0x50b04c40c403807400007074060601e041c0c04038029850102422484080015402d0600d002141191150420395216401904c001000c42c0f4050b2100c5040c200002e000062151005010300301034121341c28030740d60050035a000680010b9003c406035045c0300042e0f540480c1003400e070794112a41e00c401c00f048982601c07800010746c06009140000704546034080c3e03004c6905075070164100e65210f80c40402c0900514240016076109240b40355000052080e075000303401454000d07000703501d0350b041c4038802d10000c0c054030001102100058060a6080080074074290700e001304c60b03400d0806104c001186203008145c0c2c0107a10034820701e09156a40f240440000b0f40c40154401c0740c12071904108e503814208180e45102500c5443c3c0204107560008024901c00c80c00a02519059992107220391a83c3e1078880042c0d14810410f6400001000400001070481c4920058502c0c1003002503241c44ca00141c12050290080d80c0c0394024884104001c000302d28031041004d2022140c10050721000d4a0f442145c1c505404018003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 344621816 1250 344620566 344620579
    0x503130203100606180b09040c17070215160f082a0408060f13080a0509040c170105010e061903110417010605010c120f02010b06070c050a06020102090d031d 69
    0x70b04200456800910a6031100e855070310325202462180b501001851081140c900703014054132071103261503004044032940c03030b140500c1603851040d0780e0220380c2c00c00e5a8000250b80703c00203401003035241030040b541c0310800d10282c6658000d00240504a4008400100f0030031400ba00090f0b4500503080e400020702c1c0b20801e0000400003140200401c40c1d0050003035040c81d00c03c2c1c6000409121090b1480c2c0e11548a004205400085d03543d103100140c0c01000c280c200344002800014010746846c40385001c0c405a40e500e524810510800c4180f030f8100c103030009410006480f08039111a107070324080302c000188490110304054200d240c100c2c01458405040507441c400000c002640304c02d20707102d002d000c1000324000c1042036510070054a0440b42c4d940700600c80414120f1145081d4014088500412114000455514207002c0000c80c141d00006040740c016003964800e014a0510f5940c007809040140001c40c81c0c12592000601200b002640c0141084120404500d2820082500500e04500035003103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 344623066 1250 344621816 344621833
    0x70530040303030203010503060916060509040f0c0309020a05011e080a020c1e150402151c060801150f0605030c030a02070f03030504020f180a1a03030a0e0306010611030a0503130203 80
    0x8003c1c5d0b000380b04262003441058081042c8080200740b00c0c031184005160740300c5261409e2403d446a1700f090b107249501c00d40d52000b640303049045008000f0340b12000e90700054124124810840c00c5c3e505030300218108070100070013039840c024092040300a124181400d201c2c0d071f0b8600c44494082c5c804c441c40044240900100200c003000c8108050286082c400196000c10041400042102008a501a6010040c0904142041280001001b00d68144078002d03480040c1c903003041003691040e40c0441c0c401ea56547c2c7c03001c5c0284040700c0c04002340800c10f40340c46000e46481c60040180c000a440c10510340000008101032010a504991b00c00c0cac1e011996444801c403d01700900140000c035021390103543c055043c0c010503d000b4011303010011880341404450344032441198010160070000041003201400e00352403d94007007001d0b245400ba01c0c0c0d6624090185a01450705240e010380c0309d0360600480c29040344401c01c001c001d1780c8010100d807501c82c0d200d03640c2081140403010342040194150042c00078 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 344624316 1250 344623066 344623073
    0x20318040b030a121b05030a0c05010f1d0f150402011b05061f0929240307110d0e09060a030218090f150604050603070308120106080c0705300403 64
    0x4084d00465042d1503540440c284603c10390901c000c550b1004005800400000b48124080c0d18252485400351000080e83c3d214040003000722040c0c420b06010106024890101c01e40040100612004003c0701401c002400740ca180d84003864080c10081c10700500c1d0307081003040000390440078005a0010100d50700c50915041301a0b510485400d500c0a00882d13007404560410b041c0262012451118000189604902e0341001d40e940059030060340441c803880c0301c0c04048510340c139055100070703046c070420354a0810700c5c0007038512070424002c0109034101d11603103900160000070f4850366080c103541c034220f6a1740d020700260701038085400095008285000c08402804042412071003a4118403c42d440d07840c003d29801e6a443c880020080b4040f1108006005030810f60041d640141c4050201c49946480340d80d600440d4014881c040d90400104004120507a4040700b007540043c02151003d10b07111031503c1d140d455004a00c0c4000c9000035041e10511700103000d07040b02c6e02e00016285400c1e1103e07208e00d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 344625566 1250 344624316 344624333
    0x3c06140d05010246051614030c011a0904050709020a030212010602030703080709122009130b0c191b0203030408070e060406081e0c19030b090607020318040b030a 71
    0x1d0303c0e07007018034044c4040c00c030316124045100c85052044d110079080168114210074012034a06c401c40781034001c5c61042c59444c1041000e4412200d90318004606034101c0340c1c020040a40200c005445100640240000300e0404202030060321540c210259446000307890a030b0103407164945900d9040900000003400c55808400341500354400e594600c1d40e0b49486104a03405102c07070281218001114142c040003c40d58600c140002400600c07009100e614240010003d0390100c030030783c1e1104d01c1c1c1400f041c10060400481c030ba00003080e5060074101816461b921941550310010001403040302e01201c1405011200c0040320140c2c024110f0782c0e1540c490188940700c14852150b15044201d410204116203440d018807400c5d501450024982c01c0d103030750454945200412203503070707503806410070360420354031210002410011100409001a440d43c640088003410040c41c074a074540114007801880340e4040222442c4900510700030180805080024000303040345080b0903403511407c1b50400c10000c544 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 344626816 1250 344625566 344625637
    0x140c0703021c0f0e0a0306020d0e0708120304351305011103090405042907110604030905010e130f0b10020d0207030b0a3c06140d050102 60
    0x2682940d000d009a005990b82e851000b0240c180461000034810b40142d10600c130342034510304001c1200c101c0c0d03543c0c0c0c4c035400d0490f0300650803204070035190f96529011800400404004200280c01062083c4141d81c010b0114000508010400e040c110003a800a10111107000000c4150180110503581c1030190042e0076400b14065801807a00c1200000b4950b000d4201da6040c1c604d000060b51522003018100002080300420464a00110360801240815111204050074030250042085800c00c0f170f4016020200d0181c0e0240e29911060400001952121209049803400e08003001c0c030800704800140602c039580320f4041e1035450710480140b00803983d04090035900042c1ca8480a451000004036211402890140c0240c0d000302d03001c1000441004000351300101c80f150000d00900c882d005000c10210b0340d03030480010b1005009504400030101e90110300e0b001d443c08200080ca01c2c003140c51248000c41c000c0703d071007502040c5c284014041c084d01215582214002132400c84114102400c5080002c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 344628066 1250 344626816 344626823
    0x2040608030c06091b0604030b0a1107030302070606050a0b090f0301060b070318050102070515030a1e0b0a0905010510050f07020301090c03030e010206040b0c0307200a1e0b0408070501140c07 84
    0x19501c900040704465182e02031711781006406185031034115140c2c0103040c51b014061110b001c0c1da9540810225030881c01030400d142c480e94015035202c4543c03d1140c2070b100a030700701c0780c41110311240070003d540c0010100c544e900d605498440c078004520000030f0050100354448019803200140020405502010070301d200e42075042049401503e030b1004990f104030038085c01d0f41000075280b000c9107021b04000910b512503440f440126200328119925080c9815403242000b02c9903e4002e041614600f03000480d018118956042080350314020008240211651044092020010703004442d00b85540450710314580190080c00368082c10700d08120122198401900003036401f540f5030318550704c00b2074103a000d039401960038405511400f0a0403402c0d48081d240300140a0324182d6401224074a0041e541c03140d0030600a48404242d9042c404a29010f01c240c03480c0e0030582042c0c2e40e001441801c150303600150814134040e00c6002d40d14084ac01440c41030182c15172220840100080f8081400061074031920 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 344629316 1250 344628066 344628073
    0x150a0513060f14040612021c170f03090105070309120c0f021512011a0a11030d05190e0a1a070c0b09101a030a02100320130503070b0307080402040608030c0609 70
    0x1b650950301414180c1020001c2d03110035081c820b1018048940316519109010fa4021140c1000041e02e40040398810309050700e04070b20100c10040701c26020b00c02c55501c48000d04041c014041d103035132001c000300c480054132000d00c0185130020090003034005c5103c3c42e0541c05080003025200d0b40140d0841d54004d958440c0e0f504104100202c0c049480318095400640000c0c03503a07091425040e415102d010021990841c83d01c0305100202d0f6490440c000c55008401c182c001e00f10404584007010305454000305049a19844942500000340540004042d83d440c48a6590001d0320b540804448164190700c1c003070013070340e4188140800e4480c0803d400c11502104041044541501210360100340181503440b64540c20100c001005404c0607d00001c3c0201503146c0000e54000349680035100c0c118039080780d00c10040220f40b0042c0040580c55107006440110b004022151400c0550701c16440020901c0081154020200e01192141d0304a0303c007a24220301926207030b00f03a0008103a42d07070340c0490b01803c0c0c1c0d20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 344630566 1250 344629316 344629319
    0x30b07020d140f09061b060112051e0a0c060f0905010c0210080403050c0109140706090e13021801030302160e132d030512150a0513060f140406 63
    0x14000210704846031000d031681a8903030402c1c203045045400c04082411050300400404016540f03c1c1c0051601c0c1c41140b106803c01400740c621146000016040340502100c1803030b042000c41c2c0b00180400b6001e0709205814805c80900c440300381000704000e002080800d03d1000410b90a070410901c80310414680d440c05401a606e40c0111640c45c90b420020f034102c01c4002d40b8a100520032903205510900904103a4981001404606d00f1507107160020703074110381170144072000c85c0e400b8410031004210601d04a0909410005102d0180030b0203004200010a104218011522900002c1658450301d80751045d5540c0d5030708001e0b484100e070440c00820300c040716201213500d9505031400c2d8080c2500c142c4480c0c06e00420340e00c3d402e101d080c4104000c80780c1580c1d100c6a6900703e52903c10240c891080c1c2d83c958407251014100c490036000603215540b0300c3c050340004405c43d154660b8003000c66108980f0f000b01da280c030b41d05c55001441036421003e9194a0300d58049015070f00004510b00c4594192010480c19 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 344631816 1250 344630566 344630581
    0x512070321020a171b041403060109090803011e091a011b1707021f03060602060903030601021209010c060e0309010e0a05090604021b010608060a0506010c030f0819090c030b 76
    0x344120000e803404942d00740000c00402a24502c0190f101d041644d140c0c4103001003150710303010f540003584885842c0e81f401d06411518201806014014001c0d04000d0000c684982c1da5580b0390302050240844001d40c2d0700340300d1000201c81c0080030003058843c008010381410001b0782c12030000c041891a0201d6a85c41d8048200504581c840401640110b420a01100e03052454085940540001d0f03a11100958480742c003a0324441003600c01d90341c4ca8030009107052034040007038201a030050150b42603800600c02c0100c1a6001b1405c940c0c0040401d140964034003086006a516a81c000300141c0220310f41910001c51b604c00000802c1940d0090702e912610300c2c100c4040046090050041c56003052811011540340c1c20603070040d10055001e0f418801000380800c2140342143c2e9154070103000c660007441802000b0981c1d2040e9074105200b86004040c00300581c402030044881c60078000308109900000a0341c8441c0c504480c2003d801e2500c042c004440b0f039042c0b5011140d424041036030700401c2c0d400801c10341c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 344633066 1250 344631816 344631821
    0xa0306060c0b0a02030a020702060d090204060501050c070e07120c2012092709060f10120f020a051207080105090c01020709090602070b0406020c1506030a0f0512070321 74
    0x100795000807800225901c00034410083d40001c1d001d00780080d004e002c0d040050380c0e100e026002d42c072280b60700025800841e0042200340c5a5950200d8148081004000180080855418255013981c0c960031203c0e15401411111420089107601009151201e2908100e910003411507440314031052220b600b060b0981401e4075001d0020702240e01183c04c0015901d1800e01e8080b051243c01e83c4849080381c4a183d2000e0500490b04445c0c2c60070a4200c8810401032945010701150000d09a001d8042c0050401851649251034610f019007122104650141190344a00845024110140022010b940581c1015580e000c183c0a0301603527500f007400007600d039600041c86007076002c0305074002c0c2580c500d0400345070010302107084113035601c80c0c08120460108100d012094000c520498006980e070b02c08621003420080c441024109500b0040180b00b03059500082d0700030344d150006a070a01c1c40c00325142c0319241c00445d1100b444e400c036011071490300b80354001c200030240140d0300700c0354610600e200044504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 344634316 1250 344633066 344633087
    0xf020c071208041205031b0c0d15060302060d0204030519050606011101020d0203100501170106231c02091c080d050c1605012004030b04020906130c03020a030606 71
    0x5a20010080105480c058004140940140c03000b03490030b40c494209100c19509024152078562000840140301c01d924030040e0101001d100140820f8400c000c0011140076070b0010107051000c1c62503044545103502e900000c011680101503641c0c680c4000980c0c4042c0d0054442035a490240031303540040c9415003c01d10302e4081d4800301605071a502c900c015601140c52400e1580199424800e0803a49107081c0300450042650007691700714286040001001014101c6070161103285c46001040000e82050a070b01c440c0c80d84a180c490b42c0c1c480c0c40c1040e446c40c050720000200d13919440c10210202881640109071000068900e50000103056603013801d00300410718002c14143c002c00119000110b154041c1d6041404007900a01c1c019603e80f612601090402096407a039569806015010420307002d4071102c0b28802003401c0c00e0500d1504c6107005010f000300042e000b0fa1603d00014101c0d611001c41c1800c143c0100000c0050141024008009410408507038001c030b850700502044081c000c448191 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 344635566 1250 344634316 344634337
    0x30f040b0910020a020c101106221b090e060c030103060b060720210c1003021303061a06090904020d032a0501050c0a12022b0c030f02 59
    0x19156035a0345400303040010406502409042480003500c04540002c02211019078000c11061240780201b0a018070800700e20340601902014102039540d0200b08190300000503110030a0484100c01511010210404010204622401071032a1041010480c40a59014020812070717808c840740e80035903c42064840004102c01480100006060b54003c162449800b80c24503050942035a80c0c01d810b00c8074901d8000c00f817000d00c8a440c43d2414001e0840316448402d9602c4484240740300d5109448400c0b121070240212a08828020343e075000b601280c0c100c840348040030700b034103640c1c0c1400402020a008003502c07080298520002c03c0c0340100559031401c1004080e03071401d489030740c00c00060703407a00380d0110305001d0380c034109180f019170101b800300b80301700484610118540c0500e009401c40c0c200a02e408054803050219050456011071000300d0405400401650740780201c40100590503141c000728038104900001301810b0510307070014000c03102c05850034083d060031100381105034003840c1c100c1c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 344636816 1250 344635566 344635591
    0x10606080c03070e040e0c0f0102030922020c191704030b01120606030602160308060306011409070207090f020a0f02070b16020a09050f090d090312080a18030e0f040203 74
    0x34030700714490401590042618102080c406040034081000e8854040c3c0788011030b0000001030105061503003460004040910203145000705040008510315143c0c60034840011900705200c00000d100d134111034881c443c8400f100c280c1c03800740c480082ca4607002c900031541036100b0710440e40c14103680015201901e601c03030881d18480c2c2c2850300200743c1d4011000c05640040c0c40c1c1100001242c0c852006080d82144c0d1903c0700030690342400c001e0220640035080c14003d60001004200c0c82c1d0310f00e500801c903908202d941400a455616041345400117981203c1007440c070b0f004c0d0341309030301200fa401440311031056181c4503060b01c0200300503030311003059200740350b030050013008602d40300c1c0e400174800070300244000d15408080340c4604030760045883c01c030b17441701c0441015030902110050800200c00c218806283c07440b80390b030450799851520546a48041d0030b022a1724082803e000c0943c0003150381d80b4404003000990b07105801c00616045082001a0023491502c191040b2401c06000b103d101e42c2549480c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 344638066 1250 344636816 344636821
    0x10608060f030109170a090503120a140d0501060c12050c0601210c0e0103061811060a140705070e010611071502120c060f01090c02150403020304170f06010801060608 73
    0x188000701205101d5194195610b4454a001a440c00403244007090258003640d103802000202030084800d1b0303080740d07103e68084d8000c8480c120f0b42504854105c412803038001ca081d400d600007855580500050194484c1c00c24001103110307640b020301203100c140602051070403a40d2100055800d80b24a064400300c42d0003480c01400300030040010940c000913480c0700d82120015503100c003520010306410070054940c3e114010030902c94140110119000d4805070490b0054140c0c0ea07040250041e580c0301800760314042008542240103180c0c84090310558120540d0b80e10700d1b8034004d070702c41da00c4d40186001c0e402c22900100e80c6500c50016440c524070301000508405091060529514941d14041411071042550002440303120310080c0885a036520001d10250900c0c4e00e5010002005030452080c40f0300e804401c0039069030014800d80300d050b052250f4852500e5606080b030961040360400f0301c289180e0342044958041c006181640c8410600030f4075590398075000040d0a0f644184111800220942c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 344639316 1250 344638066 344638069
    0x10513050c010806061e090f0102030f0412081905091305090709020f0405270906071d010c06020a050703020f030a020d110c0d060603030e0a0f17010b03061807090501060806 76
    0x1140342c4c120100401d030a0070300f4203508403045001402d4401410b0064042100302650030101d8410700324000074006942000404000c40000d8000e6118002c1060344a1040000b80040c100c226076050004134040d140c0341d400a1400382695008180c120700494406808550040c104e1089900415622006c0e045240c0350241c940d0103900400705800c00030008000c00545540c03030344252040c0c0c40324440405c5004500a0000481c400003c24041ca1034109400300103000390b100d5a400f03403290300401d00040254a00b80101d4210060f403400070b10540c80000c48405e03841c0c000c00039020f000e109a08651749500c1d600c0c0060740b41d0254248520240c2c5c0449803840c01d280c040c0e2a100a4040345600f110f00d07103800b120008a003840680c4048d20000da072000244241540800451042c1c0415500300314424034040300710380d401c012407040700c0d4458950f85c0000340540084d0048402010000c003120010300340100e500b41c11101c5558462801d02c9807510001364000c481c020076040761680e40318040c0300d5803034a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 344640566 1250 344639316 344639327
    0xb01030b240105130e010602060702150702120a0c121d0303070f08091503040c0f050102061513090f05070609151b0804031b0920030c07060b0a0b0c010513050c01 71
    0x50130480090350902c0105075081003404943c0201440d50060080d03043c0110301070300746001c02388030140c440c0010040009080e0002107406c01c01c110103507060f60319000d07020104c50b10002d8407401010b03000948c03d0704049590041007a0f1703040c00815101c60310626485c04150b0740e48a1000c008100150504881010400b10740291130b07000d0002d804004100d031050499000e907802140c080344e04101b1407205004506607203c5281c003a000030300003041c803820700581c0d0170045000300744080d102d005c500c1e64104005110341c00a48140d98808a075110800e05890310b261038016900548002032041c10000810584001c1c0c072581c4a8500d494030745248000d07030b00b4540e001c01c40c0d06042d5210541004000700140c0c0760010002d44d503c203095075001480c04c01c1040c0060701c5070180386c2c60325124090195103000c0f03014021641c0010b1085041c5a81b10b6007031608901504c4082c800f0780e400b8420a00002c0c1c4074484100420101c40030740020000f03a50340514006003031000840c094807076030004240c0c02c1c080d4042e1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 344641816 1250 344640566 344640577
    0x170a17060d14030a080105180a1a0301020f0d0b09010f030f030207031202010b03150c0d1a060a0801080c0a0b1c110301080f0708010c0f180906030b01030b240105 71
    0xe016911a0074640d292502a85164604100035601c0000c0040ba5140c0c03012621340501401c550520751442070800300e20400708060318410700c55640d0000c1e02c2d402040384011030581d10001d00259102c46032602071300201c0d00400c2d00f0722a4a030a05050300710034540400c4140c142d5041d144000c203100c0c00c64a80301141c9a00c02c1c0d0440c1036114048000c40030074403242c1d10080d040125800400c10007a014180750411640e494620007841e45013050050f60182c000540b19508281840003c417079500e92080310070404d09075141c6402100014070421119840107416041e02e0540e412100405400e509100401d48031b0300c50700001c60720510080d08003210f850405c1c80200c101c141d000c0788040312200c01c11250343c07003a40010002d0780800140c0c05c00c0d21080c0401c0c1700401002c0f0082064606004020b0308080c41ca001160401110301300071400c10401852800140807124010032000d502c0e803614100143e028001030791102206800035800b10031950710307541c02c0c078243c0c56514000c0006000640d03454011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 344643066 1250 344641816 344641819
    0x40b0705150a0603050f0c0102030d0c0e12011b0c050a02010c0812190c02030c060a32010501080108012901030204050418170301241713170a1706 64
    0x6900607500744030800d404650050840c940001202e41c80c61500518260706c01110040c1130700700307070282c6d01c96a0700442611000310f9401f10100d0510025081161003203802032002c0d80c0300c0c2000032241482d1074154030006034296100300301d24510b41c902d801503030b011000440c000c12551102c0300940065220701d020700065032040d07400c241483c0b521866603444007000c0301d070780c28402e82d04400d000c1a0300442c0030310305154a59001861624901440c00b907115800103007401c0501e85c40d005400b030342e02c802080406030300c0001c00d0742ca140c01d085045e20342d0307607200c081c403440740060905000441c03481c134103100b00140c90303004242d41c4102120360010f810501e14100e108030305043d401d20000070b9948480c081d40a180780768055640e010b22145c5082e405e02100f49042591480040c401030000c2142e900505980250181da40450040881e004551052a45262241c0a04008203200b4140520301000d0009440b0313020b80303540782468000401032130065180c00b07000240e00c0f440320300f007040e29940d02a801620 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 344644316 1250 344643066 344643073
    0x4060507170a0c0c140d080304020102030c030c07240c110f0301110903010f02030603030418020d06030f03090608090705060d0e120d0b100f030b010201090605010b070605010b0f040b0705 82
    0xc0103680c9000c26007052502d100458244081e2104100651285030090060501003808240c800343c04900003500c9090002c01070034001010a09581c000c000380d800250104045940d80c60188541a8840d4031a110b039041ea032108903103411850b003102181150f001c40b565610b60b01d03442e80c0d48601841d8054002540e400c545800807000c840c1d1402c0c00741001e01d503c000680c0b0750710510082407600b10340f50240074a44040c81403040c00003d90700401103c044034000030081500c00242040c0c10b00911070070059260607440c0c0f20001003004022040a240e050190704c0c1c03800d10347c0e600c0030f00780c8416508603008040ca4008000501540c60b103000500192007034418000b0301441c05400c4640360524941c1c042c00d000501141903508544036014084203454150380f10402c8409940d0050203c6000030101000e06485550400d0107034400d5210b1070340141c00401c107202c107503503464200b44140c1c05103105454031400d01d8004a0005051811105e03009000040180f6240ca014001382d040c0d0072404041b80d0500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 344645566 1250 344644316 344644343
    0x3171c0914060a150e040201020a1716120206091f0e07031a0105031905030a080618010f0602190c05062b02030a3804020d020d05070f020f0304060507 66
    0x58042240600c2000c010f40c001500e40c08003000d682107040c007944461041c400074010400180d0380850405800c95001060301c642c280c4117000c5031400e02440761003014540d154101e4400303015003080c18071440d00c001d400b42d42a945603880419141c0c2110412a003400601664108800143da40568a85129201501d0303500303840740e44005100c0c01401d00300b0101d280d1080180b20a280c1404892420030460001840a50352a80c1d404c0d228083d00c000c4c5000c0c00090b0b400654076807240c1d008000c1c841d00000d44002c003986c60f00c014440c0304106024000041c80b0301c405443c0c9035000c0c02641c0c100e841d00015044c02c442e140400308003060f4010a121401c0c081240c2000041082c0b00c07411911000c490a009a101d14150420b0300449503910001c07490001c40210805000003191881d040c00c0080071041e00440c964040420040d01c01d80c0c1d0701820032440012101324200469016070701683e2143d0300c0040d201d00070803081380e030b4042c03040e042d46c032710b4104000c00c00c2254000c0740141801480344d1010007850 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 344646816 1250 344645566 344645603
    0xb15090102030412060f0e2b030e01020a180b0c030304150b0904050105061302180108040507150c0611093d0c032703030c1505070903171c09 62
    0x40813a4200d490f1740d10342d000f81410280740e005a5004011b004020100340c0000c075a441d0a40c041d0b8000540300c00c2800c0d10042c0d40c00d100c2d800500c080780f11070000355980d10203044001c143c8407900845d41b11600e00031801042c141c04c0300f402c803200084070380e00131342c01c40d2541d8440380c481e230445d030340c01d107251550310019070f1a282c403080324903445a8014400000c60b07190110074000c0207040103c1c40100603104203c0101c1c40c0076001c114141459007860407100030b50340c80c034211b8500803154224080184030034540c10540780e401141c000380c0d644100303801d200c0154100c00490750350080a00d425880050700a9248201d0816500f0041000c0d0743c840090000818807041d040011181400310000703240b2401c060b05050b008a440c00d400d071210b80204c2031004103003601036035060140c0401002c000c4511284018400e10356446900d5600240007000141001103000d00b21102d10310045800e05041030320b0692660b02038054a400002e20b405849080403a5007049000f091079690484403c1c04021040110 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 344648066 1250 344646816 344646839
    0xa0e1804080a170c04060c02030a05030c01061a09100f12090c050103050907081c021f022802121615020c0c0909120a20070501120b150901020304 64
    0x8600601d0041c1da11805580c0080142020328080007480030380f403091080c8201038404540850b015460110071000b240c3c40000d042a81c0e00001400c503200102c0c0c41c00c50088198420300888a810342154030800f400303121491140140c1c1c1e44180d203c600820704c02c1c05513005164800800c0800e1030940c0710007044030f64940444415280959011104c0728042c040e81d6014428a5013004045004050a501d0b000c80503907240301030043c0d88082c10340b000c49a020180208000000f410802220740c0103c048108148001d42002002c501c602c0313502d809040b490440004007050f17028495024181d113905e4905003011551001600d0740301280c00d1b03000403002c5040c03100f03441a442120b8502607642c08a5080d8603240603109102c40b031062a140d000d1140c000760001d004041c01081d0703294243c9076810000165010203480b610001c1c1c0ca00f100e604144501c1c0045002029503400362605400d0210320500307203084806888060b42c0011031824882c0000100c00060300700c100052040780d181c60385070a20b450784c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 344649316 1250 344648066 344648071
    0xe07030f0f03030b0405090c01050c10050f0709060c0b160507120305040311011a0f0316060e030607030509030a030b0a0816230d030c020a210506010602070b0a0e18 72
    0x404041e0880c5100815500d4041d80807941c200b185c050217241440e83d0100d868488004003d414400c000440c003890150070b1100e000700400b01c0400304004d1400c0e1100e00e1066030304407042400a405180d01084550040c910b2038034841d00115100305694070301d11000da0b0864100075010074860305000c5640042c1034541483c8107501a40d40204543c1001d00d0302070b200300d00c28800702440d40d0509030085500e41c83c080100780800402c8502c09580160f110100e4108118200d0003110401d4072800400c80e03903088801503008420940844400347c0e69004100c044030415640002c0ea030b0001c00413001070f00d2007a0802115500010844400382d0341d11103000d072500081e0307402e40480030740c810804c00c9022007101c8120099010100300c94440f006041c00201419a030100c0103050040722031010040d9118034036a0301c0038281c80380d0140c4145032400b070030941003c100f003012200c501c5904008079119202140d01c9080328041544036003008888c240c01d8a0109046010b59088203d1000041d40340104402450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 344650566 1250 344649316 344649323
    0x305090a0b0d1b0509010c02040b0306040515090a21021513110f060a140702030a0f05060a06080717010e0d0c050d170103060e031605060115020a150e07030f 69
    0x241d0b40c2000d44849420b5540059044429041010030307100f00b42c0e005004c41d040f101007441e01807440780c0c680c4001401003c8902038142c052142c0700c10001085400200c1d4040101e910030044410b0b517901c000700340d613462100002040c0c2000090324a030b0b003c8250840c22154141801690310380c04012034140c03c0c40c1401c46141c44140000c90406007840308003032500c130001c1015103d000035510071001291301031003038680e14010041203034803003070300364440c0001d41c0c0c0300d1503009090f6484a40c1d10305250301d04000000c01640d0078094140402c00c0c0447e82c1c407030b040031100b800c0f016080c0c0314038100c01002c0c50915454511b205540381d5664032345000003440b211b145800661034101c115240b90038540d260440c40300401050001c96000600c103c0000d00d42c00303044950050005c0b400c00343c00708403141180290980d40c58251081c010300b41c1003010103e500d0b8182c3c6e80b40c4d0003131960704100030801c83e61920010000380008582083c4511402c0480c4c004190441c3e0800482e12040c0d9660b440e48106000200c0a8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 344651816 1250 344650566 344650589
    0x506240f03150d1b05010c0803010509130c15110a0c03060f0e0f160b0a0e0415080102030a050a0e0d05180d05061311090c0d0c09090608010608010b01020105220305090a 74
    0x804c80141400800300c0549030a1820802d0907819a032141450b1006019103813089031008005200c0d00142c455040c20703071380e10400000303aa030f0b510341c00c0c01001014080240b011903420700220b0303044140043c8001c84039400c6840c1542943c40d6880e04801071500c2114242d0035502c461031805c089204020f020142d0101400909014006a00000f40e004041e004007020301010480110701c950302030743d00eaa448104032400601e000d001c661108403094240c2c4034072040d50000c402c21001d44056840030384940d08c1300c04140003203e0f00c4215641c5684c0d950301e210740411402c1c00200900c1c084c9140c54100b041c0d024003c40304040454031494038014044400c1240311444582403003c001b405144105464000e0360b03400102c0c1030090002615028480715802d40640e00d0340b800032240d215804000c014034803404104901520b48400703602a220350b00a2039615800d090b044102540705104107403140c03107807411038028070140c00401111400c0c42c2d8416410000180850b201a0340d805100318018490007006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 344653066 1250 344651816 344651843
    0x131202040c0c030c030806060d06060305060102010b0108010602031c0605090c0304060e1603080a0e06040602071a070b0c0309010f020d1b0c230703150506240f03150d 73
    0x1008180d56481d5400410400ca4007000000240c00040c0c902c022980b5051000700c2c1e6560901003501800ba030500c1503042420034400040c03158042d1300060181e03c00303900074414401ca0900544c2c45c0c45c428070450005a104106003c240c03c0e0742d200600d403040f882800070402542d9500050036400041d50500000d09000040c002004800d20a020801d60400046e1510010040c0c0040300d01d419840090200c0d03030002008101c4a101c1d4803191141400181480d44450711020300941d22902e03405081c0c402501d042030701451040240540c1c00070340e0b200e064841d07240d84442d203c901640000e05414025900e41e10046a0034100d8000f078001204241e1000076072a000200e4280035810b403c0071a018815203011460204101110f15404116060490400d0002007241c25182110583c0003070000010740903030704111031058014600860301250020101d102d48155442030b4020f182d80b040c2391640400c9000d0b0040700c850301039035104a611000c0001041c001d0701007034074150205000c5808030070715001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 344654316 1250 344653066 344653069
    0x40209130f02130909080a0c06021207020309120712020f0d0f0b060a0509070f0509030a0c0807080609120403060c0e0d0b01030606060228050304080313141512040305131202 76
    0xf8580300400b007940c0c0030b00001c4240e4481078854400c141044040080040c03501702030011076012030b2500d5403003c0303400c90b2030300e09603500030344a40040601d0351041904061030320140c03e00003410000c1d41d190098040c240d01e102d50030001800ca03941001034010f04074a0451000c101a508100b40749030040c0d480902524103001007000d02c040302d4100b44d01c60f490610a0248113540440740d24070701d18041c1082c6603104e5000c40084d00c0c218030388000030030100000c000412944030120303c9400b216a00303070071142d603a10341c0e4070141d450b4908681c58013200e982c02d0004001049503034201c5041e40001e030030a181d181d0410400b00c2d0242c0316090b025249050391b80b0040013009802c0c0b198200078450740c8041c10201d81001480c554148240c68a01d952410304002081030107414011134004014000450340e4600041a080e000310181c0e1055403450f0150000c01082d9040000c1e2008000d4550404c42d840c100085000001072080030304241c040100a00070301c0032020030703501c01c13030040c282c2055022845044c510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 344655566 1250 344654316 344654347
    0xe0f0103061103010305062e032409020108041511070f0c05031f0e10020307020f0733031e1e090b0106230d05041b0b0306040209130f02 60
    0x110b0001408401c2004001088001c00c0141e00700381c080d220034842c0192801d25000e80444c2c81007413550304008290010400c050414042d400c40c0224030103541005e0070300145011111448000790100d020400014001482c40c00e00c5002c40c010f03a42c1c002442000c60b25840d01a0704121b0007210224192100742040c00701c00d0926200806088004000c804910000e181e041c682540c1e141040c0b60700c1e4000c0003000003051004100151250808646034501450000e41d1007054880c01002c0e80a8040046403080301c012604000e01350b10141d10700002e43c001082101402c800b18000101691440c1c0b41d2107280c0340012440503410014008660401400058410090007619281d06103151007800c0c0002290424410b0454045040c0a08800749005056501c0e4400c0300d4040048a800601035203250203a45c030907400ba501400b45400905840b8100c00c03418046400703890400b07003081c800540949802d800500301004e01030426810308030005880416506900071206101d07802150302042c15a81c82e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 344656816 1250 344655566 344655581
    0x3030f03051609060c11131b030e0a02091509070306170106080a030320032401021f0b030c030102040b0307022406090402010c051014130b16090e0f010306 68
    0x40c41010940c50110b0043c1016103e4400c0f0030601181500860601210201032050008090a00000070006101200c01441c107a5640c064054251f0154a0041e00c64800c01214201d5040145a0105a80c007004008000103080d0443c1080c044030381410f5403504005540281c03456207000c2100c60a2100c640e00e00e030b0310604025240d038544041040b00b0b290018080c2003054150034000351000e010030104404c09071501010304a050000203100b408040120700082042200045560000e00d2800498480d0141031100c880c443c2c0310155031180b0501680a00580e040080407140c4200303211021a003684c00681c0011400c00000c810000c0c0e03035406001d086032140a51007a291146014100d80c0381d0300b480601002d002c0d01c2114009000c59004e2a81c204c02183c005045035480300740740c03402c000903100040d480050340610001003a81c16400e0780041c0040795209180003420395a0b114128400c145c000401030400030745800010302d000410840b54028204244c1204541d03056050010035100345 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 344658066 1250 344656816 344656831
    0x60e0d150e0106060f0e060f13151d090a0518010e03040518040206190c06140403030b060915281d0603010e130212030a03020405090901050105031207061503030f0305 73
    0x89049840c0250302c180210b0038886c08031201a25003d224412291a004038594064a488501030100304040f5515044151400964036620f42000c03400c01d4240000c18061000d0b008401980401c2c80c454042d040745074060f40c0015038461503840c42000750f0070364081c141410005d80001805000307e0074440301c0e4a4461030842c4240466040503804144288101200b10810810701911841100c1c82002c2044d50181c0100e030070301400d0420003110000d01425501100480d01e0001e2003401c9040003c252600b2802c01040081d411000304061840b950040d1420b490362403242244000c0c12591440c184a6000e03580d40302d00034038030f00e140410810f20b201c19149114510070b1004206900c3c1c50107a2540c0000310f03860003a001c214a20120710fa0543d1201401103a00001c103200c0846541607024100305d035030440e00030f4500d8484254131400c0b00c4d030a010b4650180c0007a01c2074061401140000e18283d88100d000003030b8441c801c40202081c28681d00201c0002d15003494012440f0750501805400014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 344659316 1250 344658066 344658077
    0x110d050112030206040209130f03121404032a02040509010902120f060a0b010519030209030717071e0b070501020306040f0212060108130b09030a02160f060e0d150e010606 75
    0x441d61000f83d980e000c01440280728426032000a810100030051114425074001c1094000321010701e0007400e078907031101c440c4100d60700d001d1119410600014080340a141c054980b844000d0403280801490b10002c180501d100080019000060300c60744101840740c1356250002640c01e59510402c20064104036164038a68883d8000702081c1c02c001c0b40b1aa080500c1113400511401d07000d0041c0c0351350040d506001e400c41c00c48400426216015002070054220423401d840915440b280100c50302c05445c03400e07821961100c0401d0004c05003488041c8507806011003440c9030b182c0c1c1c0d0b03407005c251a405000c003101c01d83d4003c4240507180c02c00e0b00803411781d07800c4090150304000807000c186601c400f004107242d040005c1900800c0078000d000e000785d026a6042194519145810004180e8951040715008014424910341c0b031100d4114a841c182554078070780146600900e8080c0403104003000e440e200e584141560907070070008041c0b9000554082c070b030f1280411900070301c81c981400c42d074840d403040c1c05122 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 344660566 1250 344659316 344659349
    0x4170405060c0a02030f1b040f0b0d0c030501050c13030b060307150c0b130b070f11030a0305010314010501080714011b06090605160212030a0e060702071e06080a0e010906110d0501 79
    0x48500c800060301141623800194000b5602081005050b918840c9504032200400560900500740c1c04c010980703000e00000d100b151942d0003929018440e0b003600740c3c40c2404200c402c0c000640d80081c442d811000050480303a4454540562140400b83c0c01c0309007001c04c514481d000100200e10040e507501091540320001401030310385400500244c010325010400810081c10b414003801480101240c00300c9500303d944441403a440035001b41020b010a42d0b00006820002043c02014059a030503194011301400200b403a04005005840d100520141400541100e000350581114062540240904d030089880926030821904441014003001004200003060000550300000c1818961a84030507042c2e60b07643c0d03100140020704200301c1010040c0100c0e01484441075001580005517030b04900c1d00c0d641d04500c07650034030184200f44151000f2030407180000302c10105a0740315032001d542003400481c642d0010340c4c43c1400c035580910340400c4410041082e910000c003a00c075183c0034041034121081e541 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 344661816 1250 344660566 344660593
    0x1e07030c020f18190e03161e060c0504090f060522020c03160308070302041406030606120f15030708120702031011072904170405060c0a02030f 63
    0x1003122001a0003882c180701541e003030751540c1c42d4980fa942040011480e2900748054068040014200d5000055051100100000381c0100460307181000060000120b100c45580300d080c1d01e442100e40903201c25080381ca15001c40c00c507018480440790242e80d0596602c0c140f200704070443d40d18510f0848880e1500005105980721801d41026002c03908840c0802d541c0c01c0480003010784119000b01300c0d2400045a1003c1080c5484034201d503c80c800d890300c078402d9440f82821030480c0942d00c87c002e00c02c007861040c2002814180c0c01503400840c06041d0a280a000041d0169601c50969a0201c80b408207810040507401014003540e00c0c040890141081d9840c0c8941155128008031020a05100004031354045603410030086101c00e2103038005000da002c0402500940390001c48098400ba4171a070011440c2d01041540348a0a80700480300c18859101c64a41c940703103040141032000070400400c800306059540c1005005032204a000030310124030240305140c28290a0520400f86900c00748035550003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 344663066 1250 344661816 344661827
    0x1501030602031017010c2a0321050708160201151a090a27090201050a110102160b043c02030a020411030615030c1206040914031e0703 59
    0x1100d4005001603240d4642d98400300050b4059485980580c941c010000d20248040d04800b040c001107440d90080c80d102d2100341c0c4d002c00680c03a05c0e082d03201c64100d03200c0002070058070203040504141c002d84054202039040c140840d40156003d002156800c020480070708141401504000340a2009201000e6112100001c00e06640038007200341c65280d91106102c042c6000340c9071034150051040c0c01c920f62300c002c4c2c1511201d500001003880e40b00d0b200300c02500340850155081065041c1e41d198603150000000f200c020382c5140e0803090302c0d50204110140d5418455100392038500441441d00681400d113410384501140c141c10120044407140740141082440310701902080620003400541002440041d00784030321841e0082d070183c5400b80c0030700059102e601461107100c055664107900d8903018001d80860004449040e83c9a004111021341c0b6290300c12125080500903002240c0c1d2000c1d540c0b0100e1014601500200d00d52002c1178240f0010b51000b850500c07804403180862030054582c400502 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 344664316 1250 344663066 344663069
    0x5010b0f01090314030909040c060201060f03080906090411032404050907171f0605040f05090601050112110a080609070306050f060309030c0d18050105030f040f14010906020307111501 81
    0xd240c00c196113032110b2042030040b904510001004e11147c2e25007854682c546d043c1c1401044010361800e240030400d039081100c501e050700d8100d08000e08000d000e4040040c151302141c0345581103900e503000314241611100c0950300842205204050355450800300c0d000c015441104c461255060805204160001241e890252138120321241030340c1ca10102c2d100e1a010703441d51001000c1c48411505200c0100070344c41303c0305a40081b40c0c01e002c03801d140520307001900c038142c80d004695041100104440e40c05006100c115413500300c03010801100c01c803244400d6401660840000c207038488100002440c00d45280f075404103c50900700103250401c004549490b901c5402e85010303038800030200d491501f0802c02d4a650011620403100e005803c0140101141d0803c1c44004944a0000000c0340544c002c8055038860242c8806042141e96942c80c1d603d44020500010745200030111003950200500303006900d852401000d01599034100104000c026203a10500314509400140c054208217100c002c40d2030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 344665566 1250 344664316 344664323
    0xc05120604090201141317061005010807030902121509030c03030402040504020d140f071401020c04020d0902150304020a0f08061602120705070f060f02030a0f020c0405090a05010b0f010903 83
    0x19100b10a4401038a2180d598800d14802c0c48011403180001d0321904200303802c1da07110f941e00002c418a03900d00c80b0f5072810709130303010354414481c40401c0c001540f00380d003030300e5104904d4900860b01c048990041020003610541e040a59000b41209454000701000d02c1383d01300010100070742c980402000d207607480e03001c0500001c0c40340d03856401050556035070070941412036400080a41c454544003840a941703504c7c0c076106140c13030300a0590002d0b07503241701c829901e505801a00030b0103248552b002000b000b54002c82d140d400301c0ba81e4002c03070780151710342c4054030300e44010a1381a240d4071704160041107000d0307000b5400320b500312a81001c140403410022902a42241c42d0106149800132502e03010790505258203001d07400071320301061203c280000007689030704440b1145000200070b9142c500440c3d1100110314600b0159104001c1c040c038051180c500000d00002501c182c44183c002c41001605440c0195120780aa41c016007032003090140c203209078001500d00311080f0030200002d10000e051900d1038840275 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 344666816 1250 344665566 344665571
    0xd080a090312020a0e01120203160c020d060e0a15090c05040209031f090b10050303040b0d022a061003110f13020a020d0216050d0b0604020702030d09090c05120604 72
    0x38100750181d4007010400e48144402d6484030b03003499008010b00e5200b070702c0074001182d1105202d41004203108403030066102c60707842da40b0400811000d44111000b1306040340c0101e8920340e0240461000d1140e461035a4100b0040c007521034090a010480009031a210030484d0324001c910800540402409012a2415100561600544070001c1d083c028442c030384c0c00355044000e403a8409400c5641c0308140540c800c40c004e40c0180c03240007500c44000c1d41c0b8000c10b41c25501c00c00041c0404629400601401c0c060340b0030240c134100354103040b14480341310300c500500b9000d40103e030415880b4051103902e5210505101e800394840c07464480640501c500706100d405030092015110a5450b03030344203e5241c6007181000c0d552030f500391600a42e906d07545030341030300107005900486002e0350b41c01020300b048801c000c00c1070303cbe454410346844405600c007030700c03d80d8003e60820200006883c24020203234540200d8840c0d8221a1402e030640b0181c400341145141004400c1201c0c2c92030046e80030b040b581111055500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 344668066 1250 344666816 344666831
    0x30c0d0f090807150c0606060302030106030609020313060b1f08191a0105090105120408040f1a0d051315060807270f0605060301090504050d0302090105070b150a0303020601090e0d080a 81
    0x5855540075001d02600180c241f0501040c07054064000310304903605540d080142c143e0b00c010030000ca0100752010b03585055006501b102090341034001a6090300001e022444500c25840d80070500306030a0390343d4000c01c2502041080030210300f021441c440c0250034040c071052070740e0300000380c46038003000400c0e0611a011500c40e080c2d0744610203580d8090442c1210708180d0805052440c03180d0024804d50303202200c180400b00d0380300b448112468400c0303009019135003807e0283d02c00b040034001c01071214500700305603001440440c0c040c000988401c070080d035002480d070707040c04191410508035030009864010340d6003e500c1010340002d030b411000780a90344c00140701461440e1683c0545555401720346e00036004000800c030034629500081c02644030b0401c840380904a080f0580030b90260300c0c2c5050100c0c60500c0f851011512038100e00e98008140042c040300c2298120014001ca00301e60006d9005a000d01d00601c24407901e489105c03020441e404c010b0180c581d1141000b0912031004102404080d11a41d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 344669316 1250 344668066 344668109
    0x7020607142101092403170d020a030203180d0509011101061212030b03070b0423060a0c0516081f0603051504021e030303180f030c0d0f090807 63
    0x945820141691514103142c0c500480c2c401540001c0c00380d07810880c9030444c842d071207024509480036690701e0541c00030116880e640b1091044c0440b0800c00c02c443c00e040101c012941c0e01880202040d200d1610b00580b20306200c81e128100700c807141d00c031915650003990400e588a42140540390f047c1c6007403034440c0343c48000312891800341c0610360040140b01701c103200310000c1010302901c03c51005540c0d035040101c020b0503c20941c0d5440103206a070004102044184003e800c0d542c4c0c03910030362071096070f141603422802c00411030340c0e030115100b6030008040c04003a40030007500780b1440220701a00f080f0000c8141c20116001c0d140c2c240400c0103090300800e440240510001904250025074005065441e41010390b01004602a400c8600301d10030402d400c40341007800b44a10810002800140066041d0b50b1103080d500270310040507001016922130711510400c1000200004c001901102c0090030078013240c2d00010300b102810100c03020a22003108002d01200c200041e075072080366900100c51580c0132034280d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 344670566 1250 344669316 344669357
    0x60a09090606080604120f020d0e0d02060c0a0c081009021807021906090b0703090f0201181701020903061612050c0409020c1c0903020102030904201206010e0907020607 74
    0x2070111070f46001c0e0000300018000c81540c1d995103180070b51501100e0f003904590881e110310100a000020451005040080382040c5000001c11031018018900c0c1c0a818409a03160880b2070300d00b2200a21403242c2840351880910a901d810906800c091140905960015040c100d50b008090620007003e400150010310070071100c07244445d000d030b8507181c050a509000c8040c0c001d80405a03003a4140340c0c00302d42c4031842480760b031181c10b41101031021001513550045850f0300f203091400c0d44111903020003160006103418014400681e0000040c0c3d03070f000c03070824182032110042000d10740340051110716484030341150070310700703d0ba80e0a080040d880c0c1d1020f6490a00303001e203400480095102280186401000169407103603415a09181c0c18040c4d9085c0c003c40741071a07180402801a00140701010346824903421002c400d0405203004400d9010343c2100260f00c0d0020700500741080d0140e0184003080d600301000411455050721000058030781000042c1d42c2c5c10015180504205a00003a000f1301107018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 344671816 1250 344670566 344670569
    0x702040603022206050901120210140f18040203010308070b040f121706030624031c05040608010504050c18010c200a05120d050c0f070603050a050f060a09090606 71
    0x6083d1a00307442d603900d000c403500c1c011100c84070b003251078a60040b98514210b07505a0484208011055096249500748004110f1031908602030001005a5524042c40003014092510780d030030b01c903500c07402d800002a801011451259000b14410401400416811000c54a600ba00502011415221032904107501d034003500c00a80500e07050f0070140445607028a007140e00628038851000b058a8074800c05442e030005892144015201a451141040702d1907002c08480a0090589001225032208a0400080124600000744001400380019500140c0c0342c0e015082c02c2d50708104900d001343c00ca00e054814100d2203900c83c0310305000442e40f0382c0301d168440d0100368007900c0a01c1c101c09500c80805502500800d0610680020344081000d0400c422813483c042140d00c001c0c000841c40507400e8410380d000b003d2020290041a221f61a204d8080100f04000d10459400185600d420010030007100e001901005124404000b80f1206554080440b0107542032201d00283c101c1a40c58180000d1104d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 344673066 1250 344671816 344671819
    0x5030a081308011d0c030106050f01260408041a040f12080d0e1f09050d08100902030411090a0b0a0b0a0504081603050c0a0e011e0b130303020706020d02060408070204060302 76
    0x81044c1c000294603d1070000b0b00c001a2003040741c100591203070805007624038501400f45c0120ba12210400e05d50300c07840d20356118203100c0d0850302c0c2c410310402c5041c10307200d01150306680c1128005410044003403114007150200000d007884034105405c25030040c10210940c4a07a10340c12228041c504140007000d0704540a000c0c002c0002c01011101c905101d0f1540b40410003408103410200440c4c0818056002e80c641c0540e01c01c0c043d00d007401c0c086030140d42c40c0002030150800c0600e90f920129003130301755200443c0a0f0b409000b040f0150b24902d0100b2440010042c8062000341c100a410810754858807920010313203101e020450b0310b0301030f1100100c446000d00d0b4030800040c4a203040c024140c44a42c074480b02564033900941d440a026038060100321140c40c42402180907105004000b10664a80c0d8005403d00155084014940e0380b44000300940040c02503045d583d0001900f04109a01000f800380240014005070806a8030140003035110b89001b00080c00355200000e420007107580f02d81c0580702841c0d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 344674316 1250 344673066 344673071
    0x1006080c1621020703020a0b07210302030f012411031c09150209091504020f0703020c010806092202030309030105010303090e0a02070b01170c0a120201080a0605030a08130801 77
    0x81410030070406407180c20a9110700c0b00c4030401c0300d222440401c5640c25a50042e0041c880203140c04500302890780070110550344242000507031410440c8050040413403211507600035031039061184015440d224103038410b10310308285c054010351041c0103910390110b040d4541840528031f07500f47c400b01d085110b2004044440b1200300242044410303180c0c001c0500358040e075841018262855800001c0703100d000140c80e80a503201c000a40076604501802c511103e003e400507041c208da0b81c03256900707500419412405a04045020b6003030f56800345000d60300450446110b41c030b07400d082c440381c130103181c0018040804008400307440c401d54070300300200c030309080d0040d0003045203694900f1700a094445900a4042140241020803c034013401d000f9030714040e4000780c6c102c001d6442c208031303c5280b40f8008460060342c000c404c020b102695640b110000100100c01d038404000086100040403200d0080c9046502071503c1c50034005d60b10001000c5642c10383c40400c207948c40e000d0044c0c4103100380d100e0340481d4043d030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 344675566 1250 344674316 344674357
    0x90507060507050606040c170718090f050a0510120302031207050a14210717090601050102010b041a10051e1305010206060d030516051b0a06081006080c 67
    0x41d4040020503142c0c3c0a0320950b111521160100010b9901030b00d0041c0c0042e01c8883c1c1c030002007000088030340d04424203046c00a1100c041c480940581d81d07040d40190861583c0340e4601a8400b0703980551940070190303003401c22140c50074050070011b6011078003410b0310710352204807050b080600800455480b0400f0641261282c9030206001342298800759040b000980d1511206d111034100d08140d0b94070340100d8483c45c00000380b401c00d80c2030041004240303504000507444d8131651705c40030304100c40c003d80900c006400c80d58140000642540c51a00d2003601aa180849001c0c24a00d40c1c221203640c800100c3da030424100010f10f085485000d11f0701c5a20941128400c452005181d503002401c8501500009c0758200b0341e520016030716150102e54883c0c100c00d04840700c0b80064411002001440b01c1520300200b1001e041c0c0320689490114040c901c80071200d043d428100303142000c5048000e02d2507207490403807450810540c80b0300d8030140c40f46030107001c503d10100b00202d803c0000d440e05410312880f01c11042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 344676816 1250 344675566 344675579
    0x1180627050c0f011704110a151121040311040b1207050913050d0f021e06010e0906040206070308100510050702040f050601020a0206160b190c0c02011b0303090507 72
    0x1c0e61180b00031032050400c40040c08055010340c0c4240840080e512000d10180c0e03d640710304107031000a0062a50142c24030b4400700e2210b0750101060000304036035444a00344210419218580603401d500003e40207003041910f00c4003055501200c06883c1c0c0700c406042e41466150105000e403940e80019540520a29410a28050300103640c20480c0c0041304c086c403640c0c451045154041d1021a80508140c2211420f602941e0041c142c421030813403244110b0754100b800c41212410360f038000c80000030039004000100448004021520382210b0500c1c060f01c014200395001030300310701c5140401010300c040d210010703403241840142603000b000c0282036200890220040101154816003040303201d14600b15043c17282d891340e4031841e88260810303001420300010380e80030800a50030217104034070201148015440001e100000c0a07002d03001002c3d09204401c0d0500c00c01c01981c812074101010042c03001c100002507a0b10041900d1071a0007220542400505414101c02400702c984029196118009000454 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 344678066 1250 344676816 344676823
    0x2040f1701060f12050c1903060507090504020315030c04061d040602090a0603020909151e03030c0f01060f0b07020d0b0a15060807030608210f0c010f0902120118062705 74
    0x4c10711a0003030303400490345402040401242010607180b0403a08031000e00c0052519400640c11002034100b10060964590004059034030843d030018400002c007400d051181010440394070000c000701c806100031418202080c456440d91700c5030460114101000c24103000c80750741141e0388040e02600050841d40c480c2d170043c000e0350018000c240160540400a5100c031008800c6001c0030300d000f408151008142c00f01190190b02090b0080d42c035010410440188580030045598102e2a080021400c0361400509546c001801da001d401c405004011f0707140165a0200301d10019640548001c241740c55443d5180010500c401541d10f940c000b10101095442e00b202d030301383c410080d6036000d105072521964034541f074502030407164100c12140c0c084152641c110102400d07a00303550440c2c141c108481c4506050a455109500da81080c0e640c2c4200380541c00c24000001009010600910042c02c0b64003d90b10324284559025009550755124410851820640228000700c0c0c0354900c080840e413400e00c2a00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 344679316 1250 344678066 344678099
    0xc180a0b012d0f0c24021210030201020f032d090301050a05040b01090204060509060c0c0a0b0406080703020901050306010f0941060a0e150d0e07060302040f1701060f 73
    0x42285100f20580d064810810315038125840101c000d003688220310b004204c0002c100035555055000d10458036002c401301c2641d031041314510f040125852440c0006030411044a0100c4542c4e04100412411003c403d0000307007020040d1070310325002503202c0404160500950011643c55400d00d0140aa503a400380c0040340114010012800030b42d987c2e01c1c04c0d07402c910039480341402140c0c0a118040291400340301802046c03040b001950a103040c4040006e40503c03154201203508000410705101d002e074010075290f030011140c141145400107a2001078181d0000900c0d0504002c00a690449602d00c1001d08070000d000c2a880c0d41c04000b01d0098414104002901c100000c1810350361501c0d01062041190000e250041c02c052f02c0d1900c1200101c40d0f91184802154101e45a00b038810760603011a0000c0c41401e032001000505a00400c5419080c090340342d10039410180144010b01c101ca80c034030104811030b020311508140055800c141c0c1d40c0517195a40c000b82c103008481100160b2035520490451 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 344680566 1250 344679316 344679407
    0xf0e0f010e100315021801020f0d081504020403051b040b0f0906120601090204060e100e010507050102070203030706050402041d0601120c0e040c050118060e0f03100509030c0c180a0b01 81
    0x12900d031500049035100506009e800c10742d405243c220748640d000c0d40d145034006010349003903400807120901286c243d070720580c812100b580c80030120041806242c0d520003000c0004840501c01c0d220703494002950000946005849400d03240701240c1b041da550b641d43c01e07141048506841c055030351191000002e422902c1188041100001200328911f0540f5040e8048515511680c0c000c00e40b80c80112659003020f401111199420091403002d82d81c1040500410752040c1c3c0302103018035192040c8800c0c2c600090040d4100404608d68008512011609905460360390801400660712400c01c031845d444558003014075101004c0030b0000380440ca80c017a134180d03282030f220b400313100302c44404155901415104800014900c0780d40200c0340e2400c84080701c4062401001c071851460088403550480704140d4034150142c1c000504035004c0c0d41d00340325007000c0b110120703a00024541800b110f5160110010301c0c6200b078503580c60f040d0030350360b005120343d0401000305801412600340c01c50030011004029800c48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 344681816 1250 344680566 344680597
    0x30c011d0d0203040803160206120103060906060b0c0a02042f0a08100f05060703140a120608030903060a0b040e03030a0c020c0d0f030309020a1a03010f0e0f010e10031502 75
    0x290950000041342c00300d5607100000c600c0c00c920f80c090845407841200080364061001c0140c000d150907408690750107540903c000095114141c5491b504503102c980c0142c0c183d900a1080480601c80401c0b0760500c2901560701040074665800320b500c00600c0001c602122120b440400d1411590344c0003e05007010300341d1101c40b59502c55122050506009218614150840000501280c10040d015000d410b00c2424a85c00b00c51061000d040c00350010741d840307400242034640310b640f61510350056100625140c0c1c0518901400d04002c240c691100a20203000b81d80c85481c103040d0390b112a444207142031400b10980f03840703081c8842050044c103141c0818500601c00c00c05945201e180242c00c02c0e9509920000c001459410b42e9010f0f0b016000070f0380180c2e8800813507000000c00d5580c81c0803440e2000031002050395a0741c1010140b07060024290454a00700c0c07020804c100028980b5140e503070560b002103c08075115a201c90841003000060b0700000c0815a810040350030311205070700038041401000020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 344683066 1250 344681816 344681833
    0x80a0b06030402030615011707180906180e0c03030f0a020d02010b01080403030c03140112140d0e13060302041b02010c0e03060118061203080907060819020a02030c011d 74
    0x2000000c1c002514040c0d070580010000c12403401444829040744107047c103020000398405d0300450342516048803a003000c90300300428800051381011201f030103030280b400c04001440c240080c4180a6040d50310300c41c1801d80d2002d817540d00342400c2013080941100102229515002d220302450385070444600040035200e100d03000c51500d0f0040c0582d5440d0032043c3d407828103c0c2d0740c2d510201c02515500340c0d418281603407038a004440e040321200c501d0180204801d50302104c0010300c3d18400442d5249c800780143d42203a00b0628150b5805104040c480e0800c0b20303414900306640b07403501c2c0101801c1c0c6c4001d621514015541d0943d4000c41d018001141c0309030002c0040403180d031810364030065014000c3c1e44c103030060b0300180841c0d40e9070324500c2107d2403040000200c01d510f41e024035160b14803400c82035000c90321301c00c1042544c0104201420140442e443d000c80302d8101010580c034810700707041c02d140c5455008101805010310800540325001d803807100038002d0140d00000c0c0d4414042c0340d400c40c612800359614 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 344684316 1250 344683066 344683069
    0xa0302040308160317040812040f0f030503070f1b0305070213050403080105040c0f0806010f09080f0313150e0405071b110915060306040504050a050a06060e070f1706041b080a0b 78
    0x16034401d1f03400503101880c3c003007030b02c2121028035802413049071420000100140401c10a5600819491003512050b07030342c0c01c0005c2d0107800840550318450810607422036070441c0c0300c50f4603482440507502d400c0642c0c560500d440000c011403181c0752100384503841d02080000781940b01039524126901500d040140307024428080310000420044500800d01d1ba00c08900381d94451440031103100030520b05100a5a01c0315945410f108229011451503400403030010310200c0400ca029004261044071007811000c851005407205105000c0d5602c1542c5d00c1c80091038003070244015210746020009200c0c038101c0b692600c4c0c6490015085a14050789600300080c2c5003040454080001600080c1100c0c110b503100c80421006e480c005004a58901408070400f0008404100c2109034910076a0086800b5080c810b6840a280c40100f4040410010a100032900b0b03070000210740c6000440191140d4175a2a0320105010707000c0c0c00d10300c00b031040c0224032580216600c14a590300031b045c1040180800003c440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 344685566 1250 344684316 344684357
    0x30e12150a091b0e0f0a1118090a0506010f110c060c0a050d050319050c0c06100303020607210b0307050a0b090102070b040305060f071e030b19060509060a03020403081603 75
    0x14030a07800b94102c0400c172032241d071829461380003890b100042107003071004152841c0703500096000c5a1003d585241d041151400d544040c0c0d2000c50540100014501040000c000c0d403a08082d090501504034000e101c039040c1400105242407019064540d070f13461200180b9031320142c0810603200741c0038620120450903c580c2c1168051036000e0b45441c0d0040038100800002d02000d4001e9030104010480c1e540444401e002d441d00c00d15844a581001c10f10707609000c0d0030b0440041699003046200443d6000d0304444070000f581000d41858002210002000032903d800b0302c91f0005584070341038240024003801004010700b810350081c0c0c00d94146a640320340515140c0242e0100910300c0c4c01940c000b86c441c00042c000790340d10046606c0e0521406c422030044030841002c551502c000203880701030b12841801d0401805460b07910880c00d107840e07285404002095401050f02803446032600281080a0610a130141c4000c1c542084d00c0c10f541d500d00301d0450000e2005800c040b0049180c1002e01240818804c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 344686816 1250 344685566 344685569
    0x312091f0f0e0a0503060a0506100806030a061815050711010908040e04030c0b010b030105011103070b150d0501050a0c0306060203190c020105040801020c07081207030e12150a091b 79
    0x94441118400c1c141c00261002d00724811401d4215040030070000301550104100c5001e96041900019607013090700a100c3d0000b0f41d10241c00604c0207050502038240c0340003610b102c540d80c2140380020400d206d400d00d046007800c10700025007143c9203070300c642c40b0056141d03000700d004a030a03403208080d8510822030309003655030114001d00510401c1c0000c00c4440f4908a100764080d100f45000c0400e80821f80d80d1341000e1000303030440103264030044014020b550300000030f0501d1b403117404000c60400c50995511b0321070801c020404448800070140040c0103403907902d11010841e07031001c020b001500d0440c0505000309069040440040d0a01d0000103900c2d0000c4111980a40302031003064000c03810b22001d40b00c3c0c141d4508201d041000c108000203030050b080c4040e059160014000d030907901d02c3d041100385044401001d01d00076030341c10480440020f030010b030b15000b101d10944034100442c4914003814200b03c0f0f201c030394000f00c04000e4100103840351a0f038000c0903480e01c600c1340b24801040481c00108200c84a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 344688066 1250 344686816 344686879
    0x1e08071208093c0a05121e0309011814124303020303030406051b12040c0b040f14150a082e090e1002040902120a15030b070905031209 59
    0x12030402e01c118144001415003141a02040b9207d45505500121502010888044240d000070170202e035203682c000f40308102e041410306040d186600784482c500d48003085658003486a041c1014082070710000340001c861100c40b020110402c2c01c442d200301d660400224100c6003003809062a100318141d020f03182c030f1013582c0d0050700460071a0703104c2e03aa64000b00350241c080111040c9030350f44404500c1200e4020b220700159a91401000c4c1050318245031401c07810780051038a907070184018401030700c01d0625401216040324090007004280c20106e0130300d4844a840d10f00301200003504002140d000300a0300e004840d8241e614001a500b4098908804030b004203c85004800360420803034089141c02c0a1202c400c00700541e1601100040240c040740d100354403807444590007240920124a07010303411988100446800d00c410000d0810b62074440e2580e002c0145031500b01701c003040c0f440344140c8000016100c081c040300c11410803400d00da183d40d000003034a0ba110b5800450122003014000d100071050401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 344689316 1250 344688066 344688079
    0xf0b0301031212090503030c0a030e0601051c0305091f120b011205091509160605070b010303050715050403030515030c0f01080726011e08071208093c 66
    0x24141c2c2100c4420018190703c3d00c50341c0341d00025010407005d02c011402004a04200d941d01c00003158040e05039002c43c3c001c0800d40c1c1080c401082030340c03613a000101010b40c2185207450071503c68078080d03c1d076000300c10415070400501e000c0040c0303040b2882425104094180c440020b1003418011001c2a00c2000000c030740018407150180c1684040c1d5007000c2c2d08a411441903c400a2042c80d4140c511038040314080302c0c030307440044030380340c0c1c1ca0a0308111409801c580c81c1941c40c0040c0b544a104001c003040c4002410403030300080e01000e2024019214020640c201c1017403003181800d05000b0080e01c01941d983d040c00d000080302060354540080e24166504020304500341c80d9444074010358995100a1828042c0b24050141101c00400c0c18515840e0074140d04061076554140005801e841c0d820320303916001e080c030300001402100c60005000d02112540d04400c0c0e111f40046c584170040c0d00503400390603080b0400503020f0781c0f0414611080c5501c1d0320300c00ca4400210038075030714000d0003105444a0075003220 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 344690566 1250 344689316 344689343
    0x3010b190e0402040f140106031506020604120e060705030a030c110c04050423061506071a0421020604110303030105010c020609190b0d1b05040501030e0a0203070f0f0b030103 77
    0x45001420b584107000070000500085480d0b5020284c40110290704c0031012501c00506c8002c0d0140302c1c104c081380090301e03400022400c08001035a14080500058000c000c0e4403000c01c111446910081031070301d005003102d9207405141c5403196a0f60410000400844d040c000041c641a21903001001b200444100421400702e031001840018a00600191421aa801d1140c0c0d0780c00f200710700302c2d541d19500400400c4140f41c00074802d041002902440c40c4510b10401c50710011819510181311031a0000d640010359844510b401803203c60b0041c8580054558080c1021401c1e4000c10300c184128080d411410302c0c40410300806491348403d01030300f40072a0008600c900982014030250500d10720107859a00b080910080740d0120060030b5004420080b00001c44202080c001e0007070100100b00c4501c0345014140b1400050035901460240c241003503500e0061214180c02002a85c211903000380560702442e48800114400705c9981c00b4002c020b01218100040c030040c0303002142e04903904034130100a02e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 344691816 1250 344690566 344690579
    0x122103070e131113031e0819021908120a090305220911030610080103020a03031209060c0914030a0f031808030c0a0c08150703200c0a0203010b19 64
    0x200104142c42c281540ca4007180ca604003503500411303803080301c2c40030240c03018034510b40600c030f0750000c4880e40641c1ca00ca102c00b0000842e61000c2d902005d00c03001603660035400140e0100e10707054140d0040090022201e0542061090510090210b820403901c0d41040f9695440d50ba000d4810b001d50042c0041c0d4200099940340707510307414500300000c1c8001040ca0341c2c2d560340c00b0304040e105003003000e0001e200c0000030f0002500d06048904644911030070001087c0d89141c0016502ca6100e00c070140506c5514002d40e55800c1c10b5a00500e115540500b0400003400d0015005040326945c0c00f032200c444040782c03880312140c5000100300c0e14a6900103a1501500950b81c0c08032803000380c03000001124400214081007500c014809004882c0342c140c000e294804080c200b00392521190381c04094103811282080340c070828240042544044213040104080c0e038030321840c80d1802c000a902e4540200003085040c060716010034526841e500843c020b0112072a65030801001d840c000113440c1030703808080e00c2000755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 344693066 1250 344691816 344691829
    0x50f060d060f0207080f030702070f03080d09020105250b063015010b120114030d030e030405030a051507141605010f0207080c0106150e12010b122103070e 68
    0x20300c00b40500075013010b8203076944500740e40103c2c0005612200100400072202e41c1042201d0007806a142481102851600d49025902c00d40d05443d070025201c910a0040d1f901860131100c5e400400700f1451210000701c441407a4009a0520844168a5140c040f41051030421070452100284215940d00c2d140c1c5d01205580301c01034003a1003845805140540702c6c0d07110480324818000c00003c65001d6654810741034410015034140c11100e1100402e055229007614006000006002c460500040203140d0749030369440c60040340c1c4a5585840742c1020382c810410086002100c035151400c44800301d855040065074010b125020076910000e0505c03409888140e46141c4003807a6000c1e00000400c2070076110201c00b40d91000000791080d06c0001801d03401078409105010044c40191b04080c0c4d0401e002000410b17416031700c1407051260500f000d0041942000703510229203604003d00317405150302862606c1e622818138240c1c480c004200701e0554036255400f0310440740b2841142c1e550758504048941000346 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 344694316 1250 344693066 344693081
    0xe040b0402030f0c06091905040203190b010f080c131701020901081003021c031106270c012c040615022103060d051507020346050f070f0204050f060d06 67
    0x4200c400c007c40001c0c1070701c80348015400340d0411803181401c0036400e210f413401d42d551a10414104000c8095402e00103a008102c0d603001480c07841ea60355200c40380984041809038035001050720326031545100318569415401460340d51760030303222181155140c1d00c202807000c529110294010f07041581510309410751207000000240300e414240100400c07200d45502d08502242d820300c50b0141036148400190940c49540c0044034007600030441b041001000800d0448910011984000c509940d4400441c0d00c0c0b540d410780385c03c00b81040202640d2100b401e0074501c0c02400c04409070203020b0801d014007440e112411184449000340c645940c8a00703050008503108510151054081c010300c9040b50030314030003098021890341e4000c584841c00b0700145023081c07040c03910000442003a42000e600c03d59126a8040c0546410208401110059002a10340b44156411a00c0d5124001101000c104041c0304401c045802030b5400c010b141e03140c8144204ca0401a140c081d44844492550070020304d064100c01d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 344695566 1250 344694316 344694349
    0x504080a06051806010e010302150c101805010e01050109110412080f04050d1101090801020a02060a0b0303090d240203010503030306040b190608010e06030d170601090e040b0402030f0c0609 83
    0x1203c0508910b2840e0612030207801520280c103090004005500c4d1488040551075640ca201601d0096180310040e41c13441c046455020058032039841a4401c11380768400c41038150054000e0084190281e0b030103000300024001c1c1c00516140075540c401c00040701d41900c09032400c0721300c2c0e5010580d09840f048442d0f00b1212900a125804010215003a02c1c6c03c0003003801184034041204140c03030030b200050621441a04400c85c0b60b84180700851050790300252254100f0401400042e1100780c2c0310100b800c51003001360490300489525030980801160004030008102080c2180f14030180402420069200a200c0e007030741039006201090440c40c180c0e011486e02d000003810400c042c02000300c0480110300340c0d4055008184103d0042010100c02100c1c41d034095800c80c00b42400c0d4489050241000840b4081c580354044400000703200c0340d0107019950301801c69182d280440745010310702542c803003900302c0d0201e00034000e00c00e850000020000b4a0482c01d04002c180c6804d1240354020300010b4a507110324503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 344696816 1250 344695566 344695591
    0xd050904060513020304140303070c020d020303070804180c0203041d090703050607020f01051003080403080307090f121101022b02030f031005030f03030705040b2d0d0b010504080a0605 81
    0x18107650381009845800d6005030f000da100c2c03510b4200b415451888002043c1c06400c00c00410507280da00510034030500d54103c800e850090030300d00204c0d286000b80c070001006d0240000c2c0200300d400d1400d0b0900021000504148018146403104980703c0c042c51003446036203918010304c011582c00b115202030380300058204685a141d41c079140ca9107040b4054800c031025821458500c13400900a015441e40011504025101245180e80d8071841d407159100281c440729021001c103d4451040030319000420900c592046d0b1991a0307090400c0c45400b10a049944161007440c6140c83d500101d03c04407204c03c40380081940e450080109440821011a8034046000400250100300c02ca10091400341800305a4600706500742014103160455240c01103035164018010040c03060b900074120707419035181a8446440700c050082200840d0200c500c2c0000140b00d0b210980b4100c04520b0180042c001c80040c14040c51442c03800541e140c0c401d5006c7c1010075000041100003146d00354006540140040714407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 344698066 1250 344696816 344696819
    0x91603120e011106070e1806060405060306010c0b071e0f0207051216180507080405030a200a0f0c0b0a0504091a120105102705040813171e0d05090406 66
    0x44c0c00c0c07403c1210001d01080c5003800320b0380241404a003940c4580b0302e24052040e01d00b070020014000b170140780304882c8554030000010f50030ba44110072040185600440e89107145c2403120010b04901103051200480f0810450583c044a20031902d6429001e070a4000d0b155450420003407100500241d00c0c0071805100d03803444030b0382c860340b2808a04010300c08521030000310b425025030641501c00240035001044584c0c814000420004801c0f12844880f90070300790124806028401d1003aa642c650070042c0740605c05000d0700740069000450b8240d84520714525009840e403545480b03c0c081e01009000250090106104da0f0625a0080b480c8528043c0c10705032190409001807444146070300d20a41c9a51a40b05111120f4402825030b009401d218607110350500d140d076001c9207060014985182d034961110041424480d2500c2192412240044200d1000e901c55480303207000b0f01c485c05010481e01c1444003480441e04015000c0b100e10100c400600300481c1050421155a004640615881596043d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 344699316 1250 344698066 344698097
    0x5090a1404171e031504060602101e05011401090807060f0507050f0303070f03050903030714090f03030c0a051c08013f0b150f1203070206030f091603120e01 69
    0x4000304541c0900f12402d64900c2c0030b442406803072180e42442402141050024405290082000840c00403821000941c0701c055440082010204048071000345261a00200344c1c0d502c06102d00c0b210190a0700c6a0700415a103805403503842c101c6d8440d140004128418039824603100301c0041c841940500100d441c00501d20002504580c03088e10b0401c00f007135101d180d040740c190300b40c0540d0b07510400c83c00246045150803000076101404803415106c92520000d83e04203255500c5150a061100203411240c551800b0381125980b0100840281c0d054400e010707034492030700307000b80d16102c45550031303901c03c580c6919210840624a01c41240210842c00c49003d0030b00b500701f004401c480300d601c041d089022a0f09a420080f48a00c400740105030302121040010000383ca6030046108128016110750304100c20401d0140d00314010410029800303140003040c000f82e000603440e250b024082e07020642e0f040110150303000c0c4201c4520b02c401882c0081403070780030442d140074510b61001d481042c10413800d001001c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 344700566 1250 344699316 344699347
    0x150c0d0b10080105120309061b10090b060f031b010e0111030307050a08070c0201020a032a0c14090f040f020d06090606061404120609020409080301060905090a140417 73
    0x1d4000003403a102c010000b80c41c00c08141001e9825400c0518038058001002c06c150b07202d000005103002ca2842c92942540384d00300280d031140d412004041100e1407035490503441c03d610544580d480381311042c5454020f45030104095400d0311080c940f80c00301c030034824019140801c0c1c0303825081c11b0020302e0300e03000c18030740043c40190305c40d816503940e00e0341e00c0720500030180c403c0d43c02500581c10400319008a80050341c000410409064050034503020340303c030b54044010346641108514031141186d400e080100802cce800d00da41500c400768151089c0a00c41e8091001c080d04c00c641040c0d0f0b141300c4001003000b040303040701000c00d000d0029007600d980c840710f502c0d00ca054038907025046886940d02c0c0c50030440d45070700c4001d030f004454046010038901032a02c2c5180e0507140c001c20b07004e04226500ca480c0c10840d500c41e40640920b907800640e00c1d0322583d6807480641080002e110f20340c0030f0681200000c1c00208103219982100400361400ca5060701e8075200e8400207a808008035044180802c60f1821183c80360 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 344701816 1250 344700566 344700589
    0x302131107060c1b1104050a0e0f010204210b0f0a20030f0f09030f160c0b040603050705030402060301030308060102010f0e0115051002060f1009050a050a0e150c0d0b 73
    0x41c100840d241074500c3c002070441c0c400d02c0c07040080640042c070710800140508414000500f080380d0100315911441c1840c4000c1152184920480c030031b21002105208040d000740c400c49100030281ea4401440310300703003403003131440d2403000303001179001c00020304446074000000b900510600000076071111300506107841c580300b40036102072003000401080200d000607203503075621450f81d0f02801c006c1c1c00e110204e569a80a24143c440040740045881e0704942e081c24204d18060350840101e0421a6a40c0c145a41d50780c001d00800000a00b80310000b07241792300500449000f99800350945207103a10315201290440d9002e0b01450455480381c0100c140360f81a40106000d0083d90b10000515481d09503c4405041c825800540115141d003440c400541c0c01203205540420003481c04206990340752040c4c43d29000540015102d2072502090040132240e542c000c3e489020700032810094848040d0005130740360345226001720344c2115840003e294401e01c20160040ca24a00c02c003042c81401c0c800000d0030507844 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 344703066 1250 344701816 344701823
    0x2007050f1006180c1e020c09130b0c0a140a031509020414030a050604110d0803010303030230010918050a0f0b06010507050c152a0c0105040509010302131107 69
    0x2291014460781820040c04246040c0b10101000380c00d0800c82e002c0c2c03400c1d914801070001c81417a20b14008000e40248102c1e00c0c40c440040c060412464040d20031004e1b107200340016190301d1801c00000e001d285095086504000c9a9280c40401c81541c1c1300c0418158410000d00f01056201e654184480042000c0c1d01c01410440308003503116810003c6141c14041c04c2602c02c1d200f507004070b900b07501003100840c8203a000750f0002000d500004060b4080b40b0400c920a00c0141300c0302c000400003050592503800fa10030314040d01c0d1004900c0c4c007410120341e003200e6060f168241070400ca100400001e034490b071101c010010720740500c0b044901a51181420301480707a6054911a00703550500082042c1d280705190300c42c009080c1b21b03052010310b880d9150303103100c1d0490700360003103159110544540000c5015103600321101180220184403040c207520b080803244100a00d14411440b0420280d8020b0083d203050304d074050840200b80c0e28540800c0401c03905100e029150076075a2281d03440f80d03140039004004d0b0901 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 344704316 1250 344703066 344703071
    0x30723030a030b01030b0102010b1807091d01080105070c030203030a0b040e0307080d0b09090d1d0907021c05032809060e03120606030112023c01122007050f10 70
    0x1242c00c009019180f20303640c0c6c6411640b50001401700380da10b80a41404501c2e8080341c2001942d00d85034207030b8020206400010805c032650103c0282c5404900d003150589441c40300030b000c07645517480301342c80d030000d10303032004000d41c0007400003c0e45070380703079901c129a0004000c10119440d01e0b0140d116055038480e001c01c0e5540c03040090220200d40c3c1e40d025208482030147c49041c00d900e08108140d4903014003140d6a810008020604c1401895245059000f600010148801420048800307035a520402040080d4580c072036072000d10040c002c0045d6031042c070021080700b003130021520452810070f85102400001c20355035080100803401e02d202d41d41c0501c00100066541c2c4443c420143c9145038001d20180c85030604100601c0f408013502603a07075000e90705640d4105403255024049070900074103640d8011251000898040d42c00050400c404600400e80312038001440541c0200c0545d42c4201031280104000151a02c041135050010540380340644250f80c041910b140a041c00c011106091044d003a8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 344705566 1250 344704316 344704331
    0xe0a0b1f02012306010e0d050a0602030a0204030209130302030406030e070f06080906011e030b042109180b03121608030705191701060809120f0711010f02030723030a03 74
    0x200a0702000c003d0005103c07001940e240c0040000d11800d2450740c03060240185540860410504001e0b50fa059903002c0002d5450307240654100d4001e401070700c070a138400d404407408100595006404c0c000100c2c3c243e4051842c0c00e0926400768081e200304102c03000c4501c02c0410020380c400c803010000016190359030f181007490a000440510303003907041c0c001c01d2125107001c801c109548105a08041160b41c00b464030411039449084c904404503555005031285002d0869088904e80d01c010200150b07050380e0140f181a4801c52003000448151440c810b40550045554500d4840642c0c0a030040e1070000d00c81c445500803940c0c403006650800d941c044041040402c0c1c08c003150810440085002c1c6180c504203601c10150b40b0000c00698040c0704000034850005c0c0843c8000c14244400c10b5044ca002041c030790b82c0c2208840d00900c0e50b201d41000c0d40c41100e0100c00b24410340c41401040519540f41c0d000314103044650700c43c0344408032038011009032240e0718903c10302d02d400c00f440940000300c402d4600244e00d5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 344706816 1250 344705566 344705591
    0x210601050307060c121b0609032c042a0e0a0b0a0f11240a0e030405010801090b1908031c060f0b1602060f07050c010305010e0a0b1f0201 60
    0x50180c101501c00d41000b02e00b0700c80e142c0e100c43d4100c6015003008071100c1e0080340100544080f00a04024189200700d44101c400b0f0100e66008800250711030f5071602c0320b01c0e04681800350084044078100e01c5140344c102c2034503520f181c1030300100118646a50034001110009002c801c2408105001c00d000c10f140b036044400c80e14101c038a18000f00601401c807840c240000701c005091000440b07152003400220003522860040400c4400401e0030700c003016400c503001c0070815400760700301141c544400703d050041940d00383c0004000c0c2e500b03d40042e118959540d00b0903400d503000d1701400303030304681081250b0144a10301007100c10b40c400801121000e540e1358005095000c03540c0280341001020f0034249201008600c0b06101481e0440328003211954681541d044100c0e600c507103e02029600080104100859000032070042c43c03ea4803500c12036401e107983d0381c01542546d100b4031591109010b60340008803401d5098005e01265034004001515500d144c610000d5901c151919160040c1e646005081d0070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 344708066 1250 344706816 344706823
    0xb0415020706081e040f05010519060b040506030f130611030a1404110607080c01060f180b010804081602030f0d1206050d1704150c02040c05070b01030803060a0521 72
    0x5032400d0f1070b040003030b0316151003070f81c07000840014501e00121030100002d003881140e001805c0f205074007000038065070500e0381c0b40c0011560203102d1000b20b03920305000010f485003002d04490890b54040c108034119590368841092021001f410b101e030f40b05024000d41d00140c80e45c0b285c0d01001c104070f80840e80724105848114120f4003006a9003456079070f800c050001184000141400001c82261ba25035171314654902406140124140001d03690708254002c522480000003440aa90201440004c21500307002d0700025100c0090059010030203400c00706d004585080010100c00036138514035042d0019a5021034035101d90307100c421405811000c80080f074240d10608600c2e0b10302d40c5090a200207401c00d0001900c0b05540700c00103003044002052010102041002d640040420b0421403040c030340c1c0c400b006012103c001404a2003207203424100c40000b405501518881500105100d80313680c00c5a03201c51300e40c2e0026284940c030070116800010140d45800c0361926240e20040c00300c0001408500783c0d4503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 344709316 1250 344708066 344708069
    0xc0807030207060e0117010e070c0c0905070219080d050a0b1009050108060a050102250317090a1d04030e0a08030d0b090f04030c03080a06121a0a02270301060b04150207 74
    0x100502800109029283d00100f503040d100008c0b1502c2c865100c140c002e40b092200c40700f00420108440704002a4003a00340c0c00188070b02041d40a8900030074404000d0b906040c40390400034003200b428051100565815031009a02c51200c0c40c000400c0070100b0000341003e800d1420400000303604040c06c4c401540d102c040681c101e001034450350980c500b01000130307440307520110b41920441c42c1e8035040c040a00454060000464004444001c1e0085401c082041540801619406048000e4000030f141d2090300ba05401400008114441a116a50202c4045842c20355190b0b01030030f000c5000c190b4040500051900551207800020901441030510122040050126044500400411012039086031031086480e41c140350804d8113988070080d42d4000c020035001075800a100450403010000b50400d20325505a451002c528156240d1000c1030580c4212313241c03030000e8040401c500b208107034104031000038060700070004a541da0b150003012900b0740040d4462504818040784012200340c05200100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 344710566 1250 344709316 344709319
    0x1e2409070b0c0705060f040b07140d0207230427061b0e130212070c0605060405070509040f02040519050109120b06090405010b28050d0b01060f0c0807030207060e 71
    0x50a0489445046440d0300b11842130502541c40018212600000681141c000c2c03d48000c88945401050400300480e02501000303080f2407144154440149000043da80e00f00c450b5800d880d42a005804001c10b2015050b0000300d420a4131b5031008024420302000b044060f0701000701c4410500004c0c2818029200350880c0131000e40658110001c0403a4440d140c034080c0a0306403111144119510762a134000e12500340c1d0009a480b140041c000040d03030050038409164005d400600881e03c0720420031040307410030b40b1501b012800801000c4e50700e08003a006001c00881029005040039941d6000c5600c00001c0460811071401801051000d0740c1c008c6042000b81c91540401d142d800b2540d69800c00784503000c1c001c1807190f18482e00107020448250003903110000f002e0a0485070388465240e060100d0204880007140184054011405042c02d0710f8400c0f42641052803030505074a005010f40d044142e10028600b003003d86042040400c0901c070050050922039401418418a0007000812080c400600c0b01e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 344711816 1250 344710566 344710589
    0xa0303150e09061612020c0a061409100518010912230f130305010213052b0f030e0a030c03060605152b0612050105010e091e240907 58
    0xd01140d0000c1c0c3d540e8010104000d5101c0020401000d0320807281144030084800d000051040000b80046800800701d4800c200502c100c0c0c5480f030203083d041000b12000f1480340d22440c2e012001c2c007441d070442d5070010142d511003403803900c1404545003520348051058840707000400300c0302c950561281d07076410300c0b50380c980c070140d402428407031100054801c040b640d00e825800030906051180301c250402006580c004000c40d0b031214000400070407554280f1800742b082200d9a43c4035000700070821404064400b4544207454154150b84d105446010341d130050b070070840841000f1255032a16060040030b54098043c24444c5d44c85c514000f41514040d81040340500d01c0c50368001140000302c02995108400e0764182c00318070b400c01c10406600000150304040441c1031400c0050701034050f0058010041c0910300900c000c0c0e0301e6000035041d0714800d58250000303034000d000d041c1c40708807030050078a50703070340d012040d034402e580c0030b41500000c2c48101a44030390701c2c0d03104001e01c0300c0181d00b0880c0304020483c64084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 344713066 1250 344711816 344711821
    0x2010203090c031501030311011104170d0f0219050703060e0a260328020307050702040e0a030e19030605160f0c05030d0b0d081b06070c05030901030c0e030a0303150e 73
    0x1e0040f084c1c810f110040500c08090310f039990f180d80a40000055a881104a07910751355641c9503629154009203890a2a00407031520824440c89074a86920814182c1c00030a100031907455881c003010406c0005441c603014804010001582501906c1486a07551004000f91102802e013260f90607a1a205400140c44044d4400d1103e0403000940b5440110704214270300b540a03012004401c940e130b642441284034400000c100c0c1c01c40c2c20101505019000303640410012180b003030004d54801540b64040e01140710014045800d00c0c01c18014403091400f16074001030250f032581c40ca02607035415141c03903020311614041d10083c0d0354040540000c2c080c0d28036103c5144000ea40301d094480c420f40c1070b04089991200d1560990352a810050000d1540c8590543d549030a005c415a15485002d41c1d103142d2401000e0214840e24420f0042d0810641c01c00040c42c901003420005500510300c11702e006092203c2000000c4040ea805e208114285000e5100814541c1d03101e01090b8501c03c05410a04c1d1002c0c07190709 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 344714316 1250 344713066 344713093
    0x3020301030c090515090624031b09130209031504060207170a0807030b041e140c030405070506090409081305031011041401050f030c090109050a060c02090c160302010203090c03 78
    0x401e0010070f010365920065845150100d009005100058400300841c40462304408450700000c40c46520407101109041c0d00614800c0300910440030f01030390088500904004144c1258010030b8866001004c0f01c91141c14800750807a042d100b00d9068561036800320302c0c3c500340184941031403821401c1c840c81c180303404104040900402409003000c03080566501c00140907458903070090100300150901c4018001c081406e900150003d1800924a080c400010a443d00d11000943c1d0103240c1c008090b204c2a070400060001c0c1e50401040543c2c8030340c49054032004200198014440100b9041294022340d06000c141480c00f40c0b500d0300d0a6420f8a05441c038941c2c1c000d200c1c142c2d4152600400d00307500e05010500100c032a0b000d00041c01488030000002e000c502c0303601c1401001d0904081e250500c00c5a41c50b030410039800102e103c2c070408514180381d40740042c944100b100750701090001b11542000701340020f1035503505c585402180943c3d400001c1c041e00140400a21400300c404034014008802c3c00c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 344715566 1250 344714316 344714341
    0x201020d1121100803040e0612010903080c0c070506040306020c12090a1202042406110604020a170f070605040618030512250b01030b06010c20180703020301030c0905 73
    0x1140030303100d10102003c074100c000e11908450042203038104481e1202e854510030300300c008040c0c4401784101e070704410200c4800d5040c0111200c00e40c00da02c5003200c941d244490078400703500c0344800e0061400382e0320340400c2564070040a0000345003c1d40340140c4904901c1c0341c09280c55000c1c101c0cbe01152805018440c2c141c0d5440b030006e4251440c01c0403042d0791003ea480842c0c003500020841403c070800e600d000051100043d6005000c494542e581c0460704c881d94020151544404c0d039002e5048a250071050150000224621810418500072684d0030803a0200042c00d181064012a00150001038204000740c0e00c5031100502d641203000d4455014655a0341560ba1000400c400ca1001c4001c00c1d41c0c500c3e100c0713500c0002c440c0e180d120283c149401c0d4914110b0100702003408100c808250080100360954440c0d1039070b00c40305e40d200f00b20340d0110100c25602040940700d02c0701503610000028181c2c120302440b41c03240b8001d00e0251005610fa50440c40d0904000e07a1a402c52a542403818041080105030340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 344716816 1250 344715566 344715607
    0x31d090a0902010302090a03030c021f05070f030e031006140616060c0207030b0114210703110d14010c030e0d050301030b13050105091b011106040809041b0201020d11 73
    0x4000c0050031189510040c1c02070702440c504e544e4040c0103803100006140e0000581e03064103200302c4903400020399115001007100818070007180050300c240141d030000f600d120403c840c0740c1d000f07041c4540c9903c40d1100203850081c15280016405441c0d503010001000c06181004041004030b0b00070303043c00c1c5c1b000d00c0502c0503901004064180e03501d403080145058000d1044401a42e000800c0100940e1103610300c42d06410001041c5016502180325204c5500e141925003503400d4804015011492440c0c0355006418080208141d10844050207440019060801d0844c80c03442c100000c1808144820042e04447d880e6581d82443e400015007004625404021281920f611880019040d182e281180005074407500e0001d0440d8a0102400101900019405600c0000c112010540b0080301e00440d021f03100c41c400f8418582c0070340e000c6030029483c6c03000340610700390141c400a560410184810020010604500701607507001500d62900391207401020548416940410304e040702208d40c840c0c0e0042e02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 344718066 1250 344716816 344716831
    0x203030a0207111c050c1e1002100914060105010918110706060305030712110312152e02011103010501030504060603120e0f0a030206070206071b12031d09 68
    0x180d88041100d14490400c4029010340a200031310b452114404803401d8503c1d09441e40d115000401c0b0491801d056141303950440070190000b40c20032441401101140310001c10b0960080705001484684941300e41103c071030040070034110b0300d03007004492810660181c0040b810030a86000034010b40d07218109180070805154800070701180010008165070041c400000e00c01c41c2420000401d1000020140c01024041e80541c22601080c0c1c800340d4a12100c8165411241c00900c0100340b10703101040030b558031a903c000c503198030b0201030340007415803100c813600d43d18918080085902881d44c0038035004ca0740300d0380740020080b8070030720070608809001c1441001e040640700c40c00501045203030382144006503801340e0180302c003240d03044026000c60422205140a40a2810850014a841d2240303000316034018081c145440c40d541c082c080c4992203450280d07541100c0d18440a1600004100c040080a642c09018119006454000c141060030b54031991000ba80b00f4404801e030384d5450303420790130030b44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 344719316 1250 344718066 344718071
    0x10522030207120b0a14090d05130e0a230c070f050a0204090308092401050d140a030906031b0e130e03030f0703180f020d060e01020327010c0203030a 66
    0x459103012490500750341c102c11111120724065408000081c070080d401071691104c1409042030040c506000e4071012203554401e507101c401c40c518824018001441c000c1c1c10400b42c2415076031281d03110340c0d103001c083e104440015a035401c0d10485400306036807005221a01c90307041d9a01e040c0400c0d070000f203000e8400e000d8482004911740d40f0400c44100002ca40160b4090424403c0c40f00381c0c04c0160500900b202c40c000140030f02000c100000d0310355840c000c2107050040d0f80a4484c0d08100c144004101c4044003107460418200010751584001c000d0030790054030075a5141c4e18542000001010b440d0200811403080c1024004800180d4101800c803003190400d8582c000160713905242c52000d4203401742003440b240000400d0040008018950500c20142501c0508c85210106014002d880c820b001c003500d0588025030000c014940000082000e500441c2d021a14524405415003240e10a035403200c64019400c5403450820205030b011f94207000e0510080103101c20003078010b0740303910008003084050703135 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 344720566 1250 344719316 344719381
    0x11d0f070c02270a1a010c051e010b06042903010506090904030e0613080601050102030f120c0403061802120601050d08130e0907030302010510060504063209120105 72
    0x2101e04080f5055200004162868100301d01c02c040200350840340320903003240c052821a10355001d01c0500710316a511a00401d5414800400d0000c80025104c110400b5520b4030030395900351342e5071000340018088404c1c40301c000017030300b20803112417003207000c01042c07030060500040105584080917603c2890068444003070035500d42c6030031660090b000440941c0b203040860764400b500010501e10781502c088a0880e003843e40c0324001a42c1c1c3c0c1c0242100041c10600c1001400000c50202c05104d40007801410000e01b0135403650381d41426920310070303400004d425008221405501c2d146041000011000000e01100d505242c0410030303060000c50060000b03e00010200341c00314415880c00d00a040503401c000080c104408459111113191005900560034007000ca03d98810f681c0c151012600540c44091602d440c100007a0b81c070400b640700b203070101d64607070f2440d10802c80c0c4c021480c0031400b02220107540d00d0141000f041601e4100c40000d03803180c0c1c0742c5802c201c80c81c869500e08060071580d0a01a030a083c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 344721816 1250 344720566 344720599
    0x70303050a1b021203070312020f0306011d060d0e061302100f12050903070b070302040e06093301020708060105030303070c08040f060314011202101214011d0f070c02 73
    0x102e035400402500003c580c1501032003008080090043c803031095407030032422688207503070100f40e003c0c0d0005076424280800204a00d0740c02050031200c030425143c000001d84800f0000520641c000000307d003c21a11800ea182c403001d41402403c4c0d01c1412005402100156500895925490380b11103400740080c200c1984411409200721044290110b00f0502052502c45105500c03034004600448030503d40070042610f16003c0e0003554103489622200094550b16802084400f1402400080e400030000c15102800c0c0300500120622000c40a003400b01c0b01401c00009152544030b5010715459004040140034940d000b00440c0d411544074074200540620340d017070140e0301e4495948069548512018006800e03030f01500f0158a5042c0010945c2c1c0360707030340c40c01007042140400400951154518101102160080000c1e0b902c440c0b0358180016400c03d040030300e2403030104c20780200c201c0401d590ba444200003003020711243e001440303040300717451414000380203403526501c0c0e040284100740c3c285010000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 344723066 1250 344721816 344721857
    0x50a021e01090503220e010305030a08061201020a0e2107090c051201060801050a1d0f15030a0b0406050109141519030b090c061e0309012d0e070303050a 67
    0x4003030f00481035a0392211003252103208000c3c1c0c1030700d07103c1e0300111040000f0311070f440b290524100c907006009103180900e02a03080b500b0241c001c1138181d00010040d56007040faa001d00c00340070155000d850f02495580b080c010003505408249240054100021080c0d80c010070205584084602c14840400c002154140694080c0070344800d0b000300302c1410000085040d44500c035a4100e607030076203900c0344298841d12041242100100710960010100b0045a40c0c40c00c1c1d40e00f00c2c0d6000d0300340840d6845080000c2c0020381070094590080d0740c00003d6006001c148401b41c8155070041c90410405c03c4114182c880308030a03050000c081403400004004c41102c0c0c0e84440c00c520196014000101e1070154491078601c1c4000b40965070359807603210707a0518014070306000040310714144032944540488a2036a61401b00399200405252240d500e6054425141000064804640b50400301e880c51002e0902c100000300c8192040c21000c2d07500c5180e00f0004641c020040729100445032401504204600a17042070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 344724316 1250 344723066 344723081
    0x6100e1207120b07030b0301020403120503040c0513020d1407080105060c030d020d050106020c1503010b0706060306020a110d0906050a050703110609101a06180a0b0c061501050a021e01 81
    0x24a00608941101080f00d0302000ca445014640c508001220003842070600700c0c046c0f40802442800c4080c0307801070042c05074001e15030051145e039614040540b02d0010800070004943d03210a8a5000324404401207602d024030800301242003080002031408040c01070090710f06104590007100700141c1c0300510380041c0200c3d110100d10078415540c2d00c000c4449980181424440d04005000f0324100900e14644034041540b01500015114110703402d02c06100d0f50b56028500c2119241d40e81c41000000071000d0010704001001900d442d0181242e00f5003650401079125040008c100c2403050901c5103075081000d0360501d07032503464040d498042d51710701504c022440c005140001e208005c200400c410300048c40d50422640d00c501445405030398540820790241c10707642c0da540300c0c3c003c0c003007864800c1c5a1480350410103802008950056071714070b0041c0303055001d6a0070349a40d4006204000b00c51509081c6200035040c280723003551401c0d511b050002e480e00700d0826a502c4a15032408074400f40d0000350020403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 344725566 1250 344724316 344724329
    0x1203201c021c020c1506032a01020309040509010b0a080d0206010915210c080106050f1002010b1008060a051e090702070b1605100e1902061b0a0b06100e1207 69
    0x15681c040821981750f0f41d641c0c000c8061964070040002400b41d040110310b440d1308110f452a80c1200e600d0341c40b10b6420303a5500d0126641144001d220100d81603070b6600480c0d019540c41c400004100204600703201c074001541e08141c0391a40041d900700b990360360000302c050448040c3c0310000b8100900111042907401c480e40a601c0566002e082112041c08085918080324410f0b84c06110255450001e07034240c484512410368002c1c5040c0c0c203580c150405215020000e1034920001858a0910000401c41c1094402c46000180402e017003208905200d0300c441c024000480306d088088400b41340c000800341200c5c0c05a4005c401c80004100c05038001c00012018010702820240c070b604044246801050600301e00703455901c540c204401072001248600350321900d160010b0614584800c01c2d1202d02c0c13503041d0341284c02001c1009811103801c9a0705142c281c81842030050110b641c0d16003000740e1045030281400703210741609034000400a4100c80030000461054a2102c05000b11101c054185016a845403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 344726816 1250 344725566 344725571
    0x14070f06060303031415030705121005010609031115030109090204110d020c07120c05012307060c020607090509191806020309071a030a0f091203201c021c 68
    0xc0209074143c0c01000c45c07282c01481c5c0c2d2009aa40000b401d003805048118560180c000311014407640c2024051190445100c000710707004d0110603030b83c500032510241c0c09500000c3c10400c0c140b00b0000142c0052403100700454810b00d08010780001042d0b540b1040c0718414089942c2c0900404540781c03508848100f0384100000703902c8103081ca2004c00650302000380c0f80d032640500c1c0408285214007501200d03200e6044200302100314180001036800f40881c1c806000038090307400410b404400d9101c01025494454030010482103a501000b9150800c0645204103114400d0f4060100d0340320880740036070210801016150424405110000030044041c0c0c0c2034400d9a401c9600e824404640c00540c081c080b0740d022142c04698445083c07051070000c900d180c45c01c00f000c00126520070b4054000003a07142d200c05001070500460340ea0141800c41009100001c20348450b4100044c0410047e084e01d4100b808030541e181c0074400100900c0c45d20001c07070791012264081060890b10359118070210300303003503610400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 344728066 1250 344726816 344726819
    0x3150f0a0806071103030f061c061503060e030a0c121205100e010605210402040e03031905100b0d020c12210705120601030506010e0d14010b010c0314070f0606 70
    0x1150340b510b074211a02c0f40851802403000e000341d40004100c0c1e10410950480c40110346940c401c010107048801d060202e17140d804644040032407460f21454540a0b428030048611368074601e070400985080c001d050480350014408040c1103038003c8040300419500c403155649001000b1415a5654035520303e41c079070240703040100405800e00ca249401507032203d0548440aa0f84d91504072010310070441070800082920390a0704141c2c0281c048681c1052005001080c56140849601e140d5002200c0c400d20000c0d0544803901c10609610031540c116541c944184003403410a007030f508140c81092081c564495002880c5800804140702051291044024607540da080741c0500d84206048004082a0341540e00003084200e8020b00c1101c5c1d08035408443c801141d61264015401054001c05040c140803d50207070035000d61f02e124840780d05070b1040995212002c60080c00a0840daa008403c60501102694400209400542600041005060b066076070559842c11000204d207800c80108030f035080090 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 344729316 1250 344728066 344728079
    0x1b01080430030f060b1c050406140f0604050f010803090112020d06151119020f0d1b080c03030a02150919030801050915060406030216050708150c0f03150f0a 69
    0x7182d01c403070340d0f61030040c0180c5444a0102c416032207411090044400d0640b200640640d058000580c4a801500006084145076030308500c2100200e0b0300703100d00d0000404003c81072500344505500300800384107480071581003900c00e40d5284a020603072414454441184180003210384c04484030400c1c2c041007403000c40d90f40e40d004d100038901c910344140401d4250400e543d00700c2000030044500c03d0010b181c40050f003001d800b4080316003c10030350660480080300035000814a100c4161a0403681c488003c600d2915100c8801e091015156540d48641c0042054010b0305500094002e01e55a5407400d00c0203a0316020f440d02d280411914410049100c01e52824080c1500519814100d41059944005940da11121349070b40206035000c0700d82c41070303042c031080c01000d2103a4054044071001d246500c4070140755403142c0c0d203047c2c2c041d4440c1c02d8550014420140300d1480d040c01c141c2042620320f2107428001c2071420000305000007041c81c15244004030700c411071545c5000480f1215a00601102c045d29201d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 344730566 1250 344729316 344729321
    0x3071505070311010b06040603240b090a060c0f020f010c1a0f071809241202030706080c070b2805010501080c0f04032006030a0e1b0108043003 63
    0x1c20a50201d603106607107a02840060086031003922000341614545810614113400420800c1c0520303038209280c440c0e40308400703108a4418003034244490000d0720303000480100410205a07820450800104101c1d2400148910403441036075541102d184024600d00f0004071154840c140000e0f246540c0b0100381c001800d40685440e01808003c0da400f0400d517249407003500c800b030410790503c016520900c2c08200c003a020f0b500820450749040e040001150050305440003c9090382c000c056807034000810001149000c014103801440e650911304040c0c50318500040c00d0340115400540349401d240001111000140c030f0580c40c11400103846602c620450000d0b000800c030900800e1f0214000390049452442a0070030b5458014603481c041d441c0c1170460351007503050708014480d04410b00c0521005006030792850095031203041115800905803103184c404501d09a07005401c5400d04071400507007041030360b1007070005a0103038008a000c444548240110303100c042005a01c45407050701c054401c40d0302541074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 344731816 1250 344730566 344730577
    0x303030207021305060102061311062701170412090b0304120e0102070b0f0d0b030319081e06011128050c0405010e1308040f06050a03051303080a090203071505 70
    0x1d0381c01e00e02da40d060f41e0320704003102d0080d1051030240e801040051008500c1c0b00c94455940c4c42848003007441020364000c681c86804c00d21150011000403045220484041001d20503007a1003441e0000c00f84203203d000100030400a40040c140941100034010014021700401c8000e045080c7c0050362494241000c0c444114007090110006d07108003080c00300c1d50300c0001c280b01500d071081211407070180010701e4080a54481480350031401c1d120202003d441e80c0600c05003a60024005201810340d980c2c4200034022000200214010012101c2074980c0c10b801c0880550702410030b081c210341d40c804e03460600b49849502401006640c10f011200402091940740b4801424031603800c980005640c8000c000949500340a500b0300d00d05d05800082d4010791078041180802d01906078585080e8503545401108802a08000b0120300e000a120100a5241c401c442e84000810004115108559002445054050001000552030381880e20039581c040c02801c0003002e44601151004511000180098101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 344733066 1250 344731816 344731819
    0x60812090405100e160311030108011b0207140d1a091b0915010e0a0305030c2109030a11041e0903030b10020705010836010b0a0f091113030303020702 66
    0x601002c1070b07642d0031408000c400e0315a10580d503500c0d59243c017400201c0b00d0300c41100804040d02d40510a5024141c00000e501a00d0440c0010071354035035481e000401140300c0c801040455002d01010000d07400c10b98103001a28074205c905501e540138904040040384282c6402d4185242c2640910101c0e1200144102c000007003841501c103079844c40010000040e03c1280d402c0381c0d140143d800d10030303198465500c2101c0700c0001094607403450784a840313851441d04645080007955000d00001e80f0a0700365551b4045503844036245c00791030082d80c80c0109403900706d4024001c1068099401010b41941c0f160480703800020040a401003040320b039002040541031a41044c1c02181c50007d078032445003010820b1b101c031038000d50010016103103030000449031341d40002c003421600405004011140310480c1e0444075080118040031400c100801c2d419030864845158031882074040550420400d403c1c8201d040460300810000180d8225488011a10780314048240040c040c0d141ea0105c201509940981040d500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 344734316 1250 344733066 344733071
    0x1603030801060207060c1b0e0c03061c1505060a090906020d0606051612051201060f02070509010609120204020c06010305100609022a0f010507050a1205010f05010c0302010608120904 80
    0x2d072060240d8950f0968040d410015036800041070214801c03401c41c440369205481c80b070341d0a40d41c0b12014808500c094a1400300c86500209109192900e004d814182000b807280e03017003120801c0d0f81d98028800c440042c08580780e860300c001840682d0b85510035001040301d1003090040100c0c500d0144003d44c054116910520710302803010540328820000e0340e118904801a9007440d0806440d004a81c40d84100a4020400d041000c2c074240000309501c2c0340200016269608250b11029010b07082c810310f038010302c0c010304591004011031075004400c1d6049510031040c0840c000c00c0fa0002c600a0322688844c080580b040c43c00000410400080035031002c411660108080d6442e041d0803026841031040e403a0f000d4820703003540d10f0214101000c20b010350402904440000100480e0070303095940850700303600031400c00b040344142c240c0c010040c6a4001c044400c10411503040100c2d91348003800c240910750410400300e0840d82054000d52014005d00828070031a00140707660b8080c41d0150b0b04c9403030194001d60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 344735566 1250 344734316 344734319
    0x203100609050a05130b0901090f1121060a0b0d0203030a0221070302071a090a090606030c0305100b0f04090e01020304140d020a020105090f0a0e06012c01050a0e031603030801 77
    0x200d207114050090802c0c041c100c560174a59103491a22041c0500040203e5607038440c0e41c00011801c46009000034803c0d540da1203040c00134001c100d41d1406249483e4060585d4404102e260300000c180380741c1c404030034000000c0c0d01c003c100120b055072441503002905407000003000700085800180362060251200040c0d40c00301c2d0071041c41c4050380200701005002d40d00c00c5e0405e114041c000004150f03c41d041d01011801c0505050002d5a007109a50091039101c0e5180750900903264580150b800d00c140c2410140041d081c83c02c1c101c0d100c050a440344c00614440030501649840d8102e0440d4000c110410090242c80181001c080c000d500c140c8049401c6503260b000d221510320017240603003620b1441c0c0c01902c1c0a48182d00151050351003408581da00c25102c2100440782c2d40c0340401003024010949058905107826400948004040e10b030603c5402150a0f544040b0102e90440c115203c1d42844c08903200c44a840d01a10315403410711102344d150007641511400910075010030402c81e4000c0c1d036039a0559 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 344736816 1250 344735566 344735581
    0x30204050c0c0d09060f12090f030e0907050708071502070c140a0509010b0d0e0313270e1b0303070b010305100510050d1e06052e0b090d0c03020310060905 68
    0x32104d841303080041450604846c5006009144840c3d00310603181c0c022030031445507a50041d5405440c9804c030045450b40190140d030b400c1126510341c0c020310324145680307046410f454440d01030281c1c0740f004184142605c1c16166850301c2d50140e030041e65005003200029a1608034003214000c0e031501c02e0340078440c1904009142e181098515040300d5244a07261718190b1200c0506024040a510004030f62000b0031441454062640c0c103103004024090744034400301403070035404001310851611035140f14208541c0c1400c1b04004156022550325106c5000c0c841140c41c00401e003503025040300a800c0101c400000000e06c400454600ba540002c000100516543c1c0d0750503030444081c9000c3d9540096040240350000b61311403464951100c1580d150b140410700d20b03a9050103a070f10032941e042c0103820303038058071041800020032658483c0f29444445151740c1840b95005d102d0181102040c401e441d60b0700410207200e03110b410240690f4010702035032801c0d046004584007810705032142040c820728140004088 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 344738066 1250 344736816 344736827
    0x70206060402090a1e0510170604060e0112140604111008090d050c030d020c07051009062a050106032405010b04060f020313080114010501031e020a09030204050c0c0d 73
    0x8a10004049640c40307805c00ca02d4141001c401e91800f007600d40281380c00701e4a0380c0c42c80c0044558045a070359004101c0300f03031a03040301200d1010341002c0c06142008810700005035a0103289054991100030b2440400950602d04005003844c4201601c500406c820b01c0305001b900030201c08850400e07503210162115070003040792804070890786440e072a007142d20800c05951060f0010040c48004c081200d060100e0001410101e900241c0214525400b10008022034202800c182c440300c1442d0500c103034031903d000b1020f020a0504484007808409001d0f13201003481c00d880c0e0300c015154002c4000c004a944a1410078001980c1440a02d0070a1a84481045111080c055141a11110011241440c2c94183c00b501d0b0300c4a41c038001019404207204a00c802209107808078014220310001250b14410309500601c17050046c0c02850400d4284a681504112080c03004c01c04c0340a40040103130740f110042030458042c40c2c20b0b08029446030521003846100c031941340181640c00e108809861040c0c0245600750351 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 344739316 1250 344738066 344738077
    0x12020c0d0906210c021212010501020712050c010305070c0503180406141305060f09090a0c0b1215010203041509030c08060403020a0809011701030813060806130203130b0f070206060402 81
    0x450f0f98541608044803245070071996140318580100ca582c00e40402e0b0441007600300303004483c80e44245100400031503904001e003400815120780c0a00d1207104d951280740e1240f08201c0c04a05068552000c10a01d6203e1070400c6561030b0400103894403100300d080350780c0e4044612005144164209200030400198038420460074040007401e02d030403130427543e0340b84010745401090b50340d2280556905003840d44425059030310440341c2101030030710124203148c644840c0d80140c102c1504044148407810344410440006904032040000d80100f07401001d00403807540c82244c0180514a00da6a0341e100c1140d0058642401d5a2281032400390007030319040704544e03d4508840240040c2d11000c80000400c02e240001c00c0901030614010769424110b074103404055001380d008485101000480e10040700303012956601600152900044509090f4005141c641d459040030f602d00d5400808500c030550855424034203181d00040c40859490014500c0343e03030b03030030440e186405409500005a001e24040c401c0300c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 344740566 1250 344739316 344739347
    0xb092a0307051819050f0f030303010807090c09031101050306040912032304083016110609370f030908060601050d0c02012d060b0c0304031212020c0d0906 68
    0x90704e00d01d003404104810307650f07060b200e0300a001c846003a041a10f060000394041c11040c40145900b5281c00410011101c0020600c02000016401880010a4021000c1c0c04000900c0e0460301c0c7e45442d00000c000303180399140242400c82518030007000a405820448144040110000e140350004030300400c00101100d0090495400704002d5132201001049810600801341c003d510002540702906c0c1c1e034040990780219042140c0f0114600d1703550103205c000344100004c024250038140250b029a82d520040440002280b00200345101c0400340c60b80b0540b915004030000114001e00c0c2445010148929026000113240c0c07600400d50329400104140a00c006941d010b00d071507005040440140780002c100310031552512008205a90101d440001d075120300c0e07110100480016030604c049a50325808625a41d405100d1406d18070404010340381120303080b2180c0301e00d00e4090142102e1012698006094661020407105c0d030341c8a001980e40ca036000103480300e281c0c641c1c66240503165407079600001c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 344741816 1250 344740566 344740609
    0x2303130501050307020a1e200a090203220809010906020318011b02091510030902220612150c0e0d060c0306091109030606040b092a03070518 62
    0x10080d0703500c03840041d98803200300d1064500e15040c650303c0c10030740c811940341007074000c5038107140300300307221200010b810a005140b088003000900f8002003074411810348944c5525031350101c0000c407405407110038902d9500e1500307070221000701e99240c00480b13074104030252400141c4100c0082001400001100c1c3c01500d00381c01c0d44203d04945004580681100006030803580302010000d006841d80f03814903000304841c02c03054443d440c09905218480351603001140c10181041c0b0350b0400358550b00f801d00300021200c200700c62a083c0540c49503001e8041540303c0980d0500d00800503082c00400c1075540d00101340c6000c24404c140c14420122110b0002084d4203a000e0f61a46c9400300040300c07a8048a0510060709011481c16903540107417044a000b056074800c0d08100260328505032509000c1140d05c500102c0341000580309400104181003001040031441c59500ca40140c0d00c50440d00303000110f403042c85811980c03490400c5000b0000d4000242c140722150601640d95513601d8502c0d4080924039400c800c5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 344743066 1250 344741816 344741819
    0x60f0b0a030f050f0a0e12070609050307080c03070b1015120b10110c10050415050f18100e031002090406030501060905010608100f05120f010603230313 67
    0x980c0c4944160380a055480c0c41118200685004580c440d948110b0503202d20324245a01c2c1082e94801d070440507041d04104240e004141454099406007074201c400011442d000c0e03d4100e03d588600680500823a0020a116200c01800002000074920900b00b2417041c1d11350b1001c4031900360090080f1424084400704c4140c400f0711481d44200c56035561240031444880300008035042400e412280300005401e0407029448850070001d100e4101c4056031249008c150088004000c2d008a014001104600d1b03001195541e00c2213050b0b400701c1c900d14009a65407014164003034000c003083c070765160241611807880242c19002c4e610140c005040034001c0c083d907031800103e40c402940807509103680700e55544408004103809105207005495140e900042a5040c840302030107010b0018144210300345901c10900035041608004400c4940c00d0b03603040a0701200380d60540c01d2482c0e0242080c043d61802100200b4803a0544070b010900e0910785c6a0660030f11000d41082d2244524010410304140f0b4900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 344744316 1250 344743066 344743079
    0x1030506030c0d0b160816140c070605121602060711190506070e1909020304110d060b1f0e09040f05150106020d0f1b231f060f 56
    0x4164002001020398100300c40740c100081c098260050141d4441202c1010018000c2040c2c8080318001c1c01da040415051801f11421080030b240d20301c0c044104008110803000803000f000c156a103102d02c00060703d51042e20360300000e10940154002640c480d1907600841c0400c181100c0040070305009034080c0c40540c0d10094140c4001e0058181c0c44102c1c80390120710502c40840540d01c0d25802d1040c0701a102a0400b10002451803000d01800d600c2036096800000c824011031801c8800c981004502503103a031f64a0902c1d404800702d80d015140c1000d10071100d2000c00c01180e000e241901c00440e62030503448031074002414000d064a030600c0c08194440c6461019180c0359006a03405841107924080e24a099601c41303040041240c42805e0080c0c0041c0107008064040c056401c0b18281403409071403d51038240002e04051000324a0343d407100069921744213002001d14518040a608502c0c001c1d0041303c68005940c480d0300f400e140003003030008103188060318100d001d07a004880740c0380038024100342000c0303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 344745566 1250 344744316 344744321
    0x1060512060f0301061701060f05030d2d02030d2d020705210d180c030605070c0c0602031c090b07080a27050c04060e011503020c0303041119080c0103 66
    0x140074079032282880b00750b0034256509020303030320141c800754864103502d8000140b440e003981c0640d0401c0410001c0c5003c14012500d0000e5000d1680310f0071315000070381c1c0c0f000160051400c1d0780b4000c000c0d840407507030400d01c02144d0000004c0c8a090038034481080800d00700078102c43d41c14613458580c0160004003100d24860191500070303104850298043c0c52412210b44a40d03450040d44c14411003e0f0702c2d010443d40c0d801c100520030002403a602301900c4820701d00554615800c0c3d506c0b80001403800da41d036004a100745229460141503983c1c041605d03800c031030320f40001030340c0e80d00900502d244c1c1c1201c08943e6990324034107005401426a0100d5610641c2c3c84440c01542c00c013500404110900c5e588a1580700c05c000580e00250070f01e580340903818401d14480c01d10504103140e1841c4ca03405141030540c104414424500950304580d82c3e424400c81c0007001103401c8010f44552030841050f40301c04402e2006000285450103c007440499510400020046412844180e60700c0303980900d401001440781c0550294 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 344746816 1250 344745566 344745571
    0xd0507110307031109010b0702010e01110c090a06080f01021804050c0d020d0902040e0f060a0507020309030102040801020a030e0f100c031e05090c030a0f080924130e01060512 77
    0x30042000d0645205010034504407503030f03000b80d031203901809680b01541440c0040d80c0c09081c40181e21841c2c08015000170707000c149a04046810000c02e143c08540391003003800754011202000346440c8150606100000141160380142e407200d019640c144e4240c00780520071911100b2103490700380720510230802041700400c001401d041d20031208000042c1c02c00210b100520401c5020b08000544070310310300500c0101c0d0b514030102d480d140d00c0647c4020040c00c0004541d07600240048020600d95500380089083d4065883e48540646c0040341c007103a1050190064905001d80d69001c00c6a14214900709564412085280c001c94200240c09906901c00342c10020400c840c03410045248121003800d081642c03201031030341481c0d41d90f070310600c500310f1020f210408031540b04a00404203c81c481d00c0303181d100000c2c2a802040000c00084210543c0c4a00f0350b0342c1c0007110746200c9600110303100c0303140394a158004501c0c80c2c240d86820754040350002480b103a1038181c0766160b0b1a10700b40035044460001d01d0502 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 344748066 1250 344746816 344746823
    0xb011e020313030819141e0918011e050a030602090409170915190c021917160b041e0b0406030605040e06090606060a0e03010603030504081e0d0507 65
    0x100440c21101003902d0100e0011403290b02c600740e491051600034119034403000400340400c0020042000c621806a0903500c0601c160304038440c0e040b4065614006511442a400c3d0700101040318444022001c401094100c035405c204100514a5292010101c0c032030303a0050030b40c80b446044051002c142c2d903501501c648213003d4800200110309440340d1a5440401c50001c003d01d10010b203030801c07407c2840f1041070f0f0704201030140e420a820246051200444200090100324014103001f0940d5640c3d1540081d200c204c9403002c5405403164a00605500c242481c010703184141d0034401020050300d004102110340316690b41d802d003410320303078854401c10800e056051510907444000c50701828160003440180015100010a980740400f84030664641d0058039100d60010010010405800311360740303a019a0441c0c507569071342840300303044e140341c40682065601903282c07403c04000c1642001c002c0003a2090b000860710040b1401018650154104148040d26048803201081e0b0a0142016142d0b4910 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 344749316 1250 344748066 344748073
    0x30506010e070215220b1501030515040207080f030405010b0901060804020a0317070209090607020f010618020a18080601170303130b07020304031a0105150c15130f0501050f09010b011e02 82
    0x303a40310340c1c855802c454803e407606d81c500014045070b4040e11388100d6108600707007801d2010b40780604d05076105114920301980125000036100c401c000450040b224943c462628072900c0c0e08140c14054000d02d000e100c0140540c1c2180c0001c5180f900504d2406d00c640d0340102496481800c0d5038454644481c020440200c010040c4144401a41c510b000e00703210322000d000800980c50035400091501440500e1390461340d01d080d2003440b00300603001d070022001c1b6541d000543d80c0e41180e402224008101d501880c0ea8040c200800f064220f008030340d05040b00c0f0441802181c008079038242644034030081d1928000800184080000103805400a5901403420b0058034242980e0f5200c089440b05800c1c0440643c5030054011301c40e0b40f4203030200f1100d25132512045400e02c8520202c1640d14404654007000712030384140090944041e00002500d0703244d0108003524905000d1402a0103010705031201fa00203800b07140018500d050520039500c0d0228140d41e900da2aa40403911301140f1103648200204600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 344750566 1250 344749316 344749351
    0x30c04091e05191803080f070c050703110109090515010c02040e07080a17070302060f1512030d050114060a1808010509070f0602120403150b03070609030506010e070215 74
    0x61962040074070079200450010207541414860804403021040340c207000512410b044004a548a9200b50341f20760314815007421500c2e0010160341148901c00002c5c200c1c4540c0401004000212030001c11000c0280c0303030326010350345640c1034906982045070f048813442003800842c1400c0d8403d00180d84c540f4000380002813220405e5103601e0500301660061030b80b03507202d02c004004000048904440c4070024591350342c01c1c242c4680d802900c81c1006058040420306001c0810502d45103003c070f4401c1090010041c5400351034140c03800780c803600031008840d00b86141500009102c90401124800c00c4401003c10317242640702e03030065800107903442001e040c1020150004c10554001d204d001d000d6200e1760001c05d4510b184c044103c8450300688c10400464000c49079036045146400c00380d60941303504c0843d00f21819003030100c56004116858003e5854030508100180017500b201d00f85040d0390003541503c107542e0702c0b00c0b1307100c040c988151801c40050340180c0302518a0350700d5144564200c1d44489a00075000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 344751816 1250 344750566 344750621
    0x3080a050702210d09090e1e100504111e0f01050a090909030e150a1706120106091b0206090a2409060f051315150519060212030c0409 59
    0x20f140f4090340702540c4d0040440d07040701e03900580f00b00000c1c05039207400d005003c00d10401caa102e807464001452000220000c05542c60018820f0a15500840001704001e02d407909214480aa84c1c544482c000c0100d04901c056417900d002c400c101542010b8135580500881d82c0044540c0d5225005201c2040221100840d0217506030107020445802952800c2e0f0810030a0208524401064a20a110308003008843d0045d500180c00701c0201800e044800260b5480501042039904034503c00384595103407210108511031158460280702c15189403a8200b092002c2d816a9104404e907200682d50344070510590000e001d4110019092100750042d291841d0b41d089424295680080b041f0b0b8020b880f4000f0011010103031041c0d5602c0510458140200600b5803554801d5008168498054035100d00c402d03400c00039103240e20fa004000141c103c12400311381c0703030621030500120b010304401401035506800c085000001920b02583c4441409880c141c03074080c00000a01481c001c2ca01012401001280324 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 344753066 1250 344751816 344751859
    0x3090a1407050d14072709060209030d110d0921081308030d18030804110f190e0a0501180b010e04020a03091202060106021b0a03050703030c050c0a03080a050702 71
    0x41489100c03030001e4900010200745c2070401710b411980384a80c05501a07003d0101028a00e00d0000500c90000f5012986061000180c07140c88003c40d01840360702050f080484e840301035440201041c80c241c8806041c3c2c80c8080b0b903200c4107072040300074001c0c44007403a01d800701d0580010443c443c40b40b124540b41c44a800f2429282d079449611100560300046003000c2c4e006c00901450340380c003480c1d00401200b0040c554000d410390b08003a2015140c00842001c4010f680c0703030b07629800c50482d80100201400030322403503ea0082c051500482c2e4801141c407002c1080442680586810303203580c503600d4054141c00d405141c00070194805400e040194840303084446440e18401803c00018070303580400c0c412168105441404210180d800866002074010171403603034081503e06c1c100319100c80307040c0701484a100042c03c0400720b800c060124051142c000041681060a040d0a40d110b60b017075510303400088080000040302480003030a207080c10462409002e01c5403000700700240c40244102e0801d21140001c269 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 344754316 1250 344753066 344753089
    0x17040e18070f0b030a090c0305060c0703120209011b03050d05013201050f0d0204030209010801020a110a03081b0c060405010c02010605042901021c03090c060503090a140705 76
    0xc54469a22080d40425090003050041d04156103500415440c02c1e09200841c03200400d400c00466071100c1c00401c004010b00d8601c01541c0107022240e00d400c00e903200100713592062008a010480507d40c1d6120072440d4000d0301e0955005031542c20203403402c420110462200b005c021070400c01c0170030070400902a54401c80c2e002e0505d1a4041c0444134001640070401c0c1540c041c94603c0e901d1500020480f0b0381c3c05800c50754002c2ca4030742c02940b58404048000041d000f1a00029840a6024000f0800400540c0a00840e45040d69100d10081c204024251180c220031406030001d01e1010000b00d960414140892191031426251407511100d24512800c001c0207440c11103840e5180c0f03030307480d41c0030354240150001740008940420840c4030140260454218940c2a15003040c42d101455515038001d111a1500c019401c01c0108000450b40d4010300400fa00c01040344d50580f5010040b807002e2045007968402c061a900034200562705488910100b42e03040040c031040e00c224a008540c5880e02d07115540c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 344755566 1250 344754316 344754331
    0x603020c0a0609060b0f0108040b0619030c0e0a11070b0a020f070609120f020d0c0212010618090615060203030406270c080f010209011d1903080a030b01030b0d17040e 73
    0x892017001c0c4200840302d4090300c103243c10000c0040c10700000c1403007882d07a02d40040086444a40b008404090449900260380c009040068040340c0018108214030a20740310f040812010001c03e8140811006c0a00030300501500302941340c0c000030b1420000d0b0b8010540900b5400c1101e0420780650342d500d05a401c8910229040b400c242c1444131156041010300d102c091241c0041d250342407800100820306544050041e202d0880007108074881442944008098010307902e00c80181d803034034803d0307001820741a002268560700e0124958040c9540400842c1aa400c9a000d1480c68903180c5030380001d010304150850701017420003018020b00b407802d14650411882840c440100d280382c21011f82c1013001101502e03103180d00400403003249aa1040328000c1c0c040301c04e0403030301c034240030340300495600c6d043c20622260095004e000807081c000318002400101c0483d82e0140b0641151034011000e541403200c805402c5044411120001210790030564400e00030040c001d814a60754440180c103010f425245034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 344756816 1250 344755566 344755571
    0x7080f0d020901020606030c01020a0b0a020712020a0309051c03180504050112060609110405060a03020f0307090302040516092c07050307110c0a1724190e070603020c0a060906 77
    0x1040b465030144020359000c88114003070101c040314140041e440b0041d515000f05180d8141d030010301c00c29000d505807104590003440308044003090041c080c0d030790b04140c58240c0200300b1101d000a61890450400f85400200d45504a41c1d9119541e0964101d24505000009500c40303080105664689105090083c09401b002e9207401d0703007034145041260116040044158107211510300d007900e44404a03011100c003515034ce6a1034004880c100d00038041d51496510f680400000d1242c4654808414801d5038000c0750204040e84500020f0006c10141d42c0b070f40d60209400e0041003200041e4614440b07424000c6642d12280c510035008401200300040f550b05000c03810103c203105040c2c1c0d00c2030286407280c1e0386400900625844000048940380c0038454028842503403140104404000d01413414001c0c11001c40d00300382000300011884002080340c5c80c01c1a03126041e00025a01001c0c0202d101983c0340e0300c0a00185800d0500c224007951010444442c14402c00e201400068031500c201c0380b0b29800360000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 344758066 1250 344756816 344756827
    0xa05010b010e0f0603010b09060d050103121e0f030e01060b0f03041e200a0302061303030e0a03390e0a050708070e04151d010812070c060507080f0d02 66
    0x15081c0160340c40464022903418491510725102d1401712415116810f400540f640d0000001550074490003a20400c4641400700000c20030810b078004402844030b0351550108035194080801c01008810114000030b4044030382d00840c02c0c020f6204507080811036002080032501da101000701c0d58480c0d001141c0e070a0000007080240090040c4a280e4848050b000b66543d1072580c40e80407501000100311803440c944410720041d03a40d1380b0034655000f0741e0302a0120351110800311402034170901d54801a0089a03844a2000c06441c3c034403e100d0540e903000401d40c0d264528402501c4c0c01182a00b801448100f80c04d8418852412580149006040110800e0854546150100141c501c06801c10052150318401e00424540002000800d40c1058900040c09110072118141000303541d8084280c0500c0c1c42c0c0c900e0074000d80e450000d030503070368028100ca4074258801020b20940c030544c0e0002d81048814030085c44420f1091000b000d040b03008061440c1000d502400380246540301e01c41c40d41006071700040c3c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 344759316 1250 344758066 344758069
    0xa050c0103050c040b090a050a0902030f1006090b0f0d020412050c0402070f060b0102150a09140c09160201020904020a05071a04020306060f0613031a0906010807050f040b030a05010b 80
    0x122810020280303410702c49403c00c8031100c640c50056020300e800302e142c08181c0c240b95407558103040c802000010503580d82c00c0e9617074a01400950003940c0c40145410400000307682e013802c07105401c1c200d503407581c3d07110001860190880c2d8241c108411040c14444200185001d402050010317001030000c040011741006054584203280c4040501454051801405003901107928040c4070303508240c1020700410b50182060040b802c240a0307003080c4c200070303104d4002c0c058520741076403040c92568841d620070310143c440e4000c4561741d0780b5040c911581c0000705e0b0b0002464203040d8114070502060500026051110500000c0e0a036040b403903844e40000d801085c2c4809001324111000384118a140d001d43c0d880c140340d00400d40b6101c009145600460400207541c6030b5481c0c003070440f040ea180b000005a40b2039182cdc6406150300308000e940702c0e81840e04102180790070303801003030083c103d420780c074010310a10313140c6010710101440d03503419198015581d0107250116101449000b088600c00d400002d00f00e81e1500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 344760566 1250 344759316 344759323
    0x9020d02091008100e06060f0d0b010b0c10060b0d0c021203010810181214070614041115040302090705090904031e0906090302090402040e0f0a0302060f042a0f06020a05 74
    0xc1c804c41e001c900744124200d12500c007060740b0790401c009036881007940c544900400d6491816460050640c511a03000184040c105e20152040c03000d10020303151005c200320051010f50f03049010360440084104100c1540e4492948006445542401a20034052a00103404090341090788841069000308012140880141c420882199810080e9210000b841c0d214040d4100d81035420400b401403000c20045c0381c0c0903003400c6e1280f407039114505200a00d50030300071701c203081030079a0f046600781590450a1001d01c0d148038003d2000e0800b41c0c22500b017030310315000c00400c480003070004418040700700050345154513503010305841140070752506422048001d69014810000c2c600c50b00c10402c6100c024000507500c40c0c0007100300c070380480c6c0c4c21089803160b00000d001002c82d9150340c0054422001c2071040c01e80049103010103140a6000d644c43ca070740f0b0801100c040e5004541c02004800494440a00800d000300500000301d10345075005a0b540d1600180244108aa00036401580c84100e05008124003007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 344761816 1250 344760566 344760583
    0x70e0c031006080103030c141c0e0a060f050f0d0b100c030e0102030f27030a030206070e1c03120b12010b1525030e060f070605060a1809020d02091008 66
    0x40c41c2c00f020543c510749008060241d0444010074400e03000d0f440d018040001c1005802c7d01404c1c0006000032100c03154050720151080c80c0b024018205588001082c6004030040000d004543e25180e180c0400c440904809904c05841500e05950360008032810f0f446d040561200c04100762a0000c40320442d04002e0b051600e80c0d805181198010801035a03005421415a41c410390f50f2200c100600c0380018218400585180c5095014410400000285640054180c0c02005151941021070a41030240022900c614941d001319950000481000030300c075106241c42c5000700d180015070302008100040c2010000460041c40f0f03034440395185018038142e47c1824016020400070751420b004841c0340b88128400d15403071711361042c1025444c0b0516004032000c400d2510000d00350f03952a5510b16000250f40c00512041e12034529001c0060070318200f40e00003405546a0f0703c05001200340d50f116420140030411022030704411700b034200f6401a141ca0351028080c6414054403115281803c00092505c000e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 344763066 1250 344761816 344761829
    0xb04050403120c0905031002070c0905100b1c050a0f0b04020903070302012a0c24120c030603050a060603030813030f05030601111e0c01030608150603070e0c0310 71
    0x6010a000001c1d401c070300580600b41e264000420041d1002400741c690780340c154892601801202c03900d140f240c08503801001c0c100c1c42207840e41040c544803450a002c84208030b40301c2038100b00396a02030000e030541d203000d0603044800c0080c0108512080c0a410155802924202041501c41ea01412003c0b02805039040c81c03c4203403011810240c84000080d594a990700c0047d06110f2500c06004410303c500c8681d04156800d0101503c40c4416403030300c9082e4088904c00d00d13149000c5550700e450255a401c641d1508030f00ba6650707098901502c0c845441c000c1c50908041014503986590000000c1c605002d601169401030f5000501545903050280840200504124009041014410010b80c0102002040003414a4216101d41d1004010b0385e04459251350f081d183e108100418100b10b01022100d0010240380080d40e4a1110681c019015a607032401103040903040705190842440a52940c4d541c044401000c60301c2c0269110a0803664410546018620603400810400601d00c0030542c2c42c018843e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 344764316 1250 344763066 344763071
    0x90f0e0c04110403060c0306050d05151003230304081002040f060512040b0429090f1b010305040c120b01030c0f0b0405010c0204060e0c040302031501050d151107060b040b04 76
    0x306600060b29116500004014542d540003030a1420310030b501901c05050017800d003441890660404a68641d03406004c8a034544106d80000c4030b01d00517460130f0046035407100d044002000b005c0e045000782e0124100599180c0710034400004c4004081000c0c0f40c1159603c04010b07515810403800c1e00d0172810f46d8021600707000d42088108455400d6000895200d90003044aa4440e00d851410b040340b8000f001103118032940e0f5500c020b0b0382d1481000820300a03c0840203c0ea8411880c4a6032511800c10b00800b0045010002241030294000e402507a403041c401c14032a944640c9800c0c50305c1c40361045903815925003407010014010440c1c00c00141024000045c03050306594500182c0400910580c003c5030b04009a2451481c1151190703003001000d42103007a20841075240410402980b9045840706038428859074005000d00540920164182c620150404a0f00786490304c03003103094800958035094182c1d6031860b0046400140014000151140c0000728a040c854070801c401e6641c51400b0500c180d2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 344765566 1250 344764316 344764331
    0x40806010f03030f051c060b0406020f01110405121509011b0c0b1303030b0a0608070e0103050405151b040f141c0605090a02150306011107062106090f0e0c04 69
    0x1d80062040844980ca860015506d40c0b0340c1082c0451001d109802086540c140600441c0c00c514010140c0182c440745d07401c40c0d45101c4022000d0303099410403800080c2110003000705001c1810b02100303100041c400c010031681c03085102680424407020484601842d40d640d401c804141e0750903c164010a421580303007041c0c1401040d01c5040300740101800c6100301a036009282801c06001c0d8004e41078031034004001c01c00984e512880602404012554000000c101c4602d01c1c0742907000f4441e20b4002c580007002454190303000c0d10314603100003025001d0040307a0130020000c010000190002c1c0041c2c0109c2c00246c941f42c3c50321240d036149402070070819105500c0002500145c1943c11110300c0c1098004101090f00d0b2034414160341003c644410181d080040c0c0e500310904980e0940040d40103130420390b2900d6032103181048064550855003d001c00044400082c400e46102030070300c07140c07911540000060000e941d440200d0407a0154111034410540b11400f11503041c50a0103940140801a01c0500a11 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 344766816 1250 344765566 344765573
    0x203010501051f0e010c020d030315090218060705031c0e0606063109061d091f020309030d140406050730020408060124090302010c020123030705040806010f03 70
    0x1075011251004100482c4131000280c2c1c071407400c076410550081c0c00c0300800034013410014007400514036a07a0680d606443e002411120714800c43d4440401c80e50300d8000151030500b000300d039500008083c2d409210500c007200031018552514600003164510000c0c44904081e400d5090840040c80103100f01020b1180c00c11707081c400d544020700d520542c4146020300304900d0122402000d250042e6510f6450140045101c01d4850496201c0410340700b40000c40c0d40c1e98076402507852800d1102d100c084100b0402d0a000e00e00c280e00916008580c2c202038900304843e40310070764102c4604040e242042d40c1c8060a010a00040d0302c102600070642d4030304034040b11503002c070041c0052604c04d0641028a80030040c0009000d055050328040c164440c26241156035600003c90044003072007003003102c940e0100040c50141c0c060800744c800c590b81030b1160802c01d13405400650704a40f002108074204000e4010800400740d0050085110300f40b16219542c0b02c0c0d040c0050b0300e16000c0141c02284c075041c400c10702407020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 344768066 1250 344766816 344766859
    0x310151b11130c02070906080c0609010c03090914040312050f0105220e0c0a0b04080d05071407030b070909090c030803090304080d120b22020c1906020403020301050105 74
    0x346500711000405010000340403a00c452407081c2c0401c0a02d02d4500d00314034203680403900da4216221908240005501d44100c2a00c8101188109500640c10402601c41e035000b030807090b00c41402424028015a41e411a00307060b83c52080c5181c80120300c4808000425400c00200e03504409003c4040002d0f103000300c0d822000c114180511031082000c42400381303102c03215800120010000c100300340042c15091040c5a034a5114a044c18420b207040100890415420020b8904641c2c05038020090a160801c2c181c80c04e6104800aa90222204d494181a00000c1214500952151040620b2854544401410b20055401040380141041c42e90004550400045010303290440e1405a83e038488a0643d40b4510440c1d011a245005222583c2d103c140c111102c17102c403212564060244540760004c01c1030310b07000c98100e0f0000340f40d11011100302d40d01540c09010800000740c100c4000e4482110b220034a03c41030360080312043e070001801d10440c2400c0c0101742c0180010755120148089100c0c503a840c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 344769316 1250 344768066 344768117
    0x50304230f0418050a050106050f0607080d0504030c0b1611010209090105100c050715020105070305070c0f08090d06020c12030403021f1b020307050f0c0303072402031015 75
    0x1055071109440d6860754110010f450445920004860800f400c0c0e1810901070f1401d8880d07684900b0307a2503540b00c0a0700300502102e103000e5210010782d00c0c20a00d122010000c100c00b900c1074040042a070122070001d428801098001e0701700001095540c0c54a200081c20701e4010060220b4030390050020746802d440d07902d952070643c0d02c1200c4c814140b070650002100c81600070b400180c001d1103001e0002586880741c0d0700040300c003c6a0b5000740138a5441900603400d43e002a80c4140021b01d2800c1c3d40302c0071540c05400c61008610a1107414a00b0740c4840004103000044a0b007500c5a690004100315040c03000c01103e50441d080740c0030941585400c1d10060344400b000c4500c8031800358100380d004000316103544012240140ca030500350116824480080d1340f0703040350500f143c00b80710382c9000701d018880c0040d5000c6003040040003949090ba8660302e41424940400814100543c620300c070303410460b4540080c5100300e504017030221156140c00119419980b8004c801c0c402d010840140c00e600606160003000b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 344770566 1250 344769316 344769319
    0x604050f0607020f03030715050c03130201200d18090603080405060706020d0603060902041d0c010c030504080f0a03140a0801090203130609031e0e030325080403050304230f 76
    0x2e850320020300101c0c0d0a850504180342c3e0500000a169003004131041351801c6040d18290100441d6071110310440c140d22041d070324450079a04000c1003100541c0301e150381741c40f1b9081e28000c1041c403032401280140341154040141c0b000c908104071081070380764140141030041c4800c0c6800c3c003900746580c90f03070072040c403650095600403480040e0348410b1010030780407102d201c0490390707080008070b07905e0800030010300440030200c0c8200d041c0150078001c40548607403003809482130005002c20315140001550383c281c0c1c50318100c040c00760522000a5a041c01d03c60300b600c4030300c05000f400e00103020740790003008001c190f502d000c080d44040c0143c01c4c80d9079012a040b410f46010b03903801a502e0f11040b410308101e0901d10310041c41d2904100b608410107074045001c51000000a4003a4070040030907800751401d00b41c03c1c0078030b900340e8414040c061160798100207041616042d0f0700700d00c0c0300c2403442d01d40d50b0341544240c106541540c0001003c100c1111105501c3c0440384c4183c04041b010440232000031500401101d519 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 344771816 1250 344770566 344770579
    0x30b15150d021e0d020405040605192c16020d0f020307030c02040e010c0914040e1203040c05100906020c0609010c03181d10050d020922080a050903010b0604050f 71
    0x400090003d80f490510040220450f181c1c22114a5200a5405800b07101c0c012401c4c03410014031420003032280c513002d000c0314159200f01130400d201340030300310040005901a075445d5100d03030700705040001c401d90203041c420108441d40c005d820006840c15031100d940e40100150802d08200d215400b00981d41041e40c10726103103400728400c3c00050068030702c98007403012a500c3c2c201e44150f0303641c01c120302504030b6a442c541281e00d81580c10401048070042d1040c910309410a4506071000382c044002141c4c000d21440c0c0c0e885203641c0b40c01c049100520300c41c00c0318000c03a107030310b000b44003454042011480109040741d255180c0b503c0c14000a0002c516182c0050034400c05280325105041146104c03c003070220140400300d4812a0711410307804403400e403000030814020b12401300f100d041c623000503a06650060601d51b50303902c503400b21006400d4401210030407a101341c0600c50000300d0810040101d8011583d4290b00d903407040b000c143c00c449400c00000d101e20b10400c02080740c3d8490240c40d4103464400c8500d07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 344773066 1250 344771816 344771827
    0x15180f070f200a080307031a1f050702030a120804060510060e09040302100c090905101a03040f080d0e0609071a09060f0a020708160b0d0905010213030b15150d02 71
    0x40c00e03e054040e01e40180241004010811074980c103038069a04050001101d81d09094946c2c01e21001c401403141c2c3d5000703d08184c90801409000300001e05105101508444d070307103081074079500000401c824000000030404028441400031500402d80c00a81c0b0580100d44546800300180500c2503128146000702a0031000a0034540203003c54603959010381c030144822003246400501c405160301039489175514050100f5082c8840394a008191000e20071707044641d80b0401d420381045c0d00010001c8444284050b00007001031501c0000d4041135034080000f0554400c40c2d00981d09100006040d800c07180d00541c8100513180380c07000d84005565450f200301e56a02401000b20b5400c0c4a00420070b17141c6d610000d40340b6003503640000c01d1070480d02e081d030558034404a0700b010304508100c544281e80501a0030b12200e800400250f10030f541c0c3c248142c000500e4902c1003140c0301602c07002d41d1300035500e24000ca003c000314882c001e10051920a400c540207802d40042070a0300c24940507610f91500300c250701068 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 344774316 1250 344773066 344773127
    0x1e030307110609030a26030c040302010509151c0c0c020906011b0506010806041a0c040e0a230601080711190845061215180f070f 57
    0x21201101c2002c0e0995401035101d0414644001b154010b1005510800342240b074046c0042064030b000398244610b02d0304d424999001120250031041d640340c1d01c0a080c9144a030401e8404005100596030f901c40d0518800c1c11080c900d04446241c601c0f1000c3c082c84c10100d5005a441001c020340c410003d003420484081c920080001501000728000d0280c8910000440d05180001d6018400c0340300700a52170349110224640c440d01d92040d076207489600e2041c8070611110b0010b40e0a00d51090303070600e00081d0441e0326080131100601030018a100710071808140840707568022500c030360111b440d00b00010303410311080c0d40c141d40b90004cac042c903094000780343c42c0501042418401c89607210600e10701280910442042981d54400c0400011109402c3e00c00d102c0045410750861481c03004003d00c003a050240d250b180401c40900189210324942c1c40c040407640341d641c1c402c885001c1442042820341c10380b03008078016100201c0601644103000111110343c8609500140842e5601081c00044101c17080140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 344775566 1250 344774316 344774329
    0x60b09010206061e03120c010c0e060d0509011103010b090a050102060112020609061e0408010510030b0a0515040f090b0112020307170309100c02190e01060e01170f01051e03030711 79
    0xa007107070b0f40b5008210b40c07248500c01b00c0010304040002c1500810407018a0003081da0079806030200160868410311010b104203440e5846240d10449000c000b0509091540d802840d0358000d070002d050b003070404692101281004030000b4040e200a0004081e95410705007511681402400003e00c03448000404480c41e0700c1c2d030410346000b10b03000b0910304500540040684080e8009000e0800e40b9880c1000245200e8001010301d011650003400c1d800d256154130414a01810008126089a159061141039244c5580c41040ca504144100c00a41d255540c98185110700d410fa010842c500207115240780940d134080b49640c11150492040d00019007108c00c414214010803440950002c00a821090803c0c0c2200940814074800c841e488200440c202101d845000a40610f02034550000018000c041c00f4031a10b413072503107050501303510080d44202d5075400341c202241c508810701e50300c1004010b031303080c41c180300b1303102c0045002d0356141044901c2c0401e5503402180005008200b282640361003071b0f2540d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 344776816 1250 344775566 344775619
    0x101401050f060d0203070e03101406092a03090d090f06080601020703171306050304030c030e0f04090c050937060b120916080a0b041b120501060b0901020606 69
    0x1200290b460b1b1400c481c02410042c001c070380c003500038000c038000200e46510921402c001038503d201c94194540b5100305105e601c034030082407406403000c2c0d450324800351080700c1140ca0140418501d80da9903441d002010301c0c24021000307071000500c41c2081c03060000b66803480d0100c0503500c041c642605917680300d10040346800103e82c40904003580020750010701035100d4008098210000c480d4000c034554075a02196188411580900000d081025010010f4480c244c40040c08000402069888003c0e0340060103c03002001704450b0180d480c00c04002d941019000c083c0c3c0410f400c1e280980c2051181741204107900616400002070101c110030601401c0d20354001c00181c083c6924160300c4402c2d40d41c18010341201a10303208050b01ca0511900104640120f10409503003e00300507100410090340c542ca03610380080d004807425081d56004105100800d040e54009042d151402c5070b201c601030620b036003110b031250803007d03031303000200024982a6000241c40d030300088140c07400c1c9a601d5a0401c07004491444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 344778066 1250 344776816 344776837
    0xc0203030c07080f190e101704050f1023190c0315060305062805040f0912020d090807060e1e03011b030b0409050c191a040305101401050f06 62
    0xc42d039080c1707500100383c000400043d16111116405410810046041c2602d5503500020300031011014041d8100003a0703039002407241c0100c0341c258100b51142e0342802d002031a035005455450120650050010300741c0160360058400c60380460a00018003082c00c0c006d42002d85445464003505421a8407030b13030200d000308410a0000815685802c402070280209030707241841031031400c240c203150012054503802112030341680803000624010602c400f50240320303012302c10300d503450003074a000c10f43d460b25264405010380d0262424101501000c2d0500d0a550401c0f461355100030001d01105420260086000c01c045400310746840d8005d203440049940b0901943d059402e00e144000d40c202c072201114a0504251001c0c03203188040300c144400c5584800005d09154410300c50058141480651003a004035a80c040001c0c2e180c07207541c800c13511301210403610b9079072000080802c00d1180074024800e14240a86007401b440c80d4031812a01d107180d06004962081240300f403100e04982d9038000304d8054090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 344779316 1250 344778066 344778097
    0x4120c0803010b0a02010c020d050904090519050303060306070206090c0108090c0a0b3c070c081903030506040b010c240e0a020312071502031e09011e0c0203030c0708 73
    0xc49515a050640042c21344c1005503081c45026140c060000c03824500e40c411903a0307000d050014150030040900f860750010f032868000d90030030003101c122121141315180e00841c02107640f400c0500c2411b00c3d002e001018002150003450500c99a14800b007124a4441001d1078500d05545034000e68a090020300b1288603400000baa10010700700700a44040e00000d4040008905403100300b5403402080350365112404408100b40084c1800c0c240b564019241c02d42c002c503010881c480c1c1302c91205140030480000d40743c002400c019040c0c01c15070b060140682c01801610144207843c40500064214511341000400910302c401c0c40340d500c2c00e40070110101c241c00c03030340d014000c612010f132a16440350000340301640603010b140580020100726104a50b070705030344005010008012045054000c1d00058502413842508980300080850560003a60098100e9400040c901503c038001b1900451040d0151960a04203801889420780100640394442c04211001e41e8034010740c54440241d120b21003081812a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 344780566 1250 344779316 344779319
    0x405040303050109231f1703090a0b04030210080612031215010305010f061404050603040501290d1514010b1b070b090112090605130512070b04120c080301 68
    0x1541a00b20504880304072404002c0c0da0440342d1340000252071401c2141900310300c44049100d5190030f403402c810300200442c15100c400d44408403d46c212020f0400c0c01080d5101281d9005140750160200c40100301200b0042e103401d145502003010301002d4840d01084c00801000182c0719261885020390b01c21000d42038964039030f09042c0300c0c214100705075243c9142820311002994554082d21441e8182d4080221401c05580f030210105c9038290549007089410000740310028440c0c58101c05540924072800010681a40002907000480c410030407090a038084902803944c0c1303481300050144400d8000e041d8070b0201c04e0707504c905805440903655107500c840b03100c0b00001d099002440582598200c00707088921030510300403515603e10040c00780302e18005041084507041d40c0569000d5010b401841804180d186490f15410221481150850062240c036040340b020464144400301116889a002c6414400b180d10360700d200407801080140100c00400c9007000e414000c2c8178191041d80d00c118440d40d2503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 344781816 1250 344780566 344780573
    0x210307050714030309131e0e0a1104020f04150c0b071706010e010914060408061806090d1e110d0915090806070c080f0301090b0108220b0a02040801060f030308070212090409020609040504 82
    0x1e600d1103404ac1d13084040b0030550800c070321b400e008417181000109240e1381000c3c1400c039107020034a0403542d40e4040c0400001d003100000c4c60300400c13034410112916a04940603c1600108180c00028030b01410080f2440301d03490310760780000c100d0702510094510f00031002141004544070340710302d4203c91190f103c3c000400c05032030040700c015040c1d8140d210a6a01c65241c590540f030f510920241e0350320105604a640c03028418560907100c28204a0f0301d0140404041144414108401c4d500c040000a0410f44140503132140c07441c8542c3e012102d0f241c072041c420b1a2140094450401a00b08010400c0c4078240300b00b88a28038054403ca88120300c0c030545d580d41d40300c0000d40104821014603020420341c0001072002c082040e6020030901070581460204900390b61210702c0600c00500c0115881d90070300c404203003180f09105d0341000c1c001c14004081c03807a0a40c02c0141150000a181c03000319804404018009035003841610015681034a001c520b00905100051080c0910110141c005140000b00b01c01d2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 344783066 1250 344781816 344781823
    0x3020d06050a062108030703020f03070c0201091505030a090c0e090c0103060504020304080307030c0504170601032109031520031014010509210307050714030309131e0e 74
    0x291950b06010810255180e4080b031103000711103c003c0d500d1121039008008500003c00455012255103001032404071081849901500143d8030f0790005004100e5a030115600308030442c0141c81d0484440541c00c900704001002d911000340700e259115103d07c140c6c1c0c20803030302040c00c070041c060348071141c0341a242980007150380f03a0f03000c0c00b890300081c10224002110308140c0b080780c0c001c9801141c880e18546e0743d40320980142a40300d0002c82000342c100301c00561010b4603813000c4809100a4007174542d03035141d400c00d565241c01400e040c00007140f8001c0c9529200b0740004103007040340d070b100100d03a4000010749001c4000b09001d45e03036003410303040b03a00d50820500039403c01140300d10301c404464102c40f5242d600401200304443d4105000c00c008002c1e40344185403605520745201c0b5900001c04503090b03e146014110303040b1500403103007584544424041c0d8151a500c3c00d17a607100070303070085040a58200c00140b07030f0700850344180d414941c0c032940756006a10f90765001c011810385410a0000c00207a1b42c1c559503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 344784172 1106 344783066 344783071
    0x20901090305070f090f0b0315310323030718090212090d0f0207090e1009030905040f060e0f1009050c0a0801120302071403010603020d0605 62
    0x30b6420001507014001800d9200401458200150140c440d0021251403103800e04200c2e0250b5140080c4400584d1103003690700d041602c03a20100c80010100005420401c1d801c110b0a82c84009680700b5003103546c3c4266240189038450842c0c909403201c4c168418060103a080001c2514544151850281d01040781c042c002d40a540d50403820413688040c0c1c800c4001103400040101c940d0080c03214030703049405070400c5204507100381300c000d407108980e0049101d019500c1441c0f581101080000319002d040ca9442080030280908014202055521802e071140d42880f29400691a0b540a80b00440e0481e03410140b41d52180314030202c103020000d21004501d07a00c10400989501c0034004c0c1d60081001c41c6401365074401035800200040c1c0160002d008503044100704c100081d0f80012460116000c400b00b92224000c8040040e02402490340060751045800fa240c1d002d1041541c080c90 = true := by decide +kernel

theorem cover : BRFrame.Cov 344604316 344784172 := by
  have h0 := BRFrame.cov_init 344604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 344604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 344604316 ≤ n) (h2 : n < 344784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
