-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:15:42.313945+00:00
-- url     : https://prove2.me/submissions/4a60a38c-1b83-4b89-8ac7-4dfe97d203ac

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198561151 ≤ n < 198741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198562401 1250 198561151 198561179
    0xa0804020118090e251202040908040503010f0903020f0f0a14150702070501080c09062d0c0708010b0105040e1602010908071128060305040807020a0312080a090314090307 75
    0x4000545e101117412406100501104c1140421808070b14103250301e000c0c00095440e034400da00030700c15559218284108281141a18050840039000300072000c0000310300070007050b140310142c0151244050000202d200010300840590103038028051442d8240c4d6807240c000640b4101280b036000304401a282c40c000503140d5807080342251b005003000c034580b0300054160840601400d5400304200040c01c00c07904c41c2070880d49104041d00b1740d50942c0510482141032070708904403106044a0000c0c90780e00a500c0060140143c07110786e40200b141c41c3c1510019100d0b0f20803031050004c4003203030a0015030007501c4070a200e018640705000120f007044240d42d17000055485454100e45586040100c810325043c0303540002d00709201c5410166030a52841e006c18104107191190508040d100e00021301000941c401380c9150f140e0103055443d60030b840f4504400390105220010000441400c005418440d03980500d402c0d0b00c1d016110206070203949103c404078ee501800079030b030b014481d010002500300803100003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198563651 1250 198562401 198562421
    0x318050a030507031205071b03090b03010f140d050607050d0b06030a02030f090c011b0f0804080102120f07050412023f1209012307050607030e030a080402011809 71
    0x42e0695503c058074025000503030410045900c0c0745440108001e10780c00140c084030500c00c200d0366040c1c13030071030340307401c842c5030105400c03034442d880011000090481d1b000102c002135401c43e442241d00c42580000344411403145840152040e032200f0b010591941c016802490115054800454001712200201e2102d03401540d1a121b401e50010800c00e0307000f20000c3c06508220310300047c4c248010824002400d09981c0c0905c9130303413841c108900d0710410121300c0300421815486a00c880d20380340d65907a841e000350000310182c48000030001c001010034000c00301440c40340d0a2900c030740b0308060600b8884958001041d000302e0f0042100d02003142d4990300c0c00400c07124109003102c8007104800a0030390250031061654500d01a80c00586a007101650385400d54203000000c0c600111200c00b01002e03002415801c40d42821141c0c0c0009111043c0900800e0a40c03042e841074030309100050070300c01c2d8540e50b0300c40c0507014000600190049401503204540c0c0c00c081442c0701301440340e001d8030303400c002c0d0440301034a034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198564901 1250 198563651 198563657
    0x70e0a09050c03100501110703030f050c07030c08010c0203040e040605040311060a0914030901050d051f0b0a020d0c1a090c030d0305040506060102010203220203070902030c070b01080313060318050a03 88
    0x8000b42c03104c02003031540103080c0c00e20300500d000014100c455a644e00c40d00008050003144090003600605c01c0c0250340440b0204003c03030b2034941d6282007541620000303000f141015401e1410210103180000116800c03200491034007600c59880b80c0701c040080401400403404c001c104c03090220540000c1050b10701404850800003002d481628088510341028900d6029a400a11004c0300581c0c201098410314111944081003a59600120a02d0844001c0396007840400290300820018442000350508031082e800f200d00001d0604000d0b1510030305890014503280340c00307280ca41824103062032260011000c404444180c01090000382c11710700070b20304400009a60b4001c02007440800c010b200e410903400c1c0021850750400584601c4000440f2a484103003401840c442c0003191020000c7c18010310004030119128100384640d04010381c81003000381d404203078460010030746000c00300845a94045c0d49210381007071480c0080c02e030081c03c2000c1d101507041004405a00104a050011070b4805110395 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198566151 1250 198564901 198564907
    0x2030f040b0c03360a0b0f161a011805010308040b0d0906021902060105060702030601150203040b0a0f020c0315070e0a1206020a020d0905010206010605072102010606110c09070e0a09050c 82
    0x10002c00381048821000d034031070812a401001445006d80448414620f140c0c09160f8070784240a451072812120b89001300314081c17010501200c1c0c030b600300300f0a068900042d40c4402c101d00d2040c008003a55404e010251480e0010001000004150001001444940341c80401c503901903490300801ca0708000611012600e55100c4c5096669060004601400c0104d032140d041041c41d0300420f41d212014001c81760190306030740840529074020001d5600a11103138011955461505038001c0c00511070396051005441401041405480c0c04146000c2d2080804041821a07031101c0007110305e03e05802c5c1a0b60492000c000c007003001c4280071100902d9034010b560141c0e0340e14020300d0003850540441000d10420000100920041c1e0780032400c02e04550032454600d46405060800320695810240302d608116080b50001c4030491b01900000215103441d1240c1e191400c88128454031005544029544541c40000050240340282c16401c2c002c01c000d014189019100e80051040707070307415900c60000b44404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198567401 1250 198566151 198566227
    0x5040e0a200903010c0c1109280614120a060b040f090501230f040201081e250903051507090e010914060604080604020409021216080d02030f040b0c03 66
    0x9010722180305c2190b1070a00080740e150f0310f0380310070988000da8041c07082c80d1050201304015085800000003000040c040c5002c1021500790350001c0105115401e14170350f101d410110303541740880f80309003040c0d0018090b005110b01955008001c282010171182d0007072340c40c4140c500d5040c0600c00c0508a6100e8000018038601000551120003101040490003c0c0504100041141e180b0130713041e000390b4203092000b01500c2c0d1500e030b015080d1a111a030b80604440504014030440309400c0078160b81c480d01d0810790100600d0104542604550101404542c4003515010a910302c2c5c8803038540c00074191800c2c1c01c00315240c82c5260780c5100284c2c030030400280c882e40001090740d10b00f008560040301c01c4801c2d0b1f20f000d10304030030180c0340c10004002a01c03e036600e072444015034848504c801400c0d24080c094592500c049011081c806101d802451715901ca401d0340341d0120b40c00041100e00000d070807840d40e030829180403d84081341e40043c98026943c0001d02203015200841d03000405046440300080182c540c40d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198568651 1250 198567401 198567403
    0x20f01060909030f0c0528030e01030c171008060408030709050d030903080a11060c180306041113110f0d0e07060813050307120206060909060705040e0a200903 70
    0x96000301d5549482c2a1654000a4000d42c841900000ea4184000d0510190400b181412503900100803040306141131020491001e0900b64012032080d11200207580784080114222078a102500001c1030410107038030f005d01c440a88481d882801c803000000b502d0303100e40c401410070905907000c407652580030043c01455900100c1c440060b0005540d1540c0d81085074800030a12452480301400001c80000d102011910494003400260406422a42e080c144130b182618181d005000e5415640d801143c000d8161402007082401560401d2071000d41e103038190100f05050501c4441040c0c220360700d036414207005104501404e800d0f400041480d844002c04203d5905883d01104004580c2d0000001400030b030f50054040d43d00185600e00031280c41001d89041c600c0c2d4400d548016003101014004002401e0f07000881e180f16620981d21080f89498800b5030940e545e40c1a00c1086c00310f01d0a0100b40400c0c0310a0324190b0b0b0105884801180501c4901c000601100c80415400000b502c0010303241c042c2d0070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198569901 1250 198568651 198568661
    0x6090d1401090314030c0a03020a02102f0306060f030603030d060311010e090702060a23010b03010314030a021015051c05010617060105061803030a120b06030f070c0c08030703020f01 80
    0xc0007070a80d80c590321b8285030700c10f00c520440c11840c050507804690960014420800820240020202040a032200c2880483c40000711f038000d4041c4c882c604000c0c4202d8501d0002d9900400c4064201802d160040d0095102504014201c5030941302c14800c000105496003e031400035809036100c0e81c601c80e00c3d080014400d43d00151428000c2028105000c07046030700043d0340d68003024081c0001034102d2110800c442c1d211080141e100c2c032540c20000441c0c901c9c00c01d00214100c1c0d02c1035407421250781c00c040c4100e40300d0048881010143e041115120b80c0d440c00c5800500c0c01c1c41548100755200740d00e9100041907003640c408242180070383c042031902045000d00c24040500130206850540510b1100c1c140e6071100305028440c003604012801d940700c00c60003010381180c1c010003800c1d252a403940c060300504418032210710180345c1d4105501d0003498200901102d0041c0d0008019200a648102c01907880b0340011804480781800301000140032081440a071070316610035405840d0081c28540041e095030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198571151 1250 198569901 198569927
    0x150b01031803020303040f020f0d03050408210301031506090504030302071a090a113001200403030305130204020307021e24040c051e01020f070608010506090d14010903 74
    0x45402141e000110740c0000540b603000d680900c000700c814200b0700c08a80005d1584031190341061828283d0720800d038011001d0405c0d16024021600d400d224031041d114a9844610785c0000300c18100300500c0451245031420040d030090700c07008520780f9030b01c042a00c102c0d1022541580000d43c0840c010081180200e00415004034040e982001400c0c04407078162110381810700100300d5400c0241c0031029817a19000c2c0e9214502c0b10108c1240c02210000d112030100007141074174003035460884e0404122400840035050040c1e00645c03142030605640d010343c0100740150500030500408940ea200590301ca000070352080041d98090641d2050254140b030100840c0e4600c1c0845400441110403022406810000009040d80700414113440d46e007851510707010180c100d82d0700260b0141960180c1c01d20b50b00d42850031a02a0708690344d4120100c403d0b42c80b03082900603078000039000d1004000f10319040f400780c0074464005000b40b00c2d50b0346654440c05001c0411124500607511503880b1414160010b000802c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198572401 1250 198571151 198571181
    0x1110f04060f110709091103070311030d05071101050309030909010303030b0a0509090a03030902130507020a0309141e1c0b01050f030318090a0b03030703120c02030705100b030a150b0103 82
    0x180704082c0050b6143d0f200c600505e01096a5411003009000010464050007903018003610015a10390905032200207001c3c2c1641c2c02480303400c0061203084c1c843c90480d101541c0204117641d40030301c11401101c1c030b42d0000e050b00e500e5210503c00d0b14075a5039401001c0b80203621903200061103c0704002030004001250380303d076100c1c0d021802000500b100c0480d1544240340c1c149070008003108140f00264006c4460000c44c602d00b4641010000176580020fa0781c641d040c065120660300640d520703254422004003107c260b030000f03012404410403c09005030788401c81001880303000070b001040d03900e010400c4d0240341031318000c400b24010441e60409811030041c058055028514100d807503002c02d400383e40406a110300401505000845101003a2b0086043e2440201030f030341e03144c84606004105c252103d07280358600d031410350a6803e4a00020494803100d0744480a040c108400d003c1c003000411407580d0351501401001004400501d440ca83d40d881d80c1c0090034006180003c00c0001422651000c0702e207048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198573651 1250 198572401 198572417
    0x16020c0a0306051803040e0601022b0f230702040e01020702091b041d04020103141501030e0106080d0f020607020c06090405060d02060c0106051810150201110f04060f 73
    0x480d485545200d001c0e6074200b240402d66456040c01540381903039a0344800c1ca41d002c00704003c503c1804000a00707004680076070031074403080d410320340c1030080c5054600a902015811100c1100e00e0303004040d0900c1103181c9003010314050b1000303403140b2500e80c41206030301c441d04bc00040900031450300b03110744c1b00c1d42e0021703c000310b00340b6401d40d0200740400e901501000404114440d0100c98403580c8086501a14030a0f12019503500001c1e4145807100054a0403030100e4100783d058103003050550b5501d4031621940c0c1d400c0c0c0100c0d000c0c50042d00240807005503486507540f02c640124000004101c1c210241e640c40c0e4607000c400e114000000e05001d0081c00120440d0800c40b0405001da9500003900c4944008450004980c0c982c100040e0a00c1c81980c0025001080840c04801d91001940600d00305c40c016078280c400d98210f400b0802c0d16600c22640c440e020031611000b4829040c601c0883c0c01405518000020100c2541d0100c00c0c5c030f500040d500d030500380d100090a02c15160311600d041e010203014101820 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198574901 1250 198573651 198573673
    0x3090203060f0c090105070804080a151407020c060c010605120a0201080a0b060a0302161505010f050307180518030d0207110402030610081b07081201061107140a17061602 75
    0xf4152040b401d0705810444045559420307c9642021500105003240031610401c2c1d05151a60410401196400100d8903150543d4002d00141409034407404060b07018104c46d880d800100031283d00400880c0181d90b40c0d6081c0814141c4521000400c5900094010800b90000d031000400c40341004007020151030401e01201607030f8541c002030301c01e10011350074056100c0800408041c1c8031680107202800c1044021045aa8154150f2085042e81c09800918110984a90070b0581d240358601ca05241180d04915410044030180c5c02036411481c10405145401c07041c50b1301c2440c40c2c115542d0406001c0e8000b83c02c80800c0f41506810301100e02c140d41c00d60440c905580000c21000000e6840000d0100c1c0f500010625045103168411043c0c0303600000703481d00b06a0070710001c41c0d000700613032400080f0900c002180181c0203040070000d524104004103040c1d400d003841d0000c03a0342e245103190780210813100045442094117941e0710080440b00000c1c5480d107012445044080b0030043c0007020354000400c00c003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198576151 1250 198574901 198574921
    0xb06040f0b03040f060203180c03010b030303010e040215030a0c08070c02060901080a0b06041d0106020a080d0c0224100605040f03061d01021b0c180703050402040b06040603090203060f 81
    0x1228002441c040d200d0ba00c3e0300346007035404c0c030840c00141030502c000704206c40503040c91701a40003282d9040440c0c51003013040341403500301c41141140c2641548144010081508200042c5a000d031000c0d0812107000084603203140c0c10380054407020045620f49640c8080194051040c6a0040031840c01c102e00156940105155209842c4034504005091001428040c407a0b040018220340c0548034542e643d1761030504c203403403d0702c0c210415148001d0301c00000f1810b100007506403600d50890740b11460120f1350140f80c40103001341c1c8440d8007580a9150340c00355004080074200c6284115010000306480e14900815280b126500441f05000041c8003d010301c00074081000f003a0796009070001032209070405500c103500c08880b59101c1540c00005d4001141031459118010b4a44135000c450070a5200802c0183d0700c6040000c0c0c1502111358030000c1c04091013500034039049030001c2d1001500d05120404200c40c0e5109800c00700100c0c1d260f442d40700840c2410400290302060511b0144048d0500303104030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198577401 1250 198576151 198576179
    0x6071701060804110a0e01060c0c080309090115170705031801060305100c140a050a02061b070303020a2303100603110417030d021909120201080a0c110a080705010b0604 74
    0x5004410f002603003401c2601d0b111400c3e806031010381c820f84061f44c3d40c0e8800400d03000d6019811113511074400c6000030301460000585040c040c005051841c183e080c0000001034090024980041007212504034903581c166600d918001d004079903030340d590b03803409041003030b00600c203041602d032540c2c50202c040001c13800c0400d039074004244a11001c1213407009008116075000d040c0c100350a0f01d940c0018503e14450b0060b00400b101c1005400743c1e81030390745001d1890000c2407402c00018131076004211850001e8425030082041c6001d40c20110044502201c46c507807243d0243c0d42d034070101c0300f00000b80120b02064003080c800a000d10b240034005c82c0d1340b01114000c240104e1256074605101c001c01645001024429030341400c80340c0d107007152544a10400b62400402e00304203140452142480442c40c1c01151071144841c94040c0c4070071130340d51510813402000345450301c051420000f40c2c4a98000100050103504d9140f40515505500c501040c01d0403400c403202d01842c41d10952042004120303400d40303400e0b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198578651 1250 198577401 198577403
    0x9181302011407021f08070f020705060f1b01060e13020a1707030b070201050403090b04152a030201060e0105190b07020102030d23060108090c060c0703060e06071701060804 76
    0x80041e2611403450702c440e00e4055218001e5129900d07007060101014030903104840c0c000c2c150340302142501c40200c10745d60b0f40341094251340142c0140c4818003240c10007d00030f003449004009814581074000541d18959803115484c0b50099440b00000c000242608100b540c01144180d41d03130b80a40465070014a0010035449007041c02501300c02180d1701514140500f6000b960041800700e8180780c801d10080c020001110b00310701107440c1440119600b88101d041e102520402c004084554004103c1a903c03455400c0101d4400c140b05031401e490500b6070030005038454480e80003c50018101002010300a0303058100380d00440300c0750b00c40c04104403040c2c07001044480c0500540d03502c07221400100d055201c0d200c0808201414001c408072000c4034000d2a07041086289124800c9480d5480110f402120a81d00b45066902416019a50b0301d001c84c010300468941c1000c448030b10fa03aa580d440709030f80040d089403000380c00000401c0a82c40d0454540440c40b480302440d80503c0d81480c601520842c0f0240c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198579901 1250 198578651 198578657
    0x509010e030a02030307140f010203010b07140f1903030f0506010c1403041d01030212010b030709110d060605040512010e0307150b09040501050a0e03040e01030807051005010b0918130201 82
    0x8210840c0d41c405008141c0c1c400d80181c15241e80c1d00b83c40c2880f4000031481d01d141c2415210756190300d40002c07010310130340f03041c0d032034108406140c2138554849000d404501c154031503540c01600f1980c3e0074184200540e0f240706402410006810f0140c0c18064100c580a94030322030304a003054100540360380d001c55070344141a444940f00d41014807a2890f24514042d42d048000501444800c1c4144014100c4429040780c1c402c0358540141c042110340d140c266000403801d1f80d019844000c0c240b0008049400486401d0b5a0740f100d1401d140070040440d05039549a449040405c0001a0a000a0418014202001d5a40d000078000c00c1840000306543e03210f01ca030054140342c01001d8031041d1560a8200550445c2d00070442e4480341460f0422900805041d2444c2d441b2a14010200050400100a88084075071400b80c00c05a03030303e55100c44009910402c1d007150305e4080c03c030102da40d4066a2241c00d01038100e2604864171000c00d0020b05c403440e91140a8800014801e80804c107004900030000d00302598286 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198581151 1250 198579901 198579917
    0x9010c231308010504080904060909030c12030f0513020a151403060604081b031905034003030212040b0d0e0304051c0c1202010c030c0206090913050f030406050901 72
    0x7000740c07510100180c0040388154200001d01c01881030721005450000801c030307001c001495039515450110303180d82c0001000f282551071184041100c1c00080c0a0039a150b060100f240d54840e01d03034a088038411115a07040008845080301942004010301d002782003044401c00c1699924840a401c0d60038044d180010800004002201601c4078419140204681c0040b11031801c90108c03500e0003840c06210030b500070f114010480020003a202e4440c18000d80040142d842c3c582c0f6107002004843c0d1040130012030052145c20380001c4850506192004044c1004940b03100d402c42ca030090401000900c0c00310f002c0028401400010000400c84d05040301c88800003403003000c3d131100c1605500480e400a41d12040f030101d110a45000c404000081c184910b491024003510b85001800c4c9030440f01c00640040e4100400f42d000034080c2d8500b5400c00d000400603814820b00e480000d400b904200c64000d089148480c92600b0000300f0803502c081d00401c10042d60415082c158024800d01503484002e0402500d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198582401 1250 198581151 198581167
    0x512040e0c0c160605030f060a1a07020d08070506150102150a1d1e060a0e0a150212010b0405090a06080c1504030c150f0c020a030b06040f0504030809010c23 69
    0x40291041208440f040c8001070740d0b4800c4044c02d01d0300121507580c64800703483c0015041d894180040d2098492540f402503003401251007050440d000500f0803a0000c520986440105590384044c3c04024400d00c003c1c0540e240a40d401011510002805415507000d0f06565200640380880e059000c40311000011b004d5460b44056198000740c54100c10040c003d450074851030b411880542100d120b049000c5448170344407408003c0840304e20030302807091600180c4000c0001080c8100c40c43d10131101400241c2004180d00049400310820380c031504031040005420080350901c8640181c1c030030908902088003905d003681c11a26000d150384041d104131819088252450b0001c400c0d5809103811080312803505465501180070745001c4103400340401c0030741a540c031100c0c1c45404100d0f441c5a001e06800c1c03041d0301d181d4072a00030100c09000c20b179005071610400d11b06401c880c820513102d2402039a9401107801c05a0703115003103074180b40c3c0311420080403001407003401484010759502001d803114541c0c0c0e21650 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198583651 1250 198582401 198582403
    0x31101030b04110307030b09040203070905091c0305060103051302090c0319061e080609030f0f04050904030807090506180f0105090306040f020a0906060c02010e04020c190512040e0c0c 81
    0x4081c04141c0c1c820b24194a00701c80d0101c00b00a10701c1403074070b40c404100e41300ea03400401c05e2607402201e00079450780c00701e201802410300c0c6402245c1c103d511402112218030158100c040303480c0402029500003a9100e0401408d5a40f41c01100e0304a10070076088100102d4a8000c1150300e1002881001c11440010108a058040c0b0741072130703d01814903e00300005511040075510340350540c54014280c0300c030054041282c4102080c001e010300d2091008526200c4015000451500076a1101c0b800c01400d100c001195141c0c400303114400e6210f951105520310b00228094540c44540e0403641c040c134020304c94006401c0001e0009c088030001141d6001762600302000403605407040d1080d041c2c060044130f083c402000010b10700040e480344200c3e8800481c80d03d401d2404c04582d542d10482001030008a0b21001550050106181c0302101074409850842600d0a03d80342c1084940d601301d08081c0180c640d8244003040c045003c0804400d06624a064542058524111070107005a8204000081c5400f40034070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198584901 1250 198583651 198583661
    0xd0c021c0c020d0c1a07120f020703060b0a090e030307020d09080c01051e1b10151511010615030b0603010308030f130c060806030609010903050d0e0304050409051609050c0403110103 80
    0x4040c02e4540039003104017055000c96004084112145160b50a02c800d905008517000030a07c60301c0e40c003e000c05451a200c0c1c0c0007400c58410340c10340200130064040b9150156005030400c103011140115034038102004000e181c000c800c410041004a184010300070700740c002c146100f0703031102440c05513103c854411403440c002c00d0020402088240004114a580309902a614448800c00c07054402946068040c03901391081c100c00500e401029000600c4121065400954408800e19190501d551980c14041c21031700d41360021901058140da41034246545801050304540041d92001c2c00c0d9491a039511142d400003504d0388400000040004036603581c128408031b4181c1e00b1001e500c4c036450796103a0240c407000c0240c4606020323004007000208421414001c100d40740d58940d03259072600500c1040800280070302007035909940810040000c00d5650790040740341d5030380108068098126813505003000380505900c403074481c5082c1010044c460200000b66022280c1003600c4103c880342040040340140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198586151 1250 198584901 198584909
    0x100b01140c060717091504030c0b101e15050304080c070e0f0c0a09090e0c03120406030c080108060402040f02070213051009020c2805030d0c021c0c020d0c 68
    0xa01203503500369424009800b43c0100880d03200c0c5440d01c08507001e0600d188074120b4050080780c3c0089124224010700400151f4014000c0c500300410f866640e840c00c10080040d01d4904901003403000500010226641c0e040c0080f03650a00807144528000325400d040e1b40c030600c1c04051040210005040c000d400301140e0400c2414825182a40e0300d85200c203041840989000092000900c0068183d02c080d4003198524030040d1030396940b04e40342900110113000300c000714500c00e015540745205942c0341000041c5296212484003078480381000c10090032215494105002c108200004101315a004100319801c250181c4020070b201c5504d60b4800003901c02ca400094212400c020801e42c0c0750130aa020b10b01030441da403c041d2241c0d680b42e4070501070340180315159150780c100c80b062140b088080028a07540210700070b00014241d1503602c425045421400075034581603214240104125410300081200b200d403440185002c3c0c088079001400c90f0340f0b868001307006108a01d000e00c00c0c040b10300c401a00030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198587401 1250 198586151 198586187
    0xf0807050303040605010905010b0403020913141002030103061413030f0302040e0f060f041a0904020a03050307080c010c032309120310031103010c140d0204122a030203100b01 77
    0x290503c3e14107440113042c244901280701d4502800860b2181000c404c031022213800504524a58580c070000b0000724550f142c007180e290324203000d100103030f4005101240b603c9403280d800584070741c91810040d0661708000b6000007041030040401c0340340842402c59150464041c5401480c480800340203800911864001c00c50f02542c000800212403241040d807845014103031004450000c200e024401a1000390f6640c1141400c40500b4031003504100d16581d6105000800000d0b81a03500e46445007181d00103a000d5488040c0024050f40c4010b003401201c030b0444046c0760801c60180c0144c1020700302c103000c0f00701c0d01c0105400f1012800d10350082013074402c003a8a0004440c0d403810010700c004c5801c0c685120845041da0700703c0b5100700514040c800d0b0600c04540781c0740d0248801c00603000324159071200a0780d448050713081c4070100d0000c40340700b0040d61852188054035203120001d1070041c0510b4041c01c40d110300b41209041031005880200e804010108484000320301c03031001d1341c0107880c4a4240c0d900c4540c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198588651 1250 198587401 198587407
    0xc121b01180210030e1e07030812011e0e0c0702030f1510080102190c05070308040909171611040605031204060908062206090813060f0203160f08070503 67
    0x5804101079034480580c0c4200c400c00c0d00241440000c0c2c0554044903119600f80e0802c1c80d041d0184241012081c403070b03030210015030b00b00e15140c0d620404903410110010351040451001440320300148815554480310810180c0521407034048901d80400004000c0a080303030002c500c44046460400262000180c024180c542c2c03c44072444200050341e04444414942003504000100d59606208030b40c240302ca4508400b12150300e45a003520325281000d0110b440c0e104000300000800e10013000360020708021030010900031000d00741402c0c5610f5603032154224140c1040b0000000902a40e0f2521995110540b08000d0041d100010300520041d481642c06018520301d14969180040c010f2081c0c0e01d1684890740041c0c0c84180e44d942c1d8a0341120000c0102c0924001080d040b1803056075051828400c01d00854040719a542d0041150030444410f002032140041c10300201c1e801c4400c02c243d00c0a688000c504001380724040a0260440d00303170140900d2034850701c0206020004c030840c2c5020350000b0071255 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198589901 1250 198588651 198588671
    0x40609050a0b010f0903020f060a110d0c0501060501080f0a0b190305010e010f06030f03140d06030303020c070902130909051005040311060c040b030c0c0106050a1706010b0c121b01 79
    0xd05000b10300703640003a80c010001008a8090b58241080d250050030702d920500e25007060114982c45007003058103214001c2e051b0050b80208001120005010f81d6481500c014580b404501352000c03900f04905100080d81001020106a051964480c05068010640e041d4800c04034a02d514515007144680042003404000d00c0015080018100309400007044100004800d52040359414000100044090680d100c0400d01c2000d1b0b203610340800b00e81d44d03840c00c6000d02c4640104d07401c2d40e0045010a030080f41d94045982e06101c008010a1003400540c60030b8201a0300300c28240c80390296204507955481640144442040510b03040c41041500308030b54182400c02a140c0c603072120300031340503200340d60009403186c0e450400c1d81c0c11190f010816078150748509214050382d401045131507001c1e643c0c9800011b09030759400e400c40001d0100b605040c076202d070450500b41c10200160400d12003e2400c00840041940001d002c2d43d58612407003406459a0090b030254050381c40c07000000c07003590b01703200e1804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198591151 1250 198589901 198589921
    0x91a04060b0418020a08060601170406060906241403071209080301091508030405030a1e30020a150209061b030d0e0607121503050f0c040605120304060e04060905 71
    0x2041600807980d82403106d0362011744542c2d608084403014001902d110030041c2441e0100c1e845038200c1e1041c000072a000d9204e41c0c001e8210392881d440408e11022828840c04038503050840003002015500c2d100e41110b1809030f55150f5407001821100c00c21003950400d80c600c1c0080c0d8840000981d10201180d60785d40d40303012810146c008c00200d201d40e0300c0020400940804004121000c0311000340180007150115200d85114402d001480c00440040c40000744c00641c48864130708100c0390040003140500756488500b441562003280801c1954070030251840401d800d51540e03182030084100c003503a612144008a10a0f008003103103180c015404006c800f45111022000d0102410003031010009600c03100415a514003058803e000030402210080300c911506400c4849a0700413031a84803151940da5403a40e01c0d100c01ca81d44420160001071102c6074034900b50280e480240403c035600c0b40c1114850340a039071284114440e4406026465418501a0320f903608071400800c0801c1042005103040d0030b481c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198592401 1250 198591151 198591191
    0xe21040f1202041b14090a0305101b020a0218150306040602120c0403110904081b010b0301051003081803120403200a0807120602090a08070612091a04060b04 69
    0x201e100c0c504210040d006074941054070961004c140e907511081240030700039640e86a011000c0305411145500001c000b02e01c0400805c6440c000c40c1d60000f89081100210401c42e0307a20444581c11034006480032005a6941040101c60000c0c602c0241c100c4e80350703140c034600c1b403170f10400e01550540549810002400303507940c042d05501c104640072940603aa407281040c1c2900c550b00000f0030000d02001070f45203030704001c00507541c818840c0701211303d0702c01004880340c0080302000d443c04940c1e45590790712207a410300380030316034100c41020103442c0307043d04607030740c40791140155400324090503801c80301162580c0d000c100c914558000c1603440399485d916401d00300d0800107a000c0d1a210b109501c4828442c0c0d080040843c0c040710300c004c020700034041c200074204ca41042802d80668900da020301c60f01160ba550030b40510010143c400041207160300e40080038005401d00c01c1e690440916020003440802d0200701c5041815040203c0140680c0e0389140c410001c040d40c04045d6007041c42c080300d4071504003102c1d4003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198593651 1250 198592401 198592403
    0x1501031403030615160204020414120d020d080703110a03020d0c022109010212030a0b0a0909020d0201030e031908010501121a09101a070303050702010e21040f12 71
    0x403040360300440519981ca10040d14200d4202c40c3c40c0c5169203800e401000504140390085094084c0703910305400280c1a0b80054001c0c130302840b200810100f051400c110322188031720001018058000c2e80d1600691103115113001d02d01449000d07000203001901c2944050300b440340350303107903d030f00c0d034034124001402900f12420b0540036030300d804800d941550002600341240c0d40030407084c080c0e18a980701704820b241c124504560640c070445038009500000c0f1006140300d50a0160005500e10704c400c10851008041e9001540310751601c0c00c0140035803203140c6200038141d02802c01003012142004010702c2e42c810410604035069861184040040e4407503040360489809030790303801010450f01992404c0315241120200101c0f0b0258440c40e5604280ba03071a80d11048104410040c3b03544c54244040a10b0040c402007103403140011210201030b01403040c66003180c0c15200130040408440f21035a51064030641c0d000e901c8104400202c3c0c000d1303103502110040c158560690b003609980342c4a001562510141c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198594901 1250 198593651 198593663
    0x603150b0a0e0c09012607050d0609020301030807060b09011d100803070c06140c07140a030c09020304330506040f0903020f0c040509030d050604090f03020c01120e070308030a0e150103 81
    0x500001c0f0100e4185046c5004841000d2082140c440ca40b040e140342d40183c07140e62003e6102c150000d90181c00d44051402140030b80249651014645412012212501c80c540e201c2c509020040c481d40c442a0000040a404903124200d076407164045d01150603955442080a03210008108003044064140d82d030445010303803280d0f410307180b5040300c0904500030341442464640c003442c1c00300030003204803a0b252110358000e00882149500d039113801714020001c2c0c1000d07640a40000c1407104118954021060721403070804800d0302c6481c0c0e4010640050242d07061458003986840c0424050380d51035100c50441081e4580030809658640380182d100d46010425070b980380200345402900d401c250182078458400740c0b0285143c0242c107034114004100c0a40724982295551850400140107100e90f002018081c0d0014401e505d11500014a00942403010034041c900705820003001c044001655026250f0003801203440b40e640d006200014081c1120301c1c1503611400c10603140803042d109045040c1e9000d49 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198596151 1250 198594901 198594917
    0x915031d07050d0813030209090f0c010203071203020306280f05040b0901030f03110307030914100504051512042a050d12020109150509100603150b0a0e0c0901 70
    0x92200c0d440e10054850107030494110648107000450307134001071400346404038030300e44159141d0700464040c0c181101c01e800c03158401e0305540c0310150200001d05102c8400d00c011403800c0594ce543c0c40c6581400c0050380d050640200105000d86e035407215032201c85070324407414040c0c034050703507200c0d80b1400891107001c45410360501f0205543c14103010b00c4684d020080d00c005541d0346580d40d0360b40a180358144c2a4104803400c03443c0c0e65605070078801801814025520782c601581484207200b00030448003400c0d441008038802c1402c0c0581c002e400e03942200c0003291600307081d0b10031007000415403003800068002c020b0060104000c100610f43c41d0004001159440313520074002c20041c0c40c130b03a412801616404210b4a0503c40015040d19800010103140c1c800072030800459602c100a50544028542c4100d03240c1c0f0410604901c00c001c0c03c20300e01c0b9903c00a220b003a2560b2140054500c1501e40343e5650fa4552000041544030071055100401c5000c09000321460080a480b500390001095107000481007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198597401 1250 198596151 198596201
    0x90c040f0f0f0212040f0f08030a06060e06090a030611070c090207170403080702040c140d090203061e01090506010302120c040905103f08040905010902040e130201091503 75
    0x2034800e0300d1a1138801140c918082c0c9403a11030001150780070400311240a20a12100c1c00621000e0246000b501d032948003084003030502002600c881c82c01e030030a6000390014440d50046548415500c0c00301c2e60000c000240100f0b100c102007c141c440d4240c00f0304140c4a00500003403060030fa900804003140113007004441015030300c203000360354411032101a2204800b406114050300e8140d008140000130390510748400044145800442c0e00314842c1ca441a507510b68003401981000d00c166070f801303548581280359150070324188020400040c0100b588072551140040d500c1c3c0d02aa0403280b80000c0c52038095050314066041c14020703405406001e40d0341e81041d0204448106c4240c2c91b078169402407590f400c000e2466256401006103181c129030b01011890180741c24040d20008203070000313000320412a52242400c80c40d000703a40040c1d001d00d03a914810082008842c00583e815074124090b00c56980e058405400120fa902d40740d50464100180c00b00c80c810456605a40800031080a0103030f04107154400b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198598651 1250 198597401 198597431
    0x30703031106100305100c05041706070f030e030a0c08040e0c0c01061d0a2c0706140901090b0a03090512030106021b09060f0a0b0f03102c090c040f0f 66
    0x55210045c003690210079942034100751908001403035489854803500b040e55541a8154000742048889242e810480a016500b61b009146c0b051003011800c0c00e01074004c451318090382e00e118400c01c401c100101108540d040180342c00c201c83c01084a0304c070801640c1031940100400e80c0c804c18000d5003e6203012000a243d5030215020003803c00d5119030703090b46646001c00c1e100036021800500f841c00c030386082020300302c15001c41131b240b4a01140000300100c5040c45e9014043e490303c1c00c0d1322080c102050180c1c504681c0d002d01540242c82c282c911480c7c440d00403d4003035010303040d8074400400c0d80c082d2050a8020580d0f030000341d4101c0d9410343c220348401400010038113200d81d261040e542c000e8010720014000741070400c07416400201c041c20340c0d04c103140c0d5012451103075084a000b501d54150300106115951040d2101c22011303246a141b81c4180104400308240c41d80c03003c0e0041c007290403805000450784001030144024a40d0080c2c01841401e0301d41c1d144500804a02c0c110360603140c035001840040c0c40f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198599901 1250 198598651 198598681
    0x7080304060e031e0102090f0103051501030b220b0901090e070b0f0f0c070e01080f030706091a0709050901090b030a060e07030c0609090f050702030703080a0605030703031106 77
    0x2651034036003400c0044a02c80114200290140300701c0820840070302ca4024401902000040010303101e2800d20100000b403a00090520704050503c020300c00c00580c2154100b04580090034000b800b28007003800320302961000700c14100f00d0b0340342e01c1301c244880605802c144034124040b07414412903070b2030301515030407120a214540065808a2418044c149081e0000c0c1540c0da001c461550504140c00c95001c40356119100b000c3c01a0044030301000f402e41801c403610b0150030700201420000351400107a9a690040e03070f401401c4035880b1480c01c0e09100303003018a40c03003141416000d400140b50040c030180c00401c26204290181d0103a200004102d0000d11903003441d490014040c0022070000d8031210044c01c10441e0b0100980038401d00040054035240c5800001d04864940b002028602141c40c411111003506a21001c0c1c141800c0014070f95000c0100c44e5a00c0e4142000c91560316100c0100c0700070300564010580500c26604088241034000c40e01070b0518525100301c400310fa41d09040400102c13 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198601151 1250 198599901 198599909
    0x507231f02240703090813140f10140906040e0403030b090c0901270b1903060b03040c0e0424020702030105100509070c051005040303091104050601091401030b040c020601080d0207 79
    0xc002c0404110340f54400d411020409015592281c20221340b907110b28008085680032461141c2d040d60b191610382000e20002004140443d03507203240e0000402e0240003014600807030040300b5400105640c0c1a540c4005441c043c041c040d041e40c0c2149003e1401030000c20304204820f200c2c0d1100c9001500c620175003011103005e00410707982d0010700c1c2d00e6003c48498030314001e0480383c0c18a18255011a552034000b0140c004522062600619110f440c6030240840c1e00a0b040381a40078407c000b08404584181c0c81e81c4200e0310f00480030000d80da10350400380c0024003454840c1c240607031008d11540360078005401815601c1e0003107000f0010b40d16a44548902c1d140c03141b041d103400000c840c000078086030041d0303003074800036010340169031400c0202d541c2541210300c115411400f0980d108950002e0056903501c452031072001f03860800050034030030006420240c0b01c1c0304880440d4001c6140400c56403190304043c00301343c009402444415501c00010b511032200340241d1015110310182c0200c203a1000640100325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198602401 1250 198601151 198601213
    0x903091806150518030a052d070e06040e0703030e12061017150903460201060b121f0e060f010e2107050105070507231f02 54
    0x34a100b0415242e40d08044001c1d5443e145030b440b20501a1400d022424107244210040c01c2000001800480e842000d041a415141d503c108001807010000a8820130380c3d03000c10071040207590b2480010301803d4400013050190007904000410590010b581000c2c3e03940440c0c00400409103100641c1d561441180d41e4031410680d141c040000144484a4040404c000820f4910300d0031043c0b02d10802e4001940c402140c0d42c00060822418031059040103426000c442c0008040140ba20700040d000c00007072141c41004c15400700d051070160003540300b00028200396003c03035117440d45d040d15940100d03070840d200007101c40d40c0844007004042c0007101c034056070010b1100c800e030303034554000340448164090070a605000898501400d2655111143c16910340000d4035150010b51291900d41490038590009040c408140041c000040020814000b134544000d090b000320300d0201000d000790664803030396641040f00050743e140030911025030381d8601c1045800700da0101211203032050400780446215490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198603651 1250 198602401 198602429
    0x90a0c03020f06070c03260c0a0b09070f06080412080906010b03090c1203030a0b03011803080c0d0c0203070308011203080402060c0a05030d02070b10030305121305010903091806 78
    0x14948034524192100b4060081801d1440c0caa0b540c08000d106a001a580e142400542c031914002e242003641000b00c3c101c0d58a824507810b403486568030320342c802c002000e5a40980c0090031510f41080307000014a08444d4105030f840d0303600c0d0f004d80040340949082d102c8402004000e54898000d0078094001d5404200400003686031589030215a040074081c11240d00410f000441196518015805004002c202843e80c07421f100e1b01d48001c0b01c5480b55658000e9050452030014111030300d145003070f02038150030424900d41c0c82084d988501e1081c4a00c80302c0191070002d507442d00680c004003404040b40300e03443d0420b01c0c4e43c030741c4068451480741c3d01c001000901c03068001001402c058018180c20109001180c1074200e1540d00e2a0454101c000344002456000c207444c42444400622990080e10301c0010200c414103540b0010312610960010341b40c0310b00d20102158092030a030941448440d0818000c0181c0e40043c03400414500302c9201d0043e0800b101084007081151500c034a60481d9141500c82030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198604901 1250 198603651 198603653
    0x2040806011701060504140117061005040c0318080a09090e06180a02030a061e020f0a1116090213060f170c1308030a02060903130302010c022206080105090a0c03 71
    0x1002070764000301e011065495444c00204d60701e45003c0c1c1c0c007800a45a90302d10096060540201d20340c01d071652450540c1d4050000e0000d4119008896001d80d101038801041e0038000d8482030b000350080800c1c0c40c2c920044041c20b07000b8420b005020b00200c2403240d4440d45155501c07003200c000c0d00c900030903139a855080200410030208100001d4106441c00506031844030a00344c0009040201d10304060720003688400c0c55644c001310100003d40c540319003003821030400c070140752481d810707000d8002440140304c640d145050814104215010525001d03141490449444101b0300c000b9410442e030030b4110300c00d00c01020903440c0c010b40014149820507940d03515843c146e200c0080701c0c44805024120104000c01400c952000c11038040006005200020f507501d0042440091610800908640e810b8006110b807220000c0c111080600f220380910340100080018000a140d601c8801407005500d070300b211102d400c1102640100d021103500f10700801881c0d96100c070203034071580617800060074010440010301c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198606151 1250 198604901 198604919
    0x30f030a0b06180d02010309060e060124020604110a21020109171f020c0a050a0c0b070b0118020412050c0103140622020c0723010c0f0609151b080a0204080601 70
    0x14036213071700514002c507104946480388421a51845240003594000b0700051000d20441a03e20404c0d181403040c4820b041c0500d1802501c0d40f201420080860824504890b110358920b0181300180404001ca112040c030f5000101c21448066034049010885001c0000350b60310142000ca11880d8001019184254008040ca80410040c07242e640b4400e600384420784005070100720030341100f48118000d0944c04018104090f12030001c0d80100308884041004900082440d14410304441050051803041410700c17486101034000c42d040040b09c0400c84d007806060000005001c0304502c02030320108001205982008a581403c4134403d4110349600615a81c10f9070782030100c100b2540d000001170030001800541070130044030768054210720044c1800d0411a0000c500c1c035520a032030900b04106030350402e83d501c400c080903012018101030b5507809514280002560040081203400070304108101d180702030310f083d4040b0403e015001030081400104400c03014400c4505460020004101680c6800080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198607401 1250 198606151 198606169
    0x6031509061e01050904082a0f120301050d030c060b040f0b120a031d031c05040602061003050d08130b0f01090b030a0f0611040b0406090e06040b0901060f03090203030f030a0b0618 79
    0x1e40c23120a180a0380654a070300e220401540395003c01c0c0234003144604010b88529101e84075002e01c0003040c042004100036965002803583c03c030b0f4541008400070019060402c000c280040b90300c1e81050600601c8010401c842c1d100d003084000488031241400b0051395407550303c4015401c014081042518003201c4140018003218507118014101c0d0b00038010400021070031032230001940d01203600442c09000494042c45a91b40c000c4011a404d0ba5261035500c41a41c1c5110380c074494414400041d010035403039448070880342442034220303400c0ca4090a010141500301d500921070842e0551400d0010540c030b240c040350f07100d0a290003090082d200b00341d640b9068024a4800801050614100000201103042c080540000c0c01c440c1c444603032035803a20684030700e000002048584100d01e480c0e66120940d81c0d25664038191038207881d140c0e510242070381c411780040c12806806941b521020680020411400c4015031045010b02e0342403050300200c1061000d6405204c03010000d80003801540341840c10400030f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198608651 1250 198607401 198607417
    0x20c04020906090307182901030917070c030203070b0702060301090506030a0b07030b01021b3003131809080f1806040303030e0c0102030f09010806031509061e0105090408 75
    0x110380c038068000001a103000b01e030380d006041c0440360510301d0411580c030340305140d40501c9261124090110b00c182060007d02d00755085414955550703130440070b020b5009000c00126034420601d6548400ca410629225030203480704910030700c58008003241c021102000e6815070f65002e0034a0303003103034280a031a2002d04402401c054241c803510044201050340401803e00600da2030310005941b9451000090914401d040b068085401d01c0d0a02051502c95003ca01e2102940441030100c9400009036402008400d60fa004a40d100104000746501d00759440b4030708465000c40b8142045041020f200c0980b4801c541c0604109800d001800010001400400d800941c003203010080c60541e00c00900140c2054001b0f40020355551540900200100074000e02d00c4001d000460410300c00044410103442004030460401c4002008100076403001c02c94000b859403001c01c00c20240c42d05055007583c44504544490b000c848018403143c40940c00c40c14141079500180c040b42d915a25611740030616071103008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198609901 1250 198608651 198608659
    0x612010c0e0607021512040b060f010c030f20030c01050a050103020105040e0a0f02070602091804111012020304060b030d030e070e040f061b260411060d0501090603020103060b0901020c040209 84
    0x82400c001161034000701a0b0130382551b01d90016042506084016180c0104010f001d160101e83c0c1d0146680c2001c100207020360715241524071281e146000b12040354048240c18020740d90bc82010311010350120213401c08030303681b0008001540c0c4144149050782d40c02e2002074042038041000f4011440c3c07030012658441001d1303402040c86064240c1c0c5008a9000c0340080e1030031507000c11115024980050851740340f14a010344084941003944683c8844000365018a1040001511400e505401611004101417074003004549916043c14041d018204540c8020710a0141d1101c514166000380705014480c117210004000150401d85542030b040400751060752184102d03104d4200190a0303002d5070542d807200e802117400460b0596400b50034213a40302d11110029014002d148214003220480c580e00682200a0100ca00d0700079020030b501d80300f40b9004c00c4e59641001c0c00426000129040030b0212807003a601000400c0d81c68900d480c450241e02490f60041c1c01280c03c03400e1070724254000d040c110710010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198611151 1250 198609901 198609919
    0x2030403050f04081507080411060c0a140d0207050d03050301140d02061809010902042907050a06060303020c060c030901030e100c1701050307030209070503071211030612010c0e060702 81
    0x82c0048100e03811903481190b19038007086550ba92101146400d030340048081c00c10318014101507480841c034108100c041e5005202c04140f03403004500820058030010b803c078024842d1002c42d695800d84035072540325401c001d8420a00d001035541001403080400035055034407982140d080c070b0b070151404841c0ca0703009a07100c8034007510000903940c0d40c3d00500074280707405480600780d8003140510109001c16480804214410b0108201110b16200c00c00121003800001c00182c1600100c10050780c002d188001e80144940021441042180c0d489641528065021192088940c6007002040e124945000003d50418403078004654002d40107500c0b07010300002501e01e4108000c1d80d0074101c4800c44e80d0000040d040c201e0308010b00c43c000b51050702500d000e402400c815425500441c1c81010068207101c208071001001500151040c4030854150a032040d0500030070040c0742d2109055003068619500c40c2071091070003801c12030305216506500686032502c1c01344000b16410000c141d0011384c82079030060429 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198612401 1250 198611151 198611167
    0x30106030804080105040b070e010207050418060509061503240601020a080309010614040603080a05070f06110a0e0103151701020c070602061008150a090809130218041b030203040305 80
    0x180c000b400c007808400b800003c3d14900b41c01c10103015400544804144000d110075246070b640d011070142c1c29100b0945001c12110b0000c91035800410a01c03001502d1185003c0c18010600c4020800500558010709180341007045042010f440c0d04070030440f005072140ca02a10b80b0f5001003110440d900010500507100701d94801d03296960f07a42d004464881499644d543c0c2404842180350040021800c15181002113505659075100380d449a01400000c0c050040365800c10450059032500b04143d2124080c08801d059411200450f0000c1c2c0c002e00118610440b01411540b203403050f90038410180750b40c1e840e0b003482c20764001c82141d080d0390741071680e540810003810403200800c01c5100405050b0b0040580f0b213048001c0f40c94404281e04801d0064201030b4603503154200c0d0403116030b080b01c3c0340752002445206514150728070b44541700005810820f40d09495500c07006550240c400d20460b0441006214011020070080b60015100c5105040c0300a0900031003600c00c0d800f03107606c02d11a0500501d01800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198613651 1250 198612401 198612413
    0x120a020712020c0109060e0603040615081f1a0a090209191d07020706090e100305190605180a171201030809040609020f0d1e0207030c0c0b0301050904080903010603 72
    0x8400d020401580c01030403215070f19644120a5070080c4400d280c825040076034a00018002c2c0f1000e080540116111005126203040f840c40701001822040c084455920703048007202d8840d0a0020300e0160b6034a400c0d0340303800c00445075401407030b0004002c054008075410180c01c41e0080d0046100c03d504114400d2500c48a003002c40140d034080c02d007000b24103e44c0c08034440c052485040040008045400c030400402500e50810080701c2039880c6005080f90513964074074015003ea01c2c42c0d2000e440e61241c05144145202c075020f160101c0c81c01382400340046d644002416051045c2d41c6140010740d17219600484c0450b040c0403108200e0046100030500d0032000f150803064148081c1c0040e1241b240000d0205800e2405e07101d144010044a50190306001041d1903242d03040c01050084141207881c0c2c8955502e2400d400d40c420020041c0d01d00071900c2d0912410700825130aa1070004540580c28102c010034090414410b5078100d580040040c001c40c0d4843d078034940c903074000e401c240c1d8142d03484041c04400104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198614901 1250 198613651 198613673
    0x50d0201051207030f1a090105012d1e0e040605060412030e13140f0f0402090106050717040f170708070317122805390d06030210030c05120a0207 64
    0x264242441c441c0304442000000441a4046418000700403000d559007581401c02f90b0900c01d400c8512030042c4078030301054079082500345000c690030706518007007041d090700917088000104050b142004904d440b1000d12280e441107003e0010250041520940007a1003001e2607107421402611041442d101007211900790b51400c6580f8070280035007010449180e02c2625a00d9010750121042c501c64100394002c1105070304103020f12001c01500080e04800c0c03051201c0212407403903c500c0301c15a10303503948018890114050150407180d03a400f10b54010300b5640020707a03c1c10740f079008000e002058950340d51500a080140c01c4051400414020082c40400404165200d0b140712404a1200401c9200d85003000700740c020a0b03001c952505045c080e031440c02d41d10002c101d030341c600c4100c012120b40d0000d1822000e44940c030740c40c1800d400600e00d00803000c02c0c3c01171400c03a48292410102c91b00c0484007641034884c40c0d4072801c0051800e110580340b40042c020b5941c2c000b084858014541000c40d112108050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198616151 1250 198614901 198614921
    0x1f020a03090c1710060b0f0c030903060a0c2c19090c05040e0105120a060b01021e0d090b120c0f0403121d0301020f0315040b0306090d02010501050d0201051207030f 72
    0x2220b00071040403840da042c0007141c0740310344202c000c000f440c1c14117100146d98010a860a02441408076581600e02e204100711050b0040003401c030b40c0540303820900900507051004044001400d050300b0f0340b200350001020340c001a481200e40c6160b80041c241400000d03200307540009005680580006070302c46203842030034181c1c5207641d030341f40d980c0341880380c0c09901c80410780c030590250710301440100810b4070116842d1501c5034485000301310907200c240100c4c80c0c2800c181d00c1160182c2c440c080780340801c0c0300254411070020f281d11480b0305203540e961281428003031010808118880040000d0350091140300074203c0300c0c0b00c0d000d09428103841e501d07201c0b82054803020f0000402d0352510320040250340031001341c0d52000c0440080d8a0300440614140301804041c2c1840012000002c0d035107500c0c1c1e21500304800320030029045a00c51301d044c81c926a03660120030341d044099481c05001261b54140341004107080c80c0c042e1609442d225651013822481c0030014180c4040554610b8400240041400340007429 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198617401 1250 198616151 198616169
    0x311061c050609070c0201081612060b091c02101404090617070b2a0102210708011a19030e06010602010e0106080705010903022b08071101021f020a03090c 68
    0x351a00790207000e055030004e440130081c003100504040051380e211240960040c100034800c41e24a5000c1000c0c1c445802403e54480300d20f05280e004030301400c211001e0040e082e0105c0d15440640da06074000080b10b042031030007941140341480e0109540d03008240e007189183c2040245440c0070b90b0347c603030b200c219015a004141c0c80c0d00d0b8007810301e000d130404106410103400c5010300f0500d0311000440b15901c10784440d05243c6140d0b4000109a0444000c0d81030700c05070290840b18000c0c108800a408400348022104040460f0403940003249002c0401000074209401c2d000c21440c1080c03103a005000165260286801c150b01d8440041d04030a0601005000342003503000441e280b48054002030a41d80903400bc102c4540c004070302041240c1e880016401100d8058504403800340d0b0100c000c08442034000c01071650201c10014403410030142034024044d5078000ca8028009591403c01241c4420711020072008841d90400007400601d1258001d00b50010282400181d40c9040e95032911849080e0303000c5614 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198618651 1250 198617401 198617411
    0x40b0402101e0f020f030316200c010c02060d09141e0d0c0812010311040e060601140c25060305010e010303051801050412110f0612010311061c 63
    0x21814620980c1d05494070750706003240c00249180341c0d40403a0090025800801c4600600081c0e0b880c000d01c104801403908000b80e80d641d02d0081d501c2444010a00c140c5000603c11a1003000c1080b0360119021104411702c02400b01285114011240010b46910980e804501007052101405a600c50b400000e0300c00c007130300c4034401140580701e8141a4074218407104200e4160b5600709140010031200f018080c641480c0195290741d051005480c00340510143c09210194000b000703108125001243c2d090084805002030f24608140b0340c0c8030300c0c0c10f0f0358480c0814001d0080e070660000d441d0261029140f01c0c411502c010400c07064010030032815100220b001c0c45a464140043c40c6d0501850307014101000d01304250303524555000381244034103002042c40a41001c4941d00da6071081c411038005108102000023004007508140140001c070ba0040392065088484501c0c0038140002583c4810003408225885a807860300c86c001440415155154040c000f000b00300607181c0501c03440c0c0340000c41580000343c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198619901 1250 198618651 198618653
    0x1d010212090c0a03031b06021e090a090219080411031203060a05030a0c030f050309060a11060106020111090f04020f0a020d020714130e07051c020306180a17070b040b04 74
    0x100701603451114034010b410540051011941000c204000100341542951b20407040f418010001d01403030706d00d0040000101c504e400c0c1c50408401400d102c00007102c1e644d80b56641c40401004078890806110080c00540890407952070080c0c40080d0301a028003092000c81c0114000a0309210b04100009050740000c024841d03282088416000605420750081c104035416496661008510f840000d020340309810850341044000e20a440d00550060021030300e481e000600941203681101c0a400c241c40340d100009001072050080c0c00c1701c2d08101c0c0d001407501000c0010700c14100608444190465001c0200380c101284520080902280c20303400391554058030038001b8100122580301e0300481806017500d074401d588044000010000e80000092144d1681c03400900740500e41d40002c1d1721040e07401c0102e48044134844c00c07042c010320071400d550195907080384042c100c80c7d0300e03942c00340705600c8040101c00003200c0c80240312a00020141d00d034140841c55070740c50341c004022a0120781a4010006003c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198621151 1250 198619901 198619903
    0x5060307090f091109092112150102010e0c06030a0c110d1e080405060705160209040c08160f0e100306020708041703070201080f10030605150109080a11041d01021209 73
    0x54814202c1d10701d241410170002c1d2130760b191503100c101444101101c7d0a4080c2c086004112054519101a04442850688040e02000441252003400b550a01d6000c9040741c0012440940131000100984c0c15506d45107007400017003510101d10024800d0b813040090311107004100040711281d071591102c8514201c1c01c07101501c001019291010b00030f80c10700740300c00a000400d04552110040c985580c440c41030925045892544004c040e4010440b4014001400000d051000c252000042103c40c0f040c501050f450700320030705210350880320f0000c40c001d01c2031000c8604030681080c0d100403202041c80e202c1c2c9819040b82d00005081781c07406c20002d410400c83d90081c00e004504043c0c80080c0d81000100e0b000641403120041400754150044000241440c0e21455a440515044a0200440d02e402c00c031102c14150360300070080c007040c2480070019492000080c078050041d0f200071031200081c140350600015081401c00e00849030032402031a0720701d6509101070104084100a51010f130b04018500c2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198622401 1250 198621151 198621173
    0x7090603120807080112081c050412181502010204230a0e010605090409020103060b0a02010906050c0301120305250503210606040e0603030d0207050609060a0204140405060307090f09 80
    0x61052140c0c40d4200507000341c0081100341181c201e841c1c9480000407078a0442c010380f103034407440724230a2840040c40004000c51341c400c600ca20b100d100304100060b45c100081e02e40c1c400141c146009524007441c01c1c041311407000015042e119050001508254860800304080c401400c0121042c11140803071011510f132000e4103200802d548050080343b0350428200512a2140c5000f03940220385446916045902c0381d4410070041a5401041e92103901d581002806094000001c0e5030141c140740108a2a00000e02240d040307407444070540418100e1a40c09032155004900062800c040b030207141e0409602c814840aa07851282e40916640d80e41440144100b1003180c106c4600030101c582000015202c0e1781c111001e4440c00441c0f06c8060361640c0000b4514410200c021903054008100d500410034005280703070084185a05403030780d9a0700c2c00000000c0f40543d200d1003001c07440d0421101d0944c1403507400b090300444003905886055460781440c00c161864050340c2c07448190303111140d6003848003403044 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198623651 1250 198622401 198622433
    0xc0309060e010e100c020301020301182a0f02070b0a0903060507090308160c050a0f0612090b04030f0c0c06050307020706050f19050c0f03070b13200a030507090603 72
    0x1010654021850000b07203143d5004200c1400351082640c2c1d441c40070f0041650307201e080c0c0d0050082d581c4c1c1d80c4403030b801c1d03481e00380e403600010307410f418001c0114000a080054184560b003d414074082540f40000071140600e811401109501a8050100d08030044a00501c0048460b4079248850307442c52403c5401c03250002e00e15002c00503031910502c00100c060044602d450713081601480b039800c541c00c00464403507099100a6102c0c0703128200196407624160110300f120b0064480c04d254802607204801034407034130f240040203805100f0000300042c0c002c0c012508801c6061800c8424042c0e1582c1d02050a072042e04a000410380c0841007008847c3e0400c102c6016107440d241c62802c2940c02082c500890042c2114801c0c13941c011418820700c10b12070f405131200303928198202c0d0804402602404e0316544800d900307607065042c800020300580540c08074401d0a960040407d1748082448004800000403140129885000d64100001083c420044440609107580001428601d036107001030420911300301c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198624901 1250 198623651 198623657
    0x90204060c110306070e040c02030c07120303140f040b220302150916090e01090812101410030903030b18060f0405072001020403020604141203130b0c010902030d0c030906 75
    0x30807242d50386c440c0b0b244007142404e03100402c0b421071b803000607415401207078201c02c110b02c10341000081402c02c041011800d14066241040120318244080482200480307003440c2c131002c45000b01c2c0c0060400c005040d07007d500012070030484d4010520b420102d0503114030075001039000d10440408001c0000ca141c0d00200700e074008010411403c54542c810a1191003050f04556880301c100c890000d080d007102c840ca0760b20814103071781d941103c050b90306480d000741c41c1c8249035284217401080c2141c12a10000050341c0c001c0c00d00043c182154421006001264000ca017019210b44400d0300d180c440c603c404c01101440c2d0880040c0d0314000e02030182c48070b0921f1500341f20340c0c20001480242034019540c214800d40400d842484852a007400703601910481c2e000940001c000140003c00340700d0344101d03035003a110444902000302180c448881d0b5900400040030704030051400d0820030900030708002d1560003460000800e0344038503600020304102d03d010056000c150148902001c06900500c82005048141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198626151 1250 198624901 198624913
    0x60e030316050d0908040807060f050a170406060e090703060b0603040c12030221040806070903030518040608030408030a1e17070c0b0705040501030b0307030209041b090204060c1103 80
    0xc9081e05201e0814100c03000703004002881c1c500b4090150449280907411004d12aa81c3d5a078420556603400b01b032040c1f800041d0146e4201500d0780c483e0088405040c080e90710244042c9054443e1780030031101600440328141d03904000a222411820313505d104001d0000a02000e03440e40c1051815100b0742e030600c501c940420000c0100250400c1034982c159413500207040c0b50b440451a040e4030b00a444502500903607000f807000c542c0c0d80280c01c01403066070980820382e8440e880c4e0f060151101c05c00d034000100840c100380260258038110032403082013410014004188256602151411a881500004401d8100048801e072854001c201621240c10300f0111150301130040c00c004020742030704019510091543c6020884580c4652140c860300d44c1c120b0204c84280c2481a401b8105d98060311405000c070341420f039407126502c0c002c21013904580c6c002c1c1080400d1307030b11a80c8800d05e0f40094070300400c0020802c000490140300a102902c042e000ca5141c1c003261942070304001c01146180310304144264055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198627401 1250 198626151 198626161
    0x5040f06030803013b101706040b0a09021302070210140a051819080c0d0512070303020c060c180609010507120509031609050a14011a25060e0303 64
    0x480300b03c0381100e0b0303105c000304844c8140011001142645201045a1032031311240d9254455514010030b02a1007161444d40c401075807030303520303103022801030004c0d0f0540e8000c500060f003c04c400300450f50f401882400005441c580384d9000503007140342852501800c3c0c0d808a90401141041d0315034100900c054200707080c00856624040c0c280c0c2c406c09007080d04002001c03034002031000520320441124031004000c04015403112428000c001003030310400e010351103070540c1c9182a0505010000c4441d800a000d0010202c01460b0b002c0030764000d0604804041d400c10407010100d00038089139004003186401960340d41d4030054690900c401c40d11001c2d2141c44100104040c507a001804c0701c1c012580403101083ea15140d41c0300359a01d000b500c0c1426054000e03240305030500f80b80185c80c2001c0d0350000004000356110622a9000c072600c118400465481400c0180410b918412400241e00d44040700c15240120314000200c100014818020580f05a03101034000c11900e4040d100c0383d000315030019030940c508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198628651 1250 198627401 198627413
    0x6040c0e0c16020109030215070c210201030b0d02120304080d030b1e04060504050c0c010f0204060806011209080d05040212010507020714030703080301170d1107051003020c010504060605040f0603 86
    0x42c103080501008407a5040004590141040a00a5070010201003e1007011a1070034015405038000300c03000384441001043c08101a2001c0c00d038024103600603203602d0318640c0150700404640d84110307480900580508016030b644103410182c0c454050181d03880c1d5192030440b03880c00003980d101c2c0c02850305140283c1042d0315088510b00e60814510050300004c512003001c0f400a10b01c0d41c00c0150483c2c1000200903000c50404010300a0040c820000c02040c100c10904070304034007450060304005180f4070f001c942c5541c0301d80080b0b004001840000609943e140d40c0e80c03079440d40800480d0091035202c01c00c0000b94030301580303c0c44088141c0d00080c04a460300345802900c42010780903040316140c4d18403d040304d03500c0400c036500103180e003c01056903a5031101009840e200310b6103200340a601c80c00200d40c52092140301002484101c46009000712400e01c0c0030071443e0b04805400d030007007590034048140f01c94424010640114012500060b696041c00c0910080c0d6440809207005141880d10400020380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198629901 1250 198628651 198628657
    0x912090b030f070c05010c18060c0c052e020a0b060102030a020715020309030f1b0607050706140c0d0c060c030c050f0c070f0608060301060e04021c03140403030206040c0e0c 76
    0x5100807036202995549800c1c2c802490b18040500f0541c6801c0c0000b007e1a08160807204010824560600302c95441e802141c4106440d00000c04c401202002081281410900c542041141c1021070a41150441e41d8084001e841052000184d0220382c50304240704a440d90301d6001007003031014619024508001a5071b0b2a003e10406001c03140c030890001155209009681e12404020300b0744400c04003039031010342e903080590500b03401600450269241740c5444402c0344c3c105980300d009418117914241d07007a60845943e40c900304620004204008400c001880504c01500152302c1c2c65103445000e0410100b208c1c6507903180c400303047ca03040c140302d11581c0040c00c1d00c2c0745410f50420142d072042c0420b041401c1c1841079202800c0030440c00004100240c00054031842218160001c00042ea80e419484040000c00e4801030b401241d419031508a40701082000c10b0654080d00f0304403117104002400720002d5200750700580042e00320354107000801c00d01090304001000c0351a03511110f4184100790420500c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198631151 1250 198629901 198629911
    0xb131b0309111011030f0306090709030209040f0c180c080601020304061b1a2401050703140c0a0506010612051003030212070c1a070b0609010b04050d020301020c100912090b03 77
    0x280490481034543ca116400d01d809408400c0c05907510303210012a50b40003900181c802600c45c1c101240090b400310f00c1002d994045940007040e4603c0c035103860b103c80b4894010218150340c50841c03000041094540301c582a9444803807000300080404040f60020914800500914115041040304010050b844044003590103240c904084007941103280c40345040310b081008510319508681005441c15004001d4450402c4404a021078242c4181c01182d440c4661140100820307500c81900880c0010700000d0400704a1400c225840140a6120749142ca10b0983c040c00000b0103a4145003485002400303010742292080c56442d1440d800e65a0180d02d4221400d816070041e00042040d5082c0a41c80403681c1c010b001c100d50300c6280c0480382051080c1d40d881003409889154102020441508001c180d00e41205d8031810351505042c2000d04002c9184400b034801daa0640d024820039044580512056010903400c03c40090f007140c01d0300e0842502e203840300d2403000340000c0540402001e40d8407412280d00c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198632401 1250 198631151 198631159
    0x5030c12010b030a0605010501110d0915030f060312180308040506030c041203020c151c1e05010902040504060503030406021525031d01090804090c030b131b030911 72
    0x34000c14264600600542202c540d040c0314644144040c8082c0f6803142e4144d070400c0c0d03070b461010180441c400b07541d40c904181d00d80005090803800c010300c085940703014241108501d00030940003410500c42c1d099848d2a0010b6441d9122200c0d564410342c0c20040b440d805075102a50004410701c0d41c0c84480300b41c05103210346e03405440e00000040c0303601c4c0c09800f128060314250340102d00c481c03000e0034021350750356500064a019403182120448449440c00c15619540e40701c14149080d07400c2d4006950143c144030816800e408a05110380040c04c105e0301502e0f019081c140d00050300c0d14038100410042da0500d03405176010b074204000030311540317901003008090f071807181c191040380c0c2c3c03142c0043c0401001d04007102c4031305140390300e4042c6409501d900300c03203510304114144601170004d008102d405c80c3c90b035803802003114070104420030076440c60350004081c4046070704000815130706103c00f04060701c80410300403540554900d1071018100382005201e8500420740780410003130105613149010740303801c1114544a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198633651 1250 198632401 198632419
    0xf0105101b080f0c03040b0c12040e041103100c0806030106050405010509010923010603090507051f0311120118050c1204060b040e12040305060c0304080703140408011406041505030c 80
    0x4049401c200c4031100300084c02c980d0b84940d551803229035500901d482c0651809280d00442c1044515420313201683d1100c0313580e2070144c0350399541d0300004003030481c102d81600500b0562800c1d56120700c10340c1304410050f100e00019280040415085801c1608a21305c03c074074040c0144903986400c05030f54151041010005540340f103810074034030300310050742c0e00c50503c414a50000c61040d0380343c0c2103146114815400c8640345038944e000c200c0e031003801e070504080780b0714001800280c091080e0040c1c91401c070b2070910b20740b82500841c0c80404505098000403104220800b01c0e00601049100e0640e12000219a8900300410407548220040c000740016061540705c9180303040a907102c1e40004050341ca0136080b0703404400c0d00310441d40123170410301c03054840b07019420000ea070200c002012070b84165401701034280b410165a41c103a4041722924028a0203c0043c800456034020900c07038a00200c0c1181e00c0c5107940e1400404000036201610340170105030704101e43c10080742d10005016590b03150200e5886c45 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198634901 1250 198633651 198633667
    0x3050c090a0603020603011404140c090d03030f0c180b1603050d140f091605030303040f03090b030901050103060e0c01140a1b080a091d0a150902030f0105101b08 71
    0x2e8892604061740c490000400010170042a00e610b1588140581c0c09124101d52071a00e000c075803d044a45244d1800b04000140c220318045c408860128403a04000035180c41e11150202269914100c00c0049442041c00c0c50103a100d0000900003441115842e919182880862038142c5010780001024400701003207110803180503800080c140a44441d01250600c0e1402c21451641c60558080c4102d00400164048070708038032001b841a108007038011851a2181c1c0c0da24440101c03024000d4080000e01000400d510312034100070f600035188040046080e5040d81048021140c207490a1201da500c5800070b008142d07040800c07095201d05017216a51107101406043d00d2000034a168010590000f544a00130031040c5005003102c040e072a035030028400d0326481c3c09000d540400300f00c0350f00051000e000402809180c3c00c4040e803000c2c0309004a005aa913241007402703a800650380701085000e201c0051003a420700054170310088107e46010001141310034111269007240400141c461800001c01c08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198636151 1250 198634901 198634921
    0xc1206050c18131e1506051318110a02030304030206060904230102040b041205060a151202012a020f0a1203050c0307020a0b0307031a06040b0d11040f030507050a03050c09 75
    0x50703003803050f070461983c2c2e004441131000c00a200900c400843d80e44645d101241c1d083c0310300240c03458175040c10029080d15080101c900113000300307a0070406e40d03a40c451416441d503403110b001601035081580c0055031a810306141c068240200107245c507000f0180141044040b45803006c00d010030070a20b00e50b00c1608025050000d001e40300e43c0d000b418a096001800141d856005500402e90078000c40c1a500d0503100c40c00900103035011003404210300715450105000c48a07114100d00c01d89441410500c0449101f10000c2c09412850b051564800d00c414481400350700f0700da003143d00f50341404c6a01820182c04c2036940d40000050b4500502000400b2a030100280c0b000c0088680103500109200d060513074030b01c01000103900864000300002d04006000c401d514640c4c2c0091b40c014001400c4d00c1c01c082c104010b20003160031100303031240c00e1512100d0b03030388050000c44002c2c4050658000c1c0b8040355800c60804525101c1035601441c001c0c1c2c84e028040001c03440100e0015084841251080340360b440f0180c0700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198637401 1250 198636151 198636161
    0x2d08030610030b151c020a020c1005070b070809010e070e15011403090601170c100c0302030904050108070602010e24100b030a1b0216030201030506010504030c1206050c1813 76
    0xc541101241006519242c0b100300030340400003171700e0607250203c1d0102c0c02040c141c1c02004642e0000d64080d60000c3c007149056250010240403900d001c0e41440d0890300c48040702c032020343c0c207000415003140238001d0154003030007480e406003651401081240d2519407a40c450755002410400c0061008030051039684c031030041d8005c5500c405201d00d44a08258010700d885000038804e0f8403000041e21082c2c0000a000302e00a00614801042c204601c482c1c000217a42d0303400c500e40e045007140410011100c4070b41e20351040328043c0035941c0c0246141810a44060308684200c4900070a03607010101c0500089045401000b880103168900c41d2140c448503052000d0344030a810500611070013000f000800c404940c4486c00f05904c1c48069030701034040c0c00080c0d80740c401c80080004842c0180310b00b440503501a4208503005001850710341c1ca00380e0303a9150440c2e1441150041500000d8a00d100c0046c0100e41c0155070700100c030b842e001464141500c1c880001c4c1c400c0c0704182ca00403001c00c45180300210481d405 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198638651 1250 198637401 198637421
    0x5130c090c020714120a05060f010501080c0a0327060b040c03021c09030c05030703031b080103020607030e0a1809061116060c0e120a1b061407050304080a2d0803061003 74
    0x31658580f0807440d040d43c45123400c0b15100703480341c170030400083c0541c494011940588800c0c5421454010808011405000c0e0b4000c01c1e04400254201d245508200c80804040280958000115420410104002d880f8842c400c40704060051003107000703d540101800300180c1c11000d0018611a5a150540d80441d03044070260890002003032080034160107400049a45a000c200b007500f414280f0801e44101d4001e00010350010028407281001a000d0414030b030768140020040d070022666201c010036041c0c00c0601da02c4140d5100c0d1468410001c03280250300300507100d205424200720729400c0d0300e500312289800c068641c81d10303040820021401500d114910440c0503140c4440c1015068465076074480540c0b04460008014068000450200c41e105007999240d640c4c0701201d0b0000050210180c112180641e080e0000304800100200108540c2c81c4440c8182c61800303da8400666130342c00b10000c0040401c0d20007900002c0c0c03002a00c4207080341d50100040b10740104020070148120700134504035072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198639901 1250 198638651 198638653
    0xd020d0606030305040806090316020f180907090b2b030314101d0601120e03160c0806010f030803010302100509030d0801170708151905130c090c02071412 68
    0x1404010f069000f401002615408000c0340c0180e195540f5840d40c031720440ca101d505e02403000c1116001850144005024040000c1c260031071003c981e6031315140700300c041e50001c91301e03030214000700402e10041c0103800e8501c80498034080c0d61a90907040c00030a845011002c030b100c4000740344007400c150203a441140070015a4071001c0b90f0340f4105452881007410f601841c14281e1384444544034205906d041d041c882c54060303549280c0c1c0c0c0f4142e134000003e0038070180d0360140d6000070300241c2074007500c0c961916012801003219074036452818081d07900f400e406811580702d00700241402d201042c01841268111f0351b054410661128a24800712098001c10100b01da141c0120881c45440c268000724090507074030b100ca8106c8440740701011859403100f06120340c0385503070000004181c0a00d400184250700062030240550041c6d040d45d0348904070384003100c07030681c2f20070b4021051003442485e0303072010050031000304104030214400034069590b2030540b04111500c040301d1440030154481e01804007501c12440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 198641151 1250 198639901 198639911
    0x82b0f0e060705032a09150703202104030201081305060411041d0105041e0b150609031501030302070b120f09031b07050405060415060806040912020a0201021203070504050d020d06 79
    0x100d140e20203588000e554910030aa04410007500c0c01d21f00040b9521103605440d10440400c030340d1039502081c030758007160300664050030000460f6125079421000782011403c41e05070341d0364203510000d42041006051ba8075140113200418000620005109401c04e400080d1050940400d1700000e014007400200b10f0002c02880d8007410100c1415040350b80035a205e071095100410f04120355512400c002d240282010a0102c04070f0002800e089004060340e4019001601d070000120100703203408034422412403c0c0c098a80104203055041c4000da001d8607010200d6450f159148141f8000100003810740b00410906101040440c2000c004890101141c56035118201803070804264680f1000c0c8075490146003808001100e03841c1c640f140381c492180001d020741c4410b0401c0c8044a406000030300207901b0560300c1d0626804180c1e548202c6400210541c010030030780c260f0b84002802c01c0d40034000104185c8003030051080342034001c0e0503581605c1c8280c40f1402c80c0c1450b8000100c5540000001400007840c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 198642401 1250 198641151 198641221
    0x3060a0312020a060b0102010b0d0204200c07030b0105030a0210030b030c03060c130504150303050a09030215041508061507030201090c0e0402010f050702010c020409082b0f0e06070503 81
    0x21600c3c03628030740101020044142c0300c40c01a802c3c0c8030069242d50b4810908450302e8018a00356002804400c11600400c005000005506000342d100c0703044252664005007040040244200c65623003d04015800f500358200580d0101d07108050902c100400c0c0740e1078003144e44540d1400c00007000e01c11402002c45031181091701c1d080f95190f0101c90140d51441c4550404206810203019120441111342d425600c410320f541c404803595080a8a007808004801070004050f981e190b80b5442d0445003060402c1d603a40c41d04051604141c400f580d9082485841d40c00c001850b61010301e9040440d40300041d003591440030340740890040034000f00003003252011060209242c21128442441356100f0388035180080f00180c81942c190050000003400035000b03c2c00403005040c1034202a2000d07209002c4581400070072072146404204480c100003006140c10302c003980a1a00e07010314001d816030742078100300c900482e528450300e5030802040c003824804000003007107101d401d080c90340c1aa4410945249059220 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 198643651 1250 198642401 198642403
    0x20c0f0a150b0f101b060606050a0305060103150504051e0a05010302090609010f05060a03020d020d1a0a051e0307031a04300c02060c0a0b010503100516030203060a031202 75
    0x12a41c410707101c41d450409000041e003084101d5044101d0700400101455000b06000c5410500d040c55000d001601c5110100024006004000240041d611041e8484c02c40350801022200020200c504060a102c1d4941421030541440c01c05da400aa901089076030300d0344140c10003032317032011612041141400704101b2046c50561042e4184c030300c00c4400c0318030741c0c86034810070100742000c0c083c10001c600c1d090740c1045149031040041441000b103040240c02c0c81c001034003800032a004480d00850064440007000c0c038121164102400d040801c0b201e4000d85820840425443c800c82a01d416600032000340d144c2c165601000580300440e40031980c00c0024099222a41810200391005c0328100c2d00340ea9807110880c43c03029000e020303240141070a412852900380450f0780b08017012080c2d801c60320401105400200500014800d240140402c0c10f084d450a0189490180c030a51002c80d40362800c800e0224070307003002c0702d004126002c40c0b50141e00c07902c3c2c0303a00113900e600041d0304c010060514110410032580d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 198644901 1250 198643651 198643673
    0x8060405100902030304171006060f0905120a0201121d1f02030f060607030c06020c0717030c060112061b0e100c0803010b0a020111130509010b040b0409020c0f0a 71
    0x48039a06a038121020400508141c1d9603070003000390315400a100512140b07030080301195110b00c0f070104644910501404070f80071903c2075080b4800043c00e031100d4080b55500008848000c020989444a400c4042d10300b0a444031000e070300c02810488085403003820908190000c081c0801d00c100c03100ca403215500c0c11141e4400e1210031001142c0b00c440c2010340150081c1c82520300c00d007240024030001340e0311705081003c15841142c046062025604040c408188a0300c0902a240e040b0002042101c1c1040b04d4440940c082e02c035401c1095008000ca00020b00300442c0300e5044908030441484000c60b5468940058901e0341c2501e094101010322000090b640420300c001c860074241c480e50445545c0c1e4104a9140b15040d00252004000300300411001c0000710040084080d248000100032400c00300300001940034022440c001c1c42e1001050100e85401407256006011003080c1a01e058640910490503010b503205043c1c40660204640028440134804601140e91540564818205c40c0c075102502d00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 198646151 1250 198644901 198644903
    0xa090c020d050702180405011e06050f0a0b040b1b012306040903020d0e0a03050618060f31020d1a0a0204141e180703050c04121b0f080604 61
    0x403140c00041c041490007081100d20300c40c0c01400103805100b13450f60b05000c0c2c0700090801c6840799030744c0c40224800090a12000c8a000c00640041071003440e1800f00203d8801c5406e09070b2260034400010031103542d200d0101d4045600500d03805445800705a1121119401c1c0b246c0d2521a50904800c00d10352106140301c82880700b203100c4641101c2c0c959809120448240c0701009001d0f03442282e130f00c0c900e80c0c0140d080c4a0841340040c004203030291281e40785403c2c014280d9802d450300912c0c80c0016401c207010311006500001c040003c010914060400280d14031140c04500800e0741d10a080c02c1280000341700340f008440d0041c0900782600101c3c5800c407290829608440744086100e0040340c804d01c03a5000700c40403540c50841481c8070a06040401103010441c0c48200703004042c0d100e81005544030301e0b4140b80716003400300c03861400f403a000a01030300380d800040000d41642c00030002482004400f480b13011005400c6800c103030030b005034a48078002d00101da8001d411201025140000d0b0303620002040c038801c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 198647401 1250 198646151 198646153
    0xf060403111906021c09050102030a03241202030111070209130302010603080f0a0f0206131515030311060702060423010f050907050312040506090909030f070605010305010c1e14090a090c02 83
    0x9040b40301c2c00311886c1800340200c90040c1c2040000303a031582c0c8250000c0d05401c070190202640310039140f80100c0380c092507901c14034404d1844c00400d01545802c3c4605500d1403a0a00c4461400d00642c1c0051483c09000b0403021201c0305d41000780b02498801d6200d1805545d111105a5a640e0450030031619500610040310001e083c0d4103030380440920200b4154041c0f01c1024208007904059138412903803030031140740360104a03078444c0c20440805100030702c1c1c070003103000c2d4464200e84010b0700040d5080ca100101000300790b40c804030511001030801542e4501c0c2c441036002d400c0c0b0180c3e00c0514680940041d01030006024201003c0c00748070030003c210881110412011075001030844c0b0b80800c4540100c0c4a1036a0184040c03100c6144d46c1403619140d40e001d0001000c2c3c0e0701d0101c407517881200d1600000300544d50300d47c0d034030014030070010300b403060328001c0401d4100b0042d01e8600810700900c018007810001e08200c441031005030038502c1e8000750382c10034800400d030b04503417038458501600801043c00070f4001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 198648651 1250 198647401 198647443
    0xc0b07020d0203031504090c06030204030215031608092109040e0c0915010909050a0203040204060503060f06060d110408061501091206090f020d0c090b0f06040311190602 75
    0x60001582014030601c9401543c295607400442d00480c03071001c1ca1154000ba00d81c5004800a000d0710034500c003400761a140140c8540c11030040c032000d840c0b10309084425142c10010b01c02e03a8001868003004d00000303490044a01d5484040141c14000006107074844090f9444d5401d0040454602400490b03905481c204039119020002c55640c07140c049c1016001001000422121890352440e401ca46606040c1468429604d01000003160b10403503042d001141d021090004501c1c190050500402e400c40c000d094600b04030180390004d01002d80100e200f503900042c0c1a00341621070301700c2004403484140d410344131582e0b425801e44481c0100c0300b4081404101419007155801002d60b0b80a941410030001803400c1541c0c5d0b41001080c4c40c4105450008000c0c07651801603454110006005202e504054502450004804107591101e503545104080ea800d000b600c0c2d0f201c410607201180d401451801400682d2804500700a8100501002c600d09030701000c0f580c0e640000c1d415242a500e48003c0322 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 198649901 1250 198648651 198648661
    0x206090c03010c080f09070e07030c0e0a06050306090402272703030406020a1202070809090f15090c04091409150f0705130801020d0e01050a0204030c05121c0c0b 71
    0x700b22050303d82d4940c082144000807030700703040c0701086141d0700c1294482240c0209898002c040ba40602c112051400070741c44800c0c041d41c00ba8440c881c80703011441900c8900c59941001005041d50100506050082d191a00010300759502c8441405c16607075154902c1c00448c444540c600da07404411510342c003c88040c101e03880852407071032140a000551000140d42161610740d150f00180d0300c07003004001000002c1c8007035a881c800398070050070be031f9200e480707840d903610342a40c03c1c000444402862018060040001c0000284110400f026112030894080c2041d644124414015014940081c02094034204020007062074249040d4011104e500860300b2603400d0366100044803c0c00ca5004038080ca0040100320524020405410006000004815045d0f1600b28140c22a007041c952103c07606d440d00b0344062440003e100e81c41d0020366051056150508540310000c0e000e83d10f100d1180071300820b011801c0400c00600c01c2482c15051000004e0300800900f000800702684540151122241040450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 198651151 1250 198649901 198649903
    0x20a020a05030c03030f0307030e0106181a03190f12030519020c0309060307020c090a060f05030a020a03080f16050703021002060403090627080102040801062709060b100206090c03 79
    0xc100f00b006004503e004003881c1d080c81190005408601070649810f0301c014482000c0c01190b004d489160703500354800d45040e03e04815100201100440c00001c0301522240e40c5000c103c2020024004807800c151820301d00d003401070325194401c040d00c0106610803855000d40d142c2c20644c098001a08030310748252025401604902c103403011f2804a80c01041416032500b44003020b1507106046005803001815480f010844180382143c0c141d00c210b59a1130107000c02c2d49030003060000f07400250001c2086c8401c590100e4007001c0c3c140005840c0010200b2021101d0380342c00112120403814208045520085180456a030640b90100f01e1050943e088586241d6200081d07252160b0f030141c0d549885546408025510848030689407040e10520703d0803064207109070104000140701c0c0400041e5264601030035182161081d400041003841e80c141c280609480241d4100c03101c0780e4042002442c9111441d00d14020050b5104003600312220f001c20741c9100303401003010340c811403100050380c1ca811901c000701 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 198652401 1250 198651151 198651163
    0xe0f0d020606010c0606090e06090f010b0f0402030a0b100c02010306050108040b130302010b0414180a0302030d0e0309130c030b0405090a1103030c01023004231c020a020a0503 77
    0x90401030784414000780d1a9072140c1450307909140200d8000819070b85441ca498142c40349a0700c050004c0c3d0001c824004a614204400d2034216824070007000f224003c40700040c840052002d46904ca07035004000319818403015405001c1041005013107080903244444007401c10031620300261b01292800200140b0344d40510582441a58840c10744882580c40248242a580e882e11080d0115962610300c5245a180c51290341c148003c0c80000d04014a4209001d01d40941c44240526094000345107950010b41c00006498454007030340800b292500d28201c000d440e50080021442e40301c0a090450030422490340e0103900030700301995042c4040c80c800c2040c8400e0301c10603101403039241e028103260800b0a40c0b4458a0000d42801029070740380c00f502c110039500ba80c1113030008035400d8000e010000900c43c8080c100d07106240000c81100590302c0e0a407101e90001030040040e04a03401600c07003000801901b4403041101d00413450004080c94a1600300079a59103204c10300324045d403018040800c01e4500081d00b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 198653651 1250 198652401 198652423
    0x30d020708150c07060f11210109020a0503040209070e10050a0206060427051015050109090e060708060d05010f021804060e1308040905090a0b0a02030f070e12030408010e0f 76
    0xf9245405070359a0f0303100090511222440c070145e074480a6803910040200245070b00250031030b504402343c2d60048640000003040e132000c402544100061060756030040282c03940b10b40c0469458420f962503610075111003103a42d20580e8044c0d640b01c0c140d1074190b007080207804401c80617421104159980c44c2844100e032035008030085103034000d1028511000b10070007002c0c00148078070140c0d1884183e880d0f510702039500c511080c00d02d44103841030522040d40d118172035a008140e00c5205000c01c0c2101142c01d504c80d1000b4021034104190f01d000104283c4621000208190b1b211008205442c80130f1a42c1000b134200030100018500384a503502203902d402d019032016240c0d082154000394072003d00001c40f0340c2c5002d40072a44036609010010301402c0301d1107480e1249240f00040c180030102860204150b0800601009003a841403061110003100c2e4080103502a07001c0c1411481440b03032200140545281c00206807661000003000b0071100300640041e003881403008111000b40c08441c0302281c44038000c0301 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 198654901 1250 198653651 198653671
    0x30108060403120911090c0409020705030a020f060103111504150903060b0f0310050a0603021206010612140601031a06130f0e04080d02090f0406120c14030705010e040b030d02070815 80
    0xa4480d440c1b40c400031080d0030030f9082003202d10303069540903403905903000000151115000860040300c0c6640500c0315248400008015083c0e80d03045955412600010085190040400700c40c15891018614110380c040e03d800c0c0c03641c13082c00d82040801000618a80001c44500b41420940c03901030a05c007c441f01854002800703410b0000701d03038814400400c001809104040d4079620b0000c0944c40c1d4460a28110200c000540420760421758080c0454104c0003024a003a450440f0007290441d84078415a000380091030040b03506021100103200303040b1840e00c025440880011084840c240d0001c07100103c4820b030b200317418070540e80d44800d0014241154054007200b410000f0340402000b070790083c0091980203000300c502c200e8990204048407100e030030071189010445410010300c03084180d11401011420a010301643c01080440c6d19000ca91103998148001303000c940c85903640e203070000e40d0603602c080c0c200e62a5500f10300c0e00070f590b060706202c0c2c10b000c1d00501d0700c2ca582b401c0441c2c8015201d414184 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 198656151 1250 198654901 198654923
    0x4260d0521041b060f080903040302060412061515140c03041e03051b120f0d2604030c12020106080c060c031b0106050109050a05031e03040305030301080604031209 72
    0x465001c4154030040040b50f010703066921102c694142c100204020704000d03980e0b080398012035003003e000c00c00301410303040c10343d403040c0030800c01660345100300d409451141c0d04004815071907140c0030f4040c0c12901c04288110508810204580b01c034450030445149195503040582188801030072900d10443c450001c0c10380041000384200c6640103200340700c45000728208545280d481d02c0d000c0c240b28010544420128041c600440341d441c045a00c414050010720141175102c01c032107281680c4040b01580302062101c000001d800444000300c00342040300e29402030f914035203068940102032100401b4100c0390102c0d03010340e500c0c401d40b05204030b6003030321590402060785e200504208000c6400003045546e0500c03003040100c0450000100f880d00c5180038100100c0d0507402d010025045090940010340a14442d860400180c0e400084e5141e00da00085001130385060882d54403411032059070400740240c03000200010f0140300015542e44118002c2d40c40707810001c4104019400c1d5900e580d03001e0720040c1c1d41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 198657401 1250 198656151 198656197
    0x4060207050307050a0c0614131a0d1508070b04180203040f050a05010e0c03010c02060a0905070e040b010521060601080a06090603030c020a090b01020303130804260d05 74
    0x5600400c2614000c008403402e04099a451510f00041e40f4411650000f44520800c491a00855034078410707400d84200030304015480e408803d4884441c03042d9050301e40c45603e080070105000e0121054a48141c106200b40e40407442e03207136140c0101d8400c0d0f5101d44207051002401041c040c0903a070a03206503804194070540c0c81d624680194201820a0b194211900402e02c0092010000c4604030792044002203507081041503828240240110740900903410a0780c801c05440d03002c1000c80d4008000320000500b04440c2c1007e518002c040e420041041143c3c2c010712040c0080c04103182c6c121a01101c0a404100b010a448000c00d4003404402c20282d0101010032103d41c024005181d101081070300c0050200e55420104c82500d0b0746074030550100b5052800f880c1941000c0d0361102c00f80c002802c0600c003841503400001d40d28840140181c1010101c05284801c02c04110100c1d0010423000070f20781c00b40e00c21b0241040308500107140c100ca241c0b0501e42000081401442560020001c0201c150840400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 198658651 1250 198657401 198657413
    0x120a020301060c08071514040c0b0c100e190308090606011e030f0b0603010b0a03050f07080c0c0a0b0a051e091b0f100c02011209080412050f0a150b09010e04 69
    0x2203a0800c842110b1031035810401d005047c46420140030780c3d00002880f81c04c25052a4211701040d40094140c81e01c10070160740034250000f0703080e180403c800800101648001011401c02c954814544601d0040f040420103044d8410075260151085005661441d207411005540c440000564440c901580155003100795000f503020703d20700e040314000800d5600c00000043d4039503000741c0241c8803010b004034041e151264144035003030344120000380740310541c100b0700b101801c1c001c002494001070172400600c580e86100180030048505902201c1d0729a541840107140d0040c1201b241c540d0f80c0c0b10b110303454080003034031464591401b4207a010b010701a8080c04080e00300f50003080b440c825400286103840ca415a85480180d0350a41806a5941c1c1100c10107100040441aa13034000188142c10041c2c02d8021600e0a4225011180012880b0a000c1c42ea89002410303d094021000c9150013231007549000e00c800780840303c08200c0c00d07041c200300c4014a5000c0000008080c090302d00d000742d00000046c00541 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 198659901 1250 198658651 198658657
    0x6040b0106030b01050c070308040f0b13090b0d06060f1d1005011d060d0b0414090c10030b1210200d0c0201020405061b160b09010c17070503120a020301060c08 70
    0xc2c043c0f40c00d071b103400c1c0200c5000349400220b03842201c0301140024104001c8044250750400b40111400881c500940582002024405406281c50789580d17a501d201c5a44d40d0030b41c1c0403c41d2513001300d0a204642c0c0e9580c9a807003a240070b2080c8841c100023558032001d001848045c46120300c0c0c4000c1d005403943e0509004503450045120f00002848c0114a186c0c0c0d00c2c2e6418000c0d20703c103201d502c0e021401c5040802400181e4081c0424200c181030180140320783e180c004102a810b00e02e041d41d04100e9598012003c40140c0040036400d908100c00041c6881045004500f045146801000902c030f4076042d00800c0c41101d048450504080b2810300c6551048011500b11444010300c81c400541004c4c1c03154009010755002403641c00e07881c0240ca00c00350110006001203e0a080c03a003005000452622501072030364450141041d0403c10005200c01c201f0a00c040052903265400b0680c81d200e0802e49080390366580800303031803000c0c0040039000440040395402100d042c1c1c0c005a40b80e80e883d586550300e03001590 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 198661151 1250 198659901 198659921
    0x1020a0b18011a040b0109060c0b040f0b010611060f070906052206080406060509040c0b0304240e160b0909100b2b111c021e0a020d0206040b010603 65
    0x505258803642590800340640d015043c0108100f44070b20420804200407a80c03912101814045902800c01119400c800c20300c40d43ca4000302c0c0c1901da40d03194a03101c0100d0100e0500140384034011000070446071307485a090450941028100c0360f0545800c00d088940c15022120034000590800c4107004841c8940003802c070340003504102107820b44491310b80b00e003c1991a0402000550800104070900000c1e0240300c4c000c1c4401c0e00c03088440d0501e031301c5241c0140d5481c00303952001c00700040842c0400c90f512403441e103103400c2440e0311440c4034007008041c0054418a0511111407080102001c80c010031166440c0440301c2e0015903914015043d414003080000c001c00600d01c9540810f0005140b102c440300406400d00090111104a060b42c0b014142c1d07030a20040544000340303040c00d04907403507000380f080b2000c1d20f440301c18a81c043c3c800221584080c0c42200140b06034070303107800134526030581c0100140c2801c0c035044c0c080c0d07502c00c03d281c001240d9030b0804650140c07840b10840c00421107907020b540900c51b00703 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 198662401 1250 198661151 198661171
    0x15110307080409090b1b0306010f0c05010609020310080606030a020f030708060408070c0602150103080c0c0310060906060807050d020a0c0b130b01050102010b06071b031b08011a01020a0b 82
    0x9403161035803000d9070040c0d84182c0105807070b41c2184081000e4541c0040d070003810200d00050002014072040786600006100f181481702010403a000b0501421041301c005610500a101c9103844085203c06500103880342e9581c20708840700401d03036000c085542c92040d440640100400541d5400b000324000c2c00043c010b425002d03400303020480140c1401618032443c01200a1a40d4102d07a20f04910112003a0344900c085401140d440f0a00603018818203044075040740309283c0724003800c4540da04100c030500f50580d03d4440d43d2415140070106401ca6000c0316580302c0c0030030000d6a01c05056070b4591040f0b03200c0300000d00030449122003101a5001e0f064482c418648040130034155926001051016543c050284070304900010401c00007a406a015050030310003480001c40107000b0074454024401d004001100c00e018412400c65490804001950019020040380c41e90509041a002c01409000d00030b500b801c005061000c10340c543c140c1040c1041c0d0003008494902e8940c51800040980680e40e2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 198663651 1250 198662401 198662407
    0xa021206060d1401081f050103020d020d081c05010317030c0403060f0b1503060918120c101e0b0319060510051002010614030f070e070306050301060e0108010510151103 74
    0x1210030a00b0282d010380517020082c040c0c0410078a40c65455203080b014101e1035401c0800500041c1c0b5035881c0f501c402c41d41507032414014415840d00120724000d440f07401c031969007108001003c0000340e800042c1202c0c0100e88903000b1300c400b0038940c403503403000311030504800204210030000901c290b402011242c80c5e03d500010f10060170360000e080d401c06212446100c1d00d010043c80110300c1c01401c020707007010402a95000c0d0440c904529500c80c03148890702c0910720300110301591703460f030705000122031103144142c100a0092266230000d000b0300d045040301c90580ca0450f1101d007908000640f9500604028807070080041da0356510f401810340103080c1b0544070204200003c085c1c407105003003810b504843d000821024200f200c40710a40c90520f0402e84664080e00707141e9107070200032070b010095401d41d408a03e080d9684500940152050364000758145d03281070b00008290389c000440e941a00c402e00002d108545a14001c455400f0242c010441008035100000305120301420500c0b200300304c110142d0f03007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 198664901 1250 198663651 198663671
    0x3130305070b0406090b0906011811090306070f170601080105040b0d050106091e0614060903070b041d0106020f071518030b0402030d02031305450a021206060d 70
    0x128881503030100e6815407962000b17020080d6184403d60300103001c00c001c00156141c101c004601961014691b642645e072500d4991101c002c003c1141c1c2168400340883c0c03414108010300902440d9032502080000e4651403141c2c2d0340300700c0c028070980162816550b104842e400d00302048000c0148400c2103920000da620f6000010b0000e00071040241200880010a480442d84040e1030104681507940481d1402d5400c2c8041d07103c4224035400d088058511a4071000e090002c039240c9486034011404400700454001140d03010740c0304a406540805075801281d0740c1e20b030b80a0340d94054529101c00a034224640600403140c4032001e9a6249a07c0e1800205004401c50240c042c01c61507003040c0e400b0400c0401b0030096017010800b02600f51304600c0118a48203448c3d102c4002c2c031809018a41c41041c03204a9a49500c0c541003546002103480040500c501160450702100f0121101d840034005c411180040d45042203072081c2e8100b041601148889d035034864040200036840742c2c445c0c800550f03a86100071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 198666151 1250 198664901 198664913
    0x914090601180603051905070f0602060f040c030503031303200a140c040e030c0105070503070909050c120705031e0c07170c030417070f050d0f0204090803130c0b030c0313030507 78
    0x4010445101b01468008242411814103006801c103201010b20307003031f0070450a41d00040c0181c3c880c0587c007070499191910714140540181030f5102400c0c51002005208503200e00910030481c0700d11a40760440d1503402540798420740040f018001c911b0b90031120b03002c00400c00004040700c03114000019190580701440000b01203500f200e03480030081d800400c0d8410020024400c1d01e41048042c00d10070b0940c9401c850081c14101c1a0090002490304d46001c1166103071214140c420804004003284600d00d01010b0082694004807910480022070504d004014089600d8860180c120034a140e441c0540341d0b184c0706409003a40b041041003100c100000040490f01303102038006450401558006100341e80c0844d86004180d400920a60b01184020081c50313403982d0b01c8480317066208580f100208072074000a0010201c0d4880544061000400c0182241580d044452954812162039040c151603500000c3c0d2804100e6906412010070000728052658980341c2c00e440394403919180b0320b00a1190b40320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 198667401 1250 198666151 198666163
    0x503040f0614100603050a14070f03110f070b1003200d1203150611031828170a080405010e03102904020702011409151201091409060118060305 63
    0x900c60b202c0c0700f8103011503a030500400da00070b06010030a0021003a0641001e00b6000301030039040500c640d80303001e0051140250800181121005030150b20b802c0001c030103e50300da1241c40210340501810000981692400c0c0040c02502e4004000545800811408890784000c8030700490f400b40d1851a01d000241c0b80085081e02d12803140e8010034145160124a0300d5010ba582003002408100000111103400000540d045104c202e1180d6007100513800c08280e02e0b43c0c840300382c841450f00300702d100c05e21030b6201c010007401c03130b0601280c2149000540152544580010200505006042004010641c42110f21403c1404020181d43d01c00c0302041251040310301d840c445c04a291960f081800388481d040c030085610000541d402d520300440fa500007401d01160801d03a039141ca6012418811648969021001801c1c84002940c0c2d40c1031000e5016501281c04d105038143e90341005d07650745201c0642052503004034018001070400d80d00707002a0089d0b81c0c402c0704504156030354464000020805c10005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 198668651 1250 198667401 198667411
    0x607110c030a050c10020d0c120509130c180f0b0304050304051215010b040e190f0c020f0106050406030f0305070302030702040606030c090602060c270904030504060e100503040f0614 80
    0x4104010013401808203003000000a00159042100100c0190703801882140d050340c1c1c0441d2464207a41ea1160a44040c021028116000800070380c03c1060040d096100c0c01c403496550300d40c1210007504407501c008040c131301d004694446001500c20400c0100120285801520030010340e804e05890784041a480e141c081640500d66006d0310003215104c028140705400f43c04001001854241800030030210020060040000f41c00f0201c180c503940d85942e440032007060321500080c4180411070000030b40c0c034107103c06482015440c111000656191901c20341c42120342c440310080c2c4000f030070345080e90250004001941036010401180005070b5640c03207071a028001c0d0303440024450580d21402040c01e00743e50440000e550102040c0800d40c0f02d81c00a07101000501c0d11055088610802e0408840e40e0039401360b5000840001440304050b002009401034441903a510043c1c4030342442001058001d0381c05420104204201043c0441c20582c0c404074254052035004c1194a003520741d1240b85002210 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 198669901 1250 198668651 198668653
    0xf0903060f10090615050a11160311091b03070c0606120b06030a081813021918061223040606090c02030408070618090c0905041d0607110c030a05 64
    0x1c2007014000854212102500f0219400c1280c6030a202c1c070440d00b0a01c5055900c18040085140c1040c01d1140240900f10104081074441c102c209408001503901d8034042120742d01003500d2502c0046c10120300341480361080c83d82104a114034a0342e20801030b031002d17103a01b04210b0011744013004207800d8000c20f401041c51000154440031301e42401c280641c800b50115100750400c4090b0800f059a600c1138440000c1030008820a00244a0003c0c004d030180700091000c940c000301d0541d081c14044288040b50300342c61f031104000c1c5c44426138031075842507445c05944041a0550b10020002e1015405549919422103c4240d182d00c0704e1400e90381e0340ca0031a82207a4041d101d03901400384806034001d00394500001e000460410342440202a118038550040c1820441c5052202c5000301502031071000a2424400421050350715a00042491549014031030140d41450981c1410010385810100c1402801010b1704d541d4660040440361100000880d58080c45165841841a035007400710017001e0348214 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 198671151 1250 198669901 198669931
    0x50910050735060f0901140d060e070602010e0a08030f0601050f0c0c101d0d02030109020a0905011d150906010201150906051c050a0b190e0313080f10020f090306 71
    0x3000311102d40c10000c10003070041e41092822041c64980c0c002c07003815100703c501300514040d07000020508a048032403000c3c0c6110708080c81b11207281000b0420f40b040d905030303600910450060040c440e903603500604004084000803c0001c0c41d042d14101c00c140c03c5030051400c03e00c2c060b03802148003403541210182480a401c031a8441301c040c07501c5540c1c108100b0700c6081c0400c09080344840f2807650f5040001185c060008041301404540d03080d84504030320b82d4000c5c4401c0240751203a01050080c5002d0050700381d02c4052010140039107150000b85440765080d1103200c0052012401800310781d4001902d00c80c1550340300ea4004a10310380c10400c40001d4032520702c000444a2034401081501d9542c00c3c0d00b480682d500002ca500858400b040d0700e4116604043c000b000ea440e440354811302815518a07280704075240c420001207681c070100080060002d400100b03910035480e1864aa222160604074450341c0d8410000440051401d402524003082011003a50405c4469004039091240440e00884541564 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 198672401 1250 198671151 198671237
    0x3020603070f02010c18060e0d1407150215070e030a020306010b0c30031906230901080705010e130e07051201050c090d0501021318060503010509100507 67
    0x9200701d0b1940d10b0981b40401425111301c48482080c4101e0142c54104107441b40180d406881d040c40d000381c907582c0004035400d035481c40320086854901c2c9004000b221083e182c0f14494061001403e801c0d259a00c40b42500982c4500101b6184e003001082d440b501401041601405640e081c4207030b500030800c0054803070340e0741d9040060b2818400b022820801d03118080b900618180700071314000010409211015949844551340311400540400108001504200300403950b100303500d4400f00c540400d48005081e6605040400050040c2405000704940c402c4c0c40030401c641c400c561a001e10500601181d51030303056505040c094445140b01c8081580c0000f038200420304105046241480120008108506040800d07170410310800840a11071000ca18404041c0542941252040c0c0036540601501503074605090445501800110351804c0c5003200005a030306060107105d20840040029000c40d0f4a8200d04900814001d4012800c111540510400c61800f40c0000c0c0d42c4084800440141c641c01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 198673651 1250 198672401 198672403
    0x3090f12030601020717030706020310090c02070f141f110304030507060206062b031419091a03040611041d0406051602060403030e0c041401030506060d021f0903020603070f02 77
    0x840c0d111548034084401e1b00d84034910044140c13a0210352181c0c02503030b6900e82c1480c59503029003641040291600c0c1401070303220039030000340b01c0e401c541071801c94645940e07459000030050480c1081d440d411070010f940c601000700404140305100112414040c8044450401182c80c681154008880c00e5014180601005804000d01c80d40300404407088032042e2608290070390950385c8450300700f40d0080940c05034010140187d00060550300c2d00fa034015101e07000460307418801c14180030b081e030100e29441c80100b01241d2501149291045614400c1e10790f8840365110402001c9131080f41c10402010700020950f042d900c1001848410f1003800f95081d41002d0401c081202d1000e014118410aa000e80302d80054021902e01c0d4440e8041c1400600e5018045030942031495518541c0d502a1401c0c0010038005a4034401c1c5050b02c0c05603003180c815503509801d1101ea244801d00280d0f00c0020b07401c081c18030031050f0a004080c0200c51078111109070356640840d03032542003551044041419001d1b90020030354 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 198674901 1250 198673651 198673663
    0x207020307080a12081e07030c080c0a05070f0204110c060412030b0f10110706020106140409020a0302060f04030803180c100f030c02030909070203090102070f0f0b03090f1203060102 80
    0xc40c0e40192030040103540d103244e480514281ea03042071141c41400101c008048040034182d00d000a07503200294541500004c0080008040708004220a0000f09071180b0f00041035401403950390b11414980029a180c0300116083c402081b43d1050310368402226003034101001e407035050700c2c060003000d5a080c0340c42c01c610303064000040300040524104510441c1c0d0307151101400c0540040d21803824260400f0421210f2180c000143d5000f442410000103017241d0562056081314030035900c1c2040100400d041000340da5135144003070b51016111100b8405841c00c0c100400039200703402e038035a2a1903940d66a003140d60f042203803c1003203003a5100c820202c0c13800a10441e00314840840e69960f9401e03049802031f0005000320b40300003c241d0344a40341e407a4507008000312400084020040c1100e40b81c03001000307640340d110348805c60042c01601030000311000020605000c2c1d900010724408201e041c06115a81a00001e20380c3c06140704124501402c20002e2107206451607841030129540d01d895000646841 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 198676151 1250 198674901 198674909
    0x30718120f020a0605210702010906060620070e011a0c0a03020c0109080102070314030903070501050414161202011d060a090e01080a0f080307030b131509021c090507090f0207020307 80
    0x2c0b208000b42030100032295010341b1800c0400b410079030305484101c000ca0040c6440724006221a103403000104505403c01c1444492031496412905920050045151200d02900c56146401804c0b0014491800c0c1d4059407407814000101e181d0030000482550ba00d480145181034015070400b0401d0b01495920020280c05000710000a42c0f61601682c1c009118014055900c10410380220100744038180c14070864080340d420038028001c5040c03030b042024010a44501d4010300e40300f000072044014102201d403800b00c07401c411586c0f064202030740056808802444807030920802c08054102c0c25a0b0344000f81c40c5c095503030f64440c1c010030704020b001100840f068000161075804844c0d8600003500050280542903489aa00e545944407140194041e18107911410307804003901e6a02121044580d10862022205140201180f5525a035600480c81594003003070881d86840c811040490035174100310307403481c0314004031601c2c560344405600031620b0f03000c04a230050f900054601c0940c941045080050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 198677401 1250 198676151 198676157
    0xf0304030e0a0f03030e090403030b0d060b090702071208090103020d020409050402011805030709020c0c0a030305070b0604050103030c021018080705040b040b1c1118010303080702070605030718120f020a06 90
    0x1241145c030007402c81d0407009002c6100740940070009003014800d0f008212070807800303007441e0f0300c41c0540e18051000c0c0c034004480a000303208100008000900c0020100c0445800c2c0d014036400440c0b035290402c1950020403113a051607004c01c010032001140384001c10041c032080c10005001e0400740700041004500960185e852220f03507005210507540855000221002003c0041e5160b07050450300d0309004904c42020f6000906590000070301d0342040080000611950a900e225901d050800007110401c5c0000350008403000091001420000c4030743c80c042100e828a17101e44079810380b003a0002d284942240190b504044020042ca00341030181e10060a001c6030300340541c8240e10040703070815a120070400801c2030048000020f00030220301240f0258400b4240e2a50f2060b4105135a0384054284003c600041c03407280058502c903c04502c04040da029a80c4007031940e140c00ca000c0341d9000302c0c1040040001d051ba00000380f010314074039101001510540003c503641c081401005030071243e84e0320078014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 198678651 1250 198677401 198677429
    0x10f0513140705070201020c330a020c0f030f0109031112090d020d0c09060308071e12081b04030c082e020d0902090907030209060f010e0f03030f0304030e0a 69
    0x685503111640c190300c5501443d0903034882d1040c0c00100d1a0a40300c128160300302800c011310003802d503010b5208901e100304401407204080c00c3c81c482d8640620400441000680101c1c8490304a89404042006548001802c0381c0d05500072422160854089c494100d0104a40018000c100442808080e840f44504a42c02d0304054100c0301103021920300d81002403189000d00301d401c040150500c9104050841d90004124242c0c80307141c035141d170707a01150090300d140d480c112201c130f03961034000761002185521485400300c803a54883e0994006802800300b50652504032a800e0418131030320043c00040d40100e040320015842d10036502c0c10801c0920040640d2403400340d0101d010510344c200110000e03a21900160340f500b9803c4460700030403a12070001e5101c001e0302c041c4800c10b0b400103024000d4a00850301c4004d2078681d0070070411881001079040d030102e00c00d00800800d506e8098290b008062024061b20301e0130300d1044800c000355008444c1100401e60b07401c4400c8540c2003000c4030901038076800e80b900d84 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 198679901 1250 198678651 198678671
    0x4060e071e0c201203030a020406021509100b04022b0506010e0306040b071e0f031410050402030a0207080f0c010b151207020c2d090f06091b03010f0513 67
    0x411140b030740d162000b044001200542d0030303111044c000782d4036059002501d07200d040240d000300183d4001e100315030042c82480d10141c4002c0c1c852001a000e074070700e080100b5002105a103004045d126203950103a006d5400e05c043d0f801e07500400c01d1840900e86031821030103074466120b0150101d810103040141080000760940016440020721941c119803c840c0452090b0384016040b14a0306100320032156200f00380602e50b44941d00202d0f500c420034000d840501c001c505e0341a0b0361042140c22616405004042003081003141080d5004580210000034094038180c40341d00c58031126401170326800761142e000204264038600a02ca030100f040303811030f02816206440f10f41075003a800b480b011240d00131240e802181c1c1350340c004c00c4210141e55014004000c50150317a610500001221400c101d550361070609012528601059558071840340500920151b07180c03d010300c5a006001405204c15946401641d01e00721010005180200f2a12100c0f80072141004103101c003039030100340b11407403841c10000644 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 198681151 1250 198679901 198679913
    0x313180b101202041d0702102a020703020603010e091603110609041806020310060201020c1009080f0304050d09060201050906040201080702070b0d1a030d0509010c0204060e071e0c 79
    0x164501c00140780882219801c500464024421680541415143c00890301c590440648290780700311001d80903503c59010440c103074400d0314241075007a60b004201e16005844000010000b6211995600c1155240380d113960205000c1d620a07080003400c10144000c03c05401c000304541071513018162002c00c10189140e03940da4801001d441140c0c4103980c00301d075405054440380d2110402c500074841d501c9905034541030560082d44291100c24406421002c041091070050007104c080070180f00c018924070307800543c3c3c10700400b042c0400300c0e29802c3c100448003022200002450143d40140040c1100302a8200007502c03002069020009590510303003000443d0b0004582c55070322607028200340301141e803440800c07801c12041c2d40001e510300c000802d011000428950002402e43c5004c01c0d0905620104000c15070790701403440c41c801c0080c20800801c0c440d548110302e20260f140c80504045003031901d600e4402d0640e4011605040080c0181d91051000f00299425480520385400c0188001465072290 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 198682401 1250 198681151 198681169
    0x60b03150a0f09050c0c06150f100e090702010e2b1d150c1603051e0601270e010207060b0402090a06030b0d05060f070216061b050a050313180b 63
    0xd44007642da54000501908211401c507071942102c08155031f031a26209208103408400914403d0081000c82070584103030a0a200c48589040d445d103488030380551a108100c03011740010101d070f045548500d0590035502003000701d06600707146448a061030a40d1813104901074174130302c00080308018100c25521980c500c0070703084008120041da020b0800c0032040780e050b0000c3c841d4a491520074400c140b00b0b00c111031007068451064038410000e48041c942510704002c100c0c5c0844021074801e810640041000741c411601114148221140d801012840c0304100c004845c03080708003041c503940000e0315100300722040c03040d0904000115821800c1030544004151801c00b14011441072503a01c2146518541d0b494240b9444598000304680c09441e080d80710800300791040c2c80d4580540300381b4049150001e05105000309440d140c0e40c030500107170020700d965036009511400030b032568083d54a8240100d60705100070060162099030349541c00e4581261480e512011221040510780780800300c6540b86c3c0d541401c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 198683651 1250 198682401 198682409
    0x607050f07170d09060f090305090d0f020324100f0504020c01020912030a020f03030c07030c030e031c0207210305031021060507051303031110060b03150a0f 69
    0x551501c8203440d1821029a40c03900e503940d4008503011695038010500b540001e1400e0f0321842003801900082d50000c410b82c1e42e407410040c0400c50030301c1b0740d0707800b0f0801c50390280126005030081802c000654011030b0034050a11301c4038000e0210b1094006003040c1100849030810b50355002140380c40e241c11a11003800c0280e002c2e50781b080c2c2e000108107280c600c01350140c540d418002402d0710642c0009243d00d03a2388c0e03407002010001600964841c428480b20100c01d59204410410155160803a640e8044035107000e1034200303d0a00020890840650b1410000e0320421015492210000d000310040a403510345030760f00c1000bc4d1140500000c000c801c0f41301082c3c2d60242d06040c000d480b034a990480d0406140350341c208030403211921040c114110784c64280b10304000d008078002c015035116000119114400c040740b000f00c1004003a000c000084c4500601ca0380494144280d07000141c02103d0301c016220302e80d200d045807070004401e04c410702400c2c0301183c4060004030f0381c10b07240750b01e04031224541c0525845 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 198684901 1250 198683651 198683677
    0xa081603031110020d09260414040f0c0215011703041809050d0206040204050c0304210311072a0e01150c1403070308010b03070e040509010906050f18060705 69
    0x40b425082d09030420191020840e202019911480b4000345100107004000e4291071440b40090720580101c240070b1201003148031991810700d4181080b100140d4140c40c41c06140d0403503074800401e04a4003543c401c0c4004021258054505a1028407141c0c0382030106800000301c0495000a66003800e80001c2140c007140c5108801c0c0708032100302c091040060141d0307c1c000d00030740912205e505440c1d0740843c507a032007513108a4040001e0b480b8503603203002c01d0000301c40003480340740d040821400b004098030107901d000d205403401040d05c010184d03a450858200e01802c4a00c07602010001380784040c0303825101c080ca100b80a11055140c940400b202c1443e0f4184074a40e1800320b000341441c05188a40403502c1219042001c0554040da0341308056503d038480e00060300054035610000c2103502500048078001e00c0031b50380d0000850003080801000b424060300c0d144440d9643d547c00c8001984501405100343e0a29036011070700d10b1716081c90000f60707440c48507040d4260030100402c9072954105c0c050721a407000c030003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 198686151 1250 198684901 198684917
    0x409020301060512030a03111804020c0c061303021201020a09050904170f22080303011413050c030103020316030f0f1b0f050a05030a02090606030606071505060a08160303 75
    0x100120340105126001a0340004001ca1090b100701d04c004000c0c86074034a1590104400c0700d40c820600c00700c0c0240681d20f0304656095510042d03500e00b07500078014810b814130540e40d0040004c400a00281e10081d1601c510022003a020400c0d0b2405d0811001800040350080d441c104041000a00e04003840c06014410501130004c1024007241c03402c1c003165a500c0200e103e90303920008480c1c2149030400042c011910100d020b800d520185030070000b00850b1920300c011070640e400d28a140501e804207221240c0c00c0040c0c6c85040b14138851078000c2c10301034007004040310340e00c1d41540141030074142c2e0884041c1201e55401c8040002840c81141218030613009081803003500281d14083d000c51060358501d008017801420003150f44010480305000315407088601000260391807040c0358131040c030b03084060740c0001900d0000b280740c100b07000116449400204880d240c0206551000340c0402c0350046400c19079500c1e010496142807581602c0098000d0500818a5480c001500c203502c03101703408002e007002501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 198687401 1250 198686151 198686153
    0x10204050603040f23010b0418030210020a020c03031c14010e270d020c1914090c04030c09090308010b040e040f050106050a170714010f03020c070b040e0a0b0102010b010e0409 77
    0x90b00061600300c904500c8000c003050345c0000c803801f0b08a20003160344031300d242041c680b01c500c0c240c0400c82c070b03a90b174507802525240c2424001308000750014005003040d4051400440e40b250380c1400105003091442c010705503500c1c0380006420031155615004500104500018090b002496000550090b2903904418034107452985595400141c0f40100c5920f20401219012198012030100200c07d01a10350200e8025200c4100c141d4150710311442d0210910030800c1c0000c1c1c14170768201c035404a148065940f03443d50b079a490f0000c20b06164003654180ba0790304620000c041c2d11620301401485d401000608180c100002000c0c41040a44010705010400c180c48080002c207400880042400070841da400e55a109a20705c01c0e80700c420105855800f0702c41d408115000c60700b07901840c030401030b564556a9a12888158001c3d40020715a408d0707481601d5000484414100042002e03100302d858110880c00d214a294098802501c2501e0659050118060090360302940490851100b00d6010540d5181 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 198688651 1250 198687401 198687413
    0xd0503190212120f0601080c090409081608040e10030b07030209040e011a0103052409071206090219030504031b020a0807170f06040803190b030105070e010908010204050603040f 78
    0x420000002c0d036410201c0c80620080031403209500c81c008910404110766145001142c1c02038040741c07445440740c028090044242420361007960002e201d01c80c92460084c0328001003c000440c150304a8500d000080c084c0700911071410a076801800041a0306207040c2159034109259038002c2c512020558045291019991590458120400c1101c005c11003091082014810a4101d640050109040c10003103600c1180c0c100000d0b0072a0030020071002503e424904001c0007902c060590020040786500d00f035203a040c00d01c581c000500b80c000b001a550651100001c58007070030021101c040c54540b108110210f42c0101941512622686404103a1034041c800112140002d4000311514810040003283c060024001107000b1101003085035484070318040301507541c110460b0300070100705041c00400c10041d000140301155005400011842001c00030111303084a0013101c44000040c00004c952200d560015007a034050283c4000030b40c50b05040101281c0a03100240c001044003e81300c100100b4000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 198689901 1250 198688651 198688663
    0xd050306030109021509040b0108160c020111010e0c09010608040b07030c03021e0703080c0708070f1e1b060f080c0927040b0a0c0c03031505101206050d05031902 71
    0x150041026003031750042924004030740c001c406900d01440c03810280250135030050040911800d09034506000c0070414007000c032030111100d01e0490510141c10710900c1124001c0c003c0d1200302c04c00030020300030001600100700300420180d0101060000000602011952502115601902d00c1c01d0200d07140240c90001c400901c03804224104015925140c3e0580b020351200500f0050f01946e13884584d52030b088189581807290100080050400700300c00000a081d2240408185028040b08c0080340007560b089045090200412a01c0d4101c064103d85d4608002011704003a003030525102c19001005000500b920300058007030034481c080420f441e0401d60b1621110f901c10681000000780d001d0031400c80301e01c43e10007580c0840d00e4540020019149120502c55501321140c00d594a28103114a40c4040d030040c40c4103806c0716498004c8180100c2c258944036044803551000d07a0303520394082e07410584801250a9500301a1150000181e41008284000300380c540000407203000c64262102c18070f0a902d403407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 198691151 1250 198689901 198689903
    0xf010e0f01200f070e0a0b0607031206090608010c08090c1509060f1204030e01030908030114030f0105090a0c08070305070506030903040801051320060315010e090a0905120306030d050306030109 85
    0x3103d09070401c1c0d036150001c61078608442003024044207949805500f40199400c1e080c0c000e4012000f40840d2021070301c0703031070040c0800c480c1850000b0101d0319444123030300342e502070b4102c006140c1d100c5d440303100c249910004180d0b100300b228001d04204080751000820704082c21118004207440824003580594800080b101941e4107645850b545400b040000c03060108102ca06402045000002d00181c1d40a8050240503035071106e80e043c61a820300f4100d041080301ca4180f5509440343c00c5032000020700920807a802901d40c98000c0c030000f2070a00d81a100c0c00140d40105a45400551040000800c00200c03a010390b0342c111940d03034880d0303103000ca41e500c0c41c051540501ea4560821040c80021131581700341244540c012425001d012002603500542c0d80346120006412810401c00901c0c440c40c0402c426034890014548020b24a001800107480c646083c0e407021216030381d8100346c1c005c002c42013102011340d01c00c00228504500d40b01e000680c44400d10540760050201c0080000c045d543c0c2980130354022 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 198692401 1250 198691151 198691153
    0x6030106052101030b040b01090c08010612020d14150a05181819020901060509090c0901030212010b1306020d020303070c0606151d01030603150f1d0109020f010e0f0120 74
    0x2d0f41c1d5908040b030f0100300030b56064441000000012030000520b005240f01405192100e040f241d28240c1c04442c0b9240c10011303004540d81c00e000c0d403a00c628080c01801c4641d00c0c800341c5d0840d1402c00041e0f00242040e0441c0ca0340c42056411002c1000b600c4644100d40303540005003082000c0c2e910b1110052662650058000300da000e40d46030481090641c030b4501c600303607000303542e0080c0581e2103600c00d84061040400c0c1c154042c11010000c1c0669014900802c04000189005130405520524480c00300070281c102c01501e0303401140c51201286130174140c0c0001e010301c1c40140540020200041e4480c4000b404190400c000111942d017401500e80003035009084021504d010020782040040c0b5900c440b41d500f910100300700070121030a41c4079000d6101925001070f80000700c55403001c0079000800c8002d05400c68036460303070b00e007000c0a4001c00d25151024070400000c1780b00d070414810000705110b0842c0301c505214010429041a484004038006021403c0c00c000f160812940d072041c50380340100455046c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 198693651 1250 198692401 198692467
    0x103090210020105010321021b042414030d050717090d060c020c1e01030207050c04090c030302060604050705040311010c0204150305060c04240504050d0309031a060603010605 77
    0x71507505601c400c1c101c9018a840c0300b02d1350b41c054130307110445d042140914016030060840100542a0401d01c1060700d41c0104000741400181c00b40034141108c0050a0110040e0b0403030411000b0300b201c0719003019404c1100640610445080003030b045000c1d0311400f42c075611050350041e9a60f000c000444d441d02400901c1c4541e07038102d500d4183c2c05440c00b21400e0f001800341c01d080060500302000c8092800c040088031104503483c00004500035000020150785500c61802c2c0310a003074441e4416019040e02910310152034508506000e480d11301c0250260380154078150401c40d00c9507003c0287c3d41584d50002801071088071060040f0303000c1a07006006580107141c0901446d0a200c05021881140e11810554800c0e41d00d500d11190180561b104000100854a00c03017601d0b0078205186814070f00c000c0c18101d083c6030321f820100740e54040e0b0394011400724401400510a0180140303c02103c1022414542e10f28509207021070302e1404180703e0501030210110b80700800d854501c0c41d0490300444d00d0000c0d20 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 198694901 1250 198693651 198693679
    0xc03040b03151c14070305120a02210405030f1b0d02040e15060a0b16030e120706020601031401051303030b010c060216030305071e080402060403060509100b011110050601030902 78
    0x42801c244540403104025600c020540113040440c2600480c3e0700800582403031060600d07002419805619010f0441c010007581c403046000b6041812a00010480302c181c8690a11040c507161600c5004443c0c9107030b1003010881502950800080c2e41c4190940b842e1283d0841480814090000000d0f024400c1c09081d903206d9100202410051058a0846c1c80e10142a42c9000c0e245a0703218906c1080c5030300056046440202e40641d080361135880b0007030302d802258454007070500d06040c2e068000c80b0058010400403c2481503c130441d00a00f002c07107000304507070305000d600080881202c00c0b0040030305450312001945680500303841c04a030364228506654500c060207900c240c12074007501c120040b0f854040401c91462140203500c0228580d110303001c2c0400600d1005039420540140126840402000003000090703d50050038003c0020a000b040203225107030540d02030f12500300b16603041040403200c4417003d00001686401d2000c0070000060280c4460300100c0c05401805000394000883c3c490b00c0c0c0e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 198696151 1250 198694901 198694939
    0x9060412170a05072705060f1c020702190506030615190e0a060810030b040501180602130b161e0c15180b0405060c2b020c0301020c03040b0315 63
    0x688283c65a0f607440c81d080c10081e25150b00e9442c0c0680c400c80c0d240717800300c0c20f101d6410100e00526402104072412400c04007400c00420700c281840c154002d5240d0042807400031400d0801c10104140304000c024003015003030001040141c040188101d00c02c175003030722400c110035107030504440f14291254212260321250000140801c820317444a030380500860000010241e01c0350080500030190039004100303d0346141c03108002058098820b80c0d055580d60034400000d841c010306c901e00c091040301c000d40c643d1b0b0300c2c02c1d100e900076045078031152401500300052250241c1c02d440074408a80c0c000c16020005014103166107006411a1005042249001000c5078aa880180e0074280c3d12190392070003005483e286442c00364850701e1040095030030b01071000f130090b850900054a1005d40b4102110b00014000f05200108031200340c3d13804020610a0f030201d03610b0fa05002042a00c40c0a0b0025443d14041c00002036880c072807031113002c0b0209004400303d580700d05064155200080020040013450300d40743c10304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 198697401 1250 198696151 198696161
    0x30a08060616021c230601090507020712050102090324070c02210106080313171f0209180c090a080606090106030b01050d06060e010e0f090106030216020303040e06030105070809060412170a 83
    0x240d20724411b40d40009211215409410b200740202c0d4003030031030b0707a00c0d2031200710242c02503c1d412900d55400f03001c0c0300300d01e48003003004032415800789100c0001401d440c0824492140080c05850422003003040030340150311200c04400d41208541d40344200608510401c50040100740c000180030300000500c840307517641d0142404142e0355410000d800c0580c042140750340e100942c0300400510700084020141000044c0c0c0544002c11002d040d5440c030000303120352070055200803601c1080c400c00110f03541e20301d4180303a10054050201d40e00100407d0400b0740c0010b425030014841c6004241d1206450390440c8d01c18001ea602c0012150f02c20f024040d2030301805002d002180d0a05030002e00c20300300d00307a071900d450030310144c0145024149820503406e04034114082d511080740407040f18a9001118011b8508000410043c14149460159800c10f6000c050940304090003074003c1041c51000d11801d52030200d621508580d200f840050055400c4800b581c0040d0721189403951440e0160400c8141140c035000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 198698651 1250 198697401 198697463
    0x3040203010b090103110d06020409021b010605060a090512070b07050705090705092d0604090203010f0e09120705100c021605030303160c0609060509030a08060616021c 74
    0x80c042070314000300307110f0805030900c4050128215900740d400d05082040700c0fa08194002d40700949407a86502c0340d14180da1101c8d40d40198a01c1c805594041560203103c1e64010740400c80c0d4591030f009102d10b005282e903c00f40562889440441a003c000141c10080c8900421020704c066484d5000382c180103417240502e1092500806120340011a1581b144080b1448144001c1401000581c2c01c407803019941380031120b003065001e509201c80d005035120b10241008100c0d500700540d586d0304181d924580b1080701c0d804189100741c000e0610070100004641681102c0101d250703251685154203103140b0744a01114411413081ca00350b4180740c429400b2550301400d030220016000c0a60743e0f00241562403108540354000380c50b0302c0030945280d178414040c500e40c01e801100045812092611440225501550302400c0c5030301c0020280000b580006202d0b138407100440b419810440a036031001101d48850750000e201d005290802e5161400c850003200700c19800c10840c001645225a0b031480002c50216 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 198699901 1250 198698651 198698653
    0x15050a0b120f0c07030305070e0312041a0c030a0513050d060b011b0c1413020a0503270c041d150108010b040203040507120510240e0405060f0a0b060301090203040203 73
    0x180b0805041450a015030100b82d003503032400c12251000c030020f02014102c14100b1000e1030904d0800d40d0204041c20b50103808500315075555290400d0400b0f010381ca0f0080b40c8120f034052100f81785404000c0291000002c146c00c0003542d8507000172900c0e08012458100c140c2c40400c0031000d40c28000640c0c0854000d40342130702c07004040203029240c009174114448004001884030755060107400144600b80c0e640880140c48860304280c44540c21090b0381002500070001600807003081704409000100885000c0002421400303c24a09036254a034030a540d00c6030b00a5031901c1800c640142403416100c1502d100c20140c1d00c600b003071900c11100c051400e100b642c04039800e2040b03404a83c5058421a80900c0d40900103080e41403030030b0440401050301c4001030f5650700070090301c0e000925060092042a0211080c00c00481c0c660720021040c0702403d810149580d6000410400051000610550032417620103031180b0540e20109413030042c10445c0d04c2039400c07001c00b1000240540850b00618002d070b100318 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 198701151 1250 198699901 198699937
    0x40504050105030c0d0210090b0d0b0406050126070923010201051f0320062b020f16140d0513150206040f05010207020d0809040e0705100315050a0b 65
    0x408040d51080d4103c08036074882d880600036001840d00b40036480c840d1f40c0300d040841c0c1740e0341d07640c80c0c2a2031500003610f03121100d900e500c10782c0101e1816104000141400342825000e5902c0803400040415003000044178000980d400709180300e00810414008090354242180020241c3c0402d00b0030951400050340950b080c20701141200307900c0c403c0310242c01e10568003020100e2175078680101c2d0440300031a110064000c42542e0a894844100411481941101c43e0032090b050645051f00310043c0850040c3d110b2041c0b00b560006c1c0b00f280f04960b41d811980c40302020303200c61428190000d100c08025441c503071290b01011100c80f60840c000c0d1089444001c80c2d078484580d644c618940700c443c28440280103030011000140000d81809441d00c0c50780c094400181410640ea000c98102444010291a0b002d400701c0c1c040c01c540b03054010300180c13500d0200135001541c5403d01180c40c01444003007490500d515070240310100700880c0035110080c02e000704121242c5a5402601d001c90303208291040e0040c03d91 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 198702401 1250 198701151 198701159
    0x1a041a010b2704090209090d020c040212063d0e030307021f09030605070903020f03010b01082a13060f080c03010302040b0402131517060a090504031e03020405040501 73
    0x789003954860207045142424680e10b042501e0030034442c00c500641c0c4240d40e40400c0026031901c84c0b005100f40c204500526420414010191400c0d0f100b202542c815401001203246034000c6414030303070300551f064440e9103d810804207403000f9100c5c00e0103040840c812181c4004210314924040e01c00c005400e4a0b000c8803620300742c0500d41ca0348940c001c040e42140d24420107071003d20514910006141851038031241294a90b655036050300c2c4d00b070381c1c0d9100046c0307051018400e5142801c88942c1c0f000c4120020071882c00032500180070ba501c024101d000c9600d03810089a0324052469442d12070100401d1003981c1d481070001c0e1000742200600413400014010f498a4681500404a0900494903c0d50791030540e843c56007003001411030002c0703190700f258081c2f00c190344401c0a0508040540016100180991032000000700b11000d030407010041d00852209004032900e0b5481c00100b5102e01140102c2c481d91a401c050b11059a041c0d10b00181e00c1031100b402e22100d83c1a40900150782007100c0c18005a40d035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 198703651 1250 198702401 198702419
    0x81602041a1912081b01020c0a02091f150e1f0f0903080405040f06030f1109130206030a11070c1410030b01120e010f060303080603060a0203070c0b041a041a01 70
    0x35000c0c0c80250910101d0031400704480700068031100d2898079040300007045d07583c403030b07802d9030000d074600507481d40162040011480c18508407580141c0b8540540942001011002130810f100e100f01900ca00c440c070174400c3c0451045181d11542c0340003808801000e62043e900d078184000340012b00000540710000b01801c20302c2548075804a0390001815802c0c1030074042008010096181460b60059841e0340010000741c0166415041300c0c0078444200300340780a80c081c000c140030001c00c3d4a4040c2c0043c403c160041c0c0e07502c01581c1e000014140000361130b4080312201c1001c0d00c909480a404c010584000041c450441c0c0364000e14118190380b0502038101a00e019002c0e5408421028041035800708a5501b552856110251702007001e400800c107186403104007011625544c00580c0042c004800308100ca0404103c030913042020b41c0811495841d05980c01018100c040000400310444240851305003e00180e580700345000c203041e1250a8103052070304082860502e41c4803001084032000005803100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 198704901 1250 198703651 198703699
    0x5040504150905180a03210c1805030f07140406081218030d08040305130b0a02010608070e0c030705130515070b06032d07080616090f050a03081602041a 67
    0x8141001417883d90032641d4107807a100c802c2058008400800120f403882441d440c01440c00c8920f5903101c03100c1c48500b6601c004040009d40e04001e00980c041400d080e13a1000028a2804541c00071902248030103904001901903c5543d11003030040c400c01c031034000940500802010041c041c220180c84004001c418148c40d981c0010403000844c5020f0000341c0800d01407401400c0600b580030902160940b01c10102c01036410001d031000040c1c0d5588414010f0040411881004c0d00c1c0c10000c160f0503150404500d00e00740710040c80c041c20002c002c910168102c5c0c0c00c8116130042d150081050101c60720000f541e00084e0040070040e2180700030706001c1800c5040105036807144090360496210401030040c40382c0c82440402908441d00d10914000080310102800814000d0103600c0209031182d1070442d009156802c107401000400c2e40c0940100040c1d551a10a14203c3c4d60102c4c0782a25003800d00e810743e0800d00c240303002940040c1001c4c11755038002000810449015011100c414004081c070009400e005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 198706151 1250 198704901 198704941
    0x6031e09050d0e041b0f020d02070b090d020a030803010312031406010c1e171e0309061b0c060403080406060f0b09060304021504030b0a0605010c050a021005040504150905 75
    0x24005500c11442c9034840e0354400702070070019001050301c07220001310b50500900d0480c10b200055000c40030560441d814048011402c405100410801e420110303020858450903c1051040307003550000011512860100d000854212032040d44a60796810420b0801115841c071100003803400e4001d100c20003126095900490701a0b4131070901d200030b9964040c000151056282544140801c140000765110803868280004113440c1510b071085429203d0b9010b00311203ca503480d120500400072a000700180782a4000c0bc8000855100c00503181031040750722600300d840c1da0380c6c0a088100410b040e00001d180b400b40d4411182002600e98501401803508010b0190581a9004102c22801482c0500203160024002810005400c46c1c801c200c0005074401d40c021510305a02d00704000d6101c102e4401d4070000c0800303081881c061070442d078034241c8030700740c61900174880e09207210121200f5100e241a00c01030300e400340c0300300094084035182c04241c0c00d052080c1c40c0c9140c205070004603050480700c05c04400d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 198707401 1250 198706151 198706153
    0x50a0810060b1c0518010606120e01091707061b0809070504050c0702010e12071205010506030615060c01061701060302030c10080f0721050105031b01020304170109080406031e0905 79
    0x200701e928244001601c0060034005c2c0f0001040d2a4091141003880303000010701c03e40e1541c4c0000c50440d00c2d040140d400e15200e11040d64076004040b00422686010050401c0704540d54aa40c6c003180c0c9072410013048180c8440020401c0d40e501540141c0d08501214080d400b03540c00c854000d42d0714000c000c1580d40844215008500c14094180113500034070103a824007800800c82005480d5200d0940e103801d4840c0c1c80301540d103803288204020b01034284a0103400c42d2082c6c0140080e450311401c803843c043d5801c012240104000514100700007004c0d800303280907201d54507000c01c40180100c038450190046020031b03032290282200e030a03c1468240301901e074000c00380d1601005643d0700d50303280004400c01001102840303440f15120311815440e00e1800b090749240a0001185d50404060500d00080300740310403911140d80c194400d10f6a0000151390403a01d49070b44503001c03100c06280c0c142c090702074010000c0c1081404100401c945404d90030000110081c0018100c0d404407921032042540c1c4000d5000d07042d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 198708651 1250 198707401 198707437
    0x9060a14010e030f031224010801050d111008071701140103020c07032405091f0c020c03150a11070c0905040206070b2401050f04090504020a050a0810060b 68
    0x3941d401403800c00010b11004068891288042102c01e0443c3d03c000003401c001950141003101c090301d2810794950f0b01c1e041969040e0300000e80000070300f000781d040c003800703204242210315081004504d410208600c40c02400004c61318045c03903005040c445c425908000030500d030403410001d8045049896048590780f1207202e000003940c0300154029482032071042018000c4801c003102048841c040781c0d0f401c40d070010203203022004502803201124009031546038a900130034a8000380013181c6880c0100700b4541a0000345011600702d0603450401c0045006815000300704c03915000000300c1c103220748600350081041c000208a03074002d00b000d12904d00f004104090100d4144440c168950110341d02620103000546814140e850302c848684d4100c410102410200c035843c21903072000b01d4842d0b4006070030f00740541004072106600343d040c0614003038215915034a80c000703000d650741c844084000b00000380c0000360680d2035064480d120703860340c41c1c2280501c2c00c160700002c0c000b91003400c840c881013480c004608 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 198709901 1250 198708651 198708689
    0xa0b070e030c130212010e011a0f0a08060a0503010f050a2307050a2d0e0616060b13020c1014190203151e010201050a0905031e0c100501030209060a 65
    0x201d040b80b1200c402407141c0c00c0c0244150b10005e50800f03406402007144602d03a962400c0304804030300000c0d01941400c00414080340751303001c80d02000d031500c08002c0c0c14a50a103507a141e020505c001e1036944070303645c55800c010b2030341c5080c00d1903403020340141c5a014080c000c00e0100c0c4002000c030040040088010034020000403a0103105401401c002d10312803a2030312403070703181b016104401c040040b4110030f10040609241c14080e04840341004070300c0709490803030612a000c2e221101c2c465105c2c8001c1c20b01901da100149080c3c3c0c8101544518041c5c0540440d11002400b420543c0c40c04607403001c09801d4507080c084407410040c00c880d01c1c03240303440c101d1f1a0700c0300000c1c0202c1000394001600080304140b140e1600030083d13032417600f031070700740131310407920078000c0000a00090030b45034080c00c04140107190070000004547c010049078464102e55458420b11004040181450300c00c03205000d2240c0a026119000f2141c25084181200d000701c50386446031311150f041210007840c0e0b10a50b000c005070ba00d2620 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 198711151 1250 198709901 198709909
    0xe090309061c06050a0b04080f06150105070609051501030b0109060b0a0f031b0f0219050c010c0206070c0b0405090c1303060506030a060203010e06090702030f03010b0d0207080a020a0b070e030c 85
    0x402140c0035000208500d5504e0000c544041000d402000314500041824000000d041000e0344e084940d0310010305441c103007074005e42910741c6c203800c0240c10000c000400409200e990740248000d00d5001040300c442d651243d84040c83e40800307010486031201c2202c000140c450b1580540c40070759202c1b128141c07078a0454501502e080c0038820780b80c030901d81c480d4035104103a8024559050310321090780701c04402600d0302400034200418104e40c04070109640c500640030660000f8480203d40d000c0c2048200c0020900004502e030243d86002410042c903080d002c6816a8240301900480f40d0a0710700c2e1725192100d44c04800c5a0107000c24240200701c205800700003240b03050300800e80108001e810740724811042d803208026607009030003a003085030b030070400c3c0310481c10030b102030651000b103500c05036052803038103d0720003028401882442c81030440410315080901c000c1d4100c1ea01700307134080c0800c0c2d510040c48170082d4495540400c240c0b4101c0703a100006550f20f0050421038403030203005002d0a0804c21100c200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 198712401 1250 198711151 198711187
    0x20f0f13081c1b020409050a0209010f060c152706050606040b030a11040825050a26010209062b050c07080d09020306040f12030c050d0504140d090e09030906 69
    0x7110740030508440f00c009600d60744940c10855018902900d44040a07005120038420180d01050f21902c5050f81001040d611001e030380d492503440748414110000b4030381104081c0007090103840c1c070502142c0c02052040912900000101d104000921007542d41000300102801380d88548a5108420000196400d0301a07004009440d44c4600484c10310791120115403405500607034a20340c0c0c6007822100c0c00c40f912030b02c5a03c0e0050030121a203011103400d000070314403070030f660300c42003200b04c840d08038444001003080d0180c80190300042d14054a5202c1050780c0c050401d01e19030000c60000301140c41d581c40f107040f401064824217001001520305115030346c51500561183d04000e40540c1c3e2000c0b1000160780c10b0010a0165001c0c0100705491030090030407214032082802c41806240c03605501070001354001007902d14851029000050940c0c03241000340c011507120b54a180e181c09000728210506d60001c80c1c07141603566400049845640724000300d03540384182c10340e5650196081c0851007000e4462548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 198713651 1250 198712401 198712427
    0x50a031509051002040810090816140d26060f361605070b04030804030210060902030a0b011412190609020414180613020f0f13081c 58
    0x10008072221039803107032420094001181000b158001900b000a0141005644542c40394164200800c00c3d160f03076082c030f0511400000d1044082c502803100d0030b003d4098054201415110306413400200000b800604d0380f02c02843d40fa42020652007080103500708240054812803005c0d015080c1c000811007007020309411641e2121f0103c0c2c01d240e890b41004c9000e241d8070410414012490a42c2c102207141515410801800c0303410010140001d1001c00c4400c3d8505401c150141020000342e10745003401c82c10325440d0714030760b04194140540064411f10607030065109800480c41008900c0c94200110b8070413038200b0102c8031303010040c0000307450902074190304c13900f103420044615081540103800c501a28510783c00f8011459000c9000c100341c209215070035804c100d0413145500b00ca81e68250190354080060061402115120000d4a07400001da040307039011030588044e1511103003100038032559a0301603800c1180f50040b00c040015200c2c000660417007105240035a141c03100304c0c003c004603880070940030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 198714901 1250 198713651 198713693
    0x10603181b0f09021305030624040609150602010501050a230102190803090105010e0115030c0e0406090603140a050d0806010c020d080d0b0f1003051906080f0d0207050a03 75
    0xc400203000b002d045403480203001d0030501503110180180256050701d003681c031680c002c0d0400020420885000c10100c030070510803142c600d008180241c00301300105030b143c000404191904003101d074860081c540040449000e98000e20a503030f00d910900c004c20540744540240c00e207a030a801340400701e440c0e080307405a030b00610407100054840072440481c80307607041c02900c000400100b4005505020b000b468090f01c0c000c082128954505204207922007929501a0b0426940f0442c4404181c480c100000032490000c00c03c0c0b1045440c3e480c110010300a62000315002100c80c00040280c02001c1a0b0141c142d410401502c0e02400c9100142d0b201c136002450203040205131217459005030780fa03e031704103066030051a4040d2508200c54000b4111407554284034410035401c8600903079962102c4000d00440d1003440c1c089856203503500045c42128246c0d00519003141000c101203080e00000861001a4003039904482d0400e401c00707010780e20381d115405603030f810100c1040280045008001328001c0b4141e004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 198716151 1250 198714901 198714953
    0x70c09270f0b0115020705150a11013b010c0c0f0c090507030615020106050a12062007021c020913080c071e0902040503060f0c0403080a0e010801060318 67
    0xd5582e00210350300740c0000600e11140808044010b5040020101800040d140c0480b01c080e018400c5465018809500c02040441102114444001c1d00410607002060803040c412039407008401c1690000004035100c1c52804450f0b04565840501071024207807070075201d40f000507505c1c1d1a40109208640e800f691855044840003c04c400c0d02d00c101c03441003a090341c00140d1581419080050034104111010440e8181482884290b9450440804a40d04d06202600d0f1074900c0c40c2010180000801c210614030317450802c00302200200c4014915680700700c0e60000017000c44020859200c1d9000c5000c2d400001190008400c468800b40c1900c0c0d083c00f44030307254106003c041201c1d160244c5900314000903602030f541040e100e0399009085001d45a0000c05500381070501002c0396562100400c001350039143c26003c0740701104400101c9011310382215402c2da950013103040140c1644105200c441c00035401c4400011094401d100740c1c47d8085020300c50310622a000d48a501d1448280241100440b10b12 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 198717401 1250 198716151 198716153
    0x30d05071a093a020a0201140a14070803162d03020f1303020a090c12020304021f0201240803030610020c0a060e091b0d1104090203010902070c09270f 66
    0xf0f001841d60240f02030444218500c400354400a0300d81804030203105650041241d440187c0e0050340d07054507419410050f40d15051816000c5402501300d45240004c5680040c004042c080c030b1300010b620030840048800c003486407548007110380040318402c4001c0ca1580e00710458400310800a2546080380138540581407400845d4000015031000b001c0141001c51404d041045050010b5088010150b02c082005401c5071884054844c80407030010503a15940040080d0455444164501615a4040c4601c000501c1300c04040d0003403044150328448045a060411001010801d05106a5514402960858580c10148800b103494030749800c1c203501402801d40c1c02d9407180745895009022a035241414505104240b040c1010045c0c4a0340c4006007075010708205048683c115102400d000fa80090358650071248490383d030250782c2180c0da00c507000200020303403100c25030080c05010303010703a80d0070034810741e80d86500b411200d100c04800030500c0c0101c1002181c248540184a02c035000e611040442611 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 198718651 1250 198717401 198717433
    0x20111030a1a03060702030429030403110105060d0c050405180d020d1b0506010501050706021c050702160302010f0c02060c01021b0f0f0a0638030d05071a09 69
    0x400c5900340d5485035650120b00240c25680b80d850300594050b006004c49080c0444000d4680c07180d07019405004c551050150301c41001d1304603200c078913024880019224106403600a00e00c110744040d8485960030440420720503d00395503104100396001120400272860702007403001502000b4003400848149800c8100001030a0000b02c406190550280041e0682080094100940c0f100b00c10000d0300000e070040300107240001e031541034443c2420300303d4030b440c05440c0c1100a8403c510f02d0300c54410000c24407540307034400c82e0403450040071590266050110062000e449880391840040d00080036502904041801038584010250015007401d240c0081c46201034266071208124a00703458140c0365025500201384490700d02203480501a001c3c080070f4000060b0745550440003d0005551400000c14240103a03402d0441e9501e07119010310500c1004208845811560304001e00070f00035410a84c0ea1184154215030003a44d1022143c0b00c2011030781c408041405005000058501c9802d030081d00c0e0303a074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198719901 1250 198718651 198718657
    0x906391c0203060a0603060e060103181a010312020f0c04050a022701090b0324010309060e070618080604060c02150a020c0d0801030503090d02190b120106080106120903020111 77
    0x29000c4800350b40c9081c41c07024009103c031140c0c400701c109450090288004186110915040002480c021034103060324be680a0084034103c5000b018104105007091100d40d0030303401c0e80d040701c0c0107404d03e1090b0030760404142e0304c54921025460158001c00001c070000d203895400729400152103000181800c0410071341c4501d8000021107030700748007140c40d5840110340e8404034500c0a852085812030940c1841708204a40c0144030341c06100709024161032038110307442540210b0019401880501003040071644042e2510158015000042c01d0704501160744440040c03d1411540150000c1210b07588036140d48004200700c44040046005075900d219108403080c000b14002c900c00300006039580360305190320b49007010b01e445071410f0181c51801000400c81c00b209a0307401020944801e4620710091000510301440d440b001e1709080c4540d8000714080700c0e40006032001111610030b200469880d400d0a440c125401d1190038000343c081d20403a07030b00c0580e61304608000e900ca80004648260300d01b4034004030350 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198721151 1250 198719901 198719947
    0xe03040f0305030421120c1e03031406060406090b13030b010f06090f0b0a0302091503190b0f06071b0b18090f010e0c0703020a020909010203090639 65
    0x10f0300101d801e000d60010151280d12808400704843c082c0710342e650340e80660f1002500c1070742c10701110045034414808001e1060070101e01080314107425003000e1a002e00180300c44d404c1c1130140040c181c0002c0d072a050000c2100c041c2d500e251180a802c600e0451359070401d0703011001040064102e000000300284880481c40e020703001d03103174182c10b6050610600030805040340d4000c0e604000400801c202c500c40340d10844100f481c0c90301c0c0150761075444401080202c8211440b144590100204018042c4031200d0b000781c00b4528290184110a4000208116080c80c2c51125501400c1040315400041142ca09002104124070a481195548489106d030300d402044002e0358210303401283c11014501610001d90101c44500c03105169418501d8600000c50000d11104001000240d5002454000c004202200ea802480341c0e425103402c23102d084c082e400aa0b08209244201c1c1c02051404100720300e03103100c01020f0003101c40c1d6025805008403141090180525914804011084449080e1142d050b491 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198722401 1250 198721151 198721153
    0x50d020a031e0c0909020a02010e1606170f0106030513051504030314070c02240f0405030c030d0206040303020901031d071a1602040b0a0b04030b01080114040809040e03040f0305 78
    0x34002d4a0008401c52040c1840c4100c94602028071031055040000c2c0c805a91811100603110440c8600580c0182031009005000c0e12503118644614401d07155880244c5000e070781c074a0030f0b1004402550340340c1442540c80e040c1e189442c0006010700742c8240d02c01c0b940b01114240c132446911180d00c6007414441003803550780200b04000108001c0c50341501035040b140059144c00080d034a02680010b01801740480c009215000c0464004820558001d10350101074242142030b965009581074881c499010388210790007405400d014001501e4046400c0c42c2c03070b00c069009409542d40da03070b908400943c8000c0c5011b050650703030703c0c4604205050602c00d83d60005004002c141960030502801600e15100000c40c0c50078000b00805201d1031400b40080705900d90580d004135050391650300044244015400840d40e404000c1400401e026800081d1130407160700c64000c10003007030b0114460541c900d0842c0c000d8240d000030895181740d81456401580c001c0c50740c5096030305140e201c07c00301c49514116842540c1ea = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198723651 1250 198722401 198722411
    0xc0307020114030106080415020d06120204060803191101020d11070209061c06020309010b0303030412030c020106140d020d1712012c0709031a010e0f010b0301050d03050d020a03 78
    0x11560480120700d0358005280b1064119850880002c15924005100070003032401e54014011060494059807050030000700c0500c03a55840300c01000c608034603540c0c00e07440f850902c100010303841c0d8040120741d40d2114081c0520400c084100c4160703030094240e9212803032590300300a00400c400c01c500c94228030308030046450b69154038034010401c0380f03200a03000c248240d840c0480d04410780d0a00c8a8844011350000340580c80e82d9512040c140102090302001d034050200000b00020090b08038440c018800264804008110700315604030300301c1d0058000c3d01507904005940060619020060000c4984000c1041644800d2741d41c884c43c4550101024012070307440401e205004008910405000d00b0600760301c0010421007800c00301e1811800b00503408207207007601c04030f468603101e00205c1c4050340d0008003005003d00480e140d0340c4049024030607100580e4154010a49060401d1802c50481e506101043c0c15a400e0a0811002003d140741c120113010341040450042911400946484041c0d5140051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198724901 1250 198723651 198723653
    0x13050301090f1a010608130c0504060b030106080c03010803030105220c1d030f0a110d050a03020307030f0f0c060b060d0e03030103060b190e0c0c1e010c0219080a0905060c0307 77
    0x3519042ca40c0300d2120200d207180045c071855900c001d90039031040c03040c3c00d01540c80ca402e041c14a03210680f900403907040750600d0400b00d40010114021b504860441d90b440310140d8450700354070079502083c000d01c02e10b0b820400c0100050b1030880c4034001012180d03107a52007840d001114107012110822a8507020840b0642065192010701c103440c80700c0e000a40203070040d269040034250b140c03200c00d0340040201802500180b55030302c2c1c04091800750b91f8410f080f101d49030000c0c200a507403504141c030f0850004420005803010b40d803096807510314814903512800e1403481c403030366208090300c0d076000b85c01d40080d010301040b09035419a008152900d0b0840300a5540c030750540c102030701503071014484a0b00800800381c1c000c4421403049001000c0703900545245111340c6070303496a103015120704240c0c03410610504e240320345014601c82d00c0460905035003008004640681400b030761100c0b0031507020b031f0840c050f110100c0d0200e1200070091042100b2480d0400c803031605c610002d15244c0002c7c0c101001d952010400f90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198726151 1250 198724901 198724913
    0xe100501020d0c02030c19030206041d1005011e0e03030d0921080f070212030411031c020a080c010608190303050f011a0a0e040f0b0108100608070513050301090f 71
    0xd407845903843c01080f9901160040380d91150f40e90152409881150030710b803a010060351007040170b903a00520003580c03590b4031140e01d84206440c064080e042418240498a01041e8a4906045401c180c4031050031506440904c3d001c42c4415145209004d094040c204840e0303014001004004040e2000049480060400e103904441030034181103000c00454411308141e0b0071801c541da2102200e244a4110380c0d402108030304001c59078200704040e000c04024401004621000800781c05c809171700300e03031039440300306844005104169a11400358105241c0b48001c200b50310000d2220702030500004c03075180e640300c8406142003000011044c01d13404420050041540c140595a00400400c0c3d6012680d4100000a46101044101040e0000c400038140000c240900305198000794020810004c2110b0601c4110181c400300c90214000748011000902242da0902d80300c091300e20955851110b90795591061703402e640304000420216422090000d07a6076000d0040038040303841922003142205280c9841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198727401 1250 198726151 198726163
    0x702041b091a0c03340f060f110f18030a05010207140604110405130204140915220f06020d060905010501051e161502031807030515060105040e10050102 67
    0x102e010030000c071800d090000050350001945030b504140c6840000410f03081035080340e4407071031482154990b500c0c103020319503800d0042207000342c00a2103510300840f007a201311040c102c075205c81c581080c402422480000b03400340c0131801c001d04141008050580000b803500d214075204446a0790001410b404201c800c0c0950180e90001c0c00003020390342019035a424884440d040c03001c0c003513590b440000e01451002c2c101d8420701074015004106450101124240081088440d400c030740c800d040703080384180d00e0750030124468161554001140e040b00949170308100b035900d0341561007071604c0c15802c000c81c020384000c000c01c0000703050014540d13203028100d070140c0d6416480503041c80814000c0344106204001c4c8100e41000d4441680d94907c00c080203000c405205d901c002d09a002c203518605040500b9900440c0105010b010701d068901000e0700c21035860901d404000c01c0e130307004160030400e64032984082e683c110b0702c14141581055211126042441d8040301d000352200000072017004035507014850703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198728651 1250 198727401 198727439
    0x5090609210a0507031202070c1401170606070309031202010623090403030f1e0e10090510020307020a0618030f081501050304050c030a05070f0b030103020a09020702041b09 76
    0x5400920000d10034100307442d01850031804140000004c032003003094841c41c0180d01e440c0400604545a00c110f041c10403001e029800f4000c046046081004030b2503008802410440900780c900300300079610001480141d0300008400c40600c800214080000703401c15988448110036540006040d5141a10041c072541b010b910030646010a80b00c40b103020f84400071626806601418041010f030074813a601802011041c034412241004540aa0420500c64001130711a09040e8112100103142d012682d045514059004000380d2010500c00d4041145402035a80300c18540117943d040301c0c42e9210032040d00e6001014924803501c0b48410401c041e00710a1354038280c03415181180c45460300780200c4c91180c5402d03804034140310011001a0402000304221884041d005d019507414880a140c003d55507401030199940340800820f020031008880006d40f41200d800406080340315140004103002503100310420f981154442ca001d03052404501c090002420903903aa24241501e855002c030192464440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198729901 1250 198728651 198728683
    0x61101020d06170115030218070c021504030501140603030418060b18090a050c03130203030f07030216210b04060e0a0b01080f070305120309030c01110d1109010f030e0a02030105090609 81
    0x174007880541c8401c80740c10712010070407003441c1103911120410355018100c5030000b0b502c9103070a180d540301100c0c68005070003201d107d040240010880e060390409068400c440c01601a40b0a102c02c0000650f8044440800300d4296000240143c880d0741c0c003c00d80d84080c803211805800003520700c0d894106903c000c0e03441820032404004c5030402c01c41e494410301c0050402d444508503503c0c10015036506000301c80d5040301c4641c807141d03505039030f16000c0d445808017202180e0f030382140a0000381e2517502c41d20903041c410001c05200c0003206541d6035a04400340151050300c1c51503a03450045900d50302000101c640754001c4846100d9036260200c5d481c03078140b10110403090b68200c4041040080c0000a06035048544071a1984c1c507075a0f220056459401001c00c200100d40c2048502e864070000c10006140880190006000c070018a2000d007c40b4803540203d10700051649820007803540c840e038084007024403200300f62071092440b0b4002909494094860980d00d030003000910919138010070000c201307001001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198731151 1250 198729901 198729941
    0x305070b150108040215040e09010518030304080f03070e040216050c0d20040b060304240c1e02030c0106080606040b0307030f0303050709090501080606040509060c04061101020d061701 81
    0x1600003081e034480034000a0280150500782c9146c0d641c4c4c101a10042c00001404071701600e80184414064401510070390807514034180d00407240076001c0100d0744240e0f08a09504c7c5003d140c0d41400c4e080b54002040f0104110a020007410680d480b40005c25107851045140e0902100340e0400314101100c80b0728851142001c9840500003400d100c5050084040000410258040305c1e00883d0141c1640031b0b40c5688803200104000030051800502c0e40d50b0698084215200c03d41c1409180481d0f400041210128000180801d8801c8a6000100c84055188103590418078002e452a00396481c9e03401008081d0400000c0244504061050364102c0c00d00302c0050083c54659203c0201070002520058100f50301e400000f41c8560050000c00c0c01010719040400140da1748101040d180c1074151900da02c6103003081c01094603010001405401407d075044c900d40703024a401c00075a103074106080640d050b55001c2c000300c0c603000c01e548614030052821807a844250880c6072500c50071640300c030480d00303e00c44050b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198732401 1250 198731151 198731191
    0xe09010b03161d010503060409060212180c090a0e0a080c0304060810060504050910030203060a0915090308070c170315100c030f052505030a090e0408030403081801090305070b 77
    0x41259210480f00a00b042503598590b00c012030301030065000090310381400001c0c03451104041c2c44040c1d101c1d500801d21601c000302504001512404041030165201c421640840c0060a03141d00c0003040c15200c40131030300d5442082d59501d4030384c2c10140400c40c807600081020031402d03400c0341c446544016030440111060342807100140080c01140107844c040d0350000300003407041d52138001c20406035800600322941d6140c820702c03e00103411030070700441e03500050307031100c1c200300102d4020b00422603032544880d181603072a80c0085035582041c02003038401340303000e9611681d9079274080001d5014503030400036241813035426401e100201c6004003030b180411040a050744003103075200400708048070040c6402c0d1766412881c00b147c80450800e400004c0288a2b030080b100821200200902d070416468561071501545c400164414010484015200010030000240004d100b550f00e50340c0b14025200600d01d00007180a99400c48200300c000f240441c40004480081c0144610350950011111040c1044c820507 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198733651 1250 198732401 198732437
    0xf050d0908070e0a020903070b0c0109150207020f040f0f0e070617190c0c060c020c010810060903060207050f07120b22030e060c2d06040f080a0e09010b0316 69
    0x4000c1400341405e41c04100d5181681e01480414002c00c500d401a640355070038194828001c080304841101d0f050341404100e02030581600a80d41d8042d00240620280b60700c08051001400800b0710341055240e5034140c035180034001d48594410400c0303c400400d805030800c0c001405580041b14614580c400300410010b1600032103281038484001c401e00480c0c0e940000c042075035805075406000381068200b0004185003580001e81c4004000e00340d8403606140c45008a541c5d20304014002c40f80003441011050002c035103a50000c01c0128491001c03940c0580e8407560707003418844507400c11603080d40c16000c0c440c14804540c101d640c00c2980980b4201c1200d07a8903140607603184003007000a00348008074058922980e030307003000d03900c80d009001c06a90310b13507030404803415044c03508046a048481240c1e0011050040015040f4803c5500496000200c147d640310720340c8942040b540b000401c0205107481d0070540750f5080300341c000c216081702e864683c24034100364100200c04418820801201c2c0c0c0c0440c07401c00c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198734901 1250 198733651 198733679
    0x11403070309032105190b13020f040902032a0a0915030e030a02010e0f03030106021f0209060a030c120509030409090501020d060f170a02010815010302070f050d090807 74
    0x1105050000b2004a2480c00b59100011103100f080d2402c00d483d203000700f4110f107820551080c010302d5480040303007040041910488517840f080a0300440b00120003182040241e0080c98a0701e20704554078106640c030800310b4180c0e48111568403c002314503a00000304008401004003444031031182c503040001c181d20042c4410020b1244a149080412948261070b00a50000103440150003c0c0d82d59220080f9000c2e0103031403984040045441400000b4154070303400720680b81600e055a0180c61400b1400102484140d1242480000c00b5400c00800566656540007401480c5c880d803000314903000c4601c0058401e101d60300b0b40c081c90360300700002c01803180300c08412102503031504900010041003d090250090003140c4034205400d02e091b50200f0080424040002250f590100c07141c0b05d0107040c101251120b510303140080c0401d01442c0031a000c0402401144200c0c2c50614005090034503540f10190001100d403000d036081e82000410401403580901980040c200e8030f001841d1003454040385c171130340d40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198736151 1250 198734901 198734911
    0x90b03030a1d09160f1706040209030f0a050a02121c03020a02070305010e0a050d020d090b280c0203010f02040506030a05150a06030203070305070903111201020f1602030606011403 79
    0x441d02c035007201810540d603001c412003030060a88001da107440461014920b10a08949011036081c41ca0326203102d216402d001500d1103145d4001409445130b90078032020703410040c80268140540510110b2181d003c010350559203018500030725551401d40140f281d00651442010601d4110240300d00362142281078150b4585620729006a0320241c080b0b00300e0030400f080e00002d21a50030705140c0c0341040d4001a542800f20f0184c410349148070100c95003030307944104080da1030b008208042f004205c00442030001d0f04d81c0d00c24005400d0300059410344041c0341110b046010b403010840b52403030001907050900c0380362a1078203d844110324044c2440700055407804018034101e600c0352104001880210b0100c8004840c04000d04800324868039104041c0c06904112176160000b441c0c900000c002d14820741c00e403c11650010340b240e805160b12400d1040c13008000701c1642c25590200008088188103100800401d0307002201d600ca5088644101810710700060b00d428100040d141490383d100c100081100c1d008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198737401 1250 198736151 198736157
    0x4120209040212070f1a09010206150102030f0408010f0605040204182a200a0f031d0a0f0602011104240e100c060c0c03140f0c070b040609090b03030a 66
    0x80d50703a0388006030f650782c28221004034500402500152061445800000399200e80304100f03092a220015100305009403203405005a020038046000300c0b0300d000e03446030380e0072040c4140c1340341030302c20ac4003072255a0203503110803001d80d5940e5000c0d0403800c051189002400e4201d5007546068500b0111001031030413011288841a50b0308001e40c1703909c10038409064001c940c0d241220042d95401d101911488070218540369850644224450b490000318100c0300042d4000c1010a011046480803204914400c01c3d0202150303919500c101c0710380c3c1d031507440350080690f5543e91040509200009081d42d000400002458006010070b22189403603d000c0c1e101043c4100d80d036042c01e4469401140c86084400c051600541c81240500030700d41d2028150240314007072031051001c1d400e116022242d040c450400a4006140c0004108218140c1d00040000c0101e8258060030701c40e42001c4035007461455845410300c042c3c00102080a09c1d04038080100910100e0300401c110301b059000300380c0b00d2080008200070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198738651 1250 198737401 198737419
    0x190801080c120c1909050c04031a07050a0516051b040f0b060a030b0a03080d1d030a14031b0c010903020d02030f3a050402030c0f0303271806090c041202 67
    0x1a040b000e13980e44005100c0c0c04014000f5040103036405160782d020340820740780c61280080740e07400c1210b40b4001501640300d0b40d07546031038a2841f96003200d06030410000c130b1078000e140350402c4d801f1030010842c400950601c45600c114202c1000100802c54841400b4046054100000440981d4075081612034010580c100402c240d24144002800380003a80c0004040c0680031032854003c05d115071200c0d0031036410601080f10034541c50f03c89950390080010403000103038245811411501c114002e190440c08405444022030360305000000385070000004415142c1d9a0005807007070650402014141c4c14031400918540f0390f0100c44003001d0300ca00b0b040310039051b002c510100780c8440d04620807071102c460948400f0301010740a9944029060a88040c0d1003481903c3d24031215241003101c000301001d0090042d407500781201d811400c021030440b540e651502003508481e640340c6440610718904080c040d03410790300d890329504000c016035000d03002d0030540c902400140803501496100c0780050343c040f950030071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198739901 1250 198738651 198738679
    0x21070509060415060804060f09120e030313120524010e09100615081b040909021c080717030712020c07030512090301050618010317190801080c120c 65
    0x405400200c040c0801820003c000013400e60744000e229018500c01d540602608040d040e114080d110359010103010600d0340c490040d58039008604130b218400340030341a03904040b00c00c602c0210041d015407048090001e00341c4a80c00300802401440c8144000102c08080380c40d00903c0ccc030034007843c140a032820101100020440c03100c01005882c8940c41c84400502c00c5545452240d680c40c0d010b8140700c4089120304002c10304804004c0002c02e00401e005911604043c5000402c1e0090118120180d17005240e0340e40c02080b6500084000c40c05c940500701640e03071407406240105400b401c03510145840c3d03100380284940c4580c00b2540c91200b1150310300160311000c090388036509001650384018210310802c546100205003030390150040074401c8008026640d11030342406000702d041115404078400e140010b00c00102c8503004022400400100281081c4201242c01c5102c1c2026031307d200400d8040004000c6400200100110403006071440d48a019050010580d140b0085440d544610401d1907012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198741007 1106 198739901 198739909
    0xf1a03010f06050325080105010e01030c1502060a0207050c09100906090501080c15210114010e090a0b0d0f11030f03040803070f02060705030d0b2107050906 69
    0x100581860402c110b1003042d0448170b04194070345080e0f000c500d042003441200c5c0a80204211914103504505050240818542c00030b4807001c07020780050442540420300c1a0840750701c04001d6103c1a444c606a403e081292101e9a0040c40c0d000400c284540840304480072640c400c082040380c6c81c2c48440c0001030b18024018080c450740703c3c7c4084495410102402001210607041d42400c00d112030742c4510101d804a0000c01c80302d2440c0c00144041c0c00003d02e079124800c02401c1a1000a083d400400d4900c000245065a466691166091302c1c0d1100e0081d2080254486140ea03111613040c034000c041d2001ea01a01c81c06032040a000d00013801c0c000045a003500c044400850030408155511880038641000032600900c0a0041e00f0010b00c04001a00c8035034205030022450810f100c0500c80e450b0b24601c2c298645502401c0c41303101c00344011401c5800d4a070103589200d22959000089 = true := by decide +kernel

theorem cover : BRFrame.Cov 198561151 198741007 := by
  have h0 := BRFrame.cov_init 198561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198561151 ≤ n) (h2 : n < 198741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
