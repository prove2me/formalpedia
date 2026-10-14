-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1995
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:32.938997+00:00
-- url     : https://prove2.me/submissions/5b55dbca-3a55-46c2-93e9-1abf711b86b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 358633093 ≤ n < 358812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 358634343 1250 358633093 358633097
    0x3090c0105072109090606110a120917030d2a0f0c082208060903040618090203040c0f06020f070b0a0c0f03020f010b06040501020d270f081912 63
    0x10340c1c1c0d050015400c0e03410300c030100f000c80c8102581e200d10401400d00c1003604c2a007010f07034540080031449034803c040030b84480481c600145030140040c0c4808200b20a5840c2ea03030305000039a88006005941c0080d8000e02c0d00e4100c000d144c840c1c9008101ca010313a03c856040c100404500c4690780b040074460304070428090f01c1031804036440c500700c0078180d4001001c14006024182c1c0400c00b000c401000382d0b5100180e00c180000905555580d421040e5102c0040e2101100c1d03070010b000510140e4858541803249000104100050aa8480c07004040380c1c01a0780130b880301c0312040402e001c2202001c882d000100f01c035200030300c04d0b080c07512030207603c40d007280c0a01d0308010300000b0344440c42807080c031a10b4040d507003004d0300d0f005a00141c60060360310070103004414070729424038020f14014500001681e0440714103801810100051030720407200d001c0400030b130301c2d40c044c0b07540d610f01c0d00c0c80c01038441e0380094802007410b075010500380318030145048a0b050031440c20114103400540090000c0d01070101180c2c41e4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 358635593 1250 358634343 358634347
    0x60105070f06150f0305010c030212160507080c03030907080c01091a0409060e0a05011e050906041d0c0a0b07030f200a03030b1f050412081909030201110303090c0105 73
    0xa894564040c102205200341d10400100001c144004c44807484001c480c800d4008018410044606401760301402203544d05c14031414001540840c414052261044803910f00540f030b240b030698501421703400442c2820800e5001004001e1180002c10107a806450300360001c140151039400000c010324000e02884400d6038041140403002e0040b0010741e4081c001911040c8880c0c7d840c1c0392004100041200d01103900e034200000020761440b80750002c4005584040510409410042070101042000e4070707440d0450f58804946940b965101074020b1aa0704817005400f07240040000c00280303031065080034043c8242000b54500007500039141c0d807000200350410509080705603101604012070521100c81e14000d00c2d10407010582c2c0344c4d0040400c010205d80070303a0f440038110700780344044d41c03082000c40204204200030701c03091004920003c1858800e04100d8030f44003003009807403455210016808046106914180110341e001042860144181001541549054118183c3da212071810880c144800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 358636843 1250 358635593 358635623
    0x1a010503030f1e0c060906012103030203041b0312021e0c0d0213090501020d051f060509061c0902040b06130b16080a09030c0506070b060402090f03060c12070806010507 74
    0xf8035400414003c11540210b440e0840d40c0e4040d0b8a5600c01c440f0a291805114000718040340c903484203d841012013104000210a2581c0590080d407010740140da40c00004c24207441d881c2020001040694410310000394070301d14100d0080d240c40d681c01d0040864100e001602c002213131001400311100c0804440b80300307003507a650020800100d9408460941b01d801e1045080070b201054005003094000d14204100c20760b111240b4460060107001700902d4400d08010822007107104801a01448030000c0090345002503901c203040d0990a10b054070184213840360204c50075071501c0e01c110b425014050ba42030b8079118220700103041d03550450090b201c004c03d0104205c00985200c0400403070881d030180c0c00070354454040501a00040486c441100c01101540010030703d82040b4040d0340034254042042581030312a1410000a904550085e6400240da0300d0040d01d40d179810800039005060116901d030391000c8040e03c0e0600464000c044205001c041070501c00f140c2d910400319180c3c6604140345c03103182c2003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 358638093 1250 358636843 358636867
    0x607030c02030606040612060c0908030313020f0d03020616020c04090506010f051503240a09050609010f141e030106060f03050a020f030103022707050c2a010c110301020d06031a010503030f 83
    0x102c1c540052f1854071001c802c0020036000861a4005940201c62940042807141c0070481c21003404000100180c1061001c01d240b07140e1000b800004107064015501d85112480c041800c4850922065a40e43c1c00100100305205401000402801c0d0580d0a40b401d200c072181160442d00c80501480800079542c50b240d030ba003c60003030a41b40c0d00700c0000d200f400c00780d80d50404031000e003000b5100c841c8a00010700c00000d000c0802c0c004101106c2c504500d202445d0503140801c580d6842c1d036003240140d04000340103400a03550a21070a4050900c5480741c075081101048021f040307820040c585003c07035104101d030440580712242604e04480d41160710183c00045051490b11040b07220400040322081503061080c8a03400c4070282c50100c1d4210204d4900b011540015440c40500c0c3c04c80c0d070321149000b81c0b04d06195100b81d00c0301c000350740207689002c100c40882c2e0101e401ca03071090400c02d80722a5540070a004110f039400f584540d0140c14100000254103003800a42c40c2c3c400d681e90510005c0c00020303101c100072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 358639343 1250 358638093 358638107
    0x6060f05220f0611010e190206070230070b030a020d09050d020106060e03070509040b090a0c060c2f120c0a09020d0c0f050703120b0607030c02030606040612060c 71
    0x1914481040c4801d0765145808200d80e0b0060180201148481881203244e2805200304821941d0000090000c01080202800a04600380083c2c0c0c00200802542e409070322781c0d00c1c640303004007060358040c2010851720102546c0501515501840e5401c4000e0411100c41c80e603080c3d07904034680d00001607231460711040701c1d0b004080c4801c000309540502490f2080c40c1d070301903201404032103081d140c1d202d42606440c10962a04401d004469200c0c0b82240824042211a20b0440d409000f1a040b60f001122680f03c003000ba011640c02600001c050809007020040d00c3c150310170300b01c00d00540e1403903240003030700c7c240b18001c1040090600401d056001d207a0154000c00c803e43c0d04840c06025152100d43b01c040150196110720b1892802c10b0800c109414100d102da444090382201c41e90f42c19050020503501143c5c244604600003089580b110800c3c0ac0f10380d6403070010300c040c1d407094480c0d501c403c401788185820240000d14036441a8580348c01000801c4400c0030300030344254070800004d4030001004003501c0e65 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 358640593 1250 358639343 358639387
    0x80a0f0522030201080a0e120c0a021305072d110106050d11040b06041505030c040e0f0702070e01061407080c1603050f0a030507060b240a1206060f05 66
    0x4862101c00024001c0d07021400c0d07038000c0e0b8a014503980c40441030400e0300c1c4002c9078541ca5a02042080410030840d07000703041e000400c00140d50348861107400041c104115598610000d0b90350f10240002d041c0c001c01040c627204113203c0300d1144460016445a07181039a04007040c18030010910501c98044207501c10070282c9001003500301194003900f440c10741100405400350103140b80640c0451245400f0040d2811100c03140304941e00300c1400003080711960800360882c504801c062102013065000c1c2c8604612074085150f42c0074a03860a0b110091070300d90aa03000e0b069090041c40180f00507907115203004001b00070381400c91b41c2e480151a081c40700e481a0071040459000d40104900d502c1c1c041c00400c0112801081201e010b0000880c81e0303500c449604030000c002c18000c1010b040000c0454211010960008002c0e28088000d00d510a00d54907641d2200c0c40e06540016200340303419040604c0b56140220307002d04100c50b03824050043d00200171840c49100303000011960114091480c1d0800b850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 358641843 1250 358640593 358640617
    0x30e0d02090106050909181c1209032105010302150a11190515010501050d050c09041416020c0f04090c08030f040635090a080304050f070b030103080a0f05 68
    0x2540d07940b024020507617045514964442c1c2e04413000306404021107682e405e102c01a14005d40484914182464690035a20072100c050010070074502d0140034841c401c198650340242c440d4440b00c07000d2104000c1102c402d2580040b0249050018000341e00d0312154001c000364000c00341551580281815983d80d081f40e400c40080f031161000d100310110b200748007035440a12480c21250240b0704e040d014a00d207003007401601d0006409108407000c0c8145604440e42015005440d0782c0340c00d0b420300200d8148c44203144166940e0284205011000305103802a004c40c201c02d20180aa0b80c50b804002011040e52000240c484c0351a94080014825400c0402c0000c0c00a1001c69548801048a813140c0d50060b12503000030805006103028000c000b1040d41185a4540c104002c4001051807081584c00c0b0180030a040e41c4514200900020b03260b00c0218086c0340200000c00704501013441071031406589410510950b00144010400151904243e0b041c070f403558200348450190b03000b4122101d00548140701d078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 358643093 1250 358641843 358641859
    0x1f0504020c0102091c030212070803070c1104090302071e0815040606120f02150901050a120e070b0403020901051813061b1701060305011802090301060f0803030901050106030504030804030e0d02 85
    0x1048902240703a00c00000d101c0c0d02540e49003023258065400e680140c0d2009010f41100304009008644601e810b01f000301e02c2540304944081d440e00c00328003154080740d0101c0c09030703000910074885075014006200200a031212071084c43c60800c00b000c0c0e11030741c46e6608020005110804201004504d070450b20280030941003c203405400b074207040d2880a00c00f80103900803000c44030484104003404044070b91400c8103841d524941010038800b01c8140c0b14007014604c14070380c2d460030542d481105102441c0107090f48040c050301d40c2c1c1140100b180744003040c0c0c01144180000c46000ba84a8420503c455020b41400c269070030b203040f1810203038007416503060001e60b0a10815580c81e41035400c508042e61040c0ba0302880252a81c072188168102c600030300600385117000b001c0c3c0ba40042c07680c0d6001444200c0c0c010f0000b08005079110100d04041c403081e08200c810b500b02000308054200248103481c0108214603081c041030a2580f80a440648060320140801202c440c5c0e0804940390818031000f0340fa40648048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 358644343 1250 358643093 358643119
    0x6090c090c081602010212070e01120219181a07110a06030c0e12100e010209060304061d060c09130b22110304020306160c06020c060601081f0504020c010209 69
    0x41c0424812a1000320300f00c3c00c190f02c0d007140740c0b0510a0b0340340402c42950340b65568803070400a485140341210010304000c06a1f150703021600c0701340042c101e0318052081e202c840303144103c0007400c12111103020740c0c2c8545001e8003c1040c01701401003500044158213009035076015a0034130111005025180c9034012624500001c2c1560345580701c102c003900660f032050b24411040040121005000341140c4581d401003410840e00f04895102c1d42d41e059104e80014607001d05600843c2e4950811102603850954588041003000398a4040c51341c480c81e04009400c851400b04a0011140a14200540903500c5411080002c0780c150b071210304071240041110568000342165800c515a43e0010075001a060601c070100311940c110942e4003480d8003e0203040030340c0d1083d030110301e0780c1e0074124194200480d10a10398041b900610040c890020344d0380c0641810701d00a0009070034040c000e40f030300001001180010408254103041c103410744500f100c001da6101da0580210380a802044595640200500007007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 358645593 1250 358644343 358644347
    0x405031b0f01020307050324030a030f021005090d02010c180909020f0904140f121606061505030a11030903070f06230a0b010e060d09022707020106080c03070306090c090c 75
    0x86c41c410a448202e803008c1c140b24022000c64121075008154140d8408507614000130b001c0c44e104065403084e441164450040c44000801780d58040d04c07410301541100c0700d80803081d682800740c2c08881d2001d0a00e40607403d8041541165022184030700080030f2ba03220302c2c00f4115070f0317034080d1690342080061603000b0341d08290801080c42c044180c13980904c0e201d0762140800e0001d011451075480d0f288002c046092000114803031000441c00c1908641c016681d560201c0c201c14809203c4140d90417558415450f0f141400c2c018040f140e6040355039955807024030801800940000844d490320b54400d50310b070103107182031400501420080022840c24100440604004101018004e00c20b103070100342407005800e5507005540843740b8840c83d5400100410124032901c59a401400b0342e42c0c800740c40a400c0d1000020304452070014a2a006c40e00d40e0444d06100a8590900a90000e045d4070405008a40b62080009a0320a05884000c0a031500e58401c1000e2061000381c610040000440900000b0340600c40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 358646843 1250 358645593 358645597
    0x2040f0606030507021507090e10090219020606010c0f200a06050913050f010b1305060d0903180b1c0e031303030f03050402060a08040f12081902030405031b0f0102030705 75
    0x2c0c800144551081b079440384580c1c03113480c0d0040b2038645070f9051950500b00700f2425000010700342e102d1011062000507081c03401e440200940c00c45492442403503a12000c00a0400c14050016410002c10000300c0d00070490110322020020750040541000490003003560783c0800181e0341d05580841c02100009010f500200100000380c41156040880311040030003004480382034401d200d1440055005112030090710000b0403a540388420150403041d40c176400620f040e440b03034240160158403030a4040415810244949551850802c4280c1a034100650320030b65005510100c0e681c1245848120f05030060365205042210301503058a07600c2c441180c150210440d00d202c114002505910000d02d0340c1d20070701c100d501656000b0030162400400841c11108518084c0040c0c480020410b5080001110880e202c59000e5054882010758a020700040c80e41e94040301c0002e00c840e004000700030005002004948241027804103c1210b5000a80c1302d501c3d01e200c0c3c44040304590302c00400c1c4139071281c2000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 358648093 1250 358646843 358646851
    0x60e01082104060c030203070503070606050f09130201120e06040f03020f031c0b01050f0d06030b0a0207020a120c03020306010f05040513080a0305071e0c050f161202040f06060305 79
    0xc2100c416844540c001e0412150007006a04084000d00c414404148254080702902e030082c41140d041984540b9920304661140c5401c403200d5941e03c00030001400c018510105402080381d070004c03d860042d2035a2140e265004000b4100804040d09242480e0243e0002030540c3c600c0c011648940307840d1400c1f002000c180079064025100c0c00394154018280041140c1904c0104610681d100142c5000c05000d410034020386414800c2c01d109403140061502c020b4880c500104c940412414954140001c1044000d000312030349078010003d8001503224616440201c0b8901c1901c552180710900700041c0c03061007070708000d5140c044c0c1000040d00c840c00c0f241c0300003a075100715410403242e104d03030854036214859004020103401043c8480a0090f001c0d50210380c0c040e1241c2000144105128141c0e5051700d2a00d00ca280842c0c000300142041c040200f114140e003023560401801c00261050301c0f8001801c1d107101c0c0c81c0c1d0b0140c0d00d0808000319140d90b0804035044401c402c045c480c20784c880d54058084c0000315 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 358649343 1250 358648093 358648109
    0xb09030c0a06051f030210140d0f021306050901140d0b09040305130522051305030a0306180614060c0a0813051206070e04020d060b0c0606091e1810060e01 68
    0x82d00d00e041c1109004c021045a500a00091802d980001c0c02d44843c605c8072901a070000b0240a500000b28090040000e091504800180c0d00c1c03a200302031080e44640c1e07400003170030060248003c06907646c0010035580d140c00404010360703e42c150441311002500d90180010b0300100c0250900c410544c01c1000b1300800030319645100c0203641c40c1d81c28008a80542e4880409200103003413500544031403a4030003504040030410000c124080f40d1030780c80c41c5030701c84210a800641c0d80c0c1d400700800041030030701c20812400903000b848a2440d000703101300004020030700f05210350400902e0b11200e04081101901c00d0703a00010281c1c882c0d603402020691540d00b8401d190144510325035000300c1a001141151040d42076440385030783c1240c0502484000d4000454aa403481c0d520200450094180f101810342109000d00810b460700d420003d103c1416030103070807203281d215140c20160b00448800c0c1242e0f40b080c055051503e01080010743d42d841c01301c07089a001103107460100046401c80340dd81856059501d90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 358650593 1250 358649343 358649371
    0x109030320030f0a0903030905120a09091a152101140402030f07030c20011a01111b06091801030203010e0d17060303130608150d0305070b09030c0a0605 67
    0x1418120510040303805601c098000f074001aa8031445504c107071080341c0649400a0000d426584040c40d05031510311914a042010400c2c2001035802480301003d003d100c2c9003803003a8003149010980c03940d00c160a080c820b20081620b0303080e914603082512140038103280440041440040c0c22040040d0a00480300d0000c900d600300c010038141402208c0c0108450004201659260f0703a040300107281c03144101007040400e0401342c051484140c0c01101d11112440001030f07203da000101e60b01c4015000003241880510300225a11800214100d0641c00942942588010300040010300740c2c8165070110354004504500300d03d006d60710851190680c3c0c4240e00800607004116440390395160b40401200004918a209040071054412803d400002c05001c0b40d042c416604421810001140c1207031000605072820003400044008100c20b0351401a26816014002901c005000d1710400401034840118000400c1c00c0600410440340503115314426a940b45009160403c041c200c15030f50304100a6034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 358651843 1250 358650593 358650641
    0x1809011d011203080402121011120115080a050c0f0a0c0302010f0e0d0302070203010b060301080d020709060609090507181d06150301050d050a020907050702011d031207060e01090303 80
    0x602c09061501c1c68143c1c036500340c1d40d034666007048905514154040c649015048040e19088154015625004070041c000340d281c101c0303206509035555050303000101846181d260742c10141d820071a900d400c0b00c21401c021859569103d41d0b013140c0d01c20b5002c00c8403050400603412a0035540418000013051080e80240904409460b1080035518079011044442c0c115410400e40301e4043d074010000c240c4058004a604d912035000a030080e0802d07031080320301d500031842c0c8000c6103505200200c080c10020008002e00c03420007200901d0f034401070003210072a9030b03100045040d0074025610340d1300c0110306140002d459910340329a103000c000c0c4014040a030030403840c04520300c0d143c114041da6500d402c049542d0f04680c03030501002a0072020700001d40e4140288000200561551480f2070310500490319100d5441c012880010b0180041c05031404070000007114029895138082031221590105400e06c54507039810b41030000041400e04a004210740c60030000504150f01170308446140e800500c902480890 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 358653093 1250 358651843 358651859
    0xc04080f070f140d022806050a020a20130b151e070f0c240f0e13060f090f060501171902070605071e0c050a081809011d01 54
    0x9007900a04001e0355200c1018441d540f03001c0030500f80528000c2204098031900d0700030420005401c00070b2036004004003029820000801d00c140001c0c140c91510710300d4803180841c000d4841150003030007044240c8490402c1071051106100340030000000f00091110410ba9440c2401010450707400c50040e4120f0a001c51824070100a444031844c101d03000e01014003501c680d205d0680e1040070700b212004003003848400403c000c50241d4001d803c40d0301c0103004130800e081c0345208010b006101c05041180300041c0c0c030700385980f0504000307000710151220848007050102c800080c00e020b401c0840342c00780010300020300b10503640041503a484200d81c2041101d03103940044032409001c52031480868144d202040c0841003c1010714044000510018180001962400c1c2981c03001d54000001520b0110a400d2900c03404c0c00c0f018903c4014140440c001d1520303a1a2525100000c6014180c6e010106031904580c882010940034068020b115944568481100002c1e01100f4450300c3c001500140000c10401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 358654343 1250 358653093 358653103
    0x90106091208130b0a0306050a0e01081903111614030a0819050702100f0306082103100302040908072607110301060306020d0b1c020607031112030c04080f 68
    0x20706405101401103042d0b11400010f5005a90761455003403003e000091030b29513840a04003004c8155000b01e4054035000421887e0a6150446440340d44858010411036500068502844408140e48400304101e07080685901c0100181005a40260601c007140c44030031a07558025a03941350340500c0c401c10328005040c0d603020301e048018148042000400c5060000302c449001214140c5000d03481c00c0b10b10750101b007010501004a0010a5150050104290300b40c060007000c0d100c414024408024541904400c81144440c0080200e100001240041059452540207150058000c7c0721501207440c1c02c1c035a0750320090040d220f241000055804a0303d620100d1141d2049040342242040c95030b4031510007a2a00e00c90b0140d00d50758030b1300000000303092030014010043c1c030103000159500242c014480026401200c8050300000c0c4c0c601240186e48490644200a400d07152180c42505098407842c0f8080c00c6540d400900c18011042245100b9003400034001d4501c0030301554400703155203425035511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 358655593 1250 358654343 358654349
    0x16020303060915040f0606080a0c050f09010302040905091c020c1f11060c09040e060402060a0e130e0d1116172b03062321030d0b09010609 61
    0x5800820215065242400303820307421103518002c41000d0600c01001504a481c0c2c07102c5201d40503102c903810441980c026500c1580841c04402c24000c0c0070b80030000815504c944150b80d50046000306900345983d10a505603800f8140c5028100580d0030901e040c50758803401e100a43c15030551240d0b02c255064404960308200210141045121a00f0031110041e407620000d560403c1040f600001c00000034104100da0160741031003d560f544103024024402580e0087e9054040380c1e2100d41880016110001215601070452420620f926030400019034100c4254041000031810868169030b4000041101c00c211040c0d81c4542c0e00d008180e5500944131845a010130541c420305c07401c00c00403090f0f00d030b6440300080f007001d0a580d8400c0100141141203110710f5a1a5210310f000308080061039003602c40c84010301210110301c1070b48502501c0c000c9400c5c0800c84102e00031144c440202e800742e0420b5551780d21101c0020180c1e522a80906400d4000704032000aa610441c0001c00004115015072414000d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 358656843 1250 358655593 358655597
    0x122c01060f0e01060f0c0f0605010806071805040b04090c030503090f0904110f0604050316051305060306040807020f13050406050604020a050f1303050a050609120a05090d050709020c07090516 84
    0x10741d83c43c02070117075124160180d07640300788070f54800b908000804c1c07182d0080c4200c0c46000c1c0002c40e03505001c0c401d841e0420003013040b800c4c00501e0400158035280c1c0c1d0f00382d800b16038040300c0c0840c450306000013083c0038002041000304000e074a02c40103c20031002002602c866442503c0304401851504200130400c2d20507640a0304000b50410303041c50a080c0910340c405c2000019051074613080e61100071a10700340d02c54400e000b1002d15407206018030f20701024610907100c0100005c4c4043c0c202034000940325100900300502d1502c00142e50021522070084c00a1200030041210300c01c04503404080014000c110b80c2243c0c00381c500000a1030a207030620940d00b07803003070541c0d859060036600b5403025201c0d4081e0b02441c11050303404c0000000200c08200c9509164480c0d1b01900d52402c101031240c1c40c003505440c58864a030014072105c65115801025200c2e4100d04031200356190007a400c040e82007031260b81107080c00d2400012050108000018680103c40c0000b90410a5585095400350000107680d05030300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 358658093 1250 358656843 358656869
    0xf110a08040e04021516061b0215040309090507080103020102250b1c05070e030f010b0f01050a210b0f040621021f1d0303090907122c01060f 62
    0x100c0031440102c29030003840138000f522100c001c801030345c4440c1c00030040700050780901100c03034042054030b004041480004100307002c906900b400d4065101d00260b2200b81d030044105002605051140407031400400d1045c030100309600304201d0090101009020503405845090001d41141e6246040c41c1e841480945d64000c0903400d140f4002040c1e070203c00f104400e9049030040d003a1048140c82651300541845d2200001f013542c2c10285070600980c08527505069140c881c00000070f44a0311b6848881100901e0000c1e500d003440d902c00c0e150291540c0c0c0282e01498640301c804002c050039440302000c0380044500212520303c03a0104020b4440b80d018120104a040f1081255a00003600b55401144001d00000a18060118081e003607005072418a001a007580710003001512a2440d0381024070b4280c02461410082074042088140058001000c20140e86004c2007003c135a81c2c0900749051030794031405800804681d51654081c80c0001340c50195180a00020741c0240003006081180d5442d0340c010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 358659343 1250 358658093 358658099
    0xf0d03050a060e100302150f091c0b0906071404050114070602040302100305040c050a051011012403110604081b01030906050108030703030b0111150915070f110a0804 73
    0x6018203409051580015211040400ca905500360032910500084030720340402131660040021783d0840003c4040041ca04000f017204002da450f0865000385030641c3c000000b2150000c0202e03d40b021210302030581005002030005820703021610f180112500ea95200486220a1032070135030b44664812a80401d1340400389810744250f04002d000c02074001c0d0b000509082d0342e03402007545c0510004d20f010002c1d948004010420601060160240106451003101c8904100201f18500c82481d02942808507007414000e240c0001d41003508012101c030798a42d05040f00c8100140155840d000c101ca40030340c04044c2d80d807142802d2094030700319503082c0d008200048103800400e80120480c01414109521042c04402148441c06507034003d00c2604011a600c1c142814024101c440154106041289419142c40c0b43e150000b6850040d40719040f03c480140c40305261075103004914a1381c01c0302c440400c803c0044a80c1c06c040303030400385500c13170300c540c640141040d00c01070b1142485200244185030070312042c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 358660593 1250 358659343 358659347
    0xa020d0806010c02090c210414010c080c0c0703151512050c010c0311030a1e0804022409030d020705011d0108010b2b0f06050607080403060c17070807110f0d 69
    0x103410280c0a24070314600358440c090400840d8a903247d1412100058003803100b04021090030100401c0d0060003000800307000d0000030040709010f00602c40410020034000407102d03052011400460b48141e035001c120f1000f80c043e102070700545212410300210a500040c0a511b01400500301c1a031000240110202401c01900c1c40d0f089042c1c1502001008103c032001f02c4010802402541c01c03035103030403484d401c8950b01000303103a01000c0c210302001102424000181c80e40740c0d0b80000540c00307500100b2210034945ea018814020740c0e025035494071402203101062038010491000b41c8600784d0303980d0390b8400640d01c10f1584208485045002408410040000c4586640135045800407044c00552081001d0032a640300c69024501940482c4e4601280310100b0352031040000901080c0c4805041c58074540321481140034901c030180c032903522500794801641c41500c00c0e80d1307508c800200c001500d08090300010b1030120111203400101c2e00342210352800410015000307001803581c0b801804000360744c1c40c0c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 358661843 1250 358660593 358660609
    0x61d0904030503070c0b1e0702030a0f0f0201020708070b041703010b0702010807030b030f100507020705030a06090320060108070b070f0f05030f0406020c0a05060c030a030513170a020d0806010c02 86
    0x404100249614488001001b074540c05000b03801580c12400c901081807100b82404502034106410f6501c200301d401d640c84c1c1c0080e41c2c0e4464401d9810300160f10300d41d01c1d4013680a40b166020060891400060402c100800d1030001402207000348440c8440355030800d0031000c01e101c203020700d405d400b4081c4044001503210386685a4000210700d000300b0b01c0105c140c0404d241001d0004d42540a410901113841410303507a10032546d0001c103600c01000f07000d180c2400300740c6950380c00b00e0141400c0d45440b0503d044c940900030741d8100351030000003100e601a500c11204d450309420700a150032801100c00000d5042071440c26180540d070081e08202c202d022039036440004128a40044480e07010a204091305040000060401000303150082c00000b01d00404001007254150811031203200e050121a0a1100000030f541001219040018003a11001c00c02000007121b4540144039040c2c4440941c00300510b00b001c0c0c010aa0680c00315440e403c1889001c0e10b03190b00c00c0310054005000c00c0d90a01c05454203842c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 358663093 1250 358661843 358661851
    0x1009020909011e0509010e040311011109010309080c060403180501030506090a090c05061c06051206180c10210608032502030d02010e061f18021b07061d0904030503 72
    0x100e98070700c0f5980d89001c11440b031002d034000b4040d8201079080200f0f0681084000b03060404543c020405225081464407160144020b01810903a4502d180020804110202c41d000f03100101100c00038905490000c1070031400540004012800a100240950080c010103010307100040480c20701d5503c50101c03d005002000040e1900c0308a12400101c5880300c0b0010f1881d4401d081c012245000003581c1b01c010303565158041805030b45451421105c031040802d045810001c540e0702440c4604025510303074a400024902c540d8050441c040c5081ca07640c20071121003000303e46074810500c4d50300744c0721060308442d1144210720080c0c10400600580005c0c81d0031400007a5103002e150304540d0f1031500403a1520018010100160795545100c060b28003081052991000591864a0150085926179214894103100d50022f01700000480d404c5029907805071080300758407000103410749111031802691107229100d95400306000c40c80ca00801000e201c0407102c13420018080c030380c080e11190b030100ca155000074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 358664343 1250 358663093 358663139
    0x6060503010b091f03051602030306150903160b040e0a15270608030702011707020a02040c050405060d050105130b01021906060305030d0f050a0902030a020108040203120d05100902090901 82
    0x7542c4c01e0f100300c20180c803424071071000d960000b154a00041c401c100d0306021030020007554030500820003d86c0c2d443c0034114212038210200381d00d451500000c245001494554804034009800700410f0858014001c0c004031040c1c160072010344d4890000e0002201c0b0042d40b00d4010703200780384091002ca000382252002d4445960308180003101202d00310003c0b94130f00c1d000321210360000901c9406543c2d0000b80c010428800107800c01c0e150801d400e01942d22440070000034025078682200015603030188080d103005000152946a0b2550443c0d0b248005107024091240300300c40c0110442484030240c407172180780d154181c000301000c19400700b00d0000b00d8241340044444c50703112034020002803c140080e08080a1003100410100308650464041d25401403141040d9840c4c0344065015070380010b08400c8164080c02c0819407502c55001281c104206548940401c01700041c00d4130130000030398062441030280302c40705281c9070307151035204060b4030a5803982c5500880e000d00510220220702ca242030402c40c0e01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 358665593 1250 358664343 358664359
    0x1b08120702120f0c07090213090b010509060304060516180e06060702180108010b0108060a030b04021305100f0e28090501110a031802091306090c14010f0306060503010b09 75
    0x1d80120b040d558005041100481d2000c01c480800c500e080203a00e000e003a01140c15403c04000030220026414544550598207071a20600b01c0280d010701d04860700414082c0c405603503880d00341000f0010340b00a80742c01c0c1c00400184012400a0b1044850940d949482100d4a003881c0c07901d0388000548402074a0581c0c80081000036800594900c03d03000410000c000f4180380961500302e002d030844084100700d44c1800200c004020712683c40981c290140e0703a119070100308580302e50010511884070000d0500160b45804140041008102c40e05012183d041181030007042d285d4110398101c40c016681c3c0b05261b40c446c4003c01c4101c15000b00c4080001c140c03000014214a0340c0c0340e450946401403441794a03000000f0798500d240f5410f0054407c010350f04c1203043c0b41405558040b030204c1030014407480128a06401303140811110750840c1c10306a8101a40103841b0781c680103c0c40c0701c500b405000ea8046641c0b400c00140c1a4001d004910484090743c0b40c4c5419603103004406202e07684040d001940c46021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 358666843 1250 358665593 358665613
    0x70c030e060a020d02060c0a05090607060906060b0c0f1f050415060e0a060602010902010c020915030303090c04050f0108120f04031a01031103010605130b040603140a02011b08120702 80
    0x4000203400c0d030712003c1d40240342003401c0f000c001e820700d000503081c00c2440f00c00f00050711145030071038116440c1030300a80700c25030b580c1c1079428018020000c16400800381030518000155000041c0040c0912103845010744070703a40076044000c0c2e540d0340700041504c5a811840c9520b21035000d1648034541c86401915554580c0703250222034012680283c0011074441020303800c1c046003500b00d1103000c002d407103c0d00003003000082e6900060562243d103100284501d00100005001507080d040c02c004c00301003e02203c0d02ca0901c0d510740e94803403070302c90302d0240544d00e00030002d0000250600000d0494800d02c026200213003d090315060150b11803044000014010003000002900c500d003004450311503000c4070700c5554194507220a2040506290501c244c1c103100040c401607039042c054075800b0381004000100b100115022401a0900380d00140c910710035a4204500c0440100d10312004e94400d0761034121450b140180e00032500a0303050040c0403c81c1c1800350000701250950b00301d130050100d004440c00001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 358668093 1250 358666843 358666849
    0x90e09190308010f050d080712050409090f020f0f0d150219080603102306040e01050c1b1c120623150903061303030f0c031407020106030803070c030e 66
    0x100380d440c101c0c0059a1000100300011426a002015003001ca6000348403e5040e10b400360705000d211006403e5021a8001c40007181c042d104650042600c40c90520244059083c5210a0b80d580b15090340215135a0103c41d00d107190020610001d000018505440c066071a00e40d2800942003500b426141b0303908100502d6030900c4059240855203040c1d0310701d401482d0107014142421f01c1d24000f848202c1c03d084c02a45000f400303400030031940c1c00400825403d40e442c0ca0010b07020344032581c10450a5442e11040c41070703207240c1600400080d101d14420409220900e0107044e0703140124503940c101c0e05044118945c0705480f40b6080c1c404018126004502d4035200c81c1c424443c003402c4100d00c000204c5100c40c410309410100c0c81c0f101292079036003215092500340c60109840c1c1000401e41e408407620400454100350007680a4032040089e0a0100100c2c01c180c0c0000c2d00422545d204c245036010000b0015402c01c2c41402a0720a51790300820481c1991074414064400e274819090031028070032258184004ca807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 358669343 1250 358668093 358668133
    0x1050a0312020c220b030610050111160602012a020706121407030f0b01170103020d0c03081303020a0e09070506090406081c090518010b031503011d010e0706090e09 72
    0x8924031486098240b030b1024041154020f504c0385e03000740c000d00200601142c09503028011200b0a0a141c2c2180d840d6110441c02c1880c2e0104020324148112800318110341d0550001c080c01b07204c480f024180125240c1c100c000c100d030101d4150010303884200d0070b002c0c2d03610840711382114107180280418502820400c040e89400700300d940c00700081d6100355100c1910014050142103079820b080448482000b0358030117950500500001e800354802c104000104800002c50b4002160016240c94582d005824100300113415840241c2c801d0050340e202240c8103002c2500280207803070080040070a5440c01042c450a07801c003ca40c1a0f00c15510080002c034010140304000b00c008403a01c00b03000500403490007a00c01c1c81680c11250107441450030642814103403280060540300000101038682e07580420745502804166900790305542441e01c00950b4071960b1091000c5203d03000b00030300c000c141c80f01c911a034402c20751040400007884804100120410015460f402c81d001c5400d4179140e4650080440a00d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 358670593 1250 358669343 358669369
    0x60606040308180d140c04050a0905060f04020316030308070905010305010b030619050d030305100b120a050a02070606080a02030f060601050717121e10150e0109030b0c040e0105040501050a0312020c 87
    0x2e030860441b000b01454284141680502c00c0f00c0d00b00000303052625a41d0307880a0040403524540a06004501599030800c000c40044200e40981d04400b40c40340781c0280b50980c03c1d601e03240400e001030741c04100c0758024001d49050703030030602c4c1840c159960402001008182892031440c0740389a0702e008100b5880f5401280f001038001c0e10045028100310b6200b0717070020021340c000c000d4501c090041a151003524000a40c00c03008031080410aa262084940f00034444c4240003801d840c9442400034070b9442c0030500b080100c2c021002d440007000e03146030543d150341040300c26600141041010781e000406140f08030b1106401d200c089401e05569450141040c442071b1600d858142142000c0280b003d202940c0560046403001c203410b41d02d10f005203100348000e000540e10f040c8405900c038807000f64031988040000319040404c074011307404d0a0802c11140da10900031401001c2107100040741506250007500d0413a01e02500e110f00207031139a180d1a4002c080201e150741140584154080c1c60b81d1451031031110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 358671843 1250 358670593 358670633
    0x21c02130f1a04140403121113051008040b06150c0d0806120a0210030207020409020d060b040e0f0606120304181d0619180203011d060606040308180d 66
    0x18a1030b02a40c620500351181414910650a0000d4440c000e115121034640282c1e1500b044071664079040d46d41e8001d0318403e04c0c48141018041030403001c01c2c105140c2c0c1003c4401c25950010381054079001100e80c420111000342030503040c8004a48981040d100940c030507035121055034200503007000ca00c2e00300944202c2c0700d80003d840350140b184610f4040c2400180494450041c070000005501094902c241810780c5424140c2c003051080a54a89410038245242c1c01030208103881560301d0150010035002907458002c5240c810350020b80d007400101d50380161104030003041c460f80c0c0e280400c450011440004030361800188000a440640d1402c000e04095032441c2c0170911222607040c00c40c0c48100c21007800302d00d52080c400d001c042c001040341ca207c2c0000c00d08001c104c0000c1d426008860418204000350150700e4010540c00150002080b050410900c0042c0c4085488020400085012300d02018103052020400344003c841e500804071131104001d8071940300b04500340c5600340494403003810031074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 358673093 1250 358671843 358671851
    0x609042c03120601030c14030403021e0309030604020d0302010608060405030c0d05250201050427050a050601120513080406030c030c0516030e04141f06050304021c02130f 75
    0x689140800e52a1840001a0000310300300b40c1d10580d1010705003405000c980c10f040d924070f200300b000e41c400c010b44413136105a820441e0f0785c0c0c01d0500d0000d643d04010040e03e109800e0395040c00c18401e03808803c4800d41907000707004080c161903603002c00814181c0c12030202d05540d0784150000c0c9000050007981d100700d0080c40a0350325507400c15840d509000d2200081c0c03080007010480e815800c003500b441e24855000401401c5000e8100703100680d070503c615042450400b105122010550368904030050710020041c0c0140101e4a40d240c1a1054810a5545502040e005c00c84c04a00010075400f8603440703407003541c0c00d6108041e41d0703e484205901542165000030740b0380940302c600b80e8240c06030200c0030304540752003441c14882d05111120b017101c200c2c3c01410070840144004280e502d9801210f1076039810444411f40d4104034006800562106070003140401e041c2100141031400340c4150380c41035401501450403124010003416400c90050300880e4441c84210001d220100c861288603030300c00344114006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 358674343 1250 358673093 358673141
    0x20702090c07061b171b03101701020408031b01090b0c03061f1211121315090305031b070b040506101a0a030209031207150506060909060609060904 65
    0xa400c0c1d61649000301c0d9440094064442090b83c07288443c021080900031181175902e6004405031581401038509035101004000c1c0b02117151074074040000c550f03200c00d904040040d10746007142070703016501c264003e035042400074032444022098202c906512420001500c1589580c9088552000b5a9490f50880c2d01100b04145420704090b405688800b0b641d00400e254000b4900030035101c1009040440b8548802078400142850303401d039104004942c00300b11251401115940704503500c44020342c2d41c0480680200c6580089101c1d100390710b901039440302e1031030780d80303512000c40b4540a800355084c1c800208420008030f400c403219207005520800280c00e0030700306103c88002c0c01e84650032400e0044030b440245040303415440b0464019010500f030150b25003c007513000900305081ca22a0302114100020040100000e84c03c00c080241101d040401c42d0b6100c12050041c1801100368190708602100b010540301c0c1f502001510184000401c0a850540c9050105007a100000308094080b40340084007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 358675593 1250 358674343 358674353
    0xd0317010b180d0b010302010e0d0b0108030d050f150f0a1d040b07020d020c09091c17070c0f110a12060608070915090506150423010906020a03030f020702090c07 71
    0x5940542421961008841e01c0360300c1e80b104c81e030b1042c440281809903401e45544070352540343c011070700150813400310340345036954140117610781d840049080b4200e4604000902640b0850750345602450b681e00383e150040c2101410700c079035111a0740c40703103504c0310b00e084c4005a030300001041c581c0088101a0022160306040c0742010a05102420420079074010301300f94100140d0018038418110030840d40d035051500c600102c64205801c1044450388403090791801c0b40c4c9190018541b9800c0700c0400400c0000381d66051084130b00410321003000b0018900c0c0100100800c0c2c406c1d40701c5465400003821030101607a60082001601da0201c001c441a54860008000d0f18034144920002001140018411900703e15090442050301d4011044c4460b5204041080c0e074962a00340e08035002d1305c03002c2d9962140c0380c0c0d401c001c4140d0716507840101e540448500030b4840d4410300c2d5030303002c0780c4c80b03034008007010342c0304e5034050700a410240c0d1140d4a0990921404026a0399411214025111030005075603400281c101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 358676843 1250 358675593 358675627
    0x3030b01031803030b0a0b030702030703080105010f0f0804052d0601081603080304030e0d080414121209220504122c060c0604060605120106140d0317010b 68
    0x91410315141c030210036090300701841041410755043c500000c0c0000c03120000f50350f407941030300990300d400e402208228270181c00000800c7d0f030394060384030a03860780c0c0d0320b42c01125421080b14a210000e1401ca4907003860358080d405468015101e1020384000005100d0a00a03090400140d400d0302c1003180c01d40c200302002402842e01600c2c09001605038104248036032441d2410b60f102c0200b01c404004000b60034940300f80210241000c0003000c41d40c010066080c04181c0b07810034001c0b041d01107080c00b00501107161400c001005c10746100050007151a055000c50140d401890b074258000b16003104c0101d8060702c18111002d00000203500082c42d09040c10144900051000b02c8014420880840300140210703540318000c0e12603801e02e0500041c0070300003058580c010052411401e1043c0e50a1000f0010300e500008240c0c0c01c00d46080c6603850358881c805090719424410b131503006001d08000f40c051300384241d80048050084c20103400002030703500c440305944000d0307002c600c40c01c41c00701d920f18094514081d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 358678093 1250 358676843 358676861
    0xa09090902150c15040b061e03030919180203010e1602060c0a0201062c0708100302090a0f020c010515010e0607170403020a0303030b0301110909240406082d0a0308040c030b010902070303 82
    0x80351030234000884011903524031400426500c0346100900002e12404214007520150861310007824000305070b10742c20340c081d40084c05840200000980095900c0a250003e000109080d41c001c21090b01e0f142e0005a00d0b5100d211008115502c0d02800704103001d100c000100351440c0c00c440381c0594107205220307600e00180502540208000380c002d000c0301c40d254000c00415250111160b20068aa0500c0400103080300702c0d400031880d00210301c4000070003042d809284070f8100c50030034007049802c0b407004582e10791700307404a280d02c9003050055034007040004000b80c40002c1180ca0301d5140c65140d40014100544582c0228000b0307440b000000c1c510304003802056919252641c1e0745040a901500180503c1402403250221010b1281d80e081c09080648a0145103000540100300440d00c03800c1150300c0700d110300083d50b10500505101402e985880c440078410085090240c80d80398056a01154906c00282041d01c007851014404808601102c40581c000c00c9000401a074070915440c0141c20368002074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 358679343 1250 358678093 358678129
    0x6150b0306091308120a0b120109030914130506030f12030403030e0303010e1519060c170c0601050d081909060f03050403020c010c06020d060603020a09090902150c15040b06 76
    0x201c902d800944c0d20401d8525011512040101079543c203032000e0020400b0800503684402c07801d0045e100c400065000d60405030180e5500d40440b80c0305c4242e101c084507042280e6802203500c103110312a030003071540156000321000303003500c180100012819107450602d008014400c0f00000500007050b81503c6400b2042450b0800f8500350b615160402c500070800426821900000703800d00b454a43c3e0380700c821600c108130b803480144030b2a284d000c001c0c6249151001103507a078240d00b9080740044a0b0740c0a039401030380400c0041c19503a0070242440f40cae13180800030884000b2020302c0320f45030a602000b5850204070311a69840400f03450f140f002808510800319950030305203440c00b8007000c00e9000c0707a013907102c400a080440c0000250721b02000244200b130701c8a6410351410502013401a4103800406541410390b40c1c084020f0f8643e0700603403c0380c0c0c011030001c1d801400054941c400054072009002c4d0100000240c41100e20441c21868084d001182c0032140d891241d01000306603d09099085c0005d0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 358680593 1250 358679343 358679371
    0x50d11060106030e10320117010612081c020408060f01060f0e10020712060506150c03030f1b07050c01110d0813050f03041413050403050901080406150b030609 70
    0xc691803e49624016031207044646d1101d00d800d101e000d00d0742e0241420110a144e2040303801c4542c690051003207081c0280c28090440c1505442514014080c0d2400c0e40e400301d0b4140400d180ca541c40c038000341d00c075003003401c038840e18014030f4084035519201603c014259803000d40190b15003221b00780300c20342d01604804103010100d111040280e501c00041114a24103417410101c01c2c4880c01c050386400c8141c4e00c4200d8a810603501001000304541000c1d014a07000e96006059003489840c08282e03014284180c40b00e640148000780340c040c0070300c90017900800783c0b581d40000300b804400d102c102e40d070007800103036015403018003130244e0355900c0803200d608031964030094040e0082824006010090103070401004400c02030070001408400d11108980c6440074048980d52075407001507980f01111241800d20850360640110f0f00d804080c01910302c03599056564a00d490600801580d0a0b00090300559030941c4d80e01002036a8600905188050000c01d00b01c1622458004200a041d17880240560400400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 358681843 1250 358680593 358680611
    0x210090f020906010210020c0f0c01080702060c090a0f0803070b1b0901030e030d0203070801060f08161b0602041e05030309090112060222051810061b050d1106010603 73
    0x910820310303222560440e201d8589403280d0004038682690031003401c3c4444d200040790b8550042c00601040040007174070503241d182c107040e8010b48003030b030044030744030056085500094910150b48009003a0b0410003001d44400c26101c1c1108260410290001e1900f54000900e010900500300b02c82075003d4000405042d11f85550803a0813001d01800e07085506054403003410001080c0180140c94017009803c4046480389001c01005049040c00c0c42040040303106070b0f42e542d100390300c28440544900403020ba00c4220083c4903a040394404110740d015070066020780c1203a000103d0500041009218180e40b40070003922011065120845035401a4441e9100700141c00f4262200e40e680e5044490900422160003085c0c06c01c407001c0d114200c00459912000d407400034000c07041c440c0c104140d440a6a4020204900006404900c07109544406107050301c98800c1203454459400c0d080c090076590403c0c1400c03000d9507201ca19210380c0310280000310b142982d459900c139600700a820f0051540b0310f010320420744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 358683093 1250 358681843 358681853
    0x5090f030a05070501090209040f031d0f0d02010512070e03070803180d0f050706020a033e0f0319180e0112080c06090a030f030e071e05090106030c021009 68
    0x1007100314020074044041004002c0c070400f98011085d00350050590a62841d0501d010349544400000c01c03004503801c1145d9010011602e1900d26400c5d4015061011002c2842e04115002205490490400c04100100440e81c11000e10040c010b050680301d60705901c1c0c605041508150321904501015030041c03104103d03660940710305284650003034400318086580ca00b4004001c41c0391607000741061041040019906500099840e1002d00a6407002c80014105103202d01030310040108800490107881c000c0c0c094518404890003170603000040361030310446c82448606641000c02d000c1804000d1b11132503855603801c04101a1031101c513182c6105d00740c0c20140005184c00341030046404815800d6000300c10003000780200d40181031220201d07030042c502031044980d14a03000381c00320002521032903180307540c9019000304c150100001001d803064508240c0e0180d207040e4090b081d44070b141185400054075803620000503000c2c051039540895030111040c00a443c0c4103102d400d0105c203624082044000c18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 358684343 1250 358683093 358683097
    0x8030703090e1302270a0203010305060447060904050706030b0609040608061905010b090f060409051f1a0403020402070c26160501050319060f030609050105090f03 72
    0x807009604528291180e90304a02d80ca41c0c083c1c00290030688a250301c0401c440b500a40034190380300340a00c01041c0d61610125401e900003071100404a6120501140c0050000d880c003a400c440c0441c031342030911401008840c1180301f014404e602074030341d0084000f1450740412105600070401d076429089400e00d5524144c0c0d4a0040c400ca40c02c141e0354a61282d181c0e640c5c2001c83d031000000401c188009078036541c4882d1150810350f0050107501e0f0314450b107154041e203401010b040b01c43c000d992504080200050110304914000d000e50b200d41b081001055404182c81036174002d0541c58000d81c143d40990700008803116594000500d41c0a1111045603000d03450012038080e039505460241e1240143d141603158079140350010820101c41550303420421242ca5200c600903200101140c4d52000b00b040c4404800188c1d0141c1303070000d0003c2000412a040c070340c0740c81424046965000661a541c0c40f0001e020402c107400880b5000d03151054034040c010240078440c1c20201d2540581541540880312590328 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 358685593 1250 358684343 358684349
    0x9041a0a0603031b03200726010c020a0c06030c031512020108090a21021e100605010c080307141308061602010e0a02130605040f020904050717010342060803070309 72
    0x3100746c1949045501d010f001c0d0000400001c1404041401c01600b0b801b40c1075415501e00c050341d843c00b1802011103100144d0340c0c0249401c850b59042850820300200e01a010000c030140034551203510b518081d0912801d05401080c0002140120300900d2000510303010000c1d0250140e40d21044500e40840d00c162441200c0510b200003400c1c40e94585802070341803840580001001c48105404c0144454000c03d8240703074040300c14003c000e00c81d1658010341c0e101c0c002600182011100340300081c2d642d401440f40b045c07468406403665050008140403096143c100d6000161660410024000101d400c0c1c1141c0d0781707180441c0000e200345c10300442841c0c1e07100008100a4424282c0710494101c6129641c0540d0140070050801d018525425010364040e50007407038024041c910700b600188403544500c0040c501075017405400c4140380d1131511201e007000f541c01048101529884400205221955244016107581345c014628040c14195080c080b500700c0c0c0c1c000c4c22107820412410700082e502c20901c0c016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 358686843 1250 358685593 358685627
    0x30b0a0f0905250c0203190302060f10080706090e0105060a020d08071e0e09150108040f031b0f14070506070201080405010603020a1e210209041a0a0603031b03 70
    0x30ba955004903403810041c0850403081c01d0b40036010b10005071036211503d090309500a03400c45e007400000c02010b4441d42c40380340018005800120105501e109001141030300f141041140c103406940b26042e036406e020040d801207010444000342009980881e8129500400c0e04544a5040407240c8201a440b20384088440007040105e500080d4164007032501c6141d0074807150340c0c1e680c030aa180c2da8050000754074900f64605c1846254006100d0106075130761140d4944040e5500d01e05920b80f59136119001d0742e00541141804030911506422039a400f030401c01d410700a0804640317031001030820303602c0604d0b100b42c0040603400851050100b0b0b1541401c89000030703420b1a043c111542c503400c0460040200b904001e50141e028440003c1c614800f80032800c1c41000c01e00800562583c485c1c00c9000203032400700400e81036881c541200c0c050f01c2c02801d03650b4010300030442c0114281d9414030749000c00d40d0841d0034180295803070200b401415800000c1000035140c03040ea03414015002e0710040c0000c83d09030300140c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 358688093 1250 358686843 358686851
    0x1020102090d2a090207031403060a06110f031303030e030f1f15090b100c050d050d0b0411040f0902030103020612130803131707020a180e120901030b0a0f09 69
    0x201041ca01c424541e8850380360110103d41c182c40e2040c03140a98480c420540c000f512180b01128180c104000703c0340600c8006002020451070000150f030900c0d08001d40d11494000c80080c29440c0c00d060000b27011000c50150440096801d5140203400303c80d04509042c0a80d1140800c01c130a8240020042c47d503c1083c0c071041003100550343d51f035001e0040841e140d02111500c040001d40c00f5000d0b004401c02031021102034a24140184003200c3c01d50709804090201da01000a0038981400f5000808030800c0000000c1030215600022506940c490009003c1c601d5001404210b0b040c1000040c0001d0001900c041d407465166400203a003030300035030103024184185100451003504c400301c0c1ca5803200c3e0340b040406440785415000343e51443c003c5001601c21301e2052a140034004208c3c82150002940204119041800e0040020075800b05403406034000780d85e01d0903106040310401c5481c02d80b4070480d04855a0b800b060000409a8a2610390607008503200303c014411500d03551f409030290303206104002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 358689343 1250 358688093 358688123
    0x21e030706060e01050f0d0506071817250f051009030506070806030c0418140717030d06050406080a1b0e0c03070f0e180402030f150f0601020102090d 66
    0x190951148840082581d4a02000003c002c6844412141200c0c002c5901d454240c02440504c842424400402002900070310001103550b40105643d02200c905e02c14400308054442517806000740c2c0c0300700194210fa003e61003d18085c41c0b0350030140040c80314424010066440c00255100700001d81c0981c17840380318007404441c0c000c0d1152001100868011045400d241042c0e0000340ca0b6810070b5540500901404240c2d00803418a4000d0b40c44c1c200400d0010500c5030f5050301c501c96840c0803580c0e80a5140181e90780014030304903c24a02c6441103803000035640c2c9844140007071040b608554030250066062800030400c0708408250391050781d401c10780f015401c00001140c009076071181c0c1c10a41001007507505000d02103002402035031091085807145072060304540019110052892040d59114a14805200080780301c4d44a1903006440502242c030a00f0090a00b2424810070f4039034003810030201000c0119103511380a0260b08070b042800218a030200c0310010a4079120a22009011260900000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 358690593 1250 358689343 358689403
    0x4050f010503040f06020310080d03050c040e061801180b0409080304030c170a03020403050f120f070201030204170607020d0c020102060a0c0519120b090114010f050706020c0a020a090c02 82
    0x791304103a910407021942c80c685800300c03079003800c00e50056054038415082c002c5660f502911899005100200f40b140c00c09151900e030246881e002044560400f0101c3e0508034500f402d9548180682482920850248030091040c4100c518504446200303600b0300c4100004181d144003242d4100b80c0616110400c040281000c1301610700f0201103170f103480000201404600d505a0140c0240c0e80301d030050314081545141ca00b5a210700000051103808000c0050180403814400109810341c4181005802e0039541e07405091400d00b2400034500c181c000c0b038100b000303445e410b2201c0c3c4800e40250a21068800c0380e85c000039501c910080243c116203030b85080301a80d06028900ba00d503031003c80c200c2c0104503036507440000e001d003103103490458200d401e00d0110388031868600c0003181030310b01c07500b0340c600e0020f03414004403506e5404540346014030a0400406020942c070780000c14031660020002c1a040ca400c4c8148035801842e54481c3e5101441d0038400c2d1100356000c908402e0411b242361403462090100b00e42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 358691843 1250 358690593 358690613
    0x1060f090819020a0b0a08012606010311030708030f030c0a09150915050403050316031404030609032c0409030203130602060f130305030703092105030f0c04050f01050304 75
    0x8110641d1040316014a0042202c22100000610030740e880e052096848513030807024054034184001044c400c90040c406c51020348011503684650640e442440b01000d180300c0c1c00d09a080e00300303881b45c0e00d04074904071036803d040222000070000040250f10705940d102d0700c00c4160001404200d100100000c0b0756041c14420300409000d0125200c3d00d10405c400c072440a00220081c0c8503025041c071281d25940819402801074170100ca800401451501c0f0400c0e074240045840c8003400ca09000f80d1001c802604500b03d400340019500c80c1c4000540a55a0b0401030880381d40c05e802840140c000c2c006a003c0c100552031103400468080c4c074007113411b0040d49003c1e401e5014880e51740a00c24007410700000d1003940028420b010b4040d46602c911513803501c44e109201e82c02c6140010700071910800c0881c0180b072180c0c1c840110180100e1620102100408010064a18598440000403008003e00010144800207213401176810b46100c0c4c1f5040c070301030120b01031881070058035040c410301000050a110740441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 358693093 1250 358691843 358691849
    0x103060e070306020a02010f0509060702070b0c030d0c020a0318050607020906040f0c022b020706140c0304030809010210060e0c160204060305070f0e07080a1a1905011202030f01060f09 81
    0x7025900c90b4001c205c028020303c45a01907407003480c00c00000c110400e0010841030300420b0654094410642494200000381e0300a1184201a01c003c000d036603010a001c3c8288500e011990340038000c00c0c3c40d0350400401740300b00140710311101104080d08010703541c0e40301c0482e000c9950641d01d000207035403068002030080071030400040c1d05500305034840200c00c1c0c1c0454117582603121596444001080305040d40000c400c8110200090b901c03000c3c040c0b1903d4000c0355683c18030b1029894641c50300d8a4050b0a83c2107800a5100321200c6001140580c9a50b0b0180505901031a045400b041910b2401d490340c1c0e03c4000251890080c00c1d40000e20201d0746849005500c50690060070030b2000e10795034600303140d80e422148120004411820408902c1e90b10410b04240580b415035110b10341504e81165490003451406941c0108450303407486c0d9501c5403248100008001c900d00c0800000c42c0c0307040c0c009080d0311144020052260b10410400a00d000590351607810340c3c90a192462590021f00810b03181001c4c650 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 358694343 1250 358693093 358693103
    0x2030f0d030b04060f050f19081014070e0307060f03020708040f0e01151d0612070e1003060b1206040e06010f090c111c021609050603150601080103060e0703 69
    0x40c040c40310a4140d00b100d5100312040e01e04010156070781244a802d4146409929486185a070074541d181c6810b6000082424461014001aa581c0c054941c60181000400e030342071520745e10f810050584411031654000014100400c03410703003240003e5200d1809015240c14840c03450001c80e5818403a40c1510281940044855a2a40c846152100180b075501c01c140d02d001c880d0300041220043e07004824800c00780c1741c45064504603034145600710082401c0541d81c04c90380a11445910b94600904c40f03018591341c0c1c4622100701c648206005109168943da030341858140241003115807200c4003211100c0a80b1041c840c0142c0f584000140640100910140140315030800401d600c05581c0c590b070200d5104003420085100001019a40c03010006140c0341382d0340001d1007040301c0ca650f401c20b4040014107881030703480a0703224a8960824243c0340c0c00c030010030390741c800c10001542420000c840c0101e08205500c00240303025400242141014000144080d48880341034504900400c140c0b00650307480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 358695593 1250 358694343 358694353
    0xd08070f05010e0304080c030d02010902060304081602040c0e031203060310020d020c0114101d0c030901090204050115141e0f0f0f2106090109180209070f020706050309100902030f 79
    0x10081b6641e03549204803103e1081c05000f801c5141c81c0d00500c00d080b00c09034040c0007642507540c0c5440d084025004018280179400c0b4010f404001a600c40c86200104002600c0e02503c003800e0609061402e40000d0912034400f40420601c00d40c0c0d03800058000009510a5000d40e07120b80040140020b03028890039081c07590300b800c407400a840b429014080c4960398200030b0300201c1d55502c00b01035542022580c40c000914144001c00c95482254004607809100c0d040040b8900420b0f501003000c6500980c464040c46030300807002581d166002c891519501c1a5800c002d09085103002c0da00141c4640010030b0703014840000c0c07061400160b000581c1e00b001007480d01c50381c440e1040141e1201d00c1e4030060b03801241030728200c0716a054028504040c0d02800c1c000d8030600c0c043c0c1c00e00d1a41c03002443c03400440000c1c80c5070b4060060060703442da08603e1140305070340d981c0b819024504002a2800d41642c22040030f101c400d004020101800089240b084103192a011450405c0ca001090071301d0306011b54400d90340a1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 358696843 1250 358695593 358695599
    0x1219020f12030a11060114011b1b1409041128260a0b0a050a091b0602010506241c05100609080706051b0316060b0f0d08070f05010e0304 60
    0x40b003e032200c100551506403004401020041c3c0741c1c102401a04201c5062680b401455441044000d1086611a108582c00769060300c5044109650011220b4412901101401142ca000a0282c0030300e109a0b181c1c009030929660b0800301903814000c40780141178102602200310131035280e60f02840c4a0f51030701d4000644035080d030241c141c541d01d8020110502e50f05901c1c2004000205c40c04d440b60448198921610350b081c0b54409040003500c02c4188648420020021511904010071b50b22042ca4001614615244000e800c1d01c40c010031840c03007035500b17001c03462700300307521504003003110020325030310356513400d0189081c6c0711001070802d0b030045985060300300141c8100e041c508605440042c4c0380d0020b09680c8119075076558055018400010b80c042c4401d403400e40301590700003924040c882c01e9030b08010b006480c000a01411000680d100b139140d803005d1b42541008105010b103448240c44604d564a203503103d40c1541d11404100508010440300c80f80107006d000e50002400240c8282600c0e958cd603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 358698093 1250 358696843 358696879
    0xd06060509100303091410120e030d050a180b0703050703020f30070207060503061f20060403050f0d0902100f03050c04050109031203110f12061219020f 67
    0x15400220003003112000040742051710701d60300021038507005001c4081f514550000b29031324070641d400e00b0700707081d141c10202040b154140040c2114004501d40020149003801040050b241290000401d03e003030000c510b00428031501c0d030303654040304504005c280c0b0f0303c030944118020311660001c11442040480c1620041000c01e651903404c1a00242c401d4801001b15034109101c50280c5070080541e03c004010011035004034040c0d544014010003525014451000c580c500c4c010380c5c0c0c43c0400003688001400204030005000b218800000e1700144202c2c602903038050024404c900e90348100001c0815507501050340d64108403c8640c1c050981490201d103802c004d882e2002a40300c0e400401d080000041285000314107440455505035110030107113156882c0c11801001f031042d0302003010744464a035003080402030000c000a0b10850f810550b00d102c80c00e82d0300c000042c050f00c23031031040422030b0020414040005405280e202d000f003c40c4085115480007032466a81c1c071003060b4004001c000c0c40e030040702d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 358699343 1250 358698093 358698121
    0x30423090f040b0a0c02190201020703050708031218150a09050a0b090c0405040f0f030909050f07141828032a0305100908090405040609060b03010207030e0d06060509 73
    0x10f840b5040d41c48542d2119070001d416100302c0f8a508005910496140c040321041e45091003030680180182d07012a91603440d09814013409030800704543d440040c600800380341813840788c1d510040300000104160490845ca54540b06040003146128070b041c8007054001c00f050384541d030310a0b480000c9035230501c564a400c1010200842e1382006901488a4401203801c05e405050301c85c80d44041e01c08100d01d4655222000c11151000603070401516820206180301c092080501a80f090703110100c0519240e40d005202240e07104012450b000d00740070301d4180d048440c5062148002c102d030080e0710344c00c0c60200824802610000c071000140e186da000002c0c40b02e40c006480200240829000540da80ca40042030007240d68400240147c2c00707244c0d0212299110b80c049546648203888061910820030700050558000303403020b55a41ea95a0031600070054280318065813254290300a6040c03455079100541442d010b4408580a03081010710301c02000f071141e10202c090000209201928145130741002030b52 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 358700593 1250 358699343 358699351
    0x1110d0c020306072102030c0f0a020a05060c0a050d110c0a2406030f1e02150c010f0c020a11060712050d050c09130209120f030a0806040e030423090f 66
    0x64002c3c04041038003103201700f880d039018115500c84031500d004540c0c2c8440086d80004d000252104045c08035041d164280c1c001880344003c0383d4014544800c407820454280200a05864180b502c1006101592a000030a641020b1002075001030405050f50341c4040a1081440340082c90041c108030070702b00b046508503110b010600007140040400040d84c600100c8045000140c520103c028101c00081e04110641a001c415500c8202804025070b02041c003486842c2c42c11026000701140c4403480d41400d02c0703401601c00c80d050040c40742020b01100030b529044442c0340075100440d4150024142d840c0c5100300c5031070039403004a11070789241740381c402056a004440d403140c88a00344008181000808401d54041d21401404400300c0c07081c02d5034050080d0310070504aa002000c2d0034108100c0c5a05000704c0c5143d00421015503a14016414010140b100041c00f01c0d03c0b5501d4103043c8840d40c00000252401c2d0b036040311045850340c0300a082ca014005030f140440b54071620f80304c100281c008008502c1c50003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 358701843 1250 358700593 358700599
    0x2090c0a1805012c090115030b0103064502090307060c0503042606360303010b0304170a0c12020a0308060402030c0d020d020306010e01020d0203071101110d0c02 71
    0x3031104184511161070101c0c891240040c50500700d00c3c51200034080c0520a984400c0c10f0b440c0d8011408011500c055800d92003054030408110b03400103110f406003d403002d010000d1a04000d95800e201e00e89122000081c1070800d480a090380e01c080141c8001144402e0090468414810392100e28070702010f0362000300c1e594001e0051860014199015004204071207610002442c00c00c0d00304088082c58150031345001c0c020070420031070115080b900b0b0120724021a650980341d024a9007801315030b401101e0480d202513091860303024142030f114002c010b80b8107452900c2d2810b07076241c40707900303201c49000c0c450440c0e503001c7c101c0021003580980e004000c0b510a64130880b40418514400501a0384940918101502180c82d41000800c149455030043d030341f1a520011131790a05412000002c22030304980081c686882d0b000003030104075a0008000381200200748024041001e0804009440307015520008000c040b054144c01032036030051540709810400f6004461003509108002070100446041c2a40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 358703093 1250 358701843 358701857
    0xa060603050601080f07060206070806220b1e060702040b0105220e0a06050906011101330506030c1602010e061204032d0804170403050f0127030c030c02090c0a 70
    0x1c0403005c04601001110420740107440241d0703510000307494244004040c0360340885900700b80402480501900340c508402c606000071046030384424455401c480d9603000310000544201110903603141c20032251032507416079010501c000400c0040c0c440c2d004840b60f105400b00703500e24503815580c02c03254020464508000301c1c4003a440d024031010459145020b0142c0000000c0001030141d40a80710000e1102141d100000c0e010350810500484400c03003203d125500100280260301417070150708004060074088030078911b1030074840714821061050303901206803000225100010b6a000d015418140080545400d9440c42908200f880702d940c1260700b04c4c00700341051000009200c0ba400c999200b6003d401400c907030441d01c45826640010002c008170b900c14244d15001000492480190000714804c9004121901d401000c0d1800d50707051071103800201a041c40002283c541503a002000c2c1901418404030b60b81c214242160b480304000d201a400020b0501070040d14000000100404d22140d034540b8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 358704343 1250 358703093 358703113
    0x40308060103151403100f0218030d08040201080a020c120306041a0a09090507090e010b012a0807050f15090f030345160605070f0305030601020a06060305060108 71
    0x1604a80f0302010410142c1e04049041c0811812140c0038030492900804440e200344506644c0400e48410040e510f12064011441320003c4a80d001004d0746002e0840284c5806405003170020301d0039500070030181c100400b4402041ca45400760b41241c80c20030304041950740c4c0c1d005510030340340160302c02e555881c052841d110032281010741d01e8903202c440a81c0140340025251030400c6c2100900100c103000e0300c0310302511500188a0f200c0340310f21180305100b4000868129020b10000d08441140f02c2d0080004640b079401c401c90841144212504e0356109801e580c4803034213401e0241c901400040070b011684100001070289581206c001c070b20481303003039084990903410752030303a103483c0d000940e030f8001005008210071242944940441000724400407400d01040051000e0740c02c40013101700d08034801e8005031246010395561050f2640500000e00700685020030315035410642114114014041090200114800380e2003800807001c426082201444070035180c2c1415500e5160a206d501c81c9441400000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 358705593 1250 358704343 358704347
    0xc05120906240303090d15050f0705041e080114091204030506060904062003090c060304050d0f02070b0f0d0e010c020d030b0a0b0a0f080105011d06071403030c030403080601 76
    0x107180b15110001090302c80e00d00c1a00c540d6111403603119001c0e814001442444060b845004482c01c1d102e005202030380f05121207c00c403004451014200d0101d22075550200a215508002281c1c112098142070310115080825209407111032500100d00550900c0c080b00307245807400100c5405259043c2c10348040389107801010555109501c0000c0c41d07500034600041d820f1a11100a0b540240500b0004c10b10303054018540343c04215420009080400100c24020503000800c802803030403105070307146031541c02c0c180c44036961040c820803a40100300c3c00710302c842807140c400c1c00b104001b0f150070b4202c10346a0700c18000c0056150022010010064038110340a00413070014003e401d18500d5540282040d04281c030f00450249c05518040c035040109800d00060100c0f2000007072410032038640c2d8040c508941a1070050021206901481c1000002c00c6c0644100070b84290404d403001c0d0032104a503035410b003441c000010440240c036103020f40c0004810402c5481c007000003544202d02c2940c614826690398401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 358706843 1250 358705593 358705603
    0x30a0605270c04090603030513050306010302010903150e10091505011212020109051f0507020d09170a0804030825050a12031b1d01080405060a09150c051209 69
    0x200290314022000350781e18060700c0c1400d40100c02107540500d829100d0008030295502035004034000780b00001d0101e0102070011800014140480183c005545160002461200c00740005455040500410315440741550b00400c1141166400e850503071440828404c010301c00d4000990700400d08030040002d030142446440e041c0c4000b18100c140480b09030700c401244c403201c015250250340da17802c1840046007080040701511903c00701d0014003440c84152500030b590010300080c0555008405019070305412540f0401a10030b25450202c4c03000c1044c1038030340740123400300c0042e22020300000c000c424001c030540282001e002407040300c11a035106110101c3c890120000103482c43e0007480b262130009010660000350b0305010300c0c000c603d41c210801d01008645e8921100300105003000c540c6600410078020280c42070009003017440351441c1c1502c0301d03074880720000c0c00c82480965548420042102103017000700318041c080c800700255400c00c400030340b01d684011100812514401c0007c1d400c41c4001031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 358708093 1250 358706843 358706869
    0x2604090f2a2a0f050a080d0605040c05190509180f0a05010f121203020d05150114131a16050601062d0305060a1205100f09020306010b130e010803030a0605 68
    0x28400c0034542d0640321010354110f440411101c1d4040c02e240d540c0070510034805803080194041000400a1610382004126000c40f0042400d00c40c052100c40c1c036804c01c0c51012444001c25003019980d45da140bc0c00601c15506488401542a070013009020f442604140d00c2480f601c9000400c201c96600d4100003003103980103200d00307140c01c00b104c00100d001030a55111800c94041030309025003400c20040e106001d0311400c541c501c0e1550009000700c101980c2c002c61490302da100184a1a01c3c0110901c0440d04c001400d01a46482081600c00f0141080c8002e08848400b806038890302c04800c2280340c030a49a0f40d0078814440000c8005002d0b503d0802240d14440010000c010414814205000c06402411005160a42c05400740f00b00052003410101c820f14402d00c03860140c20400c01c0341d4a098112000384143c0207045240560303440042e100050601e040d110a40707041c0d519500d500b00c1054240b101a041440d503410303503a000107038042e030000103503001d00708074403081c031040391520103025214032420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 358709343 1250 358708093 358708157
    0x90e010b1c02220615020a1106031e0903071a07080c0a0f121b03091b0509180c0310050108061807050f06070f0f2604090f2a 55
    0x1d0321070100b45002800c038142030f4140810100340704d60b513840550b486940401150000d41c10481241080280c6410b00d46861502240d4645c214148010112034100c00c0c520540e0b07503100c0d16000701c1e003060340800c183c034041c41d40200408410008a504098504000c2e2944408a8111804600c000c01e1406c01d4450100f850f50f0f4925404100b03180c04c90f54510000541d0405540d2031448c0d614800720b0035a0140d219215407404a011211032403c0412000c2c0240c41e40c0a841500b402440035aa071585560381140783c44112135152907984d00c2c8035080804114680303a140c410540101d00100081d001103040743c403244243c4038665500400c006000e144081c0c5550181c02c2100c080c05980340c010400c1c0072003040500034504041069480030014000003c0c00e403105001d0350100030801c0050350714071014a008407032450441380b444403036400ea8040d034081c0c1d604041e00c0b00f15845044c03440d5401925100d03044001d146580002280950f02c00d90f0441001d800a185c1c01c0c42d9138010030160303002001c282415 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 358710593 1250 358709343 358709359
    0x304080a021e090901020c0d050c030a030b011812020a05040c09031b0509010b0c0d11060f070e040c120e15040b0720100c09060c0219090e010b1c02 65
    0x29400c0050100b003294000440e00001c402c040a02d0300c4641d1268031810100d800169602014522149020244011302040100400070343c56010004003c0d214103449a040201d142819000142c41c24640d80c0070700003041c00f070035400044c00c1d11000c90340014980241c0e00c596009840740180015242003021070740100300b40c080c0c10000100d005181c0003160b00c4414003c15242c0d1103170000f40c0040000ea100f03041c0701001192640c000700d030034480e44080e4091401c6c000e00c1d01c034401c03030f1081e100c10300107244c04280c015110014200c180a080d507189140c000070410061a80010f60283c42164401d40203507200d03241481d5180c0003040018150040c0d01c845103422038541d200e5840c0001a00d004210318100803910041307140c0080c10020035210360f0406805404607075112602d4404540c0b2845028041042c0ca10042050980041c80851020f4056456205404525a41917000129588240388551078580c11200040e010f60046c000b402e400c03a854100d4140c10f0054441c0c2d10020788001e9804218 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 358711843 1250 358710593 358710613
    0xc08131106070507030605090f0706030b03190605090d050c0726010203010f030308070507030f030f09020a120b0615030c0d0603020d0b0906101811040f09060512030408 74
    0x825010110203126421401240c0e44180c041186074000c0303070040b41d283e800303413409000300300143c082e050b8000200030050082c1c10b40d4452155170b9510a120701070070f15035202e00503801a202800001030002282c01c82044043c0c0901d00300004100486404100303000b05018214146c1c42181203802c1c0d054507100415849003000507840c1d42420342c8910000d0705107080601c41c003020003800918020000c4914100a062031400c000c5d081d034800919542c01c000082022100280d00801011130002c00d03844e00080c0006c20380c500b9001030600e07100c0694030243d032440010703c88600d00000b4902911071a0203200781c1c1c0741c04040c0710100b80700170740a881c00f200602c0024100e50150019160341880380c0402308140d80da980129107820007404064440b150040704100c82034030200502e0341c0003001b6200c0580c0003458280c80a8007405202549480c0984a1315003603501d07a2100180c1d03000d8849561a10025603450010000508403480750078080c0072441d0350184010808130a940494415801401792000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 358713093 1250 358711843 358711861
    0x807031505061e13090207051b01050417030706060b0310140906060a2001050a0c051905160605010e0411010507050709050415090506092e02030408041806050f040c08 73
    0x8003804001c1240ca40600c9800d08448030031301c0c07180051140140c0181c0d6008036003002400d05440020610200d065601020f0950340c0c860111002c40e480504e070000c0d42d414280903a8150700c00d003c2c0c05030110341880408182e8482d207400a6004003c0803005000e0700350b40700504040c2071035109000742d0091020002030694104080180041d10306e0f0301d001078500110f00800e01591360900c268140c5a9503402c00c2141d401038a100d190031085140c00c182e4106070103200200740311900c640c491820046c02250004d5104100304000c8003040d071020043c0130340d40e142c40e0210314802e402c50b8180c411505050754207c00c0e502480c100c0c2c0d595900180900b500600381800c0f000a0800540b040b19837090903412480c03080180d101e034090542c07041001c1c2c0b01609046c02c210b40b6005462481c3c0074070b008000e80c003607030840e481082c4006484402d0405601c955803030a0228a0f4080c550200344d88001c0916055600c90042d4000d409403901107920a411a00070018407003100d03800c0f50003c020420705d50124003101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 358714343 1250 358713093 358713127
    0x3051b01110a060204050f010c080307030f1b02010e0d0513210605160801090b100e031905070305100203150d0f0c0611010e191401090b0403080703150506 68
    0x84181030140341d10a140030010b00c0c0121030202a0749540c0d000c2000e0100d403500c0110080820002d00e0038810301c12003521281a02d12029006205055480c40c0361490740030660042c1c4916004a45130456400c0c08000281c0600300721110b00e501030240c440758898090040b003c1e112884282041a49800d05000d10034000b528020041c0450dd6018000c2400244290041a10079440c0024450540591240207880d000042e000303c40d8580c1040a800000e4480b44000304501026181161041c2d0004000c40e0a0010412810485000a400366801c5c490001040400c80340701d68216240f448a41c00c01e8000c03030000342d42d41e103031400180c2540c0c60507217000250f8401403802440d00070411274a41d9158250504964480c00103d202d9054600c8141001e2044800c080c0390710000d04003c1140d032202d00c202c414946c0e0300421340c0e510182d604018440c00d40c0300440d941d0b030115401d1090305050038043c02c95042182d10800203420102110540d4501c03000c0903003182c501800690601a031003103242c16003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 358715593 1250 358714343 358714393
    0x2090c13061107090204090b0108091f15030b0a051905070c02010e03010e01060f050a09090533040807020a05030a0b040201050a03140a06030b100e0604020f16030207140a0305 77
    0x25115004020131000c00d03070310040c13006000b0044000f4504440c20005040c50b14000c0c0307003102d50341182020000da500c80110b1800705c00c0b410900007a02c1c0b400b100a4190b0307020913410140107031282d01c003080300f00462607000c030b4080c00c0150900301503031941e00e2002080d10380441c1c29100143d0855a100d005500915030b6003403c4a00500110b280501e403c001400c54505074445400c0c0f0040000c01c02c001e08001c09540043d198002080c441c002c2262156551000400389090403054442054001c022150010707990000031441020041d0410382040e44c640c1e004204181c0c801c01c080c441c0000c0c10b20300010f0324145198003040703055503039540c4c7e001525513421403402001815200c0b4505807088051035801842401a0000011403a045040a120121008120603107003c1c0d8410180003100710107880d41d9100208981c09070781d8201400d01d1328214082c80320085541e444550303000d8201500843d14005950030f41d000b03d110200503800b040002700361440081c2c072940140d003403000007140044041c505 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 358716843 1250 358715593 358715627
    0x1a03040c05061b06070e12072304090203030d020403060b0906012001150807080601090203190c050f0d1d210711030303100f05060405011d03120f0702090c1306 70
    0x1000030f140341c40504111048400e10001004c140912016281600c045051039074200010002035040c011b0b40c20300b84810903650280162581d41d1040d0640d29038101c10351141d4082e003a240c0341d03082041d10f01c001c0d402c603010840d1082c0c10810500102c1c00c0180d1110311480059507168a864003112032003c100f11204242030095480d120101e50401040d800d00d4001c0154000815aa0385031440d1b5504008040e040103000038010004d0240e2072244440302200c409502c0000584119405415125441514117090a005d00818141500020b07a03100318148005c081c01550800b5400114944811080304c034080b005012100035550300d240c41e0064521a44900d2500781009000000a4555001100c81da001e2540c4080148029020b04150f80000d0500795060390809082c28000307840c240031401003848107000a07000d1811030f034042000c1c0307101c1c1481a101c07503035810303517414001550b5000607000c0c1d0007a4034071408620100b01d020f0450315103e541e6403d0441a90500004a1360800ca540028003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 358718093 1250 358716843 358716877
    0x30d06081b2e2a0201030b030102070f031803050106170d030603051f0612050a0c091505062a1b0102210c030c0303100302040507080403080c090d050f071a03040c0506 73
    0x600e628107814003465600c00d00e8808401083c0a1000406039105510098007a0f401032002c1000100d40103041c43d032080d414102455280280024500d0040d02c640c006806582480300010b00310450001c10010515250159000040e4440c000c2c1e0503190648001819a80002980c52011001a00b03401c002408083c000ca006a55445c1c2040c08941182c02a038940e0001d40c43c01040150510714840242160403042c04114120f000303030440d49594ac0b259501486002982205e1240f80c521403084000b00318440395080f5984d064550307521380c4084903968000d0880c081e20045907000140c400322005c40c0f00030700706a00b060ad0400b0182500402c050f20282c5c0310034080c0303403480b10701880658070442d100030b40755540714590700403c415120301800c0e04080c05140d900740800b0a6122112903482200350204d50f581c3c1070b1010110b5120307034048601030214011048102c0701c190010910b402102e0ba0002a003240c0341e1001c0410790244070598005050a041000400660800e44013800f80c100e0301c0720b0500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 358719343 1250 358718093 358718117
    0x19020405040906020d05102435010902120a1112070c0b01090902060712021c090e06010206070207090f020405060408150906090c12030d06081b2e 64
    0x14003a500c0b1028111007464010503001440c00c80f51080c3c40d4007104020520840a1a000d0110010a081304100614000c45c00d144401c1501845141051800d1903007041380100580a80320503440c80c0d0101e003607408030490b00000e50002c0302d0090310b009402a817075140854541c400890020a500c803484001c4406c188054520700030b2040c4e0051041100740c481480c0308817280307030458160b10140c010f071198500d058a10405600c9d52400e40b0f0344160f105d40303040c0108440110680c41d15000042e00014080319120301020541d04c001e1450403614464482e1316035071101001a0380701c00c0e00315010401640302007000c01c803103911900120b1a110701c0303a400500e455211000302c2c0d07055001d5040600c080d4086246502d1140305c0b0300a956121520102820b12806d018110b1500c031603a00c020584100c505505210a000042c0100e802031160308804101441c1d552000c070351901c01484a20347e00986044104100c4d0610301d0714203407119201445c0030399002000c104d00007100c08100e052401c004c0241c03040703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 358720593 1250 358719343 358719349
    0x603040224040f090203070516020a080706020d020f0106030206090603180a030e0310061811040801021602010f090501021507020c120105190b060406031d03040e041505090619020405 80
    0x34503058008619040d0340700e080c00807140100c80f5907404802024810402c001400c0ea0100c19220700141100d02c0c40045051303800028100c202c50b400010b428003034441c001801030340006010500c5145602078880c101c0d40c04071401c2c201d803080d20002c0d4103e10700704032500e01071a00e0002558490200a030b01c1d0b20f45540241c0306440c0c2409240110040340300712022800516040285140e404000d1106000040c28980260340c1151403070a140200d90f140d42144e080e4a1a20090700d0240c01640c00840d22400f500e05c9001001c400c50509074003040c00c400142070b8003803282e004e003400c0d114107030018040085012202001614000c0c03200f0114011000c034400e103580c89040c60300040d502d400010070642829114004458400150000c6a0340740c10b42a28664480c001694201c4545040003d07018020034501c1c01060800c0c0c11145c264040000c000c11140e05400c8102e02980c000d0028035001714040c050340b012900c05684071f21241d07201900040310000c2c0404c04041c080740e001d82c05070409580d80d005c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 358721843 1250 358720593 358720639
    0x50307140d0516060e01110d0f0f0e06070609110105390f0a0611040f030204020c0111040909060c03110306040b190b0c0606180705130f090e0d050c070506030402 71
    0x40136000904501030030142d5a0705c4054009a280e03032401030618030b030b040b04018003000941e902c401c09100c0740901d1780348024042c40b066040d111003d0142a651103803850400028607040034101d035950081d0450783c01c5544554143c40382c100d46880310f084c030040b00c01c044410711440e569074200980460450249000740034460a0280390000d4010000c071421031402c9401d503480c0c071100b02e4015800b44010003181205180400440350107a07030040c2d03181c080d030001c1c601400645548a07106040018000f800c0d00c002c2c0d008164850054200f005080d00c00d0000b141901d038501030142d040c00c0140003085e9249001c0c1e01030140791200401000d02e03401801c2150210205a03482407031002408140824a0b00d01030001c07a038400000c03038040120348007a65400f980544044d001104008011503082c519910405e13400001d800c4200355180c0b0955198540c0700a484100c0079110203000340b0300c2c2400060300480584550285080c083d086072030410703080c03206075007009006a80c0100c2c2c58035640160000400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 358723093 1250 358721843 358721849
    0x31101060f0905040605070f020d0809150c120604111207090806090c032506110a150608101103060f03100912090602030a0905040203070512011e050307140d0516 71
    0x70086250702c4d090030840210f40004103074205200f0021304034880d180e40403a032a1400b014a003010310b20354940050640c540781c40079407086404020f150030311081e0305848000d0030300d1000d0b00b42540717110f87c0d07400140010f546d11803409043d50724061003490b820180c01114075070f101c2d884d450301d40400d5690305c015601d00030044c0d030b02c00c0700fa0700607404080d52800c0a00244240c0400e008050310106050f18081160f030406101700e908010000c00300c614011400d00c014003980d60814140038100161a00480c000c01c0c00348202a0380380f00f503400c0810054200c0c01508000c000c14050981969101d40501102c80007210300c159040c05109410605600203105080c0341d603000b230442e503a2441c248030010f421034400b03030822001d5600920140c030126900c00d003140141d40c0195400741e120f0311410000d5882c0c0c00f628804000b049071704000407403e05e08801010104021203825081c0459440040c5a1101c1480c0500001c81c3ea01141c4d411040c100b030040201ca00d88a14109d42045140381200c1d621480650 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 358724343 1250 358723093 358723109
    0x90b090402070b070e0a1418090f37020117060d0602040b0c010c02030708160206070807110f0d02060d020a0e030607050c0c06030915040201031d0307060c090b07031101060f 76
    0xa03480f20317114213150021102420104100701c20b200c1e800300014100c8500811002c0c8011001000200d4060051000c40b0040748000b0807910a407014000c00702e00d40c1d0f00d4114000c0c0900c407462038551030541c188500740601d6011f0711a101c80d2034480c1076140811000410890708000c2c45603904c800030f0032910041c8002c140002416850b0540744603554251090700001c001154400d011144c082140542180e42c03a95060452002440803403011440902901001a0411002040020030b0040d105441103140c0d070708503660040000c000c400c102501c050610040c1d003201c403e00c80012a079899a000700b060840d61f05110722207d40c043c00092038420126003d000050000c0b803542420302c0c04100078900103500f00c3d517050642c41c03c5001d440d90340c1d41804030a1011200c0030003140643e402680311044020f480c0d21110352986405801a41e00d0b44009012583c0707901d4440c20300903443c803610a0754107036000461030300d00e049a80d440840710b40d4516008041c50703550710080000d000782d40b2404103000348001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 358725593 1250 358724343 358724357
    0x220f06150308130e010e15030c090906091c0c06050c04050a080a05060a050118021c0c1d0a0b16080f12061e0303030610020f0d17070f090b090402070b07 67
    0x44143d608a010a9030320030b04807549200014400b81c408003a403246c4c8202c04c3e110541ca081c1116000a10700041100d010b87c0040c04041400f100501c0424038901c01d8000b20101c0f106283c0c51070724491002d1b072850a030350020380d1001c03c00000402d01d4120070b410070309143c1104e082584aa00151382841c855014061551042c0000c4003040401d22085500c910081c81c100710945c940150180b910021083c0642460b60003c0e042c10640441800c0103c00d040200c41000350009050002d081d4202c0b05d0000300003108481043c0c0d07601d05d040b07601e08007071b00c05000c849800c204070780001441401c1d08080031148034005000c443c0c80c42e1402e0b0040e0582c003400c894981854180003042c0580030103041c5101d01c4401d5500441007540e103002040f80d400150582d070800b22417040c14002c80c01c1421180c2c604601b805030300a4021416402680e69082c0000307910440010340300ca020946502440445007000310364a0b0108002c045015000390030421009030000d850b02c690b0f0340e6034551000049545e1b801143d10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 358726843 1250 358725593 358725607
    0x102011d160609030f030309060207170c0f0f0a1b0306091208070e031b040906020c070501180f0308030a021b0607030b0117010b0c0111190206220f06150308 69
    0x41180d0000901d4203040030791881341107446552010960703c1c4003800b4141c42e48a003508000c45c0383e04449401c1e030003e454054440209034100c069511010042c0494814a0300c0d013103900c3e40205034a0801400c82c00100ba100ca12503076424982d0765a1144d00346d00d0754800f440040030070302030701030410503030311500e58803101c009048006000c2c05400f81c0144108420400f084029403400500100100182280d01e680440900c00180203840032420082c45a400455041c80402d40015444140e8400362104040340f0f1040001000b00b4001c0d10400b484400b401a04201040c4c9807002181c1040e82d0343c2e405440d00f0707180c801c0f21004484001051903580c1c40134041082e00c651512800c0d810040903e07240d50101c80c2041441c014171018020100d160340d00150104a468003544074100048604d80219180c1c01000800a422968400c000d0094000c160000d84ea811920030700325907031010060780600c511450b494909034140200401c88145550700c400103003e1088a551600841c4221112951800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 358728093 1250 358726843 358726873
    0x30603072111040f0903030b03060f04051b18040311120c0c12010f0509030d050f0408040b21090708010f0c080c0c010908160204290f0102011d 63
    0x4568804038404a0040c10110900749564a1188041d0080091901c20000d01d001034001d2844a0111140a00c1d1071424401c150b0142c000105d000c03412000c1e65210b9986c460402242c1c007046400a00b29002560310b08a007841110704000d45003000340c0b1204500d0f40702d802c03003000c15038156000d40c0800d00d5402c000c0d14100040110303040e08905480c05504003200c401038280e6864050b20307200d1240c0c2d103103842078a82c1c160942c48040942c03183c0c40c05106a040804c1c0c0703182c0b40e43c01f03008014109424078000801401d000d10186003d2584402403602e03141c501000c010564000c800c1a6005520207510000b4540c0180d0000d8002d070b89800c064229580707840502c0d4215080c054403042c107142068105046290080c04140c2c1c010783e060074517582c030091800500e00400e907039480149004004a1841143d101030b1785c00448030b030702c06c1e07a00700b02400080241d170100400c59841c21848130703c01035803244a0b042c0f0320300d000d0409406000114411411100044480326a040c4083d00341e80000d5031007442c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 358729343 1250 358728093 358728103
    0x5010f050907030908190e04063203100f0f0c0329150309030c070605130806190b030a0b0c03151504030f0c0b07050a0b07050f12070908030708030603 66
    0x11450300f020072100081d640c03a06114020509921111030705610904031050154000310030404005204100da030b03486802c00c000042e1150903e5180c03c0d01807191040d958101600010720940c010003c243e86c0c26007880340c401502d4280d81d000d05250b1201180401103a650240503d000c0064401160480460030b8024200420004000e031018130750940c2034164484404a00341044622a1595a80d44190300e60380f030342c8a05c054100c0b552050380d0b4000365642c0d00501401300b820400c0038800c182e50b5240180c950718001594100086030b006544214001003070f910051029001a0589040c40016216000c0220003101c085c4151080002040211031048000f800c109008a81c0301c1c2c0c0c030341c1440400c00401d0145000082458000740350b01c2c0c040c42150100130004000210303005586c2c41051038010b8550041070012902040c00c3da000c614000d0045081e5440b200010802038185012501d0113002004c02601d1030b400c1c00340407c0003142a100c2030000b01103090040083c5039581c10090705142c030340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 358730593 1250 358729343 358729351
    0x6140402011803081222120f0801080d0309021203160614070503070c08190e090702120a0c020f10200c010c0303150506030a0903080c03071b0503090405010f0509 71
    0x54000c01005100082d02e5106680185c482c0a084603525a181d0340c8004030280c808400c0d00d4403003100b030321903000c00c84180c0c00055084030540d40c41421403c010016140002c0a028840b419046004150900c0344280d02c00c400c8280020050000b10b208141e245040d0f6214001920030085485052401c0c4010707030140c0983e0401415070729030b240c981710100a02500001e0288800c0000d822101e10500c42a18281c0300c40700000d41e50441041d070022000341805550402c0c45008254020000c0d5040c3c0c00403882c1c0340703010a6071511500d00f02740d542c41192010341a840403030303100f0742e071201801d43ca854503010091090300c0d54442c80c2c3d41d0680440c03120f6221514802c0500f0550015102c02d003180d9001c40040300e0158103040110701402d41c521802c2d0105000d402160f0866408020810001200e40290a4140c00f1351a01c004540700c84124500500c0115084808505503440e907101c2180310b42c050276612070084060380c0c1041e8100000405036a021b07803110890351b800e400d083c001c919100d4011908 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 358731843 1250 358730593 358730627
    0x11010e0703050703081308100203340509030f152406090402070f020d05010b011b050a23030d0c080903120109152d06020d091509030614040201 63
    0x30303140303142e454950340d081c03e000c0100701907004180c3c60201541403003450081d2003604265800c03e83d5142200c0e00a410441302440c1103100080c440c2110802845a240054451009506040d1480301e09840702d9105001c0c0c0d41e054441c100c03d030b1081c21828080319100564443c50100f850070280b00061504112a08580d0044050100a1090744c2d4000c11100d6404090340d002d80c80d40e6072402c1c611a50200f03e00069040000203040c00c01f08801980a004403c0090700c4058035010300d013690b0007113000400801015944106000c01c0071660b07024044442c0d80310202004207a0003a01042825a00000200080b00740c03110b14100d40e95401c50340103a4084000c90086081001d056aa0a007024041c03085001c02543c81c0f04141c1d8421003060900080c010f828034105948980101c48800c2100f8400d152041c1c261040c404102144042403d4540c0c82c171780c7e03480310510760038610790780070100410109100748429aa000000501c0d640214042201075800030711301803415000250103c0c03030390040c1e641 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 358733093 1250 358731843 358731853
    0x320060a0207050103050406141009060b070203070302040504020a080a0302031e03070f030c0e030a20060a051920030a02011103010f031b09060321031a0915040c11010e 74
    0x340d4039034006100422550f09107404201601c2c0d03802c22800800e4010b9a0389250762901080081b000810340d20342c001c82c0c40d8090300300400740d0381d8490080359009031034000398141c10000080015241941181ea001030000740300004003aa501e088500d80011090110050b030400b080c0042e14001c00c0620511f03074048402d07481c0c51031501a80040030401c0e040c0c2000d040c141e43e0710361400d505e8441c07840000203000c00317401c0301c0c010000c40c280031201802d81c00220600700301e0002581241e0030600709550100006031900350a000e0400722083d00e50035501c44003c1001150304100140c9000c01301148484440003024550310f1440740d00c000d007900c1c0c00c1190100b0005040004001414002c1a90b400300c0e600103494400004a04820038005111a0b21241c020341c2803410100034060810075154001d40192940303100d240c5550300c00d0342030b504507511180b074000058100c4c82040c00e000e805139611407a1400290158103a000000c2c04440bc030151680001d110781400b244002c009100784a01109202d000702 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 358734343 1250 358733093 358733107
    0x3050d02070e0105090403020f0304080717010c1403040f080f210907150306090e010c020f06010e04020409080d0905031b03070f110a0306020f09040b0105091f050f04032006 76
    0xe0302410040c0304e61401141410005401e06100348500011020b450301030380d681301d9590360115501c4400780250303d000d4428060117489101d0520a401c143c03400d07900d500f0780c1134071294140041600b0041c01901c03204003259003040002c00c40300c020104000103000d8243c0b41d02c508044410001007030f511101c0c41f0841c20082c0407800d10300207420403c82c0e500e00384030002d0784000f000490107810250301a12405042c184da2441000044d000f005004805038202c40036088400e5003607070385140a104e01c010318510203000c6805410150800c031459806020024a051801c100d00740442da1058015280b81d040400e03658816030b50010341407032108640005500303241d607640303c64409031071840f801000c525600c1841e9585440c2d481d9240e0045070030400840d15038454036114001a884401341d01d104e140340c03440042056020344140c404095000c0c044403071201319407680e00e42800300c611400c4240b00041c0306409402074820700400195104000c0202240c0380e12031490b5060f400d04400611640d0244020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 358735593 1250 358734343 358734359
    0x703180309050f0f090f07031b0c0305090a0e070801030c090b01020c060c0a0503030c030901060f060f0e0102031e0c1203040b04030e210c090903090a0329040c03050d0207 75
    0x8106590301154503011910f00500040e060600700c501d403640225a800c100301524101c0d080440c491025078805219840f4840700424024002ca0501400b082c803c240b000701092094001d08038a41d0058005444551648403c012003030007250300311300050040c801803042050010b404001880c2c8074805001c808170180010b912040c0c100041c03402400d011a103522500c108008101c100390b0000c0a81c0d990f030400740616070340d07a88210b0318580c2d01d609100c40000c4000b52180540f08030f82c01e48d42c1d2108242081e981c2110041801c10003241140f0043c40004020303c480301c44000030310080b1909643d1100d000c2079a60a0440b040c001c140204c1051040002285503030840740c1e805a81446c0001e43d02e2048400a4120701d980350151020720001420480380c1c200010300c0d5441c0c40402c44000300c41da90380020b103035130328402d44801e039400908001e000c00018514040310040c4540c6000b84060b03003001c0045013451042c0848003900c0aa10b4030301c041080c041c0a0243c03515404c800e102800c0300c1424a448 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 358736843 1250 358735593 358735607
    0x160207060207050303070b130b04030804060b010807090308030a27061a010509270f15090601090b090d06150e010e1605030c09040f0516020129130c050307031803 71
    0x40900100e40c0c60300000e0f601810440001899580b01274130038602e0070f160400911038035003120308031810352408050003980e60040072498810440740c0e40c1c100d4240c0c11a610385403d6000605910700d0340b9102c003809c540384074100207602211540c800741031030369031094200501a140d501032400c00240380c44d501c1d0901031b6880783c01c0f102507400031340d1004c0150300031031290a207000708003401c038000000701001d02801da040c1404550140d170701410181c1517000b17a00d0401c0380c8100300f51101800318010410805c64485608094445a44010322107c485e03183c50300c8040545100b10b06244c0e940c03414000034400c4150810f400c42c09441d203000000714520745100746c12520300b1480000c0081c05008000103203180034110440d100000c014005229001a5050b8003028110a40d042c00a02640701e04400701184148141c0c0342e102c0d00300d0040f400718000032aa90fa0f00141040300141c01100000c0c0744100728405000d954642601640d0305662850300b400000c0845070a42c070720021500300c1e0800c4401103a80014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 358738093 1250 358736843 358736857
    0x10150803030408070305130902041503360c0b030108070e0403050f0313021e100c0c0311060f030c041e05031011220306050606090306010b0d060b03160207060207050303 74
    0x10f22265130b003040742402d48842c0508203030b04102040861011810600e1500900304842c8404400020792140a00039800d540c0061580c0c1210313101c00000b1041000798400b43c4019403030407001e10400c8240d40d00d419030030702d400380c2168403411000401080503120030032101d0001c0a16000051080c14659030060940c8030b0151000800b45012011414804078482e04032a81a030040c040749072244100f00c03002410b00344104d8140300744002010000d065004500c0b00750f13440e0b4440001aa1941180d448034401ca00ca552a02d0300034100b030245003060410707580118000c2c8040c940b0151a1843c3c640c40f50110302e41040b4004003000503150400c119103000170810f0850405140114440005000c4500a4050100340d900034849500800b695210001420800d5902918040c8001e6840005004480c403c240a982d0583c0c04440100140701d00d100152090420402d40451425034448041410790010740f96800b100f0401c42c8140c203483d07010405035008040c0f0303001a01c031207807400e40047d40b40c2c000c0c1c003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 358739343 1250 358738093 358738103
    0x5190803010e0c0d050103060e160f0905090307171803070608070e120118020117060a1a0706020d1b0903050303010501050c010204080a03021f09020603010302010f0309050a05101508030304 83
    0x182c04241d00450a00c02c1e07440c0d6550b60700c0104110740c4c0d00e060000c007415040302d400c401b07805080c100000e40a10040c0410a1303506140880042d949003441d481c00608000340120610f0200340600800210300700c520300a44401c0d220b05913194040c0c90001684ca40003000214801e92119a0401401c1d40103101c0d560b010714941411aa0447d0003004110041100e0074011000e51900e01689281894001d021039928001c3c0d81d80a2480d07116254030030706040940721a58044480030782000565641000342c400d800b105a03c4609000b00c0e43c1d84d0714141d8022030020300140c0c2d12011160490074006c1c0340c10f0655130f0180b601c1c0401d94070355240c080c0c4031302c03060040a04114000403140940c4030250111801440c07103400f2034061500c02e080085d120010600b0301084240280c0031a021841180500c400300e03a001804a0700d180d02c1e59005541d010145000d9106264490300204040b0300140048a0428041c20240c02c5510b504c0301c3c1c241c11688002c00d5846040c10721601401201000070507240c1c81541300c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 358740593 1250 358739343 358739369
    0x21806031305060a0c03150506071202030f0c07060e0105070f0605220804080712170315060a03141f35010f110f1e04081203040519080301 61
    0x1801000c0c807144400c02000d40188600300c2408a0815954403004001d1080e50b0100f201031040100314800c0185032240381d41c0a0340030300000c1c021810040c0146200c08080c01180d00e490702801c241c080940118012031245d4001800030440c264110161600407803091070424034040302551031000c41ca054400c09404290317101c000501110424001d00002c8403051031402c0d16120700d203042e21240c0c1c01406101d290780200302000a090400030115840658405800480c80c42a0050100c26401c02020340320310404003a100081c03901d80c140144a10811540e003c40c681c5086108822080405400b4101a21004004080148400c0f00c40003d903503403840c0c040d44840d00c00740f0b940034040c2c844504013300d441403c0500307540354055000268005c0c1b4804188406124210388103400e002e10500300700c0c1e000303081041032940c03021081d9031004203812541c00d60406456400f0b5501c0c00d40b04131251418141e0000c2480240581003000d054890001039007903501810369503440205010603c243d102400308 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 358741843 1250 358740593 358740601
    0x602010c0e0d1b080118110109230a030606080d031d0717120408060433020306181005120304060f050a02010f0c09030303050f0f062106070305100902180603 69
    0xc03c2c0d42d040000e000c40030007031240c2e541454044580c800705580031101d04940812580140d401800b5030000c4903c400d00f0200700302e062440561000780c1c5a400c040d0320090890780880051000d01c10b0402800d0504005c001103082c10f0f40180884070800032500c040d172000184e10000300130015805045d900d1100c1061001d0440511291811004100b507035460100132a010541c01c00003e03240c0e11581c000c01c030280c02c484030642d1842c40310b5074103235a06c1000c070041030301440403400940003150070400142c1100c03141d240d0307010510410303a029204c010003a44c007100c4c200000e1410000300d5480060b0308003e0352a00d0300c0c04101070322101e02a01840705220000c1803c88c8800c1c001e5008001c0d030611440e00744600158950018000d4010780001c0f4082860800411000c3d0380041304c17640b00311201406c0c19403513181c03401003141c82041032281d80481c000d4145101044001448802e000301182c0d100403404d803c00c1601d81c00880d509410030940144144045040d03008010304c6c1e480007940656a650380d03a21 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 358743093 1250 358741843 358741883
    0x506070501180501050f07030e0c0405061c031d0f1c0206070b07050304150e0618030705070b07030e090c03070c140d080a0c0905030606130605190602010c0e0d 70
    0x10b800e50a02c018910706281e900a0003019040303a40718036640150842036960310542a0112068040c1340e6010303601441e1031000318245988195000300d030080440981c5080e80800803600300500380300720000fa0748a02c0d03006100c0504100d9a210b4030088034045455882800415020b461030340b0211035020704172070800b09646800e01160907058200d410207a0a00d00244040e02540c005d40b802c444003465130149070303444131403441801016100400070703000740d0b12082100c0046107000348500400b40800c10001c0300003401002904010103071221041e07200c50080c02e002d006841c00154182c0100e00c100e0401c004034101c1c01c1181e41c0541c4a0a20ba50b80080e2801d00341c0c00800302c4000002c4520801540101c086c0d00074509a2259001c00d40920500d048170a013100c0d2201c1b9403052540603880308001c135031685401510300f2010540380e0030008505075540d000401d42d0203602050800700354080d81c2071100c281d0a000d2040f0207a06403c0841c40051404040345a200c0b51210142c02c3c03290350504850030704 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 358744343 1250 358743093 358743101
    0x50703020a0b1021051002041410020c060a090e0612120c0115060e0406050402090d0303021b06160216050f010302070c0510050d050f0405060f1806010905070216050a0506070501 78
    0x80600c04c40c56020305031140303030781e810540c1411003525244500c100681c0214268001c807402d80e105000b1114601824070244240c07440e00603548025802030f15002900c07502d425010380041112559400c4030304d80340c01613002e0400c4010b4041d40c022803000c0c0d542c5851800014002130710000c41c580641e91400d0681c14640101710442c20807800082c11140041c82035801240444440c604941c20440d055860781040120300c070b01558a0b07001021900b0880110340130768042c101c80340381d400c440000d40411848250910034110340c1207201280000ca00c81c2c5080c1d0421035511a20760038610586080d0a110026a000440c416224101600010306508001401c081d044c01000d020b420301071030503100000909070f40c11071301c5c0310104a880d0100099501140300d0000b401150400060880354545247c1080000c1e402815520b208050b440c007a410a002041038a000300403c0f0b40c00030343e0b810f01400080c10500c0c10b0b03a507401c400040b50402c1c031095440c01041c4c0100d90080f90126554201d500c1d190f8094 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 358745593 1250 358744343 358744349
    0x403020309150f1803060907080d0509011709011b0f0903080d09060606021b0d08030a02030c12130c080d0f05030703060f0803040626010308071109090708010b01050703020a0b10 78
    0xc1020503103490354149041c1135041d244003201560416500d4640d83e40ea0f900b0b45205040c0706a1082401400036400740c0000d0241c0308040c0340807030060484035940c1d511031009440c400d09982d1340d0303407144180300e9117688003441e50407244c44e01c994200341501e80140484000d00018241e500b0014201010b01c84a901c0086259409402400b0490343e071040a5191070006880140c02400c1182440c0710746814090a441e55520004090440d202d09200c00c000b50002400454160303020010009420450040d0303070b10480000c01914007000c003d162200100c0c24641c454250740e4440f1498142481d000000c0307501d15011450000d8482d910f40c502200941800c1d4000d02c0c40325101880882c4c0042c02200078000d5503041d48920f40081250305a030101c55820b101002c80d1104180c006000140000d4007e00c20540940d450700480500e00000500111003614800403d50003903404016140081c0605900791100b401c000d400d011072a1400381d201c12008030000d100d035002d8000920041c03408040000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 358746843 1250 358745593 358745617
    0x1805091e090f060606040f09020703030b130b181509042303071403030702070303140706140a050c09030c010320030403020f160308040e0a11031306050f040302030915 73
    0x4a0401100c000d48851128900b584a40200c90000d000c40c140740c0100d40c11500d011404001c01441c0c09214030003500040300c101d0805407107440c0540540d4410040d20303581c80a030840080c80c040c1d20340c10080d1401c104006a00805003040c01c0040101d04c00c0c0d01c0c595452429071b503a20855845140c60751001da40c2c02100c0040728420144d8038007034500003010f4003c6610500c03091544015041500b592400300311610030059102210510003e1712035042440d96424965417a400c20035a0744d11351056900d243c055100720350110081004084181c0030311600601b40b1a00e061801c000ca1002c01c0d1541300749131030141450380301c2d010b00c04090fa40d005001e6088411801072512414185002519101c01c8180c8140501ca0000304600400f016448607045070307400481c40b882c0c03034540ba00803412220010b00c02c0803210b07034810500e00307070700449801144500030344020348034890070910f444030446002402c0c421800c0070840c1040002038001048440482d070444003040c40d0200320010140c0c1e0300c02c143e41018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 358748093 1250 358746843 358746901
    0x41802060a0504140613050d150f0912030915090c0302030a0f03021c0207180b031608010e0307020d0206031b16170a170a0b120705040606180509 64
    0x700d680c1c0d01101420a46594014a804c501c101030204102402084070203211030000300800c03c800d140801e01c90058520038040c284400d9001049001201c41d42c0c09050060381d1100307444410001c080c130071030801d07900a04040011081d140c88901c4007a060925580b40c0d00d9907034403d00140880c00d80d12000865005007114003202d00b03882d0201c0b100040c1841200580318460645000100440304082c4001c030326801010300e00e190089081c0e070304014200c81c05200d6540c078100b03840342e101808009080b01e40301f00c500c51143d2418034074a003140c940820051103600240300c1a0700503603450b8071203000750342c046400c02d443c0c5d22004544001401036080700d01800b00d0014000e0421a20300d61594001400399040a40051140090381424072070703603900a00190740000002800e0902c032112541000204000240407030800c404507181c44204a030203481d0303621405040009280c5070003010701a054514003c03012000601c00d4019560b00341c00340c14482c00b540c0c4005619005d90f5a452011841c2e19072501e0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 358749343 1250 358748093 358748107
    0x1605040e0c09180c1801050d0c0905011d0d0f060b03151b092d0616050d030c120c021519060501050901051206150309061005180604180206 61
    0x72096911181400340a051501009902c04003030401c40c9218003c0340c0d080c189060340780141701000364421003c1c981403040c04c0c0100019038015205009108031140c41d5441d07007030b040c500090181e006104440000c0484880d80c59066210100803041e0290300c4a1820030240c418900f0780c010345004140d441e0540703c0c0a0f0012081d0a80003e001d000e001901041100f11418192000301c0e403161030042c2d0b803c50104644081c0c00f84a80340303c2d1149644d603d62101c7c104c00e049c00084c0e0b0640c8480795000320319140faa920414008103004ca001044000d003010020151900b8000c0c1000c03030942880080107582e510110507148c0244103407103511031041031428040c50001054071341c24155000036000c241c94a81e011805501400480e0007100c4140c441a088c0400c0e1007084021480080c030703141d0043d4107128040c00c1d803d2a000070314050803008000c1c01c91850681061b0428116031703072040b03214417061002c5855884060940c3c5030480002d441c003045003607a89898581503804c0c44402504410700144038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 358750593 1250 358749343 358749361
    0x3311505070c050616080304050f0102030a091e0309050136090506090103150c0905030a0506070f090e0708060d02150c0c0d020f0f0102160905010311040509061605040e 74
    0x41150354803612202c000b05481d0428001c041c0220400b03410039000f0b184c440c030f011403414000b03941e10a10400407103402d841428082403da80060756203030422600c0e68101010000d01ca1400001d0121203c035441090110340c1b070060a00c0c036039200d80c44c14406032000d68001485202118154040d031502c0c4081504410300207190f0542191058519161500d40440c20914041100f00d0490f90400349480c0c18080c0b40d40c004000703094013420072050048407800003440752024040c83d0f188900500c0900700070b1800000107071402c05000d4454041150022050005c044401191a00141a45414503441d501c0c0310116101c0d8003041000795001c0c4451144281003840e4000074065400000b041c0d40d43d46800c6c0090002036440040c4c025405102d0861580690810700d01313901840300148101c40e0081003100300354060507200c0d0004603030b941d200c4006000f405001911109030130001e440800c1f592038001e2104d9200c0902400c0b030200c1080800700e8212440c810000d55001e408050b001c0002c908054080c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 358751843 1250 358750593 358750597
    0x70509030321061f08220c09051f080a0627051b06070c0b070615080c010201050f240a08160807050f030616030f0501090c030e03311505 60
    0x5660312500184c1250802c8520f250400d0210024070748902202c4d40703510b110440381968503540e2034420310140f000d001c040b40940c0c031410000c1c00c800c00300060380e080c03402c01c2600d884400e03c9a950700b5034805408001000c0e001800c1c8a01640003000011180032001d00c009041155032166820016448000c40a010000c14821001054030442c6c40b05800305178140300b003a010710344002d030903500300240803c00c45510200800701c141c854200000c1100301c2c28040088400142c1255500390310110786e200d01c0f56024811190010100000e4003002d00d0007204039840090001c2941e5282110514030741c46607111100d141010b0100d90061750a0b48150303005034442440244101c80300c1303109503203000074503080c81c4441c0c8211040c041c019000030750301d00611600f1291120203181c10150382c0d00700044102014032909019000080300401e10780d183d000000c05803a10601d40e1401504104072184948c03003110310301c000d02c180ba18240c940f420710403c907800c0b440600390b02c24080440200d20000c2d9603035010340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 358753093 1250 358751843 358751851
    0x1b1309060e0606010806061209010e061f21060c0903080d020c011103060105040308281e032d0e1903020d03060f09090609020a0303020c01090506070b070509030321 72
    0x2c540c0d140ea503010045030007900503038015800520030000f420007002d40711034907076001c050103001056610440c02002d28140c0f04036075010895500401a502c0100700c0d090a6004140e8882130081d40202a2050700c0802070034071000704890b956103440420076000303c10b010700441c2c0140030140c4411002c0341f000c0188d40810303401e40682d445c7c6194003203405a210240c074004c01c0e041c0d4075241401c0c00d595600460b907128150f605180080608042c82401c02a0f809800c1c0c0403441c0e46007040501061281c4000d207884d140d0320300c00d2504101c150302c04550326101818410b0032106550300520320304d039114030007020b122055503a00e010b02251031482d15200c0700b031940c4192003503084404107002d14070120120742c024001c000c0561603044042221242d41d81101003401c0c06403a00003a00340843c0d002a000880c190700860140e0444500000c1c6907030440c0400004000685005140c605141c1d01d080300c0c2d0400030501401e2100100342081d10752003c0007558014403012158441072410201c41a8203030340120b03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 358754343 1250 358753093 358753121
    0xc070501091b15050301080c04050912160308010e070c290c07020312030f04030c020a0801020a0e100c0b0f040c0e0a0504110109271b03150504020405031b130906 71
    0x41000903e0350310410440e4101d0345400c0151036a040d80000300005032030f002e020b003c0d491040020030005510200010700010109888540c03451040d45409040c013601644400340c001d4056040044954000140e00390b0071343e0040140c40350042c002c4c80c40c0d400c04000111841d100c02081d00300040e41c1c220700020110b850007202164bc200c0700160200910f44811a0428048105c16002c50002400b494860040501c010f2401510540b210002030032a04054144c00c0055103402ca0401d49040020907104900c11030720f406079504000c0e840d00440d80c01d000c0c2c003501d9094074000003d020302c04ca81c882c41001c0e00e00d90705400c8030b03400c1000740107000e058165016201c1040c1144030f490f01e580102c0b604d50444849520310b01d042c3c1d959082d000f880e03141500e240005546c40b1410070115046c51010200c6502450701c0004140d40d1402c08540314a6079500a10f000307501c100014040c82d80d000484007074046240b0109c1250400c4e80010071410304c0302501170042e40303080965a000300116030f040900140703d15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 358755593 1250 358754343 358754369
    0x6050d3614010612060501080a2001090513020d051f1e080d05030109050a050f1311092a1e0a020c0d11090604050c0f070303020c070e0415140c070501091b 68
    0x5100b4140d01c54489c00f600902c485201101800c144003c5881c0c841d10350014103082c031005688101043d0b10000c81c050b200e0446034000307025a0200824400c01d03400c820a551b1398101442d071144008940c0030140207140b03080052010700e54019040e011180040c081d1281034a5590071948406481c1da0030a001c0c00300f01500300000500041c00301c0c46030b07510485101501c440e40c0e031591011100d280c0030b105010b42e01c3c45c0034518206010f0311b40d20369541c014007542040400f881005180080d69001081c29200c131f0010030001540301002c158003c12184056908160740d50b1581d442c283d18042d000c94003a504900207100700d40c10700540201040030604191800c40d201e66903c0100000c03140c04413070354210348070244400000c2074840c401410180c1c0c400d040042c940300450301c0c03c030300d42001a400800500d01c4141000204031000032800e0360700c0c017042018411a0b044480040083c5402030040950000200c0c2c0202804000d40184080c075420140b50b00000d007030040500c11888040c000c2d21941c2100b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 358756843 1250 358755593 358755599
    0x10f080c010e0108190e0c1305060901050103051801091505070314040b0c040e0f01170f060402132a030c0e03060402040b06040503030406050d3614010612060501 71
    0x80840d9a42111030140e4445124203140001521405405003e001140340c0341403d1060150341403244918500400c40240741090107170080052500501948410036030601060012a40310028982e05642c9c007400e0100d01d035603400b402c100d1109000148441550b00b0804c6c014188842803c0c08001d03403000380300622141d520008141e059442440c098280000b0150014000c030303100040b244e81040744260100c0c60030307940350b444a500b68001d40d00c1d0000d4681800c01086130011a04143d0803440c130b006c02411b4108504450b1680ba100d0042010740103a002d002c854100d03010580c08011000c3d003030f00c07441900c00100000d5040501b8000c040d400881e1415401001e5240180e00743c100c2a03900400600003036641d9030a000c040c1600e0050185c00000911000c1020b07a42407000e0405003980f942d4643e02d50119517480402e80392180d078000125001807a61107040341e252606420300590854810300304403124644104401c1d100450702c15103501c4c0020104400c100c180c2d00c0241103010356414030099032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 358758093 1250 358756843 358756859
    0x51b0109060c0b070f020f030403060509010518070b03041506080f0d022a03010b0d031d0603040b0105010c0c032a080d0203040614090a0e0108010f0b0114070516080105010f 76
    0x50040d40243c6041c0d65000000c030400d2048924012440207031040d210400405e200151450704036801c22101c0b96118407c00c016060b092145551107941c840c04080c1c12410b509207135456203054052818209000400a03040c003c1c00314068600320911070080007200e81d10a001c40d21802034041451040c050b03034120190302c5d40700051b070400c01c2140c010075840441e08d24484101c04001c4901c44d0b5015529100f9040b02c1e0b50386d90904041460280d1504200c00481d0b8000d810b01308a203003c403d10801042c02800041408403c0c1d9a0640c0c0d401e00b08040390905500301461003d117036601c01031407078805400215004414089400c2c1c0104507044c0b0b240215200d6007a5901c40c0c0d04641c91000681c400d01c41040502c4c440d620b562007450301d400303009107404060004101c442c01d050300240c0c51240c03114010440b44200b407043c28074010948408201c01550000000c0c55100e4506a09880400111360002445001e0014042d141200d82d0701580701c5655a03c050701802c030074030505443d80c00307241c0c000070005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 358759343 1250 358758093 358758107
    0x1c0b010219080d150e01031b08030a0f030515030610062c010e0109080f2b0903150e01020d0507111b0103021308100f060605090a15020a051b010906 65
    0x142e00403009410405984510710081c1400611480821410300c00010000440141d060182d80a480d5503145906035030150410f260a075070050043d50310402003190aa81d00c003103a480e1294882c5400302d1182c56041c1d803901d807005d0804500f940340c05500d091042d0142c100003517408848442d01d810800040c2c6d0354419810b9217541c0c15036001107a40d0000156a58414030080408010506003d040140c4541c6000c2c9444501c80405400303901c440c0800c5514201103141100c4042c820300c800e440118041c81c010000324042c480200825408500c41850000e146c0040820703032102e03c000c40d02c88071011100360223000e0540d1110701080e903000649a142001103008031210305070421420034000118011000bd5012006c0103aa90f8074010001c100000203204890110245403000b044c3e010301241003400f00c0744664000028000100b00a414a03200c480c07041c2d003240d10030341c0d24000c14042c0440c03e9040030f4044100919502520210741001035103594a04003204084c0d0301d40202d10789610b4141c841d5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 358760593 1250 358759343 358759393
    0x50103021905030307020f041b1d150901080703020c0a030e09010e040b130c0f0303050c120306101815080901140705180d0c09020c06060303030c071203021c0b0102 72
    0x142c004000d805c005d8241041c0c5001c500718003420005190b104602000048000302c2c21200014110304400c06c003040c00c482403a001007004803480e50a00c0354807038100f0054441d005240741409086000555414001e0741920b000340d810070140c851036425850000d0841583c00b010b64403c2400e00c0020500301a03120195108a034002c1a103001a141c58541d5642125200f03012203220ba2b0600011640380d503a480010001c5110307844490310b40190b2030b9607a00300440e10240c5140842c0a00800107640e40f580d0080f400c00f00c0c0f40c20034990185d074160310b900a002c0c454001e8481602c010002c1840c0300d9000e03004610030200b440003044140c0000c0c0040c500e624041e5801c01c005003062040c0303a64100c1651001544400061945000e007180d45d45144ca5410294001302c0e20b01d80c08104086c1500e000d01a15603c113100700c004d0751039883c0040762501540107194010b410400c40e4046044094000d9045403c1030181e400160f1007900c981c0c0107075000d0010340301c00500501410548058010950681d5550 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 358761843 1250 358760593 358760599
    0x50a060e0103030503150a0608090d0c020913020d1e02011205090a0803180a030302090406080f0706110f01020408100e03030402010c0b0a091401060314120d022a01050103021905 78
    0x2141c1d1840c1c80c100d07055040500682181c05213100c548444e0f941d4903d4007001400c8540f100010751030403116403820325486840c00070500850300d01c0310300103039681407000341d10040d40c00d401e24540180780086080c02d0340b519001010120f030a1810f600480515521082c414400d076a8051a04116407000c010348006403240c0c4d040d9409007003048005032004000d11313884025010858484038800421510f0440003034402c2e0301290f4001030006040c01c2a0207100e0250200d040180381c001c3e020a1121b50b10321141c41440d0820040c041443d213450030610044e1003d17405800295291740d00c0e07940550b2109182c440c081c060b5890100384200f9180d0201c19280300700d170140c4601e400300207951200210564002c203100001c3e9600c500c07840c0024041c512031900003000200014242d1f06601d022004d440e00c080e40316020303500c20000b1030003102944c01100d4a096241c64056181c2002610700385060007044446021402c0b00c50080940c4081540024100d90085410540356140710080a030801c15034010190 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 358763093 1250 358761843 358761869
    0x2e0204080625021b1203120a0e01060b0d050405070503060411100f1d0102030d06090603020f0102030c0316020a0e1303080a0216061802040513030905010203090a090c0e06030a0c03050a06 82
    0xb00041d10090002480000d402504c41020480b0082c3c111f0b0f100710031100b143c0d515001803011081092080d0080005804000c010160404c0604202d6024004108034402d444030000b4040000c1400b00c040104800f900312919410945482c0d42c003407440c001d15900a4505a0f40c070f499492044814040b050300c00d84034102058044030010a1812406034400d05511041120803010321040c0301d040005e1046041c009415030451041040c01c2c100c403061a81154802e002d20030000d05c0110481d0b40348120140203c522140d544003003a184100b5500c6030034811080d0041100016074400511190b9211b40c0e1002142e968a0300907070103d0241d1840c0c04aa405041e80c200d00003011640502c40700b410408000d14201c09590000342500c00c00c581000c00300c80880744917002c060f084040e007009464240084c606100f241404070f030b000002441003980307443e00c5144e8108400c0c0541d0050200d124042c150598902d84006840080d100c03564a02c00060324001c001030314504144500425110314501e036030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 358764343 1250 358763093 358763113
    0x613032117040c031b081b012109020a06080906090d080c0d020c06010b04050a0807061202030402061204141e1b01260f1302032e020408062502 63
    0x8051110020812200e40300c1882d40400800d030392041030310005c0c140c034000700d5403d4185180c0a0414803a022440604ea46402070000603a0b0021239185a02c1030f1211041080080380e59400b002e001c0b8110083e4104840c1d07100030a000380d0280740c0d42e110700c074564100d40450303d8822000d9514100501e0860018540c5da0100b1200e005440041c80c0d100502d072400350800003200c500c107040400a911001ca030820015080249042c80c106c64801030042d04050031405180500242c40d840c6050450b1000d03541c0000003504560350b403800c1c0c43d61188188508469450545499a500c80000140c42003a01c80e070080b01c0f41c0d211500194085d10b100c00c1016019621060341d011890854500f000d0b4140615450b091031303400c042d0b200c0000c1f82038602c2038a60060405410f64210008003030b040c80040c000050846001da200007589801c1d20740206010b1480c41c04256041c2076548d4215480c0002c0341c000100058049800283e081c021040c03078100c0031443d207803480702d81c1c480300c2503200f10409a04a00c50b00d03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 358765593 1250 358764343 358764377
    0x4050a06020d06091104060206090316030f1110050a0b06070203030702100c050307060522020d120302040b070605040b0c0901170411040204030503031503070f0e0a0b06130321 77
    0x1c0c05042a600b680803ca10b9114001d10050318a0080708811180c808502005035583c100100c2c1d0300140450083d6242404d55180d40621805000c4080c05106000401c6000d481c841e080c40c04c00030a2100039150040f103140b4065000d00f605540703404259090500f00c8405207000d40403594150341c0200118580110303a030030700c81c5640701c130000141444401d03541c0c2c3c0701290090006001d000d101d00c1001a9600d854064052038034000f007503c0e40d074541e403005c210006031601c1420b1486250452030101901c0070401d401c078081d11598000c010800c034040f40c0c010412405805c0300380928840c03103440313609941d41b10920300d042c01141c1145000440c11102c04002000c2d0316030b15500640030380c3c00726010150300300108090343e005a1080b01c490f800001001036080c9550205080500101c001e0844a442d045401003c00c3d080d000b0b041c1c4a0040401144902d61280c0c4945030700b0701c3c09000d181c9c41d12005401809420340c1c2d44010340350140400198160210540650380c942405501c41c8041088800c0d50 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 358766843 1250 358765593 358765597
    0x14010905120c09040321050c071b090c020a0302070b0a092306070804090c08060303030a180c080102071719050703050702091008070905010e1303020a0b100e090604050a0602 76
    0x600c070001c0c00b901ca8200181e840d2011032503c03450107a254624818a142d2140d61210410f20109100d00e1070401444941c100c10700072500d0882e00502030104c00b8440c40703c0002e400300341e90b210086140c903001c00a0540d0703801103261070a0303501036005e50304407623600c90200142c0e104555031200011142c4c1802d0080250611505500307050318030046c1c000116100c0403030107541c8051400d4502c0b1602080c10814028140034680e42c094403403901c200c1c64101100800d81c1e0380406003017013050035203401d15403002603107000c8080519600030b14115a00c990f9107009a0007903026100680d00038260507101800040c1072812580c500040385064100130600031300171909074009007400c8040100400442c40940d031043ca401f0f0091805d00e81c01c000c0c141c9000e240c1454091b095002003400c0b03090000411000b91003032180c40e03105151070340700352014a142c91300f2810000300190091503003040c1c2d420701094121803042c020585884604540c8a0345614401566500c5c00b25001440f139401040120006103031500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 358768093 1250 358766843 358766869
    0x50c0403020d0f0f030509100c0b04060b010e0a090911010810090203060f221d060105150f03010b0301151b020d0c09020a02010f050a0207030f0c15020309010506010914010905 77
    0x469141030f64125500c80001e140c0d100c2050300040c0340401c8906007444c1030800040c0040e00c50900c0719013038400b99901e84c0116070007000501805c1e80d920a180c12079001c0d0038460460b8000400c1025250344070540c1000a040c044c40c00c0e035900c0404d5034450083c0d405071484500030003c112514000f00e1034181902d000e03500c0203040c60341114800c9840401d07a1500d080700c191010107079800d1480c0b05103010729a0304a4032040c000c1c000c650b10403101244820030105510741074070015100b4a2400754040065841c0b407041c0d4441c1040c1410000000403440a050051816a00202d030007902e02c43c4881c0c0704640c0d01744080c5000800c402c00c00c0c0c0303180c0140b8240e0200c03040507102e0b00c82121810707940d9100c901240c10145041025035103031403114550340803c0c0701d21a030140e440e2008606028041e02d00070013003120440894103000c0e0090002050222032150030b590341c0404007055540b8506030480b14080e10041d104036011504440011035246021251070802d01da040c1d480c0c4015074074040c00c21030310200c120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 358769343 1250 358768093 358768103
    0x8041215020f09040509030405060711030a02030a032003040f0e07020a140d14030f040b09010b0306010f05011107061d152d03060901061103160b06030709050c0403020d 74
    0x8164220196160010704094524070b1111074807103104105000659400500c542603a800c1040f0500c115030f034100a86003019040141281902c50500101e132a040c402d50000e5032510030010341004140d0702c000c050380450300b00c03c04540c00c4c03600220200d0f520b00641c003500442080480d401d2040c003141e411401ea02040c1481201c44030a0300d6103425a0090000400e88180d0b0007001c0d03000d242a4100742e0000950b1841200c09141d841e002c1082c515451019100425400001001c291003190075000032001013802030940e2142d5035903003000f0008030b01034420741d80441e00a660300e454003040824040308548498554050344000c482000200c091000303482030340802940801c50700200c004001e40540170110340500100c80c2a1280040d00d400e403110421052a42001007181d04d443c0c0c0000705044500f00e007000300c4a2460384101314198042d0038100721610039100300b14414069840f40740740c007030182582070310324050b1510480030a4450844242c40c050204000400050803c0c008800159001e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 358770593 1250 358769343 358769363
    0x30f020103020c1e01021306020304050a0302010521011202101d04110c030708091507120305070e030d120b010306030209040f0201031d0709183306081605010903080412 74
    0x6204c506a9480c1141e0015206a5002c95181c840c00160200031016000900095003003d1520000880c0c030b204a0100904000d404100101480310a0708119a89414450710300c2040d80c48004880c040c0c032440000f6031084e0740407407200311020f000d5421a090f086c188017200381803540c840705100c041c3ca4405004003030b041080000b42045002030016020807481400c4455541840e0002c1018144c00380450020405040103070f074001800c510b603010784800a908020909a481c0c05045d9980c01d5001c00c9280c1600880603641440b550003110b8000380c0c1d001071002c100000c030106c011003c40b0b038903000094000003003201107800700f00d8800307041f82814070514001c0b0740d610340c044c512501e034a45015600d1442c0d011803001e00600c038030346c0600b00c00d084480c204c0340c184c41c0c03d9403107054544607011805402e100c0e03006110310302610307520101032189030010b0007400a00c3d40d40c0b00390383da940748215118902c2c3c4101c413000314a940c8180103400450742c210218905150804915003e10f151100f01161314640c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 358771843 1250 358770593 358770613
    0x14240f04021201020a2601050a0303030e0a14030702011724030f0712120201020f12060409080f1c061d0a02040332010e030316050c1005190204030f020103020c 70
    0x1090005000f0305c0f405956042092a905000075540744038003100051400407a8014400da80712450640c04903900342ca07001c0340505040381c80f50300f030444040300a00380b81d4941d10500d0320780c0d038000000d2541d107100307a031000084445070038489100501564425a080e010b0906011b1102c42740c1d500c0362040c54010141d0b040001048070651a100786035004c072891005425220091080280c181c54031140b1a0000b9441c100305080ca01906200380003a8112801003a00401d0361030b10b030b950000b900c1984c85284255903500000d10b032111138009034000254000382003080c45920185001e01c0c811949002118219829035040240c0c83c0c00008084001645d821300c4004080380b0181c00307070000d040900020f10300101100b0741448500000010042050f0304040c1848101d4030004101c9074401074082d440300310305081c0001204c451249444a03001842001e01160108820360f200a01030b51103040c51100f210307041810303442680210700c00581519070b802620000765010ba00100b0600c604401507400880c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 358773093 1250 358771843 358771879
    0xb0a0b040914070c0302060609070e12010518030f04050108062409040b19290d06050f10020c01030908190e0f0d020a0b1e040314240f0402 61
    0x5500591400d030715101014140718415402c180c2203080c81c5804443e2034802d4601942d00d64010340b0090017101e958000544c0031384030380c0c8608200c4500a000880e07c1d14200c0605001e0300059a0340050010a19280e180c015400011a0351200314030035041d003090b11341401940d14a80c028442504980081070b06501400c1002548070081e411144032074450403c00d06120898a503495114010035000401c14202c60f030048144040780c141d000401001000b002c52042418001303140c1000c1440e02080f030206e115165000700301510425543c60380546082410010308540b0702410300c016030004d1840e80341552007a00301c0100c0c1c502410080c1e2502c42103c100c4282c902007644140000b5641500021041c5010030b94055141421102094142d400344c00150f45145a8800c2c41e02940d0b0001e140540840300b00600e00c0d6503078182c40301d151159640c0c189203456904c502c45d20701c4540500d035105107000d074032140110242c82030311030803032070544c2c500303d80c41a102406842030764090030012a200c6180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 358774343 1250 358773093 358773097
    0x90a020307080f060708091c020c1314090a21090b03040f0b06042003060d050d0503010f0603060e0a020706061a0408070b03090a02091f23030f030d0b0a0b 68
    0x20302c0ca0300038030035040014001410104090103003420800c0318414030030b4080d8000f0b450324407010351a442c00e05082c40d4000580c5402c1e84021a035421410ba000f20101070542903202202980104020652a54443e0180ca440d0f41806000070484042488020080303800300906602c03020450415030440da88030000c100460704121004c07079807110441c1491003000010b00302241c001c041900d00388803c074811803604000c801641d102110844001c40020f01a6940740c410450240d080400d8486580180c0002001c542c0309000740710b81d0907000c0f100042c1e41403091080b501111113041500308a0380300c440d00d410180d40560420f541e0640c5030710002c201c0d4160015101d0142c0c03111043c0d41c0e61141762032002030618005c0d078050128400188200102c440000c40c04c032211a41c11140080f01d03903541591480108000700f58a0396070111500c0208030001286907000c002015074414000c0c01051030201603413601c0c5c0c0d1514092a030824800d07c81c1e450415080210307003c40c010000441280c445904050795 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 358775593 1250 358774343 358774349
    0x40503070f080c0d0c1206110c031b0a200121020406020d0507050703030810090e011a10090501050309030904230709230406030f121b0f0803090a020307 67
    0x5000407440402890702c0400c4048604082503601c01210b5940e031301e8414031800d851240030012040c4180d24000c00c1003940c09030310f02192841e07090b0348035280c2d062101c2c0e40c0c4d08080090822400d02804114242c3c100285402c641a030202401d410b801401c44094a1580c0b0042418180510780541d40d1a0394003040340c499002c0511000144c440d0b14000c8000e140501c440001c00502000704007020202d0f4000c5054015a9018240f43c10140c43d0101654000c01c0b20740e221a41003464010780391170310141908041e500382c00c009a4009501000e80801242902004c450342c0070803014101007180354000c1019550081c2c404c405c2da4101071054011034150303a00050002c00000010001ca90869041c0401580101507450156107407400c0400b50040c0400460102c40c030b8051600604034195540c0e0494805035511009110048816240010814200283c00000301ea00c09110050241d6451140f0b810303140c00c1032200241d4003c1e5147c883c55544094050b010b0781c0250440e020140c0c400700842401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 358776843 1250 358775593 358775609
    0x4030b13170d1a010504080309041104080d03020a030605060c1c02100c020a0203011a130902030a0807150b031f050405070815070207050405040c0b0d270303140402031507020304050307 81
    0x5804009902c000300c01c40103030b0643d41400428001800151000015070b107503a8001d41c0c0008540b1000201000e0364065503100c902e0343d04c42c0140b80c3c200306038160080d01004820761000c0c031000c0c2e1034604102c035500401040100681c0207240321071400d031100001003600c54981c01a20555859402c4030f01c19104d4201411026910405546046003004d1181e01000e00c2c02d0301d400d102403181c110001d40d000100c0d11645990782e0326000400306564044c0048900d141e84405a6a80c0d0380e9613182c1080b28101201070111080d00d000143d24140c10013280800c803c4200e075000c1a45030f60b001d03140700020007010f0802d0382e440c895032002180702034040017a180340c1c0c00030083c4405a450000741c000c0c41d210468115074055800d11041c0000100c02141d6142610690b114094403440d220f001c110007403036040800304400b0100801601402191604481e1913030199800780310150641c1d8498052140a91b0000d400d6808982031b079a010b03114040300b0703401c01d08900c181c900d081e0b611000245441c00607084549 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 358778093 1250 358776843 358776851
    0x120c0507020f0d0c0506130b040608012102060301090e0709020309150702070503030304150b130c090603060308041e09020f21070915050c010914011104030b13170d 72
    0x825882c00c2c0101904212089454200c610740c0c507652101c81c110607101c0c95010f102d0108640000800c0c603040307980a05120241e494980c0d0703480d14020980e103401e110b04981c251850308a02c820769041e4400f9448103801030b024134038503461300751010002c0103007140c840d40c0c500464101040d0742405d03000450103038081500404031005000b0740424a91780180c94801558071821040080d900c010064036070045c5c0180260501c80d000740c4000010b0034004020961011840031403001e820f203541d002c600d00361a00e80d00c00d4021a1a1182901160341ca07010140030706800f804208515400c0c0c454a804062181500031100d5940303075090360990b041004031a00f1620045242800c0d142d800b000c3e045080a0003100750b04c0c41c244038402a10742c3d100c0d402031140700c1c9500c0c18990542c070301840899903c0280c000003006090302e9801d18038007103116030494404d25400e00184c00381a082160039181034a40084207511140c80b140042d814103051014100c401c81da240008031543d211900c0a02103d03d20001c02103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 358779343 1250 358778093 358778107
    0x71b290d022203021503431e021b1e0303160209130803060d0507080d08040c05010804032a020d300c02011b0b07020d0905041a090601120c05 62
    0x80b21703c4070703520050f464410341031080003010000c400210380d59041c030200c5101c0003082210100c85d00c0d1040c14907103803a40000d12500c289541d2210307a24400550003441c5201c400000c040491b158000604135150260300165028014684001e45154000b944102030142c44480000709080d074100f00491040381454403210307019400c0010392642d1200d08a65039003d059015910450b250002801d072070301402c07100311100108407007000054081c141ca24101d440a800f41000100500030496044904005964002480754028001c081c02a80d05032503412001d02ca04000190030441400b180594115501a82000d80c07206405416164020700e1040300a81c00e5140c920200003000e0381c00303041100f40008500e0569440f608a542c1c8650910f0010b400e0b81450604601d04850307040d0240004440d4800d1020494000034001d120340740c0c075140c00208a42e200100300840d103030f5005081105610f036842c424a460014030f0703ea8404414140900307903074040840541201c0d070702500e250110358005190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 358780593 1250 358779343 358779349
    0x1a0d1b020c0906100507151b12050105010c080a02102313030e0409030e1018140901030321060306061404020408070920071b290d02220302 61
    0x58a2003005403030b8110a0709118001c11152030550862408010000c0342e0f07801003114081c0ba00032003011010080c4115444e000c8128203d070110919100401d002d4501d50948100c6406468100ca5050711450310000e42d81d02c641c1c0c0f00b940040698411030150030f6800304040800e1007038180d5110924062110111003180c0c0780301d03241d03000d000582800b04010441d40040c0e440354060400391000e03078002c1010b9059280c20f48054104020a40d4813280101e00c1400069025004038100740410f0070b520700300d560f161040c80040c000054080c0c1c2100607800107102007409412207001d41500c0420000340320b1004481401242e9040d001154005e40795101000904900d003030703590881c01d0072201145018645000b2580d07d011074421200c00382d80b070302410082924003460f1070040c030840b401d099070b98243e0342c900241103400c400e44800d0f8100c41c00001060703040c6180c038103910340e540030700102078003081240d0007011681244401d4210039408002840101418000524984a1041413200c1e05800c1d4410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 358781843 1250 358780593 358780603
    0x31101030f1a01030b010302130e090c0d0f030c0f08070506010e010b0a05070f020604050603040501150e07020c01111e011a0d080f160605010303020d031a0102071a0d1b02 75
    0xc0d01c60140c00c05458210703a912146003141042400d0030002100c2c40c0b4040182c0c0a401010200b00c0e44840c08040080e007007082c00d11441c480c001c4002921a440310040400240840b0300d1400f0300621018100390000a01646030400c2c0340380905040e1000c81e681d5070341d4000b01c1d1310801c400c4030070360000c0e00104020340c024540a0b000d0044100340078104401400c2c001c21070300a582001c0d28000741d2011180654460308111005446d019140d01d94034945403c006000e42803090052110b400700717031000900c070031004045038003c071402d9020f849a032002d4001181d41d1000800146110b00079058100700310290101c0c44054030b040e40d40086074000a1030b00010760007030300d1026680910361047c0031000103002d680c121220290740d40c941076299080f04043c41d810211030741004042c80d03e0440080245900003a0540b44004681c0d03007446142420760340f01030300c213074201c0880c0d02681c0107074820300c00ca01e540f241c0c0c8003e14010034103190501080315259019101d90030810b02140c914510940603143d0305000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 358783093 1250 358781843 358781861
    0x903060b210f060f090c0103110904060b0417010903090b070203071809060506090103031416020414450f01020711090714030f040f0203010f0c1206050a030305030903120103110103 79
    0x2c01e8484d49480a03d003903c3d142140c0d1a10b04150780c0c2c0c102c60049090800558040c002c01402c204495078132504090701c69809070159842005601014998110050240c1a00c060741503039014041442c101004c4116000701e4803c9a05000e100300210b0f05404602220850712402d0750041036410a90500d0800c55a02800341401004417200510100e03410800149000f0810400b0581c1d511028110407c0c1c0001c90400a42c040c0c20100b51901d941c4a14000d103002d6107000404200e0200204044030120b49540f0110301c4540310504110304242070310ba03807540450200c0040e6407040454a0440b42280d01030081107a800c207541445c40414200b6811803070f403080b014203011707500b0008000c01e0f8046000061080c41c110071100c0001701000249038501061b140d0280080c041842030500d11030140c8442e00c1c0e40f4001a00008880f95000060b000390412901e018107000762150464401b12410fa100802c6008284001c0040701d00c02a014084140218001d903240503603406114001810f89a40320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 358784343 1250 358783093 358783111
    0x1092108010e0f040f0b04050303071409030c040c020309040f051501081015090305160e15090f100509070906030f05010e070c0302010f020408071d070903060b210f06 73
    0x8030040c400c604480c40200d8000d00803a1911070780f507a451403c000644130320f89005188010b800c0030301041010000245008010546811540c038035a10031910282c0200c401d425070682c030141c0e00700464102913011840208813481500e02d002080d001050581d07200c104080b081680e030300200f010100c9031140040d103144091800b103149051044c0d504100400314098030203560303441e0550032000c9009052400095510070305a403490305008036258052102442900003a162800000391080c08a02004840d86001130000115440345545020050001809d40800402d481070201c1c0341d0fa508280c86101b1440780d030700c44c09070b80d0074074070001c2c103036200c030100c83341e081e03003003100501c40f04005d9043c01c0c1d44540649001d19484010341030481c050091041815800c80c0300040204400341d0220f2030710150340041d881d91440c031041c545205112041262a01c00061060805200060b5940c04c42e001003800101102004030307950344c003094100e10140340f40402e0b601c00300013928a5001440066805034200d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 358785593 1250 358784343 358784357
    0x706110c19140d081b16052b1d06070606080318011404050405060d020a060905091003110108040c0b04060f110c0109060e0d0b040305090a0e060102121b010921 70
    0x4040f010b440c0c1c4102800078600100d03042003101008020b40d0640324600002d5140e0f5a100229040c040c1d10f45940c0f010015a2800e182209000c1040c00fa50004031480a42c1d206003600c402d40ca02040241c40d07040301c281c2d004804000b0140481c0d500e0180501824400c00079607a42e410480c48500c040b00032400c254144002070020000da031104900f900c0c1180d81c00c0d078011601b5071781d850004d0040300c80f0040007940920b01c40320208099034071200e041c1c2540c00a0340d0758001910748065654411116100c000c1481c9810304c00c41049500c524207542d0403920540700d40c0e84441d22b880105025403c680c000e4030000b040c07103c88807640c1d60b000360318021190b020380103400c80215510000701079802500402c001e008901c00d0201d40b50304c84000c5e00b14a69004400c01c0521308142ca8001d00c15072080d110340c0c0c8180d00703149000c522610060095401418141c0040c0420308020b80c040328103421100c3c41c40c000c0001c400c2c0781c1380300c08030030701400c058640300d2507550b801c40100101c0b11a10070b8007140d011080000b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 358786843 1250 358785593 358785613
    0x150e07090b06041401031508100c17130c03050a06150918031d0604120303110c1506120f010903031b200a02030703030c0510110706110c1914 62
    0xe040454094840004c80c08914401c100c0042e400350240700b800c110b00441790100058040000308a08038403c802480601c480c010101040b58a29158418190001800404900300010b0703503040c0c43e403882c41508440b1001756207884260401092417415a0455180c1003903214080d8032134051800f0b0034050300304000704019103140c1000c0d890041402030600400148103112010071314940112004000d00307007507946454009401c1030720b402040071404282441c4210354141078580a56071410010402003030080714001482e83c160b0070160807640c004c151001d5100c0c814070300348141c0d04003264403400400c2128051400404a48149008003400d5840d66448103000e80d00101002103511418000c40e03004919154207801c00d070482100a41c14450381d03070b0000800d5085a6190b41380d41c05101a940c660103c80c1a44040d552410803802201d0b10402c400000070321254400e82c3c10031004203040f4107001c0308028844c9400104082c00d0049420f80001104000c0d58403807250010b049880a4040050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 358788093 1250 358786843 358786849
    0x2604080315010318050106050312030417180a03030c0b0108062a0c0313090b090c0304030309111009090e0d1e0c0b1023030607110703150e07090b 64
    0x40900030401c6080d00903048441c50780300c1e8010040000e240141050030035060314016000301014880c0b2802030003104001a40c200d141000e5070700c80c03500300034092001c4040840034091584900801e4080c222100402900c98030740d60240c3d000b8512985a18a0316069400d2507203944e901640110b14660041080001501c48a0210000309000c005890030102d000c3c044407045000d0400030790301070b1002241180b032440f41404440110b8050550070003541d0300c0c18050140a020449040010335002c0000c180080d1084d07001d50441d500030024070ba0000d5110001929090140203c000011008441406066054030078000704804c0080200340390f4a03040720103400d40c1c0d002a4401804010f9000510045000d0543c14a4540d0301101202c140d01e0200d40104240c003030341c09154010203031041d281509c821007041e8a00000030040c01400c1580e5000d00444401150706403010721070041340d40000010b4100060030300200c441100110300400c00b48507031464082103a1004070202d0610f0788000d551b403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 358789343 1250 358788093 358788097
    0x5060a0c05180102070504050f0118020a0207060e040b04050f0108010e15060603090a061b0e0117010b0d1d011a1008070f1407060b150f09060a03060312260408 70
    0x4000c100c0c0c0c2c04415070300c1d00010f17400c0040301d0303004c5500941001b04001c244900d800a10303040e40c082c4060108901d801400c0c0c00c040340910010840543d00100c8180300b40c9008400c601c070002c400600108580b51140301241c151039003555901302000140b401803201000a00640356403580c01002008400303064034000420000146c0038600540000020941d5014203020b00f01003940c07ca0b00520458400c0c0228902c00ba462003012070000e21308000a5806612404081c052170b040707a00740c148581d0822040340d840744c0c00188a05801c5e0341c0ca0182540504200500c003000c218808000a000e0701f014030100d030141d01d492401480783c040e8000260641783c0182a041e0080082d150141951b140e07410300380d610448000000031404c0c4003041000030422103800c5400203010548107000c2001300343c0c120a00c02d0080c0d080900c031035681840f4a00b80350800300050a1240300b03034940030541c0d590302c0d161001c031f90100c0a4400002071440c01c841c503091021640440141403108050000c0d440e0584a8074024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 358790593 1250 358789343 358789357
    0x9080405100c02090709030506010509091b31051302010206040b06030331060302040b0702060d060b040b070605090606090402060a0e1203040e06090105180c1309020705060a0c05 78
    0x11200050785501c1984148400c00c64150b0240080c3c40600380894081d0400c0254070040321248207010010940381002d503940350080908200605096515429941110310032450250300400c1c00141c409014820106040c2003444611703c2e42c440c00115884007003540d100a1000ca0380880350380500c00140d80c001070ba2684260070100c1500f1580700d0800180c250302c46e0410303c3c40e48001c8452001a20018000070604824058010740f0945a4404044e01079000300e00c143e90720100c05020755400f41c100301c0010b00f0010258a030016030030303440c0d44030245103030816048046541004101c0e01704020540c4282ca4000076044000c0059240820005540106c0144000c0c05540b010034503901c4c15001708950134008900130b040e021001301d001c41c440c2d603a40140c03240d410701000030000b0500c24180034848038182c6074007500200703100000c580501c90726903000d0410041c0303a030200030603041c8413544010707007000d0709110102685d14881424001d250410142c0080c500902d000c9010f20b415400a00b01ca601c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 358791843 1250 358790593 358790599
    0x80102040f030f0c090207060506031605091303050408010507050c1e1e0c0904030513090b060f1b16030c06020d08010513060b0f03010801060f030503031b04121a010909080405 77
    0x90b0315500c1c04d14144071080c0c0c404280c030350000c43c124003041481d03000180700304020b4080307804040000c518448440d2241c41a0f503002f14403200401e45511000c85180c00341402400d0051078503651b0280903085501c11070398580015008580c010140380c00b813151010310f2400788140302044160182560710751940b6030340c0035a00b8452401e1504031a006001c041d010404c0140195000c0c58203083c06801c0394030210240700031413a032080c0441c001903e4070821140140250049041c2441c0c14000201c5a0203c0c008050032558621842d0b00c0400400081c5ca4107000502d281310041d10b0361038414003d034400c2d00600b00b9900400c0c0d00f080710f19442a0585e0445000312054000e0050302ca403000e0081c4155080005800e0303001560381001080300c2c0066040350b10400081141c02d5039880082103165103400010718a40003040400c80c610343e190004d1041c0401804d0080c0f0303081e0384428416640401030703030486109020900c00441444500b5290340101034021007441050566992a503851055004140c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 358793093 1250 358791843 358791863
    0x60c1b0d0809040b0a0b0a020109030e04090b040809030724200607030f020d090f020f0105041203180b0703180501030c0f050304050106120530030a180606060306050109080102040f03 80
    0x4c8079681d000c009074001c0c44201e01c584d55403012803100901030300602c03005034080b58a4122100d15403e19124900c4840d40210100794941c4413541d5191643c2c2c80072141a50601c13800c00d000c900729019600c0075409286007082c02c10002c6400703901030702d042c00b042c20b458030304680d80f2480701d55828041000340d4400040d10703000843c007103200f0700340b8000d01aa031117120708940350000084c10801010300c040c1050f40212010368070381c5203280044503944030703074041c003190b200e80001c1c0d0f8070000f400307007001000005200d404010b40c1c40d02d4580c518640e811080c030585c00034560600c510b41e1551a0103560018000c00c1c40c1c140542032805a01500c0784500480883c00c220001000030103000c020b5000348007a00e100c5002c03002d882000d050084e6143c1002042c8002c1d420700d001c00c04240d0302d40983d95515a402195060b05507652000200020000d00e00103200d100950907006002904901c51280500059200010040e04000006000c422950880600c0781c0c41084203204008804410a0441e035105840031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 358794343 1250 358793093 358793111
    0xe01031b0b030907030614040206121302030d0302070204143606010303030c020f1b04020a03200a09080606030a1403300c03100e0601030b060c1b0d080904 68
    0x1038110340c00600c49150100038001094004103000701128003518060000c001008500b03001c5940940d4000c0d4001c20810100107224054541e40e507004105881c2d00e6541009030300403a00b050b4420510000080e03002030800114a03180c4206c04001a40451200701c51a1100034080405048010007400e031002e18645010001d900a0b10b41150061a0594440c0d50351303481c01030040c08480f4142d40142c0145c4d001c060401c4070020b0000d13071909403003601040800d00f1805100c000e50001e01e1020802d42c4513110220941d243e90345010524001800550781c074000b0a100801c200c0ea150000d0f0181e40100c001c1c00740d142c0d000280c85600641003a0707017104142c810390129203903109105602c038480260824060051134045241c1014a900c40c501090039910300701c0901040c0b1003101c08141d2055400c030280083d401e00d126065110806040010f8980c480d2000185250828014080a9400400f000410486650b04d1000410041d158003545541c5607907102d0343d600481c803500d0301550780d501d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 358795593 1250 358794343 358794383
    0x5060102072607030c06080c1312020406050301021804051506030a0b121609060e010b1c0f02040e040c0b0903030a0c03021608030a091a04140402090a080303010815010e0103 76
    0x400140c04042c0200d80b00507035a07150030344150b40144035903004100c003040080e03048010042250041c4225440707600c042c81c20590080080c490780c83e82641c2143c0e60f030030045000d4600740b0042004c0008101d03076402007096a020807056607801000d413911100c00d2440c803412500d918042d20342041440301c0100d8200100008211450404901d6440501c561817801841d42c42a041c040240e8807120802d120013030700c8000311b101c134850a10920a404404118640e0f0644010403120300501f10742030081078018214031144240e0308990000305185440d50148010002801c19820040c0b01440324141411080000680c81c0d0092040030030a00c443d045032502018800d0116030341c014a04072128000c6070700c651175a0380c3d81e009088010b020480407500842c4515556105d650301140600403146024103281c91484111401c404803600103400788803250482d60b907901c0650203400510010b503125858000042d00c0c1c015400e80402c07905200000505c0160380304550f45045d40d0308181c59030202080c1c0300708 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 358796843 1250 358795593 358795649
    0x6020d030f200304061808030a02070c08010606020714040c090e090f060c0408011401030c14030304030807030c031202071a06130e0d260a0b0d082b0506010207 70
    0x85010780b00c4100307140b05040302201d0003660285005040802800c600103225000d00341c0b802c80c0107882d1410034000104610055001010000d1040859449007a030320400c2509580d569000782c1c015802c0004140034011020380044144c1104039001d001d52041100050440d007400e0242d1040c00d881c00340003528498040003040c0880c2c0c80401140e0191500442d030790b615030483d0103040d216508000c40f071560220481c0703116060b03927004007807841c510b031400c140380003d11a426500d5406010501c00000440c09020280032520f01030303100d5141000641ca0001d1101408021848585105100100100d0341e00007207882044c18103119801d0584905000984400843c800051610b00b40b140358171190a01140d507110040b1952030310100d0b00700341c1005030075085000c800034003031409000016140348840e400c030000c03041000e032441c0000062031700c954030b041e8044c85611000d2441d071110724401c1c90013907214150700703146190200298201180001d4548410b48203c9441000c0c03000f002c0701550003650 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 358798093 1250 358796843 358796861
    0x5071a031515070813030c050f031f060b13030c051c020405072d030e0c032a0a0801050106021e0a120e18011401030b0307181e0f0e0706020d030f 64
    0x280c101e44482c213001e044450417626010850b00300440190000345410304c51200c42c0e0303203400103000d070412009034040f0541c101c8690205181994454800081a80341003006040e2102401c2d641205141142003007036881959070301030703030242d0354090a00301400085190522080e5045401213160340b02d01d001211245c19840d845d446c800400100c0c03c000305001d420346003841c140b07a201400560882c42c80c264481c03c440d50303550303050380003802644c0d0645043c40b0011680d180da0810190701c100c1c05004648034507010381281001e42e640340014132142da01044070340c94415a0040000f48412035001c000d4513540070781401080e130005000954000d034002c03035680340d5442c0050144090312001031040740141d4421f00c69904043c81d1440f02c880785500c00d000d04901004040c00421200d07250080600e081ca00012107524000e030307104c0c90203d68000e420818180b0b01840040842c0d0480c00c1b00e801c404684d0b544042201e1980101410000250080385400810280c2e0a001402900c01d40441000d010448 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 358799343 1250 358798093 358798103
    0x609060518040c0e0301061e03020402031305061602120721021f0f060504090809060f090a090911101407230307170915030c0d0905071a03151507 64
    0x2d502c280c0c0e1303000910014204c4120001c0c492a50b5543c1e11840914041d4042026818010014000341c10325400454014644400c21002400591074442c1490803c1d180c4503010810018485544c80e8100304c081c80c0e0380a030740030b52480e08415170f85030000410564120000703c000ca01c1c105030b040c0d000b0b01003c0c0c007855003201403a84011001d00030500800c2e0800c1c50180062914030049054200780c1300d880c810603031100505140052401c1008015009065400801c01003041940c1307551300d501000b81e0081c0042075001c1080c069500d880c1d44500712039002e841c0540d07044401e05d03c40750b130320004c210302c070007040901c0596845090a04500803c0c856010303d24880e81103007075400903c0004000d00c0b00d1401061202e81409102c51107581a201e400c10300c0c1c0d40302c0005226500d0280300c031001507400c01c2c50751001c10720b0250441d1201003588e40010741079079190800081000301c00d03030003000003040356030490002d4138501d480b07418540d60804d50701401c0d0045600440284403e15244101c4a425400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 358800593 1250 358799343 358799351
    0x105300702030d0e061308092205061e010e0103111e0909180a021504150905030606030a031d240c10060302030307260705010e0610060906051804 64
    0x4004069503d03484900c405889600c2d00380b14000c0c21401049031402000c1001d03105810440ea900c0f40c440e642c10607072070954004200c402150881e060700d031048030001d811110114441c5000000c0103843e02036803200381d0704042c11b0840300c1c42a03a4003002d60b0303041c6002400e0000c1d40701d0052800c0204d80c092684001204102d080108000041c645c0140c070350700102701d174440f0f010f9981ca0b1244c4040180d4100c0100ca07039002a04000040c0b80148100030345c000d006403441d0402d583c820003d07101c030303c0c2c002d12a400704001e01c4060003142014026190301000079401418402020390340101442c102114000030030f0044050030159a894201144480c03034011800c07640c0c03000800340c50300e06030710400034400944a10714248452529900910084980060145062518a440d401240100710075480c001d00c0c003d0060606443c1090054600701c2c0c0260b00000e075040d014500c4510f060750240c018088074000071810028558490301d0171096410341d19126450700744485003030122240011003a82d0190078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 358801843 1250 358800593 358800601
    0x7050303070609060c0504030f120e0a0e15041b110a0b04050d081b09010c02010207211406012624091005160c0f1b0f060e010530 57
    0xb03907030040c8500a00450041017495580101911a840340740701c018000d149070300400c008911645004141007100c6e0400304140d2408e100010080740c0c080c0c200000101c3c1c070500f03100c80881d020b8404078140c842500d04114600d0310624110186040385250310400c220303803200340c001c007006101442480307501c0201c6100b5800d103850300075100d412680e2000006440600042d041240c19110815206c0c0e804540034541842540110b503840a10b890a03130551181c84000604840501c1c12018500001900040042014a0014803072071b16403045000d11750101c401805810515281401c4041c480402000441110050b03c0c1c24104403008207445101da5007150104510415400c6104500c500c0685a454606002d03000403100700340c039000109641442001000c1e0b0081c0790442c095030141c030151050920b90340e00c0821010301c14030540340030728070740d8800c0021501c2c8110f4003010b455903041551480021740002461400b59281000d10b008040340c0040780449040d0340c00000c8a440010b0154920f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 358803093 1250 358801843 358801853
    0x4180803010f0501020f150a09051f020315010512151c030201020a03050c03130b130b1303090b0705030f070c05100c0318050108060907050c0303040c140906130e0705030307 76
    0x2120344100c9025015100c806c1481120120b41c18280403101c20180e201521841e0b1414018800a0300c100c41a100c1c02d00d800c0a111607080380c00484644094002d6543d16082821000d680900c42060703040c4802880030b40003400c412181c0c5a0310010b15450422020055000203240003c01300c0203428041001c03e110b01031540c19002095540c584d40c40500030f540328240e5942d00b52200300d0759881da407440303020707200c000405240b03c07150000303031214948849401c04e40301c41c0c070035045c20384284c02d580c111000344c0000c01d41c108990b0b100174089218020301f040c80d40c0d1591500c0b0300c1082c581d140150300c006000410045010301348405040d018144024080c8120f0006d444902124015408608a08988051041008040c800b41d0700107030346444a07502d51100b0312454000240594051050920070402c0c03d040400c0074511841c01030200948403413524201b10b038240c141c030b100c081c002d04072501040f009071904401050040c105c6034000901d00605603801d4141000d940002d40d0600ac0007034600107000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 358804343 1250 358803093 358803119
    0xf08040e0606030103020d0b06031014010e0c070c0905070c060e1e0105011a03040c12030c030f030203011a0c0f0106090603050f010606020d11010b06040f03032c0418080301 76
    0x110805a00252911541c0400549000911000350b02c55002d90710440014101407041d07801c00f001408684182c49103150144c00d4480c500c800031056002c51004200d071260046015800848206900303207003903296228541c80e00803500640c0c0303015494001107403141c1d00c00d446141c16580c001d034041004240c11006540c0b01c21480820400322078031a00555030f0300806101e042d0403a40c01d0a030118000d5864142e124a941004100350b459450b07454000030140c8007a0885100c4c1e9210307540715802207003540781c080c1c0f50405001c1c02100b054030501c0103020002c200784010b0300c8000c110204a0312120050210342c0f600c0da8204a0250741e500b410303000107204090380c02c2201a02c6c85032059460521a0790b440e5400c03244240b107a0340059000342440f0714194041c000585507445080c001148607460080450030340d60160340709550003482500704000f0f043c2d01860710400785948412084003045902d40c10642a540f0b4640c040c80b1710b9980b803c010b075401020b0601c140d1036a100303032555101e60351122450032403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 358805593 1250 358804343 358804349
    0x70503120309061608061302090d050304150903050a030e28140f030c011404330810050103050c040e040f1a0712090c030206070b0405071a0706050901090f0804 70
    0x2070b10035800880c1c01114000d400c400804405d648483c1c1035543d010403c0f4850030b0308844101000d5003040300d400c00f520f030752401901c11b9000d107000b159100d1401c80d149600250903c0101c1c1000544075080c4000381c000320340381ea03426030549810140c103a04100000c1e508800204040503180e00d10414110002da0700d074186040b200a00c0382c0c550508070000a00c102214480509070b4150030520b0803c00300c2d80544100c2400007052184241030a445928003c8036030405130080d000032560803404c0003404201c40340c1c40480d0007186048142410072115520754490a40034071818141c4840006000d1502d000956000304110b00c8003a03002e0605041c401e540c6102c1901c19a019507103070800142241513903007801d0103a0704035580c81100056426104000b0b10002c0411203400615060000c0035948600260145a00501000c1c00c0d40c10286483c51510510764414807000094103002d03c8142d004d0805d6401090b01710f80e01040c25540d4000030341c012324240500412041103501c1c04824400008094025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 358806843 1250 358805593 358805611
    0x150109050612010510020102130308130f0e040f0821090706030c090b180405010314011d0d0c0203010b0d05060a05010b040b0403060f140a151a12090705031203 70
    0x102a298024401d451080c40840360041440e030004119506100000b0340e4054641d20005050558584215402941d0356005941c00c41d408184410040c3d003850516009007444800418007900d0001041c500a000420140440b860402c0100c28848094202d03504080010800a0500448480110119415550f4103042d00c03032440086010b174060b1203041c40c45481c9071039030b614462901c0c0d010b41d190391000b26000d0b959601c8001f800700a0b00e6034041d0300e02039441707203000080c03443c00003552501f107580040040e2004c4070340000c1c1c040c0e40c003404102e003110411940346c1032400c4141030004c01d014004d180c950507008560f0030107681c10300c0b03000b05040740114240c003410300059030b03031b8a808080380c000ea0052500c03a034400c21042002a41650105803220b00c030707182c04032b03264010b44500a145101100d980d031250b500d4401d980d0103141d078a00300c100507140090004400c1da00c0b208a030640c80c007508000030540041000070400c0c2e02400c01490b030042130000c0c100d03007010010701c40c00052608203a412010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 358808093 1250 358806843 358806857
    0x6030519061112040212010204091e0f0b0a05010c051203010e0702060106090e01090903020c030627011e020703051c0605041d0604031404050301060e010303140f031311091501 77
    0x910b609402040b50300034643e028000001d5100c0d42c00700540c0342c40c02c03031001143d90b5007040005031501d01d5000301d0360318510b60b2445a2000d40e2011802003a41d02c840d20707440d6121702e490300482c901d945054545041e40d2007842c02084024061034018541640700304101d4080502100000c3c915802c501c0711403042d00c075542034680c1c590303070388030295a81041c50050903c00200500103000050180d40044a114005c2c03046442d50180e4401080c1021400d41d814601c01060110385907241001003e00804404a90002c000351214913075205404440385201941540e00000c0d45c0c8203061050084e1050314601c411000c038844900c4840707000030640c80c8500d0b4003450900c0e10181c0e03615540e45071340542115903c058501699982d070111009242207840110f9802d05200210b0103131800d10880c8003074180302800018550440c2009031402c0030411215116139001c00403c03d10078800e1041e00e4000310181d50700001008103281c10703101c50307400142d4640c0048814040104c3c3e03403500306190342c3d200000e8079002c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 358809343 1250 358808093 358808111
    0x40201090e07050909041109040f14030903120a0203040e0a09021f0804030e030106150801080c090402030d0c0201030f1407030605040203151c0204020304080406080c0405220603051906 81
    0x32284100302c03910800328106001c462a0b501707004413040e5200740301d604540e8081030a140001c45559040d5000d650388460812035104201c0c0e0138450074820442030f0000d6041000303650000707030360302040101450078030404901403030124000c1007660050165031208004c68030702030322410300401020005074401e081c4283e101c200d0700b40212070401c100440750340d84480d0f1340c0c6985094034541e54220071250150340c0d466001501c00400030000b0444551591201c840d5450811910320300504c13003074510b00c10311402040c800180e50018060200c1c2c4d006040c0803540c2e000c07a000503402081c16101007000c83c0e05015008400d01c00d008112449150b103501e08010580d15001071004034002110f000300a1019100d1034000d500e000c00241590109000700c0c0c40d5503d069902080a81c1c2083d10103c42c40310001c42c0c18441d40360880d006d20342c01090301c0348090810f8a0580040c2e403105240c160500c401004256070410519182c001401075a0814115220440c1d0b00c04034490751504140190741c19850300301300c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 358810593 1250 358809343 358809359
    0x90c01090b03040303020c0a0b090c0109090e0c090c0d0c0e100914041e020a020106050a14221503050601080d0306080d1b0b0901140a050f1f0b040b0304020109 70
    0x120241c40481d071000d41160b03183c2da0140c00170341c007840300e101e0540f15000468000502c00000d4501c54181c14000d81011070036200050007202c1e094000072003040c20502e5100f98440002080c51800b0400c9660485585604c00b49203100c4c482d0f20208000c2900346454045017070b4000a102542c0502590203510050b00e44c002150760340c0003801040001c4074030409004062403e50800d6203030102d0603440e404545d56032881a000c9074840c2207250f001d40d4582104000a1624601301802002400301c0d800424402c074001035600701c4c0202e043c140d8100d880c0100719184519501c160b144410360140e4009d0795450f820300e541e07656400d201c0c1e900d103886104c41421806101e405040c0856210038000d10303e4a2000606603443d03114040358a403d0404501e045012035542c9888030300035a01c00c0c00001d4184040400d020300d903003000741a24520f600f40010320111404481451b54807103001117a000c400c0074100d00409001500342d0141105020108000c1000d0100c0001036004034030036201c0b0344010742c1d92010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 358811843 1250 358810593 358810607
    0x1202150c09030a0602211f050105030c0a030c09030213051915050d020613031b051e0108040314041e090603021f03021c0b030c0102070f0b09190b03090c01 68
    0x81e03415800c80c840b200005060f90700030303107400c40303107494007400c011010314410010381422a03100c4005201000503030008407450340b091014100a107410307407031860300c1904040d5500c83d80c03003a0b404260303540d042440514030440300310f0040e503801410f007910b12141c03c1e41348018090544000ea840c1803003408205841045100e0725081c0703c8507182c10307840709191004100f03803c00500ca00b80d811540420282c00d0350360040c20090050f40c0324071540c8603420324140440d202d0071225000b9502900103d01d4400520848c0001030007441801d1908403c15601d0386070403548520b0b01000c1c152404800b05000c113180e20407200b01d40601459420740700c00d440d034816400301074520610029400118611905124180214018150310b40d1800d000d498100e01d8040c90511422583c0c6140d90a47c3c0c4010740226481d0a11003505010001d200801c001410000c000e082d0210038840c2c407080010004082805894405040c0ea2196041e001402140e03078074014800d0a5104541c03140903405801d290501c0b6601800b4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 358812949 1106 358811843 358811857
    0xa0501090c0e190b0a0c030f0c020105090909010912020703060b1008041b0503030f0301030201180f0b0a0e060c0106080d0f050405040e1009030f031a06190c1202150c 73
    0x4009194002d188d821904000c1d41460307580250fa0b000007915421001150b0f100220344032140e0950045c282150024403141701080844491500802d80d00f00300c2e4013a0303200f448021240d0040100c84d80e1b400107004003240071040468085000303104003249009545002d920f10b0381c0c42d1000640b55800c400c4481880000000c0180110b5912125007040c405140360413118aa040040c411034880c203900802e00c0c0a030020650b6150b80c0d11a0200300d4078414098460b540c2d03080c000c00c00314060480d6018014091190251075480349100c0c1d43d10344d40c80388180c0d68040c1068141410403010f00b1640c01402058460b00210841da41c0c21845107106807032198503001101d40a50001400762180c60101c1c140d64116034800781803980300d42d02101c10610081003080c3d032440000005035009003031401c0141401c200e500c00c0022903034002550820b85894104222590f98400e603152905214401c = true := by decide +kernel

theorem cover : BRFrame.Cov 358633093 358812949 := by
  have h0 := BRFrame.cov_init 358633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 358633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 358633093 ≤ n) (h2 : n < 358812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
