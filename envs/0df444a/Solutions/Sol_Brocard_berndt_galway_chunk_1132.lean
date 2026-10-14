-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1132
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:22:54.825341+00:00
-- url     : https://prove2.me/submissions/61ff0972-953a-49e6-ac4d-8570b23903fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203417266 ≤ n < 203597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203418516 1250 203417266 203417273
    0x3040f120203071e0b0f0d0c0809150f01030308060a03150203070e011706091803030103050f0c03060c0d05132a1703120c12010308072001021b060f1309050604090f 72
    0x28140c00c1b00c4116880d24082400540c0012100c86200650025980c982048100300303003045503408018000948498514281c210034031038040500005007048504030224402e9111500385101669009c000b10196107280e1080000940044648200007150318420381e10395400f8110324090f40b90a24110103a035500e050500880010141045901c03c28040a5108814003403020b54040c62242026002e1003490f000864034114a031201c0e00d100c0d400140c14806e040d04184110340d00303000da0b2240407495542c1c0c11a10504c0e450b40e024090b00b1152100307095000c80001c000401c0103410030b6205004415280c0222a100700090131403650540e0003040130510b40c3c08402001d503030000d0510003840c503016103024034540c03881082c0d00403030b10035402040c0031040144000c000c07070055034400c46013549a0480c0d07000075550441108004032101d070701c80f40d50070036454000c100c0e0b104280c05c08081da079030400018400c40b045010710035014003514001c080340d5146030500540c00401d800624a900d46200398a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203419766 1250 203418516 203418539
    0x13061d04050916030507080601080105060a150c06020a02010c080109020f0a0305131205030f091c111c09030302010e070501050f0c07150e09060405010e0106050a0203040f120203071e 80
    0x140b0060403841100c507600307000c0b0b2a0080e0480510320490141c4803051070310281a15110043e0442d1410364100700070010952203ca1942d4112400108201d00c00b400d400c90070b03128152012005041c00d800087d440f20381540542005558189641c0c40c005140c0e42c075030402c000c034083c402d044d6140700810002030803060b00c00d1304281d03000a07040a55a5200c0c05aa0341c00200c402d40700c90a0300803450110421000104002c030341c1e80c1c03200c100d2010f080095007a8500c4a030b00c100200b140d505110500d2010360852004119080000101c003810300c9110b19003443c05001400c8600c8110010741c201080740c007501002241c09000c8030410303100c4506150002030791a265030030080c5190500c0c4a18880003440748101c8421075100742d119110104c50010714000e004030608010a501c0c0990b0400e00100020610040000e044071145e1034559240d4540d42012421485503a009109103440d10070301062a95404030346100d210f10072000ca130200c55607040b1b140c20310f82136000c0c0142c0d125898041003010a203802c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203421016 1250 203419766 203419771
    0xa020306011b03050414061b0d1404033309110a090908030a021b0601060302070309080613150b091e160e0114070b0a0f060503070b070828020313061d0405 68
    0x3d06031808c10700301d80c1024250202c00e106100955002c0f116440015030030007201107060344100021031403d803d6403504009030641d01d14600c4501198040d04000804000380c03881e85c000f4401062201010f1410038407142102c0c0000a44205140329000468441c04d114002005902c18010b41c25a901d085000c0000c2d000490400c83c10410303615200d904407800d11090f4083e00c120b40b00140c071803e071030500400c4141507403c84455a030004040c0184c48449028081855610103c0c009908200d1440100582080d9070121380000740d08003808038282080c4402c105104080f8451542603407480d190302e0004855081a1012030011020220b8175403103005010500d1004800491414400d51340b128918141100c04440d4a40c1e2050901c21030f04031401000010107049004020407410324450303100504c980c0c2e10042401400103502c00004000001d1106200100e261141141109a81c06074032584100a910500ca081810200b1101d015080d019500340b464522110091070301020712008100c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203422266 1250 203421016 203421019
    0x380d030903080c16050a120b04020609151902010626070b0324040b03030f03061302040e0405010b01030c05030f0403030f061d0c180d0606050402030a020306011b03050414 75
    0x1040c00c0400840c44403801011298042001007032042c0000c1c042c1c2900548580200e4401d03024850100306d01d480710b00c2e00c2c610207600484426104d03281c0d40b0002c5c2180c0700703011555410a80d2420207800078040c070400b81600c00030401400e5015a000d4501f20f00b03c0742140151a810004101c682244c2030078050320034405207100c0304440d00181c030303001880d07519001200d01b1140008107130241203c3c1802da0010701025201a641840102d4602d17002035101d000325104003005072000b01c00a1502c0e50340300040102a804a4030865840703444015581d0352203400c072010f803050340c01c01c03040c3d01c010f51103841102c165601070313698542181c40358203c0c0d280f01070016005508141d01c3d00348084080c0b00610820000304480c494900301e489102080700e80844004007420051101032203a003150608200d039a00c251901140c035810700d0f560701c1c43c001c001007a00e41c0110f6009032001c000c11900c405264000e601610098a800d6013440401c00d07111501543c03500c004002550601c8108204030b40c509206200810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203423516 1250 203422266 203422277
    0x80d11160506120c0c0106033f050f0f03010b0a08150a09020c010207050714010908010e06070302070807150b120a0512030a06030f0f060509030a020304030312020d02030901380d03 79
    0x640b00c11700e400c0d21011740064404a180c0c0c411025043d00c560340d0424040c0074000c0f000b2041e9140410321249a0821035024144500002d0185461007450b08442d126000c000c0303a03a403256103852905009401200c203000104900101007108600701d8074140070343e4080201505d014604080c0290041d401200d130a14403590203112420008400b841550060500081400404001c91000415071002a4440b508a17458035403690101400030a003140d1142580c10007694600300c0349801400e44c03007181806040d98116202c908040c9415030003600080382e080355001800e10001c1c0a09450349c1100c440101a540600e10203444038510f840130310f03403090742c51000143c407a6898071041444402608121500305a020350b11040104511615411000b580002c41c188030034103030b0203983d902c21400064103102c015600740f220052150112200004100d00940d02e908213400a03a01074007a00404200e0100049e4051807044082142d030485800c4543d4100032416420081c8401000c48070001c0d1b08004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203424766 1250 203423516 203423527
    0x90501120b0c07021512041104020c0c1507050d021615050a0c0203100207060f06060309081623100c03050618040807050a0b010e060d03090e060a080d11160506120c 72
    0x7610030086c11070f00202d94041000c500d8213180080b002a07000404920542c414044d0301003444e0000348034a81000709a402200320300038180040102c1c01150f174014040d01c24022146c00960b80850b80c2440c0d00c4140760710003060b94840382446200c4002c5002c880000740148040860148a541070601c0980090203581300e26203040441d100b60b901000c41540ca0366214a440070005070b9500c1102d000300030a02e410064a95140d90303a03400c1d440303220000303500b1100d143c003044180007070310076802c2000d0382e800c203000d258110103401c242d00e480d204000045041e10b0040c08040481c042e004840c0302da0310041042c0d00103a503c06c0002015540a0001d075a40300d001d0148a0000d0340400901c800d1a0042c004d01035550300d0700c24000c1340d4080041c80309006028030304c0c0090001c0c0c2c21030001d00940340350910040096a649000c20b002d0545c95004034184c0c0314183c002540d07150000c000358450080402910341d0101036140d0b21240b030290b841215040f1408111403215400340ca070881c5d401c034a11031000c0c0e2600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203426016 1250 203424766 203424799
    0x80711010c020304030c14010203070b0405072102100e01080c0d06080a1b0b0702010c0f0201031b03050a2d110d020d02090109081606080903040e10090501120b0c0702 73
    0x66454901c08005a8000501801480781d4a42014001c01e001441d00d09603007403290000707481380a03240005000030243c4010908210303050081c840174207030f40d4841030480c0c0c00385071400d4500b040303042041c1c1c0603040501ea079000c4684190f0b0210303810503042c0c49440c21030302c84031000407643d07103c00e4910a00c01c0c0c1d03030307a4045400002402014162805152140040311110103e88200c46450b40142403641c0e040220900503600107607080c0310650010400c031084019400168050b24824040b2101c51580e10602c0180c60f815900841c054803180401f040740c05840a41583e040a230180d1000e04203da04039240c081e9811a04140125481441494100407018042d03c050380c00401c4000101a0041b40c045080c2d42d0142c140002450b00302e00401003050342c0039403c00c011090707000b450104661640025401c510410440340104440c030894840c9203805030b4004c4486015024206145003414000540d2402c0024004d0f00541c02c02c3d4403904030784990082080e60341c8005022030b040b008003032890450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203427266 1250 203426016 203426021
    0x70306030c0920030112030810050405090105090115120f0303180c0306050c040308070f03110a0503090f0102070812090a050a060c02040b0603090309040509010209060c071e060e0108071101 83
    0x101a5800c020510f905804a03403c402c3c1c21691614044030307000d100411142c011601103150311a05410707c80740c0c640356010b05140c100002c2d000650850304080a10403454030560000f807041134140d000f0030003000851001c84100e0107900c280b0f01c1c60b214200002009c203c140d0b40d01da154620030b040014521000ba4180c494410300ca00003501c800004510400921855008555001c0d024061703031460203088d40c0d10080a07002c0c1d400e0180500704916980401c150040340407283e0054180101c403003001040c0750041d03982c2e001c4141c95000301d0203003058490b10350000070700c0c40c140c502c11000340c12010709001c9090644d4001008040d07100a1030140050182ca48401d2800a0500c84d541d000055001e80140800d440c1e400c010507001d01410020451a004048151402482c040b2004a030584910844902a02035000c180781c1c041800100354400c100009140301c211680015403421303810740d24401c40304c040308601c190b03404200e0802840314550310403405140d0001035820702c5608a03903004e00c241c0c01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203428516 1250 203427266 203427269
    0x1b060106020601030302010e06010e0a0903091e0f050d170a0e090c07050d0206070e01030e2506080a02070510240603020a0207080f0d0c210305240a0b03070306030c 72
    0x240e0002c40c014014558203000d210013102c2654000e1106500d0201007034140800184490140d50f42c8100c4403007090b00c0b442800005003410540310007052100b1340790200e5141248031713004911070a070b2000182810042c01e001c0605800201040c1c565140e0448862940d00c00c00c014010008000c00719401da542e00740406004581030501c8a03219030040c80c0c610328012181007007405540c0701c1000c02540c594400f198000bc2442843c012415626036402e0500e46000744121808040242118014a00b020000e42c011a86940c0e100040c5440e114031030002c078402caa81c06002e507042541801c1d207201e05034100100d203400c4240641803040c2d24074a0310090801ba030b046280020740000325401c00e40c2d070401204000d4150384000c1c04041002d00d543d6940c03a0510080c0d01f00f4000d440c030344038050140c07504501911103645200103411904850005009050484a180085441c00c00c540c3d03134044403203640b080496000e404a0581c5050806803151504020300c0c580815854000c04130000d5585c0300c0910 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203429766 1250 203428516 203428529
    0xb0303070b220b040209340504090603050307020f0904031e0903060c0806030106171506030c0a06050d150302061b120a030e070b070503220504020301030b1e1005061b0601 75
    0xd20a0401e481080350882001c1c0001c0d4202e00200194000e041d07030090040d90312080c07c000390201c0b481c0c80380c007940d007400355520103070525240100000c2401000700003800311078400c47d03500d000b15030134000300038440c0c0c4c05840240000b82c000c0d0801134920380c127040e114050f0100c3d08002c40c0869595071044295881c0c0800d51001581d44410322000341000d00401025100c078140041d5445200840356030384a8038403d0741e000b1090820b010640985050115196003c00945800e600302d07200c2e50050b103641d0001c408491840c0c41c2c503011100803c0103050410079070341e0041000d071804103407001c3c0348404c3c0344501c4401201d00501c0c21002d4030b403c40c80c00404d429500c0e42c602049201c03020a0407410070747d459105071402c500c01c200c0000001c0d0040300311011502c0d419414021400032000d2014820170540100d40c00510000000c01800180b55507107124800c0240a4002c8403128010500e02c0710040c3ca1160b40e2a99080c001c0c8202e00d80040074040303c180c6a06511415000d0034083c9140c10001e07806403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203431016 1250 203429766 203429783
    0x201020a080d0e010507020d020a1b03020a1d1f031b090e070e090a021008070e04050103111e01081303050d020406030606020d1e08090f07180c02010b0303070b22 71
    0x2650019001c4c0204e0303501600340c0c00a0588c1080e9860065152205020010041408a101d4603854a1005049000b940d0041e050328038403a103a6015059405516030701182c5910001c00040b82001c0030136a800410018404603446507285a8071136040103144800f48400c11000d00c40440c006506105030342c01402c0740c1d0000c051062411609000c41080580102c0c040d402410f64a0050780310b180ea10401550986080f8201d556000030071120311500035070842d4050f080000000c01e000d0302d40c600d2030840008540c500030b1161003540740055000f041e00c055010a0011001941451000380e1003a092402402e28030b00e0801948070940803030b44141c00060100390b030390100740101e513030420100e100c1801c40d0502d1038240d04d41c07072300c480c55004100390b60700304000c040030010340c45490902052040c40c208404036414203884112101c41c56200100c0c42c9005840c1407045041c0505c14051a0700041000d07000e0f5140160549a180500000410324503042140c0c0302501d803400450b80e55403134080d0085001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203432266 1250 203431016 203431031
    0x180724120e010c090b0702091303020a142b080a0b060408121801050403050303040230210703081b0f030c0a0305100b2a0a151d030409090201020a080d 66
    0x1d001308489070400000018140500c2d0010b840d2800420740002d1001d245601e4441c0300d140482c50650b1301c6000608260080c00704169050740001e042c0790000e9000c0c490403450000404007403c03e65441d11090005101a002c21240c0382154042c00201c00081c00ba0707881e00d62200e411500e03020400341505866200014401000c072040c7c00100140c00e000d103440ca2506285072200d540d81d00000c0e1004e03200314500120203150000d01d480c071492803c00c1c01e09203035140307102c000f0742c0e921400e0140342c0b50060b2902c03081001450340401c080300e030700c01c0c0c1c141c40d01c00441d260080c1c0c2415a602450070031503a2001004540492030042004d58841d2441c0d0441c2992280840e00041c16a5400340050900c10001e000034442d140c06141a140340d102c4007a141514075a061003210421051500146c0650085403c64030900c5849140f0070314502c402d500901898421712100e041c3d00d403200f9005125900280300134002c0703000541104807010300520441e6412000c03525101800e5101d6a60300c01c60b16582c408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203433516 1250 203432266 203432291
    0x809160f081b060f030a020702130b010210020910111501030c060e03010603080703032a0e041401030f020607031e050d0e0d0509060d090b0f180724120e01 68
    0x3007403408202d1400b41111a1005004281d0a0203890380d80c020303000010001500200f40e83d8140c402107a002804c88150401c0803803c43c0040c0750310f502e840c1c010b01070612203019040d2a4000c030f0b002004090480026040c1e0200111280804800811902e0040a01d500c24041613104540d01a41c060303485410290f24280001c1d04055007410494080d9061400070004120b06009540d401d54050174040b50b005a800c81c040058030b040c2c80c003a2109125007030201613007036000f1404030034071005039010458100f52540031800c02401b4031008050300100741d810001410800d014000882c841e050205003011a00c510511501c803000700364000074030100308a20448414080d008075465580f01034480f03281d80b8480108244200340c151401082c00099048411030140d000801098208800510508040c0d0001c42e110703805541d450088050020302a02c034060200d00c00c0100cad00300c40034001140d19801c9044002c00100981c10b0148400c07542d0701110f08a49014000d0010030340c20000804124900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203434766 1250 203433516 203433523
    0x20309030c0d170103031b0507030c090f050402030d030c050d091217090d0311090307090f0b0907020619021603020a020415060507021306081b0907051602010809160f08 74
    0x1d900c03c2010f840045140c015140c041c0c0d9040d0f0307400d81741035008103c04110024082c010f20a00500c0c61040320000010312130b221541000703a8148010500c03540c4809030a05040d40c105a80103580354000301040c00040303002c0d5001c111041c009060542c2800700400c1c0c10030894914000960b2443d958511361560300c0c0e8840d01c150b5600b420b04050300c02c24107100043d10355540c5003c10140915545450707213082e0851234070030344030840001400c90b40860b8032076501c40e0192000c10b14407001e95040c1403003000546000e4841d14403404090340144519a100c40041500c840c0094441d00c600f075003080941d0100d03803007146d100c40041c000c4c1c0042002d003400c1c0c814082140e100400f041001602c0b0320003400001e40c80b500720368146404507951070305643d003001500020203040d84a41340310702c01c6403208032240100c40d50900c88040b00701e81100d06581c0c2d840e025515031140d41001d81000b0031550380d0100540c017a54050b500680d900003203c0f00000503c0c0400707013038803040c0c101881a1407845000c1100b00c0042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203436016 1250 203434766 203434783
    0x1703100905040807060b011e020f1c080a020f0904090f03140a0c0b090f0105010e070f1403070c05011d01020d06050f0f01081819050f0106031e0201030f020309030c 72
    0x804104442d24181c0c0f5020281e02808900808460b00c802c0000102d0b0301c1901711000d920f402d20320440e00d0034220384002e5651182d03803501821500850400f48000c0340700240851048440c1d864840751592100407030b00c0294402e2440c00000e100a01072503d40b910307540709110001d0320072001020644c0150030f01401c1e205400265181a110800c4202c9016030b000381c1954440c0c2d440a0348147c0340e01c43e5507005040052440c81d0b1411507103400000600d0703002e9905458040d400d9038030340051000c50004102c03400140c000001055031760410100394014459070f414454903003e60000500c0700c51800545845415102d01c2ea10a43c0d000710f2440341c0d01100e88a5030000b82030031106401141c03015400b00300032140b04160681482042ca0000e1600608814541d95000d0703240300b5980c15030045400c0c00e0003001500c005881c640316044281c4a24007052154906503a04114000c508078203020103407040016801040341010f442e218852185242800550300034420900a19100c280031101c25181103a079 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203437266 1250 203436016 203436029
    0x1401060e040e0c01050a0c050628060605030c07020d0b0c0a0306050f0a05040e030c0607080103032a1e08030408031b0a080601050d24210201020c060c0a170310 70
    0x1020300b090040000061900e140103c28204540c440ca040b0f80d05036404413a40202500c1ca0252404209039802071003a0140e034000240c01481c0d100070b80b58001d0045564a0080390701140040020503102d084040142201500c020040b8182c20415034400e9040001624184540f100206400d0801030305409650050001940c41c058961400c178005984100240304090003107a580c00b80c5d074401e50083c8211002c8071244811602c15040205000304061024071055001a24080e41c080300b607034410100e410038800f0703000c0300d10101c81c00342c0710045c50340b1100782c05035001000d5510190024410f00c0145210b41d000e0407017143c4915003000b00d008a100c100070100c544440400026580581207242c00d6008003003843c1854992603803005510040c410395020007406210500e0401c0c41111380e101160550784036640340100c1c00c1e80494601d4414a107520001c1c056040003514803143c0c100303030024055010921044880e02200790b11400415804a4201c0111110001c1000745624000c00081f00505c807 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203438516 1250 203437266 203437271
    0x901212a03020f0f0906040806070f020c060301120b1f06031d0303071403060402090406030609020f010306120206031005040c020307060b09130618060e0c03151e07121401060e04 78
    0x1607000d109001e1013003100d4901c80e0240442d061005440346010f89002e0682c081c219421428403160203001c6024205404005200c2d00f440494203084c0700c8207582c100d0b001d680d0003003132200d600e587d0320f501060001c0c22004d072000682c40070b1082c2080641103800134410390301c001032040180c0103003c0041c807190030040580e030302c00c20034403007034135800402002005685007460786c40e0303291800024003038800c464080303900c9424034902100b402440c0e4030000240784201c4840501c01c00142c010341c00c0d118030b0b120b001d800c11031980c04036016007000b10046621200880c8280315007900d4800103000ca450802c00b017001640041030220411281744106858003008484401c0e413032620114174040b6455104c001001e06440d000302e8040034015440104d031b001e500c9001800314205030314181340d88660083c9964030902c22241d2442800108401c9580244a6445580c00e09604002054090b40c0301030428010810b000103c803480f09080d04c079001e0f040c1c9018000340e085502d0030230010072110180600c1c3d40300b80e1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203439766 1250 203438516 203438527
    0xd091203150806150910050303190809150a09030c0209011e08010b030c0d0305130b09040b040e1209030f0304090609050906160e0301150b190f050901212a0302 70
    0x1e04400c424000b4113812a070104079651844600e413514406d50340204e07050b2002041c01a801920100c100c08aa01a551107403e95654147c2182e0b80f4401740b0000c148840c2c40b0004513040507903d40204511034040c1c109021aa030456012030400c00c0300b6400142c03804c0200f8100003c013402000d2103801440aa00240706090b16900001d032503040340441c0c41c0c49030b64440804800c05006005407a01003010b4642203900c0c603580d001200c51a03000031400b901c51b51030084440c0107403820f8420f852480041f00c0080440086403580b803041030740700c40c4100d40c0c14420340c2e81450780854204010006005d40c020041001d0b49460205c4080e294003802c040003507000202013208024204915010301c035514506410300540031800f0900404003858820000ba49018000c070b1840e201c4402899918000050003501c0b01e0800021607104148604004c001402001302d0105903206901c0610044003844c558000010110f03070800880d100c60000c0c450b0006060b07481502e00580c4904a510150b9504007586000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203441016 1250 203439766 203439781
    0x15030304030605071103130b090a080313030c05030a050303010b0f0c0703060209040507080f0417040f0b04180204050109032409061b0f0207090f0902041404050106060e060a050d091203150806 84
    0x1003a005c3c0c040103080100740140d83c3c0d522030350303110020b0bd402c20551381d907010400b40707845583d603040c0401d40710b03400442c01c005041d0600140d4003070410303000005142140d00300003920406600c144510701d4028028860010208414400b1900552290900503500d0300010144405d49000403c100144605442046903a40070607400e40d074003a521171040310f24000c1581c10201c60f8000d0340c0120902010000000c1202c117000d200030700c1618004003820345803100080c192010f0384654040c850020740720310020000100c040414100641c014025115446107686040f000c898a1000c251002919110f04d421001410011903003032030540d141905000400340340195031201c1c14811039804503660900305040441a0740100d0a25070700600c10f110010010002045841017550f080e105540f07418000900325004145082c11040302421f0300c2e0410303c0e04d24064030700390050203003241184d842e11000d4000811620805010085580300081c490060302d1594065144c01e400152850b40444184080b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203442266 1250 203441016 203441047
    0xf1815060f030605060102071a0c01050906060f0d030504080109030914040b031914060f0403140304120305040501021204210c1509230102031519090515030304030605071103 76
    0xb9a0780010000c10380d41c654a00403498942141d000710220b0654046000c220600d10005012201c1c088000b4044c98803110385007a2076540c1a90f04030703800325003003c003411941800440060614001d0070101d00f0241da410320b95080d1803025204400203200322205200c81ca41d60310038010302d440c09803810090360b0708607004640d480045500748440e20b400c24070302c44204a8070000700442140c461050b04d0071030410490394005110700762001c03030128104088182c902e05840c0182c0303110b0354106400700401902d480c4240d004140c09001611555020040c000c120212114900e009610541800460700c076082c2800910b1500082079404005a039403000010412000310501402030b500c02c0014200724518111070502d482c021b11400003030800024007503450303040d8095442810300304480000450011300700000240940645070306203071058018014100c403030303110551103001106c408804114020000b8030b540c002da0300032100300e51101e04015156074803040307248051149500441c106200480741d081c8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203443516 1250 203442266 203442269
    0x102060a11070501091b0e133012050907030f0206030a0b12030d062705150a142b080307020a06091a06120c060c010f1815060f 56
    0x4151940361010341a000c0c001201c00143d849402000400900c1c171b041160303020103a003070090510210400180013110500d540f442a0202002c1e24920b0a9a517034006074642c42050100c2039046900f221584400f48a0f11000040e010340c462000c602461000c6800ba200000c0c9800a40d0b04420310800014520303500641c0440c0e070441d1441d84039901c440d0050000e01c100381410307500c00d580d40c400708028000840280b424514a6805100329a151042030960008509080441c0304000102e1a107007801c0d5030100d030308000c0d00360084003034500c03035400140700440d175420600a210000d2001d0b58140385c051030201d0002503070030842d507602030108808a180c1d180c00c0700c09490719500000040a0900c00d12541c0c1b41c540c1e100c1c400f0441d030402420800c012065086081110030307401d1001c1800303450503515240d1908a14002084405041c80600c00903420031050844070b0340d204d400f84580d01400e401800030102140710061121400d6040c07d9040074184003680310140c2c86c0c401c0910841004060400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203444766 1250 203443516 203443531
    0x50a0302130b060f04030c1a0d0b04061806061b03020c10050d0911040c02011406010c020a090903050c1212010501080720031c0501050a0e1803030a1b030b010206 71
    0x2429149031003a04080c1c2802c000590303015000143c030200c080c0502c0c02400c2680e003d409400c1e81c0341d4554450558610300e284c2c41080444d020700070f903000801c89400803c407105000d000401d403140d5401c050f44200410325040046161960010700c06a5441007215000510354040a800184244c6000c1e40341e4030413115160040180c00001c10541e80510111115845030175010030441c901418003082d5a00c1100305903102c0c03401c020f0301850162050040e100100b640d00350300c40840d220369005403087c07004994101d0704405805030010784110607215001e0051f002e6203030b05959200d0141142d003000c50060341d101041c901807200281e5002041e05103415185c003801e0602954407558020780c0c05114440c88040e4144048088510b405000300140140d01c82408090059510015603030054440074080e180c0c10448041c0100700c4030b025482d2281d0010407882d050f0000700d01d075661a90459004031613101c8003d480c0c070240084a83c1c40c60303100c40080030340d207010040c04c046180000d4940e40d014040c1c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203446016 1250 203444766 203444779
    0x206030612030c1903030c02033604020c0a030f17040303020915220b0405090a0207030315090e070e160c110301060303090e060a03021c050705181f050a0302 69
    0xc640041c2002120108500402100c4000e0050040d00c0031484618404400190418841010703140c0000141c1d01d581261140c0402c0c004003804144c0f4000c0c144c1d809030352856000c0046580c568640c0e10080c4200c400b41e0001e483c0000c61030901501030942c0d5a13030301c0c04104a0001455030341500d51083c030b42056140c60050784da0441400043c01c050004880100030503000074005061080080c480ca0a690504a601500a6545060741c5481c010b510400360016041313000202c001040e0750082c03050078820b04000466405590b041c180b1040c0c180c0059040a50311084d8060443c0c04001b8000180302442020301146400320034400c0e810458080c0e0000d2056010448007045058940710070321001c0903000700130040d96810010a4031441d4454202074070840c1000c0340c5942042c02c2c0703c0c81560b0300900142807840d2003409035881d108103402d043d1a10302580318041080c3e80c909810075031602d0034070100c0d29941030000c000d91110304040c40c550301c114a014800c0200352156240d031011690101d0740d9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203447266 1250 203446016 203446039
    0x408030406021602150309011a0a05040504020a0e01080d02060a1b110c04051509130b041205040e010e04020415061e111e0d0201060308030609090f330402060306 71
    0x2c0003083c4810000c1d40100651a0540c03050880d00c0958401e00d0410003c3c4822112040c9000104440c1d4076219000494000103104604090b080503410038806040850b55660754403410b80d01078000e800285003034009d0b1b428640038a90402900d500001000d0041020a0004184041c03041c4400d5091050104540c112108100709020031504250302600c00d000b0303490050006011100890a41803098407000c01056100745a51108115580c0c88200d000c070a84440d201c058020702d90700c1401d01001810000480c3d41030540520328000c2c0f0000703a90280c9070406104000640b1400011105c41010702241000500d41c0164a03a0b0350000e222040e003007682800000702c414880f444500100c0e0b2042c4241d000309141c19940020071403c04a0a848170750102d001c080b1309880c2c151102a00328901800401c156240c040311564011400b20b04403510b0180200d184e81c01e1403c0e1079002c2c590400f122500c000201081c1101c540035920300720302c800b001d18069000032150302000e41000e00852600a8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203448516 1250 203447266 203447287
    0x3090a271107060507050c0a14010e0c0d03030509030d060e04030305010b09151b0a11030d020610050118050d0302060f060406120b0402031608070602010c03110a030c0212040b031e040803040602 85
    0x413100c0100103c41611048c254074141341712603014200a40e481c5600e06450201580c4003c56011080c0030b006220288000300c81d201103000d0500038003c401c0c1d902040041600c100010300c01c0ca0003d008a40300031407a403626040c00780840d0750580c08100a04410072049a107980c0d000c25443c2d42d0307aa080c008903115001540801800750601070b00c0643c500c03614a001c1c041c80b1707020707610030310084c4200c00b141d5011b14204400c91311000191100740391440300e00d00500096014040d00380301c00c00c0c2030800f00c9040c0d55820000c0d0041c15030700400d80141c3c02800901c00308464400c001a800f0b001940c06008045c90700003070f003420444510b4050090f280742c1c0003180844d50b040c0704090449040c8450304020a44446103541c854680340301f84400743d840c02c0300d0711000c00d000b8050044070740c1800e4003031820724404080a0300504007503899081140640b0000c0000c03101400041d0003d44250400d480d140e140a060a480e41d103502941c0035161500752040000082d8460102c82c4c1c41548084003588a4003c5d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203449766 1250 203448516 203448527
    0x1a1021020a0225120b011a0a02030d11071703090c0604080703061104031a0109050f13080304050a0b0106050913020f030c1608030406050406051513020c03090a271107060507 76
    0x10490440342d030304e408500c024420b0710b201d498180d8410311660408201c0c41100c07048248541800785025800c203124070040000640e200c244a01c1440d03000301e18200c1e05542c0c1444095800741803516160000c4180042030504000f80c124520058898034a4141001051507a034001031100505003901c078605482d4150511003568000d691240180c02c24200340302c80401103d90034001d002c4900d00c0c0038000f0300110315a0f29010f01070314a074841001c41161948905005610003801600c0174442c1001240005800c2c094450007422580ea070a905d178094241000603a00c201c034074846106006000c400108804107040343c0c0c02045480d40a560350b401001e15030700c08806100003030803040010040005000d190380225100301d01c11041089150b0720707541203031608000a02e1a64100b0107290045074450310503401045411281d44c00c581c1001041000142c114207550000c1040800d5800b810540311a0398030780d141120000f030420320000092000084280c0510f150141c146030712280401c1c101030044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203451016 1250 203449766 203449769
    0x10e0a0c1806081006081501030b0402010509010c0b1815160e0a03050d0302090a08030a020a080a020c04061203030c0f080c07150f05101d0a1a1021020a0225 69
    0x30f0701590480c4295010040c000c140c14400e60105016400700708400080d0a508213050b130740e110003440b100e52038a0b001100c05810040506042c44206000007000c12300c06100c140c4074107142c00d040010030080240c05810080e0a10100c84108a15400e00150140c0ca10703042ca1a034206181500c0c40c0502000060700d202c0c0e02d540094001e0068440070f50349503a05800805401005a50201049a8490121744e8a1041c2040035005030495920310000544200040a09403000d1048883e9121303004001002c4880a40c00700991000b1403864000309074043c081d06280c40b0380c60600001c010440f84000d0810704008010342c210260001e80c1e5010019891201101303641660340420001099813001c900800b000d845100940d5420071001070181502c05812500341113403100d03440c0039182c0c4805000680003102420f20340e61200c070000102070303c0f26403151915001c5951072031b011508044200c11049030072400d2071401030042014100300e82e0001440d004035a4000c90405a144010f900d04c0d20705a1035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203452266 1250 203451016 203451029
    0xb01170903160c05040506060c1504020a051002010203091203240118060203030709080601050f0609210a06050709060507020d21051c02030609130c1a040602010e0a0c1806 75
    0x40c102c00801d01648250f100c003900c405032001c11564075981c0810699002d0300c1c00d80019076200103001710590603581c0300c1070f82052002d170139920041d849200289158820100520060f98040300704413610310108204038001080140e8103185090922803502190000c050112081030030811540c9a640304e480c00310a0b210075106580059512010025201e034416178410b400180740320008035844d00301098480c1290b000500e84002c0d070180c50f09008658000004195100441444041c0002c81d501002c522080080c0007600c803641c0e05103403010454002802e60001c0000c0b04605104d0507401c50704031038010b034045a100c0c0c40034005150071080d1021030213a0b140903a0201c0c10030040690000e003d0405011901c0383c1054030b0808041c035004a000c119445039001c02060301244903800c1881c00710f1601c601483c03da507900c0f07032619070842c40e0414111207212040c1e00001c04000081c1c0c2840391807507000d100d00c05130000d43c02c0d03501e40701c01005240c0140201400e0525840090303204950200307004092 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203453516 1250 203452266 203452297
    0x3100f060e0c090d1e12121118031e0607090b030103020108060409050a1b06031d06070e03070909030c0c090b0d290405100c0f050a0c0303180501090606090b01170903 73
    0x2407403801500440b00798403540007107000000007c0301003100c0d025a00300c140341a803505082072003010b1031104000003011100c0e054000c12000103000c40241d55050001c03484a8000c000030b05205200802e4a4002d900900d1001010b00c014401030303074801110360300140c0c1100d010a820b6402c0c10700b00d04110396000e004140000e601c070b100f0786c104024030100c01107403031315142042000c00601d1151008c6158090f001c0c0603400c40c1001803c2345000d1111f0300040080941100d001c0703606e40301e00208403281c420068002c2100041900f04101103042c00b40c0c041c080c40ea00900031404c003000810dc2d0400c2d9500020700400c2d6080d03c1902c0d1806003d01c401400d009603c074407500c0c0c01c1905042e40c4990030a11054074440c00c1c60240c50031280101c0405c003040ea62643d90074680100c0b504201c451320001c034012000c260301c0350020882c0c0302810042c6150700380100000500d1580c180380c820120b0314a507005c20103940c141000d1960301c0e03800009081203441110010300302682d9080c2032605501c91408113054040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203454766 1250 203453516 203453573
    0x6030c04170c010e01110c06030c070b1003050705040e151f060c020f010306060c060905011d0d02010e1204050906030a05010e0f010c05091302090d0203100f060e0c090d 74
    0x1c0d000902200355500c00c0e03c542e01826951401100d15103400034202041d940080340c0399503207003040b1001f554405200c1c00c080c0e0414000742d1ba907101c0800e040d940c40d0f461503250b840c14018080c0610083c0c0c020b000c21241001000c2c0c04000c039507110000c2c9010030002c076020f00f0004442c04480e0265020400488040301c044030f032140f00c003030078020741c03034800360b000d012030620301c1c585940a44035070300554440da01c1e82d507401111a510390300a0040440226559500d6404020340f0b812440d580c1d00501c46c1c10f10150140c20344880c00242104c450b4070221603540d0052513100c90003905c0c0d6084078250360042d1080052a50b450b4082450501c5030340c03008101e980380482c0f05014440104c2c0e08070050300200004d010200ca041800c45150281c90f5219a000035611600c00c507122542d401440003040103040c105003040e160b00002e080525065804546649a1180018020440c42403a018094174540c10400b820a150204040e000d03a9510500030200800c00d0000d00080d8800d0241d9803054a040b500340c038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203456016 1250 203454766 203454809
    0xc1d01110f1608060601080c0a02010905120405030d0212090d110d0303091202030304210e180118060f0e07090b0f070b06010302071203230c03090d020f0c06030c04 72
    0x2a0350740d150551071a020102d010408072000f003426130048005039107045581e02ea06409a0b0141d11110141095658030fa1407140040e0b428800110098007a4404c1a1034500d07242c28141000e01034416641190004100300c40e0031002c1d4826591421400da503501c0d00001145050417071a044c5031121940000b02100303600406074507401184840b407007100c030088000d508001c16139907800103540042c801a00800107859021021409804402051402005412840001c01c40700c50025000620b2840490014003003c10044200c0902d1258111300300070282c60709030b100805280c64042c64403003641300004160158401c1441c074016002641c0050b66840c00070300c985445a00c07c0d44c0803518641c4000000341203601a100b40c0304d500c0e410100968080fa91183c0440040c0070442c00500305507200001c5100e0b0140309088244100c6029041c00d0350707400d014200c0e83c0340c00d0380d015144045500c5004003890082010440c0e0805100c00d4520301d4403500d0349501991680a04c2e003140000d924060440000e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203457266 1250 203456016 203456023
    0x914010203150303190302031005060a120605030a020d1205040e090106090b06161506080d03060317090604090c030b040e0a0c1e0e0901090204090f0b010503010c1d01110f 75
    0xa148000e8102403940d805020f141e01c078055012400144c035403d815010f000c9009400859020600b0340010780002e031a400091000e411400100b4001100c100c50407030301200d60310505014040171001007102c040b065002811580d41c8420042281504a40d5403604902034400d80700500503a02c4050340c1442d00a204500800c00d9116440007103081c1022041d940c200f14084a82c030141016481d0315425107030721000c5010752601c1a0319509a92400e001610030800c0c04046041410b80d5808661540f8504020a41416202181c80401420012101e890355243c00302d9013180c0c0155008169048200001c0c0c00400228072000d4120f4140b980c5500c0c280004500004101d00c62920150503d44503a10700814074291902c05000d0140e205052140780315800e07800707038000f130217034004a07020703040b80d0118050b43c0034030b441211010100c0c1d07a01c108000d002c540351405420146c0003017040c00d2116000810700c4000d82240c08503950b510201c6502644245400502107200740100d4021000c80c070841c6a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203458516 1250 203457266 203457271
    0x71b0605031e011203180e010f031103030c0303040323030a0207051c0f030e07030f050a05070902090a06081504050f0601090902040815061201140a05060402130e0a0914010203 77
    0x201c0845109186260900b41d04910741a82d200902903510b2403419541030380e041e0089001e000d0391800c021700002c0d9810036130740c07164060118074120b501e0345441c6103010401242c809040512a400a00080c8064000001a05c3e80305070113103000000311080d15640f2512110000880c0c2d03800c0e40000c104403d1454a4006140c01c40c4114101c40046a000c03890080000340120a10002200c603040c0540705407181c2c008040001c00d02056801071a80c940d11004d10402d880700450b501c3d0001c071000d07024464140302140041840030410741c54041000c0020358203460a010345820701071100003045100c800d039010b00300a010041c0c0100001d042214452412203401c45500b400201d0055010942d640140244c50807500c0c0c20000705038103245280003080d040c10050000780c101c6a0b022600803480c909000e64a06c801c0108207500c154107055280406490300108640d028600402148401c404016120030440d0000d40c000038031901c0b18030800d8044c1c0303000c2c0c00161070040c2d0158200c900c01c4040d0300030350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203459766 1250 203458516 203458531
    0x203070b010503010b01140c0106050901080d090e0f13140307031d0a06090b1b03120a050121030c17121005040c08071803020402070b0a050a0e0a08071b060503 70
    0x8441e82d803142090709032003030300e01514009501002c82035032404042c0003814029454000221b0b07610746410215414600c240d0110010f0340c80503038010400394024107400f000e0941c100d01c1d00414981280b07100e01d01ca0000d8100317080c3c00d24101c1654140601240464888007142c0280da65030111070900605034045111038005030b01e80e0301c101903400d1408040c468111011501d801ca5082e150144543c80e9070001031000000c0c01c552103403442c034108240000e002c4080d580d5484c80f8503007060b0403064100d8805810201b400b105600c0140309184822500781d107916810703d05044086c0451801c3e8000c2041854811006a000700d186880c416030441180d1103107001c0e8002c03071040d0340e44500700001d40b550145214085028103001c44d464600c540740000c230000180a81c0081503590340e020070100d80c40003809652091a60b400e03c400c485580c054182c00821101003848a041000202522204080c1c0300411641e4009800c42c01c2003c4040305005003a41e04a40104003591010040d000340d10848010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 203461016 1250 203459766 203459783
    0xe241503090f0321040c0509041b0f1a130b03010b0a0201050604020f03070c0809060403060618090b13020409050102031321170c07060e010c030c0219030302090d060c020307 76
    0x1da03102c1c00081540c182440709210595085100c0f6a143c00035100504280c400340e90703d2001242503120415014082d5200d0b1903e48100081844c190341041200d130001c40c0b21640501c0104408011803104402090904100756a140006001803040440d690320100c50300c13001000004103102c0d0140500250741d41030b0024049603403003004100413840341da040c41e0400c034418804520420700c07504061804074403819480b85480344ea040050000c5e04250b004031030f1544c42e00000e01010741e0140d05070466410b480d009001180345607488903d1200c008240104660310360352611709541d11600403812658024000315620704101146909003220700078183c5180c40c041110107424800412440700f070007942e0b130350b43c0400110380c0c201900c0070001070302d81c0844084c1840503c00bc2136480c07052400300b0382208000a0742d00280070b00a42502c1084800106640100f046411402c489401341a14140c2c149401652690b201001409001618102815540c5024248003402d500040140762843c098083c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 203462266 1250 203461016 203461033
    0x7110717010f092a090e0d1d01080c2a0f010c110703080901030e030a0c0203160303050f0a050f03151327051e07090c020105010e24150309 61
    0x100c05590401100818980d0040682c4d000f00e200c1d0140210102d0410b01ca0610f425a40e44100082d505903001000150304260302000c406a088071280401721412880301d4400b0341084000fa08960005010f20428540001ca03110a074403c80e940c50030300074080c0c6048c100c0c510483c2e2440d03941e40c0140e0b01841d440d0f01c0e110640340030a00404c00301e21582020340081542c242180c0e5100c1032608001081070526444d560302a03251201132001d02940e401315910312050b8000740c010140752121109a809114210000500101e60b00800f1102c503034020460040c2c3d02d41d401401101c5602c603070100e50000b82408403d014100940d4607581c10408012140908130f403482c211603c003202c0510002e89110418514904051150880c640c3c6d00c5e18010002c1c1c075003482c040d0000b104403240508040304a44c009460511a807225845006442941803000b00000c2d03043c40b2250071060400b4080381d41414070081c6a051300040020100740c0c41002910020100d0108804480150402d44080f010340c00b85141 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 203463516 1250 203462266 203462291
    0x6010504050421032a03050601050307090905041b1e06180306050402040e010213030b09060103050a03081b1321030219020d0206040308070b130804060302030711071701 74
    0x18040c0950f07004a8900000503204038000310040c00d4040c2e0409064550003003d030000025280103540d03e100c0307010b5016007992148000d00700e03100184403a040c00010700034807002642c000355031000e460003400300040310b844504051501000c0009a85070b9911210303004075042040e0346603005a070381e0907102180240d8880070191024030211001c20000283c45204101088043e0000e030b40250010340700040c5210304c10310840c2aa44641120b07a412181d80c60b0030420451a40366081d8844580030241103507504617512191942e00c4120050100490342c0041403601204588400b6138100c11081d559688151440794107100c0310510031078451902d101185c2201c3c00f2101800c40c2e0095055004c0d10400b070f19002d5416181c1c0c0080ca084e0382041b00c0500f1080161076000c02880030f940604080390322081280780c8040d026800400702c5402d001c91143c800001388145081e0f9058410a060140e01d9659425045641c10150100080607200351140058290140d038561001ca42c0850001d0080079100c40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 203464766 1250 203463516 203463521
    0x2040903020c01081b0f090111010603060c170910020f0d05090706090b0c060a0c030b04020f040e0603070305370b07180b091c0506010b0309071421011d01020c06010504 74
    0x241801790f100003001410001200300000341403051050511600e0702c1d030b004245c0c6007103d10703a800890702180d8400d1452446504541122842641494072800320f1804940340c035100c00c0e1881d9848001500801e11900c000c07010b0050780d4444555000030425850070118241e0f03101c3c010711980b0b010905805c004120294144c08541c00c1086501c000c1c600780d00e41140501c02445804010008c25a982c80b0400e082d9039580020b00c001030555054903140c506050040402c807002070003151290f480b4900400000f040451803040b142140e040900b06d46140040841034401800700300035580211150b000c00308044200704600440075a9070f0300c030b40b060300440401001c100d40c0c0030b095801001804206080c0c0380841540c1804030b10181e0601c3c4003800d03a41e6880c941802078021816081d40031080100101040001034010080755004d680f49105200120b034200d08040c10441d41148806000701040009400c000b241c2e4082e1003541302c1c03c1c80d242516900030b4100d880b04003864000d440000840340703001e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 203466016 1250 203464766 203464801
    0xc060c07031709011d060904060602060a0b0316030308101a0d0b040c0219060609020f030a0b0f0105090402033c1503060601050a0201110301030f02031c1d01090302040903020c0108 79
    0x617100c85103442c05a4500d49519040820b40f150b10400400c56000917407614021100284003d4008041e1410811202019241a100800d000758801c88401c0500707200b00c64002c007243e4041c100718a207607c429141140d42c0c440f0307030040e210080030001064010f441400003002c1c101c00c41e200c1000b0701c00d0b80c28200010365030f94104920041e8070162a00800c02d0b121b0503085055841013400050381c0c0c0e640d941c01002d03a0001601507440e00d001008000b2800c0583c0600000654200c030303c80c1100301420b001170f0181c010742c0d4109001c0c40e400b00005100b180804140b10319210b840d8845900c40002c41403846502039907450340c021854282022942402c20078001c815a050028094039040c0e0750903004640345c4d0020602001190b40300d8003501115010100218040c600601c0c14203030b942c41c81d0051504e01b03c1c501040d284135400316103000c2c0c074940d0300084101100510034440b58204644800482d011000ba41019501c1494031f00070500f00350b00001e00d4121440c0030f881744542e6079038815a0000c80c4050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 203467266 1250 203466016 203466019
    0x8060103090c17010b0d2109030507090f0207020916090503010b060706020a09031b060f020d0c080a0504030507170106050114070b10081f0b10091203020c060c07031709 74
    0x90b440180801c4001d5407004000785800c10000038542c02600005112001c3c540007038606c0b1603408210002d0144c02c100c1d2400b69082420004102441c6a03035044d40c0700083d100300381c5c0041d82e03a8032140305a409038044604d015002001c1001501f89060a52062454100d80344007003803a00000165504040c040d0b12240440140154104500d94880324040d52107541e0000400c5034408008c07000582c4d0010f845000c50758500032001791400c241028284809145020056500c03002c0301401031030b841900001105c1c2e01040c0a07855840a140c01d95540c022608018101e00440d0b102041d804a004080c03003480428000a2060703540e580015a101d0070006080031101008001100114503411000c03a00300c20050244042240e48016032400c2c0b81440c845a80e0400c62076000640e515501d008020041d00304941c2910b07c48601d2401a155a13040d100b03420032034142e2040d8005160003400580c44a05000c6c02503641d4a01c42580241c8407079240c001142d0806542c002c100300066140180c4807800310 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 203468516 1250 203467266 203467283
    0xa060c05070e060d120906020d08090c0d061d060a0b0a0513020304020a030f06050601020c0a050a0e0c0f131707030b040b090708031603031109010804120e06190806010309 75
    0x42940301c031902100180743c507800445180010300001c000c0c581030207104070301e603840d0030650741000c1000b800c00d030b107402210041008030305c1808040f600108035030241c1a01200c05101503103042c60600e001d01340700c42c04880c010541c660003400e0400b01007501d5120b510400001c00080541038104030902000d4011a80c11510065484080740120b90041d600107000422421074140d685d41d5264117002a48811a0a69211401d0003455601040300c420401c008544200c581c1d414a00440c00d0710480f84030340240201070501280c0405480011a19007018079419140c4d00d034400a00004004054440c1040f00320f00540d00c00724200c00481c0301000e60f03034800c84002e50307a180c81d115080300d0f04000d403403080d90303016203000010b0110040000f4003628184101301440007001d42030250031110050b07451000d14034108040c00c500d0782c1c045c0109500c203503c0144032807607046000084565559440800b41c000a0001d41c00381e04582321003544091404a64507000507030b031004011415907080740c2c0010200728 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 203469766 1250 203468516 203468519
    0xa060314062517040c05040b0f13020a0c050a23070806161209140d020c0d02010324060903060612151806020d05040b1b09041d0a0302010b0a060c0507 66
    0x400c9000d8025001c180c1d00e003205180744080280381e650f41003610300725008400402c0030030044c1860b006031a00750100315103240c6e82003008404501c039222010b05130091290300040d0075849a001342204403c1d260072a0840e604466285020740c48081c030688003209030308a03c01c5002d607540c40080c25000f951403c5015100b1901d46001b095200c211800d03105050000b44012150755181c0d44c802c80320201d000721070500400003030340342050411080c4814a000c42d04048001c01c010307290042c400002c13039420b117400100f101800032003080454003052006030100a0f42000034580b94440c90501c02c2d02d000e0002085182d680b1a0751150740e40d234030103004100402e01c0400259201d00c0390b00c80030080d000b4440e11200616240d482c48100e0f8400d465143d42d9640d500140008c0c003100000300e03030348440101240f080c88203200c603215240b8040e04440921a44d112000c0881d0f0300d0758a011005c2e0040e41804803120ba03082450064041d01942d200a4001d00c0d1503a0000350061103802c0784034409070000041c2c00103e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 203471016 1250 203469766 203469811
    0x5060319081e03070903030915320c030705010605090906060915030a03020a0c0f1a091f02010f1424040e0a08190509060406050c10050a06031406 64
    0x190002c52801020240b94510035030900d0a10000314400c1e202595400301c81800c618015192a280e0342042080c460b942281d0039a40d60042034090a8201c002d2800249201c030f4049540c0c0e00c045110202c80b01140030500c0702d007001d0000003900c07009100d10020f00a003502c990074400040021112a019135000c440800ca80c0e081c803021035900a008031941060a0f03202c080441c1c5803e4003000d0880046e80700e8030300700040c8500d134044031010f000d01c584141c00c1c081c80e2040700c081550f860b2442d031904a8002540c00d649503200c17500c81d107403140b68100e8158011811070029009143c00d0002d40c4007582007001180000c003c00074442d1250000c48100c3d64440f501c8030202c104c4407a240308041c1c00c1903580e4035a45500c4801c00003a00341d00d11940c02c107955001031044600c8203041c400586814000c0910044000d6505c0034103442c2910780b546000340d1104a00c1032060310300b00010008240b80d41c075007810304c54010f460303030003000641c0d009150b900130300403000070f07015550740c8104c86a105540d04180c0c40f000f0b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 203472266 1250 203471016 203471033
    0x50a0c1406030412090e010b09191518030c260105040206030c0a0c05100c11070602070306050c090d200603040803060d15020a0503060f04021603030f090c081005060319 74
    0x20071a13524108001d1502d684000743ca111003a080b0855a0401042c10b0b03406103028800c08481d03640c1c5900c089900c80c94460300030020702290309480144440ba00c5110542e1400c0306600d80156003000e2024000d581c0c42c6441c05141c9001a14070310a48080d08014040d0f242c14042c590240380d01812072881c40d91f0300a04101c00d030b00411003401c1044081d0500c0c4004c1402046801c400034941072002410304800e0070b0103030215041440c3d20781c01e900206410040c068011800e003084942158000c00c06a451541c2400180703d0f00d610350350f01030003844031003050103090401d0802c86030000ca41212102d10010412545000840f030003001104100001a098100b4900300400b03948650048400000e46140240c01d0342c10402100002034008002c11409151115070030748401c40c159821864482110118202500c051501806054072a083d9a840026a0384074403903007a000107404c01c0031611840c000703444905526640705250300b85000b0824620703000c60035658031030fa074106103c0c201040d591019803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 203473516 1250 203472266 203472293
    0xe0f040203101a130816050306040512180d0c06030b030703020a05100201020702130b0f0114030a1104050301060314060f010b0403031103190f09151409040204030807050a0c14060304 80
    0x203d41408001e03554004a401803010b8450345002d00f14444070303040141c070552890781c400c2c1d101c0c2c0e00c00c1d801e00000c98408108a490354001580d41940c4119056800c090802c0700c0b250f050f080140c051052050180b184030b41c00650b5201c2da010300440318003604040c2e898050380006503020b681203608014a203840010f043d243c14181c000941813011a0300000c0150442101e618242d80e15010318103031503e410321047e10031a509090001030480311102d000c000c5c2c080206405803899881544521030020f4009880013484014000d1181d10340780d14201c078a400d006001416a441000081606c103001c02014034140d6030003806c5d036420146961021901051110440f0382540801c201241c0502540005c84101c00004e44031907001c3d14040c000280209038582c045048141c100c00b41004099109003000a403c4c0300c020029265a02c2000040091040c0c1d48010044803000601008108000c199112014080d22400c0a8070360b4410121031100703200082c050b44500100006000101100101d14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 203474766 1250 203473516 203473559
    0x207021e0924130f110d05090604030507020d0302160b040e010906030203030a080a060902131d06091f080703050f0706020705010f1b0b0702010e0f01270515070e0f04020310 76
    0xc1d001041c01c0c0304c00e04a0701822156003002c2e0380094500300c5400c1a0041c0b580112040004040915054078010440d01484000034441e900700700c0c1880502d442000b46007004501c8112180000382d0b070b80d442d118103601a00c01c90200c81511000082c242d02c26124030303011070380c014010b10700d4130f44640b604542f2000018050045d1a548242c003103550111072019004074244d81d00c0780e114013801c040c0d40f00041d07206110031346101c2e881c5404000a54841c01d428582080d8240341140c000384035902d90032602001e54102150510600ca0000b00344400062601020700d04002074031500ca4860f00b0480e2503102a000d000d020400762030560354007911038260a80000501c00b1000e00e40740300d5a5404200c1c42e400d03140040140e442c0c00010001d14014080703007225041110080002000303c117014403e603011847c3c07200440010100003024482305000c0300d19940c4582902d2005071414110140959110508941c0180b000210a480c07600706442102e0040c0b1841641e551641e1608585040c000303005071650 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 203476016 1250 203474766 203474771
    0x21c051009110307052113031e09031101050d0911090c1905031302120708060c041410020a020a0602060708160806040903050f040806040614040804180207021e092413 73
    0x1046d0002000010ba4090700f4031400d0070030940c1c0141001003500c1c160440265121803415100020305030490f080e801220350051290840c0d11154005881c44e01884075224007003818003403200200044590f4a146000b0101c44d098816214100c00d4401401064001100c0302c5c042d03c0300d001d006000f01c024540c40311040c0b14a00d03039540680d0102e107640d10030f4500c20341070341e129050600101009000302030303000203010901ca0816143c401140c42010b00884824010481c3d4000c1140c481d10074400c90403d079401038940036225a039214001c1d555030f4101c070f840001030001004202e40310f07181c66a45c0701800865980c00c800f600c41030100801400000c001711f040c00b501700414600c1800c0c90020344020540507002e002c580c9024101030090700c442009110120908408000004201c0d01c141d0302607904d1868002140c281c640d0f09072000f40318080001e075004440c502a40300303da2640a0080d044401503e01382401e44400310032150401c614546841300182e004a00074283c02d0036000f0411011818001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 203477266 1250 203476016 203476057
    0x90a0905011107150c020f0c120c060301031407060807092105060108030406120216151e0f0b0108220206070b0a0c110601081b04021c05100911030705 66
    0x8425540040c03400c03581c011030001034801c48800d5209100c1c81c0c00d094000390140740c984296250701c23458800300a030322640745100c0e452001d000820007031411003005010341d0742d2540c40b030618800b012485000100703144546140440c00728454118203000d55060f032650612a400d2000c07500c561541c00c903060041049403110b00011900412038980203080aa0141d40d0781c0d82002e10007402c03000010420a4a0340c010051481b20340050210110b400e50400408182400d107000c41101810180c800c01f0790f081000d0a0f042c1704140645d02c255a04031f26480700300500d18240c0d0054a00d040d080b2200103400c1c50041c01e0040f00b83c0b03d00080c070f105030320040c0380b94680380c0c050b43d0b00240340500b501e801021507659420034800d182c020201d242501c200d1001081c50f90300d494909681c607400201300c010824020700c06042c0c0703901c407501501c1484c804004034202e1084000c42e02002024100c80c81d100030300f0360b038100050410603071003103c4c954407420144910f550f0321840700b519164401d0b2140300c54005000103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 203478516 1250 203477266 203477291
    0x71e170a050d080a0b060405101107030807050c33090f040501080a030e031b240703022104050d06091406040311011109130c0203190c060501060c02090a090501 70
    0x2c620001d001a00c0300b03c11400c00345400c40c1100d8103d5002401590108400c0c006951084220414090f06d4588101098021f1a01f00e003841490361000344040d00110b000d60030444082099807a001c4191200304a80540f031a854018548400b5031115108000000401801d002c0b8000d04404201406541045120303102140494100740d05c281031a4008071f00c603034101035002d0110181c0480032002004980480c1e804030a07424420807886109103841888400080410b01460314001c50f030090f6103840d0402810301070345650380240e54110007c000300c403086d4104001001d4030305903070f00505080d108202703d0366410010210464107540c4422980300c005035084003004034901c5244250354440c03403009a00142030075116550b1141c0400700c002c0c0f0071100d19440304880e81d9544155107101003881500460180c4c11446a142030449a443c0c007a4041d4410380c2144a50502c98401d520400440e031f80c1d80c104848519880000039807260007400411007041351508040302d070030300510001821355145c1a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 203479766 1250 203478516 203478523
    0x1104030f2604030f0507050d0203070e062e020705120c010305130203030a120c0c030c020105070f050d0203090a1212050309160e06030f010504081624020705071e170a05 74
    0x600448131558031110381d02c01c0200c00d100720310003040c4c1690390000320452a0300280e151f044c00c0c01400c3d01b65a02100107080d5940c0c90b2100300480700d08051302d65450011140d00f8a6510f000c54400d000f52152110024150500707440c0b050481c8281000380010300c0031440114050600980b00e12418218000c000700940d8052008000e80582030711210304800109d01c14405540369407600c80103011000c40c0b5003001c2a00301c0c5a00c041190f0918000350f6501c56403801c42c20000388980c0240c41c47c0316000700200410340010040c03007501c80c1150b42a03001c4d0b0782d550001210504000700289411100910203020b00c0c02400a540c20a03240e50540701400181c8119040c03800f5070381c0c40300c6123844c5142c5c18003800341401e0040707140d034055482c02409a80742c142c940c1c1d101841003914204087d0226192841441203241d840c40082c3c030703c0e528103071010100d40fa400e0b000e034004440607903441c082ca680c00500d91159402c0f102003618403940d881803d0b4541801c0c080b9224682542e5a101d000d0034162a0001e142030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 203481016 1250 203479766 203479769
    0x14090609060a090e01090e030703080702100f15090e07091104121a01151e0c06050903030f010b120703090204090f0b010f091e0902010917010c031104030f2604 70
    0x650f2020401c52a100e0004c00b2074a041e80700c6450145070010201d4144408001c50f480c039034050810203000d0f12469002c914018002cac14a05250b450620810220400c40e040755214101c1502480445616154000304480c80b00041c3c60147c0d014120801481d5030a40254107104069180241440d40ea100001490a1564000c580607400c1c0015040c080c2e40c0452030501610088100d841c108285440c0036103880b680d00c0da85650340002d0f00200c84176500c1030414104041d403160040c043c030709220b1342c11656038009503401c1035120009400890b400078483c054030001805045a409107482e110400c2d0700800c00c24106a8005881c1c2c160038012848800324254883e03c21000d00020f50714003202250646043d820a0300400d040c50072903106036030001c0c0360900140d403099000480709880d20050340c0342003a540c000610020b00704005450300c0c0e81980500180c29040d00c040c400710480d603d2244940c400d5010041c030002c4c84030080c0020610f60401c095a00a03407440081129452409030100c54005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 203482266 1250 203481016 203481037
    0x105280b010e0a0906150903030e010804060b0307030f1a06100503070201060b0418060e0105010c080c10180b010504140a050a1103101e0308030c131503020405031c1409060906 77
    0x85d40000c0140f2100201031824040070351514440b0681140d80040075012504941070400106101140c113002d240e901030410308400900311070a480d542e1401548000c5512000e40c2d80144120051340c0e0741103074083c82480707030300010b1986486100800c401d582c80d42024022200710f41d82d8400200394000d01d00001d00240c00d00c2210110031059a1681c2d100340d58503034003e500e03404a040c00402003a6045200490340b56030103040c0c5510350a80d8460300e03181ca00321340318442a1500745251000b6205101000100240c00f0b002c48202c642c1c0c80c2c0c01070000392a4000c204110250507080050fa07031785017540c02240c00c8220305102017000790140b5501161a041078500c0050940c10620030094402c10080342e0524100000070703418028a180c48030324a9002c001d0403400c2400740010a49010301032641500c02403d071050a1022000d868103004009401174000e103402031203a40110002400648960219250103070b170307110754403040c0c807000c421281c01c01e00c07080b60008000d01c40d1a01565580713000d410235914 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 203483516 1250 203482266 203482271
    0xb130f050105070c2307050d050c060f04030c0f06020703020103020c010e1204181b030902060d140a0b04090506041407030b0a0f0c050a05070b19020315030105280b010e0a09 76
    0x4141080010400000d005e0400c203d8440300e020b4103242c1c04180307041100c0301140c0c1d4188428650501505140b03061078104d40c4120001070501d0400382610141050303d0080554042e0280c54121441c40c680741401210050b074041181040150b210b600140b200140d171701c0000c0b407404103201e8814680740c80100414242040400d0a06c03618a41001e8003240c111030340300901c00c0c43d5442050030301805640145004054540d4440c200799142c00c3e04603140484040d0f4104811003503c40c158456002c103981c2d6005a40c14111035034850320301401501c3c0078540040182851303031607940e0f49000346500340d16034910034010200e0001c042034100031103520600d022040440c0710b428240101c0c00321140060001c041c00414000100e03850381c02030039903031499802070b1428403c2d1200f40709641c030340c1d1445156200c40ca00000420a145108904440324550b0590003400351303441340c00e884224168800a460b2891011030030007000c020305600000c05154040c181540014500e801080580c0c009410400d00d840c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 203484766 1250 203483516 203483537
    0x503030a0902010e06130312110f0c03070504050f070c0c05040f0e0d02010c02070303080a0b04020705010f0b100e060708280801050907081807080304120c090203040b130f05010507 79
    0x5030031110304c43c4211002c884007450001c4511040020f1120303408041c09200300c0f00d880e0444207000d1403a5000200ca40821504a40d919200450351401f1009403603020b4018410005102d05003030143c58020140b4410300f01407503840301012640c046420f8401e540010310f09800103119201d9100d50240080b0811010500c0190030145030f24003240180c94400710380c0340904070302c005980440c00d00d09496062600e5402e5444206400010780703400407505500074400118101001015400b50742c82c0d500c42c060521a90751103204020616140e046540c0c0842c0305030046840c1458498010034100b0310440b0100c1c10007000003018503d521405102c0205080c0c500c0b40384452a4000000d9401003c2c12181c0607110300d00868010541600a42520031451240f000616440c60900c800809040c910b000c40742c13601d6403150ba8400e1458481c0003903455041c501d6022940c8007090007100d10447d08140d040c503031b54407482d03d80b690052000f8002e8030414462408500060001c3c041c46008a4065550760b0070340 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 203486016 1250 203484766 203484769
    0x30f0e0a0606050603061c08091c0219050102060115170c070b0c040503030a0f0201090b0f010f0806010b090d050a06140f0703090c051509090a021b0304080307060c05070503030a0902 80
    0x700c42507001184034940030300030021141d0301c1c03207490100704042e4500140380400c5403904102a02885460390340c46903500d41a528180c4a032b503803c0003064000c403210701c071000041612242c0c2c180d03240191801a0010700042c01601d100310224040105545840c003c1d01368081d040100381d0304242d8101440c0f150005007402881025103916070403501c030520380e91400c2c2ca0080040d0f5607119900091082c881c98502074a4240e0007035000c4091642c1103100510540341800c48042d554500340544000c099100304045810440080c40506894600c001c0d1440c0c2280d080801c2940c40c0b400d801140c81e0710a00c090680098024003558142d111030454044079802c01c03101000c004003005200008051804c40c9150100340340030042400c6803019550041084811040c0400a1095400d0f4a4015801c8414880d07084910390013070896071700c407450301940109542945900c82c4100d06c80c40708203900038045400440c0f902d0b8090108407143c6d0504514007000e84c0c0c0c407241507400403500a43e089582c0d407450000e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 203487266 1250 203486016 203486021
    0x18041a07050d14061009062304080f0105060102010509070e010e040620090306070e060d0c091a041508010b18010302090d060e0c04020405180c0909010e2203050406050a030f0e0a06 79
    0x8105c0301d080500c14103083c6400100f03100e80071006014107541c0351216899242009007120041c2c214082555a80c2820200b080e0281c18103446c03481c0190718020005081e0000031640c1400d8a00b1650520102d91800030f002c00c5131040074200f9110640d03240407503810701103070b100c5010324860400d180e10b4981c46440209800c00b440102201c0030b0081840c0b1424990361510100c46020004d90b00c00902004046011070700400c09401c081001c1e00c5403400a07030b000d40b824025100702c030340c802d1000e840100d400034100d031060400e01c2222191710b02884120028580c0880d00700c031208041c54010306244010f80084c9007280c1001080d180d0547d10311080c0507250741480300c4203085905803001d51906240030301180c062100810000840c0c0002d2010965550100301103030f014540081c100c038919611844c0f060b1110b00705640e43c204203052111050458456140280c1000f40c244d110342c3c2c100340c9000020348040d88880c008800701680c2e880300724610a02440341c2584d5105070002882a01d4217480c04808 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 203488516 1250 203487266 203487289
    0x6050705030c03010513060302040203010605040f0b0f030c07030c15050403110109020f0d03020106051305100806060607060504080c07030b1819260307020c18041a07050d1406 77
    0x1000800c00c10040c080d008101181e0444000b035803000d546c0b03100381003007200400c4550070007035116000000016200394003001510540302852003c48d9046c2c0d42e110034040c144240640c5441441c403c3c80010384920005000d01a40360090402e90900000390355280d030711042d02c41580103419074407020700040c107902062821010450000070840c130309840c0c00040b10402c0f607441080c03260b5050444041003610079042140204806403414094410501c9110041d14040380e00000740d21800a0000c2e50120000c1c001e4094540900128540600d94031010064000208142e4160000700b1241c0780f03101c1c7c1007004800031401600e081c20142084840d000e82c501d0040206031940d072180f1000b09604000003010140c042d030040500d003d04504825000c2d050010f20070700a6805400710400a01640210700c01814860031115071020152020420b088542c007a6409806980900030400d0410403801c203840c0c0100702405c04604101e00d85081009485c00700750300040702c2804a01703015240c105104180d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 203489766 1250 203488516 203488531
    0x807080c16140f1e0409120e09070e0d0f050a030f11070501080109051012051c050301031a04020103020d0204030f0b0c070506070311040e07051e0f09010c11040e0601030605 76
    0x82c5141d20700c000185110040c0c24415100314030706001290074500f959030090704200064000d00407140942480340303541100c0c212201c0401c0311282c030866607180041c2c8151142c505601da402110301c1c44828000c035042003000071039040c0e0304540a8400b261080040c2004244660b640180b10007449034003c00d07403502c0054001c0258041d80c07050000e40e070030002240c10340b10070580000d410703541c087d10720105c80e000b80d1021541001d4098140244030003c03c206822032008000c03d150000b100c2c100716064802448003030407652408581d09005d40250448580007401454054286801804440100e03841030340216980700000e68180200701c40007120f2940010319000a07400c00c003030f92f2501911000c0084c0090b04040e0f85103c0c1850300d401d850161800f03030918000c07840f154502024098908c0d0b0010383c200f100c0d01d60343c92181c0d80070402d20003150010440801e42c2400d040c412001590101d221480440305203a00080d070f80c8003503e8910882c040141080300608981d450f50410b902180c0c2c1c05012138 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 203491016 1250 203489766 203489789
    0x60b0f030102041202060c0a1218051c020d15060801090506060613060c0c0b1b1b060405060d0f090c170105040c181d011b0503060a0b070807080c16 65
    0x2080f0149448004c960f070950141d440c96501c18070f0b058428100484440001c01d0111410b2400c80720980c030081c2c5021001c1c100090074520343c1c517001003144059403070110007010005000c2da40c3c01418000d8401101510811145d4110740d4002c60000641d5556082000c00d030795129403500a01c0401c000c4a40c20600680c0d01c1450080060540c801d1900640075038418448074003000700400c40e03244036900007840350030340f099202c0f0045c80c2d5400b141e4a0200c01601d013441014440b119811021101a9041500800103403400c0d150209000d030a0b00304014803c02c0c6e43c0e9a110114100075907000c2d6103003883c8a00081e150807402c4c440540c00345001420091190380c0740008002c009241740100c642614400c0c56070b80fa80c550b81310b103404003401c008101e1580a070300c0b80d501c91191034815000100d404512610195202d601003070101e8080c0022180e00d9848400a0010495624030318000c0c07011600604c034903031920b28191100c2c0c4007940005201035280d40030480b5180c00000321000300c0064031000404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 203492266 1250 203491016 203491019
    0x1201080102250f06050403050408030d0207030f0512181905100606141204020607021011240118020403080a051c0209010c15020c0109151b020a0f060b060403060b0f03010204 76
    0x40301a43d81d810740005000ca6599000f250600d8040c5003600c3c001d01118044a540764980b48003240690801e070380440c0424056550510014014019100802854074130385400c4c0da10340f80040007508041c2c44440d8180150400100710600305c2200c0d0150500a0006141104400b0301c510110350080c1d00581c10886400c005102d5645c2c500111103200440300143d5246480b60700005a8502c1040c10003580010006950503203982c0200060202c80d6030307242a641d010800481550610764549804950000d1941c010321094028896031070306107001d0b11005060646941d0303004000d40c8000103960100b400802c0040b00c80341c1101d4600712000701c00c90b0170760400f160000081c0034502442c90040203140140e40c189008520b9030b041d201c0b1188040000d1100c0b02c0c041c20640082d50300659181c190504140c1001901004420110416810741d40141000c1c4040d4561800741d00310311038203c4089480701d40505060b0780d800702074030155000321380c0081c0000f044130400803030014049601d802640113120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 203493516 1250 203492266 203492273
    0xa03051218100905010221400c080d020f01050105190e040212060c04060201182303040e10060e030a1115040905040b040b0112020a0902070305120108010225 69
    0x202e80d040d02d001e0000206021002c0e00e401ea01a02550781000c80c15680031413000c10340e00c000c402103401514460100841140780728000e0180141c0c0e91410340c2014540d08282d00c02071100100f807000140191001c4002985405529051001498038035005134011840e0340d015400a11400e0b00500d0212040c82d4001840c010300400c84440e4400d002e112940c00c0000707015911045245115583e0b25000d492080c5410901c000e225040381c0501801036182c052200030f403003c400102e24100f42c01984031b01c0245560368008075202c1104c1100110781c0010710000a44d602401340c218040c4003420501200c0c1420f00d000148650b44441425109a100c40011408031b0104400c03406003080c180c45082d0445259140350000e442580e0103202038071302e441c04210a114170b20b6401402113200c0d8481c1c1010342d80c0c421480c1440000004083c1d03101142d800100403100c1c19900408980c0c0c484d040c04d508041c80c4002d241c81d11701c42603201c0e030840c0c1d400140c640310410450344074203103010f214403503100760000350344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 203494766 1250 203493516 203493523
    0x804030c0b06030124140a030c152c100305040317060609030f0106030615030503031504060905070207060221040911042310030e0607120b030a03051218 67
    0x320040d103a2060038020400300d842c290880d040ba80d8004c0c180420480b0400710710040c845861041d400f02a0003a80c90307091a10700112500101e076001002130000034103041003148030b4058842160140107584080d0014149010600c3c0d140380c6404880400c02c1c003006003070061101c040d1460004240c030700b5003044002508030381304e600d104550400d4400155640d4003c104240314061800b5450700c5000e8403101c00c140e05402081c2528490030062211803c40c85514010402e1400010072941081c80044c01280800e00360790050600100007040303059a0300c1520341120015184900160003c640c1030064a404011100d54012080750305ca009440782c04951696000306d0154844a5803124484000b03a0582c1c0141c1c0c019168690301c0e80f03001d9000782c044041c1c090b8103000c118082e601c110818454580207119402c5c4500380700b03020b041d603951103540445005c0400d555202500380d81d141c2c849810b4034100003207100f40d4802d44032a42c1e500d00038220041c503a500203002081d02d50a1100c0101c0e20040070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 203496016 1250 203494766 203494787
    0x90207021e0609030f1006060504031a130b0405061b0306030c0f18010b0705010c0e010f030e010e0316031b080702090a0209030307081209160b090303040503060c0c0d080403 76
    0x940403404664031a800194840c400c0c82d00d80fa615208000389031185c0d16010401030680e000200d802c2210315a1903500351080e0007544400740c40c0301030450fa03108d61300c0041415281c2c848417090584c6132280039651038100b00074094a05903106ea10440c04c10012144003154121b030201c0d1030b1140c40c15494034400003907560782c0141c1d03400c0c01200200011010703a1200203c0d4807480020f03c038030181c50740c0c40c1c0c591804107800205041d2041c4d800c1103903101980340601e441040d0510184d5a5111001c1410820350150100c5481c040096580e8210420b5000d024805404c511603003d01d110349601c81e0f4200101218030000f107990740c840340035060400180b240c81c00c4034995581030b80c140d940d50340d950355a20000e0003041009501804001056001c0000c0100280000c0300829010f40540d100c03820715540e50790840e11003418501c0d1207001400490b0040d0040d0645130f000604a900d010707160720101e41094029a0920062200401c100328841c2c000d00c180c0076028001c3c40c0402003480c050328028410440c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 203497266 1250 203496016 203496049
    0xc040902010210020c06190510050d1509061e0509031605160602030a030f021c0b0604050d0605010302030d0807171803030f0906010602010b01051c201309020702 71
    0xa4044400859009200071002c00c2d006040440d1640d24030942151208030031180d41042140e441c01d03044040d203a03486014040d20b100646c400d501405c003418000b410000740d40550303214110b550140c105a0b0b181c003601c003a441c41407502054003103440800246201d01c00149410181c200f4081000c0c000c800000e860040c0e402d41c0c14007003d81c0c00380c20898101808482c190070b03c0c550300c2c28042000f94002000f03040d000210703502040f00404143c5241c04a02130714000b41e140900140b159098864143c0000354040b400400051429507100001480760f00d800008962a64030750004009510b800c0c00119014803407420504681e18110100a082e0008020041c1000c1455004a4803400360358406808210b03900c002c03a9940d0411400030070b0180421210b80f10540b00d4080042112841070149142128060310307503608140b0042d9001903090b1b02e045041221503031b901000b15000407070003a08180020300e5410581d5415860b034400c2040e1603250089801340e4010815003006031100c201d0068240b15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 203498516 1250 203497266 203497271
    0x6160803060f030708030306090f0112020f120d0c021309020d17070609050f01060501020d020c01050f1210090e0102040f120507090e07060318030903080c0a080f030f0601030e0c04 79
    0x1125000100d0b0a001c1e81e15458261040b91004982e82400100443c0103071002ca8251a69603111444004d42190034051a44901301d003a903800300500300042e0390324480b03100408002c2002005520700b883c1c02131413900c40c030014800c00c020b9000e50411040c0d441c003003500c1d0542800502455004a15038a55407500208007250402c81a5001143c100503100142d600802c1400380201504095940341e5282e8000d9005500c0c000c0f0004803503000140248209070a900541a03030071719040103546c0d64100743da2400000f041040002101201504c845100d00b90398000c040c446800c1c04290b10888135510f200105681c8100818480300c00580c2045040380d00d40d00000140d11403500d0003c1c188581ca43c84485800c0c01c003000780c42c000c0c00104081050390510350b402c20542220024201054410388400b6000c500d200b207017400810004001426484082001c8603d0940303181ea4451312584241088140c4900c04000e1000d40580c000a0503003003402483d09102c520400c10095840380010b0040600c1180d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 203499766 1250 203498516 203498521
    0x3050912010e0a080405090f01030b130f1403070b09030f091002030c010c0801050f0904080712021606030204030c0611120d092108090a0b0a0c0c06020d1a06160803 72
    0x100b50441c201056000b015121480558581054107420a000d07451003901044006129100600b490b203048a420441d03111268950310400780114081c6141682c19813804101c1c00701061f44402080324020120b002940e44194078180414002e002401100ca01d4000700409c1511200800c1529500041100c1703a10140110010a03071941c800d00b84040700d10350915804094454010382881c0c12201c0580d80645201d5006d41002900c0074202e03001440d10703509104040200c4c2c04c81ca622000c404180c0119138140d03844040b4004184065400413000a030002828000c00c00310700c60100c01003505040200210142c004006d49580340140703289030400700455030711300c0e0411a41200e0340047c1c101004000e01e1030b10340400d610442c050240c01022500391004202c05d10f100089401e2165008514940d15031500255900508003074107941c820002080070034008070b1414030041500180b80d030400100e04400c00603102d03c0d4a50a182e080c4107c1d000d0100c1c0d00540b161144082c141369000541d2580d07903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 203501016 1250 203499766 203499799
    0x5090103020c160305100902010212070804030c091a040b01020607030c031e1b0c211202120a0e0c15030a150b040f0f03020f040203070e100f0813030509 67
    0xa0007564501440303803140902400c4480c442c50303000025a4045c1054980c800c1a8600600980d04071802c000c2c0143e210048000d0024401d001034030540340b18096a0745800d0307072a2944013660031503811030314101c0d50321031040c3d88950040c04000c00410040c0c2d0140f05c900f00c9440040d4441d0302c010199002d150715440c01c0e104251081d4004640c2007040d607040c0d1198502c0c0010724000b05488000911600d0b13041022600c2103000f10106a0600d9104060b043d201c0800482810701d002c034181d00d03400307001c2110b01401c405030706400940746001d0216088405490404d0100c0160780041144450075080035040c4507a6450750100621008841601195252200c2450800802c103080d100b48030b9542400022407044c00340c0c0000d0080311114030080c440e03642ca4502c2020580500d2000030f50004a2040400007802e05402455025155040c0381c5488081003000c12680b4a441020000192804505c28005600082416007240d401e406200c1c856015581c00340862140f03907100303840b0b508101c0002c83c54 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 203502266 1250 203501016 203501021
    0x8010f1e06050918070909050c130b0f0405030d050315010903050607030e0c0612190506100e0d0f14120310030201031e0c021011070b01050402030a0906090503031b0703020c0105090103 81
    0x800030001c100300e0b51425480046c0910114001c29000700d0400c00440d015402103000c0c3c0d0b0b0030078a024245440c2c1442c140b12500c0039800b007800a5850792050000050594040c000d00641800540342c0a030b5034a48060301001c99001c000034107043c81074809080c4040341c00010150341c00281420000303108445a04624905108810601e511103c0012000618929111003601070980141840611031b00c012448059a60858080b40c0110034500c07092503051182da03501c03500050103400501c2940c002c0d1103981d081a5031030003c1d20345a81120440050050412410500c4d400900300c4c9419800c2c01050040780c0b13801032001a04058842d00c01c0020409418140c98052041c03802c10844008000e902075218100c3c041350b041c1c42841c000d81040d29130400b4044402c1c1551083c1c07000420303800c1c0f104000003504003502c1f14207417a136100305020000b1158400c070440f55009100075500c80c9072141095000701941c030414003650b4410f0160600098000806130820f10090138115103072030700807004030b00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 203503516 1250 203502266 203502289
    0xe0705040207150b030f03190e030f150109021602060c1507030e010b0a120b07050c1b031e060408071b03030e0f0108220503070f0308010f1e060509 65
    0x2449072000402c4420080140450b031011a00d8110501180c00204101070311032120a4940810790070070000003529119410000315101500d08200e00c00034071582c0402d01e000110107100100780e01800101c03003040c5014009600401c1c01d40030940c64000088403a100034410200000c0c081c040c04540f07150000f1081c003400c00c03100f410440e00700840c6084917005000d8411070094001315440c006082405050809650003076172143d42c035905410040d03999540d48000000d1004041003c01d01171400310b40c5003400001d0404040a040d548a0035401c8200342c200081c501e140c800358030340f92000d0444980041007040c2d0154105021030307107507400d03070806c2c0311049200c00c04100030700e402070380120806800c01e80c00141803800b9280c5d010740a080d40015035641100781c6012980b03114040100c0b403000303403e40d80b10380c00034482c0d030036a4200707002c6654610b43c01c100c55604401107101c120061042801c2a60098000e02d4503c01d850582c0c1b00300b6410101001c46130042c0c408108000842040741c0d181c020a024 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 203504766 1250 203503516 203503519
    0x1b0e0f09040b24100509210f07080a02011e051e0403050d030e0303060f0a08010204090506012c0d020d0c17100209090c03100b03090303070f1707030e0705 68
    0x20914505450b00850070a0103d400000c48120100f000740c9030151605000003c0b003020345200600a1340060541d11a0044800954000403013401000070381020031042d895000c0d075000070104040512442810700700c485d00710749032a03800031000e0702c050713a4030a440f42038168032013000c08000e41c001d0344100c2d02480785110300c2816a001146108282e0007070001032044a025400383e403a1484049030450544083c1e201c00d54040d4000e101107a984c1c80c00240060000c24010240180565036001690a9810951007019040d96900c00c1000c103507084085460141d4201309001e404408215020307040506040c103441c0a84800c003840c2d002c545407100c001441c640c001401c40206543c2c2d14121007541841007100c0094020000d1010701ea9880b402910100072004000c21150381c0c17403a54091854000401580d43c41116580000d40420b10000645c01032110030043c5542c0e161040c000b85c480c0340c01481980800c80c10181c12080c0c441120f1002d500302140b403031b0118002e00007003002071800030b03580c0019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 203506016 1250 203504766 203504779
    0x30403020715020a0b01050108040c05060a03090f0b01062a060c030b030a06050a11070506010315110a0206060a0b0a0806040911040606020304050f030303040302060106050702030a060617101b0e0f 86
    0x442c40d03000a00380784118400c0d0024411030380ca40c001158051400e40d0014410511542c0511161400c41c018002620f40d5180c0010543e40030b480c3c0341c03103481c90840252940c0d0403000c018400194400b10b0300c0000790030070500303118142408080503840f400400c1c000c0d000a03924022217000703500c203421440d51003900404590200000d0f081c8003005201c103a465903201854100c1003150001424180d8084a40050240030180c2c40e64803540d030103000042c16400090fa0b00c9010034239823001c400207800504020341c01000c582c0f07484003d0120b200407030307003048031031300e106010000d001980200000e912050907540402e0030310640c60aa19002059900d0316481420402e0218034242d0010281085403821103180c0080035445003415281d100079100036005801080060210b18096001805183c0c0702808a818421403910740c00c2c00c4030400c0e00400c0d1243c0d08022102c00c204800c002d030382c1d00000202e00410008604414030034400540b01d01920a00251030f11491180d81c0380a140b090703008014010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 203507266 1250 203506016 203506049
    0x3050702100c0c080a1d040c020d2a12020c061606090c030213020a03050a0b060915120123010f200304030503030c0c0f010207020d030e0f040f0e0f0c090109020304030207 75
    0x3401b840c0324a414551880d14440800700d19203040d0160720308148180e009032485440c601011074503c3c1124117000b1182c1e07036807000ea0840c80d1155074910162401011588105d0610b103100a0070500580c824a00c10b681c240006800c800040f00624111548a80b0000785d41300585000d40c550302407607001035805030071742d00d15011310040c6400900640c146550100100d03a00d04401004a0701850030035900004280040180c03400c0c080340e244501101066020305080340c0304454078096a00340c0194038180300000001060100c2e0201c00002000d0908199520104080b0300801c01c0c00121a05d0030392841d8070b102c00003c03d009100b00e5000d15001004e690352843d081018455552048182c04a14420315100041c0c1c001c2c10310a6541642d401403441c1c016a2980c6c500300d030001c00d041c0c800d9502c01c180400c0401c080e961403164081d06030050501092680c418039a803401c003106100f40380c03100c1d04181000d42d0640e856030800d0303054039070b0030078016101c1e190340c28101d14041c5503421001185004218 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 203508516 1250 203507266 203507287
    0x1902090a200a110d110c030f15220303021306051923040306050103141204061214150405010b130510170103240b030606010e1518030105060103050702100c0c08 70
    0x3c103400417007140f100b121004a8903500703040d5541c0d01c00900201d55040000e4801c0040711800c40a5040032003441c0588220b0082000100d6a6441440450101f130b0b0016491400340011001040100a90709145042854001607460f2400d0000051003c011109034142411403060485803008885910740c4c507141c640783d2815030010102800141d5041d0054502c4070b641c40350000d90b8511646080010750f00341454428207076880da00401c91541420b440c0c01070003124001300b16410f840f80c80001a2519020645002d00003100d00c103802c440d1213248100014460740e81081c0d00802202c40603104940606070b52541140c1c2904044c12a1000800650000052048126030f00c00b10220b4a1a046032024846603d10112034600d103d050b015080340d80011559802100003a080d02e07006885801d00030340c08801c1c02c0c103a502c5840e13110281c42c4005480d6401c1e080900c81c680d84281e0a003070030030981c00d101360041c2d6034410150160180c0ca031a910502e039824070a418080b14180e21211b01c2e070321061480c1c4e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 203509766 1250 203508516 203508527
    0x31b02030a0b0912160c05042915030a0c080601030c2109052a010e0a12300e0303030f18010212010914091203070c03111902090a200a110d 61
    0x80c0240c1b4000641c07032001c180e80c5840d01c0342100080500502c11046015010301c407560911441800d94450640d2006000040309807000318401c14100c0d03800101101940c6015100b40409030030340c2d040600d05840c2282a58000c00303040c3c104611004a004042e40c130699071005000800d50040c040d02a40d1040151030055241595803100081c1070104400000d0b8011103901440d00c140a0340544640800c04c80c400c540300076104068060518240b61507001202002d00b001d906020341607551422780307010501c513840080b139840c03040114051450350414400c250030082020300b01310385492980c00c16594405017503044501040c869106e041003581c1d10352514005000404501040c0743e00300300000d5800d0b401060a592204c130000445040d902c030702804a522240e9010300b1400d100400c4000d405a000030000070315220284000c070107515045c1e2040c0810703108080d20000500341000804810b100c0702d03110718001d03889100003a90703c131070800604403942031440c181001c040c0a0300d0070b09410140d112 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 203511016 1250 203509766 203509807
    0x60209010207090504050c06030406020c0105090717070b0f13120c090506030109120f0207210218070e1c0b0708150a030519050a080a0903031b02030a0b0912 69
    0x241c0079a0703074050752001c01100342c46003164010850b40180740640781618051003e190003078000d05005003000f8210400c036084800946604501d80e000410801000c0b0300940c0d50304140001e54003a0940340d00c0c192900400307000d12407034502d903080d0110300900f900c084030400a00030554071140c0c2030340c3c2009003400c4805024502601041e00c0c1081d00140c0b140c10140100c200b9298000070350307190481805030031500c5031000700d050021409500c0f000540c41d01c2d02440d04848082581d031a0154072140d104100000e00000341e9205003c45050800010340e0f080402c25200b5042a1542403283d003000b0780c0c0e210600c02c50400113004030800c2c414412480c1c2c0c001c034454824505d5145c1019007400c1401007012400c181d01c00103005501003208081a98040c98401842c2c511a60407901454000d640304045c603000902d410000480d1074008005041e8017280700c48044000301050b940c840880d0700440c1d25541d004e18040c001c0e00248001c40d03242c0d00204544000c0150f401c00d4241c58201e51198a84060750030f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 203512266 1250 203511016 203511019
    0x20405010305131101080606040503010608010f0509070609060c0c030c06080603071a0405220612050c0109030c06050310050307080703020a0b0315120c03010507091509030203032212060209 83
    0x200340015860802010f421556903030081e480c5030315642d80307a00454071004028401c68200006001c0000c694a00340982009002000f00100d18030540d46200b2003140c100a03c0c0901c280e02030003013001003540083c460b90540380e0f64601403140340350904205d0800701e16580002e00c5050050000650240c0c44070b00907020704070413802d0340c1d030060340e42044190303180d107000f1580b00f40c41c2d04000c1040140b50510144c01d003241c40c440a440d9108406000004580007a840000551140b1807c0c0f0108801800000e00c3d04d042420140f607160704580704d44444904500800e4280900003001c1b54058100c4883c1c0801041c00504031008140c48042e074648070b243c01d2004a004900e48103002c85d43c502c1c0242524440c2c10034503605a00300e80340303004005000065025150180c004c01d01c5404a9450038051030b4132802035612445045c44c54284000741080b4034980146c02c11654940c248010ba03000301c1210069080050060170510114a07500c1d403001c0264030005000d480c1080013000c0082940140051000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 203513516 1250 203512266 203512271
    0x40501090b0f01061803080a0302070f0507080a0b0c040b04150507120909060b18010309020a030c03061d2a030c0303070605150604150c030e120604061a0d02090c09060d0204050103 79
    0x1400700c12005d4050302400010000441841000312075442940641941d90142c1041c01501c02152206810300510b90000c0340035030020710068040c8419a076101c0c0d0006c0c110604146000c1c07501c51014080d014074001c2c40000104403401c3c450051180c4207980b12107030040d402001444800102800d490624400e051529090a40c00200d444201081d075907003940c500d824070b25110012004400800350041e089a028900d094040040344050030f4107009140306250000f0808255000199400c0b00300601c10020750018400702c052107000c0807200070560b0b40b101c0703001041c807403100061300f000491002a50513100104201003441f0722504004e000740304190074040c3c40041081804480c0c03240f4081c1110b00c041001c00d841041d07104100458850b8001d1034281c550b80f4060000620b14071111070120541e40c4810140310612600d4817443c071400d290980c4806c01002140042004a039401d20041d00c26014540086c1090316000704444032a03000070240f81d030f6a00002a0074000790464090b090000e403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 203514766 1250 203513516 203513537
    0x10602060a27020102150c03101703070213020c0d030b0a09050408121e04030c02130203060f0607050705030307050607080108120301090f1509020705011406090609040501090b0f0106 80
    0x110500c6038007009002c110003500c0240d000507071002c00c81d55410003207045103e0074858045441502034010f0040d0603038629140e0f242080c04e2034484031880c54201a49030040d900041c0382040001040740c2840c2d6054485507031104403041104000d010b4140961964004c800501441c0c5034141c0c40101c0c2510100c0e0104000c1c0d8903007405000f00e40f82114000c02c18501001135068002a04502e0341c0e1101c543e10120359842d8840d0340000c04424195001c4011800164030002140740c02c08500f2401c1c00080800c604505e84440002c400307030415800d840c0a4200000c42a081c00002e1100401904001e02141d0386c0d0030413407800541c0c6402c03c0301d100c00015090070010a2005010410800002010340c0706030850b4200b801950061050400c420722859843d100201194000c03506c420003030115040060300d0340e00070b003045400c0d6418045452078030303050a0100b00096540d20324041c0c0000b41980c950055545a1902c80c0c01014003c0300030b0310b007070080010440841c0c440340800b81070310070305e40d100d03092203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 203516016 1250 203514766 203514781
    0x209011412011701090501060b0c100516050703020304090614090c12040303051e010602011b0905310f0203040c0608070e04180c08030921030a08100305030d0501060206 74
    0x1e009418403241081c1e4480010440480407030058207044010a0000a90066954542d42181c026070b1049120090105045010200901030000031604d803104c00c0c810351400324889100c920058484405000000c0780782c83c180b6108006031005048a92000c102d011307280d000c002c03009a80940c54600c0740c1d260030005410405d480090b110690f01d51340c20310210b5280c60740c1c2078001d4070000741403502c0d40400303100c0c090100b607080c18114000d00841e000040d42d0643c50b01303110421540302500b074045c040c0c0240100b22036110320b500303005070f5244c03c500741e400c100d00f120005080d03007803c810b407464440c14015000c0b00b025a030382c000c500a6214903185018135581c0c2e2401d0385c4a003022141d46010580ac1070f504805c5042642206418013081002c000310340703503541e494540050070360700250842c2c0e03c0800c60088034201501031038821105645041010381400c00c080c1e6507441000321542c04c0050006c04151041d178010307021409954002e09132900c4403182c02d400402403409204080046c41060042880c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 203517266 1250 203516016 203516057
    0x220f06020708030304020409080d091a011205060406050a02130b0a1206061e0905061803060906061003200a110d0e18060609040903020601080f06070e12010908030109020901 76
    0x480d0b02e0600511300390350350754080000502c44d004058404603800c00ca200e0358131041c0d10541e041c0c10f100f0a050301185903111f20340c00070590140c001d00b0920316820b0441011600001c2d035035074000c0d80a6000304d182c4c1d8681030900041d006110b00c01801c129044c6001c07a0f810a4080600702034032059903850034100100804c0001c2e200c19108a00102d2400101000664001202d0301088a864204142050ba441020905550145142c40d841e81031828047c049860305000e0260080001e40040004c3e0600b80b00180d9408400e02d1800309060351307441d43c034546a460400c05141c481d4000742094441d9013a101c06805040010040040c074051140411007941c000c140c2004c2c04540581250848400800f00389480c01e0050710095107d2070900c04044280e4a0b030041d40220341c401da0140c0b825500d000300491601e41e01c00c05042068100b40100240a607001418502c2c040c4210341d04c00700603085502960040c010080060949030002001040f52000351f0020710842c042a130381d4940180ca800c10703080d00d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 203518516 1250 203517266 203517269
    0x5090108060a0f060e010302012007061101051302060909091f1b09032409080d0207030f02030307050d090809040603030203040816080a0b0402180a0f1d0a031202220f060207 76
    0x9178807103001803001d94861a003101d4080880050700c0c0080340c4500c4600d241451660000002807002076024500d072000303000d01c6420202841c10700001d036449a002541601851402c43d000710000c900040c240c080810000c446524142c062070b42440341000e200b8041c294a000b040010250a541c003042144500d01100481e03801c0440001c0d440f1480301103405858001440b60491030302c52011b00d0105000c00020400814000401a5291a94a80900401e05184800e01035410600c10031510640000444481c25408000000e07417072000c0c5030030122070150b1b4800d19002883d01c80003000305038001001344262050102145d03411810042c0c920402a00da000360070322500f0101222000031955510550003a20060124a40c00442c0c09500c42084003240c41e441400d850381741d180b0359192903100d000c2d140079034041c288030001903c0300082c2c0e44007040b01c002001c11403102c03e6101400040c0d0305540e5210300356014084c040b00892404007082d482405104041e000c5004001540c80c0001101b50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 203519766 1250 203518516 203518529
    0x905090402090406020c033c0406080411130207050708010e0328050903100606030b15120a020f0706090c05010306081b010903080f0307080f07120905010605090108060a0f06 76
    0x10707403d80d01d59407002c010b9049401d096845110501441c141502045c00c13015004d00300e0050800740302d6000c0085025a2010200d80707004020070441481800c4d0b000d43c000e60701681040c42c2c0c0156840e542d000c111600034201504441510104008040140c0400d0010898404100030b220640540707040603203a01c11a40c0642d04070100d100c10000320912040206100c210500348141030980410202c5d00f8541c031030001f070b03120310f5443c00180803180c0c0602c6542e00e490340a0354000003990309003051302441c0c82410008080042580001403d003100b54044890b82076200c01a152203281c2481c000001e01101c4808071000310001d0310205155100f0311440c8202c444040040c01b002a119a000c010026114039042c10010101c80120205018000412008800303603503283c0e0768605940001c200d0803001e0300304100b43c0c80f140180321602d03130b01c1b020300c045989083e0800161041d02e46401d90050070303c0d62250703410000c101c000180110000c66680d21414040c0c40a01200c06052060000c0b07403058054107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 203521016 1250 203519766 203519779
    0x70b16030b032d060c04060206090c0a36020d1413030f050c031305010e1009061d1206090d02010c020601141201060f08011805030d150909120905090402 67
    0x8911082002640003c1c00718006842c403542c0f03032144050f030600c0401c44070100c210b0070001d0200455507041080342c0d809404440a4038114402400003040d00c481c0d48211030200c0800052140000f0880940107001c41c83d10344115408a00f1001b00d034080c2d00320500c0c1900052401030000395564029418034400e01d916103407442c10300441c1da002e68840308001101007c100c000d004200b00c26070200000c0501c08002414009610314200004059110741c1400311701991075010b0510b240c0d50005001c100365109420b04403001140000003401c0341c91010341144d84000600301d0440c0403440403c3d0907002e4410403080e26605051074505a0a84d404400520010f0384481c1c0100503800c1001c100700b8401030300500885090b0403a00f01d40e401d441d0070f600f002000d0700544404100103502403140c01c040070071046100f00f0015090301d03510b440e4081c40c0070100542d070701e82d409407214859460305200580314031501007000840350b0419009200f82e2141d482c1c0420b04404012a07686042d440c034510869005100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 203522266 1250 203521016 203521033
    0x1060519141203070b040309090c1803030f02010209150a080117060403200a030206090f0d0503240303070b0103020f04020304080a0c0c09090308041b080307060b060f070b16030b03 79
    0x41c00034185402d129240e0728081030080704006180c550705540107130b01950b90049030604100001048604001289041c4250111941c1305600d10001e40c0c0c0072030390141441010000c110509034060712490000ca90b1040d5140303200c05160002201804c0e00c3c4126581d010b51030382e04e90907621204c0303401016000c184e84c00307400040c3c006071055a03034038030100407034449050148800304e000e460058508012400342e000702003042112642003002d0281055544006d1a1072140c188000e040e43c8800b600881545d59148904084200450080c1010301000340072a03940e46c546040c00908200d003070004a100d50094002607540349424000c0c1ca000c1e9401c15590b0f8644040701d501501c07600c3d40d224044441e00b4041300c00080c02d045e50f106610b0700074081d454ac00c0c26171401c0d14044100c2000c4040e540380ca101800000d00002d0303000400c0d00c1c1304581c428030000d403a030a10000100140502c1c018051107000025146040104494003140161a03074420000d2510781d169059050310541c20440da010ba000307281c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 203523516 1250 203522266 203522269
    0x2070c03110402120103060b100206060a03020409020d0c08101104030308132102010207020112091e05030c07062609120706090212010912030908040501210e0106051914 74
    0x464041c400c00041c0010b142411200e519501d6880c242d1083d5101c0faa101000540f6041240d0b80340314240300e170b00c041d082914003030b0300180341000f0710300029015681d11715072201152078140c807418040b9001080d41d1191030307a07541d8081d5250b0082184201c014200301a142002035240300390b40540380e041d100c241c402d81d0746c10500e4841250f626015103000e031189151222800d4820b40b5680090805da0001d030391407015000141000c2d00002015640910340b00b10780000c41d0120140c0c1c01100005060164045142d041040c503500402e05520756501441c0000106950051550300d058006104110110b22041f014800c0e030700d0b802c8445541503008505680700100c401c1000f40b440130721400c400282e40c03669030040340c0415505198110182e5441c0304600602c40560603040d601081441c041c020401c40f5a204540f60040f4440e1905018a0a101c640c40c040d03030095455a03091170403c108881000311a090380640601d12402e03000700030700000d01d00c801030182e03884402e5a00000d04645079085030320 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 203524766 1250 203523516 203523533
    0x1020f0d0c0303050718080c010306212603010e01030b0703020a0f0318060207060c090806040804060806210c1005280203040302090708161b0b0711030a03090507050402070c03 77
    0x5c0280003080f040a00d0b0200403000d03c00b214018008150003030035059184400501225a907030810740c4c00001c0c40300405035012000d440d481d003840e8003080e10140c00540221705560700c0c81181d8880d00d070340004000426189544d0642764100c0e03014516001d030700c1e01c0300740c03090702203101d0721010800092018400352110f60080d002007601151071403899414118030703220340080380c00038541184c49a03141e044540a842d4410503c3c0050451900075041d907081a0383c4d1201c240c456803195030240291040041c00700d90301c158600501040b000301101c080c15001c002151200b403414075052142508980c0801750078403c40039945000318508440c600d1000d0000c007040a5002e890f42c2c51f045110400001c07006803192000e245c090001a00c6007416800c11a0110b1850115411401d08000c002e4180d02a00d02c050b0195040644c3c12182117078083d224403030122031042c40305954010901c40061000b840c6036140d4404000d45004900b0b9403009a200c004110a80c03040c001d02a00c65510321130244042405807 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 203526016 1250 203524766 203524771
    0x11070b0402011421010e0105010207060c11040b06030f0402030d0e0a05060c0109061401150c230a081804051602060f0c0c07060e0f0109060801150201020909040f0201020f0d0c030305 80
    0x9285840c10120740510340c12440100c440d003a80c2d013841040c01084038424689440d800b4100900103000c0450901c0d1700101a10790440b8050042006424a0125901c0780d40c041100d440015245554a142c504c1a90044031001d850490091003007601c211034130f6225500450320306400800001c203140c03502c0100a500d4000d01001d0b11255600c10782c03a000141c0601c2816a002c0c040d9a03420025890b19459003c0ca0f80c040e003550041c41b10b400c00702d0f0001900e15150325100a16010884006152990850303d4200020001061480006509031528030709a90401c503503035040314103010942c3e507503103140401081c00f106540940c0c00300c008600f010700456455940203028407140c3d4101014024401c0c40c040e0203030300c0b41e40451007454107610703942080c3e85207240503c0213007400c2c10040d20b068030080c1036200522402c00c07012644084503060038800e404940fa60040217003000c1450070a03040c29070ba00328050a049003d84601200480740c031002144105d414460384c1c40f000b80c1030465880550141500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 203527266 1250 203526016 203526047
    0x211505041112010303090302211c110f012702030c04020913180332090102070308040f05040e06010e04020603041a090105090c030a0203030d0b2e020111070b040201 72
    0x10b001c80c040e10080301010b24000d50080c4e0381c2212940c610f0040c0700c00c5607418840403044040c4940014000c0e0700016000c0401081d00b1048a9201e0090314200c4040401540b03407410760081c850318450f204815040241c0404030070304040c03401041c40d44012a4200b03007100080d05a0040d0003055910301d0298003500b0312600c0a080110700c42382c1c50120104a48059102000c1040c0500901c418180c0c4900c80c508a00382c440440c8440313540c4003c501800203007880f8402c0e1010000910446180d100380306400c0150380c030824039a1143c1c4c641c614042d1062503030003101e0140386885081c84207407000144590403940c80324072808958480d0340902c40035500040c070546140c0d5448007510282c2c4c119220052058110200002c0d00b401c02c128011b0504600c42d540c01c1c401d41c804448003000d40d40c08070031a00325809200c00090071120101c0410f1140903407a03d005610245529642484001010022010805070b07000b0450131039012602034050149040c05481800350400260041d40a030000c100710f41d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 203528516 1250 203527266 203527301
    0x70507180605060a02061e041e0323031602030f31080312060f0112051503011b08060a0b070809010c0204050c0403020111060105030d080c0f04030321150504 69
    0x1c40c0c2d40030a200368007100000c0016845101048a00300b070181c0302040e0301c0d07800c403108400c504083c1c540c0305070140c00a40d0100f019401241d40d60826008868080c1003032030786503000b800341c88600d03d0100543c00494410031008000500d1003002403000c0111844030388801d0105050001000da0f002c002d4401f080c10100c20700c0d002e000e4880008101050070020711201d40116612003015981c000c04800181071030340036400041072603040ea0b800c1804083d048062000000c1d059031441c900c0180388840e40e60154065117040580454424605a606080c4c40c4a440d011001c0d1250b40500518441d5441007020412050000304d00041d004401400d105505242400c0780700101d800140441d241500d40b01d4090350002020003c550700300005400c2e4013411806006258548000300b5201c00940c603005040280050000b255185601e058038a1a07c442c900592034946900d009045420b084d04481751000300b00c08100d034005d0070703400b034400e0030380070713103410089041c0303000b040c00090050bc1260308034081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 203529766 1250 203528516 203528519
    0xf061809060e0612010e06010b09130510060801060f0f110f1e010b011d24070b0106030501171209150304200603070c120519020d03110705071806 64
    0x25000c1e0038040c01c40c1c10000402814000104190081003000c500100c0e410f00032981000c00c0c0c08541107044480c000c44003a0740c1c3c07520200050010050402440507145058288109182c42d04406000e44200e911402e01690326120192281070140b0001000039481e071614181040c030582d024091a031544e02200d0345004420307103031410003c0b070005980396180841000b40c4400401d00079680c5804007802c11a251400841e8418600d280d001c0c0201d000c0c1512920003450700e24900b41c410b410341c500c040c00e10b4481c10940351011490302e0038480c1c0d000080c00e250002c41c403d0308100f021503000c0143c8000700507010400e070040d032080c0c0204051560122041068060726100c503001107100c1c6110f000c03070030782031200c8044d0381610300c2c030803646203003d40d00c00d1080010044d0408803136803a80344c01c0400c564074581e60407011101403141131920f44008912404070fa121580024500050b9030342d42d2818448480c1d0f00e510320400340606a0054003d6104172010410068040c9004400c0410b558000c12004d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 203531016 1250 203529766 203529779
    0x6011107060c031412040c0902070206070209040809180702011415010305070302040506070c05032808091f03140c0310090518012f040b0a08060f1003060e060603010f0618 75
    0x1d07040120300302c00c5030603520108000c0006141d0124040c0c2038808c0214103200c07040c0c02050150184200c024000c91541010900f0321a1900544004040040024100b00b03480b0701c034103410f104140c0f00d40026600f80785c144c8041d8800c14661a2140c06030440210310074813010011406402c0107804103091550800000c100782c0c0380c503401001e00034060311894008900c2d10701132601d001003080b040e02445100c8080a103603182809554250190814a401e850306241340000740c0c0d04845001900013090010851140c058058100108484500c0d078242159910740800d1059403000f00d07043d0100c010364540500c01d1481d103900c44c40e000490f810208071901c446203460303821100d006880c81a80d442c2e245100d180a501158482010400c03001514141403400e4104060b501951244a09200c2030900082c0c2c50345400c2e2074480600d0006118128248400f00003400900c080e004401c1210084000105141080000c80381203602201b0312411841c940300c002c44101e880c01014040c1030f100d403040013038003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 203532266 1250 203531016 203531057
    0xa09020312090a08030306010206060d030908010513060b03010603120507050106031e0c0609030809040b0607020a0b041d04020609120a0818010e0102010905060f06010c0b0a0f0506011107060c03 85
    0x240e4400031070281d8828400081219100469110030301030750041080201c0e0340d81c04201190050340c20395144910712010310303044d00c5400c1d030b680000c042d540c0703020200944040d40b481c5c040c0240340564800c014940b29401414281c80c098003000d01802031946040c000140305d04000c00700741c1c0c040c0000141550f04c0c2c2c2c0d601c812107104d1070014105407986400e00400c0c00003100d60200217207140e0a0007003040d460350f954081c107401140d004900c1103654082d6050345868810880d41001c0c0d00420211820f0740350038501c00d05401c00e000b41c0b03004440e0010806900c0e8980700b8514040e83c0c00500d4a400c100002040083c100d0f03041d02821024003e0006100010340d85002805c0300d05100c815088174211104c00040001d2002d001d0141160b06010412000c0380f40130612a400c4180150b8072801036440c040141c0b01c0b0000c0b4080105217404440402c581d40090340e0100c220384401c41c2e070900c044d1f00e5000c011500d40014464220840c0c100310400c0224a0258503000d000c944241403650407800d1001c0c000c2d84 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 203533516 1250 203532266 203532283
    0xf03010504060c0f08010303020a020922140609010c14091c0b15010e10030c050903190606140303030106030c0e0a080c0a0e01080c0609040f06080d030509010c12050a090203 76
    0x850390b4030f5601202c10980c1060900031a074480d071030455110f40c59910000d5807290401c00c040e00030039000c0c0101301076040c51044e1980459079030700e000324808918a4086066100015040c90900581000c01c1c481c90040c000d801c0503c6041ea21480041c00d085680c0c3c8007640f01c3c1015662010340410204028401214501900c501070100607a0364070300b58a220400405446650341042100c1000d140c5540da0001449200c1032546030010741511141340a0303d0fa48035942c181c3d40d01d4480c0d00101842d0469466403440c1a03131103200301703000c456543c01c00411003280384004103034550424001800326501c2503010718040d80341442c003103e04040d038070081400c40390b02d42c03c60415a00655140c04081c2040c41c551402000e40682000442d031415405684601008103207510035000020451802d40e42c1d9002901c1c4200d850604000d6265229156a581c050190b01c0d040403e09240c0043d012000600c01c0e50303803540d59a122000c800741c0005842005190042c0710300c0210b036a6141c03c0c030168408000000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 203534766 1250 203533516 203533523
    0x3030408060c041701060510050702040b0a08070801110a0203071502041a07061a03100c1403011508100303020705010e13050106030e01111602060702010903060f0507030c08100302010e0f03010504 86
    0x694035800e0194142e0103c00c1d86440904d143c0c1043c108210030f440c1c5040c030706216142840c209844100c1413000078050031120300c0450b4440e01c503240100700e00201068560483e203040d0020482e00082c030009511a00415486034003580040c816440030400781e9050404581c0d0362040140b4040d20b0350382e41310f95200010b14203513511030040703121010449248500c0d0092244000d5000c0d84c42c8240c00007075610403818103a84240b81e1078041403031410740a5805a50705913004501d5686941e113613841d0a1602c48107182c002c00141c610808030b021030b0102301422003501c0e01580605151420f05005550020701850a59040b490b00f800d00b001001442c4640790190440380d5010800100d42460982560100702c20a41101810001100d02000728a1401e0901d54107440141e00d0b40c0c068001612034001c036500152241d801d08080380d81003042a4002480344110780c608001b03081c00c0590465200c08101d81054401201d20028405503014403044151204024110400040d140c1d01003420f4407000c1e41e045 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 203536016 1250 203534766 203534791
    0xf0c021507031b06150501052b0f110307140304030f050f0c031303050705120303060d05030705060103050706090e0411040b151309060905060d062c030904050106030204230303040806 80
    0x50b00c8040050341d005c00502091138200c0c1030520b80489800d580b400360f840e509242507401402d14040c10650070410030304a00c001e04212850041000d0400d960007241c0f02e80008010341080343c103920f0000184c900840d056611907000b0540400107075a0741d4880c1c0060400390f4000d12054412002c04c00062584c11004490302d100f5078518a043c03172130030140d900100e1041080c1c4803031030a9502e000084d81c2c0c0c418007c4034256003540d12401c0090039440342d003401800b180a440008010700000003004811a621580e80d01485981ca213240a42d1880c00c1e5402401800070402034001b600d07003904860200d8200418a401d40c242c40c80484600f940900c0b0030118180c10700030104500314192003868001c003c9840141320514095000a8181c030103d0300041440c2e6503000c0000c0c0d0341e07586040c0c19114006060841201d0380303040000e075a40b41c01910f00c0030b200d2410702c000440c405100303009481c110303118441410100440903c101c0054161062580c1d0548818000051000030810030940580c5428801307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 203537266 1250 203536016 203536031
    0x70f030503120601030c020a0f0f0f0803070e1c020909070b0d0b01090b040605040b0f040801140f06041413061b08010f06080c03010b21070305070f0c021507031b06 72
    0xd200b801002406541410328102891058580114886681c1d0342d2060800201a51901c0c0c650418003140d0805040c02c507040f881001004403031070045010709a1901d0301c1204001c20020048a41820a0b41c0601d50048100707020050800020081d000070501e0151000a03446885040307840c0c104000b0142401d469207600c8549580111070310014006414000d0303e0301e8102000900240704500c100e603881d2500140d0f03903528400190507140a414894024004a2006001010905401e030b554000307000350440801c401d45800e120340500030070f0120b07910004c0c0d81c40510308a40300724402d00658120ba04d030307095030030480d00e120148858031081c0c2d11032000340c0d41081803582c50049550490800d1183c10002c1c0400d0400040a0740d0460711740044103507443d40c2040c40314802c0000040d101704100303024018000d0694141d0030061043c2c5040c0d40b1008842c0e036030341c021140051004006504002d1f4144101111281480144142d601178203240700000343ca648030f074090001664050311465507500c41c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 203538516 1250 203537266 203537287
    0x2502010f061e0b030c0c01020f0403170309120c0102070c030606030b06010f081f0509041a13080d0e030c060c21071d31181203020c070f030503 63
    0x26001c041c10b2041c00d5118600444a215981140103010f045451440440001c0004600d6404c030381c03040f200394000b9506c5c1c0003592052841c64002d800300b10b030f45500101400051020206c203403072088080350000d10415160040d20f441c0380c1d100040c803029030b5400300b016101003540c1c01038007802148580c2000602c0c0e8a1070603d100300c030801918803410084003150508216611509042d040f804a40e6400e16804110b5010003084295a03c41d40c0c01c01d0303046080109200b43c80e0031805801c0c20540c04021b90395241c50a07030200d08a0214014035411040c0828512040103900c0301c066141058212840c00d40d03240d042a14050040751188900c540001d086142c10f5200241036014840751034031064282803804001d012035808000c14400000071106130b2080d03a8840e103801c011903d0001541b400c81c0e5009911410301d1903003049502c0018205483d2000c400080c0000703505141d044681d0441c2c5e240005401c030040d40c01840d0720305051040d14804101c2e01010317040400110310450095950b41500c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203539766 1250 203538516 203538521
    0x11503080903060f060108012d140108150a0b1c02040f081c080f130c14121b0118051309110d020906010c0303060f0602031209010504020112052502010f 67
    0xc0c07890103000050805e00071146d070800c5025041d45d40c4107620b200c4c808010321038a0074a11111b01c402402e5801c024001503c440c400341c4906e16030400380d8903070000c2e6a17903420b80700c0e615114201c01d5802890000781044941c05800140142408001240344551920030004007a80c000b50010610100c500d0002c03c1aa901084001c841243c0c219031540c550382441005400480010014104100c0c010f002500d01d8441ca00c10300e0000d41d01c250052b68858903043d481e24801c200038842030050f078000e030420300040710014a40c182c810400000764601014500111031205080807286546505509c2c0410b0990f90349080000c0005002d600003281801d5043c840d0810380300c00c500b540900d0f07104100e800940c8415a0305ea901000c00c2c00d144210300c145190403002000035500501d0755101d40341020620603404401000400b0414003000b0a070384541b4291422a03100385c40090204114000034820460240c1060340e00c000004810309103604200340e690001c0c1f10100d50200180d65030165144a2400e91 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203541016 1250 203539766 203539771
    0xc010801090603020a0e07030b040c030e0c030610260d081b030601080615090405040503070b01170715030e0d0c1b08060c0702040b030f100b0103020a05090405040501150308090306 79
    0x725020301206245401007450300b0414081c10046466090005400c01d0013a000103c520700050000c220104001f14010000c1080d209031410714021601c1d48074071383c40c0020303641c2d01840c680181c2032840e40c070b40410550954005007600c5015290580031482095061200442c40b510685907a01140341511288121681c082e00a5505040c00c2c420710429991102c000c0754010401d03990f502c50804101640201801a5800264403e0610042200b0003034080080d15000303100d00c43c880b12990b20703080109020380240d0b01d41041a40000310812040c10120340028505106003000620100d49902041c1081000c408001c0441e0301500100100f04060360b039500c012140a040585450615a085403920005024000c20842c045944030035561154010243c5000003021200e800d004c0c54125511140c508601c650002d03c0d021a40541f54000d00072035002e03044039900c851510345942e0400000f0704003d001500d256503901c60303407103a01c000d280d41d0074040c41c040c500c0d058880407480105407404000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203542266 1250 203541016 203541029
    0xa08030a0206150a03030c1113020a030b13270c0b04122102030703080901110406210b01050a030c020c1003060302030106050607020105041203110a0c03110f37080c010801 75
    0x13150300400201383d000c80103641640d804400e002a000c101000283c000f441d0344a0004003d10003c0c1d03e42c00a501a44114000b00c001e4420444018a01032401e085503c040c0304002c0418070801c0307128010001100b0390a00c244503008903c1410b0711541006007503000740c0c0000714441d04d81c28009042c098190350080700e00d102000c0c0d0242c20340030710900039142d00a5250080c1070014600100b80540c00a40000264001c01d5401c42d840383d0b034a6400400e2400304121079450840d0071b0fa583c00c1c18129034003880c074410364182c5a4500c5c2040b42c00003180240307041d07a2800114000d00f440c1704266a00c20030850705054140e45c0105140303045004040c2102d265034005413081d00704000030b6005076049000d4404864071000350700c0200d81281000e40750130080c0e880181007409114080340800010a0f49441600d00900c02c0b000c0c9031050006020303d0349900129280d01003011484041958072600e514103450000101d0b10441c4501103244ea414120103030408800c2e50481e041000044d60305c0100341d40101103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203543516 1250 203542266 203542279
    0xb030f09011431260c010e03090109090204050d0209040204090b0903130e0f0a150b03041b0803180405070201060e090706020606010c11010e0f130c0e0d0503180a08030a020615 77
    0x18a55814440d5003401c400c01c138901600c0b134544034103500c0e4041074481148075140207019100c42d218005880303900c0340ca0814041400d015010441311920300c06d44040d100003400c80d048001154081001c803035001003040b6030154071207600100050030300c106a4054440307507000711348070b82c000204405440c1c2d41d07410001181348c03003c0c10803981d11200c0284070303002440c4c0a40020340c81303081c1c7c1280c00300e80c01036003060000c078000106000800c2440360b14410804080d46146c48a40c1d1260962070b224801c540141000c4204080301c1e0300d00785866440507412a00f103000000300d5070ba481e940164042c0d012503805038580c0064404000311a01885001d61100c02441c2c0700034140070366a2a0340c00b40c000076140504004400303165413030f5919a15a891032b603100080141c104038001c0c84c1500051b00800a1480029050725a140c034141803680c0f41c68441a07014000c0c50600141030f641c01d09048850b143c20780d00c040458030000d02400c0500c01800c0c40c1695078040c0c640342c80c100780340282801a09400601904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203544766 1250 203543516 203543611
    0x504061805211b072301120e030409060b0309100e030403120923030f061012020a0b032401170a0b0d051e06100b030f090114 55
    0x204049074032000e4211059886003401c40601c4122014010541150040f64002854011441e00000c0071011201c101d0401071541c150a41078028000100381c2c5d2a0200e0b120320340402411a03950011415000340c1011682490b641d04009400c2d186d55500206000034000305211a003007090000a080c9032200d0000c4c020b80020743e5056a4a21983c800904011030741c00803025543c0c464080303100204100c0c182d04254040301d200c0039081c83c003940d5070540b00f4810411131681c403003804902180302d03c02d044541c041e02e41c60044404000d02107003404a03032100700d40002090030508200554090400341c10403035801d904e0300422621124200e44500c0c1800080115200444c10f03150100380d01c45e1080b080030550b0501100450702d42c2482c1c11004186004811229101c0d4114100f020780c41d41e1039000300c4445403942e000640301d00c58103010b5400c0c203c40400004285007044240640c108800c44000a850110a05004c3ea40c00d400e40e1482c41641300304c2d02e04810310201d440d603c40100c03903010b620710548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203546016 1250 203544766 203544773
    0x3010605010906050a0c0605010b03090114010602030a11030408030a0302090307060509130e0f0d0201021305120703121701030b070f052802030c030d020d0c020f070303050f09031005040618 83
    0x1015501c291004c101c000180603086501c6540c1216240c0c1e80040203220f00d503154002aa01d540040b00c0c7c01c10698a01138038010001070490406040300d10a402561030403440035400c85e40d40d490a0710320300c0a40300800000a210108100804000d0500c0c5d80040c0c948024104242c101201507000760200030080c00800420342e20400c00410146202c00005100394680300003904041d0022281e203080d00030200c0e016121034040d00284500a02030f1000c03455651542e0410101e12701c4004d0030358003a40308070300c10700000d0b81600801c0e142003510b080050250600c0c024a0700c21910980046400242442c10321292640003124440e603503006007001c0382000d92085466995040d906000a0710303426814800d50503178000d0080701c04140c4c0d1641600c0d907602c401490000a5844a0901d000891500080c25851480800e200741d005005070040c1c6022071454070100d9807500401c1d05070042c4802044100703c160340070040d50a5032346a075000490145081d0510301e044544c0f00c1e0400703e01003440c11620000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203547266 1250 203546016 203546027
    0xb090103021c0c0b2235010207052508030906131a04080709050609040222020a0c020a21121e0206040516080c010c0f08070b01031b0b190233060301060501 68
    0x201d042d03429448000051b450740d00078140e400d43c2c0a82c0c0003544009841d205101b030118460031034030b1410030748407500101d8440c106a03c004030b2042c811950814400090945091001000816501002505000c1c1c0b00d110355121700703e840918900d06000000c08011040d41441010300501c0724110070041c1745011004907043c200001c01c000e10584c1c1030cd21f40990240c41007460103041d4427154045481e0101c1d500080d00d142d80300241079211300c40403038000030b0707503d98480c180140400002c1944600d4125544001d150b0741c8240c01c007010300807814100504600340c0c801442044601d54002d04083c00c140c20154100340f00c4440002a5060700f41d07040c004d40200080400c0c24000038a8441b01c881d0903414000102c95131003400900d088400078814090140840003941a01e000c0c803a02c416a151440740c2d103144480718450b05030041e0381440503991440385001e00041401560050304c401d10020203503140d4001d505007128003e008600031031070701d5008800310190303c03120a4000f004081d0030500082e15 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203548516 1250 203547266 203547299
    0x8091b0d02100311030126030306220e121b1b06090a1d070207090e07050d1406040501020c010c020c1804020a090504030c12030b090103021c0c0b22 65
    0x7003042c41c07400d010940c802e6210312150100d403d500740d101d5840d1007101207e01d042c15012074803020000d681c040404808070480e07000d014024801c010701850b40f09008001b59421f02d00017181ca80e05c903031070480319200341310034042c44c10200080d503541d0301500541407030043c0d0120100c000c0d602ca040648424401400300300316541c3d04481c482d458401060005203000c1d0307190450408803101c590f80c20311400c8826140c600600540e000d54030090f0f20f6200301811140c40803400846540103002c2000795080c031810910006026640340e0f040790380c1420b445417078507800f0b41c0d08450586d40061510300c000070a10410509544070b2025028516806000690202d6510351040030704005102003002c56503555000030083c14048418081c034509804d0141c484020400c0544445e58a00701e10300405210380b1404152001c01080700b0f013241d09640a201803160b071034400810302a14620b143c0f022909030400a2300500c8800c03811030703982b0806425065080031481400403004201d203014880a02d0350f800062 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203549766 1250 203548516 203548519
    0x7020d080402041a0d08041418060415090e150105060702030a11010c051501030c05010c081c1d0f0f030307090905070314070c11030607020d0e060c010c08091b0d02 72
    0xd44034401d4051034010300784d880c245603030020b02000b02d44c0c1002001c030003400458048404d9800b0700c3d0354510501c00e0b210614840070001201100000e6107514159001e00000303038844441712850382c0c42c0c181500c2101e1040f400451640e00a19034100c440404d940143c1c050326050fa0014103080700c07035011a5840100340740081681480440d60480f5074480c105c003010a0342c114080717a00400c2c0e010600350a01c402070005a0348480b0303044021500d94020f0540301d03075090344160142c0c5050010a0a078500c680700341d41285103c0c2d210148640c8404080440454000d03284c0007030301c2041c030f5a500e03082c5000c0c40a0341210060b001841040281500001030808030f94003502d0105050780d4114085000f4600240350707810344501401809a503a52008015a00d507110f5011411803403814000c041d03481e642120b26200591159a40e420040e21603039a61500f5039001e010b950524010701d98060a40c5c10a20002c40040c0b108000c012202c01d0400c40c0301a48094a0b00421084010344081140090894400f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203551016 1250 203549766 203549771
    0x207150e12280c030e0405060d0206030613150815090d080408120a060603050a0908191205090319030603031706010c0507170c041a1c05012307020d08040204 69
    0x490650b405100e0548426264058003001200d000780540418a007010941c009844050341166500300b6114150180c4402040040314a030141d00304892580300400841d0021200040d05001207014000d9a03e00b004806000d000035050084d15807400c0800b00e0802603400580c014443c1041d00071600054003c440d1030000002c1d907540c02c0c00c1005e8031915141e0f031004910203003040007000c13055200c8425200b1a56080c40320391104112081900e950800190811340d0030023202600c1c68801030500442c018500f059581040070300f03d004102d0341c089441c01015040001c000381c503038000704041e555154072428100724035801c64600070103140f45999034100ca8500720011441036030107a901038060550040c00c4950742a1142c48090154000c18141c0400780b052a660042d9450a400384040f20351040014841c3d000000c8204019948032050008480880b44058030118800780900000209082c2c2c400c1c10f404809600328000d01030003010001190000088640f215500054079904150111000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203552266 1250 203551016 203551027
    0xa0c05271303050c060c03061002030901090e0901060f18060f0e0606091807030e0606040204060e060702040603050307030c0308180307060e1c23030606071e02040c030207150e12 78
    0x664842c42694000c3c10544145c00c1000910890600154402d101c00d03102c0b0005040500c409980d6070003409050707404924140e00c140039110b1101140e51340014014004038880b5920204500007114a070000990b081544c00f203950040104d014042c01001c03000c118641103440e2088031070800c03c0103400c2e28400c1d000080d900c0881c0c1d8859081310200258902403c68900307061602800910040071080b0311401501d000a106280c82c0c400d50741107a4654441003c810700c44003c02079641c0c000030040380d01c242c3d034242c04004540e042005e020f0309486512000030601807804c019010010007800360201d007804100991a415000c000c2e1202c10307a04c0107005c40d40032900401d4a090480311290102a070210213164122194426901c0e24007001c241f030059060341c40b48400750b0319840102c03039886d0085000c204000c002100050b2075a1011074a1a002d19000c180d580020165811464084002a00851350b503003444076603d0705c104180c64040042101407180510103841d0880c0c02a04640a42c01048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203553516 1250 203552266 203552273
    0x3071a06030d0807260a052214030c01140f0127090c0801020c0d0e0a060912081903050a1a091305031308010e15061309050309030a0c052713 62
    0x940d00c46529104009203240c05d4404c071401d0000c045801188503410103000c109064000e00c1c110000d40030000603040b4112064544140034103944000c8402484104048680010213100790f01395200d81c408100c0482c1441c5082054400068000503400010302d44246200c120081c06a400020969000310b03d01d4001c0c00c0803010401d1a44c086070140d40002901180100c0118007501c151040742c403200c801440e003105018020440d80240710114500c5070050005490607450585c0f031500c01d51405141c4482c1e6140100201d06c44001c010200e6114010310180340010b000303002c0c448030150303e186010b41c1503000042010402400c84104080791000b90030a1140500484100700c442c3d0b01c024500503502c0300072900900c0b4800c0c03111001e00500c070299041c200d642c0121402900002c0c440240050400301000050500301030488851004000a01954606000740302e00e007401a041c00c80b44ea0715120500c8688105128940c0264809040325080c00c01c070b20100c1d0b034000001c11603a404040e820315 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203554766 1250 203553516 203553527
    0x20306070801050904060b5803030b031603030e010e031501050f0102070b070f062703080711150603060a020f03011809020303040b210103021e01180803071a06030d0807 74
    0x59860100203403044008140800d8454240b01041e2070755140040c0e25901d60360100c0b0317000c1108c51180c01d040c510401d00c04a03109030844142401d00400ba104280300103030042d28100320710b620407404a1703090300c0300500b19a00305004018148060300038040d000500c0055105024050003031501c55584a1f08203d911391003001150094149070481ea0340c2c912b640c5c14012807002501e039046640d03034104148030707042500d0211100e80240c100842d191010503265020340b00454024409001c0004000003520820820050030120440302104080c4a0038103900b41400e00304000c0001200600400000d80801045400c80703046030180c61501d01203040040852016140b80c49019500d448042004128851410014000543c0c1a1801420101d00b40c04049450a003480040d46c0220001072102441745140b00c582007945051500c070202d0080c81c03044607094402c40d0014811136101240d0340007040304000e0050703002490f074410110b040c506400065078500000d03264000f00114035000c101d9030360003003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203556016 1250 203554766 203554789
    0x60c0f032a04030b01080c0103020a0207091a0406030f03120605010e0d0821180703020108010306090203010f110901080a05010311011413090c08160504260607030603020306070801050904060b 84
    0x1070200d59403140d80c0c0c00c10210001083c010b107a190f018200e042c0101d5030013803088031a6810a074014192851034188550024000b100200101300c082e4882d01105a44a10480001e0751240c41c103106180039504000b0415541d0064111a40c0d15140040c80b182ea0084c90860710094101c480843c01400c5291030321303aa000d824296a07400319940a084c201941c0405854410080c03481a901c00e00c00003440c1e0f42d515105e0788030180c04604003400600c040b0724503030800020300c2d0001d000414180d0302c0c43c500074201d44660400321403044020419400c00e40c0d101c514940c1081101c8420b01ca1541180c0381c040b6890700c2414400e0500851007070000081d41c4107000c2d0345001009007005002c1035903c00c4001c010f41241d00b000c6000492030000256160114503a0320010305583da141e0703040500b0300d150702040c004480b499400c1c03441c07a1032084005150410046103e44001d5502048031860b502c1458a00f14000c0d001e00700b401550300040c445a100d440c4a598030540005000c41c00001c0c190219824a908 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203557266 1250 203556016 203556091
    0x70503030f010510031112090f0706020304060306050402030121020d1e02040507031e02090a050301150f0b1c0b0406122103290109050913020102060c0f03 68
    0x100421908910201e1010704a8100b6910040b607135500000840c02c682511080e01c035041d0007442100201c4503001e03003070380e4008031490032500c40d1501001403038504000c0394800001030f8000241400034540c140904002424240c3d81541194104914804c1c02865588030402d029503e00e0440155694070b081055001e130071045250030400314220110060280b8042039000d40c2c00c3c20042418684241b054483c1440c4403014945419007983d12400030b58859400c2d01c5e807143c111600891251303001c0c4114400401c14525a10707a043c0b0740419503511240d0743d806035071618000d00c040c00322000d00c6018000c040722b8900c0c00049540d41c00c000a40100007540121b4441d84000403007800b005507004005c020868203200072000300b02c40c8041281624074003e0f140c80001c0c400490111881c004000d00c1280f41d1050411147c2c4944981c00304046c2c40c012242d0f800d2022200d4044015541c0500920b1703000803980d0069894003174540100c0020788000f40086990907044803011800c0c805001e2903880034201c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203558516 1250 203557266 203557273
    0x60f1605010e06060a0608060f13060915080c030709020c07030b04240614010804080903011107060c05030f0c070f0b10060908030c0a15061d2202060405060904020705 73
    0x8090604900030103050203620003502c1000d001c070b8440d01d0815111411a11155034081d51a61610180100d00a1988015800a800d104607000c0044580500c102a14681100160b2a51010750000381d15002d6440452142c102404940721030300d012a502042e2003034610056501c554889a403403801c02d0701c0d80050a460f000e2802c0c4020049440041e8200d91316a11640784840340c06980384040312130911669140e0030070180d002d45554000c0d404035902c14080c1c0b8a072420448807401080c01c0d502540c001c1041588000f50070740400074144104042c40500e46011819494000030902c1070820280590084540105444081000451600b980190310007100d403403900b0800780041078910079014010100c0d521780c0d00411850000810b40d0840c0c800b032401041082c11a4403100c0d0800c0302c00700c016003116101e06001ca01c82a0181c80002c0382543d42e10003030424900354500310400b08203e0a408420000d10b4400d20141ea60039080e101075a00407035820740d0b64405600054000d02c18290010079500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203559766 1250 203558516 203558557
    0x130318141e09150103200324030d090e09120307030207060f060603061a160f170705100b030f150c16050c0f060f0711060921010b0406080c060f 63
    0x41d864020704003443c400c3c0c13020310a0303181d50588203140e910700d04108181c001060000508030085500508080e034200300030b88000b40d281d000400d041c0301c0120304030000329007000403c00209c0e5041d88000c6c0d101c0c6141019000c02030082030022520b1002602100030950003142d04c8041c00039640c0f0150010310f00341020006507980e11000340241c0f500b489003000d1200041c607004280c5000d8411200240403404002a400c07509560381c1c03007102c40480003502c40388100b00c829800042d00c1001040301f02e028800400100d02c4850146042e9030441c80814000e4000c0c0c4100014254001040c1c040590341e8000e200300d941e40c070340070440303070340605540003415032036060801080c0070b0040341503007020b03106840b18040c060b035242c2880300b14800c42080c600d14141c10814107001c00c0d4100301800803e440280b010f4503080150000581ca1008100d10b842c00c400c5200396403c00b69400d118034034440000386c4040c40307200d28220000e034440f5500801140541000105004e03840480f404440e00b9058924043c042c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203561016 1250 203559766 203559781
    0x60925030e0118030206010506070f12030b0316082d010c0504140f090411040b1e040b0907020a08090f040c0f020d090b0901030c0c0b130318141e09 65
    0x60034581c003510982e500e0260410b000303070707000c3d2004403460380c05030020043c5901c1c04060040691020009072910001c01d5030700800548c1041202401d4416580c000c500034042004060609144070724004800da02c3c98801c20403402c002c01d803030700125506000c045542d401e206081c01c20340c0b080c03405000e603940b070050034500d12070b0800040e0095506100640a102030070a0074401200c070182c0415610440c0d400005001480b81000c0d40300d6004003602c00301d60102c101021460900303003070140030403880150f982001203042921580d141714100702c0d01c10300700741000300010703403a020751030f030040c140f42c0f0002000801c82e2221100710003030780c4010384100840044010010200034555070840014001d8000c0710404610811941c000c2e2201a0f517854074020310030006600030500a401c01e014032038402c4001000c80c02000d0040e120b2400840c1806071a120b501c1d00411603504c3d4088006405084401400607107181c146445001c1020349140350011260755019005500b1400e800d50300c010b5850400c81034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203562266 1250 203561016 203561021
    0x6040c0e06030a02280e011412070806040c1401090501080a150e100e070908280c0e1005120304030b060109090e0304051302070308070e010309060923031206092503 72
    0x14001780b62001d0694544401c9050b1411100380315214804800300904d1995140203d00b00c2c0100304080101c0d5515603803080c4040c01d10394111410740d542d61030114100441d074260515145a0340f000d180113200c6c0c40c14040007074080d8001501c0711580e280e54465410504103c00490301c00b0301440c04003250b11340362605486000d03030751501a080c8847c422a0104440b03034015640e400036076420a002d00b01c3e403c0c0c40244400207251005444902d01420501e02e00403800d00c2e40510b002e80650401441145406450614000c000c2d92100740510114120f500c0600c1c2d010040e1429241d100150045540b02c200040b9000c0101d41c11110080d45000038120307180c08004024012100182c800b0300007a0040c1c0c2c020000c0b405030603405408240110300050f0054800d0481a5480805040000791855207444110484003c01d02c22600e60035603c107180814001c0d0641030f2184181e40e0000c52030001c400c910104c481002401080c064010040842c00c01511080b5550707280301c0842c40100360603182c400003000f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203563516 1250 203562266 203562319
    0x1021c1e052712011118090c0d0207170703030920131d10060306060b030702061801021c0b130e1209150307080720120c0c040204030b150306040c0e06030a02 69
    0x103424400c94903c001c18144503412a100790b01c0c0303540050500d00c050349279002941c019801100c103201800400c403441c800c9a00640321039070180d580003070a40c5051600d903580c1034500701a440400128110a4000c0e515002d06c00041c1594041c08181c0e0010320008810362035001119143c0c600952000030f80001d075507407100086900660040c400c0e59034417048100a8401501c0b00310060f000940012850301611200030b015000c00790006183c06003601c4903d00b0102401d444150107601c1348101c1e2010303e00b0204000708000e940780c040100740d00a403070995444020412030341980c940494159019a60742c2219800e003450070007031565078030384280300030031011084584074042695468040c068021000c20b6200703d00e02071000305545e42c1c0f06140080356030000c072150382c8207201c0c05551102e1501c5900280001b144106d6180030a410050402124071034004020342c040c0d0b11100402012504141c115000c544048240703c0041e11820040380c103001409a02031f412a00c0c0006c500300c2c6841c0c18a1000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203564766 1250 203563516 203563537
    0x50103080c120301030209070c0302160b0c06090c0604050d1703041211120307200d020d080a0c0c020409142b030207020a0b0901021c1e0527120111 65
    0x9100c021409221401c0f40420700010790001c82a00000e01c0c5140180d0702e060b501c0d03019004030703061000c84d810700c00072400c2542c110f0071004a0214003003420000c01c000c4a80c21052100160003880e052801007071a9004501c80d01c0e04c00c5811040181c14010004006100c00c00042c00071641ca282a0a11005003840c110303544e030000c1d400102403d030707403039011410070a030703040c10548180f41d521800c50448805802c040c0c0345e5100e01c601c1804074030440040000d902061030350340180078400d03030004020703010a000900744072005007041d045410b111b5010482100c10b60b412200021a0322043c01e01c024442000c1c5843c811512078420300c00d152140503000c841c0d4100614010b144140c800000031400e90054070402504040c01100500c4002156809821414418070465407840a01a120460038450880604c0868841c0c001f03011103600034100d0040034202814403500d090111404202505003e0f01c8109100004040580640d80c0f06090b540101a643c002407010b86103106200c800350f0700001000c4c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203566016 1250 203564766 203564773
    0x20703020c0909010b09060906040209040906090b0c1e0a200705040f021309051320030d03091a060303040b0730021510050a0e0a0606030204050d02010c1104050103080c 74
    0x140940360500849124040286c540503061702c5001c14418440f4019144c25801502402291544d8586106c6d0005060081001203101d61007428107110080d00900300d08a0010304202c0205208181020840c90401041d1000c0d5680c0401794210b401e00f4404e0038810401d19224018007800300300242041c16504111020040d62900082e00b00403072041003100800c4400b0450104005c0340203600c810b500400103086082e1085180e80c4166031888910510411031504800090f29400c04101e000c520b446541410080403202e80c5034030100c000070000c0c069500070b1000c0040c41c203440a201340d40080403050702e601e894070346514001c100d9826882c0c000000511520032042c0c070a4505001c200c980d582500500041c290030641c1030514203000306140d054400b08030740082e030780e00c0e0011403600a00c26143c52442c0f07030504400c21420b641c07965020304201360050206100c103550784142460143d909013400f50907455545049104000080c00c0240c2c000d180000005c24481d1141c01400e0446070102035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203567266 1250 203566016 203566021
    0x30f18030c2402030309070e041106070503030103031403040f122709050603070b0a1b0c12020102060906040314090d060203010b13062c06090306070e040c08090d03020a1101020703020c09 82
    0x80384d0320b0004544055043d840820700b0480105951601c0740c00c01d00070020010b1350441c5402142d03880c2d1000608540315440040100149980184000a131071103004409145083c01e444c2c04403603240c58003000e4108055501c64241c028020f0181c0c100364011404c030070039188491005015524034078440e9501050074000010010314002c100e84081e690501e40c440d05040700c1910454040d91527445107445940e040101e01e0104102241c0d50008100304a442c1c5070915a510009051200180c2000c0d8650310440900c40000e804ca8a04064020a90005920f80303148800003000c15500d0940903010620010010032451000b4008143e903180307242c07550b025103a40303e1003210710442500225564452495150302d85a850401e1f400c0d507004001c1400d0308100c2440c0000b4140042900e001d8041140c01ca10b42180741451700445207401c000d03041004951614040160301d4200c2500307024101540000c48883c414000c03e114046280000700841d203540d04c42c54043e50320302040300f4103846480710000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203568516 1250 203567266 203567339
    0x20f0111070b041410090c0906060c0c03290a0c02070b030f011505040504290a050f060d14090d0206010b03060f01120e010f0204031e030f18030c 64
    0x120307103181d540445503414075a62a11003045a070107a001d410500d0040101c1c1d40a12246401501422130241d80300d43c2d46185800204000c550b5198443c03024084013910440101d0030109240c000c51360000d2203150313a00300b018080b1000468050103244410b40c51014404500398540c440c60b100001ca4007181e05194852180c2d4a0f1408229400303c64100300c0c05c0140003881104034600c2e004505818610b00342a12840010242c48108210880b41c1c0048059460222205602064038505c241c5180b00458180000b0403951801c945000b401088002281c00003281c1d5a03000c1602c081403a4010715060130300c041031a8690010a0b800c20040c40b5600c00822201c6000c01204c6c0550001040b807030000108000644500300744120848201d0b80e91100d00c7c42c094030030b002d0f000c01c3c2d0708141401a07665065150550b00e2128902800140803020b01138000020b40100d01741400d06214181441e401c1424099a41c80c948c4c03540005094586045000032440301403032940d610304520101c10140144141d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203569766 1250 203568516 203568551
    0x1303060204032a03030c080702060d0506041b12051302100f030c080114010f11070609180c020303010e0405010603060204090506030c011d01030f060803040b09030d170406020a0c0210020f01 83
    0x903c042c6000404000c204000303401403e004260a1040c0c040d14200792090300051056006018024085c54a07401001001e181c5881409a030509058a0300a84038001d040140090240004102c6036650f900c0400e407084005030780c10704803941c01080304c107050001c1038004145c860002c0140b0701190500c281024418020b10b50503060783d1060325030000c0c01400348011282e4202e6116100240004020a84e850103030030320a00700500203548403031100324a0161480c54072a05d0385d801e068103916004908051395030101c11070f4111080e0f0001000152540d090007070050001d03070300040801c2d10000b130001c0c105449800a030310a4030100c0658182600d01c500551700b0012500840407660600e40d00c5010540c0260701590b08030910240c000303107054444c40150702e141c0c01030700700d02c2102c0e201040341c01e0185010405030741e00310628540f02602a100d80070f90701545030007800c000e25003a0080381121085118940d151a0141c00a09021600a0304100607466181714503140c5140e500785900c819501d101c20 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203571016 1250 203569766 203569823
    0x206210a0216082206030c0905010804080a0f050d140402090901051501080903070b04080c060115090311060c1005010302120c01050d051503061008010c0305040f060e03130306020403 80
    0x600c9604403020070340d03540040b50f0069030700c2d4031510110460302c03981d044048811300140107140c40004d0000a0320b00043e00d00c7e0099840b0360f040005500810000508070340940e41d1070021410304000c41e0300c2e003040c140e619014801c81d014005181810740c0e44000401d4040304c0c0514025140032481d512564030b154243e030340458040c0034560940c260500e04c1d510540f245903000001005072820403a07d940e60b5a2051000d4800303540150300400c8280c0509800d001c1c0c180141841302104c2c0490000c50805000821584409082c0341c02401c0300450030307203034a070885044000b95016907480e8010340e100400100801c0c0802e0340152502c05d408402850000761320305000300c0507103071641070440701511035010340401440340c0c1507070002601249403030b181080054001d0302034950b25507900e0b00700118903003191400a100ca0403d410001408082407400b00c9604841d508100042115601d01a90520310f02c9015035032000510941400014070070039134003501c00d07640b25400b000602100d5001099610981 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203572266 1250 203571016 203571037
    0xb06060a120b011e17070309110108041b06030204051c0b1f09060e0702010e01020a210b100c0b0a06050901031211030f180a0302060906070c0306020f25030f0e0d0206210a02 76
    0x180c4980059030207120100d5000c0d101c0c0c0c1c115041f5202c104292800b00d0dc1c0c55210001007a0003040c2031101d86050401000c4c000d4000038180340c040e1058a44010740200942a5810100460000f45581d9481544640546034091040c00000c1c0c3ea600b000503030140403509900154600703c2102404501802241c4032141142d03192102c0c180c3c5941c1d09a51119030450804006503500b2501704223440d9802d4141d0040c0d4580c440c0c00c4841c04900303042000a000520b4180302c2482c09605102507038480e41d560381034981000f1410740c01c80066400b503c1c11224030700903500700e100106141400c034500f4801848a0101a0580800104d4603002e00c4160001404002d50104050110010900302000500380150003001d03110300a41e941c0e2640001c0341d0260b0f621284601d000541044425101e20b442084918880800c0c16000815180200700c104402d541c1c400b00610054102c0792542c400100d1001550014501c0c0c2d51a010342e0300310100c014a0054811601c41400001150402a4400e131113280c0034303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203573516 1250 203572266 203572283
    0x30804150626071e030314030403120504080d09050c030f060c07060c05040b0a030203101502060a05090a1505010905060303030907030f230105040b06060a120b011e17070309 76
    0x880480101d04850740d030038030041c0b034896007400082c01c07844051005842d00b0b41c002c140c42440e042d81401000f403800b180340a40e0444081084c0000641c1c031003100000200c4003140003c5984451800c0101c1e441108081c07a180342c10003065406000b40491007003000c940c00c5084945004590519544401040701d604001c50400c0c403e0801184103604102001c01c03480c81d020380ba058032004100e41075000741c80b4030800240d002c4100300c0e01d2404c8680b03c001404c100c49400c2d078041584a0b0080d40c4440c01410b2038010b0b500c401c0480d010392400c1001c1c4000c05d610251040b000404416a140109807d1003011501e41c00c04000c100141000310440307005200090107410900e00b19180d0700c038032059600301140c4141a03138100c02c090b4000083c0128510b6461340000ca0313035081c28280140c000740b020f803495220360020000b141c101a00821401610b503401140410200700704070040c2c4602c910000c5100d81c110b03a010040300000d40c0140e20103810794002030000202c0d10b5410342202102c0c08614014a06413 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203574766 1250 203573516 203573549
    0x180c030a0b062808030703030b01080f04200402040e15040504030c0b0411090a090606050613140402090d03091502060705030a0b120f150c1602240301030308041506 72
    0x4051040d5070f1450104038000c0030102c4400c0c04a100c1c840d040d84020069040420341e80c00301a07041c00344040d00c1c4000d107405070311820440075003802c22101410091941ca2015002640c444601c0c41e2054000d00041046480c0c560b07903c0a180403444c00c640480c51100d11201d81ea41c2803400f449024003c540603a00d541c40003900b40e40b01549070750080c6c01030f01c10700100490000c0560340d00b4806403094055040c0400d2018061402d00c0640ea100d07040507100d41003e220014951701c0030b0360031204940e000001441e1034031000d00410002c1c400c48829940000415220600345500101140300300c9890400031030b00d80c1c0300e400007242c94180070303101c10001803820008140c10010903000040c00c0e10005200c2ca41d1100000c5960f40391080300901c2201c907411104030714544d50744e0b803000329a00c8400e00c0511381c900320045e51000130640d00840f0003841201c0b6108020b41d003540c0071074465651071803600b030f0715521350712401d025100541c100c0c1c00304c3d50b603c0e440c11201c04c0c1103114010358040303540c10751126400c0c1e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203576016 1250 203574766 203574769
    0x1a1309050a0b0709030f0804030210021b01050d06031a0916050609101824030603080703110a0b09100609020702011d0d0b040c050f030f07050d03030212180c030a0b06 73
    0xc10082c0c0f0200420140f00408800f03c0c00e0410b410740e0a81c818030b2815619403451051015919002030000c0654000d00075840c08140380480e25401e0040900e1312503910002c101500c0010000b603000584141582e1003a9000c1d01801d80e1014000d0791a07500b00d609400300340040b12460700b501d000f01074110205109074046810150003c20701c048050418421085c0700e5180c10241349882d521580781c0301c1ca1442c1d540480642c02c4c0c420101072002c0e00c0c062000e6810341c1c0380d10031284106035000b02001010108228400d000740245044258040340c0c0980300e007000c2d6005581c880c207194003070143e54039100001880398000d100301c0701c0d19a4107840715284560403540d10a1002c940c1c070141500401210124400641c400b03103003511452094032030101060409040c08104205a1a00c034060f601030031307201404074000110041218400c0b100c8113130088607441c00300c0c043d014036540040b00050b02001c2c4244c180321001900042c80e41a0100c3e121010311008145d0b60750034940c1c014200b102501c0c0400d246 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203577266 1250 203576016 203576033
    0x3020304060e01090b04060c090f05060a0216090c020705010c15050403031e0e071409010e06060f0403030c1511070f020303120103050d020c01020105041a04020f041a1309050a 77
    0x424015400000c0b51001a00d00500f5601865401c13250921080204010043d1610034183d1010071840c0001441381408440f851105c040d02589114501c0071440880c420320800224102120452941940710b035190b032004045e0043c880e144001d40101034002c541c07544140d00c04131035182c00c802040f5190313842103083d00c020880075100350100354442c100082071b441d0000c42c242110b4071801c00020180b01d5005841e003814141c3c2c1080e4807503c901c1d00007000359511b9050075419504018032010187d200e5800041031440303030880600383c448002c03c0003c141500080d614250030b01400110707444c55154050340c02190070001a025054009100c0714000c0340244980310007041c4043e040b28035150500c400f01c206550241d2048035198030100d066038070182d060082d04000002800288154241690341e810b0f052450151065001d6a4000060543d0303181c0003185820640070708200181030140300f03c011b1480b02c040f4880d0140912000f51410038640d48034a024940c1c00c03a005c0e101001007599030300c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203578516 1250 203577266 203577271
    0x604030501140907061403070f0c170403020a0b070515090c150714070302030d0e010309020910030311030903060604181b08010b030307050715090e0709090b04022814271f030203 78
    0x104680f2921540029201040e40310644030030091f00f40c2c4450dd14810070080701182d4100d9231001a00344041c01c006000000c040700c90ba03070b942d40300b5400f90391107519691034000500c1c07026a2240754103d415802d02404001080002e000b41548103c15252240c060360714000e41c4002501075100e100d951815900c1407400b0340b01d0301014900440c54554517000204e08030401d44a02c59204017600d0300700b08158000c0040303800c0da2961409581000107180000e41c0384d82c40142018002c0b40c5982004e220500307110b075006145644520640b0b5542c4035240091030340340d0729026074205903213854500d1005203000815076164540c0300005003000703400c2a40780b0f1505280d00716014107120110300c012600c003001540d142c0c8501c0b102e03515481500c1c9070004000c2a0390014140a008520400080d04060700c03c0021040d14035040d10381c00da112503000b604603120b80c52841701c01c5450030040303040400c1c407014038003064103000c44100d291000c0821004012182c1080e06400e048000400c1e4a0f1141b90b0080d000b455 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203579766 1250 203578516 203578547
    0x1306051501030b01020a0c380c0c0a0b0319060801020c0601050907020a2004180515010501110a03031a03250e0903040e270604170306030709020306060403050114090706140307 77
    0xb02d0301451103030141c0030b2400c2d00c0248c005141d004644484120b1042196002680c01200c005280a10302014990b8a01c030142c444250b409050440710a200e10a401403401030070302d400215501d00084401d03540740e0700203024551186188901258403184001901e80d042a085011203103408035103544c0e01c444481c1d1518194000c1d03128001050031072500300e00601c40900500c050106210303500d00c41c0c8040001600f080b8180f00c1e04920007513103040006031108910303905090002c0c4036040c6c041d08560b080501c0200c035a040c41020300d044510000340c4511800c010561105800c03450f00c0e0300c000c0ba0704a81c120354005880d4410300080007401c40110850350811042c281d56100e200c800c2030701d0304500d000c9401407262a031245c0144400c21062400050300c050302c004900b13042d810700c04002511020684a0540790755004000702c1d00d1940e070802120021a4448001c000311080c40c0e001041d080000c988805d844d001d44200010030900903600c200c42e01c1440c4149a18550303954006a8843d4010240034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203581016 1250 203579766 203579819
    0x60b040b1513051f03050f040c03150b0a0b07030201060909023102040312081602060109112104170304210302390a1a1306051501030b01020a0c 63
    0xc0c86460b00348034461000c680e58035400d1303440b15000c40941580d0f0b02514840c500c9034501700700004034000ba4000011f42e42d001d400384044c484036601c00000342040b1200741782d00010aa000003003080601000b0f1121500c00d80081c02880da4a828800884000110281d00310301c4424151400307401c90360715105a0001605100b101800b40390009c0100e070030070340046038a01e04414040d0b8800340c00001c0c0f03652103a000403c5803800c4140000c002c5d180c80c018400e0b010310507191000c10050038104800c0d240c11203450203904034040709a068604a0b02010389080e60385800c4581c18010215480045910454002c154698404006900c10b00c0d10410307080d4036000c142d424840c1901ea03016043c0b2020003114062141c43d42480c41da00040b0480e9100e40001c8030550100b40d0f19400188030035000d411400a813951805140e03100107106030821030a01004090070f250101b003000982a000307038150005e400ba0b8040045803084001a0b136109031102d4058000940740d14200810000640f040411a2801018 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203582266 1250 203581016 203581019
    0xe060d08040803130504060806071709030f070c0311152703030d060303080603030c1b01030603050d02101a060d050402031908071217190212040f060b040b1513 70
    0x1c0e03d065402414000030740c100e0480c01000507242601404000c0c118a1010f4007071400c1c09c1d08090100444a000c14600520040006408005c00d00689840715a00741d82c2a0752a0b001d0301e010a000c114601040b9443d070b02e2100100c0351401c01500c51900800c220369030074540030401100c0c084145100c2c415031030b44480000380f000300361003e20142c0f2040000700c4c0c0114500c0d095160140443d00d00a01c520f000364014003034584d0142c2c0000c2c044240c09907a100341c044070030001d001203011348102d130000381180c0305021125907940e50018500d02030031418141085544018121049414240001e496120000b8850b07241556020340c07105400034402811030300ca07000160301001c40c12014800664a90001050074001d001141a0144c9458407602c0d02c010401c040e024007803840100030704611a98403403c02c00c1c280c414250707411a003074400403e0081450385080d140c58821000d00741400ca61340750070b10307890712107031f0800f40078042c04010014080d07100142c2d141c42d00c40180e000412285400b4034800c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203583516 1250 203582266 203582279
    0x10090b0d140a030e01020303070207051203040f080d080702011416031407030207021206040b040f0c1805150f0a050103021806040608250503061e0a08010c0f05040e060d0804 76
    0x1d14040e19031081000d0030600d000e6040180080200d6011641550020030402c40b1182c2d0200b81e45c2d040d41c0003101c2d442c4040c2c0039aa003152960140e90044101095400c2011401d00f80c0080c816900500681c0d41c88620781d92140c0403400d07111020313480d4040001c96004911031002c6030090940b10f80042c40c001a00415580a15580c4201554200e000c2940062004113508205810005104002c00100280d0425a4403042071242c010f1002e418a80b142c0c8000040100341030700d1400503d0303009000304080900e2810903000717050503910140142980010407100d41805100281ca1090060403e055589444010f50183d0311283c00101d404a00c0c100050041d0b0b107210241c0040c0003203541d40b5451b45000010000341020a64203480e02c454801ea00c44181507004007101d07030080d815100c0d11006502580710000e031001c0ea0f0400f503846031080d88049410307481540a00d0180c8103560701c003510310055040950300340c4214010581c0c05c410724000a28141040030461030201c0c420b803c80c0b80b8069031400b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203584766 1250 203583516 203583533
    0x9051008090f070f0518010e010b030c070803010905101205060106030b0f0402030c1b0a21030204050d030807020607211109030a06020903011b050a030e010b030a03030f050106050310090b0d 83
    0x400045401301d801d803052206040081c1e40c0d007005880101c0d0f100740f80d410501222031a4505118903045405d0010020304048540b1080c0c1e130085500c00720711a104c1d611103041d0800341004171002c0b10100c8078803030005804c0300700300070060300642c200d006802642d00348001140a03090f5040801d030400d00006e040b14442d00c50344000c604c5052210006900c0e0320310b490058988a03203000340b00145038030070300c0c4602c041580104180e40070441c00d00600c61801550358254068061580038031f43c0201903d004509060300566402e102c0c1507240c1c20748031a582c0702d100c25288840380c0c0300d46000c500b07042c4406844001c4075a012102d51664100d04900348200d01000a140c103007009011115550082096825801c00f401100780c1e1000a0500e00344000102c0f40060403801400302100400d034840450344490f500a44c0030b4040317154058103465102134a81409405440d9a00b42103680601d000000910355108900340c034068141201c560042a2804003c80090311800080c1e69026810030134a400050103070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203586016 1250 203584766 203584769
    0xc030f1b050f010510060801181b0f110318010507050102070b090a1b050906090a0605032e09050303011502010f1d010c0c021f0201061e1509051008090f07 68
    0x40e0000c02c00504003102540c2540c2c00a410f840035000081740c2401040d07004a000d5041d10a1440d017070360490030206455000d002080d50380f1525a845000f494030141c1e0081d100d44c00d003100c0e40c807860300d06452052119540d1040c2d9584000c00760200100c0002907210310010082a401032001606280650722260000d06c000c3d1004009640012042810004009100c00a041d0030031480700b100d5103800c010400100c4000d000c288921625000100040801d600620140001504a0f5500702100c00010626031510f5950b07800030404403164181040b59008103a83c0a0303205000e14150703442e1070380c3c0000300881300500ea070079035407500a030032801129445200108a045240083d02504583c5c2540c212509482c048082200d010690000b50312000034405040001c21510804015801c0c8103e0040031a900402552150f0b500c1480d486083d00409030300340c480609280482c040c40100170744a0800602c5076035004401c900e20340101301c0c011203040d5409281c10041e505200c80481d01141811403a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203587266 1250 203586016 203586023
    0x801090314130e09030c0f0706030b0306060a0317162102010209101b05010203010b070506010608010e04020f0411030a05010e0106050a09150c02090901020d0f0203070c030f1b 77
    0x1944842014540e00c000d50050000c10215814544001d5001e04003015000e406040d510300c03803807030100304602400c10807611440c10440503610000003001c18651039440c140b182c00002410584100150719010072050301551006211001040c82d503580c0c080e5004c811150814000d40901116154401d00e001d40c07602e030b40c0300300d40c0c160240500004c1c84100744000f140803011a1701c1031050100c20345400d600b401a510301c5040c45218100e0305c4062040c0422008401089d550012000203951040d82001c0e1079401d10603015105245c1c1c84031800c4840e08802d112301c1015101c10300114003d410700c0317504020035040181001c24440c0120040346026401629540000d5641d00010446000d00d031442a014101074541185040807001c0010303c2142580201d40d00c4d400705113282c0c149180202d080c0c04103281e0242c49500c4615101c10098000c1d0040f00002a5140c10841d01c06120303101ea20840b885011aa1511000d20705980c60884850b84a010190184008000d0300b04404a2300803c1144040c803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203588516 1250 203587266 203587271
    0xe030d05150d0506090615100e0307090c031b0201110304320a02040c0305060d030305150405040804080d03060b040b09040624020c09280b10030522080301091a0a0801 73
    0x100241c5c0186480c100501d05010803c49002d42c41c86a03580e841c0c003040703c000741d1030b208540500910000b4100315035030344024903540c80c12074001c0c803094040d0042c40d0f10b1074140c0f480c0810b0b00c590700c405a00341c0d180600317102d04420f030401c0000e0001c1c106011075226a5030600e003d074074410540c200719940140f0740d441185640e10059090f021440e06008040c0f00d680e80b0318050200e030a04201061a400348105d000b030034583c950000038010300c5912314010008000a1082c0308034141810654034652060155811074020002c070103200742d010b0b004032800c80d8140076100345400c1c903140760021550482c1c2002d944c41511407800040311807070f41e00e1151900461440c403454002c0011302c040d2820703143e001801e01503140501001035010304401400f141201c101d00741020480d080383c855004029480c0425400728242c08044040741c0d00d03030b00951081155540b11070707000c5003810248440c586007510007026503100f00010f01420f1503c1d00300200c440b00003240d842600042c0c00020300c1902d0340d90001e52541c1c0d0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203589766 1250 203588516 203588521
    0xc0e18150a0e280f0501052502060c0d090212010f1a010809120a09030803040b0a0c02030309100c030b060d0507090b12010312050c01051e0a0e030d05150d0506 70
    0x20960b20880e50180b0740d0100604504032041080940c402c20500307102001001c201000301406107144100554690210080255151121000100d014001c0b414030000612003c03d807501030000031445c1c00340c01490081d50900d01c0300c1c40c0c44409001908002c81c3c1041800c02c400c0074081d070074001d10400400f0000089140c00a20601c00001081001c03043e041095003400d110000001041050940080c6070000382d41d40b403400c8040d41c401442e944014081c040000400090000e1440d68901440000c0010b0000e81e51014040783c2d00c2c001a124103401e0703049584560480070040c5e10001d556421418041482000702000600da80c1100e007240c00919103c000b04a8000da01c42c1c2d402c80688210b00341c0504040002d801071003c03402c140002002030b801c2c0900c1c1d1042e60301403000da60482d03503603000078096480c019000c03007103c1030401d0403c601c10343c028000c42c503080204d0142c02007059121000b1810140106131002c0038210241894000c641e1100340750b46103807a044001c0748280c2c0904000d0501d030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203591016 1250 203589766 203589781
    0x1d0d06022a1504060504050703020a0e06040f230403200319020105010e040b0406180f02030f0729070f030207030510110f18061b0c0d0c0e1815 63
    0x385460241e505aa0000300072900907190542e69140c105070011070019995442d403800a11305440c5400103075002100d1000000c0b4480e02140300c038441c1405440900900e0745000111003900c50079a01e1091049045104461054400c444958854001c0c648190185610180002c1c0f0700c00d69000c408031600000b50303001054a40e801400c08201c03162008101c07942c03409240140140c00500b0040c1618945008981030203040c2e00681e24040000760488100071207468804402c20000d10128013038040d1508640c44440040381d41380444030b020012000f00c21703041c18407528624a000c40341e28000c00500c05100400d02011074040c15901c20340051080e03d080d41042440e040b00c490714101c62509004039440381e2810701040e00c0080c2600481c0a4860951014880c2c10401203000b290700400e01151000041f80703c120840080d00a00041d2140c84442200740280b1100014019002d100c40003030400045140f451020b034400c80107060001c00400c01c60700ea504024020300d40c2e0100380001010711840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203592266 1250 203591016 203591077
    0x1210050106050d110a0e0d06020906120103120c05030913060308070503040611070614070302010212162604030c2609090c0702031011090d120e010c031d0d0602 70
    0x44009813102810a00983c400510101e13124121501840741140614104503403901034480c468001403025803076041490442c45180000d22041d10621054050115054080d000346100150810040c2d454115540244000d070010400700e0031984d681c5000000226881358040c2a0082c821400345d80d0703651070088000c1c4007a030315103120340340b540200200300582ca070854001c9051500144040782c41b81d140703040036402801040c043c0148426102c0c100139044207401c1103508140b249484000994105001002c0600a0440075007407082c401d40114000c02d00070060100000e100d09038a0454118030b408001c1c10101d003010011200101080313070081c034980110401e500c00d40401d20282003c0c001d800007942d03096070404010141342e48055504410f203e08041b9610500050042c00100d807951600300510b400088a040c0091741c20780030032410b5840391840c0104903402d9603600d404100600500c1d100041e02c0c0e694190302103107500700701c1c000410360700181c004c01082078030030404150402d41700c02e02c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203593516 1250 203592266 203592281
    0x20f060c070905040c1e0e10090903110d0c0c1202120a0b0702010605151c0e0106030302061005010c12050c01090c0311090a050702030a050903030408010e03040f090216021210050106050d 82
    0x2415030b054240d0b0b400f0070203010425007c80350441c0324034480b40c86841001c0d4640203030b40c100320055828840380000741341c0c0141c89200e4550b07030341045801c9841004c00841d503083c1c01c0c09004141c00100302040103030708803285412031807030300040c40b41c0020000f01c1c1d8840e1402231030000403210b90305500204248583c0a220302d500500c2e00365104e402d40341c48284024120f00c15010010107a2070320284504c0005800e81c40800325042542c02040040c0c4c8034140a503840100f16081c1c884d00070340c10700104003540b1840452100701c1d4408810510500740382400d41b00c0380c0013944500b869640e11403030140400c2218110200450090064003040702e2007409000c074480004000e42c044504007001c0c055140d60000071500480c88514100ea252100000044d066114503849200c9560031b01140d0300b84240080018400c44031980140e02500765074900e4442a4062103902014071209244041c01500b024a41e0254103203444094032044929150342e00101c4800f0381100c4001200810351620141440c4075000f07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203594766 1250 203593516 203593529
    0x312040507060c120c03110d030e07050a060c08180d0804091803020628060f0519061403060f0915040b040207050a03051b190c050904030c020f060c070905040c 70
    0x100e110398591076010401d8010304d001000c00582d24001c006051142d11143d0f2815001000d42c0d52402d034904008000c4c054840841d5010b0142d0b810008161901d8100ba2084071274946602d42c0740c49150302d4007401500481070340c0d1080c441040c2d1008480e03948039443c176905446140e40546890508042d403040b240b100182e062040b0305a4400c10210341c0002d410b59111181400340ca20075803169580f0354400900191041c502400d0403c08940355064441d4036090b110190760303001d840543d502000085a030a07110b14400314110018442852030880700540e03110034040c05e48580703846a803003c00c21080040b50a90f409080707801010060740303820300581c0348050317080320b09504005058440d20f0f1140c00d45080103040c440005414040c6400f031401c0d00c070442c84c01c00244d4401d008540c1d949008600540d038100c9600014030400706840c42c08a03a03203405160543da40521010b096070a1000e03180c08124060b502c03034014400526088810410900a8406136030b0200b0a0309141c42c00020f690380c581c0022 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203596016 1250 203594766 203594777
    0x8031b0c0904061107060e101b050d0b060c0a030206040c06030902130207020d02060301030609050c0619080c2502130b032a15032403030f071103031204050706 70
    0x200c5999020907150072a4100100061245461044020f5071041c0e510050a080c00c1c07070340f1020030401c00320344002d441c680b40d0000c2c00300100d203440c10000c50b0380031143d12010940c140048514810203500c03480402d0000340411b807401c140110710a203000c03d4501c4c1280140d100d4802c00c0f0401052a19460040009003070510202c3c6003640060b140c03602001281000c2580403400b5429541d4403142030740140d03006000c20340c2d296142d0038101c001d003600c51001e40300c510507a4400720541c10043d08480c201c80250030441703480c4618010403202100c2c00303010002880300900c090355207a0b01620f1070002060750445003241b410307440d1050184044002c03030312111a80c80e020420f50191400b0504c0c20080112030114999460a610700c10354141d0390010190300007005126114024003500003c40c040d01da513980c648540c082141380580644083c20a01d83c154000b0301c0442502442100900081c2c0d10070000701080c5020403011a01c8d41c0c100210740100070702d1b16024402072000030b000d8080507215a1812 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203597122 1106 203596016 203596033
    0x10c020a030602030103050318010c0206180f030102040f05090c04060c030c0c03050105070323251101020a020a1a060303030105060c010e070b18010206360708031b 72
    0x81070522045c4009d40d01280d030203000c00f03807070305540248050320304902114964051042c0e60801a08043d01c0715a039841c80d602070003d880a0050002c4850100d0300e080704200c0c058401500c8495802e904001c103110032603000c1705d2070344135940605021510010b01e26054000c000d480d0f101420070752810301030040f002e6158210202614030a41100c001066070103603080c0c001070540e1050800b0501140c01900742014481d100386000d09170620359800e00d07201c0146400c0e0390140001e400160840e25001041240f51420007031002c858441c413100310703e800c8012903138901c01802424030074180800c00381c0018000f5042000011681c40c281d41070255030380e0308141280c0040514621000b2214800c168035440020014821004141c0103a80402608400c1c1c002d60121182104c807828200f840ca1000f940800c000740c01040c10200a41c1d40d10322000c035103803000b200c100e440f00e502d8120584 = true := by decide +kernel

theorem cover : BRFrame.Cov 203417266 203597122 := by
  have h0 := BRFrame.cov_init 203417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203417266 ≤ n) (h2 : n < 203597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
