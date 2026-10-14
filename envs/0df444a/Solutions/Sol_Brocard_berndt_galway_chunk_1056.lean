-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:02:19.087876+00:00
-- url     : https://prove2.me/submissions/ce117a22-f8dc-41d1-ab9b-14ccb3aba610

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 189748201 ≤ n < 189928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 189749451 1250 189748201 189748211
    0x240c0e0a050a17120a0305010501080106090e0406050919050703020405010e092e0525030203011a0d1515080a0b0a090209010e030111301902070204021813 68
    0x616a111200502a0b070081c03040d42083d8140c2d41800e51a14056400403090703000086074840300300d1ba040d130082e4101c035001d99501065980c1c0d09400e440030000c9024101c07855000c0d030300040c0810311640100740c000c4080030031100801414000964400f0140c0c2c01204c02e0b130410002001580307804e008850240901c80c007400558285900e610b559010400341420310359008103640e00300c10300071030390701c1c405840020b2041c0031515020507240e9070026503041c40a17031902003509544106102e4401c1d80d0681e5007070025004808804001031000b9000f0488009116442d50307203018440e460502004014081c5503070000c013192464a029005250050524490324605070b254101c542d41c00d4138090880d4600540107075107840c01c0c0012100c5403e80304081c0d40643c03d000085100149440040035007945101400b44160103400c0d160103401c1c0ca4040b1032100002c0800881c1c1c4824030f080000c03110044c0f541c001071030840a03a01040c1a40c11101c40160001c121511400d154140203800a4611400400401c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 189750701 1250 189749451 189749459
    0x5090102092103070606030c090f09030207090b06090a0305010c0f0c02100302030a020d152309150613081c0201020307080f0c0702030a060203060f030d050d0504240c0e0a 75
    0x904800b49280080c01c824107801c1061000414401c5a00e101e41121040c04801c1e12410314190307009452040b1403416152000700d1802003480c0c820b410801e54582e019000f42c03441c10460502505141a0140e030160007000b41d01030316908c1c1480d01008600c682c0012599001a80c80500740c3c00c0304075074403c14040401e5451005940c0e120781d1452401850030010303100d0300d520800c40c00074054440c89180e5035180241c0c0b280c030009100c1030041220400d04002920901908114402800c016425034004010001192404620904201007580080c0100c0d0503e071481488144e884041d42c40071200707800c055405801d005090b0303940150000580000e5144d403c0c506402404000000c0c0000301c00d00710000400c41d142c1608088801a0f41c004044030545081420508000d600680d0300500c02c4031000e17403104450401064050030400700d51a500e0a001520b0002c02c0a40f500510848a4000141d0080c000f000203020000c51100030b10000a07010040404c081d1648003031040b0700d4803a181c40f0b23034200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 189751951 1250 189750701 189750709
    0x151005030106080c040308270a0e0a11071a270d030b01020708031309150b04030303051003060e060402010305150f010302070501020405060f070b06011b030c020d1b090509010209 78
    0x6411150030f4682401107aa4040c0e04107402d002c1d42d0001001c0356000520402624040300b500d40d1310303030300d10042142c0703519a0701d08214a0785901d100303407181400c2540001e00401c0c0c2d50f0340841c60216040f40075500e4000e40fa80da54030040c600204d04048c164000c4e091128003080c040c0c41d050201d130741d82424000114481001c130b50340d40181359604101501e54500c002964400d0140034010813060007100e03201c030810045880d0420550090303c0056161040e03c0c040d1815898003c1c0842c1c0050100e54581070464600310040c11008000c00c64001c648600040040c000380b0800104c60300c14006008603041c10310004003940c402400c48003956451800403015a40d0f04000070300610024200140c0d00c181a15003140603008540c006a8011408190301700b8403840c500003401c01c0d5114204000303241d80da03a0010345440d80940000d117403c14461128000103802031445616072400108082481c51840e070364410204030f1a000050405184d480070041d480c1c50b801241c2d00081c500c0025400d0603042c0c1c01007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 189753201 1250 189751951 189751957
    0x615030402040902180c09040f060e0403080a06120308090f010501030c14010207091815110702060c0307050109050d030c0c1220030301080d110c0108040227040605151005 75
    0x1c0d110383e03030750b120000c01c40d030307802d0103906108204185a00071450141c4290406800c046403442c011420000c1c440303d6010944180700c161240900400061b807600d8504070f8100c6001009281401d90743c11002c1544a900380e03407941561711941d2018000e1401c0c0745080e082c40c08005d41c4501c0c903070400d0010300000d0440001001583c80c450080e90313001d05020700403450b02038690310030380c00c1600e00f40159208800302e22008031040c4c021040004110444807442c0d08481c10440c0340f90320f80109102500040c036111000b0808480204100da00b49109034841d0781c212031296804481c90380c045860940d4290301800b551800e00d12a040c503000d031381810744511040309102da00401c10000c0c40307800003800d411064140d520089201d8100d980f01c0d80c441c004a981c518000181d40d021500d070b00311a0324a1180005c114500305010f030f44901003503c5580c284428030302035185c00007002d1841c021110b14503815404283c400d41c041c2c600030a0384d00b841302c1c61903d0885800d00035400b8a401a1440c0d6001e5001003c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 189754451 1250 189753201 189753203
    0xa1a0706111e0904140a0902030d020303070504050d021807090e060a030503090f030f0a030c0204050c0414120f1906050c0301321507060e0102031902131e080606150304 74
    0x94a83e0350510440098000c1600c5000c5099890144080c00304c0c04100e0f0740300c080090300c00d80c222040000f5400099079a03000c22181d00700019400c020a01182c02d05c001c411119900c082e0000d001c03c0000c0c1003104150b2002c40301b00001070005001085403602c60740c40fa940214080d15841c58003402e6850341e80c2c0b00e1040b008268000c0c81e061069600549040081040008034041501e4803070586140041c00802a9803007640308600b0800403409464030b85046030215480354040206101501091185403c0c03440c1c4a80124041d2040e0000042024000603d0b13100510110802c81c001610b480d80880303202402c1d84840440500042c03010b41080c03101c910112010718282a45c01c0107030060201e1500c2e405450b150050701e03040e02d403110300860f500901111449824103205000d01890140d00700e0004450307a07290546200a89820165264002d1020440c0d000740350702503944034046d8045040c41c200342e4165001801104104801d000d200c29130700014102c440084400c050b01205c0707010b00010f44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 189755701 1250 189754451 189754507
    0x40c030606050f160204090b0106110d080106120603060c05090a08061308070f050703081b0606060405041104050604080325020d150207060905030307090b0c0a060b0a1a070611 77
    0x2550403103c503251a407104c18180e0081c8148001c2d40d0614100e15401002c3c4581400302d218035104a921040c00300c0c2c00b41804002e5610800a68600300c0d04aa020045021141009a48040110100d0124000c03245000c00c90340b50781d543c0e05c03038001c2403201c0495aa03202094030b4000d1424002030070f01081c00100c026403c81441c40c0c841c12207003410341d205401c41c00c000f000c0344220f00c0000200300100c005004504032209050319514a900040c40d11051704a5840c0c1c3c2c001c04c100b1003405140f40070307881042d000020f400c44509080d26200032a00740e03803158212010607800421301a0951026079441d0300341d490303103801854a4000d15400b18440388500c90004081904000341078100e0400769050398010f680000d0144611078a40c03c00300d460741d2068440a0015100c41408203008040000301d601d03001a00009000c0c030070301c1e5200e44004002b00d000c82d0740c2c040a00c00000a0000c0e4804044080500c4603040e00e66407220751605408940e0089018501580300740103060400030341c180b0345403503201c0b818 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 189756951 1250 189755701 189755707
    0xd03020105011703390706020a060f020c07050108150405180d0f0e060a030f0504031d030712020f01110706110c01080c0703080601021e031201060c121107120809040c030606050f 78
    0x650450f51040c001301741c0300400d2040f9080014803503800940c64400c07034041c00081104041410700d4006030302c0f0ba00f040a42961007808100706d00c2d44504000d580c0100781c8104512403441c8000010256403095800100d01c582d04112510042c400344841c0d800081c1300d080444003202c4842028022044a0840e41e200311001b150031706019000760007401807040c140341c0c100080d103068600945040c00f110170801295405159054280c20005070800c1038460103000401048090fa003048038161842501504200c501680340f14003500401030640606002d8880b0041110854546e07450445241091070411100c00103100c030300714100c0210356100390103150076038050ba40ca90050345800001ea5a40640c40500d001c40e907000000400901480040700c1c040d02520707681e030901225000741200024002e5079641c00c0c40e41180303010b50313140308640d020b0038140c0f070900d59901000c0340100140281600c21480008070344640d46003034801c000000c0b9090a040020718200000100a4003415440360a980d80c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 189758201 1250 189756951 189757027
    0x603010b030a240219020109030f050301080709020f090603010314190b0105040c0201270b01050906060f0a020c060f030103050c01020a24020f04090b1309021e0f0d03020105011703 79
    0x1a130100c0e44000a021040c0482d241d219600900818030010264005580b0014110a0900c60b80c202c0c0e040b2402c400050140d80d040c024030b14000c1d030025046103182541080002210b1315483c000d14021800b03441804102030041600c941003d4560000d40c8441c4070702070b02c5400156007081514151031003a14002030a01125105a0040c0098044820016440d54681d0480008011841c035418800c4400120070f90340c440912840c50403d465243c1e12003030a12105248050001c05010780204d9403044902c07901482d0040f81a0703603c00c0081403000100003005002b400800c00c020340c4403034030031300c010020607402d0703100c6009840301c4107248252004034600d05d2007400320580540b03000c0c141d504882551940c1e10741c00000140400f040c070901035401911750406280309403080e046100e4024290351682220061170042e00c403803802c20701d5400a407034048080145c903403002010240380710750000100c40d4109000b4440c1c0344009041440564400c00100c8140c030b0a841d042c1c450201ea050800a00200c4c2c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 189759451 1250 189758201 189758273
    0x2010c0809010c0c030b0702160803300a06051e10120e1603050f0607020d08060a0b031005010305010803090a030f05150a06090b0109030b0609100503010f050603010b030a 75
    0x12241c0c0c00740c804e48101802106002065407503a0040c501502114400d5001ca00060009401480f8186940d0030034407182a8001048003500e2049405448841840421502e507007004003007910007000340c0d95a50414480c50410110701d07094079645104186044503564001510314050103044410450a2800400003d030316820656560b44980140d4460002c0c03422420303e018a13031711054a09206001d8540801c1c480880c285024108540c0500206140c480b0309880c001c101a01e45500321030480e0000480c103000c81c0c040c500600c11880007000131031414000405a40b010381100c4d140e90030821800c1c50030340d500341802085a9104410003440c2c100b900f0720508002c03203880420801c224000400401c40002e5111100303071010340c002003241000360001103521007540d000c004d00c54189880031031040c2c5000041c1940c400d0607140e4402c9843c2c0c40e0404242943c52410070910416110303c2407008520b02030160108189095000b40388440f000c0d01c0300c040001c03100700c2402c84174803111181c02c40d00e50 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 189760701 1250 189759451 189759467
    0x150504120e0f1305060f100c140c0a030501140c03070504180b0909070306230705091201021b0618031e0c0d091805010f0b0a0315080718050402010c080901 68
    0xc2c1c0100201010b05403240d00d800a48003c4803d10f20405c0c905910740c109281211340000695095a5654040c5036035a40d440101741c2190544d01c218441c0e0354240c206a6203001494018503c141c001140204061040302c2400002a005034100c61040c010040c540340d0040c2950300711000080c0b051200040c001c907020040090080c403d400420a0081000307a080000c1c00c4000c50b445400100088518400c150340c42200000f0000444405400401c2086101e031016110040c0010216080e4412482440c1e007242c1c855403403140e05928030608002001018001e440d8422040e406000120300c0f509551070316849960303402c0e44901019400002c0071043c1c41e080c0c0b0b0900d0103100032a1032140c450503000c1c000005500ca070024004402100341c9d45c1540c03502805040329032020240302094100450100e064014080c100c08141e6140c4100101d400f400c62031500030103c82d00a4440a8200413035020782140054002c0103440c140014000141d174000501c0030840d03002401c060700d4212040040700d59074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 189761951 1250 189760701 189760729
    0xf0d02030105070921020f01081e0709060306060302040f12081201091a03031305100c060203010905090712031d0a0e040b06120724051b060103150504120e 68
    0x262070700b000c100e400394000c18503030151424056000000240080c11009074411014000d410a580c500c030000c072035005d080b4258000b2801943c40f803881c5030b82035200c000900222924400120304c02c0c82004616058494400074001e5440d055180a040124404560314944541545030100c01040710174000c42400390381f024080323001c85240300e594030505980682584001b403003031440500040406494008111410501a100c4032030f00940780c0010000507000f022901c100b400303041041100015a14401540a818030f61000a0b181c10a0460706140143c182c0000203141d01c01e50032100801d4000b4100015100120b5207404082c05043c0440c0249440d50b00a071a60f4040005203c00c1001e50300340b0500c00c0c0c005450a036590314031900200c1d031f02d004a102d00072019205500a48010b602e100d908005d104142c20030030319184080040c103009004034076030440b580d00844018000c001c841da2882c440448851000e0205081644450080d030041210072010701042c1c818442e2981c8800032060810 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 189763201 1250 189761951 189761953
    0x1103120c12010303050a03060b09010c231212010e0c030a020310090e0109120827010b090f0709090204150305060406050301110a090e01030803060d050705030d0f120b030303060f0d0203 81
    0x1943d403458080c04035044401c2c1480801d081c0710021900e810884182c9201c0c0c201650b17410a08911600c96040c44401c021000300518901c02c41c802c0740c2c03035041200315800c1d015400d85664800200c5580e148114040e040810302c0b8800740f0a101705013021005881e0444051b203001070362511904120180e82034103034466100207040c0700101c1041001035100581c445d010b0030002504102c20354084496001c2191390300049900c20034440e00a503061400c0900140307010000103283d160813070025130340034411240402203114000070024910761041e0144014007901d4000d5040c541800340e07a403d0032000b07805800c10165a00d00080080d075668120500402c40a4000c001d0b101c49c0b580d6a00c0154805140c5a010649410300000c030000301180060403203800001e400e04580b03401080002c1ca0300940d4043d03a20b8415024042800d40d003d01481908012940312185001c2201c500540b004d4202c1e036050101ca80750070404951a2004001c80f41e015504a40240c503500002002070000842c014000c0d401d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 189764451 1250 189763201 189763237
    0xa030308071d100f020c0a06050415030902060403050c0a0e070203040e1513020a0f0c020a0b030613020301060c02100e0102060609070908120306011e1710030501230105011103120c 79
    0x5225000400084c20604075400e48a800714200c1c01d004080142d48500000204c080100700003044407030100a825040b04c0c5004280f051090300003513042d0700250000e407002d8006c24034404643c80d004c82128024800c103421949945484800a03490b8008c0e0b10505c51f02001c800c001030200106450b800151603402048210380750303071248d6800c0007500068030440100b214031130036a500b2406286004c5c40301e0b50042c00461300a0808008801d9500041c0038260091041200361900700480d00245000e00315a80d5a0403140103103004001c40602d00e4010201400b015610f881680c1c1da001c0340990303114200f902c2035401e0303441d000300485900b4100d41c00191507000b012500052400020011401030201340c3e01c82d14a2481500703000c0c0e03000b691021250104450010b844238109000e900345a204400187c2d0b00b60090b541c1e1509825aa520100c4084144259069110300c1c1d1600103174078090b210030300c2c0018008411500c0150b1702e1141459403510342c1c1003c03000503201c41200e001c40303820700005445100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 189765701 1250 189764451 189764479
    0x31b1109090114100323010e0a03051c140601030b0f1903050d02060c12090c0909010504020406081605090907051009030c0e1b0c070b04180b0a030308071d 68
    0xb000b842c03490020f081660b4600c0108030f030b0340440207904040da0382080050143d60318120000032074403280c40c3c2460702035407141c0b50544040c1050002c1d0001c0c80c000e03202d095440d0f2884188155103101e04003610481c1d07241481c40c04000d045000c1b282d902c000c0a00380010658001e4000a902c000289038070381e440405071044101f41d051022840d0101c070301ca17a044441d1074850000698072080211085000f0000501c042c0c00801d003125040e51300900c001c5d007030700c0c0e0040804002c00d8080d442118180780507912441800110309041c840c04000307062003405080c02500c0e4402e04498195140301c0c2a01c00c410a601080c5605018060000100b070300500c9100c0200d080030018006c4e65841c881514a21030042000400000c50718400d403140c43e002c6241400a412003034102016041504600c42d60300c21104040f85c82624400280040c0c001e00820040d0a10b0b5205043d040e5100c01030381c2c6000f42d00f0007104200190f00038400c1c641004450800ca140c20311107010b661754019449000c01c2d882070b010946c1c86 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 189766951 1250 189765701 189765703
    0x30c080d0f1a0906120a200409030e030f070605030106050703120204080f10091a04060e0d02100c0e0616050f0601121103010c02060f1807080d1704031b110909 70
    0xd0b4054080e560200d582c1e0718002040f00d04100150002d980e5008204818001443e0f410104c0030084258084c0e403002c7c2c810710102c2c0403a50410000c13030114020034040300031440c04224109401a83c1d10061409604008004006010601c40c0303900b07000c00803c18004041c0100c4603c9417401c01000c0c115111641c0e4070405640300280341018855004070940100c420310240203646a15810040030803442c07041c04400c0c0701c440c00003030050b946641d4a400321640e458050241840d10645da600612010780035036803c00807500c0f180e00000c2132000c0184410140d840b120152403424280c2040d007082e010341030520a00f0421400b4903d80b49000d8400049145203030400844055405031124074801003820041c1801c0f900c002988202503030002d0005840c04181880255000341c040e0440d407514048601428075190b2143c1001040350009060402c540d503210400c0c02601c1e004035000c040508054802400300111081208404005940501c041c091038031000349051070701920b8854640780103d829 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 189768201 1250 189766951 189766991
    0xe092104080109050318011706010f1e0e09010518160201150e0f0f0f04020904030e0a060908060f1003201302070210031e0b150a020601080c03060103030c080d0f 71
    0xb0146c1580245004042d41d442010681c10020407800c0c8a11582c40c1c0100560756510b81e0b502c5413040010a4801c11f508a6010100d1040703a80301c0d0315081c0480004a0410003103400513002103000d0b8850b80c3e1820343c0c2c0300c01803400b20b4000d11080b0080c5280d01d600c0307400328090841180706031070680c0c2030030b00042c07503100462486114014188404c225074a174a80e030300040c2ca00665030a1100070440d000f007409480d2500d041608248a4204128488000302c046001d2140c071341e01c481c003c1040c01c20200f01c41720052203880d80c014005c0300034003164035040f00400c00c14215400060b04c801c4c0103110072002958400350312082c030b0100804c4841088240310703020000e9841218100d02030301c0f0440c494241c0742d009000350013403540c03040498506000c0545440000705401c81500394400384402070003c00444450080c00190301d41d6014110ba0340c1402981480d111600e89690b01030f5001900400c0442e07402002c0301e18803a801301c01c9a985200008804c406042c64008428001d0315044001c1c089240b80c00740 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 189769451 1250 189768201 189768217
    0x51908030f07020a0b0705090a170a030e03010e0604140a06020d05040201030c02151801180623060a090c020c0a08010b01030f0515040203070215040c030c0e0921040801090503 77
    0xc5807116070b14036400300e0301c07903641c1080200b060381c01401180540340101c2c058503203607402800302d28510359144058800e10740301d5008203e41c0c2c0c01401404007459405100030300b902405400a00c040d00500e05081c1d66030200800150281816003c03013020020188101080c1c82e030003120542d02d4240d441c3d82d503401031405036000c9000c02d00d0f05c0015040280080b03100310140c9844103020000b40d030342c07582c1d01c02080c01d642110861035582c2c409500c82d4204030aa48101c01d030142e0300004101d000100c85110b202c8008038080e41c1c0b105260100442980c03a00805000d541070072602080380c014040051749045000b80440d98450618030b00811031450550008411280907a0b080c0210100c005482007150000e07185148892000705680c6503070b00b401d80003540c201c88503104131000300c4420024866025800d403421101c410030000c0800600107100c400401a0403950708404150401c0d00805546070845a004021109007880c1d080c8000c5a000503140108032010088c4400040703850010780f258081303e8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 189770701 1250 189769451 189769471
    0x40c0c06060f18140f150307120c0506040e160c0203010c020f060705040f050d02011812020307061d040b12190606080c0a1701020d020f03060108060f0d02010c05190803 74
    0x200750b219415034090001000440313100c81d00a43c40f28421070101035402000b8016400f90004214540d403820003410000b41303001440c0c00c0c0d1059451400007032001e00d0380e0000384594001d010911081c0c440900840c2c00a142c50781413441d00d481c014003079806070510140030398103500e01404d00d1080c50300403400f41d002c2c840b0482038980d030365200c0c0001c0e5483d0003680114411444064018825030034402c0e21000e045005052030411101c0003102440843d40d86d810040207200c0e4981a001103007410094040500100c1c11720800a80208045103011210444154819038071111040581d03210700754082d4900d101c10050301d480c0e0b4060b43c9280102c076609801164460f103459400510840080743d1041c455100800291f0030a140c008203000e0310010418030007455500f08140d44d00d0708010320003000f50040d415405a140e203848000500fa00c54000c2c60240100350800d60001d05035110700da0444026424201452242614104503240222110b0384031441c1d01821a12010320410202551040082070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 189771951 1250 189770701 189770729
    0xf100e01020c0a060c080d020408120a031506080f19111201050f0d0b070207152006040b0a09030903350a0906051c060b0d060b09060702040c0c06060f 66
    0x4090000c640e0913403280900103a060600e4000242c1e60500824204200303040141c10907854400350386c1800c000546040b41c012000a010f9030164041c0075001c000721400c585d60f81c14601d40440902410402409840d200c0d6450000404d100200c04a50705c11200c0c0304401c010003600983e0a0384542d0200943d04000c0004000000f5a40303812038040c03000c054042d03e18014000140c1d68030950460241101c0d055010300c4402250111b0903c207800d040c61072507035a10341c1c5c030100c07801038944141c0021031502554011b0010000801d000350b00d036035040214a440006c2e10320344c2e41411110140342d904001d2005445605095100a0302030028100032603178002e46028504000b401e80076031196402c2000411b6440d070781084000e0049024000009040e0303d149615008000e03544122a050340107030b03620f240b000c0b403038072940b83d1144201c402600c00b0381b83d510300d041030450020300700b4099404000e1207191150072458502d44900b5000c1c0107550b03c210140308207511107140d8007a00a40c1e000d2041483c11071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 189773201 1250 189771951 189771973
    0x3180d090617240109091b032901050c10020409090b06011d010f030e1f051305190f0b3306030703092f03070801020901020304140f100e0102 62
    0x5242e40b8025049111002224109035080c000100028200141400080800007540f121039004101d05000386d144081e51a03041c10002504407180c02115401080c1c3d20710514128108907080c040c60020b090038141d4451080703d8400c0d14059440198104140c0085000034081246400c110005482211148000d5031600011a00c8030004040c04040c0c4440301c1810b20154040ca0424a0a5101e0b19011030030b40241c240d41441e180c1c10280181600e0348591031002464198810340e50061480c095100c034142c1c464495503034402411210010082c08a10804104081241d5881c0c8031907010300803150a29000c4d6400c00280c5048000b11003188400d825a40003020350300c000d07460000000d01c001c1c1540c0360038a00320f0080c045c01e00105c8072080700a450121140b04c0d070b9000c44486a812003240007150070002072506000c0581c0c4541500da00610402c1c80b07607a004001c0d03a00f41c070310a080840003181d180000a110700440340d020740d00000c0000342d10400c540d100c0da8150003000c0c2031f000c03030b8a02261 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 189774451 1250 189773201 189773237
    0x301060506090603180715020d0e0108010501140c100c021510230d02060c0c03012003041202010b0414070f090b032406040906150305010308030c03180d0906 69
    0x5411402a4807840800000305001c3c00c4410005648030304e48111594161110301115400c00c80c07d0442016034040c400c000003455203e180d00c107102031b00f803800e003040d94907000001e8103001c81e0011250b110800824050382c1c80800300203400320030f80b010070184020b4140c000065119098880c036041400c0390880081c000190b88803540085039035006003000c1004038041d030548041002e6103e00c0e03100340b6040300301d405640c1d1030001d060b0b90640318003c1c2c8051035010041508440101c0d4003904030426052504202c0e0048100360703584180c0101040340740104d11401207006015a4110355400317441d00e10a292221400c076240351240a0544500700d540380051001d990200c128441c04c40b02203007c100160036420702d01c0205041c040302c04507000d502450710380000e1041c0c01035000b242c00d007984d40004100400d5401031a883e45540d50500300720315410760315540402d2000501c8410f24000000200c1d004075004a4407498a13004842900c01e05100309000070030901407480345000007544a5100b40c0b0b02d040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 189775701 1250 189774451 189774457
    0xb06090c0309101e0f020d0c110a1b0803070813050d0c06030b2b0201020105131e0809030d0201050601030b030111160c080a06090201030c030501050d030c0804230301060506 76
    0x268000405a00aa40e40a200074001304c0850a00e4072800304c004118183c400d0003203965a0140c6100547c0b2080c00712851000c8810b440d120201b00007030b8441040800d000405c40c441c1440d0003c440741e01c0d440d1024940302c1810f10075441808944800924401485017213805401ea4503902101654005d54031020000c080440b45805080d001c0980300030003006000741c1c0700700d20f442005401340c5810748d00100342450300341803008040c034440e01d8101007008561f030a120b02a4443d21213206001002c0c5244c4492514001010f40c240000500794900d809120058003036856101004048603c80e90041100034040c0c40e0076141940807904202102c1c415103018082c06d401c4505d003040a0b402d00c600302d46801344612904500361908464030700e0108007504107110b550000b500501c000b080d0741c00c0700d01c00101242c031811000c0040618000060110387d690108401c1c0d455090315101da031400c46070070102028400c90b40800400e1032030440d00b50b03803402c0074495403902070412402040002d0f034032818080340d84 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 189776951 1250 189775701 189775711
    0x150e010819170f0702130915150e04230d051c0905030a09060801050a23010e0301050a060f0506030f06060c070305010f14150a1206090f0b06090c03 65
    0x1402220034a4031040c448810441e00c280590b1603103640a00842060b01d40740d2000202400140d00003543c8010f40c00d0440c9203044482080e001081081d034152102840814000501e80400791280000c0601800d00c3c51100081d104040a0f900c075820300f032074500d10b0200500782c009021600300d02c0000c003060000c0b800701e17520328580e242c6030702d4260f8010b840041e01001d0107501050a40e2184200d000c5002000503240080b120303110907841506050001c1d21800c0168800c5120351400c0b9014808a1100700e40c0d40390856054466100038450b100050f0b07001480508002d400d5803a2004000c0079031259041042285c840108500c4004e2301d071018403100c4e00c0200c0d000d42600b18450082030483c1003003001410420600000e0f100501c1d00d0b03682d410b003510320001000d0141919031000b00c8411030000985c0b40c100840070185020009030f0800700306062005d100320b4004e60201d44002c424000207800c8100000e52081030701d1600f07005d5203442c001c0d021041e00c41c0d43c00313100c0c445c0000d5203c0300301400300c03401b035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 189778201 1250 189776951 189776953
    0x15040206161a070203040608090a02030d0e04020d0515120f07060e030f0d090918050a0201120603020909010203010603181a0406090b0f06030c0a03080708070804030b0a150e0108 78
    0x20000048440e01c00c10107080b5080ca0b44812a5001e41c4010815980a00410380c05140e0300d62812030f00901000000d4540041a00030001540c01654002030141001c0c4480c00c0454480c100103002600070b0182e040201121810071007007080d45201c86602d50003205048070010103005240820765500c0801e05034ae41c07055485054140445401150f8581d413010004046410a4100444103800e0444138406c00300454002a424850031115009610481c1001d07003040075450b000b600d5440d0b85903100100a17042c40070a13030300a160700c06290042c0000e1034010b08000340354100304000728000d40c024411040002c1c41c04280f00d00307075804912000d070203a0308416100810590300e400e0030f0222174043e10403074601e96250308030400078607103c1e041c03440b40c00d11320101940e6141000506040c4100c0701032141c8103500c1503d060002805000035112050340040e074241d207600142c1342c80c10291041e508040c2504030103004000c400034a41d04010801c9a00b5401c24000c1981d07641e6a0020f00c4d000c0c0503484607 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 189779451 1250 189778201 189778207
    0xf0c08040f0203010209062805030601051801090801090308011e082a04060806040b060118061d120307060e0a150c020a02041a04050c0c060105060a110105130515040206 74
    0x8200038402a80381e05000600051400e003540002603036562002045040300c258003105512030b20800a50b002c00740c030300b80c20041d15610700003000800d24482c40301c480c00c102503c05088240c07a4420305102d0082e096803030081041d0381580c10080d0031340400f48512807545a810304205031180301c918100040f911903500820505191211090000003007960a0030306150401001c3e80c60b80c8c881c0113a00040a40501420b55070a1a06007010700c80f100808041c188454109402d4845284220080840d940d0345445240032441b124200b000d01c41695007181d0241c2c09601c0790021a5012008210071485030070208483d9810fa40c200303449445480c03000e0301d0f10580c1c482c644021a1560132071540710003640f066905a040580c0001c00319034000e101e400d00b02e104480002e0013401e05101c2d194020401310007840c203051a07090b582e13075100e005000b424001c070008160308121034001c1c0d40703645068100c00d0081c030044c6408900c52002040011082c0d61611900e510180a0403080007003600550b000b821181c0717 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 189780701 1250 189779451 189779453
    0x80c0a0e130b1305011b02030a0c14120a080907060f08061c05100c0203040e180a0b160e0f0306070e151b0f070e06040f0209031b01030f0c0804 63
    0x50800d100925000600c4500c405000024030380b28a4280700b28585420641034980ba42041800c44e00045450746003103981d2482401c54540002c1031341c070902d109241640c402112132905440c0003001c4004500c0d50701c903502440703c907109410064101c040c4540ea4030032543d940c0180c4155610000c1c850100890010401c5550300c81c810b40c5502e511220240211181c96074078952648450110542614030303411145081414003464007031041d0300d08452004508107030034004242000c080140c168088100d5004c0045800351041c01120312094010700c0c0200030346098003221a100307a05010f828000b0f140c240c18481d4600e0080702d00900c4000250080016076244c03142518028001446650710031110104008401d0146005242c09220915140310707815140d403499150006080302000903800500b070604c00c070031105d000d0302e80c40b0600701d5010800d0500a010b400084c481c410040c0d416010304840744040c4506480b100790008000e0f60100410064000408111010251b441c000540d031940807134 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 189781951 1250 189780701 189780719
    0x10608072a06060501080c090f04090f0803010f060e041e11130603061d060303070308040602070204051e0f0702120d0605040603030809121e181507050601080c0a 71
    0x440300701c000d803060509090407607000ea82040200c11150a500d42006100c00e581c00f40c0d01d1034002003090318083c1000e82d88000100200024074209000d00e9403075911005002c40c10f082d44501c2500041c9095481d6110411104480f000f80150404181c80d113440ca82242444e11030042600350514480f00e20f40790501d0600080c00c2d100132141c2c48224240104d1488544c00c80c880f034014101c640b80040c400b458100d81203a00c13210001c052080c0c0380039004000c140d49000c01201c00e4503034107151680da1680c5910b808002405840300107900710385480c04018a190107541928803001003460040429607500c00ca028070784004a80240047e0002d24150324080f0403000506143c2628507404030f0104d446401183c112087c0c1e62060b400600791201344002c00798248240c940c0480c0b0902a00c2c82c00310002030990303a240752000000c5845800044580704031013107000d450101a40206080c5d0484002102c08440350054181078445004036000019a038200081c100c49004c070141c0003000ca01d20f40b81d051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 189783201 1250 189781951 189781967
    0xb0d0206030f040219090b030609030909010b0d14040b01060e03010e070614041a1b0c010504030206030415091101030c0914090916030f03080109020909041b0b0c0f0f0601060807 78
    0x3207070014201c18400a4095070843d45402411b4500e4001846040800401d46031078009891940203800400241c00c181d214220200e05507110301c83c00541d940d820304143c0e00105500c0d83c0c0844111181814401008808684103049071004d555074020500840c0825007202d400940748940d0707501c841010440c0798082e100b17100c00c01c8020824942400e41d03801d904440c80c0b0700444d5814114100140c090a0600350104c5940d0700c046440c010b00d071740c070b00c0da0002a15500c600d00010b403080c0340200001d410000c02419019444401c03c8090003400d01d80e181c040100b4101d40c400a000c00c0c1403562644610784a4180c07031003245c5046032040840030700ca0003881540c06e070103400590180552031064500380b88200300300004621a4460500546007800d009000c0d03141070300f005c40e01e68010460a02550b66400400386c125800604149030400f4004800c0c403001d005d42d010280c9142c010504005604020805000801c1c0342016103030400310942c544e9880d00385c02d001e00d1011841c0039010401941c8240b40e5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 189784451 1250 189783201 189783203
    0x513060f0c0815030a02010f02120d140f190b0a120507060e030313350d080a020901120e071d10050d02030316030306181d0102160b100b030f0a0b0d0206030f04 70
    0x1a503c000a1a070008000cad50302c61902442d00580b12280346403100e151400240c3d2001c2190ba100d01e2a0512060921003210081c10503440644c9030029491a50703035070000c2000170172090144411608140c509940c0310340381803061801045805000c10b00c0346c240030084812040103010403042359801c00402481007528500451074082c00d66800759202c65009407491060070120005000701961001300511003240207018810b018010300801c1e101d43d82140d000205241e40c910003090460606014514101c10760b400541c10121240d4088071400c428004d03140070380320700f01400748038544540c2441001381030800002d4269000700940c1c91750621800c400440d05229107404101940d44101c0c00d106001c606400c40010f07507480110003004407013221a00051403006000b542403040c845000441c0491505004c0e101078580c000040d50383c40b400d070b4008003401c0300149950701e80c1403101c5520344014084850000c82481d000c0c0340701062604000e4000c80c00e500406242c40e51707548038118020020040c1c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 189785701 1250 189784451 189784453
    0xc0109030b180f0717011406102d030f060e0f0907150f120e100f18030306030210020a08030402120a1203050603151003060513060f0c0815030a02010f02 67
    0x203000741d007520091207031014a007418401030084c60b052811100180c59110401411030f0701d40b034180e00e5080b003000e50761640a0811600080707031318000034054403001c0c0317584d2108002031803261341c060090351400f0011030020f0041d601041006000c80c82141298914000c99064503107120000798603002c0341d000706521203204010b807026640c0d1181c40c0080350f01c880c031500001c0713080c2141008400b0b40c843c9922b0a41c8048032400c0c030a075203810316010f454030412403141c441240c0f01c01c003085c0203610f207401010041e104d000b666440000d0609008004081701c0c001244542e0700c0c08160711990f0300c001804248075170046082851522a5800c02013103000c08001c54dc2c40d40a1040303440c0100707100d01a001441503c1d510042620325124040508084010380b10340e20010381c2c9014401011000070807072041c0ca034450f10024a03a290100c030801413131114a4010b00d41c50511441109884641d000001d142403a900d811500d5110412180404507821a4403501603010200200c099803044039085000c07203043c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 189786951 1250 189785701 189785731
    0x4110c0307050105010504050a09020d030e04020915040e010e0106050436270302120a0e0a060f030605010e0d020f041e062102100c05030909180705030c0109030b 71
    0x11055419034000403000c0e10640d544000401603407c050140950000d00c0284c10801200aa400291010429000134081182d210000308094035a941101c184000c02400c100240c00000000507007a4480e0107070544d090f0780c5030000503040c030800d84803d0681d82180c840740d04060401ca500300008107407c0d2201080c0105c4030882c0700b84040301d01c030042213800c086404903101e903c0000c1c1c52170203412400c50040000e260300f031560201c2e5010500410011640c01d42e140c0e07410204034212000e0040203942c60b0300030081d040024209070005110054070405480030300c201c0d6510b030010746002c030100c0300007500131358144100b20040c40c0c200940ca103c00c04c0140000b0300e4168460060b800030044081d81d05016a5840b0103000c080c10b10180400031400904007402c24481706e0740494102541205060240803064000a08100084c403c0e03560420000d07240d15194600706030307510700580503241c0c0b42549005080c13011540d41800f14100d5030a50040c1c6a07422064078680d0f9140030410001c0078110640b56003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 189788201 1250 189786951 189786967
    0xb060d060608030c0714030712020a050301050705030a1401050f04051902041509050a0f120503040803071109060a0522091703041a09060c0a020c030607021b030303090304050411 78
    0x54440c1c00060200ea078000c54035100004c4500e40340a40d281c01900c066115540704c180303507507800a10030098036614050008400c40910200e0444a000d400c526419400c11080181c4c1942c8080039504c44c003c0000c0600c900001c83d0111000f07001e02b8000e80c1d8214104074140303151800d10b600201d8102e20007146068401c1c0c01d01c44084103e070890b401c42d24407410312800d2900d805078003614681c0608400c41d4010000f600d40341d012840680c203807041d507210200d0041d003481401014401c0c0d800800020040e00e50300e60141c581541d0701018915903038422910603011070b000b414460588015181c0260504002074020b2a1488054110083c2002d0403a1100980030020f2880d81a400b08488520803c41c1c40e42407903d8201403a03203039144000d804034414400c11021f4003002900981010203811000c1d80e501c2d00150480c14403541c49807043e0507101d41c009100c1d8032580010503150210301080c8040714030080000f09030b224442550480c02960062005000d240340c141e02c4080e043c003064030300701d00d00001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 189789451 1250 189788201 189788213
    0x90605041b05031513050a0302062d0414030f280206270a020d0501020706140c04061202040b120411030307021f0903050607020c10031e05041502162109030b060d 71
    0x10700078044005800601c14414040007280c00c40d010141c0340c1c0c0b0006541e070716a6021014080c40200302810328520244408103d001c10310843c0c05880c41d0700fc446a85040c140317280c07964640484401c10b8102c16683ea540c17065440400c0250099a0003442c401e00c100507013500c107400ca4003031069030126010b00545480140d0b100c10a20340460f00c18000943c0310001810818111460314100c0500624208104581516500100c0d410b44441c0e05060600b0458028100020701554008141040f40040d2a00a915003543c503d40704a12418032840c1c0000c02c1070034140c5a00811100a42001444a592100801c104840c0d801d0030030314903052503170075a03030f840d8141340c14001e44070100503230003820b5101010f041c0b00040c10056941800c052241c3d28101000f610b2865002810841072030740c41001c01c0030440d14100011204018200075515144011040c1e82e01c854284821108160101a161100d900d0002e101004000039220071101914640380d02c0b0108200500465020000308025000982 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 189790701 1250 189789451 189789463
    0x608093004060c050105070c15050403050d0e011401050406051503040602090301090807030905030706050f0307030b060a02010e072103080406020c01020406030606120e0d031d01090605041b0503151305 88
    0x141a070f1800c034010707502e0601e5400c450000d028841008000041600482c42e0648807004140c016000000c05d552241011106c03070140008250a89003482812461088150000e200d120249032040115903a1035007000101e41c140e2107a05c1d0022132191410410ba21900051039207c5e020f03a0001d0308d40f85c68403000900310307914070400b2554500b01203403000505500009803400385c241500140600e40c100381002d00b4900440f0b43c5000f001c0c00020000d40054401e0300300c0c00c1601030242596446103650140a400f90625200080340380c031480d00c000030318a0094071321011508014522190b14410b545040b18606001031081c0d895940801a1a090b59424130040009240d00d65000032007a0034130b200100450300b884405004075041c809491260900444d104940c01c200c0c5c180014891041d00c1250f402c0b049040c0c0340e140d6540b030140070400740030f041d410061055210b030070b2545e402580910070407030344800c03801038903015070245402c80302d075014450f00207401c118024982c0c82410100d07076401e407400c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 189791951 1250 189790701 189790709
    0x304030521151c0f0507090f02041a0702210115050102014506060906080307030203040b161b06030b0d030c020f18011e0608093004 58
    0x60000030070900d018070030803004111140881c42512681000c00d0a401407106440e4014460019407500c0c010500c0c031080d00a07060f99000d454800c81c906103040c11a19000144520a900f5060100340030038682c1e540308640030307106c170320100300070f059100d9024103510740100e11704130b801400107010300411211046502d925801601c0020a400d071400100c5030044039164005819681400c032091f00c10204414900e14852400002d034003a40360903171417201c04401c45000c0c88414194941c1040901000d40c1100341901c2e51003109112a07943c07800070650341e00c110794014006804c00d11090100001100080004d40036800583d0803940c1e440c0c83d2615484917140021003003450400b010070009815006594450710112040e1003042e440d80c6010741011b80c01d0400a12600d120804946990b4a81c1040d910b1030110b0b0f00d2601c0e4560712802e1403601c00340c0780d05c0e00d54025035a0000004007188503160992250840714007400d240c0c800e100380480030b4641c80020030305202042507031500c038034848130143c8020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 189793201 1250 189791951 189791957
    0x301080c0319030c0f05030f0d06030203011506080415110a05030916120201050c03190908060a020708040603021303020603090706030501050a030302150703140f180105090706030b040b0303030403 86
    0x1039050403040501d800030006642100702071940a0b080032035041201d810300e05420690000345900145000e90440c070540d030660340014000b141032122918036500c40da054034800d5000b04500e0001e441c0c1c00040c0030702c5104000000e1607000004000031035030044a034120801400c0814681024080381400c4c0d00b04082c080700280c804070800014100404c07402c500080303008080300850341403d0701d00400317000b4001c2c040d051010004003050700480030401c031130007410381c3c03550501c0340092050001c0902201c0e114410700342c0708102c0420030044886c800c0318801540404168030f494038000040d0065080000e07070740300700311450ba400405601c48000861090381c002c17014000c0d1320706044e4041c3c100c88060b085507014005c03040c42400001c0c2c00240d070342840584144414090384c2c80b03d808a01400401d02000d58009440052040051080102d00d010ba0154521425850303408062542203680c00ca8491007940d10138042085080e00941c00080e04030800381010824040450210f4a10341c13044d0740c12000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 189794451 1250 189793201 189793213
    0x9080313051516230906090a09060b1b0313030611070b040b01080f03090a09020708040306090503040302272d0f10080a0305030a02160b0403030507110a0206040b0a0203090303030108 80
    0x641036004034242141c0c50343c042d19260181241d004c150140c02060034050007950002140c0302950741d1020f03100001c100f40c034014024681c640804c03150580018521800e0507030940e08030304900783c0100035101c00500344052181d00c103103107450b098090001d00c15035030341c00001001540b020401004601e441030f4000c0341c502700c10b0351500c0314142c6440468089000c5581003805204c4007a91060b4106040312100a00503031550341a080c02c03e0a031049600080000d8608aa940208100400600100c0c0e0084400420340e2103075205243c0e0450403032000240c00c2d11030350000b500075981c00e0034005030f100078014400c40418032a04401c1c83c080c810360300405002258010003807186070601d400000b411089014100c0080d82d0303a0054204d02001d4441214143c0200e181c611001c585030001c2c241d10340009560b44c8331308240c01c016000b05002d540c1c240c0001c03544050f10702c600100059140c01c1c20360187c50307589068940007010400b078000c1071020046000400042239140d80c20005103000e0000c0382c002d0b1030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 189795701 1250 189794451 189794491
    0x503120103031d091501180603150b030105030a02101b03081602010204030b0f1b0a051c020301050d111201110316030b010503060103020a0c05030f07020301050901090803130515 78
    0x422074801d840ea03540888030080c82220a600d07503642143c0c0280603031243e0003116510780f0050312247c0802035441103103d83ea01c000220aa459081110b50001d4107483c60703200741d140d0b00c01060324031090203810f406030b110045120041c14203148442240c02c25145c244924100340c100d03070328078641c154001e0340021480c00500aa001e00e0081420100c00f41303000031032a1034515034481000c46d1004020f0750010440400180111416082907502405d100c5526503640311031800c0500941c210300c0245c5030b06005015641003c544901c00c0382d068030030040c0341143c41c01150f69092600c0008100164000340c3c0041c104e021a04240644202d0341d01d000707107031610303031500b0040901c3c04000c18001c8420581041180312481e6040412280c0101c001e20307026903200b4815002350703108032401c7c0000f800c610001502d1b1280e085041c019100c0b00e4400c5000b0f11854036032079085400d99101a40240400c6403c0000c42c0d60180d000f810000305500c94001c2c0ca83c00e41054090459040084440048203c92109465 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 189796951 1250 189795701 189795707
    0x4020d0e010f15050d08092205090d1d190305010905100203010f122301020315060f03010501030504150f09021305070906111504060e060606070f0605060607050312010303 75
    0x1102c0950100308007282d4040004000b2840c03030b11960380a45030790000b100921120404484d480701014154200e288107400008601c1104001260682c5203400042180c031080411400100c106559603801c20308501400d440850000710005940034000c54000000b641c084003556005600400002842c401e142c00c015080c00400e020790524548100010302250089a0411003611446074226011540e945080110451013111401000800303e40440550105400840c498000900b500300310b400f03840140300060180000f468803c20080c00140643d5101c1e5122990060090000e58503650501d1801c0341100c41c001784403000e26488070007410035800d01190942c00b0105481e01040249080f80008062000c140a850300300441e601d00300f4840c503010480414890240101e44801c1d080c9454801c0c0100011603034401d0030300501000a185140c000300f13448503150040030381012124150b9548000307020082800b94040c2081c0070140200300b0070006800d640e4607020a41802e035040d07080c05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 189798201 1250 189796951 189796961
    0x2d1808010905060915011805040f05030c06160207060503012102060c07031a0106080f180f03120a0b06030703020a051303030c15051308090a15020604030e010e0117060102010b04020d0e01 82
    0x4c5c1d082c1c1c140103001040040d89001400501d0005210000303032607259440d14044090b6005800381c4107100103d10210b41e40340c04544c96000f102c02c06681041c91420f4507041c0e844000c5403040d034010440500040010880b405c409a1125402d0380e1050020b80c0954002001038100802c01c0b03019500c40003003071003001101c0008462801c1e1803031401c0d15a62400e20300901820005110845c2d4940000104254681e1103982c0c0700302001100c02e54006036102c60000e43c0c2da40014207031070300c10603080010403008022441034800042c03019041300e2440e500d044003600a90300508400003044804c02034000092401c6480c0d001452190f511202200910308000552420701e511a40c5107a180206100d01c01d14211004840300b54080c0c10a61a0880038000032421201603112a00411110054000c440d0b03010030003901c00c2c0d1190b2110700800642000456210022144603408500c040307140d4812000340340f86040d4042d41c144008144420090041000d0780c1001503a0752100391a154055034092080c060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 189799451 1250 189798201 189798223
    0x8130b090715020633060a03060801110901080a0504050706050c03040e011202210d11010b030102030403080702190b010302090a0f0c21050f0a021c021303032d18080109050609 77
    0xd41c1c4001d0203229007610034500f10f05911b1140e1400039001740030a00941050005210f030381c00800041010740b415851035071120310b506001500090000e00307e40c88610606007d160010300610030a0700304034060b40c02d039004400441d502d11043c030002070050100c480460103001050b410b006810600d1051009603401c003001c0d22100b403507407808401d94110020b00410004a41d10b41a0300d44082d016146004002211009030154000410041130540106d50b85d80545080c0d821911880b541d035000484411032454018900da00c04401000940b80c103c884507000303020008000349401003100310b10708646250101300041020006100a003d242041c003803c2d0842c03a450602491910040307200c000000101446030140e07000ca80d0a5024064000c152000d110300e00d0110350710209080600410501840110f0008003882003e480141060000300348100d0501404900d03401202c00603140e00020310302100c81d07503070b0b50480000c03101000d010315030200b03000300080c0c4024248070109508010030761007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 189800701 1250 189799451 189799501
    0x120d15060809101d010207061d0a0312051e091e03041404180506010906140f100320130e010905091c05041205060f0708130b0907150206 60
    0x70050007250110348410b9503e2151400651078110b1903540706918500d4500c40d40e40c0d03101280c00c404000096200401045036501080c034074114410003a035035805405402000108080340c1e810800c0b0064216a4001803c1c0ca2684092000c0c14040407180004441c0b000d8242d10070a04040d681841c000081400002c0d10040c604e86030501d801c60880000c1050014003070340c0c3d24141c01800452a88242025982c40000da81c0c1d0365940762150304c040d2480380500e0110008071031002c01a8901800b66000c3c4c40340107044000301d441458410307001841441c644003031140c180102404003001241c014581da050f040001c1040d10b05101c40f006c4820750580040c0b403124541001d0140c15440010f0000c00b21210b01740e03202c005120060215440e000c3d50780180e0040a0b800402d6080020200d40b4600c10500720154000c59a00d00b41d048030307805001da0b04a0381081c10550040d000c1218002c04d198003803403103000c9550441d92000c00c1a0b03420819000030300141c021005004410001c00b41c007801d0b03000e4000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 189801951 1250 189800701 189800717
    0xa0b01110303010602120708040b22080c0f01030f1103130b0604151206060e0a1406010206040b0109090507180204031a04050607030203060118080f0d090b070305030405120d1506 78
    0x13006581d80c0c03210a0040ca040001055940070000720700d0484025008070319019440c1c0e40c2e040c50340c81032000718002e501d00f0740b0710807080803038001e200041c12034160b4402842e0403d004441c800550080c05901d20107485079481e4505000780202c2d4000035406850406885c0e090b80c002402d0803c150035019169501c80c0c0d04003140700366503000c2c031011041501d503000d400720060055407611a000341030651100401e680240c0420280040c6d90740320050515910080d120595205001261104e00c01c070f4000385803802140040c030415440e54040d800b8a44a50125940319844130864068021003803070185040d500002c06108100c030103002200004601181e5202ba800c0540da10354403081c00905030802c02d6404800694240e00c100300a010f5400140d00c80340401d907c8488407034031003491300801c1c3ca040c402c1c42401c0c00c50320311801001d400c60f1044001c1904040d0b5540d4129000d42c00036100380ca4034400d440103800080400b100920500c80020340019841003812900c88405041c3d9103c0c2041c04014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 189803201 1250 189801951 189801959
    0xe090c041d13080c07150203040f080d0c06020d1401140f12030d0203040f08070c0f121104050702012003010602010c0c02102d08063d03020706050a0b0111030301 71
    0x41500c0b50307029984800c03100e8803945180b049a14001041c0c0c003007100b803183c00ba0b0800c2d18a8002c402801515100204001e0701501c55040d0b42e600d100103642c00001641048640001c200903502810342d2182a84001c02c032252820390a001c90300081e0003825043c44025001e00440c0303028400410091800e031804070349900d10380710013030f01e80c083d002114803c16000000207042050b42908c4088080c1d22000c01900d41069082400000f502e5014016480782120300c0030075103890740c4421074442c0358803a40b02d244a003000020311000c1c0202030511001e66407600b03004811500d00360f00342a00c43c54120740d16626076140110090039190065151424022214601409a15141052040042c880c180000f00d010507891030802c2d914101000d21454009030f0312031038032683c8100c1d401d0250000703d840d0140d9504441c80d40903404c01c00e07040180740c940c040f80b40b2160141d03440035071100c807051030a00604124064032094240d54007250318070a440d944818094040da000589038103150140e034025801c540c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 189804451 1250 189803201 189803221
    0x1002060712020c010615020a05010501060e031908160318050a050a030210121509050c0306010f082505030618010302150d0b030f0607090816060c030e090c041d 70
    0x746030050340d007900080e4266020f202504940020a45046111a06030710b900000b51a040358074002ca4140d4244000014003500c107001c04010035030001c02134448902590b01842d01c05030442c0084074000014002c00c5050780740c1d4602c0050850190303c42d1810340180241407060451103802c55481000030754410311a5803121f14032081560382c1500c074503a85401075a8141c0d80c0c079010001560300385080221444140200c1e40c000412184541000c2c1b0958070b40200d800c03040d00084440a00042c40b40490b5484280f1403481f443d00519040b0001101009550410509002000b100800319200009124080c245003002400b49006800d0140040d411640003d202003c1078441c0901752001203132240c0f6081617030f400401d21800080072981469a003070700650712032908403801404942c2c085800111400d02061000b0400416880011018140002a100c040e041c00d000c1d404c1112504241c160b5845500d1030728001c0340303424001600c0707034030f407204180d80001c4600c02110124450010700c41c0b0008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 189805701 1250 189804451 189804467
    0x120c0f03040f020f030d0e040b01020c090f04030c05071203080703022805040f180c0206070e011407020612010810020c0c0d03050c0303040602030a0c08090d110f010c0e10020607 78
    0x782c45100050302003814000a0760b220703802d0307001e41d07450b00501484c4501d1a070400c0e0800684042614180721031020720006a031100d2001c54110b8201c200c400009421088034502e51354000d1107820180d011182d26254145811007a03004000d1043c15003032001e043c542c00a1456610540e0ba00c0c05526110240c81c0107411140484503418031506480420381141d80540142d40140c44019203d0183c01d03a988000d948280d0035441070a4018544181400005e10102c0e144c3e1140c0b6054a403501070b045010011190100070000246501d40d0030f206810059407100020490381303088240e420425410b041c54503044c42e69200c0840d80382481007060a203074030004200d9421405007118501e141c2c0301e45040c19a107620804400c2840c031301000040104000843c0e0203180501c2c2107800403c0103151219095074480070a888041d081d40c0804001c00b0114480c03140c43d684a04624103071040c26440c3e2844030300b92000c545000010941d540e0030007a06003000c0600902d9005140f00916041c01c2000c80034143c52 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 189806951 1250 189805701 189805703
    0x50705100e0409050715030b0f0427170a0e01020d0e0d1b03060216030206100e0105131415090c0f040e0901020c0319081b0307050d0b03070b120c0f0304 67
    0x5444001031010b0007001d04c41d03007000b03160006030701c492071050f49001401448d403140140d10422001403400201e003401c1c0710310030001c0303000c03988038420902041002c40190440c4034126180040c0e40850003544a0110280240315129100c64241005e9a0006420002100ba1940410010320384035070065440307694001c0103941051a800018280081c08141c1b0803040c1c10250488d400018030341076001107104180c9485010350701b654055100e1043d6100100c9480c8500b41e205491040140040d2802e24030303d414201e0460b90001c0c014030501c2100b05891400c8620600c98a903012940c1402d040402d6120307408041070050514080c00c641d40c000c00d600581c05402c0b4a0006000058800d8038250304603100400b0134002c50752600720400d070303801080751044900c100007181c410109002000c00000f45810a0b64100014110742e203c040807185a040114406480e6481d08600310503030314140a0000600b003000c860650b507910a2080d250b6444015100d0000070000700080c143e0320404000f540e40003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 189808201 1250 189806951 189806959
    0xb0603120f0705010e0601150929090d0b04060c030c0519030506120105040c090b030a0302070b0307030b06040b0c0f03070f02060319050f090705030c13110f0f07050705100e 76
    0x2403052070074820300510b5030640c00c6249104400020802c1201c02d03407a404072300d400e651511351603a241d620110841107000b400d0106480113050140c1b60501c0d010180150b92401707400c1107a41101503c0b2010005001e42d02501c1060740e501600f05269458010700c0c155980506001e443c103006078003031850700000c006030101050f071790700c000c01c0c0300d96a00f5440301c401a000d04000d01c802c2c00c203400c0c004e071405100e00c5401038440c54a4200c84440c140070814040b0700e9016000380600a00e094291607840d48018214030070181d903401d441043d50380307501c0a04045d00e03252603003540322005a60290719050000d0b4128006074014041d01001441c40070070a001c01c1da054955907100c3d107410340f44504090201040e28000c5003407604200303078085400c9200b8421641c5104496965640b002071588032042550000d40120040810b21014503903034020041020001c0d40a07031400340030088452071a000000341d1200c0050008800040c0001081060b02411040720011078411100714007a016665155096001e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 189809451 1250 189808201 189808207
    0x309020f12010b0607030f0306140310050601030f06060c1505040b0a09060209180405070902030c120402030a0804030821100314010608011e05100e070c0c09020706090b0603120f 78
    0x71200203410450250b10041c00c81c40e02c038055840c005d44014103014140780003d107001c0700000c40c28060128800813240280150034100212140000507000041440781030549075450701300b140929201c0d50740140015500c02d45a00304520304010440d0504201c04040b030305000c140800304800a10054000e8450f180000782900103261200c00ba001c0c00d0951a80041c0f207524513000001081d1074540b2492050307055540180e01e1b562510220f000607206203000c1c2d481801086000703042d10600d241c019000400301c80400200b030303071800740307690194100301c0e5200404180e600500110301c41019000c841c04ca048005d61604412101c1585064480600841c9254548130365140c1c084d0300440180c0140e5000f404082030001015005480c03d102403020145003100064510722240c0101c0265504000310041a850b4244110342104c55064250b40401c1900d6000440b103c05100900d18070707203e00804158130301030303040003c480c5d8070040000c0c0c06900070f100b104400e042844102e40d00e05600070b425a031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 189810701 1250 189809451 189809479
    0x110307030e100c0c1d180615120105090c1306031214130303031b0c0f110a2d06020c01080c0309070f2409080a020103050a021909150309020f 62
    0x1080700302d03404084c0c0018440c0502040d0601c002c00e0030300e003040c2c030420002a241c8a4007842d020f000400c112907015a0051004620350041903002c00104100040c004003840d142c40b4002c0742120030640307440a02d58001111b03c1064100141d004d09100070440c000c122581c03868862100e451014501ca00801c604002011a40e00281041e11b24102d4001d540040641d01c2c0c0c030740038000300b031200c0a0740030192240203e083d41601c106050301e0820f40c088448081c2c810240e5554071ba0004141c141c81e0b00c4141140049455407018803052003824800c802d01280000168001c00c0c0c1150b150003032011501b00888600060360040c4800b50044503080d6030329925070314085000e0600741940c2100720100c4d031a80d00000c0d800e030301c04200903040400c0040440802c0c800801600d05500c0d602c03a20b1f101c1e402c440f0100c8050740c000d501595200500a4000d41f616030b042d102c4840c0d11400d4070050300860001681802180d616001078003443c400ba0404002d920556000100002c1003c0701451141620751900c42c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 189811951 1250 189810701 189810707
    0x30b0a09032006011e0b0703020604030810031502030402120628020f1804020903070303120e0c010c03030b0f09040f03020d0302090d23030f04031a0403080402040b03010b0306070f110307030e10 85
    0x40001e1002215094a44841e2318000352520400d5070190002003145001c81c048200102d150740889501c821a2680c2d000da0b000104e001e500011b02c166488022080c1e03407000500c041c81028418603150300c41002c00880403980f8908034420100940d5110710500003580b0061500c01100e10403041e07400500c441c070300d0361030004019102d2040c01d5a094010810300104058100c12200d6400103110f40601401030004001030780c90b4800c0c40c4440c00a1415854140400e01035400b45801110140403961000011070200350040c1c03085e203003211840000001c61081c0740c0d0502621241700303058034040d46070100880010b440010200004ce0140501009584501980f403100b041035484000980340c64071908200d10303203250040e20040c6c45400c030a11185000c800070303840c01ea100355490344801d103240d121a02400010034440f0b44e295051f66035400505015078040003218861002607403240700b11420014010400040981207030807540c0f0034000b440000790001c114048110301a1101d03a00913105a10803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 189813201 1250 189811951 189812009
    0xe0606090d0c05130b0306090c090402011812110f01020a03140f0c06010e010503070905101814090d030c0908031e120103060207110904030e040c020304030b0a0903200601 75
    0xa59401584d03482d0800e403242107a04070100711407084003900c8055440c034407960b0b11611404004c9030b00c4001130000a00540c041e002e00c8040501319000d0403000c64379108003c03502041814141d408942410246000b4600b8003601d0401140a00c0500751a10072a40c001c0c00c136202190003407845640202d14165080c490b42d0503120500b13250002c503800c9503500e41c4954010f0100780035460190284050204100c036a900840d0302488440c29511492403412000042902d02c007048001255120324640d04451500d0300e065003c0c0720a900a0040c0b014000380c0034089030404603034902400840c0342c0c02c00240e40080140c40002e19055900450040300b08442091403249038151810050600004024810281d0103004c4d210b1142d810f039645130030403600704200c8034011140100050f1608802c03280c28100750304082c1c1700c06c00c0e0b4011a424151260754260007543c1c02c50761609020707658611541455484044206203203880405041720200c142c52094407100c05000c0c2c144260b0f030845c00885100e50324609 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 189814451 1250 189813201 189813209
    0x1140d0809010318060501063b130e0d2307080a05160308040312060e0415020f0d0917040608070806010c14060712060b0706180c080609070e0606090d0c 67
    0xf9410f030400061804000620b82030240d031000a49903600b00500c039030200381101c02a4408517012449009c2c0e0510b5004d891101c4603182d41041e480e0a40096132111b50062603409401403024008500720844010900c04040000b1140440c4042c035200001c10b50f0f9084076401c54102810303d5070340e584008203588510604c0584041642c900801c030003890790005049000b00d219640c3c029038a00c3c0a500c0318250351641c010080407921b400085000107480780e44800e1223001c0c0c2ca0015003071200103a02e42d005900300080e80d511564544440c0001c11040d800ccc01c0083d43d01b0981014105420301400a103914001089001071204031400308100703030b008078640b40c2e110b503124880841c001840380b008c5071100000c1c0c4041010540300c00e283ca960070140c1c085c6c42e00340c40700445004c1c10b010f4947c1b81d4602420040340420034034071542040030301049c40a00c65002805852001301458104450304a10304006039000c20101c40d080d10501c203ea5031490f0855441e0f01080300c40760101210b40c01d000c50301e9511680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 189815701 1250 189814451 189814481
    0x40605160c0602030d050606090a170f030a1115010e0f040606050a06030b030c0901081015080f0a0507090908031501030e0a060e070b0906121018020301030b01140d08090103 76
    0x1c00003241e6078000028240d070750310804180540e40b030b0307101031100c280200040c0b141c2c401c1690b94280049001e2040760465810b4036400c0314142c40391142618150f40c0000c05a00008400390449450b60400304031504c4010041d6141d08043d600d01807802454442c050061030702d41285402103001e003c0c96801c04805850000c00360441c03607942e800c0180003041c0207074500c3e019000d512608041c0707140a01c402412030b18410041d01c510030165414800070150030f030358800c40c2482c1070008903190b40c08200400d0429a20001041b02e002c0c01c0c00d00070f240c071f04140c0c0b1007101e90341070420302c44c00100c554050b6600807030361510010103000000b0058002e44110140d0100d1403068403815070600c00c00b81c101f0300c207400b40401036a82903900d07145c002c05184074008146805c10000c11020a04080c0a03600d00e50002c6000e6985a0460700c03110801da0113888800d100600c01c1d0040b0041c4144089285407500514105000296000145010880c00080c192001c1c000d000040750cc6c0c107060340203400824545108036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 189816951 1250 189815701 189815723
    0x10020f120a140a020a02061803040801110d1b0f0e010306050303030411090601020304030b0f1b0d05090d091809030207051801090c1b060b030c06070b070f090b04060516 74
    0x41d4070341e4000d002c15101418001480c0000c5081c40765a40f00715220029980d01601075076030b030049200241000f4140341c081510040100040c845428444e021508500b0b801c0150ba44d22032642d82e905403044d4042c50a103840300401600c02480e0084500d58802c191030804021030518000140d0090110394081c03509408004108000c21000c00341d440b8021104450b194010f40795007004907034074002c50000514103180306020881203104038041590103441c0c01400c0300c0e800000d031840304487d0851461004401d8884050010040b004d22400f00e281d48140303000b00026261250382c25914188410b0659101e688407035107000d141c0f003885028081e003005411100141140c07040007800910074401c1e043c0091600120040e1a072040d5003150049a103d1440040d03020305480c0d1b000180140006c895041c0b003102240302c0c2ea525100098011140030725a1840381e46881c0c400982030000c0c0d0f410913010480e03d6041480700525420543d8141c9101d403800d1600d50701545c090340300b141701c03490000c1c10a40440f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 189818201 1250 189816951 189816961
    0x310f0803070515011202060702060f0c150108010c05040512010609060f050102192112050a050f070e03030d0e03091e0a060c05070312050d0615090e01030510020f12 72
    0x4101480c40780044885584860f14801481c1d02d003170081d80c440983c3c145d0308034003600c0d011010786a0103000a241c5498403824950340607007513201c1c029001e0780d500114945c500c9a216101202e00401e520320080c40781d015040d400411911450152910484c000c2c134114880c90760941c405009440301050400081d5120306060002200621405d4018420050130484e109183c0106240503580044061203400041000300342140080e0700341c03410801041c500119221312400f40350301501841c500041d0380d04150380309401c2a61300400540038806903034000b0a003503c001048a405c00e41c03c07070300001c2c00d40c009100c1d90308622903007002c00c0c3e202c003082c0c90a1071020030550004520910403144444240e5440c0c0c4142e801e0344001d10060242d40080320100045480d1402100001a8514060703250982c000094402c0b180c59400c005442030100a59403070042d001a4540058010303105182c40b42e40c9140d46840d0f4078104019a42e06171900410131000310f4004405036840980c90090303101240c0382c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 189819451 1250 189818201 189818203
    0x2031e040906081603020609060f03011d2d06030a020306100906170d0c0314030a15170703121b3813111c0b0903310f08 53
    0xa40034071116035281100c0000d451500090004030400341007a0ba15580303181d60204000c540010301c0c00d640040007000081c54203140781d00118080c024020441c049c0c980a00004002c920000745014042d0804031038004020f00d525074646100c080c44000ea140c580d6802c0301007400c3c00d071884802501071213400144000e101c62142003100780c0740b80040801403240d940c01b04080102c4003022074040f54202c0c2c3d80c061000c0784200f1950b10150b001e410000c8200c00450307010401c540c01250400402550358100401652403501c03900c00070081c6003080010220031001090310340b9087e02c00280003180340c20b4061442d5000340c0700040500842000c2c10020305a50030320201c00b040c55191101005100406030042c0c00040304e00d407002081480d10078502d541d809080712407060381c50000340d50303604401d504000c503aa02d0005a2201d01e000348888504800d00385058554000060034001d070384d4005010045402c40303c0000700c200d40c52040148140000d0000e003148600e07449401101c0148042c520104422030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 189820701 1250 189819451 189819457
    0x60c07081506030607140a030209060313060b0f150304050f060903030108060c03011508060102010e030c010b031605031203070c020915031c05031807090504030c031205010e061002031e 81
    0x4807401c40364819603a100101500c0f404100d0b03d030400f0139900300d1211002c0c41c00c80b02408460643c0d0400520b4020030b0030000300309810486100010002032240d070410031030070380075143c00b030101524050b400c01c80100005041c5105862880580c41010000405001e410030518212091050558240c4e0905504a585a900034001c8506600c262130129000d9904401100c0c100d41d9400c0b10051005443c000481d02101c004c1c140c07134115900e03880c0848544c04240001c24114110500008109801c13009042c142007181940e00b00740c00c219241040551008100c864060000d80f06083e981d554503030b0280ca41040d820006500400002e08010308005944492610064118105e45410440f0080034902c008001000b800149051012524003130326610600d036208184403da64101d0788600584080325030445040d0000382c3e08107120010305810048040784070f40d07000801d0000e0760400005503a911006454580604101c68130296a980300b402580c91400a008802648039202011441e16030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 189821951 1250 189820701 189820723
    0x5040c080f0c07020d0b0405012d1a030d0c020102100906090201111603060c02030c0a060203150d11010c03050405030d1205060f01170406021902030717040608040b06060c0708 77
    0x309a01c00403450031054074040d559190b078004c0215684d1251641c6090a01001510894840d92a8000410794084405102d035001700501c4190180b1078a291601d41640d0368211400000c1d01804040c4e0707155100442c02c0d40d40780404ac1004c48400c41c5510040745401e000c41b15602c6501e00c0c001604080241c0740c1c006c0140c0d02d000742d80300398481c1d8000010302d84030200322041050f44840210100300041058000b12070f122010300640c2e041c1413000811a00742155840d0803245130350300008002020340c4000080380020340503602603441c900c1c20341c0c440c0f2100d404000310a052001c0340c064075040512500c100d4019000103816203050080000e00034161078403407515042c1d0241000001680ca090949413810850016501d042c0603501d2198108100704002d0401c2e02c1850f0200f14282a4a03800c0c4110b04800450b50b000356a980c16030b052130340700c1c1055001d4400e10800100001c1000340c4e400485c0607001038000404000548589000130030605c6181c1100705240a1900d002903013402c003003981c074030300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 189823201 1250 189821951 189821971
    0x30e03010c03050c070b04110315011a0406020d120f0f09030f0305062b0206070c06020601090515040c020a02090109060509063c03070e090f0c150a02010605040c08 72
    0x401d901c10098083e100100c41c1d102c40c090051050300d001c00d004c25001900540103410050401d5101c9004c02d003031000c030241942402c9080001001903580d2104111030010780c4c0c4010300d0506007080402519140010669400c00c40303010654940622142c0c00020120001e40041014503800004007000c2d01c480001a40402c1158202a14290185c040e031442500300174074406140d40c803c44402d010f01d00c64140300b240803040441041c0143c071000000c2107161b00070449a41254034095000303180c0030058105410041c100000d2100f40d80c0d000602020000044a01058582941004034900562241d002c0d6100c3c40392000007503c18019805441603803000e450007401945d4001c02d010402c0f50849401038414441040c0b55440400ba5194107009400002449295000707000001e02e0001c1d03e0b04500108070300d1006014980000b08405010601003002603c0c81c10400000104044080507001400400000d8418407943c0300f1752041001e410f009108021034155203400030010b01c0300711303024028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 189824451 1250 189823201 189823211
    0x1006080c090a0b101d0111030a0f0201061a2809030b04050c030a03030615140d0b12010c0203091e010806210105010e0709060203130b070807020607050f0d111002030403050f0403030e0301 82
    0x5c9035204400180401800c1002103241c5120740f082129600100f8032128115540da00c1c0102d0842095141044194403480c40107032030301018980c090296800b41d9880c0c148603445406141160381140319441140e411840c180a180e50300c0c1021401c1c64031740d501c22907060150424100402d60140e00950554203000034402c501c4102a82c2603a10400d028406030881106114440c511310b040e400c5100c5102014022421040761200340c2ca003525030000d04c0300c002d07800c041400b40481c10881d1115040c44052600c4007000205030001030003540300504141c4c0605810784460300011382c03000c01c1e0280008114000c0010f5a0740705545103c1c054127850203800140d00302d000164003440007060359040c0710400e800d480c1c0300b031610703c0303104160f4800c100494141c9401e200c406e01680c0c0f80405418418003800c041c015551840034202d0400b0321608042041c030100c040030039100b43d80000e62a1100e07400d00401a40d81e11281415070b5203000b805400803c41e00001400b04c2015801501502c121005400a0203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 189825701 1250 189824451 189824507
    0x803340219080409050a0e0a0303021c0203060d0201080403030e1e0d09080d11011509020d1407050d110d0c09030b01090203010b030628060c051006080c090a0b10 71
    0x14040780004040d00e406000e00c0700b070000c00c0f8164070840d041420034500240e8150480e06240c01e042074030748240e01003540850740c0c5070f09014220300414030809580045107540b80501c0058410003d10340702a040280520002e400c160199201503100c452020449603407042c401010051104040740c800c1c0580103060207002e41074020107035107080d1071010000d00802040c0341001c0326402d0804201e085151f4035804010088032405200c20040d11101d200980d9501440c0c102d40140d403418425900401408020440300a5011042c1d0b03000c403986110100d12610205104c0949000c1e0b82a0400c81528118802d0300142c1c029084000b140d1042840d010584c0e0f0f1348040c0c008901003481a0418001c007000001c0b001d150190310000058007843e00c442d081c440c00c50030f000c0110b0003a00540c0102d41040003040a01070100002c2d20000c110030000d02c84141450f00c0e2688406d100d00103180900d4030440407035054080c9400c01c2820801c0a044040c0d44070b02d61000400c90a600001101007006404c4954 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 189826951 1250 189825701 189825733
    0x30901021e06130c050d03090e07140306040b0607050708060117030406020d0c230d110f070905190504060504020a050117010b0c031b010b280308033402 67
    0x40036440031100a04040ea840402d0501e48080e2030380c0460301c1490070480420903540d04c101446d041402552203c070328a017001031855030317144040e048409104a240205410900b4001201e900c81026100414444150b40c04211a4041d00710024114011000085070340640012074070304071802c1800103101001c84424841e1288514011000140c010814000000b80207000c0750388500d120b503008000d80d40c451800702c070f07080c40d450030005259040362007111001d560143d00e41c8171143c60400688484940300920b07690301c041038401c0048035915080080c0724414281e441500d0900500c4050000d49450f1500e0002000d0488040f40b05a03207000d0086582d500c90388410100c03e15014094110f642002603040682d04008141000c2c0c0c03004010b802280030300201c403011141c1500d0000704000c81003000700040c8100300e0400c82021240d0400c0e0404411000d0600821650001c40156680d100c44204400740e42c2000080800e41c81c2082a81400184070744081e1070404450307017a1f8004040d064844 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 189828201 1250 189826951 189826993
    0x70308071b12060515090f01030c080708031b0a050307050d1d030606131b0e1f1b080906040b030a050106030501060e06031e0c070521040b0703140c03090102 69
    0x7290707142c00c00610320300028815600642d081102103600002c01c00e030039000611b21030402c8804001d0380000e00c0040040249451001e03001d488103401070702001d03060481d00c541e00d0050f201c5105210b2400c840721050640e080c015101610340100549039262801c3c01d14036600c4942203003810009248010700c030880544942c01760301000d00180907195130340707a00b4104540c4c80800ca030705000aa6682c565010710b0748020240701110360b0340b500e602d40306a03061402c00c9205400d0204500d035045401c00c110121651014a031040050000c2e1025001546800c1240c04d40c05014191504404002004903010704010040c601c00da1020001303102503a00d0b10421025035400b8401d55003c500300112021035440c0050195034003035030a0000d43e19008240c0c0c90000b41410582c1c4510096400055400501609201421a4601d0074055125080e00401143d189128910800b0741360903003c01c1034001c152154010b03100042a0400c596203e4030000c01a80d1203a001019650140c42041110100e581c02c5045c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 189829451 1250 189828201 189828209
    0x7290420040c090306021e0c07090b040504050604140102040315050a0b03070303020c010518040912020f070614030411040504060e010b0f060409050601120e06040b0705070b04061d070308071b 84
    0xa440d800f516654610010b504920301240c101c481c2c4602007130040b031450000e001c010044030b0082152600d040d00b40001c8030039124015018500303001c01c00000c2a000118030b50080e61001c0c1c03078000d0b20041e8122074024080d6401c01080d1100e2043c203891901e10f182c00407030089059003410021001c0850805a07a00505d1100801603000b80b0070003010756001d403010380b402d8902401c01c40110455035001504072081040c0440e5401543c9100d5090309a0400840b4880c4a0140c003c24046080c03560141c5954507800880c2904000000090204003200041500103200a030081c031043c20f00f0314001d005000302d00e5103801c80e0b41c41c0804032600780c50080f01500e4040c10143c20b00740361505000c0d0b400050000109a9414001d80070b580c5080d68003140300c3d88207000d1960f0b01400e180e040500d00444401000780c8000100401400030b44045003d030319050760007562061000812408901d030341040e2150052080070715000300880081400682401041c41c01e101c0e0204c10300c5074512100148494040b030007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 189830701 1250 189829451 189829457
    0x30c0e0306071e111f11070c05060f0409050f180d0e0d0c080601030615060c030e04090204060510090806010801060312030b0d080c010218010e0607290420040c 70
    0x41c00c401030702611020518031080c3e04c3c025481035607494030300e4a407040407040d20380901800d5002d402d0301c0700c440c860b03072804d44c9030002498035021442d1034030201030b91940213040c4039040000d0347c00b014100300c408a6005000008090095103400c4064440008003260f1000f0600207000c0401c01020001c6001e50071440b191f01c0c1c01c42542c0044003030088000b1064412120b81d081c015000c1485c0404011050007144581c0e004030b22181403c0110943c40b4031503100c8002d200f1905034040c0003d03000115003102110a6a00050101d11800002c0181c071103644030b0b98008589030342007a901135010001c001580e0801007180c0017640c0c1d48903100c2c00c070b603450b10010b40301c8411603402c01440c81c460b82107400d42c0c0400a1101c407880500d0b4030340c0c000a0b40041c4030002281e6000400c016020003412418014003400d007000050760580102103080c40c450420020034a070112400488040d000583c294070400040e803908001d46002d00d8003909800c4074141b00e80300e942d58520141d1440c030b414010314086400d555 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 189831951 1250 189830701 189830717
    0x1080d05030405071d0420330a021e0a0305370e01020d0201200a030e1b0306010b0301060903300504050112270203120307030c0e030607 60
    0x62400c44498102400c100d4982c041c61100094400700f5803504103032520100b030142031508161405e00b800180303412202244c0007079410b0350a41c603500d0102030841d1081c0803c0003071f01c103075403c800e08000c80f000702c0b6804145003010a500380f00307a81c0002d4088022119100103000308540901d03940d60b810351000000d0000e201080001140200012017501d120b01214100410018009601d04a200d01c40740981c0001c04115400c91950317030402000c42c509402d80002c00c00c420111202c5000c40041c410807000e0400005030010046101307030b100c0240c4503400000d40e500c6100300311055101c0e01c08058160300c02e200c0c0d03500104a5600c8801201c0c1242c0050b00c3d460780e0b440c0b86035150300402c0681e1404a0508203810300c152402c540c034100240b0317080070946d2103503551403e100001d0119000305460520592600c0c84035601c02c1c2210044002201c9440d0300c8661201c0c952001a18101501140801080c004030620a41d1a055005005800040d84422a0414501040c1550303030700c081302e400b40055500c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 189833201 1250 189831951 189831973
    0x408060105012619050f060102060a0c05130e01030b1b19030603050610030b09030c3d0f140403020c090405030c120408010b03030f0a030209040b10080403170108 71
    0x1401c4044100103e40c690710100b045030034200904240c103c1d107a031564683d14804914007611481803544c41022848103004600303210000039903400c4000d04c180c00081d600c600342c880407030040042c0c52580c84045041007416071105003845610100384000c84a141016011604d00d14000baa0076240014422203170b41444051035207030110813507000c02d0005155440740084003082080c07014a2040c03000c921002600c0d459468a0b010149009201a0041d0004d201c1c4a0103200041400f1040700c1c043c1005002456071010503609103603101848030082c02c4803254400c210344070340d004500c08203da0041000306054540c8200407150f4229030050042e007003c2d61890940c501400c209802c107010b1422207041000c200e901900c0c009050f0400d0842210104080001079000d0080080c40d036010b8002c0c3d0b080c0b0042d11260116070180b48403000a06401080c0024107880e50760101814034002040030019038071250002e42848001d40e000d6001030031004480c6500c801d4080e0b1107040f11580c070004c000007004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 189834451 1250 189833201 189833207
    0x4030f0804020409020405010e040201020d02010b1c0804050a080d0207050303091f09080f0a021c030f0518150702041a0f01120207080a18060206011805070e0907020304061103040806010501 83
    0x7070040380e0065944445a0240c0c603680f080c02d01130201400d05101c181000d00001e803400b80c1110a40e011a0b0410312113001e103484038a01e0000182c0c80e02c0040c08000c1e610301e07004590b4000c0b83c101c20b40054a2510010380108001100e040f070524030307000d40d281c0a4841050640380d02c1003074441600106405410340684113901f18001e8418200d01c0c10141581d12840c01c181411a1400a0089a40440c401c1015031520760710f003d03500105ca000321440b901e483c0d43c02800240300a404101030003008103445020515036503241e00a80002440070b200c0d1515002980fa55401407507080c2d000d40c0c50040c1003a04041d0403d55400c91010040100c0030401e15032004403580b160101d0385500c039039000e101481c0000d01c204094821a2129103c1641c0d16035a220b400c2000101503000c5400c650100004002c1c1006207a2003ca41042d000004100755075481d1040d1000201c0f481d4541d00000c0100c10002d0003507010010300143c502903507440032495503030403910380c2d0f0740241d00450303100d5001380004200942c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 189835701 1250 189834451 189834467
    0x90907050708071b0503010c0201050405060408160f05031c0207020109030803060d0213050f0601050a050406080c19020610050a1a07030e09100503011407170604060801060603060512010504030f 85
    0x1c45800400c0c54210b403583c54030340001c0c3c1100e03410320040000d44c041c001380c070342030003640082440d41c8001c200030b20741034459136a42d01014101070844100001d09102d400040903200d183d060308840b60301195130992800c90f642e03500100c03c4006981c000f4240c0c03800390b0000d00840d144150146e407000c41c0c0c2821a182e04405500c00351280f90301503041200d00b001a1600c2007094404517699034002020711742102c20b0b480814000340b07a581040002c2041d552029003081c1030390180c2c0c403140381440e00303551014013450061003580d00c072824411600780b0808a0b40d078000340880c4034064541822000b140e50b030040c008c6050711030041c1c0b043e200c00c1501a202c02100c0310702800c0b04030b0292800882c1c0345040b10124804183c11f0b154500c018281c801c00384114103090080c5180e41c82c1c00c010b414046e10b42040024a8640c078a07402d02c1c0c4144110000c6089940c40b80c00c06400f4040380002044416610800900105400c3c401d042c069011007000c1e11349a40b042c03140b14407550301500c6004000f450000d00f00c6a0070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 189836951 1250 189835701 189835703
    0x6040b030a0f0e03072d060e010c080f04080309030d0f0f0b03030309030d0b040b10020601090b0117010b0703021f1416050a050d140f1519091e050c04030b010b0909070507 75
    0x3c1b000000c0d154090400407124041c1901400703000480c0e0084a18250a6407103580f00c0105100c018824008038050b21403255038400c1d04038440c2900c0391108002c0768114400c49490310041414407401011840595108241c0c03031504440810005400005040c0c9a0200b140c43c0a90350b0010310454181c00003d80200c000003074011b10010b00030f04030b10005003541d1100200c0c200103a100100501c111159031103000707101c0b4824241a490740200c25a0303016042014000c0c0440c1e00d50209800e0b0425008100804c0461034000912107101c6d15101c0b0a0010010043c0724148040765401099014084900040d0f1141d01a41c42901c0c0c2a2070f26030540d100e43c00440d15000180d80e44980e2042d01c007d070140e25001c0c1d40c00130a0b509a608011580032502601982e14a100700708203115003030b0403428040304004440c0c4040740820400105004011400d03208400849414140403c204117095040b00034000d5910600803504d640c0d0700d504c09400c0c94000c1502083d04544888041041180128041d040301 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 189838201 1250 189836951 189836993
    0xb031b12060a0c2d1110060306021c020f042601020706020d1d060601080c07080403050c01082202190314010501030201120207020d060b0f06040b030a0f0e0307 70
    0x11800080d00c40e1512030115045203803690340303600c100115540012485000b2808407000c3d07482da10090f043c40c1003040300c00340102c10300c402100d2119924809112510210140c4c1350200890f079502d0505402075401304a0006400080c00d04101c8941040e20039928110312480506040c00d05118003d82010001c0004030f484100e0f1907210030565600b4002080500c0c800e83d40503845000c3c40f80240162042c842c0070745e001c4078400f6003400e041c5000082079640944246403610a41c3c5036801e85680c03a200300e22018080510001d804814460000f41c0c401c500d0f0401c1e40c820703000e81d503090841080c110540d1035030410010024124009440d00c111319046080c00b16045d100190303580d955440c0419100d0002104a035140c5004001359a008240c00b00700766004c00c02540b418019600180b4445d5075910002c00d516a98000f0103a60340312400340380200c0c0d80c090201c0360780355240e102c40c0762140c02c211080755405007400c0d151050f1642e43d005401421020f50000c5040c0341c000e83c2d4605001030040541012 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 189839451 1250 189838201 189838219
    0x50402060f0d06060207123518030c010c050303010308090f0d0308041a070e06130f0305031213030c11190b09210304032003010f0219030b031b 63
    0x5004007050050a0159211030001006032400300c0180c00e06106901c040195070079007402c000802c203420007842c6100d03890b080012030100301c5100300790072030011944000c0e5801b02045000741d003100230105100b411021070454034807050304401115016000b00c40104590003e0004000250598005d44140300005090100e400c84800201d044c0c488280029000241050180014410301e8a8100c0c01c01c01c1c202f20840d4685002c0e10080d0501540c5480f042c01468000b804c00b0102c1c105205c820702a1104081c2c0d42e01d09a84da0802c03d507243c00488203007960303000300d501144a40e40464815500036a0540b07480000c9002511500ea981481d12007854018508200500501d0f000b03802e203078003601002c407406440b40c10581c10f00c100e0300c035003540c1058040c1c1055070302c40f070f9450b000040d41e049070b5112050b00d5030380c0608008004030400e03441c043c941541c01e0844d0303000b2001c4503030045d0540e41d8010400300c01a80360000d0031030583d903803240e6040d09900301d2054180e8844480280c80c020500217441c03614 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 189840701 1250 189839451 189839467
    0x30c14030f0f070b0a0b1f050c030309070608070306030b01090b010e030105010305011a011b0b180d02010b120303070e01030b0a1a0702010201050106080c090613080109050a02030106050604031505040206 89
    0x1da440420303061085100000c03008104403800c10500e4000c0b140000401c01e035482072000c24040b280d8001400841c05401e80d080700054860340440c0c0b041c62141056a440b03091107400c45545035250301800c0c0c08075200d0000140b50a2080c800c2d00c0881e80c0103021010164a80f42844001300304155940f0304021030385030000f00d562801d0103140d00862040e80000b9880e46010784640704e043c1641c802d00e042003c0034200f003001000a420210455410034002602c7e80c44900030600c02600d0707864504568003035000040080398042d4001281d00b501507130381000d9281a00a4562a8801111900d012904600303840005511943c080782502d2409403030100000d460303000b5644140805000759951500c0041d40400b103503428040c450040c0720604001a40b42005031050086005914000d400b0301d10109a0f01e02c45025424941d00400c1d00d00e008000b1042d150814548400b14854240d000c0c0d820490005410706204d0103c50480c1d0f003101a080804070750b2000300c0080c06015100742d030702c01c2c41800002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 189841951 1250 189840701 189840727
    0x20705010c0e0a05060f0304060f1b171e07110c030109150f050f0c03071725050f091302070210080901180b04021c080309010903080c0403030c1403 65
    0x840c11400d46030b542d0315200c0101080140700c01034101e613001d09400d22036030799030b4640101074940003580414017054610500e05103100402820948018150980c02e20300e10300c581040507400c201c001b03810625440d945040c2851a10310040d1140981d80110b407000030045c40c0300702e40c14200c040c003c00665007020480c1001a0a440d2018801d8414101c2e02940c061180014802c041f2420562401440795140001190310450b0000b441d600d030082e00040080c44281c4140004035070350030302c108440b0041c1404034400640781d4070085200101ca080c0303175440704001e00034816161502440c3c00042d1074a0358a01c00d100b000303442c0d1705440440640034055440107a450794080c0342c2000050303840100c14500100d1440c2900c0c0078040056485c8080c0c800070002c11403007521a90700c07a4040d981c02000b101404458984411f0010340074042083c040301348800d141d419003200344904e00036034901c0442e4880042c01c04451256110040104517803201c2800043c0582d00d00000d803401700001e0380d0500080500300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 189843201 1250 189841951 189841961
    0x1e0c010c02062e080303150f030705032805030403060501060e0906090c0702040e01060909021c050d051b01050405010509010c08010b042c010308070209070c021809030c10020705060105010c0b0c03070302070501 92
    0x40404013004500320846030600b250340e4035103d0780849c000e00500e80340c6800b19442d40c16501420b41c018071140c0c8407981814032000041c4650394880300700ea54503940d900f0103900504c000e0107410b00041003016841214a402d52020b4080c100080010150707445260382e0b0405584841012a00241c0340c65200e4010384082c82000000d01003104003003210201c910400040710040f062040700e0803a4000d100b804101c0000c3c140f040303661103082055403598102c0107000441e1010b00c04214940c00c1c03108100402c00d041d000035001c5c0203420003c0c8030401c1d143c030003078804083c240500c00c00782d8000d200400c2603070714018140c0c0100380c0b0014001054524040c9407054800c09800a4400500c0000d4083c03c60810213015035001c015490008c410340d2803540015441e8000341710101c51884a4404210700d40d070280100d6040d40c0e4640d044804081e00b07414810043e4008120588041c0540c5000142c0c0b540036403045102e00d980141c40d12200d035110f03101c2ea0003581000e4414410154284896030000d01c1c24411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 189844451 1250 189843201 189843211
    0xb010c14010c0e09010806060103090c150c06060b04050d0b04020409020d08071a0f040204330f0603050105010c06020c15040b090f030a0518061e0c010c02062e080303 73
    0x4525884500005003c000100c81e04901510058004000a0101060030794006c0c03400d18010aa60b030840c28103101c003c0c40b54200054904204104106454100300b21218051150b5024401ca666400003602c4078092449407907000713070310a00c07108005001150280c0d07000344001c100041180d555000310700c0c15540641d089402001c00220b03041031010464455050040c1100201d660389069940f007011007001800090184d03480d42000e40d04040c8948100c4000000c550032624440c0340305510f8800403032035100b403c040d00030403000816075601c00d004141c1a60f106840f0040b0721001607403114029805405010030a0007040c1c00343e0000c00041d561603000324000c0d40200700c01c1c241305007a182070038400c0c250120280d01c20480d0303026558001c0c081d10030603442800c5c000300030700006011450760700c01c403400d0307280301c1c80403a00c0d040300950701c90060501c82090304000c022000300d5040981c3e030307840240c4440018465500b19002d000d11820b50312005512024491081555600d0382d56240d03420641e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 189845701 1250 189844451 189844453
    0x80325060c051803160501110a050d030609060504060f05120f1212130c05060d0b09090f0d030b09130201031b110c031203011502030c030406180b19030b010c14 70
    0x1024544141e81c800899180c0800304c0182000c0c58241d0b250b900c00807034600ca001c1c14080000c00d4180f101b00e040c45000d0307000f50403200740c4850310138200009004010030701a440445161400c086001d007040d114076001d40740c10f20014141641400100800c3c42c6207945c5116107889041c0b43e88030b50710b0013070001c140c3c1507200480054464103004010408504010801c20f091007000315504003051180182000300c03031040e5030340c1c0d545409940c40d00d40500a8612041d400c003110406000800fa4005006841c1070300c402c017a103101030481d400440070b42c1e02149503250300c42c03c184041107984100c180000f40662050400103400001c8031109400e404130460780001051080c08105541c4105124005000700b048002d4a2a030b0a00075000c00a030206001e40900703500c110b40843c0c0b44a008004031010a01d1000c204ca171500c0d69804001c0400180c40e446a420001c400000212105000155400c0341d001100c00d0f8010a02100d0440c0107080503c0d0050421407117603048400b05002c04010a5220301c098 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 189846951 1250 189845701 189845707
    0x60903050306040b04020a0905010f0504050901030c0e1e060f18040b04060609090201080a0506121002040303090f1d22050105090c030313060c110405090c090c04080325060c05 77
    0x82c0400c4116100c1300001070045004000301e007443d684c0003a00200341c4000342801880c4031075403501103e09014a0f00429003115201f0000300910003200c100c0000c48011420060507540c620004090302c0b400024030a01c07041904020841c1484c1c030460401003800c020b441c03c950200524102451036400f0386094640140c1401440240708050242001500c203c01d002d0103001c1c1507600081541c00001c003120700d0b55998101095071a81c0c0c151100000388042c8007118001c4c0380d00c3e20500000d51040c40102c2c0481d040c0c000000e8964400c006403c111007410f100c0c0f0381141c04a840750303040380000030004070309090168441420140b0b44c045050089002e0301c00004d461038054215481c1c00d4000100507c00d51007403101c43c202c403003150790a0302602e003140340c00034000d21203241560714400240311441d4000e0410040001c94000050400c0c000341c1c1c02c031140709480c0c407014228051031040e0b018000c180c0d00200310200d442d8502960102c06044a10400c0b041c005c030a4841100f22500320040d400090000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 189848201 1250 189846951 189846961
    0x9080f0a020d0905060904051302060301232e020114072303012103030f050c070302150f15030304090204030812070302040f140622050112020f12040f0609030503 71
    0x422841107102e1403801c221001e5401d180004415000b070410b0701d171242ea152800940e0701c410a82101c012154081e1507940c50b07584840981c0c498510400c500d080200001c0401459483d104040314000c14140c00c95078511320080b540801104500380c6c1c028255900ea4480004450769050f189206003440c0c1e0300d0410824600c1d4140f41e80c5030100061030480c001c248018010710400241e1003a010500c045030403203102c1030f0714003603020748140c8401d2000145407004000412000030300510b00d19200c1e03400e58086000a24808a164a0644e4215013120249000070a20250420510511900107045030304180da1059220240e9001c2e80040f0342c0201e01084c14a8403040c0f80203890340081940c20107604213824040f000c0c4038030045116140b4050000400c10200d9181d40c0c0c121901181680b0380320703484a251159281350080c0603c54640010662010f42c144400b962090b00c082080c12001c1e00d18021a40303010020885c0041d10076512000d050751185c1c001107079840f49411251091721a65180c1c505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 189849451 1250 189848201 189848203
    0x10e06070c031b0b04050a06180b040902091219060506030a0b0108031315050703030f0902040504050601080607020109030504050d0302070f030b0a0b100c0b280902040b0f150c0109080f0a02 83
    0x3c240d12040407002c080c0006e10851f5194110a029980c552600885158070131007843c2032445031b41c2c00202459400200814045040c0d0010078100c030701919002034138403061305159550700070856000c3e048046040d2160000d0710a0704002c2d082320001b02200c81901c125101c6e407480d0300c800e0f0320051031030340700003840303d0380c142a4019000202180c00d40504031088050300500a441100300040400d9030b10550000c00b8005544000c60b09500644104128603140c070f040d603920002801000030900c41c140c001801180305005117552207515544240c1410726000600606c00cd44010840a5002d031040200d01c803003040901100450051608a004e0704011120b401101c440d2006036004403050300302e504826401420f48c100442d40240c00b64907942d6131001d086204c42130305070b18881000311000c0083c9900103030f400030040c00b40211810041901200100407166009100c0390381c005004450001481102c1e4020f060a102828000303c1d0700e00c071664a01c809544400100c00d105100828201c0034564 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 189850701 1250 189849451 189849503
    0x105060102011119031812030f0515120309031c0f1e0e0f12010b010215040b040201081b0a0c15090302070504110d110702011409010e010e06070c03 65
    0x5000e00003084011800c0140c1e40080c41078a40d0013501000400049481d14402d40c0104000c445086849641c142145484440044048510300000303090041d28001c010051064a0041001e05c400d104410b42c41d44c00d00402d481d980400500b14001400307000c21903103050186d440010009404c45000c0300d40400040d1141180104003c1005181610854030106480384071502d034542c1c0c10702500501c2c0e480c00007147d0a12280320a9000003070b060b1400c40032603054006c106500400d03026140424102c4100b80c801d01400c61f005440000400007050142d400784590301d41056901d02c0801c41c0036080240d09410360302000302e04d80001d4074120300f04280000072030000e0a10b804170700d05000007000742c5c800075942d034072078007a05108542e95818800c0070081841250715050140c2c0707091000614a26501903240c00c0040203a01180d4030342c01100c004124003040340c1d034040050312060002c42c0507000440380b482031148466007104042107a800403513010f00d1a0f5000758401c082e030078050f841c0400340e4031313501c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 189851951 1250 189850701 189850711
    0xd0603120e10030921050418020f0a142502010306050405060d120c1514131a060f040504140d020f06010e1e0c070516050102030304170415110105 64
    0x40c5070605103180d81d2020300c0d0011000c0d403441c000ca01100c45041540000d03020422502610a0f14005a0186900300014004981d0f01c400b070110031210810019090b4400c580f03039610000e0b001c001030741189004181c006086203800c04502c0c24000303004000341c000d404803880b01e6800105207141008641e898000c02c000780400366028003c1d07040c59408290307408050130000703040340361200c5076104907440337591042161604510b902d00d550021240450090001022106440c0f040f00001031007400101c002079110395201c04011410640c182e030280340d04501404159001040310001c0c0e2003540d4600403540510700034201141c0850310035102a150614490703068040d5007046145905481c008145241100c1d0791000b420070359507a0035010340f41309007403c2d014002c0c0d900e6003040c042503540e0b1402078095240704408551042801c0d0440c00307527103c1c1e02d11450b0700690040000400143c07040c0c0d100010791520fa02c84a0505880e030180781498a4030341044800110103c030f0f0024041070034041c407a044 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 189853201 1250 189851951 189851957
    0x4060e0105100b0d09081908041e02010804120201110c1c1b02060d090c0e0910060f0603020c010605040c021f06050306060904030207050307060c03110c0109090b0a03080d060312 78
    0x280c03520f105040c0b079010785424060956602c111820a000c2d0440484002c0c01460078070030307440901c2c100007412038802507e0959003243d114000101d001c0c1103012604c240c0d42c05071a003460035070b2640e903808000c1543c8650303a01155200c1e203240b215241500050002d66000d48041e0080304814802100c0c91038a560301d40c0c04000c040400da0b900681d82c640e694480b140c0507281c0503a902c01155401c0d02906844200a000e0710745c0303072400030300240100003440c000c40d1558140d0304840b039140a81d40c00d6032070324000c818006510403010480319000c1c1d40108040d0210300004114981d4030b600040032244201e03082d1000d81c01c926040b140340111900601703010909078104102c80c50034100400e41d1064001e10603405001d820300494103050081080c040100720080450b000b0342d80b103000090603a60010170481c04070b000100450500036010034861204041039444003600d610b0940d07500003600903881d0840e040141100003101081001001300707400240c116001c1030052171454220300000c0c0b074041603020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 189854451 1250 189853201 189853231
    0x306050a3c0902070c0e130209130302030904091a0a05090d031e0b060d0513020f01020606010c15090501050129030f0403140f1603030605100917070e04060e0105 71
    0x4104655081d0300151560360030010f0701d602081c6400c1e000311005070028109141c1110030801d070f0807180304000302c09501c2074400200d251601421190b00800380da60040150300148240c068034100755008180b02c5004516200341265502c000c204150070580310041c45c0c41c3c03244c0c100500b03280200800d038118401c82ca0700308031003c0c80f0307900d0300421098040040042e603180c410200c80ea030341d0720381030340c2c03502c1c00320b0404000750308000c040b1201070b1000c2c0c8030807401000d103000254100d41c00450312520401e01278640c03600314025680c560311072148090300364029541e1404c11002107082445001d010f031241c1040180c0d4000400c50541c51524a4111104001c03c10001c0140d0007001e44c96003900140d245c100003001d0401d0044c1207003180103480a04420900c0412003a5035059151f50f10381d0701c1406510f04000306501c1d003040c0403e104060b016240410411001044004920501c08607940d07810f6007600d60701c0340c40302c48401c0404000d072001c2d01d96035242d4801150b5120b00384155034010034100c2052803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 189855701 1250 189854451 189854549
    0x6070206030a05060a080d050d06050109210533010b0327070b0d0f0b040b01020d0c0c09140a0e07050a060309020f03030a180504091109070306050a 65
    0x115110041c85485181e84410102d24941c9a1034042c10240c00b2100540c1c01c7c0c0309043c00c0092254021082c1343c00f92500704a0000b62039402802c101003902d1040c40010340031031a98181004038202044215194807594060907110380c800310701302c42000180020b905514100c05440c070859801a005030043e03c03c10820f00019680000c201029602480c100882c801d1810428a06000160b030284901034000505400c40e90141d5020301a0818541c004004000800c0c051001b00c505080c03030b550140e488010b0480728a8000e41d2454000c510a1105582a907154803400c0c1c10759280030103042120811f0801d0003001d0141303000b10220131300711074001c0c2160ba240c1400103001e0f10142c803c9500389071703031802d0030000c1d91070740200701c154980003408499440020040061222640038030041c03c0e035600010100741443c2600500c07403036540005d0004c543e12011800c20081c42c0c8040c1942003815520781c80001d00d07488071111000204400a95012985c40044100c0740000c1d41c480c12001f400fa02481c0e0f04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 189856951 1250 189855701 189855709
    0x10032a0801111905072001030e0109050d0e061902060103050d0309050d0f2006010501021509070e060303040317070618020919020408010501080705010906050f071b0902190e060702 79
    0x43c9945002100c4807443d1a0100c3c029605481010006000718205c9081071540a860741074a030721400c001e90381000b001041402030340c225101030740014680e030003070b40d03901000328804d0b0754120005000805542c504002c00c1458680c0e802e501d95018096007000c070041091100a120f201c0e070704030803807e062183c03d44650311592036507a00f80494003408403d06050f80700300d00c2800d00c081c58400d2008814900041c0d400041c2d07440d0404d11400f170061143c41003e044040d000e07034540c1d0041e411500203103001400d0035800c1e00003000082845405100911001010a050303400500d0002c041070b07417581d66a011030400809490f0604580e1062090198915005803200058558000c0041c200103640c4070b60441248064130880d84580000d608120011a140c0380c081114000c50b0007d0700c80b4641d0075681d6005403064028003a802d0f03000c40041c440d40020507000d0451200c0003242d4003000c02d100fa00c90700250101d0304002c02c07a0800c00801800c40c40855040761040e001220100d4103035013400901ea00003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 189858201 1250 189856951 189856957
    0xd050610050705121b0f0f060c0a05030f0c070804060e0a0b0304030c0f1104110c010c080c0a030902060f0f07110102192a030302030319020405100810032a080111 71
    0x2083d14003c0010303040b002d200448502480041150146d4540c03031101108160759405150500340e203400380d0b01c0410500d151304400c9903158280c0351199400e6685910080154490081c0300042d504420400755002903e284010310280900d07445141c13160300000d091011281241d0401100050204180000700b50800c02c08420560720201841011880d454818540626610003a41150404c5001140840510054501210b803400200a0750000b260121105201640d00c460800420409181c003244203807c9204000e00152080d40340004a8200781d070b1650010719910044080031485908200000c4001c400c111424030090182c5114800003860503440781d500104090707009420050700102215800c1d0580c000301c982080b8556890402940b030f50f00072a000d8018244040c42e0f901d81c14198403d440650f040501038001c2051400000d4407920f03406003403d0350100681c5000000030b0110500d0a203000c800008030584160400650a1120701d5600310b203915904040040094001010603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 189859451 1250 189858201 189858223
    0x201050306060a030b040e0d0e0603010e06060304170310030203160602060106180e0103050c011209030e060a0e040603050102270d060207020a09051006080106050306011d0103020c030d050610050705 87
    0x83c0e0310703c07100c4826001441e842a4080d0043c0c10710f1010701d02d012010030f025020801d2a2501030701100400200f1203070744030074040c000d055030f40d100201d40e25082030001b96038014032400d8146521a20b400158503243c0084414201c83c40c42200301b40f0440c2030605c00e862400642d004000310381d5040c1440a07441d408140140c0d02040300c01031040c00c2140710b80702c24800030080390803400241c0d40c59082c1aa02d401c09603041c00c2c041030910002e208039560610400311000e0f0181e684548520208040259540c8010741c042c0c02c1003800d00340480c455503207104010003184210b0005035141d25400b07101c2c042c0e54051387c00000c0c1c00c17107148001c2d0b42d0b921188035515026a000d0700060340d4010510001d248084542c04c2007810070301c0c000801c180407a021a60070b040e142152520016aa80c4480444951000300c5680380010398030102449010102c0c10000b801c000141000340c10020008101032860b00f20180544909485409000744c2c0e041c403a0071040d400e0002d1810038504042901c50030f035a0f495140c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 189860701 1250 189859451 189859459
    0x1030327151b05031206060c1015080f0a03021209010203030109020706060f06030204080c0d12031d030c070f0f060c24050c0903070509090d081b07080a110a0201050306 74
    0x100860007610071410003034003002c84440680b00c0b0b44a0f0901a40d680c0158200c1c04100d4600c8021814610305502a51024420b80c002032089800003c2c0f4440549031100010800240c480030101390b52005002d04800300070313441c008008144042c1030003450421011101d4090710020820a403030350740d01100720390540e01070480150f685d59452505900420581e0300c80c440305082490301060b1254541c0003001100c5500c4104ea80340e00c5040f00f003000031032002100030030344186940c900840c9402034110703041d042c00c001d0b0281c2c660120b150500f403c552000381801c01d13541100c1d6090020780c1c19800c100b0090b2902d000800901820170901038500b9010700c801610035400050310a041c1d01010000802c0007003140014802810400c00144413a0022603034244030380100500460700b400c00a168900c076003900e600910103510000b00030340306408094440c400321503001440200f04038000780200081807140c050300b6941c1301441c0340200726a00b968800c10290300800d480d03402603030f401410761b50010011a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 189861951 1250 189860701 189860729
    0x4060c02120a0b131518020111120318150112030c050f07030609020f040c140f0403081b0d08010b0a210c080a141920070b01030327 58
    0x7001031441e2001e402002000024404104003460000003a410a4140300d14440d002d034030418010700b02a1a2816813200010036007a900902662080c83c07440300a0744880b003a0f134005911807882c05c1c030343e0340100c2c0c100f80d46030002c80001c80b10786810026110808882c20707141e400b035410101d11040300302282001804010604d15141d0902600348400004020400c00300c540403552032a000f8041c082450701640710b05c010b15600181401d00380548080d44000c2d903117011000c1e102001446450b00215071131500940288404000503501400901e01c0b0f2899140b1010b4440c01c0130145460054442912001c01c086003004201200001c0143d80c040c2c40982801212001898540d5038802454401e4401d11810710103034090007034000400d03d0044040180a0140c2c01c420340c640c110701c1c00c00760303090f20b1845c043c1441008003074000d40c0300c20000854640e804001d198080d02009080d00405010785440c40100010010940c00040d5481c0511603511100c13000078900c040241000011321030313040ba400310302c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 189863201 1250 189861951 189861979
    0x5210903120901050c06340801170705090f060301051006080402130e1606030b030f0309060d0908040f05040c0c0b040b04020310060e01050f010e0a09090c0515030a0507030204060c02 80
    0x24006545c00c501d80c840455a1600d042814410b9000007006090300940481c0c0c3d00d44803810240310a502d048800f520350a4203a440c1c001080b0148141c418002518061000007041c2c999418448900a030f080710b071462034905000d004c142c04c50f100900001c0082014110800900d500314000ca03600a030121030103d1802c00340c16800340502146051581e5500600b043c0b04da540311601044801c0d140c041d40c04000c3d400443c828541d84400720104010940c3c000c1c00303001050b20f000d03401041d04807003038a408144160142d54021980c2c02507001800c40b140303525003d10990030310788034848030300429207000403400f407603a01c1e111b11004002d40040c00740d51000000800b503440030000e0035040350700c6000400030f05542c0c43d801031103a40207002d1584200b03010422500298410310062910240040a1407486441c108010300104281c0c8000c03a04400745c07541c0051140d9412508908007840d00445079620320307100c0c0d084012a2801085035080c14814081400100d0b80010445c00c41541590084e05031070034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 189864451 1250 189863201 189863207
    0x20d1b08060d11040b10030e011a0f0d05070b0403080c0609060709030b090705130b03010b030f2e020f0403020f010c05030d1e02070302160e070e090403030207060905210903120901 79
    0x407200d41c3c21040c101070070790b00c86e036256002d04054140c55008120152302a40d0030341c01144000c0c829640710a910b03852107001c0c82d14503480010341c1c2c07203003048a05041c0d03540800d1500342c01c1540b00340e40452001c039803080d240e50240940d590007112640940010f24108c00090304441c450b0002400340080303603000880114040200001801d0f004201d1020603040c5058a8082c01c0696103942c00b0f9400d1440317200f8181000140401300d4041800a4501d280c50602410940c100c50314402c03500005c0540801000c000d10710003016240030f00488a6a142c0c214014031240c40103221640e03040101c404034410100e034010080e5011480d1203007002c81d580c581118040850848000704450151000403144205034000508040d02d80c001c600b0080415a02c80709030015a504032200301c00b00c2c6403510314100350314003415500d40c080e00c2401d005003400c0641d2a04000c0340ca60030000c841360350200ca804002000b00344004041201c210007003e10301403421010a84a4090640904482001045400310b60380 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 189865701 1250 189864451 189864461
    0xe030a0203010f020408010b03010501030f0b07020a1202030703081302180714031608390c030a08091009080909040809060d0b1c0f0b090f01020d1b08060d1104 70
    0x40c009000780801c2080041800083d4890300c2400040d601c2c1a003203403d14101030041ca41280c1e004640340c590030605450320311030514014040d5045000d10005800041c00060702d0290900265004540b84e90481c41c0203862040050b01607552054050b1040c4016038802d5050204100d40c90840241500c039100266070581c0080356195014902208000580d01c00c06904804c1c2c8a25944007000380e1a8a844400402810144069030031000d19041e400360090280c51001c041030205100d15168044130503d0031074202d01d041c1030004903483c1c24000c45403020803a055800041a00410100032240d032608454070600e0103450045000100160501101e1030543c4e10020000d0200d558074451600c1650040c00410440341c8901854011801d0021014450a03012540100c001b04541e62640710111250002010440d0718400c0b20008000103200b80080c001e20b0b100510701148840c0d440b986060210001410982000a04001c020455807100710035030700079801407084440311003140e0114010307107 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 189866951 1250 189865701 189865703
    0x21908190e0a1701050109060501080420060c0303060a081c080604060b07030809060708010b040902090d0813050a050d0305030606071a13031106070e0f040221070f080601050a0e030a 80
    0xc03018100042040221503903e0b0188510002000b07a13a0721050100c003191040d0003180e000070100e000190011b9a1110507820f00140e540a8164044272000001d800e9440702c0369404170340d04040f0074000a400c080302184007a0002d10301800b60305490321a186640e98440b0b0640041060240208400781c0310b84d40040050a203925501c1c5c2c0d1044542000b900c040d009a070b01880310312910340010865803280d00c505040c0c8190031400c0340340501d820703003c601942004401d158011500c90031000001c0c9003800500850740703068241c2c1c0d4094900000c000081009600017806000903441000010341d1240489602810842d1540c1c2c8445090074032032025400740103814106071a81080c4010196000040d07800d1070721a59684003a8076800030300640b60701098a000d00441c1e201e0b10540001e2800010b19107040b100640014104141e1080390a44226110700544150311841c0511046a034480040110400307076040138441b504007040000c0245c030500e1802000c1200e403203000701d0390355400e1002140403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 189868201 1250 189866951 189866959
    0x50a090807030320030304020109050607020415030b0703110f030711120c0610091506030209010c05070b04080606010c0c030209060a030812150f09060f04140115021908190e 76
    0x340e450746400b4000710920340b13181c14030b6106a1204541c2d80c400000703c2e0300c181d40c1030f540c2d104560300d04424015203402080003268070640710040c450800c1c0130001d400e40214000c064040850405501c050101c0300b0440c6c081d80c0c072080070000281c0c00040d400460350000120f00d0300f0001c3c0c4808826043c10508440d803000300101c80010480340900700010107038001d41e0024417540080755607800400454009484054507208159002c0000500940c090641180181410034800442d42e99140c100011504410103118000c40c0c28002114200803003a8840b40a08104000b0700064a42011041075884024410035000b4005089a20b50301c9402c1c00459100001e107403201d41c0910070680f0000100d509041d440ca400b00c500b0706034942400c1880c20000c0c0605005034a0320390304288a006064070441c50380164940314080e10394881d1400060083c4a0000554a080b80c2ca0100a0504a00c9004080d2941910010001007407502045580303143d1582400c00310911a00c030151a0305200028080d84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 189869451 1250 189868201 189868213
    0xf0301020c0609070510050309060a0c03060503100213050a1d04030c08121501021c030207020a0515040611030a17060f0307170f01020f07080c01020403240b03010615050a0908 77
    0x20f0450002400c1e41038400c04c50f0004540794846000f1034003404100e03488602940420003140110803150b0000100c0c96540c2740200d42d0b41d45850100c4d20f0180070502c0101340d158006a5010140303c400c4008000d498210b544114451801119001d0b090607503205c04000e02f40100030604240c040c07013404013074952103003915850f5606003502003240c04085804205003903100100c1c0c08a907202081c0080300c6148008000f5040108403002c5000f50802074049030011a045400705044d03036140d8000d05542d4080b202c943c1d0352410800010300d0064580a0340140354030a1212400341c0e81c03c8040e079071200103d0001c1072420b5440900144111104000403605400b42140110307203456810f03014001182d80d4070841e46d00340c16001e1128201c2c820380f03070000543c0340b0030321804e80026402c00c01400100f001000140c20541c41c0e0315110a440200d014000740b03101c000c00081c6a040c41c5000743c035842c1004a0081107401d2a0610012880901c0c07180c0c401044000600c0d00b105500558111029102d0780d403c0740c038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 189870701 1250 189869451 189869461
    0x1e01140a090201080a1401061b020301020708090307090209030601030602030406200d0c0207080c0d0317011e0603090b0406050a060f0e04020a0807030302030a080a0e0f10060b040308090f0301020c06 87
    0x801095801016800075010381d00003000000c1d98010303000240019091b040c1140e20380f1904951306c03140021200c0000c070309036030b0113000369030300340040c180c0c55001e0703d41a9580d1004904044c0740414036030103c64202d005001080e0b9a5602003400ca0459402100260b920303621842c100b002405400d044004a0f1000d10f03050810003a0b10000c0d10112070385030402c0006242c1800d09070b0396100d551081000a9115208000c41270501c038034491fa0051007410308100400c203c1c9001c00b0354406c241c0210000c80c6146883c0442102140c00100c005e007460300781081030030419241c60420300b4000f840038041544800128800c00340c01d50206004002c8030100e0003560b40c03100c038201d0000c4825030f4180e104100b04100420300542c0810540d00b1a1752540003180352986544e42964621801001e03071a0781e0b5541c0c290419003680500518114010700006042e10403000c3c14850229a19a04016050041804140001808101210140042201c545880c00c004030b00084c068031410f5041400c0d8040d03a01408 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 189871951 1250 189870701 189870721
    0x1120c0e0a0512070b0c150a0e071520030d0207110415120b0403030f0606050a0206102105070816031502070308180a0206160b090304081e0114 63
    0x90321082210016211650b82e030821209040140e00441c6503007200e903003000071040c03140041c61514801e20540b820341c019080249402241140e100c101c0c607480c0c6514200054081c40b05e074000c1c054060fa003510a04d42204020182c0c80400ca80700750311090761211240840c420816150921400384065540b000d15140c54010417260440007401075040440d907050400041a000c400d4540e4525050080c2d00580c03101c00c5122409013040e0b05140c1c0d00c00e0316032801d41460054a0281680303460b85ca6450311020740c000d140940c014598920319100250510011401c0110011030200204090345100e030301741001030821006600c0001c1e2885568440124112203121140032130b80240e480f4141009031340268000c0e4070980d14010006031201700080d00094503507841c0c0d280e40000404554030391010b640440c41340d41c0228003090440161404001c01c011007080b01e284d000c00120082c500786403070840015925180c0c40b05244606000185a501c01d82095108049185161100d03208034104a0451 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 189873201 1250 189871951 189871967
    0x200f031902060a02091012020906040b120603011a0607081306020d090905010303020613060e0a1b060903111512070f030e0606150c0102090d051b09070c1101120c 71
    0x864050b006410008041c1e0180d80b0a40d0020440030705110340c42c00d201403084032200c94409004c18516400c1c0090b400c80c0d00d42d8800b0b00003400210344056590910003c0040103082c0040c2800c0c860707810001d02406164500d030046c2c50309003041d2205030b119106890105c00500910020302d907070380318460000428030b80c0040c0c1c0c40600000c40e01e510340400d464114101c01c0d00e50034000038000da0f00000105500c0c1383c10080e210032701c034094507001130441c140c00005402d0100030070742941c49101d01c00c41c100103040240014001016142014424207146130703620301c084600500300385e104108102028a40c0307080881250f00060f02178035500741524000b00e000c0d1000500d8a0000c0005c1e1038264924220b103800580140074260003000f40c15040c500854401850703000420300601c0d95000c1c41000b04548079240144440d030310400203003917074507001901020001e401d00e03005403050100e8418004101d801c8010030b00501d81003007030b01220055640041c0d8114803034a00c2c1d0a10b6074a44846040003d07440000c0e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 189874451 1250 189873201 189873247
    0xe06061b250f0e070504080313180b01020601050603060604031205070b0c16061d0304260a020d030509192309070203160213020f030709050907200f03 66
    0x112452035020a203070581031840d00603503a108030300c480d050141d8111401c1d0654050301903e04503282944414455003981c0000d031140c000c00044800134000201c82d400c030910a90351200c800c104030703054100000d54851061040501400b400408241541c560508603070203150425005003403d98100802406548000f20030f40f00c9094440114607516400012920742500e0cc00038004444a1031701c030000206030002e040f00e1084800144046000c0040c80580010100c08800480122031400142142d00c80c0c2c5011018607000100041d0050b5a001d200c0d1585540524095889005800c040384611401c030301040b0190350f20f45400520b1250384101004900784444110400041c80814004004010364403000035070800e2008002c031141104807800d54900040c9180383c0c250b403600e0124201d070310409c04220380d014000108500250054805002840282c8031200186480d2400a020300e0448991440c082810710034403a10780001c03c0060102251481034a680340c290206480790038000102d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 189875701 1250 189874451 189874483
    0x209042009040c140102010e07150306090c0c080d150b090418020306070c03170a0204050a0b0f030c03131502090a08120304080906130e0601080a090c0e06061b 70
    0x4480456801c0c0101c035903020325404110354081c1800c04160a00300f0311040c660798119980c440c00120803050412000d4001c000c402c841c4030340c0e0b044c440d070b0007130540c1e800d074220003011814003103003c0c0340d250703c00c0112200070f421164058444102442103005000722402e402041c10001401245c6045090001d103031035001160200100703045180120300480022001940c103821a0001400d400d000d800d0f40c0c0040c91217485d005030b217034540c56107006000c00c080d5446c0e042d150f8040b400340b000d41044038001d0050b212410030241044500820381000b03200080ca071600e0650040302003481c03000c020015480c210350161429105c14403448154000327401c1003a46a01c103032560000014941e20100e110340c084e0004099480c41c5682da40c03201d02e1580d2000ea5984e07001441004a01c1040321540c0d600c01c080c094640e900b190608100f0b00052402801400c0122803520306000700c8002a018107110b011503849030381d0045c41390344141c005007141c014925500103010b141c000c100140d600100d0441d40f1072604070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 189876951 1250 189875701 189875753
    0x20708040e091006080a0b06040e03041e030605011703160f1a0a061502100c09030507060207030b06010915030903030b06130305010507080c070b060f1230070f020d020904 75
    0x82e0310f4a90303881c8409030103004070001f640410101c1c10180c0150f0700c44403400040b28070f03055407414030000702002c2001122210680c0302c0c0030320030006a4000c903801000c419041201000b010030ac0b4680300d21400c50b6284148000007412801c000d080b0007003000d50b40c0c11102003961100d0400441e4120b06044a59800062030460085006003c043c50700c2d0840c40c1130f41c000d15a4903080b100f220024402d001c210420722019440c00800581c04100c110040c000701c1c2d014121062a524040d044507030060310a905010035650b042c0404503a0054100008049140103d00d450403424140c00400c458269980c000f80001540c03132403180e041c0d40e00422a4401c80007000705a541000c200c80300325040d41c1c181c020328020802c881c08501c0610840750000002404a0041441500081c2040b640b02e100e04a0a422412210162041d01054044100c142d42588100035200e03040b8883c0c907100342000280350480064500040d900c0700c0c2c13036448255601a0040c4620705241c14a0820304d642400c0e0340008402c07074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 189878201 1250 189876951 189876959
    0x50c030714010e03010b420307030f0608030f070b09070f0b0309010b062701080601020319020a020604030606150c080702100309020d2004110904020708040e091006 72
    0x8103142100c000701c0c01052040003103001100c803802501e001603450340d01c034001e8010a98541000b0000780315104100589011124074084503186a8031004540d00c0070103621042c400900800c0343d501444905e00007402410000c05117008000e01d40101c1203074800400c204c0c0350701c2c2d040401006030782d000e4148a00f5a540e420102540c1d0b108500a45524143c0d0b2041000f46540030070156401070031007000419840d00c0c900c0807804030742000303550208a140380311584449845001039040780c0368083c40d001100c3d141510020f940da2041c2d18030702c4403044c0031050201d4814400e01541c01c0c010f85c014600d56550381e8034148400034000901925840303000002000140e280a4900d81c0700300395000d00003a0812240741c08018520704076540c0c10080c1902c230b208990040c0c1d21803890b400300c2e0303100d0b01030b800d4094969050705042c0185080711502441c90000010110550354050315000354080b9009a40c074585490300e00110f024a074402c1054a25010505c100c201c0c010440d1244860010010406035690b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 189879451 1250 189878201 189878203
    0xb040f0902090604090c0927321b04090f180f0f020a0e040501290307120512040902032d0f0a0216030302040305060f070801170a1e050c03 61
    0x2d00c5111a801501003004012803402c540001026030f00c0303401c00b0b00e241030752485010700c02091100c0c1d404150201401494418509101c0c124805261064083e0071004242c04142200c0c5035203a00c404109078180020101d40710580c1131110180181350703e03511240d8030840b12019100d8401c1d02910a42040b05038048102a21040030019400a584241003500b6403510000c0f101d0000c0c00340d0b00031548090114446602c1e0400d180950b201c2c1000091014203842030996404c0d4070220520307010420400130740259030003d2004296203441070f1501d144c89e02071805614001100250801414001c00d0000c0c2c0055654051441914104000d10741d0100041c2d886613030900c540c517080c10104105012a0b10211042c138071a61043d4240e000510704480c54034448284890035804400082d00080c0c14010450f05205282c0c10085046087d811410708410180200d8414040c1008002c2c9901507481e032a2410482d0600082d0010b400e881482d1f2090b80110100c1c0400d24140c58034461642210303602c0c14 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 189880701 1250 189879451 189879457
    0x906010f02060115050f030106022a0a0902030c09031e010b060f0304081c0e0d030b0d0b010315090b0a0504051501180c02210301031703010b07080901020f01060b040f0902 75
    0x200c690103098107030700340020808030b425002c1e00c0004000d001d0108122180e0510010350180026030014031000c000c0c1000c0c805010310700183c0d100c010012810701009519602160405d4840000001d070f00c07990342c1007001405000d1880000d0b45440741c2c6011505503024200c42e0040316000800a105000301c00007800150301c6600d00302035000d00e04000180201d803011001c3d00c55800c0b100c440300d000100e02d032243da003525881520920302c0d0f0004040310184a40601c60905514420340f00c0712114552915001c0e140801448051300071074445088034480c00c210780c44410b0b01b55001591a8440c20543e84410081104990813513040c49880c0c40d00d030484c0700c0030a000b4100c49041a8002d002c0b0030320030000c405800613000200652040700020030510703040008030f048803154407030307400c3d02e940c514202000080c500841c0a00b07400f4007000180710742e8003640201e4041d6908180d5a981e200000c02c0101e1070300104045544465180150201d403c0c04075800800840b559495280c2445480c0d40c81001284 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 189881951 1250 189880701 189880727
    0xb0301120206030919061a010306180207050a200405010b070c05041107060509030306010801050a030b010608070c020d030801080d170f04050715090501090609060507020f0411120402090601 83
    0x8000000303a6801440e0420003103501030006000d841d480c0d0350303010395911406100807003120301e140c42d0f800000100c0c0442944c0042c03203600346003c2c400b403464500060042c5040724003d105071600000c80005211013004003410540d8804424048540e001000e0f41261540c401e1750740c0b2560410000092460300c0c5400e0b14009031f00000c482e4035480c40c040410000f80005038001a1008041c024400811a9440f955200f404148065550703440c0601c0010092141600428403230b01e0300301020701c049143c012030981910b038141051400341d202c9640640b03601c0b59400009602003000c800728810594044086412102c285080340d01c0b5000c030020680c0c6954801fa054070792007035088005070300403180f240801c0c0c0290062007030714141034030340c80d2400a0180c010b4a01012420b8076070b0812a80d40c0c800e40c000d00401c103514201110508001c00101184180c4a01034824a20b00d000007009948681c01489010403681f051544c8401803a00c0091504048805034411030303481001030860350040f41021424 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 189883201 1250 189881951 189881969
    0xe011b02150c04050f100e0d0c031202070605030103030f1b03210b0303160204150608090705040207080906031005090a09061b020a1203150b03042112020a02100f0509070b0301 77
    0x4461700800340010480304141440c100001050890525102d624817042443d0191802404481c2503003060040f811148400b24110b60002c101044081d51080507207055036858039141c0e40c0b681c00604125011801c13078407241008004e1950b10f6080642041d10750201c0852600c4440c030580090792a001203528280800e90160420024000b08070780309444d20002c1c2f48010700c001454030600b410448100200d81005006c283c0b10010b000404508000100c02400300f00e1b403d41c604140c07580c0d614040d024370f0b008a802600702001040401001d1460100a4000600488140c0c640203150101410b40c81e00d090b560146082442d090801445a038041000100d0f0020101c10001340e07503282c80c444100c0440b400301541c81810841404024402d80f00509190903041c2e224185414050081040c00e0291100d003c100310385070035001c1e00030000030f00400c41c1080058488001c507000740c0c10a040600315504c0e1601c0c005107036040c51950f0f8080350266000500f290800d945541d0340071010300c020301800303800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 189884451 1250 189883201 189883219
    0x615030903051b1014090f03070507050f0f15030106090b0403080405010503040c0f0305060403111c081b0c07031a040305030408090d05010e100f0b0901090e011b02150c0405 76
    0x40a60f91502e544280085801100d03045844040400111420401c02c5000780d81c2d00414850010403c1108010402088010390328000f46583c1d41e41d07480740c031881400d004083c103d0711280310727680b040240c090740c0341301511004c414500301600b03050381c2e88240558004264088004516007004809403010303240d0001c010351525080000640c6c4a8100600c1101c51400d0034402150307141c810300e42c031401503104000600ca641014980944001c10101250b241c130341c441e070041803240c801d4400107031650540e414400019221200344107601840c5e10300a540d08000001c160700300c124006207110449000c0e00013075101090180c04912882001c0d240600080e03800d0000c500400c7c2d05038001d10f98094000d00d0100881165034441303081d00c1c5102504211500402d800c1c83d1019000d0040e400da1000b030684c20881c042000d8000b0381c0b540303c180142d0800f160340d01c121200f401001d6000007543c2403002d0754540c440442d840006d68840110950114140060010911007004201a2010b54070010f002d101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 189885701 1250 189884451 189884467
    0x6121828140307050d02030d06062d1206081507020706050406080a02090a0e15120a03030e0102070b090a030f02061302060702044503020303060118050310061503090305 74
    0x20305a01945101e881e07408104410400504100031401c14000d154000d9516506000da4040880b0041e42c01413062110422200c150f02d03c0e4002140c0f100b2040c00340c1c0481085110303a01b1920061801d5642c42e0311898841c02240c0d0040001d0728027520740c1c502d03c10b55480d40d2901c3c0c0407a101c00d110701c602c1010920510051201c580900401c0c0d40c400380c0b800d001420501c84030300050a00b449584030328a0b0104280501031040b40c3c4102c0b108a06105a408842601d4500182503469100147c0a410503941e0121858660000c0d011103200c290002039080da1801d1544031035454001b000c00403008100c00710003c5506900103e411849181c5a20f59102c0c00030b5030f40c00780040341d80f0581089030321903610180d0001a441c0e525091010b0701042c04074144101c0a5542401c001d200300c0c86030400e85c40c00c403c5003000039900204807030780401c003031901c82e00700e4010301620300c0380040716000b9950600500201d40d4808106038800e43c210752060080300390070b50344000c054080b545d0300320000d00054402c00c00d9034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 189886951 1250 189885701 189885713
    0x3030403110a0b0708010602190c0b130e04050c1008060a0e070c050609060601021002090d02190306021821071a1201080309040c1b060b06121828 64
    0x2020302500d4400e6420102c066600c1240b4240100d8400001c01c2000005001465040048103004074401e00f02000180568880b203800070620b01c01d82c41203240001b4810010584401c4800003002202501e08003820a850121340724480c01e038401d401181d006074004034281c85441054050b980180500017070f40d0030704010007104007000f80003109200c444030002000490410110784101c040e5005800b0307074105140024204600f10915600290040c01200401c1e0344a00380d042d48568122814080c010040615140024003540b0240c061803001c180f070322003042000c14008903090304a442220461642510a1044801886090003a4070042c1d00b0301c07144684281c3c0d24805100480c0d05420070030024403110009409030002e403801c5e000414041c80781c1c1050300800700c401400741045d801e442d98143c0382a2504501d040064001511020b010390302d40c44440803a1008000388550030380c0e40c98190701c0069681400e81c041d111a10556600540094001ca0101c0c2441000001e81400c088035460715 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 189888201 1250 189886951 189886967
    0x60b19090209010309020315100b21041b090911040c020606040f0e0f0309042307050f04090606230a02030f0304050c0a24020c0a060c050a02040f0905010e010b0303030403 75
    0x140b030602d43d517895140301582d000c1007840400e54455013100b40b9481c02030740c5411003560503031040c00c60300c0082c400c1c9100302c918007801c0000885c0046450303105a131a81003158032090800c4088111811401020032120815045643d03a81d0180440d006c046003c03500317000031100c0c0140d40d000180c01032400b190b01031405801c040b00908400c50f0100b5a4002d002c5510700703190081e1804003203944000303091446400c1902079480b218859207100c0000788000051010210401842807013004000a02d07031483d650001c069601820182d01d0070000280c40300c2e8060701c000d01c00f09884150003034080c440d201d1074030bc500c00c0b154480380c00c0e4040c602344074100003d40310703a4001600072a55400b980d0351174225501c0e50010703071b8000c1c040e0800400c4c80c2154140c01141c0c05c1100d4400b502150040140300d04c0940790b103030481c000c0350494a8400d030403540034188039050074140c01009510506200400d0210720954000c8007540e0700a00007045460444800c0bd070807101c2c0047c0c000c3d0503400034800140481d00505403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 189889451 1250 189888201 189888217
    0x1080103030318050303070504030308060409030f050d0905030f0c0f0609070b2109030a1214040f060b10030219030204030b010e1003050a0302070f080606011d131404060b190902 78
    0x351010b90511340c3d659007142c00c12981c080009070049401c04c141075102110903000082624100b001e0b04090f11f00800c0d41e220610a64144040040c4a89101d540d60b0f20001c01c1d10782107010742ea140c40d20141805480c0e80a04a540224860107810209018011441c24082e4081d1300062880d0361500c00e840720141c01c191131030641c540301804400803194000a10a1040c64080b01459594960300c00c0500014040044280300718175003207011403480410340605402642040041120f0f9605280450103001c4c0b61103181e07006103420358441c403940e416801a1040329841262650030003848181101240140c2c0b2002e070880000070300402840e50010300d250f401a9804610101d900e840e030b10388a28050a6030821001030380090703c20807040000641d400301500f074010190000b401d00b4400248011059204030464800a8103c5881c0e981c5011501c2e45044e41c20030203112410903101001d00d03280c400c039001d440701030400c00800c410b0f2a01c0400e080c160032010711144460740c2004084c01c0290003001d6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 189890701 1250 189889451 189889481
    0xb0301060503030f130b0307021f0b030f060105010207081603060902010509060403081c14150415060215090a080712120f0504110102030313062007120801060509010801030303 77
    0x40104207601c0038001000c40c2ea40d131007012503584042044103145280c0c03036070100034110800e0040c0400c441d804580300107444215005200410300555848006000b04000c490b4188101c0078910170105020911904990007602907400c0c0c140d642200341d031942e2003100a442c0200b41d1040505c000b980e25400311115034010314025007000c406401040d06075005810540e4040008100034050000d18050710100503064941407003080c41500f007203001d1410281051980c13030030031a1003640c19241c41e0700c2a00080c112103042e1240c56a034000194030f0384c0000d00f4000311099004005400144005400e9004e0fa0b40314072264908000303510741e40000d0514103020010400318050b44609842240100102d102c0710f400e000409041a2411562810a004006040d074000303004200c1034032402c100c2d50b0316084d00210007180c40b00008500301c514846040e0014500400450b01d01b0070f00c515540906a450015180e80d9010b07601e52106503158040e00145a001800100c010f1000030322a400000744200001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 189891951 1250 189890701 189890711
    0x70e2b1401060e1605040e040b04020d170d1a010504060c060612080c0609210d0605060a030b030d0c15020a1e08190605150304050f03070f03080609070906030b0301 72
    0x680c606080d02d0b03581c2c1c40504400c40003000e10900b03100440051601002e1402c000d49010f10741f8184e0006481c2c010f00280021003403800080541d01ea0700200100c555100d28080305d041240e40704204507400c681d4040078500d19000c0c0f034802d519400e0010301580c9505844050a103860000101c404855100b400c4030300f25101e02c0c001948000c003880e0701341c1c401c1c407508a0b80d0322880c1c182c2c015840c0900041100b00180d1001c003900700e4018152604218543c804590150713181035070745145000d44038690250b60024000035003402c00b03035810350010360144011420b030344c030f0000d410204562804d0313103c402504104504a543d0a035000d0780e8000d1071201a6400c0a0704e1400310070400d01d05000c000d09440000c0f50030030f410010307102c06002e40d440703801c001031408200d0541440c01060103186022000121260300001060174810100300000c000c1d00c119040704ea9a81c11860700e48100c151030381048000c10104070120740c40d450042c0115205001e0795842e0350441d03181213421005050031803c000c1c1c06542c2e41e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 189893201 1250 189891951 189891983
    0x10629071a0405150c03071d0901050103020a030902180f0f0103030509010e040b22060f08030412080417010b03010b06090d1709060a02060603060702070302010804030f03060e0f070e2b 81
    0x72008075440751103080b03003107600e92800040c064080422a0b030300100d010a03048941c1234a9542c4429181074420030b10300140c4441a21000b9001005180d00c00f0394459101c882e0240c1c80b4141d407034044e04c20b401d40000d0000580700d0071a0110010403c3c0030007004034100344000c0080c0e51261100c4140c07160010400f1a08083c200007040140f0384002c8001d010040c44400340c001e2072002e005c6c0800401c000001c6401c914070300b1501e075840f40198040c021300c02d0303280e6001d0000d1046807016580540b440c210500850b415441c6818020801e800c1242c1c025400d210344040d00f0702d0001705481140c0005084650207001e035640d01100c085802c444520035000c1030043c3c00b05a250300c00581414a011780080c4494203048003014074000300141940c085600486013400140d03030041603075400c15458104030b940320901c00d13800d4015181540140c41a403c4490401c8034505811038403038051201c03502d491000200f40b5040c040c0d502140100394011140304101d802c80c914100e46981e034894080c000c8042c2840b40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 189894451 1250 189893201 189893233
    0x2010c08071a0f330103090c0503070f030b07020c0117060315150301050c0708040303050d090203160501121b0c1704030c030302060a0509100e0f010629071a0405 71
    0xc01d03103c000f0400c005070208072000c1d40780c241c001881c00342c1d40240c0b107000301840d1070b100b030702e80b00c00803c5030403d1b07240d12940d4204150000802c021344030042c2580d1290b901c0b0442d00024010f00d100540740c0c0038075940840d03411400801c14403140c0c0810b03940c00101d0b8010340803820700e49a0151800d0b8042c0b1503102c040180605031856240151501c0c51110a800e118804060039114094480c5402101c20403000d000100e0740d400700e0701180da060819a88645558409000a0107003600282d014000c0581c075460103200c5160034030503528242c8452001c030411078a80c104803807a44154040c82e400d400304c160901409002d02058044c402c025002900400c14003245c0345400c6980700304c4101c2c000031018000c050701448034544c0514070500410040c58129030440e50ad030045e402c0060000d981d00e050110300070341400303590300a000000c0248032a59640110401840000c60b4200c801c00011300a003c450842d04100c4078540d8121009040c207042a28040c004194041e00171a51441a41030801191817 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 189895701 1250 189894451 189894503
    0xc0f0e180a020306030709060b030708090f07030b01180b1e0303091306050103110307020c0904151a01080901090b010b031f08010b0f04050103051906110f031005060702010c0807 78
    0x1940c081c0580c40781004001d05203440030035002004120f0810718140081c029002c00c0e2640042075151503111500c803144020700f428a070b140702c56040d000e01c050200c01c0c0000741607034034126401c0c1a121140041a2541503049501074500241d0000803007102501c58015010b0f100303a04440202900d1809507010700082511542c2d5000740007560300c5510402a07980c05101d1784100340d401020040c603510707000c0e80007519038409159661244011401040500c0b1110b182c3e041c8a0100c1d100c200040301e024111100004c00710000c0314001811040081c646500c18060382000550105c401522a400c101d030801b51500000c00c0780301ca690b000112501c1e141c0001c49a800181311800c000100460410140911215051403850040e0704000041002820002d4200d0700014544d4403000708041d685030080241620b42a410b0342c1d14004030350040a00302c0000150b00850403500b061000b01d5039001401a14001c01501a02040e1400b01050200300392100501c0750314810402805626004560244442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 189896951 1250 189895701 189895711
    0xb0f0d1106040609090608061e07031407030e07050111210702040c080a050112020a060806031c1d0901060516030e03060103080a0810050901170a0b01030b0402130c0f0e18 75
    0x40e40d13525080102c019548200c40107044000b010340800d241007503442d806030540f000458241400a0f0020352030b10f210b0b92208507610041403950130300303040043c1c1c01000780001000c9002079000306c4000181e190b00032200c00d0500b10315031024092810b900354a46c0a944190803027084154010800702005276228070070003034004102d448101030390801011080c100c0710160080030b8201c3c1503a034040003682d07807500d00f031046a08525040102ea5034000101c2d0030000ca862031010780c04d4440e2140d4030720320b420001041540c4000c4104040c3c03510b0010030003030041420301c21400400d00421812017200405d007200c0c0c40c01800f03030602c1040c40d150400401c1ca4807409a01c180c07481d40c0c0102c0d1407e2416800703c601508801d0031070000450a00340b4000490180c0103219800340e181d40c540c3c803000c030b9180c2806400101d035000b50000d07003990703968104640e103100220780c00ca2044101c4a0b43c9044141107210b145600e184664526120060300902503905180440784180e00c01114003503445030001d00401c0742d03c68 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 189898201 1250 189896951 189896957
    0x32802030604080714010603030219020d06090809011d0f0f0102070f06200d0f0e040b130e251a0c0609070302010905011b0b0406020c03040321030b0f0d11060406 71
    0x9208139040250000d030810700d09661990400c042040400d03070000f0a011900d210300410810b04505100240c3c84003021741d4020207003400c01c030500d42440103130340c050a108802a2540720400c000c042402c41b0429070f006c0710301e90001544481095906040300d80f244103500600403940720588070481404a81810741c8680009080f405240e20307148448043c2130000c02d845c10040400803004840604401d50080c40c040800c800d11204444654590700905036089010301050403048846c5548400b900301105854000c2c031070703140100e0700d2030049a02030f042142c81c8403806481c9810080907243c090440f015045100e40148900fa1502ea401e1055030f00481400c00208a901d145200160524100d07901560500500852900f20710701c03581d010112080c2e02c0164040284e4461038990700901698002c0001e51201080200810503200940440d05110030240c41d00b030454440104c0698031692034864106402d00b80095950a1180803021100e00c100c0c403079151900d20310f0110b40d558109600c10000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 189899451 1250 189898201 189898207
    0x4060e0a170a1407050a0b0601021e0609070e0115030e0a121106010e07091a07140601090e010b0d021002010e060702030a090e0f0c0a0903020301090b160e03280203060408 75
    0x52250081c20a40501e0010b0b22240d05041c59030b212175403120381c03c58000e891165908002075207030f1310900401003240b005a42a0b0400540b1034007050b55540d084404e1003451090402c00301d005200c4903200303812900002e001842801280348110040c00790642401064800c4403244070000d40789680003081800075a44030f0040340c0b10403149516080042c0d00c462221181c000030300c1441c6a00421910544401c41140c40030203210500fa96064495040f000d0000300c80c02c52000540340c2c001c1012030480c0c1c6544418004c01c050400310a0803502c1c410140d40c0d000d002200c0e40401420040900d180e10355440c00001510314000240070b007405411100c050042e0400109465501d4000500f803014140a86070484540740500d46941d44800c00b400b6188000c00c08034000c0701c1030f031140107043d01450303004d80284072300c10241c17500c0c00d030031402030750007030581000c46c511400e096129908020081c05c00400411910600301c0b55070030401c4003040441030400322040c90f1001361f00c0c1044082d0203148070319030f0159 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 189900701 1250 189899451 189899467
    0xc1525060c1b0b06010c030504050d080903060a15091d0601151808150c0705070b250b0a02030603100912020705100509100905040c0903030e0409030804060e0a17 71
    0x1a0b4804055000c40303007040c18110007191110440c20f030f21030003c0c2880c100007042400c1c00d6900f8020756001541c0300a48003c103000b042a110702510400d2000e81c1102c00a88401450505035544042e60808101507a03204010907641500902c0e090900c100e12481f41080110f03010381003413401d03040203030f21500e01d03010231310340c02d60000c4803114011072a0441080242044101510f9950108410303210100c0c00000c85c030b00c3c480c4c030000c59483d035030320004480c0800da075a0702601054100800c8401454012103410644189030b610403030803243e01241c00816981c840154600079000900501e406205000e69111841e415114080d240c9016407801c0d0851000b03003030001d14000032a0081c1d8001c106540408400d150880c040d82c401c0c00084803610b80d07402e0fa42030200e50002e40341d03102036802070a200c2c2500101d40c2048003041528083d540741c1d80304000000038070080d98401140200060102000500400c1c2c03640d000d04100c1c25194269072010034aa10750681c9003011001070401808000340c580 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 189901951 1250 189900701 189900707
    0xd020415020a0510090b13050c060301060c0c05090702190c080a060b090c0a09060c0501091a070305100609120c05030607120c0206010e060d03030e19050601080c1525060c 75
    0x1079081e0b0b880b080034025a801075942006c2c2e964003518000800c02021a060108941406001141c4901900c016101d40c0e64080090000c0300d0250f0a80b50300c030508101240700c0c1130944207103108428940051401d0030031a035024400702521035064403403005000000c00c0d207060610208020318000c40004c104c4034400d00c10002030f40006400c0d00061203007000142c6005030000d8400d8220399050620315851801414214090849001e000f40141d4803218504100c0c46074060130b6010320080e0307504011945c1c070304070026682d1115014903404241c100f0401c200c0340340e00700380c0031b0901ca1003401450b40d0641d030f400200f490200d043e41c031b09010403070381e40ca06001c144080c80f400006100a1005040c40d51505480c191200030140055001d01812a400d8041c940280c0010f894143c11108980d40520348401e0b62155881c04401244c0c1c40c00b807200009000311b4001920b1400b0400141914280c0211b940d607103911b1b6112040e110b100141e90303000e00c0c1000b240544661070381400744002140c1100321000007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 189903201 1250 189901951 189901963
    0x503040f0c050a09021b0109020d0312020706090b0106021e1209010c050d0306030203150c040b1b060103080d0609140a090c081606091e0302100e120f160b0d020d020415020a05 77
    0x1030240741c8c90403200d90056a19600c8a40d0b006400d81410441064041d0310320001e441501006481107040001e400e0400100724501d504913641e80d403c0c7c4071640186552816a0800301c14810b0700741d80040c1240c00035041c0c200003005400d90504280040c0308803550f0341814003074000c111790046981d8090070410341c14140140c050030390300d036814070901745842d150320580c3e4001e90064049210001c40c01d000e8038000d01988030065000881220f11039030f90f80c60309401c03d6100c0303202520400c0c00c1910000d40c207040d6020b0700320300c420040320041c40c40e03540125000040050340c405075108007000304006500c05c0244800d071800e540a801082915040c03034005170150300c840c1c0c0a46902002d00344440400c2904941403000d580c2d0440d605500c2d941e40c400c1c05c8643d1010401c40960001d201000000c8900707001440d426802d4208040d542d01d03030307403080481203c1096441200000202007200d068000b07107076401885a1460510014282a19081400114086088a1005a400b4070345403070901004003e2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 189904451 1250 189903201 189903247
    0x609070602030a030f090b1303030f02070503030406020c0a0f0b010f1a071511040b09031501080a030c0215030a020c15010f0302010e0d06090503031501020109030503040f0c050a0902 80
    0x2041024501403000b5600c1c8507900b031100c00c140c2d840030712207001d03007158100e0184240c00c40f240740d2503070070105481c011413a5004801c034040307440d10702c45546180e42070082e546070680000c0958156a110b49900010b5403041d0404120740c029256400001081c8042d01c2c04043e0041809035031560400c0f40002e2101c010f40c1259400b40740d032584440520710300d10221020750754000e4500c9001e0780d103c2000c00c081c09034032190a1041c0000710380400c140a0400180c0000f4100318121255042c96510914080000380503102c8583c021000000120380a540b903286039610140080f10300d110701254141d0706400c159401c02d001c0ea00003607040881c500400500b4103050203048440010f514000641700280310500c002414020848090f21389a80c4162681e4802e40d0448018030040b43d072498619140c0d40b04032600e04540040c181d584030b03254414415088984da03d511050301d1a10386403140510390420a1045800940c511404111a10b404030740500038140b07000e000d43c9500c241520a1045044050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 189905701 1250 189904451 189904453
    0x90d110102042d0806071214060609090c07080304030f030e0105010b0a0c05030c032206030603020d02120a120503010807060e0d060e2103010504061d07080903090418050609 76
    0xb00f402104504101100310920b07407404011551500d00807420007840da81e109030343da8021070341000034180d04003001c6141402681e004000c4000c40c0814041894002d5509a07000202445492542e040c10400d103a0401411080503042003910b40c0d5240345030f481180d0413000640100c1003582c07125014020303400c40110103402404550305240c41d00c621400340038500303030402500050030000d2180600440d1250b0981c04250b83c0e4075044110f0303101860b0740380c1e24900403580745ca82e40002c08038860b00c2442c050303d900400002c0b94045640802c0030120b00c0003400007181c042da24401002440b550f52010780c014140d11200e49030340c034080e10030703042030f00d168441e206118008c4281402c9a95000700e052035030342e000c14002114513601003224a01001030f6035050101d100c1208620405480d40301840c1206c004039428440759803208104411106404804000c61401c0c10100311414012a087d9a124500404523130904402800240a9400040d1034400780412a07181c0424000d09008042d440307103840c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 189906951 1250 189905701 189905707
    0x2040f05030a0f061505030a2306010e07030902040f02030403120f1103220b01090204151d010e03190809042d1104030b010b0903280206071a090d110102 67
    0x74a0f800c2d450960503000400e0240c1c1c40040c019480300c04608100500005402c490050300c0f185800307165014039004100303e1400d17422019171612030010782036042c2d03071416045c1845501c400790107034040c2c0502c1000f00da00c02c0d19050244048011480658421400390b030364a03243c12104000c07101101c1c19401080c9015082400c4d040c0c6055081c0122034110240048201070354040007466400410740700d01c0104000005000040c207003000c0c1c0c0280041c2d51241c204121050030210050b41c02a9078000c040a4500a070000c03100d2035800340c41d60f000320040103010745105802c07940003a200301061180845150b08046200485424548180e40c400411807461503044405004448070031360034110050400782e01c0b140c5811061f00050180c5004542c821803a46007075071104124101340c2c100c2d0365854000d10890f1751001a40f44244850114001017000e11079405003250280502548521010349070141d00c681050341403080035030b0081c442c1c0e500c3c80c05080906a1214000c00d11800840c81128680c014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 189908201 1250 189906951 189906953
    0xf05041511010204050d1a01050901061b060608030c0a030e0f012709090c0602060f04150c020f15090d0c05060a022206030614031b01180801020d02040f05030a 70
    0x28140300503030080c10100c0c0d20404250707039140a4812030300910f4000041c504060100030b0038911228456044040c0c041c000c1c3c0e220f00174010284401d01c500c3c1c0001d05084101d070100300b80c001942c020725029103008283c80392070380c0c41c40b07155031302c444112080783c0d01102c07402c024150700100b48800e28a08441c80c1181811800000300303074a140018050380501e109000032084085104480d004144c247e6050003011041c1c03c0603014000c0500c901d50150042400040a40341d0343d481040c8541d41c401540d416400754203004100811403525103000790b204145405640007020081803d154900c3d01500300d07180b0340f125041303081200d518510414040c01152207000280045041c0b54072041e0110700580303560501600ca99000340745031480c4444c0c2084400441c14540c0341d00400140c44041c0e010b080640060000d0540d1a08a1640112400e0810750f0744030b03481d0300c100ba040211809820180740b0580e161500c0d030342241d20001c200c0800d04c0d400981040820550040000104411405080c0d06076031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 189909451 1250 189908201 189908219
    0x2070f0f05120a0c090b090c0a0c0b1803070507080c01050304150f090602160204060501020c0d02041a060c01050601140a1d060f04080303040b0c0304030c1103030f0c0109030f0504 79
    0x941c0180391207400d14040500809000704115440a41c0040110343e02d00e5035100c120001b4000445150301902d400000207921000a5044400b82092542c5032840782c0c0080d01c80081940010b800c80c0c00c1c4c0c0003ea41d41c841681000c201805a19000d14043c000701498607080914000c500300c1c1950602109000304404213544207038805d4003a4106201003469420703d20910000c11900c20000c01c81440403403402c0c645030801d20b07103a01e80352003034a04004190301c0304010781e070b0b4881c040d095179031040030300b091500141030981291000d80c40f1464942a00006140001c0d600e410180380c52119039582d03010000c0c1582d0080c40100809146a1454074000c18040001c280030368104081d40d1122140e442c03e6656124502100c0f81c86854031f000f162100e8688917030a071254000d81d402d6401c400411f001c2081445004222800340382d01d03494024843d5a0795885048000032144216854001403101c4080009070800510340c007a9003c0000a0008003860040c080d5819502c02c4400c202051100303010181d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 189910701 1250 189909451 189909479
    0x303180a08030112030203091c060c020313091a030d020d020d05070b040605062209060b04060e010e07050c070314060f01140f060706020408010b130c02030a08040218090d02070f 78
    0x2141c96a1101134501d080603491442034006a076004410f18801700b8051075240c185a0000d44100400e00581c0843c41049071341e801104807118000112075020001100240c0c000c41c1c03001a2035000990f070414120000c1d0a28945a46038000350308030740340001170107030b042c4010300e0045200c0c00c08500300a2280c403042032800c00144001c00c1180d50f07602144240d640c2e20060134618203802d201050011461412502411440400311052800c08010344074030718041c0902019205030030580300c040c1e0b18007160724014070030241054040c000c04025001c40f0030403d0000001031070044a00c0300000301d40c03540e400e1070715030010411140a010385005201c100c002200104203454100c8400181d1900700d00010210f00c95180000c0c80301c2d10028000884041c10340042000d0340301240c400d19194510803003501074450b0700315034030010780013000341122603409601c117150440c1c0060064002100340c001c007062454001d5504503501c0d03002080306038819504028200c082d0181005844c081480c20401211080c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 189911951 1250 189910701 189910709
    0x601030f030c0f0b071121121b0f090f0103020903100c090815060a051c0206030a020d1508011109030c102610050604120b0411060c0303180a080301 65
    0x2100031441d481c1032090003a43e801d0744030340100750f9007078604011401900b002d0030440c60421500416142e840080300e80300e041c0700700700d030f018031060329100c2021804041140e0007040c040750303040c83d040e0003240e0306c1c00d220180450f400b00c0703071340d90b130b81e89003c2004c110403232042c41c800904250040048517115100401c1c0015800f50149000c40c8000c0e59640a4409584c141c12010091061034505150002044261806031600750340021006031201c05103c500c0500310b0039412207a951031014001030400000556000054800042c00c0c02c15414101054030041000c04450300081001400010700a21440e0400141080c4561902c48c0010100e030711100104106072042031100480001c05000341b101c1d0700c4a0a0050510414510410b000c001500050301c514400b00000704001c600c0e414088212020748040007200b042e40f00303050fa112945010000c0084504100b5003844019944a100240407c2c03241c1ea0042c60320391400d4078020f5525010b440340411641e00c44480c480c0890648801c5a05507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 189913201 1250 189911951 189911957
    0x1501050901030206090925030204091d0a110d200307060801051e0613060801080d030c050415090509070c020f04020406200c03071203030e12030106030902030106050a0905180601030f03 81
    0xb0380c7d15928421134000c1c95031100300f04488980075100006900d98010411b41324400c00401050040d044070303140c07001c2140c007404200e130720218040d0040b0768040c00401504000401580d080791960744d540300d01007420141860041e80c110507440c4149420300402c40500645d150200d031961601000401d1400c2c5001100c00501e4200707906c0c0030343c2d2200c104454180c0000b4424042040c3e803500014990300c0300b40328000e124041c02d844e07031400380c0c801c1c092521007610b1a59814203003410151010881c0c02c449140f80c040c080040d00020310b5455680c2e12512601c074030b0312040f802079032900600944010180b00d442c0305520400c07003403100030b1308800000d040d81185a02600c4a65481c0e03840343c034281040c88800d6152041c44000100d4121b0101000800c5100b503800340080b00c402105039681d2100641d180c18000030602c01845031900ca940001c07021400100041941c55540c404620f012107190040c00d900e075212420440b54140110180150b05410342c01400c5540c07447e1284440d80500100080c20 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 189914451 1250 189913201 189913219
    0xe09040c06030c05211801050606030703050c07051c09090e030f030705070f0602070201030b010c12080901110d0b01020d05181302040305012d150302090403180305150105090103020609 81
    0x464030031000d440c0110481080c103078603811140061714103c00112441c0c80c41c1d0119004000c0728840c1801041c0c00350001801090031034860010917005000001c0c845a40e5060501c12075012400c00c0201e20104480c0100c403840540303030110000d00382c00da00d4000c0700700a810702031301e5110090000101c0301c07109001100320b40c0fa600d030304400720303440d110710800600310074071070813410742400056801822100d01c01d803800c0050b8900c1d0340c01900c03244120300001d000450344184589030140504601030788600ea003400011400b049480c1c40080d41c03c0b03017400000080c0c4d200c483c4010f075601002081c503c440d0740e05107641800c400e6002d20140c0700c6071210880c059002e85401d4510642541c041d500916407100080c01007042e258081c6c01c111203a851030a080d0329540030340010b1104503200d46000280d4009401105504680a2260410001c2c1c42281000b65584d000007454000c0750400b0003851003480948403600d0880b20340a40e0f032034107070441403040c0808001080181d446000b140e1900d039087d512103031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 189915701 1250 189914451 189914471
    0x405060708131509060201050a14040f020301110a02160509010305070b07170d020a080f100608060612180d050a1d0d050111090a0b031b0c0c0a060c030e09040c0603 72
    0xc0c403003409901109200d00414061160150084c1402d000c3e1001c40d8000c02066595148210a8a0319400c0c80d01c0440b12440105001c01c90b41a210380300c2c1c1c2d0024002113000c40c0e0381c43c4402c425074400000e0701d006070000703c503da10740344000c9261030040c0b0040342d54400c0d80d411034a0f0152518914440c9a80030700000070780c8410071023212807131006a02a03c804a85034091100b44001940c4050004000079210000180007080c0c00c000c03190090003003100100d141401d25000b41e80d1114080c0050f50f01400074045243ea01449200c0030b40720381e030089422400501c0b060315852a0145000d80401404000d00c14002880c0d030018120200c003a10fa40400b0102c140c45000c80e01c2101d4105d00a000340d400d11100d50f1b03800b00703202d000b086094029504500855529403980c22980001e076646c507603452898414424074281c00c005080405586425181104001e50018031145455806040440c070030401c0358003419003000000d42c400f082519806c3d000c0c58507986908815843c2d005540c10301d80d5864040c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 189916951 1250 189915701 189915727
    0x41b18080105072a03050d0908070c03120f03021e09040f1d1207050c0922031e02010b01141308010203091006061d060a03090f0f1202030405060708 65
    0x400144640c00003042181826036004001003d802c0c0f600f00100480d80d281125046020301e00c22403603802d0b0359243e051620628070040942140322083da441c800c140308280220300c43e040b02c800194810401201014800300f409828010000c1d40342c81418410b10841800079044240307100d00e100c0040c00340d56101c20620000f00141100385451003081d19010104030800a02036800c035524000380100c8915940011003020203220f00c00740200a9006116030340e410b8107060607040c0e04403440600f04c812450b20081c040c4122080510140c000448041da40403054410854410032503256100030700140f190307000003801045a05800c02c000410000c0c00d0b210511007c04500e000d4100c4600079552810b0401d1410381d80c6001c60b1651071901d103000ba0006840d40109030084440c03d1624285801000c18002c115803a0481da41401c149a1035807d40e2002400c050000c50036148103030007540305a0102c0c1852000030049245c27410641d07104100070701c4242d40c1c203401d884d1402d41c41140310f0354440028080c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 189918201 1250 189916951 189916997
    0x6050c120a060f0807080c0f0f0d030206100506040e070e01030204050d053414030304030b0403051e160227040507150e010c1b03080c0703030e041b 65
    0x1810034089004180700c42620940c20500440316402c500300c2541d62261001905c0c2c0c10503106201c49944901120100d0f8104800000f03403ea8004245001c84d401040118140c4146480100c0058105070204021941103541000c041c1100340c40c0e8178100750805200420240d005020703441407113040c40114009138443e0301114040c00e000382014116002c185042e03a03940d030360796031a0804110380160207003c1c9004090403000300310020010031041c900e0500c20f0407071100c03c10a805e403d030004101c01300220390388150b80c0380030364801d507660b60f503409010049041004a1003484800d201007000407800d9403034100407003800d880c1c0407292407a17480f000c000358043d00313100c45074120020381d0301c0c800700b20a000c40414003604031043c0d070751f8920001d05000d8007114500500362905000c2034000c0c5541c000316480780d1480c484188004144182a51262030b400d501c0d41101c0290840d40c0d000800920405510801c5201c2001040d5401c0c02546208054048a0360480f080002040a00300565403154401d4140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 189919451 1250 189918201 189918217
    0x40f06061a070b06030a03020604020d0807050129010903150b0406090906050403091a0708031509010b1b0102041802070203031b0709050702030304020112022209091e08040306050c 79
    0x401803000050301c080428503000140290f81c04102034000440324200450400c0d04940e143e0b025115039562642001a0350130620300548003042c0030700c00344001030380910400f000110a0b40c041c640c280900d841055107403800850942c1041020201040050000c120a0000c91f03100d0101040c034000c180c0c0494000d124552000d0000f600b05004401070140d80e600440c01117000c1d80c0c95001c885c0d180c4500f0120b0003548840d450150303c0400c60103011544060103190080e030a15240c001e0030000302c3c0090301c5400281c0101800c843d00040c45240700b003480c441e0b0003591403010003e508081c60b2554100201020211580f4203035000250700c411540c00380115103480788641300d81e80380404800301c070700d07600c5d9503072f00420307400301e1808001c5880c445c000000d40c2d20440c4d059580034441c070b82440d080c1002c0e400c201079107031102203000b0344810700e00045606140a080b0602000641b60814180385a444481092108004a1007210700c1c01055140c400c0390300340c94003c2408070b4961142a0b583c00d030b9103d506c82e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 189920701 1250 189919451 189919469
    0x30910050f0f0105101b0303090f14061812090a18140f061e030118080d051003020d12051b01020918060f19050301050910051509040f0606 61
    0x200300141221003200041c010701c20003100c2c00c140da8072442031114070382104044c034004c0703000800c0710f82518000c050300342d600600c80d140c0450007c1190b65101e29424181004440301c001a40c002021044200015907200c68034400007030b4003601040c80300b5180e03100c1070500c00001000081d50182c035203402030703818010701480300c141c0c0c2c000030f805521000a1001e00c181c1c4070420034000110f14169901c4800f45d000e4400201206c91151000e0341a002c1188a1509181c05540380c1a07418080712521800c01e444500901e520350761000303044e095404865001340079030b01542c001241800075880d04d5004052440d4045c1c0d80d03c0c08040e5880054400f8000c48010b044500150218030701210411b4015040611060725840c03040210468000c0388210110341c02d64100303901074181d11182c5044825649004a40700a50010640b90390100b406d6400c00c680e8800207038441c2c0844401c120300c61194a0380704040d80c0190403000101400503902040290020300f1091038402040305001041d48480c00a0031448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 189921951 1250 189920701 189920711
    0x90f011202041d160207030c0e091002042c0103030c02060d020f0a0c140c060d090807051501050108070c120f050c1c020d0e0306041e20130c0e06030910 67
    0x1c1d880108056040381c44110401e0140d90140315139000007060002c1c0c99010b01003020250500d8408800064010101c0c0b00b14030031008800210356607031000304041c1c0b20070001415501111000d01c116604a0368080c0d4181d035544004002181e8480071107000d11b5411529181e5400300b4449103000b9002d0030003640f5003114009043d050300340d008005600f88922403100181d07001d481c48078194542d0320380854150044010400c070140052280c0c42440103d100f40d5a160402d02d1584945142101c06002942c0c3c800007100140459030700407134a0f0b5480155441c0403400b440b050f0b514a036641c1282510b1304103112816001066042c02281074425041c802d8007180e02d15440564800310009807401e80700054040c0c4107480e08454807e102c086d06881000c0c004040310b4075241d40d00100480084584142c18401c40e198400041d4041800140c0310518100380c004096194100101904020f07410612245061116005142c01500000385583c08540f10340d00da40d0345a034500c0c14a0700052150385010315107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 189923201 1250 189921951 189921989
    0x1501051909110d050117060414010212040803011403030703051815030a090b1303090320060c210903060a0c1206060306090e010204050a1206090b0103230102090f01120204 75
    0x4054400d0003503c46007804140d130307205005907500062003031400b07050b0031400000b0003090542e1943d1048800c0c8a00041c50204001041311843c2004da03400c0b03c2c40c02c400001000202c0d50040f074940c0700d0008502441c5413200668000d0a039210304111041c5210400145803895030342c0761020b04a49060000041c0d8900d0b003599048002c00c00c2945c00c1b5421108000801d107010007815501030110750585801074403d06540324040c18028105020300c41510070f10383c080b02c580b2158050100c4ca00d05e2401440b00b20701c0c0d0a298800380c00710380b0700f04003c00c5d428001000d0660700001c0480d008201840f00050001464030100c0d2420802c450b415010323421701c50001002941548075008854464100304140b0021829507400e0b4400ca120761580004491303003d0010416038075400615510903200010a1701c0c55036100c50304100268000e8606110400e05000310b0b01307d02034010300c0b10f02601c000b103240041c0038000a8844c8048154a410412600601d501002e0564119030281c5074a0710030070041004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 189924451 1250 189923201 189923231
    0xd0e03010b120a0c0f0609030312060f030c030b0f07080103021c0209070c2603040b10030204112d030106050703030e0604060b100503040503040e04031808070f081501051909 76
    0x24030088130491a44000080c4607002211100309440090380d800107168603545040300d0002078201c91483c2169140000984900401074440046100d00031b5641c81e14074505261211105c010910050400400e04106d5071a501c81d0740c0c5419254111009994282c0300442c003010242e4a90000750412031007c14450302c19000003480c4c008510400104034a0200140c8e90754100208a944819102c4180007280000715920100c940c00302040c5a101c6036195260002808c1d01c29080881128103000540e40040001844070b00d200040c0c50301100d1743e9580c0080001c00c50740300c14429803080020200c1d607481018800e03001a007022030a10121400c0d4105414005c0003490039030b800c06d104101c81c0c1c004884c214001c500380d902c1103030494007075801c040c035204c000d510304003004000b04c0402c0070810b0380c032200199030f0750b006d0041c3c00c44200501141c2e05005821110020b65004259150b008499065421058070f00c05815100c040d10711030200048800d2200700e0040a030800740d20343c1e081010f8a1102c0303403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 189925701 1250 189924451 189924463
    0xa0c0c0b01240c08030f091c05120105190608090102090a090f0b011b120c05030703030e060c040e0103120e0a0602060f071e14040906080c040b01020f0d0e03010b12 72
    0x15404564841c0300b14101810742c0c11428200f0b000f04024024800900c0240ca030708a42548003c0000035551410300032000c0c40d065041060a81d0089580411a680e4007a80313091130724058002584c0d012100d440d002a04a06190140708d10420843d0220028410070b40a4055400602c3c3c013500a100c96521503035058041d00d800340810f107100d0b03d019136080070756101e075034481c40c08a8020508041c80c66103488821560802c0407030103003030101c911242000981e08100410582e03000b55030000325200154480c038200100505510b00060040c0018014404d550788000d0459a011068030588008240169520b000c0d4040b0182e000144c1c20300064541c0d00811980d208890b28041d0214030741c0c540d04141c440f034180c1c0b82070b00541c81080541e202281c0c0101c2d25407149041c0d50311150f0400d17980307500c04015200580c10003207040c0c012500c20403d0f81890b02030303000768060074009031554414180d0310f035a80d0803007080d00c1400c01c140120600d015031020f43c000d60300c80901074941012503204401180e50780b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 189926951 1250 189925701 189925739
    0x90c08070f1d010e3402060a050f0105130f0b030703050709050a1103071209060e010e160305190f060207080307120b0303090d03170103030e010906020c090a0c0c0b01 73
    0x1401e8480100402d8031440c0b40c141d46032107082694586500030400c001411032841d05e846100180445842c44000c01107984d20030340140e00078403840c5031102c1a035040d998040c00c0c1c0d05e040704542005200c503a880900070380168242d160005440300160700204043c100344002182c040c01103030340110502034041041003c0d2011110188400c9e01e99503481d00407104c40000100042c40c043c000302d02003501c146000e1207840c2c4441000314698000f40c56081c2142e41c01801380e40240c1d0f540180d20075a40060140d42e15039190810b4507182140f42d074640035182c0c2400b41070542c0c03400804004904000504e8241b80701190010011910342400d441c0c002050340c000e8484101240d41a40d10082c080075a0240c200f1400c03024001e0340c00d001d240d90902050341309105088051107114040504001549212540214001d559241c450801e0b040050a01c500d203030044d41c1190040c040481080d154849203540100f803e4a00113071070b43d18043d08139814124014000c25a0781181c0000460180201c003e003814 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 189928057 1106 189926951 189926969
    0xd0809030c0405190c110a120c080a210c1220030f04020f010c0302190f14101a0108010506160206040306020c010c030c080406090c08070f 61
    0xd00c0d030460700092030003650384e00d02d004620a8020307034074803130b005003426110484404201178a0b04071310400601840d07842c2e880c02c000d0710320481655000d40d42103a020380d12a218040014101c01e180c140b0301d8649a41c140035866016035038420000000d00603207400e1a00400940144050300b0b0380c001c2e007450701d055800f1200991443c54011403040300100d41c0300349107240ca481086440750000d04003504010100d101c0f0700010350000340d0200e1040c1d1a24080c00840c6181c50030043c0d0ba182ea0000030440b8412080b6080100000118000340800345a0180300d080b440c103000c4006090a0311102c2d00140400c001000207042500040c2420310440d40014054a0300760041100d81d401940212110b6900107504c1424200a02c6419103d09491405004901032964020a403102c0640003400032a81d807405982040b014480a80040500005070b5800c0b6945225130301c40c1c04c60314480d0002c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 189748201 189928057 := by
  have h0 := BRFrame.cov_init 189748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 189748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 189748201 ≤ n) (h2 : n < 189928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
