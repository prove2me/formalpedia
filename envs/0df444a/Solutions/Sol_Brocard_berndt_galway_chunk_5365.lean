-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:03.258295+00:00
-- url     : https://prove2.me/submissions/c8b26274-4c04-49ba-8fe4-d57000255c06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 964748201 ≤ n < 964928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 964749451 1250 964748201 964748207
    0x50c030618070e13120807031104060e06160605071e0306240905040507230c0606010c030908060a051510050d020a0c0c08030307080a0c09030b1e0406020307 69
    0x10140c501265400040e0030401c22090214403441290303e010030300d0310140d07121101941c40d004041e40080c005420004c540f407425070481c2c591802203107507139010088811100303c0c1041a10540c0580c401050000a1050440c51316400500d0300b00d0756060f150071a03407400d641d14015070301d054911b140440c0c05003480078100c0d01e442c00d0303080c00202c0c64a400c1c0720300b03481d20303082c420220701c0710f10200300c2c000c03000003a0a40b00c1c2c011480c0300014080074204001c94581038000400010900890b040b80a001c05c410911a43e25a03090b03501345070355600605080d845030300054544486400080b01481844100040c2030401030020354454001804d02043c1c42c6000810381400c14164041030384208003001000220541c0841540d003103540325240140e40713510f01081550450308980006081000126000c500c103900030014500401d443e441c1d241e80c503180d100e103410540e00d649880c20005620315808002048074030384080c0e080309540702055411a07810002581d001ca040314103548054001050240c0254 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 964750701 1250 964749451 964749463
    0x3070c02011b030903020f030123060a3c081902100201090b010612020d051003050708030a0e060904180b091606140d0b030f06010e070504030b040f050f0a050c03 71
    0x1e100b01c00d020350000e65990107824404140006409100e458510211a803800d50000080c01040c0c01014949144044440a0b00d003040b94014001c03c10705600041403000b4240c00185460508204074071840100c0d50b0707000540c146d0038009140c87e0113280c0090942c10600003c002d4a0f03c1d2580d1402c5a102c0b4014000060350445000e401c580c0b5105615000c01c100700140c1e419030b40c2900e000030900140341581030181c00340140a62034549070109022440914022003c2200c1c45031040c1c0d00709960380d0310904c2d203a000ea541800702080c2078600c00d148520301403008000c4c0c120010400a00ca500081e04441c1c0c0034100c181c00ca541c140408140b2100103410040528681c13242404001135034200400204400911488002d9500340450414007074078443c1c0280702505800350840f031542c180c080c40f09039180b03401c1c0329060580d94600081002d00c2c4c40b0780200d42c141c980010040500d03442d15603640c401c0c182660070a81301405002007030344007200107029038800540507034020804036215508143c24a2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 964751951 1250 964750701 964750727
    0x90f0a050c0f0a030e01020c010c02070509070509060a0e06040e0c0d05010e07020d081302060a2c0607030c0f21030b0f180c0c061905090f06150d0803070c0201 70
    0x201c0600085020940c00800c0b90507000ca03500e000300f0b81294040c1190f019002e05681c00b01154200000810440d0780000c048049071011200c034282c9855011050312103200b01110b03183c110204002685005000c0c03110300500c550040e05092a0542c4c80802050344042a0307100900641e0018022204400c030303009044c0540140c0c500f031480341c204a00040e54620280154000780f112040024000040780c02e20f50b00c656070094a035035075480b18850f0003440031000c503808039151001c140f54001c1904450305210442003016001070301d0909a910241c0c2d6503c0e449030b0444110454140b0400094405c0c48007a5200440011981980c82c1c101e4001d0192030f4aa14200c0c01080c12058505180d940c404002c0160901c20124440544030b07591069100c1c070441f001c00343e40b80300d1082402020240040807402c0e02480600801003500c800090985903070241c010802b20ba44403501142c440c00d518148880007a5008094102c4c0e01442e0703903000029081110480040b0302003492602c03c2d56081846a40c101d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 964753201 1250 964751951 964751971
    0x301090b040c0e0f0307030501061e06090308043005010e070806100b34060b033d06120605010e04120806061b060709051801120f02090f0a05 62
    0x140c40c2d8640000c01c010303810b10702d5620641e10841070703241c507071070511510000d143c02000901c8032a8032000750f802c0d1402184070700014450241d02c0019014071901002007580c0d401131401703207081e10f801c1f0700c074440ca080c603015a40120989240c000e01c4195608200070940c0c8158004518a41d884000c0c41c00e02202e0340c0007080f260051810000f5000300407201c02c0a4682c0c120202c0d0b00c468201080c6211030110f50608110452205403251181406010074898648502d5003803140340c8440080c035440e0000c95640303050701c0001090300035103070210100310740c2103000d98090080036658190000c01030b54260b51100131400c03020599102030007614001c1d24050550288411b00c20304156071001a092540c000003010002001e01040481d9209001c4807070900070800e031510f094030306a00c40c0f41c541031b0680340341c00880c2001e1000906410b00c20460004810f440e0482c8110368a410022509004031303500c1141c0c91145980444016596040e209002e45409116100c2e24a000401074044403006440c0c2811 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 964754451 1250 964753201 964753211
    0x11040b0d05061807240c20040f0c0f03051f03030c0615080d051606050a23090a021c0204110d06051507020f0a03120c021c0308010312090b0a050301090b04 68
    0x11802020040074410745ca48240c046100b0003a103002c41d060600300100500e0310200c0d582d5142008182d0049400c1d0035001c0764200248031218083d54100d40800f902ca0b4041220b800d46602a680641d114644c40360706142902c2030201042c48480900b8181e410860119546007035031814840c0c90700c80c65a5403a0f0803560403024508210043e41c0d20f40140d4800000c00c980003400103c058031580341e041d401740d40540d007404541042075a41015000f140d00d14134240032602166602610a481114018940070700034081a1000fa02401285100211560529011110290016140c0380715079881803140300c1825460380c0b28580d200c2c1c241cad0307807907484648500c25600e2000c416050320001c44980590407100400304a80c28004140400c0856101500688400f0081d0341100c4c1c10094500d0124400c13101e0034092a60013449403603a80d00c1020240004d00c3c14001400052900d040080148009061410140c2e5a030200c02007a0750181c604100000c20100042042503094000c3c95042c0e0b00032241481 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 964755701 1250 964754451 964754459
    0xa32060105090402060f0c030a170601021204180b1905090106080402100f020a0f0501060510030510120201020a0b0702070e0a05190507030b190512030301030503040311040b0d05061807 81
    0xb038071240160002c0e01c0f03000300107a05401e000d142801c0f50551000e0a0a5940301e055585010703010098001d00740da01d401200001036019880403880d9400326062803041c40c206400c0082d101c0b041c1500d0142042d00f13545c0ca041d0610300c3d96400c002a4403442c207012030641a00d0601050044004041c0d000c0c0b030074070480c1014440143d5880030180841616441c002c40c01d00017a5400b240b0308440030b00050221082d41c10010103100043d08100706445043e5034a00ca44407448004400b281c100b16891414101012000e0058080d0740c110f40000302e00510458248010300c0e210504140419107111016a00c5078400300050540c8181265100f400d4110821061074006405c0301000106c804101100b0343e1080000c205030b000350b02900350541e001d80b643c60325203002c050030705440151340500d40c443c14400007486a04800002143d06890f07000014500f0715207560348002c0c494002400c49544251159844603068444020111a0501482c01000c203030610700d40e44511590319a843070b04243d4004100c140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 964756951 1250 964755701 964755709
    0x5040c0f0e040f021f170115021903021e210304030806091b0c060a0f06060207030f0614040807030e06130509180d05070606050303070f0f050a32060105 67
    0x5603115802c0143e1402445443c8001440301004e41020701100c001c466a0f0b0b24165440174900040c0280400316400c1e51f620b400174008401030400088005030703c040404404464440403103100d40340300b4011201119140d41d01005000c10000c0b950140390721041501444c80210410fa4100036503505d14680383d810142c4001306941c0004240324015400c1d00c02140300e041c845020055076181c0e4122030340e02c1c3e0320f80d550090344034503083d140c841149003031205000c0411381c1ca02c55141121070079002400c40030701c0c50742c804000c8242e81400362041c40e0303110071b01c2c02c28000030803000d4407603071141e64a6035490040303180240c500360002d882c0354010070060002a0f00c801e0002e00003c14bc5a00701ca10007455030b60b910a22601c00840806d14200d400f5881d0002d0181e5000406824010710030b503000d010560302c8006240d564050004090600903c2e25444030202c0c80401c15005402c6c0034105503010f140c815101c071508103170014040c540311f00c103098001c280a090034000a01c140b10600180c44a949000002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 964758201 1250 964756951 964756979
    0x506010905060310081207050105010e0f0f280905150f070e12010e060103030206072a051c0206010612020c0717030714070e07030b030a1401090b010905040c0f 70
    0x564040c100020200303c11134400da0f1401d009002801c2200d04099150240b20140d40001c80308654a60a0200104d4888110b101031481040a101c0000c8195518100aa051400a8000c5441c1c80305080000c00c0803a441c503241940030200c00002c103101741c5a01e056031820300ca80940c00700107900b08081c07180760503442d0034035600300c944c2e8646059103601460000c1d06d84520841d489580b5071030706d14941400700010441c076040b06d0182d0282c079041d5541b10703001d40780081c1e418451040528180010b4541c1c0040c00c0c014128240103c04441c02c9840d90035202c401c14280101000150b0b000c880104003a40e801192240f141075220700541c24401c500302d032a640c6554901501e1801a001001e212248200b00103072482c45410025000b58200e0303250485455081c42d000700d021111500002a24a45c000c1c0511004288082c005140060321034a40141b03840a04403400c0c6a5521118030380d01142200c40c5a6002c0c0046d220005158106490200b84000c1035038420b1550180520003000f00700615144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 964759451 1250 964758201 964758209
    0x21060409051506040b060d0c08090a050601030210300b1c02040c050715020304030e0a1d0a0f1109030c0111030a0804111c0b1f09150f060c0b070305060109 68
    0x90850303c0d2a44070003c0d000d040c0070301410f50004c1d40411102800e0702a5040341042c10744039120a4500d8403400d1442c0c0d1a180c80c080c01510390b0740114010001401c0c00e00320851307110720368588861030511152904211500300400000c03d0001289080081082c40c03060701d070803620031207054512910780c0d4000c206400c84181d02a100719502d031015190580110219407450381d008503444a081d420302042002074109541c2078000030403100c000c207041e0078400080815100050861444006a0544141c0b82000140103241c044d031185144020503810b0b0080b990400c00c9841c190b51240b85074400c0c5480c2c4040a900349040002061400710421004022910804000d00d00451966650306200c80344041000c0601d030085544110150050f8210b031a450030507203e444400c0858655950511940300c03035101106241d11408020041e655090b8000c0621081d0b5006000c0501c0c1d65011116816980b81d010202048d42c0138030302800c009031107020552041144c1420070017400c100c80024070500a07402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 964760701 1250 964759451 964759483
    0x1a090f101d060307050a29131d1f090504022101240b0a050304050c03150604150f0b0d0b0d050a020a060801120609030c05101e0204031104202106040905 67
    0x5040c1f610380001e0310440303c030140c2d0000000780b826030766510040f00e441e161000c1c0310201082d0000c180448950004441051407c1004461490400c1040401800094412a440281c114130109101001e2032514200c940303c0000190a0411320400b06040d048405600388200544a0620180d8062010390342e4804040ca4065103ea446140262503e840c00c83c0c1d4a62620440c0441c01115528188403446008251810711480c68401c043d060f0100c5940030f185420203068400b4041c0c400500050140200078410200e110800074002c10128500078100b52601c0e003181c000001541040314010008140d24545240e0a40c5082041394004514580043c5125250004e200c1818800c24841145541020a032003005440112420040c030f00c6900703107242c0700401011221701c01c2e0b4610903141202c0e0000c00035142c2c4042d030800c0000611046580300180300322010081303181c0c550000900520380c881541001c036402e40b0840500a0400100528031035820705500c032000550110b0161480b43c0128 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 964761951 1250 964760701 964760759
    0x1b1403030c060f060111011e0b12070302040f06170703060b060703020a0201050d0e0d020714040b010509060d0219030e010615121505100e041a090f101d060307050a 72
    0x80048031175030000c4445110660030411100c8042400580e4040360090b4a1001c000e0407209d2018004240750703d01105202c0e801034681000982401c2e0002c0090015200002480940780d4184442003c1d2071289103414cd4003070300702482000110310504840c1c600407621642407801a0350025078030008203078001d04000c000b041d003141180c21078024010b4034039038209458200d28a0700c8000d546601034443c030f07030040ca050400000681024400c054404006035a00340c41e10300d03c50203100d0960300104e840c0c40c0040d402c0103201d1204002410764241040a540c02003a05503c4480c0c90342502c00c25000541030f140c02c00080300384103822804880c0042041c0d800841c4801d55034605514801e01e551003030344c10941d401c214201132907011052441162044800304181e0380781c180b04142c0329451080858000c4614004545080007009040d940400700031003080b1030755210640088569021802111001900d909100f0249018000c5038098102928450038107454180c1c1085171824401c00748207991121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 964763201 1250 964761951 964761961
    0x31d100b040b1324031b0f0b0a03150506160308010e060913020307090c020a0510060e04021302040315090501050a0506031c030e0d021509071203050a0c1b1403030c060f 74
    0x4a0f00e84c41c1a00503201c800e0000c290f8074205050031800000c01185492042c020200da5400601809001da40461203580c0c1000c4464070300350005c015000b200d2410983c880c2000500340c0e10074000b4003140300440c28195040440c1c2ca030113011480181c100b8441c41c005802000481c0d198900d0096010029000e0840061b0f06400400d0404042d40c0059800b18100701440c805a9000180c04e050188202c0850b4600f141e454901c3c81114000d01039203d034960b055001c0341c05450301c1741c500317042401440c41c0180703065925516032500821110003241d43e26280c0c1140401e001e420321819500201001c014401454042c1c0040e4449010190907018054a04402102a4425032142640c80703102011140c01ca865210003964038010b096011541d0080c0b03c0004004040c081546c4e42182e9550007039840303000d190754041e581f5070400c10390170040104030303070140c801f080c151314400c0d20304d80100028602050600e501c00d80101f28002c2c01c00d010383d0042040c00f60390100060b6583c2c1c40400030911050395120 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 964764451 1250 964763201 964763231
    0x10e0a0f110a0605030714212d25020606012a08120112030804081804020316081f05130e061503071203080a0c031d100b040b13 56
    0x4501c154102280396008501907030000000e50054009407240c19070034200b0085a8550301c0303a6412007076000c08079910018801e513819080e0760054202071103240310300d800816a00c8102e000c1102442241c1c804820b10801000000c5400c1083c0c0c504816204508440e81000c0e540701c1c4043c1c44a030400c58280d08142e0425004200c540c0071440b0410030a00c0040a401e004074160400310b03116034082140000001c2e0000401020404c1030382c103444a00c0b481e503442e22070000e580c006001180c804440041c45004564543c0300071442800c80309c0030400020001c0c00000d00400d0000e141c11100021011075003030050700e1a290f9404c0750401c86007400354002000707481c1b015206401407440b1900ca02414042910301180254204103010b07400c42d21002c0d40e8440c1c0d403000d4a00c00d50050003140704103000c9120f0002941058203c0c8000d410b01081042c00c105a03101c40411411050389150000c1d51940b0840c00d40d40126070b40d120703086405200708104800043d03550341d01c10581c005240d0f5140c0100c0d4040310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 964765701 1250 964764451 964764473
    0x3010608030d05040605060f090415020d0c0f031b1202090a080d120b06030135060a1a0405101e09090f0203010b030a030e0d0c0e1512010e0a0f 63
    0x35005480d181d4446141e120058031003510112902030410000822609140e0800c070500d400c018500202516551500f5540d81c0c2202451001560200708407a0302852138083c04484043c07a6851112103150700300020211081d5034035403032090100c4000070b561991b200310300782d030800c820403001a0707120384010010f000d146050340220781c05e00a0032404c0b00c1d4260000d400e8200120525003d0141140000801440340b00074002c00c0460700300d840045c1403036800d065840c400c0381c0300d41c081c4000904076800e005207030060840c2c90915140e240c9042c80742003007180000c0340d685201503400740300702e081082c440c44000803640180810485110320306840b0303030b60451501004081d40d0764100040182c5003084032080300600003c0c1d01942c2061680100d07420002240c8802da074040e65030200c20300a520070481284504001911b9081e40702c80c0120380c019029003030602401220300a1034030030400e0350034403041c07050446885001c1e901d4040c8003900e405021801d280303115800021761450611074075001c01009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 964766951 1250 964765701 964765709
    0x5070b09040e010c0302091c0209070309300f0201061508092509060b030601210b060c0d0206100b071e080a1218080415050c0f011a040203010b1602030106 68
    0x140c02e2011309010950558014000140144d07130b0383c008058060312426500d1101c10700290009844000168410312070f61040352401c2c4550000514505180002c900c9600300c443c1d601904490b80302000501c039005500c20035000114002071210718504040788054030003840801c000c2c0454000000c000000c00c1c403222044807400303c400d00030b9800b2401c158060001c0783c0110400546003c1000c00d141604005032481244140c0da214204815144c41441c1c140343e0361085030600c1e8954503a815240d9039440501a404a0f08009010300d55013450024500000038010344c4c40e9001244090140d49644005c580300e554004a03241d4205c1c80610f03502244600e500c10142402801107400d1041d554001080071003804010014816450364090203501503621a00080040904100030441a8600c500712106035000b0305020b404c26240d0003869080101d07588003039280c1c0c0d5440c00851070f507141c000c0c0101081c00c0d05603030031403e642c1400342d4071540c0d22071401d800412040040c041821558250004c0003d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 964768201 1250 964766951 964766953
    0x302120307140d0210020423190b0903070f121e0804060206160f0e0409050705090c1c09080304020d020f0a0f21030509010c0c030507030305030a0507080405070b09040e 74
    0x2102c412621544485619003190014003032802940e00030f000c14005d441c00c0c0e0355019505904c5141100701103900c201c64440c02500f0001e080800c81c4032136094000c242c0103201e0300896944d140000c2c1c00b01030400c2c01d190080001004151010300c8010311007030141d0311050380b10305400c4450381d02050345205a10b8000c8020401e05000401080740c9502040c0c460003070107101100f58a8004203141690b070442c1c41e80880000032040c9240c2c250a240c5a0030010102c0e005d41c050f50b1082d922440480c007160811034001155420000c1d01c02e07000d41030101b0451894000e0b002c204150350b0280c0d00d20701c007840041c2010b480740c6220240312040d9600c45030201d40c4411b0050282c59803d645605400c0c519145128840d800003003035594512801e154801c281c00e99a166980c82d00d40b80c092001901c0e02c00c5100030070307648042c465002000040042041c4c1003d54080d890381e07034880c1b40032225442039602c010010f10070440c084050200042d0300240580036204445291500c680b0364001180050840305020507031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 964769451 1250 964768201 964768223
    0x9070512030409021c1a06220b04030c080d08070e220f0c2a060c02160f03110d020a03030e13020d09050f030f0d0525020c011806090302120307 63
    0x21a0040c0034407280716020040c01401601e80040211265240380c821071b9400002c10440c3e80301d03074000c1c044a0500e002c031511801500d035031580b55240c13140e007054004403180000d0311814882c010782008440801d4116150103202444d00726002854540125181400740e41e0174038848050a00b2607001c00e00d0400c0403e420031001104c2078000019114800003c0080b40203030f54070744440c030380911407d5400715641c0c0c00403052000fa9270300d110051051003d1402180105102906160140d100480080c85249030640006065060a81e80750100300111480340f0ad0000310000180c940c0150501101e8043c2041d50b42e4001d03040109002d0860b0501c41d2803064400152482c01c0c40b01a48250030150144c401c5504820070042116500e1060038240e90080c803003481072814904a40d04000c0d40501d00031240300c0c240c0070710240b20380780310300ea040044050b810980581d42e417035034403034009406075a1001c0309608040c58500c014102c01258080a80210b298a0400d290b0400420031680d1050348400301a034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 964770701 1250 964769451 964769467
    0xf0c08040c060201061410140c0102030103061103070f271712030915040c030803010801140702030f0403030e0a030b1303030e07150e1201180611030907051203040902 73
    0x10560844007110011400003012810510502c280c900b80c5000118548114441c5002c01012100c01e001c11001c12800d210300c0502c2503181400341815250500002d6100c1d4110300d010810b94038450341003503c01006004120466910030b9103603091450070300740043c07012100c0c5541c401e60545100034070003040d0000000142c000001042c40e01444400702540c3c02c1d2038406210318494841654050a01c3c3d0084074406580d060f2000d005800c24450190000c56a0b940c3d59600d0858109a0042c0c41c541d43d60b85000c03003084074001d0344990020540c8042d5192818030080d12859004600002d401c1103031568020085454940b44900a90303041070000e1a24604400700891110300420100c00182c1804854042487c0c009283d4041c3c2e82c40382c16150782c61310351800072624046c00d500700e1a401400401d85142e10316003885200303602010f0386400400d4885a04003070003a2070102c101603441e0300041040111140010a440c410781e0000c4404d084000c802119180c42c5010b6130700801e0b0303014800a00c0745 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 964771951 1250 964770701 964770707
    0x1e0409052109040b1c0210050405030607170612060c09040906020f0406180b0a030e10240509010b040b0703020f06100e010e060307060806030a050105010806010521120a030f0c 77
    0x1c2c800c108950610901104400b80b1400c00d20340c005403111451240400710051410750120a41c1c40054508181455502c01c0082c8c602501501c459011a44940380240520341ca00102544090107403414088581d0b000c0a065850400400003c1c81c1e51001c18028401e64454100d02c0050703030007440540d15034002d05410101c690140c4203000105041c02c4c3d030001034088980d5139000700e17905030920798100034210101350040c201c499040b1969002d2015903101d100081d103d00030b0304e21161030031800030b11100e600000203d02c0f1500002c1c0318071450b0740100858440e9004840070f0701d1404401f00d40314180c43c03905038900042c60301110594029400ac0100b5883e619031040100d1b0000e02c035007403299996010406c80041d06030741ea103030150005041440014051501c003034102c28090200c8500411070b844107801c485080e044600d0359080a00100142e140a80c0150f4a01162044400400c40121102c0d41e03102d0750400c00b10048030780850007614003800307039202c0005c1302e01c010414030116140060003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 964773201 1250 964771951 964771957
    0x80f01060806060307180c0e0d120908010e060112030203040f080d0e0d0206090d080c030d020d0e241017100606021b060903030706091209051e04090521 67
    0x703a8502d129000000303100e0314000a0b800100c4100c0b41039840b8213440400c00c500901800d05004081c006008244542601e03500b28103960b0301e00509004940318a030f0b1a0050141805030300c03281d0282c1c148142042d00c0d0f4004500241140e0001001e07980a0078246403d904501030b0354015400c03481c20784030011b4003440100f03d03080507001e1690750320040d08482c1c0801540c0d1180d03050107074104130140400c800c181441800c1e401e2483c0a00c0702a4180500c800c4801d01d541e12030704030281510b402103180c4890360341da0300940010940000103030a4044052060b108011030305004108026203410105280760401c0d06040c02402c0413802c001078a00c2c003001e01995845620138080902c91a0510000e00c0d20310224004500da0810314540d044c44122100300001c076045622070b0359041c0010428500060b105101d040c00e42445402c00740300c50280044090902460b9078805da019502001c8110342d103100c00ba03441c40905904681c0043c86940504025241c940b481c00010104540d105040110300b5101c00a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 964774451 1250 964773201 964773209
    0x11412010f11041e0b0703050a030b03010c030f1404020609090403030e0109030306171c0c0809090106090f080609060f040302010b030f0705151606092118050d0f0b10080f0106 77
    0x84803188044c1c290314088a4500d41c424544c4a2505014203030020344548000c221040170f034a0045141c2e00a03800203800c4030030440020001c01d9a421440754000400d0064104810072448072404606d40782d00440d041c0d11510300f855104551210000701014080c2d030141081020040003042440000e25015006140c1401508072105000100f03440a480001e52801d039400303481c13502c44000ba11108142c0e6400c01c2150200e9280009101e2603070607440f01164580203080c3c940e11040018600703000c105041401d500705001070380220b020400704443c00601c0581040034013220000c03a03661810100d004180b41c420040d0725000310040019030364030000c0d080c0269281210521114809154008003512a030215440c0c003c400050389808503906500c089280c030701030940c8204200143e100030003030b12000e180c2140811032140d509100c0000c0141100e0142a00b80c4d03188090f0714030340d10317658040c403007580004082d0180b400c002103500031900c1701c520050403c0021603c110003d040c0f441d01800a80c00b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 964775701 1250 964774451 964774469
    0x27080a030e0d03120e1002071209080f0a20040c080103060506010207030b0402091003080307020a120e180c042616060c0b040302010605060408010e060a0203011412010f1104 76
    0x340e038052918002601000c01603060301d07622803008100d03180c40045c1500c606014810b0181030031001c1203005030b0000704501441101c04d05101c90240002400e1a4229000136580368010303641c84d150b82000280142c5074a070481040005140540d081d500e42c07e02401c40707140c01c0b07401c002d040e100300d9070003c0800b0b050b24031030f0f1340502642e904c0000482e5207403074034030010340034030400f070b0200b03025041010155400001c0d185081000302e8407903d420381c450340b05807210380041e80039180c01c40c00e0140c210f51000101d0320514103118800100f1001480005884116102c0d400f0305401062201c2a010222002030008462008200ca50342441c0c80f88212400c03500025401991b90918413800048010030a40780c0c503440d1150340764401d44509200c80c0c0014412000e40d981d070500841e00d903507900007030320003803030507200120b511050b001009060000c082d03c018032080c010f10040c40921140c0c0f500c401032103020fa0707002d103441005109550240c166010f802844501e814041c1e00800c40c940010001d40d11686 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 964776951 1250 964775701 964775717
    0x204031a0910050c070b1b130f08011a131b0201020406030b030f032205032b110601140f151216050a03020706150e0901180c0627080a03 60
    0x1076440003d5803411550342c00303141420459400082c80b41e00c0110340160f02100c641d422404003181002d0907910000403500c04440c19002000486100800080a8420400240070003188100c540c0701c507105031004140f16100d20710b00c08541142a500602ca01c0089040380f509a810114001c0e000751311602a00002074101140399100b81070000b05200240700350001145004c2c0a980c090300c186c00100c46411740002d80541c000307019a02089060b0012a0b40d04880481c0e41d4014100032058080e6040c06003170000a40d410000007501090050440e0007110740203000300525000200350645069034258070140740f0300c1e04442e050310710001d8480003131188240c0106464462042c907410028440000000d0710800010195902c0303600a4100c05100d4880411010000881e0300503107a150b4000c050a034104600b00101c036a82406803c1d45910741100101c030501294881000c2424180226030504c41d040e80d0581c0ca2300445200090310850304441e8601090b200da0020b51100e000c00b0050b40021001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 964778201 1250 964776951 964776973
    0x7031115010306270807080a050c010f062c0106110f07080d140f0405040b0a0801020313020f040605010215090f03030114030d090e0f1b0706050609010b04060c0809040204031a09 78
    0x84005100302501700b0601800d10040360740307c0405074000740801c0b042107420710440c6840070003401070005003000c00c070340800d6072800c2140d5000c00b440ea00003080500240520f01910354031502e0315003415142c09213003a010203044422018501219090715900300d115200f00010741750401709080b52184102d940b2019003003401001654980603490424041c44805c0004008a25050740420010f030400340800b840e844d50f0380001c50880c0c1088808400c00c55101494408501c1d001191090703e43d000c50f003c001d0141000d000030760b103030141159040c00d40b00c1c800110313401c0103040000703c01c00e000d2181126601e40c1c42e8038125003100c3d070500e0061300900c11682450034a60041c840c83c8181c80142c211031450307503501d51120422880240105120801028804030322084400040513500d02500000c25542003880520000301c2d0168004540304c0702c280010b028003a070084c442540c46400002090b100e00b0202c0c000f42c0244580c0c0d03c014044030041c1c2c40b12200c0301d900810107110b010101e041e14040540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 964779451 1250 964778201 964778261
    0x1110703180e1015020a0204051512010c09090f06170a05070e220c030204050705040824040305071109040309440a0b09060f01140607031115010306 65
    0x2c1a580c00310b908000e40c006003e0380c0b01c0d6200800c110a07052044a45410b61600401c0c100c800c01d031000401c5140b01c0d01c4000c4070f0b083c038006412203102030074000c0100ea0110302c0d00602c04004d90081205c49900e0f041c0090094903039170420405002020b400441d80700340b0f0850155541d50b8250225102d00500700d000030340545030070105203e500c3c3c2808071300c2c54090504510000a02c0740508946005170b030507010016854510038907100c3d80c46615600c0ea56400d08032103a2034590b46503c0d28520300c1c42c07410614501651266155009a4541802d6865661600e00685080075001d0090381001703510040006240d80895080201c8005004c4800c9143c41c11542c05848440700301c0c008501d141d400c4c50980c80788141d0000e01c1000020200340e40f125a015078500c4414901550500c1d0145d01502c203020f2185003d40020340100300c4400041c1c0000b0f07881010075050300800d6405001d2140da9404540110740078006542c1d010859540c40400b580c607850b0140c002c2c0b000c60701415036216010b48072249400307 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 964780701 1250 964779451 964779479
    0xf09090f060f060702041d061b07020609041805010f140108010b03060606180301020d09050d090f0909020111060403030509010b01180902030a20040501020d03022502030111070318 79
    0x1c020740180704020399042840030343ea00520040360016520003a2200d62200c040244c480c051400c005020541085400e00c0c128100001380e00c0b0000c902001640010703a83c07801159200c210a441c0420030013080c5120380d1000c0e421100103003242d402c1c0401c11041c000c203a440b2580800007103c1d4594140d8130f9040c501d003250301c050040d40d0180d010380c01160f21490007401501c0c400c03420000311a9400300143c00310382641c020441340008692034400310010001e09210122842d003041c07801c80d0700b0038903054000c91410107502c114295565150301250959100d1400103410300740403801c41c0c041e820301c0d180040061030200c0b01802070754601000400315612900c0400b071100b40c90300c0140d10403424035007030070025070001d444072a405959894658201707507107440070001c0300750407030703040b92542d14002c0064207006c2079484a070201031042254844007003034440b14400101100f030807a40780d0225440403900620003402c41d04503a4a011911400301580709000c1c05030781c2820007184442c20f42d0b5400c0340408c49 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 964781951 1250 964780701 964780711
    0x8120f090a020f0619020f1b09040809010c0803040b0a200a08060d140d09080c280f231f0f0c02060307090509070c260408030f09090f 59
    0x50030000c41c100151400d0300320440c82c0034000300010b140403c01100001c0043c00440d4200150300022500015200d080c8091540c500221032114400c182c908009031019034001c000030815030b03005c07400100c0f907403044c0c10280340a54003e011030356030704141c10081c045071811900717040c480e8142482468a000407414455a40100b5400107090944030781050320562801400d00342c01005211511002c20402d0080d1140156000050440b2032417249000701500c030150809240c13a440044548800c0e1500d450082060300100c030b007029500c80e0055000043d4159501004194003c9400420132062081c142035401942c404100d035154441d800b0b010000111340c98200d0800078801e20a903600380141071030100200d0910b80100206d210764000342080c0c0045d290722001034a03000e0140300500340102283d401407800d0600d0702e01a89a0355540c3e07a03101d209001801801c2408034405000c001c41000e0f07901505000082e00d466070300d4404154007542200c07550380d10440070100030850100c3c00150441c014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 964783201 1250 964781951 964781953
    0x4150e0307290f0c0d090f05010f0e040507050406030f05040f06050417072001080f012312030309010c05040308090121090302070503060c0c0309100c0c0308120f09 72
    0x80d441e0400000d52210240e110803815200c40c03002a060340c06450052543c0b00602503016202c148103d0714170320b0710354084410010321200000c280911505192840101e400901c1c1c503544e2150000821101411295403c071740107424201800201078114010b40242c4200c3d40d4200400c420743e1030303440107503241540c02a01c0c00c21161380c44e00c04545d064108540c841d009041203090810110340145c0c05501c01030041c0c940303c2e002c3c441e04407282e050300f0350340341d0300e1400b46032801c204d09111144824101c010305c03c446031154810003c0032986074076a440702141074000e15540080700c290004503183e60044591240d030394644108498240d000c1c1041c0c0f41503a402030840307800e00c0302c05d20064a52074442d14200320768107003002060048004601031240b10350303c25406013101d640b9003410b0614040c006402c82c600101c080c08641c022010000566000c010100c45040c0d00c030704864825980300d4520803000d840c1403155000807050103600700041034103030481c1300305c03550f2662000710058040c2003d070344054003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 964784451 1250 964783201 964783213
    0xc01020609371509060609090803072f01021209120d1a12030a02010e1216020612160206070504051003023106142506020d060b04150e03 60
    0x105815025030601c1c6440b18005000c4080d15240c2c40e5682100004840480380c4590103002045490f002c1c400c0282102d9109209060280e50751101ca4000140075604010b030480030480b06006040b0f0600704207100c1d4081c18500c0100340c80c018081d61110380c00c0e0003441d1084002c41e481c64000140b450b201c13803200129a08080456070b0950141412009100c0310307211803882c40d447c5a6034020000c18040d9440029a0f40e62210a00a400e41e41300140e03451a40e00720740d40701d00c01c034034600e82264a03521400c4800301c02d800700d0f880011890f0050400340891100f0f1801003017a080e0066058002d801560b030211252607541c48401c45840c8260b0050070b810042428401084c02c0c020307005000c50740d9000c0070113a0a02170140086081881c071820b0281c82e8101c03544208012900911100d48203289070b040340c1c0c901502d07040c01e02c1c1551040c400102d0001c541c510444207000f51681a105004100076003031021565600c42d01c0c030150840e00907010116064410b0614003802400c5401e403554018010b098 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 964785701 1250 964784451 964784503
    0x309030c150703050309011e0c020d03090b15010215040c031a0903120703020c150106090b1608031f0608060108070305072304090e24040803010519170c01020609 71
    0x6a250001b5201031015901c03807007140540764031407031140340b10380161200144000444400900d0003a85880100a152402c02240c02040043c620940d00c05650300c03202c400303410813000403850030340308050f01d030002c81c81c3c20140000c008104200ca4205c0b801100d4900c0740b615401c1410b400700409441c5050035900802007401c002e420795502551001036420018182041001c9013800c10340c2000e0407401040c0a44018003000c2d03080001080075150580f002801d0800800c0c101510316904000076181010100004001f48905102c10703080c1c90103103004a003804d2340e80c80c014014000036101c2d58045407401001036601440303403044621aa800e0303074904205070000f403025404030341020201e10000d0340401000c5085416400707440c6500c03015030700800e607860303110014400c0b41003400d540f580000211801c0c00007003180d102c192030544008490b85a810000300ca0310f07440c040380304da200142c20078000c50702480d0300d40c002c2813512a1520a0702901d0007952804401c58aa402e0360000b10700003001074410350 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 964786951 1250 964785701 964785707
    0xb040c061b06320108010f0e0309090405010213030506090c0612180f0a050f0f0307150225111206100308031e0f0901380a170309030c150703 62
    0x3c10080c440000c02c035503c150f20040c0c01400700b00380c048596183c880d070041144400034030910f4014111600100004101d42196688910034042058403400c5403402180520500b981110b00207030001200320f501079034034502170b0740b585011204441d4074006c24080501c0c500780141115081c445040c114002607546203094900400b0035800051203202c1d20136004040c0c8801c000b0a010240a41c000700702030b040100d550b52509942040f1542d85800c1800714000191910041c01060300d8111000f6880e8581c86038032051a0380d400c11042e0f143c00c0e40103d1502880000352400c441d0a0040d540b94a068100c1100d4a54501060381d54a190804046041001ca10500c2c061034104142c1c0600d40b100d0040c0141040943c1d80030b582f0910f0400c050b0081c80090745092084821015401c007202c2450b40703000841c2501c1c100001c10500321a912a80c94801c0f40d074503041a24060042c0900700306910081d85009607480e0081c0c2c40e014043d00c1484045407070780c6481c00d000d03640b4242d07400c00c9510380f1105540172 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 964788201 1250 964786951 964786961
    0x70e0c03011502010f02030c090901080c01081902251b1401030c030e060a060e011509090506031015170c0904021002210d051608040615050d0b040c061b06 68
    0x303072046551765800701851961320f00040d80a0803008428940b01d00000c1d007007104801041c6d01c51003440e802051039079251f9800c10802d9070b2100704804003402c91850150302e035019101c1d140c400304032440700d11100d807164a100c00c50781000c940185c40d000301c0d00041c5450903207420b4450050180d040e0315040704200a41c8241c014400c0005d15160100d8085012840645001402e84503032902e10344990007480b00e00580001e81e80100801920202c1c030701c100b00c001030100400340c0242c220040c2c86800042e07140e1800c2004510042002504003c185011041084141d85c2c6000712129030041c0d02000060340300000c2c402240d0b00c0300410016050f03ca0b51b0030000039044880000d401d5002d01b51480a110078958180f652081c200f24880303030303590b101d80c030032804407070004004503550140e8078822071031031f64030810303c541c4581e00a40000e80b40c0030107280c2000255041d4007065100c0520212141088180080325000e86e1040706810346442c0c071800155000d060440b034481101c5840c0300c2c0e00c804202d103034102c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 964789451 1250 964788201 964788239
    0x30405070515160803041202120405103c02012918010e1906080a0b0916180e0105090318040f050705070b0106020d05040e04080c0109030c05070e0c0301 67
    0x50240f620040c031007040a031483d0080140c45485000c4200401d00c107011b8a03501a469080c405402d0301e0b4585507081445000b14051140100e58580e0705c0000302e40901c402803148240802c107000070305d0001c400003810360f160f60784030402c5020180c0c100300c001d40140100400300200034201030110038000d070400030000d000829564031800201070b4008000d074040740c4601920044080401078944150401d04100861072140b8545182c010200080200800c1848a103a4401031b035050603100d40300c2c01403600a0007a03044200501ca000c0010b0300042c49031215603030040d04141031017681804038149089030004ca42d52961508100651380503013441200048034001e0080c80020007003d800d592400b152002c4480c4008905c002450340e060100805a035030041215100418282c016810003c000d80164414a140f510b0360a002c5010008040260342004c00303488001c0005101c9410010b003d010002002c0d1200c0c014660041748207403000c2d80091180b40c007906001e01e103034070f4060300314020903620031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 964790701 1250 964789451 964789489
    0x61b05071403090d0510050105180103020d0312020307180504020403051e0f10050a050f06031e0a06051623040311040207060609050108160806061c0f03050307030c050304050705 78
    0x10010795130780b41c0c000c03640c0c6280150020b210483c10038103040100c88040c0c0085100d440b411118145009003185803505499060310300748000419441c0075203c22a00802656078103001104200b1400e50003800004541e401e0400740741c1103071340c40c01400200d104a0002400030f8005081d412480e1821841c1c20304001e00c5501103501c009010716105060030713044601080740030b03111010b000a2610500403650810200400e00380e2030300700080000d68420b006040d6640c500040c1000d0703036014100b8404000c0c40c64003d00c0074012440c0c0001d04030b01401d0b082d480c64020402c5d481c07800d144640c668001c5644c44c001034003554a807504540300d401c040640145401c2e4090703020000f1200041c600c3c0140002016445400310741c65041c00320032030401e500020101481d40005401f003103a8900000d026801000690718050130101c0d214088000d640b240d00c01800581c0d1152104c0700b0168080001c501c00c0c13180350350402450000c10030881d041e01c4140c5014045520092091015140c03000c02003c2c420010030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 964791951 1250 964790701 964790707
    0x230601050c1c0e0f090a05070c05030f040305060709120206310918020a0513021b06070e04050603060403082e0e070309020d170403020405090307061b05071403 70
    0x44001c2e2810680c40003424804100725280602e40390044411615264210307504034541388010045060404001c0c2010b80540c2c48a020501041c010500110201d41040c16241d80754034840240c022540700b4801101d507407159800091000b07102d5452202038038100c96002851081c0317178003041340540001249008080c203130305922410a10620b001c0318444031808442c07100c01d242907046e40459903220340140d48a6400605080180e5800c1d52002c282e840032584500c8110f071420340711000f80210030442425110004c00088010b03400103240e446154960390b030088101c10070043c030081e15011340d9115059800702001c90006070140710603680c8a90401141c0080d2000700c000d00010000744002d0348144c000901d4180f0134449107405c22580010581020320400000d54007180f0348007a001000b401048008000c0641c501c08801114020b6400810901ca81c0c10303c40e0405803260311115048452030f00e020701c007040d003031018060703040103540c3c9448060038040780380ca4041c101e9003482c9030111540030030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 964793201 1250 964791951 964791967
    0xa1d15011206062d0f1b06150e100501090b1c0612020111010c0c022116081506130b0409021816050c030a110c0909010b100323060105 59
    0x25100c0c02c0d00505580d511040c5483c4010700342e00000452007640d500300c102441d502140305401c03040e03000d141c2c981480c18265540c60b0f1003543c0007006040e04001d02c581d041c11480c0000c521815100300556200300c031480d6444d100c184020140b4440c2d40b05290200e81c3c140010880070300d814001e400c1032032030100240c041042400b032030b41c2112201c3e0003800f0382803540c2005200390b51707102c0740500324181e11000800404480c3c51000e402100d507540001c0c4185802c1e0f00b42c00c5400c4035056810090304000e03003142e184401100b0000c40d82683c2d400750780120710480078210f486940340c0d918a40034003009805c6401c03580e00c24400c000070f040901a065086511443c0460040c2ca424203d540041703418900f2170390350b09090081c00c00040d40c02c2884401c100042c001c01c0303007081c00070040344c81c103050909200e0200700d440d00c086410003861001c003651215030101001000705064014404001080380c07030203901d012000c0107400703c0d40c0854522102c0b0b646176004a80d0313651021903898010005041440c240050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 964794451 1250 964793201 964793237
    0x70204060f08011a0d1209171c0302031e0901020903120c1504080a18150306080d1b0627080a0305060a0b07060507051b0c0a1d1501 58
    0x8181e0100141038520041080001c41c203106440040d181140000c074000e011000145101756540720180c0a140c3c0f045006500900950b09000100041d00484101c00d00c94110a45c45210200c641c0502d5034030f82c07072141c44881c8a031088920400d003840c0c003010f1030000c0d06c2c090a911040141a494191341c2000a40c0441d0303000c03c1540f608012550006603100360044a01c0c0c02c01d03c01c11312001c440822301c42880005050300d401d40c1c0324104c47e4549426001100845c2921160032584031541140850f4013041565501d40c1001e0140c80140b000c440300e120014004a401c0c001003585002d480901082e41170015a1a4010114040080c2560a00040e0440101008520222040380d65000c00601a40002d07058042d595018404231f90002c17006107844c028050506c5490390040c6540d6179000082c2d80a40100251010b8155542c006141101c0302c0c54071035a01c003580603400b88114648940052230f00821102050311444000580780103444512120741c1030107622048078103010000b411000202c44d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 964795701 1250 964794451 964794461
    0x809070b0d0504110a0806040639021b0a2c070507060c030504031205090a1401020406030b150712090e0a230601020618030f030408030603251208070204 67
    0x1c011000140310f0a1038601500008000301e9102c0c041c00300100d0800c166200440c00b0b50788a40c03c00408a690b607040c060b40a12008541985000ca41e1481424010403944450b0320451300c0081d0203c9145181c50040c182010311454401039016042080c03d0003a04140e03031032200c2241281015040403070b18854000b44081048528100250f40469100e003809441d0107a602400703124103040126003402d4030010320b1802e50750a040882515100400c030184410000c000c6981d4010846c80717884200411524042d501c180300d4100000d04100c5174003041e02d0981c00c2d0507204011408510710304400c581e207108240c1c0035404240280078042c0c10000303840320500181445a80f03074610020b544100301c51103d501032825a80e20115611100812860381d0b00012819045552030b500c8076401014414a2803840c4508105844210700101c180010021020b0195000711012016103214000004008203a0007400c0c442c1001180c00c81010051400080032102e03409000c2c5032490b00e04455600882c0c1030312 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 964796951 1250 964795701 964795717
    0x118110609061e091504120b06030319030f200a0c0503120709030b0c071716080c010204050a150915030f090f020907090302240c1506030d03060b0a0809070b 69
    0x1540002d0450018500032180720480032045c09120304150610304100f00e150803a890081c20b50400300040790040e6010822360f1211048140b5014031045014001400b07444000411011942046100c030f0001031040785038202050295001418107218400480d106903124809840f9400308102c80c400070402ea03c0c602c3c0c0b01d09100e80b46c42e00d01e54914a8000d00d01c10b40103006042001c4144401c40000c5d0201d5180c41485800d040450b48a43c5080a41e20401e90100801820004002203010001206402801c1128002c84080e109030796184184203840307031968440400541c0402003800181d0b5030005403401801d4529002940d80c2c2c01c0c0c107110044070300aa0040e1150010403480c0d208515010124650022a41c500340f160b5038138681c0410101c0c03910980300c05e1004001c001410480f000c3c030007603944a1491070704031490304c00100303402d4482c0041511101e000340904207200179100d01a0080f4011548003000040c60b00304110300c115035951010300000c0c0d1078054002e0018808500002500e418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 964798201 1250 964796951 964797007
    0x10e03060f0f0c0c0303040201030924150503060c1b0a080403230115090905010f15030302070b0a0c062406020312130c030f151b02011811060906 64
    0x81e08002d00350704030100004001108200b01000006074180011054070f4006070b0a0038003051164161070425000001d03480d282c2c41c45055400e03074040001540e0007100034240601108503030503842c0ca0615072102c07400c9640d0207848000f0440c0f025a18108002d0340854111201135500d044c440e5592201e0a9200e58000d032004e080400902407081420500006544150360080015800c0426000d8124407a071055511055031141d200c01440300a4002040e1035404101c01c100a940c061140f07811200c05000540051183c07030000300c0c981c071f01c02c81100c3c03288007161a05612f10b11181e965401500300c580600f50894244403501c0740d40c201d00e0074103101601a030b402541d1620b04115030140b000400500c4419405040e04000c0041188224444266504002c0351511000e00d41400703810b8420301790780369010a1512000000000e408000c545200c000c80d4002d100842c20f40c600040300000c0c0d10f0020f0554001a80c010002d803a0000c004c09100303401528140c20003410490700300d402403146044040c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 964799451 1250 964798201 964798231
    0x504260d210507050c06131226010b070c0b090a0b0f0c1f0e031e1e0a0c12031a040b0f0a0f03020a1e051c0615260c0906010e0306 57
    0x1707966014003401e41e004038449506d560b909102e80b543c0900200001014091208814115140e00c8810401e64240c01400d441c070001d550352004501d00390342c804503055651b110315a001003103040c403120454124100c010910b00d456030900e22800e00c981d21030500003024800401060a03030310800e101184a1020007107410a40c2e4039810428010703a2010383d071507240342d04100310a15400803034608400303110303007410041030b01d82d691400c0e4040802200d40500380c4150010401104499001c0c100a01c00c9219a000c4502507403150b400707900351b1304c0014450482ca911505e100c3c40c0c03070805520010a507036000304071803d180b00d0380b0049113030b41e64150403807102c10504010038029400c10442c0361004141d0710301c8455003500400402c2080518a000346031207102030130501c005618440700413101d41270300404100840c1c0f48070304000300080701e5440ba1407200b0340a8104000d040c072591003508101c102501c05000150002820803a00000040045040c402c0f6641d0010041d10200981d41c4581c20300070071816 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 964800701 1250 964799451 964799467
    0x7081b0f0d0c050a0f06050f0714070308190807050a140d09050705030f0309031905030d0218040609060f1a041508180703020109060806150a0504260d21050705 70
    0xa481010350460a0380c00c5c07019004005207940101203464a50300c001030981c41d41500d203003048010406101100d002d2245180100034000c141005040e4440800e60014409404140c01d0310414000c40ea0384000c0350041c45a0b00d1041e01490300c8130103d080c8040001d00d840c04542d11101150342007032041c0d40759841210203002a040030042c48420304403e02c011410304000c0b00001e03541c1c0740d1820410622190207003580d000c01a041056070300388035002800b55260850b0950710640b910104a182e40314138240781300012158454810402070710300c0f07801540426030034600110111454000c611074528001c12002480d041c1c08441d074042c41c0c56070741d14040c050501141080c54100030031030300c0f10305400a00342040180c0e08000407401711106401c15901ca0342e28040094045050b140c107004203160005802411302c0d9001004009440d00104000780c0c012a500b107240d00d510b100100240c0d1a4000e080f2010914091040c1c1210800021284800100400f5101059810030b503020804502d020074001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 964801951 1250 964800701 964800709
    0x103060921020f06061804120905040513051b0a1401021c020f06150a182306010212130b0306190617010e15060d020909100906060207081b0f0d0c05 65
    0x1c0d0b0171060441d004241a00314000c244807010026100400301d104420a84440b0381c0113a510030014880203004201a1900b9004550450b8500c207048580e4060200d14110030004404100d0f83c10001400100c1401d08041030300c0910f01408500e00d043d445a031001c41c17030b8083e4a0f003a00f010030400d54050b1403d031265006040c07030408080c1a0802032910001c0300b900c96180c01101100302c079440760f070a1611001d01e08008005009000c41203000034541d802e01c2042030210801c89004020a80c225010f0660b0b0080c5e10080c0d00885503007401d206d46c00c8000b0001e21034090080c42c1c0020b002070140302c203540703064084000d44c003580d4481d02c041902c410742c46400390101c03003083d03006040d0004c882c1d055180201041c4109008240399510818001c1100c03c0c0c59075040c1e0640b92581d00150103140c5c182460348803c088076089100381004981849800310711280301048040841c0c80e2040101581d1103e5603c1a03020701f059882203030010191313031034186556221108408001e0052a05081d0306050000340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 964803201 1250 964801951 964801963
    0x50412081302151324050a2d021e1b0316241103071212020c010e010b030313063f0f0507050901140c1515010906080103060921020f 58
    0x40b0340354407002c005005c49907044134881344001501d051a070f940f0701070809a8020180c0c1c0d424950150307030421103204414800007078603004040c036001c480184100c404110710900c508a14900303603400080c0c2c042c0d5209400318991545083c01001e840c00c0306604680105041015801000e03420a050344060141800c80c1c9036403a225881d15100c1214890a01d00940d81d200300b03030b03005203d09084030091000d6482110b2010944c48149030540d07079403230744908403800f9003820306101c00d20b940790545d0412945400000c680140703602514140c200c0d41740c042d050f100c9158030844a060185601019182090341c0a40d5081e070702e82c070701e0b822803c00c0c1e071650030a0100d404c00c81000c800d00e442c00e01070002c0c498100c000d80d20307100024a0120900f41c06244505402d02402c07545036420721402c400f0003540b01ca048c43e040d2140001d400410700101000004441d22800c40c4144404900482c0061011070380642000680b14001c0111100c00219820340c440c40e4400c800c0311000503008410309120541d024869 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 964804451 1250 964803201 964803209
    0x50403051e07020a0b09040b0406090e01060905010312050a0c021c030e0409031d010e0a12021c0f06090f020901080601050a061701050105130305010203040c0512010504120813021513 80
    0x182a040038820790104e40d10080500411060100200e00031900350354640012079150381c098024007003e56a034000d2006442c0030b00041815509009002c1442c288510075241280d1308005210904030f00c0f0340098903280c3c00f28150000b0800c3d160713aa44050b8407200c05910700301c201c2500e0f50040352050b060043c50010007001c024440d034113140007080841d0748170703824030f8204681c1c4503551049801200142c8202d108075075225000040e079400054216020980600520b000741c9610745409003039440c250b0b40e11100b180013040c00302020404800300311a42e0120710031a00ca182c111401c2e80d11600050b0001c002680000a607600810050085040404500004200c281044100d4064803030348010b0b00c21050043c00c0c1008004078608440d030200c0400c0000031908030b0000c40d504d090509040c00c1e484880d0041c81d0164a40d00030314402010140310303807485181c001c4c01054103860441000c803003030700c0c001c3e018985610000807100b0140e5102e81d2034484144144903100d9692507001d1024010440c20b600c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 964805701 1250 964804451 964804507
    0x408042402100b0102071e060e0d0b010306050403050d051501022a09040204060320031b0306070309140d030515030c0303040b0c28110303310905040305 67
    0x240ca1150000307654000722560714404540c03c4504030040380b51410075441500d00140264150900111071481e54055401c1603884c1c603950700c0941c0902c60403015811009008100650040021480707607840150024440c1c90024604a078100c5107006491040e1590448802d000a10248940e010401c0d03800f0b00c040b101503c0010045440c582c021000022081c0b8041c080e543c0c0010119038a590005000c0c541c400140120b2440b1940800b84140c02045200d006c0e00c10808031050300b280407511b40c400a90001c000380000c0d52100c0e0100c010b4901c3c0c038401c0b40c0c01d4810744110409000d040c13006240071101c80d540026030381703455401e0684604030f040e03699000e5000400a130b445502c02000b00d4041d15901c481980c0e90b200d1001c411444d205040121070402070808624142c0340c1c0710700c2c08008000340107120b402c000380c83e21030030192240701d10040d40c01703c40420004103500c002010000b118860882000c02461130303450303038a0401e0300c1c8112021000036000280c6241c2c4580c0c1c4800103100801600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 964806951 1250 964805701 964805759
    0xc0105100504062318010602060415141801060e0a0c12090b1303020703060c080604051f1404060504090b06031207030e01030f0b0d03020d0212090f061e03040804 71
    0x12101c244501350850b1607185000750200503928a484012214442c001520303040403040da50745100039101c00017034130202c0d03034114410301103e00d0250502841c0c80d218210f0f6828800c81d103c001540c2c8041c56004d00c503030500d5480e0000003030561800841035100d030a1459000c01e020000306801004040e140301b0324041da518040e101008150240d075926070202500361000c504210b24281a8500703402507100070112424004104d44c50359004045502a00c4251010f02103070300c4110804504081e601c0d40104a4140c1c0c01e4200000c441e1015031074040c1e1006400020b00ca520b030400b1031b06a4036901030a07200441c3c404140021806c0410003280320058040b440c0341080e40c0740d5001013040e812600c05904141c0c4641903c84070200e01d5000310503500006103810480d181c41d18000e51640350026040015000c0d40400c407401340d01d24001c40721214001012607070407905810402c001504080c400f040d012000c2c00c0a802802080c900850150b801204440c0d1501d01d0b00341e298001c41c40340c4401094051401d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 964808201 1250 964806951 964806959
    0xc1b0106030f03031508010609090618050606100c21090e010e041506080f0a12020f0c0415080f070503060705040308093303010f150903030f03020f0c010510050406 72
    0x240b03200d00300a651520300850707111400341d0114030340340040d084401c05520b403a0340040d00004580c402e00c1c0c401d201315070920020241c43d00b00310106c7c4034140081c1003074011800003103403032030040600c4402c45460f0414508a000540700c100c40c000c03800c5420380320700c86401c41c105480380d0421000b90042454050b00c07061503052a82d41111380c600a8401001d58034002001000001150810703805001c45130200d48030010307181c1110756608403401c02912071850b1482f001d40300758400b0807400f501440319070041607022031580c2400014100501c1084030f4861903140820401402e01070342c81e82c030744000c00500381c940c184810103080040c050031000901c442040100b00065840d400c0c6d5000901c22103424500c0702550444200c8254451076180040030103a5117452000250006581a21112a03050340020740b10000000e030300252075020400703d149070100f000082e20440034811160203910740582800110070082240790040c1d440681107946078400c2081c80690321400300000d0034125410700c0150302d8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 964809451 1250 964808201 964808213
    0x403142b060b0a050a030f090b0601120b0d020d050a051f0e010c0e040c090504050712110c19050c090a06030b09062a1209060402090a020c0d0c02010c0501050c1b010603 74
    0x4203c00c04043c8480841c01c0d030764041c020b034051020180414000e10040740c21f46072100045101700d40042c0826000100c400450340c01b4841c14500d024040c041080703402d001d8080141083c1d0301e2804888611650711803000142050110b1031600c2003e2407200440c00043e14107506a4000b4040b07841240e04d0115900d200c00e80c4041d1043c00000151000290400c00a104480901c0c2c240c10050308103003000b0074002080e038031907400100f03907036802070400c0101c4100d500d0180910481c0030221131907009040d2101415521458a4003903881075080b02e564007040c1c400b10f041e0384c0c0c0468841200d9591050204184204a40751030f601103040700140c00c443c502400314000b0340c08003401062801080d203028281289518080714199401c1c41c0500c0341700d140600c00150350700740848089004815a00103c1c4040c1118000d0704c80c07184000d00600014080060708403400e1041903001d9040028480b60180405e41c28461316000f0920505142d56415281124a414200100c241413007603160620400c00310b60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 964810701 1250 964809451 964809457
    0xd020a030e180126060c0a05131805060a1e090c120204150f170c03270a11060702010206041b0302030d050901030b0a08060a050403142b060b 62
    0x581800c2090707640100c140826040d104880c000400326500d440003103001401c940801d007442d0322079100c0c0b602d0109402c44c0152980010749108207855004d01c0b840b00140e00502c00b404007242c0864040c03c802e6a0340580425080000c2030301c0800547e41c10901945051440b4140e0203004024994100382e20460403144407140288035030b80c805a23448911404d610f1041d407401c4d4155080d403000355100c90700e508a290300e140300e17012540003103035060f1008070b001401030801010001d501012120345030b9581900d0401030744010443c007080d040111141c0d07400101c80003000c9951030114000c0c020050b144ca0409074160000104a103c2c1206010000040c1ea0002e409980305511002030303165041c0c9056940b20080740c5400080d0306001d102c007802d050b107038020b01516041e4400d070f07001d01a16001c0d405000d0f601d010f03400b80e00e40f00e07080840096080c5245410060f0828403914000c9480045a1b40151043d0002d4100808140c62441c1040300703580c80c0c1c03c81340a234141291042117854580360035820144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 964811951 1250 964810701 964810703
    0x303280b1011010f11030f15150a09090f20190c140708150c040510030b190b121b03040b0c0909010b12101a09061b030909090d020a 58
    0x111102032418400b440c01c1d00203183d41549404240305c0c041c0211401400e640003140d4042042d41504001900f0f055540081755205502801100c903031488055002510b510024280d42889452a80054180381c248202001c542e410080002c04501d100305148034403c20852100404c0014804155030420ba0250307080000e01c45d040c0070350509001d00e000210360500880240c01c900506030005180400410344503618918480c2e040020303554801001c40602690050755041886800e000e10118081ea20500303d0f1000100010301d04510049002d104055542142c01034840c0443c0a000003c04030700040e8200094001e502c00c100020751500e0b40902004202034040b2071620040303001081e4030012038400b03641c040c05113043c07986c40e42081c040e143e000315109403450051200040410030001402826220300ca290b00181c00a080503915880d0440ea15803648564108840c41c4885000300031603007000a0403010b144c5440e070300d1041084e40000104440c4280c0c104c03002e90103080f40d001c6400d5000d0307 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 964813201 1250 964811951 964811957
    0x504240909050106030512120a0606080a020f0913231902090d05030a0c0317040f060b0102011107110102010c0c0506010e0411030a1a010f0612020702010e030303280b10 74
    0x1d003001d0070082e001d01501c2c1d00150850180b904040300703600c040d034000c220f450f10003600386c1ca039616140b0700348049403070703501c641c2002507910f80c003007000804540c004180504c040c507110b604203130341c0e0400120707a102c0d08100003180345d82d00d445040321604c0c0c0350625440d0b45000b000c90040b81c50881c04407031a144002c10141003e6600150802d095510070283d88802da0300501202d4a403941d07030740c014022419062040e40855284500c9a44034580914000e10841e40190303c7c969801403540c0e003501400c0685502c60555480b042c02e211900241780c050803074540a409200042d40c541c0c000a070031113507046403503410450014010070219800049460444841251100300303039807a070424011540440ca42d250745805000903180900840c00b80051140150100a100da0707680e0b880c4041d141500e9200c0c14011070392003a034045450f2840d07805004414018140300c40d405803003000207030440c5d00490300c90310924064030280090720a4000e01002d1801da40c00100710242070383e400201042c4ca0751000d0410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 964814451 1250 964813201 964813211
    0x20d02071a070b0406090203010b0409050a020909073501090309060804020f06030408030901050c0310030b04021915090906361802090c030106090308130e07050405042409 75
    0x1d4501050880300d1450b080754943d03881e410203142ca00301030304c40c00800380e02c2903080c954101c2161030b0912814100e2a0b01070300424513166160700b4441c080c84000c0100e40d90340551240050b18240c07100c00624100314106500031f4090403095100008041180451010b0b85040f0300500002e800c54a900141e4103c0d042000180c0d40394800101c90307920144001c0d401400c00300034481000702e030304051401801400000d00480d130321418881164001100c1003080166400410800300d9480c1d0121030700980060b218071000d1403000a5407002d002d0960100d40481152964036400b15400b000d600d01400308000d0501c0154508082c81d14050b110000c260204601d00100964000250a0100b441c003c040e5050020130310b1421240400da41e10081640140c6112001800002141b4101da06a4140703403980d54136141142c595144640110060b000780301034100000c5008460010f056118988559903140d50b6400e000510040e19a0010303801107054581d056101c0031011041c800c1d081c0c4900801c0007030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 964815701 1250 964814451 964814489
    0x12011103040803100807141309021e0307030602030403050918060604090b0102031c02090109060c05060c0c0a1a0714070c0510120e010f050112050c040903120e07050102010c020d0207 80
    0x100013652503114000521a00b60006002a406c030340c2c004401c06c00b1502d000c10010086805001d88411010080d800500c0c81500b00303135140c2c2d8020892000502600315001c02d03843c0d90307626049078400d560903804244085040420381c03070420008100c11010981614460070520041a501c2c0618091100c4254540e900385695910030029142a01440c074085007840b840544294001c1d8465945180060200040425410700450601c241680e202e00107195555802c00c8040302900080d400301d0701c90150681e6000402e80018100109142004410301642400358020b4010421003564002a460922414011815500341c090031181d0541d01075043d4006c032081110342c1618400c07441c07242890700c038640e107498605500107404184070300da04001c9641c0701d000015800d05c5a08001b0183d5001c064041d40506058001101040c4242080c030a03076800e81e0082401c1e6400c105a44102d5481100200515079090003030740400c2c50103001608541242c100d00079200d84e81c6d070050680c0c034500910b03000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 964816951 1250 964815701 964815721
    0x40e040f17071218210c03020a0f05180c0910020708030d1a040e0d030f0b040f1b030e0703030c050a08131a09130b181512011103040803 60
    0x80001889600d10b6a4014910300210b0480d8a0149900020100a10074503a0064410031005807071002c0d0b1032144020400707110a01c140b082c5001207071240780701080040186c8544100c50050300355803071070000b81c60520041c000c40c1d10100c07400190051101003482401505501241c80060302a030301548190281d00c0181d10b00f003c40c0c0d0010f000341c0b1001810560045c400e0784103480c0c8882d545402220545060b00700400c0e1440092001c07415081103079040c0c1e100d40a0750048001035200390002c42e010008134002022240d4014031904941d0715034070b01558004c002002507118071560708080195011074101c465a54032980030040501c65691401000c5c40810000000303103aa002c500c2c4c80c1c0d11289000e5061030b4580f181324007080d10303007801401c2c2c60f424000070642e1007050001d0444200e5010001085014200c540c03440c0d80c020755845058042c044580320102c0c442c0c615250348101d80350800c0203200c400c3c0010001044540d251007019800103180c1011603406ca50408243da860f034650700b90341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 964818201 1250 964816951 964816973
    0x180302060a0c05100c110307022b08070f0506060a0e16120213051002070e0f070c06090305030114190b091c0b190b01020a08130b0d0212060105040e040f 67
    0x243c00c0f4401c0c840e10081d80c014503000b0064000c2e1039503403610307032240710403000c0d543c1d000f003880003544250340c0c100962191401d1200094100714810107840040d0458807859908c2e84030b18130540da1200d4011060050003410032400e5003019041c0c40003008686440300307821903010090066407060707a54441c0000744078410241c0045080000784210341d0b034000c411b508500019684501c60281c07070b1000e2480d800c1c500110304041110000041143c46a90b1030000044481c0c0041c1171000f170018800340300022508501c210310b0440c0c42512055501d5051034002c80e00d10000020062082c89641e08506801e000c00010000f10342e20341000d1a103e02c800b02c0018800c40c01a0038214407508106c20f00303018082030340203031802046054076180711885000406e0b41900d4511300402c3c0542d01059036100081c5100c4020400884444e030903940c11074441d02440c1055000c9004400d10390f40216041041840c0400d4180e0400c400342405454a864500790703503203102005001500750407a0380c9000b01448084510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 964819451 1250 964818201 964818203
    0x2031b06090a0f0302016206012c06030411030a08190309052d030d0605120d12020d110d0507110d091e15020f01050601180302060a0c 59
    0x1a00c500030b40f1550180f21443e06844164009036000603001c62440d11052a1116155012503501d60400010a500403050110540c1c1410410754050065201c0c01c0e54400007014000203100011400c14100041c541100640c5004c01c6d0f2003485600d40700d000c606000070241c1e84054904a40340e81c2c41d07080003800040c00250070b6815000c0e01c0c010b00f0400603502c004050340c000c103440240c103205900700100c1c1250040c1c800140142e014010000d51001442c1032419851028000a0008000f402080d03007150410310103000c4c0141c481c4014012803500341d0b000da00762441e04000740310b01140c1102c000c052014078400744910726400114158090b1060308001c0c002110304003419650b91368480000024401190035000040c880a0810204032011402801910080e03650050b818100124480f02a40115110709e80d540a0440051b80caa094116001c2c840d404d50090400e2440c070001c03407800d55a00400b10360400080c22041c60f1351540340230601d0140c0e501960407a0b1500740c150703415034400c190804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 964820701 1250 964819451 964819459
    0x70308100911121e1302120712020112020703020d2003162003100b0d050a0b0f0106033b010f1b0e1f09210b0702060402031b0609 57
    0x11554050304000c000519080400c843d8841c0310b40e03504940300030041d444020500320a41c030400802c0085c900240748940d02400100401c504080c0344a500d4076098465006120303802c81242044155a001050034090740d41c1c55405503c1c0c05416a0000e40b610401e036540030a00695104034140d44c4820a4800084100e80007100d40c3c58425070030422013441181e1040f100314400f800207070000035014460070b031360301c00160050180c0400c8200d10310160544d010102d8000d038a410514010480401c9200c854030301543d506907041c05d241d41017414008050b0019021302d42041c2c0600c0620740c840311400c200300c12a4202d580316260040900c403403000c184040c05019030030a548034202060550180208c002c01480c0c00400c0842c8403801d03141c0f06684210568001060003d08101005205c0145450319151074440a91904c0314049034ac0341740028008051024a01203075010821181c015a40202142c001840946031507400280e075100d540040007903401c1180e000c5110f5480b0b4909490f19060020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 964821951 1250 964820701 964820711
    0xc030c0510020316020f06040303021c090807022b0b0a09061e0c09030b06060d02040e090a020a17060402040e1006032f010813020303040e0a020306240703081009 71
    0x1003010041c0d002138540022420071003a4110043e4000142e950003400c866000d84125912500e05400a4000d5129607a120200f035070f0200f14030005100781c04c08584500c1305280c031401c1c680107104a04030f201484070154441040c1410000e0041c40a030043c00d0f5028124504075a20f00d000d120241c404400b0040c441410445118009002920009410300320288104040803120000300d0b00150284800b8050400c414040341c0e060800100601c284c00c4203010141c40c2c40e65172112445640822035004141d504000c01d14000c511b03250840700020103041d481c506136049800c03070700b54a51401070802407249039209032190005505200008104004da1001c00180f0b640b800c0c138000640e04500c107400c40802c6540c00c0514032240894180d5004011b83d42c0400c280c1d5801e040180d4043e1145050b40c4c544002c0c00009040706920680307500c902c24090000d6100e04200c401d121440c81c19800b810016130515044a0511f40c40d901503a49694251904135126203409200d00c008060540002800a00300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 964823201 1250 964821951 964821973
    0xc1205030d0218010e0108150909011b0207031a0c030a05063006010815070c17131e03032c060406030e0714010c0b1f080714041b0c030c05 61
    0x42c100f0201050003078071800c1d0f5500c64800110740c44032013203070044100b40407621030000d1410011507299000d2440000000c040e0f104041000c8403200a01d0224010303801280c080c400c00400e0742c1c418051907518900d450041c140002108041c1c0001030000700e9495444000070311079601d01051031081071180e8413012084d21007501038101101004181d0000e4800ca06c00010031100c0011207016030070001c500c0d05003640b19990101d8140c0120102521900408002c034203140d0754010062000d410039410000c1c901e840c2190307002490079081340507900c00b0980e52082001c6074010340390628058650038001c0c504403150b44200e0101c1c03882038500b500a00c020a000c525a81c265000c5a180896a8100c031400da80c1d980392500c070702c004000310900041d0707131640310340028040c1c100702c039044044a00300c1c9034101550110b08802c00581c2d8041c200701e5000d2241040306401515080c3d628140503682400607503aa40c101d510811020041d0f40204065962041c3c2030510500015501a43c01800c0d22600c4a003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 964824451 1250 964823201 964823227
    0x20118030b01090c080f04080304030c0803071e020607080103240501080d0905150d05041509051b0406060816020a02060d0203060109150c15020903250e040c1205030d02 74
    0xb4043d0244007450034592201560140710f0b0700b4400c4080900c482d01d250b90307980d0b40d00210381001c2c5c02102405641d40b0300d5030006072584081c44c8a02440e550300000700000702d1a00d07500064194448041d9000241405480c0340d2040145055a41020501000414649408401c80752044c04413072154600384c00030a251501240201c0d65400640d10b442900f5201d004000350300c05049148254440c00b0851703295007045030307003020303034800d000384400103144050b10088020303503d462008840d5500100f22840307491070141e0180c2403006098804000140c205480901010b1014228116488207040c40050740c41c803c004ca401d0742030780034110760344407040c0c0001c10300a07420036900c290104113811000311714a080300884030303440342ca1940c1d180c124283d00e0f218168040782802042d80d00701c3c0c0801c102203541d1820080120300c818000c011000600e00094850f038a0032458106452950740b42081c8408542c40707500e107109803588514140780c0444949040c6180d40310707501c140e0a81500128000d040301074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 964825701 1250 964824451 964824473
    0x1009021507080403140d091509170610060801080c0d050a1a0f070e060304021309020a060f020601140102120a12060f0312020d09090903121a0a0914060d02011803 71
    0x1200702c0e4540c245c0c0c0c0c5070b9400340c0e44405420a41100081d101c103010415294054256010508242003543c1c1842c1c40d000d802e07403465860700141046a1048082c411000d041c420580000c0116150058113941000102520f42d840340007840d00c1034000e03141c500e092003014000d0303c01c072540c8003443d040c00e60407580ca0101c100c4ca0456030016070800c0d1900084c81a80901383c0380900c4c600040c8110702d1552180d003004581d0014101c040003195494100800680300d02902c00c2c090325464403a0780c11b505001e1002032034298142c0003080b07140001c610103542640c0000b95510744000400050b5103401c4440c000301c6200035810481001e440c2081130010322461029203280549000f0354400203942c852640590740c41050210620005003600410001c2e106d456000e04801486860002241e108001c0c2d0030080d078101c2440c5000d15440321a112030a4500450030100510161900b0700428501c8031503140003140040c030075400346c800d1784441c008581c800c001001e554010040c440c5061a281d040c1200500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 964826951 1250 964825701 964825703
    0xc070c0b19110318040905030c100506042d0509030d051e070f080114010201231e13060b01140703032c030d0b0402120708271009021507080403 63
    0x921410108485002c01104840107015045100c551050320b000510009200d40001503a16000500c500d184040050041c4800c49585007130202d210b04102c4200803c403409a4140001d09141086101a00000c405080c02c40700a03542c0c0007034503075640d0f01140c2c1140305a00b0002c0005141608101403500000b40c04411003100000c8140035580390081902c6030081d010412003c140c1e0480108030382c2418070082c850390710317042c07002003045000d420341d050580e402030f000e10b410700d406881003149510440c60030103211004000c3d600340c24141040440400074600d0300c041c180c1c585503454081c540e40900c410200301181451201e1f0b44070303401e00b801001010003441c002c582c100c13241da082c50241000080284000d901c103000d189030403034480c1030000500c40056010f4000d034084c007041c80da6058102d10188a9111500d40400c0c40c90b2545002640068990044e00010303c0258184107400c400107200c4440c0c500440005503d900d5400004e5040181691315072540310f00140348010441e015000d08112 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 964828201 1250 964826951 964826957
    0x40f0605010b030c03060d080c0a0c09230f04030e0a08030304050c060406050d02031e04121704080306010309050a02061c0f02071a07050d1419050108060c070c0b19 72
    0x141d0325180003140c90b210945001c403a07004c040c0302080032450103c0407030b10144c0c4070320901031900c1102c00010b401e00005400988042525a10070042d89140d030044095540000103090390038082c02e00608081400a400700c5803650305540060b04250061040c42903042d00104240c4586581c0c42c01a03603254021141112180a1024005401d04101c02a035060b941c0319191541406030112a0030000e42009218081a0030300c06180d481c0140da004072a8019030050b01c1001023408038500260002c001804902482060350003080046040c010583c1e820440901c0c010545035100d0500514000d0080c0010707502500c0024154107428a510109003905d90210b01841400c0c108814030080303004900740507003400c41800800720309500c0070840c503500868505010341444201a1164200c64500090342020001c0c0070500c610009030010030360480d1500782c41409030317604141101c0d440341400382c0410345000300440e500003001074840b401005400d81480c0691100700c6010540406a51200d010003c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 964829451 1250 964828201 964828211
    0x501050a0c140a0b090d0f081315020a020c03060108120d020f1e0301051215010603020a18152d05092206290301060e04020f0316091205060a0207030512040f06 70
    0x45001f002c1503403c060243d2244111552004221054107041c903c0c203c941d020500070303818001c0c06c1403000c1e00c51041c070b9038010a09444090300b80742c0f4241d8103030860462507001b840c181590750000822595250703214003015841c2c14903005030010714007072881103650402603809410700d0b8086510140d0304030b0b082102d50b540341400d680e140301d840389264221060141e94010041c001c00d8000c1d00102b2a891140c64080007840000e903425420b4030464002601201c0c0342480240c403213500c08081c0002e8000729001c05583c084110081100500c00c91401e424054086841510781c1e41e601d02484000703141c2d41e4000316003c146035000300204040e0240451a014400c4c4800c4080c4060350100c0c00c1008481206280d43d080880544d4034107034002d403d03640b19400f01f0100c50008030400c0039500400c081500b0385410b1a403814060040301c4150000402da080c0c04447e0700104200041e03168100d80580401681d0f43c625040403a854400e40044a800d070800e00188010468001ca00c0f4080601422003004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 964830701 1250 964829451 964829473
    0x6110a080901170f040c1d0408073008250c0302011d060405070602011118031002180310020f070305070c030b1614070f0b28020913060501050a0c140a0b09 68
    0x1c7c08000301031071582949004000180041c400c0001800380134080c02a4032406030f0040851400d00c00582000d6180c48110000403050603007150480ba0850301035541240700400143e01441c003c00d540d001c40d003c10516109040a140c001e40c010804a400706103078403516203808071141d40d83c010035541111144144203000903110301c10701c030b0ba442038140c0c1d9626503e051a41c00390300002030b001001743c13503042c010804051111b4940e4401410b40c03031f0407070310500900680070702014100541242d6200d60240100322a1280c0c0803144c1c1280c1c40036505082c002d460b124141000c4002e6070440d04020154640e0b1424040d5000c00c9140480c4180410b950344401c84131440407410041c0255031000b031004904c01c580c2c1c4002000075801650240090706105d5010b81d4001400c0d0507540c8052245940c4c640c000352a003101e0420a56030b000205102400b4002d517440d01c1c1c0000d203e40720300085001003110b0103100404101c0c4903501024145001011030710200450f050184d00c506064900200d20f12404107890 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 964831951 1250 964830701 964830719
    0x31005011d0a0510030209090f040605060a15050f040b07050102130f1406090d02130c09080f0c04180f05060105010318020f040c030b09011d0106110a080901170f040c 73
    0x54400018201c036400301d19003800e00500c0e01300c0325690340030b05400f80315250301904c411007558440c0c007040300130001c1d03810700c0d05104046038805861103018400d40a8240302d5580d20402035184c040d81480d096030754400f50078083d140e034003441d00403060405000802000340681500905410303080c2d00d1050324004d075540c0040c0c0003080c4034030a02500002e104c540303e9032450260082d00c1c0c401005022040c46038400c1c0c0c00900045004855032611607640c10112440c690b01c00e1411010344441c90003003220801c5090480da4175480080010b201c0c5898a000440c0d800001201c1e80420f1380c85442d00e50303d0b0f04203140058a410007400703038a00091424418000100c043d03d07481c0f034030540140110b0781005000c0c0c10300014200f085e1003042855120040718503291180c00f0030314020000c8241315151141310780c044040e21441a40700008210300841e100c0d4141c0c03404208200d00d03035406014140c2d5824a0300060780c0b800c1c081e40d0030420310690007082203007488a200c0c4181c86144140000740c46107071209000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 964833201 1250 964831951 964831997
    0xa02011254020904020f2d120717030f0409020a021204032f060a0201050f060307030b07050c100f0c022509110f04031505070f050d1d0303100501 64
    0x142540440086400e002d0b04000341541e80090000d0b011a01c5a00070382c0200b801948403c804001034410070a0080c1d010304900207520140384211032010f82c80038072040a60b95030300f60b0300071158561a990000c0d16255800c004680c014408000040d440f0740c0d035942564000e4201360021405801390041041840c00d0f2075044509496020070300e007601c0b00131008540e031002d0f034a103011103c0134414078155a01c1c2d545d040151103030206540c0007080b41c1c54440c0e5000320400007e0003080c002da10104040c00029180036032240e100c401850400c2c1c0b80c0f401c00c80010320b8007500b55020751009140c1a03600d4401400e68001c0000180140c08032070140501900c00006c1c8074040d402801c0c800485001440150384c160000f45039001e03038101080c2402e110030705000b503e60150348215501154070071a010704c006280207899000c195410010803900f60001c015025110f11003487c2803a5980b100680b081a040240310a0440751840131640c03a031602c0c0c020400308030300a0003203a01095202460303100309a003004e80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 964834451 1250 964833201 964833341
    0x60109110a140a0e040608011a06040503330a0608150705041809080a08010f1a030121060c110f0303100605130b03190b060306030a020112 61
    0x40704a081500b11450380d064100c410102c0c104020641200341645d918002c480241040200000e050001d040c04680c0c40100329110303c0c002c0748140400c005a6070302182032041c00160308011240d0070410100c0f504815800080031050007000401d020700303940c4a0744404250346003041220070306034402145081904c01100c8510004100304820301820603a40801d5400d15401d00010611140300d0384c0d406203d070410606600002c0000c80100146040042a00000c05021040891f030204550366001c86201c14001c803140d17401c1a81071801d103e40c510780c00306d1000703412203001c01038560300500040484060010790b0301c642c0710b416070000c2d102c1b0340402103902813a031424500048601d005400c0c7c583d9041160f00728001c071552403000a020700034200840c46061040d82080401c40300e8206e507801c49071498040b0b401150248100555510000384080708681c090801c600c0740b81d0000c41010180091008002e00906104045001c07024108c5401d40c407240e02d103064200c4500c40103551801182d81d0b0f28 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 964835701 1250 964834451 964834457
    0x50a0c0305151e06041503080f030f010f0303020a081e13180c17070c050d020304051305012105010b031002090301140906010306090611030106050d1526030d050702060109110a 77
    0x10421320b25103588050320001c1d0070b02ca40d4a4159480e03c920543c2e41003008415503500d030000c100102400102e00960140140c0100d4000c01421034500079554242d40300018211500013590556070b04441481c2c594550b4040f001d541c1e200201e048208100485100f00e090030f515800c2c80101141060055540000c240d03995441110b9407600562801a0080e0080c0107100400d440b01d004610180014000c01c082034000b56030300c0f407505081c00002e075038045940c8416847e01c4010310022015107500880d0b0090004120152100c1d42012030051007605442a8588a50707044604428425009071207405401c4000b000b0206c00d001c444560700f20200c849000540143d00140f0004020358809208180220000200021640c1134007419500030380008010a4001c02c0480304060180100346100064402c0b5230f0303d0500d0318140010820107080b050030291481c04d01e400071106c0070010746810310000e400c103001a041030100a5202c82086c0035200485052640007000c00b44504102c03074543c000744c3e0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 964836951 1250 964835701 964835761
    0x906030209151b06040f0b0a050124090803030106180f031e060b0d0b04051b0108160e041401050901270c11060408030108010e0127050a0c030515 64
    0x8040b402a500210403100b11081c01c1c210022404010084070388507500c910481100a2600c0c1480405030b14028802c1c0c90b02401c2030014049000110800001089007040801d000d01180720103a903202401e030010b0b0741c9807001200018982e54414000c01c40300044100c4040c0b001d48800f407144000b203080c04041d01daa210000030000d10003816040c940041c0c01a140019070141e9940024210201d4403426a041900d0000380000c0c828103005174110781c4c07000d200c15001c8180840020f0300d610030080c500d0960b113041d844000005400f0b0a0700f54084500100104010401400362140a0380c0a0003014080c0041030000300311002096030280e041d42424150711800c0308030460940c090040885800d040000078481404089401c2087d00d0155115505158a03903051040c0d5900712104040042802d81c1041c4441002c10032002e010084d903000750000415100380c0c3d0600f1461300340f2a0320000c15070790b0911000010b0210100380589000c40180c05100141c80300700740759107001f00750707000141603080e44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 964838201 1250 964836951 964836979
    0xb071e080918191a06360114030621010f02040e0103211d04020c0303091b0406060509040906140c04060e040204051305040204291f05030109020306010329010906030209 74
    0xd030f8081c0c06c41c04040c522402c1d9042501c2070000c050104281c1c0c4101b0328501030b0340301c0d0481da000a139468110b08240881400d51138034000080070f503901d04060004a8190005814024400390002c424030a0402025075940e07684003900c09102009200507034240c00c0424948252107020700600048451555580300c506d00740701c544c0903209000c001d403550301079820044008212801d0002e14401d022840c00b80c0055000300100000e00c18100d90001d20407403801c10140051074112066406c0da0600381d400040300d400324038062000300342908460f1140d044140400050441800041007603c0d070650307079110051184400d01050b40542d0048a03400020782069510b160656804964400e0004101158031038101060981c544141380608030001034000440c181e40c18401d5041e2640c2c002010600c0c00072044040040c8540818012001026000000f1904a81c8a90403100a00860704011201d600b428881115444260795299000c036802e03010002d41c00e4040d2080e280300794000b42c00c8040da0145 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 964839451 1250 964838201 964838209
    0x215010e061c05010902040f0c05070b060414040c060f02190204020a2a0b0c0405100c111008071806140903070306140708010b071e080918191a 63
    0x20041c05150040d0000e5916161104a031844842260042c000080d4100c014014002501c40000891480b141880070000c1d129510500700c0d12625001042d680554407884006000303080c0055440c3d0300c80da040000d010602c40d0040701c910031501280c94501c0b0390340c14601e040c0c0e240d0016101c1000c41030300a40e8544050b00b03081e0014681b1001602c2e2100c03c84607020142080d070020a58404204490101e000f02000600b0340780fa500260711044280c105407030f0000150000c4c0c410720740d07802004520040b6104004418110360000040240218454621000f00812050086a0711000030f84111110b09685004814107000d032182562190300c542d035040c111100d6603015140042c0c01d0710440100002054880c0306a401c8600c80e0111080b0f0b504110340010400e40046e088402200c06c100b10075030000302d4100c0c610304118070355805074210242d5070400c02c0b01e03402511011600038110342c42c2502d054004bc2c0c1e00c40d11801c00312001481180c06414a03070308032000042c3c000d049480401c0744514a1034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 964840701 1250 964839451 964839479
    0x5120f0703030c1b06030e100905070512160b0a030b040b0d060528020409050906070c060506010c081605160e0a0506030f0709050906012103030903050910020715021501 74
    0x200a56245020003c9041d2032800429280c0c48900041d54a42e1f00c20f940345400d00811036500300001040c0807109040d06c2e11525140103114182c07091074404240491010188131b003d5019034910900c002566460454121680c4801041c00c006490684034002e0384c5050721440340c8600340600941d91a44c072a9540100901c006400300d1009003049603021340842c811410140e0105070182c0c0540c03140d02d8125140b040e98005420345c41e41c2d4010900300510158802601090f00d9000314000c611504d0300e4005840030000f0301d01c040c003580000103007032a07004048a5004000d0340300c0c034216140c074801ca4041c07422071229405051402d50392400031a000030300c2c503089190031103401001d030380381e4100c0100740d2898440740b07610101001ea100c50802c41403803010700c0054010500b15801d041c064160340380022401031850401018580d43d0080c01d0145480781e03069400d829406054004104903d071006580e8062070f100b44403d1100b41514119030038030228101007041000074011115908140c41180a40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 964841951 1250 964840701 964840703
    0x902010504050a080307050708030322030903020904110307090204060e0f0a050603040b0a06050409030905130f022b11040e2e09180519020a030807060605120f0703030c 74
    0x10074840410107030f80f02581d00340204440c0000395501c82035803130304509200d603683c03001325590024020800102c9641240480c031243d1030f0009a040a010700c1c0650f000011a00041d4001042400b000104540140c900034036060131801c031803800d60b640e110790041c0e20490082d07500240020416030621300303080c1100c1480300b03401072440b10650340f16004070360a034000301e805480038240c410600008031507030300c035040141400342d50510440740c0e00c1c0c80c007401c000e080d48242401060000d1405020845076481b0b58242100040f081d90f89000003c420b8a5006000c2d101d4441103a125040b441c007450306200d0441d2003415442028201454110030f01483c040003042200841002e03c402e00e0134420801d404101d80c2c800307009445050b424202c0745002c40d01000c02110041e040809820080f43c0002202da0000ba0046103100d000446480410448240c03a8001418200041251401c00020760030580548506885140c4180340354910165121100781d21240650003466060000c00d10070140940c2d41c1e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 964843201 1250 964841951 964841957
    0x91009020d0b0c035a15040f021806030705071416121505070203041d161d091506030406051807061d190602010902041506020c04090201 60
    0x1d10710316251a000300c102161443e1001d1000010811150007404e590301c5070450a5190040c0202410303103040044421658080e860800c080701403c1d00048441c8031001d00e944066101c030103007030440680044c490301c0628180714074100403509400d1303520343c0b003034031402c40201d00d00051032000b90051215550018100d202009010804c004c0032030115400c00d201011110001c161072036207103800c1c0c7d05400860f0480743c82c085e2550410f1000c1120080981200d041054001032280c8810200340d00d144990b40c400034040e610400c00d8821001140369885c880c0040c030019468100380e500d030480d280e410340c18258a4645905002c00c1c50303401e0032409658045420700349506540b0540c0b0000352550400c4070101c1c0c1e0fa9850303200300007001c540952005045000700000349501820404050724582e815002c0c00c0e0801d0500c0d41e4801700d50780310003002010050540403040c1d2103851b501c00a001c2c1c010000d0503405242032401034485445442c1042c822a2810b40c041d0203145401d02c00c00000e030910600582c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 964844451 1250 964843201 964843219
    0x705040b060c0304030f0209010603110715151205100b03100e030403020619030c1115150a0303110d020a020d06050a0b1c020f0306010510080a110426010509100902 72
    0xb810800082019502604a00302102d80b688100003407550142c12030b508150900a40780300b81c1180384107444003039038011a01380c001c038141003912000307002c140b144110f024241d02000544015410222840c24065426100d88041d0302c2c80d0b601c140c48828105d5900740d84200022400741105602c40080c2040718016249003940e030382c00107001d0340c00c501d0342c009001c1d1552001d140341503014441d445005546041240c180280800e2081c0c907100300030b9905031221080300c00220185043c4411100c1c13800000e00000300c040c1c40781001065950102101c00c003910400b440c40034802d000107400e030051036004101c810f07421392607929400a0300002c0c1034154059140c411855803075a60300c251164450401307540c14070a102c140100a1108400c03d012402504500010700c865110700541618000350f0307003840442070b202c220078a00240149070341a44e100c4008603001c500e00c3c90210310860710096007070002d0081d0066001f00d60880d1011358180038a0391281140c00300c10017040d04007000e070030300050041c02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 964845701 1250 964844451 964844467
    0x106050907030b120d050d09030c14012f032212050d0c1d040c02030705010204030b01060e01020609060106120e03040e0417430b0103060f0e0705040b06 67
    0x440c540c0207039a41d8011076203500b080e00090420b01e2012418440c02401042c01e10081d410251182c419041c021100945480c4d402c414103015442190207a035004000c4034911b145030349441e000b00301c05c2e90b69903031030070f41103c10442240d0041620040200010102c0d40755455005140c0e410800e1804901f0004080388104404100f900c0701140c4001425142d90340d0f13035000340d40000c08070780150710003400b40000c10300c52455000380e80b11014088581990001303a0300c1c0119800f0f91a5018140006000b5800007401108018424202d581201d000761504d000003100d0100690716000704460035021684480010000c00d8825640000c00d030802e4100041ea801101850074116405500064280b8920381c0c18401007061140102c11458140000941003c030960b9060704556035011000742507128148010074224003a58042c00c2c03441e0b10021a4804660300d03d04610050003d00c010b8421718941100908028103501500550baa1000c010341074540c201000c21000b00b00394000d094114000740305140d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 964846951 1250 964845701 964845709
    0x8030a0f081005060a23040b070602030603160b0c0d0e060a08041e0305120702071d060a090504030c02030c09010515222d05091503150c120f06061b010605 68
    0x1c8086907503035014848002c08070541403140c00c862100c02d84c0d8204000401007008d6050544008990000000d80d4a0312040e000910700150300064140302c209100c00000c0e40c60f41000140000c41104054a45007203403414203039805a1100011604a242008147e1285114040b46c40e0310034071644030507465901c1c44020b540001422034044000c0740000411802d002a080c0d250307a84000d0380d2009204150030728003411004800ba408451152052201240107982d90360000340282c402040d0030483d0f41b401d41001441c0c3c45100d50141d010b8013071000401514101400c0701c6041e11400760091040c2035070109810a2a80840590000c0c02e0210510030320f01c5840e030365943c0040c80c420070700760040328001c200721900d0440c0300b0290000c604483d00030002c41d00d0712400790b60301c42c2c442a51000c840d07402c140421704040d03100020b01c04c1c10101608008568080d6800340140c030616010b03490181c1d031030b8010821015000e40b0030710b501c41810702c01d001c00804582440302810351054000b152542c1c1d220085 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 964848201 1250 964846951 964846957
    0x102061311011418012007150207080a08071506050a06050c28020901080d2c0306010905010f14150702060d090812090c0f100e0d1b08030a0f08100506 66
    0xd010b5032541081c4c0700d41e80030900b0714298002c40e0103181201d003501c100580d9442d00d4802c008103002d0000c40040c050b0f0003071000300300404000003519030700316091030414134903403294000315550381c40d1000104041c06107205040580300301904402130300c0d0401c1c0c0c0a440e190020f1966480601c07ca665500b084441ca00c90407442c1200d08800303081b0848a4410001d50400503003041da080e030720040c030600c105580502d00131300003010603002503a000e1301c1d00d8010f5001c419201d00d8980610a8000001c0c0240c081d610060484001884403100c054555401860a07500480c080e1b0380300e480040c0002115001000402d0304600c000c04440c50000c0e00c000c03a07400c2d20300c1000705544407807010501c5102d1140c06030b6565400101039016000c203103854000101a07240300d00581c0e00460364480c1d8403026078003890641724007220051060b0030645d46894680d04e008420fa0303a101c0820498800010130906c0001914419085510b0710624081203074800c458550008120b540308041c5e9650008280d10340b0801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 964849451 1250 964848201 964848217
    0x30f060501091811010c140d080601021c0e040c0509150c011404021f0909060f0302100806010c1b09020301091a0a06140c100608031801020613110114 66
    0x4241507240050302c0040303c204040140e039095201c008040090168009480b4206090a1403800b0b10f00d0f9086ca035403a021a4031040c512845440d154200b41500402d01500c620001d0742102d5401d2034240d8464000d4a00b040c0c1e00000c01e5a04128091314a815040310110082d40e180503030030907207450002a40b924150b402036681d104c00040c0f240ca01b2201307008008485400c003200000504195001c90705007010040f140d0403141300e9420700005140319103a00070090162400500c0915211403503c038400d43c25120491184005101941400740980c08052023208140c407222806a03040e100c000c10760034044444600c0c5040b0980c0820054a00d20107180607028198000800c08003601e502d020060f00c00c0d80c01c40c0b1944880500700010342c2e0041c41c00064407000b2030143d031520b150340501840e154880c000801000d080290200744050008040c142d031660b155080602d074020a801661521800c0e541e141480d484104490046011954160303403140301890070030f01400412004030100d8001f080d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 964850701 1250 964849451 964849463
    0x160603050901091e0323090d03140417070e011409040c0306091515080d050c070509070c020102061b0f09060706060303200f060610021f0207061d0d0810030f 69
    0x1c00c1d03109042d8000050322080b14404521881030006c05c40d9042c0e01e0140814181c4074071040301c440c030201449964100714070003400050946407070300e943d070f4101413905400041003644140100094000000e20205040702d03030b0141d601380c0660005052220340c0400603c20348410b041c40c00000001641307803007515050343c0110408800e09940c2d07000601981e9076403d000a920301c0e0f10506008104010911800102c00c608201d50b4a08010300e010b420000300354403d691002c2c0080811254076041100b500c482d1740300341d080c0c0740e0740d507568051200c514510500a80400b0411700c0012400c513131000040a14000c01010300e801d20140356555001e5602503042140000d22040004c0a5040580303100d00c00904242d01600120012620456580c98001d042520943d80c010240d044a03000340105240040004924a2408a8824040c0103503009620441e2030a141c071240b00c4260300780700c030300180100450001e044a8a40348a0848000c2070260a800804040480000014418500d0070520314403d00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 964851951 1250 964850701 964850753
    0x1e030c03011401050c07081e0d1205070905030a0b0601020c09040b041104020f0d1505060a0c1e0b090d0909050402090604050a0b1c1209030c03081e03070203030906070216060305090109 81
    0x1402d404102d40e08c002000e8950098079404017143c1c1000d040d0741960231880d40021144e80d001070440e008061036001a8250140c540c0c0300040c4400084001c0c4129401e0302104e00e10301c102d50921042070070881d40a41180c0a44000c24005040018900000000104090300f040d0302901c002ca003907808000c42c020b010750b80d00903041c07906030944403240c000d0030304407880e9062945002014200c8200c1c040002c143c42204004030714030003046609030421a4124070300080c64542002e4a590f6844a02d21a0010540f40e281c0043c5041e5140070f03891040341d001e810740c01903403110002d00010341030151600303121a4a4141218171904c0741138105c442c10b5640f404801a160f080c3c1005900b0130680340c024400c00070303520f20920108120b501303840122a808150316580c0c904104c940c4c8039144100c3c0c1c00c0204014008107000203142d0010181d805074180d40195065500c40b00c40c240e0b40c0d84150380150025089074241000001c4c0a236000f20740c000b85803400420929842c1c0c4d5125141304006c030040700141030707803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 964853201 1250 964851951 964851973
    0x22e03050718170c0901080c0409020d0c08160909030f080a09201f091a09030615030f07080c040e190503040821090904150e01021e030c03011401050c0708 68
    0x1044282403106040d40c1c5c8001c55414500c11071344402c5124046070096440c0d01200d021500c85510804070240c10942201380d40c1d0300c81d0005071300d44c40203507881b118020103200003103042040c03031088520080e07141d100c3c01c604910b101c5054030440801862580361581d14240900420150b4000b034504520300c4a592044185400030089540d900f508a5040c90280030007030781407142c1011846096031451500b508141c0700c00703d503083c814030440101e590580688000c0c40014a1035640100c4031000840c1641c12100f2f070509680d540ba42180f00305d0100c4c1e4059102c0a00d141080d500418040c845a829a04280b8810212003182070030414102c80a510010301080201c00521030100d480c20703100c0002c46014250005014240a08080c02d4810715444001c9810852014110703011301c0f544000c2400b80d4030301512442d0003508000c2e4072100e12000603c55041e04156107045911501152001d9829a424003041c1103110680201c801c1c1071000800420745400e1007002010018400d0720000c043c40070031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 964854451 1250 964853201 964853203
    0x1e0203070212040e062809060f09290f04090b160c08040506030711011d010c021203011205190c15050a17060418030903022e0305071817 60
    0x88140c40102d080814002072100c08142003903160020b00481d600d1b204080150380101480c0032500c1c1c10310241e60040c500207074211154100340c0854400481007040d1581d180c50a00540e041e41e403509500c01c2a88021011408203c0460340c581140076040500360300050300800e0444203040015107241811004000e8180d60f40e1100301c14440840c5811030040f1455540c030395072401280034491241801100040e48548180c003400310942402000b0b201084c195000c201cac98082290707560000d035003031400f40200103000007411400e201d4000700d0340e86160f2a05001010b8100e21800444a5016600c6018144d000780a901580b403400703560450400751410100604a0001551007801e000d0305000d0240000d4206142c0c144444449042d0b0740160345190010380101107903d4030180c0b042c50202c4034800c0c1544859288140c1e80700b6903103070450494074080d0b80000d10405100303412a8594401502110f80711303412490304100079043c896035050440450480340c1c03040f40c124070300411000750201030001c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 964855701 1250 964854451 964854463
    0x110309031f0614060a0507080d060b070c0b03010503031803151807060e0607020d03140c070f080705031e01020708030f0402090604051909140105010b0a2c131e02030702 74
    0x41140880c4100f480e0380310101d079140c000c5900010a01a000c540c1e4400e100c3ca03d4201c0308090700d02c440070400c1c1038a031070b0f112496030032110742522070303041561011071103074605412241070f654003d006600744400714100c0d0200f00300c161559509800340d404400c1c050f5284184a1b4014146403500f0061055035222244c0f5291496000e942084010b0402ca056600c4e4042114455a01aa004215421142000e8500161000398180800c00c00150300009000215440056469040e00401082d680c0e0304059640e5100380a007070b601d50031420b0841e0100c808028507041c1283d01c0700015081c2211522280c000d904200e582c1c503182400310ac20003046180c082c4a00d9441801181d0410031030070700070a00780c0440400e14240d980c1030394840d1040c00f03200706481418030244901009001640c1c442c00b1502003504400e0022001c6042081c1e9030727542c400303491441e01c040051808074a010554030310405c1403039a08021000395090f65034070b001825817130701d10100611014a00001d42e8074208160005e2401d5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 964856951 1250 964855701 964855709
    0x806150d111b1603030e0321131a04090509070e04030314160e10021009110405061002150c0c030d09050d0908070b180603010e090c10050307110309031f06 68
    0x5080168449000744100e41e4070811340b600b51510000d120030303400c04240761481020501c150039150346031004295a40c07000401c08907040c0c01304207000c66610fa20301c981900001002c500200010300050110f0986030740288d902a120b01c08a0380001c0d135441d4180000c40081c1d030241e0001e505c4065000c0019918000d85402465000c251030440c40c01010083c841e102c801e07440b42c4144d80c0c2c900c80c03800c468820400041d1850740c5d43c40c10044031301c080c5440010345200041450040d03091600084e810715042c1d40084803a40306402602200941400345104910000c00d0761801d074405120400c03002604102402d00e030400d403007000481100f82d003401da14002c0c9505050041003006102805246400302c0c4400031030b50380191007520307900c0d28011408000140045107400040c0800002072610103170030001d00400440342510481c06c641c1c414000010104030720000814001c1010a801500c26800404980d032031100ba203082158141c0080d04005010a070503248000480101600d4000c500c1044014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 964858201 1250 964856951 964856953
    0x312051501050a140d0204090b030d050a0c060e011d010905071e0314120c0615010215040b09070e07020f0111070b01030f17040b0a020f0a030806150d111b 68
    0x40c48200000038524801e100d419001c101c1d841c80c096006441c03460540e00d051020340c00640d2910384a60f0074100500c020703009640302c0d1152203980008140180100c4000d081c0031f81d280d0f942c10b01079031140d6001c1c0101c9299105103650f103071038418100700e100c0c1e4103000d03c099000c0046403000d940c0c241f0714039001c42900181800381c04044030600e849103c4410784110b03907100816038500481c1a00441c00e03c200d123050f94440c0321002445240350700d004181c00e0700c80d100c49508403010031007400049950368885000300000d084000b010038046002915280c1d88240018200d40626481c0d40c002c00d00a2001c0c0c0340140035a00a65007410071030300070f01414529003c0d0a030300f18145842034450120100c2e0600c80601907041e20034144003840442084410a40c154481c1c065031a41d8608a05e103041e406603074440014043d1211030008054042088a001505982c661005484d613800b000403070b24110317100c01b80c2c810003007012110300c80481c080c040e02d043d80c2c2c030382301502c54403000c100d12100d040c2d440b24401c1c4c03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 964859451 1250 964858201 964858231
    0x603080a02150708070309050c090a06050109060e060403020d24020d2a0f090b130f090b0d02150d180b0906010602060c0f12040c030c150512040c050d031205 69
    0x10a81d1003139100ea0300000c079240100e40176259086c4a070505c1c0540c000c580d0001d4110041000034a5540c01c0002142d200380da5600c0c40590300c00e000c0342e007030030007654846d40840100000c001519118601c03001c0e00d070240c02d0306412000c0d00c03160000d2a49400c40f01401e000e80220f81104150414424148801c4120660400444440c5c51b42016500f041c00490184402c500903400a40c0c450b910000240404000c040c1c0d541440d2001400e151030203119108040c01d03840b002282c0c2c0d60721030040b141000d0340900b0b0725140806541c2007194020303540040d50b8078403005002004c1007109034021480d480034801007032824a80c81c0c2c207008403a9400100002d9040d0300c40c400420410740d00103200c1c0e52014880c0b6a107903d40011070101c0880d40310704951126168850014001403001c03e016080c220f07840b403841d0405141e030b5140640321702810740d0880004074400344010a0004d02c03800910b68800e200b09034400809484100156400001040a50006054030300c05036402d98940300b081d400c08114406a04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 964860701 1250 964859451 964859461
    0x120302070b040b09070f030c030c23010c0201141605010c08063a05031902160501081e090d020111090a0510030f0f020c070b18061c0603080a0215 64
    0x55032901030702c010924015080043c01c5040c052060201421500006014165036810920301c001044e002c207440d44204030100080d03014480700b806400c2c404034a02209015481030041d00c40852192041e414800385001a105000800c001080c14055003403018107400807d051207400c55a200c5800c10921100809016042c4c1d1800180084000d5a070058031040300c4002000303405a000048401407081010314100030042c021001d07045010100750b030047c003038000c244100c0e5503a000c0c0891030240d00b0340d12010f0015501c24940958860710b0741101403401e60070b1701400500707158222079020ba103070040030a11202c81c3e170a01a941d14004802c65490070a86504002090b281b0a44501031258406c4140001c50301d010390800c004c1d0345040b14082000481404401c0c0c0a948000d4203003940380642c401c0402c110384140d095a420210002d09010300c0300b2090140300e6140d0000200c420b80e01d4040d1351021070b486682c01a140507501c10f4a41030388507070704400003078900a24010101591a841c500b001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 964861951 1250 964860701 964860713
    0x92417040f02131407080a0b030d121a0310150f1a0c10050907050a0b0f0d020703020a0c260303070815012d0f1b021e04050708010312030207 62
    0x700401e90119140b40340e00d19a1000e003801001681c00c54081c4a090600b000606038000b102a48150300301c19040c062811000201a1a032000414050100e440c0305440004409a0742c8640071590691078000d41713071140b07440040d16002d9140720300803020791120050103411080a185900401c21504002511810b140f402d000d003100300200040c0004000c100340c1c81040741008003c1480200803002c0003242041c00203151189228003925015086412000038021043c0c2c08441003091814103a60402d1b0034908420080d5014020940440c440e0b0f90b80d490114084110010040c400a401420b4401c0442c0b581c1e2903007500d02c030442e00c1c50f8000784100b14103950403d850b680d000c42d2031440c04205114100c0103a640300302c09140c145000c02d019541500c6103a403904002500c11694a032600c0855400d031048481c0d40b00071715005000c0e00c2076060140141030000300400f042c2444010711201e5402d100125080394401c65003a03000800c0d00b40100248401c28032010355556441ca01580740160759103a003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 964863201 1250 964861951 964861973
    0xf100b1903110c19110d0f06051b030a110c060108030901081509270111071506030317040602041508040c08010204211b0612050718060302030709241704 67
    0x30b201e090070208031400170030480100b801e1040c01c004007060324184490901700b202188400e0200c50103803405003c11440c2401d6002c0310031000d0189001e0f0b2442d542c070745d5420040c020030070307044401d590140203034000c0400502060340a411040021a00d6001c01000103004850152407015451805010407201d903d40c0c4100691003881c100c00b00c24a00750071700321001c2c01c1c0c005003010850707540f0b031180c1c4098920710900202111805110641d1666441c051103004407a00d40c400100403c0d000c0302c54101131140d0707030555030f40903004a8005041076039409960404804031869103000032510300410040201c803502d071402a04685000f141040d05024444442c0010b84103d84155101c00100038100545c00320600c40c944052081c441a5a0b603504019003407141003c151501c0600f04000110490300c2010074560140000e00001c4000c1d01c0e0440a800a50028108104200c40c1450104444040c0d9042c9441030410082e83c0120800070703e801031521555082c0c0900841011041c44042881e40c003403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 964864451 1250 964863201 964863223
    0xa0206060a0b0708131e03030e06190807110703060e0f0f071208040815040c090c051905070204050421030b06030727031a0105040e060f100b1903110c 66
    0x50b03a4410f030446201854107030368080e9011549011b00c2a18615040380000d0413284280c8444c00e06100e1281000003d008141145c40305000e014031810b0054031440140d50040031504040b05506001d080c69400c103140c07034201765070040d00c5c0e041c1c43c51004070402150440401b003401401e42540001ca2035a11121a03110b09030880301d403083c80000380140d8608541c0107000b9a01296641c0950108800c807250003124180d40340c030000c041c0000c0024031401109644204c0766134007490070440703030358001c0002c1727500c4810800c02000f03000320340040e107891107aa4020b0f80111702c80c503040f49101c0170581c1b8132040c4040703c6c8101420400300780041d449910030b0320f030880c5480c10f0181c04910600e800e284200c2100301035046001c0280c200109001041031071803402043c00940b0441c07683c9480600c0103071954220610b056500810018440403c05140c036500075446200c14122196116580300089c1c20580c407001300d40708446868005640c00d48039203208141184005070401d00c82c18055501c1d104081c20f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 964865701 1250 964864451 964864463
    0x10f030b0619170c1e010f020f060a021602060a0903020319030e0f0105131212080121080c0d02010b040b0a03020108010b0304051002070f11011b080f07170a0206060a0b07 75
    0x1030b061000f480b041c080b0b1000c0b60300280681540b0036881000c0b90b81d95403101d852501140201011136000c1d480483d5030340507100400000d00d0b00f40c031005503031b030b009505c000c107a400b005500c2d858101c01030761420021f1142c0011551054159411401014107000c030346000c4c008400c0e204031107140042e0700300c050100710320000c803802c40c40e200e03080d00103032110300c251510946901d4000340c010070000340c1c1c8143c84c844a4080c070b211b03030b01400c4407141c1500c460038280900c0c0107000b1300c400c1c1341201054681003e41d5180c0700c0e00101d401d150306103003030501d00001000581c0c0907035100d00b0805098101440b50160311101121100c942074550340005c2e051402c18010301c002c000c2e000000800f800070402100424000c140000c5696654030f0400210506854070304484481901603094810744c884c1490703c80e081d41c9881c00391003405841e0342d000e800358043e16200b04452000d110307440205401e020710111949280752215507841040b6002400e00c1e200420b140c4c0305040380701043c808003120800707403030241d80d100c6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 964866951 1250 964865701 964865729
    0x507021c120b33090307050d060e030c0f0706030908040b0d0f02030702030a08090a080702060a0314010f03021f020606010c0203070b04060804050d0305010b1903090b04050d02010c09030f060b0a0e010f030b0619 92
    0xc28141c000d42b5400318000f00300e200000d868200250002850b01c203500354002078403001900d1b072204409076429184c018085802c240000c3c021540000010f00180e035101e10001001c0104500280903600219211005a0008101c503003031681c204180c558442c44c0300c2c003d0080b443c07040c0e070f03044028003415030013034000d500c0441c0400a181c040d6029400402001141500139a989c0d119503415140700d000490044915040c42071001c503150100031030920b45600908004e03900c0300011a011501000141e82c548217014001130b02035042002030029010503565078210b85844d003059458010180764080c105403800c00100b0070004400c0548024218000080580900034032040300030f00b0307402c54080c0150702900181304c10460001454211071107550001c0c00500c00050003520407410300e11024003a03258138403d54000070f42c1680500c05a0100130305035181c0300d03210146126441d40c26000491840c602071018001d00509190700c5510007811035001c40400003001c00c006a03a040d51240e00315050f258 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 964868201 1250 964866951 964866953
    0x7030b013c03150b0f120901020a12050f01031104021b01150602031305041e0c0f0f0c020919020c0a060e100908091201020c01020a030f0507021c120b33090307050d 72
    0x12a00310360305c100350040d5100d00c81c2015192030f4000c4d0700c2b200c110340c081608006003003a42c1d061800784602c82d86c22404418010b03865034a0342690544a0740324517a10030b5007040760103400004c2c003a0080c004610741d000003882e00700c2c4580104c1002c07050742000c41558410722001500d03034003d04491066800655002c1045085a909680b2500064000107081c80c1022248000c080c0d010104990510b69596803080c015490b40c000c0c0c40c48a000745000e90481e00480008030181d00640082d61100c110010051509c03205000060821148000440f00c2a4071404807100051042150100031440820204000556961140c5141c420000030501900410082c03100c2c1003420340c11303110540c0b0000d000f55981c1c1e0384090010700800b1600164200300d4642408141150710010310841001424245005000740ba0b050556500c00d000c20740d02c0c5920b447e0154941039413101c200700e1210040e003800c0200c2704102c4244050312b0f94105102130710211014055100c1598000032100c0855006030340a0b4250505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 964869451 1250 964868201 964868227
    0x120301060f1209030201240b16020d050f16082b020a080f0d15260708070f0306050711100c17101802090907030b013c03150b 55
    0xb000103801c202850440706209154064002040c0f98455011a0710702e00301182c00800b20060034020380ca8814001d0210409404650a000d0307900e0740010b0600d500b0750301d155a1903192140c0c50111450311b801207503a09181034071101405000d0110f4402901200640308248164031840020448500804d1000c102d1050f00034420f8050407600100361607581c141c8031415030008e61201101c0700384c45152a018a40742040c0145c840241c0300ca040051150408014945082e01c1801d80300b02c0050003202d000061608040054030010402d410b038941c1003034a5400c01c00c00b00c0f035004011205001800c2c011420f45034011030210ae8100514a0000744071516039000c84141a1003d40781002030050740920005003080f12603501140c080c0780b80c050800c0c09045100085e40603003034507150813040f132030041184140290000c2031070b00c0043c54004505800084c0c460340c8807404c0307440e80080b10300414040503545240071820384180d0042c01d082c0000c0c00130b1010b940c2d448c0c03440e2182800d00c020201b00c500804e15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 964870701 1250 964869451 964869467
    0x40803061f020f070509060f04091a0106080709050d1205032e0f081f0f09060203040605160507050604060c0504030c060305090613081206010509180103020a08120301060f 75
    0xc0d030318540c5901e09910240203903441c00c0b8066004410b2294000014051901d040301500c52079014148031034690302c080500c005040c880320201c604880a81800d1403004013000910b0007060141d403a01c030281404000644410180c8e00700c43d001c2c0035005548400300c0c0c03840080c1c14a9507120b282840e6290707650181c04d07a40f0042c1c1c162090801c52404c4c40440c11b6140c3e001040e003507940d8020048007045d602c2c40e90320303542c000d46122102e010740300d5420403c004c0c1e1540c1c070a60001044510100e869401d030703a940e5080760f0040354101d501c16500c00502c500b102400070140d003a01c00908140c0d2502003030ba2a029620707080184000c240d1038590000500141c17061003510700460b401150180000d85403000136025040403a00e802c001c0c0302c0d65001690725003c200c08580f940b5004030900340340003026000066090b400401042c1804001c200101d50350306c07a410740c07502a1503202441e03036107941035204010014140c4e5010070140d41c4181c0810901c036000d801124111074072420001c92011109100b40c0e1051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 964871951 1250 964870701 964870729
    0x50a1b1d042c0607210905390105091806030703142104060903080c0a14070311030a0302190f05160905060103110322020316080d02060105030604080306 67
    0x15003500707030500154502449140049140e03019203c460384d420000b221070710310740380315020361004000700c0b21040c50299000004060013407056a00303001d03610983c03480840c07050500d4400008402600b11030a80d0417202180300080921b05280b03400340c48000074030194003008101d80c1c10101c48000c2813480d6020444040110b03805401d44a040c0750f064621503c8902c003400602140c0849414030107420500c404880a6640c1c40d126007020b00d04580707850020f40c00c0311a480850b4400c180c0c114011401022100c1450141000141005400d600e031280350f00d0f20b0400390a009a01000079000000d40110348151032a54074401c10700741601c107080c190b9403408035034806059802040040c01c0c00403544c04110003a941c408405000701d4560800440480d100c8501100192009101040d01c0e00d14801d401c2c00c107500903a400400c9203031960002414040520710700842c010b6011820082c6000500100c001e841c000e0000d05080e40c50503000c69140e0380c0c020001040141c000001542a075140c0100030880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 964873201 1250 964871951 964871981
    0x501110307200102070e042f0a0312020c0301150902030c0f0a1d030a051002030613020f090103050f0114010e04140a06030c080a0c09090809060c01050a1b1d04 70
    0x6002c00c40d51840641d01c0b122159801805041c1d00841d18652204070301d070103030381d00001c2150038101e403100b800c41c640d2451025010340500d6815181e103d950b20b046101c051405280b10403203042401e10040c1c81d0030b08401816000740d0520340c291149ca110000d900b821282080b9000d6544c0d5030b0103410541612030030040d0041651701080319802b507a4842003882c3c3c001d01250400400b00d00c01d0301015aa02c001c5c1400500c0c99201d4140030f82e0a10341d60b00074580002015090300f8502520490141c240c1e0028180c5080741000030900e0910b0307682c9805001e41042e640080031905504181c0c0d442c1642c0701a0305801d050044010f010303101a242c0f54010300d80c003881089102420305043c1e83c03e0019181600c016182812081000f040b04000803800c0e000c1c890344114514001c40c5030082c44000345c1503845050f0350b41c1e00d00b4051440e5580b14840140415105480001003d2508a0042d011220001310054446481c4003032804420b070411040e4807021102d44184c0319003050080084e0107010619220103031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 964874451 1250 964873201 964873223
    0x2004150b09190f170610030f020f030c0a0603020d06050108010303320d0504030e0f030322050a08100507050f0f1e0f0d110c0a081c050709090f090302070501110307 72
    0x1341e058041208030600c2c0d40c54054542d540c82d119000458502d481c08041c0c0007000c0141c0c1030005161210300b00003c0700e80a0240c030b5091217040c000451010855001c50086038001450301d81381502441243c0181800f424040701079411610300802000c6500042c04e1961007103001c103140d203c040540c04000e5041d036952190388040c0a20b031503014200503102200401c440800b141c105291242209000e044050f00850914440000c0c0c4844070000c1c001101c00224154400b0a00352038240391080030702800300003040005a10344000040b80c8004041f1000c0050601403024441d0007241111a0004031a00841e11001c85e90680500300c003d80e01e801c01c80d0340c40011a01c001c042420040d00305401c00c40000c01c9844170514001415104046a9000b1600100c4071140080c1040001d0100d2200b10310560655903001c8840004640c8280c8035440421303202401041180d1283c0a04000c441c0c400c10306000e4844c0d41e0f41e002e0b6a502a9001d02030520240e43c50300c002c001002c00940e6080707a001181404 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 964875701 1250 964874451 964874459
    0x70305120c07020f040b060f070606170601152c060c0706020c0102101104120f06020c060103020a15020d030c18090c091a031308072004150b09190f 65
    0x598442c880490180140c24406450b03450640b04501c070000c8003410b00c5140440700b070440387d529400350300203c848640c0d5070f8020401d01c04005190480c1c80a40004141c5541802c01c10b8000c54080c80c600230030441d58820711440d00b40070003031656500c41c03004410005c0000c0e900c00244180a07282c0c0c5d0b20414811004c0024525500081d2502001000e8080e00c102c1c0205982c080e00752030b410143c000841d40700304001c0244100c034100a4010502130828402c0054460351a14140da0080c40308440903030208005206514100c12020000d085c210b5100b00d1179556014040d4440000408840c24980d450440440250049204035403049282e60780c0343c0115203030203040c270050092201c02400982c40180204480b40e12010055005602907481811a07503510303a11090308285041c11a81c400c8144071640006000b2480e120b581030202842d4407070000000300703010032070310721401d01c0301c14800790303041045203004000860f00e00701002d13515030400c041501c0d41410300b24600d4ec0b0a003041003050340001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 964876951 1250 964875701 964875721
    0xf150d320d03060f09090309030b0702010204030f0f03090e091b06090a0801020417011e0f02120115020f2a12120d0e071d1005060301120201110a0b010b07030512 71
    0xc1a200a40000d45070585c40328a00380440b40d00c4880103000c104d00d44001d10100c0c40c0503c20756400311007480090301c5c0c292640e40348002c52040c0102140c40000300c0c0e90407000c243c0c024550301c0c044c0c258610071040d1883c204101d16614003003581c03800a070303c0314140249001e88404e000c442d0a204044c041240e02656005403a00070b5015108184d5011030305041c45c0881c0406009088008610045c036500c8401510b241c9030007020402c9041012039800c1013803442901d00600b103071340202400b8070604514103440401a0500440d00720400642e00020010204000002a50380c1041c040140424090100c2d03400b094500a00e0460009148035410724906035910240040003508d05100043c0f148a220900d407684e206240d0207000c0e15080300158582541a5881000345d0207a45032100b44040e5a0b2600410041c0d40203800010880c59994440019541c000b01c5c07544d03148880d24014003441c51a92144c42c103840041c041c24800d035100048903400e051107801980c003c0582d410b40c584143c2410000f003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 964878201 1250 964876951 964876961
    0x3090709150306060e0c0a050a020705030a0309060315050319030e06162a0b031302040903020303010f050306090303012105160f0b18270f150d320d03 66
    0x211800c500305000821700e440100e03041360040c90800c1926007440c49165050300c0c25084400142c0031407291485c0010203079400c100b0039842074080d846014035182820f00040603610868041102c03015104420030040e103000a0b43c0c00030064030001d03107801c002c01e403070200c9190a995010503071000c0086203500144040d15031185600c1d101e501560094042072506070b404840c0f4101407000602e440d40c04212441d0203000030361f804406507020b004200700b0380c2d00207030464102500c1540140c1c004001844034a402262103030191008400810042c5803030111140c0d40d20050044c0c12511910100d04c0d202078502c40c000d28001c3c0d9100041d40e41c002d401c0f00c688103400d0b00034030030721504060070040003948040301011140e60307070581c0960f4200810040c003484008820f83c0003010003040081a200d00045c0e00c644043d0041c0c0c881058082c0c0ba0074250746040340101031b0640302c1d214003a55141c1000180703006038100800d00b02910a0f600f0002080d101030410303404004c9415050140e007407a912095415482 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 964879451 1250 964878201 964878203
    0x30903091206070206010608060d0b07090812090a120f0206120403261602160e090c030606060a030504051204090506032109120712031e030c14030907091503 69
    0x30741d0a600e00191000d956a1030545007100940c00820043c403a180c0301d12a119405000644200d012020701d9480600b00501280c200d80080d49005007130054200c24011007074040f40b46035a560500042d000000e100500510a408d00440c2e4588110200219030a8011249400030107650320381d50041040c10306480c0484081300003d10b50450b0009203441114800e0011400081d0303640c280c3d503003950070034600212810704003e61094040d4142c40320003024010300a000c0082150b50941018000d0526280181040d075110380c00000401905440e41026507000101c03502c0c000c1421748550410500740700540206500b020000a00410001d40396040680580c03016021100c00048250425841c0c1000c000c038500300880c10041c6200030301e0000c08040040940c1010b4502690f55544140c803894419001100469110341c0300442c60146039540401490903805d00b440080c1da1000000c2655141150016900101002240c00c0c0c020800c80f900150109000820a02e0540e83c00558194650705c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 964880701 1250 964879451 964879459
    0x1803080a112a160e090706020c0d080910030606083304181b06030204080a0807060b030a06060906050303070b0a05090a0b04030f090b0304030f030b1503090309 70
    0x2150900c2468401d00040880d030424690a20020740c41c502032800e020481c558807040ca080c1520150a001c0c00f5001c04116200f6141440c60b29140340c848841100030b1100c00c55401200c0100000c81e008507000894007021500302c4003400040c544000d031400303800d280c10b030000c040104c1400c94a81561008007520000d840c3d03000f1707a03036451022420b0010209044450040c81e0065160190381c600b61424110700300038004500f940d0142020503030480072400980e403588010168400e080100e500f036201030046c0d440c082d450a41082c5150342d4a107482c903001403440d40000307541d80501c0381035030250308035134801000c0d00c01c10300b030b1410b084020b081d05000c0c06107514501140040c0d43d180c00011107055a81c4036461544030340d1840d084000030070008107008031030b00034403100c03100060b07603111914402c83c4641c4031408541103103803009005901581080083c0001042480080b0303030013109010100d072262a0102c0e03007032602008642903200410b880f002012000c014071212200100c060707c01039400342c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 964881951 1250 964880701 964880717
    0x30c0915020c3303150d151401080a03050a030615030e0d030209181008030c0102030a0c0311071b09110705160b030c0c0c15030601080105122e1803 65
    0x340044203810562111000a0410143c1ca03031000341801016551051107005042011002000890000e03112010211001e1540d18003050721440c1d140300d42c030b05030040780030000311940c1082d242c503541c0d03002c400010b0140440800e000358524401e401403009800d0300980c0c1c3c42d08030a0610040d003c0e08460480448500a101a0621541c0300e4805d848000d031004041d2180da49001d40c00f50340d100000791910b01d00403107400010a1044d01000200704007204000016500d140c85410b00044450042e545005c06041441d10000d8028030b2060752822600203400b80b544c1006114a08010127095200b0100d003410280700400c4c84001e0303005085444d0007041a01d4140c8200c41011491810600a96503808010310120700720608040c09000810b03540b074204c0e00d03195210300c0003480130703020106039010b40c030300000c100005560702c4010300340104402d0301c004c8100c42417880b02c16203c14600e002950105440ba211b004884110f120160000c2c030030301d4007000f194140c071300900440c012101080c3c01280b014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 964883201 1250 964881951 964881979
    0x2508041506091a010521060f090c04030c050603061027060e090f060a18090203010f050411031f0e0705330c0a0321051f051f030c0915020c 61
    0x9108071001b800d111000000c19a060741c1c5030b400c20203800380c0070079040f0480011503611621092649030181c03c84013001c03030301c480c5036250095070701400c0e4220342d0081206000f07100d03043d11100c1035a5400a03103800c0440c3c242480d51405501e602100100710b55401c01e1020004c1c1860f00022050b4018a040e1154040c44d41c030f0304070f0000590819504640c0162400b0300400c2075040740810104085101c680c045046415a00002c0c20345511000311104142ea40c0240810410360204070811880f0640103050355005074017079444400340344005420150303151100c844400c1d0080c021b02c0701801008006007640884140c07803000110031108403410440000700104520401da07010780301c241e120f040007000c50000d42d5904984a404c200300041c0e172036002e00f40488400849001d664800d06100c4100030740c07808040c20307581898400340d01050060b0f1601810703a00f17026420f109144822140c1c20045110a9200c0c0c0441d90704032281e1000d07011445412030680929030100e4882c121480442d240b408140d01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 964884451 1250 964883201 964883207
    0x60115020f03072303040b0409050a0e1f0b0a0b0d0203070201150e0a110f07050f1002040b040b130302030d0c0308060906010f030c0504050d06050105092508041506091a01 75
    0x3d480c0050300701d440b0b003d1113035144c44901004040400390741c016a401d0954030529800a60405e4000c200c11945400030848100c42a04c02d211311882440020102c145004501e04041d4201d0b68081c0318164a0381246000d58030303000c3c1c0b0b00e0001d000704801103940d4140304950701c00a41040d03a41e80c0c015401c110301c045d002c8121000001c141c0b040c641007403019840b0b03800b15500902c4070568888400d078090102c641000700b40000303400074902500141000108034007501d400c1c0080181c0341e0102510500051151000f184140c4040d600e10800301c95588404240c110000215075000a615100300c0c2d0004208603805102c803002c140c801e4490040310349681c4108814000126101400212001880203801d8440d8003c010759000c40c0c01d00500c1c0584500100340f20440e5108141c914039240c1004000f281031038030886034400008542e41f503590402c8201102d00c101c40901c031038104448840410305010a04082c2c20198400b0a801c001c0c09079114213120242c40c80810040101306000801e10075540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 964885701 1250 964884451 964884457
    0x5060420060316031407050304030f0801260c0324070e150a031d030408100501030305040b1c2307080f2208070303050105130b0a2303060115020f03 65
    0x40060109045640351814030f080003a90143d1582003513110f605240d40302d40b0070003000b40520030750b5650554a20305404e01a0000070284504004c02ca1050b0040048000c405458580a0a0783c4003081101d0060510b6918010340300b10070303940c5400346240a44840d051034120325660000350300701030525650010b05640c100219000c07030b178102520340601d1400c0410b803002402c07103505605001442c080d410f0300c40401c200e00d544032000345600c001028040810104402d003210700d1100c4051003035604507600144180600c6c07081d2071942101040000b41c101c80842c2c0600703a40e450b02000c11000c0f9040ca8010b190030341c0b40c072401c6c0c40303486040c0128103403900c40c2446500c60011a25105c405485006107141c51132942046031185007000190100001c44110017000400e0081da408210355040c0f50802c0354003140c96100d0042c0780c0c07400951030200e4030b401c00c0751022554071584c0260b5040411007001c0c00d10b4150a2003540c0750094a0010581100a18070039030280207550031995011034408040381e0741d02c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 964886951 1250 964885701 964885763
    0x117101d040b010509040813030803060109051e01050304050708010c020106030209060f0f1203090d0b010305012406050313020d03031a0d0c030b1f0801140f01030b150319050604 78
    0x41c050014000d40c107000422a400510981d120323483c2c804c0310800e890070060f01e50000c4450141c0081840003d6912803030b444040e240403280c3c0050340814400000c1003030407518902e410722001100080902c01c0a00c070a800405c0e40d0380086c040041d040000900031b09890104a00c1981d1080100340d1a04200d00e0a034440000581410740254009042150514190b01d40030141d1004014100030380d291b00d044001c4151180854800e95411403502500b5501941c0648921850f40005c9405601b28400842c040315034508100f0f42e03d803030b0b0098801048564640103500315810084100415034141d00a00c4117500c0260300904501d003840800c0060b00c40c092014041c400100014400315003c980859005201000e00742c00c42e0307d1880400203c042c01e81d2000c0140d075505c0382c81000c21090441e0440c0c0c080e14007000c4a5096065550b41a10b070003000d0714040402c0c440168482140d00d0402071200500d500e80c105c20f40002d141d182055948104640407290b20101c503034134002c104a1021100390b80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 964888201 1250 964886951 964886963
    0x706140306010309080d1409070e070c140703080f120702030f1b010603061404110405060603070f0207090e03270d02060304150501060507052413020117101d04 70
    0x5500c80360300441c0602141031058a042001b000b150a10703000e54441c036407010b60409180c141600d805051941005e4641c0d002c0700111402004100c615980091481032041d40300c2c140841c2604015000c42c0380c8102900014003d503800150640040e440b440501020060b4100400c0c0c2ea548950040b42c4901444002d508003000a000303043c03618101c07800c3c04d0048204080005102e554031307201d0340103558002c1d0048070003512904c240000c2c4104140500301c54a0256810301ca54100340c404a8110b2000a1101041000d2217a801075058802c1c01000002e1186030341c10710540f55484045a241c5d030210340302e0b9a9022203091010001d200c442200b0039844001406141440d4858003401140d60004104a800c42101041c00556031078bd4400c09019000c0b65032550340340c502070700c3c145140c400c00201111840c041c049030098040340355000ea6a1108107820410b011003440e10040c1c4107003024801c1214012001e00030814194240700012007100c3d08100c0360180b5120b601e1001c0340c0b01c1816503002c0c10b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 964889451 1250 964888201 964888207
    0xd0503160b04052b21020a0c02031209060304020f04020d0e0d020d09030203060c030c0c101a0607050a03261824010b030402011707020c09061903022b050a0302070614 73
    0x1501406401c5044c038000c0304100425034800690004030b030301078980d1f000441d014076404401d60504004008644080d5010030f854048128001070241c000140b00a106a8000007564815100c07501591840740400a043c000c920413a0700c016141d40050704101c0c0144903482c031303802038144a90b0300c4034110307030300500a004030b911001c802c03014940c0020f01401008600f040441a00c480410550b05d02800c0c40030f0014104251305441da003200d020307a18191041e401480120041100424110284e83d8181071140411440c0301000c4c0b481c0e1000501d84040c0a0380000f005180c05410340386c206103900010607120740e10308403601c3c002d000c07401504451007001e4132001400101074086c025a0404d00504040c06c081640c0d204040241e01c0481e0ba20005810040031100d4074103041e100a50483c1044844000c50251024040300c0c5201320300c0040d10842d00090b5059001c40c07002003121740396118000e00320302e451042c10100e0b51502c179038504400500c02d081d0002120745c41000e00a0094540743c0c0d007189 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 964890701 1250 964889451 964889533
    0x21603120c140d0c0903141b01080712090302010b060403081201062c0f090403020c040e302101061103070f320a060b0a030c050d0503160b0405 63
    0x604c002850132007401203407200840418207200c8045115009172004082601900c0082c00b0761040b0403103040d0511500d03a080c481300c030f40c006107007101000d2180d1b000108482142022409862501070076500420000303404070601c0304880091240d4804041032500590fa611000c0b507014150010400c1c44032500410155048400700802c02464402001c040490030317101c000448108050b1000c5001d079110340c2c0e039106142840d000d402c4001400101420011901004800d54510001d04414540c0e5207100b02e48000c01d105070558450401d0001c1a400025015980d02a0180301380100c001040181011010743c1d0340000031586400e904c01e00075100e20b00d151b40c8190420003805140c2c401d006ca0a203040a882c4488640e01d01e540709600001c0146450500b44201120700300c00c4401d000d4030400380c003031003c1000d03c200d8104485096070464141c5015041140c110700440358100100d83e840c049071824490158030060250b4000d6040e500319814050180d03034071078008100e00c4528040c070300c09d0b08 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 964891951 1250 964890701 964890727
    0xe0a0b06090c071a090c0d02130f0f140403122d0b090f070f0302030114061303080f13051801060e030a1a04061508060c0a03021603120c14 61
    0x1500140c00c45192410140c40750b80b0b2070011420321581d13203c0050004108030348040c04000b54160000d0684000d04038088507008070304c3d0400c00003a030b40b5405480302501c61298503c1c0e403107403080b0004c0f290100141102c00c0840d800040d0181c406400080040d500c0c044040e00d940320725103100d0054441580d0303048003411000603c01000c6245a001e1799039215500e1203880740a80607100e1211025030020503d0b2261001e0711040300e1807a450101441403005100030340c3e80f0f0411100525040b2280740d00d0741891196103108041070340005000c0c1c5c1e000b107820920010010082c00b01c0d400001c010f004c403192203500740300e01c48044031350b070807003440d03900004100042c0030b20038a502c2243c018054a81049403500c44014140c40c3d1071030079642003c000200f1050002034071403030100204d03511410b121503203001c801ca907481401801d000401440000c0d0313560194003c1e030441c1c5a04c0b41c1100891800b0f0380d01d00303020700640b64161000820604250041480603c540340c2c00d1240b0340410903490070055091401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 964893201 1250 964891951 964891969
    0x3020607140915071a0103021017011a0403140705130e2e020a210b0d0308062116090606090618080f03131202090403210516030e0a0b06 60
    0x4100019020080040410020355821001c000b5034817840b01a54554410f000c107007036983c0c09a80401c000141d02d980c8201075100840d046a500041301101e030403001c0315803046482580c2c401090301054550340860114040b07608021246c003100c1c01d00009008032651810f549480804940c00c1c5c004c0885800c290604440c50a80c498401c0040c080c03500b400c22441040340d0141001c24003103081c0c2d000611103e9021004680d0821088078103010000a120206100203481d9a004081c4902900055141d0310b500040074052400e649400720504511245a034803480c0d0740c5044404404050030200300110140140e400716006952821000c0c0d20300b010444210424503003038040c0400070300000030b43c00e10811400c01881100005195034444564111381c0560b0146c0c4007c0e902069030001c0005a900e116402c2d030b0046d0182060800d18041180d80b506002800d003901654500c1c0c40306000c0010803022020400d4443d5071820000c94121030007d541d282c840280082401d41d0360000503800781088401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 964894451 1250 964893201 964893229
    0x1a0d0509070312500c07060305150405240301020f340f0201030c0e090c030106090617150102030d0c0e042d050702190f030206071409 59
    0x292149251603a07140c2c08940220202c0800180a42000f4940c1580030a640040ca14246041130b407030190151040c41c2c2d15200c202d8407000e44604040b0444244210000c03a51010741074000e0360100d503150400a4020003080c1d554a81610301c0034260411414180b164601905030801c0c4800c010817825548a2151212482da41c1c15540a010f5038841e8220403018000e80f00c01e140342965600782181c41440200403040c0c1140c01214003100306000301e5400185440700540a29002c640161100415184216900340d03940d00030784000100100b81c80303a200554141d0b1680e598641070642e07507480c1281c1e0140c5541030305011002110104407140380b491102c8540d0401030054900b03045800c1058000c407401a101d14000c03c0d0385003812007052500744500c2c2901711a402481303a85001c449113008100824028a94002d55290085a5064000c0100d41030003004158401000c4030107140c94480305400502c110094803642001c40e455a0154030310141052010082c070782414500c0080040030846262 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 964895701 1250 964894451 964894453
    0xf0a081e1609080a0b180a0b0105060f04182a0e060c12030106020714040507020604141e15010603061a070305040509010611150132030f0601060201061a0d0509 70
    0x10790f0075424001d6003109070040040700342074949041c0c1c01c91220240840003034075822034604000051b0178602040d0545409442842d2030f24654408130000344226000408080f111003055030304200e9a411551000b1403911800c0401702c84416000c80200340d9610f99004a0a400d00856a50401c03401a0107204410001c4a441c00844c0920507419482030700310400581060f80c0c1807161142d0040c005110200555003003181e807501000003501c410004c0c100403d0699120480c6500c00350030401100411040c0d4160031820065241043d40c0c3c00202d6a65031910440d000006032180c06403040300c0440b032440c04000036a020014040c0c1403644201022004e008090002091b2030300c0e11003226003e04065100c4200c2c8012489010307103481d401420361580500b0001c018040c9000c9062480c061640d0803111941610049151030445000002c01c10b40512601c00e041c08511030005405040b107000d60000c00955440e80d040061400c02e964054040040400810001064513400720b80c0c88200340c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 964896951 1250 964895701 964895717
    0x15040b24070c0305060f0606070309050d0f0b1311060301031205070f061107030809011505010302280915080708130204180c08120304020f040b03120f0a081e16 70
    0x10303890032010701c0036070410307070304e540c064001c110440741020704003074000d6012550700d0704203203503560700410340002d40c021507010f2400a209002000f15121481c0e02d4a40e1000c0d0400c0c1c14600114075084d614003600080d500307954015400300440c180801201d040c0c98104d079452216032810707132003903a0b198003480d411502c1400d402c91036404582503110b00f035068881200c07200e94a88541c20001c0c0a490041d02c0d61806034506070810f01c0d003240d03040e000400c54101b8203000d80c454911000c1c400d407103a1103500d00280790210b9512491000c3c1e104004001340c90916484150008440f4421030b0804011038060000c00e2208012500249101e0342e00164284020004144004040107810011003034000403030300c025600b101400000003e01c240000413103107882071070451405800051949c0c0204001178015542ca002c1e0780210303101881903403200c004224845a442a00b007801e00d16a0380a4094140040c070580b02150300311030380c2410346003c84503102e0b044403151940f00b0888112a002400c41003071104035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 964898201 1250 964896951 964896953
    0x10c20130203070c120e100e0a08060a06060f0809101a030a060c080105010c02091906051c05150601050d0f060801090302011406060301050109030b060303070f05030315040b2407 78
    0x10740002d5105440b0340d074900040201e90302e418101d002031440f070001801202c03840f59203c0d8860044c100310550145c0750001c4401800004038000500c5034200f00e10902580c010031a0415240c0c024008a4200b81e5425007003400b0441c0485101106031414840b58004048082030310905400c01202e2a4035070307141040154004000038504002070300115281526002481d52858000101500505080c00c2030750a01905500041888a0041100c00020b442c01150509000c1c0c40d440340b00500000703010402482e8007641440d02078541c464046500b07101314002e400050045600c140d024000603140d0f1810f101c0018100750161001481e030300c0311a0396845c000102800e00b406030340390242c040d800000f014254005910b45140380102042d010300020001004547d902c0103820044070b4011500705116103c810001e400c6100d00c0c00301400103ea00015942403090120085004400007114000b0f0110f40000307104c2035902c040c50b09070f40302e08840400346144c4621881d03031210f1881654014903004d45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 964899451 1250 964898201 964898239
    0x30c0c010609050f061e1c0f0501050c0c0d021506040f090605010906090f110306011808031c0b09010b0d0c0302040e0c03160e030303040f08120a0f0605010c20 70
    0x3044592440e4039180b0818405981007054660340c0011407110a4602c16506c0c0e00890240b000c10040d450036511044d0052003803055400701e520480354018028803190038040356107905500101e0403601c90303000d85000c040c900c43c0000f4488044401d50104000da907600e4408100c01031041c507403840229a180e51054000031301510601c0e01a1002d07100c0064118201400f00d404c454500010289192401140c008603551803015607030f0001d003d19100b10004c0c0f207000c0060704440194840b00c440d02c400b00d821802c3c00540080d4404d07840c9801030800001907103c041100c08c82007071103000358aa0080088010306005a08045040010350501518181d646d80380311800c80401c82d04501c040342d0100c20300c0180d40c02c090340304070514540d26192000305c030000700090300c07444083c000800d02c410780017070302040144840a0302c3c030b40752174030145082900d030050515018111030036000a070b4910300703031002c28298011041d040c201500030074131400410401000c5141004410301d0503521180510080c0046a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 964900701 1250 964899451 964899461
    0x307051207050a12022d040b0c0a1103060403121d1603020102011103070914150304030c120212030f0c0c100209010207050103062304020c0106120c1505030c0c010609 73
    0x61076a440664880810800400030f403491464030b046240100500310014124464101c07500d01e0250459a14480070411000a489258402004d21102107403601e031010000c030f0080f845074011800340400380021010142c44420860b002000300b400402d0107000c032181c0d58000421a1549440340801c03051443c3d0840c07410700f503403801d01c04034420341d0380600c21541d080c00f0f01d1005601c602211790540c1040403010b031442c031072805650480c070346031000040c041d07464106015002f40c5041c03c035035880c14203007801050042071510030750b00000c84240c040000392002424050000084420601395220101a00c1c0c007080082d0a0a400300000d008036030344002d041c00340001c41440c2600c0160b441c90110f00282c1005a66406a414507242c0082041000104045040301034955030fa6480c851010301d00081c000c1c02120040803141d0300e441e4011540580c0f510440302030b1405000c0f00d0541c01c0d9034880ca001440003010300100040d10600104c1c112004003009405004e400d20008038260f626412210308443c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 964901951 1250 964900701 964900711
    0x22030807110415170f070e1605040902030c0c06010e130605040512130303180b16050a1509060b0f06070f0c0e0c0910021b1909060303020322060801030803070512 71
    0x50b1107182c000204e00c004000f2104080d070307a0f00140480da8603114040d0044940200ba68070003405403020481d980c0e10540c02c9601806603440c04644906011051068a421483c101c1010b48117a10010a080c00d4568020f40f10310610580b1301c00c0d03007400380d1f60103001e401d010701f01325090311450200000f06054017002d09a03600c0000c00388070f03003685142002820035002803520ad500000e0f0410038000381c00984105c440c9042c1003070541d4000300c540c5c60440d01e0300c042c6080203090740b59081c000f090045050340016180741c2c09410140000342c5018100400c1205125015600800801c945c00020340c12060800d68203000341200010985c5d26a85403d4a103030803514094032400c0000da0580301c1c900310622002d6110244002c100c803c42d10003203921040080c0c42c116100e116040c801038141d101181203013001d08940c2e0000e101282d030740c0c40c0180d40d070380003c02c2011002c01e4400d0311552121155003c01c00b140c01a07681e0321540d134610303151001c140c0c0c00985071908001c020400c200006002510340d500030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 964903201 1250 964901951 964901969
    0x7020a14030d030504020f09190939030b100e13030840150504031b110108150402070b060a0503151501030207020a090222030807110415 60
    0x103203010105824101c880091505040c5004180310158544120307140c804201543d2091450719184c035419039500b10107840c40710550905101c50108045000c1902c031340300020342145807104020100000b00c4589080850301c2240300002000862210b1158a41108000610350320703154480000100c5580e040b9125400c20890803c58000c165100d444141c2c0141000d014480c10404440103a4551104512a0500f10703100b00f104a11500c440d1042c880e2039511040d540703074106100460101030441210180d010884403032454501d91041081204942e62103600211b554500c0381c019240c40201404024080f608100c0408168442d4801000020b00420140265280507401c100030184a90400b074020313003005468400101d200029140c010b0354030410201e40c0725600c0c1c0102c009005a09010b54041740082c40046c0044080d4000c08003800c10801e110000041446802d20401061000a01a0408105c00000314400c490010481c2000030b0000c01c008054400007696025981c2000d104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 964904451 1250 964903201 964903229
    0x73c0503030403110a12050604260d0518060613020a0504050402070b04020306092a0f03151902181e04050c09030610060906050f070503030a05070e03010501080c1507020a 75
    0xc91038844080802002040380c03c806e0120f640d40d51589400000e80000c1065070a5201c400131040e0b40000d00310390f14103511649480e000d00d01c07a08009000c041cac4000d4001040c4c12b041280307111003c910944900e00c0601229990410f4140788402980320184400030800240030110f5182c3d281d000400005018a02c042030038207007801052f04116010700a01c44c3c1e41d011201c0c03004d000200041c1800d15030600100108005c1e04640030031111172220a8042c1d00d4002c00d003101c442040d044080c81d0250514142000c0400c50001101040380700702c00c01460211960441401c840c0350142c2820388500d5140b00a000401d080c001060a442d8151030601483c0c6010a182c402c6080c00c009660b8040e03003921071501341c14034140c4050300f0740403c0e000d401c080000000314690040d01070b02c200c0340d0a5038010100c81d600c0c600701c04040c00805054980f10001242200c141c41075150500449041e11900c00140030101130620401036030700310001d01031200322401e10a000c00342e5580840000281030301951844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 964905701 1250 964904451 964904483
    0x81e0f07030204092a0c1502090102010f020f03160504080a121b14250509041b06022b0207170a05100c3207020105070203011d073c0503030403 63
    0x8080c03017110920204101c3c60719a142c000c50758000102000410740d03240103980b100c0c03460040380580701c440c0003050301500000350388000c172000780002d5100710001c540144625104480c2144c0f54861803244201c55804003c80b00045001100907205421450400a407070824044150248a801a40544004c130307444400d040c05480a01c5408403d4000500c400b2100208610000704140c4074003c00b03004100a4000038100006d09009140303031941c2c140f40302d0b01c10b070343c510000359140d01e9828420100d2010051000c2152680340318164541ca0540151000901b881a42c441c0c04110190350f032501d20503241080c011680511007034001040e1814081254a1403a0018051120300040005a0641407100b00c0f15681e09034080100400801d000ca5541d240b54001210580501880030f9030651030542d000c0d15442007098802c0c048050801038a02440e034450180030704140003580201444203c515104840155027128441703000c03035010002c08183c4840c0401c0c40c1d9002078108654030591540210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 964906951 1250 964905701 964905761
    0xf091e0c080f030d2c0304050307121e02011e03050115020a020102060f07030b04060602010504030e060a0c0b04061d0303040c0b071703090708030316081e0f0703020409 74
    0xc00a810a18020480ba07140c1c4102e941c0d4030f101d04c41c410291182d481d0b000170404413040c18280e00102c150b00c401034881a04120381030720b0382c1c000c5c803c3c50303c030344100e45000480c203601c2100c000615810410781c841803044415a28400c0001040c120704002c1c0b40c2001a0140c900500c1260000f1480d540004142d03040440303807201d145804003100159070086070140f0060303030f0008101d43d01850400e4032200742d440b4080c05070b000d8401030016a038094108030300440e03c10340c158402c5204d1800307503464107000c0e00c0c05400d124403840703150740302000074007a030782c03040b02261040e500315403c40c0c0704001c0005c0c2c540d00c04184100c8801001c4418020390000010f01c002c1c0803441d2280c10160110651091820400d60743c2c0d808130f8065100c0080e40c0180110010b00003480030301041d4024500d95090720795910742040d0b0200001001c4000e032010445220105002d074804907148010035200301174040c9240c41c2c1805003020440014641c408140d0200000310701a11140184220050045402160513120305006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 964908201 1250 964906951 964906973
    0x120a090e0105030606150a03110a0302030405010524010c030c020415051f0801060806010c0c0602010b04060f030803070806061b0c011716110c0a030c050f06070b07030f091e 76
    0x10503c40d070310800500000b0740d515070705070b58141c030046000395a400b90203801343c002e4101070401a0705248003140160035250540c0042d4490741c4990002c02041c1d448080a04d0303201040300d00c03407450102895071020154003411711041554005d0a01700480742003580041c0980c2c48041040f03480ba03910500400003401c207405140101c118001c4000421420484000e1400c0c4051240c80300700840d210210305141d005450282003140c0000089405986910000e8040d0100d00b109600980c5000c800003404c1925000d079100b601e51291076280b5507184c1240480d002e2101405d00c552161082090400f0b501990006042000002c009807034220310300c4e0000f504510a04022a841a52240070005454080d41c03512841d60894140501e401c0e0306050300601d061001e0b615507400c181881404402e01048003101c104964003182ca21800c05441c40520403a405040001003520b4a0304022a601d503009800c010a8600040c0c2c00181c0310040d602c860b031081d9500241c420022a40f052800b043c8401e103503007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 964909451 1250 964908201 964908209
    0x7060908030f090f010e040905160b0901021c03061e08010f050f04020d05010608100b10020a1e0f0204110c010f0506030a03030e03040e160e040c0e12120a090e01 71
    0x40c5040c252552402c800e6880b0b01214a4407981c40c4100312030041c1c2c01191500c4942001030020003103c0c040d840d19030b0307603444102e45070380306605150703000510040c000c01212001c0006034080c0840e810304140d925501a06100c3c1e04003030607111207000c00c103512640d981e440f00b0144410b400b052246007240550849007140072000169040c90104200300812449031600190b05981804809071981002c07801420344e5003100003d0300422819030f02d651000d41200b00c2840701103c4050520380000c9042e0394500400c10024449140141e0019182e0080d203804003045004165800d4000c1c0242e0020b8100c0b61381d146294645640411802001c42007482101180100040c0411190a0200000742d5a002c403450003010151908041c0d40d03201400e100351002840800c282c0ca6103404c1c8443c808121030401510000003034100c0c078984406292500502524960507200c00782c030441a50240b1140c442c0710802000f084c80b404059218410318034004104140042d5101d080141c107040610b0200c17901a40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 964910701 1250 964909451 964909453
    0x15040e060d020f130e030409060311040c020d1803060f091b030b0c0d0b04321003151e1a0315060d2901060e062d04030f0507060908 58
    0xc00e0300607202c0c20f002c401512000c81c0c141c030105071000700030070280410607100070300c6000110700040d0a0301550480401c2c1d070701c13619804040c200000203002c2114a00d140c800300603408902d500450b9405a412841420b03002c151807107020740ca0f52922001d07280006505405299144082401e2180031b04082e000d9010000c0c040da18a4510b4890030184000034218401100c400134042a80d000e40f036200e1203809501030400d1024074090010410b186141080c828414040d0907540082030314000701480c410720740c0107500340b0010b04580310360306100185009900050343c1e405012500320407540c1c4001c4920b00d40ca10109188601ca002d604c03901030300d00c0140d40250302c20190042c01c807600035141d0790302c2101912a201403200d1403c1a000f0f4241000803507400b500c040380c10100404102c1d040c14107891854607425442c3d603c0d1414004544a40302c00d4482113400e0000411400000b00c2883c643e50403001e4190741415103a8032003007250009404101c5165008241c10840d0380d41204c0400010103400c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 964911951 1250 964910701 964910719
    0x140307120e0307030e101106010e040519120804030512090615010f0914150d0506180c0d0e0f100f061d04060507210504021203131701090215040e06 65
    0x90390140861660350021446210403040c1d0009a0303100d102d000702d1f40b00c02c40007221b130f442d41e540c2c1c411614990191070a403424040c1c0140c0d074000c6010980795883c4658081722090054111074070407209814081c00c210200017041205d201c540545c00740c00d5000d102900060310481c02c1a0030240002800c0090300d50503c59194050303104150071036120070881c1c4800c0c0c025044882c8120000740401c41d0b01407411310205010444132220001070380032611681c070503100440034241452010342e480208440c0b02442340f03005c011070b61080103190440c10300803001a04403048007221803401c60606c9120308852070b00c10740e201c8002c000d100700c0d802600010403c00c0704240189818a82c12040800000c002810068561010940e81c9101e14052003c0b80450120030581c1c0050400c451302614060710181e00c035507550440c484070503c2c044101e80103060390140b0301d45098130745040b0018001400740c0085d080e550781d00707441c40942c50380c850340d0144082c5200c2256885045c00404040500302912240c0152100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 964913201 1250 964911951 964911953
    0x10515040c020c041d06040507030b0907030803150f0a1508011d1b0f030f190501061d150c010c1409060a0c0204020d06080309040b030f0303070c03140307120e0307 72
    0x481c2814083e4020f490108030301e50303586802c1c0700702c4d41c070350000c1091403045000300720910402041200070f491003180c0c0528240c44042d2140c0c4e581c8010300000d05000d0003000402d2101c40134807640d0804440c00752005854159500001d80020b100340d0010742e08c01c210640d401a496402807446014203456144100c11303d900e0612400c2c02e0b4002002e03c180b0101b40111f4003092180301701503915100c1c06003456a92450030009030601b0075820303911403a40111590200e651018a801002e0503505c4580d40c4000030701c079085240812008181105410102a0041110320b68004c00140004c00740100080380034241002d00401e00c0a42144142c140c020620070342c0c04030f940d00c50840710044518604440420481d0002400078881c103025041094500900040c0c075800c04005002d40d03a50880702003016464070018142c40d00c031a000491f099810410003d51782c2402000c841a86900a15000d003010707109c03115000c0c1d00c0c3e105031036580100e21a0364043d4001e520600606c00e4101c00380c0301841c00c00006d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 964914451 1250 964913201 964913203
    0x105010e0708100f0906060905030a0b040213060306050108030c0c0907050f0a05040b0304111005040605041505040b1c1109010c030807020118110a170601150e040e010515040c02 78
    0x3024060104100e9a40042102c0b402c55201107405081030381901180c0c0c07903413501c2000080013030303106000200b0640400000c0070314011440520b0f0369000102c840003641c4950810800c5c080a0956001803076031007034040085901445220f01038074660001315a03600c100c5951520b0110722407035a40c07066141000700f0440c240d005084d60a0307040d207039210ba625a0606039050394103000e50f4224080c40c0d0000300800040c824086404610790500b134603050030203400c0e40303400c940074420784c081e04004c954104000c000f20b4070011400ca151b10100d107016818240c98040c01c40180c0d03c0304011003805903124084d6014070310244200d100622091003114a8800c40c1c0001801c1c4108055000d030a0085420000d14039500030340014112502445007007107000e01c1440e01805c8484440611030244504c180d002c200c010310030040c0e50510150710028103050f8038003407130000e0200d00c55104d4000c01c003c8610048258840c2e01480004c0100c00002089600d400b10084903491310200150348102d0510b2014060030390 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 964915701 1250 964914451 964914479
    0x2131a0a17062b1203051311030102040f0608090606030304051c1406071d060403020109120f020901030b07170c091504170607090609030c090c200c040e010501 70
    0x80103107844070203944500001d10303900c21a40c480c12180c81c62000c90b001c02e65031800b000c600d162003450301040c50800e85400b1000c8a00450320218581035410b00e00001c44c60b15120107d2820004002510742500c98030903010003405a0300075070224203030f9414071030120014030101d80c0c8050140c0003981040d1410740021440845071032640c000c295a00108e405120b1050110803001044000311252400d160600500300d114204030790050448907480c4155900d03106084a0440b5016500d210249040c48540b843c0c00c00b0061080f0356035110002c0c40e82c010307141d00882c54020b42c000c2001504600c0c0071a0050100140c90354100c0c06023200c4402c1080b00c0d00c041042d034804a03419034141c03d202e2106414030a1520464011004000b40d41c06544000000080c203244102641c3c2d0705c3c070003c0340d07850400b51003a41c06400000c080e6140d044042c00310300e5260f0b20001d01c10702940341018a10f800122100821001c1842843c0035800010742c0240c0c6c0c4c102130050400041e5100d00070003031507150001c1d180080c8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 964916951 1250 964915701 964915727
    0x203090102031c0f0614030c010903020306010b36150a0c080f040801091104060e010305030d0b0121050103032c150c0f15130b072102131a0a 62
    0x1e07600c045451541000baa102c4d20b8504e90a12081040d607407281c1441e8174010080701020300c281302da130586003425440b42d908002100e50160081c00c150342009415030041d003180300c02c1c04a07203184100c81101c441c0c6007504d20318041c81d010518001d100c1160180281403400401c540c05c504d030100032085110b54450390301000d1a40002d1407070307211000040018001d10603540305d80c00c01e40c20005000305128600b11401844001110304108141d40d40c000d039a4580c0c03003480003410f240c0051040c80c50785640ca030001e072030060051600f6040034801040b07a40b11002d03603400403101c25503200c0050041581203e4000603d452140010b421809070780180101a4855004075009107002e21050302200300840944d4105045281038513003d07804407110a1b6074089401d5010102d1a03c0804511906008290040001e40007402e0060350313038a440055821203900c4403160303010036450007001560030781e42c03000e08440c86510f45000b4400d45049140b440480364956110005002048101c03800368001800030585 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 964918201 1250 964916951 964916977
    0x2102010c08160311010e0604020d1e14060702010f02040513020903030d09210f0503010608090a060203150a140108010315090b1e15091315060e04030f020309010203 72
    0x150307140481031070046480d00c216001d6009403480405800000158034101404002c0219403481142c040c1e613200e040c1d5001c3c0d080aa10494500421900400c00c0411040c4a08012201c0c03075543c0c41e44101410112400488c0d00404244040158280518042001044000c0d802c3c10705110000d03402500503484c114a46a0000e03421000d600c0a2080e40d001c10844802081307408454101110800c5440f00580d000796801035401c541c01e0b02924141503981580e07a6840c0c1180c0c20484280e4001c400644142030603c01d0461000000f00540000c601c02c0011321500340d0000d0900003417051028140d0841e002450000f0440c6603030766400347c0242d04480d00030f0515003404e07002001d450002c01d8011009005400e10b8008c000c6014100c6207003030041d60005040c507086555185808103d03d07034914405910900315004150f843c4810701c1e502030300c40d000304110802d4021850f1785004840d03507540032100400d44c5400b0802032580240348100f0348400d6001542c90001d0b02e1000139168800c00b0102440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 964919451 1250 964918201 964918217
    0x3060103020c0c090705070b0a05010b0304080706021210050a050f0d032102071b170d0f023405030f07060f260f060f010c17161407210201 61
    0x31008202d03210a40f10081e0080da0141060100100107501a40b0142c3e8403008610110f115041300e441001c0c101c854450046003162150780c3c400340076600204055a84070380a000003900414201c480c01d02036254000a1369609260034103100906c2e41c1c9a000c148507180541c0b01000e152102c0e480341220319410314003e0004d14000c102c170a032000b491800910454030105905c0100140540810b40c200d1204041d00700c030301c0d59a81c2504541d045080c090308180c2005c042e00480600a0007071013406000780c01a01c94400c00c640e0f06040254a90051600310450302d4240c04c21a1804419417015001c1500908400c000d020041a66880355102e10801c00c207008069900e024070400400d8a28980c5400350400ca8400c1c0f8a10113415100f561000c005278424400b040b510f1400400d8421134050684640410540039280c86e0f00b202c0c01c1c0c03040e038100402d0030000d0180b46803041e056900795502c684100d20b070710442a94182c2c1380004a0300000200840c0c540c0c0c50401041440c00e081800e0750910346044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 964920701 1250 964919451 964919467
    0x105090709051e01090e01090c142502130e0102090a0905091c09090e031b030901020c0420041d0a0501060915090b0c010e010f0903081b19030e210306010302 69
    0x151750000707584802226495107002069011345600107900180065030381d40d421540b9181c41b10120302c101d100c850100b5001024400d0101c403000e031100b403501c0c001049002d00301017801070350043d2240031100f001d260354002400f07006454070b010610094444554200300310b1030b20b504050750340c4c1b40d41c414401c041c1110305200390000b40308860110203000011000d00201c043c1540403030b540d401c00e0380c1031006180108441c2070080000019103400c500e0581c01400c803600e043c0180802407041150b0308060110381e00d00100c00050507001800104122481c802001c41e17140715140700840d0241100c0300150606c001042255800f15010007070340c0030130001d00c40c03411540b501524000201d0b4451741c103844004c900c181a4450650048181c045800e00902c1091401f6204604807070b55101d0080204101c540420110f15545818000800e01707185002d1408070500c0c80c0507807904028403500b00094444a070400007140602184030040200c0f11040041211020040464000101024109a03000c120342ca = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 964921951 1250 964920701 964920707
    0x30c05060d0603020d0f061b052a070806040b070504080703060b0402070b0a1b020f06070315080f0304030c270506040204030f0b01080d140306100509030102120105090709051e01 78
    0x350390062005d07101036081d103000b020321300c28128142da1080c5000030400c100c200300c00880980d20815a28280361400840c0095200880d190f0500f00c84aa480b4100c0c503601010000304014000e041b0081101d80f41c01c0c58040750550004244208204081c00104031702d19000801c0010703130ba80414040f8244407583c0224009008103100603103c0181b0364207000c0c1042c3c0302d07888030041900040c1c00341043c0c3e020442c2030341e81e084900c40d01e902c50f40c03009001841a41c803c1d0701004405249103150b0303e00b155140f092615101030b5032903120064200180c200308010080804c000100100c3c2000c07040d10051030303040c00000140921100a141c2c50704001010f580d82e80d4102d601441d0700240040d40302c0240c0c00c1800c2d4458090013120344d544118000024413030b0080c3c01c48048001c81c2000306103940d03540000e019032086110000c2d010311409110f60001c07641e003130004c0c06400204c00403011b1298503041c10854141e1001e0020414070089510600040d00d400e00741203004012050034424814400c8012 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 964923201 1250 964921951 964921961
    0xc030f07180902041e0507021b0405150a0b1210050303030403080a0b031902131b0516080f0703030b0a140402030603030918040b160e131401060201090b0907030c05060d 74
    0x1d603c10720700b14003040401e841405d440d90b41090550100460344d95140140da894201d14200040c402c81551000703803900e01500003a6004903c0c10700e1005890100d004a28a01450f8020801d816404589188660003134a0303059404404080c66841441c50800400c2d00c070f10002d000a81005034000c000390840f03919400a1b5811200034040f034041803140c801b501c2d0744042401040b0300c00d400c0340d600140349030054001d00c040a00c100360355000080720804250f40030345c412004114515154004100440d0701003004c0c180869000c102c240d640c5031680b90050844034400407080c0b20b111032020130f0100d40f40e03240c0d64603280c990541c0c0040c0e0300e0300c5035000640346004580c19190710101060a81d60742c618407403612406140300c0e2440800175160403411000d14140c2214010000c1e00007040b095813460300300b4504c80c2000100c5000104056181c40b109865207090b008080541e4407080400701700962180035584c4002c1c4440500f02140c2180d50301f001d0b0004910545210715008980300c00c400d80c2a5200b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 964924451 1250 964923201 964923203
    0x1020715050903100b030705130e060a09030e010c0305031f090603111201060515031306051005120111090607033b010203070f08131a04080c030f071809 67
    0x490340a2081149005007203070311203020603009025416001d815000c25009040d10a800100540049410801070020b0b90000d101d001041c2510b402a00c0740040c0c041c003a10340980d64050011819641504000c0c01421544816504018241c413501000c20341c84001c3d0b1f1b030020003011481400300e42152032800308031920380001810500c2c00d00c00000708400044a03803088041a941403400001040181d0300301c80c058440c6030307001085c060504c980741e000c4c1d50081d648108000201100e668950721100201c59003210b0000317410409030014440d503d804400b201014034410001c0c0900481e01511072118064190b030980140b50104a1108042c0a070040311940d400540c0b807404400744144950000c1c5032010f01c0316028038110036540400d540701000b150310f002c3c0c110300c0102d050030850340d1311031440c2c0c802d07040d1314a54104082c000c1740d9046500b0074401480047c00942c3c1c0c40b03034203022425042610074410300b80310364003220210f04214804a00c510803036021061240c088820610440702038100350038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 964925701 1250 964924451 964924469
    0x150c0703020108191d121908070909090c170304121e05160302040b0f0303031308040f0b0904050109060e0f190903180e01050f0f04090b04260405011706010207 70
    0x1d26117050940c10782c0d9400068402c4005c88040d400211040003440c42038841403001d4200c691709a400c0e190180c0030b038981040191508181e01aa501ea82d2001c883c00c884003210811305d0030800700485d800555034161a0bc42800145140030700e40900040d0a000c40e0320b004101c600780d0000119601102c036100c8118a82100a940c1d254000c0040b29400200342d0208038881c0b0310b8440307446004d040209152010540c0a00154916150134600c082c0400f02d080d01191031600411010640b00d1101e0817110080aa9102d03450716200e14030200000d503141604280e0380c09203458000c11194038880041500840b00c000128580c1d110351160032443c0f4010110302e40a5414007403008101584070100904c80702c500b00c070340f000840d00c4030854200c0e1740c020312405500030b0403102d5000a80c9895031300c564a840300200300243e04151a91140d1450908840544e502e03240e9404595030001d80040440c6049540c0b44280d141504060010300b682c0030f11080b070300c5a007040d100060310300d0b4000c02021000c2d001400d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 964926951 1250 964925701 964925711
    0xd061e2c0a0501050906010e0a060f092c070314030f030c030702010222031a060102100e070f0603060e01061407030c020d050a061d06010b07020906190e0402150c070302010819 77
    0x43c032100da0f80c032020702c6404115010800010030600c2701e449800d064501c922301c003403455072500300c0210180c4280000e0401e41000d80000106c1021081280004040c0c403030058594a891400c104440001d440c421583c55003040014074507a4880c8411240d0006440a0b03003a103075150401e00709e0081c06041800040b0001c0f02c0024140d900610041c14220781c804c0c080d8134044100076a850000030410354405026900070541103a80b0001074214201e007072410002c0b2106207950306282000c442040e0310490220f036484034240304401e0140ea071070740904820308011101c08240750546e96144603c000203420005004500001c41d0ba030203030600304894010089030b281076564104540281800c40c1800c10110010141d00112071021914504031403031506c0c01c41c1807061b02d4007401400c0c0c00050849501403812b0001c803564400380c4030710602900c0700001c480307590318240c4144170288495104003200e18074140500c4100340b000240400580360b0a107003035203a5807180081130024001540c2c10201c214204 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 964928057 1106 964926951 964926961
    0x4170a140d021e1905040b030708060d061407020d1121040f06020a0201020d0c020f1e060c06060f010903030206041b03020d061e2c0a050105 62
    0x420030143c40c01441c5810b410401e0400100620003c5004c04c034100c9841c0d22005020318030350709050035468141071040300344150000030280000c110a04001941e42e49403d0003000095901003818007642c04d0820304160fa1a00c00c035442c00061040c0417003030a8a5102d00881e07010711000602800459040084240345400502c5081e20300c00410840000c04041000900d4010072050307011707121481c2148002404e04c1312000c003150800c040c0f803000401503607801000840d07006045421643d40a008603c0007008140404140e610402c0407800b0441c8480101321148074003070894140400700ba16500656800c1c419002c0500143d102d10000383c00a000c0700f400140c48058607010503031255903980014042c83c1408001c40d1802d445900c14031000d18240c1844c4051070310940140289a46170f12030500c4506028143c0b900c0c00c1c0024440c3c0105034003032124142280d0098001e000a10f00 = true := by decide +kernel

theorem cover : BRFrame.Cov 964748201 964928057 := by
  have h0 := BRFrame.cov_init 964748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 964748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 964748201 ≤ n) (h2 : n < 964928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
