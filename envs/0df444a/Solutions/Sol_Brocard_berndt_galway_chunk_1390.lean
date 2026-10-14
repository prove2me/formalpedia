-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:44:24.898378+00:00
-- url     : https://prove2.me/submissions/a16741af-d6e5-47c9-a18a-5e512d05c296

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 249820143 ≤ n < 250000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 249821393 1250 249820143 249820183
    0x6060e060d0201080c04090203091c050a090e040c030f0b060f1008040b060411030f090d0c1203050c13080307020a0f210606050a150f0f0c0f1104020c0708010c02 71
    0x80e030011100018080c01c03017074030a807040001140300962400114030540080780141a105011864030140b000350001d0401000418030801d881d41c0c1e032017203040301240e60040f843c2c60aa02c45d410280c00c4220305600080c1050103449203101040020340546126200848604190b605a070042c094110b1481101c00000b0310842c0000d00040c1381840c0954020303002800c00038942000c48400e01d0756a10503213040440b418008100900528100070604168113140f41000c808800c80c2e4540300100602d603814801e140e160380c0041c0d030241c5240180e41905621044140c1519130717450309079841c2e40c00a6000d0380030300c402140228281a03100d03200030496000d03088500040309960240442c900803800300700c1e04944c0312040011036585030100329002e4989020003507403078041d40001810101003001c01d0000e0028042d0702101c60b130381040200c0d0507641c00440f51107491060b803030000b80500c00d05070025172140c4080b50384484031100290f40410394800000810084840381030584c3d440031100d089a070741c0206 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 249822643 1250 249821393 249821419
    0x906030c0d06020f1201140301020406080c030711070906030b0609041122050f01150f02060c07080d0203100e0c041412160305030a0216080a03050c120706050406060e06 74
    0x1c1a031940d02400005040c00c0e00c400c0b800a1075445501a031401040c0c0e00300500c5000c0ba980018a28034000718021464689015006014000d000f042e07450410004070008010030301620711205401c07106002e50b45a50740340c011840040c42940803d584445206c1700080035805c007590502e000c0d41c0c0080d5003c1201b0404d6003041035240700d01c03140b141e000b04201031520881100340606405005001c0c1480c0d007640c1424480e60513240398140180030070080304c0000c54015008200250080003a0081d141d4a20311400c3c0040740b4450400100c480380e01c00401c0080b1190440400c07415a811050042201d0701c0d001c10b40e010900550043c201403031603410940b0614a0320410303c10344811400160340750380132050041117a0701442d0b030065880d50000541c030360b0344c01d130b052100003078628984071540b640c18100b0000703d0366070459402c0107090040005d07085100e103d04000c07001481c0c01c154180e40e0707101101e1a0500c00b5180c02d031003c8440030f05080c004540288007481c901e00c110b40c090402a018ac4e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 249823893 1250 249822643 249822649
    0x51612020c0c060702060c01051303030c0e0901060e0a030519030e0307140402090a17100b0118090f02090d0302010b0f060f071203020c0a03031d060603120307021c020606010e0906030c 81
    0x11004c54102d030f00c040200034440500c0e8082c01020f01c2019403140172181b95210341406000c2e1400c00701400104844046022000c0d65401409810740304140f4200c54002d032182c011405405c3c094001900718850040024a0102c0d260380c2c0c120a07901c0782d960031400501c00d0085c180d60f90042c0c01041701d07010340400041c42c1404d166010740345001000f4501146a40c0d10082100d040f0b071a1000d0348405e40000030000420340c04ca008020403a00700f032a01c02081100d18102d035501000314011098000d0300c03610006440115030f0161031808100a007085c803c00140d15001c1e00070b140d50a44035000c2c40075007542d98414580781c4143c40f00c5899480e1000d04e020600e80e00c0a102a50f614902e02c00d040d402d20200729030b03071800c001c00c624940c844e4800244142d503442d510883d21881c0024412140e102404010040d180807469000b5104000280358803512110800d0b03040c104176041e4440124030b000318114055500140490160800380c883d00c845540d00414004e8400c0103c88003a01a0310640020409003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 249825143 1250 249823893 249823897
    0x1030b1902040317030604060b0c0a1106040302040c111005061c02010909020a200120181804032007060f031404081e03090d0c020d020301051612020c0c06 68
    0x403016200052a1a490b95600e408140c40d201c109009103101000300900d90a0520a510241a24041d00e03402c0c1070704c0308041603031200e400000901850301501d0301102d03611030600743d4001e950b009009000360344411500410202c50342c03c141070380f84242403011411030b881c0e100301c80c000d01c0c000d01a80c02140d2013884220841159040490400c50f504800040205d0244058110301ca59a41c3e0b01c0e0510f4004e05500d0f07200d00750300c400c0210700c0c1d241c900e480d001e02a0174090358031001034000000c0c0d211910a0321130900d9460010b011600a0041910709403a409180311144c40365209440c0c0d8450250303e14810822001100c0b0b08120a9000e03650520805020b051860745d04401d92902144d040c00070741c5c10084d00c1005603011180c0380740c00f06000c00c000304600400400810303034403951801d501c1c0000c02c1d11307a03840c40a8428002d00000010150640d00c0700d1201c1c400741c40e0054028045402c012001c601507008440d0301c50001401140140c144d14040d00840741c40d00d506000500501580d001089815 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 249826393 1250 249825143 249825181
    0x71d10230c19051c020705152d13060201050f090d08010608090102041a070b0618151804030e0f0f0105251b09051b0a030b0105131e080601030b 63
    0x1510410700300941c0408844c81c05001507036654080d000311840c18040c0f19035050784e00000d0580040602c24440f0360340c0740c82508040220b03011802100c400702010121210300c1141c0661001c17982060340404c0d219015041300303000780341e09079002a0650728074841607190113098208000060b120401000454402e0844030b0708801e0003400149801d0717441c42803903803200c89103003100c0c150100032845c0300a100101c02d030300b5841801034504103554070901c0040800b40000402406111030802059001504c6040c280c40c4413070341a9800c810182440c0c10040c0c0000100e68400748200078600c0800c6c07103401c0503a00c607003c40701e060f15031504056010040820001402e01c0c3d50f5000b41c0c4030403540012410109010710420702000b000220345003411000400e90344003c014650a540050390184a8038480301142c0b01034549250005d10038500000481c1ca52141c507829020700070700140003040741c01602410b14584018001003e100642d28640c440d16414248400340c428043e030400500300b400c81400c02d10038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 249827643 1250 249826393 249826403
    0x8060d080a0e0402041d040b0f0601021e070308040909050706050a3203070c0c06030501030c05131508030a03050a05100e0916090b03190209071d10230c19 68
    0x91a481c3c41c106c1c14004503c50804585400000030300082c41804a40c00b90003643c451110103c910380700c40080d542c1c401c212040446007000c01d0011011000c10300c40032001d141c0c041e101c44c0da9640c0c2c892450024005124003a503440c010320000048090083c011514080703015201c181c0f0a99484103030312500804000034000c1c0c1102d00408405c11413260000318840c81e010784070421503401c1411b00d0416006560002400c0c180b84c030700148040b86150b5201000c80c0c1d411107607d00300c001c1c00d550b1800a804040d000c00421042941c1c042280322010003d8401d110789550200010b5541c03c1402054030816a4a020010004034003400580c141c0c945a0b07501c50721302402c6035105d9601c901041c2002c038030740c5c1c044d61696541b10b900c8041440e05101e112403060801d0724070912a1419000210440130140191080c000c1e6050000c07149254150900c4c0c529000500351402c2c0360148001900d10030400501d41517624581e5600c01d1301c0742c0000306440d01c1865603801800d5440848801145644200c0d40c159a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 249828893 1250 249827643 249827647
    0x1a0102160503100f1b181406161505090f12040302150702060c06070503070318050d1209020d0503090a0b0705060c090609030102070f0210090e191508030a08060d080a0e0402 76
    0x39002e4000294200c0030000303540b88240106c101d06c03c42961840c941201443d0250712100d00c03055500c00703040d50314105400140300c0801c83c1178603219050307200d07151030341c5101c41c10017040000720100803c0b03955000c00a001a50300359001320126504a01c41d07804000d40c400783d8810f49016655041000e4400d0905c0036005503c2e00f284175610a141a0307044860000180d0004208444264103000b02d0503942d1407020004e4070700c0d049590b415161854141c8103002c00012001712652070700315410440540d40c010317001e80e50b0340d000d03030901e1500e0340e001104140c024031035a800020315620038001c07101e071180c0040151106885004554255034803451101c3c0d409402403208402c1e940d000e00c010080c491040c48545d8174100184180103075012807140030814000341200401562174064401d90f4000308102111004c80d9200d003950006003001c0301c001c40703800e44648000c10b00e1400040141320100b1162500c0c42e460361400d01b0004200108240200280d20502c9600b0740140200d80044032078100030000740c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 249830143 1250 249828893 249828911
    0x92214010204050d20060702100305070207260d110a031103070b0a1a10120b03070b07050303010602100c0504030201081305010e030406030b030c0f0d0807061a0102160503100f 77
    0x2404c12508880969841049114040c03142d2104a00212046000c1d00d461303040ca106030b00002c00101401c120310080c50788400015034042d01c00d000d84405442d600100311601a03102c201e00c55120184040c2c2011440b64542e12a0300034001e0b070401c103604004200400f40030070585d03070444e9104951884002648010300800000655078407909200c1e503249403001a030110041074214166505540150080e01d08950102e00c0c1d030341c0a20070326040103407560b021403104404e901092824075143c0c4180a03a0901140e00c10801001000035412a0030a60882e900c2000340300ba024100d80b01072100d10003003181008104015401440c0c641e82c010595070741ea100e0351090b07031142800d4504506514030143c00004003401101e40512511490340400c1c1e0003441c41c09a030364003184030460100c400c180b05d061315801e11410002c0d000c00315001241d010809104c2403810300036100c3c40d503c3d54003515000d801842c1000b489985900120400c80e0030040040187d010780a01c8a070090240703100c5204650b494010b40307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 249831393 1250 249830143 249830149
    0xc180e06012105150f0a03200105120c130f080601063002220e040b06121006050a0504092a03060e2103010b0a050d0e190209221401020405 61
    0x1d0b8400d0010055405a00c4504c104000465940300c011034404c240400051001c10f580081151207c0c0c5070b0055541c2490700080161414080d5070b4130700500c1c1f61840d0401120b1406280905030350901401104851500c544049954003000d0041c00f0680d448500104101449a0303049868204014140801020003042c04000403500101240c2e150760002000400c2c00341c4580c2c0904100100143e0141040c1000c989510b010340203040a004107883c40040b9449d683c0303001000303058000010807101c0e030180407c4c0318006042c040c07254511400710b040b40003d0600300780c0211001c269102030a04110065241921843d00c464411060131101c602d2021000070710500c070b5000d0a460742c100900180e00c0200c02d420540c41011040c3c03188033400d100400180c0c500d0320580700b10042c40d00300301d0b8031b900003c070510008103189844804c00e84580c1c8207040001c042d4503000c0709030500a0317030228903581e43c6000d002d003520006600e82d0065140411003d020825414000c031014219900161a00350341d1400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 249832643 1250 249831393 249831401
    0xf02151308070f11040b0f060a140409090308070e0108040b07090b0a030501090f06060206010b0304081c0b01020f0304080714040e0d021b090402010912110406090c180e060121 77
    0x10072200f080201d60307103105000966940d40b0505030100c8090220410000114101c101c1c902c01d03440c002d041c04214041140c1c01071000041200d89680c3e140e4407981e6860740c00014051a540650100f14030001140041e0300c00d607404034803d041a10f0703441c0b0b141c03a03503901c0300706401740104a1810400c01030008229000c80100416040091b50b5002c2000d5040c41c049100300c4640c24580c000541c40d00304200555038000c1400340c11107265089042d00c80d552401d0201e10340c0700d07070b5400e00c0050b0199143c034a48074800307a000e0000c07a0000c0e8212040b43c000044525640d00c164040c03035001e58840d0004001200d5070f42003100d5241409000442d0104290500515210812641402503001081e030a851148440c4c0880491a0101c8080881e400d05400203402e00f401805a030440d8109118910207014210800708070f0044068003c01110766038441c424014a001c580d254001119030f0095032a0343c403e00c40000940b041c04818290070348030b4600540304103901061441c0650351a8524140b11501031003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 249833893 1250 249832643 249832657
    0x50c0304080714191110081f080102040b07061a061902100c0806030d09060f03090204090b070206060a050301050f0a0c0c170406080f19020f0408070902040e070f02151308 75
    0x140c0c007910551915001740000110003040c3d000c0da50300354501c105a80e02c42c11568110b420700418072015000028044000d9105401c48107496000280001e9908401b0b0010000b09016500421180a120019165182d503440c1541c2c0d004a043c4883d5091740402d40342e4000c0f00055004075640014030302022010307102c030f80e003601c0041110700d0b081014a090500256a4070311031443d003d84440d08140d00a480a500c40c500c400405583e000c202d0110b45403035201644c2d481c0c10100300c1c155427426078402981c40a04581c0580a803040d070200103102e040c14024540240c003038001003d141d0f566001190700500760724240b1000c0002c40800076000c10009401003144550704548669110b05140014000300b00140068910130040c0e0204103242c843d1200803045070340c52500242e900c5d3b40c41034040c3c50758012078108043d070340540100001e84200590090049034400003d250f21a65015001e0310b100450306c104401503040010506514403a0601c07080d8000c1f0181141d8600c8000c50b1110306107031300121 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 249835143 1250 249833893 249833923
    0x11010804021f0521180a120807050c030c060703060504021c09020a0b120105100f0f0c060f060b03180d0c150204170c0306010806060f1e0904120f03050c0304080714 72
    0x400c0c003900e210454000d07808003040e04000c1c1003441280d0745100703036080c1c21740e040020000c5048c045040e003480303a0203c40c0816010700c00c480c2c03141d00b015091a1540300a0310560301007464a070b40003d450a240c002c3c0d03030945d0040c0213038504c00003e028011000e031a5040c800c07613004041c5240460b200390700001400c400d2002540e020701660610b001d0004501c0b540c44030f4810f220001c110f010915600c0702d215030406c0541e2074549091035245c5071650107030014686002c1d890707003022004180743c0d0348240030394031402444080a00009000014a40b10100001d80c400021505110800032800c9901d150b4450100307070a0051a0582c1d41500c6050541000c207130345000d40200b81d82004500d020059140504201c03000f405050034032070300042c0e82c1c1c5190f0114501403003986600340422081c0c84040403d030300018050b4082807601d454046da0080d00b0702102404075400c21035400d0468481d106441c415100c051002c3e00e19151030306c5590403904001d40c2211101c190b100315045c1070005200090014540c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 249836393 1250 249835143 249835207
    0x807080105061c020f0d080408010b01090b04030b07080714040b09010e030c010203160302070801050408072f06070f0c06031b08090c0120070b0711010804021f05 71
    0x10541250a59078040c0c5002d1261002c02d581c40f140307400c8030b9800303540b196044680c09011000304010803005406903a0240c00b806010400049122064011012848090f40c80400f102d132218040318280c01540405451003005c40c0004480c039014129041d00001c041c14030030b6108009046080e41540103400020101d00c01240c40165075820200024245100b24043d1244105850000f503403401400305030031005542e882c14205050003804060098030301c110080c026840c003030070031810a612900044402e4140f14591109071000000740020400492061a00003a5648200285038014401c10b8918110001201002032140d50000740100455200851011102602600440d58000c620303024000340c2d4041141002010420743e620800900b032018080c4c0d100103801c000d084942c0c1004c04184201400400d01440400140103118170a01c80881c090b10000f004550b5058107aa0081d000480d50f6400400303a2143c545548000d401450726070304040c00c0301901c1c106102c9401c0011000c03c1d03c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 249837643 1250 249836393 249836399
    0xf0b070f14090d030302090f0303070b010815090d0e041407110f010209060d05150325050a030201020606090703020903071d09070506040b0901020304051e180c070305130f0807 77
    0x50381d540e90300400ca03101141804800e0340415950407003114010700b0143c0c0002c0303054241ea5150001e03510514007804580d2181c82c503103081202c00c4800c0c043c40003644100055007058003401c80140380b10705507804c00b50400c218288025198940c2e071091990703005803070700d41810090340c9082d2001e21450144d0f98041001484400041c10b00e1881824480144d00400002c0c4032621514119000d101190b00009a140d0b00e1400c0104440701c0c55011580c1802120103400e0303201d1408840034400031424081c14080303962641000000201c51000171701681149001500c075240070810950b1011f0385040c09450003c4020020303060241a4100c00f8404070342c16484a200d0703440c4070710598448003002c0100300d601d00381800140c06001d00c0c0308101c40c49800140c04c0003644d20910a0360000c0034082c01c1c00401e80c4071000c0801c002144600110301a1300b1984901580d01d8214400ca80104070402025240800c2a01e040b18190b10040000c01d81910303541000074035400000400c0e000b00b0344903002c0c003600b0381 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 249838893 1250 249837643 249837647
    0x110c060a0f080c210a0605060a270e0703020a17011701110301062102040b030a060e070c11010e01020111030f010303110102040609210f12090b030f0609040f0b070f 72
    0x40a08551a0f80d03400b403003101180c8940003c6010040050300c84248680d0b0b03442c4840700030300529000103070410700220340c0c81a43ca4008400c20504600342114100e01105000070310000e0409124034480001c0700c00200d403040b4000e0303005104140080c50185210180039044a0070b071902a400707144090071400c526000140280b180d8003006000444951071540761003801080818400c81815000c8a1100303142c038400b800d681150010803204036055200c1c50452448030080c40d161140003e10312105000038051481064958405a44034034241d0f0460008401100c00040b6071200505541da03c0850b64503803540c05000d0351140f0600351100100e98110714000b0720400050380e10b030842e40c0c01408240221034010790305034182c0e03407503c07500191000c0304500901c00301302c107080150044080c05809001d2040518500180701e401d030f180c1c0b1205690340c20030080b4074801140c94a010104207004120b02d4500500c600d0b8006004201d108100829038440c88800b41d400c0c0c03030740b0001c6815008a494815 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 249840143 1250 249838893 249838907
    0x10020607021e0706080c040306050a06140105072003010f06030807060b180601050d110a0e0306010f03030503010e0405030f0313112709010e030d060e0c1306110c060a0f 74
    0x2842d542e1901e0304103206001903664819050141030148403001000410120407042903130021500300304180079a06082c1c2444004280358040d0214004400d002210329500a00c1150b0030355a00400303450404080d582e00141d503113802080568155200c20340c0b0703031007400c039409490040c5001e800701d2655915545000781c00ca54035840700d58082c072850041c40b0b4081009500141d8007540a0914640c2c910b844020407009101c000b1004501c1c0c40c000c42c40d030190aa01c58802292540c00303408039602a40ca800301c000e482052480300800286c0100018000d515aa02c140b13500940308608a900300940b82c9114070640d0412680e40d6224070800301d165046c0709a0b01040c1e914a081a82e05188103288001c0d8562880185882c814000140c00d021404e1440d00750700c06c00d030401001c0262902c03078004541300e0f0003030b0504e0f01c5444404c424000c0030038403000e60170049911684002401c88262403801100792001d142034403008075903010707504c070024640d00e900004040c5003c00f551140d00c688441d1501070584 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 249841393 1250 249840143 249840163
    0x1a03011805040503041701020412030210050f06210309031f06050904150207050c091014030d021903090504060f05281215090c081002090901030209151002060702 71
    0x30381808240004150003104850946014100d501c0000e07919001044c068413803503100f00851950b0200d2201810341c08180e40000b1214040305211548034007912140405068408a500000700030030a003850444800010254200c1e6040c2da082c4100d0200007400c0086d1004154a02041c0c0c4000400761043c5105d054060001118000003c0c1042e840b101801e07120b030f4880d4903d182c2e00150100c01d1100400415a402e00005c3c1744445921f0141c2d174403075542c5c2c403d00c114008103c012400d0145440c000c0303000c20807003c803503009090b402120002c540300d208141e02c0c1a41030000006020840c0d85075800381c000030f000c41d2540308101616003410710880d40080552440e4425400c0c10a841c0c10754511107031011941807000c0c0502c501c8603030800d80d8100300c00b282c0e000c10f45803608585008100011502008035104807084d208a28408090401a841500082507020044d2401880145070005041e908a0044051010f0700c42c500e2010801b9008046051000341e88501e0402100b43e604108100f10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 249842643 1250 249841393 249841439
    0x1018090c020d0c17031312021b0102061b0f0c01060303030b15070c05120c180f090303090a032a210908070b0f190c03090b04080c04151a0301 62
    0x454005451300310744404103d40c1040300f07203000004600d00390070403c00707a5003540d00100c900c0050120780c000a5038a0004008500c1540c10070400f8115960001c509240300e0380c0c000c0d204802e0412951445c040540c0a25003800390b14100b40001c801d180800d10404014502c641ca000410f08180410460b80d4090010400d02c014410491040014034480401084038001d0318a040701d40140f071400c509025038640543e8100c1200104814888000880075026400880d54414142c44d408110354803840200c030740c0d00041d42700b0f16141001038480d81c4008035030241000140358006040050308804c07802140140e41060000c9032800d6007c1011403841000350407828070440746842c01e0340103078803440d80e807194510110307001c507506080000140488203a525052540116504081400f4001040710710080c0c001415035400869002c514504950070349030702c035001b0036500d0310207070401000e003100049086052000c0c1c0c00000e40050b101548440310f0000300d15841d16503041145281c0708070703031402e04042 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 249843893 1250 249842643 249842657
    0xb04022d010801230f01031e02190c0f08090f090106020d080a020301060c0b0405010b0406080d031802010504090b031c0306140406140118050310090b0601030501030209061018090c020d 81
    0x15031404c0d401590040702d0b001c1c1c0d00d180c0f5008000006800a216410410074460382074201e80c0128403541d802045c0c0388503462100e0410300f10202007281d032981d50400c01007206486000b2440400e00301d41c0900b03a4440e0041c06070704c010004601060440300282d1010000d07034069600107862030b4200380d13082d9116116103411419036141001c020a83c50360101301500c03901244d00800c0c2804020342125403210409082448056038440307025035203003600b1040d0302c0007a00c1c0c1480032024110303404821600d00e030141c1d1000d080500346664040106030b6034482c0d40d8075205501490614032807080c0315030298000341d01c1c0002c0c442c2c81c04001c111002a0301003030710b01c502d24102c0280801c91710560454030012080c40c140c400305413483c40d940d491084c150030403030f810322440e150500d42281503001034080e288108400029030f294180194143d94080c0402580221048002245130905038031020250001d450001c17a40191000c0403c40e942083d0450350303100d40c889880b80220744e010400d034110234030710386840300b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 249845143 1250 249843893 249843929
    0x3070f03090c170c0d0c0e0708010f03060f020c0a11031203060a0e130f0609020a170705010f030f0207061b0203030702070e060a08010c03050f0907050d0b04022d010801 74
    0x1a003009540c02074001c402d5034241c3c54854903008002d0b20090314000b420740c030f404a10078282181140030038880e41708140031340b00010703800ca441500210704840421100d04105415640e3303600c040c0c10f003840302c1c1d0708140e4203015600f6007071000c01c44d1030106ca02034028903000804a8090500341400900c0207540c110702003043c41400e80b240342000701103540720340041c05241c175003550720b0301488006003004e428200a01030705418440c8691240301054400c42d20581a940e58055410403000c00b402c089007150410901000340d54014000d0010690103490005125203001210108a0308511410f40e8042d41e03400b60350f000142101c000ca05000001d000440c00d614106100a5071401c42e07004007201003c0b9003002c44c8054540030f03200c0d005000701200a00201855040c01802840c1c110341d44c101800065000c10342542000c1170260913200003400724085c10407035856003410808003900490300442c1d403d0712031100c1d4000b900e000e5407825100070004144100383c4001031507220103070003e12044005c1e1b1002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 249846393 1250 249845143 249845153
    0x20d0e180a0501080d032003060d080a110d030605180a06050d0f051203060307210c1e050a061202070f0b01080f010c050a0c021c2018010311010c0501020705030f03070f0309 76
    0x31f0041c03c181c83c2c025076039a42c0d5071b40120f9096040000c0080c480c0c50007003000803040b0b40102807041d42560740000c0311583d004405048050f41e105200d0182c100d410440e4a0340103190104502d0360161101d240803070415503c0c40450f4680207200030070303a40c110212140b4800c0003814031003440c0c011240180c05055041040c00203499019910035000c0d604036040740241c43c5040c500807681d40c0340e005a40210265660480b4107039a899034051066095102c0300085010b192101d80042501d0300d543c0e8082102c0400c00114009500a1805954104075462010006102011418060400200908446114071202600b550552030b44032080c860148560f5003920740c4901aa442581c045400d410700c00300d0844c405407110080e6001400c42220100820040b4a000e0a4003c01402c240d507029508003003000c41410801083c040200700f401070b08d103210300c00e6100348010301d0401d00a070001450302e10960395643c55507000c2c1e041c02014100100070800041e4004d00e5032105524903003000c3c0000042941c43d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 249847643 1250 249846393 249846431
    0x709020d0506060901090e090111180117101a070c030c03030207091a0405070513090501150207140d08040b0703120506031606080a020c06090c031c020d0e180a0501080d03 75
    0x47c0424040b079090008040724002d4000740000e035044c90104e40d6503012602000401b40942c1001404200c503681c0360069400904001482100260300100502d403d1003203140050091491030a00d4110074000040400d400d1151078008510071490100690b2a40c0b80290a181c6250304c06003805203440400700e0716241e41c413500b4801d50b10883e0b001801d86d590b02c0054601e0b02841c050300750451071844000c10084600c3d44460f050360080b9020304a443c2d0010800c90396011a40201681080210503810782401d1404007128001e104028030b40c1001d40f12a08403106402110081d40000c2481c07400821400e00d0744151908210143c0140030446a00300310018581498407800040205410008580b00c00550645400c14410000d9940c18204000815034a010341d100a81c0300780a20110300c0400382400110829106650300a800422400c0f00c0540e1983e003c05603840c2c101d03403c0710000240c0480040043c0c807e04d502580043c0650400305890701d0301600c56000014035141c05c042440c054102c00c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 249848893 1250 249847643 249847649
    0x1080610030f080721030501120206040e1b07050102041a070b190b0d110306060f0a031e080c0a03020106080105060d0609020f04021209060603012c07080709020d050606090109 77
    0x2c05a41882042c03600907603911900c40003411452070501c03018400c2c00000600307110146580e80c00c0c040381e621130098045500307201400961090307041100300300140160307240651054103414040c845204842c00031703003664414003044030f05941c005024481c02010841d54403081004e05400390410b085a56a403200403405049802c01108841c001a00004240c0000700c583d680907000e4501c80e042c602e03240e10105020381440344a0b0084800240c05420100e403041c2d40768000801e000442072442d225102003810740f5103d041903034140d288213000305490b4001400340450650003410f4080e05405c0003400c40300181c10075003241c2d06200611000d0b503aa001c2e40c00c0d041d5040100003881100340d04c0013400c800f0500000c543c1150000c51036443c0c0052122146206246920980c0c250b07540d003004041c225012075411010711580c040300081c3c3c8000c00c00a140e840d0f0300031070031598125120701c1c0052414101d5448109625000a200318004210f07004954004c00c00341c03039050420010b4000680844100c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 249850143 1250 249848893 249848903
    0x8070308090c100c060b060304050715030b090f070f020703080315040902090408030417040501050403061d01050c09040f0b03060601030c050d050408040f0602030a1d03071d07080108061003 83
    0x90040707070040780c0912441d405120003e01d42c01507000d5098015225000b0094241c036524503000f1580903d0030000c044900c15a4010b010780130780750520340880c180e242140030b62000c066903009800c0b40c90300c0b003900e0351b4041c04603800120414907240000070303d1501311581190442d005603000b000029180700a81c0d8201c0102c01201c1080310100d00801d00070080c43c440a988036040c10244400c1c0003003403004500a078000d0010135262080054205824170441c0f00e904d00040d410402000440c0096000d001e03a411501103c4241d901d0b8200240d0030b4407001d45611a5036030b8005507076070f01441e0500c40c1107815440c00300144016205400080e0703c5420040c0b541d41810384409011400d6481386c0c0440b0080d4032613940401c024145818200300c01c1c0c006004254010711041004203c003400001a01c01c441382a50b1404d0b90252048070f070480200c43c1241a540510030071700c01165042010b0714002920080761440c03015880d100800800c08070046e88400c0140d0007900903c01d004401580c3c081c10790b5004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 249851393 1250 249850143 249850157
    0xf1803130e090c0303130602070b0c1c0e0d150e0a0f0b0a060305030a0302070201090506040b0a0c05070801140f0f010302090c07110d03050c0105011a041e030605100e07020703080703 80
    0x400382c450f0510f2200d0b4031650b8036010004a02c1025034140003001c064031071550803541d8035a21408280f6481c400e0650003501d0307134441d8034800311141c4696100902896945801000c0f10303100703004500e0a0b9010b0704229054034111003031140704452441000d40489c408402800c4203000c0da01e0f903810048461001801c180c04240c001800710003136800c00d03801164480203c944c1c07102d070358200400039000400f00301c0c0003400d083d5001070286451421b590641c1c00c0801c0341864a6008002035a10300052442103a15014104001520034801c0c4502c0700315408951500c4014030380116403244054000348184d900d0b4000764014405602c6400d4000d6000036020301e0513a0781d10003810000560b0908190041e440100382c010541019442000340c003030101420000c3c01680d80f10091050020340c1c102204000000a00040102e5550301090103110310280c600610075030303140d481c0c020030b864046074070310b82160303400700c04215904a507210346a12000920207820705606541d54606103100e81c03d400340030441c0f8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 249852643 1250 249851393 249851401
    0x30302091203040806010630150b030108070e18071203030e0604030c0b07081504020904020c010f09021002010606080a0903021501080607030c030b0d0b040305040306050f1803130e 79
    0x540700415072000d07a214100ca80b034699640240f541d45c0f00074000c0e4400660171003594030110030341c1000c0081004100c4080141111034101c4030004041540701d41030841d410010002e0070110b24030055018003480340142500a08040e44201d44890283c920055241c505032841c80750b200200b41c5000395030013103c5081c034060b0f103400c00b10090101140052000d00969051004060b0007149005103240720b41c014007000e0307464441c1640c0034442214002046011080074045038a0103038010050140020720040c240000c08901500316110380e0319098119036511201c0b025858040d100401092662000f40701e0a800c1160040001d0300107022560070a03120301203881018000e0110990400d03c080301c400e0650303520840b01c1d9981205a40769004a8070b0303d1041050503110780101c1d5820403001e482024076030141d035034070041441c00070001d60030080f051101000240c1d05024050042e031101e80711a0f02410290035160001902e003214080560017048131180e4991341e941280110340d04030303190281036a5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 249853893 1250 249852643 249852649
    0xc03030403110112020d02072f24030108071a0a0f0c0c030b040614070c0b0f071407031d040c1b0606050607030915050408100f02090d0b04060b011b03030209 69
    0x110340c24039413151400480d000301600d946070301400d0158080c40b500610400c43c40c16031907072841c0303e03900d42000b13a81c5580c240e0600d00f00300320540090340a0b03030401c8650a50b003140101c16070f00b00780c01091041d08002410054082c3d00728664101d40200c070015854414188409018890401c190b84280000c60b8141001e0000c4180000015600300107000d140c1d240c0361401c0e60081501c642c003e40070b03a580101156000348901c49440d1815441a81c3d0411600c8982c00e40d0003c3c0b03c001c220388100a6803501850320901c40c034024081c003a1181c3c030b07040524144410205122411407482d0341c051031411000d4041590310000c1d1511891034180c0840044509080200103400c007604115080080000c6c0364081503440b1629108580c90402003001c54002c111045841e4815482040f0380d55001580c0e00340c07140343c190b0149006040014005140107000300108600110880090320609445420030040c0070300f5000c1d5880100d001d03e843e08000415900000081d210088054101940442c031044951 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 249855143 1250 249853893 249853907
    0x1605030904180b010b0f040519050a0e042907110109080f0c060a090f020108220308040b0a09170f09040603060e100209010e010e0d0c03031d01020c030304031101 71
    0x24400342042c4010304000c0302030780020441803000c8a1540d1400d000141c070000c91400c0d650700b881038408040c5464a0305042100b10900c02d24404640030b55428000b0b40340d17850304001d40052600c03180c003440915080c100070b4070014290340740700c0765880300400c1064000811803040354803100604200301c82c0c4000500039801440c401c40000c00b6200c00180304104d120128001e000c444212004540d107075510840c0d400d0035101e080400418035143c0321660001907005213402a40030b03100107401e41003015070303802e0503050b184200e006070003241c3c3d8030050200340088141110780c40004406e050000b010300b0f5403002100b101c41c60500e42c0c21b0402003503184040b40b5a0003124000c5400800610074a0b03245c0c00c0c450028440c003100b81081d44110748446403c01c5090080e2031154005842d07a56611211400642c1c8259a090005500490b0401e003900001c03104a404d4001e180650760341e82e96546800c0c513501c0d140c80c1152407141554800c0c3c80b90200345d54004119004c1c2c035441400b10100110a8005803091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 249856393 1250 249855143 249855157
    0x80d0c080d0606050306040c17070e240a0801080a0b0601141308030a11070b0d0902130e0d02010b0307030803150102010902130e0c01140a030515130608120a05160503 73
    0x802d04082c400600c0503030240c003950065404480801060031100403d440354240106014154408000064001c500800d419002c1d19009000c2001d4105c0e0740b618901645d030600c080d41d0f09808080780040355035610400301c501604290b00107015000071911580b04005004040038100f041c50301d00484001c0e02042550702c201f0016a2400c0740c1d9846010070794a07034004080250009281a4090300c02e040000f40392030880303401201683c07418841c0c8111308060180024141e130400b502000010050925100b20880c4400b1400607000c103250040c07000b0300b503aa440c0481d030302ca903102201c1400070405c04401c4a030402d0240910410352002800140c3c05050301903006980400c0360005c29900c507102d40c10801e01d2044180903241074554840045d40c000486810b1484602000d0084550aa01903071003140c00945902d031510f1413030040f030b00085481404d0f000c070111090310b540d410050f04000f0000340c95a42c0c402c80489061007c040001003050080c6ea1001d41c42c065200241020b1110a208440e00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 249857643 1250 249856393 249856417
    0x906010e0d02210c1311071b0308030f16081504090c080a030c0b0609010f03060506150f0408060903030403080f0424020a020609070b0f1803101e0204080d0c08 70
    0x2040e481580e146866020f21301c003250140450800c694001c0b013052142500d10340d414030405040101c0707134556a0381203494680a680800601c0404030101d030f60940903500c102c01901d61130b51245441003414601050040703540d42800745e24000c0c002800d40c102a8010b00450650700054100c030f440c01c0c03d04a61220ba803006c0b11078042c8420301c006141e4020356840c0542e0007603040002c0c80d1221001e0012100e801d1213412403044e140841440020026008940c0002000b02040f803018600c0b580022194012001e401701c1020005082104510904c090b03036003e100711000d9810b601d40764030b001d410310800508440400c5907000008040186c2424260900900300c0c03422550401104110343c000c1d0f20084c03090000d480340310300140750504001011415260340070f90b00b60070b11040d07103140c04c8203030025015080451040080a0401d450030061600e040803150740c0480d085215a070b040c010040c0e0104089140c3d80100f106200d0f50340c00007003001d0005260310b00b40545038124100b24959001d042c2c400d41c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 249858893 1250 249857643 249857689
    0x5062103041805070f110309121c0306090c020601120b220302030d180f0b090a02030111030109141510030906020d05040b090a1a06030c0307030305040e060906010e0d02 74
    0x40c80409035002512421403505c50005600341c040050700c40d4950802103202d590700800c103040f0107003840c0c044641d540c010700e41101c60310b58844800e55698142003040c1000070380d940e0800c00c100c180740d000d20f141c182c00b517002800107035052103d001c03542e07400018041c2c0030030701d00400310314142c24004d10314850068654128000c1401454000d49907440f00541c401d81c0350a005104815840c0302083c0c072080c80d4029074440c5a800155500040944014420314150051047e20000340e2800e0107809820442040c00507620340c10f011517581100c6218106045010000003082042108506a4041403000703d6001c983d6000c40e500880140078a102c00801c540e00104694080d180305400003401540301c2d003150b002d03c1d82e565550541c1d6000001e005001490b40d0490f038000d0781528180c841d00400d028040d203c01c0d009180121303180a006500460000d00000b130f041140e0200902c00c80c1c0c11010441e00e01095041500c002800c041085141a20406016010f4400c551f0740d80c40c0c1004d24486054004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 249860143 1250 249858893 249858929
    0x112080f03191a03030d0c0201060f17010f061a092e0f020303070c02010309050a1b0e0106030603020607031b120201020d0b03010b09040b1b0d0605040c030506210304 73
    0x240c0b0101060285202942400a4081040c40100368481103540103801141040302100c100400341c40c200c000602036540c1e9410106000000c8101100586560001040501480c407840c6085841e08035041003864600803040c08102c81c1c008421440c01d072520200d989824103500003c03212200784110090021040e60158803100d507542d84d51041e402d294444504000009a060303071244004c40e000300000f180081508015802907111444043c02a0225501341a10780c0c0c1d0040380c1d110020a440803000034840c1040f12464483e10075016060394a0280403951466003c00d005000e400303001070520281d40e1305046a418034a0884a0060304640034002500031610060700035809108a244090b041088640560805000d8500400d1003d007501c6413550311a100c0c2406100d02408202c000805460f100803007040c218068400c2000d640800249540380404100071075000301502400d141c100010859144d80f401380e550790303c0145103039250780d802a800d4481e08610840c0c0200c603500340680c82c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 249861393 1250 249860143 249860161
    0x304050d2a050f0409020a05040e030f0714060c07020303120a1e0c092c040515102d0608060f060c010b091308270d030c0201020615090112080f03 64
    0x1804542c0c040e40e04801c0c80040f801404240c5407030b4032020790000d1942008100d42d0030160f0000d500201080103807420a45401c0720503025600c01c8400b682c40e0400702204038503811051040e07a402c007a0521407035240444aa01194490181854001c40345041200280c02c902482d0020229000041810941420081c100700c000b050a1541d0f88001964188040b13443c0e00e0440000343d4a001200814158074080044000035510003813046030310b030141650404200f450500114001c410648085504070704000c0744140500060042e005ea42600364101d1003001e000c0400042664a02d24010000c0c0c2c0e60315010608001d54035400a404c40d40008088011000650107000750a204441010640d1581c401d21144895500409481050100311103809024200058591580842105d051005d20480000c0c407903610000c05030702103025159100c085603414030040383d101c05400300300c040122102c4042003c1480500600b0507802d01e0307950690512041c03000751405c614540d440640d4034a000509 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 249862643 1250 249861393 249861473
    0x304120302132c0a0c051602030a23060a090b0f0601051324030608151905010303030e010b030d020c27010b0703110c060a0c0c030210050c1e0304050d 66
    0x3a4250302850100401d584c66034034050300d03186160555416040c200010b9200c05119a8107100721303814420304a04100080100183d0074107960300c4012000f920b007107031400a050545c024262600203181c2520702c400201c1c3c10b410290000301003503941d0b00e40d546100051b101c070b02c140b12481d1521202c1100001390312407100d10480854001c0440c0c5038880030040c409809599043c001c440c1c0710f811096002c0e80e158901d02c2d400ea44601d60502c045440c0d1081da041000b290f10a17001680042c3e162000501901c4090091a000450580c007c01495140700700c001c2d00c0d4800d408519100700c8080c0070b00400c041800302c6441100718035040f040b9071565038100c42c04080d84802d100f1804640b44150701010360078041034800e4921409451203140103400710b011200c81d828180708aa0142c040413010015840c0c1c2411980002802e4031030311344e00e0b116401c01e5031901e40c02d0015903081faa0803410403020f0440100603181100c10035658800d5041007031038000d4040040040040175485000c1c0440103040482074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 249863893 1250 249862643 249862709
    0x50c070203120c03030f1f240903080306060f090415080607051207050304060e01090501290f1c1e060606020c01020a02100903051b030c06030412030213 67
    0x300715155030080300c00409039400f44003007a02d160b4000b4000100890700510001d54081d20b030b0700040c40403580d030b6030901c4d0703d0f08201e822200e8150311206c60340d0307408604103a00c03003819907640c10264109881c5a85a04180c8001004d1a01610000c9032055040c01100255910540001d20510a046c02c0d4660700202001510811180f0700c5804041007455000e04120f4214016001c0401c44642da0000c00792000d61001d031007191181c1d80d07040d82d810024003e11a0f914810b114100109400c07001c00d5842840580a181540c1d04e91074003201c4180396a9501d84030b00c0500c1d000c4d1001c19662001803400c0810007060080a010f0145071030680c4c0310141c180b0360120190744161410820151100e80807a80d55035400c0b0580c1c05a07001a0020b80036140c0081002c04d0105d0510b8031400c250b0700da59905081182e042d00e200402c0d06480d4580c24640b9051050160707095003038030041c4c2989040d03102c0702030b90395a4440c071200307045d40065041070300084240500d01401d01d841822043e440f0b0003602a0400c20094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 249865143 1250 249863893 249863899
    0x102130806092a0f01050706090501051b0a020705040f021207030204090c0905030618120f03040525060302070206041203080a0b0f030c01051308070602070e07050403020108040f020f04050c0702 85
    0x10300d01d2040180490340c1c80400401e1944030301d41c48075150302401484d00c00460410b06101060010f00c0000745280160340603544580700100b25070800c02d10704001244101680360301a40140120104180c0c0040d408048a404036004165698811100802840382d00490503101c140700d820444029010380041c070031945500700801040345805008c0f220440c0e00d014603981a04064042492107400c8042c2d00080d85841003520003115880c0d00f003042d0383d40050100c200c0f902002c410001800000d0004210310440d000456030b250921030078100b10b140035070050b501030582c0818090150b46802051350060102c201c1c10749414101e600703010340600c070200e8003050002d0500d40300100a082100c5200b541c201c02900810185203c18010340301031304240c4000f1290030304018001000401008203000900a035000780c070b0b4060914508182c05500105500f0920804100420050368015589076001c0d8001111102d035054501c00260000642c10134164400e00b05414007000c195200014180d6a200b1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 249866393 1250 249865143 249865153
    0x1107050f06010504180b0411060a0c050c060f12220b061212090607030c05010507050301080d08010501051b010e0601170106060e031b0d0b070305070314060a030311010213080609 78
    0x540f0401094a1805030120030340580c4019080020382d480c00501c2d0068425030804c6031251044011904030340014a1440000d01d180310030a003402400c0c0720f60302801d0b1b000c1e01e1983c6840f4603102c480005200e40c3c1c40c2d84104841d0500011141d120282031074100d804c000c0c10b0f070449503a650900303036141c902c00e5071100e220344200300550b01c1c1d0040018120700360341d003050700c0f2504000c1414100801c03500445030a0f806e00603011011000110207206691040c0d01640701c2c25201c0d411b1034507652800090f00d481d2000c1c0034803040140f1040e038001003584d040100015002c0044e042c1c1da18040d0142002c10050801403059000106000703506512a43c4042c025130b0081045540c0c07580708a8003010008030b41c40d0580c200301303150300144141d00011404810040d1810450b40406e82c1d07030004800c0700315110b400107962682801324469042c01003220400d0119480b03205810004005004059a848018180110762810140b03404003034040e100c661071545440c1a40d1560341b685a5102c0c0f00c122040c21a030702034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 249867643 1250 249866393 249866399
    0x6070e09151e120307060504030e010828060306020a120b060711091b0a050a120506030312040303110705010f0e06040807080a050712170106301107050f0601 69
    0x486400c0381c20002041102e10382d403a040d0a60a02c1c0c18038600941042d2105110f0107002410402000110303c20f003800505850941030051003030b0f9050602c0740c1080200c0e4184403080100229075075841542103042003140208500c07090091883d0f500081c440350022807004a841c0d0010114520b0324088a0140b240c01680780801025103c1d0450042c0038240500001020781880b81406030303c801c00c030724086040b840d003042030b41c0310f40c001d10b00c49400036200162520f1032542c84081049134201940007880b0605007400001e460340504070b04140c100d0b040300005014580b0a80202d020040181c001a13aa804203060441c0a808007218001c0c1190500403540c051810000c1c8840c800d42d0494100d9003000d84640c0c8041040c2e012000410410031b0901c170304404a5044008410b1041461700c91483c1460185201080c458050340300c1c1d4184a02102e40742265040040350302c07294154a88000b0b810000019281d004008031448869030306400700301341007040f2000035100141c038001d50885615030780e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 249868893 1250 249867643 249867661
    0x120e0d0e03061902030405010902060f0301090b061606050403020a170901021209240906030a1d0c130b010c0f0b040506100503070303030207151a040605060c07140d0506070e09 77
    0x409031440700460583ca42240e0142d80c00780e000c0c0d60464412070001c0796000c256000280395410171900c44027140ea0000041000310824803944d2250a4141e9903d401c04c614040c44945040c01e8100281c85c164030b0b000000c04041c800e00884164942c0600c41440c1180d449440984541112600740d0240c4284a0b80c012603200c508140d401d8000014102000750040c00c600c8164041d200411240f400000c5c0440005030340c03210061403161481c180e0008030351100c0b0a08956174081e08a00f1840b0760448045ca481b15140e0b00c0b6140700c03030340300054085071008404004989001d1441f1000c3c064144121b40241040044003000d40110b01900c1152081d0b207501b400e003030491042e07216843d45540610001c00000c2d0098000c4e00744c071800f502660444500b000c4a00d01500e10200d000d460954980e640d41c1201d103030074402c1601030f00b02500c00c207042c045a50a196aa41034501441c462483c0c126460320440c2d8640c0041d0f03c2c4181e1040a607000f500b801400680081a2080c03103c0c41003510f0710028603010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 249870143 1250 249868893 249868903
    0x602010f290f011e0e011b150b0a0504050109090b1e0103060f0605030319032004030204020309010e150403020106060c03050a0e1201090804030204050708061f120e0d0e03 75
    0x485a00401d07682007040303007000010221851928140480c242101001c001144e4468462aa454440c0c012810a940004047c01078540d0311900004207210080c000c1118120203802c0d444075a42c00080800e101f000240800742168800340d8040d08150020031130440d107411003580c0e00d11402202400d0349400c80202e042580805081007407641c41c0c0010000314100340c0100c05a4041e4a600141070303500c0d43c022034213660090201410340011011000701c81c0340c2c11703c11103c09000d6000e00e0740c003280c861000c6580741e01c0f0310711010b44235a8000c000704503040d6082d80540d0400fa0708004503041d1b00c010030030350b0b80c854200b100d060b40554a4414002155400748541e0590294190703105464510f00303040507103001c080313564182c1d04078440c042c0d14446040b09200310b003007090080c0c1d80552680e113184104130a41c0c400905a00800506c0000d04c40030351511400803140139665800318051080d6071400b111076404040810f08030a08100b0000304680300400c3d036100e03401c46541e0341400b4190704011b041c1d5032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 249871393 1250 249870143 249870191
    0x509150603070810121406070801060504120510140a05090a0b0606070c05090702070311040e19050c090c0703020c040c020303070f02070f0f061b0b0c0d0e06010602010f 74
    0x31940c1000007446491040799100d6110520382c0c0c030354001544602e45500300e00004001100c1c0c0c405e0320b5119444042042004580c0031180b46412500341d81046030003005070040744240807100e071805044400b0031500f4407000883c001080340c1080901b520040d01d417243d07801610382c044010316010110700d6805010442104454010480d000180ca03044107000855101440582d200c1c810b080700440d8550f24240c4180c0961700950003004007504505088014580303002c0d2051046240c02c4030b48500072130110b80105803481c1c01c280c000c5195000c0c184113080680c400d030200c1c1d11902000801c403410040c04040c048040c042d0b402c0740d521034692024041202c1002c011407000d03900520006000511484014030448003d2041e20704035651001c4417103500185400403c400e01806405210b100d505c0500c44070428090308000722100e0310f07602c0c1d6070320345100a41001c54034030f40001d52428000d070941200c0310752141103089035495030750340100900a05500424541c698208008181c1040c2054211020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 249872643 1250 249871393 249871399
    0x2040902030f1f0521150103030206060f03060103020a030201030c021207060606081f14010504080604080901020f16031506031e12050f0d020322060b0f0d0312090c05030d0207050915 80
    0x260105c22843d0329213030343c08903100c020034454034900304004503a11410500071403103500104503d0420700100701840f004491070500070b90089004002503030700d04c045941220380a003000110454140300c1242045078818170b84219680000c0c0e18810041d81d079000c0d0084400070303a10030f0f61039100c3c59480340c0c039490050424080300034469014412000d8080003e80171000505001d4074003075aa06401d0300b001e008540603900c00602080032031013940c0501000d80f00964510103080280b60311140703107840a0311404040c1c0102031000018840001540c03040f406581c2000b42c40c0303d42c44d40090078011501c2140c0048900044224000341c105003d5001e8074290b02c62224024284070300024030500a4000402c090102040f80540c00b031102c4024064241141c012240456450039010900001c42246020507016500001d104000b10b544250903109894035404082503544403030034070703000c003964540100340d05004c0c5030440b0070380c0368001405c10112035040d503059403617a0701c00404042c413203a0515a41d0b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 249873893 1250 249872643 249872659
    0xa0203010e0a0b040b03070b18010504050d0b1b2205010504080d050304060609051006090b090a0e0709151805040b0a180908070c081c021b0402040902030f1f05 70
    0x40242c0c82d0b000090100c1e07002e40b000405810441c002407500c0881c2c1d0101440c3c0d80f000840343ca80144a140e4440c0442080c01d0841c505454040401d901860901d8090f005494150101d01482ca0312100c0000c007403044c41d030341500d0b081b00446076005140074415608254800031702c000b03aa940104251800c440e00c5202074504a048828180d0701584020000c031010b603078807c0086940202440f13254000e9100440102c0342608150010b001c420341504103407803101051024042950300c40a070343c02503907501c01c0c01d400943c95801c0c0075280000150445441c51010100007100a684804100243d8015140d85e405080d5644c007404202c55910800c15001200d000703040c000000260350395085200203c400003480d186c1511401201d420040d411507009a091804204c082d5080081514a010320140403200c0d040001c400796448561151034240c640300790703405080c82e81e0b0701d50503078008001d6510199a646000000c10200400864039500c0f4030900c0c491003c50310081442c410140d48018007118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 249875143 1250 249873893 249873901
    0x9060f01030903020f060a060e010b030c0706020d0207050f0606041512110d120503041a1e0703090606030f120206010b0901050f040302030a0f0606050d02130b060c0a12080a0203010e 80
    0x10090030b8148403d60940c400c0c84031380c1103440c100f040b850780f140c1d6138120f0019070941004916200c060301a4048000841c0c24010b10156000080403204d9150380818010303030720444166084081e0050301c42c050030303e0081c003100048002c0086802032080c901120100320f00305000b14003d54a850074000d60003a20654040e980001d00c81a02c40d07025000e000340f400401008955841c400f41c0020241c8400069010050204000c0c040342243c59440701000c007031405141c0115408030310031a000001070001d0101000c289154026444143d440c0d40001040c441e0179103074209407000f0348416804595040303c20928204203071000c6400e60503a218078803402c4c940102c3d40d00444898004d400081c40d0004100000001640c040001d0040c541c411702c28402452981e0504c2c00440c1e0295001c079001d50088140c000050344e915900d960101c000050004003840400c1c0402c3c09800f40d1080031119103c0c00d0201014000001c1d80192031440075030350440655651794100741680020b1296200c3c40400c04081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 249876393 1250 249875143 249875147
    0x20a170f0a0501082b1701060507111e1311071a130f060506031e16083403021203030415090c030b1906060f0e03070503030a11010905030f090f09060f01 67
    0x14610900b5441c0440190b424140c81b03850007402a40154042000060a501045092840003812090844240b600185051030042c2d0300122050aa480703258801c065000205641e4846056440480640d540314159490004844000c0401280c076260404000449031000b00e10300da02103680c030002c01d4a10100c140c0d660f00141c10301500d45681400348003c001c07210202031750706c221442c21040013408130800c0c040d112a11852503070001111500000e04403210012100200742d0300c2402c2c0f030350382d035159880b005004030915090b030002580000c1405070300d49800c1002000c1c6000300e0281030001c1034440fa5222140494800c0100201541400038041010402043c00580e00c200c1300c815403001030380b18483e980d003115140c0d040340000c0360024035a80c0d10b544d400981c850304440709400803d0300d1410803002a44c0c80c0182c51b4000d0810010300ea00c011408020740140d141c07554404200c90306c0d80e108012000c0760f0340000e80940e0007003c102c0d00e01001d038540151a01d01882c070181403482410440001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 249877643 1250 249876393 249876463
    0x711010b0d0201212307030b030c280302190614120105040c030e0a030f020705120c19080109050d03050c0a08010e070215040f05072403020a170f0a050108 68
    0x204104c1682c4a013848248810030704680184140f000806600b40703006903000e0121420b034400035000340e0040002d44085d032510441441c3c5030040c40000c0c48501010000101f04440c5034000a401011110300d41c041907103042e030fa4909640e0f141e1106811032581000d00c851b140107003200011210640c0004210314105a071164400d5181481d02245a10781c1203035040c6056910300307013140014a4402ca0050103035051040f480503190881d80c01121042c1020035582ea2920040001d20480003800f0182203060801028400ac0400f00000d010210003410140d444101a030f107c00d000ca420701c80005d1165040104441c4458003507110580c0b80e9003407504003401641c00034408404e40c8214400040040d2041c80d21612031482514a014000c0c810301d00745003008140e174050b0b0700c410030f403212807002400b0110841129484a20300161141e1905c40304648401c214003500c010a0404001d02540ca00c070061624480c40a105052115990301c4440660303074014044034524070241550803030340310982102d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 249878893 1250 249877643 249877697
    0x60111030d18140a0b06010215150303070c0603140a0c1b020a050415180603030c120c0b0106030f0c0905061206120f061801061503020309070902030711010b0d0201 72
    0x402c100e581c03003150351450315111160704400207642c0704103458020400303894482580f181081c030140564000300041d85030303a40b034040d18107078911a5060035040036880c00c000303440300d150300b20249105045e55144007500411221040e800406000b100003400344995020300707103c01c0d031290355203081c000ea4040300403859604110304983c1700c0007245000079035075614000c0034003500c115a183c0718003c1c901454052000e0341c00b0440540c42e4200142040802e810841280301980c002d04110002620040112401c102c180c3d401485d0364448800410042c3c0e05601000301003110000401543c0118403040d034100c0f54512560b03600550400410440500c85203100e50014005410b042c51281c42c00d04d15800c001030040c5036186607201008018480141155a4005101c0903008100003030a005e044418149400100b209141d000000b15603402c20400036079000b000135640440d00c0703040442006041500c8020480351642c24501b02e01160329002c24000c0110b94140c45812000d089441c1c041c2029007845 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 249880143 1250 249878893 249878921
    0x618040b060a0f09020a120501030f03050f0d05010f0e0601020f060105010f020a0203010e010c1b0b04080a0507061d12030f13020a0909210309121d060f030f060111030d 74
    0x400116040f08490103000381142c5040503888484c040310090494210004001e17045080100400c042902c1c07002c407000b100d405141140c0c2d03801d920221002c0c640324854140032414907202c00050301243c40c1a01500f0f441d00c1107902d00d81c80c0c41b114012a640c6212100aa401d41c02c454010061507015806c00180c070805401600c0c1c10300b1076600001e08440b100010f075039850351950039801c07205a0104494006440090034180300140c40d0300c40a5062000400040000c1e0002400d442a41e000f001903030342640e48840d082c4040303802902da02e4021407801d04e60071000d04c940303c207c00e0760034006000e40340306403420200c6081075902c200089043c084400000c1e6004140d45201041a01d480c1c0100c240c400c2c003444882649064140c00100c4400140102c6c600b050315001c01d04000521991850019004520341071000803e124013212002c5a41e03180d541e4846400141c0d4000c400a10004c1c5101d20344043d4400d43c507581d60300064580b0207551402d041180c10030062240c076000c207580183c3c5481c1041c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 249881393 1250 249880143 249880159
    0x5040c0c02120705010822030302090a1e1e060c230f060907060c030c0219090c08090d0201050c030103030305070e130b03010605060a1b060212040b0406050618040b06 73
    0x3940200b400507561414211441d0003105040c4913558001c26100d41158840c10101901581d0403409030050311000001401c040c0c0014940303145940e4400c3c0700d4003520100304182594600d41a49010b0800f9500c030b04400402c0306d400e260701c0b41d004290800104c03040c58941d074000300b110303076a101c60300e000b41d4800900c0c6560301c40c40c001d8051010815408140b001c04000c0100c0c0c10401145440d00041da0f104030200580400b6817000260702561444c01c00b94103a81e100070340000c1c00811603013417100740c000d246114030f0007030080307040d90b4803100541c0500900c0d010b07940301c002c0603c0300f203007a0313401160031500c083d008000400000703100343d100c01c1c0e00200a1410300c2003074280e2800a10170080100c5d1581c5c0305a02c0c7c1e01c040c56981b40038400d800003048100c035007515122400402a103190f182144268042c04152403003001d1003260340444000d1107025400d1240c62034545001061030009507419640703035180c10300041c0c190070f10400101c034885503e40c074000c03560364a41d52030611050003130030355412100c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 249882643 1250 249881393 249881417
    0x203010908041e05031209060904090b0703020a08160203030c03040602090a0b1c06140111030405270f1e07020a021203030a110f070809150316120b010905040c 70
    0x800c402501c00b6000c0021100000c00f03038540514981c014941105100742c00c03207400d003614411403034100e42c1c1c0c442d0152259500c64400f02c001600610407020080d00000040003000f95065241d4000c044070425900d0300704543d00e410010001001c000d44860015a0040020810304442140034681c440c2c4180400740c500b4071104085030b2074240d81d501088640710086200c444c180c41121000d07150a017501c800f00b00c3c0030301d0a9041000d00e03441e200300340d050102030024142c44043c02c1c03044074058440a0a0740c05804407046203034292840c02030b0441540e08460340852208a40d0301c045500807040204000d030541800081e581c28107c0244c008429441044180d5006868030120740c602003881801561304e178540448910143c0c0d50800070200d44003410401203540910308016a039542d0342061120f5111042080030a01d000e107060440340788a003010003080340900c54444100e001c02a2961014214004101010280e03240c1c41000c40c08103140c02d20511140c04e180d0b1001c0004881807600ca086802 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 249883893 1250 249882643 249882653
    0x3040308130b070c03150e060601080603031e0a1812230607030c020610031a0c0909010f030611030c09120102160b040b0c0c0a03030e160e0708061507020d02030109 72
    0x1000d84004c403501d881a25082003884900c828866480031201000e01c4240b144900c0c1d00d40f42c0d9001020345042c801c0302c402184031038500300240c80da2a0350802c03c5504000da11405039490f07030003483c66000040d40d0031182811030030039018030f00221901100446120041955554011110080140600400105c0055960604000090040110352000680028007120081c2440320050940340c449200307110800004111407010318040c402203207103a0f000d4403000d04880c0507115035045d043c0e02122900010078400240130640d4101d80c45102d00b04544034440d00004020b02040b264001207203401e01203c0180d041414a84072006000c2d8001840e01e4602d000c20104101414029206000d4aa0410080200e80c0b002290003c0295040d03a01300650368941c80ea030b44071480700083c00c241d141d580c6107000715820071418a00c6809800038507040c03034585412802a0004492500014441348045110740c1003003410500c10b488140c000500d440c12030b800b8040e8000c03140702c007240c0540d0b0780c1d030702274000c07031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 249885143 1250 249883893 249883897
    0x80d020d09171c0e0c040906020702032e0b010c060902030f030d0605040b0406030506040f0f0206120f0609061c031b06060f1418040f151e0e03040308130b 68
    0x220711074114036102c080c41180400c21801240700c218005181100c40d4001c00c8000a0490750045c0450307010801a09500c0c0c424007a00503c68003c3d014801c00d180b500c03145042c0b5010091507079000148542d00c00c0803001c07400550350001403180c01301d00b804403e00040b43c00381e00640901030014040b15000e0200b80d01c06880c5522a860312000207076504004e102510b0207000361541004219401e014083c2075071505503c4810262000308611030207001c403010015012841180c2e140c00030007403625911b0300a40c5c40d06900045581000c5943c4000001d04180303050300d0302500a4102030215102440d51001160181c402108160f052003403500c001002d0007460380b210010381d446940081030051070302800145050041d0412440111644415402038492007585d40d040c4d8110310460181c0d4a603801d0610317502c040700c68050003031500c0c9c0003400c01c4d966040e045503400200003d0034042e01c0200c2069081191031300136500c034181c0c008001c20000b01d181d4201404902c00e2450340b03410310070b940d840089415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 249886393 1250 249885143 249885173
    0x81207030219021612020d080c03120105040e070e18010204090b1c0f0602070f080c06011a04080a061a0a030c1e1d150d030806100903080d020d09 64
    0x36000240000840701d5807140708a1141c2c1d500040001e0084862058001c1402e0b000302c903035013a44c0013842020740d556500c94051058000361602c1e5552001e040980d16907101000e0b40020080100000a02d81424465001e2854101002e8001141071400007210000068001c031405041e0100b04a541c040a10051006050300c5200003400320158061040c0500e0035040d5000c00c1c00040c00c2c98012500d8079901da62015480200161b030307194140b800901401003844040c041590109608020703c030001364041c1683c1c0d207136540030202031481460401602c942c0c0211801d80d042003031b80c0c0b0000b807155000b59040360b00e0311001d42c05030040c14002c07032800c5200354000e54400007110b070100311080881f4810b42d0325a10401e15000058105181c070440c02a485101101120500c4000390301c4881016141c0410000180801c114007030034200108000f405544c0d140c8203c590b00c0c014502d181c09002c1d100300302c0b54050441d07030034641c2c00e054120082d001801d0181aa50701c8a000500103590100c2d0410b903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 249887643 1250 249886393 249886397
    0x15040204090c02031c0b060301090902030106030c170f0303190906060305030a05041401020c1c060b0a0803070209220f0f0b0c0a03150e1506070c090605011101051b07081207 76
    0x446080d0404105012428002c007440e00b0306d0b0001048290711070000f1030341900c0b10420301248980b810700c0424010700c520750001e00131100f9400e000c24a0800504440e441c1c250303040448101d150a03903072007500c80c44240e80540d0180711002080404100c1a04441c848a005601c00100e083d81d80d11218111750181c0329481c00100c00003030a222000500c060b440c02004217100500e8481010000b00d0a007401e12848510107141101d0310f40100981c64011540460010781100c0c84143d403656059a00e0300400302c2244035010309400144005844440303100c480000e40401c0524800e540c8464a8004c00c901066035441e414400d03e20108008022150243c3c16950b01a0781c2e07400c510b000101141d00c034000c0c80c0c5409070346150410106641005241d000f00c108942201c0000e59100012081d10400000a10440f21010f00045138802c0340e00070011034400307894002e9610602240300d4200e0394201e4540c1200300c0c0d0803204100301c910680140c450300f4070480e0002e107000c001074900131250381c0848280c80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 249888893 1250 249887643 249887647
    0x13020f03071701061209151b020c0306040206191205041506050f010c03050f1b0d030b0105070b0403120209061209070911040e060109122a080615040204090c0203 71
    0x50600d070b110380032100e02a154002c4000650400741c0003407080d06100e46802d4480d8030f0380354000038044841071804a0800001040000b4a441044440d80701503c0e0003180150158040300b080b6404c020407500e206581c0104524504510f80301d00e1071202c1104d0304c00008000c006140c183c40700b0214814a8025030080004101084121002c0b4094801c140c020a000300495105075040ba6040145914895450f0400c9030b200c81951110220901a14023120103800310148441d500e0072000c22507849030042c1e903409000701440c0c4801903485204420005040c0d00c851030028002c43c0c402c7d8900d104484220300054500400131002030007907004078090502051100082c090803c2081198000918107401700303002601001c410300b05103000d1031040030441000080090026131180300c858014200902d404089041c441c10711100d1041c04a006140740c001c07407582c40100301d883d00400c104941c0c0c10b03401020705030f6540724070356020040b800080e170704075030207000c045120503003402078040103001c40d40155 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249890143 1250 249888893 249888901
    0x8040306021c0905030a27030609110406080d030b06040506033607060311040803040b0307020d1d1c0204050702150606030403021905150f091c1b0213020f03 69
    0x840d0b0440b0210790040d885292148500010307401105480c86048241091031103080345468521060111070051282c60107400000300411096a000072079150095003000c907412801414441282d1040c065a0000d520601100c0ca41c21700ca80c2043c402d28001406042c00c15a8800100c0d00641081c0e5000c1c2041d40200712a04000840131030681d08051032202030360000115032462a21882a800380400b0151905224040c0c1000d0200301c4000b0f088102c11650303201d07030722100c402c640c0c0c01c15184003005000e400047c004080c03041219204440b40c1008000d070b050481c1c800c104040603150745c284260f44040c0e000c28050b9982d480303410301c01c102540182c4840f5a07450980424071400030100e034403170030302441400042540040d070380a001d810900030b4552510141000c80c039007c40c41d01100c10a242400c01c0000b000c581c0414036018120710401c8402e011040c02440410080d06c88e100d50004180c800f04800c201201c00981500724000b80002c8607003803858503440240e9200c00181101914008188 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 249891393 1250 249890143 249890167
    0xe0f0c0d09030309020928200c1608030408030307030b01020a02130b01200303070305091203101a07051507050d14010609050307120204020d02211008150103120504030804030602 78
    0x81c0d01036801f070700e50407500b1022110b110f0ba182460000b410195650290240c01145800c0c01e881e02654000c24140c560075990403007030381c60003103100841d20518540320015030b600c800000c0c0c1c1e0503255a40003850a642d83c0510460040000d60072560441c490885840050307110f418010b034070300c9140c14012800006080001d082c16032510410b00301c0c030f281b1941414021394040180c81d04502d6500d0003140540b035491303400d4a840c200303802002c80c04400000b40304103010003082580071581540300005a00038822240c41c41801100300240c001d8115110701e409180310041100d9001032a0708003241031404c2c0403034840880d007017401c0c42942c1c00c000c2e8005101d80350300100b503140104401c40080c06030074100f180107842c0b5000040c000b40900d03004110018103440c1901038800780882c1e11b00e007600d240c0c0000a03001a9034000d0780c0e50600c600010745d010400394000328605035400d4a02c10074002c280d1842e540c0031144481e4910034010030070140b001000040840008200443c080c56015850b40e814401c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 249892643 1250 249891393 249891409
    0x140304030315080a020a15170a020309010b040506280f030b01080106050409020307150309080f0a030509062703070501050f0103302706030c020609070e0f0c0d0903030902 75
    0x4240f4150b400700e80c103c40181d44030010101038a50354024040028501030703068980c000b07102c807858070300803041c070401180032400d0303006d10b01c902d031500001e0003000203000c10300c801c0f2070003914050b40100c1d0303001d00d0b04401c40c402240c0d021181da441c5000054940e80714008000a5010b0b0400c17151191491300400044c1c600b4082d070702c090201201c00300100010b41e070002e03980b16007a200d81c540d002c01d0012080c54480c02a806203100d030b90072075540c0b90741c0c1d034400110807140d901105141021a107420041240b030140005c0c1c80e48a01102150f041d00c0d020305101780c0d1403442c0346404130701c0184003c02c05d24000032803c0c06524069006140401919415850a000c120302c0019101101e582c101c868024000008050b5008a80d280d08000054080c03085506000f5901c90140481001c0d801000003042d5900d5031025020140030303800ea03240768481c150001e450700142d1294035242e03000c48020070070700202c181d14a500100d0100c020342c90000c0c00d403400c0e8165405904160302007991000f022041d420701242c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 249893893 1250 249892643 249892649
    0x10f060e1501050a0f090503030a0f081e01090e03130609080f030a0f030b0d02040e06060109141503091924150312180b0c072103050901140304030315 66
    0x2581c01259881100080c400d00501d82c2800401444a15408925016040c0b0a000c0c082c06020740750b481c0020719000d01008520001c0000050603140020780d2a06401d0b03210329515012820013442e40d180410200242411200c00390f404c0c0402c200c071009110750144c0801c02001c1c542c0303c8610140c03402100390f045c09182040001580c10401900d044d05a00600f0301d0b03040c840b24100081ea5400b070340c0200d0284107030041c0c025007042c608141c007820902c2c0010a82d1080a013642d0b02d5007142d07100d26001240c0c040080e2401e411003080004a80e88039080d0b0040c55000c0c54400450b00716070150100d041400107107500540300300d02401004001c402e4042d01181c181070a884003484440760500c46a040048207100c0a000e450b40740c2401d80125100e000e0426003088075072000300c40c40b81c452240c050303d5840f1102c281c610b4881d003100003482012091505108030b00601c145640d004040d00c050320503902803c201410071061039240c00703600c0b00e090040c40c01503000342c1c1c000607418603000c90b403500d10310703550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 249895143 1250 249893893 249893911
    0x9150605030f04030c1403030717060d0b0103060504060b1c291503032208010b12060406050405010204090203040b0901050105030f250e071d060403020d0209090f010f060e 75
    0x82002024040c0d00d02c61600300b5894540949401c3c52802d00e03429030700c56200081118000001485107466020360a01a0b00412040550450b2540d00070407089500003000103210018140c01000071551039800705a200b4011880480c8003407044d000548014404101100ca0b109034000003410300c8a100e10840c0950768002c25584200003003060840b600da0010203014ac0600520140c01040d05d081c03003034555a5507605040303e0511003e4028122100d45030250048661131320081d01e22918101001d002980d0600d070140c82d0940b40c580f501800350400410a80d451340d0204000140344c216440214030030390141007000e240c1c1c1001c46041d82500d5044c1e0016200f980082c5507890000008174600c0f12469009400083d41070341001e220030b06441580c440200001c695040000c83c0b60002483d59040b1000e004840800c15403000700040c03400f850001a40003c0000121001801c0c240f90081e004030020080360301441c0180041800e6503102990a00100e407110402c2001d032113030312003c42e0095566 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 249896393 1250 249895143 249895147
    0x17040b1303170f031303110601150206090604120c0c180b0913020109050d0f050f0303040c080304080d030906021201060e0f0105120609041b09052203211509150605 72
    0x24510f00c07103030700014226028108880025008140c000c01780b51485002d4803050302c01079039540400b5046d0550010f4850050b000d0100064008580424580c2c03240d41d201c0600c00f8580c00d43c401c00c80c1c07649400740040b185422070050100d070868a1030303101140c42c46180c1c0c02041c00400c00b41840021000035180b80503001d03440003240b005030b800103402ea0940c0d13030075991343c0d6203698242040c1c141c0ca0304161025105003c0c1000c4510428404401984203e0150b0007201c0343c0d595034039069503244103c5c424860660000d4681410300f91107a08a0041c1d24040c080240c20070850000603500a4000e07071080c4017184000f259502c082c1094642c0e000040001d0900d1828940095007482d5514401002580710344943c9001608100c000e18900140d18001d51010100c01e0b12580510300a003425202c1c0340410700c07100b100110021440d101e801c60180d1540d200404801c0c80c9400004450101a15025180d1140209090b5641c0074083e000108120040410383c151034107996019070116030481000c010003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 249897643 1250 249896393 249896407
    0x9150c030509010302090406080c12060f130309090f0509010c05070308060402030c0c19110f0303070b1b070c050f0301020a090e0705040b160302070602070f0317040b130317 76
    0x2458a45105406080c59959100c2d50801200248210b840d000e0f80140b411501003103812000503c911103c005070f940408801007802364aa44131801c49410210082e650f00140a0b542c4400f0107515840c0301c0d003800503000f522500310328141c1d10016522801159a5401c00801c11800d0180ba403401d952130a01c00e15041e41c07520028590b0300001d001b940110340000129050460740c00442c1c2c1524450025580c03c0705107408080300c030f456412000d640102d1501ca80e40c1040c40c28a503103c540d603200500541c54400c01d80c2c0c484410002c001c1c229960724290b98000e4003141021402019854801d491116103141010100008140400d1000d4001c0e0300c18880084000d4200000360291000300b46248456074520900b101d803071050f600310300343c00800465040f411000b013199070b0800c0f620039000d13220019101d40d82241e8800882c8078030303030250240d20001c1020503030341d000c054885d00045000515140d101c811850345944100d4481e800c9046154040003444000c0280080e80c001c1062454a80300f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 249898893 1250 249897643 249897647
    0xb1302040b04050d11090123060f03010513060503012c060c0703050706020f0403030c06202a030403051609050408180303211905101202030304080703120915 69
    0x5203000d140d00a00c00d04d09000e052000c200220048404000d080100b29a11046406503005050f01e48504100000407014480d01c0c10304180e0354000d0220b40d00508507842c10080145000b0090b81c200c200595500000c1001c3d1030a0085000c02c1e0302c00b2403200c00420740101800b805002800905410340c00c14014060306481071800c5032a080d8151074007a07152400ea05103078000707205110b00c90500c4400007038004101900030903194400c2d030254004100c6950140e42003000c14040d03c10088001d0b40070000c040700c8001c00c0c94480c4041c0c01d80648820015010700b012031440d842904280d07407580c840a00d080c9003c0d404000400603105070802402907040aa1780c0d400d690060031043c8084020f601403103284c6071020410386005d03c42441c07500003001070702c007031210002d8010354113101c4046151a03800c00c3e00950f405910300035200d480700080c010b441c00e000c03044140ba040804a81c140810000003401031410410000618026900407100b036520560103099104947c0c001a0034041647c0c41e508444d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249900143 1250 249898893 249898897
    0x10b0f0916080403090e0a060306061706040305031b070809040510030302060112140d0c0209010605040302010912110907030b03190b0f15040c02070504060f080a030f0201110301090b1302040b 84
    0x70109041011103500d0740e190030f407544409508100249440682045103400c0d01e0742003e02142c1c000c1404201d065101e0203620b20405405c00070503101c1d0300c00c4010600107441200195808a04c0c3d110500c240856104c0102803640541c8050b160f4040c08500c00c0748520301032140380e8100b110400c003500c203a0f1030f5540282d1106014429001c400c100d0700200410320a81c401c0d072240a41c03908040c1c940b04007a640016203290114641a4018154540040b501a0242d011170702900d4050711042101441d120608250504000342150010040b403001c401d651980c800c4280210340c95200032800040f80d8040c113286c01ea03616005101200c0c0401c8200104660300c00240e04144003014144007075469206280c0c0284442c000d8a80091500d50060a91503010030440d0a5410441d41440140e5413901e000038001c404c3c0c00394034407a0f04800d5034200024010704002c04519007500000c1071031290340c468440743d50000d82c00f11100e20340741c102042030341ca0705000c444a00291030300114141402c20440055038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249901393 1250 249900143 249900181
    0xb16110102040905040254040b0406060f060210090f0803130501050a06120f02040b19060e0915010521010b0301030b09010e1b0a0306020706061a0a0519050c0609010b0f09 75
    0x102c01580301c0c2e07041e081441c00d043c41858002d01c404201d40d00b2300d0710706401c811100311425138559107466004221100c0d01c1080f80201c50043d4010102c1000c00302001e0020007114404507464400d48450100162126014600c925a0040a00301c1c56010b0f0400c00d081d103030001c207a441d4980c5804018442c128812a8401c02d6541110540381080c09510100300202220300d5000d070710410000c11561071802d024103d80c255503403555402d40c0c54002070144291540d00b0359403480303031031010032001c2070030b52051000e041300021140141a400842c0340c4040c00044081c2c00ca00a00e080000051080c404580c8805030403126400081150b00c440d03101041d00c407403103c400360031281d644020442c801d58402d00c2a00241d0341007201103589030241d1501d0401071640e8030441888090802c01600822640001e80300901d01503241c251274481c40000c0c0303a0f07003620440c03040410700505000e200400325040040510582102d800069400c2c004000c022038064061b011520855000c810032080050b02d0000402c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249902643 1250 249901393 249901489
    0x17090d0807020409201801121205040e132109050f0109080f03180102060c041e0b0d0603020405181509030f0c07140d0b161101020409050402 62
    0x1c803016840080d0142441040280040c69140341d05030101c1040c1004030001181203c601d20044592403580710851403d00c80c000e40001081e1803c004900c0440100c802c01501d40b0b0f00c54941601c03003a100300921400e8890001041d20055054100041a446c0000c2c00c194006840c8401c03000142c01406a41c140c001c681c025100e402190740142d01171000710000e840d1b5881510210303c0b020049556039004010104500c01103007070100101c0d4000b040641c050101c0c015000e1410b4288030300c844003208004002e1040d48000b44000920f404480d014011000c4800703130200c0c501d442e600411090701c00140651508007141d100c003000d20310340081d003c0060fa0700d810140c0381507a140c2c0e8113a401d5000e02909084bc0800000b00c001582c00003182d0b80003075a1888161100108003502480508100400005c0a080c64000400d42400201010a0240601e8a054800000d00308030060aa030001d600c002001130b1580180001c40c5081c05c462086d1801c00ca024400f2407100011b20b0032841e0340340182c240c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249903893 1250 249902643 249902647
    0x160f021e06030610210e100606050a1d0a090212221b12050d0207090c080411030708070603020a0305060d0807020d030e0307030809040b010815100c05070f0317090d08 73
    0x261550190310004015070398296804d4405088072403285c05000400351007002c0d402812010003010100341704603000d9032500d0b80c2d45030400741c0d10f51007078600709280d81d90599003008680f1842140e90f034100c004c101900309c094002d6280c9400071040b01c60444043c1c00b0000c00c4140001c0710102c25084d6091031512074224550b20307028801d42c5482c0c6440c500300c0d0002e4034020081800b6209001002a5a00700c000c1a6421142005d5031802c04008840c11810100005080e0f400420040384401803856101c6500500ba0f8141e103568101a07460501d1503440000401c0d004240004042e4043c85103a9000343d00307071202d545900c00d56440442e588540200284280500b0640005151141800c21001a00078048580c619100d0410360760f550000304040e84aa42001008540c030b5104245c0c80d03000301904604003004298860402c0000032285030044100800c0d40f1040d00420403c000b00d00061038002a203100316811810100c40c1e05c04951009100c0100c100b100c1c01031500c0c3e01c0c07541000e41d900912029 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249905143 1250 249903893 249903919
    0x40b0d080a14040801020301060f0908010c1202090102030913060602070b0304020d0b13050a03031509090218070c0203011b1e08011e08010e010605090603010903050409050606160f021e060306 84
    0x2c109401103801440c01d0f03610110010450b5078220340e459001004603101c500d04a582c41551500f03880c20303400243c000a11010925120325465006801c100300c050040d6420942102c010807051a00001010b40c0c40b038a0302d02c10400b00c5d805000050142c030400c1b541e10b00e185016004030302e004060b07200040460b845d0000156030700380904450455a40e200701a40c0c1000a6420020050800e5650a0240008541000441c02a50300c60341e5509940a0080e2184411800034a080b00600802c0c1006000401a880b40160380a105000350100100c034440d90309410b4004c020000900c90401509040081c403101c0011a00400301c01d04540800400d0030104092900f488056070050303200d810258201400d0b0f100c60a010f40141094a00c140c4c0e02c0c0c80c480d5981800c25086c1c500400e0050080380007000240040141900140e5005070068405480c1824071003404001900e1000c094401c031200c1032401e021441c200c4051150400914816808902074800280f81031101801c072074030a00d1404004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249906393 1250 249905143 249905177
    0x30708190501110a0c0302100c1d01050405040f020304060e010902030a060b03031b010e0c031204033207030b0f060a050108090703080307050702030c0306010605031906051c02040b0d080a 82
    0x249140503001c1d070943c0d0b11114207507006001c60301c50720310450141c06100c1400760841254802c1d02080145036075514100d1903100d00c00700291800d610701d01e040120410010405480714040c01120032079503400181d0300d10f8542450401c443d4400303956100c3da41031240307500241c0e17400140f020100b504a40e000515132501030001c0c4c41c0d445450200320384401c00050f09440d80e030044d07002c8012003a100c811b403407080b031403882090b03119140d40010300901e8a0601c0f060010860030032881c1c81540000c505503114038283c840318155051200082001540000301c20b20800c402805126040081600c2e50029401c064002881929480c0681c2c1d040110000008100d0001007090070010768000c807000d9030741d04003588010300c2c0784d01c0004141c0c0a40304440402150f4100020305030b04864207a541d40b400e54450340321000c24000b0141c0c43d04d10b502c0e1112004590ba40c2c42c103c3c1c925030b41c1d00608080c1c0010885106010650307119000301031090072200414408150400221800c1d0585841c0c01a034130403884000c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249907643 1250 249906393 249906401
    0xb06120c030a1b0e01260109020a140c0109021e2416110f120303010e090f01060e1806060906060a1106090307170408100f0632030708190501 62
    0x1441040c211905500d41c0070b40c0244a48030303007403c2030742c850921001c041d490a8207041b1002215507401107000041014141590241800c0040c502c1d02a0002d03041100d03d1005400500024015035543d5114804600d48140e0701c0c0804c0400c062084843d00c5904d0000f90300d141c080340308400365071120310b06503a00360949048070151410701e41c48820416803400c020080307109511a450007080f5104040000707140220403a400740c44800011031a5a0070b1004209680d00040d0444e07086115440ba048001403080c05500060000103625100301e28080303580e000d00c20700304c01c46820260043c0b000e0098a803030300c03000c060b4404410f861417956000381100884000b8056880568240503481c240860014003100030202d980c020402c20082c0841068285203034495131090301d00b268001482c0102c100b136913800c81604854017060004480382c1d10100501801c4800030740c50030340001003400032000002004400505007083d001408182d00700400c0d1541c6842c03a00106004c000b003220301808101342500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249908893 1250 249907643 249907661
    0x60316090203071b0c2d120302070f06030b030706050a020a03031109060c0a1a070914010201110c010203091c051e07050712060e06040b0103020918011e0b06120c030a 73
    0x3401c1d9003805603814120f405076980e000740c11441e81d1b05085a1804000c007081e40741c60040b88100208281c1ca0600100c0340b26482e941d0032000c0d409039641c00150340000e81e800070014005502c011032004044420141080340c40d410260602109101c05090b465002405606540c0e0505000450b0300c4803030002e062500906079680e5128500240c1030003041c4011996a0303041d44a100f40c0e10041d104a4a05107820404a826100140a0507001c10040d04980c2001e0240302c41800001810f4031b00040c1e0800300d6206201d071550685d00042030080e024010044068900400c3e040c013040c0078480d07400204a482406145072070f640c26201c0340c2c6d29540d40c40044505866200d800c13900c80595500d40e41402051307110081e50742c0d6141441902e0411000701d0303100d202d598031008094640e82103a08002070240007414070004031141050104428500344034800c01214203403c4400c0300c120964240d000d54a05503e50782c040c82081c0000e00501003900701d070f41d03004409818416143d81d240f580310001400294 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249910143 1250 249908893 249908927
    0x51e130503031b1005010b0a0f1e0e090906041e0c0902031003140f03040b0d09050f0708011a1c02010c050d05031b0c0a081308031c0506031609020307 66
    0x40740310991282040581c0b5103003154003a130308154840d03011002103c00034490713a40e58031810800c40a46070310810304010915110b040208195441c4005008050603000b501004610000d0342d084003440e0249000d039104c2d500a00521891506513a020119091001d0005011401450b03480401040089420160102da00e0440d120300d810800d50f442e4040718030090382c81e580306002d42010300902003040045a8a01c0e8000c5141912301021280a40e108180c80c036440b03541c030252080020b0007480620043c0d400e5038000c042c02c0c0e003424021381c04c68000340540b000c40030f442103148900d6262072500c120500b160044040480c90305000603201c0c0c0301e900000400a009000300d0010264002c00a98081c0c01d900321034070142c90185084241d103216907c1000700300d13071241030341c0070001c1d14400060080d20006e201d005e0b540382e50745026900c3c3d500001451a01790380e0403856000030384154400c1642c07040703044005103d080220f03154401c00350310030b00035030070001d07000000106c103540185010b041900743c00e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249911393 1250 249910143 249910147
    0x4050405011a06040b030f13120905090c04050a1a0c0d050a0e100c0b040606050d03111b10120b100e01030e01052e1203020d0807051e13050303 63
    0x3480c0c081c0c0240088100c0c600c4400316000c01403420b080c0070080e02c05440070000b0451542c3c40f6801d18090041004015003001c0030004039201c000f07802098900001c0360341c0c0d15441502420401001080a0010907d9045100500080240e95506040d120444092004004a6008545840318603125480c0301801c06e1140e01d0001e81290390000040c2030345aa19039845240100c0c40d42006150220075941d50005511403130800046641c1400341504640b283e04001540ba0b920008900d070002c0002040c0e01003034143d03030b11080340002409084010f886c00360240040c03205500004484000300f00d0000200000c041c8400800200c0fa8440d543c00d800090104640c4501038400410201f9207440f002e0010b41003440030f035591141405064020b030706800e0031484c00250031034008080c404210402d44207810300e410025401400c91104945140a9409803c0c400740c090b2018295023805801a01002402c000c0e02c03a07480407038042101491203000c0c3c26a42c3d07242d03003000c50308100482e400c034079858040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249912643 1250 249911393 249911401
    0x60702030c1017010603051006030513020306090a0b06030102090607030c0302031201030804031a0601020d0e150a03060807140f04050402120f030408160308040e040f0c0e0601030b030604030f08090c0405 89
    0xa40780442c1c02d01201d00e00d0300c07260317202d500440a0700c4060f40c0e42006004491024004540640c000560200d0000c000c80456842500000c0c0703004410380718481c0d9500000b0103007060040d42800703180e010006a00035841c01204c407000c00e04a109140028003000348100400e01014807d0080b162031883c0c00c1d880d034400b56102c1c2007907446c0342d0051104a514401d00b0301c080c1940304100c0146445a0016000340103042c004103c29209000210f011951110010041d94101000c090250521213410303540061614200040c4503d40f40e01c82d00140501031401034400c03259602c4520b021100c1e00c0988000c01c10381c0700c510120f000c0b649004124540750007000e43c040d0120000002400c210f881d49002c407044252044034942018859000103010307464100f00c103004200c0c09610950304140309900f0300340248016110308502d620b19400c00300840350400140201da60703041c041c4129800040300505540c0c2032595000e400d402c1025171110034424040005000d4060602568001c84c4000c0d00a00240c54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249913893 1250 249912643 249912647
    0x4140a03051506040e061506030703200403030f141c0f020703020c03010c21090c17070e10061e03021b06010e010b040608040611091201020c151302060702030c10 71
    0x860f000c0c0d010300d142170070b50605010300040082c020814542c50001d01d00e00c5c0c80901c0035650000300f083d0240350f240e0f084515641019594920204802c0103800c2d1607504606d001071486002e168031004214158072940c1e601420030301181c0c0c0300012054008609141c42041c8000b030070807050045101071000c1106400d1640202d181440c440046008010b036050095081d80c1c0403403030194852640042500c50030300d0002580c44221520301032008002d000ea991803407000340d013019500300729581c1c0014034100010070041407080d41000401c0404001d840c1442c0d0002c042050032215480801d1011000c10b00a0b030090f8103e0f800107410310340343c020000580c0e0f6050b0703039483c083c414441581c0441700005411098041a642542c880d0741d02c0451507180c1342ca4050262070300361910030a040c81001a0070b1943d440c0382d04811180c1010340050388401d2103030034180c141019164455500541c0804200606d905404840d0200b90f04803559505c82d035050020a00d4101e072480b915810050340281074138807079 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249915143 1250 249913893 249913933
    0xd09060603060902120706120b030a1704090e06010e13060603150608100219050a090f0e070e010305010302010f050a120228030e031602030c0306010608061207080304140a0305 77
    0x41c2c002d17a0a940d505034020082c0340ea072020303885443d000030f00303610b0036041880107074000e4500804000c04585441c2002d49950700358000b40d40c5e2044031050006000c002030011070140440228031840a481e040d890309160201c4018001c082c40e4040120a2403c0c0801c1000c0d070201c0060754000d016100002c5101040400401060080341128420000540c40a030001d00880796108100c0c2e54104804801c03520a5a05802044001003070001048001c2000040d10b05203900414100ca282c1c422800d20200180240840c04810742c100b5040000500160360400c1c2c200711184250300e042951540008800c0302e41800c10206039812500001c0e42c0c0203a41e0045c420412007504103612040a040d01440a90896898000319051500140811742e00500c8407011150800c0c0007505854142200780b00003820204240c20a001150078941440344074100a100c4102480c507a00c01403805505114501d075880c080c5100340b104600861080d0785894642c22051001503174044100da03a90361f24400f04504031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249916393 1250 249915143 249915161
    0xf060903030108161a07050304081c0905040e07030b07090509090c0103060815060d030c080712030501060e130507030b0a030308060f1e0405040222050f1e0c0d0906060306 75
    0x4d12454024451011412042d04101c0c0d680c04031100c0900c0010380280c9141d00011815245400180000581319005002c203d2024507403030700020b5900030101c4083d1000316240c1100e809181b8006102c9000d0304000394000540390441114840b42d035580008540d201c826400c1950464408000c1c81207040c4001000108080b00343c034280300c215100c080f096070320740c0e442040b41e6885056001069490900080841c08a801703890b102c100710807aa1146185580980c108540404104c180d15500700d40c1031103242e0243c441403034200d0a5080c0503000030f03048010100d110042a030f840020601d00e600030762080c40c8600000c0c01da6100311b9034a04000e04083c070111000790083c031600400800344d00c0c1684219202070711240d03c006001c054041440000c040092040303820482c1e06200004400881c01082c4140891b804049680e14200030030100808001d465045807004e019050020fa203080d0005561103030300c501e03c1c5601c9090800d5480f01502c03860710007502d460f207400c101009010541d0800c03824 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249917643 1250 249916393 249916409
    0x10e070f06020606010203030c090a030812160503071428090f0905070f03020703020109061104080c040902061204081e093115030b100305060c0304030906080402030f0609030301 78
    0x341da81e0100343d80383c100c111451401070b00b08100003240101000b0241c901c0c03403406130803449582d840366984c40e442d92100d0817002c11600810b003000020451000644503086003458404e08500f0729160140c4207981c140041080a8270100c0c080c03e6a0300302c201c1c024180100b28004c4c030704c0c5c0203942201405403620b5005c0ca03140b42d5090900401c9420003801000d000344410703611000e62940c501012002034010850440846d5214800d0300b0118000703010341c5c01031080d009145c035a21484c012050749007030f410590742c5015a0418450001507505c04041d13582d4041c2d0a0702070110f59440340740096551040303400c0f0b0b000020350400440301100160015001f0b614080c1e405490300041d6104100f52030039921030f01c0c419554410907241c000043c40d00034060540380300d1551141c094585c1e0300c880011404480c0400031f25000c6004005000702086902e80005803642000d00d18145074400912141d8a4000c0806002e007400c08500bc5480400480081c61a0703c1d054940c24104069207503160b6200380314103c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249918893 1250 249917643 249917669
    0x6050103030309031d01080f180f100609110405040c020319020102030f070c0b0403031512120807140304020906060c060406060e0106020f10050a11070521040b0304140c03010e07 78
    0x14200510851700000e12816105c0f011995150040045540d80082100140d01c0d140103074958051010000d0b000500188030185c0740c0740600013070303134000c80707040345d0110000e41d090039643c0b403052030824221019a00705a40c0490f1000440c40d00b80d1440c402c001c203c0003201300d15407400d4000c07a810f5000d14081c124080201642c0d8855480480386044800400703880b1500c0813010800081c0245e10513031031500d0a084410100303503035107541142e40d0469201600c0038403005040742c22031540400c0c22584034149061002c2c0160951031402d01e107000061000717009400c9000840d072241d9903201950781501f91102180c045141ca445d014024003107034480c01640e9040c59001040940c000b00701c031052030040c0f1380108a02c5164425100141c031010b0003031002035591720740703118203070301c0340c40c000d0221a00803c01404041004005070508100e060111403600c402440140618800541100d8019800c006403010a10b203010a160401d084181c00d943c0c5503280042c2e8050f800000325880c801c8a511700b21000e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249920143 1250 249918893 249918917
    0x10618051009090503031f051201020304060c030204081905070314030a0e040b011b02120601060f02102306040605460611030f030711010e0a0506180102070605010303030903 76
    0x1c020f441d40c65100608540043c40013400b49101c51654a82d07009203a00424940c903a1a4003103200e01074010540800d994002040009210310f50003054201445407500318503107894003603999101c0c16104240004506104d0051041c08020000c1c800919005042c420141d810203038040c0da80c0c0e01c10102003000c24074011a5000c149171038840c90010b65010385801a00a0300c841546d000a884403004980c41410f450514680e241d00b04002d0b8040e0100d91203103846205c0c54200a85040403c26401e810756080441d9140842140f0514145400e41002d03600802d0b2940400500a816a41c00c91a0090040c154101c110031f007462042e40c0641d44900d0f0100f40040e0003440440705152801038840704000f040041204920518611420381000700503281007103041004100d00d9401503880358000384070100300100c501c0382845424601892400141400300080c0da401da15050001c0211811038a403158420100100b034049859081d8000000c00541d84c4a180180083c480d0700d20640011786409561 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249921393 1250 249920143 249920159
    0x50c0f0105040b130810060819024209190308030402220e0106050f3703020415090e060112060908070b10090e0c0a030807050106180510 60
    0x8004840010380d5100d25041c20484960516407114820441002c000400003a00b10414006c518614404c031201103015460140038a2034511464129103010696400e4940180d51302e020020b6087c5e8900a1107100340c10208060342500d00f051440610301d00c1c80f480401c0d440e00e201d00100540740707044880c4400a000a00240f440c1e4090380001014010200041005444e28a10f03540074032400c84802c0c01d00501d05401c2c4030070b81d80d44204280c4160344a6800317004500d4841c800d4984d652050f984e0214406032f82c400c500c081800700300305140f044100340079828203c01d01180207010390f80140040c007401c04d02c1051161700070810310a66600034544454500340711b8000c10464100c40c1c4042c1c54601208070b90300c41600504021070100d503600703410051080000c403400707002c41c417500c00762a004401a25105904041e40c4a4500e0342d01581c02c165211055a84e842c0040320a2f00d0304507060a071210113600e00395005080c5a080120702503107050b600e00340101c2e0368010300e00c00e442c8074070510112a030303480300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249922643 1250 249921393 249921409
    0x709110c0709020c010b1801060306052b02030c040e030c07050409080421020d0f200a0b0310030b180c0103060b0a05220602030a0e03060402011704060e0712050c 71
    0xa99000d5004600204001c0036550060200320765682e00014541c0001d0b00001d400781086002d0755401041a80100180c5070903200b01001803030142c482d40205d000425800d00c9440c8200403800c024201e0901000135501e04111003443c503000500308220141401c9081f80d966000850b08041b540700b016030105060030f080c02580c414560002c4024201800c01a86100e98285403003195001310803109200096175503003102d0200fa5005180449141543c0d0801042c5040c68080a0240c20f18659a04006486291440046480c84102c0e643c607600c0d148a01c0402800c1980f0103000e01b2581420721240c85109006441c0c081100012070721001c40200040d0103480c001e01c21401e180c8000d01c41807460340d000c1c0c00180307010442c085020f49441903009000c13950350070f01c0d008603006030b001080e40340c41da0b500610350075203c0324114014960740c0303010303030001340200d2120070229400403004e0041020004190002d4550b0204c42090750349007502d4946000110281007001e80b428407454184030348509150038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249923893 1250 249922643 249922657
    0x70f0510150f050603010b0c01091a010e100b031b09121524040c050c0d050912030405060d241d0703021204030e1801142b120e060705070911 62
    0x3044c0b5041d43c0c0fa000b01c803581a04811918001035484004072400600344c052400d15080a03003046540e654100034207014110070007014410544103901043c0041c40d4140240c0e5032100500710520100c2c40e050705030751850b0243c000c0341900020210480f4100b50700c04210074529010706400c00e40243d85200040351500382e002c4441c059500300742c503581341a0402c0e0300020381502c021b0801d02d28100d440744000d0310b000e803050008230000e40007050542d070500d401c40301c00c030318044440000c601349400c0030001091441a001071242e21582e1710710381c3c10f43d2a41e0500c80001b48000e6549040e10710b665400e40c1c0c041781810b210301d03119100540300050310035002e4804d58012050180f090b42084e42c8036541568040ca28044541e400600050010504061006254040c00300401075512010070074007440006480c902c0c0b07420400c5000b0023507a0850072000414020543c11602c400f040c0c90000905440e04101d86800c1604813600141181c00d0000000d150300032141203c01c00c000602d054140c84a480c00b8084c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249925143 1250 249923893 249923899
    0x603070308161a0c030426070308060f010f080c0d0902120303011e0e0403080619091a090c0f0906090a1710060602100e010e06130303060905040209060402070f0510150f05 75
    0x110100700414525900704011f4210a03014607903404158203144215045420106d00044d117500c1000158180181c00c030703003100c0c401e00f0450315007061208040d161400041a021050101203080004800700380c04c90f004443e0058000b82c4400100004d894403544240140e103142c0a90710061040e06002c040c1c0d00c1e088545c030300b0369150717a0b441d030703641c05c440300c160251450342e0040c03801811440b03a40f0103a40d41c20041280c1701e000202d0401903071803550014065006c80f4451000142000071078892003003200c1d400424141896994641d680005149003e0380017056000812103101250028841001c06000c561540c00c680d01880d1001041d000c0d00c0e854082d400060708400c41d42c56034a011a0030039894030300b860b800803400464000d074140c83c04900301c2e0551120138000804905240e05445000082d280d0003206022a18090700841c0f40c10030051f01c2c0502413980000c2840a01140864004146074080c041e110070f0300c0101e045801a0489070101000d001e0282d4002503038186507120700341103c07400707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249926393 1250 249925143 249925147
    0x60f0303091a0d0b04110c1b030f0c1203160602030103061b05040504021305030d091a0309060705071401060303110d0e102607021c110c06030603070308161a0c 70
    0x760303c644060b085480055802503161400c54031400304000160004030900c40081401000ea03080340d1500d580d4009103107009400c1030b108d0003801a0041038000341c0b10010780d01011002c0f00c251000e480c1d445840384080403060000c502000300f1241740c0080d1304032805140e091001c4682c914016020000700d4205034045101080200301d81e040079000b505a051085044651896860000c24185030310f0407041170000b28200c80c24044400000c1c01600030622035000300f41145094400550380d003401401c10014800d01040510400c070032060f10040c10b0b1000002072080380d91b2850003500702c01c94a00c0034907803801005648499907120304d8811070540801408480818407230275081e030b090002c0d003070300d600e40540780311501d841c0c0304140e00b010f4082c3c5c0f419801045400814aa84407070900c840660208200001d170718040030590002e80c40a0400040303400903030781e032240c40c0024600149540000c01c1c07820046080d0150f00881c00c03000d24014003500d001902011048582135040710121000f072600003003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249927643 1250 249926393 249926407
    0x506010203090f01141309020304060e0d0905010509120f062202010804020904020d0206031306050105010e03030319020c0f030711100504030609170309011a030c060a030b04090204060f0303091a 85
    0x82800d22401c10000704103003900c2c1c801301c0400b0007501b02882c0c20044a00342c000040c0010042144a603c142500b550b0242601e12810038005040c11031500c20030b8100320011440d21410703074030101c0410f21002e000c82203070301c0401d003e020f0b1038031148116145407410040200e809981c890003c070070302e1034940c140d44040c1c1554869082024100d030160060ba0051504c10405c1c00681702c03c002140607003e0100f90820f03010708c9180c0707a0140c81c41600454100005520ac800c4182c40001c1601d41001d004040c1c58200400c84603024024025010f41d0b111501c41c0087c1d8581d5000d0110040500e00d00500600d03080500340c0b002c3c07041c401c400741812400101c0402c01040804c0282d844901b00900c40c03005104111250789011f80e0079001600c010105035540c0300340c081c01001c06528400d03052826800740000c01d000100180c3c1c180201600442410745a80310400301d9940c50344100c01169006008100d000d44503442109042d00501088011841401c00440c2a101161f21710300c2c0041c824460500d0040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249928893 1250 249927643 249927647
    0xf07110705220c020610050a050a03030305090f0633010903080c0307050607030b030114010b0f0903120301080f1213030807030507140105060102070605120109150b030f0a0506010203090f01 83
    0x2044014026034a200d0341c080d00d8280110f000703d9201d0b6800f03a000340041e05081940e8000120a540580d205101c1120100107030317142c1c2070303500c4112505420001225569039440b46e09080b020f843c00c82d6a40a1070040040307a42c0d200045690120343e19440b10300600025801d01c02024010281d00c0c00300311002070400004610000030a1142e540c28280e0f42440380310382d82d00d807601005440c00e101190f164041641035050034480d100030060717401030181c115490841c85140c5803007100c0441c6074010000400e601d0a40f01045002c9640d20003010b525929070b036030350308161101c205400741c444a01815002e041e542c0d09501c2500d0003030328400c07602d1b09840d01e10303910400f0702c1c1d020141c12070a0140c207102450101f607170709420400b0301e924000049024a808400241042c0e12504040144030013032082e0701d8000c803036414040c1034500d100e4002034100641d00051414484503808002c550100008000b4181c8040301c9582c05004201741c10700a42e1103a80041e40c582c081e46140980000d40d00c40c8040a41d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249930143 1250 249928893 249928909
    0x10b030604050c0d0c330e0a030809121b03010c170703021e0c0f0609030a08040213060312030204140111100b120a051f0e070b070510140f07110705 65
    0xba1048240d41d200560310003440040101440b0500340746c1e4188840014082041903a40d54220010310703004000410840000340703403d00707500020704240303404900300c12103072a07460140303480204ca40100d85042e580e24102e14070102120f40038a0081d400d00d22240c015074046e88220102c29100794000e0034541d01c00404230000d4100c4900f003d145203011840c0000050024020400741100501a003070948042c207801d482c1003030142c000c6403a0b40c02000100c150a500000c41500154104d40c0b070203080d59400c82840203003075a5040540504581c508e017240d815003507401001101d400602811150500c01d0065620f5690416039814a4100441d58100710b00341c0d1340041c0c444000101503800500410780130504c2d00303e00e1301085a80742d20144a85521384203508000c0602d00001c1001d010100d030150341e5540705c201511402e182d032000425800c007004003c0c0100106c0d540110410417500000c4a5250013000e0240e4080481c85c0850003c01c90702c5120728810316040c0080310013842c0c0c40f480d200c140b003040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249931393 1250 249930143 249930169
    0xf040506060d020d02041a03090d0e10030f0608190c05010219020d0219060504170d020304031412070b04121d0f01020a020631050306130819020609010b030604050c 72
    0x790b030b1708000101c0c1100700070040100405411951035124541109400e11341001c0d6400d4031300b03003d2007515941c05541d81c002d24003442ea060f481d0118600700c8170100302c005801d0542188001d03000d14060328040d42c07043c200000d21140500d01582c1129912001680c541c1c00c59010401034040300050103026040440c8000c0c401c81c03000d0102c0104240020011040140c0c9810000014600150401141c2200c0285142c681c0c0300601a0402401e0302501a507203201d03070310000b82105a0341c107642e01d05600c14041d14a2030300c5041c0b41141d0700c0d0420300d04803101003401c540480d14400d81901e003818161041245e4444185005038401100c000603007040040c1c03003845441411441013660210040c1c41d0724001c3e0050502071100e0081c494064001018000c2d651807064070303411251030042141c1c3d940010f0a84d00300c0c010342e441d014980380300c2c24000d0403882800c45200a0f40900901c2c031a4050f800100203102e018250000c03c41400d46030304050700c42d0f034152400f428075848159410a140b804815001c65 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249932643 1250 249931393 249931417
    0x10e0d020310050a020d1d0a1b0806010b0406080a15170c06120906070c03090603200703020d0f0302072012070801050f010603020403150f290f040506060d02 69
    0x4502c2100c070000003903500c2110140c24040d0042443c40c0e20b08500c0c051a02c41c00c104501c00b05940c840310f2516640ca08075490081c2c0000b00303210049090300c0c40c1c2041c00300941500c4003600e171190384540002c1440d0303205124003800121a40c0000d4400102c0703104d0245c18003035100d01003000c00e160103c402c0c1501c0d40c0070b4a256460044101c00440e07540c44500510402c8111070140203a817400158880c1044401000e200621035132040d0800041d0303001e90110b003a100d05060004103244400500d00407040746d409500101c2c0d0001804a0a24ac1c0015000384031030030707a0303680c0481a030b44e80320224241c0c066140c2c02411340d07100421204049501800c4481030a601514050f14511000d022614140442e40204c806035581ca0901c09806001840c25014201c80d04040d880c0620b580d44062038000b44c1c0050412065030f419002c1051200ca40200d2814000080c0c4903090b514440c180300103241ca130201d2288150314008414110b07041c18091240306800041190341440341100e514000395000c3c0c00e1f2514 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249933893 1250 249932643 249932653
    0x7050915060a120b06040303120b060c190615090e0105060a0503030a0305090118080717160b06150d0e060112030e060304030903060207110118080613020307081b030d0e010e0d0203 79
    0x4d43c1c0c860f04060001075010b1f903562204d141040070401700b00c0d105243e62500600042045030310030720001a0001100c08001c4030603e6503001c508141000f4003004042000c800e806200c0001d0040481d04a0032030b04076098002c0245490f201e0800c0b20f024114032682d60190010301081520fa40680e002980c0324041c000045404244d0100b81c518006650b80d0450340100007044480520400070f0781940c10404841d900d61130720306000380d141442c01880000504014140340064200d80703518400e401005400380310940c0300c0c0040c4241d40c014000706080700308184a02d000004041c036500038412081740c2c05480e00610031150105100d1240d20041041e010b00061140000000769144000c203500341c026101c6540260b10000010305082c600d039075010343d418508100f401000d9001c1583c94120f47c002c0e07050708014944d407000c030381407008036807201440d4054081076008954500010511141c02181070b290f01600842d01030701ca441ba2900303c2400a248800c2c000380741d0425542c1d00207028001000c230b803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249935143 1250 249933893 249933911
    0x5011419050411070302070b09010e2205040b1806040209070305220602090405062d0301090b0a05041a01061e0c0209040c0303090801200a1e0207050915060a12 70
    0x1403d5801105880281d0311000440c44141981071100d000501520003801c0d150404110000b030591102e9160140b1404070103e0791540c0c1411015003843c05e01000030140024075107404c0000195400315207499025002c500b02204505011440c10701c42c60b401405019a500c40003402c0f4014003008003180c0c441001d541e081c00d152400d032103625501510650340540c0d1403002005120070713075401030800790168214028040050300c2e01c1c410a000c627104405042c141c1110400041c1c0507000014001d001c2100d10410b02c45072200030b803c40c500c06c0e80100c2081c403034405515042000c0358000d124140000b0300c0559034088a09500c0d020611003c0300740b40504c1e8007007007500017500d14241a03904464031a0f109608008040d0480194001803010100030000171210b5080d03250940c9032500401c02c2c0c50307000030b0140241c50081910020302c00301d065600c035032607500500180da102c241d0f001c0c0b180314107103081c0060300c107081c0070b4202404002c01800c054101802005d041d0f4010f15052004e0520940f500003003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249936393 1250 249935143 249935149
    0x5062d010803041409060d0f080d0608010603050105060102030a0801151e02150907050f01030b15070f1b06090b0a0c0506160908010b01050924040b0a0f02010501141905 74
    0x4a40a05100d80155035200d2800584921a00c020803000d40100903081c1045581c2c0c4d250110f0102c829002400d0041c0642c2034036000c1b0461140348200604503150031404580c1020540c401000d503031042008010301d450742001681d0f00c1c0501e2034140000740414005000d2034401c100720301c800175a1800c050381c24002c0303807407103040380f40303210341c4200069000b0800480102c0e1f46020164009501c00086c155031801d06020a04060412004074103045d11020804159292141600500015240b05070b0311202545480c0342e5a08507071034280c13010380001c2507038041021548804001ca4403a62103402801c1d14101e24044107800007111001401107020703040c070200c2c4080c03004a00c03d0102c6201c103480f00e030001a01401c8941150000500353b0b142c2007034070310b15903002021262a000b080b142c3c1c201500745008010b4201c0c42c01503c040840074045030015903102190b01500510706140c40b4480100088402242200d03024803925007415044a009115803d20800504001c0c0403034006a4a25450b9004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249937643 1250 249936393 249936481
    0x10315020d18060c08071d030a020604060201051006030b0f040506030f0a0b100b040311040509070911070201030b06090915010203070212060f1608010b0d180b0406050907030506 78
    0x8030341060b42c010464810800300340b20b4140e980340103003414085420084402045400750320640e004802002010b580e4aa40c10002e800c6030903802005255074a8035690002d000e0002503802d54101190710b80003080d02401b03401261404440a44501c401701e6a0b03400f0070001d40809024250540184281c00d015580c0c10f10001000a001d030310318102a043c0f2040d0003035035103d561301c11a040c0b04180021310025020b01e4500e00414411503010034541c4403003407160b0030004107502040f021480d0041c2441010404005010098001d0300c08005404050b801c0c03200a12620f0b1600d640040039800003440103c402c0b400180d5980184103c8e0b00703015440d030100c0c6000d03901c2c25121113580c0c849420000400171161900d0390014003148006c580c030480940140c41c0b180d042c0203090044001003569116041190f111481036081001a60048481402d01c060060401c1d0340c151030305814800060f07070031030000421904607a800b0009080c00d981c0c0311014584a1a503000a01c0540c0290f01840b00078072210700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249938893 1250 249937643 249937661
    0x10b04140d29162a11060307030e190203030901030504030905060f071e030c080d0906110730050d09060e15060f0607030f1101020a0c050c03010b09010315020d 70
    0x4203500600302440003030320260480c100c100c10031902c002c0849501c43e900c070b403600d100c118603c035100c1c084400d032034404045c04003042817682241c000710410006640c10b802c101c2d5a40094800e445401940d80c08010700201e1000f40a505588100f014030440d51295108a500a02178503107403011a45480000e007040d0321001050b84648800302d10305e41404a1442121420071200a005003142165034001c0d02c1c20303000c03800c01384c200d4101042c081018942d81c0c100840a03a84200c041002c171482000c00c2400b6000000259101e8010210700c0c03850090f540b01000785008410101102e030219000112680d41c130244c401d00507a501c41204c0800180721b80584050f80388804058440004140d202d0029414004d1036107104d1060500c2c100c2c26030300d40364100d40c00c007a014070b841240c0d091100015030381c110280e030f9414465840083d4030303c80a50700003141c2c1c9181d44070f58107540d081d80001c802c2500ba04c00c0070380e00d0f0342c0c410720703140040000444130300e40069410305940700503003001c00c001081000c03212991 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249940143 1250 249938893 249938963
    0x16081e040f0302150c0c09040f05070f171b060c01021608030402011211041502011503031808060c09060901110102131406070b0402060915031608010b04140d 69
    0x210140114903100c01312095041c40310b6007490508415240481d901c2c1d040c030103080e00070800400840e0902004120000f02540c1000864800c281d82c1c1c0e201050300d0110b0703c01c50308034992072003190008400129080b64105942585c0203041540902000303515032024840300c031650b50030800068803101c51805020254080c2c417140b6102c2c80d0600002d480c00b6009030403103188074945a0002c80e102250802c0d0390a5800c0d0380c1280144000c500703016401080203c124001c4000c49042c0001003507803211100c98008082080502031550307441045903155000d50f040c2ea42c00d14280460201420050082c10710707080140340c0200031007102e4402d0382c00ca80c07000b4107480700348100010902c1802c90300100e0015281c01580c10074a000303802c1d210340441001c041d0009114004c00107544103140c0e0341c0b2011012031545828455500d0800079281c0c2810243c00d4901800302e8015800020310b41d01c4003080d10125141040b41d141244080000c01c1040900940304550401a24240c908202c0401030b040041e44030304 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249941393 1250 249940143 249940169
    0x3060a06090c110709090c0302030a0f15060503070b070c0e1f270e0309030709050a0e06010f0b0a050d090305271c02031903121116081e04 61
    0x45484582541d11040b40c2009020a000d9420180003000411030126038600b1400210a81c091030000c01c900441e030f101950501c01c3c4038021003072001100401402500c268102e0603900c408440f00000d4940d68880c965041c2c10801c010000d60400100400700540300c2c1c2403510b0b003d0345512568058590130384400345c19145600e8041000704141842c400981341f8210b20b080003035200b81c000540c101414001070003191b21003440c101c400b078041041d9500300d80c00500395036503281c8410040300201000c55004400e01e050040b0090010400f04480341a56a2a180c05161504002800407142d04c034000042c104039040188244200d100d10070092010b100381d990316603c00311104820144c24400c03001d0120b44a074003d2802599890900000130741c0c0d100041c1800350802c500010f03017000807441c51900416072151280003010b52020f4000200d00f4904010065211207048400e8540600920450446072402107800400e901d02c001d49212000380002c028800c44216080040c0d80040e40100003541c06 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249942643 1250 249941393 249941399
    0xf0103051b0417101103070509040e07080109020405010e091507120c08010306150806011511070b0301080616020d0e221d120a2102040e0106110c010e01030507050903060a06 76
    0x3c18020407280070706960301404100244160062244400f81804041c08000144030400d0344490700114502940d217000c0d03c014964035051b450103001004822441203280100119103072960400039401020864014080301006640090101130b002c2c06000c24445880802c0c5c54044490180c2a090ba081e660748004079491842c280041d9003541c001c1484015002e041441080710010b4580e04403192400720b20f80300c207503000c1d0650307034514480500b20150280c4e5001044003039488005504a80580d070450310560b40b814000d14400c03908100000060704400e3701450900e2084100380c0f14200e00404625503034454001d45580c2401c10b002ca4549103884101031158400002645c1c0280c211100c040c140f0030541d0400384009100b02448030050040c51504030300f1040076594654182c900c40380e0219074030742d1241c1010710589000d00c50f49002401c0c40a41c01756954001c210800c1580040c0c443d0f010108120700150050400200b00d541004800c1c0128070081c2c0d0700708001406001151000034400b81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249943893 1250 249942643 249942689
    0xc030d1d060402011d0105070c0b2a190c0e09101a0121060f08010e1002040311090a020d0c030212090703030503150102010f0903051210050f0103051b04 67
    0x25a40d00100c066801901c208000350741c01040121100d00b03108141c480050170000142c0310b501407804060480707950740c07202280005050000f815818180d01542c03400112006c84d04054058030720200c1001e07086100c49105440c2c1400001c25074900c51014400b40e0760b110403514941c1002100c1c00c100310740c841c460564049180c0c0c418414041044c21078003000014150019148072001036418155982440005e500c003a180e0340010b02400080b011700d81d02c1d650300d048840c00b03003841c0700011005000e03001217031141c4040b502c00c036400c5913401010900400161010000b600708001c0c080380d10107400b0003210403544124482e103180100c4075200107880300160100300c0300c1404000c2403040a030f40300c0d40303080c408a44c0090540ba03204102000003c0301c410b0040c0101d016001d4040d105000d103092203462810150440098210403011031881d01803a1b862007031750281011035100e541c3c1c11150b003207040d4070b0551207a008194440300c0c48000c102c07175805d200c0b0340c1d4036140d00c0b40d4085141701c40283c602050301342c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249945143 1250 249943893 249943931
    0x3030506040b030d0e031908040306050702030315060a020f100e01060510020622050a0321050403050d02160c0f030b090a080d0b030c03010c02031b0a050c0103020703050c030d 77
    0x50010354041250488000220340c0e284900c044e40e101784508103041d1103665900700040c0c0000c0c00b241154403507011643c0307000591034120b0301040310f0550a00000903010341c40041503a1042400704940511a40c002c001e008140c2e0020071070901b140030380d401c070700001d40d0100082480a100480000355215810000c6800c40d01141c004c2407080d0780e00c60001c0d81d800d9001803001d8200c900c00006d52844110b074031000c400d055501000030054001c0451040a15030030103880745c00790649500701422504000074034400c45208480c000c010400030300032103195154550142440c400040e01ca108102403036110340305d01240c154000004400100011f000f00880c20020540000501c0010900b000b0240c1d0750742d00314014030990705645562040170000c2c42e5010840c4031079212001e0001c110510788000000e44983c06100030140d83e06c9a810100400c0350000b80030018160803001401c2d80102e11401103000e9440314005808100c0144012065004184000c08001e822107000081c0000c1c06200714200c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249946393 1250 249945143 249945151
    0x804150614131404080306130603290405070e090c0a03080c0f0d09050402130306090f0512040303090b0c0f030c0601030302060106051920030d0b3d120e0a030305 71
    0x3007418002da600704240041c0f41680c2065220700745a8072995072038046200c8441ca400858113071400d20000006000182031100725081d1003000c01d14082621140f02c100b980007d940007091070717012081c1000350031010b42040d904440c5841c150354500700d203000002d61603071141d0020b40700401c0005005015000c10018440d030240644042c000b10a04200c001c0c1c100ca90611400380140d07000100218104801100074015550100040100300303228141408010485101110180b2407a03000342200105407003600c0480e40e055417801c02890030205c8280140c0c100c1a1080040e1080c0300318501100e8052000d1302e48125850010402ca62450500078603080040c0d0004041c4002013182030460a6419807842c0140070500b07102c01070301160181032a10030961064107199000104441c50101c1094120703c0d00b00c8402c4036906680c03120b159010039041440000c144e40d40741090480c081c8610f410052646107005403c00704c00042c3e020040c3c405480300340d90318036440c2d04207101d10301c1050b03014810b032604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249947643 1250 249946393 249946429
    0xa06080715030c0e040c0c060506040b10030b0307081203070206010b030403090302010503040f02091501080a0510060c051009060203220b0c16050a03031e0b09070804150614 76
    0x3450326449000803024802075008068440307000031005801040b02004851002e8420030803a00700707544c0104511019802240d4050800d40412214502401000814000244016800d00a41300c043d00101500040640c1600401d0740c0024800030030311282010303002e103040441c0d807854120002820030905070444400d248050040c003022a601c0540c4005507a82800c01583e00c0d01c0e581028a080016990021f610014140c108007511528206541c80e140c0d0a80703813846142c451116480660f80110741a06a041040004000b6544210352180c1c10f540108151222461000060345c191007000c2010744101da000000d02401001e05405644007a0012a44021440c401d5132a4028508080c0c2100d00c59a0040354201c00e8035400d000d10070b001a0b104048801061480c0341c058003404095003540c80741e8000300d50080280d50710b8082c4184503100208160b03201c1ea180c4071305991412011700103481c2c20780f0401e152182d1034403e00c00c1c0e10240c0160707030090314124417403420081e0601c03900d2420741c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249948893 1250 249947643 249947653
    0x251416150c0204020c010b0415090606051206041512080301051c0b15010207080a0f0b0117060a0c030b031603050606010f05040e0a140a0506040f0c0f030e0c0a0e0a0608 74
    0x64296806400541d0565040f03e02582d912610100c15024251440616901914000e01c541140c084410003034100d840040742400880e0f0780305400c3d078507406032a049000c801143d0000074078a1516601c942d130340c0c10307464640d003e80340c0c2c4070122441d407401807600407201c0400c0003005000e5413819115103400329004d081100304da002c1581d81c1e14040341d0302030010603241035050a03085041e802409400045c203140001c03900e403008182080042556412070070f40d5079011080c00031030b01012004541035000c22120040070903444500410004100810044040568a846880da03556041c80780448203910080401e0501d03080d410f04900300740000c0c1c105410300c1000440348081d40d030040c3c02e0f035048455141100705540e494080810103850070802035610300d14039008016034079015a000300d0103a04283c40421003100380211100454014040300c101107141c04015101c658400e8000341c0340b910300d032411794040f000d10303002007000084150172500d4005041d50412501342e080d480b4520061010b000104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249950143 1250 249948893 249948929
    0x105070c0e041a091f110c160506030412050a0e0d05240603070e090c04020712020c030a020901030605060415060e010e040516050d0e030f0703180b251416 68
    0x80d0b5036a2842c1460110411001c0c1017604c3c0300959070001c03094101c0000820b03a601c0700d154009440304524048140402c5e68004045103d042100540340710b10340c0b041c02040810700740801628160002c21107181004014440c0c10f41d02e07110b01c0b0301154514400e02c020400c15180205c0030321690140310001951003210410080c503a50002886411529000d4113104181c60f01003c0728180b804181000350058000601c8008010345003e45110114040e803c1c0ca06112000e002c054551640c0000658002f284400500214030140d000580106008100080354281c00d00300390719502c0c90340e000402168210100030b07250750304588a1400000101d5042010749005030240868880780c2941c2820400041103115202030123500821068150704200c98a440c0044010000c46d4040a001c50000780040340100c00044c2c620720680650700168542c5040c2134021103840e40304100d00300e03800d00d440b80c244c04003c04108041c1c02c410441240e82d026080031403551004507000744091b4440c03103140c84402500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249951393 1250 249950143 249950161
    0x902091e1309020103021b03030105010801240305190e0c15030103020a06080606071406060109061d0907090e0f011a0412080304020409020418020a0609140f0105070c0e041a 76
    0xe00702010301d040029036002c1c14001200280255034501c10b034010115603000008400101031412218243d07a91400c80e1303220f06075021080c07034160040c1d8400c00315001d1480d113075000f50055980014654100d08804100300c1201080c0d40b04602100c0080d005185281034a04114a00c011868081d90b001803a40d4550340c0422202d9840d4490341c400c00881170041403066807460100c44246402403808507921030000301254460800382c80032030104d0f1070b249000a05900943d161042800702600e018111450002031140000004103608100800d4182c0820380026268519001e2040d1504035042d81d8141900c1c0740d4070f548811000316107a6000e0204001c0d03110048245070360300394030100d0207459840314404640030b801e120344000d5000e42003940b8522700030707040858100014002c0300c00044595550b441555281243e00038441e10701c4062446006505180352903401141041c50090719020540d01c490000e03e105401a4880c03400c500140020701540d1540001c4600403183e4410880c1824900c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249952643 1250 249951393 249951409
    0x10c02040b0409080409050610030506030a0f080f0a122403030315120501020702040b1903081c02040602101109090103030c0c0f12030206090a0201090e0c0d060902091e 74
    0x402446039840e04044546a10395410220080b036001501a441c0c80c0c8a00c2184040d00e81100d60a00aa00101c0d901001c180b0a015050080c2c4014014110f091b1140e00e0f40c24000f001c45005980b4101c2c00c001101103540794200900c0d62042559680020761030010040d01500c4441d03a681340000e0503440c155882a0302c4081f02c03412641d1501b4001400040004d4280604045038496044040300b00320120034010107400a1081074402c0320304108111018040250511502d1051200b1100d9007200b0f00c0040c06400c024980307001e5581009400e06140350315007060342d2090700044016000b00f11460700680c15401590b80060482c4281c0b410b0070007540201c0e03108501403102504001007180e0110500c00b028034540b0151800b0440140020340303400100c0c82c0c00c07604a00440040c4511030005840c15008540903050b1030b8141e507031000240ca0142121103880010707102c06140c400030040058644103512405000f414501070151701d6003c12410080c610050517041400b620380500700301c4141e541c0c00310f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249953893 1250 249952643 249952667
    0x3020c1903020717120d06140114030a0b130903022d0312060d0215041e0b162f130203101503150311040e030711040f09020d0c14030c01 60
    0x81343d000c900002d11482407801102c4400c0c0d040701c40c03000490444404143e00504244c0744410315180384207081c8001140d40c00807565640e0f1481100744013152040060780c1011181d42001000052020700c1c415003001259400c0904502580c00003101801001c031010020003600b03000c42070801c41c40c01c5242169103034484c0c0c9401242000e10f40000038081c1c2d5a05412161240d0050494112110789595801543e070181c06104102c500c1d42105013a001b054400410139525134281e01802c0a003580388007445201120000c55200d4000d807465101c0d0241c20317451031408004590301000f840b14030024400901341090003800341c14010400c002011001180c00c0e000c0711140c076100042000e85103003c600030b00d0081c058618419010f400081031008440e00d4061011084500f00810106400309654a00c94880001c0440309032790100705042c030706035200300080511448081801d011603400a0400007100e1401c407405055800140001e4050030284802454140e004204444003440040e200e81101c0c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249955143 1250 249953893 249953909
    0xa020601030209101203030b01090506040b090906010311030910050f0603061303050f0409150f0509040305130f09020a020105010905010b0d05091608030c0c190e0a06031203020c19030207 82
    0x84085035410001000c0d85004041c40d0116a8070401c01c0c0c58003c02402c8c94001450002c0c0030b918021945217400011030741182c0e03c0c1e506181c50401d040e428803032004801081c090516903540e290345086601d401c0114411030340f00c0301920182d03078150005411200e002d84451042030380b05041103e02d03100000c40641000c0344083c01a840e211601e402c84442c451003d03585004070001c11300041041d01c5030004907194400f0564005219121030341d10880036294405e8a510400c48404900480d018078018000c10003011040c0c001c07540c49204100ca13420080c1d0004a2040d0b0010741c09540d01c0e4203101e524050007103000188a00d52400d00010468081d08141c04100e543d03c40c0440c2101404002544e034540c00345540044050340c43c0a030a80700d8001064000e0310380641c40b41741c90545403022002c12002d464070028019282000b003142210396009003174410389036845401001040c41e5002d00d0b01950382d9590b016036a8090740c1003550a00075a441140510159400100002a0041044801c0d61114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249956393 1250 249955143 249955159
    0x50606040b1b01020a020703110405160c060e1207030e310207120206100b0a02030a1b0f0b160201060b03150102070e07020313080c1302030601031103091e030a0206010302 75
    0x102c41220203045065450311550361001817030b14180b50700401c814086034001c5020002c1c16800d04140415900d0440d070f03842c207140d045003119040038001c21140007018003030f0000050014401044903c0e040c003030341600000c030703001049410415a02841800c055001a980a10307100314045400c80c41a6140e0440444040b5031000c0011140701d076419105601d800040001c4a01a20f10020b92605001c0d56544d66058040d00301143c030000103011100030000d00d60086207440c4404000300c6800c02d048510040a0119401c940042010010551905801011a030700709051642550040000c058000c9065905180040100701c40000075268014000700e100001d25444000403428031889130022002801c46000f0301440d180d001001e06203601c21500b400f46180c0d104c0727440325030311400030404540c82a40c60a00380076000160b0091504640b043c100821890501f940d86095504200d982d160a503010b08109003c4100d000304c1c403000c3e100b80f04081e52034034010000007522703141c05000107802007502c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249957643 1250 249956393 249956407
    0x61a070b0f1306060b0c0105090304060c110103060e1005010e030c010806210307060f0b0108060d030c05010e073f0b090703020d03022109030a061d0312010315050606040b 75
    0xa4051040340c2e19500c01000c0081a44858007034070701d03400829614419601e41000121440e600108685c2030b40d2041d1900c80f4004402e540c1c80051002c0079101c22304140c2c4941d80000c02c0300198222502900300b203140000c2090401e00014613003608071154912981c009000140d0698000355241d410003400d8641414a903000900b090507e40c038031421070982c0c03100207a00707c14000c99910287c40004082c5080c8038100ea8900112500b40d420340702d1a41c0440c40080c200002801581010740c80c07803082c1c0020801e0012001d10608040d4194802070080e24003205404611380407090350140301200e4a01c0603e0344541e903207030508042d03403070314000c0401c00741c0408152a00c108220b03882c01140c0c000c110302d941c030310780d40350094841180d650203180346001c10200389e10308203442c13041c0d54950300042e0080040c82000d480e110003a00f102c0b50075215003040c00b403c05110a00c180020098402504850360b400d51641c80c1c01c0c0145840e400c0312052151415040c0222a560f840440302118102000030742c071254 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249958893 1250 249957643 249957661
    0x9060309080909070f0306090218010305100e270106080703020d0503040902130305011d06160c02090717010806130f06023a020f0702090711010906061a070b0f 70
    0x12800742d8140c0c0c010954420400c2c035560115082c10082602d075000d004845c0c2d40d010520582c0600d81644156002c00001840301d54429405107600103802201052140d5890044480c1180290340d2040c80c40344080d403c00b4403916012504012079a0031000700505841c125040741c030b0f10241e0100920804480d00e03503406001d000c1007507801800e910702d004c640d1021312000e0301e0300c2c8012a110454955007801c41140942d15210203402ca00c101d100040c1145a07980c24108040c14440341d00c0000303000800c00b445015859421540c2e00c50f1125449081c000f0506c0e0b007400136400016405800c05500c1402008200f4049400c1c8294403603000d0b81060100d16a0300d4224042c0c02014540c070108070b030050038140030001082c075580001a104845004903580c41d2080390a9114920a10500c84000c1280b40011f00340043c0c4c0700e901030800d00d420514110145002400d42301c2420080c2c0300d582c2c0b00c140600041421a11138100d20f8400301203030f4035120041c3d030b555103414070080003510711465040024080b10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249960143 1250 249958893 249958897
    0x30b030a0b012c0c0712030c083606060a080d020307080f0d050424020f0f0c0c09071101050105090103020d031d041104030510050907030605150904030f020c030105070906030908 78
    0x11200344000c0c0ca85400c2040a01c4e070342112605590340c0c411050840b1044e4040c4c4140b0080d00d659590b5000555a000c40040301c03010b414205400c00003500d41e1302e0041c0404000514040040040a03245030700b404810003005044940141e0f4884e041500c656030015000011240415400013696823244041141c801d00c50155074144050f1070304110400c010002d569007840445c509240c82c6c2444480b0140e00b010403400b0700320000f01050010441110380d45003000150591442c1c074030440d9018046030b00801c00414003513480c40081401d520741e00c01104000c2c00740074098030054400c461150326540008034010201e250181c20301c40d40c40c1c14400f4101c44c0e86a0340c0d040c050301900501010315104030101030340d84144000c2c0d6540c020000e03180303480b41711400390600030041c001c0104806802c0d900c5400041401500342420200354942c005150f407079207902944903d010b61204003d840309580042d040c42c50303206003d407080e454039040101094021703008005640b003d280000e64203203980303042107481c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249961393 1250 249960143 249960209
    0x1707080613150c02060a0f051003110f180114010c03120c02010e070807060206090d17091f020309011a090117070f0f050a06031103040f0318031101030b030a0b01 71
    0x810b09007214090229000500940500351b145810440c240301c80c4004002ca6400340c42221651400480c1003000c500030342001ea1158000801d9050382c10351040029240c0d05601e50162072030040d507001000500014841c0c11021902800c000c074069000d039800400c01003503045281c01f400c1d500c01d45048064400d600c00281c0860f45c00071680c1a940700e100740740d501d40c0c243c42444014803a02d4001200040b000c01d14034001010703501c81c914030b41099102a2a00c04000b00285260320851850310040700295240300f00d20300c0740401c01a6170b410840300342c60075038402000c0b2034481d01c03450030000b4a5849814005046a0307070081c0072028440c03903810807404c00d441e6502000c060850f07004041082c0c100714242108840c07003101c1a01c04940d5a000c15410754541020034080c0304d4080c000140070580e80e181a80b1054800d02d05001e11405114410703282000940090700d90200c8402800d501d0358040c4500614941c045001705464042030380d0350004000f05000d61206540030000c00c601c52040d055014400c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249962643 1250 249961393 249961433
    0x309040504080702451b270f03011802061608030c030106080906040c060f09150801050307170703080904090b0103121b0b0601030c0203130f1707080613 67
    0x580c0f01005c0500c1800042d0049541d2100e800d604016102c11603050b02c10085290080a0482d590b44c10050100c00041031189940d040100411072291502e1110500d00044c0c407240c0031210b65099050007203559031030114602903071600002d01010003a9046040c0203660450700c455541542e40c10040c1e020310304444c02414140301005100b400e21400f809941692580d07614510180d0b0380901c408d5441c3e0003910050003080b2080307014014507200b0b00000e00410038505003818010b81d558155034110340c840814800007000314005000034681840610020504800301a46001d9003408844c3c44120324400100390340d40c0011001e40c00d031616002034180d140c1106c1280d00c19a0769040000c441700344410710400103252011a000b49481005012419a81080703200909685440040d0000e12011000c002988801c0c8400040f21303a100002401501c0203110000c020342c501040c038100300e03502c40a1501142c0002c071007032142090008005501c1918800340181d54900d83c00c0200c000d40020310710400d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249963893 1250 249962643 249962659
    0xa05071211150412090e1614030f040c06140409230108030d0b0303120609060d1502090114040812130801020a0f110601060206070e0402190810090209030309040504080702 75
    0x202e03103080301e058511a60180a0390544409125011104000a03016a44010002c5404610780c40361505d100c081c00f24980c144000320203803000c03469426820480f0000c409842d000104803c00036040c01c9000103003000e00700080c00c0d09840d0041e150750700450144400c4941d0f144651718242205450b010b1348903107840c03809801961204011a100da205140c294035840c10f11540845e00e05001086605808000c698483d043d16410700300006000050400d96020302c107412032034080346140c40720036403015440200503030307800e458000036040649140060682c1d113014001004424000b00744000340c00b035140030660f175030304601441c680d8003070860300030424640c4007180a107846d81c0c00c5100c1b82e020f815180c07500c0d5150482841c010390340750001d00031000140c1100c40441d03801c42c09400e403000c449a0007000541002542c1404080e25901d030400e590024128200b4003056031074240c1140090002000d085d86401c4456000c0381d5a846101d95080c041d0b5540c030001800d000c0003c055941c3d80e5170041c1050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249965143 1250 249963893 249963913
    0xa051f0506220b1b150c09040209030a300503091209032a010306050607020f01080a0f02030a06030c050d0506010b030709050d110a09060303080c070201050412050f070b0a05071211 79
    0x404ca4522101c2030f00c9886103000301240c00154101051113034148003442850060101e05010194118401c03198141c4601200b4000040040190380900769040c4c002540400410081c01c01402d0541c24810500c1020814040041d0020038081d00d40c41180c4600b580c0c888420000c6031070558424412010728140031000d0702440100303142c520034031a00340d0741070280c00d440f182003240751300c40d20030025072240c41040c024840d54007883d500380d030109039038500190081e0083c0d44c810580c0c4c01100c1c07000344182d40310418001c00844a0841c0040c0100380c40c07420406220b036031069500c9406025085e8400004000103010600c50814030000d00301c05440e0000407841032501c1c00048a0300140a132040384030800110341591030344034450403241c040e40e0b0401c040c4c40d040c1c50101c05900001040e41080300402000c941c42c031441c0024040c8030b10540007007005030040b100013410311207142c1000100d0002009060409070703221043d10005500004490031030703003400b88256600700014000002602030003410b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249966393 1250 249965143 249965167
    0x50d05071a01080307031103270a0803030708040308061f030b04050a020a0c03051606051003110603100501050307021e030406020f03030907210204050a051f0506220b 73
    0xd01042803141031501c1200c4014031106441000c03d0240e10070f103034014002c2c000824403800720300c0c007015500c0c81500d2515078041c0e40f1b03c0f051041c500b407984d603013022090030b141c1d00e00b0040380300c1004042c840041c42c01d5080100d4004d2128030090000b5003040410030114035a0380c0d5004003103000c141d90007064580c2241c016800341c042c0041001192085150070005006d500c010300807a400080f060fa19140c0d1044150b4040e507158210f5160880c0d01c40003a9100000a138140c40784601814004000444141c95450261b680e90303203c0484034007c41c000d206028450150041260076200e090801039101d0342c801e20300720310780b03000507102c1d042821401004600800001c4020026954540d09454019a00390580b0380e9a21003600c2134956540032510401c90588845854075246042c1040b13070080c0c3c0c81a4001400f5144103690310300c85d031542d82084c001203903840d1304140c03c03808280042071402454480041c446011305040e561003210f030303102081003030205070007901c000c2d040c0e207480e258440000c0c800d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249967643 1250 249966393 249966397
    0x102090d06061707030201050a050a12090b0402030d09140d02011101051617010308030c0c0f03031e0114010c06050a0b0405040803040c060216060f050705031b010b040b0607020409020a03050d05 85
    0x90003101c00340f00c501d441101d42c1c04510242507030303010f8407502d241c281e0188045502c2d40c03200c8007903c04c0144000000640100d54001d12000a025041c0740c100c1d81441e004040c20004155a00d500f40070702e084080006103400030214286e2002200d0f18146000035000603a582145411049000e5107000300b0000c0c03c0030194201052420300381c8d0740313981c00302c58060f4844030f00400303000c0506000c100b44000303000d885d00c002c02000840c40340015030711045604a240c82c03640d00241da40003501c0c0e802001d198450b140c02c0e6009801440d2240b000703080103080000203410b20501c45001380a1544520000e4030f0100d00f504044540340c000b51003000b1030700d4141082d000d240c1056504803135201d11918000384151000035a40e4a2650140100c0c3c0d042c0c4c40c01074299182c0000324076040a00c20140b01081c08a0301c1032000d0101001d038810703890f00840c4d40c2000c1c0d80c21104580812803050785482004d81d01c0d034558030140c402881e415200001c01c41070034000a030310500c20783d0004100d4420403079140d070a03d0784200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249968893 1250 249967643 249967649
    0x3100603060504021305040513021306080c061206010c020f100c020306070201020c0717070e0703050406060b0a020d180902030103050319080601210b06031305060c090d0b090102090d0606 82
    0x180c204451600c610411080c0d11403084400d10b24699254103000514103540242d410401da003200a231003070360981c040307054580944420403400355240c0081061040501a002c10003104480e030f24a000d0360819400c603c10006890a41001542640302086442e4648024040400100300304901c08c0d91080c01440d9080c103210880c040d00902c0041003002c1d00500a541c41c0b14030302c901034540941080c3c07000240b51802c14a04449114107000000c62050050f0168010051940e01040724901390411000b030780d48a43c01907000c0c81c0200152031601e940826812a000c044d86014190803007016500c0e200c28032180c014a00c038070302c00400042084000401821a115100e080125031a07070850b09445040d01241d406003c03c12035040c855010818004030100c90140038000140c5900400200790590400c403005814000b013103811360144001001010b5102ea040f0018502e0200b180000c81d042580d42d43d0002c200007810b001003900c0301350a405480755100d015001801ca8446422729001500445c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249970143 1250 249968893 249968897
    0x11d071e0315081f090f0f1505070306080d0809100e0a081306171e06010201150e07200a020105090a0b0a030912020c0d02060307091802040305160609030b0703020f031006 75
    0x280b80804c01c0201801001d003500e402c0250300d040c0c00b1680d1a50741c60300002e017004450880982c0c84407040350106100301d074000c0c0302c15034000503000d00342080c80703240894100c60202888400c0342000840f100000d07840d12503a00544021a1f2a0101c4d00d0319494140c0f0b000740204025008a2098030070480c4135264401c0f5041580c80c010911481e8029444a400c00c0d0b8145c2003400c1e00b0070204850300c9000500c00c0d0000703418030000880d4090340e000050014455000b45204c1d05d2114140032400b0b91085443c03a0602401050b02500045552110b5031041c9240c8020b0501c0400300310301c1c40a0303441d402078400502c00b0345071180d6a0001010700400500190341d088402d000c0c80c070702d0328122a200103000110704c01c000c3c042080c0320041380c003000850b4100604039802c2003c008004640500300d62103052090404c07100c0503071511300f549001703800e00100701000c600221040ca010050550b001840c01c040720f0300b11b0200d500548818100302d02038032520340340d2118443d000041c001d48102008684003152255 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249971393 1250 249970143 249970183
    0xc030b09070f060504120c03060e0d0f110601030f1a1305010c030507020c0d02040b060705060a1802030619110307020c03010e01060b070b0c040e0f011d071e031508 72
    0xb0750880c200b440403501410000820501061008071581c0c2e0000f40401d01503068070180a6481e580c035402e961086a640003aa0080038201001e590410140c200f0302c00e0608201c5945001225080c1e942c1d481480090029120b0ba9050400d10455066482e07000340545045a824940b0003424200b80034241400c036219031910400032602842881100d00400c0325501810303511030781070300b00600840301c024140d0740301d65280003444d02c07070f80e955000b0b190641c4184080c0900d8500312202600b1101c146400c41c08200d5003c80004c01660041000c0e603001001104004a0070810b4400c100248014406040320600010078050354580025503c2c280020440086c000e210070100041d09998142c803401c6070340c035824402a40080d00090f0516440301c040303809103081c565501c400040c441401ea560b03140c60b0300520f00521091802c00085000a9100f00400c1401d061100000707200c18140c0c01e507910070a10400500031198402e0f00464010380f06001c1d000074a5455030354854a440e0607001c840c044141d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249972643 1250 249971393 249971399
    0x30309150f09090209040f0230040b16020307020a0e041b06080604020703021507080f07030504050309040218090403030c09061409060c15040f0b011d01051c0c030b0907 74
    0x880c0c40071411690300c035641c44041c0c5240404103400307900512205503200da2162451802c00190b4400307802d0103a040808070200c0411680e140300b001e12407a16a26805d1601010800443c254408442d080401041500340d1502c0d034038422419406051f0f0003d60007088968006107042ca40c030321640c06240140c00701c51050303c56400c20030510505204140100b401440014a60301d4a58040e02455010340141c80c001034035040b0034004020708507660380118001c0820301034507074a4030b50442d9000f007040c00c0810560505807680d80d601e0281584091050307800280c090301d6140524403002032040040c2500c20103080c01c1c903000d8094018103e40350001844201c001404922400400904103d07090b101440c0519a80c213004460f485a000a400740c800c10000f0701d900504044141d116070b000300344002451400e841c000701c0301401a03000340005c40d46058030744d106100b240c0540341101c50490300d1205030150240520f04006401401a0600c40d40d1400001849000664284209804803ea69900b41c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249973893 1250 249972643 249972647
    0x11030307020d02220501090c020c011407020915030303090a06150e18070f030809130203073e0705031905030d050c040f0b0a14030c160204020903030403030915 70
    0xe00380081d50001d00345203203401504212401c2d46081c0005a8002c1d00020103524420940d0405c1c0c3c0101a586c0e030352407045c40c0081c0c0c18014081306c60824070309042403ca00c040c1841f41d03406650b1001c1e100c4c00c100404100208802440741c00e58810180c16243c4030300e05a604113031200c1004009407031341030a20115441810310542c64600f82c1e240221403408a454980084906c0c1d184104408410f216224010800140f124014001144140001aa907a000304103009852180055440485005005014100740c005448000c00c4403901320241203500002050142121990f048081111200c0300048480d14003040c50000d8070015011180c80e603003c800030403054440c04d40007400c560420b1140304000e42c001e07081150010000c459050809460f024020307017690060380145181c00c800603400c0b40058000c10840000044030191a0a5140041c10071440b80300b106500300d00ea51000e1603034000c55070b960b4142c2d402400c001d0101c0362100c0e140c0c81c010b0028081d42c003072502d200358642c4482a4280c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249975143 1250 249973893 249973897
    0x20a0807060c03080612060103210f08130203010902040507030b04050907080309010503090705060a030207060509160b09040914010617060610030e10051006140c250e0108030403110303 81
    0x200c00340c0c1d80c41d0142c1d005460481d406032014200951110045003041d042d490100809400f0f14003804684190303226030120f01a010f4400e000350003c3c014424413202465030080c07216640507400700d902c1450070841f0700c0000c1c010540828000c1d0302c1032501041c4403901da4140d001d04100b00e016101040341d602c2d103404042d55401988240c0710340d9402040050140d501c80c030040c41d08441074804481364140c5400018216400c650001d9000a0303000c03540c03c0900681d40100c5400200003406000d190300035001110b00c0102c180251207101c400002d0164081c0c8460f404103941030703040070085618a54042c50f039400b0b4801482180c00800c086640d8101f160000b20700d076401942c004200da41954414041a4044c0c03115882c4400a4000c030705021401c009a80102c0344210403e0542e4030415080030005000d0f4034082801000105051100020040700080c1e4020040a401d6200d0594a02e410300ca004401054010503440041c2e00700020302040000007510a407441f407012800001100350034540d480c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249976393 1250 249975143 249975149
    0x21c1a09090304090b060f03040308070306120201022a03070305070311031216020f1306030c0f060210110403050a080409050a0209030d080919030e1201090c060305130b04050109020a0807 82
    0x1d9001000300300503040650303000408510002c0d107914100103480e030000344190030032035054001c031720b10300c04121405505200382c0001d4030448402030302d506503d400003581c1d2841c4c131040e20304c0c0d500590a1864034041460603000450001001ca6540a44900c1c020341c440e2000d2101711103040c07259400002d54640031444858020111719041e003885514901065440e045d442c040e6003010844ad00b40010751242e0b46004412080070401251047c40c62030911100b4a03240c0c800b807400120700700705100c06507010455038000a40c4c00c5011802ea00540b41e04446072003154030041ca0380c0300f0b0520b0102044070a0000e0b10072554000820062561003040c12016481000326031030380342e000544c070010250701802040c4e40240000b4201d4403203201c482011030400e00c1049054000c98201140882a4038091a109414001e100001d200891003580c2d070944031403450080c07200381511540000c00e0408903145240c0560340108130f24046041509141c0e00030308103140c05038080d00d24030388045440c1c2400605a812 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249977643 1250 249976393 249976411
    0xf0705030d020106320a0b18061603030905010e03040e09160506040e0712110c011d06160519110c030d2703211715010f03021c1a09 58
    0xc4010311034a40070200c0781e0a0064800241d0030381502d140c603101c0c6c01c00310029028a03040180e0b038400c49207004001c98140b800c2544118400c100c151380b03965648100c0c56107a82e040c1400b01d141450b030310301503000d000c60710140c3d800ca12020500040f0222804000740c0500c030054180c070300344141801d440c80c8401040c0070313403500304008000400054520442e00e543c4021030f0f2030030f04059801d41ca40c0a054550583e40d601a01c4000b06504420000a00c11140e00c1c4503200892980356010704070481c1c80350801044021050603446100324070b81d0117081101d41042011856003100d03148658060700b4114840281480d51203a026500c0c91420b0000d820007141e40d5985502a072070720026590808800b2211202e041d121300840c00100003100100d10942500e03074104828100100381e90002c0c480b55507021540b06191140d0284598690094913120341c1c581d0a180c250092110ba607000d6020f84905030640a14405010401ca2100c4480c2d020746855540100444c038007941050030440646410344071124 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249978893 1250 249977643 249977669
    0x112030203120c0d090c0f05030105101509170703060c171504060305030f0306040513120e1809010905120408031812030409020d060506040305030a120204080f0705030d020106 77
    0x4010340300700c02c920f50021051440e14a4250103800c5441130391160441101d549168041c24007106a0140e14500900400d50003006103107050700355480c070003802d885042d01400d929042034400a108018800240401c030328001c04142d545855a40c0d00c40341444203403011450908451003a034070030706030141d81400503050000c6d80d0700e40c0a11600c000d40414407140d849030380d50300004000b8200388050040c0000100d10581ca901d40031052000303a0b280200b01e8103035040e201e00f4042c005030780000c1e000351002c654500304101c446801c000c03c0f141074548208090000d8410100000b801c4150810200c451080301691056601d0410300070543c001c900034040d03035410030300c1403450300300d45c011003008484c07401005030303929100b5111414195840754101003030090b000260340c2c9445c00540650700c01008141c403454030f4070b45182c9506032039020300c00ca2801003103019001400c00d000e090301614041d1040605483d24910b40c1299940d540300b041c4101c50003801040801d490550043c40390b14210340070307030040c1a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249980143 1250 249978893 249978907
    0x3050f160b1302090420031609050606070f06050613050f06040606020d12090807080316020c0a050604060e010908010e0c0f0603011a130801051003140708070b0903010b09070509090112030203 84
    0x94030008811103e1568010401b908031890b5030411500454003800d001920768030341445154420380b81c1c02003030036000328400c2003000c000a2140a1545000307170450400145600ca000000b943c8100301050221400d00304000e12003800034141d0814041c5000f01c808002803551480f0680c0c562010061040118004900c200800d0040380c000d11605403041d41594641202aa9031129640050713800c1c80f00c10301d815041141c4160100000c505403081110403000e098031f001c000440034850f80c0169020026001500c400c00c7c0d01800c0b2200c0a010380b00000e2007844043c403002695203841e0f6151a11513180d02421215505005c0c0c1141d043e074042340f500890000d01c152090f002d41d03001260f010f03001003010304e00188410b000e1003498018507000d135090340200c2c80c41c1081603c03c04041151030090700301d4030701003002c03080005030181181c001034200c90f210054440043d0040200000340c0e45c200110030104280d00f0b030f0080c010040e080c8100d4540d407250340c0300c81d09c5001c0d4250b00c440003005640100200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249981393 1250 249980143 249980153
    0x100f1401060e06071115030115091a090102191101180e070c0f0b010f0f0e0907050418020d060203071413180e0a0c0302031c1b03050f160b13020904 65
    0x2044c0c1140541c0d01091000b40a130045056002c2895a00380d1080d0080010f001d0891907070070703200800080e890809001402c1c1000f100c601c02d000a00d40300700440000310803655034004e01c00c020b061002050b8444034820b16040103100312413018200d900246190505081c42c00d41003000c4c2045e500065a812116038854100391450048220182d80358507045105d800020f800b06440340c01790406010704e85169103003260400007110360f03800c2131100720b11400030440304090000e6030000311607013207402003104a490700a01d070b00c0f030a24502c080c2d041941a1000300a0040310340045006001d03994130f15542d0b000c9199044014024810b0460108500d20750130481d84104c20b04503a0700d40d03424078000a4414500c1e20140c5440c00141d011a2036010906c804c005600c0c0c240401c00617500c3c1207c00000b0754048010050020a6003d84600001814010b1406161003041910342482c0a4420703aa5140600a10148180210342e012600100b884000582400711804441c1c403841c0d0140441074162219920 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249982643 1250 249981393 249981397
    0x2071106030c0f041202040606030b0618130c020f0c0d02010807030504060b0a03050c181e1b0a05030a0e010924090c14030105060f01090e0c040503100f1401060e06 72
    0x120702c0c2d50b1801800b400803a006064000e000400c149a0400c170344c002140705002c1a110280e20580c00e251034240111029103e500442d600b80d07480d003942e500d0b840b02c8180001c5003d000103a2000903545803a402000c11900050705029140c1c0c1681101c05010860041010f01e941c0401e000303001401880c0810000c078000e400c560b401030b1007a40c001c0380c2c40a900c004205014661361042c1e41640c8519001120f9040c80440760241480141801040e0f10f007040c02044a01d0110b81034109a000c483d0008101142500507a0103044804190070303600c05014134000c2c1660400d64030b00354514030788141c2500301001441a1041c541d032041100c2013020309070310040464641c1480d00c10815484400e0280055490790034640607101030810941e0f40811403041c1421507030003c088502608103082140703016070b001801c0100b2607603c80100e138000e0340e51440d09440b50199038002ea426201c0c0b120000240d040e50341003824603441d130b40c000300841d40088509070510642840355402042c090044802a4148400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249983893 1250 249982643 249982651
    0xd0b012007061d030a03080103030f0c020f0d15050a0b03100204081203061f27120b070516030504170105100603020d020c0703060f0c08010602030a0e2107060807030207110603 77
    0x50310160f603060300703001c00d041060004048001480d14401401019000f0480c1c0c91841c2c658640764848030303074940c08503105881035035555205560207010001040100224104111120b002c01e01071403e04141d004e02a011a00c2040c0c030a015156007072500e03c2c4a0302c20380c1d00302e0b000031000f015110140145001d069201a1180b80c000f108000201d8103845613110607148480a59220b40702024440c00604e0130b43d12200015690b1044581d007008200c0000010140f180e400c4414080c107034039552402d4802d8403d03100c142d8424a0a0116030051503000400307041100d041030312045050360342d101800d003200e004603980b084078425000e00344819031290340a0f001d03c10307190200510b0030041300c03506407a2200503481240e60540b03441001ea0141001c0c01540c0b1000c80d0350400740f03d154104070019440b409001040410130102d00c00400f15075aa1030307551040d500d44d407542503c000b070b940e040a6841c0c0855020b007001007500d0001040d1314500c2842100c01560304086510303044030100701040380581c0090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249985143 1250 249983893 249983927
    0x8091203033303060709061d03030306042a050309100204031a040312022a1903030905160e04050c01090b1b03040b03090f070b2811030d0b01200706 65
    0x350b449216460801805000780c08a0f141c01a90b80c3c600340004000720401829180e0844059000040c0e80e00c0000550b074008004480206849580070307496540c051410b4204080d10440200d8004105d411000841c022210301055074601441090750070706030310451200511039440303c400104100c4c03c1800b15074206110f413500c209100942401c0409a03004185200d000b031010030440e0300c010440401c0c801029942101601280e8868104103054401d004c80250905880c0c442031400c216050280010b81d0746480960300c0740a4542c0f5100c0c0e100c0c54100c074120342922030401c600e9115070062108400301c1c1c2c0484161072910401600c1215084072110080d40103100034000030500d100013270702461140310a80000c1c4159400c20103100d01d002025400020140001c00829101060701030082c22200d40100400006200d1000129920060241066090b000c041070755500000142c000407036040c400d80e5460101111301e18950151240c00c031120a260348254400c00405000f29488481c0d0b182030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249986393 1250 249985143 249985231
    0x1505041a0114030c0915060c152403010905120903030c0a030507121b061d060a0e0c040b03030702010c0f12081b0310060e19030809120303 61
    0x306280c040c1a400707030801e90498100b404000c1890804001400302d480c421116040e0a0400c003030402150300c01070b04064000c0000090859280d0010042080003c034050440009454180c0c428981a05941c007060b500b00080041c64002d072805010342042140c01c08040c0c02e03d242040210085540304441064042c08244030f00c118822043c44180d050328060348840384c0d524004d1038218900c00000c200c200a000144804c0701d501c104400c1e030144070b99400f072800250610f40f81e5030340303d06460304200c01c10307a4880c4000304454948550421031100780e000c0202d80814603003504000a0700d803906141d6405034001d202d8400550310402d40e402000d8020150524080e4198a403446240a507003401c1c0d02060702c500034084a0342d024560700841c261403100460550030007805a106100c503a102e0642042680f4081701520340d6400701d84081100e4881181140560b41e20300a0010b8011050300d034882c5034041c2c03400380d01820100c1224030980c0c084c0d040f098a5901858010b82c0140d00c041819000030741 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249987643 1250 249986393 249986423
    0xf1c09050a14010206060102071508100806090d0f0201090f080f0c033601051606060906180501050f01170c0d0f05100b1903110705070f03030e01080103150504 70
    0x303501d01d070760050300880c06001d00c40391481001a245c08009050281158040c100401600703415203c0e180d5800c400b4039010f1080d48031b45650b100601d5654100c02d0342ca008540c240b0044120010b00c034002512640c58a0000004c151003d90032105100400352820703981254207400540380c40010110301c0e0350450b145040c07200ca065094655003096040032141d0030f1481040d10b641c0c6813940074190810b41944210245100500000c0441c015810208422680d80ca450800c00001d500a04080c1541c40410020345917503105034954195000600e1382024503040012a4608201c0400800e203034042c3c5940b0340352071101c032801012403001003030744100c1ea4090020780c1084403103004d2242001160040441c0c01e04142000c0c203041d071010380c0900e012030320410814604170613040f400d07900c0b41580e09002aa1080840c101c2c2c071288074281e40100b141c05510300c01f00e100b00034060310b48280d0b4040d80d982a0404031640056610040a0001038080d0310010000d800260468010302d03441446490b0114600c0a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249988893 1250 249987643 249987649
    0x912040806100504150b0a1e090501180e0601110a02030105150306060307150f0e060409020403140a0c1401050909010b040626060f0d0803100e090f1c0905 68
    0x580c11185164000c242409049210300140901405040300c04000d40680d038180c1140480341d6100e015440e80001c14003c0c941d40c0507061400c26070f800c0310610700c41da011081b40100040702500070540460990b800c004103081401001d601515480943e080d1591100d40055800d420070903c2102a403045c80554801030f1800c0c0500c500a840c10003611f00400e01a104050078080f004104500a41c001d010030890710300505032401a00a031810f002c0740c400040d03c0111001d406280c407658100d00002400140a86554004c2084900a007001c00040c503070400701d0340c0c032084242005400c40c066071504ac0300080807000c2c2c42d207044034141442c61170305103004080b6280103801d03441416440c030003060802c035464005081c58541140200103c40b980d10106030110000000b4003040e0182155640002c05a180d038110300d00c40507003041000c0d4591502000070149202140500448003100341c0100303905900010303000003821388640207001c10000141449105100c170f140840300300031003001c001641343c0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249990143 1250 249988893 249988897
    0x105210a15060302043e070501230603070605041a04050907020c19050105190c05060c04080d1e081005041a0315010b040b0904090210270b0f030912 65
    0xc801d2600420a20724500400c03088031100c1410350341c0040c034000f0318240e80c02c0710030403174840c1d240c9240c6421060907044040035980c010aa0700030625071810b0703103c030204122001c01c054440ba40b0f0260f002c0c5699001c06154031081680300d48404140d05010030721180f12424586c48000411000c85401c05070341c0c100040042105603940381c09078128542040c06800c20000d080012498071852018a5140100003420b078820110503114024000340710000880c4504030409129401c0f008580d203500388a04941116485440380c88128810f0444c03030400d45000b80e1040d002e102001c0c08080d0441c4010000b560b025500411614a4404601c00441d25a8480c8948015a0f41550b01c007459000d5034130505141000010303a64100841000c010071180d10208100c03400c0c1c07003038541095101c08620002ca4081e1018840c0294020014007110740c5082d4401c00054004084200030300c000c4501c10301801e641c000f1400703190300320481040341c0241038101600864009480d6421640d0b144038044442c0c40d60707 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249991393 1250 249990143 249990173
    0x10201140c0304050f0118020d020a09060611060f010b030c070609020a09140a0b0328020901030b04060c0e10200a03020102040e2d0a0f0e010b01170105210a 69
    0x1440c1c000c414001071100400c0840d800d004c50340001c001c140907840c20924801d200150003072003030b01c0300c0208130119215519038200500f0008802d00c034994807054080c01c1141c0200c0402c80c103200f908d00050508a0001c100c5041382d031301c0c2802ca840c544a40b0801c03542507102000079240e6940342d07181000140c039100440401401c0301c580020301001c1803510b10030708440c0907140808484c00c203941118107540106042640400180700c1140c000311861300100d400300500d00c041d52105800000105001150240510a40c450501002030300000c4205032602c4071403241240c2c2084071602420940e60088101c03400c640e001101003605075990440480ca842c0c9525411070050f5000300b41007001d1100004e001740c11003886a0010001c1c226254200c1d0f4002d00700d1030411100b80007038045200e111306a401600e131100c0000c010300c00d940c3c0102095020341030300544940026950b180204100601349040c1e810380f01c00a003501500540601484140c4001101c046000d00440c0c1855001030f0186141c1908 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249992643 1250 249991393 249991411
    0x6040e1c0305071214010e070210090f1a041709010504050d050714220c030b120a0302070911030c09041113051311030610090b12041b051e01020114 65
    0x1031480c21620081061011201920515042031041e892003481c04d80c5186c15100b0311401c000c01c540e075001041703240c5460700e0409070645150400300818401205480b03440c1c43e0203042c0303200098035140d028103400d030030864000d07040d4440c6941441307403a900c00f0300402c64600149015401c007522800091101850101e0440e417a40c450310041214500d1150242c402d8401141c2410301411140c806150000b43d90041c2074106940300c8248000c14004e0b8080070317001402074007103840c0302214200c4543c0e801c6076130420b0300503105520001483d01c10a0050b05040003400f80c3d02c504544640880c080d031500403600c41d0f40d1058440381000c81141008010348401c84c1241c008108551500046c82212005141c9078080c03903081003450f80460450b001101d40200c01070300e4000c424007a00c5000c50f0320311926044100b1505001804003c800045080d07a4001c80c000c0c001e0050715031422084039000c80d0340e441055000b1040d0803a2890103044801c055505060600011950410440c2c001350320040846071146 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249993893 1250 249992643 249992651
    0x20c030a051308190b070903121d031c0c051009050307030305160c2a060e040b040b030a0206130e07110c090601090b0d230103021302090906040e1c03 66
    0x28060b8030180d00600102a140c001e4510f21902404c0381c0c0d03144440d4000545100181008161100d210300c02c80030003503070096901d40e920078803004001e1032209510f140340141000c2060612052502042180e101415152a0203640e650007200369142c880c008000c1c2c07168081c21001d070704210000e00071404000c0c8110003541c2da034150f51401800301d078400307004003400100e0807159041c415080069881d14030381003040842401c90481d0228070b000511462081404035042c0000b075016001907405403034038012241804035007092010b0000311000310400d2076250707001102c2840035051002c0104650920030800800c1981c0b541c0e0920750081c410340c0c44030001001e04c1d07002000c07080c091020102010b41192111410f09114000802e03030320150084c20071420001541741c002c0e00c0d6a500c802051503e40c00103003040da001c010300d2483c0200034882a4041d10803a414916846c003a8804c980f100040200740f007450741c0f071301d1007404014180d009015142c0d200351a200048100c005c88500003c1440b0b6a02107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249995143 1250 249993893 249993907
    0xa03090b0c030f040f080712020c0a0e0c070b090f03040b09151e0d020702030a14060105121002181909060906030213050601020313060507021009060e0d06020c030a05 73
    0x1450148010300301e204034001842805407030707461103d809400640000f51250101c02d50b042c007110070300c10024003c02e440a8810714480c525008103010410020890700d10048940c3d501144425003021190146c60750001c201000c006501855070307039041003841007142c00716415070300240e01d035500640004501d880c0c013103000005407901500d040c101103101000d0318101001c0012950710b116000d6408060300c0e20200d444401105c1a0f81a00c0100790001d085842001540c20305100c3c01880178220307140790055400100d61030400ca110003a140b51200010504510f0303001d00d9100940284165803294040c0c440019010740e1303807000c00c00e020780d400761000400500d4803d20038112110351740061442ca08044c0c6c2000581d071080084008012527160101d9195a0440101d00f54403512404012100c2c04140103d002c0e68024050b201c942d10035105000c00c2020a6419074103e01c26100da0000151100c225282e6420310301c40b0b400d0054410a005420300000f130315118116003003152100c002440c041440303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249996393 1250 249995143 249995153
    0xc060801030b06010c050d08040809150c1902030307111f0302030601030e0c030a06020d0209090c040303030e01052e030501020f180d111c0b0f07030e06060901050d0302030f0a0309 79
    0x403c0e0000c909080c030f8850201980e59641d200e80e0501c45a000380b0400c500040d0a00ca0200200c03002103034010006021054020070a218503080810f0031249803140c03c5113500c90000001c02c0c0603580760001c000b981400701c1d40c0d54032014440c0c101840e50b0040e000d46c90200c140044070020802d112400d0301e002da100d20b41400010308903919285003142c2e40d40141007050303042c0c601050b01151580c0107080561788090003204040684500035215402c841e95500b040b01302e106810203001581d100356003c0c4000b43c5008801802c1c4d45081c3c8141440c50750040e041e0800c60140308506602c1121f50301d44000d82a62a11554220f8004180300d4080b040006522401c25452050f2140707003050480d40400c2d07410345c2d40c80385810a11490080740c000d0301d20f400991005000c00441c4855160b128410701103500d01403101c19808641540c0207004641010101c0b90001c40c0440e601e48a00009000008160b1038103040201c0c0445404040d015401700700242e030748280a800090000042c0e03070710041a4a1450302d41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249997643 1250 249996393 249996413
    0x3020c01080f0123030304090608061f180e07080c010f03051902090a090e030d0506060a02060f0a150803120c0c031e0c010c110c03070e220c06080103 66
    0x14604000000003002a41660381c0001410f46070000c113030802e45a019800f030700040c140d14401c6035040c8804500001e1800540e000481075414140545040c1d032510119540c0741402c1040130300024160050a004d52203001041022a03129120003088030360840304020304101c016081840590400c0b0701017183c6517000f6040b8203c04200e03143c20040340c42d21240206107240c00200011510384c00251014680d070b200e11441d00030713000c400000c000c0c03244c080090a075203911810800408a0400002600c40e2800c60700b501c01d950f00a0300a0612540c602800c2c610a5000400038800307555a140740e4250106c1c03103611500600b4040d001582c1d5980f01032140b115100000341801c3c0454410049040034600200540300c030140454482d80c034104807042c28a03418001c02480f82419840d0003104000c46500001c0e004d6414405419608143c40c1c40c07043c076031501054010729058201146c00310704100803440859201c110000310b40c2801035203980c3d607030201107103d503c0b110006034050018804e000c07107510 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249998893 1250 249997643 249997663
    0x3080d1d0307020603060d02060c030c010507030515030c0114190c05061003020a1a0421110102060c07291801050601021b060703020c03100207140c0d26030f040302 72
    0x20360030042c2550028400d440010700c91070003618115082021900c03140d040e03403088010341c0305594541044135241402080200c6144000034140004038548800306445000c0031580136020b000f8120702d03d401510329089011400f02c0403a403c1041c4120005001c46401040415035106103116584d42001d0746000c0f0054800601b01c201400100010394404108a04803003d5084070501d068a9054041084c00303203611070b0103c00101003034a03001c00f410030182c50203540314107030410703000301400f00483c3e40e0101107a4a0400303030800c110742400303e1054824071201e440c0001d9800c2034480c0000c46401d1241003582e00460219420141c1300c8030032000e01506900072801c3c402040c038609429241041c56040c0c000e1a801000005091024580300344254101c600d409030448003140798125108000f98841802a039170507105d07001556410801143c1d000303120b540208206003450458a46150544c154000c40c403020500041c81614000d008016511a00100304200e64503d800d0a001e8105035400c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 250000000 1107 249998893 249998951
    0x303070f1b030b190c0e06090409060204080c01140a0207030206030604090b011401091d39090f030a03081807050316030302160311090a020403080d 65
    0x440e00f01c1d00607500b03c4002101c14010400160845000003600300c0060078170440d401c1c031840c25001a1582120007440010540c0d030a9640d072049030303c00d41c0321516075004545034848035a006032030081c22001a5491900e06001c48100039202e43d01400020311504001c404280c3d19280d40e841129101e51002d01d0400a585660750f505003140079440326400138821010108030014003480c44410114005c120307032104d441c4c5a203485a810080b50b01c801e91003c4c00c8001d14184200e00c2030301d22025140c3c2081d0b036a541111001c0c000001201c00307216010707600034003121000079803009d000741c1e20014a8a4082c0d00c00e810031882030411260350301142d450300ca00c041044215400c141c1c070f6012244640c0131200050f075203004080030400148006040240b0b0f80c0190314180c00d1108071745a114840e048014a05038982e66426459004116200c042d035a43d030007015580600000c001c1e030184118 = true := by decide +kernel

theorem cover : BRFrame.Cov 249820143 250000000 := by
  have h0 := BRFrame.cov_init 249820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 249820143 ≤ n) (h2 : n < 250000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
