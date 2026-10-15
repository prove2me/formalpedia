-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4672
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:21:41.933116+00:00
-- url     : https://prove2.me/submissions/a1afe1de-11a4-4a70-a25c-07c2d2bde204

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 840107913 ≤ n < 840287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 840109163 1250 840107913 840107923
    0x4121404050f121c050a030b0105070f12120e010e0d0503010806012706031a060a0b040608040602040305190b01090c0c020f120d2001060f030f110607060e010509 71
    0x14042d0700034008107610b0301c242421055140080506020b03202042c24203940d50030242c3c2d0f00b1a80c140050700c04198100c0c4550140305a651424003400c00c0ea04150403950346080d0100440320041504040f4541e1280c07aa009211040000c0d0105004dc05400701603804c8500030f28008920b9251441240c00d902984ae000b482224142c2d0360310b4000c1c00386a828001c140384008000c06a245150110545101680c00b40384a6500610700c0758810074008210048039030300b05140a00381d18441c20f503260042102d440b94008030780480c0c2440c2016009655141003410090181ea8009442800344a0310022158441550411032a02c2005500020790320b0308402c038110f4407800b22000104240c400101d025142c6484614051403004040b81380860403080c40904021040c04500003240840000d124104502950300d07180c00c44400080185516181d60186804468071000d00018156802001401401403c46041d0350010b05031039079680151611400030140b00c0920051546040080b482d1030f1000b040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 840110413 1250 840109163 840109169
    0x3052a0d05070e040c091416030e0601120507090e070f0f03201c0b07110c0d020603040309090c0f11010203150111071d040b182e0504121404 62
    0x282a0300e8180f01c010009a01c0240003030790310025000000034100d0140c014280c600020b010000d400303082a00e03c909101030210120414981002001c1000040010710317181190b102040034011803a01c1d0510904001c0d90f5080503414500344098031218050004600084605031080f40d1021039807002c00c800c422040f8040200003034a40409882c8001d5641c85c0e08a43c102c0041c8000f42e4130303c4141000d500118424012249420503d0030810429040f0030401451101342001d0500e000301c900000340e4a102d80030009110391008404030b010f140c0320301d5240c0d01900040c032003084042020a0080d100707504000d0038500040c0a00a460000721040c020303240124420906010302002130001503403c00c088401050440c800ca100005010040b40500d00344017401342110b00e4142441c0c104441000001091580d51b4450807191620191000841c0100e10607500c6400c048a030721000c140440765070750001c0311101c504100c244010700007240c45026082000d5142e8558856029a00301c8450080d44 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 840111663 1250 840110413 840110423
    0xd0609020f19180b030313140d0b0f0c070203030c071404110d0504050c04060902041403060c070b071b03110d0e03100209040f1503050606032d010603052a0d 69
    0x882d00300f0a4426142c2c1e840e024281c420008160203003000042840c5410120355140b039804134000810020324010305620903020b0640304050513009a45410b030700864081d200520035250400040c10110440003a0b904050b8010300307482d0348041c11800f86a40c1d40e00c6000c1d460002110000c10505860540305d80a040305203074190504201c000c070300b0352004140003803081c0e031940104021200340b82d9580c030464001e008044401030b1941c1c10701e1100d4540d0301d00c502e103183c02a4804420b020356164020141c8001652140c510960303507595100884000146444090015614040810806401100b40b080f4402580200da07041c90303c00c5000c030307004060040e419801d0341065110010b0b00c07003035400800318658003500c049000041c0b40c0502c8215552320024082c0c0311400c2000340108802407040039007001049000740760310540c100304000b07482e0400b040568401c2c110405400021000c0d00240c009641000544007109080326a00f01010b500e40d10282072060041d001c010f44e03140c0407419400355500b00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 840112913 1250 840111663 840111709
    0x212070f06051317120a0c09031203060905010902042102091305070810090302070605030c0306010302071e0819021501030308221a09060609040b070c020d0609020f 72
    0x352503840061001800e01652083d100700c018000c55504014000002090759001d81d45100700d8440c902c1c007490182c111844241481e03c05004e03140e0148102040e603070405005203105c02c11940030307002005a0340c02017003624105000018405e4650307014000b20360045180384c41c44c0400d881145609034200200940c840140300100d0301e074440ca00d4044541f02e20400407207665541702c0c0c1c0c4061a0407850700c81c408501b61030314550400c0550500012008011600b000d5066040c010b5002c81c0e00e02004101c03030304140d404507040b0140600e02e00e41c41a8881c040da20110f85030720340e0501d50859800211603010f0001f0700a0060345903840042c2c2000820003012072600c0590071a5003c0350a140c000c0c00d82988002c040c4c41083c01e1020f03d4040320680da01c640f07031441c0410310340104003400a900070301d00310880e0408010041c0a440e4031002942c0f2941c8400c0502035a581c1030001d0310f0201c280180030790801c104401240c10407569a10114010b40210f9109011190000c100b14022146c0f0034a0840020310f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 840114163 1250 840112913 840112943
    0x207150e090a200d2408030406030b01050409050702060a1107151503020a0b030106021b0306060d05010f061d0a021c2c060711010c2724021207 63
    0x21035032003d038000d080c4158540445960310000b48650700728a24481c2c0966407a01841c4020820300c60340e4800404e44120602c55510b44044a500c0e405207102d82c0040c95112226940c1c1d42c1c1c404c0085801400c907460ac10065803c1c0301c8402551600e0403503041c5002e5207800402d111041d01d141c2075803041e07640328500c03036140c005480442025054031820110341c500d40707041c0480140da4240d4000050440700c403c4c10f840350300d0f10034001c2c070b0460b80c03441c0c00140300f2440c040f1103c244c4020070007580c800d10035501001c2c200854030301035005010101002050621b00000842c40001c140398904c0c00f2626104002d041d0f46454000c40d04911a2515280c02c2044000100c00c0b03e40c40c0360002c0240d00d8610285000020040c01e8100e8040c10504401640380c10541c1003146054015803816070558148000b045a0040850007034400100e48410400c0c903000c1d17900d071030b010241e0b40a100002e000034aa813829404180c070240861103014410a8000d40540343c3c440040c03040303100617203110940101880c000d4600c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 840115413 1250 840114163 840114181
    0x1b041514190e061e07030822030503100f09020403050c03031201030b1e010e04050f0c0609040f110409092109030605090a1205031501090e01030618120207150e09 71
    0x70300294203812440a010700c0e069200090b80312602d60010b007110981d6020317589001011804000d080c0d6405000c50504181100300300c241d5800760640c0350505542d2500d44466850244030103500c10705a03540c05040c08600492640c0281c01100d1084003191800800c0208058a9005850422110010364001040130503000400070b0340085081820001901c05000a150016004d800c4114590840130074402000810882d1801d07181030400980010491240020310320b114150040d8460380d143e00380b0007840318040c1c1c04881840700c403c00c600c0d500e6561319115000380890f400143c9222200713510035003c044400781c09400003d129070b5010140ca05541d1076900800c80548001a01e209181c5080005540c1c1c1034440080702c081d4940707a842c0d28104003015005820800c039135040040180c0204040703000720550f0b40c1503a9010b40081070714810055070040413414080040d203c004c00303c4610f03a0342074001c1606420784010b8201e251000081003010b88440c2402d901640e00580b6030000100958 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 840116663 1250 840115413 840115427
    0xc02250b030c160503030916051807030b0102100504050607140310090c0e042f0f0304020d02040b06030a0c0f0903080912191b05090606121b04151419 66
    0x680d0100300d003d1480551200d80c9550004c40c0c0180d043d40c0061400140700400040b40d0b4000e0030200c9080d500a034203074113401c0602e08013811003405d041d107540d1440060ba0092040c1000d204103520704101514240c200381d952044142c0c3c45601180303089600c00b045441c040c003101c0c810010328444031801440c01045070000c04d0107140410401c6405552482582e8483c050b44460a000d0760810f4560115040200b01e021411104400b00203010059006a5001c6000b40d0ba401601155245600b00e050300205014143c281c41d003e601c6075001040000c554159480800466090751f40c000341c54800c110f098902d0b40c4a40400b5000050a114003481c1d031400061440340300c910307002501c85038082000309034403214840000700c440e1040354042e160884414074205004260448215030181005000300b40a84115644007541c0c2503a080020103084254011080002030001c0b143d075203e0ba19a11251800c0140c0d0b000c1e030000750b074080a21401054030050f05c000d0f01648c0040304000d0007511090b031b400c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 840117913 1250 840116663 840116677
    0x71218030308040203010f02030108030306040c020c1825051c060609030807060e030f040302040b061e0a0e0d11091602030316090504090803090601090908030f04060b040c02250b030c 80
    0x366490b004441f40595841c00694000d0100c5001903842e401c00034108010f0300d41c044450400c551000b070300381945a6600c0315242e0400140413501072183c075261085460160550280000010061860f40c1c0a03507000c0010711041d038107401040c08480d880035040007a1100b0b0b01c940000616654010f02c0441c5e1507800800505228000000e0815040c40410b030860308401ca030700780b0342440400d041040d0b00701800b0f00e001e0341c030048030700d40d29100344110340300b010500d0410320240d80d0401080303044040d40100300100d4100340c014500c5034001100d181040c09540c20b035140e103004620900c04207890481812050440e10314640103141140d031410498140600c0c0400410100b03c890200059a80c40d03e10940c80c405000e4021a581c91520032801c514294043c2d2106084910f8940c24101007641e02d000d80b900045480f103240882d032202d0428201a1202090043c0d20a107020200d444541d000141401c0780340d0800e8061240e42105031410310b03035a19270310400924410400014040c0f01c0010028944 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 840119163 1250 840117913 840117919
    0x503040312180c06030c08160c020a120b10050405090d0f030b090406050403020606220207080d0e0d03181104150f0603020d060b0406021005070e13020712180303080402 74
    0x1e103280c6181030050100c034614056900c840c1c083c03030601105a043c0100203185099007000101800c20001076840c1030b00c9440000204814003018204542da09180c0d84000c10003440107140c201020b0a0242007000b0544004040c41c040c1c100000350780c00c040c0a12841812220098070f045e0040007410303607401a4603410314080540d284042c00c2d40b580c03070000d06070145002e2040041c0d01d180510b4040c2c03825002030500c82c403400c2c240c0710b801c3c02020790441c010f8000f00207040c05611002ea500e423480e40b90040280c02001a03040c540c410b805000300007100c3d1181d002c5070340c060045114400081c2000b109011000e80703030751003007011140302d410b0903000043c6055180706030301c8605950f884995076020058000200294002a01516603011030090001500d15942518641480d01c0006941ca000441c020011151204006402140580c28006c0c40080140903200c41d2101280c111000798040c100490301c580b410140c103c1c3c0303079114230070007e48081c00c001412040303821524190b403054001041203034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 840120413 1250 840119163 840119171
    0x1806120201080a0f0e0a03020109020a050102010506060a050c100603031d0402390123011401080a1d120409110c07060815061615091104230916080c010503040312 71
    0x120100c04000146d90b0500035400010302030724034410040c494185602c841d04580c10102441042d039141c0044038080051800d2541e03448051a0415040400d09454001c01e07070f00e07080d800014180c0104000742031002098011581c0403460f01040100d024203107000100c41078440c0803c1901d4000300e500b815100690b4803c0079032041e1044141d00f580e0300703004006140140e4007201400480707070094460261503020700c0d4100e038011900000b0b0850900508140d030144e2203a012681d40511140540d20f51043d00c0145d40c901d0048000758903480c0d01501c2450030b15850000b440b02544500001c0c2e070250700f80180507002c1c1e9454140f045400303450241c00c0350502641189102d50507525540106030b02078252a40040410320341c242001d02c1807544100050703035410480c0c40000074004900c08065a0421100042c0d4102c0c03400b40101c007842c10705201300082c11650140300d03c004000030170190584440030900c090030b4560404c541c90344803280c025030215105002041c00a40900209503504c01d45180c001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 840121663 1250 840120413 840120431
    0xe1f0e011515120f02190309050d030207021c03051801090b0d0b220b21100c02100203040b06090115020601031709030604030e10020d0207030807060908041806120201080a0f 76
    0x1004440c91107020130001d681c0040c82c6040080c600e01003042851301424104886071541e240e064a40303203914503103000c269000030070008566491620301141d0111082540610240389400b5009503c0081c1025440c0d5001466008540c49080100251044c104419062005500222001c2c141c1c1008545d4081b00c81030088103003101c80d840d507600c9550f030350034080740b00704c00141402220145115500340e02141905002805000090080d21800c03038203600242520030360008a044c030000141341224140000701f408113104006c132400b170148200f00e81240c20703a6a65548a030186203000d088801507040382004202080302030035400000d50001855618121600000031f05154007141c0440104000c489280c01a0504241440c2c8104481c0010100c504056802079541e440f94030009207265400a6541c2c100482c542110084517071202e4196181c50300c81a17504084c0550400d0042040c1c9070100008011540c0c0c000d800c521078040c0c481006036156072a0000c00340280300c01800140341c03183d80e64 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 840122913 1250 840121663 840121697
    0x30f15020418090215090d1103030903030d0b2e08061c080c07140a03110310020c07150f0e0609210c09060904080a120e1f0e011515 58
    0x480900070b0354000400807038a2040082ca440001c460381031140d0144a420b64540320b112210381c6854001000644440095002908c0e512440903400c2d0580408a181c0001e444150008643e15900719003109424089050b40818940d11403e8407107804903075503044001602401c51650441c030080c00341900d0b404d880c0d4a100c40c1d200c9105044031030023000218107a071440184280f8003d001555001000346405100040120300a4040504248540e1405070324558041006010700203d016041d504c822200b010540c95041034429051001c43c20040d00e00f589110341442c62984440d900c48944154004041c0318180e0004842160040c0102d00c00850301184039000741d0104140e200104400c400000901c42820000340c0101e0040403d0428040043c04007004c1c0d034100101c603e8500c080380b49451440c4050085405586a9070103514a508001c41d109042050303214044c82040c4038080c5041041c81c00c80b05138456003040e104100c2401d018540d0382900010000603a8503100104126003040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 840124163 1250 840122913 840122939
    0xc07030f20030708100f090f050f0f03030408161401050127020c060a0203070c0c09090b0c130b0a02011104230312030402220e0a06050a06030f150204 66
    0x81030320454410349460141c403100c459120a07900058014060503480c2461007035503521500502e10f150358036580b051001086030390003004c1064015040c41c1540c00b007402d001d501d070a00c039000c4c140e8500500540e007000d11800003c4a006075801000b60380780441c0c2003451064034036260011104446181400c15041509020340c5000c0d000c3c0c0803c107c448040703009845801410300d0112810340d030041c07060680c0c2c00c030302003081c40d0301c20f002100141ea603a40301340c0c08990540e410480140303880000d10b8041040c08460348540810303441401c582d0901c1d05c0301e00c808003007400f900c00c102d0240a072460043c031103c1121405405409014000401c52400000c496009908140c010b04485071064081c0a00d5088900828032510025801b5004840d00b02410600700c2c07200501c040d0190090082c0210700c03850001001c3c49500d00840c1c200690311101022546030401d084056403501e04200c049070702c400c1c5620031041240da11110141d600169992030103420038000340803002c1c4a40c203010010340b01d400990 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 840125413 1250 840124163 840124193
    0xb09010e19060315080604060c05160803070e122a0a1d0106030e100c1b030e0a0f05011b05070911040e0a060b030c070c081002090915010f050c0703 65
    0x10200e0032060600c80b005003103440c2c03140d444d4082200000108214840070414541094214030045070b1041d01342010b5616104209034800204a074000350750070f1040c0c104c0514010a020303070710211a1454030082140104030358890b0901d41d000b648098075011100340b0f8055400c4015605010b81041c090300040c404180ea0744120750498000d14407080d000c21480e600e038050303c1c2c41e0070204038800254405980ea17801030038036000c516507a0890b00220900483e103140c1c1c24948504607403584c0c0154580240b00c5000441024016901c50102044010042c1c10240980d201a5910783c0f80b0f101341c989440d0048020b49040d60765008003078001c10700700c0d480e0040301a1210b10500861381d076071515440094030003000b03043c02d5105140040034040245044c00b00c0c0c0d002807003105401d0301c40c501400d00d182039a2196020340070600c41c03401c10280080b0960058020031030b046805080f150b0b10345118641004c00e00340c9582c005480511003c080302e0055014080c074110000031208081d48a42e2140d1070414603103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 840126663 1250 840125413 840125449
    0x906150302040f15120f050307060c031a01080a1112090f0d0e030706050c010e0d0e03070e151908010501080c090105030f0a1203020f18010e090f010b09010e 69
    0x2100500540c1024000c10303a84540c0c070300d802c21001403c415002d00c0351030280a501d984031002d0000d90144180d0008003841035410000b56661480145800c10040c0f448689007030220381020800e555524503010608410b09040c1c40311100c07550b41c43c0d1490b00611800410f003803d00c2c1c0070b0256000071110194100d00c80c40d1024001c060302c110318041e045c0b418007914103140400041d40c0a110300303034401240950448155041580e1280320340040c0901400c5000d01142c06407050880e1000300c1d541c010903c048a070750039000c0c0c4207076545a064000b1100c1b411a10032504079140c0d204c068507402c20813644444010401140c85201e9102d403600c03425039100b03a004d5005c80c0d0064420055070714040842500400b0110000e060072402041036948541901102510080d01000070081241c02030b0121540320f88246d041c07540c0d51034900045240300070040c40f81c0c2d00040b080040c00c140350520101c11b0b8094206950800319030381c03801d4125942680403860560401884003501541512060030101802c0140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 840127913 1250 840126663 840126701
    0xa170d2a1202062409060d050f01050714071e0f050601090504020a23040c050c011d0f210a050409050c1e0a0e06180a17060702031903050a0906 63
    0x182002458400f0103000102c40411400010001c0c0320b54562013110004265149841603036280000303403000c201b261010305603000d680d00c005440041035018500c50351168403003a150b08000d8288029501808400070120303801540c1c950761074510551640540f80c840c040205030044507503111400d00d00d0a0303000450741340e1264207100440c03504010400181c01c3d44482c0400901c08100c1e003100608940b099940959561200d1f181854810300407503400b4403545009001208040d0402c1fa0102d8618039000200c0c0035030340c2c40020001c404a5528130140140308a860003071800d001061083d40b02040c04c20078004200300000c3c19105174010584901e202040c0c85488030380144403000258151034002010220800000020681103d0b040c92031880583e00315440b8418505a4550300340c0c86661503500c282c0580f40058480301040b465140030319541c003038904945450030f0903603581c0240c0c0c0da40c00765032510709004211644650701903075008401c0a130115488490f503c81000f00e84841e5900e04118800f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 840129163 1250 840127913 840127943
    0x30c1819020703050313170f0a0305130506070503070903060507050408011406060a140d0e01020a020f0f030f0c1009050c100903020f0909030403080c03030103020a170d2a 75
    0x30302034649581140880c0d007989000c40507a401001d80c0700007404120002144030290090103101c41030201520b03480c2824a03542c1e8000004038a498204412002c002410300c40020070205981401030f04542e8401d004100d1525520810358160704018071510401c100c5200010204025000c0c00e4050f03940d686420399120b0070324458a0942d8000800300e0701410f915030a03c901500c5440403107040c9140ca191000143d6940c01c0d0705141841007400e400c0409040c18541034044034103500421103003556408603131040d02000c4003240c84a640b80c07800445600203010b6529800c1040c401051f030440e10f1410f880301d802d25484a07900f12254010300b80c1c1c0b280c0c0100c581490f1400c0135000b080079000305003800c120b51440c56001231120000041c91078040e000303034400300d18000d070700f0000e5038043d5500030481900c442c9525085940d0782c0007480113170300c60311400d200020a04029002404d1031a1440003821020310482400c0d1500b969200004400036026400c0040409004940044051003104a01e00c0011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 840130413 1250 840129163 840129181
    0x1302130c0f0f0507330e0601261506041b0c020a0f050a031119031103070b030c0702042a0503190e070311045411030c18 53
    0x14494641003c3c4141003000e8400304611812002081100c0ca50078100a982012000c008207401e12043c84042c1c18004540d110001c01b080e42810b84207085151b1100c071a81504c038000401c0542001c0d2501c0d04100c9590ae5021040f1140581c080405000450340c22410481e144180140500c042c00040311801c6079001c501e055082c03a0000d0014940e08801603082a0008aa1845510008080c80b01d8142a1b03001070326102e0300140e0b1107211150b03006025583e801c00070010301e11203144501c00e0180800c00300d10700201009072801040d80074880c0d4104481d40d4240300060114141801c0050111051000d101c805040184005a91079450f152203041c100c501e044c0810046a41218481c20f010030100741420000d0307004201c2e500844001c06d5003400c0300106005100511908140c00483c2d01c44c03100d0203c3e40e944014440030800f42001ea44131038908046a603900c0c004114500000b684000800700d040d42694811084004050721440d072003080010f460b40501c543c158425508404c20040381d21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 840131663 1250 840130413 840130427
    0x9090609121d120d08042109080706021207110307030203010203090a02040b09010602030306090415062409061b110d1110050a050f160507091e0608061302130c0f 71
    0x2402c01e0780c0e4555500f2500e825a0f8492540022650410040200090a10521803a2840280c0003942465008428500c000305000301e179014150f401d108101c030004400d80b0016141203070300e2182581c9801c1c41100d60f240c145003010f210510340d00d80700e071030404030140e50203100440c000d1140300024a6440010f01c10721003034451100c1c11078400d901c00c000410aa03a0044200c80e4800412590020b16690b10300e042d2551140390369035149403502c0d04402090b00228044041441d040d901942104403c0c003210071600d05c4428040c443c0025155142820076030800310080c491a40320b44500948450201e012a02070f103800c61003a5851202510000401d05040300c01101e0152940303001c510300fa81e228006040c510442d2203004044030300140385047d0740c030400ca0046500740e200e424ac2e1001ea50300c140c803202070f20000055001d00003c0b00391841e4441164400d003400c4424503406000141d42d2894005107416020078241d8120026000c801c5030100e80b4420304c0b05d00709035629100300310340314960001c00ca0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 840132913 1250 840131663 840131717
    0x150c0207091103090c010309080705060408040e091606050d02070203030d060f0b04140613170d02061609210c09020301030b010506090303090f0a0f092403020a0909060912 75
    0x20400070011300911100200340703881601c0c02800d000c20410024501000244981c0a000c1c01a01900e020f00003008080e200a00407580d0b042604a200c2d2031302111580c45020f40c50a808040b0b2807000e00f08040c81c05000640750549031000010f042c108250042800d582c00005040701312941c0303000500040c484c2c0b40100000c0d0032280c403d1420706041a58a810902d450980c9911a5001083d15a001e48001c0025005400200c0034404070185040c006680e404d0b41e05000000360048400150b020310384041070405054a6560360400c081c54600b4410000c01804414056826810074810102e8004100c00c4014400040010fa9170b61441c200002c0c14070040c0c20442c0314450030010401950b41c00030035030790a90400c40f90030b85e081070041f0004140414680c0103e40a004850f0700141800183c2c1c001c0242c2507246840080c03c01829038480000c940754040254489140780c4180106030305d07948030f1512a03202c0c280c00222849951a1903010580c4941c084001426418402050b603039010441c07449 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 840134163 1250 840132913 840132941
    0x603150209060a0c5a02042f0a110a080301090c030b03010c050901080f1b250b0405010f09020307090e120a03060509091b0607150c020709 61
    0x28007898600160981c464408008100080c6090510510403c40901001c0c540f420707004400c08040c00001c070003400a5210b8000520824011700e42d40da40c2c58503c96902c0c10080e1342e000707030500210350070403000f01984c8450921108082e90303082c00441d415404a01d80504115225403108125900200701c8038595141c0c07280380d04200d1610300015186400d1301e054490700303000405c0c1551100d000720000c103d41070406600d90300703203e00c001c0010f80102c010552188280d0301c60a180d036440480803081030081d10a501542150381c01100342d1103285000d0b10100980461040c002070189800d001c03600301502050b20b0341c403070401c00d000070000244a0080c030590000300c01e00410381950002901c4040e1803042240003500c65600b400040e50078031408240c1207110281d0346e01c3d600c0c907440c0200240790074095540684150b902049a00c080062507481d0707071904401d078041606080040c07111907003040004032000105030850780041c0e0241e0140c0310768040d0b10340c01001e00d613141c29524010380e2412001484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 840135413 1250 840134163 840134167
    0x1110f16080d0e0a0605090402120a0e07090905030f0723010213290903010f02070b0f0f040807230102070302010e0111041d1003020913060b0609010f080a020f0c0106031502 76
    0x9184e120a62081d003221891b05142d0384504205000c10044c0c41400b03a400c00c5410a07074104030030300b00158040c500d07003c0721008841c1019252808401111180c08004c0d00580c818400e0105288000d001824914442c0d92421501003503944009400944170445d920142d4012642c50349101e0800420b400800404102c624000c0c0d4165014074a89861441d10441c80800100000c0a4509401203102110801da01b190764820506100803864010340e0144001e003407507002f29904030720905200e0300442e0050341c080d20304121350f41d0b040c0c0c20701c05403c204007000b003142050740c0c3e03108803c0c4003401ca040c2c0241c0021a200102828080c01c55800d501c210080681c10701c014420018548443e442c2c240032007516805640b580000c0c83c09811301584000d5114004408100030400d0225084203007a200b0f1800380203c0d03480705c01304034a50184c006075500042d1003140e50f40201303100e105101e4211002c3c090062401c01120004ca5a42c0e00846c2e050090b03a45818041042003a01c41c088a001148100114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 840136663 1250 840135413 840135437
    0x31204121e030c02030405120c030106120b0c03040f0f060914071d1003022d090c0d0b1f091d0408121f0617131101110f16080d 56
    0xc104910041000201a40da03c800b61110b40200200c41c06010b00a1400c100b80b141c040c0e2203680c0385042c2c3c4480d4000d500b0300030002440c5040080d40955241c1c8020403595aa40e2100c490f8400d0700010016541d0034014203906000c40d03c40f40c1c1d0009210b00544000c5032250f40340c2045071b60700410b000c80005a0348900c4040104001d00ba00c2c1503503580086180e40d031103845200707445403c0c00b6590000781d4400300a44200c40e080d010852074088410710100c5030001d89403c4801c002c0ba12000304d4011026100400012080440359070000444603402406803581d04403416402c03030010700304034100c008910060743c103004d55042211440031001d88000824079510301a03032086a18000c54050001120051000c1025500d1401c0903401c40300004e45c0c00040290341380307001441e40520a01511a641410010540741054446070003807182e00140003540566142004542c070001440c4020014010030002e0002e044092000300744844048050800e054188060f02d400e180d600303c803003014400c6408241e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 840137913 1250 840136663 840136697
    0xc0909070801081e0a140312181b061b060901110715050612030a03020d060b1e0f070f1514010f03031404170109030233150303120412 59
    0x404c010b42000861001000302001c03501e10344001c1400061410a03d10032080c40c0040c000082e149160b1280c0160960f5129911044050b00c4c40d00c00580003608030f0005101000b084030541c0110500150503240f070141d109102000140009054200ca50040000d00c420500b0902821201580500040f41b8142c1241c0d038414103140718400c000115921103000030303860781d00c0c50400305407000c281082d00e42d100700d6034100400a5000034035903003100b071501c0004030780c03d02001c055a240384000e140440c6180008400f10526401480300303c0d41d003001c10030501c4001048440440001403258210481c00071511140324203940c00a441f9000101d43c0707100401c8a800b59000b07101c1140d41505090245061414420529124680041c000421800030a8507260415844112468006d40c2503a0502c046d4801303c40840090107880745103070324903206894562100031103007034209102d050505411006800070a055030800b900601180031003000b004240015842c034944d040361189080c00b0101842408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 840139163 1250 840137913 840137923
    0x51b1902061506030a0b03012406080708070f18050d05070f05040b101b020a03030e1008091f0e07080a1a04170a030f18051e0c0d0302070e0c090907080108 68
    0x310490345031500c6c4035408544080d0302516692841e91040740414001d01c410500c030310b244e03100c0c034800620604001462503204010950080302d2507a50094400401181242c84c151890049131640c407009a0025596980d0815006d8103440303400500b10322481c200c000f0220500039404903000303034240f180201c00356503000e00c000303030007482d50a040c5424001c80099900210650200039001560201c012040c55000740381944049821180502e5074100c25004a610781c006498100080d4445400e04600c6c2c800c021018040039680c00b00002c200c100b00d6407940c60b040300d50b0b215503ca40c1200d40c00e0001d101019680401208803100d000410f0b0034503170340703402101d900f04000f40300c803507400b1074810380c2280b194001e54034550351807001780076030011340156a09802c0c611100329820320030011914400181c40000300b00c003505d18000307010080c4599061094108100004174110700607402c0c0842c116600b1300c5d171107008008100260781c035500014103110b401503000d45600d09000d4483c004025002d00061 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 840140413 1250 840139163 840139171
    0x100602060108030a2001090b01030b04261b211308070806010308030a090c0303020f0c040902100f02160609050f0103090b0109020f16080c012706051b190206150603 72
    0xa10107405d0444502c103d0040080078801454a500d06000009206090807134074025801441581c100002c4401d00d0349481d600d612801413042d009001c0b440a45954550701c40a034001102911a1501440025640d184107482e0242000e00040384910100598107400070140994000a02c49113040c00c4500380e0750b146c1448000d00d0b6120000005943c01042d8000e40c5045034894080070344281c407440e010b07488580c0711003c44018818200139084d03904d0903004074200103030003905013a40b040c840c200440b281000c0c0740900f03095211300c4202401000c49421510018802980c03009929814001003180c0342030040c0d9070a040504082c840310100748060290380c1141d0b01000c005940e4680d050315000e460040c04515101c000c2c0c190351410501810350002c000e1000244003c00034801003400122070315004030798044001c0003c2400703400082c4c442d0311030781c0c0148000d411004100015000810b02d0340c0400049503080c0114142802d2440e010452941c0145044501599043c4d000b070200c0c01070b000c010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 840141663 1250 840140413 840140447
    0x31202030a093005161401091b0f060903030f0e13020a030203011e060507060b040605090c1308012d0902060f040f14060a1115100602060108030a 64
    0x100d91201160350000e039100340e1060700c2104004003d40c036031060689500e01040110124800b8502e0584500200c642c0d007504020240e101c680e9a44440b21001d0700c030700054400307640e5541c074880480c03001d01d03031480f10700701c1c02c03070034414480c1450603050360030506130f0010052014101e410f2000035009040310005070800d02c0d1040380c041000d4006000013660340e0894000c2480051031001c3c103030b456002981a030701c0b0441e14004800702101e0602004e401d6115580000398107005100008107140c2202441a03001800400d080b80c0303603030020b200500280c680500024001448000d484400000f6000415a0a00800c0708060789825588141d4840008030010743c50341030412b02c20800380c1d00102c60150081c0441d500c1e400e030002d281c14107070301c940950034030350210390320000d107144103c8134000d51190f0141c111424074071850021382d4441604031001880380038444280d44894000c640240c8284010f91448140320710f482d1010b403d200341a0080e9601d60070800002c05515080203d548011030b03c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 840142913 1250 840141663 840141667
    0xf03151103220b0903041e03020604030b1b04060804030e0102011a06090103091502030103200102070b28050306180c040302061e0c010b13090b0103110a0306140a0b01020a031202 78
    0x40c00540c03104074242e600200301166030424808072000c000054019628000d0481402d43c0c3c15540303544440d401e138070000f0342c40a400c0005000080c82807452940155140141240a0071143c6101400781c01a41207400012140f000b04400d00d54030440d1100f40c80f17070a0000300503000c040d1440c1d80c000300c62032400c41c0c026078002640c03603a0361340b01c0d074081101641c21405891100a8105004002e50f02c02c0c84140d84038402100c0c6614445011030201d010701d501600104103d52070000c954a594000c00e8240c8a1200d1034150991640c2501a48480007540f0ba520145e5034039007441081514042241108403a020450401001c00c500c5030869007940d03012501a62600c00c540303001112031071031000030b6000b500c01040c803a1407074005404c203040c5a0021603c81e4141c06600c50071104031fa1403100007074075100040d801000440d54520701c0c03101c9881c0103816040e040d07880780c0759001615200540391420091200400412442d00d06c02d07080d580c40700744054543d540c00340c2c0300180902d00000d1001a15980 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 840144163 1250 840142913 840142951
    0x911130509060d170c07080a03080105030f07090f0b0409030c0c090605010c14211908060f011202090d0308060a0504021215010e0a080f010b091303030b190f03151103 73
    0x10910a8984002ca17003011512000c0e241d8040381e4076034184102c203c007c104400004101450045820341c240301030040106661842d113030001015060b54254042020fa40f007800d64041d841d940180600d40b40079032581c0180d43c01c90301e4000d58520302c5601000d0b0b01c40c0381070700900c0b55a91080e2075025007504013521501d43d8101b894000d04000b0b100007000e101d40703e01a18040d01e50381c207101a0040721138940c819194040d02c1d0302c1c15508c0c1d5a040310740c20307400340301110445203540c011640c0911856480310010b080041010119181d030780140e5040c1c000c2000c500400906152803101507028042c1600c0560500002003c4043ca550024000c02c00d0f052120500b460203034860103861058602c010182d0000950740d1680a890b807110700040105035003888403e0055040400c4901d001e492601e010a4a182094804030000c0240e100e5103581704034000d0700408010140040030024108085002d40690301d14603003802204007024140301da01d800c0c03581c040070380c0702c10300c0c15030741d110f040b4031116070103030709 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 840145413 1250 840144163 840144203
    0x604120f210908120406140a11010c09180236030109080d05090a0519060615051306020601050603011701020c0105180c01020f100c05040911130509060d 67
    0x8095101114201075000c42601c215034446110000c551082095540c4002d4607440f066052140e03014540100746001009021990041e00803c1c0b1011240782c56002c45820f0800316094440c01400040011040b01d41440060b00207000e20446440d44503045141c4422500400405800040710380c10450210440e0401c41050611054400700024002c11030440340f80741680d0581c000d06e00401c6d040b480e1000047c00340b00c002401041c9580c0007401002950b00c440c0c50880c1d0300001c408100c5540c0d403155030028141d540c030081d00c1220000ca80f00d454840160070091274200c04154403d00031540003d00410440e142c0740700f03e80c1520400080c4200540310022458003903c41c1c020143c51940c41c0800300441b41d00f420000604920203181a2080e80240c24012641c42018112340d69568125004216090241c2d9111485280e02030901c5410156217010300000c650b007070070342460b103070a00003040c1291001645000380684021281d0035040d0900c20042441201e4492004000c03243c03001011200c51 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 840146663 1250 840145413 840145433
    0xc100e070e0103030807080c031b0d060e01080a12021507050a050403050a060615030c02060a090212060a0e060a0603030e04050405120c0309040f05070203071e120e0f0604120f 77
    0x12400c40ca5002d581d40d20b00107080c0d41c000c07102c00c4001001c502c003003a680301c0750701c0c00c0320300460020240c24400542c2921840a56000090011b03100f030f6150000501d50012a51903402865590043c6c41c001c94a403d04016622054180404540042d810300f4001540000d00035080081031800c2500c9002050042e245403190b130b00f014106c1c1c40f6084191040048030307085102a42d0700705102c07c00c1c4215501c0c054040e25004c0303032988050303044580001c25800312507200200c200d0000308501d0720814001c0c080390400c1e80c00c0c0c4a603607085844030070841c3d402c00e0400001c0c1d000a0045800c009840c50340c0c60003020508030002e03c602c5940c42e4008582802003c001945000080d4200c15036036103001096143d99501003100b160145003000c694035002242c0d442054031551060f0051880c1044655941110401c4240000802e580c2960301001103400c8249a03c3c014003151180b0039907486c0242040400341c04d2001c00e500c11036003000103100344a80041074503c81e0b0b905c203e4428540c00e0926205541c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 840147913 1250 840146663 840146669
    0xc0506010e0604061a1902010606090603090206122502060601050f070c050901121704122310050405010e0606031f290117040c060e040207051b030d050c100e07 70
    0xb6844111400740108000141b203400c0315408200e005022885059003038031440d1007002c2c0460004001084a540030744c010b00390700b43c07009000c1031a0080b07003c910005103000360f8948001c050f60411600c41c4600090040241a4450000f0840c1e0315001000905510852402003403440004c6044020807100e000c032003026000c0144220110f40c0c441101d5110b5444107641030f6859510b40d43d8110301c11a111084809582c0c804000b9400340307100b6121419055a03c14807007a070080d02e0002200806014000d12002d80140e410100302d17410141405401e41d8400484000c040d0090028088507960000d13944800d200ca81c00c1d680341c2011145210802400f406240d017182100c440340840000ba01103104d10f554150980350184050402c8800e4900c202c0b003110000e042005810b420300001e401030f10b22034040e203401080586032400c2507480303908000c0e50040329003045820001d000b0142c03800b0300c50141070324002d00d0914280460100c80f2551201f200c0707c41e043c0c0903500c0c1d0500203882d41c00e2043c4006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 840149163 1250 840147913 840147929
    0x6051209060f2e0e0601140306090a09150f0b0a0602010509060a1a0d08070605070804120e0402070f0b01060306090b0f0d02010221180109030206030402010f09090f090b070c0506010e060406 83
    0x84558940382013000c0041129428001303403d20f094164251900000e8a0080707501400001c181c0d81c80405640c014021700100780d891407007110400100340254000d42c86c0884a440b000700c3c625258038240070b04c000c981d80000e02564141400c000d0b88038000100d50f03900c40740f0710002090708800c02000d0620600d411001c1c0703802100c81e0500790140304610b8000c00b0483d00c03d001c02c2015036103101c0100c50110054070000c0003c036184030011080d52144d9242d08640c14001e10052900c0c81a684050101c1a40b001c215164010a07004121054051241d40e0040140307400a0013566400000110043c2c000c62409219090ac0001e020079648200010341d041c3c0c100c0d0141c0d038401d42d446040f24070560002111407039210010f0021480729441100e0100859074098001425a1070301d9005440880900425104001c10340c40d000822081501600c00300c0b0100c1440015030040c5030800403140780c0c006004600b40f00c07250034a10001280056520304640d000e10b0942400d03150704000074040d00c00da603c01c0d20 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 840150413 1250 840149163 840149251
    0xa02090a03060e060f040b070f120609090302010b041a0402030a090206160c1418070c05031902060105090906010513150e06030606041b03090503040f06051209060f 72
    0x10401905510800307070b00f120700c000c490083e0f8030401c144040050440d0b0050140a003000402c018902030341d880a480b02050800304010090001300710100c480c2030781f0011126480d45010814141c0a1017101c50842c0140e6040c07252611040503640d1039540c0d01c04240c0625800400180003d040341e02400e24194010440f90f6038201600300345800c0301c0d40083c05c0d03a0903801034400041980b0440e1050700020b2010303100c0300000a000180b2240b60f0f100030f1401c0c1c10320848512803400a10240001c010407003544400d80c2020b186010024548601600884e02501150003802100280020711038119901140c40c84800030b03402140030081c100e075000ea11031101240601003440340b2024402d9100303100c00c0d0119080355031040c0420068603200007200300000700c05041070040714481e802c50581240030700700300c80c9840d58410982d031014540f0351286000401c003207000d923000001039403490b1b040080c280003407581d0b00f019540e20040040242880c40704008a042000044d070703e000350365600350010601c0300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 840151663 1250 840150413 840150419
    0x70501110304020907020a02090c0304050a050604030210060602032502030325030f0804020f09060102070e040b01141f080403210f0e031e0f070b1023060d050a02090a 73
    0xe000380c20075101244611100d900203000c01d031001548400b150740003400f0101e180c0b40c101a240311703a8009001914a8000c01c080c07540441d00070031210380614402e500400781020b0542c681000c0761840c0c0c00440864108003c0c00c00c08056501d040c100a011500e00c00f003a081c803070720000b0311390700c50070155442c40c08200d184110310300c808a9803044a0360003610307803840c2e002c1000030460301e080c4100c03802903000c140e0a54020b4903080c0a038490b0b51100040c01114801303511071030a01e60403181202c048030b5036001d220043c4452007500b641c4140703818003035900802144e42030b030303c031402119043c2d8244200710310070b400901414030480c03680250740c884039100c982040c09c80b121701016040b00650900c50380e04004103810401d84c0002280d00c1c400480460b2507035400c8008625050347d205000303500800c0010f122100100d8000c0b41950301560310042108000e900e40320510040e520403500000d10320b50300b0f480320141d5880340d10403104141e008640019a540c1c0701c00403000240502c1c0101a000101c100d004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 840152913 1250 840151663 840151691
    0x90403020c0414240a0518160504030c030b06011b0501020309070b0408280606080d11031903050612060c07030e03010c1b0f120c151103150105070501 66
    0x40003840005550601210100070803443c40b42c0420b40d098001c82080f074070103120703200c030b020f0710803600c004020000000035580340001146000f0f5030344400044181217040c400c1c5026904d1840200046605202d4242440c42d29902141d11062101502580c80708002450983c803414a021151014680002c401c58950170040e000b50404c07034041036207110340100400e040f40c54500765003c907000003005244404200011a0420a803c0d04100d1950f0700142140b001070002e0041078003610300100100700c042000c1c00c0052070342c0080441c64150390001c201c0c10b00c1c040c40c00c0c0288024903485041c085000d80720303180420594154140e241817035004200c20b000c0546d01a0008041090003581e40350303484049902050300700e803c00300341e50000c650b90b0080f0040b040030001c0350108090103241015880207990302c80103441d0031042000400241c142045e07100b086001194000c000c0c080b220300f0000c0c03009203c0100e1051002a0a050070005140260501c1da8454011144d042d0340c8840203000310140440d00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 840154163 1250 840152913 840152923
    0x30a09080301030b011403060c09010c11121c050f1204150911040c0e180c1605030a11010c170c07050313050109080d090e060a0b030f0a180f2009040302 67
    0x9405505540f40d040d540f10b07403500041e6140205010b049d403600d0155444019103410303024400440b4071704080c841d02003881d0f882070021051a10140c1c098006801d50382d0703001104140b01c0d2660300c140101480000b10070b5180c0c006642d80b14003900c84944035070300c0790300b445842ca032100c030107942405051030101c008004a590a44c00c4d02d00c0b042d42c00380031f24444a0300c26900c1c0710001c18599003100d4040c402640e5601600c2082d80c11040e0710701024509841400f2152030350024900558941e4400591881080c0d4040d05c8045c41f580042d00030452031069150051040d0012115812101e10100c04203404809581c03c035046144e0144c1100d07501d105500410804100c6071183d50f000c20a9800c0000f1402400300748001c5d0428503a907198100ea050810103039800340e0281034035400200c41c5d00f000c2107084240c802980607042c4000e8254062516181036000e950010700203610069071200b0450001d002c3c02d0503042013030360003400704101c14000842101c204880301901c660046101091109158010603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 840155413 1250 840154163 840154169
    0x19050405031e0f0a081c061502030403021003140f040501110d15170706050a02010618090b0c09010c02012007030c030311030a0905040b01021609020c06090d14030a09080301030b01 79
    0x190f8041103000c5010540b40e896000d4041c02c1d4140c2086980164801c004451048030b0301c2d00c50005001e80c035001c900c8481c010400b82c0d10007681c4001400e005501e080c4449030448890391a0a02c4400049207045d000360070f018000c02c030328604a00100d030801c90b0030740180e43e400c07a80a502c251142c075400c0c0c50340090004c89c450030340e40c840c180c1004079000c244c183c0c0c0b07050603100c0740e40281130051030040102c2e0a5804083d10790f0031550780e040040341c82042e8a40720b01520741034500104100c100d900f468061088007500c0308600c2002002194200c1e40c110540c88140340d02402c00c400690fa40790241440361483e07082e04c8a960040003c04010800540c181c2c009803802a594040ca40c0024a003050b0b87e071164096410225045003001c200600d41358111a545100c184190742c00c2018080e11758050040c03a800003541541c000c1024101d40808014680d0310000c554000c1040c0c0c4544100a44038510030448640100700001c00a00700ca6816005281e0603644600300a6896950782842a0b8116081c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 840156663 1250 840155413 840155473
    0xf0b0a0909050c0d0302070803030a1d0d0807051b01052503021e0702011214060312030f130f1403070309060f0f0f020f06010b0d050108060103081905040503 69
    0x8201003040c00301480780e00251944035004280c50300d44202040381381c400c0ca50085003148119a404120f040080c0007544c001c02d00c40340d001c51658105002c040780701300e80b2290045581d1143c13601503451a4091180e41e002200da080c529034031303500c5811030000540070001d040d00710760a10090040e048102c0341c1070360148000140003d110541918110f00341d1082c50391440c0395500c41d28140860140140003040e0f00352050412080c40103c0c84085829280b0854032a410311042104006640c20140150002c100c13100c00058a103203130400e41c0d80f40d80100684a4820f001c20003285008105003044202840f9401880f05003480350341c1e00c100d85d44d0f0761060604034009140b52100046250051104190b000d00c1d0f6159002d105000303510441d20841d101011008520800d014123803000c6051055901030860300b1003080d901c0348a40104d4056540684c81410143e024000400110300c10805070342440c1c007250f111b0750140c410024100d0b0a03016540004d035040c02103400480903101981c22107c03610001d5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 840157913 1250 840156663 840156679
    0x3031d0d1110090f06140f06010318050a0c0501090f0e190e070305010c09050901120b0603030904390903030e0a0302090a0e0c120a0809041503080703110d1b150f0b 72
    0x100521040c50441661f521600c150420045666580280c0005909005070000d510801903140c8500d880d00304100000d4030008500f40c010302c90395901480201c064803075003201c100c01514000407241c03607041c02032020a160ba21054075001c4030101c0e400075186241c01c0821202441e4076414414003e2601d0107800000c52941d00c800522030800440041c120340c0520000c220040c00381d11100c42888005041c5941804104007201166996104400401484002e900520000c0702d15003080000c142c4500424841004801400d09500948110075640c0c18681304041c85081408103a0000c00313900001c0d841004042000940d07030031548441040f100107002c0b10030b881100810b0120f0520010a400b00680040c49040007082241c8001c10b41d0311800307400090f03002f0040f00c0f100f98070741454004960b1040c0c0054840181644040b5484a095540300a00203a0860600242c611040c000c166030316080203a11003814000415140b0481e09071051091041001f41c4110000900748000e00d11311550741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 840159163 1250 840157913 840157931
    0x30e06040f300b04020d030905131a09040b040f03090902030f0603010b0f0f01050f090d1202100b0a06081e090f010c0c0b0406020708040803120403031d0d1110090f06 73
    0x842454601150f04244241c105848a4003409102500604140c082c803020300b2002130300ba221600c07490b244140116000500c10102e68000410400158a103403240c22403401703000104903c584116003242d0700081004083d80c0c141f03000d590030102c940c00f01c01c06910100c10050502c04039601c942c40f6400c200d00801003132114004202d2105044007409030010540e000030516540100010f00304040c041100e03600b4a66400b000491080740484111818148224506a07141e010401c00d02040001541404500059404284c0c010558880c0004025030800071519103002400400c840c42082410080c0d20721b0805029541e40340d0030030081486610f80003800148503c10f407130030000140d101d40703000910b0719a43c8034000603402c40c2c90181c44200d41040300049080081004001c90001c020b5003001e903203020308001d0200c4480c41c00e0070720840c1401c102403507441e10100d41c0b0b54017100075040c42c840c40754107036050310715000100c04c86960661424011a0501800c90078031a030442c822601407103230502e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 840160413 1250 840159163 840159239
    0x10203090d080105120d030f020c06190605060301030f02011b05012c0304060206010311150304110405070e0108240d030203030a15061b0611271c030e06040f 69
    0x10700110218a5a040b407501880e0847c8290000e000b0385900c0725000d42014007604149041c90700a88041400ca104000074444c4000c46020b0517008003811180707641151315644440d81d08400c0000300a04008030344423000051803010420f0644030350000000c11100700001c0100d014280c000f10154031440c0c02c1c1040703a5100500000b102d05580182d070241c1381d0359180d0b5079440410364030300542aa00c0041e40c0b60402c9050b140350081c601c41c80c0a0207200458465540c1440219000079214008100441034bc4070000d0343c004002e9904110080d54021449038084206101c0104514100d903004e001d00c4500c40038103900101560060308402010801e004441c0d0b0500421442032166801050340c42103010003075051040742e0200c1e40d0003804040381d0054491310121003a0b0001c0c6401d1405d9903401c9600c0900314418501a461400c1030790410103114850103400070210003200e00904011091a8500c819211101900c00800e507000010840030384135500440a03d000b10300701070400010744805401c0403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 840161663 1250 840160413 840160429
    0x20f1e04120b0c0d141b13032402030c0a0206010806160810120c03150507051801050415020d0215070c060b1906030519020c10020912010203090d080105 67
    0x240121203620320014071599060882103004203401c0c0c5601003403040340ba6441e91801102a1900800d08410340e52401d040c502039903450b10460100d9161051190100207e170410311601501d410040400842443d480c18040301d043d030820b5400c05034004030500896034812005818941e05039000d5929a07070300c880c200b580d41c201c1240c03802c61204000003c101d443e405042015007009010341d80e2010309440b816944903c0180c80310403144001800e1040007440302c64040c468512030f410700c7c14840707802c02100091250161002c0e941d07210300ba484c03900c40315078040c008940040044c0e98030004540d804240c0a03403514805000d00c400350080b40c01c034900010307034090041e03c50308041d1982d2100c0b01c00d58650100030315169444c00e4004c100c80c60905c0c1003201400c4043c0c002d2800b0307075021030146041019060144040d94a85400034018498007003020404241414002c00014005886100c01800200c05141c1641c80c0c1c001540300200b403040701c1d4008106c9550001140d01e96210b641d9845060100003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 840162913 1250 840161663 840161669
    0x70e04090f08030606070f081b0313090b0a030203070f21080315150d06031101020c0a05120a080c030705011d06180f1f11120703021309020f1e04 64
    0x140300e02103141400900d08a000d1034000b08051300e46400c6c0030482d1f80b02e28002d5559a0140e070741d000b000c01d816001c03000400b0095904616031f0051410000e403600300c0440150349004120355280c68411044a9440c4d2000c0400210340080483d141306694032408211003100d80100311260583c2d81c0030003001a005449400c9455000c0551807840d40d035820220b1245078114081548408007109100d2076a00401c0500710138170714508006810740ca18940800c5180f10071107180c0c19500001c103460700382ea03904043d100889105640005455121000320307070800d0403800c0c0c018807225002c1039405c0d8465000001d40110303403188000300030404482c074030110b80f0720118044522540c060ad000803c00b4103152100d0060002038012104c000340308075010350418085074620215020b1080118448040038000c0d024021603e9900c1ea2a2905004840800700002421a010302d50000b4481841d46811600c12004003100c1d8130031900c85031855204a1503070f00c0388030b2000c1f07a0011280c0f00b103885c0d00300d10300711021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 840164163 1250 840162913 840162923
    0x6051305011403010611011806020a080105090c0403031107050a17010f050103080d09140f2a060307050a21020a02100b0604140111010c0e180405190503070c0b03070e0409 75
    0xa43c1e1070321508844d081d4586d003540020307540740c0441c401804449440180b40d54030441c000742e01e407540f49000422003c1f0503409540f184503460300303026120071944206c40650780c051400c07108814244002a1612885512080d00548072003000644602c0421440c1605842d410092250310210310f564010307034900b80005030000c6000c21003002c10344c3e110740c0042d602510820650030320001f5000031a080058010300e0440c0c0380c115402603080000642481110b504140f0001d5400d00102d401003045408010300c4842484000250048100d0007540c109501426200d92404150702182c0082c5c040d4002190381d602620030740c2c3c07440e603a288487c0122a4079500151816040c5450440c1c0801021015031503541804451854805071324800e004804039000c46465040404c4034250a104014441c034900f019010510000c1c8000a00041640c51941c460098000d00106c8981840750641c481c082000b8100e900024000826040e080065449001c41c3e032588039540940700c00348000c1d2140305200070a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 840165413 1250 840164163 840164167
    0x90a0626060108010b0a0c05010603080405190308070f1e06020a0e1f030f02120a050601090b07030c0f031e091a0c0c060a17040b19060815060613060513050114 70
    0x170040c1c01d40400703044045654074107841c9850a54861600b103540e00d810569076003a000030144628140303090300b040e45841a00d5440c1c052451034448844078011030070003d141c2000009450300303000c02240025810015124540d094603d5071501c1030003580710300b404002140b0314000301520791400b15006580d08900f054540c80400e0503010880040010b0088502d4040e400c2c02004c4038a0514506140300d508240400503003401c0200c0090640390148d40002d84840c0100030303100c000b943c0800c21003a4140e001c49400c458006900c1c040d035a40206a54a84c81000d44404900c02240d200016070110398581021150030041c03202400c4a034030445a6011256000b1a01c142580c1026401421f001800d480e00f040e03a40b0b8a00c032061110001500c0580b01d900703038141400400e810b03a698a001e0144000001c1201603e000c4000351200c3d00313005820410414400040d80c5902c442045900d080b150003450090f050715020060010341111101101142070900041840d5010349240d802d2000380c1c4c18403c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 840166663 1250 840165413 840165419
    0x1020309040509010f0c0921080f0a0207030605190516050714010e16030c050103050f0103030c0201030912020f0705040218120712030903110301060b0301150302090a062606010801 79
    0x100182c44040c140c20744666031214400300d1000d0a1141c0700c0c0b6024a40d485c2283c162a1214074001d04450388198245820700040050008285208030342c403814039000700b643ca940d0509010b038248042984040c2600781440d04100b01030300714182103d500f802a1804006540b0b40104141071841c506250074041076080100c000411101c06265002031049000426103850304803840e820558602c44807440d1241c1d0701001d000700003804070b02d000074002c20320b0200814a020048050075070410703c406400e20400040207829a4401c0d0070240b83d184d080803084400c078807072020095980a0300c0d6010031840c0688140032445140c640201c2c0e12503680b5040d603081000340700c402c05c42c090340820300040b6648914500000c0400d81c80d100243d2050094880480080c5141410310001d800009410700c282d15000040c0400c111042c10340e819071b03000101c1500002c03c440e0041c0c0003842234080c020703031022110f2000103240c1d901c860520180300c2e8001d00001d240030443e2031180007640c00d441c0180807403c190018 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 840167913 1250 840166663 840166669
    0x31e14090f150a0507050708011b1101020d2c01050f040201200a05060f0109090f030f170a020309160e060904061b02100b100503190204030213052401020309 69
    0x1070740741010080000300074480b2031060b02c2e001e030b1118042c0b101181e00403d10354144901809600002c0901e42c000340625003451285602194024000000b40318000c80410017206095041ea00c138011900d400b0006040000000e0020341111f602c40d0303251a42c840101c03668142c040c0030b61406100c102c1510b2160b40c0340c0b5030041d0b60701003144504180d00000a489000c48507005c105014516003c1c8025003100c2c14001c415a44090050f0001003510b8240740000c1c00091900b0500e41d2201d4040c64404041d21001d10b00703e5803100703801581504c03c112881403003000c0807207900650013100711000f20380350004100c405100c0d100c0a4820031078003c42003400140c141c140407a105a0042c455400000c1c06610264042d00490001d2141001079120104400c041c003018407070000300e9079081703032940304e44081204010001d01c001800e249402030003400350070400c803040e01564040c603801402c4c00013004000f0940001420119820102c14081c3c94414a1070341c405c00703440b07500b0403040c0d01030346c81c120700784040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 840169163 1250 840167913 840167929
    0x50d03030b0936031204030e091521070b1305030d030e0d0804020f0a0e060a06022107050307020306092b090e10150c05060a2705030405040504031e1409 67
    0x200c8900d600017081085c0841030282d01c4244520310035254103030418020410300008250040074128141c2c0c90b50458201ca40d60764407800100d1041040d50140c009840b020346080c00b41941c040f034891030011920f000380060b010154020b540b01601143e0702020507007001c40a035501140032041c25004101c0d03450300140f0032084c05922a00140400ca5855001d901280c401e00e00d9a00c0380219000f5881440b40c0ca00c1c000c88801c0007882644001c000080c030841c01c400035010f03940c000072030501d0001607000130003a05200f03448056130004d00360742280c0f504420b02501ca02110000c40481e40c003013028400a1111007001443e0036005950785007090b4188a000101c0440140001403512243c0000140c640d048400074128110f041d03070340ca040c0902c1450014a40712000d040d084178141800345c2051820f00c55001c04c83c01070b00d42400411500c00c01d0500604510440d080141c0080c02e0000304400d05402c03992130040404102c0c0204e0f4070704c0d210320084481c1848514000515070040000001e54a0080c41c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 840170413 1250 840169163 840169261
    0x30703090206030a020304030e3a0219080d0219060504031704060204090f0b1e010522031a07020a02150d020c0105060f090405100207060204050d03030b09 68
    0x14001031054441d000074845400445130b025000e03400008210070990f020a01e400e80b070700306888010b1003180c600b2800d01158948a01044400380b031a040c000b1140d600003c0c400b0f46600a03002101c1d0701c1e903000114900d00c120b4022803903d0311501c1e0309002c201e0b2000805500e034243c0000700c4803081d151561880042d090250082e002c0000710075039001d48103807100455003d6480707800c00603603440c80c040881e0103840b100c103c00c5882c6c515009159005481e40410740e4014200d51003000f90903255540140e401d4000d6250141c2d10f0300d45102e0580b24507140343d03200070640e4014040351840303910314001c40c514814215800401608104160001030800301c1c82089030300c0059806604081c0a0110700089030001c03200810145e4442081c0700349030a00400c0c00030b081c58155001c1641d841c1c140c9529a8455950400307116895001801c0070034041e50303605680c00b0306002002846800c40e00c0c103004010300192050507120720b010b000130820400000188042c03155412544880302d110030300180c80c02c00d00c869 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 840171663 1250 840170413 840170417
    0x20418200a0e01062f1903030513050601030f1704060206060a09021801113c1c0c0503191e05031b070c050d140f06010b31062106050a0b0307 62
    0x1d0000749032085c14080040b48070400309580d5407141035030500030266034003d0705078800c02000e841481c001c1500440c0f40c0c0e043d680c100d001c00b00e400f2150301d06000c8108285180700104c20000c5004100715901151990140d8001c0703070b0a005003030710362090004031301c83c0810070b1204011030500700d005035024580010300130102d40c082e0303402c101450400c0000e103482d4000c00e0b8091140383e00b011804c0c4c1c0902000001e01c11040c80180041d40c040d8490152201284212109228400e4002c0040000c02c204442251854074100c0c2101404440c000d800742282d26203400b2502000a84001d00c5489602034034840c820b04072102002d05003074000070055030310000041d10551070311035010506448a2022250861040325403c82e06000500042e080c8070310100c075906641c00c171720300420010a003081951206d40181c000b132107558074800c1c260900b8040c505100c02910404000001e003050f04549a1000e541c0c00080e51090000e04038180c0d006c8640324081c05520000d005800c1c0b00b090054006103a20003030354 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 840172913 1250 840171663 840171737
    0x15040224072d120924140f03010b0d1e0606080f04030906050f040b03280e1b031f0c03140105150703050f03090c010e03060f04020418200a0e0106 64
    0x149020751400d101c20000c40100da801c0545d180c840c0c6501c43c0402c00e00e503028408041c20946a524540e4852106114a515070500030031224000640c0394032841d000600041101d4282d55150b610340041e00480c4074140100d80c09200250040000c00c0f602d40c8196132554486201c6410410160361a8010541d07200f4811742c241300109801030480d0003140101e0a01c8118402c81035418101402040f200780e10b0003159040100c2c00740f40c03c1c8005075043c0a01c2269101328074403081e07070f00420b01c1c0680085045948141060350220518425440105c4240b00fa80c1c0034030402c4001d643d00740e5006828821076070030550400844a80982440203800400e01c00e1400c5440e01000c40c1040c84642c10956a1032215000744030b24074100e41c2c03c00300130110b000c4158041d08080c0340000408101410062019010710f80301c14100f00c95200c3c00c0d164250241d400810440300e041d1410240c00d5880d0600d102900070000900081403818082000364129005503840030b00d2009202c0901020608203110780000c4907803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 840174163 1250 840172913 840172919
    0xc0c0f0d0f2c281e0611101d0604120e0609150a05040e0906010815010602100b0103060506040b030610091512060302150a0206150315040224072d1209 66
    0x4203c4440001d007000c107000c08010402e50309500c0c8801c49a8400d405026000030b0b86030341c9030000f0641108142031a50b000403080301052820701d08420358441e010f000d0265200700010021000c0004103c00095504d441c800305d0100301f4401c19100c0d09080542c00001e50396180c4e8540003c1000f060040c0b00c40c82d104e170a01c0d80c0d8a00f059034112007030390b00b02da0b070350004c81c018800d11004100304096800c100400d0394441d45401806511001c114000b9001540c45044140c2164002d4110034010080070b070000e46d55035942d55249141c0c3c2c00941d03980d40319503001d2502208035440307081f0b080151008804100c1e42441c40260036649805e0f13030030300c80b00d2180c1c40310b1002000d43d03540c200640300900900040d542c0c2e68060320009042410040840c501c1c05240c0301074a0541d1000101896540440f512074866174a03a8000105100420000b030401004154420806280b4003005081220301c01c14400e036481e1a802d071000c3c000103030090303100f890045007002c610208451008960008846007043d409203030b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 840175413 1250 840174163 840174229
    0x203040f0816110406030c0e06011139010203091c0206030c07020907020f0303070f02010219020102040305070801090f02040b04141812040e0c0c0f0d0f2c 68
    0x40700601014040003916114148244983ca0510240d01218100052419940c0c5d40300d80b04080d024020b01520500e0000314141d000e04c00b408200300100045941c0d050400c04000c0c1c003c500c5800c40750020007401c5800b240411b1001c000000d209058018604240c1d481d0180700c41804944070200030946036900700c00140e02e483c401140a40e8901396810381d224101e006101d96031501038503810440d40000b05c00074400c80c003c400d07031b500180f942c507013030506100500b8200d000e4000c0503007000c00341c90840b040c01800ba405500410440e407007201602c032000d03030703d091040c22201d002001900d0810310404040c0140340603400411403410003040002c80070800603551034000c0003210142c441d03200f001d454a404503010031001d0116003030000000d1400e814003080f801c04540c080c004e140b10060100742030741400d4043c0064522800304a0407582c04050000009082008030b404450110b144401c0b075100b04c002c0c004803a004203e80006108000d24100c05001300b0a0f82c160842c00000210004125440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 840176663 1250 840175413 840175417
    0x230903031b1e0a14090a03060c0917030705010e120f070f2307080109031b051c0302072001270f121101080907060c0807020907020d080603070f05040203040f08 70
    0x1068200c0071a12818a00b2010340b600c41501c10070242d550090000d0801c5a8890414906888e0700407008200703001c0e0100155072085098100d000e06c01c08500810044080000182429500030783c000c0c0240040080010b450b00b070102c00d1b41c0b030104c008200703076a2414005001844800c4c07041c84089440324a0342c0340c001c00343c1e60380201c1034100340e0040700c0519400401c1003200080d201000003001800d12903640030300b84003030a072400c5142c00040840213050110900c410075045004c136103140140410820010300a500c00d040071144103411443c1d840c8441c0ba1941030000c08c010603156540010003120045041d1a00000c030041024480b040220741482c03501c0d202c2004118000e00038000d601e00c0d2030600040361010021a0422450702d00b040f00d03480d07002640d0403c50300e04d030900b888603040c1400d15110700e00c940b0380040c1d0085000c005000c112036000a11308114902541c03236400e6a1540420151161114441d003240014184000d201a18040e4011500070f40b10720764481ca0070303002e5a00c0307001035 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 840177913 1250 840176663 840176707
    0xe010b03070c240f020c0705010e040603080309101503080409091110090614030f0609040c0506130510111b0d060608010b150306060304120509090901230903031b 71
    0xc1004141c007100002c3c0c0e01d00640b010b80c4400c1c0d40030f60030454901000f503911480391003980e040100650350810380b512183c2c4108041c41d002840780796a0702d050482d07240d4410342000d05004d000d182c190045e01c0b803408104180140d0342c3c011003851409107032117400c0014182c40700c4141c07410344840001c03101c9941d402048005241c01c94440707420307842c680680a8201034180700c41c600382920030010800e584180800c540da00001c125840d1106440e6810b009051800507080786401c9a00050003440005441e00c2e803101f01d80b4115192003c107002501c08650f005091412100160320603402d411942c030845407441d14202000c0d0511500d60305035101d49043d01c1041d40040180c1e507443c510107442e0305103108141d02d001c400303400152841c00e2880229005100080c40075011516010801c0f000c00c0c42034040314964500100700c80407505010010b58001d111034007408003508600303200070300c1240c0038803011403003145a10301440c2180d40d245042c00d41c00c050b259500002171800c100915080765039142c03030118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 840179163 1250 840177913 840177953
    0xb04060f06170613090510061d0106052106010c150603050f070b0a08060d080706050a050a090b04170c030f03092107020f0103020912030c10060e010b03070c 69
    0x41589400700c00340c4075a200100ea0718582d0102ca0422449071241c07101e132803c80b00103020000d402260303410001d0400d000d0f41c10120489081000002d840c101308513096807420412030541c41d151340d03038101c10344192050a4041410f017000400382410118003800b0a9800501030501d07141c0350340703555600d404000e03540300c058003003a94809080c8180641044a600c003040f00100410100341069509146030091050240410007040001707001d5464160103c1c040940c48294075450f500c1c1460036001400007102c030003070348502e404001204a045070241552280e0072135103000071600d8035192029800d404000c80d4038030200c00c001c40651104208002c1c0703a1103481408180d10382c02c00d000c1c05402d0042461005000a0341c500156485901a10803540496411218501d0b200c0c1c401c0d0050f4060f00030340c1105039018690070400555003201200070440b440e801c606540511a00204c0042200c0880c018004200d4190006200038101880116041700b558141100012100e50390385140c1c4141c6019404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840180413 1250 840179163 840179189
    0x20103090512040b0d0c0c0b010e0901020d0e033606030a0b030f0d08010b0301270e071d0a05040c0302010c060f1a120a2103060b0301080a021503011212030b0406 71
    0x5107048041c806c6540743c01052410718940812900c440508072010300459410034012804102515025412902000c45400c0e00748810742502d080c060703c079000014402d00714240c2040b0701c0214030804003c4003440080000d0254882e621805000c61504000d0900141580ea9040c07190169001c0044841440b03186c402080d04e00704c04c03800200406810707031226a0003582440103104080440d202c58824002000e0708a400c810008200000780c0182c04100d803440c0940e400218940d000c0c80c2c80000c0d01800705d000a5000c1e201e045a450403074500716005170541c240c00c5070510040d0301c283c0d4102c0c00c03607010303c01c0859642c07000c1036580c0880c0c01004c10828190000c074824981401e19402284681c0c40303035400341c410200709842d205040b061a40c1000b4050a03800d029489082c040d034090005003070040941074503581c4035400c45685c0c1022502c00d0380319241c6001210105032111086a058459080b0400001074031903898115a101b01351200c400e0507144e5401c4401600c452113104010300b200c4610007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840181663 1250 840180413 840180427
    0x30e1903030f090c150305040807020609030c13020c0d09050a0302010509032a09010501020105040c090519050c0405040b06040f05060d020421171626040906061e020a020103090512040b 81
    0xc443c05c0403041001e0705150805041101080e80a01030301c02003901510703247e941e4490f800c002810440301c00c003059030141403002c80f580c2040c925805042d12260b4201240c504015400040c2d6100060303100f07003907010000420600040d4804c1028007006034020301114400520382012a5000c804402801c1205204480d986454a44004101d00504d0700780020012418142c40380c000211080c010401e0103130315100461404001e2050760a0b04111103d0200018101043c4841e02e55000340b03c0c003403090741043c4050300da0b03180c401d084500725103503180d20810032440d1005020044e042600d251400c039600b4007001800d07903014040e40314520040964015900100c0c0b41040300318000f114180e05554041c0641c08a00ca810b0801201158000040c1440120009050100074550703103000300501a01080015442c0200c2d00618240c4640ba103035005c0e02c0c43c1c2c203180c1c0300000040c1103ea00040e4041c44900c0055402588a895024081d00035139800d0240045044050fa20a0b4441a41d2800010700b030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840182913 1250 840181663 840181679
    0x2d092303010b2707020f011806200d050603030d060e0703110c0a060207050a060c0206152b11150711030d092714040201020d030e1903030f090c 63
    0x1840350241e04880c4052032800c100810f080341c41ca01c20400003052802e502040f800c500801400783d10812010007801200c0600d091080380c407120031402c8440900b006070300d65031441e0b100d039540e40c2c525603540104d08100201d034408001e080094500b5406000c200091217007405280500e4018122000705c9034403a0502c168000d0491365840840c0c183c864051046503403101011811400e0b0f5900300c4030240e1181d0480c24038906000f008440100034901c1c0003000c400040c0c0215000b0320039420302042c004801c0c40401804001d030203460813640103408078030300c9031044610f50b81c01201c15030050020790111050031021507289a00100c50075900070300402e00301c0410041d811032a80041e002c0d0003915840b948100c1c00307082003035140074200214900d0b11a00f01c50040b2242d4036076410201d05003d01c056042c1c0511040701d100c0a0b40d09a00600903010381d62102c40c040e004084006403008000c2c1340c402402c5510049200c0fa0040031030805840c0d10303c07030508801d2402200c40d8203016528100202c0d2420b0b002c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840184163 1250 840182913 840182921
    0x60a020711010801051e01020102120112051b030304050d14010510050411070b010e060d120f0e090f07080703020f030a05060307120803040219030204140f06012d09230301 75
    0xc05810001c143c2d0051083d03481d43c01c010a2040542c900f00f51640704150b0040c0d0280c060f0112610302040c52000000e10f0200344181900c095000d8405d407288540400c0600c0c510071901e40d4601d406900401c000c11090801c0d00700d800206000c0c0308030307018503c3e002034958250b44050325282802d2104040c1030280e8903083c4590002c100c10880381c0c5180401e00da03103050500005108003031281c4d0902001070b05175100c0303030700301e483c9158080172110011031400000380c103060f1400440800038003181452140f50402d141d07524024175921008014550315408100d51a210040640701055002d02140005418010107140a030030201c801143c240361140c1818600f666a0380520942030341000d03071002103031142c011690069019951448085201380410704150816400250002d1910480040c800c0c440c0f03681d140100c5410519400e99210500111154001000c60200245104064140c20b021a0305002c03d42210350800070308450303650a01c1481d000a46500404503401007111780000e10703080c8a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840185413 1250 840184163 840184193
    0x40608011505011b020a0902030703110a03020d050c160b0408090415080f150123060418061406040b031f180c030507090501030e0a0503031e060d2111060a0207 70
    0x510135480c41d01a0006145883d13144101c1f50345a90010124000b0b03442904003a02440c10f00440607621780c5810001002503122210ba072030b08038940740c041440c038204101151a803404840314a41c1100c981e4070341c0351031000054000c60703501d181000b00c0e06503901e0b41c2c0034441d40e13403960001410034146000030150400001d4a1848129044041851013601b0800c03a02030555100e010003a0100b036500c0841880042c24007140c40e4081c40216001039001401c3c00000300300400700c0002c1c80090340d10b2100240c02e031840c440f1154000b83c1800705125a00ca01ca000d5a40802d90300044c20711030311400c060160382500c0c0d422241160760340060201c5450902d010304111a11039180810040c501b2280017002c0300c3c000d0050504054640e00d40a0b552030741000245a26900002566070360b0034406080743c0380b9941818209c50304001c050025040f460300aa1121926420090143d80418044503201c000400c003c9404140003094046000030720040254900c035007591840107070307110380c1401c101040c1a1906 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840186663 1250 840185413 840185447
    0x240a2f060c09030a120e0405010e01080d0c150b19060504031e021503070c140705120601080c060c0703060c020a061a031e030d0504051b0604120b0604060801150501 72
    0x102d800140c41c00507100c0c95541d00403042126800103010f08480f094588000310764028188800841e0701d005902d6414101c40c141c0341100d00140100d042581c2740714103820041c0030003000036000c07101c10560381c10070314035044010610040c0b6040d030454400c40c1590760b08030100055000c03401344100401c3d0358000c2c01c0700e102c4c620394298841172a80041c124900403410383c2051880031001c59202c40c0070718500b002da00d80c0543d480d44040001414680d50380203078824544a500e41e641d40f400d1001c004a40c0c903040c0c0b0403250107051750074561820321407030b41d2203c1c141068900c5220000000b090b00c2e807048511482d481c2d8003800c4900518101039007034611042c140c4460700c030f0701d000c051441c1e0b0b00001d0504410401d428614100c4030b2081c84581540202c00d03202107880c0c1081c040000300100413400c41c00039050311901303a6040c2c14540c140b02141c0254020311001703e1254105001040d0100902a440400148049811034841c01084e080d640c1c08540d8422007002e1641c240207560700070081c5900010705e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840187913 1250 840186663 840186667
    0x2070c0e0c03010810110904181101030c022d0f160f0b1c06080d1205010902030115230f07061a0102030f0d150305060a0b240a2f060c 59
    0x48036802d915005c580400303000d41982e900c2030844950380390003550401c20b002802000102c0b0f4100100f4088900c00608882400940200a0580d07001c0d100384043c505550f030003003040c0610040710320408070382101001c0031100070f05121000d0301c1c0100141f03414844080041c1c1400f040884806108858a40144640b4241c80d40140002ca034140103441c0c6018000e40414103031b200c00c03019080100141e07003207101d1900a01480da81004e400200404001c04c0e007802c20090f903070b030310032440c41240028090322445001c10b114042144c2d109000020341100203258203091500070344109080307980b100703a40b28400c9002142c14400d02c42c00d885450f01c50f500c0076400d44100c9004400003901e03403003003800006042e03101180300c4a0341c40040e80701e24004d101300e102d00712540e9241c4c20125500c03482201c0f20041c25007050020011400c2003800c06001900d9074060071120000079002c00e400d40c11200b200b03410030000352003800340801e00f00702d41284204039009007160b20511442c05170400700001d104800401d41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840189163 1250 840187913 840187919
    0x1501180e01150816080708101a1803010905060c07030201020d0c080415050603030306130603060507020f1c050301150219210201020405130207140d080601171b0a02070902070c0e0c0301 81
    0x108520031b030b00000321b1400e181c0603900c0010307801c10209940c01000300301d400801121400e21584c0c00400e4100d0030848a415608001802c0600365040d0200041c01b94015034041540b40400780b01801030540b190001504000542200904442c00d071401400011003070009e100910034906180742c000c20040b04d041c401c5180c10710103c0d680f444060640b078040d04803580d600c100c2148680c803400140d64003110034040d0b8140518000d50b0b80e83e22503035040700e074003a0060151900e8182102114840c4a82e203995045a18095000b852588010750400640c090040d41c0344944080f61500c15581e8428000c000003e41c0304002400c20b09084c4141a0540e03204000a2086035649828101408194000541d0360020307441c0541c0c0f4200c03000d031000c00b18411686001d8515030011200b81c80750f0b0080e41c40c0e01d00140c90040500026205481c440c05c00300c42410364030a0103080030001c0031070021705c0c0115481c0d10366a21600040764040c2c282900c804031542818043d010327500307a241e50081d802e20005421541 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840190413 1250 840189163 840189167
    0x4051e062205180f1e1504080a090509100b0a2d02011a030705040209040b0d0602070b3105120f040f0909050312060102100e0c03010f02031501180e01150816 69
    0x104010445c1251901903510800558208410364400c0269100813034241043c0c503201c1c90341d801c08603850340450440070002c2098140a0540b41c4103801c25014030781418600290009a0780c80110000c1c2040380c401060545c0c603240816810100d50701e620a01248000c22000900315411550407442d0040010a2074070b050b6000107061080c1d80301200c1c0140d070781002d840020014404450126000040700323040800380f11281c2d002d08980340c090300402c041641e42a0350b4820100559100b032401e0300c034828100003a12a42c1c903807400b10501c03c50449050464600f006101500002d29010b0f4405001406002d22000024558000c108000c403d015000007941d40f00e40306c0c00340c032340c00e412000c1600c40007650982c402c004154a040034141c04100d00a60001e03c2034071440e600c0c1109001e503003000c0701c00030360710564801c030303032164081c411241c041c8500340004440208101458200b240e000c0c2c080800c084514144e42c5008250072105120b4078440d140020780303406001021409240c1001c2d0205000b07075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840191663 1250 840190413 840190423
    0x80c030c0607030c0609110d14100203062214010e0106030c09180203420f1f050f0d090303180308180a080c0a031103041a09040924060504051e062205180f 68
    0x1410a1701184ec800380180c0014005001d440c540c1d0034208100800003545041c5482154140d03180740d03609001c4240c42103070544a102c2948682c4a4200540310080510f04181e8003443d088000901d42100000588601d080145980210317151071203000135050b2007060740740f40d80c114014001d90322000c140c20824005107085802548070040f48204e400030014441c45901168000003a4070b580c00e86500251081e00700918107184214082460b26003018414964045918420740d807658a100d000c0d03491500520740540700802c0701207280315407420440003034810805002d0717412005d07000f844009094100107201c2084040400c041d0703002044240301003600f40544008032a40403690a55441041001c20000d0403800000392401202408a900e40c18011070008815075041400784401d64941082000300c54060304d40c0da00c10310082e00310044c0c0300654244c00c0e42c0300700300810407004c1c0d070f40000c03941c4008410000300310151640c1390b041200d080941380c401190084020000c0c41e002d0314001c0429528 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840192913 1250 840191663 840191689
    0xa0b030c031b060d0c020a0c21110105073c0b06041508030310080105010603150504180c0e1617180f07080c030c0607030c0609110d1410020306 63
    0x6a01c401c440850f601d030402103807000300610108200220103d50000d44843d420581255140203100c0002425603024031126280301d000b0704003011600c0c85559075070810f14000007141c1440003e014103400303e6110860a542841000c00c41c441045075408400c035950406180c0c60400844c200f0b05101085e1180c1d2465400b0744141c40000f00c0030784d8801e041c1c403004000d522440749031200000300554403c0b4840312000300d0700840c000b4802030362039010641c281d455140302c200000c0d080550800407881e06412207a02d0009150b0f80034501d910740d40350345c10440510307000002c03070810800c14001d44041e4074800180342d055a2400c140c09540d41301410342100000b80c0542c0341842c2400c0c02509012040c03100f03c40d2000c001048454440c0e0b600415511041940a11031082c01503201e24111070801d5000c80d0511a0b040d5900300c007034182c50750b84000801034600240c4802200064052640e2940c40b0750700e000500401340d2a4403098444482403400d81c0c1d45c840c5c82c21150040c4107000d1680c0700e0900301010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840194163 1250 840192913 840192943
    0x111071101020303070c0609020406030b0a0c0e1c0b25110c150d050915090a03110a0b010e07020f0d030501090b04060510030f0f09060501030212010203010609060f05070203070e0a0b030c03 83
    0x200ba070231400011301030000c50704060500301d510f0052000d01d6465601c8240b160716141c54402613183c1d10801c205d6160b0341b52464480e1419145035460004050b8400c040c1d000814a24070011100d05900340800b40c40c120002c98007088081c450040c1c0c40070100039200c4240da04071590181c0c2c0c0e41c0b09807881028045c0c800d10401c002e440b907000c1202090709201e21441115003160740040752406000b4a0ba81d80e003d84819400b056034180402907554012a04411071900421900d4243c1d1a04990b0441820014582811401075218403592442c0905c02115032034129a1b010038194107041d4031404480e5020001485245044000c000319140d58a417441407644600700040c2e0340000684107800b40981e0703081040d500e07242c000c50701c04101180c3e101e81d0581e8020340d0085100c2c00c00c949034508034271003800b465011030000c44041110620030030100003201418903109052004550111b0700e0b04c611508116000003d440c100815200c10340315404440c071040b00100301e19050b441c0803d0b01c440c00c4136404c0c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840195413 1250 840194163 840194171
    0x90509120d090f15060b030603060601080925090b0409020d02040f0b040f0507091a0324060307020f01050718031506030803070806010224070810080111071101020303070c06 76
    0x494080c20351016902da508040300142c030b100c0704e180c5004030b011541e03c915001458500e001c943d08150f081504d1040601a0040980c0e849031401507400c00c0000340050410321404040d090b84804848070261469082500074601c9814044544c003543e8201403054041c03441e080d100c10150342c40c0c14040f664550151400030b00c0c081501e45501c00380200b40007154209040038444008010039600c0248034510650b154001c2035140c5820841d001c2054042c04003243e002c1c40403a1881c0740a00400f0544070b010407022880d121158081241604122410000368100d08619035021000703004180e4000f00a01c0c3c0f640115066100020341080c8500001d000706a00303801499194145034403c0001d15040b2401c943c03245446c2000522096003180c0660040c052403c3e00c00c00e94140d0903103031010700f4501c80003000540d554401101c12000082121000100340040001c010800707111b000b80d000c40c55600c045d560040c1e402e0076114521051035940c1194020000c1002f681c1e400080381e0112540900c3c00b007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840196663 1250 840195413 840195427
    0x306090408130b04030b0906070819090213020703030606090513020309010e0f06101208040b18060a020c03120403030f0804081917090a020109170f010e0606010909050912 75
    0x6118050300d00d05208202c032620303000c10120b52907009032040301d2003068070440b19500c1620705910307140c0c10789000c00490802c002003240c864a00200c0b0403040c95124000a24201c181c00164860401442200f685030380041c0708428154580510b001406a41c00c20340c00c44c51426000c100006012003440500b550f000c0b0225030122001e4100310030700c0f80840e048036050142101140e454903000d4a24034010300300c4038000100c1c4101001c0503001c0a0700700323005a06003860044613030441e9110280303404a40700c1280c0082019950f0f00043e04954aa550003400080301d0041407500c0c01c069013000c120400001d1200b0000a640003035010b80044903460800881c0d159441e00c0c0c0010f0203006101c4100070540c403008414250301100d480c45003000204038100b030b5240e80603829206c840580d0040c2c0050181070040c0100c0c0c0c408005040e0480031081290041c010103031640e401c503030511102855a07048241031003110740c1d101c010403001c0c2c0001d050400c49414000301081d81d80c42c941c0d50071303148010041154 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840197913 1250 840196663 840196673
    0x90303130c080a05071d10060c0218010f08240109150807030308060103050a020901121d0106030f02030d08221a07090611070f0b0702040225021804030503060904 71
    0x5004110b035404440700308001d8540070382c49200601a00400741e1144503c4a000f002440d00940030324040c10140d0290350410100700c902c44486981070740c00540407005424034514442d1030500800198201c003040c9818000024285819034400c004454080c2c1401002e2886c140d000e641125a82400010100031411144004660640c0800c0700c500503039000005150304030403103503c00e0340c007642c0801c9281d60b041d450130224014010581e000806130003910310850040e030301207000c94104070f114120320f0384215801030940e482c60708111810341c3c1404c00d14003142420444204041020b05085249141c0010303c108544444000e40b06408031201d048014001040310009441da484d01090040c1c0c0750100000d01884401d00c10400020030706a013194414500bc59007401382c40745d84601500c624034003410024039400030002a41d100c0d6081020b0b9041000185030b4a4854928011307041003170031035004005146044603114401100004200400a0b5000b8203d84d400300301240d4800c003540b242d00380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840199163 1250 840197913 840197933
    0x90a091a0406090818040615020a060b0f0406060302041d09150c090904111f0e01081e0115170106051b0f01060810290d21030506040b03010509030313 66
    0x60304c8208002042122404e05002882c501d01050301d0078002c06a0304c6845815000000140500582048075180002a402d40190030844001000d0b00d6004287c24002000c49007154081e10111760b0018040003a0901c06000720680c0c10440103902e42880c00f00d081a456402a030300340003a400c2610000360585500c107080e1043c4240281200380c00d03283c20703c1d01941014110703003002d02c00c0c0003000c0d4401d403070302914600b900c2d002c0b110b03503c24901d00800001034900400140100042038070348a02a0b0440f40c0d0180384500a106040703804d1120300c1c4115016103004e032565145450000100d0041c401c440d0090111400309244145010170345d14031300860303030610800420100941d402d2440c0010850000a14944404451802008101103001303020b140071844500d1403420390715501800d225494038880d400305540c0a9130320380c00321102c000b40c1d4030848448541034070003003540c8000b40207071030815114107560741c102903008200700c0c104804103a07034900000300500344200e90221740204101d107a040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840200413 1250 840199163 840199181
    0x9040c09020d0b1c05031603050d2a180303080a02210117010204030f08090a030b01082b0c1106090303031e07090324020906030403020705090a091a0406 67
    0xc08645480c4080b140074040c1c002c00091038810701441d10030080c2d2003460366220141c0c50b4480002c51070071a504406c9100c1c115040002d80511100344041c0103d03000c18000d81d014500031041100740c0340131961690005000c429003038003c0001903030045500061032010481600d801d401c1501c02d580c1c0760850180a80310b408c1c61038030a6040c030081d2090b0b0400942200e8180c50700f402c2c2c80c24a0590300c11401d4200d00032448050b041200e2240c103e00426480e00003450640c074064103e00c00d1070f031280c86480700c003502030f40310105690000303080c04190218182c401452544407480060000050900204002e410040180500d00b4a54618901d644c0301d070121402400007409580c0c69141a450401400b00049129040c514195001401241c400c07040b003c00e50390300109601c400492107400c6090204000d000d4040207070700704132281190355500c001d14030851184e40205891030030311050281041c8094000196207081065420014030300b40c000c000f904251450b99000c2d562181429400342c00c02c11 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840201663 1250 840200413 840200429
    0x603110a0c0303050a272f060306010201090c15020601050423100518040204050a0212070f090905040b090f070b0702011d0405010618080319053118020702010504030209040c 76
    0x81070421741800301210ba050f00f07e001c1d2051001d4500784261409110903002100c0448541d880f10b5000c01d45400c40c05103030024410301c0006107514099441102d055282d4200c0e2000c0c89040303078074040c5150704000c62030140101382e500740030b0890301070004071500541c0001c0d0304080c2d842c00c2c00247c1896046100400030480100030f5404c0400100005d5007880313041d18240d000d142000009540b40200f0b00841c2c110411440c010721256650007400c88000303540f200c1c96801c011981794009013051590044c503010f2406415480c40b182405d2068914090746592250288d0300401d604000d080d081300705452459030203003851504100c51840d03659034000d0b004a0580d01030720b03000010802692120200e1990001c2c000303a41400d644800704941d69028260f80740141c080d4011680500f14440d4010740500240c1100b04103c810f811101400300e80c03409204002c42001d01c45d4100900c0010402215424044110840c0f5103400d80e00000c11070300c15400040e00034056a4042010001107603080f1000303016103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840202913 1250 840201663 840201701
    0x102100507030f051303080c16021e040b0a06140a030e010c0207051c02060d0218090103120215060f04110d020309070f14010c06150b0c03040603110a0c0303050a 71
    0x1006001011962940500f59140c84005428054061210f081141c0c16490b20b2400e944c0e10008115075620800e8030707040c0b00e00141c0481d00113865080d100401a4031840030ae031900c2201c0405d00c0b0031a004090494420020303044100100c64129001d07914400c040144695514180c0e44103401801c5054007140b5603620b05040010101e80c0490190b094400c104c2c2c140800080311040244000d1380c14501a40c8640100481c03800c03081140e000f8410b80741d100012240c0c08061000007203503d0f100b42d00540d07200601c0300f0003144640d810b10548540000c0d4642e0b41d1103d08082000c29080100388203058051680c0300840c0c021000c0c90000d580750b2180c2c2142c195036914089210a03215003452003407200d000180c0b079000c141c10240c80484520310a040c1d4a0869581040d02d0300405450b1001c00848221460880480c0c8910480018050540c1c501d00665855142203030040885000300010400c024040c0310404450341d0103030603685c00c0354062078042030b103440c1c400480c0700601c203c540b60304a0f80f0b41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840204163 1250 840202913 840202921
    0x142805160b060f09312a091401090e030c160312030e0d1202250b0109090f1b0b071202060919082110030c05150a0e01021005 55
    0x41c4210a01c604010380d2280c0b03140a450041c403100003030a03218032100400c80d10b070390108080000181d1072202041c0c1c01c0903408100315101c3d00707039110f40380741d401c4807039050040801c441c602010740440007082c010804200c5006212a00405210180a10480e6a8a440c1070f503d13459010415145e02d124240300b590080d0508204109110400d40f10460301034940381c0206280500a201e0320382e10b0000500039181d010f24116044136040c81c40d00b001e441090742805100030400d00c0c481d010503002c200c0c04200714800b04a0810440c100b005030701108240d4100300c0c1140008000d0805085020391181a81c12200c01c04901006003c80320b0f00070450a24010a40300b06000d00011000290740083c0c00351101ca45940c01d145449210460821446035010400c0c0e81c00103803080002c1441550406403649000c090550030440c03007800703503914505021030394410710500c06402c402030000d04d011510510105040c41c03031b00c1d032140214520340c014010100d44040599000f4000452f080102280402031454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840205413 1250 840204163 840204173
    0x6050301140a11041d0405010e2d06040c030f050a060507030c11010501081f0b030d020f060a1e090602071b09150503030f0a11150714280516 62
    0x12045645200480c20003c2c098442072000048500382e070403601e020b25181000603144001c0603000f4200300c0d495946c50307828011002007800301c1071351000c26100c01c0c00000d0140003010708150300204007c1c126001403091000080c50784131a00c0403a80c1c4107030340351940706050070000d00b00140e9070006081035003004200728045905a1080f82031034a191914106c0c0680c881d84c1c070b403c03241d00740102d11403988070b270305260f10074416952112a0329241000c00300f802c1100700082400e1803150307129100543c0c04941800b60a0707005001807940200b000008001e040740c10249503e43c1382030310365058001d950741c4a0943c140450394044030340c030a401143c0c283d101000c100080d1140881842010a100d1a1a0303118241040d64040d8404680c0010011030a0620a0880e203941d58801c08501c2c060005440b01e00d0352007001480400c000c0e40d0206005103151038a4080a410305c0d4080a180e886c2d2401080310030004400d0005002913003110564503484480c4141c0160b48504c580e00741c4086014942c0d41d41e9003001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840206663 1250 840205413 840205451
    0x403060216021c030c020f03030403061b030e030a0203160303060305150f07021b280602071a0a050a0c3e0114070f0f0c0803090a0f05010507080d06050301 68
    0x1902c2610858101090108403100d40e0014030001000141129200c201602d003281c0c00c2049020001d094a02d0607580780d41d0a81221002c111501038a410a80900c02c01078040c0b040118500c143c00146d880c0c6079030001f00030740700d114003031408a050480140d40c5060600c6948080c001d1503024044910100c3c002007050452038003218185081c1c051070000568003480071801601003145100b403007540e003003a0010480002c4000103107103241c640280f90f0061300981460290010500c90300a032104905003c154024203120b0030803a44500b100f017002a00d850307030140450b50002802d14103143c01003c14a08400c40040f115862100a0100e070900c0440c00440710081000050b044d07100e4810020709001950300070019103e482080c10240130440200e103040d903011400c14402d46000e10000c0b05a40c81008280c0290811601c50380041003e410b58100601c000c000f0f084c5401c0d40b21314103443d00c0002030a601c102e06006020103004240c03112945269089071001d000000e00901080d1170414880c0520 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840207913 1250 840206663 840206707
    0x30c0606170c031605010210020306040902100f170411121c181a07140309100c020102160f1a040506190f090b07111801060806100207080d0c030504030602 68
    0x607004038a90108051800e0001e01300300c94060b00175007401403032140258000d401c024501c40d00a40c44040e90001680d5004400901c0580e03a07c61868003210404c0c01071036039000680d1041503200d0102800301141581d0038403404230004032031010000441129035420f003250354032248920f1010303400a01100317030440c54030301c0c03844070780c40e80004c12a03a036501c0c00c03821400c044441108160200292008030b10003e021072001c2c105901103030700d403203544804682d8641d41001071200054980311200219a418884045559a4103600d0700715203080c00940f01c0211103610440391040760100d814010708035210103031070080100528950311032042d1607021500784005804100018140081595101d004008980958090700f0840c0e00340031541c1d841071404a107410005500081340d24001005942407559903018140326982c5c0b201e607050000502c054401404010810740d04601001e0010032000106540340d01d84514194032856128201505d15114542010f0082d60000504080301d40c1c0701041c00c469 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840209163 1250 840207913 840207919
    0xf090c031605121603080a141218550506010e040f060504081204050706140928050a0305010515220f1e05190513030c0606170c 56
    0x310f0070220341020780312000d8607400c4070b0000c40001d0a2001c5007800000e8085110642040c034003030b1000050242003038204004411039040c1001c10082c650004110540c400c0c019040103150324142d26501c91024191503280c001c26400ca02c106107400c41e00f00c100301078480c017458041c2c080c50703008201d100c3c0341034007050781030320f09104417400081c02403d5952580e12a07900081c1507400310410307540341400350030040c00503100071030140301c40300c1c072034000d102c400b80140c0c8120014096145400c001801c2100c44c07800d01e03600344405108880aa84404030342000032112440b0030a48007120300e20f074025400c8140c00c203c0e00a024240c0c04000c0000540c03080703004003c4001541d9107404410104104500c2c0840840f918584c056038995070440140c004045a44400d940451528200603119800480640c6101c0b0120386500a02200c00340440c2d0112200121000510180c688000040000900d0110060400104194001c1413081071341c01200030304104152a84c010703800804040e5a40d54000344248 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840210413 1250 840209163 840209179
    0x11e020702330d09120c0305030403030c09090204090f1419050a1404050f0f0c0a17070515130b04050f0d0305211512120708090307031b1502060f090c031605 69
    0x209006e0004420001c0d8150354040c034659450b58120050620b4000070024004901c01c08280a0210b00191000d08007000700010b2440044a80f01c0c1590902e01c00305016104050034002c001c0403041c22038000c2011407601045503150020100002e1214802040d10662881e040c081044004145c014510740d500c0112542901c0c240c802c0c9480d0413441600030792220201c181000040061003c0c289500800c8095a020b55524001715022680100c242d0141400001b1140c14000401a00c0300c040d02d9141c8030300d4107007806c00f8045010340b00000a414880e1401c0901031003014412801c40c0d600707242e002e20607542c0303002c01c01700c58200781c1c0c06035119030140000524040850500550324940d92a80e030700181810440c0b4070340f9642c00d40c8000b205440a0f4001c2003016100c2d201002000001c51103031101c9034007110000740c50952100e00360011420b00c0480448a00c10130342c0000e46a8100010341c070b02d541da90b16500200b91a004920b641d0a415000e21000f082e40d10502c42d205c4000c43d003040e030f0110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840211663 1250 840210413 840210443
    0x90c120709080c0d02041b030c030c08160318080705010507111501050f010e04020f0904060807060c0206160f050c03120703020a080c1509011e020702330d09 69
    0xd035801e00c0394040c11a240d4404a0b144402d0700d40b100072030500714005440003400b605038070031001c0820441111000441d0312014240c0310a6450310613824180020300c0c141400381040c05c5080c5400084801d410100f40e1100c0c01400101754083d0032141c96a840203206955091501d44140a4103003280e020010409494258016170f10104a030348050203942e00305c0071941c0c203042c108040d08120341c900b20704102c0b14010310388403501c8030b00c003c2c04071540f40b801f0503448030300f810100020346500c1e8000340865044050100441034101c2400b4060070f504440183e210008081e40d1070780d20300e0106006d0700ca5403001a001c0c4c140040070401c00c003058405d40a503036400310140720101092145600040050344410998404100c01030050b003c096022030070758800707800100b000110480c055464200613595000500c851a030464002c1d10180b40048040d0700348085500018001000504401c160f2080b80095102511510b209085d500419401503a00d803800c0d1421740d4024a01c1440403201c236004800a2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840212913 1250 840211663 840211667
    0x1c030501120b0415020d090602040e011202090412050d110a030c030204080703020d1e1a0106022b02010b03010606030c030506040204051005160f0b072019050309090c1207 75
    0x44588641202c01d400007a11196034444060810310b0345000a03e60902030340220001c80d01500288601600b4056212410034520404203003060740030040c010890400341e03005031500d0700301d55801504001c2140603131101c41c1c4142c0c0d4510412150f104414540480c14a00d016001c0140c40780d05180c2c0d40c00c110f04555054107030100c0c40703540140040c0b41c4c0812010070041c074001d803945094610599541c1c5a000304c040000c0401d40d01c000d400c84540d07a09000e410181103020100d24014403407440106402c0e28100e003400311905941c000e20071024091807004034064002d4121744543c110103002045a140d80700700c020000d10401d4070101c00607041c00b01065607071425000b0349058400c010107000c00790305090703402d0b100c640c0440980d204002c640e41003400860050312400c0d80d07150085500003003a1500e10401004080f5003038000300728010000e100091101c0c000f603900780d0101c0801e811880c0d6240c0d41411491030040000d5241d12100030020040c0ca004184090900c00a01c1d401c1c0d0001c61300d541c481 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840214163 1250 840212913 840212939
    0x6060509132604091104030f060506032404020d140a030915030e1513080a0906140c07050f0109030c090e010605012a08190c030e0f09010e070509031c030501 69
    0x10b5030003102040c0000e102107503541d030007446041550070f82203180568981d2514070b5544103034401d8810540d20030070000942400d00501c9500d18080c41000741101d6805441184104041d02c042d0040408034602000c02c68080e40c591800299031080b078000303120030f240081108040e4024503080b40a020351111040d8080d000d15246022030402605550001015020400380f0060070b8500032900380e84a400032a070b805005002c40002d66442403000d43c24008050310055562080e040f8443c020001d001c1e800038080381840590790203d80d4031012070918030048611005580000d09951020300002404aa03954004070394243c000000340411035441c03006551945000c0200344100c0c00c0d0b075491460605003952043c510600c541083e6042004818000d180c001c100011030f008500401b00d010181a001000703040e5400045aa103c04845d60f00d02040c0b00e540c042c0f09500b8402080c4000c00e80300c901803070545031418000790440c0d0820034400101210200e00c0c10144000c40d14003000800c6030700000700303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840215413 1250 840214163 840214223
    0x17130b15031b1f05120912130e01050f0d0204090201020c100c110108190207020102100c0c03030e0601060f08041e15141003030e0d0b10050f0306060d030503040606050913 75
    0x155541049610180c60303408403002800c1800f1801983c030400304903907410008d0704480c64011002e541887c101220810744440680050740b1558421741780c510140c0da1516030943c01ea5041e80e012078000c04620041c0e1070080c456501944c070414000b205440d2aa00c04040d50340329005080c1080340c1220140191603d2605079103c884a0f5030041901440f00c969400801c4007610610407610a000c281e08400c08840008005400041501c2072a0003410780c580103224846240001614095240882c0a48164030940104051061800004040c8124114030300d0709141c1d10105104420380c186002000240c00000d034000840c60001d00c20305100101c00b01c240b2036207941c1e8500d2015411a00c0540f8004003945460b41c1c40484a103c000000d045c0071403c50050142c102c02810441c20f02d01000002d160365401e15010340c1c401320401038140c0e2503020790f0320807030b4240c1407540d56a204c03070403c0b10207888590402d42e0022501028824420b941040380562907004401c4c45948041c40300c082c00000384582 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840216663 1250 840215413 840215417
    0xc0e0f030304150504080a03080a0f1a0d0f0b0a050601141215040e010f02030711060f04021203040b07050a03091d01031401020d060f03020117130b15031b1f 69
    0xc44188400703101840030f0744021840c1c2c00c0c01e40c03d240d6241941b034035003c00c86804400103200f0109120000d840c501aa03c0c05240c004018040a55426040103168a4403503205100e091884640010b0000300c04440003415000130250515191148021005d04415100b10740001c10268603000400396820541d1444140440c40040301d0320f505181e68100c43c03001d481c01354000e94030f213000800e1520900c181440c9650004000d6200d1a05c08406001e280c0114821002c0d500308408000d5025400c40c4003d40c01541140c40030001c40503442a01d00d18020341c0c0100401c600300040d10410320000142c501c50035840ba540b500c0700e050b00e54407400340c4181c03a0910350319800c000800500c0060110643c500d1090780c005c00050400300c3e00b010309030a0303400907401650503041009040c0150f59200501d4406644071240c984280c0c24100707003240902d5403a180250104440c0d10115079000c12039400c9640448004003114000d820800759241d007014400055449061894040d182030703140607401d600307441c5450f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840217913 1250 840216663 840216667
    0xc09090a0204090611070b01050108060111063111090109140f070e04140109111c2a05090307090c020d0c0f0b0405150619090c1701090c0e0f0303 64
    0x107600b488040e00000904450460700d801002002060841c0900610360181c0484a00d40d45060300142010300007501441c108445465042100000041e0031074001c0c0c001030206240d10011150952a81004a800780c03410109143c05e10611032004103410a20904845402030f40c2d90315028141110f00d2664a921490401c0300024441421f5502c0c0c55131000460500c092500e6810002034100c07410001c080c020995000018011201e00d440b030f00e4140c07944011558a018050014a681c1c0102400c3e40070300c13140c60380c1e9919601416a100302c0d071540360000c0d0780101c07078411100240064000e0740794640a4400d0003400180c21400b406824000041c40d0058030314803640313003401c840011841d007003500c80b4084400c1520006000404d030500c100e003d10040c0c803502050f00b0300b80117802400f80010b445180c03010b104066400d565800340c41103c1c0a0f840004e00c40a01107003e03608020000500a4071b42015400051101001c1c2c0112058010301e030383d0362065414101c00c21100d950010400d030b070540e2003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840219163 1250 840217913 840217933
    0x150c1207050304020a030c260a051906141312141605031611100c020a090507022b022406040c09030f200108041511090a08010e0c0909 59
    0x1070320040da00913001900391401c00d610b07a100d82c0151455588900300b84202d0803104000c100a0001031501141008082c1071210020f850301c650301c078181d4513040401070030194407204000c0079501c002b102c151103440020b1640350103001c01d05200f070041da0a8a07507040c104c40110600b032003070040c00404094092100d060000e00c040361528850140c0044400e0721040010540e401c80c00705000e424140b02d0555005240c800600703020032040d80a1400081c40341e944001c10059407160780c07207020354824070000645540c070020100e14005000b0700e551607403200001307a034505110340103800c4241d140f20703000c950f010940c0311803110b2502c1100d05005842c4c500e200c0030604038940b035082818480304529040743c03482c0c0c40f0388500b04001e03881541214007485000a0701905020250040c5490f0800d0800001503d003c0e240d090503142640b071125100e596501d1030f10051601e541c00d42c0d0311210080c10800c1103940b1851802d0092403c158000382a01c030744044101645848440c0c80c0c0319500c1800640f0941328 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840220413 1250 840219163 840219167
    0x114010b03060f040e01021b1c03020d0902091f0f0605090609030304052d0a060206040f021203210f0606040e09190602030609010512190f050d02150c1207 68
    0x10142c40141e1210004954449980d10b500072010484244400160b070303911110303025a03402ca58403450600075000786190300e44079091919820406e01c0c035800c01580e20a01802980010034071100d00950000781d040a01c90b480505c0f00107a1184e0142070b110325401e44c0c807469402a00b0000e40f10310000208200f0007898142009009081049001b40449040c6074079200082d000c2021075214602280d403251f40280c5440300800031029080c0c2c140c850041c0d039414070800942b034a0004001070140d14414030004110340328500001d503c14550020703070b0344907044a54202c0c41c202c040098061420749810100709000c0465075400d009c1c01c0024480c40c03078180340c98030a00428800a1180400703001c0c0620300d50b500d8541e881c0b107000ca284200c0005a503407400a01b00642d001c0b043c0c06c003c2c00b485035400d61020b0503400145404000505082c040b4191000340b500d038901d8500e1540040036070042074607a5032426000220040d510112214a00066a030302c25160114007030500d500c00501c096001040380a4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840221663 1250 840220413 840220417
    0x151b0e092703040335030402011205060307241e09030311030408071d0906010f1707051002071a03040c06030e0c0d08130e04082a0a0303090210020114010b 68
    0x24007410560781019565215100036440c2c2105161050075450440c0109501c185401c3d1000b440403401c403401c40c201398000808030080781c00c2034800c09a03074401046c542e039030812040f030052001050321040750700e9085c40c00114100001568004c0340ca0310204112201504010807103076682035441c1d00b4418a162021038a40310004a0915140410000441c10400178000350010b00851400c00003103000302030895100d41c000901d0705401d40c1007500184440740e00c0b074200e03000721800301c2c6014450b540e81010b030a0a000c2c0560140d03510905049981c0c20325600415690b00b126081103050f024070036020030f10440c031310007104c004040d0f2680c51010320640e8040e511079903003503903010221101011103401051081203505425259698081040410340d002010740030302602c01001e8911182c1044c0c1e450300058050766082e040c29202c00c00c00361a840201e0001e92a110750a5011101902e49508010700101f10004c1c090340940010602e01e079015005010b01c920104454020766000d0b0318107480d1154035 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840222913 1250 840221663 840221731
    0x1f0306050a0e160c1b0e09032d040f030b0114030607050a050d180f050606030307050c0907180f03120f1b1104060b130f0b070f151b0e09 60
    0x100043c1020600468125024903d5603a01d0505c214600d5041c0b080a02c0c0807000100400c503d640100000ca01c41c0c000b40c1c1040d40600000301011180030040b2041d80414015034101204102030500000144160703c1d80d0141212404203040384408081e500f45a12a201200c6000110341d041000000303d9125000802c01d5255807007000030205803151f200f07450314640410590301c0c208002c000205016003403100ae40c02c000d045004501e0f0414a0b034605444910041343d043c49010710000148695000e81d008183c600e210755000040281c40342c501d21402513690005640b51010030700643c0205000740402e004610844e1100760084d000704006401201043c2021600780c503074590544e40c503441d00d00a440103040c050b07540320313151740f00000c80300d03514003643d44444da40c00203000b020050180c2440465803029001000000d10703880c0c038100318482801204c055a00d01c0d140001c07080740a130700c840005816001d55965403030341030980c00410074420000e80f15030382c080e00b880e004146101045c501520b08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840224163 1250 840222913 840222917
    0x60c0203072c010503071a030a27260904021308030309070614030402011e03200d0b04111c0e100c1821111f0306050a0e16 54
    0x6071038864122080d1460070030740304180500d0b0ba421500100b0b1101160b00d024100560081a0399840d142c5060304050900072803d001010020201d5403124050704940b00c030741da20080007001c440002d24003101404030b802003601d24806101d9120141d985540d4068403404008142a081110301030810009500125080814000c030440c0010030500900c0a1482500d981014001042c9008400780030a500b2001180b11030808208000040c0c0c0c0009000010144100c450400c00d242804240d004081c1c8005150b481042712202c207070345401200090560800341c0c039062000d076101000748000c0c0d4002c13030010150b080701030002d210928074241c0720a400041c5800041031141c8140f00d46030605030300300c00d44403d0544070243c0124280e048501d90380300604c4900080c0d519441c000260700074814104a90300b4507000f400211040c002d00f5030142a8003c001020005400288002403003222180e80c50400460300301040000d052420090050444006c50b00c81c08650740d46c0c000c4610609080c800e0481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840225413 1250 840224163 840224173
    0x8060f0f0121020a0e10170d080403170112030f030b0d1e02130507080c0a081f2301080a0e06060603070315030501060306110a020d0804030329100c0c060c0203 70
    0x3d81d03100740909004000070100346800e400c0044c4001503020950300700c84a80d0b40d4040000560910000f0210b03980c0c84180390081480e1078034541103550030b8504040780c0342c1109220000c0741c5148031074042c1d00f0140c03194950a40d56100944260140d4081e2600d0b91303030003100507641001141c01210311142d18504ca4003090700d240740c55070000e0a4504030061005010340c1d210100300c40e042d004040c0c01e030400300f21036095040c00c05a410092510308000c16001e4080d5a180c1d035900318120313000011018201000840d0400c600302d1110700712904074010001e002805510104a4040040c4030340c003020a2403c0103420156910014081d480d030015104004144c0c0e20503425100c03d5040b5402d20245208000204030240b860074038000f9a0201d014000b10110304201401c201c607000990400c040d0f0aa042840c050713034560805070002c01781139501c40c100302d900c3c0425031940c0c2c000b075009080040048500c60860311806034200e643c0c15104400600d40d130718400701809400e005568156403c0d1008044031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840226663 1250 840225413 840225479
    0x3050106020a140c0310480306030b0403030b031c02100b031219021b0604030231060302030f01021801050304051207030305061c031b02040f11030108060f0f01 70
    0xd1802d103071519003207411b603592044000f01605e10441100007414000300c1010204041c800400210210000444030003621358a038a10035000c0c1d0008001182c11410290482c501814050b000d440524402480307030007600e00e488800d800030004412440c0c001e0303005041d001098117901e8024140b600000b9418468035941140403520040140101c01c48840304805440360f800c1c1c061720302168508042e1a06507642001d45860322800182c4048a404950ba0603035003000c0d0041c20f03204c2c03000008506001000c000407c1904010740c00c41000c40c0d04c25000c440703605a407095024200c4c06420790030070401890f1450003680798800d0740910b07046401001a2180f00188100b1102079500008088001c292101e04108240c5000d0140c40e00b64490a140981501e206540060071060100820342c400d546c0140d6181c2551116442144003107a0403c08000003000c00170520b101d90024481c00d0a0307845402d000480d078450441c0070714011001074008125590134120740c1032104805180d01c41e042413a4402e0b00d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840227913 1250 840226663 840226669
    0x4060330211d01140a02030106020c1c0f060c09140a030222050a060609060e01080712090f08030402030105060d17090409060f0501051003090503030a090206131d0703050106020a140c 80
    0x504040310703a2000009810160004403019604d0080807200824414401001080d4010915400109040303c81c001c0221002d00040f942114000c0b0182c00a000b6500c0318041041503403154400b204607032224082682d030313034141c1c3c04a0643e42c42c41a0300102ca040c400c200508281d01043c0c0743e1850710400710300044100c1c02d008120780c0100c0706d95003059150304e001c0080e550804031102c09802c80e49086620308009400103801c141c00a0b100204000e00403081d565420080d5200380b0019034080060700000c000703818031844a81058030260301c2540381801181e81d901c2e11913010100641d0001040f1203048004441d6800c07a040f801e11280c0060300c850308040010300300d2040c41841013401030700080d194145814001d800c0d12001030882810f2503c60500007045000090321fa0101031f0200c00310300601540b0214072203005d1117080f96408880d6100100b4452032140c41c0035408101c1441005031507035070080c00c030241c0360280b0032000075802c405200c0010400028038010079103440c004940e0012100004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840229163 1250 840227913 840227951
    0x2060a0314070c0c2c15030d0201050907050604030f081c05070c0b1b0d0b040f020a09030b090111030109050709080601080c2d01110703020406033021 66
    0x12400120071001480400030303403440c820064a0804c8400200094184060a03000c500c00c0403528400345c0c080005e0f2030f0880c0045c40c034051740c5004d0140c4070148904000603010b0034081e01d1031002d82c01039480200c2c85081039010340341102e80080041c0560400380e1103e095581c0001c11044c1d00d400360101800d0340c030764a8010180a04440d0b0380e605c03019001401c040c04c0c020000303404420011189024207418030580300943c1c40941e414a0300103190444080050028000040171010503400420541129900a04170703408490142801401c10381c1e036a08c0150881c1e580d500740d2200c110060005211544659000552006c280d003030254209441d1031040b03180010907404143c0e954410547c5840c2ca04091101e4896441161450102001f00600e01c504500c160320340e00f81084081c50729450402820000403000756005802044510303228240280c0e011121541000e821000050007158504100980c4508a103241d40d502c039480b00383c40b082840c1001301865444560f031901d040400351946aa8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840230413 1250 840229163 840229171
    0x60702100207091d011a0307060f020304030f0302070f08190b0a0209030610090c1704030503091507080a11070218100801230117070312110a11091003020d02060a0314 73
    0x15041d44c481c080d804485007034400200b100001069158402012520009031801c10303200d242c1480f01c0130070300071030301241b65001e250f20181c02c0707195180140c024507401280c0da00030389884a040c80304541d105c1c0c0003155140200c0048a0142032955080c5020600ba0001c0d541c0001c94900d01514000c02003000924002d0f003519a144000080d90701004100c0082c46103ca201c0f056090048000c140d400310507880b030600070006418003400000040c5a146c09014600d194040c108a4580501300040000c03d200c1c802ca8184c1c5915247c14180d03109000c864041d15115030380206898175001c0311041c8402e0001000d0407442c803d210b524408031f0070003003c0c001c46190340c0d4281c10380700072141800105403c0c0e40d0103034413200c0030103c003080100e4102030200c0c100d8281d90704003400d0080c9100d224012142c170000b40450000500400c08140f00704002c003c1f00100b6040c2c1201c0302001516000c00100c1c0580c46884004d42c4501104101d100604055019000010f038a0400082c9003050700c8002c1c0a0300030444d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840231663 1250 840230413 840230441
    0x15023007050c1c020604030605071404030b1e0405031606060b0a0c02191a09180f0a0f0b01050a031e150e07090b030f0402030133080c06070210020709 66
    0x781d041d81e01d8201440c02214642d2040104440004240c005c550144035502000d000e403512a000031f080203000301b40140c1d4a404040034281d03216170b07070b05200580f9541a030310104c10f90b0403101c030007407400000b00f145c6019a800c0740c007440ca4401064803090b00c40c42e40310400c603011a121800054107140301000380c8040807031515807400880c0705104000c41d0381d44080503d1491102880c092183d03c0c81c94042008101100c140d403552158a100021000e600c00107202c000301e0461410007021108501d1564001d4001050905c07807034411003240003e5404116509000032418080e210401d031094104091910300d403600861230b0540003101209407250070b40d03986407042500380108254444007400d240c0c4800a45010180300b41004150b0100e48009842c031410b24283d1408501556000c0d031040d03c0030305c402000b14041d000c40001c46070b05580800700302c406120581030001003902000c2610702226000401940c60103c60398200040380040712605000c41c4510800424500314620801000c241d03a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840232913 1250 840231663 840231673
    0xa0602100e0a050a0201050a18030c0503060a0c0f05090621180303010b031503100603050c12010b090609220807060c031a10051c0c091502300705 64
    0x144011006441065648141d56800420302c82c021841c00701e50329462942c2440c1030740d0380c0d003604102141d00b80c0000d00300003030405c260040003007040a125070007402c58030281d06039081581d91900752021030713500c0603500c00401e19213400303414418409d00050071300b5100140000d04042080a02c4d07030036000d100141c18440c0d04114144182e04455114403e401c089580065146604200b0f1907100d030b000141c8451000020300300041c01940d001d0004050002003188200b04040c2c1c0d0f82801c2da82c42e4407940d22540035172250a00d07902401c006009115241c10081c00d158030b6074440f003040c0086200d0043c0203001e000344500c9072445103900325004c844018066902780f03480e6005800c00e10112441710f000e51060610300126001540750304080b1800d1001d081f9480c4051090b4084161189d100e48250031443e0944010154503e0704103074000c080f020880d1b9284802e183c3c0303a8850ba030740995a44c84250150340003500c2c1032040e400e07aa40e41040300d0300c0410400940c00d010381744070000fa04466400c030391903000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840234163 1250 840232913 840232933
    0xc0a021213030308160519030b060d06140a0b03041209121115030f06130608030f04090c0207320a06030e1015090b030c060310080c06090105180f0a0602 67
    0x80131901c190010b1900021000303d82c80c050004d029031080c0355001411406005250407900d0183e03028588074000644a142e0f07400c28181e03040c0040c42d4600500303080c0c07801c3e03008442141c100890010290303250707100580e02d19241d50f150404404120341c400c03030802c100700c4404502402c48000120301130748580d8144020415605c204807015480010301198800c0038405c0001c0c06165034440c54101e8000ea4281060015007070f0858013901c816000926030381301c0040c21a000c0113141c0020021601281e10170001d1011800041762511443e10862468107889180c0c0d803220381d850302d076400c1c2160b40c2d40e8040440c03048900128611445076481800030964500040e02500790510050580e075014010070840800705000079011041c90b401280c10082d9102c202d15101e8404014100c004c0d48002c025036141e141603010403c1c0304c840b5024072062801044500b160604060041c0c0e401c0150507100c09090820240f031105d0940e401c4440c1c241c1c0549030349011011a160722910300003408083c1e002d0890052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840235413 1250 840234163 840234167
    0x20c0304090b0607060e1b01030516050307180605180d0203030403380f090109081b070b0f0a1b0f020616020d03020115080f2d070e04290c0a0212130303 67
    0x251147da41e06160510080080000401c0d00790300d0210007030304005403261181541290401901c1c80b90884405401001168403a0804042c01c41d000170692007851000f01745040c00740310142040002e416600501c01840082c800d4030420440c01c03480140242d102105101034598524450852a0004540f50a100c111006c400700d0550003007000000b032000010940c0c50138882d01c603451240e21881201044600700701d00c14040c00004100340d09000d0b441c1ca9480c40c08548036840030000c00301152078121013113078401c100301550350400c3c3c10030164800070905800b130107140c2d40070b60703c000e03e085000303c0b918005a56417204041180c1c0294000611000031085164030703000f45420550305984003001c400340308940042d240140310482482051545901490828030b251040b054601c580103001000c20b40d54000f000440c4140c0c002c10064080c442d903c944d4030a118802151181c4510030a00090f80178800304005001d041080e01c100d4002c0ea07a40e1224803000c0c0c000304540e9064000c80c50082052507 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840236663 1250 840235413 840235453
    0xd140a0f02130216110111060115030c02070f0b07021302030a064b030f08071115070f080d1401080607020f2a0915030d0201020c0304090b0607060e 65
    0x2031041281149400c010151103410025482c00040c039030b070140e0800c081a40d00c1f50413103031340c10701c00e10f400c48034176503114080404143c030000c2c09040000d241c0700020186a00c001058021503283c030000084c2642401201c050990107aa0240c0e042010030510f0f02201d4540e1006500c647c0d04075200040090038621086000c0400c0c03840055528101122102c01505450110044107000e0b12406e07880c14104c129407414505980c07002d401282200304001c2440f40e90401011042e02c190b03181000c1c89105410406104088001c5030401c3c0d50a12890000a200003440300c0d0050203407400e03a04100703414400d8410388010f2050062030054803001000800001c0120680000140c00548101c0307500c8183e10f03030380d201d00340c0758142c0d40c513500b0303da00c3e001d000350340072510624202608498081c1341c000003281003c610800c507513000f031082600c400d014074410310980e154070102c40c0155181503d821800d6000d0700001c0c0c4804d610076410004080003904900c99a50881c00d000040c04c0c0c0480541c14040e811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840237913 1250 840236663 840236689
    0xc02011106060616051011030a0b04050103080306010c030210060609030b09030301030b06100c080f0a0810030507090b010302091314100821071b08071a090d140a0f02 73
    0x303644800144112603403914141d4503485600c20b1101c0c1d00b030700d03541841c038030b001c5070140c55030700342441d01d1071010800c0b9940b002107110302ea22a906104401940c410321040340d1003440007500c100b40030300100d501ca42c072804000c14030502a10460300103481c00741e07940041b0b0300c50750300807808104160002c10400001d010b0f180d9000b003040d000b8504640c03440c0c8070880c8142c0c0c01021a84114140d82c0415500e50042141130510384d00050941e8495810fa2107134001c95204968080205990703100184070441d40340b000310142d99000020b060014a48954000a809080602410b2507003e1081003056150a142d03401c0b28540a04081080164070f0050045103501070041101d11009031400c0c840c0320400201009804411840b03d19000f10f956601d000034062900000c000c4030100485910b01520b00d4189025a803105099500e42c540e0b03400c0705d030355402c03116000103018030050092581c02d140840115a0b081d019030351461100807417118441c00d01c03071044811201076920341e922000754201944050f140c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840239163 1250 840237913 840237947
    0x909100c0212030a0b12060a0b18060f01111e0102040e010b04060c03080606041d01080105012c090c0607032d020a020409060e0f03190207260a120c0201 67
    0x2d490001403002c01c2d2100601014005032648620581915051030b0707040c00111030f00c10789065080448511001d0f18920b11000c0c07081500c1034000202682c4142d07158000c1c0780040c04a29842e04040054030b001280c0c0c151412680100e1280800400284802c913000050318000141d8950401c101d000007100103800c00400c108080c4000c0c000c09800050000c0425010706040d107203540d80d00c0009086214641043c18118520130701f2055032800b141129043c2d401c1300009000c0c907030302c4046052602c2c1d003540c0044030050720401120740c005d140f400080e03040300488080c5c40841c400c44020440c1940420300807000102c3c546240d04550f500c00d0301c175848413003251040c1c94107582c40702002540c51002a0010344280d5485414004001c49544651400c0d608001a181c6880800c4032803501c2c1d0b00103504600b034090b030111909405600c04030350001500d45000c0c62542d00781c6075062540140c002580310398040c0c03040300c01541c04035407584074808400129a9540b0406107561000500350103001c901002 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840240413 1250 840239163 840239173
    0xc030609010b0904260d020a0f14041206060e090a0c08030405010903080901030f06090b0f040203010b12222d03050315010c12030b270609040f020909100c02 69
    0x1d0aa941e401550303400613000b82a07940205c000707400000503ca00040c2403141090005052446242550098001e1100548818004440c9604240d03109004481e5a10344500104030a000002c00c40030300c071101c01d010740c000151b001d40725540c1440f01803007070b0792881d0715902c00b01c001d408020800d800c1c400602030102c003540c24a0301c1c20300080d0100c00f803404014a2400080b800010b540d1080d80401344414142c80309000386a9a655071b107005140486004d40a0740d40500612002e00b024022641224840c01c80300d4540000d0340980310344408050b024006020350b00a45c050782452036415012468001e03001002c410b144400d07603c4081085018607a41a00340480d20300102e82c000080c0c990021280322040e1b20003107c1c5004030354058000600070031001074111203030325055041d4040400c0100550760741100400c1e140300005070b911090308441d0610b580e40300048076414005901034005106446814045095038001440c9441c00c603000655903001200e0740390311888502502501c0401400640 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840241663 1250 840240413 840240431
    0x150c050d1101090b040803011e140d030903080708040e010e040c031e17030a0b060408060a0c051204240212040f0c1505040602151e0a02040510020c03060901 69
    0x65164040300c08540c0500c180041081d290220a42050b00b016920400d624454589803070b008005030000e0045005440004e01c907480d0031802040651f003524030800d03601d801d070721043d4200f1414007250b2400303d00704901c203103000001038200b030098840280f0616804e41c0722410b040b900b030450759050313200f0090410f01070700388400300e9000c03400309081e40e400c0354440103060300021301804401180f01c0c0c020300c00128800104807280e511000345004044401040c04040391820070852180118002c2c03416980000d008150b140c82c45601039aa000c10a0400074113044482d24070b0766101000b143c0c281c40d07840044c050b1ba581e40d24500807000c2c0c2c2240f43c91085040c004006042c070140400100002d024041c0c1c1105c03101800802030410b0000c0c0a007080303204894415200040181d0424070860380540300d4001e0385801b81c0100010580b180300c0035a01084001c148641c8806944406000800900d5007007001140645940050000300344040e0001d001b4108500305040c81d158001b095030039140d15040c0a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840242913 1250 840241663 840241673
    0xa030f090807060504050102041a0c0c10050417010603080a05030405060604231803030106110d0816050310050a0f17030301080a15060e1303020d170c0a090306050c04150c 75
    0x780b80c0c1d0380e070032600005040d91107240460081c0310304e82100c03004965035003003a04028003e00081c4000c2d5611000d6548414603101070080300a0001901c9012803420312060000d43c01c60740a09219484060021540a0b42c0c0d447c3e80d60340c1d5203c08819800134400004000511804001d190b400110a85c1c0400103251400020440e9081c080d4040248082c0da102140142d5021810420181c802c103055070b54035651080043c2c03a04440c0200842c44e4000c552041035500c1c01108414420140c0369503142c021b00c10024112002d500041c120b248507031060602040700c0d00c440382d00300d0241200c180c101482c542001c0e280440907050b0003034070b4510f510410040c00001000b140000045500120104116086140580c064140ca401c0035001459290400441e1044102444525402074081e01d412202e000350846242001600f8a45100010808541c844016000904c040019458000310980d240d513241c1c1c2c02c1d50000c0d5201a01041c012805000089014003a40c0000c4041d040c45502d1581c0e80c4c1d12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840244163 1250 840242913 840242917
    0x90c02070602120904090b2703091f021c1d03030f0a03090c0e0408120601180509091f0203180d0905060706020405060a1116081914120a030f0908 64
    0x41c091100300d01081d040419200c3d6000711183d240c0c04000b44039145400f914a20403144420028203448c000104048446030020080b1114600c000c2c11500384040c1541035055084481d00700c000031031207650107144688855081d85680366603996125449102c1a4000783c000a823a45e5802d4071940040200d2914100b000080722250030242c280492421a6401c02c90401c840e10350088509136804802c000402000301c000b01200076240c1809400b0f41c8071017004440705010745c1a0009009070440c42405507203003101e00194801041011a042c00c0c6607400038062060309007450110068007c0240914010554120300720150240c0040000c0345080000424000c850f100f598001d12000079840107000840d01210043c10380075095583c0c1e054010002016084800c3c44043d40d40a040790a80b0500040e2022000329160000104a81624410070111003034030110100d80302a100140d19180c60800d01440c13000501c651a03542c0c03140c12044016095441010402c1c00d91450314020000060079041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840245413 1250 840244163 840244183
    0x60307080f0a151d1f0e0c01031109040614150c031603090f1202090105090c04090209060d110d060801050f15040905010f020c0115211119090c02070602 67
    0x401038a0041c09070010001400041c060003100e4034200300388201100c00042814958414102c0d01c1c000d0b80700c1c941038500702c0702510900e80c6c0716004030205100c55071098000000d00d0148920652403c0c01d080002012100c803a0f019564407410402c2500d418a02050369401120b03452504506e01032180160948034481d0824213000280c00642500070706106001e031002402510100040d8207803100d41c0181032082c0e03500102d00c52600c0310000300e2070b410445c1c1064001c1046650741c90415041050100194004d14140f40d0440400d01c00d07200002c2c01c0d4000c40c000d080481013070507174640840d07c0c1e003c01c0d02e880ba001100d46030b05020a2101c4078000810780360348441c880c4081c074074600402e030000d40603102002020b00341703600f084400308036100164000c090401145008000c000030014080341c1c2d50005200b651516091469000458091208840d034114800c840800c0103140c5a80081d104107502c5107007400d03c198486043c0100702081c07040024049590008000d01841e2202c02550390740c1080b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840246663 1250 840245413 840245423
    0x5010815071412040c05121f02180a120302060a0606140d021306031a0904050312100906060507110103150b0c01060803031801180305070b06011412060307080f0a 71
    0x4941840c0c030b0702c0c010003698003114a03001c44035603508060805a1811304580201c0b4410040c4500c00754280b070000820318049051541d81c180001c4480000d10000d400001303041004040000b018600ca95035030410201500c81802c018003508018100240b0700705004118466040c03411308103010b91600240704032480a001c1c0c4200d41d40d0380d804040b4001034040d98410484040713030120007003001a01504400c1124009156400c0903a00c01c0c0108401e481c804e40e006040e0f6002003054011a012903443c00d64403154015109000d035035100071040c01c445880e4400c0c40043c078081041000c0060a504061900e0070918007445200d1001d42015401300d5144030f0603070b201d14001008100031030203422940007404503106407901c2e4546200b05000b844030602441c0880e5184c0303d184142c40604d064039a01c8640c0666413242003c00c540d5510080c2c0e14061300d440d044c0000f4800b660300098101004082d00a000240220726007012001c3c10300c0c1411070340014001c2e0704005941441c050002900e40034594200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840247913 1250 840246663 840246677
    0xa0633050904140d030b0102061b0315030a02091003020a050409020f01030515030d050319020a0516050309060a0c060b06090d151b0206240f12070906080a0203010501081507 76
    0xa49407640c519140c0b0034030303c03105000700c5455603081505580090050b02c4207070251400755031940c0d84d080d00691255804060b00500f440403d010004d0482c2203081c4c01800b0f4221450002c1c07039000203052a0040307070741e0320039401d52101c18411400d00b10407034001040e05490a001e001210f07400070b000e0801801d80ea80c10140d44600188685a00c0341c0030102d84a00074060304c1c00c20b4201500203000d07a0080740c4c04020301c483c1c00b50294040c5000d1085510b115a150744507801c2c16400ca00303c0e40884e60b0440c0070317a118441480a000d080d5138000003400a4913854440342c03090200d519100b41660800d50000c2e10130313082480541815143c90b81007d203450350160032146005611700c0e0300f000910f000e8018070352041b040706041168a400060b5603005000e084000d001920403080214070b0010884070050b049081e11101f00c0203401d0019019120340449425503414907180d50340c072021900d00703602c41e80b00d55110300c403a01c00350b040c2031081601402405001e060035040b8000504030001b000b401d900100b00d99 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840249163 1250 840247913 840247921
    0x8010207020a0e13061e15050a120f06020a0503150306070504180e0a030c0212010504030f05071e050c010f031802060901050f0d0603060e0309130b120a06330509 71
    0x304000b02c40d107460303101c81c04001843c1e4450a1131091031b102c5694001d0b0600c0c080d1030a1500040d01080000c540d802068480301c1801c0000380307222010315442c1224200000010b1030005441400a8040328010740e4810703840303203081303030f00b1513503d030b544030701c594025007082c0144908954488111810350350030070701581c40d00b901a425a0010082030030010b0700340c0141000d19040643c0300f500c100145000302d44600c108201006110708950f0203030340080100364001941c6500c41d0280003d41a128040c0000990b07194103168408000455200c2c12a6243c010035010700941da0085100c0d01041010701d410080b8510340803c1d007008102c4e41c24040c0c407920021500141680c491001c9610030b01c0100055600c0d0303102045a2000741c0b02c42d010890f81d07142400c0141d01030380c500000f91100f5000003000e030101c0b0103060807100003e24410069640010307480080e4258500200040440c1511a020002e001001c01e01d480b082402300441190440260211503084c00c1c0000c070b01002603032000c13105000c0caa15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840250413 1250 840249163 840249181
    0xe090a1a0f1507150b0303040b0a0c0f05061618080a02190b221a09210d0206160e0102070b0319090b15040c1d120304030c0f08010207020a0e 62
    0x440030440032100e00010f0a9800c0142400c1d481c0d4000105100510400c6451010183c50f80121f0082c848114002c0c080e03001c0c03551185010b1004c0500501d001200c15019072034180c01c2c61300840301c80940070042050f4141c016440700044080d8000551900d101d103003403404640d00e890140101a2060030302036906070100800c400310800800d0034900540d5103115554814400108050421400040b100000564441284180c00a800141c036103241740841c4541005809544803145410002c06452000380d604410000d99892400d140c0060949140c10920b4400b0401c642d1780e000204141c0601e106401c0c2d800050000580b409201001e4980d40c4c0c400300c503103000103d858030840300d60502c04040c1c180140b01c08a41d00951010604d000e021505c1024401944d0b4441d1416001031080f60324081ea00500805001c10380760001d1886002081040c0c0c114990b4104ea041681c0c1ca40e240001001820b00d4407401c2001060080300039420443c4513000920002010b01c10311030707901e5034000001e10040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840251663 1250 840250413 840250429
    0xf03190c08030313060b01020316030309050c060d1e0605100f11030a03090519021e120d0504170c011e030f0c080109060f03120507050f06070e090a1a0f 67
    0x800c40450343c82c0d107071a6002c480d00f8403448005a592030728103021407285502c007104845600380d045401d03483c400c405680072001801101400d0b0361a005116210045566080003072581604010700452801041c7c141040c0b001003540b062020703286401c03000c0020340c032060208080c507000340c242000000d4103800c00b80c03074913134440c0200001d5010009440705000e4044e401929601d001d42d0449003030004682615104c8065a60060742c00141e1904446107501500c1c5102071107030010740401c2c066000c0750300052410514804620214030f020900340024508244d00c2851f20030030b00001c0504480101c0081e054080000b1806941602211031001c0240690002d08110000c400e04102d03030340750301d40300030301c080800e0041d00341c2c980c20070000103046d4600e2048002601d4100f040c5552070072810344140d940303511001c0100d80034000c988000e1110070052101c0e43c8101d44a841d6041070301d140c0000c00c8011440107202440007072512081c2020701c0c0c000e4100345088130069070081e8521100c030700020020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840252913 1250 840251663 840251669
    0x120503040309171f0212190b0d080304050d081509040f05030d0914030414040f0612140c040c02100b01020c0424050109060c060b0a090204061d0f03190c 67
    0x2a85810f101c0e4a00080014403000041074200301125003a41025016050744a10440b00e503103070511201040d0060b08500c8070b4101ca030b000500000c0c0480703e204c00b00d005500c82c143d098400010220410082c4201805050410303a0940741541c207900d811090040704441d1148400c0c060412200014100801e103000c0c0884150031a080300d485100c140e01c04000303001c90100c125030041450110b002060030003c02c1d031741618104110401e9000e505000e120050800c11a01180c041c1c4944001801610038407246071024060207e60007040c030b0750780f0090b1500c06103c4016008034034003444295110350200e1034002625140b200482c0c1e48002e80f004038a80403011a84a500c10310b060312111407404440140ca0707942040c0e07440003102560b1003006507010302442c401c9402207181507102000140d00c55100704103900b402441140280c0c1c0340c0390f81c0400c03a0003c0e00850045841d541c04c2c1000003c1d403c6180c054400c0072111748280580c4500425142c0e0790740560040384821550104040108941014001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840254163 1250 840252913 840252929
    0x31308030901051e06010e0d110a060207030c08060714070515090c1813080f070c0303050a2309100c08190801060f0e0f0105160b0105040b0409120503040309 69
    0xc0741005a45036009007010707600700c074444070b200d4400d100419100030124810681615043d4407400550180407040c800b8040851b2580c8064801c03810700e64444940901074006940103040e0036003149000b0110013095002252154070403010840720741e80c03180c80e41c4400c2e00300c3d030310302900d65840345012031500c0740981e01c60501e040b588c0100454054009040e40b0018000c5802124030114281e05a2080070144e03040b82c0341e0310581c1800c001091a95005044a0460316040c40c0303003a0f011340380c2607640c18403500f0840001e980024050700b01980440c0fa040707031010500071444440c58a48404403640f00c2e02940c1c074001c15800013410700031409a00769003000d81e0400142a50740a580000103441d0780000b2444021842140000c525544114175900d4441d0301611030180000100303041004981c0501c0c19241044030400500c055200300745130161259210b8032600c0620b50425040105650000e00c1e61802103190198000c04910840d03a201c865a4283c10119601c4d1180e007001c440840e4a60481d0300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840255413 1250 840254163 840254167
    0x15010c0b0f100617040f0c080607030204151b0204050a09060203090d091517271e01150b03070306080a0b040b0604090320030c0f07031a0402030a0602031308 69
    0x740421a040e442d119010340b070b050504654440c00c0650720a1200c101a9400c1064640000e000aa10010200e00b8031b000ea102040f0043e510002d15141c04412140034002070380100d0104100e81801e40005000101414420386001800080768114000004080d01c5140c845000c07441c0071856510403180c7e03e0b0044800c1d0364918084030910f1786e403168000c41000048000d1300c001082c100750700c040042003416540b04424210b00d461406c101000103440d80c440040340c00f481d8000019094160610050a03001138280d038108074a1100c8030806210917561140d040c680892000404100c000042d20112070b03020b5125265000b00303c0c0104069002103403540300d00c100d0b03981802844010640306500c5210064459903e84061000303440d010b40c3e0080c042400e14000d030080501e01484082807205a20840342402d503001d00e040e24080e0380c890509026002541c0c18810b0114603440b0045c00e501006007000181002e13400300b552150840c1014003016404004101c0300016410703104001604084016 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840256663 1250 840255413 840255421
    0x408032109060a092103021c0b01141e07050607230f030a0902120609160509150f0a2709080910030603020402040308031e04170d090209130b010602031215010c0b 71
    0x3e0001c1d4000c0905202348407501c5d041c03018440c66401080a80b2038180d440c810712441d071000e246c8258000c90700003e19880203d040307038031812030803010f0074910340540001d242900b4984400350490f24050380071404114004288081a420042140d6150406130b070403654965a0703004400060004d094002d51000718030082a2032840000344081c00740125405942c0b01c20319046d1506422070079481500d030480000c0c4001040140b14a01d25000090041d0802c1803180440000420115007a0811140c0c10014400040c0601403107841c0351080054410800141002c0d807503601c101d0003070700f041511810310b00d139030030f405148250070040c011680600155100d41d01c07490204443c2d002100d42c00e44500e1034520202c10441d1a030301c0d00d0302a54015081c68401d215003080440341e5403000c6607040c0040d4540ca01c07580141c9078000d42522a1004c10840c0e02924054030340025a0007041c2d0100045500034002e40707004c0c403441c2554a410581030070715410610461801130b225120b00c4da001801c2440110700700 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840257913 1250 840256663 840256667
    0x703020a0311070807090506030c04090b01141921120203120903070f121b05030d0e070303020619090615050301110a08010b0f0403080408032109060a0921 68
    0x4040d40c51090b00d070240c1c0032541d14040b07a500c3d4600c0c4240907045e40000d208202a00c201d80c00560440d0b4040c054460040c3d80c0307000f0a06651082c03108486821101c4010048144610040054400c0031903060803050000800316000032082e0140f056161131b48503003203080f105403d0340100000ea101d660800340110030040030752a600301c2d034400f0140c00f0740080000e0707110f00044111640f00390b01091160140880307484107800070200307100c00780510606003100e02c15042224502ea001031300c14030046036240c405407146016243c102900b40c049034003660f4107000003900407401580c0708080400000000449143c4140a0000110060107d0385000c0302d1002c00d0350f00c00c04581c10b4038010380080c00342c68542d540b00c09030340c41600c26843c00990b4003c0180300d847d1042000345903c0328210f5030f003800d0030b8aa4075413142070b5100d6803180303d41743e100090a9111802180301d4826107a03154815000c07618000c030600f9184d1000610a01105030388402c08410008184d0038100d054a90941405591441d5040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840259163 1250 840257913 840257923
    0x403060b06070203061602030c0f010603060605010c0812040302010b120d020708060c0a230408030706110a14030601090806011d0c0901050f1606020703080a0c08070509012003070302 80
    0x25100241018081000307800e150302102c080310703030140080c0030656881c10b024005601601c2c884d0704502040000d900036540800c840700000140703200024034946075180c40c600301c0e5000c2d44924140b1809611840c0854121001e54034207007a80c0915140da55668a801ca0041401c41c051070b078007800a90443c4042d41000481014007401c1d5021030381c003135842d03001c05655020111480d0780142400c11070584400e120386002007940c0d100c089c038030034514040c05000f6240c1c0c00c6031300150090707440400d440b400e10440d0302031000880620f0f05001d20300b0000307040051131020300d00710728804000004041a41a4401d0030400000c207940c10545545584aa185c00d518211031100585a40101b03000b140070121028115032680c40305850301450060341501d0313070360580c01084d10b1804403486040020041a158001060303c01d00c01c3d40c52207030078646286400120707107000094408201000301040041c03034100c0c0440b00c20074400d00300081461030800461510018101c2c00000c503000c0403a04804068000607 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840260413 1250 840259163 840259169
    0x160b01030b18060f07140c0f031e0a050301060c0201050702041d151003030c05070b12070f02060403120b0d02060f0a0e09041e03030e0303090d030536010209031204 72
    0x205001c1044905540c2540d03c03a01600c480000b0980380c008200100c2c02080411742906c040c00005041048401c2c601c0e04002400603800c3c41038100040c00d410300c4c0d408008945080720000301e010b09014941130018040d01050181c00c05000c140400d50342075a005d08103803000994002e02c148981d03070f038080508802d900d5200014000d4402c1050400081915071002c4d0721440a903861080440d1564500f200c400c10078040c15141e5014684011070820030b40310060040150200b5402c0075030521080c001e02400c0c00e4501c2500710b4010308140320000ea4031110100d4160100398022071259086c0000031301c80b40310320714003c1d8004800a11202001082c101134042d0114548038854240000002d0220002c000c171002020b810204070103c8040d080800c1c01500103010345000900c440d0400300e02c03403440e0b20a0700d98280951100c40100350803541401225401a46940c1c004038040000a104007500d202841314902a6603621416041801c01d505a45005034010101d075807a004d640f889a0240c0d000d80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840261663 1250 840260413 840260431
    0x316030e121c08060f1c170a020d0801060504030302300d0b09090601050a1a310b0a0c0602071509201507060207061409012a050a05160b01030b 63
    0x48002103041c82c0072100c5c11954040a004100b8400c1c03070300b12a0b0803c020303060049502c80020090302039003204030700140410b00419001840200e14005000d008854140c1c01502048804c000500000354042031821300240340d030545202d254810b5409400304040c1a51881801201007505c0f00300800c603030042c1420039015500b8000715241c0e090f040d9213845003401103a40049110404000012240d90300c5010101415100da00f4030000140004406414003000c140e007075100d54144a5001c00d600410000348510001c162404402903000b800c82810641e0203400c01c2c0e4041028014011070303960031800000c03405410004c1c10001d10b850304224040343d0000301850103e4064481c1400e00c80cac0148107031090203000500305900e540c1d889000e94040f9000b02c4000361160042d00d410104040064003848104c000841c1c900d4581420001c0c82c00c445d40e9148140c246020603c076080c3d04201225024412490810354039600380e40d000f5001d450000004003018492000001402800741286000303558035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840262913 1250 840261663 840261677
    0x120706030b0a0303020a0308070c021806010f030501030c141818071401050702040509012910090317031e10140306060a0905090f03071101030b030316030e121c 70
    0x1404401c410b2400000c015034030600500740820700400095034000143d01c0c3c031140c034858a6001c2105042038804c03203c0600741820074800c2c81d40c0c20404981c10358413580f9040003a50f24581f11482b10350000e01c20100d40d120740254000040d00c804400703102c91008001042014100380003447e80f5603c09a1104c1402d01400b0004118000d031004080c00c40101607594600f020b440d6000c2200511018000071072944d40d42207101009041101e20280e0b519141034540d4130b400080c828850b64031408000c0504202d0038507000e100041380c6902180001428005032a01c4e503450300341d01d141c04500028083c00300c00c044020404080c100c04d81c0d613819180c111911034254080c90042c580d4a4200356405540b02031215014002d103002d950100c0c5e40080240103e48548100106403801c5920200013954500c8a120303081c030655030140030341c800c04403040d40154a0881c81c020385407078550300035100504008156282040660718019440030710340c00b207001d4401e00700b031018000c000700c0c0c3d140302214046900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840264163 1250 840262913 840262931
    0x40f23010510080106030213120b040b13020a120c050316030c170607030f0f1505031e03030f090c120109030f08070504050402030a1d03031504051905130212070603 72
    0x100c2204003007a0455210f600041c2d0030410194017a400400c5040303003680c1c5030039001445242d86ca10151000380280261481410582800c04100b4001881d54680c4407103000024010f1312120812030032a00c4841d614070382d11202c1e24100c0092a403d504c01c99061040c41e104038881e0381e010702803008591080358a001030556940c03c00e815110b40c0c0c0040b103034940104001445040c02500036070880ca00c2d01e0000543e0341351120517103045960564241d80018206003042c00b00e03050806c21300c868203100e19182e01d02030f100d00c5041070790703884020081d41c441c240080208110000400c00144241001403c6404401710402004c4c0200710700e100c2940021060f00d0414512070280c01c10600550080d643d480c505030405007407101075400036111154880c2e50308481c0e8640d0b4210785002c0781e00451381c030165660303083c886c1130700b2490910301c0c410905c220b06e08001e10422000c4121080c185c66065400883c2641e644007401d00c0e180b440c41c0780a074001581d2111080b0180000c45d491041c0c0da061b850411100709 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840265413 1250 840264163 840264169
    0x12020606010f0905090a0e0d050901030b042706020d09030305070f11071203020f010e01021209030306010c020d080c01090b0907060c0507140a230103050718090b040f230105 76
    0xc1038180004250400d105021504110171420340c010f410800110345542c0144125181101901052000a00100303400100d503a00d4000c0c0002c00314222001e100c001224200c0140504c046a480c44503003899130b000320100900e60301502c1c0400a40401000111100d090180141c001100da41c0b00240165410324081800303060086051545000208541c46c1004000360541414000681c150300c65204660540c0c18240514101000100d0000d40c0350780130b00300e0003031403688081c10000c06900305008000d81030341d202c5442c103055a01282c401212582605020b280382c491990f07520032079403c01c125081030040e984e603418010300d004011a261140c0c0c54408842680c1554002450b0381c00c5404100131603c188407404400d00d100828074501c0070b035200104040c1d03d06a4a1a284554a0b00d80c1d5461942e00f41c4030b00380c0d020600e0700f8a00d00880f914010f610040a881c000c08201d240d6071011946d19450f41c0c0c2c480689010b50910402407461176070803600f40c58841c00018a8002440b10001c11241 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840266663 1250 840265413 840265427
    0xb011e05040e060105010f180b090a081b22090c030215070b0c070204110a09300f081b0705040f0e0a0618022116060c0f0c0f031202060601 61
    0x540c1c00009000f02e41d09010045900901c0130062204101703030102d4031042540426003100051a11804540d0344080d0300c0240a0354011946c40444107801070401c4515800701039000041004007280d0750f80c281c002d5440f1410524002c003440c000d1043c43d1248034010084562101c80035a40210380340901c100d90094540c0051140c0c110040c0079180540128840c007001101a20140e40b0040c400300300c40500503a0000e5903040749020900080c2469020800c01c5541e16103031700000440c4040011003902101c8800d00fa41e2402c0000b882010340d44410700c01e00c40f82009580c07101d92583c00d842c00c000c1141109543d10100f9004042c07096141201000710310003544603070304801d000e210103802800400c0e00d42e1401003251801d605402008000008016035139240310380c48052454200004002c1e0144032646850b8291541c46a901138080f01404440e07000800742a00551103a00007200100510b000c420440e80c0b68802c1c0001d0031031035004001c00412160040b03d14035681d003114034559a0000441d800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840267913 1250 840266663 840266681
    0x708190201021b19080d0605040c170a090b01061107080f0a0507122d05060403051206010c05060a0f020c1c0f0305010e04020108060d0b07030e211204020109030b011e0504 75
    0xc13041000c1001c001102000500025440c41c02c00045065407400801c066841281c40c240029644440c0e501031642d00205450f01715440820401a003d00c640c0c55940c000c0c3c06004110501201100c0448001400c2018101501c03821094552003400c00281507542c0c1004c110485040c002c0b03410108078480803408400c406604601c0f030340c410b140d0040014181d41505501c140c42c5903500903045011503020840c81e8080c42c4030303540303155030760303852003111120301602800c400d040152807184d410100c0c400248250300a83d2000c000a20740300382a0b00600284031310880b1064030300840c0d003082d9075484c805541c264501140e40b90710170f2103010080c0c201d040390740902414106070050030100c0c2c0036511580c0810341c01350003d42010341082c580d884040f03100004030341c0382c400a501c4521083d0100024005030304050468160200c04885404c10f08000e40205002d1003540c1d400100080c09580c41410a50700942e044040518a940c50722040342c290041049200c0008020440010702c90a01d0301c1501b100e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840269163 1250 840267913 840267943
    0x201140603060703090804030b0114041d060720150109060e190b041119020d020f06150d02091e013003050d11040302042f0708190201021b 61
    0x7040d0f40d0524154024a40d03210186c40100c1c050001100240442d00201d0180c450361902034000203803034007044180e03145285081890102004005408040002e02982250450400c5135849080c6040c2d2550740a09584044c16440f907c040b08054850818619040e207190300400e20505455044034030f456401500c541c5c071410b440e00c580303600400c801d500c50041018010000f10b15000c854200d03031542c2c0c10100c03102c030030b5000c046049021590104802200b00b0603d00250403905440c041709030316240024081c08505120803030800e942e64600001d2046168010102600750415070354a4050294442c595108288040c00200390b8807035400020354000320004054032220b048148609914500901c11828840b09212540a541e801d0280c50b40e603034880c49040b6102c6155004200550b14075013407008060005201c01541f03d8070346030072070402489103000309a8070601d610f03001d4000e01c6001580036460540c0300c0c0c001092030b0b064005003200444070ba1081035900c0c84482d1281c48002031600c40d81c1d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840270413 1250 840269163 840269173
    0x1707030605070509042c0705060d1805010203071106060a030b040809012003220b0417100203251d010c0302030c1621020a2d030c060201140603 63
    0x80040c038103800442d8041114502141405100c0c4045400d5803050303111800300001c8a10b01c0405040380300300d00c90154404200400f640d528150100b4154807445440040041e201d0105984000600c0c0d150140580c0c400300840d07883c904100c004254039500420141030740502c1002c10070502d8400d40a1040c0d0ba00400404141d8546a850340b032154000c90440781400b03100011002c2d1030740444c3c4c540040602882c0076540d10540c6070b0380f003000ea0030314400754504011800c8040c018980f42000f643c06070b40c0c840301240103580201c0640b501e08400c281c446001c40b8000020000c882142000c0c010098001d040080d103055503602040d6a000740c5030301001c000841608241c100796110301c2402680030b00a0058038603000400d11464107012006030b8070300e4010260070082200804a40c24024502e2000c0d56402102d0003903030000b400e44180784a0800c4100b8901800c9400742e0048000c401e8400d001d105400072680e0742d14106807010024818400554a80300d0b0181d00c0e04804544140b00e140000c001d48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840271663 1250 840270413 840270419
    0x509090a050403080f13210e030a050304051c141b0d050a02091008160f080712032d0305150f0f060a020a1b0504060603060b181918061707 61
    0x520390240201031010780e550800c0b601c1c001c00c80001070780c80e47c1035455100e40403400ca040e00107080c4410100110b0b0183e440104907070003140d000f0003681e064a500301c4001c149a10391004040d241c2c400000003078217603c240440c012134820001000b20944900c281d0103134882883e0350400c8035414040d800900f1a4100001041c010b141500030a68001d02c40203a5540141d10784155914280140000109020200d107041c81a4151008001c0041021000506132581002c03082d1480c240000c40013414007044c000030001c4030100782003522896013410031441400d000315030006c3c090310081e50914101141380e1482c6201b818800280e80307880034040c04010300007d04038240401544000706500450180b075540000156082c608481011a0440c1044015060030100021076020780c1c070203428980b512108106181c801010b07602c1c0d50005609404212903600b011803d00d003140c6104041c00c0f0302940011070390804820905207452405035042015540344d0491403500080090740c0c071581d6000c14020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840272913 1250 840271663 840271681
    0xa0b0d0504050f010903030b0406080d0c12020106051206060901290d11030f18030414090a0f150e1f0b0a0c02180712140c0702031c0509090a05040308 66
    0x10039003241c03098086030b00702c3e07020014260849001c3c0008030000303900d60a0392000303032600d030042c50050102c903405040000016140940b45041080e001020740541005508056000798403807002031902404000140100a1110342c41c2e6004a9090f44079020310b40001c51828005032140031030421040c5110700b140c40544800d20141c01c00d010024900351039003440d100030700040e40614094140d41802e88032604211096803500700400007400c005900902081094507070304600d005250f83c06455440b1a03407a5010a0b0024010a4a90030078050034000c3c8801038074078005000044821020310800c150b2a90803a0860b0070031441390360306403446007440c140203241a9800414a4441d00c0c100007240861079030100f040001c901495004501c0d04004004101d03400864945064251050410030308000780402d880114016082d00760100c800300e10003045480421000d081454026144441e03818610340082c40c1d0761050031090b0040a400c4c000c03400d003e1403401743c18003566258446040b659501212 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840274163 1250 840272913 840272921
    0xe010f05220507180203071707121a04050903090406091a061b010e0c010e010305130b0903040e0f070905010203030108060606091f080f06220f060e0c0a0e0a0b0d 71
    0xb82d07010f014410b80050604d91020828a550110030000750701c91034100c002800040004007400304070312101040009540c0c0c4510380c0c00030f84440c4c0b880011050060380300aa031400b4409a5950054030300341c140811b448000001d06a24132089900340001601c0d0302c0068103a403460244018041c904c0c41245206160400140502101a154210303e2584070741d00c4509403240c5880100d12500009250482c41d43d000f605000c652a0070300f400d0082e818504400c5502904650020f022441d020300030441c001410300c1110018102030800940b10300300543d0151540c50240e43c200d0100d500c12000242f80e50012050b64101d030181e0000d00810707603510052184580c015008240d02c26040c0102e903106100002041454034400d680d0029585020321314944a41e101030a43ca00c40c100c0141c940070a00341c4008c850351560214000811000030486200000c0e00e081e42040e501c9601820411062100400181400e002c1ca5504e02c00490162000e01c04030b80c2c4c4600a200440c902000803070384164403900 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840275413 1250 840274163 840274231
    0xa0c1101030e0709020d0606110c0108220c0819120302030606040302040204060e01031a03031b0106170a05070f0f03120c0c060e090c090f010f0c12030e010f05 70
    0x402080d03200b0030b151507904003007040d0000480c140d0f000c100b0203042da5452058401400f2207007884541119a912006d5840c15069401810402c6840008a6500681c14038090300c003c0419401300484c1d05150090303010440303000700504e600c00c14800c040400c0b41030300c4400d00241c018000c0345801042000032406544010440c03078100c2002c000000c010b072594401070000385a07030f40d182c514404e060300004007660441d5846654070b00000082c1c8503681d6000c01196008070381c001e1000d48550313a034082c50b400750046900c039031000880c10f50840034119001c5480210b603071044041c1c610345603d80710701041c121075901440062140b82d03901440041d684915640b64502c00d42000680c01c172103943c444080407141e070404170014040400400c05800e0100b041504001104007482c100440356010942c1d0f40300821400d4104040c00309920030140c0943d6010002ca03822840000ca04c0c2102310016010b000d00c500803541f998600003017080185058402e9500078054100e81d0380405a000c4012561203204030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840276663 1250 840275413 840275417
    0x60f0504150905030d020a0510020d060306061202120d140d0905100c110c0f0103240b03161d011412090c0f03060709121529060a0c1101 60
    0x1101141c0364a486080000019096a5002010303050005160500c024180c62005641c0650443c01c00101d002c1840c14030203030a0880141c907140a003401001400b442d07840038164134641000880c2d0030203600b501d004a94005e0f64510588000f0085056485900c0d50001d00055414640d051542d4041001016801001c1002054601160b10b6590a04450414403044d5a41c1e641c442c4003ca90440c88003503d03488203902905d200030703460012502120b0340000311410507070707038102014014010303002d00b4a0010040c144820006d48401c00309916034000c0c1c900b01846d0941107202001c4503c6840400100040840d8103510014140b0054641d96402515505039001c140010b04115420388090f0f03206c1c41501004001188621040c809205c940714200d9010fa0803000030000895008a080811512910403c0c20b000c04582081481a001f0300910711086003419407021200c1c940d144455070218032012508421902c1404000c4070703100d0221400c000c2403000140c40040b032608041d03010104418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840277913 1250 840276663 840276667
    0xc010c08010f1206022106031c09051912030f12020702030a0b07050408010c05030103020a0602060c1e07020607080909150d030315050303040e01171603140a06050a020d14070801060f05 81
    0x8090160b01900c03500b020300092400c00b0048249010402140000c1c08540700c49c008284a00b401009480705026060041c0c41d80801c200041c085841d08000a11300039405040520107450000c200041000801c00003c1102c1d00740c032180d60b81803003181c60441e4028010036003103d0303036982d020100c14000c0456040c0a803c0c07000007a01c036821701940142c0402565225569070640c41040f0009003d03030401c0c81154841e070100701900b10300340222200c02001002c40c2c85480084858007019119001000f500a100800d100c410480b0034000b402d41820200c40300881a6181c030056900400302c4200c80f030344030f41540003c2d000f180c0650300c1040703212444922400c42c0c688074400300f859540160b10600c0c00e400c0b601300400262500c0740c0007a001c0c0090b1070107041c09881c2d81c10652322551345404081e2210007000d0150203600c00c1003040d5550715911503401c1c040ca00d0000c1001c0001d400003c0c5552050f0304103501c0c036108002502810740709500c19250f95519074200602100d500651521003000e01c142 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840279163 1250 840277913 840277927
    0x108130f02060a12051f0b0d1104060306030201262410020604021011030304082203111e061b0304080307050106031a06090c0f1e0c010c08010f120602 66
    0x40c0b400142503075030550301c881e0100103c868090f021580001d00002000008010400c410074207180c006003102d0000c00741a0719076409140700c20041601c20030588020200080000e42150180c01540489000343c0760f04601d5072400c46101041c99031000b03003410100804001a1802c4103090082d03604128182c1c800150b040c02c170010070010401c152640015074884c03820001180b4010300c841070001d20f60324003c0309808916421950324000508000c04880c4040303040c1c5c0110030764180d20300c200d03810044020002d50366403d0a8080100b60320003540150141032824040fa0a2090301d0801c059014000d00c0c81e00c483c100300b0111103072808140d24082d0004000c002003090041006e00300703a0340654000130740c40380340d458440c3c10040454402981500d24808200c0a940c03000b82c900e901803621059560f841c0803986010002c0e209844820b0705244200c02260b695441e000c019140018100000300210b404050303003592442400d105211000748204001d2001e0040d0364100c08109120390005030400f64 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840280413 1250 840279163 840279169
    0xb10060f091e0f0e010905090a05060a1806090f05070602010605030c0d050a020901060e0a05040c0519021f0501031109100311060412060b21102f04090e03090108130f02 74
    0x2003158030146190313940c2e100611184541d40b117401c0d00440f018000b8405810b00d0350f10192221001028a890b0750790718005815440d10601000501d09c2e40104100600d02c004e1603e03030b201e0342c10114180c0d045e1103400c0300860351a005101305002e0b502d0040062000d020a0345c00c100c3c0e0001ea40c20210f81901400c010000143c85041046000e8070190f00d0740c0e41228042004c0c040e10710301c103a20061007079003424050350070f06401c0b070201e4401500c4116014400c403426007041c1d18107203402451008001d0a42c5c94182e0003101766100341e041c0c86c850820079490140f60010841800001d444c0380c1000e0300020420000500a0640400c03010030203080e090611703580304110b0b03248070a61034059603000c0d140d120200851401c0035846020a1082c902c64521021510045075500b042c0b10604203080d68a81c0b448171140d1030400b00c0e00030141d0046140400d00e050024140e2103810502c0740300300e010700f010384035440c0c40d1011050b1080b129069503248401c2c2e841d501d041c040d5420403e03064451104505d580707005070b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 840281663 1250 840280413 840280439
    0x10e0603060409060509100f06031e02040905061e01150e1e03010603080a02010510180b061c1b050705030a050a0509031209130b060a0f050c03070b10060f091e 70
    0x2c2020001c0c00f20700b842e03c0300344400e0b241c0701500c8c0c070b0720203207030101c18230000703603040c015403642074aa0413401c29508452000c280107140211018000f4899101003054600b000c642da500c0d144040c84021070266a80d030307001181c00f80d84180010105410940d01d212908064011a021814594030441641c0e42d0744017080c03c440e1950020380c0d00d114001021031400350240590b503007040044071484901854001c1003140c80140700b0a030040c694840c2d2a444c4650394800954041000d40c403038800031003030381c41055030080a401540400c0b642810a180790160300031816244502d40101c040c62900113b100b040700e660f8001520b510a014040c0310000d0203490800c11050500c00e0059920364445014081140d189140d0340c14031080da080c250301c0c940c1c58491100f641e2541c1c816041183c0b40c0100800152a503004c3d4811000e01032001040d16800d01080c900e07550b0094103e40014150389803039845c00c4603000400b20b00074001c039008030010066240410442e041c00c2e0001d05800f5051925130800b40c5080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 840282913 1250 840281663 840281671
    0x30c05160e0403030507170703110f03101403030f0901081017010509060901020a0e0f0d0209090105010603051e060904020303040b2101082406060d140420010e06030604090605 77
    0x44034007410030040603003500c01e96400c28986e0403e040d0a00000c4d0048112902c02001042050780714046180c00c01c00c40b50a54529005440070143c0300d1030709901804a010080c0301e4465040c0ca42401c80707140c0c1c200401220385440c29000c80a00e882c0d1b50000540300041c0103403d141c20100145400215418444011089038859000103e407504200d80300b00d03d840c9014001450b0380e4410040e0503800c5410144984440340242c41d00e2070500c1d410310004021794440140a5046030030841080789405042d4803040c181e60440d2000c121a44030080e0300c3ca0459440c00d00c0c00058507414010035076030311f0040310182d4024401000c030781c5455111902400c40d5007001c0c442108031701d107810820f001071403400100c0d405820080020400004003400001c06c4da0402c03840d500700d02c40503002280b041d45580d42250f1021044060034090300e02c050340b81013001c820881e0b0a4507002000030b12040030400d4074807a0250510165540030072800c0c2e6104000030b603030010340b240d50700640e214140b00c002603071030144500c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 840284163 1250 840282913 840282929
    0x110d09080702040606031505010c0812091f0506010c0b0a110a02070e01050d2a1a040e0f01080318031e0a02090f0c0316020f060a0507110604080403030c0516 69
    0x1140700920601068a4030340d080203080c1030802903216220800c00c00c2d03050441e030003460070009144c038a0509080c1c038480c5460350403040600720104604204000313000741c111901202e84000301448102c4c548100e40c0c040c1e4203980020800c000082c04603d000301040c1c1c000c19501c00004403582065202000f96000044032340260700240800c01545105800141c01013600340c480010744001176403082459003a14042c914841d200b41c0c100b0010211010410026028540c03459403017142c000030908003608035125001e0200b6007180001c003124140d2803007604a8112200950a144141d40d110101003444d249403034140c850781100681e0448040101000c40d200300000c1c29031a0428010301c000340b0401003144201e00130b440280500c00b00b0318401c0700d91140c2c6425103407da92103821000c0f41041043c0880034460700c134440501c011229607602440c0580c105840b00d0300c0d0500403944242c2c441070100d802a1001030180010070210707005101350500c46200d2826541400c0190b862481070b50001d4000f501e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 840285413 1250 840284163 840284167
    0x106081e130206070c0b0403150506011b03050f0d09080c010c0c08180a080a12110c06160c170105010302180f060112020408010c21020a050d110d0908 66
    0x54400d144500d100c2580d103450210040c500d010003804001c200c07420700090250320002214001d0103150040400540a000f210655542d030b24107025103175a0400701042410745c0b40002141c150741c0580d8005d00c0c02144201c0c003140c0c444490300d0039038040c0c101e02c83e44120f41e2010000d402400c515480751007005c1e442021016111502780602600312080e007406607051040100086000c1070302e030f078203650460b030080b0b203600409402071000c03504029590b48401d00074862803451130704000c1c007408030042c00c0501d9640c00d441d001c101000c207551a26000030043d0816010418580300182e0382c1c4407240d0440c05641ca04444ad907484628000401c0010b848a0890f5540d0005004516044241408444500044001d00e040c041c807070044002e00030f803507a8180200a4413118801c4c0582d0155001031804000030400304a40c4480501903054075410000003044a61402802a0081c030a46882610f00c3e61070a0500f01c0c1164100c1c001c1c01c20b9500d008010a0502445902da00140a0070703040b03d10500e8240d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 840286663 1250 840285413 840285421
    0x2120406031505011b11040f05040605090d081017010b03070e1914070804060b100c03260c0307020a020a090605210d030213050d080702091b03010b09040212010608 72
    0xb00401203a40c108074108860b411a04811000c00d540f4006150f070440c6090304080745260015005102021000d5021070800003048180941c0b03900441c0305a81000a4030342c201d6042c41c0448074140110350407034039505142001d1010814451040540c1160b003400001c0407044100003d02d4102d29500c2400c91400180400402d0451026601d9071284000d0051040d550203505520075090014856420030140034001002d0094513040307610080b102030700510403081051002040004440025401300344034a500122039042c801b4482140b1580c1da06142e02c503151000c0d130301d031240e1020700711000310b224404580001da5112440c00000300410540001c49031b2402e82400810211001100050803440e20310b031504c1000841d0000d09900d007403500680e1080034910303032209003150307400c03460b00b150117282030034104a8420700800c42540210303031711201580d4074a0003171410812a03015000035007007400100004000d55002d08256040280094280350300808a00c43e441030076408400010b000e0320503c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 840287769 1106 840286663 840286691
    0x7030f06150e09040203030904110c010f1b020c01020a02010e15030f0601200d0c03140c010618020915030c0903100902010207050d050607030c0212040603 68
    0x1040400d8a400444207414052900000030a0891a01030100e00d40028080c0c8125401402075103070002800602008d00034180d03500079504414032000b040448280243d983c05070001c000010010508002c0c083e09260001d124070564101c8003800d0105c0c1d81c00301c0c14084158080c2000808006005c02003074404c43d80c0100b4402c091408410b0098001403004c8490190400340d032000d4070288443e41051595482e0340118510b503010500c1d003440319029213442c416450090609003540307005154030390400d80c00b252200c60780342d5690300240082c00d00980000503d141100007142440e64240105642c0410815000403500003c40040e0300d414143d8100d485003034019094402a1031003c400d070000d00207405040b800340c0036805001c11035042c859441c2c131103c2e411000900154403140740a40041042007140d400718010308041c2c1403c17008400041000b40550380d0009401060380d907003 = true := by decide +kernel

theorem cover : BRFrame.Cov 840107913 840287769 := by
  have h0 := BRFrame.cov_init 840107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 840107913 ≤ n) (h2 : n < 840287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
