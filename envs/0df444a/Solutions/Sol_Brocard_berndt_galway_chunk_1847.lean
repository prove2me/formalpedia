-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1847
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:21.250111+00:00
-- url     : https://prove2.me/submissions/a45d7cc4-f848-42db-b652-cddc1613fafa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 332014388 ≤ n < 332194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 332015638 1250 332014388 332014429
    0x8011103010819060e010f0c03060f0812031e010303020f0607030504030c0f03090510050306100806030a060c02010612110a05010504050a23120f0606040c091211030706030b 76
    0x5040c9620300307855024403c2d0302c9010010382d60001040c800f0755001260040701400c002c00138100741d002c1580103005040484030200e414820001812a1030203001c0040b41c0241001d4002c011440f20020420380c0081d0800f100d0300380440454600100c5c100c000c038020340c800d13001040b00c41030b060021801c2980040820b014145000108004079400c62401440554040102d00001a09240980d1000310741d4010a40003418003400b41a055003000045002d000c0461302c04541042d144011640c051044035410b401d0b030040e14690000451a800c5400000c03024000800c0407900d40303019070b031040c80d084025500c55101c0c0b4030f100c4507414071301003520190000b031801c24581400c05c404501c40e0b585c01c1c411000a40c1402048451801080260a1111000070078401c010080510745d00c1d91400520304516140c010140070a24030300c0e151050f44083c0c60b85d602d8146c20340d807030944190303038440e801c420a80c4d10301207102202403599024850440948599200090038955010034803260540704001c2c1100c08 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 332016888 1250 332015638 332015641
    0x4060e062a0f030112020301060902040605090f040c020307120921060c030c0e10020a0b01082802181906030b1501050903060c07080c120a0806090f04030809030c031308011103 77
    0x580d0907800f2241502c0281001c46038550452001c0380c0181066400508044e2001c580800e109a01000600e2083c07012244110860800b40820044483e01340038103000d42d0040100030300003640e02100750700100c00b60400c030003860364980d101f2402c2005601c4c516403d20300b0002c0f1008121440c4641100207900d442c1c00c21142c103000341c016195244824039144202402082041c0d614030800014219581c0102402020b5950340f02d060765030b012684441000400340e00400303210060340c0350304050140d001403c005c192039a10b03400440007840940071405e1701d01061540750744400700b401044010b52158068149500d00380704500f0f00b482051506904206041161380c3c069a80025484d4000c0032155507960b540d0004c0c40d0200e00303846240b0941496006643c4c024142803601c1c005003200380c00c180c460903030a682d09400c03c92401e00403a51a4140c1003443c01140100c0d104418050b8440d010604036858040301030075003803840d042070050030200101800f05201100003800781402d036000190a0740c2c00c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 332018138 1250 332016888 332016907
    0x606050a11061b0f0c01020d09020901081f050408040e070206060907020d090e0a09020a0e0103020a0b0f032a070f020a06020a08040e070e040c020312100f030b04060e062a 75
    0x581e00324680f40348483c64045403011018800c41d007142c0f5031001c008002c641d0f45402488400241011280991081c4103803000056580c5021600c22100d100c01c2081071f040343d119140303000040101520a071403000040c0000708003014210001da00500c1650010115850844c01304401c0317a100401c50707411034022074040070400760409005c10a44400790b103140d899551340c00c0901e0007002c880c40c01035448072241e0000180314440f038903001e042c1c80c02540e01c10b000d075171549042001d500c9041c0600c450841c0c200001503d03c2d0f0000b107008211a01202000700908550864801030340100c0c40646650b44800200001c41c50280c401c2e00050030140040c007004503042c0c03a01310b107a024a10501a0102480c000540d030944241110060fa00f40140104030312a0b01500c000c0d070329041082c9090345804114003042800303220b8018034044411a6403490700890459a90403820540900222101d644425002e01218001c1c40018803810802881029a111049886007606040d2409480081080003481c1c034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 332019388 1250 332018138 332018161
    0x50a05011d030a05030304031e1409120705120f010615020607110f1501080105070314160903080a050705100608071a0d0501080105100506090d23010606050a1106 71
    0x4141030100040c001c80c030449011034240300c0f0700c1c0b5005143c0e001c000f0130402019041030b6042849510703041d11500b040b812410074ae916840946260320220b005000b02002841c0100802448000f60b00548498581c2c81000c80d0340035080c1e5a50900941010161400204091040700c008165404080700030805020b00a900c07900094581800c200060084800403041045200244040c9204698014580451a81da43c100038001c010b03440d400d14000c00c600e28030030b0003a81ea03800008000c05001d5180c901200c0c0300c11250001150a01c0700c100c00c000042080702001d0014526551036442c1e4030900c500c2e005050851900c81d280101e40341507000c0c80f404c203001503000709641c6c407002d2100140315683c140b40d049014401c111000d040c14003001203900032042d04074a000b05121001806d040e44c541003040900d000d8808501d4000000c4030040000c035030744000041c03580c0425840b491980031034110150039102560414408075000050006080741d0160704c170044001128042c4c200c0342418140e900d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 332020638 1250 332019388 332019407
    0xb0f04200a05120c09010f11071707030203070e040c1a090f010c05060a0608161a030403030219080f0615220504090b10060e061b1c050310050a0501 65
    0x880c10400810700544140c0100100c0b02e00c8240103c1182492030000299071556100500041c001a10f40740304e942103d000745c1086440c0d00043d0043c1440320b05104003c1049081c075490001e19104100d800805a2070910000000d48001001c4400d41d1601e0b042c4561203003c19401441000e5403110b0a0061030000420340c1c0c42164110780801107020003800480e840b80d10160090f0a034011503086c401c13034040c954000800c5072000c00a440e09010515902c141c041618420031000c140c10f071100034100040503004640c0700d4480d06005082c408294114404092024100004500c0e11000d1141d580d440144c5540e101d4000c03140104050000038a101c0c1d82d028001000c006107a42403401c2600c801c15a0400021b0b1174040d200b0020051103091950b0a182d05440e85c0d858280f21440206006126180342e98140303001400b0107143c07111011142c0d04c91040780300031030054000c9800310203154404588400d1045410340c4c2e1103803242005804001003048952003540b08019050301080266005201c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 332021888 1250 332020638 332020691
    0x30a11040501020d0e04023009010c0504090b03070911130f12111318030e0f010c020d0f060c03050105100309020a170a0b041b080105060a0306020a02010e060108010b0f04 75
    0x380d4401903c100030401901230301c44500c400d50034046000d5031403007011021588034070030b030400e900341e903100d0704001e60032180c000c481c01c0e0002e40c0c1000140590034064001a03a111406001c54070180c0d69201d415080380c502d03c200d1100f50704002100030141104c40c00d01005004083c00e00750409140a58001e04101d42e400d0042c1000951040031100e66507210605850074481d010502c110784440e40d41000f035001c50081240468080c009960881c100003d40003004035043e1120f096a4540707030200080a0005d00040722580b210b12001000a4418090280d00441680b40460254101000c12080c80070000c0924201840c4c190204096038503014104212014045c49601c030003084903415042c079884a00140c0b02807004800c0c0020040116803043ca440c1c03019041c1c0c140c040d10744204a003a0740e0b0030b5852542c850456502030022801d0b40d8004c00b4007516030700001034034600e0719080c142884800d074013030203032707a5584c101c4824075003020481404100404c440c2084101030720b0008610000b290600c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 332023138 1250 332021888 332021897
    0x1080c01120c0c06062913120f1203050411040e100b0105070506131b060807140c0f0706110d020316030302090a0308130608060d0303050714070602030a11040501020d 73
    0x82d0003840c0c1c0101c1200140c40e0300020300b48541d9883d58042d00e4184210039001d98036110b40f100706100901c401c0140d400d1115962070341000986003142010501d40300400903504511400030381070020300007601404003801c0a46000c1818a0f0500305045580078031440e0500481c00c1c1441081d15507404209603581065402d00000c03a5540c01004071000d0080d00301c020018402c40f010701445052200707015003518403580c41d401c0d940c00600c807200709a8405200d1200400c003007101080d03226009110320740080300c01600103410020404050b9191800d001e9800078550880e59041c81110341c0441c100aa0f01c007400018081450038000c0207507a0b205031940714820700400c40c40042054841d0b01210704154000342000d116603140e0803c8005540442c543d100841800b0300c00213400c40c01100401c1c41040010406108031000381c90540c0548402400b0f18100a6200500422241184050078000380202001a141c0c6410084c0408903039072031180c90324800090000700200d82e400180708000f542146031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 332024388 1250 332023138 332023151
    0xc090f040308190606020f1b01020307030509010e0405011701150f140301090b070503250e06030411091314011a060c0111031e0a0605060f0f0706090b0f01080c0112 72
    0x2840401c8042c90f108428895040080020ba41a40080d590804005d540256042c6155a888001c0902500001c0c140541c00c00e215440100c0c0c001c02c00b03025040e0f010705080b004e20f80403c0c0041c0860320243c0002c064511511080ca90300b00c02407254120384403019116143d81400c00707440b020007001c2441080490881001110740c50340b0f00390403002c0403542c00480910242070112002c0c140f42c00072685104010800352822400030120f01c4004131300320041d01d80ca004406580300340b140d0759000030f10940d5901d0403824003605076214072003100e2041c1c12000001c035214000d403601c184881c0c0e19156540c1a0b81c100080c0300c0b046404100002561802181c000e6610981040401d000d888105400a0010fa01004000305003640b40f03d5204080156104014540c0c0e034108641c0c216403042c01031a4200e43d003404075045a9086100901c0c864000740c01d024142000d42d41c4000503640d04110868400911400384096020040b482c0c074050036514028080e900035880c00244000f11010f1000286601c610 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 332025638 1250 332024388 332024401
    0x9060604090902030c030708060403080906100905091c020c0109050301020405090a0513120206180f0a021005070b0c0d14011406031003141f06081506180115020c090f040308 76
    0x4c3c0d82950010303080d031f403603259115140358444408a41c15000f04c2c403d40002034800402003405c074452032030622a10311040c2070242190080034000e00204a620894901c2003171a0482c20720a24050026801080d030007000c0f00004010483c076a00aa01a07801071005109654440c0101340e0300290a1000152581c0c90314030580d10151100e1006d811064101052008560302240180c422000070100b01c800c1d0f0803004410781c0c1d803020907207450119007040720030720014a84101c251940400c82c0c5071690801d80242c803800d0203440c040c0c0b80111030507000100d810310f8181500410b50a4522801030b581558034200d1480800050100784512801c80000020345410a580d0548091a00103110748240c0104610a40c0c0c1d4901440c40401c180c5500c40407102c100350940904025960341e04080c0c080b141e40e503441d2121803400984410340c0080d44003546910350207601042402444003258010502c0b1500401030708002682081c503000c0c02c8240e04000300c034400e00395480c0d0801c0d4585000c1c4800d0b42c0b004c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 332026888 1250 332025638 332025643
    0x924060b03010e0402011803030f2106080303010311030705060a180b0a03020706060509150621040812010e1012030e09090a03081f06120608120307020c0906060409090203 75
    0xc0d0010318620034044004941c55403039009040c0306501c00c0c3c0b206005a80c00401a02110fa410b1000900148484c008100f48a1085041000c1c44241440314102001c4809001043d5081c0d5006481d281d84084010424445c07421130880d40013106030040d00060341401c1c00f0458030302c40d640c545414005201100d842400e0f4962404000b0945000f005855440440004010390700080d02940c60300e00301803012031a13180c10883c0310300482030190381942c201da4980500c1100d400008000614090365030b00c15248a0342d030210316102d5440344080c55a1031150a1084900f442d040e001030291701d102038200520611041c039070b082a00c001c074071440064121b6280403150701040755030032600f0040090a02180f00c2000a525498522039101c114140e6900d034140c841e1034880305e11201d124a00d6106c20410b0b10b01840d03502c5c0d00c0030010b40003c25400e0302d411982c0d18010200c2e0a030181a10000100b06401c1c0d030500c030641c88840c040700c078904139060900c0054942d0045000d401c0810f80d55401803821541c08 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 332028138 1250 332026888 332026901
    0x150909150228052101030201112d0a020406171e0303010501051605010c03050603010c02030309030a050306010c050a030f09060c0f0b0712051504060b03041a1506070b01050f01030924 80
    0x982411540c0d040588440c144d0300803007844100e01094241034001c001c006d0108451050b80156440d404816160001c82a02500b600c10008820b00500a0400240e00e0741d000d402d0160142200200c2d09140d01c11800740f800500d8986014451040324440040e82d00120841e81168000d180468071460580380840c15002256402001c0e07602e82410f104039642c040d0005031141d0700032402042008408002170380c503440f0455080010360010899000c10600440286801000c1854010310101c113940d0717160301d02648801c0a5000c03800f000c005201882c0d124007046c01030421403601044808090b5609218962800c030000c101c801400d0010f022039110303d810703103c01100e4080c107004c182000c40070010724070030700000c050265003400c0d0b0204007224894102c0b40110342c0108080792000d210601c48510300000b82055581c0c0f004808118005d98480c0302601ca1580200050025540b422040180c5d011009408505260030204614049110b0300c4da20540300612005621017002070444000c002d010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 332029388 1250 332028138 332028157
    0x50d080d0f09140304060509040e150f10051804060f021312060b09010b031302030703121e0801081225050703051203010b0a0e0415090915022805 64
    0x7410103060710300c1401d6001864802e00800d00d0049010050696588030310a9010701004500204200d450a0801360b01c20403810009205a410012401d640000c5441041e00d6500d0038604110900503880d610344004001081c040300c0340c62003042803452482c11004000d00c0a0602541c8900031352184040d80c0446044007507014600789807540f50b084891141c01325400544a091501340150103078280f40c15214107071034450030310604654581250341b2000c0050b6004980502800800000040381d14591b242c22a20341c0d100d04034412251054003050320500c110043c1040010130040082030b00124200c04a0000d4405403aa10349441405404002c3e40700301c1c14800100c000e280206110300480c101c02540d10a1064501143d04125620503900080c0915040104200a5211914054440b80e003d1040240000c00c08000c6a41c043c04a150305038401c0100340e40f07904c0e0070b508100003040c48101071007a400c011414a401d45158074a4040381c10764002d03007860303440601c01a440c02281a207603c82d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 332030638 1250 332029388 332029391
    0x91e0c051f0507030c02040e0a06060f0b0306150904020f07120c08090402131e08060a0c170a0f0504080301060e010512010501080405031c020d0c030c08240a0f080d0f09050d080d 78
    0x802c00034089c1d84d00b4000d102074510300d252440101c1e210201c0c1e11440d084440820209017181c48070380402088480c0c036803100c05000c0303081000008584450019007807111249584549605160070841d0b00c144140d4030110030800e0303050350703480022032100c2036804d455000c1c0c0380140c54815000d16884e04030300e650803144c00000c66501f42e081c015004602d94042d1040e40042e03940540310201c004094a0300980b4903000301e848000105000d5140b000815400340b1040c1c0f0100d80321868a0807101198000e031000c0d5001200000140000c0340c10010100b00e0300828a0b0070340c508181c0c0c01d4400301c01e01c0e040c0501d0b41080015004101405010820b075031850403040030fa0b0760601400407446009501084030980c646050402c90f00480e8080c0c868104202c102d501d451400e039603030140108a2a1700ca440000c1c4d005102d0740b0f04070081c1c40321003040b8082d00c60310311a0a003450402ca1990718144003c04030300c040000f01100c070b0380440d038070201800454400350317070080300d0004a152400060040d60b240d010310701d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 332031888 1250 332030638 332030651
    0xd110a050409120f140702091e0a0614011d040902030a080309070305120f0d11040b04030506090709020306062d0c010b0114030106021b04091e0c051f0507030c0204 72
    0x3040c800340300f4401d0003c0e5140c103550848000c1d400c0d10950f281084020a45805000360303030245c100810485c1c0c1c015440c0da051000c04904200984419505880c1c20701c003d03565800074400000c071183c4a060104090800000d119003155280704403648800c1c60306c1c041c0e902c6849140854404000c2c00003016405190b450b180d1400c4a01265151598407040c0c9183c8603020300c90412000d0f00e012074900e0703012841d40900d000002a00074014040c1014504c010010401c00054011030880180015520074030181005007040c450507864074206810601109104006200d0b0a1f903c420803a50145a82d5a102d007515101e851916000c0c0c507480004e4980300000290603030100c0040d401004019426215224030140000c1d030f40f9400c0c00240550303000760340541190910404164429502f443c13004001103034400d403c0d554070b00e6a6440c601001401c4e400c1d1402407003002600303103450000e058240c50341815640001d4141c40040142403003501405400104002454425180703000d00507000f03003052224 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 332033138 1250 332031888 332031893
    0x11150f0a0605092e0317070506010803281214072c2e03021c020a05040308030a0f06170d021603021011070909020f01030207020d110a050409 62
    0x500008980c90590246840004645840c2550105004810a0884144801d180100350a45078500d50440300481900140000012280b050001c8105114071059448035040d1400b40e24242c010380082403241c0051180c5400680c0c00c045485150264401c00c540c51024084255807141420396121703440c6003006241e481c5617100c0110140103401565039500c1c400c414640c03105140240944d14a075490440090030704600e0b003585141c20010844111440211806c2005201031010b201914040703038000c59290300d400c400c2e020704142e1a95200003989009a070480c010308a1017039001c018030303c44002c000301d24400519808441c05d201c0498080101d41e8036039508040d41d9412034440c0d07040c1c0c031611140040552011400840200300c0c1040a1000e0381107600300442001c0d10050501045012000030510b40001c100041c02009070a200081e211094010710032a900100c00c1d00d4180741c010058540185c070b40620303060311940c00543e03c0402c103c1803800608511615403140d0b5205003002020001e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 332034388 1250 332033138 332033161
    0xd0305041806170a02090a0c090801091a16021002160203010e010b040c0c0c15020c2d0d03050a0f02120c1f06030203061305070f06020d030515060a1115 67
    0xf90341001c5207940050107200380b41940c8421902009420040e031a02050488050b034100802c981301d503040c00c441242d2241c02c000d007182d96100f0169244c1c1415140000c030f01511000b0a50412103400040c2401615620040d541d4540b2803030340b8000c1580003400e40f1503619000408040140e0080c020301c00d141c44040341a01234484a98482e00c40c615124004603600c3c01084000d90b001d900c9034212050510b80060342074051601d5a8100942c00b450824060603a1010b0101c004180301c0f04204e4944025030500018441c4404900d0340074941c403a03401c8000c81d420405444d24005145400d000007404d103d012420a0300000411380442000304818210707a101042d0b00075003004440740c0c6000d001c004510340040d03a4040c80b01a425030801c8002c101c0d0349010409903034020317004000b1110707104c0c1d8903080048a00342a501800040c1c10030f503803491005a2600900341c011a281030320010407410000064442c0c0300c0c0780101c0003889050103104455030710a1046282910400388036400d01c1c41c000030040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 332035638 1250 332034388 332034401
    0x8071a07021e19020d0f080c1506060a09141f0e1c02180a11120604050f042001090803040915080303071416050703052401030807020d03050418 63
    0x1a140c00b0b40000e95181400010520300040f608005084524503d800344800b04000480664440c0283c038500804035507034200400003032030b201000749520100f01c50481000d01c1d0243c0b10900c203400c1040740c50380c00317a44182c8135030945035a108079076020b20010700042e49484281503d100c1507416120001d4030241c010362184403080c01924030010f1090034040105400390b05e40350081d4020b061005500c02645400c1c0c0c407590040c284000050a4000309041a1140d0400900706480b02010340402200342820b009054004408540351001c5080c40d07540c00c48814000941d002206260b840000b215a104904403001040320000752a52503454046200103046250a602003d0010310b10014002e10300004a0344070343c1c3d441d50f41e010602c03c1c000041900750b110081d14100c04260040100104105101810086109400429074040044503814802c407041c4201d955031100c00e8010004290900121076000354101c1d9105001420742c0b8054841e4010b0742c11240060000106201c0c104203141e001c030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 332036888 1250 332035638 332035663
    0x2090d0c0807050901262404030e091501120908031602061305030a05031503010c030605090108030703020a02040507170412083108040b130906081908071a0702 70
    0x1d944150300c580c2480341200084c07003091114202c014400c00c1d28041141c881c61111640c1041e07c5600e00f03130021495071000c48003110100302095106001c10140c020700d60506070303401503c2860062070440d11082d828001c0c83d04960502120700106008400150b01000f123085d0b00c8400a078403810428a880b040540166964000d44119000320b040c2c0001c103401941d034a54060000c500c3e0117515401290160006001e442c0d11601400045815540070b000301080102d4581d400100d01e40b501082101000c01039003c980a03410801078040440d50103c0e4034001e00390152070115060f1100001100e0208102120112600040e014041000003010241c80801801d42c1d0b00c10003030301d41c0142c40b5180240514610500f59a002000300e201d01101010390850340912031541c1841e0383c0702c00315a030f0396001c60055500e00c1d280c42402c1c440c04d80ca0307101d80d00186c4080e000421203040d1260344031041c1540c0e810040d0107001c020803070b04d0401c03c41d042d03102c0d03200440085207016410036400c040c0d80c0c0e001c0120310 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 332038138 1250 332036888 332036893
    0x2805041112150a12021309120905120309092203050714030315090405100203010f1e030b010501120207080d1d0a030801091d010509070f0605090a051302090d0c08 71
    0x1c00c90480d80b00754088002800144051a054642114603000c181109002c0380c0107400c405a0007100001c51180604060050392890000150b800004200c203c0540200784200a880c0001c00508000016500c52800c1600c28008540700c0390080071a13a0310146c003903101101000001d00406a0040207003c40c0d502c1a19118484080c002c1000d4a90204640841807031483c0c00311208a46400c00001d500503018800f07551200b00345202000130390340260055041405070200410061004020750340240340e80084e0780250b1411940c550310302c498103102c0c26040100c0d94820505100d03041d4111500c1036402403100d591116240e0030800604048030305140c60070b20054080385441c4006c102008807640c595280000c6038205030030b20f00148121220350802841ca2040506003070001d200b0280227007101c070020b044052905555005004090b04803108020040c001c4010780e0b202c030b112542c02daa400b100c0e40e20650544503e404020b0040d5440550b01c0407804050380309004e10003c50005840c0301d03c0c00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 332039388 1250 332038138 332038141
    0x607060c080c0319020304140a0c0611070b03010902031f1d010b09150a03020d050408090901081204061409030102030a050103060605060a1e030e0d030606030507030b2805041112 78
    0x264040c0301d000131602810104004891100400d07a2580210750180c4070300e040d0598480001801441d15021480c2141e030010445424402d954000c0300746610842c1401c01800b60a0600040000601042c420000c42035000300114205240c040b458a140900c112441c8110035912400070a8060810b440b4442e611904000403e0121f40b002c00c46001c1c0b880030344140396402014801c0065680310082c558101542405800318061503401450b008a003d00e0015032506119002c001d944030040c2d001d44816441284e001c0f5412010500b078034216141c60800132202c401452104813136203d8918060b07810352000ac204200d00d40030380e101c41d060ba401100204601c1c1e40724014441144500c54002010461801c600d0304101483c40b03407040c1c0301e500d524011030300482e042440f621b001c0070790360b400001ca5103d41c000d103c440d90611400da44407107a4641840510084000316441d10660001c03143d0b9901d54903030f100c6101402420040082c00003500801030041100070300711700c2e500081543d0310814803060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 332040638 1250 332039388 332039401
    0x21521070c0807171b010b09090d1e031103010e0a0b190b0903120a0f1701030f02010309030e030f0d14070c050607030c0501020a031a0a0609170106050607060c08 71
    0x1400016003941c000d07402c0f85041c503180ca50f0a90a130400d41c001c0d1950008002c40c402800d45007172980d002c881080004517900e800e0104101c10b55000401c0060a640810058200280c2c461046001091400019030650a966804802611040c0e0710402107041c0000000344103000c09164521828401c0000c00c43e511512007003081da1909000030f4a00484068414040c458000005000b180001011102103400b801a8038180d5000483c040c40030480d041102040c140d002081c0340c0400003441d0541140e076065a0b03400190490700d480c041d040642c0d075030418040500503200f00522200040440c3c61903001554420b0b0760700d14041d104000149a18400890344605000355030816a012066000140c201428003c140d0020325050307080010388040007011840c288001c1846d0702c072640c1c3c042003403038040320701c03d2811000c40c01e83c40c01035201c43c1082087d01d921003c490b00740c0f6000441a001c0d22000b80c11039000d008550031031584464006080410800e8642c0300f801070561585890009541c0c20 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 332041888 1250 332040638 332040647
    0x9050a0b09160e180c030601090902190303170705130b04051509060d23100510020c090a05060301150f0915081c090315050109060504020c0c0d02152107 67
    0x500c5000000d000c69004144510800f281c044d4152603118120b801802c030103000245002400e80c84031a600382c0c3c4112410135400d00e04e80c04d202504030000b015088a10315600207020400d170001c1100504240000708021a21900442d0005038085519149080e01c9110304449540140305251107880c0c690550580744942000340c5400c504010719050800c0d0b030710b4240307402510715407080e0350764200f645141064410444c51010f0141031492090f104860806080c0648142000300e000c2c1903610401994802c0c0c1c2d913084441768048020640410192100000b1070b02400c01250141ca0852131500f020a032500c0182d030300400c8801ca080305001001a034020b00a080c2103501842d0543e8018800c429040c03401c03540c0c0046802c003035140c0b491042c1e54903180c1c20340700e00d17481007103501d241e44034001040500000d02502001e014200c1d4114504045840700c90350300c1075202010303401042126510415076903240552110307000341400c40b580ea443d507c0d1034419074000c4076000d1005070760000041a5001c1c0b05 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 332043138 1250 332041888 332041933
    0xb01030e1c08092a0a150806010e01033b0709050f0601080f0a02031e0a0b01030b061615060e0c030108070e04021e0a0305030f040806011a0301030201080a09050a0b09 73
    0x15840134210300c400301e4205441803e203c0745040e08a41070705000a2a180c100860b0510421199211002c80c00c1803000100040c05824080d8105414441020003035a81c00c4810180e40c60a51241c1c4150000020740c000d01d0280060011018000c80a001610945a0700a00c0c89180e045801074441d6a90100644082d0011384000904864040c0040c100f0b00d4150300540d0000711038059564001346c80e1205000105049401a11098407500015110358050184003c85030342191001e0600f05880345000401614803405800c602c25000f1501404915521942c06800542c039049444d1411040d8504141d10a03c03030032103107104104002403640d1748d4100f101d001c1d507801400c108800b14050b64450282c488140d103158060100c810010000b0b204000078240300c0b9480a0306916145018101420168144e00c1079020859441c00198150b040c0002c5905407a4242481d2809450b6000200000e1039074480082c840d100d2100c07070806012190038114800c0044108456a00e0b440b490b1140c200d0700d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 332044388 1250 332043138 332043163
    0x1f150203031303020a050604031709060c0f0d0e07120203060a05010e07050d0b180132040e07030f0803010f08010b030c0420070b010801111204060b01030e1c0809 71
    0x106101090030b0b151041641003a1900900c125001501d07503495850500005480440114414800ea102111405405141c3c0710300240d0240256207000c41c00c014061090f80c1202c1c1001900160354840d1000700e901001540003244111644141c5540391070304a1000300005178480d1081070002074100500c1d028260503107910540a0b11503031281001940d141d00120602c105a940b111620322564441074042c90303e1442d0004100b01b5549829540c5003051441541091040d40c200030440c7c1e0840710f5451600c00040640380007801d4014085100d050480710f8000401844000e185101803000f24030186050b107107000c0c03125202c00e90310540d480c221410860300740c0c2c06400071200d8500924040d030112600716111402d40540b070312210301c0f41540d070b88200c0048a60b00315800051107166004d115114038801c0862404d4500b0b004120141062500280f004003a1a00e901d00010302d1b0740300350130203460702c00b107001199403004115641d214800040060348001450b40000120fa096000452103038082c0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 332045638 1250 332044388 332044393
    0x4020c1f14070c171209060f0117060613060f09090507060504060e040f021e07061a03031c020403120f18050f010c1703010f031103010c140d141f1502 66
    0x1240c0c0e940f401070004d4011002d10b0500024007220b0340e02d841941c1d440e4410000040034010a20f0100c4013001101810f03080314001241208081c400c12070f0004a041d044002202c050890707421782c502d914007402c0307990481d081c104403054000441800c0c681007003206610500a0b503c0858440408803101d003d58800d140008016801d40d41c0c441c00e0a0340300240340c06168801500e41000760013110441507605c0070a4101c8640056020180601c0b886a00e07101c0f0001c069500c140191480020354900402071010301c00caa8004601c0c0707007240d1550456000710b41c040e031101d140501e5410701070003111042a021022440459000c00d10100f04002071054590041c1881c0c003138140d9200454592030145000c8900e4202c0f40c0c030b01c0e0010214000a1070003403c07601310b0040c006085250208154803200685030080e03040c5100302803500d8000192182c0d03410340c03901c030135100d24629240300007805052030040102c00c0101e0034024150240043d8503030603a090000031882a50340c25501108089100130b000068 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 332046888 1250 332045638 332045657
    0x60216081b01030207032a060506090112031d0307030c0e0907030c09090804050904060203072019080d05040602040501021204140108060a0b0309011b030e060f0604020c1f1407 77
    0x2c1d80070758003030400c1900030324000c0c103103911040c01b0103100500680e501e410542201c0e444010003525000e41c0da072100e41551002d6903949041050441c1019200c0e0090620065261044591001002558210300700030120b1b40c00c0c07a6a401d040f8400314490050229842c9158006a1341c003000155603c112a071100308a0080c81c034280d01a07000300800f4000301d802507001c100014981c0d49200344d50f4061170013414010307601e040802015080800b1410b01850303240c81e000d09046140c0000c101d142ca4606d1181c0d01100c602801e24000f5003a00c43c20840c0080540340c001400f00f84426075001d0004d840007a02291195a00e511105178140a80d20842449002030ba82d0010b9a5101d143d41582003180900000c14070f40d207c04401c0c4003500225500c03030890307550348501500981101610213017400ca90038100040f660b841c180300c0d12804010032521482d448080071440c55151a8111003400e00b2400c155600070301c1c40300d120034141007181c09484806081043d52104030249585041c0203000039204c1403a80c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 332048138 1250 332046888 332046943
    0x109030305180301020d060e100303120b060f07050f0f030408070311040e0f0a031211071101020c060a08010e0f0708010e040305040f120b090d020c0603041b06021608 73
    0x19075105005124040b086100c440d04161024006005440d080c00310115040d800e100844501c6040100304800704843c581040020039000b04145400903068400401d00c04040b40220b000b038070446142e000d1880b0006110400d102010510300843d010003c1030740d810b1880c03d002c140c0d07240964040d413031050b013080310204009081252280f28076100940003081c0300c1c8050300c0c250305081d0400503511440d000040140100342d0b110100340c0c41d01c02c090300c04114081030b6003481c0303182c2d01410100425103582c41e00d4000b82d980c0200194803c521004107501c0e0758040042008028807400e20a01c5014290304010900315441c030804ca41c07059203180c3d1240c00980c604100d000340c6100240007034003401001c12010400062000c020f00242c0b17a210110f041c03102c0a8503100ea1585c0c0000c1031251310f07801c0705421a0f2559408030b081408030008031982a141c1c0c03101d007000001145861803018a6030300082000440d243c011840029202103984ea1884031682d0315400e0303442d81416115002d13405002282c4841 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 332049388 1250 332048138 332048147
    0xb010e0f1c0812060405100302120109060e1614030d0c0f05072301020111041a04150207260607140d0c081006110303060904021c08030414060601090303 67
    0x44415008144052500c1c0c9405144100e404041042c1e91582c000076101c00c03001e800440682e080103017917034200725514040b00c80e0700e00e680302400000d03c0b1704074a0121405004003508901c5c0030742d8005200300301d6040c0b50b86100b03584a000100d1004c003506848000608001400c0c1d03040d8040d48040c0c0900f00c01e0080440c2120001d0340010101c44680f0341600700e1000c54020030068024001540104100e103881c0700000c3e030320842d11138150b8116810708000030f00113140b41054a04944811542040344200c5060031030f00e601540d04013111007107030543d552110542c00a1503200711203804500f202503110300909016550421800901e00740e008d0750200e060244100c41c200728100440c0309a6080c440311010740c00503035a05000060001d04800d00f480003004455190400400050070324020010406e0100c980368003000340010f10444c60103001500795103402c0d080300f9440340c000c0d512001b1840b003031818226907081520300b030307a001080c0582450a840c00041e070a0141005840e409a01851980e0444 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 332050638 1250 332049388 332049409
    0x1120b07050f0c010f050c0a120c020c040f022104110603071101020d0605010f020a170705070e04050330060909010b0d0311060702030f0a1103070f08120601030b010e 73
    0xd04116041140800354024070000d4420307250354900118010569000000617202c02620f11881c8000411180e402d03250021814401103081142c081402808014180d0074403c4022056410074201004214a01d41e5a8010181e402d07803414010b9500f00c08000c184516003084a0003041c418108010700950f2825a01035548840c41c0c0c5840700c00c03146280003503826030f048201c2e001407554941d00103000942c0c01213a80b0800d080c080c03000f00100c4406031a90000040903018900900100103400070a115003404100c0c0500444140940281820f00e032044d600c0c1c2c8090030f0031002440c5a000300036280600c5800703d17090310f0800307280c41c3c1c030f501c40504029142c00302400e007a000350340e500c0850320340392140d18180d000349000e40c030303030b0840081089803441c2000c40c01085401150010010f4001d501700100136102a10000e203131500e40840d41808680c5117124076079001d024102844210020090900d0090140210002250855480d150015030541c1c0d085040c603404030300500d2003104281040c000e040d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 332051888 1250 332050638 332050651
    0xa1802100804150608011a010f090311061201060f0311040e0a0518010f02071106030f0426030115110f03031305010204050a030506060109060806130218040c030c030b040501120b 78
    0x54010710783e000404002c030340059001c0040341e5102c6200c000d641c43c0c2d0151007881031000307007044542400350020080120226000c010400710b450006603020740c4842040d03806060b0b00c139007080c800e075071106000b402c0800d0000da1b0b00c0000c0d0801030b4030701d00c3d0281348041d6412500e6107401c15078191581000400917101c003c00340c0358803d0440c0501e4140280034002d01017460044100180d84401070b080c05030b400000c0041039801190300f00f00348007000e218441c407150301c5604800740304c900c10079080032541d408120744101c124801001c030020590b0303a4000070081000141c3e807030720601d2030001d140050f04d03500010300074421500f0078400603032003940151002c0c841e203114a000610b490344035000200e00d03c0c07680d00261081d600050400c01e03a540c000180c2400340004e410403529914100c03000408840c448601440d03d1600458140e0203070350303103890421103460003d10900181001c0c0d40004d00402008080100090805070707101130038102071081d103040e150600c20354040c82c540d585814603040d80c0900b40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 332053138 1250 332051888 332051903
    0x91407031217390a091d0c0c1501030302011401091e0f06030512030a1404050606060a452d030206030403080105030d050301050609040e010b03150a1802100804 70
    0x1800d0340400380a0f114a540c0c1401c101c107521521181002007076144c2d07a400c040d840a4881034400300401c0200c540c0340d8400d80d183c203419519200758a501d410b040354446400740c9a500c0300000b004164040d0040a0000141d51240310719a030b88912200654081d20f46401c0b000c0c0f0b0703503201e050f038241550308014001e83c0d5401d00450b6160b66a40e1f428038180c608903641d00102c5c8040281301100d80da82c0104058001e000c808072007942000d44030240c84080241c211442031100154895581c2d0081c08071441c00203480c101029034120800704503000d005400350286d1b5841900d1640300c0080c4605c44480141d070055a0700c08044003001c603e5100a12500d412502c41100171080000141d0312000198401c51090fa40d1204651401052500e8501012169024440180f0040c007164850702d00341c0d0042002140c0204404c090890000e004004255229130136005840c81e051200319801f080c039014010004003001540e1003816401000c05803914004c0d071000d1841081c5803132900c14002c860300180900340 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 332054388 1250 332053138 332053201
    0xf07030f02071508091c090902090a0f030602070201031d0c060c2b1e050d02090409020a06030207050f01110306060304110d140d080c04090e01091407031217 69
    0x703079403160b415241c0c2100084d8074104104129100340540740f1011070302483c0744a4851000005019030f034290041c0d0040d13550106500145942d010075503c0282102c042d414003450b01c070304007100650702c0130005901003030414110191402c0070135a19204d0003491400b512980346240304101c0d290f4400840d120540c41385030840843c45400002400302c20f8242c3d10392030000380b800c55015048020307203800c1d04407841c8004031200071a504441203c0503200390443c01a619422a00010024900007001039040220003602044003501a401064003030302440c1114120000440e000342030b40c060804201100388140b001c07901c6420050090741c3c0191050100b82c1c045000c00b004282c2d0b07505100415202112044604a40c00030140100c584071000d515007510185440c0200240740e1240b4843c01080319540c41c07004000030820750117141c005a0040c080f5a1310811600300075504e82c61070000f9501d14905078804800c050040e0904901e806010204920365038442d0b601690780b803407521401d55082c2c6507a4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 332055638 1250 332054388 332054399
    0xe0f0d03120c0f020d17060409031b050309040b040911060c0a1202100c0e01020a02242206020318090604060308031003060b0609030a060504050a0c030501060305120f07030f0207 78
    0x245400e26115541c50f5104200418030091401043c400c45509000d1608140442407814524050f07200c04191008580300c0b625240480d41c0d084082d405580402c003070310800040002c040028584007400f01e906001112000c4208006c03507901c4c00004259849200900e03070785040081c0500400d0519105070303050083c2c4c0b912000500f684020743c0b000183c10506103030030914901e100f071102c8000c0c85d142c00d43c4c083c1c035000000307075070b607102900c0107841003100d22544000844a402e600780401010080540c5503070484005120340440211071554171161004089100d030b10000030b4550103102c8040c4880c0c0c8100a805000005034040d102070f40040c3c44060201c00304000c0342c003c6010b02a071002040c1c01d030f4a181402422240170740402449003804100884c0f03241d40018030354400c03a4208800160680796440d0481c5080c40004d030080008a90f41e0001090004c10b5000038101d80c064005c0d6001d050740106000d03c94481c250704000c94280c14031609020034411240490012039034011212002d4907072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 332056888 1250 332055638 332055641
    0x4050d020d0c031a06030610120b0604060b0a0e0f040b090a0b0d140c032503020112020c0706050d05100f030816140109110a050102150c04030c0f080d0e0f0d0312 71
    0x444100391801d42c4c003043c131a0b42d060412100d544451a1045001c89504203908491041541e000190069100c40b0200d860380e0f94640c8085d000702101100a07545040088001d0041c00a41e024a441a060340d05403800700e003401d01820f0b03a0302c2d00080682d940c0390758025105c8002d010700000d042d00610440a06e1000a0300000d00c0d003890061380e4014141046d10008051a000e42d03c00410031800c945249250000b05d035402c090152a82400c108007094076412740c80000b805010003c96044c0301d40100020141d030090002d00c0d2000c1d0806017800107940b80560031108566500c2208100d1200e114108042080710f00503240e40010303500f9401407240786032916020100110811110740c1d540f0130707003c4100807802c081c6040c1a001034400700000c03490880044c1d1103a04406010903c00c1102000904e42c80d44041109c0186510440c1c40550b1901d41446281d503a903036003c0e00c407152159800b2450401d006580d00e40354480f0040c084030f0701c0d4800c80306001130b124080404809210041c3d03400d4800c3d9159 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 332058138 1250 332056888 332056913
    0x1f08030d060302041a010801120218010312120606050406050711090703020d0b090112032604030207320411040504021804060b0f0306010806010c02121b0604050d020d0c03 75
    0x21000007180050841c010070080399924a0b00741814450059043c0c0c003070b40c00c0a0101d0444a003021010704c2c015490021031846861243d03640a014000c1002004014101c200c144003414540c0d81c1c104400c107106881000c6803507600950021075828082080064810402890801e10885140c448519014003161024509036070300d4001c65004076020886002d18840d5000c81c450485450109526180002c42c1042e200100901000007241c2c145540601c0924031005903a124601e68401d1314090130000d4030b0f001c1c140500c5841d1411700d0b040c1c1d0300500560315500d01c0100804186900445940c0803c801041400202c5440e10b609000002c0c15542c0d0b8030142c0180c0800f40c503140d0904540c001007208072011a001040d01d0101800384d20342c407500c00c0f07003500e070702801c2070901040546400b001610040081c44000794000b44018401c03188200c042250203400000c8003402d100b0200c00c0d1300304209800341e40641c0f9044400c8d00c004c07002520380b1010409000e400703a19201941c0d13840e41c039405002042c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 332059388 1250 332058138 332058157
    0x2010501091104030b0105040f0608030a08070e04060b0306040c11010207080d180f12050d05190506060306030a061d1603150203010506070f05100204270e03031f0803 73
    0x546200402184000b40100b45884a9102a4038545030441d82e94101200c2c040c00f034180110b0781c5440e4941005180e6024501905118084a45481c40e4140044c081d41007100c5000015402c0210321009007014014030050300c2011100d0390a55540005000062409030702d0241000202e2030700c4002083c081c401003104500030410550740e9500005048199002c2041c015080700c425410b8034040b42211205002856114800c2c42c1d0b0303460382d40c8085a140c080c4000022282e07280000b4454450100c907484020410032240c14400c90b643e001c00c00c2014007040711904d030503030010009000022115030108a6216009403074070a6508611480761410061880d0060011240c94041c418400e000a0780858000d440310150300e0341d0b050401091036409030540c010641000c0b010306d02c007000000c4c0640c038240105080c085403183d984003c9200c4654000740c1d50403410950122603600301c2074a0142900224680b80214030303644030346002a41c241a40c0380b22513030740d450004000c104210706100a000410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 332060638 1250 332059388 332059391
    0x203150903070b1509071202040b0d0b030f0a110118030c090203090f01050103050705040f020d1416080603030301050907021e01021b0a050a1b0806040501020c0c01020706081f0e070201 81
    0x140b249007a0300701550141c04245111251501e1134020b43c0c42d220807543c4100145010402c504003607600720082d00803074100700e04140c0c02040071001003040340c0c08021010012403c54401101455026807100c502e040040d0035001b521609034400d502038401e0a95039244140181a000c1c2d07242c03180d1005408980114203601d8000080c03062078078040180c8101c0e105000000c0101354510380e58942e40c0d0025125460082d600c88021680c070001540c1030b68080700041006001caa01e405001107010744044941c555400b040400e01e0001030302c10000d01b881182c016009515603402c0038100420068000c01d0f6508511400c251580c0f00c001c2081098140e6000e00700141c1c440c0419495140390014100400020742d10107070b268008901d00041e14018550400010f100701040c4d0018444811125000224184175403818070040200550081100c40c903c4400c3e10034071350911004a880f80600d10500c0000703a2540c0c08180c29400d0000085c100e07449440c141c0106540d10342e0240c0b2104421500b11000d41d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 332061888 1250 332060638 332060647
    0x31e020a060305090607110c1f18080d2d020109060501140a0317192a03120b0a0906030305090a0f081e0c0a0303020105100e1603021803070308040609090221040203150903 75
    0x1680004010312012801c908103c2b500d410107a41d250b8030601c8600280c20401c0580107043c558070400304110b519035045185c03540d41d14025102a002c0c00c0b0050b022100c0b54909400020103150388002080c0807400189800c140fa8a95207640406101e180c550a102e080c0810001340110401d005002c00d90807103403907010380301200082d807641801c0600010b0400355214140d10000a41c41111f0000c001d0400d0300c0041c508002c40c021a4103040c441c1c00c00c2110380c0c5071480100a040d045800390944042c11038110481c9925030b01c01d20480b900911400400303601007904040014005e01c0c1c06a00448264110750900394484001804070f8025401580940d55074824081c43d003918007103070005840d0500da0a0414109010207180c4004440908000c141e0302141144914146d010b076850103100c000c044600031a1039080610440d802481150003240750300200040c1d8200070300a035050280c640c00d40d8020040c0021035241c0061000780100d91601400425591a042c1441a10b00401d0790800a5448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 332063138 1250 332061888 332061949
    0xd03120f0507200613121110020d11071e080f0f04050f1002061b0702131413050a02010518091006030b03010902100e0109031e020a060305090607110c 66
    0x8101c4801c60321802d42116080010800010541e40c8055a201401c665210006c4508850030540c2c044031428034003407020002414000c0e500031703200c0d40c1c452030020402e548031080c40c0400d92103a804014044c036a101d2038544015003101000194a009804191900300010040f44923070f4411042d22401c0c0790701240502130382c148031020442002003559265511541d16001035552035000744454500010050160724200340325003642c00165002d0644480100314104860240c041211000030110503040060780d0002c2e00642081000d41200190000203813540045515a1058204c2c3c1d9104001041451148e01d070704900c1c40c4076443c40c82e8014103590400c030008065034050110944aa0f0419410002590341c412124803c0081420308850a44406005850605840e8005040c1d0782a04510381c1d0b22140019406102501c03c4400d0102503482e18005d808031441030700e088001d07038800130000e000303540102c0c40f10f9a4528851308440c5010001c2c0d0020f2103600300c86c0204080d558140c0681c1e000e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 332064388 1250 332063138 332063177
    0x302191a01210b07020f06090106030203011512062019030b010e1503130c060309050c01080c031810060609090609020909040807030306030b090d08010b090d03120f0507 74
    0x2400340802e2500c0c0007501c6600700c2d030021068035000341400402e00f0201e000c6030b0081110581c0c059210099907111b07c3e0009a1a008052070320043c0d000354208130320040c3c00d102c8c00e03881c0c8064600d0700704109080010b0b034850400a00300f040e0b2054420002c281c0c1d0000d03000c0200003504004103051141003074140300d84d5004007642c0e159524a41440714441e4141000d40d9181d036020600e040b80544182caa9072860200c040600c3c02010107002c1c0192900b0100342d0f039500d40c00c81500c2030301520480d8030354002d00c8011180303120111404c50440032b0510104050306072001480c10780403904800c5550041c03c4560710340407101503602840109505200400c401382450054000400c0b041c2421070030303c08800041b401c02c42d8010801043c002c00060503004140c000c1d88004040c54001698081a2612610607a502c001581c3c101010991740340000440c0d00880b81190103000000d00641c150f450705070390035205d4032800c0c51003646440d10b03aa000d02088801c0e120729440385800740d403124800c1600188918 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 332065638 1250 332064388 332064391
    0x2100b0d02150a1d0a0608060303070c080703110910032604290c0303010302100c051f0b03010b0a05010c051c0806280303050708070204050906090708010603120c0302191a 75
    0x2c041044104c221907030301c58070380500310364031801c0c551800e640c3ca0700041d00f1441440d00c0149600040d980c0815010000a0780a058038400da00394400920003034108171b81d161044894800d41000c0480600c0012010300d00640428103541c40280000d04e0f003008000c46800980040725222080d001d0590316525501550200241190f107151610b40443c00743ca440303200502010340110020141c0c1103105115000d2100a42e07000380507940800d003100f684a811203090001c0403001810083c0300700f0145010b00c11303449000304c010841010240741a00542e81810180400d5030b490046a192051220003003000c4c19400da080e60380d0146519091040000099803504107200000800b42c1943c81012040705c4c200039680c05007003142d1112420324000d0081c0c441c01748000d40050070a02446544480003801a01a2246100342d80c80f1507180d94215003280c1c094400038044000280813034010702d00174103c2903006402791041e80d01c005034482d40c0c6041400d40ca20b0881c2c55908200d50368031500f40404103e1b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 332066888 1250 332065638 332065667
    0x20d14070b0301080a0311070b0409050610030509100518030c160807060f0c06060801180605011401120207110306100501080106030b0f010e03010608010f020301180c02100b0d02150a 80
    0x41e030030765040820140e6141110f180090522003090a501c0604004100300030051801c016590383c1c45450303100e2000640400d5484602901c00e80700407414085c02400307010300c107400000003046803600f000201030240401400343d180f01c0000d8600ca9000e4101032004154022018008009007603105242c0035201003541e204206a40045000303104890b40640a1404400300e86040040d06c41c0c0ea050001c000c01459000007002d41c600b081e50300c40c042001c0460b4040600841040019a0f41c07900910b081040d00c0e44024001000611040750114442c1e0241003258000d00c0e0300c0d1003e62800c40420703d003210544010104166200e8100a590f80c09241d16001d00082d29040c4003800850010910554558810313a0520403003001140359038809512a1006000ca50000c1c80110107204141e4001e50080c01440300c01d040209100c5a51402406440d05c040d009500401c02501100d01100040c80c5d0582c0441e030200c904c0501401694a80a601307000b260101c166903a01e03100034030f000d002d801c48500310 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 332068138 1250 332066888 332066909
    0xc0e0906060a14151216090803041a0706060602030409050c09011b0f080301090b041a1012090803040305280e121002040f0312080c09120a020d1407 65
    0x1c00c007094440d000d00108590921074042c002d8200070000407003d02c2404400e51002070082580d00c41030300521540341c0600f02051362800120b90000b02103640100d14025141c0326032081004000781d14001840b108080d4032a000241815aa0783d5044207984140e0303c18401a0f101007018803035000b580c0b003001c3e0408000300d10203182c9441440082c0c1400420304407074128104080d079034820f010500400c1c0c41c0460b4041886907603507844200d03100c000c0005180c2d0a000d03520700f034004144806900344200c2e0180004018080c0c18202403400c440249102d1205403595803034000550014031200040c0d0f0040c3d1007a00c409860b402c0c24040002c6502070f22403d0701050046d40c2146070308a412068101ca0305405580340001c0610321a003241c6485030065004030450301c00100010660341c030143c10b405882c4983d40e049441000130b48101c0f503c8400344d0b00520060403c00c2003a05514140309802802600300c0c066803241081a0006190040884010780703440f6a42007040342151810b0100b00054000700b0107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 332069388 1250 332068138 332068141
    0xa020322031220060403030c020d110303010e060607060501030c1a0a090e07090e040f0b0c12010504200310030b070f051606060e04030201020c070501081e041e0c0e0906 74
    0x201c0b44a4429001c200301c0034428002d00c0214103072980100c4820b03003403441003120454105890010700030b00e84504028014020400060005442080601c83c918408001107095074200b8036400c010f0ba81c00307480d5941c0b2841c10006c0a00246183c010309008502503940e40b50710f203150007150070b03200f040c03000701000442d01002242c1d112034021002c0300c02d0b1200e443d44c916003070340c2d07508059500c0d40c0160894441021201e00b044100712200b6414800c0c1ca126140480036622918038590b0b01c0d0041200e1540c400308040018000c6040a40c8060103c22484801d01b0700240c000f1013a86036a4015500d4900c03107800b13905e052050142c0e1085c41504806145403400c0d429005075401810344c042e81070200c4a40c0b0f41103002805004d05a04400045c1011103290202c038145454080e0007076100f4600c0041c68001c0782313000603866002c2c040b0701e48a031100021102940010220b600e802c0c0c407000700200c2d0b41201055402440703c01d0004210b0016104661000c02c56003001598040c00100619404d099400b040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 332070638 1250 332069388 332069393
    0xa141c05060a15091401090f0504050a120215070203070201090e0903090d0c03050102041203030614060318210403020f0402071a040303092111060f0c0c010207080a02032203 76
    0x141e859010b15104000102c842c00015003c0e01e658140c1c0c0280c01c0d0360304241c0310b004508440e02400c1d040303c014020030480c5281c2001000103541c1c0803034000d48150001c1c0c0c9103001050101f03041400600042c410364404980190365240809826122800141d001080900c11075811025180c040c003400c020100d01464080d40c2c183d520700c5460030060045000104200401c007412684d0805154004025526140c58205400c50031100c21000d5000a0030a003001900c03541c90090311405040c0a003030a8650742c2c400f58404c0e01d01e51046070604907881128598100e080010708550020180c04001d150f4407840c40c010000d003d1030115407144903d1040054100084201c0d50b011420581d40c216100c0503903c505040d0018011800d02811030540e0750030400d024902c450120007406c6c82e0391103109403440032002990380d6007412201c8104103050712001c56004407410018095260810002519002c0c642d0707139015141d084075101c040503030300100d140c540140c1d00c07000b2014202885524660400d1968 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 332071888 1250 332070638 332070643
    0x1d0601020610150e040908072006040b0a0507020d03020609010c02060903090103090c0801111213050d05030901150b0a0801080d120510260c010c022803020a141c05 72
    0x14821124400109080701e03110324081c001000304c40400520800c0b200d03105061a600d40c2e401365008035142015174903903850300e03412015504c400007800b030070b80d50030142080c410300b4041d40700030034080a0000070300c02c1d10016943d8041565002d4425405408182080c5d8002400d560340f010201c01950400c50800050f518000213a815001003441c021917600f0300d500b414180ba000c2c0e07070480d2149508181d042d12118140720000c08180490901403c030b659a00241c0780391116491000070807035044068031031140c40c45400603540000e212400080d044050000e6060729407d151700c00402000041a003407001500005402e0041c2540720280048004041e07004200b61402d21104079142d0342c03140030407070103001c2280000c00b600c913030860301540100807100c81c40441c000184131850380c8555900700d07505500ca0892050043e5015010329402c0c6485031404102401642448482070b07180c01002001d0398850800070002c080c2d03880a018411046018000b12520490804401e518022200300016000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 332073138 1250 332071888 332071921
    0x1b141005090d02280b01080601060e0d05030306040504080f0711030c0312030106081b040603090c0906050117220f06050c0f071101020f01060902180406031110020f0102041d06010206 80
    0x202d500b8001400501c07086a80c40b10740d11001410102c0145d0000c82c091800040381416034609840d05455a0b03106000c00080042001000304540c0080c80850359506280c0c000c150040d04c91540c0c01d05160801141504c150030662080e00c7c2d508071001985261704081c40718244101090b0003904284e00c10500e50200782c441880b60300200300756240024030750104061504054021052090341d00c1d0350302d0400a002c0c040f03051081c0c0d0081025071001400920610411040751746c1030310351610085d607030b80080c11a007500510011100040c600c1075480320700880c030815021845100d0710f003484d1500f402d0480860b44010511141040104000011010034a00b038070100396018600110103092440100d080c004901d5401c0000d600300100414000308a40180040c64050b88000c1e09050b040320410040c0c54080c4800303030944804500421641c1407d108600e000c0c40d082c01100c1e03030401e070310100720b0880c5c0c46540022000c0858000e540981644802c1c4107401400c244014141814242c030718420181c60b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 332074388 1250 332073138 332073163
    0x120907030f0f0804050306100315151a0c0a230307470a0c0203180609190e07090501051809090703020301020301080601150c0803071b141005090d02 65
    0x540300c400c0001c202c80e940c1140c0140c40c0246c16101141460440c0c8800c0080782d0001b1191203a03060518801002e2074890700c1416070b0a0342c0000c141c4c41c9003404103000416000810301d585c400c1001964030544c030410a2081041c418580c0b036508110a502c05013400782d4680c00c920b02d50f002000b078480842d841401e0300001c1c6400e925140003848580e102201e42c440c19840705042d0a08402c03020581101c90510280300720b081000c2403000c0b64000700b041744c031f91003000010a11414001550491801e08401401b0000740152001565901c20400d5102c03488450307001c1c0240e9044442005442c3d580454124002c10081c28114103148000d01040f44010380441440c0c040c04128002402900d41000780740d004580180085503a035849420349500d901090080304001c901019403210480e00c1501c0c40c045840e00030710001d00b15100e4240465058402050f64140b402065a07001c0c0450b07107404652101c00c0081004000007110750b180d8200346d5100410140443d0000f460b180106a0040f841041d82d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 332075638 1250 332074388 332074403
    0x90b031605030a0b0315040c0f06201908040618030213090201140f12070c08390c100801050a05040216063603120c090e0c120907030f 59
    0x985292883c001019540b031500e5062150a00c2c0f00203075600c10034010b025a0140d25120900c3d074854200d21014461841100300088003403c03a941010f00d20785440c0901c410420a55070490340c4070710303200a2050080d005a4505800007001c000b5540c210701c807058a0002420110891032450300000c2501d842c0106008000341c8605c20329045a200d04284000c181b81d007200541c0316203060001c454290089030039900b441c0e140701c0210b00301c103004400c020701c1c20350300040c1c40346400416240d03203441e05204921610002541c5001d5016461050042410071f10740600500301e03038220600f00113412134403080d45024005401d0061055844000b840011b842d4180e50142c1d569500a002d4801300305c8030310001d015a850711103d41c031072050f040d091a0713641440c101d00c07100140c0f00ca0000c081e080c3e00000002c01140c02a05240f51903001ca400c0361140462a0170950700c01c42d0f035010700c02c0c0c0210f001c5810100c11200015100d0b403420b1148403183c0c0210500004001603030551b0703501030082a02140140030003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 332076888 1250 332075638 332075641
    0x11107020618060d0209040b030303090a080a11030a050309010b0901051c02150708030405120c0d1b0c08010e0d02032d0f0c0d0305060d120f0201020d1803090b03160503 74
    0x11982d041030841c0200002d411a40c0d55403c0c0c581450003034000e1308215100d80e0a0203c0a80e2034130740002564000c5040c0006000030741d0499580002d1075209034489000c0c0040c3c8859100902014005010709003410340f0303440d0745c82c0b070402603060848545040e03441c4617030f0701d5070014003090300d59541a0281c08030300b101c407034200b446038000600c01100c0341d03c0d0400c107880e00180047c03c100303601c0701650041c3e1149089414a8800341460b5810f4000c8003000c0c00309034011103000c20201e01c20001c1c1d80c901c14407400303c041300d200b4075111512203a0341ca401000003070707444594a4142c00402c104120004a4a202540c1441245505200d80322180750903c00d17001e48406003442000544000c8401e414410b00c00c2a555003c4405180e0f2544c03407120040022a14050001c0c1040c10b00384d010400c000e07071008011888103007070388007600d144840c0821102199400c4c001d02451803040c2c07280d02440348214038042d1001000d8a030040082585400c543c05c40c500c02d0040c400054040c0c0716070820b64915050081c1ca9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 332078138 1250 332076888 332076907
    0x90303020a350a0608010603060e0609070b09093c01120201120507022a03160b030f180d021507030204030812060607120f1206050109060c0503090301061509080111070206 75
    0x780001790801601341d440c0040c000108461580001001ea400100b035032050f40c3c0303041075562204900c1c4240340004400300105112450405c0c1e0643d0300c42003640c7c801040d0400926a00507400c2c11600788482c9400740380e64480da1509920740d2030b0042c0001803041444454990000340a0f2a0084091b81c48584810100d90300c40c1c002d0089000519046108034000b410030080701e40c1c0141d0038034865002c0d008102c03c101160960f134012038159140c40381101e165031180072403415840d1000708030000c001c80305541c080700b6103001e0110a005d1800c40d402010201e1100711070842c00940075001d0028548100400c00000d00048180d0b50642c80504425816941d5000810308500c21808010303d402c003207000300a0180d40140181c60348800f01c0e0388610307a00710503507402d404641540c082d05000c03840e2084200041c1380329810703044050348500141c03030408401d8808a400d483c110342220f1208080c2c00c48803400035502900500042500000a0040d44805061081c481c8030300d000189c01103a000460986 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 332079388 1250 332078138 332078141
    0x332090d0f020d0f06050705030c07030f03140c040302031e0a0f050f0106090507030f0b010918091b0501260c0a1808101508100207050709090303020a350a 68
    0x10455005072800200c43d40500c1e1942001200c19000c44060b031600001c1060540300304181c901c600d4908000ba8071300122920161540c0481c4442c0e68105611000c0702c136200c0f102c5000450064401050f041d407142d06600c100350500c041007624a046806284190b0080e0000080c100100c6401c104244030010003070520703a0800e180c00c2d821080307560030b0100000c0d0755882903000c40e00c071301030a50307040200701b0114951100f0340e2b42e05a00c203400144a81710500c07183e041060403060042c9407031000034421081d030303a401c6c0031400300d081910041c1c40396000802032540c000d1410304001508400c0306213076581110441c0896900540208012a40812a180c0c41c90042e41c551690b140701e00c11810205541c2e22810703030313a82c0e8880d600d411160304046c81180e070300f0400364004042d510020040c01c80e10000c800070700025040000152070320310030340d41300040410703940c0300b0003e01c0da0103030740c0c0540d0b20214144040e0050400b020481d240320f440015200070a1901e80e4000014001882540b07500e840f0644204d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 332080638 1250 332079388 332079413
    0xf06060f120307060e0705041b0c06050c1b012003090a11130f1e0204180b1f0206040201030b0d110d02010504050316080f030301080d03020904060e01030332090d 71
    0xe200502d044421780720030000048140491780111410711540310f090840118501d07607250b1440200e001c4010450000b4180c1c1c000503032081c030946a86007064004014028482e000d0880045e060f551480f0980807007441030750350702c1c401604d585200d00d1340c10f082c50a56541c240490014010365290300c461902d03943c800200fa41c010b404030f08148100301098040764001c14200200440d140c50441580a069520f4001d88084507840210301a030070103825062800340070300907482517129641c0c039858800808070440e410070b400e50503030061245162501c0090308039505405034501c10241200d610002039611040d0810989003070304c04414004551006072624000d83e0442079040c004d0007100a5041d000d050508126221708048610540c10f00405035140d02c000c0c050407060f608040244c098041c0a03800419802d18081c10001e071480d0b580e1089148001c0a1304200c000130304035446182d40100910780700024048a2511400c1c001c1c01e080104c50500c5610100c034095080305041500f4440740030b8401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 332081888 1250 332080638 332080643
    0xc050307080309011b021f0e0f0a1208071416030c05070b1c0b18190f1b11031804090804031118010b09130e0a0804080f06060f120307 59
    0x20340728240300c0740b01400f03003805100c01e41c2c5c450075401807400260710002e00d01d2441144441002c1c91050344141c00300143c283e02840c00118400c00d00080c0070b840c0b042100000d0940030b80d0501c113081d1a103400c0105100b034090400310400420741c802445030315541c0100c404000b184040303145c04082c0c520b02074610040c89203015165001d64034001510040315401400b040f5111602100301da03241e40d0745481101d81010303015070800c809810241151101c2e000640c0c1050307803800c0740304540712301500364000c5c7c1c0c4220900130f520540f00c0c200400038509895401e00243c1940c01c1003425a00700ea100d640d03583c0070310060a400604e080b4411401360301c86600000a02d070700f0030b1040e0740d92074803810054001c0c00096403060007800d0f040782c84a088203540d00f002d4140d80840c0e206524040401c0c080004211410418208031540c1d2450210008403c10200040a1082d40d00e10b8445213003900c0c0310b0520301c12414103070003604840204101c0f07945042d030040e141901180c001e000c4002d0901c50301c0c40d40c02050f000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 332083138 1250 332081888 332081903
    0x7060f0315031b05120a0b0c270a05120d03020d060902031e0c0703081302060c1507030e0111040b0f2b0501170303040308042405090d09080a030c050307 67
    0x2c414441689001c10f6a0a842c588516000741c4e0340c0140300031700d02401c00031841c681091400d42d0005040c5810282c000b00202c5105040000e907083c50103404014643d54680c49046550241d1103003003c04021000b404111617583c0f001490301c040d1510345080300b80171410550b0006101c1e00081181d40468050003038210110b4991a110000700b0341d06100d406007807401c1040200180041c44480205d81380340b503156440d4141c07512280d03036000c420a127210301241d00590a22842c0201700303041255943c4142e01001103038403824200005002c80340321000c50700280c0d0412501c00f1a1261100c121011525000c10082e601d0144030b001c0c00590140d030880d56500300e003410a109030789207204030260766122840700410250340e80340c0d01504001080e0b411030f103942d00705000044c0403070700440c44075500c140900d00c0c0500100d0703024030410114113662041c84060340e5820034041c2c203490400c900720b150b1200381004000981400e03d00359803040400c100a0400c8503c5040c01c017002018025110f01c0c81d0310005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 332084388 1250 332083138 332083181
    0x17070501020315030319121b021b0102031603081305070e07030e060105010c14070e070c11030601061b030212030a0903020c0901180e120703030b15030907060f03 71
    0x24064042d5000781c030091400c4121624400c200d2602108458509660f40701245044403032034400d448008101040703100103903403584c43c100781c07580d140e00c65404403460358090402c15100743d5001d01041e40f9000e070030f270441d4000d10a545000c405200141d0380c090305414048460b5440000a8165042c0800001e089000340c14000070043d21b5113341500502164405000c0e00754402c0ca01543c95009115090010707815054650104243c1180b281d00380e9187d41c151408283c503242c01310410b00056900c1d13800036482c07003804014400d036615401c81c0240201e02910b0103514040008251483d00746590000c421440c091800b0117008000d6a030300c043c500f070842030300c03440c11900e42c4008201012064002d8066000c00c602c0c42e2030308000841c140c0d0412158580398800040d8120010071035241ca0300f94912a21160740c02811340c54002c0d150482c0f00795000300d1480900000d1190000600d10b203024450824800c1c4080b141c0045010820b07660a032804405080150000310090048500c1c960a04501e010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 332085638 1250 332084388 332084393
    0x110d050c16030b1b0a090e130c030b15040204030b0105040e0a06090c03030f020105072c0411130b03040506040f0609021f0906090311190e011404050a050702191707 72
    0x21203106103100300000c0203240205482c580c07207100d0039030200c0001d2046d41c0c00b80004081107445a8101600200803000c2403110b5454040703840182d04107480344140c11040244926186c13449015041003038030203506040c1303507a8405200d000103001d02407095880740304008024004006800903240c01c1030302030103290030b03074144070080c090603000560018144c01c007114a414014040c46007d0a16580c2d02042105003142c18a587c0d01d0a0451950a20b841c60907800c1c659224021981d00400021403280e0710181aa400c0c0c8003a40b40f035024000d0082e0900810010901c0802c5a581c42a04060f0f480c005601e2850098000d00707000c000250301121010902880119480d044400d241b0710361514008141c950300c0958404005200081012000c4080001c0c1401c08005c1c0500010102d42d59001e200d481d41c9a0b6595060240c020721300c040b80580740d1803024603142c00303241e03006443c40c00c040000d4100504000c0d1100d407502081d40e0300b44030800a4030304004106041c07000d00780b0003412a0382ca41b011032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 332086888 1250 332085638 332085653
    0x3011a1e0c1002032403030f0a0e1008070512040c05100e01030608071406070503090406080a0b0c0a08010b0a210c0305162106030203031c0c110d050c1603 68
    0x180750980340352003803009070385100c8607038400c40b03009001445150a125890680c1040c1c038031000030034581c0501051001a45049003080a010301c8144ca4881c0800e840c2441e090040340c41c0066150350820a18800b803054441c2c005042354070810100342d402e08141d85a042a407440d06107907110703641015900d058030307501590180100f841c8920903601442081d6035a01855540c04140c00303051124078114541e040c56190840003060380d207120f1000c3d80d04104c8148001421605a44d00c029140c0d00030342d0200c41007120440405900940c2901e03e6420600a010000c001c01c41c140290700d890140020b8111905000b5a44440c00c2c40da84000042141151042c84000e0301a0000030000310b820140402d103540c6c00008103010840c0700b940c44052800f100c050782c1c40c030446000d1136440d03500c3c0e0718840800507803414801071a101e01c0d4030308611000e01011600c0012207050b5680c1c9410000d0b00c030200c12904130040b5080030b000ca201d1030103944560f131060b011400d0003e401e14000301e80740710410010820414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 332088138 1250 332086888 332086897
    0xa02060301032906060f13050a06020609101b03180b251103070f0c0b04080303070e03010b100e011214070801050d1104200a0e0405010b0c0303011a1e 66
    0x40f14044001e803060601048200c0003030703d840e540040d050041d0980311000ca000b801e000805404000d0314182d0303030307008518003016a401150040c3c00060400c0031622041250a4288070103030410401d450341901c4001910a64502d600c04150320340d104140c4100c20004c02201072600700d1a41b400038200340301d10100c0c1c2c80000d480b541c1109269a600f00b00c2a02442502c0c0c8035068030006503150030000d0b43c51035200c61852108803081e00e421203002ca0449032481c003801c080c140c080015030707581c01c1910380904000e01e003c101c40d120340e04000d80c0c0c3d03c003611084070340c85000c0c0c2241400f05503802001c0c01a42c1110880300f1541c80c061030110f00003800030014428600031082c40c1c4820085036200d20902080c4100420084c04150200d0f14141850601e035110310243d104c1c0000f940c00750100603840401030f50101803800006503c070032200c1e1403450244111070046c850980781e03e02d13002501c0c02a940760302051051071060701d00540c0861100510750101c4040c0c400310407000303114405000e1005040e800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 332089388 1250 332088138 332088173
    0x90a020f0a030b1c1e0f0b1302041404032309040e03091c08030c0a0201020f070b0709060206010807060305101a0c1b06030c0304020102100e210a0519020a0206030103 73
    0x1c118140966010414143c0c1c296a81000c0341840a0300f08980346004409017040440729001500c15040101d440a9a09405041101d168002d810f207240100029140d250300d1420700550150107020000350401c01c001e814070500404090010003944210003603020342c50010360004c1c10046141d4264802000500114008072181c002079095007007001c0e50480f428900030002d80003040070031400500310015020070502c500c005460304000c1540c2c40c5940e003001e80f04941070041001400402504070b920036001e030510f0310040c0342c1589460031039a56403400e48101404e1540e11008102c0350306402040300c0140c8101103161450703201840c0344118a600080504040d07000340040342401d50026900440510700c01002282507448441e1000c0c0300d03a00280080341075100d1407a02d942c1c035594a009a44142c480700c005001e000408801241c501c070302c00720190040450422450b5001ca8201c1300350b400455864120507178204842c00107910340500309001030341c0407070044000010004a989548101c41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 332090638 1250 332089388 332089399
    0x207031b03050f011107030518060406030b090a110a0302180a080607021c090e070318060c02120906070f03050d0504060f06050105120105010e13050a0c03230105090a020f0a030b 78
    0x850515403c0c0c00c80d8400020040b001c3e00030415000403a10450150075284941c50b0600c07804030003040050200e51099002201094844069002a140c14400345602011a0205102004c00d400c800502449407025800c1419070100d0081e503180c1c9500368003805e90030003504031046580c9030015996540400c031340f8440180b248442580d954000e800840c14032180c0c5898908840c0e003008000210f581000303050104055450f07000c01c03820503098242c0c2e624540a8040010000f41c5e00000070300f01141c0742d00d54482060100071803283ca8940c1401c9420350ba4015036a42d400c0080c510301100c10707105000f43c100000381480f0910003400040e5021243c035a09846080003aa6030b00c5c00103503001e0080d5601401d03007401220041059500454030070601400040c29008000045603101d01156025501c9940031559017004c1290190144103008500c5100002e550202c1c04019040201c060140030740340c0181f903680082140100140c06443c01080340048460311280d85100082c010710142c64524400d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 332091888 1250 332090638 332090653
    0x80c01140f0a05090a03020a0803040611160c050607020f0405040807020303030405030a091d07112409060c030402150a17040f020109093605070b1210060903020906010207031b0305 79
    0xb600c005034401417241e06401506454019480324821030304000c10503900d032a150017102504503c08001006508007031104071440b04171600746520014aa60006c0340150342c00c01c0101c000d41d0b84c03130400702d1b940841100c000c180c03950fa910300503010340102c010080d018823000c41444104800840a401c880410345d842c19825a591880010011300018200f0b00034407001001c0f40074030348524440c1408010100c01c8a9040312000305c0e0002c04210f001c81003080d04020414440540300c2401515001544240b00c2421400e10f40c000404011300285401540d14002504c504e856000c0e44400c0c0212403038507219556407900d0f08040340700525450f0203d0014104613408103401c2c14070b11404444001801122016030104480d2516554850391107030003200c1c0e00a400d4000650400281029180c480f03c2d0b40d407074106100c0918240903000e419a0f03a40000d0b04d100f4801e00d640301c0d004108580d012074510700705803140b000507030905030365401c007620800580340f12900b0301050468000480384141d0440d40b01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 332093138 1250 332091888 332091901
    0x1181104050c0d0e0115060903060e01061d07020c131e15060c05030418140108010603030c15180501050619031110090e0a0b040b01030513080c01140f0a05 68
    0x440e88110b89540034988284203141d207840142d4480050501048000a00300072404008404c0500c03682c012070000300e08620900810155010780501c0c0c0f40548006e02c01c1504040301a0002c00c1400004010302c113a0b20009001d032882008500500280542010b0500142c680d0030405004020702e00175404441c015940c000400034410302e203014602c001c0c02c480160802c0d00413125030a689205440300d201c240000b040380800c04c0f45105200d000c140c0000340d5116880f007802c804c02d00c141c3c0b01200991421000300007003030304403022000c000e43c0328104400c420012204c10004000c10308281021600c1c4d1180c04040107415030090380100c034100d942d0340820701a2605800105103a00004212130200e002da01c1207810f22071020504600f00f0b0a00e400e0242e242c014549109408495802d0113903180e00b801040d904262180869040080c60140b1451520010305003810100f0030300144403100004032401d001034290310001d0420f00400a900e000e05044041104203d0244c488420340d92400e40450308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 332094388 1250 332093138 332093141
    0x1201150905061201031202070e0c121803190507060c0c0209011a1803030f19091203051e090d030c02040506061c0b060904090308160e030a02040905010e01181104 71
    0x1060700490f00718620b130313821a6039070040c1150301c50b5242c040d07201d00440400c801070200190303845000340364000703920f8015000c803601c2105c10103001d0100414204030424448800801100c502058071054000300420070042203c0070b00c0350460162001c0d180c0110b030021f95501400038034010b802180c00324900e903201c0007204500a02c88250504c4c0010811910710031282c140c001090081e8004d040d2400d00c6800d90150129900c4180201480c80c58001c10018070354002d038050000d0314089162420b180c90355035000c0c2007840340304003443c011481410f10018800300801103469020000e00901c200c1c0506141c0a0050b09186000300d1065082a000032110309080c010f5607a00000200a1015608409104030051070103503841c0d40c00010402c0345481c3d075101c902440f000d0303520941e1101480e04d4803408403c4101d0320032140d00f04101c24424410661341d00000d058131303043d404642c0091040f40902d0f142e40141025120500603500340322035034005d801110685405c85010301c0c1c00104503403e4608010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 332095638 1250 332094388 332094397
    0x506010f02030406211104090c02010209010e0f130c020f070504022d121501031404020901270e030a09060c0b0f0a020904050a0b040e0105101a120115090506 69
    0x20041e441480f08100a901c160075007442d02041307140795082c010103040003c0076900200003240346030308006001c2000341304a12440d0815500d03071000f18100001500000e0502c0b424102c05071081d4142102c04060340c4c0c0c0c5030a1321148490550f4100400e140e04c2c480a5110384002480e1503090191030800600b606141c000c965002049102d00541300100c04842d202c02c80401900c14000d038014050f1001e2030098500440c0202c01c96000641281c812500040035a800420b20403100c1c2140c105020045c0ca819441034192171f055644c01311600b400d4400c101905041c80c01c074a1100c1e04040402d00440300c0800100104452036440225082d120441500c0400f6a00801040c8254000c00034170340300340f4000c0e410b40108281d280540b4002e035907400034090f91400d5a40b02c050560300c4d1148805490944644c0c01d00900100080c04030703141c1b0064000b002440c502c00e580c49a5810789d182004c1030011030448041e50144403401d0706a523180c003141f40c0140c06400040000c10351184012035107181510548 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 332096888 1250 332095638 332095667
    0x919050a080604261308102d0e1002040e0105010207060207030b0610121b0305061e0d051c02070302091005060d24030b091005070c06021602090106050706050601 71
    0x9601c4182845180c803074030f00c02e1403c01007200c03051040102c142d00340c8503171500520b06c020040005d4054a070105048400f400220011100c9510740101e418480b407aa00861500101d000208203034080001410406070b012180c0b02a480002c2c04a00200c6404e0903505036a003ea00311030045480e03200aaa480c20640805001142d000700066901e2070b0500c01115004800c0c5410f0301101a04c00c02d0005444101c65002140c0f082c0851213810a40e262080660004040350001700a0300e840d07003024405510035503050302640c60645070302c0c10712000700f0103038243c441110020700c41c003031007144021b484040d6400200d114803025800300b840101918420026030f64000c00591911103440100c01c01050100320130341c14074401000c540114214065a84019401502102c079a403401c480b5803418a85100c108814071860b000920000d1a804224801700c07036802900140e4400c400102c20b040c07501c2d403680081d030000e400b0b400443c407254030a0140c084248104070034409519440010349003040b00e071500c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 332098138 1250 332096888 332096903
    0xc0303060f240327080d020d05191b1206210605060a05090c070204090b160207080105010e010303050d0902060304110108090a02030c01140f0301120b0112020117040302030919050a080604 82
    0xf1301c000311208007111303800d070303114048862401403c490700030181d8000c8a9015040c0f42e41e20204044184458014080300802c50010051005084030a20405981005c21400c01c40c07020482050503442da070102c0064640710140703070300982c0c0c01c400307001e840c0c8050441240c400b400d00000c03500c6810490394040581d02d0044c01003280740e660100e400754603008200140e030302c6600d6440d10408200800b0701540660050903040503400c800550192601c05030b54082c0131300b68584401003080801e156200d0b070550f5854600300b80d03030f0300040c0b86500152040d600081d50016000040c842041846401c66030f01c900280c0725000380f6600c513404140c035003021180c06501a00958444e0300b80b584150443c1149500ba81c865904052003541d540c240f80d00243c0100c07600c540010008424084070400c036500400101d85010f681d110b0302d9000a24804414041c4031450848401040c00c050091003903509070500540f104250411562951441c1356282c0b20300d90045038103c8010521000104500b440780750407086 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 332099388 1250 332098138 332098181
    0x4021e0607120c1a06240d0c05070c080304050405150307050910080f1027120306031a0105040c0201140c032a0c0709060501020c010c0303060f2403 65
    0x36880d2054a42c10403010030001a107081074005060280c90454040701c0d0004ca00851401005002840301204c003855a55500711249980c051040d00480d0002108142c010810250206017514140102c54000300a00410039010a2019000000e0011100d0031101031040d6100e81c012142d510645250b5550541c0184d0410310880c2414102e80d908480c8486c250010540d403541410304000e141c0b15210003a400c03400040c11084628007a051000e001521054200d5002c2d4414414035405c03180010035a09190800c3c0107500e0080d40000025030300308a42110318081000d4040300003109004540c4114a4a9030300c0300c0c41031052041c0038081412504c01c000d0750b280c204040206401c000d141805003488410150140c14a20380780c41500320403241500d4640085884460034642540c01001c001032400208112aa9000a1041802400707003482880c07034500f41021405007030207420680200742903840000d1000c03084c1d003d0b64000e01501c3c2941c0303000d003c40314048098840d80203013960908411f01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 332100638 1250 332099388 332099393
    0x7080f0c1603050d0804020114040f0e060a050d0b0403020a080c030705160f06121d030706050105011407080c100501080a02031b010c241401090c02120406051605031204021e0607 78
    0xd04840d001b5005041c175501a00019844a1459100c0c1c0c0041c00ba81e0601c02e820001810301c0d50525801400031112241c4c00c6045c000480e25048a400d0080c10410001b800708090500030b0144180068200149694520350451025a20340c007000080f00c1c1d9124015801e0020140c00c0b02d1401562402210103a0482c42c04400b1200019180e110121066881d03400c3e07400c84000e00b1110780c60083d880061034a9a42e0b9040010403914141c0c001e0741400f210608114200c0e07117880c125242260b000f50215280c1c100d0142040c0342c500d2a441440c1c40e81c0c0740c580007048607540050450302d000d200b10121795500a2400421404079002030481380425090504500090420010034507071140701e580c008003800c0e4081001d4242d4800681000241000000601a00325203010322071a640a0380020460160071444086540c456882203030108075020680303110070b040354641030200c0341e04082103136103030268903a14485501c002d44040313110f41501d42c00f2400e00e030101c00880c1501c00000313120504250454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 332101888 1250 332100638 332100647
    0x2060a020706021c0624140c0c03060711101802010f11060c0702100201090b070503060a121b171023150907020a081e07080f0c1603050d 60
    0x5200480b041c41e02031203076643c000c2000300e0031014112011800f003111490a28800c0e516860300d04000e8520b643d128141d0712040c1c000c403500390540804c0c1d0040f5691010840a5424503c81d802903c0e8540113150a1101d810351107441c1000c25411078043c4c41c1c14140c1e00d1690b904491452403900f42e80d9100d80192005036001d030703010001400c91030800e08240111050300714200301003152440c1143c1404038000e010760a000c501c22000b03c2650000f0403141c01251540c40c108080104040e04021002000031401d031981440080180a480340144024025242100c04003a024120081100c030400c0c0c00100340440c0c05000c5400e804503409007102c1d81010590340d0140003821499a05601c54540410b9042c0c2c8080707605108070312885425100c0c03286a810003082c4400a01244d00710340c011807501000c9503d507400c4944000300009580084191810340c14480e020341000540030040100b101d950301c0c03044c0d200501c06a003a60302541d0304102e002d03800030018030f020b0001422a07400143c5488145006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 332103138 1250 332101888 332101897
    0x601031202011b0203041404051513060902040806091c08010e04080f0406030b04060e061c1104090803090c060f03160306090e160b3603061810060602060a02 69
    0x51002181c1c841540d200c0382d8443c0070242d00440103910020f010003100000d50400c0c81001c00c1110b043c040c1d030500c0e5569018241d0903a40017841131a00310000b214074030355a4454070003002031410030340d11386035211a007648a80c070880e4440d405010b6016010074131b80300c255413080b019509840d152020790038056a0000850010400c840c550000c00028100301070100140c4000c110302c0e40c1c0440c010194038144400e54810341c2c800e0701e4a00b0000b050250a950b0310300701400010100d100e02200f40600d080240054480c4024280c00c5440c100c032410611591800852245222404481c100b80b143d4082c0556445490304c0041445000e1000c1b40c000c02100440c004052118580842c0c081e40381c030309180880f500a008800e031680030300755500701038039070840030340007406070007040390406d907401a112030742d1411103000b5002d90100c017045c01c1c4001d4121a08031550840038040343c1c001c1c078060840d18045c8511081e84807642c45101030315000b2441034090142070380c51075400740009454824110010350007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 332104388 1250 332103138 332103173
    0x509010b06220f03211d010e03010209041104030b09030a0c06020c0a0c0608150a050a050d0516120c080a0f12020304170c01030c0f0c031b0b04030c020f1002060103 72
    0x1004080040c0f0494480d41860103035020704240600c0c0440984c4148020340540c0b5041d0500400544d81401c2c0300c00d2843c00030925200b1308140218061001c0020300905c200400d85600900d004142048030700903201410030780e44941c80780b151030340302c03011903030707030340d000d400704040018000c3c0409134001002500501041031f0b00b50304440e4880315664408001203000d8020500203002d00040110304e2000840003415040107a44c440265401d0001180100b43d00d03001d03550280d045410018100002008909003501c0c000c842c03820050b0302e5030f00741986a960b510b010744601d5404103001c14500400305219403016400300c13041c100c80045070b641c801044078090021003540818071000900120103400c040e10449598050714040681c0030000d42225050304000342046a01d00009007901d030032030031045c0250740505122a600140003055060030700301c41d6008041c1003515041c0002c268200189550051084462000120b038400910405c450320b20359031001070f1b00c03820041010900f500c0c0000725909 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 332105638 1250 332104388 332104447
    0x3041505070c05101101051005010c020907020f030316120209091504021c0905010e0c011d030a0f080306010f1d04050a09021207060f0206100e0907080f010606030509010b06 76
    0x2956540098150190041303c0d070b01003880e00703109103001c000c01c0c840c881d03200c482110b80c01a01c6050500090080400c620003d00880310000442c800303900811101d48022284002c0300c0c0c0d41d243c80c64207983c9008290080102280000c01d1003982d915042c003c1c1c1e10300c0307500070b003a040159440580760a120140401041d030090360810401001540c440413010b5111050341c404581c1c0c00c020b24102c2e00b110340700c0c1045015500100d880c80c0701ca82c1e0160b004c1c0c80440c2c1c0c071111362016070034050020b814100165001005130f078400a801003001074041c0914419030003602d81d40104034030394105a415105100143c2184d0310b4108a030400d500d42070380020f4000c8404003000074960f00c039070701041c0101c0d01100218225400010b08214455100310349030302844462002e0201c902300350001e04d003088210300407074610340000400030f640140100808002400d04c0c0c4122450303010f0502c03089000f0865805804000f82c1400005001c1e00d905005144040c000541407a16051002a42071203003031580f0406020607 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 332106888 1250 332105638 332105663
    0x409020a091505030c04020412081e0a03060303120c02070b0a09030c0801050609150f04090323031008010e0706050a090b03011508130b150604030c0b04170304150507 73
    0x14040340324982c0c0c1d80320b46000d148071150400c0200751a100c034403c4000d00c035038010001441048108a550626968030081d400d840e6070a8100750300d1034502c104141812544045a100d03d00c9038550030101c120b0f07000b9100c0d00c03580d0513401c139842e00f540e40780c04880c03001d41c1c055042007080381da0100007410070000170704d06079060a03129620521a40d1280e0701100f010703074403a02403180c1498004280c0303030814500a00c0b0480301030170030089a288140302195138441c036138074005201858095401c00c1c8075481d800540b000c0004490402c44200e8000351141001d02d9603e10021460020500c640c0400200031001401554640321080b901d652101c02807400b004074001c00020100700c02c42c00765010740780001e02e0750030003960710400403c8690001c040c1550064803404500c08505070400058100030b6908640b400703500b44102280d082d1180f507200804101c2c170640c001548404140180058070500010300801c034509038001c50f035074055400340c0354405006034002044030b80141c0007040150320500521644 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 332108138 1250 332106888 332106899
    0x11070b0f0c06130204060b07170d020903010c0c14030705031801031805011a0915150c0f0a050c031606050d09080a0203070c050603010602190c15050c2404020409020a 73
    0x9210007030340c000d0010b00310307002d0300e80c214031701405458041d000b5a500241081d4894a52042c041c4003c44541601c007400103504803504810340499500f108090000c1c80458a41c840042000c07000f00d606803401408101d5000b06814040b040381d0b04140c00100940c20201450101c210402180c40314906159640714920380e0100001c41114071140100000a080040301c40e2103010139811040c00c034481c02c41d2104211402c000800080b84100c0240e46042840c0042c1e400401789110b0368803020741d580318130401c1310790141d40007400c410010b106409803035078501100c0515603943c81e0a203504092551403e814050b0a2280000e419018a0001d02040c1c0d0318094641020300d900c1010b82c0001a0000508401400113140801d0000c010544200c0d00e190702d8000c009442c1c2c0c42102002d00f10b061000d825074140300b680750301040640400a034072940d5441500021744240d1040394400c82a0040d00300c001c2c0500240c038280c0300390806111a441480d0380341e5003003200034a20a14100c0c0e000c203082501058 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 332109388 1250 332108138 332108143
    0x30a090b04030503040c1a0406081506040f0602150606090909030702181f051f030b060a02010905101415010201020c1002090406080109080f28030b010305010611070b0f0c 75
    0x40c2d00035121035959040504048000310416000103c02d16403910700400c44000340002c55040303034140c5c5044c1c4103940310444940c447c0910f9440050f4070a0000c03801080f2000405c42c40b1007210001d800b00d43c200780d424070920000d0300301217800790782c05801032101e001981001d010003036200314580c054919068007a80080c0d11020034140c4007981007448000c00591800009001b0180c01c4050701d400c100920300000101246c40d451149000903070080c0150404a00940040058a0000b000c50743c07100d10140c1e000b802841001300030749040c883d8041c1c82102c00780030303c210100c034552a42501d40542d5411000e924004039090750718119075080040300142007050003c00c1640d1210840175a944d040700c410030007955010741040d001645024001c00005011504480d184441d22070b040707480d100368051031000003196221140ca801d650904801c03155626a200c4004d400c8e09032020800780c2d8a42404a8805015894140c880d0740300740d10a000c0b0000c0340d0080c1c0110054009170f50701e0a14045000d90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 332110638 1250 332109388 332109391
    0x315031518170a0e191a07080f25050a060209130c080405060702011e180507030f0204060e010506070f0809150c0601060e0619120c050304171e030a090b 67
    0x402e2102050007a00740e5404629240b1006080350107040828006980150609081c0f0078001e64142c008550141c2c601c810040d21089504407103010348880010702000780030380c000c0700e00300c461a8500420b00f001c0c140c05204100c101e0f030800300508504a6554490000f54032150310b8030741c0301500424204e2111801e01666094010940c3c0b402d40e182418a001441c2c450050700c80f80640e4181564200404902c82e040c5100306038008c1c0128914150702041c8240d4044040c01601c0c9005501d40030041c8444900c51420980c421350301080110366400222090302820f02581c0c1c3d01607803c0011380e011403000705110521a0240100303600d080c3e007000005041584880001900e401c2c0030070030b210480014000719006290074100f41148115142c000390b06803081806c4030300c2c1d0030300c00700f80070079079900c10003403203c1c18041d84d03008200f11301110704007420300e0304215811075040800c8458076181c180014282c6027460500501c1c917451502d80700d0440c01c0d5800042c80c01c0903003a0749442c200003044583d028907 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 332111888 1250 332110638 332110673
    0xc030f1a0306062713050a0308070807021504020607021201051018150b0703030f050f060f010903021c0f050d051209070b09040504030216060509010315031518 70
    0x10034480c40401070600709280245440d201c1c3c03001c0e420424201041d0f03201414096403030820b45410350748000c4c40c501008800704020f07205200312413400003016088101603018803813035103600c070302642c4803a402c0740d580342c0842c540c008544d00d60000c6001800c120016203119407008001c0d8101e00c42d02c550880c21140100d035581c055418102080003d4050204440010080400c080c80302e059510340084100c1e03008d01c9103c00f1402e0000e1500281442035011401d40742c01000c0c00c2c80241030a6211202080341900c150340300c0c40f00c0340f248070540e40c06202200100e950207843c40910503105000482e440e042c0e4030094480c024039500007000948140040da00d100e00310b4071002c0d1501001c0126a895810090a6040320b9202000c00e000800003103003902d440002c02c80700030070507565601c0c040341030052509903940c03042ea0110000ca11590401c2c00340c20505001c4c0d030100403c1d00307082105980703001e4610000c0c0140e061919050344544150700400c42510a5180c2e08904924554410442d803034601c046 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 332113138 1250 332111888 332111921
    0x308160210390209061302030f070908010519020d1503200306090a110a03021c030f020c0d120201230a1103091c0915050c06070207030f03030c030f 65
    0xb5014800a08094110300041440510000250000c0d080b55503050a070184c803e24640b000503d150780c0f07192035681e0300c0741038030010b5440303040c4942c0a91400074103031480320225145004c08502c20b081403140500c1205000c5030040007150088402000307500c800d45036958a5140c1041403400182c94017818006c40c401c54507201e000340c040d021845da481d108000705100350801c109101c400000050f0f038107030309504030304083c000100c05000504960481c2d40001d4208a00b0340b28030007484188500c0b0070030a806525000100a20500100d803101c5100380c05640c00711540c40e0410106400105018501455000024405941c01c1e11030300b61540b260000c075038807a800010003842044500072085000d01c1c85400c5801c6041c0602c5440d1184640d41d011321070b07660b235590f903896418441e1880000070003c501080d480790180c83d1004159a01509001030035120320350104d00c80902c00580001169008404003405441a503400c41c042c140c040034000c00c0507113a240321309110900d407080c0300514000040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 332114388 1250 332113138 332113157
    0xb100b070309090e03190513090509011d01021905030a0f1d0f07120204050916080c0f030d0206010b0703030e01060605090f0d03270306020d020c06010e100308160210 73
    0xd5540955040000c2007000b41c1051010b810b1a40b81c1a000902050301420103a88a145c44201041d003c9030951100032795908117130a000d00300c3c0f011f51004112104100d00c080701d040c04145424242d205030201c800802c641071040315100e5201e034010f036400103e2542c02040d42d407000e987c0741081e42c0380c6201c4000300a07046206035082c40403c01c42082115080d10207058031600e402c00034000404048806409252140001440c03e001030100300c01c51807038074400640f403989070000d00c1c5e074652003030002030301554000c05844440d240000e01c403030140c2402c1d030042500307a00f0000500d200ba00240811018951a1211185500d100380651805061140e9032240ca49207440204001107140072589405603240311082c101099004903107914a200b84046495800d000c40d040c80c01c500811f50001e400c1a101040c00d00c0515120740082c02e141e440c02d011662a80d0b2110007031222094141c502940034032070324074104006000c00001d050000324a480c16502c982a40e00441e9480c80340c407641c000018010300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 332115638 1250 332114388 332114399
    0x5010e060108120d02091c03021b03010b03061303021c020616030c0815030f06341d0f03030c210703140702060f160605010e070503040b100b070309 65
    0x100107401406803100070032001072200840c203118400e41c02d60250054001130051445e031121808900345450004003440342d1200380c1002034955000c00d50400c0054400d208403013461505011b2191902c00080291103e40c94101c01d4428040000c0350071001c0d80150103240280c207928898110020120b60007800362490031007036501ca2403030314041030b000380f503e80aa40244240e020f000e01d03920078020669507280e2100c40300020b15144014082d041503110320010401c450500d103814814104141c001c0c81900304074140c8c1c94103401c0c12011035030000f5104a00055180e6400c0c0b90441300303568040d1410412816110109040d9481403241d8800f5500144496005400c280000148441d00190740c60a0249903900206295100c0c40c50011504005c1402000d6580301070440f40400085001c56035102c1082c040000e607075200040c1034035201d190100010f291241c1c0d0488511482c2695a9140b541d960380e031b00c282d42640040c0100c1d0541200b4140811042001c80c01011050b000b40c50341a00240b804 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 332116888 1250 332115638 332115643
    0x8070317070503041e050f0d0507060f110d021c0203070503090705041b0c0507090c1119110603040614091b060702061902010e011b0e0a15110307020d05010e 69
    0x60008002c11908004000c00b01d100c05040c415502800500c00100794000c0c100a49400840c00c140b403220300442d0304000c64150844024180d5910174842070080d0008030b5511401c41304429181c090f40042040040c441e42003da0086c00400040c418000c4028401c00d04030f4101e8100f1a104000b0070000014040241410070803c4000c020445040c8240700c81c02c65007211401e04c3c009400244400090303603004124050002ca005071190440400c198500c03000010550402101e1651460051101c285e0504034188942c51070b80d07400010404407020118280241075200030410b4400719582c0c21094181030a644120b40140c841c5002084021800c41c408464000611100751054104200c1b03140161501000e0741c494041403280e120340e41002d14002e80c0900070400100140354170b0010f80c2943c9618045041701c1c0f07940c0d50355601d41c01e000d029062080f140542e020785140408021498854140302c0d0304854500c11a8400f5a800d142c807540c0402c9042c528802d0440d075503511112100c8000408 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 332118138 1250 332116888 332116891
    0x1021507080613321303091a040504090506010302120d1e110714100302090312130312020d1416020609130f0504050c030607090e22030306090b0f030318010c08070317 73
    0x1750f0741c000351014082e9a010706400b03928400c52a451039401c040c002d03035001580603200100300142052205008500d05a0345890090008922440c0000c00d040e183d60b81c002450000800d03141c03206100d8082c10884191304544404640f0f0030402000b10a032580ea900340820300050036080707200c2e0345d620490703820030840c00038821581040500c18402c00030155000207014040d401505606940ca02c100d0071040101d008c25080901040454100d40c02c560382d00180b90800c18480d40e480780c0c6442144039401c2003611469103409510413000e06180d0140c071300320005115445000f440754041c45000300c4080c3c10b07030310300d01804240750350795000700030500806001329004100c085016255901e0080405880b080c12030160f40040c461040018080034074420100c808980074000c404100992494000c001c2c0c0800d02451103483d040690181d001d04000e00180354045000f006181400c0b01000f41003201074640c94014100035440040074080f502200040000034040c1e501e4080d82c054400140030030010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 332119388 1250 332118138 332118151
    0x8010f0b06040e04050a02030607020607090501081302012d020f010c091a070203030702180901110306030d0e0415180b0d0f39050102150708061332 65
    0x92185444503562280c040b20161641049005420b45803828101e280c1207541d040203425112303a605001c101600001e1062085206584652003107490304011a81807034140c1e41074128414080501c40158012040074100841c211080c11070840e509540c0030900800a00d282c001d0381112488815421081c080c103110b8001505000ca0000c2c50b2502c0b110002000d03c0c0d0340e0100c020301083d401b0442d503091041310702c01c0e03400900303520040e14040c64804442100b13480f10f03813441d03207000102032024602c3c5060302c0c41044010094006c4021a040590f1800310401001303503c183e0314001903400b0a00c03500c11802801148407044418000c0804042c11140c80045032407081014420410000703040718440600e11750320003d030030f0906162240888060107006403080040400d80c3d8005034541e148a08402200c000341d00312400c0031080845d0000c40481911170000180d041000940103042c0030580d9404030348070000000c1c2039102015000c0c1c0d940c00303058080030a101014070103030400100c001c4c12900400c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 332120638 1250 332119388 332119391
    0x1b0e0a0203092503050601091b0c05010e3414010f0c08040905101a1801260603070915170a06050411010f1b0201080705070506010806070f080103030c11060712030608010f 75
    0xe400c80d59409c81400f0a801001000b40108401003004820341141d90280450012a801500390f0342030380101610000d0000031080042a41e080f2072072500340040d04030340c400600c0580e0300c0506401101c00c070351002128024082481400310029980800901c000d180d8254000341d142429110903040d6450b030303072042c0c40b8400740107003510450319240100c0e0071540201c82c204641c540600700503140d03034481d104a41d489a0030102804c140e881d80311025442420102c0541e0300b000e40395411581141c2e000449aa0351030120002440180007400d16500c56202c10f50442c0c0c0c62400c00d50365002951012142242c00e020400050840ba5801118007145842941006920010007403441d0000c0c0c420100c02070f04105c15500401c10071030141080f01c1c8000e4001c01034031010343e12005030a80c0c4600640b8103d001801d080d40000515120704c9040d41642c1d07141d600c40d40c41c0b407415255500c070303444100030310341e40b050041103d080022012a0601c8502001307440200e4000d1814050382d0031500110680e080c0c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 332121888 1250 332120638 332120651
    0x40b030f07020a0314031509090f060108010207080306040b010e10050702090f071d190303030902090604060e010303120216050d0816050417010e070e041b0e0a020309250305060109 79
    0x650052440b83e40000c1c10843c0d00d451751fa0344041c031240480d00c114516005a8280103002d08004081121010101801e0442d0410390b80c44401500b02d1003400c80207441d4a10502c003003030452906070007401c3d4071481450001d81da005420006290586000408000f24400140007411400c1408040b80d002c00418880c20492406181c0038207000344400b9690844a40c001c01400240e50360050000c0310260000100b43d825100e10b40540100721100041c0c3c0b06981d0440028420316044c0192410381e00c0e030303800d512a680d2071aa07056550406102d540d07150190240144180c0c400b8850040303255a00440080421042404019004110160503150001c0d403141e409082142c00c0002c40c4c0444ea40301c02d0800502c10b041c5205401416150303084002c03802840000943e2900341c0d104580a0781c0140e890700f261031a04150030700c00301c50510517103062310400030004607010300030340c00386601810310b1040d110500580e4031009444500f07540c000d640c070f801c900710078070901c94204415030141c01500c03002c100c01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 332123138 1250 332121888 332121893
    0x1080a060e0f031c0b0f010f0521091b0d0f020d260306040b1f210507030605010f030b01080c0711030708100b040e070b0c12040b03060f040c09090f11040b030f07020a 73
    0x3911901050701d42402400281042b0800c6200e1015541905001104940c1d00f0001a45900c400f00e00c100380d50302c1c024611008101d0302e8040380f80000a039000c40c100e0301a00b6982e00340488025540c0d800e440302c00c4070b0f4003074140c01c800a41c040100b0000000c02113540b4074045040001b103502034020700d4010401846070b05035160344072170700786440105801c00c0070364000c03c009202c1c0b03c40502c5409240c0c0c103050400f8080300d40c0e0142c000300709448090303d80c412980705480044088501d412240c0e0700107500e08001c0f4503520b00c28401031003098010203403000522450b8000c28500707650755104102a41c89142900c051460300d100d4100283e034120340600501401c4a40180e440705580201c2c14034000000300c5221180d81048800b0130348203204401901d413540c4103003041958008032402401140209662145403500c2d22641c102c9240680b034000c01b103400e0160300d2004000c0750550310364241d510358290400204d0300020740003c02c5403941140d503a03e003105c13080c0d5241070041c10513415035100d200380000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 332124388 1250 332123138 332123147
    0x504030b01140d02040216080d0203040b01060c031d06070602220902070503181f031b050703120902010908100501091a03060106111501060f140301080a060e0f031c0b0f01 75
    0x21010740417034015848001600c1404209025500c0c001c1c1800e40002d030480301414160040d52049000ba0302c1c119183e0b80e503160644041c0c0d900c0c40018002180500c49295140300440c5011703590201030001418040b40356075010483c2d100350060000e281c44a00c101034040c07031400e0b009020342010705c0c0039800d00540359181a660301440c010418000140300102c01e460b00c1d004000c60321390640c4240e052441c0581c0700c0140040103404c01c140d25190360304000804450199048a000e43c0c1e155694074000240491180300400400300d0483c10041c1c94000003c4500040080d501c55443c80c110009080d45009001d10031210b80e039041190860340302c04420b00c10368001c01c14a0449101d400c16140c0710708100556403d0248000d641c540c03002c0041d00204034658131a07090610142d01d501c400030340d4a40b060102d1080d000074491281030f40e01c101c0b40701d00000d8094000c07207100c45080301250003072800592441d007107801030041c40500f8619900503072184550f60040c5e0007030200562340320a04481c0b80340000c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 332125638 1250 332124388 332124409
    0x1201060e0f090604020d09150b300a0203010e010c0e0a0b07150209060f0c16080726010f1b0503040503030c0309160602030d0e1501050114040b04060504030b0114 71
    0x20320602202c00060031030385594048401c0c806109104022064552415401c841c500e01d64620919144c8213580c2c4843c00c090380c80030345494020100300481e020340022100001c2040800090718060190100010b0305c090158000c003580c00c500215005800e103200410100c0e0f0b03500c0c1c0c1886084080c104000b151103401c2101c4d138241c0c00441c9244d080c0c2c403841c10300010348581030415404ca14001000100c40038000050022084200e0907500640c800f8289010b05000a000b00d50702500f03d0202000390b0501100c4201d890180034801c81d03510b144d40440c5900f117500301559242c0f925102d8188100209207000c0d26074035100c640c10a50304600709178481c10341e030f404000d04942008400001050402c1030400a100c070007001c00c034004469680340e05009440703030084109400251304002140c0c1d840710000c01d000059481459074587c45a2900d4011a0102030f0241c401c00002010440412343c010418000d0010b800d50f80c4515940d2459454080400001688407152070740c00141170344143c4d9a00010b44 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 332126888 1250 332125638 332125669
    0x6010b0f03070504030503070b160e0a0605090f04021303050d110d030c090e070306050a05040e0c040b01110d09030215030f07120b060711090c070206070b0a090b0406021201060e 78
    0x90384a60300c214003903d00348180e81002d0407500c40425200100040030742c010703202e0316002d02c2100c0c00040c003100690b1400030340249198030913003981d800e2040d14482d0300681111107004200c03403411041e21000c5812a44403028200400c07000e0141482481000c10800070f84218900c2c0a18030354481c0303d4407035121201d8801c05405c043d01e6800810f1034607c241c1c00b1102410300f40c1e10070300c82401e140c040680146010300c9142e001c1c5100c03a80009007440c0603c100c850311a031b07030009007141003000000c22005008007807083c1d05000b40d402016404880402040c3d90300e400c0c0d40c4a408000c0d007180100061100d00080e0140480001c00400c51005007003c01d054005440c0e040c88104681c2c0540100050003400003038503004180414094103110903622131038081d00040d40c03102c66a0703c41c0741c010091032050740c0c006900040104601000502044036460f442802c041000940201554038005007180581d0207a43c0705d80c01240c01e800400003003100c28014100c509040c101d6040c0340700891200418070617803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 332128138 1250 332126888 332126917
    0x30423031e1207020102180f06040b0f12040b04060f021e0309010608031309060f08060628120218060a29130f0605070b010e04140109050706020c0306010b 68
    0x240c114a081400d40b0700c070a0014440e603120f0302d4400310080c002e41007007000c904011220f201d501c80d941807245000013052800340110b45001e04040390b00e07995521403c0c050402c0082001000404208039415601942c410500400181020b08024044c1c0d500505e50302c46c0c0a1041002600c3c81c507900400d2500c05200180080d200c0e9284022240180a154042e49450000090803107129004490710816a8122401049003580320075035030149c4001c60140b41d803641e100c2c2000c540986814110721f02102e076280407001c4c92031000d072081824001503030f1244801400c100080000c62400c0302941d000b81c00c0560002c0f9040c40c00400017080d40c50a0b00c034001c1034182c030b0300c580c480014500c14411200501043c40d01e0b581c2190081c0700d2508420742c420031480c202c46240210300c0521420403181c0e869044007004000d642003d032801e244650240044580000c152160b010007103082c0540b8034a60701031009040440d14210303001e8148101c4180300ea01c2500201d00510020110500ba2084603c01c0c841c4c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 332129388 1250 332128138 332128177
    0x702010309050a020d1101320702120316110303270409020a0e01170615011409030d08040203010f1e0e07050a0801020a020c01030b010219020316030803042303 70
    0x1803450400e07045507030217504515200015801c5c000b4410968007596002c1e6144144111074480c0000500c0800ca001040ca01c0380d01520046001d0000191005500080c0703001d903071080d07403180203255a001011000a40303421070201d5080c40110b0022814007102507014628280b041c02c5c079180c09003903841c84030300d0f0204100803a00c0c0c2c64039a5409403100b5540507100d184003036103450702008081d40c2407141c9134a212840722205455080403400f903002d03806000000720010201c90043d2108000d103580c4074044201805071144075501080f6601501d442c07a2540107160409005160a48041c4100711807801d00b0031030b5442105c405050001480001e01a000800c0d100c0c0414003820005a079200b9540007036102c1002c41e480354194001e2200d0850764084592151031040103400750b0f15100c01190158003d0031400d15440203442141d40c4940c801411b5a150710b803030080c001030070354050f0015601e110010040004004450702c03101ca40e0f10a0305100704001c1e071036451069032441000903c00c03200b070020381d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 332130638 1250 332129388 332129393
    0x31e021f2706020c0706050309010e0a0b16021f0203070908031305011101060905160e031b0103090c23090a0203040209061909050c09091005011d06090d050105070807080c0702010309 80
    0x341038884c40925036040c0d4508940c0e0b14002042900240c49298241d46010791440310040c001030003000c01ca0b48407500648035921080d90309800c4149909600039405101000540148604004814114651001a160304001c08014044c50340c2d6004144035900811504c600c0c00305e0908c112003114000d10340000c03081d040001142c05094660711000700e103810181440902c0b16040311030f604e8140250380b83e9111901d01c8003016500c210904e0100e03842d620708001d60340f00e5482a048421f20318060200707a2641d940d03441611304041001c000ca10050f03a00d0345200c202c28a0101002600088451010f50541c14203800162100202403c1144108a50081502e05000b010304203001032407506000c201a190102001c4078592002002d1407245c564007000640805045480405542c1d040c0c4d10b24000b400c81955540e4526041843c1c42d50050050000301f8490350390f42c250460b1a4031807030000c505414580381c040c084000140c0b104061010f000b04002c10100141c090b900440c0d0246000703d80440d590 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 332131888 1250 332130638 332130641
    0x1060f0b131211011214060112021605062a0d020a110703060203330108151210110301031703040f0f0b06010806060a1b031e021f2706 59
    0x5500ca6002c110300440198140418400c0f001d00240e002e80790b0707494132a945d10b0100212034110003551030380340c40e40010503455403041c03021001007070070b4150040c90b0000a51a1100407202560115643c2e4812010020b40f014410b18440071186040030583c1c240004510030030715405008a444220399000c074099501c1407241815a002482d0807050317139807281e100c0c04c00e50007a5108a4401c00f4580a0348001b0324172007000441d89002c000c010035402c0a01c0c044000440d402000a008202c0c0344506c1040c680032070740c070009042500038011005040c01607202d03070040c05807421044003d41081d0180010408143d44140c680800e4400d070141c1c0707a40e6a9107150000003d00039007805001030f004c544282c4104400541001e0142c2c4090320b564076613994030020846a88200e402800010300b01c42d001100c001180c4148040316480b9040240320f4800c002c9000e60014041c41d03030240107910100b002080034100514030780001e0903002d4203022480340d00c101c80808030131004070700080c1031103180c0c040107010030b0703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 332133138 1250 332131888 332131927
    0x60c030c040f18061202010f0c17040915060e01090b0a14071208010e1302060f12070909150b030f060a031e0318030b0103020d03020a02030d2001060f0b 67
    0x112003901a103261203c0d01a00712480f044031120040d840d00b81d01141c1c440009000445c40f0741c3c160741c2c240803a03003c00c87c211a4241c00003401c46c0d807141d60a441c59008036442000d000684004035001401414000607070b651b565040e800f5009100c0085020309269911640c1c44094440c03401a480c0c5d5900038000c21100880840f41703811120802103614001c2005000059844c2003941c0e032009690b903281d0281740c0c4170030030030340340e07500205050f2001c00018140344014011541d0f40c10b6605081c0901100c40b0035417161b0482b49440013610283c0140b100400303500c0386c13084004200e0348440b01582010182c0810b488054007200741c41a00000085035a510694968040c0d903010201c045501003090420400982e1100c0441c0420341e504094182c0c4401c0070600c9007120340141844000c0d901c3c6400b8001e00ea00214030680445c052056a035000d80c42c03c014500c00d81503107990300c242d800c003201021300ca000038078072540d0354990405604210a208250480c000c0c3c88000d03071080c0e070b0f40060800e02201070f00e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 332134388 1250 332133138 332133149
    0x624090e071505040806100513050c0406110c150403120f0e130905161502120a0e060d050118050c0a20030903060901050f0601090e040605060a0b0c0106170c03060c030c04 75
    0x80b10704100d0624004612581166015074401410b141d03800808418ae813411201c000c5840d0080c44100030040c4211001da02d00160b01e01600d5000400002184005509262403803105c1d03000582081044154102001c0b80c1650b441c10341c03a84480d40400030500b0b00d0343e01e07089108041342048544245070036804000d00940c844101c0d219080e25115052614400d0b100c0c1c05e002c0e0100841c2d040c80c03140040b59040c6180c0000403054500719029200360740d101703d0b80140d40d4008809004050008041d4031815020704615034a15211210200c015016550001d26a82d8203840600c24146850b41000341c1e009440890405001c02010b007129562440c0200d04100b42c5c1445510140031042006500403806003500b460070300440c3c2da0300d500540d41d8000911940e0b00d82c820f280700003004500964001504054020003041629a40d60710b200e000f900650030007055070755035200801007102c502c184018250341a00180c10810181d02c0085e442d601c0080c4003100402001000840303040c1000c048a01400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 332135638 1250 332134388 332134393
    0x304020a05030a050105090f120f030c040513020904151202040b01110a0c030c0f0509070503060d060e0309090105040506061206030111040303080106021917160624090e0715050408 79
    0xd00f2410264040e040c141c035003481600031510074013290030001c00c091030105401c000c031034600950150f0006865000801c000c0d2000c006000101e0b02e07076145a000004000072840c00768580e241d6400b04021030b18050685000c011070700c9030820a584011400b5000d064040360300191269140c801618451044100905607000b015900c00030406446001402e4a0290000f400e001d41ca0b0010840075070a28020700d41e00141d40c00000e102d03a4464001140d008201038103800721144165a002c040c0c4070b004d81d400500350804102c40346203080070341c02e00380101350445e001c0c4442c3c2401c8003c44c41c0c0d40b04400480c0c501070200000501700f910700350482055a81843d0041d42c0c1e455903030400500c904002e000740c80060191200c620041a4400306d404429904110520004051203400c034030168882e608c030042e440b0301d400ca4240820224424941b044021910303410714414000c100e80c092030350640010084030328110090302154000280b4009464076241202800081030100391850702841e402004c061 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 332136888 1250 332135638 332135653
    0x301060909031125030f030c082101050a052b0507060f08070e0a050409020102030909011203092c070210060803090f06120411060f0301030c141c110d1b081507020a02060304020a0503 80
    0x1d0a010078400ac12000a000b000502d0740c8800401c04c4428051080b690b000b4907181c0c685d00c0030a4a004001d85800c034864041088006568a003414a01700307511404c0800c107502e0401c1c0500c0d030080d0b40c85030b001034646850a50426100300040100c007007801528001ca075144c4090b821a4000c1040342c3c4030300002800b05507550703034446180c0012120007038100d0018441d0880000c910501405402d000e05851200045445d21418003070741c51000140f55900710720850040d44c0170803100b4407468001d003600c00040d5941c4c4101c141841220199030f180070780150f500300685110144c201c108184c215600015a40c0a0a010000140940140c448035625141e00100000412070b40c44001c6080390042d0300312002c001d100c2c1e02000b03060702042100452030380941003840001800c07484203130b842c080b004140f00d0700d5103001e80b104038204101c20701121550746510414040800e081080c2c811039011001101e4880c50306d100002c0d22091107e00003030003600c000c8007141c21076131854550f001070b100c081c040f01c182 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 332138138 1250 332136888 332136907
    0xb03030d0f0608120403080a051c0e0d17190207080c030319021207033206090a110f090d060203161103180f0301060909031125030f030c08 61
    0x1d11841d804088824a0030800040180020030019164149124500e00741850358940821590180f03e980d010042c080018900e607103140000989800c2010a00050610310460120b2621341c0f0b100c6c42c0f034107104506007245203c500d050a2940c2c0b042c03500440c80b90403100800321034081e001e10719005101d9040400d042c01d241400001071132240c03034020713407200c103014500307100310101d01c01c00215010704110080083c100740d000c0c2c0c002c07013130400308d589e4480545060340401303080110514008882c5101031100780311103454500c0546801104c000010007000300e10340030b8040c0e80e1082030241d6200107004900c0145603a1968010000503822040a655a240040318858054096400c00001c01da5210171039011642c004203513219500c00d524008168182c2c8410017a159a400700300760f52544d2690004102c03104c007800b40308550341c030a44810806610b60440e0508100c0031582c50319203840304001c4247c1180d140c22a400c01c490700b00720400c01e501501e00381100c980d03040b004080e0440c00c00103100d031030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 332139388 1250 332138138 332138141
    0x52706070f14070b070606090213030807032007031104020a05032a0403030e0102100c05030109021303080703020d17090c0f01120c080108150f010b03270c01110105040203070314010b03030d 83
    0xd21718481c100411040d074031100a58100c0c0240740c003d21328000c0c0b0305000d00025070440300806171240241015490240c41c0c0d06040281d03241c080e11100d130703504070391750400410820b22281600c0b92000c070f906505240e40d1440003031090000a003110300c072f540000208003000460340c5920700002a000d02a5076105c0d10f0782805040441031400f17a60040c801e01103c070407200314034401d61050502c99552249543d1030b240b80c10020f9044410181c1142880c1400000080c0550000703000c9184290050700a0f80f0040401410a1a00751001c40f41902d01e0020042806808141d15a4244003107900405004840c80102c9856404002c2c41d44c501d4503140707003005803c3d00320351391a040700e501c2000c86143c10781c2030704480601001a00d0101d050440b08006010040800e80a507034440345c1c588011403884403400a0482c041d01c1c200803484d440c0c00900450758196400f07460b00030b940c0111b000030301807400c00d0380c0825034070552440064001c255002042c24004c500390030584076120700400b125212a0f007181c0e03410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 332140638 1250 332139388 332139397
    0x50a030807090b0c0a150e011a0102010c08160c03030212090703110d08030f060d05060a02040306110406120f150815070207050a1a070c06052706070f14070b 69
    0x402040b102980000c0c8545460125410741041c10040c1c8848035003940d80d01010410380c0d003581020764864030041500070702480742d082c0d02d041001c10a90542c941800190844000345030390402c00030354004200e01c030481050240f20008043c5041c294002160400310024040e41000d07040c0075000c08140a0305120028040095038005e100c80c40321035104804200b1010200d041c0144501800d0002820740c116903542141e1110b809024030103550000d585a40c20070104039840002c8030b074042401e009000d0180724440e00c2c54440503042d45400d0601c040980421414603000b6502500c81c3c20300f0000c0c1c203e54021041c000720504c0c08110700d039107a0304003a88441414141c402d0381c0038140e00082c036040c800152001200c0024080904241c1811511409541541040c20481000300038010018131845000c500a01d601c5d9129610b502482814000ba41e02c0400d42d4a0a54549040b01205039100d04c122803c26034001020020313040300d85414a89910300c01407240b400d0062040c0001e0040d42d100c020b0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 332141888 1250 332140638 332140651
    0x50409050117060130050703020a0e07020609010b0109050607060605040609020a1101090c05061e04260c13091703040503070c0602071809080c06091e01110702150403050a0308 77
    0x880d91a17803200300f000784a020000b04400d80780b011001580908641c020020003890198060341c2c0003903102e40107c0d041030f01541c05000501c2c02c4404110090b5414000507030464031920007809046000000240b8601c090b008440c8030303100028904040100d075038040c40080401400a0143e941d80e203031501d0007500503852040100e030243c140034100640c180b003950072055001032040541402d040c14448141c00c03006000c4411944640020441803554006c0e200500c2c18a41a001d040143c1c0d075103c0380c440c00310111a90503481408841805e9481e01c5003c4110b061440001810040703e08044251184603200e0501c1d0305000001c1c40207018001c0000c0a081d8003031a100198559200c1c4120f030355403114490084440c41451088074000d00c1e82e00000b140314040c164907418000e0802440342041d405071145d0415a0290320000000304512840009550000c0d00030803103080c01480e10703801840340540080c03041d02e2034076020003007030786e414203840c05140c104044072807109030740ca0080c000d0744050710003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 332143138 1250 332141888 332141893
    0x18060501090b04051b090d06060e04120c0b06150721030b0306010e0f06131a040f020f071101180909020306010f030f0f170a030203010f0509130b07050409050117 71
    0x10100d46041c1030044a000d00070300303107501650316002c2003d81e6031a00100702d0721fa0f0244242d084500400d007540a400301801000d000d210301402d01c1d10b4015102d4081d100f2080c00e00150700c07048804100000030081d44184140c80416985040d03544211461042007401003915542d01400c03e500340001d1085a64100300d91410080c00c50488c00f015581e0070240706070314401c03000c1b2000445000e08101010780000c030103172038580b040c00030f141d0729010743d06045248004040300c10400345151420380241c49020320b0303902045161003a88014030405220340d0402400c0514482515059644140c0c001e03440c43e00d48c1221a001c1684803031050300504810201603101e80b0400d07001082c3e68010a900800f201d034000000c0540309210394801e0f000c500a0907080d24600b0f110402d092501508030300400703c226140d600140c0d20740c184080b000d215141038100c0f500510145c07080120700a1044a01c00c0c0d002e03000400c04406a80300042100c15100302e4010b800d1083c101400040e0f14001d04260800300c03ea60b506 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 332144388 1250 332143138 332143151
    0x20c030c0106050406050319020414190b1f21060602030414040b0105070b100b03150103051303080f0c0d060312020d0c1e0305040506070305070302070b0c070b0c011806050109 77
    0x1084185c2c0c00300d015150703161304000308929101442481c502d01302c510140c000304103078940c4142c01e2151720341142c0f00d1315400a0b04441000402c060320070070b4805541151814000da8082c0581354006801032541000d110520220150380c00d020315541d940351400d4141440b4031500c2d901c009440e60010b22501b901c2489400301481c6615041c041c40790b881406940e400e04241041c0c5604896610240030b01d18002014940803690700501c4000390300c10810b0081d48032503004a0f10004080359001005a0041848210400c8c0000d0f4080c0003141c21080020403a515511500309000744c92080690003001c49290090010030010350300e07103a1041130029020360301740d00002c940075601c004c2e82c0e000041c40e80d50030711403600710281c5541d4070f1b084c42d6000340f074110306090302d65000c1103c59000c4102079002c950b000c90b066080640c100501d00240c01e50070821400e05815461155407a2201c1c00780220b107440126221800240c00d521040c11f82c0801c19179000382c1101414690018082800f4901000e0308100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 332145638 1250 332144388 332144399
    0x2040f050a151a030703021b07030b1905040c0302090403170405160e060901031b0b04030f11061c050a091a07031802010210020a0201180605311b0504020c030c0106 72
    0xd903e04001c0c40c1c1d00503840c607503556130808800950124054a8844030001d5101381208070400986016521414000b092801d024000b0180c06800c0400d002201d03003440700b00030010302c070112040112030341911145402c1d00d80b8a01520300e09401120f62412000c140c04200c14003000054244034a2a20b107098541c039038544841040b800ca045402c00c0d00009128010000076641a200004206415030712070740c1c0c191640106403040d0f22951094498010f420406003c2c8040d4040e00441101c0441b080d5142c100000045030102e00d00010303c211041c2d4400001c1d81c9007a03650007a6001c0c40d4070100e02e88094003c00e100e00c0301c3e10819070760400000d2401d02558a14000303542400f03e1250142c00808039100404403d0003e548003000440842d502c03218010442c2524030a000402e52042202080910740140e10000325007400d2036103140c101c4d08020a03800405210b003203a6500390400b003030504c10324100c1a0748131b0181040d400706400c541b002540c40080b440210240c0f100c12181c0e4000d03c401e9941f40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 332146888 1250 332145638 332145659
    0xb180f151306140c211b010608190309060c080403020a0329070c080f040906060c0501140c092709030406031d1c140703030207031704081602040f050a15 67
    0x24140c1480780d84180c08211915500c0b6000501141c050486640382c80300303440c50041244881006c070307005a034540c2d4041c041c6030710502084041380c0344040300c11080c0c0c440342c8000306060098403c1e1810300850440403130500900c0f8086402941d006410610b46a503289040503a6148144460701031040d02140201d041c034024009500070003040d5114480d1000c1c03510f5079081a80300c0141c58240500030000000c80404034014000105850303151003401c082141009425101480c4910003222285010005560034400c2034aa480744144c0d0010b04900c20000001c803811004422044801e803648108001007800000400543e8181e80c2c00f07100c40090300b040d041c040c1e40740603031030321094214002c10381500c0c01d4804071002c03403822403130980c04c0011901078682c940e5200000a4001980004461050507003101c0000081ea1191402d140e40340b5040d10303215040d02403d4803a44911f51080084419507996030070103400844003240401c882e0405003000001481d6401c104040800e13a0080001d40700e100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 332148138 1250 332146888 332146897
    0x30f0709091104171605060a02010f050c19030e0304090e0f010504060e010c090b0708090d080a0512060f010f0305100b0c01061703130e040f080a0f090b180f15130614 73
    0x440c1c0d01050846d00301010060b851300154008030840d980d82c8074110303070b4100500816000d4810000c0e02da5499610319450510710000d15007207001d060400e2400c0000314000400c07907049441c006000039612007440d180c18141b28804200c2c2080c1d42c208403c0c0010b1102d540d0101d1140141180204140c40074050166110787c414803405040306024403183c00400c1e540070090807954030081420030303610001c0c2d50b101020341040780c0c40800100c002c41c05280810811851075004001140c98604200c2c80780002014079117403030405c104158030b81700450321200d107803082100a040303480c90850302d071034ac180c000a0090040c1d100f20404141c007013011100d000c501104464400003580c002403509030802d0341d940384045001e0400c642000c46409060081061074000e42006501030396801e80b400450a002401c00c0d51036008010203020420140f000e001100c020320030018026900e040c0030100610000301c1c1c05221241752050a00002140d1021400d0b81c505c0c142503811507215454800c4405a20b190715018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 332149388 1250 332148138 332148163
    0x31a071e050702041d030c010b09010509010b030414010b040903050d05010e01030b0115140c0c0f090105010203071e02030d050a2d05031314070608060312030f070909110417 76
    0x20104010400f604103a04500141d10f01180c0802620341ca40360150700e541d210328a501c0b03a5940d24441c2440328580480d00b54010714003150b070705401d0b504084030982c13a4403024000034402d101c8402005c0400d0b20039040800384070001002044144036500303010b030030b5a100300f000306046454003002040c000007588406041c2ea8000c0020751300c40e800d180c0d911091001d02c1600d0024411950790858000d12810000d0040b45040030240a9140307192080c0051000311000071886001450010301c40b40e40e0000c1a18100d54105100004031141400b02050780001200d02030b425000c0e00c5101101182c00c5401007504000c0c550f12840a0043c40d91010a92802003558150300c3c0440110201100c1c0f06d08081d54102d44410301500c004c01881da5180d1022400c003280c04d2582e000204200241031700301c444c5644c8410f0a40190413402c000c0031105c081807000030030001d042040c001c00300c2c803403c0c0f0852000e0090040c510041085120618207409990054401e80300c99500da001c4c521620b01011600e21020b03031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 332150638 1250 332149388 332149397
    0xa091b1e080a080a090503070b07021918090314030405070e09060411121905010507020712150903050c0d0e122e0b0a0b03010501020c010c0506010b03060406031a071e 73
    0x300c80d030f580d100c0d241c0c40b43c4480d50810003090350104003030780d061051200a168804c1c0031170391102c4910501041d100b81c40c0384210356213200c900402041e0350314140c5020031951a800000d4180b55460181d49440101c210510070310008010801004000640c040c00e5490f07201010f0500e949201d2120394803072046078010400645034413000d0403814004161071001d660503083e107070300c02541581250a000d01c90320a4450741e45400600011035018843c00303000d005c800040180080341a1155140c40391650710348203d42d0703501c0030f120082c1031150060350340304040c01003550048000b112004103100f4038040c420384034005140c603110740720a0008180c0038100120b485603482d0005603041040048231a0150b244c91341e2500c507074803a1703076a0343c040c0013018109000d00e444d00da50601c80028a04501c2c510310b1410301070081c0000c3c0100b44000750150444220500c00c503900da55910103d0040c00b516440180f0350040b02d140d10b441e115004001911440c640d64801c10020a50b84001460034011100000440d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 332151888 1250 332150638 332150653
    0x61e070203090907030216230c010503220506100e0c0702030a0b06060c0111071101030501180902030c060712080c030106090905040c0f1805060d0206040e0a091b1e08 73
    0xd0420100b4194132900500780141440e01203005100c0203405444100ea0712481a02e00c424800c410010421101c0c2d070031002000060540d60003c0d22a2001070000f901d140d0a900441c3c2d00b8a502070784070790b501940f010580341e103400c00d400e2803040350745940240300910845000142c1c2c46405441600c4000d03030002d0041280301c0f41a151003010460180500380c00000030418100e408000340523032200746040040040d034441d22410040e180c601c0103450241050700b0000108011220020500030200712100e00007507900b80351000910f01101100802c3c1c003d0030106824080c1700368041b047c0e40008550300c0c2c6400542d50030040c40c4942c40300b4040c01c80440d1a0481c1803048607025440150b10502c00c100404009486007108491000300d5070110320344400103030074000408a1400741e1340d0030010030f54069640004030b500140460290740180b43c8005203420004500a00302d80001c3c1040c1d030480120504003d10281c0c503071400b030090044801400c42d00701d000f90301c0c40340142d50f00300701c40718000946010b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 332153138 1250 332151888 332151907
    0x209150306040608030307020f190302211c0207020f0f1c080403080309251202010c020f1005030915090c06030c1e040603062313110705061e070203 65
    0x854002412182e00715555050200c1e248004200450040450340c00070300c1c03c4100c030503a8502d0041d120f01803240b4111094208400642c00207400071340103141103400100b00012210b82c41d600d0040107401c0043d61260403540851140d0380d4010051580240c0d800d520020350041880030030008011a140c005a816148124007140440b0707400c1ca062152a80314901640d07629120856001515100c83c9500404040000b0054038000c02211189000403200700910b04203030341c1009a900840070741404041c24000c01159a0b0041005d8074110003001040607001160b0001d006801c11103006a1501c101400000d120300c01c0603005220b40c03040401042020240d40900483d80c0010700341c192a1704040c84410500880d1035a04c045800560400b90345551070201c00800303a0744507038002d06100e41c10300b00c0380b220135550780075114451000b41c0b0100d0303103680c0170a0b04400608925209289189001c50600104000805c2c2103015481880f0106500c00300a406906e12000564031900568401c000c0c02d10f5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 332154388 1250 332153138 332153179
    0x180303020c1c03200a090b090d02040203041505010f080a06020a110a03030c0806010e030a02040c03020c060f040b0a050c1206030f03070f022106070f0203041d04061a0a090e070504090804030507090209 88
    0x40d4005427020700a881107030302042c1039030001e850481d0700304035039018811b44042512803240101103494014101601c0c000d1041e031111b0418078090136154001a11817200c601401e9400c207080400300482d440c0158034140100242050b04810001494110201e0210361080709480200351004001c2e1a007140750b07900300f02c001c0c01d2072034540060540034000d504e403144003800424881d21840200720b9807440c152502c0ea0800720000e00708241d0038504407e0140d02c0c2244006c0d11244920207405805544900002900c1c1c182405c041204901c4001100d40820542221403058035100351010558000030f030070718004e5149268a250030b588d0024001440407440364440000b05020360041d80c0c60661500c001a40400c0e0001181e0040d404410a000800500344100c54201c01c400254000518076080003a0840d00148106444035495000075039501c0d00a00c446001000000c204202200345071501400c0c80d0007910003a1014050784034001002c05050084405a4100138000425030403844c81e03507131 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 332155638 1250 332154388 332154397
    0x20c10051303080c0601140117040b060d0c1401090906050108060d030c0204050c030411011d130608031201060210050c04120f150e01060504180303020c1c03200a090b 73
    0x940390108607200002280401e001024100200d070090001981040e4048100c6900d4a080d01e040000c0c4000303d0391075200e040702040d041a4000ae60707000035222500040d603240500b0030081d0440840c00320018580b10400708044146000303881c0c3c071184a87d5071601800300d422134418280842c3d240340000300700e8580007254641c00351007800c03c60700340300180d000304040782c40c21034000065010010911040c0700e100c2e41c005020110918005071070004091040814484422010340903048804078401100240e0701700c0400340001e02c00b12900c40d60348a88070b8804420030720509000d0f00600344106070800301402820b2260606284043c42c241c904048204011000c050907220040040301400c0026440c1b5403a0312200c41c8141c0224003580e015680e2406c64003598400c520a52615a45d00c81540045039800c044a400d4180140c40d50700070b408550910a0582e104031b50742041501c4101d0060301680f1440350010003025030f1009081600c10800b00d032207456950004a840c1d8041080541210070003007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 332156888 1250 332155638 332155657
    0x506030a11190504090b0d1502030c1b071d01030506010509040213050709140a0e04060b0102010204030b100801110307081f080706030b0f0301110f090103060b0a1e020c1005 76
    0x441c585148455110650441c0700050070003e5000075003004407402d10b00605006a0003250103141400075a0748544610200d81c14101400d03401100055030240d0500960728040c084070b012005e00d244840095886503114000c085070707400c0081c1018a810304101c1c00505803079102008081590034001000441d9074001c00490f40101e19941040600442d80241070041c0c0701a2038114030b481c1480c0307004100d40100c141d428025242d243c41049007110200c081034000b6048000012441007410040f4064819500050035070a844400d010018001e80d02c0c4204440c421030007080205504841075a0303902c429150040001c5042c404074003440304031200381d0500d40842c000130070090395076001c040c10f0598540c4101e021981e107a2403440b00c0c3c100f030108298801022030003080002c0401aa0fa4100d00820242115506000c640900564025484140907000320255162034031000380340200b500036030740e60341001a80403102d070182e06400003810341c40040d401480d51341d07040b8914204a034140c1022840 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 332158138 1250 332156888 332156921
    0x403140c1e15040e1503030f0904050a0207050307080a0807050a0c030e19080c030708031920120a1d06090409060b0a0f0f120f11120607020f010c090506030a 69
    0x114031100e190b06004100614131405a001c0e2032800564a03e1541d966170004ca003e03410400100256641900442d20207101c11140010103841d800b2000009000d1020020414800044c40a083c00001c4014001d9501c2c260344400b030690701d104049691380105001c8d8404100381d2010200000d0140c42400c1c1007007001b4044550750325840d4110840808503078400f54864120342c1c0c4001e1181414040e83d4040e0510000440c90504400300d44d40c03003508015401030802c80c0c140d07007010800303410b440c1504070400b0103002c0303820355140095112184e610407414040415407405650045480800c0a13008000005000c40e00704031507402888050300d048282140c11541e10000c0004555620003024054010360030f400d824603007021f511040f03441c55504103008240300490000001500d03034010f0409070b5800006081e000c078502002c1039581d00b00b000c100029004a41c200b1030100e40c0080c01d501896030100c001d000900c0203c0098600c0049030080c1a0000e000700b00051318a45144c12502011011301c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 332159388 1250 332158138 332158159
    0x80a0f02040e0a03081005180a15080105040302070501090e15040f140903090120120703140a11010506180a150302060d05010303020706030b0d060b1309080403140c1e 73
    0x40b090402d02e810404401242102d801e100607200441c45580250206540844031609200690301705084020458250a5151a06440300c042d00e50420b500401d071020003403104d4101450003a48800150003103a0001d080c1d40000103010083c040d4260080ca0721901c240504080c400602000d400c01085841c01291521020300082c040129014400d584c44c1001d940c803507128200040c070044000c182000c0003a003100d2821100c00012406c999000c3c07031035440325038a110030728040d6102400c0c4061a0f8450002203682007495420403030130031020380c000c8000c000681c0c0b00820000703624000b651449004a404000a90000d85644654002c08802200c032000750395950001e02d9503840340d0401d0081c5500c41004004050301000b00c1030182849081c1401502540b80c0807560281c036440000d4a000d4a81020103001d07250814807040b845040f490610541a0381d05200a00b0340c498070040741d0f00c0801d0000503582143c00f251200010200030403203101c80c80c1e000106400301d000031160710340c8000c2c40c01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 332160638 1250 332159388 332159411
    0x1a1b16170c0a0302010e0c03010b09070809120f03190e03090402130902071424070f120204060302040315060521011404030e0405070e0603180c03030d150b04080a0f0204 74
    0x10082c80200d200f907001091040a4900c010709041318110b03c58083e030b04100803844195074850380141e0141181c500f4010f00e80d140300c81c03141b409a9407042000b9904d00010400741824501000310310440013400c0542805404c100326104444010700414881c0d00240401c92040c90160000c000040042c10a030300350036100d41c04030301280d00010f01100d000202001402000c4002d0040411549100d500112600080c0304542c803c1ea000a00000400048001207a6200d000b02ca904c00700f003161740c0046444a07140d030400f0b80203501c00d000035180d8510a0b20301000c0d510850050750b0684034082d1900c286004800115520500c1781c158890f559500c43c402c1030018400140e40603c558000c6d6541d05040c00110103120481d0405400c030420044401e02c1a442902c0b4401207a41020403004103048113a0782b406254284803001c0e51041d81804005545203d20604d078002d60380103120b984c2c0010580d90703030706034441c6548282c0c403418020b500268010000f0883c2c2c1045081c1190018001084145840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 332161888 1250 332160638 332160643
    0xc0904120507110405090102040609090b030a030309050102071a0105010201110c2503060f1b030c0c020f01020c0d0b040b01080f120f070204050a060e0105100c020d030c1a1b16170c 79
    0x1b1115440c160398003041c00c120465101000300014071440900f0000038280c100841d03107492000c0750160030f0503210000103040007000d60450303450541140d0f030101c103c0312049030946500350078841c480c0150b003007654800425040700c04944e180308040e0014444d140307854452003100b00780300c1a20b0091860090000000c02e405000da000c480c0340301c85002036081039020a0681c01c041c1c0300a10343c10145400485941e840e00070f580c030080b050301180d950890741d000600407444c12020400080c1c0240c041c0c032240c41040b404000341806a48204035803e8140c3e21050791568039a282c02141850741e110a07a80c05004603460000c0a5514040c03407094946220b0303401190654105560b083e4107a036a40600304400400c511440b40903120440e1819150b8441c0c840013419004145006481102c0d51284a010103000b0f000300b902e01d03980000003051a51001c042c0412140045a9030b0380182c0441e4a5601001020f0701201c2640201e80120510b407a915264088400c0300800011417000c001c03c540c0c0d1010004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 332163138 1250 332161888 332161891
    0xe1b0109170f010c0e060d050a06080a03111507051204030e2707031a040b03030702031f0501050a03030504030303150906080d0e060c07060f0509040207140c0904120507110405 77
    0x103280c001c0000b05803600109003190f9051400d0020803050221100055640400b15441c0104008011402d5240c0c541c0c0c80006048540c00510309200740c101c104101900302d101a03080003c541d0650790001c2407402c40404a0a0865001001520400420003400c0e08511500e4010380280351001100c403655021511000c205202000c044100c9090260b90b882c20040140c0d0280312480c2c1484640f414040f9800a168540c0100c1e01c078540361400a41c00da102001510207141e0018100c4624080407400c0801c40001d900c4071040160400002003601d041454000d000c481d8540d90382454030b032440e20210001c21121130031a0f2003010b1940009078990305c03030040b00302800d404d00c0504845508264080c006e0030841c1441409140c091048442510000c9180d00c216401070620020b202c8101000b11410b2150140305503204d031002c1211001c0c080c0c030080010304006c544044800c00c4420f101046880c80044134001e108019401b01c01d80007500c514081d00420784070780983c031840d101071400103060f02d80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 332164388 1250 332163138 332163179
    0x602100f0902060405060c0a060c270b0f1606050403050c0f0d0f0c06090215030115020a020f01050901050708122409010303031d030d0f0c111902120307060c020f010e1b0109 76
    0x1940c111a410074503189404074244100102c2d5008400d1500300032a107640600040c0504d05540801c0840112408030ed9400e501c0798094000c201d50706e4640340190050304405940d0600b032203201c0381d560000c1800280d4060900d5580ca40c2e5959030110390049600c074416000c12242c00b51100c14000040e01d4001d2940320440500a84039225030400d000d044906503214030060842d4003d00d14040561185108820714610030302e802540d50150400685141c4501c820050005200254102c01b010050f041903001c2c035a03c1d107107400182110158042012080d41c0c000380d0018000d001000040d01030740c0320910240034201d296015030414006103085801011040140da5201d0750714240a08940c450b03000b00800504080584071062a89590f070369406d4455884040180c5d16660255502c80807000000080441220768403c0e9600c0c190010b05400c41d801c034007510580380c9220031440180141c20454a8060090802c00707500c2c01c00c035501c0e415400c042d40c140089282c000ca030070600d0202d908040030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 332165638 1250 332164388 332164397
    0x80403020405180303090a33050a0605030703080a23181f09050a05030d140c2806060e011d0a0b04050915130b0604020a020c0a0602100f0902060405060c0a060c 70
    0x401d103082c07908070620521030748044040030682440165004c442c20643c0123400120000343e0b0740e100d03e03484000b400c02d50040759140c07040350800000c2000a1004040401d4959609215038542c10b501240b402031b1415440790b0004180700d1480c00e6030400310610344c4620010200c020b0aa4010b2101c40401655160700d8005444400305200c0d50500c40700010003060f003a00203065903000941c008040010380d44030110038000002e419151030b4410400115401e28603602d0000000c0c02c2c100c25810304e00043c40c1243d41d41e0411000054482e1949400c0b8102e81c001103100034031051520702112180380041c0900511903a0301400400c40d200e5105a5220391b450b48000d10305060090212900441e00400c648010080001428000b80c80401c0d03180c0c003c00107450240e150105c01b5016424943d2281550380c0100c1804000103c00d40c4c00105025012059402008424544a0348805450350311902940110081004000c1814603138002d000d913000c0f440c140d401c4488070f6903030f160070f481182200c5d00004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 332166888 1250 332165638 332165653
    0x3051b070201140a2a030507150605031c03050f240112150302010207080d0203040e071e0e01030b040e06060607020a0e0a0f0506010804020f130f0f020d0608070308040302040518030309 81
    0x35050041001080300d055062902001c15643c007c6c058421214001c006000c2145041902d180c940c007c04098403008051703800341260180140e014044140340b40c80020700b01000705002d01c2c00428000d00032802940405000c552081c00c820b48100d0201000d41001083c1c4802c0c5a00a01440f8206882010081c011036044c5140002494042260851400c68210440c1d18840d1070b00001110200c99500d0000999603850110540708803903540d503011519068000c5504010f9402a00224544800d80301048900300101c00d10040396000c14080300181d020101040c031350f10303000d40540300551004200740f110b07540f503140c00c2c0b4018100b55107014109446007580700c01c809650003041e5110708207107080c5401d4542a0001000e601030030311098025090280c200f410840c41c0e42001c21200784105c07003440000e103202840342c000c0d800754036054041c41c608800801c000a02161290807039402c103008500b024156020080100809001c2d18035007a6456609400380000b4030243d48100519005480c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 332168138 1250 332166888 332166917
    0x615010e010804080a0e09010f0303022416030b12060901050c0a020a060518100f20090904060b060408060108061006021e070e0708060a050f0d14070801052503051b070201140a 77
    0x745001003372400c0c44515520841e5060300b43d440440c99008040a004c3c1c1c0e00662071480941c001d040c40c0b1400344c2c01461464428624060028207039000c0d17142c1c44d000304402da851858404040c0500300420300140c102072405030202e0480d4000a400c580f22140e015011804910603034500b41d00b0040c840811900e408414071025041d00c64440111400d808420104c1d940389032440d030b0380c0714907100c0600c40c25420000c03800703200c9aa40a02aa600c005e0561540c694907617450700d6480b102403040601ea231040500041d050381c5082114404c85429400034281110003e10084c480c5036100380c541c40340c0c450300c08000349848280404a000e0751040e101e00b80780382050024048010115007140f4010100da9408807882d88840341c108141c0303a048110000d280c0300d1183c1c050308006641c0c0c890540c56092505009040b80da000e40c440d43d0450040c002d08020710f0180d0300382c0030f5803012100241d0500d9180074503001d075030645004000342e0348140741400394400c00040c411701c02d40050341c243d00080c1e10610300514 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 332169388 1250 332168138 332168143
    0x9040209123301030206070f240e12070b1b0c0106090e0c0102120406030c0c05030307020c1804170706150603020a0e090613021b0d020615010e010804080a0e09010f030302 75
    0x1259820707110b0224550b0564000c50503034452600c008004d21081c0104009011002048040743c0290400d6890150901d24207000030f0040049005000e0040d601c00400700301608044406003903101000388145ea903003010301108002015800403c1c01010002d072042c0c40d00c02c0c03041034090409550000388101902d400240b41034035680c051819036010200d50841700c2011005d40e42140d038245008030312440812411134520404000c001c103144000720510840e03035004a260780b50000c064810b24090300c464103804544800980380a0305c482d1840300d400b40105440e400401800b80600c401140418103a174048071024000d62042d40061fa0100d0345c3c90b02c10303a1120701d842d9644011204580c5500b4010002815817031076400c10a9042e500040c0440c880810420040e803091280040d5209404402800fa444005c00c0b00d01d504406042d440c2e118886d0b00400a40034003c134181c3d110100c80c0e88070b03510700703400340d010100007000c0c03045070400c0c0300c2e440d074803006203d01821031120320482040c6141303806407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 332170638 1250 332169388 332169463
    0x3060213091a01021c0e0402070b1b040b1611030a03030b030601050a3507090207031e17100f120b010b2b0209091f09110904020912 58
    0x102c103801425a902c0c5140c0c3e00182c081421054042190321400400d081034551039503181020303400500214455062205215030075100d607038003d0005402c03a4070300900200c5881903008040207a0011301c51412940741401c0c45020551289542e51811620100020314220140d07070124002902c52a1200e0641000c0c01894010941620003a05d01d41c00c00d072a10346078032602000c2100c0d81d840300132059090000203141210703001300343c000e4604281d141d505401c065400580c4c00d401191403074840025100144484820079071013541c039202d1180924000d02c600010140c0310302c00440041e130022403011400200300e0001c20301207220ba4000c1501c0d10300b400000a0580c4035020108007481141c2040301740c40c2c00034a2020010304074024003403804610324002d00801101c503822035054820405945985040c50b540c0d003107440038484c08541d4030190003050b904180b916041c017070800d10144410b82019005020b00210090a05885102c0b080a89160500d4407024030170045641c01001180c900454551 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 332171888 1250 332170638 332170661
    0x1b0a050106050f0f011412161103070b0103020418150606020105090f150405030403060f06180509100209040b090901270b07050d02131418040209130302070306021309 73
    0xc0e0b201d491803c000809011404000c5414865009070240d6003c41c1607007190f100241d1b5441d002414180a4282055141950a03071000310300c0c11411005061000010340ba101540410301c44066803c0d80c0c24800501a054130041c0c800c00ca210401e0000707619000c030804401e030002c20000348103180c044001c1c00d440028200010300d800c1002081c07030520000c9181050211001c0d036240d050384840c60000e29501c1140d001802c21440c2580c803080d080e00d41d4010300c0860366481060003440c07502e840e0880880e03400341c80e40d811591001c1109103130407032030381c0283c254034000600c0020041d40e80c5000ca9020303107040300d04058a07503540c40385240010100c0c103411602240540340409078940b585e078100c0c2e06c01016241c0c0c024014040703a0b0304401032490701201c1402c0300113542caa810b1642e400703c000d540301e0918541846070301d102840c0c401d6400c200640600c01c2e60002c040d0001600c40c0010342c5202c81342c46006500714000e000e4007001088150005110784076140d401070903484d280041c010101c40d101ca481 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 332173138 1250 332171888 332171899
    0x150b0403020a05010c05030c03041203080c13180f1a0a121505180d210209090c070501230402040b100507030305070306120f0b060402030115080c1b0a05010605 70
    0x240301580390115100140c8400b820201c2e0f1924590030f10b280f1398015080300d942c4034840068041902ea40240868202500c691181140e40d215940c90036828098000321614140080004006020394480d0b5204603c1c218080040d1032141c03d0050000c0e540d200c036114441f21070a00201d001414200c01c000000e100c014040c2071b12203481d603208440b001c1c40300c03045210b03a510b070380100c2c074001c50b0f001c1041c0c3e0700c3c02504d0468554546144c00035010301c0100107040603122840050102050040c000c9400100c002030020310310303a0714100c0105858008540a84d1950f50f254122048000f00f28025005801110301980d81898144100400e0741c19189000b4003404200164803401a040401e0b280c54581c503003000306956440f00c0088004048550000604801e00880e103020710590654900e8028001c6402c0c0100344e54403800d1100f6444284580c0011a05d075110011215120320003064100c4040000b00c0d00d0078040b2600c40609a900c1080740040d50400c1003028208542446504020001500c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 332174388 1250 332173138 332173147
    0x90907060807031e09050a0501050a0c09061103040906080708100209010c02010c1a070f090e04080304020d030e0619270b0c100e0303100605191b06060801150b 70
    0x1001001031078080c04400516850742034240e1004059500b034409142844020000c130629810400d903641c0500300c0c20b440381c2d4649070100c1d503000c40f030303025521090106444042102d40b8021080f9140c2030f00c100f0452450000340008111604940141c8d0000c10840e4001c15500c0d041c0a45642098a07007a1004500c5104008100c800d903003001c1c02ca20040c0d02400d0a9a01040324102151450641c0321503020244d210810428a2034020f0b1600a1200c1e09650710310210303403100549904a0416640030b04415410f2000500601e002c091514010f8404e2a10303000f440c003000c2c08540141c00c80c20300401c1d0030848000d80b11919070b2100f40e9600200d102c03802d074078804008400b0103440f410345001d215910354001030401d00c0300d002004041146440070504000b0542c582d20819101d03002a00c55900e0007607140310000b56280f103130058a410345d118018041d00e55503c8001902c140a1003411401010400403003203012941c0c611401c1d0082100c840082464078810f0380b0100b0058054000c003900c140b0610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 332175638 1250 332174388 332174399
    0x604050709090201050c010c08100e010e04020904140f0705150307091415070c1d0106050a0c020a0806241012050402061c0605030d030e100c0909060306020405090907 73
    0x50003021200c501000203107441850004850341d02c20042001225800c054030340901503131040070039203d207030201d180c4010a501d40100c201d46010a21901c81c0100c004030109000d4600820f40e01c0c0c06c18494525440f05070041c2c2e044904003845079210144980101104001ca03007001e1011000600d5031101007461403a044e0780141c031000b0f05004040d406034501c01d94014a4680c0c88031448a8043c40200c241c544455140915003105c1e5802808008400140d5145001c00d0b0144603030f040c1d41d0300340c55141c20007101c1d110888000c0c0d0040320603030b80003a20079000034030a901440001d000b101040005003a00080303002040000300c00352a80c50040000740071000780c1c40d5000342c11000c190b10030301010656072202d000041c02802120b0105220381c06000000c00004400d60115088410641c1620b01e1011001410781c115500b8486882898201d0100c0548540c51a48021055125810300d0b4160940b6400004106c0d40c031a081183c2c401e500140074002c81c40c0501c1c4159001c085500109588d60070714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 332176888 1250 332175638 332175643
    0x60405010e070f0315080717030705100246020f0c01030905010e0f030d05010f0b0306090a0f11120603070b12070c1b030b071404140301020c1605030f060405 69
    0x40c40d1204000354140d407040098402e400c040e040036114442d55017000d407980039a5403100c03100d208200502020002c900d03128113004c0146c550084d0000060b249070030001c1c00b4880654440c0400001004c441c5c0c641c4038a080c1d03241c14840038444030400d42441c03440c040960840e01181841d165003594441c0070900503890300054000700380c140138a1301103402c03401d80c40c10602500d102c03a024a00b50184030049800e80c80000f01401d00045404001d00899982d00020807a42c1076500990344080002c000190300790034041400c0e6041a441c4600298400e1907404200440d079042044101441d000104c0187c0c0a02d032012040c0c20010880140000514001d0703807001c180b09880081c1c902c5201e01d400102c1a074000d103d8180165040a04030700640100c140c46e0280e58143e000468410b028000442c1400d4400d00d04207200781111903140d468581800100e500c9040c2c8154903650664080004407080c1c1c20a0018030000c2410300e00d542a803d0600341050b0400c0d5003e148006260b00071000c000c00304200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 332178138 1250 332176888 332176891
    0x150403060b040615050a03020c06150321090402090613031104230a0504050a050307060f0501080109020a05010e130603060c030b030a080301050409030e030303040b010609080307020108012c040503070b060405010e 93
    0x42d0400c41c6c0d840300c2d8210142e02901815411542c6ca005d07010801c42c0c0c0c01807a01c41d034064240101d0940b12a03622526585142c40d1030b0064040c0441c0741072000461600340340d0300500070703500c00801445c100200c1c0504008105038580046582c612800f000e2515401c0030301400d94000300c0f64030001510240c549816003c158020207010a080e15040441d084c02418000b01e007900f50408262a90b407046400c0c0715000d0aa5104016241d03072070280001000b210612404241070f900a100610507031608004684120140684951152841c40b400112000d2440741a005520500c0007081030803070324402404964801c809140290007041030440001d840c0421207056074000c403800111010a1306044130104603200c1c500b60075200c00000c2c007041c005024070b00303412904150707520703410151034101894607400f0741c140c028003044442005100c00303104110b1101c8a01840840e64102a510610780407104c10213545c2607820380c1000030a9824010702440182d8060310944040c03045516100480b10038100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 332179388 1250 332178138 332178179
    0x2010f0b031b04020d0605060a0f120e0a0609030306050607030c020910050a120302030708030f04050c06040f14060c0114090105010b0301030b180a0c140906121e0c150403060b0406 79
    0x1800504a600c111701d0b0f0f0300c03900160201411698461010b94000390408000e60b034801c0100b14440b500911000040c06003c3c02e01200380044c0c40c03611099513940c005082c80c01c40882c280b64031a1001b003016103d100107822320a020b41d8500c1000748981c014803061400141420f080340400354801d0006480c5c804040f0700701c0ea0896004407481c0c00e42e08080f41980a0084002c200c8a00002032180103444000a64047c9025000742c2e90b1090f114010003403d0700c118443e27034a20243d81a4100940030310404100342988001d0107151030f02040c00c83c00d600311240d01030319050b04000c034070900250801c00d2080394050110500c0c0185154199150030f01403001c028155032000e9440b031803241c0300d21424040321008540c0040c640708425181c0c01c81c1801c08031841600d034041e00325400014150301d040040e01006c0e80c510005060309211030302c400c0c210b0041c0320072840c03081d100e40c401411490315502109080248024801907c4070b0651902034107441540d035410740301c0c1e41000c405100282a40014624100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 332180638 1250 332179388 332179391
    0x20705011101060e010b1908060312090109050303030901050415050c0d0b40020711100516060f0c1806030203130c090905120301060912030c1202010f0b031b04 70
    0x700c1906060b4050f101070b070424400d1040000000511701c010501401c2450340041c106402c07120b171410704940000044a03036651551120107015000d4021000425241c1d0040c9009411103032154040fa280da40b0546440c0c156a55600800080c8290350340790200c0296807550500c01d07818004205003541c01203048441c07400e907462842411995807628042100441207a80445070380c52404520348074440f03050040c00c0d403442c0c050b22210143c054401c44d15181e91000c001c0124060040c1070054504081510300e00344203007044825100340e0340300c3c0c803407034014030501c004a288503030301020400347c07100d00700d03160103126900c95403012001e9440b42c2c1a0690b034080c0f40050301c955401014698032000c2c0e80300580f511210042c046100700e455044041800d0082c4100c0d006200002032090b6548400d214030340005e50550020b002c043e880b640e000e821203010b440e14043e9071150b516184901102141208090303950b5015221441195000300003843d40304401810b10520036032404007103076007400b070017521a9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 332181888 1250 332180638 332180657
    0xf060408040b130e13020103050702010b06040b0f0403080d0603021f2c040609020306031b06040e0703020714010b0312031b0d0e06011503050a050121060e010e0d030f0c02070501 78
    0x3c4400d14440b00041c40801a4a0f40500b040c4007503c210003030b580c60581c0043c0c01c0500280c807060050180b990700e000003400b001d1805c2d2410b03612030050b0b00f01042d681c000020800c000000300310b001c0c014005051504400044003461403040050f02c04c2c5100d1341007040741e0039420101039a50840707400320071484009015900c0040e198030044c0341c0c40c807000c14594840d280103400b0405035800d5014604c100307c01d0f400c54599030411000b0364001410303664100d5001104006c00c1c8082c128810300d00b6048030103070901504002ca01d0f5034400c00d490441020062aa5495000001c246810014510a005400e90492460510324a0000740c00c0c00c054000551500019201d21070940550290440268850a850075941c40c1c4032030301c103d9142003c180300003c1c101400b25080b0050740c0b165038121041d00d0100c0750300c62171300201036030340c0c0360811021756040b1fa55000c03030000c1ca03070300f8004d10b52541c0c03d04e8054010320111000c054103c0343d1018091f0307461850003046242c860307000584041543c03400d08200010b0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 332183138 1250 332181888 332181907
    0x12060f05090f060406030b07020a03140f040303050c100603081801210b011107090204150e090601140c010c110114040c3b061503040308010902090a1706090f060408040b 74
    0x50700c0170b075200611964019040003078640c4d01249002c3e19902c680e84501e061004000710b0001406151120011f80b0010442040060702510003040400d01e50020760b5529045400d10004a580541c0152600900011f0b044040040910203200304102401d240429550301c04402ea01c1030544160701c400b4990720111030003268040d14038504422105030484440c0380d10340b0300f60030194000744198056540a5100041da0a02550068040d400c01034400d40b6031350344003001119100040380b1465902c400400180004200a02401c1044612500c2e01050103207840007541c210354082d21032100440240c0e080c00002006c0b1003004c021a802e0000c0c1c3e010f00d940c21024031061505500c051024007201007201c03e15643e145921921904040300c552614100c411010401d81c842102c0003000140003600611603000d55501800c60148003400600c200f03611010118030200c601505081c03a03611500c2008070005080122100c4000980003420341820700d07590f600071502075800340b9203201201141c201c11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 332184388 1250 332183138 332183141
    0x11a0d051005010e03070b0a2a210306030b19111602210c1201020409022704090302030307030905010902041107030809031e070c05030a0312060f05090f0604 69
    0x119004114208401e05180301c0300d00740007410b44640743c0410007030906100c0324500459054104d40071600c0c810700c0c200d48580221a03481c5142488824048880603800502e003103aa00100524440c0564a4090070100da0582111144200c007508060910a09100240380721400c142c004044500394280440841880005000c00d08401c9085a202183e4107841008000e822120b29000f920210001c83c5000728180896020349004c0009a00858103d07072542042c18804540d10441000103080c10344845e4040140c0e880080c90040c46410303041c20801408a01ca281c0342080000c0f40c0400a0007550364000e5180d01008101d5810325a407115150b09001003900003c405a5004004000c13010204501c0c0d42d56400480e01540000c813803c0c00507a6106c000022552402003402c01d15666900080c58030001d41d2041d14100c9070b903860f16000252070b03141044828515071107900c0c1d01085001e0944c14600300c84450348251070780100c004040040d511507071308264105080030701c0310070316580c5d40b4003140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 332185638 1250 332184388 332184397
    0x8181b06091203030103030806030a120c0507030605010803120108071a030a11070305190215061507050d030608120301060903061d060412090609030b0c220b070303050a02030f011a 79
    0x3034200d00200b0300804105030201c002d6058a1082e01d4090450300c0301814180d0f02c0f031003c0700080c0841e00e110020b050b59170080000c003032883c3c0300e034044030000e540f2541c960094910a0303008240a500100f0b908038510b42c0c0b841c0036400340440a000b071405171300d0702100c0a02001c0c0f49403503c1e900080000400c001c1240c1c0d070003141e4034000f980c40680e501d482c1c51400030002e40c85981000103105400c42d00c981c80790b01c007103130000e001107641c40d11001e0b40d05d410301000080b1061800c80b141501d42000601c001031030034002c1903140a100d80b000151a07141846803414075004203c0340348840d4080005000444d00301c04040c3c10b4039088400061940c04c056800c041540c54402d80c0d10b2103100d402e042000b001080748481000302091390f07400d00d165946001c1690800410300000302001040000285d1000191000d020380c08180b18a500c44840c42000f40c84c4e0f10030302038101000e4983d0000740c400c02c0c19054054641c000c96a00e008526519103509503000043c1d06000c3c841b90302c08000c3c080103443c090002541e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 332186888 1250 332185638 332185657
    0x4150507020a1b060f030b030604170702031509070501022b0e03100519020403150509030405090702060906010b040503190204110a090807051012090309032108181b06 73
    0x280f241e0880b101d400f8000c00950302c00c19000070403003a4425011031013801000d484141c0600101490744481e0703261049540301ca408107507000c006000c0080560b0381001049185036034544007050505204440a00704286604005e06640c4109501c1c02980c600b14003881d006200c02c0750703600d020015000d04031280c1090220040d13140c0f02c1c00f10784c00c140800e04c0d07012034019002c3c00e41654104289088070740a80c0154800a403500c08485116042e02034240c1106610064000c152850f043d2100300140070104251703580d0006901542c20808d801c40e04100c070074094402c1d06c20350b0341000d18250020783d9810300d050f031090031122010b80362000c40d00d07603801016460442059140c3c0310f43c42a60300038a001d505200e0342d8581d10030601c00080d241403480c59590385040a6884000402c03c50302404090406044200c0030452107020000c08901d0001c14014280f400c50000801944400c1004020440141400b40c82d00400c80c440030400c0d10008200b4440101d1580350f03140313040b440000070040d001e01d0120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 332188138 1250 332186888 332186903
    0x109120605060a060216030206030c130303121811010f0c05010612200303030402090907090501030614090609030406180503030301090207050f15180c1f0e010804150507020a 76
    0x2900420040c1e8024501c220303010368050a0055481c0b034120390b2644482200e151030345041c0820700250910800460b840803207801c0e500c0c0b91123004118008006100d41c0241e00144d1341d1105040c600c442402080a42140d000c2405c4ad849030584070b11011a00e5410614140001d2080c0f0401490268107900c5400d81c01000800500e607072900209955540300c08201e907c0f040101340000c46003001c504600f0300c1c100c0036000354155501c075800d00c51003500c007410030750183c402c541e80000d01e1181c3c2d0184a000e90301c030f55004101101c103030819542102c2c018161340302c10342188041010b16080007050314101c1c3e24030f103040c01c50701c454100d02c001072425a80005425000000003c6000461500241840345c42082128504007007240d00356200c895026200301a2aa080c0104818040c1051221010f003801425644c50a420b000082c0e42d482c1d1600e0454508040c40c200031030344c2c5801580800c2d88800030f080070b8076541f6080d6031303540c406044040b0729100241d480c40420a4a07108201c03c0703c0466000c0c10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 332189388 1250 332188138 332188169
    0x720030f0d020c010e041a0424060215150f130204120f2105030a0f020c01151e0b07021212030f100b04031e032c0307090513110109 58
    0x200035120480f554400f4080380d00c1e034603014610308161094001a40100100c005004220300400c8050145185401c04410001d800c40207071071429415030b401080e00e90002d020000c141c00c2202d0400c6802030109d4507008001310360220715102c841e03d505104200f00c0b14a2440c14405001200070f00690704001e2150104001d49020030400342c0a44a02138000e03055200e005807804152585c0703010003400080043e1050001c1030303101c600c9400c02228403a81c5e2030094108050801e03150700711089081301d000c00c02c2003c0c200300808811064402805200d80343c4c1c5085840c2040302206841c803801c440207000307400e400303a55075800c0424001850900aa0380340c803079a80c00c081c0e045110002060715030039540d4039800b0000035402d424508840c01c580d03120801801125081400341c480410450041c1c02380000007101e0b0300441c14900301e01900d0024510f90110210600080c9460104540c0002031040d00e40303002d100d000d10040001d501d641c0d0340140054100b090500040760003040d0303607100d20401c0341500d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 332190638 1250 332189388 332189413
    0x1020c100311070c050906190314071a0702150405060a050309030403080a121413021e1c060609020304030e0904061e0902100c0b070e03010e0708030405150720030f 72
    0xd41c413404075030341103502200030b858010400c4140418092802d0201201110401c001540c11110798003254094058900180ea00c0d400a1003101800441510300341000400c2da0840c0b078541281d180521780c18041c3c030300342400c0c0404510144914403102c400c1c480088006807144004108840c05181d1140c00c0c0c64a82141a4000d40f415001a196807201c0307084c003d11241c64104120a18440d40d82c940d24686105015001d10503e010741f040780700c850b40041514600305032140690010308205038001c00c04003440e1810000111107241d0800c810050042007440040b0b54040c1c640050044100d42f08441d58940d0302c0d100004149240d0204100c4080102c541001d00751540841c040e1402607805426104110400f00d03810460803100404505110010448981c403400715100c0031100034000081c11420310000a28040a40c1d00c44480c50748005010302441c20b2801d4141b52541041950a0400486039100748410841061600204401c001c0e0f1502e04d5600b00104030358010b400c41543c42511416 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 332191888 1250 332190638 332190653
    0x305030a032306151c09050606130204050a090c0c060920030c010f0503150a03051e0d021507090b070b010306110a08180a05070609090c090501020c10031107 69
    0x95800800324200001034140d81480100314903c40d07071000340500a43e40940c008040143c0007071602da01c2d41100420443d001e050180301c2c0e082503e02420003049586425001c10100030242a00000300e18018401044036440741110b0b48107407070138840085034130300b103100040707031103020f0741c03070701520103418005c5000074400c404a5030307a40e0b00306035400b600d4022200000d0590f50514034001c68001003117860801002403040021716003004102820744a0441e0712800516100308a07001030700e241e002035540c4a20614900504254154200003a00c0210040b00007e034950800086540040308004002003010b03101d60070090182c4400e001d075940b0381710359041c60120f04509020884404d0719001c0b117001c0714140b41c1c1c2a500208500e0303480a640b07544141084032001035071140004248505411400051014040c4401a11955072040752962500c4681025100e80303000e18014445107903810310090b42e000c501c035403080c0d80aa54580d03041404400880c001c1100c0040080c1c4030300049416010807500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 332193138 1250 332191888 332191901
    0x2071506050109050a12030e030c06040303020c04060603060305030d1a100e100e0616062a090b04030803070f11070f080705040b0607200d0b19050912130305030a03 72
    0x3c0e40d4410006403240240b1a00c042e050040e601e5004103c81d901c1c0c0000c2c1308291690036810042d05403a15510b42d0004a00305800c1074000b00d0150b0000342c0b090300207050074407410000346001d140521689146031585a201d2103401174003a00a51140280c540f19071148117076241401c4080d00501421005010050072444c0329900240b00b00065500411a5841140c504000e0305000f004540342022400100c20146c011034000c071040c40d100c03102d0320045084060310712007500d81840299240d541c0d14600401900e215006100018002d10051000c070740c41070166035221496007000b007100207841070709a44000490109207a03500c590400410880f4a041598003103891030403c07912156203c1d030401007503031000d90f0b84540004051020402154483e02c00b400c584001121308094050b800c0c0101e203012402e10801c1d05d51360760781c0040c080c3d41c80e02640310400340c180089080100b420130800c02626040d400c96070520380c4c0720100e0b45030107511040b40c0c24801542e0040441c1e42d1840d030120090050b000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 332194244 1106 332193138 332193149
    0xc03130201020a15020301030c0b030115030b0102010e060a061502030c0d08060d080711090f0601090e100e100f051e0103020d182a0f050d0602071506 66
    0xd0342c2840260344c04155402603603a6040d41007554207064958400c0000003404c000401907161240900300c0040b0841c900400c4842c0c0460040b0b006d80b40c503555180b91400703070380140710001540ba407081c012100c0c25070b400c0c03501d10041d20042e62a170283c01c14440042d04901c0c204081c6520801c44c1a510030380040c100ca00300c080c20788818046030441d8000b2126489003002034005031404e0060981d00041002d0060704c3c510707240b130000700100702500c07600602d07200b100003140c11000d48814040c0a0101e0341442d0003580340038858626040308070f100340300b0f030294440d01c045010b082000c2500001c01134030603d01070040c81040110002e601c905c00b000030321551114001d295a03041d45034403003d24000c1d40e401052405000100d0a68070440302026000d1000c1482002400c000205442c1100c0f42101c5912841c03441c0d0912001038410858024078001030a900c1c1412070f50160310290545e407 = true := by decide +kernel

theorem cover : BRFrame.Cov 332014388 332194244 := by
  have h0 := BRFrame.cov_init 332014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 332014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 332014388 ≤ n) (h2 : n < 332194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
