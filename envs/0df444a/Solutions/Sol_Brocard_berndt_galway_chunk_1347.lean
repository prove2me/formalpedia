-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1347
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:30:17.681317+00:00
-- url     : https://prove2.me/submissions/5d18406c-3f79-443b-8fee-7ee8f716bd50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242086330 ≤ n < 242266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242087580 1250 242086330 242086333
    0x52226040306110c0706111e0f0c03120306100507150e06010801020406050d020706060e07020606090a0203060325080d05041502030702060a080a02090406090504020a080d120203040516080f 83
    0x1103c280c4401d4101c1601c5000501402078490396140c403070185c4000e00e040c4201c01e100d016181304e0007a55410501c20303440740c81c0780c2c500800b05401046440c51901c4e8030100514400d9114440300080c0941120032079520800956a0b41c01b1000e102905507428029008014035005840c0354065085030240e11030b0300e03c00da1000880300c1a0741e8820003e4205c0c4918094200080d9082144401400e113607001000154842d000019025980d05008015158250360034030058002d0300070300c43c070b501e004000d003500041c1c107240031440c41c01c004000941e10040704914804094114417048580b078901000000107050721400d44150600c00d8400a010764018010274114000c2c117202c0c3d10541d03100000382e800303543e8060540ca00d044041c03c801d4030000c0d030003050001c02c6a003c0083c51015140ca0203000020b240301a0b0220341402c1600c10080d40309882e40220180780c1c0001c4219103802d070300c0320400215a8080200695948031410302a00384106a520703025007624a40000802200c000340441c0810001c90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242088830 1250 242087580 242087591
    0x4110d02120a05012708031003081219060e010e041110030b1201020403170f071203091406040201021905030c07030b01060809030f0a050d1509020418052226040306 72
    0x60900d01041084492000002145604a000110550001c7d50003c00b14240140b007280d40f6a0f030255942d02511030317440b07550381c5203041c8101704290440c410140c0c0c1a0140134058142001c0041049000c14825054840c1072540403070140070700c480e100d026000d4041c0152210740ca0802015018280056140303000312944d0001410307012041c820b40781661352040340d072210040090400c204c0c68222641003041036008202c210001030400300e80520b2070485841c0420b2146103400c02c40518140504002010340200e0f00300710043c0ea0101e0750b4620985245c1c40004400c41e01d041c410701c1d5004105101882d4401c902c0f0100510664489013412508140c1c0e52012941e200401c040d00ca024000507980c541005010188640780a4405001c02c60000700c40007903110111200c40b01ca80b502940300590447c0c0c001400e00c00100c1410010064250501c0c0500c0b060a01c0c01c00f0440f41c581082c0c9150314020303400841c2042000f005040c4130240c40600019078a003404088400031a8014032003114002c0c41d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242090080 1250 242088830 242088851
    0xb04110c0c12060711031306022b080705031f081c050711060901260103110a260a0f03031b090501051e0409091103070f05060304110d02120a0501 64
    0x840000b00c2c09a00000c0c1009480b0350105462003000038480300001c1c0402d0010b01415102407981000418080d4001d104410041d0010452800b403242c210b094203220401d01c1524a42000c101d0750069820301e00329aa964480c0c58440340d00254010341401000035101c00901c0382c1c1c00051842d202d0b0301c2c0262015400c1c010410903901da03c04c00c4801420b0380d941041300840381c030b000740207000c0d142818100450448030400340d400c5c42c441d408610010300184070005005000d40041d4a4003102403c0d1142840941404d81d40f6464160271940c003140800002d10040010343c040c4150860981e110245000e0300d5150304d400340241841400103000000c1c2008512a65482408007030120703801a10341c14074065051038040465075102510440c6c508040000080301c0105104401550f40150011081000e0b80f13410942450320543c030a07200544029003d016a070703100022241c00903482050b0010704225100460102d40f4142000383d80002c0d00c940b030041400000c503a8115241c441c0001f0015100070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242091330 1250 242090080 242090089
    0x3070311011805340902070f02181005040c0e1909050408030f0606120f090a0b0711070f0b0301060c030201110a08010510020d0f052803060e01080c030a03120b04110c0c 74
    0x98481130800300154150401c9600401d40c006c0501c80d0007017501c450b021019801150703161040140c0544401103140401840d5990201510042c100840b0140070b98000010b0041450040c410110312a0844074071070204106144502001014015000d010500e05810802c00c2900b089603120750071a60000020324a00e041012510f0a018807040c0140c1c94840d0503158906060080101d00c8502c42c0030003200101307070790f0105e09101d802690390388076400394100442401d0103000d502885924202d0b5009110204280040c2ca040d01c0141c070300700a40000c0750400320b000d0400100c1d82e2403804000500381000d160310840e514140c2d80292140368085100b010102c0e41c4003501d9aa2200254600d20340602041c801e60040810240590840314101c1400304c2e1240040c05800c0084003090b900c40007000603c8d00150313130900418100000d00b0100044d04086901c0c0d014240f0000c0800a0a102410503030405611030703050b40e03101400400c8840b500514108144e48034100e4603e0070b00c45c45c030841286282 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242092580 1250 242091330 242091403
    0xa0f050307030f1511092b0201110307060204090b10050307080103080310050a090c0e09040305030402130e030304050f0705041a0d08070203120901030c080903070311011805 76
    0x2009802004024919103826810090000e011203400b03071406542e5518942c20b010302080c5c2d2181c0401565200c3c1c5070020401c101c00f4143c0e2801e1003800b006029078080c141c4600100c810f40c5c082c2020f09812200142140c11445180c6c0300800f524808034010ac3c5500d0300354844160114141c07113500d90005940700640e140e010442c0d0881c00226990300500000d01900059900704800f482e40b5542c0948800016070b2417001508142d1150b966190b6568225a002030180c45001d400c1d500940760b42006d44000384580700080020b8010462018860842252607000b480907001b90019a81c03241820b00d0b142c0e8690703181c04090072040c46440004a0b0303e142c00e120b480020032142c001214078882190038000141d80340902901d0110042c018080075881c02c2c45040031150780b401c0c0d5a40d885132908005000c8ad855192410100514101003151403540002200c40243d018140310345d031001c1c00e001d080e0151502319000d40e41001c1d0009194100030b00022505130038001c83d0b4022407141100c01c119501b80b030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242093830 1250 242092580 242092589
    0x60801170c0d020102210706060b030610050c0a1202100f0605060403021c0f1b06080408030609040c080d03091406130212120720040b01050301050411160c050a0f 71
    0x402001141c455807411608140350184180183c0b0107807441c5920720045a52100c820000d25100000c0d0101003100c0c610814002c0c2c071104014504508145000c68069010200e850040c40320001c0d00c5180c44c40704004032010160312600c112401e0320034080080d15800d00b00007400341c8a0030310410314181403075806840180d84024000c40e003018a0744d02004002e9015040c2c0d00750303001c00ca003402c0000c181241040c80d8107500078100002a0a4040030b074180e102610340c00b0108004100c01071100241000c81120341024085034480d11a489a0510103107021059001ca0014030800c145440242d4254200040807030003050340000030300103400c00720f84aa80c01c8401442400760b0206040c01440c102d04905c0d06081c022003210780c0507480800721380407a48084030648403d803250b1210480491005e00b00c1241c1c03401600e041c8072420b00e00340042c1c200c3c00180100b03031149403240303040600b46403031105442410020080c0c2102d086200d00703100c40007103014000c03540a1250010049071180c0c2d02c0b0b01d40740c11a07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242095080 1250 242093830 242093833
    0xf0c030f0b09010630051005061009061407080c0607020f010f050c0301030f03050c0604050a0605070518060d0e061306110309070e060423090105060f06070816020a0f06080117 77
    0x10401608020f1748041d042e03050b1403603e8101c0f1824022503410080d032201c813201c01c0305c00209410000c0c10042e001c1400f10002e42001401c13441407103d20b1b8800113031002888503075205a101e488a107040b02e0140951000d40003140324440c00c00500681c000b0b0f080344801214402000943c0b03944402c082590411903503580c003500c0410040000548290003011108e009181c0300c0d0900507050002818040103480a46150740191814002d1080511802d60001c4050424518180312120a10300304d1000000b030303503c1510041101c00c10542c1907040f002d48440760000380e406074940490018007203040300d0030036206146003030361072030728a007002e801c0b24015540702e801007500340c0c0741450903400020020305107500a034458022200f0007006035070f0300a824400c2c0e029001903140c06c010782400c48100030400c0303106e50001c030081e00322074413880f085446541e0410000382d43c0e80ca005801c4105200110002904180c510710001141d00104822070280c6206540f4081a666200d003401d500c8054031000c05440e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242096330 1250 242095080 242095109
    0x7020109030b100312050403052b03110d021201140405010303021b03120a050a030f270f0804030503070c0902180405060a030215040512011103060d0f0c030f0b090106 73
    0xb0034110070303109622038860b840c9081d07074035102d03903a1486409400c0343d11300c04200041428410400b05002ea1418102c46180c914000e00c488240b40c440c00580340740c0325041c19501c1071080d8110081404450180540000c150351301d40c204103d40c40c01d4070007449010398400c409100010a80b811b80102412a80c1650040400e040203000e200f90300d88100c0c1c00240d151007a011109a000303004800303400c05420503161681c8403520050b002c1e0070340b4443c01b841700d901e40c030b80540300b40a880013030f0740b04480c4881903801c14186103861401e040c050180d81006071807040045800810450b00000a00c07016104e803801c180c445984449020907030150300f4a102c0400d003d00f100c2c030082e0500c0d502480e4441c3c8010100419990750f40c0104404000c10790202400d080d00003000d21050601410b02103952149000030058021081c5181401e1701001c0e14442c4150340c1c4001c080180b00155040c0f8901a0b040750007816259664540b99603e5500440115600040c103400698030780018854401114034182a02c0320 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242097580 1250 242096330 242096333
    0x106080c150319050103111309080d0e1009050a1a1308030a090209100f080c3d0801090609020c06040201030e19050d1e090504150506131a0702010903 66
    0x10340340c00052200302d0155112410075034640050240d2402180981d01d204041c04047c800c0c40404c86014042d05403071130401c1d9172400050000001c4a0301707481814400180f10210341030300c2d13080c26807000407040c041e13040030841da090207070100303100c24080d01c1503403035860115070892002e41c440d07012901c5540e5000c180c13484c0b0300400c0d4040001d5901910030100010010580d6000441d00b60050311010f04001800209004159104041c100649100e2004000141841c4001412400e00c500c0c031921800190607002940100e44881216410040040104407140058000c220110901c03c120058cc03e00d0800a020044c17032003202c9003081402d014021a0340c071600150b0180481b42802e840302c0c80b60b40c00e600c2c854540e4002109950b44600003401c860424a43c000304240c5200c4040c80d864406983c2404015400103031443c00c4031002c0c1c3d404541c0f0b80c86608200c001c40c4041d0f20068100d1f8000036646100800d24042e00255422400d07020f01c1e24108803845082400317140700081c08507000100500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242098830 1250 242097580 242097619
    0x9010e161d04021602031f06060518040902150c060f06010504030f14030f0d1a03010b090703050702070b0c1029092203120e0114010605070501060e180106080c 70
    0x1141c58020456071020798500c0d8042407420703e04c4100740c4003103000140007107e10819402130030024015454002c0c2040c0d141c00c0d04401d00c0710181032041c416607440510204640710a20506003005484d10150b4907101c8140446407113060032600c80c214003a000c00040c0156004405032403d41c0d1300b154007014100c02d190b4134800800a2456400e046104c01d00c440c6040d20403a800078540c6015030300c0045010014400e00100880340c2410b4107120364108251074034252284004280c0c4502d8520340401e840e01d840c1d50503400c0c589143c228508082c00042d5400447c0d400003600010111043c07010003d050f00c6501e41052050700c81c1204065100b0070119804500e031a51881e074010003021102118000642441140c1c07800c104021004130b466050030b042000c41c00e1150080207164140207100510725074078004501d42c01400760009104010178268240b107400d43c0810046c0100103c00b1241c0d0030081c01002c00d03901c0a1881c6240ea40c00c080340400c03291004900c0c0704540c18043c000c1d949a4041ca085039 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242100080 1250 242098830 242098837
    0x1606030905120408030c060108030a0c080d02120705250c1503060b1216050403020a030b0702030904050a06080d0311090126161403040f06180209010e161d0402 70
    0x1a03031144900d40c05560300b40900001040203007564002190707596062524141044416401102e082d007050045821680d0007074040c0c51101c0c0d002c00355965500c85489030700000c1c01845041100c1c214820100301c85260040c004006080380c5038a00358180c601c03102200c011100c24540181002c0c40c4c2d80081000134000500750344070f0001d500707020403103035207c40642c502a00f010164203150103005041c0b00d5524680008607445205030b280075480d090660b00401d001d1a0644070081180e440000020700144c4240141c48804a000344148864100440d04402504040c040c171754441c0100b00822620b103000340f11b8075071100790403036400c2e04204200c00191a100c000c22204051400003ca001c84203107910780e45244030f1415100c04801120505d8002480309c12005d9403224844020028000804c03985400410501d0b4400c40c0442d8a03c4004842a24115001002500145210008180242c50450007442000c00c0402d592003284a100101c0d80f03001400034101c0303490340a4030040a90b0600c2d8006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 242101330 1250 242100080 242100083
    0x1106090312090d0b16030b150702010f05120a09051221090708030703030204080705010c020d150e12070b0a020301030f0f0c1a0a0e030d0f260f070f0216060309 70
    0xf8882e10712610340711130311001250310001020300081412070560301840350070aa241c00b5504803031243e0703004690500b24803c035800a41800224100c40019500c910200c5800444030740d00d10401c0d05041c3c1e002400b074020000c0448060040c0f080b00c001d841c1d042000d4401e05110000489081c0e0400320b4500d04142010b130180850f400b9141c000300e080c100400080c08460b1099500580d550f182c00c88907070a060f500e400c401c0c100425021a140560307188d40b2800302d00b6801c1000c0303c030300c0000c001c0110010a52004a195680580c0e0701c43c03802c00241d08050b0102d03a00569114070180e4540b140d060883c40300b400002c0c10280400112404604d0000c9032800040c0b01d041c6002a00b501e8049140f26002c90441c4680040d400240605041b0303800f150054014100307400a2104d2014003102a010a071a00341401c100012a2401c041c410070f40215480032030b012407080f0102c1c2c1003800b5000340303e0001725000008907500d509903076000c510019810701540e1403045c0c2c0076180c80c04c100703044001c1d08002d40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 242102580 1250 242101330 242101339
    0xc090b0a120f050f1615080f13140307030219020d030503040302030c06010f14030d081504090b010602010203071e020316020d12110f16050f01090e13110609031209 72
    0xb09880000c204000c8007900103208070044c0340140002c071169542c403030941c2095200002c25105400d602d030308030140c150006603280f048040e6030b0351034103958402a0042c1000d0203945103407241c1c410403a0088000c1030f080e4025800d8510a01d04402c40606d11120740f00025080340744141040040b074810f030007464209100f031041d07031300d042c4031400c00038500030382038000c000704081c0c0031070400c0344080546512240c0d000c141c0182803540030700e00000d000744000400c521001d0407010740004269680e07901ca011090303440702c400702d80341d615014028000d400444522011480c10032101881407281c7c140c1404062031680150720b01031503d20440c1103070729418401ca03040001d4202103030000d401d01c030103019800d0240d03a501090000d200d401130300d801000c071407420b450b4000030b2381000c4100d0501ca007076040d01c100740c40298480c0c2e44030300120340803120b660010310558802024401c00e0680302214040c15130040300c5000c04622200100301e828490a440d480e456404400c50400700d503441000f9080c0000007c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 242103830 1250 242102580 242102603
    0x3250e0415092303030a050a0b0a031e02040203100501020d0c0f03031104031509050d0e0901120c030c060c060609180303050a020f0a0e0306070201050105030d0c1e0501090c090b0a12 80
    0x1824020f00c0c4080803141090354001008010280c4030780d01c0354a0303009400400601400c0403103408190020114000941081e201d001001e948030300720710140b00c42d10303405007046550703140810880380f0101480c0600d60040c024801c404410500c1000c45514903a0046030403e2800d105540c00d070020300a000320140807113824440003020a1900b0500d11010100044c0426448ad8074940f075820308522600303013401c1c408901030440c403903110100558107603030700d80303403141c82c0c245c09424203035108a095071000f0510051440701084041c0c6c460000800d041c4034800500070551180c0f030340c0055543c1e10300340c10388224080204401182c4680c100c00e4220910220040c80c02c425005203046a9010200007000306030186103125041c1000c00545a02201a00c0204000d50401d00004c0e140d40e40e03000c44070700308018034a00d4014403c0c001031204000190784444040402c130381c60101d0182003c960241d580e1301980100040090081c028003000810003001504100e040042c600420501c0306000d03100b50040340c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 242105080 1250 242103830 242103863
    0x1080115081b0f041a130516030209030a020607050715030c050f130b031e1008190507050307170f0705130f0908030703090507080a02010c0602070f0203250e041509 72
    0x113200e1010410000204074505c0d603070b00d0051010784071404501060360ba1418003004250007004820844890651a000d61703200d20100c0000c0c9042a0300401135809140007540804100c0002084400c03512000d5280c81ca9802e9450290210740b5005e9010000c07503002c11615024080890041c100700c4010b1f640030503401e813910342428160b0421640c4000004840c5028070b640120014020340c052943c0101d41402801c01d584981c449100002808080008403210010400e05214801c05041c0180480c0c1c040c03650352800c90030003545c03201a0030080c00f440010f40903030040807a0b10b006549020b85a0b0f8800d02e84048400001d20641c3c40d10b081255031601448001680c0c44002c60140d00b207954081100881c600788036040444a500c12840d9a01c0340c080040140d0300310480c03150180c3c003c14010b0720f0301401d0400e0b0021b400300c40310003903142c010444540c00790a18100002c2c8040d002c05461a107103611046219243d5030140d07006002c1440051402001040540088407980e12a44170174601d00703503a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 242106330 1250 242105080 242105089
    0x30307050909270c011b050a1704090f0515030f1c030f02040f140603010806041b0b030901050f090c030307080d0608070801091209050607020f120d0801080115081b0f 73
    0x14008511030300e0304584500ca42c0740d84e11642484441610b184298511b0302c0642e41c0740e540700210300c401449524803020305100404940c058800904c1c0d030103002d001c10b8262040284c02804110b982c8170a102d92820100c409040001d072220018900c0c2d03001b4280e02c90452401d103943c000c1038091070205030b2180c039000809003050020300000c6c95803411001019003090066084202c4900c803080c01780206000410000303e0005200b500320340c0000b445403108004a003440e52074106500705c2c404d41c1400109000e101d5405520642c4520006200c20240d40c988885454550503c05443c03a419441407040d0f0f4041400703000140030400000b840014031035600c001c1e003810040c803070740f1a2120b41d40d00c0042400b1312107045032a0032650010302e4040c1c0d8040c00c1070002400d5024900d8064001c1c1c200c041c0c1c0d04100c1e1588081140c1400c2840d04441a4903602d080c01000000709004110700340d42004c0045800c4d07036820902c3d03000d80ea074403000740140c1c90150300083c40c511480800366074806810115035030300d03848 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 242107580 1250 242106330 242106391
    0x90809040f05041202030a02060a020c160806190b0f0f0f151b0c060426060a02090f090c0304081806030106090905060901050f0f03010906061e08030307050909 70
    0xe560002c6124900340c2099104806514000c50a40d0020440102c83c581c0c0400c05641c0003010402c01a1945040480c891030001c21003907403010720b41d00340301c0420b04480010b001403103541c50b050078620800024500b01c003507a100d001d0064002c200d4604c401418a0a610314008404020b0007000e5012000b0700004c010304201c1c800c0f000100c3e4009400500302e40d44941c001181c8441c0d078004d051010004d0041030052185220700203140000d846903503134034100318a4440c08416007900f101d80f1424107000903002580114150b52040c0c0e1112031000c014201852a944a03c54a040d030a003140e55548980803a17a0224841000780d011602c1d10120f140e0340e450195005e4540c0d903890140d0541020004000c0321006001c142c4142d221070010881c942e1085002d409030300d070a0f100160769200300700100b4054442038030003c0101c2d00381030700031070035981452000e8030310132142c0040148a03594807040c6807240b00c00d4a6900000700c042049501034180200b0032600144403168100e14040d0b0594021000780 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 242108830 1250 242107580 242107601
    0x30c0c020d03031e02030417030601113906030417040b042705090601060f2313050a030305040e060a05090a0c030b0303120103061a10050309151909080904 68
    0xa40d9010a5001300b8401c0350201914100000214074500307058a41400c040004400d50502d440000002481039108070811026440040e0031611030034146404c0601c1003106203002184001c11000c598412640401c04060040c0094590347c615203550712803407007851898030640a900c5080000142d10a005802403008190040c0107900001e540b41012040440c01707540c10000d2810501400042080410090b04440e014203100544940b000425600004041c0001100304052682e0414007460340005208404c0c0302c014160a542d220410003034030b458540809000110144014410800d81d070400130382040000300b510b04445c0d03a42c00001c40c0c070841143c100c6010b54580d408001c0d0142c250142000010f0304801031820010154044021034038148400792016459080b003904200320f40d040a4440384005d072804c40d036a00f1501c8080c05070707841070b2400080da01c1000200c0d5100c20940202600a604902c04450021581710510018121210050703402407001c200031885556548500826075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 242110080 1250 242108830 242108837
    0x11040905010e0d2a031d01030b1008060a0905010e0103080702060708030c190f050901052107090e06010234050a0915140a030318091517010615030c0c020d03 69
    0x224130640d180040c0700e8a590f428440c002007950f0780c0d0010b904080040d41c006520556042403074520001200504500c0032001e070031440200e1031440e2181c0c4034889038490081a1003200300d4658401c0884d040391024404d52104040100043c07001a600c507004281913030004008604144039500c5801c5558015600101220340c000f0304038031110020215010460340c0307820203072a034418180014100c0e101c0c06490030704109000885044030b11204010542090900b6001a428a04141c024103840014004c0403084454000010758940c400112301d50781d503102c2d4104418030b40d000103510110300700d100800201c45030650400302e8181c40b40d80c1409c000f0940b20501180790301c010f541f0081046c1664120701250007202908180340e445202900d402c9941c54035251880d03c0003812424140300858014415242c2881c0420a040c40070300107440a031035645c0198924520b0f494100c4c1d0895605100b00f0040702100403c0a4099000b035001c0c10f2070040c1420410030703800c071542c0000c2c1c40344a54642200070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 242111330 1250 242110080 242110097
    0xc01170901090501020d050612013c0908090922060e03120c1c0501030c030b0402180412140a0f0305071103120f0117060a0c031404051c050711040905010e0d 69
    0x10b031516071000d100c1c04227100001c1000d48035906c542a082c045607150100c81070107401a0000c8030584041c50061210885410048003003030346000072450303120100356480b030103808000c50411500031001724a500100303000c0303040501c0a6903c031800780001c101c0100701c0380014090700081e11040c1c00b00c944242c0718200f04998502c5440e56187e49802c00c00c811081d800c2c584401440043c5c2800d030030405598210003809a50350f194800641070000c0071910300a10240702c000d12007040f0400384c1c2500300166a8490050b815410900c0d21301a000c1c00c00c8403400682d00c4202822024001c4d440250040502d1a0100a070b64441c08075602d158841d21240e138406a509013001032000f0303004103540c05005040804141c568a0288880c2c3e11400904900801d654400440c1e49582c06980641e0a0f41344c110b488105500e40740c1041c90321803a401c0786072164443c03041c1c540400f092041040721142984131a07030004003c400030910009080195040f1120341d038640b00230400d01c40400058003000c0441e96141070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 242112580 1250 242111330 242111341
    0x20d030608010209010e130b100801050901170a060e070f03080c07060206271e0c09310512070c140102030a12021804020f0909090c01170901090501020d05 68
    0x85a46561003181c10780d03c10f005458807a03a10110314104d1000c06c581403e10704000b1800080106038002c007a40e4407e004141300c40b02c06402411803812a0700c21210203a42d070b80d888a091518151514881e10a81c004041140c00145d0f20740c45921a02071403012102002d80342c07034044d2142e010307540080d64000700102d001c2c41c042c0010007a20700640500c0c40036020a080c52480c0380d007042885101c1e554584441d4400030290b0034200a1308100e00c0c80000c06001d13034541100010b03124880015030a021788441e4002980c1d51492885009242d004071512034441824203084c50003854100c1030884290080002d10f080c0484c2000150200324040c180e25480e00c2c4c40c00e42200001e2200408503030640d001405035010050f00014009034071103082001580d60301c3c001c520b074240002d02d009115841840440d0310400302000c00003500c01c18005844030007060b01c45205241c5e40740140003850340000c5c1c20310302c0318402042c241149604500001c00200b0040501d40d200da0980e0000c80320f015029a49004014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 242113830 1250 242112580 242112587
    0x1309050106121503050c060a021c051b0106030206041e0306021b0f0d171503070e07021509030a21022206030e0d08100b12010501090b19120f0507020d 66
    0x1d40c3c2c1e035a0554400021843d41c0d403000d848100d5812075602c5010082560480325009005070002c800c20701c0400c00201345038580c0a04550040007106514420443d83c0d00b40c803007414416242a0781d0010f140e20308081c40c14140c0484000e500c40d000650103482800000000c000780080c14008110402012503110720300c84aa1400140c500c050800b603010148409119402c030401c02100c0c20503001c003400d50b40d62081c2d01d5007507462000c00c3d5605485002400201e1075491a4600d028840d16402d442800e0003054101545420558040000784c1040000008160207002c001d18108401c20400340d5800c42c0010390400c070b070007884808854510b82c0310107214540340402c41c1d4018182e181000c01421040d142e40991710301041a504003400001c40104a648018000c24001010405410b555aa00441e001d1500910a02c01c0c28041440504003160a208210030394802c02920786010842000b09402117130031812040b903102c130650781c800000e490b101081c003c0710700c02e01207038008000c4c40c005808c005 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 242115080 1250 242113830 242113841
    0xf151409150a030209090f0f092a011103070303060807050f01120207020d0804080705030706080f0711160b040e1302060a0c06110a0203090306090304080d05030606040807150207050411030606130905010612 90
    0x300054010130384008120005031302b002c0034440f010583c910b5440d0a00c006840c42d1019a0500c00310780b00205d248820103501d03401641c1914235444c1a6189503a8500c1401001c54101440a0110b0301000d5601465a015406046103500090078408024200d46401450354440e0700310030f030a030300807010611250400b041103200805492820014514007081240d4482c0e101402c1c130400c100400c0084403c80204010800003010901c8400e054641c0d500f0540c135599100344500c650850581c00060b51030100040b9071086076030041e04c02840e20704030f9501190311b0006910111030300c0ea81c80421500c44c0d01e01e80301905090f11207030000c6035034802030310815150440041041d400340d4420401032201c0480450049660340f01d03820043d07225121180001d52500481e0480a11481011800200b42c4440040e40c0700300901502a1401070b604e0358188010f580340c0140f0280d800b4010404500307542020341c010612010484000c1d410151242c040713906894003030780518005404250a48948d81d0f0b0761041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 242116330 1250 242115080 242115091
    0xd05030a0e0303070c1401030f020313051c0207031202030408010f09050618030d1d030703030c170c030c03040f0b0702061806060307050114040f151409150a030209090f0f 75
    0x11030408140d5510030117141014000c0001c409031019403813620364060382040e4103a00041c0070554903031808594201151401c400165a103108403030980340e5080c468111400300013125400b600320b44e41591290b40c11801d0072250002140300c104000114020207205800c4400098031002c10340c0c00c1c050a00300c0c80c195028050110305000c50b401503500050000440c1c0b001000620b0116420002d10300150307050703500c80034580c264000001d40e041019811361220401c0080c503261383d04500030600c0910f401d42c004491040100310b0400c0031540321f010480c0910781c0030348114000310400080384d40700c601c80d41040d501c0c0c1000d41d22120910982d11841d40d030500060a5020052286290031000070780d5400e9039118460500011010810850b400e40d421100a032403500100c164040ea00c0901840510900d40c18000180000012200c404010000c9840c10400208059480f401360ba8541d07070713194440c8812100f40340e8204002c0e19503442d002a5184240c2802c07007081c1c4103280c40c224034040701c1d0000b8035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 242117580 1250 242116330 242116333
    0x40308034c0806310803010305010b04180c03020f0604050409030f1b031b02011704050c01020d4b02030304050106140303040e090102132409060e0d110d05030a0e03 72
    0x1003006880e10807400542c016281c0c084405580d4407114200c61040402201405c00b003800000441803107415048160b0460b010388041081140c0c02c03000348044c80000b60000c081c85440082000540b8042000c01010072004044620b0541c3c0c840c00941143d410300c03030031800f103a010b0480c00001030700f10400c180b030440b0f080c00f0a007804007180d40007005406035040c01c142c49a10507a0650540e4070500c00f400840414030402c3c2c2440c1010301f8020f565030219201c80d4010f10402021a0800b44101e040520b05e640e44502c180c0300b8802e2512a5015403151600f41600042035901c44180c04140300031044000003039005076507079040900b015405c2d5486a00141c039005021034045d400358400008540032141c1d8102418142c1d1140c1418074064442c242407030303a00c8401d142021510f0031000b4001c02d040b04407e2007840804800e0711094403420414070804000c2041c1d10360401d85810403600040100f44507085044101d5880000103004415001d4260364641c0042280e404082e0040104002c4020480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 242118830 1250 242117580 242117593
    0x5030105010c060e07051002030408011505090a090201030b09070c031b0b06010c032615030a050705010e03030403140303010503060703050c030703090213141b040308034c08 76
    0x40c1c020200b00000610b42680d0740200891104180310800c0078250042030307034081104031000203550360040d001e4202903528005560a4000342074200c20101d03080540260310a56820344a0030060020910603410f2648030001106e49981c0c201b803451040800341c4801d03074030a0140c2001844086d0a1501c0c800b1750b80440c4034600826103050031030b81d00a2091070011001c00103480d080340d0952140b0080c0c080c00c04100303d140c50044104050a205101044010070110100c100300760b590803141070050a641c100017400d006651061511209841c805800c03a4034141d40d0f0303640d1642265001e20000782a800c040014007007450103001d05034100c1d0041c58103201c0d034204120350703504030300c4050810814542e44030848411511808540f01d05c540310301c141040400c81052844504038401c40e07010340c50a01c00c401100740111184166010349400015007411a540e0300035002c000904841f1648810780803c0f280a101c03c01c003410030b0703120000b42e6020700148580e07040c1c40d1003161140d0800c594541018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 242120080 1250 242118830 242118839
    0xe0a020d11060d020711040b1009090209010512010b071106130e040c0308030712060902160f020d050307050307150e03120c041203211503060c0201020f1809010501050301 75
    0x1266400344040d00404070780880301900c40080c2040c4200c00c0a441081c0c00807842c0c00503c814040031164409040c1d9083c488501c0c0d410401030b400b8800301b04c420100341043c10522246000e83c0c01381941043c1810003c0c0f80441d04240c0d01c82c10b003c00d074020340c4e04071000241d506c100030340c203420583d034120265003690514415440742c08888503540203542524000400140611494041900017950000009a5a07080c6141c000701440e960302144d0340500c0c107001c00040c10099038404c40705958110704120b8141c8074944d13504a0303084810107050741d110b140030407400c0200b00244014402d0701e10078002107940d80390600d041c02d60740000490224a4a1510880941d90880030003183c0025440b10340c080b029a4946030124140e0040750011002e983c038002110041581040124800f00c1d80040801e00d181c3d1520350120a541e4201001c142c11124050100000748c2c8581004686003958000541864222000036a0a4014502d5420b0b011128510300c011414581ea255000d4035081c40c1540c90756040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 242121330 1250 242120080 242120089
    0x5180406180c0306051308040303020105070906020708030f07020d06140a0f0c0801050f0a080f07090609020f0a050a090b0a0806040507030e2d0a0302071e050109051e040603150e0a02 80
    0x5600c4040c00045d00d840024541461044d01c41891079030148072032381c44640b46d0400034003d2100300c0f00000402d1145c01c02181403400040d1842c201c0e40d440000f1446c02c00340402c618032070380110000b241c108000c11030440026403540140d9180c0410f1a049400920740804500e05441c0f01a198803211440c01d45403103085a0b0007807155041d03a00030340351503005000d2400070400102c0c0e03a9001030702902541c407010440131404101c42049036000a400d00500751540840400c80c410030b401a103101e041003020400f00741c010700244c844c00d00d042c10540c002d00d680e0b40c60704560341d0102080e0800076541104010462500e8842d45800640500d0208842103000000c03d40e15900040440219900c091080244128218404024108180c181c64103c4480c3c43c1c00303955894280245114000390542c038100348140404d50391f0072210140c1d21140a03a142009002030214201c040c40010711505e00c403262242c0741c501600e4011482559010301102c2d00320030710021a1f03054069415103420456403030000d80c2c0d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 242122580 1250 242121330 242121353
    0x150c070f03270b0901030e0c030d26150406060c0b06040b19170705030a0b0a0207030e1903020111031218070e0403020a02030105060109080312100518040618 69
    0x925040c0b2007000e03001018091501c0c20031090441040041c100c01140e1001e824016000c40c00081e00e042c403945104281d601c5d100c442404003560194020454111002d00c501c02d20084016401103000245165907400000304030b045808100500c203841243d4654280b510802d0010070f903528149085000c80e5983d01100c510240c900e5225a844001c032074104d640e441200d41140800500f86003c15643d0b0b80300d142911104a610040e5000d81361340041c1604001c980310030b1040e80030400e0201e1303543d6030007071000940101c5815820025060200d03000c0380c4031007100c0590b080740240b51101052852000510000c101180b8507080d40090080c01d44a01304480c800350800700c0b610310041c0c24107000816a10303050017540701d0304202c100c2805000c14181c01040c208040c40c0260000d00951b500d440041d00c21001c03a20814080782d00c200721101005c60040410b513000bc1c69080082061540d03400000d119091215410740a0103000d03050104009051041c4c81560881041150007440b05480354100800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 242123830 1250 242122580 242122583
    0x61404060620010605061204020f060a050d0926090a060201020408030a0e04020708040b1201050102030723010b0310020c16050604060c050718060602060a0e07060e060702060c150c070f 81
    0xc0071070b0542c01c0010b80c01e400020140902404407510b84020640c0c41c02c0300241914103a001e041141c0e003c0700705042403021165019142d1315000d01e84000c0d01c0421004068201054581c0560040865003c0445010b541110b6900c140d860f81c07a903491908201c403681d043e034080d01c196881080200407a21010054449445141c1040b800c6441c5401c0400c0291181e0300009000b201e00050216220700c0ba20007500c07049152034444030315a030701c600059984c1d100f01e031009009208248040701400100750440c40000041c3c0001094817010a0302191401070310040102c1c0b02038000c80d00302c2c1d151004001c060f082040166444950030f20780030100d0700500c03c500807502081001143c00040c07182c20441c00c00103004100b0745d01c400100c0c50740140010308003402810018050f00b0042001f01416002d1080c02d8000030700075003a05498008241c4c1c03051606400c2c80e820000612450016a4903d0040c19035580000301424444686503000d820080001701140000e00d230520400000c520043c400003501c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 242125080 1250 242123830 242123867
    0x40f0c02010c082814010902040314010e0714030a141b01090e0109110f0f07060f0b01080c2505060f072613020607140c01030b15160b0405010614040606 67
    0x4500c02c00314030b409805e80e00d849031406549000001a02151030f030080007200d001d0503208416480c0320300101c0c02d0303a440314100c060340d50041c101030003c500a0107103620307160030040c210303107003020b4645c7c41d1342c500700f0078100041c00340c0c00403e4a5100200c49094101020300c0c2403801480150410542c03081c06601030182003c003070b0351103003140c2c503a4a1038030844842d40034a04400752129070244203000306600c1000e04440c0141441d0140d8a115458002d041a1840586603180b441d41e0f40b540c80c0c80e15400003164013200d1020382c4141c401101038070400071330180c008c0c4080d15117458221500800c00c403000d090348003008500b618808401c242c607900c2d84050888404d90700e0312134842c11514040d000801d000a0740c40342000525400300f08114074001e034244120403e540804c418400103404841c00d00001a411407680200c00d0500000c000c000c2c03a18180d2140b45080448140d101c51440c04021201110b2aa40d929400c2c49030b9a50f0381c09040c800082164244002820310f40010b00c0198020040d8019 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 242126330 1250 242125080 242125141
    0x1605010306360b1c0302101103040f081e0d050106080105030d031a06030708040c0509090c0d0807060501030507030b16050702010f0c05100c0e030703050703021e040f0c02010c08 78
    0x11203100d421983c0c20000040c904056811046542405500803060072409403044182c0862104400d0140d00303040c903201d10390141141c7d80c1d500c88190440450400304c0750440204049030103104014042c0040c03105c00500305403a601c2c10800d01c401c80318107801020034040c070ba000401c040c0e61f0005030441070405916001c0354806a260505c611402803d41c900c0d401a800300410060f40c1e400702c0080d00c910301900c5036803d110754400030b1000104003912040080e401c00e01402002c2d0410250301034010f03114520451038840c01d619004101c80003030b00b00701e03810380080b9810804d00031010050f5030400103c9640a8a48000c0e039400b514078030954200a0500c404002d07071902141c00307901900e4030140c100080d504020a60a161001411140c20301000302d2200003211101d4140003404106499000009100c0c1c1030458080011198198107010071124a582000349582c6884c0203500d00c081c045171011640c81880300300a0300f5240014510805c100b1140104820714030003500d1820040c18030301e4243c51 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 242127580 1250 242126330 242126429
    0x30f0d0608011a010314010f0605071505040503040608011508180f0109060c0f0203040f03060b03030c011b09140a0e09100203040f050d050712080c07051605010306 72
    0x500003a500c400c4695103800a07041e203880e004215145481c0b000d81e000c0000303a503045c841440303d0700c00f0b001e00701034201004020300c0a54042c400514905008155100e42042d905448034140c0e079003202c040326581c0020804000f40758003c107529000d050104a10408284220300061800c0c500408500e20003030b00403a1850013100900141e004560040024490307103c1c1c0d81841030290140d0b04080d4001025910950031181c800f00584080d01d414031400d507007142c55512080041c15407580240c3d850300040103d400c0380f050034801c40e000210350f62150000c40ca08000082c10910b4039170302c2401d204020034032100703140d500d512002064815103401000c441c1c4031032000c2d81c644031102c00e61100c0c80b031002050009000816411500941c8244220340c40003031469011a058020719000404141c00840320000e000c2c09032100641c0303c0d9405800710f05140198955a141c03a0f09201111507031140d200080c0201e5a160195401801076405168003d4111103120380d07012650400100740024942c030000c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 242128830 1250 242127580 242127607
    0x80112030c1518051b0906040e1507020601080106051002030d050c1c0209101b0b04050312281503080f07020a06020709050a0501060f121d0109020a09050603030f 71
    0x3480004504212030940c1460f07420408440c80c0c01a40d030ba21403418288001a02c5003456036241e0000742032240c0c01d032218402d0001500103240201e2443c01010718201c00d024545417400c0c8a02030b070703500800032945860700c158211401d940107a4001e1552140b4002c400307800204950700780624480000302c5588903c2c8485d5240901450300d00041242c02070751441d14201e4000d000700c000c0448640069501f40c1409658958180c0290400f041c01c0c503601002241c0d080141991041c000d0059920b4100200004c445080c0d08584035030704200b000645810440c2c02c1201d16443e190052420440900240c1d03daa80c052040d01c001001c8110000385220880b070620b06031050369038081c00020083e5150700c4040d4642485000710800c0510b0700c80002c100001e6800380718100d50b440c0d12403c00b92169050304907407450400754102d0215444411303c0100220400b41e50f04090a20b900006090f02d081c410800d00c0040e41d13204103406800c12050100954010049074045230213008655a1018500d0009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 242130080 1250 242128830 242128853
    0xa08090708010608070810050727030803041a06090c03190b46170102090a0e01140303031501050702031e0102120c0a120b01030b04060b0901030c080112030c 69
    0x703495080510000742e540340014850300741c501e01001c2d51102420707030302481c007182c50407103080e400281054584080d04003d42074541280d05408400d0b165151a5241c041c0c0c56441510100c2c4d101d4100c0400794a09400d04110a40114007201c440300903040c692860038403400050015403400c040740380c010780c8070b0400c0c1d8000c03000c01201a0403c4d00740107100d44240c498a2010500348a800101004072110b002e0242c0a0b1a55002080200150508102c0054152031a2484040003907600308001c009681c1d440e501c0100a10510f4144040b96040102d00c107412541c03010f01e2400b80d4028001e00c480c060001e0030b014031248085ca013881d21a44a030000a203801860f560003403c0c109001c2400c00004410f400410300260140002c4080744c0300e401144d500e520882c600b00c0300184103255100c8041074a60045100c6120500d4042900320780302c030018084900e1544100c0740504002041d4546503014003490342698403500385204150b143c44d44404188409000050800c44010b04c0c0008119805140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 242131330 1250 242130080 242130089
    0xa021c05190308011203120207230a11040209280b030c04050f01050414010309060204080f030715020c0d140708030708100f0f05011b05060903030f010f05060a080907 73
    0x4481c000d01000700c040480c41151002607000490501c0041010a1015495100c0e01d0b4035540b015201c4684000c02402500403080842e1680b890f007000070030f2182d034541003981404a0710040c1139400a6403414224200c00c3d000c0305405203005100c032944035a103100303400c00701001090040340b083e5484a002040b10345e50342c1000d0750703c1c00d01000303110a0b0321500e800742090b10400d80c1c94500440c00d00006403000c1c0114820031000c003086d5110080c40c1e5100b6080f544600c0e00c11100581025222452241445d00c10003110459038030100d888010321110303c40c1480c1c005500c24046140c200c2aa000e01d888103002400c0605002d2080c94020b07040a0480c12a0710860b0400d10680e128201710030020310100713065540e01c2c5a110280b00c00b29000c0e44c034030f08050480c0e0901244e40c011071b20340001518a40054010b98008461083d5003001192046c8507da229500080103550b9a2514030005d141c0c1b402c0607040082da02c200120144040d440e04000c554080d040c904015030380b9561118a5407900d080ca402 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 242132580 1250 242131330 242131333
    0x1302030c0d02160b060a1a130f080d020606041a15090a030c03030f0906020706140c060408070201110601060903020f060d14061302120a02090604080318120a050a021c05 74
    0x8107911443c2c6018881c3c0520b0b03100f180d09107501d0b1075480030030042c580280181c000491400d1a9825003c03003c0d001030009034800111010b11554610564003251b0ba03507031000e041504592546a01e03594180617042c1e0000303003198100141d902d020070f4200154001d6400c7d5000391100300c02103154090440540c0c1e1580b5005104c000c1d01d54407441e10304112680b40c80200d01240c8065400d54031140900385440554001d540200201441d1080031070310100340d03445140b00b5030401c0208000f2244103008142c4610b0182c0f01280c1d542b84030344001414020383c1d603960600e5810484c01030001c0c1d41c0c002d2032102200c1d0115508402a0b10140000d5070310300c2020031041c5001d1401c00c02c00442802c2e0710140740715607030846001011344070381800d00d0181d100311800c2d80c40050501000403502000b60f4058103a03410081c0807507080540300c075040c03465030f406014001c0c1144040031152102e40f425141e440c8c190080d85000c0c0501c01802e0f91020f0f62043c1e4880c00a1081740f0310090b05100c0c08910440f09502a0042c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 242133830 1250 242132580 242132587
    0x30b01050d0f0903080609040f110f041a0a08030a090605210a0e010c230c010603050613050d0504060c06050a0b04020a0e03010605090609130302121801020c0f1302030c0d02 76
    0xd503503002003c03030320001c401007844100060010300e420100d40d0f101355088803d603506511580d0300c104451105019041d80440c0c4a8a01406615680720f82003032504901c48206c0055400c40c204640102258030903c0b0726072040000c0d00d4416488000d840449407139081044e110814980c018040d0701c00c100344200f5081c04042080504589070b0050076400c00d0300d1000304502038030324108680d0616452209000c036084030b018003c110001034014413120840d58000a40c094499035000d08000040d54103a10441d080220081804014444032001c0f11807410001d1410385004000740110440c101c01620b420ba661002882110b2503070072036003148000800866442e152510098440e291140525001b0342c230f0160003103000d05105102030b0160031f000304a2010380d82c501440c5802c05040d41c00803021401100b13a12503100c2c5c0001c014001840038902590580c04400000a1801c4040241c0a200341888000910700c3d07103c070300c40303107884103900c250159503552840203129040c0b0402541c941011b2000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 242135080 1250 242133830 242133851
    0x20105041e230103060608060d030503090c0303070b0403020c03061902090a050307090f060812120406090615091b0e040f0209060d050412020c03060606090d0507061d0103050412030b01050d 83
    0xc14002c0d211500c04d0f24104445070700e414080b90119411112940c0001a205241c8007181c02400510b6210406001b254440c06000e000301c0d00356013100c81d0446644c0452000c3c070007055014082400840d030180c008200c00d00d0688184240d0300c58602d0845c200d50303800204502c90391206890340c0090403000d0102c2e0125541e07034220200404000c0014540585084404a031a490104800d040c0221460083e42080d00050130201c080001400469040790354040c0d1100292007401160928104440c901502600d4100d900701900c80002c0c64580c92201030798400b141303641080c1c200441d400255000244004500c456a009100e008085603001d4800710342c900100021b44c120b503108500c1030400c4100c40340d07001000d03640d840c14035851940c1078000d000014034604040020344000310004010308080a615240c00e401e0a4494202c0800207000c0403c0c4411401008120035640e8802c1ca0304100d2171806031110440d55080e02114000c00d5166800c003000c5a00c10400e841c000550040d04010480c1c21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 242136330 1250 242135080 242135129
    0xe0406031212090209060103020f0403060f0507080c0c060c030705040f0b040303021612021504050d03082406030a2a05070201090e040209180709020708070506010b0403020105041e 79
    0xc01c1c0381d650000721822840c2e40000c11600803611600d038098024002600e0301001075000c2c0d0008040000c090324103000001c04242c0c28000c150282249030740025076401c0c00d0700c0050008200802d2012000420000f035051080300040d4240d000c14403802450300c9884514040381c0314801e40c1d10405070700040500101c2d05242c203070010001c4a10039001c4840c19450200440d8810005205004601103185864005820720a03407941110b4012202145441e0725040000c6000c00030720b0341540014119801c0151885081c1c0749030100a60403200380424685040029405d03100042c904c1098948484d0039000e0758a04103941691041040c0300e80d4505518900000c0a507002400f081e80002d1141c280094800c0019140d0b902030382d0050f01c03103840c640d1000c1c0a030300300906042503150180720f6401e00003155440c1744054098039110390f02103941ca0b20325040c080c2c60800b06801259440c40204402c00040c1c2c2c105084400325094442034910001e00c001c0e240c0e000302841e81c1f052000c070f16182da10f002543c81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 242137580 1250 242136330 242136353
    0x30c03030c0601080f070b120702070905091b09010503070911040302120a060c05030c030103060b0f19030203120306031f0b060708070605070e030318060d020c0a23060a0b010e040603 80
    0x620700704450b9800414054175548041c1ba2291500f111f10070400003070100c43d010142d541c04405e42c011610120341d43d100ca01d0840343c0440b401440f0350000d69245169100681c82c400340c1c0402110000300c01e506003400282c07516a51721600032007941d20030f008910031a00c1d006407401140c0090999581d95210502c403603c8140f2110100d55092400b40a0f803101c2c0e01550030340380112a01e92007181140c1c215600d00005041c410b40c2c203070307010b60700c0b8000c040c09035620086623000c0d0007807d07006420541b0f14418145400c2400036254884c40d014002c00003035460000b040041c2c0c802d492001030740e08007009290802007101000c5aa04840b0000319142404500c10003005800d1040804103e07543c0d890354126040380d0711500f00d40c2c1c0f64000300004c21b888a070206d0715010a003002003c0c58036214a0305500b0040f03a00c041109611500148040400c1c488e030041c2d85100000c4040d87c00020090f0b400410741c841000800c1c075880c0e01d5a648030000a070b4070407030007003641040240003048200c3d100d05104108a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 242138830 1250 242137580 242137589
    0x60902060c250e06090a14070509040c0203091804021903030314090d0215070905060c0a12140405211603111519021906050f0106030203150d02030c03030c0601 70
    0xc82e03030b2802c40a00034805201c1d040f200100f0814409480da5020812400707400b4080541c02500c400000d00c01102070348401c0e01443c0310b9207525a035441d02c1000c2c0701c181c690041d04c240554001740044c1401c2c1d2102a100d2119004040300c0d03640b40d5483d480040d8100030040b2007908010b41c1281e000c820184c04d540400d0784109901998081641d641d8032150343c408040c2008030050b001911031000b440c14841d030300c6030003c07114241000c065031030b2000b003036540e0001d034000c00c2190303c034505c0301007806a5640c0c4001c48541620301000400010f050600c070b14821031290f00c0c01002880010031410306401c825407140113003a41641c8822b50021140d0130b0100341c9000c295000181c001c4011124540744501c0103106015983c03681c00c000d01e0504500d03000d02d01c031200c0002e6005011494030040983d594111f001d82c424500001c01d4100f001c0c100c051441c058010400b803602c1041442148480742000c1440c0c0d00e011905660000e0240c070101c1e04203644440150340610010070104865130300411000d040e0ba = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 242140080 1250 242138830 242138863
    0xf0601120611210621030301030b010e061f030209150d062405090a0e010b0d0c05130306020928170309010f1b120e0f1f0c060902060c 59
    0xc0b4100c00c0d4201d6920825281c0701110215510807400031415060381d60b80700c1e5004211012a00700341c0a400707050000c03103418500d19000003005008101700008020701400641c0b00791307000761500d100403403e1001080f081c40301c00ca1000710000c00e85071080e0101c1d501701c070007d413900e01000741d501c141080750b030800100e0304100c0d070034100d0202e46080141c070754082102e038031f0440030700c0d111540a003520f0951003100d005800034004003002c946404040829402491040d505a940341c0485525204456006250404110040113410b00d0580760807021030035a6042000180c1c1c40100c82c0010340003c03120071041c0120140c56107801c40c0e90011980c03050803282c81d04c0000da442c00c261081d9070740fa0300c26040028080b07076954021040070f51080d040341783c62424072945900968552344038480e074031004110b54400200500c204100070f0903c915802d10001c4190784800290395000311407000600401080400c00c103001481c00300f44807030398000b01481d50b000340c0481c1e40c4800d40301d801a250040c200d00c604a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 242141330 1250 242140080 242140091
    0x5011404140a0503030a0b040f060803030f0708060108060103110d09120314060901030803100e0901060f0b090901060f090308070c0306050f130f0819110601092307020f06011206 78
    0x61550200d40c80120360740c0f08010b0b515560380c0503104402032a00b0401e40f50001d5445103000303504040d43c030500028050340001903840b40740122001500d00c90041940e0104800303007081c003401d640c00c41c3d102e503000402402c1c04990a640c035261030096010761401c1404440c01d011030034013407209003400e0240c141681e035810b1145540050a40000c010141c1d030071034011010200401c00300e140740014640107540382c03244034205643c4148013047c20030b040d60400f00d03d0359100703020860100350000400080c4160b00310f041c2400072075000560151014400c2030244000358403030414441c81000958081d50340542c1c031075180d0b552810312480560de02c0c0001c8800614040c0410385101e6017074101c42c456000300072524150b0155070f071451000e9440000c1110b43c45014405007030104441d898403d035040310355545402110444001d1441c00c20182d01a028249c9040c080d0341d212090360644007100c0c82518005661900c032584120f180003259a9584142d004007000031990342219094803400300d0040009110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 242142580 1250 242141330 242141363
    0x5100e0907080c130207020d0b01090b01031823030a050c07090b0d110d020402040803070506070f17060a03020405190c030c05090d0c090c0c02030f0607230705011404 73
    0x180c50200d40541c0080f60301070404081940fa0559156940210a043c00b5041c0119076011921004c140710f0b007103866080d844014400501180725054207000300b46000d0004540086500241d04294400a49038001c030b400302010300f24000d00420b101109010440365141c4031781400500076004094400b8250040709070001c0c0507a124084c9a25050000b00a1b040401d1a0340e260b62002508a4140b03401904624800001d0ba44d039102800041a8800107950781c2d20107860881e080c130000070150000c1c00132070b40091581c2507206d104040c1450506001c0c07034150300c03104001400c13440340ba44000e6101e4207040170030200300000030310b9030403512079000180803212520a0aa0688040c44a2500003a1040c440c1104c50304e0710184032015240150b0010584940f6a4039040c2524414010400030503440960345085040801c000700340c803c83c080252140d400d00c140000c08092400003420000856810744951010072801158041c5600070020000c8071040040321112a00c101e40c2910940422103c250 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 242143830 1250 242142580 242142583
    0x20a0e030c0609060a090902030a0615021605040f020705030d0b18160f1809050114010306261005040b07111501060809030d0504050a140a20040e0105100e09 69
    0x140c8482008011038100105541130001c00c1d0820000c0310b08002a812002800d1811803005502503036083c800402e10b1414801402aa01150a003000840d4031400c491480d200d083c8d04a9002c1d11400c9a010030300445a89004000c2d008040b006003072404009130303210440003103502454003203409503851085801824904007107280c04451a1b002e038000ba562040401c0d01c00c5100c12620303074450a001680703480c49405a8101d24254020014694ada04014000d00c100b2994010500d0000d20f01801418240000649140714600d08401411483c074404071400b5424048038124690b903000030001c03441c1c941803808107418195a1100410215038480350b130391201044e00501180812400040c5920b0004c04403240d90005192101900003841282c0780e10a05008642c004c0e40600024800e00450b404c0c80021500011440a0a580202c1d50745e0f00140100360100f0007120005140d00307083d2111000705001d0208880d0803e0207510700802c01001002c1a210b000c25504203100700003259481180301c0d03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 242145080 1250 242143830 242143843
    0xa020303130f0e150f040914100f020f04030602131703030f0f04021e01050409020703050d0b04060317090f2215051c05070816030303180206070b1008060109020a0e03 73
    0x3900000100d42c4e0901c1c16040490010b689001c0113400021149043c3e25402d10351070841c548001d03940c100d03420901c82a181401a200c002d40003040441c6004480a0310031010b10503803100801d1a03401243c8007003a0004c0c484000d00804081060140b82200040340c2501d81d0300c21140782440d50704035030219200e91244005644500d6002c0c003480710303c15484000313a600e20f414411b41c90400a00708030100d01f002c030b64000750000e244280c41c0d0a8403110000f86e00b20645d0b5112151900a0389003410400c0071a48020300900402400b480701a52005c0c0e140c00f183e200c2c8464034669401c00e400032a11600068600301d1940340482c422000c1145803c0101c1e484051905807180543c0703d034250494442c030b40900a042c10441d4403c2080b14a50b40d901c0901038103100303041941d00f40140140360104107241c0c050080c640c03103000e8032441000043c1d45a00041140c00f40403400703041c08510200040baa8006044000041c0c503001c806c5036265139681104002950201e00040c00240070343d680d00c5c10908002505 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 242146330 1250 242145080 242145091
    0x390e0a020a09030209090a150603020a0806040f031103040306230f0609060411090405010305060601020601090203090d200f0309180c12190507081e06100f020a020303130f0e 76
    0xb901a51403841c0c080120100d4094001412802264000c0c40050050f030308a0f03100aa500d81d01042e5980755004104588456900c00300264100d00300300000900090f1036800026410304126012000c641c00d00c0d45140200c0c0c00040c825468110070241100d04484108e41070b400d004007040c981e5542c201500c006072020f80340030b81c1101180c80861102d01d81038000366031070341c141c1417454101041d17503001030306417142a80b050301c07207800c0607081c4111941d040c40898094100c5074825451414107070b15140e500d0001005400030031040000100b48044000c010120b948604011202141c01d10b40c1c1c4a034803940304e07650f500d10500303240340c00903c00a051648a0700c510746c55100a030405540100c03481850000402c848040c0520002e4182541e00601ca55070282049a07130308076151504150306a0388a22888030700c02c0480c03100041000c0e0fa5203900c0c07420400012031406034228160560300340d2a00e141604000d42c140004a02400542c0c449540c040840300c0301d104031150707a0740c0d510341c080e0124800e590 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 242147580 1250 242146330 242146337
    0x1905061006030213060509040b04060b0310080a050c090709090207060501060801060f02070902070303090c0305010c03050c460513060c080301090504020f0a081b040c0903390e0a020a 80
    0x11304100c43d07405100500041d010181000c203600c211280000e08491080c1c120410680703021051114158003070060101134034514000340311075111502c90b0b0340c0d9941500401442150b01500103010240311300030080043c40c40c070506640f0f841c031600c0c0100140074240186400103800c180001021031007400b044022440a80180080d42d0404402c04040d41c006c101c15000c0c19250400e800000302503a206100840c01031000040b42800907100506403007001d4040304640409100c0c000600c000400c030207440a030707810406420a16018000c15502507800305103030050109044070a0029001802411402c01e0091b800c181252241c9003030390990120000a00102c5040c401405090311135400705800600040064131b55400440026680ca041c44e0403000e19900012a451107942d07845140074184841210148280c0c1e00403003006210010314400505034851280d0a915070541074002c45500a031410b4030b10300c0e0a42c0008003220035040d0b030f120704a16400018002103210304a07200b80d9507002456903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242148830 1250 242147580 242147617
    0xe010203031006121803080a1a0907050a03091e02180408030c1303052a030616031d0a030c02010914130b010e0307030303060911120a0e19050610060302 67
    0x40b001c9030035150301c40c1001c2c4c02541d5007040040c2d03190403100003040b06100395680c000a1801c0c070041800c0d1500403c110441c00c150054491403955100800f03640020b09103030441c1c40e541c0c1240d00710050701c8110405485c2c600d00700a803400030801d044400e204a4005c1c1c8920000000c0d005c14013404840440f40941640c0081c8040390340c3d080d0b11001070486002c0440400401500c1e82c964500b0049502d1000c081049040103240040c0c600c18603031807410034114064030311440c003905684810003e540310780c02010365440006050319842500f400076500e0080848400c0080ba1502074881000c04805902140380108002601d0b40503034007104040c0406000e444540e202c001484014015008415050202c124400b6803552000c00c811801180280c0d80070400c20310f064070304000c0320458003120842e520100845000b4410300c0c800180c104166950009842c64420521410090034142d2101d000089a8030740082c45000210b0070301034000c400304007400c40d913200b0741a130407442090210028007403046c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 242150080 1250 242148830 242148839
    0xc0d06020306040c0c0c1e0b0a05030a0c0e09060114121512071d0703060b22050d03050906030c090a03030807120603020907110f0a0807140303010303120f1b0c02010e0102030310 78
    0x1f000c45a01014154030454180c0310324902e0382c290403402c80e9100044000c01041603400300c40c0612040d0320100c2c20040d07005a0410003181e007001c8014080e905004200d9030000505440a045545140300002c0c81310346d5040803049400203070720342005248140c21900c03149401300004140003048417595141d030b07040c82c45110307408040000003c14090600d60756040008e04805600c00500d00c40b0111b07802da082c11210813101c8109000e00e038000a000c0e1000880070320010341c0190031140e45075412145542c0f00d82d04c0c12612401407040904203a00718404c09000020980c001e00510b000b000192200c40c14864955a00400c903100303032101a40c00100359010a0900d80500a0500c420440130195080280303408800c916081d0105000c513015480046c0440510000c01c01d001e00b400c0b07100024500d50b524640f40140814118408414403030750383c04c5103880c04580e03540701d90980c48000481c5d60708950800000342546500540690100d41b884580d50030703540c4048100e074407950300c0180c142172888c00d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 242151330 1250 242150080 242150099
    0x110f04180c0b281404120c08160509041e0f11040902060405130b09010f06090b03070f0518150903060a0b01050307110109020303070501051009050702030d02030403020c0d06020306040c0c0c 83
    0x3d180c1c0100600030100d002d400d00c080301600034009030940d2881c1c4006082540381ca9004000c15912058050f0030422070314180c0c00c07200d000c410480d00c4c111420340f00c54940e820403a0524aa11003104200314044883c2e8040044c3c141c01c800304503015540002c1c403070400c0d0080c0420385100c100000c0d4480c80800c0140044c0c90201000f01c400307030300c80c540080c2e48203002d40410b210740401e8100c10780c8220040820881194010040700150015000360381c00c0d03061800000d45110300c441c0100c400d00501103070f0500c00005620500710703252401012510b0086526600a80e594004025075000340140360015559054601994245800c181d40e0b19146580c1c012084030388101620f0004655521a030b20040540d904101900420303008100001716800d0106003440742d40243d81c000c0b0344942c01c10081003441a000300940b51a4007204c0009a03036035031340e8501241000050341c0c1d8160700c0281145900180041d59015610419054500b08500522180181d40717240a00d0b0000f8101706681d0400c0c4840c403403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 242152580 1250 242151330 242151397
    0x30d050c070312050c161a120117121306090803031302010e0301020c10050f091516052809090b06072003060411090114030307110f04180c0b 62
    0x1c45142550400009488a40c03c14107071b20080389030301049260034000002c2030005401810b042e0340100345801482094050810070510401c0c1800c501c07504030008141c0c05001015010031081032107030780d0321707144402d10320100c50a02801d400501900d40c007051001c03000017224083c810b03020401030070140a5004640c90700480d0992a0155000d00c601004028108807820034113500d0f1002081c14070b0040c1c0402070452005183c6260703a44621660944200c24201d0150048a111801c00e0100c00c140c0090f02d05204514088188200e2140c50804a0b1004030224081d04810390700c00c100f460b5100101d2064882621509038030000421618000907010001c401007002c13070381890509284200300113800c0c030340d04071401d40c2e040d85112800f20301880c14100085c09803444210111030500b80002107a038901031910008c01002e80407440d502c60781d40f0500030b1401c0880040090010a400c02000940102d0b1000104c41d0315461140205400060b01c01f80d440c01121088114802080341c10b00101c2c003013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 242153830 1250 242152580 242152613
    0x170405031603020a1a010e040311070512060603120c030f130803070308090d0201090b040807030e0a08010212180c0613030204090b070215061c05071203030b030d050c0703 75
    0x1100304400c04040e4109410700071568029000303064190f0030380c2003c46030019140214070100300404d00621206821084698100e6018a020000343d04208102403506100b600903560050f90320744242c540c0c000c0000da1302d1040d00c0a130107039000c66550801032091030040313981010f26a00107000f4800c404500c2c1000d007000c0c044109c40003060695891695086600031a402e90010f260714040007030080c0708014200302440c2d01c0c8000c0044425a4544602200c0e001e00024030390000059170340c1c14144280d000b030381102d02c0100102d540b82e81d0b131204203000303610480c0f40c0c0510b00c8140c00040e403404d016140d01c11450750000c014064a108581c10410300d580800406290103001c1c11010015860b00d202d1000500d124200740b1a031414a0700c0c000c0d1034010030051034001c2c00c00640c10021300b44c0342c12045808284514860125002c2c45141083c180310711a080080c0d002c0f010345070041416415005110b4090040d4243c2c1c048480c0000308480310321a000c50a98654422a01000040c028581208546 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 242155080 1250 242153830 242153833
    0x6050904060c0e010e090c090a0e0106020d020715050304030e0613140a05010c020a03020909030c0d090608160e040e0c03101b020d080708070e18010e1005130b01020a140601080c0a06170405 83
    0x7a626107180148ad0380084e04035900580c000310200715160740421003d40540420081d5444001802100602922004000608005c100e80f101c501585482040d50345610b81c02024519664440c030b6101380c03a0001100c1144a0240040005055409115000070a580191003104102d0658090051a000c09030085400d440200312101e0110410f000595102c0070680d00c05420514025000340701d03100150003444031803008a000d18440b50841c541415a000640700401c80b1000444024244070fa400041d5416010310f4181c501d018410b0f610100014807841c4c1188882c0d00b81c810103c0c4e031115841d40e03540206030244041560b141c080d52805500448600c1c100c100c8413040740c04540e50303400007528018002d0701e078001030010400820859510500c00700c4801e224926190006240440d4000402c02c0c1990380c001880352070344280001c0b142640c00803003840000405903011795540d0000d04c50059903000c0d0003255103480c64149148802c6400ca96034048600180f0441c0300d07014440904112280d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 242156330 1250 242155080 242155099
    0xe0601050f19020d14182b030e04060b04080604060b061c050402040f020a0f08040f12050a11010203060f0103090c0504020f04091a060405040b0a080d030204061b1a0a06050904060c0e010e090c09 85
    0xe032034990105100354404d27640e00e4450101e0000340301c00d4683c1500155100081480184404440000d0283d80581c200b400825065148008100390b885110100000407910818698501801303030080d42c0510f1082d01c2c108075000504004000300e000300000007000a0907044290101c030311074110303550032074042c0103024111103c039584c64000000762a10034011a8002c100b2202c102c0e08203400c0c0f66940c00e407400951840c80e20300d0005802e005030225960615035900c0e5244140000c00c1d6102c806824098030441d52584051041c5103641c01a1064000050801000c14000701c408240034600320400341c03441d4140f504001c10000605810f120f00e60300003841810006014038200150072100c40140c5005035614140301000345901110b6280e45408090340c035000300092360301c600b190001111050b00c4402038540c00d0713a56025021360307849a0f038450110300c140300902429600141c510690381d128800c07501c850307000540740818031060841e404070a4000060002107a0740041c030b4280c00040c201c545 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 242157580 1250 242156330 242156389
    0x4d15040b060d051218180405030f0a1701030f120309080301030b04060b0d030519051204060e0a0f03032c070b0a020a0b1e060a0e0601050f19020d1418 66
    0x550b04003400760080032010801e9402c95003030440c1008103079841d1304840b03070441c50548c5403d561b9225007060700d108803000149100d100c0b44594007000d640780080408101550f50390810343c4045422000c09d603101c1078003101500c1322501030720070480c0d1181d000303031207504503841c54035806840007004005542e0f00c2d489440c0c140c155582e079070b15903660501c0390b01c1d00750729010400304840505001410072000d21504100040303c11021202c0700f9846540180c011643d50000080c060806240007001081d00880703108040806030107070019800301c0d1424081403400c00c14013100c0c90403a07560340800c19450b0400030303092049060740720040811882c1c600480e1512051940c2d00b07441c2413000c54a0300742c01c00070400b5180050068603d845d82002c000c039041500e2508151080c0b0b80c0040151441e818000c001808a010040f92015075000841d0030080c102c444288243c082e444802032546040081d6039034181408444001c016200c052510341e54084161803480709100440c036001e0004449130107003030b18400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 242158830 1250 242157580 242157613
    0x60405100804140a08090910170703050d09241407111003142d01030b0a050601030e03040b07060e060c07031b034d15040b060d05 57
    0x65004295450821910b46810240c3c80c00c2c0c0b50107451006a0411221070740404e401e18251211034408a0311031500b602c0d002001060780c001d90313121015030700f40720b90100e01d903901c04940d0404a03030081c0300303136141c04022030822285600280079840302c100411640310440a00074400401250760b9081c010104009080c062100e50400c032012144203c03091000c0d14a810001000c0044285a003800d20499a00488a001c03051008180004515210440e00078000c02402d0815503801050a80803903542c40382481c400710b0804030749038107040c0d0420300460550352082c0f040c002d0100744403014500f03080c104441c1c801030340c5c02880c0c10742c5d0150310b868107001080790920031749000d41560003280b5030b2000645000360111000031014081801c0e41e94040e00860b810040d02110f4072051010f80203059000301030500c20b181c1011a44002d0b00c01c0d00803988401c00480b4013442e0b100d041100700d803d5180288a2807400403030880b4010305c074990601c0807a40e01e0411601c18901e8902c90f10507551802c81c840800c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 242160080 1250 242158830 242158849
    0x20307090503060c1e0301030206190c0f0b04140c33040b0403051009120c080c0105040506011a0304050309120f010e01090201030605040b09010506090d0501060b190203180d02060405 80
    0x2c0f40d91300026407003980e008840d942032107040240344158115851500003955500803403a0030141c40c10f00c02c14810406210f0380f010310a240d07000f005040c5c0001c5604210001002c112821604654844d00d40440004002084000240d005001c02c3e0a00101420040d81d0b0403245403895154030f04003244960aa02c2a025001030400680724a4076146942000c51400803450500c04070645000010b502081901c825004020101d061003c100c1e60b01e843d00000070700c138500c0c842056510340820703c02001000f1501504031451103881c0200108030441e5501d581c401540c009290394401c100304482420940318a13440b40c4250020f4429149403095850700f9a040541105000d943d22030440d000c540c0c16102c0c03000a800c0039035003040349401e0308011800c507040c103000e0240314041c08180050b141d505c404980c524150302000a100f101c0c1d48003030565680d08440b070070048010781d4110a0078511310003c00d541d078680355494001d14022180c0140300c00c2e00c01100301a40c01c102c0400020030302d40c8075403030304 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 242161330 1250 242160080 242160091
    0x509090d050d0e240f01141c020d0b071e0503010909030905030a0c05040c030e060f0a0615020a050607030b0a060503100e01080d1206180b061306051305041b0302030709050306 77
    0x1110444c0c8140f0040424074100801c412958845c0d203005104d501090701d0002208074050310301001401d1401ba20a154074070f440402035002820351188410440c241c2c00b000d0042000c1d40b6904101c04401c40656079004403082a000003540910041044100d075800c0b6010080c020300300000826110404a404c3c20482c0d41c080c1c8140c0d24550040104c0d00300780c850030010034014503042104c0400301490f291904000b03422220820f442c100820301129555021000a0008003034082110340c14000294644202540681c0c141c0241d80000302c4a901038040c010a20000400007602c26050620a58903030b00701801c00e0605500d5048003041d860443c1400b9806440d556005040c1e0600e0910000d0001c030300d000704e41d85018100101000500242c03c1e2050003038039407a0300030940d0025a0082601e5004002b00f02c0e003903841c220400a50306401500a01009a007511415881b588070002d1206561520300320008210018101c3e2440c28447e038042d607006211032070310380340b400d90701c0303000070310301034080d9003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 242162580 1250 242161330 242161363
    0x1103010e0f0f0c3d12050606040b07120302070f140d18060c03030b0a260f0c010503060105120c0903070602070f0b090303040e0a150509090d050d0e 65
    0x400044007000b0011118601002e000030200380d114078000c900d0440d00106908406000200e18203030310442c0340c0340741070454181640c2004d0b800b20a84001e02c5100103480601820385440041039131070600e034040b182500c00c103078940c0389485596940c29440345902410302041607428400e050009901c0140c40b88498082d02e6003804038610f41300c00342d04041014041c2e9080c409894422008450103c0d162000c03200c10b402c15854001090400343c015100e181452680681c5001c03010914000114000340c10402d480420864001c651000a540d40041904030340b03d070344402440c500c3c40d84500000c41e80b01034181340c0b0700d041c00c0c04061200d445180039a00113030100c030080b9880b21725040c00c104000c01045244010900d19141c0303d41281035065034001c407400501d00281003000c54a003002200c0080c51150892106450a089404c00030600c08050b01400030114900150300d1825010b9103010b80c158074007402040140b41700558240d03000783e203c541201d03140c0000b03000c031840500c0036003c415024003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 242163830 1250 242162580 242162593
    0x402150403060b0f0f0306070e010e06071520030f102c0703150e0a020403080f041505090f13150b03041104060608072609030717090d020d1103010e 65
    0x400c120003007042084103405010818142c3c580b031b580010b141500f00701d40c1c0c24685603007100000101c030402c88001c90540c01c804002248801c102102c00745200c41034900408104003718443d268101c0041d5114107040b003207007800880c2030302d012100340582001c03106c1c641c0c00229955520708a01e201e004240002c50100a0a03540030b0540d880c000d0680c04071240c40e04011a500c4c0b0509290311a10310300504501c1d401e4200040d000f00d00c2c40d0f04850185030404051501e030780070007a045078140c0c0640100d070110b0343c0d101c4810203043c1c00755094800074480142640045003082041c025a86860300240006a45981c000101c494400105001a142c0c10150650b24a41418903c3c0b000300e12400070f0340941c1c9002c80400540e42d006900c01d030051158580360207880206150010780300102400c2400c400100010310491250020040044a10840104010000d09841c03c201806030300b07585600a1486941c100c01443d10b06010070180d44904503a0b60342505801c0070a08445009120504580c00302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 242165080 1250 242163830 242163851
    0x120606020609060c040503100f0b060301230402120105040b040f110919030503160302100501120203010e060c030a0209030a121106090106081b22020310050a0506040e040215040306 79
    0x2400741941c131184030701405140502d04000700b641c925400008000310303a503c2080c0005038a55410111458000a004680b256100c0c03d52103910716a40d0807081081c03c030072251008504050003030b10800c902c40c00039030380300d60710f00740c203020140c070390440d549500a54a602c418614490ba11501c4100c1983c0304030642c03503200d100140660075000307201240800d100000108006030002080f02c00e511103081000140119903c0c069240c50140d580b55081c00d81400004600011350310019084107008800030301c00503170781a0100e92150340980d813207c00351604000144400005400400c640b000190880310ba141260b100d110010301e14506c81030002e240e1124004c01920100300300d0303403c0b070001c0d002000018a04654075680388420452a010005d1b840d54404c1e80d81e45040c0d0441184004044182d00e0840980e03003800294022529144a400c814802103200d0824a00c4001520405005c80d440c2c1400e080c12108a807038000e000703d0b0700621b50341405142d401210050001103200340800324100303200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 242166330 1250 242165080 242165083
    0x20c12031804090203060705070311030406020a0b0a05040b1b120a020304050c150702010804060b0409240c1b14070311100302070f020f01030605060a0e10090501021b01120606020609 80
    0x800180d441642040c1d034a401585c2d002c00c080d038008040d81040c0356a080e85113002d80310424003401e5042c641c00082400a801b40d00411389442c028459519200341d5580c02241c10202c4400345c80c043e22101030b0030009038a41044503802c41c2006880c00c2c8050034005609000f8141540c111803c07040583c010091004200042141a088900854001c3d02c4100b000131140001e00074850040d040054040114041c821190312001c85000c0c040c10900002115003400e402c00400508011240d1103407803030003403440c1000e22a407540a500307079941c2d966003460500c008052400c0340b101580c6030003024840b421100c01c1005800d00440c4186042c1072403040c0702040000c403106c050014002d0500400c6081e000404141501010302c0d41195460610304861004900400c1d56070001500310b400001c00c00001500b1000d01549038808642c25051510030343c408a03040605441a80e005d80c1c002050500c0c9401c0641500110302d5061400d201021041791f1b454042d6034250f071143c400344e0403100034801c62000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 242167580 1250 242166330 242166367
    0x120d0306030b060111151312020303041b050102030d0e0304240f0e060a050a0915050d0b060406081306090b180d08100b13051504080724030b01020c1203 67
    0x100742000078560078176020381074694011429109507020541c001440c0100074410050300e69030407451048860701c6040c000396482d80b054038103585414a000030301c00000c1c0807042c04800d03904103a01031420407c0703445891000e401203a03603403041070200340804150249071a03544020b08610000082514141d40c6025003608c480f20880720800074003002a400b1078540b85c0072242440114a0705c0c0e95038400078142100c20210b01d0b00001607046260441e16502a0300c03401a040301c6480d22800c010a101b01b5003000340da03100718030580002c0b441c200c000030901d082c07821030070b01120701801c800304440300207944811141a0858009030380f420605590301c1c802c1800c210309080414503007882d104030700b4968518a007002e84d510400c1047d803c00601214046556042c00008140c00391105200720500085041c46070014001d108251007446070004030800441894200c0f84c0d41c0001c50061502014001c0700500b00801c1900d0540c40760022051554840c04000342000202e0f801071900e5100840180b0344012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 242168830 1250 242167580 242167591
    0xf090607320c060306041e050603070506070507050d02030a0f08070b01212a14090c03010f12020f1f08060a0303050d05060307030206040b03060102010b04060b0a0e120d0306030b 78
    0x1000000701c0c00401c50025040b101c1c440112442900c0340e96240004000d00071101b51901d9049003003a03001d602009980100c0d005810031000da07107d072510340c1d041c040c05004100016000f175200013000c00060802c1d511001040340041d05643c80c002e10f940300c1c511481644241200c004500007620800c0c01044e4040b02e000d0a44403c0e00402d14400360311880042c660036030701900d1f006038030703103844480800210707440328016000c0702d101d1000781d8a00003840d000141c0c44e6418000c1c18541c0000301122580c40c226416605081048407845003024400b50703c031a4075000c220303041403501c41c0503030301e07940c0e0b40c03850101510b4110520300342c100c80c0090040107042d014285602807900c2e135406000080c0c0210542d40b400d80603141c0019a0b9a42c400080e1500d1000e91029410060003e40411403003d2040110b100351001c0c0c0003070000344400c0302030008582c95803040e15061442030144002d40fa21071130286544000007004050402546861070742801d1940c1011004650746a0041040128800e1b1456010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 242170080 1250 242168830 242168903
    0x30506060414090607080a0e0f0c04050702060f04140709020d020c011409150a0b09040308040c080703020a03031809050907061d031c090b030a0f18080405060f090607 73
    0x28280106107640d41d02d000317030000d824041d429002450419003540305020140000d412502d00c4655252038a0311091141c0502d4000c4d400d20000581c40350002420030b00803070340481007040a98032030300c0784608014070360459074460240e800000340250350740c00500f00c1c11805440050b81e418640700f0302400c54000502d0340b040500180100824007002103011070742e445c03501c0b14005047e5103c1103510000e15030030b004070740c0c006080e40c00c0c08285540300401620a42c41004a0b014030713a00d0300e03201d0342d848000c2d2100a5104c1d004010610000341704000c4d5444268000b0300766003c072030700c0305a960b003950400c80384200c1592080300104420b0f90700c181c9015092280b00030f49135003c50a500420340750319002c11840100d03001c0f0030b50040494858201c407401040701c2c4041da916410200f0302000507040c3c6009038080c1d181803a500481c00b483d00003042e000c00b940441d296181601d0a41800700d150031401e640c660003031040c4101a507a80f0780c1c100400e503081c4144100020720741e80590b65600c5960001503540d06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 242171330 1250 242170080 242170121
    0x615060509040f0b09012114030714070b09040c0e030609010e01060e0f010902090a090f02030105012604150e01020d0c14040807120f0501140103020109060c0803060d0f08040305060604 81
    0x6480e0745218a040d1f8008101d440c41c0f007130802d1803010602d0403404004081004101008200c013101201900d000b030b20410f404024486e030bc00c00940d032000c240c02102c1d81c104041000151514080c1c2c8202c520280d542402618040d05400182c20400208d801e8003559450344840c8034130038000c0c0325031300240c110f0f801c400c030b11400c3c4803245101084050141c0319030590300203613080195076208800001400b450400b40075100401c611140030750420300c600e5021030500480740e0000c1c03400d10540450000d0305074180d600760317503181c0751442110000381c015448c00e59202610105518280002e01030b08104031400706480002200080c2021010100014004001c1c4018025134101103519811074a14284142c441101800c100c0040925507800500c20f40c07820303040d100b0781c0d240c800c1304038101d80c002d0700e030400b149503100382c16107824001c560700500c501d4007000002c03400d20700b01c102c2c50b03803290050744243c40502150380c54604a44c010340082e1800d6000f4002c00c05503103400e005404004aa10203038501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 242172580 1250 242171330 242171351
    0x10e031e01050117070524030c070c0905041a040204060b0c0f12030108100903050d0504110112020a050703080c0903010908030906130c09091401051003021e0117040615060509040f 79
    0x102d4107281e02a051140740801f48440c008640601381c5c001c581c0c0c05501c059500d0611404104403503010320380444003c41c24510004030240b262113503a2055812484100402c0c00e00301d002c480c5201e00401c02c07170307009039144404681200400050600c045000004000790f100c0f090b0001d1070301681c03140c1c207440b03004204011f0011000c04039820541c003104032000b00f04101c162505032001c3c05642944200c4a10b080c04020030300200c1c43e00c114240304c080c1c9030590503e03072440307815060780708450811011980400048002070300c03406085900141c06000740307040c000d013400000e0940740c140406507031000003c024004e84441c107002844c1c104024600364020032205036a42468803005104181070343e591140b8840c01d029a95004400e15078180300208050b14080545480c606054082a8081c5551200ca4140704110382403089513100140c5884613042e15a24120415841c001e0080750348980325203d8a04035a0b20500000140c245500d50940324400807040c0303c00c85890b000499407813800e041d00d011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 242173830 1250 242172580 242172583
    0xd05100f1b1b03020c0603070f030f0515060906040b160215030403020d0e0102030706060801060602150402130902030a120801030b0705120612010e120a140a02030315010e031e01050117 81
    0x8940e10340c1c2a482d02080040c5050690074603801400a030b420050001c200403a981d072113050300714964615102001103031440c82c0303040c0440e64116000e5511541042402509251520183c00074610040c4250b00d09501e821003201e1503000003048228403040f81c2108011842c1400c06146100314030003446080d4070f410f8500a65600121a4032014403030070b07084600c2d03141d10074003c44641e01d0704074205122142c0d03502000e0317000b0a01c5124110050081101c007041c9100180412801940c0050070810700a65104d90040148031105040ba8148a044694000a0501d16803001c0c0c213821a101c0440d41c2d031540c18a1011000004e01d41010841e04211f0340c520b8001c0940655000b44094408204056821404e43e0050603140e0010180d4030483d10003441d400880c100400704108070756500c1040d0380054054003168020003001e04050b0300203000013590301c0400b40321038110010500d03040b1200344540000c6403d281881420000b40580300000b8451700c4002d025a0380100609400115003480d00c42409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 242175080 1250 242173830 242173847
    0x2030405120c0c01031503140615041112072606010e01030506011205060a0b1b01060b0705060f060105190807110613022e020d0e04051b090d05100f1b 66
    0x120705055031b0300410030b100c00c6010390710f8014503071089000211104040c24a5078460003101c0300d000e0112031141c12142130a050141007018485200b1040c18101d02c29046100d002c0010b000a0400c4a846501c42500c20920040005248585000b100d581040f900040c540119041c1070390505041000b030185503603020800000c203e1850400244540310701000804540d59544682c0890f1400b103550070004581c11030000d03481c6c103904020002159034104200e4036000d4418080c100c0d030005c0001030306607407140e42c0c2d01e9841181450994544160314820640c1046800045000242c0a004105c00c040d0402c3d80c100c0b41640b440300a002c02d1402c0720022511282081000b4050000168150161b01d0055404841c1178200c0009205010b0103c40c001c0d62690100e2074580041c80c099118000742c20039210f6030340240904000307a0310010b103d2100342c641c0c0c2d0002002541014403002c0e01c2000c61014090f1006281c04c07030002040c0d43e0b16800044c4140e422890903070552800240c88054000d03000300741c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 242176330 1250 242175080 242175103
    0x50a0509040f030e031e0606030d021c02030906040e1509060a1203050d09030c1704030507090c120c0914150405091906031505010e1504110c010f02030405120c 70
    0x1407502c5840245002c0701c50030410100720707425218030b1040901081c000000030f0201100342c811589983d40e00300400d50344203161508200942c01112a04c0a51402060340080440d0b09004030fa1510b107182011640950050740b11078203520704001401403402d06c07030014a800e070708101c4803035000b070038171134001000402280701d00415007641004103010140514282c0f0145200074200304400c040f10708000d8110214a18100c40581c00300e10701c0f00d00a10714001ba00c1c1a60781120040c01e0b03490610050000400c4000d403014240b0043c4001d5854007101c0380225541149039580c0c18a0091803d50001900041c05245500c00d0003100c440c4d0421510356815102150802c0700c81c1c0c2502d440300e0303080750400d00002c506504250b0405802005100c21f00d0b803442c10b0011807080c10460b60b0f82ea4030f40c0002c0b00b8000d903a613990740c40ea00740c441421442c20f5044040808544011949080400c0d0175036401c550081000e503c41640110412080c040203100c0c581441c5020650329282403da4041e180e01c40c0220000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 242177580 1250 242176330 242176343
    0x7030203090c220212060a0e0c09010f090e090d080903040308030412090e090102030103170403030c110102010f1401090e0606060703031e0903031406010905100305041406011d01050a050904 83
    0x110fa941071850186211030624080c4804c654814101061007000748086075003d0154a070110006813807400c002c0c00700d2040010030f051030b0505040f0340044540c031076007040d00010045400804900407007075100c40c1e130213810b6200c02000c0e03001c201c24020b0061600280290341d03940040c44200f02107038000003103a038015403200060f03282448e03503941510161500d030811911081b00344100040140d05600550681e03009030341c0405174040201e44400f10707204900005000940c01400900000c901c500001030640c814000880c2d40746000d80000211031080e00d00070740c2d94a48400401010394107100302181c055011016050503c0c009021524520507094010105640c503c3c07044103807040c0e90418010404060300a01c010404d500f0014081c100c001d00d00c480d030510000c0070820660283d03400d24206c91001e03008201d003c1030480140e00420000f04180c809940c2c3d01d9004000040c24440540680b580c003106400c8903c00704595051844141c10550017034507001000e01481d610803212942c440c2e40081c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 242178830 1250 242177580 242177599
    0xf010501180b1b12031e01050a0e15060d09030801080307050c010f05070f0606060e0a15030903030e0604080415090509061c0512040510080408030612210a0807030203090c 75
    0x1c00d01c0d200c000d400b4004442d50060513031086005020000444c040e00e4000d0fa08076044440000e500021403003031094652103000814200b22502c01907039156408454028105800b48940010503000c0e4888a455401c0559584400701050b4110503000c0c0501000c01c0158102505039584640c7c03030403010500750600408490206006200300100d0322416807104a0804450b645e01c0e0402c058019030143c0008505030180700300042c1000844041244c0c81d01d81c1e5901c105240c00c40980c000c02c1d110f8816401c140d1500c05400c2a0402006040e000300e11a80d2441c1c0e4403860000d503140000000d41d4030344100800c9035010442c130b03507a0010503074000c01c04480d00711540c880192440c1246400e0710004107107000303620310702010300d01c0b41001c1d100315101507e001030240010b20341101c24580446000307202510a102281e0581850b06c11015000041c4045400316820241c1407480700114056207840030000003440551703260300c414060340118090400350b05504054003543e8644441d010741502031031780103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242180080 1250 242178830 242178847
    0xb0312092b050304060513090c0207090203071b0b06150a0c081308061305010c020a02030709090204020405031912170604090501021605010e0609150f0a060512060f010501180b 77
    0x201c48410540c0c07240c12250703156503807500900f41d50052001140000a0200005255034981c010106003250581c06490f1482c10909480004d40015200c002003011900075544000c0e00c3c1440088a540a100c01100c149001410400101126591203401b1401484040c80658014842c6c000266000ca40c860311883e0801000b010f80300194811041d138442e0000340300749650036401000846000750024400b2107803551060b61350301c00245000b90158040301d0100964001944003c003281d00c000c0c40980780030f50302c0300000d00e801c103000c06c00402014205402010421111b2110510804508000c1c0351040d00c00340c01200c4079801001180159162070752042002003c0d81229031481c40a100025526220708110b40202955450483c0038414440814001400000c0d04108801004080403c6994a41c1c1140b41102c002c1d18400c452601c801d404106507071800c0081e501e8068400c010244c40c54503841c07244035003d06a004074103200c0d51804414138001440030501c107946036540c900e0759804c40d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242181330 1250 242180080 242180149
    0xf0307030b040c1e0807140904020c07080610081203070f020f0d020a06061a070305070c1d060906040504110d0c0b0408030a0f020105061806060d0f0b031209 69
    0x5450520350180c07414a03103c0c80e19070071030755a0391900d4440000410800300c04800782c0d134001e025101d01c0b000c103142d034010f280d506c07030841c005002e1f000d4098009400c0035005010949895442e0300207049903085001001030111003110820001e0954100400d028140f8070b42920651201034200c8040200300310061820500800604e100b4200c002c00304e96003204845402500e8140710407007201d0450070000001044000c10f100450042c160660541c074000196805540503400f9410440da04030b000d0307000040150101c0d120303458032aa001c500c1105841e08204110380d0000c0100042d100f94a00b00c203000c0803c0c0180d0f5040301d006404d8030810804080c50a00201e20200355000d4407aa500002e80454201404800781c0034207480d648480306451071544080e070a841301101c615811a1440d018001c86541070403e0742d80200001d0242c81c03038909800c04040a58001c04006000d041e211109190a801c040103d40503040d03c060b02c5030f090100c9480003a0740c15000428042c54003a1513900c21903603405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242182580 1250 242181330 242181341
    0x1506080c040e04021318050d030b03010501140919050a020405040e0a0302070317090904140105100308030604050c0417010e07050a0338070309020a331808010e0d090302060f030703 79
    0x4030201b050301c4034946160299403480e28002400000342400100c0205003414080d450590b005042401001d8850340180410444010201d4a060107071005840030398006204550103403159040141c0e40342c0c20113050005580d04550013910b2a0b002902c1030010980c0451881d042d0303170340710030784540d1030801c1c62112500380900c42403d540b1507404001c0c8000c04c1106038001c1c9032031070f888009214942d5a0a880600059144800fa01400c020000110300386030a41c40543d100d042048840c1c1000e403135000300d403030103441c01090707503102c0e99103075076241c101b15040141000030601121859401811070b079800502e131070f44d09800c80301c0500305907007110184131076034416240140d00300e01001240703400c1d00300030050210b004090340078111104001c5900d01c6080e009004440c452065196000044001202c441c201201690204900c2912040400c96202540c00091000b80004103500482c2c880141c00c043d0f0050188080c4078a42d001040143c4491041d2025090568561a1241e456a40907405082d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242183830 1250 242182580 242182601
    0x507050f0d0b04110c03040b071b0b07060e0c13020d06030b040b1e060d0b04020d150e0c030d021203070509042c1f0c020307061506080c040e040213 65
    0x80c00803695019003022544805041102283d0900180407119074544184c400e2009180a58104102c02e02c400c1410340000c006451068203585060700c4854007094031130f07091390091104450001004014010240a402005d08408020b44501004000020710380581c43e040c00c01c410784c0102d412480903055600c0100110342101c1c3c005101d02e002c0c94150b03203211044420340800360545414031500f00d002f1020502c1010003804082c00b9181c5038540707010000c801041240d000404100c840d0024182c268020012405024082035201400030420700f40940710b030000340240c0c08102e000800542c0040c003c00c49591b100800751f81d07900c13800411940e51080c03082807074000707080070400c0c3c0031260021940d003c510219182034400c40080004517031200e40d524000110b1900c0070b45044100c540755841007a6644403401101e00e0030740d181e40c84100b985c0c902c188035031140741048400c0001503005040b40da480031005446a00e0682400820408868083c001a0140c540c20748041503160040c2e014401c1d02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242185080 1250 242183830 242183857
    0xe1503031201300506270d0210140f0406230c070204060b030f160c0501090506040201020d0f0210150b07061a011d040c05120f010305061810050705 65
    0xe43e15107103007000c0010940d40300f6490401d81080c240745214a040504a1241c2c404d003e0b115a481d844001c0c090740c58402d1016840403a180c00c00c240240042110300e0608556801401340c017000e0074162004c4602d081d4034011800400010803031502480405035500c20352082c40000c006454403610307207040c0c10040d0088141132140c000d02c6012004a805800036130320881c0d00713102d01c54460b032094445001c00c1d00c0c0c7c1c0300404105e80200307800e190f1120b0402420701e480d2074100040c50050703c8803400c1d615125000d070751581010080c03006550b414044905c0c10002400c18401c0f10040f09002503907440b0b10403140400c0e6550f21903043c0341070500d005450041000d020040c0d100c41c0c041c1040b2004040036014914941d440d020102040c6d40686960140c0c6444084910807018018081c0009405807100c3e20301081130030012a8101103851500c030b4050070f100da101e9086581945801460164007401c2040303403113004603c007201240c4c009004c0850840e4100041510744400c0003d44144c01002c5039100d41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242186330 1250 242185080 242185117
    0x4230f1509010b092b03120e03040e010801050112082502121e070803090f0a0e040b010602070b180f0a1505131205070b0a050f030103030809060a05010e150303 70
    0x602c000f8a0140540581c221a4441c81c3e0706002e5071410500a41d543c80385050300c05940ea0404a40202c200040b80f0700e0401e0301291501000051a04590080e085010107221000060040c0030092044070702401070428070202341c00003030316400004d00a50b000d94114011500c0c40601400301c074950003142a50140c051490610104d02107a1984c051a40d020013903c542403032440040310010741c200c102d656190245240c10620390a000c05611300c030050303a8000280b0b91001804030461180030344100d0040100440795410701c000281080860341c483c0110903814455081d4485d0401c040d030074020021941505510422408943c408680340e0011040310400a6620104e50f0880c0c0181100218203044a03001d13519030740340100c45a401600500b455001640601103010990700410f2000740703504203030707052049040d10881e090348242c000700c00142c0381200740300c1ca0010801026800465a0b10240322660502000389060300d001000500f185004424602c8640c07401d10407600d0758030408540399031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242187580 1250 242186330 242186339
    0xc03090a060f11011104061808030721020a150903120504150605031606050c070314010903090504090b07030b01180312080106020706092c040f0204230f150901 70
    0x81004100292408036203003030010143c510040c4a0840c107070f01081202420242451001ca4014003071154501d04961000408a403e20342040500030300d500c10010400e030400f0744030300c452001c0041070b10f100941d40140e000c00001045030042000425125100003003244041c181114096021450158100e1a00041c081070140c14856401c1550224800f400300c41d80c2d400c1495940e132800312594102d050702210511515224a00410451217a01d08072410760b40c82c3d480d4880307100b482010072030780c5a660385000400c040c1c101c1038000c01010111001c1200c60100d44640e041d82900a080000b01661242480240ea00400c43e1400c0c0c0303a0700da0b000030300c4c180e2645890719071180110300c9403010030300850000400b6840001c3c0c62040c0d842d00d6403a02d054078030704000208d240640e61a0400c000d4204100411034440300903110b03208601540b00b40c1011003040c018003040b1041a121900c2c0d18006012070000d003164895020b81003d090710b0b0340c1000f030b40c42850003c514004140b034070b41d121100c0e000001c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242188830 1250 242187580 242187587
    0x50904020d0f1a03100902030a05060a0f0f02090619091706040605091f090c180f0b01050405010905061c09030c060c08040f0803060a0306240f050102070b0c03090a06 73
    0x1407090351032002080401c20845141058183c00000541d059022001c1c0081d80721040d04030813480c3d807002d01100c0f01d80f05603580d100d041502c21078584000300c2d1366600385144e400d003c0c010b400e0400680102103103003100c4000421003a20684400e4180d40b4440348440160ba4070441c0d112004001c10300c10603000880350081d9580321801501c2c00ea4806007410003040c2d401c0d00c003223a1180c81c2001564142c00358584152000050469080203a03441c4110f043d00280003c46441801c0c9038010700f11001543d00d5000c0c0000b4100c07450580c0003410450f05110030f2080c0d9030410740070b034241c4d60100c0e0b4080e2124401e400044e84010400804001c1c0390514501004140d004a40d035405032b482000e040c400c05050800403103020070201d501415a006401102c070204028400a503001030000e01190100c1e80c50307880311001d66035003014241e21404821003030a54804000c009030060010741180d540d0780e515200000350703194001d0103125040e00e00000d840a40403030070000c0f501110b03005010404002e540c0c00c0c024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242190080 1250 242188830 242188841
    0x10b070201031103010e0612010b0301021201030b0f04121b060e01020702090703180b090c09090618030304080d0509161206111e030603010608070b070311060907090903050904020d 79
    0x481c046420461010040512101681c0c1603170030011000f03155071f417440c1c1000300c41d84110340184030555075001040c04645087c00140301030709036418080c0035945107240c20010503200401910b504404001800001200701d00d102980a44503e0000142914104e800c68440c40500005011f1482d182c0c035503000f202c0c190041c000c0e00d030003120b412502eaa6500000e4080d102c24000b1642c3c284d0010400400040c103030341c841c0d9040322021040310f2140301c10901141d83d400f002e8614807581e5010394108103156030b10040c5040001c1e1554080c5080d030500f5a55001d1901980c5401102c180c0c4407000a90600c104000000c4210711a41009825036a254101c1e9111030408005484d61800c1c02c126401e00003030304040312454001c107520365405448000b84080d0981001c0c050360b516548a0f680010031580030082e0401a150007400389a44a011f890007034492805000849001e0304603204100b503400e03000c2500381c119a045034010440300300070700e011189480340e01d4500c1d602900c003052804018540380e108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242191330 1250 242190080 242190083
    0x402090a080a1a01080d0207030618061d0105061509270f0901060603020f0703031a0d0302070e07020706020a03050903120408011a0f0d02011101020705070b2d0702060304031106010b07 81
    0x10b95143c1d0341ca4440c2d1640700c6a2498540c0f0159002007001c20018006030f00c2140b0151a5040e150070840b010344d9098103403800e121a140300e40c000c070405045260000e1003201e41002c000c482500c11031020491580845c05000403144c400c8042500400c5007042016400d07215642d004242040361600c0c10070340c44100010b0307901250300d42c0707041c90100381c0b00d00900c2285d010001031040f42c2e0821402e940e00700c01130540403007803244645804400f01050749a400c15851001d200b5006031203040d0a0201c070880d000d000502c04000c551016004120458002c0341c0400425003502d0081d5584d14182c01180c50004a081840000c140008000135056410760040640b402460140c0a002c178410040000d00c8003128034240e4815104102c6600542c0650380c1400c1c140241c5c40050305090180d01c400d418009994044020341c0c100003140e0419442170b4040180f8500f50001c203540c1401da2610007841c500480358000d01440c80040450141405a100c188880355014200c821660712882c050030700e500324800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242192580 1250 242191330 242191373
    0x303020714090a0b0127140a0302060708032e05090a05010e0105060714031206011e0503150f2107080304050303030a150b03070504030209090c030a020402090a080a 72
    0x10041006101c8008501908500605961003511160900c0c40148035120156060040422000c00c1c00c94281c2c0c111440c0022101d8000f4001e490003065131400080070740c52174440c2c98012070038001642c17030130203980002c0e4210711007030707140d680c2c5611000c84a512104054010807800b003007980d0a0004a0800c4140e9405403042040d0782c495101500540e8000e000b40c0d0300d80300030b41d40103201d5410030002400c0000e0040507440c0e046641e24240f18155486038031000720002c1807100b0081c40e940c10480429a04034500016009d5904a91000301140406040350b60b40b030400c4800d0307201c0c1e07075641230180d10510001444201102c210050784120f450380c01103402d600707000d2940000b51182000c0700351012110050065491a0358403007040c40204503c4c6030080702ca222050010580d194240040c520803051350300e84a540e1390841c0100110301800a020344025031080c0c21062030740d18082402c019a56060b5000340e01c032901400001d00c4240340381c110054a01c0f4010010007840a0100c9203101d0901082 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242193830 1250 242192580 242192593
    0xe01030309050f0f010f02030409110405040e0f06060108040f1b080f190213060308040909022d041109030d02010212060307030302120f040e0a0e0705030304060c06180501090507030302 81
    0x1840840c080c0e00c2000c9900603800c04c1d820040e03500030000e4001409903032054a29068440c9501411aa001c0030911140740010505000d541058481c4041c0141464001c115202c4503261041c0d0313495000b0105410403242c80046010016100415a189030340811280303140040b402001c041c500c850310442c10303e44914140400038510104510035008804441a041184079400340403090112083c04d4194541e603540003c0810310890246c0080c040410000c51610224010410705412800d40415017813000d41d00030300710103180003200201c46010758000c690004201d4415046008000e101c43e054011040e030401c101c0c0d1b041d03000740f0480d40d13584104180d03500d860040c1962002d40340002001b41c0d2103080d90802044440b8040c01d816080c0066040c92301380c440a00701940c88042e2a084511500da51588170002c0c41071200a002e81000d40c011405c00d481c0c018010300668446402030181662454462170b9000a034510140c2213411100174000c500d10f51901d2070f078601c07031840107800501541 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242195080 1250 242193830 242193839
    0x307050d09081b033301090218010309030201090c1d090601080322090903091d090607030c14030106271a0a0e3102030907031106070b010e01030309 65
    0x4281d20030980780b60800400c021211603800036561241c002c0303440d034581700350300d81c6081c104281c0c86440c2c2061071385080f41000c00040c0390f6600c001d91068010f15480c40c01401003511200404070500b000140900e4045101d000c1410141d005080e51100070b460400902401300e0340d21a0722210110004805140541d00e90340c0007151030700e1b0341c006c0c01801c2d89600b081003080305080f101040068800801c44403946c60340d9440324510300300c81e50b440b400c0b000310780c0350b10f0204502222080e0a646004040c940341003946880981d040c3c8a070070007407030b6405041c1da4000700b4146038810610003503200b0002001c25600d58603100042c007001c2c05c0100c03a0300b00d4000011110310840b6018003000440d002c00340c0c0f2111240b02d08250b0429600030383c458400b081420840f5000a58890040c81e899017880c0003c00c5212100111160000ca010f80b41c40264600410070320000e20780c00280762081f0703034000312094055000080010b000388110880070380540d4001c0000304840b15030801c52070403248aa124050940c0d940c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242196330 1250 242195080 242195087
    0x5010e07090f14090705160506010e09010b0121020c0105010b03060a0b3a02070b06120a020904080705011404060e0c0d0f060c090503010c02060a11120712021b0307050d 74
    0x500500003800c181d044003c010b03060450700550808072505015061070408440d081020140c448259015808403004000d0030014500300380d0030a041e4030081c42900b034000c0000c3c06c030b0700030001003400140030000264203d02080d4113803506c0002c0c0d0002444030307594495603008260010381e038440c0700b110403940008000303101404480d01d1101d0000380d4812041d1100881c0d040b5140c9a0380c3c51412004500191000d14140c402440014071a0595061908082c2e0500100380c201a4269655a00c141d950501507a10b0000721340d40180d01098090341c601d0f444c980f035409040d001c40385500603407902c01230104200c1641c00c80c0c105c1c4400e2a00310f034225401c9804009441941d40005481510720840400100c0c010360000d9000310041d00380460303800e0ba110f010070300f1280841011401a0000c07414071044050900a5020399680b9124060a1001d404203801b6601c4005d0702c02024003051a241082c604290b4041d030b6079081e900c04c40003c80c205000c1100f900c95100070000c807001d01031400c054594500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242197580 1250 242196330 242196359
    0x150a090309150c08040b030a060509010f0e0603070503010e0706080c132d060309111509060c070302030706030f0c030c050d1a040e030a140c15130605010e0709 70
    0x40640d1070880c41890803860108004444140d64200103003103900601045000009000034200002c2d410755900d08091071004459140c0c004034440c0300030f000100560360642619406940c0d219245a019031074510010f0b14020140e40500d807d0b50034828041c40100002c282842216100d8035074003001e960741e081e188d0300e52181000a06580701d210700280310031250080c401c8511107207408080010010740004c0c3e140641e49500c072000194403602e47e0010420300c4203401d01440701c191003010103071400034450440b5010f000d007428002c480c0425200c000280030461200156000b50680d602243c035240000c0241285240b2807100e00d04040301c80c07030180c0c8244201c190b48007096881e42d0400c202da180b01e1010742481001061b02c0044014040425941c81c422010615441c034000c594031210301c0005080f40c0503420803c4002c600c144228801c103400400e00b6400310b07036052030079442c5a441011708180c41c9005d003001380000e8174050012444075103a102290040082e915494400c81d0744490145030f01a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242198830 1250 242197580 242197583
    0x9070302090315250201150f06110111030a050907090207050a0201030b0108060f130b04060923150907050408030a020706112e0e030c0106090f2705030f0a02150a09 72
    0x500c00c1a9000c202c0300210f04c00c81d0782100c40c40041039403421032441403e81c41998000d00c02049850204000c003a40010101043c00320b990024029511960308048440c0030080007861650784070700024002000c2408039001400c00c801c000c40d154030309400e142c2d0f03480201310400c0b0701091070f0003226a5070358020407080784116030007880280034146070800c0c814005040541280000c0c1c0700e01904c81c95a88038090f110151000d03000c0095594a0740800070440f4040b1941070944c040b09a06200e104201400070840e07010065072040c0441d1035000086030036104a40c4245400d00000c07400c11609540410301008490040d51003001c004020103203031f921024101c06420038400d000d0035014a112012000244928034200e0005450800300412400e56014406583c466556400e080c4070030515031050200c20800e091040001800d640804811454000040340e00300142039811003c100e800c20450b030100e800680c90540316140300c44060358400f81a40e00e4060046004001030426540d40b180f00c0280303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242200080 1250 242198830 242198851
    0x18060405130c0314090c0d0602091806030106060906080403110703060903051209060c07060905011803020312010915090f09020a0b1b0d021c020a0203010911011d0102100c090509070302090315 84
    0x71170386031b0810140c80e503140d104444840e001d000c81c5a07156228581388081c544c1d495040c01651070078204042c21240d02c0d41205d000e00280c00e00902076150301503503003540300c0d5040c1443e0400a50f5018170318a0290b55a00041c411070a080a2030300701503006e4040c0003142400c9191000d10b4580112017500c41c8012181580c0d000b50500c0303800c0100750680c02c10300140d401000001280b012140d0880c1c501e211040f8180c0159100155084a0301141c0300e8a40c010b0400d2903040003c0c1305850101402505203100b4504255118000c180c1c650340554055a40f50394001c2510340c02640d82c00e01a20030b0f030000700b80461504140140e5400c0100041003e021403026580039041072142c01c0c4445800c0e8403001060021481801d00c280c005031024850445034a008035041c44030b6030141e00006001c5000c601c4d116568041c594615500799030000f61240603031101c1c1c0c07800310780d4440c80002107482000a500c41c0782d0150721042840b1000e40c25500516407098141d0a89a4017a04444a0f0500700d00c02d0340c0c00e01a8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242201330 1250 242200080 242200093
    0x3060b040e1b04060803160b07140a051c051906080c130e2415031609020912120903280809010c050d090e0a1118060405130c031409 58
    0x101c9041101c0e02c1016801000024916101c000322840c1d40c2001d0111081070400702d003000140021030100f0f40c4d019441e480c1c414200f06c03041c9018080c9001d540130b014144000070820031004e001003005111401043c4034200401d00d0003846248610a100140300031581c41c3c0341000c9070390a0f011400390320500014112880e0f6002e0104004001c280e00907000c04176000d1b00d402050f000541d426202001038403c4984140f0341804480141070140c0c40e0480c604c01e9105580e11703048048080c101500f2984070540040c1c64982000110b4040410321540b124240220700002040d07071990300103451031040070341c00c8680110102c021024001c142c0171091864000ca41038000000b011140104910710040c908200fa040c1203a40381c40c45d1012a0058401091a01405000e40812900f0855020304200001d000d00700c94600d15004c0e0b8491060b5801000709001c030f09480700c0d02c50380104c4000b0900900115240311500b400c3c036004103c01340941b00040c0c00d2201251100052112446c040c0342000b025110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242202580 1250 242201330 242201353
    0x50f0418090203030307091a0403241d030715091e030e0d0b0a0e010b28240305070903020105030f040c05060c010209030c0a0e0606030901020d050106030603060b040e 73
    0x5051480201900e9403140500001a2030a00c051406100203490750901542402c03a082159200b058044c5992001480208003140d850098101a8003942c22045480d102a401d1400642102c003007100c5030380200300a0300e519900c000300601d035803406203c0c8045c210309102164070503515101405042180b000c245009e907140101c003031010181c07280c1820010740b440140441d91000d10010142c42401035502000400c0d09180648810310201800801441c00b1030f1000908940040003409035612066043e889090304503e803071409400e00b05010401049140500c84050b0110780082d4002030401000c038486070b000d00717100401d42c2da0584443e030451381d40520b40d0a074820b0007030050b2080c8403040c10005a0342c840d00000c00c001d50421001580d528078901c2031519010250074150b0082c180100204450900345401070b41100c0b0445540380d0341d03110130f800d09019010768281c2c088403074a4500000780242d01607015030101c03480b0301d405201148180742000308440100c2c2c3e8a001c20f400485100c1c1c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242203830 1250 242202580 242202599
    0x906010b0a2001050a0b03100507050d020c03090d05010506030f0a0c0603020a1e0806010215040503040b0a111005042102060601110123181902060703030920010f050f04 74
    0x385101034201072282c40700030041c003840c01c0d50b000755131150034541c0e5200f43d0802070400707110600c88800511000d1181c7c9c10701c160020601d11076000c1c404240c95002c2000d00400310300b802140c14184000300700c001d00020900703141b4001c3c60280c034003d12901c202c818000c030710000403c0c1e8003002c50f00810851406494034409401a611030110481000080c0f480c084628108040358001240c0a80c0da0340003c1c034004002a2500d4084003044a08121503002c01002580000072a01a20080304200392a490415002e5555a1416104280e107000d500b20302103103c0c0c965440548154010079451124641055441d076045403502d008000581240001a0040d402505128a5590a0000000c41c2c2c002d100a640b181d94044600704084084002031180c0e1210040c070030746d0841d007110058141c403101003551982c0700c0100103000340600004503408041c1400b075409034900c2078206041c000300340f6540c100249400702603d48140417441a10690500600c184160760f07280900c8483c661400d4109000c04 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242205080 1250 242203830 242203847
    0xd0b040f0c0e13062414061201030b0402030d03020a0c0f03021f0b090c190e011b0302031b06061e190807090f0212040f06060911070201080906010b0a 66
    0x155001e80d25848001014a00c9103102c40c450034005020486200c014500030303040c0e44001a96014020144a0040301030001c8041c4c40125019080e075800030041400228000d4001c40724516601150340d8000414490400c0c00300b882a4401c0b070555441c3c081d03544c0d080c2e04a000302c0f400b0100140180084100040b002032092400d18041d00440b141f04061918018a4004011004001c2c40d140e01400c1030038180043c9498000166900441c18981138110058450505000400800c404914031007e42d90040300038180c400c85002401200381c1080c01d0280d81e80d4891082d600600310107034404c00c1030310408202180909401092009034440140340740342e190460307010081e400000003034100c256104008c402401440303910003070f0030424581042841103440e600141c0400a004004802408005440642d40a540801180000d014034140b5200a181603000200c0b8176250130841020800c0560241c5127a40c405d1307903020603607625203500b103031910000c1c450442c82c18024000e0142050040119 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242206330 1250 242205080 242205083
    0x1e06130b06040e0129030f032205130b0f040516050a0e060c06090709054501050613020408070501050c0a0501180b1807060e010e0303070c0e060d0b040f 67
    0x2ca03500030822070031403c43da14034440a40040700c03250303000c01d201d10002a80c0c5d914a412400b0f440d06441108480d80c682c42002081806000b003000301c0281d0b281020511000381c8000b50810072400d5281d0008001030003c01c103220b1080c50050081c0086240c540100b034402e4512600c0e076040c41c0043d91065072503400102c0084107100b99401e800c40182c0b078002c06450b540f4085802001c2c0c60a003c0901400c000268000e02c51150901301003100440018500390343c0d1107540c0c41c00115a0b15818035030740c501040c0e04800c4d00745129240d10352483c81c0054000714001c0c2002c80702c0e001c1e41030519441d8401c900c158402e00819811407a4100030a40c091070180c0484010780c3e06403001401165100c03403c5030701104810700c20585400032041440441850a5401441c240000c65040c03002d449442c1e40700c216210784401c01c06842203c40d42c60b44180c040400028019088039180c0c56145420050024a40203001010302520300040b028a400c0b0400301078550810003400e82c9460b2920340c3e00310400250700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242207580 1250 242206330 242206339
    0x60e09041203150515030a05010b0f0301052e0305090d090302090a0b060724050604060305060f190f02090f040b1c020a031203091a09030a0804051501081e06130b06 72
    0xf40000e081e15a005d4030003001e803201240d0b0340e40307140c001c1c00c00c0115041030700300b83c1c01c000003800f400c280c2c0c0c268502100e056130760441c0c210860040c0d80702d06002e85040c81d4030f10004142c8640303003104815090340141c0c1c0980484001e6442d204a0760404582d80c1200d840065400343c415408501013024a40c8850b00c0510702400c02890052140c07101041c00c0b1200070140c40c0140d03071030f1445d402116517125490f0803404c00c031014001c0b249540c898550700c03c000380c80510000c2c24607010a909040390303110180d44240044003070182041007141c010094002e00d00031802681c5440c95a0010719040c8540c1514034402800c40fa10810320450241d1002d1440104980017642c504021000c51216503151b52550140d6501040306402c0e480d0040c81001360400c0c0d55241d00100f8203200031000b003c420b448142c83d1a181489181d511400c040d85005407003919000d0f01030001d00080f801c1c60001c0341c8a0704500795800303400440070a11150f19a078100403502c115208000316030400001d01d00c440c200d40c00590007030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242208830 1250 242207580 242207621
    0xa02040504090c08070e1302010e03011d0c0307091b08090a1e0201110d050301140402042d060e0a05040f0e161a04211e0c060e09041203 60
    0x40481c04039800c21400362404010038400700f01c0d0080400085003d00044000c0b080e203800c10120302d42c0750400565009050200800030a003480d2000d500c0f265403801641031203418a0040390f19580c40d15404034442c0c1c00b9008001010904050900903414910100160f40180710300f0f0300c0080340d1241e009032a09026002c1c04d41e140c00411030001c5096060403800032905140b0312544009003840e0001d900184040d04406014460306e80c00c035090302d04540740c5113a00ca490501c0980082c00034803ca07007040700101d4034007c501d02482502c0250070751140e95080c017203899644400c820b6454003400c0c000c540c1e1245c0da860b02401182400c0d007002c00300c0000b0003000b103604d183c105807680c01c0c41c40c410b50310029950040c400700503001c5204a500207030180a02c400e890325041401c880082c02e0074071866000580303e00b0300036003045100c000722084c8002c1e400480d2516155840d051009030a41d1040e81d0002d030b6800c10303010042c07400b180c00c507000755403000c603400c0e051600c0070054025055013071170100020f8660 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242210080 1250 242208830 242208839
    0x28140f28030303020316020109020906130906060e0412020625200d0f030204030c0b07080c0703051507090b0d0c090902130e0a020703051b030f0c0f01060608070c06050a0204 76
    0x44254101440c0b09450150b2a840c0210b031000b15016168801001c40e8101140c900150b202c102421350428030586e20305001004041d0010003401417840e0041501e490b040c800038000e0450815180564458401da810351041603e0403a07507540151080254443c49220b0320601c07803008110350001a5060401081030801c2c881c40d0040301d404805e901e0103a07002032200090955000c9408181c0050030b060440c2428116294402113001c10700992124240000d2081c080c481c81c4800e440c88400303500121440c032074580c5049911202008a0943c0c4405050702050f06a401100c4480540f507004076120b04008041c26540e0192001c40411001d104045001041e07580c10f030f000a0898132583c103450158945400c0c808040b07000010a515445841484401c0000c0d43c004110350800000d402c641c421104402d90701403c2d440347c0c250007951800b002485004108011802e00e00d03031604800200540e0340d4485040c0c40c40001101c41c8070015640480040020321141c0c4001c0c2c0102c0003040050a00c1c0c0c48 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242211330 1250 242210080 242210149
    0x402011209061e02031005040209060705031303060b10140a110d0e03060901060f05060c101406030c03120a051608040f150c020109050904030e28140f 66
    0x1601400d4401c581c4a40b007064041c4071005403e50303c1c4040310b07411440e500e8150080e1000401c1405220300c55500000c0d044411b81e01e0b40c003a00d64254110041e40c0d41c5019000f004002c101c4944821202e44d420002c40c08503a2a000402d45081030f041e40710142141c8031964080031550169006c0b0341400094000000200010040291080400e031102c94486c0056800c140c81c102d802400c400060b81400030521220b0030048405003107403000d5480b1034035046109515401c000420500f08820b44c540b1124003218518845114004c11003581a59410802e081c1819150720f07030752004101c01342d804c01c8a4504140f046c0c0051070020700381d007100201e0318404e503511521680076500c030002e501c40d08003040c00800200d025030a103868150401c032100ca20ba507400a00400900e2156921845015000a081c180a025018110300e8010071080e9074030f4058012004c86008540780b0301d03494400a5004c9540082110034890b00b1030003e00c500500c144070000c000d8054001c0b0410700043c03040d0024100000d02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242212580 1250 242211330 242211341
    0x8011e230c03150405041a04020105070803070503060f011715040902040e0c01090501081303120b1009030302010b0f0a0e0403020708060f0403180b0a0e040e030f07060b010e090f04020112 82
    0x1074200d00190b8900f0328480b100b1a0310401041c1c04c0c81603242509000009841002e9a00c161080c3e40508895a0790340c001681c8074040d450340609140e40010400110942c084000d510600d030403110b40703480c8a0340200454070810310315101030030900f1740f8010441c1820003061043d08980020b0022801c41d04a80c04181600c009038117400490b4442c2040018660300001c00c02c020b8a000e103071410692800038010710b03040720440005014088042c1c1c0c94401c80c0490303000410010b00182c1150a09405020002d00403c1c5a2105900651800040034000d03c0c0000102c242190010b1407a4087d07424a8915107002601401c101c1c190301c990f00001a140c201402070303134800c20003488402d81b24602400c01600310040402c00189099002c0028468000034205540e409042c40c64150300c0c1d45c00000c003080052075000451800c0d8400400c4103185600703003030010500c062155000b80300780b0944400650f020701c400d01c1c0c4980c5c070a100f1800171344002c40100c612607100307005151140c00c06508921a104030340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242213830 1250 242212580 242212591
    0x16090207020406050f010f0507030201060509010803030910020a021218100503040501110f07120e090108010618061a0a0e0a0f08011b0203160804030501050c03010f08011e23 76
    0x5401141100c01d600d0580714450081c0340664001d04003030010300000780740d2100c1281480500501050300030516200b5030100014160143c240b98213540c45816042d941d820413144001a0310801d08000c00c9160a4000e441d00b0042c540c00520f903c50100741c402c1413540051404020017520313040ca50b0b11651341c121a80d03030401000d0b19555620304090600381d0942c0c107540710400e4080c038100319121518401c0f10413254120780144545004141d610812117541d1140c0c4c1e183c80d44101c9903400032519080640c019405c82e008070100000c2090200c486074141c3d641c921402d824802c40075041310070740242100a04141105180204a5040f100300082d10258181c0160480100d4030f00180000c0009114880080b2104850320a0400311a40300a40c2c1344104402203036030070000b100540c01c01400c1000c0d5800786074081c000380442c3c500460414a240c02c2485941c2a14254801c00102c6035018031a24031001404421410702c000c455039240301400c0381c44c000070989080f429080c141510600c24460089 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242215080 1250 242213830 242213849
    0x915052107111507050c010b0405070806030115050f041d1006050906061305040e03070b0a02070302010c090803031506090402180a0611060f072001150e150f0316 71
    0x5003400c40e40140482c110003030251850340304030b0003125041503854240354011600c1c40d00d150384500000b61103015000701c1d44911f410508001c2489031740b0307410400b00d61140b84180c00070061010b40701d034030071a4540a4410b098001401c001000d2071400c3c81d400458840a00384140400584030ba00000e190500c03803141540000c0c3d44907024017051800501041e080501214503a04011802410762004c001c50b03c600c9100d15980c0494003244141401600c07003803500502000d0351841e05851000103940928000c0300113500e0510451807580c021803805040e19540d2004504650390300e10501e42480b02000d1642d8030080034081c1c0c207100d07500c5000402c00381e01c00003407801c0c04440f9082800780e10f015580111042c031401c2c5840702081d80c800250b4580c0302030308a04001d03807a02d4a840958074100c0c1050b611540380c4e480d01c0b20b035485650540268449000482104032030550b10909005d180d42d09a5200000322074072000c81790b081c41c000c80c41c03030752016005050300d1000d51a0200540100030325441400b24 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242216330 1250 242215080 242215147
    0x4110a0f030b01050405070e011d120d03050a0507020d0807110c09070309061d1216021c11040219030e070e090f01051605070b150310052203091505 65
    0x103401c09006c0c05801210340c0c02c08101c0300617580006043c216508031600929401400340030003580d0340101030520b5900503000c1d90303111000c40c60000c000e441c048422080050510000c03540552000414003902d8200d562001002d131551542140d003201e6160b80142c0b1445600b03d1071120780d07104c03171140e4061100358a001134260b490303107000c5094814410004504c51201c0803100c0c20840d0110b10b062180b40c0f40010b09581d0f85002c03a14403006100c000010b0b410240f8405030034160f0503800710300080c2500494a800400d0105e10802080e80b003903540c10324200520881700327621140a5004000505a210700b503070350321603c46c1c012484160084890b5000d0740d1000148509042e400e10421b900a0b030b5148100701100c01011000e0300d00d1007401d070014056108000024096011001e074011010001802c2c0d0344807204919030b6030040c1200343c81481c0f0303580d00340803041480d8003500d600d52444d99040d142c3d009110701d4051202d45000b210414034040c8803040020141c14078401e000c1d0000946884d4a0590 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242217580 1250 242216330 242216339
    0xb030f090a210f030e0c060a09080d030915060605090909100f230c07120c0507060f14090a14060d050f01060e0a0614030703090210020d030b0a0e04110a0f030b01 71
    0x32880301c000d00c050134180740010010342d550340440d81c1820960151202960740850301742c02c80d1601c0c03171513100381c000c0e000e0041380d400e109074107403c00b41403c2e0081501030513944a4400c2c0d00700700c80d45403140d0b0001c92400c2010035124200218001d40c4401c2000907660850b0a034411801030392081c0b044aa0304690780c1845482010450800c07080e2803603000340903c41c03854a60210301d0b90744100720307001d8541c18044115002181c41151200c2c1201d5000007620380d110b0f920103020701000703001f410382d401103074511441c140f006100000360340d06810000d082d112580e20b8202e56a40040c564440d0f10b41004042150306881c0c0303c240500d41c003564034102606010f45c500348000b440031f02d6041400f440f4140d880d44c108241c640c88088801f0880c000098036540c1e86074109c003a0014141510000d410111060540306065004558032113010b0240d10309102181306801000500790180c00ba090154010801090108003401c0c1c4000940e0005048080300301c0e282e40c50840714401940c0200d87c484404d000500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242218830 1250 242217580 242217587
    0x30f062d090204060c0b0603190c0f150c02010c0203030f13030212060c0403111906120b0402130b030408040e0c1c0501050d08070501090602030c04030c0f0b030f090a21 74
    0x802025080740c114101810701400400200004030040e00515030003022401c182c0d000d1140c0395100b1701a843c0f49003a65144d00e000218414548609000302810388400210350504c038184034034a079520740e50030341501060307401941e00250080d82039070144801e00009400420f01030003030905030403001c2d518402900d1441000055200c40700042c05541003d428003014800110070341c0c0c00c0c1c0ea40b00030042c564007450340100c0e403061480340c0c00881c101e6041074005649a00000c3c3c1c0030100074809010300c46038201d80280f00a0f440f800c60750624a00c04204100101d130f0000c40074540281c8030320545480e055841050000c4941c0585d0740c41006200042c0020342000c0f20004001c040f41c07400c3c01032210303600d02400192211012403015040d03210015514080200039804280310b1640103c1c21500ca00f001c415002880e000740c08216070a80c0380348000300e1058512041c8204a423100085246035542301207030f9040f5076401401c2c60703004d84191400d640006104003603103d2802980b510a492a00c00e06600030b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242220080 1250 242218830 242218919
    0x5030d09090c030e0d0e0f0612131401020d0f0b0102060103080d0b030c040609140a110d0e150906160302070b061c050703031214060a0608131a0a060b0a0f030f06 71
    0x500c0388a0401080d120500e6440e2700c60740c001001d2482c08004900e07400c244070200350030352101c1c802e9403001801a0340c1c118154401d0500032031802c03080000604940069984880c20b000c0a0801081400055001111600241348440001d01501c4001d030b42c05000c203056415a4020000c0300b5103a404008924209000231980040c05440601c4803411008241c5524418901c40c000c106803995030480345008204100c107c5030081e101d1591080c6000400107407141029505941042c00140c03100b000e092081c02510086034101d40c044140d500ca210410075990280038401e03036044518115030300481d03030502035a40158000c0d201e90002411900000f803c40e83e285400807000703032805007030010716181c20002c00c040d6030181c10001004c0c3c8a0400001a400c20148002c118160041c44078845078030b4418128060701d4515410300040b500c8009210880c010740c00c1210009105007182e100b120301c0b941006840c84054000012a945c481201c0404d0b640d00d19400715001070101d0f0361080e1044901c25a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242221330 1250 242220080 242220109
    0x1305090a0204091815020a0302040b030a0504140a0213051e070801080d0c1a07180609051519050a120528020406120506060c0616020705030d09090c030e0d0e 69
    0x40d0640c0c00b04c2c1e60300c0c1d0741c080c40c0505000304202d5010403038000f59030081d4102c50203400d42c022915100c0c0f60249040d0068041118102c81e119100c0c0000300d4082130006070101c00d940d00400103040420406014001071100901c60340c0c0c0185418400c8200c640c00545e542d0081c862540c4406943d818040443c0c5024040e1000800700b0030f070000a00c020500c5540b99541460a1035800319079501d8081080350310120b00911194099220807000032159044501203086460640c0c200d0000d140d0384400100e5401810740301548440b55800021a19125600500740440f560401c004d140d810101104211141100e0801c0d900402041603080c40c2c002c1e11140b0b4040c0c2200e44150b18250605000805200a110311451510303200c1e008116a561500b0682c1c1602450008899140c5045600c085203000c000d80c045015001d490408511410003003000c0d18805c2040d10b44c030760380f1490448400b0085c102c48604008150341c0e035030103220703408041c4540d182c1e0103601d03078405608403440000c001004400810 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242222580 1250 242221330 242221361
    0x21f020a031710090b150d090201170103020f12010f0c0e0906030a0c05120c0603070206191a0d050f010e06071709060402060708041d012103141305090a020409 70
    0x100903a07220010003c3c0c1c180c59540c0c0002c2074046501c00460b0804010060220103050041109404507519602000b1041e000f640c0b4181c0c0707800a15180c5466141c20300002c0c5d04050082200c04032410b210b051030f030701000036600000c2c0c030010300e4a6550031100c90750300d02c00c00100100c1c4590400d24040100ca40c201d0b00450142004005540d01c0c2d0341030300c4070303403054500800c000c0f03000780820f58040c08400c07450400a4511a070f03900d82003400039180c5804036590246c0d00074280d0400d501e6842803103079a0304020300d000c0030f80c40d01c0e5900c403c104a0703000c220b404980030300c14981003031103005081c020131945003100002040b160a1544010b0654040c20a81148010b68031040250300080010010341180c1c0680c0d40550342c56140c1860b40d0300d4031030741d004603d8480f071a030440708000c6214098113040744c4407165009541c4018100e04076840c5066100540040c1008071170340041c0c6000c100801100418000c0d03000100d41d140082a40803900311400d0040d1f81e804202040030bc0300900810225609010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242223830 1250 242222580 242222627
    0x40f0302102d051204110307120312150909050a0308070c21230d0f0204050d020927030c0106080c03060f090c0904080a1103030c04030f021f020a03 65
    0x1042ca41c2e00c0b000281c0302c041580846200345141d80c0c003801c100c13402c0380c1140001c4101880c003420010b2030000c0420040d4002e200703524000a081d1840380d0140f42095142d80d4000c1700d0010f907401807025025003206c0b0700c021420424001600f41c10352040c0c00070715110324003416040f41c0d9801e0107049417800821020501c0319108503000028400340d941030345a04103c4503905240c0046408a40072100249119055030202d0803201c6009900d0001d450050030f0f00006010100d00184060242c3c001c1d4840e0940000402d41c50100600d445003209500c4a446a00141d41072903000f8110f0850507045030045840c1c100060481c0c2c000e10030300a40d030213002240020540103003000c0c046a5144c0c00100035003000c3e5083d40c00306260150501c80d110422500802c4440e2904060805180d0307036110450040201c1c0250b0322008840134044140c9219114160b41207050034a90348909c80102c040400c126484110030400c20203244207100540c011407815402000d004280d032a0141c0150040c1418090488285 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242225080 1250 242223830 242223857
    0x70e061305061c14040b010b040b03010605031b0a0315080d050304140a050105040b0915150d0206070f030e0306070201020702031209031e0f0c010302070f1b0308040f030210 76
    0x100e50501101c00507a48a0b503a861546400c00c1004410a0002111810103002659840d0448020780c00f0b40c1c0103010310505641d032645a149244030314490450004c005000400c5a83e0098024640c4a04400d120703a0300301c103440d80c0090a40d404a481000401e81c0c03001c8200d01c01114084003000f0742b9600f401040d158502c0080900103000050000303003c840c01c00d010905a8009018010969034840021312050900e407428401161007291030b900640b01d404100740090a030014100d0040112000040106020760f0034081500241c101c266008442001100d002400c4072100d40b25030383c0a80c0d149549042d8460070141001c030064001c8045a00500a4501507a40803851810040c1444a004d9481d030b03a00011900f41428450900141034013640040709125002c02c0c50000300445c4ca05490304a00c005005404038004d80601821040d242203824000406100100ca040101c454034281066900e03661155a80d01540014401d0380c3c2d01d03103080045082400c40310301d03500c010341020140003c03034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242226330 1250 242225080 242225107
    0x20a090902091e0607080c0c10180b031806010b040801060e041502090a0503010c020f0601050102070e0c0307051306030e010f0606050702130f0f06030506060306010315150914070e06 80
    0xd140c0341444501080a00504039a52001210041caa11004187e254001214502e8607000c145817458080c807407403210820b916218803561001d411000b1444424103040a01446103600020043d03003401d09601042c40c03040404000090007441190304840d5202e003003a011500755003080c0d0110b450241c401c0180800150205e402d00312405909000580f25006000003600c1030842c0d074031242e015485e15086418465000c41d26041121030002243c0107641e8500049a851032144140c0c500c0c0c1d0f50442c081002031f500c1400030358000906103001820178500d100450840b940c940c4c451000b003036443c0052442ca040a00840824210151080143d54540301003c1c01d0380c400c1c050020703c520810445e8203482400b56100510310340c03010a0030003849100000780c100400403408180c0d5944108030006484d4540011918182c95000c4074152102c50744d00c0d080009002c1e1988094500c410310340010034605024402c00c1884810b030520f41486040130f44020b49140e00400e4000e00400c03040005a844450303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242227580 1250 242226330 242226349
    0x402030c0a0b04270e030d0b03060603120f09040c0503010806010b0406080408090406090515120102072f03152a0a0e0315130308070507050d1412070201020a09090209 73
    0x744c0e03900c1c2070384640821101e0a803030080561401003460130400b40044d09001025022004101100304028101901090782c0d4039800c45103070f1342c1607100c0342000d10001d9290025005d2485e00400c0c040c07e040711b07071000406036008480d001000800110040140000801c040d034010310b41002003514045c10039a0061181200510207864484005040c2e240c07910b035640010000c0c8640b000802007414000d1520308448501e0314030314810a8200c7c1c003400c0c072150600c01c071205640e0200d100c02d10f54071800c005500c41d501201141d80034172a040c2d00c0b084951424000e4042007c07401149080a00c1c201040c12400140c800403462800c1c2c95803440f03000d401e031080440d4540303c09424401d42284907030b400a403401031844000010703c00000b081c001070000d00482e0010580c401d4650b0811941c42640454050280c2c0d8000303401540102c034620303c040d0045010781511100c40d0b095901d4101e940700d0012044409480d40070050b0b50010712280119400082003002d01070448041d032600b009000000c17200396 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242228830 1250 242227580 242227589
    0x309050105030628091a032512030807120b3106031208070206070e06030406090227010501111b030309211b0d0b0621060402030c0a0b04 60
    0x7000010900c15903404420400296a42c0c0003107030744001c10314580b8031007041031069082039810b01300505003003220781c50070900d03121018000740802e01c4a92640200115048051030f099001940c011503000700f41c00703c01c8070050084d1511b54450030002001420080342000c0316181615040d0180c81c66030b030b00ca01c0070030840c400103407044034540d44019200c0c1ca203000d44000c0c0e40c0d451600f0000400c100300110380303c8a00b1113a4540b0065540c44103026620303110102c500000040c076100f9155a94902200550b0700203010b000002100c00c003d501049071425074025030458150180c0d1044100141103184501404e0207107400400c50150403155039580c1100b03200f80d41c180180310007103007141c0c07410010344400340c40040503200f43c002546030801252000041c0385000e03000e440c81001800c0c894010480d03031211301602d41c00c1c480d015a2140300e107549002c0d00c2503510002c0c240f0f5030008255680c1d1883c0d202e40c1c440025000d07500300740c8101460101000301d690b004d141c410714104003000214060750101da = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242230080 1250 242228830 242228837
    0x1e081e160c030e0a080708060f0c03071407121806031e0b0301090f080301080105010806010605040302060a020c090a1508061e180616032409021602030d03050714040303090501 77
    0x31500e902d02561aa00e01c42122900000c915070b001600840005403c0c080720980025100251189035420100003003c94800030928001c1002c2130341c0300d00c900740c0c904000c4c40d0407041e9070528286555400400c107440c6044800144007120010940c1c1c0d01a0500c4014120340c101040f845620641c6000c01907021a8600351080d0b4440c012a95504c0a400034001740d80d00840602004d6224500b42e1040c5d00280140f1081c1d61900001040c240f0001507014103a0f40c16844050405165608203d4107038000d02c0114118021802200c5142d111390285038000d2600007c041500c50256a02403080e444980c0038400560101050041544100c000c0030f0580111802002c400c0e554003400301841224104101e00b00d00c01c0004000d464801002c480d1403950055030306200c10704d28010ba0060038040d280d0034511000c0c4500c0100409902d550051006002046043d0003507542034000909040760326001c080402d0304c0f90301700508180e0141d1a030070f0408440486500701819030703e000b41801120f01400713060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242231330 1250 242230080 242230097
    0x314130e090102070b10080c04052a0d18020a150c05060403020303060405010b07031d040603050313031112030304020607080f0307090312030e19031e081e16 69
    0x10a105400640203403128003600c8105062000040c0e000354402942500d0b0340314400003140d581c26956159000311200308005040c041030740c504202c0100405082001402ca4102c440813013004503000d2843d5034041e5100580d10741c4070403106a42a9090340c1c00321011711015100d01c000595a240d8030600761400901d0000c540803c402017641e21034003e1001412500c030780c8081208041d4000001e610900c1c0940e420700c1300d82d0b0384509203600c0b8003640c200180490b0a070b81c1040788140b82501000e42d4040d0050020074503c0da2501c0e039604541c42480403007118030080c0e00a10a0090018103100300050036035150611503d40c0191580749d00020700001d00c0b41c00006104402d010089040d144900040c03080f81d640c90500c90806088058203110844242456002c650302050003403081c007024501d103002901d2200035844142d41121a80481101031014904a9842407100c40138002d01c940e01d50344450f145806c00c0342c045030394026451440380340742a00d070080200341c10540b402d180384022503080122a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242232580 1250 242231330 242231347
    0x21b0a03060207020a0518060420030a050402270103050c0102030a14070204060b19020105160909050603030d05010b0301080616090b031003020919051e06060a030f02030a0e01180314 80
    0xb807038174164442a4062400c00003003071aa0540960170b03014a50407501000b074500307640701c0440d882d9840504000421024000104142c00b00c2e000203602c540300800d82d000020041d6000e5810f070001c0b800d00340b407170380001c0c0c01030003044420855011740010900085003400e20120008240c14032102a4850500001c105841151900d80041000c1c24800800c140c407180d04841c00d10711040781c3c0b00034400641c200800301c3d907801021f404500d00e0136030301c0e603030b40c1c054604040c840d40150501a0465806220810210095200b14810340340a818100d102d19502d500d084c600e0342ca0200040c010446514141c002ca803207049d004401c583c100c80346100855102da0701c1003198900718019078006508294060100603010012601c89410700d01c1100c410032540d1a00005801c1c000b00c180f0f580b600300c154060100c0d6482c5040c0028050700074007407401107000480420481c0c103a030000d4031a000e08540f5070b41180002e46003802054004001d0350300e03104803803410f900c0081030121054011155100c00007502c02c1e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242233830 1250 242232580 242232589
    0xd03020309030318090f0c0d110403061503030206180619021b1f020712110a080d090b0601050a1d060f130617010303090506090607050f060403021b0a0306020702 71
    0x2521204002c0680c0e4484400b0b940d0728264080519601c0c4c46100c2d4500080c00e40001514050300603455444102d0429101e401c09000400c0740304203003155107900340b00000010300c190041c41920030714a80180b0703d00c1c1c51490080e00c0c0100203041d042c001c1454449090a4020018441303501046090285c6420304c0d42c1c0c02000b00901c1050b43c0403065084a05090305540d400042c1020b04070750083c1c092207100c1d00020540203d00034140002d08035007154800c1c1c0003d80c03040100c8080c0c001c503602a100e20504641d5007100c03552118601d190b0307194440312003c043c40b00345910654084020b0034018135101032034100500302c0c8600c0b00d440080505032649a04a0b0311a0070070f5074558101c4100281d80c66485840880a8007070603c66180000c94014011040165058801d07040341d507d44c5452501c40e0504003004143c0d00044001034000e4014840034011400801c500c00000e0303003440c0608803d0905040007810403281d00f006d6404165003820020507526034150840032a50090001030311079000b4030008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242235080 1250 242233830 242233837
    0xf030b010e031c020f01020406050f0a180801050603060f0f2a040305010219020d08070302160b0c091521092e0605010305220c05060d0c030501120b04020d030203 71
    0x719014400d405140d40449101c0e84031560b4980650215145070101c8980c45080c1d1113140130b0080003072010300c140c0080c4a01c3c2805007440d0b000c9801e020b080606080f0215602035400d90155400b691620284015030806114003078005418041e014000d240840d1010b80307200e0080c210410300c1c0001071a402c03524041c8402103203c82e51400c1d40d0340e03407155a414110301035003100900e000003910980d40300c5111400040c001d450302c1c0d261744402c0707c03036612600d05500a40000703903401c0354020801203203000030b802d04489502c10384904400d9900c80d58000e0600c900d410f0101ca82c000c1c0307070400b0081680b8001da540c4581c0b0540c06d2501e2202299547d1003030050070a6550900021342c03040b44c09200064081c12a40801046a090010012240c3c1c841c01101514019203002c6164207003400042d0903490000802c4816601a402e5000d1190762240424690b512208070345071281d5854990b2851182d0600419004050b01500c40d0341045c0c4540350b952200c08040c0009100304880e81e1060b04041c0280f054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242236330 1250 242235080 242235107
    0x1d060103090b1303141e0f130b0406260115020a02040911010206130804092301031211010b090703020a18031b0806090703023f1c0f030b01 61
    0x40302e90300b0000c82204018184100444c042169207000c0a401c2d400722043e00d1301e45d5000c01168031090013406445a00c0d83c4620000741041004101c2e90f41d41c4001203c0b140000c00015040c1650746240c83d600038aa580460145aa801d070343c000303412090a0000d00850544600f18807107444003151400907442d000c0e070346400035042820300b1200c200380b040c0c030701e86003189207020b80a03502d40d030380d405904c9010241d06040060001a0601c01880b10f00355a0340402c1c2c1c401e030075902601c010090518501450402640100c510040c032a03041c2c5401c0754002c989400034000c2400178460340c1e0000b800900542c60040c10041090b502044000841c1d12034604840c5a100d00b946000030240c0700c0c00c1940c0c0b0004c0c1d030816290000d104020004180c040080c20310301c20b0103058042c12400d4119801c025011452954588200b13a02c9514a185603030f144265021840ca80307982007000c2034584106908000303039031080714802100c04500c0c7e68510342000d403040043d00b180c40d0000d00e480e181001650050040d105 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242237580 1250 242236330 242236343
    0x9010c020c12030d1b140a0c0b0402010c050a060e010e0106051305070c020d11091518040302030f300405120702030106030b0a05060a090e03040302010815040903020a0b0708011d06010309 82
    0xb50f805c1494510150001e2075071075601c10132130403a2152401090f11a0381c07600070004516207088804521009405130308030b4070514000b4010802d13511540c2ca44001450305407000365481c52503445040c2c09104007442e002e100c8000348080e52800700012040c00d6a602d5079003d950700c03200001d04071031041c0300d0312400b9940203041000d08850b40c181014440912481d05d40504110004680300b030742c004550082100000781203182101c28040c2280d00c0e580064412130a500c400c0c42514501801640a0410705401c580c200002e04030006d48600012508180207101d15000e90510001c1040415600307050030351038800d15901c4e44144042401403403503600213400e040d0907100380032200f40c1c01c0d08002d00580b001c46281d03030015101d007107610445111800c80c0f955070380200001c000550050b50000d51003107442c0580c0100062400c046810b440100b0400c9005030426900102004005007040340c0004081c42c0418066060421002244281031030821001000c07034008ac0391603205c2c1c0c00803001c1c19807025 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242238830 1250 242237580 242237591
    0x90b0a050f1e03041205030123040b04020307020c03120301030302061305120403030f080a0c02060a270c0302011805010905011218080d06080118020402070203071703070b09010c020c12030d 83
    0x1902c0a110b60416181211504259281314118074800c405990580340c680e908441c150083e0100080b4103031548007041e030003e4a0b0150981940d0f103e102a51151a9640141164240400406041c441030750400000b00005100500209500041d101d5102c18505a103107250049820520b1800419403115121010006404410940c0c802214042c0261075200d1242a0711a40c500c1070030f840401e4014030050f8800000114001c186400000c80284950310004e1081401c600803440c0c1950504181c074481c0f01c1110820840d648401410008001d40f500001c0f003034201000200740222034031800e41002480b1010240c1c007007803603001e23072007030740100f1503030240381d000e0b03207014038064010750404400b603498500005146041805490a100c401500480650642d5401c201c0290814003050741c01d031103191000301394034051211100c80c0103442c80041d52030701c01d189015114020010810701190341082541e00c240d0790009142002454101d9865506110034040341d8554080d00344100c220341c0c1005c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242240080 1250 242238830 242238877
    0xc2706030b060705102a09050a15020a02040203060d02040501031a062706010915080405070f0e04142406040513120c0809130b130605060715020d021b0706090b0a050f 73
    0xb07c075250445905480551010b65141e10b501101090400f107840581c111415200051600c4d500640c4d2140740204602d8901c0c490750045030440301c0c240c0046a1000400206004140200e14020b6008801f2140078200c040340d00030100b61001ba40504001c04500403000c691503070b005220410141c00d00c4d400c0c5015075407080000804050007078500313039002c1c020500d010907060407014044050390810108510076485540e40e284007007003a0700c3d10f14460700038014249141500c00c103940140a01d0b640951003503051100401c0200c0e00d011340748641061440030318500003201c280050140b84541d042c44504043c5905144086204012040d035001d0782c0c10810809206080d807042201c240f060720203015a004445e14482100d54a02605900100030b0006000080a508040304a1076001d803004d030500c2d0070b4402c3c100681e00030808071500c8201004945100301801c01224000700003034a42080b406160003510b900501c07030108802c0800000192030310910b00c0034011141861089200c5500b0b69409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242241330 1250 242240080 242240087
    0x70506030c07080f0d0203150a0603060807140d050f06010905090316020d060b10020a0302010510140d030309020603340f0c060605060a03090b0a0209060405040c2706030b060705102a 80
    0xb100723590b01c91a40340201244c0c05219209041c02e641d500d8000301103850504017240c507143e481c2c001280d41b00e04885016000182c0c02d010074401503c0d240010020f039410400c0200589500500c4d061290384148009041d0700812022203e10350380540e10140d10050390300304000030f0200b031688190001c809219007250140c1c0010405a06402030b4002c000e10b0b2612100c1034113003010b920841c5007643c0e01c1ea0700409249031495005100c944a0300b400100f48031242c0c046140307500115102c0d101000306d07020b02400030b0b00350344565860701e60540395150884444a0003501d9807162072401d13000c000180000408000c600e82c00f4902410000b4003075030b01da0f580024000d029102e122811a006141c9030007181c03c5044600954020120041c181e501300350600050100601005401c5400c00c1094162041446001d5400d10800d40002c0c02c0d2041d034030706011020f025141c10b40041b038007404d02041544040344000c240702402c0c520420b404220000022421040e070880d045440c00130482c1000d021007880d80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242242580 1250 242241330 242241361
    0x3050d0f052508100b03100906080a1703040506180102120a0c0306060219030c0317070201140108030f030105040f0b0316090c1e0809030f040b0408070506030c07080f0d0203 76
    0x203109682440e80000d10089921103400d0300d5441324041104010700c904a00c2c0b84c06194001005060b0300011035031241c00310b0a4076001c1e800700301c50303070820310501e024008446c440c4010030a6140149103142016034513030b507540600401c00c0345200c00a07803022208650a40403901280b1400c112080d190421268440013401c981c1403001c0440d1502c400041c5450001c140e01a050001201560702c40341d4980b420799000c01c00020840411a000d40d440c1d440700c48901069000d00d078903900001d4500d841c2059440d0020042c2c014101c554020302543c0382c1c84e05002c1c1141d041d100160f401041004102d030b81203028000e075480300d540c18003c020220100c0f05072071000740c0440e00005800d0120745c4140c0001e60b1050300c2e03003095600b0341009100c0c140e540e5000d1540707683c010703088004803468460a0041d42040390001d400c00ca0303006034002410042c00104000b614050f000440700d052a40c14203090031a024441c60300300604619000c80c410460200e11025514917445404082d9078a01c1d083e5424143c441c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242243830 1250 242242580 242242621
    0x80c040c08070e120102300c0d090809040c11120c10020c0c030d050c0c0f0d0f1b180509030c15040312140106120c020303060f031e0d02071a0703050d0f05 68
    0x2407c7c2c025041403103403560b100798001c001920b002c61605096068280250201c01e50503a486e6000308035029140d240c1d48103040d01c1b1902583c6620700e4103180c00324242440101c3e40d03080e000c0242400040403d0704040f8489074024040c000059403407207498521803d00301c4041c08a40d0500860004104854104005085507c01c001c00d8400d811115820010700d00c00401c82c26401041c42c891010004044a10410026000307c0c8031200d26001807c94545180560b00260610040040d001104440c0343c0140354000703040700301541c00c1055407020640d881d4100700c8601105100540814141402202d202031840090141400a05030b548a9046d144030b080c85001d001854210110742c05042c0c40c81507105200055016501e5500c0c1c40d020850b840c90610300c5076615020b5462050f902c40c0300e400d450600e56901c6805044c0d503014201d4040e0400070780ea4000880100904240740246076443c08451950342d040c03c0058a84d40302240d500001c000360341c0d031010009d141034280030900c0c28204895100a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242245080 1250 242243830 242243887
    0x110a201203040308090d0f02090405011b02070e0c130f0603150905240109170a0b010e010f0621021303050c010908060a0e011b0306080c040c08070e120102 68
    0x400c04142980d90340e1081c0e00c80a00080d40500002055191400c81002080e001c6c2c0c12640e4007400c1038000500030702d02640c08640d103a6480b11002d5180305108034844080c92580058000c01d0f2400142c660702010042143c1104440003407841146080f01c1d079000090400c40b440418040c4c0c41c0c200103001060700942c0c84042e40781d8103800042d5840d83d8010b19126444190480b0704070354180e070006402c550703150000e5050044061340403804503155652102940440e400801d12140b050501203015a030680081102101003401070180b40402000d00d42102c1c1c00d45401c1d940c1142c1f511100f50b00320038101c1940105030000400382194020200407000380c0c0c1c010f42c15220038000308001907448840030f100d240c1044e00008001207500e1032903800705004422400011031419020801c05407524000c150440c04261340b450188440001085025180c50b002d0301e007045110003071440582041d00c010504020007000303404400c0581c462a19056005446500030340d100c0c0c244402440090032010b0003184407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242246330 1250 242245080 242245099
    0x30302030c100b030a060e01020c1203060f040506221401031406150d030305090a0813060809150f07020a0b150114160f1b0609031101090f06110a20 65
    0x250503c54036407003c10040051261540c0307a030f00c06016001002118020355804e20072508115002d1114002506c8060b080035900d180c000c04000b0282584942e25010f54a0441000340b280c80d0840c2083e00c01d40d8200c101a1503105607890350010349240c507405071224144000000410101100d00c003a4004000c0a485440e41c0e020041c2d2000d010315001240c4c030051001c06140400e010b03520454000380701c0c1040d21034603581515084c21a903c01c20411020000612080140c0b80d805103030103412100c2c45020b402d0302c403501c5a240c0c084e0440540008044102c541c0801d10b19402000f1011805a11040c01e902c1c0d8640070b07070420004810091600c2c04124051041e0b50111000030031641c0100039050342c3d4540e0b1119403113020a48401343c408036805003807600c05c0445106c9140c6d460000f401241d498640e41400c610303200e105440c0c0940c0365414800070020500031001d9441001c4103030344013841e1a0f041d84101c1400c103864000c0010001c0c1121100151100c01d01c070f080c40e402660048261191902c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242247580 1250 242246330 242246353
    0x320030d0f05060f03100e01020c031902060a0b010e06210403020106050102010c02070503070e09100f0204180b09070509015a03050c19020c1c02030304050402090a0f030302030c 78
    0x4c180328081c030400d03895003201884850b110390642c0034071458072094000504183c40340000c585160300c40e001403011001c108014800f1250b040103080c1d40a1306806d41400a95000ca0010b00000d0300035401f03510880d00490300440300d9074038542015020703658003e5071f030b580d041c03030704010303000308220b004180c015420070062011241c00090084202c0b1400760090606c1854008019100400175001401c540108888031107c0c10080c0164298805e0300103005a1b00d80c40c010098011a0310009150302840c282030824400c4e0b91491b21a41c3c0c8030089060a9688400c030070012070744170140070440940e0b4016041c4550000d150792966036400040e1f0300d942d000d10081c2c5e51540c0116011000a5408035194542e4030ba102c1d8480d81145802118140da002e09002481800306c0340f400050b000c030170061348022200f0404c1c1c9031403505008400d007050400c1054070210b1700031a031240300350f014240c02240c0004052449440c0d90700c0c1c400082450a1800112903200d10340251242e102c0040c000e40c603c070343c2505a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242248830 1250 242247580 242247589
    0x70309060e0f0606060c0c0901030c060315060e010804021c15050703090b040f15020c0d030f15140d05030a05030f0c090a18060f12060609020301080304030320030d0f0506 75
    0xc0c100e442d200000c004560f240000c00c50b1603841361028401c41d00482400000b2502d819107042e000e1071003041d001d01e106081100c0281141c0c2004684503812030031400c03c000e0b0580140c26286024001c0c03902c01601d580b00d002040c0320010a2520389213800b14005600c050001c618800001e000e0b0014080c86a82c44030301007201545c0da00c1002800741c4600c500440c001684150b09005050b1040403821183c0980200500813a040641410003a400c603000407000315074948030381c00d9510365010702040b000100e00c41301910720354640150060022030000c80707401a52000344401c1300d15400b10491796a612095001000c6800030350700000c914501401160000202c1c8054543c0b06502511502e007072844c1c01504101c241d840e41c80c61002036618071005c902041c0200c10b140181c508020480d811241030301d0020112146540038082443c410b10045c80902c40100c101c9040341c0d01441c0401201d1111240485006440f884002d054800007680b0000c01166411680380c544c031040041100b030340c4010900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242250080 1250 242248830 242248843
    0x3060b04140612120d020d0b03071a090d050d05040510080c0307030c0e04060311030c0922020a0b03040c170d0903150f050103140f070f09020d0209030105070309060e 73
    0x8003241205030002491803c0080c0715488032055881103444207a24100ea40e03810b54000ca1a4214481c0c000895800d0000e090007502d805800c02e03001030500301d290010700a0300d55480b500e4070300841800201c402c100d56501c45041440c81c0c00c081a6a4429100b90000d45180d0092050b9409100c1c10b2001d045201c0c0210b100070f02c2000124109031460340e030940210018441880300105000050010465a4880340710720b502461140b9140201450160700709407034203507503141691103208641d0401603640fa6040021a2084c0342d80303104a006821440004d4402030f13150810a440c4401008020620154a032103204903840c00c031031040500c0e0a08040f5484282000380140801e090340010000540202c0041600e5805210001000c50080c1e0120b0140c810a920907507607041c100c89030015480c0b0034441c8100c800050310041040070b140c010742d21154441880759101995011410b0107156000307030125489001c1c0100204400e00d4000700103002003040600035200c03545000200d100d03100d00020503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242251330 1250 242250080 242250101
    0x406110d09060f0306030f060506030601090b1c030905030a0c0504060f0305030a1d0a0e0609060d030c08090d0c06021609020306010e0d06090507030515090a030503010905180f030403060b04 83
    0xc1e014601d040190540d240c2d03c0d00b802d40d404041e034500000000c29103203548180e420b403041ea0003154604246007054174180040e00441c0b00189407603880311a039500c0c1e20440c01c0c5032040d00680180408203080076030394207545500560301401015590410003500d4162007080e100110b41c100f202546900300001d00701c0382404002c00a03801006000c0e44a03010740208544400000003e040c4118000c0c042181b114042d44005090405001030100c5450f000d00035652004007616014880480c40d100200143c69400b0083c001800c00103101c0305544441c180740480a8011140907450b59507004000e40d50f14880d04880601c5140e0030300402c460b010760084038064401603681e0b0703100800200422110140c011800c4075000c2e5101c00ea4400601c1c1032202d1070045000700c0183c40c8551010546d040440c10003440542190030030b1900c0400250080166030640703540f80c500045e1707560f41c0c800f03486644128800c0d8420a12422a581307040c0c20000004001f5207104110601c0520b0849040c402601c00e4101c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242252580 1250 242251330 242251337
    0xf07031b0819200903150606160807060c0c0b07020607120c0e0a03240e0a120c06050c030a0e0106080a12020a0b040b1005030303060d03030f0b12030406110d 69
    0x12440c00d0302007202d02c48500030400320004190710030100303031003c0c0100d8600d01e00015801080c0c4074114907045c04213155440d19024000502d150100006403103110b4580070b0711140f03401e49440c10602051340180c40c1c0a80d400b02d82088107001401018290300503000040b1800c0303001c20000740710b0034400715101c0d00424040c1c482e00c90104034a00110041c00c6054408002c001921801415a9403140e0b5030500070b50150420f400b071826a80010100113081d00c240849150030411056128034001504885a58001c601120100040c0508942007120070001a1489003408103010b52034240c1802107000e8102103d082100c0014202c00d50b0980d0014812400130b6000312512001040803240101c100c03684c03030b2054540f42c103401d0351041c40103072081e98143c0d141e09102d001c10035244038280d10140030304001ca0003075003103180180000e1442940171000400b050f48a000340784080410b9042100040c100416441c000b0011001e803650341c4d00070b840f800c1c0001c2c040d02030a00449002080703810071051681d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242253830 1250 242252580 242252597
    0x102120601030506010c02090109021b0d120b060412060c200a1704080d030911010905030a020f04060f03030305150f060a0c0c15021c0801050d14150f07031b 69
    0xc01500141001040e2030306205044601c14016901c0000780781c068242190010b0329000b60703e00008440340c0034080d0403480c0e0311842101ca2143d40080041401030755424000c100c6d09080070210f03500d400b5540c46a410454291100d804009003074000503d07885a503038070008011128042d50050003a031010203030480d0400086880800d01c03034490400555000b8100900d4582e6440c04103141c413580314004c0c1d0010340e5541c0004104a08401c07140000d807024130b050302905050a0009072142c050f954001d10600058141403840d0b140c41d04450300811120854008141d03076030401a01404c4220380040c60f12960000324003944c5841542c82c1c1c080035029100a0414902d1981580c07004403045d01a03070301e0039840350000751001204814900c40100c541c06422010154001c001070303804003880d501d0500050310010302054458410075111642c100901590210306010094200364440b0b41141c5941a500108040103801301c0c51280280e41f41d907410007402c1d01840104e111103504680f110001050070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242255080 1250 242253830 242253841
    0x606070201080a020702030322050a061e09171f02071101110a06060b09191a070602040504021b070f080607081e070206071404050a05010c2a0509010503010212 70
    0xda021a5003c0400c94005140019580009140d42c10a407000301d910001c200d5004a080d440e04140300003820143ca04000c07040c28020050b016221038000c80f008080213100156031a840740345107100500071481c000c0c507054168542c0030349802610b0003d849000021501d605444518802c03122002d400011340144000e8240044804482c090031000c890b105140030f00c2d0115a081c030440f401401280201c65840760740c8030520080e00e0010fc02c003200c45c8a43e8004004041c101e454085841c0200301a41d80c0c2d600480c9010310003401240c0003d50070910100e031031521000925202e8010218000485031035954400c0c031803800c060140502c130358541101000c10390060090201a0300300000c48003007610305000070718044400d00c2c22100100141e00076410b0141103a00044001d400544103c80c80d4a02402e26002c00c05901c00351040070f04003e00c1280b00d5050000104820769070500c1c04512118507003407c503001c20217148601074180703c0d500c0c040c00050907181c14400c40390401c0c03403402c035680c856640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242256330 1250 242255080 242255087
    0x105070317070203031603202a06060a0b04060906120b030d0f030b01030603030212033c010509190c030b041103040b0906040b0406110d020c0105060907080606070201 73
    0x10049050001004902204121072211203100701c1083d4000d648a142002c1104280c004c060385800505140c680c110302155a07100a205150411084841e035411028643c04101c0c540094111f04010403541c103040382210100f03546000d80c0c02222103114072a1100d201d54014840d0f0310621b40030807506c040810200d402948001d074a81d18075440017a401205002103801e01d1141a000b40001d640501c000210035094410280900001e20303040100501703690380655195182000702803030400200002d5603000095091ba4040440350304a28151860b0030005080c980358180c52001030145400003241d80d0130201070701882140f0303244031080c1c2c1010061a0360000c00c9500401410151900c1040c1940d072514002c0852440c8403940c5507660345010b041885500f0300241c400903060300060240302c00b0502130071980f44c003d41c00200004203c411241102d8075445901c501100450011441035144041948414402c80c400d41d10410550380c3c0050880d6588030865080da4492410301c07034080994407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242257580 1250 242256330 242256337
    0x340309030203040510020d080a020f0412020619110f0d0509060c0721050105130b040b07111207260406030905030f07050a0507090203061008070c060c030b100c0b01050105 75
    0x7801581d2a0640b5240450880034504000a01603400241e0740c080040c1e0086540e0f0303104032100700071030400711503c8a04030b0034801c3d8404c40032141ca00e52000d5040d5901d04003210b07091400300c60f801840c212940c0c40680310f0089403100410a0082003260b0a458002180b1002c11110a540e428a0100300004004198100c103000c400c8602c1000400704403081641882190508000f03030080c46c0d0319040c6801400d4074401400308000d264090007550004040e803c2140d00103034060003180d416999910211510240c1641c445198401d520050f0b400e000140024141140101400b00020f401a51201c84c0482c449040f000803160411080004600c26448080c0b4288100c0c20b403460100c024810804607000700d5416907113908040b00c0b000403c60100b0000c001891402029803c5140c030700e00250001400b4450308062151110006004a1050341c80041c1d041d400b000402000c403104400400030321a0f0340034280110710140c40f05036058000e0b855403001e2a88291001c4103a801d00004480980 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242258830 1250 242257580 242257583
    0x2160e09030c12130518011a0d05011e06032d180c08010608060f040210050d0c0c0204060b0f070611090d051b010c0b0402011112040e340309 62
    0x24403003941414002c0c000d0f01d0f04605407104840d22160040b01c8250072010a6010350f102da1710903590070340711506c1d40b1506411100d102016541200d00340880303850343d01c1100f0951401610304000440c0680521003614090a40000483e03200c2c0e490301c20030b8040b10300c0d024240e0038241e85c81d0030b00c0b04002054545150745445203000414040c402000950000d0043c4404480c1610801401e1201060900c82d15004103420b1340102001c1c203002034650030b01840500068095100d01ca201c0030200e003c1d400702c0d681c100c003824003002300f115800c10040c511000d8140c101e2040d4103001c40003902d1030001c1c054031011980107541c50f00e0980c10795906001044040d5582102450600080c0500e5442085041405010f03002900091411400f041403120400c03040906000e500340002c3d010910380c031150303640541d080c01e240c1c40d145130380c1d070200b442c1c5290b0703e14610714050300040c041145140151214025500441c006a00e8501004000e20000038a180ca13004000130310358051101d4402c6e0807004405 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242260080 1250 242258830 242258833
    0x70821071505060303040f06120e01050f0408090d0804090e011401061d121504060e010621031206080a110f010c03140903011401051c083009010504030f02160e09 71
    0x1b9a81c0c0c00c160916090300c0d8410400708048a0641210544900407483e05400c00d4000300820720b0100341c81d04000ca0b020b413000d49005000700340803845480c2ca110340d01032150854410340d222641d56401e82c018041130005143c003035081071400c0307003c4560034015074140c44480c2c0700e0103a030301020b880d540440e050180741ca0b644a203550540c480c0f855014000e180c0300030fa07030300000070b5107180500308081500c3c3c070103600000c0760707150450411444214081d50420480d00c03c03914420b1907807604040303070390700300c06e1803500e00c56482c1040026031f10b40c0004802d4002d501c42c03809182c018403450304120880e92105040b602180b040700380000040e1094901750701c1800c43d002000d00b02002c050100f4215203502446945003c00c110040c815454902010380341103a800021242902841c0e0f0303000c00794012a0401c3d000806001d003040081282c0c02d180d4551030030140c41d52080361420550081c0070b0001500c040c3d020884440040c4801c91011444031203284510202d000b00c1890640b0003242d282000386140e140d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242261330 1250 242260080 242260087
    0x2a0c100206131e0b2e180209120d0e15070f0c09090606030b060603100605090a0506070503070204061d070f120f091209060e04020d0e070821071505060303 68
    0x481070700c44402e240d01400303168109041d10f03000803040081201c0c3c22a60b17040742e09182013241c04101000c18002540d0030b0002c40140e8104400b145400303801881c4040f94040441042100b541c0c0e00054038450a08203a40d0340c040d0702c85000d05100058180b0200c05107100010004400031800490055110341d203d250407900c0c0d036942e20618012290085011110191561010014021210011074015a048544518509041c001c0c00128a824030900c41440808a4480703150780d034884042d001400081c00d02070395414203183c06038036039010300022841a4a01034001c2407021740030f501c1c2c2d8640301044405066540729403906031010b0f02d0030242d00c0108000c084480341240c030a402100b4000c4103002c000b103421215850684440040b07401720a0410441740020441c00d0785c0304541c40c0d41004250380043c0e44461080c40e44002e0304090380d41c0700702442086400500308500007131400101683d01c081e5a8900751503c3c04240d41e1040d0003014042600d140c10540b40c0024592240c4d0b01301400a045074039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242262580 1250 242261330 242261363
    0x60304120c050d052a03030a090203070503030c010915110a0305040510020d0f05162c0a17060c07020a03120c06180212070501020d0807052a0c10020613 67
    0x58581160031080008102003019104030300c40c00c407101c02c1d001014070040b80b40045c0e005015a06d020003002854a5500d49c081e110a40d01e05000142c0940409000e999039031003548041ca0280c00300040480f801421001003c20840c414414000001e031006521841c1100c0d80c58118043c0101603c190380c68041c264600c090b0300c41364030041100d0014030101180c0c240c001d140391801c030395008101c0c0038982e8211a401084640c42000da400e01114012070f103910300c1455840318841c00c0042c043c1504501403400218442d907051100382c10140030001113496540d80d40c50782c46035501a20710025000b161095081c0002949010000311084c0c05180c102c6156074036440b02815622040094600920144001c00a60526041500f00c1c000c400c001407028501d4400000d56441c0080c0100c02040031240120b07851520402c01c40721014411004442103a20340c5e841c0c003804090040c0219254412032021484905021400e420400c0854001d030906958800c0d100ea1598200030089641d0800340a5100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242263830 1250 242262580 242262583
    0x80a0e0a06060801151a160512090922030e120d1d1e040b1302030405010c1205190c020c0418020906060408030306040c0c050a050616030605060304120c05 68
    0x808103402290080b45152500c4001c5086500220b4414450b00d0046800d11520602511320704c110f02c0c0c1100e0280d6a0901700004416a268100e0010900d019102074028280d20910161010103011107000e810b584640200c0595461005c00c2c040280118a8a05000ca405400820075145005e08014900404000518200814036002c01d01242420040311114000f21020000f0302030281d400710349800410b02102e0100b0304042c0d45c0d0b0710450711100340700d01d00d03102e00c100142004607110040d912414189003040c0a00140041e200001c0d200b500108c20858150080c14000e181d0b5074400041c1c2d40c90707040917070064501c0d01221015840380a407102c0c0e403a282c40c41854010740c2c40c5848207840106500c1004410340d0003405881c8205424001805101804411680c006200303e5001821381701411041d42c903500070b00000707002405040d01960900402199061040466803c2c00540b0303240c03802c0540071251780b80501500030230180b00040c0040c600f03100c809500046800c0034034a5041990b01d03903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242265080 1250 242263830 242263843
    0x5060d030e040c0e06030403031a01050c19050316060204030b0f190504030203160303021b030f180d060908070b22080903120307051c0c0e041503061b0909140106080a0e 74
    0x1c80000c2c1d0303912600c14140301e0700040c0d0151112b09180161400007821540c84e99560310582e0b40c0041c5100207494010060100708803002d030710f54105003400308001c500380031001350494481031300d4840b5041c0006208090041c0705600c125100181c2e120f90051841d44c0720014000244214194481000000d000901d03000140c00c0e098440d940c050380d5049000c86006000c00c1a810405050b4414400540d1480281040d0b444009900c0a03072410380840e03200041000040f04000381c8402c6c54071f1012402d010048000701415800b0f50400000c3d51604481200c107108403030600360300d088102101100180380c00005003c400e20040440d0314081d0711100340031190340242d40c00c01c0411800188030540100d40c0316a01400304c020700081040354400e9001402d981040e2900c184201e55071645d52101d0742c141c505010185402041c100131102c480091040000b40d903590705001320344001000680c000c402e01a0111007183e001110074542d18204055400c09405855998019200c803590003a0070001c0000c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242266187 1107 242265080 242265083
    0x6020313030914210a0615060305070806060d200a030b030d02030f030604020304140607030f0f0e030f030c04030b07020a0201030c0503070903020f0a03050601140405060d030e040c0e060304 83
    0x80e0308120180170002c0480c0e00d4003903d0541001348510150603100c0b15282007029031200c010503a005441140c40d107500002c01c11108401700b615400c00c0c0b920b541d403510300c581419200300394022680c0000c085603000a964500172840b03841d08001d4840811824000f86180045540f203a40c00d91200a180c10b0085e40c002000c6020403002108002034043c25070700303403905410009002000b13025050401c0f0010781c00c04919805034a124403a1000b00340c8803800071032401c205003030305501d1504000c03c1303c001c0700414040000402d11004459205402a40c040c000401d064030001d01221103400811003048024002c0001060f00301402c002540c3e01101d00c10034140b40c46000940064003500010294000c8030000181e40d0307045000c0c0e849014080b2000c1c0300306d554040500c07090000d103030001f60001e80310003401d050608055000c450100164070308035412240c0d1001140465205580 = true := by decide +kernel

theorem cover : BRFrame.Cov 242086330 242266187 := by
  have h0 := BRFrame.cov_init 242086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242086330 ≤ n) (h2 : n < 242266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
