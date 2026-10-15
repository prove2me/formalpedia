-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3823
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:46:57.300057+00:00
-- url     : https://prove2.me/submissions/a132cacd-8641-4cd9-a38a-23c5a067f892

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 687410071 ≤ n < 687589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 687411321 1250 687410071 687410077
    0x3090d031209050714040212060904051c0e0a0b12040212160b07020f040612141501120c0501140d0e10020309030d050703090c1203200114010b2b020708 67
    0x2c56407680003941c18481100a20760482400c00301b240c080d0325202445041d0703451508041d29a038026426900410100319051114002c0ca846002d0440c0006410510007801a0307102a03100c1c1c00f46101c61000700301c0817000000c45040469074545070300c29031201e0782400907003044501c03450701501403842c1c0007600d5850015600000d1440c85d420544401c540d00402003c100f6040e40d251083e8070700241004445d002682656981d60410108048161000426401d00340e07185810b54400381c4040021030409480781c17003445224001c03444180100d403680e00646a0300b02c0040c800d51301e43c8003408410301c44485030f0048a040c0c05d401041e00d544440380b007070841c2a40c000359020900790300003150826481285200b101d6000242d4a014410700039152102003c1940d1401042d6501140c6562981814042c2d0304240d285c040d5410901000030200100c00d000703100c0010750310a50350150300002419107004054400d400c110a40d003107502040751442100740501d0041880c0110703000d2010a011501030009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 687412571 1250 687411321 687411323
    0x10e010e09210a1205090a140705030a060c02010b04090b0a0903050405030604030918150314190605010f0b030f01060e0102240f0c0711091504020c07050a0f0803090d031209 76
    0xb45030344501c01d804020f8100c83c00c80342000c010303520b000c040040300070300052003c4446802c03a040d07016980d44280b09506044040e003085405102d1541401c04005042d8003840201800c5c0d1b00800c42c000340300080106690310001c010b040c1c5e10f144000704150ba0215400400220312a0502524090b0f85001117424032804603419008900c00030010006121088072804030044046400c0101d44004003049000560f00d00018004c0701e81f403110940450400c1205015485103411016200c000d07a28040f030103014240280c1ca03810211180015648400000303a0b405440340001d0301e0880d03170914400b00c1c0e9803a041d942136411403040c254051f018115450943c40040029402200c00c1c1c90001c00c104c00440e0302030f0200443c031008018910220342e00b824040e41c1c660341140d890b0b485890b503407007608114034000d202a901a02c009400740d410b11000405c5811280e05840215103035030340b03809041083c01c2c075209183e0140c20130007400d021480c00125403242c4174441c2c2001c82c83c100c2041d0021080301d4003008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 687413821 1250 687412571 687412633
    0x6122a0d0f0807060e060906010b0f0403050316020a0501050c030f0d180b09061b09041e020d05040b01060507020303180d0c0b0d0b031c08060d02040e03041508010e010e09 75
    0x40c521003888121700a0001c4160040000c00d454245514283c0d62220b051240410f03110000c68002e0f04c0360003143c220303030095410600b00c0b51030303e000880300b0f88818024002240720b8005840c0c005429409001030f0368200c036105019500300103858401043c0c1b42d0281c01060f56403645e035035a05421562202c540807006002d2883c80c4090718000400a15143c0041c0c52030310035400e42c8801a483c0c900303250803980140010798011580701d901000542054003d4188031140c1800801d050441c549242c3c80301e48903900884106c1400d9036030701010340b43c51080b40b40203501500b003000701c41c1c1d074251408074142d2a40d802030030b6081140610b4070340307606140d84c4d40c1220030704090005a00354021301c01d00580c07082440860151904094800d005c41689100f160b1410a05c007040000031102e568482c50392811a801130070921421320710400c420349a40c024003a03911401701c4000b14075007407031250f06054107840310109180d026900304180d40301318510060482017140304d5091250084904140000d8003500c0400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 687415071 1250 687413821 687413827
    0xe0a030f03060e04140f0d05090319020904020904150504082206020303150303070515040317010f05210a1425050103020a0908030a0806122a0d0f08 65
    0x1240003418100d02903000410981489400e03c51859034001c4140c2095201d802c80c0703006480200743c1c0b414034205460300c4c1881c2c01408959034074940c0010042800e40012020b55540c01c0c143c03810043c03603c001c1c42010f03401c0300c51600050014208250703e1034200d070203001680c03080c440c840708801c281c91003110102c480d540081242c501e03074400d5800c001e556a445c2400316110609110000390307607010007060041e04a103100402d00094070180111210550018280c8a0001800c3c0740f03c103803940141c908a00040c1e19501c42c50b034070700304a205c290580c0c40f05130010700d805180108000001c1d49003505400091092100311103903d40030072100c2e10140c8a1a903901d078a01711030f001c1500f0054003030b030060011250300e01c0e46101c4d14407400d002d10036100c090800580b01c01c1e01e407000300d40404403a0015846488001210345207644c002c40c02c54425403080703850362114075003d240c4a441d03088800c0c2a02d51782c2c80c1880421301105004000c6454200f0113010b080e0b0043c3c10f900d800b82e80ea0151a001e5603044e07000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 687416321 1250 687415071 687415073
    0x60b0d1205130e090a0618150e0606060a024c050604090305032a070c0801060b1c20040612150e010b0903160905072709090f0203010e0a 60
    0x72100400051507003000c40c0d40f0b98a00304564035100d11001d0f2004144075980d0898040e40b540030014141d12582180b60107240800e170342002c10040c5000040603c00d031140d400050300d5454108121502c210860780030341056266001030f5111260215484000000503d5295142e00002e11901c805003004a01e1036a0a40c8199460301c102c950260005005500b004002004a0b400a003183d070043d980159003a20000d8000ca100c1001039429400e408801c00010038800f0b100c260034000c4144c82d440c90080000d541e0301c800e015000d11401c403c0b00f11651a100c032030b0900000c1f030b602411420b010301c8121004c00701c02c024010030a40c00b40d013155000c1020070f5139144820342c1c2440f83c400400c0030002e0b400a01d03070805c0b20340e520f030450512840180c20380000c6c444d0441d89007800515403020002c80c0c0b5074240ca40315a004005860308480a2001410004200d400c3e89000424000350000c4200101002405c104a0101801009a00b82ca58008894260005803070034860909181e9402000e4500c1d1522 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 687417571 1250 687416321 687416347
    0x607050309191d09010e010221062409040605030d050c010b0f0303040b0a030207060525030c0813020d02060d050402190b030604020d150f09150b07060b0d1205 70
    0x3951428951841c2050090150a507500344405200351111072102c0f141d40c0312060203000d015004000141540003040807455148855080300324021035200c580016941d03442401491500c01d01006802582c0c3c107003d2160381d141400909420001520200b049520f820209240485100c2c00031b00203900050340001d100400e20078070a0320036080b100c640c40e124801e40082c2e9280141d000b40c10003820005003808030135010354115107903194005401c0c42140342c00341c0228038404c0041b902c14180700c0260540c0c45d55500c02d21a40d100f113846901e1326907072911034803540c101130710048030300b2604900c0402c80d080150381c0f644003800030000581000314071850f003031050000f3742941541209121506a00c1407200350140c0082d0790303104200fa0380041e01d076a41414a07001401c08101c100402c040400030200c1d100c6503420080c815a07502001c248101030411500c110208007030f12464001d10028080c12000034801d0700b004101400082030718016079403540319901f000404410000201d000010040b0003648 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 687418821 1250 687417571 687417589
    0x118080a0207120f080c0a0c030807060b0117010306050702031e091507080706090f0206030f070219020d140a150b0a05090c1602060d09240504210504050607050309 72
    0x6500d1540c1068140316510300e841a0130a01004050304004a0548800741c0100641da0940780c1080b105012140d490410786100d6020030401e4644c3e0b418a21100300e194018560031040c0003241c850201d950b03103152075003801001d010f460101140010044240e0310006c42c001d4001303c0200a14440c0e590804004200265042e01d9103c2c00c40541400107002003007803c029280015041140800c900c0000c0c54154500c91900a00960086001c000c0c480000700d110307045071246403281c00311080001c590a0700244041e401e07800941c01105010700400040c03800c1e004500c860504811114005020358412402c00b5a030451165140c2d6078420984e43d0b072500ca1049402404203844011003401d1004520f001441100c80c01c45940c404e1050000c21911041c040382d0317001d066150308201500f410724202c0c03000110541c500001d0000c0c0d40310510304204c83c4c4501c83c0601e0b4000f4041c10540400824484085c2100e680001031000510000030329440da0030040c0700a910450140d41ea6800d0340007000540390b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 687420071 1250 687418821 687418829
    0x160f0c0b130e0610050417070302040e010c0206060a0f03020f03011401061d09070f05090a0503060a0f05010b121902040503060c0301060807021c050f090d03031d0c0906120118080a0207 81
    0x70f40c0051403544c207540040c2142c080c0d501c252040000000c14107081441d080c900d5000a4006140014070780c0b05410640c4182d0190080e90f00740d03005078645100304074001d0558080d240c80303815601c804100528010114202c1d840b0080c0003c91030a04c2450780d40100c1c0026032042c000308905011781c0f001008102e0818059001c100ca80301d245040500c1d0080010302d0b506803810901000185800a603942e0001d400c0003032a005085507618a0080c44100c0900f451b03640032142c0c14204000801c240039a0b0007074035045083c2c07105102030b5680715940c0804203000f510070707890380c158200408581030b103060004922685444032a2540da501d0b2140041090030003c2c415804c40d0031440300c02c8560840d6103010504005a407905548801c1d440103025070502c80c02030351540c480154803d05003050303095085030340c01c054965000e03007024036141c002a482e50000d003041a031000d603003400103000d49880c4400c044a05100000003034507881004092072140891030064584030408100c00211560400100007d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 687421321 1250 687420071 687420079
    0x4061806051c12030e0a150e01180203030306061308030301080a0311031318061824060e150d02071a09010e060a270804090b06160f0c0b130e06 63
    0xa10780c46810301150f103c00344004164a40703000c2126840e080180010301b036080844407903104803a5041d44000c0a2081e155600c41d402c0a20742180c40821402c100035141c2c02030055480c5950b18020000545e004000b0618560614030021030700e140100043c5020300b81040c018502c080302c03401d01414107429021031116603801002240742c40044801c00310121546404101c03480e14171031400402629050b046040295800900408110990340182d042c040301d00c031400180340c0c4802c000980c440018011070001c540140295201828a040051002d1401006560618075426418016030f40311003016600029541003036001c030140aa041d89e04140e00d44002c01c0340b180c0c03032081142c4502000b401c0c10880c580d0342e01c2916180e13072a2466480700203a10140700ca0945581c3c54003041c00e411034002c05551500c3d00240f00c610f4100541110301b4207000c4007581c002c5030b205a03155000708180580481d40c0c00300441d80007030040042c0c40134100c1881c5240b51043c0030343c10003050701c1c0e24260040000c2d1107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 687422571 1250 687421321 687421369
    0x2070302070e090c01080403110a030206100510080712020715020a14031009050910050c0d050a0b011b24061a070308160315030b090c01020a0c050f0406180605 70
    0x2c00300c8005101c88241c00e082c00c0000480d0f07208d003000d4441010071141000280181303503a0b10101940402c1c180d1007600c50502003483c9540720341c14810111240d00c0302c0340104016901040f01c040c001c1101045104428001501e8030740596a0051703502d8502060a07450380e00802e06080164010100140c526080b00a441c11481c104201e40c40320b050600c60000390390350390800b240002400740000c0c1c000f00c1b0102c07418005400e0210f256501984003400041c902e906e0310022980b00022400780c0307030320f00304169518880c5181078400000301004115045420407070b142c20780f80200711500b007900c1c804c00040070300241d1249007804000143c2d4007032841403040c0c1020400140040d80000d0240e4003c0500c440c0c2200011000c02c06a00401c80d0034038842d040203607a4800410011280c00a500c0340202c6000d590108080708010780c3d4400e5192402881244811424452400c040c0400051044010320108020b56540c165200c08480c00840903d0b1917120030090003641084001e0280801c00700c041444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 687423821 1250 687422571 687422581
    0x90915010f0f030f060f030506070c020108010e0612010e03040501090b0c03030f19060b0a090501020f0d081f030501090203060c030415020d0621030206060a06050403110402190302070302070e 84
    0x441c10501460003418004690650260144a940f100c180b0400b0580f00300107031500c840345e4200300c1e0040d00c41240d0307130711400e00000c0095208400005d0050b50685882c0840d07400d00c0300201807494010007003170304184040c0544003240e0090090740104c0c203a460146aa544c00c03c800100b009a1603086a49002000c01038400404000011a81c0c095104400c1030065140c25aa01080e08016150001280d050010100d00700032483c0c0140902912500e030004600d60302e0005907201d60500f5607000760741d040120f150220700d02130018a6885600c52501c5200e081d01d0942c2c3c030380d54031020380050b51145c0d07442d0414000c6007420000341d030b0815241c80d171041c11f5141580d00d8080d8298045c064143c4540c003c07546407c083d03029000782c4042c10745072182000010b02d0720403841240d81d001a00350f0040c451070b00070590500305000d1081c140c031050303a50146014115114400302c050071001e09500694200303c1c05908807100880c40c42450701a54015a45000a0a000341341c607025810443c15400000b080c05 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 687425071 1250 687423821 687423827
    0x16050d170a0902010302040e040302030d060512150a2c10020c071503060905010b0d050106053c120123010f1101200913050412110304080a0809091501 66
    0x360300109255001c90501e60b0703440120b02078040ca62108400c26544810301c4101500840034110030700100f0b60400115503a007080144403140301882040da600301c0c6008082c000300d5075110550081c608034010501121030344030466200c40c84818001104117000c41644d03a01414011165004444902941001703001061603840305031a214030a00c16140004805049000c0d4010310700402c4850b20400072982d4402219020380c0c4409903441c451742c545070020851071702440c00d440700c50400d490320310031005d401140035241c003180c07810542c0c00c280b41c1c411403020a20a100182181000141d060805514041c040f1034842e0000c0007595071a00841903404c05030b640000c01903801c01c81072414801100c503804030240103100403030300030003400e10164401014162140042c10380740000d8450310000e2181e00050003c0f03801c1910001c1c01310480002c80d40300300e03104145040c0400000c2041c0ca00d4156034892051802c111840708441d02c0501060202d03007403800310100d41d40300741c5116848900c0d0301020002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 687426321 1250 687425071 687425117
    0x6030b090c0f13061a0c0d0815010c05030c010e010209010909140406050a180602040617040c1a12090604020f0306060a09020d060b1b0c010c2111010216050d 69
    0x18007030038000c60f0000c82c02c2e00d281c2040c802413541c10108903812921402c208900d42c4a590950700c948a030400720300915200d900100e10450441c0380079401000e00c0b40045614511212056560384800d0240c4c2c10b8440c1c0030f03c21800c0c000604800160340394002c50024081071029441801560f1400385540035500c0c0807001598440c0c1e0200700040e9554400c040d03032000f8601442c00507282040300041000304482540103201b83c030119201d048641000d0040780c04900400c6800411001640204102014016041e40c500300301480c2114100b40c0f0703984a031000400f0884080c00c80358881c00a0009600703215002d1004540b0590103000783d481d0440c04207460609a00c40c0309030302940001e03200159460350388148080c2540c082465a201209404985c0546d8000910039141c055013141d94410360082001c0d8021560201070740d40c00b43c0c0d9209040d01da4001c0c0c4410710060046401d849100820203100501504e52101c4a110902499091040c94a4698800d90040c05000c0350210441800a0701c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 687427571 1250 687426321 687426349
    0x50606010e0604030b040f06060807050307120807021504090b0a150c021f02010906050723090f130c0f02062e030b0712050c160b072106030b090c 64
    0x1c0c0c10320020100102e040c911482c0c1c0b024001036455000d000404c94008403d9007410301445003841029110b40d02c041c1c0b030721424480d40354568040841000101000b400c8080a680100d0410341001c1044d00855004e055112a1200703580300018103100d0601c9502c00e58482031030645020988604100225405160480d00301c0d090103e070100b201c04541ea80c6e201088180c0302803020b4011780b005044d0103806040c0044080380c030170f414840003810b510701c941c1c10200111081e07842420f40d00e900000c0d030f996a502460b503050300031281c0c0c00c500c2c0b12a10741548569011181010000703501d092900c0050030000e150012800315004401800020444904048030074040301429220841d800454441e0300a00c0f07500052408001e10b041100d150380203603003d4004d0446d51418020341e661095001810b01c180e811504035040b00c59694008600c0d084e0103140e105010f800e05a10308014181c0500108d444842c0c0b0990668680c4400c3c000c1100302030003207400c0641340b801031164154941c0054060180244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 687428821 1250 687427571 687427577
    0x70b0702062d07020102060a0e07260601030804090c0e0906100507050a1101180303090b0d090f11010311133b1803070b1803040b030108060402010e03060405060601 72
    0x5040041c526551a900c44901e12070a440d20408010416020301600298004da0150040c44001452a2094001d40540040c00005055107508003810b01300204182c207403030788081442008c040b41e0300008000c0300780654003d440c8952101d10f410300040a850440360444100464103181c911903072221b02c1e6140d0425011100d001d203000c4a068204c030b2901039008054528802c005141041c403500c043c0d80351683c071083e030b0341c804540c05000c2e141d2903d403100c0c80018005844400300300301c10800320003d0951403440c503401050f1040d0326103c0900c03a24010805440e4100d8512075000e8640c0c240c4a610b001d520389040d540c1c240180a12041e0722502d85110303e802011014404021040e12205c8022102e410712148000c1c90010519120700d2504c01c03aa030f1003110010909425030b400c0700005440c021540405140c04030359600684112003d401054110148001d0001207050304003807001e0b50281c025a0300900e003510b00341c0001003c1400300c0740014025000350040c040862404a40181c0c4501e00382 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 687430071 1250 687428821 687428827
    0xa05011202070204050c0d05010614071b050612070908070303021207020103020f0403110405150609010e0a080a0506160903030507060b0f0d05060f060306091e0a060e1c02070b070206 80
    0x34404040d11a820000350701500d44810031040c1c0b03d8100181c010710030208410442681c035a002592407950f40c01c0c0c403516144041c029940010b00c038011031840300c2600e2042c800300695070350210b20075030402d0390344601141002c0e04001c02141e101590800901140006020715403440c2c07800b07510b40b115803c84220340d1000044d081e082d640283c040b00c50045140d1401582c07240c0d40d082c038148444600042503c194100780200c0d0721020804c24070001044010500c85c68008100b0064035032a40740c40324140c0000c484400058446824014400201d002c1c201900d42482d01400603114040780071900d00c144401c8440c02c0c80400c1d03200d0142c8000580c01003000414030102000100503000d1b607802540c0c040d2015426100300710021602c87d0041e04911700f000350f903850390420143c4940003180c04600750340c00342072444c2c2c0a8095070b0045400d06680400d0380c821640075209e500c10380300d0070302c0448030300c2d4098454a692100384281601d01c0e4001c52024024013810030145420340e200b6660041d11a038404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 687431321 1250 687430071 687430097
    0x60f0e1612061805031e0702090f18011128210b031207150b09281a011103120f04060f06060f030f05061f02031b15070e0a0501 56
    0x250b2201d043c1c00c0790300300c4001c01c1681074600f07199242d010000030344085404a540700c81c0329140c0015a104194003c140548030340d6404104028801c00521040400c1e882091101400d0300030b01c6031400d150300d050299542c0c2c00d12034a40e507141000d20400640d14801c5500d10800d1140e2201118001c401841d401342d003540e1700754503ca00605141441c1c036505000341da030410b01940300c0030014110913100d920f0703042070541e410703c0380310440c0d03079030756055412100c3d40000643e101c0d1561400058680c0d00c80c01a16001d4549003010b040b21a0240e04590a2245100300030082d030b000391030842a541518025450803c0b040345080e000c2c10040d1000d00c2240340100030030104503041d0440b071407002111000304142c2c1c0c0d030340038014405101144c1e0300c804240f405811110120490040da403003254090110b00010703010b03244410040ca1002240421030005014110407011249441c150b01c2c0f55810080070302130407044007000701200c0541610240021250206025283e080a88048542c2402c01401d401c0403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 687432571 1250 687431321 687431333
    0x503060d023003130501030e340e090f0a0f11060d050709050907030b0603010b0708070b0703200307210e07060804060c02120d15090504060f0e1612 65
    0x4980c040390340000d228001c42c4408500000980512200c0d040b022080e80e945800560480d203101c074039842d03582c002034040c81040b11003490705207501c0600140307042900885821080c40380c03056007101c0810704440c0d0900502310070400c00700310400c44000160203280d41c103680d11626180f00020060440d150343d581414942d40c0c900695881fa4440354003403009140c1004002c1c40040b240c01164407421220f40030906c4240320b071140451005010b08020314503404c200e504101c54001240498a104042020b88006200000042e000307417002d032004103581d003100b0702407038070345904580850f170500c42841001807641d404811001c1400401c1c01c42c8030b441c4980d040d1640982880b00c25035130320f071207511b0000841343e50266805126500400301000200c01c08241240c6a500d803040d04101940d0030320400da480000ba9000400b130b0700b90a8208400c196488010310705613402120b090710000d940740740c00c44e00d41074140103e003a00031442d4050130711440400085126042035004000740303682e4005480c3c3c00c00c44 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 687433821 1250 687432571 687432619
    0x12703090e07020105090d020316140a120908010c0e06040603020a1202040f1406070b0c0f1c09061503020604060e042703020d08010e0402010c05101d0d0503060d02 72
    0x180000c41e80001c1c607241c00080d000e00800d4540051380d20840703121400441c400300540e00c4480e08015100d04100313840e02e43c100c510201042120341801107c1032034002130800216651035843d07940340d03c003d0700c5c90100d010342107a0480e00000184038072031400840c0356580e034048405407452810016210b9004120451700ca22400307903024041303480050b0210304800c0e92440e140495948003d0951414840000d00682c1d00038281e0080c803450303900d0003040d04118504013514103009600c500034180080c010030b0104c03841c4200c1740610074565030107140c1d05100325402008608100c9410b01c1c0917140c6542d012403900d00c5a0b100c0caa0400032408420417480d900c83d0030814461014604030041000f41030203c0501c0314103650b0460248c071400d04001c902c640242881c038103c50740700040308055510740c1c005550082d044001107500c0e00941c0c03402100c1c40100e01c102d1009a9546904034201450368000c50324007240024050305010702031003000002d03612224042e07091036040c0d6003c0740c011400703008a01801 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 687435071 1250 687433821 687433829
    0x212120c0912010203150411120408072901050102030903061506130801270f1707050d0306180b061605010b0d06050a0b0d020603070f1116090c0201270309 68
    0x84036101080b0051405401540c05449410104d2090382c04800400003104e0001042240d44c0c0c4050000080f03800072840441e61050207051032074504115030f03440c0103000b280c0f49603400460980014000c2501440400507024120a000444c60f06031210700007541c0c1d02d001404000040403200600c01541c54560642d5003030107040c80041d010b10344505a0750301030960505161244010100c95400c01410489582203880d00710f900c180300e007155901c4e580d4003d03004660313641e40e9510400c991000600e0400c28042c812030340d5a0300081d600c1c1030043c07409031004100b104005160608856039007079070b035a004a03480e540c10702c0c1328215803a00038039019000d8200030882c10303070250709205848184462307074001c03920a1341103100400002108400f0812080d180c0180079400c0a018400103468030f004034684950f0000900380070070304010b0300b0f61151074903c0820b51310340800850442004080018000c00c2d01b01100f40c0000c1c4942c0368400c032000140798035107240d1448450003510f07100c14580a0358055000e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 687436321 1250 687435071 687435079
    0xf150a05030f010b09060a030b0a0509011e200406092d03080403110d0b0601180f0b040320011e031803050309190b0705090f0901030b160212120c09 65
    0x10508201d2030743d00a00d060050940142010b900180c1c10f0300d08210301d5400c2d240d10000014040c0c440201d142300074035005040c401c040d96a1030070240b5407102c0c42c0b80c044001c030892601062683e15048090701c0240c484007840803400c0c081c0803d100c3d03290807180c0442a00e10481e5400c0c0590351804404641c0c01c01002c0d80c00c441860350502109100aa40040080d01d006440181d5580104014407c90000700c450203410014190046096580f2940d04550141c1c8215007401c44140c40c0c200d54880c5407095400002d02810000d020420000003030010031810103d60314000d264001709001903c003403200c6064604c090851207181d600c45009500400380c0c48940810b801c500c900340c0c58090616481500d41d00c480f0f1007a0003070041c40c0c030040010303400d0300351740161200b0907030705c0c2c05e41e041d40c850300424101035105000380744040c0c0d60340351410624021802403107003240303c1c1070154003c500c5c070352200c4090045400030000341c00700403480f20031641c0428401024817150781d01d0074103903801405401081540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 687437571 1250 687436321 687436333
    0x1106030103031701151d0f030d11120702030705062805040603141306111b03030a060f0e24030102181e13020705070803160302010606080f150a0503 65
    0x42c50342c0100943e80c088254110803180341d884000700d105a2401404030310010b80c02602c070b802100c60103079a14416100240203690b8600c00700c0d00017402d01c08042d5a40b4000782094000c0e118424003000b90001803d00100018503099013500031a07118069406090300407800000c07612116200152294050611100801948028080d00415590140c03040074002401d00380d240500382070604400e8000c1900b42d19642c9400800d9603001d0142822a18048071200306000c1c000001d4445491110700e8080d203405555207140c40070220040b01c00d5608443d0203200b00030010f00881441c4a061904010030044805c800b0707103546103200c840f800c03409509405500110310300c107284201d0044800e840c0e0088500c20362031a07090041c0c800c84100e00306215801a540c130030389034440089a00801d10035009400b0b441145440e0143d5030715640c09040c2c1c505c0c01000245050b4140b41e82032180b40d000d007130302d490b02c010380c0d0a09410000320240c02a0180d1001f4401300708a0f2195610050b50000400f8003506840d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 687438821 1250 687437571 687437573
    0x1a130203030d0c020c040203011811040902040605040f271a1012110307020a020607080708130e0127020d1e020a030b030a0305160f06050406050712050907050d1106030103 75
    0x20290540c150f5a0000d4452461683c15510305402501e040e1503111802d1390070280c0108200001d0517880329017120000701044007103010070031030004001821090301c42507a02d51601d1004118140c15a00c0684914045007407400802c1400d15400b0003070342c010300d000c00d40c000000d806500d00506903580301e81c000b00031b03a502415075420400c11006204007000c208402071910303411055920040300c01900507000040709400525080b00070348000c07405031109034104552a50381801d40d03800328150b051020206c10080102070305100505004d0142d030500c4030000c4030406028811540486540c41c0260b03008641c0310f607250410342c0070030048502555440a0000714225000003944200541c0001904081d105042c90800146c0442d020781d00d030369803915210300b44407004150111204211240e0410340ea0000120740c4600400c3c0c02580160000251030070800341c050003003800302941660090420003003000006000c200c003421030301c0036185160741042c0c40c03410884010150728140d50080c40440080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 687440071 1250 687438821 687438847
    0x33030615030603050c040903020d11070e01060305010819170c01181110110c10050408010603291017070503100b040606050f0301090b0a051e1009031a13020303 70
    0x2d03048a009070184c0b1040c0c01442c040c042a0343d0034400140260f806080313840c901c03a00c030b264418000301c0d08800382e40c02d90b13032606000204881e0a03030080c00000c1e02c5d0345c010b0010600501c4000c040079441d008035402c01c030103603413506000041c01c1ca0762280d0b85400300d00d107640341a0a4100034601c040a04e200140700001c2c2c0ba000c20140207091060380100b48810b50309240601032800e60700302d090290010440c01d00040108900f00c0c10781c140501c100f00c024171000030200c000340201005103205540c001d02d10160907003191451410b651a185106d000c1d10144011048802d0741c02055950402001216500740c6010a20b003c0e2594001605803160304c440b00d801c290f81c0d600c00342c1403007400c8806001751a03075070302c08a0b9a070098890090a402040004001120082d80604d000c90405023405c480345a41d00c00282d281e00d14909a550100311400494495141414200e07881c03500c41d050414040e403c40c1c40390307100881c060003400d5407500c0b0807011075000705809003180c3e54180d00808a1b80c2d05c4484400300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 687441321 1250 687440071 687440081
    0x12070201061823090309030f0703200d0f0303020c2e050606030f0406140a02070606060305090c04230405030703080603060708041e150c08013303061503 67
    0x142004441e4407207400c4490507036025806080003c000a440b4032000d040019422034800340c0a00c01a10080041003160703141400351005000c04d07000038000292031801c1005040c500e41010030280c00b4000005480d075650fa804030701c19103070825540c015480c201e203001c0c2c2c001e210b800c02c0320481b40704000c801458015502e84200702c0c0c0c00210b4a03945008188000c46064a030280c9420781d02442c18800140075060f0780303940b2030f40075000351000715507425280d10f4003028031015203580859a4000620700144001801620010705461030100000d00d486080292100740380d140440c460703a22440e000e05240404400c141d08040f62801c10700050402d0310307005990b6400403c00f1008207107104001111850041001481240142c40710b00c0d150f80c0d25070f600c01164507240418000100f0740c0300380d130000c80c40006132180c42060103400040c800700030101c0a018048141d20401703001d601300a80e14907161503034480711049100440520f2400d4461402a03025007641d0f04680500403181240440496140e084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 687442571 1250 687441321 687441329
    0x7020a03080d021c020403030203071509020603040308060f0d08160c1e1508042103020c0d08180604021807200c010f030203100b0a0c0203030d0911010206012304021207020106 77
    0x1000e13501d08110f0100034240d004500c00a00581c01c14081e02004c00d095120400c6100c40c00070b800141001c0f55070020f011504191810750004200b81c0422131503003040c21042d00c0260b0115015020000b565503800705078440c1e20403150000314003d0600d42044005005007011340019040249000e0000c0d02d25081c41d003c2c1d02c0b0b40c5000b02c04000590200600038040f05029a42081140d001600031400d40071003071044070384680426500304401d0103192009d100b0306680c10466a2503801c1401e0000d140c0714518001001007146030002001d00c00169100300e0480d5188680340b5084c1225a5120803d40d2071207946860180c2c240c0d80d000201e1004e82012604011840090329034150754054544e0440803800111002003d031110348505008452002000d07001640c6d6900d89101c6d04951640401e041d900308000010055448159880c2000711f012010b800082c82840100380179890483c060b0484100f4002c3c2d2900c400404651203225100d07901114804982902c0404042c140840000d00800342481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 687443821 1250 687442571 687442597
    0x10311030f0a0b061f120b131a1f0203030a0b120a0303020301090510032319050a11150315030a0b01061805040c050406080604020d061d1e070507020a03080d02 70
    0x12031100400040c0d42e161751110402d550b01c003080c0c25150920801842101d0f05180c0c401040100500d07040d40c1e9000307400400032006480207600310940140504c01c103c1044403440311004080804441341d0004c1665030000240c00e003c01c00e024054041208048207507000c582d00c0c09401100740605805400541c126481444100102d50341d100403201500018040189041205240c0860100c4460010342c0090301b00002d48148940f06451860307a1850312008444541182c88203106200d01c180e010054400107a5400d07007a00e420496500c44d0b484000d004480e0000014001d81c41c0d07032010002326151590021845411b546c44040141010710032005107030325001040c002144134100b0b400b0b200c944131561784900c0d08260800e030007900c0c0382e24003c10450b08141d0034032130344101c0540c07802a480102011000001e44000c1c000b076a0812181c010100c000c010079451540414080d107c90084d0300c00310524006413100a6440050100c403410390014080d648086000b02e40386000303138010130801040704 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 687445071 1250 687443821 687443839
    0x1021e130e0c1206031b040e070810060305010e0303060f0603040c091508010c0905031f0908040f0509150a05060a1b0b06100309050c0405090f0a0b01050109080c0306010311030f0a0b06 81
    0x4c0c00305955841c02445004500c00211044450b40c02d16820007100050140d0607580c4480d10b65003424540007071205502c0c0101d813585420070900c0f000784141c424a54210300614618a0806c0c0030075070740411001c400c1c0c05034000200103824060400c400d0009018410001c1c00140820144200000401e00805446510340300041e5070700c9004400e82000c450300a005400e2015001011510b058a03840388041c090340c0b502c0c801c80c0014218401000030388140d02d4a42c41160504040c0159140010018801012204541495a40da25414104079001160480d03076911003100201c40c00c0d9040298851090320602d000d07401c01400c4402c45101d03000c2a12060342c0c050a501c03003203041d922482c40c0500560003000f00b915075400d09800155112000c502211010307622078483d18a8414110b80554840d10150018001581e008407031500801d00c050013407454079a21000030f03440c0c0006110041040c5080513a400c92610b0030f00420340c504000c0029100d00c11240d0410700400e2008803902d49c030402c1e01d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 687446321 1250 687445071 687445081
    0x906090507080f070302031315020301060908121206040f0f0b0102101a090402150408030c0d0c08032404020c03040515030420040207140c100201021e130e0c12 70
    0xa000308511601c0d60364907552507504e4041003074000703500c0548401208a600342c40440071609011184024101001c001a41ca42c0351150003807210b855030708408030381e4000780da48030340e440008410f4640a60b6070b110040c203e601d0b400d00250081181d564500b1040b4104a171982e42c1d00040e901480740441c0c282c0a0b20301c4c072099044007104482d0708003003230003002046542000712820100c82c5503510502c041d00303601c041d004400d41d03004c454110740e1100c0480e900001e90302010030360a0106240c1701446082101e40d680f07895942000ca808000d18080c2c1c80c44c140b6004003000c04008412003503480c0050021543d4810140f0740c00d85035801802018060b02a000c10200520108007c0342d200f1174200c44c00c202c1003030080a04503104202040d0207540315401b803042c00302090703104c609030706c0c0d02d498100141029005176017480401d4580e01042030959106100c040d42009c4561004c1070740c0044650f42a580310035030000009020425004a110030011b0010800d010058800a0096815048442d00c0307a2361a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 687447571 1250 687446321 687446327
    0x7020f010e012f01090c090e06040b0103080c0a1e030206060d05030f0315100e120d0806012d030204060809160905061804030f120501080601060c0206070803010906090507 75
    0x14828102c0c00030f12100189484402002900381c000464541011003e81c0c045400303500391401e8541c184d5001d49003050400811403d842960111100d00000d030450380f83c0b5444250b00d400c014400501a040006641899201d05000c1071403429803106c0c6103c4890511054200c6200b40802c080b400b5115080c04601c1c2440d040c000c1516103030f8040c0c01140341a059580441c240d400103015803012160481d00e9006a0f030b0b400c0811040c9054a50301c2c2e901c0b02019000300854010f6441190545400c00c2d501000c0c200d0740b12200d184d0004083c00d26080840700e0603009812403000144410b40e82803444400036451758513400400c201d80d000c0da42c001ca9a01c40100070f585178018244d040c030313841c1405c0c0810001d00d05980c001aa102c00014104040811140c1000403081d07030442d0101e0000341c06000300c41c80c02d030b0000440400c90078818000c0051b50b052180070f0f65225410300420003841000340080c0c0441d40c03454105d840c03040d0302c00801038980d40e44280340d001074005400f03202401414240081c2c48c01744 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 687448821 1250 687447571 687447587
    0xe0f03030a1d030a030b030a1e0b0a0203070c03081306110c0c03030f0d0c0c08211807120c2304180506070305060303040803041202030609010b010c03030225060207020f01 75
    0x4031000654a0680e0307104c8182c0c002c180401c1d549815004a2000c0c2d000300b50700e0741100c202001e0100344580140d4003454004c000a04c02840c1030002481803091164150344035842645140c3d05040215403038840261003040c006880307100511850500c8aa91803120742c08001c0c02c072140d4214201c1d00d01c074a8031420151a401801180c001c02c000c1070000f1000007895800012480d80542040c5a401110b5240c1d600f499014486c140c0d03440308042d20700b420486480c0d480c903a0003d50824468240240740d01c00c280c549807240f09032404a5a0b00c05036806000e40c100411008121554000c503c4500c91a51400c0b481d01011075a0700ca14038102e950302c600b5951190041c942070340070016201c103a03161581640104006449540c052100380030100c0c04041c100000c10282c20481c0e920b034488a00c5204044c60550000e0410900c0d90520340c0c0f801850760401341c1c650805502d820090380b42d6450310b04101d401030590181c003500c40040a4040d09000855009002060080d501080400e4a000042d07036124 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 687450071 1250 687448821 687448871
    0x7050f01140d051b0d0902030d0815011d120d17070f1805030712020a080a03140f070b070c05010c080709062105071e0f020d0807030e0f03030a 63
    0x850400c19044103052592100313511022020001810310154101c560b20398000419294169540389a000305501d0108500a0310305e00390714020800303290100c0c8401020806000c3d40b0306101c04401046181c0c0d56030810400c004001a001020794418280c03501c0d503401e40c0b01d15000100302e080074107172612506207021902c40d58403500c80130443c0b0300d0321200300c07100c1c3c040700e03000d090b040f902c2c50010800c3c0e5401d00c00d0300010203030020056000040c40c01004140c482a900905156020f0b00b401d0002941090310344154910a603610f03a29401e9500a2010502c1485001840c48940c0c0041080e925000700f83d41c081c0034060710013080803455250f03085d2240f1303109035020b0000c0351440c04d00f00a4035105041d0b44040c00c007084201089980c0b0140e0b40010307120700740c52040119a5078920501920b01600150010040ca40340c40445c1c0110313054003a45036081c14591801300841f9a0004030020301030b80041842040c1c1d04111074140b001d2421030f41c2c607a04143c440312031050030038441c1c86584d281960703070b50f5620f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 687451321 1250 687450071 687450107
    0x21c02030a0308060609210705270c0706090807060f2a02070b0d0c140f03062b060b030d0201110d0e0c0607120f0c151d0a0507050f01 59
    0x72410342d107042e1100c0b0b9000f420542d0240d400c010b5078045469200d06401040101c42ca04825400e090301c080f410201a41c011302d008483c815002c0320f10030f00c4810442180d07548200004c096484158000e0b06910a03104060680ca080400b07404c20040350b80000d000781c070b00038901041480d01c0d82d0022001c2e1200301d114025504448074080b111070000c00c00c4801c500983c0c1c01110ba10701da60340751007405030304807141041001c0e950b40014048a40c0004051040c2c2d511041c1c1039140c00340c10360800813a404003409850203018070b041e89411800c0481c10640060400b000180070080c25441d00b1409000c000c0070150090090707100d00100c0398014060148200d460241160402c0000032140000f840702802c440e54900ca1004814225103d54000f06615400392060301c80304115020080c00c5541c1c00d9801408001c00040002c006c102c82c1c44030a81045811030000c5521903040c040142d96800003a0301074124003414141c4000c21200068100c101d03001500c040b455258400c0042d41d05805410750360402d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 687452571 1250 687451321 687451333
    0xc2503081e06031b060d0e1501060302030103080d0e100f0203100f12060504110907080106090b2502011205100503070f0e070522061d03010c0504051c0206030c07021c0203 75
    0x800440c400301c0d4041d250080e015074107041e44030203420103550b0342520f400b1140d00203c0601048d2040342c9a914090106401d00b58615451a51400c00c035126102e42401d82d2944c60b00c0a80c0140c0c0c0500c420b00304404411810f000d1030380300c40c90040081d40b084d0b80c0b107594202031100008510b03082004583c200c500244407140702d0811502c484000d040020421a0500d40345074020500741d0301c0c0c001103070291206039104100d17981001005804500f154000c07204580d414000e500100c3c0784403090800403001184208410034551006075080b07280080382300081c83c140030070000108810a0780360200d590444c00c039400c455403610708290210301c50083d6074041e000c403030000301007074041d60050460f80813452100a01c10b000900c21282900c0382d410800c000b849000096240389a03071056640b2030386048008105590a2840140c4140301d00e10a550050075141405510b10038030f10200c42e500b0f9000b074200c2d590f80c84c2101107051150b000746001c9100b40200200c52240400104000e1102d83d03019008000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 687453821 1250 687452571 687452593
    0xa0c0905071b170a03061d093007210e0a0906140415170c010f021b1e032b02033a0e0a030311120c2503081e0603 50
    0x103032907116180340b01c03d02d91942c40001e840046503a03458402150000c21f485135040c44090682030600c580c3c80b41a0107105110032410411014041c8050040da81a12660707400c40e61406840d8103a05004c40700d081400110f148802a8024824024044c42210214080c5880342240b00899907180943c40401400450388041402d09a20101c684450b20318041845507403503402400c2c0b0141905420100c3e00306103000046541c00082c3c00d0000c294034000b520703e000b0191038000c60f42c45100a098890210003c007450150b003015013084010801405451414000c0350031105039045580f0780e505111051a0b1700a291407001c010340702003030320481c0c6065442100314011801108417011401ca1040da84e240160f00d05110b114480a00c02d0325009800102118240a0102c03140c41821503102e400c204000d140c0c01000450a95015440058a61711280c0e81060303100d400b010001000850328203414a0000d0541001540340704a6104050b6222104680c102200038002500c040340c06030701100c4440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 687455071 1250 687453821 687453863
    0x6060301151505070209040f0b0c1603030506041803090f081f0e0c270a02160308040f0203150f010803070c05040c23070302010b0607020a060c050a0c0905071b 70
    0x5002d4803001d160841c14030703006400240e0110026602120b54102c069200c504004000c40405d80c03044a5290740f83c14204d4590941c124400403140003070405903140c000582554035a8003088a22011601041a1410724907020304410070b41d014070420b07084041e400041080d00029188010015000683c84040208145901410f2844088951402029881c1c440350715816005130500d8001d14464254141c0d240440da178800c00549108031036401005124041541018542c80c120f504d4036000301c0740e0b0b545040041c1c1c4500b0001009600d8002e1403a004032007240380d0059405a001051750b6105642d890f07a01c161381e4829120000c028298a8204002170702d03040d4454048420070b4203281e54020a101d600001052540344220240c04010600740f05142d4240308409030654142c0384a481c0000b80d07000240200c005110f42010000032008003000c101c1c061060b81c030030300ea2180780da0550b41d03111010300000d00030449001c00000c03040b01c1d8840b8404c6403944000003690300400050312041c26580c0d14 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 687456321 1250 687455071 687455099
    0xb0405061c03022b030e1c0e0409020a0b0a0f0f08131103070611010b0316030f1a070201090209070e0a061202041212020d0503010b0a0309110910080606030115 70
    0x10b40560041e04080c0c2150007410101e6100d0301070300481c80f5081291144080d046a1a6402d803030180d5215412880f15104e031200c0e9060015000e0420301e05001703440c000207028014900000750030882c44a00015501000c801401503119241c6640302d07813200e00303d004c8824407040c2040c01c00280340c440c0415003019000c0071881d03110b4090251600e4540c1000c1c0824074101e129408000068006094029541000c3c840c4500d0040118068400300d40000301c1b21002080c14080a005100f1800c07249041000700e00c82032201c4890002c003030b40c01c1d00c1c040c0c0c0c01034000c041041d4168090720100000540484c809c1c40c3c44010508010989070550341094802c484140c4200005100d0550070000031580c0c2610a204507855803041c1461800b9903c2401c0081c00e0110f4900403909111080c0018001e00300030905403840310982d03150000301c010440c180058078215001941e40c2041800c2d05112107455030841d1841034913480b4003250b0881d1500402e25080381c61010f001c251a4020030382c248400c0d87c100101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 687457571 1250 687456321 687456323
    0x108160e09250c0203061b09060c072606060f1008062407060c0503040206040314030d1406030f0d020a02010c11060c03190c0f060506040906020a02070503010b0405061c 74
    0x10240354041c481200b80111901e00c071018080f880103100c001c218502007149030341c00210b03400390780280c1c00318004080360707801101c280c24419403020445107500d0104003c01d500800d00d046040e4400e0f040c1e44019020401d0008143c4418000d02d0001140b509210303079404905280504607040b00700e08000c084a4550703001c0c00143d40720340d01080011100e14188d40c0c0303400c40b445080340c5c40e0383d40305030346400001c580710b44080f041444014010803007d0f03070310b0505940c11260441c08208141e9040d0355054154815000100100c528004101c81c10083d40300715a482034000703804a0f00c03010407074a40e06650303200070801c0c50010703809030240000652241746030507901d034030804000488002500006000307030803041c0d0b5840143e00c08208c40f030041e20000c204c032285541504010070541c41c1c548803282d1016802901030701054a80010074032944481d4480d2007941c0e0020781c01c43d2a0811020004c6d04c6003c0340c401c1c54032075801c1c5011040c09103814030503140500ca005003c400c0040d480e01000b2049100307400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 687458821 1250 687457571 687457591
    0x80106030b12030a0215090606030601060c050705040501060f020c09060a090c03020d05040b04120504030b010e0c090315060f1f08090a0606090c1b0506281404020108160e09 76
    0x102d0040d1080000e40120a02c6402501c45080072100310040c9a1005002d010b4541c440018031040703450104140c0e05507241440c255007950007604059252085640c496500b0616003800010001d40c40354a03600703044001d50035035041c2894441080250a030a480d0903602885240c3e0400018099910030400400c80303007405420211110000ca08945044030156850700080301004100080520b10703c090200c5410102d0038241151215100000140680c442c040c0313180e001320344191190016240c034910000e0803603807240b110304441c00581318182d4400d4040e00c09010000742d03603d026100006801100007000c40700306568031040b2142e56028041c5602405541c0115021880d203001cae64010704412880821001d001318402804890310992010aa0384060040f1002410200d1607540280d0710205064416005005480c0c001100c207001100e00c074500310f100131200c0c0500404034404c038000d0b00c4958599640442e10444943c00c4c0720140001070903000c1c45401d0b0b1828204c0a0340000c4581 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 687460071 1250 687458821 687458839
    0xd2f01080a0c120b1c060603060606020307030206130c030b07090303020705060a0c0807030e0607050309150f0a03110903070905090d05130312030f020d020c0606010509150c010f1b02010b0907080106030b 89
    0x52a04042400d01c000281ea0147c1c643d907003070091120901815006014a1009521300f180d10b0710020740b10a00507081940441c8604511003c1c400110442c0000d560407100d511400d0034180f03406410300360030380300c100c0141c0200c40f0000b502c0d1800b00c098030858142c0d900e95074000c16450b6511aa0b99000440c04c50901040940b0040181c0300d281c0509000380c41403006641e283c000c58104200040840b8030701d80046002c0040a8404440909460b05000d1a05020071080001044071003140100c0c02c00c95010310544900160801d00ea4000303e01520000c030984295144d03242c0c0844071840780b0700c0c0d005401040828100005098240c00034440030f01441d00050a03904510f402d000e0341e00031209100b08980201d0a540220800d01420b60000024244107103081c403074001082c800c2c0302c00c040c1c161080704042a445001e9000390018142c2c1c002880080003404003003400d55400c02d0318501414015864012010741c0e0741440c4c00018001c000f6601c40c00d0300c40e8603002c0228068018500d00580080c100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 687461321 1250 687460071 687460099
    0xc0c01050412110106060903110a03021002070e0921030c07050102131d010e060d0201020f10060810050f01090903020f0601030b0601031103040804050d2f01080a0c120b 74
    0x80c440c0901035071056280e40c201c1c420880004000c0000030415442e03903450503004121958000800701c00303d80e4440c08450034480780360000b4006805a40c030207034000780181c0144000a0b808034210007640c9855044070000c3d12900600ba50320000c0076003150540c1e01c0f60740d00307082c2400c0302d001a640c011000c405441c40e050081d2340302426a042020214480c0b100c0050612498901d0354410011806981c140030940d0700d0400100307000b110282c500e41c021044040090190391007441042c41104440341180c5c0484203103446140242040d1080c41501e000d01000390002c00c81c58003c8030300811140e1141d401c182d080c4007404000f400070380303400c41c298420000302004040d002c2c82000c1c000c501400300c160b01860400b00250a55818081c401a508000c004200c00114581c0c00c0e901503800559203141e210000d40b82039603460011a03021040c440c59000c030300340d11843c0c00e1490740c01c0c1b0100b83d0310b00440b5110601d07114180e410b1024060040b403280c070220302e003202c0700350300142030b501c001040e0100007400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 687462571 1250 687461321 687461323
    0x2d0a031805030403060f06091509050c09190302120a0b0403031d06100f09061d0a0b0a0e070e100f0c021906050301210c0e150a06080406050106030501080a0303050c0c 73
    0x644d0045410b03544502d030404a0007464890b940050120803400d10207144103426490580d0030500401e00c103282d0b640040380068041c041600c00718040a80842d42c030034011510543c88030744a1000b24410311641d030441c0c400d030f6800b10b101541a90b0210080702d040d10b50f550b05074042e042c10302c0c25030a25900d8500040004404200702d134021300b004005014143d043c20000a18180349411810b041800e2560410444060702902c0800004249100d5102d480d40c404030000b030601c0440c19035004003600f401040d480c901d490104d010b01c140381c40300c10f0703001c600b9401c8c0003002245001c4040403403141c10000b0700441c000c800e20030000d40300628410010120200d400d40c0703205c0c5d981100000036004401408042001c00b80715915800703889103d0011002950b0300a03030041c060080c2202c2406030800f00302c07103c0300d410f41c40c080c80c5001401e058400e500c03400010031100d001c0f41c05641c501d003005d000107041030191042505942b0380c13030080c16205e016514150090032019007034080f4040100220300140300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 687463821 1250 687462571 687462577
    0x40915080f0307380c070b0f0907140f0402040305030a030b150d1d0313050310050c03161103070b04030e1e0f0303070b0f040c0b0906090f04020c0607052d0a03180503 73
    0x3240d5140741c40c3d0f001030a0a0847d200e004100007024210881030008801c0006014000c89910241c1c04d071b06540300741c001c601c07081121007409410500110323001c0100003003c0003400010209a40c10414442458100505443d07090f0f03140b1864101004600900d4804d40c20070740da9500018404004280a0000c80b40745500625001030a2049001c05210314542401080c40403030641d0424030113401c2900014050b40b00182c101c1f50032141040c507c050450251050416803880402540d4807010079041c042c1500b8000c4504070006800c0c421440507610f01a4440d8484034400243e2940f544400004e20a045045010050f8544410f010000000d052680e02c24403d03113441602890794101407400d0b14144080d0f800040605d4001d0120385410380700d00b801d40b004048226601c00f4080c4000e0085002440743c00016000c50041e41e0400907065006801400c0101ca00007490109072a10469000145040001c12500d40703020021010847d110343c0019405010341c1c940040640e2a80c2c1e1500d10b503078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 687465071 1250 687463821 687463831
    0x4120f0203210702152203120608010203060112153008040608130f17040902032e03020315040222140a0c0206070f05040915080f030738 60
    0x60004200f0890365414003002000881c5042d9049050410006801480100d03140003045542181ca060040c1403060703204034000c20700c0180800c01da84c1c549030018080d41c0f08072100c90200701e440c503404500f81c0b80c0340b041c1c3c42c1c2e0fa20880d41c084403060030b200400700d0f610703250b6060301e00d000300c10001d80940c0b034006d01b10701d85c015110b020880c0e42c03145030000182c26940e00034010b4005e420400d00e001c004c585040f47c6883c5030b035800f8808414003100d2240060340c5000d10b401c41c0381002d2001c420891203010103c0007000e4000801d20f55600f450303034101c0718a510203503070100079015000064103c0501d0704019032650002c0c070082c0740b0008115080e50300040f0800300f031500040140c403094000c000403004450a50080404c01c004d20804107540d01c0a941c4510113441e00d001c10031040302c1d80884900c10390903a4090b191044091082c10b5250001d00c40c81007140c0103100c0ea60040c410204407410b0700000300c40420f540b010f070201f016014110920000d60410018541c10303030141c402a181c401c1c8082c043e80c424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 687466321 1250 687465071 687465127
    0x21f0324050405070908120d15120201021203010803040608100b0a0f030509060402100806180c0702031501060c080d0b150714070305100209030109020901082404120f0203 75
    0x1180c907000410099880140c103802c180f000c0150244080000484c400048a070b003811078580e01c0344c1e81c481c560001e1541103940350422024040210b4a40c4810344140e50941c001d90031603c0c3d0300d20144c6c00140c603200a1007624040d074030400c41000142d00560480340d200e00c65540818200d0340c1c0b14011034a642c0103002e900005180100c0074a8031a40620405170440070000003440303546000c0d804640c1e02c0c0f15040c070035001c1c010301c800015002e690700c005441c1c0700070403a40d800c6141e08001c0000803854204050491007401194904050007a6018030903040b40e0303242d035588031001000c2d12505115880806408406130b10340b00d27110819150100d01201c500103250a081d592041802e083c4511000d03011100d1458010404c1000480e500241542c8005280040181e031140c4000000b070043c0011034009421621000001401c1500811042c4143c186900c240c0c3c0c150029a903440e0103541c0417580140494850242800407070312480070307407000f03100c84d0044038a01400c0ea03225150240c82c0448040308 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 687467571 1250 687466321 687466391
    0x18060a11040f080d09120f0f1110031e090b0621191103010903020c01080a02160803071e080a1505030f010b0111030909010909061d010608011503021f03 67
    0x42250311200e017500505040c04240d40541c400e9441c020b40010548020b0b001100c1481d611051042003450642400d80003899107415000c4020050050184000003412030340b024040c48503040d03d03c2c080c0da401c60360700c0b0310740b02541e80e40c420410580c0c183d08100f00206042040e02003d58030310401041004061444101e52805220310f09000b0400715007582e68004c0c0d040110030000070f500010040e54942090070a4946541d86041c0750009000300c40329509090240c1c1e4007007050101203002113026940d1a911a41310103614407416000400080012000030300c000001040385070300398400c40040400c1c808898031281e5a40000f45845440e0b80c0d0307c1c1a1784d644458103050303503030015a55031035100c114010358100746000b40000d203004030504c02d400d4030783c0c2c41e654105c040060550001c041c20060508a00c440c20104001c20300a003c1030046c3c06032586026096215025aa0000384c2100e138020185004e8000c5100018221100d09003910180360701c81880d00031502074210107420111048181c000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 687468821 1250 687467571 687467593
    0x4030309020f150912011e050613050108060c0703051314010f030c0e0f0301090f081b0718020a11030d0905071203050703051e030c1218060a11040f08 66
    0x100076036401400340700c1c0b0f20041103480076a41c01d005075905104101c034041044104400c855024262103c260b60300d8000d020820680c020060f4001c0d800f0b10010744440700b004070744100d06400c0703480071300950006e540004001104408041c0042c00c000c0e129180040c1426540c0c0641f02240c1c040780c014540341b030303054803403500c03156400341d1008100021450240809500c0c0d0701c003d01804c4040c03210900a811030f01102e01e4a48007508940340d610783c402d400c0701c1040f03068101412982c004204546260f6103802c40941c00307000004d81e00f415608442c00c10980c407200ca60401c0004c0d07002400c0031050040e000e00b03400240401744050501c0801e0a80c0101d4440c50f946000c1c0c1c01d000352608070040701c540f00700f4100d010030351000603900c8141d89402c181303550701145200c2100844c0c0c41840350447da20000200980d40103420701402500f0000b803294103803a04e54031401e403448000c141403001c0d9070303006100007640003115400c624000744101001925040d210304a00200741d4660f000740300d0381d80c03050200301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 687470071 1250 687468821 687468829
    0x140c04140405010e1602070b0a0206160305040506060111011803050c160b041a0f030a06030b2d06130f050103050c0114040b13080d1205060f0f040f0902090403030902 73
    0xd110300c212420401c0d07605103a4044d40140000d07107082c1010f4244840601d402e8002c1041d10040d1030b5110b100c84d190381c04001d00079a42c9508a8001c6a1410f2a00c074041e0320b1402400740b80c0c0501c1d80318020b0825513903004011210130040452144a540d02c51015440c1000448102501d10707011395107203a5281465030295241141c03201424003003c696443c10442a0810410340c1e00341c6109481c2944503840002c0c00407224040d07010700c13050110000060190340b680741d5104004880c442c00b0b42c000681c0c0c44c2211011902d5481f005214141580c070301d0b2114000010070001d0340aa4018014040351030020361080446565141c0800351540c2d9000500c1400420001780c200c007442460104607110592003120b030680201d2185402d04440030820f051140c864002c0c45010344100f00403034400c1c1c103007208014018092407609041051034140811143d09008400340c82e04000a05441d2041c030485050000611070680c5021b040b5030354800c1d80c2e0042c3ea0f040c840f28041c034029540410361101c540100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 687471321 1250 687470071 687470099
    0x4060b040302010c0807030e090f090714010e010c03030e01060b030912250c030212160807050f0603040f02060705030406090b160b15060415110307020919140c04 71
    0x1820104400e000c1000143e901c180c094101c5540500d407507860b04554030341650040115285554886030300410030009580241003d442008818101c900566581604001d003c64803500c1d0707070029280c580245440e5000f41410580c10340b080c9000501c05000300b980324211501500086120880041444010142000380c880300c51421084549009a070380240c603001440b149400c561107c0198865041c049a500c5640c01580c0181003500940d04009450f515901e660701021101030510700086130700200000e05e9420b81c0e8000d407001d4886c0030740d442040030300c0e04024011612508451a0754006803112009024114030441c001c603100ca0070241c1c00340180a1071340118107034035414000310110071079002c458482250042c6602c4442d8a420365203003c2d1740b507003604040e0041e0740003c0006041c40c0e501d94541e0025000e0703403a90001d03007800c0c40090300c0f4850008042d50040082c1e000c110107141108006104843d60500007a410004a4880356410812903a400c2e885a01081c2000002c4000740c40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 687472571 1250 687471321 687471329
    0x8030d020d110a081b0c1f0e06041524060504061e0c0809010e10080106020d02070b07060525050d0f020705060a0b030f0316030f0f0909180b070309020406 68
    0x2e65040000c1c0c008020b0266200030040c0200d0b0420703c541d080c20081c041c0440360821102c00950361200440c801d12544100d20300300b41e501d242d06e041121119410003040300382c020303036000d500c6441a054031013090020340b42258500681d4000e26601d04800000042c443c0001d1082d91225a106e51034150007030206a1171049000c04a400300305807001841d0310500c1501410381c40340d0181d40702c500741d00c01203910315003040401382c00a20000f0450000f070340007800316040b1084c1b942140c200c640003090490700c0d06000d108008241c0401d0010800140c940e402c00d40c3c1c04050300b0040720341c8100b0000c1e443c1c00500d0504540e00402c200040305100305445014840d1094492401549800015651240d84910003007900f0f00041d07440750010090b0b90300b8400c40894080c00b5040301d88401d400050f0780f081c401984800c5000c81e22002c00e11800b94016289840c0c0d0140395110199014906140f01018101909200140203450600c000025042100307560046102d6030740000c210003207105000c1161a1a00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 687473821 1250 687472571 687472601
    0x60e0a0509070812070c050613090c030e03180f030307060e0c0103020f120c0906040807050405090c0105220b1210051f0e1206180d030605180403020708030d020d 71
    0x2828000c0715000602d40e1a641d00401540390b0301c46050401b030078481096007101c1d520480c002441000020110905001d451036000708001c10000c00409034106d8a1040c809401ca4006002d4000c201509901c20100c19901602420001700345a0000781140d000039001c50b490380d92035038000c1103d402040b410034120700c01c1c20304601e000c64a082c1007043d0701403e0600300d0320418070390000342c0ca416594251000010054040c40d00c45840d8102a5115501402080d001e54900400903a90010001e10f400c0c4060043e187e2514040c0c010785818541541040c0c01c00e107484c0c50358000075440c6805802030450072020580000d036401c2c84039403600f04c0245030f809203201c1ea102c4c00107106a01050703007400348409174a0501c4000000d40f02d01045240103000c1c02e924060203800100050160700b4050392a82c000010191183d0100301107080d01100c000b03002e03194100d001019004082080d1180043e080340c000e004442a065554085604e1584001d81c031101c4aa0045010800350149024030808107030a91 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 687475071 1250 687473821 687473833
    0x7060504180b0406121109010302010507020d06020403120509010f022e090203032d120105150c07032102030c1c09080a031701170a140102040504060e0a0509 69
    0x14001042030095000e0030548850903120070912035490303802a0301115000c0c1090002c6660780400301081d61070008180ca0107032200e09018118544800300138143c960503107859007482c0642c0c0a204803500d210004480d2039a007040080702245d221000c01c03403405a60359030140d98101d41d0780010320904c030b201c0c200c2c401c1d0b5014400d81c2d01000310855144007030ac1184040d0705d00c000500c816880c00380100d400301942500001508405a0034450152240e0941d400c008103902260440c0410345072080e51900c003e0002d1340401400b80d440c1207880181c003c0304050006040c40c0300424a50300b840c0300da500403180a07211a01e4030409182c412084a030300c640a0020b54240300d1403210268503444a4078002c0d4003102c02c0c1e81d00f1203024ac050303d014805002d0070401c4486801491074090f200c058000ca404680018100c00012124018056407054140c0140600103001407959002100044050003651654082c000410710751114407624004080c4103040c003c003801c08421407021030f4000303807040300550800703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 687476321 1250 687475071 687475079
    0x1b15010906090903140a033b032d070218010f050d0305030f04022d041104320d050a11091b03041b0e0403020708030405030a060e07080303090312010807 67
    0x84840703030041e01e203d01c8a09681b40b124010890080a080d400004010550f000580a1503401400398070103a1625400c00407041181c03185503a02c1c050078103ca43c80e00010003010028040344124001000c0004448500701040390b4002030407602e502c018144a4200040100300d900740801c1940018582503410f40420307007680c0c03002013203480000e05041a140099003c81d0845d102c4c2c400400e540020710b101d034040400c1d44089610024182c081040c885c40c07d03e40c803075460903800b0f4100c1d8100c50411038818001d070b070380c1d40307116443e0380043c004c441200d030408a410010741c494007984520544100701400c7c10300510324104101102c2121001c0c014408901003003141450007803010300200d61018807139180d6455240c0000910b176803541205075150810400100c0411004a16000760300c40e4081d90f00030750301e80c2d41c0300b07550f4046e520505500d079001c0075903c00031070310039840700e5828006070080c0e1b51400c1d00c815425155500030740d9280d2595000003046003d4000c01d03002203000d00740d01c101400840e464 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 687477571 1250 687476321 687476327
    0x408030c0c100e0d05190c091103061318140a03080a0b060403150906020d091e08030c1309020f090a081606050c010e0607020d021e060703021b15010906090903 70
    0x403e040340e50042554040d0003042c084104a030403901c1258401c804458030b002c0c500120b034004140b1640f1400d504001c202d94041c40010140c0344644000b422054400300030102260140140c8840803a0480c182c420b40340115040b000100c101f04604070040000c190a45001094900000d1159003d945031000c1289540c1d204c1040320100c98212030311100c60036400b5261300041001040050070301e40b0004900300b00d0b044603000404200e000d280040c00b9000203020f0036406110210005107180300400c006800f481007138000c0d00341b00c011f180f400c80f01c8585900c0104120380c481106000a210b0206900300146050803424020b86020030242015521040d42200100400d01035101031240102d99010008404d512200d8030b2a0500d0480700d8a0400c0023019445500009056005000d500d0003442034401000c0340c40c0200185c0e80091400740d407060300c21802500240f11000a10b0034415840802d0b6400304076a4074140f5180001c030f01c86e94503054001045503029404000c07180e007041020000301713070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 687478821 1250 687477571 687477587
    0x130f121121181516140a030e011409031e06070f0c030c060b040911010311040503190c0b030f072a15111602121c0507080f0408030c0c10 60
    0x80340548111031030b2000000541c8045070744602c0d9032001008200c1100c0001c90380e1001308001c0c080e140000c82851518500c503214010200e018004c030f03006001d0103409520485043c3d10b00d4110389030380f50411041400081c1802d00d0040365008452014541700701051003881160b8000c04103007458011640f41c5680504003551214014003031286c083c3c9100c2c18002c99411a04150b80003c004000c8098039182c85500075a0580c0100d000034a400344030300c0441070070001c50f81a0788004000784030000c0f80000811441d41c2d000300442d18803d00c9400060071030705420145020b800c1031441503880d0720300000000c0c990b02c000307109035031280f40e901c120054908003136805074201900604849082c0c81000c15507005841803d450740c0541a0003d10850030704044441d0000c124400c403148081100060f4203a0750b1403800102580a04041600460400e4024801002c16031b104010b114140009190700c0c0d109500b0a03488003000b90400610751148200038000a0100101142e003000300d0801e4400c000c0ac403c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 687480071 1250 687478821 687478837
    0xa0302010e120a12020c0c040609050708010b0c0a0b09152d15041a06040b070c081516110a030905240a0c02010504090914060c0a08130f121121 63
    0x5036000403801b003501c8060081d10500ca20140060241f2079842050500500c0f089400ba0000b410080020070307049141c50480c1c810400480003800d00200746d8940300220764000d4011191032081d1000207070b4188a6916813031041381c0005088408038a01403017200500d0303a81c0908400d00b8502d0302009981c609580000d0b01402040e5000500050300311201c2c0c41d038000c0c0c0b01c045948260701280002d08160b48400401c0000d10071b041031100c081d60b410f00c840c0c0e04da00d00c081d860707089240840010058040e08400c0c0c024140c80c1d02d0020301030000d4111050a0074034110040d0300040c02e40d00c05200070b05004800038200800b04800e1151070b402d50101d10f00300d008280c502c000300300029440c0d80a40e88600d05550140c10440c0003048330a8192410046454000004407050f01552001580920b458002c0d1856000351391941441d075955000d4800b0a059000c20440b034113940015040c0200360251149403100c0c0180e290710090700e2486c14030903d0030766890f03210100c55903140c0b081e003040214641558958 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 687481321 1250 687480071 687480107
    0x17011e17100c02030c0609061906050d0b1f0905040b07020a050d0f02070801020f0408070806010807051c05060a05040b060a0f05040504210e010e0f0603180c030a0302010e120a 77
    0xb802c00414200d08620078007003034000501ca04410302c01c0800c07010541a02030b15031201e0703c006010b80254407a054803000c0c402ca6038082142150b0001150320b281850f940202030344c1c1140c81901100081c5512885540c00804d0042d590384100701c1000920a110b5400c8041800145007c007103941e5590795540b01035500200704007200122130441c5008110716005403810b030300255100c03a01c0110390300041d00140300e010075910803840c0020301c00c4c8020405d0b80c16110328a01500400381080103020608004402c420381c0300340e888000401089003400405c0c091a00520085801e040501788400c401c41c002c0c00c10780c4200300140e01009205601135131002154801d46003c21941e80d50301b40080e0b41440e004045007036181c45450141840d612100c42c45407a40f09880f072603a0301c1c081506112180c015404020f8004c3c80810104105040c2d40c0c40322115005010b01702d812082144000c241815131200e000c5000d03039100c442e81c010000d001c5c00740c0e107030450060582e581080390110006050003451410580d0b070f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 687482571 1250 687481321 687481331
    0x715080415090f24020406030b10030204060206010e090a080d1409010b0f0103052e09061406030703020c07090c030b12280f0f034b17011e1710 63
    0x307922500d544a51301425014046403115a546005009843c500240b684990607009108080c40d0291081e10305449881d4018080d9070700b8802e106040c1c06024110340c00740d00c2a84180000900b140b0020109001d41c0d46000c14840028400c0950040380a40003078107a0741041000328007a160f8010303103c07001100b444c0214003903d0380ca40180d005015000b14034094540201d03524500040c1d01c000c1d03030484104003020002156030300302004040c454134440079030061040021400651003a000fa00e01c0004800560304142c1e500e01c1d4803c12210100d18103030201c4c0c0c903601e0303141480c6401030602190102e07a1019029075060b4008181c025081c0f030300d445000d005211409001d20805011b0051200d61186032003801e00c91505024091382050f03007920055880320100c4010300102195564004035409100300b00d0759030403898108803030710324050030713400c000c030310021010501072a400d001e0007000300c0140076090410041c01940d00303420980100103c041c04000001040e040040c20350701d000148030340052 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 687483821 1250 687482571 687482603
    0x102a020f210702090907030302060a050610050d020d0f1d0a02030a2904080909070c0312020307031103010f0302030105010b041a0a090305100507090501020d0c140715080415090f 78
    0x2001d4080e81c1d40107504240c0060400c0302c1301e0800105641500d010340c08480c0ca56980700f2004040c1c410880d01d6a40140c035041007011414042c4028011001080c04d003d41882c0010b1240f1007290f84500d240c0708001d8503030440444180814455012489030303100603008024243e004250346440303d0310010100c0042103014400403290651009181044101020481c141424004465001000e00912032005400031401c076501804092040d40e070705403100088041009080c50080d0402000d680506813503204450081d801d005c01180a4808808080c000c06c0c00c500506084030416003101000e0141040284200302008001104100902190703965030100c0d002c007220917049941c4020414450450624202502600002d01c030304541d9a070020229510401203031388003114911030001c80d140d02101404a1481103480000400c03040803a00d45903620746041004090007c200c1d000a404541804100001c0201640c0d8800d0140414041440581c40d40e00017045943e81c010007014148640c44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 687485071 1250 687483821 687483883
    0x303190212040606140a0e16120608061b030108061603060506030f040b070306150e0a08030c0a0c060201060b090913021f020708060907050909102a020f 67
    0x1412155284031540e507141403510b000400f8220300d0150b411503040034003200c0060b0610644583c100c8400020203020341d100e222504030701d008031154503010440002103484480409010301401820f4050040144d46030981640c0889000380e074507034482e0740781000100500407002a000b03420007401900c080751850a040b081d0010310882e84130070340240021042042c0744184038103c6105500034881b07000385660340b000032012a0100c0c01484000031040700d41072881c9105a64110341040042e00000c505502c661101b0320f5074100803a0800140d003c3c0c4101002c008580c0d5040c0020001070000b41315150a285a045060041d245032038000c0c095800000d0107030840c0940d011000c0d401500c0448020312462804100d102103104400152088000000d9003140014449125a005c040038110b02400c080070007880c00005051107155101d01e5021445280c040d20511082c2c17283d85400d10900180404400d061454825038542136410410369241a07010200e1039101e080000450301c02d030240c03000044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 687486321 1250 687485071 687485077
    0x1b0b09042301150c06050f0115030b150f0f040308190c020f151207050c0c2209030c140703062f0a0c0f0501020409050c0304081c230411060403030203031902 69
    0x145c58541000c050211400c0c8010055045c2d8240352145080005a000c0a0301601d00006002d0703007000174801c02c46d01c1c030741041e4080c11000c0603804140b460006400000c44403500240c109481e04800000c3d045100122110352950822450402240400c110b03000101e00c11382c0030305a80c3c018840c0d194400c1c044d03003142c02121a01103500d00c80100f030707051a00740101640c1120a60000c54890210a040c0d64541f84c00c0c0c1030103c4050b07890368083e0568003148036020702510344040301070201c40d1100400040c44c8a42840b0103100a00007401ea103813071420044182c6489040000524100c1e40f01071800304904130500311140380d1050403a90341e00144008487c19550518081c01c0702d82989174250400c6011f400510482d820b1906c01d03c401d40340e840c6038110620041d40c2c0109416000c20a1501009014440f03203021a83d428000560300440e070001c0f900c00d500d20440340301400340c0d90200002c00c80b33a051503c2c2011380c15034009040c1800c6039000703586c2e0b2201401131001c0b54150b141c0d205a0301c0e419011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 687487571 1250 687486321 687486323
    0x20708090f030f3304120914031b180106080a050c0307080a1a030321060f100c03032a022503060e03070503071a09030a09050108041b0b09042301150c 66
    0x156220030700e080d0801b0402e102c6000d4903400007070300c560000a4040003041e11040c0700e0f440180a00340c10f00150400c6601d606441250700e4000900e1480880e041d0403400e00c80380284440e440e580d0f090b00e4040c040b001102c05c001d254200503a005d0041c8801c665101180561125030301d8000a10001c50070321096280000340310081d4184400100b500c40750051050b461031082c19049110300c00e484110400c0101044000505d802410004060500301d101d894410b04180c002e003000500352040039014094200283c1c4004114003080b400319580319410402c04004034a20609074110621000300907050000620000c1d0601e622460741c40e444010070b00483c5d05040c0d01008581e07450300c49240c07012114003e50362200c400d03d40c0c03e0006911803c0881103680000d10303955038580c3c5070b082c50015150400c010340182d91f4501ea41c0c40002d40b03440b2400303c56015150b40240142c07507400d06c0040200b5250141000070b2025500c1081c102c95603011594203040d1141c00f940d13980c02200350b40d4101c1d2446d0b40644 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 687488821 1250 687487571 687487663
    0x60804020f031513060f0614060304030306080604110f0d0b0118021b0a0c080c180c13080c041a0d020f1807180602031c0509030904020708090f030f 65
    0x34030a090724a0920b1180a6108005c01c1c0461003030b0201000031501c10380300b1590000e8003481c90035014903000004641c418801d080014200d5201e010941ca420300849040307502c5c542d891650300d0640303440070f000012071714200d07100c914449031a9140c1c214007406100342d2603501442c000e01c84c415002c0760191586d18000d402c034804150342801c01e85903240356216003a12900400500803405500104100c00700d2171001d0003188410061010361a0080401001c903e01414140502c96017031034540d05103401401f8000080c0a002c980d0703001c100c02ca03410070442186051031215660700300d4440c1c40980044c560101c90740113119881c0c078085042041100500d00108258204010a10342c008404662045a02407840c400e41d4075000103994a102c0d002e2900d403102d908104182d181d90040d0000c03640013413104e0a803410410040c021406a8103e410103c07130189000c160f180c0c441c281411080d0300c03c1c070110010015000740b0f230b1b0415201c44075a0424144503000c141100b04442018680616140d2610 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 687490071 1250 687488821 687488863
    0x510020c030a0b0a140f06101e080411010306050d11180901090b06010512041101110d03050105101b0b0703020f0315040f20030603010e0102130603060e01060804020f03 74
    0x124000c915003108031400c00195180a03410400c0a2250004d1131040f51b0300480d1044944840041240d0b05280c1043c040030405c0780000380501008564044645501036128180340741442e2408082d001040c2c80040e042614051080260395184274030007607c15046580314210400c2c281c04118407440303401c0d0001d9800d810000348a5402c105521007002c035800b03011700c00f2071b41c3c851200440c0c4511a02c3c0098284900e040b021501003401c100c070256a080050401d65560441d03a88401e08028800c13400c02c1c0400c0e510001007007142000c00d6040204440c5240c141080c1050000000304c207805e086000d400e018010002400c0386002c2c0c0c0c1183d1000005900d15500c904e4007138170302c00395101c0901107280160300b4840703d800a400305004044680e41420504d914203030200e1100d0a01da04014041d661564903152030304c05500c3c0a100130001040181015140141070030005810303100240d0084020048000042200d540d10011154105030304440040c04091000c2c00640b40084502800480032641 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 687491321 1250 687490071 687490073
    0x20a02030d060e2401020109060f02071103030a0519180e06010201141501111002040e0f070f021902120d02010b2d09061f08040611130510020c030a 65
    0x101801e008141a80d0500400f91110382c2d14403d2282079894048004410442c81d40c0081000c9100d00c6180c410b2000040310405921000c054035030f11120b014413640d0000708002406201d942c0814581030079001989003076860440208244200f1414a0f1000740840c1c40b281204d00c2401c045105031481407440c0811511501c07400d0100c041640c1d440e007d5032901d0103003240d0824001009114240d4a0184a11a00b0803401980c11000c0d04521131024000c17441d22150303030b08003840680042c1210103c070740c0c0c0f90b141c008000d464100014241406000c03802400d04444c030744c000b5032043c1524140d070000b04c40c40001d101181105010541d05000c40c06100c03210380d54541d05500200103494100c45015050031108410003140c0c15201c003051600c449408903403082d040810040350000d01c05028a000c0361032010720401c01c042e0b444040c0c1d00040340c0c0014041801454052187c43c0c0941502d401e10388008800118a245124410140110005100d0003001c0b0700a101807100c240c1e01801782d520204e2032b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 687492571 1250 687491321 687491323
    0x80304030527031c090902160c08030c060604110d0e0d0f03202101060503040303150e04030f050d0f06030c0b0a02060a0f061d070e03121c0f020a02 65
    0x1126038203103114050150181c9803228041202840804060081d080448160b1500e038510b2102907001018003900c0440000e00646d18402011054041a0701c507601460500e81200c40c00020307400102e41e6401444840b160300350200754a0740240341114000307070086e504801c024840c09590102e03e02035280600e450394141c400b08d0500a409003d54851019401c10101542200e00d0f00c030540c2100042c2003004580724500b14002e00980566545110342e40108808803208420260094070024801006100030980c250007252000c0303000c1d43c1420845824040345007082400204060308100f440300030300d0f20382c81c0290b04a40050000c40030034843d450186000340082c014030b10080700c014114030400a000d842c00815aa00700c5410b134080c2071a40c6031050030102800c0710407180c01c10940d07a0308002505081da0400902510060814190149000b15026000c0340311204503e0013038001080b15030b4480b0586c41201c07090004600c4d0000c2d90414110018006e000c0d5140503074203244000790980303d89170 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 687493821 1250 687492571 687492577
    0x150a0c02120102211b0c07030606030305040e060103050411060313290a0e0304180615080a050901060810110d06031407060f020309010c0303090c030b01150314070503040f0803040305 80
    0x4c030001194600c24403c1404d02d040310401c4514034030200e00701c0d001c00c10200c0308a00910704000d1303410844620a0301c03521143c0884d000d80d030044000c184001002c00c00c40341c40714240390f844042400d0400191801d0f481d61088030200081c0d00344076200003c0086c0c41400701c407071a1034483c3d40085684040b0f02c0040482c1c01c034461114070380786001048034001102c1d80124000d524441d00503001541c00c0a18160015202e00c5005003002c11081d15098082440441003115003028800b80d0740c0c01c1440c0c1404415002103031006880e03002240d0410b10180b201000014040d0302c4e084c05180c000850040040c1054020701030721901100050078000004107000c0301000001c0c04d12070b40303c195041280c0d5000280c62a126414001d80560801e103c002c3da81d601600c040c0c42024080d080100b0035001036550205101810b07081101d208045d000180080d100d424800c8581043d0b03420100051a5001c01c02c00c0c860070b0044c0450104480080000d00b04514074070a600c4040c1c0c0015460380303900305494050300d950 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 687495071 1250 687493821 687493837
    0x20010218040207021819050421021903050310030501061211030327151605010e300c0616080a09150504081312050106080309150a0c02120102 62
    0x244040e056004500c1c1c10b1003107400007075006002d0030301464a110b00a07107010000b00902403920007003410300004100d0f406100c0c0f240e48920266030f03501002d4695040105d5160b0006001c40d4402110b9920801108425030f616a40500340305031240e580301081d210540894100404c25420720744001501024034a5410003213100301142040060f541c0180341c1e030b03405540c661070980580c4440c2c489181c803c00c604852520f8001d00f499000400100b60502251310503580c107071003500900184800d1003030a11a00380c0c0300d5207100103000d01c8078010309084040031030010b0030b00e1108040c0404802e49082d000444c0c0702032041e0810b686807880c200c6403213800c181e0a444034001050601d0001000c030751152181d03c0c003599000034142030745600000b403080140801071080710b175001c0c10048440032211242c8058010501e0103d0030040f10306600c2c20030309480b45903010001c20345c02403090308801e65500740850b07034400407440c0340c1d51070798024902124000290340020750481d8402810307001c000b5041d00280b081e9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 687496321 1250 687495071 687495097
    0x90803040506060d05032d0c1c050a020d1d04180b010f050d0605180609030702011806050a050706061208090f120d1206030804080607090b0a050a030c200102 69
    0x60ba603403001c4c0b103180307405842c004050fa002005840443e02445c1400004030030841190400d400a101e141c8001c0d602002c694121940191054202d1309241020540b00c2c1040c0d140143c10603407a200040e542d07660840040c0244042000018400007060017500d20030000148203110990000149104040c891102501d844120400200c1c0c8415808048401c4620150998000e000b0b540c403440f000f40b40280a5031400030b84082482604801081103500451f54070340910741c2d5114604c0054082c9010032041c0d4410710071014200f02403600310007600c101c13181070b08155070b035050240f40003002071101350040c0343c0c503601c20071066090154507005441405400da40e035001081b001010084140540d0040540720fa1100e40c81c500701c14403a032011001404502804600e43d034881d40d51101d00e805c290081041a4048c4041009141d4040041001441d0304541c0320b150000f0488001c0503445459003400505845070150b011007449990034010203030260751101c0c5940c1c407444e1014082c1d40304404800d60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 687497571 1250 687496321 687496333
    0x21b0d02100c26063a020f030619380d05031602010f1d060c1005040503030a0c0c0b040b190203090714030313140a1206050108070f030203030d05060406090908030405 73
    0x62004c50345001c140e0901d480c4040c00100d617682c030340c015021144040480e00800320ba094070800e13403800c1020074011540d00400d0403442c2002c42c1d09008a44100043c200415100218140420b000303002c080c4074816900315840d01100c2c001c0104092148094004005202c00180b05030260141e40952164a1003603841c07011241301a0021200d41503401c82954010210031071051003454550000c0002103004401da4860f280703c1341c400c41c12034004646c1034941c0d400000822260f040c02d03108003c2d071742d00103080c074014992003030b201d00d0200c0310018070060902070b0001c04034032075071480f80b10100c0c00c80f4030100171b554900e000c009c9d8980b14422445440e5002d480c19107485603034580441542c1c81141e11889114006140c8000d2010b460000d220356074002c41003040100b01e1a4460300e0f11030400d03008240c04a45545041c198901c0c1082c107a000300c01000b09030302d0500041ea00817040720410880528003003695180c45000400900c07003903101c09005464101480308100300040610b1180c0c1c000c4042c0c0b05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 687498821 1250 687497571 687497599
    0x90a0806040b01061e1d06040e040b090303040b0f09010b09091f0203310206030106051b061303030c02281a0c0405060a02011509021b0d02100c2606 65
    0x3030701c0c0220301c1a410501010078600f0b03c0d010b10560101d41640c000080d603075145044c4401103155235001d500f0400d1100425020031090140b11b4000642100045c40118a14641911550208440600b06544031170030440801d4551400350048221100004c0c01c00695007440e00f40142d640e02c0c0c81d4000d158034400c02e04224040110b510030b0740e110305c44902028168220008291007410f10040c0d0012a9205c180c02d10005a26500080c5020382a6034a03a90380d01d8495030226004808072800650031984020100301000c88904041341c001076040c100400c400d1403070b100a0f0b0401d060b482041c00042907a2281d000b0100100040301d58a41c052545004508001006680b0001c1e040b41c00b03030422401004204000d0034a10020408089076100014100500101548011110b079008a0805802142543c2030258034001202e12440946c01050780d007082d0703400a925100044000300340030307030749402c1e103c1d000d4003540340402603500c0b02c01a06650075851881b04481101030314a54058400185078070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 687500071 1250 687498821 687498827
    0xf0913060503190512160c0909080a03020903030702030d2c1c03170a0b04050105040c0c061505030616020115060203190e0d0b0601181a090303090a0806040b0106 71
    0x100c00d032480034002e0403e40d68201c1c20504103040c0c241085079076114160300c51582d000c042000e030000ca803088095122122442c01e022021040a4015400842c503064450b000101c1c0c2d242140e8404105040c05a101d40e41d0b5170001c6c1c00c50044400c0650140107219008800702d0344104d90085000e50920301040c0300f54502c0c080d560010b540626503400c0b51002401800c2c2c061803004049402d8071a1403c0c0426202072120003d086509070391844102c0d445030086401854140680c602400c415901002000f80c40d80c0020541008560040c05080d40d940040c50300032011801c040141c40090200c1c0c925003454841042d0314200a40400015407038090f01c00740841d680e002840844166600540c141401007924003a204100c08490003031081c0d11300c444816441e00a1400c1c0d01c1d030701865501985180680014180c102018022403580c18003101c02d002800021038043e80c0001601c04c400d031038180d000c022034a07500c01c0e0304280340d00c1800c1c041d00182e00c9000084181c4101d10030042c0f03c0c45a41d94040c20307 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 687501321 1250 687500071 687500081
    0x10e0108010c02120f0c0d02071a09030a0320010c050c0c03070b0d052701050403030b010311180d060e0601032009071b1407080601150203030c030a020408030f0913 72
    0x510041e0800341c030f40d030440e889070030180c0010791001485c41d19050300c83c41c1c590716102c11580d110025030000801080461840c1c01e1030702d20713481d81b000078601d8608540c0000c1e407202d83d001402401d120b61942000903408052240601c0301580070300800405003101c402030b106400002e2207410610540902d501c982c100030402a00300c8108180450514082c01184405010020000f071400045071140e581c0f1580305620302500e10455100001c1d03030b4140303802d0040c242c4030101c104c0c85c1810300740001c1031796030000d00c022a403855040314109501b2200040008026160509002d000c503070405540680c610703808a40c0745d040300c1c8a000020381034542c41086200742d0403191090b03980a10254001a03200d80103d4603000695107120402e5110003241d50382580d0100c1e05001c040341644061010b00140004105503805451151252a15003ca00000940c0c2c3e100080080c01c4101e4044041090708070310380c06650152801c0f009603912080390400c803000b10342000907120b01c507880090400346031180034419 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 687502571 1250 687501321 687501341
    0x12030703020a020d110d060920010503070c03120203091e0a030801050405131406010501030b1f050c03070c08010f0b01032003060105120108010e0d0503070e0114070204050f010e010801 81
    0x7412202c41503800304641070b07072004016103406801d80710b0f40c091603075402c3e044500d003031140000080d419020300f8514a04c3c0b012000c1036891728010314088071103a8000e420340313602c100c03a4501000380c02d10701d140c220340f0307095249a0603001d203002000b400340306400490001c00409220301100411460b006102d6680d0048200203004600604018012424640c01156020754010703a0002d1705203242e03032603064008202980c0752264118200500c66582d150240d0b807100441100c00302c500111f00c0ca4900ba448000c02e42180c14043c001441c045e81040c240700b5100010703000302806458907503661000d806015104950011546455030400c8c2c00d40c000e103d0440119035404202210040c55100b180c125840a00a141401814030000b0740b0001c408020501a0502800210b60f00100a0304245090501440402480014010050b146a000c0c5610000c2c03030003403811701088100030200d0020b62042c4540a5049030a03c0200000b16003140300c2c0368101d402c0d107004000700fa070381c42403032074200e03500640 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 687503821 1250 687502571 687502573
    0xc030803250914120a0f11030a030e0621070302030411040c170411042307030c08070e15040305030901020609070501020c13060f26010204060e06070501090804060e1203070302 77
    0x2014010001c3e020035003d0a000c01070560000000100400c500c1c1c4003070b034101110102000070701c0c00d08114085c441581c50030b900780e0007000d4020160f500608060001c924807070082d1404241d038019100c4100040302810b01c0044040081d041c00305009020790320071101514140c008020f418030a0800f031081956800785691440d65503c444020055a81409001a92402c0b0020300c80719941e551446451101894030700c00001d014080d012040c940e0800030004028035117060070352246e9035000581d042d841b0700c051511203400320700c40c03002554806405d40d0300b80301d1031400b04001c02002000001001c80100c260200c0e449070b0395008020b0780d90f403101e000c0d0f1401030300200038083d003508000c030000b9440c81140034080b030a9500d07614040381600302d65120f040080710081d4921401d40c03480a100341d0b044040d4000b0b6250a04002e0301034101c0350010802c5000d20400220242800350a620100c444c55004050540e00e66448100130080d14444030401d215800c592a072a0a401c0300100712240b555143d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 687505071 1250 687503821 687503837
    0xa44040e07030e070b040608010503121606061d0402011d10110a060c08010609090902090114062a071d0c090109080706020304140d1505090a0c03080325 67
    0x65001020510058840c0c402d054894410040803a824040032000c5d040341004280c840d49042d0004180d0101030748407038060303004400c9240c4040800400c032415180c044074003110540701458107000030441d680c88110152121580340b5102d40030030100a00450003680c0c0c4401c2c8189903142050911000c500d01c5070322600c11000c4015540c000c01c4444510201c280a503030080da040d4603004140c403220140034001070340e60303001801019000b510440140030303000c00420200500d40d02003003203d481030168182030004400700400640e250030407103804002c00713403103000141118043c0301e80f81c00074400160b225000ba10701c0072902100021040b03402400e507030389180321034075100c400d0850741e4085e200b00d50400c02ca03d4000b1800440400082004040990096a80b546055141c0039001c4205034164450382d021203203100411a09070000f0388540a801000409444c1d0041c2c052405652640041864408070800001c0c042d1031806544504101038031640c03410000c498800e0111155000040824140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 687506321 1250 687505071 687505079
    0x120e0c030c041d030c0d08160c02011404030f0605010608060303070209060d1a01172802040c0915030209040506090f07050319060801020903010e121b0a4404 69
    0x5070304005150a07034003880c58250f801d074001d00380c00c0d91700c5101d00c0e030120fa018240805035079a00550541c3d002c015800404104110000002d00c1800d078080301a041051182000b600b08240504440003194410105940c449181c60900058a001d2248030b01017030505001620758203001c42143d6010754000c1400030581e440341c00700841001c0c085c1c400d6030f958403035012000104e108003a5103400303418140511121103159130402c40c9860303130401c80f1401d400800450303841031784920300d81d08101c00d0341210081144055400100d405007059440081c0000b22101c0d0511800d40590042212110aa60a1200f41d5500c414440081d800b0340d0804022021400041d1400d032046010b541c004c45c00d00d507002c000e203e400282c43c054502a1b0000c440d0340e580010a595145001d105d85003070720b0b0100019240f9444003480c2006c0310700a04e1a016925107031200d980880081c203006c0406110303800f0b209480c5444101c80803030f9054414038203001c40100b00700d100945802d06420844021060700700c0d010710749410 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 687507571 1250 687506321 687506329
    0x60e01241208041e03050708031204121806030608160302060909040602070f0b1515040b0c01180623010f14010c0c0e06180f012c07120e0c030c 63
    0x307041a07905210030f020100c1c140c02c200321058081d18040340c94141c054150700b089814041e00740c1c0403030303500d502c100400c07a082d866a110690b4025007101a13100c90b00c80b0480142c0710500e4a06800c268810b9170200803034410f801d60300c40710980f01c0c0f25041740c01000c500c2100341c06400c0e5502000e0350080050100340b220785090700d6200d502500c0380e00c0250070030307146944485000607000c41c100e58040c81c40782008084081402c0c5108801002c5680c07a6a03010b0075a0326146908c0341380151036140f800080c1c40c001880c0c00350015659040810396411000c42142407820041c250700641200780402c0403000203500c80500c00c0d141c181d48240c000d0888403460588100341602e009801c0c00d041c40320082000c030105403401e11341d10040000c0781d03102045141c0481000102802040c0b280d0000300d0702014080b002a1481071981541c4103241c260401402c1100000380303003180e621110010885134001c003d015580521000c84d0100004000d0107404c40f5152200e8603803074540007030741e051741c84000003514902d8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 687508821 1250 687507571 687507599
    0x40306090c120b041103191b050312040602060601050403030e010c15090b0105090603070807030f0f080d06050f090f0f060f0a090209090601181e12060e0124 69
    0x4411040d903440c0c0c0350b8400310040010798108065448140000800c010700001d0b814000705510304402804c0041c03207030001400d642c242c1d40740c00703452000441c1e00644c40101c0070030002c0251000030100c60b401f20079125003402581c0039001c0d0358018040c0502003111035000310142d40540341d050715180840c1201400464484128030f0080c0c8403030b90902c440d10408542c5201d11000705011300400d032225810b05042c086c0306075014150f64040c1d40211804c1001c0400452120103807607015110301c40c0d40641c0d06007802500114030001e800b080780003c01485013440f83d0701c080c0803a403007558140818020b5608010007210120f0b080d042080103003000400814001ca050360b07008000030b1850310324062640114a0523070b59900000d07100e6900180e4100d840c6041108154031840919002103c40f010840c5078905c0e800c40e224910205001d0304440380c4100201200348054445181102925403050501001624034008840d481c5e510b06690507402803002071303c44000c0c0e0300101131035642c0c1d441c086030340d08468 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 687510071 1250 687508821 687508823
    0x1d0f06071b06143405031e04080c0103020d150f081507080c0d060e0108160b0304050721170301030b1005010f0e03010e1501030203101e0b1c030306080d0e0604030609 73
    0x81003400142d42404d8100005000326004130011501d9040b0f00c2c00450208905418802e80c4131002d0100b00b00030311001a0140d1505400c4ca8056111442415000c0c003810314401c569080740c002c80004108031052440c0c41c0111801141200d0001c070040350f03841c4000800359103541c00596401d0000701498403080040c50482c1204d000000d21301e98881200e0500e210030380041100307810116041c0740a04103032422a010703040c144100fa00d0340c14959038165840c031651054250a010442c100c606200518440080d459041200d40315420105400d854495200340001c0ba0313802500c6000c9042c01e82c40c0e40c61501074400603100c600403000588400d603003800c8605400e9a040d0f40350510310400c64010700505003401c40e06515900254114410942814404c481d1000b50a240404800d40440040d40c504001001107200240400216000c01d01e1183d8580c2449112001e0421100806900d58044030880385004103030b40d03002d015078000300c07403134500c2d03142180d0702840c284001c0c404210641d000845407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 687511321 1250 687510071 687510127
    0x20f0706181203020c0f07051311040e0a02030403080c0901090b0f1312030f0206070e0906061b0a0209060f010c2a080c0312030402011d0f06071b0614 66
    0x2070640c41c1d8550300203031034181405002075000f01703031802ca09204104160045440c80b0141c2540b60624004c1850303c44c03010007480c2c1d9103898a01d0b00d4080304001040703c01034003004111500d10710b85005160041d500c1920224002590140010030844c400700503241203840580d90b0504c1c44ac50004031002c0c94000c0c0b512000002c6040242c02c9848422502a40082543c007400503100003041c14040d0507000d4030f6400380c065400080810610581c0b115280f051564111201401da46404010504a009000c14020340902d41e2400c1180d0540024504204d14821140968140d8030503040c0860941710348503442c0810301903d03610000449419094850000580cbc15545500342c0b030a070b00150310b025a001c1041d03034121380304143d4241414003895505501c908403803441c6040030b41c0003d0203038041c100b100605102488880303200355910460350000c030a008000c52741ba8101f50606030b0703900640107503a000c202e03410078000071a0340c06082c01d018800146491203040a001445c00c15098040581301180 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 687512571 1250 687511321 687511361
    0x3905031e10091a2503020a09030807110a090b0d140a0f0b0a060603060f051212030c090406050a030b041e0804091d010605060a031505131e020f0706 65
    0x140581c42c03140c1c0c00810700801030000b5220300030809543d5414003408004060034800000ba9524118001d01111184989030043ea6051180012a503410711900018071403000000c4820511025640010261504840c2204903c1c1e0354061f4408aa4003140b5a51700585d6054844022840214821056060740307001c4d10b403140f5543c6e0b20a20700040700a006c5668440b1001401000d007018031680c40505240d0404101040c24441e01c24101c10152054510400d58441486010701041c006400481c01645202e9200d043c42e1100c0700c16500720f00c07038007402985803500008151505440310f1080781e03041042d00007035841d9034940c0c06401e05d83c0c84180f03141666040e10100010031035401032008000902c1c00040310000c1c0440a80c80c246408440342e02c6a04100c070130300943e6611002c80d504004142000034080f29400d090815070040e0307030300465000e940001c9150884040d80c002c5545440c210091107003000410310385038103c0c00741911030b0341c07046414081c02e400180540d1041901c5090403444000d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 687513821 1250 687512571 687512593
    0x3080a11011a10120c111b030c0d06091b061103030f010b030912040305032106010e091023100503010608011a0403080a0f02010501080f1f02073905031e 67
    0x8240c602a417044000100050a4401040002e00c011000d501071071950a8031907829900090740d81d1502181548a8909042c12100708102d540c0102602503001c3c44581200b0b00507c01402181614030940e0081109452001c19140010013240c0c4207003000101c1c6103140e400c1224003003075900000c04183c507500c1104020510a1141009403000311310032002190344085000d0794a032502c880800841c000c0320088184041030b030f08088806a02c010542e0301c0b0710541d031a90064a02c281c066404210401c104101581c02c03000c1015011001c044240d40361104280e0841d4101e50700c0c8401d02c620400114180014011622684249480a0b64000c080b81c2415100d8440002550000b542c0c2404240110810816240c0a0080d24010a034100c0900004056914810f03152101c0a504111595290302c01102002e000e606a031450340d00100610703581440c0036446902082402526001803035000345c4005100340000b03030074050b03030b601502030303c2203444824400c18002c40c02c010400d824003450700822 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 687515071 1250 687513821 687513857
    0x8190e0f010204050f12150702070f06020309121203040321050a090c060509010c022404080f1903090501080928060b040507020d080711060103080a11011a10 69
    0x5003400318000005944070310f0130341040080381882d29030718024491031070002000000410000c3c1d441c4074182a80b60b05a076040d03000c03420403209400c1280403580b4000d0104000d41d000014200d0b8903c280c07441d42d41c0c0c61040c1c079116554041045031404c1c10a0030000200040c0c416040b0015a0f0609480d500028140c689145c0954200304e0b03a000556980308000340c14844c4400710358004000c98140f5a1038140c82c06c000130500701103c03401038022034850050840d0302e40c0d541c2c1003900e80308000100a44403512850640d8071074038a400040814411707143d01c0d244441c1e00115043c6025499241d603107a003850a001580e40d240b004041c42c8041c002d400700c020520b0441d55000340040c0c101c100d4964145014685441101c0307000b10707031602032403034442005010768000950180340241d03400d01107000e9607154002c075403200c0650301020850098400000c100440000542103c40d400d490b40400d40c40050324181c225145501c1501001405030000c1c4c01504000c80990403603182e81c5014041d0051080e520 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 687516321 1250 687515071 687515083
    0x14070f0e0d1e151b020c0901050a05060702030703050a081210050108190b090a0605100305130b190207061512020d15020904020c06010e0c070c05040b01110105090705010809070608190e 81
    0x80d60050680304e9041400e160b041c0000d0850345000ca40250b81d41d418200890b04076290703405000d0017158001480015590204000002107605c0000c58000d6080d03071a001c142500b014540c400e12050202c081015039805498103410ba40b01070755000510f0f919000030b01010644a0351001d2001c2e510201c0580c10384802035014440c0031a110082591131610f424402c4420032100b210b402c0610300f00900c0200c46810300941d02c856080b0b80e0608140d1a14004020305a44000a0344409480000c0001c10881c154005801c02a01082018040c0756645040c030142060540c0003035006d030210308070000080741c0000c00305824940c4030380142004c83c2080820301301d9008241012072035110b54010441c01c4403841c030703065000c25680c0a1504011055840ca91404039034007506100c1d075118800801564801d100361100004110028801030405000441d1076156030b010380c83c00500080e00080d031003000011000111445940c0b01001c0395104c02c401900ca841c59000c441d600360b110b04480300700340420459 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 687517571 1250 687516321 687516341
    0x9141e0406022110080d0201020f0f0a0905091f050405430c1103160b0c2103040c0501020303060f04051005030303040804170c090606070614070f0e0d1e15 68
    0x10588000e1704003283d1a2030462440109011680100b004403200390401060b03070340c8404200c03130141e00c2e01d54004040e039903000141c00007900244448104280c084a240340c00e01e20f4550303800d03a000626140d60511068600440b495507030a2480f58108404a40c25540415440510b501040c42d2606000b40b09680d51a586074880c00100b206002000b132081560354050520342c114014140c0c82c24040020520b00424803c0ea001c2440c00300b029007610030103001158802000c1e000c0c252a030540a114400c0c0c5400c19030703094a10b0100c5010100d010350001040381e0040b0741c000c0c144400e1004c140201310182100500f08035442c01301e0200000c564404002650040f88681660344e02c6030305042d181c41864080007031042059010f882400c04030b80310f441c1c0340c94005030252102651803c080c00e100000d0810f24502c032800c0c00d0001e003088180c84d0b001440202074031103039542c80c0c1c00d14441400c000751070b80000000750036a9070800340c0403c0a41e8200f0490104c40c03003408040c0c03545c1d90149410781101c0c1a008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 687518821 1250 687517571 687517591
    0x100f30051e0d02070509060a12050f030409061518051210050a0b030609120d0b0d0f11040b0d05030307200d1d010201090506061207030c09141e04060221 67
    0xc0e4a42c840d41c06001c40300c0078180a99441d1744501c1c00400042075180c16100d02c42c0d070040b030181c40105000051101c00c546480260485e0340d40d13540c400700c0c0401440e9030311900301500e01a102d078042c068802e2211048103480c01c214a244181040100b004000500307642e0345280c86074147d0603040a080b40180791049811000003d0401075107030505050600c0280b4540d0543c00c50000740001030501003e444400c03000180000d0031940070300102c0d1901000700b4000d402c0280c0300080400304868008000d00407a4180c1d0300b03010f00c60300001031102da02011000244190801d2000070b240d1031003024820940c014070003440101c4a03545682c18201103201c61f11500140d1008200002c0c40f81c07802060203044420b07c02006043c0d007d0b00e0f21900c0c6d24002d00040d100316001010303c1003e00e0304108040c091038210504003401d564560080b03000f411940d110094a458203000101c0381d428000c03481032918148050107140f90384941d115002075101c1c02090500205850881036100c880c2c91520340f003045507107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 687520071 1250 687518821 687518833
    0x210180c0b180109030f11010903021305040606090612081305060408010902210319090506041d01050111030a0810090f05090f2a03010f05100f30051e 66
    0x1050b6107200e00c942e2401d01e050050210701080090b2840030103450f256004080301452010410040b51004065403010b54820904141400c420442da84168011803091008005182d0b8401800003940c0c030505c10b00038128480300030500441c441d540108694104c1e800c3e910260b6403168005001c982194002180e2a0742d00e04298003181094062980c4e410822820070388452603090045960b03100b86254030402102c024074143d0340c2c9000301c03907040180078000c02d025156500c440c0d0300c400501a480f41c03482d06d0118040005295400340e0f0810745041c00c000e020b5498200400c406880780d22020b04405102441c0e8040003030590107521908401c1c2000313010204072400c04010040c6000c1512880b18102d4124144540240f42c3c000501201d809103c1000070030030300c0c820002030040100c0a61094414105020000840c1040c0304240580e2402d000500c1c41a86034443c80c0000000c0e983c141820500e05440f14002d00501202e01d40424810001c98034090040d010344c035a460810520341007158011307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 687521321 1250 687520071 687520087
    0x50a080901021e1c090f020f150a0e030111071703190207080a0305100503100c0c0c06081b030106050306010302070f05161412100c0c14030405130c0210180c0b 70
    0x40207080061110200342401100c403d42c4900031034229440000388a140708d09400c2225888580c4c0044080d090b504810382c0324100d10f100640b00034440705500f44207529000901d10f04c5110310013a0303443c2d1034204800c900b9040210200c0c9207280d10184c15a111500c005492455800581c0010300d0f0315031083e15181e458600c081805000d8520141403003842c001d8040080c0415240000d020781801c41e410400b280000444105664049c01400003a010900c801300c040354081d00200c02a001c1c1c000513145280031038010503001d940d40028018800040e030f041002c02c15962098019214040c0582c034591612407a950f0340c0c40c039014090700c0004098000705030410001003090741d14035580038103507200402100c64004158590b4801941c05400aa41e800d07554040b80c400c0c1d000003c51544088242e10090341507800585d42d0b005441554800d070b0045558025503001801800030f40d60341d9400911611400c0700b81074028001c402801c00407c1c000300041408070b4909150000100f480c0b0003030640d80c10b46 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 687522571 1250 687521321 687521347
    0x406090311030309030a0204020904240e010b030f04200d050d030c0f0503011a07120201050603120c0c0d05011e150f030f0b060303040b0307031b080106050a080901021e 74
    0x400761154030a03001031050078003c0e1004581d001d4450340c100d500582d02c00960f07001400500410407400b004250a10404070720381b401d026840b00fa5a070008426580ea82c1e503d9071129603110440700c40c1e0750150404c4c040740008040a244552102403180c0004484442c000403403880110201d05803520b500420034480c000b0313018171a10b00586140e20708141400320b80c0502130f149101c10b10408202a4144e1020b80c14008203000391030b011a0700c0b042050400c00e0502c0028007074182607400c0c9200f405017031a01d10415181e03400b160051035801010b00b071203010710010003440303240d40305081d902c035502c070f00d000300c0c40c2d0303110800200d076038200e500000801500c69242c0b000941407640254400a00e548024800f045107000f801c10310703030741c004180030840d070b56000440c0c15401a580301203407004001c405d224026405422419031041c0c803928070801903441100c1100c0502c000c0c45418081002080f4120040303105001c1c442d841441035002601d00300143c000c0c041201c80744080342201100c007107000800310b11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 687523821 1250 687522571 687522593
    0x501120e2b08010e0105010f05090d0606080a050111040f091a1201060305060a0908030606131a070b09010606120e0a1a011814060607151d01060603052203021204060903 74
    0x2100211315002c0d604000010b8582e5248807140014030070042080324284e40d908a120848031790203002840980d5450000c4c0d0396035950f1401c210b03000d5003040c490081d4919085c00707980c00c8481c07a4500d03065080c5828100c0c030003130110202d002c0c0400c20b50003034900245c036281e01854010ac0111300001e481032850070301c6420460003400d940070042c1840090404940c2c5c050a0340d400200840d041560341c0c481003d500c0203105264480681505c001b401202015412805040c0c4940039441041c0c45070f959003522400c032507141c003a0ba80840e8101c07000e0480d0300c0e074035488000c0ea01100e030115000e1800d1522007652695620b01814201e000010060055070b03c064120f104c2300b10011000d0095504a403100112281d00414581c010040882c034a41481541034a402054400c9001049109c00c845203014618220051174203080d0b0030300d00c001403103922a100e0300d40b00c2e0480d40b00031403a080c14901070b41010703d40000140c003180b2800709405003a10001c0002c100030121030703c989005070319618006080b44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 687525071 1250 687523821 687523829
    0x1150e01060f11070608070c0f05070e070c0c0315060305010f05090f030309061302010c08031303090605090904060510080712060c0c080306190f2306040501120e2b0801 74
    0x3c1c002e5074021103240000341541a04c1a6052201c841d070f640050894102185410107000c64400080030701c14000003107040e000b42ca21141025640303031749021701030700c200b404000000e100000d03526003000071400492003986601c800c07010100352a6a2911030a0a4428410700300c000280d450b824401814010010b692050706d1a00266081d46019002c5e1602c42030b004181030801c071840c00202045a209030b94800b081c0354415241500c904000c11000e4010960032422004120002008228a4021030588000860007401009a035645580b40005008064050f03141c1e980964000300b0462010300640001d0110620f04081000c4a4207100041c0d520303a40591041c030582c211b07542c0214a0400c1240c0c1d001d442501d0351a10007880094821140d0400e43c04110405444d00d00824040c00b20240400c1c5103043e005100b200d80701d00703010030000703110320b03c98540070800402204041c10030681003d81e490740c141050301d4003000c2c90010f101004880c881c0b0070200004074044a89480c1d0001d00946c098 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 687526321 1250 687525071 687525077
    0x90f0f06090902061e0f031312050c190501020c0706020a03080105060f030a090c050a0b070201021e1c1e03020405100305011413060b0c0102031602030705030d050901150e01060f 78
    0x2d1034007500421081c0c4140040c407140c4030402c0e00d041081c03000d440201c1d00c401c040150219541e00e042e811018441141100845500b01c4484141007014411820f40c1e0303030540028054102501c01c12651800c480180c0c204407041d54080c49243d50801050104c580144010f03009802d00744d2451a000f050004141c00a9100781c07000e0019505568a840540c8da000e407204200241d2075601382020b0b5244041507010075800000c64602042106020b4064910280b00383c01719201340c1c4d0a003007007282161048224019980c014160070380300d1100d6558010034031810781000f030103181e5401c108001845e6040490340100790009000c01c03035401e02440c00c81082c4058074040100d5410300b404504076200c1080042d12034422401a41c0e800ca5559010100516580c454150b544019586c0d5901035001298091100820300c0c0b540d060041c0080300303c3d0440b55000e0059031900c10500c3d400401000701802c05403156503102410382d026141c444030303400507000c0b5003807100c01c1c1c0d0300d0100000c1803101030200d0b42d420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 687527571 1250 687526321 687526331
    0x1020f01021206060f090909280f020f010512010b040f0b030609041b081e160b27040c030b030f0d0507080a0c0206030709080705060f031807090f0f0609 67
    0x2100a812660070740080040b124580c1d210340e4008403641c140510b01b081c0354800d42003c02d220010200048a00d4900c0307020400328108060841000101a076030751015262018035103d074401454042c185c40b14850050400905240d4207042d1511090780c01d030846807034a040007a050101040da56008001090000000c034594038005010039010500030300002c00b04c044280d1071260214860540d04042c00d1100304076408090f1410152401850b071003c1c2c68a1401031031244030310001000c5400003654440e4804515150300c9407800011840f08103411043c1e52020020b000540d500d40c0110049008035980100b0364180100415040c0811900e00c1061540101141040785030008180e4903d250449480c0e034841e150040107072100d850001d0300a50040e800020011119041000b040a0711503010464000702c2c3c071103050018611030100e5080010000b07200284244501c5045840000c1c0a2000e4038421035850071a80c00740c3d004e4000b00d101075501d44420511400f01e511491000b05015141486 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 687528821 1250 687527571 687527587
    0x1140d051c09080f01062607120201020703020907020f011103091f11040e010801051e061c120518091509100506040b030103030f032a120c02070501020f0102 69
    0x95251000100ca8000400e60110140702502039003201000303044210940d0407021421010600034040c500480d403800c40c0c0c0d00d0051601030018402d400c290b2849038003c11040303061690649106c20070081c228114458814003200680311a200746028000e1034004100b81100c1100460a6450386483d46810510900030441d07030190005501d0b06210203058800808000714408601400c003a14062102000018000030031410442e5060f0407204180002c200c0381e1641070000184010140c1e40c00002c00444000c500f441c5082c1032014403180f201c001655114040d541c5090300e50000141c088003041d40803030701103e07034a0a00e00324181300004440054980c60100322a03118500d05000032401101c2c45000500c103e94441f40000c0940002042c1c643c4440e034401c0890956842400101e00081506c1c190181d49802409001030340306600c01050100702100800c420b540850140800400a005c0c016404920417803154440d0807255070301918096040c0000a440c0802082d041e6407503a00c1044641 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 687530071 1250 687528821 687528823
    0x506010201050f130807051c0212090a0e0c0c011a120f0d2a060f140f15030a08070503070c0b0406050406030b0a05041a010e0625230601140d05 63
    0xb03911400f41380224507181c13003500f8100e00d0703405403840040c0f01d407103200c0b84000d007842d02e030000e28800310751a4220703002d58200507441b0110b400741101094210500394001c0c0408080b54001c02c1e4041c60008500b4240114120000d080d99202c50140c221841414114482e40c100045200c101600302e1000700b03501c40c1d02c4503900b076030345014081080801c040000e00c2880303032802100306950002400c803407030f4136003d01d420160006c00b00c01400d103804920340120540c0341000301820398840c04441082d82903554941030001d410b200351070140c0b030341400341541280000b00740c0000352000c20f00510065490f079005180000c648402034024070002d0f40280801c00c001940b010845080e03409600d00170814070703410f80209088074415040141d00c40c1c00c0a0b0f0340545c503c07400e50018580030090b69400c909000300c40c1480064428030325036000030445010340102c00da9608a05001c0d2512134141802584082002603032034428685107044c46403c4200100a05c0c0c003a0841040c0b40d040844161402501580d03d107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 687531321 1250 687530071 687530101
    0x209040207120318240b10090501030c030e0c0f03030f040902030a050105010302252d051501051c0c121b0603110a0c0f0206040801020d0e0c030a031d13060306050601020105 76
    0x14035405c214203002c0000d40d0055403c0081c2498001d0031801c9042c0c50384401030640c01d4903000d01030009107880e4842590a2080c001c02e1108591100600100c000c001c06010004c0190841d550309484104110407904201400900c0208868500140c1b20300700401d960f8152201039002d14101401400314039202a2000514441c01980c1700c0ca1038003c0c2001d14210100c1c10843c5038980304507034102c1041e42e200c00d0301c0344000741051041095400030801c20141000c001c0c000c0c06a45d070052100400c2c1750f184106504000d203110300484c01c00280c2070381c2d02850049412268402c9684510096040844228214204c0084c2445080510802584d40412f4040e03001d5165400101300c1010a403a042c01403603400c222956030094001e690722921072070410b02035800b00c205019640d02c0c1c0f80310b50110001c01b24100740e0515000f0050b01900d501d0741c5003111422102018000b6401c6882200180c0d80d0ba03441039500075107407000307003c50326514500b0140d04075500100039178156414002081100d18088000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 687532571 1250 687531321 687531353
    0x1060e0f0a06021e010603080d050f250f14070f020111061311010c140102031509041502030c13152006010b03091e010e16030b15040209040207120318 66
    0x2101415130003100541c058041c580c4090300107080064010600c01c81070b0082d5204901404100920351591161300400199900318a80218007503c11a107000c0d01c03032829a581107070326203044048030a100250015940c8020b0302180c802406110000855805c002e090300150424009040d49107000220780342091010324000309003400a44058449a0113412a02506500b1400300000003101c14180b6000354400d9407209030304042440007c804d0b15020380c01d94411917011650854103498019244c2c041d403c094a51070540b0780030301415201c02c85d02c5035100010a010074404c16400c010b10313406801241000300703a880800561005800e40c3e000069046e0450b000168125941d5071011250750421928120030030030489542800420800150000d01c405005030003503603150354582c01e401c0383c080047c2c0f10041c00d0900c0708002400c507003180c807040001070300050700140c5001e0400300010120b81c8071010403180611146002a80c03554181f041e188901503125140d51107800e1a02c0c1c1070404194829 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 687533821 1250 687532571 687532603
    0x50f0403150608031b0c04110f030a09021503041a04030e09060f1206060307080a030903030806011b031110060b070615030f050304090e03041409040f0b01060e0f0a0602 74
    0x805903070210040d03441400189509010790b910b584107440d461400409018410f441303403041ca5402803c520307242c42810b4018211290b07480c60420030380c800403c0b640004010809141c1d07900501c00240c0c903801d4902460480c00c10000d685ea280030b00d0a1b00300f980003c5050301c3d46080c2c0c41d0420000a4108040c09901e050445009221f580c54100003502e44041070b40b096045100c030500c602141d1400141da43c0503100840a0380d4802c0e8590030300942e5403c550700050000748410781c0c10800700b80036015158002e2818541038000270660030000700321441e007000840004c0c450228a4201c0a4103210680c60b40209003401e202040c6010845001802140c2c0003070071a594810404212503410901100110740c03204100c0c2061000d0f00303110351290060f100d80041941003ca48040b440e4002c0216400e0360102240c140440350400203102410750005c00445d0f90044202d2144049426444490f0080407a55180107142c6603141c1400740c1c01c2c1008091902503084000d00f030150f690081030102698040d04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 687535071 1250 687533821 687533843
    0x603060b0336010905070503030a0e1009050405040f050d0c03080c0d090f0503030f010605040f0605070f020a0f060207050d08040e06030a080d1401080604020d020108090a140703060c050f0403 84
    0x101509024440c0c0201161402ca103010b030b4400340c80c4040d00103401e000c0c0a0004d40c2d202950f03800501d80c0b47e05c42c2c01c0c40360f030004414400780e040a2602d2044038160406074078014003401d4a41d00820205e81c81582c007980c101071000016410040e08100480c400308c0c082c901101004a1035401421540d8080c04800104d4004150f8115a81c20340c0e00229121b03030000000b40c55101103003415a242d6005032624171132034180d88004507409020f501250102c42d0450074100c0694a41102168a60001901151405100d103074400c0541c3d42e0050784000b0300b00050404100381c1c50003c001e413404038168040c0e80500040741d21000803d100070240e9046a01121034129682d48410000742041100c503002003d80401041c80716400d0095809000882d140e40d4440d5056622081ba266440301c04603002548489a000c6110065110b01030b10390b080301c0500c1c11525006408d0351901c50806c1c00c110400680e80c8502c1c4c082060140343c0c01500c0403e811414880d2a20034440d802130a88e2186000203003900d1440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 687536321 1250 687535071 687535111
    0x302150a0e0934020105060102060702101517070f050102010b0123040b070c06300b0a090c080910140c0906040b0424030203090c190308040b0703090603060b03 70
    0x1020160a0749400f000c1c1102048003210900041d56440e4041c0c0b030040d0718200c002001540000340b0f0381d00036220f50300106000413600f400c000c00750458450041d041802c2c504006903801e01c1d00c2d03a0b0302041d038045001d44001801c0c00364040c41c0c00c24661100341160b04000c540f500a03608502070303900c4245642046444940030100b03890107841194400001c60358000740b60742c2409000200e88064031040d599000f01c02c8211044c403241103070084801c419034401c01d044100f003040c942d40020500d21010302036186450ba40c10705c001c111140c0601e1100404c52000801c503400100348144200c440c06603004210804507a40024107070b07000103046400074200010715010a41d41c400564008144076502c032940e40b500c1760078200550351810b4000702d004110b006940300081c007034020350b84030381309480003046201000801c2080701c9045010519254400070303804004940d90200a202611102c4040359891105150050040401e03a01402c00c062401400740f10a204003002c0b690041c4c08450307091800050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 687537571 1250 687536321 687536341
    0x3090102070209040f0623072003210c16080f070b0a140702070312050f090d051e03040e011703190f121404060e07120308010302150a0e09 61
    0x241c1030065400b805140070041003202c4130a001d200c03a84035020610550005010060202c0c82c041e2011721142c2c80c040008504600c585e2189580a00740c1c0d05180e510500b0340302842c2035a0080a114041051042900052039090704807150400406006a490054100b1030744942d40700a62005020020000d00c400c194880c900640d0200c1c0d421200401881c18030055220040c1420b01c080d1307a00800100c00624024004106481100d400001d0420181580f600896680e81f044080c407a000d0000c0c048698144c0b141034586407400d11590007081d074422401d00c00c041c0d15070000452050b50f402000706002059400100c01d04441b600314886030004295410a400c0d070090002110120100c0300d1102c0c102039001406816038000b0392540d48002250384004030540e03006103412803002e081c82000c40e0000f00c596103c0c0f0404500031096035029512000002915414544140d0000d200330006000390b28101d40201e44140c0c2d180084c0d4a81038901001919848000003124030070700d0b00c04000f40070004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 687538821 1250 687537571 687537577
    0x40c090e03030402040b0306130b071115060102070b0c0705090c0903011a0418030242010501090603020a0e0d080c370b04060f0209062a1f0203090102 66
    0x881000a100d42625401001da40750001c8074164800c0d428001503140302e003400320703986014450103251416000321644138140a03141c060080760030455000100c50140e0802d01c150f041c071041c40316420303480f401c18000084c904041e541010351007117800c00088120707000008030001220410784402403070b559480c031056968054030302119019401d001e6140503140c1010421744440d0070440d020000070042080d050036800546074001c015034800c44409012101400d0745000d15400a40c0040d959840000707064a0110303010000080021000300501c2290303002441c60000c0d05140c6421410240b050100404140010700128080c0400e086a2814021740d40300b21342d8060891822943c804030061418074000052010341807070320560110802085c0304c00d0318078075140c0c4d030010320380c00306900da6803190380042070005c005e0448075500b0007482c411916060054000300003845031074140344100000303a1042c400b40b0b0200b110160031150b030f603590174401001c4008082c444030100507101d5458014050080c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 687540071 1250 687538821 687538829
    0x120703080924150f04020724060f0e090a1208070806011e030209030c041104030c0803092101140c03010323060114040605041815020703051606090c0f1a040302031203040c 75
    0x1030300011b4401c09002611490800c0e404e100c23034491f4410b441110b9560102c684500540d620a03081c80401c1050900d2400b50320782019551064805142e2183d03207290b95464603084d84000f007003409080204040d000030406521500070b00703180208862440d4410184007050032007505040d40801c40207601d4904018100700d009029000f045a41d0006900c04074940251000300d0b2030800e00a40031880c91004010713101d5280d8040c000c807404101014001303445858002c5100720305d40d41c035404843c1d04c0646040b068040d5409005555803035056040560714000001040b1412050003862060716410001701c0a04540c030803005504820044070004000c1c1582e035001950003810008050020b031982540c1d11760700c40c800c00d08507600c1207024203004140d005600c0d015010071414404410808420b6003500401d501c1407000040c1c0e0516550340140d04002c5401101000400707030400c0c8001c5002920b40b010822082910701d081c0703459640040d0755148c1801e184540c102021004c0b0701081240c00c00c10303000e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 687541321 1250 687540071 687540079
    0x1b090904031112070c05041d030a23030708070516050f10060e070801090b060d0c0c050d0e03070b0a110a03030c08070c150b0102120703080924150f 65
    0xe0a141c24000c0c14020401c0d4590894054002074810002c00c000c02c0b244055401082c00c45050b1410b0104802010410107a1104401c885400c40d103050301031004100030400754a4001c0202401620249801c032064851282110b04000b031140b100c0c0c0040500c0e41c0040c9528000e550b520000c8000d0072003000840b8000e101d0310030301c4003a2140d00b8011072401c0032240c4041c02001020350b43c0c01ca400520406036144404100d1150050054203410780001c020604040c5c8102d14103181d80301000c04903012011203070b00003039418410504000040c4510200c00e0304619049481411420000e5280e0040340700b4101681d00c001b403206c41641c0a80e42c5a004072200d0350035100c801c92981400b0f80030b000810340c07007400a03282400064080c2d02407140d00c01c41e10b40000c0c0d4800b451100300318440040ca8801455810751107001603d1030500c5124000f0041c3d1031182d9a074690303c0c202294000e2415940f44640404c0713160502840c48811104103000d544010400c031240b92000b4000049002d504c0544805e0b030300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 687542571 1250 687541321 687541339
    0x9290c0304030b22030512041a16080604060501021005040219030f1a01180e0a08031503120301030f031b0515041a010503031c0b12160603090b1b09 65
    0x6001e0142c0c0c101c0d00c5044d0fa003d011800014022442403100391200c1d000300842c81c00d00c03c10031400c1046201035071280c0314200344440e2161000301820040d00880f8036a800d00c1010403001d85243e0b00c043c59981040c0203a90a00c800b604220000c0d4494262000d08a440c90341e5000083c155902c10210081e6444071170f6400e0907a80e00c90805c203003c0c04902c0b4003501c50400b201404140b1400b00d10780241201c80ca440c806190200c1103101201a007058000c0804a10500302e0a002242001d0021030155000c9010400a02828414103062401035084604200780600c01040810300c2c14200e0040c10394140b0705603062411007441c003030362080c09a101801ca40700300030001202d01c440103182c500890040c1c8d0215202c40c070500080014040034090315401d50003c1c004070319880b800c240c80d405100d28540b0081400e803500c4020ae00001d8640d040c03c000c0342d100030150050a50b1902c01280901800c1c40c0a00140005858503031302c034540a0301c907070010503520741c42c040c02c1c0e034048080ea0060b48008000c405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 687543821 1250 687542571 687542573
    0x12050a05010512060402010c0311390303040e0a020c07080d2604240b041802010906021519062c100f0905060616031d0109290c030403 59
    0x100401003400b03032600400c40a1140a80b4000014400c0c0c800e69059650007016102954100e49072800c2d02c5034140315205000d1a424800021045c140c001252500340e4802e00c001200c15428a1148a000f0f5001e50010002031202c05210340d42c80b40e00142009000d0b130707101000c1d0a4103140c00c0c91584002b600e40500d02c2c0c1c0b8190260b001c24480d0300c1c03544413074098100c2d042c41300c0740c0900340d94151001010021240054800301e116030344600f40300d8141c0f1900250201d02c17180403c0c16201186210900c6100740d028190842da006460400607150500c024181890505841a081000601000308000004038800914400c0f41c2004028040c03590100303d000c980100c141b80e5412002e000d01c0c480c0c2d410303080004c00b0b11071114100d03c03c40306072500c0074499a1400e203e5a006000140c049600302c142080080a15050725402d04440e6200340c0c1c46104800e40c1d10f600100860080554504000c07251030200724068242ca030a04010b004904000e4481c44030104000d003902c10009110070710700000c10008 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 687545071 1250 687543821 687543841
    0x21c02060a1508060a1a2e02070f06030b040b101e0f0215090c1c06050604181509200310050408040e04110303072003070510030902011205 61
    0xd03018032445541072110360000407000d4041030700c601484686510030000a1a80c100f07603001060441c001110785d10031503060602042c8440105071803d4002c12800c1c80c040305003042c1d200701c3c03598040070740701501d10316090034019201002c1a11840040503190300a0000b960355035407060000800041c5202e121700c44a9030080c0403c030094400e4910040312000f0034800e9030003001d0344040d04807070790b018000c003020300350450411070300c00b401d248054440c51102c0c8500d525043c4000068115400b500c07151088540351440989078000e100c140030b1401d24a403004e000d0420040141d00c1c550005d07000c603441c0f039400407060007001c3c005806000640c001c0c2e0a0501103d4005540c0c542041c19426035040d001442d51000c20b844040c2e800500c440350070402008400e0004206540081c802d011060044442c8000246160403114044e0b5829010741404c0004400400e200700100c4825400b0780305952800b800280d0a4507400741c508203041d20348500b40c08683c4584002c11448580903802c00c000e0500d00b03240 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 687546321 1250 687545071 687545083
    0x11030a1127070e10030b010e01120e060702010b1c0b07080921190507110d0311010f4b0f02041205070f0803090d060b040e0a0b060a061d01021c02 64
    0xb5000349138003030365841d005200b80591821120183c4964000458600045034090b8415004941d41340d030f50141d400100d403007884480d000300c00300e5001041300b403140750030004158080d000002da040f584042c03100024030510101580100784c0e080c402c00b80c0d81c8521407a410003030380d9000030b40c90202e11540e001081c0f524401805481820f11120341410317410b60b009845d28480c10101821160180071111040e14182807002d5019200703203461681048a0300c6040e0a444040741d5240c14143c60b40074107070100304000420504800107041401e85000d861140003012880c4165001403494090004080300c505508018400139080004543d60f1760b40707822900794014030310700c100e446001d58a80060168408d0744003c0075542c039007000d180380601e00070400201c0c10811204946075601c95548100303503520341c070510b100c05403884060010410a4070b414842020700420320b071b00c905c2200d9028002140e00883c00340020880e4034a804410031076100503031400d18011a44440c41300c51740030020710a6030100300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 687547571 1250 687546321 687546347
    0x60403020703060501170a0212030f03070509130c050315010e0a091b0201200a090302090a090209250e061303051609090803060f04060308040b040311030a112707 71
    0x401545e601ca04810388110a1005183c1b1958016220b00c0301505d800301c28804446895800c4900c2c0200b9034440d140150002c0364044041140031400302c03807505007120301c08152260740c00200300200466101901c0c9003c0a840101402161003060904da40248042648490010320b8803e0307450713403010301e6000790490350f0100e40500070b9091665440c0b40140100066100c0740c0b0102c540d503203d070742c00c00c140716040383d00c1c6142000030b4008004003603110503480c01e003d5140800d001c0368411150061240444020b000c0851101640922210343c08550031000b0100c0c1d268948802d104c2c00c010300298060084000444c00f500c001d040010400000144000c640284030b40321101540d51400d440f02162141000500161400c00015141c0d107061440700e042d40c100241b0002c0c60a0f1030343c031150707001c2c0c100703401c411030b489400176062040c4042c80c81d00a00409007100102103140f11039403010760000420a80798090130f00d050b0560401c10f421004864449100c62880485281c004001054107600a036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 687548821 1250 687547571 687547583
    0x140106091a10050f0a3b0a05131a09070302070b010b04050a0b0d090c0b0405030106210f0302031606050610020d020705101101050a020d0b030703050d0e060c060403020703 75
    0x41d8419441c1822a40016996560380340d050030804444200c03c0142e01441c070000c10041e00600080641c4005621030301044c0398070031840f00084003180005050100c041c440c600c2004c5011301000556100841c082c40241808004600c8007c844040074490301030000745503000f10010704200d017440e0306034042c10266004040305001643d84d103107813091602c0b882c084c06401000c88031080c8a4142044010006103c0c1c00b480003c4030069501c07000e02018031a0403048004e98006001c01451500340a400098072201c9007090910f0003010400c4100259610024500e611140c0003009040c0240107403500d04040c01d070b00d0a900403282c68001d000780001c0312010312032134000300709800840c40094024002820703078008140c024107080c100401c80201c058020204a2043d0154205410038046c0a0054a40d0f038009a22540c8c00324445040c3c5103a200c0c0c082c0a80e21801042021600016100c042040300e818122036611003180481d002d442042201a070b41e100380400d0204241c2d0000303020080743e00850f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 687550071 1250 687548821 687548861
    0x6050406091a0103080f0a0e090f2a070f02030322090c140313050c0a0617010b0a050f0a090902040303020604050d020601080c06280804031101110304030c14010609 72
    0x9903441d02c641820b001c0640036030801c2c03205000021810009103c1110141030008130700c082c40001440304a8201d801c400d450007850240020a40b82e251441a54001d0340c0c501d45460104c203000041d0790044080103080d8000c0203c8400964800303100320340d400e01084002c1120000e040c002610302d000c1511840c44100d01e018080c104207440b40400814129801e200f09142d030701c07108010b92005910f040f041e0b901c0d0140310014041569070001410062003030392981d903040c1c5000b5000c95441101640304946110b001c0041c1292254414108e4100c01c0503444c62684035400700c481200d02841c00d42180d80003d100041c00b01c14903800150b190b100340d102c1c20072038440e02c070110400ca07200e401c284117500e8250701c011a24015460480040c01008100070241c0347c00305490b66004501800e81e0104001052004090000f41580201c81002600d81080203202d002482c2c140c059203031100170300250070015003001c814100085200c48201c400b070500c00038012180c8504100c402404207461051250601c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 687551321 1250 687550071 687550103
    0x120201020f090402030402280305190b040b070309020d08070623060607050a050d0e090109050c0a031a09042306010b090603060a1e030309080c090109180605040609 72
    0x14001c440c0c81c030010410359420074110206000c080c5d0005042241d02c04140a06c40b9180c200300d0405144180046100102413895401c1c250309040036002d041c100c0e05a05020100861860340d11950420342c01344041d0025918880124024060304400070b5000144004c11420311803980d002c2c2c0400c0d030240904110441003401001d880f034035410703501d0020400c000005607103403801c000540b40a45c0104140c816003901c03a940d0304d0501840d0507000c00442c0404000c50403d041404401b805070504160401c0780d0304151880c4501c81c0600c5514008060315030f1103079500161100c5043d80314040240c0f07171041d0781c10189000c005003901454090b0030351092400322100030b400010901d040303031000c80c2140d25150604040c400e1950009281c01d8111480010015040c60065500354400c544c002005402070b0861900130400c00c0380d5030100913581e010444c1c40ca8203650342d01040e811030b40e20f008000b84455035403644001d07240040602410007850f200402060002d150001d0214602c12802c01021040f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 687552571 1250 687551321 687551323
    0x4290a03120c1439010e04050a060e0f0703110a052b0c021506060f03060f01140a0918020405091302030f072405030c0706091b06180503010e030a0c0809030a0804031202 74
    0x3400c564500141d030303048106c00705044c030b0b07405150803c234440e20105001c1e442d0340450140c00c02c1076030700c180710048040c20002000d600d40309110380481701c283c4203882c0c40f6103200001c100e401600208482c0c0c1042a4481c480c0d031800c0e580b040b42c2600030100500405000d400040d4840740c8020342825200c41441c0099410324090003100c400c1d0034050030090658440c80d05201c0100c0c1441c01aa0500200b802c3c841c5441414101810350011255500721505090100041c0440043c0042c1c460103401440140000c1d0350341d109156003c04102c1c4480740107102c50001910b00403203400021a640151000420140f101d544242545050401e20388423108152200b100d0610003201c0381c04074a80280300c0c480020780e090700210034441c05561745031044000c1c02c02408404c0c1140c2c0c0900c003c03a4809001d0034415429400d11001803400318000c00c148003002d1001034403885049140000c201000c10b10500f0460303c90305070782d91080040c2c1202e8841040707140104a540c0980016100341510300c422a64080c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 687553821 1250 687552571 687552673
    0x31e09010209040b030f030703081314070f0e190b04091b33050a090f0e06040f0905120a09080a050c0325031104090204290a03120c14 59
    0x106e84030081d0f1800c44180c07012240100041c2c5807840d80301b84051403901141e2072600680750402d08001820b01d07186030a081d200c0010403540003500c002004420007078160101280c1c00b440c3c9100d80404036000340d9500000c0c0041c021034100400302c0713002c5101003001071800d030a800c00f540e04041c03101c9140540201c00d286a110500076603135031070f800380d02c0240c03000e88504043c1440c2c4074541094901503813100f540d1041e841060700303c41c0704100c0c081d04000e003d10305405910043c0300002c50810960400780c4a42d601c903249420b480300c207008000744070b02d1746034464084000240a00703019541d66105c0c0f0301d40185c68040ca0702072544a4803426070031403948211031290100046295414203052851580c4d28030400303001c40c400c3d0b6400b595910036031015031102c1c001c2403010061421843d504036040001c13035004203410b0000c58050340440718180006030000c996000705040b54285200c0545ca5840e00c80b55502d21901e0302c2c2014014441007600c0b03e2106007100b400d8071680a40d148490032481951030081c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 687555071 1250 687553821 687553843
    0x315181212020f041509090204090212070c1101051c05040b0403032304023604020112020a090b030402060f16061b0e0108091015050f24031e09010209040b03 69
    0x10384100130411845080e500e952000c80000c1c20105c0c0407070364030250319040f6007042e440ba40109800158100f11500710f140e0311984110503040442d0050500e445082403501d84129841c18004002494060103101040a09040074440c2c0280020700e0315142c41c50400f60181c4048010a003800400001d03d18141690204044045007804e00d81c0d845408010040f0310364a40e000c0201c640c110f15952035100c10f10070300c81c0401e04e50700c0210542001e100041003112522091a0814418030100d00000e6100d001c40d000c55200c602e07a00d0300c0b61a03900007c4c4444c8200319424880701c0d4000b5400704070718402010307100e03858001c0704200700010000e132000702010340680f0034500250091194150560181f20f070260010b22420481e080300e908100c06130110b603a02c00200c80700d003500c0e0b10b0801240c6414a0100c412a1090b1130f01b00140180d000b118007803400d0010040d0f004400400001e1903c1e000d80390120551010241e400707854244000024000d5011040c600e00540c24030000c1180c5080010700d1045507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 687556321 1250 687555071 687555097
    0xc0a0605030105060a030c17070e0a090c0219020303040801090b0a05011410050a0c05011d1e07060c0503070b040c03050c030c061603031814061807031518121202 71
    0xc2181c17050114020200354901e802841040d4003140c0703c9010700545607215601c503844004002011038200b256107205503128450080c141115084081d60100d07840d44603441c2c080c0c0c0c201c801070992001034154010f90300004141d6107000140014005440d4819004130f0000c40c00300320a98030380c44520410310016007016003215004c02c0012003103102d0f0300207003003aa1151038130301039004195a440d0700755038401100004c800f00d10002c4000501b000e0210840d42c030040c2940e04501440503003030503100c01d218858107041c4080703042104284402481192075061340072a94000c107107024a00301c504041940170070794452241c4013860b5001d0400040e0000142030040890b41000540c0b20500011141c680b8100c1c00c044d201c00c00c298203443d100701000c41c0c0e14410218a0703011040406014a080b01c0240310350700030343c0703500780d02c410440703021400000786ea41040c0307010184070050402c480035208150708090003156660781d0741c051004c44401500c005210f40e983d12001050342c0c0481c8168010700c2200380d05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 687557571 1250 687556321 687556327
    0x190e030d0c060b0d03020c0102250302010807020f060c281d06040305030309150f040c0302190b0a1e0203180d0f050f0f010c050a021c120e0c0a060503010506 69
    0xd000e01400d100d040d218402c080c08250294010040303851a10000000c07409a0301042405c0395668052040c081e01e140407220f0450305125400f08a90200120700c0080d06110782e035008101080d10030300c46051503201520456140d4202141600c10301d9000307801090a401200c100440c28103255880b0160701c152950303502d01083c91003c0c81d030f0b444032210158150b002c03d003044008001803043c4065441107a064000c0c1001403a44d001040454500a11080c00805240300304000100401c0c440320030380c0d405503603080b40c1c48404a0820708003070580c0c000761040c100100d8a0800651311441000b040d6244416030390a00c60018001c0e43c0c1c2c2d01841c103405402e00984214101d031800c1c4451007a00150054900001100494446c0d6003041c1c000050b0070b259811011020326201002d00a40303156520b5442c2603490454a80d0b402511901051036161500b06002d00c1056414860443e5014400398680704201e146210710402c1c4d0f0b034003030208046000d605552030008415004038152812204c0140082d85 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 687558821 1250 687557571 687557593
    0xc0911190306080d080a0f090b1501030f05180d0306060507060e010b060703120506100e0f010c050f030a1205070c0f06020715020903010509060c19020309090705190e03 74
    0x300041466495810941d41d00d40000d140f2400b044280114080f80e2590722880c00c091a040054a0766041a00507190424609000103481d40203400d601004c83e510540311000b038400120b0203428103910002c0d0050601052200c5920025900c0880d03600100c2100c2c8082d000c0d150603015035955208550110b40c0502860003c00c0340d54014164240000c400000c01807a20b400007085a0842c45068000840d015881e515086c0280720b803c3d0446012075400346c501e48105001041c1c5400d00d07182501494940b004030840da409585250880c075803083c29204240010038801c2ea4035000300c2c01720070008910b4500030000c1c0c0c0e2207200d5240290159650241c9054650710380e15030005000c1803c48a40e5820040c0c90701050000d03240000703060604d0b801594505c0080c0405081d550040d1005000d500400140403103002e0300700071036080340c44455005001d102d0b013010903800e500644c50250b1300302c0e80070740410810340d50080003461407410417012170088410f0030350b04070f0740c041003010026095401024100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 687560071 1250 687558821 687558847
    0x6090d0e1003020c01020a0203040f1706072604080d0b0d0b070c14010905071d0f061e13050403091a1c0b0d0308070912170a020c0904050a0c0911 64
    0x46800012030070051301d044a191075490880e84402110001030300301080c240002501a05204020544860003800d45031141c4043d5440b030038090501800c0c00105000c440e0b60b9202180164841500020031055601c1c060802001aa00a1510300465442c00c0d01c280610707d0410040044250469402c01455070f4454042c2c030a15150700c0241e0365004090154011950240107645210f407199000c0c2010f035283c11740000034031480c42c2c5418803000100042098080b007004e020360380410122045901000c2d40036036600c3c4114080c110641240220750b8082c41a10f050304080c0c040c5100ba614203074195523900080c90000d02d9000f162501d00310800c45090100c01000745051508800e40f000120704520200040710500c55540403008a604407080000c0143c000c100f590003407258901c1c4c1e400e520780035a16a200d10304003401459580e0f602041e0409100d01c20003000502c200c0241a141460074103040613944c680540ca81150003003044100800c000d8141d0203514280407401c7c03040c9003003280b00c40c010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 687561321 1250 687560071 687560089
    0x51005030712140705030d0c1a0c0d0f022104110109060212130e01061107150207171011040f0603150e06011205070e010206011508010509040c1211010206090d0e 71
    0x402c034407130048082800d0b0f9080c4000040c840f200c3d103502d03000014600d02248501484100c1210340c00003403042060b0380040c607084800d10341c8004400200c10070314500e594001d0040110b400318040411070343c5080741854200e5203000b140280a4040b104400740300465003101c25008100c01a0010b0702740d05410485100034105a050300c204401065440301c00c11102141c00360710031000988400600d028450060010130050800803603401100810140041d50f104c156104a1038025811080302c06091400d0003010300da000c8130390042c065110000c040c0b4005800c280201e4803078501100f000995070340a8803800028050740c80050301081d01e000049402c0180090442d030502c00c4d0080043d04841041c41513510a001640b200b01c01c10340700300700081c68060140c000c81c0c50803180100204419800c60900c40c111002200e1240071a615858488a450450f511040c102105140008208201101c01e4050004287c2c01c0720309507500c0a0382242c1c0ca80074400e407a40400c03104c10702c201107030529410f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 687562571 1250 687561321 687561353
    0xa1d04050102070f080703120b010906050f090a1706280f020706091214030108031b0f03070302010b1005031303031a13050105030609060c122701051005030712 70
    0x41c10000c0710386a10107404c0b0041003c44003103200148203000c05401504144014100100c20003030f00f20020b001130b0203180c941c0100750600501141110201a4601c03c0307400070744001c0d00c0140350b01e80c0d400c0c6002451340704e03d44505050080c2030008400e460b5030000c08018031010f800700c10912a00c24032140041444080c0304000c00d03000c01c00079021990320300540010503c0341c8601c00c500f0304480001021490007030a08031030254100b004001ca4039000040d50400c14604001c09100d11a0108031845c020302584100514080481c0c6a000c1c150194810b262011099370200944d83c1c6055044940e444100d844000c0d04481f01250400300f8071a03407112050522141e503044a513a41c000004210710800b00d4000982e80c1c5800c0140003506007840780d20340010034070005207214100205114042d011b0108106c40e42281d03070002904003011901025a07800350282d801003100c058615007030207440215603410758092058000161341c107001030b11a0840b28448803400e04802160f81e9280c2214001c07107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 687563821 1250 687562571 687562573
    0x20105090d1b030927110403020303030a0c0c020a0b07060b04050402060d0f0f18050c1c030f183c140a030206030c030406050c090915030f011b0e0a1d0405 68
    0x4049040403180140e000c01045c07800407654041e000c90714103c1613864001744050f8040c005d01007040180c80c008292a0464070390303031000c102030a0a110840d000c2a514901943c400d80c040000101d10315080000c1c5409402200b0034440e40b0f40d00c0060009503101981d0082d0030601c00c000001000041c0d60040e141c0d120302d0500801e0f80c1d1900000001074030403207007400848400c594071603001c1200400ca441400003060b0b850102c12040e40d003200e0352402d0340b070001500340400e041d80b52400d10701c10710040311041c07100c1180a24298a81d01e0560b909002003891a42c02d000c0b0881613440d0320b134042280e55441d01c034030580241c03080c1455079925120f1400281650080d071043c1020005946d1a8080d510607580050103e40f02c1c0b4040c186402951009044a20018010002d41c1c820b9191400032540c41800d1000804500c12404042403a10560185009044d440e00c003608016510490501a81d480c60703680701c5601d1003d0300100705001c215442007401b0f00c042114034138841007a0081c51a03001d8000c1c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 687565071 1250 687563821 687563837
    0x207050307060f0e04090317040807051218010207230f0636150a120e06060a0f0b0405010c030507050a03020303041a100b0315150a020105090d1b03 65
    0x400481d141035002d4115a01142c803d41c95825000d0384210040e00d601c00489080c001c10380f4540340601240b81d40c0115541c5000c4000025083c0b121000864821903402411180c500c13407884010740094000882c05504020b80c2007480d440d540c0300190020035550004a1208c001c01c0000484c9813140744501003a07000203d0146c0300300c45940c1e07207014015480112000f50030748a00417400c03940003c0040090003081c600c210102c031a58460070a2007403030030601240b203541e80060000654402c0d8074202920480d41c10020b907031002c82070201d481809200c042c1e031101e98403626450440480012400380001000c414081044503611804072004440d009080180c41c040d410b84441e802c00c000d902c003c1c2e01503400041400108840c2015244048071841d800642030304001401c00101401c0d03100300300010401202080c0b100303103102400d6880310801000c4201503242d4a40380030b1644c216082d103a01552a10300040c40010010511150340c0d5020382d1102a1140350401401b00302100000a808200000c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 687566321 1250 687565071 687565079
    0x17060609062206170f0c0114070209040c030b07030c080f0c0403020a060305060114071a04021f0806040507030c02120f0d0e0109171e090613121a0103030e010f0207 72
    0x102404540b03001042c1d10200b00700d0b0408180825101400400c088a5484803003100303021500410200b041c0e110910303000010064011400203a40240340c4040e5000c2c03092001d00c41000110b80400d000c5a101d401149015030399048240c0440300e011240c4008914404c0004030456914030540f0741c043c005900607410035403a90081226641ea5070045004a9030362002d101556800402c9165045da0898806280500d540e840002003403012210b41009804100807c04542d00e00d40103041c5813100d1101c0c580c540311100801011400141c410391f002c0c92070140403c20304c03032080c040c200310b000e155001011100740c0040100b1740c40e8040764007040140000d200100d59070901c0e0091080c1e1408100021400304458100300016a4100c0c1075401440c0003005002c840034601c6050312043d8052108982d1030b545e481d404501c042c8100070000307044401d00ca1021401a0342d4020300c5200502030a034041e441500741a0024000000b03000140c00710f03d00b880c0c00c401661241a200b03000c3c8501c0d00c140d03442d50b55a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 687567571 1250 687566321 687566359
    0x10516050304031415090604020a03030f02121603080a050c0301180209040204090b010f0f0f1b05121b0f100c02030705070326030c09281e1706060906 66
    0x1801015501c07030717085007400d8940102d240300140d8200d00703060050030300d0b401d00f0b0740000c840882d64030005080c4402ca99904a41d5402400b541028505510f002e13540e950145200388034140481d20210701203090320000c58500c0d8810701c14035200d00503030303801e461640e400c00072114840700d01c10b8410b40310b00d1317020040c0c5001d5440e40d0020f44028081d410001c140060200009001c0d120003428800801c0744030030000c0000341d0300c080380c110343c03100b51b08005c681880d40b1003880d00c04040c26040900140b084c4551044d5090b01e00000380b11665540c905820001032510180e43c50304c0d24001e00310b0b40340d808451004580384250f07004103450b14050040300d262080941d174407400c002060703005031a20000300400b00680d01800803010540c0d600300208501d1841c220317014800b54015400c0440c000c0321220681042ca540b42c1d209411013440c2c035007501c913115689140c56049100400d10000041c5440c1100082102130040d82450a1012801030130840c6e41c1d4805200c402c80008001c40d50207002c0d04a0801c1d01d0b10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 687568821 1250 687567571 687567593
    0x31309180c0f030b010e13060e0705030f07050f0312070605060d15050109240b0903070e010806011404020414131d0c0f01110a03050d1e0e120901051605030403 70
    0x30040608560702d03459818020700c04c1c141607100710000340e14a0300f0000c0410b502000318030082e9200c0f100142851520840c13928159181d085540c051046109668000c04d0004444044500860300081305010400034140c40309906018210110382c24421100040e5058000341d0744004050a020580401925903405800c042601203c040b55120018080e41c012401114180e48228411107081c0e58801d03071803401240c40388075440c003c41001c00d00f0f0a20b99000d00521f00201030160000303c507540c451250036100c950138800c034030171403039180e00d41d4005044c18003e440c1110704000001d800c190700041417103810b0710f020640d215125600c03510140d0020126191781c0e00710041e40020084264181c003444250420b2100c40c0b4180b200b648040030a2201c0040c0075442d095041c0740c91034a6500b8070306124003070648140e0104841025074480c01d40c030501a40201e20200d0070301d00300c80d076002103e1402105d44c8034445007035000403410000e890241e4003401d040d00c2c40d00e00c14400c9038503050743c94407201ca1401d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 687570071 1250 687568821 687568829
    0x90a0b0301021e191b060f0b090f01060906020a12030203071101060801020d2a110c0a061e1403011a0708160b0a230702010b10020706030e031309180c 66
    0x880840c114142e491404c0b2030280040070340c28040046040e102c0d404800c0c40854a004007420b8483d407240c2c103d44025008642c03920405803c20565082036030804283c034200b4015040000e07100308000440e144000f03210090f06411540406085219940848c01782d800240340746d0a0000c0800b40004d4401c00b482582c00520343d0718001a1610700200c42e10301610b050500441a66035001035000e0791406c00030501c0380c400854100700014404484000c0d0074155006140c03588040c108034000b4449400001004010303603081b4611202450300c0100b0b03075041c465210102c40200041c40140328154001007035140110b00d503070350281880c20365960202c00703a2000e80400380c0c000c46d4001440400003200c01080c1c1083c82d581c5d040c0000300b000c981d1a040342e400440420032180b040700218240e18001c2d03202284400000d0244a024a11140060365a601c203106440000e4580503505030221004800c0d1003040d202041e426040c0d40c0b425881d040034001030a64009a0404814480d00140002100000074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 687571321 1250 687570071 687570127
    0x1506091b16140d0509300102040311040f020c0d0f03060306050a0207060e030a080c090f0d0302010506010e0103090201140307050c07031b0b040e0f090733090302090a0b030102 77
    0x103902400d8440c20040820242c030f052203402d100090903a45d50060404001c03030030349200300b0a0411440381c0116084112500305040d440042d021003801030034690904a0001a242071143d084214004400c80c85240b901410700d421000400529034030814001c6851101d914000c160340d0307140c0d114107007150030503290401582d81c0050981c08010360b90040c0441203591001850401004200103051a100140139a05441c40041c180d5625651150034441000d00641030800304100c0d440c01a000384019245280410b07400007080c0e01d0366200e4040d5401d41a41a035480e0300201d5054080341d0380d900080d188409110040c041c00400c44007c00064000358003504800c0c030005442c2c03111175120b142c0c6800c0010a02d03001c00c0188000c2030104240c682004460b601c0160310350f641803c4604001554000911103400e01d1420380f210444020150403d440004010b1059451240262840c0c01580700003500440000c0000d0030241d800e41c040a41110301500140c038150000d5500150900c40c10611004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 687572571 1250 687571321 687571343
    0x1b130c021e03030702062d0403030207021302090d02010e0607120504031b060905060a0c050d2c03060f0a060f24090f090c02070e01080f1506091b16 65
    0x15500c25151400d9440d200020390b03c1c5040801009407104c200412501d403001e038034500b0624085481c609201e0315100300000360304505046c6402400303940214401d9200c1d00300c40e0ba200395420756901c200c41c0282030003400800510155401500c00e4456619070b640d01107828082840810205034040c4040601981c0d015621030641c030b042081404445401194280c198038184484c0b50490040700a84100b16105525280310748422a80d002003070100805602170040c9038400703035401001640d01080361780e20361412101c0d030129810340f0b440007814a03a40340d844a000300d581c0540c910640d0b500480c14840c08100c10303449502c02d11883c4080d900c14540011021030140004030540b0390440304400c3ca00e090090f15260403503a1001100034050345000c0c0c2d580e007904203000c600803c505001031055101d820b40035a13540030b02503110348500000d80250b00804020a00c414130b151480c42c441d0500a00200c0a611880e403407144141e80c0c5000c5c154090010402d245500c4000c46031410030310720601140031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 687573821 1250 687572571 687572593
    0x6030411090907140111031b07060215040f0201140d0c05030a0605010206100510050412060f050603121c02090607050c0f06090a033005030a050f06031b130c02 70
    0x1141c1e140148102d11a8200240a2001c6107540d0304000b1001e03401d2a048104030544038001e400c5108141c0590803000c86a089140400d101041150894182d9000d46000544006031400c18080071038005088403442c3d01c0311401903028864001c2e2800f01c03c0141410801c0e40c054000890302c641c18500003064000c001c100106e4014010040907010a1000d0400b608017485400758090450152610429843d45000c00d01c1e44560143c50041c0b01840c846c00303401d041c40c10030034001c18031800b02c00406410a0001621402c00290b5103154540700e44240707143c0218400e0f511202080030900c03114298080015980aa4907603010b4010f49006001a020707030056031040001c00242c20409902a0340c0504c41c1c1c00c51591101145c070b080b03d4010389046981038011402032440c44210000400030504c00c403982e003101d80d0200c00f540c03003039001070002c0000b41c0321400d800030b208000300d510590680c082424030030842c10060762701b0b4440a01416417540c0c040c6c015112010350301c3d01134815005034041c0641c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 687575071 1250 687573821 687573829
    0x303010f050a1706180f070f08060717070f05070b0109050619060c0305130302090c03040302070b03190f112209020307050429070c06030b03010608030307030f0b06030411 75
    0x1004142003e21441000241c080413134840c0b02c018400d41c041000d0b030f52080b650150920007116050080e2050703854041d11440307400c0c000c41a501450a25104100000b0012805842c0201020001c8401e148080d03031003010480d25052240d42d0041001001d11100c4001343c0e07200c0c10309000e07010002000c112813900c54144003520100381070700216000000c0d8100b001c5500800030071034982d01403a259a1300c103000c50780509071215644c4025040002c440800a82c0c9900360040c502451203507082e40e030700a940724810505030200766070420544a9544034940114900c0d13110041c9007001c5400458074102604d564103403074226400408040c5155400d5680d00c9274001c9514000e440894421429801d0080f0000c12074041c80c000c00c4001042c690086400c8414104140c500e441d00280342c1b682c0303180c82e103040b824207502c5105840101c1d0401c26175010902e410f0007580c2c00e8498190045045a540703001c101c0280829521015055070760302c030356000544906001710720940c0a1044004a8010b03003041c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 687576321 1250 687575071 687575089
    0x50709150c02060a050903010608060c09010f0c05070b030405100e0f0c060412121416031704030f0806120a050102071716020402180405070c020f030f0309060307050403050303010f05 80
    0x80400c2000015a00c00180d80f01c00c265000c16010f0301c0c0c0301d51256016404a4010704858103d0b8801d84a00010009224519401004808001c0c0e8078040e4050001c1c0c0700355403050142c1380c0103003142c10a410502440401402466106000d50100c0381c442480201c1c00c81115074481d94201e4a40000f1866009401f00700003031036410106580607407130b0519000c5411481440c3e214005d01c42c10b0100540b20600d0310075900c107076100c810030048940d200c2d04001c0c08195180055402c8000c00c40d1101100703410072400d00818450340c0c00d41c03640e07510000c4981c0c04a481202c0101000c1d8418582003004412080030816404d840e4070510005035156900d040c03d03d5110f14150303400181c1c1c030082054001241c4110350ba003417940c1e41540d0150f25556201061107004c01100140c41d04545481c040014072540800b210a200d4000e49c0c03450325001e4000281a140c8034040803a4801c6c5c3d000704007501040c10542c0c025036100d540d03454031078282030700da5443d141168800c1c1d012014110b0120001c3c0150715001c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 687577571 1250 687576321 687576359
    0x302040c0f08090d0806060d0902090c070606060504081b0a0b0a0206040510230a0908030406050f1506180f0301020f0a0e0303120a09020a03051c020c030c090118090501050709 77
    0x401c0100c14914009010030705c0141203502a180204403c0320a98082d00084521030380103080da056071038140c0105290341c208a0b4143c82e8141002000104c4602402c21035050390011000b070300d4a040c114038074214210305041415001381c0c1803000010b05080c1030707020302404040c52f40034140d90300341802d046180181d078070f443d1009e0620303140c03860103060034440010501c0581051000303081c0c0d1380c5440d548004c0050700d9018100c8540042000100000e0f94440340c402d4801c02c61028103a00e50b40351401c048040c00c0800c1e81c201a0412218a801c1548100d40c1000d12004006801040d10703500441c1c03d9800c84201da90168001091502507250458422800e009080d00150700385410341d100c841d00194041c140d00709446d034444250701951140c101683c06181c105013141c00c02507409080e00c00503651404400c00500542c00e030030f0703014030300450805190340006010605c240d080910302e01245031400095040380c2c0e41c40d020000050700c01e020340b1784540d5081e00c0d203102d083e1501101044152509a03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 687578821 1250 687577571 687577573
    0x6011707051012050c0c1b1e03010902030109050f1c050d0b130c0207051008042328020a1205060a02030a0207020a090204140d05060109020d060302040c0f0809 70
    0x55204450400500350303048540c11142031a00125004094034101c1d106644442c0d01c1e03081c2801c00844152510081500d0005882102c8014410300a080c0044040d800302a500c25081c081404c41580d11949100106e1402000003a0107884c5900003803c44096039003c0325190085d4400b080718040522a01008d010b80c805559105800104020f14030b21413030100824041e50707481c1210098481d21200d00a000c162a801c00100d464018041c0da901d010f48185803048032480305245581780b140c0312a81c02150706c00a04070340c082080071412454010f0126100142c071070b4190032840460501070180c5103200c21a0b501d141d4000a00500c030040c820354015210b0403521501034400500c0c0041c420340d00c503241040044e00c0e40c0f034000022010748182c020107580101c900f4000300d84803006a00810486a000304001c054a00c0c1109000040c0740224024140e034000350010010381c44076030010079081c100728800040c0c580d10390f400070301241c600308103150001e403880100301c0380260415500d03500640600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 687580071 1250 687578821 687578849
    0x41d0907060f1b060e0a03080f0601020f0c13020f0301120203010b122a040e030414040b010c0f03050d02040303020c10021c0c02060409140a111213020a21050601 71
    0x420103402902408110760303c01e58a48800c0080c444a540281505c44480741a181c425801e0304004200351786c00c2d603142e1417034034029000c128070b90300014802c65840b100310080d01c1494040410040c00080b9425800c6d041d0f5001c100328080080154000d5000e48500603d002d00843d0900600d400c6404a040d000d02400c203101c41700c40071440010310f008096000100078038a440441240031080e0aa0304051500107080c6105041440300c08000b50040d22843c00300780306030390480000c10003564106107261707000c50708805a17100401d0303e42d0308006000b0b000341810791030026040f060340104c0c2d01c00d9100703400580100d080741c9014a002c101d50000c00c1190b10090a000f00101c1040455074a00300100090010100d14801152144410790f8000c4c18080001c0003400702500012a849008941c04068240b421081d01d4842806800b0740b88111080c00200800343e41d00f072140d175401d0000202c10b0f40d00214020700041e1104549215451203c01c200e0302c0217800c015072521514181060b044121110206 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 687581321 1250 687580071 687580097
    0x82a100b060a050f0a02010b1507140613120216090c0e01170106031e051008060f040b011202010c060f0f0f0b060a0806130515010807030e0d0e06041d090706 69
    0xc03c00380e07581c2500c1082c1c4a0741d944110070060340100440c4030110f8110045000308107040e0240c1018100060190160f0b58076007141010313441e01d40d01c0071540c000f10340c0140706412012424207a03009118446900480307140601030100311004910301e500c5038500545800303840c0c000c2d035403000d244d4007415001e00700480049688120f8040710782d41401440c0c01c00d603480d1200c01001d03030103014404503101160300c1009982403a00005501e0001c0b800752050910410700814030b620310050580703110320303000041e41c5034503401c215008400000d190b100341e0400c00170704c1c61603012540d01e114404500d40640760000d80e44516880c54007e80d5120840d000825150842c03004840d00c2e52421185406064a80f42001d60b8400c4000b4040c0c040e1001ca01481525140820154089948100090300000d0700c5003005903840405c100c0a1700c1040c015040b00e500800c00c0101c070140522565a0850303002444582840d8417031402d02500c0c4000d2140f88201240a0b0600c181030100b4001c110240000b460071003000d880e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 687582571 1250 687581321 687581327
    0xe010e0403140304020f040f02070206030406090b070c0f02270a062103050403060f0213030b01051504061b031e050d0c030b090403050d09170901030e0613082a100b060a 74
    0x8081b0721600a6483e030010462030281907049132000c1e0341c0204403945a00749410721000074a80b91408640d00c45030314010a50042c02040c06000e1139a1200340300da003c0404d6428083c00c080c110054104401e100c081c248480700c075901680344034407807171000081c800d843c08180c107071150b00c1100800c0048802e14010808603610000b101c058079004000400d15503044403d560081c4144001c42c02c580801c0b60022007000a18140720b0304171181221580c44800c94002440300f54410f5100d00000304907c410300780084020110b00c410454001c4c1004452070070700e5041d00041ca000c026078403001034000104411b2034401441400480800341c03134100101c5641a0205110b108058000740c10300c000401c6401d00500705c1e0301304102c1141e02c45503c0710844512851140160400010345011034104042807500140005426108030310744403c25a000d0302c0c41c1c8404220b90302c02180c14660408820386001c4807107030841c0c0880c40760050002030495904400d5000e040b54116554203115120805c126801c0d00d034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 687583821 1250 687582571 687582589
    0x30506010905130b0a0302060720061215030a0c060f080901020a27050a030b0103061404020a051005070b0906070810120204020a0c0f0b06120f250e010e040314030402 73
    0x2e49000042c0121130740c00025007141082c4c0c0003e501000018440d030401c02c2270701c031003541e8400c0b60500010441400782003280e0b80c0120b030b0a0041242e010b00c0041e550108416914407456005410355801c09525150002c0b00401e40d04000c01051040c08885000c0e0b61003503c00307a00c001104001c50405c480200000c00280141840126040c03c208104503c1203441a2840c014040203080007203156032841c14074078829003403006072400ca10b4417241e8014039698504040c807565000700b500c4201800c2c070b01088880c413481c506002c1002814003805002400401080340100d00340c1004020324500400000c0c12820014841414600411410007030001074048482a20340d0444001d030725000f0050044a10180d5084080c02c0c440e80c083d40301e4140140c40d1009401190291030300080c00c80300070101e607a241d00340720584984c0e030b02250700c0032410300320064800b6200580c134140711415a0b507000d040006003030a822809030602500c3c28001050380180e074000505110719049420362607c0d40024038084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 687585071 1250 687583821 687583849
    0x2c19150608161e2c101505070209060603071803260c060601050304020105070510050103060b0301150b0c0106031403190912030807110f0312060a0f0902071e080a030506010905 77
    0x10340d0131040e41c010000108000407030081c250500100d54a080790f6908210701c884d11413031320514844408984403505c188100d0781199006040b400e481d45402c1e0030f008142c0e00081625080100b1613013045485d08a960f8203000940c083d4178100100c2c48003003428108112401c0f86050034210030040c0c09440d02000c2400350b4425401d0801c103442c0c1d40da90005035214861454000c00f54090040a070501140f980d00c024180c1e406010b01700400319214040c182200c15241d21003160080002c1c0800c052004140107106c030003901d0002003441e942e81e5450705005e4050215512980c0c00100d1280420720000c21124000b00300d0749081015940f511503680c440070200b07a4041c0400c201180011025402000d01c603512202075000c940c12941c02c201ca0035100c2c0c1005010168038607041011903076502e44a2000410386100b25803905102d4a040382500080d40043c00840e40034035075000354640600000846481c0718041c1c2034141c0e40701c1d11414006c048540c01052507062000483d0144003546402c0c8512a5079 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 687586321 1250 687585071 687585089
    0x1b030302250506070c020d0f051e010e03180f12070e09010c0c12021c090305071703030606070c09051008100c05091e0909012c19150608161e 62
    0x300c1179034008140408070f90000030b0301503134551340740e28100306001607141d030450381c2e61310750301c03580201690300c01e00b84c2d80c03414180304080e0b1090010109a0f01d10024108980308024120b565980c4500c001c51030250030607502d14456000fa600401107a40e111440c01d46c413503800002017065484484018100c0c1580b601c028121054140c442000309000b0011440d6113035219140703110741c182d002da005000c40d10300d0004a5250107900000074007000740400ca41607030300c0410061411542c504040c8001c940040c10f041d2a605054980050f580426220b0580608040781080100c1802c040340c9600d001072044261219a19041913181041d620400303442080c84104d8000c441012034181503c803100410030b04540c070854400500034508015480245070070084004020700d02c2c1030940403c00e400001e0450812500800880e0030606a620140c00c15117100b100c0600301034203112038030403c6650580100303c00d5031180030303c10a4011000d011100501d580c20308001070034000c0112010000f0030f88281101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 687587571 1250 687586321 687586337
    0x110f0307080d1e15051809070b0705150f100605070f1707170c060106091d0a0f1803022a0402030406020912151003020915011b03030225050607 63
    0x2000c3d510300700840c400c2400c040180309207a042c3d4460b0211495610680e4455100c0314107a040521030740e01814821750960004d444410710b07100e4030002c0d81c5e1090004503500e014034000c11540b0b00c8400081409480b01001303941c00ea140c540c5001010480e1a000f1800303120090100d440003c1000c884031500c40e520074440c0445201c108850f40081c064850000c00001c000c81d14955443c0d00403024000100c02e5808481159a031014240c1d8644001e004004c001081d00201d1010150404038807038014032005c0d030001d02c15100c140800100c8440e02d94118686e001240600240341d0704225290345200e886200803881141030800c2d0b200744a1310b408841c001d580102c002001d000055060311218403016000e000006030302e0200f035840703038540082d0032103d03140d0b50040b4903101b940c3d440c1c510950b076000e401140c86482e01480c1d40e9131300710710003a00f50420940740c01d801007101d8289074484440380b081e240540c071041001650710322084100280103454070590609004030310000351140d00003081c0d0428a01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 687588821 1250 687587571 687587591
    0xd0c110d0302120d090c0f12061107020a03050c1005090f0d1106120103060f0603030e06094e030f0715060e0f0a14010501030c0e030d110f0307080d 65
    0xf08094480d14003041107200030600e03811000351a01700068040c0320b0252110f6244c0c481021401c464214083c030701048000d5403440c0c000440550040c803001403424203607418440603600140f050241c581003120184c01403a82c11003907040461a0020314006401c1070fa0400e01e014000c2400c1c07915624286200b09a010601c40504c140c810000100c02400b51146564124414804040d56001c0c4401c071a00741c50510039048a40d80f5100d503105480e07040d5165a042c54010041164a41010f0a55640a9200030100052a24881c000000719000c80228610b80c00c40707000720503585400c4d80300c4400d25821041c498001050220880b01c44055041840b611208a0304001035010084d411030b03500039250080216503008a8100e1070710803800c0c010380418075510005101c059490242e4440307941d002642c014000c5600039044172503808418a014440713254a840007901e0a603407401840003081c41fa044290940609200c40c540c0c89042000951409071a40d880050500c103180f0b1040010f070b550b030103001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 687589928 1107 687588821 687588823
    0x201140f040b0304050309030607020c120604020f0607052e32130605040b010f050913030f2010060f1202210d0206090d0c110d0302 58
    0x49040070701e405800c4020780c00c082c04c01c075400d0006020811058604012541c81001158010703c051503500050000755a4050150751035500b00604000c00b507116001c844151450039101740e0b680d0340742c500f801400c02c500310703112605c6205102524643c01004c2d00c200200c4178040041045081c1c5902c582c10803102c0c018036061824103019200301490016400c10f160310000d0070030040e8010546654410461b20102c500b1244031807000e0040c00f000702090b0550019150076901d0b0b101c4c80c01e00421102d003640398020000e0410072006400b81d4064450b0010000c10918031800c0200014008001c030f84445110178500c206600e01100059410300032400a000c5035014142c00c80544119000e0040781d80c50031105e0215803410304118000d031003041100b048403210b80d5000d440b03241450b0129500b05a4007400381d40c104003082c0904000304049070016003c0400171101e401000f00103180c10303 = true := by decide +kernel

theorem cover : BRFrame.Cov 687410071 687589928 := by
  have h0 := BRFrame.cov_init 687410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 687410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 687410071 ≤ n) (h2 : n < 687589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
