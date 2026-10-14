-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3678
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:52.028544+00:00
-- url     : https://prove2.me/submissions/ddff5d45-75cd-469b-8805-52700a9487d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 661330935 ≤ n < 661510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 661332185 1250 661330935 661330949
    0x50f030901020303011404020d0606090807090e03121f0f03121806050a0e03060a0c030e1603110103091e03081509130201090324110a08060d140d080907 67
    0xc01505000d681e0100c101d90642d5400060940340110550100b4001d0040081c406081072805001148042e00201c0c150121005d000898140030303221040312051f200c82070300e90f51807984188404203c50111080803680440000e600300d5070048842402d481698051340030320f2039004407050500a010407070b01c03118801000c6080605100203100c107020041d008070f203e80410800080b40c1c030725403035110b80070039091500c000703040b1050303410045a101c000b0f04001d9550004641f40c01880c18810f103020a03a5010b108506d00303241026455500c2c2d40c6400c96110245c141015a55002040040c1ca1408a41c00144940c214500c900035a4074020b08150745c0688618a5200074013540c4c0701c26076501080070360149140f41145d24182d91440140d0b220ba03003580004020411001d010404034480244484c1c2d2000000402d0116021a00706042c2a201c3c0e84514400a80510000b400600704000b4034001c0c0c44c802c541b40d4001441076424107040401d210380c041b00044840b01030104400301049500094003030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 661333435 1250 661332185 661332187
    0x9090b0f040519020102030d020a0908100603051b040b060406020d020f0613080d4502011205060a0308040803090306060a0e070c030207090603060c02010c02010c050318010f0c050304050f03 83
    0x8103482d070594480100200c1461120411400b42c116403003442a903a0040508006545666040320058044605401101a40c0c070940002c000010814002e80c0203d0b500f20020b41a036600c100d100e00c012160034120160026120481c4044944505008000034490795001d00703d4030610040003401c0019502c011803690740544144802c08560f2030b40020001c1c0c3c4130f60030a55a10340c1c0e2080c00082d0003294469201c108000003a45483c0840000312203c0d40b01414071155100000000007458805200e8080d0005000c03c1074100703068240e43c0300e1390304401c00a102c6034101d5669511912240d10541000b60703150400303e0080810f08040002c1e0390020300845007604043c0c24802c3e44000084001c1488042005400707104062500920140001c5c0280740c00500010b502ea0401c000074000030365141006610b03100c400b070721591041c840d15420850654400e4999111020902c04076400080c00c5142556562124a94211540b00780c08034210951030b000d0300e0b841c01d4140325042011840c040040d5400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 661334685 1250 661333435 661333441
    0x41a01030803070f1407210203030c0a030504020f040615120605100f170705130e1303030c050c1e0106080a15020313150f0c05090d060504110a09090b0f 67
    0x84400e49510040b80d02c0c2ca60018113201e481120200305486220800c80300c00200742092001169040e644800204003500c407140d00610200c1e602e01c0121100b445003c0140402070102e4030940249410a000500b8032162401c1c02c8002022a54658400d2a2001c254000742c05280e0300200e0171084c1c554008002c000715031030000071441c0c91040880700710420007144041100c1a000b8220611021025a002c3c200d82c070780780341d01078803d901c12109520500d04c078000000f15200504241441011901803194140041d03660507000b40c8204043c0e8400c0c000280034402104600300411642c030484c55454035085480103020500310780d00b9400c03942d070680140d8071060108850f448600700c100100000180d480c0e84030030041c2d00701140828003c00912901e0b4412424401c6500b0031282c034400ca00c001c00074034902d40c00035a02c034400c5080d40c1d81c010340090203440209196912055211340a1026081c8500b00d03480044c8509411b5000300c06c403141e132044100180448006000d41c00002c030840d41d40513003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 661335935 1250 661334685 661334693
    0x170d0503010e04020414010303030c031a01021e030418020301050f0a03120507020409020901140925050f090a08030c0d1d0906040b030607020a060509060402061c02040f0e041a0103 79
    0x1100c140a403076a0300e40c581c400f140454486500c00a0b04402001d55101c0c03658580c94010003130080d0021441c0080c0c00c181c1018030704039010300311080004050b002024503944040d040701c0450121036503060140020f03c00064452064200d01842d254445c000507580e604020420084007400700703d05004511315403003400000c00701740781d0342505840e5042054598586100040c05003400b000000e402c02041000007448410003541100286d0088070711002d1a071b119030070300c180e105e000d0700b0a00004a03070000003000640504000c09180040e40c14952804050801066040c03410740d203c80c01035440000c452008a4051100c0340c54200b242c600100525202c1100d1101c8804d010b6000788180605800705005503141d0748005017180014040e6086460036a802a4441c2d82c03049054a1090401c030000303689560105020780304a034001c000ca414150380d544003c1d80844e50711740a030181d540c0ac01c0045003440300419a1f0000b45031408581c40c291800d0300e850811420ba02500c2515080040300502c001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 661337185 1250 661335935 661335937
    0x10030203160b0307141306080103140c01020309060703030e010504030e09070906050715020c0a0b06100903051504050a0b13060b0d0c0306020309120d09230309040510051207170d05 79
    0x40804e52500300c150800303007904000300d44a05030804c0f84080041100040710744c0c00c090780034101c0e03002e81e00c405681d10808680c40c1d00d50aa041c084c50058000f0044d19210b0715102d0054500180680703000103080560340d010f1400c4510a039402c1e0007240c0c200c502c440a910304500c2d016400780e514a0254406494101d02910900400400401c82e50003c10030f01007408040d41601c02e500362400071a01000c08500700002902e0017601d005006d4502043e0131842e00b0b00846140d41240e40c090000c009942200002c14000e441c0030300308a80070f020f4019144e01091489100c1800350001c41d4081202002c1480d01200b12a00d21000f0b0b400b410380f800c404008550309002c0d503001c6130380004001da52170b66640484d60504a02944080728418081050031000ea903950202106510070341c580554005102c03450102100c0d000c0403c8503544c0200305001d0076080c643c1280d900903801d40306919800b031300d038000039001901c8039248002030307440004204201090300d801805ca0b003080100ad407170181c2101c0c00042603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 661338435 1250 661337185 661337191
    0xb18010b07060f050a060906090e0c120106080d0e1305010302010e0111030f0408070e0c09090414030403080c010507030b0a12060519020703170106140301031e060510030203160b03 79
    0x208800c080340690900465800018a052100a04010501c1c0c40b040f488020107260007522452071420300045100081c0b032259214005068000b80311f01007195003004202404940d000c841035480d01000281d03071904101140d0011700382c0d12816007000c0c4850600607591038003003015010314102001080542d8014840e4000740c0820700c0c0940040800521803461031003005010040e007500040c001407110380105805094540041c0d0104d115159102440300a000c1ca20700da56108030601e0114000846c003c2c00790313409922000540741081c0d41c903203564100d40c2244500c06600e075140c004200904d9071501c21070091120440700a18583c3c00c200c24080c40000082d001042a50f481000c52016000f0180d0b044302ca036100d520544d81c0b00c6892500614140458509056400303900c1e00109002d401569041d0410303071071000680c156880c42e25004400343d000541c6a1407882820700a070040b4185000317491050b0b1714568030642c507d14500c185072422001041034115002e44010500440810b03108030313030f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 661339685 1250 661338435 661338449
    0xe04110916030e070510020304290a12090c0b0c06091c030b03011e1b090b16110901030501051605281b030201050121030206160912050f010b1801 64
    0x2489440c010a10f525250351904415840b0b40100c0a070250389034000000c0080c1c1310a0310001e1103115201c601012240390031044062081c0c2c0074042c010b03403948980403612525a2030b12004c26603600075294440c024039035410501410398000f4107031400d600100452070704840d07010020801400400051803090540450f281c04168481000b070701d680d0303002d4020f118600b00d440c400f01c0080c4040c9001c48002d081d02c0701c05003251942d00d06081540d9000320a8141200d9003200c03441e141040d01d8125040c0301d184080125034800c1e00040061359074039a03040d01e5010b1841580006024103100320300030701600c501c1c0b000348100002000058044640f03401c1c0109125481c41100d40e2b40300c1540d9080d1500c8a40c104581c0114502c1a2007a06059054000a04a03400340b429850361440c1c40c2554441d0444215002d40540d01c18004265080f0000d0301c024142c0440d4500548055100c8107501050034480d04242d80039404141c8141c0005003c2c8210089900c00300d90780700c011401d0031401c00540c0d10500c1403803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 661340935 1250 661339685 661339691
    0x2a280e030a050d20060901020706060815040f1a15131104050d02031f020d050c090d140718020705060f010e040321091a10180b0d0c0e0411091603 64
    0x609024001284813a00000c00000d481c0107160a482c0d0034001d4002070001e4512034102000020301000102d0800d10465104000c08425516910345c41c80075440280203c1d41902160916804c101d0326103c0c490180c00c6a001011074140c1c124200000031403064500c8036140d161441c038030400d03054007003164106c0d2030030f4a19001403c0207000081c10700100c13204013250f9101d10350f140320340403d0700e90003012800000d070b004100513101c6030070190460184091040e007040c40e045202001c6007156442541d4042c0100c211a04a6114509031007280d100c0c09040c0d40d695008550304c0b080040c18003080741d01c0030312000c03600c0c0c0c3c0d0740c9082206141070101801c050184551175825003508010742810024071501c206040c007040c035440c5821103000040240190203100c00e90701142021184090100c1202c10b01843c0342401c04203041018001c02140110641c014140081000002c0b52511511300400010450b090546400d06001015011030014203220b030101c1c4040003070640004409400701c1c1d0083c9800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 661342185 1250 661340935 661340957
    0x40302120c06030f0f0a05040321090c0f080705100e0613051908010e0f0d0f0203070c0b0316030903020303070c02010c02030601090c020c03062a280e030a050d 70
    0x3041c200030003840c1c81504454000b0403c550618601e4406015940c020103542e142c2c0d48000502007124010354000b03001580320154100e0105003001000040756040070300184105041c2d86000e400380d6a6441541d61030854201008204824404c18001304010755190284c00760b2003000403c14044c3ca0358051041c000464100d4150440004240203014080c1452011882640c480c60ba000b1862050780c60540c00c0c02d40480900c1008100c02c150301081000910040d800e0490030350701401c120204008500c010f001c1c1902046c02d0408140c020440301615030358070f09020100c50f110040600c10002851709203154580001d071f00000320390344810a0302d02020445c0540c40101c80340000080041e503d441504004640111141e10403104207190760203c40c15001440305042d124102120805103055184410100c180480104c3c004c0346008609064640340d00d8540301d05124001421030340a002528280300c06550b0000840d012040c400c030300401c00341c2d0700d0b555030319520500980c5a0341000501429 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 661343435 1250 661342185 661342219
    0x20606131407030e101a01050703021c02030904051303120e030d0f020702040c0203030408030c030c27040b04110d0203070201021201171009120c03030b0a0303080a0b0d0201020304090b0a03020d110a06050f040302 93
    0x80090301101041e09485c9020f800c0cc025520b41007010550305c5a0310b8100400d1280481c018001f0000b0382c1134a40116608401c3c0c422002403810004490150004002403e007052062060084500d1a00b00058a9a0060050004484d6440400c106641c410002c0c0030109034804c09407980084025030103a901c2e40d8030040c011944c00354900812290100c005107003130903074a90703281d220300d0001684c00300008d42441c4100016105010b07032402d07030100104601c096009041c2c00031540a401c5e030002500d00f8124906010342840264801c4d4240e0702c65040040001001b4451804081002c6005011601c220340b2424031b43c14030a5040e806001c080181a400c240c0250064049100c2c010a0031901d5966828041c00c804000c584c80941c0701d01c0e03c103001210746004c115200c881e54040c3d004508090074071408600800310b40c40d5140d40018059800001030742c4048841c4240741c458000d11100080003001c1c0640c03102e80d81c024009005040c488140c2c200b02c1c10041c3d90499030120b8010250113000a5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 661344685 1250 661343435 661343443
    0x1206010207030213050702010e0c130908041a0c070605030609070f211d0a0b040b10030f08070203150105031903050c070609170d020606131407030e101a0105070302 72
    0x110094120790f903140c4c0da1001c200598001172080455030002d108000007440d900c2d84a501900840d98081c4401d90303268003500ca280d1110040e90300c100e40ca1844d10340c481c1401d40200c55410458031080f1740c002840b03400c3c4d003802d108040040c29036050090446c2410320001d203d0501c010013010401090707130350351500e40340f044800348190401030200b003124503413411010000d420000803000243c0b004000303210910000180b19115150001460390607500d40d9070300c40c0500d40001e40340700341210302c0500110100e0820319908074607a01c03440c5c20300d590304101d1050604007858811075081c0c468080e001000340b91008250390158601d4a584100c0480051606880c02c0c0510303500c0c1c000900c00d0302404590704e43c00540440c00c1d111001d07140f9a40a2003074181030360310041c4500000c010380020300494100e041a1607800d000c01044000410701c0514101c0d00020018110b864a00180d1540d079100c03650300090003201400c034420501880202c14200c825590400c2103141c1d0b0b0704001000800d4018140700380 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 661345935 1250 661344685 661344689
    0xb040312020a0f030504080708150c2d130501051e22090e0705031f09140115030212030f1b0f0f061009140a091110050d0501090509031206010207 64
    0x1d035407070f070b0300c86410018084e401900446407140700392840400c5a84001541e03280c0a007410445c40881d40d282410003440b031f08840d629180c480e09204c0e075000c846e046d0384203034030003803002801180e1a41e121680c4040019090b50015044c0041080400305411004010308900d8800000482d5030f00c04019a41d4407031b150100b4141c1340c4c00810301d408514907809401c24505d1500440845101907207840406489103200000e9502c030a0102842c06241035581c4c01500696001e00604000d00c00321040e442d00b541c6400c140d512031003280314000c1c41113103042091140038217a440020340c240040c00f00b10840d188074100201400240c13030041c08607000c0d0204043d4808280c1e21056400310200c28950541d140001c1d680001c0d0354100e09400300301e031242da10804d0300c2000005005c50f0750780c4403608850001d244429090b00c40040c003280c3c04145440e00490040301d466242e4031f0765038900f803c6c2500c13412103c1c1a044030361964103020901c141c2c96400000c0c2c07141043d20081c2c2c1c0c84207131200c00040c0d103010030607 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 661347185 1250 661345935 661345943
    0x1090213050108090d0e2b0b06031c11120d05160201110d0510050a06020d02060a0513031115010b04060914090103020909070f030803060f01030605030d0c060609090807050706090b040312020a 84
    0xa001021241c0e0724049901d101841416005020307200c9c1c0d0304150f1680e20105881c034100c0a48a0f5400010307218540544c3d5001190301502c4203018441c8090245601c0a1440a190348d1140c0600c40b003e1821411103d00010920080040002e9034540540512650301080c00840e12040490320703146540007101c00410005000c2501d0b140d90744000380d21851040d0110015000311000506c140c2d240e40603181c4105620005411488503d523001d640d0341d010220701407440d08c0b030006c3c40040401e2002481c0e002e0b0014901c95a1540d1030140c006241e03a40a802955903413414040380d402070749074100e080703065a50440d14481c01396a55a800e525040c03241d84401c2c3c01c2c003100c40d0000b0902c0098001076004240c140c1d9165030100d00f910044d815100700d44601c94141e804a031002502a00c11110310501c14030612000c100a0b80d5161040140c40b03401806a555020014407901001020042080140703ea0f090030101d082c540700740c210444c0940c1c8006040c00010059443d14940b080c480e17403000e01d0340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 661348435 1250 661347185 661347229
    0x130201080a0f15062c0901090504081c0b0f06121308120109060609050301020c1024030b07030c08090607050d060506070f0606060509060f07031701090213050108090d0e 74
    0x140b03107401806844211440c11000c600142c4081c50b4081440c0241710303c010250100f200c40c2d2a043c1d10304001c01c4000c01c241c5540303409010911101c80e503490861903d20600002003403da81d03000070003a0a0107080c1c10203200351010803901d41c1520640b01c200364130204002c90030b110300784c2078107141200d44030722004e01d01c82c650b202c000070814405640c00441510b0282c0e84500c155501d44041c9402c034840d40651003001d40c00b001a8041e1541180c2000365800c4040c02000405005500400401002e81e041200e0100c07030502000300d041c1c1d15104018000300a4030340300c80380f0304100500948401d0054000420480c0006209551201c0340e0003a0008102c040c101541c0d801c094107040c01a0085110700720ba25904001c0300055a034400c1003690740704540104211b1805880120303182c0b583d40050002c40030300078400300340e1054003201c54200e4000c050f82c40d4050382e0f07840d00b5000f14043e000150040340c1405002c20038000c0380c81c0e002808001900030380c1130102941000c0c0300080d54200000c0c021050680c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 661349685 1250 661348435 661348439
    0x61d040c020a0807050303160c030e09070e06070b011d01050d11030a081803070b0405130b0a0801020a1e02010c080105040903120501061709030307050708030c040302031005040b130201080a0f15 85
    0x10003144202390440410851000c107200071100f0019103c0003038001901e11444110b41e10b40000d005411005034103020b1414040c250114000740c01c0490141c50a04114004003d144000881ca04141c2c01943c89000faa604140c00101000341c0080c002d0945074510a03024a40d131070030030400ca076150300090030540351480c2c6000300b4500c01503510418003a008585001545011003810765060b144010004100140681104001045d100d4503165000c5c0320b148000030030300020310043c19040f0791380c0c3c0c0310b00000b0644030340b0281042c40c2050320421a80351a407003a040a5020b510f00b41941c404070b1300850001c2d85801c040f034890090a40d502c4145281100000d24103030048695044460003050140300c50b035401460307585900081b10700e800810420800f2000060440000b144e000010040c414102a100c0d0042860300000340741075100c25a483c4d05000506c80850142503004d900400341050b10740d440d41c002415880050500c280268940c0445e42078020250841040400225841a1281d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 661350935 1250 661349685 661349693
    0x70b0318010f2c1b0d06050702010501171506040203132301060b03100302041d07230418260c0a0303051008070e071413050a061d040c020a0807 63
    0xf08490a026900c0d80c1410501800c00561841540806500b034002e01a410011004008512009000f895100300c140f00ba00307001800300d126060103803019070300000311981426084c0e6072002c075a00507011194094101c030b542c080e0103083ea182e8031000640b00541c0343d4594a040b4400c44210200040c200280003900e4801090000b1a4a031400c021000a024140c0e0702c90f219260761000780c44c020130b0052100b03070a00260620303400c00060301086004c41021100003070344840c140010f5401c0044000c2500c20050303a0201ea2500c010825401242c007009003035180d40031a094500d01b8a40205651003000c400427050740818035600e0741c0e4140383c55540c0c1d180030800545d03454010f102030407400700346040d011440021602c040c010913640404020b01c07032a403c0c0002d2084020f0000c0c0098100440700595030310030240407014104d00216980035122081c101820401050b00c0e540104003044820305400043c00d40d2001004121001a2000a80f507603854000300e0030000b141c0000343c0b0030180041e8050800c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 661352185 1250 661350935 661350941
    0x10306170607140a2a0b01180c0504050108040201030b03190302010209091b0f0c010605220b040213122a060801060807050a08060f0a1203020c12070b0318010f 70
    0x50049950340c0c1c80d4880120740111814042c6076612800520500d1714a001281070300c081d021200e5aa41e40201c2c5010650380380b40d40000260000000c2d00c0ca1450850030081507409a641107240c141409070409041000080090100400c00390406403941d80b54100d5840500030310701d95070060b083c0102c02159906002c0e000c0c0d40b000115501820303600c000202103000400d0401023100a418041d80340502003840c600c1690813070048500e803556166000100c6550b00c1d03103c0d020440c8150304c00f4408169103e2071604507140026a94081e500401c880c800d0224100701210980f00c49001da01920b00041c05d00c102c01c2c0200245a000042c00304940c1c14401118103581c60841e0071696907400c061b030700c54004540045013650400c0100354103020445516004944141e4000c81c081d000b585145010303c0050900c590660090383c00080200724a0b0501d51b051110b82d04d40e40d8155000303c0000103010700d103586c400d218030500030741c040044045407054001d0070b01181c18800300c60007805600c198540c140d0003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 661353435 1250 661352185 661352191
    0x60e10140d020a09120c060f02030c06070e090a1e0207150207060b0307090902100c030c05070323030304110603130b010e10090c0f08100509090d030b0a0b03040f020103061706 77
    0x4240003490000d01d40c2c080a5070369817072591040d0f8110a180c600001582c3c1d82d41032940010a5000600184031a55010402d151196145035203003d0030f410607000f0702100f94030107840703031101078205200120400c01140110f56003001c0e5000060b9503020b00c1c240341401000c900040c00c95070b0f00004800c0c051041c103800009020030102d0547d5915a40c5e103010004640c1c580100a4000c0c84007055400d8690040805500c190b020b402c242544041c5a9030f51402d003d021b030400c417035082815181c81600044003891403c400c81001c01107140d8246a21a900c130740c0707480310042d0f00c51030740000001c40c12404980402d50169008414034a5542c541591420500c011640020584005000000c0500c050f02500080f1070181c4c54011007090794010440d1240002001d000e02c40200a03800119600c40241d100e2043c04984041d01031080c00380b00c01000e9861541245101d100742400600100c1160411a90020b41c0490030499148a03480141e0160040da170005000362129040b40c040c1c4100482c4c40b604c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 661354685 1250 661353435 661353437
    0x1505010602010c0903030e090a0b030f15060f0f130e060a20121602070519032102071403071d06090f011206050901020702040204270204060e10140d020a 67
    0x443c6181984003100c0d8a24640b001500250040001b6006802d1000c60b150b0080078130880450b492110401103880c00744100d0820566601101464007200841d07041c4640004003250382800f050f004600041e900410500344910520190b0403803160b10780380e54803090071000000c003a500c203460000442401408c1a201c00c00c083c21850007040394909104c8112021508803882e45080c070703191405c1f031400485000d041c10080d032040981c04582030303940852001c03050040300e0203501414254501109070700e100310400a880301c0c4da90643c400349074022234013101b074421114038807240243c450700003450200c0c02c1c2d01c201f00c1c409484c40e1040e0090700034003001d4800c020a031080d200c980c8400c182a018154240700741d2109061540309800020349039041150000f209030f00160401030990009012039001c2d5005140807079210b540c00c089035080b11a5004403025202c0f045003860b1510350050940444810300a2003076118034580c03240c41c0d0003220001044542c59800c9074a60031215074800087d07002513079541c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 661355935 1250 661354685 661354691
    0xe0a1b0c0c0602031204150b130f18050a260d06080c01021b040b0f1e010206011406030604050c120109060906080f0d0c0309031202100b010804050a02090a0603150501060201 76
    0x800c40c2e5000208a4620050f4488514010b940f40e488409141040d07503038190000d07803078403a449416503843c0003070315400c1c2c40c8840002c0c2004820912030115034400c0c2c90301070b40794010246000410408540c1041150304071151101d40c08030f81c500021550256a41c9141c1c3e13544c00b0034121100241035000b9400d8480b1002140d101c540e2a0300160b9a070628016508848000c00b8290071283c00c0c16045074600c0d0714060842e100551000c7c00081d901d20034515000e00107809054420990340c0c2c1000010300511104060840320450000072440501c0014841809913450350003041010107800129030b81e4000b22900e180965840da41c0e141c001d0641c52042403d13580c2012008034114502150180a03120428000d041c40c0101900c00d45201c5030301c1900760240000c4d984000301150881c04038030070000c1c1c5940500004281094240110b415980d0308a04000d00e0404200c0000c80010b003111415030110746148840d07071440c90440c041c0903142c00090544180e50742c00c2100031000e410a90603107580750024 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 661357185 1250 661355935 661355939
    0xc0906062209060e2d07120609090f050c19090914010c270e011703042301031a060a0c060b04230105040908040b0f1603051c020903070e0a1b0c0c 64
    0xb038204813000740845d19041c030000022902540c01808090010204210042410b55440702d00c0d004075521400c00f510860507520100742000014011854450030882e29540c0c1403045a100812914a078000c09505031743c0d45c101c00041c0090341c100000300d00b01c0207000344a11840c580004100010100b1401c0324040d00684c4000501303852110b03035003038540c1c00c0702c102c49a0b0b01e400ca8864078100600c803140c09901040201103810a0b020545c1090184408540200981c2c1100010219802c0c0321415142107107241804ca03051ba10401118000c880c40e1924603910445400d02d00d008007210001560702620b8a8401c906c4d00d0b0000d0000c4010881c4207600c00c205a07a00c07401e010640e0b00c03008000700320607001c0006011540390b05000e0104611040090b50914010818052090420b204158040368010500c8900e00901c1e0703055031100700c1c054200354181591343e40440d50340e01442c02200982494070002850010b110383c45035146800c01c0b0b0403c101f910065401904071141da200c1070341d280d1619640 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 661358435 1250 661357185 661357231
    0xf0e0102070e010603091a060f0409261b0304050f010c0309090216050c1c03081b070305040905060a0308030114061c0b0108220b0403050706050c0c0c0906062209060e 73
    0x1f200340700c0d29016003400103541d90740c410080100001c410440340c04501c60040184116401c0c4221035204005400c45d6a0740180303094501000083c1660928a0307204100610258451420303039100e168080c24054500402d40c541a6005207a5030050380b1034900c0418100165585000d4140c0d0f543d002da0b040d1020b00d02007500b4819103e6440d030391304074a40c1c1904000300009200308451030307000111001d20000141040c0380b0004039440208150700080c800704081c44000300d07a204540c3c0101040310301c003200e540345555030700c9c0c0b600051080255400e840444851151038080c1110005011845580516040c48407031000a00b0711201d510300054007000001c801d203400510b011031000a11105200c001600c0e030b940902914010400c608200090100d8800550b0300e0041c90700035a80845807903110700c1e04805281ca400940c01d0f550b4400d0440d182404190780b01c000458400b5400400c0d000c0c0c01e4500351481180030307681540040c901c2e51600e1b00000301c4280b80e009050041c0c0d01d2441100340d03a060050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 661359685 1250 661358435 661358483
    0xb0105040b0301300503030106091205120a111507030c08040b160c081209060c0a0e09060f09040303060e0109053d12120f0f0e0102070e01060309 64
    0x7840058500400041c050940b8402100c1d00314403050395a0b00300103040d0916101100350210048841c0e510110040c0901c940080b4050007401070b2500014000040d51955a81c494201c070900ca1882000280700040900c1030981e002c200003100100d400c0c128688070041442d600031500c0c40000703490400110060340c401d1000d00e00179900801540c0858803001c900318800e0a000c95802c040c000d0701d4004400254155000e0000f089444840c001c0503d0801059030401c8001404114601c20030484400c10766049000041c06520694280305955a0702000c07807104210242e134550320020040401c010168160402d070256404406501c5203a41e861103002d0aa540c203407200c0c1d80221401300f80174500065450500e000e5141080742070020755501d008461110181e07040042c03500e40503d100c60900c81a040680507580b02072800d40000504408000c0152070300c040c0e60070400048400d5000140c1c0b0801c0035034080c0c0003661009007156900c0801a000340354091007202c2e4008506100000c1c212019 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 661360935 1250 661359685 661359689
    0x42d0506041106030402101407171b012c0307050604230c061c06030c06020a020411030402010801051c0b0124030902010e1210020301060f1707091203030b0409050304090b010504 78
    0x1d0003003500a81c1c00c087c1136401c074546440390307a41013a045c00a200440c11140d100c0e9540d04000c500313240d841e01e200208100034440d001c0b440c26140c1c1003c000f1074800d9000c20000021030401e00307041c624114040f00701c40c01c41c4503506001d01584034440c00e01040c040d0296200c010112006100e00040700003801894456502e1201d81c0d60240080c451106400401207c195006840c400c0000e144c64880e80c415419803050342060006900c018a104118100340c490070b200c21f10b1b000074583c01e40c40c061740000c02c400d00501130507024885541c94ad40711400340c24644980d56078401314a40e40c40d81c40d12840203500780c03c981201c3d08032060341500500c440c080c0c400d009410f90180c0d502042d442208041c09207a504010340c40140e84a66801c0c1c401000031480514060720aa54400c49150303905400140501680c2c080c01c5072142010041c0144550080309440485100d030755000013102c00340c1010340007450b0b5044d4994205040901010400030044003c00c265803480d00c003044074842038401150b03140114 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 661362185 1250 661360935 661360939
    0x120e07170f0601212301110c0c0d0201022a09010b07030e040509160e07110f0c011b1a0a1a010804080f0412111314042d0506041106030402 61
    0xe000140f14031210b0780c0032845016030102d421070030140c4070782c0c40303584c140441500c2801c40000c5051000c500305c0c2c20b01500c111035022140141c240b0035655005074a03684110000c03440f070705250300c0d1002103900a1280010300c0e0035100d00d0748094000d0000324070f26030a824002502c500900f50010898000030f00a40b4136850b0582d45454a18802006120042034090100d02c800d2045500c4407903994108801c0b2400340601c0300010100b404c1050000d00714150721403031822107030070810304141c1c004000105510501d500b4685413000300905165640c010700001e00142c19004026044a801400070010707502580d205001040030150700e405040990030340c803540600141d02c80010a011840580c09031002d1941001a989050b0346c0b200002240c1148007001c460281c02501c025581d4a0852503015a1441002041c0924282c208200d19403c1d40140000c1808202952a42203d581030b440d800801c511503d2404003d88182415540d0708421a01201c2018440c07c594069003404c0040d01d00450b80 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 661363435 1250 661362185 661362193
    0x13020f150d0b0619120b0a05100f1202030403110c0405090a08072307090605010201060b04091503141e0c01051c0b03060703060e091204050d03120e07170f 68
    0x68500c9040c0984010b418055020304280100366500103200d82e821540c800a4541042d0801d850f0041800d56501040c3c0e2845003850748810400e0352220f10325040f007048035203480620b446041c202980c00d4224082c54141442c804000c100c209600b000441c0f1043d410384003101c1559812904003c2500e80c211803070001c81e04103000600008811402500c9982d101e081c060015541c0e807800000003040c40008402140d01c0100c003008400c049215001c0a0a400e10003405074030b0801071208214401c91143c0c420280d0384c1d01c0c11244556500d454030740a1540141541c1804115401055407910290850510420303101c0d00048082400242001d031080107840c0c541c01c00d0010083c1c2d8a50320010360011480e1a194220720640b96002c1c000d4501c21605030310001f40781402d142d042d103450f4000400c180c941c0e600c080c3c00b41940c075040205680403514105c900f40d88524592904035000c141f25900c1d48100f0341040c021140c00c00c000300b208419602800845130f503a04401c00840d64859813031080b4001908 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 661364685 1250 661363435 661363447
    0x110c011d100e030d0e0109033b03010b0d03020303060f1801050f01170103320726010906020c0c0d1505040311030309070f0909051906090b13020f15 65
    0x1040381c005201c081c10300b10a40b41480381981002c1c05441c0081560300e8165900c4854004068110004042c0b00c000041180c0307031f0b808081d8030b94061003041102c20200200a60000e5000e503402d41202e540c0c1700b00580004050042864041d50b03d03082511401d1081a0045d000b00007070402c01d40f0903002c090201c1141e0b407107074a802c0500c052420a24400d0b410845c0900c41d5041d02c1e80c044c8a481d000314402c0c5642c40d01440110500403402204540540c6d8029400e281d000d0620380003c1c0850596600d5201ca000703400700c0803020031206400305210782c00c9509000d24001030044070782c00340030003112050580710800300c144200181e4025080c002448503070b82c0d01c102c144801656000650051083c00c1070030203400d408099130f00e540c104841c20714456200c0c080900240003890391200c0140801003084c080b1401940e2000e07202c1e0200a0303640460441503580311b05001254000c0180340d81c20250790900c60501c0486641002c481030016800b131054a2200000d030f040c08141c03a89400c419041c4c0c581042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 661365935 1250 661364685 661364713
    0x609061518070504080a2a0501021b03240a1d06010b0f0d0501140103060e0c0a0c080d0c02070f140d06230c1209031204081606110c011d 60
    0x10800b070040c0e0708200040c0000714284008002c0ca04e00c042c01000f4150304030300020003445180c1ca0340c820583c89102e1040007005681d800103103800b0500b8030440a05404d441180210380740c44628070311340710180e40785800040c8a000e00544036001e0782c0d0103642800041c2c0e0200394649520240b881d880547e0744184010401403c010015150801040454601c0c0501c03525084096800030f1304a118400001841027000b0740e003600ca064000c021002d071482003454403488019460041d640120107101903a03120a0030000c10b0402c440d40c1204401d81086810308a010095940300c2c035000d12014640d5080c0d0101e00303002c00419240d48150010301d87c0c680e8548036036a802c00b410408211030b6840d40c00040303003801e100101c0040b84c403a400c20180d01d42c45034030701c072494056030744007508040254100f00441103100207000710459100d0f4110034002d03541d0f5a40e807030344000106921300142080b8a00555154140035404c01400008104002807000c160280080f084110b1220841e508903030040f1b026107611 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 661367185 1250 661365935 661365979
    0x601140a27081f0b060706050717150607020105070c12021002070f150e090f06100e13090c0b030a0906050105030607021e10060e04031722020d120206090615 69
    0x3c82d1100304041034015907035001c6603841e002154220795950702c0d07004000d441a0f01408117060311222a250712040d080c4410704131a01c40303001c00c040c2d010b408002204030544e4001c01c01c40e14120381c081a41c03802c0d103540340980c2c0d5944031410740492040801e1416070840d54400100e40081d144d1100b0020341c03640c501440c4421901d070941002040c4419035440141a0b0f5401112900c40c6201c210944040d2070f0410800ae24075104c0ba082d901031080310700071030a203510f5501c502e100030b01c640440054000e00710300f0520400b80840e4001c40c5a07070b100000b0070034a001c02d1381048985500c03402d01480140d80b60420076440e01022121400181d1010607120302c100808500d061000f0300d080165007070402c2d081059020b540890b082454640b101d041408100b5501400085c28201009081441401e0416401c04ca069103c041c20740c10b11001e01142c0103555481020a020075030015941c2080b0900c00c0e806503e07070600711055200390040000040020400035250102003200802441c840300140006506c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 661368435 1250 661367185 661367233
    0x20301110a08160306031a091006030c17030903070b07021008150d0c15021b030a0c090e03160f030f020705130e0a0206160b060d0b0a02030601140a2708 67
    0x10941ca561700000404e0384054030940f8448100850046854104020f515108002c50442c030110f140c0b800030400b04070480240020754422584069038003001d0f01c3c407a891409070309021541400340401c0011040c03c0d045c010101d652003991402d082c100c3d41182910130600c11580104d8440141c0c0d80d103103241c50074051710700d203480c451481d204190f80c13102d105080c0e0001408015002d42c1c00710f2500589604000c034010300f1250101c000344503041d10f654171055541040d11031992050b817a0034112611a1081c800d640c121803107602c1000780144030381440030791050241801d4003c200f20401c0c0c0c066413840032400800741c44002d0f1204800300f070507030144001801051122140e5000e40c801030001070b55060300034a083c05000022a00c00b14050034074068440b00501014800e681150070007000510f22800150f00c4945007800585a42c4c40300c1c016030749001410000b201c88035000400d0720f00c05404c41c1101d070b00602008114004846000d2618280725640d00400480b9405982403640100580c001c0c0c6d03070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 661369685 1250 661368435 661368437
    0x1205010906150603060b04120f11030634050f1803100501030b010e270c04110d0605030c1309030504080d09091a0f0105030c0906070c03020301110a0816 67
    0x24200036a03403514011107901800d41a2003a41407441040066458020343d4050314260704a185880c0c940580040f00d040b00d81001403641e00d091040300180720310091000010800038065610340d183c02c0140c00311010b100ca03000403910005261481d059a15140d401100002d00c3c3c0b00c2a02c0c0210307961000708140c101c07184515540304441a0900a0344050140c000018408040441d003035042d4544403000c00340507000144060a07800030412480e072100c0c2c03500d51100721141000562083d0703910541c20003014103090b940281c24420f1101006400704000d01a01d80500000c00040b5150070805444a030741c07800082c2d012109980180c8000c0103584000c4036a4820304102d80707055175801c9000d082072410030040c0081003029104000c42c18041c0a00102d0303050341e030780702480103003a040015205443c42c4501810080c0105c0000c140040900407030f00d6414004104c25203540541c50719105000180c00308078002c0d400d22000c109500404800d447c0302034200d880c0c940d030030349d2400b400d25a0503964101e010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 661370935 1250 661369685 661369691
    0x6090b28050603100f0e09061305030702100e040c360509151207060207050d1a150604030c0305010605060405060a030915020313020907110304060c1505071d06030f01120501 76
    0x1c4000b105c0140500406814075440e0709880d1000c0400e0610320001d000800300021070301c82100250011007142e000540c11648550107109030181180e01501010481e90007134689800019150b401007400741059010400e00c00360f44440c0f44502130a00b030070307080341d140c1121108020f00252620190440e4040220501c102c03210400701c000800082c514008110702e0b4011100074441e056042c0f052001411080e80c0801f060500d0303a4804031001e0481c0c000901141003e00803401c201016003050b030000030001d040d25241d03600d0f41061046054903200c2140d580d840e000000803a410320300190303011a40005c203214207241d15100c00380c000d8442c011041b40c11604503900200020060f101442c000e00740e046d40200d02200601c10310001aa010304414103001400380d0300d00c403410f400012a0103a41c2c491074480644446407030720900402a18050402075400d01d0104042c03035a2107c0c00440802d0880380b905101c0c07100c107091040300d11040d9481c45100000200500502400004a59105200340000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 661372185 1250 661370935 661370939
    0x3064905030a081b030609060103090c03080a0f030f0c0507020d03020316061e09020306010501031503080309010c081e0402060a050d15051305090d2106090b2805060310 74
    0xa941103a01403580707031000c00c002c80c003400005034000d44c81842440584480d589141410701c0020310020008010504141d04c896149003003004840101d401560701403d181d44440e25044040c04000c00c000842c0d000914080a140d80b5603028045d041445034191591460b016445d000d000440d080a0b5055065100400040e0015800340c0a14035119020307450004615800f010203010050741156000300c42c508104108001d42d0700400d045044550900b000180840284189070f09210281e0000c2c041000201c100801d210040d04110b01a00340e44c0e65803156680d55081d40300422214841d204a542c1d20000020b0060510750010480002c2d42e05001c0d08100c812110101900c402d07a00c043c9100002020802103428861240b0903620040c42d428445464040303c03e950720242d028201c0200304001034603614280d0704130940720640100c0780080c4206a2640c40c400042d00c600c0c1e1105004141000c00c3c40382c00c1100c0300300880c8214561003180c43c0103250008102c00c0b9080501080030607c445840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 661373435 1250 661372185 661372193
    0x3083402120f070f030c05060a200723090c070807060c030209040c020c0306071b170f0a0201050105180c0a0c02220506040e0a03021509010b100203030649 68
    0x4070402801c80e01101004c044c00e500c6c2c84a0480501e6101900442c02400b020085a8004511705220b49401b9881500103540c140707618500141640000415440844481941d00800b007180f144240c09841d50788a80c4c0310000012141d1144e41c002415001c0240484400206945c000840319a80d910340542010090000601100c20840c584800350740081ca03181e50b9410b050204c1944031186003800d85100c2c1c500c0340c24600052140c48020308090078410f160003644150343c21b07034041d00194450780d03841b0008440301a000b0300d404c1c01642d106075022102261550801a81588101030311541c280c20403007041070903a401440c042d03049074007400ca01000514050801000c0d088541929000314031410300b0028001283c41d55600002e0540020f445000402d4001610b1642182d51450510107582c540c0c048034010440e03135481c1540031084c009048401940000a94040c84080716201c201034030301d440401c803070b400200924200e5554003812030307020351698001000c9031010080e050766100345565 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 661374685 1250 661373435 661373443
    0xf030d0c0308270a05100606170408130e010f2301110f01020a120605060a0c121101090819110c0607080d05010803031b07050a11120703083402120f 65
    0x10320b00075800f03603500c881403000c1040309520640007006d0402c041824031400904401041d002c0d80ca00341c81503004a0100618101102d244007040c23110b0b240c07407a4584032080d503409801e104142580c0c1003601c000c2030300c8262180f0786114a0281c02d804407280f22443c019a26503540d43c48884042c020320b84408207550080c0024030415045039908140380350707210300740d0040b908650080740c041d05080c0407400c5056000000003c5054114401181443c00c1c51000c4840361094800240c0710350038070300d4032001c00801c1800380c400311000c0012071800002d0004112500110080385040c81e0b403100004582d01d017001c40c0184071131405001024a05444020220705542c420707488000240c1c00001004080740720a54a1400303903100202d0185055259243c613030b0b9466040c4400703400c010142c42740b10103a580b07002d41000725440405c183c8450541e43d082801103900400e05e4000c240410701224003003040c030351080703050001507440c0702960a0201e4091200c501e07055580c848540c81081104548400200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 661375935 1250 661374685 661374751
    0x20351070f0f0509031e0a08040602030901090905280209030a050c0f0603101a1c0b09150306041b1e06030f060b1c0f0f0b0f030d0c0308 60
    0x103220a440520450310061007425018041803c101d4148008006030754045440117008510064551000032032884241c200301044070010301316800090300181c20390f0044040c1c23081000036240c4442da150f8400d2584251082203c04454910110150306c0d0310400228000c0c403110b0600d1130041c28540c0e04c8020925003d01944144c4070395222480e0b40301281342a02101c014428240c680074214107090f00c5252058000340102d008140310034281c2c007a218101420b85070b115208001c02e000610101c6180c03001054515043d42c01000d208000074288c01c00022250030307085000d8000c00480d03030f4070348900c80707166483c1d1104a01c020595000003490701034082401e440100c0090065030051910320060120f030034007040d0a000c141003410402c4504820000c0c0c0e00941418000c0041d031800d14140d05005180e03440c0043e0b045860030710b900c01c1d8034055901520004001741d4950500c22240010903a8a07044584c1c003100040c3c4014080340080e1003410440d40081e10200324114440d0070164000107070000c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 661377185 1250 661375935 661375937
    0x41205030304020a05030a200102150c0a111c18120b070201051509011401091e0f090b09011e05031902010201050f0c091207080105040f02035107 64
    0x8424001036113000c584610050104400500e14007281d0356500742c1000210514100c40da0580d500e1b02d0b240d034002e0007082c0910580e0306846d940b618024964502e603411014500f0300160003070351500280304000034209200d59000101d03040310103448000302e030203880340710302c928512203411800074155103408080c0a40b940b0400150265140450000b030031540c0040c409000d11507200040714443d280c2c0e55042d41900c0384440d68401521107003005075080c3c00b55510800043c1146003070b01407131032024a290300580b0001c501c080b04290f5904007134015030300700c24003041d80503805200401c04c200c100040d040700b02c1d06610b505410a541e03100000e080104c92518130b00890b000300c071090115030342886941d6002440c441801928101082506490b0065000803406a68410b28032040340c002005198004d1100700001d100b2031506107425003004d104c507501203000340316043c22503180a203207800d8155501124000701c190b03203000c06520408090000d54020039141d2600c040c51180006081451062034a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 661378435 1250 661377185 661377187
    0x50a050708151b0c150901060810021804020304020d060e07060305010e09060c0904061205030c010c02060903071112160510050a140c0127060b0d0816050304120503 72
    0x3508510909245264192150700c220a1040080c26900d000100e100d110f01d482416844500a01d59545072040922510000c56031000c00c00404180541103030085e11800d0094642543d00b101c1d2480030380c060080c1c110004810003c0c4616141805d901643d4024001841c076449480c0c56150b0404441e00860703540300c507400c811014011240c150041c80d0060804e0380c035100151a0100d100c40c0c0f2800040c00140c0d2215001030b8030003840e616a0090b0002d0311a051b00760303862100720324015640c0e40c0081604c0c035195085c0340581c00c03894000301e001c521039001c1e040a54900111507603a00300845d2001d03e225401401d401c410500307003c3c100080480c201c2548a003508060070002040904042e060b02d0703004000d800c116001d40c0e19401800c003683c43e44229036003500c07209030841e040d0240803400041002c1c1b6002c00581c51060350903001c00a041e0340501003c00c81c091441e41807111260003180040e201e4501040310790003d02c800309032200110301840949062a448414070800c0242643c429903c0f540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 661379685 1250 661378435 661378439
    0x50c09090705122d2d060301050928050a081602012c1203070f12080a1401051216081e030a0c081305040504060c020d1814030703050a0507 61
    0xa103040303081d500052030400311070040806144e10b03044c1070a40c0e21240542010314012030700308012001c88100c0d104200300c600315240c02d00071700782103c0710044507003500c0b9600341400f1801c503880c0894021215480084003c1040030f214080500061040f00102c07494803c00480b0008a244d01c0080c000c401780c0500142d000c400d40e07000050602c810010000804162001a854103900d02d1440050505058415603402092010203500f907000c1e2440207050a01c008182000700400c0503076410075601d268607005229264101140102d03500c03a0707001c0e180d48101b0320041c4a185031078002160000b0001d401c4442948204034007011442540c0d00100007a0f02007020001c03800c0c00311804420210760a030045061104c1000c0c002e01c02e403d0080b000e05610400030b401c0d00b090a80f002004c02400010301f00f8001400d01d407030800003e0201c2400d410050003040c072001415841012000c01031815800002034440c10b025032508494100070032164144500c400010010f42c0512110300d199020350080d204882c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 661380935 1250 661379685 661379707
    0x106261303020f1506150f04090b12010603050718021e030106120b09131e0b0a05090c0d030e010c02131406061c02070804030b0907080705060705030409050c09090705 73
    0x910f40641c038504640003e83c0c40044e60403030120895008100300c401084c11900602031401510034070070034008042d0700241c0070554840b250441c050300031040e65458003000040408908039641e5001c0142190840481000315607800c2130380601044a184006113807401c01100c40b00d5001040444403099000480100545a04103d40510354002484140206c2c21182c000400c0f541e0300403c80500290521814401d02003020340d8400e0601844007405084034050800d031303032143c8007203601003001c03801c180000c2c00258021402040141e00909000f019a0265406540407440d084609042046910368900580d40740c802c0504094681080028600b1502d0408001074500400203401100100301e070400c068645a600100c20884000042c1c42b62210f181944a80c400c039400a000c292003101402801e0a0101d50103084990060465240c0c9541c3d07003e110303050049403409040394100740010400025281c12041d4000c000c207540501d800c148100041031000706031071100c00110080b64000c22a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 661382185 1250 661380935 661380943
    0xa030501090f0c080105120a050d0504150c03020607030506060d0c0e0a06090605030c0705070909120206070810030206071a160206090703021f0e0a090b1305040b010626130302 77
    0xa041e9550700f44210040c16401900740e40041c42a0b41c0280003021007951008001d00c0f0a200c25035201040e0340040424850003020354005000d04c1440071000111690903d0041c200e0502c203da064010f80002e6031001c900350000c0400a040340e0300410308106840c40d041c102d02c2040030b500b80c1e50b21840c0f11140450203000c40000b0a40166041c00701080050180540200070341e5030248860b00240c2d504c510a260403802d0501950203030a046061098241c01c011156568905414003a4201e814030b66a500c811940300740203640941c2c0c4240304250500140c2014001840011b019100100044007145901080480c0480f4249030484011102c010f0b401c0d0f040c404581c000780c1d20030082041c3c0d400c540018582270f5601014040d416004640d9101450041191038008100104119101d5035642c4110002d07114205840d0321031800e18110070035800384e40c49600c0c002c03508aa00c101441c2e090103410f58840862a102e1100540d207a4904410400d40300301c0184600140c415902300840c0500c1c0117850 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 661383435 1250 661382185 661382201
    0x17190311070803061c05010c0c030210410f010312170c0d2d0b030318100c06020c0d03050702010203150f0f04090b09160e06010302090a0b0a03050109 66
    0x8903100030020100440c0e140d0003a80d03040f0204460201d00264403042d454a40d50500780010015420324040c0413050360085407c038826030094003584c08540810803035030100c03034002d0080c03030910601207000c050081c0045000b10542040d403d0b50f01d01c2d001b02c01284c09600c0d000300c812072801c4922100600800a000000c644109a00d052005001d44008440200c00400400d0303148240350201c0d0f14200300c10941c00092a00c900d616001040c114002110400c3c441401c25021036181802649000c2d4100081220125520410b1410a54140b1000c000320074103040328640400007910301c640d001c43c9039440100382001c0d01900030a003201b1206006403e55400910700304c11b691044c0100040001c003031405105000d0111148418505100c0c00940348801900c5aa500103141c0b0010600304a410741c4510b01607001502198a40000d000c00041d10601c14028480c40c00702000c08a8000e5000e900903020388400100b18003e06a02c56a40b0481e42c1c00c030b040c44000003070302c40c001001450068419202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 661384685 1250 661383435 661383461
    0xf06020d180e0411090f040618031436090a2702060d020a2a03091e0504020f07030f0302030105101d060a0c031707080f04171903 57
    0x40d184108100380d494040d9109070a00b12881000260401103141078103224a03100814002d0b86042041e400150454126801c0343c80318a070010407001c0440440d203151900d5403540e201148041c580129116030f801c6403041c03090407610b07000988e80101c0f11103a0480290010340305100d040b031200040106004000d01503413155850644451403607100101c0321001405c00f5017042c00941120300c01b28119200c0c1d015105940c0d84003045a058455200700068120003011040b240c02821080b402c1c1740c006000c440c01800b25091210800c00c50099401c440c02030914091003602c0190745801240c240d038010f411030042424005030050815400100c41214a1041d240440c11503041a02203440e00e1003030a98942842800c51003c5802d00c41c0c1c4088030700040025004a40301d4080e0203003d0010b1000344012408604c101a20055951600803034520172f04850750b600d09541c0f135501c0300144401020380241c582c17101501411201c1c004020091102d10840e580440d450b076601400201281c0f20804400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 661385935 1250 661384685 661384697
    0xa03050703050c03070c0203070308030c0705011128021903030507110d02190203030d02040f1503020c030706090201020c100905040e1614120706050a030e0109030206041e0c0f06020d 80
    0x2100c5050a00144da030b01041c0c07030030b0442c1000c44600020f031a21210390300080c05600004104008040ca060103840c4203403041c03009102d045c007504c50791400e0307029580c0181100c00c0c0107040c0700300b100500e0310b00100c101c045006441c0400d034131140c1004450703184003054001c80e484000344030609038004055000c8110380009060041c0300004001c1d2907003a43c0e495103081c440103140444c155034003403045a022480150046558176a0742c1c8110354403a02600c075040d02c00e5026402401d4603070003402200d07988840c0c07201030744c80d00d14070359203500007031505407400c0c1e045102c4c2e070030714026545441c0d20820035902076803070300072003146841d0030041940c0d01481130303040ca030700000e6100010140845501099a4505241000c002c00700004148505500c85181226100348a000174420350080c0051580448071ba50038080914695241d5090b102d00301c000400590164001a01041c940e0042c1000707000f0030020000306a80b662120075500106030041420450401010022550104101d0304481d10714100b40e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 661387185 1250 661385935 661385941
    0x10212221401021228020a20280c0b03040c03290c090312090103021603030b090609090a0f081903150e0705030705180d0609020109050301020c0c01030b120d050a0305070305 76
    0x7400c1d03540003000080d00c80ca8001c1f078070318561402651200f540c040d44c00981107216040b85a07035551100c0c0b0086e000e10411207100004440c0e0150f6190540440e04a500d0500c2c0510344814000749500c02081600ca56904030b0000c80011030800700142c900314055203c0c40c1000704100240c850300000b803c890032400003088488025100824508884080a65940e446409010059010b442418448804640c00d201c0c1c00c1c0401d034145e4451a101e900640c1c08807015030b01ca0007031086180095650301400d074440c500390f000013104030b00a560202e05c2800c9035801c0c1a0f601c04141c1c0007860b52054403000c40d0311806444548884d0400d96402480c19882d05805410190030140003840040c1060342000340000c1e420031000c43c00e030030907540c4003009040035806010320304000c00100f4100c2c1c0c1c00c0303001800ca0b40001419107014000c1c1d403506d880c071001618014040d0c1c0010750040c17071110091500304014894144000c0402e03c03040003022459216030341d6610683c180202200c40c01000c04c07007803505c0c010078 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 661388435 1250 661387185 661387231
    0x803040c05030f280c0305160506030c0d020c0a021f02060f0f06120a02151210050306010501120e010513031205090706120212150307080102122214010212 68
    0x4184004c0d000104029140c0f200440c1d503030410710380c050024007403400040e800800c2040c00120402c10003600c04500c480e41d600c50781000941d00c010f44241e00f85660030320041080304200d03030007424160798000c00c0344c0c010b00c1c150740860081c0c10002c45407601c1c090f0814030380c04950703014000306a0001d035a004415051408a16006070f25074058140e17130050701001001002000c040001a800c141c001381a44403440607000400000c1d40090400003038100c212000c01d450298551020b01980c000a000c1d01940e800d14004440c440100c64010445946511860032412030a100e454007600c00d1030001d4a0000081c1409816003102c02c2411510070724180400c0321480000c82c0c2e92054605516000c0b800c50f8115003284041d00942c1d0001144401880c01d200b40010040624612040700740c007039075401c0e0355400f2428201d008543c00c580342510200002421021001102c010b038009542c4200560240707a114000008400c621b4000269400030b211184504801d960310f600c6243c40049103800c031b00f603c0f6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 661389685 1250 661388435 661388443
    0xe1f0513060230060f030d1706152d190e2209020a080106140f04020c0f0307020418030c0b0c0c250f231c0803040c05030f 54
    0x3101922550380840c85090655008400e0010068070358080e8030329950602d1440301c9a6415a5a14071034100440c3d0301505007000314034081002030940300c12010038085d00f842e034025036008050940c8041c1030450b00340d80d0030720369010303001400a007660180301149030303001044a403110442c00c1d000c000303041c0700b01b60502c0d03224652507900c1149403600080c00048240426039285050214a00d101414044110b158906501181c0a58022102c07420340c20342c0c030102c59080301c142d40200001078541c90042500c81c10700d001d003c02402409000145850182010320303061203040204000d00350030010340c40c825858140508030b42e040e0900d4156461a81958006c3e082400700c01d0001e0070b80030010300040031031080f40c0c00d55003440d2992040da031054000c05000740d1413000e000782c6000c43c4842140041440020391001c0030a4550404c0c000c00c00c20030240040d040280380d950301d10340c0825907032280600c540e00001040d035042d206003039454072400c0525048804481d50b8202902a610034400c41224102c002 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 661390935 1250 661389685 661389721
    0x105010302040308071b0504020f0706050c09061b190b0a2d09060f02030a0603060513050a1b2301021e0624060c2406010f030f0f0e1f05 60
    0x101c45402c282940030703840400c0c0311b040d501c00c0303501070310204400405c1030302c5100600f6818400e2400f0010317590390b8020b001403402290b108580040c001d12004401e200c040395428114071504080341c03c42e41e9a80c0409030700c0b50032144219640702080082c0714981c0410b0041c0034002c000c000705001040c494191641c089541041d5045403036840e0400d480a12541c1e40c045000d40c041c81d08107540e2450894813081c064005032004840c0c3c5450302001a0b8622400c0d03014403480d507402400740070b80c40c1d1940c94550355482d011003143c0c400314222100240394103243c42c0b5071400c50440c01402403203d0718a0300281c2442c0c09010f00004807072500319500404000814159403000403240801002c3c2c1d00919507a081241d15100c160700031200003030000c00601e00068520361004400c0340800c08840282140c2500001a1080340c0843d488940000003207010340c001c0b5840e0a800c5030000346440100701105d00742d4101211503640c1c2e070882d15070b652054020501c4040450003502e024001c0e0700703040030b890b0305404582d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 661392185 1250 661390935 661390943
    0x140d090308071e0c0303030203060f0114040311130513030e0103050f16170c030109150b030a05310314090d060c020a0c060504080c012d0201061703040e010501030204030807 76
    0x1c00d0341d0900b00940195803411560819484581346844e40381c040c000750300c141c2c1c00a00c900b505600741a0341d503214038404420110490300c2907087c640740d41d51b07228417502488200317944074030b100380ca200c1c2aa20034400c0d1803041c10940d5103081c541c0490308002e083c00d030240400c40e0406003410100107903405140701071504a500040304001410084100300c03034180052003c0000482e05005000501544070040d505840340300d10204400700084840d0f40e1603d11510460354121000c1c0b00240c182c0c0520b0340815840344c518002c4481c14991020340044845000c0c0e104144246800f840c0024140e000780180c000c8000c0c90340301c031700d0810721000003a101502d0702802010151100a01c0c0080c500c01c1c090f4111301540514020740d056201d401c0900550000e000d0107045104140060711258403400807090940c1c050f4103182080f9012801c105400c1040d1504c4009540d25124000b03008a4250146514100301d54041c58075581014120f584030801039007d181090b0042c00f003070011490201c01c03202c540d640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 661393435 1250 661392185 661392203
    0x1120912110c06071406010504060e04080a091203111b0d02060c1513030212070314031f06020a1b03080a110111040f050907210e03090409140d09030807 67
    0x40c407992500580e00ca805400c400042607550801041c442801041c2c40c0354030589120780c1e203806c10b001c1194128031442500c10118030116010a46560007040201c075940303002c141e069103400b0318613080703403c0395411800112650b400781b40c035400c10b03c0152002e6a82020341d004051050700011098080040081c2c880d40c8006246a482c8004102c1e201204a45a046052a1400d40c0c3e4454403801000b50603005802402d40880340099104100c4e0841c96264550707000d00c001040d020000c0750001002c2e14000a41120948907001800440500810140e401000000e40516081e000011203010380041190054010300014605505960f4000020b10340b80b040c00da506903d140c05060060010348000c1d07000100400c00c21442c0b01c10009650040c0ca00e02c0b155202c001040340d14920423640d101035800e18080307084844680d500100c0d14a40443c044900b05410100000c0c01c43d00e0902c0211000c0482250700094a0800d10003240c60b81d60500b880358585286856401c030f58860000300a0003400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 661394685 1250 661393435 661393457
    0xd08040c0501030c0c060c020a0b0f0108070b03150405012c011503050403020312130309080c010f110f030d0207020405010605031b0901090e0708041e0213270506010501120912 77
    0xc466408080707006c0d0131030010700c28140c0d9040b01944514007074505840707445000c5d00049024040c060a58101c421050040c500c0c031f444c00d2614280764001406100f40c03621100381e40c8500365034601605000c1c210f0080c1c50402141012031400d00e100080940e1110106081d00400c01c2c0c48140202805169060030045a290b40c1d034982207007548514150345051404002c10700c195086210fa052400038425100c4041050710381e540c003507031116040c01040c0000d20841e40184824441c201c4110041650411114550a0b100046085401ca09121020746e50f001c20000d05500d407501840d401088107080880c41c500b000e2100c6103c21050f1400720818001c0003400d0340c4940d104580c00d40040940e0308030450300f030609070b10003001020103607030a840480c1640300c80700c0d224220074024031066074020300781c0034a40302190352003024100903094456031809603204040340b014690612124144100040c0c0400d60400002504100344513650a2005d450701043c940050b08a04150b00d20140d18144010451 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 661395935 1250 661394685 661394687
    0x6010306051503161a1822020d15050111030717071208040c06180e1b0408030a0908060f040b04061d01060302041b090b0c1006170d08040c0501030c 65
    0x300c002c03030320305805109210903618156490805a001c1e01c4001c0401e04040841541d41d0746107014401c0401c001c0390300d450003c102803070414048146d550f1000b14444013a4001c0740050120382090720300150680c3c0340e10385804d11111245000c00500000d003440440382001c02185942c9001e65030000746034041500311000500600010360701c40c03550200414502e46122500140120401e440807140300c07170300b514082401800b540041c40600c00380d0090762022881d1900f45104000e02500480b400d00a50040c8107281c4210310051010b401480001d59031000d0380c1c03000401c0aa42c0c1d0f8000920b40c5c011006000d11001c0b0142d4140d00305070044035440c425100c034240000140300000051000c40c80201c1144941c20040d00104101da00071181040b011160407080c0101c281c0107038042c000140c070702800b400031051042c080d05403240b15100b111148104028100100c0e811034004c041e180b6140f42800304860000c20062520b0511440c0101840c10a170f90f501c00366030300303901500e414980c580117404402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 661397185 1250 661395935 661395961
    0xb0c031503160e09060c0319060f03050a0308074503030818010e030a03090507030f0614070302070201090504020f0d180309120f061e020703020610050103060302030601030605 77
    0x454004003a10307101d031998800701c2c0c0440600d208110300d515508000400204c4082446840f80c0c500300049440d41d42c0310340344c40d8240b83c580007442400c030340e60324004035490310360680c00030145100750014a050881c1d410003520312007000305010f04001e42c00740d13030640000c9481000742c4074101200944580e014248200400004d9000080142000300e502c0081030550000205014410850914441c60511040e840c240d03030115031103d445500400c51040d9044c82036100c26074250061007a188026141e035111858801000c000717507039440d124031050030300d00c4502030020341210700b9040461800c40c0e0b5900113081014a88121881154007094038180f0340000012200030b8100e5110401000b038002003401040c9006070400e0340001e805c0c4801007541c2e5008040c07071180035000341c0058030240d038580e40e1101809013a00c806006800c001c140c4204a00c43c1e0000e05442d81c4a40c0140a0504e001e115000f25844075030b00580c101414003c1c10800361710045401c1d03040d03a40011012645580d210192410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 661398435 1250 661397185 661397221
    0xf0509160312030207060f050406110c0a1106090315060103060e01140909101e05150a09050702010908191d011205060d0218010e060f0f060901020f0303070306031e0b0c03 75
    0x505407c003d11306581400b15031007103100d00e01c1002c0800c1800b0700d60000d01c003640a141e03011119680890f01c1321002c2401c0b0708984100000041010b8074003010078011a0508010380c43c110f02c0031026400f4458250f8044c000c50001d000c5030102a0060f41c98040c4841280c06501101e82c000c10b50b04012414400d001d1004140c1e11010500070b000c0948048011220070540707291402c400d920349004218080c5400e02794241518000345482103103401d1030b600400500000d03121205542d40d50210000040c540809010740ca44c2203c40c000002c04c0e041405850710750300c48100405e402c120309440d0b9060381c1050460358400451040011165a00c0010850100000602a42c41807a22003494032115040402e03038165901340002e85810b840d803006020140360300c070400651140f00c5032a08511400c0506c06040c040702c051044841c0c100c036400b84075045034000e40b26200001d40f106014014080103070880d030780c0046030308400b10082801d038590305409800641411115000040031a01d40c4a1104007200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 661399685 1250 661398435 661398443
    0x121809090c122a0504050c09030a03050c010207021806030d140307050c0106211202071202060904150e010f050111030a180b0a09143a0602030a0f0509160312030207 72
    0x126218100f0f0124084442c91248500c12400c0c84009070041600a00340c0b241002c018006100240b515501070b9080d40050300ca88159641c00d10410340541d8030042008009400420f03000c100f070400c0340625040001c1c4480d404140322072903110402c912400012203503c44414580f5070744500b00d2400403805461030b68040440b80007800104005000003485142c4100d00c1a605045005501d0409a84031034081c0f2409400005185000f009030405500404c03440340e0007880001c21800900082c0d44510003038204030a00e080d8000148505001814003a01500f400d00b08034070409115040c03555248aa41810401c21074a89410041c02c1ea07203008000c044d04208021a4484803c4003006114100038445e0705a640c121161281203814604442c01850344284000c080462101107007010b511045040319090030320141030100445c0044c400f07036010f04030700000820101100080803040d40d1003d072000485402c03654a403134144100007100f1003103e40c04003040440c00b0b0003507000d41c02806046c0c0090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 661400935 1250 661399685 661399733
    0xe1e010b12030c070e070831060f0501080316020d0c0305031c0c0c0b070e03030c0f010905010506010504050a17010f09110306010b1314040603121809090c12 69
    0x101c00041c0100c050402c681c000c2044403010741d41d800100440c2c1130207035100804203040c01c02140328800c40c001050302445d0301800c0361001010301040034041d10120721003526070340d607161448a0f044003c0d003d024010109000194200b15098520213402526020001c0c031542600e0113080c200507a13003039141c00854010007580c4c2c40e6442400702141110040c1e4803810110700e0000060003150141102c24482c64109000c0003844d59400c00555164007642207090b814401841724003c06101000b4036650b002c0b0900c000309a0404a251890070358801810160500c00c043c4003c1c0655244c400300103080311341c00d03030340c45c040120130344426030041045030a2402003505040300b04080c4000510b00400d00c840a03021207007207a9807141020003070b01541540824a01ba40300d82004030040c0c442403884030000081c0000341c055600d84d20600d45811488503480421081c40d07030700d40714516400141c40205241101804030f5203403030ba1402e0b412000ca00801070040c0c00c44540780c0901804691070414046d83c01d000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 661402185 1250 661400935 661400959
    0xc060902060708040f0b03010612020903012403030305060f220917070218060306011a0c0d09170712060906090203100e0f030c190219090504150e1e010b 67
    0x540f51a0b4040c0c081d003d07003140b000300300240300103c881c2102c2c12908940e0320410424000c10401001e9806511125071640d01e4600c5658041030703001080c0380c1c419550007484e490341e203035140140503070f00010038451041c00804070342059901c1da0a0340040480801c0c10540c00c06e50380105a900030700e0084405400e8011501007019000130070001059a14000c41d0380384822071041d43c0c2441402021280c2a405030407602c010051200300e190b0340440000b520310310342c0c1400c9a04414134580b00e40321100c01c0006c0c41040042110b0110b401130031011300700002c00b03042014144541030103540d100e060003c00c155902e4100e1418271030668801c0e40e2950307005041e82c0b5003910009810b40504000000000795004103c000c0880000002c201c404e035100c008007400c4106909045c180a0040ca0700301031387c0103c03201d40c8048a000c1c100c48504082c10410100191909190030003080c1c1641344a8002c140a01d443e031034408450000500a414025000800d810941c4c143c50740f601408042c4234154010b00401c400c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 661403435 1250 661402185 661402193
    0x11190b0c01090c141806030f1f061523191110022502030a0b07170c07051f06080709050105130203040b07050d2003040605150609010c0609020607 64
    0x10001c02c050045000085403611682c50442c0d10784151052903200c03455110b03100c548100780003a10350140008068a0300b03903460410841c2803800000d80040344842d40c1d4242200202c05104080141c110b41c1d4801c1e030302d110b000302c0243c801851255001c0f02515652041d2030400120421105401c1d1039050415070010300c504007424100c607021440801c0e01802c0b000c100b844000384203448181603030a41d00e107200c40c80c0183c421060a15094281e8041c002e003001c5030040b0710395629550254000e40c2e40c401098284006080c40d100300070b071070070511039010006140403410001d8014000c1110900c00362410400702c203a0801048164010300007400f941c500040e404259500c1141242c8055441104031440644078100f00d00c01100c0c01840e40c061000030a240324415005400c80d20004200024202104a0000c0c0440c4080080035180840042000b040000d14080ca5801110014000304d03650142c2d80004d51500460010318100180c05140006001c0c182c1c002448554014180d80d036585000d041c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 661404685 1250 661403435 661403441
    0x310050d0609060c180e15120a0c0503030702010e0906010c0c0603020c0c180103030525080a1e140702060712051909081504020f0a0602030a030f0911190b0c01 70
    0x94141c90043c40c244c0303c44125030003401000c20007000b081980c1d40392818800d0300881c807800540741b04000d07104080a00c1094640514482c0c1050240300213295040d1b00c0d140c0618600e4182e00854000d810074010800140d8001c94140c4092a04603401c204035038441c0012510040040741c050014424040d001070200e030580e0040400c450880d09075030300000320f001817000c0405111484501c000c4800d0041002c80d1046010f132161352103a0384c0800c121a044a40d080381c82403c80419103c122001070071900881e044805803941d5440f080381190151060382c0b001c0c2480343c0810700f0310300d41c01e00020307d0f104554400e0100d9400301d42c484c0102841c1003034090014100d82241c152000c2010380c544000c0a00e40c05141c861003266550030060201d811200002c08520701c0c0500200d8001d1804500000310382d5034802c004014100e1039008607141c0050b01e9000f815981543d01200c0c5240c80c2c50160b00c041045400150b41c8410107403800e0b450958141020a44a9040d070300c00c05006001140455003810190 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 661405935 1250 661404685 661404701
    0x31b01030c050702060a0806010903080711041409060a0b0d0204060e0108070806040c06030c1b0b150409080d0e070e1006030609050106020322270606020307050d050310050d06 77
    0x2a904125007401c0880c1a1224410800041d61240d0305202101402e8030420304603604c6013041c940303e0030b1f0f907569642d258540d401c83c44084600400d201c0f9983d0710b5003000d2059102145000d40150010b05004a00c5a00c802001d0080c3c60031a850320030040b0291107810443d0481a8040c0c810031101d030f81d0340100c140c1c111003030113030710701c2801180000500160006140360155400049414000e0310f420029802020300440f8030042c400d21441c102803000c203600045582a00400302d0103101d18021410300c0303207060307283d02645c0320b14944800c10001c02c0300101500c010312039000c000a200601c40311101d103450b0071544600120b58080d0200034061142c40c43c0c100455860740c03001d0209a443e01e0100c81510300900610380103910620028210300c0f1042045041400311209285407151102d0210341c3d80511408a034806007002d43c2100c1c10000c072442641300601d80c40c0f01850409002d5542c3d541c0710302110030f00004114010000c140300d12088002500180030040011240690700d10305500130380400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 661407185 1250 661405935 661405937
    0x5030417060f070e03031210150f0e0a0f05060d090209040c150518010807090801062603040b0406050705070e070807260a24030f0507080706080a0e010b031b01 70
    0x1102c00708802d2401412202c002c50001405581862a4401c00d4104410300a0100c100442403140004040c02200c1c501081c03606c003035940c01074071440603d016022000b0004082d014940b56141002001075640c010001d48004075079246e50b03440c001c280403001c1c0541ca00060350203203819060108004a0032403800c01c4429401f0b400c805400602c005031407a0080c000d1052503408030b440000e18662142c45141c6e800807281c14000701454885040c2401c45d003081e0465102725066000d5140c080344201c6420b04a184480000c51401c0d0400803107860b40d004500c03860b000d1100200f410740420009101d120003501041090040078502810020b21084d025200b0b20080742c072074010000c45032081d41808050b02d1782c500d039081c0182c035030200301e900070007150358040383d0008145906c2c20b56080c241519001180524400d01cec08204a08084c1d05040300c2c0c1e40b00c1c80099100182c1001415041035950341d0040c0c80040000307104429492403809420b0600d071a40e418010541d18446603010105079101d883c0007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 661408435 1250 661407185 661407211
    0x30d35090d050906040501050903100c030e0708010504260409020a05040608090f0606090c090406030c0801060806150d020103020c0a0b01030b09030406081f0302030a050303190504080904090503041706 88
    0x340510944042c03003083e07960b030b0300719404000c1400254002c6c402000d82c060064210fa00d50b040c50718074101200e1001c070050f0002034a0701106d0b03605200c100400c3d40034128580080005080070b0361103120300068032046021105044881502c0701090106540050003501c1080d0340e1414181c60082c090342c0180515804a0700c10404134007407900001d180003440c14160f004000e141c40c0c5404000d54410000c5c000d4082c040100306804041d212805600e005511a1a480c02d0042c1812000c0703094503041d410840e0036500140c10031001b694a40e843c1c80c0d04801c10798800000703080e1800101d0280c480d2071840358040c852003072110b003007101240800e4104e038060704003400c441d2142042d140c1c49104500c03d100025a030580444c080013060895428001002888030b0542035072030340424102241c8000c00d0b41c0b5038002004204203000703400b80010405048030700810032403405695115150058008480c00780b0343e50b0b403d5404018040046601410481500c0032100c80d0301201f0590703451040310001105c00e0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 661409685 1250 661408435 661408453
    0x10e0702101a09040602040504060602030c060702012c01060f15030c03020406121112090f0105011401050d0f200705071d1f0b03070c03020d0e030d3509 67
    0x410b00c00c2000c9036042030303495140342e1141001c1205000340079006580d216803c00c00041c83c0d640c0c906c00d09008107195006591910101f110302d604050004141c1025039040055a00d9010010000b24084403194a0380081c5038500c9080e40e40140211b80000701c641d005000041040d11a50a000305180410b035400e00103a070003610100e0590282d0701c20900401c840c1c102568140406410041901c58160103a50500303565290100c0b0340b04040c0c40400041d00515401d007500c0390280140b50140c0035034400030041810344000203140344a60b400d41131049030b5501c02034450110680203442a490000e0500142a80440744074906600014040f6100d104074140002c000e41d105a40f1200b01501206055480d51080c44018070b80320a0305000c5032802c1d213590040740702c80b0f14001850142c0ca89690318071400c42d40c0e03d0013070700d00480c00d00180c0902c40c84500d2800c40d41d8000a60004501144c50701c0055508280d60240c1502000814604c401503040c140d04a000301c003e252922800390382d811070f24404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 661410935 1250 661409685 661409713
    0x10110c0316051c021c0c0902040605070209130b040b0610020106150c050a050a030320032e081c14030c04031b09050a0903140a0e090403110303010e0702 67
    0x2408191401070204a030001004980b400722400400f04601ea180d54910215075400206015000d04802d041180070900802c144003d5900c044060241d4010443c6007a082c02e00c0503059020380200248109403100c0014003640031054442a060340c8005206070a04140c13814140070103080b62040d000f60075141c00c0155161050044c00200d078040f406600160881c40000c5480c41c070711480981d000d216440b00400012004c009000703903103000e0798001030032000c0101c402540c0900c04000c074414000038401d00114054001811403444071101c010082d40c950000d601c0e40c940016402107080c1c2c00303084103104a9401e40e4440341c8105003a0b69a6030070040c1061381d9140280402d0780c40034241c12081c802400003c840b010140382c0c20560302d00144030300d1342d00c1440708140c0c1c0b001c4130103d03811a1141d1501c4209a00308010040c1e12107407000306810069001001042c02d400402d890703101d51400c41c0803030700b0b00d4020041c00c603c0c5d00703025003a0b03a500d40c1c50702d44041000c002076032488010310030802205411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 661412185 1250 661410935 661410943
    0xd09050109030f080a0c1d01020304180b011211180f130b090a0c121e020a050d051614300108070527090705040c090602071d0601081510110c03 63
    0x1b040c02c40d120b0301e00140202004c480c500d01181e12050651000308404a1248800341d0481c0096620610106d070a44c01d4000051400c0105050046507608011080040741142000ea6802515401ca07081014191900182c1c3e034410742c0d0f41c0660400781840440c181e4003011380001c0c0c01d041c01901e0442a40d21110320b844c5c12106210100e000040710719040b0607c4410307075040058003801403607504204000429104080b83e01541170b40d004900c0c0060034040d040614041c0651103004170103500a18150500042c000691400ca100854180042c0300d010b104407103048182204060ba910340c44420340042801c02d0310400380600c0c82c45102d00c00c0b000030107240511201c0c03a00c0c1e0030500440365580c50982540c1c3c0021014200a4490240b900d010500b505c2e80d10804400d0f1056607141c10f07203140703403000207802c0a03215008890703218601301c0044079005900d42c007030750040428038001c0d0141d5680d00380701c200c098031011050f5021210700401d220441d8400846103a09000c00290f44660199408050b84c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 661413435 1250 661412185 661412201
    0xc1210111201050d1b0b07020111010c02030a030e070b0f04030b011a0f0c0c090906010609050105030c0412030c0b0a05011d0405070e130204050c0d05090708030f0d09050109030f080a 80
    0x281c4001500610807403c200101030f24682c850300c502c800324010001d000d40580b2050300300290081022903000195a03008504101181c01c00b40200270591094000035241d10900759079409041c2c464109100700c030420440c0da40140701c1080c54a88035190002040d8190f48180310035126030495100101c1d0b40198003401900002082c9480351800c640138071114010303003081c0317022802070140c41d11821451301e031052410b1103010604040c0c600b0391704010001c0e1144880360402c1c2e04100d003d10400130112049800c9400380d030042404441c004c00c60f0718041b9241090164018030b030f81402c0090142250305074000350b050300d5046200c1c00c00c0c1400514228544401282c0151456102510030440090780c00c91194001140d00324010ba41d02070303500420169041942c0004000e2400200410b2000f141c0c85041d410140080180c0f13605407a28900c41d5480c05100100c40d9010750010780034070094001e40c0828203084d4010002c0c015215a410090081401542200085515200081e02c07212240c450700030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 661414685 1250 661413435 661413457
    0x306060806090a110f090f060103180b01030b09120d140105060702180c0d02070b04050c09060105030c0a090302100503101410030e030d090b010f150815030c121011 72
    0x90f03034142c0354940307003d0105468a4950130107480c40e68000c4c2511000d071114400c0080b03281d1030742d9504003000010101c0301138080c41e0302c10049965141001030000c091960450380c0106806441d0340310070414034108855a82c00d01c032400390002d50300714592407a0300a94400310342110100d2190381d03500140b101c2880b9801009500020a244c9540c200304581801600040340010b0141000311035808070301240d01140003990600a41000c00c02000b80030028501c0c1304d10203980400036400c100c000a012402f01900040c02500c0c04a01400c2d042c1c071400c0204019a0014407100d182a140c4c4809001030703101360380301d441582e29181c0c08912129244c81503091528090420359500004100407001001c81c0115800036000c1008808214404c3d402001800c5028a640710019490101401800856a80102505045001100c1c00107810200e0540c0c0107006860000704074a010000074140711040820703e602c043c0cc85000540c4450028001c2d980700c0816408102440c0720f840c01203800d0061001d804 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 661415935 1250 661414685 661414693
    0xf0708150103021e060a0512090c100f02010e0304090f1802061e040b120613051003061d15010501030c09051302070f06020f09090f0f0c0a27030606080609 68
    0x100508240c40b000050422181600301800e201c03e000805c0c2e50300045000b0001180410a01005500301c2400354000c03030110002d10118440f58082000c48502c00031040500a82d21007842a0368000e400c086900c40503282034030380c1c89880c0c3c0065002802d2880221000900d072a1012003000200c0080d84001740d0020465410030b4100010110319a01c40841000030480512000881840103070240180380c40c00072800405140c1142070101440040d0402c0e46258100010b00200329043c800a5098030341020001c00c0e6400c01e2007080424440d0810301c080f90348180d44002c160240c1440205050b5502680e05015000c10401d0842d0810028040c460340542c184000105080c40c640c0109002031061b203298081e400680c0ba21001c03038201d0300550f81091000924003d0620700444030360745c40814400c101c5001d0a0030b5a0301c03e484000208410080c45c000604815510f005401e480505c0c400d240550a003071720080e5040100c420136100480d01e007030410303101040c4000c002c280c0c40d2048424034010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 661417185 1250 661415935 661415939
    0x31b02010b0904080309070909081803060f0a090606050d150b06070203031c0b031506010206010b040b090d14101506051e070206131e050a0605070209090f0a03020f07081501 76
    0x200e0031a91002d00044030302d1148a200080c235a041c0d000f40c5d540103024444032511008404442e101c1d50b540c895542c1d10a4016404105031081800c520b02e4001d00041c0000443e03869910304030004040b1078010690101c2028020f5081140d820701c20802c0d00c043e40d1003884050a920300380950b03409200d0000394075800622080001040b66506070140080001000c00c5190b0f02138086801c08522940642607980c0c010204480d958042180a005248860840e45000d01e01048841c15001c0c007424030b80b24080c0c0c200b594080c07110b2104184924002c0c1420b4405948a0141000003810700044520b8011510b400011f500c40c010740580c0c0c4140750380d082170202c1101107041e00b8041c1e407140c081268007420600c80605580007083c45500a1300b083c50855050501c000710f405084017031540320511500d0081c10a101403580031302502d0080b58146c914034419140c50903031a040180100706070025200740c01801c004e02d507000400c0500c030890032050b2a000d54070390030615110b84480c40c10f508444844401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 661418435 1250 661417185 661417193
    0x40e091018110d082805040f030201030203060109030b10060e2713060504060204051c0510021608071a1503150405030c01111c05040506010e1f06031b02010b0904 71
    0x21081c4800b800402104565450341e46400054008050742104001d4241010b841641044450301e40384402d811314a0501c8e2414500403254086408002d041580200c0400e807140d00585041c00519404010b460340c41c0341203c0c28140d0740d5152b10a1b400091124801200c503801e111940d10010240d010041c115500c0701c141c008140309020b03042e09003030440c044040c804102c943c40ba11740120311820f005680d0b6071401c0308014005254952040703512941007000710004130002070712006020304080150329201d61101e0001d90700f050070f001800300340d40003807000108107c1040e018401d54040e01c032640c2c207440d400d50350040204400b900c0341d0107500800410100740901e420701540a40b04038100c91a00c0c0802d0b20302400e4400d9a48064901c113004580c1003411f01c0380000d4502089044001004103241075103030990f882c0410b00c6154107040700b000102d0960030000710074101e469880e10b10030603805e50340d0000400604c0050190741c82034001c0c0e218408141c2c8103004a43e034070320004013641d865484e1521 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 661419685 1250 661418435 661418453
    0x9080306091801050a050609250f0306080708071a0c031206060702030312181513020f15031b161101030b0a1701060608011523040e091018 61
    0x1564501040c1000c0300c1d4400382e42400740500c1100c2101c0701080305d0410b5411b0044031100a0482c602c0000194000020610400903518001ea4140340c1a0b41506c103449080e001403080741c000c02c039540107428011840f4a000980241140d41101d90070402401c0307655144840d0003150141c40307445d0020400000d14081c0b4495a03900302400401080ca80b004590009180d64080c068080100454a0030400400c2d0401203103902c0c040d220b0060201404068030044078031000401e51600ca84000c00280e0035500c403184040c40c1c200001e031290254024583d66040190800c60342e101f80800c05281d41d81091500750b060700c00c00040c001060344601680d564240218040001e5141050360b030300148001c0e65a05105500100081d4024201c0700548220050a4801c15004032041c03040a5004200040000346166407010007441c1081d034010005103000841200103c001002c100c1c00300b00412a140c414580358050f860303150484480400e040c00300015100500603113004540e40070722413004a010a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 661420935 1250 661419685 661419691
    0x41d0421090527091b09100f0305031c060e0c031902130603180c05060c0304091a010f08190209030a02030a0812150f0d0809030d0f120908030609 64
    0x414941c5825440b4008a10125542da02c41050900c9070f1104000580d241ca03c81508491041e0141107400702076416a007011005031482d5002d00c14001c005100202c28114000c060400000a81da9096517410401c0d0389400140030043c050014554051418445200300d1048648488040383c4550f140311601e641c0e80c0004145005094440c0c2041051545a1000344903007a1504100d0b0031150400e00018215506005004032030190070310b501005c20080e040c000c0854100303c81c0c07560390f190065491811030246900c5a40910705108142c0315494190303411a00300d480a80c0c40e10358100d4a9003080358a1102600d01c0100052a601c4a001001080d00140940200503080301c03004081c1394046407070025810744c1a2a021808100e100000d4041118950455049210844000304070400180780074500100248201d040520200c100018581034444900006043c3c480400311701c817024009070140c004080024401c0340c000d0707924070200c0c030401003803d800065090441e075605082c440009005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 661422185 1250 661420935 661420937
    0x61401060c0312020a1b050120040e01140114072402070c05010e01091a04031a010303020c04050a1803210204081216080307091e47041d0421 62
    0x100074045d0340c0c3d06104100246c034521800000404c03441401106000152421b00d802c3c4840781004100503050300c00700c2035415101c900e04124002c41d08640160340d15040d84150034039150707012030b0400c244001402984242c040441d852581004c1080a483c22881010002000503030016403d0145502c02c1110303607050001070400101c010b45810800e1940414110700f428a4140014284200050000c000e82c00201c603540041c110350665601a45482c10034481d5405680d4801c00229400d84d50f130003840c40c0c02160000004000d6580c00e000b8074402845503080d82011120f01c6070b61450a40384210303006c4803030000281ca59052203914020302544034000d44524a0094400b40d00031915000c000c3d4007807071050300c0d854050781c645040b0304075450b000e4122540e04020080308021603c0000c4840c28003075450880e000c4c03580a421302250000611800400c00c5140082c001d80042c0010001041591f0150f54007541038140344074040c0d05644216401010081000011103030104200c5d100502c0d1401 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 661423435 1250 661422185 661422197
    0x6030212160e1206100f0b0a0804020402040e0711162d09110c0709140705070c0e090c1e060405010f05090306070e010305070824011407061401060c0312020a 69
    0x84140003c0b0304141e0040381d43e03070541211003031050559058094000038074100c2806036040786000e4600816000b0007688209000e203440002d01155516070484d00a0302900417015900c0c141000b0040581203142c0d80c0d120b091041164502d201d00b1150184021141c40300345d0000b403000780733203400501e80503108004a910030300c0c0303d008681103c042c0039240100702ca0440550702c48440d09140341c0340108507801031000601c1c0c1311940083ca008800380c50740c003c90a0030840e96a20b10782c0f80c12038400e40181e020080c0600100140844624085550031980100300c0f000c25499441503410f0741044c0000103442d41c0300e2410481044994054004c450300c0407003e041440c101030041e00400c0c1030500840799100003170002d0014404a41c1c06100f8981c000541d45822841882c0c01500400500e104400d404c032000494003540080da80b144002c14512900c0d03180e11030712554140b41450181c1010001e506030310061f40e0021814603c42d00304188065016507c428981d007840010030001d500c194003010030460 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 661424685 1250 661423435 661423457
    0x3031e080f2a0a020f0d090308090603090a0f06060f14060a0c0201020a0c080604020109140a0302040209060403061107051903050d02070609080318060a0e1b04240f0603021216 77
    0x10444010b04040b00da44c0d0040c02c800c0704007080460030100c2408040041c400e8400c030501c049070145c0c0c00d0341c03400c50069070581d0b80d81c1c0f10891114079120a041d0300502c40f482d034003103a03010080d40350020000c4500701410b055101d51113550342d006243e11600d840790010024003100c5805031054035802001c03070040c010307103262807000c0d01d80521074100c0b43c22074481c0341d01010a0000315644490400010541c18950605003004038000614800042c84082d21540d004a040c0c0d2155488400325130055074440401c1002000010051441c1d03080318406403124014801c2c12400650038006090304190702d569024903150750b500b6400c000390070a28080d00c4185c2c0c0c90240a0000da0317108029400360000c40c0564040d481e4240c00c540c0b030034000034800d50785181031100c1640710b014001080c00c80d1003210f940c0740f14100c6c072210208004000401d941350240c03240711401100185010503102c15610001c000303051303a688170042981030b4400d480c64450800c0540d40080c0901c800100c4191120505251040700c0103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 661425935 1250 661424685 661424761
    0xd05060a12060207030f0c021c0203010e070e061906090306111c0209031e100905030d0603080d0f09020a0e1003150204050a050d02030a03111603031e080f 68
    0x164800880d01c4681c0010003409154104150300040740b00d501d000a1018016400b10b049560300c270f50104002d495131100b410441d9820742000d00041e040000312140d0540c0c03541c40ca10101c5066800d6030082050a41d40340aa20342c509900c4181c0c7c00c1901c880400394915962440241071907083c41c00d11310070511a00f040c3c2224011940d13001000c112015889402d5841054184200d417020000e0110200d403030711800303a0340811900703000c980e840c00c001900f08440c144941144246c046d00c05590380b6005010007081100e402822002d4091641080000b0810610000b124100740001e980401e01d905c0410040c1c004043c855801101c955112001940c1c9640c0c1d242c0024510140703400c403e03000301b8140986e050000b4114020300003110800c0d02000140c000c282c07140c981840140c20080000c18001c403420f8200006c16648100c026140762059403410010000031400a951002040340342c010019144210b400c1030144d50240700f85003150319a40c0007401070301d5031160044611030030809011502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 661427185 1250 661425935 661425959
    0x6030702070b0d020a08090a0b0711010b0a0e010f090501060207051302122d0c12060a172b0f27080114180303041e0b040c05030d050901050d05060a 65
    0x83c8984100543c40d5001c01c0d8002e0503002006200030502e46c03002982102140c40c00804a801a2580c208210b05040c00082c150150220700041500f00208901c0001c1801801c2c602d1030498859544c00c00341152180140750030b0b80c000380305000059206140034000b518204010b903904401100c001890b0038166920000c104d442103e41a101d091114007a0048100780d0251481e14405800c400085140491044d80b00d8041d08800c88031524154001445a03100c0f41040009800c0b44001d503100c030320702118615580d01c070407c9604a02c40800c0a000e05031080402001c400389815101c0c442c184400b0002210090300c4088480a144054001c21115030409100071700945010300020804e00403242c400040d01801400d0410b00110052090b0400000481900c3d00194032003804206030007984041c03988044200b0000e007180340d4047c14007040002b4000c0d50341c01c07228141c0a4400a002024090b02e26000e030390308550208004000c1d540600c001680800d901c5080140904076207500d9107014003507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 661428435 1250 661427185 661427197
    0x91623042409140604120620070c090c0509040c0201021902010e0d1b08030a0b0907030b19051e19030312202a061f0e011406030702070b 60
    0x218000c04220080c40d030700c40342a0018001003001c60f030080c03031881c02190700b0344164803d140713004c514102c0c41c10401120781c10400c141d1600d21380141100b62450318001a50b844000704442c0d1010601000814141030b0242d100c0f0802c01d030700c4441c2005114018400030f400c0402d2018210f550821951a04550366100c9481222165000048020014200324905901075100606000110b9071302e070340101040140443c841d41c410743d0780da01d80d225280203a02502d4810329035035005640508000c503890380742c0c0c40011a40d404648803500d0f030000c181c00051640180c0501a000510005400480d4011244407900c03039501502c0040110f00303140003481510b060740c20440c001111a00302000e028141d02030000a181581103107014020401303186d0409200e4030384103c124015210842c2c160119070740751103200c40c2440c003d80d01c65142030024020004c1b08440c984113a103a0244011643e07000c6d1041e418141d4414400c40140810202c04000303141d003008282c101141301e091408964001c0900240107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 661429685 1250 661428435 661428479
    0xf0f010506090103291809031c0b040911042a0509030a0b01090e060a0605060703030e0c120d02070816090b060c0a0302030315010215010e0a090803010e0609162304 72
    0x22580d003060400658140f44021000c032030b00e424044c00800c000101c201c80c00500c1e4241e014100b4808800500054100c01c20000d2f44107141004c5c4000784a414903410a407248119401c00014126042c07091403c10002ea1544500f001c80742c0d02451103010720002c140d030140050403150401002d80e110b800220b800d0f081110195100c6071611001d0108020f46500a0a884404d000b4a420040030881c2070040f0000a02019116280391840c09403d002100307449102400c130304181e5072a41700032a5540030300502d20006101e503034000500305d070001c0703803000548122401e440c0042e4600b043c2940501b141070051640322204111900d4034200c00c2020000280c0301e0780140d51249412400483c0b4081c1021000f41550020078052203038504031401603066a8641d0401c1000b9160840c0050082007000d400910b0450f001001080401c4499034440c0720316001c6400b00c804c3c1e03441c3c180c02140d1454010a403008113504503903c4043c100700140c02c102d0b507184c10aa0500701a0b84e00b8081003503084031030110b0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 661430935 1250 661429685 661429751
    0x603010308090a080d0c020108070306090e01060f23040209060c060a0c030b091603050c04170102070b01050d330606180b0a050a03021e031e0f0f010506090103 70
    0x340c40c03410f2a8103035100030310903c00a006030084508003e0a2003e058000a04010100c000039030114042d40c03008020340fa010400f0003031104201603040c020502c43c01414134a950107000024079007013a5040d201c00540644410980788003680070703c40603400c60004664000020f0086451486042103114800c848801d00452201d80002001d4101d41821034141e000354114800c110b08203104200410300044a8500044c1540d91117000b90701038040e507000711004441c000c0320103443c1c0790150003500d007480c040e9012104990340c960400034903500310310307000b407004c90151010328040041107402d01c0800e00407a00740d11084d02c184003440c00c4440540101001c2111441d900540040105000010700104900ba40c84c4c0301010380e02070014090070155200f0590005645002c0d00081600103045c8203584800b540c5904203080c040b542c0240c0300005817100c0410400207840c12420110366405842d00d075540c000791b0b03401e01081c002554000e8510034181074840c0c002c002e60041e100d4450004040d4070240d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 661432185 1250 661430935 661430947
    0xc190b100501050f091c0c120b010f0f05010c0809040f0f051503030313050f0708010209191d041e11040c090e0127020a030b01030e0615041503020603010308 69
    0x4100c0d019a40c00250420206200076401c1d041818101c0716616812030b80f030981c01500b49000c40c04002d41c4200103140b8949004d0000f0140103000045503218845e40c4414040d07030720f1b240c9407944500c03d84114641007001d00310402255001c2c080102204d0702a0301d0b607a00e4002c2d40390214064620018440c002c0360743d40c5032601001d803054403400340c00041d212203140c501c1c29080c000a0f40c9020103044e034906109c1218016041010401c17501c0b03c203100c40010f5518003581c8011485c000c0d04046d00683c000c110488401c0c4e8081d101c0d081c0d01082e6480055520014141280c0c0034161280040040320075242c442203410b0140400c41c0742c0c42016200729a075082c480e0b0000b05200c16101c1614580c001c1c0004081c0038041000c0445207141521015200c215801c601c0e1419905000741400b17002c0003051000403030b02d8001c2c0d8550050145d40b4820b88040c440311a0f00c0d400c141c1e4500044414403052019100c0280c400c0c41c19410049900c10f450181410b5280c403600054080c2d4001e83c07080b1504a40041c039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 661433435 1250 661432185 661432201
    0x807140a05030c0a05040c031e0203040b1f0303181d4303020f0309070f121e03120f06030c08010e06010e060a0e04080c060c0405060f0c190b 62
    0x502400307010241e010b000c000009102280710f407001405a1840b031916844e012076103600ca030b442017000007500650403034500ba4242464009501c2984c0c240c3e0f07443d599100242ca8000c01d8030002080800304001d01420a18503103044032604c07902250180d912130241d0b80040c80011601140b00880d8100c101c4401908040c070200c9118501d41002c51615082406c00880301945000b254001d034010f1040b401200000303c40c03c6000b4402c3c90340c0004501070120611035507200c0001c1c003038165001c0c4000c500700da5844076400c4040801c0000c00038515641c00000060001040c0201c01e240d0784281001c01c1c40054070520b000075180701c120184000341e1b0350f203420803d10030022a02c400400710000200205425258010303110031303050140700711240b404030104040381c0b0b41c050303c8802401c40d40120343c0d25040500d0b00800d0340d405100808000d01c1030b54007180041d003150b03003143d0841c0d1000b0100303850320100c1e0200c65081d400c040840184c9001d24890700110a8442891000c03030752050f002205285481e5003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 661434685 1250 661433435 661433449
    0x602100f060506040603050c280e010206040b041209091b14090f1c02030d03020a0f09050f0f0d080c010501382d19020c0a091104080714 60
    0x91003609052500070081030321182c04450a8811030700c0c0104076556150603d03000c512410500021603400e4035048405190b8011614030303216070941d41c412441c2a10001265100710507640505034101060201c1c001807284a6840c0382c020841c00d104e50314a40e100c1344e400485044095a00115507544086000c0a03800240c12816070b0002d03291a00388400300000c0350303000c842083c056024a800c5035498200744494112440c0d0a94010112140444000c1c0020080c3d0041103605001c114070b485400703101c9010702411415560043c10140305c42c080d000410040d9045c0c0b01d40e982d003050380200c164010460f600000c22030010204008595545414000303040d00201d042003410603501205500410350300303000000b40126801030003584410031400b1210842c040404000074140660032040c1a200a4034050508540c0da042c08044009407a84103a0b202d2030106c07003090f40030b803980340107200500e444c0e4461850822440e10a504003502c0d0202c00d85002c049410000c031500b801e0b40e180c4114a0032076 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 661435935 1250 661434685 661434701
    0x90d05070c06050319090503071e0f03030f090f120905010216050603041703070903020f04020f040b03090102070c06050c070f05060a0e15040608090c010306060206040f1a01060210 79
    0x11424624041580e1102480c0c1c203410300469040000000205400008048524002083e128401c000d0b002540c40d0042e541d5114006c00c48000d00031095099100d140b000ca841c1e1540d4211301c94209803076666500324000c041e140703074143c0b1241c0d03210450404105901c460310740c22441aa00031020250902002c3e00291859100f24110340c002d0400e2111450030784800c208807101525400d4071f079111032510350750408180e40d40c0c401c003010200402c040d44c0e911400078811070b0300941e90254901c1000d030034002a4840c40b07045224104007000204100c8a0305001982d101300a0700006090990307139074a503816640568010000280d000c914898452401d1000342c00904160751358039141d40c584030210758240220f40e00501401031120700d103806507c0701e00d0100364641503180c0e40c03a611621100040e0440d00250f4000206200f41c503a101025402442960181d502c5034008090359070300d503031f10040704401c203400c00c56100c10740d598000103141c60340d8821406055270341c004e024040688003804080711844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 661437185 1250 661435935 661435937
    0x8060424090e16030b070e10170105031b0607060b04140103050f0c01091412030c0d090f0e040f080d050f07030e0c010f03090c0f090c110d08180f06040308090d 70
    0x32a030007204002c030b000c0f583d10460350300c500c1080d11aa65058140c8400300e60180c41c6803c4179131110405480c540c8150b0032100307161603048a0400d030741c98509050b9101c50b1002c403c40c81c1d013800c07101c55007186000c0700a4000e09105142c04200382803942c0118040e42e00c1c10700c0c0b803144942c43d14014020003030f040c440030b4040b0b2140401440c4007a403d800080180607548a03500316407580304081001920707107400507200d14401c002100da41c1c080b0007407181d550380441702e9440e001440c07039040403034002d40c9004040103c40d04d058019030152140c0e116084041100181100c6041041100c014002140e026507071040e4031000140c10b00303203401c0c4c3c40034090350b920180107003068110107050384280c0c2e04541d04480352040313490002855400c42c035100101001642102a400c001c4150000341480941c1152140312034641d00e800d840c0d640c04451a5562000300c44400100d02d01d1000100c506124880c0d110318003490000704c0307c4044032482c1050410100790f80035400a404030f803c001034aa03082040141060807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 661438435 1250 661437185 661437193
    0x12100e060711100f231f0b0a0810030b010e1902270d0212030a1e050406030c140a111b030604060b03010902190801180f0308060424090e 60
    0x4803440303030740341c1150303001c281d1070160380701004400d0040030342c0b0a10001031110301010703021068039a1030345c0c040c0b4126003114004078000c1e040c80003004000c1101c0220742d0000c0d0760341d0800c02100d0064852000003007103620424800f020000100b021480060700030140c007500074110f404c210200d261940c1940000305051801084901c1200341026020704c507200300c03402c4a0710314a4451002a41d9070070454400b941c4001082d8000641d0000800204144401501d1740c0030103940040c0510300c2c14136251201408501c09100401855000317030403440008400d07240c41c030401e8012440540494021248805c0014000442404002000c1100702c0042d241944800e00700024017001aa6070500148020a801d46410709400da584094012911955005180e0702c801d04007102d0200c0c2c003101c00d1041000c50340c2803d0105200380300b020f402210494000120003480200e82e10b0549500740c1c060f2035150402d90b1040c400f14242003c2080a551060500c0c8a0031601e241050403c1952540d564001503500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 661439685 1250 661438435 661438457
    0x2040e0610050304030c110a0902180a080d18270c020f0c01051b2a01090312031a0402040f030507050a0b12090a1208090607111b12100e0607 62
    0x240240540c0d034419817524200903540540c0c541011909007551007241c106840d280702045903503490b006003110700d001140300004080d2907020001c00c404503110300b000d203030030402a0b02100c42c402c084020080055140130380e02c859403411900700000241e900c1c0c1101e1204000b1803500741c10341c2d00503480401e0003813005102c1e101c0d0b400f403002d444540034048103051241c005110018007080740d14002103a00190300ba1a0711081c0b102205038038840440b0150b403024070b6042c041c0385560181400d441943c0d0024030401c95801020001d82c003e149501112404020300b104100c0250f403240018070140c050b0f600071710440d40ca54549030346030190940181c2e108441c80e5030305000d9220781c401907032a0071840c082d81d032210b61107a00c501801c00e030180d000035000d001c03030381808013016070045e00d1103006030b04540454603a0750301c07a98212260360302001b90100603045404c0441c1201e20100d114800d070500104000d1094003581212440d01210551668442d6152840c02805000612200780d101d00719041c002c40d061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 661440935 1250 661439685 661439687
    0x610080601090e12070f0c080d0207090515091504060605160206090d05010609050f090319110c0315040b0c030426071a060307080c06090d050a1502040e0610 69
    0xc0d0140181c0b81c0c095690341d00000240420800780503074560760f14001d9554401c3d0b00b04100d5411040c80103561411900100069000000401e103208209030340c0a4448241450f8848028000c090030780014101000b84560540c1c0d1000b4580d030264840b1218a01c0540540050000b9601294000d205106050003102c140d0b00341e620400d400c440c0d0460381180c1e9180644c0010b4100c12080c10301401d81e61074031201180e000640e40c0020301400140400c00415503801410b5681c0f4440d108589a030201141031098500303009000300070b800c4082c4c80070f4030103d40d4800c01080c070304038488403507000c54454001030100b8080549036040d00920320310038071495460a0303101c1c20402030001035001c41c20600d140000c030b07440345414141d492041c0d01985401100c07040c2500501984000e580c51031107030007503080005a0003000940d4a8142c1d8000e00414185110b100801923140b040700342c01e5902c3c0c0610ba000100281400c2c1082c14202d00e910070058070f0b182800c3d01c90000d003078010f140314015421441148282 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 661442185 1250 661440935 661440943
    0xc0d0311071e03020f0d0e040f0203090a150605030d120b010305060102030f07050715210216110d0f0b07030510032a03020a09020a08060a05100807110607030e061008 73
    0x144004181c0e02c0c0b40d209140807440c3c0f07682102e10260381d018080d00300d1905076003d00c003420f042800702c500b03101010003008020100e2005807100d040560000604900045803001a61340c106a0b1403000902c190781c0350086800c1c240400e01640010703100d141640d501c4102c92041c440d01c80000c0ca02000b0074641000040c0d642e21600c071048c16001070101c0c0b01010480e0821402c009400f91660380d072540403010001801c10804104c804030300500c880490042100349200359620640103001003070f006c01c0c0f140c44405078100300b100819041440380d00c040300440c5001004481945c80b4042070b100d140380141c0000c0c1120300c06031520ba421403030701320b0810220304050303580c1c80c030000350a07200b5203040d01404c2041500c403102d500003500810f44500015024180d94007400c00c5042540f03429400d95602c1c410444e154100c0d00a9640c4001400b5806086034031681040340e10602e5420205120341800716103d1410a0407141c000002c1d031100c00c03038000c000040c031003c1c1c0c101a0000c49000102c1c104500b41d51a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 661443435 1250 661442185 661442213
    0x31106100b0313170a080711030301060c0c081506090906040f030e031f05070e010306081e160321020f1e0309040e011b09030c0501080703020f0c0d031107 68
    0x103140c20200c00302c2e006590b5900c219444030f6100c1c1c04007510008002c280c0340550041702c803603000318030910300040400380522504880024143d0240d46140c0c20244252465040004161045034030083e010482c00c40c00c004071035120503886102411450a0b0040000c100ca000744034070000d8004005001c00100d5480c181c441d20f0340c1c9400c000d401615540017207403030000204260070486906224941300c0407110340c4030b103026a4843c0e588101600c00710f0010740654009104080050303111282426048150459074540c0051840a60711140720005003440c440d0f000d608180d4031880c980f102c24002c2c55209010f8402102c0301c2c005844141150b48501da00c4422010011000c600e00b940341840c2d41c0c0c0140211040410700030000c10803e0340b0451a64004c010082810b0203041b000311865071094060801039007220b44c0182c00e440070500300700c011103407010080e108006058081c4020703901440007001510300c81e181031004000c1c0580305032006042d21158818240c542c4400c22582010614040010358 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 661444685 1250 661443435 661443449
    0x18021b0a170c0d031d03030a0b01020607020c06030f0414030705030c0d17150f03190c0608060d120e060f0913020f0f07050f010501030317070906080112170f0703110610 74
    0x2a00308110341705500b1140d960304015500c4d000020030021660034650050300da11030281d0894600341c3c0c82c220180d0b42c40c21880c0c00698440400e200140c2440f4010340c00e550300c140f04d01d1000c0d4891050104491a5401052044030241c00200398401d2594017008400e1000b0450300c0c2c1080c1a0f80829880b911024003c1c1600c02040d44504011035180c8a050b841103583c500074040b280c90156128503042c10041c001002c0340c40b212101000901a4410016140190001001c00f0010085135941d08000c0b15401ea45e40d040c4a0034080f00c0340c0315641c200c00380110b42003c0c03009030750716484031041041043c0e134100464407440c414400d14602100f5102502e690100807030145030b4a40b40750078410310f0180b4008401006600341070001c010036030300460100404403005031800076070f00c0c2c1006c145c503000c40c0e80c019000061340d00401080340c0884085100302190040c85210f01620076050305508030fa1000119800c1c6034070020b410310400d9803203a50a0320040c4810060510341c00d11080030750720240903201d004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 661445935 1250 661444685 661444691
    0x60c1805060a0309050303100f1410080907030c03140105061002030d0213092d02030609060103090828110c0904061113080d1205040302060118021b0a170c0d03 70
    0x300e030a009600c216242c85d0810100c030748074500b14411a000c02c00c1800b0302808a00015000252010302c080e05208040005191020b01c0c08444411aa1a000200b15145070300c202c80c0000046440307400c9000195015401004001d456010514291280a400f690041282e11444501c5540c0441580d40c0c104c0621405a81d803015800c4081142300140c00c50000390b450a0b030a044c814150014504200e0354001d034150154811003001d80490204a4100d41c00200200000f4855886640000c002510400c1e03001c0c107007898107107003900382c800700890306580c03c244884281d58070303801102202c500b000d400003d041100344000814000000504010302950b00e910840540c500c51006944030040c000d08851300107513842a00d1661117004240340700c00303e080c09260030320000807400780030301c295055002802140d1811009004460403080c400d45025800e02c40404d040d680c0780e000c09000c001c510000e211410fa18106100c0031206281206000d400420040f45080c03004550881d03084c5042c1400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 661447185 1250 661445935 661445947
    0x50a060509030903070b07020f030a150b0607210e030d0c1403042310050702030a11061b070e0603030a080c0a03090b04060c0e100203090d020303070f0b0103060c180506 74
    0x145580a070f16101549402029800310310044101d0103001d1040c001c6400000c00010841030580ba20403101d03003d818071240c8e81007020300031259003041c0c00300040581083c2c80c0500e59101c0b2030746c039a81c0c08072440c448260400d000c90b480c0e80c0041ca0b2020401e044010b010510900c0381d0140c002040084024140c0d41c17443ca58020b200014011781e001086e507142038285440c0307440c0702e8184140303c1140e034900c02c1c0c103206000c80d81580300300d00385c1d10031a0707018004160b440c035180c5071401072554800c5e080e90310100802045007019038400075646203d541da070003441c8003030a00c600c240410b080202160f0080d03000340a4403410035803191034103411003203071284903550300f040c0801180508400c1c84068a2004400700f4002081a40c2d44400014105952007003109039965040002c4040c1e0007041c64010b92060000b11203d02d8030f40c41408105200030200c0e03141200700c3e6110101c0105280341501e400c0700d0040108180680c0b80101864080d1624102c2c8500f0300c0113100304880a00d5003e030a02540c2d000c220 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 661448435 1250 661447185 661447201
    0x90d02010c140f070627090504020a090f021309090c061808010515030c0118180b1905130902030d08040203011e021c15030b0c12040302010207120c050a0605 69
    0x448422074003003106880d00c0c500e0f10030704070341e45080d130348a84400520b4110000da481c0030b2480b00190b2000010540c050325610306005940070701006030099070320907141c41001904500610840146411100015803038040040c01c0c0072089060703a200000250a0500c2d140004800b1a14038040e01c07441d082402102d10031044010411b421504185413a6107400244074816125100b580b2a0002c2101110703004000e020044554000044d0780c0328070782c20300c1c0c4014040600880402d41c800700f0a0301000940d614650000b40c80b004c911145100300c1c8049600a1013207040c00760042c490140e44210902c540701c0da65001c071307035130b40c0103ea0503404106000010404641e0290030200c14401c052040240025038001018001d5200442d50b0000c0111481c10103004030490182009040c910640c03440c2c00391640d22400b8403503800034060304101e582084080d000c904440d001502650080d400140c982d0032134a8980d03940150402c0340001d0108400c502e0300040d1001a15401c6035600420201e074076101c17004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 661449685 1250 661448435 661448453
    0x70f050307080306090601050901092105030f0306031501030c0501050a030e010207030e190812090d140c0406050d0b070c05010f0c0e0301050f0f161b0f020a0605090d02010c 76
    0x500900500000500e4028401d054003c2c500404049584c3c621641b0341e0001980c036481b0b003001d0f07a408501409030400c1503500400514211405030044000e1408031a034a480c1168004614540811408024858031f814200304a207030354100c0c481c1524040d4155122102c14800510909040050004c0e8030841e0500c290000400c5103103100007035445240740e00e006440001d00545841c02121504031500c005211110003008480850000d00810705a00c401000176901164106800c06810100a0005602842d481e880c1000035030240c207401c042c0108120603600b0310742c440c0744550440140b0002181c101400c1070340080c0369050a80c04400c00d032900c24090021251170b02d011f2407601070008551070b04011400300104c0110000c2049a50b0300c458004004070a4614900c942c00c041c0c0000c0e44a41801e1058603145080c0c01c003d2a01340c0a00d10307281c05860343d40000c4412030920800c000071410500c640a003d484203061403400c1c01107050102d80306250311000641000346400b014000d101c5156 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 661450935 1250 661449685 661449713
    0xc0c0904030219030509061b0c01020d09173d06030228080d020c0f04180f05030c0105160e221104050616050709060501140a1709240609060607 63
    0x82c100315160311960300c885905100d885c4088c0414050341c0c100412961000c1916000c140c0302e5110049024281800302c405075580c455500564800c140721021031214010304407508404c0c45d100c0d1081c003010301641d02c080c2000460341d502c00138144042400180d86100807030b40ca4420709440051041000d001e03c07580340c00580d12212072400384880704455150702145100300040c05658800d08802c01605103c12150081c01019a001404070450006508028a1020640500100c9090401141c00613003155000d4404000240c220000401c11540208039015020b50841d00514000030000200d4400c4540e8004890200c0c0e07500411100702241e241a00d0140002038241c0b0744929004500207243e602190341039801d80701e0320100080c00e14403402000190f0341c044e511880410034008031050650010f00c041028480c2000002c4003199492494511504e0214014950400382030600b500401031241e031908040702e10402c00515407500c0003015000030041e5003081e42c4554600705020803108030303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 661452185 1250 661450935 661450939
    0x6050a0509030c0d05061f03020f040e030f0c0d2d030b0607080d150f03050c0d03030e06040f0308090c0306160207050307030b0402042d05070e030706050c0c0904030219030509 77
    0x34034041c4e41801000140d01c0d2041180007a8015014104020151380114a01c0b000b9800440707080c012449041c20313000301c0400928042224184028412205401d8000880c03e00084d4450241c4040e8140e0004025100700010152841d890400c0001214202c8049040c0000d03d603d8203140701d0181c0716881143d0036140c12040203a2204080010b040140c00c40782c04002c03110340d442da000b00e4068401e2440c0412264000010440d030b20500c0e0922680d40455a000d42c207146c0c0c2c0303c8011a00401c00d00c05140304503c1140301c401d0700005880c000c0c248450140c201c001e294811408070820707481c00944290040d80da42c100f5240b00300281d104a2800102c0c1d0001074250040c9103001040020441c00d081c051882100c06210703101c944004490904414245845e181303482103c000c58014407940190b82241003440d04034520082e8001007841d10500d9405031000600026090055440a2124010165045450a86070b050070f480082d43c40510b45082c2c0624010440d08604041c010000c5030110840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 661453435 1250 661452185 661452199
    0x270a060507231e150703180b0a0b040603080c0607050a0c080c030409020408030c01110307080103021207090614030f0105060f130204080a030306030201030e010501051c030c08070f140706050a0509030c 88
    0x7020a1500c1d40440d011051802ca000c00200750300031b0090080000a24052030352400c4040ca40d190ba41101c00c0c003030040d40003e075030b84442c0f0a00792102c0c01050041c500943c01300e65512500808a803030010b0040c50f000030400280084000540d021942d8070899402580746074403112084100d904520a80e0f0084007101d200050002c5c08a0000c4040d050100800c4002c028003400c82d400780b6990700c021100e000000c0d0290b00144010315041030001c0303d00410310102c50000d600c0c0c503d1081101c040c1d80180011503602d0200c40715903e41004048140030b01403000f8072031030400e2000b280000e41e121000d1031060b070502e120321120503101e505460003060058110303039500c506410050024001404103a00203410804140d040c0d4105014040c101c85000d022070302030714900c66140054a1a080f0120308100f903141300c00c00030841c0517016044060040c1030002e0019407600d82248101c40e5100080b4141d00100c004107c5150040c0598248031a2810803a680e400e59000103403c140b0162112540100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 661454685 1250 661453435 661453483
    0x40f0606090314010608070527040312150e130201053c0a1d03010f09060b040c08010e071b051e06100819050102270a06050723 56
    0x54000d2080c01228083c48103103c3c40c0307003000300721403e07200e07540101e10702903214203403c111506280742030b0079016802c40102c0b100f88501d0703468103280120544003940029100c0c9511014801a403144211502c040702001895628210020513501c000505944600048078505829640500104d6091142c140b40002c0701a1500040034400c8021100500100030a650912440300c51001110500140c039200c2e042800810038070302490000041c08076406540b036526401000c02c60b8000c1c0300001d0300c070710408910340b4002c0041c002185d00c0c1c1d0a5000030040510010070007503080011071600080d051411070102c0303e001420718084440500000c3c401d216501741d4020240403558003403a45c0140c0800e40b40f152700c4054043c040840f03d800740500f1500322110341d4141d003100400706c0c3c8501d0720520015090400c804514041c03000d41103440418a580540310b88124505501d020015200070304040703003001c80710784840c11250785803409810035100320030b0208480c420030000e45000394145507940000b01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 661455935 1250 661454685 661454687
    0x607020604050d050c062701060b041401020d090909110a0914010e0108030a120e121c0603170307090902030a060f050f03060408160213090201020c12030315040f0606 73
    0x8111402e494902441d908001a980300c0c50407109201c0c24500180019100d10725034012011403034501c01407142076480d41c03a814510078020503000b40f030301809031511949460564080659000440390441d04010202851030750070009203815075080600014203001c881c170300002061048014545d000c900c0384000914034445402c0004c0441d5019100d9080f07980c0d41b418640c02160030300441420360030030311145181c603105449403402e20346810004030701280180200e90030851041c014841d006400600f00401e140701c81100d110407400300404000161543c1c9071103525a8480700c103205103000000206a00921402c4684044c141c4c41c0401c540c0c80c00c1882c0101d000704400d2041c4449181c4980300003e1074039124a101011550260151010b40c0c0d43d03a0754045194800140c0c40007600c040a5485c01584034109454000725800c400020b440c0514000607103820b44076054648225990100006641c8000c0180c940022000344d140038103000003000500a0300750117040a50803460711900040c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 661457185 1250 661455935 661455943
    0x6211506110a0c2312060a020a023c0705030604020609220e0706080f04020105071410050703051f0303181a0304020a06020a0803061009091e0f02041a0714060702 71
    0x460490040d043c4c1d81c07541e4404d001648140e1a41c00d0410307000280010860340b456001404464501e20580390500403042c0d03c11103000e500604174a5040f8005c20b822915000d9035294111400018014104070341342000082d580c0c800100020b01408001c140c038215070310b9030020840000454a000400382507402c0c040710040142c0343c02c8983d544140c07000051810b0156000a001d43d06101c8a03030629038564005440aa0224504661101d084032601015900074005403804c019194008103042c14507000c003d0644002034022036080440711042d107401444a401c1d402140e9040c1880440e40d24000201444504198080303140c07076100342c4103000c80d00c00b541c0c0211b00c10391003107071802901c9480d20b40890741e8042040c0006d03c6c2d070301c4c10008180f061410100203030201c80301e803505031840340d1030310608401d981d0540000c203180c603509040348800300010b000e40030714200300e80e1046003003e181200c106c51009082c994000c021400103018001d102d215402515005040412504d145c1002d03c1d000b555 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 661458435 1250 661457185 661457219
    0xb0c060903191b05031b1908040b0c0708120307080609070c03030f02090a030309090c0f080f090a17070201030605091b090d05010e0303010305060c120a0b1906211506110a0c 76
    0x2847c0100b4001c51150240d50500c3c1c2c1080380c201c917509007001c0c00c00604103099442400c900d0784921500d0030009817448200080d003000d0440080d0141c0324200298003400c030b52405000c90b8400d004030010010695070040b0824800c0e6054640400c1060105010314001c1c45140d0360030703801c00107000b0080249604a0f08010072241d0300c5104014034100c203102110b65404940c03030400082c9100010580f102c0e030900301c043d000101201901c46030a1541d44a55020b00038011044c03584a0200d44c103c190741e058071408000744415581000e4038507040c008840004032060100591070b40205441805464408050087e107038081e00801c10320300e5070130348a90b03030360024031040b2840c3c46030900040c0600418410f48800026541c03c0443d603441c0c60203880301409000c40100d070407082c3d0400324402c0e84000c0c0e000c1402450607032900001122042c4241202c3d041c0210070103e01420310140380c0d10042850340c40c504076500d518016001e038172600744890800d00e07190070141403a550340601080e1004801c6501803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 661459685 1250 661458435 661458487
    0xf02100905011d0918010f02070309140f130c02070302030601090213272f03010f080c030a030806180a0f050a0905070b090a03050105010b0c060903191b0503 69
    0x11a8a0500f4021502e001420074043e00007000401107024000414520070300307000000c002040c201c05280c160801c0381c21804d0140e00150b0340c01010007190710b071844096912801134030f0940015890502240c100c05c4400d500020995841e215800624420b00c080d002030340e40241941c030b1a503599040500070750081214016001c3c20a40e0015020030707007601d180104e64245219003003410780642c680c001130191520700c81c55810300c1501106942004440f50b1104116140103a0b200e50500c0350382c80300c0124503001a0b510ba48058a18032083d5000a900344000d503051410030f14030b9541d01e000c14006220220000ca00405001c140170421000da0440b4619081c5814100311556032481c0a40c02e0b540740c1d003006860790700498418480043d032032005000c40da00240000342c0c030907620f0340c44a0844009074070403480f9034404100440002400d000076038100003140000c6091541c02543c001110a488103d00300380b001c040070440d07135400c1850880d0061070300107050f00d480700c140c01012240e02c0118a0006 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 661460935 1250 661459685 661459697
    0xb16050105010320090709050d0809100c050f0307030c020405060103090f0f03170105010804170903030d05060a1d15010c140c1f090b0c0f0102040303180b03040b060d0f0210090501 79
    0x403845e0404441e00362084159a03200e402c49441d080900840410301d4005a5001741d0401c0700d87d046031a2003a11804143c1c541e5940c1c102c403940d40c1003217414440390b040030300c03a2a0000c100c01000702e60b00c0351004403101e40445000075592610350040c0c0c01054441d10003801c10f1f0888039004144858600d280310698082e480c0c07480c05d41000740802007403143c240120f5000c1402c03500400c010425a446440c85c1003100c141445c0703049000b0717001a1664100716501d011054685c8208805070520800000050024490410b10715061102c0d404099074014408411021007451030021a8480e0040b070009a4101208542a0002c200707910b0b22131901c400054062958084001c401c1c0b15080010b0790522526510f519549051040350203003070f03010001c402c03154802c2e00b880800140d001c3c40148019440307510f94040c60251690442403d6903142c3c404082d1030410300800011440c1580020f600c00400c41e0a8680e61400d481d01e050318100842c80a5000380f200078003083c8240d0070512285c00c0d500262114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 661462185 1250 661460935 661460993
    0x605090421080112030c050708070807060210150509070e130506030105060f31060b1b0a02031c120e102702010e0a080d030501090e06100b160501050103 67
    0xa5840c0034080c840c0f600c0703013008040d80e4008240300700c0307503c141c45203e070003030360b010550701d49120385000010341000040c0c0e0003083c02042016010881e807440f522090710144240042540441c0d0b0b44034080c401d290054401000040c040c91264121403143c580061507400f48040c10b80d03d00000303000031944e40740651300e8100412064508480401d003040710081281405c09c911444250590455a00042d00f01c4020f90030080c450b039690050318080e1a4044840d41c46040f4883d21240c8003242c020720652a8121240c0c88015032004a01c2410f64100b01101281c18030802d071007125005034692a641c1c080c0e103000607004d194000030a41d0b00d10880c07074110030300854600941e00e01084181e08442903881d001c070364042006501400d10550204001020070b1010b07a51801420704210052911600090780c4400500095007035200b04404003181100401f018034043e900f40450000900400110200102c0c00c4001603190b6111344543c82c0d8045d0082c1300a594038a000421502d80c5c64025441031010358074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 661463435 1250 661462185 661462187
    0x19060905060f060d02070b1f0605030903030720010236211204031b17060711010b060c0313080d050d0c020c0d032303190b040605090421 60
    0xc0d49000d00001000d40e80c0c188180780400070301e0350250b080042e60503001e005040225a242040602c01c50f070010903080090078004007040c0c45000764000c44140701041c024004000000000e40341e0181c130300c0c206442d01c0491103684140d82c0703110451010056000280110b20a0700c0c0000d420304141c4820001c2d0002a00c9207480803010403900c1d10590403c5519000348000003040064400300d009103015210308405058210070340c0d134801e8100317844051040390f010411210039205132008202c100d94001c844ca40d880845520b9440241020381000010700c062503041c002948400040f18005003510755404007601d40700d44135080642c5169481195600c005460640842d00840016080c1d90341481c01000c030a04100420003601c04c0e5007103205580410710152500c00401c10b003070303000381c45007078440c0c0da0101d84201090311642000c4582c481407041c084080c1c0b42c01c031a040181900440480d036880e6000c0170400405255001b250303c03254a00611080c410404c0f00842a0700d00080034510003010810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 661464685 1250 661463435 661463441
    0x1b0b0d0e030f070f020d060615110606130e0705060316031d03030c160b010902071520220b09030d0503040b0f0c0c01060b0c0106091a101205190609 65
    0x6014440d010b0308000074000981880d1001024500c0100108000402907c45108484881e0050724034401040b4035040550380000305200e10040fa03a000f060545042c3c00400d501c0a181407102030000c0e200c01e8a04000b0b50180070f184050080985919180c0c41c10035841c20310301c035501400901007441e010203502c05e446280394040d643c0043c9001945551030b8008280380940c06035408010030a50f4008000c00a540c02881500a000e800e0015890720040d0400341740000400310311105c581d280c03400f171260245000c01055004d41c2e03031a18113274484601d1541d040726900c501644ca100203107803010202c0c581e010346004d0031503010240d0071070714244205641030f10365110a80c1c2c090590400000020251800700003003651060100c00c0641c01c0000d6850091300303490040d00400341d004008542c1e4100d41c50244295402441122030900c000c3d80b108030035059680e4000d50072070145607ea521301040c3c0e0b0240c40c100c5003c1241000410061500c43c0300d410100701840000e608203070800c03a0002d01c005843c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 661465935 1250 661464685 661464697
    0x60a0605032e030f080904054b130b0105061c02030606070812061c020d060207020616030c02011403090d1d030a030801030c1a161b0b0d0e03 62
    0x14542032240c44402602200640b00c00d10111011040714404800074940c6411401307683d1150010b2515031a00c00c0400c82500e600410b43c150244011030400b10003000c495025402491080305611703608031441e410103401058480c070040401c00081803015007803000240300701d1203000b413003c000e4590b00c0d603041194922413410707e1043c52805403503c1402c00c24035401180c1068000708514079003841d9982d06030164104025521103031200c0000c102444c2454051280341c984000908030b5101078580c002088102e0114000e440c0b20750220b01d203c110b40f541c00884026880d114680c50f1220414503008240b071001030422400280c52044841401c4003590a4900400140c00500703003860741c0b404200d0302050399040c0d0340302b010300400c00d80782d441d28103005401e402402a03642081ca9030440c00c004801c1402c0e980b001c1d02c03098010a00b00b02c2003c1443c00e5981d0400c40000008104409041030060002d010707805100502c100c0d8000030307a00400000918050301c00c120140100b103141d400083d00d0340284 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 661467185 1250 661465935 661465951
    0x10b15030901061e150e090a0f0c020705010225030606030507031a01031a10030615090e0607050703140d02030a050f07020d0e01210f02041e03030512060105091305060a060503 77
    0x1000050242c5003001500b00384035026440d2807a1004001c00000301c00d880d0a9580645c0c080c0c9e00c82604a01d03003424090300140e243d0a0006014070352a11000030364486441081c0b88000c01031901d460b003143c0b00000d80c00003c40e0090410b12089440b03040c40b41d103d42441c80100d81d00c280521400b4040136540101303d040b40d41018181c00b10b880064004005418020078400030755900f110b000c0002401e620400d170350040801c0316810081d0418411030300303c070001200d00e1140e41c41041080062640241281d07410740e41451301c4100d00d00b664250500f41d000c0d0a01c0b50281900101c2040b13800b0b40160b0155201d0001100ca515441c0c5030214141c0e1222002c0ac0c03100b000480b0944141c0d15075000799403001c1607159a10290361300310000350350703681204c400c0b00c107207c4450b800050810403000c4803240244c40045c100100200945580d902810a1040000800c440d1076640c001807241da005200f80c075000c10020f491105101c007003204020041c081115124401c9410f0000840c00310701c01c50980e4410900 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 661468435 1250 661467185 661467239
    0x50a02100515010f03241a040e01060e0a090501030821060d140709150302091b0403020103230a0902120c0d23030a090f0501141209010b1503090106 65
    0x50045510a429803c813070107068603180e03a410100070b5503070020300f611004682c980c00c0e141850040c12100c9062030b40341540c030000b0b2109004482e60342103200d045449034203080300c5400d100800300d940c0150340e031310016080b460800000148408140242880c42d403180500b0300307201002c0c1c002e624122050700c0039a0400c481c42800000159941d0150303026200c42411109140ea071110207a041d00d00030b100103107000b00b03681010011428a02e442d6034208506100310500c01110000d006128011407102a04042c1c0b1040510300b00d01e602016070141e2200307152200e560b45080c8100c00c000d484410801c078003600d11001c04182080317001c51265200e041c02004405c84503a0b90311114803640d0205000b18000740c19070840140003508100920301182076443d04c0151904d403070750245d00e0080030740c480c9040c000d1424802c110240d03100111842c015000d00f404001e80c40704582c2c00d0047c0455224140c01064840d40c40c1c60108803000591301c5000594000d00c99a40c452407490315001c5003803a0404c401103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 661469685 1250 661468435 661468471
    0x3020c0a020d020a12050a0b0c04050d24111e21040c0509011205011406010801091a03061906050f010c14120310061e0815040219050a021005 62
    0x28000c2d14529495000070a84001c15031034865541c0c0e010100301d01110742e5809040001c081280202d42a81d0102c030011511b0306040c5442d01140d0300b90f00c030f000001c0011501420f00b03001528501c8840c607242201940801501c281c038030307070359005d64000840249450502c40a40303521822500c1281c0e0004000e914080c3c540580e0100340422030b0010b0404c07a42d0700305001010455803209003034940200482010b042d900f02ca5410f1081c2115000f2100c0303c28007521000304035407a43c001980d2811600030400008060445c0c1c40e60b444031a0039076460a5250140b8010300882015019000c4240321001c2420080541c1d40d10070032100c04c01c901c180e903004c1341c84001440c0100d0620090041c1d115481c000f0742306800b40000f0003140580c02151000003445004a0a000302030740445040d1411402a54244840c10180e07400b8088500080025500c040d42c0d0f50000f1498550390145d902885442e1036003218200781c000e001d00180c21040041005101d00341c003c075519800741c0211400b500e4102c030f01440d072103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 661470935 1250 661469685 661469689
    0x9021306080c0f040906020c03090108101211040b0a180c18090b060d09031d010c2102150c03072d03050406110c0607030606050f09191503061503020c0a02 68
    0x45800c43c0c0c450b441950f580200000c1019400201802c20b200006191f80311621000541002005803044424858a600c00e000b110701c01e40c102c10243d6040410400030004420020340a802d00004194006130750240004000903480110308101c1c50b030000034480e070b0b41d000400300e0301d15600c20b84c40071a20b51641f0040040c4403940e807101300200d07800b81101d841c000d0825000740a480c030741502100040c50102c0e090502e640d04162110305107800340303040b401c65400e5481d035880505800020011482c100d41c1c41c41425802000040018140e0043d05086841c1817010309045400444250700410b61100031305241c0c0c000145651078001c030350b41a06a07101000041100103102c0140200c4c0c07817603600c0341d00814010300b03c005000e0060700280241a14a080740000701500c5081e4810b0003440f100341300c13051160300420162884020f00755004182240a00500018101c00b0751200d61621000d030b90340c00c41d9a9143c2c1289098030014040c078001104289811022841200c4401002e07801022a4070018 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 661472185 1250 661470935 661470949
    0x41b080f0705070b07020d0311030708060f04150b0304020f010c050601091a09040609030e030102040521010b0418120e09010b0d0e070603020405012007150513060309021306080c 78
    0xc08502d070060800c98156100c4030f50f08829100a400b5a02c15008a07800aa06000709000300c00c407096918190304164801406d08180a03011905c01d0342d81c0c42c0007682c552240e5011405a104003050071740c20766a12180300c91181d00664041e4011070484d0340d40d40180d4014407100c0142940301d070040019a1800300c4220081900300400d2140140200c540d012994a100803a40298007800740040c0034001ca1a0140c040089440098007a90040c0000c210a503203012200700e200f04052400d803100e540980485005200c0d000030580c5c06494400f2880900d440304400c0926544944a1100d003088a00000d4442031072070301d24294010029001800141102c0c005030001d40c100d0680801e170030700709030012400d28030207402140000303a0109003081250303130049441c00c400119440e104100c40340d84c6401c2c1c4d100e452074000c6150300200800404140741c030520444040c2d640c500e40c0300072495240d8000401405a4450680c0314007d1200c2c4401f070030790305119100842d8642ca0003008019440c0b0244841 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 661473435 1250 661472185 661472191
    0x403051c020304082b0e01020601051210051e010b030108030a030c0c020a060f03060e0903160206130e0a0f0203070c061107060f02030912070503041a1b0a02041b080f 73
    0x85001c1803100098404040151418100c0744020014a1030f5104160b81485c0d0a076036070307510801010380c008075a60f980100e811415154240d6040505001e4030014601c0d000341920703c001d4992074181002000b9011b0b12411120031209440e034440e99031303140c604d000b49010038050740e0752580082040441042c000d5004150210680c1031144001d20260001482a06e441d400a400304114004c1641915454880d84028040780a078200700c40c201304a180d9030301d014080c21031b07980a214858410555407140d003a5410300700c1e480e820070005500c82890042c503400a8401100442c100b0040c4c0c1c01180e028000c3d2403040c0c05954510981078540d403588005080c0c5403803440d070414010030141010507101c0c000e04504084103400503a403810001b19a6260400107080710070380b00c20038011440001e02c00300440c0c0458001c1440702800071a280c0c0c0410300c0b480703181e02c0942400e6440f242403170444000f00d540400c59000b11002c00006880d4042503204140455024002803441c40c0080c64400071600e0090b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 661474685 1250 661473435 661473437
    0x40215040f0e100f0f0e061c030c0c0501180306050c09030709061a040506090d030909020a05120105030c0a09020901200604060f0b060a031802040c02070e06150a080405010f1e0e030403051c 83
    0x42101c01701c034008a5200a10234250001801e200e6258248072803000120000c140a1038541012806124001e05000752804000c05441d128030128071000402410313039204010040903900ca03d079880f400d6000800280c1b007a0010045d464107072b40842550740702a9001c4a501400c3d0314900552007007081183d540815040703050020090003c512a1500e201420b603244403519140c0d9030b0320a86803400c07c008030503440b66109034020100c288498a41e0960907003143c0c03240d000943c69143c0d100060320f16004107921000751401070301d0043d1020000041140c051f60240710104941c0d5904800b42040d684401e03162900450100301c01c4051600c29402051400d00303610048140b40116400070b015107428419000040c6d00c4440c00f070144060f010329064019800711810091405040b204600758002c00d0354000500040e000010240202034110030800b0b403900324104040d2500c103040c0040d00d1905940f0f03210813441d00d0f0041881e00000003c58050302c0d0007030000c2c0500902c0c91465841007816140c060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 661475935 1250 661474685 661474699
    0x301060b1303020906060a0c0206070618030c0b160e0f030a17040f060f0e010c080c1005070e04020c28080f03060f01030b09040215040f0e100f0f0e06 66
    0x56800080c4054511810440c014403811465401049402040030307140c80e1240c18100280340c480341d04207820800803039064400c030303403600e0700740c140440104008800382c400d0004d000e00d00000c0541c8000d0b2012440e1290038201030a803204003401c07200303112490a18010a92030704810000349048442c92a410500504803440091941c0e02c4104031100d403d1b50840300d02d8045020f201400f14184c0341001f800d000d14114809440d0542c00505000794420100c0c14000000d401809002c2c2c402c007200c210020341c80846480d00c0c5984404e500506040342d5480004a051044085616080c003c944600200200030580141400e04180001112006001001480e40d4610000900e50409881e4410301c400340280c9900d891428803403008240030185040601c1c129203048030342c1d540410150032039010343e11390380019540320b4460720302c1c4a41e40101c0d4841c141120000b880d085244200d6104440e000d4490000c0e0340d980401c100c80c1c142c20b000c3d031020041c1040050010000280c01c0310381c4084002c0900f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 661477185 1250 661475935 661475939
    0xf030f09030e0120030d092927060f040303060b0f03180c12061509090d0e011404080a021f1d01140c0105061f091a09151b060709050f030106 62
    0x41c0d242d584490301c03c180040d00c502025042c0001c806c03444000c41000b05444035040c0110654807080301c80209241803d0300312003020030304001aa8028091200c80341c0c07c0303071014100bc0740141c181c200d00b00c80403030000781040c0f00850301e0301310b01068840c1080f41c00c6190b03085444121030202d681080310900072007413203001c6901107150354207880c090791b00c81d01c01d02600e03541c2040d03550300d182ea5892040141c002c283c04020b1003403005000408802e0003e80b07283c130a0340c04981c000104d80c1c00d920201c108032040b40c082808944d41e040481d0311100b1074800c68086d1104204c841c0e82e107440d18200302041002c100203103d940d81110740700300403402c105014984107800303010780141c180886d0000704d0840f500341e54550401800f400c0045140c400300c113504003010340115031418024260079070303401100040d54202121020410b0004c0642c2e01c0401d004042d4a10742005c0782e200c2c0140d4000484107268004101c01e002d04003800030601501030f000d11f61b1540c8c0e0307140c00d100074010f0740c0440d4241d040e0159a6a000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 661478435 1250 661477185 661477247
    0xc040506030f2a04060b04050409110901092304030207120318030303061502160b0a030608030d0504020306100302030a08160b090610050f18090703080a0f030f09030e01 74
    0x3c501200c11020715241d03c24900390402c601082050b07550141345404028005810040255070413190202d4000c10068114039090f01d0b040d01d542c541d2500b11007110000f20f45c062098000d040102d42c91500181c01c0d0b09244115038140340c0a440190158005103018060b9800c1c0b210140611402170070100c40001031080001c1e40054203901c00d60005c2d44d11541484500800001c0511440f0703188020501041001369024000101340b00b920b2000e440042c081e0580c0340070350003180c0104040001e0380d880b030860311000c4000d004100c0d0100d00c03034040d000001e5802d5418a0701d40c0d00342d0390040c2c0241a4501950303101342c12940702d212982e001d110b10010000c001089844410b200c0e03a9031002038080782c10b18190050581204c1d03088103200d1000c0c0100e0070ba43e9100c0f03011840c040d40c8108800c80d1181c56444202c0d04040c44c0d9000507200c0d070740c0003401c515200c0d0400780503644196280d034108210044c4668403000c541025000400158200b07400d54801d600c20078002007425440c1c0c82c5c0000040052030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 661479685 1250 661478435 661478443
    0xc060f030c3009030a0f080604110c01090b011e05040c050c0a0311161a07030309140313090606120504081b0705150f0703110c151309020901020c040506030f 69
    0x1118401c201241032000850140b40d0b8200794028162800031800e1142850f4042c116007220314082c004c2080c4000040c0702507030303240c10090022904c40c0f041a030394130f041208240a07000f64002607596a110500001e080071551152003006c0340090000070942d030400b020040a48901412601001818410307003c2c11304c0d0a10640c0001482501d6034031030407185e20101c500b0140c0c000810b850340300b0400700800014000c002c0058814400220b01c55541e8a10704e03003900102820350001c1d041d8801c01070003101c0b8460001c0140700c4000300d041140a501d684140e03041c180c40e03113402074000203012003603014800c95840d008550854070560850741401d90f074115400308000c050700c10300d0340c2e80d21103141001141040c0343c00e0583d140100e118070303103082e40e6122850703064418050002c003008000e41415040600a101080540000071300038408091182851b1195030400851062400800c503c0042d004440740308039128400c068010344502c0702e002c0104401010020149505401064480444194248 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 661480935 1250 661479685 661479727
    0x1e030403140a0b06030c03030702150c0f062e0612090203160e0f100314012a0201290409260703110114180c210f0c060f030c 55
    0xc044581aa082c070901c03c02026004d42d0094204814000c029103011044a030b071a0b4042e00d00300610780c0e105800c0e200d103204910b040511405501368503030040d007001c5560b0340503540010f0390b2641004001c018202d00c1041c0c20540c151300500c108100308941c011110102c2e01c170b050401c0040d40551a8022034142800d030101440001c0800d502801640b0501001c983c11444103c8610341d40d00c0d21914a40c1a07858600004c1d00f190b8035802c0c2604000340c00d402c071140c0c01c107181c046003c042c0d400001c04603a200713000c2c107100d001d542800c0c81900c4600707103200b0104030b500c44101c540c201000c60800740f00c0240080401a0b0785a004a500e0015855541c490054110000640c07661354013014240200300b012100300514180e4101940085a0000c858109422003412017420b21004d5605c2d1a00307140c43c0c10a802140c100403601550500b440c0d817014600702c0c00300c41030140c2e04442000c1d2062501c4124480c1400d601580512120b0302c40700000c40a558402e94010f507041c5050007030f100790f0800200c16 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 661482185 1250 661480935 661480973
    0x503030109150305030d020c0307050f060103020a0504051006110c1c0c0b0301030c0b1b010504050c01090603020906040b0a0306121b060306060e1915110705060307021e030403 77
    0x10041111607401c2c4a921641a503860070858503508503600c107500c030b119140402c1070003a00810401c1201c0f10600c12a00c5140e0710200300d592940c603070381d11240c40b00c00904c4168402d821660000076241428002c2c2442131400100b40c402a0f42040019245050034440c400c1c528440ca007030b8808075032145407900400342182428401004814500011001a10380050040c86409d000400014a61107022000e0314109918603458085811210755000355010010003598240024042400008614105000760aa03540420103480307600c190183e03c2000a1550404e004120400941c030800000e880891b80c1e52a02280c0950f035205c4000d40d03109c0c40481510100c41c0a030722012107484044585005007124102885140d24111020707100d04103251003070340113001d07140c1c02800c0103c008030110082c0100d0f03600e00c000d10b1741d030013001410f03400d030f00c10b4000c114450f100011645141c101c055a04c5500a41d0040014200c1c16054603068001541d04c0078051000f80400300010381400d021441d1a607030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 661483435 1250 661482185 661482187
    0x16050910021605060a0f050a051e03150405100b07020a0b0c102703081f06031d010501140d0c05040204030602071505010317180d0c0518060105072a030503 68
    0x80c00e9185a000c821076400701d03111320402c00005c038a190708078181101801c580c2c10119240c6104080c140c55600c9104e90388a11306103941d100da1100c50441001e180602c12000d02103070728445201c180812940e0076242c0c200180c140c01010080301c0740f01001010b12602c080e0a00360401e03600c5c1040e40f12034001780c1100e00903810040c0304200c00403003445010405503142d903810001080300716561507e810802e601400f041410710015000500111003000c0720340c40c5a551150311580d41c44010014441242c2d080c0300d00700a60b03540000104140901d5060351b0400d010301440b00c84000802601a04500c02180c444c0000000003030340d40d4940c4081c00066009103c0541c1e51641841e000020614070420010403a207030000600210340700c095003400c00301c030002010343e454070500000000c85008682d2160b200b01d044540754200075225020804580080d2010a80b1000c20407612200c3d0b602111924001801031080c940482d031420001100084909280040e40108840f01c100c0801c1d95081900d807540 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 661484685 1250 661483435 661483453
    0xb0d02090a060918051e0703090b0910140c0d0b0a0f030f23120f2a010b0616031b02060a0c1506050f06221401030b01171605091002 58
    0xc2001c00010303028200d0701c403c00c00d030b20300b50413162030f02004103114400d01c01b401800201468081e90100d840c560b0010340c411654505060b0307590790303034803a910340d00000350074940030054680c071a0841c0b40c0101045418507007441b40250010f4001c103500d9401c1540540b0101000902039480502080618003a5002c150303a00000e007051070390280c0b0600041c444594000000503a1017020402d0701c80da0195046441e51480362180d10309040c0500642150700c56211340c03901710144200c510704201010034800a1007030007103c008103c00380c010300742401d880800c500c0b03602000900c070b5104a914207110036410380c0000c215401092a503000402240040307050782040390f0502c40841013004003141045001c0c0440c034180070105407481d424032040b0780689008145000d8818041d03007000c1d00e2018408504546039611460000c4507910150711038003091404100c01d20311b500c94035088112001c1c5045060032a140c0d101402000c4c6018002071041110a20001ea4260360304070740d00076000302c20350007081c02e85 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 661485935 1250 661484685 661484699
    0x40c0f030f020f011704030c05010f2919030809040609020a0503150901080a0f06110c0709110304110609010915120e0f060103241b26010b0d02090a0609 67
    0x500109201030521040280017229400703880c2003a82d02c2a458609061030440c0c41c9080ca01420103102003482541c20610711078854007582144898004407406095141d01c1050306101801085a221100f131900c4140c0520104150030010100100702420004079155119484c00c1280c2002c80000d00152002080c0061000c2a10210022160403610252a5498120105c0c6d84400405008111002c0d14a440062002660204a00c2c8145000040d40d44001c034850f661504c2d51400794161142c035106884a40c07600c0031058912840d400003100f40030401d5042041401c2c2c116520341410405c1144002c54000d6107600c940d1180354841d00c5482c07030345030300003600c50644a2825180c01c4542c06440743c1100e00c2e400185903411250000300d12010400b007001c14130140c4100d5940f01a806003010f0385a000b00801441004250055949268a13a4a107601003040201c0e8511251640100395006102081c10740c0002c0c140d801710180014581030011001c641d1155496200e00017059000d0b0041000d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 661487185 1250 661485935 661485949
    0x22080403020f0f06031f0312020d091406030a0e1914070e0c0a080612060903130e0411011d0405010e0603060c0a0512041502070b0a060803070506010905040c0f030f02 73
    0x445002c841d40801c0003c101c0c00b144141c00000c2c5405840c03407400904a07008030b10030003004040c6400c03014010703001f0b4240d00040d6883d0300f000300b0341307000695003600080c105008005820020344c004001d14138586403c100c8602400403031140000034043c00801922424190f10800c0d405032003602d8900c1109205581507090992640c8880f5092610004112075401c0f06070403541c030707003c150070150071545503240800c90b208a815180940f0b44281e0f800d100706250000080c2030070082c107909480405450f070150190076801074400600e0702c0c420155044440d03010b503403c282c10b4450a00c45444d1440120001006d0301ca0a0780181440e0f800c4a06001060230306000c610303480800507488500d019076841c0014490300c41d618141154074690004101000780200c0c10820120b10904150345034201802c04040d00e8206641084180d4a80000042c1d988408003d550203107811402078511350303103400183c2c0081e000c010310840f81e08419003400b1425842600840d0061801103c803890103440600c140052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 661488435 1250 661487185 661487209
    0x30c03020403030210050a0b1327051905030c07060c0b0f040206192016060e150c0307020a06020a05070b09060702040b030c03030d1e0504080a082208040302 69
    0x41600420082c400300350002003041c1c5c108480600040c569694020417170050019008983d448101c0202c08041100280c101d00d90340c580f91403c001e0b04001c40c0120218100004000078038541108240d02c8150780801020320341180588240c03885c0544c46c00041d400c080c110b4100304007046241d00b910043c010f42c1c185c1641d01001d4280040305a00306034001401a014000403c58120301c1c281d05001d895202c1c00c500c0d04c0c1d4040110400f02e000d169a2072860319114032084d0038407062240503002513420712440c2d40d0b0f00c01c480007a00540b030b08640781481c03804680c020701007000e552208101040c0181c5505181d00b000b04500c0e80030b40109e030814074001e0b051000c5c65020504c1010140f104c01c2c10340c1e07610000c44034001d5046034000360942100340400c1c2010411002958140000b01d1034548000d030603005800d05040d00e0500030103802e10b443c6410308903101074030302030404682800342e11b102d28040c0300c1031034001c048001d40010b03400090144040382c2d2900ca00803228018007141c01c0086040600000d00c1d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 661489685 1250 661488435 661488437
    0x3031927020a15180f1202060c16030c15020105011a07050a020a0f150216150201090b040c050a0e0c03040f031403070306050f0d020d02040b0a05060c0715020d021209120d0f030c 78
    0x10170501c2c100188240000400001e07120320b40001d0441141d040c00c201d00300380c882817054030700e100b03c0d43e904100c8a184c915100c2d54030b41d001d4030007089108070300c107100b610705039030090a084402150340c20000c85143c00049040307503581710f4180440003594440c40042d0041c0442c6112a401c9800c1c01400d840da0060b10b003d0b9802d6510190110818404890403c82520784424101814022080e003c90240105200190050745114240024400d070728a0107800d13a141540c4080c00150f0729540c0c0580418220b421005007070b400d0010800203016290908003850080c030f400140080700c409485955030050b5405000300743c4d1000e0070031107410f00345080210303100e01304c0d41982c0107034040d00400c011140c1c00300300030701c92a034420300040c6944e280f49621010f4007014051644913100361810942d504aa409130b1110a00141150840c05100140c849080c0d034255001d8944800d881030f020304142c0000354003503409409450b8820000c00c0030001007064802c10307a152142283c40c0c0102500f1208816030f140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 661490935 1250 661489685 661489709
    0x30a0f0608061315062d0501091a090d050f0604060b010804050a120203040f0314100b060403080a050d0c032c070b1605010e03031927020a1518 63
    0x225400c1c010319403d015080c0c122043c1c80d28003202030000320040030305820080654504040c86000101c55800d4803140e61621034540c4003040e00c2e50f005654070011807044811040318488800c1c074450202003e4400300310702070300c203429a5015a032027604141c107644007030442c2da01c02c0c4108414002d6500034800700050a0078140b0300c9007800e44030152981a150b80103000011140f141804140c400c01c100d800912040b4040030b107068032441c2c80c07940018aa81c1500a0b0301c03451519900b46545441038500b030210082c41c0074905407540e07a0700c4003590040d00403002440802e004142424401e030280241c02d21850741c00040d20f1039070300c0750f944030131403c40400800c1c541350303c0e1540586030000034a0b90550f941c0840381610307005540c03042c50010705051401001c55080c00d03151601c3c40c0000000d180200021480d81041c4a840e841040c11600310104810320948400c84200009080028070080d0f68000f421110b60726449031600c4d4100c290311b502c01800509405152107000ba245401c000c0503115440f102 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 661492185 1250 661490935 661490941
    0x1120b0d0b16050901080f0907030b010602150c0a1b0c05130605120d0503011a040b0408070f0b09030d14130807090b030106030209010b13030b0a09031101050603060a0f0b030102030a0f060806 84
    0x800038600203104a151a0b0035601240c00c23403c2c100a281c0040d036014170070100641c0c5480000b5200c89602c452041e100880070302241000e6030300d8055a8010520faa203420300e42c0790505031602c41000042c070640308044032103004030301d513110340107450096900f07070001182882c9032009100041180d40220845a00241d66152070560700c03502300c90464440310088480d624418150031a036120f0b42d0711001d680314001034001903005010407048120b6000c017050b0040e895592840c124540f00c0c0b9528664035400101d4010384040c0100d25848841042422007418208408010009410590403040d81270f400b500080005908500401d1100c94065000f4000700d8270795804204100c5060080441182002c0340d20607017541118280c2c0c0081d5001301c15050307039080100b5080c00815044c4410340c00244402e40400d01d282050040074000d0300060020100c603550814550003c0900210b121841629018030b043d130b540d000d00207103020b0004524001060088007240c5d81c00c68000d0380c007104443d001b941c20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 661493435 1250 661492185 661492187
    0xc1c110c090117030d0f1b0804030c330e010f02040e040b06031507030c02063304061805061e06070f0c0e011e0603060f0501120b0d0b16050901 63
    0x150448842100c00d03080800c60580d000d0070340c020312584100d103601d0b082d2000c00d040019081f07090002c5c8402d00c15515a02480e1049640c044111005004150b08500480014901410100c59180404000d0050900b20108500c0412003034065009194031a00598000c0300d00313100b0411166941d0500f18641843d003000d845c0300a0005001a02200045002078103c0c1c505101c1500480e4102180c20030a00d00788602030010320445200d8401841503400048140743c880d40d070300c1030851014003015400c0020540558842d44560000e642060716500b0010300d04150745071441e84d0081c80e5802090310318000090003400300004400854146280801d911940c07200300c02c40b00d900743c125040c40c00041c4582409940407455034002d55140d902a000051480483c0004141c41d40c46c0100d804809903868104400340c44a41c084c000e200702c0901e000b0080756010710796070300e1990000400822401000380004a00140a240030780c3d05004000c01c00448909100607020010340a061450800b040400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 661494685 1250 661493435 661493449
    0x507020c03071d04020d0b042004020304350a0f02062520100903020d080402100c0c0f0605031807060906050702030f01050c21010810020304080c1c110c 67
    0x803e19105860031008038042d501c842c04c0407440700f6007100300e02c04141090700d8000c0070f09100c224100e0707610245100880301840d01c0d00880f40501e401248004018002c1010040c1c004400c91001e079a4184560688112040500141c011800c00d6203560311141c2c526032004c1e003050710080c00c0b08500c1103542e080c03058082d80304003000019101031400380c000e54504104c00e04808005c01110019220300c0b01d401101705d0b072641200c508540319609071003034102d0192003500d41c84000e5800030360000c081e101c0210140d04c103100d007110481c060319503003d04981d18115030301410f41c15000304000400c0001007005114114039030a90304501d19008240701403500f900142041010300071403007081000070701c500075940c0c1001801c2428080e80000c21036400d00041c1c07061144d2201015080041c1e004d00b4120b050084815264100e581c2c2070040e00a054032203150030300950000384200c0b1000300038003001c1310407032040201000c140c0501c1c2101c080103281c5030000d851140c7c034000300441e540c0180c040c4011a16641 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 661495935 1250 661494685 661494719
    0x10b07060b0a0801020d02090a2108090d060906090b0108030c030d0504030c02090a0c110d05040e130c03030801090501170d0c080c01020f04031a0c16051608010507020c0307 76
    0x800007407068544001079104035007580041c0180d0b0000c5004416081640d000780981a0222440790100d41d440109040e0420607c0e03003600020303058462200820701c510010002054000c1480030801404d90f40c110480c1e02010064850a80d500ca40d1810011980301c0b2038098001c0000079424540020702190350b86c4600a40c602d0306507211008142098000c5102c20340942c0d000701080000c1c0740083d90300004001e241112800100780e011198408a8081942403085c501903907090300d054203140d00300f60141005000380c0030010074050b0603004689000052000ba600c640c0d00c0d6400c551411458000317444042e0461410185c2d4140c45c00c10107000050702c03a442240350b0038410000451424800058007485c0944025540001506d91103081084010425079200b04008115504c055035901c248500407501201140410081440040445a80d0390041c1e403080084400049510019105407115680401c910fa9101e40c188514240c041c050340027901c0d0140e0040c50b02034501a8004903008001e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 661497185 1250 661495935 661495943
    0x60402130b010c0b07080702061b0a0305060604030204020c0607020c0406060f110f0d03020c010f020a0203041a071e0203190b06152502120114160c060903030b18010b07 74
    0x40c40340541141d001d00b403490301c0f064001c030344c0b64401e14150001402c68241200c042005002d102e0006088520f50141d201c500d88485100e2400c01003003003425030040c6006000c0c194083c405020020040c0c3e030310f00040c0061140040927010a042404029191400021840e0300c15030030940305101c2e180e44514040081d5940780340003106108031031085401c0c03103a814040744007805801c14006a071a05a0010490100d220000700310100d44aa480405c0b0300904281600503002040100006a031038203030440002c6241d048076140484542d03070100705907044040810310400c00b072840c000f980703230621549141000c03500c080007003007440e0303136030b40181010007420f480c0b003074405010400701200180d017500c16000c4c444180e0348405035204100490f50901f158101d2180780710000111a141301802901e5030b40c03c101a80d0202a290800212502c1040410302e40400c0f841110700000700e1203502440e02141c0c00380e14000340c81c0110b20140306a06070704480420440b81c5100c01040b00740050b000b140c5005801c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 661498435 1250 661497185 661497191
    0x90a021c0f0f0623010305090606040c090e0901060609080318011107050306010305030705070609060903060c030902030d09030c0504093203040605130905040809040504062004080f06040213 83
    0x801c0002001084540c60748800b6614003c404540c4c103030103070095036002079060b0b40e01180004600045060798402c541603840382c3c0280d4042025814650000c00400c142d130700b02004525118402c9203000d000c2101e00d0509691030380801c11034140c001c2d0004000d081840040c62905004500d4940e080b43c03412049810000c03194005c1c240c103c4140729540150000400745d5005503540d04009580703400100003510540940200001d05901801a9004503421038a62001c00741c44c54885000604d0040400c03818191140d044800503501441114103c0d2080e480f0700d078030182542054501c082240c2c00c82c5014030b14040604003c208917450156240311408003090b9062100a818200030502c40d01c024110312020502080c06900480174001d42c0088107420360800b50b9908680044d114203881c0688a0f03201000791107010304164101a6019000703501c08510760011202d01051041d8403d86600c0072080400e003441099014402c1c20030340e481702c000502e400d08103900001c9800166420003042c00b0341d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 661499685 1250 661498435 661498451
    0x3120c0d0915050a08190e0106080c0109030201020a171c020d14010812070f05030309100506010305040b040204150503160617011a0c070b1306031b051c0f020c0705090a021c 76
    0x2922505043c4030b640652001c0c41f1200210030300d00e000c0e161501602c80ca0380100c4940045035403080d0003ea0480790140d000302008036142c0c4404014154181c211a00000101b0003082c2c030f01c03d0440d0381051210b610308010394a000c1a03150900302ca2501c042c4144880d0349034010808044001961503904170340e40203069880910340307816040c0700d01c0c0101c002d0180c00301004001c6880e00208400c03840e0f11700024203100b51783c0c518004504a40044400402147c07116000c00c0142c00c00743c0c0408103400f0448401150907460f240001d18085425001881803407000c0002d102e50b680c17120b00002c0b16031140d034180c0c0d4194105000044452401004240d074031030042030311102e1000c104141002460301c0b00d21665030b801480c9101c564081c072800b5082c0801e0a02e4601c9100c40c054081c100184105503840c2402c003001b030f07100d9148003401e420461003240d0b261b501002280710300f40300401c2001c0c1420002d02e0824541010700000480040c14120180d2042c0441150070f09014506000c02c4003192001400c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 661500935 1250 661499685 661499701
    0x4060f0203090307060203030f100501020d0f03020c0f10061a040302040b060d020409091e0b0a0c11070b04150c03090923040b070207050303180f03120c0d0915050a08 73
    0x405040d0b4020b80c58030420074001400341c0c0200c002c50040120700445005681c46540000f49000d940c03050a0041c3d100755281c401c5240304800f0155400d0b268a005807410344031081c14ae1410035901001240c0381c02004981c1184155031040c500100b00d5001c0643c82c0245013010038955000d2844080d000315280c0c4030324400c5554180c2241e41004502e10110f44071505d4101081c01041c1c1503500300d8401805a00615154418851009900d070340648603080640e00c41d16800003a0000010fa40e0a00844d07030201e10705a207040c070101380a40381d090100e81c1c49030702d0010b454482c0a999510340060041051504022075813002455054074070780c01c4080b62030419403d654042c41d5410f40c84040b25104007042c44100006014034900400d160f600f21102143c440c0d08154403840740003003036000041c119441102a0801030009400d02000406032104608441313110280b55004250041141d00402d07510131308180c010800201030003240c0801d00b9a54101d041c050310030b01c240c036010b005108000c800a1255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 661502185 1250 661500935 661500937
    0xb16020f1903020f03030c0315151b031c1e06060219170d09052109040902030a050105160212030f0c0903011506030605010801090212011a09090f060102060703090804060f0203 77
    0x4084c0e40000c907a03881c60000400c08841e0000d17281e09034225540d1812012038a045a03100c1c0c0c0e034240301c59034146048031540b09170f00078598074007101c8130381e02040c04800040b411995240ca02d2000c10fa502007642d07040c002004610003074030700c035082c0000d04d411030900840d5400524465149820038002c6242056070515420940900c2c44901900100242d10b0760642285d400c00c1800a00c05c1d8120b0b130703452101d102813941d882c0000c044805008000d0111068501c1e0903044400a0790000c0c0503184640d0050f22440c3c01d4500c1113825100c200c48169440640650401050303d40302a0000c0c2c190079400c2c84a00080055800340020f8401403001c02e007400c150f41d00390300010120085140c0000499520710000e00580307018820a4040b51001000144202c990700869003402021011210760340e0030411001d074550b42c82480340089880c10b1005407101c2e12405070450090380c50119036012407800800080c40c281e0000c10700300806040100034400103411105607820f03100f00d804c0000a407446100120700d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 661503435 1250 661502185 661502203
    0x60e060108071106042f1f030e15010f0e0402130b010e1003152108031003060e160641070c080c031b15160b16020f190302 54
    0x28041da60074801001080f1003000000c03440c0c02072950b602070b003a0750105803141040282a4004000c800341618031f0790024400300702e40300710741000201a42c4c0c4000030340c50100e61420610f00000780400501c0042030007070080c8002c00701112440c1c80c3d407a2a501050380050009800c80c00c0540701c052031071309680542201d49141d4006822108405500d98004014010b0ba103e40c9001000120000c2895030035458040080d4810703c440700c4e500781280d0350390a42d0740d00c02020000c0701d501c4000044000341290140c0c8440040d4a0000c0000e1190907080120061203940141c080c0502c8100d400c3c2e4103000c10f01d100302a41e8004030614903003041084040c0090ba0001c1c0d440c1c01022002030b04400b04400d01d07652a055580d19004c481c1001080310905030303503050240d800001004c011021100d80e140c0b01961030342801400174494103101000c02852201014641c00f01c0e41e4003007490811950f41e0000000301c98245151004000071225101d406484000c02c0403d44851443c01d800c420074103008110b5460 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 661504685 1250 661503435 661503467
    0xc060b0f060703030b040b0d02030a1203060512010209090705091305060f1507110d150c03090f0605090c1f03020306030a0c17060609010614090301140903040612060e06010807 77
    0x541d40c0b5203440c004004102c0386407103502c60b03031400c0340d541403601341f44194080c070b80e0f4040d000b80151021506c440c050448400f50280c2055201c82002c074468803014507850219114000150300d84065004121144400034085010401d060058201550703407500d03030f58401403803054002036644030a000304441065034050b06400c480c40000c0100400c041400601c3c0700c1c0c1c00b40c1c00b0b01c02d103070085c030040081c80d074488440500445280001800d01e0302241d40855215641400c00050310100c9503945100720b82c049005803800e41d41e036030420140f80b0060080c03451103401110340300d8000450391231112000121052410415a02200290040c2c034100b001030341540d0041c02c6030641c25500c519a81c074901188001d401a0b02032007000c620380b4281a40020305840072a00c912505440d80c201c002c440b9046900405d516640f80e0312102c40314031400b000540514481c40203142e80302c1c140702001d00824040b101844030146056030400840303a00c6d00810790400c6013442c101425858140080b12403240d034407038001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 661505935 1250 661504685 661504687
    0x1501150905040c0504081b0904081b1c030c08060109060e0d3002030304030c060905030d0906020a0f09050a03060504021203030106030b090a05070c0305130e151f0c060b0f06 76
    0x154125001310151003258038040488000c0f0141282031120310007901030068100002da0f000c100003c04542c081c1c00d00c51043c0308078800900d103100003075181c0303805113804400c1000c80c030811343c10566141c0210034100015041c4001300703041100008100507ca071141900300125040c00d00510380e2080540c030100c1d600320001d9104680358900081880701c0444104459034004008000074500200940e0f1280b5016201c0005040c4581c50b10300140c01c00501c00c4441c1c0c04204640401140c2c1b5100d0741d00c03c10b0066100507281e06a10750090051000704010800740900c0910030003e694030310002c03c0c1a6540f001c2d0109030707500c41d4404282c0130785045507246030b203002c0800041080355059001403044a4101c5440c0c105844810144003116016110f42c00059551000c04000c80c4c0500003d012050004250101c602d5131520a95101d9030240e9240350341d80900d501c42040c42c941200c0486421000648841040500400c041c208074a408001411070b030712250406410381d50003240b14561000501f0803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 661507185 1250 661505935 661505951
    0x9050a0e1501230a170c1e040203070504260606030c0d1202030403120e04060902030c03070e060d02040314060c0a020304061101090204060e06150307020c0d0809040c0801030c08150115090504 84
    0x150030016800004038661150103103200b86403507c5007008081c0b020391880307588100c44040601000c0d500013004038040c00f608000004541402d00f05101c0380c00704107043e0b21000b02c03056604a040640140c200c501c6607001d040a030381c007540c44e442c4c0440d403154403021618401200c00401c2e03045004580c40581a50740c0c0d020006203860300512403461008086904004103030b100c100ea07000300e0109540b00d40380d0000038400940c00307030f004042100c0c200d00000c00003400d0443e004401d80c2070707038410381003103e2400ea1241030754081c050400a071034000104c510741600b00350703241000070754900480c4690020401846550301d104542948a1000150098004e104040e180e43c0d117103030a20400d46010b030040b0203600b08a210500080140d80c05030007198060f0103c06408010008013000a8074291840311003001050500d940f284070754030042203651181441507140d81403000c120703246540030720701b03580219034140c1105417491070250540d240302910310070035182c514003168880842c0d000641c000380f0784214 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 661508435 1250 661507185 661507199
    0x5180d0c061205270a0209130606050607050d18080d0519022b030b12072103080403110a05010f02092404031103100609050a0e1501230a 60
    0x5004191511926140910b8052081c00d004450b4211303100c03c0f11854100d1a02d119445603110682020340c50750445101c0020390b00000d0701000c003a1154008946404201d20130070a181c0941c41c01400200e6610381464001d844a603120b041440d001010410701e280142102a54040f4038000b40c090b190845180508500d80500310b6840810852448442d002c0080200341c400222241070340318010307a010300c0c03c6403401e00c2e400000c18001d0349000c2c1a102c0e40000390315100c10350004518220300340102185442e164148843c543c00101c0a212600180442c401033604000b54a800560504d00341480b0201f03030800310704140342804000e149500b0000001007a02480c4c01a1440100c00c845410f07640c1883d0040680400341c0140403041c80030705100800220303060aa4185006d540601039131244040e000c0035604840c2243c2020010a50740c109105101525225200007040e002c070041c609030b20540740305800c0500c140b268103030461640048400001310320000b58000b001c050306c0041140c0c2c81b0f01e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 661509685 1250 661508435 661508453
    0x22060c09051509031f0207050a080904050c0f030408031801230a36020a0e0a06051002060f04030e1e15090a0312050f030403031d06061005180d 63
    0x710315441001070701030042c0c101810b03404035100da1100800506642480c403050609100075a888080455400d02803040070610034001030300000d2161085170b03585c124150400048820140c500c400400381804900b03400419442125000b5400241b030540f2691038010a2804038001520446c440d42402d8400d5900000001c2d034541d000417003845030344107594401c07001003190303450b641811464980d4604181192003003d20700b8110a82e220710740e0700114454001c202802c0e100d600500011200004000c900c1305244628806024111580171483c0d0100c8002903440c800501098446045500407404150141c4492085440050300020b47d40244a1408400190149a55000e1018100c0405151803040d0072140490001132000c038117a815a10381c11214141100100c040c00001c200c009080300c800d8000e075200303a11999010480b0480f0ba0f5038031030541c1c081600342000f03902c0081440708554403004960503000e10740c6010b03a103641340c0350b022507440b840b2040c94a803ca04085d141d001400310f121 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 661510791 1106 661509685 661509689
    0x20c100e031c09090e01200a110717061003020a0e07090b1215100e130212090f1c08010b0703030e07140406050402030f22060c09 57
    0x815104001c40c084405000324001c0f103020064201e50740218022080824028402c0180d41500000800fa2409121903100c1010461103c02d500c207114207650074030110221000d2643e20f5128402c54030441d00c3c1810301d40142c0300001c1b81e03030070140788000031298050a40030440340f400c038004451041c09030541081080040e0001403622103840039101d04510006092454200f22081405580049545900030b2500e005124059904100c18071303c130800644280aa40f0030542419000b840742da460a480680c101c41444100040011784540d00408034085920b0b0585800700c8241c841c1c1c07145140c000045218005000c0500d00d14090500c0c42d204e420003117000c0504400b4241814110342081c0720300c0d900e03900d0342c0e0800e1406004000041c070701541d08510f1400e2400c41e07004407507001080c07104141200203466032250070042039480b000340c026004014100c00755000810500540c = true := by decide +kernel

theorem cover : BRFrame.Cov 661330935 661510791 := by
  have h0 := BRFrame.cov_init 661330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 661330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 661330935 ≤ n) (h2 : n < 661510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
