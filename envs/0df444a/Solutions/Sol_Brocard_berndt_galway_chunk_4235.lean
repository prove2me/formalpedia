-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:57:49.575303+00:00
-- url     : https://prove2.me/submissions/845454d7-f1b4-44e6-bfa2-d8194f3988f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 761510791 ≤ n < 761690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 761512041 1250 761510791 761510831
    0x112050c0304020f010c05030c0a15020703090509060d080c0d030b09090c04090804050301052e0f0306091403130302150a02150405210d0f09120f03060f0810 69
    0xc0019804104003280040c0741c0090741c0450b020341814040b0860b8000e440d502d08580040303182c3c2080360030458001e81080004141609810010841141403030f0721038900030203000e098002c4a000c2d5240e44046007543c0d81c0c0d02560a84540d11144d00c0340e0318113628034800c0d222414801d21801090601d40e000601d450507601d058401c1c085003000b40782c0ca03240780c010080500308500090320140c50801c0041580c0c0c0f0203014003445030101141d8203c5111650b28207160004c0d9a0982c10315203420031800b80300403036009402208580c2c0000c4041403032119400e0441000d040141350050622001458070381138810145411700300ca0003221207203160034840003a5a882e2151110300c10060304400c0f201d45000001d1140035030498012022580040c0016010100442d041c01c64142c032a4804503664034607103000d0149040c8044d80441c01d1010304003030f41d100554804200d064500b8401800340d404c2040f84603a01040040150740240f503250359485441540b2518511526554181000e8401c00b56002c0a806 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 761513291 1250 761512041 761512051
    0xf0d03062306040b04080f122a1e160b090607140c0913020a05030a020303121e0a0e010f0b09130305040308130501080106020f030304060e0c0a090b011205 68
    0x6281080000d1007604240128644415920800622010604509000185c406080c01c60000d0105400101c07103d450f00004d40d40025420900304540100310b001640224449025442c01d0451003801d43d034140c0c10062101044d41007a030100b80380d14151080040c0e00030107040312204510805490301803c003c14440c44190a400070410030107000010880d003804100c20189000391940701008c007000446000c010b40d04078844000145150040d4a408552000104000c43c020300c3d2804413a070200303859002e01d0704006005081400011413850710501d1901132040300798030740341c414a810301c030002c01025080442c1c4d00c0b544c40c1c116007400390021032241c0300007118000c4c4005003550b03480020500e80010160200e007001014880003000900351005801201454070300702980d141010f0004101c0003052340031400f1984a10305074040d41ca1f01004490b0081e4000601080c05890900031901e003908605d025900480c405500189114150340240d030140c500340e0361540350f06465101003060300c805890f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 761514541 1250 761513291 761513309
    0x51003020a0e0907030209130b011103041203050c0f01090807061a0f0f03030d02040306021801020d0c1b031e0302010c021b13180807050105010b211f06020f0d0306 72
    0x500c2000515203e11200d510855924025141401c44c90100b001c10b03172900321000140d502d44000084642e00048003030030303482000c0003c60800d840d101d24421008500d40014050107000102c80154100501980b01c0000c2104000c0c00f5000043c03801010302d03480080d082d55100d1525901c4400d9021050881c00c001c040186800a004010303420001c011401450483e0b16110030003450040e180d4034000342c001180140383c0141c40c0d028402c210310000c44480341e294115003003102900d0142c1d4011442a05054001c040d000c401c230001880f050002805410142030710300c031a4092030741700074140900d0180500c60350003130016024104099a40320841c90701d041c40c3c0301420500e144281041c0000d22420304140c0c201184148984c0aa0341298a031000c0070b0b2a50f000014450701030003005d01855006044600c0380a207091030450715450400d550400c81007000e950310020908040f004c008070b4088110b4901061940c650300d45029682e01018405c29803e0300036003d100008902a00c96601142c2a0503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 761515791 1250 761514541 761514557
    0x14160302040b0d210201060f081b060910030218041e060509070c020d05071205030c0c09010b090d21020c0117010b040e07021207290402031c02010f0f06051003020a 72
    0x4099000000030134666004643da24a00080c0c401c2503844c40400920160700a081c000912200700c485440d11a518280100804c0256200f1600c2da0022521f60180d41d00c1c0c016290380d41040c2c290b058072410b00e41103a12a0900b07240110f1401404900115803841c2c000c00c01c01c032540c55080c895200000c0b22410301041c0c41142c1304003d07061820005d00224030910544055648444161000c6003000f842610310348c3c008034089055103010400c00e12070f40011205401d15600d00280c080d80c522542d0348080c081c042600300702c8204001a106400e5101200002d00d10103140081c0007580c4101c0021311a00041c984203030307540d40c084030602c1c0038140c50032514103031301d010304160b03c4012640014000c80214421580101c80b044994400342c0180e0744103001c4109110b081200d607a03c4103001c0038440041c0c8040100b480010794001441c1694070300d02c500414604152140164010042a00841c0c0f0b003e0611451600d45100c50f03002005850084504094080b1258022800c078004c4000c5080422182 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 761517041 1250 761515791 761515823
    0xa1a0103020c010603062307022b0216181d060a150e07020102030717060a15030b0909060a2003280c020c04061d0c0714160302040b0d 59
    0x10341c0042c80000d48903400030a10540d280d0b10705049528880300240500e41000090b0f1010034452810340e0850344520050885a03031800b440890240001800111010548104044a802030004101e0880e040202004481d039501001c9c101d8012801691000d41c81c0031340c80c40013910700010b440ba44da04000e00401165669864040c000c01c01440e00c960403050302c140010310800481e01e082e100303020340d80c00503840b828012000b070000301407501e20048107070f07000c0c04008050701c4da1046d078821904041c1c8802c50f0b010700e1440a400915140004580101041d400c1003200c800000d4094019003000c00700700308040c411568500c107280700b00c01c403203454502000404c684000032004d0030303170380020144000340581d508034002080310f09004110001d40c00c400c40b10001c0703143c2441070600404107141075a03440000003801007880c000007090140790348004241c0702c042c004020900740d900f80c4024211990301140400040700d03408548070403445181441104280da040000e038488481c4d40c0300200001100301 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 761518291 1250 761517041 761517047
    0x3280c12090b01090e0304051302090306010e09030904090813030f05070503150f1b0d0902011e091a070c0f030c090911100215011401080609010f05060f040b040b030f0a1a01 76
    0x14505d16603501c2d100a000110fa1a0f07182e18081c07000c10045100182c1c0c4030f20103400e260034604160b124400a10041080202491001c42220100c0c4030441e4001080390305481c094119014000800050221040c4040204444441d002c40a02e001e90212030201d0b0340c0300201a41c820643c52941c18040001c00840c00c03002e4080c40190300007110001220f50445003148998007a0801004904800d4a90b40001c0c21755030000e11803240541c41c443d66402100747c0b0000030740488900e124044140d180034002c1e9181030346480990744201c2d840388030608000d584800070b45001e0380900090ba02d841c0f60345400600c50030382c3c0c4a11980c2c0f03a07020204110180c0124200100f00007030314051001e5008040d502c1d01e0f40000115424040c0001c20642811014080700040c401e203401404503010b043c41c8001400622074105e050800c46e0011507401d941e520b40c401503855075000b594003da94510b0f0200e400b203000c89400e0090f601c50000c84080c03150340c0c3d031480080c20680f00c202d240e03c01c419035041904082c5500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 761519541 1250 761518291 761518301
    0x320a03030e0f03041e0e07080a0b030c0609010e0121060f0801020a020d030f0f0e0607020706110c100207080a030207050418020d3f02010507080708010b03280c12090b0109 75
    0x4601d0300061780c169848841c504040f0b0304070350700c0b40090000410040c0e450043d01c01c00c1c1d40c12500b036000349030300f0000f1008a4942e01c50b40d203c01d4180222424201016840b4000710180d03c070540000c6600307c19000c0302707070018100c03601500952040610000c02c1c0b120051080d20101c1d00c00741d00810007106070020981c0100203c0c07040e205042e440d40749484441c4440d00480d242e03c040741d0300034a0a0300d40018000c1c00c150164104808116070108185020200000c00c29090f2400b103c0d010072100319002d06900e00070143d44466014081d003488017080c550080f9141c1c1c11910142c07800d0002e094003420040a030030016100035032104d8442806008210503140c0701c150b001d14244d243c0c00146000c40300c8000804540034800c00000c141d6020205a0303030a000703042c5c00013098201000c450601000190249505024100c075814020000607201403a5030340000c80c0e80314400c250b590324480c030207840340a000300d03040c00e0000c240100142c000c2c6440342d00ca03040607942c01201b01d042a909024164021344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 761520791 1250 761519541 761519579
    0x604030215041109160305010906060c0210051606090c050109080a11030708030f04050301140f070806030a0b2d07270f08100b040204060507320a03030e0f0304 70
    0xa603032541c1c3d041554640d590924003c144110f07030480c1075280090300400307840b01600180d03406418002e0401080360040c81c1002e0040d4103c4103040c03280c01b5180e0486203070217082000705c031001045180d4401c0c01815030201000c1405420008812511a001552007500c10b11541c07440f80d0040c400c08010441c80741c0d010083c00c00050944500307940e1080c000380f554108141d41070758160001070822440c6000d2180d08520000031013017000b00c0c509804030200c0005d00805540610a40f000062401d99050088080484c0c2c4002c60700f10505000e503181e08540201102000e40c40488101c180701c107840304400b80d12900450b51002420f000007040301c2c82c0a0b200480740e500d0002100008541040e0740101000a1b0041c9401001c0c0c1100c2403096005461404000074010b510420040c84055405402c03140b415411a000c00010f2800c683c0c010111118840c5d8907011020048080f250148049844000715010f03560901040009841d080d07156a0380d01e51400c2c1c00c2e80208401c1104845940d2045004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 761522041 1250 761520791 761520803
    0xc12020d11220510050712090909060501061b151a041a01201b0d02040903030b120325030c05030a020102130602060f0c090a080f0c03060702060403021504 68
    0x68184420260050341041c08030041e224003144240d2005000b035206a030040c0b108442c0d040b0403580d070003806011845012009020429480e030800480e44c0a05000030060031040e0782002581c4843c00d0220043c4000c2c002c00c00054400401e6031091038001840d007284a4000c190b695241d10040c5651000f40040e02e6040203002c19200202442d95451080403c8404d108a0f214150180840010000020010680031407040150404001d2000081380c0f40703100280001e81c0140c54400b0005801c030303804203900075441402c2084100805a040e08010441c0005540c0c140c0d040722010102d40c0ca0b0f002e0791060201c99002402500c843d07508904540c0c2c17074140242070045025950b6218182503600040f01100541c3d00091180314428450120307100034070044c0b010340002d050a210700c2c00e00e9130025200740c030300c14408200e1580032f907110607041000b8201c540484141d50720100400d034030b41c84581342061082c0900b6000031801d80c0081000c0344510381c103030b0280048526600309180c107035038091300c190780d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 761523291 1250 761522041 761522051
    0x40c03090506042001080106090e180d0c020f121b06071a041703190e07151808030316110a0614040b01141c020f06030103030908100c12020d 62
    0x1c00e90030711105000d24002c40a082410741c81405141a5034006602c460401ca24040100507095000360601e0585004a41201046d204c02c040700161030b1654201803032501402542c001003030381110f01d4450b02032098038000034000d1041f0030404042c0003690000800d4200103000246144072254602c002d4400410650405400c0d4980c3c020341d0300f074080000342d101c3c8200140014020b441408484030b18090026520b11b1500c07010450058000380e070301c4103043d901c45041c1103915405001c0000a800010408081102640d400a250801902140c545030741100c9010500c400040200e80c85111504110810000401c0045840d0703000d854001060340544860800011814060100007000003800e684c40e50404c0d042022036104113078065454043c076858494600c0e01c5045002c0c0d0034052104281c3c800c000340d4004030354500c81d1400740d9680f18a0001c000b100700b40e0405008419034004404680800040301607040465520b0380340d00b00400c064010031100000c0640040c10710352021100030038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 761524541 1250 761523291 761523293
    0x1080408070f0f050c0405160804240c2c060f07120c020f0a060206060f0d050102030901090515040203030409020f070510050723160c0b0304031d0306060a05040c0309 73
    0x20795140040c2c084908110310501e410a0200422412403103640848040100c2d040c005113601c1c0c10b03440118004280885030000500b0b2103d2802129a01980108022a01804013010308010705100c11500d02140000503c907018003451041f40d0b58000031000d40c200306202000030841c0e240c000300c50318040d031001000756000252031110034038201c8545444402070080d40384104028a4200c888042c02100c21080401c903040d030000d041c1d074002c481a04c614040d116048042011214604400342a80d0700000c01e10039600c1e4154420580340707000320251040203c3c6120018001d610075a00a5032581c424001800070b1080b59000740120030040c00c0c030701d00d001c5055503403606251448a148403c03503601e40800031000c2d04104038050101112807072610710200354400900b1b0380564203c4c4513210841001345010041d0320270b0010040c0c80c8488005890f450107140042010070703e00b07003044d404070750842d02038000c0c10b00152550042074001c185136076950030481804014404d89462404260316800044 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 761525791 1250 761524541 761524553
    0x602090607060c02160e10180e0a0f0b070507080f0f07051518070b1206121507140405030a14010f0903050405041107080d0b030c280506030705090108040807 69
    0x38070480d6641c005d0080307070508000618401c400c941c0503466660b402400c0220704c0581c10305041c00e03161405c0c2000b103001c811030400b500074511161342800905c14080010184081c04c94400740c424840c0011094940c2c80010407079542c000c40760020110082406078101c401000409080e100c0340102e20203081600d640c5a1601e03200340400003507826203400c400d0080401404030002c03211909000240b1240d407810010702000d00c1840c02120301c42411034040760684c1e96400d40080a041120200c8080344501203104034100415903040300400c48030b865844ca405910b0098500300c50006010700b40d410069141c1d1807440107100045000c5550329407100c4000009482055021070083c1c1e14561528240010b110071142c00c06034441503070006100e030760300003645882103401d071040b42c000100c0c5110310140441c0c43c0100d54883c26501c00c440110600800e00528003980c0708010119081c0500da61f5031702409500d200650307040f00042e90411110f0360950042d110280c100d807041881c180340c0043c6450351 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 761527041 1250 761525791 761525801
    0x10e04050c090316140d08040e041415100e070c210306080c031207140a0803160e01080a09170a17090102034302012306060403060209060706 62
    0x10951008074018201c3d0400704101341c2a4980c2c0e451041043e424400d11001000302140a2441050f50403118001c001c18041541c00410044c80388074a14280380c90a1000c1080a06400220b0310400c0668400c18207152003290040018011a03606142005007901030114014814801c1c40540c80712240040d01c1070340d4682c80510802000c04603074140c107100605860300365002200307a43c1305013001c64443e0f9021a1405c182a505030000307507114203d03d060910081c820210700224003034030a05505111010006601c903a1401005101c0c035481440c055600100c0045610300040c00307140020b105203016806541e590703000d265602d00f1000c6801c81034006a0018092500140403c884a408901c807020b54580082030b0344029805c40ca408000c140c0003180011200490f101c0e4084600003004003a02600100d40780790054142881c50000f01a02134a03070300160f034500f0300d6036000031904000040c0906002c1c00c0014802c501d054610344501010f5040791518552100c800c0010100064140c860 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 761528291 1250 761527041 761527051
    0x20c0102071515290703170c1e0304050d08090703020406030c090518331003020306060102010603080d0213081501091419050c09120f0d0f050a0c02010e0405 69
    0x41074042c88030340400c1180f04254448401c055082200d8500900030841c0e02c4001c05140403400e8650080f82400c903031150440c3c0c90000c050310310409001504100c10020b20301c0340f54a00c2518500b000017001c080307143c401181c01070007540004c51003021a85c8561042608250881c0444602c19100e400080c00c40e07280c0e900448100001e820100041c015030700909074400d480a0016241d07061500300341d51140641061000c41001d41c10181981418290100e60108202000344035146020585445121400d0000b41d01c24031906001489030740c414050343d0156540120000e041c528503140190294008400d5401072048038180401c1e6403a0400a031442840304c10b400e14119417401a90b80120741c0084c928010218440003005546904017a80e000308070f180d01d000149941d218503c02142e4000c120503507a0103c41e40f030600a4104000030301d1002502400d06491001e81c1211060714000c45801007400810002c0c403000b0b80e1a40583c540321101d0b4018107045144403001c0000608440b01250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 761529541 1250 761528291 761528333
    0x1020c0604060f1413020301140a0209040e2a0a0e0403200a0f0807051c0504050910030f150f050c030411220c020f0f010203040b0a110706020c010207 66
    0x10001403210703d008000340780c516002c00b0840f02200348051011290020f006811362521964220210344095010001c0340c0c0e8804220010f0341009041c4002039407221040354451800c00781c0c0c40e08007000224048130000e80c0418805242040860b50303020501160b1080340d44040076900000e030206080042c1407159100e941d44000858803e503192000c2c0c0c3e60000744c4a02c0b6881030010400044044500d1070030203070000c02c15900c5031850326040c1e00d00b1151845188080b4484917402041a03004805070059901c11146820b10380d54601d001031040d10707140700103040310400010030404079100350841c1c1064881000c01080400308600544180d513801c2d200200280e03030010400003800700c00e242c910040d14003156000100100710040302c2c0038000001e081e00460381c2d0b4401c2101480c1c001c100c123030704031a11401590720400240078114002e4004031004d88032250070000040a0441902c40c1c08a00c41c03100c9605030070191070303403a41c800079088002c031507445c2d6500700300d9030000c580001d03020b0180b010740b02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 761530791 1250 761529541 761529553
    0x5180d0b0916080f150411041b021212010b250b04060612050d03020a020f0a050604030206010f080a0303020a090b03040b04020a051903060b0a03150204061b08180103020c01020c 78
    0xe22004034000196104103129001240d20310303005180481d80d0b0504020f81e16032681180c0716414806908255000c55a6000340307000d203001c08040e092707141c03071030342c003406400380e0b03004441d0852450048d204248440d048204040014084030280001130056a03003041c9041c0c84074803100c002071201406102e8145c070040c144404220030400c0c2c1e4012240a800503207042c56070710070b0384d0340c5059540058000c10402c2c1500802c00d007800501c200000d240005208040341c030440c8817410035a0704c448003a5000c0d00140540c2001150744041030606000b03c0c0c031050b00620403403820b51001c5000b5000118140c04012480e00b00041c001c03603240c0030710700460040392051000e09062040010f01c282551102d40143d46071020701160190444400042769080507021400800c010005603800c502a04000d0403030801c000281011900c5501910030740d646600c90000c0310030300d07902d03004581c0302c0700600411415081108107000541e260146d0b600400c18100035007089580b0038038500303a80290081300b800e0741c405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 761532041 1250 761530791 761530813
    0xa030b06400f061202091b0d0f0b04050103030c0b091c020c0102010c09060c08090f04090b010305011a09070f12060825050a0302010507140109060614010f05180d0b09 73
    0x900c503100c420750100408100b0703c0d1811810301d04181d400c00780644565261000250024100c001c8040e143c2035a4442d25501c144074004d8400500d008000c0d01c0b1046c6c5011100d18260915220f002d05994054503404030302c180c1130341c07507410080c00100082d115002e022000441000d04a10055294040b600600b004080c55000217007110340190004040205c5003601b040025048030f015448a6008140560340c0c0c021031003c20741c44d0199244903900940f4141c100c00603c25403d44036410382e84610024403401c1031010413003102a04541c3c0300780d4400040000701c4c006a010307642c110500140c03400c0000f034140345883c409048031101c5d4071103c0780d5000901c800e1410712070345480d40102e0440c1046070f03207a5824007020665000d001d0200a051090016900c0c0500c817480c075115000c101c40100030312106840d490484081c0c02070348610314049644a10300041036005803580c10030503146a0755241001980340300a003000c0304ca00c102c03076040181202d440010801224180e03205450600c02010f0740100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 761533291 1250 761532041 761532169
    0x306110712023007020d0b09061b1818010305011e020c0709051b130e0a0c17100b03040b07090803041802030601051c0603110a030b06 59
    0x301d01c8085402c6040d2500304103504807607544a4030300c800b240d0120515650a4082248203020010b5482100207203a80d0820001c084610b01c1a0808030030f80710140c441e14071001c0580001010301d4201306041c00105411043c0d01d000281c0300348002d010145140b040c02055107480001e070400e0b2090b9440c1d00c6c1e105c0700142c2101400c941000c0f0000214038000d0900506602d4144074041d1200c0300d500d89012030460300801501388510200c8040380c0b40d4804064810700f40290852160034441010034001502200341485035007080d00705604d941c0111800e04250503d1041c00402071562010301420100d281491035014521551250b608255a818800d40c041c00c00006648151200d6104002c01d126400b85802c0f0840c0102c0081d20241e01c0b9214000140c81d80d0144109213120804002555031400401e904a4800c5a004410401105150505008502c0300c2c50001812181c40c04012450700e090001036020340b004050441800300d521402d40501500c0080e00d0744504141d048282000d101c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 761534541 1250 761533291 761533313
    0x822060c18060f0206240306070e0301050c073201020a02060f1321030f0c050a030c050f1e070b01150f0512060d020d08030c0d060504090804050d080403061107 70
    0x20307824204090800f031180295a0312000b44010045880c10265510003104030380402d041074070040c01d80d0150b161088005051001c6400c80e01d201e5801c03c0003003903010a1080c121400b154210010400c0f01d0101102e03d401c0c2c250010440076036020b00960359001c04400c0c8054005d9103a00d034050606401c0480141c1a15030001d081103051200d03000551000602031a10081220f1600711581c02e02511048181c2c000c184060944000904011140e60b0352941b050041001201030f8404000c411300340c02c1c040b0f50900070f030501408480000c01140400041403000f001d0701460410b25549807140da40e5800074800000c2c0c2c440004003c101702c1c0c41102d190052411050002a49407050800c0c0c0d02504c6042910005404207000c0d04d000d140040079074403000c0181001940001c02c4650780e0911481c5240d40380d0110100300f00c81440d194000c641e5281c140a00d030390725500203103600d080c5400c0c070701005900040c10404403413089080000100082040c01200080503d1203c190340b5091241003100d8209 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 761535791 1250 761534541 761534549
    0xa140313140718060e012c0a0908070f031e091703090a0b12091b0423010602060a0c0e031203101203080402130c020a080306180f01031a070822060c18 66
    0x21f2119881703940e45540c07413544100701c90146829100c58550004d0f142c010104100080d001406c00203645090040119207259038900c81d0b51104c18420403044440c01e00d400c04c686400005240100400c409041d0310aa28800400d1b0f1040da0f103030040c00c1c0700207140001d17543d205c00c0740e0a4000c249841241c4805400b1940000c0301d0000d082407080000b00c00d0003850410018521460743d910341072104010308003008041901180c00003201c0d503100c1402a60712101118900403040c207080c048220180710340c9200c8000c010207401024506482201d0640e03641004240300301002200000060303100044d62103000460080e02c810b41d031410203005011040150000b440e135000d0901001306055640084d403521a1a00400c1c5582c0b01d80b43c0c007000801c407100904d1643d641d112818203011400545119460403684a51445105441c46050f10920014201d031402d0200d4007040c0000c00c1e00d44400b200c0100c0e188900c98412006007565210310444a220441c00c00248142001a10b50031a510420002d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 761537041 1250 761535791 761535809
    0xf0c0f0a14070308090409060f020a0207080706170115020c1005190c0203031b0c0a090b0a050916030b0a230a1a0a050c150106050a140313140718060e01 67
    0x814115200c84d4014480c8440b141c0c0159915041201800410303800503140300311b10070042d0b50391206620000c1d03039110f80b0702075200c4602407844001042401856003004035414143d05c104568a0141d02c0c0030850800e45100c010760180704216600d5503125032410244882640b515a100c5185603001140c9424099246d402e12002040c0030000d41d8000007542c24100300d1818001c48440c0301407030b4508042c8008049030f0802d44003100869a8a01c0e0341240501c1c0d4010f81c0c881a03000e556104105280105507250002038021282584105100ba0800044110050f000c404529902c0c00865101e0141c21401da088003409802001036140c80e1440000511405e10b050f0403408100c440c1c1005442209100028001c0001d1424605c1000344505086012110100589507945800c040e210381c2c03002030408000f07014042024103101908050724091580004030136030070412540c4c0c2840c90654604d040003e0b10078080c0c0001c1221146a03460410004944080b40c400d2805c005140d5840c4103801c50704403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 761538291 1250 761537041 761537053
    0x609170d05040902090a180b090c0f07121b1a1305030a050a110d020c01020607020106060905060a0c17040503010f060e130804030b090c0a0504140c0f0c0f0a14 70
    0x60384041920b09941296030b0059a0381e102e00c0001c0c3c906061a4840208440016154001c402490380400756451003907840c80007541c0e8a10040015110314407640e603807004180581d00102d80032118140c001c0b20b45080c0a003581220740120040c0a510850444201003c50205031314000011080b81e006040b0402007006000b041d5681512401009550b100304000800d400c0300d041c2c4121000031440c0b04031820703168030400050b002521801c038602c641e40503210b200d0109202c10701c14480c400407a020750b991740c0306140c1410104601750f8801c1d8981010407071003c1200c400700c1d00342c0140003546142212102d13581c1c0d1078a4189030a49054200840501d1f2914108004444070708944a41c004940290005121080e107040c1c8824021340c0c10103401c010701303001000074940000a801d1140d500440380a083c4550319410001a03d5039a041d0102d981203000c007084005000f000540103c0d074442070010b04240c041000e0500e4178a1052500d1656400081d8a10600403510003c406d0f11143d0406014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 761539541 1250 761538291 761538313
    0xd260c0c0a0c1410120b03030409180c0609030b01050f12010203091e010c080609091f090c090501060c062708040e09060f010b1804060b030f01080309030a1119060917 73
    0x112040c0c0c0c1c6000d001c0103a1b1079104000d0316075400d00c12280a040d0310601000990002110389c1d1a4445d010800c4940303541d0903001142d000d0184200c1d404980c0d20240c11100e6a080200b800480064500d4103900801c211070405408402800a1071003910b45034001d02c0d401212050301e540c4100ea0460203401640740c140091450761748040d4096020a0503100f413144c03500c51414641c40e2001601d8a110948401c1204a0101c1e03101c0d004450703660f005440900e4a00d440e80070100c200d403c00c1c4582004115036201d0301c400240c0030740101c15462040070104902da41102101d1080700c070b03905401c8500c09400901813090b03070545075516800004250080c003040c1307004045004602410f0084181d0588041507080302c01803400b0300702075290005081441b03070a540d002c031030b605600b00f529584170902408d0004a2a5880041900d11000004004006802d140d89038515034146074454540c001800003a80c502c03240b80f00a000000b4695980c1b8440f15902d0040382d07404140000d109841e45c1e8020340c1703100e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 761540791 1250 761539541 761539547
    0x2030106050f011b0f05011104060329210d02071a04080606010c050715050a022109010c1703040516150906110114090705030d260c0c0a0c1410 63
    0x8001c0d00c00c1d07075021007000303031007170a020071000c1c84100c0c020260741c2404000d0340300d00c1c1240e003e00100c0d07a454a051016419000950724122f550820941e4085c1050200d4000b61401c04020501c040d403500c0464440d80e0098901d41c1442d100d00918030145c4d1007a141000485540d0858200c0311048290b0703e401c15081456054647d40060301c0141005020031480b010310105018040003040c40185002d004412800090400d070040700700500907015079000f4000e078400400c5111a10014800500d00d0007415100664820480170800e544458a4020941c080d05404c80190b01641c040c100070182000c0e07462451802c0342d125040801848010800003280d1a0811000c4042c0c4045040403007080241800140c010421601031509130b0714440c0c14406c00c1c80012500d40c00340c03401035096504184042e0004d4818485040ca55950032203240c11403d04003052202c40c541160380704403440d190070b1240d1240d5250400d44002507a452a44100c1041030360213034a04211100c0095070124900c2d0340306c900c09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 761542041 1250 761540791 761540807
    0x5070e04110702060a140a09030b06010807090519180506041b0c0201050a030b0306151306080c100c02030a0311060f040f0209042604170105100b070c091802030106050f01 75
    0x9001e4240401c0792001d1711300a00310480648110311445450300050040240003860511003a112112504081115035100b50100d0303100c0c58030f0780c864003621740c64042848030803006440c00e01c00500070700e41c0114400c001440d00c02e0581604040100c1d080c14080f0401044980d03031030000300300c5514906561343c0706400242034060070350242822512800800d4003035002d0410101d500e07505004600802c1340c0e100000c030700f0451012055542d19450403411030b02008442082c02420a1a80a03003112015454480d804450046861500020984c03040c2c1c0424a4801c40010890106082040c4440e2081041014a40c4010f100003408082d050548807842c1c00c0707095101c042e004104050001e0140141c103000300040030365007404200203400000051529070001d02400030600454010040481d0050081c02e02131100031403120217242c9416500310311948950001c81e00103a1581d000100d0b180240700d41c50040d001c01c00b1140c24551140704243c00c513692600014441c6000d40c9880c0c04c0c80c1d07845510 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 761543291 1250 761542041 761542043
    0x10e0309030d0e06210423151b1c0c08010608131b0b0903150c1b0709020403060b190f090b0307080105160206070512040b0c090d0605070e041107 64
    0x860212443c0301800710b000752003001c080140f007034100c1c1780104440e611000264880c80c09642c0c064069000384102c0304203165120490a41907100c0b00c1010f44400c81200080d0b00038411a440c030041d0f500b806c245d451039400070b002401100c60300c00e0307424203040000d0144012029142c80e0002d07866051031000380100dd0040c0c010060308610310f46070400c01c801402210400d0404909106900740d441410307140c0d0394440c40c03085009009040b03c52092802c2c80410900691038401140c1c05c02c150341c40544441602400c10322114424100b000850588a2009101030f40c00f650000c00c014400340240128203044208070007400298400400c2842c80c40c2503840300b620354110000c6044900c40001a1600d10b03c2d8201800e0b6501c0d08050240d00c100c074000c81c101321490f1380c0980300d00340c0da98401a550741c044c0c1d0344030004d0300440341c000a00090038180c10380e51200c019800581808840c0c0045130820301910412107540da940c0d01408403558016260043c0004125000c0c48a11750354801c4007000e02551030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 761544541 1250 761543291 761543297
    0x30f050703090909060209030a0503041e0e060411130e1e060330270303180108040618031205060402090d1704030f0f02010e04020a0219050c03030703020708010e0309030d 75
    0x1380c6042080210b404945404c50001d00319120040c86090403034a90780309200c1c0030a045100c031003251450640d0410042101c0140c3d0214221380d0343c103c10311003c0d1440f42c244100c2c0801c10046280302034000107400c800b9080d45084040c1a20b001e1a440b41c2201d5816001600400702008101040d44c001075840d44607082c4138201106d0f42541c8518228000505400b200c5091011401f0000b01010f0b0340d083c8240e1141540da00f280c113a030b0b1400e141d100e00c100c0440399406c8030603801c03004182d405020016001480344c200080e0124130b0220424108100350750807800a48940104c8140303040600600d47c0001044a04510f00444440020040074410600422080940c1580015903444d4402c1d200215044a01e480c450119841c10007503c07280130404070302082c005070102c04141894401c4ea07440312860703002030080c910b052003810103d911185c3c0c00c81d02da2080140180c9651001e00180c010715200390002c10403e42010b02c1c2900f542d820031011055980b0600c01510681c2d0000b50343c200d8000a41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 761545791 1250 761544541 761544551
    0x8191119051005041e260706060b091014070606080f0609011a121006080a0b0c03100509100b0a180803031308222301090302090114010314010e0103030f0507030909 72
    0x8031300242802c1446141c024200e010241b00056603842c80000c0c94802d02c160720810445031175012031402402000030564024803980f04100e0f10b140110110407003521500c0080d400d024075542ca0b0804d85440d030300004a150010541000565002c02c1200c1c0c00224210081c005403205403141c0a2ba01d840d01089842030030114000740c207090781400746110140d80c00409101c807544130000c540d81c5080f0003070111154458040000c0b100400401980c1c0a030600da040d1000d52031400041100b06034015241c0401c1c00c03120070f00066a401e80900511441041d9280c011200d10410f44c50620409241c0c00548590420020002e02c03441c85a0540049070740b00140c0da480310000c102c2d5080d600d48880780b002d55903c58000c0841d1407005100d40d80b00d4981e010700c06511461107800111152501840020341100f824001801444010701d10020240341c18940010216007041420b03251607020703072210740e041548030014814035500005040c480d00d55030070098a04025990b000300020308034031500c11525a90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 761547041 1250 761545791 761545793
    0x3201c0606121a010e0f07030f02130303080108010f1109060a180b0409050924060105072a0e040b04030e011413081908191119051005041e 61
    0x95211101401ca04810040b0440c11032424161030f508046504800d4443c400c00003500c4110600c0c002d100e10038024076140030f81c0390030400340c1c058500f00480c617152a07000c0c444120b175410300c017030244002c41c000d0365402c2032945052540c030b00311036201d051030040034102242e041d1154824802c0f0384541006940b6a07940d900030b410201d40300c0004150484803440b251f0800260184650003400c20ba5000c403c042001d52640c01d03403195500000c1c106008444884400381020b403540c07046483e03000c401810100e1419010741c1d0340d50141d6412282d2003542c4000400f02c0d2a022000d125200d01518600b41016114141500c80d004a8440204020708102c042c42601d41e02d41d01c20544500c0c24000c003d40c0e80d49841980180d40b04510b01402080a00c1c4240100380641c0d041c0d590180342c88030b03040b800b12490164166418045a1240740401c0700703014000184940144081184015a10007108800b040c41010324085003001c104074038614800b400c01e000d0101180d000764202203110f5102c0320110851103d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 761548291 1250 761547041 761547053
    0x120a020403080406020102030907140306061519050706060608130b0a090b0405010b091005010c03230a0c050c04050105330c1501080604121b08070303020403201c 71
    0x581e070801410110040350000e1a1601500654003400400c3c056626590700d460a14000900c00304406500d5401000030400703500b800030840e00c8030074021a40900c0d001c40308100ca1001d181e030349400800900001003106c10b20030320344a0400a029240740054642c2002000900351110320000a45001043c03004252070780304c0e0703034044920544d01524102c02da18080c10024002d01034800c0050140086200055007076010b400c200d4152a01610f0302c02404030b50340c13000c5500d0f0401c0410600e02507200c480340c0c1c0c21071401d5005000308030b295603035680da8500039141082c10f100010074594000c5040000504c240d6440760303004448003101d241d080c20030003010780703140d0700c42007000c281207040010000310a02d00007408903010212007580c003001c060301d99a4210860b540c6038122409800d1040d0314a0a034001d510800e09001c00c0440310614201d620269141c58000c0d0303004030401c6020a500107030800401000301c102c0c8000c03002c40803031400d201c585c0a0204900840b007000500300145050240d03820452 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 761549541 1250 761548291 761548297
    0xc0a030522030602040806090a03050a0c05010b1c0c08070f0302040c03020715150e060a031407090e01061401050702030d03050a020c0f03031b03011202093d05010c08120a02 76
    0x6220300310503002a0b81e034100b180c025030050141401500031100001e454101c0007a078007950703507856a1018500440101c1c01c55100c403403c2011200c954a80000401c207640703144103c01c3c46420405003010154503868000b42c040083c1c1e000118681004402304420000c0041e4030088030740584c2c01003201d01c0060340c100c000f4414a03500400c3c02e001282c04200103a0389a000c940540314240c4038441c0a03803500401e03500044103c805661000310b040c01072001035001541018031040500403034000300d07161040e0710261003a80e50002d003aa9503400c1c003004000030a0b401010b8441086c205070780b810040fa00480e454191800c01034007031507100c102089003007130164111003481d855071055230080a05466819180c0c0e2003550b205001c00c103c081001c0038074a804007102c0c100c0c3c801241d41a0500c0e0a42e00340841803000030703c03034489882e00701c070100841e1407401d04056600003419081402208141950010058250002e030304122864191100203100c400c219502000c0c0742103140d0f00380d41c2d41140c8801901c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 761550791 1250 761549541 761549587
    0x80a09080a030f1d0d060c0302070807150605100807140c120c0705011803060c0210050a0b010212190e120a080d05010506070b070806010c02040e070f0b0c0a0305 71
    0xc81061500c0082c5a4096031420801c40c0503034464026690030b0100d03c0d101d03410508416800000050000c00294542d801280208180c2c280941802101c0c3c9803505c061b00b002c5010786101c0200380e80205400007c1c420300000e0813089620101550814a00402c2c038100106a0001d21003203040307100b0103101400c21f484103946000c04883c11030604442e501c6d0540c01c0a403055080744a810300115040d8040c5001001c400100102420304a295460703000240c4894245c190550141407503003e5400d03044c1c001d5a1065880200c01f2074441e203c60002884c1003803280351071100010a110707091143c4440107403240c01074054503101c2d1071a0b4030072001074400781ca05d0009a54a1061520030b4007001106030117080031042e1840104150303070703907141171191030300c220b0b9001024881541c0010750003038000c3c0c003110340007031040c580450202d40c4d80c0c1c0882c080381d41410106040e0790241c0710410901070078007261000703092b40322100c0e400c1009180d0855620741c001e840040034440046401480b5841c2032f5420301c021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 761552041 1250 761550791 761550793
    0xf0609100f08030c071203051608160c150c030e01030c02160e0702060c07020d1e0b0f011502030c071401050c06070903030e0102010b09070305090f010f05090c0d050604080a0908 78
    0x1036a521065940d8944c44880c00001c140207850300004e80b203000d0600c983c01a60140c035004d00e00150011829562442c5000864142500344118000740101c4490802124410f4083e000c042d424031410b0058100e50160003000c01407806000b0f1300180e4802d00c182d04c171340800c0c01c002ca200d5804000a07401c04c045031a10115000c425800001c80303161a42040d03004400355000d88000e0f495200320b0940741c0c8030b80c9001a4102c070314580d80c04001402c2d9208602c110341e41c540d02a0b90072105944103440382c401070780e01d00340c415003100042c002102120800000c0c0803003800150700d041e43c100031032a12980d41e413180c800400b4003102c59000301e0740602c044550b504518030030b480461506010250a80a0343d000c02d40c001040100c01040c5940144100a803080d001402203407555180c202c220081c0000800700340d040c0c000d4a500300c05400c4240902024a0508072000c500d0f803a00400b000d24218009100510500113050500b01007400804c0164000d9084101c8556516182070b05880740000d5a10403559 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761553291 1250 761552041 761552069
    0x3121503020d1a010e010b0a050310030f05010606020c06092b0c1d0610021f110703030504020f0301181203090c080309030106091e09060b0a06090801140f060910 71
    0x2003210406050f05103011204090801da40c8038095150300e0182401044031404081005004682c054005103503c40d40f50b000c0107008549075913545010228001049807a40e460314400c0c040e40d5014002d02500100660f8002d0801e02c1d214005545c00b100d000045150040011340380c1990f4806880300754070a50030100130f00c05290f441e114201200b41041441155080d81400b02d8424584030b03440070500ca6407035004012041090b110502c0e001640340380911450740c0d403204282000180009045528029100000d41d8a1310740103100b4000c0442c444c00d03100e40d1400c07002c076412103032004d000ea0b501508841162500134550506400605004070040c0c0004118400050303009030020080c40380005c142c000744a09640ca420900540740305040e204080d80c01d14002440b1040c843e0700101c2828004c00010401d0441c1c0310114010004d941c100ba400103034481c100f0b0017503403024040d080c00d00b0354028070103002e0310b0004583c580000000c0c1402d4800d12120002c680f00110314a5a6000340ca40ca5000c002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 761554541 1250 761553291 761553293
    0x1b010f020c030a022404140c0307060512060f0306040f0c0b040e06120609190302010f2a050307020304050103020f1b0d020115030c05040905030c0a060603031b03121503020d 76
    0xe40c82c3c00024041c40184100d0301c10400c90002d80d441c1c00314040e0780103041c00003500c440d034401c09040d140c000c040704140f04a8140c5080760b43d0400c0b16100a12103910350729030340d010740d900d0000b0104005200c107000c0d102c0503405044a0b14001031030396009401c1000c48030180310510341480150903540c0403810760100810f020610701d44140000f8001c1000f00c0b0a4007105040a000c0350701d0b041c044800015540140c50810b040500425601e5107003031081c8000120070310503003001000c46440915906801c2d0358004031008422102d0b070001804601f500708681103207010140290f817441207000344c03030406070046610714030318510205032034503491500e261788001c0f40300741c0b48030380d45280c44550f030001982044444d0504450641e041c0003545d07000007079448a20705210034072000d00f070b504800f03c40ca44020042e5840120081c40341108041c03044401040c0b11380b031810010103140d104644050704030101c81c80700b000260860150b0a45c1d040c04103010444011640107480d0014490b0300180d0400c1e9a40c032008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 761555791 1250 761554541 761554543
    0x62706030605090f100b0c0c040e24190b150a02010f0b10050d1109030607022104050d030e010e0d060f050112020303070602300907050102030f1b010f020c 68
    0x81c0540d1010b4440c00c1c21070f070b24000400d01103107060b039000b8041889041c043c81888060b00c02001c1c0c0500400840310070041c0300010900b1913881ca00700242c207400034044003075160410301880704110708402c0c8480f41030030104403103401070303e8004151032042c0c1c0e10700d09503015445036034000901c81c82c40c0300d01d030781c43d00445840a8042c05003102514202d41c0340202600903440c02050712980110140d41e0182028040108a030080050030b0340e01d5091501804440e07040c1e034003000101e1082117244d001d0b0a51001e1260780c07081540c8503050200d50380906100501c401e40b04d24180c002d0342034041c9000b00b81c070003440c00103941080b14180c0645d0401201144a014411150450001d4021200d02040340380c2e80c50780207685200500c1c42c0298150400c01590022403516001380941900241d201a035003402c050519400701610700b09c1c088005242420440b1341c860906c01c1c180100b001b80007031458012001c0c0200b10910501001c08403180d09800c0c1c59030820000d40c850f4100c001f0681003195103a041201329 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 761557041 1250 761555791 761555801
    0x90f15130e06091204090207060914031210150e01170c18150306011404180f0b0f091801020c010509070305191106030406140c0405040c0908060106270603 68
    0x5101c191140601182e80c060f00040c2404031101c0364035529080500b8804400043e600c10003003954650303221f980b00c2d00814140c3c64000100c8880f100111f03030390030019480303c080901c02030102c51099806602084680d9840300310402c52566440c200031051016801680e59900440d002d60807004d042042145071900c600080600c03829540c61074203072904803410003a02d00d800d490a42c116040601c0811502c2d4024809a040204026241c6003429260390443d05a151290800001280c031a010214825171910500c0191901941c0e100103813480000469101c9501a1200d045814000b40700380c40c4002c01e6040e164011821382c005d2045e4104240b0480e6140d0036400305035a64000c881d4890a2801c084505600741c0341e000d4080000d03008404200800e5070030050080c0d445540302d0030103100484070000810310a42e5400c019075165420072050008403440c2c0c2d1301100034000c0411050000904c00128581102c1b007074038208c00c40e40340c140c400c1800714401130741072100d840c0380a0300400c0c9640c02d80c01c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 761558291 1250 761557041 761557061
    0xd08090708010e030d0b010c050a0605040b0c0304052d01050112020907050a0c1101110d03140702010b0609040b0a0506210c040612050703180b060a080606090f1513 72
    0x4540c11107840d540c440b8201d42c1203034034545107684104221080413010b5006110300c408141005040d1611940306c60381001d04200084980680c1c0b9001c100800c00040607003600000200b14050a614045c2d503955564040d600320500101803002d5103403c4034200a454980e1600c000c00240070550b034a80e8040302c51058000100e00c55907002000803d000d2080c02610750440381c0d5950030102c2d6000d5121400c8509204284030b0400020382c011280d0b000b01017195410314002550002038a400040149281400c00791040d000c590410000c2c1840d9901d0750113580c7d801000f140d0000e40e41014000017048070b50b195000b240c20a0010400541c0322460a49003a4008601c4180b0080c681e203494001d00340c2e00c200d014030b0010030038901c01d52100f0280c41c0d0180e0f0744407442c0c0c00d00140b0003211880781010fa001086040742c51180c0d080030071030181040c0b0300b10700c02840603100134045070a1140029400b02d900400d003080d80e60915001502884900c072428603201d0000e02221660290303060701c00702800665403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 761559541 1250 761558291 761558293
    0x501050f01030b01080106050306061308030d0c050316050306030a060e0303040330020d1e09051009260d050f160207051f0903050f060f100f050d02120d0809 69
    0xc00300e40c8550082c0076809010380141d40e03901d01a820318030b09803856040030b080305401400510032055001042000d0501400b00d040c001c5407294003202489050742c1c0703940200d00c10485c0c28401d02c5022091140f44218100f507500b083c0c1d13122368802d00031034030744004180058645806d1042003c041800070000307500403402642d0300c51120540408a121401da55103c103016144000340a1000c00110350140207108140c0c1008602418051040c140b601108403400203483d83e00e079030700002c0000070000720f0380c24401804240441c041c29143c0c14044003104945007013290100c0c004c0200d0040441c102c0b1100081d1400410603800e0007007816400d80700c00c80d1703d0303044c2c44840e120b00141140006001021103200911035000101007144000c2c1e010460100c503400d00c1080040030000031424400000964603c0c0018041440c0c07010030240804005005c005a12285c088180811100302d50f07000306079003040c0c845140c007107008d1001c40d415449005507031465000382c1c80c41c20481a4020300281c05880c10300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 761560791 1250 761559541 761559559
    0x1008210f0a0e01080c1206010c0206070b0106180f120201030222060c021003090f110d02130f0c091a0306150c060921091c05032b0b0609091018050105 66
    0x104500b061480fa80d40040c0307011403003800041c1f030740d07200d4140b4482c040d1000d0701907030400d6003942c1c401d0b406120a81007032000c1062130120305458203404030090000d05205156584262901c1245442592038940180c101a0006002140d2821803580104040c80c84003201240a03a100f000030142000500c0c200d102e91010b01c40b2103c0d00344640104003c103504010783c0c0003c039203d80e0700d445d8001c12118500d5000080d600e402800f5965160b481c0d511140c15101c01b04010116220344403c490800c0600c1041c008a000e081c007180008000207038000c000c04038202c2e81e9844440015444407800f840105055000103180088070101140e424014522801128a2042039400700b03c10001c9000842c607105005208203a203078a4401500d2601004011a403111100240c40d41815075010580620344030515800c07405400d5100001c160581d5900b04042001e0509000022454454410307114030030f010240114620b050030490070001031541ca03c010658103440641c03440238000922840388039103d80 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 761562041 1250 761560791 761560801
    0x1834050402070201020c011206080d03021315020a0f060b091e150607022407082701050301170c120a0302011103060607080c010207080703080f1008210f0a0e0108 71
    0x5000b41c4855507416001791489142c0c40c0c004646820040c8044d60545440305000101190207000310b10306503000d0396015075107000400d800c2c0b51003c101d0f80400c440e420b0742c560703d20711158007043c4202c010340c1c07155089a50100d10b04044018101c0300b0000f560141010301484409400c4822305018081c01d01e02880055849030441034195980d4a400703904003404121100041c5030490161006603804810301e881c41401142888840e00300510032100d01d070000036402800300d401180c1c41d00d8400b41c1da02091280b003080000919501061082d5041280c0020b002a1000300602c83c106048002901040500245801c0660360712510b10064001d5440c0007417640300c40441404076840f40324007902c030728036084d101d41e942c141d180d0002208084955090103100b00140d4800020300b0708a02a5544240600f440c0c0e0840c1045280070b0911780c200704588400304074030b00010540e290070303101548500c0480c1d003c61404c06064400e10b40b0380b0018600c0001d50000890304400c801c0d40322017080c1d803012960356030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 761563291 1250 761562041 761562049
    0x13171501050102061504020d0204060503092a010507050a120f030612021e03070b0304050319500c0c0612010b0d1b090504050907030b183405 62
    0x1e0240d079005800080000e000307000a45203100180c0d401800040c9000c40f44450034040340c20503084400002c000100740702c90304504102241c0c0303c2c41000310401c030750480c0701403d0490750a4a00e07254184100481c03402e09014041c401942c02c1500000300101c0c0050841000b0144109084c2003c0807d01c1d044010440da0303a044482c2c10a02d501802e00b030521102c64240300c0d09a0480c8603181d5061040e0b010118408802c200a903009500ca10001c549541c140d07007a107000c003048955407200704909040c103940741d00c004c440383c1e51441e190751914680140f40340f4202125040f000307156000c014840c08149900302c0144005041c55107551050768181c03400c00302000050311612100c840008220307401440f9040e0b0710801003c001c04041c50004000340c140700c440341e25000140c0628045182c80b6802c02150800d070040f60f0f031000080026001903811951810402000a40110500704d0801c1c045407070b003172040000e484041c15601100c4181510b15060007032a410380440600b2416011500040d5800c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 761564541 1250 761563291 761563333
    0xb0f0a06060504050607111c17072105091002060405070509010302010503070f030f0e01020306090a060b12220506090c0a06050f03091231060c1401021317 68
    0x30550b0307030076140929000410006401404080d18131002c41302c50918507a494001d88041900c0082601813111401e0809a8080d04181071041c015001006460001000e41c00b003e6140207420003204110110b4003022611400b800c400c0740e401c520360114002e03809400141e007601c03440c0301318200d4209544400a02040c02001c0c44003e001c103c0a1001c03410f050f0280c00d41c041506c0302e82ca800035800100d645081e081d1420000000e400f41d5002003404454200001d0541d8420075052003484440d01d4045690349a10031a614070708280302000200d1143c007010680ca20100590907190900c440403424032a849440c240d070550800d2040c451070031420f09102c5500001c4070b6090b00c0d19814082d00344003840160380020804082405110420715090400f800a840c0e1041281105000c0d1420b0361000305440444181c50140c00745080020007410340d1140420080c0e96001040d04003038182d1050184c003a000d0340036200340131810603a000c985800e51100700c100304030904045518583c01c05246640e804 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 761565791 1250 761564541 761564549
    0x1060e10081b010c080d1104030c031b0302030c04020d02120108010615020c0901230d110307060507080a230d0902090f100311030f07080f012301050411070602070b0f0a06 75
    0xd944c8921003001300d40140060b040c5500030402c0860302e13294001d405043da602c41e4004803050700c1242c4040c0107101d0035030390082c03081b01d100c1d0002c0b03000707800c40d00040d540e01c1c0003104461099030000b452560314403050301503640600c170b4021900d1071540c40c0d00d0481c0c06000c1c0c40c024502c03013076598502d400c4100d100040c1e40700540310141c507a50703190b424004000070209801c0e0320950020400b0711203545039180e02001400a81c000c4c207840383c142482c20101400c18146034099000c004090081d800030458540407501d40010ba81440c080c032800203d103507141c1d80c5000c410920070b008007045482001c1c150b9041800c030a442207680d8003182d030305c01e20788000c0000c0c190342c600c500e942c1d603620600c000f4001d00e10320b040c0403030000c4c1200c440549070240b06142c20b0307071a041240c087d04103c000f82c0e1500c009000d40b5604520600c400c3c0307083e8003600988007001e03105110b01840349480b03044007441c03080004112007400344c0290043d960b54401741880b20f8941c00070f50752002044020700001d6110412403180320156 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 761567041 1250 761565791 761565797
    0x110c0c0f0a0f0905100e0a0504030816120e0a12020a1209031104050901020c070f1502011b051e070807200a2714040c0801150909030201060e10081b01 66
    0xc0b40c2400c1c000030041c040105101e40ba410744900225050a11081c445e00c034000522000c81e06182605e0020402d00d4090850002010060034511101307030407404600c00d0402c0210002000c2d84031f210800e141104d8001301921951810700c0080708158082030030207131140904400c4c150800c803030314200c411240078880a40010200c20310700d80b0920b0150452134200c054080007504050317003070325400d0501d1902d030b00491100c13481c644100404075082005003a841c1c0d06000800c00005070403100d03000c0d4100fa6a9500c100b110014404001d80d5011600c01d413550301200d4800e0b00c50707100d450040c1d5580e000f001d0659100d480300f4801e400c5088071810040d01007001805621480c0c0c030340461450701e1303040c80031280c0d9481c0703d02c0310750640d0a840d8420500102c58802900a581c1810304103000b440354a500211076990402e08008185040b000491782114100d80e400142481c070742c10101e0062580342c000d80c0a1100d01024480300891030304a0741c0c140d400040a44035001541034091140d62148400c00d404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 761568291 1250 761567041 761567069
    0x1a2703031308030601020705090a09060609050c2d1903051305120d0207120522060e010509030109120206070e030105011406031909031d1c080c01110c0c0f0a 69
    0x1c2d03015010703581090b01070041b10070b690745a1000506401007200e030604429901d450b403006205890081da001070407550001c014034200554107044034481c2c800544c2c11050076001401e282420620000b07100d041e65400f02d03440c0d460070001c400e00e8480888403000000d041c0004122008038610000d214940c0c460010106019004200c0b007032500428900d4417019402c0c400d480100f800305141c0080108142d44d01541e804000c1e64032401611087c445807440484c40c601480712a8012141943e00c0c1e03070900300a51200d40e85800a400360041c198014082c1041c07603648812281c00043c500d0140450340c840010b040d00c25000c0c182200c1d001d20945200c02e8025205028038100b0700011500700303c00c1403604c05500f4001000c0e000f903d0700075104070300081d156807035450505078816840809110440e00260075425250b50003000901404000d00b61090010b201c41000c1d800b54071003001d030040349214075140c0c0c10098105465500c218005401000d82094401c0a4501503200005940e505003004607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 761569541 1250 761568291 761568293
    0x3130621050a0f06080303070201050c07080906030411030109060519020f03062403010b070c050907050d0510090c0c05060705040f090b012a110301020901020d03091a27030313 77
    0x3000e444040e002c80e5001e0f0780c9010042d0204075501804018210309402107940c0e08201c0c0009003101c20083c0028124181482980001030311b81003101c400080c100c9010780c4a840720306182c400e4000454905500d50701e1b01c0302000c10804c0c55000248100d1790103040498004208102c41d059104100c011600c840b810000907585282c80d0349a8204031f039420b150b1802e9040a00241c600d07540c000c0c1c024104401000c00c01904000c211003040b40900f03029920250103062220001d00a40905500205002c1c2c9031000920307448082c09200b03004003101c00c0203108009c400d0034058030280fa500000c0c2c03003c0c0611310000740214081da088030100d03002034001d030089500d083c801030010607104000b64100320f071541c3c8040762000c100413071122020141e1280583c400700b51a0016800140440f90b43c040c1e401404454400d030380101c0c2c17880421340f844c140401e14074418904400c2606040c0e4021401485c1c040901c403403110b01c20140c0001c5902110b140c2c01d10114108015524042142c01c80c18030030790036640e94 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 761570791 1250 761569541 761569607
    0xc09030204050c120f100902120604022b0c11060403091a0408030f18040504020127030b0108010209090a110304030c061b0201020a09050f0a030204090201110f031306 73
    0xf80d1025560b440141000620742846905282c01d0b510313261840c070b011043c40341602c40c051154000f4414540210b10b04003948140115150000700441d11499001c50321381c03803000c0c050004407406a003d03400000b245000d00041001861039041c0b240003c1c0003401070007460340c000a00070380542d800d5117411043d40e05c0c002c0443c2c501614900300308000d40c000d200006018500f040501074800300d884013182c036107280002c000c0d0000b500e107a02900c2181030009020143c0d1304080c11141d031680c03000540c400034540994444040c0400c1d417001f440c08402000010f40e0710381c10740c06084491022110200c8035195598500203407504000c1400454004002140000b80202050400c1702c1c41044003046084000e0741440d25205c00b0031909c000340c0d40000749281e54942c824148000b40a0450b04980b011600501103a0780700200d000007400b8a5407000741c0c03011341e07014290000462040000715015042c040b00000d4030303500007480980c5030204440c1c000c644113009840a00c0c803115450b160a241100300c0b8012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 761572041 1250 761570791 761570801
    0x2010c09082107080a090302090604020a090e0636010f030507050f010905030d0c020118080a020d06110d0f0501050d08030f0703060f170d1107120507120f0b0a0c09030204 75
    0x1044203100300f0800c04001410140c05004a60543d460b081c1c00b852550051003074a10006006510440c0304015880d0715a40082e444025240e01032241c14a65031400e0120300d20300d8007440005682000c088050380803007039a0303408000d85c62110703041c640703c0d0741c0e182034481c07644445000c01807241d00b1848061259007449409202080c00c1458401c5140c1d95900200f130500707a142074907200146554181c1400e6582008141c1d0248070302485910540c0d2400a0260b2504107490b402442110018075940910a1941020038010448191140d0f50803a014413800103103007951a040c840d60410000040d90715214040021071500605001d203150f0700c009000c0f8078400d000340702409169565601080084c881c1100201801e0080e01c42244d20081e041210b10709404680883c040104c62502e58411001c049442c0c0111000e6a104180002c07451404608005641d0001d1540c094900d4810041c84842c2c4122103106020300702e504620b80b00c0c0516942582e50350307071310500450300790b04081005050a91003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 761573291 1250 761572041 761572093
    0x9010b0a0905090a0b010e010203042d08030f040f060f0503180f1f061703160323041401032703020304030b07090812130b16050d03060602010c0908 65
    0x80c0ca0160302e840024050850699180340c40b181d80703c002018550704100400481c05090004600701490080c00054004140070413005000c8480c0c14400e80203035814403d405824031406590b103508580c180060660840e1141c180940d11050000a100c0d0003850030442d01c1000f9030b0341d103145648110000d041c040c180f460301c003014441c1c1c024828247e0b10602900c9040290040c0c80d04074888680070385170640d2119080209000c1084c80f0798146100c0010880760313083d003101c2000400c0ccd00242801c2c0c590741d1006101802d02c64401c680701002e10403000041c0140c0f078450080f1480142c0c01c8004400303c03851220041545d0700100050351a00c00302c11990f9804c0340c8648126441d05450340d40b8801248010707a103502c00300e400044280131007481441310880001007441c4460429849150340001e2000a01c100c0d8a600000030b121503000092402c4840640e4000c011514145040880100285203e10070103005510380000c040c41c40d840f509040e400c4806a90003001120303d0307200c82101603500c40300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 761574541 1250 761573291 761573297
    0xc03070203130609050f1c0201080426030109230721060311030606151602040b10080907050f010c110d0b040c05180403020a0308091608010f0609090209010b0a 70
    0x200030141c00050440b4000545070710b030344051906240405010600c0740e00f40c4094403880c00308030f1050b5880d82881e025010a502440d1940700e98a50381082400c030150a814144c003080030b2070110320008040da000318101e03240104100409090b12138031100010501c04249140c0301903c000c00c04a0f0300c81c6103000011030346441e0700d04038071000540c000100c4d03005900440390303084007a40409640c502030011944c0704000f1703030750782c0d11540343c10300990990703c20b04c01e114185060f00042c42c0f0940d2a9a406203411140107484506802852172002d040c41d101280c0550503841031810105150804590100c2400c506031030384000200e0b240d445c1c0030f40c000401d03011a0403811689600012810103031016000703d005002d10140e03a820a814008085500000704007039800003400d00000950000c1c0c1e801e04950145450b15064a9005450b41418100e502c04c00e02c7c0d040300c0742c0c041294001984070041c03007511a0820007015aa8207a5801a038000e44400b0750b0005010004000e00040d035401882c407008286 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 761575791 1250 761574541 761574547
    0x2041409090f102004080703080d110d05041101020c0d08031f0f0305060c130302100e030102030a020c0705030d0c031209020414150904080f0a030207050d020c031002040e0c03070203 80
    0x42c04a2070040f1500b41d000109032140740c1500000b003a00c00c905880540345400510301424a8061a40d40352584402400712000180c4c40c45a10b00070351222048407a0360100c16074175921806441e0290800751317800d0714503403000e039080380044d03000140960520f4005807203521144070075100c544140d003005018240b641080403502480c00590344014014041407103582d0481e50460800c20b103481c8000b0300500000f4010482c1d0410006140461411070b58101c3e49890580c0300b85904a4520383c8501059030103600104c00c0c00942c48268010307040341c6000c401202c2e0301c20340d03920816907142582041c0b00085007040d801d01001c20710a050400c0b19800c14100401e440c95158080f404540c0402a90031100800005114010740401c240d10801d00302103615040c0e0342055212500d0398490711040c03490b215000500012454065010b80320704030f800c00c0640700c1855240c0c4e4069111340328402c0d0180b2a00403820018903001750fa109440c02d6901e00860840d55607500c039003301403688040d040205610043c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 761577041 1250 761575791 761575813
    0x70f0608040b0a0608060402041a090c0408010b0604030b06010f020a0b13110102010b010e01050a0c080d0c090501020a0b071d1914030a02030a0b0606090d0b0610030204140909 77
    0x155114000a11840d6034805041c58030781861046000040c0c00910f103541030840801c245a00000c81035080368049900040620f0f40c2c80c542d00c440310046452036004a290f0042050030100e00c4082d00884058400038840045141c040000074411400010403680e101d00100d003441d4400c40a00001c0c0507d40103c5d10030100170b4682d6076020034102e6a140d20810303281c0005c1c0030407001c0744500e0882e034030030b0000380003140f16900064001620300915038104400803812929103441085040e80841d0040e280303d5a0341044522800030f082d100d10840003103100010002141d500c0019020707081a0020400c211a440d4028101c8907145441d00003c0d524815209509280c0c1c1e071700701c400041d01502c0500c13106151034800d5440c10318201ca2112480f0380c110810071009031700d01151102039a5404036110f5403e80d14080041c505006204805d601304140300e41070f804109403031000c14002e030000c841011660355155800c405904c198001d60740110491021202a41000d11020303030407140c0c40c0d0980c1e02100c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 761578291 1250 761577041 761577059
    0x6090b070c0b1b0c040e1009030921020f22022805070507060f142808011806120f05010902030105130c0b0403030e120c131e050f010b0a0207 62
    0x75012080d100402c02481e02d2002000308a04c1c07240e89820365051150010003071a403502d50640e503550f200c50a864071408800c0610071040503004d03062810440c3c04903070000c0c84212200f4081d040490141509032004143d41c074105581da21400001d4034641100305481c010640030750054490340b01030014a108603c01481400810b12001c2e215913030301031701e5400a0402501d4080d1a41c042003d101019106205941c0d101d8030001c001ca1801640540c0c40000142c90508160040c0f21807078510f6003080c1c140038150340701d8480c504072652040044038101e042d00c501e104540d6148540e100d4141401d0790100045c01c1080d00340d21582c05a000010000c9064000c2030944201712805901011015035030010000c040f07001101600c02100d960381000d0450f42d0140c86c10005890607403040103440400620000101f00526049201400104039030000e4000c42011306201035421030610802581950004402e100701842503881d0344c244840360740703007412800c09503003e00325200031401400030204000ca4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 761579541 1250 761578291 761578297
    0x6170d120f02180f010801080d110a0b040c060207060e1804050a0b27060f040f0f0501022b020a0c110402040e010e0603010b0d1a181609060f06090b070c0b 68
    0x1004441c80540080f69040245403614140c6540c10f1017850b10040c0600342001500802c102c08505248410050681c9424507080780d280006241100d010704000412117240501000c4480075004c490505c1d450385000d0341c00300d029504054000c00b4001000001012400c00c02d138205000d6070603503001840d0398540301440141181c000d40308143c42c00c1386501825016911080d0b14035442e02402c2913003400c80340320004500207803000d001c2e410054241418001246010700b040d40c2e03c00e00843d920900b4902c1d5900307030a44c041d503000321a8a000c6903040d0000c032034000c81e171a201c8030f0ba6600d0046001da5032181e150f50b00b1200740729000f0354240004a100301068080d203010f0b00c603030f91914156140401c109401d507244244024040c03569a812480068140c801d15020308600c0700100b000c0356075990b4110085524403c0c24030f03403031040c2c000c44242060403a40820039a46032800c103200711394407060440c909003c1441400b0010f5008001005442100c0000e0311400d80704a8840e19419500c1d0580c030502d070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 761580791 1250 761579541 761579557
    0x60103050a0e0102191409220e100b0411030708041b0f030804092004270c170603010509030a050c0a08030c0307090801140c0901031407110106170d120f02 68
    0x607040041031021900b0550394150451860f00d464908140040423440040c0d2200030003100700a0b0504842009400750002d8040e000d406042340d0084107040e0f00c410281241224280c080c614010740070755040da0340b40840740714a8580d2928051911190350301002d886420607001e400031480b50000c242d00c07002c41c954400550240f14819180d50501c030601c401c07240d584c0152442231402d1100c0c907002840d03450507102180c1101e214280c550a0010000004046110350030b8010361508400210307541c0c00011080d900c43c0011410902075951400740f60172120103031410b03044c50b4004d2040070000d0344500000d206005000080d98410099640e989000c0e4005807014026050084100b003c0641e1144980b001415218020320078006081900382da02c1c1800703807048408507800100040181d001e81c000c1c480b2044586299042d5203032104d401031400b00e080f8120b94203542000c000282950341c0d002a20081a080f1014007180c4403034540c140c2c0c00040d50110b080c010b40e101d2400c2158544a40701402c0d41c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 761582041 1250 761580791 761580817
    0x30703020a09050906010c0f030e0406240212180a0e0a050601081003030822021206090c0301140c13030b01060804140a0b1b04030618020a0608040b060103050a0e0102 73
    0x41e18264005021910356400c080e00814001040004980e407100c111689a038001c10502107100590804440e00c00200c03010f40d42050911100090680519480d011192207a5030041d442c40d10394041281c8400f5080b0038500504014041110361a601036512402a04006c000d104043e554541d58003880130701311307940700107266110308015003940c120146c01d92041090741d4a4808a045503005846490090300e500700900020740c42c2c200e1f51035001c06409000b90010440c12400c0c0307221482d80c1c0d8a81044480000d0342c000c83c0700b801c5003030605024a16002100c0b0409100c075070746050f1540300a0308203440c0b89500b4108410f0010102d8000c0801601803c0a9550a0303d24641703801d01c2601380c120200d81c41d4159021250640c0401d21581c0c074507800c10300014a070021001c1d00440041d4501071a000904418600700d65081088542e2248000d503510a40f222810a5940d480580302044110340c0548101443c0380003a80b25031003a03201c0c0303a01030100e440018035014510241070072138101e81001864 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 761583291 1250 761582041 761582047
    0x9020c010e101b1107060f051605070510090e0109091a07020a1205040e07030c051308070906050316150201021e0913061a07020f030307030909050c04050d030e031203070302 76
    0x2143d400c081408040405034108007500500c0d42d5206540e0b07031300030f1185c142004030340300703c101035984548100c40c02c100c01c1c40e29181450703449040071502c8012601c1864481d69843c002c9204542c0110143c4003200c05d240c07041e04d86a03280235003020185c06440411215030029160249140d0380030311031580943d020382c0c0100b00c040b103a032030002a86850300401c10207014052008105011a0754040380d40050070b440c000c0303004a841503040e1080d0041d040b0000c0c14400c01500810003100015040003103500c00c2d40c051214035134900a00d6140c10002c8080045071544800500c070301244406103d8088549200043c0303011400030300149a0b1601d600500402a00007507501414502042e1840012580c0c5000b080124a041e1034129440c48203403110181c03031000309081041d541e03624151000b00c100501a6581c81141d8038005118080700e00590400a1801300410b410100c100c044d82c040d182d01601c22420b803085a2426502c0b40d01006140394188034061042100403107000245000305a00d0f1005a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 761584541 1250 761583291 761583311
    0x206090402210105010e0609101e030c02060a0e070501050a110303151806030c10140c1615021f2310080606031509161206050c0304030909020c010e10 66
    0x78900b48103a00040c10820b084000d20744a0f034622045405085040303403071200d0740e000f440041e0b4240d000e54202505451202e108070004640641101a8500c025425101240e0703540340d00400b110344e002800c5400380e000c0c0206200c1540140000c0269410904200b040c00e400070b213200c1c0c91070b803049070000d00d03580c080c0507001e4503800c0035107042100c1c40f44101c02800d07a00d0300401007551000d000100511926944101c140601c6c01160b071004039900f0744d00031943c0d40c2c2c0900313412540c0300744020f08900001801040005c050500c9440544941034a07070142c494000380c50442e11003510061401d03e0704990b1358016000c141c61010080300900c000507000c01203868031b0070160b44560700035484245980c1065082041980d070114100c81c2909807120b000c81d007a00d5517044035140468092040300e80760890301c0081030250411540426461140da014840d5075201115407440f070105840c001d000c1203121809204e0b554894000e0001801840e0000400c60252964075140260230309100c0c040baaa0740f0405a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 761585791 1250 761584541 761584597
    0xa0f060e1201110703090b0c1c0c0206040306050702060c120c07021309050d12090515040819020606031c05070201212c0c060f0904110a2609030d090206090402 70
    0xc00400031f0303100040c2401c8040f62240e031103450706606041741764403141103203030003d02400c4042c0d40d150300a04441e44881c1c0b6440d001004100aa0750080584907200c001441104002c00700c803d0780f102100c40c640c5c0381d21240b140311400e07004000c0499000401c00c104d003400001034800c40d0f0b5028050b0008040c1e10100b03c90103402c281c0c0c411230414107a0f007402c1c0d0550100303a002824a0b5803c0d0380703500c3c4124a40d26414151024014895a021000f41c61007101c4803055000400d50b0040c14100c0c1030700d90030f2108130700244110a40400b200c0205a01f440b0306405036000e6054140e0041020085401504005400008484540b0660f0424403c000c00000c400d1304140c0b01d0498000285004001d00181d00c400560980580c2c4400d10001500088503003182d1107580200e0115000c01d0421901c03a0040c400103040908041d01c0145070700070042d95400c500882d5800c407802002c0030b5000e10300d02a2011000c9001d0310407448181d81151040109800a407210b1004009036421040340c0900c80709881641 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 761587041 1250 761585791 761585807
    0x30f05030316030c1b0204140705030403141303121413030c0504020705060402120705040f1a0405071b060e06040606050901090203040218041109070e0307050a0f060e1201110703 78
    0x42da04240c5494144425560402d01c80340700244064840d02c040c9030b03a480000c02401c00d8990303046480044030103108106401c41c0285008910a03140d24090000c503201804260040c1ca2036042c101c08803500405c041590f04150a2a504071860030740b4564420903a0034641e58402c6503891040b00441d03004000b8012180a460040d141c1120306501e000301540350640d4a2a0150019104191008404014140c100a10001020040e00a001802e00241760f00c00038504000c5000441295441c0c081c25840c1c98403a00f4402c111544840002d6a0044940760000c9a225801c9820b81d55400c440c4034510f1080015620613803003020040ac419007041c0601c01402c0040e40714091043c0107000740001650707805400004031a40c121140903ea4440c180001e8041690000079002a0b030300090200d000c0d030029998042c8041179048400c06541c03801131040e12031181c0709a178900451803c2c107000700e91040b070010400ea44001c21072220007040d404450b0854129610206811038002108010107801c071031a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 761588291 1250 761587041 761587081
    0x3120f0201090c090506120106060203091e101209143f090f06030a05040210092312030c010f140402010f0f090b0c07090b060304020d030810030f050303 67
    0x7032016241680e03c800d42da0480703000d03010b4070580b5800080c03001e0300e600b640710201540c0d0000a00681d0f40d1074401a40f2a440350411600400c00c0d403c010b2051540c080c1000c890a001510202605400381c004480c1103d680002240341605c809802000c83d01100f00308001803905006084074451a0720600c005201c02001e840300c40502e00e0002e00d403c0482038281410302c5014650a988400c40c0001840f0741510980e4554410740c04010f214640a645d40018400d40c429107070481c881d150482c0030780d940c25240c403034400444a0141d69092840202145405000c4090040210b1040c403452907401c0d40c010109031a6141c0d9120301e1550f21901502030b0307400f0400c1030801d6004500f02034000920403600d03e4424401d200d843c00702e403010540b04001d010001e28950529544a0500c0f940003500c0c5d11651190900d280e007040141812032514100300c0740915802003808101d20b08175030302a9010040203000120800c80d8020000110300c1200d40c4400c5144504051952440c1280c12550413403c0c0284e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 761589541 1250 761588291 761588293
    0xf0b030f070e01171b1b010b010203180d0f050a030c0c0504150302090910060b0a1205010608010e090c03120c010e06060a140411070308010e131104050901140103120f02 74
    0x200c20340310f0740c1101400d0b18000041c16540c0d41c0340d07180f60410310b0182c0300d0360606a249000280006030362050300a803c0c5403125103002070001c501000c1c0126900d0007034184019928004e80c2d00c8018524051504e4250544103441c110400d0f64980c1341c4c00c1c20301d1000746045c0e0224091b031019404000b9518100409420100e8040204800e0304041034902540c5020090103a20107402040d2010804c0004060040c0311034024043c0320b44410240c60300d138005180f00380c0880c61043c1c0e0040c98a4580c010380d816900c0f1542c400e4110ba2a00840e05451f01c80501303010b440e4007440c8400d120a071000e01000c203910940280003640e42c4010144079085030500100200c0300d801440130300c29165940302c0c041040f00c0c07000c0310012002c0c8014000a0081039801d1200030f86038000521141099080005107040b02d007205150703141070f030320701415030340d52004041c0c02403e6485848015010389029446140c102c0780f19400040d590741c10054501d07002c20203810a80d241a0303001a089104c07130f8008050070603003107c4c2c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 761590791 1250 761589541 761589557
    0xb010501081006020d030c050d150603060b0405090c0912030d050117010c0e040b1c0609050c01020a082205041a0424030f020f10080601080109090b0615040f0b030f07 73
    0x207000170340300c1107003860340d008142d00d0302c1d100840340e40700740242c0d068006080b0040241d08941410724071503036018800c0c440030074104040040c2c0c05120f2800d40d0100d98001c4d0252450b60b03517900f41d105155216003003280e4000800340c0f114a0000041003d001c1c142039205c4002400c1d41450b82c40c1501505010101821b80c3c144030801071503690082e211591618240c5010621802c90000100349003441884501e00c2491400760343c4c2400b20300d40200da0418010815102400040e2004a803201030400c0050480c2c902040351608500c0c10a001c5104003080d001c6084010707403614005000e03a451300f80e510b00c00c5d80052000c0c202c2c0b403806104d9150344585103890159000300342103c402141d080c0c0c1c40007808955103000b1010070740d281c55010140c190b031b0081040d40707020248039000d0704c0664140c0f8140c0c005044030002140100311486007800f8030f90080c03000800c607905c4104000e00038540b2145208a90410700000982d10848190040a010907116060302e91410008900301e41d078004109c401001212 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 761592041 1250 761590791 761590799
    0x90d020127060b130e0c0a091527060306090209010501030c0e0603060402070f0b090f0c09010b0318011b080f04080715090206030103030c02031006060207150c0209040b0105010810 79
    0x803050341c030601c0d61142001c6100302c5002d0000d50701c4816640b01388a0b641c1009003000e0f420b40040366000f65003c0c00c49807184055190300d0103004880300001030310203210171220140288190004c5076a5900303011440c00c2c000c41c403001c042909503000c0c0d501c129901619604800708524012440c14007415081c40e080084002001e030091480c418143c0d022300800340000410810b85480e0101d6482681000403030410400600d07005c160b45030216008042801010007603c048d0401150024400300000c1032200d459091140d802840c6c0d10141c04d103182d50b903230110300d4080c1c41003e014004501148003280819610006c8002e46814402002c518501d448001000001a011016911410707081000300c80314220b0310440b0401444021006540080040000000c155214542544040c400e030240e814503c0a03420080581b1883d000d401d001d03800410f418048522200c0000050300e07100d00d080007412a0303580100d216403c0c159000d4500c400080010300041d600320001c20307000005c801200b560203140c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 761593291 1250 761592041 761592101
    0x22104060e030109060c1106010609031203020a03150905010f0b03010302130b130203040503040302042409051f1d220602070c030203150708060a0807031106070803090d0201 76
    0x5240910420720900765600030071034409521280486a202204000c07036800c829024008403066a0010303200d00c18000003080a9108000640841364041c0d298078900d42496401e80c080d40044d18603104050707503411000c0148d400300903400001e000b40074000a980d41000c81b103480700409900405007120040004000589948030a1009102001c200040d600c10403c001403441d04d1201c803060100f8008000e02081c00004002401180c2c030803181004103810070310a411120164046a202ca861002c00070419001a0340000c4d901c02030009007140c060194030003403801203001c0d820a80c090208541e01d400980c5500d61440d070080042041c5031006007001d500540c0c6446260f100604240c2c0201d0214108500d00d0307002130186238001c042d0340c112003c01d10b06c194901400c40784040011004400304406007425030102040d58001c40c094030070750f4110b480f680d4100b4110041c068202908100c50004074650300042c40c0201c5681c0041e2095143c0540000d0a4940c056660340000c045101c2403420461 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 761594541 1250 761593291 761593297
    0x120f0608150901110c0708010605010e1c02060903160f0501020312010b0c0c120d02010f0b0307050111030c0105070918021213020d0c08070603050a0e030f0c1911010221 74
    0x40000c007804140c2d0b410016902501030034484408480001c1410200d0807404100342d400d0b41c013094001c1000564450046030b200440c0104a03400401d0040f400d065008030140e540300d624005084c030b84c80d055030140070a240000000b11100a14110303003081c8005840d4101034801060300748011804c104004420052074401803040d5812514005401480804207000c68074104e0401014100f020302010a07850304c8812018000005510b481d0f461b245e82e00c524032892940820140003040c60310706060054420102c0c641480d20984414011000398060034050148955900da0b1042d0341e142c54000001c21641005101110341401480081c0c2007a2040100543c0615442800781a104c01c40c00030031522405400003502a544500c0c010402507000100c000031036140d170794100303c540d581110100841c1e4051900c00d400303070000c02c4070f242d2202d5070802074442d6404200582d64030415804080d41022a441da04035101c5900d41000031180da018401c8220507026181c0040084580f904003002500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 761595791 1250 761594541 761594563
    0x309060f041a040303020d0b220209191d090607050d0c051605030342130504151109010f050318010f021905070c030b0c0f0a120f0608 59
    0x182200d40040c0500902ca0625054461100c04440943c142401d00402035072058030340d02512420646c0000311824800180810410040220380c140000650702d80082c0d803141c21019808008000d28207041201d100051000300042568071890b50720303c0708034900311600200306c800d0a130048010015529001011951502c01404000480444403e0180c44500401d0701c840e20541090711943c04005000000714000c0803400280d01020001c0c1c1d59600c40c2c01c0030241380341e0030048005250360110030034003961464960020f0102140040065802d41191170444094a01c101d542030380c001c50340c0e90b034415602030307008003030708685486031480010307000781e440c040d0041c2000000030018070100c1410006a01c0b6403003071390013032201d00110605240030750011700790240181140d0203400015030081044400b80e5521601401e505441c52702e400d0000d40d00104143c8590303030100305c42d80c0940100d5009108000e595101e40b058655403c0040088442d1700c0040d0802c145080400e0200001c0002c81d10149 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 761597041 1250 761595791 761595811
    0x71214070b0a060e070917030a0504090e030c100c09090204050d17161110090602100c050f0c06072c040207060b0a0b0a02061b09040c020a0c09060911030906 69
    0x1d0303250308040c60001d04040d44940d800c0601e00050081150703218089404803904903400541c81d0b03002e8642035440b4402c05031950b0100701d080200304004600358101115107030038881503e041001d0400399034108480303e0301481e4155610302c4070400198020900002500d8907107011030400341000e000c181d0058540707001070400c213404070944600c60742ea401141c011140e841c90411188030f4624003031010030301001c5054800c0c1d440400c41c0482500c00c200501c100c4000340d009001003400202c100008208115440d41041401c004c0b00690400034001022855120002420349180c1120000c2c03208040345425215031340080c0d11810302d80c80c1d0365201628100101d400690360a800d15003400140880000c064204110a10000f4184000300280840300400d80a590080c1d41e080481c0c0420346480751038481d024000d11060903a42080c0d4081102c0e110540102c800205540d21110302151590780080b085a45401c0107004040d000e0041c20303c152140350945096040c00c55030b09488860042c181002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 761598291 1250 761597041 761597063
    0x10e0615031f09020a020f010b030d080c070b0c0d1a1e040204050d05070e070e010c0f080d050f0108070902040f0302090405120f0a030b030a21030f0f0207121407 71
    0x9030640229080b40c000500090030116a6650121500070f50000c0c3d200c0000b5001c0e254807403440a0040c0240b89208000901414455414030400c1d00c1042000e024120070030700c20300503000068008000c0b02d01500e4a0b08004c1d0700c4030000f034100c000b80d50120030002888804000d6011141d11446071100050000701c5902e51002c0e24107010030000d009640c00a5131005142c1d030000d042c8500071500005981444680384180d6031882800e41d4584004c0d0f400b035000441e00d409150200d122212072040d00e91065100614154030b804000082c5c5000b43e5032988066600d034010801540d00b0000386000b04440107080d03003070914140820203c0181403101034010101c0100080401400303100350960141120034203034036141c14065100407034000e604088086031401c06210760900e40050381608060f4414028030300d81a103581715078a031688aa400e88240f68642002007288089401035224100d10b4040c01616403040d4240201e0150703d144415003401000301c0100c00510f2003104a40f4140e41100c0d101c60 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 761599541 1250 761598291 761598301
    0x6150c1b0d0515010e07110a0201030906110a0306140d080d0c02070803040b070213381c02030706032f1e1e16020904170705030a020105010e061503 65
    0x501c658180100508038050180182c0800801202e0710303041e1008614080041c0c3e8510b0710a49180700d02c0b140d6005954050f40c244001513100f608850000d81c0315507800320798918040300d40300040d08031032504404652107040601600d010140c0b01204942e04583d5091003860b04c0e00c82e40c580b0700c50714100000d01505c0b02e0a44413054001c00039000205030f4401100d070f44030f035100b0412140c0e030001fa01c2280b14196102c0e00c103501d03030390790300071941041030508950700c09840b41620b0700f9658000696a988086640d11403401e590341e07a0700342032408024403950f02c10301241c0744105410102690802020315190080c141000c03403c1050003400a000d6070304441081c030400030302d21600d00410b8024131200000204032011354640304064500030328103580291480141c101c4c1200315001d213071599007260110000500241c5090f0709000d0700580241e00c25080bc0344460482583c690000f001a101139100092002441f81e0900c1043e006110720034512a075400c108000030110b94080f020112804000b00c0869 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 761600791 1250 761599541 761599549
    0x1905062115040516060f0512040f1401060512010e06040209090a05121809160c060f0203160215010602060703020f0d0f0b030c090f011215020c030306150c1b 69
    0x200400d122003007580d015107000d00d000c0c0c0d42c400c2c9841112184800800000507246e00502140c12901d0312529050b0815503080b50030783c0300c0c08008005071201d01c3c0280b1144d01181c14841e525090b03020060000c104141000305001800c00c22000354601a80740c00749124103800003180e146e4006074110303201d241c90740faa40c250a02e082155100070342113000d06144012601030740030050205464039a44074482d44000000c02501c807100720360110581d0040810340e02c01c984200c44a1603024414070000988180030b8100b84c00302d81007203c00c8401035492203078010720700360100b11460310b000c40079089001ca0f60402c0002522804094a00e809041c7c0101e82c5484410300042990b040442c0a501007060865113030740742c0701801a0a40290082c01803245411a0342003c1c08034921440d00e4420081c0542d20b88001000c206502c000140d0701e034034000b42030074044101400208401c1c94100c0c020350b01c1c0e0400c1010040240c4001c0d4207850044000c03c2003410810300410680c01c0c4110b044d1103000f100a02c10081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 761602041 1250 761600791 761600803
    0x306060e1f021f0c11160513020c030309070906080a080d0f1b180b0c0a120c05100b0f04090b060d141218010503070512100504050f19050621 62
    0x40d60081862191a603c5103103035074041c001c1c02d1400d40c0e41c141d00c40c614401c15a11000340e003080580302c00808074103100c6814142401402803407203a10051500031403101d41070640d0020f135169001a0090f5804000c01ca0351401050041d0803248054925064260307204082886040003030a80300341c40c0c1142c02800992903002c0b02c0c40300c0380c01e00c9400c5045003001c40280741550000305420410581c510200303111200340c0940b0310f03082180d0001c004074040c0381c803420301e41d4558045000c108a000091503002450a00c800d0141a400ca280480d140520b0303410050031407070400015000d0b624088480000c2210070710a160003400944d041c03161540c0300d05141b1303100000301c0c0b5201c00c0c605c2042268151081484010b208040440c03c0603109800c0d4140111124032043c0e48120003e24148130032529100000442d83c0c010110381100030300c0c50341d00c2c0c02080035203004a4404105105e000e0800c060307030701000a41088820300032010480f501c0c0070300c0020110103e10341584111500303450340080c008010010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 761603291 1250 761602041 761602063
    0xc1809050109050c34080712080705040807060c0206040801060b03010315020307091e0b18010e0d0f080f04090912020c03070501080118021608040519060c0303020a0e1806010306060e1f02 82
    0x807143d1f11805800c0400c00451032601810001d5810f100046500e88500203413819100080007503c03500d0310b00001140d1050490005a078484020840010104808d119090003846038110064136585942005c0c0241024120b0003075003540108200304d85c40754441c4042c000e503449a242c051041c80d40d82921562304115800158000b140000c80480c0200142c180494804090f65240d1500003200d080c0140d1070b82d1140c1c001c10443c0084620000a0410b0003c1c0400002070f8100c681425601c000c540d041d9084000c00782d503281891162680a1a814440510a08000d4006202203864540000c003402414410b4138050b40e06034071046494100b079011202c000d0f0090104426810107800c01ea09030307610a100351032048000304d41000c511004482520100c036a140c0b2030404a2410742c0301600a94424039100e0b00b0401e0040c2c805400750b0354084c0800500010107115803840c680440090111045a04484180701280440e0f031500d81d1204a0302902240840a03c02d003800c500c01c00341d14100352004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 761604541 1250 761603291 761603303
    0x103330905061b0f07030c030c2a0603021911031c05100501020a150b1f0306030501110c1c140412050601060804050c040c1809050109050c34 62
    0x30500e014400700084450060340d240c0e003480403804074114003041520491020a046a10a001c14404a400b40050401c841c0c02410038204005545d600d503106941d011140b055000011500c0e481d003400c06181040160203a41000c501c0c100038404510407080302030851004100ca1042c00e8181c0040070300903141d5940d00d60001501e09004100b4450140808403403207440051020b600003155840010b007541480e422a80d01d00d030040f00803e1030409007442c0d5820b142c0200b400b01381d402c200200c50b004048000c0040c1e80c005100c0303045251050940714220f075002807100003070020305000365021601460700181600780e1030022684400542d01002c010005125401000c64009010180300300240c2807203100c1c000303844440e80c0b114000d03600040c003580c1c05452a40841e0003191745080c00d50020b800700c8418100703000c00100a6a209044108030380219010f1a150b0340100700c0392040b4010187c1085098109070b0512401055007800440c2c00c03881502c5195a81704841580d0454000c41c03188550061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 761605791 1250 761604541 761604551
    0x308071e02280915080d05070206120402040b0a0b03040c0e090c13060503010e031309230a060504050915090a0f0305030c07021c021311030622050907030c0608010333 73
    0x75010103a0313001441450894003a000f08114018403d41c21140e0480e801030081d4209590301d8607040103064000c0040740c11070764520403d0301d10743c0c03000221001400c2042000360f40b0310700b92424038582c00385a0321440f4041400001c1c400e0441003c251400340c06030580d001c005410210044001408a5074002e9800d94a402c505a040e1000400100308003000010081c03650340d0f03903540017800c8460845100c8000d488110044402c80c240350b080c0d07134018440d5000804c020742c81b0350002c0c003280c40c10f40702c0a0752a03120310328401602d00f0f10301e0507962045184018020061a035125000a042c201100408128000001428402018003610310481d009044080500d48462002c13031004c40414080c1e2260840d240700401d602064011144c00b6030540312050308545400c814440050007280303204481300160300d8015144003552154a2040005000905c9030b64514140003908403103940008040251010052001c075a0001629842480030030001d02d1007450000300350b0f08849003000c100141401c03c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 761607041 1250 761605791 761605811
    0x30c0c06050a090f060c23100b031e0c040c021e0a11100e090606040911130b3109090b061002010603030c08031503070308071e022809 59
    0xd0954910380f0703210f0b20b40b801d4654028a801c00d0091040700e00080411190000181c5007040b280240c40d800e41000550301c803000c0c0c801c2c0c280300315000c0c840303580c541d17a0001408a1400300042e6500848844c41d00200c802200140b41d01da0801c0c154190003151103580c00041c151003040340d41881c000d070f20315406103140d41815030fa4654840000507280b45001d80c0602d14103240904402c1c10034801621042c0c144151901440708030940100500c2d0f00060500000641010b24020648141d8151480315940c2d184403501c1318402d0342a4110300e09072041804015040300c01c2c668842c00080800c4203400042c660b4071003400d58071300c458003c00700d0703039042240032001c02c07141008003406400202d480b0f00550040c01000c038200c504174400600000c0b5031482c801d01007a0100300443d00610022740c503042c40354025000c21f2600f07646500c01c0b2991107000404500741701c0800c3c12140c80a102004642112201e500040c480702d5129a1072215a044080c0c03481d502d0088c000d03800c0041081c081e0a004004032 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 761608291 1250 761607041 761607047
    0x6130e0117011a2101020f0a090306140f18010209100c060605060c07140402091837020a030905061018020a09060c0501060902040308041d0105010e0607030c0c06 71
    0x2900a00c04070960810801c003000d05100c00c8000107100003e003042c07105409810f103124010302c800301648a107543c00c01015071070581d60b030000c00341c0001540350a00090320f5454003408a07610000d4588620710000c00784280311141462a03900b00e141421070613200b444801c0030301d0083c495410015840740300b5a100c1d024082e044030482600c5400703044c040120310358507000d00441c1d10139803960746a503801c0341d0303014004c085801044428441001d0001800d00440d00e01241d141d100c442441510002e2032070401032840031303900d05d034040001000303020064411051550402001482c8502001a03008a00c10b031090b8030a41c4031502e026000300c01c940c01400e00007080c0c0c0f43c5000b01d0043d500c00c1440c8541c0e48258508034021a09502204c0ea2507044441c6400c0c003c0741e140c401c03010200c40039500c426000680345d041780090400340d070140203e59580c40c41c041e0302c0f2018603c080c00b117842c0014070800401c0241c1e0000319001e8644070644613141d645e44507140c00c96210349981e4006240d07084c400703000320b4003581c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 761609541 1250 761608291 761608319
    0x10090302041503081b0c03100e07080304080c061c060b0a020f0109080910140301031b06020a020102060109180c0f05010e2e031103090d0f050f0906130e01 68
    0xc026502084460041884242076202070f01000d0312103142000321703910a4200e03160740308103655844240c4038041e5035100002c0c01c0c89400410104020303242d1080300f01c444400d200340340013030900d03d00440c0742074908003485413500c40380d4803114400c280206201c00702081c843e485045c81d883d007035001c0114584400c050034040d044039001c440184102c80301004400380511943d030180760001030040c10a4030810420030508000032544080081004660790240b103910051400b035441484680514100c0100b9500500050b034000811903004074000d00241c0d8000c210755040d1842101c021078000c0e241d041b124070132600400c0c0141440e018000004100e03049240200c2643e000340d0f80c0a040d109560100310540503081a001201d040074002501050224a41080c02002d5800c02040e0031140c0e0400003001e030400c81d204480d0342c002000241005510104080c00446c490400d00c1c1442e00e21540364606d8055030031a180075600002d0035041d041c0e14810316034010a20ba82d503c81d800d60b111045002000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 761610791 1250 761609541 761609543
    0x50102070f0506130509071d06161203020f120703201902030f0c070e061207061d04050f09120a021b0a05090709060806060702090c3f09010b0f0d03030605100903 71
    0x41d050b60230680c81c1d1501300220b030768512450110f01a00f1409460b040c6224500110344400c1c103900300942078200c44a20003410452150000c070030500e1520b40c40c050700b40d5030503110021000c0070481544070903034603082c2520f00c41100542540c1d00ba09450800368594402e40344040c1030800081021182280c0000f0a2000d44110310001000d030744031a000d1019190301d28010420791703001000240f00240c802c82d440212600c4403d100000d42100d003000c107017183d00555204440307a030b0314410450707001c070200070380034401000d103c80d907191440d042c2c0300030f480c1c008001132110145502c0502c01415a20080240c0190500078045041c90405e4200642852828420600882ca4144c00115246000c506950ba510b8001d0140720b01c0395121461a00594072000c0c00f5445620b06400c5142ca0340034114a500303400c1c203144060010307003441c0c644440d50174070003d2030f44065a0400c1c03803032101c685076002d000c203030aa42600da030520071007286820380c068a841c0c3c02150b0803844201414916643c4a14150212 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 761612041 1250 761610791 761610827
    0x204060807080706090e28060b0409090b1602060601110a080d0605120a2d05010c0336080901020304030b0702101a010c0b06030102120a0213050102070f050613050907 73
    0x1e070340d4603007170003221b0b0340308a45081a000312020780e0910100c0700d1082800b1603032401400580e458071009480000c2d0055013081c1c42081d610101c04003003001407205541c000c54030690079820200700000c001c1d0b913100c000b000241008401a1500c901c0c82e81004440d80e5598414080e40d201d00090480b80700a020920540f0700c02c0e07054080390740003603101080c004d0740e2982281c071006440c1201071015070001a82e10359245224130300407040740460b600f0310074807882e00c500395404615040d10300d002c4000600c0581300c402a8061980c04040382e07100081a044c401c130b0380902041c4d126400440140e085009540c0301411071710541e0100580346501107122441c02650681c100712400c1e50451164400b50b80d03214031404610182c0c040c401040d1003074041d03030b40100b00400140c49c1460b0352220340c090902c00c1e521402001c5e00071803246400004040c0d40006041c0c03e10061030030a190130080318480c8418480c1500492001449445d00c10a0107148000340501074608a407906016500405a00001000d6014 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 761613291 1250 761612041 761612057
    0x5070609060f0810030519110a0b0d0506030102070b0106081b0408031c0b04020f18030c0102190312060303020c120c061b0703050604080c060f0f04030c0204060807080706 75
    0x40900480200d000d0381c1082c0e5880340c04820103001a1a00e0201070310030801101040400000108100841380d40e100b40c1d20b00c0000503104528042c00d038034103019480c03803140b00010800d101c640e1464040e180174980106001c606900c1c9c40021900a2007269406000d0b1103102001080300d43d081a00310340a9a0003103050010031041d1090341656020b940280400c035041084840c1d02070a04142030b0403540c070b01c0a40010008201340004041b644008001c43c01c40c0300219211850340c1004060f88038046e010740141c05908602c800003034441102e102541350500b010600700003407501c115503284900d40342c000d04010564036410040c2d079401d00140400e2060b806c4440c0070001d05404501c5540020019000034108121040f0102e410700b20132943c9619403155807000408600b0401843e0301540c094681c850307442403440d030098203226005120035088400780061014407900303080700d40c2d40700f0b4161070110b021004602c0001c0c0502215404400b291040386000301d480174000c43e10340101c60040c3c40b07032a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 761614541 1250 761613291 761613299
    0x403081222020906010915120501120b01050112090c0b0315241b010c05071505010b1e1606021902010506060a14120103050a030906020a020a03060b030f190507 70
    0x40c0c01e00c000500311030a44a03070050006040c034807043c5402801c14189032480c2c1d507c40418202c500e010088280c00a00c84244c014050041481007034003401012454a850b1041d54580346542d00043c8281070400034100301c404401d031115407104e000c1913480030303840d2001c41d92030051601c0b941040ea9008010200909080e04901c0c0c600b418002845400102141c0c040103070400003c950403800601c10b50104400001c0c0303907a0800c0c80765000032055a150381c2d80300d280c5410070f1880c01160200c0080c41615080c0181b0040038054103031204110360b005113420b940400300829007940103a040008550995803100c01c10068a82c010700700c40707031504002c0711040c100084220b0036507405641e66a088202009a01714081c810b0141185040c0c01000c282d280c41040003038070b00e00780b409030701c00d945c035400881005040551111480d0b0040a40388000c01c440300c0603070000b036103644981c07000400d03803555040031007141d44060040c65540d0725028240c4111846040d951b10344008844400c030362351701034094042 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 761615791 1250 761614541 761614561
    0xa0c030503090405130b06060a0c020607050a0c06080411100908150403030e03040e06090a0e06070f030c0509060d0903180f030210020102040b0d02030402040632041802040209130204030812 83
    0xa11691b0821400341144d103404007800302682c4069074003010080e4050740d000c0507844860040141314801c00052040721141d051020359021250000030400c0700060600c400309a01515540d5130001c02c55004600c0343d40110103513030758a056800009540120000c000c0b240d06444031841c807580c06070f10305000070700c4400c078002d443c0e01c514000c03600203400c02d10110794142020800300c0e0707025400f440700240303991450041a103000000c8504200043d540c0d000708800c103034140141c401c003403881d0501031b042c1980d050004100340181211000180e6031007239104180741c49001100b200001e9014400c01c0d0710340ba0b00010120110034001603000701c4603580c0007401140305100b12800c850b401ca0070141008016030001000e0f40c00900140e9019490b81d10104000200d4242c01000c0c454500303408414000396081078106181c1e1080b140c0c4110700d0b2143d1a029140c1c100400601c00340d0444005a868450300300052804900180a80c456031001c9400300401c0141c0004010810040502c8000c40e80d80e09021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 761617041 1250 761615791 761615821
    0x60b0a0506090a0b1c05040818010315031b0b030a09021809030313060e030d0c0f02010b0a05012f0f0708061b030406020d0f0c0e0a0305030f0c0a0c030503090405 71
    0x20541004100c5010011840100082d25141102d02040d45042c400c031790104081c0c1d001510182c482410020b00f08060b501e03607950011034058207080900420040100c0918442c15034440038042d00c3c031071403038604040d880a16500241c070300b103044143c880c100311403004010440190224001c111244048000f1649018614420040000114655600e0000b204090500f000084030752903101c140d01c0d607446000740003030071614034891000101002030120040c01260810030318015640f500d14000c2c06a10341c1d0180c501035580a080c02d0304055201c050050400640701c521511250000880d029154808602c03c06e200f10008102d50304551180e99150300c0c1ea900f501c4141aa4034550800c114609010010b99401405490700604107050150200140e41101e030100502c540d071960740e84111034020320b001501103015902c0150141c210354802e903803841030340d10301c1c0c4200e90085041e42ea2502c0403c0700000b4107038490f90f00000340d541c0b803429603030340e4000c0340c0014807441c28980001d28014900c80d903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 761618291 1250 761617041 761617057
    0xc0828050c0105070222050f13020307030b0c09030a050a03020106170d030b040b031603060e0a0b2a12010f15050a030c0e150301030501230a0513020d060b0a0506 71
    0x3034034040071a40d0040d40e10b070b444004126040744003200380e982d0318402201001865800b00c1400315181c640b40300c044d1196600201000714045a880d001000350324001550780680c1c0d40202180135030b440c2e10484802c3c6000e045040c81c0d15115800c00102004004503180740070314407d800900c400c6442d8400706281c1c5000c0d80103040300760300038111048880e2207504141e000b400e000e800041c0d4140040c1c042030130301070380c00c50050084c50554010010400588500401d030306e01d5a001d000d0b04440c59946200c000e0020300022071034118807000310341c1c90768902c0c0403182103034008d40502d580d00a12850199425001d101d00c001c404091440043d6444107060a4010403819543c1e0320b1500700c0c890000e43c02082c030a03041c8410132603140302888507a11850010b0802900d00303011203450f90b14518085003950780300c3c0810740d815440d522088500c460360110761030304840f2542e00810300e659017201e011315008804a004c0d5101003080510380078040c0f254048012a0403c1d161909602d4544041c4111481540f071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 761619541 1250 761618291 761618293
    0x809040204060c11101e09093e070305030a06090e150906040c170c04020409021b0c010c1e0206120106020c181819050c330c03070c082805 61
    0x40c2c11440d501400c601080c511500d080c1440d081d0748234030400e402c40341a45d216804000204444c00e40c0c3d0b000c1c02e101650411524080400b10800d554810f0000d8040c80300001c041c000040049a0402000d4010002802540e50700300003200c189014580d5a0130b002c1d00c0c0c031355826105000308100306c02c081402c5d0711030741c0c1006800b00040d240c51101d054418040c4440440c6005019800c01e55a585000030002003024650244c9c4038854400b001000c040715201c400035940c441c0e4144521640c000c1c400680c19900007100b81134250141ca43c00000006482000303500c0940000e094220340410804141aa2486e0307080302d8008121009200f408680b484204150340740b1400000d628041e4813034101c1e105071605090351844040c01c41512500b500900c8112080c0d002039503440004d08080700e0340100c1048800911840e900070700da010340a402580d02003006828000360074900700c0f1041007107070402903002009005441d643d4070b403162902c1d200848207050a00d02940300c5120050f800803804042c4e0048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 761620791 1250 761619541 761619557
    0x80901060f0e15040507021f0b0a1406070605010608190506031005090a021c0605131205070804031401060512012306010c12080a1d190809040204060c1110 68
    0xc210004404000e206400703d9041201028190329075015090084885400a041281843c4016505c1c00854040c9401035890a4001d088540c0c0300c544002c1221054000c040c481304491010a10074400d10070701604090400c000001c0440d4030600e054442e403404202a880d1142000c4000c0603100192901c3da4140e21088258000034065800160402c101000702c1e203648409601051412208003070500f0342ea07102244400034003000b4091180d100e103408080c614403110544d00d010403400d5146082e01080b5010038040c042028400446001d160003590b415203801040002034064500c0d4007549029805260f514124003105008124004240c3c000700038074180c0307240400300340260017440a4100415000c0100101c6d0f10305404d24000511951800802e2620090305000d0341c2c06003485050100180521081c202008265640b1014841a17090903960a60500a13410300440681c00c0e03101e807000a0002d0b0007a04004012449882541071100c02c0900f4001c01c000ba003000c1c109000803e20070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 761622041 1250 761620791 761620799
    0x1302032404110f120606181003030f05040b0304061a0103020f0423040c0507211202091909020703090518160507050a0605060102061609090e03120702070303080901060f 74
    0x2559030b40c151000040c18020280742140d0009440c038089050103c520b402c42410300003a0304101c0e140c0c00103243c403d042c040c1242412070081001040301c3c84040d04004c4183c01c0c5c101c100e845a4101c400810000c0a140d880e42481c0c01d00000500c07004501e4400d5440c00904a00294001d000b59943c020519111604040c94980c0c803642600303860901e000c9403030b46001201c0c2603a880d03206500c208850341e03a825849008520b003440700c8002480041c001d0710305040079030300040c1e403010301c00e21000034a03007025803038a800b8400301c0e445e8905030004841030048101c001c00c50b10b29030350203084024003c0d5201c42520b035440040c00821400403045e5840c9150001c0050b071440b010010404e02c14000785000e602e000d58580343c650506805c24011542181c907041030001d6507904000480d00056010a031800c1c55521790000742c200446482007501d00c4d91940c00220304001c0038415250041c01c1d56084209900c0e100d4002900e0301e1b102d010440c00f15170f00401050340600c1c14480e94055030b101c0c11403540d540e030034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 761623291 1250 761622041 761622053
    0xf080106020309041e06060c174e190b0f09040f0614070306090c020d030e0709020f1b070605070f060209061912020915070512031302032404 62
    0x1056480720b018074642a02c05d02d49101c9841408001c000a0341d07a58940c41c11442d006c045400440c4030110246801e10000e40000611001c00c0048101c0c03010031219010b085061030b0000c40031103d600d80c0e42030030700d0b8801c0707170035425940c1c49100d001c1040000501d42c4884400c6401c8030744450455401c45000f41091f500d03401c11100300c41c0c00c14081c241c0649a0040c0e90307581c005607500f5092002e901403003030302440b81568140c0a08409040d0b0382c8018010248054002507071240c50f0f007101d104150312800003c03070030001440b00c4006031040100641d91444007610301c140700c0d401a800110060102c12401056001c0441d21000340d0300e1036038500380b84c4441e40d1130700090603000c4d80d07080c0c40840d07003080b0016540d80c4000041c0401c002443c4151400049488094103145d5401d40007540c2900402800c2c00f1644c504199018901c2071039401516000c16050080c90b00284c0002e80307110007000070503c410f040c04211480d0340705100318100e98400c3e8040d100a8820311200d07201a444444c03080108000440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 761624541 1250 761623291 761623301
    0x80118062301030f020108070309030e091b120609091504030e0109171b0906101d0a081507052a0f0d051b01020708040312110d0e010f08010602030904 66
    0x10324002107030102a040e9940305440000c0e481150f48800c241d0b011011940c000a180d54080503d00b8100218520f0f900c2c0500100c580a00c110711071000640003549104154005240741c115480c0c20645501207203ca001281000b41d45107481001000c0004054560008050308606075400841e404c0c1c1d280c6650940c0c003102c0b04104541403041840011600c81403814021a1a200c4a00101076406269440303048454903105001e00488100c010041d040d152400352844241d0980f600540d80000c7d070b01e407480300d500009807080d401904200c0003c0c5540c0002002a10700d10546203003c0310752107058082c0e035584605e03940802407402404400b055600701070189002c0e040d464081c0ea103003014507440103040c484d142c52a400272030808640e000c4100141d01e80001e400070100000c40c604034254444203214011844000e203d200150590041184039075401c806084d00303c8208d4422241c1e900c0003803d405120528940062203030000c4482251080e201d05040b943e0b150044c5107030404100c20b20000d05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 761625791 1250 761624541 761624561
    0x10050706061208070308091c0f03090b04050607080705090102070515160b01060201060501020a17090a0e090123131403071e03170403050306010c141e0708011806 71
    0x541d68200005000c1400406034182e24441c0080603662030b21481c020700b181c0e80c06448640d0a900c416001e00624141040854240605003444071030702250910840c0038004141c1d0050120010b1018001045000110a8011240c5441e54041941c072200c0071102401842a0140140d01c0500d0401c424200285001b0a11207002003c501d0002c0b50b407444180341d00403a40c101c852684e14001002140d90a2055901401091002e0b040b6034030162115060071914a000035180d9400080703d00540c0d807150900c0c8028402014074501c1c61415040c0940240345403000d1440c440859030000c0c1c94004e4a0840c14420300722074180740411801030302c0c2d9042c40d400079000e040e60f51108009a102199030404c100340b800499840c54440310255150050400c1c10032114024240120320500000a80020941764841e03c00c2c6041440d0b00503074242554208441c1c527205041d80141000c04443c904136004e031400741c040d0700c401c070750070943d8400c103903403ca41c01c1565000c1c0e210a000f020707030002081900f01000003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 761627041 1250 761625791 761625803
    0x801090812011e1e03080a0f09080f0303010e15031005040501110306060d090503210105030d030606081305030f0d02180a051507020604032a090501260a06020a0309020405090309100507 81
    0x1584039030741c00d5561f03440070b00480c01056104000300c281580c4041e0711406800c00303201500e20188681c514940d207000600071080000d0340320001400d4118038140c15060541c0c02011511b8801003485000f00604060321300b40c910754200310505040f0a81e420071207014900180140745040c2d1008503042c002d243c0608220790314042001014100e10a00140f00c1c9030400104241e946949860f00300f42c034140c00c4010b0b0b0000e00d03081180c02c10541c0e030061100e5a100d0f2203245055035a0b11185000c900314484d01c0c66001100d80c002c03811801c05285603000c0c3c01215643e0f0046600445543c0030004101d843d03115540d0b0200000000c500c0d221410360150549602c0580b01c642011349942c0e90304105c469600003415489500c0e01d102c2d83d01d9082c4c405090040070310104c1003000f5410310700c0c802464418038000703500108100020143c03441040280d5840c0c2da80200c1d0454503415405030042c0503001c040000da10440c280702c041454200c0100848664000c014085d0b5401808944150307400d400c251000d45603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 761628291 1250 761627041 761627099
    0x506030406290a17070501110309190e060a05060306060d02040b0f030f0703140105010e1f080619080a03110a3804020f01030509070801090812011e 65
    0x2407a9115a011078011404080c200e8840241e00a01040c1d00e0f555201c1d1650070f422459132060410086441c10680700c080c82c04800d840361360b000c1c05103544144000c040c0c0103650b40e181d8004d01303255607000500390b0f04031000040c06500d42208000500c8058014942c2c80801000440c84501c0e1040050083c004140700141c20996244040d24190300048801c40135080000104011060154005544a801418100441c207030034443c2c00440c0c403050050505001c00d0301d61404481d6502000d42c2103c480502e0040141e40f034583d4000d19042c0c040d030303103036000c1e54608108000040c26101680207a810b036000418016009440480741c0040f021150a10383c024030b80f01c40e0108041c602d400e1109880a4503c40707800707088000e114882c8120075004018070000406000061f52000441100c0100c00d02e030102c0c01e91110311425040450560011030150300c0c6c00044800c10855601901c0b5100910602100301c2e030b61080141040348040e0b00402e0040002c0c4424000d003803810440c107460140c2d280c08028 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 761629541 1250 761628291 761628311
    0x714010e061603080705070b01060302090d050f0c03060a200a050c070603051e04030f0305040201030e0a030908061501020d0c0516140301050601020f0c010305040f02090c0703110106050a0506030406 87
    0x40c40c0e4012140760602000c003020384030a05400c55100380d088107140c17400c40d280000c08c0d00c504074044010301400081540010707000c0c4090ba603090807075064a07004416642500c1b15840388030f81e07a0190000380c1d8020f00640000480c1e0131a60f00c0742c9102441d201540440010002d81459150fa100710003000034064240020320f902c85d000c101c0c0402801060328001810b0501c4035003841c0615803071641000f0741094004003c00203074460200d030038010090401091640326880140d000e0702c0540610645c3d4400d003c1d029080c568800046001c82e02c000c0d06494590701d6104003040c0c035143d0f1080aa0150f0b0000e04c1c400d070058410484540e00e5030081c81960440003400d064440d000e0b10a0740314004c2e084026421110902e402c0c4141d50704201c00740000c00e845030306a40c1c100c1c3c441d01310100290601d80d58000003000c1c0084500e0420b000d50b0700400090282c90903d45d07024481d08248400d4001840c284009001810140b0415060f61030040c12203050615020800c00e041d1310003042128036a45440d00c0388 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 761630791 1250 761629541 761629549
    0x403061d030c070602061006270905090a140307020108060d06020c010606210501030201090519050d080714071a18040609020d0e07121211030d050a0507110714010e 72
    0x1111280e50203001c3d060032807600c81c00038984113000e407042e0300d40c1c80700c0e600400c019600198070003e0702da022216a841c1483c40a50400c00d11000da01070743e159410841009040000880c440322044d01c220b900c17500350807100344003660360b0155000c002d01040b20320011400c1c618241d800d10704010300c141009450100e0b482c1d101c40c25240240e200c103020500e0400246191281da100d9542c2880d44081c08002e1989150002040f0b03d941e40324690040d0786844030016040310010b041c00140501074100121407070189001c405650144000350b0301d94066003445030342014041783d050221804041c0d0740100c42008803508000340d0081e100c024110701c8610600c0f40b0b03a111806050300070030300e05000603110254010f996003640c200300c01c02c00340e6402004c030500c012200c040e00241d03519001030000e401c0700d145000c181e4110707141406405136403001003802e000c0010b081d04428842c513280d1301c00340080d84030ba10040d00c80f905030502c0c65000d608440414442c02c804041c3e0f000060405240c80c0100b2040f190100e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 761632041 1250 761630791 761630797
    0x61606060e010e060301050f0601120605120c0a0e091510090509060603120f040314072105011b5301080a0201020a110625060c0e03030403061d03 64
    0x7115280d010200401c4100600703180c50303601500070340080c0301600d070800d62402c2c9503500501c2c41d814065415084070300205140d10007000b805020305941c2d080d003551240569a06800079910303114410380f02c40400c84145003680780e4002c11a80000f450b0f80c851407405020800d80080468070b868046090005d0b881080f030003120f02402c1103d0180c4480c0c2031200038142044103801411292030b8040204101c0301c43e1031011901241d8204002ca084c9441c11a00d0600740441640f24600f5201c1c5007005084000c40401ca921a080c45a0001c11454981118140080c440f1602120116500c04c6150b1020400000c101030382d4070781c0c085449140000d240c46000b40c510320091000500b0316001440c8140c1f2803d2038254050003102c4000c140224243e40000d50b03070850080000c0c0401003040b0300c0d22254855506550708005552807580c1c01c06aa101800c045042c6121306560b52400c21102c10300311780c021420003000c68070103400b440c40c19003151520301c003030214107007002603681107911500745052043c005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 761633291 1250 761632041 761632049
    0x123405070807150e0c06390105160e010e09060108060406030c06021f0605060f070507050907030e0c100519050f030a060e0108030415110c1005130605070c0506160606 73
    0x2000802220400d180401c02500140a40d40030441c03840407e042e00241c1e44880e00c141341c003010114601e0001c603106200f03000708400c01d41c20001801141007021440700b013a02480d0740ea220300c002d04200112126445000d1031074011611034041013103035228207120341e4040790261000c46e2281d96035580718020340482d80541d0058202c003849080200000d0240802c8141200c4144802410800003525610442e03600403211040060020108401030140b0001820004e10040203841c1c070200240c00b070a0403450a43e114042c004002c4058504056141c20741c4020342c3d1080c0c1813020241c801c5c80e82103040f40b80a01880401c4c4000402030070800000c6104e1014250301003003451a010041d0544401030700090b240fa0014802484100b60340e0300444607400c000d241c0b18000507079004280707042211000d81c940e0405041e503400252a41c12200600007401300c44000030503190342e10000c540e2800342e010014200c0104242c1000f80e4a040c2010708450b038506404c2c84500c280d29624402112190343c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 761634541 1250 761633291 761633333
    0xc1211010e060408220803030f040f060903090e090105150f01020a02280b040317030414060403081f03020a1a1317070501030b0f040917123405070807 66
    0x541d0f202d01d40c1e110f00401c0705505c1402506946103042c1340d02180c4a00004103194000308506000034203200319075003001100d64015000700811400360400411460550040d100c944544501007540c040d81449610b100b20103251002c11000700020800c100100c0c500003e904511406043c0c40c05a0b40700c2505d41a0704450800382c164450340c01203902d0761801c4950000101075000c0c8410404035140109401028000f00800327656036503203180540508d581d1b074181803620300ca6001040202364102e01c0703060040e12030b00e0301103640c15018071110810b1800390100035002050180104415502646005210b9000414040c284514aa01c20001c0c0801d9880034490982c2c950050414200602c05440900303801e183c11700000f50b82c05c02044180d409060f100d4080c6540300c7c221401e000c0001c8a01030700d490b1451070283e960021051303012001d1000d81d0b40400d0919109014403004441c000407603640e091800b05d00140030620b44041d142504003c8003600c1d40304041010742c00199503c42c03000740480d40c001c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 761635791 1250 761634541 761634547
    0xc02030706020d02060106080606130b07050c0a0b1b102a02010204030b04020d0f0516170304050d0305030c070210050a0e12060a2c0c100c1211010e060408 68
    0x401018a4540c00d81e20000c01e6401200400001a90216955041d80c03000d0422007165100c1002080075840b5641801b81081e54016011810a001b00018a04a40607070202c6a038510748104000710307104148140e400b0840100b1084060400b41e260290602c0c030f841d021344018210010811083e2100d40c5240c007400e01d903225840555403825031503440124802e100071828541507591320b04c0000c20240010784541c146805802c10402001e000743c00b10380d401010781c0c2500e81c5510b4101d84528060040410002e031410b80726003010740003c166001c50780d0082c00b610161b030254500ba14568002b0f4511811180108180d40c09038490305410420041b80766103403903840380341c010300400e03002058140511400e002180c994020000084280c0c2044440c10005103a02071000441c04003030001130707515050b03085003420b50845000800c0080c480c19040c0c40010001e480000100c03240014031f0380c01448150305556101416100d010301100400003040000b414a602c070117428a0300744212000c983e440300c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 761637041 1250 761635791 761635793
    0x3020d051e010b04051e04020d1418060c1b19240b0a0501120f0f020901030c1407061d030c06010f080c1e01090f06120b0d0f0f030504090204060c 64
    0x300103010b004000820f0070500301424140060210481c10b941140d5102030016100c5040e40c8542c11207500d1040c4d0202005208900c1340d82030341c080d0742101c2e9041c0040d0282c07141070b038100b000325031a44100703040030303942e450100c85491aa40509410000050500c00c038240d04541031109000625460700a50000b54038880c000c1c22661900d4201c44080310041c202128403000303464241c54001510002d09000070003200d41072007080140100001705007440e040903110106040d01d54000e00c00c00e2800c1c2c0e400e1041113601c05050341d659100c0703400031101c00e00420002000c54055805990042c016400440c132069101c1000c07451504504800d4140703070050001081750400300c1c070340760380103041da01e0142170703110700f03106c005404560515446481c031040800724040340d80c82200c02d8030141982c2507103046c00a4451000420454622026182e0907241001e22825071400280400341c542d480980300d0716200302e954908010801001084041c49014032000c50000301c2130025201600c42c0d503440c00320350003103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 761638291 1250 761637041 761637091
    0xc0201080109180f051510062c0301090606030c2907020f37051e0307050409120e180105040c0c050613031403070e060f210708062b0303020d05 63
    0x940100d4800c02c5180d010000c040c1c000d002e4216a480c0030304a01a40c2407072440050007270b0308210600b9410b510f055510710405c00039510140a032401562211300c0c56494680310002c6c150010300c1005401030031000d140d0b14071030b044003c0001e40e1000d00b0300d80a18020310302082c4600991208103c2003c5040f141e2100d1400301100781401c185a00c02c1c0038070a0745007e0109450308020000e40d10071070a003407a09400c0b034504001703440003001c011f0020061074600d410505482da0101c0726041c0050104c43c00709084e4908140d40300c1f80c41200c1e803065040e0781d01c2c100c1000014080c2d01164014821901e0032900813410920441344030b01c0584840f107100700494a0002d0941c200c0745181c4420180600c1440345d034036030101d2103040801083c0c1d156a030303d122460040d44c00340201c05200c220480803010020442c0109100c0c1800b8541c40d072508070460302e82d0410820214001e140030340c00810781081e554443c0500700d10f11580300c5e000e403c0040c0b0b03090060000d9003d0341e0007200c03003003031a40c81c494800e100480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 761639541 1250 761638291 761638333
    0xd081201030c0806090c1302090307050d030c120c020f040504061e0609061a040e06010908030a030f0b03030a0e040b281518030b0604140f01030c060c0201080109180f05 74
    0x4108003070000306c100b000003e1190f60810105504040d07022841d0b0101c0e8504200b4a00038000c01080b18084018915000300a83c54056040f070740b01e8010160807518174000c503040a0025070007800c180d4040c101105100082000900c262056078841c21550f151400308201721f00c200e45502000b184180c00c0036411025107200c1e60052500b2005c1c010b08e0044d2a00c0c0030181d40989203001000c0c00c0790380711900121102907050f000340fa0103001c0040d029201540581c85049010f580c54828045036108200300360300c078011804581d010484901c3d440085141507801080e00340c40003001d607469000d048090000041d0440919003001b481c6100034448070380e04801000035404a4139010b056104103090955120b03203580300003015185d1840100b203182d034603030300249152040d0800f804000e241412030b4031240c8000380f2080d02d4020403407602040c00307031092201da20038039010703151000c1c1a440d02d00c01e18002d24610b007610240c0800781c503400b00098044111b01460500401c02007610380c2100d160800c18607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 761640791 1250 761639541 761639551
    0x1106191404030209060402030603010917180a180f1b02060f0604050c04230d0f020a05031b190302040e0a0606051f050a020106030c0611070915050d081201030c0806 72
    0x80081c0030400041e0340703050303a03940e01c207030700752405a00e0351208000700b4050703d40c0f0741000700081c1c43c400c000c4112503803800191080840d1141480c1140c0b402c0c0082c4103062500d40540704500c2e20826017081000411781051101814408000408200c0000b001c003401500e001c1c0c00d40103821010600c042c9600842d10305400941c12182040039080402c40c0c812030b80705900c00c415641c0c110b505c00030028000c003103010b030b6000d6001c0d095240030300c1c55151044180381c3c840400c80c07260030002c2021825040024101d1103142d074185002e804c0d01c0d8500f0400004011005034204408191403000c401a20307103016120343c042110703000b010800e1151608030240d802c580c00207405500c80b03001ea09060031961520301021041341c00c00c1641d8105e044d1089014111070b81014000740515100011819404111140d801d14820309652410b42c89040b540203486030203c2210b1018407519043c44286031103010240e00303a01c600b02c22443c040c03070020103845c210000d90040c2d8074a50a803c04000300c0c80d041c0200c9031301c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 761642041 1250 761640791 761640827
    0x408060612032d0d060503060a0905030313050718050f0112120e061608040602010c030e0a14070f08030702120f060a02090409050a060b04141e04110619 67
    0x40d5081908041c0d581c0660309040200e144824039050203c42818402080001c50044055480d8400303030030303440984010300c038050207842084000307003058a0522a200080741e06c0000b1310326588800500c5040c080d01514159681d00031490001030200c03594524844400100d40f01194a05c3c020015005004059002e1301e03200e0a507210321030010310720318141c107200c852074107103940d1140ca9a008901c441c0505526500800710040b0808244051070029004aa400e507000380400d10f080340049040d20311030b075071784007036640119548000615000130b020a02a072030340455400d0785e503c0744901004541940070758419000040d6076015810840581c100004a400003410420301803201513503682c1000b8621a44541d0106101903a035445411058269030050f0441d020300348641040c00c010403000782254800ca203410180004000c60001d03192040720000907800040070242e034044180140140704071008000d000b0061700e69500c102c003910500466610a0001c4506690041c08100802c601c10b80c0c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 761643291 1250 761642041 761642059
    0xc1002030703170c04080d090f0b070519080c060103030e010e0a181e110325050706090201181d10080a020607140a15151503020c0c1504080606 63
    0x1007500b00c2c81e4050014884440202c0c03d99500104c2611405607030003080050103038440301881d50358000e68010941e42c00d00e07501d842143e0350780c54180041c490540c0007405a003051445c001c40d03050b1485811610b40c000d550043c40e00750f07010344c50f50a01500f42c20840224030381d200d9149030740d42d000181c015201c00944607449494100b0769600e42e40d0540482080171503889a5502c043c00c2082110041140d9441600303200c016903010100d41140c1007200c2c2c0c40110070171103401c1c0801c41303154508009a01c056842e658507000c510780302c0030094528440181e05001411403003414a0040c0c8490f000100400159240c05250340e94450003a050080c0220442264201c0203009250000c26003144c51541101e05a0703807409249801034180348080320220150050000442c10f007c0c000c3c00655803042a854100141d503003085414422a615004401039405803090440038075000354001c0842c0340c200340858400030911000031340d071140705400075404c01c5000f1404002c840310410280350000d00031116201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 761644541 1250 761643291 761643293
    0x20a0b0402150403390e1f060e040b0402090906010f050c074e03020106091107150c0806040b0402120c0910110a080f0c010c021608010c0c0602090406080f0c10020307 73
    0x80b5504981c000c0c0d4801b03e255201003607030421b05400303c032945030881c10903030005c680e01c40c13020309101440410580500e00b0601c00815074501882152282c10b00107180050548488004446484540441c1c0c401c0c420104080d968013001000400e0061000f1801f0b00c1c0704501e042119003122000702c5020b190170b40c2c41d04446040c0110040c044100030550000a81c0e0f45405007003ca014010707541c000040b842c58440120b032841c0c540c000400d140ba000e41910554510f54240c0702c02101c80550b440320000346010701061151800c2e400035402c1410051001d0306240f64105112080442516010803581c80000c09003950f04000210720b0745903203541011400c00c580340c01703031940711124444014a00f11002840c80c501900e000706542100000764001c11070b0a03c1d105010795a661882c955103581e80351032000103000441400350009490340b660703c01c4a101c40e075907110030281d0803000005a110303031100008102240c2c100b2407441d401001c3d5005003241d40d210020300411402c0e2030074036002c41d00b04000d000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 761645791 1250 761644541 761644643
    0xa12120207050a15020f07060c11030a020309010e0a0305060f06010908010e0a120302070c0b041833050409111008061c11060a0f091401020a0b0402150403 68
    0x81c1a8541141081c107866202c041104002c1c481e03483c506c50400c40203d1118244001903025104422040c0c0755480c0150032151040c0c1d6074010115143e0040c0c0c420445400d031540705110f031202d40b1001402d0001e9803500c0780e0300d441c281002110b01d80050560007040088070741e03001c40048002c02e50305008000e0b001c44804200d440702c024200c017526002910325240c071040e10950403203044507001485080600e859036203100e0290b0061151907103c0c0c110a1442c60780703c11611481d24070401c1050001c0080d1039145140941070b5480b02c0c800c4551031010382c001050b896134042c1101d164440d24005031403100800402c440543e09014680410400380c0411880343c50ba1705080310b40c8081a0aa112184818503216404065000315650040000309215072060f03000b4000341065112500c0340801146c5508000105071611403500340160301014a0402040000000307942160000d000d0341086491100200f1841e4007a138801c07105a0420310340800704240071350880040d81d101c2917100312600c59501900e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 761647041 1250 761645791 761645803
    0x10b1c0602032508151f081003050d0c06180302031b070906120302010c2d050f0a0e010206010f0e0126100506040608070b180102030c0a1212020705 65
    0x40c08181e001010a941000c6100112100701c040140b040e19100200c0f0300928000081d03624900401700c1c510060100c0c0780845e04403d41818035070740c9001040d513040341140d401901801846261304041408004108240800720b0800300603244e07450003189603e000c0d803c0310100100381e4400324800b41c8550000e58048212200764001c49158042160150388003800c01005600c04c5640170303d001400592401c500d805060070600980080004a05922081d900c51140c0a5a0645441507058a564400701c8c2508141c0c8203a0300d181c01400d0607604c0c0011500c80e40a0070b000c00100b42c1e00c00c5d034640c10b0b43c1e041140d0350140c2108a6165449803428040c0204840107014803110007100b84190852111301d061080c001e414042c085900f00300101d8101e40052805582c40c500503400c03c0340104080900054400840b9141414a490011b0303842c0380078076900640552604600040114064038202004813104c814002d001202c403855030f0110103090007425040540000703006114101c0440c802040d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 761648291 1250 761647041 761647043
    0x1c0e040e030429030906010f0e0402091803091507050105070f021207030507081c0b0a0b0306120a14030c010c090506180303092e0305160311090402040306020c010b1c 73
    0x50304104400e0142c10703c400040300d00786112441d1020080203011080010600e040b100d0f00c10194412035241c0c01c1c143e2121a08407406500942d441000c10f1107500d50011030948580c0135007d5038289036818000800420082e403004d2103100010564a01b03012080c402c003a04140241051043c2d50030005001c0e40b81e5003003d00c52401144003240d144240f6002c1c0017281c00e40b6a100550b20750724021802002d8482510743c0300d0a82051511880c1d041a0a2041d00c101c140c1c0c0c040a112403c6603038900030000790038a150540c04083c024400c0c1032000072000c0840041c40900395001d0350b11003403060802421964090012410042c54180c100920385a03841290704080004943c90101101c0c50042071461049011041d0040101c0000704801c0c0484070f404007104080159902c0c540519003812401d952080d1046051552000c0951a038207010754040c0040300c0c003040c00c6d141030014960004080317070010352007558040d8000803500c510000a10036200959404c4070303902d00c51038003000811070002c20a00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 761649541 1250 761648291 761648309
    0x3050f0604260d0608011b050a02100203090102040b030108030a030507020703150518120a260f040510093008010915050301020d0e0607090b030f0a0b031c0e040e0304 73
    0x12001c40c42c1c007a0000c55074869815402403050369a64070301d5900810080c0c00c0c80380100403003664004000c0c45042103501810569000300444034600d13120300000e51001c2c0c01b140c01507508100018413026640301450013003415001954940c01d9504014003550801001c4008540003008207000003040c8244094403084082c8000400342e80ba094210455450001071103160f1060004c00e10380c40500000600c83d5030b645680d00190010b100304003001c1200c0b00000000d05091110003e200d80c844035034106c0c0e1150040741203074010300e90884504111620b001084d20b00411001d8807116103803450040e00c4002182c200b108901d44100f8500a10002042c09040e8940341c4450f4152140f5039400707039400c082c1c04010021507542c05035000d030b00010500902000d4181c01103000140c11607010b0220017040315816043c07503103555900380c030a503100d600051442e20b031240d80d610082ea1503181000003600c00091f2118410205281d8400585900d04008049106a041034912000c40c0008000d1318101d541c91a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 761650791 1250 761649541 761649593
    0x304050a0f050c04110f030718151e050702150c0c060d0e0601050303070c060e04110d0e01051501120c0c1209050f10081b09040e030403050f0604 64
    0x1280190612501400c0604040d10389110319050082c040395504004800301c4041140c150305402034078030750055801421080c4414000614114000c1254908002004500f001103a483d04000c801c0a0559030341d050000f82816a201e00c0e1589001348a8505521400c00c2420603c0301e5000a840311520f0752002c070f002070049100201d18804210110008800810709a20345040a2002e0010409051790b403040348180c800000311410040202d0318016082500c01900d141400703030640f0004500700e540c42d0050340d036055000c0040c00101c003500600c40c41040100d4040c9480441d907007520b501a151050070050006000c02981c0c000c04103e541c44440c000c0407600d40075510f42503404280b4010003501103040040b40761a196071040e0a8000c1c0d480072102180841c0003401440409040403542c1d001080306140400e00900b10801540311084240c030f031540c90075850402040039a41c0039840410380d54004a004d01c01c03c001032042412042108006101c50316040e281e0103403500704100d100c0c2c298a192 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 761652041 1250 761650791 761650793
    0x4050f0d110303040b070501050a0603020913031b050c01020f030f160c08060c07060e0a02221d0c090a0e03090d05280b0906010b091210110433050304 66
    0x24501075054400d0003815282c40d60390300c1c0d0320040f07264030107007088455500c6c1c0720000311480101e214280070380703801401d902d006a0b10f21140c5580b80c552510203409100342e504049003001e0202024684c4544180e0140c00182402e90019240401880741c504071500144540700c8070381501000d80c0e009948182a0121501040c2443e90840249410001c01406058208002418030700003d00c080c5100304000c000910801a0300f544400812400030342c0701c11180302c62502a1044070502c8401d14000b00f00040c24803c0300881c140d0b040701f0a00d0180140c010000b84000740c03038201d030119440f6107901c01c103000892080030019281d104001545201c1c12a504051040c400304014450701c1c1c082004420600700001030328040b801c460007000300c440703a28075800544114030224249049941c40501941400954400c2198044108903520301d1845848181070900e60203014a291f42c0503c040c0ba030f60307904d04114001050b480e26100007056001a42e59100e41042c049228941034030041c54020303125210707 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 761653291 1250 761652041 761652053
    0x90606180f0b0609010e2b02030601171c1707020f0c0301050103020d06051b0d051006021f0e10020d0c0f0908030702010804020d080a0e1306030203061603020705030a0306050109060504050f0d 84
    0xb4132a00b48507481c1200b00947c981d29021210450228000c42c12a91140c1c0d1f03c035605464031100010003000c0c1d03007081c400c2d041c42440707001405160092034103155400c1c0b408100c41e0101070380304656000041e40560400e81c48018240009040c2c190107030000d002c55030450300810032090030050700600e59a9a01c0000701c41109140c0341100920041002564030408a800100034040944008110140080000070300d035000103207181d142d0000c0c600ba030070412032007039000d00103140071000481d06009180103c42e200079184014030000d0013007080025943c001c4000104040300003000841409094442400f44000020035500c1040d42441c0c030800a50f01c901c0402d11050041c40000c000d10008248489555004a0100175018081d00c2265001c101115070788141c400c64400070350140c01a10200782c00400300b0311101e9040045050251600582e03603184c500c1c40e4000800d02c00041e640700c60511030b03581e00805180052074030b4500301e401c25080100140b44c0074a02050b940c81803420440c42030800c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 761654541 1250 761653291 761653309
    0x100303020a150204170a0308060103051504090203010e0f0f010501060f0c0b0705070210081902130923102909040b150d02040302010e0d0c18090606180f0b0609010e 72
    0x4500170080521a080c0d403c00d95941c120150071004100796200041955101c0d01c202807180c00c2102003148680514020300c00101440b45003a6015500d03500b500c160140700704819034403819000000c2c41f1020345106040c1c01c40c1d4041e045141000707001005c86005030b0340009040794054112442e1034a40d228000190303028400e500c0001c0d0005142d14200000030780002c110703886900002c01800d481110180108128401c45518919508078a4024884204c0c250312046030b218a2003450810507072042c21500e512070003280c04c801c0803982c0d02e02c140106e280c2c080506181085031040c40600c44008455103a0070b000384d88015000796034070840c814643d0f845020040c0c038000b0000d046941c0d507030300e134075a84003035030042c04240e000c11642d42010000c0d00380940002c00494000384000c01060501b0300104064854070000e20182d40c40311200008201c070f40c86000001c4ca0448000c000e80d05408819070f007510242002c038203400c0d00d03184110296485480403208115000d00e0203d9501c006040081c1d0801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 761655791 1250 761654541 761654549
    0x6050108041e150626120a09030614040210020309010203190c02100207060e0102120405100909140114010c03081602010f0e010506150c10021c23100303020a150204 72
    0xa1040042016103503041d484103043c1c402c06000c00120401d50841002d102c01c030172901440750b9008140c0100112070541c0504035401d000d00e07200c0b903401c0c1d907525080165003018003c01107405007441848110700d805a14031000c40d50b580069403d10300000c1c0080d40702d0040c09100c0000c55003031f20907801c280340320343d2528407015401418030841c1000c015000b0340d0f84c503d50003036074042400303420070780301d15070000681c900e000401d55202840c1905000511044070f1a0308082000c1c051b0003d008222050140691000a90a1101a1500c0d85088801403400002001c800d042c480303194a5200130070761080100d41d02c1441c031640083c80c0a010402280106800c540c1459010700d48202107280c030106400560054808403200744c01090140325102d424400c0540082259200010480e400041c60300030301404040805001104941c0d4044201500c280c00701c1a00c05601014065015000030f1250326080080b5a9030381d255241542e6000c0d43c0c80102e9400900000080c0319418000c902039011078000d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 761657041 1250 761655791 761655803
    0x9020d060c02010c1d1509031e0d080705030c0a03111306030605120105011d1e01030f0201080a110403021201200a0f0e0d1104140c040302040f06050108041e 69
    0x418442800a0080c080c04208034009586074011007100f1500d80f44a85d0002002041d0b841c809044003813004072503000d69051900f501900124446158546600f100c40c0e81800700a01048041004000c000d03130401032008040c8142407040c08070800050b030903182640b081c1d05000500d070302c011201c0c030080d0180d9444825001c1d80700b0f10108100358190400011190181c3c1c40c00c20200121110307134244da000340500c4c89a100132103d10000f0802c0318501582190140c0c0200c2c0d0345190200341c0000164090704291703441120441034404550780040181c2e8800c0441e5820840306407017140c172641074441ca1002920803224400807508240081d8401000d00350255910001002e0400c41d0303440b1900000044000701c0d42000c1001c1c1c4982c054000700c103070750074010300c0183d030000c855a076807800803100840150420ba440b10130f0f600c0d0000104185029140d151042502e82d4618810802507072202190391112500b0503204120741d0341c0200c0001d4100d64000f046d20341d10813046506020b050302e0880c000e082 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 761658291 1250 761657041 761657051
    0x150506060f19122c150609130506240a150507030909151806063c080a0b04090503090402030c0f040b0706050f060d030518030a050c04290409020d06 65
    0x40c84550440084101c03d20020040201c050000b56038644000385074252040f001e0310000b84083c0b921f14540743c3d0010303035503125404030380807912060310f0544103c940245440b0803214030030411030303c86c0c070062082c441218111002400c0203615901c600080c0960418040c005c1250010140121050300241126180410140301001d06c0d01d5504082846141c080d003900d40030f0b0700c00c2d00d500790107214207890007038488608401c440f040d50241c4103101c100760858161070380c008803183d034840c0400d0440034120b69504e0804c0d00f07003455500120b4800704000381c03040e803801d0907003000590301106441b80f402003260700603100d689102000c5840d225400b866803148100081c04200c8502202c060103a060040b0001c11040d038402400000540c81554950b521210040d43e14000900c00c1c40207150020040d4880c5103604008000300c1c0c90044c00510072036242d00080c1c0c01c1d2000b81814803d507645c02d0401c44000c0f1000c1e442ca800c0404070170f804402240581d84504075071041d5280c0c100c00200356a80100b04200e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 761659541 1250 761658291 761658311
    0x100e060f031218060301150f0c020301020c3f03040302070f03030215061203070f030329031006151b230601150512041b03150506060f1912 61
    0x8559010102c3c01c0d6100e5108902168141031001c1501c0c140e554051500c1c40f1a21011020345031000703080e050100308408950310000517102070002d422080511001468041c11007040d080780c0c024102d42c04150452442003080030102130039041103c00c07401c1d03624540c0c0ca0303c45003412410051250810380e19211055400010182d000905c240c1e00100541c18180640701c280410458007044910700400364030600040020808030025911241d02c242030000d01c2070541c101c403800c2c02085680021030558015503190300c604087c03080150b41d0b58155400c001e42801d0807070f0583c0307000c50300002004200440c0c00459030007001c281d942c00119042400d80031440499190004c03081d40e4850645001c3c000c4400006041c282c0c60358072200e003441600d0b45820440300c18182140001c009006903401045e0700030940e41e1804a20242014500946090781c80007500c00c12441030b0351010b00a640202e000300141208420366a042d074442082601c25407212580000c012241c0001c0d16a5080710580b0f407691200e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 761660791 1250 761659541 761659573
    0x8150f130501230a03020f09150a1403060a0204150804050f1c0f0c050705011107052e080108030307050c0322210206030f1e090c0f0306100e060f03 65
    0x43d02014650384044441c001c1a0a003d81a4081d02c4000e402c40300030f00c3c03500e03040d282100032035501141c00c10380d00d454900d129000604080240d844102c1d150140c9444801604042c0146540068032000951070700e80303415011480d841000c1d00c000200150b0030041000c000003803005921080d241000c0360107400408602d0b900c810b03071400581e0302103584880013101090003041c00311480d507000005046030030300d40320040d119040003100b44145030007071500200e096a03030503020400300024000c83d400c0900f9254500da0401e04000308030020703c5040e10040108100c00412650700a00d10301e481d0352601d018410076840c2d07004890310030b00322640c03842e021701c224046080001c0496904110042c152005010310310031303800c2d140e240a900b1220400000318030f009604400c9411080f0240070072010780724805499038440c400d40310462150000e0b0459802c41c58210105c00700440120301514240c00c1840000308191306a100b296a481c0740c5170300013002a50f60380ca410060040180980c0c0041c0b9040c480c0c6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 761662041 1250 761660791 761660819
    0x130203010e1006080702100b03151006091a27040e0d080c0f0304021c12090504150b0715060b040f0e0a0903120b0301090c03060f050708150f130501 65
    0xc0c5804402c20300d070010b011031080c100e06009070002d802400c903074001c64400d0400380421060254061007110713003400e1004c0407801e5042c030401090102e0445541130030b40003412200d4035030104440300d00d94001400d84048150480d041c880d0a54045252410380071f03074000c14072400e151900e6115141942d03c0d8640301010030342c0e808a40c2c807070b660800941d0341c0c9008402103021300250001003020501c001401800c01d20300352449109050400c60002d013556a4144c00d0800c4003424500103030491004005a0a190050320005007898482c41d50403400c0c00568901030081d130303a01612004500000804a195591089014145071420559110f485801403000c03500310b4071840124103040400a0010b400070b104d01034070b07107505599041e0156240242d01001c0c040d280503095041d540d64450b40000b5861540c000700442c072545021600d450a078030510120342d801030001c0184001a0204034900504015881c215502203c0e40048030841c1c0d03000c02e8000d6460007200314910b103440004210603100000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 761663291 1250 761662041 761662051
    0x150a0f02190e04050114010507051203180d0c0b04030507020f06190908070b071b050d06090201021009030e0607030302222102060316030228091403100506130203010e 73
    0x1e10702c2004403000c10320048403001d01c14000c00f032080c0014800f82d9032041c0000c08403e4001c100310380802500e402c28100ca039205840101030fa894103d6101d20301d42e03080c815003940134024106030303420807070607103980c0b501510080004040080c006410b004541c1c54106041751150081e1003e61581c5032015190352220a081e04000400e0028a001802082c000b40080c2940c90b40b964141c2090b01660721804241c0c90703c0d41040c142c0c0707281c00b004242900d403a042c92121500914003c10301c0e0040740006800c1075550b4800303c03c01070608040304c020a4020b130f820202d00801755101507aa4049003402c80003070040e0b010140258500101c01c20f10b05101c98046004c1c0e5906c2690414401c181245407082002c0f0300b400250405400c0c40001c04807088109446040017450401600c1c1000c030302c00c4d0310107602c141040c841e0012401e1041c03401c4503612541000c0a030450360b450354081c00c40440013a50720303e48084c0b10b0134042d490303800080c51074841030b03c0300001c83d0000d1401c0d5140e50b112440d81c1d03880300c01120 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 761664541 1250 761663291 761663297
    0x5090f190b0a2717190302030901090b0c0a0210110601030807060e070e061c1b030501050714071709090406270b1b13170601090e150a0f0219 62
    0x460085450244110b030040c1c81c54101003007000d45000700031300029907142000e0840e8024600d0300d025101a80c0d215800882c4654051541c441014001500d20201038002050050090103014a401800540405101d40465000e5088050044100c400d842e04811f90140740c040e95000104000800000c1c05409202c0c050a10100040c07515140c0d03a090548140b000035a40c00012800c207040c042000500c920040f00c03c40d00c8003595417a84440d0030b41c03800c00502c0c0001020803c10900000f0300c0303165040606440c0c50746110030001114043c5d4020313001c02508505000d1a516030140006c411500e149001074808030507407405041400042951400a9803041114640c0003a0f000b40305c0000032000303078442c6090840f9161461807020113070410b080781c07240900800800000001c0001c5030030003001d4403900c0c80c0f86081008503860901006070300c04c480c0d16003041460b19000c1da0215001205030b139001401400b56070349005007000313405c0c400ea0304091144001004031a05d4000c001007210a1000c0e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 761665791 1250 761664541 761664557
    0x70804150c02070306140f0c0c0309041803110d050706020d0e0d05130803040302130f09170d060803120712180f111504060507030e0a08060402100201090305090f190b0a 74
    0x684a01d10403036048032403102e41e039a008006060b2340c0206024003900443d0300100ea0518400e203001c9400c8a1700310380c903860740c40a426081c40c10590712600440d140c640c680b024001b04801a00040c1c601d01407a00018021134010070580049030083d40301d01c0441941d18129810070130024005070040e4080190348842c01140800494618000822501100d40c05848021003c2043c1d0f00350000340110b003064204c8a40750380820b00411560046030303441210101c12207985038403500292003100c42c66071000c0044e400502c1b03030941100c014014664040c0050034500500c1d00311040c0b10b001030403110580090b00c017642d2343d00c005111402c0721144210303100d5400400b50403101001c10400c207103400340b181042d50003040184003141c41600070380800c03840f904103200300118100c00246010102c1d00a203610340e0003002007005529100454032202c1d012400204100c441c581c034000c0c220302c1000c0310103000d020603c0d003001250301d4915000c00100075100007030201980311001152035900101c0985c0000345a4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 761667041 1250 761665791 761665811
    0xb04021e070b01290c011404061b02012304140d08040605010b0c07210b01080c0414040305070f02150705010b090610120504020402070803130201020d0e0306070804150c02070306 78
    0x11443c1c030311004c03141c101d004001c48031940600780f150b4810101c2144654a46401125000300e01e0340440c0120311404c1c0c04a05540d81204511401d01c1e425006070441e81060001d6401071804100c4401009410002c80000d0341c45042c4403080400815400c03101d4031a03048100768240e409100c041c09140710340000c0c0203690340d0b01c0d0703070705107134050f004c2c0c000d2050304480401c00690342c15115990100b00da9040d83e440c0c181d040d481f9210b2076803099100c0744640c3c022207003c404a1510b40304086054485070303560b40741c0c0e0a00b500c00602a0190040003020f0540003c455001d65030342e103140740014004010780c45d40d6201d113031901d14080c03c10044040c0c0102c06202c00b00c1c1c52440c0c40d40709038034820303107641e130707a180070b6192201107405071001620598116508000f0040800c4007100110f2241c005150704203460342151000a2800c003054040c5000c00c00c1d08100c802c029a004181d294004c007080c645440c02d5203a038104541c3e00c208407650103031000e140151058075140c02042107401c4a000c0d6100300905455 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 761668291 1250 761667041 761667059
    0x131a030604030c03170411040509190c090c0504120602070305040e162a08031306090c080606090424150f03050c03070602070e15030105012d06050d0b04021e070b01 72
    0xd41d00107244e200b01f240310200500b000e41c4540d922050f100202c5100e81c1804106440f80b942030401681c000d01540428042e07540107000d1504009404d20300700c1d1404e4a8501c0c4052001c20300c0d20010400b58000401d01c080c548580155000ba000b901d840703d0060030000983c2c0b24000d04a01ea030404103e0305c00440081c1c101510010304000050306c241c03c1040c001eaa10400a0f600060084003900c94820303895010442d14882e030b00516100d503005804030f41c00d0111461400000400d080c0c410807070082000b0004441820210043e4240c04041c550700081307085490241202c00400040720009840002e00b03058420100ca0480b40a8415900e5110242082c1510391031303280100300140c4c1c00941e04001c003580403852075a00c0503411080b00703030301d41c40f820019095520a03404100004c2c0451b86100c0740c00b040c0000c1085800c2d060800d68410b03498900c02405902541c0c0361400e01d69500d400000c001d4442d41c0407210f1801003d001400a82e080c03000c0c1480d15084001c2c00e98108943c0c0d8000301c1c11040c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 761669541 1250 761668291 761668337
    0xe040c0809061611070608180102180d0f0b0408041514090f01050c0609010f1a0a050112020c150f09060f0f19050703060303110c131a030604030c03 65
    0x100090160a66585981082880b2003041e5190410003044c0c10013210031003410b024503009031802d40d4801260341000300d8080c1480c031030040e49072020391040140703209916906816298000013510040c20300f0f062400d11002c40c20300041d000d01000780070070822013041800c80043c01500c40302181169240405c4008031180c00020340d0304070350403004100c444ad46280862003001c0c41c1005140aa00d0043d04501d410304241082c0c6110313520717a4652001e1303550100d5a014461800710b0354580740d20f41c010702c000003490318901f0f4402c0505000401001000100e565012260203d29040460b01c40004d251203608a00004031103045030105c5113004601a00d4010030f1260061601c5000600c6039119030800b030713a40c004060019240d40203098882100380d0000d000300ca11540b11520001b030f03503a2550401a0201781d0881030203a42e600122094081c0740d850201d031096051280d040041c80d002000460413108811182c0554141326110810040642c0305a440d06000d100e80d454a40072030420003001c3c4022 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 761670791 1250 761669541 761669551
    0xc01020f0114010506070c150314010b0f07060e03040911040305060a0902090c03090c040f050f06061e0f0d0207121b0b010b0307022b110705010c020d080d05070e040c08 74
    0x80b8550010492480c0070000b034030780741e070160046490b0326a032448840358030712002005401103034541e549286d014401020050040008184551801d0441804854284200b210080c001035450006200359801041900c019001c4ca800070030995407040c024004a42161108841c20700c50000001d005c1e4516000e007039001903014195100a807540400c89200b034200900700e000c0c0e07201e808840e129903642c0d40aa090b503c075152000103680c0c00c08403104800354030300810717132400751710300304030a140491851100d0068421802c04498032135101e02500e40003441000036403c1c00b1400407410006001d5105078032152450a91184d842e0580c812a01000e070010b070210140c0a03140110041292681d04e070010342c0e01045a2043c0d4424175455002c19400240d4951800c0d1225035500040c00c403a030700845191640d103400402866440d141c0000205502d01d0510000c1c0140c41d40b4909034104401b40b003e4078007002c4c03141e0060110b0300d80050000c107043c01c1914803621031800d14901c03110301c0740960b014500070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 761672041 1250 761670791 761670821
    0x1a0a050a0b0a05090901150f08070e01030908070c030309060908070f18020913050108010b0a230312040806061807080f1009020c031908070c02041a120c01020f01 71
    0x15180001034495500701c0d9070b102d01031001c10410b10f00c0f15528040c2007406491704049030021081e40030b50040114040c2022401442590400d00200d80d8020704c0135016040c003483c002c80d24a5030741ca00114a802080c0c0000c00c614400c0e1004410103401c1705100064500c03d554800c0f01b6642e518906540d40082c0c80f072198113035030b01c200c248a207050014800810703480883e000746c90000c0c0200400e00c40f034000c209501c03000380e0360001807050980138010299000c2080350b11920241c1080b00120486032601c0d8992004d09046841c1c82c40c51300c06202401003200001300b001d17201e80c4d4544030346442e03042c1140c2081c4a1019011400030207000b91200d00d02510050703456812a41d40c201000c0c2017004003400c140c48044005100041c0341d0315900080142e2003100f0080c54851080c0d44103c6000500381c403040c01440b0200c0304012201fa0700c11420001503030121008980882d000700c1c90710215524a0f076054212000b040c135080c04010000d00e0070309426080e4212001d01c005102c1450880300c08504007484 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 761673291 1250 761672041 761672059
    0x7050d0810180612210513170f0d02060709090207080306090c040918151404110a03170c07060509100309020f09071205100b07020909070305060a1a0a05 67
    0x16201d5016101510b59200b90300040c0c9540c98580202c502d12080c4021204068407010b02d2440b0b00d0790200a44102035a400d10a04040420360134010598445c024140081d43c020340419140804009201200f02c40307200313840c1c2040112000940340c8008441603070214242d00b0000030710b035419100316081c0503040382d072031800c640301d400400418100c06455503407402e074144004146041d0030b01c80e01e08619803070f11358101da20005141011a019a164010112a02e055800d4080c0ba0411740b29a600507881801030780c0a43c1c0c101d000452004c0b0a800c040c0c1221008400140c1108200006215940800e0304662103d50349840442d502d104031048242c0285014006c510128002c0e0006054148000c0008045504002c007040d8100070840d000310000c0c0302d0040c8a00d055071284916030708101c0c400c080004050800d030034010342d4030649900a02445046001941d050307014056600a142d1010688040741020702210300588100745d00e038000c0300701c1494a180079203015803c8400312100034042c003c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 761674541 1250 761673291 761673299
    0x6140f04110d0c06020312061002070e0a0906090b09060a09050726060f220201022d10020903010f090b06040e0f060106020709060909020f0f010e031207050d0810 71
    0xa00001c8142110703410103060400a00000c4080000b9800b409041e4000d40d1110f01c040c900456003400600300500500780c40001024050b0701007180f034140d0b1641a01c1845070344904400d14000c200085016101c03600c1c1030308200401c5001c452907800348500d001201c07502c0c0c42c5d030411682103800588000f440d0764000c40003081004911454a0144c08920005143c0111484552410000c04681340f4150002000801c404150041e40b0300c100c0e9980f40e40c24848a51181e800030b991032245c01c3c3e4000d0012092044054115481d00c9522070703c83d010f03070946008c060580310321b02c0a900a030100390711a50030801c001040c1c400c9032240b82e03d03558104007080ca0507210b8200f404018104a02000071a018511802c44081f4003088424020b2100382d0040654601e800d80c01c40448407150804110107003040f9840c0f026907590710780001e0f0800100c0b0030358900343c02000180d801c0749505501c0d940500844010b404404400c0010300f40c1280a001601c0e03466070340100881d041081101c48240a5090640c148 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 761675791 1250 761674541 761674553
    0xf030106080730021303060b01080907151b05160e09030a0203070b090a021f1706010c021306120b0a0c1e1b02120105090106081605060904060902070f06140f04 70
    0x204403c54040f100515000214424030000e18041d0800e8506644444d04586607584c0414425401481c0c0005172003090304150105041c0c10605444d001088103514964560381c083c1981c02001d20360010131101c41d600c80c18030381c111310714a51052918011045000411b07003580402210040c41840d40590315205080ea1030300c3e694600903080da42c1e10304c240304d200001626121070f201c403a00c7c484130075012840d8403000000c00c10655180340d40c800c41d050700c0c00d001c0d00f41d81240c02d2056060341201c0c0542a01301c4004464000e0903d68018049600d0014242003480310410354240038180c2c18105006140a048064a08519840b4150034542c00000c611031041d22500c0c074000a81d00ba240020280019500000e002444500741801e41342d43d03e606210209400b48200d100421090028225031100c1180030490301e1f2003131141502400c00000c55400950b200d912000240a04010441d22050242000107035140300107001c550039407800180d0014612071203221480740210b010103588560703031542c0312 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 761677041 1250 761675791 761675867
    0x9011e020f160609060903110d03020703080105060a03110d0c0212030f061c02150d050a0c120f0e060a0b10020a0209180307120302030a0605010504052b080f0301060807 74
    0x3510104d035540300c030034001084d601482034072500079512601034550b542c010f54102001c00790198141441007100000080d08441074504542e81107403003d80301ea005100980160515103c1407020351400104500d181d40705600642c10344013075a00b11400203130b040c0c000c03144910040c0ea488a800c402c0c1c0001660600e02100615849207100c10005141a182d03408101554201c1d151802c1d8003c0105d00d43c0300081007403060303c4d4400290759051004002907030303001d81401ca00074499a0015124061440940d010380c10842200300380c4000c445a80c40d0000d5060010711081c91071034401c501c001c40002209100003440d401154004003000d400362295038505246d080e000005014901003801766002180c0507003128090350345546c0740544d80b40b0700750543c0c05c100c81c401e0f004a818880107100030700c495100d0303c00c20035140b074020000404c10546450703401049203254200528501c000258200e03011000300107181200c0154951134141c0e1203421040c0c440c00c00b541032980007440a00316480c0342c403161a0403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 761678291 1250 761677041 761677043
    0x182304091b0602010b040b030115060305060102030c1603031e020601090b130f06030c0b070b0a0f140403020106030302070e061018050607060501050a0918030f02070e09011e020f16 79
    0x1018219054a0714144400c40558401d0002d40d64441030b000c035038141800b41da00c210104400130000c900a070500760110350780b140200802c040d6100c0001e0344c0c1c2d134000c204588840e01030404440420015684582e0883e0984c01300b00e001600703030518076070242c2080c052100e9a02003500a003007141c1c00c0070581001000c480040301c0e400246502e031800c801c0282d1050741d0700807407a80800700f049411400e2403100342100781e00002440d20108403400c0412024100380d0b070007100e00c0ca400700b010007169046c84043e01c1221042c05403044c00d4401d000c10503405520442c200d900c29025282169540c00c601c80030380c001103d2064001500c42d010400c041d200345004c23551001900c50b1428074945450114006070003009088801583d207400502840c0303440b00f03401000b00903a04041c00501580c0c1c1a0b103540500742c0750020181305001c0d095a0450b070003882458046c00010b10320900318a05161240d01902c14920750740c00b800d9a0000f2514200d41500840c0c40c410f01402c0c642e45010300c081581c20320000c50b004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 761679541 1250 761678291 761678303
    0x6090c02030309060f10150201330e06030102070b0915090c0607080703110f0d08090a0201090308030c0d020f070201170c0a0e1314011508040b010302040b1f18230409 73
    0xc0204280d0104440071030190026230000948144e540544104580c481d007068084a40030201d1041030380340814180e054400c0e0150100d510b859401c0804d029009903000104600000000c1004900e00042c1e401c103078030712580300c1030b030f5545a200d003864031184840c0880760081d204021501c00306440340c0042074a2031080c0f8020a9102c90742128908140d600c1120100d0381e0890b04c1600d54040d406a0499007220030740015001041084d4000b03810a90342d44801854404003000040409000d44103403045584e0001d0155074235035102c0307005010365011000880c042600380c091080b80e0210181085d105920401686103000d000300d0080d210000106040d036800320588448030201d2449000d1081d105032a00c0480d680c95060030036015003c034800f20558100505181008007188072411100c0c1143e4050310700140e400044e23808a451881516040e5500c60020701411440d554409180944880c0c0030b81c49140b015180c84c0c8407071428014a0011407003c0c80304440034105d1074164082d0f0300a5100d11 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 761680791 1250 761679541 761679571
    0x10504060f020c030609030a26041e05060a0902040f02030906043f03200d090c0e1f05030a0b18030c0610060f1704030c0305091306090c02030309060f 66
    0x6000038a40041280d0301c00030b6030400b090002300aa08040d0750710248030b540c219850510090344801c3c40c0580020300180c20605020951034013280c0c13490f03602c41071a0b00305094440c68a4441c00e1200a09040c45089024900c3d205030480c2d040114800d4900515040c4050200c9484a8a441d202100e6403642003041c1c946000c032081d0300c0e1040054440c40d50500ca68141e000c408a90009000c542c2c0550900706075020100144c10160b460700101c4600c91030301800017501144906142402c0c181d51340166101004c0780c0140400d8000e540c036510402c05440e00c02040307940d20b41b011b0644804410a00a01c2209484040f90401e030002d20340b83c1e440f0740b00c4d1003241d042540020440e454400240c898200784880c0705024003155900400c41c42507500c050902202e4000e4010005030080302c0188043c04000b44405054201071190085038052580200520f420131440082e580040c5054420000004e00d03241c0b14510b15800403082c0e911920760a00a4449981d400760401c02c00100200b01c1101c4510310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 761682041 1250 761680791 761680813
    0xd0f020f06130303080f060901030c270207060207020307081207020d02060903160603050f071202031906060201060f0914010302011b1b0303080601030e060c070503040302031506091005010504060f02 87
    0x20b0b12a440198040d0b0703116440d0303081c01d42c40c00348a000043d2586005621841c01403000c901c14400440482d1030202800d038482c007102c80042e055008110700483c0280c00090b628041c0134864000d0b0600c9802101540c944981d100c00f481e6607504c0c00e911242c0414424090440540350030311142c1034090025041030310700700049002a0800d6414035000c40d002030340300020307c03007580c1c035101e000d038008807540008000b410310080c00740071040e08042042400750000b0001d425118891003203084080c94100502c1029112034019020b8580c9010f1803c1100d102680014038841600410340d07a2004c038203520340c1f6a42182c00440c0c40406e5151200f081444580b00c40c00051001c0010200380410300b000c010a00e8114940203240c02409031070b42e0704050900068515141020541d0342c0c01040201e6100e0390340d0031600d4031070f007540520382c8040c2d85070040380f106043c01404551043d10545040303450b0320b6155030705841e244280e40036005a50001c2c80070300003402454050010001c000740c032401281c181d8655 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 761683291 1250 761682041 761682067
    0x302071a01032d0f111306080d1e0e0114040f03020a080f070e180a11030c010507050303070e0a0305030a1101110a020a12140c010e0c0d0f020f06 64
    0xd0300e0840e0503480340c00300400500c041e07a0646451810140003102501a04814510a03a07100040c00b5040081d10f110103401c01c0300a0395548902d1001901404100040001c44001041070b40310796145802081e2500c8101032096000001c5402c0c0c0e5514407520344505a030846401c40c080414505101005100088010148015000800303140303090654050a600c1071040003801c0d9448a022a032000c42c071080f4012010441c0400c1e1902180212056030b81d41c0036098040060100c2102d450003030025901c18494500600d9030303142416000c80d00d07181d4410004540c0c61003004400b80c25038100b80041181d0714820190b00403421030041c0040c0300e040c0c481d151309045603c110780350780104d0001200481e51071300a0081c02004d4601c40261420f0940c1d4040180d03c4000c4d0b510b006144000d801d090020150103942c1400c13210146403c011b843d00c0c5501c81c0c1c14000d040352070070020b042c820700010700030718906100745220565000b18004010101c40e824400e9650318140d119512850506c801c00d1a201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 761684541 1250 761683291 761683313
    0x2040503061018020301060e10051c06051e0307030b070309080414030c1921060510030c0509040809240a171b1b070503070e0f1024030207 61
    0xc1e80c2d001012a051510800201c0c3e5241161414500d0f40140010004a50805c0e203208402c04140e600315a00c0708450800c81f61445a0b00c001001d42a140e01d10814882aa03403080703041e07030001c0d2400c03010680c044441c24480c000c8003d1203075150307120080c140002040c40442a8000000b41400320b82a259540e035a145600250000d03011004541600ca0b00b9180401c10f25240b050140c032046103219500c80059038140c014000c40d060360380780c0050813580e15007108000754004d4002204004905200d600380720759441901c13050749c12010140c0c0110785032403e001c640c0c1c05a40d000f040c0519250601d0144520071000000000980c10007844001e62010741ca03000780194807155503508000340f0b400322401c0e6180340c050500c2c40c035600c0c424a81e00040490400706c840c5d40c550146074500f0105980c3d0b9042c0340c811103030000b503018001ca10000407006d07501a012402070394a40b501c40059543d10244a80e80060b92007034414850001c0d55090003400400240c0c2426034081c580980f400c13040c0d03150104481 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 761685791 1250 761684541 761684551
    0xa02120d050708060a14040e030f1204051203060603010e041401090b0703062102010302030c0d0603080304060506190512070f1203111f02092706121f020d0204050306 73
    0x40d880c1e03020400380a81c84181030398860022110010fa107414042c45122581d08010707000d008560b03603807110b441c1e64410002e1f11404941140120f5581c44144824009540240c0e8211142d01c40d030088403428545140903644900005400d40d411686405910f03802c00c4009003040d01c604140d87c5c07a0000c1d0110a0040400190098074400810300303043c400102207a204d5404010034212844443c809100c1510380700703000940920b0003503180d8450640009503849429058450039250200010401984002542c0328901807102041035076512000e1007440d4035014102000c40340c180b1010701852400344404002c51480d54112101141c44050f450f100d80c4154211045201d148101c3d5010142d1002030400400c0c84a009041c0040200302c0e144180440140c035021641e0f0003255005064031031604d00c054201604000e400182c0c400358030a07000100640b29980100c8841e01c00ca0110f40c4d00180b4005104c195048202e12030074400c0c40000250421300c02219280c0d000c220000c0d480d9800c010183c024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 761687041 1250 761685791 761685817
    0x504060e04022125050702010815040b061603121b030905120c0105040b011e060c030201092f1c060510030218100e0f0106030f24210807080a0212 64
    0x52148900701540c100071520513004001c010482c80700141d90002107250080001c0044144900705940020f000d4503881300711542000f00803c231050400e0071482070051140c080e44459400c2e0818128007825101200d24507c0e0b0031880b070b040700f1090f9110364050707030645020b9001e440012070040c001c0d05031948146c0160b1703201da440700c2c184002d0001044c43c1500405080c0704444200c89000d02c0242c00341128070514080c06042018132003418002c0d0002018103074004030054150400c20045c2c0841821040c052101804c0078001d201607050080c0e225800d64428500000d003000c181e5107000180400500700762036102d0a00b00040180c0f252014444019817842c8460310383d151054000503403407015072100c80c500d601c40003031109000e420740709103040d41c03501d160200b40d183c03009a0480c05040004599200203040c031b44072503810300103482c105c000e40e0666041203810030f0b030941003080a0108958050b0070284100304620010f0283c0c0001c0c1040501801622a40701c440103041c0d143e81c002141c640b842c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 761688291 1250 761687041 761687071
    0x92701090308181504050f12120a0902030705210106060801150801060e1c17030604110301031a1012050c0a0e0702121308030310030201030b010504060e040221 70
    0x10560000c41481d408007440d03a503000207414010800e50749083c14540700c9004d0b01c41202240920401340004e242e100703103000488030301481c0c0c1941001550b010107500c004405003c800b240c0060224000c500c400c0780c00400038a0242c0c100020405483c4c0701c822040c9141c080070502d44002d40007801510000e0000f900c4202c069031400d01c061000051080429042228050040c01034642000d41c40311f10080648040017820031a10401c051020700c144003800c0c14060440321000018120000d41c45400c0903a400d00c00c01480748090a1030340000e00000b460b03038403da0300c0d11100c1c1c88461070182d4012103c44403150020b0303448061980801c030900042d591500012841001c508045410500400305028540d410340b0b00104000d403101c05030b0904800c80180068000c021260305441d040140c0341590580b42d5134105805406041610340c0f0013240440c4c24410340e81c82c55030244041c2c5007118456101e50701800d885000b0040203600220042c0441c842c03218224850310302000780c1c140300d80a03c0b19503400b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 761689541 1250 761688291 761688293
    0x525120206012112030b0915030d02030705060114210703060b0a0e13020a050a17070f210c0f06210605010f081302061c06060203070309030209270109 66
    0x700705101600074144010501041c507480440001003460001c0d0040e810300038039800000102d010780f02070010103034404281800c0c001c172003140714404055414118100d446500b080042030f03031a40940000945550402c00040045103000003458400140042441c247d41003101200000e00c400800d45180342c0d4080783c404e208200961141801c200c00845800c422249401c1c190080c2010040000030030400c050503590440d107452041c2030103488014480c1440d2511a000320400203110b855200c5c09201e95600041c1c04042d01030040b040d0f44000c681c10102d403c0300304040c020003541d003001b121a4401c07042e00040490b00d001d06040a0700305ea03a940c140c034201c0c030b4240201d000c90103102000b42034a046010082e60303800001e4204004121f0030041015a200c200d4140346d807a0920001e5000100011146141a040d00d00f0f10041c503103076102081102e4a869003240d40340102071008011a18050b0184054074210f0740b1a580608440c4098291515640032842c583d00010030341c0100303a4417030703240d08 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 761690647 1106 761689541 761689543
    0x30c160501020c0309090a0204060c0f14010507050a020c0405070504050409050c03010e250f09020304060f11040602010605041104120317040b070305130b0705251202 73
    0x15111841c1a40030f42e104d0388501011807150f20341d60000781c50301500f40300752403c1e55402d94921103002c40076a507140702a648100280e90294445c04c41010003102405181c0c030500007980e43e1626a510044046e14041e540d4841502c1141444100720b07450f640941604c04a803000c64021402c0c4501d400c004d800c00c44440f08164040d420101418180000000d080c0078402455240c1045000d15614809034005070340241c0102840c000004c00c00c002e200e8015681140c000e101c0001d854410090b8002210800000000d12001c00300d020448a5028401d00004080c280e0342030002c041e0241110b50300c2d01c40c501034181940042d26540003410310031640034020b015a444105114109814660380694045032542c0020381400f002510440750626a4500642c0c09040103032103403140c1034140c0d010f4118117240d4100d6081610003c030b01400d403c20b40044c49008a0304000301408c079010007 = true := by decide +kernel

theorem cover : BRFrame.Cov 761510791 761690647 := by
  have h0 := BRFrame.cov_init 761510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 761510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 761510791 ≤ n) (h2 : n < 761690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
