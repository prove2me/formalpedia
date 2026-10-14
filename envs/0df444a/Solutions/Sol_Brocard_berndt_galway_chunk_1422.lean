-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:54:30.125034+00:00
-- url     : https://prove2.me/submissions/bba028ad-84c3-4d45-a46d-9529cd1566d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 255575539 ≤ n < 255755395 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 255576789 1250 255575539 255575561
    0x10b0a0c05030909010b120105030102070b22290f0c070b04060603060218100c150905070509010f05090106050711100e040504050f0f0f12090105040b030108100e0a050607080a 77
    0x2138a0400001c1a00c043c80141030041e100c4a92824980c0e00c6800349401c03806280001b9000088003004209408401d00302030040308014415000000a140c95414104180303010201c080103004503041e242d6010032003041d4020210402160171410814a00d1501c5d018000028000400c01d10200d810020f490f03000e80300455200300d0039500e401c1401050030440c0316003505140541407482000254503c5950480c106607404074101451015015608005020400003100c40e4411a2004074107981c5000c0303114000c2580300c030615121f908041c14003100b00c1d01070b4020301c02c3c4107003030104c000040c100b0a11070003112010b03100c50030b644060302c8003201c0d00c940d80c50141d078202d4074010038042440008031303590000c00c00700b00450710328804070826a035403802d8500944201d43c000c8141c54090b40c442600a090302c0c1014504541420740b51540400c8951080e8443c3c0e03c02e6101000d0601003a406008441204107194098540800031340c5800703884440003051f95007000f40010001d90001a6584940c05040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 255578039 1250 255576789 255576799
    0x81e070e04030c03030c0c03080a0b04022101091b05040303030209060f0d0b1c1104050a02070c0806150402190c05070b0a0c02090901061211030309100c03030c0305010b0a0c050309 79
    0x4207190901900840718404240c000a007890703404550540680100024141c0c1562442035950750088000c000745030301d200c0558800d400b00220041400c6500c0f404c9014801b80307a0b980d000e54540560382044801102115075282440c00d2464100da42080590741160381506000da524401d403400502d083c4502003010b50300d0200810340c2c420300192940032504036001070320207601981e51a5400c08003190168001009418540030030991824540c0040d900a040c1d5403000d401c00115507600480401a07070061512a480f01041104c001c02c02e4002e14842002580c0461031305c01e940c9030144410166480e00307814032140c24999410084100305250003003401101c803589032080142c000b400b841b4800c2069100b00310400c007040d5808018882c8808075161141405088002580d80340701005c55142c010b51b0502040c00001e4150b104e06030b002e54503807a5a610748014006a19010b4125264540b0410400d4500001480200c410700c00322646c1039024141071607414060b2400c00c1c030f5403103403000b855041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 255579289 1250 255578039 255578041
    0xf1515060f030403030e030c070b1336020a0c030305040c170309150a08060d030905130509060a0c02060117070803121b03190513020405090c040b0901081e070e 70
    0x4001807801a501030b5209030703802e200c03519484442c83d9890103aa002c2508940001400700320306441c4400030401c1c00890b1014141c01c80e41e681145510701041e4040e900b16071001303a5508582d81c0518102c69514020001c118248040d1800081028001a00c02024076030794601240c00c1c041284668002400c4080c5002c500311124050113803281c000840b8140036107281400512007020200070307246400306650361009590782e00810085613040d03903a410303401d12a5441c40030580f0b031200c2922101070000b611000c180d50501d000a00e107480030081c0603458440c5810040c614240d40485c1490460f080c000c000d110340c40b9141005d5003016010f41c85a0b0951000085144c0722141002c0702922400036000000584903490b000c20742144001c41da00c281640850074a00e008815a032300041e08000030f44201c4410020a50220381155010384102c0481d034040b0700203844a19081c000c0c0a900002079401580551502d8549583c07100100e0541c21203c400306480415100e0130455400101703880c1c000340701a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 255580539 1250 255579289 255579307
    0x40e030c0a0c06020f0f25090f0b1c0b04060209011b0c060e09070819020d09050109150c0504090506011b030f02060a0209010f0f020709021b07080f151506 68
    0x603030040f88102c00160103951502074081d0000f09503010508144005805180b00c000f4035000d9111184004152980039102c02044c541c50510440454071038131400021015000c40070028a00d090380da06002907030b2181181c40014414000c02074000c7d038407040140c5c845500000688405405a104681601d0151081818030823050283d0040300c0480c2c60301030508060f001480010382003242c10320003061140c3c1c0880c03002c4a07a96141c02481807191030041c1054040183c40707050301c050140070307a4603a44445000042c021a400c0398036a60713081f050304229002904401030110f000f41d100300c4022641d58000120141d02a151000c030a0f41801c10441d4000c2807131401502c0c0e03c40c06c03011200107100360070014100c0c0c5850310072190041d5058503801104210b51104a42c0b07610380c030b0307800700c01c50241200c00079600e1f14900280018442c682c086052605585610714135000c81603005520035409107246010f4604007080000102084090042c41a540d940c00c2d440344d100580003403a081000011503141c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 255581789 1250 255580539 255580553
    0x2100f0e120106090606020303060a0e09033105010e1008190507080a05160c0209040c080304080c120d090302061b191e1104091e0602040e0c070f02040e030c0a 70
    0x1c1d214200405c028103030b1626000c90381c034001141c140d030f0000d1000b1024807201c0b05040c0401c1e482482c01c01164a80403a11040d0500d411000782c16842d0380001101240f413002040c54020b01800081c80c007601d0980070000001d0020507102d041e0307400e101c4614081007042c603d508690703c0c40307064050284800d0400ca5002014940b00f203039802c1000d4501004160583c03503603030280c1c0542c1c825a0350804461303180d408125002001a1044a80c441658000600e812060000d840207107441c6020300281141d0009010348100d05100d1441140c05c5015a00e90081e00000c20717070b069070740694000791600510004150343c03139015007407003445200e0010680720142d400c101c4070100500c02e41d042035a11100300c090034014ac0c40104000c003504001608014241055070001e0681800307860b8095040c5105500e42c0c4503411540000d0300c4980d00010702380401d000550311542c2003408100c6081c58865a40c80d2151281d03107141c0001d1040c1e4441a4a180c600c40403c240c60010610100740c0c1d40f60001490002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 255583039 1250 255581789 255581801
    0xf110609061807080a08070302190506010b03071215060e030303010810050c070503070c230306060103020d090609080702090c0301080318150a03090b0a0c0804020f041d0304030b011202100f0e1201 86
    0x600510455505283c0262b92118540f00c444d4080c0050090b42d003000c0e034081640c3c000808101c204450203100703404400f039600541c200340009031071200316032f03041c00c900402030310313108003594000d920400c01003108040000304000d56403011400000c0548500304444810301c1062400ba1041c4800300b41d40040c448202d052204a502104031511812141021542c000701e000510642c190031007030004920754002d80061410f00162070000540480c1d5a036140100d0708031140a90310300c1c00103d9120b0842c20100390705a001b07440400081d00399890220915500d205001c0074401d90114401540040e446e54007990810b180e0b8001c2c81078a40e654110014014512070342c0680300d41d07848402080740741e5624410342c8140c0c0215aa005440c0e5200d800f44114280c1c9420306640142e83d52101c1500c3c03500403101c0041c10401c140245980e90b1450418035040c1d030044e0054103100250710316020050740e9801c60750f10810820300700801c0001c194074090360728003804941140c200e46450003281e0800010f610003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 255584289 1250 255583039 255583043
    0x90a0e150a0b0a0c230102030103060e01090b0c210132030a0209130b0f1608012711210f06011b0804150f110609061807080a0807 57
    0x4121205503403801c20000003028440e501d0240810880094661312403540044014000c000d00620131010950765400a202c078044880c840c0d5000c0010f00400106010340343d5a0f070401e000038803142d44561100032000c48007070200d052200c40040c009400d40c4000400001e002c1c08a41109510341c2d480d004482c02002003502800300409021480b02501c0c07941e12880d5400101500510031030209509108001c0c0001e080c860810156010322000250032108142c801c60480c0c0c2261601c2c2480101d68020556207500da03000c0c4451000140302025980a050106800001c8404601d02c0f00c0308400f4010400c041c0c403280c40000020b101002d0012218100c60b0441a480b50040c0543d1240c0701c1c03681c0300b082910218006059084d502e01c40f820060201440d0714042c02140b40780c20307510000750040382c56260816000c906000c2d1a178030b0854210707a12540404141c0090911441c248013502d4a481c0010410809106d584110a00718541000400701402e001e40031207103240524240304500390820482 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 255585539 1250 255584289 255584311
    0x11070b1801090b100302030607090b040b0a020a05010e0d08160f031a03070e06150c030a0320070614010905071718030412120219152c010b0418060c05090a0e 69
    0x456500e03441102b0a50894024082d030703d0a16007008842501603000d0125042144030341c00c50320b40030620a1003000c070070a06071801480707110705144000d03050300c0d0300400e0030783c055001ca03440c900080d41000100303101c0c42aa1a002860042c981d40b0f00158041c001c4042c0d03010b00c40c00c100807406902ca0039460740200c00884030041484c0440b01d07441031600c1031241c1c002c0c0382d030402d0001a00d1140240c00c008601e1100d51780c8901c4595100200441c41c2c0c02074031054034119101c81003582032100b45010300b805850515401e1210385040840a400c030722a4402d08034860181000144500d4020742c01540000c001d001600d5442c0c2d501c01c420002505810800c1e1152840030540ca000540009060068001d0755400c40300c50b2441500d680c03803c07030703000400300c2460b9854644101203030340607094030003070100d1711055031000c44040600e0f00d08480d02c09a0303980c026490120203001c1d66034040c00c1507000039802440842e01801d914800c407118010003801542000031100080b07410f05031081d15078803c0d0410f0603 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 255586789 1250 255585539 255585541
    0x1b0201050901060515131a0a0906090303081906120b0603011529090904080a030f020f0d0b03100e030301031202120a050a0e10110111070b1801090b1003020306 70
    0x401c160803902c20740b01d082c0d0300000c40e16030f00b60340c01490405045103031035603041a0703402c540d03400310041400042c0c403984514280c0000c00c0070f4015000220352000d4042490030b00c80a5043da034001d0060903014080e4400c41d00d90030903103c01d010300e030781142014200c031040303c0011025628000040540584040303210b5401c0064010071242d96110300360840d00400c01254080d0b800e240003001c1d1840b00c0380c0c034031841101040a00c226131a001000d038007507071050030810780c2d1701041d49004046030102c103100510140100500aa080590001d442507071282030b10000d0714484010029250864080c1f02c081901d00f0070300711030445c00b804000f440c120303805980403202002d20b095003240c90308405000400f5010060200c100014880c40c09400c0d4030f4400c1c2802280c0d410150300044503c000795407014005580c0c000c2c0000071600c02c3c01810301c10207100700d4003411311610740d54405c0f5101c001010b010450003a0700a400000c4400d4101140c8a07402254448540c1030050600c00480c0e01400305900070700c9954 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 255588039 1250 255586789 255586801
    0x30b0903030403051911011a03060f09070b130306230c041203050c0c0d060c02070b0c120306010207031505040218092503140c1c15050a020c011b020105 67
    0x44100c82c4600c1d89513032080d2820980c02c810902e1502d007045c4030000c01c00c0a2800700c00d80d03802441541100c117443c814100e030343e010305001c00d07107090390040c1882c002100300c3c024460002400150001910b5614141c41e071100c0000b85241c0600320303540c2c00a02480d0501568000710080e01c03000b5040b941801d800030070700e5550218a104a03106520840c200c03a4911070f25080442d22170005850061070300000e844074032040000040300d032680404c09884c0da6985040111201d40c04010030002801c0d00d013825418a0118050140c4600d4040a11a20b00c01c1c004001500c42e84280021009581e01c40c2081d20754000c03a2010702c0007040100c5040340684031904091100c00b4078401007500c1004a2002002c441c040e03034420b14030241520380d001126200f110f20100c0052410070010540c0004c02c07000303010319440300c3c081000c1901460441900d43e564000054082900202c0e030b0044601d03103a2010a00362154104e01009100382010b46000b035182c00c4407890344900c9400c50b507800103e42d50003444291100303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 255589289 1250 255588039 255588043
    0x50a05040507050a0e0109090606080319020606010e060d09061503050106080105010b03190b12030c060a0c0503070f0f0e100e03101a130209030712030801080703030e040b0f040e07030b09 82
    0xe005240300301789004010061f030300c01031700002102480741d20081171642c0d44005082ca5508070b5928424040307499100360010750360411149038402c04c2480c000300d9500403032010404a101382c8541005a82d1602945414040207400500360202d1080c003041e0115a00d0904134009e05a074002c01800354288400010b111002c0d6081d02d00900221946018002490000c14010120608155004242100801880003040c03014004044020001c0c1c20f40f864055495001c88010005140038030070140280010107070b01a040401255250500c95038105001d04250b0f0808000c0d081c0c180d011542c1e1004007481c41d4080307503942074010107500300d507001c00204a006041d034860b03048496490342c0c0e010201d035081c50413421000001054800040ca001d0800000c241050702d150030071380210890b5460301c000c00d60701c99969170041020350047c00002c0e0540d44c004201d61401d0124520468036004e070002107a1b5508108042164014000c00001004480e03640e00d80031144070560301d0030030f003c0000d1101d01340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 255590539 1250 255589289 255589309
    0x1c2301091416050a0201110301090b03120708070816020d080c01050603070821120a0207170a080f18010603050c0102070f080316080c01050f0a0b010c050d0e030a0501050a0504050705 80
    0x2c2d042e00003200610b04221640e4000703103489021917480348000c85c50000450000c40c06031001c14000318805140c80c0a0529080691548240074241003056102280141003607440d100e504c4110b00d5540c5c1e40c0701007810101c08400c0c0d0040d40c0705000700c10120401030717064024401c1111a50007031100e580c80104240e2100300c03504c0745100941004ca24240f804695180f19031a00c45d00b000c0d00782c1402c0305450a041016400c484210340d2076800a0182d0038801c042038011a60b041d583d6540307241c22007007503005000d4103014149800301c2c0ca8160200302140c0c002c180c2d8009030189040208040c5aa03800c102c0d6544000c0035071140903006d0500701003008942c074211142034540c808015490000800f105010003100c003402036400d03e9007440100588103080c00f452b0b01602900d0301c41a003a05203040e4400864260300030940c140030055a00000140f80405e209140002900b0040055007070316001c64204030600400900315403a2904010035018207500141c06640190103c61003107488200b0302c03100d0340b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 255591789 1250 255590539 255590551
    0xf050603160e0c0d061701050c1318020d020703030510150903110f1c02030c1c02121227101e02030409050f06090a060b1c23010914 58
    0x3440801c10300c80c035207105060a070840c101c1c2100a1506602c425640308480345a00010781c4407280584c8400c454100340070300354100390074015241c17601620301500c0d101c440d0759100345c060a0401c1400714002841d140d0548081817034100c015540d41e80700307180040090000300d801d2407095450b1103010a01240c4804224050386064685050395411500c991a02e81d5100c17480d26400380d41036003010120785070320001000c070048201c000d00c0d410120388105801d00f4000101c00e030003040280002000b0303c2d4102440b8a10a405841c004190798683c9007440c1044200c6010031148140010b4410394140380e88030780210062584001641382d100d0408100ca07060b030201d005000285920805e82550400d0049604020a40c0c0100c84c03501d0780e10f0a0350002c0e141c08071001c00e040046070040000608081c403425a12604a41017001401e05280180da4540101e0b81441d081c50f0300f500d40e64403c0b140507480b1480d585440c0c0c0101d40241d1100102055a004c240945c205584c10710060000b2800c9005a03207018030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 255593039 1250 255591789 255591823
    0x2101140f01030e0a080406090608070c020f0f0f0405100509130b01151704060c031d030d1d16080f060f0c07050102070b0c18010513052e02010f050603 66
    0xa125000118094010030741c900603240a611505030004907110014401484113231a107007542840c011000e80b0032400141940c00f40a10300912000507505c03030361040070502c4110f0304c41c1303c044407010201e4504c28415000c190020325110038030051103a2104854215502211901c032079079180ea0000701c00001e5250700902c02a0403000500c4421100082440d0308407052810f45031003000340040c04010300b010780d01a00c2c2180c1d1005181072480d458010100850880c0d0f000d01c40c08007004c0e0702d00b0323500c3c400d0351890341a040e9509503160700401580011070f10280000211460280100c0700c04100303e44078451803c40b071140c40700101e1010008603060b881001d5406001c88030303a540140c500b101d07070301c03040c01144e20f9582001694005003d4410490265058030841d6880e005a150014499414030710060f051090034024400700034026019941a100d0569141b280a41c60400c1908007a00f0b8000490041110403004c40c0722603815031001800600c544401d00645e04c0c0d900a06440f50b1100420b0f0000c0c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 255594289 1250 255593039 255593059
    0x4032706030b0310090c090209010c050105040b0604060e0603060a0209010207050301020c0105070f11030702060307110102070f02011209150902010311190e0a030b0604091103011103090f030406052706210114 91
    0x1f07108940c0c060980c00300d06060902c1e041200d030f601c02c1e08651f000c440464082e03101c10700f406160300780340c03040d0f60180c041030208420500b802000250303100b000038003c559040d00001d5542c3d003640709000c00320081801074005d544400c650510a4060942210368000080b50300700c0c101526441610702284082d43e410140d450140305800703020f0941d01c02410002402126500da0004034024401030445130300520400c90807103818400144142400400455401e00b4000d20001086460607084200703409900c0c0040c2c03224440c40103a000d4031035411056040740c80400c14a810840107420802405400c0e81c46041607820300303040101204031400040c001007020000602c45081c60744c0003404040c042c008030600d00815a0000782500c10f440d405018508011040c091200010000d11fa039000c480c030701035410070303082080081007401000803440606085110342140b0301d02d403030710300f01e00000050640e030340d140040702208005e00085600360361040c05000000135401028002c0e0100c00708010264030300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 255595539 1250 255594289 255594299
    0x50601050a050f0f090901030b15030318040917030408030118060605030a0911121b092512140402120d050d0f0b120f060108011404032706030b0310090c 67
    0x4980c0000c41541390040c0c041100480726a5405e0311140214460000201e00b46440a1a0485128070070600c40c00b0341d00620483e0360700003003c070b1101d034000750035100046c0c50001420101c0b8000c12103140014030503000020321043c08070105c000c6051b03c2c03143e118008503688805100c011951980324040008505001050840359680c000018450041e58080603081e0143c0004011b615000154425644440195145005880c481d0242548100d41214141c5006184920303034401224454008072044140d88501901405543d25107403040042045041c41c8405181c40d07070f003403d803400d034407a0b041a41041141e2000040740804195203030350740c40c182661003080d40003401d812102c02032000c5d29041d0031501138480c5403070342d0030000c107002c01401e6244883c9a120b050400603084080e890341002d5400e5100c88075400003a030401e0b4146000d001e80d0044000c01e85080000807201e20f030500d4490070010b030340c030b90682004032980301c00c405031307100f102000e10828100c501c1c1c038100030022042e1210401c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 255596789 1250 255595539 255595567
    0x2070503101e0e030306042007021005071b0311030105041a0c090612010f0e09060619030b1501080a020a080103080d141014090402010e10030605031f050601050a05 72
    0x20240c03040c0690540d003808122a800c20383c0c5000d550411641d002100b000013515103030280701c0e111803640103060404802e00d42141c280348101031f00a80148111405501501d1040007110802a000081c030203050406092480c14801c0e60300c4152507441d200040710340c1c03516043c400c1c1405141d012842d00c130700e00d80e0030100e00f00f404c400800080300b01e541400301d6802615003900a00c250340141c14498441e60500c0224034003100281c1210140c000c001080040d41c0c000090341c9a0440380c225281d03a0822941e540550b415200760f00b0080042d0b40d142c040c00245c0c01400240e03d903000090300c9050f41d650b40c5000c100c00700e00980012100003040d6800400200e04070400504101c0f41400c000301f0084140c0403140301286055442c0790505505800421502c1c4034040c91040c200f030102c991500e181403680000b40880300300700e030561241c20348081d18464030b8000d0b40260002c01014040d01c0a0b0190008590082c02c405e008500010f4240000620b6641c4a0000c44a0401c044d071656820100c0c81d4807050 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 255598039 1250 255596789 255596801
    0x1e01090b0f03160207090603110901140d1106040f060c05330c0c03030f0129090112060510050a1e080f0c040509160e04050709051905090c0a08070207050310 69
    0x43c00e5004041000c0382c000c01900503140070318050401d55001e8014503082c00b00179141603001c4e120f05e410500c904a40c80d85c911b9928100c554001042c48031440120000600d10310959100c03004414684400103400394105000640c818055026680a1301000441c100a621061050684494007000ca500c0038a81c1055094002d00b803100c0f02410440c019800c1d51a40c0d100f515408841840000104001d400001c502900714415102c50030b01401c04040c14550360041107865810300c84840080a0b241d401d5502c45001004014103440700c1641ca41000342c62580604080390000350402c103030403200146061103106106065403003182996440e4842c20030305c1c03c080c00b8021150030412000800b95500744c50680280041c1015036001456080c02400c4900d15803202402581004100101290041040c80403240183ca665120f60401300c2c85403041d40030782d00321a9100150070305100e403201c80d11028003510f404a440e1b4503d40d460314202642d45424502c01c032641540403c1d104003800750290424 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 255599289 1250 255598039 255598081
    0x5130804050105070f060513050f030f041710050a021e031504020c0a06092306071e09050409140f03040305100902010c0b0f1506091305060604051e01090b0f03 70
    0x5c0c0e407410300c075644101c1900d006940713204507090741641e14024010144140e20020741243c00035840c003c4c24102e000203500a902c2840c04c0d800c0414070301d080c600c44c00c2c09000e00e03044a01004103c01d26049006da002908429840c91020b04a848100d009920020880b070041103403402040000c10f2070001c0002035804070085c4001801801c00110001b09180030b01d0070000d100d5801d01d44103442824a207000c004543d0301604c000ea0005050043e200d4000102030105107207000c10003140004000180c800b2855a4401900a89800004018840c2500708000c4180507103050350354800c515800f45541e40554003010b045500404984c8440c0440c0e50304c40c803111481810058090010341d10b49111900c0e01300c5040c84612001000c001c1e0380d00c14548180440702080b2201070074414804040703002d042c03c14080703451442d62000491025a2184140c03401031a0003070075410b94044101c000540500b24940e280e010800b94a40462800e07031420565600c6064451101d081d5170341c09610741c2c0303540f6142400d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 255600539 1250 255599289 255599303
    0x30908090d0f0c080601051504030f020d05030f0d060302100e031207020301060e01170c010801080a140304050d080403060c023c160302010e03030306030d0f030b180a0513080405010507 81
    0x11000150980c0d83c1240144151406402c40d91302d000140701c2c3e40c021003400751242050811040c40011114800019081e40556204000d014945001d91451003040304c428214140450030041581d9690081015030b4030980d1100e908034080308064480800c49070801c2e5068003d42c03428030702014400c000d0301405000800101b4140c1d620001c0742618802a040289150b02ca4010603501e07100030461035014030420306e484565503141c00d110940301c094840006220800b01c0d40000e03c24401001501d010b010010200300d190045490a51002e40c00b9101c200c81c0d1078100103081c01c00500110304807580c50714141805c120302c08141c080c50320b12030403016a11110190310800c0360621342d007040a4601140c0b40260401c400d425800094110940305c2180b80c03103680204200007280e1000300e00484006540e0401c0c02240745226010b41c040c016a01c1d40f03980081011014854100181076241d02450a11904103ca0b0303d03403102c000c05001040401415280f0f00f00010403855204100034110782d400340d02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 255601789 1250 255600539 255600563
    0x10e10020c2e03090204051f0603020d0e071203080702010623300111090612040203210a09060513030818040216030f020a050c150903010c180501030908090d 69
    0xb018242c001c850500e0840042d42d035039048411824107100300d50300601f50121801aa03502941c5444805046015440805402242d14550020130f6080750710504001420f40744a00e0301e40d600a418204800010307400034083d00e0220b11854010b01ca0241503c2d0124420591201107400000d04d11091100480c2c05c00b078210703500d01344c01d01d10342000d1507454012590343d041035509218050035102c2001e005408041c017088212100d030380702c0e0200c0325060a014014070482e039450000070304290009000340c240c1d44807003139241200c00b0b8410003820158801c2c3c0320fa50761507440320703030480d40d50140c0071030036064a481840c1031010070021000f910030206000b0b8019520021800814181e030050010800c0408400410104164001c4004006c0c0a41032009003c0c480300c54a07003640da03c1c64031482500a8840e02c40780042008050300b10b82c40004094024032565940c20030083c4a407145c0202c45c4000d10b100c00b0041007640c40ba001e032550090304181d2850400e8210f408205c2c00c0d486240086643c803032000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 255603039 1250 255601789 255601849
    0xf03020c1903030f140a1d060f0418060f0b070b07110c091b0a1205070e0114070302012a080105090709060509030f0a050a06051e040809030c0a080c010e10020c 70
    0xf0b0700600e0146c00e550f540c501e074011806030a0058484160f086c03845142c048c032600340c10345c5800080e41d0494111070142d0f0b161410f038104c00801848240c20030500c1034416030740440c1c8524204c000302149403003103404001565812000303c49229400300400700e5074000c03030004101c91806841c1181c122071041000b030001066862000011780c0080050320216a0555180c900c0314a41d1041c1540200e05091810044002d000000c00e41c0303516010704d0295130701c04698141454402d40c800308049000d244c100355203440d011000488184102c400342c000071448400441c450405e140352501802182c5c8030210881e0500900759180e80206501503094401c1010381c500c186810002d0083d1540150060030000407541001802d64500800c5001c1e0741e04a940341000c1c200c4410394141c2e001d83c010100136116070207000084e0400211102103a402032150030f0119100101203092100c008090b00d030b12003141310400a0086e952504041d00c00540c0003604404a1403d19400715400d4105c500081d88144d02d2076 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 255604289 1250 255603039 255603077
    0x3070804270c020c01030f050108120d060509070e12120f0a020a020d060501030b09010204050d030f020c0909010e150c030117030f070b1618050418060203040f03020c1903030f 77
    0x252002d2001607105020580b2030f03580500c143d030746e44140c07044148010360404030043e03510023000d4411002140009401d1102401640c004806000d00501801060500080081881201d4104280718803441501c1c0c0c0070509001074a075100034811030310745003801a207040f4907960b030b00080c8000066020398800b5200581e9000030344098a8401c04d00010749504504010150202c000c00044640c1c3c410841482140d4850f091099103d0b07240c505215201c03000342c4102d01306545110318903008510b6005001064806400510b84217941404a4483c5001c903c0c402c0221001980c5d03030084007504000503c42014401614803e0b80421001c0760310700382d20085950711a41c4002e1003074032039000550070700003841c901e0b980e040030240c001d2800c00740381040e4103c4c080700641c0c0b51040703a100b140d8840131041180300f10203209066680085085480c3c0c50181480a02c07030030000821001405000414104d500d40402100a15041c05050501d05401d43d036050b0385c00200451244103010000c898000a40b00d4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 255605539 1250 255604289 255604301
    0xc0304080703150b030a051906140a0b01030b0a0302090c030a0e0f0309010806150a0e0310060308070b010b0309030703030b2e08010b0f0a050304060908040b1305030307080427 77
    0x49044100f080d080000d5102c004c440107000d01d40e200350800784034240400d0340058061001c82401950b80e42d02005403070454000d02402000c4d0b80c45031200410848448515800401c1c8803a007038800b80000814107081000001040c04001e501100e1003012890b00c2c449400610780c403000b801400a41c150f20a031185203840481843c0e00070076400022600d07495640b1501081d04260113a5804004102c044204d003510300810421200300300e80200f8402990350200011b010070b1a042c0c50030440703140c59040021b030590003800140c926030b00500001800c2d0302c1d00e0007168821076200c0095800c003540e50750110040d01c050451681c0c003040030400900030318007510030000341094174180d02000b5105244d000e459610164805645080c05020082c9100d081c0c108942c2c0c00d0100349801c0c4d649569510340040108442403000d084588007180204c7d082c0341d080e0003000300031104800134125071755501c00c159a92141d110b00500761482400104038108448111840352107030707a21b4240c450080f0204101c102c0d05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 255606789 1250 255605539 255605543
    0x9030307060b0427060b040c12050702011104080714030604020f0d06020409110a1710090b060c030301030c06090b0a0e010e012106060e0d020f0105130312020109020a1205070603020c0304080703 85
    0x8005913240b4200441840307031348041d0700240e43c1800486105000640001000d10510070744e00d44802c00505078500c00c2d40246040e40303503c2c02a640f160385640c1c0c40b0741e40301094043d0310a1180c202402600c02d240018005100b40e81c02040801580c09140900c00c040000c41c3e01114030300d4081c0700c041443c0001c1e005280115029020041d202c602e8043c0c001c0403166a4040011012428002c0c8003071310060711903c40907960740d510b011901c1744c0441d02045031f900c1005080c0c0740a01011002004215003c0801c404a803240e44c0d401000135102c2404903494462030681102140006c4000c4549500422480d8180d0405052401d160100c542d030b00d10916047d5102c6540d43c81c2e89290902403142c20011480d86d0440a6400e005110307a26400702d051550045a0f860501002003000f04450082c4003100010b10b41c028000403444249000c040d01070300794450201e00c10710000b5000709650400c4d00500241e0340c0c04c00d0040071024600030051300250712202070101c01d40010000030400060400a88000b18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 255608039 1250 255606789 255606851
    0x161511070308010506182b050106030204110c210c160905100302030c040e030903160609060c03080a0c0e040c0804150605090106120b040e0f01060b09030307060b04 72
    0x110292034020300642c8160403180c4a41021b00814005101c031002c03000c0e040b80150780c0309003403552541008030034092003000803213043c40a906840c10400107401c21001c5a1098070180060480c0c180380340710b135000f0380788480901d0f406085d40c00c40908607100c1c0ca1807458000d2800600d4154100714aa0420f03484154800c00d03101141c000700003065052140302d91010650b044104102e0869000039264441070300d00d544034039218500301144141c144120f07400c00c0802001c03038140070030111400420310658070031600130943c81c0e0360000b1560f004500351209103500d0390351040550350380d02000008020300410b04040020b9020704508a8170355205841c0f4080c869100c0700352500c0c052504042007007150041069a44c04c2c181d04005e252540c40c050380c155280d03030a16912440d101506d06000300300e41c51400383d005041016001d41e00401080e0107951028200c0284007045c7c8a1045030b03158030860f40001c0d00b6600421290010413170652151f070341d1500003400860071100042460000c1440c0000d019414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 255609289 1250 255608039 255608047
    0x601290d1b051b03041206020702030705041d24280e010f0e010b010206010e0a02130f03021c1101050a03060b0301090204081015061116080303180a0206161511 70
    0x150000000d07540319000c080f001949401d0a20300d507560852140940240740980100d510340c110768050100704003070030028000700400a8100118012000320303009140c600e00274030004050075400741c40c1070080703a20f00e40140301c1c850b01d0710340c41452500003000c56209521203130300200b0b881003070714094000075184403800032883c080c64028000880348080300c45d0708182c1c0340c001000820390300403501c18111280300220840b20b580c2c845c0c0c42c1c0c01038420b52441380007800c0102c0c0041114460f4204d40320540b030003958202c0e0351440d0796240c2c11030060101806041205454500c0c030b070943c4920000c2c920080c440ca030107e0290f40c0e620726410650820b800410340c09801242c18040d4440400c902c0920083c110014808943e820548802d21500303405040104400e2100c800c0c0e03042020042c5800b507840031303109804501c1c0e9400342e00c0d0702c0c0c0d0000c3e101c011072800c180003c001e450100203004c200d0a6001001c06150086000f007280302d81d01d050504036421301c8519441e01e44100381e0b205030300090507503480c0c00303a072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 255610539 1250 255609289 255609307
    0x30d0e01090e0112060b0a0902070807060b0405061e0d0813031a0f060621040606050a0b0c10020703030e0f06040623071d041d0601290d1b05 62
    0x202100e41c100c450340c203040e040104444c0303112180003c98030790854000540e5400407008501d0380c0250750041614903000203a50010080e05030b0040002c64042d01013048803031240b00c00c00050b42e13416100ba03030340121500390302511740c1c0d103000042d0740c0074a008144c5161030402d0755400005c0e81201c00440103800d1010401c10034010000a06149912403200200441c030b0305044400e6948005003c142c015800411110002d02009113140d0000c600d10040b500145810303e000340c090101c034005e260149045c0c0100065241c01c0005076001d100c1c00c900504084080602460000e410005d400d80c10035480d100900f0304014203004c0b00c000212a440a001103281508146050343c00c1013044a840b850084030b41010284a01811500599903140180d000300c0c180441c14412100d01d02ca00ea03002d07180070750a900204250b400d50701d000e0290300950b40301d680d035100c0c5614800055030320032030319070380c24a0254281403480d401041040d030a0724001038a051200d6085003812004e0300810089000002e481c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 255611789 1250 255610539 255610547
    0x36061401110118060f06080c0109360515010306180203040f1208070e01050301050109050d0311070f06110d0804030503090f010504060b0118030c350d2a0b0402040902030d0e01 77
    0x1b014280c010000c180641c128030008211608902c0380340f50640303d406000d100c1d10445100b29411100c4e850b0022225200e4484420050a007524804a0810000410340d0315502a020b2141150002c45c012400c11400c203444802075030004000b2a04403481c0c0076250700040b4103000f600c44642d082d5660001e030346000c40c0086e0504001540f4030f8184441800100f01507a40034074004c0640c0c0b02541c40208440051406952a5001c012020660701401c0d4000c210020301c800d0f4001121960760b01c2c021091010710000341c403440158912000a841c800002d00800c1c003507001560000060421078a12111aa100908640040d00c0880c0d070341391201000304031981d01200b40041c0c60f403100f4121811038990713560308103441454407503c00d002c12000d00b44191198601a100482c05a0058404020180d03122080d180d5070903e10329001b146104543c5c004400d8148400202058184a1410050150b4a031300741e8a1784028812070f0b101d5214084070005032010b100061503002c8a403101200c00b205000054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 255613039 1250 255611789 255611801
    0xc030c051c230a020406091a01030608210c0f011a06031003020405090a14060a2706020d022203020a1d0c0309010636061401110118060f 60
    0x41d414940e0503007200070500b01105080e502c0500300c0140c65041c20182c1840c1003c4002c40041c2d482450701000041041054101e003101c5001e400c1201d0410083e000103504035281350168004690010907040404d00d0554802e00c00000d0401d1304908004000071140c0c5070804104060400b81d450b0408001c80041e0f1903481c100049048070200d0451900d400c0040031200b552101920031038940d00400d03038282c000c0c004410400d401031a648840d0500045443e6a4501a03d03480c0c1001d2502c0400340c1d001c12498280668901c0914550080daa480d803660b2010707411078220f440311139500300b1104402d031500114103e4455187c0312280001441c5004005403860305a000003099040c160080f1131402d4002500c640c0887c0168180340c0307a40300c104206006000e140c000340c000c20030f600005043d400c01607100d04203860003c10aa56200031400c0310106458142c0b14a1104240c80c1c1203482ca03560040c800d1b902000481070001815494080008c100781808480c10b8035450b55400e08600e26200b940039038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 255614289 1250 255613039 255613069
    0x30212060f030a032d0c1407080d11010f0501060c02010f02060603031c0605060406080f011d04020904050c0603010f090506041505060d0b04090b090d08060108070e010c0c030c05 78
    0x8004407460800310b520381d60308520080401481005404104240104480d440307a52031068141c8504000030140c4200d103452400d880c0b598481d55502030400740092544c0c1a522480c1c090100b1056944040d6484d00da0036007406525521a101e00c0390001c01e038810ba40c020a00da54401ca104140c90002505851b10180c0c00d0085400120030440c0c80c1d01d0000031074440b10000000d807150f503111880464020301e240d0300600d6002c107000400240311640210341034000d20640e05101d05a0340d0303034180514400c030310840700c494482d600030006016151105085510901600035942c1003419440002c016501c00d82000304030a03403110381403010444910805500600640307003000f8100c02c904601100301400c6c460366219040010b0244041101034002d0380d1507543c042c0060000381e84918152000880031150590140f080e4007501004610411b00e940c011f01060f150b070402030b00c40c1901103070344507035041080741400400c120036400200c000764030030000c1d801a800c205002d4241010010802003040d06 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 255615539 1250 255614289 255614299
    0x102180907030903020d140f030f010f0b03060a0303110c0405160201060b0f070f1a0c03061305061302250807110a0303050904050604090204021305040b0102010c0c02040908070b0703021206 83
    0x101c3c100003500016800503490007814152141c5441200f0040036101d6000800707044403000c01800481c010700003000d411780e5555419400c91a40b1480c147d001800100c1d1801d9206581040800109002e1140c2c41640c50003901960300030b640d03800c0403d054900c00d40d5291660011a261507000300d43c203105035805413100c08000c40c03038030080410480d603a0017400b030064807081900341103900b0810544681c0c4003000e0305100368032962900303000094894008450145c0601038a0202589098040c4186840340000070080110200402d200d1002034100180f107a440c2c040c0450b82001684580241082e094450f8500315600d80c124608101c400b4843c21001d40596481c01d01440060f0704102616068181524005015036030240060040c10768010080e401c40c3c40040c900e45580050315003641aa07801f80d03014816001041e004908803a1a46030f40d000040480c0d00c190010310700b070b40001f540700703004d10001c0381032040315110052400400c4c0e07110008030303500180f40303141445820040d0b64001c40840b1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 255616789 1250 255615539 255615551
    0x2010e0f031506060c061f0f0e0f040503040b070501020711040e030a030203151c0201020f0c0d020d0809090f0106030509070308030103030809011b020318120a0311030c010218090703 80
    0x420359400019075102da11480c0d000024445860790010b0b81d401c01d00c40e0741190301c9802c10341c00781004810440804a00d286081e02c012402c008424404000ca03a5005a00340c0c160780c4030200141201d901601c11203841c042004000317500561034010704402030040000581d60705486c60300d580a105840c000380e002c0d0b401d0030200d0b0021a4040190341d540c0340e181c1005a582e0382d450546992050a900005500c885000c9070395280f442e540381d544048038801e13000c45921a140301520f658a1000d104860303800640300001c8001800e0201086140034400e9122500741aa014000360700c2003000c94500442401c40d80040005a0745401610341180344940035140300350075501c400103284014000602407146960200700e12490035407007244c24800b028445c561401c824800251240d200500d100c801c04918501000d0501e40941c141c840059004010100e04004d65000d9940b881083e07080c007514041840306200c11402800280800c00c08049920300e0124030404014030340001918034000c15260035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 255618039 1250 255616789 255616819
    0x5131a190611010f0606050c0f1c030c03020c030d0e07091418151008010b0109150c051626011503060b030703200f011416020402091c02010e 62
    0x4100003664402d01d440c1c0300465205032014090a1600d503030480c06031a1100c00906a94000d0142c004100c1c2c040540b0720340c4040b012800d1340c500c030403030483d14143d0000b040120200d0099018074000001800d0140c140b107034201e041c60031078005000c001c400503142c7c1e80c5903510340c00501c1004c020741040c410802152017081d44600119a00400d942000d01e220001080404403c00c80d00c1e030440d11030210000f09203040c11303410a502c107a610810700c0c9903080085180d05076005c0c581e1081600c0084040d85034811005000304d035150000181640e6600840011300f031b1200d0402400005495214007403517020307104945007007114501a1100070642d02d0701d0813503079081121030b20751800c480e005540400c1140c41c00000038103081150388002c2c0060551200e1022a0103100004c2204840071207601d1003090000d801518082c06400c1401004503003000409224210b1017007145803580003800050800004030045a521207000c1018943c401031503400c2c07000c56038464024001c08200782c4030349041e01007030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 255619289 1250 255618039 255618079
    0x3041208010f0608060d1509060c1b0210031806021e04030816050f010e15060603060105031906030c0305061006030b100503090f0109030c0b090304030b0a0207030905131a 75
    0x240103800030000f42d8030208413542d844e4082c040c0340e40c0e007010065003003402a146c42e0000700b110520480c0c401c0c3c140ac0c0c840003541d00401042d205250740302d10180303c204056082103c14140c40d01c03200185991050140038603c001800c60202d1403140e0001656554407143c914260300c0549900554400100f000303100042c1c009040e604220800e01124800c003980e072800ca8213100d0780100d06d0300150701c0c1034040f19845200040c010282107100030303202e6042e240d400611000303210858005011890400c00700c0c01c035401410108050400038540010b40c40e8603961007039034445180e8001d8440d9400030003400911600080c0c07910080c100d908041106502c494041131302201c41e00441020f00c035001c000980710000c10322100710f440c82d806000300403107842d524015081c04040c0000340e4ac00d17480b03240040c400490010403181641c1d0008500940ca9680c0614100603502042049040054000000646e600d808002c01005c501c81c2ea000303d0f003114000c1000d42c51081d0320032881d100b241b5040c005200300080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 255620539 1250 255619289 255619319
    0x1c0c060f050601050712020f030d020409051e0f090c1005070b06040917090f06040e0412141602010509040e1b0109030f0602210103120e010c050d0f0306030b0c0304120801 75
    0xc800c3c450080c06d640d0744026814080604100e080c180000a01c2c00f0740350146070300900540d4810b0b8400c0000c0e498000948050504240950200c41404008240c1441d820641a64480c1c0304000b00d030350391a8120b020601c00100711807080c000c0340c00230503688204440c20b0105a40110180c400304024119502c5034014401d210740b81c840200070006100500d51500b0180c003884801c054920f0340d50fa0b950300140074408904450a0f10720310401445280480e02c1810050031420741e0783c15150804501e04d001403415513851904034144081002035104a840e0b40c0910007101901030050106a190b448515400503000a04d160401c01d0280007400080e15401003501d41c2034206074010703210640b10304083c4802d01e5000104050301400c1c00000100400b0794004103130480c8998130a0380142c0c4c0e0b00015100400c030345a0044c10f03500802d20710b0b00990310480d20581d410070700c1d18002ca120381d56a2501901c40f28151103030641d007480003041000b8401c0640840c41300344503620300061998036208065000d0b40c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 255621789 1250 255620539 255620543
    0x2090406020d1103151c0b0114010909180308011703180a270606090506120406021306020f060705040f0e040206190f030f020310090504051c0c060f0506010507 70
    0x1a0100d5114200c2d50680d1007030001c5100054090f6032030814003a1944a0419615418411200841813030140412506030740311042d80701e1904c0706681d00f004a4280001031002c10a41000410351001030310348564090049880d1207680c00220130061400c4c02005050140c00c9100600c3c40580c040c25411070020484451104d100e035109003003003044002410070803144d130080005400400d1282050201c1071320352090301880240c00c01100340d42e10f40649200c0a244181c1c2d0740800203108865541400142490b817042c400c1c1401850700c9500108022454640d403c128016030007402c52080380141040b40d6900b04010341411401c00345000020901d04519000d201c07a412540c80204007103480750303000d0768030008081e1003a5070307000382c03142c40181107904829103040081e05010b01c543c0344030790074401c5030b00404210840880302400c002442c009050060070454440c45641c194840c201050250341000c04100e40d20608190498108134040d2600000c400030f07220314003010302c64103a0704030040fa12403507 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 255623039 1250 255621789 255621791
    0xf0f060b0a0b300702060106080610050d0f090b01080f070909111e0409060f0f0b010801050105130506030103140d0302041d0c070b01090507020114060f01050f0c01060308030403080f0402090406 85
    0x3c0e40e801c51003004000f00307007540e440000081c4a0002d40201d1244e06031442d50359020303c95901d00d4104240714548101e1304c40868410403550541a10741c2c0c00c5404e4217800080e000c2008181a0340c1c4c4142036500b6444048240c10444541510860a202110040c00360440034080400c6681796440544e10000046201d20322940b0440c0414658240400000300c00810800804455082005c0074282e01e00c0a1200246008550a540030343c5110b88010040103a42d16003040e1700b800010345080e4480203030001ea40c0030014002485a603030200541c007031446100d10307089101641078030038130781014a9402c005042c01404103100c0c0d0710000c0d6904091a2000f90348003420744410302c0404892246031000b40810040301e00109c0c1c0d100031500a103020f00502e47c003c200d01c2c10502007104a43d0000d861055000f00d90045242d400e41c03085018001c5d240c240c080c102c1c070b8072401c440c003a800c66040d50700031a041c0c0c01c04820031090503009000a94401074445005106142a60008001c948020310041090b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 255624289 1250 255623039 255623077
    0x11e0203060a03051605040b09070c030809012405032b0c020f03010f05041407030804170c03030a0206011a0f0a030c110d02030408010c02070506030103030e0d0f0f060b0a0b 76
    0x903540340c00b100001183c00c40305a48109003404200310200003140a458051414030200c50005c2c00e101040c0c91154900e81d48004691090396022110020050301c0481a50b4039100101305000d92a81c07403c0440f001007207002d440d1441d0406040c140180700c10388040301000e82e13400c201c020124101ca04039694045c0360400e06441d0720710002e410300a00c080d0850f003540ca01181001146200c0d405140668011103c04215040362641550382c0d801502005003016010b000421a007111000042040f040784410baa1002040c0c0000c40e10b1904440d03c4071005900c0640108131074241a0584003204940a418600c0c3c00990540d9210368855030a02c0020180d442594802007880b4103c070341441d800440039580b01e00218a4025aa81c0140c06134211552900841c0b0040900005030384003110030142010303040d40e00c1d58038107840b000003816000340c0041f034910350030f000502c0800d80a44403903c41c869420122030941040c0c0100e0b14000b5005010306a130320418000300d04400e0941c1d020b490302402e09810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 255625539 1250 255624289 255624301
    0x5090307060203010e090705150915210a1104140120030d1406040207020a05090408070602300609060d05030c1b120606060412060b0901090b12011e0203 67
    0x6984104480a0081c610202c0007003804000c003514180105e1076841242c84064130750041101402040d03401d0b104044041000001c42d00744410b1001c1c0c0d00d040981c10508000c2c07624212840094002c52480405140710b01f000442c103080d128074450065100c1e031482c01c180c01c14105a40d1140c0001c40a41800482054074040a155614100d8400c0003001500d0b02d0706509804000900ba4803c1800141c0c030072403001800030309151013030350b1000750010720021760180360005110040700082d1007030f102c02e801000f60740c000c24032078002044140c5003500305001460720b0741d07421a804030351003d915007040002005d1081595030440d0b11a046002101c040002101f1072404074074500c203070000f03a82140134540700f00f41c3d40401010040401001079a0400110944002494441d40c0c101e42c2c25502180600c018480070b001894044061885080c0005091070710000088840509038000f5400ba511016414103d091044000d405074000e00000c2c440c40465091380440100e007040c01c0c249007580800010a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 255626789 1250 255625539 255625543
    0xc1c0209131103070f0e0a030206030702030c030406080f061e040f06050a0306051f0305070608070507140c0109080f1f140103060209090f040308040209060f03031b1c020d030509 78
    0xe086060800100b01400307051800c1102d581003151104049400702c015045102d02034a000c52641070024900e17003200d801d503401c00100f900050031000840c482480613206a103c100000e00241070700351a01b603494941158081d000b824010312413070141c1c00000f10512407042d200c41d0100c41520894011a800740740c031140000a21081c1d01560f0b00103441c080010a0004540c0013074001c0e4102a5003840b941403151907607a06513510300c0001c1060340815420001f0502c904d10480e001160b601c2c24500c2c09100351144140032181c410b1503001e58110413404a0f880da0040e501900800211018001c0c49101740303102501d40c1076040e61b2082180c50700c0f4007180901ca040d44091400800c1400000c0340356140d0800400940002c803240d4060b48803c0082030f1201e84006072584203a91659412010355501c0d0700340801031801402d0f150300301c0900c54188007e81e6003071020f010514403540c5070302038560040504a291410081e0000c80b611102c0e10413080280d40403440840e20010f40c20085641d8640c038401038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 255628039 1250 255626789 255626809
    0x406051b040603140610020d18030f031706120a1104150e0108010c02030405090103061a10030e0c0a0302060405060a02120a030207150606120c0e0d05060f0c1c0209 72
    0x582210350004000c80c1c0350760903a001c140c2c042d28200481c40d82c0d6a03a803040c030108602114100300907901400e9500404c42c461420003a14494400040c41410b0b0349544070b01d0f600c104442c0803400300b400c9010f450000910301104a034068012038020300104180c514107500d41e903007480c000d400c0d00380d0703a40b800d4210784440c0c01414510700ca8281803040d107542c460011441410a026004183d400d080342d44082c0d0b0b00c004151803c1d524001d00d905081d9182da43e4030b00c0144148400248520402404070701940c0e5a44c1c02200d0300c1740e443d1004548080071600043c240592100d24601ca0100d0720014405601e410742a101035131000d64504d5528a400300c0180d2a001480d4034080000500085282c12144e140c1c000e450304900c60f268544038180c0c510051001c1c0c0d0070314094a00000c0c03070010b0010218040d50403078203a4908a047c440c50740d1180d00c0c00702e003e070903400c44240e4159200e4014058400b0440310001e5000d081c104505092a01e11041200e003000101d01c402c01c1690081444001540c1e04a022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 255629289 1250 255628039 255628081
    0x610030c0b0a1b0b0610020a0b06011218121103031306020318070f090c02030307080417090303121006050307020c0d170a08070908010207020609240309010207051e0303040605 77
    0x100c508480e00d40f0044c940c104440b4a40104465a459241c080c000130f241807202c0c2d802100041c1c03e588807401119100604a00e0400f2180c5824203480050302000c00c1ca0505406a82c181c079000501502c0070341004404803011105a100b00200310484000c00c10421016600480243c0e40c4e41b1107203203401c280d403d1003060600a000308035002510540c5100900e0845619107000d10400741c1c0320005a03202d0104545060100c2c24440016000522101003c40c0718a51044911308024001010a185811046103044480019018000000a0801c40300c0003031080303240461442c6450f0200a4850380c9a04034035010384000f400700f408100c00c03c0040200d462103204001c0d11403909000c000d00607001942c0500100d41368007000328140e81e06000b1124050703006059980b0b0701c00000e06000b0240705c41d00d400742c00001c00400f0001101498402180181703010b01c000368883d00d0508200307013400d0700300040351440a440b4084030848800030081d03e5120760041e00006840d0394820807080c1803010260a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 255630539 1250 255629289 255629327
    0x12130c05121b06090d0209060a0f17100603020303040b131518080c0d030c050f06010f03121b020d111201020406080112030206010b0d110712020610030c0b0a 69
    0x5103a070100c1d400101619404030380b1242c030030741081407010301509220752410241c115204804280250038804d45d03040d00802d010348500e01d1181e41d003600520170802500302d10013076440c0d94880440c03c00200b1100e05402da400d101008180e1039503000075a81e210702c0c400d8400019001c5000716514200c640c40310003d2540f0b00501840b0301c14084000c101c0b280441104075524003021300440d09507400500c9032010070000c0c000d4400380362692400e80f10110007076402c40c0c01e0310035030303500c3d0111482c24082e50340280b0003203d0300c1901c5411403030a034142c2d00c04240c0c07580821440034000343c02c820050300c04030a020380590740d540340b102c0c00b4180b00c110856a00c41c125005602644101c5002405600800880d0400d503601001e59803550304040c0029040400500140d100200500510100d0741c000d001068801e000000e825a40d90500d910b1030f04440d2060b05d800141100f0340e1100741c0c042c04119445809680d104542c0790840d5180390310034030745006041c0d50410202d880001640180c1c45907452400f0650 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 255631789 1250 255630539 255630559
    0x1c090b0301030c09050a0501082113031a09061302010f0e03060c0c0c0901050303070602030601110a0b070905030607090e071211071a070f030b0d060e06060307060512130c05 76
    0x1030142c001d0f00305102d280c4030300e407810000502c2000240315441c10b880511014158101441020101074001425007485e0101c00f000305401c1040321802c5140294460342d020503180521851003241408010182c9070076030032078801c00040c00c400440000c0542d6090804000b8150341d500203c2d21546120b500580501c106e10a011401d2803c00203401e1030500c1404070381701c81d900c00d406e01c85140000c0c031866415034070070300003000000c120b03030042d5074086010316110030b8105034070312060326001d0845019034030301520345c2c00d000d03616510a550401514081e401841c50307051002004098006910444814040c11004039070407901c01c3e4914540300c80d00080074041d5440000c640000d83e0b00c084401c843c00400882c98001040f20703140e6003445030529488800840d215a4015806032919410072540079030b0390700d0084001040351284104420001c001448076141000c00d140c509005a08800180841480a0b0f4100e084600302241d00c4235150b8040c540382c03400f40c038080301c490000c3c2d00b041d58001070044c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 255633039 1250 255631789 255631793
    0xd0f06050f041101020d14030a020f071103010c09030302100903051b030405040605041418070506070503031006111f09120c050d0c0b040609021807020106030201020606121c090b030103 81
    0x41d440c140194040d989a5094042d01030069a482d4030a4010701e01003810042da06c0880201007016550010b48140c2c0949003000400741003c0e19842810115072400c405400b03450541001d102c0e4604130105410618072903429910302039900d09139061300c5c542c61510343e03048804142c0308409590390200500f550650419403034004503103d82107401868002c900e00f610010795840d150140110b00390100040184035111141c801503c00c0854001e41420704c200000000c143c1c5840009103c507a004034041c4d500c2c0d0070824650035420005510000030080944902242c403000803850300820340c5c1d8280f83c080c804a076800800090890020040c00c20081d04800001c160b40142040001c544600151280d1915840e419581d0780340c84180a040f0349840c100240000d403c41d8407003207504d40010f02e0907400202500800c007005c03508880b8003005075120300081045503010001d49800c20782c112148190741c501c0c8510f055541c680c42c884110311400094519140d02d02602c40c500c0503040032a2400d58a603128 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 255634289 1250 255633039 255633061
    0x306111c0203160c0f0203060c090f0a030803070c051c03140c070f0305030a090c092f07060b012312130b0c0d0e010912030e06070e0d0f0605 62
    0x268020103020000800345503030403502442142c0c4194000d048118150411800894512040d020100c840d003501070b901c0700242c0d03810800c80707100e11145c0503030b641d80e0452003040c80b400c580c040324107500a4164103024000a88544c1c2a00d50201c0603280c21501460136051003403404599800300341c000d40301803859001c455403580002d1880c554640c3c0800b581d4070780802d22129441b40c00006800d085034541c0d8040081d01c508010345d0003061100001c501c401e001d803202c94149070381c1c2e800410050360310001600028428071032141e42001007041c0080b1481c0c130b600849e00600c1840401007045030b0b1f900400640c0da008465014003111715000b000c0000c0134001c018405584842904018801e1900c0010540300e070b0542400040c40c1e01080c28a00b0b62145055144d40e60480d51101550a45501c041d0000030024480c900307401c0d0143c4184900701c544d1400280c01c03203082448840654010310104100b00f5001180d00e07414603420707920442800f849061400580350300203001041c060500b000d00c0040082 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 255635539 1250 255634289 255634297
    0x30e01021b0a030807090b0301030303051806100f0602070f0b0318060f062b0b06031f050a05011205030a12020f0a181e0504020715020c15060303090a120c030611 71
    0x4a611070042607217031100c0a5030050550321900c40310b07000810050000038441e422454002d40600d0100000e05145e00000c1d01f440c20884010780e040721011010445c410201c1038403801002d150000d84451070814615041504260003900d030044000400700b01201c0214000301140c1c0c00b0300065030000e041114100865940a8410342c3c0f01d07019120003e0411240140c100c00c85044040030074160004035030380d0300d42e13441e002800a5854003d24541104014148505c91101c01c00c0010018561801c0071081086400603049503e60705290801d03240010b00020803038039560014180f130400c0305003c10910001e07228818007107215040c0071801007011070b040380a0107000c0850195069038151280d03d80d00c0e00c0050500001000307031020f00100064103113039004051043c080e004841c070b60a001c100000981e0701105401d40e85030700c16100f149406442614107908020110007a6144c58110400680760007424000da08444015444c0c2c041040120381004006591101c2d0500c014140d0440840080e08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 255636789 1250 255635539 255635543
    0x70c030204051e100b031302040e060a0c110303060d02240d060501031a03030a0f090305030c030307020f0a12050a05070204050901020315010503012d03080d0621050d030e01021b0a 79
    0x1d0074101040c020b00c00c4d040c0220550b400d01d12013904582d60091403000c002d034840f000b80c1c4c006039142c07004000c80b03006110703551103240005008500040000310051541000c000410015003040c4148081a034441640b000b081b40c040310600905056070a64a041e00c114102c1c074108403d00003030310400050541c0054045030000d0300c0810144003414024112000c450100e140e0507002000b42401660103801035813400ca6880c5000e02070a40c40396951440d40c1e0141c50102c0715a407020042250385503042020b0303008001050007620003180c15903180301882a14a1103481840004542c0c091a079118905483c0102c5e0018020312490411050880c000d5005031010080902092038200241d40100212030480708602e0680002c1021148941d0740c0d211004040c44080019100000c00314078a4401351030642400c1c20001200d078580100315048225422605c42600c0551441402103000826115030400743e07400c000c01d0070080c90042c68024402c1c4007411041c0581c204420400c0d103400220702510038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 255638039 1250 255636789 255636841
    0x50f0c030d09060612021f02030c1501030209070f092709030809010518060f0a090209040b09160b030604050c0c10020711090f01091a0a061115061005070c03020405 72
    0xa03212920045d103001da0000103508801110640900300d4480d441c0c08211405620640e0304000f82d88141c18200b40030072540d9450044110014400d52401c0010990080c0f414100628020b00300700d40a01211418132070306481c406166030640351904026030005403900e4a841c1005440440e26001d803002c04140d9515045610740000149001030030300007507815030304a5000380b42c81c1c3c3c1c9a50780c1040f10900100301108240d2604c580d280181c0340c10b403040d4007481c41040180c1302840c0c1a122035240501c881c10314000040b640c0707010801c90148408581e0001402d484c04602540c8850080c0020f21440300420010300c10020003002e03424140e409003030118400d00c4620103081d95402003041b412400d40c0c1c494075050388640100b215121642c001414026a11400040c11000da0300181703440c0310b00e41c085404110b0b0000b0700c41c0140410322411030f1032084485000c42c581003040201340001160450f880a0010000d48102440404a002001950300420074442850441c84008959480b803e0b581910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 255639289 1250 255638039 255638051
    0x2240405010b0102070b09040f180c060e0102030f16030c021f0e1207060516050313030213050f1909050106060e01020706030b010f03050a15030308070207170607050f0c030d0906 78
    0x35600c04250b070030407510846e00d12410900480e00b080018142a6404848a5598212902c034822440740d0380c6030503401400020344040c50207a01403c05083c020b0708904540017004008103141040d0107481c500045019104145000d528058454140108029502a4040e006600190000740061440030302543d207111a00c200319051144440c020741e4541c2d01500918801e01074644500007070003400072042c02d01c40b407031402a25003905643c040500802c01200401c0c0038019400c06040c03800138041140410401ca10b400071024030015405460030001c50782c01c41200254613199000103d540c1e070460004c1202541e14103025280c03139149003e040c0503005444000500e05c1c024452040701c1401a101c185521003112821001002c00420031102d060380c50a06132021000c80f1031031000342d0302ca92100410f50030030441c064902001d503032140441700c02c00e400902060f00b0104985030040c010342031054859050141400943c0500e0407544007900c030108540c0c4030407605811000800d80500010800c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 255640539 1250 255639289 255639311
    0x52101140906060316140a03020306010305010b1602060a030906050108010c0f0801140f0112092312160317090304050a061e1103040504060320030105040302120702010224040501 78
    0x7080204898030b6074482070a000041d0b50601041c101c1d140c44816141010500c0d00c16800085c440d0002030700030340025400b004108107940c05216050151441c100c1c00c03030500d41034039407041c90a0740004000740154008200894841d000342c010000b041e601410501140d138441100c2030003405640c0c00300001440d6091120724050003140c055060380c1e0488800070034036400906210101c0344409007103041000c5441020f01300013080c440c800c15680724807000d02412140c030b150040002c240a00d1b44045070000c0c0103950b1462030b181d08692822100d201c403890201a41d05040da2550080120f0b0341040981e0800c12255240c0480200140d40e0111000e50890f40c0303640701100d0040d40b0400725880540c00122081046005460110100b0072800890380703000d445102280c01d460069000b01ca210b4100451000ba51515940c646900700041e4020446403800c3d0310029540d211003449000094400540507040d64800e100c00e440e0000204050001090550b111041e01a02190250b071103520303003525055 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 255641789 1250 255640539 255640549
    0xb0604090221090a060915050a02090102060a021303110402040302040e2107030f0503060a08010e01020c15070f120f02071a100b0a03020c0106181506030b1c0305210114 74
    0x1c0203000f02002008803c1c1a81ea61400030004004250b801168061105041c10340364050a8492484030b4800358850543c4000646401806445558461300620101008051628101d404c890b00316500040954101e40410000c0c480e981000e5001800c01c5d5070040c8107040060700302803201c1c10726a030300760300592110444000d0084080080000c5d41c17003800302144030b02c200061608004000c00c8800d031280d99080302421200358446040c0c841c0d40101d440c042800c42070000441d05508640110300354904403200920b05110311140314144100120065a0407145510215240c0b0309214110340d2080d16041010544c0018141005041e070030b0302c000b5250200c44002e03081140c0700d0b041c100381004640d00090340a90080480c00761550b40e51340d80040d14142c05204503415000e00d15000034001030098000601e070711a60000c800340340c00e020441d0865140c44c010300c161f64003008032807080b580151034210752502c41c140f02c1d810420410303c541100d00c02850380850485200c3c00c1c002c0e14922014050003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 255643039 1250 255641789 255641791
    0x30c0f05090c07060b040f20041d042307050901050d0c1401230c060c0c0a030f09030b040b091b010c0807050a020d0305030103050105061e01120b0604090221 69
    0x10341c004000602054894222102408a60340300340d002081003440400800c0403550f0040c0c081d20450f80b0b404010b0503840b02c0c004185921408005114a4281061a602c41c3d2a07a10944004402560000a02030000c8901d1680e404510100200c0f101d50600c21400e903607580c1401010320940d080f5000081d5442d2030652068030943c8900500351442ca812024041901c6801980e41842000b607080d100c914a202408140404034169413611003000c0340255140000042c441400200200088548a040040c000121319818070305400184c075844400c855280c4103610040c18074881100788070130010080000c0f40301c5c11003038040741e91154012840400030300a01c0802804281e80d41c4004c0301140640c1b0080c00b13514000c500702c41a200e2035501003038404030514402d500044000c001442080000e0040e190401c05c203d8600c90050207001c03000131800c01c102c0c13000d41844078150a40c03030380741c4581c2c020302d548100007480a0380303d46d95840c001e03020f54400e90b08105900200c400c401e81e1414540b00d51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 255644289 1250 255643039 255643049
    0x1a070f08040608250c140f0303190b01021207030203190f031b09050108040c050604081507090f15030b060c0d1806080609090c06030709030302060915160315090501030c0f 75
    0x300080f540a188142c0e800016801705460b5814001a0a481c0c040308000c44c2c000b6030000002150369260030f285032000c00c1903242c1e240701c1003400d04114400350ba1f400242086c0da00910328201d03a94984900c0c1c10303441d512070002100c00d1040c0d44c0c1c40000d40141c0010404050000e5a2410702102c50811441c1342c100049041d281c006c0b50715410203100551103220700aa1103841640c1d440012512040000e4568000741c2c4810495130000710015070403d0641001d54102800d82031042c00d00303040c901001305000650251080e0004da452030f0a4089210340c00030070080138007030a4141d0303410f48021000d80380d04406141c0b8000c1a02d014000c40d4600018202c4012207040b44c0c1c1d60241d035216007082002c00340d0094000189840796056225103030351058011402140180c0343c4d4020740707156150180c10301800038419a40d540020203100000141801c0160303001016441014500302c01100940c01010b40c24410705900f1242c1001284201ca564401c1d41628040e40581c00c0e403554810210515400c40d0041c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 255645539 1250 255644289 255644341
    0xc060f091006060519020709151a040e06010302031302151b0c13020a180e060a0510200a0506010f03060b03030f120c0906030901090c050f0a1a070f08040608 69
    0x11640c0510741050a4800170075441520758280d50740c00e4074403e07074a458030034074610100c0000400c0941404031862a600b0a000051410986844d500c4241d0402c002c0071141407603000400290707952908800c0054080d401860a01040d0500d0032501d000d8010101607115860b06000e218040c54000800240d03401c001090791021501c9803c60b000a5004000c0760014401403907803038000c446c02c00b844c04002e020681c0c507662041c9013010070031102e00c5403030740850700070120040040161035102030110064076070030300c41d42d0340e4001e404107052420b6100907001d04140542400440d000b00020308ca04100c0c0c0c0141c00c103000280c00d610405440344a40c4000c0b802d2100c0821243c10380e03002004200b0b0b403212401d0407442c10005e1010105186a00c22140c0c981c5a03552182d00b0780402c2000c0c42c40308040e00055500311704030f03803070440481d400d100d09010b00f0300d26511034620f168040c03041104440c5030035803013000070b41107002a1819440c2c68010340605404141302d14009401c44d1014807140c0000300d61080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 255646789 1250 255645539 255645547
    0x30d020d02100204081b0409080c0d030b010503060915031606080f09010501180c050f0a030906140c0d0203060a0504020a0f030b0f06041503060b1605010b15030105090c0c060f0910060605 82
    0x506d0300c00d403001c0c3c080c440f03410a80325100c4401050381d40d406003503100c51500240142d0146108014102c845030b0405505005040c0240032240d00c0340d0041074ad000e19807051140e481e06003100000e1400d129280c8940d50a4000c0e84007107071141d805404680074101c2103a030202c8584403103002c64242c9030240205056040c0c3c0040e61036241a50740c02035000c10140c1d04049141c5000e94106122592210030010003090320f0b13080240800c0310912641d041d920303036807010744401d0802031040071941c458041210b503a10340100c08100306a039003a05100003008010300443d5503503103d0303101424002c00c031030581020030724101d004407003801d0500c2c14810f242001040c580c0b62609000b461005904540c101c0d0707007010b91b01c94010400f0f00c0c10b030340203002d00080700104100c01450340c90514255a01703607030791a02038140c81e55100d400c4140f640a49040d02c0c802c0720010742d5542c840c401410b80d4001e601046080340300d92000c0c000780480844c056401500c07118140c9070202034421400041d81c10b90300c207401c00110104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 255648039 1250 255646789 255646813
    0x4030503070909060f031208013b010906030b13030c020907020109050d200a11240d050f06090403021b060708070b01150f0e0405040f02030d020d0210020408 69
    0x119070004060806800c4140c540c500b83e0100c80b500d80181e07041c213010410601c28080034400c401c9144540e4074041e074496062405030b10102e12518984803410010481a0117292114a58420102035030700d02039000c2e42e0340c1d03007208010704407610059070580d84082c0407803130054129141111903034041d04d50480302e0401d82c5c00d10510040091910045550303401c4030a00080013486201e04146041e50f540006100054005490707407000040b0000a606c480c0808002504403040e0105c4c0b82010ac40300c3d0071002c008003000341c28083d400b443c02d17003c3c0380c001508100c00d9241d62120f4018680c0554906440e580c01e000d118200b0750998001e00583c0c003090741454807480441100100200190603542051065a00d510b0650010142111041d1402c0d0041c891001c43d80d00074101d0002d5403a0840400b80d0740300d0080c051034281042140141d880300006410f000ca109a81d010546e4003408403a000400410025101d49140c690036005015400d001240e5002500070b5409070703042003010b403035091070403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 255649289 1250 255648039 255648047
    0x828111f02040302180708060d0f06020708090d05030705060f0103030804110310181b060c03030c05072004050606030c090105031819030e090c09010302090f1513090e060403 76
    0x59000c00c030800c1c0c0800c000300050704c134404400d045c14040800e860701401c04070303805010100020890f500602480c18010040340c0042c1c2a204c0d03085d0446d400582d904400c0c240030416210312101c10b50130090b0f00f10322608202c4000014461680600300f544d16a0701c44540b4145034007000c1c0f002400056080c40403e022504550156501001c01000c039055415294901c1e015200c540242201c028084403c10342441342c50f21103076800351520100b00310854104080540400d13400c1001038109076484900294403030180307040b50320380383d008460490074900c00b070b40742107181040c003441600a50400c00454210b040084c00d80c0d01907d4a0780d0150f0514000ba0011a040d8000604071200540c0740c00d61030190820078080c01d03046908036803100b40056428207000d002460340000181c040c4c5841010000a41450002d0325400c2c0024a000b42c0d45690900c0020f84c48d07485c2190385a4800c1030000b00c4060701c0c4150b401007607034100503600c200c5000e83d587d9990781160713265401c070000364000400080c002441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 255650539 1250 255649289 255649333
    0x30c04150207050a060e04050606070203060c0a0309080d020a1709071203051b0604030212030402092d0702030a020d020109020a050402090a030602030c040611060601020d120603082811 81
    0x103510407502d00e00d03a103a00041000030a41d02040c04503140d21748219860600b0300803190b000009881d0a46413840e10380c04660391781c40c024064000c0b220041060300c3c4080c4241c0050883c50b81001c0c0303081d150000d0880d80c200a44c40364000f00f0110b0f0303081115039a88401ea0390350303134461400503003c0c0c000649041c3e46540c0080e21040201e0401004201800d84607055280c003005280110700100820310b030074034004e460315412042a0b144510300703000300001039446d01c61481c4e200c400b280c80303130440e10300d84608545c545000380140007800d004903042240340e55000012b0040b21259508440300a020190103034203c62000303d0203034011402020910090902d81c00038500c00e1000390103030090310740e81d0719a4070481c3c2041d2450303403a940d40083c3c100545a4030480b030703401014030140a4030003401c240d00040d542d560780003901070a1001c840c4806a032880e2a0344610020764004050030394469032075451813442c0e40701e0a882001ca00358542e1a0034000d100d50441004005039100910f034225400f480300c0e4440b41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 255651789 1250 255650539 255650579
    0x60b090d05070f08060613201e03011d06030a0c150309050a03080702061f0e0c16030309120e060909060402090a0e1801151206093807020712020604120302030a02070b030c04 76
    0x1080b07102408090f209c5004500138004822120990807651510b00201c01c3c0107070049200390710540414020808125862040b02c100c2c00300040c01c80300d10801034018061040303001d095805074003904024180c004424600c644c040ba800d9540e15034035601d01d80004d14001c2000203912200410034441c0d1141420219000b90340e552604d81001c000c0380f60701c035200e000f070b146c12000030341c90315403550400100c04845600d540450030f00c1082d5010702808125180605069184603401d4040030481a4985030704580c8030201c007512012009131a0700c00c4840140081e9200300c40301c1140d9a81c41121981849580c00c1c250b00684501c0c44140b50400c01c448824400500380d81040d620b070540400076076000c4501c08490360200c11040300d40400c22104490b94491900340c08034804840030400b90b654041080c2007564460a1146950669400800c65901964020308401b44921540105040e0000301030b0428506a074221648251642d9002c10140400c0c1d8400c05282d1050005000310b01030840c01002c1b001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 255653039 1250 255651789 255651817
    0x70816080603010902030d0207080d020604111e04061203090e04080a141603120b1e0d060e070306060503100612020111030d110c0f01060b090d05070f0806061320 71
    0x3104d140c00007414485048000d002581c0100c0341084202c4c411310510884903d5800609007030300c0d1580720000c0300c80070746041c54411440450f01c0505081c41c40210705502c58040c1c01003215030344138802c180020a41d00700640c0420711048002403038075851500b0b0b91241b40d02c84040384c1130807211002030311001c580303980d450480303641448410341d9800c0000c09103110034000d0760790341c18400300a5113641c215401312280358000c1031640c884051404000064142e0841e050f51180e515603c28203140000f090850340d40c1d0281d01844e1000070510900c0e0b001038050711401c90549040d112180342c080d00b210594418140b0f4101d480c0400400340d805030107180503005150080d00e02e4541e44500440c22034911201c000440304002c20202c80e00402045252105075640000f00080c2d810924090403a00811211901c540e42d01100b00b42000340620003071000b406042e1107a07980e00d032186000c54581c6411219103010340c0301411b1221181c8124041c910f08900421140d0180741d056a0921030150311103009030f01e02c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 255654289 1250 255653039 255653051
    0x30303011206020a0909090c0f0506030925051e04051008210c0f0a120201020c100b040b090c0304031202030f1f120c170f1905011506030f0507081608060301 69
    0x6c0040d00801c10194800d880030510141054640030004000c1d410240c050340c07082c001c108201070f00140c42640c50000c4650703c6000034010703100c00034400c1c40e9040207410003106202c048000c080400340ba101d203d4212018130090f80d401482400340076461250003d182d000000b030808110039a10115005d01400c500707589006610784c2400e14050131403808175030540c0401c072001d061000411408000107610704c005c0d460705002141d4250796100d20a108140c42d5542c2d290031409944030fa1090100341c4025081c1403243c07034082c0c83c907030036a0003c503815408584003888609201c0d03400c0c400c0788d1140011580c00d003165112030340ca800302c5d507440e42202d0052102c0c183c40450f0010314002e07000e0079144500603a0054a00301140e600100c0402c0084228680c810a1082007a00b000326900384001d243c1c0d000304001024604116000d400101145403281c4814080400c910360b064014801d094250001404151900b030412108080102d4600985403010490800c800303105610454210030014008240 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 255655539 1250 255654289 255654299
    0x7020304030b01120302060c0a0207051215040506090607091a090411180118050306040f051507050405102f0109060c08160804032019050f010b030303011206020a09 72
    0x200050030703008941101d6404c0c0740e072000c1550410425910500b028103050070300d074008502075170700e94032070040c0b9100d900203407441004070704200200c412902d0240c007600d074079040c142489501d903031068554003014000e00000504040c010141c84007220213802580d1706101138a01080708035007220380031a42c40b544a5411040403950540644003003080d528060400315044400505401e14001003980c09034582c000c10065035401007041984150061450f00144081c0d01d41142070404052207002d541a0365801e002c07980c0e6001c000760040d80c1e0292600092100210303000e449000700c41301a81f00c896400c1c564025402c1e884540000b400d541c04001003540300f46642d501c020755040314201c60004548104000c080a2000c0380400c02910f1410034103280c0c01d20740c0b00108250f81d42400000300c4070030303503000004012041100e9500d020790703180550b0241c002803414a031100182444821030390b080640120307403403501004170380c100c42040e00314600e04202d40e0b442c0f40194001e98136a00c2400340d003880000e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 255656789 1250 255655539 255655553
    0xe06040207140c03160e0109090f050607020705010906030207110402301e10050415080f0703020118060813030e0d0602030406110301060804151b0206100806040305120702030403 78
    0xb02001c010030283c11454641000e151410507601604010400258400c200000034205e400d4150740b034042c030100c1c00c6506824450001025000010442c0c4241d80070026902d60113700641550303400d0f0380d084a2165651411026400303451700280482103c1c124816a0f403510f03138001c240030301844014403c010f080003001c910690a1003d24000c160340001000401d451070880b00d021a040010640c902c1e091000040041c103005014060103256a034040e04821079030152414020b0084104032034403410a511041d8132590948401c0b400700c3d48031035910000d904111042d00503a5140e69607001c2503501d03540000540071204c00300b9400e0214012200c221a241c5851003c111402104056036070b09042c80c10400b2106882c2c520010071405000601441e5440f045083d082608100e07003425045131901b04900030f14030181185039a298209080420075004910944295140e00d035a4020b03e035240c00c0355880b04401c550007000560104207100301c40001c84c0101d50004007902c12282070075100c0c1d0b1118 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 255658039 1250 255656789 255656813
    0x111030708090916020a06021c020318010e010b1810030b010f030c08011e0905100501091d0a080f0c0c0a060309050d0c02130b010320090907090503070e06040207 71
    0x41c46018002030b01c202c07a41004900150440c059030b4100790b0103c61400000c0d01c54500b040024030841e000119a0428015580c11410040380c444085540b401d10018240120048410a090755403d05a01c40601001841900220240030703101046200c0c114a000f0304002d40107000b85c0002c005039074040041555104a140a071400c1c003104100941942806040441c643e806000307180e050804414810075258240320000c5c00f00000400d0351251860901d04005140c408009240d00d00340000449400030780100081d5038510010409140752204a180c840083d00c401500e482400c00c054641c80384034200400c0c55200803000e0b0303085080d21070005442c02c010307a4030600c00280c40d1340c0614103009007802215040c00850810303046124060b408a0700d281026550720700465511020444541d0280c0c02c800001c00c04204588210b291000054a003500f001011034096440300e4000b8800d20f00518040703090b18402001044c04529144058004071001099a41c11035003e008a0700007412a031070364 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 255659289 1250 255658039 255658043
    0x7030201061e15080408090d050607030b0a0e040311070306090506040b0c0a090302010f0201090605010e0108190b0a020307090b0c28020f0402030403090e0f090706032901110307 78
    0x10074010320300016501d6060754100d088042c081d4036402009811000d54480085000906018586503224100312500340616103139641c04c81c0d02d480315041005004284c1e103104002545081050301c00350003d00c003403905240142c15400c1e48120109001c01d0080799286611182c4c81e085952817038580d80c034041502d1000200b00c46079402a0140010002d5403410550b0004080a03a5402e203465a031005200d90700030700c000ba05004001054400c4207200307400c980d0030707160020402d11107960350b82408010301d1002d1143c401d01d03005054600700c40304400080151001d40200c0d2421090300c078206200000c0d40040d00f18002d100400000060320030400300070b00855034020001d045601d61505400c0140784000e84d5290f820300c2d0741c541d100010703030303c80040014402003130310016125912841d003600e00310510b8101101d5000c00d501040203a80204010034420b00c14a001d4821a5070765000a5041c1c440150310381d1000c0c11030b0000300d02001e07409004100410310500d0403034042c0707908000341c1e821a0300200c03007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 255660539 1250 255659289 255659291
    0x904020906240702100e0d02100203040f06090302040b03030c03040605090a2601050f091f0212010f140103020301030c0302091918050714240702030d03050118141306020c0307030201 80
    0x104005601d03102104455440c0181020441c6c0c0044c00001011b4550741c400082c8103c0030b01d0781d41004c07284200f0541d0040d06042d6001446240c0714200a0300340441031008900c550f08116080403542004425522694810b00045050a061a8043c1da1a40000500d95001054143e001500c0f0003042d010300700c0032100750b407078860070140c5082d01421b4902c018985807403441160207011030704200183c440780f0b1103041c400c180714680d941800703a406031143c280120003600340c590004c0748400c1d502c00f40c603040710b460a00c1840204802001075099000c24800606503202c00201000903040489105912138042c2308060420910b041c500400c0b205250207452560510a01841c200102000360358003a2044126403004440a03500043c49000843c032801c403141ba030702e070781c85090034109420b49665a0303006060700e00b4461201c0009004000901c10502208144010f18045080e24815810740b1000c04048004950f550308602c4500040000100c500320b030708120b554171060007400030b400300900c2540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 255661789 1250 255660539 255660547
    0x20a1d133f050a030e06040b070c0204090b040305090108070e0102030712050c06010905060f03030f030601180314030706061211090601120e1525030b0a090c02010e07090b090402090624 81
    0x3030f000303080b1352420002c040c40e0b90041d42070001081c0e03000d083d40d40c40592494428144c0c002c0b031020501610b003000008146840f0305080c4010140c0041c0608841c00080c1e0340c9030380b00d5584040480749400c4215003d070250300304200840c0800c801440084049242d41000e0745018140c403040b0b481e0007000d0388014492540c031018803505142211404004100c01c60085090540001c440100d074840a41558148081c50f444102d2107050442c0a400440e0010340c150b104100f08807200b07031258444541142c40c145448070110300080400c2900300c80741d401c101c6010020207000180500c034140544014140440c01b0b29030b81000c0011300030700b4074804412003c0c004090200268080001001c4e00003998604a030b48581c02c0105261003a20f05440c0500c0c0c017103010001d0f800401c19115140d04040b41040c00c0811000710160150080020301141d00202c924069488005104407204000b001c1c1e88040c540c0701040161130810902d84c0c0040300105110400ca500418554940b884125150340002001c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 255663039 1250 255661789 255661807
    0x1b0306090b0307060806060309070302030a031806030504030e040509030c0f03040302031b0d06020d020f07030302030708060307060903080c030d020712020601120f0303020a0c020a1d133f05 83
    0x805040300110307050b00200036550400401600d00140200260702411307021000400d688001c0001030000c540140070340c1da0003505030034000d11400b40c2c05400500d00c0a542400180a807003445024030482d0103503500c0100c00c00070800c100251101520340390f121722040c00f034035022000901201345050040d000459646285d40306150410890320001907800c0e000030b540354801d03280c00300b5401c03445502140044c0c1d40d8120710001e10007806007030791011505402103803000c10103402d980290300035100c5031104010b55480004040d5a01114011800090f001e103a041001800c43c40c058400c2c1038450003074030708060f80400d601007281c1140206440070514052a401641d070148074841c0035100d0301e502841c0e48403040c4c0341c82200d01000c807001403c165001403a00b421078070079407403090301e540d000304a6803c803541d900c40241a26012a80c424042003210041200704902440ca14845c1d0780c8180a403183d24055a18a1540c0c4071082c8145100c2194070f0004010b444801c00148034100707140c9503541c07a0f500c00303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 255664289 1250 255663039 255663041
    0x151306060803580e07140409030e06030a0606170c041403031b07150819050c04150815010315090b012604030f0c0b040f061b030609 58
    0x5603214a240350010480c850ba0603016014038120740348290081c1c543c10058140e20040d91031181c1c08400d01241d101000151001680414421445030070414001d0300c85103105151654824411000c50240440d100c515070300b015084910510301905080402a02c0503011503881c1d4400c803503110000356125400e0000c41d0b000b080c3c01c1c03910480603294642528103403044404a200c3e50107004151003444402c1c3c50305907801c2045648080764442d403440d40780000020b0581d565540d000f03e80c0b842801e00e6140802611904c45544034181c91009501d84064001c1d013100101405042c0082d881010000400c215030012151400444640d071114000d242210950004004140300702d8100741c24240120b000a444441e0801565001100098103020420060b1031512840d140d40d10004103a03800c00031191050740c045840f4a000741c0b260300c0d4800c1250011580e0700c409900003843d0344401801b04020070f80105520030100e206100c001020005000000d59801c089900b14000a80702c110078000142c2e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 255665539 1250 255664289 255664301
    0x304050c041b02030d050411040213080f12040b070c0812030a064103100b0f040504080319090b13030e1e1302070204020403050d080603030a0818151306 67
    0x840c035402c010341128514025124440c0b0b810304112181ca078000b150501c0000d950410050000900c115500c800106904004105500c54682503000b038035900c46160070045280445e074030101c0040c0d031515003868035401d01d9030007459043d1116480718202080080040009080141590060740e4882ca0864034100503699290015080d00da840882048101c041c2080d0b40949500c0010000703159054543c1c03110140c240f08007085e4180700c0e9040410b070f502035a0344003003c131507000c0e6410480c0e4940141032205030380042e600202018010000190510341d403000e14a41100d9821000c2010589919515246102030750150424032000b0315038030400d03801480d00030050906450715280b21722038076044440c01c0071561001d400342c01403400d840581d01095048400803540117000310f403680d032241403283d55224078075a04400715500320003146452070b000050301c401d41a255200182a92902c030b14555038828084240c2240c400c10340000d1801d0034106001e4401d000031106400442c03c207060800079a07070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 255666789 1250 255665539 255665561
    0xc060f1107051209010e010507021513030c05030604030504030f06020d02040905010918050d0e01110d0504060f03020903030a0e0d020d050f19051209011e02031b0d0e01030f090501020304050c04 85
    0x800b045030f9041381e40c10404030402c0178000d0800c1d81d1116941d00110341211461045000a1b40b00059081d01d1900702240d5171086c1c0c1c0c00f400066035116103a50074160b80d014182d0f8043c0201d041400200700240a844522907018864000981001947d0f10200280d0300705400441c003841c0c03074200600c0f01d03407032a108010001c650f00c0040d000c054429196551030381113542c1448100141d6010f040b080364050804070010403440320498024885a1300020038a800c64000d49001641d60308041090350b109000b540d0030307030a0090145180c00303210102921452241c0c2d000d144c00196140b6001d0140e540c20813a003102600640c0942514a41564403a0820480208003000c51038898040400b2480000302d003c401104080324036034401907980140c0e5000c614010f4080d1700400b45000240b05640400500800d400c0a440001c40140d042d09498135200d490028400281e04081400210343c071a8000c0105072040d910002000c00c102d44410b42a0b0b401182c0684440e07000b151b4070309103806d00c0c0c820316560034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 255668039 1250 255666789 255666823
    0x30c072d0605060418080a021e070f0509011d10051230070209070e06040f0e0604020a080708040c05120114011203022113030b060102011103060307060c060f110705 72
    0x5c4064503c0560300d0070043e80900640e8000c100c036103c80d4000c101000c0034680c141d6404100f004140e4403d6a244000d0181c0c9c0011000210002210b00b000800d05052720040c0c42c4003c0a01e00a1242c0f0254032001031940703900540080380010640c64265440003005e07100740140040104407000c150308488a2040b20410380327020110700620b0540c03202941c1c15150b040315807100036112a1800c840a040c00200c0c1e540c482c000140020b01c1c450701041d24012904180e4000c1d040e940c520b81000103d0043e0756800b030200d0300c414001141c540c030a64145500503c07a10020414603241c001207603c8001c541c1e101e4034680c1d90341c0c50120440b0039000d00301e401081e24440b814405403040e07030000d4075003402142103d01c94034a80d0301884034810030410b403040000b198102c072030000e90b2410034503180c1c00305540c0346000d9481c000112000e421036800316032141c80098002d0040b6440c1420496850026003c16103030541d4400b94000502282c1c003a10011458500c1102d840b021141001424640409030120b001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 255669289 1250 255668039 255668051
    0x51b0316021b100305060406030b0c1e0f0a0315090e070f08030a02030906070c030506040609020405090a1e0206070b0106050712050307020c09090c09010b030a0606090b030c072d06050604 82
    0x3c2c1d031000d6203d0540009407a0110b2651500350108000c5c00f001e0f000100342003d08000c002003a10404041c069805500301c001002e02526036590001b489049607020201e141080f031004403600a0300416801c0400507020540203540d03030420b5085400c03140500506401c201c4e8200503420740181464054458100a50718042c008803000c0d6507407040c0307000d5038000c6002140c040d06100b01c0d00c190030300035a00081036801d2468907191010040c800080100e219a161101145280b02e00158070055958000c03c2e140d01008141c85c254000000b40c1d104a034054030420402002441c144002030007864107032580c549030000c41c5840e00705041a450796030708108040c0100031420798002040140c0c3c04065901d04402c2e200c60054a04041c055014550000c1824000003000031521006511072080200104040c948a4030111481012482200d404c048103201066030b03a08030b0790061002d0740c0714840826040040b041c40300b44400d642800ca44040310084044028011036010302a03202e60200d4040044e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 255670539 1250 255669289 255669343
    0x140d020705132706020a03231b090a03290403090915030609030c020909010e1002090102071e05040c03110d0f15180c21051b031602 58
    0x41211150b02c0700c0c000985900041c0b07030000030490000103902c401e4030314038046001c500b00603000e580601c0040000030701c0d0011846c040000040300721b400c110301d000c1a10168907034a50b4248280d00703180040340ea00700f0801c41c0001e169030b1407100c48025403141c00741b07100c2e820010740c1041d4480300a40d0402c0c14014010b01700000a030b0301800c0c00b805da40120000044404041d0380c450f2070484580c01c01002640380c648c0510505030485230742640b19200f00c038007080316a07807a2201d13400c0e80c2000c80e114130f865200101c0d4803804112174026200d407200603c1120f080386d5650742488101500c0c240c90200c40d5000381d20610450030903008080100d80c0d00c0c1814083c0d40c41e090032088147c855051000c641c40e03512000402244007540080a0048240b9000380c50182c0311441d10760700304d030601b8030507000c42c0c0f9124503001a02d000d00309504030840028440c003441480c1e00440030140500400e03804903c0001100040c0145014002d18010f0581800c5040c5482c0003407070281c2303015100c441c001804540b01283d220313 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 255671789 1250 255670539 255670549
    0x1005330a1b030e040218150a450e0a0b010c020906010309150f150e01050d050102070210030c200d0c1e05010e0723040216050604140d020705 62
    0x50500c004020010800441d82401c45000d541264020344c0b05000080482c001d510032080c07201c00c034401700c1d8240580c50a0a020406078030500307203180003140240e1299243c000d51180d00b40c4076507004d00b010607885841810000011603d000e5034002e20450210309200e454035802d803091740003022020402c0040c0d071110019181013501d00f0001d12800d02c0000083c2d86034803e07080341001c9d6901001c800781c0c5000701000c5c0406800210240380005241580b08540081400200411a052245240980e90a1030184009078040300c8084e1240d6400300a14001a00e41d0b1800e007105040b9a6400102807404550091030401031085a42900c4000b8020743b00e000030100d0f43c01406425420042c00101807031602c03d030700c0e4280d0803032001c0200da400105000d100043d00a11014029003080d50001c540720700300322540d465070000d44080c050f050801c440c03403820303d9401842840901c05101150300c0302ea0f9204d526107a01100d0807100900040347c0e950030340c1c4080203085c900711820f002900e941820503000c03070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 255673039 1250 255671789 255671807
    0x302030a0f0c080d0e01150305060105191401111501080102120f07090e06010c021512070801060804080a14210604020c100504060b12010c120b010f03051005330a 71
    0x114140b03940308501e25040000354400d0700b40703d010f0240c1c21081f1390307070b81003240d1209824494107001c2c20004080c0340002c00e96484240603604500c4082c0c070950043c9004490012443c041c00c051445150481001242c044004174000c0003ca0000741c0d8a902540400d003900c80050502000d106c0b07d0303000e004429070400c1c1000180d5500041d90b22541c0d0394400120b030701ea150a40041d400450a9030410001c020740c1c4024910320909034a28003494480740e20845034980240724000c0024101c001090024104100816000085192112a07003481070401590f59200c003a410041503ea20001c10b070340840340e000d41e0741c0034004690460410910960440c0c540c480088105115a80c0b9000203007008a40d500c071185030390700a8602940c10701058171050090a002c05075901107030308403100500110355801140e48200069452540c000075482050b4041c00002e0150a0101031004011540d5203800c02a101d003032031000d0030104003d005100d0340700544504044901c070004100034043c1403980001080b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 255674289 1250 255673039 255673057
    0xf0207030e0904021302070605160c030c11012604030e100c031202120408070317040f12140a0e0108010902180d141605030d020715031e090302030a0f0c08 68
    0x10010b99610f910000d0410280703801003610b504c0c1b01041903002d03c06130f54000c5114018031000c07500c015036400025103801c100304400400244100c424840007a00c0705c0c0c441c00d00c40d032040c140303241e00c0103d00702c0035800051031011070442e2a8601c1c007084103140d4070050007404141c0c01d440100310a00380c07040c0200203050304d0b000501880540302c3c500305c640c0901e038110307485484c50402c180d48505041c9400d0143d41d000c0714054001079022215801d0000300d140c081c500855020302c0d41501d80e00c096488241c19001861031800380282500003515855070710000f450b80003843e60b91005801011400074107129410b0304000d81c2188144410f1081800498001c8007400c8201e0340c0c80c200d040580b510204601980302810014021000702c403140390284c00000094540460035a98216030700c0340200d0303941070b4078490050091008000501000d0090f8000d4007600c0e62000d03031031034850121500d0015200c40200403001a80001404d0b0400c03907020126101c1003010b071a140700915203a45411aa03401410a5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 255675539 1250 255674289 255674299
    0x290411060a05040801061d0a05010e0a0b01030902090408041706010b1b120d0219020c030c0f042003070311071203020a0c0b04050c030c010e091f120c0503010f0207030e 74
    0x64241a8050003e803401400c1c4a0004d00030591103019019a403025121928004c003813403808124031002074004c05060791f106640c80e51240e41c0318018035029095103500e60b41895030b0380c0000307005621002e603024070903401112003d9890f86040c0c0c0100c1030301011984c04030680c2014005010308904001210054510101c40070419894034030b0880c00c019201c107803100c5107580059000084210703a005003810b080d030600040d6402c1c0490300280e840d1a00d018046a2603042040f0010282c5420303182081c06090160000442c8070850481403001c0200c10380c1e10040d02c6001c010800784503414054410707081103405a45082464580e90690b0071030a4100801c14540c000c50702407140ca1268100b502c031590070002c6922581000c1c01c10988441505031098003a000311460b04105502840c0010201d54014040e012503a441c040c140104802104011100c0c03640e1b03500c00242030800703014640c171050142401d0300905280904040c21200d0401c00a00c05500503c00381c40400d81000021400c3c02041e01d0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 255676789 1250 255675539 255675547
    0x10f0c0c0b07081c0609060f06120e010e0d0201051501020a0308130302010b09070302180910140a0b0a1107060c02012a150e06060414161205010329041106 68
    0x580031050f402401d9600385452000b4a0021804c685604142d00b00c3d03644501c00c00c0005d48a0a0b41c402034100e0780602c0300031400c1014600385142c010740c084090084040000920a04040b203c40d08002c3d03643d1100005039110801d010040e050300322510f80000d024002800150b6080d9030140c20f41c00001d0018080ba0071610410b814507000790069000341100a01000c032600e40300d60050000c2d00b010709074040780e5240642e00c0006081480780c0901800d00310300000c041034504110390848201c0201d8007604211119030014400007002e01030b02c4070360030f2512103400412035400001e29103c01e2340d00000411001180800250b600700d4048405078108003c0c0414007440c0e0b40e00c0f203200d907a00c000300600706004901798101e50305207948a1503070078401000b07990305502c0d010108815500101903080002c14003c0c040f403525003422180c041c00c410710b8100f612040200803079200c200c1e4000d134419070303082c00c002400850320782103a116008002048503601001d0f08180c1c031000a4032045501d110f0140b0ba00107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 255678039 1250 255676789 255676793
    0x10513030503043305090d0e040903031509090b090120070201200304060212090f0f0d17042111041109031e010c020712020f0a051806010f0c0c0b07 65
    0x506101d000107142070169500100d009580711064000130003c221003032401c00480c555040104a40e0088429940c075401000010800c10004042c1c03803004509243d0b0354806003180c40820000742e0000c05440d600010480c0c203e0400b1000b644000380072040f40d0b40f414258120501e0b90300810890390844044894880d5602e10058600d80f4440030180440c1142c0c845e01c80c04040004004d000b0b44001d80d00f0f5848114070031401d901c843c0280e10400f580803094040c10406420605000007550340010a20031200c410f50b118074440070080e207120f0f032403810001420321046185030800910b088040f1100303001d08045032030701c0055910040c6031500c210f44490200d007010701900140c8484c0e00004068a030320f80c9142011038412140c2e910024001d500f40011400202c0c00401c0407011200035121314840c0e17142960130020440b81003540d080c0c3c0f14144440100d0313281c031200340d11407540210b503c01400c41c2c10309800140c801c0b10308180c000204494402000d0001381e240c0d0444040310007680c2a261150f54034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 255679289 1250 255678039 255678053
    0x306020d0f09120e0d0209061302040b0f04063b030c060c150f0106050a050c01020706060e040614190b040b12060f0604150501051e0409060e010801051303050304 71
    0xc00d07048403401d0510222209018041a215060b45040d07258201401d0b004030a004030a500078601075440880783c00002c0f118106288002c09100700b140c4010324084e226611100150009046102102d2000c2814811141c111150010303000c0c4044210a00d640c800f0ba41c1800e0440c00ac42c90744143c035810b00901d8450310b042002d541503001c010051525091609440c1e603071440c00e0350810115119220101e031458001480b558183c2e1036943c0c500c0c0c9060042e1409507150b6000710300c00d01c0c50b50350801121010a00307034441c0d00064420084420101d04007400c144059030071022140c50480d8085041c041c1d8801c19a0858215034400400424080030700d00000d001003012020194103ca05040c3c41c1c5c640b03c50211300c0e2489500d0310b1990541e1500c400c01404211503180420360b1000c01d03800b50034000d541c0290090b103100c01a0442d801141811178071002501e8000b40d0083c43c089840d40014071005110b8441c03140035000f0017008005e14644681c000022440003e80903062001c000041014440a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 255680539 1250 255679289 255679301
    0x603060b130312020c0a1413020c06040f17030408070b06040b0a090b030304030611070506010806060f01030b0d060c05250b01150909090b06090703021305010807090f08010906110c070306020d 84
    0x801800745c0380c440c0d60303403501f000040500300c3d4051090305e039446589600b503403078030035651401d14040040020350703902d56900e8040420081c05850400d048605407568944901c0198444c91003815410b40f01d04e40d500c2c1c900e40120000d00f040d4030460070254408081d49030417080e0b90071100d5544c000302e1100c40980c0824203512850b00054441810510320401141d21040244100d92042d000c0300c000f41c0e41d40003002e8030b854040d100603a01000070841100650b1080c0c2000d00b400320001d00081449015a4401e003c5511040510300460004203a044030451202803c0303544242c00240c0c40c241c1c44142c0d1700d00131400014011842150040180a030300c8602c50a405006440d21039003c010600c0c550400400c0e80204440161084202c403000981181c464025204a00f441c0d10107844464101401911140d2000b80382104000a0a00002d0b165103268001d13002004203c00009180f01135003410340c195454080340b4a10004104000304996000103000c00403250003050060b100c4c0b1204001c1030103410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 255681789 1250 255680539 255680563
    0x30729061e0301020708210c04030609060615090305061e0a05091f021e07050c041d100e06010506030f07050705031201031212110d0e070801150603060b13031202 71
    0x210214001c2d00b00304031a0000c04644075508940301c01f28040440c96042128100e40014054405100c10000500244c11444485206120200c0e100ea00c4851414812003420f03c0341c00000c007044c1e000c2050180501c40316800031160090010780d070308200381c00340d950000030701002d1040365544001680e0950500060001c810190a41080208082c0c0d00d00081c0d0480c00b0840711401c01c4855180044071440704a4a0050344100070b0300c500c0044004110003800801c03a4800103100500c0d00c1890702c001400600344d202e18072040050042d00d5101d807075185c040141c2065015039410014004021000c00000764003800350b280c29640d0f0b409c43c2c50402d0460043d8803804007840c640c0340020042103000250420084100c1d82c854843c2c1d08406404000e642c06103a40c1c9128400401c0050140b500360341018801141540444a80c0ca039294001800c6540942c1040d490403038102081c8001d5606014081c010807204000d542400b003c00813044c203092861000030a800c1202003c040080e0003030045100e054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 255683039 1250 255681789 255681791
    0x18030106050904050307050c1e0402070f17130902120f100803030403051804060303120207030507051002030711010c0806010c021819060603090503070f0c0305030a02030729061e0301 80
    0x20400f440c00b10345d250408441101d0358010103da840a5062094001030701d11454010b170603180c480d07078017404020350000505603001a1460002800700c0c00c42203030348122a017445049030f501d121041010781e516001d908491503060040240c0211603a09e1402207411880c20708900c10380d510340c1d50401807100e01079404400580000f00802003410b41000152040081c00e404a46503240e49201308070407a015404000c0219044840da102500c1c001c1e030107050b4140c0b282c1000c03880c1c48281e848403440c00e007603140d448060703a400004020800c0d0340590190b41c00156103000344887c01d40305002601c800d100038891410008090102000d40d91410442608000030041054070b80c1400216403600880803030b4101c800b0340c142200099001e10a10030b034101d1030b801801540c102649941c8103480f0620801e020307983d4001884003c00420001e00040c0341e00040f0f50003c540d2412285040090880041058038107401400d6070790580b80e22240c001503100c0800c94281d21a180e640103000815540701605c0c2d038040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 255684289 1250 255683039 255683041
    0x131b0f1403010b0a171c0c17070f03051303060f020307020d091805041a090703050c0303040608011802120705210610030b01091e081608030d0c020a0b0a0f051b180301060509 76
    0x786402c2191044002e01900c5507023182440841042403038410480010300f42007020400e400404d2107800501003010070544002d590650701c3e01e0f51000d0328000d418401d6416400020300040710380410810006004600b0200e048601c0e00c9a800040a00c800d6000502e9448074000307800c0128000030044e102031816590025810485a0389542e0100c502045a442c4266002108140f80000542e4102c031038a948094091303003000d00034008010044420381c1c11036002c3c1300c0602c4a00050044d10b01c11002613a5a94440900c142082c25140c202d0049440600b041c00a001d1192100c4001e1078500c030302d5003004a0340703401844c0100c035505203d80c030580c0c148160452039555015140d20480441e40400308a5103030095045002030500c0451284c02d90301d0380100424075180000d904441000042401510b0b800320288d140c00450175801c075076031030070180d4541104156120724814181c000c041d000096201c81003094196092340314844444140c0c5500d804039240079030b02504840e000c0c20000e40030703900c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 255685539 1250 255684289 255684343
    0xa0e0d0b0a02030a0e01020906180303040825060e091f08071508150904030c05010608070e01032303040519090207031107120506131b0f1403010b0a17 66
    0x2500f080da90310802d242840c3c042001410140281d80c41c8603c0142800e1400e00403820349950000031000040d05400305000006138200103001280c618004100220001c1090268507a0042155040350050061186903c40030352110b400240e80101c8412441c05041d000304010740d1903c7c21580100c0aa1088034804210000c40013030701c007002001a2034401e00e07500c4905484072100e111842240d041801400000ccc0440d1042c4da501c0201c074000c000004080c2d0711402403600b8104036800c24841c0c0c0c8800c00c0100208150041d83c3c8440c0c1e40e000c46d5680d5025107900006899110f01e102d80c0d0f10400484c02c507e002c5002040820008000181c421540d800b014035000c2c01d9403802c003442402d00c1c028104001140c1040c0e420800069600030080e14640d62080d011a80c140503082042d154000b800180c04550045203031104040e0001c19200d151481c40d0040c0d00c05004c02c3c2c80c0290b4026410201481001d4a07009144070681e95003034042c80303a4148142c80c0c5407030035022146520801501c8203209032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 255686789 1250 255685539 255685541
    0x1e03090213020c011103040f290106170a0c0206010b0a0504090603060510050a03030210150819050105090106061b0201050c0a0827010c030e040b1008011403010903050a0e0d0b0a 78
    0x4154024400a00031030a040c041c5c4602c6010441e40541203451042e0b01c1000202010a4035060610298409034001600b098074505a6001d8000e940454645182c10b03501880301705149030321501540741400011460007009440d18018414000070f19008680004a103001c0e0007070790040c08595104000f06652810100c0203800c0940704c0110402940c8404240c070700300a40030005036a0150020543e401d5a0480c03440280320401e002c01614041000106400805002c1c1c10003409404840b02d1090348113080042c21150083c28480303641c1e1401d08100b00164000c5000024032a00704507101c2d4140d05400140c1d51841000781e030351990301401e05002c00b000341c21405007203540c404d00c0e000500c2d41241074000269150344d020700d502003004003d203540041d224001c4100000030180010944c11074003400b24000340c000c500f09401041c18900148002c038252940c00c5805a403c038001c0c400c8600d00c0e02c1c0034081e4031405500004001d5003841203c080c0e160400120134995100d0008041840c00c926884 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 255688039 1250 255686789 255686797
    0xb0603060c25081b01052401050a050904150602060901151a1b15090d09061709010b060307020a02011112070b0c16210801050109050f0406050303030a09120f1e0309021302 75
    0x400f02c02c540609454500da0301c1243c00d00c5008040e15418680f060144ac2500c594101049155000c1e41308c51035401001da040140c41c2c0201800c2e0020100c80c106084203909462a0080341030300180c0c1c02c03004105250081d007041240c02c4180c1407059071a511000314082c2651440340e2411b00d4811341d100e01c110361000383c85445c0f24401100c143c52030078140241c1103d407024140301d55000100100801c41800ea0344c0c40c155a000b000740800081e6a00d0480e000c2000390b04100c0d82c2c0000f50300280a04800d65800c2415150f070b040351803000e890120003a074800c2440380600d030005000b44412100203405116501e00300d413080c1248a6140313112012602c0c2500c01440074000c041030b40314607030120110590040c0d4540c2d050724416150841c1107420070051000c14007000580c0d83e8066119100085e164a007440103600801c503404000c03a0105403411301600e4541540800c10030000a17001d098046a840b0107400e580840510140c080e03550314220480c0605182d5101a50041403040c0a0000d0300155000b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 255689289 1250 255688039 255688051
    0x503090a080f1036060c031505060702060415170108031306211107021309050c030307030c122607080109020405060405040203220b0603060c25081b0105 67
    0x10380f00114044070940c2510010045400b0010005056070010142996a420b00e2031420003a203050507660f4a8410560340c3c09150035000c684d0720100c6456000c4070540590103001d00395400c0b0b02d04031310340d40461103a12035807040080302001c40004c098072510038003484a040c44900c1001009503102c10501f03031a03a0210300040c144c80c288110004003103010b0707036070032031940c9110090004008032502c4d50f90140003c8003034401031880400c0800c00607500d90078013803030001c989600051300c41c4031860030707525200c0403a200174070030f6009110450000ea40203049022041d400500c4182c840d92401007030784c00410381c1da2503400d5503100420404003008010245803007440d169070b0708006a641c03070035503a0403032140c0d00681f60400c0d001c000c00c0c405400c0c144c00440d00030840c1004c0e010600c4180e8421075080000d50411901d2051238014040c4520b01041440c0d0490f011a50007440c180070f29400c00c1c800c07000001000d05400d42060202c0c248100c02055507d03200d4481d507010890781042510718001c000c11120 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 255690539 1250 255689289 255689293
    0x203040806060406050f0d14010f0605031212070e04140403030509010501060e0d170c03031003061b0816091502150903070b04031404080114061309020306060d0503090a080f 76
    0x15031149403d0041c04c3c200c2d4070141c03003200405031090500040201c00c50040d540c01c00914036102000c1d000b4400c45c0055014445c000801c00c0c10001050304000c2d01450300b001e41d9606001e507103e0b90a81c114416000300090030444e2802c1d40250129010740794210311b80500c40c03182310411040c1901500f1161040f20b002000300132030b81c2c03140010f4454030401c00c40759030000c0f91540c11100141590b00781d901488074130154a400c144018500381e14651045900561504110f541007081004500403c2d120704513243e04120000b0074a08010300382c220040c00039041204080140c628a0f000d0f20f10384010f849078020301034441000e1900a0f643d58000746038520460b089500007191403102006030f4801603444000c1c1442900c1780d407412110228030724406c3c05612410800081d5101e802d1003091202889050006145d14000081024510b45460303a8602c5d0b609020850b40165800304007203034403c80440c0d40c400100c8282c00d0061442c01050841c079040b80f10f045000c0786410300050700319140319103035007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 255691789 1250 255690539 255690541
    0x304020f1905010f020c090414070b0405010507390510030219080405192102061303050c010609060308030405010617060106031d060f160f1713120203040806 69
    0xc01e201060a4103200c100140038a201c080c01650310501105103100c0e44c901c104d41d00708a1010000f1340c9404251b804588400c0081380c0d03445020001d00c00000140ba04558580c101860040003a205110b206d000a22601171440004044442440c0380001c100700d00d11800c40a1007611104113000314103004191284d40400c00e04581c1c58464002c45180002c40002e2074086d554035401922014005442200c0340d0103501040c14008282c0d009010103180906844941070814503020b4000202d80080311045400060420651010001c811045554907180081da1203c604032010b0061099401030000300e42440400814800e040c0091070044d4041d50080190540d64180c211152806014565130307504101c0042100300d000c0e6001c2203114805002e01c000d800c2d00602c4039803c001f0201c42c09042c40041c0c7d4248903080d06030390b400700c1e9540740c0d03820440d0300b42d40d00e03041c00743c071008000007603000340103844001400403070b0007101c88079009610090b031030150b42996070003a450782c1090007010b08500c80e03d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 255693039 1250 255691789 255691819
    0x20c1c0e0d03090302120f0f03031f03030e0904060b03030c030c010f05010e01090c140705010c09080606010c060e0307050f0703060f05040b0406051b130f090603030219110a060302030402 82
    0x1c00c25141c5035058844904051443e405d00c89041702e10480b02d90140110401314003ca0303c00e000000c4030f87c000304003841d034a18025801c9a10711143c99019140701070100c40c10301c00031f600098156a0300388121a09105640c0e00e2400c0d07005050b0642e0300d29010b01021074440b50f8110008040e01c4c049807004001d00615000c1c1c014042140c0c02485140085202c550040245a000360b201c800045850b1030f0024444c1e09610100b01c2d150700032113040302e040e1364941e5441001d0781d010352498083c1c08010050400390a2a10009205000e81710f40603046956400312452032200810440e61079039400410f4424144100381c42986541240c881561550304000c4007040c3c442da2751140d540b140d503020801d620f19840c1c0e40c548400030705009100305020100c071105840c410064401805401b03500d0910a240c00381040c1030524a190035a000300c9088c1e09003201400040e40100e00000c00c06905108240012100e0034031a020610711010303690403582641010480d039505d900114400e40c002d455a0125903544 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 255694289 1250 255693039 255693049
    0x50a080606010813050a06051005101403150307080f0609060c030705040b2101032009040f020d080f0d0f0606020a1101050f070b010b0702040b06070b0c0a03020c1c0e 73
    0x450701c003400030f10b9410010311040030360803002009502070307011030b68000d009590700d0045038401d40b218140d03800102410821031500b40d4244004400510b012591080311100402145c00003520700e00c0070b000b41c5048141d0301d031000c000c0040245601d00c01c4070b410600c00203446446a0050359604158001c400c00a0544c040c02c0301183d014013015590b841c80d16103055803241031600b000d0004c0c2d1104000d8142d0038080003000100b02c2c003940c09140c25890400c015032140500e824090480b50140caa000200700102e840c4010441c10180c05035400c10b041642c901d032401d1035108195901c404100049610504649107600141ca81d0350280d2040000b19199002640d40d0749016100038501e85122407031401c55407068010340340c00a95408c0c1c3e81c0c100030541e524101058000d030490445a0340201d20300f400d41c0780078020010306103021b60b00e05260070026116030400e1040101101c1c8040800546100014403e0f81281c05144c070120986400825a4007440291220354600c80002046040d40400078980 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 255695539 1250 255694289 255694291
    0x4080c03070f0602090f030714010f05040503030304030207050f010c0f080306031504030801060311280306080304060c0203010c080c040306050415050703091104060803090103050c1e0703140f0708031801060b04050a0806 96
    0x30b06c4420701004201400110341322f503458409003041243c28400043c04d03403000c00103180542c1c4240c0192010710b0402052001c05800d1411b0355040050700784d00240031620030f01100d0b00340d40e044000c49503241c0d9003001103440c0c42c0c81d001b2120380032003110b8200014075521075080350684150313540500c8902c0e20390a842c003445c0079000302e4480350607090341c908444034031891040035007034540d041c0824510754070031065095402a070b1101c0c0c0030802d589804011803400b1700c0b950340000e1090401c6070035803d101074600c515008501008103995610030100d42884402c2c076606038211044a802d10907442c00d00700090140c01c4503602202c4060071003414002e035250900400381903845010040d410724080d14011009040043c1c408442d4034020402105a82c41c0da6501c211450f86054002d6654041494000c02c0032040180c581401101030104400e0040424100d48540d50041101610307921020f251042c001d0001070b48144544c40c04000058114140c0301034000c4500482e560341d0300b030350b680101b1521124 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 255696789 1250 255695539 255695549
    0x902040303080606070606030503031315061203140f03010f060e010e031c11060702010509061003020d02010c06290315013b070e1002030a020604080c03070f0602090f0307 75
    0x100400010f040c904008010b00040d034003402c000301e034203036880e114141140c0c425a60341780420340450b620024024403058950801c110714004101031890b00114154156074940d0090401001d101c00d1085c40f100001542e0b41c00030041d6495580356900c07406a180c02c2281d2046070042030b540644600c642d80111042a070541700a0040c10031400483c7d400410002d0320a0b0507418000c048e100c98103030550401645204d0001c0d40c00010380c41c24550499481c1090003440d11003034400c05d80090005071100858001034650a0804201e24a418504100a4001d01895130b000389007450b40c00298803c1d04d008d143c8804d1b0b0580035103540140240c0410132405090203003030010454071034070342e2141d00c013001900c00401126100d01403010b0340030b0301603071030300400d5604200091000705044c03860314060201c0e00c0b00c005180000c1d450301d104120701a4485400400c080c0480e000440d0360303000c280042c02102d01c09a400a80d184100d880f51a02034002d4100c001010f0150300700000e99141800c00046032000d41d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 255698039 1250 255696789 255696797
    0x9060f090114010c060e030403110307290d090b01090c1404030b07030b27010906060206060d02030c030f0a06110903060a09020d0c06020a0516060509120f0a1406010902040303 77
    0x1070b0038802440c5a41c910300050703604001c4007181c0d90300418035501c11900c01c0301541c1c0203035998520718100301303207100d0035082c2c4580f03c1e401480042048064208030f070520002d0041940003545c080445490700303402840500728103141040d440c00100000c001c143c03410f8803082c2d04c0c10410708507a080100c3d0f06a40041d01c8001c2c0050800051001c242c2c1c80440b9607100020340340104100d4803450110f01c0306041c0342c00604141c7c11000e0425041003060390034030f02401c0311480c20001c441c0b9001c8002d6460700c0113046640103c4414044000355141071040240d510030103400c0340c0c3c01c01ba21111b11556404000800d03900c89140000410400c50b03544116100742100a0040000d070722040c24000082001c00c10482c1d000382481c06010002e14412200e50040c40150041c0034080600d0414509150054000203140c00b001c01c002d22403150010305440314080141c8400040201c500c0c18a0301d07021540b03165000318465400e12904011203040748858071200300040d01d50a90381d0300c0c08002a030140d404020007207 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 255699289 1250 255698039 255698041
    0xe0f0916050603040f0f0b0702010b061312050c12070602120405032806051e100f1404020c070e07020f06090709020906070609030518010801050904022206060c0209060f09 75
    0x940b50030405143c1080c015003e0016810307659035006280140502c089940300c1c600810040066020b11400310010030030f80781d091424206141007101614107000e800c015a10400368481030210400c281d03541c0c1d04015181c40000400540c1855554501e07224000041c031a1011000c82d860709801540d08840000e0000d000e04034101c11610740340802d0383d09100b402c58100d10a140402c07114040d042c090038030cc0b03034041d44081401104030311000c1d004102c0c01241440e40000c000c0d01c0003806001c2d088070107803510900b15105000000b0080c0c490a100680b25200d00300d00415400c181c1422640200055000c5604000c3d404802c10b480b4075040b104071500307030403080080101c5002ca4005212018000717104510b8031403280d0b40c03a03045132801c510980001d5002320340388184102c01015144001001d080c841c0c0320f58908000102001030003000280a40340c922629100c01c101040300c004514060401480519110701d00103001c003101c4001640700f107008002088041c100a40c401409490280c041e1841d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 255700539 1250 255699289 255699299
    0x15020702281205101e140403030b01080405150a02070f1a010509240114130306051003020f040e03190e100809030a0e03191a070806010f12090c0e0f0916 67
    0x305001c10700d100740180c2001c01d4019907281751141004034902903068090b1410113090060445c1c400ad0041810b008560b41400b0100d00e0001d40d00d000240302c074904409a50300c2c28000c8010f03015101d0010b0000d15619030384000c009a400b5074480d1071800003a4030b003e50b81e0301e42c00c2103d520340030345d1958018940384255041d0f0300c0b10405014010700d41818412040e80c001c915040b00c59208815024500e44120b500788100441402056004403540c0b1580340807500b560000340c036030b10041c010684900e655150540309000b0a005644810a21000d0212a10390964000d040513810301d903a42c0c4150641c00c0d02e00034a030b0040e0010f50060684070000c608284000505450b0405881341035a40745c4a9808515160f6548250481c40284101600d102e07000303610503550344801000c0c013581c050140100c200030050341e0090010500c0803040c6030591442005400880081004410160228801c92b00104d0302030940c0101d140122901c62204625a50b0000001e4451000e1a05001c00300750000b01000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 255701789 1250 255700539 255700541
    0x305030409050a090b181212060f0111030a0819090b012d06050703020a1403070c12020f090408040504060b03070807020c01050a120f09050c010207150503041502070228120510 77
    0x207150b01c40302007220445803a006100401e90886001f1035440d0f90468100015824200040ac02d000c0c420b0030b1918007034920300540d5032030b4000c44608804000c2c00d2000a540140c00410001d20180006400c00135441181032001001d07009025404000681800f1b82c4011042c0f010b000340b0140c0401c040b14810703400d2000840e540d0340080c20503802c44c416400040049100005140740180c40000116603440c0d2503e00700101d80415440307144404030380300e49400540ca8903814412061802c440c1c01420b5940c51a20f0704050180da082a0340161030300c2c80100381c4104000c02035005411980315500250366612080703035a11410551603000a005002c0548000d0240c010416003144005000c90050000c501d000d0440b0045142603401d43d01040240e20a96010b0041501501380c00007010300c543c0c1c440c18050990b01c00940000c055031910448100f252a0a80c16100111790050000c2c280011400d10720620030040180002118851480090040c0c035000c4114840740e80403011381544018a08544 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 255703039 1250 255701789 255701821
    0x6021e0909010e070e132003160e0a0e0a0203060a050d0210030507350903030f06061b0114010503070b0405090f04030c17030a36030504050a0305030409050a090b 71
    0x20a12a4071170070740d40c083d03a8804607003001051072140041d450310516a405070307034034180791000c080c3d000070000c1c031142ca00d581d080c20b1000b003031a0820714080d014801c041007034607049502c5034448090314001d000f04205540c00850140380304491070000c850301c91080010b21010546c000354801d82c08000c00c1e400c240660000360b44945642001215080c0606207104a110390840d150882c06d506c2d804a140a03545081c85500105c0742d8001314103620b0003480d110150603000d08840d105040c041050440c0c2070b080a0500041d50b2020001c0c005a1500d403060303020080b081c05414401d004081d8041440811b1600b60340480300700034024000c179298001c0c809488607014006030104003407192240301203550b80032040401a5440601a41d83c505040c8010032220f682e0140890b61000041d40503240520f40031310a1803075403100c0810843c1c2800e24050303501c0e01c1141d0050b40c116203089000014850701001901c12164120390500199403080507000c11906c1c00440208404000384c00b140741c82e140c0c21540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 255704289 1250 255703039 255703051
    0x6040204090c080d110d0e0a1e2409050108161202250b010905070f050a09051201090b0a06060c122105040501140408030a0c02070b0706021e0909010e 66
    0x264090700c0c0d500c864107000c030a06404c404107590703c54007001d2840070401c0350300000507403400701c032545040400039441780c94910030054070f40e02c000304c00070400d840c891f0003d0041049950301703040301c4100d0236401c0404140700100e00102d9091240000c80b9409641034604ca050304500188014080000507a000348a070302003282415401d202c102d0724500c00e07403d011104441d0488640c0300d4009840e122011110580040700c03030384e0400c5d0900002d40c0d040041d0420f455130600381552200c583c440200c0ea10315131940300c1503200d0001200c09074090419030181c0c0445020301207000306039984c0303002c860544109220301710004001581110104140070006206028149050701c9002c1d04203000300a02840350201d03081b0030b5503840074881000000d00c00c0c4019040703005542c801e42e00d0030b61242c40d103a0000805140c0000e454000d03a0341610304c2880098080e00050f41180d07124506801c2c0300b4002d4008009420300c05620f45011600d01d000d0200390f039200000100102c10b00d03030a101c1c3c1250b0364580030f084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 255705539 1250 255704289 255704303
    0x15040305070815100303120504050a23010f0b0307060e06390105040f02060306030f03130311090903090105090d0b090f10090206041401020a1403031906080604020409 73
    0x10200004a09100700340082079041d0041990030381d01064080c010001a1403d8401e001d000810000250019410030f08000888070004030740d911800c4c03a5013800003200e0010b010142c45081c0c80304a0500742d1620280c1d40e40c401c000c0104c90114152501217030f5800e44150b9040d07205680421202d44501c0d40503011401c090f1a8a045c481d80c41100d1840303840414400013400d00010791500340068604a00d02c00001c218007e01c51400e15440c0e52107802e0741020040c0c014100007001034a0742e241003012094907410781048a81c1c403c02a201600d900e01c40d8001101c441940030800b0040746044100980125080e002840c94005a4001505c06030300000d02280c03c0010a24410003096910180358458119040580030f44545040d20318180030741000181c010b6403400a031390026890301402c1c0c038150768030741c3c041400d500c2c2e12000503468031a010300024015000d107820a405404044003640c00760342104030240e05148c0400564044d240c6900131090f0036030001300000e0142c5002d4001e42c1c3c40c240a150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 255706789 1250 255705539 255705547
    0x518150f04020a08100c020c2704080c0a03110d03140109090c090204140103110a120b03010608060c0c15360d03061404091e080c1501210506010515 65
    0x200d890030302440b114172426043c0e80c0c1c0011a800b40d018804416400002c41d11388003407100d08011044d40c10340340700242c010100080001020010041d0896807075101104c02c51384240602d10b4014400c100d21080d44d01c442c0111440f0ba19110b00a0064500c0c0e030816a20780e400c1c9a007002c06035401000441e1b4141c4100c5440d840c001000c00b61403000f4000740400c8804a2a0508001d0015007580c140d241203c6100c041009440d00d003da0182644010040c9041c000c20a200d00d000041e01512158200e804e20f80215011300840514010003488003080700301c01d846891100f05160034005004a95a90304240c00c580c03405035060106103041c0d00050001c402c10040e01003140b030317940303450300034804000461758400e01406542004414014074041c1241c05114181c03455448200000310080401d180c86400c0200c001000403030402e0ba1000c81042044420b542c05050603103c1d1a032080c442d40b014900062800d40c04c11809a42c4c520f00c0640150040103942d2070b01041c00480e620945a03a624200300340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 255708039 1250 255706789 255706799
    0x606030f0411180a0c0e011209031e180803040e060d030201150e10090204030206070b060a090e0a140c030d0f0207080f0708010606020a0c0323030d0518150f04020a 72
    0x3c40000b40049600d030b43c0300003620f00b40440004542c441c802c400c040c0441031031801c80d00c1c0c0c0d01c040d445420144040300803400c0d14541c076080d12500b810000780f010381841640b2103448036130b104198221086e40380610f0651190f51382c10884c1c40344194041c140c110000e80c0000b482500340100c0c1038841074401d20000174030150510384500c10401a170010074a00c0c1110040c084544e103101081000b5282031f2404500d07062540d400030310b4a10900300c005003947d282d003001a60383d0751204079280050201160500c4840d44640101d911a1506801214001c0740000c0c0408150350000d60184d0303405000d8010b0000407500381c801c2d120303042c0255035181107100d0840085040b4005210125107009084024140282080b01050035600142c11074411940030007592000310342d00344802c90440303400c03049201c5000d050110017221040038029051103031200140412004401d0b600c100e00c40d00c0d007007020b01461500240140c0d168001400c80c800b50b0800600840d107176010f030b0041d054104e4030041c01445415617034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 255709289 1250 255708039 255708049
    0x4060207021219030e0a0b03181c1e050307051b1c0507020307050609060301030311030f0f0901091a07031b02270601030c05030c1803070b0a030e060606030f0411 71
    0x21000360084091100f29480c20180c01602c011800401215050915030030006c60aa00d800010403003c0d290640304120140c541c0280003a9000d0712198519035020900c0844c064480d8900c540054001c80d50000105111071213002600d0044c0c0b0540e44070b914049410040781c0c501050f1100d407a1070f90103402e010408174100000743c1c032043c00d66510345640710040c50041504148a651000b4042c520070801240140c0d0b0307420480b419240c2c141480c0a8030107040350300520b103015141c020001ea50300040d1515545101002601005000b44d0322034840e41d850302000c0b580004140c1c0c4000c0300076030a0040030006805880c4943c0380c20b075480700d83e00d2001b00c5034002600c800e0102c005440c0c400300260007501da03461030010403a485482803d05200c1c0464107000180130f0b11008107404050000402c01041d145005c0409060900b4000e0031164200c1d01c611442183e1b900400d1040c02180c41c042e02407045890205016110708401026241540c3d06c4811901c2d4680009204031004142c106002545981d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 255710539 1250 255709289 255709303
    0x30c0504062321010e0603120c01060f090f1a1e040b0a12030909020f0301030b0c2719030507060c021206040b240a1a0708180103061d040602070212 65
    0xf906808180f0b000d50f60b40c030002d02000c10b811072448654884c00700102c80c0c900140640340c11107095810341c0c0d5040103141c0300740100b0b80f940003981003400059001940c00340e01c4d0800340c1564a0882c040003070702c41240305224880604090720b41c00c50343c041300780010f4600c501da080c08000f00c06800030a80700d207480c0000e80380700e070f19030000c4070381c40e442003001d40a16600c4541c14003d00300c000c801314581001c0d0410b134082030005210040c980020480003948140308142070f81d140c07141410706002a1502c270702d4010103000c0300300040c900844e17041304044c141c08914050340040700d07001006000e40c01c0c201881101c0308143c41d1016070304580e2030100c0d43c1c8100000c2203110702c03940c01581040da00d420013091442d00150306540a40e0f103414850b01010041d660101c0402c200c401c07808941880441150114005004851000e419140007007448520700c24924410204004240e070200009500d0f140c01140342e69421208500c0729406e540003c000071aa60f0003812414001424101400c2610b0f445502c3d00340c0d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 255711789 1250 255710539 255710557
    0xe01020d141b18091015050307090b03061206040609050d0207030215090103060302060d050712020702060316021006030c0314030406021002030403030b120318100f0c06090506070f020d030c05040623 87
    0x491705401c0040b6141c00d00204480c021506d4120300d9070600d07081c001c00703010050207400b140100010200e41c10359540c04031000300b040380c2403d03503c01e480c180c100300008021000081d50306014400c0898030040c40414400b0640703500400500300d06010000d2100142c109982c403606065a505010025941b02c501500d0380ca56043c0d0045a10328141400a010480035004064040d0050091a00603541c10007a664412021300883c41880080312017285810b0342218000700303151400c04040305018450444405807130051345800880e0b07680429181e944c2c0b08902c46d02c401a0071a0304c400001084a400468215029140116143c1241d1000a81e02512499070b000254800622215400072241401c001c6000071610003d90500300300014025500341551407082010421040d41008020b600455080350802c04491680c500014040d02d0b9201c0040b10b0400340c412019105072491003030180360150030a0b40d8a0340d050901c0d08109603070540e510145407041004540c200d281560810303001d01443c103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 255713039 1250 255711789 255711811
    0x40902030a0f0c080a0c0302060310091803020c09040c03020d0507030512120601142b09050102030402090a0b1005160b0f15010e100c05070305010e01020d141b1809 72
    0x1128a07100e0390254044d8040d6840da0040040c0e5170114440301540300449030142d41c016070740c0d91607030b140d0102403020341c0000505030f01e08128000340790749180004410758440d400b00d40320480320404011044a040360001c0c80409554000d00041c18007980c004284d0b8410340486404589076914642001c030500e256280300344011440141c1049104e01242d0002004c0c2080d44004404445484c5544120680c50042030440351400c2260170300140d0980b0100784a8500300700d800e18070301d000c41c040d520030b07102039100742035035004944030300304030300c20900707502001003140d1100725568a0030754441d0040c040019001c0d403520b02410100b00300200242c030a107550802c0141c1480c0980600c989035144041c15410000054210301ca180c50b400560030355001981441c00210005d440e16038503103030f840d42006049500701203000942c0302054024140ca184e410405109070383e480d0000c10300c090070846a4080c09076150055540c3c48000e100140902460030a01e4079131b50b05c0c0c3c80007090b00312800351401c100079 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 255714289 1250 255713039 255713063
    0x20a0807032d0c0509040207061401052706010c1b030312020a0203031b2808010b070b0613061505030103020312040f1e050d061b0906021b040902030a 66
    0x80e03500d44106140408070310031902080403001201c410468902080080300d9684107040c01c03880f80610295429841c0041055641d98040c1c5021805054225142c130740c80c040d00d02c008aa0361500c210820f09040e080c004440c4110308001d8261004074000d010903044c01800c00c2c114020403207010003800c0d05042c001c03000c0c000ca1b10b18030380100204590540c01807040d1051220300f001645c044100c031303008103040e2a01004203110040054192058155080240080f50038184d84190208914800c188164460000517070740c1c1c1040340b1540c815850300402503504a8006141c0745801d0b0010b00d40d40360040f00001c4e184e40c4590b4180072984030020303c3c10202d50080010011403801b08215030b01c0c0c0f0000c50015041c207240c08402e4030803c0f400c5c043c4150490b4410b040c1c0e980307640301113190380040c03000038040740010080e4144000180b4550030041c0080b080302ca00c2403c06030080d001e20045852a900419105560030390030301c0c02031081c0c0d020590050712440007401580c3d081192042c403078001c0525101e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 255715539 1250 255714289 255714301
    0x806040209010b03060d024507140703080a0b040f021b0312011a13090b01110d0203030a021e0f0c07060c0b1803121609140a03080a0c06020a08 63
    0x3074090507401500401c03030400c01c0100f1030f140d02d03a2500d092a815640e40110302001da8444401c1221320700790010409442d0170740da01c0c000300d9184c900441c01151400f000583c840a00803a03441031450031010801c1c408005031400203200c0d081d02c0d80d00460302d5000152401e8844001810b4404d64404070340600d40115607011082d03c05c03881c0c11148212200114944103030303190001c1c017178601403050540d00c0c1c01e00030410341c40c0c0007170b032040710b00ea01c0c0001202140f043d11034085500600700071011038000740741e4083e4503000040000740b800340c81e101070b00203504540d42e140141e0040d601003051072a120824005101070030015a01402171049103030300054862050300c101c546030a1080d0f1000081040846240c4089044480003540004c6084c08240c2c00c030b14262079543c514070900441e014818685d0b42001088207107400f00b0f01c0c42c18184d0755003610f240c0d0707540a00c201150801150300c0d03024a4100e0100001407001008146142d203d00380350b00d9a000544402d4202d8000740c5c902400f040c400010010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 255716789 1250 255715539 255715549
    0x30c0a050303072a03030e030d050901091403070b0a0b030111070809010e10080a090c0305150f07090e2406040b03010e180c01181502010225030f0806010e0a08060402 73
    0x140301d21015035507180b85812880081100c44c1d0340040d0502d582e80c011a1a9158140100c41003c0b02641c02403105081c407045003802444400713400d49400c039020304e0a8200500210807526082c0c1c0100f0109026148c2480030002065000f00c00c0b0381c0340d9a20700609038100d000c14090300c1e0250064603c40d0312410b030070002421410700c607500148607500c2041920300300c035007080da016000b00d15540000388104e0705e85401448101c081e00058171034400e00c241c5201800e03448040c40d11801c030360110407106850316882901c02064500801489044c10000900249001008000c8440074000040c25074500c580224041c2c0e80241c01c41c9407034200000c01803100c18156450150082c00c06111521a24900d00b00d25131201d0030040460704000c0c0700b064201d484010034400202410011031060780615803084042c0c000c1d4070000b10b91098010016034107103c00c84524008a03040c0e016294106075182e0118210380a0000600480c140090715140382c1c05500c5800c4ac00e00542002da00a21041c2090b0042003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 255718039 1250 255716789 255716807
    0x204090f0603020306150d0206030a0c2a02151908090d0c0b010b03060a18020a120c050f1b100e250b07080d1107120801030f030809030c0a05030307 65
    0x1240d141081020030058800184c0c45030f10003590031035804030040880c00601d40c1b003080800a0742c4844d020091005603840d6a2007021204000e0300c2e090442107a00c2060035041c0820401c83c80f070000201816000350811100c00d494002c071840c0d12a14001c0103400004500329052420000240003004010f040881003220246030701c068104809103031440c0c2e882e550000014080d0b000701c03940100204000342c4503002e54402904080700482c2a141640580d10001e402480110300014850240000c07502c4451142c18250070780c0b070399071b40c0c03404030845800c1d072055006651507095411401c90050b22040240a603580c240ca1059010440480303403018580381644600d1820500c0d0004282e5003a41c3c0c400102c1c040c111580364010588400041c1030298840c010801101410350512040d88030403500d400040989503c2501081d560600100f0101d40d280c1e001d010041080c08420103607400f1030b000d004c065512800c0350b03045a1808819130005800c01001050440b80c41d400031040c000040e4010300c001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 255719289 1250 255718039 255718061
    0x507151b0515090f0705060c16090f0b060906090f060d0c0e040f0203060904022101051f0b070b04021309050307051c050a02100509120711090a020702010c030806030c13020409 77
    0x2c2130a81600d81c0e41c9900c8601600c5040d104400005c0c1c050101e44c3c0a102c95521046800030a00da201d5803070070050b001e401d00c2441c02001074504400b01d04240b8080054030301180c030242c001c0381441d40c03050030300c41150042548680e205a003440101c060302a180070325120815541d490510080218090000703582d42c2c83c00701c000580c0180204040b5480c5e24040c2c69029404640b6003410030090040402c1a46024010013619402d0070300700000411404001d004260b00345581c031260a80c0c60341300605500800c100240700c040318402040162074402440303035075114090b8001441802507034400c0d203590f0002d17134211010f0300003039108107041c940c0001c070042180281c2030080c070300341c40068002c1d01d86004c0103152590a80c0c510102d10002800c00c005010070300520703540707076642040b400c200d5100c06034030032014410852400000d80010550007900e190a5044c0c42c0c00301011126030f01a11607400060455425115801e040d110369541d0640c3d007051108041c100594581c200340703528007950303070513209 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 255720539 1250 255719289 255719293
    0x40e06061809040615090504020a0503060103050604060f020f0a020115080c0a0314010b0312070c08210c1015050301050f0106080103141c030605040b0109030507151b051509 76
    0x1240c59a1540307126208650315044846620302d035030341d1411100404e50420f00b01d4088245090106443c08a60b0005000c0c40c02214400f00d10b9980302c1c209680d45e402408010300503000341007c80d001075015008039502d584203101c05820564040d0f031440c0240c114800c410010f070744600c0440900c44260011f040a41660005440c5040140010901c08421031200074065500e480451049074002c0d40700d01b152a100609031101220916465490768011980c10f03148120100300020380590001200040483c3d0004a02c0c0c8403004541c8014160b00446070340a050300541c4428500140c5034442c5101e41040d02810380c1c9843d040c001498211103004000902842e1004014420a9081404581100d5018203445042c001c900d400505040280e502d010b2451003024200a003d03426411141c242e5000380d80411204800100440e807003451807101130304070b8014031018400c18076041408000040c0904202c00c118850b9044d88a03281032242042c4c03503e0b0842058011213160a034819500140c0070b40c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 255721789 1250 255720539 255720547
    0xf0306120a1707020a1d040b010608060d021c020907090914190510180614010519030b0a0302090c1308060f070804020d05030703030b010905040e0a060f0212070302040e0606 76
    0x900c1180d5200311400b440303400300022880c0001c550f610601400a802c15140346400c1c00304a1000b008140c805480c12104202440c00200d004e610803d00f140c41000000c0c1031194480c0c498090100440d090710800b0200005011810096102d001c0d0150141340ca60355a00260383c5080200307011038400a07400200980036806116141144071002c51090195000010f5143c0f1381e8800c00300d40d90110381c440c13011a424607140380c0c001c1c24964415012113941c02da0108503040108011a00c0b4442e00c4d05407000c20598000c0030349041c0c481e5000d190340010207010500c0482d140d40014071541e0b012503411540a00003d140e05850a440c0010001010341c24024407583c10b0052040e004060010018010419104001707001d5569110445203140c0d082400d40ea540c4419041c020060b180340030319940481c105101c002414100351054045c031101110241c0000c01c1d085c1d0301d0340041c1106006225901c0d8080c020020300002142c1c64034024201d941f40180d581c4e190810600c65281d008003030900c1030400344 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 255723039 1250 255721789 255721793
    0x80c0f01060f0b0f090307170a050d0e010f0f1101020f18010801030f080703031803050d1b020714030709110a020607050414040b0103090b01090c090902031e0712020f0306120a 77
    0x500755907030200005039490303c40140178046890300c0ca469001d00c0350b83c4020391400038001e070007183e0021024020415035944440d406000e81d4041c4a001050703002541c007103c1c0b010614841d4881c10542d00b200c1c600754110500d110040c0e426a00046182003014030002007003038250600000d00c24120b9428200300c400b941c95901c81541052821901a20100000554004251207548000d1191000001d021180d51031410b0043c01c90300601d05180c0954580380f01111840460740000150441741d134024500b041c1080740801100c41031041341d6405201d00400401c80c1e1406001d0030314020109205180c940c40211030092034000050400c1c420b0100802060000419610410420000c10348000c5440580400128024a00640041c201141f1030300045401419904051101081c9688110500b0380b40c6030072400b213100035500d0003107485d49032425102143e803030021f65a21058500f082c0300c1e2154080d00500a036030050300000440e003000010044c440c07410b4401c20660305c60110081042903003603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 255724289 1250 255723039 255723059
    0x50403140304050604090605100206010312030e010605030708060f070c02030d0c020d020a0e010501111c081b07061d030a090b090f130e01050c03070c080304020a03080c0f01060f 78
    0x14080500030518881040301509810401c80e001071801500081c1d4480c0d543c01c2500007000305000d42d9104400e840711070000b05100060890580340c200110082ca080700910a030010105280002d41c0341d500c4010001c2c03295400d100040040c45898094040380c507000c0c1c00e180100e00024031480c1400b441c0300c00b540151b00c0c00a111a0a105036003000035074a0389600000f4508070028600a501994884011841110410700c0e0350480b4400e80350503481c250a110303420340b03d03582c0c00000c56199440c0c11582101b240b2981c0015000803810b60840500c91111b840070146501c040c005075101038071121590680702400c6c503200d00c1c2d80e000c2005503040541c01c003001409a180c610603c4080200429121001e903039400b503801c14010b0080054980040700c000b40000741c044143c0d50700840d4a0b040010311035410300807c42c0c0c41340325590348100f80c400745603840350600d0b080540181d801000c2d82101100107407507440203011007001d0100070714844000e1f55a0a0960365913400c565600c1c448103504000741c0142d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 255725539 1250 255724289 255724297
    0xf060301230609041505042301090305070803040218040b160f02030a0e011214041707080406080702030f070605090f12041703070c0612050a050c1207020115080c01110d05 75
    0x4200e03950503c503200c605001c40004142c400380c105140c548001e100030408030341c01c00300001c4140309112841d00302408241d8200c1b050030b0000307000309008021140001e807100004561152008006070081d07452110305101030382040302d04482507080310701440340054005003019540b8010b460040072071001000025103d020340742c0c401c82445401444811581c0c043c00e294091605160b4082104980b6200240300740c01050b9000d4400c0107030145210840344044044030090754100306818075040c5410005c0740e40a0005009000f117000501c01c172081e103001c1030010300039140070341004503ca0070007120740c0b400d02d00303411075070762040d400307094041b40d03000d598010f442c201c42110f02c1d000a840e41c0c503c07510b4154412910002d028114200c00403546c2c030340060b03d8026107020014204100e64400d00d942d0111081940d2020811506226000040303104052150303001409100220740d1600031188044412880e820280640d044454850b4807940c2c09600040300106840c014403000341209405402e5200b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 255726789 1250 255725539 255725551
    0x1505070504171f0f09121701090b01021c03060b040b04080c030604200d0210020f100c140a0302090d0804081b15130f080d090b070b190f02030f06030123 67
    0xf0312540001c80d104901c1e417001070800d41103149503158440300100180006070000b01814080c09510020030311106a100c0d4207000f0a06030002d00c804901d40c0c415401507031003000540d0070151108000b185180d031a03800b800040c44240c05140e00c0b54100080142400d09031108030f4001d500079004c00002c03070345108448902400d5440050020784116011442c481d0600758069040580c2140c0c0c1c40d81030354002681e101d00c52080040e02d002c2000420b02c0c10540e450f60040500060113000707005d800980c0e69005040382c40e00390400519003c00d010200d0842899100c1c20b591088000c6804c00001c1c03030a20040445c0c20144e119502440d0b010b00000d01280c004c5810741e4102e5201017400341c0502003030b441074005031078141d04070120b00740d0310340406079102000042c81c40054061100091240c13904001d540600d03511041c03220055481102c04540e08a140d40e0301c260282d1070714130744111110307035100640c019952600d881c5940d240a805040c203441e880810f42d41581802000b0204030007003141c005401407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 255728039 1250 255726789 255726791
    0xf0e0f0a020a0e030f0c0102070501020d0206240414010f06030e121e0301030c0807060807020d110c0607030201060915060507030c050703061d061803161505070504171f 74
    0xc04182d0100d5a042c04480c0d0182c01d445158228009841c00194400c050b5509908481c42c00703450782c004985801c030103001800940e101c0c10210304603444950001205185142e50b43e1108550840002c085d0380840340b03502c41410400c80140040c00303000d46503002604036410140140b40790720240d02d030b641e801026603004034000030a56009004918a648a40003900e000c407a85a5031642000304501c50140b190314603a00c108032000820900841e03115110310000d4001d000940710010041d07a1000313240c00241c4150150507544c00039542c03203101421500c1d0203580006083c03418520340301c003110070b0320032402c0b50014401810020705511804403000d071a810315198011020502d4070383d15140464000034401d909005074040040b5400d4810000e00c00164100c910175150880d142c047c050340001c034003540350400c001e900c40b071a904e5103030410b507288075179500d403101d0465002040481d02c0564141c00001c00001d01000401d100002e60a10710f00c7d010040d0056404500f42400c48000314028042a9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 255729289 1250 255728039 255728047
    0x15020d02240c0f0f0d0b1f0339080105030c091902120103081207090e13020604031713060e010801030b060315070503180a0f080f040b0708040f0e0f0a02 67
    0x2428002c191420719440619507901d940342d1600151080c0c1206040700a203a140c081207005c90320704040111154400025480d40e00c0611200440107807203a0007090f1207404031000b401c01c0408808201c1e018003001c8200c100039100c0314600040c1441c1060340411b2090384801e905d10303210303650350100325008503800007500d00003400440f016001c0d000c2c0c040515107040e041c00000082c0f0201c03030010700c4080c040709018031403a52090b030107898480940c09a001ea50659a00003102d050700c041002002e070303000410b070320b0406982c0d0307071030481100001d412040d901d28003045a000d01000400b9042c041c224a050403090010a10f00091010105110107840703403004101148050b141400301c3e000f1400c08404d04a014508204050116401030300c0d280301507d502000c110f050440031502c1d03042c031648441280c0c1c2711344030350711485c09079080380e10200c208810403c00041c0440c1840010550340b80324198040d01c0700d140c00d50070010f8003860380c0054200007501c001c2140c141824000c1640c080383c0e2000061712 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 255730539 1250 255729289 255729301
    0x5042307050a020709090305120f1302090903090402040f0f0501020a05062a0d0605010e0a03020a091104120c0f0f080d11030c0123010801020f25080415020d0224 71
    0x60058154040b41c0c61518006c1650281030340300d0300034290760100c0c510103109915401c4824541420454200d500d65410303500301001460100c0c001e54021030000212828100d2150005089034499401030621215901c42000001c40b4549064000c00090019141742022b548a0310b07180d80d8010400d0310143c0601004602c540c43d06010007400c6480ca10740740f62601c40e000158030013455135000e0b140c04500310f0401ca800fa482d02c04142c0c416264060048000c040c58441544090440c0300320b6007010501c14040030400703d08003c14400440d001d80380d80284585840840400b19000343c11040321626907031401d20040e0000144404400e00c1d520b400354400d00f030004841c1c11401244003150955080150703d808460b40030b45c11008005c0c0e1405032088990342e503094103080348030f02001e0820381c040a0000c1211500001c0003135007003400100342c60550b0545942c40da5030692007070b08403910720710240a81c2c1030415410045412540c440d80020000d120380b0b5640d0369403400b0703c40041407240111f2000155 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 255731789 1250 255730539 255730543
    0x50f010b090f040218010b1b011104061214070804150c0c02060306040e0102040909060b04060f0302060c0102090301050c0c06070801050306010b0730110601050a03020907031b080105042307050a02 86
    0x882c51740001e1501480d58543c0908091503100c40d035220349005442a203075008003418464684083c4010340400c5c501807a042c0e003540d01d074140d41000044690740b0b40540318103c1c01c0c9448584144070540e641e25152819180c102500340c080000780d003105107080740910300c00c2d81101c028900306804462080c0c980e0b0320240010007409508503544559400400d0000b0180040d422001045202e04030901c0b500c9400010310089070364178400c514400c1c64110b420009401c000c0c0082c9000d44040c0001741c900044c02001c80e003500d2058500c1c03114040b0010300002400b4062010940006442c5000c072507035458000000e54440d01801443d070031250015902d0100101c0e40741c02c1110307030f0764650810b80c4c18640051840008086814010101c0d4102000d0b21b04400d000c074029050340c0780240004556800c1d40c00344821550020312550074141d80d480c414030440c0117440d80050031501d07075032071203050743c1007001380010303600100e0300c48102240e10070000c2d000304680a03443d80e220049240042c1c81d0701710301608038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 255733039 1250 255731789 255731809
    0x30c012405061819090e07091112060604080105100f0e0402092412030c0105090304060516020d020603190b100e040c271505091c03020304090f09050f010b090f0402 72
    0x2500919100f84c00a0301c440c2c07a400502c81e0045c100103403000305070703901652420340b840c1ba100203a04003004c0090350038180641c0074139038010301c01800060030a038a80d0072a40c00c42c1c0042c0d0b28101669034090003081a000d420300342e100070304810042c03004503080035030200e0103001d0082c05000c841e9001280071001c83c294000960151314004020111411301e400104d40c40b5403061000030030307a5092000286440900008840072540a030f500d540c5440a000141400044440c0d8100d90100d400322850000d66034030406103028502ca02c100400d41c40c08020041d045850488505024041817800c40301840e8001c8400604400d05441c04161740c1040b043c02c541c0e401321041e510307429907507280300d80d080c040a5807685410340b615491804899451554180c80d40d0088081150b807042d803101d40381140041d0351020180e80307480b80c0101c909103500c800000041d02ca440032007902480c1e54a002805101c01041a00040e01a0308000c000146007030010840300c4800131b00e2a1520303a44800031600315202d4250311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 255734289 1250 255733039 255733069
    0xa0623011b0b0108010c050703080f07050d0f0e0d030b0a060810090908030702100b060319061526060105160f150b030d0f02030d0e0a0203030c0124050618 68
    0x104201c1a0140703802c440302d840c02e005203a11076203064603007903001c0e004030f0849003040e4160300c50701060740d54800c5002d40d03680e0041a03070f001c00c4020702c201d09d200700c0c1d41e000b1180c1c400c800c03a001150540004504529040441003040100350511107450881d80795029484103645d454940301c3c0003565000a0702407040030a5008185a502d812480c1c1e00b03024081d005540120703d9075090341e40401c2c8101c80082a6040010042d50207070081011425043d0340031200b030340d0440c1c050030100f030180d13580c1144220300000d440c03250085001c0c0100d4001549030020444580c9800d100708120905082000030864000c40080d44422543c00c5040024807041228400d1040d50060310352444440001840c40904160501e85010b481050161409c00c3e01600014040e4407441e40150f081c110108442c4004d070200136845c2c0000d00421000c0b1015071410b20082411810440c00400c250011035400101414240e10b1101d02c0c0680d8202480b8582d01d22003151007000b550105800d41700c00c17903c00940201c0305d42082c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 255735539 1250 255734289 255734327
    0x302090627032806270c1707060f0e0a06020706030c03020c03030103030c03090b03191d0a231504140d05070b0a0f150503011a090103020904050307051509060a062301 73
    0x1050b00840440042420180e12951060109980d18100c00510b500c480c7c546098540140304107000961150b04a82d1082c003507403500c131100610320000305000e000f0580210005811a400c01d2003030741e8160142131020740b001c0c03404620708840000c00d5074072400180001010080303401945014940f04a141c64090201036035041d550342840003440c510140030a2030040710a040000d01c0804400500b85007001407220006001408010b98a00e44500f00c58440842d450510b1030070031440c0003040240d07000101030420703014803d0a003820441d440b05482064200c143e803105803000000c0368810240e0300080d80c031448000380c030340ba0651454003804038400c007031000c00d1810310035060f000d0805000c141160f4080d00200440201000807072800d40482e410144c1080a0707100404c01410442c1038140d0288c01107050b00d04141da6541e92609026481e00c0072610072665006200700940c0501660303801c40e00901e01000110720b1700c080781e450304504416074a43c42c002111408043e900940862588041101e6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 255736789 1250 255735539 255735581
    0x212030f0f0c0d0e0f0d14010e03090306060a0803070b04060b10051305030c01210605190e010b19081f08030703090905060913030302090627032806 65
    0x14240e00540002d40e003440184141c1c000e1203951030184000b01d000d89000303081c4503400d81892052010700750344d440c8100c4d40c1480d042ca000d40c01810070720800d46c0710480e460107180d6814980003052328029000e0002c030301c03444000404028001001084440040e4001c4842c0c0003540d5509103100200400340619420131291842d042d4403d51013001040101207030b500130030a09032260207259588214054003400f02705030140502e0810554095052140e02000d401700d01680c0712001720340070880c01c0841900011700000709000c000001010070303001d8002192a903003800c858403035404203400104007940501c19174001080e050354420103281c18242d809848548580d641d0110140d5030b07803240300c081e8000b07810f1510204607a696401003074080c40e002000c4103000e444000c03401c0c0940040300b1044091603804c00062065403910001380c25038036040070148a100c81c0000c1c441e403015840d61706241c0b00360041120100d02d920499010000c208003c1076100c03620140340340c103030010090b0181c5045504041c0c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 255738039 1250 255736789 255736807
    0x110c0a14010206091c0c1e0602121311062808180f0a06180605010b070c0605071a0702070b04170d0f020304060e0607020d030c020f010c030c0212030f 66
    0x1032800c50009020b03400c403441c2d941e81034203168075016541d100f011031a0540d07883c050058890401d80d40704600900c8501065288841d030f88031200e00c1510221080383e004554102c0c086100d1611540c4110030801071040340800c1d650f501601c2d01181561486003501280aa0282841084c04414800c080440f0161340c881c0c09030292071000c00700c880c102680585451015013500c0072803426203203030b1402c0c01081c1c491042da0b50080500b0550b0303120040c0e01404400f2501281e26401411f00078100d03e8003d65443c0100d051070155107a42ea0454021b00408000d2480040d0041c13101316043c0510000380e0b10307079803100c80d0f0403401c1040e80d5120080800c0c0208001c90440002484800092a03481c121010075086180950701074010301b1218015170001e10042001070b00507000075006a000130003007803821700c2c140d00003601000d448a0540001c0c00540c49102141048000003d0048090903c0701320342d001c0340d030024041d2412000087c000c00040341002070840382002a80e960b8000d901c002511201c40c0c07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 255739289 1250 255738039 255738059
    0x270204021308010c0c05060604060b040312050c10090605011d0411120d02070f0501081311010306150e030606040506100e030f06040311070f03110402091f020c120303070f110c0a 78
    0x2100c01034172a40214004100c8509d0b1502c904021101c0c1011040d003000d02e5070301c84c0480b001c9141060011300c08100240000c808080c001044955005080040d0303c6407207081038001c44d68145c10001404030713107184c0691010341810310305600c554400c0c840f18005040001082c5080100c0b00e45021600c543d50607804650f402040b080d003500d4401040c1e00c1c1051b91000112039030b900c151040101c81002084110103e400328200701d50929040c14082b502e00e682c0e21070a01004001245907000070700b0b00c05050300d50f140c1406404d0b00803008a07401e000c5414a400000c18600c94440300c4001c3c0001c0d45c10564080d24144050b2603880c0280701603d0151030182805010301254003d00d0409001c0c106000c03d03000c5010b6a500c003681c1d0852800c29801121106000003035000220030340c1d21821100780171030b0310410a201d228409000768040d01c0c2c800b00710024009003500aa120f440190001e1007042112175208100d81243c81c141d14090070724000b10510345d03080c80460034005404c8a0a200f012a0a040e2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 255740539 1250 255739289 255739307
    0x6030c0c140a1b1d0c03040b0702120409060603051f0b07170403060b0109060c0503070605071e020102091207032a0306050c0306181302220519270204021308010c 71
    0x844c240b0b100c5528040146403401070844100c1e00c010800d0001c54007040c2044020b80c0d005e846401113940f0002d9591141c0c003150402e51010b065691640e0007071000c143d043c0101d941040c0508002c007042d41000c0881d06c0341c00c11a01078031030081801b00e031701e8090000410340100201060008182d40326140e04046014281040450380442c281000c00106540300e40c840c080c0c81e2b60450065402d003140c1c3d41c0c13104090203003d04060200502c0741c10b40003040c25805840c104801881c0c000503074810f0000107001002c07180518140711904421010004100b03420b01c0281c002175051741400301d0080d00540c20003a80701e184c00107840c039841e20080000e848103007401140180400c440c1a03121007560000d07200f158100701c1c0c2c6400d1001c880941e6400604011a581410062240a80c1c015800c2045002c0480c1c5c070840701c41504010221455107114518401c0060700c0807418404540842c1040001c0c402e48903110b8020701a5a00240090f045d00c17107010390801400860000b8003164000800003800c03400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 255741789 1250 255740539 255740549
    0xa030501090b091506060a03020913050a0608030a23130e0103020411040312031e141636030b0a02070c090c0f05030603010906090b01080706030c0c140a1b 68
    0x5a68010400307281001602c0301c0c403c0e60002d607104480d45ca000c02d002e441c0e0041c20490060507000c2c00300740d155030f840600244036641c00303803070000305817510030b1481b0182c0300d90782d0040d446500208480f02c101c5500005849c0403044420b2440e506410300c88000b580b51103100340b61442000b1903040400c108819a00c0300f8103ea00840d002c0c060710f01600c0284206200307501c002010740031a120071035030041c0a900a4104820422944104504080c00c034509035000c45c491024013000940c10040c40c0e443c03075418241d15196502d010004070441c0b121001c2c2060010603201c1c2e880f107056888004c028581542c42002d10f5001c81e800e0014140549a4070103900000c104466403011401c000c160480300f881442c02401240c0d8828200d406002c3c01920319a2000d41410b8055403522103100c0411514014030715400d01c5410300104a601d400d0740039081440a030880340c101401c10070000b0206a1258030685855004a0383c0c2d14220700040c5034501d8020000c1300105403da41e02010700d081c1d541280b545044038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 255743039 1250 255741789 255741803
    0x40308070303060816090902010c0c180e1506091302060712020613050c01031107170a0f020607090b5202030d11070803070b0a0c0c02130e0c0a03050109 67
    0x1544a20005844142c000222007181112140c20846134145402c07c02c07c003401030420301e500d080f00b0345441ca440310b101d400200780a1510f980c01e08900d600c51144036452140316001d480745105100220b02e44038000361480380b0501030b000209201c0701a03000300301d40c06139004000c182e072139660b42b40445000d070852082070058081c4100044101d451508400b0750164482c0c003404003041444011b4008024131988501140e1040c40400001001007500b0742c1121000100c09880c1d00c00240d0040000410507075034411904074900b80244c89030002c5401c015541060a100cac0c54214aaa54000c0b04408881315400c00f00030204c00c27041140c0c0083c0505603040e0118003040e0b02030200041d4100d8540f203040082d0994054140c501c003540c8590410404900d2076400ea841c0719030740300801c0740b95401c0800d06907284d68500b814844108140d00c140c00302c190382400c00c2401385240d5000903101400140301d2000320354541d010800840400e12442c40080d400404600b0302c07070384a0030154020840200200c40c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 255744289 1250 255743039 255743051
    0x1050a090c0e1b03180312061011071a090405100608011d0606071a09010b01080f010b0319020c010e0a02030d02070f060f022a0301150b2d040308070303 67
    0x31152042c0da40d4031a907800c03406a42000c24200452040b80e10082072407440c00800240c0d20702e403030b00902c002e1282c0040e0441682d03107418910100801c3c1c1100b185088240001c107100e601d280c2e000400e4601c00c8a940d803184403050903040710585403612901c0d00e01581305107490f040080e4025035013034001c182c0d110380d92030b811140c0e2a41c02c2001541441807851080701001c07000518645008001400090310908541026000115040800301c01c02d0b141506543d4444011196a5a00c0340c82c03241c0c405110381500141d54905082c8220038400603001c50128462400d851503c030300365804442100c8400f1008126400d0340c5c0b000302c4c0d15180c001c00100c1c440e00946000b150814400100041a6120001982c0d903542c0b40c04e5066402c40c0c0d08448010179400b4070036541c80c00050440c0b00b050685e000c00541860200e14000f05400c44a203e001082001e00c1c0d02c40620032141c2d00c40035511a44040040c12004000012212507400e14803000780301d200030002400b00c1007041e040b02030032070340b8441d460078401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 255745539 1250 255744289 255744299
    0x1060603050c0d090212030309030c061302100302030703090203060901090203100605090106111c0503090d021605011d0d030e0102060a05040302030a0815040f060807050a120605090f01050a090c 85
    0x5640d01901c03224480d25062000d1000c3c800c007035004002e007034402001d041010503200d00141c21904101c0d100d420075080800c0b000c80c10b83e402e000e1343e41d00020120784941072410320b5001508a8900d0030f899401c155021000400481c000c1c0d01400495400408962140c40e254816034060580759800324000e00804c043d08a24450601a031416101c000f401c0e90b00c907a0800d001140c40c6641000f5407125886030b080303610803001c1200026036140700c241c2d9426a803881e080180d03628010690b00954210360003000b1031001350764170180c1c54090f00c40c2407908054030015003403140340e00c1850b6844c503688040c00c008a03100705034210b41104108042a001d03200340d580d0310415a807c0300d03400c58000c1e0240e0030030400050624410031040340e100d039000310074080c6102c0150200b01110018006010704c40da8803141841100010012500200012030342c03842081c0c2030506100d01250820380043c0b5540d10303000842c1862038140400c150030b03142940204074600d8900100c41c06010700704400d4815500800e40458 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 255746789 1250 255745539 255745541
    0x608031c0608060402010e01120e0a0c0608070806010f0c08031e010807030305030103060b0a08010c0f020111090f0409020f0d030c020901050105040b070b15030d09080705061611040f0204031401060603 88
    0x30890b0035410140002e903683d80c005594000c0003ca900341081600c100030210140030b40b00700020301d60705100a0007070072028501490400c00030b40203078050040810070041c185074090842c55200f40c00780b03450308240c00060410ba410000903c0d004000c0d4401208009100c0a5600c2c20a140010280f01c2041039988201143c1c944105002c0600000c50400050002c9001074002410b2801e01400080015559210550841d05915041c03000a0000024a402640d09001e42d0740c48401d140001c0b86801440000580c940040300c1049018580780c0d0380200565440700c043d540380550103445a140d85803203280080503491844405c91123411a2000400c00f944035400b41c1d825504000300180c5040c4d01e076100c0b0391800c1d400a2040b61062083e0340b600343e054405000000080c002c585030354800d1420200550b0420a00d40c0015018078030130b210700948402e85481810300e040d04103205c0c809c80d405800203d8040c14548044045903800090700004002024007004660800007000300039158842e00110 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 255748039 1250 255746789 255746801
    0x5010504020f03010608070c0803090c030606030105061e040212010e040c3f0204020f12150f01080910181103010605090a020d0603050a080415051903020a120608031c 73
    0x342c141502400144101802498030b160481d805040c4403401d1695135861404a030b00c112107a00ea00d4004084085503070804114494010300101d000f0b0060f0301c0c0c10f50218200c600000e00d08001010401100149030300c80798100d5a03e50001491042e996840e004940c0205000b81e404032600b0320030304000142c40c0c001490303500714040f9400302c1007413002d40c0140114445038030710303140d019902c5101841c5006036203030320041c0f504020501209032681c07422914014104001403e1200c01092016480e42a941d6210500c0e0784400134200302104d030b08e449000c00e2610201c3d80b0036101451611106030803003c180700d8810100e81c841c080e143c05c0c0407070181c285406c3e01c081d88203150304903400c0301c0402c0400b00c2d80d8001d04005e0186544c00550565280c5440703140c000f00e0382003500c904500050910010002c2011070059540c142005440c0c143d42c4015007201041c2000903204155010800d01e030000c3c07260361240749210300700c035060015545448620b0303140d40c4040040408400d207400d11941d0081540140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 255749289 1250 255748039 255748057
    0x1406090d0909200a0203090307030b01060315050312030405031603081014011d1909091a01140609040605060d1b020f0c12031c020a1d0303070f051608010506040501050402 75
    0xe004500b6159003000403641080f0341c81802d40c0020301c403035401030720100527500085004081e01900c5514040d005400c542c82201c82c506100301310f513418002c6803800600001554a0012143d9681d9210304200d0b0960142c400c80f15010b10005207134a0030306a02624407401940d407180380903011a50b41e030000300c40861052600b03000c1888032411011100d110b40c980788106ca0080c0c112844980d4094902c2c180c2c0c110380d00030a07001a5203080610a02640f880e90008440c2d100c008080c00f94104000081e402c60040e100304d205100009100401d5140c1d80c0002c0c00505014084d0360300c6003458070400001e4200c1d00d00d10175841c40503040110205200150000d0807614081c084e20700c500445082c05400c60405a41c651144020804103425014450032480c088000a00c016180c0807050710080c0702c4030300170904001e11041040000b4140da408030403518643c1e488071514040481511307196080036444071031440300055040c40000c2045043d04010b218071002c4608203d0782e80c03118104070480c09072240c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 255750539 1250 255749289 255749321
    0x50303010519060e09040804090e060114012a020a030c0321020106120312020906040f0603050603030909130f06020a030e1e030403200d0614180303131406090d0909 72
    0x58944da0922062258005000307801a078503160300d441105007a41c050a640d12100d51003000100082104041030034607403142480e0401e00030461001d03003c0c0d076480304d120301ca04c024065901c180071541c80c0b0780c0d6a0020b6510940185000d42e49045c200d000124442c00f400d5040a0341480710b100c0c910610544007075810740d14140c3c19a502d00d0300c080303c540a41c014405503269080280c070b0384a540d0440030b40010003010410351071031420454001e0a41d03a015003294003981c420f1040743e41c541d5032209110740c0718440580ca0103060402d4104020390080d0268040c0c410361000501e00d08107503060b080340d41e8000c4400101c403c002030408800303080200880c042d00c00340d0418007041c0300182988150040c1c0d281b0b4581c140f18400605400074010100b600c2048032140c1ea6010000d00700010103091036486050302aa000d107403404001c58680303a12000301400200350322000f42d107040002660110514a0302441241d889160880380c07941e9a0400f21507030300109140120009481c59140a03000181c100000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 255751789 1250 255750539 255750557
    0x60905010815031b0a050a03080403021203040e04020f011701230d0f0803070c08131401050a021e030403060f05070305090303132d060c03060b090303120a0902030a05030301051906 79
    0x1103035401c21400c290000740c5c00b110300040050541d0b00c03008000d0145005404059403549540304020365031120107000310300c5800502c410080c400301c03080000c3d0b000360180c9078034261549500048420400300c18030074494502120000c2010448202c441c1e000106400341d01600c1c40c1c00504100140400110040c80c111043d10010000389060000e150004418245003c003090541c0c0c41e1341d01a004850400000b0cc1160030400481d8418541985070788401e01b4070501d4040600c4009483d003d40d0175001ca0038a0400b05800555042042254015030b0070030360070000b041d900c656035800f0307050650380c1100007070034800801c041d218044112400341038642d010038800e400036030b140c0c0c031001c0b00c400401c403260040d0000300080c00149030b0700200700c0e486a0303000902590803017405800c5586c0c980142c00710b401c042c0034400c8140c0f4000112001000d004d014a203155440c00058400f034036070048000c2d01030040f10020010050008083c605844007100c0340e2008080f524045040b11030944616000158002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 255753039 1250 255751789 255751813
    0x1d011d030c03220e0a0903030f0c0e04090c0b36221808070b22060b06090301060602060703062c0a32060a031101081e0106090501081503 60
    0x403403c5400c2c1680e10301003864550b130340307100055250003260817121598540303a9000030990f041c41001c440c01c0340350720200070040c00c03500000c0c01c0d844c050100314004c0e03a48182031420321180c50a40b100500345a10b030300341d44100040003111524500341e034129038621080c01001c0e06040c0306500300000385000c1c02c5600d62142384450030f00020f80a43d03020f80b866644040c000070148243e42212041800b45a03a036988640ca85000802a40010003013001d8100d881c0c2c80744503d10410110300e0745203030000c801103144529600024181d10503102a10340c15803070b024000034a9078011814034820719294508101d06661003144400000b0003041c644540f040d4204010008524003d040750020039280c000034100c1c030040034240d12070030034110110002800442c0e03500320352122080281c2c80070050360130810580ca10365420011410b0181918144a41580010740d002c0520008001d039404031120708100e560340b00c001134100c10050040300c1c000349201001401448285c0070703082d180d10024004240015260b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 255754289 1250 255753039 255753067
    0x2030f1b030a0503090c1813140a0c170a02031e03070f110406050609031e12030705040612020a0c02090c0c061008060906090a0b0a1d011d030c03 64
    0x580034110a0910300844140d485904101414204000d600d515959090483e400351802110b0340d2140d1051506103500c1e5175400810300707403903001407501401e01040b911524000c02d02015101526440d44186000ba00038801008121000c454035003480d0192008001c14954a0f610b0080d8042e4055009110902c0d82c1c07500d030503d000c0510703c40310540381801250394031002c0d41c801502090b1507c907003804d40074111780303001e218030390041c481218941c0c0380032343c2040800d881e410150703407440030941380e405e19001c640b209126131085005d031000816580d1802c0400a00035070058059940000c61040e1040710406051080350540306046c0c951004440456080044001008016450340030040c009a05080810481d05006008074072070150201d0810603414a03000c03005200c0e02d0070364461000d0000108000c14550b658980048200301c0e41e80c2d071800307102e010302040d500d800c001d07154042031104000010341c4001403203044642000c000000710001c650750b80c043c1d581c00c0c520a810402c0900e03e04696 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 255755395 1106 255754289 255754297
    0x4030e090a0603150b061c05040302010506060708030a0b030f0d0c0b0708010b031303020114011202101103041404140403083907020a171006090b0102030f 68
    0x80e5846840a25207a49045508165205c03545403841c0ca400007100d03480300070403084001d1040e000301500001d210884040c2d00652a007000300d40030b80b030441c2c200e13086035410426090464aa0083c1c0310010300c5045805c039414407440711000768048080c412091100c103145c039038010090060034000d40025004200c7c404020280300103005007600386040d240c01540711490341c4111421031500741d0040c009100303072480c0d96040100005d85003e1607030714101510300c2601e4002c03000520300d8003035a441c415840b2030b0909410a0009202c00314000c189450060303030050000c03404d08003440341e030107051005580a4000814600c00c0082c01020040d1182e220204603428041c640781554a034410322030343c00b891141e51000007070403a095581c2d0307a000c50b000d0007900d181d00b080391910300c50540da10410000a02002030400d47d00250b01c00c070500c43c0141c1c8560680185182155031b407072540706580 = true := by decide +kernel

theorem cover : BRFrame.Cov 255575539 255755395 := by
  have h0 := BRFrame.cov_init 255575539
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 255575539 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 255575539 ≤ n) (h2 : n < 255755395) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
