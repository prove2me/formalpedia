-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4591
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:06:55.475975+00:00
-- url     : https://prove2.me/submissions/af12c1d5-83cd-4580-96a5-a0842bb44a92

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 825539568 ≤ n < 825719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 825540818 1250 825539568 825539573
    0x1302030714090301090c0e1b071119080d05071208160f0201181523130f020d110a05010306030c1a0f0f0c013c021b2404 53
    0xc03400404080c8500762000110107603651001e4112401c203682001c001001030f070780c4610b0a02c58100c00c07aa4007846a01200017041d48050180c1250350054004041c40c960210070b408012054040030180042240460f4002440c08002e10800c1d400c0520303a111280c0300c22080c10241041c0b04481040e8007002007000030020840c10b203c0100c0601801d51920554071180140c2c00c2c1d004052aa02640180254007a69000c0004004000d070100d48001001d12003a01c074507000840c90a07a07200d5414240b424680000c014030410f20f610300885004118600a4800c6034010880c41580c1900a4408442e884ad61052034201101e15000404080c6000c004240c44c1d0b85588011130aa4019036800d856001030340310b00b0840030000d580c044960711600c00c1d640c1a0341035580309590303c0f4000c4207405509100d4100f00c06550350420703141c000e202e110682c4112401146401303a040342600a51001e586c03c2c440302d140b082441c0d0000c1c5c0d00f5070b1950000c011070014074101a21301c5110740c010307072100304c08002000300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 825542068 1250 825540818 825540827
    0x20c070b03091c0f03091b030606080f0313090e070510081f0602030d021c0612052406040b13020a0207050117160f02070e0c1216020d26040b0613020307 67
    0xc0e4244d92400080408187c6014214040401000410103e85120100c18844641e1152040b6800c42c4210343c40d560354403031260b84038051101052141000c0c10010800d0702255000441c452051405681e05552100002130320150344480d0080051018020800c0044110b504c21801001d00364440c03901c5450144001d40e07a203c3e89140d111600d401081d0890035004820744451124107503030b0240a690345402c1c441500d5071410b40d01743c0d410710441940030100001400e40002c1d16261000c50b900302d6aa42c014880a409405400c03a0814484807039a4040015840907100c0381d01c8990291150500e0500010101c0907a91030f005024058001444000d038134040c2c81c0c0c1c00600c211305010020347d450305030582c18240940d01c00c00f0104450001c01066403054030003040c0c60306884600510941311410b44485260300c1c848082e000d64062480b9003e880c0c0100707405248403a841c510300c0907503081294400701f4104180e03812500101500244582e40c07405109038441c5442c111021400c501d4040307001031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 825543318 1250 825542068 825542087
    0x21308011d1b0111100e060f0405070608060f0d060c0e03030906040303030902011107060306060914010f0e130f02040503120325090b0c21070201080103110301020c070b03091c 77
    0x901d94000403a00c10660f40140ca401910380b800781c017661005a0b1114907103020380081c400400c3d46000d03400c0080d2030990030601030f500658001c0c4c014006241000c00594a210000d0b01341c0c0e07445031410b409040d9a9550620441c2e4143c4110800300d80d099484502810035240c514181d0700c690401d00140001340c4460080d20200c90300340c50045400d02c410b0005a40c104000000780300310b8040c186c07021410a8140d0031000450f0b1050741e90050844e91591185400110025410b000440100102a409102d80c1c4031180d0003500030a808480d401c1608114100d50401d18411203240d00440c08204528003030200102101d0020000c920310f10382841da031811000091640082c011200100480c8140300f8818040580325906000f0781d1000002c01003666894800410760b205d2419003090780310300b14000b09540c1c0c1541e0686422003541d085581d003190204006010980540d802c2c000031610700c20801c030040050440c0d0b4109640e81c1022442b85050031002c3d50411004100300c6c2200304196400407110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 825544568 1250 825543318 825543343
    0xf0603181b0308130e070507050d0f11030a020a0b0705130b03070509100e03070b0c0c0d0602280809060c070b06040b19090e010c020703030c0303090204021308011d 72
    0x420480c01100c1c1c440305400e080d40000c0d020300030210f031001ca041e0341c0411080c103450803d000ea650540c1d42c0c00080b1081e00c200440103244e60441e10000c424a401400118080095070901042d0107014811540c076680081030001c0c0140c1c0017042c010300f4090700a50031508901545010791510010f28031420444c0030b14450212107210000000304014410416155102d00080030801c00e4085504014040640c050072188640660500059442c1c1440c088076420a40c080151120081410811800d5010090140c03203050302000b44038a000000c512a04c81c40221815440e109103580030002d00249004241036038550045040c00b00385650321040e00c4189a1000398507041d03943c2c0d000810b02038000c1c500100e400c80b18030000180c02d10300e0300e83d010b0207a901c8000200f10080305200c89600780d4032610b43c21000768205c1001400801e1040f520500701900130706000c206e5166980c0428200d03846002000c0240744150018060100280581c00b844060501450070b204255111140c4424009041 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 825545818 1250 825544568 825544583
    0x90e06030a020a03030f1b0b0405010e010516030c09240801060c0c14010e040903020606010f0e0a0b0903120309010204060306120c06030213090612021906051903240f060318 76
    0xa4821b043e201f120300c03c01d12041c0d08005c0c0800d515526102464100c165021070301d44d402c220003082243c00521403107124182400c44a056600c0c10001038004044801e91801040000c1101244110032800040c611300c00003e00c5003d40c250041004003803030701c1070300039004100890389007002180100c0d01d50800c0e24940c01c42c01c0291080180103079440509692100e07045400c141501040c981c010074214400c0c41c0c203803a10021520703e09400c5401e4103c40f00c2a0358050700040051202c2030a080180044030805421502e4841c01c10914002c0d0f600111465403a60790001001d0045540c50b0007220010720014003c4000c0d40019a140f03d100c501c140109030800d90301003400c80c1c0c41602e0001c5c1381c3c014100c0510400ca0386d910340031210020921000e090b80150244010910815400304203001120640e64405042100c0c1c000362500941140548004054032407000d00941c242000011201c1565880032020791464480256648942507004c2001d262500002101400207494907894440d4001350 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 825547068 1250 825545818 825545837
    0x10308090d021002070f0506160b06040b13060311090c03070e03011d0c0a05090f130c03140f010e030c19020d0602071b0b0316030209040615090e06030a020a0303 71
    0x812801d0000241c043e500050b208030b400700c2c0d950081140c1050b00c1d0b40b60440200c5903100d4041c4a0548106624035000f113804040000202e800c10a107036030001002000031038210340e4880000c1c000b02d502a281201d16548080800800149039010b00072008156110301251411110b82c046c24000144403406002d61144071002e10741d03080d4003080c010ba945404d210070388021420030b2640c4d00140745016020720f03412003000c41c0928122010342e104000c800002d2000355074603054250050389a0800f110505101c03180400060710248481c420b2804e2100140707580c03081680114203486014100c1d03039480e0402c1128650b50359002c65840e00c00311022002142000484c80030450b01007111102030001440440c8103401c01c58403c03042a83c0408202e1901c880a443e07640c0c1c81820f20042e41c1c140070141c2880210401140242c01900504400a1000035001e540e41055070403182202124000984444000e10951800a03582c64001c4407d134018001e1555903804034190602c03a000140501000c102e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 825548318 1250 825547068 825547087
    0x803011203020f01291903150b03030d05061306030b060f131d281e060504030522080607080417041221200c06070c090b01090806010308 60
    0x70155004003901d80c020042040b545e112900909440780c60807840d00701c51460344015207001c8400700909140c440c098140d0500d5070b5a103030146000021209000e40d01c8d494500255a02440034110001c810080801c0724a800c2040120440100580980407480c280040c40403442c0340d004681d0044050319444052608000090601d040381c180012401c2c0c01d0888418209801500a04180c1c529404a03503102400d00300c56403000b92056090800c161140007400041181c101e81c000c48126201120003130b48501c1d88842c01a030701e0486d026004120f0000d03c040c05003a485428400c0a000402c0200d041400e28030321079110000a4022010404002d010605020150004050450802460607920395030f503024056511031000c1c00781c58030080e260416880080d0b040c0e500c2100b42d1a40d6403074000c00d003107010021005085085ca9016445071590074800c0b9110040208a00c0f4000c1c1c0d0312404132072408840c0400d83d1602c400c11410403804c2d09040081c00c10000755141034951080040e030720346c0c1181 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 825549568 1250 825548318 825548323
    0x60b030a2a20030d0606260a02070311010507080f010b130312050c0a05060103021017060d080c0a0b2202063c03150307080307150603080720010804080301120302 71
    0x1410740300d103038000014030742400341050741700504070380700391b104c00d06106c0d61180d041c03108440100311003000d00c070b004000401614259000b448000d00c45e0400220000000361a40c0c00c48d001100c800000c07941102c03d0080801c1d140303120500400b010320140e840e104d03a03c2441c12481e861071000400030400314116840d0140203a0a03143c0c9038420004940c2900d20340d0a08a5440700d0038402a80607480071084043c009200d032551655082c29000e01e485541c54100c2031001d0400404003d848860082c0850092403031309010380080300340034040800c16801c140301c5d034a1480010707050320182005100b45000051711000c080c1c400b61010b410000e820400a900d96020000994441c064105880c11808060b440f03020b0140d0b000b41c001034030584a022911046c16550600d9004103821a402440044c00203010381c0c5500303656103000310000c110303503541c0d98a0341c8551b040003034119501030b200c8e2511042c0c0c0b403411b12100309400307007407801e4849410903480e1800c040c40180200c030304062401100e0030502d8000c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 825550818 1250 825549568 825549617
    0x10e01080a0b060f0403030e0103060e13050a06050a0213050f0123070803040b0f0a09150c020f0f030406020d0f0c0f08091f020d0e1e0112060b030a2a 66
    0x1e0a1542e9440510340000c8843c2d003c6e000c100c001c90a10760307002110754820700c514000c0d104000c5030140d0399207540291007181c9201750421141e40c4101000740d40000d4480c01014019080450301680f10040440305c0c8401c09c6d001c2d0480c0f40a07074135101c0000d08aaa005040c0007813200c10750280b00e00385e2102e100c07c0030780d44a2030801070615507002040c4402c010288000d00e100e200c00d184460303059207402d030410040e600030800c0a04100c0d0441581c02a0007225400801c504115004030b03006012000d11a0303080c000310740301c20703892600042010000c071501482042314a41c0301d4500811820230402d0050562500004007030903c41c0691495010442820100c40c00c0c40c000030940e885ca135070f00503941013080b00c0030442ea1005000c2e09400005460282c0701c48804800020b01c00107030b055040f0000d03007682207420949810060740038982440501240b140c0ca0140c002c8401d2242d03217142c0710b04e204040d61410700c41c10000c0c1c411a00d4500e048911b036805d51003000307082e2030000000c0195404601d5214203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 825552068 1250 825550818 825550841
    0x50108100803070503070312050603060a1107050708030306090115050703051e0d0501080d020a030c320120030103150b040b130b1c02060d090302100516030b0f010e01080a 75
    0x81c0f00400e008000026203542d41c400d948102000c0207062540701518026901603030141d1011000c5078104090390480d225104412f07080c0350074841145c40e01403078009079078801c158a030800018001d05041c481001d5014152100501150b5440d0f61001406071250840c090104140418900c4800c0d22041c40000c04140b849101c58807a90b072880d000700184802e10a0003041c5c4140528455200d00204520b91450740507141c0d45001036640d101c10303c1000c80826a2650b0082d19044109403901d01c0031084800c07045040006820010356602c0c9005600d141500140b1a1040c4010400100b98100418028060072408541810510f0106002d004400c4555a02001c0c00d102030720a031081e58805171300f40000722000c0fa05000e41c0c6902d0b403c189000c22005e504132000700000000001190006140c2512034070469000b011003c1948088501c140c604000d4030282150042040e030345401504401c44040b900110341100890011f410303d10200907050500c000500010441340301544550303240c06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 825553318 1250 825552068 825552073
    0xc0c0b280b040e0d0e060309010e06041b12020a12061b02010905011803081f080a0809102124090b10050304020315040615031b050414010501081008 65
    0x804000d4058514030480780c0c082d61518019007410040000c103500f06103441e4440d858131208201c14081035500061000740a0364031000c1120082d8000c0203200d200303d00130310303000d015882504003c060400c0700341c0c8549100d208000075a00580e07128404001180d00f150443c41d500314592800d080a000340703a0f0b11040d50110700c104910002d4064101c4440140b08100800040003814414618003000c820080c000403050710029529481a01c2003031010040084e807a801c0c10754800b4924640700744880100c03080400410009402d09150980a0f076984803402c222060017982c19064954518800340e0140321600e5407101c144d40741410401094509000994149103511222004041d180401c000d5009a4000c0350784880e2a108509481c001c5070b00030003401000400306003101c2c85110241050703031010340e50071048025180304201030000f54890b01c00d0070b00c0c1d800c1003800d000018000381d125a024030705100034260903001c01c10885040d20005d0800341d0054460100795400e108554000e50b8451 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 825554568 1250 825553318 825553381
    0x3120624110a1b0b040803030402151204080904110c0a120e0307090c14030103031704032606100507050613030c0507180501051c063201090f0c0c0b 65
    0x101c210f0303040356518000e00d100101c0d541e641888008900c250300c2500c1c801e40003480400e005181c8800c0c40ea40da0803054603141d00340b65400318600300810003520100d03100c80c03000500c9907240c1814060103061405120100381004803900880b40c6990280000502c3e01b4003900d50806d00340e0049034102071400001d801c42d090715450b15140e8000f42280340b00500441c0d60400420100e4014604132070580f0f81c595915501848952000c050120340984100d040c003a0040303a00c001c41d04130305a424084034103400c0707100130340c1010018003051401c0d280da0081005010811400420400500241c01c18180c1142c02050101c608003240d0b06c4040300f4005145000c0c9203c0014090046c1214408055680f00c2c10050340e43d071402003101c190328101c0c00c0c0c0e031040520b11406000c03910380c0d400b0780d40301e4440c6191491514010441e2040301c081c00440386485000700741c010320410444e03104502000d004074800304402032020750007415069003c0801000e0781c80c04800990251085100095442c507a022200c412 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 825555818 1250 825554568 825554573
    0xb220f0f14011502030a0f0909050705070308010f060c1104140403120c26060d081306021605090c0c0a020604030b1501090b1818040c0303120624110a 66
    0x64a00444030522070700e000000071903460801c0b80a4031030852160000c500d03000030480142c408840d180358000a01032801c10004100c8514041d2a00c504908c0d9a2141e5800c003a14004c1e2079640107130402c103024400301e90144001c86d00002a0380c5480d4112110821550361000001c010705050300c041c002c2480740303105000805810980c1c4800d21405014140109601c0300000c07207050101d000604c0000f40c102402400c1c0101c1202201e41069010b0b28520089440d0b4907194004e1307209a149482452002d08100000d81e414006000981c24040240107002e10744000940000c0000c3c02d07924208a0008a010090000704108107a03598044e00151f21103649080905144004031407a90390034406401000580d88912003400603500c441da909814000c0c020351081486044031300107034126110004840001c00d0041513603200e02c4c0f0a80b01c140507070782107180003001072822404a45403603082c06000e20074099100c2e4510110100c5c4e803e81108500c640100301c9402d0310009144503e0301581168400f0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 825557068 1250 825555818 825555821
    0xc050a0e030f100543020c03070b0a030608060103020607030f0918060f08030702010207091d030c010e0106080a0b0a0b011214040b0601050a0219050f070f0305100b220f0f 75
    0x460f81040c0b040c8100b00b0680f420040348006006076001100341501800c4001c24912417407503a100300b0a10481e07040955950102c1d1601c24103403c01c0203555000b00d0104403480d8140102030107410080050040c951459011904a003c2d40e81c005062141c50b601e1f5011943c840c040380e90040020510800c0c8010701031740000c1c000c0083e07020b195690795826001045103400041110f00155041c0d004010b050301d01823150000b0581c1c5820501d400e454140903101480d0100068807441004100008180d01106034103401c446090380b00c1d01e000d420a004103404104007105840d40b00c0741c44000401d810582000499244021240c00d1114520b030841a800140d08022401d1189204034013542c0c0a13107680300117449500a01101500691200c034101d901003c00b4010313800814801d00449500594680000b414141203810140d10390001c42c5081013840380c01c05c10304000004a100811501c652503011880b0803c0054000541d05996441c0b0500b0303038a40d601c242c42ea0040a101003140d850310008110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 825558318 1250 825557068 825557071
    0x2d03030f02070f050f12030c0f07150206190e0c04020f120a020f0708071502040e07080a02030c041509080d030911030c220b15091002010c050a0e030f1005 68
    0x1401440760860101e00c0d40781c0c00c0c0540066620040105000304005010000101e451b40d10003001c4d030005008004207022304100e07408048640e40c020345200c0c2e04200d80c0080d00010700041900b15404501848241080d0742d19003074044588280106002d40b17034040c428541107040d040c403a0058030004106400004c804088d1014802c181480c0a80d0340750072040302e06034080c1d04185880050100400400502d1140c0103050b00e40c820801e5190311950b2083d0304003240c020f80d1100c045201902e0400081d1507001d044c0360340c00740043c101142141440e43c0304030040e0081d4026075503440383d00004240000c0c0203200d03520003480190101c690006800341d00401520020710102c3d642c81c5001e140164a117030209480200300001b8181c8440c2d21100b06401d03076500d65136200207000e03964525540c00312346c83e00d802c5e80560903100641155540500424400b02810041c007807011a4136107a01011840d60206c02c8412024041c40d101c100d00c8901c1c8001390602d518103025084900c03802d00503a803404156007015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 825559568 1250 825558318 825558347
    0x6030f0b040e0304050f03070e100f080d121d06010632030c030c0d02070c0e070f02120f040e0a0e010e060c0403030c0f050a05100f090c2d0303 63
    0x92088124403401d00054030210304035039450303400512040c0440c0c1000403418010344001000c85010039075031160f501480d20706482034421592010414440402c142d8011030052003008024003e19212990040c06107203a803d0990790a5260b03110b20242c025400d4101842e900c2c1c10307003691190750f9551000380a65000c11a02c034001c0909491212010b64542c501c41006410540090303d580d80d44041c2c00b0f50351344020240e8081100c02e1110710402d600390301c0a005800e1003828103203005405c040d00301044402c01401c10040014604d04a50701c1c42e0b020825481982d08083e0681d00ca80c0700c80005d070000c1c09a42c004888060700d02d0104a2540c0d0030350044040c40c8071000c02080801100c01d60f29413500c400300c41e802ca0602003004200002031040c44442e0486010b00186618164295a81e40c10a108aa01510560302007000301c0821100c81c82030740401884120104440e0410707070f9071030b0500f202c2e501c01d0814241000400c6401a0003040c40140c940741c2906c03010f01c40c140c0b6407502038903810605a1a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 825560818 1250 825559568 825559571
    0x100e100e1203090d080a1407030c02030c04051e0408190c0b0606070309060c02040b06030106020102070c0b0c070504020721080f0903090603040602090a0f1205100501060c030c05070e0106030f 84
    0x8007205900c0100440e14422400b41c0224055a140d8039841110362180700f1440c20440b0380c40f85030742d0320203440c0050300c0800c2c840d079150b448046450041620700010914018841c42c540b405001e000f03d05685035803203082c900d024180407176407142890900ba01501c590a0110001c403000c210b101d43e0300c031050704200c41c40350b620f042c401c3c5c0f140424000f881c014440700a0100700160b03c01d000c0c1c11b0080c034840982c3c1c2c2c40100003094043e40a40807035601e0f007082c1d210308d0160390007184501c10480034588041c0030f4090070401c68102800ba000703040da9503a16100d401c0c0240c0d80001c1032000e1101d2640380011302803040350102c6007425103400040003100201d80c0c0303002c00c910001c00b1680403a000b008031220000014045402c42c1c5807070300c0b000c2c002c2d440000c1700c81d8080f40c1d003d0002903207148070159100038020720104048101031820b1150800030501c14003040c007483d01c401440855081141c9540c410b80611700081004076500e40b0618001c05034001003e100d4410000041c26070f8140c12012409261000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 825562068 1250 825560818 825560839
    0xf3001140f0906040209101203080a0c030b0102070b0f0d06080a1502030432060108030a030f0908070602090a032a080105090c0907020705040e0106032609100e100e 72
    0x5041c04000c80540b00540e254000402080c00b5241c41d040b155040054411103078031803039692504410311101c0d004210003242e4208100010381d016481044621003180c20180712039440140000d4403010b503400342d83c950480c08104000c04640d413400303a034503810b0f50910400c141521644410b955000090b002c8981003401441d4403030341c842038000c1e039018580c0161032104009655400804410b074080c4d14146013014020421641da00c00c001c080c0c000c3c05144065036481400c0d940040c1500d030000c28460000c0e080c030302c201000944881c2241c02240e00800c0041c0c40780d081c003000601251503948098020000f10700100b0340c242826019a240240014510718055034910065082e1002218030494540003400d0071007103400c0c20210594400000d02c140c50800342c507440001c0445a40c070fa91680d45a540d01014002c100b403010046a030140a4405041c1c20500005004058400c0700300303007402010203c074440580c60084c01005003c3c00001c0c45001420703000c010042092450240c001e104007080351 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 825563318 1250 825562068 825562081
    0x80916080105090d0507050c09060f0d0c080f070e0c0f04050a060201050a061d07030c18030c030203070806010e0703020a0309021314100b0a030b0d0b070503010602010c08060f300114 80
    0x1b00e580c095804030203820b000d00d61000708208034038007c108903005145401d2185440d0349060032a603010744105c050f0b2580e1400c0034031640c40c1800c09240c942e00f581c4103040a202c513140c515142503004c18148911980c444240f551001c072402694081c0e50098020400801d081e42c064010741e100d040d00d001c0400c244c0d42d40b00c03c1c80100079403150b0110440391060002c940068440c0c1c0200181c0c40c410700300742466910305004580b604003d54400c1d100b001e02e8003000d000f1031400340b0002c0b0080441400415495042c510352245c0c22501034403038414140c1c001080e004450184e000880706a030000d194100c002e4031904401c0241c101140e003a907864829034001103400da01c060529040c0c5400c1076080d4109451448242e0051040340d41c0030b40d00106141502c8005180f10000354401c16030340c9e55450310317949003000180c295520a140b40d410f01170703c00100055521707640d4401c00303410021541441da240522200440302c0114400c101031003c5c0d0f4100c443d03000300054018084180c42c4051005850341d030712 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 825564568 1250 825563318 825563327
    0xb010e06010912020108130b07050702040f020307081303020f0610091d0303060105160b0a0b180c070f0809120c10090e060405040317040501141f06080916080105090d 73
    0x14020261600f01400024000d544100300c0310b9405401d25180305440b04054452402c0c5010480d0020001900011080218180750080c3c940d000c044c10b506504500b800030740602180e0004140c80c50302d10442035a882031620030020380405030600e50555640e4100000c0502d448842030250303050203401c04050072041c030b82686c2c1105240f08100c002c1d41c00d44d20783c0703401100c4551284d480181c0007440f2607085404600c0d103030032807030140140e0b0700c2c00180d190340c400c24854002038074014020b403184a04200320f0341c0b22000044554180d401075042148502900e82000c42d4000e495485401210000c18410b04280c00100b0002546040300c0b8008a242c0c41c03081100d90301c2250103204d03031440032000400c41508003600203540145c441e0500950710600700d1052a11908101d0b0155241e81d1503c01003a40108001c41098012600c1908076800d000c0c101d03044868048030303100c2d02c01081440800118031040a104c1c5410021030341850031007455503080c040e8040d010668281c6440d008120712075030310074001d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 825565818 1250 825564568 825564587
    0x18070f20060f1e1603050603061510170702102405150c0a0b1b07030c020d02150f030103110105040807060e030709050a1a010f35040b010e0601 63
    0x3004200760303510b00c103165069a80203018040d100107040d072620f842000c0d20400b544079a85440b18440d000e4080e25005040e688040c20450103500284140030b80c45203105100703050b10b0018ac4842608031000e103011500c184602c00200700c005401d609101c00c0e15404600b000d0503940701002888648405030540660600300113056200c8000084100014148841519a550224000c20b070038070215019241c213229a044040710000142410008214601181707248009070000d12a07061888669002c0d10ba00c0410b10044c1c821803244c0c10503021944c680448581c2c40c8446602c098480f00c030703002c402c8060b07003080c0012118040c0c50001030303846500c00c40c2a5011611007600510700146081030649801c03480d01c4040744c05014500e0007185a091901540e8000c4006800010311111404401c021048030148403034104042240030700040e03035100b900c3c20f4054be40c4078108088a1101800700e180403841c100b04184a6075038000300170501100c002840e0488a038416a60000e503201c800440b5002c01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 825567068 1250 825565818 825565877
    0x60f010609050d081e0307020d090e0739020f0f010503010308130504020304030c0201030507030b090613140c04030b090703080f03060d0507030b01090f050603061518070f 75
    0xc500360704100510341855881e00d12401114101d180c450f040111144080d1400804596101c00100f07000c2c8056041020f00c540d0049850103001280c1040ca8100e5044c1c1d016040d41c04001c0d20242007615200c0700c010f2030429800400c2168405921100d41076084440307200b099115280602c103030700312401d0400d40124074503816520289035a08664412407a900030011507100742441190200c0e658031180b00a500580c000c3d1586105103100b8400101a00d80080a03c0f0030941003244c540c030b0300c2d280c00d005960040c50466085414201c10556140140a96981c414640e8403e00034010403034038107001001560701806c0301401550703611440c2c6682c1c0000307100051180e001017001c3c3d00d070329016201840c0c022200030b20003281d154840c2c640c80d10b4105207400c1590180c0360180104440421481502503001d41d40707600b40424a411b00003e0384452000700341c8500741c43d05115011031517544040c5036060100d6645a0040e9041507072008010085a0301c0c0c1034046030040c0d0110b1040b21540751141c0d031414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 825568318 1250 825567068 825567077
    0x90d030e06010e010e13060507021e01020c1e03070b0c04030204360f0503120f090a020d080304031b08131211010c05070801020a02100b0616082208010509060f0106 72
    0xd01c0c05903c0c0c0141007006050382402c46d82c4540510000d1454020180180c0895005081c070240c095152501404071412104180c0c0c410429070f404098086144081403403024040844889120484d43c19449000001850440030808020414156030082e2003030742e0080e201042203030a806030317089487e031864070008030044c0030031400e41105500c05080f00d50b06100b81f480c081045001d5894518503080281015074446000c420051107c8543e11300136402b424400050500040c950086001811180d40107410108004001810b00d4054000720546d1402031110918140f60340c206049682c00510b42c1c04041340220b20300107000344503840c1c0c20b407080d500600d000e2403002c9072000550703100010703503000c441d0740c017450500156481e0284050698103a41d40c000e45202d0100622050494580c408203602c2400e0600c071030849076840c0d240d2840120f038807284050f680d0300181c81d9071210812250307480441075218003021942e010b041d04024004c010120440f020764442d509001c0c0085002d018110015 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 825569568 1250 825568318 825568321
    0xc0c21080903010b0a08010b0108151c0c080d0f1107050a09020a0e1f020f0a0b010b031009060b180d08090d020d051014180705040905030909090d030e06010e 69
    0xc8a150040000030300c001c000086480148001c918a07a1191703116400c5a55242c8244c062540c010000c0382c0d10149400d9070601c81b070218000203208846a070110f01d0001078107814803041115183d000400303070192a08680c611904070b000149401c40013000c000002d000c41c002187d8a100001c0c4210a81c4c500030044d000250a02810710005d4101c1c0b80c2d42c00030000300c80080c000580701e105e0300d00c2e40402010844000505680d50292a0417400c2500c4c070000d901c03d1700f15401141014118a05403070550517020381d40c1c0c84441d0401400e1140350401c01e1240d2619400040c00c000c210020702e42e0a0b0002d2111421000030701c100070041003651400707070240004210b09412440c04c1c40e026031903e880100903081c074448075214180f81c11541d8104140c3d1555425201b0003044160044d558070400488803a00c500340c0410f10300b80c58032b0840c880c1038001c0352115030710700810000740151040c50801615041322881d00b084242c0e5a5901d480f14a00400c1c50300400b89800500801c00c24103030f400b80c01003021903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 825570818 1250 825569568 825569573
    0x6020d0f0c02040b0402190e04060f051003023010060503090d050f1b0a111504090b0a12060f18021f03180b070e09070f080603030f0a0c0c21 62
    0x1030011011545d610560070014858401c50460301c1e5a070005031581e0f01ca071070003d070750207200451306590010169034588890801c0340d50388107010854044024900580c903020342c072070345466815003d6000e40540d0030140c03d0958021b0020403007441003195508a4140c10341d0f84034143c42c90300c0140d0703944030686c025803c1c02640d90701600003055011501a013003803034104d410b0343c8e0644190790124400c005400c108040814040040a00d0420060454903400184080d16008038030b032003144543c4540e2510340402c003825076034845070840101000305d5030b2000f1103080c0c03415030024070104e01c003c03800c01e20b045041d421950324031322075542c0180d01030600e00547e0008400300f4800311109040504040d100c0300125411081c0140400780944103400038040c1e07042c4401d0140c43c100302800b2440c000c04201c801c10002d181c0c006240000c0380c03480d042c80140c0e52a40300120f0b0071445020044840720000040c1540b400e0f5104204440250041000b0154107840d441c01a42d194080710b0662001200310200201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 825572068 1250 825570818 825570821
    0x5032a03031306051302010813050721110307050604120609061802190b27060c100606141b010e1b09130305040e090109020307031208130305180105041a030106020d0f0c0204 76
    0x4416000310100c80031941ccd9804040c80d00005aa5101440764545501001300300d910051100c0c0e180040700030b0034540c1e043c400414070a004901c1484a8002460390742402d00c81c440d03000e5840350341c0000040c400c0d00c2e811455060b0401c0c050038102c2c0901d41c032050409d5402029000c2c0c0f82030360340c030000b100e1400551248141ca081400c3c150b01030303030401000040c0910342d11940140080040380002e460360358200342c041c0045a90303a5100d0f40502190f159020b03020404603040301c5c2901c140900c07841c04c84146100741d9005080021080c1c103103201d17100d1150306454100c5000034000030201d403000002d0f641c005010100e450034010060100750240403c9c0148a00f1410065004880400004080074550000b03441c2070b40552068401c42c0300c80781c000280f50740c0040c065600c00800802060070800d282d4006146200c1e544180b0f0034603000e0a039440a5a100d10201c50081c4450345e4891200184c5007a000c0140d8401c0c440e040251054244003400c2d20700030200f2407001c40c00d0703407500c0d03a5043d016000d000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 825573318 1250 825572068 825572101
    0x1030506150a0311030a0504200a030f060b0904240b06042c0115080603031309050c0903060c2a060c07060e1609060f0305032a030313060513020108 65
    0x20a040d25400e0130760404040c400558845e030040300c40802c2c0b5060604006112124031906844540c1118085500903150400100c040366403150710711490b9412424020020700c040b03040154481a0b41d020711043c03100047c11341030344c121480026840c070505411000111180b070400650000b0301840100b00284c010740f4881c2079400d044907109049024008481d0f040e0000b60806891039040e04840c4807069402a03c03558041801c0e4020b6203014042510a00e016405128542c0d949444100160140800000f51340c2c03800b1303001e811079a0030304101c441c1c0d82243d001982d58943d0300520403c5640340b400e20407419800800c81c28050555501c50b4030702e43d5001d600400098610545030021082c0551080003480602c61504d0b040c0d558181c03c141040c010b4401c00e91084004804000381400458804001c0fa40c20328544000d421040c2105544150203882c4509080000d01001c420024241c85280c02d4140c020700c5028104940e40d680c070791503c016846580c01900003818940001c8110005007840c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 825574568 1250 825573318 825573337
    0x19061b0201031d070e070836030a110606040b0a0b0309031b1c0206240a03051c0305061c080313020a081f0614011818020702030c0103050615 62
    0x3c5500c0e2030700340e15543e100310042c201c90b286a21214003000700304540700c41903070003500c2072929202a0a1000c1d44041821944107050b400051030135410001ca5201503a02c001d62002a0549844101c0f20034050070b0074640b03011075038940c0100d00014400389094402c00380b250f071001b0820a5914146071142c00183c1009241500c144000c100407680c00e903541401050718000b030f000901044170050021000f01c8a0f1a40403015940f02900f0700000450b400c0d81145050000405103000b00b6505001440c4908254005480c42c0070303003116492048003000800948541940341803203da101c107030a20440071025044520f000d005000010005804c0800558102c1400c01000d8040754281d0000358850446910942d810743c000c41c69281c1d42c2c4110310000d0b15034401050308008040c41c00514035040300b440b4a0741410094110101450100d44102c0c10015102c1030304c102e15450381400e8000020b500806050744a8130559900d8000d541c464019144602401b401d4641209030200545203a40c0203210134 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 825575818 1250 825574568 825574571
    0x120706030f0b1c0f3c03081503070506031608070207080714010e04050c1b030c1c110118150213030311010608030c100e0f060f0a020c01180219061b020103 68
    0x4480421103000f9021744c01c5040c40300d000d01805c0b00100101090500702c070803004180003204208042900103404079032100300d049904a448002000180c100080c640015900c44030101c01e018010060406c0c02d9610b11250b11800040c0d1201241070381d035001c091056044a90090303000344115000089c08401000060501d42d0f0b4034440400000d055540494501c0341000003c104160440000c0f124500d4801502d0042c519080794502000d45074440481c80300000c481100540803030354030032510594503520806c020440504c00c036503540002204120252202c0070203401451140800e0700c03c07115822400c00601c5003040c603660742600d0b50f52400c65014865560340c1e5002982180500040c0010132108010744028600000c00504803000c007800d218540c3c1c0141280f50642c1c50005009400c200e00418051490b501c1d00007040191041d0544100e00d542060250703001185a000c2c02c1c468644201e43c982040c8c450120805041e26407449401d0000c1d84402c008108090b400310401c40c4140180740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 825577068 1250 825575818 825575843
    0x20a050d0516061d0c040908180303160b161706040902010e04230c0f0406052a03070b0106030507020a020f0f150318030405090f1005120706030f0b1c 66
    0x44200884131680a100580b100e12403c051350014180419060054105d4013000740b842c05803180013050249990082c42c0301d030034040e20805942c042060310201d07410303400c1110b0203030340d01d14003513003541e03002d4803c01c91420601c80000c6035140540765490301594200d090303610702d5a9800030400540119801030b030502085042694080e2107074000c80b4590040e100090800804480e24281c0c81c640c018800496803500b80100c0c1c411a0051084a003140d4072483c2468584101031002e000c141c480032003018801d030742c41f008080d940c10080090810203007d41007128650b0798030241541030700d104543c082c0068225504070b01c01460614101080b0310400b5111a00804900020480075140c40d02c0440504002004200c00c80300000c010030810020340f0065411b00b4900008a2805000a4058040200104c00060100d03d0000c1280c004000003081851194100680300c0e03120b0f80c240c050400020f043c461129282c3e2820b01428060740301c0505005d03807481030140c0200c0d82d01040001251045900740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 825578318 1250 825577068 825577073
    0x18051c05060604140406090f05011118061602060307050d021305091819031103030a1d010204061209051603030e0f090c09041515020309010f02010b0901090b04020f160c06020a050d0516 81
    0x32034bc1c03010203c1c10b000c807030351480341c112420301c44501c031044507208034420088040101c0c4101e1420180550646506890740c5403d8410f40e45030089881000d5100c0c400701d494441c21520001d8401103d4069403419071944880690319000c00440400d07002d0f03070b0b1044d005074000448140c51078107503a010b4902002d090840e480001d085034400c3e180220324079101c00d141020108001011010f49210b44d00851070b203894001c4c040c050f00c0f0040d020548080e580d122200a001d401d0110700c40d05608840c4040d92140c49140c00307020303e0b5101d02c42c940500d000e81c1c410041c030304040c0450b5000e6190190200c0c2000d111a0800000c1c1880c00d503122400f100d84840050644540c034100f101a4840d90040c42e210201480010030391645c2c010501c003168100b0300424802c4c0c031807802c26130548032200c2001c40d07503210403000300f4003a2044a039010241400020300d0b400000410900840e0140308500e150f040036500c0c607003240c0d00d540c032032400b5140b9049482d03c504180e00880003408104402921150f0456094 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 825579568 1250 825578318 825578321
    0x6150c0102070209040b01031103070e0601080411060c06040b06030a030c020609030c10020d08071419030209063f1303020c09090f0c01020d0f18051c05060604140406090f0501 77
    0x2a0b1702144d000b0102c0c0010b0040248110722030482103415401002d8940c03a00f24560034460001d003985052046907008507081c040c4003000b601d02c840025020a54980ca8070000c0c5540d01d1085a0590740104640003051040c680400d140d02d04541580c2e8400801e0029003c026081e0301c14501c15038144502410b0160503143d441204d01c07001401c0e0060040b07000e1001020b040e0b400b0003085d800801c414645604006c005e00d100f543c105002c1d00a401c070604562580540007482420b0342143c1c00720020841460035040e440030030310001e20740181c0e04040810180000c44028441e100e889400c0f52030b20003d100014000110041c00d4024070407070310a0904000402d80e10751017900c2e0150660020b03103201001e07003410005244412001e20040c02903170113014004060641e03d105400c10824068000c01320301003010812806004010044003000d02407090903404440000c030105c84600900300060050300e0b1910500340044015202c4400a6945650303c5008060b0400101d800c200c4801c0b0710310105009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 825580818 1250 825579568 825579571
    0x51008220308090c0414040308091e010603030e031b060f191d01080106081b0903010608010c090b03130821040b09070b0702151c020a0810050906150c0102070209 71
    0x79807910622030901e1440f203402c01620601180c017550902d202c83d2a00c0e41b076413080d0f0703034003981610f0403a445450300c2c510340e030802045404041d5241c11103219140f6140065000e032045910948038880a0f90b41d0905064841c0104051050b81ca0410309440b1a14141030b001031004c0ba40000b5043d14146540c426003c2222014a41100091914001008002c646030700b003941c1620908000c0d80941c94500c0050a41400402180b08000004c3e07282690000d8201139030904031780140248201c03611030012a000301200392054000800905001644420031402c49015089003030401c190710300681c485802c10b40c48110982068030f0072103103402c00c2001c0c00f440680240d20800440d1501d09145101500d4003816401402e01c24000300452801681e4a40c3d44403610303030103402c0b5140c58044120044501441600c40c6400d050700001d8190002648070201c6442920710181c1951220b44800c1032001d40b08040760b68a07080000501c00100d000c1d06c0c803001d4000814204000b52a00695a0200d03c51800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 825582068 1250 825580818 825580823
    0x207080708150916150e0f0d021905090c0c06010608011206020f0c0a1a1501080a1a10020d0206011a0a030b0a0504060b0706060803120114010c0c170d050405100822 72
    0x240d03460321079080e0341b000c03402c1d0142e04110303011507a00801d8000034002d00348440c8000e12030091425100344841100000d20000d101c002e003e11138a14000030140001c0c6d1100380c003915240106000030855038001c07030040e0b059410290f0040c64a046a66500000350302c200b603215510704060291980c0c180040008031300c13841c401c80074820406084000060643c1d80038081070015500484030381d5859a010301150b034001c068150209140c4079406101c03c03141c00c0c0c10300d82900940304003305a038140d000100e108c030703502c03240c4c1c221a160703130342c640d0107104601c1c1c580283c0c40c41300f1041000b41c03d564869004800040c500806000c14295503100041c01c50300d0660040700700840100f150b00a0015600c0b60400910920024514080e03a00402a000074414000e0452040c0c1d08820b440d17082e48039811442e201584400c04201458440706070150710b01c010303007013405107205110015440912030700c00c0c0d900f201c1019086441e1a801200700742c5121a0050440e002c2c5c1c103641030b6a00c0c14400e40c0864184903130 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 825583318 1250 825582068 825582089
    0x6042904090218100509220b060406020d2c0d05100e07031406040309031202011407050324031b0102010e0d050703021204180c0314040309060207080708150916 70
    0x2000c1011302c0000d560382914042400014846405541c071419038884500031400c800c210414152844280103000d2003007aa81c0080c0701280103e41d03103400144060803107156480d00030400c440e84c0e1180014418408454a08a140015080860404c02ca6940317040e84034505540748900c8188140003110f101c141c03040b180382e03c110402c005000a280701d0802d00c60100c0e014004038605030318040c00200c0c643c803000f03181614910907007003a0351007980203640b511036a40320b204190402c0c078002050754009803030b4200c0401d09103e444141c10358031182e01c54103080203001b0305003d024084440a5200b1016011070540d500c512101030360280a200c1203142641c00d407909515000d42d0304000382362240140d072640245400308018010f04103114840c2904201c02400480c0c91600d00d02c00320060090102620100e200f4ad0b000d1004064011042030309954650f030840e044580d482c915903603150003600c51444a5080302c0c00000d6140f00100099a110108808030f0750703401e4840020304144e00d0300da0300c42001c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 825584568 1250 825583318 825583357
    0x90612030813121e020102090a051c0f03090e13021e150d020a11070f1e0b030907090c2d021203070302030109150308090d020103060510021506060429040902 69
    0x201c0e0501480c4d5214449100840c02d007008200403408495884c00354504c13840c44c00181c0c83c9564245040305500d1507000c2076901102c00a0319020341002843d00810300036596200020381240848401d110801350014502401c1604141c118401d038415011001d42101a0504801020f403e407002071407048080480183c0d5440c0809c1e0042042000c051946041e0f0440c2200700710b00b00042454800b61074108081510380e815402e01250f00c0c8850703900c844003423500402081201e043c0031404408513416034806002e0300c507c0d0f050440340e440310340203025107407810380b01800b040c10502d00e0140110345039401284d5001800003602040c0780c104a490b000043c1c0c0010050013105103c2c02111001d40001e038a14241c5825030355488100d0040e01003550082500380c2d10301044d6842500050010035018065420200510800035120110040c411011948140c046100c0d41401403c44e011280003855064004c04488034500c5e00704c0302d00f00280c000b040d040c040420541020b10060081e580c43d0b480b1a51030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 825585818 1250 825584568 825584597
    0x4050607031808010e0604030521070e030c060a091404140f01090c0c12080a060b040609050103110309060f0a111329030105190f0e1009061203081312 66
    0x2c41c142c0140c4090b074100610301241c100c001070b00f03e03006580340c18801d03264800c0c2c021084112039070710400346181c0003d17030611038a641c00821502c58441c0590944540303200520a220ba20300c01c8940e8080090405141000144001f0341200c1c44510020700100d01e00c0120300c1ca40050341c10035035000c0d42e441d80040c01000003c920388500020f41c4c4213400c00695030400380c2c84483d843c5500b4400b150611a0702c00006500840c1503100e6005041002d91440e00c0f1500ea6900804200f050300070036000c2440c25081c844100030644c1580d01ca20030791401004580d0780e49001d0490500040c1440e1503480d01d0702d0351441000c8252025007000040480180310f130600c1d03e10708040140d14003103405218031003c170405203c58807800480c1d054600c00e403241c1204032800308141d803001a06a00c044590700040f034001c18a030030070303009590140c250142e40005044d03d420280c0103d4250344507103810b0800400c00384001a009a0b9001e900406416400c0707140d104586a124079071b1280c6020100003104d403124000e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 825587068 1250 825585818 825585857
    0x612141504032c0a0803031b0c0c0d050a0c0e0402210a021e0d050102180a06051c09060c09081204050102061302042309010b04141504020405060703 65
    0x110006040c140000605054501904191044243c00700003a60003c40c808a00d000003484500038101802102c140d5682c2c040d01603c1c0c0d001510350001d440b00c101040c82e100300e444002e40340406104006005098084410401c0460609130112901d00850300041d01080c2201ca08600404049152100d02e01c2c2501c10000d80d120b04400d60448000540204241090000341490302941d054640c024074110a03203061010090b20500c40d540452040803201c104101074002c4d215500c03022510250403114042000700c040c51034081d0780000b0740309110717400800c0030018030f41c0e000142030f8100080041c4181c495009840d8061000808158580f00c00c00840d0010445224821b2b0700c0c090181c180f50602000039141c0d803015188582522013807800b4015562980e002584507480c80c014800410010300003aa02d0120895042d5501c3d440c0c0b0004406030f00305070241610181c0300c8011240036648200190880b4400d40c0801ca40083d402d0001044545a100040ca402802901c600b000d01104004079031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 825588318 1250 825587068 825587083
    0x4050a1803030e190305070f080c1f0b060901170c0910020a170f12062803030f0c0308070f03060905090a0615030803160c051e06090c2101061214 64
    0x4561340e90146a6003ca94054103881d01654420b802140e100303050308008207030f401141191203803409a01c018004444803078581d040340c00c2480e17030240318240300003081140d84e0281c0101c8034040341030500340c035080f102034005590703100866071000b500300200100400c51034a2100314007409603006244800600c028080e01c1c0890301c41c0d0604e818640099180341c0c1405000d40314803945c0201a400c041038880e60350400f071960031046000302e1880c0c446002541118101d00d80b2050300410002d14030300c00c09910513030240032000e400d600e41d00b40c25200d000046444890007403000f401c1507600c9202241001e50307405150702542381800180781485c0c02b0f00b4040100e440c40a10382201404640081001400780b1050704d030300c001d401116400038440010140c40407801c1e44d40090460158030401401c038100202c9005150301c01c942110856a120b80c0d0070781e69048140103030b0364048440301945800d41034104d4410b984480b01c40c0081945a903451242600011401040346c4803000c88584402d1900100310707a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 825589568 1250 825588318 825588343
    0x9121211060103020a0501050c0c060f0a120c0f08060d0b010306060911090f0103022b1d0c0109050f04060f0b21160e040902090a0c080a14010504050a1803030e 70
    0x6001e6075145030700150828449108103410b0003008a6400c1240c60180720304560381601808a660b50000c904050f0303001d90280107007101140d04802405000945441900c11001c402c1c0c80d040c44010141000781d0710a1001402554000003108500000076184c80c00303039008601c02c000c08902d550400743c4410580300c61040040400c0d0741441950840da48450350100c00c42020700740140c0d00d45640e200d540707041c0d4040c68080c60900c003040c81c0e0582040c41da804446509110030000c044051450141c6403141c0c2c120581c0c90010344420340a000f5454100c1c01c5004031071000344001130055985400d45240e0750507901180c80c4a40104841600146403481d044062595449207002e41c50b020110144814442c0342c04020006030041300c0f03916840f15031040d103465400404000f4145050b10980014000840062001400d0080810307072503c61405070300340c000003043c825030f096800c041c140001004000c10450481e5103a50300707801c4800f9800c030804070090082e034000c201c0180c0c00500620b04070f8082c07400f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 825590818 1250 825589568 825589573
    0x120614010605070206070b06010309051506130212041113090f0210050a02120304030c1707060b0604050102120304020402210a110901090501050d0905032b0e03030708040309121211 79
    0xc10300165140804c964a41c0d5010071f071040c160f101c40c0c0c0100d00805500c0001481d0303101f00e6100360400344c0c008820900c502011900703689071214001121081c1c0c001d0420b842200c1d81c5440106000a0784070008054002001d044140d110707070210407000c1a99055542916062260f42d842401d41c1800001024620502c0c10428a00411460000e680b407904e2030380541301031b2022000c030701010b21500d80241d0854020049420b8800302454031880b603070109100b1540c0c1842d2200b500090304248054508982c41600902140041c00502c441154030040c02268001e9003040b40e00c800c031518216110340b1490b000c4200a05107449a44502140c0c8160305808190800740000302c216a484a680c400780c500c20700e4039a807030340741c1e404405001d0000c4540060090002280303000d00360405030010b21840e008000d0b017101d814103101c4100f08417000342c0c8558540390010000640481d009205898015100345050750040d5a51410354800300c8500f0401ca40d40221500504800f5030321003040450702144001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 825592068 1250 825590818 825590827
    0xd0605040239120306010201050a09110607020d14010615110604080702031f050a0b180708190f1b2d05040e09150c13051504120614010605 61
    0x100754019000392901c0310214801c00c0c5102d0941d500c420140aa410b8010101d41522000d950006841d8000300c072410300542c40d0000280d031603a540d000308654281c01c200021105000d14042c0482544003040990300a0401d801c100006503064a41c0c1d0454141003000041d02070608400c0b20f0380126120500c410014403c4508260910105090743c01503446881c15a9074007191011904028903a003410207070007510302c400d6190f070505e6044a441214440010441c0c058180e040181c80c440c092401c2d003100842500140300d10340100c1483e90001307401d040c001111015000010142d40084c0c00c1803001c00e880f45003601f1085494240104c500e50503080400c1d07000d10b030b005002500d00040a0069170f44c00481000c8030824001c0e4200c81c06440503103440c201e0b0345402101550f0347c070303002501618002003400002e05c2c1e40301c10405423021820900545c4d010145070104009880000301040c4101c1c0c41c2c00c000c001007400c40718090340b040500c00c510110700c502c110760b0041107142d1b05a0020040c001d0810 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 825593318 1250 825592068 825592087
    0xd0504061103090c010f0e03010e010c080117190204090f0c0311040239191502120a020702010509061b06100510200f0f0601050619080613050109020d06050402 70
    0x60030070001c100a1038005131b50050040100c81e401100159150035510b1703c01d400084100c10341041020820503201d00c10a83d0b42e4442c030a02e00600c24128030207542002c0b030f910b001c2010459a08200e607000400102d40c4040d940c5070340c02403c0305684101c8240801c24820410088010b5414696600480d000c40c101141e00d8038801510190104100e445030400c0710400c44c5040c2c24210300e202a058004030383c180c0513505000315000c18402000c0e07407000701040c0708004800c0c0900031240c80c500341010401c1d40340c0f100345030000690400d403412818040b040c004030541341c5a08010b04041544d00510750101c0100d040d00e10300380300703002d002c1c11015100c0031014041500d43d0807181c0c804143c0741c0386c03072a16011b4000c941d1080c080c09032071030749032401003800c3c0381041034001500340400e00712003007a02c03001d990741d00400201d88140940a203101d00c004036800034031402004003c0c2d000b48094421441002380d41d80b18070444800f40c0240143c03c2c0e000c0751406001c4041d1040c03c000c1c10b4141c0d000c44c40c040412 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 825594568 1250 825593318 825593323
    0xa1b091b12150b0a05120a06120b0a062301030b030601030c120c0504020a0203030612010506010f2a0c0923040b091905060421120b040e030d050406110309 68
    0x107010540c84645803610003a403a165880399100030842c00c001c840e250342c00c00303200922952014501c52002c94940c80468010315403481020100d1b824544a0704401503196a2210081001440c04018580d950700005002104041e05507400302d5002584903440780d520005821140c451a0312806a0300c03110042c400642004010710035901c018964111203440351401c1c2c5505c803001c2c1c2007a9042400458600007203034000002d1401a4001c0b00c50b808101e80ca0000e090880d14111001c074002409000f403070900a020b86010b1200c0640740141e0400e448489030202c0d00d03981c114a0884000101060400040c3d1040c45031454040e090700c04854001608148250f4181700a003020380702c500301c0d40104403100c0040042d1245410780001c4501158200e05100e0b4640901703d800f9034071418400c190182c1d0040048205075200344640758240340e183c6580c2c1c3c52004101c925801604180d0302c11030810458000c0028005440c0039040114691400d454400252803400c01c16144042c814000d000110780e01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 825595818 1250 825594568 825594587
    0x714070f0b01120b060103020927010603271b031209060f030e21070210031407050309030a030e0c121f020c0d08070210110307020607081e090a1b091b 66
    0x1f4a001368450700d038800003400050242000710524800c0682030310015421074022030407500d0b0f60702d0400c44031004282c402c0c018a09030020744e810a50070544600060020440300e10840407640c1d50280c426100d40c0c808240c65820741022002c0382c1c3c18001003060940c0400004009001803406211140c0540e01c1c0c2c0d03958032003111650510601031003130451161145000d03200071075001403000982900c802d801030f00500c4010003101c0a801c107500014459402802243c0c02400360400071483d000d076002c0118000c1c2820394905010740070711504002140c3e1105446009008600040c2c01c000710300000c2c0c0c48070180b51600c24a000c600601c045d840400011842d50700303120b200d0816000c40e40e1035500c200c0c01d02140758580c1011510740b0005a00c0200803801951040c0c2d89602100e919840342c42003511183c00c02c84258541c000701743c200c84101408401425000b0125400b200c200d007200340e440d0118071010901500382d01144c000104002d2009001e0300700d94243c12215a0030601c0322031001000c0c04030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 825597068 1250 825595818 825595831
    0x7020c0f0f0402070501061e080102120f060a030525051504050910050303160203062a0c0f0a050d020d0f080a0b030c10050a030b041802090714070f0b01120b 69
    0x2010a1200d107503100e5404545065501c4030082103081c1c0c460b08036001c0120b84145080c101201c0010100703410005208950210450340c180ba80b07280d035143c98024a109000741441d802880c2010b000000801c00c100d002010039513046642060f460f0702d0043e0502000701d034001d900c66101e900f5036040850800040b00e082d070784140d418603040d0340c3d0140444417010f5942d00040e0140300000704026a15485040380c006240b0031415a070036030300d80c0d440345068546005403c018892a004583d15020440301c000c2a5072012502643e50070300f40c1c1c502c5c1b01c0c04c0203401801521240c0154030190003055062017281c84202e9181417001c2503d008890041c000d00008110b10401652a0a80b548540e0704001170b01108200a103205221280558000e00d250407480490b0040307814031440c00a10715041c002c102c115240010a003001c15425000c0000480014040c20b040c0000c4005500018104070001c1c06000e0003210328000b41c141c1481e01040400e0164000f0080d11807028081002400300b0407090740003034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 825598318 1250 825597068 825597079
    0x1a0a050913020105040f0f05151c020c071a030907210b1b0706090606060f12020a09050d0c0609050f030616050412030e040b0f0d0f06021b030d0507020c0f 68
    0x190502c0161041d11880d00100c00504c480c40002640c908800450303400d41e6420382e510034101c05280c00c145024010000ca41440d4960460f41d0356942c19540c0c0980006d9508070708a038a132564800e0441041c0c03c04031210070b40210700104004400d0410805200100a04004800301d81c010410307010007500501130017040c07003900310003040084805410118940d0000d0121564032071191402c50000c00f05210211072140c01c04c00c000650b58010700c20180d606a0545030900e00b5403070010280000d5011149241c14000f1000c03012450b81c03503540b03428200a201e0008200b4203030501402070801031680d0700035440342c0300d00b00c00c0d8649918040790054000e0001c0f02c20107403142441c1c85c2074801d80070343c0e003040c5c064414103141340f414103610100c03503030000505071800c0102c1c90035281442450500e000700e0341c0d0844440c11030140090740382c04042c2400342c0510801400d14110b20144020001044066107080d032001c2507038185140c25125040e08803911780000c04c045d012440110310b010417021141d5100b036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 825599568 1250 825598318 825598351
    0x2c011b081e091506030102090a06030c02160f0b030417030103081308060c1b01060504230603070b030408030c0c0717150405210f0d0e070603140f0703140a1a0a0509 72
    0x117131006d4064078192800148207141c031580740c000c024020301c00756454800611805100320440004024002c00390b41000740130b1503545061460f9010141e0001d80121101481c1d02c001d0010700c110030001c1c40c0a18881c00c04540e490248810072035410b503c0341c105940e80d400031403d1050b5007110764100c400b01c9058449540040003821001e500401c03d541c070440d00315042c407400c1081c85894000103002d610034401104a1900c862050507590b076030320700410380280010000f04000c6490040650340c40070504481c545004006205c2c2c5040a40743c1c2d10405901c00c00040c400d1403080c013444103030b0038058125180030280c981394598076907070101c0036458039500c400001424000c0420350100c440251841c0c184590f03c03ca4495002c1c01024020030030550740c0160f080110300540309004161441d43ca0101d044c10548030205003c0c0b240401403e00c40c141543c4600c0500902003491400344120055480003a0a000d12194003140c0b0346100b0009120315260f00f03051140e0380e9230f0040f4079002000c0440c19140c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 825600818 1250 825599568 825599581
    0x60306010c03030e250b070209180a05030f0a09080d0f0311040909110a060c0807021c05060a0b0f1503040b07050403080304242c011b081e0915 63
    0x1d040214284d40c8600440034907076480c42c07074207030078903249402c00300d44407201035aa2445032514064400000e600c58506400315492040368101030380525510030954030189403c6d594a45160321440000c0c0d0107000100c0c490020030303046661400100184001b900050f40c10000040154109000c0c0344c00381590351243c00300d2151030801381d401401200390104240c02540c280441c2c4030360000a0980b25594602001c00c01c90310614505600507444624241842103540c00c000740351034410100b20b108035074a0008030109004103c43c602682d1000e1000480d00c1c0c01c00c045c0300b001140750003514010342201120304000780d403400480707600a81000c2c103054592100401224a4461648090007602000c4240018040309142210210840c0d50000450360b000c50b0041c0d040e148041e10032044200780756000e074ac14200c5040301e031940c990480300008620200c00f001205640241413286c0004214001704842503a002e00001c6254544002c1180e84e880c1840c02580d4036110301c0024405c21483d840420030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 825602068 1250 825600818 825600821
    0x1603020f040f1d1b0103090308010b070f15050a151a090a0b0a121404080a0c050f0d0f090b03090712080c010c0509040f0b0a06030c0e090f0f1005060306010c0303 71
    0x42e1001000d00619001c60f0b00d83c0d40c900c0e606070580140240c041300861198040d00c50700104036415100da40c017980c81c00b290980346400202007a220004d818841c1000201518500091041e40060020310b41c20004c1c00c030401c0b244003400085030240b102100b4000f1150111745c00b60b009900504982d40e41c0d048001040c220700aa5020b140895004101605443d03006616855210b104000410082245140c94080d044094401408030311040140e040c4651103203002c41401400b0b00c085403213a600380c0214500e40110a034010b0002120340d029030440c03951210180000b843c225002c02c0c11414a445680d4a9500314481c1c008528180002d950030000c211042d1508000d6980c020882041c0c100c0d0090328a6001c4514644124034103144403444078983d1290003800e00d4060458426542400d10035002012000a5403044c45010480241d5559560303070350a1041250929505140c248004103900000300a4100902e0881141c414000d80e124281500e43c070250910341038445a4603801c0580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 825603318 1250 825602068 825602081
    0x190f020d03030207121404091a1809190507050f010c2f030d080c0a110709060911040602060610110f010501060e01090602150c0f0c0604051603020f040f 67
    0x94000d03012203100000d042e0143c3c040d0440e580640040024442101000c40b080451600f00f4140035405110620180099600000e1480007110140d0021200140021480d122000100803416000307020030000580a000b4404514110b009070010070071705556460700c0d000c49010305400b03998082c0082c100c60303101e188694051900004844c0b00d101d60400300c3c41040d142000d20a58020f003142c445481428001540f9202519650315880d0640b0303517078000003803070344040051f4040114032096183c1c91882032240c580100074403400021990f20300362091080c0c40b44003100400441b4284010440301e80c000c0345150b03000700c048500703c0c07011860803000d4601c9600000111914480c12220280c584815844203060350896103500311a4400301004464031092401164016003005607101c01ea14030503016180c1209641d2031980c00c021083e5128030080d00455001c1c6e607607910844c04d1000340401030007070388510703854051403581850441e0046004d14405641840c06207036102030495240500d5405070 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 825604568 1250 825603318 825603323
    0x80f0c2206020601120f1b09061e091e0c0302120906070e040c170a020403050a080304030905090c040605070f05190507080706200c0a0905010323190f 66
    0x5000c0c800c0840e04100c0d00d20034500401001d8402d800010030042d418400310403800c2c0e88509003070350380304079980d800882981443c0710f125030070060007001c1800d02481c01917001800c02080040301040000d95070300000301c4268003100d91700346044101a0044180d42680d08800300500000c41c0031500003400314001c0c490341d0030781040d9400d440103101e40c031030700461064044e0004e50b450401c0080b8400400c412100071003030751400304001e480058681c4100d20301e050740c0142c07031000042c1003a541ea180e2900b00303c200d45044522110000c1004209900700110f58003800042d102d002d054036042d0001d290314492400340c48140003003c00d00c401044500340d10070850340c4c1e20200359585a018041560441d849211048a460184050106840c01c00103058070403500f803561243c2c0380025010b20b42c00c21003140f40d208421405207441c403444175216840c1c0c039001081c4003100096158074506000101c5940c40d00c4031442e21040c80c0c814882c06030005003180c0702c03080b40c00c1c5034400441946030075403440c9442c4000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 825605818 1250 825604568 825604597
    0x1c020a3906020904051b04090c05041805010f080a05070303030906180309050f09040f0327080304260c091302150a0e1206271b0a060f080f0c 62
    0x30100320894001d4109064203990a00041d00c0d4082e030000240003c146080c142d5030144000c0115042d641c11500a180c400e0618a00d400d49481c049405030210264142c0026101c0c0010041c0c0d1061041000040140c4000b07002c04e203804d542d600b41c80f40c4e11844003a0400d91140c9000f0f050010700c0e8404000800700c1c9940c40702000503454050424046803081034071502452040d51010306000c03400d01d1107640d00004034840c8110f0380d0f03000d891400091942800d040359070300d964240b00200d07a880202410785034000310b40f240d243c14641c2c03070050400300544d40d08a90a103c000f41440c1d0000e4902400c2070102c820595540e20200c20100b040001d4a01030341c4500350b51540d131480002c1308003e0920b500180c1d100000c0707000010038410038141c4180050080d5021800141c545114482d8035000c0060000c00f080e40f0120318074116142c041d160410105c1c050314103407200d6052500701c201c00d004100500b05001041e0b8844800b400070709008151302c1c190072084001502e01c10141041300c013036602034240c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 825607068 1250 825605818 825605927
    0x609032b24150507020609150906030109091e1101030f1518110406080a0203061807050d1b05180d1a180114181e031c020a 54
    0x2621041200c10b100c1d5510000c1a054110300341403041c030403190704540141029260403403110912170081c000c0c0303181c1080d00a0912600c030311641d0f2207000310b00030f08064402060380720700e60a0229101c0420664595144000b943c40c400080607000c0d07029800c6001d0034009052907030110300c2005000c00740b200f03840000c500000400c561010011041d194000010100015007548029070039034415801844c001c1411903001400c003040940003564404000b41c214400188070110802020005403076590214202040440031021035100700074140741000e10903101003aa14501904500c501c00d1703405500c1000c40320b0026184c80341401800c0966014151004007508019200704000007518546151401e5580709280b205050144801500c100d02c00034a0740d4440f481000040010300c3c0302100a40100006004200007560b900c414540c0584080d55a803104040c0c13045a440c45a00809500741c0305010442c50f1581c0440110b803864a2400940403030840b4010920f000e000c14003800900110440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 825608318 1250 825607068 825607121
    0x406030c02010f020f09100e0d03120506010c020f100c150902120606090123090f0a0c09150305071202030a090204050903031510030209030118050609032b 68
    0x10300442031584150300801070410380c2034549042c1d1140c0c0001c501c14080502206c0c0341c0740303080ba034410070243c414106103d58904010201d001030034080c0341580410302d00600180d0200d11802416840602441c18528000c0c00703600281d002c0c601c1c2c0c1c600034003800d401400000c07002d004100c00307407079142c10943d40381c1d1011201e848a0050300544004a004104024200c003000e4800101c0c0c60096200510250b00c503800e00044070101c180309184540d8124021015019035101c8480c654050584030740d0928443c50304003110b9085ea00e150591070b00b003240000342040781079202100310101c00043d04d004102d030b441b04802111840c01c03d010724140288000148001c207907103940800802842074401b440b259660b80c2500d500ca02084500d004d0202d01980e0060f928035000301c00c083c01160904005040842c0c6001003400c5850505900c21120100301c00e000c02d100080106580c04400c0c50000c40c6084004006c441c1c1044032460003006203404410508546a850780000035458081071400028a8024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 825609568 1250 825608318 825608321
    0x80901020c180105011701080c151b0a14030c0303010302100306030507080c01020d0e091f09140103110f0102120304020a0302130203100e01050d080c072d050613120c030503040603 79
    0x2031040502140050740c00141d01450310441504840c0c03070344040c0c0980022101070108540324ac0403001d01600003000207040480c60340784650049284003004145110083c41e14007804142010851026442400560040907001045906590341600c41044044c91fa11058010304025003004100307000b03140c804990f01d0400101d00607908000da08076070858011362821303103110340702544494205802000048a10101d000c41e101001c1100e5041510300d82d0359080202128032005123050010fa6860040041c02810240f10381c0c04032080758030200e041c42060010395909050740042c588141d0200c00101556130b560b102030021500613241040038408520070500a60048400c10f910404910300420003501480f0381038140c1d080038141e030401007a2900e0b8030080760404c1148401d544581c442c0407445c2c00138140c00d203194903c02c0e04580c0d020f40603808042c1d044009900458001c80c001d2005044198546014070704803808a00c075131400509a0074041e05646942d00050247e2200250004403194076 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 825610818 1250 825609568 825609571
    0x6020f07050331120f320313120f05010504030c03031506051b010f020f190503040308160e040c0f021510410f040207050604080901020c18 61
    0x40b10300c0440348024070710360a40f0b03240c100303103164644000d204003d01540c44401d44000b04030740035803076521214202c4c5c0d0340e030b140711103110b0101c2d1004103440d16511070941031210980d1110f41140c02960411507145c1800c0b419501d14800d20715028000c50949041c0845103402410340342d0003500074005481c1070b08019044990460013203000918041c2d01000000c07441d0503160035a0101d654861410415194103c2032009c1510716461a55841160303020ba08402e10003080c2d140c1a01040c5500e0715481c600441140001d901c540003800810403c100020303501071035180c0c6c0303c0034028402d01100341e485001c0314032030100c215642e0403a06e8400007140c0300340c01684800b001c690a500f214295410b074041c010b00327544181c5060290000103d0240510000107290b041804d07540e28942c04600c0c2c016040c550058524900c0303102c0541e6a9810301d04500b0242c441d20240003060f00c00b035107805c200c0d0707a420b59a41c0d001000a00a1130000c107508050744c0c82444801d8408000800100c100654040f281d07010110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 825612068 1250 825610818 825610837
    0x807060b0a120f06020d020c0715180e060d111c02041b0c2006220501050313150b04020417060f0709060f0e060c100b01020106080304030f06020f070503 67
    0x600302000648415001c0d0610146030f00210104056031140d850f00d010350428556040b070f941d024440184400700402140e0014564400183c440007111a40500f0a81154000d004120407041091100d00d0900c0785440c2c01c40b078207039001c150003503560402e803200100400c5010b610801e0a03c0e01800f0f00040c01402550600880301000300801e0315100524100f41050140702094003481010b000c500c00015528012032243c0720b0000040010b000201c641e4044c1050a400803419110a030345916070580d0003018080a003801e41c95410100f4211703000c0c4003440c00040c941c41e0845003212445031150050421001c01600c04d5440d070707449000c0084220300d030a01c411800c2c42400001b0b03080040d010a244d0050129171180012241810400c40ba424000c148913018005054000c0582e611080010100411050007801250180c9a200025031b031140a600b41117a040000174003600a010003180c0c1101e900c8a02d0261041d164a4410041e00810124810342c02010420348107200c4080018001d410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 825613318 1250 825612068 825612079
    0xb220801020a020d180b0f0705120a121404060203100e0c0408010b03150105060f120c0307110616051c060807050a0605070b01090e0c210f06250c0807060b 68
    0x1010f1042202d00d0012800c80417590550032104120400c2d1490003840e040300481105440c2400c40e4072050f00c0c0160030303900d40e0071501c000554695071642c0300c0d04000140d00f00f110140114000d2426800c20024080c00141000b540000032842c10b2000070b0f0f208000301000740d81c512461518104807171050700140306010855003089000303c00c0e46800b0500c500c08144484110f001a400c2c8020301400d034015004010000204200c0341100d17540003002144102807850450340c1c2c0c0d240c4000e00400d00300c04d09009a449602290602c00758010501e00c0b00d12482c3d2601d02207468449103250b0344d03c0e4500c0390b80c034005190f20b0301c000450f600e08082400002e070b4505442d04031149558110840e00b034441d10754060306200300303040144200700c2d141d0040c007000400f00c07080b00c480340561f000062400c0c10081040e20100c1d0004903003c550501481a030310b030300c44054054405444c1141c100102107019200d80f42e50010107102e04024140108030001905410000682e103a01c500c0c68a4001041c030000342c0361151 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 825614568 1250 825613318 825613333
    0x30108070803090a060e0310110702040b06090121090b0103050a03110a203706030b1309020a081005340c140109030305060909010c090b220801020a02 66
    0x2007000000c4605010001d0802d0065a14102c01213039030340481c21803964580201084070500d600d19004400d581d004010040350380b11042d10400c0101c81c4078008050054405010301407050380c03c0b03402d00e148006600c2003048627940c8001c107003006042412008162a1000c00007009001c1d00040103481180319440e5001007071007201040e51f45d400407040041c1440040c481842024200c00041d1032100c6014008140b4014080040304424602c140d02030510705264070084062082d8101702402000ca0b410104042021034004c04c01103150400c0704204283c9607034500d421925529500b81c020110a000d81d41101c3c0d10070910400b0342030036180c00804000b800c41d4006003018003d00078820b015010030010205d8541d003020b4034049580101560360125000d04946820300a01620401c944665000a010700d4910100121404050850f440984c0341191248401c0d410030000c806503115180301e86c0d11400990038a00400501d102d540008500a40c800105030b201500600424503154007a140d50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 825615818 1250 825614568 825614579
    0x506030d0207080a082a01231504021305060f040920030f09120c10050a0207020f24040909110d03021c0207030819111b0f03100e0303010807 62
    0x850030140540942a00f001c080700c800225400c0081111000c25802d4091366006c261000001140c0c002020160342d46400350354290904070403440c0101040f40c2540c4606042c800220404402d14900c0c030f0740902ea001905516401100300340d04000e10000385038503542c0076400c0792403060740c1151060300015410210800400840100001001030b49900d2880c20b40e610200c5581d01500003410b1000c07035005080d080610226034a0007803079421196001405120000d03034681c42210002003107046518414009070f00143d075112121115030808541b90420462250b003011404c051142c40070308450800540094003035087c2d084881640d00030030790b20390115801c40c180514410100d10040068000c0130000d04400d09000407801c0440e031520440740020f8490b55011420303445191040d000c5100200e10402d20351340309212000100010010309a074070030580ca1030382c1c400c12403c0854403400c9032140e6240643c50800170301184154003c024450300c0c001c00350103a101d60080c01061143d00540c5c001086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 825617068 1250 825615818 825615823
    0xa09050a24031a0307090c0e060f0405090402031501090b090703050f0601210f0b120a03020a1104020d0203102105061303170709090c0c0b0406050a060f090506030d02 73
    0x30032052009214240d9001c510840c0200040c100800d18960640020300142c4c070700308040409000b0060000800d815078101c06003141c0614200325200c3c1d807040040311600c400e4482540d0454a043e660112070392590310009003070501040e0080c0203544240000155110b5a81241030900415944462241c40f4020200c0995030102c03851440342d111007000c1007a6502c60710070944a981d40860602c960100155600140c4140c140d2500920b40c40f66031800807403900c00c0024140e024548010807c80c5115a40a5151600400d014294083d091050000b41d00c270340e0102d07038178044a94011540ca1615150390200083d5501034041b842c54007240b003800d91a1100fa140d928650840c00610703041c0d54141e5841029124110100d04100680d28501c0307643c00d07420701c0c00d40124840e80300c0c000f805041c21802c00c102c5191001c94402c000c1040c1503d8049402e02d461660000d82000021483d070b5903412281c2e000d8610303075211414038254181c000072a00201c2d4090390103071100304c080c0d401000d0a25012a07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 825618318 1250 825617068 825617099
    0x71109040b040212010e0102070507050a0b07170c10110a0201060603050603190503070503190210020307050f0304020f0a060e0f060309030405101b03121d061302060f0a09050a 77
    0x424001d42440801c0140c40c01030f0b003c0c0751400e540b000200300a44007510709800d83e0000e01d8101c8955101003405c0c4150b20b0b024602c50040d205c01040c007402c11001ea1500425031080c5007605981802c0040d000c0103400c0b00b4008031021500c0460305011f00c50700d460600380280d0050103064015483c044020035490b1190040d603004400c000c0c010004c001c08403c001902c02203210b0104d60a1104020b41c2d030014600b8409040c1d40c19142c400301000c040c100304043c0c100219111800015407040040000f85a0020107a80301c40314401883ca45a40da5840811443c0c03070200c9419910108100000590b00e030b114000341c400c00c2c02501e17948180c1c0c098200740081d60105441c50101a0001c0c00184918204280302814000943c6814042d0b00030448019a1242003004254009409a164422040a64064514820a111040d0700102c8c8441764080d150b01000d0615850206080e0588080d580d80d20300307980d00d403001d02c02c003e9982d00d49064040d00111407845464040d10801c000040c003000c10301c1401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 825619568 1250 825618318 825618323
    0x406121b0e0103020c0c0d1214031e06190803090f040e0a0602030618091e0c0306070503070c0b011221020c061b010203090109020f032803090b0f07110904 68
    0x2071003550075a000540107500103480f0300d021807082c0705003c400c558400090ba22590b0180b22400302d840b40310380004080107211030140b15151000c01c14400340703100008040e0640b180c031418104203520345400065040f080d03007046200b00d415044000c02c8100001c00140034009007200d540440c41000414881034800c0c0e812480341d95008014420041841c1750002c642c081c00c01000401d0003018414402d0300e200d030035545100542d2060003019000112001c01c3c0240c501b00100801e03081100600184e41c0d0000101210104403021000ca071405000b0146400595800344a40f03001c0d40e1141242160320044150650b1240c03034040c0f842420b281c035155400c0030590680c4c054804803104c80c1c02e01549a1041d510710790140f42031004000c03082020300c082d6001c0c1c80420300102e0b400e0700b98010406d842100d0a062482034005209407400c83d040742c141583d004041c0201e0b003510070b010f0304094441e001c2944c0301c4c440e000c0f400640c0044010321032005040785445400d2180c0c0c1260018140200b1942c02c8500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 825620818 1250 825619568 825619577
    0xb180a060c1703180f011509020f070f02030c0303040909210207060c0828110609031b0118080403030f09060504030813031523091c0908030406121b 65
    0x1841050001401541d0220100901035001180703a148617281102e5644031108695640c607440d51000ca4400390500100004002981440ca010789240340c10f00c10104000c0c06c4800302c4245008540b801d00000b0034104004084c0da44642d51040101c001c0c041c1c0180444400d004160825404d0028084080149007183e0040107400c2c14403070280d6981c221280300740c544602c2801064144582c0c0d180502e201c95007801c10b11310100254801070080c8032482003400d43ca411038420001c417804004180c41a150200c40c5402c1d0010115050b50300504205400000b0320f40c807900d011040c084050000d1084a109035900034601543d20000c540003c41c038002c000005000300b104101042c103402c0034100c54a0503650340c00d1003564980d10600d881c44007007a40c02c5003075110125070702020100e0610740f0348201c440160680c030b0f2070b115030601d40b00e1480c10702640714020303000090412280700300d0700d840c0941110412a55202e45070f2102030001c15105151405103420f103030405510400c55040c0000e4010349494 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 825622068 1250 825620818 825620843
    0x40110403120507050102041706060a031110031b0908190506011208190f03060503070f0306020705150403080f0a140c0a050c0a06020406020601210602130b180a060c 72
    0x88107907a0402024104041002c10302602001c00d00a100030030040469400c030103400e01d4180c07445804c001008111521030300710904208082561001115200001110344200440c0b000800350000e0100361440412000301c2c4100b480300c00d8011211105540c618002c071030380301c81c043d0143c5070000540c80f0014610380001c0010406c1c00d00325404010a1807080d1045418007102c1201000500c40080d015400070300030483c0b040c8541e07050f20943e400342c102900070340011410541c038400d582540e0710006090b281e0005070700041c0302c0148590321010440b008400c0c0281000c5c10000c2c00c8841c03d0b40c4102c1c3e199045004982c410070240710b039024110752030481d020981c1c1c3e090b45030815500314041c841c4c188001001030204041c020710103e2203151141c1001a01e550414000900d0050140c0000e503000304d2a4200000c046206801c51410380e90100d40540c1d02c0c0703680241c00b54220960742c00340c46007410214955080e000e10b0401698100c2c0e09448500110740d035854122100103000f240607100484415 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 825623318 1250 825622068 825622073
    0xc032304020306010e150d111903020a050411041a0909011503050a0b01020a0b0712230106080c0f0708040e012c06011b0c05030d1d0a0b0904090240110403 68
    0x10340818207d070047d08100b104858113004241001e03c15407420750b0003800179030203204500c3c058128201604098404000480c050811141d0511036802180781306508911160216081c103000c0b85c40f100009008202c0300d580d01c1c9220740a50b11010007001c046030420000814000040c4500b41d507441c0160b0042c000c50b941c5c4e840e42e001c0344030041c00c3c1e03400f0010005400c40c18020203028203a00b217010701240c122401d0b150703070076045607600680001e81000002e405101d1004022030607144000071070700c6810342d43c0180340b4141005c0d125a078080b0808081190001a119845000001881c02c000744020a4000c60b2090040940c50071192a03000c070b0400149039100000d203c501a6100e0311a00c0700340c1000e6100c20001e07103000c02c0d032400740d800682c0d2074201120f50001081c0002000344241c818000d101d060030b0070301c001805240005d0f40116502c050a009542c1c134022500003c0c0d0040009540d5400c2c8a80d2054035841000341540b2080310010b801c1c41d0556062040980138003110308514102810365 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 825624568 1250 825623318 825623329
    0x241503020d020a050306010f0515120118020c011503021806060d0f020d0e03300c070519080904150b2b0c080f01060f02100c032304020306010e15 64
    0x1c41c0d003660043c0903801c0100f03454030104403140c040c201802003400801d14210030449900c07101d11008480700c105004004541c02c600032541d06490703008840400e080111110349000380140c0300c00b542c03990700300b503010070303102940e80454801d480c0260b40c00100c8900c0006142c00c0c0da01c083d17134819084170b0308003c50024514158854400490b401101524044c40544403500307890645c0141100c0707420014554140d0107003125100f100780c030240201c540c560a134000c00c00510f0001005c5038044100003500804000c428012030120090b0b004040b540110036090080c4103070131080d080d034000d0b842d1811181aa002003640f9100300c1d80342c4800e2700c0c6010140501b01c916035140701c1d00c000380901100b103149036140c140c5c040c80d0144000c0342d075025460328140104150541d0180d010500b80100000e00010041c0d0102d180c400183d008100400c4c02c1040180481c001c28150b007214240d42805421003030040c61802400d80114003ca0480324140d80711a44007511410940e02401c1ca10300f1004a0129420700c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 825625818 1250 825624568 825624589
    0xb0f090f1f0e060109020306041d10020702060d1506020f1501030609030201110307110d2a023106080606010906030e03090a0e0709090e0c09061c24150302 68
    0xc0c40c4000ca0301400c4607201d0b900e8800203030801039880da004000c000007800e043c42400031610b01d01e803610354040c5400883c00e07140c11003e6050340540f0340016406042d5120102121400f1003280030400009424850000700c8041c02e00880c0010b01039000aa00c0c41d401c0015001c083d60034404811050b64a56510f0034010544100b00b10255501c82443d6080c58001c80040e42c80381100d44c56206106242102150401c0741581410703007400030802018103122140c1001c1d5114401c203000e8038400b00e0742400001c20107803450180281c82c825886507442074407291403a815030071020794018803c11b62504c403036544401c42101d03204d00240846004010f1544030780c11a602e00e505184c01d8a2400400300c001c82c6030601c09800c40c440038001181402004c0390311010340d500911244c4000c004180724418000d803110707031000c2c180d803151115001203115540da265a01141801c01c4044035401c41c1c00303203030174481081140c89071509150b07452142541104607000b000c446060944425650390305503030821002c0c500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 825627068 1250 825625818 825625873
    0x10b04021e132103020f060f01052e050d05060f18040309050901030303020c2104140102120c0604031e05030109020a05131e1403151902070b0f090f 65
    0x20b00300c40000310f202410700101440c010382520085080d4041c20060310380380304030840394865407102c3c04004081452005042c1134800444910a86090203c50018140f0080890101081c0503054643c2c90980203c010001c0c06040403051010380d941500b0001d12403140040e083d00903a00380a204206d1120915480d0b101d441703402d00d665050344950214002540907001100460b0340040d90210303400007000008060407e9211707030681d48480340c11110f8a030149106d841402c0a40180040d2036a00034403086402c081100340090f00d03020b2507240740313550304800c0e0b50075000300d07981c1c1041e07101c03481400c804070001c01d803603844503803641c1d1901c15540025031080e2158020800d090094100f100c0e0220110002404400454140f103520b04003024000502c0c1e81c403091501d101a84064030710303103002c136400401e00300c8140111410380d642c0784040f49130805210f960009910000d039840400c00007005407809205070140001150741e07081d10141e03075044141d6174210a40d105c000d00f061900704106500130381c0803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 825628318 1250 825627068 825627097
    0x1811090d02030703320c131a0301020310140303070b06060307031d010e10091e0305091302040905010905090c09090c041a030c0a030f08090609090405030705010b04021e 74
    0x2596600c43c140c00c1030300c8150074003005170320080f12a42e100040400348800000d0901070f0515020000000d012015003840030311486407120122002c03007003040d581240240c2c0290003950380345014010100205a94018541102002140c020700c80c1800019562b010781d22414500c81c80d15400108a0142c10040c10380c001c06032128490304060702d1030103108420743d02c030b18000f0400c0d058110007036041400303003004035103501e2800703030880c001c0380d640d208684800030387e4201400e06001c2400c0895191250003e45038100000a051200b03030300c0180e00510481c0c0f88054200240d1b40c0b1840806d003540c8041e00c0615481c0d01c400030a03145458003115040c3c01c030710301e0700884102d034031060080b4050740e1008841d0f10f000c2d04060180c00c4107040c20700c40c08002d580201e80c072582c4a03003140d0710201f814800c1c61003d004854003103081143e540f1000100c07990000300600d01001e40c03500d460069039035070100c41c0c100e5183d402c0500039803003410a4002e69444580b00089001d01c10302c3d54510140360340055013600c5a40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 825629568 1250 825628318 825628333
    0x806060d15031208090f1209040e1608100b040b131d06090a0c0803090303120c070f060204060f21020d0f05070f02121c09050312010801061811090d0203 67
    0x3c80844100c02d58043c07540307404c501d0703181440d002420905641d2403030041303810000c0200540310400c401c6410000701100d000416010303101440349480c00c0d07c40c4140d203d0400700300106c3c180500150f0a05a0303042d100044c80b00c00380c2c2c2d00500050f01c07404a2466085024000c2541070104103070801c10170249a8014030381000c542580c0c4505d440c0c025640c40445420103c41241880faa0360480000f902800004524240d40368011a0350b0748a60225401d081443d00040f8103040450800c0782c0c13a5540011410702d00002606054000394400d10500021030170040010b40d9003400b803189510600c410445c10044002e00f01c68070006036110242c030241c1c081e40c80300c6461002c0360f00d100d2540648020707075070130744a11411000a8580510101c0d41280c0850620000740203171940401e0b501a42d1103880302140c0840c56240c0a8954000c01e85942000010b01001042d11101584554100d50304070b007080218450600162080790b84098991031885070400082d0300768200101700001d11403000c1d084034140e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 825630818 1250 825629568 825629573
    0x2040b03010222080f1b0127060201060609080c0d08090103090f210804051c11010e060709060314040f0201090b04030305030f06040203011d061f030213060806060d1503 74
    0x40f1211160280300f10302030312505001d0000200b24166141900714001d160000170b148134041c041444444550410100311201e10041d0005412041d008035148007000d007803a1a03400107400303030180c0d005110006084200010720090000f0701d080c00c510002d0540c80d1250002d0f103541d403140c0c0c0180b00300c906050300c1d10f0100b00091100c5030032407655405003281c40703d1031000300e90b41501701c0c56490550f41084904002d100218101003201c440d00003a01c941140c201d240f2603030030758000d00c454084107840d5103000c0c50030240803004240d082c4281034503910f40c0c41c03181e00d4080a504a5002c0c0c00c10041d100d0391f400006000031000760742228003500504044160503607502080289500942040300010350110601c40304480c0411019001401102e0039800d640c14085841c5001e41048402070344903c80001096041d100c25642186101c1060110b860b60020144040d000e580300744a07402d401076001c040011800c2c460b4003101d001c1c1d24001c000714500403202d848040904001c88070304000c10440c0500000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 825632068 1250 825630818 825630847
    0xc03120b09040b09120403030e10020c1309111809010c08090723040e0a0c060e180402040f020c0c03070905073c0909050f0723040f030c0e150d02040b030102 69
    0x714403a550b4030002060841c14822604801d4ad084401d540c4401034030255a520151103400d00d190001c070000e00c100d00d604040400310b0b5400240380e04825010048096108128016807184241c80007d200c0c4a6503554112482c440450f00030070700750400841408101115140c2c41c242c004801c1e522107611203000300160480e0ba4554400742c41d07500141c483d408103c1c02c071410750010f111a051580010303030404042880d808440d9800c249403000e0b1070000d030031951250312139900c16004030300c115201c0c1007ca00309503135514842802c034800d100344140001e14160900890b841a052030780c4200c0044480500e0001e0100c0c91000d40a02c2c0c0d03a00b8002e81e26114003113002e00620445950f5101800b80351410306401c94030042d100d500d0a04881301042040c3d900078808880000c004598900c25070600241074001c0e00030790304a090f24000004000080c0212011107000f036032a1800080b03c143c032060000c0c2c0052140c42001030f0003540450415003d460103a1201c1010f12003d00058034200c420500c911 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 825633318 1250 825632068 825632077
    0x6030d14091203040e010f0b0306130513061103071b2303071a0f0105040c08060f040209120307030e091303180b0a021605040b030a02040b0607020d030c03120b09040b0912 75
    0x804224150004000c807d503069000e10040000e2280d8615600f00000492500c0340342041d918882a103800102d546880c02600100b1101d800420821680c0198200c40c0c0e1203900940c1c0140000d44071040c201e218204c01240f250086a01c00f54503049a407031150b4005044000c081c5d401d400d80400d10170a00405d11698003103540c035010304c03601403080c54101030000c08054184c210f03601842c6080206602160403015041c0c0051007244e40c04018005140050042e10032480e0380350b00300c644000c2d2101800000009030964910076120100708a10031014041d40030401c95110b035054082c40e22201c0440e0003415118801a10740c0c0111452680b5a80c0509e866884000720000681c400d031000c442151404100c000a8601102e06010a207448000a9501c80ba070340c5000e4491035990503061300c169134100481d02920340c080c0c80c141683d1001c1c00c0291070f4458100c001c1d004904c2c5201030784a124450300c50148030b50070003071865101d501d0300d85441040401c0208a000c19103d00c900400240f2550b60240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 825634568 1250 825633318 825633329
    0x20708060c09100f0804151e05060406050f060f0903120703110708010e030414030102090a030b010911130b0a020a0501050c0a020f010b010f05070323090906030d1409120304 76
    0x50358446011061001d01c00c9085003000800c40c030000c100502ca9070041100e41c0054001400350520050305076000e00503e080881c0c04012023009030031506004403074012610030402106c00700289a5145c1c01e0080000d183c4440c00d60004041144591580340d110150038805c1c80a0100c860b100c01c3c01c8071000322236012440940100d924003e0003490752100b00070b2800038080d184028440800300b00348107540c90043d402910800f00544c0c0051005072002d5040d600d10390b0000303041c102125500d042002280300f00b8000c00d818941030920001001c000031045904035841300d410079100c5807900c0503a41890f0850b40b0a04218044c000f040000309a00740515406040ca0142d01580c0b003148005c0a4a0192240c0e000840303a414146185080c1c0c3c2c04c0200200010741c0c0342416a607031061441d04945c949000088000c0c041240301140b4901c00030400501854402035400707000c41c0c0c41d28410140e403040c44071440800926a00030f0320100d02911000b40111040140005040c98003180041e8203580054104 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 825635818 1250 825634568 825634591
    0x2190f0b07060b1815010e031e1908030c07020d0204060e0702100912080415050a02040f06020a0c1809020901031a130c0506030c0405030f1506060406080a050702070806 74
    0x15141440010f1250040c0f0520440e9020310751038407014618100e0030010080c0d00401d640340025400303a400f5640c3d4008182004040e500c000c01da50b440d0690310703092084001c1b56403203000d1158401d01900d04030900500e07042034001d425940e40581d00c035071315031241a080340c00c034003001076102c01038407980100d801414144400400c0c03440c194a0007460401c0c414154030a05080915003004261851038258088056240c030740c034640c2d6103044c101005118605a91b104900d4070042003440d0b0081c3c0c0c0940705440e40412003038001940c2c1c080880e42d031004100043c0005031058410040c0c5c0003515509007019008020100d650b05464000a2203040264015956110584555180720a28161071980a28081c1d00e14034505c000ea140c84004441600810740141c0001001c1a03c85c0075805c20303240101402000c86a04e080700381000768480e1103490041c061585007102041c0309240c0300c0b00f501c003600c1182e502d000c1565101407500e8064000500b48000350f002d1000c02084103c000d00c0010300c02c108502c0c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 825637068 1250 825635818 825635827
    0xc0501020a020d080a0605060711011704050705150c0d2111031e070518010314011212110a06020f190c0b07080c1207030b0310152102190f0b 62
    0x100a132009000401051050703240c903109202c0c940e544011b690784c3c681c00001e07089230590307280c005881c1420002c014a40301c041501c01c06c820000009002801c0d0b4909480c400c1400c1034040174201c0d40e00680a000f0001d0700803003e090001441002d280f2007480c03544141807000f1918040c40d030119404040c0c00f00a6481c008204862540202145c48406101850f941c1041c0343c03006000781a03000b000d50400441c0061811401240e100750041d01c48101071070044649035940f00c075608851000c100040701d901c07152040d011403550044801c03031942034680c4c0c060201c4051a039100030081d40035501c080210329081c003074807402c032010310255420001140c4400a010010341044481484018996400c0101c0c05040005c3c40c4040400d454001542c0404544c054540800c10360140113543c080d1038140c4110100320b082c0c0b4125810442d100707400700080a2405407103039001070340d0501d80c0c000390304080f54200b540001428114030b0342c0070074801103800480d129110140040794160a912610190b400802c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 825638318 1250 825637068 825637093
    0x12180103050c0c063c15012c06041d10082109031009030f1706030d0807051603050706051e0402130608250803031014010c0501020a02 59
    0x460180c1011400c40b42c10305044141000c60342d01c100c014070b0000b0b240e03030007902c481803c410300c4103024141400990b40d80b140c08003003440443c2e240301266100001c1b1001485401154095800c1521018000c4c02ca000c10650101001c1d00d509100e0a02503003007281000700194000301c84c00408103806840100700c07114103154013030000514840e00400c08075005810340840b403d0294080c10b070350041244059440342400000281010064214091124203000aa1040540c04051009080016120541044c0724041d0100f85041c0481b20150140c1c001e400d02c80245014070441075100c00d032450314074030380b000301501041440c45c0c0000403004650b000c2041d0342013145034051140d00c1003034524851103140d9010003000e040100500080d000d203090300841041e000098001001070f11300c0b00f04a40c02d0348400c20005e88100e0720200042d00b40302804101141c183c10201c1280e004c1c02406540740a400e0500f0b184038a4903a1102c6051305109106202070009582030010300070075845d0b50081d04e90381007800c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 825639568 1250 825638318 825638321
    0x1c05071716020d211107021002010c120e031b0a050a150c08090c12010204080d0e0312030c07110a15080717010f03111809060403020c091504050912180103 68
    0x3510030105118182c24000f0118403601203115a0412131000807820716480040c92a0714411400042d4100807854080c0304107640540102c1c0500c0c559541d42d0f0380f140c0c4110240400c903180d20701c1002240d00704203c1030344c4159968083c860850181c5054484e914026a00d40f0720f0101401000c03259414809440340303a01401348696210380001d4200020b0703e18150510b59180d1141d205882e11515030003a5204501ca42581951f001d00544000c5070185044144060040d26072aa48984a84202c080b42038a40425038252070142081c0d41555081001075075654408070303034440d480c94001c456031000044106c4030300304c59800304145450399841e90810445c01081503000902d603520040002004000a069070308898044a80004004030704500250000d0010440103503a003081207042e00c18802c1c409070100d080c9018502c65001c41b01109034010500c0801c00080318910345140351520510f81508103500f00301d900c81c41d09000d54800a00a0302c114149402c89015403004841c100f104070143d5815 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 825640818 1250 825639568 825639583
    0xf080d030509010c090b0703112514060708070614070c03170103050c01120b040515010f020105130f060906052d0903030c0f0c10090308010b1c0507171602 68
    0x5002070040072020003015041740d80510a203210201c3c00620441418800c0409c02500b56840013903800b210350107019090300d6045c224a980041b15083d6000490a80740c42000b04034010283c02300703082410a4450080681000d00c066032015200c041c200010700304094101d00c00c8070700340c507509003480715030a0062148556060b090703181560040140302007080020303c40d40100091030300300111a088604800a80041e03104907810034201824070018103814008403100751000e0762101800002c542c0224280c40c000c2d2604c082c4030181441740d00200748215121802d0a01420020480c4c1c0d015a4902044038401c4070000e0280d040101007a0314410f44110394980d5540301d0340c0701c260070308040d44815107034070002d003100d2900f00000905403d8500a4400d440180e103080c030983e07025074481c2030408050301e090201100091440400031a04450380002e5800c132405000141c41309100d00d40c044001044080c0c600014000a084408221004400003900c00c1c1008030b0451803140c600b00f0083d01d801c82 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 825642068 1250 825640818 825640831
    0x60f1c060e060d020907020a0609080d141006030207080903100b03010f0903200705090903040f0b0408031b12040305010e0f0a150c05091203120c0405100311040f080d0305 75
    0xc0c5100340702d035950b1003100054409404946009503500d03401402c2c0d161480581c4010841810100030a051010071b00181c01c80a2000c20148100050714000d04140d200032200c8481d4200040700038860700b4402d90151119611403607842d40313030002d1500003d1130700304c1d402100000ad0313403103048500706c0c1e08080c0500360025404590030b015503c00e030750703000d04900c20a0740070a074140450051407148200030001d110041501920281c0b450a2480b1a55100e07441030190804200c5d200e01e0000350621301804503401c80300d000740a14100208044e000030540d9a075a28a062072203244440c585038281c01004200851090000203540354034803103400e0803c00700625030001c0c1c0d003014038004c0203d4180406246a04c002840000750281c1d00e00701600c0038090010030300e0b044051b012481c0001d0100100409100c00391a02c10983c03a170b100101d40c003403441680511504a03800007aa0809130303020380c010b202e510100c0c1c0c0015040035200d003541401102d095000a0f0036911a1110401c03841c1c062084a070001c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 825643318 1250 825642068 825642089
    0x307080408240c0a080c0403080a050309010c261503030a030f05220f080c0a0f0b1326071704051003060807050d051005040605070905060705120306060f1c06 69
    0x2c3d001c43c000c0414021020a0030910101200080b04c5080341012035014640c04a112900c0b100441801021500202c6410f00c6640c6803500b5446102e004150b00344003d041c1c00090a400134021940c0c590000c0c02404424a040100c9000080d5680c103001130311100c1c40c541c0d400034000c5001c25510082d148081e00b114103640300c45000c8038404c43c00d41d030700a0785550030000390f042c1070b41c2c1031038080c0641c814440a9840c40c0a81c810040c10442c0304440848410300800451040e51104040d4101415940b0f6000b00b00b0100317401a15210b511002c05109400c0d14540c0302070400040f074a8416244008110715501d03890700040c103115034a0080d0151804c18840d2508009450601180c40d0342c407540360056500c074030003914403002004410819001803a564002c207110b00e0900b480c0480141c0001d5a4500220307030107020100d510305011055460203030f0031400600e811601c82c0d03101c45156002034041a04032508125403412000c10200600c0b40d0304038964400464400c0d41200c01c1161380c990071407040d41 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 825644568 1250 825643318 825643321
    0x9040903080a2d0c090e0705030f0702030a020d080a06050603181236040e01060501090503010218040905070302030307050304060306051c0312021b06160e0120030708040824 76
    0x1160082c69055a100c0c6801000607104c803400300c00c1d5505c800b2544440404201d503010400c075181d00c44091030148002038068150350301c032000140c0e200d00607984c2e8000140d00800100107250700ca0218542c005a81080000740191140c004c03072210b50044840c003001400014690b40f0030b04042003559261f80e04034201c1d60800200e0140c80030302e88a4802000302081078803641d414544070301e07001001e00800007001042680da2620200303010f041c13684620f90110304d05070800291414180200d40d0203d0700d8101d000380c0782089604100c02007140d524161514441c0300400300c011f8508100078001c0a000d18011901d8030318091008003541c0141e00424010015098100c10b294144503840c1100b580c9802d2a0290700f05a18090009025007105002e11070034122480c10701140c007040003405116018140d00401c4900c1c00b040e0b07162400031030602c0c0040e10500c04084012904041a0801420350707060307030725086a548686000e9000b9402c40c0c092034100c41201243c03030300b4801034040f0300d01c1c0c180b58000b0a03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825645818 1250 825644568 825644621
    0x50102070f0e04060f450f08160c0f0f0e04060b0f041805011113050616080304110306070315091d0303090102072003031e09040903080a 60
    0x10000340c0c030a0402d07491042020400b000400d80160307415194094040180c1003840c00ca09100950b000244e041500f400040c41c00c170103c10a25102c4038a50401e100782100e503070f9a44400c0c40413919041074401400c1030000c22075081c0020903840049003e1a03410102031f0520102c00e000071010380c0040c12181c40440104414000308420710390040d04441b00017009020b50000c19505608003540c181e000740b82c00458100002c000300808841030040d002000340c1c26a410020301359108496032002007d0342400108150324000009000207100b040b152030a6503c01e0382d620406800c1502d007200d0040c01c44800003c40d090401c503266024006140610410f9032011000b005103105000c0c500300103407a01a01140f1102059016050320306881c00c59559181405500c0d000b034000319811101100b4007070409a074201c007003c540c40d080c03a0090142d4500460054040c2e00700c03400c0b0b8562035440d031080c004051580d680e4031652007164000c0c0c8802000d032811084900c11900c6416036503103000e215011107400c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 825647068 1250 825645818 825645839
    0xf040c06030207110402090111060f0717040f24110414030a020f04050c090d050c03010b060406080112060e0607030b011b0c03080c01060e1518010b0d1515030e0705010207 75
    0x1e88000070358006a6407e81e101c0125040c3d080c0e08002c02e0306100d030105101200c5a03035041c244c880c101c503545075080d0144001c04100552815a005884c51317054180880102c2c409079800ea1008602402c141c2200300c03182e4003442074070740d66a965107140d440130504101c00300c101901c40b441c5a10440252030300390300a6000860405002d481c80c0c2c001d9560304006129060107404880c1e19440080180c030413041d6038545a0390768140694514002c2d42001d90340151410114203860540d451038441f0300c0582e0820300e2055020390b5002059821649941100701d03404028050701d40180700d84d44d0085000b030000c0c00007410034000d90000284404403944108041011418020305030ba9110b080c10350303107104100d44280503001c1500480991400002402258140d400c2c2032310f50072001740d9000c944402a61400d80c90803100740318004046030308004207030104145034030032001c1001d041c0040108980b82d00c440c1e44031100240024002c00d0781c81d0345240d21884208154401003a003403000340180d0f03040c445c2c0c0c2c06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 825648318 1250 825647068 825647093
    0x1061a2701051608040b0708090301060f050303030a0e0a151b08060a231c0c0603200703170c0703030f060605090105071104050c0415030c200a0b0f040c06030207 71
    0x182c54000d20000f980402400808a50081c644a1903098a5403164204240b0562200d02894804d6183c050000b4030140704041380c00455000034055810365945a03001c0001c5c10122481002d14000c0403044400622440203ca10540011400103642400900f040000940f003200c1750050042c008100a503940e102c240c244161500340b000700107101d00c104200500c054400b950140e000000c400043e00c4091000310f80e140141c020884d042e461981c8202c1603080310703a003181140040c103204e101d0800c100036400050003560301c00d25114412441010a103d08131006032139032461075000060003003d1540c0342c0580c0c0d1280403444010008545043c50280441c400d03003203258140003011403c0070078844218442c552081c0003030300c10300103480e1081038500030394868060b56074050a40d0383c190341120702c40d1144840c1c0f0300060b1601c80b0030380701d148481c000c0640031a100c0d2459100b12055400011500d0043d00e00514096012000743d05080c50440b00210300da404c00020144103019000100d0010840103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 825649568 1250 825648318 825648337
    0x605151003090206090a1205070b03090a02012a0c1406121f0f0603050a0e0a0b0f181911030d0e061809040b06011101140c030901061a270105 62
    0xe2038850343d2000c0b41d03060140b04101503001001d03110006e60a4500c00011013070900c01e500b61a1925210103241d095800203596125035030388070760085801540140e528090640304843c0481da454420301c603503602404c0560381159580322601c0100150001001c006c4000f11080320750b10b04117214400901162080100240f042200740e074142d0410280425841c005404140e15290700c05071038800240140800f5100115168a0a0301101c60510045201004240c1c4403880e0549030300c070301c60700860007180917007040b20020101c40f62419504041113184550075480d1048090740d481414440e206142360800361740241c02144241ca295903200302e4820000c1004ca130501e031180502c58512410014941c1160f070005510014002885098020b603032003000241c2c0d4200c40c45400404403804c0c1d44844c40050b080c1462703200803c4814901101855120401c0300001802a640d0030340740500101008021070004000240c84c10009084039205401c1c030b1400d04d95614200401000a080c1e1180d030960 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 825650818 1250 825649568 825649571
    0x80708092205041b030506040212120d05100509010b0406030504060b040203070302121503150919081306030c050d09060603050304060e03060609060906210d05070605151003 76
    0x2040190303600c1651032480c801d229445607849484460307064000700070030383c1c00382e558445103a940818051555004000e03281e0000140269486d254244029168145080d160030300400d41d00d80c0600800d4005456441d15194000c40d8500701820045040c5986e40c12a9000700c24075001840b9442402c021101205c3d2985000210f0b80c0c0c2d541880780082c21500c042c2540640000180a04580d141c1c0142c01c0c1c0811012903a903054032071040030f031810030100030441d4064001110070400d0f540c0219010354070403100ca0558800155180340a00100e2241c80204c8203418046511800301d85646089805804241810002c500c81d020010305540156607890b28520f884812280412135550010300045502c40203c1c2d0300c564a6050290442481e100c1481c003c1c8035030000100c2a2403c4100300b401010084c0040c1c02c1602d07014103000c14182a0001c514000748801d2107180640010800c030b036840d003115628561100240c3c80c103038040d035202500d81207010412158010565503039404c00c02c40ca9100d41070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 825652068 1250 825650818 825650827
    0x2030a030807110109030806010f030b0102070909030903050f01290a0b1c0c0915020c0f0d0f0f0303021305041406060a030f0f020918010b040b030c120411030c0a03080708 75
    0x8a034003036420f01c0d11101950070035145000b015044011640030b9a4240c079240681c3c034006c081141141d00b0120614016800350a08002d00441c44c1d22003c1364600a2615481d1651240c8405240001e100c219110b1a95200e410300c04000041000300340280340d50104a05180c1c00e18001891600700303001320300510000280e400044040c80750303508000c09421109100840151074091f01e0344034244100a454201e08a1b0820300c00c0c404503417207110a00c0101100d00aa01c0e03003003031098081e9a8001240e064140c0030345403011410f0113407020003032031103a035016a071003a40000c401c400040d0342e401b03c0d01580c00d080c1e4030009807030322400040c1d106801717035030254454103841022009044040c2039101c0b04c030315180d61802c4136100b03500144041d00040e0341c0d06d101d201d02d1403040524103800f48140d030390089042c0420302003400c4404c01950065945404503041003103418154040c40c206031000c4600321001d84851401d410103001412000c8411206101000d1958554601a10905000a140c00340000b03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 825653318 1250 825652068 825652081
    0x70503040501050d23041115040b0915220b0403020d060902010e15040515040506041802071e060c080c0702010305041b03030207030b06090c12060f06030c2502030a0308 74
    0x602824a09240a010009418026807405d007100707403d64080c2d0701c83d0260750880780d0354100384001500008a0080051506181403e07058141e0032480b00301d90310041c9501c022141c02c1e022009814098035661825149000d44141c0364401001644041c500d41000d10082015907a03444082c0859a003120000c0f450b41b100344012900c0c0c41300f0700ca440f540042c00b649940c60300b50110003d8420385109460f4200a2044407480d6480c034008c610070795901450401051000090446070a406565250f80260a19072951f5415040c0d0304503603811180010001c1008044c070601d03020300d940062150520b160141401c141c904c54a01c20135001a0516464034042420800910300030b1000c42d2889400341260741d12803034000e441c0c03440391105584402841020540d07a00e0a992254003400da00c411796031030715102481094070340c0401000107510041d9681c2c4841c55071558401140b1590041b0459a039070002c0000d010030641c11008444042c90002e0546030040e240003503204451030305424280c90580d00d00303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 825654568 1250 825653318 825653321
    0x6040213080102040f0305010b0301020414102a030f030531080307020f0721141e030c012d0b030f0d0306090507110a030318020604120512070503040501050d 69
    0x960000000b907100103000100148045160405c2e64441c100078410041202c01b00f500b81d01a034001c3c4516400006a040a6450044080304415040e4100481c250610520b4a541004a074045903108000441c41004150f03000c6010804015681010071030f504205c4141c07045203100720b0f810015021500103258202000001d5551502e501150341c0d030356403400080094450780110401009482803071004a8040e06200304041c28440760140c12b61541c03c01c0e1076111502d01a1900141d89000e0510740320686a900c0d01d00940395001c0030011035403000a84625400c5981c110807c4c0c0f60840d052030a0110f10300c8010a07443c01c0c40703500b83c02040c1c294040740001d0802034500000c080c5c500c6038950f150b80c03654242d0018402c48aa42d8420407069492110a407481c152005100800d6008030920380b0009010703910803240c0f0030007a50001e11348000c07a40414a15032050b04101051a0099443d808002d02040a20080011020824105111940e6056590040d400b0300f0f4103102c0301290142c9400c806 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 825655818 1250 825654568 825654607
    0xb1303020d0525260f0a030203190510030309090c020606040e070b131404050405060601200a05070f0801111206040f06090b3a020d020303030f010f0609050603060402 73
    0x18855061684205850903041c0d101c401c01c042c5904c0140f03100900f861100300c406603202d4400a1401914110080300110000d52000f486080140c00c0d112101c03c20040a00c14241b00d502510003100c101400c3d410058040d90090384811480c0d4205040c103606a0360210b40030b5003011060720040b981d410149001e50030b0540540064180407000f0400f54280108500300a040301d01004548401050140030300095a40450f4050f21540c801b40100340d09500c030b1443c0c12007070500100411500c241029007a41052044603003034949910031a0f00f8007441e282556140007c2c8080002040302252405e00e144181c01014600100c40e071210b8001500c80d210745d00410034000420f002002099181d20340d80c40106006000d81e400f41d0741c03840b034245040000c04005800004655080d056a040528031381c90031140451080703800032114401c44006840030006140210911000c003c03581d03042025928010240394001020007491075010880380c1c480c401103e0304004190380143e1303284407410920504556 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 825657068 1250 825655818 825655867
    0x210c0c060f092d15010303110c0f01050304110402191d03120307170109020703080f072a060207030e090f040201050d05060d020a150e090c04060c020d0606060207030b1303020d05 78
    0x780384132048a00c031403101980c1a2803080d00c1d00c44892a1790784045680380f41340400741d0303008464181d0301100c42d030049e8003851703005100c0c60900c800544408003040c160380000345924580d218006003a2112900038903800340d048a002e02c0340c1759a00c00080080e43c0d40f803c0c0200e54040c10f0300000464940d1b4071899040048980981c88d07a8615690b9040200c000d5225100c280c0000700b02401288100c0341c4410003a000782580d59031448402954241c0d0504c001c00e803401920713000103004c0f4040002d403090010b0403803031b4000c1d100c100032940d9020510888480081850303030302e00440c208200050303810005840060004c403c0000c0c013a84d809010840d081e11005000c0d41c0260400310025101074142041098012950340c2d145d0112103500900a100b00d007500c0c52079100343d00744018840188241422604e1078001170442c03004400a4645104030b6101303130003040050300105001d10500030140e943d03a4021242c01c0441d0401502ea450080d20f8640d1000c2e241e041103400940e41142d11140325000c0c02c4200c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 825658318 1250 825657068 825657073
    0x9041a0903040302042301090c12050411030f0a050a0807020423100f050f0d02010905060d0614010c02010c0b181608010509071a210c0c060f092d 64
    0x20000040ca540e0341092100700d01c50307410001744020b184450401ca0354040c5500030458140d9007402c2061001e4000303003a04604011001d088945403000c940101d03400340e40295501c68400c0c80010030b05003000a400e28040c002c0e400500c805002680001d00210341a0b00808525106c0341d04e80b0005000d040d4881c004044040c40140709403a506000c0c0080d40649030104005403010365948240e50070001500c40c0329405030710300841046609000c0740040c803a5105141001040d07844900040407134016006a0003065a0b5a0090000560b40244145c2200382400e14201e440034940c0001c0010100c800003c5c01148440f01250000c904804c1d40b08084021406540400800c0c442c0d03aa0400032511480c41150f00305004502c41500124280d03095455011101034019040103e0000079032021865094000030441c5070f0f40c814a642d0201d5000d10284d061503176490201404192422f5809029101800e0401d002e00c08a120002814228410340e01d50008542d0400201132004140115501d0b4160 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 825659568 1250 825658318 825658321
    0xe030d0c0f02060901060506070b190c0f0305060a0e0103150f02030c180d081b03040f06030e010506120d0c080c030c07080d05030103170702030a021e040e0f0303010509041a 76
    0x10707401407070307040061640d54200d40c0540d030b0f40c401071402c1e280a4402d0b10382254003001414042240c1c1551250701c100d108441c41d23410f500000103a012501c441605600041d40601c8911081d641170041c141c10000460f40d1002c12402c1801800300600184001000920021005501e120745074021541920302c8100c21502c1389040004000c46501111074045030761480703200041c55151540c90310182503000340d25207080030ba580e480c200300109010841101d0f84414031000502107100f0000c9000760502d90b030040303500325042c460a82524000b4060b1446807075039042060414000103650300148140d450061442041c1d42071268030362003401303080e25550100150055507418001485012265000219408441100e004035100c1c0000e001c010722084050440180740d0042d00090b000050000302030301c0091001d1360014590018080e51a4400d20044100d040d45103014403401c984180d610b0301400d928100b504145460b444140111031040d4141000f0030103109204041041804102440ea20325 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 825660818 1250 825659568 825659591
    0x230f07060e0703140106080102041a072d06050a0207242c0d0f2f0607110f0307020d0b0a15030303060e060a03030c02010c061b20031207030e030d 64
    0x40c1000504c2d400c0e2103609116000038846014070845080301c0d1a407640185001c00400030480c5940041c4050714211665100d005070301d9a294003400000d00b004078410840c0c84640352420a40d800180410b5041d03105004010101c6d8a0000d260301c000c2c844d5041c0900704015000c0e9000070322100903509246041c0d940f884191642c90642189801900f00480e03024104a032411100c01604807034810029041241c4400d5103c0c148903085400448480c2d10349034a034001d81030360b15201084940c0000901c0b91481d030030640000784000b4001d0200385010b1494034440341c011854052030310700001e02003d5000300250f00202682d00100c810740615000e089040c2c0ea90500034050942806440740c0508414086422443c110551004903545a01c6101c03441d1386640055030700c0714042d00156100c07900e601c0001d030000411102e000d403020103901c80b140da8a400750340808407104aa41c0d01003240e8020001b01d900c43c1e81c540c2e40350307030320801500e00410009843c110440c00c60041440800640742030034a00542d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 825662068 1250 825660818 825660833
    0xc030902063c0d11040f03171611010314060102150a020c150a050f04021e0f040e010606110a1112100f06230a06201c230f07060e0703 59
    0xe8800d2400701401349500c900752484c2280b10782e10a01c544600480c4d020000184410281502c0045107860181071202c4415840100038103410120340750488160150b10968140c440c031078540d0310101c1072a420b450250000f0f903030392242e0100740700a00094000a405102c1c070307804883d140940e00054860350146086500d0382d03800190f80142600d8184000510ba00134030464482c404da40007410556640c1411245655940c22603504a800183c91508800503848030300441e1407485408000245072454244001e00700001c0140c941c00d980c110f841380c1d00c08a0703241c4510104600044460300c1c01c1008019a951034141601c0e020200c0b00c1c1859024105c2d03107103640c0030343d08680e155101c0000441c3c0c03080030030303c00ba6458156654851040315083c82418400c200818112080c0c40c2e00c4580c904101c1d00c3c0c503207400c025000806080440302c1000e07004a40c0400040789000032031899412565484080d01004e00801004604011000c1450030601c28103170401101040340e42c1c140d4840d030f034490421a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 825663318 1250 825662068 825662077
    0xb04110403060e0f0d05040302090903070c14040e1231270e070e0c04030b0903071419020f0d06020d0905010b0a0506040b1b0d02010b040c030902063c 66
    0x800d00901c070340d0344c404c18408280740b840c0b12040e0b41c07054502405c3d0b40c20030280850241144c2e0481c80f00b032155100050b081c040340805017450422000b0040070f42010041034480c0c2006803034042e08030140a041070300519040c1d80582d01482e0010100c144002c41103110720440080c0710408000c0313860001142000e0300c40405c0e60f0680541c54080b00e4400c00d03107240035140d0140c20600981e11070f00b01041144c07a059001604000350201b01032a0564948071840b6a070303400d60b0b8402c05c41d000011980d0070094a0b440015254a004001d042d1030180d94500c102c11240c281800380c0689080c07840041d03190380f940401c0400d0795200b0310464a03054400c0c0184018004654101c84540c45c0195500715443c0820603030707046032401880c02e0301d410704100814059412102d000d01110407e00888500c40c1c1c030510130440d500016a00014070801c50400300004c0c0d840005109050510f40406000035071120307400c945065056034084854220700c8402403030b000c64021450420b6480072040007058140980050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 825664568 1250 825663318 825663341
    0x51504090903170717220318090608030c0607090b070311011424060c070501031a0a0608040b060d031704230c0a0f05101b08030106090314010605090a0b0411040306 72
    0x4007a1b40e9803444c80b11001c4402026000407440500c1040001c3c8901004803000d58007940c10b0310a00d5071090010240d85881d0440c03123141e0004038201e0740e00003003000143d0f40305501d8035040614a03d409100c0d60144079001c07001e801c000d1070300c917080c10040c400d4000300401010002810700d01e2030560003042840c51b04a49d401550400d0b240041980d14145d0141d0b170010b480750700608166458078005400900f941d0500048102d94a0820201944c896503002d0007800a6107800c030143c641440c0c80700c1144001016284076400349160710010075070201034001c50f20645240d000e040c3d2918101042421705288560303044a690508800440c0d502103500a0411030a94240d00d1240c1c50310307085803415810f40611a001140c10403000c08261042c0d60070004140410703004031a285880c0c4400346141d000b42c01000c00701d200e000c000c10422103a0700701c0c207107403078200c0000b00442400c05000461045020704500c900704d0b2100c4140d0155500c6602250030700c800540c110303940340c3c0c0d20700c1c0050103020500c014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 825665818 1250 825664568 825664607
    0x18010611060403081612020714060106050a0c120c0f03020d0e030a0506071419080402011b03141e0403050d03061d040201030911030105090f070515040909031707 71
    0xc50058510008071030340650390645900b070240d80d80641030307451115061025010440180c840c0a80300d42144003d059240c0281c12034000440343c40c0b5031500d40003040e03110604101003040b8450029a000c000d8108541c0e00c020103101c50321500000711803103040c2c42c4014107451088d622103800c01d034000a070700401880c00c3e00e40c2c0c100c2c440b240003010f49624501d403002e0030f907801c414009002c0d00c0c0b04a665104c030004c01283e040c105039400003041c10440c0201c072043c02081050341400709541e00082001102600804071011503a401c1e50001e000300300e4000c144e0459100414800000309400c0311800c00c003100341d480c440d2555640d0030242c1e91401a18100c1c07001c0b07440c106000c1045c0b2203111644440960915511805445550044000b080048815a58050300303080d103040343e690070701606001d01c0300d040040a400071008074190402c601a8442842110700e9851515550380400549003100d00c01d9900159606290606a0f0081c0d41000c0c0b8640c95800305017040b102c3da4000d1070404100001106 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 825667068 1250 825665818 825665837
    0x5040b06150702100507080d050718080309010309050304090c0203041a030103120507050c0d1104062301180924140609040e0a23120703090314030702180106 69
    0x244007001200c1c07a60759900140402c501c202604102d0320f120b03840b001c0c6103022450311182e07440380d0805402641c41d910340381d0707242d1061003a0980d1180c078040700c2001007240c181c0d0f20340c40d212459989200e00f00c8a18145602d60b90700c0000e108083c028bd800408407482c00744110341d458200207407a5031090280ca0240c070307000f620581d1072200c20000c1e24141e0340d0111140d00c1140e100441031f503032134125040440d068401d40c2c62024158581c01c44e4281c0c018031508606283c04003041c2003000380c9410750400c002c1031035555445054803081d80240c0c59081e000b07081c4005000d003905500c0001c980036800c402d58080c1080c401840c0c03140f040740f40140c65040d10511103403507921500b1030349006034a00d18031540008180a0300e456131500e0b5115032078526134201110401c076199a80d01600000115185c4039604891812450500c002d1180e1030040c83d0720b024152618900d40d8000d40000c04501001e450400f400406c1d00d81072004108541d01140c005018002d0801c0a151920018030240030b410001081904d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 825668318 1250 825667068 825667081
    0x20417011506120e030a120e01090b15030a12050405010f0f0c0b091618200304030f12050c0d0b011d27090a02040501080f0706200d0305040b 62
    0x10980710404075291000201d24508007040300c040f24894a42040385039504005900c0c242c003000140446040d540380d6080c22800341580404a4002c0d0340c0040a9904044212001901e6159020b03400702a00d5142c1d000100d290012078940207143e03400500d0b0452b0058020003030f6803c43d01074411150b09a0342c00781d110305420301c110b8103c000d0366882d01c00324041c1011480040c0455541d640e02071508011607030018102d1252241320b1040380d00007031480307204402d40d410f20045402100301440c03500d0b101e0340d81004141c0e0440d4080c40000c0000d020003092030790440441c0d114100c00924540c1403a800d002d81d08021402401c41d03880900a2098a072901910b0754a80d400340028880181d41c01c0f02e40038800c1401000e020b1942d00b5003103440117201c0415132000321191401d1250780a00b003003400503e101714040c8148001c40d00c040e000080c82c1d0b40244041c0094040004621094a0492608a04441210071840300501ca0b514202e5032900030180172898655066000310301c1680600c030200d00c1ca45030388 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 825669568 1250 825668318 825668321
    0x5090105060c15040f0501050a060e0108010b060f07110306040809182509080d0503011d04050d0f140708031614180a03020418060501141f090b0d02041701 68
    0x40d80350180a030041e15009030020b0381c844145031320a00590780703001500100d580e210300715641101d4001041c0c0c0e84003c24403a802c5010380450141010314020030003504020005074881c040c05141d150645000508401001560034610285500c09001c0340d0140c2403078603120249804c08003c190284041100317420113030400c00603450040300310b080302030007644a1180c1144a00c40858402e001d1008801307002801d00000c20030052404e110ba9141d80d2a03505142100f550004018110181a140b01e014040410b9021850b900e81c3c040b603003010b15500b0b20360601601d03040c14100100041d030b4070100e01c000072701444600a51040c08035415803074040000c00001c0d5612218104028043c040a201a91046224141c0b5400d929001401000c100e0354903400102618070300540014902c40380d00c1c41d142008064000c9170701505121440048241603100420249a89401120175903144102604a0325004040b054003500380c002006590780194489040650702922039421042c0c1c00309682065030384103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 825670818 1250 825669568 825669577
    0xd0e031216050a0c1101021213080c0a030201050301230409030c0302010c0908031b19030f2604291524040b0928050a0905250c06090c0509010506 64
    0x360301c440181c0c0c9a2511500f154182c01700f11541984a061411000845180042c21706404040b02c2c001d0020f04002d440c1e8101040c5440d094000c1c141e203681400103030b07080750503030703040d0380049058120a030041540010707521014061242c2040c9000300c044c0c1819840080c40c071903140250000d1042900e28001116456018490320109410600042031002450324003007080c10017000460b20740c0c40b61140c4180304601984004c9000c240100801c0da1041c0c0c2000300001e4500d601501e60b10111036844585514050080005044c00c000310b0345400350703a294104118462640c80e40d52642d603d04800181000c41c07003114103510807200e88501c40c80b104000c5507940c900e0464a0a528145458190200426000b92221030340c011a40300d0b24a80c0003103100b48641c0260705010000402518000504c00c003e032064000c5981203080004104901d1103c14007007000184402d6840406055503900f281d0303003201da80b40103000d10700741281001480b180448a10a43d40308071103503246a641d507410480180b04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 825672068 1250 825670818 825670837
    0x711090f0402120c0909030a03051f151e12151d07020c0909070e06010e06180604050a030c0305010605060a0206010608100e0106031b020c030a080d0e03121605 70
    0x80e100001e0042c1465078441c61803c0541080b00d406410100005184080807264103d980d071010030800b020030350501400707402c1034072880300644060400c0f24a41079084140038070001c84820f40c0c2a122114807407070084000d501c4503040f9069041c10380d20020401d0340f448400761405e6040c403183c02c070381d004104699422190b501c030f40d080340840e00303a91548046100800c400c2c250b01660104580c3c03510303061204c030311804004000e800b6050624260001411000e0601c0741000140a4683e02649a00040741c07c0c02c0c12030034214030005144400a101440f8541000c1e4101d141040b000082004c0c0a5640090b00d100710024003200b41c81e141401361601645400d440142c0c440740040200f02e0183d40660b80200266110300511519010101501036003a071110000030703990340c544111949500d150040f08410340c03010384001c07a0000d00103940e0780d824240c080e00c4000000740146405040d6403028030843c440c0e41c140c0f40c68807500c1304040ca5034407080b91a0b040e600132420050200c0c034841d5045410815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 825673318 1250 825672068 825672091
    0x20912060114043605070e100902070c05040219140f04050d1509080a030b010216151101060e1006080402060301063506010f050316030b060708040902071109 69
    0x260840c1c208030242803210340a00c1c1184d000c1400c00c0c501d0211440f05030b03141c404142c3c414690100c51400030704c2d19000e0390001d440200114107200d210302d58541c4a1045811034080503840d412103050030741030300c1004e80c0301c51350081c40042d24a20754012508040d04115854a510700200300c08030038800713180b188041040314201e04001c188a14500301c4a10350b4001d024481ca14082d80300070007482d00300d0745004010f0369030705004203441d0b80c01c80c1d00d0300600741110003c1c409020303c0c0b41d64408414600d9070b03502841d20500c070004021b0021030f20548004880b580070000a004065445589041030300d41900c510310203c0b102c03174010407814040c3d216a805581d0103800c01c0e1542e0f2030724000320741c07404104108809081c0c1c1c100c40d00c014640030213092030710f101c401d074541203541c01c0c0b640c00505021540072125040c00803d10400804800c0003840302c500600034140841d21441203400203e05210300340e8020404840402c02003084d0b185d607400b40c25030340d100f0103017180c2c0480c200040084480d41150450100c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 825674568 1250 825673318 825673349
    0x3003060f0607030210090c14011e0e030a081215060a0c0204050a181505060d0f06091b0f06200619110406050d1d0604080306130f0209120601 62
    0x207040090007012031074041d00c15188001c040002201c29200c01c0074060342c281044a009006c6c2c0c06000005c100c1d010400d0a1609010100b441c1095100f00302c2d480390003d1102003e03910844d524140002c002d400da10040840d6100c6014004245802c000c0d03d02c0d524211a201c21844141001c4003100c42908940d101c4228450282e8204400b802d801040c01c040c180d155421101c00d00b44000c1030505052080600140312205020700780f0803550020002c82c4108000510034001c144203041a09103035421440125060b043e0342800c9003038507015580702c03035403040c219030000c0d2501c1800d01040a90b030f142c0c4c6d61282e2110304840e04180c42040f41c5190002600080045040d80150450085010050300404a03481e942c2e000c110340030390802d03803081020510020b03402c40d02c950284510124601e01c16086510106680e2a02c1d941e02c8000748024006080000454070aa49044c2106071945a4040a0102d03545010605000e5009010000e010302005c9000211b1041e0214000e8141c880c407840d08441c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 825675818 1250 825674568 825674599
    0x313080729091507020f03030310120501060b0a0206010602010b030706052b020d020d0f020304050a14030d09140607091802090613081f05070903020d080903300306 72
    0x414034200c07040034200041280810ba038031043c28400c2800d940714582c03a1070740a64018410401a041c04691094100700100300d003007003899000e21b080c0c0310200c400500c05001450b2a50050080e604144d44a401c04150070303010b0350f800104281030b00d0613640244407003400300e0185603907010039001d098042041072000d00c02040d4011260b00030385c1c0c20481144001e1940b445814100c0c0c0c01102c0703642501360001445080a0410f0040340854010124110b156140c50b8030760316114030602000514207803e80d041a900100b00304103807a184074088408014014051404a40042c0303040005c4509014501c0000c0b0742ca4014580e0008407502e8010044168032503007a140c0080d8821010180c2c80407007489805806e04204c4031060107000c040c002400401100c01c10501c414000050503178003617050400b00680c4942c428084811a641580c0030407444080b464070902c0e034000d21081542604c038614040305240d0520f0300c5072020741242c1c403400d03890084d900e800349410720007240c41a400c491403880e0702a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 825677068 1250 825675818 825675869
    0x3072403020a1e03021b060c0912070306050a1b03090b150a2d0b040b09010804060e0303072109030905060d0e03040902070c050109143003130807 64
    0x18240c0c1d4038030b00782400f00300c810b4040241e510b400280c070000030303808148410350099952404106403403030300081c81c07103240502118180d403003140c030b00f140900341d0001105111030301000742c40040c40d4050390034400e40c1b40c8084854024005403c9440d100c90825501d10000c40c041d10032092640d0b08a480710141c3e07500c00700030614000a511456070808034180d40010301f41a00300e01050780707041558581d4004101c4141041d0058403d13005600e09a4082004108001d03002e01216450002824840020307500d50070541c0c01464144805201800000704020000d580000b440302c0801d01003008241d071029a02c072203012500e02c3c90004000ca02103000500c0b41d8038200c0013401440707000c4440030407080042440641550802d074400140f494002c40c81000700007124030600c0143c0000c3c608203070580d01e000b00701c10301002c070021401e0054482ea0f00080e16403100011b080d454864032010360450680c4244215503aa010640d5285002d1201b980801c24080201d0800704441c11040b1041020010141c500c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 825678318 1250 825677068 825677077
    0xc0a021501090e0132040c0b0a2d0c03080903040b0a121d10110f07050d120c0909090f021507020108090a2f18010e1f17010204230307240302 62
    0x94007421078210010320040c00c1002811b4240090303480128103d234841c0c0d440203601c0c40350ac4500c1490980c028002066600c40001d510494161404040c4c0792a20003046013107110316045580d40440024408900c15002440c024442e1000181000003c0414400c212103045130300d5903e0050700550b1215107042d1307044e08188168004504403600c0d24070651660701e0b9541c00080e084459800100407411250b0b0442600c00f9810f425400610180480c41c800400510380d83c06200724040e0344034410001d00203204400c404007070380606000341090a4807440c40e09504000c6c42240094803a80c00500000000b148070025580d00c244580b0b02005100d400cac5604c1d868412aa80c085480c03004903121031760b01e0002000100d0500011500654140401003840700350041018140c6244525440c40704200582004121004150902e6180001744141806446168041105510825140c2000110064030007003094011011200001d80e00ca501520707481c2c851701500c1c0d403044415550080300f4000c2c1c00030f2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 825679568 1250 825678318 825678323
    0xf06151207051824010507030c080d090b191416050f04180507081501120f0203180d020a120309060204030204020c0a0605070e090c0a021501090e013204 67
    0x855103151142c012a0407056605040014154003009025040c0007040d81080b010390383e292258031604107000064400e20820303a0003000c0060b400030071028060329800340d40101007498420b01c001141414030035036680b000d0352240640202c5d440c04241c4c11a0318030401c0404069044004400c2d554a048440c003d6040c5d03c030941407001c10000c1c0c14218200000a0000e071101d92005090400110106400c9900040440050200960600000945000c0c194244150034a03100d40010a08402d00c406441500d60004140e400402400311200c804044801100d42ca601104c50446419400301e95a41c0c080304007921007070b4801a075000461298108a0005004107000340c40d1540e80c1c1c0c0400d0890307120b031008590580000040c0410850303075005081d0810f0107450108404441007000414100000d05040795038500041d00e0b0300c2e801d00078000304c1003441c001812409a581c2d980341020280030704a09103e569442c009044100f851b808540d40c1601001481e00c182103244158070840c0d84002500a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 825680818 1250 825679568 825679573
    0x709081005090c0d0516050a0e061003020c0703230a030801060507030201060b04031b09020a0f05031510050a080a0218010f120f090b0901020306010215130209040f050f061512 77
    0x69031a91340340e03841c480c15068803480c000c222090000b500c9003180d100980000348a4207880b98200811900011a1600150308442000f8012003003071081c0c000384580c004c140c044d401809400024408080c841e001c680304682c224102c54200c2403510b80d100d04141a0090200b100b140061000b0f038864005003684030311a000000383e083d1279403100300c9541c00c50381c8100c684200414a2205420145030b81c00b0041c510300390254103008041d040544017011440c008800c0140110008048002400c0288ca06d80e4002e170103d9103254110100400b19807100c0340407400714030104049006334119100301c58008120f04d44402d0250b44600044803945000406c0348200960314800d1369203000f10748181118041c4501001440c00c00602e4034084401d8000d0440c5c903d64418000c00040345d80120f490f12000ca190007680030b0070f03940e4400d00700d40840710080280d08042c20408100130030003c1c007045801103004034212030300c503001d0701032071950348408449002e45840d0b8000881b0700d90404920f0040482c08103000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 825682068 1250 825680818 825680833
    0x10f141614030f070e040b03070b0927010618080c061b070b0a0212040e01030803060303160302033403050a03060909051b0904030503011a0417060708070908100509 72
    0x800c0901c40e00140d03200300703441c0031030800e014401d41c209031200312000d0161014450701c60710710000f03901c400040c410b440c26a100001d00e032202e651101000320b0840060740c8200703090451084440e030b100e4002d00806000c03844040b0140e401884400f642c00854144200030503d03640500c083c80b14a4009000090701044211034080b04584144004001351192417032040c1c4507003111780c1c001c1ca008202c16198050900401050141c0282458040d054030f4024005a5070b03501c41602003451440798100e41501354004c803022008040e80400104180c10f001d0014413280388020f0180c0d6013400c2c06411042c22404513402070000640120080d0a0140381030030005660755881c4c5201050746d03c0d901e0101c6807908000d145034540d00f89002d006443c004103a03540b5480307141565000e0014030040c09403c00c0d41c408483d42c01603141c44c1c0c00458001c1c02d0f45c8206081c2d00c002ca40e800c0c40e51070205840300d201140d43e41d000a040c1c90b02c030301842070468080308002d00c040f00e9030841f8a401007070702811140e40c43c0100c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 825683318 1250 825682068 825682097
    0x1703030a0b180906070e1008011203050f0304081804050606070b09010b190905070509030601140a030c061214060f0103090f1a04060b03031306030f060504051305010f1416 75
    0x81d141c0c4212030f8900644103030703e010900100792079454810a07200c0c8488180a03130004c1da11a1b00c030f0341541c2c034510025a880400d400c050340d00e4000e05450036260403000040004000c00080505403236110700124030030118547c070812054070422980c00f90401c0c42448800c02140100725601d4210020030300008a880b04540480ca60390301c08041246480440402008071003200e20541381d101d001c6103011410407008600003a00c80300e041c42185e85019031075601c800c007551152004d00045900018807001d4940d60390026088214200d4000c8000340381c1141d07048003c26060b4814481d19009200f034100d844200d00550081a4600d015118100c0340c00101c00014800302036190035104801c40847c8618243c44d02c030040c1c5441103581e0340a07800600122411151002401c000c0c2d4100d401d0101e80520721442e0400181140d0b84460f6215082009000b5481c0f07610300078414440c0144001d0050700c0c816614502a201c2c10541c0200402c05080011503181600e840b0b91b000e0000c61070103540145440c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 825684568 1250 825683318 825683359
    0x90f0c150f0c1e0212060c09032b0503040602040b180f0a0602122206020f060108070302090601080a0b040c09050a0e04021c03020f0d0210180507030b061219020102071703030a0b 78
    0xc440034124000002044030149c641001455021245034698030602541d00500074a51040d8400610600c80040041410084150180d0b070140020041c1c160b140c0f04080d0003625070a11003003100380138003075605144c01c1b07505041600c801525a590000e121034072101d0702001042e809040d003440074038042010a00342070080304402000346055030080000c0403181a0b418107203c0c4c10703404082c055101d44402c00041e1246914698005000d0078159003640e269190600601034500c510b1768020b2419a41d100700036007141c044020b071074044d10043c0250742c9603955054100300582d0080e5200040c59024200c061441244400e4a48139206689141c3c2804107401d18000c11429803c0c05078024035420b88800c12688590040119a294209916015901c3d0745803036200f00e010203071249030000c001030307503e85844809001e5541400102d800c50900305d0340101640083c101c0480c018007840c240003400c2036100103100c50320460b15000e1461510740502d140000c0001c4140150007201d50741140380c140082c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 825685818 1250 825684568 825684571
    0x16112a01020f10060611061e06040e2e020a020304031e050304090905150103120c110d06020d1a10080712020c0a0302060a1104030303090f0c150f0c1e021206 69
    0x100710012a01031305040001d814500c406c4035000345544240700b00b01c0381000d030320f06c896808400c01c908200103807502404200948a442c81e260081d01c2001e0f905400766200100e41801c05224820111060184204510036803007140c20b401c0041e070040c007050001c24009098000049408031035281c0f0b2307021a695642c1540c10030b41c4080282590b82c50407000f840000c0c007945105213154154445198195500d034104c24074040140410800070404100c2089034205003044441002490030000a5803441c0c40d0000c0d40c001c0441441040c100743c610003204a0200504c1e907462402401c1096202250f10115103140300213010104204059003c522040986c0c801044501480c0001e000d0280302800c001c4d207060300180c0a018080d00d401080c0c0f003120a560b0595082c0c981c940741c081514052070030001504a0085800307404078003820700001d49103800c200010303c2905a030302c4140c0c01e40c52070413040da510b1103d400d0103400002110300e510019030000b410248002e1008008800110304a86c882d40780190 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 825687068 1250 825685818 825685843
    0x7030201050c2e0c03060b07060f0e100c1d0114070c1e150e01051603030603020402030a021b03030115051c0c0206070306090b031005040f05030316112a01020f 70
    0x60201c5034880640705004415400c4c005003400d200c654646a03104d0118450b028000d40256500c4083c0c540d615810b0304a070381c04246c15000c550360321125624080083c0b0205a084002c42c0c0d503c1d41082d00c00324401c0030365582c035030142c40d0007441000541a6681d50340c4130f0507085825221404001c80c0085282c0d2058820171241002c5000d45410a500e120b210011441008184400303280031040d80d0381e000c0c04840640c81051401c40000c1c501e0310782a0040d00142d00000d50181c0040108000510a5405000e0702041c00c1c05801310395000f902c210380c903803100780120ba030156406403040780041d0080c001080000d0481404400d4a241c6117481011105001e084c0e4005030021400d00600302c0e814010310001e49003103101000301c4000e00300083c0e501d540300e41c00c081809071a100007a040c444482210044d05421406580d9a07182500b0a82480850795900a0109660040011903241c0016120703404a00d020800507207012041142c1112a00c0d1075000c60461042000d402c241050a000d460741c10003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 825688318 1250 825687068 825687133
    0x216030f02130e072102130b0415030302030d05040f0f03200102040803190306170a15140402040e03090a0b09030d260c0904061401031d07030201050c 66
    0x440380e00c100900c2001da081c0300410903007003030200b030650040850724a08440b03043d20030740c16840c807102040c0700080c800500650b01440e41e00d08003038030a045402c10951014200c904101c01c140f43d5074450810002d03404003a006920a11494071704100640c44a03800c90b0007081880a140619600c0104078000302c00f0403800100c01c040b0b14480f1840800c51801880d21a0000b90308260900c0e81942d0b8038045c4852a004040e0075055440005019611150280c00030848490103140d44400c00c03555004e5910048462401569a01007105000c0c402c00003043c12100b41084262076517002c0102800b90f44462500ca17010402400e6000d03600c5600c140010214815419120240c030301c20181003000c0c00395080240948414041c80c003480d860044a5404a8298500c4103622030700c7c03110155010790aa0700b9040b510f01b890101c0d80061034005120340c083d09030303414441e0880c0e1401045840040c04000d80d51940441814001507000b80042c08001b2035800450360802c5075034090ba0202200501c1001c40c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 825689568 1250 825688318 825688343
    0x20d02120124200d18090c12020a021c030902030f0c03120f211609030c1202010e0a0f0501020f0a0c09090809030a0b060a050306010506090d03021603 66
    0x8411044406006142048007650a02c5180381c03022100760030300b18402c040080072108104540340700e20030f5812003201607046950482140e0009040741d5031000d04060402080c180020728640b9602441340310a400d0350f00c400d02d1803162208513000c0d402c42c205510a50055880c80039550520521400c44020f80765008900300100b801403504044406011030740355004944212140d03140004c0c5400c6041210f04441d0b035581c62014070312a075000d401c0414030340c03110600200070000d491f00400b60107103440b401c10640c0342149007000d4032084650b12004210124a40301040b046000d8038202482c5401030400740341c025039090009541f60030b9a007242c03010002040c401c0c007180d40c0c10031511089400c0e581c0245441c17401c81c0c0311000b1900f02403040011040e122544d070410090340d1000d072025a03c01604903006500f09280420720900212405030146943d00d400040358600020124102ea1024214510707140300301c424031002e5186110182c040d0312940c04403488040c0042d0301e08000b0347c010300c009020b0303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 825690818 1250 825689568 825689587
    0x609040f0e1b12010b0915010c08070813050303070f12031404050a050d050a05270907020609060c0403030e04020d1107050a020405060405270708101506050c070612060504020d02 78
    0x3c0e070025100c10b8583c0c1e16020001c0c0380b54441c00400380c0c0001c1030302e00a115a141110040380c0ca0300794110010041c05000c19544100003070030028094501183d030700c40c030a482d140e40a1554034011740c14043e041c0b450381030740007000c00d04036000341d071081d071062802281e200c40e24480d24109640c240e4048506501841d070480c10302400b03110b000310300501850420f140401d0001c0080550069201d10440310364080000703104c608031904680b4074a4005008500146003401000c0d449000440d01d860441c00356030001200d0802d86422601502e515864021210101b103050100079048514080b840303e980e2010100000c131081d0140c41541e11030b900500d5845180d20521003039510103050785000e5800d01c1c0c14001c00c10314a040003040040307400301d12601030380c4d080b0740c042c0313041d04035807100b951400341d001444984400c0e0380201150300c07002401504c03110703620b0504481c1407049054880b12500701d02d03402e1048510900300c41260600d20b94020440b1521440010700720390045038102111680003d80040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 825692068 1250 825690818 825690829
    0x50a110a120b0901180b010e040e0c091026160b071104090b0a0b1306060207060207050d1214122701090803130302070801060608041a01050609040f0e1b 67
    0x1070a10b41658141c00c6940b4152948407644281800f004400b611030710442d0581c2d1003104001e142000c001c00601101c21900c0039252220302202125000c2d080c81c2000035090350540e10003104807410854a640f070020745200b03140a000b1207070b06c501000d000303101100003411100100c420240c0361015800e0340d220000e1518001254514150034003403420725040d0400310300342065071a841801e20130045128000d28001a200080780140d2507034543c039002011503003581c00100c44064074a6602200d0342c1035107900402c01d034078a11400003000e4021001055003100d206408400e459020440401e081800d20040503100000880c1c0c1d071031003003405a07400b94030b0102c6c0071a03113450705e00d000c00208211050764607000f000e844000c0c00e4014105441c94401c003098030800c02d100080c10118020404075486480041401900355002d8030261024a1813090b015540c50b085030484400800c1203141048107001c1c4000341480c0020744403002d5030341c1d8070000d0345003040c4114a00b0509020b850712092030309004215 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 825693318 1250 825692068 825692081
    0x130e09010606020703111c061d01090f110d141606180905070e030609011a060c07151e080603010c0e0d0624080a1208060108040204050a110a12 63
    0x806581c10150100328442d00030907200240da800601c100005842c010200d5400d52a944060340490b454106076407d1000030782c404807400903c3c24072600710002003800c1c00d09032210210040c1c051580c1003084400110310215005180c9006081443c20304800d4480c61142000d0b14220b0510f82c0100d40d62410803010703a0448005803810b41401306402d07417898000700b0b800c452401a0642c0555031804502800d014103980c1c01407410003400c4a0540c0384ca81c4140780a81100e140030205404800210300700c2e86031042c1a078550342404402001c8007480d0201c0e200a5140a01e9108103015154054070003029100d1030300c0000c0d06a64a0340844c1c1d0500d0420705007199444902102080840c0d645111740f50b42d074008007192260400b40c0401d00400002d03c2c0c0340300002001042e220f030240303003000054007103010481d9000c20340202d000380c05581c861801a60a031100701c0b0b40b41c1c00140f42000040c01494603034046074000c485c901000492140e4051805075071f1f80301180640224109a403244c2c460b07441c0e4081c40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 825694568 1250 825693318 825693331
    0x901051e0123010912050102130b1e090d06020706090201080106031e0203180102040303091a07020901051c050717120a08040f050a020d0f02120109080a180506130e 72
    0x405507140c8800e8440d03100c0c2c07040d242640d8288548030240a80e10403c4400042c000c489802290201c0503d040d500230b62000d16051180a810b40000644005100c1613400101d80d000801c0100c4088000e40b071034544c408000d15906c03580d00085040400c4441c4080c0005034031030000003c0e080c2030741c0005480003005902c41020181441821111030740500002c4540440716140540c4039100c0d520f8445191b44190b0400902c4d6102050000c2803642c01700c40141118105045209200014100000c20f44070f17100d4041c2d00301140c42d00400c0b02c0e00306004840d04411140c40008203a20090b581e01c0d0400c3e02c5540100d000485c004d04188810100b40300c2d4206034409030459500d0a0003400003d403024800800142c0808800580b80080c803105100035034002e90700401e9203e0b800240e00d00b074984400c0e0004213a014070030001c6800c04e4507005102d0710f030030940c06c1000a8101341c481c0004a50048515440c00f0300c5a8040c1c5000405840e104064054084040810b04201c6d0506200280c0d0342e0300107203138 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 825695818 1250 825694568 825694621
    0x81c0204140316062006042301020f0f0706091202030301050f0307240903060c0203030103110607110f031009050a0b1605040e2e03120201060506040b21090105 70
    0x10410808050348407800b11416401c110149280b20071420307403582c018485c058003030b008100400c8104400e0003039031a4001921414a03144401200c20a800c0340101011444c2d040c2080100d4807410784068058808070f440390402080019240c4d4a036545034042c0e4400d800035070300210040c40146407840780e0302d161010646c01482a82d281040f01a8504010364424510078510045182c4452003200d00710b020b10f400030800c0c04850b4a0400080d0f59601c00d03c01170b60410040180200185030040407210719075000405000041c81c0401000342000c0412001ca5240c810310100b075071451464082c00782c600f4043d40103000e0400b000c0c00d2450901c2002001c0070760540b00c284402000b0b541107002d480c00d41d1141011282c1c40d035601c1044110521440c90645220181003010b4a86402d88021034400d0324442c42c4820031000c8192426400c0e0341c160700900b0350048085c4400d109103a60391003d0414406001e0500d0103105071000d0701c0d400e86800752501d03509070351184104191080c00426140c20340326001c48 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 825697068 1250 825695818 825695833
    0x60302090106140414011404060c051c023c0303180312070f050426010c1803060e01060302060318070608070c1401150b0c070503010501060c0f081c02041403 69
    0x50303c04840c4100d0103010461817000c5901c1303000303034480c41030400342c8001041900d940d96144d590141805010180c1102c0d50b01c26542072070701c1c0344200054040c3c2105190001d14225241d00e07442104014007100450640ca0006254040401140d080c1c0346031410b000013459903400c020f00c40881c0c0c40c400d626032199a82c02084040038900401c22459440744c03251601da0010502e951044030580720301e6000001c50408661203c40c0c242071650004014030342c440c020000503402d20401c0c2c821010b01002c02c0700341d603610700342080492526000000460685400011901d40300c2e0300003682030b001610441401010070716401c00301442000402c01410440c1001c802c207180c088801412080011001014289200c5a08443c1107094108101003091010314082103500c0c0c5281c00780c69040319480c161035220310240020b940c1010f1103032a050356070550325604540155191410080944101225401c008002d0001044104070480d000740031044e201503501c030315052020201c90b600d030b00882c0c07180c3c00101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 825698318 1250 825697068 825697097
    0x120903070f0b0f0d0902030a0311010b1e010e0a08070e060a1202030c0f03010b150a030c030605240c162d0915050d0f02120307080d0f021c060302090106 67
    0x106860341d1225543c0015995150b00d01050302405402000a41502ca42c1d0b5001081507007281b2006450300b141c02c02000101c0c945001c00100340e114880c000c000c030104940c0d01c0015413080e24030001e11800645102c415070b544141c05890b0034800e5210000c115912001d0100d10b01d405840400244550741e4042c644128580000b912141020f02e014498024049480c2241e2805e400130003903110018403031903600140000319422980418003880002e854107500b501038070b00a00c2404207440c405013201004200012001071844484607031140b4030b4100f1300440402503410421a0740f41038969021039652445c02c100158440000025026070414100c0342c20402d1305041100c10840d010030b040801c034400122900032404029802c0036800a00401c2c140c410300c1407030084481c050b442968012070f4080000080344d1203005800c4010032307640381007190203406042900308589010710054018905400400068042200c507a01c000070030ba22080100113600d8046032481c0100081c0c10107503114294034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 825699568 1250 825698318 825698339
    0x120c030a030b01091701140603151302010201091b060306210f060b0d03051201080307030f11070509090a061409070303260f0412171611120903070f 65
    0x4202401016590000c14050381e00ca04031000040078150301070004441100c42c034034064a5601261030150b1f40c038001150480c10000f40b064505003c652058035951645146162251034540f0264119074075612507101003000b88e240d050700d503d0405981c92185251440c0a001d071401c0380c6c000341810701a60b18070b1140150582c00d0160142c1d00a4038860510401d1400800801c0c140000c4c83e044000e815100d4100f45e0030400401031400407901006060b0303a21101c0c180d0720b00c10344074000c0002c2c4c0544a03c06041d801103408034038803170080054909294640010852030300c421650902107600c49403214040c000c0d64404d4012140d03500e080d201040c5003000c14581e551850348030007400c0000110088441c0c0999404030349102c40c1d51103058074541016840c5420700901560199201c81e11402c0d03500c02607001e00700c0407040c01c15501c5503040587c2c0340c20000f08450900c140007400e00100045280310307008284060003009420401e041d4a84100c2d0052601d08010394000000a61506009024003402c5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 825700818 1250 825699568 825699577
    0xe0709030312061521050108011e06030206040605070809030114070e0d0b1b120406060806070302070c27051f060e03030421050f0601050103050c090f01050d0e150405120c03 76
    0x242c1c10620300c5005e01d80707940d481c040003982c40000503a00c0c08002003500c40c010b401400c0b400001c81410030301410398200c007400311a06440000c1d40031504000c1009040d01038000340c12004c0c02260b1040c1440440c2001c00d00b9a0001111555222180020424465080404028030100603203c4140c034400d07550f600c007000702c0d010784001e9951985540407135a414541045481069100345a0a02c905061901402400d00d60003001e1f014001c00000030b1100744280b094604071900001e100403403615005907a07202d890ba0301d03030030200e030041e204501a440c4010b014441c065100a0244010741c010441404042a460303000f6004000c0c2811904400e5500041501c00f9501250480e80c0c510714101b02110380010080380082c083e014140556661302e1000c90414100c0300c5c00c2e02c00b803000e6540c1b10300078441841512485544101a00000703101948038101a01ca0f00c00342c280000340405400c0b94507031a01a40a003201001e000490822041100c207001041c1000201039000d0b00f40003811000c191a1700a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 825702068 1250 825700818 825700859
    0x15180e0d08060a1706060a1d130c0b07110a050409150c030b10050d150302010c240e1e011811060f0d0c0f0e03070b0f040e070903031206 60
    0x1101c0003080300c07940c60900e803c004000f20540d903841d103401160102d45410084480511910309040b00080b07051104a110b1600b10010000c0d103184c7e50380c0790311140b03914076120040e144092912404210400c0c90300c01024060301030101500500510401c010780d40e032980d00814015400c0440307210011719030f02c040f1030252902c4040401c000c402ca5404400074070160b540e43d90b0219082c4c0300d03080c0c02d0307422100902c4080098030040c4000341c01026640b400c601203102c0240040c412100c010041400c2c0785003884020000a000d80818a41e031841d5016a0040709403c2000d40140c40313901d0300c401c9401001120814108001e006580e0030304110440700401c030f02d020b000304211040c0c405495440b5012510485c01059900f51100c041281101c020304060f001f00011607101c1900a04840c040e50112902c0140100200350690400b020100d03941c1200d521004070a40070700c80440d0034150034011502c9031096031b8505807401c0c80c5003030082c16000780440d607000300344c54200280800103404500c403070500c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 825703318 1250 825702068 825702077
    0x9010f06061b060902060f03180d1e0503040c090c0215060901060c020603090a02040f050405160f15051b0303040c060512070f050d060f05010f03020c0d0e1315180e0d 73
    0x11309001044061140d60182e02c04488004100a07034540c0b8409086c034240d65550444203980002c1800382c41d40d8241c030200810002040301c110b65428407a0006640c418441d20340d00081030369450b403030305c00c1d5451100d028015810500100c5030500c032442c005580440704944079039071545841806082c503101c0c014040e000f0b4200000040180d9020001e0b00f9030194050320400006924503c0007004010580d030445060043c88090030000027609000c034265440c41c51052591403800010281d4414070a40b403a0521809100044516140c03440240000e24220051a52031500749040c070200541d98110b0400c0c0241400b103243c0600b90084581d90100c1e080c1002401c03050058410b441d680103c04068150601340200400c0d44882e032044201100d200780c0310141c528031071020a50036401102000315050384100c4101c00c0c44c603c206030820701d0341c0307021b40842d448541c01100d85060b604808141284a0640c050030000403500c2e0000c43c601d6158528200900d0a00c90942911139071826403681c20007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 825704568 1250 825703318 825703331
    0xe030d0c090e1617010b120a05061e120304030b04110a030f0809131b020c040b0d020f01050c0303100608010b040506030703151e0e090610061b0b09010f06061b06 71
    0x501541c51340c0318505221801c008a9a500e42c01903030b255018504491a4807141e10201c1c00040c0e060007078500480d00140000b011440d149807001c801d44152a0080d03218144104455000380c1c00d00042014501800c0c0c0d951080c5814203003148103a1031001d003580250000201000443c0010041c4074820f0380c01154280e540789400700041e1301311040301c402c190062505030400c101c8603603100da19089c00c0c1c0f941c0a03901c025501c6001c0004039101c5025064101c0052140301d001480c190b0903071045902c0c141412400e0415015543c0d185d034004807150070001c8e10034101405201d400c42011401842c1400c501c500c3c250404020448a01014040c041410b4030707040340c40ca00d8a03c040c4000007600c1c00d081c0900400c21481480c4508400d01d215900c1d00c840490b0100301c00c3c10000c110726200d00110411220001d24203282103c07050b0780701410303204100f6010b403003200007440e20828501a0681d24008107105450090b41c504036400e6900c20403d1003000d1800e280440e0106200c95031145c0c118400207008e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 825705818 1250 825704568 825704611
    0x503070905040c0b0d0e06090c0a0b030c0c06040f0308010806070504030816050d0c02090f010b0301060c150f05091c020d05090a170307170f030103080703050903010e030d0c090e 78
    0x940040e04841104d030404920107049803001d6000943c03039440502150803036100e918410b516611020081034204060040520201c0042d00056400852a05103c1e18041c03d1200135030411074103940843e0030003038002162090680c45550f0034090040000a46400d00700190040c01901c10b030302c002800106c2c01320ba030b18a0307030704c3c001e40a241c100c0d00700080c1c0343e0201050a0042001c458080100d00c140c400a001c6105400442901810703140d0f814500d0349164240141501c2c00044484c1c100c030324201000c5005c0034407500d4010000240090b280204140c203114072442d041000d039454045d0000322007142c0c1d040c120340c0020b82c609505a0760411656804d046400f040c062600e9400c012000784494200107880b840002c010310042d8003482c5201c0d034079821101131a032a441840d24080d0820820300050002c2181309000b03148051182c10080d00d01920b580103e800d44d8160245450213800202c0c0c02201d44445001c0c1101002d81d9140041425080468003280104050038002142c0b142c83d1080e040c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 825707068 1250 825705818 825705833
    0xc170604180c080d0509060a11030d090606050907020102030411041505030105010e1501050a020d08130515010501030e1501170f12040311060444100b0307050307090504 74
    0x11030409019500800041c01c1c20030690b409a14810b034081031080104150380c051158094941160004021034a03140c1c58120440c0c0001483c42407150300d000402051140034160310400c18004c0c41038502045040c0381004000c0d1041d4010010030559004104000000b094042c9a0400b01d40c201d8000651000f40e26507a11250000d820031505986041d001060001c1184081841075090600c0d4103411020383c8011142c0303010301d26000c2c0160b0b2100300c91510740c5000d0200d0660004085001c00c894044580302e852030129846241030703c0c5803081c1c0040c840b65a02d805504d84400404005200d110200103103041032480501c141c8068055211a0341e03145001401480a40e10720181150a2140c541485901d2540b052108456080140d852500359041c9801550100c6003001c1001010b8462034001118404075115424507161480c00491008180c1590394034a40c0000c400500c209107401c8607a8003100c00910440d40700ba070010f0010003081e9000034001040e074100030380209864035203180418 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 825708318 1250 825707068 825707081
    0x509060904090303022512050a0f120b040912080604050c0a0e18010e1e0408030a0c0e09010b041a03102102030118030f090806060d03170106030e07090c170604 70
    0x1281000901c41c0d00e8154058600e021101038042c1001f58960525010b09071118410b502058022910b191301c02d9a45500401c00102008030324000403c0d680b01210018040307070b00315082116101080c02044c0500e5501201036a8000c0b0700707076010802d50402e061401c0c0580120107815007000381100c903080050301d0351312410180440f540f40e06055540c40740e0455010040495030a03680d481c03508a020800d20300302044901560f04200800c4c5140c41d92161140603090015003c41401004510000641c5814030428000d006100380e49031190b003000c41c4840c60f00e0300c0102841081e1418400c3c892010740b241c0300c2030f00310b440c7c0b1030b8140200214606c090100214405001c1d6240d40b80050180001510242ca8584140300e0354a49401c000c2500090311000b8803402450b45540c03010b00024110b0804194020226000342041c040c41000c1401c1d1a1062000341c0001c40000e40324020380c00001000c02c070143c050400541e0074406039032251401081c43c51070300c1c0e2407511240a0000b1840c4c6403204d50110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 825709568 1250 825708318 825708337
    0x6090406120201020f0a0f062d06050310060f2603070501090213051e190525050c150c0c01050405010b0307120314340b010501050906090409030302 65
    0x340402a641e07240401d003080a16020380c09801880c0540e500e444020404250540e4004050242152142c481200030890780301440084001d07500c0c0c0d011a4a04940c1d400700007201d07420701040007400c00b07041c58201040c11403000034403801c0071001d0240ea2064400d00c0c0c11703101c4804d00d000d0307546680380c0880d101400d03014103270003d0b00002481d032040c04410f400c9140c0990003035038540c42c81100391000c441110300072100d6401e5101042801b07410411011140740d04000d1655600d4945001048004d08458099900740705039003030203104800c006008840046800c00d1801e100d81003085102450f81c4441d507041c8890744021400000600f06210101903c0c038103200c440081180c1c0c5064a0700a00a000c110703046442445101400903d1100e41600451660380c1a5141501068000d1201105412141d94407800000c41603100322038a0407000c00c514010445603845401c1d81d61030400340500135040e004a41002000c000c0c1100c1c0351506811250460016100060344420744d0800300c00070302038400070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 825710818 1250 825709568 825709571
    0x209060708070c030203010b061903050a0b12061518131a01031b0b0a0c060e1905071a03010501080412110615030c090106080619120c0e10061b02060904 67
    0x2d540034010301ca101002528801d43c006c2002e51145000c221a070b0147c0c94540b0010845407500d002c18511036003107e608910700306004500d550701c2900145015069184040c1658044020801040610540001c0100342503540c00016580d5401c010403104005241c4c0d641029440c00013820401000041c1c00340d000d13040d00043c801d5840b4134000304011601400f0340c903081121040801c0c00c4140f4400c455485d00d180d128100c840603a90f90b000e014242030110903015000302021440320211180103807040911400203003010901b4010200080e21500007280c3c010a005c0c80180282e9070041d071034a80060f081500286409902c1c04202c0d0403141c0840d1342c3c5898082c0313000348034080320041d20b0040024011015503016403882c1042c415190000d105400000710080f0118002c0c1c00d0201443e07012400d154051615070b0b49079222800d000820b000112207055190780204000e401c3d1310032280d0000700e900840e242d16031800c41d0081c0300c1c20385a40c0e4084182010540c4208559940e801c0320380d0742c03002a10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 825712068 1250 825710818 825710827
    0x206030619030b0a020c0f070b090d030309020409051f0509070b0c01020c07140a05040504080706020309070b12060a0e0403021f0f0e0d090b07081210050402031f081f0209060708 78
    0x440c4c043d40118468a80c2031003030344d0074440100e0012445c0d5080d98141e520301130a2221400c20425242c42108003942855039a6807a080561214040c140da9a8098001021050709101c00c00700c03800290890001250315220600092100c0400c4420480b920101d1840e00c4081401704c040c024031480030900c00c2c134498480001250980307140640c6608804461070b101c81c980c2c2d8802d001c1500c10455004050540070800b01e40040e00c59409103400c02074400c00c0302c0c681da03110300000c0d4141c3e00c240c00c0c01000340c13040e00030400c0d0761909000c4c81d801b42000d14100324680c14203030780280d9260000b0340c1355107100201d0b04080c442d8032a00c0d0300c52003001420314414000035044a44890302c4000301c252040008488110100360a442c0c98115202c0951100c6040d00c0c1620f101c0d40500c200c5400741c2401c69841ea05100061265941d001440c002c811345607000038901e08544003601c25030103990150340560410540040f038046100c150040c14886908096910300032500007038401c0c03080080c006c00c104c00105 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 825713318 1250 825712068 825712081
    0x60903010e062d060d032003030a0b0414040f08090a1805090f120903011118032a06030603070f0b0d0b0103051015091a120109090206030619030b 64
    0x1504500070200e4070680038010794422040d2038040540d611000f40c0c0c10342071010486908044074111501c5009140c00c111040304d40000300ca0242c00084c4000040c0d201100b405411207040c07085d18101e40d8111000c00c06000c50442508003240024000b82ca06840004c03d0303001c0c4442d00040301c5c1c20701001040c40302d140b5220000140e861104960480325640341c2000200180f4000803052400d280210091508010140500c405680700c03241070f9130155210b0200c030409070003400140051800100c21601e1540489040c146845140c1a071141d8104d00100240d03901c547e0100101d42c1880b00b92415950b9030745200120f0b01d0302c00298081c44010000400009120700f12a0192904106c006800c0c8030600101e40110305032541a21001000000032100b0480700003610503030301858540d41082d00d40380b0fa840884008000c0d42a0850411483c005907180c4000c4920031014098110800300300b0a000361600803a00c20700000301094014201000018200c5440040c03c2000715403003510b0340054501170 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 825714568 1250 825713318 825713323
    0xf0a0308041e02300316020d050a0804090c030b0102060709170c09150108240402030711010c0f030b06031003060e07090e0d0e060c0616051e090f09100603020306060903010e 76
    0x85513450030511440c041c0200007240817040340d4076004000101841c040701c80d000c201a00a10700000c0b00c127441800a000c0000303204d10054001003041d00000180401c1d02d0001506560b040075000f4110740046082200e6690080c141ca81960041c0164141c09202e00c0d08007032134401e9181081d40e1000425040082080d4000c0c1d4a114111083e0b80d003400340d40b220f50640700ea00280320340903485048000c0a400c0181099800380d50320003041e18090900340f40042c29a400c50f4440d20050000440030402135001c540c00d4011146002e8040c4d94492841c45c0c1460490541107040c040204440d0f20f8a5080005c8541000400046c10803998204850102c2c0101281d986425110040c08655018040b000c64580b00c0242c407032501ca59809007100740e4a606985050301d4040b074411003402001d201080d150458240178403043c20980d180036644031108803c211300c0b540282006d6100c0c8112000304503003001c8101042c01168000d08025072203894080002e809402002c1c0044e4056207016030141800300300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 825715818 1250 825714568 825714619
    0x9010305010209180f0f0a14090a140708030301090c050f0f09030106060c080a121508060f06030109030c081e030a051b190e0a030c060801080f0a0308041e02 69
    0x13210001c0c1e0320032003100320154070402190030212100d07032440050324001c800010a41e001c40c902c0e000003200c03000d80b011401401c000340c4d040c40305035218420b1401004110b10718140344c06903c000803c4054070344401907030b503444140990201a9100c2d8000502c8900810684500d180c0c0207080c80d0300c1d0100b0500a070615040303165030700d100b5802d1410001c0c0444c0135464452000e900100c00ca03103000c030034400c1070b1020344035440304041e0140c1e0b40e01c011211703c000340340000c09042403d02401c15800c0410b40c0c440402000f03020940f29034500502000002e4210310341c0c1d4501d5038000461611404d646002c94204840d03100000003600e0300004001010b443c55109a1140343d10380382c02c41c0e42c0d0b112038030400e03018090054480c00400b9201c501403501c0d4000c2c000c0d00451000105215141034807999110300c1d004a03580844007080e18207005001c042024031400708a643e204006014140440c9c400600f80e88002e400a002811800c00c044d1039100540010344505401500340c20007a80000d000c800389801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 825717068 1250 825715818 825715837
    0xe01060e091b01080a18060e0d030e0f06041704051c0302100605060904090c03060905030a020609191401020c0f061006090308074706010f02060106110c090103050102 73
    0xe040d440b0000c20002c402e14484501c1c103075070344103155650640c0000140310180c100c10040110341441e40000d0036a010b4031180410715400340200701e40e6040043c05595001c00a4070058005504040d43c1d03410018035954816003150215140300c08895004c030240c420307a08a240c1144a0361002c80805240c0701c0c07180782040c840d500300d40708588102980b00450303100d406015440a000c00c412021468581c0149445901813034084198a9072076a5000858102e25811102d40d00041144c07d5010b4050142507404400075000c0e0005800200c2c0d40c5003090209080141a01310201440f50142425030540b8007203a004000c855071400c011064940d40c1c1c0085074514a056000c0d640450180d22035888102184c0d8043d2400e820700003581d48810101c2d002c100020305a070200604000c00030080da16981c02c81c003a0380b000220501c61000b404020080061a00c4d05105104111200d01c036400140300f81181d015241c03d010355407841c4001402c14010300c0c1000e902042c004008028000103500034080d41d507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 825718318 1250 825717068 825717073
    0x151a0a09080d0c02121005040b0402030c0a1809230f011506090905072705040612020d0308060102070b040b03060907261005040c0f030b06030105031f0e01060e09 71
    0x55894200e0756554403039031465000290740302c400600500300100f0390b03c04444400160b0711100d508000c034000300c40044030159202000d0206110a50074240b01d0786034004c03000c0e603466030420304000f0710380c04802820500301d544c0c0da5900f40b40350500c5070076615103021804445458501280c0800701c01c0c1e8030416140b0b85034981d444c0211403070081c050040e600d0120b44164651070895031034542d194008040081948090000c2803035855640c518141c61080c80303281c502c80e0311041d03c0c1040c05000480d40c0540083c80c280c110b2050407400359690f44405203c1c80d0f413510300b0306a241c3e6102d00407030071320740c00c1e60001c0c282d508041000b00d420308071500554450720094581c0c80050b031340c44000b1280502c800c18081040036003440180c20304008015a1a0302a07100b08491030b41d80c2d0317980007041c1100d0324205004001102050742420403a4103004030310070f04a048401500355410b09001940b601c0c644d2000d076815012104040540744165080219011142d1008202e03959403100d0041c5c074414119017111250 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 825719424 1106 825718318 825718337
    0x3060e01020903061e070c0308060d0c0b0a0c03080907030c030b1003020307030606080c010306030210030c18080a03081305030d050c0702041e15030f06151a0a 70
    0x680320b622a0403090318031030b0720311000d51700040d02c02c00420a1021010020a901081090f00040c003141c20402901ca140340036004080c503644400a50381e8049518440b26400903c405001402501c0e945d1050395074440e02e076140d00d21030200818102c0507071014800304848000c4c0310b80c00f954500700c1500c1e00781c890b0006894072900358011141941c072103105010071001400a507c8914082c00c05020003401c50740001c10f0007010040800805540781c5840d000703144180e03190303403208100c0b44510141d1501d802c01c0d951a11640709054001c5515580131070416980740442c4580e5079002006541041d4118100c0070240c1030280c540d10501606200d542c000d0799962003038241d400c482031005081c241d003c48084064801c072205103184204070180030070101d400d80c2c0701c01c00c5d503683c03041e8000744880c0300201c0041d1a03200c130f401250308482d18039825405000080c004205442e503a0700d491284 = true := by decide +kernel

theorem cover : BRFrame.Cov 825539568 825719424 := by
  have h0 := BRFrame.cov_init 825539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 825539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 825539568 ≤ n) (h2 : n < 825719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
