-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3891
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:08.486561+00:00
-- url     : https://prove2.me/submissions/668875f3-c93e-45af-817d-14448fec3ea3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 699640287 ≤ n < 699820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 699641537 1250 699640287 699640297
    0x618032d0215030613060506030a0c0903020402070b100801290f090702100e030f0f0715060f030311150a0e070f031b0605120601140702030a05010f0c02010605011b0602 74
    0x2c1c050088000401208100c561040b21070b9802100c059444108004090041ca0b0a95a00030b0095003940c0c2c80c4102c0200400300c1c18a083c0c10046201070010168850340b0080501c0b5003c0c0b450303410a4500720144100b44045a840400307968907091030942c5054143e081c4904c074094080a1142101494001804440d00c1f2a840c640c40304265040c08241500011403124003008800e0a0180075084000d040d10384c0079003c0b003049840390801c180070000c0c0364903004002e000e11032000300c03417800f040e14444812200300d50080464403030301ca1000d000b4944c0003013806020750a2600145001c50072200d0000d03610501030000ca00361501e5211900043c2e60a01c52103014060307544141c4e008075a2400c1c031409046502c080002c2580d408a0b0204080d0b1241c1e013110148441e02080d60855204d440c011101c1c0740015402200040d420b000481c01a68148035040905000d24008114140d04449240c2102c51911100c0156850240108071503600400c00e08000e030480901900c002c411410100e001e4414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 699642787 1250 699641537 699641539
    0x20708100f0e030c28021c05120a020304030302150105011205041419020f030303010807030308060a030f03020d0e0405011401110a06021b2e0b03010e01020a090618032d02 75
    0x2c00f08040f90682d40025205c000c1000240217a190069451448203e001e85004040e4209003420803640c0524100801c011145110750200c9200c84e4180703606840300d0300100c021400603080010108103266041100e1207018508043d010010b52405d40040d1a1a9081848928041c1c41c2c00015003400100070342c44030031001d84001d40b03064000100101014450020049100381c69140c000c07446810000140c905039582c0d10010a5814150340b0b0039076022200800d080d600044c091404000103203030801d442100c0d48a0340007007001c54421003014110780c01d1090194021450140100241c02403c404944910707400e00300955100d04119841e814201e000b034000d044c09000003032000c0041050203650051801c080d06071645a40c02640d00d00d503100c0f0f13504411a0049846141c039030300385407aa01040030f40704c00400020b0100c03803d4580d40c4c00d9800040070b40011640812042150b81d0b002001d400d035402d8844112a1001e0550b61000c0030070300d141440c1c2025101442d103182d280702810b00e24002c6aa0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 699644037 1250 699642787 699642793
    0x8010c0c1104110414090108010203040f150e030d0f14041101110a0f080307080901021204030e0f0411040f06030e0303222f060c0c090702070b0417010606020708100f0e 74
    0xc1c50703000d120171a0b9903d0700f00b1409040362000010700d41d1410300c00d8900482c1d000a07040782d03510640d201d10350004520145240c0903903403205200701919081004040c441107062010540d02d07440109081128180c102c6840307076090000400000032164506030342e44030404d00f03010010b258001c41031880d01c03180c00801416540d01030714030014081c5403400345105d070001b5541e000c40340c0d895412250a0340244800941d0b07048920000c10002409803103048101e4001400c0100d558005000050580d921282203d00347c0301c00290600c903160903440041c000d00010700b4140840c02840c10442d40e240310042030100f00750000a41403000c000310100406160ba0000c40b00b0405464890304400d800d1144610103d00c0440d813244a4540d080980a0b1403641d90307880c1c081d086443c0071030f00307001c01100000e10020460141005c0854038203200c8002d040a00222501118180b6041d04114215403036a0480c00655200581c2003001d40b07030003d00c143c100d01c3c50b06c0b4081400505134201d900902080940c000a83c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 699645287 1250 699644037 699644039
    0x5030f06070f11060903250c09020f120403030f060506131a0717030105190506030720010e0610270f06150e010e09010b0a03020c070305010c081008010c0c11041104 72
    0x400000603046030b80807d840c01241440c40c04003500042850740e4010590a80d8a1042040c42400d80c083c001c444007141110345054605942d4200c080c80450742200442d507503141c6a84101c041e0b22811011301400e440451070901c814684600104291060103883d508413036506016100950030b07110070740d50201440070290b801c1d0b280300c030300e9400c24000c07030780900b4840801c4010341216116400c221400604a1031440d05e81180c02c80e040f04449500d2024080c441a0310020003000740300710004840c40c00050704040c180440c0a982140043e4020724030100003447d40f007024620340d001001900401e5500250405145003a4009484a90b0150240e17410601d041c408541e0880756440c0d081400340da6032050b0f00c261504209681400f80200c4034058018404111914003a0b40145100c115030003c503143c50f40e0740d5032014252a261200c0340006802c010034411002740d2003001401402c03c90000340004460814002c00704503165001404103c00d0041e0f44bc6140c075554401e84a94000329801c0da0b8603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 699646537 1250 699645287 699645301
    0x4062003010603110a0512101e060e0603070f0f1407060c18030b01090207031b0c030b0c070506060d240e0c090108060105040506060f030109090b0105030f06070f1106 73
    0x303420910640700480c1c00c0c26081000440301800316032000b0070548030300d81400e0044110511522008028040440b08100049604100b10150001901030009a144050704041d802014945104280c500600d414414041403a403c42c0384c0081e40880785c03030420885030820004480441000b192400c0c0c1110001c0c0c054140803183c0c1290703500e02c030f441d00d800c004841c00205980c9411041c0c48007804840c0100018014044290010140180030b441d0941c000c00200400f2040342448010440b400c601d01c020030401c01c0b1031821051780c8101030181c03050420314240c0f81c03580c8031407000740014400c2d95511040010400617010707200a020468694528091400c00d082000b0114120811003900c1070104003200c9103000524607050b82e642c000034160700d0b4078100500c03000d0440500503542c00102800500304a001e0394000c0d5000341401c440104611825040469089a042c1c121300e00076003000d6120b4441c0c0000003101c80e00f240c501e00d0300e04943c1800d00d03011a41c41c460760f00080c086005460520041d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 699647787 1250 699646537 699646601
    0x120702060d18120f090b0304050a080d06081615090321050f0a030c1803051507020c0618090f13031206170c1002062502011512110405130b0406 63
    0x101301907074607040511a100c4410b41502e000c100d9004105130f00103000303507002603c800003800710212404800b18540e5110440613050181300402442d95000440d0100051894000024080305507402d04160345402d540700d83c0c044418210039028420340508004d80300030300c214110b4003c290200050b54450300c0c0e4080c02000703080076003150000508010250a0160500c0400f681100c1e03005009268181d0740a0000d03039580001455030041d406408403d072101d8403442d00800b02c4494800b03220307c91407030000420071843d801801c2845003800d6242009441040e0031060240c02c3c5c0c0505002c08410300240c5924041c107a9904680040d182ca00308007620564001a02e000ca10710440c2c0b0350569822145040740d07614002c890035488070b0b4020b180181c100f112980049003078009840089141c4010140d9070700703066082d5015040c42c41e03c00c0c0c080400d01000100d24200d068049800b4041c9061209021072260402600540a44802000f0800300311003684001a90036600e95954500914941c0340c00b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 699649037 1250 699647787 699647807
    0x6041206020903010c0e0a210b07110d0905060a0c0c0302061605010f140f100f15030c0e01090b090f090c030601170606032701051008120702060d1812 66
    0x202075804e10388100d43e40d5004410380e1806090242100d0500d501c2c0000d001101d010403080d00760705e007603041101004200040d09c1d80d442561280c13078044c0f140c0401417403c2d1511900400150030801000402d000c00d50b107060480300940e1040c07410903940c10050a00e49410380c0c203540025841440000c2c0a8102640c0d44402c121150064001300038411440d01d444064034540020a001020000d000402c0d400c61828065080706030b804410703500350b484000090104180350410800210001c0410000275070500441c41000c125103861807642610b10300282c030150281c00b41416080003c5104d0199860310070102c410100010502c200e1410b050180440c9039100303841160001d8542d2100f081516003d0701294010a070181030703546035a82d010748803611212416443c9006c10311207034010750081001d005081c00740c44d186107201d40241c0fa041c3c0280c1b41c0302e15a104568000c400b030210401603a200010344524000304c1c007012980d4860101170130140104240000d01c104042c0340b424541aa02c030000358 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 699650287 1250 699649037 699649039
    0x1c1e08010503280305070f060f0506131b05030c12011401090807080604080304151a03251e050d060b0906060705030d1d0d0c0611070203100209060412060209 69
    0x44281e1440c280f91500c0211001500454154540032000003900c01e1005000c014040d10500c1c0d498041a520032080c3d078a00d0400c850150307110360511141d0302d00100340c10007944440300100540d10b0251074480207009000c03049402d0010120005e4404800b20089600c0b20b540440309007420f684940f0b24040842200c041a40001c00700c2d0000f248503d40007072940c0a4410150003000c3c0c603644c0b507844000981c0018011604c8001110034040204000c4c040d00107420348060000401c0f03c40c510501d482c003441d11051002e043c0000d88105900b01310009604150344c040e007550703203c0984000d2003621651159000c940c002c81100055130620503c0d50100595203030072145101d1030780311181001054020428003030001d8104004014034014240c3c0203a004441c28000c1c50038151364280013a0811003640b85000106054010b2141045100d100f1041c040140c0050207050040640200381e4032a0301c131440c0342206a0004000d9040d954207000c3d280100910b4101c114102894a440030187d04002586 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 699651537 1250 699650287 699650293
    0x5031e0106050301150e0c0d0507021c0305060d1502040e090703060b100509010513170f010b120703031d0d0c08010b032802040207080a0c0516081c1e08010503 70
    0x81010320b018000c017985080301180074060b07a0308050022800c0d07800075000780c41c40c18040210941e00310040c011a441446270790040c080702c5038070340c2070f0015002c0b400c0c51003400c05240101b040300556032182045455a000a07002d1400030390913a480d07000748100c1c0c02040c01150b05000300450350000040d64800c2d02e20859060010164440034480e03641c003004443c030080780040c080311560b548504050322500003400b802444c2155107519014500c1949900d8180c01d40098001041800342401a0985450203888044001503074501c0075840f2a018040101004801c2886c0242040c691100a0544000808580300408545015222202103100d0b00c4495428900040d500e49000300c0c000740580c81215140080e034084005001c2c566425680c03ca030310076420711607030380407403815006416200700c00c0e1900c842d80340c000e0801c20314110540303a00c118032142d801018095003c010a0034500f1800d8007074210118900040c05841504801c407024001603400c0e4421b43c0702581c003034800c604903201501a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 699652787 1250 699651537 699651539
    0x1e1b010c050604231b060d0f050a0606090f0b0d05060102030c070608040b1e0a0e07090f020304171c051503031c0e031810020115080102070215070b130c05031e0106 72
    0x44039417900318000d880c012440b980078207032070340d42070881c000c00102c5280c40c40060120340c2c110324001181d801b0340f00244004c0d540c480c18410f9940040c0d180c0c025108001003610070900d041000c030610700c189130525001d1a158008940544d00800c2a00d1007003c803030040c2c80c445902c072940200044000ca5050300c2444030400815042441c01c0540c41c00040e2810020002d9a11003a0b00d4000d09412a1004428442c040000503c070800e4403450b04c0644061502503501d00b0b141c1869003e004507038420500c9101c007045040c0c01010407039510300c1d00c1c10300a000031805640304046645060304054220307416000001d15041c8a000c401c6590000d00303840303075003000703004e400102c825078078011040708461310140a5920a458500442c131042d03048094400032444018840130035034031120039404020b2583d00410b50f103045180c210300c40c00c01b0700040880035040503495101c80000300d6024062645c081004101703007040c011b03480b1444002c1c002c0036040710a001d00300c1d001c0650f0491450100d000c0c95107000e038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 699654037 1250 699652787 699652853
    0x2100c030b091b0c0d08010305010e15150316060509040501090e0a080310080102070f0507060810030b150909031305030c090412020102090d030905031e1b010c050604 73
    0x3180300051030002d03000070b8950b51030020300c904000c1d41c07a940700201c98007032040c0d0030100000c2100310542969a900d82255524524142d0300b526048400d001e083d0b0024103440b040803c011140075401042084088552080c20010a0402e81100705030801101e42c480701180d80380d0000b008003090304055030208040d0b170761a20084129000c142c915102a08401500800720340e10001550b00140241522060299642e84c0503089921152040308c1c80385614405109002c0c061101070000d00a42c10700c41c01034a40344002d00900d06080c0002044c0050f280d001c01d10f02020a02c0c90850108044c1034000079041051002e030b030301e401c44016a1448203040328045803d040c0801c0702850603c0103003543c034080c0c0380d0340d85102d255000c11030a50110740d8248a0040183d8410140607100e9020343caa41c0c520031300b05400d250801a5150b5000d407c00e151000183d101c40000a5004290134060756000c1d070321301c40d00012200c82e100900081d10368800d10061106110100040a42d4110260340c034000c80c4d41c041c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 699655287 1250 699654037 699654041
    0xc0b06030f03030a0f06091503031821050313030b0109111603050a0c08190305090a031e05040f1d130f020f120102180112150510091502100c03 63
    0x2807070101181c10078030119410710701680048030000050080030540a8072103006034122648503420380c56030610365500308241504000d00300700075004298801002070074800c0340c080e210104400c0000c0300c4864101c0200340441401610022848029458803140da00c0c00c0845010324203018101c003c51030000c291040580b054100e81d50407030342c420b61310340d030320078030b03141940d290700310761074107400d0068958510000429441c01494420540800780c9044450024000e00300c400041051040d0390050214a0100c1d0b04204801c0014003041010885134807406000c5580e4059903102c2000d84c5105800802c0302d58962880c42102c2c400c4200000302e60741c594921800780d401c1c801d40545903926410102000d410410308500b00f2010203000c1200d80400d900703035035089070f10101a0107041e0560700e00354445982e00c40080a41510700070320901034000c0600d4001311880c0c3e68800e16100300b00d00d150300b089160103888030200030004011501d40901c5803d10181d02d503102d042d1428031543c5800c01e0740310300e18064 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 699656537 1250 699655287 699655303
    0x402010311120c25151404030512090106090c021b0a05090f1012060e1501060906200a05030d06061d010c030c3c080a0f090801020a0c0b0603 62
    0x50292416121a10f04589550040035001300001280c0010001c0d0218480040301d1300e40b09404000134503409113103242c00c407013140c00f0030104c081201d42440701003503001e07040c2c8421090002d1240403c4e00d82e03035609401000160311a50b00319041c100486540b94000c20250300d0045502c4500100311001020400400c0d05409442e500c0354002d0082010030316054055a4880c190070164280144c03100c1c00c021840c44c00800c1100c015803100e030702101d17562043c010342c6141008880b1149031075050040140208102d07009038420440940c1203540e202410f20441003c03a0b031b00409550b80d002c40d50402c4e80c0c4a030b0200e0364004405047ca080003c64521821400d00340708001c07045c0354442c9502000456054540707490640c200031003640008003140914003204000c0f4034031a0155045200300030141484401e4902400e5286604501039021841980858900d0703041840e140c80d00c48802a006d540030221a00b08031050341c804182080003d420850141c0c0083c01080703214919580c48042603510925 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 699657787 1250 699656537 699656557
    0x127030b18071a09060d0204140f0102100b01171006090b16110310110406110a050a020d020a0b070b010509060f010f080a0e01050a0b121b0d0f050f01050402010311 72
    0x24070820004494415050340050001d203d0907403030200074400080e1580c1020010129413a0f000800300702d140301c1c82c1b200c0440000261740000c108060940041c8d1604094100000025107402034105142e1240b115080b1349541c003124003109082442490f04003407100c0c01204085400407002049030800841030740c645e01020b016180c00441c01d80d840c1406400e508152540511906d9a622821000c40c001c04410310601d04003030f81c6403403401800500a55a00c4d0b20011207400500501717000c030301c0202d0b0350b0074002d4040d0781d0b1894900040c1301144050344141c0c0040d1a8440100d84601005810f0389202d0488000715010840c44d12000308009101d0101c0240030f010070011080c910000e4002d2502544c006c00c2200c000414150301e440c001d00b9910112100900c19555000d00121480c00348003282e8001d001e2402084450140d400415603034400c8018913201d440d480442d0401c1104059a42c082da6900800703903100141c400e081c5a010f04025141240030a0424044205c006041e50640d501400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 699659037 1250 699657787 699657793
    0x16021206070801060912030c060f0f0e0c060901090b0a111009030f050f0d0f0605040c050c150118020c0c0a150908010e1209041d070608060f06180127030b18 69
    0x60540c0d0f09844022350303800f040380c1e0151100c80c44070690b060b902c5000030240069202054503078445078182c1c14040c9004c0d03d1480b0791030a110200302a40e12000c00002d9808101c40300c4c3d600c1038545015100c40c15043d1032200a84910140b00c030204545400c100450340c881d8680450203411150159182c0c0610300e42d45201801c20301221005500b240c104040b031221418000034401d8072280800e0036507030b200e80d4403000b0810019042e0341106d800c10003000c00a034030702009140755050080120380900821480d81850b43c0100d11240358001c1440049046040148110310700b03540e4031101e119102e01c0c00700310804110a00000144c00300180a0b0601129090003c1c02a01040c0000790f0700581040e400503030000d955081020f1000700c0c805a40c4100f038088401010742c589001070041c00c070390005140600603010150322030781507107681e03090b110005420f8010800b10701c44040121001d08017540d40064182e5083c2d698101c01e14114025400d8a01484214142ea40d58140c0854481030004030006158 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 699660287 1250 699659037 699659069
    0xa030c051c0509010509013b030a0f032a0c1521110f0301030c1a0a080105040f0216030815032b180609050f040903080c160212060708010609 62
    0x240c440d40041c00e0a80050525244480e408c0001c1010602c00e0071505400064a41070005101c04040d0020445101100201894441d43d580d03071210400c1940001d0900c001c121404000d05c141042080301c800707205903281446d07441800c01d00080d006601c92074140d07040e04218003503841d02c00c1403101c100e8000e520f004e1032000d45040070752005085881d047c411050051040301c16052007000258000c5000310311254029041900c1014000022208051900c000300120102c4e01d800201242c11610700700c41c0015400315032480e03140a8490020350402c0a821031001c1010140c000b0740c82c138001d000460382e04007481700f0781080c566114418415803c00580303000303e5000805000510160015031460401440c41c0c40d2210190406c000b6002200403c800c90700c00d116030304143c04515140032040381c007800382c8062a10094074448014040403c1c0c1000020790b03000b0410100b9801c0200b9601800c40c40050100f1540640c507002d003039805600007811900000b40d818890100241941c00c010503020001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 699661537 1250 699660287 699660289
    0xf18010804020f150403020409060e0f1906180f0302010f0b1804060b030c1c121409090c130608040c0e070207120516030f0605010b04080c0f120a030c051c0509 70
    0xf000a680504d40400e08101c044010f803038900442a00038443d00f80455002d203520a050b0034000440620460340c1c0c050400f5039502d4003420090358441e6000308000170580c0c0310458803800e035888078001524018070b001c812010180d0540c01598103040c0d1282c2080301010b040308010244101c0740f82045400d2101011501180c030b60792003c4030010004007124040003c850224011440c82181d40784800e05400c81002409175841c211240340080f850b010303c1c40d580d28480c281041c082c031480c07280240c2103003000480d01d5039403008540084a0307811540a00302c0d901c1e07a0007030411100f101c045640000000300000c540d03c90402d91801034041e0b03006841c96606166004407203200300c5605481e5032103503214001010070b1498107000030314010992404060440d041c2002a0398041c0c0c00b02c1540d01d0200700411800070040390a200c107c504a8044401c1e000c6500020f1741e082450380041614080d06441340704068000d044409480d207c0c1e400e481c90345d035800c21582c00b1400341c0c904c02800714200b001080a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 699662787 1250 699661537 699661549
    0xe0c0609030a140d021203070c030e010c0c30050a08070804030f0c0312020c031207060906020307020606031002030f0601080606070b010b090a080111070210090b0f18010804020f 78
    0x180000d41141e030300d200280c5030a4149800d40c80f441ca8036400c8001c020401aa0501100910700c695940d050b245041041c80100b01c0401614064108005e440440c8050713880f408200003195040f20707074841c01ca074440070340595508400c1c40f012518081c100800e0700d0351104038601b203c103540181c00740601c0c0006844422290780702640841c0c080c801000088000340001c02c440c2c00d014020b03120921700905501e41700114502c05040002950b00200e040401e0f96030002d1004c0315603400d80803498585101c1d00d01003003c0c00c200301008000a001108200c4201d0b07000030060b208a03012022145111145520a0200e00c0159002e4030b854404000017000d65015045e0a82c01150140806185c5484c50b100c03500312590030707045011102000990304050303140003410320b00074240c510000c0209110f0b10340a46aa4820004024014560142c110384000e006072402c2c4c000f884042c6815a580d20120714101c01503008001c0e503107a0304a04034081c0015441010035030700c9194040c210201c5c154080040043c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 699664037 1250 699662787 699662797
    0x103021e0613030c0e0c1303030e0102120c0a0b011509090207031b051506030c060d09020a032306010f1203030b1c0c0e0a2309070509090319030e0c06 66
    0x1811940030000b4251100c1000714800040d07015200c3c2c1040c860070900d000d1a11000980f40300c401400a004c0d0b80e031174040c1031040c5802c0301c1e418100f04c4498001c03040141e0505200800c46c5044002c0441c030135426500202d07441c0e030a144038109580c0240c1c0c80d022696900880b00210000180e080e15051004c02e149500501701c0320300a0030203010003a007142c0d0780e4035501e03100c4108840c580c010859544091041050b1550403210440c090400c00c06181d01007076a030300580e60500d498036118030b901010b40d15011020800b0b9034120f07402542d55030f040c2810442c00d582811021006110300000080d0040c403c1088000740c603c901c50f090000700c031300d46003280544070105005510000380408030081040c0c0840c508041e51184004440451401d507903000c0d0790000822242810782020284444d030103078454080703000600c0c06140c5500d615000d80e4107103460b5442e0081600400d111090050100d80040500000101e40308070b5483c4030020b5400b141503851058000240d94002241104a4608140509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 699665287 1250 699664037 699664039
    0x5040c0c031d1807020f0c030c01210e01020726090913060f050a06180203060306190608030430111513030f120c030e120c03100204080d02060103021e 66
    0x20f000c0c2c0031880c81000346480030790384180568080c0880c486c055000703001c3c4104a50381207001d00f01c3d00d0074420010b04040c41d01908400094050500849102c0c1254041202c0c50100e070021074464020380f9104c070412081030940c0100d0602d090038403126240e6241120004000540984000d0300c4060b205e100100c0c21101c111a40c946408403495031400d1446094850078110f1008a8141c0c604254a42e000007c003000200c2c0900400070003040d5200000c810303401080301085400041c42c200d11480090041d5000108603000004000134091015001000c2d80c0d13000c140c0c46506a035201d84a4002c41c0d95402005003640310640c41d2489070710705601d0b0f1420818030f03048111310b85400c4090020300b00c2d0f059001224040001d031102d20521505082410090301d0030705011a555800791405400042120031040c031076845500c060448079010310811140040c090b044030038400c5075640d604060f4001e4041c510380d611a060341028440c1c0700090150489801030030b0b00c1e5000074041820f4005d0800e0000907 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 699666537 1250 699665287 699665299
    0x302060a050d020714070f050901080303010501050306030a0b1911030f04021023031f12020f0411030f06030c0105040b0904051005060f040602070905090c090a11040b0405040c0c031d 80
    0x40c0c04100c45c8200089030202c80c501400da02400c044c154840f000c555000640504032040061014810000807a410344200342440d41d2603984150010b850724006100003043c0540c007200380b0550b4a880c80782d0b1f640c0d05006550501c4141400000000a07010403202c03a01c40381440004034001d41060203040301146582d00d1710360001c80c002000e5545c1900b10401e2030909100000c10044101800312420400780620400d80801c203140c5945180c4040306c03007501038421880d40200302401d07960356000c2244501d02ca00080d0300c034901100c520690080445109000340900101140607610500464081e0f40c054001d081c1000304200500c00107040042403d0140c40808102182ea551854040c2c034607410569078041da00c90616500a007440c2c5260f00558200e41401c062040607400807a20b14001c1c0800e131030490303c80d540c0a0544010f07020750415441450301c005008504005a90300500a541054509001d481d5003040c00b103072510307940c0d10050009400d569083c40008802c1c0f8185030300e44401400c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 699667787 1250 699666537 699666547
    0xe0c0d0204020c01090525121403120106030506031203190f200d0c02060c0702010302070c05090106030b1207030305160609080d020c06060a05060a1413090b090a060302060a050d02 79
    0x484c215100948141c03030940c04001d030081d4504590492001c01814a845c11407894034054a4040c030503584034004041c10450814910903020410541e07d036031550b0284074000303594a220240061a094a81c14081c0c0036080e011203102038140700b2240118101040b0b440e040d030b640010718001b0016a0720581600e03403902c00d058001c1140900c400940003c0ca40c03902da0382c041c2c00450a044078200700a070019500103408204d01c0000c0c010a0300c030070a03020300b80581d8400031071402815008803504065405920140080350056040e845490010000e40300d400713003507234580003681e07449480340701c01800540d040001d003d164403401c0184c09034922882002c14034552603030f180c08417034001b901d1540c41c0070390102d0704a4030ba400821402c0c2e0002804d4903204c050300c0c1000045849807040c40d0101e010704c025400c0c2c00146401650846e81d5103c2240300e211012529041901c01819500709418413480c506000b04001141900c2480122580100700741d00e8202c01e85000c0c0c4141c3c1041c2c2c513030707680740ba0b0030701c6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 699669037 1250 699667787 699667807
    0x1030b03070f050a120b01030305180405160f051c0e0703050109380606090109121b060206220812040f020109061103090f0303190f02070501030e0c0d020402 69
    0x5600103440000d8081d10031a00f80802d00045040c2c591086883d42000d04c0c044000c242c1022900b81581d40628065960340d2603040c9150042c1c6211013050740040c5414100042201a00d4104d0900c0900b5642d105c0c1f01c080981c0120350b18002c48154500d200805148a01c131062964072659004428100361144503580f510ba440c02c40d000c403142518864206070076055410802c03404850641505a80301401e028100f0b13159903885c00c002c01c1240284000100d60f21075a015829180c02808121502c60300c2152500d0308180301806020048010500c01c1c0c1c01240e180d0004c100c05106061109511b5014030414400310603041907040c046d100220100400e40000340c00b24482445603005000000c00090188001000d8100a500001c2007003800950601d080c0301c048100c0700d581104172005000c69039408006821031040b00014800e16184041c00c501c2e8075000000f404d0082119025201c0c0141d4600056055070307504c440d120711941000041d010fa510b07040c542c441e8900d00260005041c050700300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 699670287 1250 699669037 699669043
    0xe06010c080309010911100e0d0c09020a021c030501080a060c0311042705060d11030118030f030c09060c0b071101150f17060f1801062c070203160201030b03 69
    0x2554500360f40e511405e2400074800b440c04010004d01c002d03605040354103c0f4500080841c1c24400c0351501ca0258004664140065a00000c0141031800c07811591000c42d100041e540e200d20b100b2007082a80c1700e0391a07582080c02441000e0489541c58040c0805407899503801d001800e203800524141651800700305080314200740500040c05100200c000e101030b00c103002c0308442ca507034201300d41024207081c104031362a10b0781c1040101c3e01c0d03031200c49422025002e50000c0c3c09480100e0452900c50010104c01c0b080c598400c5401c8180300742d50300c082088190a80d01201c0b14611030003010b000c6445580f00100055504d91059441605440c003070b620314104004650035160007496440624450b40410b00121402e242d82c14000c08002600f88204840d0780c039807645942c002030400302c1c030b480c4c90b100061480c4c8110309403800100002008100598484401c00c49103100e0315140c00082c0c070000b640072070042d40d5a404c05c0c010299a0011810504a10941c03414005280000c070b0405480f052001e2680d1420 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 699671537 1250 699670287 699670291
    0x90c01080c120103080a1107180b06120f0117060601021f0b1005031902031303050c031b07170105041a070504090501080714011b030c210c0314090102070e06010c0803 73
    0x140c0e14072a5294041c1c1c900900c7d1052580414200750002c4d0030070090350010002c059810084802d010507100b0b1003400040c0303d030243c1010840851400d100700100d100366170030300c0341c181d482803003401010b00c011202c11a640c13101120418050703440350b0742d504e0112000c4030640c800d40454402c00f068034115003003c40c0b000100c0415607800300d60302009128203401b455800c14441c580c1c0590031802e62520100e00d2050b480540005010b1010018034150746040038012580d000c03c03205a426041500044a075543d10710920a10120421181c0354044e80003060140600071b580110b5007452262281c100c0c0f26030100040c0482007488010440061000ca40e809050700a090b910050a200ca151144418034841c0d10700299042003011030054140f105a2401007194640500d8003801003015460806900f1440168020444100d101e040304070b03552001d0440e1a05d40710341d94800c40500500009031480c014170b1143c80c00740c1c0050300184041c1030181c0309641c3c0208c0524005200210076150402d80da842 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 699672787 1250 699671537 699671543
    0x6140d09060207020d151a210106081204050a050109140f0102100e010912080705180607080c010516030209030d0c08070804060c21050423100c1505090c01080c120103 73
    0x1510340162241c841c140300c1c601d24201c1faa007541d445d4400b03074030000e00214526001c64091031a607422000e4100025481400500070b802d040b00d5041500008945054000d8440c20f44078085c4078101058a5128031000c5040300c840c0070002c00032802400410400d1440c0840c02411032103030460040000c030040c01010007043d114000014440518240252460060500c3c0c800344000e1000b4000403e034001c048461400140070b084103840700701c10000b403161040c03010150008c40c020803030703c03031040041d800f89000785a40a018030551200c1c02c000d0b01617004d059481545a0030a0700320305103003030044d0040400c09129605651420590303907182040d42e00140c00240005d070f29015104200001710b03a41c802c2c881200d02000c1007100f481f003001440361041307025915201404800c000c2c505840c6042491303202d14001d010052119403c0c000610b0000c00803020360326142d4500c01030100080350300c50a8001c1100b117001d885031808410066504d04800303020704446040c1080f0a030a0f100f2140f03a4207018504c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 699674037 1250 699672787 699672803
    0xf0402090d06110d060b09090c03070207030804030317070206060f0d0807060212010509070302070203060103021c0c0b0903120f0703050304020a0b04090c1709071e0e0112060606140d09060207020d 86
    0x140302c14a03101203c960350421b50300c0c540200003c1078585d07110740502c0d80c4003803144a403c3c1d40f641c507031104a04114140c0d100400c91500490701200701604042d200082895000e4000c6666030380c0001213a84020940f08281c21503810380c0c0b1007001782002103441e01154001d09440f4034201e902d0380d6a000300d900400740541820f2610005010900d040701126801104915080d0b08000e40c980000740c0360001884000c3c80385001d18490300fa10810004011801908000031b00b03241595142c1c014419400404c1040c840e00842511001c10502003090b0381100b9440b11030681041d40c20f690035070b0298401ba00680c2e118200840c005140000340d0002c1015003610000410070040c0481d0103000108110130111400000204100c0c02c5080080c80104a400c2e80d00c418a5400c00007205509a11042d0410700f45c061300032001246200043d009128440c0c4510b00411081d5039840c02106e17080b9810a40845058040041500340102904210703400f501441c0014901030b440d038001a92903c0b100d4081754215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 699675287 1250 699674037 699674047
    0x6250306050604180e280201170f01051c030512280e0705010507020f04110903010212010e0a02070c060e04020f0408160e0c0a030513020306090a061a0f0402090d0611 73
    0x130900840324480b03d104000c1660f5848a50030b148010300800446040d03480f0a004a015681b040c6000850754090300e01c0307880d450030f01003400c050311078003401030a00401a03400406006d810b501c5c80e01d002e07d42c25996a030300b480564124020001c1001c0c00d00503002c00094951441d0340d6481100382d807082a00540084c0852000607500d0500304694040c0b0705100c024005a030141e180c100d4803003500d4108480015408a00d0b040042c402d014500f442c0350150700c040703060b6920030015911181614225948800c0da40e95410800042e0704c00c2c600000d001108043c420004c039070045480900140700104050b08012241740b405280d81c0003988448002c3e8840a0401100d100c01c1499030003800c21240100f40520304020f1102d050f04c2859030380c40426650b9000102010840c0000303180300c0d9130040a0b243c6504040e0040c07070307845900d4001075074100d141608070310381f85244c0300f21060008409000da094010240d0108002504000303070858000050602c1c160000c3c3d418401e1010709000d900400f5152 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 699676537 1250 699675287 699675329
    0x50c091302161a1605070201050f07030314090f010e0606010e100e0414220302030a05090a05060f0403150501080c130e0f01060f14030703230a0302011d06250306050604 74
    0x12589441401c020700801b0812100984da2200071103c08030082180c2030b58448403890101c004202805003c1104030003041403158211001c1091908084940002d010034907000110a880c0c000a4803074030702003014500c082290307003400d1200014070703481403c0801d990007032980804c00391356031758003d44c0948661000300020004142010403104e0200e40c41004452050750b8060358a10481103504107000d03004c5400407490361910720700d0010b0840a440c20380c8a082c2e044048031035400900045034041c0c6004407001c0e908041c0d1191358100d0720680000c26141c5555418443c480e820401c02280450300c400d00c00c42c0c1c0120070441001c20041d03800000800c1c80c50b280c4146642415504000000b02d00d6205008507035800144140c00c1c1d9402c00c400d1810300030810040e0000e04251002c0c06114010304004a080c1070701944500755a00c1e040100c3e003048000700c050f1035140d41e4111998890480710347c500790000c0110f0b0110b210100c43d03d00380001c140b80c42c1c9002413104c0d0840d42c090f40011030852885112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 699677787 1250 699676537 699676561
    0x16030605090f060426131a160303021620090108010e03030a0b0303070c060309021e09130302010e01090b010801060b0a08010605071113090204050c091302161a 70
    0x44007020402605408410755142501da46000c0c10282408004052648a007030348604052502e140511000e6a1605c041c84030b030155103030501c52402203141035410300814804210480d200b941d803040700260001c200e964250000d40010040c0c0c450f0011003035401000070220b910454003c02014242c104518990702003140c880750580000405034142071081e80070f1707100042903076007110a50f031010038070303031585000700749180282c5202400716103030fa100c0040c200350583c3c41800824001e65a401000c031000a520f00c0c0920794900c116000b01d810700002c4d989404240c80303280c03c244284000319020342d460740c00341d00b07407035205d0019a20010100010001c4800034410038000f400700c02c6080d41801c3c0e00510150408005102d103900b40140001c011003000041c040c2c1480854000b400c12560709208a03040b001854030701c00403406a45804046035042000c0030a488401c0c0c0f00410054400c003d2010f10800f0750001207000e0a0b0340e0208403801d000071a1010080702c0c0300564041202140342c0408a410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 699679037 1250 699677787 699677791
    0x9010b040501060f02030729040309090501060c02101b0c0611190c0e101d0414060f0601120b033a08060108071b081306031a0405041416030605 63
    0x5000284d0300c2d180c0c20540100565140680181110400442d42e41005406c40441c12500f034000440d18108010183c01080c580207490040d101081903a0300c808040e5401800000040e601056102e581144640300d0192154401c035140c48103210782041d40d4071190011490780288001c02d01908001008000801400701f80100301601141540e02176100c51381c0511b043d025002e00001d1440000341100e0311005c2c000e00070320660200b00040f134000700c0d0302503140c0020b84d41107419441d2040110101ca03000902c15004400d40200456503071604c07001900d1450103030810359500341d10b0307440240640d41c09009404042101080328000c1110803400c5074040521a02844010500a45014442c50703100d21000d80c402401e00300420652104c410645103041301900102c1582c0041d8600f100300700d8410084c003650440340c0111820b41e41c440c0400d4094581d0b4041d5040d00200c664981b18a034038040c0c0086400a01840030354201c45006501b65081001c3d00c81030040d804004035080007003044030700c00c1503 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 699680287 1250 699679037 699679049
    0x40c210204030803150607050a0605060a0501031e150302032409120a4d070b0706110426061005061b120a020616020106032d060509010b040501 63
    0x14030302410760b510344101c0d0001428614401460501e00c40c05c0c1e4854070100c0d00c82d43d8110084032240710300c510385500a46012035025000e00d0310001c000415501038000d02c41d1030000c500f4401c51010300005000020709411041e10f450b040301020000c0541c23000d0015500c5c41c07900c6d192698241e410801c003103110700c2c4060003000483d4084200e4003210441001a90201c0b41c03d89449810842c2d0003040c0e14844c80b80092115040d03071107040460f0448261210312070100940904000f101d455440141c0e103a003640e2103030080d51807080000c240011400c0d8084502007032941d0205040c5070b240ca0300c1844030110740240d41c03c003454080f00c680014204225690784210081e074404807640c02d01021880d14043c00c94042c852007904a01d21006210620111414400910000b80c46d0b000600009584403020380307130b0304d80405040c050f03464424410b005d10019242c03c034401c160300380c28026100c1c0c84003614a06c1d00b0000000b4000c0000052602d0052071f01650001c40042030030001801007004070358041e8045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 699681537 1250 699680287 699680291
    0x8030912040e07050f2106090a0b01020706080402150f1e090d030e0a1518090b0102150411090a091b050109140307090f02040e090c030303180a02040c21 67
    0x8020b2a9252076442e507100003603142c01e0f6150001d00b0741c44800e501424508007606041221051302d0070350220a4603219580071a040d5511340c440284860845419001050050300002c1c03080c4441c80c040d4a609410a102030074080300303100c112141080b140c0041040b0703070141e0b00005000942e003c04560f40c810740c25a50303002c1440c060181000940e0940e581c0c03001801e202c86030064070310f25900e141c280c00c010803024640303880340229808002c0c1118188881a10340110104011614101501c82c003038411a041e002030814110440c0d1826110000078401c81e810070f0180100541c0d902d664905030700500d0300803070101d06030101d450184004805445520a54008800108850f81c1d103c0f40c80421141125001280000700801090400c0701c66000181400d00f0007400c0800d0301080c0c0d00410485241c111780c4036094071400000c9844515540e001c0758145d0060020030410030b414a95459500700c48400c40300b04407101c1c1d010400341d494644189000c030352003003c00d004040490b2003a4504103902c24003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 699682787 1250 699681537 699681539
    0x10e1309050705120f07150201090f06060611010506030d18080a150e0f07061112040b04050f010503161805030d0c0314070309030f02030a08030103080a02100209060d05041e0803091204 81
    0x645c0795070304960f20840032699010600705101a000798050103001d900050004600301040c142507002d00018810000000c0810280b42030081040c402d85024920040c05030000b10407014044810b42001d00c004103004c10403520000d2845810096851406e11a8001d0940c1070041200e2101322483c08803241d12a4100c007082c03000d024008500c6070300340c5d103850510903000c80e44017070000d01d0070249a0b0140c01c40d120004010802c040c1c1d502c058001c0b40c0d0201c54025040300103600440c1d09000c01c2c0c80c1d000d0900031140348008840c0c000c120304481800740c201900d241c0c5950b040005c0c40c2c42465100980840d8036074003050b0905500655a40058140082c42854461107640080c010851884040d1001494100820440d5414007280b100150000505600c9503101e0600d02140d43c4a6621403016105207010384035030448030300030781d0000580144140d00304000d40c1290b0015000090003103c0302d620103030180000d04801c5c09111851400340c0001c80e140e160030900c0601e0440245101d40140d032003400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 699684037 1250 699682787 699682813
    0x911100e1009031a0414010c030e0c040c17060f0913060606030c0f120608030a050406023c0709050c0403260307120b1c05100515010e130905070512 65
    0x310b02d50443d01015044c0c0320aa4a45c1814407440080300d100402c0c0e54200600d20f06003540c0354015146202e6010161084020300304100400c981c0540c0d0702802080300405240035120100180d10351151028051604112980c000a160468110341c42c45034441c0e0048414280b01c0d06100741c0c0064140783c01c04010503600340901500d0306071050001e00030411001c03e2108506d0868000f20010304420040700d8540c491018050500c3d0028028178006100d490200400b900340464071480d140301385101340c10050780c40194008031040307501d041070040c0304241002620600c0303071083e9440f6104229002e5122800c61130071001c402040f80800249240f21000b00c0e40c180801000c030b07a003029560034041d2000d40600fa04030094802c28140380c4d407010681111001d1f486c02c103840c0b100c2d440d104000350f0360244402c07178000341201c0d0705403000300c0c0101c1860760107601940182d5140044080080503203040e40013025414095580d00d4100300d0301c1e9080131104020a00b84080c10092201003100508036000c4058 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 699685287 1250 699684037 699684053
    0x30e0d0302072a09110d060b041d0f0105150910080a0c1d0603060a0e100f060f021f021b030c061806130f0623070309150911100e100903 60
    0x1c01003840a9550707507000340281d0945801c0b2005550301041c07d0207402c0c0c2e15031180403d0b4200f481007240c4c50344401d0340e84007100381c2031011030f01c1780042245180150f400c010601035074810300f600d00001681c003080b420180390354900341440406a20ba43c2c22503181350070310441098803501d900c201c0c284540f9084448000c2e6640340040180e100c292000c54517980c40400280b00b606450740b18485120f44c6500b03000722910212020000d840e1441c80b000030140d40d8101c01c69a0000c213150750b90040c0c20001c0c901c0d500e600c48044201c0b030701105540150070401440104442c0c8508138220201e10741c00080c40b06d0b243d20040c080594451a060408102d54803407440c081e449441c001e0468250800d8900d1610401003080d0880000c5600800c04200d0008402032000d0b4aa0780444828058020f200024034414440d000d05115160f000803d44982c100c010b03111030250091a80484a81e0080003a000d059217403498141980078095440c9140303150b11805000c070050f044103202040054417903062011032049 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 699686537 1250 699685287 699685289
    0x2101180621060908190f0c020906090403030f1a03010b01050f0d050907170d03061505180a03080a17010b041a0901110d02070e0c0a0206010b0307030e0d0302072a 71
    0x8001c4065108a80303451002841e900c0310080c18007401194401c540c0c07404a0f040741e1400b00303a8803092506034141c2c0090321a0000094025400b00440000940f10305040f02c2a0303400c140700e4100450101e1024800e8801e607240304000031901007071400550241d140900480d16510742c01c0c00d001e8a40180784031840c03194815841c48040381c07034550300800c112079410400c0d007006003600072a1011240c81c4503003641d280c0055502141c0003034104040440c01640100c014541c0c0100c0b600c559281102140144038481f00d002c502c130b43d100f50548030010104280200400b94004507070740e0b01c14441340340710a0461454040c0c000984202040c4000d008c0703c560041c60110031849072140540b201140340040b12442281c420060490003080f0940a0840c0c00140d0300003914450303a00c1c0d00c0159680c6019040d10b0142d1a2810700503030080004100c0700356000d0003940c1202c04c0d4034021030451902a203046c9000042c007a1807000170381c0010200d0500c499850202c44081179045201401060364422000d04845 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 699687787 1250 699686537 699686579
    0x11030708060d140601030c0504050f0606160c0b0309030a110c03100203280b04060603050606091210050f01050a0902121b0d050114040b0a03200621011806 68
    0x10094550081c08401c620603903501c8428804c5564560f128641040c402c4105e02c80c03140581e0901001c601c600d98003415507803280e01f0140070369043c4444443c41d50003540b1403007010394403810100c1d804500150a50011449890510300941c2d540c45040002847c1c40b10341c006500c80c6802c4000d07e055295030104800c80b8540d888000503880382ca400e8040700c002c0180c0c41200016840004080514040759000340001c0d000c00c40c0d007000003541e10138083d003da5004880d050341c445400c0124400a140044020031101121000c8a80a80c000500942240c1041e11a04401c100e8107004020302d1620036010800b0f0600e418055003084414890306190070340140800d0302a141c2c0d000c9807080c9040250540e42140c44000040c4a01d5940d4001e80004010703030340000b801a030400740d007140c281c2445100c0502300e03684400c85080400003e40e99201000306440850381c030240802006055040c4e04850160080c0043d02c0076081e545811000d003c0004141852007503542401000c1002e07600c01144a003203112 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 699689037 1250 699687787 699687799
    0x1501030210111c030f1404080f040803070318060c051c110a0b0a0518061305010b0a0303170105031f0209150307020a0b0a05042003010f06080a05011103070806 70
    0x141d160070654196032918012100b0303214000072880d608110991907a04111a5102089040f006400d007900350b948105003d400001c8480c0403500180c4000002e024250454030303041c0c01d040d1200402d0b811030340b02450650000300180d0a0340d0603d02402441e40c020440c60901302d0b230340b0500d640c0b840d84890494010240d140c842540001103240140704004480c0e000405903007948030369207040301c0744032800e07581008990715080000e11402c00f598030814000c0c40c0480105aaa503864001182d040c26802d0225134654840c025085162282503050000e1803094580c004c440c0051981301d0303140141640903605c81d41c0900401210800700d03484403113213540920300269950900394040303441064550705001e401e0741d000042010303003540420100c01c6180301d0401020307292105651001039807016100070302105180ca40c04c1e404000030303901c01010603101a0020403108231b101c0c40310003165001c2e808542d4540200a4200c2040428415181c644000004150a44c2030800c0000c2c00c1000081190380982 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 699690287 1250 699689037 699689059
    0x6060f0302130b030f0303090a0512091f0212030c0304060b01031a0103150308030103050708060c0a081302040b210c0402030405070509060a08160f081908132c0915010302 75
    0xd1818007036010301145d02c004582e624200300c143c01d507580d140051709450341d001e4010b455010304803000459418000003130031a41d5103090100130301480030341d410b10031040d40f040c414800100804170300554030400010305000d031246044e0901e80151598981e68604040c0780c02c80c0050900c1c44640c1042c2244420300e00003e681104290080380d0401e40e41000c4c1c00fa2074044000000c228000070f84c1030541b24008161480d607200d5461b001c116014101c24200441c80c0c101c001001403414501452000e800104080f8901a080d400b00d9500340d1078203c00310a0710340580074034004003020072000040290a032000c524524060b1145c2c0c1d29280580500d600c51210a008601b1303560f07800c1700b90300140c01c00106031814000c40c42d00c8043c01941603c244100944030800000300c1c0a0040341d1600700f0968141e030030303d101a039551104000ea00ca480440e003c240e445d0804200c05070580c450901d92035000e00ca040c0b101c404105035820801000b4103007407840d4001504005100c080483d800e044a505554010f102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 699691537 1250 699690287 699690289
    0x318090f1603063201051303080306040b1008010905150303090f0409350f03061504090c0509130b01020d050d0f0527120a050708041e0306060f0302130b 67
    0x3800003a0300c690010340301c0c4000d00c034081c045058513014643c0e21a4038840460038442c010344890090065103042492003e404001040c01c4c140291b80c0030000420010700012144e00180f600420f900034940007441000060221000520903990400000c8102a0b064125000080d0384c1f84610b821540c00b60050000620702030701c56401c54144a80d100301031110b01c1d0200c543e50504075645001240d00d4030082c440e0200c164002d1011149030300c4400d020103186035103400a101505c90804014680024100030008a0f01036501c102c403890708140da10325a0380e280c104100324145000300aa80782c3d49191428010403aa000035880c0e01989042c2805503e03250b01140c03140040205d090910b140f9801c102c204808030b19800b50030807a200c041012013085611030041c1d1a52444100400a40c28100f00900701c0721a000320084c06100c1d115808040c40c00752110625000c4844c9501d41380c0242074807140c01d01c20042e09000b200042c0115030b07140c0d6152855074000405d03048844c0009200c03d40d0342c000100f09 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 699692787 1250 699691537 699691541
    0xc040612020f0f0d052409190f0c08151c081312030807020115050f13060b07050f010b0904030e0616030f021e06010e190507020318090f1603 62
    0x2c50480b03a000e40740c039100044141074051340b04803141c908580c40c00c0c0010380c00c038540d034400000802e012060903040e2411281801243c1c0405003034102c454202541c060300e889440d01030306108413030300d40002c17400002404020b0203903540138200340ba000031001740e00c0d681600c403d04c06900e0b0311b46494440710314401e00e050910b11441025a80d1551010840e80032510081401208403514801d6803004056510400128200c60764416080f003a010b200600b0003c5140140071880034050041c48814604e50241c409001c6480075440130b03110030000705500007448001e0000101400058000303201400801c2c00007a618000200b00034140701d0146001600c0351102015181d508242d4006d06034400e071a0305019068400744030890005104085c07114001c000d0301100055480c44100c01003a050f42170448000d5100401442c2c0c0c0386400d0644000c11a03060703540100750143d00c4c030303070040d56a9130011004112107001c49041d45005041e00e0091000610a42c0302003503002040040c1801c803103010031002c0300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 699694037 1250 699692787 699692797
    0x3040b030403081306020c0304030c0605180f2803030905010203071104150504090303050f0a0b03060f0915010311041505100309140a06051510020307140c210d0302030c04061202 78
    0x7002c1480410101e81449000000708196070042c5c21521026549001c102e50714422203a0f907d0307001e88900d58020903070030802000552804020820188801140034485c80303480250c3c401c0704010344840f020020b0640055031400904004e00c0918a800d80540364004800078901d00366001c1c5641300004055031048032503400c06850014010311200400303040040c0035060681d1030350001c040040104010189038030a000c5040d070b0140242115a0b1558807400344840000c007010081d004894013003a080b88144041800380d0700c103211803003511810340f0500040761000307228006040e00e041800c1c4541d96841c000c06445050510303000c24180c205140030825050b02c0500180e1070302c2109180010090720307401c41485407124640b42c0009181c2601042100040840c2c0301015030400c10000010482240b05448864102411260009000d101103106204100c03d072000c103d00c100700d4941e00c00000e020505001c10140750a40c00c5041880d00a81c0a1246101d134500f130041c00c01d8031a44800490701911 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 699695287 1250 699694037 699694043
    0x3090b07180f080f1c0c030e0402041508090d03050106080c0901020a0c0b04051219080d0b030601060305092a130e0601030302160e010b030109110c010e0c1203040b0304030813 77
    0x1c41080d95901c000f81d60341c048070301c146400e405034203818999900300040e105e00c00c0701c05559903140e0301c00c283c505441c424102c1213043d0b003146e000c20010580c41c05e028181401c4000d280c0d82d96400303190200b80141020517045c070b0003040500780001048060742c403280b82604078035040c1013559181040c1d00183d140041c03201004000c1c1021807000140c2a1040b03005d4021184299186908107169607015030302c0c0c00030390304034090a04440c10510045010b40001d02821100c0385400100040c103100000e240420036480600020340b140d00f040100c10007840741e0000800f1125007081c0001140d014465030b0780040c014280030307803045030380402c1e070f90281c0c0c11802480b0b0f0140141ea90b9540c503810020344422025101e250f548000c0b440c00101d04e00540407490489000c241228203690a102000c00500b031600c0740c1d4040d2040901031105181001e00c00c071425181c4c194014291010aa4148180e00c61520760740c081039041440100424030840045a5200390705103081409a612151804502c0003541800f0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 699696537 1250 699695287 699695309
    0x210050d090f11030c0628172406090d08030c0d181b0e041b0b130509010807030f020d0218100303030f0203040206390105061003090b0718 61
    0x2d002406400c0e6504082030f9015001d0b51800032030b00091203181d10401c0c50992019041d03031541840b550f007092145000182c2d40c544001ca5603152240b60f6402c41082d40d100780e8568119254000115003403218802c001e000b0741d80702c0d050803243d038001000e03a189808003a058080020000350003807281001c0f14801e00c58040700b0005442001c45003010940301085c120b600c40054018020780e40342c80c81201088a410442203819542d95617580d07610364620350403c8018250b07000307020862080701805001410524103102031f4680c6004104641903e06030301c041c0b12078100b0a401c1c004103549903104000740d03030144c8402d06a10414400b2400c0c4104c4041e1040700c41044d41d00f800009413241400305c08a07070003994184002d5001c0c0020703508070710041e10025800f036810444031106040c0300340441e400d000036000020714004000c0c0040020140c40e80101c1d0310380d40d50410080903280a86001c1c0c1155524501000045103a075180300340c1800c040c1008090003000406904184803240c51500034144110701 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 699697787 1250 699696537 699696563
    0x90305161401050601020609120a0c0804090c030b0a140607050c090f0708160c1b18090b010803040b0405060c1f0e010e16060e0d020a080a1e0210050d09 67
    0x200310715240703842181031601c2d4204004914071790700c001465406441031201410000781e1a84000c50310303900942c1c0c41414004004150000314290780e01400041851400125200c040304000608841030f038441c141c8155902e1748184a50101440c0056400c842504d9881e512156030500b00d00e07101c45000c3e101d501406075030170840b010b02c0300400c40b8081d040d0341d01d50810648440c09480c10000003110b14400040b000d00030200480c00032820709251000000141c4803d40c0c461174018490039412284030741c4117031205468000c000b52940f94900403e0a400591700749802c10703900700300398412446100d00c14134000c60300005000d8140030700151501d0103000c1c440529400f4406001a110038440007002c0d51a005c8449501000411403241a00c1ea41c10140074140c14408241c60000309000080d4128818181010040c0c07a49461800680700800080c0000300071403600d110540220740c00c03198401040b803150710040c1c40d0300651440444043c1443e50b110402007482e08018215000301030034654100134 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 699699037 1250 699697787 699697793
    0x82e020d06181d0102210604090b0c040f0623130902120a050a02120f0a06081f05011e1401140318010e0c0d060c090e150a05010e01021009030516 64
    0x22001040c40100403c00b207203003e071100d03d18203d01611465401c4001c2030500c0c030440c070743d200040c1c9a106030010030018843d00f440d201d80004103401c80309400344400020301030128840d13044012004003440d182010840c1011204442c1200110700c0b00c2c503903801d02080840109254070450400303401d4000d011521580c00c02940003980c5802d8603407176011072500001c00d240d90454002c849888200890141c002e80310700b4645090031030f000380704004a994a0f2808113003a1420301401c440500c01d009040401000c64514000302c0300181c0c84483c40c205148a001c4495407035808850495111426040490b0640f0b00181e41c006010003100022000000c20002008111804581030310080e50003084030000c05503419540302a0802c103c2e9108840c21880c2c00020001d401401048007070340340500200e030396004c90b405402c0007a902e4201c503a280c0041501c003801d001d2000030041509280054907400d01d580007030f440d0810707480450209a21003c0d40400e16015400304c950707a414615030641601d803642 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 699700287 1250 699699037 699699041
    0x160b09010519081005040507200102090301110c1005090717030d05070314010806100e06041107030206070314060907050a02010b03030409020a0e04060806010b03090c1306082e020d0618 81
    0x640d4409600a110004945d5050500c2450320421550302c41c2c4500c80700c1220220990012895003d103a50740800030180f06880070b00440a03803d081806a40e12500310344100c0e400c1c201c5012661554518080400031748010024030301007214027405440c00100c011500c954190b200b081071501c9094100007c2c40040c503031640c0100b090010038040c4d401c441e62284641612007205a07450354000300e5183d0701340312800c00d80344141d800000003480000c0a00425550b02c101e50030110094000d03820180800000c00e40600039542080035048008000b4035015000985045003c1c1c012400c100c03002c100b43c81540e000354000400c00200030b08594a07241d45400d5a0f000e58006040c0c54001103015080403484d0506004940a03070b90b40a01404c0d660782088c0090f5042e420080042002d4400c168404009031a4200d100300000048000411018100340f203091516850f20035826540c0918010350214224400c503403ca401c180c2c04000d6038942020f21903c014007038640200303290220f2010398007040c1c1f0803a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 699701537 1250 699700287 699700291
    0x120c090d03110d02010605010f0f0c050a110a0611030f070317010f09060b0408121c060f151e1d0405150108070203070b1302010306030f050a06050603160b0901051908 73
    0x342e0225080d002c8100012820380c0d03030324490903001c20290403100c083c03a40030f80281d80c3e480c007c1d880c01e42030555582d100c040c50f1045549043d500c841d0b000c8130007805800d114074034901806083c14542085941454020b0b6203110745140c0ea4000d000c0480e42d6070801d84648a201c1210740c0244400c04039586038407502c580301c035041c4240484189407000001c1c4c411100070a55088a0050000d00801c5c05e420160762006e40c0442c01d07641040c00413a40000c81c0600a20a01c0050250924101400303801c04001900d10800864004140300401400c40030b20078020000321320b070b0292840e00249a43c410000010304590031541540d1241c20602000460948514440c0611070b0036070717400940f6102c0c414160317103030304c030354030340034201014540008034000765411103903034501c1c810b16002034203941d01d4640149104c2200c0e02294940c00200d040d0043c00300d20300649801030412006420b599600d0f035441c13010300e1076500c6587e04a01d40441d001c425603002e07205580f5804034001c081203114402074401080b02d101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 699702787 1250 699701537 699701567
    0x120906151203092403010303030b0f0402041202040c02010f0e03070c060905061912090f050d0908031206040e010c020d120203011508040203070807080307030314040503120c090d03 79
    0x203602080405140c001040200380354000c015601c1c2240318000c1c0802ca1100c031501403074044502003044c041421100040d8003c5002c0d680000c3c04104010400c1004280c0442c1d07544039500502c0140078074051440f1040c0e009504a0340010140e1003a04140c0c050170207011581c035004d180102d01080d220000c402881468403a0030290754a5403610015102100c803405002e401440c24080c034092040f003808048080030b22401c14841c041c08600c0c0140c10b80c0c8410508a6111010742451701c1040f10802650b400e011403400d103400442d051500603580e03405201500480595039001240d141d8a49030711105040d40403000a1047d040420806035079559a012480000340c58074042066011007407081c2ca05070b601661810824160b0b44404541d0107102a0003a03034103008601c4001000d2000300701080081c8001c0c405141c440340e203070070007404030f854281411440000e500c00b000001080482143c122001c0c18041d928161070701403030302c0480c2c0100486150440d584440350301c24150080700c00404405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 699704037 1250 699702787 699702811
    0xf0b0310050705160606030507060c1110120b01050d020304120f031a0108091905010509070f0f15111501170c0108040206030c0f12010807080d0207050105030c120906 73
    0xa0485201140d07811604880081c400b4084205a102404e20300c051440c0600000308886440b5120641090b1080c0c2c48440440d40740411b600401a11010b030801861086a06442c52541c400c0054801031885c0301c1082c03d583e4401c420800c5030302a0301998043c880042e0110745926192400381d0003400d0182e0b1200200c2c0c1003055580550388240105011801c0a0b6424040e90340728000540b021940541402058014980d011201c0c0e8080100a00014002d00002c5543c0c104921421f090160315045106c07000240902800907440c4c0c2d41e028011541903124208425a0102c0100d8480000d80d5110f4114000c1032000078070740f040d80079a41c2c140c42d2003110144201d0041c5c5811543c613403441c1a954049100c1c4000503005d464114007a50344426604241840c150400e09103800380d5000c00702e4400c030441c5410050045850401c03d5101400d0a00000c02e078044c1c0b1050007035610b00041c8102410448000300050140641c80141c60003002d4242d100704842c2002d100050702d0703040c2102c1031381c2581 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 699705287 1250 699704037 699704053
    0x1d210d14040807031107032a08031305010905060f1b03040f080a0308070305040b0604050a0b0607060912020a0507091802270903040b0d0e150702060a0f0212060409030c060f0b03 78
    0x42000311b03105003102c0c1d01900c409a01e1000da1802c20001500f00c02501000e070304080002080d14060008010800351f080780940c41a041200141c0f91107070302d4004900888051100c0c1e8000c9116004480102c040124200071400c0d84005161441c401c907005501010b00610703002038000780019224800503c01e803141c8025070707100071084045032030890300503040c1640500454440d04050b072040e60030603100704000c51080346450106590b94041c80c412500e45a445406006000c008201c00c2d1842042e44090309190f1403a0b280c0d960744020705c0c0950006e070b540c4d603d4035011a19020200c600001e5001e8078000490384518070005086541503000350b240010000020401400401101e0907560360603001d50030300701425000c1b002002d20809220381c0d48250782c80381c0540020004d62500c40c2c091a4001c100b58075142c00d0801c2a6041d80c4e412103049401032111080212034400c0990744194140d40000d024245410202c031080e060f044060002881c10701803025407070715900600c070300312000c0e01151605 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 699706537 1250 699705287 699705317
    0x6080a0e0111040905070c06062306030402030601170312190c0906050418090f0506040515010f050d030302190908010b06040803030a0e1f1d210d1404080703 69
    0x1e82e1888007801c000b100100400e011043c0c0740d0f40042c2d0000d520349001c00c000951566100c048072030766000188a010030161042d80585000c850b100781a4080d9004c504605140d80070955840040c01801c0715114000e0415040351020001c1c2d8000d091031401101c5503040c0305462422010385198030318031040c1801404d07030425001301909000c03150140d99080c80d00b4600b10440c0c4000309244070071060725494200351404101c2c8142c00c00344160149028100c2c60504d460b15900c1c00320903101c1050710340aa9001042100d100d0300d9128200e4005803041a404281841d04038001e10504407118201c56090740803025840e40681504140c0704070074000c002c040c080404101660049200d1010154800c10000e250711800d6003050050b2603130281211a4046039460180c241d11400c001a52102d41e41d6940448005c1c0540090259168800180440c0007500700029034204a04071080725a0314002042900e00d001c80e4000440e0071300001b00c1c1100c508151400204035441a141500000c507244400f10038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 699707787 1250 699706537 699706541
    0xc01110403060c0c0203060703050603010e030f12071412070c0b040f02100215130c0e070503060906120a0b0916080708010c080106022806060303030209040608070501050d05091606080a0e01 83
    0x2500140101f07041c0c2c1d207104c004c0700075140c01452a41c055403501e0701d4191200003007014000d0808dc841c0f0003500c6a48402040070030703202c000d01c0352041004208402110b4031000301110300450086031020314542d542201554410b07034002d001014600c0c100f01300002d2001c0400c42e004e005208075200c083c1d25442040403680d503880150b862024108a001090141400420b00b00e0710500c1078001080c090758901001301403440864522001c40d100008100d038a281140d009503000c00200e030410800c0d00c0c3c09482541c2e130383d03000750024500d10808001c50f024070020429801a10200e99049510755100c98913240c4500552084400300e60030107100c052a640035401d85410707181c9a0f4010f00003140c0700310904030414840054041028200450640414000c0c01248091130081d20302596421001c0144022034510342e1001401e0342203c501840203070780c481c0131221001707800c4102281903210311144a05040041040d0244154103040002e5034641059000e84520350010f420009030700813440c9039007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 699709037 1250 699707787 699707807
    0x32030712020309191b0e0f091504020d0609170406112e020c01113006010c020a180507080708010b0a050a211b0203180d02060c01110403060c 62
    0x81690080d443d00101360f8104500c034209607019501041a400f040c4880807142d00350f41d0030413503150b41600108842e00120035000382e0080190b8005106c0c00340005c6210b04800340c0038000901c2144281414810301c5240d030419825103800c40c89088240000d14003d04d03c5501074030070071000c1817508a140c0e01c049800300b820b03c44404010492040c2d4940000201c0c0c0034541c88182071000f950920a000c0d115009224030100340c00907044455458a100e4030403202c8000c5842036902c0098100c10340080300210040007508130307000b0308144100c020a8070000f01e69030700e103400142c40e603440c100e60400100c08607080b15024822a4448104584070200c08940d0101d00f40146a1802810051404040d12840080c1001d60540c40d00000c2d10045003911101d03c1903071203803d8002900c540c809040500181c041c645845a0390001754a01800309003000088501e00b0307061881070313803220090410364030b642d4101c8585001c824020882500c0148603002660024001500c4451408403602629030284004017 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 699710287 1250 699709037 699709051
    0x7090e0105090a0902060d0c0305060f061e092209111f0c082119020412021003090c0b03010f052718120409110910320307120203 57
    0x210040da03400c002d050244c105801c0803a0020810006141c00c00098494000c40521a5a006c2040d0422404100c0e4800d0300c0d51001c1e110305410080484031908102048507480311924205480e0401c401c0044d8801400e1940c075484011015080c1c42040c0789035110f02107403482214113016900c01d12081c014009000804000300d0341c1c001d0810100b40340506c006800c0c45100716911031900f82d0001040310203440d8551605a13405060040c007c48110f11420580c150f044003c045041c9071902c1c00a412402003443c021307018154128a005140e1f06c80d4000c4003400b81c0010071001196030381c06c0c2941d40c0f94030920580e2804081e481011900c2e03d42030a015039610344035861021541ca850440c0030000c1409041200d010f044061310310107451b41808ae030010030b02e00c050242d4881e4a030100740c00031380fa4011032010042c0c00812083d0001ea4070a507084200c180c161609650b41241d5a4070904450403e6008844031020782e100d080302481041c00642c4101e844c0d0f911140154481300040c826400280c0b510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 699711537 1250 699710287 699710299
    0xc021003050c070f080306010e1f05070507090c0c0501140609151f0e030105090a08030412020c040f0e0d082a0f07030806100e010f030c0c02150307090e0105 69
    0xa2004948a900010b03001a214041e071460700c422543c0d01c42c00c0300c40f20541250112804800c011007036810404061506c0ca05035000290350004c145804460156801350000b4850007040442c04d00404000100107040b90010030024243c039080007070800641000d089905601340b46822800c0300c3c400c8940f5000e10400b52640c006030304da4400f00001e0058139003036990044c40000f6194000d5110100d05803081d200c07919103045804804081c5030079201e00a0800c2e0040d40300c070308614005a40b05007220b40c0542c0192400000301440c2000324242802000e5296105c0e04211a082c0e40380310a0b03010b80640c0614800312024121803400c261407080c003c8a495407004070b135884001100b1500c00858000305101c200480c90460a040c401485800250040e000182c512040160b036083c14000e4000085040c10061507003091440000d11142c1018189402c268483d000c0c0096140650890244940e00900112001644011003c51078004880003800522080000140a1800c850b00c0c1e0581e1006000c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 699712787 1250 699711537 699711559
    0xc0928050a0b09040c0518010e0708062d040515090c1c2c03190f03231504020a0e06070c0e010f0303090b12040f020f19150c02 56
    0x200090100514801c8040c0d2a03646100c140d50315060030901c00c0d0310406440c0501400c19041c0040c3c0003014901c0e4079002042030061198010000410742c0c0308007031f4035014400303650300d40103d409522411040b40702c03550685001c03031240300c48044950500303205960800c036a40d18440e04028000110f50001e0300103070780318041124492814010b216007034109120200802d09604944125401c0c00e0507584049170510002c0780c004003d0340c1940c4131383e0340d55004500b003034540700358644c1c0244618512010310044240c5102c0b1a406608010f049520310b0b002c060241c0141d001d044550310b400c4a600900b13581d000310f4080185410303c26141c8800c1c0075a1112810f01c1e0030018400940e11180c0c040e105000005400125665500c03181d1340680b812885a021440c40c5281c00381203a0503d801c018007908003881009185014841c0881d805070b0004814002000d0320f0002c03d544030761066446030400801035044510541910419040b6100360103a0130441103001e0045803120b5070544001d6101c0c0350222 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 699714037 1250 699712787 699712861
    0x30611040e13061e1509020301034b03080105030706122f120a0c450f080f060714040f06410703030b0405090c09 50
    0x6079a80c0b2030f00c01c690028200c40719400c9001100625001c0e54415915800011811400c400c0a88020440c0340410760555066541d841c40d55401e40c0c11105a41082d00f4180703003010000c504220782821802084103100344c001a030828281d210312020307000700d10729038000201c1307041c001180d00840e4a142d4941c095904603450100c003806500c941c40c004031034103000040074a120300f0008480c0a140107c201c0d6914143c4008200703e40004050100382848c150152041581106d220310704407c2000340240d4504400746a00f03031125500c201d0910740040d00603c0980b20000c28400da00b591103c1e000d41c51030b25a11602156108500e10f0203035081d8100f20301007044240600c68540c40e203042c000c1d172681020b0311000310011800791540400000b804000e4003552030b5055074080780d1541c3e01c3c400c10300b025002d4101510401800c91484841c00000094100107040c800d03400140103c10080c0140300e40e00b420501d4655800c45120301e07034410000d0b403000c6421526034112140c0f0b0300c40c0300c44a250001460036 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 699715287 1250 699714037 699714061
    0x4062705070504330305100b1c0213090c14060705030702010e0d120903110103051605031b040305150717040308130803041401050c0c0718110f04030611040e 69
    0x252008842c0e1114581300b00311100714942da413100024040041c01c562840c04c0003842c00780110fa40008082c80c0800ca0803440c1c903500c5601100d02c0c04064039040c102c000e0300c0860700345001d10050190840c605a40701d410000340c400010220780510213700c8040100004100c00d42c0701e5064010013070f6000300640300c01540509000303000304200424190034040030307441d4854038034a00c040b220006602448184204048200d003441140428a03040200d4a020200d44282c0400c511800d4140701001c0002000d0303809100c5586243c7c8210707070720652103a94034079040e03a90382d03045041c01c054519454001035205104080069001280755040da041da01c86440a4802e00d40184c00503c91907509080400801c05402c01940102e2140e01049034800e039440d4041c0c01c40d40098401e0b071403840708000a2020b902c00140d00c1d0203a80e5144034003d810020f6800c010700030542503000912030400850750680b204140b101404c103c0c0d00941d014000b0300043c00d45500b16210f05d009402c507400190340480c0390300c0c02003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 699716537 1250 699715287 699715301
    0x18190f0e1305101509060e07110f100e010606020102091f0207030b0c1209120403080d090c060f140f25021e270f04050a080304062705070504 62
    0x9106640c41c40c0c042e40302c043c18100740070714200c480d94542403688103000b07400d4200310061076a00d100308a071509181c58002c040c20081e0103142003103200712494000341003d105c01d400e039076400c10445051880002d078004c0130303041e80c01c6040c2d4103520f4858002626030060088a0f01104001d0000c82545450000604401498075811003140b003150808070000301c6000160303000364141c84106880302e8840101030321508004080020300d8110340c0d4400018035007030040d00d05030395125255546503040385103c04024240507802900c3c8100403080056101d4024113128510a0300359114002c00c5404200c3c0303850ba11a22040b02e000700310401400d0080342085510505801c0e07264000c50080c0259000120242090380940060108140c0c02c55501d183c06c501c040c4c40c04051010603940450b0800c00151687c1c00100410810054007000404101091290560b005d9124800d1074a900b054204080100201c0e003d1580c00e0510444866501b40c644a65007000d0360b12030020002ca13424027003400050100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 699717787 1250 699716537 699716551
    0xa050a090e07080f0603280f0f08040f080601060c020906060702130507090509091b0a0e0903091509101d06030c0306040b240a0504080318190f0e 64
    0xda0081160301001108a018140e00da03650038480c2001c140302448200c01a01e0a0700c01da1100040c030356482c0c03450501d0404101c56200e42c00c014651400c010f035900d039a040e030041924030b00200560030849200090025070b645109a41c00301d40e00d8500311076564000380941c201040240e40c2c80c02c01490b0030258241c2c00403010301118205916540880c0104401200c0e00b00d4954994082081c117a07440360103c4020320007101d130316032a820202c1d0b08031340b035510070a0b911000d0340501c02d01019985034503060400901519240001f0382c60141c070f210751203420170800c042c481d41a200c441454210140141c54108200a04000d07040108020580d42c20002c07260500c00344110024030540c1e981c42c0700181d17101304a0504650342e240f901070200005c9a0428544038850256880300a0031065603c940f40800700003189420f40d1040c2c44501900d0302c0c011a8400280c903c0001203092805040e1030051183c240107035205150a4000440d4100d810b1050140030b6140b1440101081800c04030801d907504003013 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 699719037 1250 699717787 699717797
    0x608060a0b0111100c0e04090510181e0201020109050d02010204150528030b060c07080c040501120b060402090a0602010c0e0a08121809090601140f0d2907090509100b0a050a 76
    0x107220040380230307034442c8801610310b074009488400501215000e070a62030f05120b50406440d4803030ba170710014400110340c0440c0014214218071b10031039000754001e51304190048100c48501151a40080c080d41c06800366050403104c08211301281c40c081c0040c1c50031030042142121040c8034150740c40e6043d50941046404060300c40d8058040c80c2c5030007000700a402c41c03400c0a400b13400d040c026540c0ca0b004619800e00d02a030b280000402ca5011382d001c080485a900c40e41180c3c0c55203410000034041d02448d88425800110b092000a011f07030154012100700358940c9402d0740100c1d20508108070746c1d4181c07048681d80e030000c82e17654a0500d0b065000300302c58030542424182901d06040031461180303080381d48ca01190302580c0180055400a81000310103842201c2058582181e81c01150140d40c2aa0006007030782100c80c008000d01c2070409000c0c103a00d02c546e1a1550629265200401c2d540882c4241801940c1c081e010880700305000201c401a1002030b03028601d0301d55020802c40740c070360114040508100b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 699720287 1250 699719037 699719057
    0xf03080a08060d172106100f120f060e06150d090503070b15010206012309060d0609050606120318270a05060a050904020306010e18010608060a0b0111100c 68
    0xb4090702564840b04d02c01400f1192900080002100110510500142100c9204c020070403a540c0790004034407180c410b8030b0141c4030441061800d46100c43c115181081c01c03410003e10316160780c0c2540c418002c90358200c10100b40b644424003800741c0040070580c10442028104604c036141c103100d4102d2910207109a04680c602000c584a0802034101503c4418102543d080210300940c0d0400c05580034101c110440174043c0301c541e00d03c8984040c01c2000d18050298000082c02c00e5032820703d08640b05070408030038807503110145031142c0c403000112100c0c0c1c4035581c00441025017160000a4410403000c0b0840b16801c00c00307607002c0014080640e80170710b250740c0c05074102103860b5005404140c0140070360074001c07503103090050400c00c54041c40c2d00014002d4200c03408100250340c002a00034115400d89601080c0c64842c00b0111600e80201c40e484080c0e036081c1500000d010380002840c0c2d00c0781d5052a002c04c40000f00000444040c812034800e40317072651010401084440e0298403614550546003000010a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 699721537 1250 699720287 699720293
    0x140a0b0f1608030601090b0301060906080a0204120f0302010c0c0221030c0703050a050c1e0409030311040605040f0801091208070c0c0303080702120301061218170c070f03080a08060d 80
    0x2442048a00310382c2003002105104e150350300059500040e141101c1000c1c01c66050a200401501c0203200e0321041084203800700703038034491907411900500740ea0341c0c0d619411038181c00e1170380020408901c1207005629003116680b01e01d1045c068044e0040d4010725006a8400c0d6400c804800030a5116042d441e000c02c200301c510401c400c1003400300644c400c0c4081e044c40341880c20a03508001c041c2501d1030040b8904080803407648440c411400d02400b0444002811405da03090480042003c0011019016000140407a61580003805841140e02c92400d0b6100c4035201e445850996064010042012144405140280303008000315a8411054a0280350b069001e80346c03014240300e1680107030b010480340820300c0402035050001c1800346007440e03181032955251900080035a42010038400c4900d9a6100344c410650700008407880480c0c06c500f026250440c404800071180c1d10007440c0c10424818002c00144400c0780550381d03400c03030b5002070b0032600f020700140042d56204e030014101c6511504080b504000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 699722787 1250 699721537 699721567
    0x8010f060c05190f0533090a060203090106181422060f02030411030d0905121f0203010501111f020d0f09110103152105030f22140a0b0f 60
    0x40a00944214440340c01034108175007000d0002d4110f20404101820040b0ba10500701c0802104c03010301482c0710056034038403204500784514940e0081000b40004140501c08105421100580e00c100314107100401039451203004403600381210080b401390010015020034100f080990031020111146148246030341da0b40750031629010040c580b0a0b50210900c414400010b000095a0b00705034020540c0d85420500906007540c0b901c15144521002e401e04d401085080c407640301c002281c40e009480300480421158040d42003405168001291a40910311f11000091201011a00c240c445250108010144030203580300410202d000c07501e0314040441c07120984100f40c10303503001d5050907408120880005080e0f501200700c8100e1501d140d51305020142122100c0300f5948a4000c241c000003025151141c114000e039165550103110110740c041c2c00a0030100d01c002822464491005440d4840c0d144002e00e0110641d0144c02141e2f02c1e500740044686000201041d2850690b0941015245890410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 699724037 1250 699722787 699722833
    0x9010e0601051008220c06081503072601050411010e0306041505040812070c110d0803010909050f0f1c03020c0d0e01140406030e070518041b05090f070f08010f060c05 73
    0x6074011b403d4004105056200051981050502e081880800140030000c3d031707980494003c1300444c0c1c44000041030008000021001c40b52800c800074001031426040c00d0388807008084140d40401d850707021540e10740c40c01085441c443d690200b02c030a000d0006408a0340281002041102e4240c800c010400540181c040707124410302e07141d0f0301d8855900d910302d0001c454070045c1c40468000c12540000324001074034501a681503800c0310900080f1b10b4220b0902c20f1400301042040052800b4282c3d400d220707100c01185c16820064442d00d8603401d8400488210120301c61500203032419008502900e810600c100f0000a03820414904011841a00d034480c55459006070300200110743d0300e003910031828105000410040508071441c040706042500a0007000000410062100b090062400900f0710340c00d00701e0005d0903028007040c141740f4040c090120244402d40b41940444e114804040d50a031280100c18141d0740d031501c1c0821441c1c9464015140c408000200321600e01890b04612014000d08920b00c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 699725287 1250 699724037 699724043
    0x40206160605090106080d09030318050a0f08010e0d0f0f0306080706020313080604030804020607060905030f03040203011b140c01020d02070809190321230309010e060105100822 78
    0xc490401941860171201254003a00d0281c00080c4000040ca4020800ca4202c0350907060820b481d001100314000400b4142d04000c1e40310201c2c500114041140ca0000c07810755403680002c01402c10060b11342c55032103240808410008005c403804442c8140b027000b5840b1658601d09000c6822901c492085040514503088130005a1001c00ca40e10007102851000006110f45000307000c0c0c0d82895100200424001400a8065040090a182044842d0344803040813a08542034a80303d0a5100d92440c140c1d1003564164400d41c00c2003c8011f556080e10400d22082115480704d4a0524122900c01d210b50043c0410001c155800e00487c00c41c4801400205096881180b160740d6500d01ca01c01c00c0040f05500f0b1401400d40b04102003400040c64104204114400c2403c3c007522030035940c0402c80e80c01d1104400c844104180070400c080d400c1720100510301a20300c00c0002e00c45910441010f5640e048244102a40442c2060300500c0b090302030100f49130014a001031021548446440007003031000500350403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 699726537 1250 699725287 699725291
    0x2060d0f0e0631080d05250903061a0d03030b011101060803030106170705074e0f1e0311030f160e06070b0a0b0411040503010c02030c0709050402061606 67
    0x1c201807041003402085803940c9000b00c803200d50340341c4e15a11018041d1521540d0556030718004100c143c50301c829100c0c1116403815104140c50300c2c0ca4002440c1c1d03002888200c030841e007850f02c0030040b206020940c903031024002d070070415807955680382200070f400c2a1176250f0500c02040b40e14000f0700c0c420700a050180c0310b024011503507540b50810003000c0d958a441d5004e170503030480041c4038003103070b02c41c003100c140541028045658181140007010041030440c202204d1001c100b258205404010041c580004150840c110404034120002d95903484401182000200848103940c80c080c0583c500400000c024a00002c89402d240d81e841140e1303200baa00346402401a404100703480b2448410844000d201c0d14240c100031000307501207503103408cd03050028109031112000417030141c0075034041c07002800e0007001440071180d111003646040e032050280901035400c1c0f16100c0061800002101c2c241d01540c0000d008a51401002400034100038000301e034004c804000c030240500500101140c900c1c010840 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 699727787 1250 699726537 699726571
    0x27030207140a0521011d0a2109050402031b04031b0501020c0907030c110d0e040f11070210030603080f0424020d1d030a0302030c0706050702060d0f0e06 67
    0x514260001141c604510030340c41c140061019484a140c0704400c100b42e10b444050512443d042d0301e01400344c11000050320748221059240c1540002940501c0602883c83d00c1105100106012505000300794a0004241010701c04c0103182055401503522036000c0502035200c1002c07520780c14555125500079100001c81d0840030354040a110900e0b40180b02c00d00041505408042c00300d030302220000d2181c030a0550380d40c00001054003685240c2d036100c1001083d200b203443c00c0752000d0481941780c9603c41c0107620b440355140081e00707684100380d00c0740f408001e02403c02c660341d400c114080c101140c0c03440404d51039090010020380030b18040d043e40e00c0030820884d00d541c100202b004200f140340c0b0070b200795062400c4104480b513401141080114005203881e41c01001c1320045400c101c181c41c1c0e0019098880c240203c8189580403002c2d1180f4001c441c1a654000d541d00b200302c656004100c03019510140412080c826a14564840900303080d5500d408200656003954131810080c7c121f03809278811584d120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 699729037 1250 699727787 699727799
    0x207210b09010b09010909020f030609061b09030a120903060203010308040e0903310b03041b06111b0103090618050f010c050412030e0a030c0501080c07110427030207 73
    0x41a56120040300001c1081c0d40c0b840d4002104c819040c03140340d44242e41e5050000654884048244190780d02408440d45070800e154500d548800c2225030742002366a00b03a180c102081c00c03504079200050300600405d03031040180c030781a4160844003455028000c4100300000000c41c140065030007035000d5030030303603468a2500080c4814403400503c8000d030364104004072044a0021008500e0079400c0382000488003150825601d80044141c11041ea090030102c20042000680035542c03000030000800c02848540d6005c00307440e14200702003020181e4100b002003050b80c0385071880c0300310003601c14500400c0003c5540c0f90034084540762604c48801003001112039050010030440b00e120249010000c104444404000400501403070044644071594420444141449a03154500950b002009804401c0d41d078607141c40c42812500c00c40cbe0101d240390740018001845d42c000c3e1b59844e50050125800d0845d400d0400005180030200804003003407038161a0324138000c259540301c02c640701c1d07002801080d0900d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 699730287 1250 699729037 699729053
    0x21e160602061609060210050c040f03050f100e03030f040c0e090c0901060f0c110d05030c1e070f0b0c07090f1401090b0f010f0c0f030804030e0103060b0f0a020721 72
    0x20b450f407080c05920001040380c40c0c0d0010b240d01c806a40400d000038117491b00404c80c441403085500a41c01190056804001d010300440c5200c002c0c1c2c0804c4c1211200140c440e9a40141c5808210511150700b00740002911b14280000555205104143d20030070281c0b030b01039001c1e42c0d4100f0740d0300c140990321100600c100d90400c02c0105000d44074505204400c40e0002c0070082c034040c1514402401c00f562201c4800e09034461520104009038050f09698484201e840c40c55924107041d00011040f03601c051440c0701e480408039954013034030403a60042c2c211302e05192100b00756502c51240203000b40308050000464285a02c2104928000a0004034003074407460703046503940c081a00300140b00c84c907003001c0e0580c50303803070501541c4150340a00b0248580720442c00151854040303890040c00c2d50a000701c2e00d508040e030003410588a14031940f903800800c62640011001c661a501030f42c040c41d401008484886c03540803000e006540d4080c41210403141d242c250b03401c4888440761180c640d00c01c070000759204211a41d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 699731537 1250 699730287 699730321
    0x1090c0510140306011b050a08031e06030a020f0d12051909050612100b04241e080c0403080f1317150705090607030e010f0c03021e16060206 62
    0x50301e04140181d201c040003142c01e20002d404079040c481c10b00c01c140000b201b846941d401280e0000e0a4841c00d1400d824800840d50085922810742c2c00321007900001240c0d02c03401180924009002400d0b40007207542808000c030603054505030700c01c0d004d1500303400003041c0714803400b000e1882c0c1e0f48054513000300e12280d0000400c0200e0040600818881c00d21403920b0f05000e40b074140c0e50700000f9445546509980c0b03007864507175400c8401c18880015000c034840c1031482d43d8a0260303030b60f114941c0501407007410071036a1541d01180526407a28503158a10402c0c81143c7c440d400400920b000f0313207031695a5640005c964010415a0381c448004074850402d03c0c02c00c00c2d244001c0854500041286c03c0400c0c0d2551146001d8040c4801210300b0004500000c0c0320f2070943e14041d801402072940d501440c01c01030012040036000c1400540800c06200071944503030500d20040c0c0d071680013000300901c20400d079044031340000c06d2401c0c1ea10881c940206600002c0001c5801040e1076005029581450300e407a250143c0d034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 699732787 1250 699731537 699731569
    0xc11032505220225050307050d050306091b16050c0405130201080a1503020a060c0b010b0906040311060d0c08011d1e0a0e010f1e0513032001090c05 65
    0x12a048422800600b1020386840b844549001a55016035103900480700b071140d034040b030042840c0e800e0b0004003c000801447e0f400e0084044902000c01140c08031100e1000711111034024151602003401d086403060a41c0144540b80e00e01c2d410301c003a0342c04503041c1707201c3c110081e1050381c012005000241014803409802c128400f1001e410110f80e500003800420300174110100c1c03290381d44150b030740716241d07041000c0103954010504120603503208001846002211801e0b1005040b030000052045030100880d5103003500600360b40c2c01c0524503160008240007800456401000411200840d10168403070f1098040307840c0c0b00d05001d07504180e81c10484148120b46521307030b003401c2d2040c40740755205181d411000014582c1c03925441e81d900882132003d046400310165180d0f080880d1454001100c0e001045011900810390080e40701c860f01240070340e001a6560100c00e03200741421000700703202d00240c40a07071313075811032040201c07283c001124211600e80d9004d07540b02700c00c4c41089c007107864228000038000390 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 699734037 1250 699732787 699732799
    0x1e0c02060f042925050307060c03180c05060f13030f03140306061204080c0a240b130207022b02010f0512012106050901020307140c0a030c11032505 65
    0x1c2d000414030384545640b19548074000310135109400348650076009030580c0081030329101d13100752034a100940142d0b18440046030804000c600340d09041e40c0c00030012a007000c2d1000c0442c0c40d100501c07080350720000c5a2445c50104010142d1811030407004071004522800ca12290100c03079060007064121000681c9417902020028410340d0b0b940c460640700c007114080c0382d21106458514003054948104070021000703000d038103010400c1c4059a40300c6600f1465550b15000311510003600703141151101c03050a0f900c1042d92041d03002102d0035501805909101820110951104002c0c102c0341c461078800d5081050b030402c0b483c2e0304550744600c0540442c1d40c6810140c0c1032600d4520a01401c02050003841080d80140151310358046a51440040141c1c000c40c0812040c103194912038040c0d030045480c1b401081081d100140301840710b8048658289588000c0c200c1d046040d0350849101c0d1060f1001c0da0440909100580c0540d41070140c0d480088000d1101b40207400f03003046040c61810a40d02151040c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 699735287 1250 699734037 699734099
    0x51203010308030103061e1a09010f0b03040b06010e1302070302010b010c201c0c050907020f030a050310090f0c181a0702030304080105040305040305060c0a1e0c02060f04 75
    0x9201002901c2c107503541b010010410801c00403000c0d0001c003001c044090624180200260110801d80b81c0000303a0405031003e8002c0e0ba21002d1514208402e40b08a0341c17028070801c0041d011490710010341c0d41020051404902c0c0f0364002c000144287d0014006c0d4084545c00110300d0109602445400500d4000b0f0070b00c0d40291010352a107641120b6200c0030800000c146541c91051036450b2901c1c003821021003421780380c81e00a41c0c18007a5008001d07001e128020900880418107540c00082c1c00d1035030007038450041d031902c00199022a840d80028004040c40c0c0704000b0045079500c0c45002e2410005900c0c5800070340d684240c9130090014000302d80420946264078007d0099030700084018101c4200381ca0341e95903900c254400300b0710f188540c4d03001c0e1120394a001f082c0401c156118000303004603030243c030844450341c0b600f03881d403510707481103000b010042901c0041c405581c807100441d0f900c2d1b44205040581c0080382680121f015a030265101c605002c400003401d2180e8807103d4840310300300700b41c0c80d091103841e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 699736537 1250 699735287 699735293
    0x9010504030504030b0405010605090a0905071a04150c05070902090f040605010503010b0f040f08150f090607080a1e0e100e190227060109170d1d15070512030103 71
    0x10f2182d404080c125000150020301840401d4200d1402080301604d400c3c1c4ca450000300c014010f0040e2402102e8900928000041c41180c1d070442d0f003210b00f1440c00c014501340c40c14554036108600c94900005000d60400303450f0200300b0030302119004060317554000d40c2c1e400a03081001000da1040503420310a80c9822824810340c0d03849400c0c0e80c1910401d4121036916500860041700c0d80c0100e61180c1201f800749640030403c0400421000c50b2441800d610700520b0b1601c54442a65040c100c0b001c1c0040c1c1d000b500014049845407181c41d030800016600000c1c400c54525500044414803950030380c03504d481e8802316110110801811048566a440030040d005199022980310102c05102c07496108514507180c040d0359501c4860b0031920951040102044156110285124021101c0502060b41e501e000603040d800800d2042c1c0c2240600c024059414030701c2000e480001c1c0c3c1044c40c0b54040d490603d021100c1e10380704100100c1640043d0034649500340742c80d0640c134110342034115558101080c0010000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 699737787 1250 699736537 699736547
    0x50a02060c0c010608011b02190f02061b1b0306060a140405100503060106180b0f1911070e060a171e030d050c07024014011d0901050403 60
    0xa054030041c80c1d40e500600c5030841c00341a050b0054181395282c408170304284441c0028600742d1040030b4098540c0041400c0c00085009403501004d810020079843c1c0d440140b618400921107814213a07045461402e80b00722580c1360005007040d5490701246660788a14074601000480d5006608450100e0024104500c0c0c14800840c41881405582c0300c9000ca4141100300c140c07980601000f030203d605075a0745850080a5101d115044484421403030b40100e9007003102c8080b9511400d00c00d00311b0b450030841500d80b85420f1014002007040004840d0b08500c0514144048401400d10407004046400c1c032604000d407084d150780c0b2850075000580040c0c8107800c0c004c501014444071030100035064000c0303080b40b942584501d64020444620703100410021aa1203805445e40c07034000d6942c241212001c004209020482c1542054440c0c0061485000040390162044070a401044081380264440c048840041c80c00c2e0000214880c8444001b407155482101155000d0102e50003403216081c01d0710060a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 699739037 1250 699737787 699737791
    0x6110f16031d0f040e0c0409080a0905041a0603070e03031303140615011404030c091a0a03050303180709020a05030f1302092e03060e0d03051e0405121315050a0206 72
    0x406241c5a0300305256082c0c5c144500504141c1c09041882541290301d0100c045a1194040d100800c0c490301c3c0101c0c0e0340c1403034030600000401506151440b500650208400d079000144008204080207800d038403242c500f480605850021000c40c451468114034105858030074a10303000c5100d61003a401c00035848200002ca01f816070342030819484518102d5203000882c41990000360128400010008243c12039a101028502c01e600c04090442d039104100040e001043c40043d0241c0e00601c0404d58490195007103560001c0c10300102e60100382c0d58030404050307801c02d0503200040344000c070421a000c1440c001896010000c0c04035071b180c58416500050038040d025207066048524034011a1080402415800203074089040001106a43c0c0c0b80c540040d10b158965503030710340200c00322031250038001d008560260306040a500340012003204850900c10004009450611480801a580c0702090008203425062880c0540c8030b5401d00401e810000d10f410400c1040050070005440740303c0c4e0104a090f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 699740287 1250 699739037 699739039
    0xd110d1b0f030b100c030c05010623030604030f030e030705120301142d0a170d091a18040b0d0f061107030e040504030e0a060306090606180306110f16031d0f 69
    0x5c40d484d018201156a06041c940040c401d620304080070400301d140c500513030395158044549a803001151010700d40c452406907401000300d20202d2031802c02c00d0081d08910850178074003040f00e003061000e44035240303064a410381a0b150b43da800001441803207040c1000c184114025a00101903840d9280e11040701e00725511088149076601540291568a2410100041c40c061a4110150340c0c1e16241c01d48a00001002c000443c4200da0001200200c46828004d44000040a54113022110107174103000074005140c0d0340c2c0150344910384545035640d41c845c1244640a0701440702e900e0081e02e082c00c201d501101544800312014068000000d0344240c8079021070b0360070b80b0046400d0f103440c6000d032a841e91403100640e11011002c40403130850b0381588460100e0720320035801d00100381c2e01da8084d202400000720a0b500d58041080a10100e02203402140301482815206858400180041d0400c1d40080316000f0340f0b807001c860131505240d40318642c80008a26800310720004d148034800a6071406403e007500d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 699741537 1250 699740287 699740297
    0x20d030e19031103250e060a0b0a170604060f1214060c0a0201060603060f0b0c0f07080c01031805030301033c030e0f062205060307082203050d110d1b0f030b10 70
    0x9801900c424225000502d50082760276100d5a12a0020700f0760b10000c051404680c080c0b01c0040c0080c54a809500d08843c40d040340b804607982070211036440616103580698207540350f6400b03c0000241006044c2c0b0a00500b18499120b0f509184020309441c49076101c803040608026080c0320048400920b0380440c0c5000380c2d100d5541d01e10051460400910044841b824040c031031002442d22400700d0200c0320310400b40c0e0100801102c60118005141c640300d03018040354001e20040c400074402d55440e030704195440076510144412011406107001c10790388900013000b054580441019004440450944401c030768201d406500c001c0416001c0c020084d01241642d0b010703145003006103148044602625014040e9580e82c81c00032800750002c0000e403000d442070009648001c0302c1c40b06002d0300800d16a816518a4130300100c00d00301d0740190100c0703400d1001c1801c041020100c0c00e88588a00034010000710500400c80c41d40d100c0240c220b4003008402b90a060526980020960f80e02800100e034111178100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 699742787 1250 699741537 699741541
    0xf160608060f030106060e040e07030c050418050a0c05040e0c012c030102040e18030309060a1a1818190605040512070503070519020d030e19031103250e 67
    0x10301c2c00781c03280100c0740c05500c0c100c00800d0ba80c1e4040c108461000040c0d0b82840f2090321401210764400052001038820b0001c2c0d0406d000310316064002028410003400400500031064860038108104028211880a4054010000b030b00713160203001c0803203000741d02400c000000d040000c0c02d12600c8220380202e50038100c95004114581c40c0e001a03043ca8050001c54440d43c403110541d188220664050302a2180301e9040c0182c0b58000003100e1082915001a0006844035241400035040c0401c0c40c01d03054010000c1c4c0845501c07040780002418001c0c05c1031201c2d5007840211100b07815448803900003207402126074142007807000300c59080650703804100081c82e551982491410205400414405c402d0001405002d2040020190409034003c40580d2105400a07840d10059900454001d4001640b104041c02103030103400804c011410141c0040c26405e04446200e5809030a604215041c2200c07000d848260b0904100d0a005c2d0745109003100c02c8011403000d00c0350700181c1c510400003a1004840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 699744037 1250 699742787 699742789
    0x4120f0606090e011517030414040b040c03090309081209090415110a0e0603010f0b03040f0219030303050c03011a030a0912081501031a040f09021807020f16060806 72
    0x806400102003242c02042115a10107071980a0150807900303507038105140c900490000030010030104650400d000031032a02e031030900c0c072401180080c4040c5510030380c0c0d1060f03007901e43c441e030150070141040f03907800080b484818603020746085aaa00584250340c811030443c20510003030b004035192090100c1e01c42c880c503540d41c034100c40c0000d582003078001e51300e09000c407002a000c00d08001d0f040080c06900c40c21400c2c90350900b403100d1804244129025510040c10800c03110801000554205001d002c8100340e580e85a00854281000c1c100301c7c698081c01c080d001c20506a051288a030020054a4410720715450041001880d80352000e0507841c40f070000020541c070140303e900803401035911440c1d00c42c00094030500503124850448401e4001d9a030b01410b81103a40c403034403808100107001c16403005025040410b20004204446948055a5903210f0403000369862001c0c0304a141524640d08605152203a0003d041a40c0050b6102540c0c0c420712007940c1d01c40b83e45481e5425034001e4641500507a131484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 699745287 1250 699744037 699744041
    0x9030f041a130e06090a09230106150e0a080d02060109090305130b041d09030d02130e010306140705091012060302040908130602060f1506070b0f09160f090c0512090f1204120f06 78
    0x9400503244000c1e1602f6000143e4009002d400c540d007084510208507035030303010460b880e82400e4081c20700503041000140907000383c80c3d00050340c090103868540d04100c0051440140744416421949501700d02240801543c511080501101000c50380044054244054503603a60b0141034001c542d441d070041004c03400300e07007c18011001021800644221540d40707007003520041c038502d041e60010240d14000542ca560081084944060019007540489480700c10101c442c480e607107181901c003948603180003015a4030b60150101c003501613056280d8840014004400d00c800d141d00c440e003550451000c01c51640c0401010660242d1200b0007040211140d00001d003c0e40301d4458010000410701040c0540c0c0045022424403540a20044030741500d85c40070040c048001034898291200c0042800344070300011038001340361607821420a142050300284803190601000c580c040140d601034a0b0220a200c0708010002d0b54100010035189001c0c00c02c6000d901000070520090011801003803907100b000030715 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 699746537 1250 699745287 699745289
    0xf030706051f0e090105150f0409080405030106181b1d010201020d020a120b032a0301090525061403010608270706020609030f041a130e06090a09230106 67
    0x4032040c034101e84880c1d2070680f0a4098403c000203629000004d03040300794110a03401d0f03212008128030954940001040301600c0c4180c0100c0e103d08040c40000b4142c0c8007400b07101c02409401c120140181da42003402005c03602416007805100708054207015066400540c202e044140c18440e150a840000e00180e0282c490248141403c51001950110340c9600000b01d107000030039640305200d0100c0580030540c1d50030703501c484084035104c404805402001d40140da500e0400700a000030400700310f940c45240c141840080c075600300d034007406006135400c0d01c5805c2e04c0b40605032078106035520400c584034668242c04140100e006005d4040080f44200c3c2c0013410542116142c07407221400d000865640503218040741c42180c02510520011421060b00401585c2d9855000784076135003014a000210040c50107070301c410328110f50040124007141d0321403040c1500544408000c14045041c40000c0c49070781e18005021004051410130000c00190030020741c14000c0303940801520310007200014050041c543d07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 699747787 1250 699746537 699746581
    0x6060e01120603080a091d010b09010e0312040305010507090603020403080d0f09021201061a180108060111030c011a01020c0d060f110403320a03082e170f03070605 72
    0x1c04a004a04070b46e010b0120401c0e1780003a01004032030303600381d07000a581e00c10a00580100d0117090000e880154803480c4524400c0c54004c5c125000015078401d1802245d020341c01c00d030b43d180d445808001712141c010b03002034000c050914046240c2495610307051128001e0007502c0c41010b80703503405060221420f404c0002c1040e0000c15050498804000d01c0c0c0c02800b803071061880d101040841c02581601c00c2c3d00341c0da41401c41d0218682c3d801108401150603810043c400790501c51419103c040340201000507144848201c0000980c081d6141c2d100c2d10006d0729a28601d0440d0b00141011a00d5210ba8144d6859507920050210f000701030581c3c1d10010b0f10004403100300c6440e0205000081c000c0760b2800308000303c6a10034600392040300404440080c2c851600f030860540c40000702d41e000a00ca81541903108001e02440c40d548106c00e00a03034948540303024558000c0a1103403081c001142c4240a02e540707140f0f80002010000000603009840c0c2c0510080a0809a035031000100d070440c03030f91001d041c1408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 699749037 1250 699747787 699747803
    0xf15020c01090b0603011509020f1606091e12030c031b120c0e030a0b04020609120c01020f0d021e0c041113230906010309141f06060e01120603 63
    0x1846100d03480c000c00c00940161944000c1d680813911508061149030090300108aa00a0309030070032131000003a6021141d50074800404014040750308031510400400c007840b0306804103001d2101c0c10011403015400c9181501141c00624100002d5414452551301c804035003408902c82c90b0602058000348900c5400b00d00190011244182c519070004c2c100603264a040001c000510b00520115981d21036031001c5034155004030b0407100400d951300d40c0e99500910003004e0740d260014800200e45001d0403092003e081c2e920843d40d007841036806000da07041810005004105030518818025a100c12460030441c01045030361010010030028488850a0040500f090103401c1c000403c00c400e59010a00d6105150001180401c02e130000e01d0310b030b81070741031000104803198618a0401c604903001070f1800341415076034841840002e40080c0c202075070080c040082d00e02a0510b6903480070a05c00c2006e4126418540f100500841d0b8000300c00010049003841c001038218a00c0780c40c840103002a03007000d02400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 699750287 1250 699749037 699749047
    0xb011701090917070210080a0906020f1911031b0705040c02030901080c0403020a03080d1506050306010e0906090c09030f030f181002060403030e10140a0c1b0f1502 72
    0x19098000315042880340e40303c0000030140800410660096510003507110b04094080905180300d4015142c200e0940ea0000614200c1650f034081241d00c40d0902011803140442c258401503840701d004208034559041ca110303000e41c0c18203da1b45903c0303072080340406000b802807003402e034240400490025010141040002d441d544a02030762329004240403030300050000380010b40700d810351b00c10b503011039074041d000c0540075040d561880b44940000c489150515a21082c150304425400b081c0c100504068803425900c0c2801400106510000088103005507008010301c526070f00d603010101e602c440900c2d032954885000400182c00c0c0342a803034840150703101c0030071101505500e05004050613900400d05408148644050240110440a000d40036070008000030f0007080c02034102e42c40c40100641502d41c40203852030300000701c3e2070028030241c07000301c807404000350302440348103810084059084c2004880d14035101e01e0080c24a540009110065080000042040250b940803508106030b50540d111 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 699751537 1250 699750287 699750299
    0x5090301020d02040311010f050316260a0c03060810020a020a050f0705090a05070503070e06130803031009090f14031207080f010906050607020118030204060611100b060307030b011701 81
    0x2e0740285c0020740b0b0172500e42c20010031641c080e40e0303603082d078101a0300c40c10709654070400303e0602848a8a41c03c001c1c050403003007042020710785000203454591541841421400d0603954a412109004a48000e1501d08641448000c0e0006a4000c10b0380c40000056520003051200b2410007400e514010858840c10003400425280440c3e0301e0300381d890a85280c840c60703545411160070344505030b60f1507001c1041000414901440342c89400c941010141c0200d107400700040c1403001c218055070000c0358540010050195034100e491604000f0001080d00b44407400c041d0711a0000319010030001400d038200c42000d12060b5405000b694081c0640d04a0031907145040c1201030040c100480e4580041d841103400841d003400701c0c0c0300d8001980d0014003000d040000e50b40c015a4099031070000b406200ca803130400000141c5e194010074003c0d002d640e40c6ca0708421140600f09213070018007565400003506104201310a40c50b0038055a600c41d400d49030115007994540d0050b01c00c006200d142c200050031130f0380041f4907 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 699752787 1250 699751537 699751541
    0x608071a12010b0d0c02030306090f132301050a02040510120e0318131b0e01050c1902030d031e0203040809091f080a05060601230c0c010305060603100e0705090301020d 74
    0x13081041c500305000d407101c00e0104a0320f9100440f40160705c0300d503c102161064007403040311548002083c0040e060040345403108540012107403401320850201d0f0741c45c000e0240080c080c1c242c00422040e006e604143c10000011000811a10600d0401052040075120a070168026400c4000c4c1c0b403003540d0ba81c004940c2041c081c1d598084000b801202113205480d0b800801d442026045a1420000c403840c1d4104c4000701c50b161490301511381000030510140341c01402c1070003a04c5040001ca8900101c1700640e01c14582002e06203400719040c54603141c0441030308039410000204503050040016500d03956860850020700646041c283c0119445040262541840e50001c0d00306200c00ca202c0b049a60303a0000035a80c0c000c1110044c1039401000216016502507222850000716944072101d1501c2038031000b42580c1c000241d002e1503644800704000039542c06210b0076030007280503208d103407541c03600c40303640c020f07004252040004218801c000110464461400d5512011000740299618a8481d440d280 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 699754037 1250 699752787 699752797
    0x5070314190c05013f091406090601120503030601050304062d0b0d0c1a0c0a050d140a08450709140406090512040303020609010509010608071a12010b 66
    0x40880c1c120202102c072003422040b80155500f46102210f2500d62605c10242426100101c11041a444010307101c00500c04551013001841c001e0010021860040310b880d01d4420180d211310440004021100045040401100d90103030080c200a0364035101c178601040100341c100030b01c0c084d10011068010381045d0f80c42d9407416051a4a02c10300140c0009002c10110942c0104001c12075440420200140301004181c004010000000f5608003040b192203182881c507648411926a04400f03504242c450300165054280c1003881d01d80e9003001803c07240030301a64400b4009000b0400030051041c000c2101e84400c61307070491070640c5034000f000035075540c221a01512014548600031b0720004280d01819101d80d580c0c9003030a442c1d0304925207032511054020f103c40340050310325005c0e4154006e201000c0c50000c3c8002c5210794020041841d01c14006400c4450103070a000d1941d041040803c8010b9000503103500351072003482820b411100d94400040c203407140d012919220325180c40009045011100908 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 699755287 1250 699754037 699754039
    0xf0c0b0327071d040809032b0806010e092a0901030b060a080402060d060e0f0610031104060315051306030302120708070f0501020903151b040305070314190c05 70
    0x180c1c808144a61442d11200d403400f0710001c484456805010000341002241c0d000340c020600c940c40e142d0b01102107410090700c80300ca10b200032202200584a5041c3c0103400c442d5480c02d00e421401c0e0b00703100000034000030040b840300703200b20441002314001d02c81c22507075041205c861a038103249162404151102e1a0064040180030034a400101c141e1130800d0012164040758607620700403540c3e590b50070040c01340c0040c07040002c91360b40c6001c00724490f41d0f03101069000c0c003001011403003103181440070082214a8803080038205410612400c180e18900d005440c1640e5140c2004a503c2c9082046100850420f9101503480444a185546601d00380d51045003034a00a48c2903450b40c4035800c485110910a0b40001024404100203400c04109902c0548900912030b8001614010103600041c4c50070007118a0001500f80c51400c9c0700b040b10844104200c0e0300441c42d040341c00c0034515264a0380750702c2d25110242900340c03046108020711506101c20307030303682d405040754016056181c18040400c5041340645 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 699756537 1250 699755287 699755341
    0x7050c070e070f021501060c0804090e0303063f01020721080c040605040306110415111c021b0406051201020705073015020403060506041b0c0f0c0b03 66
    0x80c443d140d1011909103409020720b174082c2410303460001c044a504042807070a4410281c00c1c000801c4c0b81c8a54002c00c2040403480c0025512030412034104214407010140d25240e2104400380007070001448200c00040d45100c4010f600d1141c00040050701a10030500000c01d00c5038550441000c107800628460307890308407036030360700b48556480c90041681d1146001d23600c00708909001c1040051005e4005250081c3e089071481d00341307a580c040001e800044030b030340200448c2c86400c5a4104075020008058034003901029400d444100707240c06501c0e8140e140d0115844806a141f40c2e80644507504080001e01019000250912124514038003d4001c6101110507028201c4002090703400000e030000c012800c016404008148200c000d44600007407101201c05a40b8812500e03c00c0c0c0a510180000b180144000300e45450030310108400c460a005001c50021799001441c1c1001b60700070a45402ba80e841100d14400e102d090420444a2000381c0c080c0c1c01c40d1030300004000c508840a80c0c0ca03010700f2881420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 699757787 1250 699756537 699756557
    0x1d0f040c030e16030c12050a06061205010c050306011d0f030703140601080c0a0504021308011b08100f0e09030d150303020c0d031409060c0304060504080601090b0d03050307050c070e07 81
    0x86283d10020601c4003525042c80c801090180354100036a82d04201d11075400c0705c00050342603071044280ca62035401003801c08403246426081c084280101c24031003c1070314000e0714502c0c00000180c60000e0b58260b240c3d001d6064070803454903445030f401c010041c034401011145c11640d01d00c0c201c9072800850f42e0b000d6032409034000024404500040c414041b4100a003203942e0a41854280310080d004080d2403603040ca000c45002070207000a10078100f03981401140c820001c1c41001d000740000c50007a000c2d010345070342410701300407166a00d40c101045d240c0b200311054040d25240c2e040c0303196009000c84140281c1c42d140c41d5160441c0304406503000c030f0307100f902a200c91100c0c64040102c40440c8007006000b140100e03a002e000e090711403005203506100200014141080396050601d160456080340020032070002d02846041000c0000c61700510203902e0030702c00704001501180003c045281c0007000e20402102241c1d050707004a0545600e42e400b80102c9107070035520020002409016981c00340424410700c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 699759037 1250 699757787 699757813
    0x9060b0301180c0e010503060d0f080c01150e01031b03050106060504051003020c0c040522050601060305101802030402010e19060e0319020f06070203070b0a1e1d0f040c030e 76
    0x50030f4903c40140e00d580c1020b094000c010f40f690351004280f954048102d242d020001b61910711030382411030299078003644503412101e50a00f1070380b2000d100051207600c10b03420003922085214180c103403035000c040314980c01f80d00000007425130742503000101203509102c00400c0c50396120000d082161801c84d040e404000054005400728071404e0360032149600300c03500f02030507418550050ba4104074850f008055040c0f0242070100c010950b54002c40c6c41c0d4010300010401240e03d402082d0300502c0c07c000f8040190b24081880007001031100034900041c0e0084001415680190000d820354200a0002d105030407242540d010036010342e0080c407000c074980d14420009400d00154454400822002d88400d400c0180c08103d00d203024140d8680c0d10143c200240401030328180580c00003440d8040a05440304100b0788003500305040b04003892074034000c8921030b5403042d60110003000344592600403a51444a00c5000c510f130508207400e4503410608181c03140410f2640742d4007003050460382109580142e00d21035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 699760287 1250 699759037 699759041
    0x309030a030623010c1509030309060b0301181407122402030c1209010603060213080105061c060f0e010e031201050405090304030209070c0b182b12020409060b030118 73
    0x400c0f454030a03400191581035401414802d117058020207554038286410380307441040c0c82001c0c00c120000703034640034103404000450141b0702030010b0450080c00004004000201c809900c10000b802c5103140c031010080800080c860b440c0a0120302114202001c01c90602c038807001c0c400002c100f9000e0b01c000c0100c038000c14501c20b032401008241400c1e407800309018440341c0b01e420058409801550b03940b00c001700203900c81c8000d00901110400c6408914944240da03030844500900700c60181e0041d40345e491a8892080d40c1d1000c03a507200c030b00081c41c524800044401840500d211403c1c40d803a00074071054110000014051400310386201348a0b50b0b80781c40502040c0d07074050710b1400b0150700170710082c00185041d03a17002d07510081b00e250168403503280740c494002c40c15098400041c00303000700030200000d20090200c941e40c98201c82c807454100c0c4440008130000b11200503c00100b20b259060441c5410b601d8040790020041c140303080c0800350315800c000c80264000c0c4554140c5581d0382080206041140c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 699761537 1250 699760287 699760319
    0x106091508070504050f011b1b0b21040501090b010b180103060b0409022101030c06090b07050a06111c020d051311060319020a0207051203070c14030a080309030a0306 73
    0x40d654507081c01e1030001401002c2d0040b442060500c50800d40040d21030003108005101303e07008000c0c2040782d1f07110278200141e00c03e240c0c000e5030242c2401c0004110441c03003056142c66021429600b000d031a90346050160041c940818010b107045000c4000107188036060000d4800c0341900e507445044013420a0040d4100c800c544100e001c20a418001041a0003c41d400751900d0094011a50041007c10300005503080090300100c0d1080c042500034022268007450b22400b070888100c407146491a1621107941e0303120030500080c407058490b81000701c2d100b110f41c203071507060f20900391084070720010165500194001002c4100c00c1c914040009120640103411086540c4c3c0048103041400014010f11041c2e900080107400c10b424103000b031030071084a43c0300508035103880d5405000c0d0075007050108214107003141ca2a1a041d40140405c2000c1204a4000000c0314419180d00081800d2031f00072a0a09511040160145401208000000360044001c11728171f48181c0d0100466030702c920162241d1680c03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 699762787 1250 699761537 699761551
    0x60501110c060a05040e0712180f0b0709090c110c01020a030914010e0604090f0c140927040507060f09060e0d02040e0115030c0b070503031315050106091508 69
    0x4901c0e1001d1003400e050300208a245014980180381548800503420203000681e50078000900000c03481c03621031901c2c4118035030000141c4050710b0f803116686035092160800c007005044001c09901141d08240540f0049008151540d030078404c0030b002c08000750007150400c4541c0803d014144200043c0d44c4049251038106500d0b458000f90503003000e09160400d880105c5090600800d80355101456031100040c10081848120116660310b00d0360050080e174003580b00040600480c0351800703840225a10903510310342ca040d124601d0301c0c031911182c0381c0a44c05200000080380100c2044c0400e0110120303410741a64a41e0b02c88582040f504003040b904046d42c0c0c80b40d0341c0010f4405000c0300e00e1b0f24141c04540d9425000400c04124007005412460031940b000505210b8410342d8002041000510843c070302c014604505010706181290700c905460384001007078001a880c01d480721508101c44241020002c0000380810081c0e9070319214003402100490083c1103001e0903681c4015040f5200780304052184070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 699764037 1250 699762787 699762793
    0xf12060f1e0b030f041514010b03180a11010c02280302090106020a030203160201110d030b01031a15130f1206050a023406151e030b06011b060504050f0106050111 71
    0x2580782c5668200b682080903648105031203441035007581500307644540c0a815a031275419034900f0208403030b5a00141242e65038449811142c149001310b40003000200c2500d6083c00c20703000d030368000e10020745003da085400e60000d4810051003883c0300384102010003544d10a40d2070b052541d8950000380c1c2d440000100c0240143e00c10444180e0642c070801914026030f2060401506124641503013a007040d5610b82e00c0300001340c0d9050300206540e0325014070070034418031500c07920021880c10f0101d40d91000c0c0745507034992030400240410b030313008070207248100070400a000d0941c032075250000d04035001c42e4404140d48450404010401d000094403c9494905414503104521b894440e5026621101080540440725003039003410081400342c080c5000e10354460400030320240c1044a40c0320745007018403641080d40c0c10140d09000003140a900c0c280c00038001d0030a40f00c8500c100600b0006e11082a100404640c01d04042c0b004000c8001b40802c41030364003100a001c2562110011503801280c41c8118034194 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 699765287 1250 699764037 699764041
    0x30c05060d0902060a03050708010f0b07061104150903021306050918030d02041d09061902091903060f14070c0201050906090405100906060f0f12060f1e0b030f 70
    0x200d03004006107041c1204420101d0041c030300b900019a00d030011040e1350007080d141c1c01080441940481000d01418a540c002d1640314105440c0e03c005000340c1e0002840d495039140b603444139080700d00944004100505200ca50300d441c40c0c02c000c000c0c83c8984001ca00410a440740b10840d90054004c00d800c0e01e1006c0e1140c45540d5610380c041c10311028a0201d0040d90008201e648050009400240084e04000c500703264686401101d0011194009040c40c960f0b4010b002880031440d034080c171001e405068900c015841d0050b000010b680c62260002c1600c41502c01c1000108200702900400100710340d045041090000300c3c0310000030400c1c211442d000148840c1c1000c001136000d07401038200d980c0c01030302744c904081d030038400315045a0f01070b94a8143c2c0e410040c010004004c03140a01c1c000ba02c07451032b10710030014448001801c000c00750314050080c000c4080719000030035016401a0014501066008105650f4408069062400103c0a002d01007581c60104030800140c0c2100d014141c180d0102c001a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 699766537 1250 699765287 699765289
    0x901060b070b0a140a0b031203060a0509040302030f19030e0c0306061903080703110d170115120507080a0f020903030d05130c0b190201050402031e03090a08010b0118030c05 76
    0x4000201040b041c00d98136202130301511100c1904512401004030b00003411042841014076058520b403000c11206010000c1180c0350303e4481c94107003119020341d410031450310740f032600707074214094600c0340709030f5403004903544058000e5412026450039140e20100000000c88142580720700314042200e40650012010484600740344d440d404a40d00341d0405141000d44035610010781d58028242030740000d2007449001e580600600009417149164140310402ca86016114201c6190500c40d42c0042d5000e004040e8140380104080307400c454001c181041320b0300d8450780181c0404015207464404a1a00c01500c1c9001e02c184210b41302c03070f48001c000b542810707407040500025101c01066034282c011461103007400a2006200300001d4258000c40c10703140d50041c201e0b803c00d0720000110000f160705050078040580c81c0482c0c164852001c2c0d0000f60344401b44c04030781c40d103580304109045401c000740101c001109070066001c80d10690f801da031a8000601e8206c03c2c601d81f040e03907000103044401518020445 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 699767787 1250 699766537 699766553
    0x80a050a2406090c0e06070b0601082206061814061905030f030301090b09010b070204090203161d16080c0c01090213020919080a020105160c0303020a0b0901060b07 72
    0x4a50407000501c1072030500c0c441c185064804a501c80030941d91119a849249500120329884901046d5211030030041d03a610b03406100407016124605000d203050200e0b030500001c5140e06070700c402808a52242c420b0511f800d10081c0414460004204200b03040044041a140290104244032a480402035280c00c0100002c1d00820341c17000d5112100000f0000e2035840a108002050101e0304c00386403203601d008040c100b0b03148940305062040645070300501c03900b007410040d1940250150340000d40a0480c1c801309241103402081c10744004107040c400070b900b100d080043c0307000c06500c8009560680b182c1c4070000003180c1040c8200c01280403140024020599103005d481c2c003150680c00410351100c03603000b083c520000740c2902040550000380080080c00c1568a8a482907240c01004800324070706051700380c4886441900a040100004440062110107500c1102d46500300c00007071a915030f01c0ca0065920140b03400103c415482d244009407200c0018420981103400c2c4064880c500865540c4400e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 699769037 1250 699767787 699767813
    0x50c0c060703020c0d0e0f04061d01080705010c08071713090b0402070f0f210906110a0c09020f040902041410030e0d031d0607031505030c0d0b13050d05070309080a050a 74
    0x90822070001040b11030348c1d11030081c200100480b945118410305840400352961030b050700000c1ca141e0040b5020031044c1d9000840350441500f000c0107688130002072038411540526a804280b00c8100818050040041841c00c1c0049650004080046a00c13510900c803d90164003400703040018821200004248491110300340d4512640c4182e01c038244043c0000340d86901080d020340040c0718000706000b030942204205c081c203841c51000300201c00d0540d6944603041d000c0d001c0c00c0b0013540c02062040500e50711605880c0604074800c1309540320f03034a0312072100d0215176094410384500350929044c24500d009110b840806154000509810062048203034090a424054038403840420164a0102d0a0901425025400981c0c01080c8944080703e1041c0c0280c25811191003500802025a41d41c3c0c0d481c15100d400592140302e44c0305940e20301214100b010300000c0050200c4c0160f1481c85002030340207000f001d08030700c0398407034503c2c0540340c0d5802c540d101080340009103290300944002c8046507001c48502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 699770287 1250 699769037 699769039
    0x1b02131107120305010e091501050415090207110f1f030c0903060c09080618030712090b0a0c0605150102060f0a0b0307080337050c0a0204050c0c060703020c0d0e 71
    0x7890240c035075507409610804610288006651070300140300c102040d1100c542c005030210f008004000351619003404250043c8205031117a0b0350b5105002400311901002001401511011911004942411036001d46031220440c4200803810181000d40761644550b0390000c1c801d07038508440c060104040d8020841c070890b034814820103a400200080c2c060082c140c881d0040d6407840141c030710745100d081c82c00b103018252040728404800c03540c0300d14100005071090715070001c01c0d210380790b1901042901d00113550380210001e0b030b00000ea44441c090300f00f6080c1003094407800f820041ca50b00c0c5000d030181a040c9114a0b8016003012001c1846d100540709126003000c05845e0014003120000d002900c3c056046e4002da201760004a50b84035114000003c80c10f58481d181000130058281c66490f0f142e0043d004000d40034080045503000041e034081001094666004e0010801c80c00c1c090381e41505500003003030f020b405114030800500703600d2081c001c0d00c6040404030003c10544811800070355244000d00042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 699771537 1250 699770287 699770321
    0x1506020a05060f1e0114040f0204051c06020f0412110102160311120304090f14010b030f071b0c140109142b0f1709060406140910020105071b0213 64
    0x510380d401329800d5141c020245592811000c01805052000359540308001c841d056106220800c81c3e5118982e6207550380304e4001170240291424034265000307008013500c7c0340313035080003280120350000e00c51142504e490058606004983c000001207a4031404803c680000c00301c1044208000b030341302102c0ca81c801400800100d055003440c40f415185d90400d40c4a403090700e4440c4a1540c04081e0740c840c104821101c02902c05803981440c0d080304481c8409401b00302c103a001000082c941d184101c0003a001e083d5001d82c0c0f10740104036814055034030f80c40c5000c0ea03440300300c0740514a000d541c02041001c0c120340140403142e80c0c41e0380764010000302c445001d6842c08404010f844580c00302d0f04001c200d8102901c00d601c2181c400e1405c0c1013040380d102c00401c10010300881080a1003140d90344400399400c0710920701d003400c0308031016550310b00b5601442d10101c0d04164080b0300c1c170b00500d0b01904140d200d034107240e49602210a1203400f1650b00795480784e0180d005070100c00362031304003001078002000c080112441c1b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 699772787 1250 699771537 699771571
    0x14060702121b0105090601051203030c030714131e06050a140f07020301051906054c02010c1101021303080309010b06070804050a050906060a1116091506020a05060f 72
    0x2c16429500d00700c0d200c40f10f40c1c2008005208501c2d00c00003030383c01104403000450643c508034440b9140341c4006002001802030200b80a9010601c44040b50150b94400c0d402e07520045e070740e01c00c0c0440c200c50010b000a80d500700303141c0840d61f00d104601360788a209803940d4941501d000c8440c2001d40b94089400036801c0c81d0108141e0740545c40c01d01520340506100c8244104038032200c9110130490342c00d500300505c104428100c0f801648650b800041420300441c0031101d080000c244103041c0c0902221058450040c50160f0300501601035215a8200c41d498542d8401c510b11407a001e0b08034400e040984201605d0380c0402d00110360207001850b80100440000035803c0c58050000d142030304141c50894040c240043d09000504100c81c000004000a43e110000703421308000041d0540611003246040000c00c9110303000c6d5010030003036451a05e8039021a048a161136010910103844103a4441d040c49100c90300010f178503032000602c0d400c42c54000c0050441c40c1c442c48409a6a0080600066056124140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 699774037 1250 699772787 699772837
    0xa0609020a0e0a060906050403030302090414041b0e0105011704051e100c080c030c030a0b060d020405150702033d02070b0f3d0609031406070212 64
    0x4018207152845864402c007201e1401d042200219280d08030404200c0d001604214158001040d241600d50604000d0380360076541d004900240a00c03400501442c20000912060207195045801d1484d150403603004080c0d107500c900c2008920030b2080500040443d0120703403041b00c05081e0645c0207403048040c0c60801e210a00b440348000203a200d90f054030340041c000381d942500075108603000202135042c075024030f182c003c50913011404000c140c035442c8074000001802c3c0c41c9803940200c42c078100050609440e200c0c80c0503020b0080d00640501c5004d8007000c40c61411550810701a203000c90b500030002c0000510740c7c0113034070141c0807031400040609041c590200c0341090809198400e05030410006845a91a04216500761000b520024443c1c400340c0501001b0080e80c2c0078000074004002880b2494075600c2407090b80401d41c601c4044004110f24004038000d03a03c203181008030381c040c41c901203413042c49100f101d031980e906458500250380300083c0d8600300303031214005d40701151810628130070548541c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 699775287 1250 699774037 699774041
    0x120712080c06011508070e06030730050907120203030a031512030206070e0618090910020c060f0f0c040303031805010207110102011d0a02040b0a0f0906080606010804030c02090a0609 80
    0x1c3c00c140724082c0c828071303030b260480c1d481030469070f101c8000e14040e10401d4250b80810040d20020f0100007c008001840d0080c10070400346000414000c1d00d0280560400c02901030000c01e001e0f213014029005803100001d0740322080560030205038008011394500210b051f010350040410405190b080300c0c05000008864892021b1845c0c0c85000390041d11241c41c0c46a4010301e010707240d20410f8410070b0148601903454500c2e890700307802e80c40103480b0004651036080b0881c2c50400a400201d072110700000c1c3c440e901410106199000e0040c88401103015106c00c1c030b5850544000300c40000200000740420804a8843e0f0880e81207500411980300c400411a1584c030b09a0b808404242c80145107600c2410350303964244540c11020b11030340300d250058601101c0b9551509640b40019108075160721200c2403d03a25803801702d0082102e008022005659040380c0000780c4081e10480405008030400a150765024643e000d1040e6459a40c1d41c48208a40d801c1000303483c1d001e00210015070342d6481c00703c1d100c0c00c24 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 699776537 1250 699775287 699775289
    0xa0e07030c02010615020c0409030201020c120711030c1804060609051303110d0504091508070f1404020f0d1a09090f0c03011a100201090c0b0d0506120712080c0601 72
    0x155400705405601d8200079003910f0311a4440d18103103810100b00403550f50b001c00c511689200894000c98089942d0404a019004020510740180100d003a8200300d41d006200a00400f4403903940b900c0985c02e01400c06841d522075204540d00f29001074140c0c0b40311604420300756071283c4201c800080c040c0e100d0307214404842d0f045402d8520740b16002030540515401001c2c0321024459031004000700141100002c2240c00341e8440c525125803120301c2d03401c01d0142c50360a00090140e55003201c0310030b6078a40303041038080d403644202e01c00300f03079481101c402d80d081a0089401403101550850310f041c485a0300000141481c410382000c181c0d81604100072a03550320109401a003240c0000c1068a81c0d020103a801c0480207111148280c0c034240303154442544e09540d42c0700700c242c01c50781d10140d403640ca081680541203405000b07009455601010400110b05400351034181c42500042041e07656100a00210070b0b40200d806c1c240d6800b11a00300915010410340c0b030507030b9100b1040d49051901403e417540c40c19500b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 699777787 1250 699776537 699776551
    0x4030f120c0e04051b0a03090f30020c06040e0702030d09061506030506030c040e0709090b10090902090c090111030f030a051f060e180a0e100207200a0e 67
    0x10300c0084806190034043c15070059a4007024000c00301c945c4021600c2842030200f2001031546402c1d40c2c07000e010450004404642e0002c00c001080d0000d40d4403481c12076000179848800c111121620703101030344001000300320380101501007450242820031044404d64010315040840c030003000031104101e494051290520b21074900410040b813030080250301403903650040400c041c41d0004005503503600060f9041c0c2c040007034800003076600720f0f8186141003101e1500080621030030074040e0340130880c03040081886160300a80ba8060103403502c1e01c20040c1c0b1400c00001e5400002074000c51015189207005000b80c12050602c1c11014040083c62400e6411502d9040b03503041c004002c100120f113840c0502607105040d00c04c40749a40e0642c0d941c84c5511007680c001c000400130740d00c61280b40c42c9c85400c2000c1c10030142542181080c60b1250185000d004040c0c4c0c071301c1c041d0117040b5910295102600984000c542c3c4004c45d140e540c0c140c69503600301b0924000c04035070b1188100000080c1e85091012003402040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 699779037 1250 699777787 699777797
    0x100b070b18101508010b01080f040305070212210324010302041203180b040308070803220b090f03040f0605090612040c030b1b04031101030920121504030f120c 70
    0x2515090f0750540311a40c4810041d0341005603181c0d07660b074040081c0c1c2c1e024506c004000031a80f1035060464440c01403078002500910340f103a0f4080d11000004100301240e48140d001c145250390400040c91501042c0c504c410440e080c41d0341200040d11000000800c081e062400500381503a803201000110065042640440d00400c41401a2400d04009802414101c404903140074a1680c1d6030740b140c0f0801c440038020f20400300c0420120802031480c031030881315a01108080c40c0040c03c0c10261800150f4900840c0e1180d0045048070314004004e03101114004d10000245a10b001d000f80c03101d41c0700c2403509a0200c000c1003005807058160b582c5078001c5008032800f409140c21450709104980000d0710030840801d6100100103d40c409900310f8017600e90000b10140d48010020050300940f00c041c2d0300820b442c0e0b0201402d4444426100b000c20341c800d003203d1103001d1741d1898048070348030351504202149040c0240700250100c1d004403203030380c803096070303803514406191002c42c1e5801121022304945001507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 699780287 1250 699779037 699779051
    0x210207110a031e080d09060e0c100906030915020a0806032811060d09110f011704030e01200304060306060201020c0a061116110405100b070b1810 64
    0x10a0a14480100c03000646551103000c0c00c40d11041c031040c058080a1520240300224031007000130402c240c031700d1703254440000d1014100900e8150013800400d0240c800d2480b65104508241c070700340a0300c1102e00351039124480900c0c14400114081d000701d004c1030b107600a8503e400303403201c0c44034401007110800b40c0d030341ca20490608508150070401b030b1814070400b0841005140404942d07002a2041255200c43c82140800f90361010644c14018509052061440e00383c4a10900404006c44901d210003110b160302c00f0140000151801c0d04c0c00703101c0c0c0041c07030340d220300060009000300090300d1108014184a080100750001c16032920002205010594001050070004190180a044080c00307590000307600f03100e00160800e640303107924440585100d03111860344141c84101400c941c24140e1411900110100904009141405900059015501d0708002510004000900d60155100301d00c0180c9083c445803140c0740c0000f000390030354090982c980039680140c102000751851039580340318042210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 699781537 1250 699780287 699780293
    0xe060a0b13030c050d030206011e181a120a140a0f12120204080318060d09081c0e0a0f03050d0e0c0306150d020103150306060b030a060909020d0f0201210207 69
    0x5800d580424029400c0030110000240c0100348141994000b084050300015640860004001e07950710000e031040446009010521064000e41c40713300072440001c82000030720b010300020385950011010941c1104d103024001844807a00030701c0c00825803040b24242002a102c0c0b00204400640846030030f800c0300084082c082d000701042e9890341e81c20000710f080c030f4a04542280c59108444264040281c21401d4a541d0b50303c6000380c942c407950600c000c000c4000b640c0f9000035294000790901c81106841022450b440e0403d00858583e82c2402c4054103043d0f086646a80115241c00421411322000f400b008049107030a2141e40c00c4031204000509000c1c804000303150130004003801034901c0042e04084040b0f55220124096000d075828600002c900c000c10004030a048102e8000030a040e0410f48001001403030040594001d10000c402000241e40d42c4401c00216080804001c6d00100110340038004150800904a011030040c10442c613881203201513001d14180e180d06514150b0742c041886024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 699782787 1250 699781537 699781553
    0xd141602070e0123150c0d02010522020111070305010c05040806010f080a08031e0708041101020105040203120c012003090712020a050103020d0b0907050a110f0a26030702011a060a08010e060a0b1303 87
    0x100b1080300f5400400d0340c5a4860180f080c6a01c4c4001cdc1c1400b940d01c1d019a40c04c20200100e600858010b0020010031028100050059010348260300c8a40b003844008500c48692017441400ca078100300090484843c0341d510000740ea0002055490340c1406001581c0826142078444c5101c1c180c1c0c0c0d561000b10b880c040c50f00107007002808984c10304680c581130030040161030004403021a00078013050f140d1183d40d00d0342c2d0036015191543c20f4074a40400c2845043d6203004030800b4502450000c02a1150a80c4900d42030342001008c0318060f5000080344001c000a5000358018203a01004200119079031180300c01142c42041e05840f840001500014484032940d840130740c4502587e0880080c03d003000403030100c545e5030702055201800d4458020f0200090034040c0c010200b441d0102c0c11703015100c2c41c00460107402480c0c842c04c0c5846c80201204e210000345002c808407104820251101c1440c0c2c0d003041c1c251410070f08020030b50ba8110b1803140002c00c2d00b801c0e0310f02628411401620b03004100d4198541210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 699784037 1250 699782787 699782791
    0x1112110090603080a0f18030308090c062a06070203030604020706090506040516050a06020c0418051f0f0203010e0a09080c070e01050f01030204030203060c0d141602070e0123150c0d020105 83
    0x81000807c05000006511681d04041143e41501c4c0c4110147c40301d5120707500300303501d00d9001c5910240010700407000740008880c2c1e212407468540440c01c000c0c14400904e0b210907049410700c00680081000502c4c0d0f10341617001d0b2140c0ba00943c40002c46115555815181c040181d03000e8070386a114542c08161980c0003441d91024100c00d07140180880d141a1000c0c0d550b0b120741340c1043c1f1454545010005083c6044440815039402c401110900032002511468801f0340c481040d81d99802c0000500d000009402240d040b20340002d1a0112603940c1c0760110300a00d95807201319902a001c1103807405030031017004604080c0560046541351940340c41c040040032021180b40505150040c0004c101594000c11003503409281150f2059481c10000e40510040010410569101c80c4d05410f0100056140f00b004103180016000c5440d0b00344c84d1044046192024447c08020441551646050f4401020300480502e8007401084486a51318003411154000c0700081d1041c0e4440d8202820b4103609000301c2e5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 699785287 1250 699784037 699784067
    0x11010e0c1003110918180d09060e1206010f090b0301050402090106050f040b1c0c11032b0903020c01180b03010918020904060e01112110090603080a 65
    0x440c0c508008408106a03540c0200d44a050543e01e01c15a2120800c040c100c400d80003004004420601c4000040e99000c0800d44030395024951140010090b84c80000341d00c8520945621600c2c80341e890f201c0704a0b9020264007403180c01408242002c0d0f404a010000c00c1d019048543c2d100900e181030420340400c4650301151140729038142418040961640c51b001810350303825182c031540c0c42246080a1881d8411540031449100703000403800b011100e002020306510746884000d00820f40140401c85103508a00d680c401150010051141011500c1140d02c5951142ca240c40207840100110402241c010351400d0b130143e0090350b4500d82ca903074490f58000d00184291000841141003040010684c0014040c0d900da40c1c0d940e1034000c0c640300514041031080c65004100c4541480d02d458141c0107442c1c600a0200a90300b031401070310410484034195490442e0681010001038111000c050302c02e940a44100c080e030350824030100d07141719140111000f5500500c42c00307036a4010503000034402c40303145280c2c1c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 699786537 1250 699785287 699785293
    0xd0f0608250e06031c02071404090b0105090a06031b0603050702030f0406050901030902060a0905040c17160309150204030510020304030516050313080a0209070e0901091a1011010e 79
    0x3000c0c012060040840079100511400c16403961410042440e0042082c4207017034030605e40ca810492281d00292120580da114011443d04c4482282448161601504000e0011503140014401406d0030f01c4e4150b8000c1d05e800340860b0749550303502c40710882a1a03000c90721134084995814000e19800d402082e820408900c019403400240410f2285103008600401040040009000000360b20a401800398560020b026039034a4500140143c400134062141c140103500300111420100e0003043e09404452002c150060560368100b40100480101480c0f2410700d56600d0000300807405102803402081e841c40c40044c0e9032070840c1000c81c40c041040010740388407801041003000003070b0f20905542e000130f1040040f1180c4074482c03810a045024a00e50003030084600100000e0305500003c080341c440d4026504080c5944401108907500420441ea40b5000011a030040145682e01e60000e010600302d034074107003420001c074000660011440940800052810141780361481028490124503021640003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 699787787 1250 699786537 699786583
    0x415050405010f080606070b070509010f081e04140102040e0a05090604030e130b06030c0702010e06031509040507050306100303110601051e061e070b010b180d0204020d0f0608 77
    0x281444650f045207010001d842001c42c03120703142c0f08261907070f659014440c444a4640180010480e80000402c103000a41c05602100100c1c00f80c0025030184002c2480345816210030f5010504190000c4e000f101c0006814510603003c2d6001c0c4080c2c005412148054000303810511766101c10740350701400160f2076070400c40034400026000100f5243e10b4800751001c0307488400014410740200980009142c01000000030031501203038400045c8001c0f803003601e840c250091008207002041c001102c642209590b140c4c2c4402c4545005012640c2c0300c0d10840884a82c0742e00c0e0030202e42820002d49816204458545083c010990481e000c001c60313808083c0100f100d0341c5428002801780c04403900034280610014420079094642104a99004c0707803991603041c0800e0143c0c203003210350784982e02c181e0300140d20301d0005c0764a501c41c03811554206441011468450444820841284c140c07130000c80c2c0c859070800c0703607001402c05801030300700e86400000002851840c0c040c015050a1000040039401c0c4101c0c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 699789037 1250 699787787 699787789
    0x40e010b03012402031e04090e160504020715090305070b0a18020f0a050a1d0711120306040207020d0b0a0e01020a12110c0601090c09060c0305090f1c080415050405 72
    0x8035000c508061090620201c84401d03001381d08621038a003c2da01c0c0e06601d00e1580c6602c260440003441101c14464041000c00514820a40c43e00d001048001d18100461001c001d14035240d00580a41401500245919105010885d040310b0080e802140400d10104013401400755120101d607000c10015001d001d5402100b00c3c0b0038011020380b900030720078082543d43e103c081d20343c0c0c08008081c0602500400340103880d0b00d40701e905c80244225800344000442e00044481b03208241140c04c1e170704000020660281803420b210515003005004a40180d400e102c02c5015a60b0030590103001d41c040d908803401810502505400e8512002111209030f0040000200e02130340071480440300420320000180414404081c02842e100d000b0807411148103500c00070891002640c41101d0400140d15040c5455952b40d0040c4c40e82c0000078009004590280075056203820102e05c010003906008294484070b000c2c8840d01c402a014100094400c440081001e108004011161088400d801e0410600f41442d000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 699790287 1250 699789037 699789059
    0x61805071d0d0f05030f0f030906181906021e09040609021809060d230d090b0304030f020f0708070501230f07030e0604090c0828090c0806010b040e010b0301 69
    0x54001405801480303d0716040c4542802583c21404030042d034139a89182040c1a007175070350400d0302d10742c2c02800b500c40802d0b5405402101404100300000c003a18030030b603401c0c0c5090030031078070b08401392080b40d0200104140c0b540642c01c13521003480e1404410740c030384a40205100072a401e940282c0302d400c0c0304120f100341c10598880102d400e058100d0f41c0c9003040d070b96a00801c80b40880d000000b4405400d82200c0c40070b1401d1030321a803600001d03280403a130340600c5a903011030701c81c20a4413a0b106108400c0022901280c400c000700c481c0c0c1001401281e1048441750041071815800340e000306559004500d0500256a01c040b01c000c030901181c60b2104d4002030f034084441075104441500403d40000100d15040500a507480341c200000242941c0d00c859231101410701a0070030150040000e0031040009102c012106100702c862850f11822880141e00045107000030700301e2100540b10410301200000345880100300071406010780a16041e110f40c80c01417031068000040e0807420a00500b4401404944010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 699791537 1250 699790287 699790309
    0x1050106090e0f0606090d140303040309150302040605070803070201090210112118011211090103140727121110020a0305030c13050301151707060c021003061805071d 73
    0x11141a5007c01082c81c0890300c0c42e60076080c405150001000300018140c028003c4012103504441c8540c1000d1031030030481c202c0c4218000c2c040451401e04c0000b01007840c0b24040c503440a0341c0c1c0000a850310060300001e9150720040d40700f50010302056142074018505200703108000040386600800700e40c46850300401c1e03003d0020240d441402a5444c0c010316845541034000381601e80c5003c103c0040380f8134094038240d02040e20503010078100b100005520001c42610362140030a59642000380c0e030b4100a41d041405940203405d10060403620108809a00040c410700b141d1003200045140d0b4162010b1110708031100d9030700c40554101280d0100400c2e0820201c1781c3c08850190340360b07583c540741c24125282c02e40d65000907070158640304500b90546021210700040d03070140481c0000b40011381e10543c0d88ca0415014001c002032070340074510014280720311650840b8800c0d09000c0742d801c0c2c03110101a4500f0036421001c400310f0b1180306024a50740c20126200880d0300c0c41c19000105044c05010031050411 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 699792787 1250 699791537 699791539
    0x4050607050312041a150d02090403050c0d0309050118020607030503070207170a0302100e0304140d060c020a1a01032d080a020a0b06030109050717070801050106090e0f060609 77
    0x1100c20410506004980c601d2025504100560909043c0340907803a03201c01881d20001c0222001c604644842004c4026101c1c00a01e0f9031000c401030b07800c0c08101c56001c3c0c07041b400e02505024280440c0020701a852820400396400201c010031030070020301307648c0300c3d16046110f8a40c0004400158840a048554940e0542801c1d650b039119244101e103840c00c03035030162104a1024400350350486c00400c43e2203030240a0b5080b121429a042c1503803048407920b003200d42c0700b82d02c1000300b088200c01210b41407042140040828110010f140c0354581a036110700104001604080003400820440444003c0050503017404452250304654454805001c0c140c520301d000601d090361801c3d0000c07000c1203c8203c550010805031200c80541d0302075910202d440e8211080c4060100140140c02e0511034490101c3c0c00c180104510703840d11541080e200451910f18446006503040813903452402d000300f80c000e18041e51015106d43c03411819200e250409025400c09040c0c032414003007180d0740e1100751698800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 699794037 1250 699792787 699792799
    0x5150f04140f070b0d0b03010e0c100e120a030206010608090d08130501091209060c020a090b1f022d1e030c100e0c06160f1104050a0c0207090902060405 67
    0x100c1c00500034604501002003007460b1040c0000495084c010001400b1444404881400354003001070806090b9068507190707241c5c0d90b014551900caa880e2180d080e030480581420001c902050f4580800c1881c5030a20f0303051140d501000445041580c108401401004076281c0075420b820914941516440e4241d400d0b001c2003c88004100203601100e82c6007216980038000300300840161420710201c200003a404000f10b001c401c0009200303402007800003402c50303000f8244080700b4146146600200b890b0f030702c1d03503800c108040012040008032105100545840d5002415410303601582c91441c49a83c0700014210744140301c03d4601d00302c002601018445180707008582005120907a14554012100d05541500c9003001d03008104095030f01440900c0105404d076401d14000c0000c1c428584a45130b135500341c2c0e81000c807100010542c20070380170300081d2040c940640548e84080028098410030354900400729621410070b800c05404111078030007001907060038040d15269800145071070003644a1f4a010310 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 699795287 1250 699794037 699794063
    0xe01090324020408100903080105011103030f09030408030a0903050c0a122402040f0512070e0c0a090e0703021819030206130e0106020f100b09060d0f0501110705150f04 74
    0x1076015010b48000e0420790045403040314440da0b03482c024000c1000d0a50100341e05800210f120352003004041e103d0a0800001d5240d41c440000c01480400020400c00b0700d40424003022400100520085c20400015a24284903a04605105003400409400140300303019810080001c82e0a801180340300941003d101302401100807440c411103214928010421440003402061402800401b40d0076100d066695041400b102d0703001d2a504d0515000303211904a0440008480062035002044030042c50714201c1842036403005815010344082d601c40c00800d4022803134101c038100e10816004d103402304903a00305044010765180c142100c00360002030701607a400150f8582140e08400710100400718008084041c0da59054000c0d1a9800381e810380840d8000c07500c454040d885c035400b0b004140d003c000c00c5003506481c0c640800800c40302d044c00803200e8040c4020300c0030200d5005c0c402c556459043c03000386030f40c800082c50100e04040b0040c04d01140c0089660602c0310302c4040e0004036610507405000241c242c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 699796537 1250 699795287 699795353
    0x70e3d0e0601142d13031202120d0516170a1a0918060c090901051c0606060305090c030111030406020702030f06070e0103050f04020d061112160e010903 67
    0x45030300355080403003c0c0b00002c001c80050040e880d002000c2e400d0390741490451207418140d032054861584c0c443c00c1e5440100040c0041901e02a51061062450044459a841510101400c0c2d04070002d0070304810740d2407042042c0c5200c0e040b060b01c0c098145152a40200003d214109507001020340f0340c2003c02e41d81d0103014800260f06440e800840d200502c14451480c1074804400980d07100c00082c0c025000d0380000c144030f00e820f84290fa000040043c0400303040e0382070105000411200e0303141c400003a40d140103e600442d580d8420070010b0400395034041b40e01d01d40404058a041c01d10140070b4000e80c50800030b401c00030b00340741c29030360000d90101000d83e0303500e80c500000303241508244101689008140c1444407854100e0b41d0f1102840e0203032002e11807a80e030f51043d9580d00c0340403100a5000401130060100141656001580f0720400700c004d10b051110b0840302151aa104650810883c40044224801c0c190004840703d02c4c1c01c02460000005410740e0b41b90b81103690040696a820b40d5090101924 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 699797787 1250 699796537 699796547
    0xc05190809010b190518010305150a090813050a120302100908041701050106080a0203060f091015170f010f03030c08090607110f150f0c070e3d0e0601 66
    0x1d000c03c000c051030140c058806518407003444038440d4038414003901603003c0a6400c8032a0190490360000d0117400b541550f0502086e00ca00d005000e400b0251342c642502000620b90300c041c02c6a40fa03071512030510300f814a0284080c800745500b22030b070745007520080b00b40040c0d0300085403140940c0e4800d001c500f03440340c1c0c6030001c454066500680060444c08900d0281070005600c107074100d42155075100c0250b26210a1b910891005954554101100b8114144d079401d0201c110780c3c010f0901035000380030303964500d4440c0c0f8008592212100040c01300c40444441c100d4070f40c2498108035403000e0319940354034000e9a100f10811600c8000c00740018044a0414003201109494541c2800352056945003510b1078101c82c1050300084241c81942120803200490034103402403820300913549001803030308a03d407140100980180400b40028440c402022807604110040c2d18015800006d002d0484080d5900107014034004040c0c900506914202e4607104100011586080b51801d4a2030086500d5070001219 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 699799037 1250 699797787 699797801
    0xb060403120f020c0d02060a030b1302030c070506090f0c0d0c08030315130e03040b090d200916050403030f111c020f0705130c12050a0504060c0519080901 68
    0x301201d16410402582c2c000e2160703a0740110035400d44a90801000c1009445a90501c2c0a508107d040c0701015042e0b0181d40101c1104500400d4002c0c900150245441030b0ba2007291660025100803a501e820403008108040d081016000035098030650f6540c5180d560100c006410310500307a40070440b040c4240100e41c800a80034005c00e0300c0d40c91804090901201081c124005d014404003002da0907842650321509030b0b9000303144061403405181461807280d5802c02e0707442d035511080140f03080c0c000440d14004560a03030603000443c021134402c4410010b02002c01040038bc5800001c11100c9116548071007124141c070703450b040200300c0d0a00c0140440d0440c83c4031503020724500c200025140540c1a40c0040c0040d81c803954200e034151015000f50f184c841c4134070b120303050300a40311189403005c1002e00d810800c0405501e240551202d0259007490b01034035070a594802c41c070341c0d54109110500c0141d0040e480d4191580c2411423400b8101102d000300409540900000c220040c0d010411403403007900601 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 699800287 1250 699799037 699799043
    0x152102061204050a0b0703090b01150e04090b0601030b032e0b1207080601060908070306020c01020c1f0605060403031d0301110d022d0f030405031201080f12090303040302040b060403 80
    0x1007018507061a03d03507919220560f058030b20220480014040703510134064503503c1f95022003e0341040c4d1904551103003503030b242c0500302d00740500c0300c00c0d0113925101d034403844540a0003510303c04140c0c01d090b0005402c40705007030101402030b000240c500c018400030f103002491a00844441080c2d52100301100c2e0000c0481504650f403001443c210907058010004100c026a6a00800d0b1812660303a04011f071035508151290250b42d40298204001145c11640640205c260f0000054070301a0f103200d0240c2401d004608007030b005140d0700c00c05846034006115040c05818140d61300c914207800c64030003412001080344540c000c00e810705071144040c0c41c2900054001001d0341c0440f40c80b0f8010008900c0a500504545180740409592400e244105181010911220003544929010b0f040103484440e0740010800d86030b5100411040c9c0e004526180d0311030091141ca4003800200102d0071406041c03465202340c0c1c100809003489a48010b9601100f228101c2e0703811500044d601a40002091080c00307aa4005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 699801537 1250 699800287 699800317
    0x93005180a03080a081803041d0a110a090f05010e13090c0305100212090c060a0f020705060412110f130906110a1e080f0106031107020d06020405030115210206 70
    0xd100c2141d0003d02e400d004880744040d09040c103509441310740d92801540b180d91011030380840d00519a49d59030390b429401c8a9000000303d00e00c03089001c042103e9018544440002d406424100401c000c900620300107030000740381c06d80740100f0f940000b40300d5000340c0e48081c20743ca544440041c00c01000601d0440119486030503241c5049035808814020b4002d82400d0700310300c20002c000b03902280b000c40d8070254102c0040c0810306020121100f10740d00c0f6103540306481988a8024049115a11000904000d00c1c41071220741c145002494000c042c61000561a40111800391180109685080c2a0004401601c000140b418914100301010300103aa10820302c207480000c102c202182d21140c00b4202c0035111000d03544140b60078004030343d0506c0454848a1104001005010303691285e0483c101c800015580301e420280c1540004d15150041401211401d80c0050304210a043c20b01503290b10541403806102c5040c03a1010751103180042d00880c00e041c2c04082d280004664500b400c1e038000208032915 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 699802787 1250 699801537 699801547
    0x6040506030a14060712110403080c032704060b1806090103113c030604050a0902060307110c0d030e0d050114150102011a030a03110c04093005180a0308 67
    0x7542c4d180c0d10709039100c0e00040e510780c0412491000c0d90145030358001132a44520701e02440c3d80c035002643e8001c0d0030b4403c0b00340000c1054091807500b080801050303000c80701c4800640c40d44a020017040f0b6a1503031040400c80800c0c8480062412192841801344409541559403180203100403001009111a03850420001240e0520440400c0d9415680324200502400c0c0b00002e040050720a0710030150f90308100102000040c455003000e820103070f00603011681c0458818202d50020300aa001250400000f80303446119055845e02001f000701c0c6164281c50420600119450003007a0180808240340110404c003020000c0013000d510001114001c2e41c150040d50404500198946080142142c01076003400004444107011030310404410000500521400368981e0307055420100541000d5501e0003076450610040d10355010345c0300e201d40b20700c500c110342c0e04001d442c525140d80202e441c9880e40300c002d0450300c03689402404459072001c4194076043d942d20b2550004504142c680c000030035440000c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 699804037 1250 699802787 699802823
    0xd0c0507020f09010e070302130302120d0906030b01020703020127120b0f070917010b130b040e030307171506120406140609010b0901020f03180909011406040506030a 73
    0x5050610700c22221001d80a01000c01c01400c04001e0040d030420b440c0f14408070742228020f0b03004140c0c01c55860115101c19580c1d40004e40f1701001071a205e003250b04640a540b0740e140d4041c0202000c0d100b2070604202d58110000001d580d40380d0b60100905005420403c0c402e103030101214081800c0400e030500c503281d40ca03011603810b0700d680403001b1155056410045821054881025440f44a1039078a00c100940781607560010b041d03a0a003110f01d15561800301d10030f140c0740c8100c0c009034400e180b400490410101002e0204981c0e03403200e07510032074005000703028485a11600d9011000000035095005454080c620725550b40c4040d0304552050300000c0000c00d008121410b148100c2c000c0301e042024254500c034411a962045540f19446010540107101c0200e2800240151050600c100d52180c0407007084240b6650140e080c019001038210008121441c2a01805034400c1c0c1d1000280f040902821a5030540f45c0041c1200d03220380d8946000440701d450800030a25030a801402150308489007203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 699805287 1250 699804037 699804047
    0x241b1110020319020d020604120c3002010203010e0703240f031a06210102040b0423100e0d021201140106120e060f0a090b0405030408011820060d0c 65
    0x4220b11040b215500fa031220707180042010b0400606540150072035640b19a2034909225681c1d40e0481400080c014000100c0d0b00303007030f40c01300c0e07510034041c08010030040d49403e003002288001e10304d085a0040005012460607116030941203001c6040115110314500e8298260403000030f0344598000d8991740000b07500d0034074540d1100b00c1c0e010380076880d0103654801400d55020422144144c2007001e144040c1140c06060340100d0550880900040c00c003605c0b0000c2400c50b0b449903001880f4101180e581e16a00c0c29142c80360651000c040320120402d1106080180594424a142c588500c200c800441d0543d01c1c0c68240d1107040c1031540c020440240e10040c0d03001c0c0c104080c060600051444860400d240f070103845002d010008210042ca0180d0302c8007461018058010b24603070340e03da1a0600100000d0b20b00b11950b014901c528007030350300c0f14103104c040c0d070854480881d0a062842004c1c400e20104070940b0054800c050050360000c00012004081900c44c400c03490452000380c038010b02d544c041e03a401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 699806537 1250 699805287 699805297
    0x312060405181c090503190b0601050a0918060512100c0f2a05011119090e01050609030a08030a2721110106030c241b11100203 56
    0x212410007030341d259244909120b0a6400c201e46050b40f028031450108030a1501050864034589000142151204042803c00240000d00412000140d802104104000c070246601107020b1800c40e01300f0b4400301d401080960700d44500301100d20360403044a5401c141c2c0d08284058940540408940e00c4066036059642c00c07602003082000d850941c080c000d8070320031621311b107520015a4500090003140401c0d40360304001c0032072048013250302c440c1c0403000a030280241502c02c0110700c051515528060306c03504104203088840c00810884040c2404030a07002c01005041d036070251003d58071048400b0200780f805100b41030160443d1008000c00800e807049410940f40d030801d0980b2961000285000300401c0c018511004201e04030100181c0303400c00f00711044020420092400800d14514158980d003120307402e4105603007138401114140502004068040004003808006c4210f1300d40c0542d00802c003030529031140107007101001e4046c052003010401040f4105008000e001c800c12000400b80d629444 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 699807787 1250 699806537 699806539
    0x102040e07050c061308090f12070605130906060207031101031e0b0f0102010e0d0305091f0218031c0806040b061c0b0a030f110429010e040213170f031206 68
    0x440f0005520311503000440080070b075110006901f05694030080044c05180304d00c596420115206510320390300410000361004244a4a4856490051021320314105115410007203605080c06010044684d0001b40344d421240c208128a40d014080001203020b0703d0403030886181c4d40499000500100c14950290501410459007030725410400c5005a00362200212504840d410100a40340d0a902035005254004040020342c0c058000d40c5d001c6080a48000000d80c01665002c03c00408050030700e40002c0c8980000c40080c0f044030307000c0c58000389620b049003100040101e291f010030785070346481d080006001c0b002000d0070340b24003c0d070307001e4000300d00c0711030f04000c555041c140c0c41030b02410724280010503240c0041c1080034040c4a91100b05403440400c416541207981c0d02500c0b40c501c0c180b0302190310320766089030701c0d00039030b041c0320300010700c042c41c1d02086601c075510420880c0000d1000e006040125030b04480f40c2c140c1060600711941c10400b110040d090340d8000000c0a54610800500552007a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 699809037 1250 699807787 699807793
    0xb030709051309170a0207180c03060e0f150402131715090601152f0d050c030a0c0f06050405100e010b0a050105280f230304140102040e07050c 63
    0x107402c00c10001078401815000e004058108145a902000c0c0402850320038050f00448074120350361005100d400d52150380b81039a15568001500c451641405108014844103031840b101d8100540b010000c1800a4401c41c0c1e100302e806000246a00d85da01070390b0407921301c50040c4803010340d10381c0c903003021401c10b1601301c2c114020380004040e07441110300e48c140a01401c02c002c0400f84c0c200720001540000420038401801000800740b003007904007001c0c01c00d00800340440a41c1b130380a44030300e16140131600d005000600100b030010250040f000420b40ba40b4100b2032030954101c1d07120b400c0984200e080ca4002400c40c03810300d0200001c0c0140000c950341400d0f00081c0c20400300c0c0940142c28200c2e0440c28806911000d0840100020340c420303006001001d508a40c00b1b03100c8014029400781e44401200140003140300e400b070080c070003900300007002400000c5507602d00909086e14880b19151100a0008162900d182014421700348258151005003640e0035440800d03051200c001741070741c0c000c100720900c0e600c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 699810287 1250 699809037 699809059
    0x6020708010b1f05160206282115030b07021e03090d24090507081212071b0c080a110d02010905060906070507030602030f01050d0507060c03090b03070905 68
    0x100b050038460344103d8107402d2080594546032422159540308608410f103e810071052540540c6e40d01c00203050761030055042c8000c124200c05801069041c001c0842d09000c0b003040046c400745800e01c044030b00e1844191300020000d0540d050b980d54051240c0018100725040020040c140b0f0300020240d0112011185c50b4812031203660405039240708995005800510480d00d0a000621000d126035810042510300c900004008481c0400c40f5107c201c1070302c1030351180da010400c0c0383c2c2c10701c900c2107910700000c184e03450040740c2e074004410000040e1080041041034000c070465011440b00c0d1605d0b6641c81854842801d1740ca0900d9559442503030800e50b203014440040f030180b4501403001003030b26503040c0c5400740814544420020150000c09016401c000c04002c1680000c500307000d00f802031403042d00700586a0420740c2d02408000f50581100c0e0140b816980c0e0000826000501d02017251403910300401c08008915044520301069401040300400100500500303c1d000b1051034255002550343c1c001003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 699811537 1250 699810287 699810289
    0xb0414090f0c030616082e060e061305090c070b0103030906080c21040501021308072303031e0d140a110f0714250317031608060d020a06020708010b 65
    0xd0905481c000088503101c54040742c4d4a0003218216032101c80c2005c14200e07a0941e56401d286c0c1c0d4241e801641c06086407c10070321003541c110032205040001503900c4c80c00c001d644d004941c854803450055a22842441d400a01000800e104560311203900282c8100256902c0ca400b5118500b24040c4502044000300020249141d04007560f50035001300d4075444507060101b6040988400c05407041e80c07195020400c00c014007502d2014007004058001c02040c9103450180c400c4040c041840c14030b000403801d000307600c202da540041a68108400040800000030138041049198822501e0307a040450814041c042491091b45120b4480d4002020500070b181c01605000010700c40d110031640c00f50800e21900c0c012504010300e02006107215412180d00c1e5110304240b0440e84041048107101181e014000d20070007180e0450248408041141c290441c1002e001c0d82c000201410350720b01c00c014004001803110358031912500e016540240801e440349854000080d20740380d26004140c080d600b4000c00c1041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 699812787 1250 699811537 699811543
    0x30b0a03140a0c1508012601020c07080f030a080c1303020d111c170f070606080303060a060c17030a09020d152904020a02160803130e040b01090b0414090f0c03 70
    0x1344803507954590040c2e0901c01000340541e140c02c0401010610728203883e00000c024401000700d1412440282030103460040b07140d190207a10b210f008075a4005111284a44c2e410003111a0008180b501c11916032120201c41211544603134000b0354014440d0224000340028641440189003003a284206031000340c030380451118000d200000c2441010503562240e1150f664050803148012004251900210f921200140d0b841034000b03c6194000100b0300c002480d0410400c2c004040c1404c040c3c2407048180c80d44444100410076081d480030002001404a84556000e5030300f140e4000c00d00d06169016082c6000c500b49215441094685031951291496248400d400e41056040424a035004441301c00c0c031020303404c481449400c2d4499500001121001041d164003d130410303000958481e1845060050040c1503a4410081c00300620148404215064a00f6040d141102c40208140c001007010400070703d01409040c855810803024424500f4010501c01204038540d030484810000c88000c041d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 699814037 1250 699812787 699812819
    0x120b0112020a050609040e0106080606240a030903110a0c1406040b0301050d05070f0e0402012a110316030317090d0c060c0918020310080606010f030b0a03140a0c 71
    0x2d80264450001c1102d4a09440104014007016201091503d12009030a003510100c6c0c1200c1000c0d001203081020302d04143d8843c084000004206010429241100b4401441112026070405071075944000c241801104580348070b22103501203c1c1c015503142880c2420890700e004000201c100c0103d504e81c0c61802006983c2039903025104a490744c2d00c0c2c40204403107003903803000c00ca42c1400f0308076000440c42c044070303201c1000741801003c100d4689083d1000401181d001c0b071400f005500d02841e21011000390600348803905510100300f14003002400300180c90312035074003070071004080f0b041d001104145d0f11000c40500c1d0321004050800340d844840d0307115290020111204006201c1e00c401c9000300e040d42d00090440d666509210660310b0310f40c2001e03110700c0d03c1e05040c009425000000e01c40c00a140c0203000c0d0007801d541d00a81018105100000c1a03000001c4402c41015102c101d620b055076508400000110b81c032a4641c204860b03000d241944687e00c45400f5101405503003030001d88085041c0d6249 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 699815287 1250 699814037 699814039
    0x330301090f050604062d030209010b0c2415131104090e07050303091309120309030f020d0203041502010b100e0a06030902060417010f050a0501080d05071203051906120b011202 77
    0x4a0468040200050f06c0006d96001e8000040c1001000005d603c58aa01d0b5028080d40d407047c41d07991883d00f1546280801c409032031000c10b2501d140201020032441030441d0040010350700c0c06110402000001c50f4111040d501014603482e100c101c440303100c541401031086400c00e000600405540040c0355484000b9031280d0360301a08100540751240c130300712101c50700302d00d2203801c0003800e030805490f010760b11190500c84070046561001c480c814160081c0c00c01c422094544000c002641c400c80e0004d41f02c0c002d9104060201800c6161240003900070341000c3e001c114081c06d091030346004e09900500c1d100590420a00483d0f45000c0802e030103110303024100b100c5401501c114642031520440840312149488450b0965586010b40d1060a080f8004e0030300680020b1340201d442d5050605907820020340d41c0b10304040c031108204000005407254140c0322288890b0800041e1607451520348a044503011415100603890490003140b0b904400075928030082c00340700742d072000380c2e00e40c0104030841a85000103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 699816537 1250 699815287 699815309
    0x40905030a03090c030503040803131707170102040905101a0a050306011b051509010606020705180403110303040303020403030e1002190606050a0b09120c330301090f05060406 77
    0x29200d11400ba4200c20f481d90720400d1040c0c5207a40d03c0e21040d04580280c1c0080c5000d400005403d0700300100d420b881d5026045080090052151031451240d483e815407003007103e945c6d02d0360409241c202d82075065030300525200505020394a0208581100007143d4040c0401c440002c3d243da0054044142c00d4580502241e01ea1500c1c58858000550f000900030360740b0301c901d42c0b101d0109400110180b21024001c0e1807041000554108103402e1405d5480a4004004550081c03000301b0a80d61a602a5104c10341d4891a0031620b0321a41400c82c0d958030002e02412082c80008140801c141d41030303008004036402542c80141c0c034800b403410801c03503540000c2e0910050b0310080321030000303440b0341c01d07402c121600c0344100060301d40e9600302090090020b40c1c818104680c022803400d055040c9521200c900400150240103800c4000002035060f4a8000410100207504158511405441c1c036030380c802344801005c1ca68aa42e503404114000c1c001d94211041c105080001107070b4103040c40d00602060321220f40c40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 699817787 1250 699816537 699816547
    0x1d0a0f0203091e07090f09020a06050309120c010905030f0a08090a0b0402120c040e01150b0412120c05150403180503100b13060608061e0603060f060d0e0c0f04090503 73
    0x1000c3d40d800d14102e0460f03900c0c000c0e043d0001d0900d04600c294036180b24402000b2a4403c424010000c00c0c200d01d50044040c030004104101e03840b20003007413000201c084004031544920408682a00520071624000d082d0320001807110328500b074200c0a010600750a0f61503819965440f2015070f103030010404001d00c4541074001080c01440c1c000c40e048918200d45048400340c00f007100000b01a1000c0e050143d00d20b9648000708860801d050410720064600c070701c0054a042e15141d0302040c0154010000b50a8100c2c401d000380700603200760720002c81580c0040840315240e0f01014003010301d210550b4220081440018191a160103140c0480c0846030000c01074036254102c031a01074080d00c0c10003100b80d40641100036940b40c02c101ca00c500b001405040d0340b401c8651600d0418400b60310201d84c90000b005c4200d81000d4207e039198021686d000d4010340b011030310510044045481030054910a17483c103820402c408404010008610103035031001c983c268104207403502130000700c4824410142441d001044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 699819037 1250 699817787 699817813
    0x308181c0813020306150a0603050c0906090a030b010b180103230a110c0f120c07031e0602210c090d0f05030412030801091a0102030306010c08041d0a0f020309 70
    0xc0702588a40180640501e118070b9500007814a034003200e80d9020070055a0a020715400d02038020009032405040400040c107040305140454020703414150310a102c000798028036078440803190b00045500035820000395848504000c0301d17811051503a42c15180001011040390b11a014000c0c081da8101f0300c0f101c1c01901c0020802e200c0c28002c0003e0f40303068039407100300204402e8000401001c4d038000080c001401101504508240402d82c6030b41e038500c0305220b40d002240002c20801d089035842560300800002d1304c0d1181c004c1551040b000f401581c408034440c2c030b4a26460705000701e04a2540054000c0d540d0309402d00c1014042d46500a41191920034981c002641814560f9a802e000c0d508032403c0503620340c001c400000701d0003002c90000d8424001006440300741e000b50039089200b084c8054440d1a1103000035680e000c024011030401c2103112150081c028000102d4002c2c0c002804c10310300104031030740c0c130b124844030076654800c0300ca00d0600080c156001c10301c21390380110b00d000c02800600410b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 699820143 1106 699819037 699819047
    0xb0a060501050a0f090906140a0902160b0405070e160243150e01120b0f10030b100807170106051b030f070308181c 51
    0x68140440d030380000940c3c3c00941d06141c90244070080380001c0362580003561001d5049443c026005c2851040e4201d040740d00c8a065508422556031641c014040344214040300800c0d01d40d0483d0800081c80761041d43d900280141c1c116642d10323464000610001e002035800c10700b10601c1c6401d4000271a014030a0321f0700c40300024403d40c803459070001150701045907000208140b002140400d07a2507641c9818010141c000c42100c0c1d070029404042c0a800d60030100e1351980030a10070800d4020f42407840c000d003010302c01d02503d8a6a040c80340f0041c80000750f0910350b030100b8140c9a40441c00c00341c4500940030080c0c001940c5428140c2443c0380c02410b10302655582c4c40c3c00303900c00c0006024260f04413040724030092550b903250031710b00508140d05045003e40d100782d18400350002404810b240d400f007074060017140c1880113031504003404030b03207140e40e20308403504800401132071001e480f00c081c051 = true := by decide +kernel

theorem cover : BRFrame.Cov 699640287 699820143 := by
  have h0 := BRFrame.cov_init 699640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 699640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 699640287 ≤ n) (h2 : n < 699820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
