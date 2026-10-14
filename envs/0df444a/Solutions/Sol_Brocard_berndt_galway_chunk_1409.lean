-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:50:41.958286+00:00
-- url     : https://prove2.me/submissions/0fc6e2d0-7f17-4723-bb7e-da69d73dcc2f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 253237410 ≤ n < 253417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 253238660 1250 253237410 253237417
    0x40c050714281109010e0727030302030c0d030605310e010c0207050312070b0601210207120314040b1b0c0f0d02060705120714030f0411060a0806060f 66
    0x10b5585060452440c015100c40c045401c1d042e42c12001111800c2100d2034407030a00303816125056100415603e80810859015130440f0050100680c1426200b00002d0341500090085109500543d51003092002542c2409075024a501c02c0c54209002407000f41d650080f412652030314080c1c56201001044481342014048828203890603140c01d0220307600080640001c03080380c020740c0032a81d10960780c1045c1a42c900d00c00242d0151000309201d5100000c407040c268981004051510301a41d1810301c04920300008440704071111164005010030402c8429490008400200d05080000402403404103201c002c0007040107003540300381300000d00c0d0030310340070584205510048460382d110700040480c1d5944150f00768040c00c01e44648800b0049161000554911070307a110b98582c1d062074640b0113243c11020000c0e14141c14402c5281c0c8022032000850301452082c504000300700d0050501e0b04001200031a00014180210b800b0098000b80e20307000340b400c68201900390b6416a482c1c016002c0d40f10b2501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 253239910 1250 253238660 253238683
    0xa0b0103060b0a03090606060f052d03010f0801050f040f0b06060d061e090b060a0c050717010f0e03182b03020f100212150406080106080102040303020c040c050714 72
    0x42c004265101c1d65681640000c00f00c5204101c1044000d88030070b01079030b401008100050014400304100c1d0071444c404101c000414002e071482d4909040448042451508260054203080000b0101040565030074080c1d5034118410803c007094504058036188007811401401500c0c04505001040503500c504d0300300c0c0d080c09800b80c0100551511041101842024140f0203000000d9000e030100e11000c043c4030718514030380010a1249400e190100640305954903185c00d9405009000c0002234411410100c1552800300400004040180f19004001c4901e980703031840841c0d00900585110f9a00e058030007081500031100282c0718161814418058041c25090044000c003c20110040640004013034009102c0f120541d5840c40940c51030303404034090428045038928115001c1640d0032801c5100101180001e071001c21590349400c0d14600399007042e80301c00c0d0580c1d40003d080052581c180508008a2811502400725040000004041c0c1c003a41031301601d450207450003035500030800c01c01c084041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 253241160 1250 253239910 253239929
    0x5030702070f080c040b03060105090f0712020f0405101e030f0905010603030906090902090d0b061c051f0213090c0203040317040f0503160e07020c030a080c0f060c030a0b010306 78
    0x42d9201c004440d00c03040b14240040c003a0342401d103581c0300d41c9000704416058600203040b0401c0b0380c0e42c20148110f101c4001d080b4000f84405020300041c444202d0008100812848560650380d51410080c44039a4221051103c100324840170115200411400007809140c65450089000180b1006c0f5500400f40701d00001c00e5586010000000c054021621500305da00c0b03601e502402b10340d907105010591145400300356008581012003000205400b6025070080006000d0044040d946500d1156140c1a4003003038074594880302540c100aa103540b8030f6103002c10203030802e60410300b41c0581e10b401a8032074050a2110358550412044485c0f080007520020b5403c46030900608a00400b40d039002d070f0003400303040a14030f82c0a4001c40c0a050008110006941010303442541c1441c00380840407400d40a86420214001d6482050f402da40c1000301140f01802030b00c6c0c1e03a075030b0b1044140391883c0c814103564000258001c0d13410401a98500d100b034030351124081c0070116040c45511b00403002409160000d0f801d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 253242410 1250 253241160 253241189
    0x901060f0e0405010c1e080c07020913110102240919120801120807030e0604120515091c0f031103090606030c010e100c06020405150c01150b0a0503070207 68
    0x10407503098000d0045010340001c00c90304a9049007180c04600360200280f031030b0702400580ea04180f06030019a0b011805505407401c08042c0e03800560310000030303641c00030741c04c204003116000e10480030014482d00f10309000074000c1d111001c207030003c030600110008031008142e10000c0d248000c1440900d00c4603960400055081c1d1061a01c3c480041d0350004110005012000200c3d145c3c06101c06816450b41100803a801c0c060107607012a0080c0030b18201c207410120500000581051620f54809507500c00e101516203021131140300c0b054080010300b03404483d40102034076581d620241d50f020003900681c0c03034044603d00110b40b0a5020301071030f15440003d8a000010421f40d00ca000c41c44a000c1d91084081c0e4650142803030045a42c41c3d1281100c0da0300850340341c892483e05020b040e107244013134404c1c1c0c070140c1407550702d00000e075551408198402d40701c4000a03102d0315001080c403880040c0c3c0b50000c2120805030522960b8072007405903080310001d00a001002c0340d001e078000c01c610002415400c0c2510700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 253243660 1250 253242410 253242419
    0x2070503070305190207030c14130e030d050c090604060507030314040609110910090209040b150306120106140909010b03071403011d0a02010c0318030303020301030215120a02030901060f 82
    0x8075813010910b0801140d4401d100460f29202081001c11203801c104100311090038200301c00d1000b202d500141d58821000c409a20000e041800b071080e00e101036001031911880d03280d100c102641c1004010803811107007085152000c4c0c1d600e0055030b0503aa030310700c0d0190703c484c41e901c1c051307004000c01e0010b0181000362008200800145800801300309108080c03403104138017084148060040306481c0c910381503c5d0740605002c0d580a6a0240c10840c0008102003550300c050300110f10741451104901148010000401000b0300f041303040a0040b00c0f8810003042014608950101c0d220860801c2900c01d4440c400400e0200c41e0035084200300c204000c05541310540d5a28012020700d201c010103500071b50810103403141746651000e230b2040320740401c0b0103099900740942c01180d610340315503411428803400004100054402c010b1603000785209403001652941180104046002c5401d0105103e590800c040b0b681d8000810f02250800722804c1b0150300c07911003070380490140401d40c10040313414954500c00035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 253244910 1250 253243660 253243667
    0x3030d2c0d0f080403020c0f01140f030a0612031707032306461a041d0103020607170409090515060f2107050603070f030506060a090302090604020705030703 69
    0x115404071500c80315036040020b00e0503500d80e6012580500982c010100822003404c240001800002c0305140640d88078124403085080f542110070300c003040d64004010410521818800c0d00040e04941d0320640c1158a6950000d00000d0040c8000c00206400000700d1004c40c000d03000000080c4400c01c0b40c440700c404290000300301c9502114600c2c491059410041001300c01811260450150404406107110b0781e030044141081d41c2a29000c00030b052084000b40c0c240a040d42c44070002100b4455940d11032030402c1d1810083c00c81c0c205101c40d004100010001070b69010122540d89510440e503880ea083c400041226a010301d60010307010a0900091500f00400450303490400c4400c10341e0f5440c0c545501c024400c03150b4140101a0304840d109201c1c5a01d01c2c0e20040c0b1000c028084402c40e2000742c1c6407408500c1c40d820a0714900e02050714011407044503a05402595884601514150b04100d400300000300168920b11000c0d00404240002ca0301d07a48a40d01201c0d201c0341c0180c2100d584411910b80103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 253246160 1250 253244910 253244923
    0x80901052b05062403060303070c0807060207051f080709031202010603140706090e151f0305070e0a0611070312081f080606060904150b040f050f03030d2c 68
    0x51001d620740700005266140c0b42407000004008003039070149500125000c0340c09030340042c0a40d94103220601c4031400141541d0076600c06091844050070340136141200c0a03103490350982000e44a401d11964520f1802c15a0b1080342d2601603510386440c0f1a1107801080ea2894010381028020301e03554080b003c0c2140e01504207d08a91003011a15200347e03440c01c405440d0a01802a00001111808100300359048218415040041c0030946104403010100181d42c500c0040000c407607034240900301651a94052159590000c442c1c2001c680c0c020a078400035045090074020307501440052031201c01c0c8204200000c4000e10341c028640030140601c6100036184210840c3c3d0f10040d900400c01030580c922011103c04c0480356080006d080b80e849d4242001001c0d04240c6840382c005540d000ba0900c50201112840d00800402400d1662541041d0002c400725500390001c0f805262214095141901c00004071881074040000016250421443c031041d0303404540d05c41d451842418a0020071644c021860 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 253247410 1250 253246160 253246237
    0x60a090221070807050d05030d050c0c0607261608071413050312040b0706090f0803070f0207090902030c210604110103060909030c02120712030c0614060d08090105 72
    0x4413568580d84078108984072a40080003480f0390002d110518101c01260410394001a000200e10308040207078803814941a42150301c140001c690b8805013585881d4041400d4000c031028008001d0307850200e030100700c8100e00c480c2c1c00c8200300d90b0300c0000319900c3c820f600b0941c076580080b403241c0d035030442c0d803020038050b99681c02514030901846032a101943d0883d012101154220400c041c14103030680c896000500303810206031040354000041030300003810440194820300c900e4450441c20210140003d20300103c907000194094070380b215031405030b580003501d401e54071400c135200201007034040050300f2040704221245c0d80d24426441440708015004e503080c03200100a80c0c040020780e41c0c4001c8102070380d400308000f5004c542485135140160503d180c514507179820f41c1041302c501a030703120b15071064841c00c04001d4000580c1500c1410420206015403006400c44060350320b45802c2260004500c0c418104000b44660340002d46007065900600a5070800e201d400b140c47c1001e04110a10016544036460 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 253248660 1250 253247410 253247413
    0x11010213080d0c0c0b0a02071a0a080108030a0c0816240c0302120c09010e0a0902040305010b0d2f03070612050a2007030e040504050706110105060102060a0902210708 73
    0x1801008511415824214503005228001100c0c5801004000380d40000041c404600841c8000300c9d03a04019405030721100c06501c4482d0365100000d03001440c054040e08500403540082140080c0706a1040d428090140c0000d00196954003014008081c10f08500004000c16228030f50300044c3d01207030554000e450503401090000e00c0c0e110070228124403411500b4410840c0440205000380c820b2030140c88000c0041c140320840c84c20480001d03484040e1580051f08041d00024280100642801200d11b6024113840e0340503a421107035110180003100701c60f40c4001c4c130f07087d88002451520300c21148070001000f8050360740035034450304003d20004528941e4112070303023414040794188400303118035503032402203440d4011400c207168640c1c1d40036485483c00350704221520810007415500c1d07110b4640524840e100400380d803450500080d00d46e11045000580e81e900d4034040101591300131407140e5000341740090002d0071021910010b00c12540119411403e036a02e0350780200c100c04001945420b8410031070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 253249910 1250 253248660 253248673
    0x30b040e24070915050c071e080106030213020306061605101404030905040e0f011119090b09220e0a0204200f0d06080d0201050f0106090506070b0402011101021308 72
    0x15a0588031000c0e20342c0c9001400804040200c140c590003408020391880c034020f8076103140700d42a145848800d03000441c041c0569000480040702501c4503200a107001d100900c5003d182d5000038820303078904248403900320b800000103031407a5200800c03150300142201740000400d0311424042d64844030490b18112062030170300840c10725404801418804ca50503602c104407213044c1300a120240010005000c80ca101e20461181000e0080c00360100d00c00e803503054aa00c0305c5404182c2c01405900f01080400d20074030400c1400504500400c8680d5008203440020440c030700303002d91082610408448403140ca02e031819151801034041040803400e8000c58050000c03110340d00421945905149075003030381000802201d0900078000c0040d00b500d14000c5c2c4001003d50303407620400d041040300000d00005035550400c000c1c0c0401303403a43c0301d800742181d841c00d00c03000350500300411074620a0400103058030040708006405c680c801c030710490050311014020764540c0e03000c0d030300061352441c40d000380070082c001c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 253251160 1250 253249910 253249963
    0x310090c09090809280605031b190e0307052106181506120f03040e10050612310309090b03030901110c0406180b0d050d050a030b040e 59
    0x10b00420120a80201c501c0e03280c1036503c42001089061401070070000300c00900d03504880d070050b4140000500c455190707203a4070300c0e200c118000000340c03074010030000c90810300c14800002c00000c43c5049035007446c00c0403143c489580d40040d10306036032540132651120808031011085900c1004589890701d1005c01c4840d292240b078207090540d0000c0ba901c8a150b031204460a0500603d04440c9070092000740c481c5405d101c2c96a011303420a07030f20100c0c0d0398250f880050304100d90480009c3c240d0744071110a80300880383c2c0c04c1800140191040302c6445010507040c3c008034400c42d880c40b045250103061110b0403054044000c03110440322140030020b90200d0440800042d40070307050b010b1846100c800601031440d02d001d070b0005441c0c116100b02042000c1c0300d039190045490b10b5501c02c5070050002d21002001180185000e41c00b81d66466a1003400f8070b002006000024400095025488200341402ca44802c80b00300214010040142c0c219030081c01c081e6642066000800e048610b1543c0710254184103403030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 253252410 1250 253251160 253251179
    0x305010614070c03050d0503190c020a0605042102011e050609041b0b07060b041d120f07060f05100e10090221090c10022a030106050310090c 62
    0x3481030002060240020304080900070006294840c0329901004a40380c5a4542c51314207490600390901140c800000d01020707030094007020002403130f12501401000c03031000c0025111240b640c40202805c1d16a030218041140300210341c5003141c00c0c400c5010a40d905c51000a010702401468099902d5004519814546040c01803520401c0e01516400664507143d407115130100120390041c140300341e240008210344100a0080103c2c5010b25400f1a5020039201000100c60310450034903004c01f041e09008442c1480414042d0b01980007001c43c42d1034070460084c10a140c4100703003004003114030f884903103110100a40c5c0b04900414076070381212001515901b04090700d40d070980e01048494401d0700c013002440702580060030504010011090b84030305007000503581b6541607864000e183c00c065403480c0c81d07041c00d100d486510798041c1b00810206000700d081c0f60306070609988400700d081d0680b0109649440940010006003c094100c408003103582c24410300514a22504860000040e01c000444166 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 253253660 1250 253252410 253252421
    0xa020901020c0f041b0c020f0f09040308061504090608151e0403090b1603030e1c1b02030f060703150501050a0c06110c1b0303041a030c0403080a1e03 66
    0x41a0000c024684404003040300f680c010202d000d52040d10740c041800b68072454003142130108407548641118030503e1040218215520701e03040d001d000602081441c580c0c4175101309400940505088655070be42e1404182192484108082440000500041d154407a0350201e42101c1c081800d1b00c1d0f07111299031840d030b2034200c00d40380080030103042d5800000e52203022040580061084c100301071610740d580149074481d000140c01c0d40071480d041603424185601402110f00d0354000300090f00d0b0380623000d0308400100202c0040380081220003001141080c8000c2c0b50142e4454000b002c0341c07040c041c03a441c040d96800040720703850b000034203202d000b00404501410301410707100141c440e5801e0000c041000c498002c0f504001b594a1a00c581c0c414440602030402400c0d0f002528010300150300701d0b81400c5907845100301129019034401c010412140400150102d24090140583d503620f0311400400f40c5036000f070303030006044c0a50001707032250540e802c0750a041e007030075009903500800501110280c04680c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 253254910 1250 253253660 253253677
    0x90c0111060f06060318060a0f180c0909030e090c04060908070e010603050c1e0a020d1404031e140109330c0c2f060304031707030e0a03080f0a02 64
    0x1a510b40441c641c2c2ca400000341d030780100059268801259891030315880e003842a201201c58964610b51181000301d180030314541501e0300c40c01c1007840e158903900d02002e0a494880e000400340d650b040c81d01050711032282c1005000009100e0401818004c0c000e0b01c40d903005100d142c01048400800003042079000c91108210783d40c0403043c103816882c00405601902c802015402e42400800c5000c1300c600c3c020240030f0000c0c00d0400c00c10748501c940200a4a000300c200000700c14800d02ca2007015410f03002c00100c0e415682e02c00024203110065280030304119a113031400405003095419000e0090005603ca02c0140b409441801100d130404038036214401102c00b14000d0042030100440e00c002466001400d8048903854654851204d58a596148191020006007a0100c80c80301e401300c88060890300b401a88100c81083c5035040a070b9000d00b21018190703500000495000019202074040e5005007004400c01c0c094034100c0c41c2900c0c0c020304400f41115010140000703a000315442030024400e980001c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 253256160 1250 253254910 253254931
    0x602030f03060109120b04050606030c03071703210f0a020703080f041104020409050603070605090108191103011502100605180604060906060503040302010c0206040b0c0c0a0209090c011106 83
    0x90242031400e111680002c108505008a4410001da030001400e030000b102401002e0f050901d0030f00b490468117142c1d01070480361082c1e20491221507940d801086410460b0068500e140c01001402000d50460080c513407104400c410b9101031a8942c61902c641a21502081d4000031840c3c0d0b50700b6125040740150b00780a40007542d032800203040d0815030700c2c4540e04140140c5008150043d10800142664099081040c440d91203000f4000f89040030003051001d8034036820880d00346590b9400080c41d05200401e100440c81025135901c0100640b07900c018080205a04015500d40c1c4900050000895100c8103600601c240103c41c0a006290300c105020f586004101240200424050311000c5001509550384903659000004410789070b440f551004100d141c50b103540724602810301a003154100d003100c80c20764100c04104800249001340b050340c44034104080a131542c918641c0356280003003000000f504142c888040c0103801780005603011004009a80303140c011600c081801d03454100c15030f4080c054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 253257410 1250 253256160 253256167
    0xb0d03090302130915020d15081c120c05091017010504020a030f090b010303120204180e21030a150803070b09101e050901021905130504060e1f060203 66
    0x14644000302d550388920f04038000c00e000d000c1e5141c0c1d600c695800042c9510310381c3d0000301f4079080c0c80300c0e0081d8880c03880c1c1140e01c29186031800602c15211080c4565001c000c821640355044064001d00442030b82201c9c0090400008500b02c40141590307114984c002e110b01d00001c0c10103c1c0c1032089290401f1100300c0808140349901c0e00052201a40000c0c1a440c24135855100c000030340a441d12901540170300a4051140c194514100900100007078030b50301000c60b004100500810586407002c0d070344070401c420001480c0103000422801c00302d0040d0100610600500540d43c08000030001e54061080303641c00b00101c1c024243d0172034400c4000d216002440e04140000c074003240d1444401c42e0300404001c03d030340d0644004030303d041c00c4404506a880b0307444c1108180181d0044540700d5140d000040c10300840c60148a4030f540e512221030428210704004000429040640200c4900300003898080e005014041d1600300d401c59109044400184844164092030080300186200d8011921507401440c035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 253258660 1250 253257410 253257413
    0xd12020702032a060c0a0605010b0703020a030815030303040b0a050105010306080c040902040e03030f150a0608060d08040b13090b030304030c17010b060403060b040e060907090f11031003060b0d030903 88
    0x1410241c410f0441e0810000f0242d5041c03a03e901e0002e101058000010b8580381c401450030608031030041c0c2242c16101020700c4a40c000980014100c91b9240d058105040990b44400e200542038031440c3e00950980408010701c020450400880c9001e28071203081844540c2c1c940004408035441446554000d0740310310030710710b280d0500750301100202e40050008586111000074071803640d88159032602d0410616020407680701c0b024031440750303d1042204e00d5020585490b0740104203060140800d0701c6150a6181e0808202c0d406049034000d03c0020085a154880c40d400c50114002d80d115090001e0b04085014409140100441d01071b40d0f80094001c040c82e0030442840c0c1c0b8111107001c500c1c00e035981c580351850303a6610b82000c4c1c0000c0d0701c40c51000c0b80e01c0400405101c20748005130795612a030760100d010b10041000110783c00081e41c0b50260300041c891140b075101c174040c01c0f058600707060700b03d800002d20000464401c406402d8178010742007400f00075080400d11080f2854080d0207000110b60100900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 253259910 1250 253258660 253258693
    0x15020f01050c0f0d11091002070f090b06090f0112150323060118020c03070f150c051e0405040603081914300c03190504050307020f0a0312020d1202070203 68
    0x52840300852007680c106040324021400d0b000c821071441f0007680c4801c1080280b8040030514001030502141c0503c4403110310ba000c0341582c046c03103d9040c4915030400045c807031039214801c0d40c051801c551006002c50000360300445440003ca000030f45e4851a0455103150034144001d940200409140080540381c5c60100004d2003002c06c4074031580c0701034080029190840c0100702130500580103104800c20b440051078014429582d0042c06100d40f410300c03101807003958005094507001d9421022410418800000d03034012803040d83c0240e540240781c258048180002c03203014003054104d203145d0701c070f80d050358100558140e0035a80c0d801200070310030006206e1010880030540d501400604d81000000012982c43d548c03103000b141c1135040c1300c8002c01042100300030058018052102e5000401c40d41c10705441d4162a03226881c17020303000c2d00c81812440d04544608440d00300454201064445000008400030744512210002d000000c800100504902046100302d03078489a004000300403402400c50302a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 253261160 1250 253259910 253259921
    0xc03010e07140c0c01030b010f08041b081006080d0504150e060424020705010f09090908071202030901090f0e040f030e040903030b031002120408031015020f01050c0f0d 74
    0x700402c0812904403a00e0760680019100c02990349015020300001000014100d640c0e01c00c8180c104103583c0c102c4420942c21031281c0d030300b107900001c103e5081e03804e80c1c0c80e030206240c01c0d80c0051020b2240c425410f114000e10ba100c00184c0d07c4520070744014030014081103c0713500481c05010703108600682c84000c4213009404030b8410100180c6102e05207560f54ee54008146881940900c100200341c030018400e40e414401000902405d00b1f03c1c80c01c16900c00002800880e480c05030314156507681e0004424840c000b001d0702c080e2076114403c4c00c540180381e5002505d9420a000c00c5020410441010403403001c0c2e01255400d540205685d0619599075449442d082e80703000c481a8240f2025503014007468907640200c14049010f1b8801203034400fa84001d040c0350000e002c040d20042032041c04201000b01c00d5451068000e47c00c643e07099100d441c0e0000c6092080301c150700c22391550071f50040c40c0311059000b0803403040e2a05980003c2100b59179841d074104052155809501d8144401c000d009540c0e0a680d100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 253262410 1250 253261160 253261171
    0x204030c0b0d1b08090f240405010609020a050d0501080c0f09070c0c08070e010b1801140d2a09062015040309030510110901080a09020d0602180102060c03010e 70
    0xc2001c01c140091044080e49015941c070000c0c0d44c140401c01341c6007042000b40c00c1055508020000114004100100f1129425052103410f400b50003003028440250484030140c28030210440d660a141a4050b109a01c02840b074466a42000000901c5400104000c03958010241440900743c20000401c440e8500081800c410710030100200300201d6089500000170f084000014500c6604000c440c080b00c203c140e1040c11190010840000b40070109041e000e0003803420301381580314400c0c03400c2c1c41449008103c001b0450368904a40001c1140015901c81200c0c1e10320202c101c00f4180d1444201c458445a01441000c50b07000c202043e09002180a034007008030340d550645205070b0380202414041380342501d040d80003908070f140510501006006280e40962079a000b0032500c0c07900c0040000b01d01a086000b070501000000045100d0342a40000300101c0d8010460a141c11076072910302c0003500501c03014010f1008800d00e040300c43d4000100e03180a02180d00d1420300b141c3c41e1030588640320000600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 253263660 1250 253262410 253262437
    0x518010c170c070c080709110405100e03070306020c0a0212030703020706080907031406040308091b04020d020c030304060e06060406030c030f08070b0405030409050c0306091501110a0807060606030204030c0b 91
    0x43c041c007050030194184040c001a41c00b030404e541c40c207d084000c0d5a401c101b2000440800c20080120b665400003405a810550030407a0091050a000a007810f040c0c1d44054401c83c00002c02c141c044001142030a840c0380300f100d0b46100742d0703205181d440e0740b0300500300010096404480140301e050700664030280e0002c1c5c500201d5824503101d40d43d8400d900c00800d86039006511520a1004268100344160340c0220303410006c11280069841e410070348038009400c035000f20760000d10203040c071450b038048404245069048960781e040610f0714000424988041c040d8500625001c540300b8906801174204598200d0280324943e800c584500d10840b107101030031952900200801c0000510191886109500035801345842d076107080020019035400400b45910000200100284e5a449070881070f00480440c69007a100c280081c01a142c00340040703202c00305889207100300c604200c2d50000608071079204010505c4440d6403130324150164004c5000c02007048410141c18008441c00700301904107080c5980 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 253264910 1250 253263660 253263667
    0xd11070b190806031c030b0f100816020a0b0112060509060705041e03050109080c060106030204120b3706050a0f0e0415090602040311030c01120b0619030518010c170c 73
    0x564001040110802c0e80425262081f8840520b014000c0041894042d00c560424180b54980100081002400d0704052080514504c610b20703c01c00620542c55885100d90f01c45c0c3d6180c0318040050312241c18116200c50030303c00020a03108011410078051801d941b1401e040c28180380483c5095a0002c00040592140e10350000c0410400d01030880801e0040886a9031040d90036581d90801c0300c140c0120003414010802000440c00e040d101c54a959004141400f01d0380764501c081120251005015111249032030052070f402c400300080a020200d60441005520b5980050020a208501c0390b1880c21401117420400361100c0b546959002c0c1c410103d2551014030440942c0880d11074034070980b25540e020801b4020007000380c0354201511000c070001c1c014034801e44002050482150300d0a055162034104000e140d880d0f4034184c46440301c0c0c9070508080030055402c010700810007214000310b000c120311940c80007500c040c441c4050100c640e03562081078040d90362030b0003a5094054601d940c500d4040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 253266160 1250 253264910 253264933
    0x7060c15020a080910060506070807021807080603010b04060305060c13090504050a0c0803070f081809090105070f0c030c0809010915030c0207050a05060301090e0309030d11070b19080603 82
    0x288028000002507841d02001802c005130709514020301c2c00e201c24021031621805101070341e1054140c42056602048030303036442e140351010507403030440c540100c43c03d505c3d00e50a1000c2c5a802c0642c091107240d00358020041840d0410402040c0c6110303201c00740c041d0300414003058503032030400300529181040480349601195100310441c200d0300704035426901600507a10f41400c003c6400ca069008141040007141800c0e4a5200c1517043c040c0d9080040c80e0a200060051881c01e46120011096900a019030321364074011011901900c000c894560001d038803031003580c0819000e000411006509035440c0c180c2600181e0751190568071000700c5c941881400f100004031206140071100000d00303d6030b40450040819a40a4079141079a04968442c09281398144155222341e010340b8115411550041b42411a100c02242181f0841003a00d80601801c0c1028007083d401100b6104031201100843c0c0c2c91980c0d5000b0003840340a2101940d00580c00d1f0b10340c0c1c08038588654020350300f20130020251094507031031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 253267410 1250 253266160 253266203
    0xc010209030a080309011b1209020102190305210f0c03041b1211040218060f0d15030309060e10110c03071404050109090803072a0b01050310090507060c 67
    0x80c8045503144800003c200c400c0c2400c0c01040171174050300035180e1076407000348006003854681117841c0c030425a8270040042560710800a4149404454566008141d481d040090070b641c881c207200a100c2c46a9031018202c00220780680d4425a00d00c0b01501450301d4148041040740e00241007991401da8141002c00341c512500b07600001000c80c54500d5240c0c44280c54004036400850314228462072050000b040480b101104c01c010030076080f241250f50351a107440300401c074084c0c0caa9040c0310324940a4601c6403440d150722a034050341d0003500d50b10400c80c3c0c0c1d01000c460481c81c0d100070540103001a210186d1040c0216206024002c044065620f0050804046071401e101035100d0041c0c4603402c86000b40c0d90a2511605001d05600c00092121303800503282c4910920004d40110300300203a5200b060300b2050703c00c042c2c48000c4158034680ca18610385041c0090310407400c0c02418824021501110188490b5104900c2c0c850382c047d01621001d0f24202e8107903000c100141084e03614900c1203868020b034844 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 253268660 1250 253267410 253267423
    0xc1502030c030702010b01020c0303030c0a03020d09050d09090203131e210f0512041b030f0305070b0a02031501030c03110d0912020313180b030f1509010b010c080c01020903 76
    0x5202500c140c4903d0103440007425103003000b03140c030705540100e00a074030151804011a44d100c01c0081c0120343d52404590b00b20000e01c00c46d40f407801514600302c620001c00c00c0205a504003506959030350302c41d003500d48800c08101e20081d50b010a445018025207400147c0c41ca2a100c0d4901200e94440c288110075140c06001e55068107440c40380c024094001b41542c2c0d04003400d00a407000e9407818904125000b80070521008002e403000e8104c1c010b020b840410809444010700185038083e4800707009206030b1130090311030742291808584e61640100020500c50440c800c1c0d912030124005044000d0500d6001500280141c448003003c1540301c000b5500e29985c05002000e0581c01080300080402150920150107520340301320508540003002206544c01004040744207035078640e1000d500c7c4144082d20071005020211010b509030184400781c50019802040700b8111004481c1010907694070300300c01c1e608840788240c0039030104500c80c1d00400031038082005400c030491410b000520340482500024581030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 253269910 1250 253268660 253268671
    0xb0712090b031008160b07080c0111210a020a0507020f0a050415080c030c01050301090e030904050103080a110309060706090f020a030f110603060918070905180106050f09070c150203 80
    0x4000f002c082220382000c000340c081c0c180c1a01d40510195080000013180c5224024024100c88000f00302142841c4082d480380041405036410b4540d00e40c40b000480c0040c81070324044900e81c0c1400c00c000346100d200c5000302e03050445e9035640c491403c80d6035803c224144081554154101c1c03054400410340c0d0302c0383c0c45001c80250302814600304242c54401200c0c0f03022160001c1d14065000803030504032507600007080c1c0b030545000c00d8010560310207402c491460350041000c0b082e07100341842e00000a00188500070b115844540e03552400c80312440e482c007541d070f202b03079120142c100d541000100d0226040d40e0043c0718083c400c0c1c045101000302500052100081a0400d49155004101c0c800420220b1440c810040380169602c9045181610000e1002040103020004a04c40081464040c040c00d1000101400c0c03e104100200c2c2400d040c810b10a400b050400b84803586003241c0401c0c2d40c904054115100c5800804074070302540c441c0c0088505044080301201d05480390169070504003440d0018600c80e1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 253271160 1250 253269910 253269931
    0x6130b2d0702030c0c0a0302090118020705010c1e0906020d140d06060201060e1005031b0f1816030204080c1c0b090a02131509020901020f010501080a0b100b0712090b03 74
    0x1a081d40b22002d0a0414400c0401e00c0303044580701c200010727102c00c0301a030f04554801110383c0401544091440191054000051541d46800d055056007500240c503104d007962211020702d1402d078408000c0e5400c0d8540d024640140c1c1c40380c50895002841030707546880d00d01d0801c030b00e107042c136908450510690799960020409031351141d0782405841d4280c005c55900c40e0011005a440e5858400400d86508007125150100c42400c111520b0070303103449683c2034041c5e0b03020300b01c6910710300c4450f524602c14a0944000801d01d01e00710b05241024860300035034040e80d500401400589102200708200344c0140c81401c041e800b614180e500120300c408064030301c15007405002d803110511520400032401c42900e9106400c0e446c2084245030603000c00c24010503121007540040e40c0c1c05480005030310b04403903201a40103035070030400081120b51011922035056031150032400019242c0280300c4800405500a1586003031040c40100003241d10b064080c00707844041d08200c000c464842408040c03541c0100c6041858 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 253272410 1250 253271160 253271167
    0x30604060e0f10050f0609042103060b031003030801090e10090f0b0109020405091b031308160302210304031b0f061a0102100b060a05090415120506130b2d070203 71
    0x307145410085a42c46402101e5121041c071f0965107005034840301c0e02d03041c81d083c90b0400c4006080d81c0242e1200300a0141d07540030649a13b400054400448541c0c01304400184141000103120551402040381d441070300d8026141054540407604020303c91048141c030700f0f10a182d20480820840c0c0d840c0c40c06003150101c0540c1d0756007404c013400300024000d8884180e40d46103281010103044070801b641e03000b4803801455107802409044c510154029124003000e5030368115105401c041e000150504030f07a0b148031702c0d4445a02c40d00082842c900003250301501083d40146001402c101c050202e41070a48180030802954010303889210403150501c0000300e1400c014038000d100c2d581c0401003c00003400c401001c1c0a2080307000041210b038044d4070312540612001250003101580e4036040001120b54091001c0d900e20b54603100d8100303a174403540381a5414028200070900321079a200682c0c15407034010710010b030345445040400c8444d80c011070310101001749c40d03094451242c0010031714900404155000310745 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 253273660 1250 253272410 253272421
    0x904150e071803150f0219031103010815071b2009090714040b0402030907050a0801020307083405040609090218042003041a0901020702030604060e0f1005 68
    0xe2060103060030080c0040b518040e070341038140200702c205a982c4a4003007980319210310300c10405440c1d44403104541d14000b00c0d84042411541684040c140090b0b6130038020030804000c1c0d81603e100030700410740c00b034002c8014620b0012407003105a4100c4018a040c1020b649180c1082c51150002042242d500103080d811120f0b40014032960504142d0441e29001941840407031540d0b41c55080c03041c4505186a00303600301c0d503592154494108e002008d4000c0d99203250110041c0c0e02d400c0c4500400344210710000001c1040141442501c0c42680180c551071841d4850202c40b0045400700e074004080c200200c0040c80c1e81d03003100744501c24004040e48546464a08204000d04204c0480d0404440c062040c880d00d6450b40b1054401003240800b500e001400c41a07041209900c01d2055165049008000003400100700184104840b5944440c1c0405d140b034840652003401d0384980b04000e949079000c00c000c100450140c4d0710550141340a0381c11610350070089480780d4106007000c204042910740e00c004005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 253274910 1250 253273660 253273679
    0x1713030906080f010302040b18010b0a09080312040201030518010905071a0a0219030207080706050a02011a030c01030e0c18090601050103110f0307140d020903070603060f05060f090415 81
    0x50a0542082d403024034250220001e081014400030b8030640d11400086055103803581380e600a10502c0090400540e141c00c1c01311480c0d8030119174a80000c046050016050201006a4008214001050b030244d16030781c004601900018041200b040024441300c040100c0910a1443d568420405040403520b0441104e0740c410004001d00314015080020552103136011a80822030008000e008020303181c142070882c40d0501d20341001c2d5443c4981303000402c1843d0014090141454240c1c000d00003241d00d8100c038914600729181c060340503030150382c45c03100030b40c003d4011036000c40240c41203510403000710000441d81d200c40400010440091420b0043d100024841d55000d80800e003014041e085c900400d4607243e2003a0300d11901c0284010010a0281d445200407440049448600341d03100d00040a02200952050300d402d03209101d04140085c0c19070080c05075130122050b0054a8204520740002e001d840d6121058a00303104004110034074458ae507030b1003074100405010800f81466820420707000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 253276160 1250 253274910 253274927
    0x3020c010227040b040501050604031e0203030c1609060609050112140a1409150c0d06030f030905011101050709120c0e150a090e0303150f0d0303020a020706080103020a06050a171303 80
    0x460045d4107040045c04103440f982e0441d41181d82c882d049603112054401c241c0e030300040036240203600d070000042004001000084011407210808580c4072011f41d12a60001114414845e80011504c0c0f183c040000790300540d06001c20070104c04001c00c0b1005034140d20040640220b034442d0390960f990070012100f4042c60309195108040f90001c0540300f21240402c0b040d08070080503510f000000188000204069401800045174003d10900c00380030702d0301d00034240b15228018903000078032821094015110501a00d805a555600d41c000c0c4a07003400241001045105401c0d104c00c0043d0034000350b41c00d042e019840c03040580c11841414155004100140d40f0011b0348031a04403810f04902c3c0080c20350110442c2c5d00656480d40c0146c12106d41404035006000100c1055405451603941100b8545c25400810890055900780e03040c081d15a201a07810560030301000e508142881d04c00d01c4400c0c0a14000d00162011342400c8960308000d0380100c036281c6c0111144100d881c13520016034100b54000401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 253277410 1250 253276160 253276181
    0x330103050d0e0d3503010306050109050c0307091401020f070803030a0c090812030a0b0603041b0f031a0414030a09031203020708030a050c0409020a080f06010203090d0303020c01022704 81
    0x1003404071800d4881e00485543e241001110314045982d043c4504180e040086507213901d0780a0315103d603502d040c26401004248100c007001400d01002491001764141128468411030300c4154210307041079414422061490100e506520070821060a91801001040c004002c1c03103008650300d00d040c811080c242e8441d01e18107018440b0b441d00a105900011800902c0491000e442035240c3d9a503070f8110014011500d1410340102001040c04284100700004007038509144502d42075903580d034400001e51070428403014061017844012085410faa0038946034001e0b002d140700e0101d03100c4554070036046a0040d140040411040c00c8100102320b00c6214036034030107a40382801c60914030140c4846400d40f10051203150303000e994100040903d512802540d0151580c000110344078003040c10040d094a20903079060078040d00b03080020301158400002c0341d18001c030192001c800e100050360700ba40607410042d075412955400f40071703a008103040748182c51101200e0f000e80d60205584d200c05c0c0002c41d00c50001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 253278660 1250 253277410 253277419
    0xf040324060617040203150408031014010e1512010e0403090e0c03041101020a0c06110705090903070f0f0b070c030f09030804060c0512030405010501080601120302330103050d0e 78
    0x304004580d04280c3c0003d8007801d0f00c0030b01d036543d0b4a07840040e0600f1010662404010100014482445694405541b00e00d80d0340d001d6104c9951940740080100b40d80401c82030000d1059006001c3c036003002c0c1081c4007540071130034600c2c0c2004016640d0202c0384009800010440724510200801d1543c00000706000b0b0040c089000d04a040800105100e4400140003800c012155041c4c990540d10030082c580902c0e4000300410303407240d10ba90000700803078098001c0140901c100e5002040510300320828901030540170009520b03250711551038140d00e44d54800203542036100e00c950356004c02d00740001984503507640da44041c500340b4070780b038041c1001d4031080649040001800044c00080e01c03810403101501c4c440c1c103000907050040c1c5425450322030528204c0065800200c244000c000f015005141038905080c140e88440e030b04c2d03869102c0e14014001000d80140e00620f440040810340d00354184c03c040716480100c445550b148440e040c0c1c800280c1c03044480740c0c860061142c865504c400e03000c5441c3c0003142c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 253279910 1250 253278660 253278671
    0xb0f0f1b0d02100c020d050705210306040f0203090601061407050d022b020604200d08040501260604020d0b0319021912060c020f0f07050f04050402060319020f040324 73
    0x30351b100700340b0414400380f00002940c076080c4802000f200c051411500194030400b1040c00008500350806e0329058042c0342030000f035a152484a000750f03441481118024260f5a203840b500316000781c0000e0040074032190402c003803000702e00d0a0000b40840a000e400178001040c101c1003100000c1c41c4143c6c00d0040300780c0581a9411a0350204807280c0003a084003800c01c2c0130b03a0312040441c6800003041202d500a1141d03441208200c0490060412100242c85114002c6006200030030009030103031a200003959410001341c80d500d02030380604001c0c8001840011aaa5400c010902d8a40d104009110020398184941d086140404400c69640d82039212a0ba041b4545030340ea06282c1c081500040207186c40724100f107a003e10800c1160b0680410b4001c42d01049000c1d5440c41c1c46490500035140100320a00f007800b5542401d000f0300d03004030b070701804a611f56603e82c007510070b05200323103c2c046110580801c2091440885180900041e601400040443c00c55080c15100f2000100400c10700c2d80c0d041c04d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 253281160 1250 253279910 253279931
    0x10050a141204020405060102030d0606020a120306050a090c021203040822061706030f070b04150c03200a061b08010e0708060d030c0b0a0209010210060b0f0f1b0d0210 73
    0x101803542c1181d810789000ca070030b40324500140e0a500442d040f01c9016840c20400040040d40040c00d40501030180c0340b03480c2e03051200c3d6800c6080c1c1d229809459003000608208100d00c11503039004c44181403103481079600d00c0305441a1119207610669040e074946001261403020100c104410442a19001d01440003ca1070f20101402035203c104d0461050450310002840ca61000c1c00040c1c40002040305076010107840b020101525042030042000d400483d10300c550b0100d000700c41c580c14180d0180c40c0c01010306442d02488250a1121528094500910b900303040018018060b4a410ba9102c02d0290f18601541e0001045040d0580c0079240d11a021014060655080002541c00000a480b4a00c1311600390400341d6007500e5074600213160742d284004101140304964041c1200b00c8090b4240c0700d00d00385c005905415603150340540b2814040800400d81c0310440c0c1001006590b110301e203000d041c90a10803c0c0d1a403021101d00f08245034000c3c581c003051466050003000000c400644082000c0301c3c06 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 253282410 1250 253281160 253281187
    0x1c092c010504090611030a0e0609011a04050702150108030a1706090c0306062101030303110a080705031302040204030803011a131401050702030a0501090b06060f0d090f0210050a14 79
    0x40c4a160701483d41c490307401040c0055a00861418546401c0559890500c0705807580202901e24020503240503c0003c106500010301645000d0003d031040070008d07100d1801040b0080a019202e4015480b40410340040b201d00100c242d802000e8220240d9151030755120080c218000702642d035164000c000b000c1003120390320f101d05150000303130704500c4079100d07620b0102040c1503108102c0382001c0b040f4101d40c46100040c1c4805940c2c10781780f01e0f13503043c031560781d045000440c0d900510030b0750004034117100005099580b00b84050340e0310003083d03100c4074046c001a402280480c0d02c960005c1d180034070008018000d1800f003c50a6a409480001305e5243c0348221001c0d011915281c001e2181c1200c280390f80b000581e00c03070000ea400482c1c0081c00c1c1e03180340103103207041c600a2980140842d41030002d4130018070949004001e59405400c0454064a400041c483c041d00401034220100d4400d5903040851003d80c4601420b15140103054845980d660b00481000e40300c030710320501044c8442002c02510343c0e482c44 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 253283660 1250 253282410 253282499
    0x9020c031606180c030203011d0a0303050703060f090f06060903031b05070302120a060c021903180905090607020f0a08040308030411040c26070801030b091c09 70
    0x1081044600710302814a00040500800c0a200c828000404140400d020100548800720b9100724001c102401010071652003c0d510a1103a6200740c010500a0003c00c1c000e03040241d2014035460b0000345c25450705240c26461101d41c00c072a403255607070700c031022070395416116100240142e030405017421881c0d558002d0a03c0303418085034041c0b035070315181036040210030800c800146900500440343c0f240301c92115a5509603c650503030b070007414141080002e0740041345078244007180008200c2d032100d058a05490303030075a100c0d032800907080c0c00b5400180b0030010f2203500d0103070f801d0402030022400e12150007841e00702e00040c1c160060b0010b45e46840016246800c5a0449600013003503a00c039600e9090600701100c48080d855003060074540d28031084c560045070440703e014185c50403000b00802c0040d4840c2d00400b1100340010131000300040c00480c80c0c2c48000307030780a20b200701102c0d404c0b442080c1091000c1d04401c0e03100c000c580c0442d02842400111400a003a00c0128100c0c85c0c400d9a5107104201e00d40d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 253284910 1250 253283660 253283677
    0x5060a050705010f0219021c05040b09010504080604030504060206010e060d110409050a030306080106591006032013030503030906070e030607051c020904050f0402040609020c03 78
    0x203001440908110007034014000c0010310000464651400c981200c45150450300c1c00d41c0107008083e48406104201c80404428000a41c1c45604003800c0000000b02070344041d070300c641404014080001e680c1402c0140c1417140c1e00c6a0703540c0703440d01c1c07800d640a07203484c506801002064900341c040228686a850150f00c4050b00700310700054020120300890000d080c1d03c0340c003a050340a050600c60605800d6000402110301d10f50003008110ba4981c45055070044400c00ba030716003034a0310300d00515400da0303c05406400340c1465101c01d140016404051031001c54400c00002e500790481082104502c1c08605401400706040c00d01c12410020a0051100407400440700400804138951750040711914200c0003941d031010482c1e03500d01b414030442c0d654400407201130000074a4550059502e040c0400c00d80d00541243d1540c0b8100002814030317266143d05240810f042c01d41c2403022108599660040901400314184080858101070040c03000b62003030768015044070b9004002c40c00001d40000103e6002030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 253286160 1250 253284910 253284917
    0x10170703050a0b06030a05240d1202010212040b1509150d0c05060c060105030111070507090c260402031b0a0b1b03121819060b0a050907030207021905060a 68
    0xd80c0c502440e68010f00304058501e41010011040150301034540d80441d02840303803c0c4642c841080c0c080c6901901104000f40d003038000b10307601c511100081142c40d000244104600015040049000408210b12030440302030701c0380314020090080c1c0305180001c1c020000404d540320302840c0f41501c007554032401420843c0c0e016503408081002800320900034403000d00300050003503550b1079520020300c2d0788690a0203114400d510300360504000c1c404420403500015840000b070408036150450765030040c885610709509100f10000110100c500b04d100c250b483d481051600e80d03241c14180181460a0312540c10400351084035014458580d65074417050049440c4189036640d074400341542104c004194900b440c40c940b00c003150240030f04900b150300c248255000d0380440740408030f80340301386e40d0781540c1480000754218100d446000720700107400447c0003840241000c1c80303096540012a9107004200c406500003603012400504500d4820740800302007400002c001030040c2041c0c009a494810030f088101030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 253287410 1250 253286160 253286171
    0x3120f090206041509050303030a0b031e06071407120c060528020708090301090507170a0b060f12060a02040f050307031e050f010c02070f080f0a1407031502040510170703 75
    0x13514450301d00c41001d445c0103002c3c0c039104d00300710740620060030000c43c0722482802039050810010118084000d5008424001040552a800d02c140e816401c41e01211380d0244c030400c020008190241107a00917004240c2c0d0700400042a824400d08482c00680b204044002d5202001959098425a1410700c00ca0027001603371203905180041c1c0500c55809025011b50801c00c0e5030f800e00001040b0002107035507500c0741e06030341300b21002d003540c843d102d80c10010198a4190b0101c0d8103410440c0001806402c007a0441c40b4202e0800c5030145004021602c24101e0f5800240c00d100c035a00607034126009140540c0102544c0341181d885643e050450a1800c28070b10303203154160180b02d002c00132590340132001c2000700069030350000c1c020340743c2c2c8840c00b404542034007000380000c1003600016a850f5000b0520040d12841100c2e90b242800c5040702c0303803060654840c4d000c01201280c01920347e0380310b40403070140c0141c1e910314000030f000c429041001e1b500b081c0245030010b035a00802c5101c515510101901e000901d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 253288660 1250 253287410 253287449
    0x3090a0b060105120903030103050c0102190615180615020309030705060f070f030806010e010801060815150c030403110604080303010603150e04060e060114100c1a0403120f09020604 80
    0x4103402013126880f8111401c00500c02c40680c0440250b060f01c0c0200305a6414100040059a464006820100e070f0303901c03580e045c200440c0c00d660000308541910700c4401c450541d40c1350b00114400310499103140e0b00e5542e00042010309488034115214441c0303400034608001ea4680082e440b4076562080303e0081d42d00081c1501c200e8249402c071303035030b666000d6081c0c00307a00840e080040c2025401c0311034a0100c0d441d172002541643c050740322641240e0340d5507604001e41e5198410444a00d40941406130884202141c0d0b00904484001619440040100450321545503092104540030b141201500412041004bc444400084210790540b4018103021829103240704001038580059440750009500d118107200400030380750000d80c1c40407448012035503140d0705d602c04403074282d00c0d003402290302c402011884001c4501404400440c0c0340110584003504018801c00d4004460440d4210f0001e200b211311f0340701000c202d00c2141001da000e04030412000740613601080452080f03000310350604d000e2440900 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 253289910 1250 253288660 253288667
    0x703051602120a030f0503220303141f0902030c040e10030c090f1a100f0302090406080d021608060c1b0703030e0328020405090a0f0803041703090a0b0601 68
    0x103045a400303401403100c2e001c42103070242c40c0d401511040b000107941d102c8407002948103070103a90148a640080921054034411541c1e09405415400c070b040c140c8940b442078031544500d040302c0c811709801442d54460700c40c0580100040c42c154100000c0144140184180e280b108001c0c2e4081c1c46200440c05490f44844100000e442860f510040c103410541d42c0102d40301303044d90417401400840e990140a11840401e18410030000715649a400850b42c1107900f592030f21031071170941075411720304006281c444080080380a440941c3c2028031240d100068440490303904021040f0005c82c0c155911410504110342541c0700c181c00703815140028804568850a052002000e044400843d411200300039507074900030b0900111186004d00c07900510f40f0070300009408489030141c0e0780c0300484445101a00d6400c00002707180140854282d40308d08000f4600050160b51110580c602512200b516480c1c54500f40f060030010010145120100340280b1910320800078068500d50b6000b03c0030032142c0c0e42c610048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 253291160 1250 253289910 253289947
    0x3160c030c060201020a030b01030216060506060919140303120106050706020c011a040605030304030305030a090f050a0818040b060304060c05091314101d060d14030a03060806010b070305 82
    0xd03055200450740003400341d40550080c07901c00f003140c4007801080080c60041d81240601d4403601d140354802003010002801982c40980d00c0a4018101424010b40d0400310b1600d84510b000075003488090b40f4107200f800191115098500340460065142061401c25110900410300c02c82c028040301207120804c02100380c0580c4d52801405000300710a4001d01000c1d00381c1481052103500440c81d0030004100d5050100c00c56055a1701521107605d1074039014280300081400440a0310820960040c2c940050070900c410030f0f0344d5003d1202e90b6140d0012068030400303070707040c02d00d00c6106501d001400a00d685890050303a501c40e030044c20008240056540c11b490030b109101c0b810f80d014030801006104024035a101041d10340c41c99098039119a10381400803030f0381d0007a00885481c164940c13602c4140c0d81d80000d5480e0f010714050031071020100300c0e44c0c070310040e900304000809640d0404174080d0302d2581d144c441c0000030444500140300c6940b41c858000780d03500c5190b5000c1d0800030000b45801c03c424550101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 253292410 1250 253291160 253291163
    0xa0207020d0303050609060102011b0507020f04090b04170a0c0f11120304060305090d0504031407080106030b04120f050904090c0e042108100501080a0f05090606030d020a0503160c03 80
    0x7080c0c55510746250007801400111035545c030807080c0d40c000c41d2655105103c0d980307034580312540d1802c0181d05020301340ca0030780040100f01d0384035004c1c80202d0215142c50281e420076610070086107445080030324002110444801490721440c40501c00c02540c0e981c4140010300103070304001c4450050509060101440980e184455004400c008103000c18500000c01002140c40300d42e03040156031500700c0c04640310440c29103414002442444203002103510040040810450302d4201c40c04265520101425141c00c1d43c0291204c050b401c04020600a1072910f24440d4240c500d07100300f100e85805009029401072a20321801256035180400401c120a00c0b18006400300c40d0320194940352a252000800c00340ba184000b40c01150340303650381a04e0141003d540a200112074040e07100e81044011104814010000d07855140c0b140a111044500c510629014220f5100a8040c500d00f078000d0614000d041400d130f20446d800070300301c400881d0020080e41c072500088000101c039078025082004001003640c20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 253293660 1250 253292410 253292419
    0xc08090907080105040c05030405071e0e1017160603050c040b030f27030a140d15080f071802130510020709050f070c1101140c0c0f0402041d0a020702 66
    0xd2000700707508000c1c01412118105d0b0180420061403008640034002a03070024503903485500c0c28000c0d0403000c01400300303240c11094001d0740c00742e5480c81c00110000030b41c0c514259121001e000e006030b82240e444891000d1141c0d000f41a2445914640da04102191084104156660000c14400303081c103800c44005029440d04140c41c0d042c5070000c0a225901038480000f0305850010140264903560f5a076945000040b019604042d03103040c00344d5400c00c0a5602c40c00f510b00c2004907804e101000d100e00c11108a00f01f040030130150808440900e04080c86d840142e196204000070040601d034101c14a004403074401c005a00c40c0e1a8139200c03a402c00d480e412296000c01900e240c0c01003a6400100300c0b04841c204041440070b520385420080c00340c402a100c0200080c081d1b40803801191003540072529038001890400d0240074000100c40241d003241c011101c540d0007004060f0414170b4842c05008006408032011894070340b0b0200401c012022111310300300f04060040000740328041c02d0303043d10031003078000c0e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 253294910 1250 253293660 253293679
    0x61d06010516060b0913050307110d0c060c0303050916090b040b03031611010c0215070f0c0627080d080c120a050a0e0d021b03120c01021306020102190c0809 69
    0x6000340103403152130320060040d10354000048104007104141890240c00801562074000944c603454800c5520000003034000e000780000800260440301070000824441e13942e9800c02c4240d1800400352003001d002d101040d400f40440b8050000c0072444902291000d140020f4401504d8000c980504485296179170b0500020603507055182c2031940d40c0072210300c01c04540781c919040307600541d4068545c0308040c0d0844040c00454112103214001022100d0060518404003409a80d60314100005900003800045c0383e503d201c0e00034a00c0c41500000ca82e009401440d52904103045155a50400840d0340d04100400c4046030503e000e503022600c8041c0705040c0b00c040ca2900001003c080c0c00240d03040c0100c1c9140140750b945501c00416900e641c1c0700e071540500a406d40c00924440590051340b03a05501d03008a4120450a140b5034004103080320114002588420304e4540c0d01d50440b02d107510410a59004001d01c0b0500890505c4100c42d40c1070310704007071805040500b4a001c0c00d004800c03201c0e40029551 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 253296160 1250 253294910 253294913
    0xe060a020307090b07030504170a050a050d021525090909050a020f011d04050a02120f06100f17100b340506060f010c02030703061e061d06010516 64
    0xd8000318070600440d03e80b11181e66903148440c400d07201c1d00f4001340000c1c0d02808144500c1c1400c0d00308401d1481005e0803100154032a890f000c0c203042500c2e038221407075805131030b407a4001d030780502850380746607a005082401c07841c2c24002108806508100240000c0400c0c0d14402c41a0203102000c0140124003410421142e051800554842e18200180c0c442e0258010300c0760103602c100c0c0656181025212921400c020f038a050001074074001d84241d80d00c070b0b02444110b4400000c20300181c8a49903105c0011042d040120912018452800300300c41000106c1003002010341c4c101500d4829a442e140c5001516612039a00318101c120907000482d40f02c40005889d07a070006c03000c0c5c0071060204206061408003841004001c0e15056103c0c0007040d0390841c100241c06854554464495210181090790081d0034582c0007c4c100310440c0c00032101d4a90b25440341c4500002445244490300080500308049400c00c4528039810710803100b10b800302003513140000d4117a442441526074400a8203c0318682d080b99 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 253297410 1250 253296160 253296181
    0x7051b04061509081219140415090905310204110301060f12151e05120d02010f05131e0506010b0405040f02130b030703060f090212070207050307050d05010e06 70
    0x39214012480c89101a030f03a082c0074810040701c1205c4400c0c034001d040d486c1d40070b01c00d030b03480301103034441100204e814040000e1010001d41d82c1c1d030020900c0d950b4000111b0900e900b501c1111030241c1048820082c610b955001c140c07100d02d490380035842e55035401004a0b241d10004024021518910203003007000b1000103000360b000201c145900025459880b41c0a444034103620407115074100b100601c1d0401d0340c040140b107280e00d0041000a501c40c40e80a80b45482c3d102050a004000600c07030300c0c43e4011254402640c0e420702c03c1c030341000d098036400e204c607051034039458109001000300600b24401e001e8550f21040d40d079a02104400e41d21105880d110741e03640c4104001500301d03210741d6008600f4600314040482240c42200c1010300300c010700c2c150681c01d024054030710350001441c1030141551894040303001469a5121001003802032409603a82d19010000c0028500c080c20003401d56010440a1080b55400b080b400c0a03144281c611490211103800e08a024107000360200146014500910911816 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 253298660 1250 253297410 253297427
    0x1003120c0b07080601020607230307020d080f010e0414151603060b0c0604110604081006061d03060606180402040807080c0a08060601050d0902041505040e0307051b040615 75
    0x520380300c405039407004819180c40d1004c644050040c0c108100140071680200400d00070142000030440880a650204a1032940151136103400f580c001e001c058001684040340c56803040e40703d00c4240e0294074100c0c0501e11140c2c050700040c0440842480241d10550801c981c80c82844c40d14450141814810012003c121004110b10002403c154011400210340da084441c6134114000404d081d03520360f190300c030301510b07111451940f00c8001c020009041600b0822100108041040020b640e89008009064021007502840002294140c121070342c0c0c2d030110300c0c250700a90031b42d6401e54610221441400080841c51880d034003600c003040100780c84000048080503030300c0d05801c980308400b640c020444a00c0c440e00c502d100541c0314400150595214001424114003507200214140019074001030035501c68004031a401001d07000c040190b85014003410280c919008059841c0c00c4941c0c40720390300ca200c11018001c1ca20360840f000d1045490700d510a5000740115805e20a0b90662ba0900400c41381 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 253299910 1250 253298660 253298663
    0x81c0501050a051806040c1403010803030a050f130f030e04020c0a050709090f030c03052719060504090203060604050a0b1c020909040201080a110a02010e1e0607081003120c 76
    0x60701079000c9a14100440000d1014084030290244c65507642e08102c0035000d0101f52004004d032040d0044583c0107190095400781c1800d0029507120f1400d041040110b907801003c10039041c82c0041400349a1103801c581148161300240d1240c1d05203102d003400e8401429800155410901c00283e001c140c500102d102d14090b8071520a440d0000e03520b0300d101d400d40d100100c014041020b0402c00d01c00007030284021720794552081c00c0c000d0034034541420200000f0000304003012a1440e080081d481417501c3c040c20b01d13540c10720344240f80d841c41c18208024210301480c011040c0503580040460b80c669101c0051300c0c002d2200400102550340c440c009400f840c0c103c0341480c411489103100c030825034040c500948548040142c640c0307007035540e182c004640103140a403002002d9903a0340c807500c802e80210740007000c90b2403240d0004141034500803104c03454035105007070041105240a140f1a90500081403c940100152a01242c81d0321050303209600300718654401410501d0340c0805401443e0070000384e00207103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 253301160 1250 253299910 253299919
    0x180c03060f03031407050c09070306060225090e01240503060c04050310020a11070609050111030f0d0c140703021018020102100507020f070f0e011e090207081c050105 73
    0x866507104607240070704042c007000300400d001c8801c0d100e0810a0b82e0180801c80d008404a43c18066094041959800d05441000c0007039125070307050100da81c04001c0a511342001c0010495208000340c48500410b81300e0260104071038a401c10380e0b0300f0841c2500040114004019490503c2040d000345000d00d03041c0d0701c501406802171070001244030b07515500366412941c01a028215000417600d40d10000d5100350a440144400406d450b40c04c44403c10880000c0e00035601c4030000581050001b4144116204030100c140c0d2007002000c41c469821800d440b511a0f020f07502182d44078585c00103850300c0688840e9a14500000f0901809142d4002007140446014000802a04842c09025180001444c4019016a01404142c0d01200d07207907000541c01103ca01c1501d06d0204528a41790620825900c5080b504001d554184005d110255003140140051103108a52181030302e20080c12000b5403040c48280c0d41e010401c80240241c040c110340c0801c3c0c40116492200c1840e400c4040141028050503014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 253302410 1250 253301160 253301171
    0x80d08060d03050418021c0504021507020a140109031a0a0f0c020307150b0d0501021c05450105040c0801050601020c060f09040203040f1101020a110402070c180c03 72
    0x40e42030500401c10810342560340c0610741405e00e001c040491040c1030380d1080681e401c100546a031a4411503480102a107080d010406040074010070018806a181039024054100403000059484020000849250003400c442d14200c00e801a02c18010582c801380c02d04001400d03441d5104070102c281ca10500012108000b142c444084038012240030762012000342c2d1003000a0004102059540c0c1212031011501040c0d408114011401d0420a0070080ba03a07a9000b0a503a070b02d400424a142c4040d03040b51b2410812842c00f2040012111040c10742804140080d0150b003600210144d510703100c031440841e07041c100b14004090701c0e000f0700c0c007103905642c1c4210800d030100b41c0c6041030140c1790007200140c1c01412074004403003c2000d10b50064001c202e51480802c913050039a2541e0000d14846c034022140d0034011541424480050402444400e0443d000400c0050003d904651421002c05041e680182c440401c4d241c0f05442401503002642d8080c1421b00785c0001c0b5800f50444200ba8500ba07606104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 253303660 1250 253302410 253302421
    0x3130b0108060601090612061e03170c07030f03030f05130311070f0501051b0a0303021c06060507031b050a050309130b09130206040b040b0d051501020d1b0c080d08 72
    0x1102d41041d582c507070000e614500f042000905c1404d180d8841c1801450000f0302076500d29080d131050f8162100c1d40c003400d02002040050005180b0749458066448200c141b401c2001c0c8400e544039452408014403940e00b0f0030402c802e040c03096005000071841103004004134101840694503a0b941407104038002600c01c0203e800c0000041113180c11550000b0100302414103050042d51703181c001c01e8100e010f1240b0940c103098190003c011610b0070070301a480040e500c2c00c6c6109902d00841e050502580300a082120410143d5886821201a107425143c075840100b1411404a94181c124001030000c0c8161a034410501401000138843c40d641154011a000b107003043d4001510829440030743d201101000044610044ac3c02003d07266100520781d07460700d40c0302c05541590760055003103009100d202290414042485224494115001c1000c00301110b6644000070341e0b50391600040c01c10011f54050340110580c3c0c83c000342c0c01095105544510072600c9000d00e40e0349401c1c0c142c072000004c003400f0100b00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 253304910 1250 253303660 253303663
    0x30a06150815030f010203150f0a0303050d0f060305060906150d0c03021302040803120915011203030b0a0503011107051e030313030203090a060e090a020a121d0303130b0108 76
    0x1030038010561a282100d5446a01007040b0069403440c9503014007840038400c00c1000f017880114410fa040c0c24000b044101c0c050b0a0140e101d141181c0c003802440c00100030b0020940000c02e955089002d14400b080f8040319075000350141641d640010090f01c144c0051082d119408902103100c1c611810045138184032200070455031810000e4060b03c0d254a261060000d130600801c685c0c05031010801c0913203041d999009140c03031544000320f0304001300310003414010360078004d014501d49143c40c20740c0c55543c1d5040c40001c492073340340704800900b8503a48a030780c101035032121501785005100048c003c12920f00205a581a59400710358111154020a008154070044102c5d5000119490070015411507481c0c0c40c189403840740c0510250150b10080c0404001503403030344045400f81c0660381d0340040c4030b000381d4107100d00d802010302182d0129006104540c446a407001c0000a550380c400e5010803541007802c0c0c06201e0800000c51071045001c00020001c03040094644a00c0092144100b0301c0750360380e40d01009 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 253306160 1250 253304910 253304939
    0x2090601090b0d020f1201061d04090b0705030703060b0f04030b010b0f03180a0605040c080610050f0f0a03060911090a0501050102060a05041109040318080f07050114070f0503030a06 80
    0x100b80410007444005064251a03018014503000340c41120324000c3d410b042117102c102c00f60302c00c50000f00c110b8461403040c0700c1c80505070a09441520180700e1004117030349001300c0100c000c0406040280201c00201c40ca813283e00710b44024006018003e80c0c0700036440c12946141d100b07000948982c1c180b40b0002800a00b030300b08a0342002c03019840c117411a160078072031010b440360303400800d00c152054145c6440401d040b481100e001d244110b0441c40721030300d00f81c40d00d401c14600800101e035810704040200125158001e12030b00418003221103031b02c015270480024160340400d170809440e8500d00f051940421206003000c1e000d40c0d204851a4007181c0d1080c1d02501694024055140103802030b00c08034404509540203950070502c0b48000f05139529803500440c5541a0071070741540002c2000b49006009014010308001811a042c058075504001c401034035910046072003031a04100020703100e130700c004101005031003074550320240c40f000c000c201d424017560b01d030020399030105440d1910000040e409940d0860 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 253307410 1250 253306160 253306169
    0x1060f09120803070503040f060612020913120e12100207031715130212090a11030111120901020c0d050a030f051e04021f08041e03080a020c12070803040209060109 72
    0x44600d56504d00d4000c4506820260003200c3c0104800c000c080080c446000c0c5038094103400110805003491030040110701c2c0c2014042200410500c0740d06008140d0003491486a2480d506020000094203c0860500040814054031a028000d0021241718164000f0240b0300d0080c0d8481144078085074900c1100001a100c115500040403940644ca04007001c040b12081e12410006051201c0b556a50040c180101c5290390b0315080030054008004a02c00e0b20711000c08140c000300301c1c110008407044440d1189141850200300c8010001f1100c000940483e035910325800b05454075070500150151441d001039520101085c00d21042150b81500b85c407172144240b41e06841700e40081c03004039912501c0c4101501c183e800103001060890b224040700f41d11000c00a4030b0f503c0c10014034003803c00d000d03000d000903980034500300c40808420100e50701035035564201842c09001a92204c04054446c80c0058002c50000c590307402042e51010310003d01c02540c426030003910590100d0340c61600440700c42e40507025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 253308660 1250 253307410 253307423
    0x30d02063403110d02040303050307080f062b021203030a1406090606070212250506070f030807022404150b0307090e0c0a0f06090801021201120201051201060f0912 72
    0x2a0744540c4a0381048100302c180c08546403420740c401d50481c090381d02c680c1007540410030000600090307a030b000b80c0d482e601c034050300c1ca40c141d5410071000140e249100714000295640d06e03480341e40f203200a07158a10040035401400c0c600c210716805c02c01c80e100d8004840c08941c0b2454039045c4503000c1d02c4002024410341c0002c00d04416035950208000079600102c07030582c0c000000c88107940a0110412802a6101d8606040301071500c0300840e42c402007442c3d4100b507004820500181000034581d640e600c0c091a40b50402101c640d49840b000c0b4604080e5116110110002607000004078890104d214040c60085040c0c6481420302c206500968030f0285503160954480c1c18100309101d155881030110004000c1a40c1e0300388030180025042c1e859075081151010360b60b2400304242c582001100c4020b01000f0020b42c100140c252020710300640500c01c9100950803000d0300e03011a803048086510b11400000d010303800e9611000c004080038041c42104010508450021401800410980660a61003034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 253309910 1250 253308660 253308751
    0x1506120a0b070804150501060207050307230f0303070c06030b09010806160302212d071407080d1b110c15090a080f010905070b040e0f15030d0206 64
    0x1c403c544281d001403090301c5c02c2e030104181110100d164080d15000703007941d40c0100409405d0408045c10700d02a07600c0340c41c401c01056103840e4010000d0700302429642e03045541c006103102500102e07080d446540f0005085e10040a03001c1480b41d09940301420b2198141d51039545aa200e142c103503036035032050790521020407140c40c0494140344a5001000c20b41800403528082c0c8051824640c0c040c0010385102501922048800c0358114400d4400500d989094007030041c0f5050419024100c690841c0c10703032445402c002801d00a0003881c00071103413603000f050000c1012014003a80542030305401e070300a0001a12041e01554035140000d410003411900402101c5888104e104d024504e0340000c40054200688001c005000389003488604a104110300c004901c40704a86801e0b8103040b11034110109a010030310080c08428035046443e035100040351124511501e41c0808000340340760002c400391b851301c104416081e14541c0885c0c007600802c00d400c50203014a02e0107450100d20400300e14001910705001c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 253311160 1250 253309910 253309921
    0x706060512061b040f06020a0227040807050c0a0608060a050f0f0904050106170307030801050306040f0201031e050c041d130308040c0b04090e160b030a0b010e031506120a0b 76
    0x8614486580001c3e075880c60155a02c00907a1400d0304c80e4080070158004030444010f50400c070b0f05060304c4840c02038035004103021b001011124241c0141020f0880c10020540c0b40411100300000314004c10f00406406089688001c01414010100e91082c0200d07610000020b0a007000303211503140c031400510341c021000c2c1500074854103080c0200207403115921a0b070005406107a601410b001180722038051583c5404500307000c0c01640060b0300040c004e03404503040101194840c055071900301d50908e004200c0390b40401944452440c805031101c1c01e14501403c2c4440032082c080140100c55244420401c3e817009100102e200342000c407140301c100010b540d0340030002445121000c2d4054820f0b9089004c0c41e4486d00a090703690890b4100355206030f41c91030440740d8038804200a00d80e480d00c0b405140f40300c6051800c52540c80c00090304c43c0680b50b8640303d161201c1d030700030107031850314420140c201e4040300c0e8048408150000103589260040180303608000d0400300101785404c80039046011103090341c0301c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 253312410 1250 253311160 253311181
    0x20a06060b07050d0e13021303021002011506080f07080c0c010606090f0b03040b0a050601120504050d1e023c010203011a03090d0c03120203040b0603060109021804090305120c070606051206 83
    0x1007a804d40008c6504c80203c0140d4511000c40440c00455000003803a410b0200f4406664039590041000d0010420400c12802c000e0a0720301d41c04500782c42e2145480c0c64103404650700f8081c100540d6581d5007400da0114072181e10841c14000c035903014001c00d40c81680d0b95604034040c80243e5002d031036110b03014000f543e51290f50704502d4002d070041c50704d5900c254003100945e003183e0b03040c3d0302201c0300d07040000d25a5045070f0182c012500d5040e075076100305424020b0070002c0d55030110f40d2002e07003810b00040e40002440040ca6244c44007030281c0c41c00c5000807110425401e000358400d000d855210401c01030304030310b62039000c4143ca1150961f02c0c0101903a03982c1180a5800c5000f03c2811802c00c4141003070850a0481c80c000346001c0c0f03101e44440241c03030802604060038460305800200303015206011400302e6122061038030380d1156007a10001040b0b03d00741800c40d4140704803001858485604010b211004c00688018804140940020041ea40e1900200302c107200c80980642503551100700402d00d030409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 253313660 1250 253312410 253312417
    0x7110606120a0b0414010f020f070312110c010504120201020f040b0306030a060609020c0c030f030414150304030815060f030402100915090801050a060302030715020a06060b07050d0e1302 82
    0x1840300403604503045030703903d2141c210b00480c0c084541c110380f03011000c1e04010901550405c644981025401c0c090b060300e050001c0e009004010f002c2042c0382209002c0c0c00b00c543d0107400301c0f0902040303683d070340c2204090300313400390800b07850440301d0740a420113058180d8810310076200e80090548000e4a814a040d41070040c0ea00040e00b80c5a060060b500d54900013592842414020400345602513140c61041e102d180c14030b0407142c0c4132030003608801c2442d1400b00011080324141c444400c44400d07038103000c00100700061340c0c8110020250030b00000303101c18550040141485201c200c80f0380c480e8480d203002032040a000d00008016000800c1c00820014507150211b07d81061451070124081e07035a40280400e1400403100c210040394040340d05000d060401e005540d84010303a000d090103503910318ac1c003090340c4a08a11072900c4010f80e690b16070705668801e01002c111160040c0060000c0790301c2d00e010724180d6003c0d8a040782c040c41031382001c4a10b01c1c0120100e8101020007807100b90401070b440c411001a52 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 253314910 1250 253313660 253313689
    0x302060f0a1206030f050c04061a0705010b09040c0510171603021c0506151c0507110d090608010501020f0601061d130501030605130803070309110d0b07020607110606 73
    0x40b08001140711112140b0403040194064590b086403641542000ca0500d07a100320f80901a82c2400c80501541c3d015120b4500d0400204500b2540e492550500f24018510000d90a40c440420018001804004114901035581c01ca0740200083e0201001340c4614900c40e5940040100200011f4a2801001441201c25207a0b04001d494400301519040d044080e107801680352030b540d00c00f4040d06003400309144c4403608d05808202e1414054000002612840030840007210341c5540c00076140502c640541e50b544c0317035800c080341e10081000790043d286032a40d0260b40009480b1200004680d0320015a200c00d43c840310000c0c0045900b0300300100c031108021000b90800d8280e00c44401d1458507620002c00c0d00b604a8080001d503035065140010949501a1003032405403681004407000c1049001200c0c4c001596007030000f00c24490340741a42003082003c02c01c5070b204000b00c0340f42c01444170350b8004900c00c200380c0d400d4440c2c5940380b0500341c1c0e101c42d2400050b0129405040011414146600740c03ca001c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 253316160 1250 253314910 253314917
    0x70e010f0c0f030c0b010603020933040801021e090f10050405121605040c08070c0303140108010b0907030c0e010e13021b010f02040501050a0c0f060509031b070302060f0a 75
    0x884154070389401c480c0061000310300203180c1310411020302c00c1020a450141205150551502803107070001002002140300780d940f40005900c180d060b2140444400c0d44c042c0b40c82941e15140c9a80d02519030003900f20fa00700600d540c0110f5418040c899031030044600d072500041c41d1506601d4030005101005c03460300000c03014800100310104956641c0000344112544003c0202100c2d000e400224804000300d0780483d00890400158202c00384e04000071740c0d440046460030041400e400e084c220701030404080c8030601e42114200108401e4410341182c40102815070b005011500c81010480407961050f070000c0026030081004c100941c41744406a81c3d00100805120030100100e260900f240e00001d008078205441e01c04a4605550a011b2100c0b00307014480c0c114146072910001038814803a00000404012501d8004410007080054508059800c064200302a2a0810354a40c2c0c0c0c0d40b11010900c2003208840801140070400a005404d0381c0d40642802c2c2481d2140481540503001944c001003070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 253317410 1250 253316160 253316177
    0x1d010b270d0206130611030f031807030c03030309060b01080f06060d020708040801051008010e03120a0e010e0601051c02060405040b01090e150a0617150105041a090414070e010f 78
    0x2581e5540090065400340d42c5072020140e107401c0d0b014003600c03049010fa01e016041030042100f23150805090b40c1e4403a00e941c4c482d08501e240d81c1052414810581c01c000e0107074401581c0032050551541c0042813a034031a0504001824401d0015500710340308a50b42142c80031850001203003810070381d0290800c544d54250140c10031444da910214260442d8006c214141e54410402801d0801488054010a1548002c000d5588403038129034407486a182485035000780c0401007080840c1a90268842c40780100003080a018002ca206446610a00c90745102d103481c034080c03504080c80c0c0504029084e0780180042d19151619003800041c11140d107400d814403e025030005480340303850700500e11600c1c0500d001051038010404201602d0b00e5608480c08021260045102c540d184003201d942141d031000c10120703403020306001241c03944100e8000c81c10b40b01d11950002d0305110000c6c054460900120340c28400d800340450a40080f240c11a52040081e04070540c0b40c619500440100d02d981076075141c1b8030038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 253318660 1250 253317410 253317413
    0xa03030e0709050a0209091f0e04210e01091401080a050a090c140306150319080c030d02030402040e0606030a15061a0a2c06030a0b0301061d010b270d 66
    0x11500100d4481c64030b0717900082c01c0c180c28545002c0035544000c1204030280013005c01c92541e559000b1500072221840b42e0500400d0a00200f485800c1c0b031000c10349d1080c0a40c0c051114020003070240d581e10b0902040c0c5106022074821851444000f600030107949211080d60707681041c80203003101402e4003003000e41e14250f2001260780048408064042148980d00c10803408050610340b88004240034020502c1105140d859030303000c14020144a0150030f0f142c82c0074070505002300700d8415400203001a01c000619602e510f682c64003e548214000c44040094030b40302d103c1c00b038884104a40443e410341181070800c0014100c20071501c6c81083c0c1080000344070361540341c0000d08000160b89190441c101040962078140e212068135000d074500302204d03980a00b040c400d0104145103101d007501c660000300024180940c0c03680729a8912030018000d00095650702c190782c4400301031025542c0300c0c84040c030000c913030b0100301c2c8211821105020300001610200585808108041103042035002c000803040d0f50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 253319910 1250 253318660 253318679
    0xe090708093c060f010e040f0f030e040606020109170708030c0a0302070807060915090b0601050a050c12032403031903021309051501081603091b0b070311010203090a03030e07 77
    0x10b4200364584010030040c00d110780a20a58403050344130300d0345403614004000c0000c540441c0820703156405003011112540c2c0345400d4982400030340c001904a1329180000038010340c1500b1030b1407031502401f00b50746c076a00c550014003064407034140090200ca000b00040707070190350190b0081030290020b280c0142840c48550750750540b80d00c0305070192a41904c502818042c81400fa944100180c90420b00308200303c0169503102c800b94000784a18140107000ca4054000750040044421204c0100d055524180c1c0406180c202070b0415240c00301c050400c0131055810390056008440f88520041c0118100100d500000020481401c000020540c0038000c6542c00904100002c015104104001c02da6180c81c03001c0715004100c05240c01d0411002c0c000384034240e182144182260117481c5808503441c1c54030705024080541242c182103420802d08030000721452603c0103452000d1203035403408c4454407c103580500341d0000760380c580d1103a0009012440001d0003a4007000c1000364150544601690b600103e5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 253321160 1250 253319910 253320013
    0x307050c1c14011406030c010801052b05030a031d061f080f0606030c0a030b0f04050102070f05030307030f060e0a150f060e030706090608040f0c0909030e09070809 72
    0x4842d03a445855014103007403641e00256000b003040d0300410110004a000900100041c0302d070034011604a181801c04000c01c050103e00301e40c0d90903c4084200c41071614944e2940142c0c0740c3c0002a103418070300b41c82c9c10403240c4a11180003405005261a0302d80307034410100c0201920b10060541200d001c0050080401d12000c111500840041c00380751904006140c1000c2e03010004a1141c01d200c4010700000720428100e40d04120010807022843d41e841c0741c00c900900c504000644010031412400c8100a00000114410101980c040c4103071420401d640c4282d030010f000b4075035124085000140f01e50070030340c04085044243e4441905195031a802081c0c41d00c0036070081c00000310305c00c100d8400c500b41000210014500342c50541c03805450550010501c5030080d200501c4251410442c205101d07040989801500300e10400300000d40281c68040c003c1100f001e001801540864000b69019025021580c071440502c40036141800e1103212000d005003070801c0d0074201c130242000e81c0e0707800121203442 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 253322410 1250 253321160 253321193
    0x61e040b18180f071701201b01060f0303080a151202120c0d0f030207050612010e0f04081812121b010b03030403020111101a0f030307050c1c 62
    0x30185062000105010b40000d1160305410b600001d00001402c00024600342150308070880c292442c0754011540f80035080c09145042c2841c0214180e81c1d103160345100800c1e06104104400d0a203a12034542142a2525446100d850050348803082002c00d001d030b44025440409980300162215616031000d0214640c0d400c9031004c1d81402140d2001c5043c0700c05a46a40b98410300103086d01082c400002d440602d15400041c10322101850700c10801d40204541000b801d0004c20083d110b4681d00c49811681c042441004e02c144440f201054a08421146070b43c0100d03081980280f5042001640c800b01030103d180040d042056541d109030100411b00241c0e01c4450064400e0380e84100b1040380365100d840001011206902d01205031040c0d580000880f07044903428200b8070119a825030185007007020110106107454208541c1d0000480444c8141ea8408070856404403208240800d06541b8054050300425030382c0031a0501c441e502d0301400121038410001c3c1c41400090150b41d440e001440780030070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 253323660 1250 253322410 253322449
    0x30b031e010f02091e0d0506010e0a0c030203070f0503131a0603070614030a050c04081903030f020a05040509090712030f090b0f1e0c030f071505061e040b 68
    0x124203000300303801c0c0156401090007000550400700c000c0001404070741c410f14890510002001100d8131515018900980c80e41c00c0030039aa640d41e5202041c1300d070f40e80200c580100c018680910346000310301a00c2540d0103550155074500714130440e81820b507502c0e40058161420b03071010340000300006403400064000d01030015000d841505100c001d262400308180c1200050044565071007807140451405e6039840f606141005c1840d0b2528a04604144030303540017150940034003006403030ba0603000390403140194070a130360401150768040a00001ca0050602903000a0802c00042045140c881105a0042403820945040c00d0740e03207115000070212540e00320081603200719070390f80c3c241e0400d440d2001042051442803030700c2c1ca000501c0a1505c1a20005031232045000c405881c034182001c1900c0e0050601c00c1100e0340d800e050301004000d81c102520031a460b80c411a0480400340042c081c05015240240018000441000100c4010303022903204039045540c2da0240350b8a903480e15841e040030b004d00f15 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 253324910 1250 253323660 253323703
    0x5120d020711100f05030a0902150705070e0c0403060b1203220608040b0a1a03100f0b1f140d0609020408010b010c08220305030d0b0a09060e010312030b03 68
    0x18140d54842ca0400c41d4512445411107024802c0c1e0704100e144145610501d8000c1d03aa07a40c60060000030406048065004445019042848000c241c003c0640c036000700d04a41d603807691040004040f840445101420781401d000410000f02107400c20320306283c00800e01c0d00c4c103002003a0214a1504503a2035205810f4100c4061820005400d00703180103071a81c0e14003150b00b843c1c1030719058034010016001903180380d594002e10544140c0304081c640084801001d48016a40d000c2809000d05502c6907150312031854100d000240f4900f01d20354103801102e40c26502d5132080101402d0f01c131402c0421441c0c0911900300700361591113126115010240c051684016203c906241e10795084500c1c42000c135044c410a042250042000c1d03406950b81c07148080b0700ba010145200c0a0905441d4959000a08510021801c0d0540d1440e903041081e11031419110265059518503207101179440364440e086414203188018004991501405101282642004145503500501180c581004a1a107200034803120 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 253326160 1250 253324910 253324913
    0x23040320190302030d0507060902090c180307140108040c1a070b220213020d050c090f100c031404030f0c0303140903060c030702011b030c090b03150103050405120d0207 74
    0x44880c0011245804000702031541160b011036a1144143c10900521030086030850802225030070600100f507000e050040b0030b081c550203403d0306421002000480c803a24140c190401d040002c0e080d01102ea106000341e00c4002000015200c90034003820995002c0c00c00040420309000ca08051140c844404129a1f034610013030605000041c0003410756010200189094007021100100c0103d04640403200c014004852601000c001c2c0710383c4014031301140c2003600b04041c5811540251403e06415503c0d0f284a0078208100000b60032108404004904074507031090101344640b83c103050701250382410350b2515480c0d454003010200320900491b4038040c103803408d1040540c00340c40080d48800034010903041001c094002130312400010003200d0002008030005649030710075049080700c5030f00211180b004140021005026202001002000c00c41d10b940004066840800302c034401e1006001c10f0480000001c011000380a02030b00555051140d401c000303450510f85802002c4c2003500e0301006035155200e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 253327410 1250 253326160 253326169
    0x4050703141f1403061f181a040c0807050a031d100608030922060b071208060904020603040f150c03060816030203031213050105010617090109020123040320 69
    0x1a00005030310b400390344600d03103a1340f0001882a00000022545445003000c45882c1000340d0040e4400c10340e03001c1d80c1c3d42080240e00715a0041185401809004895a1002051009548001c41d0f07150014000c0ca0000e0241441400544190111440c0201d9020f0b140d481202c101110404204810f8000351002000b481191160710024883d1a02541c14100300d040007901c040c8004101e0108268046050800214642d0100014204e02922a512250582002140256540d4010001c43c4140c1c010480038507040c004680319075801002685196515600e410400f00c2c0740030100c40305800c0c01c01e007202c000b103140509030480030280d5000035042e1800d00c0940c6040c3c03918918501c100309400c1c0510260b2030200483c0c58000750f005006140e80c032200b00e20034020805140140c219440d040000c900d82e82d2104882e00081003000c00384c40192642c10055088801d0008001c0c08940307102d00d040c07882082d03061502100001086500d0800ba920780310141c1e4150140f10b00c0059402410403800d00c2d151 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 253328660 1250 253327410 253327471
    0x1060b18010318081603050d0510031e020a0b070320010b011404050a031b270b01050c0a03140c01090b0103050f0a0b0a0b0a0510030c03050a15050405070314 69
    0x41003000700d400783c080b44c59007803080c80384698002d180120060014141130003101120785485180208200c1481c1c1070300703081180a540d0100b124604071114108180c502a40380300c00e02540c0040944282c0d41c03030808810916880880201e013401510402510003900042e681043c0c07081c1c000c00402c101d4045d400040c8442503029840001d071205100900c00c9440d01c00b1264292944084203241e01007241c3c8000520a585900c0701d06080d0384902203902ca811600000144480c0070034050104004201c01580e59005070480300d2060b600041021020a214407030700e0450383c40d68448580380c41031150006007510b00500094034040c03200c5004004200041105c1c01401c4141005841418038a0b030b290411481c001e403000d0002078841000a50f180d07940380c154401040014403030410710a14040c0035025191548a0002091030304000030030030041405400c41100503101e5034060681800f0810004000207011142010750b03d138000303030b1040070005409014988600c175410007a800c042200e4441034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 253329910 1250 253328660 253328681
    0x105130906050f01090b1813050a0f080706050106030203090a110105210412050a0903030e03031c050712020f0f070602070b04080d05061c0b0a090804060906020f01050f1801060b180103 81
    0x40d10030030b0140d003c41847d01d050704040c000303500c107400c00c05504000c2d1030040480c10107040107009040101c00c018014005029552007240c1c01e000031780c3e8500041c0c00b20b000413140702c00c1a400c80c06101d40042c420341410302d40d9000c1414000d040020103c0c50810502400690100c0d80d146d050501c0309000c0e281982d07a00d408002d1500f103180c07107410f40c401001144540300040c144034159210b031540307a8040c010750b0215101081c20b13a6100120b40030301d4002e0407041d0b66120208920481214050300345000b110602d61b940202a45440d01d03040d41810075034810503050b074040380d00703004840c00503003d1024280954010b01c0e24070744131001242c00b0300494070083c10051089000380001c50f00e02112981e1f1868064014030000b03a2581c481030410b015110054000f0f24a260004000c1a0950400035400a4890b10340c00c8880d2520306116080c200c41d816544501001c00244c00524507900381d441c80c003022844000041150b581d24110b040c081d0704484042c2c040c1c06028012490207503850f116410520317 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 253331160 1250 253329910 253329919
    0x70f080705030f212107081f0324060f120213090b04020603180a0c0f0902030c0909040f060c030207020405060409020112050a020417100c0203030903030105130906050f01090b 77
    0xf1150070303c00450303101d03003c42c2c40d0340101c0340810154841040d540c0b80503461a4100080c803c3d1b883c260740010708800b411100000072201071000c2c40b60020100c0660340070b03a036200040d0602c85c6004c4800c90508407000d050410311b191510701c045400803800108030024000c8659801700510380744104142c1c10751040300c0d035042d640341011000200d40300b0107456410540560310142d69490320080588504d80700f1203520205e102c0e8104642c100262640304400b101c189a4507104510344680c40f4500381d10080e50302d80c00281c014000c941e070310305d03005441c10b4000d03101e811307414000d14a0350703100e43c195003007081c515011a0b80460080c00303508150164580c041c0b4202c41c10000803020361b002030308101482c2c211501c50b59603003000486010f103560480b4041c0142c0841c075422421010195582c07010f012480c180c0c2c0d6410100581c0c2901e0000055901400c9000c0165017142c0c00d01046c04000c064140066203007a4071641e52030086007403442140c0c0902c0d40310180b508258104200c3c0e00a4502803400703a03014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 253332410 1250 253331160 253331173
    0x30a030318230d0f140927010501031d100c05120f01260d0e061605060a0e0705010f0c05031902060601110d0f05160605010e180606010e12070f080705030f 68
    0x46075100003002c445501e0381c0e0251b5101c0c25850042010411815400d100c03c10403100c028000c4c106545282c3e0407210b00741d80c14401e841042c102c00d21918000d0040422a42c0542c0f10b4560808542e0821070400c4414645542003400610b005000214103403019400000c410006104804442240d2021410301d2442d80f840400390036202650b40d01240100030802200107802c01d404d070703200b008039440000040c02d00c880300350701070900300c3d1500300a655040340e5900c1c140344a01440b40114404003251030503115111080c64664050307072400d182c0c480448841c0420401084403e40d00c101701c151103402c6a00401d01840c000300058000106141d0540060340b0802007803101c0c40d40460942c21100e080e107012504c44811010f8134041d14040e0100904007402c0c4400421038540501c40ca900c6001c480c503031842c1d10310900000716158103050303170640e00107560f1200380200e030b00302854014420010a401c94031201d68416000d581e0703481d203400c404030716001400308100c103142c104401030544c1d4030000600030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 253333660 1250 253332410 253332437
    0xe010807090e070315082503051203150301090c1409010f06050901051c091a010602100506010e090903030601020d08010e040201030e0a05010c031e0209030a030318230d 74
    0x440c1c80c1e10407410380a081100080707580348603400c02c1040180301380462400c40d468180e02c41d1511441040480c014006d0300003001d80414048240c0c0c2203980001c040c00024000c0d80d21076203140c0c8010104019038000748040103140d2000d11409090500486068507110b007094104c2d40c01090288401c2c2c07007803603070380014001d80964640040465802d808c1c882d96510f041c00044c1c0d20b034046d4002142c442030a0305030111301c00009030085034901307100d51030480c806560382145c00c1c210102070040000513400004000b500e01181d0b44629002541410010042100310b000075420743c0c0b040380c0091407600044144260340d6010008a034000c501420040120742c10000c1d04600b103680204041c1c1050740724801007080646c140000d1030603642180092180c400070000140140c008080c5d01d60114800c00001c00c0c041d0300501c261001024001d010385010300540c0c604802600c00e080c5030041c03161140b0000303030024050880841d0071401140c6410500d14005003c0c600b8090090301c84401e0051f60709a842 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 253334910 1250 253333660 253333667
    0x30702090f090a1704050312070b01030204024f060e2808010b0a0603110703030905010b060c25030b0705130b030106110607020d17060f060310060e010807 68
    0x80c0e0100e501e50352038006684aa070394a1400d05036000180c005410b003116280c150a460000b00306442003034044417114283c04204a00b21f100381c55000d0100c0381031900602c010302d82500100220141c07041200d842c0c550403500081c07030645450200c04010030900c1030740c00c80c524040303004d111500c1c0d49d038461401c0380c588500039041600d206c484500c14290211061803c1da0107034064505141010341e004440b584800010f4020039808060a01c00c1008000000708140709004206a0401003042d0505240c003650702a005030680483c2100d0319501c0312002003540e140c1c00302070b09a001c4001c0080c000d03101518180d5414203000e00203124034402c1650244082030103041c499402c65a40d29119a903042440c2940c400050640c00c50a034518000000040041d4058544202da11602d420380345140c4a001040ea654460041078a000c17032a5000c00105103d15010000c2d80082d028242001c02984c480028125920071280708608a0248009004880d40300c81070a4984000b0700300148603042109000c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 253336160 1250 253334910 253334929
    0x12060501030b24070b010e010602060a050423070b18041104060203040b0705160303050301060f020f0d051602040501030c0e090d140a030e1006061101021804230a0903080603030702 79
    0x1a00d8403041042d0844200c040008884107243c212000c528996120881f41c0000c00081c07007001e0043c4200740214891148600c188c030f0180c0c1d4021000380c507030007420760b82e007840a000200103080c1c2c0c020107000160010101c3e008104401c01c10304034031902d20080301004101c60680300c0d1100e4801040c8014000316800200320b1f010750310200a03440d203407807041c40c00c245405142c0d0001407401081c0b620000406803c60055030581c1d03001e40700c0c600c01400400c0b00701d03514840f40415490030784c040440740000c00d0140000f050b5126a4224101c0c0e149003540104040c2d500c02c0e0710454540507040340070000c5a5407204615007044c11030000d001c80d010b903040010010310703030a00c510700014070000750420200c0c025440301482500d008190749484d1070050300ba100900b060301c54030002c00d100540395000c5250600c00c4030b008030300d406d082c1d480b0000e11106000c004e059011040c40032404815071610400c0e102e000c220302c581142c0c840442c1c4200d42d031500501c4c81c400504a14069030050104030010307541c01c00704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 253337410 1250 253336160 253336189
    0x606031a04110d0207050604060b030f071710110403120f0215060a0905090d03200706090302070e0a02070c27050c0d0e06040212070308040b0309031912060501030b 72
    0x410710b03200501504580c0d11455645800b2a032001500e80100b09012662501ca580614420000460300b48103060f15600349041402e00742d0800c05c814812040001242080304d88480c0c210344040351030710315580c200d80625a0300003126034003140400421000b95030722003c50f01d6514024128150040001c0e40e40c5801540b110140542c0c10300007035440d203600214600234103c00304c0034490b6080c440000d580b01c112400050340001d05109080c00c071040323811061945000000d052914204041e00d403c001440c0444040782140a4840c0018445041e00501c50140204403001a900d080c00c1c07400613900300742540a50038a210031064840f0400d14039211000d074a00a500c040f405603621b540280107807080e260441946458403240e0940700b000041e01e1482a4402d40c4d400c40076007101d00d0f1040d030710725892100600306041080140061a519400b854000e001402103900f0038007034a410035240341002e910360000402c0741d84155011070043c05014003c0c0000e0804006034001d6802080c80e44044600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 253338660 1250 253337410 253337419
    0x608070c02030a120f0e03030412020f041d0d0f030b060f130803031e0105030601030b06100c020a0902180a060e1002070902040801050f0f0708040f0201170711010606031a 75
    0x580e00103545040c00b2080380594414609541980c544002500c1d44c1e0000c209030001500e0f400e002402401d0000c07c4405861051a050911114650801c2280c01e1501801134001c1d46444001d4414070207010070710400309101c1c0160942c550b87ca0b800500400452180204050a0400d0402c5039202c0070100c8009100080343c440d03540491001070038a1500c2d40c0c0c006101c41c4000001c005180d40100c5c2d480b040b0391481800c0c09591f9076a4020107541d01c00a010190610701c0980204140303142602c11190585041d083c084900c100075000644550480d0340030180c00781e000a010503454205550040f5030303c02c02c8400b00446420302d84024800f459010030701c3d005c0c4200e0407003569080d00802c0890001e004100d400c0d0742e50b5840d410058080d02c0c05950b00e555007070091300461300000039035016070312030040c5079a104240d5507142c485110040c04038401b80d060241c074001601c01070112844083c4184215103a00b121810800820350031548985d004000b05441c108068040050300e0760900d40060007190b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 253339910 1250 253338660 253338677
    0x7050306010c05070b0406090f05090c091816030b010c11040213080a060b12030711090601030b040f06050a1202130507030e071d060d0206031b0903030d060302100207060807 76
    0x40e540b2201150340500a485008000214a4584801041501c00c150b0b01d00400b00c0e600c40e8034002984060086561140342c644c0054001040d01000d4031006c0c0d00200b032035610248113a6000c1e426903068480003112403010400982c0f051700741c0216101000e0a10304070380e51703206a448104035068021075240c1700fa500003130481c13801c00340035000101402c040000d4070354032051407500342d005016101a8a0042c2a500f44c03800c0207190210a0707a401c99040002d00ea0001112420401c2d030010081580d8145079561140000b46d0312540b140c010780e030b080d500b40024154140000c0003200741840d40500794400500d11104010313115403040e2107841481c10b4000c1525150400281c0146c024204200c1103172240c0b520014665140b40d441e07040103c800300724107000d07459501c244002d45c00c0340e1201035007085040010600d01c0410988007041a2005094241020380e0000041d085502151125941a455071024015443c2407004061140100e000411060349018400707003607050010300303040a010380f11 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 253341160 1250 253339910 253339921
    0x31104080303060121061706090304050a09110d020409050901060807061202071106070b04110109030f02060705011d0a11040207050a14070906090501080c030c0108160c080a1e0201090b070503 84
    0x59445c4051146915024400613403144186106440e0042c0c1020680c80f0303d401083d4607800100444013920320140000341c080e0304200009000c0c2007000c1081144000410a1012030300d010700c043c0001e400200c1c4081141d0515500366425181030790842000382d008070404004013130300009404210304c08075401607225400360070802d0346132002d90401038001030300141c00ca0800003009401c9100718440c40180c455a0040e20044880c1001b9010040c403003000380c0121009031034030a0242c00034511401c008142000000512403c082604000d1005c560116011200300900c5c02400d85503000151030071420582181c842503aa41c12840c1c3c050000c601455208221100520140024000415082c44000e641e0b91403540104001d01c01c91401e40202c115a0a451402080301c3c06660016507403820203840f007200c4000600484121402031040305828a40022606009060742c28180d842e880c110040b40e03c10341280340c00c036405c20340444e450318a81d0070005041e6146035800c00041d150190b1071369100c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 253342410 1250 253341160 253341197
    0x522060209041113060201051506180a0305030408010e01090f1e12050306011b02011d041d01050f011d010b1608030a0b0f01030e030d050604090c0e01060311040803030601 75
    0x1c0607030468010307083c40c004500c001c0704400141300003511840240d4410342e4504040707088400944007802407903081c80e01c0006500d003410203802112500342000e005622403500141442909900c1100d0380e81020504001c0c03803000307106201a680202d4000e01c0964020365a80c6500c460400e00241a0f0707404445510209440d180c0500301070794000c0014111240501d00540140c000300c030224009110b0003220210802880c8241608a6044e110f196040710210340d00350008a42c28105904140d55400a1030b09060101c0610a00700103000002002e082c120901041100140c000c4a1601036140c20107400482c5034014034110707022005240e407181c4c281060340c03200c1484004060115240402445010561a44150b403100703c21100d101c0541c6c81e61005500703513006403070f042c500c44d0401d200803882d0f004150056940f00303400a000080080c4155a0b802e8210301d40c5d041522501c01040c01408881d03010320644007028405c0244908087c501400d03143d603440300034001410071000b0b03030310300540707518 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 253343660 1250 253342410 253342417
    0x7050d170d02030103110103020708120402040e030d0e060a0507020a15090c03060b030105160905010324180f0b0607030302090a15030b090c040807030336031505220602 74
    0x304140300640e1216501e01801c043d400030701054842440301c0c00341500d15802813080721596644010b000d820201246080604070900601c2641c0098490750342c120741c04d100380000c102c250f4540000040000c12426980c1c1b0300a0010030021402c0d10f41400d2065098002450a000c60340c800c440c004e18400601031302000d03103041e07031000f050f80e19484404070405ca140e41088002e03241c02e400800c01070351200035101c682d080080401000c9000c02e0b0050000e944640c100c0000c914102c4810f4091310014216811240456400ba00c03030b14125895090001070140992002154140414081d148030400022454072032020000c0505900044100b06070719441009c40c01040100b80882602052040160242a0b05425280710780d038240c000421780300244041d10299003102d80200300090641e41c06407515001c5000120f09800c40f148400904003215000320384060301081d8000c92503203949081031342c0d80600305214000394185020020030200c18144650ba1070a11181642180450f0070718100074030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 253344910 1250 253343660 253343693
    0x9160203090402030a0c17070e101e17100e01151b081806120f0403140403030905010e180606090402071e020108010506070503031302011101050708040501061707050d 73
    0x83c004030401809201607400390f100000e458885c1c4015888080e2154000d1000b12042c41c00f196903081003045a04200480d032101244030704000300c10303150442d0b0103251b00e5102c02e10903001940986141110300001c1c1c1d00e840d04903030000305d00c83c2c6542c01e0180856545605002d10441c6005440c80041a60f1007010412644009442d08102036002401c1c116000d82c420707070081c000e0922203c10310110f4101041119403129100754040c8183c0c40d4079010106102020300306070100b0044e50111a40b405074440184002e51094881c840701c2d500d400005840203041501140c4030f00096002498802c481c1420503500010031240c550f0b903410f1500006d0003e005e0000081c101591288420b040c03c0211000c0c400707000e0007605ea05160baa170302d400304102c501c12908020442c1d0000d04c0490001c21500b80c2d01d00080e40b050404c2100d0f080c0390400a42114812900940014102800e2000744002803081d10050061000c102a03000d69041410390b5402a502c03455004d40c1880c00203105000881e50720403d481b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 253346160 1250 253344910 253344919
    0xc031302090906040b10180b0406030c0902030603010b011d010f02100f0b0f0a0f030312020706090609061505010c0201051b0106121104140411043312020916020309 72
    0x41c240340c401243d071950204c0301243c0d0081400041001c04020a0740c00c4212000d038a076200d9428a801c50840c00380011a0b00340b03401c40c1e00d41d2000300010f14000c02420240c426100016240d280400400d802e686154442a042c403000ba04185d0003600158030641030b8490a0811100106561700c0892400040c89881103490340b60406100d6a240c4680084a85c05400c42d03680140030056030800503030004034414103080800d082c5080000a0041003010340c005d208010050800d800d58407000c080e201003080071600c107a0359441c500c0401544d4400d0103039180c4814000d82c131440c2008001b03030a03140400c00282c18800c02099000c91000f00c004105c0400d41e08074024002c0c1c0d50759608000310390504a20455661174120000c0e049414980b14800011003030f40e54044190301d0341e45800030143c10005415811a844071304c0c11a00b803800704208000000c60b48440390281c2c4045011084000c202d820264808010702964000740e44d030b201899402c1035003c2202d10354000102d005901e0f6119107840160007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 253347410 1250 253346160 253346179
    0x3c15080f040f02102f070b0a05040314210306190f051507020d050a150c0f0804050c030f06190219050f040f060f080f10062001020d05040212030703080c031302 70
    0xe40100545c030603043c02c011702117035070154586c1158000d5025000e074540020320140000c101080c201d80e43c200c08003806105442c070b5007101914542e4030411940e0300400006000060000034106083d440114034080480000310078106101010b8644141c880d083c8959036071b0100070100c0343d800046440c000c2d80240050000c1c88940380c4a83c494500c0300307040d1542c18200e00100784030011405103405440781582d072a240c00c0703a0042d0550380008043e1056031107110302e0900030076540f01004280000f08c0c028000b00454644207a028902c01d800b2407161684c81c4c014440c0b92080740310341007041c0d81e044260500e5601d810305d0603200212801170798489910b80421050010700c3c0703030300031100c0c1044030610b640300d440541c0c3d20f80103101050400c0d2030102c0c0c0758800d044100031440c8a142070300030041101041024038901141201d003682c0040704000e921680d07501c240011803920381500e00c640d0204101070342c203082e601d441c081c020042c01000030740790b0f000000010355000e0340f10722905580d6a004202000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 253348660 1250 253347410 253347467
    0xe33040b0405011d0304050913080a080105040c030216081b030d0b190e0f040204110a090510080603071205070312080702060906013c15080f040f0210 66
    0x8a204161801c0d203480d481e04007130124440300c012030006044001c900441c42e051404050200c440d2001b001081e044000303409100028045200a22032106156540c44a5505080c2044100c640c0019900c05240c0b040000310105504011260004c541043c0c10603240c0c800780c102080c220400a0300b0b9503050100146100e1020722035405405024000e0b90011000d8008840d0480c07429507034060440840030200c00144044403003042c1d07652040c80a00085941900702101d0041500010303480c2000c55100740051020f070a003028040010020351400300141d0800034040794176821240641480d24420403403040902130108980b50055030300080d03030065031100c620001c08001c803d0302e40c40010b004140115942d014001134640c162a65844d48001e41000420000c46402038030702c0c070500390119201031940d0190300310440c00c0240072185120ba0003d440602c000d020210041401512402c1e40c018000861104802c10303005035810b41d03856400d07058a00e070640d4042032649079840440c100c00350700354 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 253349910 1250 253348660 253348673
    0x90c041503110f0f0907020a0b1501080a020307090e0a0204030c0e01031401050702030906090a0314060103050d090605070602090402091914030c130b150406021606030e3304 76
    0x101224050303240c1c0002110a8410000030b992910455a440461040c0051300c40c94940809900051240100e400404403035403010b40401040314801c0c1c1c000080c0d09101aa541c0140d443c076031107032080c0f400318594602038a015044401d90300664a15000010005481111650444002d1608000b0f4290107664481c603035024220300f4001140c840354000080e5150710414040c0500692854001e1410080c0c40802e203d050741040303958030b900901010001000c1203111038403824009251000c4c10041d810340c2890307071809481607511310400140034010040c43d50311005440286510100c0546e44042c8000000d0107802246d482a9002c15040806417403e00b151504070101d8841405803d03456500c1c030f0400da1941609100150040b0350505920412041035010040e55440149107941046001011b07001da60815001540580d1046039003030b92810400784803000070803462a0a10201034140c0d41141c495141401044009d00c00310030307441d029801641070200b0440e02069400203407a00e1705060 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 253351160 1250 253349910 253349951
    0x5010905010906080d0206070e0103020d3306091203140d06080d0201020903070b09060708161506051003050c16060f05010e0c0f0706092102070b041a03090c04 70
    0xe01241c54204001350051010030020010413031a005444030f50354820054800e5010f80c0201030400d54204a0501c04141512998850414810549450000010200e0000f00d03c0d41c1241c890380d1158901004140c1c2c0c4081070748180e440c0420411601c2025160070303900c0d40384540001c0f0001c040410082c4e07507035905901c00e50444521004403240b16051020913400c0b440f441504135015040300d81d041c0045518400203140752039000d803a952030070145494881d0180c00c10380810310380c55100c0c2c3c000024011711803403804009800900402440d8680741c0001c01d041406a640828140c40e040018901c0c841401510542c0e82c004242c0307005200540303040f034028030f003464501002501e40400815102281264540704541d4a103241303181c002c2a01a820311a000030fa404c440591700c1d03115200004240a0f450102e401441a1200b054581500060308064450700300b074002007000c1c8010060003814144084020080c45942e40da03d0b220b001800d4200b036103006109401030f0a01a00d0042d0343c00c075120700c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 253352410 1250 253351160 253351169
    0xe0102010f05091c09210c090606051c0c1205090109020301060609080708030a0f05071e0303091a0c091e0306090303071e0215070509150309071a16080408010501090501 74
    0x880c2d135801072502c0c207030b8001030700d4050781c655599521000400311400c10414000e550080200d1800a80e84101c0c280c1501c6603600003030300090011481c038902c03502050709540c00040240c4140580c2c0c910000c0140a1520b00c3c101e0503240d500c3d00081103208000707606c4101d549401400900c291a100d101c0a0018a01b0340305404803803042c40d00002d1821004410384880c0b0859540b42c038030905100d08200c40a40210b042940c402e41c1203c50708410751081c0e590384e509640b00b514046681d21250a00c107098812052145280414010030888610064400c944580900326102e403d89030704119452040c25a403104240c140c481d0905000171440000091441420141e03902c180d0501e4600d011101c0720105100303200940d21220402010030703583d0140c0c640c000c44034607110303080c0580000014400f58800d0103030880354400000b4842c402100b80301d024040c1c44440d04600078102607100d460480c0c840d040b0751080b01c0c1448243c1d9810481010100c400a0100c00000d00c210350f100ca860b140180380031b01c41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 253353660 1250 253352410 253352443
    0x20d050306060d02090d20010912080714010c0e0a1203020a0b09030f0309010902091f06080a020c10060602010c02070e040f0305041208040503010b010906080703050907120803010302040605040209060304030e0102010f0509 97
    0x1f00700c042c0d88948500c0b02518400c80c2121010138495a030070f081c0d41c00c050310444c1c3c100c5040c020550305403070034460800c24820320b0340c60b28013000c3c050b000c0c08144182c540142c80ba5407007248a55012940000b40420300f15440055400c00d40d6078000603509600039128440d22460000040c000e15000540000040900031039201e00e0580b14078405099140b01c6901d0020040c0c07541c24200010740c000d03100198031044c0d443d0050f00c2d10000c8000c1302c2c00c02e22408480141c01e640e504061104550900c00c491300c540782c03400281001c0d42402d005d600e2505000b0002054400200480360030544283c00b074400a000794031300044040094070704404581c00c20b02400b03010398648440c0040d2980704000780811103031640c0310600b942d190820200d0190038014940141842020000100010f40c000b1440c1c5907801044201d48039415481044103980c029408203108900500011101d84d070307400120b0760081c7d070504010040c2010200140e02420419564410180ca80820451107613801305500140343c82002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 253354910 1250 253353660 253353713
    0xf02031b030c15041b0e1302040906180b0108030922020708161104110307032c0109030324050d030207050901140907031407180305032107020d050306060d02090d 71
    0xb85e1405803100c184540d41a5030b0303030240841e506c0c1030090700500d40380d400a000410402044d4913070000740e03581014004070b03041c020802d80092180b090b400c14050905540170350b00d0120300700700041c10030701141042e4040000ca001000c030720a040781d04845030b440d0301101c3d150f2100c00d000f2070303000c3e000c40764031080c0c65103094084111a549004d1184500150003202030504507250148102d009140b1040f83d07a4512080f101d1101080c01c400040c01c60300d0701d9240c00850500303664500242030b11348414070803009178014503201000c000c0248008040e24420b40b09040c0b90300d2941012460403111b5404207410141e10300c000700e03410a140c1d40340d00140300c01740d44d903000caa12003032021401ca0740342d000c01900c04200031020940a51145c140a008500003048044455803203844050842d440112010741c5e003243d038019100e2104a51007182d90015031030000e801a844004406003251000403c01c2d803007508001128414002941e06641d94500050050402c8000c036103030a542944618031421521070051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 253356160 1250 253354910 253354943
    0x221d0d0f0516030305060303120c13052b08040f03080403020a0b03040b0402041104080111030f0717161101180302160513110903060a0b0f010f02031b030c1504 70
    0x25421903030b01e01001030700c2c0c05400000c1d481c01c40080c5809490b0301e80c5400200928520100d0799032405015155000c0103607510030b21074260206907040c030b0344002d00500e00c040c140c68090103071110010207203104643c03180482d40c0c91314050085100700d400205200c06e00703000100071b1144102c00380c026603100303441c4812103e85408402816000c1110300414400380c000c0010014100b540007113688501226580d4205078941000c1070a440f048451941014800f0007041002544641215001610f034180803e42441e8030400c400f0200009119240e2150003110301c0106901c1424410144001c0e04020058542014601c0208030700c011000e80040c4180076100500350b035080d0040302280d500602d0025582030f2842440d0150000000c80b10303440340280040c228a44040c4046845034402900000761194440108040310000c02406070411510b81088030070940c002086918000714000c1400e000000d0603502d41c990711803031500c0802801541018032030b2036401c010460280384200700e81c584c84c5129 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 253357410 1250 253356160 253356167
    0xf06010905191a0607111c0203030a0507020307120b070f021903030e0c06070c092405013002040905130f020d0305040f0611010f050105221d0d0f 64
    0x2d980b071280112510200b956001c2c9941c1c030405042e83c22202c0d11500c180f007100007803082c0d00010004e56100c020322800c1245845e00000d170325050081a114143c4061443c4c0100eaa640070746983d950034400000f403d04255a000c10680300103001640326001e5890b11407408907412001900d400002c5031010300002d07484c500109500410404400000c40b04174040d89084000e0301e80030400c2e240fa40201c50612006480d080b0041c080b59020b0b00c82107400ea440c18107107104949070b4200003140305140510740002520801d0741c40c012554240b0341a07804a8240651600041c081e41411141d41e05514041c01080c640f900a0011103c402c0c10070442a500e1003000e501010003594002c18044070201f1010040c6095642490340a000b86001810b00380ca45a00e0382d40c50805400410104a0040c0d8000000000340a01003400030050010311040d403501011680152020080c212a08a0744450031145401940482109185075445c01044055000c2054a500c1c2c905041ea00090004007030500c2e8600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 253358660 1250 253357410 253357421
    0x302090f010801270e0f0307021507030e12030c0a0606090e070b0a030e07080d02060115031404020f030a0203010203130201020f1b0103050a060504050702011d0f150402011b03020f060109 82
    0x10b040b10325455074a03100550507040010213010b400300d0703655140d44905050100a40791450354140300450b1ba0380385900400420030b00707251034145404e5007006040e0019503c1a107003254520b06403003482502986144003420f5002e40000321a241c42541e0078a400d009142d00b04c00708031503210b80100200d01c1401c0c1030503110704043c003515813004405c0002c000340324829444042030f0015001500c6071151a8403540741400401105940103900042c01440303040300909095955141c1810100310002c0700a0001c01c1c0300e100144007078070038220748007041e1035520144000070345030f81e00034001c65980c948400d40c880c180c0d00031070341039005105400c0c525061280c00184896244808410710b00910380040045010f41001410300607801c0d200d040024403030300d130342c09440e000d055150000b15070320a910200018000100400b86003ea0008417080c1c84008080740035482e94509902e021003550b128001a1020319522050005904900340303071005060340071803010803007e6482c064858a0342e81d00c4281042da070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 253359910 1250 253358660 253358669
    0x240509010204050d1b030b160e0a14040b220e0c01022a1804080903160f030f0816051e010209090c0d270507051503040206030a020702100302090f010801 67
    0x10703600804003041c0a081740706410391504008907038950700c1e980d500c10310b014151404400d81150340c10b41c0c3e41079900500300e125000400e491581280c1d250141c00c40101c3e060701180341c050341d0342d01582001510ba20554550b80350318a035424130507440008101e4018141d107002a031203070040310341a060039840416100e204070318190104040c5400035a046c540204c5c002c00e040d0340300d001d47c1c4601100711a60311983c0e105d1030241e030b25039884805000505041c0074094080301c00760142e003202400001091251101a1b941040d10400d800400e031a095000d485040100c0745031660719110314042000c0044c1d03441800316540105030560f0503607282e9900781d025130264694014440b20009041038002c40141c00c103200b802e04003140070701c10f003d1001081510607588403056080c0352071840622000b0045d01005003016120a1b82c0d41c016880802c20714040500b00a110320000000b0171440c03074903a010f4808298000305401440200c1c8a400750003944102c8a09005185c101d1801c02c1c258046d034102e50403074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 253361160 1250 253359910 253359919
    0xb0105041703070b070924050301090f0204090f0209011d0f0d4b0b060607030c0606140406050613030b070207030f0503041a030112030e010c24050901020405 69
    0x25081c2207a4066140758804125074030b00c814040315010862074003800740a603c072515501641d500744001d06030360b22009440c1c44411481c40d200e407150030b580081103a0450b401e004002800085005840020384070359030082011900300740340c1c640049455401000141c2d0300340c9948038800840b0303a000c28007044190480d584046104038856407400c04d904203200c0c440c130401a40c0780c4840b1a808000340581e1030f1004400c0709a4400034182403070403402158500009a0b40e6050100d03140340d4480700e000b00010102d42c021540450854100f5000f40604015107034811800d20100b500d03200c00850313281582111038400e90070160006884d050490449c0d960b5078160101c43d903a5819921801482c0501a10060840c1704240c07002011136a80c0151060082c4541d002c0e5136146c0c0350a51035500001c2c80d1030940c44101c01000100300c00b83c100e10070860030070352600f040780c1d041041000588408914001c06841040e040a1420b400c400000d0708000b420180c10040125440740501a03080b40224060580c02 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 253362410 1250 253361160 253361167
    0xb010801060203120604110304060f0f09020603131106212203080601050903030f0706390314070c030f020f031c06030602070320010b060706021e04180b040b0105 71
    0x80e4400310007240c0d0025000d0b10104004000b214901f41c2a1f104071400c1c0e035026500c014040425816000304500381c2126a01800310320580d800140c40d511010340a050115040c03028031040040b10302c1000e900301002000e0719126603484002c1d190328200000c6808a400c1500005424003032112816060a07401110b5245109450340e016035103501d01410f02414040700b840244551b40c0c040004114008041c2242034480c141450a4019101082c20341d0006600c40284a00301c110514526600c6501c0d40101e11015080c11400340c00500b03454002400e1403c2a900f0800754a402842c4241000d1180d624625044401c680c00c03600c0d200d046a0602081c0c00070032200700700c5c581907401d056145075038040004a02d40e90741e4440c0d0880e03010407405c0780400d0031851542c0c5805860b8072000b11140c40b0500038020f072140100050042c1c031480400807c1c2a5002c2003101513518407070185600e904001c400141d8503521403003d0b01c1003541311400d011352282456590300350360909014200300580107840f8a800d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 253363660 1250 253362410 253362427
    0x3110603040b0c181228020312030a1e0b0102240a0e120706060320060a0f050705010501171b0607030507080f0f120702010506151b060108010c030b010801060203 71
    0xd40d90108640100340c075a800b500c038000745e40d0074040e42e188035448001010000b81c104001000607070100d0540003400c05403841680542c5010500100d40311004002a6a81e5582181c450040074901000400340b00300d00e800d281501c1c1d00d58040d04450b20244c08072a60988503c11045284411600540c40ca500751701c00b081c47c81b0300340d41040388603440c50415250040464000325105402c210b1050f1000368913460100248150b0400115030a06c400c02e0b000038181090022070181d101d50b84501c82000314040700d4000b042c0c4107109882011768810024801c9595621041000c0074017050400b1080c0070315a5410041c52845d07942520a00020b890f490600403503403000d941d241c100700b0003990844000c0120007642d184050060100b28803c0c4020b580b15800d801e52649031282c0103040c2000e680c50a001d01c0010fa071000d8044120640c400b02c0159a41e0040d5003004558603401c141c00e0b0a84600703c00410340082c19000040c41145698042150341150b800448a080d0284168405604100311510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 253364910 1250 253363660 253363681
    0x170f0f010b2809051207090c0215070c030c0f0f0201020c180402060703022107060b0a080a11120f010e0f060709090504050c06160b100f090b030c04140103110603040b 73
    0x501c142e42070900404441c0d4410100d50340d88159100d05605400400301800788048510030700000500b00e10003410111315541c006858442c0142c1400d0621081c1c52603901050b105a040000656125054288901841c1b900411811651a0480c0035014241080009003803906081c003803d98051440d4650362100d40030300c200d581c00840103804600400e0140004080c580d04c0c0105c0c0699040c1c020399035032078070b4180300301202e0700049014030504408504020325400040c1d100310182e0000149000c0c01c061000003241410f042c00380c0034240c012040c8482c03c1d100190300c9101695220007c1d660300110f29682aa01c890080f01c1d02c1020507194482405680056400254414462022107010181650019402d9000b0003100c02420400729452001c0061460155400c000b6040386800c400d82400645043c6c01070302d014880e250ba40e0380c0e4450032940c4c2e0402468501410240c810050724007201d1028140c22000d02003915032115550170080241086070032a0310882d0459010803898403a114070780b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 253366160 1250 253364910 253364977
    0xb030c01080a1401060c0311210904060305010f0603020a12081606150b0309010f110318030d020304060222030809060903011d0106080114160f170f0f010b 68
    0x3030b07103140d8a01c0400900d051001c0c8842c0600120703140c03c1c0500300c3c80d25008140b0402c9855040ea1900001d24000d4000141d44110340c013020400d0302c10391030350110804540101032070f50000c0d045600300700100c24910350950050054030b009450b100c001903110b419002c0040d01d007100c0200340c81001c101c000c4c1510b4441c0707074180480b40325a0b00440d10001001b02080c03028802e82101801b64030000a02100900074480e0301080d031180c4209100250160003460500d0100410f584458428125441503294040c4100c90108000c194115140c2c20700d800e000e4001e40000d020070034040241ea170305d011440f0b06801c0c46002c49500145050cd080d14140c01d01000e5001076141940640d200c00c090035040b0340000d00001240784041c0000740523843e05141c0307425a294100243c2d288007003030061000700e03d4040c0421410011505000341d84410155084074910424856600c60030f030900140003494a500c02c0d400d00800e40c3ca02c0c01d000a9132034401100c1c0e00d10804d280c58060f13440b2480d000c41d02800d040c198 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 253367410 1250 253366160 253366171
    0x1509010302090a180b0414040b041101050c1f0b12060604020d090605090109031e0806120f030a020307050c041a0d1103010c020f0601170a11040b120c040501090b030c0108 75
    0x8410302c0079910604000710303104144854144e191182107520190400744100300300500246800001d45c241526000702040c0090405000c10100c9400300f405640180100c8003955904021500414201c0b0300c0300751551504154080402c0c181801e10840d441e00944450b071f201c2d0503001030003030340d00c45030100002036020024043e2196241c4050b44082a44d522403a0721803664a4008200c402107841c0c010202001c2c803801d1a08400c80032260000ca0f50b00081484d8000415141150220b000680c0b091402c0d0b0b40c004a64207a01c00010300c9660b1a42c080060401c8511420482d400380305e03000100b00545242c1480c41041c40d0002c0c205d40d0300d0345000c0c80c1e8050480e0064204800c1041e0500c0881c1c290307010075483c2000f60780041700020b64850f00300079190041c907600200d00c05017070a00000c240c881940c44005410700b41b00040e103540546d41c552101c1401003000b0b00c08500b03400030350850703a00e0b0038600b0b840f10300c12031800c40001501035960043c005100302c0100a402c11705010b6005507900e080c05003c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 253368660 1250 253367410 253367419
    0x9071e050909060a0f0e0304030303110c01050103030c030f020304061d0f031e0705060306030c011d090a06090e0705061914030c1b1f0902030309030a060b0f150901030209 75
    0x40008558858481d000e000e030300d20070050070661508100c0c040a46444201d8183e825140c0b034980018081301200351001d483d4075280100300301c04641800405405481405640c0f9403800c0000002c0640098440c01e4a0307109845400e58161640416610390065200791000701e0030881d004126880c2043c484000d02000074403480d00b1080c1d50010074038200310700802e0303500b40380e0720031452014803c2007001000400003203c03620314610300240466140e1a0448110781071256201e6030039240111020296503062026203040c826250444554015120030320a0032022441c21002c01c00d8010301184032000c0e00c0004d014907180c5622040f80341800c2c58488000401c220103000400080c2081200550040828401298440d80c03084070500f0b00380d0f881c610170140c81d0300c464045090b800f4110640180000310550000c1c9449441c00404d0a42c403560110700c1d03043c0175828030b05082080940c0030b1f81c0144001d481004600900b2000d000e040500401140340d0b5203814044120190b1007034000300742d8240081c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 253369910 1250 253368660 253368719
    0x605090103141f0905040f021c140c0a09051b031f0b04091b170c070203010507020a06110702030307080f0408161d010e0412020313080105090d0201050907 68
    0x1203081007000c0b0b06545050302884001001c45a40343c80041810250403249002c03c03144c1881d546442e90110785d060000e0042c00c1c14601d6100c2c2d4043d020b144030307000307401084480d8290401c01b110398841c01d400041d14444c080c0640d010801505a02c40d40e480f031451242d507031015105142200206410040c01061104481041d001c885551841044003c0280118503505c030b5040240903404d48050100070401c03559801041c0d0701c000ea00151000c140a42c038050b139101c5883d07018003d0001d20031601c010350158240790900400f6a40001d0030f0540314000d0b10b0070850702c401603c2a140358030480101075419802841007402040341440144808a06058882d02d056941c549580c24085001a4141c9095110b54200401411000c28900f40b048113004410b1543c1000d0f0b00c6450b1100180000c1c240c14007800306441805d00070800c0340d0240f0340b10110800015030707032400c09020703140440ba00c036840e0140c44034465410380140074280c0504018405011001c2c108405484020445842541110540d8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 253371160 1250 253369910 253369931
    0x3061905010e130b0d0503040f14060a0e010302071205030907091e05090a0f03020318030601031502090a0512010b030f0a0c150c0b0a020306100905060a0c0f0b0705120a090209010605090103 83
    0x401030305040d50b12030306c05140c07035510348460000c40490702c0e88501000024035480390403990742d20049a50042c050304280216041c114012402400345a00042100d800700b21039806040d0420043c6101c5c002c4c42c0201c072000341d1105441001c3d6040070706c070301c0101c00b10700d440320350320b411650403071a800003501003101c4038141c1d241c07200c050711410140184d0150f0400599104641c6038224400c0805078194001c2c0940d524580d0b81d499013008503034281c80d04503404138040d41c4903561604c000004240090024885c0e84070001e48a000303011001d81c01d4401c3c030940300c030080040300100700c0c058056004121207c20b2031900050501c941d13184568401003140c01d8103401c0002e690303803214074058010072100503102e150150074043c580030940304240070b010714070300208500c0c0e42d07c800301e802c1201d44c0d2074940c00d044418900740130144104003008004242d01000c228002d84d005000e0702d0b080e45010391002860700ca00201000300c503000e01010b900240700400500ca907a0080c00142320556041c540001c00d014003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 253372410 1250 253371160 253371169
    0x1501030b10050702152101140f10020309030a05010c03060f050a091107060203041b05030f1002090607050712020109050904050d0e01050904050a05040c082a06091503061905010e130b 80
    0x401920350b0440c6c8034401c0700030401e650059441c003402a0305401c400000c000000142c2803c5072003e6944210300305160304403003902c00e00944195102c050101c1b4034010091038403d018100072100c0000181c64854005541c02d5400c50403011514040e2800c1c9815040507800303409030a42c00c040c0305401108000c0000001c0003071000b94496400780c99004d2114001d42c098400e041c0a03507204c0d0f4804e601662809070081004104035800351041140142d0742c000c04d00100d003060007181000782c1540102c0f000041c0a1400144044113a07100b661a40221a02c51007004500202902c001e405a442040040171441c054180d02d0f9401720141010b03800d0031035140004040c0d030000c6420451303861b2a1020b020400c110301d11350401401c0340c2809070040da03c60528000000154140884048070300c1441d0248a0322180b04840003844040c000c192002035952940701141d105803100d90240c01024500a0450220b003d6002660b40580d03074103500700400420425805041012000010398803920410a581c0303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 253373660 1250 253372410 253372417
    0x9020d020612060f010c1e0c05060d06150206040c170a1e02040b0108130209060a030c030506071806051603030e032703011b181802031501030b1005070215 68
    0x21071542202c02450081d06220000702641c0040d07051000e9580b4403c0015283c4440c142d044c146400c0b0b032100d02c107050401341542c09149d4041500820700140c0d030342d1124041c0d0085401d880b10205005500812500d08982d03c0108540117000751000d40014030220008642030b030800c035540700032528802c0c02d42c1c80362101c034a100c003068081a080800c0040450404e0300810b0031030303802420800e03214a1702000700458690403a200912800d900000a04140d45594905000e10b401c4000c04001507100d00d0810750300c10003580e81d034003c00c044590460344400030500c07200c282d410660750942400c2c250310285460281580c821002d140d1240c10f06660030000f000900b280d00704101c003461360700014003141d0303c4500e0185280340c0207034100100d14a50b0307150b52158190030006441d124407500308a8148408032843c03900917908110711200d00882822454024500036002201c2d4181d600810f02d005400321010000411b03000b201c000501c0300050b0254002c0c202d01400904038619003d40301000d02919030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 253374910 1250 253373660 253373677
    0x80a0f06060309030e0d230307080307020106030507080a030c060f0b03010e1c0c050727060f0302010809030c0c06030c0909010e0f060a0b0405040b04020c1606111f09020d0206 77
    0xda4443c1070f001030542c07100807020b0481c0709480c01c3d4520b240a85400e598013501445682c103d07000090801103401d8200201d6401c940c00c0040350b42ca03401c0000700240a04054070007680c2c00d00c43d140f0089054030740484c2e0511030315031548466000400707079540d004c0074041c80c2141d0f40e9540c1e91807030a1500740e2030070b00441c0c4a903800d0760090402c100703142c100d00b040045d070144d1820411401d0107090300003400c000b031280e081d506503146201c3d035182845250001d82054040c4900e03040c0c2060000112142600c0080056070b01c00d0b00d07007228580d210400142c2c1c1e40034040c2c501c94654050754040045081c9070000390340064103142ca051405101c4408540415004c1c3d03c0b2401c10554501042901c580d020b000030f40000003103c506001500d03040803050301b4041d5010b4580710329580e00150000b9a40e660450382c0743e5050381c080e01c1142e01c80b402e02d80b80e07007000c40c0f14840126100359021441d100c004035042e0745071800706e000c80380c18040031601c00005101645040303800c00718240901c009662800050a42c41 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 253376160 1250 253374910 253374917
    0x30c0901060c0b06041d070f0f060c08070602210108060f0c071106041a0408010e12041503060e04031d010503100e0402040e150103050709110901030213030b1302030c150a080a0f0606 80
    0x15448e1a070307148131114190744a90b4540346c0110301401410b60001440c080e5a800454054584486042000c000d120341e0901002911001c0c20300300341042d0703480d1224102c40c1e501c03041d261107903134402600550f80c1003150b04c071044400c20041f040c0003e42c1840400003031000a070a250826841d075465080d21510803468242144000c601040303404001d02a000920020401408030049020380c81e40c0540a41c0c003403407801e0300000c440b11403444c0c4a030741b03d01d00501301d03090341103050708160401500c5102038280f01819008110030b014041d50040084900801001d0450510740d440c01e48001c01c0d500d8003510480e4000d49070440c000c205001040500f90f200720700329198160354550f182080c40e010071980142d8074641011400c2480d40c40050599131280c4080c2000760f40c5c2e500c000c0c00b81d55440b1868100400c050100e81c1071007030350108042c49401c1a80f0a0341190b80a000c4241001500d510a4504540d914400c000701c1e000c032440f503000b007170f0800040b00002c01c030600201c95800640c0c56541001000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 253377410 1250 253376160 253376173
    0xa050f0a240e1905070f05030a170d02040609080615090703090206160327060503070507050f0a06053909010c0b090a02040f0516030213081605030c0901060c0b06041d 73
    0x113001c02801114014140050030484481c90040482d031514517072500030301030000e600c01c803d0f0b0345d4131100c00b280e204080e050302c219956a2607440140c60304109000740c2c3d070548104400107009003600500384c07207070307404c024008180ea654080048010b1301988100b20707042002407205030880900d503800c1c0381e9285d100341c0b682c41d5540204034a0300c0884526010030510034010300c104000d0b00f500001240d400003154501281c1d1aa0641000da2801e205d00d1104015442034011050a1100952160b401030b11503011a01111000121b1541c01c0c0310f88501031258410300c102c80300299a84a0000c0c1031058040c1001100c4420fa42c03074402c1548407c5a01c401290007244045046140c140303d040c0d0a00ba88450410560420f11044441205581450780a01d0380c0041c2c0c070103250b41605880030080590b48200d511040352010740603203201c40da01c501402445445042005803511000c0103040c2c640710790301e80da002042911610001c0d880500540c1c9c02c0755032a060180f0700e4a03100703504402148008010082c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 253378660 1250 253377410 253377413
    0x9060603060204052b0b060f0d1b060e090105041d060708150406060f0f020f030c03090f010903080f07150c05090306090d0210050a060e010303020a050f0a240e19 71
    0x2805140917450f903084000519001d550801c0010f4403007840d54104040246c666100c101040d94455680c0251350301c07190706e4640740100b1070700350500b140f840c19001002c42920366405094074180395440b030b42640080141c0060216040940c440070150700c7e80d4010700c480001000c042400d080c41507503010001000d10042140100d51a001ca0030b9514040c0d4040004500e0b2500080100a04140f00010014200410a05148201700c400d0041c006074054903900d42512004c030790389a00045486002e015a28a40a0b2542c00f500b0000704507a0030040051912421404040503640a500c0031a00400040c2507906202c03c140f1441c1542501d54417110341c3c0d600070104144c50481c0c0205022601d900054901c84040d03804580603000ca4410000450329485140c5c0240280005420007444000ba9000010501d5030002e02246501e016006aa43e103070f0101c0911a114026114054003000c9841c101003401120498180c00a00d072100b00002c1e4400b416040508003c81044a20f0389894410307034440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 253379910 1250 253378660 253378669
    0x2010506060301120618080c0d080f090c1005040b030c04090e121603050705060f0f07030203010b160f050109080c160503120c07030b0f0a05010b1e0c010906060306020405 75
    0x10342244003207800078215072521009082c0c09540f00c030000d0590b0345601405200d10b15001d5007518003944192160b40b00e00b041030300150380d00842500e08000a00001c00318400301c0e0084d1440b8041c0100d440036280300030442080c440b000381050719050400c941040b000601e00e1100010314060300701c9005180d42d03240b41000360001d48814003608241600310a0480a03000303112021280500d0407045013038135040d02c1c4e0505503072a0040b50009442d078044e600400480d4540248034a00c14104c61528a8203502c071440100e04034002409001d5003014108081d988034003940d4020113900b4070038102001c1710481341d941d4600351842102c08807084000484c6002d400c04040c081542c4c2081c24410840daa0391074070b000203568010066400440c8100020000c2c1c40b840f042c0046e81c0555005012001c0f00e04218000f609190303c104c1f01c52111502e80f90011503000c41000072204032010340100e08020844142010f00e560703200c5070380b1180542d650104800000c03018003900c03008601070040107860720324100900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 253381160 1250 253379910 253379921
    0x11b0201020a0806010f03020d06030501050f070c0c0b031015210c09030b060312220906030201080412021603030e030f031c1107080f030601090e0622150e070201 71
    0x540e4014824014101d80c089000b9a200c0c4007480c0003280c1d02c40c0c18030141d0080c071a2107007261030a814120044180b000c150040f9020345145400a08c07103a4074800102c520b808080002850707612458402c10208244030051130304106044d00c0c43e5009540c81031408890344000d8104c03070200e00b0041d15200d0701500d6000b01c401034a174059083c001114050700090075080c45010041c03505903c00080b90311914200311a0461024510303134980e440e5a03030140135544448418840c14040c1d400c0c00e000c161608240101403c480d4182c440084075181c56a400a80303002c445010002c40c4520b084145c1c48120007002d01008500030b455071003541102c00240b50800d5014529004180d100f0011803030705008031100000b44a6880c40c00180094100d10300030f4a51140207800b41c031045001c40d8144280780f00e180110f003d18000d89401d070841e0785d50504114405400c45419500c441044403003503444501c088080300c3c0201d08000041c2d0350704400f0100c0901c091a40000c41e4152400081184050302486603 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 253382410 1250 253381160 253381211
    0x120c0c010809010c20010b06031003060b0d030903030f030b10170f100312030f0c0530130204090c03050d0207080f0307290406020904180507140315010801 68
    0xa225011301d10201400020600c1c51880d120840b200e00c10140072020f6101c9030000c3d00090010f81d40e402d194210b07a0b0300034010f000a48401d0f2400304c01d180c0c54501103030490721036540354550070091850b58900f911141c130b843d85450f0a241d02c610390b207109513a4450101540030000e071070b0403148a610482e01181d1000060182e2401180d00090181d210402ca5100c0c044035400805210b20324221141280a8170090407090400c2d4103009036241c1e815001400f50001c01410003044001c034091203120712084c500c0728410f01e04c43c00c041d40840d1040600c3d01c50b04200c140041d0010401500d00d0341c604048100e43e600a03180c0381c000c0d45502c04c80613414012200200204401854029030145c111501c1e8400c5620040030f070180f909005004180161b200002c504074203441c2d011524143c104070f4040d500411086100e10714284500000c05801595429403d40100c000c008043c00c02640040c5610b6002ea41035051085ca0081100105011800340c0030b032001000100710031200510030003880ea0031a60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 253383660 1250 253382410 253382413
    0x1006110102073503130210030216020618130c1710060518130c090f030308010e07020705030a0303020c0105010b041508061c0f1a0f010611120c0c010809 67
    0x40000c1030805042c044142402c0d9100030100d030300349a0b03026584100f01d80780301d50f591010081141172641c0c010702c500e41e40d000741d40d084200d810f0310004404900ca9040511140a003501e550405810044040c0c6070000d602c440c0409001403080005a02402d0115584002038448070703042c00c00d5501449803076851064000e09142c0e824886170818a594080c018001085408a21b10b04040a030308422410004090f201c480c4400c480503504000d418008035600224890003000545005210284000c0f00e4040c2d8416407540d080800010b080f002c060140403c5105610000c215560140500307042d07240302c0e40300180c1e2490400c0603542510b40c164400c0012181c244000c0001c040061101354168026161204140c1e0300d50002802c090901c21720880201040302c80007003000750b82484c0307040700360103001210810b840c85000d0100d9404102c5101c56103209000041080e907018094121001c4c0e074000541d060003070801c1d620b074001d4100401c490035a91210080c07400550300501d1450300031002030f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 253384910 1250 253383660 253383667
    0xf18070b1b030c030403031b0b010b03090d020304050d081605010c110c012d171e010f030215030907030215040501110c010206070c0213020703030b09010f080624091006110102 77
    0x100030130386a019510024082c0b1009003901034032103110048840441740d01030107400320355840d041c4906035134008407000c0e84144101703800c000900380000242c030100e0304010f182c0100d801081d40d5846080c0c1018075440100b4900c5640040090403e0150b001c444940c1d5035601001604500c00074549039a4200d01410f000c00402200440300ea105e0300c00c5581c84045090340341d0041c2506048030807690540500c061030358481c05020144414150500140d00c2d0300c0e0001b200c690f03c610103003064074030a11000b58440c0c101c07002c0d03258080300d20001d164080c00c48020f03030b0a0280c0c0d035004280207194011000f840400300080500031907801c101100000072140005144a4901e40000703955404098195418408040884000c56998164010041141f4102991240e04030b207009005408101441480b40e00d40f0300002c103d01018a90400032a00000e0041c1010345801c0ba801c1030404841406903264207400e40c1c00303046900d591110a00601c41d090448580394a050360040036480ea68039161050390040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 253386160 1250 253384910 253384927
    0x150f1617120f0408070c08010c020f0c0901092003070306170c0f040b0301020912010501090b011107030818030d08041e080723070e0402090606040308030f18070b1b03 73
    0x7820800e40c032100c0c40308400341c0c1d42c40e5070404644501403510002c1040000318804a01d007101034104d101124980d40807941c03112000c0c4070440c0c9480000c2c030500e0700041c0e0b51004000340c06040e0002d0400c2d841040c0c0b1031200c0e00810b03101a031240c1c0111030304404aa1522000c22840c0841990250b0f600000390280091f0420100094000300c0340302441340c0710310303200d5a13602103998080d41140d01c05c000080c03d40014070f070150402030282500344503109500f4640090705805501808030364956806c001c0c00b4040c41c0e0b040d55103810301a0800010500c000c0f462089103415600c007049003131810301a581ba400ba4519252520071049403002540000c052840f00c032803c0040d600c0015240c0c41075020840624003024108842e4400505410702425031240340c10002c1c40080e0401c80314000d50081c3c03523094407540e421302400028491031100400140b01040024411100c0d83c05041d001142028058861260f04a503140f0b00010760b080000c0014001500248040c100c860710962500c1a10196041501c103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 253387410 1250 253386160 253386187
    0x7060e030303150a080709050109060b030603060f0907030b0103150509120901110309151c05040308010909030c0b09011409010605030606011803060f0204030b060d050705150f1617 79
    0x103800f01e4982c82440500600319030315401c080004e403110000700c5c1d4005036696060005004284505040103107000400b00704203007003004076880750201074014015503c504840c5100c1d60401810a50b803401060000f00008155001450081d03004681c44503140210700100401c661014042c0703600d590090a01d4807600b141d03d415500e6200017401c0003440c019031b0712005420340c4902040981e200b44000346841d03892074240c000e0328001c130483d443c0c1ca8101d4501c040e244100c95059501502041389140108030320f03819500841c11061081c9840d00360b040040d80d6903040044107555140803a515030101e003804024282019502c061010000c5c0030381450980801c0d100d14004c3c004504220300541a0407401c8031151142006540c0b0003c204800700710f03000c05c03100940140c0800c6035107402ea4804034032a45030046042030b03400d800a02500d109032600b0100402403950348201c04002505010910310082c000b0040c0c0542c1c41300001e078480c2424203282944100043ca403c402d80e031213051205c884501314 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 253388660 1250 253387410 253387417
    0x60e060f0c07051005070f0f0309020105030a0e0102070f051c14120c2709060409150b0409021e0a050603070f0e18091612020102060619080d0c0507060e0303 69
    0x100650749503a50010350800c5070034441c01d140d84001d10350802040c4090190700c03903503e1301c1c100c0607a80e4402c000d03540c4250880540d40b4410019001580900204105451580c2b03e1014041d91700c0005180080300e40d40d00403180c14010042c0d400350491a80e4155040710054600e410709624030384903d0014680d56418064010900841400c0e0341800004405a03002c0044a20310042144011a8650402c04100c0c0d69a030030030b201401002140042900760070940240340d85203034803448100e0ba400a0540b0b01004001100001d6442600c03080e20801584440303d0320b1140b074030781c0c50481100c0700001090150b62441540003a000301010020001407136888140001c2210b154a4842c0350622800006000e0450b50300c0c0f500081e880100034807800040000b41c0c49501c03040310030050700c05035964500c080084400e038800790140c0c0003140094030628140d0740000c0c1c0c20624507195640d043c0c403140303043e203001021541c0401082400325502c050200c20400c030401068149858a0f0900290000c69100e02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 253389910 1250 253388660 253388671
    0x907061103030411010e120106061205011214010209060c01140f04030203070b060f09150a05060c0a0602030615070c08120403031d0102010e16170c0f0607050115030609060e060f 78
    0x80700c60440e44e180c1c0e104081141d115100180301e122001200441c2a0091845124680c085907003c000d82c440520700d400350030704a4426204181c4950740548840a83c4d5074007076060181554204002c218540d100e0019010700c010b0140001a0440d00c10785120240901070250942100c02c5800c21001a500000711075185e644512040c2e410b449203008529561034410860780e01c881500200300445600b100700b62522102102c000c8030a90392002400524071544c0307a040c40035001944410003041054004540110015103d00480c03c01141980000d400942c03088400c803a0380101009284010021002c1258442089520386441c550f03000c0e24036180c02842100900c048240300501c2d07070007984000c122a051070143d8804004815160351010380a01690b0080300c8441020011050f00050100403d00003520034060300c007500c4100182500002c4044480d5900c9080075031a03d070a0400d2140111311810303000c40c61b0889490880d00392407120052180c190b10400c00c00004084090301c0d40c0e00308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 253391160 1250 253389910 253389923
    0x20a03021c06030b130524070f0c08030a0b060405030118020102070e01150f170403080118050108031209030f0c07090b09130311280605100e1906050d0b09070611030304 74
    0x83c151484c0150911015a28010000c05c0c7e030220b115031001e404e605944181c601369038195032050304010a0314a080160800b1f0901c0d0824070009840d00c92903805000c600c00d0040100382000d41c0e4038000707400d49480900e4490044440c103045c00c2103503010414500981015041c101d50342d070400340d450416040500680d41004403c8130099211405180c6843e9529840d20301c109203490103007400381030748030b0a200301c105d1000340c0240d0044000d440d2083c5810b81d030b0140c010b54640f0310300100a0b0004c4d00d019000a6150108001500741c1300306d40d40c001c0c00403c820402401510b4580f85036802162445030b9034134058040c50042003600761040c0d001c0211280c1c0b505000b081d00013494400c0e460721202d8510b01c0051007da40103501c40e01e00c014074544d10588601414031155491105403244195075201e1090704081c03820104054001e800c030380110010202c031000880d20342e5000000c0030b0091301002550f503e4141e0b810f01001d100306000600240c851414200b0240c403201140075501c6c4001407001d0f004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 253392410 1250 253391160 253391191
    0xa0305010f0b0f0a2606030c01020f030909090712060608060c16031d13050a05160f08131709030c03060603070902070804120b10150504030f1401020a03021c06030b 72
    0x2a9000c0d407540ca20340220001e4000e0b02020fa00044541000d090380d14620138448c1415510256100040c1e10041030b40b940d002d10704224129040c0903170464080c05602440c01041b0b00415000c4c42180344046140c040c0d000842c4d0145848800ea081c04d030301401c1c81040d460100060918001d00b8111034040320f5242c07900c50000f036540d400d400b1a0407a00790495600100b0070119002104035a004280601d0140b80200065110720790300c04452140700c1c0040021030300b40750001d1006409034810b01e41c0030558006070302d19603800b41e80d00c03040345401c1a80c0d200046004500b500c0c5904040091039003000e0140c0050030281000c1c00043d075100303100c0c403407225101c1e00041e40c00c2c1009402000d6070010943c018051082404515090000d03d10031507070400d801702151000034010310440c813074a400c3c0b001a1505807600713003142ca0b00d00341c26400c54402d03030b20540c1101c1c0c1d001c0111803d01c01007000c600180ea005032a81441d02020b0b541074080c0d0500868242418802e001041041c41266040118801240c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 253393660 1250 253392410 253392427
    0x8060d0b0702010f0e010b0118030515070e210d03151a070b01063f0c0320041502120a050918010303120e030a02060606030714030c0a0305010f0b0f 65
    0x1401900400004130340c100904004011015040401200801d0721007607026108a10020090b0109100c007410644c40b680d02486a803080d00102c070341000a6160080d58444203501207507004450312560a8840381b02003d80543c1c000c18480055412080e240a21501e81406001d18202d610350180e81001984581c0c1002d0404800040381c1c0507982c81070b03c05400d980d403035802626680141c2507011094090003110142030a00c0080703030380302c440300c80c140e0907040c030216038200010664400c5000505680b0071001400d00e0079141c44a20280d00c2c140f44e075658600300704c1048550b004050a90042d58440c100d03100712010700d1029201c03040002d00c0c1987d101c880780d90004024050000490110074240d8001000f4035510008603030b8142c0030007809204644114a50540e03070700c196001000141c02c0381c0007094035450311030011504940c01740341802d84141c4140d400c0c82c103507200b5200e6407000540010030551080d094041d0600501d00101c5440f11145403000d00240d030320a80901c0b010700880054180e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 253394910 1250 253393660 253393663
    0x1110020c0108130506040503030f0108030a210902120606100504080c0f04110c07050102010c050a0f2f0a020a060f050307050a05040e0c1309110403081606020c1c08060d0b0702 77
    0x410755801c10b040342e480703003403a052144c8c4951090340d40ca004400d540d000401c3e10030000040341c012242c0b6680c2da20380b00000f900100401e0311081810343e5403580b580c8020000d83c3c0c605580356856400c03c006801c1c54100301080140341c000ca01810000e210007031004100c5201c1c01704103012804019101d0007500d4000c00001401091a62462040c0030000700711104013400002d000701c01c0d40c20070f800800580b2500c040903a080d0054510b03040004180b24141c0c2d10451040c0c1e001030240d03118000762003e140315509003c0360038030700308800141588206800ca080d841c3c01416903004100c50705282c9150903030307214001c010f07100082c603150038440c000407512421403292049500401030500c612a0303130300700000f5951442e448611840014981200003180c6040684124100342820a600502c1c0a00c2d540c0c030640075400c01c03d00124960407804441c000310710b6600003891041985c0025004042c40d14102201d0380c0a440780c2841006034590400ca0a51244240b036904c3c0f83c0c100f50000c0603591643d400700d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 253396160 1250 253394910 253394941
    0xe0109050f150c010216050f070807031203090321020702011206060503040f080d140702010f0c0e010c110910030203060c070222090c06110d020c060904020309070e010f031110020c0108 81
    0x1c00d1b0521000c0504240403000c52400100e569190a49100c48d40e5500b5260b603072442c43c0800784c00815480b8000010754020f901141001d4400d0800750502c0c0c1507101800340c9a050381d01d4000320681c0020b9a071046607449126010b4441c1c0c07402c000c2202c0c1d42000390041040c080244020098039030f0800e48010320100f02c0c1512245048124244541d25140c01407620030036050302c080000d5030a001d0304400b69800e0f0300810313103020000d50710f001030b483c000001110416806c03803080e2610314454252000a13202c1d4240b0500c12542c0501c000075803482c3d40705040c64000018606412114203000000c0140d4442c06640f0300400181580c07414400d001000341d000700b5050360028807041d441e040028203190445201200141c101054038800011200260703140c2c0200c240c2c4aa0180c0300308000303021450301341d002d180c108c00280203c668003601c0d103140c20031402c02a0002c3c0607050020004100f0011400c02c5004912001d86070001d075411100c0010f5501d401e5904c3c2075040c8494000000c901c2c034040c3d0441c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 253397410 1250 253396160 253396177
    0x11808070c0801050709031a16080a060b0c010c020c09040f02010c06020408010c0f08060a24030e061807140f040507030b10110705060301050619020118030e0109050f150c0102 77
    0x80100d810100303c040c0c41701003144012140ca15012403032061000b001c420081c03140e44030b00d001270000c100300790084801180041038240b10300c3e621400030030380c000e00b80e000c1c00d8881d900f600002040f04c0d15174406807070044070602081c420900e000411000131002070406084039828240a000c21401b4035040c1c010740110b410a07102d030341c80c041070400c09550150081e1700c0c4108984170721520380c44039814041010346c3ca00525070181c02110403030802c00114565110040b42a1400044045c0381044d814103041c0240c81c45110070012100c480007208090110400402040c5402003006403c4000f00b903014018454140c0b2541c0e4600000703980e240650400140e009000300300d024980284c0c1e4000c0c0c84a20301d40a411240d105002003c2001d04000c401c4034140e4400801807803c0450190b426100071200680b001d046540f503040c410707030b5103c8054050516034400e8031400900c0c09808001000381c0c00707550007284180204840c581450300d4403108500c0b94410904420340e100c0c0c040d040f46029100d40c452 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 253398660 1250 253397410 253397413
    0x60e07031401090b0303180303090409080a0807020304050a030f020301150b071511071b0506040e07020c0a030c06052d070302100e1e0c0a08070603060602011808070c08 74
    0x100140154503901540e5946980101c1d50070741e03600c0d21205811100354601c0300703030541e004000701d454001003500c016015002c0201200d242542d12408a0152800003074202d41e44800824001581900f041c2810740c80300161004504041c40d0600055020f0490700c0050f001c0000c80c4070100640d20b0a411441034140840705180c3c070309981301404e072900e074440c110a0b142100c0b4482d001c80071910314001c61841300b02c5a25010308180310350b2180e5181c4181c0c410120695909800300140c1d1740c81c1c0102410040c0b408030f0411b2100e260408000c0e08200040c5050303407003403000c940c007400042c07011540748041d5181e61030444e0b115501c00c024508201c41030380892080704041c0544003558002e010041084034480d81c2941d15041c091200710054840b84c008009198000303034002c6515550391500c581102400604513448580c10b0000300342d014025030000d00850300701c68002e2013100c2d054007035000144032600c02000a02e07200c0341403410941007040020840040000d03082d080c085c000131484003038000d100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 253399910 1250 253398660 253398689
    0xa030e130c051b0a0c060503180a03020c0109080a0b010b0a0306120501090204062309101206060602010c18090f020f04090b01030b010e211006030614090a031e0306 72
    0x1c801600c260410032251600b2100b00d100030022100200301140700c0b81e84607142001c81400c040c0709803010380008080041c2070000f6440c0c2c001d422420081000300f28005d0b000303040a0740040000411409468002c41c000340d228420100000d1980c1e102c00b0f0448a0104500d61078103880301d02100689080e43c02030010000660449042c02410360014001d44c0c800c84d010006503545071007480b5650b80307030310406105810302c0341c03031000506092420690004507503c0c041485c03038642d00d452240003400f000c10ba0340c00d0340d99142070110503024454441500d46070300b010507140c1030a41f05040d902e2240e025a0070341603100d904a4508400a406541c220380683c0d028948498544410500601041034102d0010b428402d01402070b50080d1000e182882c40581074114602500309903121325242540202a1441246a011400708140c40340d5005580700300d00104810488624012610501400540075a004018040c00107600848100041c41229010f0308071104e40d104e00350000d202d1a0b200400c046001e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 253401160 1250 253399910 253399931
    0x61505040603110910060206040611040902030c071a01080309041a03120c07140a050108060d0605100f09150e04290f070212160c05030102040609080f030c0a030e13 72
    0x3c8640140300c41c09131400800c1d5510300c441540c2c2421248640c0d00541c10240216010545030b80105002091850312035180c1581c0f0030402c812a071044507403200514000c41c1c420b01300800111612040c0f5000d461100c150b5060a80050300c1c0e101d1611034030f100785d40c1d5a8450b0b4004070500044017442000070107865031076142c0212040280d103c0e14800031580500003010031a40301880b110034590f240600001d10090601c2c0040d5101a40901510f601c0100d04016a0003d9400c0c040d040c8a40c10009014030064502540114800300c5a040000b9003414418074a80e410700c00664801210800048083c0d25203d5040c030f0114110111408844020040f281121107501070b002da90251380724032011040c940d28440d00326240d0000c00030007900c88100304070014551403c68105803d0703c1c0544160411195288d0003e403c982c000e80c400400318201d01c008211041c41840004107442010300610700d82144049420746408030520020b003442488006440503482c3c4d16510b00203c032040e5407c000c82d80c01c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 253402410 1250 253401160 253401173
    0x21b010504211412040602090a0b1c05060d0b0705040b030403020705121603080307120204080f0d081302040c200717010204420e0f0607030507061505040603 69
    0x10300d018040d61014030030b0406030244103c00c881c0106007008040c03401e041d030780c1105500184001d4810b0780c81c1394092010040a5407130700540030081c8015010266a81e1000f003141d1031040e1445a0000410310b0f01d001c000c035544030f03605541e410b0340d40030074800d10300e90320080d00340e0306801150071143c008080481008101a000192082a10313001c80e01e0340418a50301100319510f80c038800c00c441d401034995204000240c00d0304040d64202e40d4030308210002c184014501c100b240c002e5484080e55034025089420350107000d1081ca4841c00380c0749040c294a01d00716000d000000120b0340e00074000c507500c61040110701d100d00030780f410740090721404100e80c2c0d04d02c0e04c070300c0d940300c1c400d00030056581d001044038904020140300710b400b103038801c000152901c01100c02c44000d1794482003a01c400810105510032a203805010400d82c43d11841d00da2000c5030300f090782408003080d112032600c4e000308401c000000103c0d411400352480c0a0b48080f0108500c0000864841d581c10711f507112540060a2050100c00c2250 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 253403660 1250 253402410 253402433
    0x190c0b030a0504170306030a03031a030a0f0b06030f070b0307210c090b0307090302011107030606030c06020d05040f05040c0903020405090f06060f0a03080c2506180602060a021b010504 81
    0x155100f00d500304007603450911521046d58850380c941d10001025000138001c1c0c0207200a04210000d050160b00c40301c004c07909258950b00c0403a10060384480c90320170046201c01660700701d0310642c002c02090307400900c80c2d075650090b406042407900300030000404041c460141d283c100388542e296100c40c00d41ca241100007510134005854041000e5510102c0e0907004a0240d0b03118407240d82da8141340f1480c0d5001991001c142280321170440c0100030303010011034424002d00000358802c0c64403040141c50048000e08101141e4000c104000d810841084240b5880c81c120003903820407900000d0300e1107008801d403107410199200035000383c102020098480008074074401c41441c1441610201d0352880104842c2002550803664803044841052021030380020180010b51541030884210001c0020880001c5600c019030031401c140607101804026400000c92201c0803507400d00703c60b010b06003000a51108030083c21010312503408101c0f410003030a404114078903509090700800607801c06040c0030310102c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 253404910 1250 253403660 253403663
    0xb0d0b0d081209120306040b030a0501090506074e0f020c011107020a0e04050a060219091e150311182e050f0405031506091602190c0b030a0504 63
    0x212582c00207880a100800c800180c4094115820b103183c1e6004100001030146600c6240c00d4400e41000400050092160070200f038003d000810345407501e100010004021402d0380700c100d1180c1d85100b0145603904480207402104100300c0840d60079040c0124204c0c0703c030b0740724520b0788038106142c21007030060315801442c012010100a200820f2026a1281c1c107100d1520000c3d088240c0b05000c0048111040443d500684100151140c82038941c98090503a004114802082e4048114120410b500301007981d004080010260b01042c540303541d0380c000180f503803040c6800c1a00301a07030700000611aa1020714a1040110b40c141c81c1c015412383e03221512641c0e1940c80c06035105107803220220340c55140d00c051040c1c120b0214841c051101c0c4040312280c02070214402d6400044c080400d5940c1c0c00c0c0112085103100c406800c003580f5040d800c004419001400b2003c214114003200e9110a0f404070b600d480c035071310301c460418400d4428138007030703403c00950340c00000c05070004001d00c02c0010a03a04050b0089 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 253406160 1250 253404910 253404937
    0x8033c0708060d05030f0c0a0b0f060a06080c030412090510030501180b090a0911060406020c01031104060903110a0b28091805100e01090f18020a0b0d0b0d08 69
    0x360390350000c2c8010f43e9500320b405440340d4000c0c031805070380070039040080800000302020303030306079030b04903541c018601e0800d81d0840e08903044601040070f9800c0110307410b0001c2c055882d0154141c1048500c1c181da52102820107000350b440030811182030f501550b9480b00601700600054801079000d100180186028022904100b074070f044030380b140d2103440c0a40302d000030000700140b210b0b849600401c4003c0001c1c01040301c20b41030048800d0707015520130f4080c100030a817507005442e8800c040c0c07000604072200540721407811207041c030080c014154003681c2c290590f50300c001c141100394003442c0082c40b4107030f03c1c1c3c2c000121003a0004a003001103000461101c07907040b0082000003122404801610300c00c083e405500000046200d06001907513407a044260440405908504401d44481d08920450001d806c40e07591103880380440302c249002c5201d0a1a06005403c412800444540c00140343e25058414034000300070109480e84e40300695402007040f00340050400c5010442464a001d0503004004080040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 253407410 1250 253406160 253406177
    0x30106231e01051213060204090b1804081803030c0a1a010803180907030f05010b1309140103030507021201060305150703020c060402040e03070203010603150b060708033c07 76
    0x280814505410700c00a050f103a05007080c07400241c0c01c5402c90010303c6500c0c8400400801d40101d080c2d84010b0000e041490000305500e51054180041440c902c0408120220703002c0811000c58080400c2d2080032641d01c107100041c1c12a90006495401030100c10402ca0294688207410424030045a801d4074007641d070107613000c0c5e0707848004603100e0144026200b02c0720000160502e482c5802c1c040340c1e03840320681c00e0000361080d03002d0703d15080316000d82220034066000582c0e0000c3c550644240b200400f0b04401c00c2c400501d050740e02c500002c1e4184001403c0c0900810b00700110354844100d8403130407003810003c210455880c00c02070390b240034184805030050001d42c0803074849846802200d40d61034161004004a403610360034000105202c030201000c071300007800040c0042e1303428084c03440294050740000c0e54520b8040102c00c200d807000e22400348210703c1040140001a0518256644040402e090381400c2e025950103030140700030040440c01a10243c404020401901000140a40314547d100b4a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 253408660 1250 253407410 253407439
    0x1018022a1507020705191d1b090117040f05030705030405010807030b0d0f03051b1e03040303200703080f07060c031e150902070c0e160801031103010623 67
    0x1d0303039401500c54034010307000b00c0010300040c20071008200c1040540c0070000c0030b0954070800002004912489109207210309014464034800c0e02841d0408007946200d024a01031080340043d0401c00f131010001038014020000909020280010024254000302030b20b641c0c10343c0745845901d0754444d0180c180440c00764404100054402e01c1030b40b540743d40180c41c0960040841e141c0e4803250700008000c40c1007040810400d00e2120b08120030002014164009200c0c0e0401c04242d841c0f2940320040805241c1e006100800109501c440a688a8141c0699040341c10140100144c101a0306400140220100050f03440c4d00e0300d80c0000030300d0f06a003d880304100b0340c01c0d980740803001da450300f4820020724094600e03070599451b460761001050303807403422400c0851356a0305614016038008500556440c86602c07800c201526281403044c1e4480c0d40409100c000e0905c070341015152000c180070142085010f00303e5044107850950210010b4811511078400f01c0d443d0000121114039030782c01d820b0080e51603002045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 253409910 1250 253408660 253408693
    0xa02031e0403020a1d151e2d010e120606060f0f070b0612010608250504060b0913020a0c080f0c010f050a0c020f0a110114030c0a0e06031018022a 64
    0x4101c400e000b001c80c140410340e5825003400e0518003489507445410084103140703101003c10441c00407580c1c0c0c40c01001118238940058034684401076a2801102500d11480b55824045115940310300c00715040751f120014407900e20340c5c50081008161803075000042d240c0501079454102d40c8030308011542d0151102c0401c44103426903405116983c400e60101050243c03d1a101c1240c14a504c007001c10544120303a2000020140c40d007a5004801c100400a5a050103003010026014916114541549419080300008214600803c00a010303582d0100701502400c044100319507602c01c6040c02440b04100700701801008141c00e49040c0501440c0241c541d10245c0003040c1d1a088111420142080c000e0a0316550103035180d901503641001500c642c01488403c103000910b004086056040c0d454034820000500006c04038440103220744014010810005480004a0265111034401c0d081c07c068036101a8080e0061102580300b021b0001410000d006000405210b060b003054200c1e2aa0080c40d506803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 253411160 1250 253409910 253409941
    0x220c1209061521030e0103020f031e090a051902040905152a220e04060203060f010c020f0d170403080702091b25060e0109020f060a02031e0403020a1d 66
    0x16083c0a60f407941d060200703014040e40a8102c1060501503d80f4a100702c07145265802142e034a584001902000c580003070080605030350060311310000744440d0702c0c103071241c50366090f81d188003412808a0015032411500c0c3c035040301035a5a80300c000c5400c8011262819503d850089401c407460f940301e0981034503c0d204002800e803016060710317106407816207241004003540219000c80028405e82d124001250124841000d101e2401a000140c807414041c1c1000452a03840c0b040504104c0000c03215409030751007078145141402c080741c22440f546080e24148280c00c00095111301e1f8500089400800d101c107601c01030074240e02c2142c00700c80d03599900107800e011540f401c018990740407052094802c09027090003402c1a2450031300800f020030895a80781c00030313126845840e81041e51914095000c5040500008515140c12103003541400c5da4090001d58901612210302c220f42144448410b1103c0d4500454000d141c0142c031203481171b80c81d50344000d103000740d0b098440d806480c0c040c005901040c0760102c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 253412410 1250 253411160 253411199
    0x90f060f060f0f0f0f040f0f080304030b010b0706060801060803041a190f020703020d081b060402030d1b0c0e040317091c17040c050f220c12090615 65
    0x107800c11400303101c0c0018075000b8400d40800d205081000350741540c0c5880c0600000d001c50301101d6801c5013080c002807142c01e407031b0b40407049e1075209005c14400030700d0741c84640381910b111a061b50345030440360601c0380203050694045085940b07055030100300260040014400e84062180c1c03130f55005040311045c80d0500c600314400285020700d00c030084001e0f104018000d102c02051046030091500d94000419450044000b2520050000f865030200d0800b510007111800c2b041c00902028070b055004251169800c1d016a005c224281048803010103580f054001503a40003110301841945501c09004001410b6a0550206003440081500c02d08480c40c02c612691044000d4802c0a480c01e140340c4050f03c1c0a07c0540a00101c03418105403840030000c098411801054500c10301391501040c0000d6007850190103010b43c000c1d6107c00804d101302180025161600c01000400c6156620200c8090400d034050410b42801d12a82030b042c012543c0104010750750341281e8090703007556503182240e820504001d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 253413660 1250 253412410 253412437
    0x15080309010e0a1203050f040f0b0904110705060c0c010908030415050612030a0503190203070309021002010c080402060306030c03030d020705010b120a1202010b030f1006060e06070f0f02090f060f06 87
    0xe000c40003070310600c040d10360005c7c0c4402090400362600c0c15641c1044007508410924070010608403954a881d00900740d45c1583c040d02140b600e80036032501074890790003d00e190029580011206200d00007584200d90742078000c209a5141d0629144c501c0035205080041800c06041002080180c030300383d4400c00c4501400b0005505e40201a00151200e81009000740301060481494040118850004520420700d55400107009242c0c0d1041020400405404400310380c03400c10f25404075600700c24010f1704030341c040f1030154895964000182c504003580203225098003011030303c0f02075095140c002c0c160a502c9030000340443c410002c02e100d1014032200d0440f207a40e00c072010020102d0440e245080005e0b146100125941410a0120786007840001140761503602800c0380810482c0c0d80d1203507030f000d400c5a02c0d010200f070500e4000945580101000079005a09190100c410400d079443c0c001c1c0281d5024160356020700e1f001d013100b0624101210b00c40d0040310303000241e4607a032904004864000c4031100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 253414910 1250 253413660 253413689
    0x105060408071e050901031a0108011104060e0307030c030c031202060c091c0512130503030301050a050907030b09040c05010813210c0203100608070909020a0b03040615080309010e0a 80
    0x14401c0001003c494550721074200a03040204513a101ca004c1c1c28047d50281d00f038004944407176490384030303022016032150107140d02d044151100c1c400f04000b250125140d5140c040100040c420010742011456070005101b401e00800000c00c003d026509201241e00400e03c0708280509080c0076070b154441102e020540c4102081029031506d8801714094402031030b220500459039481c0d0f1500d18001001010a40c60707403020a1a000a0002c480c0d014054103069001d07505551500010849509003401010b200d000581e00290882d4813035800fa02001c0030007001c1c90300710b040604010f2141c110038000c49000606150020300661010000034508560007901950001c5003540010980d11000710007104200c4808180009aa400c1000c0c01d210410340c0000a440380c904a4414541025507212040c01c1e41420601409640c1d03642c0910100d0f200c1c0007030b03903076a82c1c1c90b450400000c0000251201412000301da010a030030000101824599500380c850308040300c5200e00b00303c0d01040c6807081001404500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 253416160 1250 253414910 253414919
    0x506060912100903081f0e0609041a04060f0e0604020a1a0906032d010305030f0f0c0a061b050f03041514090105040b10030302210c0a0f020405010506040807 69
    0x711540c4001c240070070654040c85000690801501d15891043e0000791500c000d01400507410f01155400710038050003e00d0003442c1a680c0002c00d98020401446404000002030510141e00c1030511501c2d00d5902c404c8007441c281c40c000c002001d44180d104a40751806001200090b00000c3d010300654004020a0515180c5000c2e1010003010360380a00308074405114144032038448001a5004200c001480d4a0200051904014803e11900e0605159840d1300040001c104048101c5000c41c4581e40001d5a484e008502400240b02e0307180d50261921030141b07044180301140d4407503007604e40d0204c14100d402030b514200715401e00a02442c040d13204810004500081e44400144048000030180440e5011085140244802080f6606070702651a2800c020802c80e014120307c4d840350300300702032120031400c40d10000e54a514400c020845440141200240c0c07001000c242c48181010408407454581c062500e650b1003021020100e005504040000c5254541042510152140d0800400f61075160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 253417266 1106 253416160 253416169
    0x605070302041805100f08010507020d020106050604090513021908010501080d120b183c0c07030c060207240501052101140106200105060609 62
    0x4000500200c1c0c440507001d50050740c5060006185d0b9030310a5644a00d07005504102d98040b03614000207101d0605400840c0300e1a0290300703540001c2c2d2400020703820785000c2c2c0242e03039100c0e83c00c1c0f00c28403150109600c9141d103c2040b80d00300c3d100341610b40100d10300114403030141280d443c2694003444610b90074042c030784c01020814000c00143c40c1236280140b81c281d080c0741408a8130b031211711740c0741550380e000011160161103c1080c141c0741080d03031606200071110043d449203110b010351482500b1401002e80c019059004050741040d82d03034021518130f00d6110690032014800380601031008074006201401d0124801c0030341507419003003c42c904445420001c410b408550401d00140204d444403502e802e811324a0092421008109403003d41c0501919080f401071100d0880000a82c158040e1522489004810102611442d00020142614003c40d0400d4100c10104507914031410f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 253237410 253417266 := by
  have h0 := BRFrame.cov_init 253237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 253237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 253237410 ≤ n) (h2 : n < 253417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
