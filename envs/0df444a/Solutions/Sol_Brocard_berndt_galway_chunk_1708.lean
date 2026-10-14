-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1708
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:23:08.488574+00:00
-- url     : https://prove2.me/submissions/4cd1731f-dcc8-4dbb-a037-c7cc28090060

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307014388 ≤ n < 307194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307015638 1250 307014388 307014391
    0x1050c01060e09030d1a0f010f0e0a1212032904090209070c0308011a090d030e090a0618090812190923030a091e3201050a0f05160605 59
    0x4651351000030400c0701c4280134062102c21410f00c85e031404d90030010702d002a484030711606500e03040280000323140c1c120620411a19148040207090700550b82c0d00c2d401700b02d1041031075038800c1d181c0c00841100e2402d118881e104000849405800d00c01d101d846000380314442e0100440c00e40e50003074550050300056901d0400c0c960060055031200840011149000b900c040e00592100f00182889001800307544612412a2030b602821a14000d14081328941510b20044103082c041c1c10030040010031080c0b080c10384c0200e0035143d048c881c1510000240733a2010585070700240c0101601c1c401d0000c800c0341d40e5605a4a500844401e4044003182c1c456541002110901c030015288031504800031000c54074010380c1e102e903400380d440c00345140c440c9262014140a410b4820342458028103020030b8251044010300380c0150018000c0c0c107250190005071000700c1c02480410140751200310307000d00d400b90300401c21501d40000c141c03184041c100c104c1200f90b0700b58200c52109800490000340c00d400140c40f41c03040c10f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307016888 1250 307015638 307015651
    0xd0902090c09010f0c0b0c0a1209060911040606120b010c02030f0c1936020403050102030105100504050904030e030a02040e011508061504240305100b0402030c040501050c01060e 78
    0x701d031142c000c14001041e101003005802e0134015200303240c40101c2c10702d01070160301507202105e4aa40301c0030041c080310b85100c90582102128500f41c0d20a08000c041d4010b14071660064a84200080c40c00e01000100d84051141e500820110b81008001c1c45a58110301d20110050601d03403c03203101070700882d0034220800320360310040d04881c0414059181c060b02007505245684c6150301e105060032a24030f0711f54070861420300844100e4101e04d5203045040602926020200300039525580c0d285006d03030103500700b809418800c904084540b61403611407000e0714200c40c0000e01d0f80c01d4684994405842c1410303480c1c5c6860301800340c00c0452001d6204c500900d00d04007041d00000400e5645141c1a600300c0030700303400842072070b0000300c28490051140300344030307010303003070440300040c201060114148821008012680f08003c0303054000060207408a400600130164503401d02c413200c840310400040380700480c0c41038a5040c00344014800355104002410507030558100000d6950380712002c401c1c1241c0225050b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307018138 1250 307016888 307016911
    0x7080102190c06061e031707020d03050306150a0f03061202010e0d060f1a09090a03120c12050117060114010f03240906080f1b06071505070201020301090e0616050d090209 75
    0x2c06c1000b8021449404143c2003903210343c1803258681c00034210102c0c030070001c1e04000001c00400c0c01c60b6100f90400b101608a004026135541e030000740588040c0301039012002207854a440010070003405056540401d505a482e00c0c21010314034100700951001090a5074400d81d6170300d01449880540c03180c4030f4418400d40384030100f501c850040010342d250040000d09550410200d4130002a0404040c02c40c80c94124004980340d0060441181d05200400140c240c5600740000010648500c2b002440c1c648404030070f07a8002c2c3e80b41c8049201c0078040c002114000b40240f507410180b40d03c80c0e480741c1c0204883d40080302c80080c400b07001001040c2c10341c1100d00c080e80c0c2c2d01810486000308005403280e01000002515100303180c1090b08211143c0c011816008941c000354240c1000084000d071034004610107410452414100ca0081c004c1d00b09008005819181c8a0101601e000000d140c44c441d60003c50b0303a8603008007000c012605900105c021021680c2c541c050000144e41d241c40c894460104200c0c2d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307019388 1250 307018138 307018199
    0x15190903170a061701091505070201090f1b061103190c0f1505100321030225031202040308091e0612040b010e01150c05101b0207080102190c0606 64
    0x400d402c0c214504c904d242066803608401d800002c450403202c00c0798401607080042d0f2603581510983c0505a4a034000745081c00300300c075910800072901c04401c01030000128080aa540b40c01c01900c42c0080c0700303141303401d0390700a0003024031200656010066007900d40c80c1800e050780c682e5840740c03c0d100300d81104850401041519121b0038a10b4491244d1120707040010fa0f080c145191542207003c6010700c1c09039042000c8200d5000c85600a404580c0050a40000c10082107074460540c00212084a002c0700000c80a220080b0710421a0080e0380c19603401411440c5000341030020090390641500c907200d5103006418038240141c0e0b55901600b59030328880300d07604540c034007450509042c0d0b0058100c40700030018440184a64610051040200b60b128203000708081180e003041458401c003102002901e80c00d00686164641d2122241054030903140c088610309601d881c041c42c282d028443d642d01c502002c1d121500c1555211b9900e0124040c0140c074006140e64442d011424060100c0e040e07600c800f8000007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307020638 1250 307019388 307019399
    0xf061e0c0c09020a080c091c060b090117011808041509030c060207080606030a051f0b0306010906050f0f100c0602070503030c0a0908060f010b0c01141815190903170a06 74
    0x11004e80d4003141452207289087c40300740c0002c000c440e42a0051381c001e000c1d100c000e8200584da5201d00c0c45071600810b1a6942d42c2d40b01c0c00c0c007624001040d140d00c0709500300784484a5010a050410040d1603014844605082c2080c403c510b1030b4007200160b80c10801e030719200101054540c94810003030000c9a000d06020790404020914090020300f110340240c2c00f0000c103101080c00806c03104004001101810840204852444054885200000d601d406035600004049540e64000b1080352810b4498594125680042107480c44d14500c4040c0c0041c11164518500d40c0b0954954002600c40d81005052100c00d803500381c40d6400c115050710000000040080300e0310b810004000040808400820315454a60301d640d007507038010310980aa1050200e02ca034420002904000aa515020006415484c00445808060350203000c041401d00410a031100c07410316024240d482070b500ca82807020150791030001da070000d1440080903800c0110702e00300280984070008000b800742c50030484c049107550615 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307021888 1250 307020638 307020647
    0xd0e07050f0a0b2215080601030f0b0a060f020a0c0e040506010509010b04090b0a0933030203060c09061e1c052202010e0a0b12010f061e0c0c09020a 65
    0x56140034442c10038040d003003061180100c211079682020118681c407141103001c0d0400c00c01800d400002d4030400146800340300d9540400032a00c180c0d004d07031b4240405040c5400c101c00f21070a10541c99044000441c06204540c001c3c9051600010140704403101c03c40141c0b42e600c100c05481d040104110110401d201c14400308000b49805840708581000640d45031003000c007070502c5244070b02c01d50303941c40b541488002d540b01e460607001009800c406000d01c00300041c000c040e61039101d40300c02c003440002c000b07440c0c05801c82c648074090b681d014009001e40d4840b46282c24013604400d03e42607010790b00300041c180140200c201d640c1c0010450058a40b10542d00c141000c81c000001c00c0400c2413840c2034104030b1060740c0000f903491190201100170075441010700048a0032103c500e0380301e4000240f00d000241c2d14240200034400f00000e840039000701c1e620f54074900107d02c540d2043e40006085416822924503103802e2600f13408003681000c0c001c096056070f0341040f1460300ea20241e4004e901045d0100e905410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307023138 1250 307021888 307021909
    0xe0a09090c06030e071a07020a08010b041109010509040f021306080a0c031b051605070821030c030c0c030705010f0c020f06161211030a020a120b0d0b0703020d0e0705 73
    0x3d0905015456503140d04507590045481517007400d0110185042c40780c0c29a504645041c0c1c1c0207040106810748404046010b0715020454034007862400c02580c0d220220701e03003961070b2290142e5610b460700406004210144c240400a98843d1341d00b080005a0b020b581d035a44002040a910f82664528005407100100c540180000060602b00a20305c81408400701c0101070711001810180c2d2034488070b501100451148002c0185a0b115030b241c00b08110704005030502d034050100400308004068410b0030042d6000523100c2d001402c9040c070106022440004c060103400a036401180e0620203203071a001e081d00d1440041031241641c070843c8401c540e9040c044154810510001819581441a070440b10a00200075030400c0004c500b100500000490b00310444103107904218644a0412501040095100740901c101050309070784003024800090245a070b032641c005007143d0312140c040e02c90060500c0001e00a0042580c200810050a1010b00c80c030110341340610020003ea505090602c100c076510b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307024388 1250 307023138 307023149
    0xd020d030504120c080c010f05010810060b04050105030c130605121806010608090a05011406180108030406030c030b090a0906051509040204180828030e0c09070e0a09090c 75
    0xc0c441080081190f088401d200550342c3d2600d40d079555000e040c598498010320596060075420030784542c1c0303488400d40040781a520090251200079900c10181c2044800d184902403156005200030003203580240042c5501a604421941c07905c90b416101380c40b501c3e025000100814404900040005000d51900d0380c065100400d404690150210840da2048140328907420800c00c40005001400140b08600c2510392110080c410303420011107668401d2400c8038400d00849c1c1c00a060100c08044815550407101918080d518260030180120090030b6040540c40030b16840349040c112540360641024401c0030300c5140050035020625010069810180c0041c03444031003a0a4001c0c2942c84052181c2c100c0d0307040f100003900403131610218940443c0b114020342812030124540b034440510310a00040951036900680f020501d4207019400c850105513003100d41d5100c6202840b40e0300302001d149810400d541040b94603800004009200642160006040d56849004d54010092804a104003510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307025638 1250 307024388 307024391
    0x203010609140904060b040e010216060c030204050109031415150102100c09180b0603010b030f061c02130b03010c0201150e130b0a020903160e090c0603180313080d020d03 75
    0x2c0100000744150030060b102402080c1e036500300c268995100d520442d420350480000f503446011164a550350040445010381c0e496007006183c0b0240c81c468801c4806594058503081c40d52825901d449a401c0d1403900d14401c60f10841150003100101e5840309031103850507001c41c060b5400740a00090611000d122058101402c0200100d10703250004140c1050350b25030154020304043d500301c0352010341440944903410003c00000442c41c280400c00841c820a041390100c14661100c1c030511200b80c0c0c461992160341c64102c2190310061900c51220845246101c601081d01d0840c1000a42191104142900544e44d1428068a41512505824018100da40741400b5034901117243c0341d07507440c0341c01009010030b80510000b041c41441d03505590540f84050100c840340f02c10440b0b2196501c503140a080591420724002481e0031500084260344680e01801d602c0c25034445580d00c65600c0e442c0e03442c3c1e07203082c00280f04a1100746510b0480000401c0d000d0000c0450111448004e1304103901c803482a010507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307026888 1250 307025638 307025669
    0xa050303101716210803011419060903230105070f0f050f0d02070c0b0a0903230a06180209090a030905090417090414180c0301090203070905040201020f0f010203010609 74
    0x80d50600480f008a075001503410b1065440020705000c2c588885400405a040106c00030950b564052121140c0c2402a14080c070000b0a1041d61480654240b10768800140b001c00d003440099220040d0440308040c0115403900e209103100410b0944804980711000503031907681c4001c0040d44058880c81800041c2050b51414440d07004211191040200440100c0e4000a01c3c10400c4402c00203c2c00501c490031036980c44a6482c3c8005000040c20710041d00c4c0c085c0c800c00241c10342844480d04c0f00d0b000c82244002c0800c81c0b81c1c0e41c2d881020380540c00c240500d2800c00c80c2010f0160700c4d40d0100300c0c4107020000103050350f10ba841c40d0203005412940c2100e802426a44200400140d20141d8000001c40b070b030020a0325030400c90001006400b14020440c03118682005000c102011540c0010b0001d40000c00c3c0e548000c1c0b40014036080300d0001c1d030080c0d4558003038601005040400c0d407100da080350042c8180c1c2e035058103004050f8035208504c2c019000e1a03500100420400da4400071300000b80000845d02400c2c6d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307028138 1250 307026888 307026913
    0x30e2d0604061b0203031b010609060b120402010c02060d0f1d06060607080f16032c060d050613050c12060a060503041121030403050105010906030819020a0503031017 73
    0x801c0100c0f1903e140d14040d4412015990100181c50b86d012a0703660350b00c400088984014080c004901c101d40a950518a001c030b2541904030131344060101d00d18413160309640c0c94004449008065038181d8002504000d4040000040c0c050a561a0800080072401e0344c2401003801e00c0d52181c103000401da401242c20301c19542d403032000319500d15810035106034444080c150349010500c07c1c803842c24010800f85500b1000c02d0382060755911100a282e00700c2410300200700c001590700501c040c80c1a84a80e0800648007902e00c181c1c0516004031010b8480800000217045110840742d064078000292403022910407a0400710304495030380f15106881c8400d9180ca4410054514040904018072114503525210303c0380d1a103109424000c05081101511401c1440166843e84d02c81e000070384184d420100003281601060080f0000c683e80801c0c480d1401d0020141100c85c0d11003248440300b10f0060405600129200300051805464509407002c0940d10304020b6040c1c103880301c40401c0386a00400c1d0261030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307029388 1250 307028138 307028147
    0x90c050d0804030f301211090409060b0301050c04051002030909130311060f07020d02060421090f0e0f1810050618090105060a0602070e010501030207030e2d060406 72
    0x1100c4d07200740d100c0c80d4143e5528080444040011443c00920307840910803d041c20068503032044424151031b451185c500025001007560080765800180b500200001407103402c0c80e17407260b01658054900007890100d000002400d590f800c0c1c0300d015001001181c1405146000040111100c1850000314a03003817a400c0419110301c002030103542221407004100080c540203166107100f5080764026207100e403170b0a549800c1e0301c6806503403100045c8140c503a22a10310b40002a4a4051a0010000070119009403002c1c074030340a07421485c204002d10654001140700f001600600902280b00082e061850000b0041501c030b03c00800d03461803d003003039006610403400440d00e4452410150b0010a041c0d80e46004154100d4005094510305840c81042064407081135000900840048420b144d0320350341c88104aa48003201d025260200b00711500402071513000303500600d12644281442182044190001a44d03c04001d800d0413030390341c01c1c01c0360b03449550500d01c00070507505040714440c4c10641040700062 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307030638 1250 307029388 307029397
    0x23040e090c041401080606150415020d090f03020d121416050115050612220303020c01060e010b25061a010201050a050108153c06030a2001030b03030a03090c050d08 72
    0x14058413450000100082d0400200c1e405410301c0c852116041e82280e80c001d54411681c03584400040370314802041c29060134403900c003200e400400d58410030340d4548070110340140194008043c44104085c4015442e54680546400c0c071401c5440c1900c0101ca0500b242542d03514a003010015095a0041c020380e0740705410784413041c02c50090740c040342e81d80b0b11040860580112415806501c242410002c0641c50b400400004500b98002c4c044542d03a4040c01130031071000e020b55244000140304a01c00c855a0707508521000041e6202100900060784035070048031100307100420101000044143c1303c0d602401801c3d000b014040d030400c059071408401d00d485580c00300c80c032660f0b071440d0720110749000c0714101d1040150280c50000c490542030034085460080e0351008540c1084103000010340f480c41c0c017092215100d074001c02d019101350195025042d1010100205506055880c10300d49480d0310100040d00403407501c1e45000414036401c0c10300800b0304220794403452250040141183c0042e90760010759 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307031888 1250 307030638 307030651
    0x6080304150c17180a050303030c030705130f0f032f0f030304030212030403120c050a02010c05150106050a0306080318090612010207030507140a0323040e090c0414010806 75
    0x1007500b400545401c43c3e0102d10503819000c2c0f0200820003500450f50a0205410458100d03071903a00c8076510000d0680f030340404c407104000700500b440040c0d6035038001c2e00208141d06045d80b103250181c5c0c8611806000c510795800c11181d50021110500410070140c000010701c040490854a9060050b05000c0041141d0707030781c050042d40f8003c0d9007071890f2020401d40d8069a4000c011b040c024003000700565072500b00e071009031810704000c1d002c803c0b07041c02446450000c5800001900c09030805400640701213603c0d0908032914131541481c4443d6541a610380b6010741803540e40c45595004214004080e55020740095040c1d070410004480000c1503079a0040a07140c01382c4160f000ca0391540000b82113603401d560070816650001a02070200f542c00030007890f01c1e501c110480409002040c91103941c483d090b200003030114106070400340c010b0b440c0705202c000340c00105a04600d004e449012915403082c050b2481c1c0c00c981d10500746a460f62509025994140350b480404100640c540042c1ca50748120107800b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307033138 1250 307031888 307031897
    0x1201092102030f0f2503170c04030501020d05100f050a090c03060b21181b0f0a080f0f06070f0c030309020901060c14010515040b0f12030c010608030415 67
    0x1103510030340240181e0b030800b08000c0b070958842c41d02440c00842c0b5481410300c01c0840c24402882e0080580e40300701180082c0d0103a643c0c0c00640c82120181ca401c0311301401720500c0c00c000b4040000020b078240010240c1221131107022809042c64080340740d20001c181c0241040ca515140d050004d5219900340c44204d600c0c003900450103407884a0705900600c4582c00a07a048000000d94144078107650800041000d0403215951055071020440180003110904d410b04c1500001c4c1c8000ca41d28a004200405040080c004080c160021002074010307481035220302d5698000740c5407050028018059400c15500d0721026040c20f14180800604007401d1112160a100c4d40242c02c2d07061620a85c8107034513007540500740c880c1300c0d41c41c0c0e140600041c80c1c0c0001201c5a98090080c0400010706004460003206d07030141407148010844204000781411030044c50300b014a8800070880765032580d6a440c0c1c2400e4646c080c6da0380f00b202c5030b4810300391a850f40051070b055000b044100604204ca4040d040e207005680740 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307034388 1250 307033138 307033193
    0x40615061409370816050f0d0c17101b02150403020a0b01031110020106050a0b070305130b030601020f0601030203060c0304210f020d0c080a03090206120c0702120109 73
    0x3c4011002408808807005951241c1441c001c0e2a811803800c05031841c100c103d5661101d83c400018071042c0e03600503035402c41b01803401e0400f181024031541c100e10344070f69102c180064aa16010410103022010860b990b4403400b40080c000440b4801c05a02c228002010310a04e502c1e580047d41c5c80c65003590a080b0758903448000b8060520a1160b8400c840c0d0100f001465540e590401c1e61400b0707181925184200e802445141d144c900510541045402c094410a952868040c001203a42c01c1a07030140d003030060800485111400f081500030240c00e511100320b4507070900200082c030348049140c3c0300d01ca640c0404c0061000d40d80006545512030201c80d0a266030b540c131454034040300020b43c02641e180b0300c05003234041c15090300948880440c2820307608442c07291070f502c02d040755026407a40006e0070b010320030002c5407826131007900082c560a0000e441c071854520b890500d9914100c04941d5280038040110321001140b81c80c0c8400007142e44024001d00c02c0007056200c411408440b07020768520711280d2038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307035638 1250 307034388 307034419
    0xb040e04141b0a05190612020903070b0409050f15040209010507140f1603031707022503170901050901031e0911040e0f06071b0803040615061409 64
    0x11084200d05000006803550103007180503105003030710960612031040f4107010b004101d9013412180b03007082c612400d00c81142d80386030a40070340300362203c004008241e640800070f00b2600c0d142004218001c0c05e425451039550f610304903c1c3d1080340c2c00031300030505405031030051100c000c4104102c1281084100d0340140e0300c0f008100143c905101d10f241c020b081250b111101c0b03104d03070780208010302c20005160a58200350304000c07000a8042090000030041104021030810b1710501009143d8040201e0040b123025141e5504516012030a2400f00c120b9412803080901c1000340d0907140a555049c803443c424140012a00060018042c01312000e0426548005041e49644405e008000d401c082c134604202d2880e040c06c0000c080d41d1626041802039080c007405e5251010005407040b8041c8205014010784d445500c01120218801e602c411500001180300c2c501040c000001540254401d000024181041c0303240c0c802e82c4160356000300180300c03000710803c40c281c48480c1100d10207001164149a881000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307036888 1250 307035638 307035653
    0xa0b060a030b0f0a0e070801060203030c0d09021201020c031e07020105040e060d24270b0a060806010605070213060b040b0705030c1b0306011509090905011b0906180b040e04 76
    0x2c9680715440100d00c10001713031480036aa116030041d03465035220086c2d681c840300d00360ba6a01c0107580c1c01100c4401003003600c4c081c40ca19400086c010b48020712181c404003160401da801da0f08541e0140002e50000250340101951600e14100304860b2862454201041500007803d00d0080e803103110912188040020001e59540c0540e1031841e034031030b220305150324804882018003030021341c00b80101480d280b421250040c0340000f030180c1d01c03995510710058000640d00c540000310043c2030030b0806a01c43d0404078144070b0a002041c003804c541d42c3c9040d2200d02c64010480d9403000740e85420070041c40d00c8000d200074050036007154140c80308940410740c3c0385428502185140b09407440c1c44c000d07004002081049441d40c90030101c03009812402c0f50f80c1c60b41c070354800c480c00008062001c00031406040c0100a20407040e040340e80e640d4000d10000444030034240c1317440d0503c01c0440c41100043c0d00e400013400015005079040c0d00300d00c04074190010b030b45d0900d801101503102e00e014103259108000300150400011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307038138 1250 307036888 307036909
    0x6051c0c0305100905010e0606091309030c1104050f0a020c0a4805010804020a0e070e131104030602161205130e0903030a15080f03120a0b060a030b 65
    0x2480800101200ca540100109000d5460901d45a45460001100754071070061351305a90035521201d0054903201e041080c5a40202c43c5140c100300c081100c6107018801d031080b03000580c040d0b120311121080328501030f0164188007120034441c0d8035100601c8488007480d44001ea1210030040c0050341d4540780c504480c5001030714080203041d080c0005141c0403403d4090205081402032905221681400650041103819810f0f2181c5031074000007000c1020358480c006950f000b60028108c241c6294942070032200740b04048542401043c40034840c60994280a1284d9200360031042c01040b8803440300e8501c0e4094800da120103011190049903103401c80d4440488031540c5e6038800c406c42003044640401903c03541041c1222004a0700f1b0a80c005440c10740c89140034415040c11015510310f941c0c82c04008010441000d1030268000311a42c0070920003000c0000c0d802104070080219244c6c5400340f0b85800d9140010f11729641c25083c100070034120345403001070b40c02d02c1d88142004602141180007184000c0749 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307039388 1250 307038138 307038187
    0x3020c06060103090516090605030606040e0d0c020a1802031806090a080f1308070f0e13231e0c100507080a020f01050c0d1514150f0a0315080708070605 67
    0xe0b00c0c400145100d00c90f40035400300e2700d0980a980d031540c0d0b500c003000101c80b04101c4e183d1886c2c0101102948043c4a03100300c00c8814402400390660300e48505100c0d4110040f111046c5140d60300100b4860803080d00e0280384100d02910008002030700d00b07055001e4071240c0c00301c0c00408801c030100310010421241e07000c1c1c4901407446e914050000b03070f0700c544941e664030300384c0710f0350164513028000412840c1c01312446912580c01b180003410712000564940c1c1a00e8200b021091010075040c001d11a180d005001801041002d800803121881c00c070841a4208140321213050710811007000c50341e540d01e41210a841103141c0050b4101c3c0c4544000d0400c0c5e040c21001d03010100d043d4a800100000e03c0450005841c1d02c9114038010040c41d5140c0082c9400401c0b03d00502c0d064030b070004601c140d146810716000c400c192126074210301f045c416041c40c0115420207550745001c40e8a8068a00f89506015402801401034800a03d00545001e52494981d10180144000c01000045200900010300c032000752415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307040638 1250 307039388 307039423
    0x207082a0d0c030c140717030a0203090609210105070314042607060e150117070315061a0c0d080103120c03110d030606121e090302070b04121203020c060601030905 72
    0x5404100c01707074407a19140214902400149080d2030aa0400070a03030311a010160011490920580c007044095001080000c0d88050040c4c81000756540726541c44003d440c441c400460981000b02001c1e06070b603900390382e803220790120301c0c100408500c20040000034295503825007501100100030845280c46801c40286c842800e283c000054413038000740405450080800807040f90743c07901d80e02175042e50448001102d80c0d200e1002800800c120f600781050b100302118000401d01d964065a02000413272240001c4864030100d0000b01d42d03c01440309412f401c0007483c0034403c560541d0388644030a02100c2e40c00d000c00820000c01030405001e008060200902042100d12100d68400d00801800a60250b28000b600c0b1001441c0600518040e0807806138241d440f0100745100c46000c0c400034074440e2000d034118414031500047c03021660009202402d1900d00380384080e4520f040c10b10314292076900c0901018810001100c800401007450b5030001e01c240713008110302c2038604107503181094100fa482c3c0b000d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307041888 1250 307040638 307040663
    0x5120a1d0a060b0a08060f07020717010605030f0a050a03030203100513090516050102070608041b03031107080706140a110d200613080d0608010207082a0d0c030c 71
    0x4880000301c0840c80c52207250140112541c40b4280208070312184540b0f04150f11010104c2c03462440714000c258484028811030b00e81030790301c01c0580f02c010a0452003140300d944d184014040c6040901803645a50500e8000f40224103081e6a05662841c0c03840c005420540e0100c040b810a1114542c1c245c01418000d12400b4003102c50780e4144028a2143c00485140c400c03c3d003030751400b4104142d01c0c03045440503005008200d15256040d207998200410403140c004000142002540503180e208002d18066512502030300f12213a41240b80c10503d800c55036241d445041c04110680d440990801d1503514550003e4031140040c1d415100812070003920340d134900914100d0f804d060f52120210111400d2141d00c684c4128030703d04003070717100c40042c1d411024404050b8032280101c4e80d6407005106d2025912400a02c00755035410580c2260007800c4120350f50400000c1142e05d1540c00c00d004502c0040000d4041403940550402550f122140107004092140855442c1c1c00d150086400f907502c96001030b003a43c0310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307043138 1250 307041888 307041941
    0x6200d1403150901140906090903030c0a020313030b040c08032d0c01050a0b1804020f0105030912030426091e01030b0406120302011b0203030103020f0a1205060603060a090305120a 79
    0x20301901120354020900c900011f101880d101c1502e42c002c00004c0003a40c5181c40d0f074054100242e10108060007548010045110146c0010040300c0045010381e1840201e400c184c9000340185150750300024581d03200b13014031107440404c1f4082590105010101c0f0000b005120901c2000c0c1c0200400c041d0b865191000f0020180c2135500b041401d003a085480c03610359804600d41c03403084e510541d4003940104603003c10380080d50244004680001c0820201d0300e03010300020403a0305960007120221800748034991110401e07401d500c0d04280300c1d074003094564104031000d40400d01d00e2008000355002410700c519025810b03402a4044150001c01030700500c0001e407500c82040c41826264004c4005600e404161801611401c0940c1d4204030fa03503000c3c52a5902c2e64080045001c014410146d1001042c24002a0000c52a40496400d849807020f00383c586800000c15040210090200c00e0450600b902c9000080e4004c2c12a009035481c183c1030740144d210b0300c00d00030003800d01d407032888221542400010308 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307044388 1250 307043138 307043159
    0xb1b0613150212010b03090a02030f03090a0501030902010f0c061d0c0906040b1c030203120a050a1104120b0c0c030a02071a040302060301050f0103090602030106200d1403150901 78
    0xc44078000c0076100114144140904100d10903048104242d0550074010301410030480300450f0090903100c1100c07205a034a40020382011201d459074480c1d6480050800d840d07041c01c2e4003100c02032400b42810048860a50000b0b040d800240b8a003008000080200401300b0840c0c1c0c0c4182030700312101080d41340c1104440101951401804056031040c0c12120001d0070070700e0b29000c0c485045402030301c04407402030b070030422041050041c0700440545c0814081c10b0a009070a1a00341d21070702200c0c00108580c10081040c1e000c580208554403c001010002408552001c00d41e0307036459a80b01c082c0714a6940d687c40244c900d805000b890030f103103010001c2c12800255000800900342e90f5101031004d010508400b42282c58807a40c4002500520140010001444c00d5020851640d806060200d422804c0c0d40e207840072a4400d030040c401113a4181203c0800c568031501404c1c450b0000300042c05008244040900440b804d5945400180c0b4000300003045001503c0f07003010386040140115a243d61034950b05003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307045638 1250 307044388 307044421
    0xa03060c12051f030305180405040308160f0f0e0a080d0504030312060f031101051b0708010c170402040c090e09010b120d0e090a091a070f0f0206010b1b06 68
    0x4580380c14040420080603003440c078203038079005103d8031000b0759155903810340d0b59400225503920440c0c003070b1040441c0358480d0b003e070070f10591103650382c2c41041c50400b106000b003014180c04041006001040c10350741c203030400c09845492038182447c2c0303d1140c034807002a04440c01a040075004d801a101c01ca061150010050300940703200e900c40b200c07018900300346070303003110b02c1442416142c011070001003022402d00d51848004110602d001803505003c1031400454486002100b642580020340400c520343c001c1c8280a620040351034180d1030810310403041c2000f00009000640f05680e5403400139441402000d41c84020801940c50001601d000548207009080301501c01d401041d0590341c01003441d0001c01c85529540741e541391303001c1c00c24140050184480700146050709a542d20881d4001180000f1102d507020200308210b2401c07031400a0004001c10021400302d4240004084548a0250042013160640e07114030b0120381c031400f01d00760114801d078400d090b4944a014410900c108143d0701880b40c2e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307046888 1250 307045638 307045667
    0x305010f0b10091e0506030709050f0d0f1709032a010827070b0705060108011409060114041b020105071715090903040b130608012709020a03060c 64
    0x401200790a01e041c0603040c9544408040090345a0030240405138454660b0200d0f1164040340010b004d1300c801c00316809520613511b840c007040004204026920700303c111004444c00c10385001021064582e0340b0718684501d008000d0401c0c4041d2401004040d8503c1079400d43c0340020100d8066007000c0b10181d4509811070202d0381240c007002d192410550181c4a650b01942410120301a00e4051081c407086024001c14680400d0080c21340014162a0710f101800009004802078105545814100d50858440c4051001a21001c0c8104060084041090750440b00175206a5034002d40d600c0c006402007072000407040d00006031701c4841c0e110a50561215102c1c6440340c0301c03010302c0103041d4055400c4401c110351801820409043e1800b071420440d64454000300c000f0100c83c00c02d81ca4110724940c03904219490a1942428401004071590040b01180102007440d01d507040008aa103411124511a541ca680e035161903240340340c01c54075014117a20055030800400c000c2c11900b0306000b401406000b801c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307048138 1250 307046888 307046891
    0x18080316030504030c0605040f0804080d09050a0f1710140105040c0c051e120c060f0a090203030304020d0f0204050c0a021e0d0c020d12080610050c06010302061806040305010f 77
    0x164514000c2c482e40340925015220591000c80954441016060040c400c40c0c0a11322261100c000441250140c406005940e01400d4002c90390308000b8002e00030fa5010506c03032074080e58104140c0c08031100720300c1a00c84070190018004442658249441310b032001d400721140c604595800c0022007003c2c8141078071001c45080c072401703821140c1140d10340d06800e001340942c0c1010410711002c1c0403142074104104804000da807000d41039100020513a402860500da0030380c00c0001003200c03c6206076512584034a071303000204052110340d004a40c1c0c9000080c4028002c15100881c64213000810b40d41007103103035004000b401145000500710285800c01c1700800098415400f551004030702c0c1c4031580480c41f10800040c084818000d204540300c80c02c8000990f00007040c80c2e1701c0710200d0f1101901140c00c2145480d50100d0341010428050002a10301507802003101c02d2240c142d100101284050460360121440781d1580d5502032203051111078241035580c090800240042000410342000d8803451501c01c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307049388 1250 307048138 307048171
    0x20409050109140109050907080610050f09010614130b070309050102010f0216020f0625050616050316030213090b040501090212010911130314010e030a0c031101180803 74
    0x2c01000c0c1c03110b00c42c02a10306982d000060044040c66405558008008400c8443d020b60b9092802c0c00c1400994a01c071444e002081c091119042c08141d6880d844404d80d0701c44111341c074209000701340d8000f5a45820f828900000c0c2d141e188607445d60307200040c20305451140d40d12485450041c0507440907101d0a03016500b070982050044a892094071031031000394a00200c501038550070443c202600c2038140e035000c14140050801f2080c10005142d070960110b003080110221810524900303134004084044049002042c20740e01540700058a4005003030000e86030541040107000e401901501401d9030b00802c520311700240d40c2529070031034444010217450811480e605e442000c0c06038450080d10284540c0e03413000420503440c0381e84c82003c9803000c451025081c0700d15034800720702c068180c1d80103442c882d070a200324480c60b800070312130001c071018081c00552030712841d8200074000c00d40d03941003d03080c840fa948982100c0740d0207405c4500b0003a18600ca44403001128a00b00509802c283e4000c0d007403c54140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307050638 1250 307049388 307049399
    0x2003090a051b030a0201030e0106030b01030c060806060307050a03230a060906080c10050a0908030703050c151005010c0501061502030a090602070602100b040f0908032215021b030d0204090501 84
    0x16030000030281c05405010489440d800540180023240c0540301a50741c0c810b00000030940714100d15000c0d61090000c0c4d50390901e0880300810603040034160b281f24060030800d0001c0c55800804484400e450303802c010a00051340e01c00111500352480f04044410500410010104071607402007040d62543c4408105454584403455a0f8490400145401c1400d907210100130901031800b8041c03c10507481c046c0030080e107c20000341580c00446084000c5000401c0c040c40010003441191508a40c0010828551520003c40c4000103040e2152905002e0210013240500c502134208402605074810100d046a52483e0b000f5500d510804403200000d015034000304030230f4804100341d030860b4890350040040c00f00b5104010001d1004950a80e40140e031000b110200311040c0c0601d260135401950b6280d00e07490a81c1c07008c814118640602e24621904455000025a202d007805040e08004540141c58802103880481101c2a0342d2061426100c00301d44429010100d070001d2040d21203005090207240d82e13a6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307051888 1250 307050638 307050673
    0xb0702210906030403111903030b04060501112a03060906041208010b09091806150405010f0803030f0604181b0b0a02061303231b030712032003090a05 66
    0x60a540d02c00810000303d000309128aa05103003d00d20042540c1c0c0300302d00000c94003694000b00d0000c80109880c0c0c101c00e14541307840d1040d0720040ac001c1c2021940b0350409550035448003e5110040c484100c000d11030307170712280044a140c000000240842d0070500740355508a0751101c086600300c0d142000c00e41120b481c2da02c02c0c102c99040707131400a01e16042107112400c0000384640181a0055403640302c07141c00200c3c20400c811402030300751058040030405075209000903140141c01c030541c600f652803000c200c16403000040700e0b4010013001c0820096210f1340001005424440400100080350408607800c0c092a80040c600c1465a916818040c90781d030200034020340501400c4e6400340c2c04c00760021b04100d0b000700e10044a00d100b4a400f0300990849500d05450351018034904010f0280420701c0c05100c20180c4108003581c01f103030011410a042d550391684100e10415580041548178520280103820b40c107500e07901c014038030b50600e85900e441420f2542e80d140f07514003030340c4511810580e04a5010322 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307053138 1250 307051888 307051897
    0xe0309150c1c0c0609020f060711010206060312040b090a09150e0a0b090103020d060603080d02222d08010501230906011407080412030e130614040f02070b070221 71
    0xc54071640b00340f8001d901e81030000c1180b01c101380d81020960301f0f00b900c5950317001e00910a05100f40c0c00b42c0b0456116034002490110001d01c3d50380603521080301c0302410840c0100f40c40490b00100c11160340c445c503e101180200500d41c2c043c10116085c01c1c40301c2c9402c1a00d514078003d40e242028a46c4c041e5984d0310140b000d80d10701c3ea05591700402d0180041c805414030403d40c880c05400381c0c0021820665039030b60759090f81c0c008682042c02c90380c0880d091030848841244c00007440081ca42001010307003800b141c081300803911000c1e055646500b903211022004161842e4004110f480000c001540c0d4074600300789000400011741e044081002070030805031411004081c06003506035600d08000c03111b051301030501d80c881c890648a5200500c00050301c0030081c80c0c003040385031082d42c03031040e480d4001040c07240c0c01200d0b00c00700041d641032800c1808900080e503000481c035030f0110780100315500d88181450082c41000c0d0040c0c2080d0a0b00200701741c5640025a0b5084550301044400b85450040240c1c3c025015 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307054388 1250 307053138 307053193
    0x80604030813020927160f050301050c0301050603061203030901020a090e130312060e040f0b160e040b0d2a0603180b0402030f03041508070c02010c060e0309150c 71
    0x48000428130107485c190b08401d9280b29080c90300b0780180884071491a2141074441c02c0d09840d2180014860100c40d02102001041d0a800030700c22400c01004c0001c150105000d014003560010000a20a0b5102259605005501070950b9940c1c24000c03065400b03940524a26004214501c0c80021080c4000c0c0c2041d00c1110100201210341800741c0e030485900025012051042e07407580b00224200d40e4003e141c41c040ea200340c40d42e40841589192015041c03070010624505001515440c95403181c00a00043c6ca0b04000c035400520a5400d500042500c0301c0e45401400101d03c403078442c0c05594503131280c0c20390030b0402c0701c41101f40c0c0d0b5682c504034141e03040030132003001d0300d4030f468007280000c3c07041da6105810910040c1aa180210f002030010f1442c2c105500c00f2840e07421180024240c0c0781c0082d0043e811502c1e03450000b4143d4070b2500040d2016900d600002d18607603541650b0442d40754140181c0380c69540051032145200c50f418154055500014003080007030050309101107180c420221503032460074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307055638 1250 307054388 307054399
    0xf200612061014040e0a050c030906070810030c0b030619083007051b090103081b15010f0e0c03060d0209070504030b0a0507030507020a03021b0310020408060403081302 74
    0x1a00d4030309100300340d03a02e68060401d20442c1d82080d0202000345002d80301505909003081c0c42450300114030400c1c0e52000e0a05018490200103200f841d40002c14001d81c043d20b0b50038800c14648507000e01c0340141405034006090341c8410407001c01e8600300c03d401540180e500310742408030b5800340180d00401c03180754464034a19a020741104a503a0b88603051604140710a80380170781d1b003030110780c4aa40140d03001c034408031a00e80000d14011303a140c2e600025654110f50507070744c400d1558150f80d2140c003a40305004012105240800c3c1d00038400c0c000b080048070180070316030b58a155594512290000080d14050200c0003130303c0d000020702e04181e24040e2849030400802401e40f80c0240e03002d1140e01e1501912980c20444200302c00300108440e400c00c0c0e8020390040c04e00003400c0c0303003d000c002c00719a0060003031310031074000901f04070100741d001a0b6603000080a060304400407410200291034401c20308140840c240c000304002822810129071a8401d07806a1a0001070341d440070046c1050480000000390f002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307056888 1250 307055638 307055641
    0xe06121f091403070501090b0a090b0103030c060207021905040e031201060311040f0b21041703090a0219060809033a05090106080d0c020f0d0201020a0f200612 70
    0x10350079001640c0e0280509440199003100302c10441c00c691111405407074980d100c1c100441002000e40049500c00f642c0d00041003588040d03508c404c130901e01884043d08121601e41c0ca241407041c681d049401d41940103281c0742c14900c50000c80504175125200b041e100c0d41c07420901d00c0700d0f010040122014251103d880580303581c01c0403815001804008a81da0100710705000c08100001041c1204000d4400900c8003625100f00c0392050512a098440c403200b000885410f010024803003000c25001c0c41d521480c007a8983d078480c42c01030325000a03800c002e136010b0100e01c25014155103141654050b5619640c2d0840700e0b9641f0144503580f44145011407514280104000600e8000c40081001141c0c240803c040d6210410040707400340d542c02d81d0600c0150f596100c4c100400081000007465100041c1440d02003006e154002685080d81055054000c0c2c02003604a41160f1080c40318103403031544114880104030715410050b078184004181c0d0748000202640380d014614003c0140c810700312151840c3c4030360703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307058138 1250 307056888 307056943
    0x90501061a040e010521031201031101050a0c0f17120412030603240b0a03050c03010f06051c02180711070506030415150305030f0705120c0c010c030e0a0e0612 70
    0x3101b800c1d214031403d003003d001400c1c1965130140000c02c1c8122030341011f11a03650441c101405500811039206040c880100844c0c25a41d81040d10740c14100d400280882100c405800d10b5242620354212854110400140c80c2400c0c07850105554019805044036142000b2140c80036822603417039000c0980b100359514840c03080c47d0320202070340c44920120745000c2060442d01d00440d5042d041d80c0c0003103a064100c0c50b040d10840c18240305401091811080a20015107050041000c0b0300d00f401c4501e04a000b28512039040d51a00010b0001c14018410541182e1800c1000101455070890081941d409130200004880c43c041041e240501e030800044a0181c0300c04c1882c0d80201041012901a01311050b4000003258051003e0040005150b01c825554440e514080342400c1c4c0000700615240d0b03081c40145000280020a449803417001e0a000300205500e013020741e440d00d108020f5035030064100402061a1054502d418003682d8182c038039900c80c081d4440081c0d1602c54142c2401032031501000e80445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307059388 1250 307058138 307058149
    0xe030106050612040804030501050106080604050f060906130b092d0405030a0e0f0d031e1407060203070903060906060317031e0705040506040e0f090312040f15090501061a040e0105 79
    0x200981700c1c5200526003a900e556403425944241d00003004950040100411401c0c6030054a910140d280300e19215840d05e040010582d10014201c64000c2c04422035524900d021680301103202c0100134245100d501e499032203851580320640c1d46290030754035028100030000c09000d460b401240c0c40b0b0090f5081a880e1441102c00c2030115564903405105091500c4603511201030090b1030310300076504c0c41031a141052030200d551228500c410100107039192117040d00c40a11003078801d0198032800160b902d440c2c00d14100d071450900d0b0401381455113400a44420071882d584104100da01c5903800e0111030040464200980c0001c036241d07102d242d0b01c0c8032114004008130710020391002650400d142010b8481000c1402600190845c1000310401c000b40541c405640840030340c4940310800441c5050565144550880005000100301d891003000410800860852550061001120411141d0081d090013801f8200f00d10900c040c400c1c440c0007807420f0202a0301103a003030f110f040480340030b01c2e4071b0001400b4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307060638 1250 307059388 307059391
    0x609060302070204020918070f02070e01090509012702010315060503040b04140a230303070c03050f040317090907090b090f0d060524061201062007060903030e030106050612 76
    0x1303902603400c0145124a075586400001007107a41181031003030b85461b10016040c075104640134002e550183e0f80c200009804e96a1072819540d0620340881d59441308050b01d805490103a8a600c06500c6105d010003805499040c1d0507031b014000d0741e06008901400041c0c083c1503410780a884d0014004000240104404d81c00c0980c025124040c00046010b903c2400e6040c43c4038140c0898812410708450205151071140c040700c00d207040c401951450405044c041d00c15903081c5402010300130042070125841580c4000d80d002103400c02071401550940d4084040c0640c40491440c1c0301d0b2400c4c2d4046082d00780309035501e03c151036000c13400c1441c0c040d019040001900ca006480b607400030745c5058034000603116028460003248010405502c9249410302125402154000640034160070310285d8001003410007010704558bc1c905000d0100d000c0704c0b900c24036034102e44a00c070060b84500000050850341c01003142d01103d009581b4070707401c0c1a19004240c20b0710214032880d41e1059003448913042e40310f13480203ca07 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307061888 1250 307060638 307060643
    0x62d060f0e0f030703201503151011030a030606020f0705030d1202070215041701020906120403180305033a0b0118060309030e0105090d170c0615030f0601060906030207 74
    0x840104e42da9540341c00300c004081d8a800f0800c07907081409141d50804110260200c466030080508501c1d10103004c81c7c6056000c1c40103841401c2115100180700d025030144060b04480c03c003502c1e0746007940070029015110520940e0018412204c0c180f03207a0030080748040680398000c0142040782d1080703404980f0741074850700f900c0101d80c1c204049030050752061800ba070542c90044959454520705010814400d24621440d01203034010400700c00c00d039942c401110108280b0785880700707036078941d805c0803110301c0c41460040f10540038001001c03041c00000030141071a403005410448a00500a1410414840c42d0084a40091110b09142180182c07078100b0380941e0018544600990308400006060b08081d91011010030b0356140202d06150b07000040e03000406007030901130300e480400e80214001c0c0100c0040600030045100c6681d0081d8007960031905080f00120455483d0b04080118000118100300741c41c0c401c0c451652810410100810038134121261911264070151400d501a0041d50008008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307063138 1250 307061888 307061893
    0x200c01080601080703112a060112020904060e060a09051902030312070e0d03030b01200a110f0a030b1e250309020907020c04060b0f0d0906062d060f0e0f03 68
    0x54507019250b4001e0140c41c000405444c5110501a21420309046500700300e0447d900902e00521059046100c2d0002d12503055070002d907244d07035509041c0000c01d44402503000d46e00a05d8184405031100fa04070314a00c07030155050720f402c4200c440c07102603105100300c3c0003900768000b8092071280e20800a05507038040500d0400d181e030742300301800288480010f80811804650b032814414100d5910007000ca441c1c958594400c05034403030550107107544100c1c86a00070800d005000e40c10a5580742c0c026181c0c428030010740242c000d240c4038034299003080c5046a0091001c40c117421103103507018410001c140213080c20781d0b02c06881000e40c03100e6400c4003079544024040c96190304290005840e0f2032002c0d4070034183c0303502804101d0401d008000070b40352140e10040310180c0903c20216111740407002c03604244248040090401c10300e240c088080d000507405503503007071450305110081c02d4100c045040701c8041580ba2000203511104252004d18a101100e40000c500160b41525410b2440b5650180c9100404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307064388 1250 307063138 307063151
    0x150901061517010506031003140709020412021509100804080c060a140901060b27030a0501060509070201140c031e0a0605011b0b06190f06200c01080601080703 70
    0x5106500d035650710240701c0003480841d0104065824810001d000d4a0b0803240c00b4514280302d04012070000043c0030280400d000c24000340f0100303c08000c2c1c0d10041c5284031040d500d496036150507001c1a1242042a030040324a04403c4100025100840340144c50013003031407002c10b030b500108a03000400204201d8070103108001c1405e002004101b000e22407440340a0100c1c56000c00d074003035160108090120300c000e070f0402c1e0040c0142c4200205852507112003a4144810b0782c40b00388041484043e40c24040e4150185000000a014040d0440d070103130b9206079103550b81526140da04908030b601d003100701201900000c0104030480f048000540e0005c030004150a00000d202c00c1c100f4001c03e051364607001446e40c441007000b00c7d58000b048245524030380881c01d1100c0d290343d00c86111b1584000c04d80e5110310590704940c20301e000243c0450001c2c06040001900c0c8036200c8a015010180c62054a0424072440d5440c2c9420100003c8058035000e06030343d080d880c1c1d00e4050041d41c1e1604081c02c050103040d120b81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307065638 1250 307064388 307064399
    0x40c0e1b0c07050103060b030402090a0b040227101e2303160809030c061605040e0f0f060f1c060f0905030706150602060c09060403240e010b010215090106 68
    0x340a004076065400207000c5061400d00054111243e940c0020b00c000c50a10411000da680d58006560102260b04007041c83c80b03a000c0010024466190684d0a42d650300b09014603003c2c4030741d004141c19900341d07446006241000d10a444ca44440802c40079070100301c65080b400a0310404d20a4002000d40800740940c05d00e101d07100c201034104491005c249000f0350200780d01700f0b50000c01340d508600054007644c5065202000c1b0390b101c5030010040e42400788142043c1018130300c0b94041b60002d000300701d00240ca03410100781e080d11221041d1105a0b00240e4500400d0480c502040d05142c0942d006003d06007a060400c2600ca4441500c08107964090361006503100c607190350300850480074032030400345980303c0c2c0500c1d00b00d0448044054a003440030950005010880c0c001a00603001502d900510b40c4403882280041ca00f403145130402448044400c5400c1e0420310301c80ca541d0800e41c07038813405000d00914810520308030b82c24050002d005a10612103040f0070040000010b07005806100041581c1d81c462 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307066888 1250 307065638 307065691
    0x809040216060c0513060e192301180303030b04090c0902071b0305070501080a061503020d360501060b0f03090601060807050d050c0c120c01060e040c0e 67
    0x1085a101616800e02041c20882e1078819525103003003a050050802c440044000100c4a4600582e4140b002400885105688010907003402074292180c3c1d005160b2245000711401ca0b1100b0b41710110341e4007400c1d07803542c0e6000d48402401c800450343d012064a180d52800c4000c1c04402c204107411907514071a41000c81d649414400142c15404409640d903201840c040b610415003d08021000012210510004001007030f0321044840901c1d098a154885541c844010251a40b001d50801900140707559116010740180007000141001004100010180f510414a0055a10240d0350340544100804070a100000b030031940110000241151108040b5031760b030f403207445004604000441000460750007000700a0141009c0d14080e01e541c201004050094010440208046070710307080020b086468a80c01e442e02044024202c40c40345d65030f1301c2c1681c11030f03129070001d013407a5007810f001150710307090420041d014551110245032110300c2c20b001200d10301e5000d4003000351070103201055800c0201c1c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307068138 1250 307066888 307066897
    0x10804060c0309150b031b030c0402031e01120b0a0c02150717010e0a0b06040f05151204030c06050a0216020f0607080a0305060f0108010b1605072c10030f080708090402 74
    0x8000009848043d201c2098a01f0003020b00d0600058507542c5c202801d40c074081103100d03e6031016203025071681c40396420201406d03140d1a20301c240104500000800c50041c5440c0000d10f800b482d01d0750107079110880914107035841041c1c044090313802220b4901c00c2410204680b40d0000741498000c0b42e082c4e40000c0700440240c02c0e4050f020740c6140741d00b80102e17000c0c1440313212003c1c08112084d5150a01e4541442c2c12031040d407003214451000da40d1400301000000007185d80080c146070384074506203404d24000e00400c28110b02a41c00c10714040009540c80024800c49240002807055880c50420300d90030400c08200d400c02c0c803500114203220302d100141c4002c01400740b0041d903440105081c82c20b0000c1c0410b200c00003000c203040000d14001002140642d000b20b0300da90061402c1041e0b043e1f40703810b0641ca05003042c1c1c000d220b160784140d50041d040040c820107043c481905960301c215901c0c0e8112500d410311090201900142e0885c0341c0c4000100b1810007000700911542c815424181c0d0f400c0018201d810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307069388 1250 307068138 307068173
    0x1011010204030b0114040615080705070b040f0317070c080f0408060f0103030f0206070806040902040e0d020a03030e0106030302071205100911030c0a0308030c0903010e011a01110309010804060c0309 87
    0xb00980144030305c0080542c0f1000185007910f0402030140f034000b401c02c44075803034030b0400b080c0142040426082ca105070221507481e41c009640d02035500b040d02d000540c2504108055000481041d1108004000203107194000c110b2035031504202c103480c1c0c664240c503030f10501514a0b07c0c81c0c10400003803211800d2010500c0b032280c250031100a985107040180842d1100404801150405820000c4e2983c000d100c0c1c82d081801610002040c3c000c62000c140100f84440051420740310302c0070150b144690014600310081d100f541c051100001644015013613803a00e01000740503030041002408505070b81e0781d00c226414052030403100070201e00c40c2c0c068103c8560361b00030b0ba145480c0e8510305a0b1401d00300b082118150042d0380ba9000d50b40385495414032408043d0a80507031007000079213440c043e9001d401000f84130500000801010000500b495090b008a0004c0c1d030109461640e8092030752000700648500c50b20684409805503110f941c0c0d14000e10348081e2543c18965224494004100c9032001e40c0c48006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307070638 1250 307069388 307069403
    0x7260607081605040305030a1103070b01090c090b090603070807170108030702010915020c01050c0f01050a091211060c09010c0b04050708011503020102032d2214010e101101020403 79
    0xd00035001c1c040d0b80030598103041403000c100002c00010f0701c00000c85407603074481c0c540542008100101d540c00d41c41020406069450300c00e001140049607a03203c41e03e4859907450b44080250741c0c0102d00c40c20700070340c010141e0007102032001580440c05012160791000c0301e841c003040d0000d071349034051003030680030b811041155001050606c215604080c1e081c008d0000840c6141105a540f00b0007580c071481007181c07070304110700030034110706c10780c07003000516194250000240414542050b4580c0200483e40b01618109045144a500c10703000d01c080c610b950031a1805407225541e080c448044603804440024108140804200d01091808140d1401548140f002d000d0581c5400585802d488550b120328000940c03000007040143e0f000012520000c2e03103010081510180742d1141125a080d0401690780104d00080c220f00c1c090000703441010540004210400c2e154039401e500001450418548ec04140802503c40040c82c1441c000704040c10140341041007082010001826a04070b64011501072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307071888 1250 307070638 307070641
    0xc241d0307060b0603090613030201021c0906060e0408040303030513020d0602030f0604060503101508030c0f151902160204020a020102090f090c0406080723180406080726060708 78
    0x70042c0d02451100c0102200d4250071410910300403074803200054852844024298001400c02d070003074041e02c40c84003003c00d000298101c2c1e282c00c280602411001113806d1440c107400400c03400360500005005036080354600341082d0441c0c2d0158000c01002c0c01520010b146803803100016682e064142d005c2901c1810056140e040c11895280242000b43c2401e01c1107041200c10700241d10001824220607560348808545040702014107450f00410b6080100b40d4000014480080880020005141d0005a00305c0300c25898050700f4503d12401660b000c4840700c000d055004075004183c01400004607100100c007074403030282d40014200c1c0d014008c924050f035000701c1d240606143c403c420112910013030319041401d1900420803082071080c1c0c0180c10501259a010803d45807003000c5030403480b41c6400410300300a92503c85490240c21001503581012811544c10281d800c0c20301a5008440b800c00041000f80c3c140710790b54052001544c80c030484e11030100718103072026008120841c012030440c2c4174107005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307073138 1250 307071888 307071893
    0x40f020a0902271e040b1c12080f06060a05090301051f09050402030a06020322081c0207020a060f0e15071103061618090c02010b0a060c241d0307 64
    0x204001d42440314010f40c8000103120307441e26550703880d2046084120790348004100c1d000008008040302080544c10481000d10310400e00501c000c5810220300610260041416190303040b10103680c112004120038a8260206150b41007200c040c003500c0065003012400c0c4240d42d03000c6401c5130000c941c3e504015000720304034201c0c1440c2e040c2c9407016115000c404d00091510340c0109a41381c48400000340881d80c0000026285003419a150405000b100444c40040b5510b080c0074180340c00c007548076401d07034806001121912056108a968150380a00301444842c0741540a841c00841400d0354414401046001206a1380c0c04034918000605861200c3e2101c82c00d040c010110050441c13040d0096020105000c1c103c0c07501064168489250318011030f0400e0b14001c05444180c2c01d622880e03d00d8140302151801035019080000300900030761380d40c408182d031079004480e415004c9401420f00000711407901c8030135940c0810140d1000000d080410050300340c400b0172482d5442040710101542000c82d11508 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307074388 1250 307073138 307073167
    0xc0f1909060219330f290d050c040c02030d0c0c0308011a0f0703170609060a0b130b0705030d060902031e0712061d1608010608040f020a0902 62
    0x140c4814801407810040010f150b642e684032200d03000e8a01c5003052200c4101d0140d0301c004005460442d0280990040d5035061003020f010041d5154107580d090110a0500940c4128003003a11640c02007000c0c210041034040c0200304500400070b44081c091811011f4880e240e80c0188246c9001e1503008543c1ca810b50b0100c90304641030f41d05481e040000d00b07035507072021030b502c0000d16054521006800e40c0403400440d0b0501288110316448503500c4001c196542417607088000341070b20500c1551003603140d5444000300441a81d00b00d42099000c0c050710030512068200401130440342c04c615694000749521600e00c3c501c29040702c202102c3d0b0f603100194075180050f0754010b410080207444400e50850500f01c682040c1c009400030402e049150310800900c250348100d165003005040d4482c10090240c440c2c0c03540552030044203084500785807910124100b004011000101c0000694902207941d003800380407034040c8000360080e40c00b0350010442c1005a2b4a0101000050030380110040c0d9900900d0403802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307075638 1250 307074388 307074407
    0x61501030f02040b0304290c0c0f0106051507020103060308040f290f0c0a0b010905060a0e0c09101e02031206102109051606110601031a0c0f19 63
    0x186240c01840304204d4143c1c0c09040e07942299112112503a482501c6040580700b0303030390650b80400c0e002074000b40020300c0300030001001c040c512581655035603890103414500340e40c400c0c410190000c2100f0080c1d120011a0005411503910500d404035000d50f598640d0038960f0425040300d2040d5030000c0c0300700f0202031410110312001000910038035a00721988045030050060045201606100041c8000c8010301440040490b50b8054501c0b41c1550311070081c5801804201c0b8264044c007040700000c24910700401d40c40b4803800d00401c01a142064001c18040101c22800703031803043c0102d200f100074580540a10301a49081c00b076000b0b54a03200e440c101c14410171009080103002d4424005141d0380c3c00d504c008100e2401e141c0e00010245200888810780c02403107601c1c405007050040c01a2003400000100300d0000303c2d00d090350713248407514544d80e1300c0d501c2d00401e04c4000c2c403c0501284810003083d111086540c420081a0303090f040ca80350a4070141194401030f54450010313502c10400c90410303000050076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307076888 1250 307075638 307075661
    0x1230c0f15040b0f04030e03030d0b100e0f100507150902010212070210080709090618061a1207030902040515010801080d020304090e010608070b0406030e06070c030f1106150103 78
    0x1001c981400d072030b1032000c0d5a0103071140c0000302e0740b40000b40c2418081c0c0c0c42105500c0c0003408495440c4040305a8800400b01c020409105444024082d40190322940b174008004100605c0004280803807002c00290f200380c0d400700c10a0207002c1c0b28400110704104864080042000c3c0041201d498610009003040d1410000c0d80d103c0c8403d11220700940c0f03544410714010206070400003510707100c000d03007521884d0f1554082d0707409500b80600451112401044000e4070420f4010034408540c49080046500c00c981400c807040b4039050211035100d400d00505a13821610034100003c1303052541d000728040c0e900803107455607030050720002d56111b03503409a50f030707070040040f28081c00041c0c84180c40251280300341e104095030356859040d2005150b400394040d4001309118021510480d81d1807080e8a00d6230818032418000c03d1601407005030811000c0f038034a00c69036099941ca0240c41403540c00359504880d60320080108599000fa00d00072650402a4501846c50b1000b60003402c00800b00040640d40e00c000750 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307078138 1250 307076888 307076923
    0xe1501031703010605030f040606170703051204120b040f0b0c070b06011103221805010503070801020412020907030f0504061d0a170c03070501110301140f0f01230c0f 73
    0x401c841380d0700000751707900511440849000c507102c40c2000005808107411a0391620407a0700c164100384400034000301140e01c030b00b06845861840c5c07025a40940120320540005008400c0d418000a8070500c5807a0311510070040b2036911040e0fa10707458880c007030898824411100000314030080c028414141e59103d8000d10300290344500052802e6200d000d922840e500b0056501e180841000ea000d812201801420824010301c840b011070000140c08203126090203402000008224010103000f00c4080d03580203102180a1212a8240201110000c0c800001c140d60b410a01c080c00d542801607a000354050180491890f5400c80745403120000d00328400c0c901e43c40010001d000a0700e007030403280d4110204080704d031500c0155408074198400c82500404a501e024071b4403440f6506e04000d103058804e480020000d64081d442440344850055440d00d52211114a0402d55580301d0201c801e0b0381800c0c0510b0000042e03007500d2204664110400310402c68004540c0e03010481803c02c03220007403403030203001e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307079388 1250 307078138 307078141
    0x5070b0603162105030c03040f050102151b2502010f26060303090907080108060609190e03040f090603110301020702130e15090609060106020f07090f0e1501031703 72
    0x26203200480c0e0700c03c20022003111550341c0142d044503428100701c903401c034044d01e94600b02c0c010000d48035480ba004610302c03842d1004001c5070700d500c00142001e0f4030711800c45070348054075030300301440e040840803003c000b50990402c0380b0407004451206503412400d0031415007c0d60b03607040c4000342034000c041e000d49041020502e038080c2c4910f2029041c100c0d0f0f00c030300d5580100c140c03241404a400c51042032070064000d040c83c0103111006520583c4241207622400a03103911351650420484c0d801001e65023204940c000098103840d2000980c0002030040a03203040fa450a940c40480c500004019030041d403c1c2d40d96240c0c104148001d0340c5074800640812002186003100b580e0010300244007402120b064159662602c44007440e042000d400c040fa030f004c07a000e445280c03114480356103202c100c0c9c1c00079281c003a010001610a00015400000500e40e5000d82042800c201d0701038020090b02d81d41151454403101036600414044c0003c00c0c1000000340120308960443c01d082d80600001c40803150030354001c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307080638 1250 307079388 307079413
    0x2010203160f17041e05030c060c07020901270f0212060a0321090519150e03062811040f0f05061c090c090b0a050d0206030402190b0a05070b0603 64
    0x30406000c400d0650f12102c0952034604100c090000c030080d0f140d000020143c40310081c0140000905840010042141d095039141101507a05000380c40d8001e412408200061240b030640c49c00513250081c4001c014410303a00d981892a05485480071035401d003a90004030008042140341d00c1541c840b8080d2030551b040c0c0d1450340c030208880740400440300c440c0026442020018840c04091008150003480000515440071030003d003402c1c5489456409010b00d11841071749030103003044054500303006019090b00d588003644001e010101d50003a0716014407800e0f80c8034660300d243c441c007040c079a040d01c226a10f803810100c260800000e01e80004148018030142080541d4038017080f91038260040c4100c1c801c581142a5050240104d4140105a403683d070b44c2c0442e0b480702c0f0b980150306000701207501c078080d00c1e5100c003813103151038008401039000102000080c0242c00c00b409400340c036868000001e114542c5c2d56a982c03180d6042a0a050000b420009406041c01950784005401403000c50240c0340d07c0c4002c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307081888 1250 307080638 307080647
    0x60424210f0605180d05181903020f010c0c030501050f06091006030b0d0203010903080a050c0702010212070c0f0b040f15020303071206080a0f0209130812101502010203160f 76
    0x350300c0185850303200c03000142c20304c100180d0001c0e0301303049508540041c4004c800c054016004040036880703103036411040c08514a0454030f40d062030081c4110000840d411074003880070780b9442c0b4007000d05000104e020400054249609040210b004400018940c00d19401104824502800d5503100320780d01e0052001010082c450340003220300e141400900c07114400040391021104400103036240d480d0916410901d500300d101d82c1e200d00c9801c1d40400207940d4100d05910035024015010b801030717100c1d01040d8003100100004020882c09440348000d03d950300e06000c0340d940c0c3c0c9504180c0c5000c202181c100700c00200440301c40041c09540c900c40040011028ac02962030100814420030000c480006031031400860f40304201600b40841950b031854183d04003c9848071500d80101d0041c0d03540c030006038001d42c19403035141009520507000741c03520403013100d0b6003000d502c06011080b90609803000045c1030303801c0400c45d40a5003265000540c8916290800c0c032507191000e88182c0c24080c142c1c80d0045102c1d40b0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307083138 1250 307081888 307081913
    0x40902180904020630071101060602070602070501080402310f2d15062001020c330106030f0e0c010f030f11070f050d0203090a09020306042421 63
    0x405c55402030300100100c00c04800f4030540200054a0152800c1c000107540c00004602e140074144003d20500ea5290412030f41da003880c1c40b4150050300049414040d942c03007903600e03940050008100002e040c2d81c1c809204514400c000108842a042c10000040e1192602540081070305108040120742c00c040451000c0074050300100744040810103001c074a00b22103500082c48903a40613503000d91b06407600700240a41b103070400c000d15405944807603400405414004c541c11040320b200131344260084140e06414070410034104100301550031400c0c1048030041e00160b40240003a550100e0b95000342601201210f0324860a812a43c00c40e404080780d50760014600e0b00c01d12080d28002940404111954004012290310303501516400515081800f500d01072542c0c0e1140200c2c162404c80b00ca003d41640d482c0b0484000301d8101c5d4614030b04000d44a4158099a4406405040410070ad040100485c003c02842504114100b0222405100509c48090034a14808484070b85054144031916101c07a01c41c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307084388 1250 307083138 307083157
    0x803070b1e0703090302010f1d070920071703090105060901090c09061d030703080a03110c0a060911100804110103020403021c0309031403030415050c070b04020a0b0409021809040206 80
    0x21100310030b13820103200f517110720243c400001c030401030380107a0303402c10310500c035403440400e007601c904c02020030023060b5440f403801440c0c11141e440b8105c640a501e14549a04101d4007910340b05803085081045e10410002544902106000052945000d1007006013401c8103812203110720b460300001d41003081d001600710050710007604216088242c5403c1140500401550303050301802040c00000406c032003000506008001c945043c000c1e032451400f81c00300e070701440d18403841035404003030b4220209a00ea80004000744c06000c0076503120400001003180141107120240003c0e04000400041c000002280381100f1001d00e01546414615000100e4102a600c443c80f07200d50401a501d003090b020b0130104004540c0103980ca00458440c40c144c03501e0b0307081102c0607500c208640c268841924140d200b0b00b841000c0e0035404605003071440d102c0300b03a400802082280c0040c0144c40114042012a025100034100d90201613a40d017080081c036030144d1503111080703020301c0101003404010303510700b400d80d024100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307085638 1250 307084388 307084391
    0x10b07051b040209060f18010806010c03080712050c03071101180b1305011407021006060f050703021e0309040b0312092b06020d0e0c03031801180803070b1e0703 71
    0x3200e100140080c807070107581e568865000160186001c43d0300740944050b024404007c49440708043c01920100030456181d0300050704029903000290140301101d40003c1d0750324201600d46400c2c0210400c40d84103a134a09000c2d24084100b00006502c80c48030742180200702c0080c0403154403e654513070300d9018408001c0c070000706140040c0c0f40040c4d41c90ba94030601d800c40c00911213038001c02d0700c41500c404d06a07203a03801400350050300c034448149400343e0b008980c82c595a40802801c01802115283c002e054100d0440c000c81d82d0842618204070820034092003940041c1d65983c18400405c002c681207110320038065048101c08001c082c0403003056801548041d603054150581c03080c91002e01ca040300c11000c010448502181c000e2100f25030240c24135410003802088154210b5030070b03695800d074910070241c0c50360080004035180344881803107403014901030508030314100c101a0071803985995604240b00035400442c0c400180060302201d56005040d02c640d010b030710307100c01190902c5010018461801d05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307086888 1250 307085638 307085683
    0x612010e060c160510050121240b0a060801060201140c0702152b05090604020333180d08090a030302070201090b0705010c0f0f02070905060a0815010905010b0705 71
    0x490782840f841203440c1c0c0304058441c0b6401025210000b001d0078024240f24040140c0d58280c0035031900b5856000d180c2081024868003540240c800610540b54818900251104c000c000c1645404141c003028090b56100c01403150b040010081c03c40e10020801c0c4000c507040002d1003460210348040b40c1040da0142d50400c035400e91a00c8041181c0b254000c0050700072010101395615080e0b612410218140c0e0510521058441e500c000756039400540c1e0296040c4c2044c804681d074101c8040510315901c445a10400910340c003683d00c02007441c1c0c01c8580c80852110810380d011500b105020130101c071009802c08807828206120300d581d54103030a0000600380342e4006000c205580c01303031302c000008003003580342e00740c1d2040d140c0b0300103003c1d021407111040400c4003140000101c500442641002e00340e1503008110013407408580801504020700056044041c0b80320208025005001c4c101c96680c140700d800c00254501403400d800c0741c0c4140d0000611140601140d4002600440cbd804030134401c071401c00f00300 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307088138 1250 307086888 307086907
    0x12020f0102031201060804050d030b090a0902030f07090902040506011803060f02190f0306060503060f2103031303140f040e280605030106090624260612010e060c 71
    0x350710481103d2008a10240f0000074641d5100c51390500c214030480c2902c20b1403074034440540aa03a8401202c5920015420008050305020b030301c400303511800101103071303206002503071101c0c104140c0d900700d20394164603500c0a4066003054080c03030b60401030a01e4420504184491079806c10700d000d000003054551500030328803e1104a8060740c003170485645050507040003400b0b015014100c04440c91000c00c2c144040002c15600410640f845000d010700001001311440c010000c040c04d20340400c6200020200c02003442400c100051445440420343c000c003070340d50710305000d448100c801250161500c81004140480c100c0e010645044070b03400e010841d055126501441102c807096140040080c45a202006218a507500510b04071841a0001c2003c0e60300c4e03501020a1b9042800345910a5201410740003202e00c0030100300700d001d1040c0c07400100306c460402019000c2241c41080320340014240c41405040d20f00002200c21001c5400002c00584045c142c0f002d895800c0103000c204401e1010507038442 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307089388 1250 307088138 307088143
    0xd0c0e0f03060f0c0c06071707090602070b0a110105070e1903031b0203011404030801140f0a030206030601140c070302040e0f0c1507050a050601061404062304050909010504030e0a12020f0102 84
    0x8440a5150694407980b62580c00200b98120010800ca0231840050201e6000742c016070a40b0151850765001e0510f0501302100f10b03406900103101c1c01c04021140c19100303001d00e402c1c80f44a003e841c1940d250711a4080d00d0382005019424803036203d102c043c00340d904200098010900119402c805203171848441058000240148010764a40c0c5442030910100001c25602c2012181610074400c00082c004042c2000e10000320000741c81c0340d41141034481c050001d803030124041c65021105250007800b48210040ca043c880d00880c840c81c2141d44406030034421860107015040e4070300104070041c04c0d8a1410040d031560f81400b01001c0707009001c00a0703c0315121007550102c441060708402243e201c21414030b05030355a10b209204540016020019460705246110704079400c0345d44aa982030b00c242e40884038000740721304145444200381003c0100154644580000c241f05003142000010310340342600780036061112000303442d4403070144107c060003400b41c0090160341c8c482d016200c13500689124070040c0d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307090638 1250 307089388 307089397
    0x807051c0908070b0402011803020603040b0c0405030a052803080a0b03010204150815010806030d0f030b040c0c050d052106030a0c03420b0f060d0c0e0f03060f0c 71
    0x402802c1c00060410500c0755081c0b0960103a4801e0740c2e9005101901e40c149170a07001d041c08020b42c002d808001040100b14406c00e4290031135200b084070382c682680c0350000380c07070b00114040844031038218854142c10124030000f80c48400c0500c03c120309907a03400350b40c000c8c00e0b50401410740ba40c0d0795442804d500117072001d6044d94054000900341c04240600c5603809046944110340d0102c80c8218580303001e12a520039510107024800c0900204000d552882d820384841611210308400c055488000071400e80d02c90090b4402e113901500d5010380404941000b600303050802c2c3c030402c184407080049442e441902000e0100110307480400d4801910303a5400207060082143e800742901d0440040402403201500901c08880c110180e0020490101d505003240101741008884507220fa4040381a111003403070f04407021b1110010641540c443c08540050030a40180104e0810300da07039031603c020003a07006490a0030740c0b20b0850f2920031040b4204002a5030f008024012441c81c0d8140002c150549090010344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307091888 1250 307090638 307090643
    0x3021006050f22060b04080c03071511011401090207030f0906050a180315050105310504111908011a1c21020303040b06091e06130e0604060b010807051c09 68
    0x1c0c003030b565545090303005c0c98001e80100c12041c00340101c00b944600d0005240011a00710b0071401f16407a405c13401c00d86603407001c3e030a0041d042d500c2d500c0032071505884070811130181c0154140140c85450500b4020701508203121420107010158a00f03010068114060320001c04451400303040380d1144004052042c05258401800307000c04140200a20315541c03c090b050b41c00035280240e2246c0750f44e140c41d41c41100c00550144030400100b10103900c440fa50010381d449409500c400d0074020b45840454440c82c1385030300091041205420a00042c0401c0c041d900d0741c14480c1c10740c0d0701011600c100080c12460280c60503003d241c500018803080010f2074044848810705e162404454900b0180040c3d201e03072041342c080341c41c0c1542c08002062450b11030101c41c095095520030300c803102401c54a135021108040d0545500045030958405015800c1c080d0b8450800d600c0c015020909291070700906403445910f00078140414070040002d02030340b01007500c150b4540060a030580f8036084803c08024120004003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307093138 1250 307091888 307091891
    0x30403060606110604150207140604030906030507020d1403060111070605070b071d121002070501140603010915020a0c02100509190f060806030f01060e0403021006050f22 75
    0x810301060740d00c14001c41c1d48035100c420200341030072801d688640b411200140402c0e4901000c2c030a102031580607000c11440380c2070a4190020032010b0602d00a000c4a08800041704580e00340240e03585400303801c0c0c00200c00e000a14994031098005441c1000030b40070111150404800200c03942c0c42003c1c60b804113010f10050700c002c1a103480000741907030320101e01604d5162844001c100c016200700c40171a0080e40703203490600c60071456020404036420020320a07100f0f1250809200e140c0c9003902c001c082c154869000001c542603071058071071000030000c140c5446645841d1400c1e0100343d41514003200301d0011800140e40d89200d034420361b8802e60504019422014043c2c0c01189590088001c100c519000c442c4608210307060848126000aa4010800407104402c000c11919001741406500000002c080e601e084428a09590840f410755000c2021411860140014550184240080c4505d0f005c03003400100e051101180c4000320240a460040361036130201510704d4079001c1c00d541d210040600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307094388 1250 307093138 307093147
    0xd0b06040b0307020c030703030e221104050117091905150a0c120905030d021308160314012c01021b010c020f010219030506030307050304090c08060301230c040803 72
    0x1074112064004841080c0036201e00f6031414079500d0002954022070f40d156451b2034118408009011000145c098410004920b010f080c05000310a800f5103949902e55403406600c540c50540010032082000200b0b250148040080c4449104080380c019400c0d400e076500d0100100301031602914040364080025a20b800034070600c05440b4040c0c1101011400f20741c2c0d081494900b003a4181c013250000c0d07000406541c820030442c10010740700d4000d0000004e44800451996035a080894105881380318100c010b2020340200340200b00e800300300c43c1a80c040d064020001400250841100e607402c0c02101085401d08100074440080250102e41c2104449002110112003c644031b82c0079001504418015016041842002d00d105109489200c2d1108045801c1c0c82d00c40c0109038000c02000e85001c2d0140410440d02c030110348108000c00003400c0401000415500c48000107100000207003180340b00c2d9050140081c241c0160003004800b00c44221019982034a900c0310302010b500c519071221046010115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307095638 1250 307094388 307094399
    0xf0d0b010c0f0c0314030a09170102071b080712050703060f0905160f050d03050d0e0109020612010504050c04031109150d030216080105060d080a090f121202030319020d0b0604 77
    0x8048400c40344142415407005c00d620944c50f4aa010f42101000003650b00c1c03208024048086424032040714540000501d800c2d1b0548409000e0001c440100c0e0784d007500e02a040088000810041008116031a1207410001c01c1d40c1d41c0d6500d40e41d45202c090905919185940281800c2d613111f6008540d006e800c0740c0454240b81070b92090002544615888003605640002d05820700d0401008010740c55030343d6500e00090010f40800900c41700e05018100c3d961400481c0050319454014040002c084d2103880ea1980345c00100000d0b41c0c4010880c12941c50b00b8482003000403d4160042d14240b021141520f0319555020612440c200b81c4c2c0d4040d81c0141289000800c0c1034010844c43c1c0d41401c2ca020110760f142e1100711150a0711426183d141e0060071446040b80803440c02405030601d440e452a0244085684201003448041c0e1a0400c2e001c0c029003007114403c01901d01d1a404450b0075900103541075150034500320303101040c3c010318040c0c690f80000311143c80740c449a01081c06c041005000c0c13030303d90341c6a0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307096888 1250 307095638 307095653
    0x203042103020c0603070c0b2e0e01120b010b0319050a0f0b0604030302070e0405010618020901020c01080708151909090201090e13032010020d110f0d0b010c0f 70
    0x14803058000d40a04100b030314043c10040f048034800e4145440b042e500c000b181d914507902c1c0400405641705401504181441d5041440040c0044800200346035801810701b0000380184006a03c880f440152040382c01e80000c1008008a0441c1c2d0109401601e0703a8810300002500030a030147c2100c010310b04810008800140d5006160a81046070100300124185040c400c07144194080500036900100d0100f095105432140d031540103209200104026545007500c0550324100da20747e1009a802068014007540d0400c440248000c0074a0300c1ca08071300701803d001d003584402804800c080d07055020701903240d480e40c00000c000c4c8104216070384085990303603400354000c03c22100224009084a01c0c0010714505c090341882c0a41100035859502842c00d0390300381c8852100071602c4030651584d800c141d0317107c80b060080d00c003198401600565900007042d0360a0846808a03907140d4280014044241d1480d042c0054400e00080d200b0300140300036000c0d0040c0c8000c41d000d00001c1030840b030b0903281030070400c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307098138 1250 307096888 307096949
    0x14090102011b1806051204020f0d0f0c1a03070f08070314040b0703060b0a05180d060905070e0c040e13030e090a06210803041115120906010506040b0d020a020304 71
    0x11090f4425025116003040301c43c1e00c0b4000c20304e030300c0c000b010340410007501c0c12a041c05659038004000c2c06800d0116900c51020070a042003c0d036102103201c1d01082040c00c0c40d0805a0301e02510a10940f82d840d1025016000041840042c1d00304510303d0700055105000707038480c0110782d1100c40b25101030b14041c6000da040c0c0000310391403c000303410a41c000440c80c80d40d1b8107441100d4011745540341041c04007034442d000302d030118003400e0340b1181010307040001c00d913240304404006010b240035042540c1880301c001ca460901a00c201c20302030040104006581112440c0c1303810003481010b000b804041401c04440c0140074041c07041d8085002418012540b4041e80050100e0354103184242544002c01550044a142140050b01000342080042c4c001041c00100c50301451004001c40200e0456a512258540011401c091401709180034030a10010400103140102030451b0782515040c285141180d9900076410380c5a801c0c0e07004a0591146070090060350301408407011640c05c00c4d03010002841c0341040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307099388 1250 307098138 307098167
    0x501020a1d100f181410090b040306050402270a0507020c0f2202030124020a030f0e120d050c0712051f02040506070f060506010305041707020310020304050f0d080714090102011b 78
    0xc1b8030b600c1d002c05078080d40805007100e038020101d504092443e10381d80c1c05403100078401ca9100381051401800c0e1100002c6e9200710708003070105402d031445c0c4034240e00115013020b000c40e41554004024401c2c02d541350f284c3c460750a1030548e04e490b500c01170204d41e440007a1090080c04040750000c000491003090036107880c4200c51465020b09400203c141003661900d60750300703003c0d0010300b0520016a171a130141802001d0740102400354030141d5654070200d402c1400301603130703800000c000141e002600302c4100841d0b4003404907a82c0c012443c0c00107644d41755840100c04068103081c03036141c0501c4400ca20380d5040d5001001d014004030b40d160964a0000b0f0644103e620444d5072519140101380f00354464411030348550390010107440600400150a04c181d00b2840049074540b2918581102500f21400518000c0e1f00c98002000742200240e1040d05011040141204110404040000540d03001d955601e0280c4240d2086583e15070550040340542819610b100049034544912455550f00c40001c400c4c000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307100638 1250 307099388 307099399
    0xd060e161505030c09040906020904061a0a08090f0d0e010906030c0c0311240f1b16021203070c090c050a120c0507020d0501020a1d100f1814 62
    0x105500002585003014080c19035000104001010780c1d9008900071508005485003003820131442d080020142c4010000c1194116004a0740407090b060500902e8040c007203840030201021072441c04110b190090080303000800c0310090200b450300d001880810110510001620075016540c1406000904a10005130000c0c404100024920703200c0c3c82400f00941c1345580d100762a508903113086550100002076012a0b0241980d0790030b1048411410518813256251081401d02c0e01c10803010a03088010502240e00d035002c1d10440072628240100d80d04007401103401103104101e0b0010172198803090403890440c0c0310000d00c04041c0802403070440d045401059007404410010b02c0220741c1070207a450444049501900b0380c082943c0c503070b084128a109070385441e9040200c0740d0000b4508040d4804107958607513000070342541d5140e0244600400c80d001c0e101103030043c145a0041400142903000102c10403d00c0d6050361400ca105900d24204140d10030100c025194a9000341d100c10811080c0e001c0c03244 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 307101888 1250 307100638 307100653
    0x903050a0c0501201b13021b010e0105010602030d200403050c030708011505130b100c060b030606060d020306031e01150509060108070f0306050604060804050c0909190602090d060e 79
    0x20409100a1050804d0f0070050680c07075411007000c0d4a122050714603035500902481540190664900c00b03042c1b19920321180406210b064810341d821107010f01c10380b900070f074100001802401d4002048400441d481100004c45440b44e044202c007103851a40100004140000c001060210000351840c03032603411000e1b00c19095031040007508030340c0340344201c035803200412000b00320b10314180c01640030110304c008001c2000c106010000c0c0c0a501d01036882408030b00f410303021100b88201807042c591004400d800800c0e050405d2000100c1034001c10345d81d090790136000000100c3c01d8500340808500c403902c0c540c0c041c0765103050040345406000d00121450704a104002d0014061070300f600b11030b000c1d4406071507070290b0ba00d03004001c48160003401480d1081c136440d1003001641d6180e8030000d100a01a85e035464136203013400d1419500b420640f1610030700c1010310070244800c5400100781032045601442215050000700d2800a010b4052401015400407900302c18005200b666000b06600c1d207200b00954025 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 307103138 1250 307101888 307101917
    0x203070e01170f060609040f09050a050706030216021c020901060e03121603030203061906121d12160c0902120112110d11121b0a050607120903050a0c0501 68
    0xb645800c403041d6021404080100d05a402d000c0001e003883d2101500100d101240310300c0c180180c8100f401c0c01c503000d03400812a41e09001c418082c83c40540210300e0194944100c0d9000d1215400c43d00001030310803481e4220320343c450942400035140c2140d01900d50003076503940f500d000d40501001d45189019018074401c040f0071029a40c102c03052a81005a02d8421006035201100250001803071550881036010b070054011540780c1c00c01c001465150360b50200d070704512010009440c0c0784000200a0908190588400342c004115065004a01c14256445412081c0441c100c0e0100100240500c0514003000c41d04143c113800504110120b000c002c5030f40d99071800349154000070280082c042c09a013100620791407602d001c40c114050300441085c0c2c401e04002c0001801403607269903807121980b01c048180c40484501143d000b40800c1100c454044600e0007010070214811941e0007003280240890014010380259203a4010710342010456603074038060b281c0907a018240780185404100031031902d100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 307104388 1250 307103138 307103177
    0x302010c0311030f0606040302090c0309010b0a030f02220e01061403030a121a060a0e040605010f121e090803011a090d020103050403020c0334030507050603090c03010203070e01 78
    0x154030341d0001d0007510f9580d40769440342e50103002804403640002c00700000409a0749180c111400f810f06030765140e60364200b010301242140c5007840d020703008034440d00e01000480d10b0701c501500a02d03015914078460740314848503076882180640754614524580000b10326480815440a001d941d0710743c2c00c5094101c082020141c0d607014640b100380005020148000384115641c0040b80c40349031695413034420408010004159400090011000942c071441140c0c442c0740500840c8020720080c200a80951114000102030002a1241d03d00e03039038072000360303d2104640000700c1c94060b1340048104030310311151801d0450f6902c20321581c9460500072507135071110404802152840c0c607000700044c0c0082e8082e8019009040000d10580960290742101041510207001040d601030000c1402c2e03440e05a0001c000085640d41082c0294150151030f050001030b00000d4808143d40040354181d4a0b66920500340b803400300c00d5030103980c0550000c01404500c50300300d85d0465000340c2c00d80b2481c00300042039603100c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 307105638 1250 307104388 307104401
    0x60f091207050a05010f02090301180302120a0c0b010605070b090303060307031e0b0f011a031005150d02070b0105040506010e09060f12151f030b041118130302010c03 73
    0x100590444861103100080c848010090a071040341a2140030245445803800c4440a0b0403100320346400040301d20aa142c02e2040b412071400b03600c10340c1c000d02c0741e644001750381d0004191002880003000aa16262500488021940340e40c401140d180d190b8503024020201e405c03c1c4030071100249024041900c41e000881940d11501018004002d040c1c41c5850304104003160110300701542d40180040e20100c0e00ba500c07120311505c413402000000d540340c44100c200031300c6290200008403c00f402880580f0307012540d80400ca640c11200020328418800e00d06030540300b5240c000100301c2c400200101000750f454825030484400b100d00b082155107140056801461301081542d0000d01a0000741440c9003800502031010005400d01d241074501c844c602d0301d4007100541c061b0604030b40500b08107a50351001d0349011282d2000da0801c10781440c1d551000480503000d0300043c45841107241840c00341d04d0304000700d4172446070340d80c031000b076070501c0c401d64085001c40040c01da00550070154813080d543d0080c003c85 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 307106888 1250 307105638 307105651
    0x40f0c030e061315020c03030702070807050303041802030a020903030a0c03020111040303052208010f020403050d110d05070215030a1b050c030d0209040f050705040618060909090c0f0f08060f 84
    0xe02a01505070346a00c0984d00b114840c240070b590a0000b0340180800300701562007403019400501d0102d040a254070b00c1c1c6900b41e88594420b5000b0001441040c101c1071280010328041d82c009620703521001200b20180c000c200c0c59a070944400700ea0a07615580c007000303010300f0328001c0d00200a806500680034010b03100310b00001d40400c0c402c0000d040130000310004010044603201c42d00a080e40c44150460075612511071110425401150a00500c801070114005985072420650302c7c2a04550741740c2d49510844003030b6010f00401056000544d100c104500c0004064003411565907c1c1030b03040d04006007101c622032303034001c03074402c5583d0081d43c050002c4074005035109008609281040340303400f01030b51001510540060301c500d41c3d802e09901c1c901429000f58010303200c25446904107100207020301c406500c46440c10070700720300400401d904100100e05948003184081040035150401c020780c14142e40c03208240d130991050020300030410300395241c00e440656055485c0e0361111075058815a00030390f0342 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 307108138 1250 307106888 307106911
    0x80a2d14040818041b0f02010615020102040305070f060207120f0b0a020a080f0408030a0b0607020301020c151609030602030406020702030a050c0301180b0112050a05030d0c0f08070c0201080a0209040f0c030e06 92
    0x85015001b01b9074814180c02030300c00404c1041e1a143e03146040360700c80c29400c0160390003041c00d000b000000e00940002d8032000c51902005894030000a41d41c0d07031781e840f81410f05401740c0c2c290300c184090210703401a495001000c0c1147c03818180340000c004d501c036851440c0003a040e0000f20b816100544030341401560481d0078141103441b8602c82d100141030300c0b42002da00030740800401005803020300141500010f240702500107145c07030340503a6190340d41c0100080040480c02040d0300311190030141000940c0d0300120700585030707900c61a140d00240f00d00035000e5418400c030300d038000400500248200700210180c1c003c0c0896002c401e00c00451284500c1c008195036490401031052404081100803550701500407141a003071729840e1982103900002d20f00180e00d4442c7c58030040c040d045040d81d2040c45051a0080c0310f4503140000500e8501d0310000281081703c00000b040550aaa80648284d18402041000045420062a0010000214800301203030070902400b540d80380114040b4801c80d4103906 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 307109388 1250 307108138 307108181
    0xf120702061e060103020405130905060106081306020306060702060711011b0203122101060e1c08090f01050d0c0c06110406050301170a1e03080a2d1404081804 70
    0x4007410b228600420003810581c0c00d00c000a110755071104580a0f0500d42d40000540c1e1050b81002410100140c22080034000b800342030001d031125143c0e6141c0741c1d07600044010b0320ba445200019006114002d4042e600c400007145520a02c01c0f0180080c010a0090320345241c6810442060350070003c016001035810340006000529010110300281003141494192001c0303415480e9484c3d19000c400e800980000302c10b90b10f011003d051a03161540404800c841420294100f5071310300700700b80308815140d8081c2007900c6514102da40a001520b2062541d50030070b014007070304004028401e2030b81680030340c5d0b450704280c0189500c95040c4100c0e800d0340c4103680e8041c0b4580c01c00302580c010f0f848001b5040110b2082d5011032010880d169140c1c0000503030b1451684144400c2d00f00200031403000f506100781700c0d00c0d042c401112098107074400b810740400c80c440003500da000304540c0001065028038803120b44100604010410501500030300701c0040001000c210b01c2d00042c28413045444090864498080400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 307110638 1250 307109388 307109431
    0x50112060e1603050a0519020913051606050c0105010b0403080307050f0910050901020f060114010e0102071d1e010609120204091202030a0e040b060f1c020f12070206 73
    0x4101c081103150314000c4448050050802d20042c81595106075401d400000540c410081c2c01d0044a200d5980440c4528120801e80c00080b003205001e4004402001001c80d000200042880040540800f05202c0805030395102030207050360b880540c00d4103040d4603000002c01c1075004602a074003902c2c0c000f10b00b02d065549400055500d680702c4d004074143c0d00380911101c5541d40d40c1d040405010784486d91581c1e02d07038018000181c5043c1c2c3c0c894130380c1d41c55001040144a8001640588250707071109180c0013616103035040040c3d09181e0140c00880100e10316401d01c1801ca030440440500505022590401010140354070a45007002801020700089240c60200803000b00d091201d46101d0000f000069010760329692542c0c480485c0319400003603000440c09916803a0003100510411400743c0d014080d074040310002035403500c0354034012040c00c800890381034900a1003048072503406441100c1150380c0d03101829030140d140c00544d5070b0f62000d03d130800002e1b829440814154007030786144100104d01c0381d005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 307111888 1250 307110638 307110641
    0xd0203120a0b033a0503190f09020901150e030706120c051210030201090503070b070f0602040320040c03060b03070f1e080402030f011b0c0501060315020c060105030105011206 77
    0x742e034065240c4241003e040c95100d415100103142d404680c4081c80c034111311039980820303001c14107803d010b20506104006002200c54540d20780101055800a049008211034500424040d18080c0d0880d85400000c01c00803207401440e610142d468403030507281c2d004078003010340e41c480b64050300c0b000030075201c0400318039040c0c2d403c61210b02005041050821011036807603900707800201c42100d6103030030340782d000c10039960480748550103414290090000c1c5410409407076001c0c40b428000a02074000c1c000c03024240328159042e200a1580030810348941c214115000d0705202c40000e0b294815480c00790380069142c040e1099400b240c1c0c01c41462030440d5204003080d50402e04800c9480c05020380b402e02c800c1c241400aa0740700c2e4480c0030351070b600114141030050500c0c25000005c000840d03172600102040d004034100c02c0312021403207032500c09002540c920f0002c1c098030040d4030080074020442d40035040e034006d0b42c019014406d58681102e090740c0e66102018240c030020300c43d45e2210480091780201080c0e070f5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 307113138 1250 307111888 307111901
    0xa151d13020a0e07140d1505120705010c0804080106180b0f0f1c151d0c0303030105060c01090206030c070b0912030c07030912031110021206040504051c0206090d0203120a 75
    0x417800c00b580070036064900d04200d40d000641d80c5103030aa80300415907d6102d0024003d018100a17106445081c0224911a5030b07000c0b54092031741400101c5a1141c10405800c08036006040100020f205650f6940707058a5006102c9603450701c09410441140d056051401e21700f0000c0c80003c1c0100c881d0300400d424041480c0080d580300c2000c030140c510400128200380c801318043d42094a00141c3c1d150f0344031188601a001d642d000c840c50b0421070944036644e070000250b81c10b4820407151190360703c0700c200d07081e4018403400000a400084c00710402205800358005443c07003e0007900000704544e14a4000d58444880404004000030240f0100300340f40a108007500c0f88c0d51282c209001e800d51542d0a41000c049095001c6000a644030031491072030009104c1c0c140200d00e258003d506101c8a00031815080d10004e010f03034080c40c0d03510001400d0101c1041001d44482001c41d624003188020711000351940001c50f01c0c04070a10402034031055a9100000302c03468146d4140304440d15441d192801d00107001c0c1c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 307114388 1250 307113138 307113151
    0x1302030303160c06050135030a0302030601020f010e0601051f08160309050f10140c041a04151205010b07031403040c1e15080403020d080a151d13020a0e 67
    0x8401d8400c100207130091041c18080c08500c0e0350803031040940104d03c0c80c00d41a501c00c0e49422504500001e840e01c00000c00e8843c030328103509006d80c90fa0366200c0102d06e0000410305e4aa441d60803d0910a86140f02040c0941621001d5030405018085d0801418808081d4055000020845070014800c9860ba1a8090410000b440c001c2401e1859032219803a040c8007250110554010004d450524a0b1510a0034a10071465400d07103141d00d4000c0b40703032500707014900c41e00da6000c1c0c1d42c800d411541030200c400c031f401811840100049650100100400b15920038a513444401d19090001c0740521700902503c141c182d0507910000190b0513101c8c8030b48036400c0904226844007010a000c40e10501400443d2405021202c0b2080c101d80f42c12105038064800202d00024050b0030803e100c082035005c15860701c0e0710381505020705a500c1d1500300c0e40c000d02904001000d848020300d4045069130111a900d201d5100030300300c00740c107500d4041140040b07a4882c0c0700254407004c0890108802030380c0801240e401007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 307115638 1250 307114388 307114397
    0x7051e12121b0f0403080405040e070312051e03090a062702010309170f070501050708040206030f040c210b010e010b0403120e03010507050d05091f020c0109080c0d08130203030316 79
    0x80b01c810401e03c0c5904260000c407981d000201d130501140c01c10f44159614040b191340204589481e640720340c001c588465070b0050400400041d2000b82c1c401c2d1172520480ca5403180300c0e4903a82e14000c2c2c611a12504070702c0007101d13101c0c20211001c1300a55880c0e100d1120000c0302e03102048052035035005600908901200701e070136061a240314615155184080d0601b0340d032030301041d0f5032452145840c50840f1402030156003403280e201c05100140e114401566840701100e0325030304c815191410306402c000b83d5540f02c0c2000300f03210754054a10b640c140300b0744502107100308009031841e45c0b140018020ba5509005603031205c1002d04c81000484c2e0741341c1840e01e40e0342150618096210b11800030909440044400201040c00002d9042c42d101140c4211517008050802903ca011a000003030f40d59200c0030f446106182d1740120b400c0d00c02100030341c440a259030f8002989035482c0c0840e22041c0d1284141004a404078000b02c0001d858148456042034006600402840c074665800b8070703a1070070b0070315190a8000c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 307116888 1250 307115638 307115647
    0x10e0415080a020a0914010501051c2a0305060d06110c0a0602070c0506120606091206010e1b07030c03050a0e04090f020306150102060f0c07051e12121b 67
    0x20310061600c40041d2034541c000d02800da01500500c024040345510a8280c2854042400b50320409000e540d03064030303404d1030719a07650003200480201c9003026000302180740c1d14015032a008000307424400500100d10606400c01d003441d0110680451700201c40c441c0d04941801d02d410006022a0700141000703a040041c1801c0011622410349819454101200c0300c0e80d001550303e080c0410b29901100030076080318400e180110944074240c2e00203003c3c00b02400f030030022407002c0c0c89035075400040c01840203900c1142d03a15a502d0b518000c04880645d030400c0e100c11244001405081d55004945c95035416407100a40558035540894142e07001000960802a40d61900581c0e0340e5240030b01d046860295040346c02550341401010300340280503140c0400e40a00c2084403406980108000760304c02103003d00790b85a80c0d58600d00580c81c0c4209440107003540141020070103d99024001090700b00040e0b011145114005c5482d424948645400602c404803100e0001b42e403c169807118003403100c1d07861071250a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 307118138 1250 307116888 307116911
    0x6040912020106051e13091514060f01080103020114030901021e0a02010e06062407122304050120010f060b0a0e04021306080c12040f0b060915010e04 66
    0x60480c0c012400181d44440c4100094601002c201001c03d555a40001d0f5090507480012264210081050040d9458617420300c18030110400d080c0201054900a0091048140807007085001c201c1c3d2480c42000000f80450140d440b414045058a5042e100c1c06082e944803c030984e04d5400003403514031199002c0055020381644507610200c1e10f02000000c0c0d49502100d000a82581c000003d45071444c0d003c941080040e540e21002c0c607003e509071241400a000e400303550501103224250f0090407241446174000d05407648519030030000e024120507103c629412182e00d0313109208034810b00340007890440400d130a030320b40c4d409c0b401c206070400390001070b9080c070441e00341081e02c1e410f0f0700032801688007148803801d2a801a094a440c480c04a03400c52400051217424110305440d0301880d0104241900040c50340e1303c92504844450f0034403400b02000749020310780000201c80c0b01004070750600d6084007041403420300c20349560040b82901c00c901c4070300031048011507000c44401800c9610036111401e1015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 307119388 1250 307118138 307118153
    0x1b020a02130b030714010f03050906160e06211e191e0609060b070f0305130e0903070c080a350304060507030e070803030c0a050919030326040b060409 66
    0x52410f4212088171080303000014211003000380a2005060070082005a0341501184159000400a11104200d581340004844003050810595004900000d4074001503813091003080e546c0451081148007036a4540c0f519411040c0542501c1c0c4110803c1e000c100c2a14200007070780c11501c054600052022036a40300c5081e040c030814070318803120713669440600c40c0c403d8500032980646070307016107a4034201e02a0f49154103190614006801c0003c04110140c003c251038090100a18644072144e00c9420908141a10780e440200219858449010001030741e02010070f142507100c0e0080c2e050300001d0170b4460744648509420140c601c0c0d20214001c0c2100320880f08000e103000b00c3c0242030014070f601d40340348081c0031180d000030945c060760b000041c01c202158000080303a81c005c10000d02c03e900e130107600300207a0711402212103207603100005411880705031001361010700880f4002ea40381d160f004005c13041c80c0079090300e080482d600020b1000c00140843d07441c0e4005c030340140c00980005811800381c3ca8a10307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 307120638 1250 307119388 307119403
    0x40308031315050a0f11040b0c190c081b1e01120f0212130206040b0f041d040b0f01050a0e180706110d0306060e011b080a0c061b020a02130b03 63
    0xc08459440041c401208014420000e002030200001c00c41c02194500741e1106c0d0040348129134500f0f0000651fa00140011b010400641911014400d5042c1261400361400451030044e021940b2408544224145180303091251520002d08003421040b92100c107d8804800c2002090521500c00540c0406000500c101e43c0c032034045040058803100003490540c420000501021080c02030310f02c0c1040941c1e180d00c115401c0b5880300982c4ca6540c60f10340d200284602031503116074202c0c6407801020724100e1029841a115900c2902900601c1c2e680440120400400b03026107074000212100074440f0032542030b10300f07400c44104074800c0d000301c4210300c8091a00c62550817820016240310100c1040200420400e1100001420140320246c140100144103c509100041c10030000c0d030f00e804c00c160345441e10f11300c00303541182110741c0d0742c00d150102600c62103603070204a81c4d41e89801c004c00c00514011031000b90704011540500900740c040d07000c02610401203000d800c079142e03580449080d103075020000d11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 307121888 1250 307120638 307120673
    0xf010309170c0705040204060807080406060b03010e09010c020d050412020303220510030209010f1409040c0815061201090c1b060501030605090d0927020c01020403060605150403080313 81
    0x40c0d89440824150f41803401035840140202d00500060086540040703d1035804070040c9082c58080c1d036107043c40070180065900c0440750344070000010a1b425820042c40340f144581c103009100200081500304c4e5a414103031041c2c400101300707110070b0101ca906800f505000c05d00040c02c507400c1018013440c0780c5080303000390781c03080c4007010340d100401080c1042854044d09115504045081155070390010b04441015000030040110003900b0b4a0004d1503c0705540e8141800781c010081449019000f0301410401d031400f201a40540ca101c6000d480c010045801d40304280c85005142d928190301c1e480178145440c040c0c4240b084000300b00014410b43e681c03011849004500100e160352445c10190201c8070040d10454042c4c201101d800c1c410780e0400c1503003007101c0c039840da4550007150212242e0310110f03039910300407078180c000110302100d04415000361050300d00030794003007044940d20810010319403c1e150b440354061400b030000f0400700d180d070005142e000c49012884201c1409550303840000103000c0b900c1c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 307123138 1250 307121888 307121933
    0x4210212030a0209092215180302010507030b030d140309031b100614031b03121204141c030c0302040f080d030605060c0a06050c040503010c1e020c0a050f010309 71
    0x89086171608034119500454031420f52001469103180300d200c5c40c0c001d454060300c000c204980180c42400c26501240000028030f8540da1003082c9494024041d0005403440f00010303080c02c02050191801043c150a80c070200d8984900f00004d2070000010750f00002d004000302c1c0030a2000c0c60700c2c008861040284041102d0181c080f001c1d04280040855456030400450524440c01c01502a240020303100700e04420403070359840304150000000c0c94210b021951640a620100d402d81304000500c4506002d14030444d090782c2e4681c24500c0c4242d58503060340000c102540c0144608410b1402030f4130100400c0014540949065150f0800c10a1040e0301e500144566005081c0c0c220349507414811000540000c0750650316140120b44c800340e40340340d8004080c4c003007a038400200342c0340070008084900600d4003074000e002c0359007c40c00c050445d02d90a02094040071034001d19000d21480804c4805000f280100400201c90501092000103200b840740c050502d071b611418103020860035601c1703204c1d004c00c103000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 307124388 1250 307123138 307123147
    0x504021215041b030312020310030c090218030c0105071407031a01062007050f0d051c021e0601060f0513080105060a051512130b0405010213060804210212030a02 71
    0x2803943c0c2e00070140c05001035a0f03803485001e0001a5011506101b200c0c010075025031039440e00190002620f10300d030f00051907100d121000154114081c0c000d4038a000c054090200e00b034801805040c0c0f104845106940000c8040000742c000520040f032000e281c82c288001c80d00915141d5554208412065041c4500f00c0c6407200100a4142d2201c90000c06010001c40e8005042e000d24015a5520759405000e00c0b800c00c0040c9100a500c400060012240d008801c441042c0381800b84444000325001c008001402240c10076120140d4545500512a510100401850786050000c8940c030301d100c500181000030811003d48400030780c020030b50140a14800016560070309604011000f01c056219900520040c061617565911150a655042c0b0700480403003000d65451922458200e0554002000c00308144284424001c055002e0840881417619017540c1c2034032104290f0701248116002050b0380c4410103141041007904c10302103115210fa004440700c6c088003040301513042e04100d500c0503507182e000c030303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 307125638 1250 307124388 307124393
    0x403080313120c051005190f0609050606040f0e04110d0c0602061305060a0507020a02060d0c1202031303030b060405030f0f0d05090a1202010c0b0c0702031b060706050402121504 78
    0x80b081c41a480306420140d00c090265582d66440b86030603001c03005481d9541c00040c0c141d049980544035262408802044409440300510000304840d00400f132006180c10005141418840c0450b03080d40c10100520b4204c6141150466450400810848268a0001440146d516070140c1001042d104110b1544824200380000303240c01d03c0140712403001603041c40b002c0041500030515a03040306451001080c540d540074416880c0280400740250041d40000d09402030005a9218035908542e9079500340503170104040000a9001c1502d00000b05080702c0305590000b4081c5c2d014228209000d0111401c0958440001313051040d494001c0c0d911b50803a2a10540010003408900e081587c181001c5040011210105940c0c103142d00070710170021503200b90481560701821010000b1940010801c0032440c0c81c0c49041d6aa030480314080b40607105181c40d58003070714041101c0b8240204054038042c2080d03543d4030f40302e015240151003642c1203181d650b030150400303105003e6680b0010814005034010b080c640b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 307126888 1250 307125638 307125653
    0x30602030610050f071415090f010506040605061c2405041503030f11150c04091a03060a0f020c0a06023004060c110d031a01050301050918030403080313 67
    0x40780c404225040028031084410881945c0203190000704280c5a40c0b140c40c4043d00e800f61200c0900702040e1000100030b030010b40003511800011240009110a07102c0c5028001550068019a81c2c015000c0c481f40001c4c10081110050b420108400850030500c0c3c8081401c50011841c104800758138440801d21580c00c290007502c0032401c68000e03080b01030b0300e540c900411042011040d582001640003c00b15000d20800c960000c10481101e07684590030140c0080320b0315881407155000d00e50915405180c2030f10b113901603404125014025140b59900e41c000000107201c503210a4001503401c1c0204040c8107410841003100c1c034401d420050341c42500461081030203503103901c031440c800503029101311007141e020075554000d0391112004c6040c01c8a044155020000c4003000d0141d4030070080c084550a5168019030001c140010b100c1e00b0000e184001120750384024020309801c11001404510700d020004d01000c081c82450741aa401c1070340720b50724128035a00c1691041e04090042d0210810b0103802c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 307128138 1250 307126888 307126909
    0x225110406050904080a0807180f050f010201020a14090d0c08251404050a02090d0b06090a06050105071e080f042c0601080702010b03030406120b010e012001150306020306 75
    0x483d144006840c1c159035180c21445040f40c81c1e0304019031a00842c81c00f501a032a0068a000d41c800f40e645401d0721140d81a208101c4c2d8899184511416241c4401a50041c401c4440030310b40b50b6221120300308403070080c0342c059110301d01c441d80010300c40c0c4069021400c449e568501a11003030000d01111040c044444100d4203030412400c0020046030820040c0215178940e0002d4002c050702c011541d83c0d540040b05000780201e074401d5820260100490b07080156130b4040901c9040125000103680c0c030360103001e10458250340642c0e40804e004000b0f460201d00d03481d20a0080390ba01c40b4a1803001041651400015008201008401d20300072800303014aa0010000c1d0a9903880403020180e0043c000020b0500c1840c0540721505210384080416500351003034004649000300034003140e941d59907030a80108181a1125050840e03454001a5170043d07104803060440310780c051f515200350b101c50032582c800c8811181c401125a41d61080284541840d1504245c02140103810041e1680b8021050103202d285 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 307129388 1250 307128138 307128149
    0x1d061e0d0b12060f0402060d050a050601020d0806030d0e060f04060504060207140108131121010506090c0415030209030105010b0415020105010b0409020a170a0207050d020f100225110406 82
    0x40c4102d1400c8201c40019450364000d4a0380c6045810381c40e14000304616200e0f80004100003801c0038200034200d0b1660b0440c90081600703a00f01c41400754910003c58a442081c0c42140d41074100c81c40140c68584103c40d0020a504018a414030b080021f00700c911041c2d009a1241c0003159010a040103c16018440d00004140030352a03004102500400208100b000511090060000c22038401c02c0c407007102c00601200c0000340103a4901107000703920b00c1c440d25502800e5220707903003040f000992038240540c1590144102d88040b03810036050801100c03070b003844110080101030303091100c42400d9600b401075074000c0030030000300d9a0b0b840c00d200b80081840c45148a4106580c14070b401001000c1600c022681110b401e0400162909182e1004988004c41d400300400304504040501201c903c41d41c8c010710140b8461003c890b00f244103d10180d071216250b08030040c06400400714920f1400365600180090003020013072000712540d1700349542121000c148260782c05214108041454105440344901400c0d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 307130638 1250 307129388 307129399
    0x153e030f0115032a020c090403031d0304050315040f170a030e19060b01050d062301020d0e01052113050d09080307020d0302070b030f060a090203071d061e0d0b 70
    0x410759196403074800c03a01040d49185402d092013610ba8070078811410003080c0144455400c0c01d1605009002d00b88040700c21450103202136103240301c1d240000488045a8018014203100f503051350b880502c03203000400568074042e607002c0520002d0913480c4003890007892150b05580352040f40701c5c01402c81c0ea400c040385095070b02103c80c10301480c480c041c0314191694000c82c08030f005d2030740400480303850284501c3c08082500f041000b14034a20a5072100a0711700e0108001100310103400012a9201007442400d0003241758007980c4040741d4884c400620308031136021000054040c01c42d1030844002400c8640d006006005041c03481000410300003150407030b2040c90001e035400d04002549031a4854048024811400840c0e0300041500a12040000700325122807075899183c401030350494440200d860318807070b00031440b01180e00c868500c2a6802034240d0369560b41901c03421010301c3d28101c0768410480d449401448406851a01e80c0d000ca100307203491001090b200c200e501c814001340c0d10760440051051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 307131888 1250 307130638 307130651
    0x90406051f23042403020414070c060b210c0a06020d0212031e010f060206060402040f0b180909070602011812140d0609020304153e030f011503 63
    0x110340000d400d4a602d00360440c2d0011018031880010001d05080104100d15640600703654041307400c8a90f541c2c01c8a0080c6c50900840784c40701e0042904020484011000c141c42201c0007020542c96840407a07440005800da001000c0021168800141e030030ba210241d83e80801801460743c1413003000d41c00104100e00081080b401300310707000303501c2d04150301da022860780c0c01000081c85500e0105401c00150301804988100c1e503116010913015541e580600e401500c10000401c880b820710740b003110101c814591500001c2e81c1020500d400b103a10041c022014045140458082507690b102c4980c00b500501c001082113030321f012400782c2940c0b50281402040301412a044000c00d500700f44610071050a031a00a003481c03456440c2503c28010312200785000380c034266002c9104016503004601460044614030483c901000340746040e61001e495030b0034100c500166010140344004e05002c10750b0f0940047e1034100206600e60311154008a41c0b00c1805c0c0c0c1d0340d100403c254003c6460701141c5072458903090124 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 307133138 1250 307131888 307131899
    0xe0a1404150c090314030309060108030423010509030607030204090b031b01030b0d080c10050a1e0203060d02180403080c07030f0e0105070b040614010b070f081305090406051f 77
    0x40c211601d09804215181c4000200c81c62243d01c040700510b90000e40300740780d00843c60f11550340f50802c40d1291114440c100003c2042d40b0008241d504407202107409003a00d906003101d1901c01b001032100141482018000e1042a80c0c0a201041c480c08a035640143c82c2c1c0d01d8100c84c54160f401e1103071802c1c02a007240300e040c41081c500403422b200a010a00b00840c0340500034002c07a41e4001008000351040c2c102160401c2d542c600403407803010201c0808400d00035511080015400c83e500180305071068002030b9107007624112282c02540d4041d0700100451168205500071a25801c00f068601003428010780400c020550401c0c0c0311504080c14039400350400c0b04554020b03240903030360b0007d00140545120f80400980c411070417903424549c07102c18042c03641481d05c3c00300003512102c0402036110255038008101407445038161088260400302c0049004101d07113560100364000b07040f0880015501501041603241d40030341902803445140d0005132898100e2901d00341e50458158030b401c050004c4401c00c038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 307134388 1250 307133138 307133153
    0x10f030903050906090d150212070f05030402040c030204090f060812130e150d050c0a0b03060307180e01020417010f05270a0203010c090e0901061a13030602040e0a1404 74
    0x1d405a0070b8134082d90b210a51000100328000c4407000900071b0f100401000360100c007540242c18200c4e0500781484082c1c0700d0300c00c00e07910040e980340e01c3c0d40010001e000181c050f103802d030001c5121002034180149001e03103410301c0030180c0c1c0501280c419136a80311031041141d95005c008008041c8101d120301c3d410042400303803a40ca07000103485108240f10b0340401142e4500352034440b06032440d800030030315544008070340341158442090842c891702c0b0b0740d07a43c3c0000400d11084d001b204d00c42c1c040140600b8001d420a00d80007003212086011412869a912800003265024030080006c0d100c24144c50001c9251140700d9801d55a8100300003100ca42000240004004490041c00380a10b001c039240c087d031070301d443c009460404a80c50195044d800d01c05480d0140703400c81030343c0702074940d211501e1072582d444400ea00d00380c42540c0700c1c1801c901d41c05400d10680140c1803014110300c00607602a41812603494860034141d81298000c080030b1103180c404e110078954640315002c61524421010042e1345029101c2d0340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 307135638 1250 307134388 307134397
    0x108010f1229010e040204140403140c120a171308090d0213060b0d0b18060d0f060603050304051f0c021302040b030405030309013801030914010902010f03090305 71
    0x180b924000503800d240c5424005426002420b10640001c101e60f0f5a014240290703000790b805a0090340b030003224501c03026148003228030071074064440c0752444180051030a040d82c090780041c1c40d6401080300c21281d41c4030840003406c500440e6a10151882160b91505100b00c0c0082c118280001c0c0414501e40050049400d4603003104c41112043c800c000d03103002154a00c890200c0d00c0304458908600480c4464074840136000d4a501c418040100a0340c00b010b108865202d001080407000c4c0c81000120985420700550407054458401c150205009685d18001e403011508101e5240c0c102040c14803003418066034560f0502541640d031900030314810000b030424540c0d030b01c4c0640142c0c035402e0104110382e61394041b90000c000303002515680c0e20b4035003415a144e8009850f000195405c240000502d10245800b9002400480000544022441e601084000c030807915460509d078450b07003480b000c90b506640b600c2d90540c1c03101c00850221a40c0c40014400b819642c442c0052601d41503040c000b20741c0c058240c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 307136888 1250 307135638 307135643
    0x30b04020f2b03050417101a0105070206070f0b10081507050304060506150705010207060506040209060d0209040f0504200405010b18042a0e090403050d02090f100e0108010f12 77
    0x4000c0b2258181125280b003075070483e034050241c03901a800c588600181a0003002844507080143ca0032140d103608004414000d0140014428800200949490310042500300e208802022140d402c55542e80664101220b9059204003021820060040103026925030086540c64014441c9005800a032580c0006413014100594800c005940c5850b1348032408020702c0c26a5801d5200d86403450428080c1d400031740300b215540d0a04011444a007054001d5030711084004100c50306043d00386100900a420001c00c8513030203a2665040400c00ca0640300e22401035000d040c40d02050b00c10386498150308240e4490384c501540c500b00040181500e04c0c1e007902d1200340c420540354a800c04400000e0b0240c02c1c42005142e088840d800220000d0030305042c2d1040d082402d440d080415002003040140300c0d0700c2190041e011580030031142081c105c481e8000d000110000b410840c01d414544041205110000f030450301103012508490510340c4c00000807401083e80300da6420031030341450070320114a030411100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 307138138 1250 307136888 307136959
    0xa030c033003150e0109020c1b030307030c03091d240303040603230708070212040302010c122f100e15180102031003020f030109020312160c030b04020f 67
    0x2c0f210b07100150803901009242c00c003030203820782d61030f401031200940c80710140d42c206200f03410841303406141c1c102c0c416075100f000070061401d0444544042e40d051000c0780c0c04404200e034207040400c030045140340201d50242c2c1c0e4443c028040c60b180c56100080d8804119803103a020101c000702c0c5c0383c1d40e4000202c0702941c01914012075070280034400001120b0a003c19000301c0b00c0c00f502040390a80d80310402d42d2080c001c50342201d01c58601804000e410344594040a40080c4095040101184000210080f049130034503144103a0844c484601070060203a890200e240a18502480c6050100f0880c445048041420400c000b8103100030305659041600c51010740403030150005580c12468100c02c07820108a900255520703d0701148421800049010881c800e841520202c00e45007814410301c18041d601600803d00c102c050b40c1001100c0c2c105042002c0c132800c041c4403500c005005201b48078002e601c148048000f070305040c41003221044821301440d02a1040d41900300503010703c60710034078181811050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 307139388 1250 307138138 307138151
    0x210020a05030d0c090f080d140c0d081501090e0402121606020d1b1a060f060d090b0604020304080409020a050d0606110d081911090a030c033003 64
    0x1681491280c2202400a002c08a0150300c64490350b08004408812551144039031a00c40f0300d0031400c181d403402003000580c403902e0700943d043d0140d409806101c01c014035150400580100750b918102d04081da401c0090700c11014081c94803540b00d10044104402d00700b154000781007001c502e0f250003001304041d02c1201c0300b410b8042000800e01103090076641c0c1d00182000c450b07e0341c6e00a5607646503e140d480006000c8500450f9103401d114289601ca40d0106081201c0403e001c005849848064409030380090034091054180e92100000d10103455880300c04110b5a45a0404070720010300141500e019500420820000800d804121001e4481c110390058642d000054103e495003da10031804840e450401e0101c5c03130710f8000800540c5601840200c1e82070a00515003195005c4e810346244600c2c1314640710f500000c044d1074004c81a60761054907410304000c0c080d030018000e200d00b64420399211103d14418030a010303218842e021018000c998103c1d044400086d0f041d0707440f0050218000b0507589a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 307140638 1250 307139388 307139419
    0xd0e090c1201030503130e040b0a05060f03160e09012f120f191505010c0204110d0618060e04030507050f0609030c010e06060303070f051e01060e01080c0a0302 70
    0x36140026101010081e2a41c1c407031504e00c1e5a80c0c0f0081c010380c042144440000355010a40ca90310384156840b40c1100040d40b241d400007406000017622403903101c070007080e05418a40f0100f00410710600c03c40c50b14602d442c45c01c4441c04500c0700160048904d80d040424035140800e5025012b00e802e201725003084d06200d5002c18502070350040c40f0703409210300e004000b4030250849048081e40500d215800e00d200000d004000d190449605208002c0c0aa490440c1002958021a00f1840070360001e072001c071700b26214802c190916400b500c0207903161560743e80184040744c0465000345c0056181c036000c109950a0814100034000014401003c0050000e00c50082180c14458503484003036040443c4c0460a150340e0890712508003401c03080312986010f201d0103100b032000800d14090f200150146d4a408401d465001100c10459419a05441003110b840c00345a40842c1d05d0b0198084000006581030a11400b100c0da60b10603442800f180d03025a0300501d00365501080c46040f41c0d8110b40314034075010310701d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307141888 1250 307140638 307140661
    0xb030c0a0b131701090b0105040911450108070602060a020a12020a09090f09020a03080901030b090c0a080106050909130201120c0e150403240b0d05010c110d0e09 71
    0x43d000001210540b5074410101030054100020452180407000311aa8031003041c0012540b9142c000b84c00c0c5d40c0b10a05070581800d103c65248280c0c0480d4250180c800c85000b06003402606090700b54115403650807190741441100c810040c050609103019014a602e0010000c1d6a000c001d000b040500d94009824502d1500541601009040c2c4210a44d16900e101101400701a01885050180c81c1804401000d013166480b407805c0c0240d0007812005583e056480f9214907800071004181810750301d100d41c08195171480c444920800c40d40c00ca40780c0d40c0d26504801004081c040c2d200b113050020901082c407051381e886d00901d62000760114001c1407101070b400121180e80700b0900c41500d46140001044950b030f40b00440c0c10303d0030015030300000110714140210829114511000d00760300d010030300e141401d461075864180d24600c50580820004000400603c0c50300c1c450908641d81e03036544000341c806642000c00c40c8038050440c4050b0003200e40c0050054180c508a0b4501d6200340e0401000800d5102e40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 307143138 1250 307141888 307141927
    0x1c0203160e0a1502060f0109110f03060d1a070314012303071503020c01110a0c0206030901020d021b0c0405070909020717040602032107090311030a0b0703020a030b030c0a0b 76
    0x2c8030b0b12240c00f60048041d480b80410740d80d000d0384007880400483d1541d107a00072588001c24000310186482c00e4192040d50941001c0c7c0b500b6449032410440102240e6040c42130fa1601d0a031000b00001030034420000360071a00045690910780b02c411004209402c1c0102c1030090740c0300007002c0c04086e07500e408002828400756806c0030040c44a65602c10200301d03816070182441c042400d0081040c042584400c2ca101d002d040c490800040402d0100300042c00d2034000745820110180c0054188054281110180c0e0071032200501c041502002043c01088100800300700144140c1d410032090510100090002d425405003981c1950000b50600801c000c0e0040b2000101048044030341b5151120300003910f0394840b903051035280218803281408000c400d1106c0b4001c41144d264001c80303e240d95103460b50842c0f001a0380782d0500980da0f03460041280100390502c01e4002d41c0e401691025503200280c01c80d82d40f454414025444080c0407642904c500c03089109552040c1510390300d981c04070421030603070f115 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 307144388 1250 307143138 307143149
    0xd23031306150f050402120106050a0c050a030e04060504140a0b1c08130e0c0306010c060b1009090606020c011b02030a14060103060f18030f0905060f1c0203160e0a 72
    0x3500088400082280401d001566025540c4400c0341d80e1301d00800c0241c0c05542e0654103901420001001150f000d00c008106180f0242450710f420096510303134905148616200358045110051b4203210f503e0075229400207000200c40c204842d8000a4451003242c00052080c00840d903981c280c000181c1c0c1d00e2054001c00c084001424080704000d00d407542040c1c20521640541c14040745002c40d5820700301081d41d02c1807203000701d0035041d43d6840f801100c1044114100703544a664515001010f80c03a0000c0040d0103921545608042600e0502008101d440d80e83c050402c6420014109c60180e074014030420750b10740b642d6101e0f0366100d0140000b9092022000000700403400307100c0550b4080358046035090480c0d000d05010407850141c01d0580c0191400c1242e100d0490141000f1800000d00030400c02c03400c08950300e070214840e61540007261656100c581c24494146d0003107962015907802c0c03030b0250351101c4081000e50075130404224400a001030f100f010010b0000d1420049920b40b94810040d00904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 307145638 1250 307144388 307144391
    0x60903051e0405030c0402160b1f060509101d0105090a08060708040c0614040306051009060902130f0f050d0503091908010e0a0302030301060f0309050f030c0d23031306 74
    0x20071145090140d01500c1014042c1c0650f4000303010515181c400e84007409000300450000c0e030015501c001844070001c040581c80b07e45d0845408a00410750300d000003400c2c5940b100d07650b40c2c500034104001103041072088000c01030305050600c40491040098020001c0070300700305440340c00c1c040008501249070f410020322807203000c0801005643c80001140510b008921420040d0b490307410884080e91096905000140200401c00001c0d40a51169070322450301c81c0ea6404c0319850351070000a41e5401d500c0803480a40105280307001480039a195030003803e03042100b1860a240c00400c809011007032140b03070320450391680034400344102402100e00280008050142c0d00000720507605071450a03016101d290340c03802880f0701020100081012100d07801d41c00450071603280c24070403604000103804203401c0548950b405800100104005001908107501554403120381c401003d103802062100d13541080240700702002116201c11807004042c011a008035a2559040654800481c8842c0000c0449 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 307146888 1250 307145638 307145677
    0xa030615020102070b0108011b080c120702070906080606101b0807150e1b0405060a0803070c060f020703030c0602030a1d0d0201420b0c070501020c060c0a06090305 72
    0xa54103600500030741744102e01040041e6220701d0380501302d50500c0010318207002044001c3d0015070051052680c4440694440341c5003103034609400454140a45450015901c511010b2101c8031040c0108005000e0790b00040c0118681180003ca143d00c1c1a4407060506c03e01d007841e5104440029802c4c3c44036900b0540c86c3e540c1d1442c5183c10b201c0042c4010641d0700180c50602c4084010700b02054405c0b0074056804500d090f0700301001040000e040250200d64440d014ad03a0000e034190040c001783c202a03014119a945803450524044c112105d5006041c04541254905200181d0080c0c0c07640c00075034118000580381d81c0c0710140b100042041c1a181d50b1003049104483e88688030014a0316003111080d4020f2000c481080b5008840ea6a030903025140040d81c141c44207480315528550000503841c0d18551541642d0310f066250540d400191004100c3d00315071001c1c48156010800c0d03002441d400c0d9401480c00580c3c4040540f131b591101401450a92140d10840c03c0c14490401c4c2e030200d821141c3c0c00c4100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 307148138 1250 307146888 307146929
    0xe0f01110f0c04060501031109041119030203180708121e0f07110604061205060d0206120a0c0e130f1506050705010f0b090103020108190510030b1018020a0306 70
    0x48980300035200f8400d5041c00030108555101c0d008101ca004402c181040c01c000500d07003080040c0044000261840d0014000c0d43e0342034148603c81d0501c50581e440040e901c3c140841c4101442405102e541001c2d030141c20100042c9000196450404089800c00358640118010302d014840b041800e20325009004918940301e0301c408402030000300d1180a40380d02000850080c450140900d110303c40100d0000042400c1070242c03900300c0c07503101000070405e004143c420b5001408076008107e000c8001444441007003c14415445401c2d07800d407171410403414044040340020b072000740c4035555000311926200b41005803c43c40e08045000e22040404107000b42d100c0e08000c0c4150440b40080d5910b40c01d2030841104031a00307225a8a428a0103841d143c8143e0840d0019607031402e01806003010780407614141d000481c214800c0301d005009d0080c51132529441d50401c800b007504040c006c0d090300d508400c03041010001c5980300b204103d034611005a100c50170420f094004248075481080181d0116409811 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 307149388 1250 307148138 307148143
    0x13030c060905010f110705010e030a0203062a090607060b1804080c0c0d05100221010306060e060f03070e0c04120503030f0c040b0304030c08071b0918030e0f01110f 72
    0x10b40d035080c2d0303d02600050716802129507160004040b052030700041c81c01d1160703510480b490002c012001c3d007102c542468542c04a0315024013111b4203080f0030a00c621018440d02035996030703480f41c0f501301041400c3c04540350000350b50384225240141903642e01c0800381c00d143c0b14548070b8001440c0b03501c180030091406003840c6260f548041c2e000c680d14000c00986c20b02c1407401c40c950b8082243c100c2c00402503076440d850800001d40c0034000615a52204120a507600500c1c150500e001c0c2d8410680881e19502e005001640322001600c600d20902e020403208640340c070b00042c0c1d20111602107002c816a0b80301d08400c3e820611541e00302e030304200041c0360500180240040194004c1c0120100c00c0c04990b2946087c090f28000c5016911003c8130810201d40424400c0e4800007200d0b0048003882d14180c1e1540c0d804152103e1400110f01001d50002c0802600600784070b00d005140350541940480d00c181d07503004155150300084288038002da420102000d07489030340c1c2c0c2070500703d0940488007a0400707121400d9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 307150638 1250 307149388 307149407
    0x1120c0806040b0919080702040515030601080706030b040b091302010e0d0b0907060c170901030605130504050c04060510200102070309030c0b120c09010311041409010e040206090613030c06 83
    0x80103880342c580d942c1024100603681751070740d44d004045c46040803031030b50800024040143c0440a00c480c07501040741c5541c1c0c10300505009014070390007004503130f103170081c09030030f85982003101c1e07104a180090106884d1a8413201e203600c500c00c0d00c600c05070f8184600c0140c0c2c10710a0ba0024607080009103043c0010042c4000307105010304402d504903041c00b955480200c7d41030401c048000c0038201a03007205843e46401d50086c042402d0141070105040f0740b81d402051400310301034071180903e92a98184000d0000070b000030605005c0a507400c0c0006400d140110340007002004030201017080c0f1000611030601010000720030309032690000d5644220303074180140b15060794001078405020307a205c0010140d02400c111007007040341c0c242d00394081e41e881413a08401e4003d1501d05041c59110b4500c6449204124000c0020304a464102c54000c07052105001180c00140c01c11a100b0b44440c0502c00540c2d10401580c2d6105d50031541e25554880c0d40c21b14114514040d031000f0041028030340f0218096800940301c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 307151888 1250 307150638 307150651
    0x301150618090504020f0603090a050307030c031704111e060301090605120c0a12050c030d11010e12030f0402060c0708011a0d031d0d0b011e080307050601120c0806040b 74
    0x750802500c810441044a8064070025400404078100069505000014550003e140c3d8240c0340310034140e4503440c1c00c580c032100d0214005154441030307108158008548e418049282042c10b6410b14103581c80c201e0801d1241c2e146840740c1d480165272002d4a82c481c883d44000700313001c0c0142d612543e6a4240b0405070009001e100d2260714044c84141d100d40700010a0390340e01c840103141d411000e18140542c0985040e8850070307601030003071035281070341031b2401c020000031100f596841220b1700750740948050845031804c4a602213900204d01c040c48202c902d005807504080c8100305a2243c1d259817000407031522441c5181021400ae88200245024043d0300070340f00044d01c0701801c44840d41620030400f00d040c1150000300814105802800440c030220b0743c410404001402d521060f01050301d500500721001d0344a001c007072840c07846044140302541072800c000c0c45030200440c2000c040b652010785031181401540002c03091000f01d0424411409a2000105002001d0b01d20300c0c10642403554042034101d403036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 307153138 1250 307151888 307151927
    0x3051b160302071208040e040f02030a0b0a1107080d1d1b030c0103051608280504020a06031401090f09080f0a08250507020a1d0901050a1401090b03011506 68
    0x5013000c02d107101c54181648403103600d10b050b060090b56100c0180c00b400c1501c0030001c450724500103072000c1040014150003080c42501600d003455106056615140c0080d149807400d0003a04000380c0030780c054034011030440b00e001c40c0c040d9107100c041015048a142c0580d90b486014560800741e4914101100080d6042e020390704801b002d1801502038800c250340825422981c0174400c81101c0c4140350b82ca40108000070000021030b0740800040a4599502c0742c0c4208940c1c540900007185005840300000304600d06003070001c041c6888102084030f005200703c0d600191103103003030310081c48643d204085035640103054a49840082101468a41001c014540072820324000b04003901c1100c10030130b0820549178500c1c3d4603200307941022100c580203040200d80000001c0d030041400509280a41c5080b1540740380c04001f85031414245080d40c5000d00300c80c80c2c1e140750200e22082c6003d00b07540641034070308411010a25075143c0300442e00610b18040e0100320140c4054002c544158409043c065855a4944 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 307154388 1250 307153138 307153153
    0x14060c280b070203040302010f0c0f080c1608190209071107090f0c090510120e060a0905060c03060915011205190f0203130f020303132c06030a0303051b160302 70
    0x103041c4da8a1081d07000190104540181d6880341603c64407540889030300c6520b1441c6c03821060b1740e4441d0150000c200d1220140c010300c160a103a9079030684542c000700000c9004010402607403a1611040281d504080d004032075840c001399085000c4c40410780c203290440c080b03903003c996801c0c01c103004000080107040b40c0c500342070b001d070b00c403a20500100e0280e1301d00820210030303000304840942d0704260b01d8010801c0c0c00d80704d0825071840c00060107140d11494601c8000b2800107107914000b0305104004040b010042400d00901070645c03202040c00d540140c4058580e940320030005e0041c0c40e048a84050703c0281800e24081246c100d030150039040c1e507001c0c1c3c018240466190b1210210a070f0008480810780240740d000303402c000c1119034551155442c005800c2e00c3c80d000500c9811151080700b6002860200b0301200ca481003d100320300f1307501c002640e0032003c01090910800181d00d83c00c0d44d22025007010f4995011401d031060308101000c0075000c030802d03c2d5035000c0e43d0b96855860b81d440141038002d0f016120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 307155638 1250 307154388 307154401
    0x403120e0306010e09010b0301090606090507092709150b0114041d13050d0c02011b0b0a05040c0f0f030c0801140c0d06030c0e061002030414060c280b 66
    0x45494086403001006402680e081c0360601c2242d1000400c00400d9640b00c06068501e074074284144407010303004110101e191408c05070313540b0540b44060703e000d04004082000704031b802c2c8200d01038656594100e007983c50f41402c14200d01c014014031b90010708018040c60b03440d400114903074005010540300307032540c000110b0500400303851809544600f102c902d01d620300d0300c07404844030425664801d00c1e402c03543c000701c0c0c640d0320f50600e0414030380d81350b074041148a91318109640e0020030300d4141c40784081c08803210f40701903521500c4840000e403280405030380352030101e8100039540400030007400c8401202c141c0d40d651030b8984010305949210960300e0b1440c5d1040850a031106005241c07506903100440303e06500e610b00c9804c030651001c1a518250f0303aa612010000406000c00031006007542e941d0791a190401004020092580940c0348080d54070801081103118102a807a40301000203d0b4140c1d201c60400c14030b5030810000665a11000392103400d0003800c150041504050b05000ea0380000d165900c03403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 307156888 1250 307155638 307155647
    0x210a020705120a03140d060e0919030c0201030f0915060504110316110307210e0406050109060c0c031403030412020a02010507080d0f1a031005010b03040f02180a02040312 75
    0x120702c16501504000c0405011900505000b080c0d40d4190030664a0b090b00102028100c1d0b11540008421006402c2030002001c0d0401c00d4818182c0000d10750b4000c0100c0360f80181c0000c5440c0d0b4020305168a50402e1401c005042e03210a811680084110303100300e00300041f00000b00b04d42c0c00b03030328451440d000007010b81c1c00c000000d991080c8040a4450700d50400c40c0c13819144e0f40748003600981f8a20007000920009440001302208645024503034181203c4441030147c130f03103030044c40d4990140d841e02c0802c1040faa0b05c1229070007141c031142404044182c980c100415940d041d0380024244c0034116851b00c2c00208008021803080e40203444030501d40d0b0f030b0001e00700d0b01c4070082c40b0701a00054003030002101048074407009146207412510700003412a400c800d1041901c2c0711071450200b91648020b0604181014800701c81da20b00604409c019660615150307202c2800040d001a00e14803204000004544500e4203940c40209038255000307903460402c072a2000381d03220340011a0004c81505d034010519004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 307158138 1250 307156888 307156909
    0x503040b060f060c07090504110910180e0a050303010603180506040308061f0e01021e030403110a0b130f0605031e07090f0605031005060a090b0903210a020705 70
    0x40800000192142001c00c0402c00307001c1101980004204041d038542e100030004440100400e10011840e40f40c641030519001c01455040c1307018070031080401c4444406403101205507240c0d21007280c051a00e4006501c020900080310310403901c9451401014010000060f50480e401964240080d0440c0c07003846190382d5108100400aa100350040340000f80562070040d40b200010702048441c281c4c0036070580303480f0050141007001c1000b00740d4041c1ea55078140209142d9150007816544185c03401c048440c1c0c2c84c0308031700c0090a64070401740c0405130707680c5803200a0010100c5d401859101c40c09042611407000c524030429001b29822000003400314020010307240310b808428107004041c403040701c1036403004100030411401c0003040035002c5400704241101c44060714440d625140c50f45841c0d014003520103100d80060f44070310380601032121107660207600e91080c0c03503481a203a82c4500e41c090100749000c40d0350380704131a0f0541c1c07043c44101c00c131b456102901c86100300380e00f190704180daa0414007400650 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 307159388 1250 307158138 307158143
    0xc150f1303020a0326040b09060a02191101020d360f0206090301060e01080a02030c040504051c12060603020715110417030904090308010e1024030e0f060106030606050304 75
    0x1140c860240401c1c01104030002e0100d02c0c203469207400d50440e891800d41c0700c5c200c600710b0b109480802800385007501000310960203803201030118039201590701c82d9410f101c82c9599004c10044040852001410207405071071048054410501c0b09070982c40766a514402c151050414a0031080180d550090642640200e8070342c1212108030070080940034027000c1e034803140d4180d80540d00c8a50028045000f000218024204240903000403046807040505220550001c14812802d110512010900118a100d03650f80c130030001241203207940d20207131926500030000010f2642b0300744001a6003074042d0020300817903105044510003200441030200843d103055010008000040c07005121100394141083c0000c0b42d4181144e0900440c1400101615a20042100081c50001c0100403161010301c400c4c0d08138912184001d500340c10401c1c00030018441d40c412a0715056410100c2040c20b01940c0106210215481601d5144880c004140c0d51201e081c07041d800000d00c2c0400001c0c4039031160003540d001c1c03503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 307160638 1250 307159388 307159393
    0x20d050d0c05120403020601051216050603090a0f0f140d0f050c030408120d0c0504060503060d1406040614061002030405060304020f061303020a060302090f1002030c150f130302 78
    0x503902040c0200501e0105041c0d400d10408100320100d0240c0e0035080340c8120322035030090069604203401c0c041d41c441c1c00801406280c0c003d0070880041510004410706440c802d407801da899680c2e1a403130b00e1030031416000240158001da034444051140141070000301a025080300d52007089203944c500c2da5840c021904400050610380f01000c40c40c4a18002c12f880d004200483e41810f40703643c01e2904000d003d440080c501000025041c0c03004045020754844040c0c0d03414440d00b05407800c81e0160507880f005100510450400608500b00700c03100d2183c4910208103000c48500e8942440e01c040103200c5904034039424200c0300009146840c01c06a00d49112820343d000c1c60806261800b480042e13003000c1d104030b902050b101800c6026444443c041c0c900e00e1007007043e00031303244c0c914018041d1009a5801180426004001c03800b1a80c541c0340d98111205d4003074034040d00c14080401c0484c00e500072010007001c40d01072543d00024030490024468000d41d88a0f40d02d010302d4943c00049410030200050040140c3c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 307161888 1250 307160638 307160647
    0x11150c0a0212010609020c1c0908030406050705030f0f03070908010506060919171b01020307020f09100b0307050a030b030c090c2218180507090207080f0304030e0907020d05 76
    0x5081c110409a024a02e45001081264469003500240d070403541401500ba441940595002c00380c134406a100c40300c080c1819001d182c201100703940c891060380200c10610200060703000421104108503980407541503c00794882d00ca03841d006181e54401d86060000500e030b02e1b008600cbc0001031040c2c0d0300943c0e006000d03d16244075042406070003030506010001d0400c20303010000b03810403002d800443c40c03000103024051a03030340e14a4210038401840035a504551041c0035038001030b107030b101180d02e190030121800740031036840401003e074254081e00101190395020080c04951a0040c5c00341c40040d02d161818440d40030503100b0306560f0200c100d90203078407c108001150801c09100000c041d0301096400c0504240c60140e1145000d01c0d269025441d9070b0301040b81c0c0d041e03440c468450086201c2d1943d00743c022012a980384e841e552302c40e5000e00ba411960004d100800c00580008941360155030102c081c4d2686410709010700080c080c400c81500030400000000c412504c08030380f410300c403191601e50f903092 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 307163138 1250 307161888 307161893
    0x506270a0e0a051207050f0727020d060b0409060e090d0e15030c0324010c0b0604090b04060506030c01170a0b011101050a0f06080705090f07051611150c0a 68
    0x78240365055100640155a1202d01060051103180e480c1410807036402d54805161030440e140441210303260845030000350081c0a40c0c401e000c00300b1090341c5070f6021401c0b000d1081c03d2002c024441e05410101040c544440055018074007000350003140c0511701c08000c40c0b50f96015041e50440200d515504c0b5800c2510072840742805402c11580704000900000d5100c42c0d202c00440099005640d0440120f1001c41000508040d0359000004806c3c400c5503510f1200d02140040c1608007102e0300201840300240020301e17075444507484040c0d2035800c500c083e007840c10142040c034018001522454024000d0b1808440341e5401074000b03156900c07503c0400082982c0d0214000024480d80c0c3c1400d040001c0c0c00c240c03c01c1841d0034010140641700e40c410004070310300801c000104541d62684410b00f19000385000300f06c542c0d0390808142c0d00c08440300c41e03405240c0c0d07031080c01ca4181c802c014010b41c1e03074130300010b1202c00d0140550203034003911b0003a52055152800d0303107007500284c014540403130300c0c560128111000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 307164388 1250 307163138 307163141
    0x60509130513170304050105160f0807030b040c030e1603150c03091505062b08031f03050706030c081005040902120d020c130603030206070c0813090506270a 69
    0x240408126541c076100c100c02d035101c1e4801c4066403c4140444004800e201c103100007882042c2c1c005240005801c0e29290070034014010301c0b0b40345222005d100038200041d0710140a42c000c003503161801001003119503e80701025009045120b4402183d100701035a4554119000460000b90b9400104440381081e581f4420303c0505103c103050740c20151901011070004080010340c411030300c2e406102066070f00d407010a005400c07a640c03403174400c10460340d0008982000316841e445560340c0c2095089940c1c1d9600000f02c10304020f19101c4282c503410b4913070000103004005c5204002d480c1103a90034841d01400c3c200c200c400c08230a6400303550400c0c981004225502d420707441620000c1c8080d01c001040e10000340d00700e0502d81c8244415001d40c00c0100c040b0101d00d000640806000700000003004420f0031a20000e680c0c2000418504c14408060905000d01914400303940340c00c0d44094886100a8407440e111007c0c2205035890382c003510f074040688041c00c500700e400420500310303442c00c03e030195a400c00120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 307165638 1250 307164388 307164391
    0x30709150c05060103080706180b06100207172a03070501050702030c09280e0706031d0115050918121305131b0513060c08121305070605091305 63
    0x2000c0c041c01584010000b4024802c2c0760086000c0d8008640f2172200d030400405541c814100d01d00c50984140c1c2c030708001804013040c0c54200c002601c02004240300000164902a03413600300c4071003a91481c28a4402490004002e00300c01c4003410710b900d00ba20503001251041030355013191a40f50b0072481041c40310354810000303458110300003401c4a1a1600c0304000c07444070f410682c1c0b40300e0b06c1c461110580b80310180c000d1b440301d00e042110388200001407460503429280e001d079004440803d525540c0b841c400c0700c0191210003c41a002c4002c104960000501410341038082c07050714000c4403168009404460b00130719141c000c1d21201d01420140d841251401040d500005082c55200c0f401c1c00041040d07241e1019100c04c1c402d843c0800030701d030f803200d0807030000c40d8270404020010072808010b2908000780420400d4101c6010b070800100c0f1000b14a4041034a0040705145000c0f103d241e801c00083d801c030142c0e55020680240c0980c3d038280c2c1c4641c0100c45904c526446160410340d5001e060310300d44580c8d48000e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 307166888 1250 307165638 307165679
    0x306030d090308121e10030201091d0411030102041503020304021801081f0f020705010603021c1703060f270135010e010207080d0f1509020a0306090e030406090b030709 74
    0x1c0300c0d004001203942c80c4c4117005e5515010340040400c060045580002400307020341459010380a04041d841450140c083e00180300605040c18401480c07010344007501a03802074011140429482181031100500942084a05900c02c0d100c101c64850046442c1c00380700d044e200c041c409455070842c100e0072906506c18140c400f00e0316990720070140c400c03582580301802038948114000b00d8458a103004100741700944d015000ca00e0140325207080001080044145e603440000603e16450b580c4080c006800b10780c100c241c0c0d07500312a1141c3d200c0b908040002280c1503184804405600b2640c8548403108124074000d00030030400e03514907d10f0446204100c00d58986507150700041b0340f50703000b82040360990f00310001c1214032190100310710070500060300803406070740000340c1c08110b41c550001c90f015144649116080070030b540005c58203c80c030710a421010150000042c11300c254030a102d074456403640309100700c100154802d000411215444ca044034000c09055962121700c50605030404540c2e120450403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 307168138 1250 307166888 307166911
    0x5071a03131b080a06050603060601050405100507060f0c020d0c1104091103030a05091c0302060a050a090609200303090f0603131a070e0301020c062202150306030d09030812 76
    0x5102c04000c24880c048040c0070104050f16a000251401d4001e440e40540000e01c00c4d00802c0800503144d0340f000644040f14000c94100c0b049407001c050036582c038031840030094605401c100e8191540203240e041020040390550840e9445111000110340752004054010004c0003d143c1029540c5080d401180641d0b000710b03492602010020300183c03555000484140105c0e00100b031030f070001d00c0e200c0750b00e68400c260070000001120301a50001e44401e801070040310442c0d5185d01103000380380543d0000b00c00e41d83c800707403c00201015040c22078207815035080d510303601c030520143d0b0591818003005840d881800940070f2500b141c4600c00b00419070700700420001403a05102c0c42440802d51413542940003120150024a041c1840b42e0010300c030751803009281d80268010805a0162100000c02d55032000e50f8801100c3c5501141d100c4000e074007500840a0341c81a034a10304180d402800c04020740c0500c804601322552044840b000f90b0f00703c01d041c440074020b0001440704114148103940c8003680159003101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 307169388 1250 307168138 307168163
    0x31f03051605100c0809060903030c100e0a050d142205150702130b1207030f2f010e01090510021f110403030c08210f010e1017010e0a0f05071a0313 65
    0x27103031558002d00110180c42d80f0510040c4d01e0401c1c03c0c407035469200f1090000d001110001d84616075919201c903031823410008600c0100b103005407200d05480d01406500d40c41440d984040c1140f21254144d4002c01d4810100202c0c419003111428080f20403a56024183c0940164445000001006049600794200030901074506041905005807400303144116410900d034443d0b420028503012403403092a0007a86045211440507070880a40c00ea031400910b032500d904000c0c0401210100040d074071075134000c078040d00c80c0c01d130098010a241d4448030800800c00d840c261800c8001c02900c00d0f014202c02540d801300720600100388128a0708002d0f42c01f40c60403c1c40c1c00751007400c28203101110f4031740540d062034410901451b902c800c144a4010040c681025405003443c4000200d402e9442c45441c0c10042d440d82030301001d580039009000c030848200c040e2422402942082980791101340030845550182610200d406008010482c2ca00a040781c0b2460a42d80c41d40300481c0300c000c191900365a034228420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 307170638 1250 307169388 307169407
    0x807031e1406160201050c0414030705040516081b19030e030f07140601140f12010e010510090c05030a02070f0609120215010b0906031f03051605100c080906 69
    0x1d860010070034440103100340d2034111111040d103c80101c1800459042105203c00c108002040e00d0560f9040c0d10100b40d60b4202d10f0000c1d10740b500640c08903400900348402c01811003e202602a41036a45480e0550ba903611400000d0454010002c9000100410700c5142031100704c80c050180007850504002880c250000a042c4c41e54200c20204108090001108020070001d004000c030f6041c085401024154102000071010780c00340100c041c00b642d2000305802c61031352101d282c00d40c1e080e44d5900801c04c82e101d550701c6078084c020456501b107a40c3c00749007001445030b1031791054414825484da107a50035a1100c01c42705000c0d610402c829140c1020342d60074400483d496200c0c9810840c170508407020850300c4041e020f03050804c92410214400c00810040108003442c00442e8002e0f1030442d21319030b503a03035614409101035020a000c2441c0c40c0e914000841044030014a00b21600c1c084c0d03402c00300c00341d40c6a0820545c2e801c0e0b841c40d40d0004443c07425140c0080c0007a00980003a2038028051400e000301d08 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 307171888 1250 307170638 307170653
    0xe03030a0b0d0b2e230405060a03140102072901060507030801061407080a09031502041d0a1401120b15030a060f020d0c0804020a0e040b07050306030705150a02010c0203040807031e 79
    0x1360040307503900e8205c0218480d05080898010b0440000303039030600062800030000b6180380500c0c4000341c0106021048510100030a6045801856000e422801085000d65440144a4180d2607034088004040008a88903000c1d00a5440c00765140d91a250160b0801004030b070055000705034031084241c00e00007100058843c1000d4141c42c070302030f610f0800d403500d1410956429840f071030b85818403920400007071145401e400700c0840c514881200458003522503030b0074140140a200041b14000c04c4150000c40c4d1445580c0000c500c01e0300511a04845440c0c1d1000d1440d2010920f800321fa00d9403040451000048058006440500c0009001410042c4180201040c1d65000307070301d0000186100100b00440c030b4048400c40140003004000c014a00d41580d0f00203a25201034040800c2c4523001c000104030760390401c0038001401d400b610800796403035451440d2905130440c928501c055402d02a003001411700c00816102152074420062580507e5612404080c2320035026807241100030681840100703829 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 307173138 1250 307171888 307171981
    0x1140d06090303020319290d080304150b0306060109290a0f030e01020a020a0312110d050612010902010e060703030b191e0608010e09100e03030a0b0d0b 67
    0x80d40b80584c1d00d1400d1100b02c03000700784160811540b20b1801087d58140440180140b9910750391040e040c200c103504030001200403900c004010604e0310000100700400100400940b83c0903076450303090102007800c104054680c1001c030307141800a40c11020030404444100100d56507009401081044650702a100708440c2c1d22000144012403032409202d440554144952501044010002c41c1070040c0000020b40b90000e641000c0c081118812201002007040d5202c40310005580c80580d54400744200040041c100031100c4a1007030030068103240f500b900600031204d2041c7d0503510103d41d9a184010400ca5400c600c1c8141e04161f0788043c00784260321004000340340d00c4074440c2465540c92a2103070000c3d060640c10842005030804d03007020010b0030740085516040d60354611003469580c0d1540c4559180c1480c80922803030150038040e0350070f003c0310040015400758a0109081c844001820248000c1d109013880080c0f419010380d00040a51441007a020790003034100f0403034643c950500c02d00d204082d22 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 307174388 1250 307173138 307173143
    0x80a0f1b060b03100504050c01050a1106090706030509192909060604060b1201030213180b010807050a08060a0f0e07060518010e031e0c1206010e01090e0601140d0609 73
    0x9540b0308251807440c04000007401c40d009400144030910302035490948882030020002d06109000c03580c0022140548085c05100d10742070100d40c1c1c82d01d07003508480c2d910344d19031146c000403030300c0d00c1c000c1106554042040d19804148110420001d042c90f0359100d100c0100040301c0290906284011104c880603c007003c0c09004c041000341020b082c210f003000201e8a0f2680300c204007480800100b24414518112181101e030112036035207440000040d2a000b6201c0e0144200c580c5003080650b104215141e0506410307580418201d824803500c500a219200ca0f003402240110b502071800075a8030640340d000701c10019001c00c2c000c2181603005c46080c0c038000048d00b0402c080350012607995000c0c041a46094038102d0246020780d60400c1c0900402d4036110710071400307a08164500c0764111000010003009040d24001703000d181d66a0b80700c18105460f0b00080c0180c082c050110b0380001032001d003a00070040c410442c00081d080d03e9103444d6a489541e10710445d015004101c03000131001040040c0702c1c500ea00360 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 307175638 1250 307174388 307174391
    0xc02090a02280f2318120f0d081e0c0706060603020c03270904030c060b090c04060c030e1c06061505121009020a050307030b090403021c020a060f2403080a0f1b06 71
    0x4104030101b10045910410a0446501c000455246070400007122507910030142814200c6032030b40c82c100d0644280800920842c580c2e480203106080e15003000802019000e18002c01ca080c0e203c50040301644a242e03410180b0341d006001020125600404162002003141518803508440c0c1d008182c01c01d0707007180c0036030100e2100b0091505102e103500941c0349498003240c111b0b0440c6003c1e500942c10b03000794041d803401c2208005c1900708242c050a81c42004180040c880141500d034030b06140382003080c00c04221180c6080040003c0c8921624000c2108002591225800c0070707000d40c4d1440c210040105001407504603c0780009108405100802c1450b500d03a40b43c6a80e45440340c400b600f55034110720250b0241c08940300300700c04654003092128902ca910483d00b86c032461106000c07440c082c8110009800549400b103200c0d034a0300164003560080c062a84c1285450151019940d048900c6102c0900600b900304440200c0340c1c400c0a845075040210f007040828510006480403015188920403264503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 307176888 1250 307175638 307175677
    0x609030601061701080601050306012309010806060307140f060901050d09151409100c020c0a0807140a0303050906070606090e010f0614010c0609030c02090a02280f23 73
    0x200020303d03066002d065060003c0001d9451301d0b0200380e90b010140b140d80b41e0b540c0001016601c4101080e5400c4040303500810165065840f1070f07006858840c140d078154443d1240100002e0780c1818840419602400100408080f0b1035602c10700441e54010880760341013100c02c100d00c04041c4454402d2002032400f0700030540a00e000040c0d90001c55040c01840311741e030720b0041c0c108030702c40d03000007407903400c06000786400301c0d00004a4030180d192480c0140000e030f02c0400e041001c510031600180507011a03c5a0a1040591910205124484026000240010718100803807a400d00303007035009181c028820720000407030f0ba645003403802c1101c00c1c030070b0a090b01c0d944841c01070700141d895006da04043d1400b8034041c07001d0170141c40041c081c54250900200219111240403080c5405800c50f00f96854014080030782034500302c02c01034000c0d40074042160680b9a40e2041140c610f4807601c0340d4800c08010340710009201c00894040e40e11201076900030454010f120b1181a1200f00d08001c1c03c0914078240844650 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 307178138 1250 307176888 307176917
    0x80102030403020c0a03150b06040807090f0605180a0207110d0609060c03180f020607120804060c0c02010c0803090a05011506080a140103141203040f020310050108100b060903060106 80
    0x4008804c0c2040d4030401960390280086071400250908151582000050107441007007c03035103c2c001c960040c40180581da0340003800f103001d81c01c484941c685074070382004a6910342c810010a0b110403601031050488280000d503840c00c0550040000b24014480d00380a050020002200c002e1080e00491b416502c84402004200703c40c0950042c101050606001042c004d2140c102410020280905280d00441c2144155128001141c0d4070541202c060030a046400ca0050091207080d90708840c0303946410796684d051446080410030b00d81d81691562003400442e102d914042d0806031900000d80100d204850000f01d0034419501305045003a200c16a06103410300241c034442000340300002c005c1c02c01102d00d4004403040c103400e06495000c603040f030300141c80015013450902c0400c0b034191070810000038801446032860029940f03074402c0b02151510f10541c4102800e46000781328101d1560b00c250082003802e4a01d070010414000054041403d1007011070009140140c2a804500031902950303a1020 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 307179388 1250 307178138 307178143
    0x5010c09231f11030315090703110d0905160f14091905090a0818100c030e10050f1c1d030f090a050d32070b1b0708010203040302 57
    0x1c80004214004000c2a2024045410b080075001120010003007110700403490b070f0040400c840d0319038506085940f28904001c081408a113494000f5110340d0760000000c0c08035210340500c0c4e000c1e0003802c1010781000d034900d0002d1f02038281008111024058120940300d6002c10080c0c0c2c90040510b94400d0b1015031525100c40035000d0507080c814050329550080011100b816184000c80e02d11f030180c002a00d03900c160302d4a08140382c80400502d000c00024088a20f10880e01d1062049036003181c2011040b1803543c0280d5040c030340c290740200441e4604400702075528044804d00324503034803801d00610340741c0d0081990350300b988030300283c400000c1144070105500050b4445d03402d0088050f020b0760021b02c102c000c6190303203001d80031542800d204002031103056500c40742100b5009003030140500c0d92141c0b0519040b03160b007110440410841d035801d01146044201b003000b0391814148100a001f000707050081c03418241d84900800b580d012003a84500c00101070802001000f00801000140c40f410540b038000e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307180638 1250 307179388 307179419
    0x30d0f0e0312101208070b07090803030901020409060b0702090f04020418050f07050a05061206060d0903020a12030b1c08090d0b0405060601020615220f020703031803020a1e05010c09 80
    0x1408142c41881c020005d481041201c07015504001e41001070340d240102258180b0407608908514003020041c00384984054001d81b00b6103038510402d02041d07032140c050300418000c1d1000654440c0b40100807610300c050a10101d600140040c10110310081c1207002c0d144a40850071003100d03564003618011005850621601010f014100c844d400c40e1450080000c10501a10503401948050200443e409a540300d08488441074040414042c90105080c00780d00c803030807038505403070040600750343e14507182c8207100702010444024111540900000da9102d6007107401007084a500341c080004008070b5070b942e041007451030310440b65521240f406103011030a1810142480341958418418001541c020b41c1c0c08804004041e229180e0051506500004401c2c4c2e07404524071980c0703801601c00c00401d194008100907070003900e003402a14142c04000d05c1c04400c04e40041c00503004100200001080320364550b9082c4003924928101007415120182117403010f40712030000c141c0f454410810210010300b610b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307181888 1250 307180638 307180649
    0xc0303040503060403110c10080a0506101407020307090216050d0206070e0405090c040c020d031a0901030803060a15030501060e060c060115050d020c07030201170702030d0f0e031210 80
    0x2503040500e020003083d40d60601402c01018841c03001c3d444001d0050800890000c090014010014000340d8800a803c0720000c3d0b401080c0d05040400140d501d042c040398200324005e0301c1d038074880c0c0b00d001c828a5231a660814101241c0c5409100300000740505a40050580e00d8949030108030808403502d0700e140740c400032664003001c0d90005020000318580206181980f29016500490141d5078080c580d4288000e42c0c15050b8024078024452018503800180303092114a00e403810004040343c0c081d812040460785040c66803244050005100040c001c801958001c01c0103044801e115858240c4840615044203000d0b0000395550010844294031018003c1c4061040d0b900c10701d400020301c00f13107442d100c1c140a02070020412101c000c0c1e40901c2035040740ca5170440000110b4503030440400e85622100c1a11050340000d0172007a01907403c0c0fa1241c007030b5000d105980c009519141c0d90703280d00c1010b0048091816000c558603808201000c80c18401410448400a0320814620301900d01858030035054214 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307183138 1250 307181888 307181893
    0x80a08071b1106090909010609050105030a050a170403020d0b072d0e031018021002030f180612011d16020a020603150d03050406090e1009330302030c03 67
    0x4a0884a2011507640c1d052034014074032211426808001c1003031441400d0595802c4420b40742006003540c0103502c08815034009a00a201590381d42f0101556641c503108003400d240c1064414000042400d603240a810003002140c5007402c0d900d40000d000c80681c0c1e80141c03a4825604100140c0303d6101c5600220605c4aa03014450b8100440b9906562200d9410404c10312900c201c0c507803c2e5030340030400d20468000050040c003049010b0058031840401c01600cc9000c1c3c040b80c0003241c00340340048166150114000303481400d00802403296120002c0c05d28080383c110343d04002e180740c071028000d0081e000e000700080181d60300021a6041c2c89050004001070311250b211400c4004d1607038007023080d04502c2e4040b20303500d44130b4440d4100d00e100742c100c0c0c41e1032990160501e0800010160014003030021120240c690308001d0b07640c0c0c240100300c010212580d6800c040b00b01818412041e0a0b8085500482d9135a59001c4100c1d007400301c540d50711140c9440c510300c074001c0541081181b0701004030040b001e03425000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307184388 1250 307183138 307183157
    0x608010e040c05010309110406090e0c060c032203020d080306120a030522090903032a1b0f0b07022118010809030c010c1206060e0108040b070203040b0304080a0807 72
    0x41c2c00a6419a034001c0c541099203031540081801040410a810100010010011070f0b5079104014010a011005800240111140b20b41640351400c1520f030760a20380c1c0c02646c03501c03a0811814070f900780c50358000b15507030280104c0400580c507850038250420340b0400407181e0701d003010802c0080f440c101e228103144660041c00c007180080d034024103444102e508003d4540648001c5611a04205403d400c03030440545010040001d06502d40c001a4040303100030340404011002801840c05d1200b40e80e80800828248902c8200458500c0d400f810194043d09440121761800d5032401085001600c03858016807201c103c60101c0c02c4420410001e030422140350324501040b165064904128085942d8144800130001542215062084074192400c130b03802000301c640f1640c8081d002100c00121482c41c686030940103e0320701e0040400c4109080140c48401d01030340d5075a0340f090840e40092410303046000c1444001742c2118180c7c0075500551041000603220b1283d01001011884010725984c01c0008800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307185638 1250 307184388 307184393
    0x501020d200c070303050c03211e041a0402010507020316050102100c0905090c040f0f03060501050414041709120c04111c20040905040b0124180b0a0503010608010e04 73
    0xc0e03c00d04499140c185070f40c80b18807841a150840c05071501042131000011240c51604c6141e813452480341040130031520b02c415010b43d0070821540700b124000c02941c0750b80c0d04000c6120f540c41090713034400d2052609500d0700105a002c02c0c10200f055070400d0b42c10841800c00d215a60301404038119404100700204400400c122004205a01920514ac0584c0044020450343c50700d21040740d010b0500b0128582c802c0e551b545590118507024441590601c0c984000483c0900e4240a9091284400c09220780b803070716a625036807075580103807914204862080204096030f0722200f0040003401c1021020700086940d517018442a0381c0c40321002d070b8070442c2c1005841e101134849402900c030710380e050b00005008004032900c5c80c80244540ca9100c4004c0000c0350008410b060750300500c1c402d43c49174a4600c1d090748d8607010460200784150070071a0f8411007460400360746209010300d0708106446206c400d1815920211284640d000e0320007c0005580000184030b1031750840a52801040550840c01e81841c1c6034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307186888 1250 307185638 307185643
    0x80606010512060d020402040b04060801050319110a0314030414040b1f051c0504020102211b0114010303020d08070e150a0216150f02011104050906010c0501020d200c 73
    0x2425201c440b20118008181241c4810107507521140c4d01401c110346d00d98840c1c100a4883e0003c0c4030341400a03116030004681421b002c5000c00408640006200b89089903a07500110400c40c2061690040c028290000c08100603005070031341080901c002d155980e0410f19040301d03560070005064001d03400c020030718070381d40c6600410806400b01426017400c06141a4000c542034881c00760921100644c1400c3e07000402400e41c0400d000714400d808480c0c50158070380010701e02c01d4010b031000000328014000d00b0700d41e200c4000010300e5010340c03c000080c00034103600c3c000e9101100ba0401d0700103920000030082e031150400301050704152a0306180c5514250306000403252440d903010b03400400780104000c81440d0081201c44189150400440c5c00700d40c54034010368882903a50006000951100c641c4400d040c0107200d0070b21004034400c502450941000c0c10300241260242c081070410540e40c8400022500a2010f03043d071080600022035100d840340b8818003104421200030f05520001c10040c040c10100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307188138 1250 307186888 307186897
    0xe01090510080613050a0b010e010c030e06130305060c090901050910050d0c032102010507050a0507111507060f0501090506030316061805011b02060402031915180b010806060105 78
    0x741c034040c070059031810049130802c0c507000c0b48040000c0c101818002001d0040e0451000e80344280d8a2402c40d0034030200442d62550711100103008140321000c40c0020781080002040d02103100344ea40c14402c8ea0300d0f41c89502d0084100d407018200d03000800c107404246064450280144800c441d81040d42c1084a40140c40f282544540f41c81010a003c0c0541040000a024001113800845086005400c0b24402185415051220006520341400580c2103401003040e581e00b0426540c1d5117051001aa0b25080107007140202036074002803191844022012080050825910441c03000c00c0c0d441e0b0460b402001e0701c0060300808422400c4c50104075a5441c000f0940c0c80c15505a454500042c1450501000a0400020641c400d405a02c440d1f014810150425800c0c4200c541903101064140041203841e41030903134000f941a0425810303c98900c8680c80711140c59400b42110451110000f101c62080b1131080c5e0b90002e240002c050001e080c407407428045401000b480c40030341458680000005c20314400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307189388 1250 307188138 307188169
    0x215010b0d0612030e040c03020307021902060d110d060f0e040303050402121212010503010504080a0f0e06070f030807021b041d010e030301050907020705010f031e0906020a0e010905 80
    0x10045007118081d038460300700384010400c2e080010022101c60500818117043c000313001d40203d04200c0c1c6e28008a02c00c0c821a440f681d0558082c101e04003030a902c00c0c00003100c1c0d04061782d01404c2800346440c040200c1c46000000e2120014296582d040c5442440a42d591a4410441030001101c200101c0c518081480c1c0d00561510f00024250307514400203582e0714040c0000c42140c40780748a02c2e4040824980108002c2c0c80400582c5200d030381e01c00c00c046c02d8a004403030050498800307200f480c1e035032406600080da6440c00740c141400600300c000e000c80d085402a01054505e0340c907100c2400c00f41604402c0098014202d44082c10001341580c14400d000e12044100340e0107944c1d50098548940912806000003c6602001f80708000382d8041141d581c0d0002e0107500d1056603444041003c981c00003803410216039040e15051400d0342d0407041070380140700140000100f440100404a5040c0041c81808944c52250b44d0042e218052000010a880050925141400020207040c4003650b990700e4a041c204c034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307190638 1250 307189388 307189409
    0x1006020d030e070e040f1218080c0607080309101401050907020102031005060a020703020a1e05060304030806010c17030f07020d0302271503130b06010e0631060816021501 75
    0x110307076180541200e1b02001c8064002001f103940c2c4c0500300da000482c10030034000100c506280a0710b440085884288030005030380e020400f000540009400d0740041e540c0f000001d401d82c0c3c00e01d08059104021740d52084100a0060f0f1040014000e51600b461681d400421a100071800d500c2c1191480c0640003150160a21900d00421303000c058a2080203104055a400b3700340ca20aa40c0e500a07803400c200d910003140f40081480c4030007045138202402500e2149801d96108150b0351606c04c01902e007081480e10a0b1040f051246002003001500f40045001d0562000f09998600d04007100900344141c00c000202014010014044140c489051130304040d0203055004180541c01000a903d42e03002c00420b4202c08004800c00c040d62805586000c069409070b4694947d41e940e2800442d0704640c10348000c0e60100007407080c041203c01d801c080d070072241040d081980c03031107078440a4000107032450b074400000128010100087c840e0201d203020900060390000b00401413981802b280e030031b5814000c159220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307191888 1250 307190638 307190641
    0x10c08130b0405030f040602030903100b03030a0809120f0a0e0316060815030d05120a0c08160908100213140a06110c0a0603050702013e070b1006020d030e070e 70
    0x50f080c0100c6095620310102517950b41e554101c06901c0350810401c442c0f1a0003903424681d16040107004248040c00c00401952500c0b00c0e240094940b198050201404d900c1a40c0b0b800d03464007107600c010031407517040420050b1580b1031400010a00b91980d49128080c0c0c010340c5801040f900405032440a841e0f150408140030341d608204155071607814080258948160078920306483d8001009003018501d2203841240307036942d00744990a81d40316040c240700081d02800082c96100c542064040c10300103500d00355140307540d108029407a001e05d543c0d55646941d40010308000d5504141c0000c0010541d404204880d070340800001100c8088500c6800107002400322903401c071032001d100a45040f8001459643c91580700c0d80020001c007402c8400b1800b542c42c2c03981d101040010f80d03400000d01e10904042c0c0400c0110540c4010041d141d071a41c0e1081d007a418407424001620045d2030b00d2151000c59041058207180103402440d18445506520506241a4607525400404992402034504c9032071510800d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307193138 1250 307191888 307191893
    0xf090c0512070c0512160f020105070605100504060905190221040b040c0b07050c1c0b0109090228050d0206220501110102130e0705091002030309010c08130b04 70
    0x40c0c451080701c81c608403122000c10407142e0b000111003000a00510403901022142003481c01d6a1142e0006800f440072880d1000e000a28001d00700d550003071041c5020350500201c0d549040a0381d609580c5a10f03499440b220500c0241007603c80c5000810b0200303024000c80c1084007000e60340340c8000c401c80d14481c0c0c0000b0580c9034020000414840c80d00c084045041900d03090030051100c0c0819141220342d0041120001801003119090310245038020002c0d003a495120740401c40c0180c0c40800e061001d46180094802151034088078a00800d44d5290204001507203104010142c5004a03d074005200030720401603e03010700694144c10f469040d82d044071071464a00005045012b00606c0345215200c5281029860000b0b0003c28202c132820380328003c0c00c102644040c1d00341e000c1e00480340600146860704028002e50002c1390b42d0012400d0601c85e250110110100708102a020510809680000203004400409108840a1524910f8110348604040d5101c0180b0036022034080c03d0000000041004d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307194244 1106 307193138 307193147
    0x60f0f0e0315041104020703020703110a0b070f051018140d05070305090f0402130303230301030210030f05070e0310020309030306090c041a0d05060301060f090c 71
    0xc440c1c1922461070306030b0340010b0090341c80803151440030342651030324030003820715a009a004d000c1460841c142885011138000740d441c000c800e03000c82001905462002d580c109903112400c0404c141060911038a492010b04044c04070f1842c001e2518410b15100e845849600d203c0d1a1a031003642420a240f5120181d000e1b0100118000300107400020b4452002030914942c0100a52254024040440d01b02d030840d103404580342d44100c41c00c0c801d040d00400d1607881074882180010a0100215800c840c5000600c4024002c0400c05181d00b1018043d0700501e45030481004100480e10b4450340007055103411044513070080c0282c2c110381d001c03c126030003141c1c402e807e41802980f844d150f04040c00031080e0010f040800c0d5001c08d01011402c4a0300d9244503146c107800d402c080f03807200c8400b810201112005050707075100742c0c03414600b0440800c0d40440481200c0f00b4520001c0c4013404001c041d038 = true := by decide +kernel

theorem cover : BRFrame.Cov 307014388 307194244 := by
  have h0 := BRFrame.cov_init 307014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307014388 ≤ n) (h2 : n < 307194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
