-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2461
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:47:07.435073+00:00
-- url     : https://prove2.me/submissions/fff6a090-707a-426e-bd2a-4e9d391b7123

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442446043 ≤ n < 442625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442447293 1250 442446043 442446077
    0x1401030b031507050903030c0730150f0e0c15031b0702150c011407030507020309040f020c0d09060f030902060904020702150d0c080f100b0c2803 64
    0x1000044440d096040080205051540c040b00c00e81d003c10a820031a150100c01d20102c1e14541c04101c032030003541c0040c0f100303109100100d2421502c201440c14103000d01c0300070700d0301600c41220414008107a101074016207030384110541c0020b04a000c5890081122903a1500b07055180e60900c20b0051082c5d100c6900c4003074015080003a60b008010480003958009030380c2c5542030180c0d11401060f130b070040084480140c2100030700c00034421a4040320020a140c0c10305242031310100806803008043c5404d02c0100f041d0554008140c031612501100c0100d90303698085040340c02441442c151140758003a000a810000d500804070b00e049691070768455401a0840c10110119212244002d44c48402004291074034a4240c002e083d003640004c02580041003042d411741140d520a2908490042d103507501016a01e400c4445507234056a505420340315407600300040241c0742d0142c01002c0d041c0001007620303840c5100810181c0003030b0401600400b0083c10f100d00185032003070081011000119100160560b0130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442448543 1250 442447293 442447301
    0x2c032506080c0c0601051c080a0c1103010e0c04021b0706020609070e0c19020102221d060619091502011e0c090509090c04060b0d060e070c12050c16140103 68
    0x18a040028001e0303a400c2c02c0400002401c1c2c460f51541c2c0c204000b47d02408900c0ca0001043c00e01001d480782111032034140340c00d003150145485418841d900d8420742e94096007001c0fa819080786d204403030059464504802c104020345540c0d032020b94602c40c3d207030007055298002500c01e005801e00411a410243c0e208a5108109002c031801c060740300061155040c00300c0c400c03c02005038a054000503003050b08400003420181018802c00c4416019200208a00c0850b030440206007144100750100303500d801004120309200d200c50000d01e0600201c3d00d201003d2207402d134900034150b4260f00240c030300344920700240030300721142c460580044c0c4801c10840042141c0300781c17148084162075880555181404204403058010120304460140600c01c0f1215a968890302020300703010740300d1540f00d0a0b491850001c8a002d5009480705807225400d0005542d04200f082400c10303481070284103000c2c2c1018007128503002d9080c56140d94841c805070a40c00004c0c8401d000d06a6a52680801c820303184c000044041d6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442449793 1250 442448543 442448557
    0x3010b0a1a07171c06050d0b041502071a0a06060e010f030e010f060807170313120812070302030a2417071203080403020d2c032506080c 60
    0x901c403220850711615200310041d04050b800707080546105811006103201075401102c8140450000d80310b41072140d0b11512a61019200580b4003000c403425541d02c81e050950040e10240880b4202100003011b8106601250411503210100480501711000a584092070945a04940c036041002c042a940d1041e0103500c1c4c0003505940b0340e680d00500e144190003e2404141c0c0b846039540b40c0040a00206203030059030010030703012009055141c1303044180480881840c010403006e80080004500000c0341030740c0607054038040d10180700446207610b000500e520071003044220b401c1600040007209070305903001d540301d028400c0c0d091049504850380c0c400701580450664034203050743d083c1071103500044080e40605d580210121840581c1f2405100e0700a5020b210480002d050301040100300341d81030001c4400e0311254141002d403221601c3e80076201440008046000201d800f40d245440d035401c200d04000849803e500580f00c01c1c0701c41001e4400000d40c0580340108000b840403179480c0d054081100c4039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442451043 1250 442449793 442449809
    0x609030a111207150e031204081c0c020d141218190807060b0d051c0201060803160c080106060e06070503071a310209070c0501020a05030105010806011115130602071103010b0a 77
    0xc540c2c0ca6545040c103d0b0410100c01984908110340030384800c015100d4441d03070324290340040000300e4070376500512403800c9042801102c01e00780407249603038114102003500080e5442c04600e070680170329505454070202061810704d00188080d807009001480004101e114060f01051040c0b9090030240080d2a18103039005010f0703440126100c0c03804a010f007800e103040032144000b049150340c8061080c41d5400241c0c0250701c0b42d91940d8200100508070070000001c10561000707002c080d10300b08000c1d0007014442042805802d0000b0b488080040c203200b10380110303601c21200385ca2064819801038400c2c0045a90000e0b00c0313041d0020000740c0e1800d420311511003800c0038428180d8106c55082c0110818064512428001000056400110b0a0014003403520044d990643c8039072501000411034039010346458140300100312000c2a954021407580807807510300e101241552196020402d0140c04000b020f07101520120384c100403c1a105840e8051040403030090140041820401091041501c58803103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442452293 1250 442451043 442451077
    0xf010902031005120f010b1203030408130915050f030705061c0216050609060709030506071d12031801051603030507021c02010c0807020609030a111207150e03 70
    0x8425411600255030044180164010745540c500c0403030f80880e14031030700741d4803a00017001c03c41d5a03000c00d120f80091004211031480c0c1c604010b920580c0c82c0c3c800548040d000d00300004412141e030440d1003005009050700d440400ca11540102d0b802c50071a0036000316031048220407559819444d00181c80e200390340300105654508004000528600c0c2817074500d941c052034080c0301c820f283c561481d11341040c0740d0091024107003510344000c4440c20010014081d40c14400300d50010310115800249155100180b0304044c00202c6800805d20700f0866005929588440c020101082c41c41c40400640401654a55102107078454440151468040c1c0702112201c80407110211021074425040750b0f401111500640d410281104a803020301c90f91138000c0c5001d0307911261550041c40c0d001c8102a404401c0d032001d00580c0c10000d00d45d80d200d2050394000c004101322007103803c040c0001400b85045500d000c0d4140780c0d9501d0369180c1002d1086440b043e445407249040e0015071849400b00403600d0400c140740c4080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442453543 1250 442452293 442452299
    0xf0402011413050d110d030504030b07030c0c0b060301110c0709050105030d210f0f0509061b0a0324030c1502070806010306090f050106080c031b090708060102102d050f01 75
    0x120554200c40025940305e000400f20500303a483c0ea040c4181c1c030a00a9071456696811414041c08030031014003c202014581042e0a5155610505103a1180d622140032580350f111400007034090241420103407015600081c080d40e403040e001a1050865110440c00d00050782e8860415803220b03c990550700100c0c4818041d1510080c4041d80404005034205d400507150098921200486620744103900d2000e50303403030a01006010400c0f410b5031007068000200078019181800303840c00d010710b02c48541803644481000348034020900c03588441a16020b061010160759003441e1246c0b803968070801c2c141c242d240001c2c0c08050b00c0861441c0503508036100500c140e920359601c181c000c1610b683d0603203c0490001c2c0440004201703008042c02003440c0402001a422a581058100103029060304960108240b016081d500d8518019920040c541040c0360a43c1e0b801c2c0060b410105081d0309000100c3c6032030744100c0300c06600507000b600301101c07110030241e071402900014119401030341c10a042c1c680e500010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442454793 1250 442453543 442453549
    0x80705150304051011070b060603070c080f04031b0f050307030b16050c0d09050301062106050603031c0c12050408160203030919172b05040e0f040201141305 69
    0x7541c00502c01d00440380b50083c0711a120007283c0890204110303002c0001481c1003841007003850207030442c008640141ca181881400070780b030b140018000615026003c074a110f2003207000e5058a00035904040f0a03158400100198031100102e4090000b20b049104404912409d000407200103032036105107825941e8440d64415038500e40c40b0040c0700c0030040c04101003000303a001400460540f04143e06c4200190381040109425140706410038000010840b80b0b2421600184521400342500700100149540f10800464118840c0c242c442403440070034040d0604e1146203074030844c801e80e060360700c841090000024890580f00140c802805036801031045861a0741981c281d030f0320705403005007124a03082d14500440e2000c0038840d403690150038040010019621203400c400001740505001e441c040342020804100c0b20380c4a54081605e83ca000046950349024208550160152080c2460f070392401c011021040102201c0490005014120021040b0184819030b15590348080c1d590b0300741d500b01070034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442456043 1250 442454793 442454797
    0xe0a02160c08010e010f180b04020d02120d08071403070e031c03021b0c0307031b09021206011106010501020601140102010f0c030204081b0d031209050f06070908070515 74
    0x10480c00c0301941580d900018280c81d1660008100180000c10500040c02035582110040c0143c4090a0704242d08290f140c40d0500d648507550ba0b014003212400c1d1284e0010030303070f010302402c4000d400440401440543c4d05000071103c126020990354102e00ba1341cde00100b1601680c1c0e0b01805d403c1c108007407002c83d00c141e004901801c6001d80180c00c5072003101e619034810400055044404d008a9800681010100d00c20f001c85c01075030b6610002010b2a010303550201e9038400e1030b448041c00310f041090320503c0c81ca03802c00c510030050108603015521250849035035501581c090352440d02180420061100c03001d40403c41604844058016200a80c40c2c911002200d280607003135541195a240e4400f110124913105180c581c05003503800503122418640d0381840c001d021b01081c0000c4080c500c40c1c12080d91030036070311140c0550500d00780d000708420b003d000d4003404280345d0041c460701502c0c003034120b4418001745291141c4000d43c0d4191400e0b6030360803072544a0740070780680b940001000031920203900201c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442457293 1250 442456043 442456057
    0x102120609090102120c1801020309091b1b010b0406050141210705070803010b180409060b0a050f03030405040905210304061518200a030e10060e0a02 66
    0xd8a088285d40e40880080400c9035003200c440400f01f0208201031690b080850304c25000c3c0000c40c60400380a0014015240042c07803150744e91100602c02000d645650700fa2400300d00d808102983c3c501000c1c0720740780038108502d5020700852030020005903139880b0b0240f07061500a070341c2c44142d0141e95030301c52101100110910f0364119400c4031790450311a50440040c030180080d504404240c000d014112100d000000d000c0f1020030400303000410200e00120100e90440e640056010740d600c00c0707152000b001c43c12280409070702a00c0e18103444107115a503001054015001c42d010b0043c151103400304510103c03e5001d44da09a8001d10003448030b4201030784400740c0c3c64003540c101c1b1540f168079400d040080d20a41c1c0e44039034240c0301205000800185015400304ae0300b003070740b940e0000da0410003e21400d440849031088000c3c3c4422201c00130004150031f4416074000542a030340c2d59100c4910141c080d008070a000003081c4110140c054040c10107120b684244c9140b6480c032030300342d02d03024010000b9420a070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442458543 1250 442457293 442457311
    0xc0f160305130f0e0a090c1215090501020c060705130b1602030a0c1d07082e0b130902030105010c0f140114070f0f0207091d1009050f0102120609 64
    0x401070740b012100d41420000e10a54030500c803901e04000207041124806402a0f980500308080c120005d241d081b2614140d4580c070300030900383e10040c103080c1c01d036084400c2409180b51030002c1d0310081c4001900144001480c000c00c41ea20340d1903541c0d0854080c4072f0841000b43c411000312060200110060042c807101100a01408808030941c0009040500d05401210780c0506041d08002d02c4403600c52480d01601c5070f00f0840b020389845503003e07003401070047c100c1c0d0b041c44d00201c070246007802052101d90060a115650039007552202c0d50058140c0c4004e0185000c00030240001030310b5072103070088905a60060303681480e83c0741c580e5204840c0d5110b80004a9840340360f0f0614403080c1c00c0074850280140e800f4244400c03a03092840b0050300d020449141c100030040d07445030098403240c0019040c8201d40b024680010315010f542100911078810248480c0e1034040c1250a609030300c45a0081202e0a0003403007500e20944401f52a5800c034450078910304014001400012490b1920b04e0b440e43c0e006442c5c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442459793 1250 442458543 442458547
    0xf0c0918030806240a35010906140d0201050d0e010e0c03031c0507021c02060601030e010c0e09190905061f230109080307061b0f0518030705060c010e01050c0f160305 73
    0x244101b18501d5483c0c4241000c07004100c001d0061000c211104140105041d00c0b04211640c2041d05404005c1c85100e43e0038020080c4200c55021a4450760454601440c07241d410071518101411241c080c2060700503c4a842c4540c130b20210741e0b450040116070f02031031208000000c40a6406112029060041544040d80244d0108001803500302507500929409a4041d140d94540b801c0090120350205000704010780c50100c04102841d0081c02d44d180c402801c848540644e80c4449081800b0320311207490840b070a092944050811000084a42c05066600e0b510500c140c044d01024040100310301c210100300140e00e00401040c615440302000c030201c103151500b04561209000752a562000c034048607540d984e000001d598086900800000130440c4c81c00c2c402034000600010004d0141041c06d002c003406205074030003180c1e0300f04400c10040c200a031105840e0507140640c0c0d8005d20100100300c64a508220024210507190401c5541100348012000d04021691407041e500c18455141213041c8941 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 442461043 1250 442459793 442459817
    0xf060d090302151f0902250c050303120103290408030a14070c0309060806032a09010608040309060f08040605100f0f0501140301120f0c0918030806240a 67
    0x40038000342c0c03113560000061180021900b80200c0d80045a03480880b503184107000340c541e980340440c2d0809041030b01018910604040382003105075411036910541c1e2502c80043d501c0c002c0001c0c6440700b8100c2c4e0156100c4054803043c00b44401510039050340f611018800702c0005400074500d82d003cbc50300040039607000280300080308084805540c0c1500e031800841c026051a8040650102c03d65001d000b030751410801c20b051040c0401d540e071014915100c0001c41110141d0041c9000b0700c810051400010441420381d42c2d40c090290070703850299004d07000600000004214a4001c2c0700030701e030304036459903905c0c02d40c1d455458400080102604142c00ea00310402c00003100786a18140340d0151520b00b401002d40c0d0714120000d0b0140c1030150f83c01c031041ea401c0c00100501041000341c246103942100c0c101d11890075500e0102241d0321503030800d84803030386000d2002e405103046051070240140b09446001143d01d81780c08005e000800030051904c9403a08480d205d0301051100c01910040c0c900341030030410220 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 442462293 1250 442461043 442461073
    0xc03070602040e01180621050c0301050f180a20010c0b1503010e0f0606150c0a030513051210150b040b0a08010e04030e0603060d0204020d05010509060f060d090302 72
    0x200a900a120804014005004405d120303010b62004d00f421800c10070480c1c0c5000310f0003602c001204580441032012203c07140c20706c0010b000500221100a00802c0a842c00c078800d030000c5001510508401800f8555821044200040c4c04001c2ea810216840d10b00140041b440300038400c40c60014100300c150380034400000c034200c1800c1c1c006da242c0303c0741c1e040007990718003071501b1980c0b06102c9940d10f0307001d14000c207003445010480c1a007100c0251900d07100c10101c0c65a8510707a21446100309082c4c42185464018590b011002c0c0851815600c0c114441550f039904000b43c40391200e100d03030165000002c02d00f28490300c0c0c0e408443c800411400c00710703c3c16940c407800b03074040c4c0050b40100340000c00080c489842d0744c0d220368020f015005605aa01e1942080d84004080c440b2240c1b140380070300c200101041d2140e071a50307100324002d9401002035654529050302040540000e01c84c46006011140c0418603e140800b40b040803044094251800c1c0341c040010000548800c1e201038055009200c0d150403194 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 442463543 1250 442462293 442462297
    0x61305030a0303060e0c04050d15110c01060302042a0c1401020f0d0506030609031909090f0f0c02030a0509040207061407080403020601050105090112020a02100c0906021006050906060c03070602 85
    0x40d020780c50000c0d4117803070310140f0703102142c0003403181c4003400c1c0412050103a681d400881d84900364000348461205441d07099881c005004d2404070030134240f804107170348210420540000060781d20a44c0c041c4030007500700c040200b01001c008428124442e0601c40801c0c001d01c951500f00c0b5090066845101040b0f95103141800c90348400950b0318070410020351f4600116250184942001d801d800900c03003071a211030541c3e182e020340c42d101c889514000d10720590543c071490414010340010341040000300501000d0800914810160900b4181440407070f4640c0c82c0084269002082140c8a0500d446241c808000007540049001c07100340e50f0f1805c40601d404200c102071031090a654481144078242410302928110051b401141008030401c4008050790f804402d40f50f00e0017406902584980031110141c0c00d2104103248070070308a141041241c1c1c0151f00c4408401122815003e030390703279004485000e1060300c426006058100c4101c4022403010305001005180070512001074906007070051341c8213400e03a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 442464793 1250 442463543 442463563
    0x2070e090c1c03140f120c07050d030605030613060f05070306051e0d020d0609150f0e0102030105060403080a05210a06080d020c091003151a0a0b0906130503 69
    0x50362101d02421142e05110381d10750505500c01d414200603003100c0c2e500a0002d40c1060181503900c0740070a1503c0021242025a40d94208030519004145084d00300d031b200a400110054415208801c81c3c01103c6001c1d110b214280c40b00540030b04540e984028071400010100a4203c0345a0ba40c0d210504644120b482420b000e4965a85c0101c0d050b441e040411a04080c1d10500000c0415084d41810140d503440410340d070900c0e4161303010f4501d07034400d003040707401030401080180010f056403031240b440b0141a0311100c4140e29441c01080b001e206a8102070803400240070741c5401030702c10041800820440c20103044218070600e0503502d03000c001d000e00d0790300304810701101c800e414050040c00b076941c0c0305003d000301420140300100b28500014a000f5950303240101e5050040c3d01d054081080d00c0c01c6640400f000d181c00090350030306050102d141100500c1038108103468a0100c2c400350300d41d031400d065040100e1b114055181e04004501003006027590020307500700c0a4080f08440020503840a1000281d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 442466043 1250 442464793 442464811
    0xb16020a0506130c0609060f0e060c0102030411041503050604080c030405030a35090f130c0809120715020306190810062702070503070507120c0806010e060d0302070e 73
    0x50f00032441e2100d010000c54001405020200c003040c840c4507070041d1b00301300f0050b0b5890f000c001e460408011800d144070744d80507400079500010410040c0100c44011171842102176408004054055180c1c1c000c84c010750000800c0e0b500581d0114000c101e10a003d45120001c407800d4070302c0d041d50f400003c0e10740090150b00b01c80700c3e0f825500c14180d00801400310407444c112900d4508484450030240c4403140f240c00c944034454407030207442c0aa20748940d1600306200708410410454060100f40103040c07624221843c20680c4200001180d24043d5001500d0362640d00c076a00c1c602e40050301c1040800f030741008150a8014401000c0c4140800441101300020480d200240141d8400b040403441592102d40010300c48996040d25100c084000c0010359118645100c0e005031196001d2070002d040d4421602c024025120f10f490201c0c04500d2100c240d035140d441442d8000302103555004007902e0700c43c2442000c8031521030800140c1c2600b018042d14610314421b00c107840010f80c4804001050100035220780f170f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 442467293 1250 442466043 442466071
    0x1030302010e060705090d15110c0f070602190611040303080103033c031e020a0207091104030210051905091509151e0705030a080604090b16020a0506 66
    0x61603020300c5903508058088024000514000c4806030292142410070390040c40c45450403414011030b0040d100055a1080b402d000b8101c0c005005102a0022919030f0700c00d0007104101c00040c50005540001ca40054015100807403900c008030007502c0031141e090320350980710500340c003827001c0100090000c0d52085e21201c4141d4110f0400420b4030f621503801286a407464818820941d8200302c950b60a14481940c880241c03c400c0d8089000d0002145081c03450044103103550000280c0da005052014125821640f40c1c5907a188540d0544015912028691008020500150030100b07580c2c120044282880b51170080100f043c250240301005883c0001400855400d490703107405104222040d03010034000341061000000600304d100408941889540001a10a8407407405141603001540d80800c0c9500c035586130401c10b8880d030020b800c0100042d40100002c11515007841b034220210b0f048414102540d550080084003e0ba101c200030080d07201c3c005000c400a0300400c6454032404008100781 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 442468543 1250 442467293 442467299
    0x304022107120819030e100e010e010f02070215040609091d060702061f050303040e07141b0106060305010e060d08192d02030f030402040b0a030b191e1e05040b01 71
    0x4880613600004880815003000600c4501000004462014010030400050340083d440095401481d01c0d00c1054130b075500b000482191a0f81a5020b030001d07d000740d0f82251013444140a80d10039103c0d41c09101c001c9202c060041c40100c03140c0d400400b1000b0302c2c3d40c80c540303e4141120060320308102120400016170145040118041d00c80440c0031000b1071410b9680b0049007003a000030780368001c0c1c2c080c120717003610100d00140352680705008403100241c00e58025982d4500c4144030400300540e0f90b404640310740c2071190005086100c0c1c81568100d03081200000095150030b0100151400040401c1e0340303440c414004c22860050300e1104202070b0380d06450b84140103440f151020800e1500750091068560f0218510321219008001c072042c1c1980e183d4040c1d0750380e403144002401410007048007a0410701d21040841000100c01005028042180c80c08212039031322804142540c07031150b074044100d1144510304c0d40710306080c0c00803403994942d001c21030046a03140c8846000c44034101e030140c9513002408010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 442469793 1250 442468543 442468567
    0x303090d0b041704060e040b1906021c1d011b081b01050109110a0f05070c03060b1306150f0c02030109050a120302070f08091807020106051503040221071208 69
    0x607280b89040c0f4001608281ca0040050844210903490038080c41e26950780c61403d986101e842803406205c40e00c0c3c0d0340440d489100084d5920529034129045018000c004004d081c0a05010700e4100b40d800524040b10079450011200d50113407144408940554190150009281001400500544032000000030b21825212400c1d00d2043e40705d10359180c40d01c0c10340f112051803602200d014a92070700741001c1061585c4000c0f01c0341d1055030005021411803081c0401005400e800ca01c02290040f10342043c4d114000b0721600880310b00c3c0c803414015070b0101984002e86ca0044104284039007242c10405036240c000d402103429a0a060001c03160b0350881d09880c0c2c01c10080c08079411502030039240840c100170107039850070b403203000399880034000000110345075000d0b940700e03000003100380b900f5003a003281400d02e000041e010708020300469100f5020000c1c1c4144048084099034882c0d90002c04405080c650b541c180101484001008041406944008240706880c1203140b84258400c04800d41d50307040341500d0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 442471043 1250 442469793 442469813
    0x103031d0d0b040f0201020a0602130603061e06030e1009050a17030f0403140705010c020d11030a140f0702060403030e0a051008150604090c0e10020127020303090d0b04 74
    0x640d10880030081040701148440c40d803198000c0d485403071680a4252400181e01e4100c01c1c840007407a43c1c1c0009803000070030030b540c0c44450844440380c0303003840200e8948564580d18034495844d000c11500b000e0742004004e2103034004030080498202a103040d08031481079042610365901c8103a030f550f0310100f548010094003001d281c50082e1600380352411400c221542000c1c015014101508100d103080c0c800c124160f49008031070f242c0303604c603000700100180f9090107916008000c1c48200031800500c0720000c1c0c4031020044410480480d503da15440c2d05080a0b2307102600103202e40d002e0420f05101c2d05c001078665000610107140240c5402034002000e2040010811094004501607554501c118140700e82103441c0d15000710184144040d42d01d00036000c2a00e03030003507502041c41c003410b29401212940c2c200c5030100c0e0390482030303c011040c03020400b401d0707007a5928082c400c10981000c0200000600f0800c0d14424403902c003c05480c5030011100020b001000302c1041510244110b0041c00308202484403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 442472293 1250 442471043 442471097
    0xc05010c080a03270b060a0504360821100b0703050d0f020d0c020105060405101502010905010213080c04090c0504020c12031e0f13061a09010303 64
    0x600120088403036074030080e8a0291420390b605140c2c44018094a10441459084aa03420002e0007aa00e881070300340001400300c2600c09030301400040d4000316107401c1c00e02800c400c1c5010355140140e84004c40448114039110003006500f8141e800c40c9080001d040d0500a007000800e80410400c0c80660788441103903031b2805022084410540c00c81005410390301c2d820b8400d016018240300d5210320a58120310b014164034003141135940d10028020032803030443c0d80241d514044980c0200919034039071080c40115001602e21401245440104002c5040c0c5030540c0c00c09441c0510011030880138039914a8260780040c0004840c006545000303202031901080410f41c00c541c2190180a1040c4a403030780b2103452524015607014a0300080c41d0401040c0401004010010034901541d892400e41c1f00d0304245644a000c9440304000b60001c00c40c0d208014110304d01408c1018a118840840d0366249001040d44420081c812000c0e01400e40c13060385d0324050785e8029402500d071040010b12140c980f43d21526049 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 442473543 1250 442472293 442472297
    0xf0616021212070e062a01061a0306040e030f03090c280e06190e1f240c051509250b1308240105010c02030a0f03110f06040c0501 57
    0x10040100c4080302e820a260041d080b814200b40c1c910b081c40c08617019100d0090861420705540140c001428044100d8200b468806802000501d403210038481b55031400c0391104100141c1400800e542d481c01d0f03440780761006c8404040f286001c034251104402600100c0c2c039201d06421a14001820b410400c81d240901000496607880035000b076042c1a00820150140311040ca5803e000a4581e4031121012030403050100100d9030401c0d90b92071440c00b0400b00b00d070704129a9800345000c8000d52940480b50003030707416550011100d84a00407510034103d060694010030030004100e140003285091144140486220400301610318040c2c250900d0020480c02c0001a040c000b8012280f03000d8503c0714030140c500b1005619074541d010716280415400a070440209400b4402d07030303601c3d81c2c20350040320919440e968030030807550b0781e80d00c0054413000085203019400d500005081000611010b401254070740c4282404030308178041c084030b0f618148001c1d298600aa001c0800e00050100c54420b400083c0f13030034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 442474793 1250 442473543 442473547
    0x30804030f0c02150307211a01260402030c220b0f0307030b061309030804031103032e0b04061d030304030c0b03041407150809060c1204050304210204201b0f06160212 73
    0x188240154ad540c041103d1603008811008141196024401c510080d0401441c1c200d8124182100b868210340042d01d852400c5d280c14000500c900700790046c540d20391001000707081d0b4285161110700941c0d000600707199010781c2c222402c40c0c8040c1107214448100e4001e070b43d045070300c1c0744c01e240c0030782100304a0031540d001d54410700800c160308606160362580c010041255a050400c420032421a00070580c000f03148407a00800c0120700c0580c07045003402e85405c2040007202500000091585034071603030002a02c0c180f01c89c01c007844132004100095401c80c2c403542a0400e80c0040010440c107140003078024418050f4004031540885601600480c0c001601c0d0000e40680d040c80342c50628030b4412015649428828000014188101070068a004103d000c841950180c1145d0800480c070030b8401d0128401c034504610a012250300c1c841081d20000c0b4210b42510300540c4e07000c8961000700800d0521154820b1154414036443c1c2803000a00641020300c0150003030450740e42c0a405c091441303000010200342 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 442476043 1250 442474793 442474817
    0x1818040803010909060906020d0c0f08041109040503090a080c0a1d071812211b02060f4e0604091e030804030f0c02150307211a01 57
    0x24004072070440301d04450005400342d01e8a0060090184090040c000342e102046c401121280da801440b41100320365030340c0c4406080600d0581c3c100e541500d01a2400b05100440072807420700a0406400a000354120780c10154600000781c00300d100d40e085020300b41c00c0314241e16101d08007058882d024080c4503080c4110784840b03d04e94001180020142c004009060452602060048820101800c462601d0018142150404a2401030446000c803100350400000e22405481510705218103104136400901040380c41e002c0010640100c00c0c0303810038100030400c1050f00101d803407906040511808807103510b040f1040d00005410b0b01070700d1590042d50b601c207410b01c41511101c4c10541c0074100b100c0000e10f0003071900740402e00800540d60088111795101740901410303001241366126602c240d8481c1100c0020000c216240c3c0711052000750003400c4445540340c0d0ba0103e03c00386503c0221460146003091b007440080b026115040e407000d0078250355411411100c0c00d040c0c02045641003c2c2000303216544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 442477293 1250 442476043 442476053
    0x5040608030f121e010b0c060a0e0c090c0d0c02160b0f040905190513020a0f06050a080405010b0904030c0b0f071209020f03030a02070617060d1b050303181804 70
    0x101d0558083c11184080000900a0241044180c1c440401401d0502035603140c40384a841035020001c84200c900ca43c800250120044c0d000340011400420082e00d02042e64070207100c1c94000141022a0309102444451a45c10075072281400c4100140e000b0020b40c4000d24000c100600180c01c0b00b801040c04004a001c04c010840444c2c0c01c440c010b600025840e5642000301e24240c101410015201d41004280b0400103050608600070328022035001e079020f03a90301205007050b00305100701030209000f4030240c940380e805040d21940c07041c00b810010500d103810301c0008130006412070b800c401051403200c66100b4007900c000140d610a200300d03611645410881d801401503445014080c2d40c480d100c0d0140790440d150f84000b190b2110f0040d045a80703e8601e8003001c1d403a030307803d8022140018840c0904035490103000c1c0c2014040c1d5009000000070f000309841d01e803881007900d034207a802c84107658800902510100000c0180c021100c410400c42d414200070454944034004005079202d010b0420710020070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 442478543 1250 442477293 442477297
    0x50a0f0c0918020309061b040f03150b030105101e050325080102130b09040b0310022502060d09020a15030203100e0405100f15030f0204060b070803060d02010c051605040608030f 78
    0x591f54135040006100354940d003251482a0b07007102d5803d0f62600400020802c2e021525040c1e030504e45403e021200a00040c07500300d410441d0011403d01440808201c104035031502c0c00d0342c180700b03117030900101a11a00803c0c031348058028417040d8400c00c020f00312000300b40302d805100604040c0c0000d40c5012001e44400440d613505020b6001004030004140c40195182e6101c150444005400d80381a442c042c1c50050094000d00784002d0310310408010700c0d880c82c1400f8181c00155500504450500000c2c04502c0c00030142d54a0480c0c00c483c1126000c210121043d41e0032a032854142da0140e940c0c644006203100b410143e0340510380e0f588100d410b00c0700041c3e0201e00da2140e100600000250100e80c0a1483c0280c2440c42a440b46801c01c0708012083c88140311060390910300076902880060341e40c0b45d6809842c071860300c0207404104103001203000d40c9000c14086842e10f00501d081d60142c03020362955030030428080c000303085844021208000340d0038980503441c018440305001d54280000c0c09a900c20034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 442479793 1250 442478543 442478551
    0x1170f0a020f130f050403030e01090b1b090901090207022d12010b06130509070504030b0a0c030204050603161403060d03111e030a230409050a0f0c091802030906 71
    0x2c0c81440c26001c42c0351240c94001c045006106004e22603492400710303a130001e010548040c0c0020742003030001e100f01c10050044d140c24503400038214450f5078415a214480e01c414603c461000201000b500e8041c4c2d45a9802902808aa034030059943c2030790b1040140703842d5084c00380740cc1503440703540410304480c03981040c0c00c20315010381c3e9038a414142c5d000700900500f0030410a607404040403561711000c1001410740b00039203100359811002c41d104c0318015074960145100040603003000c800002c0b88444c0c2c9400c13042110410341405402d0984a01c0010f80e150011204200c4c042100c400502c03d03507a01980304608216031340e008524604007480031402c400c3c4159005000d000103e10350f850b074080d0402943e260740002c0c4c0c0705d845071350310391616103502c82d4417207130040001903402e141030a49140254034200c00300c5c4030b40e51241d190a20b841888005401c00425084140d0b50b960f11107440d0300002d000740c080c01c00840e03851035841810300d008403103107080300c0103288512481030003009003000d000507402e504 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 442481043 1250 442479793 442479799
    0xa0b040b0108011701092a08150105010c080409060603051504110f09033c0316060e1e0336010c050a0f0b16030b0f011202120f01170f0a02 61
    0x41300a402603809805034900042403001d000301c0e6110302c201d2001e00b1030341140611200019490b41d031303c006980c45500038142000030301800010005c641c0540781d5110000d01c102841c1e81855500c6a44d01c00b04c075102d51241010036124400c11404504090350491903e50454003000800c01d04c02d000b4180d8019a051030900040c000f5400e4200d03542005900c3d08462581044100030300110a851840d00300f040f2240e290100d200c0d14818000340200035a84003140f41603001031400700b6a00c8460151500c94041843c2c2d014803502000b04c1120039035942c1412000c00c004543d1060401a662070380c4c50081105143c082c902c0e4420b60510f82d00c00b9428071b01500c2403030884000344040c10003508100100760010701d11440488103008001111040074030403248800485000440fa40099081d10004204241e001d200d64004000305d42c0901d0003e140d0807802078005060003400f419810005100b69150308200d00e24400401c020030101403c5194403541001030000d081407400440d83c0c40005c4040284 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 442482293 1250 442481043 442481069
    0x140610150909050603070315020909010806042103060902070c060f020705060d110405030303040302010e0c0904121404050409080403111504060807030b040204061e02030c1902030f010e060a0b040b010801 89
    0x1344680d003c00c014406150011018240003401c60303142002980010100c074000d80c0c0550000510090119500f4480d41e003100c105004001760760049030314480c1001e03820713003410350b22980420301003020b03c05025410710403841065103504190003d807500518001d81c81c21540101403d02c1343c0d0322014140c3d10407444d444008950980070707450440c01030149800140d050320000c002c0000b03043e4150032100d004c04000b400d49e160041081e086c41b410300d404075405000c0c003004441d152401c5e0301c118809400d400040f05c000342085e4481001a0980301130b62030594134035601040030b0061200e81c9a00403414101110a1020030505074018041d5019902c0752009004900c00019840d5000f41c00207500420f008008550312a2541d0028108079500d4001c0c00f46800c040c0d21158811340000100d8101f407150000801500c1c6903083c0c0305a55019407001281c03d4016044110300d0890300b40142801841200041c104600d072110240d000c23142c840d8031b401d104606101e00d0b0700403a60403000860556003510b80b085 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 442483543 1250 442482293 442482301
    0x40c2301180306020304032003030c1c06050603070314090f1c0c081c0c0c1e050307051b010f050f090f010c0212010c140702030c06130314061015090905 67
    0x1001c2400e65a1020f084940004104030405500145052100d903c2c01c1a010f240f02d05055000c0d52400100c40042c1c440804204945102440007084032465205a001254064444006c901c250b0000c0d10580007203511602c0c8007001103020080c1681c0411020f00820000880c3d46c075555a505034845041e4417a00c140301c400b80700c0f5114408445807607030403420340c5d9510680c4c0d4082c00d00240040c00d032442c06919084441c03410520590301058415048046907103940c1c80603025820203580400110f23070700e110401c00d8200090091148142000c2c0903101010b4641c01c02002402c0340584030030030301c1040b0041110303801d408151003e496020b14169407410001890700016120211250300203507010494080140c48800b054003c1a00180560f50308000403d012841c83d01c18022020002d515810a002504903400c12002900c0c1c0001d101e4202d610f802e07543d44422601c503080c003152000070b4000308100a091420041e00c031000300066034203040c422002440041c00400726002d8110b0b13140c0c4900c00b207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 442484793 1250 442483543 442483577
    0xf06050c12040c030b0604180204020310170f210a0819140402100903020a0308030c07020d0f0c0b0f12090102040b0c15010f030f03030c0521040c2301 66
    0x981d036070036034500095032241098140710a001020344811180c613a1144002451428a800b8018581d441c02c5008002d0301015800c10000e904000c141d18525210300800107070030755801710f403c440701d101400540604072022000031700306142103940040c290416903074095140f1001048600c04209458074101680310f140d217943c58610303000a494101070518580c4004200e035038201c58080d07482100c03024051484648181c0d41035400348800f07540055945801c1021800b400000c55010f200307907000740c0c5401e440d940083c815000c0180c05484100d0105d0b614420010b0104400f0042c011002c00d031424a28010300001040c0301d42c484ca811104003c1c400310b9031740142501940c018003501407101751240920500329950f00312102480d40703285501800003800c1c01c4190068401d580d0040d290181c072600c1c84d00e094000d0162100e50004001c01088030051548150307250110307851103a089500642414109201c4400da640c0107000c00600c4546c003078500c2c044000d006840c0039428200039444010402d21 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 442486043 1250 442484793 442484797
    0xc03030f060f06030c0807030501050102190f0b0405160b09060306100e03030f0909010b0a0f051803160527011406040b13060f0f05161103120c15040f06050c 69
    0x1c0484500c0a0140103d81107070540c0141d078060b020b550302c00b285940c950400314182c520a1040c140542c00c03001d482c02041207489190000c150160401e80c01c12a40c9980d201c0003010115801e81d900e801c02150303903d410024a2801008181185100d03043c515241c5c005056807001810b0180700b10010080d426015003e4411003400110050651751903601c40c10800d0115030202074007602c039031043c0d0004038104c00d0300d0040d520341e5417445d50b07106c1e0311114200d4140ca15030b000b181000f4090749200e01d1407041d80c0d4108007414a44503c43c141005240c58402072044a20003902984001100366418508901040c000681120444400d041032600110b000c42d12521840c1c012840814001a5545801c01c5601d0500d080785c0d9079070355100590800d02422200900c0420302c004c000f41c420450312401038085900d0100090244212200700b580713000019103808606180040080030224281710403c0040c405c55030b42c03035041083d00c0040c0ca403070707a01c0c188002405800240225520008100a5403c0b401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 442487293 1250 442486043 442486049
    0x6150614040b18041e0b01110a23031c05130f0b060f03011a010e031f051b0c06040204112104030c140a020306160c0f020118030c1d0103030c03030f06 66
    0x4420003c80c604072901900c80d0240c0006010014144610402294450f9207110044510b03040079249c4005181c0c0e40420710303602c00010184880700703e010703e9143c074402d20007480502c0c05000140c620605008514045e10b2004154030034840304910f260000c0380c2d4116000c2d020560080401c901d9603104800070740c85103004142144c0540c030700076245058403541c0490381081074090f00e1304405080c21004043d80d40a42507400704005c07611603500c0326075941c1d1750001d54010050800c03d44050f03403e05554015604003900e0b09510b5800340041c0b105600b45482113400b5000c429005602d0443e440c200803410b1b020400043c110f110203000050b040c144581002d0081a9021864501900b2000b0107903503a0010704000340d200c0d003d010080399078825081803503101c00c812900e0fa00203060098031003130410406604d0503414019488a689441075103518550041c62142249103a040c0c1440380d03004f2190744100350020004181401440407035080614a201c803980361401080a048420890014001c568 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 442488543 1250 442487293 442487299
    0x1506180506150f0c070503030c0d0e0609120c010801080106050a0e041103120d0b010516020609031f060329040f0c180f0b01170106050a0215010306150614040b18 71
    0x20030b2104900034a030f0014001080c002c003c440100740c88404054a91041c4024441664010341c080f0003441c0c06559450f005402c018030305418034040e0300201c0c9100040140192403504820307403814442d85c1100c0d02a000d082c1da040204690f60801700800c080442600070003a02a015034001703001c121440c0750702c03010090050705031140f0410183d10314040f07411844120100720308084c002d02503540718070706860305c0013031013880c02103501580d8091140302e5205609064041c0640360089100c24a001035078482034807800d100048103441c5040840f05071030441e98002502845040c0e03410445481040f40b90815040400e1413a20405403402e20540d500c00c1d440310800550ba04e100600350b0882d075006000740456048144070710050800111411b061400c0310101c060980b000510202340300d1000381400c50007500483c0d4019070544000d5500308002d0307004464003070300ca07030601040400e2940081d004044904104e102041c4c2e040c2c0c0c0d81c189004500ce1120340c01000300d10300e548024071845000c480103010b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 442489793 1250 442488543 442488547
    0x150807121d010e07031505040203031602010e091f0e09070608060a360516050901020312010f090e0721030c0b0411040513020904142503150618050615 66
    0x810020f60310380000c1d20040c0c454882e0002101d01c8030b002402124441c6074020060f61030001d0b001040030103181d199209030b04002d10007150078040c1c1c41c2c1c07006460040504100ca4180550bc0003600c40f170150042d0403450994240c802072040700100025680c00f903422034200f900d005d0703446501090450039070350b01888810412080c00c0b480c1543d4031400307010030781a00076041410050f615001c41518410f54076440001c1103030303c113105858070540180507840300c148113a0703284c1000d020180c04016000c0c0c00c8402c10410b800001c015003a5644103680341e44601402420742c0130320380f00001100421500301a110b8011451204081520850380321010a521040b0003516040c2400c0a08603104004030f40343c0100c1c42c1c40c010903881c0800d102f8544401c1e60040030040e0780d546968079250300b0070380c00303074001c1191048100411068040c405641e4503a0b54640701210030340d00d03500f02010881070409103c4c1002b482c04609015800001c0c82403040307200880c201149940351407000c210f19800801b245020703042c0c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 442491043 1250 442489793 442489811
    0xb0705090d0618210219051005100803040603020306040b010e010f0f0c08030c0d0c0504210609050109120f0309081215060d020c0f06010518091207030504150807121d01 74
    0x40d0013103030960100507800c07940850b949604003001310103004409011036014400800780040c043e000f040c0e010b8191000d90040642c1e03040d0003803950b0415040000031a03004030400030749060602c80c03c01c03240e02c02d00c0c4c01e0000c101c1460004c0c02c1603030085581c2c41040044508c0c0e44502e0f015800071113a032507028070450340d6485c00e004c00d00250703000608005c04d400d0400407003400340361044040c6c3e819241c40d04848803034400d00c49180c00c8d61045082049424503142c0201e4404038100380f2071000124050382c054401000320312001810180f11005144c01c1c18603110020f40881c40e03400c2500c000306d00340031030507480e034440c0301540c1440c0c07ca001c581d980c40240010b04040080c43d40c0c0103400031565403001c807401c804101e144035031241d009024442d00078241c40040302294000411954102010000795204915442e1a481d0342d94840300c000da0116400090812640584245442c454081450000107600341244020424040e824171200500d4403140400c152040d007a5003411000b40c010001c2194803c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 442492293 1250 442491043 442491083
    0x1e040f050703110f03071809060b0306040602031b031003020f06120108070602013e0d0603030305041109252001201c020f040509130b0705090d0618 65
    0x40c000f80d02a000e03007008500d8181600380018028155074404d030281d000030100d4071141c1e005103031503603095400c03c0d140c0200700c0150710f050281c940103a002c1d140151380e07441c020180348100b401c003907030000480c81c0801c2040342c5004a019900145ca504880703c030b20705c003074501c0025058021164540d0a91200d400001004c1c42c0004000d000c84200d600284030003a030048041c100300c000b44800010a2100c04400c0060f90225014070310104103400c040307030901c0b2140c43e9035821150745800460210740d0300c078240b0041c4945680c11001a0030211021803061800d0050030700c0c00744003142c029071009d68a6004071055401400e00742e940388001840f06622180000e0154082d00c080300c0184505d00040345906104c004510480b06220b494087c003280030071080d89a03070025803140b5070514500b8402d01c4041415910008018010302070f2060701007101d00181401650540c01030324000a015080241070000c0e11900c844109083c2c0104001070b20030090704a0b905006541c48008190100301440c2a020403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 442493543 1250 442492293 442492313
    0x7060f021602040c05120f071110020307030609180f02040b03250801090201170702030d09030e09010801021606050405032206021501120b060d021002071a031e040f050703 75
    0x20b8021502030225403003504040d0b440d403145800d19400da91031740b4005810740700103582d801d03007100711403400d80b5070b0800c4500c0c1c0606004070b60260485803134000082c0710140307a041c018080a0f00c1e0702001048000d500c000302004160414100401c04c50070540168195034844d4004a45050080c0546094150308036040c0e50780040b60090403d892014800424107000500c14984031540c1a103d801c203144c4420210840c82500401d960218030040005018003216402240002c1c0e219858140c248030460081000b010030503009a44103030300c103200c510b544050b0520b01c690050b811100c000303096121030401c02e0031841403a0240784c1510709a000c00c503400b05181145812500741f90b003952640c550341522030005900130704c04c1d07040c00145104001c020542965900d40c0200000300005510300b40c07076020512009803111484c025070020441004850366400c0b003045848007100035240740d0720b4883c6402c401a955403045402d00400316000404002c10b43c034051241c250068203c803a060f81d0b914110b040b0b9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 442494793 1250 442493543 442493587
    0x50705040e071701150e1003121718060c0c010f0504110916020a0605070c0f23010203060d080c10090f031403070815010e0a0e010807080f030a0507060f02 68
    0x114941041852160006100701100300560aa00c60b8a0900c0c06d940000300850280000c2c64802088100000140101c0ca8091416145888408600480720343d0311f190400003c20080b002e441d02c10300744000081c0410b130305c1e5110034131307072181c03030f20313010f000c40c8290041816040c1040e4407803404060009000c01c4072500d50082108460203006a0fa903d004001c8040554141c0790150348044801c07030002c0d5480c0c04c903070740c40501e51420300c031024070a840310f00550009031400d0302c45101030f001c2c2050303a045081d2600c001e2414100298a5810400c009c207000504c19840500078040108440c280c0000610103800c08081102041c00070890700e040c03000030748030f84010490100780c0c04d41480c01071000b800c050340c0c07242590381c03985682503441c20071805841078040045410808000040030341d41c1d440c0301c04c640140c03c980c11b0040031076040c00c01c1c0920301185a0002003595100342d03a5501c00180c0041115030b859201d00e00135465000c03600e0120f02410144030407039441e038008118168183c2c1103129060306 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 442496043 1250 442494793 442494809
    0x8280617060a0c051201030201050319020d0902040b010e01020a02060a02010b0a080f0106051008060d03051b0a0c050307030c03060b0102010213080a060c0305010f060503130f0c030b07020d1b050705040e07 90
    0x303401c02c01c3c3e4103450521070040101400000758004101641c010b40c00365034084034140303044910381c60090b031005c220303404815034261042d03440c000c4d4015401e03d0f208411a51400f8201076090303107000e10020350354049035000203205040000b400080780b8070039040782c0503d80b8042c0a420341c850b00d0b0103140e6210700709a500c40030f0a610340780c1d00141900d44030250255030074141c1c9801c1040e131035620500041c21000c40f030507420b22030108115002d0340d40d81054821410900130180c502e5808501c0d0040c1d0f0381d0034940c0b000d440381e40007400c1130001c01d0150101004407544000005032030024100185c0c068003071808082407525540d040010000c802265800e0964840c0341d08200d404003500055044500a0150018121440105009460040005503000042030f0000c40b504451507079a51441221114101c600900644040003006841da400030381224040c00a05231140c03989000601d000302c26140f44804520003611101400418009400070b00301c00341c41404280e110050b8166650028810095 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 442497293 1250 442496043 442496051
    0x6030613080d0612051c08010f15230c0705060906030f0a0b0a1203080f01240e040203130c09090f110d020d0302030c100603020f091b1305010f08280617060a 69
    0x842e01d4031980d000d134140c94427400c01040d070342d003446800d80c074414820f082482030100700d20b075030501e101d007460403000484290b8080e155034244c0c1500d59410480c196000c140508420b00c0860040d03662201603940c86060381c1c8070307240c041c1d0b10300e25a1409000705501c03c5c0d8100013200342c04a0440748040d000030501d40a915245129140c4a403541c04004092103000740007808254880d00000a10401c0304084032076140216041100000207002c1764816641100e940021f00c05e0501000000400034008028002080100d0b00098994801655a5000040035a02001071008c10713035aa04890342e80711500030f800203596030030070702e0069030305e0303211100c81c2001c1d204c2c40004050031046030050500381c80e4040d00e60b28141d000901441680340016001d840180601041c0e514813000d9000a811005110050800c0c420b1500001410581400500b034081100c07040401c25811629041010090312004508a03007803401d07080500204403c0e08100040b80009003e040c0710400001d809000c0c59048400700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 442498543 1250 442497293 442497343
    0x339010b040b0910062102040b0a03060f0303051806270108060a060221070213020d0b010905061b100606030b13020a0206011403010b090106030f0506030613080d061205 74
    0x10000f150225004950f0308a918802d001c000d00c56011807001005221403800e18004032000401643c0041e0010b00d003044000c134030b001545a05000d20401040c143c2140c00c07600c0e0464800030058407400c1014484045861003d00c26074603030703e04032088010343c485e290710740041c0750b0031000100384442d035414001540700020415515180c50003108460454000b070403141022281c444144c01c8400d408500d0351010b00091015860ba02c00b56014516020f8005030f45002e0407603440103c079507901c4114108100c042c41441b2076142c4400301c894451032171400080003400c0d0403000c3c4c41d103e28a2415841681003403400200241c1540007403000301021030302000300c07041c949c0d4072008034001e86c0030020059002d2001000b10a40c0fa14406a6500c0b01400104240028101160780c804081e404000007a60b5401056400c4c1204e2044540000b4102c0141016040c0700c0d4982030550300c400c10150008900040a081800070381d0f0002009000380c0d683d00c0c0c05e8010034240580c8a00b5480061501600250340362 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 442499793 1250 442498543 442498549
    0x5010507090b0a1206030b0f0a14220c260f010b0109060f020f0303071205130201020d0f1701030305040305060c040317072603100501050301080339010b040b 69
    0x741541c8550b411142040b1110104071013101807902c215000c182e96401c0030010035100c420b568030904402c02000c0c45030030440481011030302c00342e4030300502200c10010310214940803816004a050091303104400303400982050440f01c606903001c0c406e101070307500030406d685040402d0240d401c0c144000b0b8604403a0340e440840d0a13104010701c41400034611710342c10721181c0c0c00707443c0c0905280801c1c0b0446020309240300026147d035000340c40c5400484c0300d44100702c000c4201e5005099215110311084652500e00c2c1d40040d645010021030b035414040c640c084a1000c510900401ca4034954022010303400356501d08010b071059201e40416216409504002a00e20503408111006c5070350101c4d44e501c144000351040240e40d0001b010403240405c40071022070700051341c1c0d03910b15030700801070004039a42d090102c02891284280d50125040c0003003403004100181020007035034a1682101c034605111000b40940a080d092483c0e07600c86951400c1c3da40d20600e210551180c0c3d5580403c0d076080003407070020820 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 442501043 1250 442499793 442499807
    0x108250b030604020708120f16020a02151605150405150c030a09020f040504060b0a1d181f0204030c0b0313120915080a05010608060a1401020c1c05010507 68
    0x941020503420004140700b410554001e042240c02554001d080c007041d50441e00e69144240c4100c081c1841c11010b110203000400351904046c8a180020300855440d680428502010b00d503081200c6500424440560043c2900c00c25015078000300740d40c440002020700d0b01c0d5a0300b040d21306a03071900c140849404038103101c42019000d141e50400746420f5607287c2c1031010240001000491300a89801c07450308541e06c40c1d0003118080e81c480c2d28085150342041303081c4502c00280740d025030140e04186143c00e464000c1d002d021600f00300f1030031994104810041101b8500060404502a19008c0044020240400d94054015280304013071001c2820341d00c00e01d4000c43d0000340c9940c02c0411640d54490005403002c1010f01c000b00480c2465503016036500d200d019420101100e071800b040c3c01004009100b6141e100b000e02520700c5092480082c00c10002040e4524010f00031310035407140580348100280e008100804c8030800003003d500c13540b8088071400540101089045940d5030a10002c13580c2d250244c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 442502293 1250 442501043 442501049
    0x6170319090f0b030603070f0806151f030e0304030c0308030f0109020f03221b0626132109080c040c080604181203020307090801110307110c09010825 66
    0xc061034040e0802e500d07248035504c040d05840d03040c4500300000818050000000c4006c1100101510743d910702040308240101d80031542910983c001e10040440544011240311001f1f45440c0002e040003840030001c1c40c41c4a103800241c0740c41020100003007004000c20055105c3c101300f81d840b0155981c0c1d800044c042e030241450700c0300301a8046c03002800b01c0806400c50300105000c40180e40162055846121074081d03c83c490443d400d41609080c040e2981000313004c044100001c40c0d80c9901801884020786010002d03000010650300d581010301408050603a003100f4801c00344012001c0b40061344058252402446543c00074090070504290618041c4522860359403c0c2e150303247c069540b641008003e01020909209096070302510f1008108034048c7d1503048015030300c0060341c1e0b0404040181c0284007907071143d9443da0412802c180111400c42c01e80703800a405040204c000040c8003010790424004101060b0048002c20000070581030001d039445c031102c0a60901075085054032088504410640 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 442503543 1250 442502293 442502309
    0x304120f080f040308062d030d080105060a0e15030702150a090b07050904090c0902070308010806091f0608060709230108010312020a080307030e070510080a090201030617031909 78
    0x2002030f0109001e4482103520006c01480d00581c0c48200c0c3e0300c103e2070b4050720307520004000440110285070402704094001d110f05402e000b80550b1400d000141c0c10711a01c0069020400210b007a51070607107611900301c0390416900c184680702e00d81090003d50f00c0400d0342c42c2100312207054020076440340c440d11034508006c0d0004410f040a540c0ca00080d6200d030310015006400607a200c4451001c520031142100103002c841d1070242c1da074112810010b25401c41038002541e140c0020050121104001070140c8500414541e21104090b0a042da1030080c0060b5000c840d460003540200002264030415440c2a02c15404690401180610444201c1d140740365036240407803034010048c0046500c020603581c083c02c0b1403045170309482d00fa5460f030490350400d6074a200400e44440512140030300c1448424042c050503030703d01c00441900c2030014181c61001c3c08900300785640b2600c402c15640f00760032050103800d046070f480100aa0b4024034507900d900440b00c0b041909020103101c203041d40b1941080044942c58 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 442504793 1250 442503543 442503571
    0x32307140307080f090c04060b030613060617060f0901090b1815120a050d18060201022a0f06010b1b01050114012006010b070506130b15010909020304120f08 69
    0x94110244c5060140500c011842155156821a600e0f07008120107800d010815035142d00304003051100354017a8040e0350f403100e030a01c601072090548c0000c01d90f5842d010341030580c10350303158080803d102480604006030025040d60010681070120b030800c448081c015600c0418000c03c01e280140c81303034400e840d40000501a0510f026143c0340a0314012610b40054081d96041d1415683d00351426610001c00000b04d5540d02100440396078103010340d002040180000d624100503900f0300320000d02e81e445044401c0c4400e000d426400c01040080240100540d812200c16503100c0c0107075405500021050341c2e91031325005200c00503174018062a4100d070200341039514840402001900d010900040100c40c11142080c140b403426002c00c1528004c00c20040e4a0b40e4800c0c030741c107210f41080c600400c015100c5094000c51800101034950302ca90101c4485548900744640314012100590030744e00456805002106101c10b2140c40c00c20345001c0401034440c030b800786202d001c0a581071101120421462044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 442506043 1250 442504793 442504801
    0x60e0c09150f1c11030709060803040902031e010603050a180b0606210f070f0201021216030e01111207020a050a0201051303150e010c09050303040b090103230714030708 74
    0x10a50008241e02ca00915503a618680c070320038118200c10020007603a010b044078684000900f000d12004003e00904a0207000c107a080c02a6259680704511520940d1940000003400e001d01c28002c0e0482c01d1324104004490f540c0d40c00c03000700902000d948890285180110740d003002005001c0d8544281c3c3e1180390785409541e44d00030080030341c008080c10001801c076080c260115940140c1d01c24414203c1c3d910184d4076040c01c201c01042402c100a464040d684104468424540c40076072050303115200300c68418840a440d9000c50241603a01c0f000201c1d50700b0300201039544600440034140c00c0201e0388031844655a0208100c1e904c4042d520050300c3c90b041a060400507511500c01000b107880c400401000c056541d59907004038061030000082542c2e0b4441159500410a01a6060050640c64200c03c0319080034006504ca1050b40b20f00860841e0015502c5030503406500709410b480c0440f803000d4044840400761a5048604076054000940c20a11140c0000b46c20f00a030f80c05442c44c2e5440c0f410b1542e0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 442507293 1250 442506043 442506049
    0xc08090f16030b0a020714010f1107020d020d0510060b0d0e070b0301030602181f030f0c090603090c0801050718050103050403091214031308071415030a09050a060e0c0915 75
    0x44d2a503c3d00da0b80810a0710041b40801c6d0f645403e015513000009041ca00040c044411207048007070840c1001c9041081c000035a0f1000c3c148004160100d41c003007110b802c2458010724103a032120205000600f40310001035103044030b001801240328025028040d00320400360494440800d4020340c440702c1001e200500200354540d028115405a0180560b054034050300028020600c1800c03182e00030b0310318081e940407250302d4002d016040c081e03c1c8050005411012000e01042081e000d00810176030750310659002d011031550000e000f8100d41000304400d080c075000007017003a080c5800c0f84601c90400080003a2951082c8607a07403081e0b8041e40c0301c6042d2414903501441c2c40405c01c1080d9070008003402c0c5030b40b683c0707010310040040c82d05150810003060b00d0201c1d191700300b0071180d0069105800002c0c4011540c2c441c1e4041488a1113013203203843d0340e961749034070820091003a100050f090744079a94650007000314503030100c1004850700040380c0d0b807900000b0810146107003c5a08c881342c02211000030603541 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 442508543 1250 442507293 442507313
    0x50403051210081617010e03093c090f090604080f1306030f110403050607032316030b090412030b01020c06070501050109060501050304080403110f040c08090f1603 72
    0x4030b03140d4056801c03540e601555840c0c003281c0c100c10614a05213203c10441c10203040000c5045c1c19491000b80292044144400d07200e0065400640c050340d400b00c465005201d0448090702103100211080d6015510007543c1401a02c0c4d8240c103a000c0e415100101d010541c044d004a44158000c8009104954031541e4204054100e9244c1c492012000d0200d11441c0f507190300030ba000303081569000650703490401d03007003020b80f082d4460b0305601c03c1d400c200031b00214402044d655800800f82c1804103050f1401000b049404101d00e40e000e8602250400344102100b0700807001a4510701c1e0740e401e2204100d8042000003144090f03034010704c0d076012018550f03006c9000750403403154014140185c0b0450551800400c106921000c4104d42d0350b550340005005140c504c0c803414010702000e28140c0d01390301e00303039444207a01e02c914000a800003120410510135503030341c0540c00c0ca95034005031060101c0103481c5070281c0301070010750b40e806107030081800302c403400303240000c0100d07081b845414109505803550f01e1302c8a00c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 442509793 1250 442508543 442508551
    0x3010f030303113c16020324040204150b070b0a050a11160c0906030c031505060901030605060f060c010b030d0203090321070f030804030e0409080d0507030902130b030705040504030512 81
    0x20403002c407103c030701c028858809000ca500d41176007400c505401510406050611036040184007034000c0044040ea040c2c03500034030f5400341c2e040d03c00281984072568074441c80000c0f584010f5034600d00080d0752042060000001d0300400038000280000d071101110003080d5070701c103124409200070a0200360f05851003244c807654800e0082c042e412600b6103c00d00780095580c0c6810079550007802c900c0800402005101e07032403c0c030850581c10403041c10600c0000301526010700c0040e0034913807928045146551000560380020600034166555071516040084c0601800c03c0028402e000c0c2403d031000c01c0e4008005ca6042e1540103000e03040303a52400c0d03840549a100e40e00e401298880510040c00017820041d084054a4002c1d1a407100b640303800c0c5002408680311103809401541000c54840008180340180d801c0072441200104d019a6003420440087c1415203010350b0001502c00c01c4908124940c0c056400400198280c03129035854a06000c29214113450040002c0d4003003012660082d8100e0802d600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 442511043 1250 442509793 442509877
    0x30b090403270905160816020c1002010b0409140f1c03020a090302190825150215010f05100c0b06040504020a0308040e01050a05010e0a09110f03010f03030311 70
    0x180d030b440f40000400c0f10300864104660703040300043d1208141d00b03d01e0180d402035a00c0d194084003e41c4a070000e4940204244840c00783e0601d4040c3c00c80c0714003e40158050880180003000b82e0740d401d0611f090524a94480ba4185000d2100e50b6100e0602c0072601100c0c5012500b912022040300980031002944000381240c108880c0d810003000580d103510458080b00150000c691100b030900c03104505205401030405112800d4002c4180110346c0e206e5141d00319603074100035090100c0391010503414000c0e4644104100700c0030300004102118114540819501c06488141418038250720a455071030003040040e0100800c0c000107400307840c2c180c1000d540540b01a000e9290305540356602138090b00150450301c2c40f0141500140481d0030040c6440c0d0041c0000d1a00025416403d00492040c81060195089a980f40d03418903821007402001c07181d03c50600010a0ba0301c1d0303556400003141230f900b400220002410030041300d42d507003040b8040d5585400c609101c1d00710845243c0c10000203800703410810300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 442512293 1250 442511043 442511117
    0xe06070501050a050619120818060d0c080a1103010302060717030f0402040506011716051c0e010b06040f0b0a171305070503060c090105031509010f06030b090403 71
    0x1000031000c2c000e050081c03043e11404030b003a090580400c210550b140010f02c4045140c00d00421114440c4c0c100034140e41c3d000302e0740d9a6101a0100d0040c080b081400038540c0180000421892032785090f40450000340496035a000987c8030b0754030741420313034291035103c80504c0400d20042c0b002d450280010420a48200c001d404003165a10f4240003a4201f01d440b075030011208010001981014050554820400d03e000f500c0072640441c4480184809040c20700000e802507000c03068140601c0031581840035002e01140c2c001c0c46c81c00707244040d000e2040341100700e509103980700d452810060180c2c3c090300c5490b01e400d01c4082c108201c41c481034200a05213000c1007d019245464507841d1032b2810300410088221408c0211700f420003a2034195944c2c481c40c001d501110812007904525019226408000d1811660783d44540641c06c1c6680b40c500c8030715030321035811000001c00d49603680e0000300300e0704140c074180814000c040400018200c115400380c04905540c80e601e00c0c0e107000b11144068101c403583c2d811 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 442513543 1250 442512293 442512307
    0xa020c1302090a1d07051207030f090813031e12210911030139120c020f0610050a0306051e15010e0a0530030c0a030e030115060e06 58
    0x550003402550001010404030020207103981501c149a5610411074203080307241c0980c0b1a265007181c071002301035104155030742042c0c0c00c08240355000006c2c00e503000f03c0d0568844012000480161b0301510088903004013010a20b100060b080003e80881c58001c100340144c404800010340d4940c40307181c5007009143d110a6914046466071258a10b610700031844805000e5002090608480545030703000c1111104d4070900108504144204880c000c40a0700c80042861080c01940c40098052205200c1c45c00e241c00b0201e1141d000a003007050002c401c04480554a03500d110020b09039443c00380e15045003000000f0300100c0d0107500420b81141041910b150408000900102d40000c1501d00040a03c0114000d9006681c0698006600d03003049441d030401394601400507141411a03940741c00c52441c02140135900401601100040300150400e80303580380020904903845608041c01180844c0f00840c02070b6950405129a0503841211812940181c1c208401600c0300004802459801a4104084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 442514793 1250 442513543 442513549
    0x50408070f1406090a030210020f06161b03081f0801020a0e030105150609090403050705070618060314150301062102040506030f070b07030203040905010303050d0609020a020c130209 80
    0xa0001008200941d11090b401c019902d140ea58020b03005070700c603001c02d2103d002ca99440103a4241280d030b0440d1751504171421200141e00307094a18182c650745001c0c03601041100d034003182c882900c54440340d035204192004807145956004120b000507000481038170004240840880422480c5c002c2294000b12240d590407541d800c1e46e0180380124000703689003910840702c0c00c1c240207860300048101d40d8846911440c002140c010b0141120741d6101e508984007040a041c0070783d0458404941080a884e80701c0d40b01c00d030240040500d400c1c1c1e64842c800d1180005011031280c860841415901d00784c02c4000d4403440400d40741d060f030035114076605560341d0000142c07060244140080e440400e00120060b411740780104021200c0043c0454000e03008190720302001c0901181c014140c5296036801754a400c4941001c91541c0510782202c00e49038605800401815040780191a8419140380180150b0b6102c0e16040309a004184004015070b000c05003164151a254180c4400034540601c010f0800d0000000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 442516043 1250 442514793 442514803
    0x307090f030609050d02191704030c0e040c05091306050402010909050907050406090c140a030b13020c060a06082e020d0516020102071a0a090c0e100f030809010f050408 74
    0x41102e0b00c80e940e2800e007013000381c18450243d0700c2c84030340041d143c400300070304050448214030400241654030010b0031801c00b603580000d48020f1600143d180136107545480452103402c4043c0c0c2d00383d400c006801e000007454544811200d2151079207a101d0000100d15075904005004003501c100c0c1032040d10600440c10014078032a0034030505404004103851440c00090208580058100503080c60a085410076420b41101401c84503a5030040348681c3c444001c14120020015204260790100e00c00c1294480d0030341580103401104900403d941c0380f40c17181881300f130895150b44100b40d9170340c101c650752a44000000d02603042d07515851b00400060b08200d10904120f901180c20018410303170b42d8080c81200901864150030301c034091700003180303001c00c503480c0d6100252040542004900c041d5001070107a46940d042241e040e40d101d070707140440079200c0240740c41c456001c5400c840144412840010b00e44240400b00307048079000741c4068944400c3c80300441d0071116240500041c040304200c0000c0803801081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 442517293 1250 442516043 442516049
    0x60903060a0605120613140f03070b01030b061e0105030703181a1003030e150d090308040209090d08060f030a0c0311130608030d09110604090204030b09150c0307090f 73
    0x10005000741494200311804d12050303004806076100004000701c5443c81282d2141840e04009404403101117071401d0341c5000c100c078815080c50301000c0703480000c021400b02c80c181039a2160704c03513103110341c5c60720140070b810b00f0800030210054050840c0c8a4065005200446c0c00c0280c030300d404101c01c5a810007030f10110741445400c884013501410005481d80440c4420b6800800d501c10070307680589541c4000f000c0e0802c01030550304c10303011130020082c00d00c0007074220b036001200220305010300030147c200a0f192040844040c1d000300820000a601e40314003140b012180c0190b130f11500c0326a02c40c0424464542d41c503810954040c4140c2e40b11001144442ca45480150721030240042c000420506008601d06081200c0758203604101041c070200d54007000303850010b118010005507403c040e003081c00400508524958110100040110b03e44081d50018415640100b00015081d143c10102c00c0c1d0380ea002c0003c06e1003d401d40408a074803040c40c0d10045403c400c03146030902c1410b485000d070036400c240c01c3d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 442518543 1250 442517293 442517311
    0x50705040e0a02030c010e031e15041110030b220908190314010f03030c03091e05120703050d1b060c0e09100501080c0f0f0a030618050402060708030606090306 70
    0x421660440c5010001c411004a007880c01e4074202c08100e008c265070742200a50783d440ca070445544100000740400c1424180c0c12055520885c0341801c1c107001c00c500000c0c0640d036004840360102e40081c0c0d0b01a000d5030072b010074017800442c8038000c1c004c06003844080b00780140010760748424811001ca103031100130300000d000c0412000600032941102a044860600c0e00050780ca41c0040100005000d4100c1e600489030035041a120140720340c0b4045450141c035412420001340340c1081125030036200340c00d410a40d1020344142c64042202c03124035994000a10004080340d1000d5010100c00c2e00c180c1810701200100c0301d40042020701d90b43d400003038a5400e00e0300c00001e003481420700f07400d14114030015044180d40900391350b01170402000030810342c40104110a10000024581620464141121284080b41d801c642c0c840c2e085001c02000f50400b403140c0160030344c41c1c082c08541444907100d0980100c0d402000c040c601640380d03541e4040d0341c02c0140350660111041c4203034a403640b424401710348580200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 442519793 1250 442518543 442518553
    0x102070215040f0f1527060906020c041406100c0807060207060506040b01090303030506030304050306010f06020d08090c010c020d0b040f0c2702030411030f07092d09050705040e 78
    0x140c0c0e19401c0c400c20b6200c025001c40002c420405e0003442094002162420b1030040054056440a83c100000e81c00c0d004a000d8558000058441d44c0521440c0a44000350b0070f60b0a80041c9204100030b988080c806200c5100c07100740450520324021000350484c070b140781000201d82c691a126816240c21050042d01e02e240c0000d00d00d010031100e80700e1564041e0040300e08109200303c140000700f035030a071800300809141d5a500410a035560410640c0c006200003400c03982c081d84c444000c0a008041c0d4410324003d4440e40f004085114010700030f491240e415400182180c140400046460b800c0020702682c10403c401007a10106549000f894421409102d0522200146291008042780d0035409552400c110781c051003460b180010010200d40c4103c08090784a803541c0c2082007024041c0d00c0d0707c1e54103100322900e060303104030049850000c48036601c0c801c1101650112603ca416030002c5000c5c80e2009503140808825210b9030320049031076018004075280700b81c842003c10304848410000040c2c0d0b42c42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 442521043 1250 442519793 442519799
    0x15090a0b01090e0d0c1208060402130603140601021c0e0406090e031306020c0312030c0f04030f0b060d1505070e03070f0306050c130e250c03081e010603020903010207021504 76
    0x1044810701800440c070309407074404419141c0001c006902030f0520b0030407079603501199180d80d0300c3d010342f051514440b81c200c02203a07682710090001c02101c0018400713000346100148a0750b00100d4980da00c0e11600100c1071000b2400001111032801943e1151ba00c503a40c1c0e0710210b22075841b480f0301d40414080700c00541d600c0d00c1025241000d880380d64403402c11548610341c000e499440c0801e0340708052032801d080d40e86a0304c44000360001b80c0241c180310480f06e0000310b000018400c2c0c1c071103011841801001e9010707480c0c4640e014002050180d60020b0710040c003002908401001950001d9030144152410070b500c0c0540340002801d20303020740e206000c0a074112000b171043c07009522865401401920038146440d003880c540701c114601901c41c903003d11740440001403000800380454032848095401c2ca9200406100c00a00740c900c3c004020b40c0000c40d0980081c01d00b400111302ca110460041500030080d03881d1280840180d40107903146500741d502805446d005880d08140b80f0400b00c0200c18180d2900d003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 442522293 1250 442521043 442521071
    0x11120103110301060b190903050d181202030c060a0c05121b0c030601090b0109090c050409180221010e150f0705030c0708090103021c0b03070b0c15090a0b0109 70
    0x84003901c1c8a120340d140000402024500394200c4040e42c821004c062002c555038881a103c410042e030010700540550311050f1203c031b5000003403c2d404c05044070314902c4103444504400c07440c40c8800b00250158051040070800c1d10780310010b0f01444407035240c0105208001d0351000c0c1445090034488000e6400460b41d1001c44400707100c0d4092042001d001010b030f144680d00025599401803160209590781c1d042c0c40c0d10036920505140c400b03130003100303403d1243c01880340004000b47c0c424420780e418645401031510080e170200500b000300d5500144880d403211f1101c0501c030b03d44400718100c4440e942d40c400c1708800782c40003440561000302c00c21011005030b16100d50701d804055401080032040100c10010820009440801d483c000707908000c0f61905c031150100180c000b485010003110cc21480a021301e81000981c0c7c0080780c03400d005400303072039500341e40d4540c40300c1741d0044024081c080c0c0c000c1250342c4039104151000d580d000040740122011080540c60310708401100380c0001f8501ca40f2a88200c00900e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 442523543 1250 442522293 442522313
    0x91c0315051e01110a0b04020d08040b0a0905030d0c15050a020c0d021515010507030f090e01030f060b06090a0e04020d060507050d061a121b0c0102070215070206070209040611120103 80
    0x440820051710840b60103903104000c1c2040100002d1003110006a02030502c07207100162005803598988451380ca00818131b02512005c01841110b200e8841c1c4082400321a1260544c00c103c80d07484240110542c060510980180c400100502c0c0180e50a0210005441c0b08214400f00340025401401c0b0054008825190403000248120101294404001c215903401012140c1e000e070149440350724000c07101e204440303034900356000001c0e54505600100a101c0300c40464410940720b500b04008120402e401d0080a00861071780e80d80c0010320000c1001602d0314032040c154054401840218103050b580d640340308031002a18804001900818813800e040402d1065401a25030806030051440d211100242d0074840c1d0041c511415840300082506050280c0503014030700251a005070b00c403610845864000d4006000a0f849a20f00020345240c5d00c807108203c2d510641c01810f003620740f41090b000d01200d0940500210b40950b0f4415100400e40c4090700a4400503044d0901c11081d54510709210741c184d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 442524793 1250 442523543 442523567
    0xb010e0915090609010b0712050c0d0e100e10050c010609020307210504050c0d020f09010b0a090509010305070b0f0f0304110405090c0d020907050405041a0306091c0315051e01 77
    0x95600d44c1c00602042c40d400c402e0703c0701994410f00043c600888450220741030b010754915690640f040c20801c0c001302e500304e52500c070103041c150b50078040100c2014040715001600140349070041200c03045d60100038424001002c10360345880011071031030b030f8074801e40c0101c2e0320844008001900d501080c584c2040000000010390071000b01c01d000b681019258941c4903600a0480361254586002138070464603000414200704c0c0c0020019501581c0d180d00a9105038801985e0a0000711001800f281f1341c944640da01c0e041c1d9030004010540030741402d4410929901180004202c0d12040c0b01040552558a000794400c80c0303d542d40b19209070328a42800b00b0f650020b415503565410041e61020721b03481d1041391081003501211417014a80341d003081514148110b8206507003041c10609500103c201c00559181040703c00e4040b110256179200020340c890250002c045503008444150084040c425048a03020024407070590028980e50000202d000c42c03901480780c20b80000b01c2a2205560300f080503d00c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 442526043 1250 442524793 442524799
    0xf0b030702070803210612060f060a05030a0302120a111c021504032c0d2f060d0c200a05070906050f0108130609140601080109080a030b010e09150906 66
    0x180300b8485003402d01708040d6460100035518507000680b081c0d0761454036480b40d85640d0203583e1075040404c444004402c0c21039900b03010700c0042500144900b0000303282c011268041d800703000441e00311588a20036034800703030381c86003080b1b450440e1419120050000c0603043c024681d6102300004203820213030034101410812403c00402d4010080030a81016400843c120b416841c441b00002c004d203102014a0f8004040d82c0050280104a00b00070005202c119028111914107420a60b21409820351034240210311360094000d2000c0805520715410400c1e284c0d503035040681149501024986151900c211581c04503400140008240082484811702400c40104140560307405c09001c01c076298500d81c10a81000364480000d14007000c8000704000c9590b1015081c042c5054a05203a541c5141d4001d804509001d40000001c151005103e0b000000d0350002c0041d08090301c8046c20340041c50f410300a40d0600850105e94440c80c1d40c0c0480040c490100440c007441c01c40964020310090a40007003030940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 442527293 1250 442526043 442526047
    0x203010e0f0105160f030b03250914010302030d0c170f04060815100f0507140a12020c130c20031e1c0915060b03060909030901080f0a060f0b030702070803 68
    0x4a5183e004145043d00c40186c200401c07411200e00100303180200300d8a440889000c00100750011000c01400f22046500e03c0500340b10345c180041000703c10140a100003035056004d16a94101240900502c0704802e014242c1003400c490800301107000ca80c08507007030020b80c3c640040d0500ca21a0001d4030302da04441c08500980488040c03201051903564541880c1c2e040c054201003080740d9074800c1d001c40d40010fa0041085880004100e4040d544004150040310442e4001d900391909510004080388031520007411919014484900e010061050f50801c4040102c40704604001441d410503c0e020480d01400031950b5070b41d001c2c0442c103524541c0b41113024620b810006110380b1800002014191010034400080807000c61810540a00c40c02c41c500e0390980c181b0200281600401e0041c0d8840e030402e44e0507038040c0d5220003d2645030b2081d140e01303e011030510000b15420111200f03046034800f13100700c000a40561640d65101e0805074951040725010070000800c196282c0c1482008014411080198 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442528543 1250 442527293 442527331
    0x1060804020f060d0b040f0e0120031308070206030f060f035109070b0301051f020c1903121713020409141509031806090d0203010e0f0105 61
    0x3500c820b0362241141c1c071440e80800d110201914a030310408060400030810000d46144552410240186109104640d40b8280703035017500896200030010b0510100c43e040f0b140d070380c030b010300900a01c0d0080e4050b070f82c00e8000d000e0302005031102401103001d20300789031441c403d41c90160204040380e030200c07081c02d0080e0480c8890040c81c0300350300314841202d0300f25500f244001c001c0e4203014500d9140c071000c480340d10701603000c000c80340f40d80042d40754003d035540002c6d1441d0b562034031502c0059120a2203665000041e003050b480000004e0000c034501134406206444400004a0000d40c1c1c00409164007000702801103010010040361440d032481c860310900344100e200d10a00c0c60340703808007001050401c9290b00f02c01200704640da10392104000075031000b21b10084001100440b69a81c1110580804d00c0c100c140108040520002c10b03101003c12855400d4241d00290b0244003668200c01020380c3c011030b2600e01c060050750203005815100e8840c00062008490012000303007510703000b41072000303640020041030f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 442529793 1250 442528543 442528549
    0x30a0f0e120304020f0a030b04050c0a0302060412020112020f13080c01051615050103030503010509090f030f090f0a0308031b0c1c0c0b160e010810090506060708070f0b0106080402 79
    0x1070394044030501580307460341e03520b0000c40d0003008241941d55100c540200040104080b034030344140254011400c0304d034010001e4050214004d1107004c0650710440a21081012051518084441c2c61062510504010f1030180344002d0380c0101007403040e81d100205150310404540c9030210010300d01c031001008007000c1400043c03d075220740780c50b02c118207110f807000405000d46508509150400148100429a5030303080c004d01030b400c203001d420721803046140401c10280740003038507800214540020b14505110350b0244081136000b503507110740200212408400c10349e24130303501c00001c5000788601541c07840c0000c40c03401c414112640c00608420184048101d980b000901503aa1a40026104d4030360582000181da610600306e00080030000c0440401401c0030012100080315029034455685180b02c010042d80c455400b107030640303080c100801e0104120b05075a04101c2d00901e020740701d9458805541c82d400040c5e4403548003914141c80e1058101c0400121207441801001680390440c16403c1039400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 442531043 1250 442529793 442529803
    0x905060f2b2d090302031c150509091203060f1206090d05040b030103030c060902040504050d080105011d300c130905101d010c170a0204121b0e040602030a0f0e 70
    0x2200b103243d03a1143e02d0801c050003002103802400002c028500c0c0b4074100b800c240040c00e040130b88240c0d2000880d01c00101170078181c0c05103000b1583c0d50003401417120305001d0220f0503000148056484008082131403044d0f2202c02d01e04542d54503c2c8080c100f03d05c1c02955403481e10f1020411041082004c1004204481c41c51061302d040d20740c107192148500d255810400090701196501a41c400d1a000601040150000e4443c000902ca6201c0481c1c503a81c2e10015185a0398190042000c070340d10901a01480ca4030f9200c1810002207681c20f100d5044e0280c4e9001c08003030010003907403101c0d40304a034640345915001d42d02e801881000030007880b0710312081d03031803c0e20740030a03000da40708591716040c0f110280e42101e9100039002c1c0c42080208400406041c000b08500c01e0341c07140221040e41d52010820380020340c001c80d402e4488840161400008903912454400c101500030123448034150004a14440d00e80e03111400385006039005620b909120348103104441104040d803c010f071511550060000d03010038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 442532293 1250 442531043 442531121
    0x10c081003060b030a1502070311121209030408060c040f05031207060203060a080319110a030f1b0b0109060302010e01020105090738070507060903030905060f2b 71
    0x3801042d85100c0e00e004c20318003104250028041e0305400008524020194064009a07010b6a613019061000c5c4810300e455614808006040c10340800c6000c0c810f0b000c041649421010f4841241e2505540b00451410300c0d0040d21403640845000404101d4503401c044800b02600c6e00f01c0c09008002a001070850780e61089400041c526a0080300003103071907880b00c10880003081c010f81aa6a87c0000c00152125403410b140440c011422a105d020401d490005003028841e515496040030000340361410b13184000c03402503409880c076400000400264101c907120f40240702124000c2162821440054901802d000a07581160f01d0801049100c60b40018081c007240e980c415010521190106800307002c0c04281040003c0810903110000b403407483d03c0003020014050410340e1711071901c8020403501251188030160000c2d0a0b030400717002c2c0b840c0010081c81c0b846c520304509480c001030403568a02c2c280130544110407079811525108903070b00d0b0500658055503e100100c24403a01581c5c14085948541c01c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 442533543 1250 442532293 442532303
    0x90307140c0307030605011a07020d020105160c06170906040507051504030515040c0b040b1c1d0c0126190b2e08070c0303150b0a11010c081003 63
    0x400d030044202414001c5007024103001c0d0590741c10035113906049001d80b4080c46501ca107803a00d0340582120610b060143c8100950047c20150254216001107409810080c00a81070130348174100000090005102c140090800b91100c00c3c0b42c60f54107000011600000307202c2c41d82508000104400150045000d800343ca00465504040054104138108507002d150402811480b0b0200d0660700d80d10401c000358810b0380314420492865444a01e04210341c001c62088515454050054106810309810942200c6040890000d9030310202c49203d2001802d00390201e8143e04203c1081c4003a507402400c0e110310303500c04000ca440b0792604070010001400001c000c02e0803140903281c3c011100c0c1030390b0011607041034010880006019541d0400c5c88404180c200910141d030101e42c4560041e002d114081d1007611541c40f094006000f6031001e03000740c0005060140c03408440d0402041080e0450b018007103440c51540c411100341c840c1682c107421a4418184607080c01843c20820140700c4446e1074006c2503030740c45 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 442534793 1250 442533543 442533563
    0x12040e0106030b1008160216090b0a080c0d0b15130b030c060a0e0603100312020601061101140a090204090602180103050a09020f0114040b070f03020c0a03031b020a03021026090307 79
    0x501b4007241000c0a44410070040000d000b0f00040c0c5d90f80c16000300032604001c0740c08000d119a203c02881c0d490004505a40d088034805034000302151030b808545511241e14140d01401070350007400111101030084090587c81d03070f03505501c45907003020445030718809000d8a1030340c130780b4501741c0000e060500b400280790b04c076a40c00400a105511070b08003010055600a202c1c1040c80040b074000ba495940c24011031000460004102c9071402050141d00a40c00700540c6030365007a19421000300c060000003406a80090300e0380e1554000903218030061041d07000700ca0030030400c281c051000405072076000e000349580600b80b806175009640d07034000c007214880c401d0034a08072203200f070310f0851458003c9501c580039000300442c0400030300c44100d20440c1068441e030f003661800c00e091401c010410a140c000500050030141c0d904030f8403002c406840300c800e8001042000f501d030f6240c0c0000c0f03040c1e003250050310000f48a040e1200f0100307200702c00c0f0209071044864100a61621900c055a60b004101016015004d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 442536043 1250 442534793 442534831
    0x71b080309040c02010207080406020a03110102040b0901140c0d03050a060503071505221508010b0c3003011805010506270a080d0804050f07030c09090512040e0106030b1008 76
    0x354110340401d6886051140c9481c1d2b034220194507604598005c0c1c3c0481c01c400440c400d5201c040c421103041d078050071000d6040c10500001110400c1c0f5080705c0c01c2034020200a44d02000c1810405180a0146560041207a2805807406820350f0314542c400c070300a50169505001404c86c80380500400714851414a8071900b4112a49480041001011349400001440489c035101c0d8808c01880302e00341074440d222542d90700c074401501445508410041600900b60304006a00c000b40c10400d64459254040480c10203082c600345994000ea200e0b1800b03030a0ba1001031129440d80c00350300d00512040342c10500300300c50820400c03142e40142d9074550300700c507620900e5250f40d50780c50800005400c504007100c155144800002d0007414058030151400e225027001903443c40000204802500c3e40588100809450640264003034102c441c000c44281c0514030014240d103400308054001811995030181555150030406411200345209442c0510724500d00c0e4034821b6040001c80d034000103940c05001242c0300e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 442537293 1250 442536043 442536047
    0xb06100f080a020f1207170c0a021b030708010609020306100e0108150409060911040e061302040504060605030a0309031106070209062202161709030d0f0c0215071b080309040c 77
    0x125482d4001c517829040024001d80c07e60108240c015000e514141c540140ca03500c4001d40c89004106885005901002660520940c0302c44507084d003148c05401c13036107800d407140750315429102c88e40c0103c2c400c0ca030701000300041440c8c50301000103a0522402d11180040030103000030812503009000740c03414244000c8803015516030380d00c4481c0542e000072003002620303483d01d00b4589800705401024030940c00c091700300507002c02c041503240c0114801d101c0c5201c4403240b68203200c00f805004000307490f00c6540300800941514103100050840d8440d50324404001c1c11843c040c80d144064102682c09040c092001c0170068491200300380d0400801c840b480001014004e1010284030101c00c0c12290a0021132403001c0d106004020441e80c80c81460005002008142c0b1101c450054105540d41540284401d04629010f182150244e0895240c1030395480f03125004103141c541c0c07009154407441400903a0400b449482060041c521604c0c280f00d4950301d15000300c0e01c0d44c0340100500944600c0d9a0584420254 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 442538543 1250 442537293 442537297
    0x40b0a050c0705030a030801050414010e0a091a1005031204060c021c0204060902090a06030513030302070f05071508090307020d1e021c0b0108030f031b040e040b06100f080a020f 78
    0x3103401411101c90417514500100500001c2c0308030390003241403107c0501085c00c00f52000c0ccc182c0e54840d11080e0301d03541d400c2c03841700074060100301a03401c8000c075640d107880401894441c40c80b514400c01842d07541440c0030140751515401507411260b00741c0a00052150b0b65000384d400c0c2e001b0f0b80484092211a08101c1100000040d801d002540145829000204400b00da0050040750b241210010f113401c1d41c480040d000e40b0021036051303091a100e420310070b001074020341c080e1114a0103100c014034003003c00c0e80e445141595640003003000c0803650104a481950001400303600040c2030002e94104101940804d55040c4001c4000f4450462612500b80c0c4484c1c0c0130707880143c01d800803e01403402000050f00346002c07a0004040c0c1d4004032450020a610500204682d00c00e001e1480d103d10395030b19030240b101400c14071400404201c1040100042d140b10340b4010360b014038015420705000c4c5c1014000c00000200700c0c1c640105012610203007400007074000389601d51146010002503a1070000450702c201074 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442539793 1250 442538543 442538549
    0x2090a021b010603031b03050706020c01020f030702030316031109010c060f020d0209040e0613240c02010b010f0207050105071403130f0306061a0901050703021006060c02030c0402040b0a050c07 85
    0x38004030110708808440541182c411240240c8510820071541c0007903000300001140c0180c003040c41040540002100d07a4000d04580c008400014281041341c1211411380d8030985513000143e1003c4144226880c5904c1d02c018011520308003004415131000183c03542d4060300800a041c4201c0552410910442d03811509081c04072030800c6540b80c041802202c0250420f5800c0c03809585400c3c20000e0304440041c5190145068035082407501d20959a0040c0482500c0060b06c40481c40c50441e125280c40e038041c4c514a80207640000c80c0c0e8024910004100d05e101c2aaa0030441d40008401c00060760081c080b100d40c140c020b501754403400b035030244003440c600c9103440c00201100105400146c9000110308041501e03c60141840701a0340d0f01400c215203400e410401500e90010000d45509602450003005454032078010340f1106000412500e08442c4217512600c0403a5102021604500c1c00703005a1402c20313801c84045040c0340c20200700e03140c68000c80d078071081032000000c0c140307603141030400642c401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442541043 1250 442539793 442539817
    0x204091406071e090506130e090718060506041703071a150409031d0d08030c03070212040308040e0a090c03050f01060e090c0418051f110702090f13080f0702090c03040b0402090a02 79
    0x440e007049e802c02959110148601505000312407010290384195003c1c0b541201d00082c512801c00c0c0c00c10000301c0e140c840d20040d0301c80901c03082080c403002603181049003401c14854600e042d01ca2420b9041000c43c01c0012460301d06c22441c201d40c040000b42c03c031020b143d40a443c024040a82c1b8044c02c0070500303070304003554080e16090021041005a038034450046200b403815600f40d07a011082c806082480b4016808002c010200500c0240320202c8400b40080e481445070303e02180c4144646c548503c90384013500181c2d125045140705102d030309424046d2000910b070241000c2c40d5454611041a04e460140d06551b10694943c240e810244a14114605507030b82c100040e110403802d8032510076400160007540f0005641440b10346a02c0c090311105440301c050300a4109401c0355101e18a110707202200600300720242c0d0540c0f41c81d80100f040d10010349400f080c2101081c0d0b039048140108960900c0081441040036401c0003003200107005041c50329041a03054a194070381c0d4503850000c6000c1c1c0203002c60048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442542293 1250 442541043 442541069
    0x50607020a062a1428060c05040504020c0f06130c050f060903060c030106080c0403020d120908031305090609010b07060e100c080f070503070203160204091406071e09050613 76
    0x610a10940b004c02e9075803214101c5d08030a0852869900c03241408034004c00c1d003542100c000d00810320940181000c41740d0340c13500038134164590b00000d0898001a030340c0070450f4070035070407102800307020041d850308580f2900c00310703a41c010190f075401000101e0b0b0040d0303805000417902d8400c0d00c0e16242d080d1071340861700a0030b640d400c0c036040c5e10409040c0c00c01d100e0300c00091302a6020a40c4410301000725429250090048034140000c0e8a801d0119114a200d9404001001c0f100007810501440523208a0000708401d41c4094030b0141040060013002d8095440307a00c2e25001080044645011124015400800440d11181d480012800c0404c00400e2a8215040140d501c0c0400d0740000c40c140b00708003c20182440e41c0340c241d0100d62600046640d600540e008000381c115801c8480403040c1850300c014404a40d00d02580c0e61420021609880d42c0800e51107081801a0a2f0300302c24000f1107003c501d5155145880c04200060290388544500e9005520000305a050700d031040c903020020b0a410904c400d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442543543 1250 442542293 442542377
    0x306080d1107051c17040608060108070c080d06030c17031b0309040f050108010e0a05030406030b13020708190c08030a050612010c020726060106260a0510050607020a06 74
    0x302a903d10101d04a4580c81e10003041c030b00b110415000d880a1f04d242c0d59035140983c4d50200107449481e0040e0040c000e100d50b83d06200002240d00d0005c01d446400c4035408610700380346151090845c1207642081c820ba0010400342012010008245c9401c480015280101f40812282c8281584038035100d80760854145500005190400d03041103048510007002006030070800e0000a441d41500b1900610341d4104000030000703148650001d1100450003841c520380b001060365408100d902c4100e0413500040c010605509101c5003c0d40170702c020b0f407a400c12418004c49580c414200e844000c01d144007995071580412080d40301c0400f0308410340910b200812540b41c64600c043c1d44c0d0740c102d1084608840310650884200d14a68071825000c20300f800042000b1390800e4001c0d60620404120920714034810400c45450854020381d03203008200c4800c000886e400c0244210072090030a80003940210400c00c2118016220740c0301d000b0803201c9603e4007000e0000400c01c0c13861440f030119010b0912604000f400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442544793 1250 442543543 442543579
    0x2303041a0c071707020a09050622091103060403020307080d06050301021308120702060301050d0203010b0d06060f0f030b061905031212060d0f1e0c0605190306080d110705 75
    0xd00c80c09015414110b0f5150060320720885a1140b01c40003500b21903800c9041065001e5904010741001e0b00600076040b205aa1541c3c030106d595607403065440c1501c42660708144501a50b809800d440b0070303000f501891510340c40184d940e110315080141170010018115201c0d00d400c4d402040a030200a0007955201c0c1c0001c0200032a4009019000c5180941e032891201ea09241049515003a4007400c418156880c20b410030942106c1702c0c40990309035480345010415075a4078011000c08074400c010000b01c0c030f41010748181521815401c1340b40e1617850104148041000140c1c40c90380841e003196603d880c111400e040e046902d5066001d25054490203001d00d800300040c50283c18440300c04c0c6980c40d0103071f1743e100c200b015080c1c040001030601442190004003003902c0705000130414403080c00d0040c0c3d04065544548995245500110000d0030110b52040d080142c1c11010000544625051010b0303410015070070b844003141e205880510025070502c100c00941480020001c040c0105140ca110f9011408 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442546043 1250 442544793 442544797
    0x8070221060f15030d140f0310030605060108041a180601230a060c170c0307030804031715010e0a03080406020102070515041101051b01060305010209010f2303041a0c 73
    0x6031a080b442400005902c0525800c541100c520740240106601d68000d101039500c003c4518038000310b881c3c01c00480700c1e0304030543d00560092440461a209040c614103095044803800f4112030704004110b014400816403014500c9100281c0503015500c070340300c852405c01041c0342c14110507840d000312400043d00c51410055000403e00040c00c0c0d5481018880401c07905150754040c2c2c0020607942000340011520600b03900c50b00004082c80c60307103000120244103155821010f000c9001900301c508000825900614051400c802440344503914202000c0e241c03809405648600d040050361105214255580803510006640100c010350303540c1c1e100c0d480207000c1c1d4440d101c2910644a100a01e4500d2150070f09660302c2140c1011050010032503c50044415511101d050b80440c0d20000204040303000c280700d02c8009520034000180d5a100c103c002401090b01c0c1040c1d4002d02050056205140300c01c40b094050007150441100d58a5840785010142540364000306055403600104102c0c11055000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442547293 1250 442546043 442546051
    0x21e0904050f0d0827030f120402040b01030b0d02060307020a020d051b010804030e04150b0307030911150d050426030402040621021306081605130507020a0807022106 73
    0x3d0f69045030556034140e0b032104065400003007210704030300c0a0019100c0c4402038443d0402c00d009a03443c242800340c400d80241c00082c06503081040d99070134402180307800d20440c03072103000a00b0144541c501d00c0340003885485ca10140640030b078a00000181d040d92003170001c0900686e005103444524811820190794030002094040005408049422500c0d8000c2517924411603140e40c490b859545000c0501029001d0b040000e4040111060046451824240a14406c10b03044e034001404030b5060806201c501c0c642506030b400354084105c1d8007410000402151118040c5ea640070980da00c5a142c0300c10500c031482c0e901c0c00ba0144c0095541031103001c810055025a000301c5042c0f0441c4d80300c041800c1e00b4110100c41000b4411544840c1005040a003410111400ba0040001d101950b0346030f494100001e100d40003200c0c0c080281b0902240c0307488144518251141c8030100507a01c0d20100203990f8a0740f1400c040e104e64404500304c8215076403142074003404807186211074401c4940694403540d610f4191 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442548543 1250 442547293 442547323
    0xf130209130b1c08040b0a02010b09010b040f032604030b041103241807171209060a110c031f0e0607020303130501060e0112031403070903021e090405 66
    0x103200c00694110b07004100d45040010b14038141030110044480f140e5811003001c40e003c0d001407200060407180103018001c43c004030b40000c508080c915040009051058100035852002408280708040103200940705070b03507200c0d00daa5150780c1c80e44400200c0c0b40c0544505070b0a404002030100800030304080c0a030046101e55540194510540c041545030047d0001c50b0101c040f00e001c0b2820010711800c6025040f12001922050441040010f03504001d41c640100140505040071500280350801c811110700041e07400a608000e0448001241ca10911845000b0001014080781c043c10040c8480202c81c400202211020002c0030380204141c0b00040a080510b4540000c4462018010906920565050380074601c3c660710b20040302500003c00a0540e110b43d6504004148100c4881c6218060100c4402883c0c02c002c0d42c1c900200100403041d10030700c0400c400e105000d60705401219406c2626070441e81d491a91aa91055801d0650004501e540c0100300b001400103000b00849d0502000b4509 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442549793 1250 442548543 442548559
    0xc0d180c0e0f06060d0908090901030506072d030903110313090e0a02100503100807080c03010501060f1e120216020a08010204060e09040201021c0f030b09040809010e0f130209 77
    0x3403100c1001c1d8000c50391180c01138400c00c0b04c0a2804007650050310000d10401400d801c0415020204103a05826041100e06501420034002108e81015510701c5140040301c0b0051800804a41d4540e90107234183c01005158840018104140c09034050251560300c0200f141d4940110140c0c40310641c40500c00d001c3c845140212141815502285105096401410003d840740e0f509030f0440301540300515812050380c0e094000719540d0320034010103005102007801415211040400c140c21590180e0010090015020f040c068aa4020742c5106d1000c245c1c044501c1c145c550310307000f40e4031603944c80701e0388001501c00280d41ca51041c81c2e0031070301d00a60003581c00705021030f1280d0000307080348928002d02010819040c40c51b441458903505041d84184103105803100300d507105504204101c095103000000c101c600d03401c0c9400c41c2e272500c9803c490b81e01c1150105410f040584400c1c00711f200c0c440540381013041406010403583c80c0d640044000c0c42c800381c1100c0c1c0041001010100a400a80d00c440c800d140e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442551043 1250 442549793 442549801
    0x6010f090e1512010603230a0c290a0206040303110c032a0f030a031404110d06110f0d05010e0403170a09080f040608060102150c0d180c0e 61
    0x800e01030841075448070200c0355030503207940141009462200c0d190a40c865981d550080a03040c0a000700300045100d00c00103020380e82c1d00010801812024905803800c1d40c0030030070307135000f0840081d60002200c0203a40d280390049080c012500e861204a15034500c00080007656030552a8001081449980665001c10000895120f4018907100c0c606910003698070501464103447e4200d5801c1008945100c1320508074440240c485007084048004041c5541010820346540ca4242c095100c210802131703a44406880c0c10b540d11078a80d01110701c80c500810018030342008000d515400b04083c040b0000181d5142c110740d58503a54542e002c0e903440400217041c48000240b454031140d87d603015981c907442d40300c044885085850f0440030001d007a660f041d0344440368000800c440340000c0c42c907a6143c413200e55039070741095030140010340702901c2ca0b811503100302075038488000c8030001c4a4020080c85240c9a4400100ba4540d01400b0489941d505001342100148200007084030301c00215404800401240d1ba1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442552293 1250 442551043 442551047
    0x30304140f0102070303020d1d190513050f04030522170f070803030414100c090f0e060906060903070302090c0c0601050603070509090703180b010503190c050907170f06010f 76
    0x1201e00c0000c01581c01000700d00308c40390040720440407410085c00105484c50501d400a100d80004100300451100f41203c02d02c0a8102a0003240c000351028800740524146203040007000040204090100714000c1030110f03c0c0c034405030a25002080135106034025545a401c0480819420720941c02280b1550410302280d16020982400311254500070f14210b513070326166008404220a030380075090080c014846500340d0b291084451700400d9a40c2e0300001c5007002e07019012403101d50021040e4820b100100062a0b6921429503480501a108280c485038640c0c04680707001000e0300001c2d0b000c84404e00700403080d040000501000d800080c100c445030f0740da0b04180302ca03500c01500c2400015404020030025030806004d102d802041c5031030002142c40c0b030f0000d221403c409004084416840300b0004102c10b03e01080201c60581d41c908107403440000350340da8224010618030440740901ea0349000960001d0189141101221401500d03c10a1030314511501590900711441d070301140f44211800c1d100b40c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442553543 1250 442552293 442552303
    0x20c0405092b091e050312030c0a0c08040b0706050415050903041208160609020901050a2304061215050108060f010b0903010f0e0a03020c09040803010605070f02030304140f0102 78
    0x10440c14401c080010b000d0281041e10024154a071040c0306140c2c200080c040d610800841d441d02e0b030a0311007842c060500c01007504060320034200c082950024024000c0440186048403480480d60401087d00c2550345081941406140d102e1610350401050001c244207040e00803510840c070641040301044540c54000040740c00580701681280c1c4140018403184514a078550241801a07002c3d5040003030000c42d003242c07001c040d141201c9284d182d00601c821814610845400350070b0851b0712442c50b9080c446003400c1c01e0340a10081c04904510860703e9090f44a81c0e204802505100110003000b411504003007030f140c50303011901d000f85e900c1d000002840d6400401d010340206001500100306918141c641038890300100c0310709516550728500c000920902e40b14030308080801c500a80300701601c82c1000390402e100c92507a540a810203600700400203100d601141c1c1562028100544c458001e404c00e01c1c0d52502010009425110001d004940032040391090b070506581243d1855034a130105004a0301d907 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442554793 1250 442553543 442553563
    0x303141009151d0a0603020d110118240e030a032105010506030a020a3b01020c0609060703050d060305031b0d02060a0c0512180105070c030801031e080a020c040509 72
    0xd0440076116040354064414180d000411303204085000c0ba103a8000601928050310300b03d42d00000f101c1c00e02c1c42d95030030040c422001005100da12515071315040c07080d02d03900381812541144050254102c01c3c1d0500482c2c4003100c0082c00303001c0311007030b00b0546805400601801401e1403c03c03400d540c401e0080c101c03401b403581a107401500c0541561030320380340718002c2d4021032040000d06c241c001d40015107078504203100c0012045070941c205007100c440c9441004000300c60000d4115084050081100c1d11208201c40c01e021050341d03841d59820460604035003a00507030030349185c1039081903000400d000c00007000d4014212181d001802c03540100302000d94035940d20f9840c0340980c101c5000151000b24075131203141e0300b01090070154503140459030400111082100c45040701d90000080705043c4c0d40921620307912500c0d605018016000c00e03200500245814070008141181d452150011200d5a0f9a01101c3d02c0c0d20003012512035903642c10103034446e44000b006c81d0140e0700d4100050043e00001819141c1c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442556043 1250 442554793 442554809
    0x3091504060c0201050f070f05010b0a1e03200a06020f010b0103051e1b0f0301030b010f030503070b070302070f080319180b060622081203010308090607030314100915 73
    0x30a0b9030560064030203400481c15a902617030f00b48244130100e070f810b07201c48548a200710000202030070018104456200240c21a170060b100c10144080b001001d1080728003526000035829440c044222403000d0310544000246800c9408504002136040d00011183c201003030321300080c000d104015004504445044400220100d242c0c00f06001720303024980c9441e00310614281c85c1c0d03854a104407a0031443e034010071040700300210000c010018001812881805044d800c4054041c85165446266413070288060190011907820085002030703000740d044030981e952050502c0a0380074103003040d400740c1d0002c40300603c101040904100306c4d800c0a2107407070540c80c600361030450620607a40300c500381440000c103010b030030a900308980b001011030358142c1550044404005d50400b030601c0500350800c040308131b50904d40c000610041c00010501d000340d031101b51098a0300f64594049042c2100a40440808062041030078000d000001d60810284000c3d101404018418911649000e0301c3c02074040c13140802c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442557293 1250 442556043 442556057
    0x1c111203071b06150f081c05030a1e0e0f12180a0f030b100902180d02010210060f060e060414060f0f0d0f050903072003030f0c0309150406 61
    0x984180110440740c081d424100c01d10300300a401c3d65039441103a206400300702c0070b64000c100c104520380e561150030000c0c003d464050702000e030700200d1400c1c0c1e111611000d2001c2c05070200000e0b208140301d500680c00c40d001940c5a0085c6000e0341c0c1d0385e10040607038074001c0d40180540c2c05104e98500c80090300d41e400d0840b10495524005601041c2c00480b408901d040364060b4805c0b0000a01d1a8a84545c03000b460207050801c0c09810040110440e10315198031119041d401400002c2c810811103040c41c140c001c069a402441c049103100407400c0a29008000904038606140850000345942044081c0c900d9610b50b03454004400341000700c24082d62080c0601ea2601c1101000c007410100040c003940e1154080c03c50501c22a580700076015002a100f02d446150750f1307000e04e0444078003030180c0c5030490105400b443c68202e15469013015504280d400c41d840c0d01c2446102c1e10a17840030021075160515060307282d5150b40c0d0014151703480b58420002e1a1282c0019000c18a5100f049000c503000c544103034039140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442558543 1250 442557293 442557301
    0x5070b0c1f1509140a1d0f15010e0103031e0c05030a0206060f0607050a06021e040b0d0b040203010e0a1d0d080103021504060f140d0e0c090115020304090b0f031c111203 74
    0x100600041c0e109078161981c2220f034866206c000b00903081c08902c141001e49040e0409a03940c00f141340c0e05034450b2090306a01c2c0c00410210303402c8000d64880b090300e000458848503050405446000c14140014210b10000900c001600d0f40410042d00908084034000480b460120400c0014012110041e14513082204984d0018840754001c10b15400310101c06102000741040924050708146d0144442c080300280650107000c451081c507980782030458085055504081d80f04d030607103c004107001c2030166641c202d440007120860111035031803c1d69007110524800d003034000300940020700c407c81c0a090303202d0003c07083c00e1114080d24151805540c070785440560aa20403255440d2460f1401c0b510070701041260110f5400f8000d031a1203080000041c6490720000061102245050303000704064080d48422031039044c0c1c0841120200c030100c00c004103111a90343d0028420384c040a5107198584a090b828549400f045040c0130140784003071f1503610305200e400090707070307182c8041076003460400700100009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442559793 1250 442558543 442558561
    0xe1e2d0409050f0d020a060627020304050106270513030e010c080405100302040e09010e0c060904060b0304060c1206080c090a02120106081006090305070b0c1f150914 73
    0x2010303403180200112424110411002814440c070480208016081b0038621024881c003801018010310310314042d02c0c400054880d480c1010040c8235001c030506500000800c003480401d4221b40c001d00340006003140d0000000b01e0a42c0481940b2090155203800d01c40091003c071078100300300d070f011a0991501d8800401007001141c0075402142d088aa1240c240004070743c0c1d48503d1202441520b00740c5005070348509000e00c1c07000c560380c001d03c5c03a1940d07170400000200c03840c0c1c045400d2168800c142d03445921151048001000ba00260304840514180482000188401c54000c0380060a080c1c8625642c14070100003002038070440d00030030410b07078082c1c60004c4407070405400c0e0561003040707824018100240c004042c40c01c4442a071000001501c1d10041c0f1411b9690408028024032083c20700004240c0395640d11615851584100320b00b2244c0071501c0b00d01c0324000d1000c286400780f03080c40c02e40c958802d40c09a04c0180804151800101c1900350f000c82c00508510840b5808800704901d4419550f4409003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442561043 1250 442559793 442559801
    0x19060806040c091d01390f110304181406091524160b0105101202130509040303140109140a0c020c150415090501090b0a0e1e2d04 57
    0x1c00c1075040130b08445804446080c0300b110f91541c0008900846140c070b80c60107075014144c24000125038001a0a0f020440d40c014609040380c00705030901040d80c5100381ca11604500682c0c0c0700c1600c0c0c03240b150440b10060419440150345440c0603580c0c01b0262511401c0c400856800c860281d0190441c62802e882440d00580c1e0050904002c0b51422401c403284419400300e4000c4903003614900c088014010410405076a000e000d03000980300881070302c0304510000e0100783c25411840b8087c0c0e000608402c0080e0580341640030b000702030000030f400d08041c03070000e0081803e00c2480402e2040d0380008140c04845005000e040c1003000090313030b01070b141c200c543c02c0249a400920f005602c640444040d06403192088041c0c01c41324500070303648031850600034100d00a15400358404100720b00301d052090f680c20048036070584040200c550b03121b00b50304400b5222440c1044800c1d41c0200f20100168000180303400f01d0406441c151043c882c07403080600300c0d0392038400648945075412104590320b034a6040c1a80 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442562293 1250 442561043 442561061
    0x1e120206041a07050d03021303141606050c190309060f120606030c020f0102031003080319050a0902041a031f11121006021203060103020304061419060806040c09 71
    0x41031900350356882541003803040300c1e01c032420210041100402e0090030b1016029a48050a041d460710342062303a40c02e059502804001c2c48040c41e4a48411f190404001840e0043c8103416410415502c078900130304183c010700a40081445007105a482e40340701246000840c41d450307110b0000702e40c01c215040d80c0242c8406403a0003000407480700c0e203444400d60b0007540010041600c0001c0c0d10b1301c00210080c24090801104201c0307a0040003402440007540400c5030846e03405c04112a140d0703c5031a000500208000072086030982070105000d00c0048aa0100078501c0c400c42e000c1041a001e41030352404e4100000009505821036021035910101c1400c031040801d03198500080ca2204510000d0342d0380e08408140040742d45c6180800440c006800940000b51686000408080e181d180060140b072000500301e504064010001c03034100902500580303075290007003e9400d5a480c1403208450f1415800c0f09104905050140000d10600302090080c010744c0c0001003d0111030030000010094030b4519 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442563543 1250 442562293 442562299
    0xe0d0b070509040c0806270f090f061f121101080702070803070f170c0601030839010516270302100c0204061d0f060411070506010806011e1202 63
    0x1d02d00c1d00380c0c0c4600c11803000708942e03191341c00541001c0c1c042c010980c07100181d90071011040d0603540004004024116440144610001c015070341d42c800e4681400c160090300e28686c0304c2c00081c803450100001d00ca80c141d920107500649111780d00d00f1701219903203c8101c054184820003014140551040c201d0545c0644e80340102d41e071141d564a00280b4550003120b0584411044d60b461030100814999440307000428110150f08082640891580312a018400189116800602d03050f4a03050361803c04009186d4905100308540c8100025a080400516450a6501e801d00007080500c91002201e12400c80340e803500c034003441c03035810041c000014502a03a0b011031800c40000060360751407040700500380c80ea900c1064680c824030500094903a150083c50f1090100144d100300901c010000b030f90b100c940980b1050307850b100c200200300207004030320401840c0e0b140000e0120a020000400e24102c0e90000e00725101685d80b4500c51419a000728208003003d61600410003400f00d8075181c003d440c0d4002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442564793 1250 442563543 442563547
    0x32915060315191806060c02280302040219080604021305010c170f040305190206070b31030e03070605040303050307020f06070905030c040b060d020c2406100e0d0b0705 74
    0x40c6081521801041d440b243c104200003094132041025030059400400940c20040c5130020180e00180e41546030080350f026a03507070140c402c03584c0e40c00400801c000b560003030011076031011040c1d070102030210100c1c4407d02084480c00851128203040c401c550000214210100722141044011500710840f9002035403000d40e24a403145030b821f41d14000b002c942181104241d85c5610b1850201e0a10b2000710300300b5400c41a0340f6040b805a2030300001c441c040742d48508525490341d907104520507510540443c000c0c00100300c01c040904416a0400c1001c200d0003a15071064840980d400c240d40c3d141140101c0000a0f001e020410000740140040c5400210702d0064800024110490750300d403d1040300e02000003500c42004200340d0400f4012144072003010740d014400190510007040e203d100d10020b45401c1e5900040c44e8a0720b08050285003880c03210890418040c140710b4a208200120540e402807182d9225401114010302420114140c51400781c541908800729498011198100820080a010341 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442566043 1250 442564793 442564819
    0x1110309040e031c0c020d0f080a050603010f0f060519050303040303080702030c0d080601030e0c0f0f0f03030f03040b09060f040602070303060806090a12050405010905090c04032915060315 83
    0x1e09031310142c403142d42e0342c400a4900540c0c64024a00000580040c00f8455054440503c242d031000e105030f0302880c00b0401045648611001ca80100180e03031a15800c3ca18108803600c8104690308900b0844504898480c0340300d200100043c4005031a00c6465455801000100006809015150307400b1000b40180c9045c10a41c4101b2800c04ca12011031030009030181d0200102c0351781601c039034031000440c0c00040000981250208810511243c0e80da4030940e80b00c0e128189655440ca410109a0760203800e490b191800d051801c82d41d900191070031549505c1000c002642c54000041c1c05116030030262002d081622076403503c034002d50140703001303408040c1ca880c4081100c02003005041c0c05900f40000410314041d490401d50f0741c00d520201d01404101040008200d1030383c1c0700503810240da0080316101d51544500b0445174181c0310300e0303100805003204407c00820281c000f85170524510000701c290b60701c56641810411148001d1601180c1c841420700100394904082081d00380c0080010301081d0f10549 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442567293 1250 442566043 442566067
    0x1d07030b0403051204030302190c051f020d0e100b0904020102060c030604090804080d0306050a140105030901200705072702070c09050a02072108010e0a0f020403030c1101110309040e03 81
    0x40882c0d051b0042a00020164100710300003501e00305407172952414180d00344160341e43d0394441c00206881c00740d09444074001303080c521842e4115003a03140030315020040300c000c0d603090035140c0e0410b1452880f000c3c40c00382580c195013040048903100d1075050307000c0e215558801c1c509168a80000d81203d0b00580d850078561700082c00000140050303e0b10300010100b02901c200020180d90840d0032030750062104020400c40e1f201c14003400d8001e08400d0038000e4480e581e29011f00d0050924560050015201c032581401180c106001001400d00500079103601544401000715440c42d003d004503c408001d1000302d104000da540a02503103807161030350680c502e950b04a10810340c0e43c15600001c145500040c0113040210780d00d0400c0200503204406041d100d02040c0c090300611051141400007005040020712050b02907218141200100c7c804545a6480382001002d4125698084031900c0c1420f103203c0786036005203401401c0000505c02149003d002a043c44082c1c41c0400070301056100900100701c0b019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442568543 1250 442567293 442567327
    0x30106050a110c0904111914040207020d1712010b16021003020904050a1e11090409051c02010515030f0d030c05120a0b01021e1b0a0302061305041d07030b040305 71
    0x180c0189006c1c0403410b0001c4c10001082c2252003040c440f0120084100101c10001480a115031740840340180c42d81500d0000c52000d41007980001c026080304072060100008110141802a1440c04002c55581e01c507a41e100c92803003880f41d00248984602085401860604917400c41000315181c0582002c042d0400304066510030340e000256503455101c40d0302090b003a4101004403030258101400000030310a4203420a21031a45c2050045854804103802d0003400c10119104140c802518155005c8048009008140507a5540803001d28002c100b2854500000d10a0000a54001409a100501e02c0690084c00c45040000c1402018082032428280e140c0080384208440740010400d014514002402e0030004d900d103020306d0a403040144000b04000a03e410156540082100301e010740c6000207558480700e500c000e40c4100001603080030800340c641510101c403001e9900b40081c0360306454001400c0501c0c0351100c020b030300180d41000403074083c0f0141038000740603082079484c00464000c0d01c1e26072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442569793 1250 442568543 442568551
    0xc0f060f021b0d0c0f110307030b011403060a092406050303071b0b0f0409050c2803200708090d050a05030705070618090207031e0c1106030106050a110c09 68
    0x554480d00e01038591407091080d4440d0600a1402d101311030055503c142420280140140c400740302c003150130559880400c51400034540021828805607502c03a0b92101d00541091042c2c0240a280041400c03a502030084101850340640c0e00700c50642040c00790548001038070142d2001549650700010aa2024402001103d010b02c4400041c81e0306045091540d0b40f00d0b600810074428100b20441c0d807514001d05072401d9882040010038907459007800621113001c2d030b0741049400c4002c0b03070310051101d900c8030700004a200c1e662008c2c021111010a000c1c8244a8416598081d800c10807011000401210080a11400050560f261020700344c507214503015042c8411240e0703a00020f07501052110410400c3d0040400d49400d2070204408100d6281d50380840c841e50314110b401180203410140920150b1003070201d8010540400700d01868014801c8603401700542d015044202e0800300d03410000c00b1241620f0403901e0701464040719040c12580016541044806030045807511600fa60b107101c803040c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442571043 1250 442569793 442569817
    0x50a060e0108071a09060a050a030204080102030c07050f0606010e040207020114030103050105240307060f0324180b060a11030408010e0601060305160e151605030301080d02030a0c0f060f02 83
    0x14403030a01c40c0300380303009560400c884d00488041c001c10007030340c2e54542201c044240c0e91600685582d2412419000780c00365400500c1c5550005c010060040c000201803e801c90046040341c005410000030952104000d54803140010006851003210741000e400402c11903106150032080c00c414603201d00916002030300101e0b4265190002e01060410b00b030b001802c0742e244400c0d10380801c0c802c8000265200a280300d0301061011445402440da8081c0d800b44118654000b0801209451006884600407080c091080403440c5045200440b980c0c1348606007106d04058601d80c5811301200040d5104c160105030100710f40f1040002141c1d6100c2800b80314100011000200119414180041d09840d8010202c00c0078009100031400c0c020b0b809124840100070070380750b210030320661011400c5548181d19440781c1c40034280e20300300200a40040214101d50301c02056801844a9001c100d0301c030722845d030300100020002c80300b440101d07401440c10321701340c0e06c104000200070b41704090240c241e8201d2101d41070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442572293 1250 442571043 442571053
    0xc0f060203060a081c0207080601150c1e11010f050403030c020d0f05190605060f06030711030d0204120b06010c0f060c05210f010611031c0e06091f0c12050a060e0108 73
    0x13950f03010447c1c0b001600384c0078094000b56050680705500b07079040c3d00500c81004460a051820f002d034200ba4644502800b44500358408224240011500d9800c500d06002411203900000301902c64400e58041c0c030785c155200d0070410f42580030440c101f0b0b1a00340588004d510881c1890008000300954900032074201c1b2032001070f80240c1408412564010402d5014500141d00e03140c4983d01d000403a03511903140d05114088490140c010381c598000e0200418041d440041c010070f04130300c48443c14401c24458400202260b03114401125000c0d40954001c2c00d2400814001001590940100b03a0154091030500e040a44900e98011030200381070740d070396602204070103010801140380031540c00352007207081c010804582e541c401550b078810303092038003a00389860002900444554000b0001c440300301e01264250f04205261646403141901c0142c3c0101204006624104440c003400140c0c8243c1c2d100c0d400303085441d20a54000d0a0b0081010111941c3c5400110705114a000094003034405140182 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442573543 1250 442572293 442572343
    0x3040623040e010e0108010b0a030206030c0706060e0702030c0106090e07051005070b27010c02060105010c110405010305030405030d09050303090105030c1605010f1401050f0f0a080124060c0f060203060a08 90
    0x2402c5a92401d10240114449e02d018070240e204c1d0b0084940081c0941d4260b507039003085040c030310001c10143c0c1100000ca4000b005204480d6030001c054094020940c000704042030751017001380e0880b812000a03d850350022082085240792a00381d840d511402c60400526149050740c42201030641201d9096603110100e040c40014203c21040a403130003184002003180003c80c2802a5903414148203190401200c01e1f0a0700400103217610701e007140c0502610610155849103001034072500b081c000c19009108100394100071900c00e04501c0c044501c007601842c50405690011110f82e4801000005039031004c016800503010269032840b60317503008000000e403c400701f601c4201540c0d01505100c025000a400600403560740d500450141502106c810f00711040e9100450301e040c00e01d03482a007041d4604048402d107803030340a083ca80c941242a00d408422034136500c09441e80c6481c0c5c04050816005800304000181c0d25134000d54100b0001400442030581c0d80c1405403174403000d250388600829408240d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442574793 1250 442573543 442573559
    0x150405011a06030709090b01020c06030406060503010c02150f28090605010504061a070302010e030a020a0203071d0609060303090d0305120f04030f05030a091205130803040623040e010e01 82
    0x340341c032038a04480d880c1c81c6050840c0002d250110b64040c0b6402d03e41e481681d1000b9a008000310a0f1040e0003610709520307032900d41400e9005214901c81d060095090188005003148042000c40c4422450b111641843c0c0b03c10102e400149802003401202d5003c40f40815107060041d0211522070401c1100410401d50030301d8007005890781070b40b250303001d6810400203000e5003071640500540c200d003a4040584581c41c5003002c0b80508840190114607004c00566804081d0380031174455547d900030307000c90305480e87d10301d440e400c0304180285030303015007285001241c21031410404541e00312400408407400c11311041e0015004c0849000308034041100040d54a10b2007000c1204c403644120302c0b40044c000c0c0d2800d070320007030a11503220340c19208014000000440001c89036102032025078006500300d14515242201400725400300c1c4140c40400410300b40040c08100c000100c8058034010b0351041d9a4160340300c0c9183e454494400c00a40200b41440b0228064050b08403d500030500d0390f5807005c282d4540010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442576043 1250 442574793 442574831
    0x31204080a03030f0204140402130e04050d03200301050108100e09031209300f0f03060414041e020a080303330f0f030109050a05011e0e07090203040515040501 70
    0xc90131080d0300600c001c201da09080c0240341404102a200566250102100c0f510405519080181182c042900384000d1010000b10078849001039181000720b541a2684001d130007408161119034a1010030041c00a54403400726690005034964210381001c1e00c0360704038100101c084510114540c004540311071905481c1e80c40c90340211090020b00a81d100f4000405000000c050030769608200c0742e800700703207505240b00403180020403903011142c540c04c0080045100354003d54104d4403950421414041a168155509000d9603102035903200340e4075100f175a00680c1c90020030580e4030000c800310014644d10f0610082d481203211490f260350b481b41d0015031803990b030083c528040240c105501003114036100c4803102d18055200f11506c1481307a0242c40013a000d4444050003c250f802003681c0b02003084015003041c4407034105050030350300300c81a0301c2240003107890050b0085c41d41d62100b8420003800c1840e5005542090003171003031702d0410340818a14000048140d8040760983c1d560003442911903e1070075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442577293 1250 442576043 442576061
    0x60c090e09032b140103020907170609150a08060402030613050709021b0118020f1c020f010302040812090a0f080a0201030b03030415030e12030708070e031204080a0303 74
    0x4140e05410803403100c0d0380e240603c140c41080c0743c3ca094007004080b40409040c00f0b101102907414421a030222031000344101080c84124065000f200100781028007511217004400305806030714000b65a1402048900701000d00f400f030340784040105981c0c1c2e544402c14010040c0840f03500402c40303410035105142ca48540100810400380b070700004a0005003000c1260f0701200e49648015803164a0404400d90501c0442807011407503191110098503660868042d0b0840c034000c5030744500e0140c5483c18003a00d500e8818203005180128024040189482007200c2c80c2044185001420036403602c01c4245010301d002c0148004c1c181c082203c80a614103000300c00c0c0585184400c0800d0741e464000c029a4440c58078000905054aa90410407503840030810f07640200303401150044949488140500200211040c03034800d40244802d025030048150704583c00b40e001540c84200b143e60301002100c001198582c0c0e02d40c9400782c03d40307041d52900404c024102030522480a0960180681760241c1100c48100c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442578543 1250 442577293 442577309
    0x50c03120c0304031b0509160306060905060d05100b04170c1e100c0804090218040e070e09120406030e010c090302131109030106141206060a14030c030a060c09 70
    0x5001070342010064404683d07104a800b1042000c034030602656000ca0b420980c1c104184904104e0365030304100c201012981162001c0104645440701181d49500b02c4c041c56400a10801c01e482c401b8001e540160303805005828512842ca454050504003a40954003c841c8038a148507080d6044005000c41d4100034002c0b281103840170510746011481904800c0325a126003101d84035003400d107000c2d4240902079036010541507079454960803010002d4004603101d070031401c107261080309030307042920a0300311242c1c180e0000d00d6400e10300703c000c402c81c05004006860600405104d000325061200191000c0c080a03100441e00d0351340c80c4021421500046503450030882500c0c030800241e120b820002104074078500001c50500880d0583c440e640c89000d40380c0360103601e80b132400201c07084801e059404003042140d0b002d000d101000c4500e6076454095139401c0e40040c204404001400704126110040c0700040d05840482e004500002d0800d00048030a40301e42d51120340a00b4402c0c0e00c414001d01500d011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442579793 1250 442578543 442578547
    0x60314060718080d050a030b181008150c0702010c06050702010207030e06070b070521100906061e0e0a090227010c050a1e0203060c0a031d030d05071b050c0312 70
    0x2281045550342242c1e1303d040103011002494041482c800c0c0c008c0700d40450054a41048a08030203d0002000402c651401040f50780d8600403800a4003c290051000b0424051000303546a0880001d1640d0000c50102d05104100103464001002c40c010944a091540c00060320340c030f03080c01c1c05400b0b203114140c8284990f100f04660f00009105c2c1c614103400001c1440c143c3e0703d03440c1488100d504550007411503041c0c410030700208145602d010002405a138a24002071248950702c6005a40f0040e0505803468040034850304254440d1051012565299004201c500010750b6840300800301c1e4005d080d00da00c44840e0140b801b06007041c64440f5071a02d034081c40d004103c0c0c0050f440da1900c0c0c540344000242022a80f00c003680445408111116407d50002c09460441c00c2c80e07030303c5414a600c90001c8501003070802c0701404081129010314840320300e104015501e810b01c1c0134003400c010040140b01d0b00074050403840d03006283d01400c02e5001d00c64810001084000c08100800d0b1611420601200c2038100c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442581043 1250 442579793 442579799
    0x80316302c091303030e010906061703120114061c0902032e11190f18030c0323030c03131a040e0c090301050c041409060121060314060718 61
    0xe2140843d0300600d42c2104906801151808070081c0c1406000070f0129800c014500e814402075900890480325035442d603404040701c0300596501d81c00b8201c49055611200d0b0010850f03500e00b5441e812214200511040c9402085890041e10580c441d9040c80c1d0955102c2c03800c003c50408010207450011303400a25107807120041ca525a5450304a8504004162540901c4d2410324040041d103450081c8007030720321101e1206c003200400c011102007803017000031941540c00e180711030302d040d0711400e4035004245202200c3c116210301704043c1440301d0403100000ca011401c0c0041405101800d80c1d41414000346a49110400c1141c00810300764215015090103000c100d0009100c1c50300310313400c4406a48a03481c1c0b954410400b8502d5000f6407215542550a090070448240c052030f000340150b8050942c030000100b02d40c1d0500c68004400c440c22030201c0c03c14034520801a48a034081c08620707005540c04211a9142d41d1020464003000498104962105080c401e20700c1e0400003412240c15040b404c5545185 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442582293 1250 442581043 442581049
    0xf0603121805120a050102031509010e0603100504031803140d110a23030a090e0a09030c0b100b04090903030e0d0c030518040e070807080316302c 64
    0x1c110312900c2d01c1038906400b100000001402500340c42074000d8021512031416088000f005d000b0440e6417403141c0c0c500c4d40085200c107045005940038000c0500140705090700000e180300101800b40056041c04450b05c034003148440400c4420024502c202d44d040780c441400c1e5a040c0c906441002c269050003044032101181c0c110000f24440800d402014582c59901d503024005151424554075040c4d40c0000502a04070940007040d0b641150500c11501391203075140c0058204403512860024000b4000c03101c6c00d00030039600041d0603041201b6158415651350703503000001071a8407903441f4030042500c07560714100341a0180f080001d000101e0014241c0b000c0c50b000300038401c0300040001418400b002c140c511500704501070801040801403c07c2105c52206284070346c0d5034045105d0703e50144110440414094004020380350000d42c0100041d04030030380e903602c1002d4615950030044540b00301e9018400d80400304030045044c14007a0300c0d0a02c004104203a40e41c00c110b100754103030680d9002c1c580302e0038a5031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442583543 1250 442582293 442582337
    0xc03060604140c0703140f0306150a050703200d0804050d0c1a15040e0a05010b22020d09060c09030302010b0d020916020c04020c101d0d0c03020a060f060312 69
    0x105411030350b144c1452805690f8003c5103054011104004101505502681d800450003007404440c41e140100040c0e000c0d49640c45181c1c00407000420a10184000a001ea01c18004282da140c0c50800c01101c03100d107440c6040c2c8901200c00006210720140024420244403e12440010b0b2a148136880c04544030070313820040da030319690710110045000805a400791407448560203001003041c0a4160b00907001640d070f8080c4070080d10346520b0003515000c01d00d8200c0350301000303aa080c00700c0700c680515205420003c1d009034120b88103043d02c0c0e01d071090000c0d0544c481e242961040b905c40c00745032030443c1002821a44550081c83c05409402240c1000d60340e001c005950041c2c098910000c10070540f5001ca0900c50f205404030340003400071070359a402642c0401c4d030700c12a46120b641080041c0e50201c1500071815601c1c100360b00c0d074021010b00d001c0c00b031080c102103040c03030300900403202d040c04166501c2088032002e50700c02d00b49940e5968180100310b44141c00a16084040c80d007550119150180d0314412 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442584793 1250 442583543 442583551
    0x80a11010e0f0705090c0c0d120b210105090d0912020a030203030f130609180207021f0f0f020105040809091e010306020d0608160e1012080a111204030f02060415020c0306060414 78
    0x4030206028270094800c1680043c0c038400343c080d01c1c0200f0352004582401e1030b2010100107159039402c1ca0300090034103000040f960421015179942c0c840c044d20f0822052140c0a103001c0c2a078014140d82004130258a00700005c00000d540080e031681e440e020003002c80085c92854010004000405204000311001e446c510010340420310740050792090350b440019124081406106448540400200c0405400c03034070ba03038803103082e42d198580b2706400c08404a00b00c4108072001065a2001d01400456040c0902c0850388080b503036100d05803c5404515100114200340e001300c92061b000103840c42d401183d401540000c100842c0140341c207070010b20314404010524040e2040402a402c002030100ca403007180307540141000d20300c0c80c41142c05800c0000175a07009008100115074404060442c0500004140c12183c3c40300c1a13407410301d0308540c3c40d2841600503100c180e9101c201800082014000502c528441555640080c0143c0400a040c1401c100c0000c0c01c1c0307841140341c0300903080c006c010b0702103403980 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442586043 1250 442584793 442584797
    0x7140402090a0302031507030b04090507090c030b0303130911040b071202120708070516050d060e2a010201060b250204140711060a0504080a11010e0f0705090c0c0d 72
    0x1141044000300c1d00005843e0310180d0700d40b1901c5285039020040b2500b0038000c020554040c00b29031140750500040d9240001c0003402c030f50009004200c0d80f280e0f030740203800d280000e207004941341000b400000d2554000c4000440b4030050100f08004500692054964078030081250908017071404c0c8447c00580201000a461001c02c2084100401e100b0322140d04d00d8020244950b807540c04604084440390000300301190755204030a0b00d00000a01c0006c1c007800c8a170001c2ca41502010203654090103000b003848440351a1189a03641e494801518001e949164004031070f041820809100080c25200541d109004504080080c1007445917407a203482c00315a054203a103801591a440070800401300b441d03e80500c4600c010503c03218640c07103201c08136800c1d03c2d28200d03052500e03091007201c1125002e030380c01414030f0402c10107200694081c1900c040b241d042a00000703000400352185a041102c02902c1c050b564001c09000d000d036150210b180c46d0004000740080e0b05010b640100c480e651000f019803401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442587293 1250 442586043 442586047
    0x10120305040f24050702012718020405060a050a02010e070603051f1a070c030b09031b06100317070c08010506010909020f09010507230703060c0309020906060c030d1103041407140402 80
    0x429640035400200800180000c80c6045601c4d0044401121010340034405409c9000780d80710740202214000c0d10182c0758014141031904010900690341039126682c005d080d5501c03248400c0300548180b245400034010b1b030f00c0100b101d151000041c10381c2c0c44503002180c8042007060080c0000c054403842d08100420003914256074070444e0502108041c55a40010109140281000f240182c040060310341c0680f2001c2c0a1840340d201c100303003030302c1c1d10b411141d00c506503409540401c04244480c40f0a010b14103840001490032966856000101c80c60340c010310b06581d11581884010f5a000c040c880c010102c4090440c1401d00da000080c03000d00c01c3d50042410400302081d00d00511423801e144a24405404c04603142d16510038100075141d4070303d8803007a00c4c618504080c41c0c4980d400390040d07000341070340240040c0c4180e4442c410003400341c2212090341300910041c0f141c80123800040c828555102c40c030001c55601c07071602c1d151098420501d0913102441d50000c540c108800c0554408190081c2011103001da = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442588543 1250 442587293 442587307
    0x20916090504020c12070c03110a0317030c090d0f020108010f060c11011806020c01030b090405031227150705040e010902030a1e0209041505010c0b10120305040f2405 73
    0x3a1426031401904000c4150006d05081080010099401220321580c054100300a07042c04112200b4102d21003c0c004068112021010601e90402581c0c031405170342049080078a01c1000c280207040c285c100f00c2d2841c42c58800d00c000c1d50f070048007090041040c08030705e6640c2418100000e01d4000140300007061900c4484460ba2070740e000310402d0720049030f8201510740c5540c0e9400029030301c4104495280c00f09140042d0b42540e0b080a091051040f60444001c51404400000c48500340400614225099101c1603082d01001202c108041c401100783d0010700c0c08401a101d0210048400381c500400e2102c1088104001e295059a6904480c0b68140050300e0356603002244000c2e24105d42500f101030f03034900e80700c0f03242907180e40a4007070780c1e400b0307030b0200701120141200b40300b54030301805447e021030800c10781c080c00508010340c0135600901d50381108080b19915501030a0303824001204501250b800303c0c0c240540112145070030024000d407243d100107001c800c250018250113028040041080005000c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442589793 1250 442588543 442588567
    0x6030c06090d170a0e030a020a03290a020703140307080103031d03010c0807021e19022103070308070f081603090506090d1b02030c0d0510140402091609050402 70
    0xc008903009802080c035000d034001071141c3c1d540303c0002e10021603000401100207040002d040601c0e40da005d045002c109045444051600ca55500880401e60512128540203c6403107181c074000d0324044400750722900f403490060a0391484040c1a920a81c1c1881000081d9900548060440e40c06041100741c080041c0b00d9004060061407100c0d80540c01c19402560703003503126280ca84600515030a40c1e02070784180390b800c1c0b520124054864510303405224068444220b050090f04181c1c4000d20084d141c06a688000c0d024200301c04040e28a50004512101410341113031005038403000304d1a14510058031828041e0507884080c00241c0f5101750f0031013200429000764022084507400401b2680c3c585170841c02c0640d01c00314024080001858040c034407442d4009240a1743e0307000e500070f0141a40c085904140004880b8000c4241c40d01c1c45060140080c1040c01d00c030b4031300d04480e08842c1e12480e00d002e0052015101020b40303d6805696840c3d50041215440001d8034141c590031580580d82e10504020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442591043 1250 442589793 442589809
    0x61506020a110910080312060108130b0f0a060305010f0e07060c0503120402010e090405070611070f0b0a022a150a0e090402060d060b0c100203010501090b0a14071a06060306030c0609 80
    0xd92164800015002c00c17001f808003039144500c02c00da072100c0c203d40d00c02c4d48a4070000740c3c04d82d00800403880c1c00042120b1441c80000d8903480320b00040000b42440ea00e4803000d0035a1300d035031416038540b595407480824041c01808500050030a500341031031150081ea580c207982c0d2048400d240b034604d9080c8045000c5a100764100001c0c200010202c00803410030303003071107034480c40f0358412580071a4418001e607400c0040072a0b072100300c95400846a201d41e15082c1c80b01c1c03d030b510540207001140a4040f900c80d800c60021481034070705200340403800112030020240904407110140c050242030003401341030030640c0c1c42091010140b1080d038103481d05031030300c0c408542c05000300714181214a00b80403001c10303426400d9002e00301090f0040103c4001b0914286101d080f40300a00419000410346001480000c402d4802010340e50ba861920300e06400d02240c04034015008440203e0f002440700f03c420480800d0f003192150400d0742150b0f400c2c5582404400030350b40f00360715149207004080200e2010140e95030020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442592293 1250 442591043 442591049
    0x6261009050c04030b1602010605090907032907230403122d030e01141006140705030a0c060c170615070614040308070c080f25061506020a110910 64
    0x804000141046c0d08000481c008000a0704015860150700240b140342440016024450005c0a404c1c640d041d034644440c414030319400f549040c07090f0f034600403180e400c2d5041c2a02c01e03600c607919400d005d914420264003400624078940802d15080c001800440c0c1d00e0003480700161701c1400c0990300c01100100e00442e5080e00c440c1103900388001c42c220154650144c01020768150310304000c004d4081c81c110307000001e078400e5a442010101444090102c03500a02d0640440403590081a040c40790560b80d852540c0c0c00703800944001fa03c5444088100013050245000c500e0050a00c412013981e40c0c45e203250018801040107111741000417081000590449c01c03108281d80240003404050001090b482c04c650b416a01240014405000203c10910820401030200d030722a410914010002c03103036072896000452520749884600801c07981c902040040b03101103e1080401140c485990b0424410303400c2160310071000e64012000c81d030002003031107840d48501c00d003c440e0b606e036907281c8840c10b01180417660 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442593543 1250 442592293 442592303
    0x180105030607200d0203090112060b1b0f010204140a061d040c0c020303120708010b04080d080c1204051608010e190305070c171002160f061506261009050c0403 70
    0x50544213800e5400300040040301020788444021115900ca01c90880300c40e842003100180c810701c83c008400e840300c00b00c680d07a2010101100c18610826078814220b1740141c0c0010909000e1011000c0b00e41044107003a0700a0401e0700f46a1894601c031160340400d07031a80940d4510075652000c00b03c408500410400b40080c2d0090700710f81d16000b8400c40340181e40026251100840e043c40000924400340300211010340701c504000c3e18011100140a807914034014201410024081c03013980c0d0301882c0f08000e2131107a8000c400a0403103020111400b442c4d02915004410f85905003c02d09148107400030f00c0d1300c89041700504065503000c0e40d040882d07190043d45001401c2504241000807800501d49034105d800740c103c0d050340c5104039401090400c03445924500c216040c2404143c50218902c900c903120a94010300020450318441c0507a030025850300e801c9000481c0c0c8525204820050140801d480040070000c90580c81c20700311403800c0400058407484450b00d4403440014261039501040d00d004507800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442594793 1250 442593543 442593553
    0x6050c0f07050609010b06040510030506010c061404140c220905030a0519050405010e01050c01060801062d05011b0302011b03140703140a151806030218010503060720 73
    0x1030b00e4415190201a58041141e6080109012440c50322500b281c040f10001065030003002c020388001d0300504030080640f03060001c994101008074034180a1042c0605110002080c03a10741440e000d40450124076035a40d02e540b02511751181b40e103410b1200a840d0040700410501c0b51407150180025180e0090700401d43d01010070344541d00b5800c00090300b001c1c51b241e0898407800d01501c2040303810740224401c0c113000804254154050b9401840208031400117540003042d10341c2c80d62100c60070740d9000e030310103031040d07102c2c03428402d0014074520402d00c05030020100c21109490320b80001e01003800361120304d5240e90748901080c200f42c000d501c08000321640b2406096003000c1400068028402d01070082e5055040c000000c54103442031148001c48803041c040d42c0d409480b0303a040040109501209403824100341030011070f202400e5040010004c500040108032182580705102201c69600a0002844182c4005106580d130200740f95600c410300c4d14100e04440301038421034901d40075280d01c000f0320303000d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442596043 1250 442594793 442594807
    0x9030f0703030f02060405070501112506180503030f28090608070806010f0e03010209060f18060304110d02010e100201050a05090d050d0b01090e0901050108010b091306050c0f 77
    0x106140d01141c2c000e844800f1900c1c003104040e40c5490040318010040e4104200034082507015a40250702c0404503021500c40714180e500c4001000590740c408001c404182104025144c0c1c0034070f07040350301c444507042440c1452070080481d580703000c3c18202c5c110901300418090b1701c0d00310402c660503206c2048200200354082c40b41c0046e250080c0c4c2d020302c400040b4420005080305003c0e0b00124018a07043e9608600350012480072140c600b060070a20b903155400300300c0c140142c0c0c0c0b00f401a1800130b441141c000d60f0f801014040d1440b00b202e845400d0b0041d08140304010100d4130794603c2846000066625101c1c3e8001d510040f40c042c06129565544108025400f41c0e140341d056018501c141e40e048020401901d609040700d6440005a42510018a04201c50064950140c0040c40741400604000c0f07071050321004014842c2d40304031407680303080c2c3d50340c07004000240f02402486c8655400340e4000c0300905000041a00051500c040505050f8070f40001c90324140c0b50f035044400c00340c4907031596a03e40704 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442597293 1250 442596043 442596073
    0x80613021c060501030b1e0d14010c02060a0c090e042a140f04110405010c0c15020f070b03060d020f131104060e03060603031c0905030f0d05150a17030903 68
    0x2c0140034503400246405203000c002d0800d1420035500c6011a034421407007103405c8040091200d0591011121940da00c002c0034645002402803050001d41c540140c0381c0e40c074003600503c7c00c42d008036141c2000c0005960342002a5249034860326000b54005c40444500e081400c20800c41c00d010240b020030703580301000f00040300b600204400d40300900c12600c41e501d540003002040103072a138400300502c0d092000c000801c032a40c0680174907101e00e4803d030710b01c4171050b54440c6000414004518682d0141c1c01000341c98402010912400c809400340c108090700354145140480d210203000700e4000c1c05072540010345043c3d50754000c102500b4a0f0031010603c03210004078409007041d00988540400300b801c02c001c0200031324012422038841c81d0050011410840c02c1101071442d0440300000c41e029a503611185404100f0920082001c1610600d00558420303240e8003c0c800c540004101d01c41844c400c0c0300c3c2c02401e50b03440301c000085031401060407012900c87d001581c1036104070241e4680c9071243c5072000d04c82030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442598543 1250 442597293 442597301
    0xf0f091905040e060907060c020a09090803011e060c111206010b3a180c060201140a0207200406230312120f070903141615080613021c 59
    0x3880c10b54062102c80c0c00d00d400b690703503158280d59038442500016810b2144500c04e01c150388031180024030072210740d83d940702c0480458400210030303200c425000005000c042082880101c100c05520b240000003032400320001d00c0c1243c1803034020030303600660110b0308842d43c40d884150182e51104c01562025692403c40900a61041341900d4120403e030320b20700d26131050703034201c4204906405040e81d00010409241c078014034a01c8001c0c003060341c01020080200d41041e004c10080c0c0200d400004900320304508103003000000400403152240100070190009081002003d6512880c10a07501d07c81403083c00030b0302a00340b42d0840080482603001c200c44150244041181801c000d41c19900c0030180b82509144c1403242c0100004028104ad0110310b5401d50302c8100c550054807840c00c80581a10b03980c81c10000c000103608a02568000401750b4ce00c1c0a00340000d500a020020940c81e0b42e06550750050803444000781118401c01c030290820200d40d4440c1c04846441040780d007000c080c01e4100d10b00d00e00030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442599793 1250 442598543 442598549
    0x6081b0d0e0f070b030c03100b12060a140f010f0212072405040c030809041404030806030714010c080904020d0905060a1104030c090e0c0604060c05210f0f0919 70
    0x24481d005034503a581e02c020901800340d80c3c1100903145956075042c2e01e41d21640c03001d05000b007100300c001da0000b84e000800010341301116088100700031b02e040c0740040266510340c0d60001148e45070904c6055881c2d0740c44641d01d00c0c00000a09041080c032140800aa0800c002c24040e003801e07580010b24403041140301caa100803400e07081c1400c640341003050081102221800c44004240306418203040c004105020301510400d0401400400e00b03014220f03c4600900c019601140407030020710510801707207030600246026101c00c0001c1c02d454000780d80000c0040384490005056518005010030407500e80381c0465080030702c8404280040340192514599450040702c403e480303903140420314849002d095003254100e82d0015210001c441c2002c08440040046181041c814441c911045145494070805000180400c1d2071720340f5444040c3c00c0c583d0400300f403841022203103140703e4515443c100080043d120f680c01790062007a20395166080701016403081d4800c0da03901a121078005520300701004c64100507 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442601043 1250 442599793 442599821
    0xc020411070201110303371107050129010513080a050a0309062c04021e1b01050c030a0902131b09050d030903060f0b120303010e071806081b0d 63
    0x80d00c40500b1682d417030340001c0d84c80c00d910b442c4206070703c9062607181c0c0300340341c00720383c0c070700c003030906030350224181d004848210020015000f00810f110f000d10500307200e01250150f03810211101016041103028078908000d450905000000c1001c4031904245a94440030f0000305044074005007040c10003540d940504c2004500140e804400814040d11800d04400c205440705140945002c046119200e48000000007076040f035030901003000000d080034501d2400f804101c0f50999101444803c030040b110035110650301e01c0e8140f5091050581860007182e0380071071420000190250709100050540184444607102c0714203140000100200110501d001c0c00c0d869120702c0b011a035260309105601c0203813140640400d003840002c1020178060380018042807029240007546070b00c00000901104040100740d50380e5440400140240398155007415000f2581c1e060084040b0100ca10301850098503000725420090344d0808200d1000c099030544680461195000f0780324914980c541d0010541600c1c0091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442602293 1250 442601043 442601057
    0x6050405070518131416030b1506091c0212030d06050d02180601091208071a16050705030f070302150609150114090301020f030709090c0905100c020411070201 70
    0x4952800c460000643c890700e085680307441d52207140f442c061100d25101070350500828030805034100780c1800085142c0d90072480d0a1040790550400d59000d01c001805004160014207090000350380e01c4e400d82e142d07880b08541a001801c9451610304141d444440001c1d0030880c0c1c0c82e034004a01e02c0100c003a2400301e0842000b00070300b0b0390301c508000104606d4100a50804212840d40140360040e03d40c01c1d900905c1811300703a50340c940d500c0048640b50b84000c000d965615002c40d010040010320554600b1901c4094091891030416805290403450b0a032510018090300003001c20400c08140142c408502c2c101d510303240c94040d1418069100e0400c0140101c48000203000540d00346030107031440b4014090182103a4108958000546682104003913010603a002130296041c00d88c1e003400100105c1d894219181e40324200f8580183c0200a981c002107076040c20b0540b9818a1544181100100c610440d00c3c0140d8041440082d03070400190034010b0741007800c0071075400600000c80c00034110b941c800e0380e54207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442603543 1250 442602293 442602299
    0x6070f1406240a2304060e0a06060212131509050d0c080d020109050c10110a0311160501050901030b06090405070305160e0f060a020f19020a0506030f041407030f0605040507 76
    0xf2070503051500424070100725101c07400d042440142d022181025018000180b41502c0701241602840100c8681c2c900d10344845042c0522541031140d000e10079860100181458001706070242209903d00135264101d4984400c03184462060300c0140c001d150141011701041d0640c1007250005201e8020072100340700e00c0301d500741414814032440520079044405040070124420401002c019980f4011003001114811845400e2090141c201014031030345407032030800c03c0c1d41040c600b00072080c00f03110130421840408000c540d0300324046a807a4142440c000480030768000003e01b007801940c0406400500d081c003003140ca1600340e800113008070148010300c100300c021030300100c8020502c41f044d0f6400c07180385031500c050f40c20944007405c80c0e51100d0055803200c80d2121030191420105100d80100d00d0882c180803419030400131a4000a800243e13069803861609500b00302e19603a01900041100074261440301070343e6003c1c0040d0f03014651100f001c480d034050b81c1c02c0040140c4002e4034180ca43c1c1c01015000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442604793 1250 442603543 442603549
    0xf08010b040e031317010e01050a0c020c0a06140f07050d020f10091e060b0913030806090408161b08010605040509060f070c03020102121f1406070f140624 68
    0x501c1c1d100c41003010b010440d50500350f091700d5281115840e2202592a11151007100700c0038040c00f03100d00e40b41040090440c0000e60000c0c501320b0840b40680c015289000c081c0f2116a20100c8520030940b03d86582d5130780c012400b0041c039288109000034150307000b51b2260340f6075140e002c01c00d00300f00304640381124040303201e030313020b040c21107941d058000e00a11000440014040c1c0d20821000c18034090900013891b2546100800c1c2c54010448030032005054448900d000c050304003100e15001181910003800720301d0590780d06107181c490b041d1800302c404907400a81007081100010b0441403441407484035811a078034420039000c1c2001d4004d02c0c1c419410b1000058a201e00010114403542c080400c010290301c078130300705807110302c80e1410940844d5000c00540580380d1342c030700040740118541e01c400401c40f0302d00e940b2160403a459130468426a1050441340030203540700b0003510019a0400104802844540382c540202c0c100100c40306a140214003c1280c164035011580c0e040349180003080080748115410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442606043 1250 442604793 442604797
    0x1e03071401050613050402030304050a080d030c0c1208100503070f050102060a091a0c090402120601030f0e060115022503140c090f06040b0a0e060406120b0a090c0f08010b040e03 78
    0x11908060758104c4251180b0b5180c0096402c00d0003c0c0a0b0385c5002d07160404541b410742160060300302a4001c1e92404141c030703814410a540b8291620309142061455596000180248041e40e4100103145011a0390451910340401c01020001c0403180000d070740387c003649240150782c4580d03030150043d0000100b071122a0b0140c2d0040a80c44003010040c0010304000b40004a00a040000744103000d201000e00c58945200500714401102c8504106191000004040e9400c03151010603880c101540c064034407600140c0c03681900c5204c90032180c80d41c00b00f1402c80c0b900c419411010540103681008502d03210900161a05603030103508103003d10f1507aa004560340310000d6284c60381005c8144001200c2ea2105543d90340c11400041000c0f5464900c0c1000400002c000d40111810060358014041c01e0307d014441d44008001600880c0d03952070f055150ba152500004002c2500c01b074948980504004001d00032401a16140701c0e024121503c51043c3d80c003c10140340c5240c0110b00c0d15040d40c19172000001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442607293 1250 442606043 442606051
    0x201051b0304081902071703030a1a0a03080a0c02031b0f0a18050408040315051014090c030a0905070e071409030c041a03010f0b0a06110604060507021e0307140105 72
    0x4140c40c58072130344204030b0100c1c0070303001214000c40c0200000400c1c00054000a4160700a10703c00460701c0b03040c8040a44101c030216640c521041480d0000c80c41c058681e961800120380d0400905621000d8141c0f0549031742c41d045c0c50003545405980b6401c80c03002503645c0c038100c1c1e5440c05d07148012102181000d0010004503400b5001440340ca128a049035900d482d0030a5134410700c9440b1040c103003540c07a9a120b066900c40c030822280314dd10348080040100e1501174a00051003c802054688912840816003034074001e02805a00003001000502c010140c0e00105685544841180d402e15a125005101d8803001d41c2d042d40002c58035011458641105001c1d6684100010098420034407500c04000040c200441081c4050712000349200d01390f9401c1c03140c1519940703900b10204c0c28000c0301080001c9418150045030501660317003e054529980014866031043d8000c1000800e5113411806034a00303511607440d102a4034003504280b140c600c010020b0b00240307201d1b0941c00000000c0c0111542a10001c607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442608543 1250 442607293 442607303
    0x4111c06051501170916170d0509180604090b18010c0503010303092105031c060503010e070608040807021f030b040926040803040816060c210201020909070201051b0304 74
    0x19011644c42458a00560b0024100b80485100346aa000c0c0e45590788142e0340410740900c00061100c41030441449184001c1141b0314003030b03280001c000009801d40b00d02884198090b000c04002034250f131603a5000ca22115042041001e02d03241078800754242c0643c1ca80540346035401e002100102c40e000f141568142c1c0d9054540c0e09429091a51304d040716150000540865043c100e103240100345c060005000c2e4108404a800b613408040c1c03404015660325501090080e0b16161181800510200d11340d015a1070b58600740845480b641031040c024060401c011b54030804034100c0d040070a0000442c0f554001d01a01c080c412100f5010811040300d4a6220141a02032591180804900d11094800000c4020055030f400c1070f444688079461074109802445050307020350790103560700750604d2018000b07250a240812410b56190754540000c612020188001110a01300641c054001c0d0151022840302400c10500741c64140c0c0004c0c041c00d0309940b0080c0000c903062036060200c10b040220781c840c64100e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442609793 1250 442608543 442608557
    0x63411010305070e040606091a12160903060c020709050901330909080304330f060b03040303090209070c030c0b1b040905040b01121a04111c06051501 66
    0x15030281100800c8102000f07440742d052016940c540c4240b501620181c8d95040e851428844584260400000c4107541d562003070011003035094244441941c40820041e1034601003000003000d4544402913000108442e052920111b00f0319800540700c8102d580b0b440302030005840b0704000030301329140c04044610640e0b05c0095001d224218480c0c028448034054151810780d0390f40d584440481e243c41d2070071200c804000050000380f0504007508441c01c0d4003840f21844283c0d10081e0b46080d140420201c5101640b601b1144e1212413680c2e100d0340050031040e00a0742e581c40e0a1078018000c2000b041d08920070703407249010980381c51068031070510b01c0f98143c0700c0b0403031101d00d0f0700e400000d050007d0070304482403a8203600c410040700c80006880207100e1110301007500d06042c58a09c40c014016001168004640702844000c60001d00308884500c4503200103a0058841e070800710300300d61741a034400340c12248801000a190950030074908280d4010a8100a00c1e1210807114001a0030b041043c4c2c0080d9107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442611043 1250 442609793 442609823
    0x70f1704030822060f0f0e060f120108010e0303160e040f0216060e0304050d11060705120d06090c0801060305100522060e060d08030910090309050f030607050f090604050634 76
    0x9411f20040400c3c018180c50400b40e4001d0340000592024043c4480300c0f00110042015080c00d0141414034800100910b08500d001c00c6400764030f03004903800c2400c000728045407006940b2160b008010f62040d00c44d0942d91050455140c00380441c02c803c04660080c50070612889881001c801c0c0ca065a5000b4803113425811580c0b81d1291154200c4822070b0300c05070030022140003507400c10550160700c002c00101c917100d8404031800000c4030303c0b0383d208035031007400c4c007400844182e4482110307419500300e81000203440d203402e003681c54420003940141d9017080e2003180c03a05084807185240078081e28142c0f000d012a527101c10b00c914070403a003640d0803600001001720f600e001031011005075510429150445984d01d02c03d10514003602c50000040d0080f503040b2030148918140044914803400098004202605040e0b400604500c030307000f9000a0700310301140c000204d95440040b20014034000b01400e40310301d03e202103002140c441d188240055101c080d035040040861001c950000c0b40c100800651080c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442612293 1250 442611043 442611047
    0x1b06020d1206050a0603091b03022202071a06042417120403150509061905070e060f0c010605120d03020a030b041a15070f1704030822060f0f 62
    0x81c0e403180594154032802c011030940c98a840200c002c100c1c2d540c3c0825400f0140c202006004c0040425400c0449200e0042c130160f120811031407804007100103040c0c0805101c80e44a0001d003d8103030000e11280300c4c21000c2d08000590021280114030841d02008030b000300907024622180c08540054203249100400c00c101030120b0803a00d5400c10040035200b0880e80400704c807807650f020350011192501100d42c05a80b4414500c120703580009030310000c0026061060b01d055003520503210644920b91a400060ba030346101d5500040b0604024242e25150600070031801069000a240c0b59129840d0160018213460b0081102030b580800034003400710040c1c1881d00318041d42c0a402c3d070505040d00c488035440b55071030341c0c82a440c2034504944401c0311030300c92004002c011070140c0e05409401c0c1e001d00041003c0307100c041c480c00c540d9a0104010081341c03480706140e4082d020b81e9102600f403401c0420010100d4003881034400505800211080180303443d12000c1c0c0304c0162129007075002400d0444c55a500718 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442613543 1250 442612293 442612307
    0x1180b03160810081b031608030301060e0d020108132102063c07051314010f030c0914030c150307020c06040e0f09010624080c070210230d0501031b06020d 68
    0x10000f0f007c1c2c0b140b15400c94503400034411544d010100c03d40c00003004200d000c3d4410340700c6280841c00c5600b82000c00d8240c0008040060107001c00c83d0301d04a0303080010070030040000c80c100101c00308501d50441540f400780a5200c14045a400140c034401c1184080c6a9141c400440007526040b50703002c900e4000078003070982a14004241505024042113004001d1521480000007080030210705581c0c9c2c003601380014241c4d40c9030700314441414100500d201034550030403182ca040da030340481101000403600001a25000c03002c03103201d13000490901910111000700c00114030800c100e8084800400311101401064491441402d50408422004c01c041c549041215500904140c0001c00c00c01e4542c0c004411200304055143d10044c5c0c609484135159800c110300691001030508202e003892865000308000c0030042ca500c5042203281d0110382010304482070b69030307006400c1c4035440751562981d968041c020002030101b030350031070000c038110303011448002c180500303584040d800391413400700141080d2152 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442614793 1250 442613543 442613593
    0xa0903140f040302040501032109050f040e070306050106031506050306030a02090402121203011404020705070302190e040c14030c1f140c010606030b100207030201180b0316081008 79
    0x81c0000c0000101681e51030144d60702a50240d09001100108000c640c1c00b060310341100d010500010700020000d0303955440010340c4d00e020660b400725130301254003147c41c20482a6040140180d10380710003c02d940354141d00030316245107034404442c42103844090686d95400111450303981503100408880046c02d280f001c0300e030014409400d4031490300b6004050303803e003001401400b51400000c07004025441d903401ea0705500032403c0d1411481d00300350341c03525500c5105601020f4010b41c00c0c10ba80c82040482072110340018600751012981c0c9040615082d41e54003094491000122107070111f01c40d045c40d000c201100b0307106009003034090020410b50410700d001c40388051601804940d0302842c803020416001800d07000c05020000500c903090610150485240308009801145100600c00390b42d900050804252a0242000d03050200b003200c042c1840040398000100801d000700c18401c1c08040012484044011030700d0f285460b40d43c1c844051a03070b000300e02c1141c43c1130307104200654070705e201c94035607002d0303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442616043 1250 442614793 442614817
    0xb0a030f0e03030702010510120b160e09100302090109060b12041110050c0f060412082508040b1803090d17070b090d03020721030608010509070501080a090314 70
    0x5109104400302d0031030300100c0e140000f40c0d44810402c161020111080005000d0340d1560310f0616000e0340711030001c51070041000d242415414103121005014000181203804000c0c580400c515000f01600101c0341c01e84012401100401e0000c16401c07143d010b00e030140c0c0c805600f05400d0802d160b10940d10340d00c1c0640280e40742c00310040c2c210925212294180441016600c0d40c42d9526a0102c4503403615903d81080c4840e5040041404002000200c3c0c0740c2ea6248540b0b40b9048540319103500300c48240515803603603001814071142c0741a01d41c200050b5441540202500320b0680d803040c40d521000c1e5111011108a50000c1040c0c450a141100c42d09400601603180b1701c001c45030442103d4490f51140070161415014802000301030a410012911110914a010740c00c0c40c0e225520080e201c81c5c3c0d000d40094280ca1800c4581095119034820380c0103018020013030041d0700b09680e00d81d4a82d03040e409a00d0029481900007a18013145008249600341e00d640d074800281508126101503402c03415030302300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442617293 1250 442616043 442616051
    0x1a07110a05130e060c0f0f031503100603060c0e030c1512010b09031b0105030a0e0c03150a06081204030f02180406050105090a2c011401080f070501090b0a030f 70
    0x5550702c501242044250040d6000500b44100100c0035141c0040180403d07501d2004000b00c0c40d03801c05140a40d5420a0520704180d140c1d10f07121480030400403081095900340c82003410481d08864290002e0044a0080b202007103601e450741c00841e00d04100c040b280303826901c020004c40b1541440301110020f05201c8018904051060081ca440c14a0a90003440d81580215860000346014803e002891448041c40c00e501c1350600b001030041e0100404024080380c0c1c80d59001e401030802d208103c00540020141c505802ca1840075041034502504e000541c145000e1000c58161000602184888092409582001c2c655620902d00b645009e00480c0c10901900f9610222252155214026442903001180fa58145420700c99480c400500030b4030018140801150034220714080c41c0d401e0942441d507210340d040c015114a0160244058881c11010a035000164420001c50211051f6001d00240d0381c0b01903955004446a45450151034800c80080100ca0441800395118640751005510041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442618543 1250 442617293 442617299
    0x12020408031902011401061b020d0206070b040b0c090d120306081e0607080c0702040c111515040608070b07020a090603060b040608060108120c0f251a07110a 69
    0x90708642141506589211446460218458082c06000d0400c00c00c071400b082c0a41c540b010041608500740e25403483d40324200d000f501035482d004100480c01e03401802c525071791001440d00603034004044509807404d81003140803d051001900482e0880000280020400c2c41241c80d104c1c91014000c107224113140d55082c00164043d0103001210620070701804007040e10206030507103420b00500500441c10420000104141040440f084c0c0e04010b4040d41d001a08034034041003a161881c2e0090039071003504c1030940401c860040328030418855140001c41c06131840c071010500007079800b90700420100340c108503401e10244a106000d401180c0c001040c1d042825a04d550007821100c0302d40064803010345a10040300d07242007501540300100b50090081c41e1a40c0340040058603522039010080140f00001b03079124802e01c08004503000d0920203404d403414911052151050784420741e50031090241c00f0200010480400e0581d07404140e0f40e4101e0526145180c0d0700c0400321080b2080b42a03022042c04404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442619793 1250 442618543 442618559
    0x8190e1c0207080d0203190f0212040b0a120b030a031103070c0e090105060a03120507060b0a0f1505070302150603010e1c0e090108250b0a050a1b050d120204 69
    0x216034082441d4015022403800d00019038200201c2000507030956000b000200300c48040b003d82c5039080c2c0d1031b41c50b012982850001080b820250b504440051280f404070b000314080e91183d004000a1042ea120743c0210001344403190255292025030b43c5d8150411000040820700031389a45d140720304080c007920301d0882c999840018a0000750410388003259000c0410100c03030000d100c3e071900000202d0b0f8a60f402c83c6156501d5040068403006101041300205480c0204880e0750000041d03064010174015043d40c5900c0c03400c61050300e0344120107030707016842c05910f9000e005000300c400360358142e40a01424070380740e4507407050040040c0960b07426641c0c170580b1b84800c01c8103101d0701c0511800414070011050f1140d00081c4644030b0b488800c0d01c07070038948004000004c0f0000f0400d6001c41c02050310b070800b6070203004035034550041d603000030020303c000110b640c882540407004081501461b1210200102c8400b005580041d104034010020391250198440060241d00c0b01508015080070251520381c44042c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442621043 1250 442619793 442619833
    0xb0f0a12021f021c11060103061107051203060a0f0f05210604030309050d2d02120c25061709030d09050708012301090c051306050304021008190e 64
    0x12060058100b100c4c41c21121007041d980c8250750005103080380742d0f020610441a121401840020308442d07a44800300346142001b8203442c000c0c0c2e04441aa10001d00007582c01d8070a6008640301031140d5a94100400c0c58086000082c041c0e0306001c0b100034545080105010155510b1800e40a440600074610400408100711407480340d4401d903000300c3c0c6034442d17251031854000301802c454180541d078540000b201c102200001c00100402c8080130003114a243c007030307062124549040910000000e850010b6800000355040d40f101c068810300629000e00910b0198992180952070000c5c4c000701c4130f100010801d090f036a400c40d9019007030303a1138902020202ca040b82c0c11840e0480d0f4a811416082207110828890120041d40512003601c81d05c450300103860b0813441c14018101c0c0190354690001000f48a07809881c51815444140e601d0b642c0c440354060001d41040350200d01c80d0481d80c0940d01c9013403144440c80d001c4d40a030506410840596000d04c80030340003445041640b0711549400c40080112014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442622293 1250 442621043 442621099
    0x9040c050a0b0c10020310030f0c0306091217070522080327040c17040204110c0d031104080c010c0314042706030c09090f0f121d0603012709050c03010b0f0a1202 71
    0x1480801112103d50050812452200e080c04071940c02010040d84301e402034121148036410803d06182000070072080c082094054205800911000c01c0e130040c01c4107840d04e400500301324401c446070f507030300c0002c108400e55503208101000a1803201025400152903040503801603c010800300707980703503803042c115119000001c00e10500d40c800d07402044020b405104807404642813180317071860b007410948450303550a00401c003181000044450542410303c40c415181c1c01d2f02207440290b039110395903c01c80040641e680000c40041160340000c181c170038031a100d0341040340d074481800d42140d45002c4001c3c00600350564142d0b035046079400404001000d200341d0181c030601c0754030949104640440010444810a80503420702000000308000607510030050328111504000c400c0c070740c031412205500120b4800d00da050b000c0e605043d4190208207000c03840b003540d480c065008100c04214401000400c0700340c80c2c034031070308180513000c1480300d8214040c01c055041d0001d82948040284003903400d43c6007140321 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442623543 1250 442622293 442622303
    0x1a131a0106030b010c0203030306060f0706020301060c1101020d140f040e0109020711031911060702030d0c0b0a021305060c0a0c09020c060c070201020c09040c050a0b0c10020310030f0c030609 84
    0x1001401041d0b014890070b61581000c0c82e0100c0ca192503a03002c25664400134264030306c9400041904044520300178122005a64804000e5442e541c0d1550050550b2059400441c0c800b05a011001d000e948000b0700604071100c42c0e9a02ca82044d01c03d41042c0043e07100340c8a054100f031003000040341400719070705103034000c100009005070398062a003041e154003d90050202d20942000c1100d032528005900481062a0000c0c820288440303c1d600103001449000e0000350580641a154803221760413024000c1000c2c003a21344400141d54940c040c0c030403440f54003090b070054100b40701e05200c54100301000d0701000710700f8021914401c0c1c254503441507150282d07100c62070f15600040c0d40341c805e000501c00b080e003104401d42c5080c102455540044d4031046c1404070107006004581c001010b2000b1178a1660041c84003a1081d9801600c07051014074036407220407a6141032081c00b00450000c8814130850b8800e24060080e138034001e0a5544031441c002031484e0540d1a25000c0c0b1010000c1902c0c0d101d80d071041440f42c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442624793 1250 442623543 442623593
    0xa0f0f09050901060b0d020f12040f121e080903070501050112050c100c080c100204080d081302030d0f020313090c030509010605010503221202010204031b031a13 71
    0x20500c00c080d58001400e01080340d050100c1041503000c000190b5600e20003c03280541ca440e04501c03072414500858031281021a001c0d0144024444582840c242e914061400310211521a100940320740c5266550340c0075807004501d242850b04d01c14040ca5401842e440252840c04000c0e0b1101070075582c082e044206841130110410003000000c00c034240002c0b1050316900c0764458401c6010b064030700d80120103018120001048200f582d001e205154000304036050464646844440c1c0e070361346240381400940411851170104603014050b42c540c0201c2ca0f40180240303603e4a500385c00b12008156075000405510041c4a41c1480c10849101400038084100c80007550078a052401016074002603d282c9903645020070600007640d000040703076800f60790b03004040008044240f440d0501024040003401300041d12140c502c10a81c190001c03c1124002c002e41c030201107803500200ba0560386440024121083c96031804609034401084680c4004030f22000c0e5000500e9840703403003102054044000d191008 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442625899 1106 442624793 442624799
    0xc030402042306040f02120610020a05011a150a02121803030f0711060424030605090711120c031e040512060709090506060a0e0a0f0f 59
    0x12282202d009031824040300c55840010788241d03200d60b00302a461518a1194001d49614142d104c03840101074503110300b045500540d581c0541c0a40c000c0480c201d003c0784c0203120301d10380f403121a0421003d10150303204015211390f48102c00780038960240440000c590380003603220244041a883c182d5a481d04154400e103841e8450aa80c1d818803000401d020060054400742c1411032051454444040303058081240d180541e00403806d05c0c0e807044202d8040e0359042c5c0a403025492846c18002440d949030004960024030803a007900c04281c6001248d0380a0f401041b5000b5160901e2005a04010030422140e03121b102d1010001442c9042042925000a00100322001044020610080380c07a1100d40d25032160411140507000c0707218103600141c0c2c1d011602880e4402c0200400f101e180c5003d0038400e40b040c400d401c03215a0442c6d9011004038624404071156806400c01114910903685 = true := by decide +kernel

theorem cover : BRFrame.Cov 442446043 442625899 := by
  have h0 := BRFrame.cov_init 442446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442446043 ≤ n) (h2 : n < 442625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
