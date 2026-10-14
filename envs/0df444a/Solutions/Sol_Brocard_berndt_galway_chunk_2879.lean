-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2879
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:00:59.304379+00:00
-- url     : https://prove2.me/submissions/bd08ae29-530e-495b-90fa-73a2293b62f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 517625899 ≤ n < 517805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 517627149 1250 517625899 517625923
    0x506090a2f280b04051003110904051920030406091703190518100203060102120d0c09052209020a05040906050709060c020d020f06131701200316050c 66
    0x80c40c1d022020b407141c40b111150081c021400218030b030030b0610001c1001e0342031040408050545070340c0900c0303010f04680152400366030060020001c034a803515903a07030403c0d80400003441c4145044600620701701819131242c05091a605401d00e1038031182c0d2803c0090001780b40596400791248600d81c035182001b0019801001c3c1c09400c9154001402c02c40e100311000a486421010003100150b840c0f560081155240000020700042e2207650b0000182e0400c81515281c207008a0009000c14681c9503540c021802c10740d0584e00c000d2819190424040602101403da1002d05103450f00910390b900c880d0070140e0f02a1010348030010703041d41da002180079181101022501c4c0d542300c0c001c00c1f11403036000340c000c001041c181c50014000e405580101311740e0743c072080c0041e00958440d8403104030340d1248021074030b940401d8004902403e50360a103210000c002c9100e12109035080c2111844100780740805a40283c504111a40c5951101901603060003000711007001880002e01955414100511000c64102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 517628399 1250 517627149 517627189
    0x3080d0617062403062701060305030d0b030d080f07170103111207140402030c0c030c060a1404080a1209050714040501050d050a020d051f090506090a2f 67
    0x4240303c00d41110720b440580602015408941c03140c80c50703580020300c16402c00802c440c2c003900325000d0003000e040707108035500d500b007190300b452030020800200000502110486890403c500705990080585a5074880b540c1800200b586011030500c014880e0390b90303001001da060040e0013100020a01b046c3c020242d2042d80c40000f02a0001300604210f030720081f078045018042c1400da410111400841c21031182400d0080768044005501314540808032102821144202c03031302d0f5000400b5065550004a48a414140c00d058004c4501c11040c00410f0140742d000c0001d07400e00107611000c450030b07000c01e070386010095122880032020540903c040340181100c5001c00c40228029401e200540d40b069100c14000c096202880000c5040800ea076035035039074100e404080c0f030459418501e24000c0341d104000d04401201e82c040380041400d600c5a00d0017407242003907a40c0d42c1d4074000500d80b1145400b0001d07001000170307810800c1c084102690345051041707107600940c10388007a8020a400800c0c903260040c0741 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 517629649 1250 517628399 517628401
    0x706050a0314072c1c02030a050109080301080f03030933191103060d02041814070302040c110604021c0c0803030702071514030411090f0402040f0c080103080d061706 73
    0x301c80031030044040300c801030102c0c00c3c0c0c130320f40c0e0b001090b10b0341d0307a0184105800690013035220441d54280003801d1300d107030004002e0200e0b00b5a4209440c590b0300a110b1000c2c40d200748840b0903880780011050380e226483c83d401070009110903040410310100840c005a01c452200801102c840d20508451401650407104a41ea50344903103070100215042c85002400c06101031040001694450707005c2217271a82e044d84e01081c884036001582000c110b00d181c0c0200030786900101803094600c001031400c100d80c002c503414011900740380c100303a942c00d05840007031425800400c0024058141248040294070040d0b101000400803604c1d0250805c60075044041140c2000050141d01581006200080c01e00c1137101c4640c03043c540400390240f0107030000d82d510b44802000040a000c222440e10a0302078011300010240d10300305140601901c1e088808900c02c038031382000070811103c03510030400804c9072502c030054075074250788552800c1d41040b4400b000060716160081041400e115003401c00340000301c010005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 517630899 1250 517629649 517629677
    0x120807020d02120426121201060c0f14071802070c0605030c070318050d03020f1e100b03031303031d041a241306030501080307050706050a031407 64
    0x2801a910840011580401081e209000020301228200c406880701d03000c511903070a9441200300444076600364580100d0709440e045010540017481c102c407047d20020139503a2211403d031a0204403c00140421001105040009000000303168000488400b00e6481c0c9681e11220880c2007400d2071490061030300498144100221034000301c0261055080c0a400d43c985992000300c00e0081c04409820003160310b01301c00802c120300c80c190018020150600d0b90070000303420080e540e0862240c6592051290021825102c0c6110318854011070305003000e02459802c2200c3d074405044039500c0641c2c1408100030a0308004c0084060000441c407030344480342c6109500d0780846024203601000da018604000745120811a148200741c030702c0c881201c1c2c44041e20785810500708040c24411240364202000166164001ca0107451002101c881d50f400380850382e21002d03255128024480020601d07881100140f103110b006030050114106145400110305c0000400c00e00340c200140c4109010520301100310701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 517632149 1250 517630899 517630903
    0x901120c0e04080712030b030724020606010912050c090103050d0f020a1511090306010b0316030603080307031e1a0103050c0307020c060a020703080408071d09030d02130312080702 79
    0x4010030340354000d003039a880d26072540f02c914414200d0051203046070912200e40c0500a510040c0c0310705018044485141c1ca03100300e198000c0c0c0707410001070a440301d400030300352070b520000d8510310960040e515031010520b0250b02c8420304402c89411562130090302940c0a0301d440b60150300e40254092801814826100203001e00a80c00c5100e01904540042c103100d8081110180d208045001800300000c1d01c2542c0507083c4024041c400115074140640d10002601b10000c00c007940c021021800c0c14102a414040d060f01122400d200091009405000082c0d119029030b110090200043c0f0340c0d00504006001c5140443c1d4020346016081a01040c0310812944d0520a031079020040b070141618604200d24040d40c0c0d00040610300b40300c1c6400060080d0054820300801000b076501c50720031030300d0b641c59140c815203034003040c0509500039081c1c40c124140d1602180303800703020b0000880034618010019220f80d010b5481042d95540c4c3c4600c4107400000503c0742010b1148401c00e81c0d1f03c254003070800190085c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 517633399 1250 517632149 517632173
    0x903120414061e280924140906040f0b030406110403051902010e042906120f0402030c0d0b040219180509011d061906141e090112 57
    0x601414003440610780c404003074801c100c0509400350031a07403580c1d900071444809100c074140e281c18210203900c14014294000c0d003450181c542c250702c920407506c60035001c44080c140204120001403007540c1403519050465000b8008400702a0000e0f140c00c2d05c0d681d9410400c0100c0d070004001d4400003080200303210461103114002424030307540a1400c0d1458650580d034548410700820b000400804090071a802000c02c0821414003900500081c203004ca613085103114040f81000d584132041c00c0c242143c0c50000201c52600c07403100c403401480d8079815802083c41c40d00400482c1c01d440342c50b20440300e5958140c9031880305071080b00c2110710b903d0a84103010074104061442d10030341c0400700040c40350b00c20fa89181003540120200c001095a1007038000c0d0b0150000000e50f007101261032161940112000c0f90907846100401c1e82c0001c144505540038045403a1031060314060a4144c1c1c030341c15246000d0602a251255012070603618007507503400211080c5003a484800011074684448042040e01807400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 517634649 1250 517633399 517633439
    0x503030403090602030711101724030102130e040f061103070e0a050a210606171608061602032205040c081303140403050613060e06101a09031204 64
    0x16508104061fa9450340c3e034407130391008a12803c50501c04000880c0301d8145180d0801d41200320204504020200c1c0642407112418400c0c5084908418682410b050003111b80701a10710708000c0c02d0a140448402c0001000b900031030710340700540d4203640460480d000742071980084280607652420403c4000d4098001180300382d0180c0560b040030841a03558103109402c48194521040910114205580095150800040046240c84c1e03000c030705c0700d050900c00c64086114408035800704420b0040c43d41700850782d22441d200c1c1d500213000103050000309a8011080c0700e4030b004480c2468186004041c40b6404c24402d07600502c0d0f4103000b007100345042c0c068070820120a041c031075920f0801500d1010030b01c100440150511542044017081024403004441c000d40d006402d1718100d050100662690001c9014140c1d4490b0424420340a060300c00301d801340c000e00400300903201d0945065607013600c800e12554401d8515070148400203550714140a043c10310741400c468155501d041400b030030700340d0360400c0d20f03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 517635899 1250 517634649 517634653
    0x270a06020610060f02030c031303021518010c2907020709090b160c12030209090a0c020c130b1207030624180f0c1e141815070503030403090602 63
    0x240003450b441601a001695a2031405004224203800d00f03070716500c1741d950719032103d11000440c2941019401215030a4a1088801c1551564500011040f9010b000a035200003640d00f00c50513035135805030314120b8405200300c0d0a12100c13040e840d002000b1141104030700d61030312100c03030800100350350502000015080503c020071050880c0d03283c2c03440390a0020100c411003882040c03848003141c020079045165640c0649407a0081d015142c0080103500504c80d03550145003440081072030000540a13521743c5054950051018507405802c202007070407010003100c2c1c010394407030840007962100d42c2d260200c07680c040300501c0c80c01d145140c042d0840701035101030300000c1c04030074106052080c0f8802034000c40c3d21003400595601220b81c007240c0101203400174180c0242c60010740740d110a4110b40601c0929629161242e01210480c800b42c412030768150f080d10060310204034454040d05103110f0f4811410010f88041081106010056500e910050040d030306540048100401c01d680000400040e101c1880 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 517637149 1250 517635899 517635901
    0x9010c05070201031a04020a0f180312030518030c010603050c0406030b06090901021c1e06150c0812040809090a0e0607080c2206110c0d020411270a060206 68
    0x2600400030300421600038101a140d424082403010140c0da1810600c1006104556905064101528043c500002880420440c950007003100c031171300621008803608881904d04010540c40200c000300700041021050b6100c040302c1c0b003024442040604003c9415030000640c01d403d6042481ca881a070001c2d0920031400c000042c8001101400140e411440a45001440b502d132000c8690281c05180311411001c40120b01c00b81f00051250001d204c01901d1400c1d016109000124030030070b544403401402040c400556017440044e20484041e009e05004080c1075042020010072a0103000061b05c0503110500c020030842100e14080b81d80e01d030040c04e6081e0811854071045481d586820008203080e0a12060a00180c2c1c181c05c0d0b43c0c11201d80040b001074a40001180009407401040c050180100088800360052140c5030001000c0c80403010090100c0c800c03624582c200400b82444080403820300c0b0041c802c00a81d400030090724071075064122600301205049070103014a054065105000b10350000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 517638399 1250 517637149 517637171
    0xa030c02101b120203060d020d0317040501052707051203070803010e01142d0105090d0302061902131802040503030d0e061b0a03150f0303030e1011040b07062d050901 73
    0x11f0511101136030705455007042c0013400d041c2a510100080c108147c1a00107000b003004106040d4801d52203a10899465007240e40b800d151100c907400800c0f10140f40c0e610145041c00245402c062840b010b5031102e003104d10b4401965914400760700281d0220324454160001030106900b80c0b1341c2454000f80c156400c881780004640c24100300d40c0c2c0103013040c080c41d03003140b0340f05c245901c40c008491203080007802d11100b82015140080d038641c001c5030b86a000701010000111023210358021030f41d4040c04000d00d1800d403402c11001c80e00c8404128540312103160708200000305901c0900c09010000e415840000702040ca440826080032001042541d000c0c1c10343c11071160005412068509040c81460300150003800c2860100c246400e98010240d03500008038004200360345504103e9800c1c4402e01940c058140d1b84800c0e00075030356000745c4c2c44d068850501051040c9440c54000c0c103c0e13940600300200d1182e00b04001c801c09020035180b08248440038200840104009008840d000070300140200003541800b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 517639649 1250 517638399 517638409
    0x180f0307090506010302120c1224092e03060b1503071b021237031206050409060e0f0c1f03060302030f0105010f0602030a050a030c02101b12020306 65
    0x2900500007099a03440c08503405900ca03905884002c890364613400315508100c1402c6485401182c08403640d10103400014140c1e081421b10940c1030b849044000e903000e441c040070418400c200504d559040341401950b5203d0360300ae00101c40300c1c10354009c049080349085017000030030748902d00d80890107403040e9041d640359200c069085035070202e181e2403d409181c2a04071044034103031104001943c80500300010343c40c0c402000c14000043c0c00c0d13220284050f508070003a20010030f08241e0f6001c400607162070321031003c41d005804001c9520746125000449545850001c1d0031905120000d540309135403a405151018000c101090b0900d100c000100284e011000c0013440f0380d018800410782c00c000340d07600c428039a8003d402242c0070303642c020182c03010170500c030412034000e003024843c07200c071241e030004002003072030000c01101c0e50300d0030582e6964a40010891b040e0301505009000008501c52104902c24110051041d183c002c42021088894900e40002c01802102c0800c0c60602152040007800855503903 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 517640899 1250 517639649 517639663
    0xc0311030a08070503041e080a1101060b12092a10081303050a0e0414040b06060a0c02010302071e0309080c031b33033312160605180f03 60
    0x1d134507040d0f81c0d82d5114500a40d49400042c02049940019510340f010486d030903029169501260b903864184050084907207007070702c04500c503003214080d00b007104100011040407410f5000080c0c008541d00c10507150609201602d40e00c0ca4200f500740411403903446442c24110340410300d03943c0d10b030a500900300740521440818082d503009003441800038035a44504d0080203c3c08010700024000c001480c5202c007903c040102c1140d0481c0c810108030001341007031800900791004041150b80b406048500c581c0150700a43c0a4a016a084161400005d0741c61020000d5000840c0c8a0354600c0c2084d4030341854185000c07001250544690041104901c01d50f85019070007003d4001100d030b0518150500a04a10002e40d01211300b83c4407660342005129007640030029406840303c10314002c81c09903401d8080400704040a4042846085d00b1ba01040e280b034921031100141c842c0f641694041c0c001a080c0c0c107102d1b10700d540004042000828403912407103500961076100d9506076030720034904494400103515117030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 517642149 1250 517640899 517640911
    0xd020108061306091118030102120406050402060d090524160518091e09030301050a0e060f040c09091a0904080a110d0509101713020d120c0311030a08 66
    0x5452694210320380c000e0300860003d01804100304220802045c043c91158448103c0051580b1101113091a606051003202c0c00300307182710541022611950340f80700c0945000f50050b80e0000c01403003408102581c034821000706520520080c15001c500c4090200744081c0c055038101940b00300800c02054207000125500812090325000d9a02e401c0c0c0401c07295901d410f0019036400c444c44000f0062241c0c140c1c42c0c50565100c1300c0300e501c0d945a03980344000e50340344024001d043c0c100200c00820400c2180c24491503807c1140200300a5806480c44045011110b00c0c104010008101c0c801c10080032105103d10a407000c2422294221041c084012420008004d400180b100c80001820250944501e0030800365043d24002d6545c451120b500003081d07a0403500c00315204a004c035403508144e500030450310036215141004120995601107400788a5000042c099130007400f2102010000343d1000740c1403008100303d8450010071000b909004111882c6400e40d2011940100110881603401c503034501d03032000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 517643399 1250 517642149 517642159
    0x9070509040b0406260f01110a110a05010903050418050124170717070318020105030705040e0103052103070509090621010e0c010f080c030a06080a03020307050c0d02010806 76
    0xb11034400450300a080941c00b10403259107841c0d0010703100601404283c1c001184004868600c0ca517658514202ca008000c500c0c00000300300030504050380140443e00c409803000040d101c503501c103900c41c00d0030b65119200440024400003000d01c5000d11080d9492107101c0f22907403c00c40c0758100001107840c0e20740d02c03400051989901c03109001840c8140b00e44415034622550b0031032075050848000d40007102c00f40400580e4466000041d0110b8400d100319123682c803100c5a489000d1202e5001999a5032003c0d101504001c0c00708004a5040702d0302c09401e0085114000405030340806440c0d0595400b007142e41442c0100c03080ac140310110354040280d400114044a01040640354907000a20400c05002081c0045401000610b8a548198032090002501700c0640361100000380044500070001082d140c04118142d01207540e101c3c00e40f0245600c03c10f01000007030307a59290700159280942810040340164030002d0218100101403001c0d040d60402030300c0000d00129281d00280c68a100141014007070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 517644649 1250 517643399 517643411
    0x30a0c110c03030f0d02160f0c050103090305070b07021213050306070e0d060e01060e070c050114060d2004020408062a04120f1b05031912050703021005070903020f0907050904 77
    0x41880740e1b0403200395071b001000f00049062070345000e0010350290013098514854903d00000c00c3d5000f40281c441d504da03d40c2e00c6d1442e00d12169a5000c1011000d0003000442c86501044030081d800400140b20084c1c560700301d1008907180100701458500010140c0003081910a0b0712003c640301d401a002d00d0300d81c01500868506506091540100295400300200d4100c0303009024400d908510500c010ba80540024003480359521210900024250340d80d43c0c000b4002c08007035010918a01d240b6010210b140104890310004134001400ea8020f6001070200303401030420711100c408243e0303000f468100482c01e071340788c0c1803100820032089004501c41d1641000110fa00f000400082540071502103a1040038107005d0824540180c15504250060502074422980300d0421040d565038210840c070f5101e90324a03001040705108640a4204090840030b612800c1c2940f080c10910b4024503101da0020340e1036403200c500d075004000402c148000a54001e0000c4410310072020740c031808942c4a110700313076004284 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 517645899 1250 517644649 517644667
    0x5130b1e07170f03011e050f0d0501090c06111905030a0e011b05010b010e15220810200a09090b01140708030603060906010e01050d0206040902030a0c110c03030f 71
    0xe4082c24800c1069049000030719a8070100010001d0360580748403902c00240744030642e424080b040078a0190a911890b5000300a003146400c0c42c5028600c0e10403000030641e5042c690b106000e0040036004800410520801c5000c408010054a08820005000410501c00380d0322903076103e2003107045034005c0183c3c41108030038a034000c14a04881540c0c480c0602d600c04810b0400b00c0c028100940080c0c0081c1d37640b4010341152504424103107249216844e12803914400c3d9124034000300d00800c0000c1c00300f400c030400003200201402103507104610a10049803e40788502c0054070302842440313401c00620144898640c0550011011041d123016040002e141d580f480d0060742c207150b46000d00c0903e032400081c040200a80d444c05580180002d400302c0e0116151854a540c0b80c000134003030242c40403103120040005142c851040c851543c0050805c1d03103400e0300c40412206030386c011106050f915454181468a403035000e1030344d40d0040e0928000e82058112000000c5c0c42e8858420b81031510f140128200c03030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 517647149 1250 517645899 517645913
    0xd0f050a0c03170403031e0902060912010b090f01060807050a021e190822031205071106070f021f0e0105130e0403080703150b1c1b05130b1e07 63
    0x41e1000b0710594002c200c0c80c4c0342c0703001405441c68100a1250500c1c2c81c01e20b50708010280102c03480a90300401c80c6043c4580c2c2e00034440110b06114a401a564032000208015140c14041c9405910000c0025040d98100b1401405900016204c01d00300801080020a084e6021800000314401070070203284199141d082c00789019144800c5200040d0614060070400100e1002441580f50341d0303141800c800d17107103000c403410b8800c54400a00a0076840c01c0c1240310622520003060042c2c803030025034013000700c410045200c64001441c1120b40009031109403040d0301c0c0c0703411b01003061000042c81c1910182c0ca070000501030710075030138040e06016002c910310404014008550028028500248800b0303c1e007424020b00268090391007c000c240b0b00080d421020455411040c15203140781205890501c080c440151030b405040c490040381c40c0e036180e0001e4085070380b8042401803091661340f191108500c1801440c440200c0d840b44c0b0380d240c010408140c140c49040d034000600c0405154a0b42c03114036505041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 517648399 1250 517647149 517647167
    0x31621050a06050613030b06040c020a0807050313090c0305060409030e04180602030c03100b0c03070821090601260a03050a020f03030a0c030f0504031d06040504021b0d0f050a0c03 79
    0x1a034052004202c1700c0241008141403004c40f0700600c5100502e49540c018407044035401506080180c1001c01f000004c62000401045154892000c5a203850050a103d402186158000f000140e4448910402c2e0075458000c450f0801c80c111010404034a41c1e82e001341c5800740c00000940655103400b03040d00c03120800840c205156411036825503032031070500160307801e82d40f040745c00b0b0085041840c0d021841c014180140ca484408020085240000585034600140c104030390300402c00807403503060b00143e58500c100d203000d6280000280041d50404400010040450070b4081c10f00c1420424902c288600041e0100b081d5058107200703513030703841045089042152030b0001610900c000000d00955900c0c66010380344605603583c1c1000190500740c1d0003070581d1003d807406400980583c185002180d410030000c0050070004000ca4030303195495001c2002d0381c02080340d4030012074007000b40895180041c02018411441450124003210411002810301d0194034003850402c0054002e050415026111107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 517649649 1250 517648399 517648409
    0xa140a0e1e0301110703180b04140a03060c02012c0715050f030106090303020607050304080a080a0b0d06090209100b030112060621060e070f050f0a0e0c031621050a06 73
    0x20300c40d20009490113030466224680882c0000d901e000100407070122540c0203000e4454060b01c852034149801140380c000a40010101d921024025002000520030300c10325114850580021401541191a90240101f404075001002c0b1003600810a400c60101d8407805a508c10300b140443e00d1600c07002100c02d402907003010004101c0020012a11641103903c0104880c469403c80b09130781e41d055007c98a40c001914010300303085003407280030f07a440d000e80f00c125407041000038009010099031000030003658080000351500c40d9104001001c0d42410000980e01403400071103251030914100c0c001e1100e2205203d00c080000b44440c02c041005904e400940090004e10408070008450710310055402c118840203c640e0361130300012810555010400d1000c48890040661800f440c080911980822040481d603101200321008034070340c40400c440e00d00502e0141340c62506e0b41780440c0304040308410070407082c0a200010301d08a00802004910398024010410003003200e03202c0f401c800c0d02408041d084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 517650899 1250 517649649 517649651
    0x1003050907030f150c030c0504060c050a020a090c1b02010503060607080f070c051215010b1b01020a11100501050319080d05152701030206031b040b0a140a0e1e0301 72
    0x7408140010380f5482041c0c44283e034005c1190701c040e07840940403a0b04c12484d540100e5800d00041010500030144100e290703004d0000c1d508441559070004511400c1c0da0407000030699241d2000340e5090b480b954840220392445120030600310b080e0006051800020030319440390704000340301420050080d09689a80c001c020207070741c95601604d0701c241080b465004290040c02440346800180380c0008681c0c1018416501441d200e034280140c080e01640a41090700102210300000710565800f480180b50100d01603892104120519481d43d00300240161520301c8079042100602650381e01280000702040b8001d0040f04c3c0141e94074000e04280250f403000c01c0d1403072a1000b0884607044407020303512012011286900e200751401c049001600b058048250b81032998001400181000f000a41c2c201d01e06804078204100340d600070184540c0301d9004203d094901240f210417481d08000d000701030700c0c00008114104112400010316140c5451a4144a0300b0b00442c0d880f8501a1002c07100510040900 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 517652149 1250 517650899 517650923
    0x70627080403121d01030b06090303030112020a0509010b030f070c05030c0106030b0c07050604170405031204060207061d010e06090a0b030f13030c0803151002060a06050301050105100305090703 85
    0x1030000841d00700e48000c1d240030780640102e080c114840e031025001c0a0703102c1480000036065200440081c000c424886130001000c220391076803549e081005c1d42c000c10000d400c0d0710004005105002c0c48901a6004c28042e11080d4014403039052a101036a500c034410f29011499036a031104120b40383c2a42c6640600705020010301218032450641110041d24022841000142c0b9910214200e51140c400040e0954100f4408240000e0041250310540c100e8251600d080a40341c60000e800c00d440062031b0408441c0c001010090290184199002052035081004010340342113071503500c5141a000c0f042c1003040700b41c803803041a070700ca00030703100c11400151491440681343c12590300264410b13030f03c20106081c26800940144030541d01c0800190b40755407142005c102503500c0c10826040a010701d4041d00464206480d25200c11400b000101c0c4164018000c03410f00700400e000315443e640203d4000e034103040041c040d50700e810f50b585406042c280790005203983c03410341e91418003826400041150100d88 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 517653399 1250 517652149 517652153
    0x316090b040e0609010b0405030c01120e0601080312061008040b100308041401110c0f090a0f020f03040b0a0606050f0703020c1314070c0f080c0f0d0f17040206070627 73
    0x380400d1140c503065070310b102c545c2d807220240c84813805207203d09540b561140c03940d89080c0d4499272444660000f840030100b00180280311203800c00400360414081d9a002060302005203140703c00480e000b200585264103002c01d000c000802c0e2280c0100090301c0f2003a6a804280c0600d043c0d8041c60095400500d070544581c0c4803d02004166041d8441e103000681400c0c901c1d42880c408580c6940b049801421000d0340c6404500388904810000d0034550140e6560021030100a00f0b4001405044100b00d81d0598a103031500d0038005a00700988092440c1c1d00d0702009001482e00f000031607452250714003911307031243c03c41d140c12840c0c40711035490250000a110300c1440303090143d400144d08240c6c028240e961650b5807070000c0b81d502241c42409003c500c801054040450100720090248040080c26116403541d41c03a0325500d000b00460320b0038005046003014462150b4008410051046584011606403c1a800240d071034012150085c04403555640d040304c0c40c510301d0030707484540481c001d8007540c001d1042c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 517654649 1250 517653399 517653419
    0x8210702030109200316050f03120708030117031e1803120909160c0f060609050420010c02030a0809120d08070210092103182607020102030316090b04 66
    0x101300d041c0b1400441e0301508142d20300800c80c2c4030703004a5000b40c480741c00d1800f400c101c002042001da2580500411803280b0901e4041e03402001c1e81c0c0c0c002d49001d0303541d500d00404003240b55107014003130030a034009004d8406911718208402c4421000078a0b0305495440150240c038000d80b01080c0d140d814441d41c2c001581070044200504104682212200c01c103540711a11498001341c402142c600148000b00c00c203002400075802c003100c080c01004005440c9032038800340301c104d0340e06544c19590380e44040310b180c00d00b40c080e41d00c12400580a280070003c200c0f855010039a545103422005103400404100c3e041d10384c48411401d031041903d4800c941580282d0540500400d40507613140c8014041c0e04900d844a8500d40030b20501558041c7c4c0e998002d8088050341d11102d02c1041540c0c0405440b00710f03460102050b42420742089000e80c444250241130720750004c1d91221200c0c000d1610720302c00d10091001d81c3c2c000c402d1300d520030f043c0c08120b0101030f0040c40842d03104000d0f400c0085100b4005c41c0101e913910f49 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 517655899 1250 517654649 517654673
    0xc2a09050c03060d030f0903080d0213050105130e04060f02041508070305160f0329030f010504110603040c1203080105090f0c0d0b01050c030a02011b080108210702030109 75
    0x210104115200d0210401d410300c0304951041d08141e880c52043c00091159510101d06d01c298940319400c940c9a6952840300e038004403a0101c0c2c2030700410500122045003018900819003401c0440c40c3c0f02c0c03070460140d4460700f0791045400c2110390400180c10b110085d0440c0c107181803a07540c21540c454070703103c40350354480044522324001522600010310b1b481c000c0c41141d00603c86001b41e070140c422005421141d1442017030100c41015180c0c0c0041000d000c00c2001c00c0d02c4101e81034482008a092441450b01d404400844001039078140003e0001041400c11454000d1400f541d1055503a940c90600400c4003c40b58861440d449600c05120145903200000d135059035030823108003049481d003040e6140104015604900b458004001040c1c0d6544d0543c03003500c0f104810b0500303d08203c0711b80b462a045400400500015035111a10003450380c0011603281c3c0a2402824004410750608100c266180d01c8008000164107000703908488182c500f01c291346555600800900c203008062501c0c07075820380 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 517657149 1250 517655899 517655909
    0xf0d020601320d0809090c04051e060403080a140d0b09010506071110090e0c0705010b090c0a0f090509090703020307060f02190c0b04090b0a15020a02010c2a 69
    0x1882c0c0c0804002400d0504104010040340280c0303a460048220800080040907401220b05442c1080702d05040d484180d40ca80c85143e1000d03189881b04d281030144201040351a40074200e05441c0806e45041c0e03a22942503e060341e410100d607540310142e00005a400b440141c0f540c403800039000c070308803400001c65003080c500c01c0d806582011150342e030341c01404847d014a4800405800c21030440c01424200842c0302c038064555423904c0c140055840f000140ca1000544031010703480700000d000410700200b40501e900c040d605495800441c41d040484c0620340c003408041c0300800c00c0340d62007070403080d01c200880000761100909804490401911150b60b5042c0c600c401c84c007900660800044d142d02800c0f80105840140e0040c2c003100390440c85009101460800c01c0300d00c0d01e21101e02041105034003001d403014060420000905181e100d08109038209594400e00c880700c1d00c0808209060b6000c650700294a60a0030308044203821450310990325921a45240d0124200c8210030907008004610102110 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 517658399 1250 517657149 517657169
    0xd0b09151504112502031c020303040b0f0f010605340201080901020f0d0e0f0d050c0f07050d03120603150614150a1b0c060e090604060807120201020f0d020601 70
    0x14030080c0c00f10605004414801c1020400c00004ca0400e00c0801c039118590b0388010242c0e10b20300340c4010606140c00d154402d0200503400801008104040f1011483d001005035040020500d0308414510070100140030305c004010020801c043d12180c50501181d108210001e4400100000d800009404010800590000c0c007010040f50f001d10040c8200c0c0c5185520000762032508801100c1c0d00c02810300007642107214820413041c8004118180180ca8801c0701c940c3c3c0d000d568059684200d80f9080714510164419000340208010a030b995044000d01076505060031100100c40900c810000c01c215400640000481543d0510f110566440501511112412000001c65140600580602e079445c021900700702049844c00c0b40d07006140e408807800014040360b0381c0c40000d80c0c581c02c22030b06030b90003040800c4800807140503625000818a078401c1d01035074100051847d000c04075a0703445407807086451420700d404020065920170300881c501d19055500315412802d031124000c1d6500c2003486012551 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 517659649 1250 517658399 517658411
    0x1401120201120509060c0c0c03250602010c02030a0807020a0f0302031b0303010b0405010507080d06081501060201020313030f02030f18010e030a03020a1502091305180c0d0b09151504 80
    0x5056203200392402541c0c13120080203d0790303481581600e15400512a04001c1c40f0306443d80c0f5455400704101c1409054190080d0010410901500c0c04c62200340c228a05590501d4526101b1589c0001034400d0100075241c400c0d003070340f121402030341000d81e0f82c0300140c01e285428041d0420b044d0000020801e075421000c0310790745540f6400705152a80400e014440c00350004010402266218a02401c2c10700c0c005c00750203180c19030300b65902c81211056404820140c000091066800403800034441c01003425000951a618050380305480c3c1c03041655000701413084c000d00c18031520780700700240d40d506940442c00d117558030b0300003d52140f04408032480c1170020381c10300d85120f0301742404560062800d505400800c06864242c1e00d00343c0f040039446030b25504660030302c046265543c0d00c4420140706803160307030000f45da4103000f45984c03002108410402e01c15401502044041d031100c03481003554607041490210140c55220301103003000c0c01c0b40c11400064039144144402d1854a00440025282c111420004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 517660899 1250 517659649 517659677
    0xe10120f0908031320010e0918060a0f11090105090904081c140c12070e030a0c09020715061d04080d06032907090e07120e030d0e061512011401120201 66
    0x2045e10340303641c11400200c8450035500541080d849a50700502d11a2801e203290507414115454260704a459490482e2900b41c1c0d000c40340098070402c4141034800100919121400700040d240e03105040e8840c0c01808940001030a002802058039068501041faa0300d03207680025103440039100141d2401414849100407482c400c41080031109006068203c00060b5130f0f03030003810b4420032902c012858060084002c43c40010300d407620f00c500940b82e11000183c8aa155013070074082180c4440310809034500e00341d4140a00c60404014010580e80c0c020208001c0e56146000c2e1514000d00144004042c01c009011082094104500f24082681803050616a147d014480140b01060704d09202003003041d5414028101108602c42e480f802d03506100701c03400c0c0007071040d104071201c060b611003054001150001c2660440d02429007801c8900005003004c0c100640d2500c6900515002c4a01c1400054014121400c00b90055640c80c100c240e1903ea00b9a59040b000ba54059005400c0340003840c1d824601003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 517662149 1250 517660899 517660943
    0x70b0a020a03111507110138030a06110c12130e060d0c03081801020f060a09150f0605011e0207051212190e10120f09080313 55
    0x5040405500410035003000340c5083d20380710b242c41690022030040d43d00d4042503900f0b01540300e000b1182030b6601c884210250f00d140b42151407202c60030a480340d9940e4844400080902412516803802100d40c4441d03a0120000340b030800c419600404581c1044209001501d921014000c030b404004181e85070101070440ba184c0b648910102842008010078041c03000040030788402d548884081e041c00c00500c1c1a454411182c00643e004480ea00d0700050000300484102c003a50301c2c094820b00042000e0401c1182164880f030b402041c03801c51130713030361a5808240070510041c0c42001c010034500f0001c04d4000304072800a84214064a800b01d14052048158050790309040311118486502a125484c1810100032207031107011a1159a807040f1002c800c400f00c1420002c04c107103682000c000d40e0b001d800080103807601c110f000c0344d11300c600b071034601d58201d0a81100000784250014140014800103401c242e10040c14691000742c0032480110401111800080349200c030a801419444250100165008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 517663399 1250 517662149 517662157
    0x3021c0e0d08161205060a030204020c0601092018040908460809010b0613080d030501080d080604060f060201140121030503040503160308010317031003081602130905070b 75
    0x10000480e0201100d00013071a5500c00b071b411a80091a481c0c100b07540c0d03000a0280d0300b1800404286802404c010040c1240610880c80d0f055440c84002024850407143d9807928002d00201082d002580c3d10b02c0320b2155115441154015402881d141e00d13039419aa00044901d14040341214800d4904412a44040e480400d19110300105c916650351880c003900490300b244000d001d00013a0342d07c6141214080d0b9888000c2e11000000b0000707941410700e4611064a019074010703508080c9031a01d00180440000401d9003524000ca48c2458031303240e1a1080800c0050015a01ca0f1800b60040140401c0c2c503079064000f2a041c01110702e40d0102a602e803400c0010807843c001d0550000c4802c0175a1100290064026550150040303050724102071014100120740c00d8904c404a0000303000100500c10413402c810a034456100c130380480703402c6207030043c440782001c03c490002600e00c20000c10142c0c0e0540b20a510415507a60140090fa103100101c0c900e8406440320000031209030045042c045200303540c1c2c905507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 517664649 1250 517663399 517663441
    0xa0b1c053402150c0c150c090d0302030909041a0604060f1202060906030903040812031e090f01111801030b06070807081201080c0a090506030601050103021c0e0d08 72
    0x10260185061005940400c0001ca0065004110410400c04010029a8131a21140c112959100b00076011282441c1141401001e0b8014040611404c040c055082d611015801e030303604482d014450400380d24500410351001c0d40400701004000c100144540304014007500c0d480b04003565100c4c1c034104800e8503154000c8102000c80d600040140c01c08841c1c40101860000d0300740d61403e0f001e900803940980c800c0314104044d45c0002410410081d00708104c102c840c05010302d0f03508505055420700700844107029421a11102c0e68040358403510240b00c1030704c5a0307001b08001c0142c1b480c10414070382c3c603400504581c101d00d030042840c030f14994003074040c0c9000004003d05072440c292030365030303501e1180d003042c107059a10007800d000a102c07106516034018060030303010b0000e26000d60004108250b070b1032075400c1100014101011700034252000640c8070705554007400e025841d074246100d2080d10101051a44100ca1b040010215a2403070119401c1c00d40c030300555524055a40d041d14a629a201401031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 517665899 1250 517664649 517664701
    0x902070305040b07030f300b0d0614090625050901050c060f0f0106090f1a0c0303070804110f300a0c0306230103110a050d06020d0c1b02010804020a0b1c05 68
    0x5101500f541652040302c010070003c2c040035840001340ca03048210bd01806d1040780741840d4205000c0e4480b801c0003150362183c00702604084e070300300c8403840251084803e0341c4003007840404202c03504540c0c051401c0c0d9800144910807a050351600d440142420401580c41102c91800040080340c0244101c022a0a403411828030031760441c5051a640c41d000600413004646040c01d00c0f000050820a0008500a801070f40c3e034451f540c102820046c54800d014544031703100719014440c10085031103514000311442c06145441d074043d142c01e0100080d0b2000800b0300300c0e03907024941c507100030402c002c40008140e0b07020707000822030740c105c0703014181c0b00045c0c002040c02d0980b501001040042c4c04d203100f9229200c0090003082d400c640d20000300b4152074450314100e48594001c214010030b80d08511910a02100350300c2d200d0303204049181c0e00002d80e03901080213410402c0040005080d5103030030390303903400030641003440c5980e40510564452a60390690700010450b8200404142100403819103c1c18102032205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 517667149 1250 517665899 517665977
    0x303060e100608130f0b15031c230d0c030f0b01020c060706020c010516020d08071b11130203090d020f10090302010e0d0207090606090f0902070305040b07030f 70
    0x307080e200300b44014260360484c000d420f0040b0009001c00019581d00f0701c600011022402d2901d0300c541ca684041013007601a600c0340341101c01c40603040400b036140c9200d605210728442e950041c0e40c0d02001d01480500c0e00018001280c2d040429241d000003c00d0490760b50800405443c07943d01805e4070b0410401e140140e2040c1e141110919101008080c101d116401c010f26141d408880142902e9003202d41815446011050b0900546c050085805901c107078030340b007003c502d4441000703440c0307510355034503004040c040d03242ea10100300c00541200701003000101540701c03544c0c01480c0c50740654002c44204019005410241011900001d840c40e140e8034401c0c040d04251550241e50001410b592030142c08643d216049111158400e00013451010300b44d501500b101402e009205003940c10356071000042003030a030410814024580100c006035160940050783e01c80782400c00b182c0c18000c6401218429030001400c204258020034008010241505d44c0d076502108075190a170707200c15080c1c0d010b00d4200c002c5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 517668399 1250 517667149 517667159
    0x2f010c0e0d0b091f1508010c080109050606160807030e090c070201030b0d062a0e01140c01020f0315030105011a090f010315060507050f07050d080a030207060203090105040303060e10 80
    0x5000b542c0701214004846000e1812040410b941d4545451049035940e81c21101c031301c2a15550340c3c8406015040c000f0711180348a524020b144c88414461601180c1c0e42d000030802c55560340c030441e8100000540d5814403201c050424190342d034001a811004103144154141681c100b1059551103548a280b909013003013585e03001580502052042140d010030020700c84070000720b00d0b00c9181000b51084e80c240c1000700111070403110310400d10001d10280074001308a0001603070f20a10207402c2071b2a50041580700c0240850030340c0039001d9202213104c07260f004000c115528155000c0c49084480450083c422030340e0701d80389174580680a4551145004081103800c800d410119211441c4030010b16000917002030a810710341c1c401e401c0c0e40020001400c0001d1003018442c040040c2100070304400c001e40074040c40c0c00c0016600401114005115110214140c0e0019000741e0540350352a4200710150f43d24074010451600900042350b0403800f00e45071000100e10300c0b420b21082c9116010b580c10844101f8140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 517669649 1250 517668399 517668413
    0xe01080f1902011b060b0f090912090a0807060503091203010605180307170a02040b0f030a030f1101090f02180408030c0c1906060503121908072f010c0e0d 68
    0x3660300760b042c00a50310500c11000d4084d030180048600403040041c440d26401c0c2080303160029a40020312881c98a8140144040041040d004090701c02229941d07448481012820050b010f502180045c0500100054010f8000d0020351182d15040280c0340c8280c105401284580802c0c042d88000450922649400c0f00381c0303124881d6411030040072a810240d68620845908a141720018480e4100d880301504500341406880100702049801c1c0300c03074010070008030f070365100812805420003503009a03843c5520b005407542d040c0f200d0440020300c503c82a070304280f206690311440c101e000d41c10110860b6200e2244000c01c0303004940c800301c2d0310305d9611181d41900c15500480c01d164400e02840e40200d4810340c0c001c40b03000c100391091002180c07292910080604000305c034107031103035581003c000049402104015180d106e4029041201003510b40c44011034500c03504814540c02e1542020304114503200112800860005000080c03090100c030314000c48400603900303140f0b6000300b0300032a148006002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 517670899 1250 517669649 517669693
    0xf0607200d05122e05131e0504230a0c06020f1002130b0d06090b0102030c06070507061d1018050a021005070f0c081207020303070b040c120c0e01080f 66
    0x3091301c00010f003d40c44501007244132a854941c0101030001d404005c9424220307940d903c0417140c01c00c10007003000804901010a0720703001c4d200510035a10000a002c0011040c0c1101c0c40c0e05007020000c03103074041c2c001840e545120045061f1804061181d0014943c0d03c002001c0410500700070160010380754281624000e0f401c00e030811b141c0e83d48480c8020414210a0f806410040d07036002021030390b94500786194040b5505404560304641041103c0c2a0001001800c1a000101c0d850156a19101410014010010720b0b000700f150b00080490035000c10000110309041c10140101042030028055201c0c5240900c10310003811078204039201005854000210009140706003801480e10b070460340da440d03045a684100301c4858045070410b010f10041041030547c20607035800c8840c070702001500000d03628041c52400038a200038801c000b4081000310101800100416090f2140031012881c00c034903100c4660281240842200000103450760000a44c0390300c1d0034880c000703840c4005005e01414032041c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 517672149 1250 517670899 517670911
    0x1c08060603041208100812180103050103020303070b0903090607080a09080c1003150e090703030809060c03040b06030705030d020c090f040f12051e0903010c1106010b0c0f0607200d0512 81
    0x5c40350300041c403100c144103443c254a06e010009036240351200da1a40d030a00c0b40160941050300d0b107801440107860000c00c44078840e402001540320380e030312488800e01d142b003940011034014102103460810020100c01a000b8065682c80d0788424a49600c01141d9600e00145002d030f0040d16a103030100490f0080d8400540800079007400382820361074a180f0718110809030740740e51490384540d5042041c1540031900c15000041e51000d0041410030701c0d050019804040c1c40580700303850400120740302e50b404108036002030101074281c43d02d8585120001c1d458050f000951805240c4600010304c05004504c10305120700d41c001121000035450b9215024294440d40c1c0440c2409020081146024140c4009498441c184034045a440790b942c8140341c2510710302e802035010703c0019900c0d4142c684000c2480c3d815581c200507030310340310131a20560354503141c1c04a0001380030f40100010301000580c0509965a07014841007207140400c000103a680d03480e030001900c1c500181c07040c8007242c1c07400b42039203040d13420075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 517673399 1250 517672149 517672171
    0x6040b031c020a060c020c030f16090f0212071808060606030718120b0103120507050d030f2921211c0e0f010c090306020310081c08060603041208 64
    0x10f00c0d90b10b03a41225110100308000d603004444280907860100028050801640050300170110780300700304801a0860700409080c0b54551545540c080034544c159011103501034908082d5080c00c01c0c3c040c094011903220f4002c91841080041428800040d80318000d00014060703074a160f8500f07400b207440960440190702ea50f11817160000b10900c2800c1d403030748403d008103410941940756113001d82e84840ea011001007071280501460340451004120240d100080d4100812143c3c81e0300c0d4403900406200d00800510501a6405d074150043c0c00d0000d252580c0035039150000c0011440100e0340c0c86c1c0c6490380100c060340700c1c0c01d6a00203040030034500410503203015200ca0400c000c500401303100a00e031600c41043d06580f006003d843d220104500e140c01a01a4000c0019001e1400014105d0000e8000541a42e0300080443d060b40306040c4484c00030114403050700c802c9011500d4200c020f441d0030041030300040c00b172000b04146140800413a4000c40e40036040041400c500389080c0e0344100d0042080c0418 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 517674649 1250 517673399 517673413
    0x519020f1c0b22050f041104050a0f02070f06060602030f16030c020405040f02010905010e030312060a0801020f04090c03050105060316020f03040f06080c04060e011d130c0806040b031c02 82
    0x56103403242d0710082c1c04070306040080003c80188001d4210349004194854401d00d0005210101e801141c500c0e4002e402a40c020070207540f81180f420242500c1c181c0262070078800100f41040c8100040720f5036049210740d10610420350b80344812644c0b8003402c0324030702031510100b00a0304c6038400d203811586240c2c4681040140c00c5034540000e000c40f0402c07035041c1c1329130144c17000100440d0b0380003040703070058002400c0c107001e030622210204e036882c003850040055042845000c02e13440d0750b548940d03400a00c1880c00075540c42800c442c60310602e40203031056501e45401c200c0180450b500a024107030580b0005090f03207085503100c4491f2407450580c0c0d00c5c1d0341c0075805400d41d881c902440601c01800a03205150880403121f03c1e0a1b0f0041501100a0594080e28070600091001650201540840140910f040041c101c030304104c1c00d100740c041c2c0c52069400f88140e19150b0b40d2004d1a0130000792840c0c5600c5806159032102e0a0009894902c9001c07a456040240a4407401c55103030b012100b0241517104a880c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 517675899 1250 517674649 517674671
    0xc091f030b0a0f0509070c050c0d1a0108030a14040503120d020d060e06011d03060a0509071518080a0c0303080a1104030c0806070c0c0303051e0d0519020f1c 69
    0xb18156541109101c159484030911803410700a52094000740c1626100c94103140584400741c46890400807107100e0550000888180700500701400e03908010745541170304559603030b040e180d580d0344804d00c0d10000c07896440c5400c030455001410b03102181c0c3d011340a8603410a0030080f40b003a607844000160b4010340e01384070b8140340300700e140700c0c1300040c04804101c0c6025003085c5001408055501401e50150907030350a64030b000c0c0c0c4010030002c1d00400007410104194507482111803c1c440c0e1a0081c04c014034888420303040c480d80c4065042c114401c0c00c50513500c050b80701c00d4030f20303103581c2ca5440140c01600a01c1e010030000784529180740d8003450000c0700094038513a0011512507a070181d8000d84001e0705481c4203022a10f4113201481d0007a0740c03401c0200e0030800f41d580d000050200e03484081c0c1440804100900d49a100c11800702801c003045181ca9600e925405039500142402e42d40c00b4040c460f050807000300e807a020320865031401e01440c065030402d83c441f04201c040000000c15282e25546644828074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 517677149 1250 517675899 517675909
    0x40c1e030603020307270b0a03021906140f180f03030d09020a171513020a030605040c1509090b0a050301060f03031106010e060d02120f0309090c091f030b 68
    0x8054015030340208026140d030040601c2c1081d503400a1408040046902c0f00401d0000080380185402880114850883d139000603060003860740007a400803151000c040000400e008410156003181d00d40180d0703800b5901d1055024014070903000d1000d1420800040101041d00c03200004440007000c54028049040c0802c1c1940c00510740d078a215610b4200a1045180200601c0301401c00c00510401e100354924501380c0c2c40071090bd05001300e041c1c5801064500140f0301c8200c0b0f82e46c0c0c0141c005880a69649040d80040c02c0840c0c003503410308140315020504000906038420065040c0e9100761116081c09040001043e1131a006603025021010004503030301d080c000c82000b0a160300b1003601040c95410040e185902d152401e11450300180e00601c0305030050243c0030b420400c02e1341c000003488030354804181c5038050040720040d5403095451a0414150001c001c140072001520904c609448284104038607000703182a00707500c0190007501524180380540707a51103280c0c59142c082071001a01000c19 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 517678399 1250 517677149 517677197
    0x309061b2318011206120b091b01021c1b1202190528020301060e011401030e0d0807050706050f010f050f0918070b030c3006040c 57
    0x1001041200c008009810722803020403119100640e4514580b0160350306042900180c1d2a800f8107011803040d031050307503240c150300950280140340b020002600e4a420414031015007223135014010b10640034150244d02742d40c41850400311040c0c0080050078a1030390a0040b50135030059000400c0300c56800015a1000c400200420780d02403070703095403900c880c0d1200070f080c00020020b0a0a07030400c4001400001c0c1c00240400e0305103d9800c5c3c1c2010b11000d00c821070074414480c2c80195041d82407007408070b9004217090f105812074070b50001e00c02031010b41c04011f6050b03814030402e498158000c146104212402042d4403a030201c118030b070840c9069107aa85e800101d40b001d4884029030081d102c01400681c4540b41014040c01040b02d841360461882d0f00000c0300f01c440145030007801100d504003881440001c20042c4080c000d10802c0395240c0c41c000c0a0704000350800c800c10a1401100407400304c106031008811660020300410381c43c1a40e50380030038840a080010000000c200100f04004040901c0207115 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 517679649 1250 517678399 517678451
    0xa02061306030b03210d1d07050415080316020303070b0f01030b130b07122306040506041b0810030c0e1e09030904200a090915030b040201030906 64
    0xd61246030038860002c088400c48440307180694008680382800040e4003c0c3d00d100c00164100b01a62002203c5004000d020801100c884102000c140640001c0001c500c0d8025075005a0b000c020480654188414000c00c91040c1d03883c0da00100225014240c90310a4900750034009011249828110b640e44500ca40c2d080303800c045540b0954005100300214840350300e41110b40d80c1020020360b00a0345031403d00d40c1d006401e1131700b40004203031608603d1403150000903044580d50418038640110b40c8845c00c90f030070f040361a24419458040000c009203001c0c0301341003190740b030724800018044081809450b5240050b110391032100405c80d0010001c2c0e25101d03440050180303248100d240e0b080840120311080d40c100c0d401300c802030624040020f0b54400005440003a0750484001c036804c1d148164000385908005070740301e2070780384c0081c071503101d250420742c800105d60703182d02c040221403034450303202e90200003a000c010003d904400200b40551320a800401030746000d20b1b00041d0304204141c032064400b4a0500c1c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 517680899 1250 517679649 517679677
    0x905010e190e0a0c03050408252001030506030106030507051306080a060b01020d020c1f090312230a020705091f0612060f120212160305031207051303140a0206 70
    0x1080b941070709a001e00f508138000c90505110380c5c2410790780e400c400e008200c200440c01d001c0801d02003d030001040c0381e88030160844481c10030b09600c652603890200000c19003d021030b00344800f0602d1401c0520507041100d40040180041070309000400820b840c1250100c82c140303450b608049110002400003100d004d2040700300040d100514000641020103401e402420354008015800d09a200d194000d841c24139815428801c00b1a440c0c4182c070701000c160005420010b190500d0040280c00a21551040480c0310b000f01d860f02c0603040410141c42407000e00710041e081100c00704a00d09042040a400080040070b65424216010364552600d04a030b0240740081c2d5810710f200310811441c030800000e0700b0021021121141811640c602c00032039104024011103442d10040301024003480b0f800440c0003004219040c40303544e8202550341b900200010352881140e0030204c0c01c068042c500300d403d040440011507103541e00d951282107412a407242c2c41c075044d00507244800016610500207045040031201 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 517682149 1250 517680899 517680901
    0x9120d06050a0e060907050a03090506040b07080f0121020a270e010c08160e0a0f18270309092d020301050105071506050a0320060a0905010e190e 64
    0x108014101e0b20a9020012140c50a01800380503203840f08070a40c02882ca0034000da42d4600c10100b1001032a5039000580305008410034031040107801510341d4050256592200107980710b992241d03524200a102e010709450103044582c83c4400c2c03564101144a00080c81214115500d080c03110340c501070240008020026000c3c204107402e21446091400742251001b0001c0d4220598050882c581c041d0060408180303c00141c209540b140450003541040542002251a52107812032401c83e00c131b0241040c03118481d00341c007001030340718410307842c55003803061020f0b90918061500d0f82d540007000a0580400600040c0880d01d520103024083c40f4044009154080c48080c0c0a00911a580483c0e1a14820700401c01000140e90100a8416868100c0820440c150400c5100001002c0d10761210740c10549180000041c407817020f19440b11161034001007041c44680d501088850b104100780c0d00c0100c0d480400900841d41301e90080240d00101802d80140b000401d20848040c4255611014004030190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 517683399 1250 517682149 517682159
    0xa050603070f060c0f020f180a050c13060e150a09030203070e0c0406081905011d090d021e0c060f0714150c092103041401180306020309120d06 63
    0x3070003000700984480185058240000108511501040a415541803c62110070b40d80d030b2001c2c410010314002d0002c071040c50802500e41800400702c1e960400c0c0362404001074042c1c15004100ca0750000c1e060b51400314035080620a2301c04584170380c4c4441c0c0101007401e076502c80000d003000504250102c0d4640004180c40d500c105461b00701c958101c14a510307640d0040c4089081ca040555003a00c08504040c0e1aa40c0d684d001c0c103201481c27898550125509040000610a040880c510304801a6002e100b401d580d603188a10351340d81000c110400144e1005007000c00340d81c0340c80b0128101e44205001d0303c0e201d094180000e0340c10703082818101980c0303d00062101c00c01880e01c45c900c0141c410705000e40884035020f003040d00880d200070103280c401000007480b04c801da40c9242014400e1141115070092042101209a65981243c01048100342c40c15200021945c0250030180f40c0c034a5490701d50700c9050450b42c81c40041e400140c40d06e10700388540070301d030f00c015111324000d001c10607140340740010b050f8170704 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 517684649 1250 517683399 517683403
    0x8071e2010090f090e0f12030403030b0d020109030605060a0518090f06190f020409020d0b030d030243030305040605070c03020d140f070b01150806060a0c020112050a050603 76
    0x103040c088040c0044100100410140f822044080b1400c920000440c8068104403a04111103641210900e010b08001500144818000b442c06140a0380d03080025005074800d00458079448038020f408246020ba040000030f40c20340145a0003e4081c0013030300f085540b60301090710000880540e031441d44941c0108040001c0800c290708148135000c00406003070400c66035140741c21a05043c43c140031502c3e415008414040c58040300c009000c401021551108800e109100429400d0f4100c0c0c4280607078404211202e11078025038a01d910030360030b000c2c1d20000c0200c080d5004405c000105c01407044000e07100880742c0d90104201001070007601e010585103028036211045070b400400b01014454441d4062000c41c0d030024801244400768103040d800504101038401c201d02440c4910a9400760000e440d0b0100048000c0040c1211642c001000c01e401c6900340a442c0018125103d5802c04800d01508182c035119000c409041030040c14140ca800045802810a984085071003100c150388a8050140504007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 517685899 1250 517684649 517684669
    0x8030403050610050109031209031505090c010822060906050c0d060f0b0712140c031209010209220b04151403210a090807060801050a1208071e20 64
    0x9003c40c0d1280d8682810300280841015000150800306050008030742140261900390165030404d81004c800d10309802c0002c041d11089511884501984030b1904640d401503205ca40900341c50000003015000705014410351150480041e141c0c00c4d2100c020740c001c10741c0c030b1040c14020309540321450750324082d4600140075603a20354040402c01c4a80c20381085111900c1c4241e8901d10b901c1a032411030300c0b01c903040403940f107885645a4041141d0004001440560010041c040808640d8124a09996003030007603081340204c100700c0381c011900544803a000c00e03d01164081c0f400e800100040c1c0380170040c002c501240c1c0003180c1101312220403501440304a100310000480904102c00404401074290715800c81e2000d501482003107050701180c0050b11034090501e0b00301070034040b03046030328a0340d44082c010007000c0300f0f10490b4002c0d00742460100d80151030001d6a075600742c00046161810809070755450020000d482d0540402079001006000981903800010480078960b040d62488001e840400550b054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 517687149 1250 517685899 517685911
    0x130909020a0b040b040506030601030f050705040911090a0b0a1209060522110f04061d0a06170d081018061815030b061807110607090315050a02040f080304030506 71
    0x400c0c48100288150001100d003520740940c0c0481d1291510001640a030233444240c212060400d4100684158000d014000b1960808801c5c00b0000200000e8842d9100e040880f03600580103550501030300d00c0c040d00424400d000c516256100b0f03052400c481c002c6503003240f411a1416112814803042081c04500c2d081f21340a82c0e242c641348605186e0715500d49181d61180640220225001c1e10619a103a81c0842c1c0205400100704030701c07008440d01d09508070411114100760b249001004640300580c91031888000309001d0081c180c005009405881c041d0b0000d1203243c2861000710f000c50100301a001140c0040700780c0b000407a0807400d00e0786504001401ea010248214948501a41c81d0210480c03000100c1c0e800030750150040e1900c00c041400e04c1598140041d410b00110180044150701c02a49510444807a081e030302580c0f00c49904844040311440050720380300c00440b4a85400340c450784071035000700942e0001481c05e903692903503940002190b407000225420202d402c0050160a010150f0701c0342d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 517688399 1250 517687149 517687169
    0x7030207050a05010f0e1201020d1d06040503040611030d0c110706050f0706050a0905010509100b030a02090403050a0c020a0807090501140901030b07030b030610050f0114090d050102130909020a 85
    0x150800c00000c181000901c010070070041e1b40104e050041e2548001603100302409402555905da00410b160003400103902d0091256282d41c140103504003021511a003c3d80d4031201941c5090300e00b00c01200d590b4010001e0140d180820003d10701542c0080c401c89007400c2054880c500d100c40c144110b5410407110340d20003030621000f04101440518080102c0380c12035030066002a89031171b102c0082008202c0460010000d40ca010700707001e107000001075105080780001400313110a204240074140c460b141110300030741000030382010500090042d8082d003921a6649001d2020721003540005502e8904c990040c02950041c100601c03d60041c0e01450b80501002d03640e00a4030514640802c401040c1488080c0c00c02404c075012036200d51080c0c000e00d10684006007101d100381050000100314000038402c0904c01c07880b000f1404800c2d40907085000b01b6038032107551a414110103406001002c1e11003c0d003103070155402c00110f110013050401c00f0b40945050440020000c0303080c41800035429598001c89413034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 517689649 1250 517688399 517688419
    0x1b0809010b0a05040c02030f0f03240d0303020702010215040c0801060e040f021504170d0305090c01020d081807080c031204080316080c19060b01110c060705031209030703020705 78
    0x10303482d0301c01c090040700c100350740015460002d8075080707003540030b17881f2424a241000503641180442c00400356029500c103454652b590740c954604d0703000d42180344d00a1030304081c0d420499004640640c0c05096128010300645111000e404400c204c101e4013240c0440780380021031002d00c40070409115100c0904550760340040903042c10384841464010098009110340030060948078816140b00540307000f440380703820500ca40080403200d0b5440b40e215018140002e440c00300003605d0042e0020315070408910680103030a40880c1000111500f070070041100704481c03104452142141005c1001c00c00034800300010b0710301d000c1c240e001c04d41090001c41e0045c8543c2020301083c00711550110071192007051485001c00c4001980c50a48440e02440e1002e440394003078440d072507070f81840c0c08400b804c01e58480c040401c4101c05060042d2500c103400c08449666911024110b620b904007140101465030207031048a040c9104e40c4000318042e0000c56002c02c5542012404004141c0c04010380c40207071904a070300c0030039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 517690899 1250 517689649 517689671
    0x9140a030c021009050a060f0206060108130b150d2a05150a021f09030201060e1006030e01180c031203061a031e0106050a080a02040f0e040804091b080901 68
    0x501010504040e11960760f0218111006000e090743c034008080c0507041241080d41c6100203440d8032405203001000d0702500c0005642c03584100091803187d9480d06410301c420040b0303203860b010300c44000c000c007024040c44039803003000d40c1c0c1d2800c0c8032550a124040c1840c0500c100c4050300c03000c00240f800d1410300070b444102400160b4680803600840300384000302c5511180494422840c04070318410380040301600c01202400c00c0110342210110386c3c040d070000c4c80030307558070b0b0f05050203540121140c1480507030b041414480588030360030081d0407001c0c0300004204228600f10b10700f010802c00704202c58407100e070a401c10400c08810b0800d01c1540041c1020010301c1c3c908812240880d180c481180300d074400c000001860030b5001a030002c08000e80802e1449591303154180a8401e6009a469101144015001421400d494000c540540e40b820301e000c408586401c10681000f07102804c01c40f4204014007000c25190b01c2031040e00c6070009404a4481240145400585503060203421613185da4100804c800e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 517692149 1250 517690899 517690907
    0x4050a090207030e1c0c0f03200f010e01030b060d050609070f050a030905030c060907090f1a010f0c080f0703030524131401080c0102070806102c0a09140a03 69
    0xa00c0032090390030f20041404400706a250a00c202e0b17000700001c09010000c24100c0c0403891140c15644140d4550900c100c04082d007055003200e092041d41e009190f25509c150f1544105100c580f5458181070201d841415080003c82e01d0b04981c180c2c5c1c50896951041140078136042440c181c00c4209800c168400501c1c00b80c00501601c940744008092540f03511200e42000702c1001191003042150003500c81e2424040000c54894005115880300a0b0420006200d486214812040799039100103900c002141018019546440c201c0d001c10148113030320480101040401d801010078000440d125980da2400340340c0a001c03170300090075141011042024000003600b030114445504841218010141c491040f0100702403c00034100c0890011107000000f00710000140b1246a000241c0964001980f00d884240d62850101c0d503450165642c1070b030422400107801e080c01001110200b940300b06640440d90807408070410b80321005401e45e221a490700b80311452005413010381148002e000310001c1520014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 517693399 1250 517692149 517692167
    0x15030114040c0308090d02090405010606110304050d1227030209070e030a02091801020a020619050912030a0b0d08030612010c020309091f0b0705010c080106080103081b1204050a09020703 82
    0x44c1400d20004140651741d81c0c1b002050ba517540c0c001c0110010f482e040c68510702800f881e01c00c01b0085012031035403002d216400f00039141074500180200991b00301c25160741002c1036010015200344101e480240c0b00001011603410061041d510b80103940900c6c51050102e01c0400600310010030404050490f0645d40100c0c40c03250b180e404440812454413000464080c030360100401080da0362000070500800c1ea0041481e0b40f080d01242c01303150318481c600c0e800c1c0c001d441e000c448144207038104500b11484070252130046d5802c00e91000b000a01ea081c0880462890ac0c88102d003070301c007040040b0030000c482c5006014002c100200f03900911103180e46500c069983e0007010ba01e1803089103542c0004010a603004100040001000400c002150340c0703005404d002d5000440035155542001c000c800001c2c010105541265002c1d6580701e203a81c42d40d01c64042d1030b08115020201e00640c4001e0a5020004109209213003403e0710f031060303982d03140204203c0300d840243e0080c1034090050049002103070b0006280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 517694649 1250 517693399 517693403
    0x906030207050c0901080106030308090d02070e130f0606150906051c200304051207030801030b1e070e030106050a031a0c0f0705010b0103050106021606030c020f0615030114040c03 79
    0x16844071401e00d00706091008405915800c1030200b4000a407000054100ca0b04584c042e80b501034181e100d4441c030707540320007084d840c01016a0254a00f00301f002000016154400ba4112405451504660b107140211441c400107513110b0307858100034000d00d0131102180c181c0d00d00606100041603e011000b030a50300400c0b9a02a100c0403902c5440f40004040d0811642d00400d4003983d264540c403082e02281c0368105540039221841402c1c0084041c0c5981c01c00c803000280c0680381d00840c0c0c0e186544450a003080100100c1c80503840501c1b10f02c0702d586428946005450039250078000c0000350f070515086502035404144921175402d02040030950004010501040c081601c60541e40d0320680c06040784140703400d90701c10203000240c00f001e0090641c40f071032400e1400da809000c641d80c2c41c2030881c0c2d030710841c0e800c01112500f60601040b01038025406169a03210318016242c0209141065504015046658a41c1e2969100e0710f180d052a080c0704615400941c605942614181601c860312002040c1c000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 517695899 1250 517694649 517694651
    0x9060819051f090504030f0828111810091d040606050901120606170613020307050a082401060f260a09060501060e0609210f0f0607030c090603 63
    0x80340b101040c1d411108810001c00c242c1941e095500d0150b04020328003154190001f80150b91413462092241d80d4603801960b2002d210000507000340a0240b11034052071069803190b82c3d40d00c4000b0007130f0900c00a8101c150305d900b08035501007400c405121450004503480bc0c204000d26800f4888150001180521340c6043c2603c07105640d900e1820301c0040c101780d084690701c0a550303c000108070000a440400403841800c00384440d0b42d072429000d060780018410701480740c02003c00181c1e000960380040f100980020100c0c0d03283c540d100045003030024a600403410305e0700301c150b104424096000c5444250003e0100400f203c0d850107100030301d080d0420820b802004650030040f00c151010b4001001e03035843c2800703031a04900300806c418000b00f03034858007147c0c0c05003810300000d01e15000d0358100c42c0386600540390303e19040c0408208112840200c1e8826000400c640d00310069680800011f0f003007400600c01030141c1b0905556852508800030880720403d820050300c845040c0e40410140d04a03181810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 517697149 1250 517695899 517695901
    0x10803032e092f0f0a1809020d090303180f02060a032415090305100e010e190510060f09021c050c090a090603350307050702010906081905 61
    0x60800038070105912030010310b41843d1040300c400e41c0241111400c0c00200c1100b020701001c0b44060701280c01000130b07006400e80184510041d0fa402100000082c4210039031101c41a9100d6801400b2070300038142c18140f50742c0d114003100400d605442044584900c0d000e01030300520540c2c3d1205000c80c1856030007802500c4c046001120140250040020340c00500b1140546025000c2c80315200d059500c40c0c0003031948580344041c14075001c0c0b903101056a80250241214921510b452006800c1c0070804c00c01566a03582003c076021810700684103010741500305051a036510b81403151512410b070001c0d102440c80c00804004142d60b0307116003030131500321801c05078071201c40841089540e82440041952142010104607203942260000d02d1801d008880d181c0c890b5858000000840d004d03408000c00b55140901c4411130490300030300800740c1140c43c05543c0d092410b034440c20792042d04180c0d21070f0f0200d4000311f03942085603044441d44010b080181740c0b5200302d103001030a60044400701440f503006195240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 517698399 1250 517697149 517697221
    0x220e1803120103060c0905010f02060a051b0d05011a030f07080c0c011b110c01020a14010e070303030b040b1002100506010e0a0b03240607320d020601080303 69
    0x200c1034940003034030001c1d0003065694a0030403001a000b0034203080009101c602e00030440b98050b404c1d00480c1502c81c0c0c0240990f50314010642c0082034042c107404400039002c0884010281c00310000c000460a0b0240401e69514260441c0d00400c0c0d60400c5254200040c003c000e40b0000c0440681e034080c080e0310300700845498155020701c081c824514902655400e0400a1a610701e42c0d11441c52000843d035940c170f9442c0c142d550000d0b01c86e006c002e00140145c00440003c004a00a400f004005030314003400010102d541040b85031070141907620840200741c40705504400b92a00344106543c00c54280c4181c2002240c08030025290a4a401e207020300b90740e50b8000c0f9030140d115030700c0c1040e860030182030803000584030340d880c022a4004070b0300f040c2c051020030140101048035626004640d40040c02d040e00b80a800d60710786094400312000784000c04203850403900c1300c0c0e640c503000c005101584005000e40c0c03205100c009050840580010009500800900a5110950072030740e03c003950312042d04080721100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 517699649 1250 517698399 517698403
    0x1403040308070c0b070804030f23030406060f06020604060b010f0806060d090602041e050a080d050703180f140103060308041502030403020603090f0613020307030b0a0917220e18 78
    0x128001070540c10501c03041201d61742d000f041160107240292a03c1006901c480c40c100c480d00c484414080182d02016040d20845041c400078540281c864040840c1054480852184204a41c0c0c003001c0180d03c20414007041c42107510486481281c280780a58030036642403006405024054001382c0213000025082030818200da00c801440da40c800d1045d5903c546c4e0f040700a1001c0f42c0d0341c104001e040f03e00c9800103042c6c07600c02800002c40d04001d015050310a0825025a101e0700100000c3e01400601e810780036540030300b00c60350780161070981b0241c0c2010741460f6000c40000c5260030102c0c1450b00d01001407001c900e490302910201d62f1110b80b41392014401071412400c501907a40025005000441440ba00c4040800d20800d80c00c060800c03245140c0ea014141c640d00c482120020f03403d40c10020043c4041030f0400103090344820354030b0002c42c845403030b0f0741c80c05040300d59502da4100200e0702040c403001d40f16842d549810042e9614481540281c1005481080001c1c081e01c04c4a80145100c4000940d05003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 517700899 1250 517699649 517699667
    0x108070302190302040f090504051518010e0d030e030901091a07061802030c0a12030f21090506090d0e1309080403050102091512040609050c0a03060b0907140304030807 74
    0x107240c140c0310142c1d503401c4016010303400030f0061011400003810080f5120542e441001d01c80c0341c110006099141000040c101030703800c041e01c800102d80c550840307014505c3d024080c240e201309031400100811005900010200e6101d43c0d00342240740c00821001314160b0303101c2c013440c00742c070813180258456030614224281a0b11600200a00081c108110224143c49502000d1a16402542502c2c8450841030410050451038000e00740f0001d038104020001ca445007011700021045030502142e42d00400205c160800c280b85a19041203482e03110078800c00205000403500000103000a05125007551000303440c0701032102d03606003e0b0b5644200084030460365040308040c250403012144e0350323a841c0d0400c1c1d03002c4d40c01140f03000d00031050404411141d003403002c21500304071400f004501040d215940c820b400387c2051102130703c02e44a10103030103000d42c2c1c4a005400c01544102800078504030700d0000e000402d8002403901c0140b0140c10611a42000f01d2421a1380c015490310303000304181c0e19494152010f002c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 517702149 1250 517700899 517700917
    0x604123002060a060e040503120a3918030605100f0f0801050705070f150e0313170309150f0d02071a0f16120e030c0d0801081b0108070302 61
    0x803805900010364010a00c02d004041410013400500c0d25146a40450202034a00501c550310400c11302c2c42c140c2c2184101a003080780c011000c00c1e50007654500382c034480f42a4412144c103010084115505180090b95892121114280120404e600d0b10782292040703224400901100d4a0354000f910504064035000080c005010f81d4813519521a4240c8003604201d0041402543c45d01e008611103500403010390790750582c000110360100400303a941049036070b00d56030952101521044914143c80f028805020702e949400c01c0701140d1442c1c1115451007101d03101020340c068200f048998209d0315544ea800c04100c0c1e00600c415610303a0340e120003550920032004000480da102041482c00c00c401c0c43c0a4940c110003502c40c41000d510f400c0281e1109a40a48452481d8920030070600800ca00a00c0d40050320304054070002001403c1380a1581954130483d0141c41a80245a881c0e454641040f82d107405004030724020940408006480c0c448032007101403250510501c1d40002d0b0f82c851080c2c045500005d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 517703399 1250 517702149 517702223
    0x120304030512040e01060306080d110a06050103150c1106043002071409070f08220506040302060f09060417040b07120e060c0705040c03060e07120b060412 68
    0x4a10390b200149030070902891110500c188000244075200b40201405e851008000e030008609625081d43e050300501c2104074540120041c100102d0b2561098a00950140754001c604940320700120302100c0c0701c6c0420b207051041c0c0c0300d404076200c900061070307690150b40041c01a60030410003c1180c501c1910740000c290102d000c1e45424041507020800f80101c4a4803802c01d40d001100b04104100058210b40d01000211100115001c480c45280b0898109400c003551107200050756800c0112141040303c19240c0e5030000c1c091104050b810070072264060801c00d20014903060002c0e9107a26603501810181c4602d020124503081404107200300d50003403103a500256a20705c810710341211584003100005000c03920350f005003044c0f418890708079a46155018043c0c06064100000c10001b0200312085c40c0406aa401010880341090348076580201c100b5128640c0c441014454041680c20f0b5400f07540c041c150a2008200c0070241c05c1d0b07010707070302c0d03a00c40000103003103440464500081c000c480910001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 517704649 1250 517703399 517703413
    0x3120203060d0b04200f130903091503021b06070c0602071a0702060f060a0b04030b090c1c0618080a030c1e031a0307030c0b30150d020603061203040305 67
    0x10507105545001040c003680d11740800000700c01000310558180d1a000d0300210301510080b0002440c0c1e00c4510450f100741400d0b4229901c2c0c140182110034048050300120350300251a400320200c40f1a0341e410306046000801c250b281c059801401003000c4000180416000300d1007001b00011862003030104507041807405018680080020341c0e0b90001c0d1128100e011228000c503546040506000c0e0550301140905031030f103441c50703940614600000b000030419016050706209503640b0790800c4e0030710b0f12503007024100041d041d017400703412103c01c010400369070302c240007249000622040643d0f1501046007400030340085844426a007030381d030f04280d00b208100b60103803c0d4211900365205008001140000301c50b8520000d09055503004103000c050500148070324100310112402005000e122541c11b40341c0345005607048414040c1e102180290340356040003041005a4240d00304100108c0300448480345030040c1c54000c0703031161001a00d914041c0e0741880c401c0d44240c10810445d001141e1000844981d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 517705899 1250 517704649 517704653
    0xa02071a0f0a0503010e0708220203011d0313080105090c040c020a020a03060614041104030b0402031203010602010501210b061e13050103020f032b031103070e150703120203060d0b04 80
    0xf0341d8001d0240000d040309820201d6101441546024402c00d00d05003108071954417485910501c6021420499140d1340710610242168121322b400007514401800940c1c80d410640003541040f02c00b500715941a80c50302d0100000300c034000171703449100c0e502564002044100c4110481c2032054504c000303500401c20040000800c00b81c5c1d80040d003110005441199150702140401042d81c100560212441100f0310050010450400019401a100400322111440e0712100c4d251160400d9100c4000350355980c00410000000c10481081d8514494840c0e0014280e0380d1810142103024002ca40980c0c1c00d1903200000700d2040d0341c044c22034007004002c210300502c1c01500c1e5000d0042400100d0141a0030300000701b45080008403800006280443c600810020080194102c0215010321042503100e00507100b074021214000d6000e40c031590b48450070a0045001d001d1100500d401c0c1e6a40c4110802200011983c44a05408101450130016a85e511080e0014004020390440500700280344000e00007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 517707149 1250 517705899 517705907
    0x4020a0e28050604120209060a0510030209100804051e0c0414061504120b0c0d39021e010b030607200705010e040f06030501051005150a02071a0f0a 65
    0xa403041c5020381c54070402e40382d9080c80450302541c807078229082c0d640140c4a0051804d00c503c2c1d035000ca0042c01d001c1005684d0400150000c2d0790031001c3c4042071340003d2075080d43c144240715400106860401d26450b0410b951100d56030559420041002031400204020500c0184098485040e00030b000380035517000c070702141c566880c0c243ca800d0b00c18280d00d13280303c00900340b0406031811140903040103800c1204a48920340701d240000c10441c6174170340400104a00000718800c2461000442d40c1c00f8118200103400083d01ca80e0140e400860745590031100900e469000601020403403007103800780240345100403814090002e603560540c0c0350192000300b02c10036921030040f6042c003004410f100d02504031065420b032503160030b00031180050540d0301d411585003030507003003400420500c1000198403030b945c0e00c0d000d007142c03010750b9100000f0705003003001c00c000c0c41c202c81401d0300741110000f15803520150110103551403a062148442400d41c60b9604820000d10a0581d212051245401584c480c40040010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 517708399 1250 517707149 517707199
    0x317060f030d050c0105060a030f140c060d020715110a1d060409020a12060b03040303110705010603061d0c0307030b0408040b0d1e0e0c12010603050f0c0907140904020a0e 75
    0xc084c5603e08000102c0e6450440211403c0700d4204504071000c107c5510b580c420086078031900c0040e0b1003000b103440c290f5260240104161b0b04160001a02d501c628503180444010b0a91350032141814040810b0115600da011900c0c0c01304642043c00d8441c4d02c0400c00e60520b41d540344103d038454004100011811a1900101041c0c08140c1c0d54074000b80f0161954400c80f01580120043d50310b082c40010f0020703010b07070300080c0ca1240e0810420f0a083c131603940c5500790380c2150000c030780040d1039201480e1020303040500000818048406000e0012040b80420381c0c42610b844050705044084000c902400301c4a400c8070040c18220018568501e4001592000360540b200a0010307032124001069640074a4030070320591819850142c0010b0003407804100182048050700310840d56070341c41c0080010001c200c0d0002c00c103040e0001d80301074180074041112056004045000380300e011485010310b489090110b404600080b680140c403a000c000085583c00916001e4603000300140f0348004040e24101155 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 517709649 1250 517708399 517708417
    0x1707030905120604031d2409151608090609060a03140703022104020d021003090b0c0f18011e021b090f04200901030b0a0f0c0903060915050f100504090317060f030d05 73
    0x50a0b0313071514440d041c1845100ac4080058005d41022400582d0107001000e06c12401020709090055100007c0c4035503000741001000300c2d5a601050b51040ca00002c1564031200605085040520070750240c0c0c00c1c01c80c18200d612071400c9540c000303011552407401c0c0f800300680140c0080d0b0461841e0a0190051682c0c0e50300f51200000400041c1c901c41d605000c444800c9201d90556003040c504525a042d886000b40c0c0c024184581d15015445400344090324680b840f28035802041011005800c0403030b010050079a25010b568800304008940c507144a104c5c1c0c010390301c52680a1070038002164820ba01c00100c00290748545010000401d00012444a502501d09400100301200b0341000982c00c07661104640303000700d68000404c01c00729005030700016440e0f0142c10700104891880310564110307801128441d003882c0b101c13400e20110681c85030702daa01600e025501042900e005440142c604404006101940074005c00000d41645030f0100304075070404080c088a0881c1031541014056030802151 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 517710899 1250 517709649 517709659
    0x20d020301230316050f0d050105070905090c040312140d0617160311240a180603020909010e0415050403020c01031a060a08041707030905120604031d2409 68
    0x1440e5890086a2082031442c04d52041c1003152910b014807a0030240c20034081d074480c642040180c0407902c01c0c02414440c8159a540c07072001820003040140d1544040e09002c000c40f024002800010400c2c044a01080802e06003101c1c40d0101c1c28202c100c81c4112010b07244e51500380003001410343e01511030400140c650100b9201e08020a000e03014011134140f0001d8100480b6800e000d259080c0f035080b48000d083d180c500b03458080310043c0080301540c8403502c00710014590001818402004524884c041c048600d0103620307051000340040e0541c40e041c01980c80445c2040007180421025500e00164180c480a041c01685420700300651a2007955034035501103070420045084034050b0110300b40b00d5840040144e42003a144200844800000610484d07500310f80d440041101854000030b8480740f03100b9510580440c0c20502440002c040a50052140c2e0f40903100703000c0004c2d0000315806c0450319005040d00030840300800070b03801c01128203a50714103038200782e9002034000c0310070014140144240c41c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 517712149 1250 517710899 517710959
    0xd020d211508030414090109020910120e030301170c01021606080a0207050a0605011716030f031107030c0302041d0c0f0613090501081e151b031303030e12120604020d020301 76
    0x25508e8103910500c40c0c15030b0311401910320701c000e460207030b00c81c6244030b5481c860000b8106800440649142e1081c1c1056184c203803c0c2031b8a4030214820007101142440070302c00350028148a4102e81007140e503a000e5107043c00b03542f000103031004129505580c40030f500b0100301c40b00500b490030f2400c0141020300902c000310794a515089212072001401c0000d101e5035114640f40c0790b1658840c00c0505487d25021420002e0328403525900450400c0f498003d94007640b2980703805442c42c41000308603a61407024116102c01407100703d12040c008694140b41c03800541d03410300c0c2018810000b0760300b481040c95110080c50542c00100d8a1003081d44924142d0758000c040711a840342c6c0e050854214810001c40d080030b0740c40018002611006132a405401ca0170901c1c01c6003091904081c0304042d0b4004680340c00c03100c80040c08000605503d80202c2650b0f561410180c181602e0320741e180c24843c410449040300e07001d40e800c013241c0d4584482d81100ca00ca01102070454507942c403544051801195514217640c0410018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 517713399 1250 517712149 517712159
    0x3070609260c030f160204090b010e0609070f1110060906170a24020708160204140906070f020c09090a02012303010e0403030209030f0d020d2115080304140901 70
    0x100480350051600401942808000c80c40b036681c2e0b0f0f0040010b114061718101626006880368002c1c068041c1c482c03455886590305003c129120300000424640c82504000d041c400a107421070f100f60364101003480c0410426010740318a0b454240e050302040074040c9031a00000c0c6280040d403004080d00c40300c5c10000d140079a0121895510074034801c0141a80301c060040e0035140840e01441454480a19005800c20003262241d650300c3d00b241c0007038603003600c0300c2c020340003180f40c80c1c81490006c440c08110b91056040c07250341c2e1944c0310305c024a45810300501908200c41c20b8000c000e4801d1041c40240444100d1030407121494440c190700c23800728042201c3c000814088a08805081640f038582081642141c2c81c1c07000c040718013080030b4015810706508210b1501c058030240008454544054000c25801c9003000f00207141c40700c600d81c18801c008070041c041803540441c2c031405003805052540442d031000d83e803070301c0320074069030f03034441880c46c0710000300000d100b40d0788108100c44010888480382d05a0381c0e9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 517714649 1250 517713399 517713473
    0xc1303061e020c0c01050307170c03040309050d050c19080a0f050114090a020409060b090f010503280b06032409061303051608040f080f120901120e03070609 69
    0x4010881e680707030000481000c440d4400d8011f558030050303924040041600c01d0414480300a010b9501000034500001003009050300244a10018603058407054882d40d06901c490351900320b10000507214803002c05c1d18620450b002684080078145180076200907030704c036203040ea26101e4088004c65030b950900c203c020300c0c00e441c000c90718464111103024100c40750311a42000020441f404040340d9081c0e541d81603006a4641140d142d100c2d041030300d04c2d910039505000406180c841090f070490202402c4c9181018110344140f0b1851125034000d1600308545c65140010741031070500409404115641010601c42181d80808240100c0008040c0c03411602c0d071172907410038001c240c030300680820b10070014402e07d4a40442004540e50080c40c032a401c0c0354903420340c0300300c401e02c603070258805610104400c00c5980c002d02600100c0d5075000ea00a280150200020305040b0305001e00c185013542d54100d00c801e002c2d0034002c44049079404036003040702040c9032a101d282c0490300030305000b4040707000c0e910138000e00300307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 517715899 1250 517714649 517714657
    0x170f010b0a0e04031404060e0112020406020a020922050604350c01140a09020f04050601210b04020712030b01020607020715050d0c02030309060a051605030c1303061e02 74
    0x301400c034a8003641041480d44a8060181003102040034a840321718241c1d9010340900040d2400780e8514006440300c01c001000305042c0d800c2029035510400003004415000624090185e905407030070042a03880c89003425402c11035403811142201e554031130008210700841e51500c25445401a59a01e2000800740b000300c4186040341a0000110000e049106801c41c01410071000038000104040c1075a0b0a03410841c9819110400090744450601c402c40c03a1a0802d07000868050343e00700414980800000c0c4016400300d00074251003028002c08403141200c3d00a0021054040d100752350f1280305183c200c603615480179051000900c2d001c0704803029032010a20174047c24403540100100f45c00c1c8001c6031070b81d4920031082010300c6400c001071215002c4500624141e03c2454001d541ca906e01210002d00f468801001ea1b00b0b40d61a10701005070181a80040002801c01031800c1a00da41d9103e018070fa00348074043c000125800d8084000082141907007002d251000c4a0300c00140114050601005030b0003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 517717149 1250 517715899 517715921
    0x106050904020c190b06041112060402070c0e0c0d180210030e161701060b041809290604060815241207081e030a03090c0f170f01 57
    0x9000c000e0560186080e0700a0288050800256080075064500d041d86054483d04100d80501c0f50004010052810b4480e40c8652924101800d240c0344980784000180000141102d00c150790100b800024080c80c4152032003e415000405856410810810b51780c0341c0104124100d001d0404030f2002038505202d440713000040e800f819020100040b040b003900a40b07001356102c5190f100f4410030300307802ea410b11281e40082015070020300000c0030100d8103d081d580c4176005007a00c84400c010401c420504500c0507103007882c0c00e0318001038501c40c030300e030011107040791141a03078445d56440001804c06004d80c60241c000c43d000ca0381044000c0d80d03200e9450b2141e80d0b0a0110364543c0400001840b04000480c1910310340aa000d4291030070003005001401c2a004000782c0f410310b174009071080c480c05804002142140e2020740754490310ac002a00d5040e501d20480308584105a12405013004001e01d1802020140213100080c3c0a400c0d207d46003042d0030301400d00f00d0305091040700b03610104003406109000100c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 517718399 1250 517717149 517717157
    0x51b0703020c011215030602090a0819032f03090a060905010507080f0c010504031124180a0203030a02010c180e010e1302040f050402010e09102310260106 68
    0x100e0042c0055459000d103000e0b154046884488002041d0000305c841e401071445024010303160002c000030f11050754126008516107501001c1250304503060580d20700384041c0d0610b00080d0b00c1d030101c1c06900c11224a50920300c1019440110600c4501010020b488030a80507078440c1e20080c4d031200e00722108a0148111400700b2000c010140c081480c520091580c548000d41007441c10103000b42117404c45000301d8080d0002845040c00306005041031040040b4802142203051404950140c1010800b20240c000a00c4c004102100841c082041c0456020143c000702502e48801d6000c001a01920321b060404c0c000030802004403840d0100c44441600361500038400003c26800e1a8107c0f80c0b00350b0250043d41d8000c0d00310704070070050340c650260b2418449000001304040c04c12b4400580804610701c01c10740304c0c1103614100910101443c081d103088400c160b0401114508030454407140d80b00954605401401124150000582000c043c031848903000111000582e170a5540203c1580300380988c078001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 517719649 1250 517718399 517718413
    0x50a0f090b0301061b0510050f09030c03030606030402010e0a0605040f06140f0702131505090105030318150c07090b0f0303070c03230f010e0c12120708040f0801051b070302 76
    0x61041502d6002c8109032808440405c28a07100c0c203240090400c221490251124200a0134404149005030050781e240029420015090702280d10b9000041510b402520003000041c1560301c604540000c8140c041d00c030300305840d2030713805c002d00e568418001c0b0a04a10700c3d4400007205e80c85208910316100907411a1410242c8940e0b17100c04c1603010340d13030580e4007008091804030a5601441021a50f0050201c41049203107004144400003030b05070b104074400c1e0814403000b00c0040b90b814020121120071a1800380c0070310030f6041e007600c9004144914086120340c01000c1180300c242e40c028806014115405000c0c02420300c20140d03039200f6200010030381c4c60400d008100281d842c04090007111142007190030769100900005141510404c0040603507034440040c900206404d102e43d003841c2d0b4090b43d001111092507400c1554544141b0444422000000b529009118500303068901030a0303044490b17000c1503900c0c250749010b02025103500a6039454842304010b25900c0d00210340e19142e068001e4510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 517720899 1250 517719649 517719659
    0x2506120b1c02041a221103010803040603060b0a1e05041a0702030c0307030302030a08060d1415070516032006071809020a080601030537050108060606071410060303050a0f090b0301 79
    0xc00c83d10810002003050315021b140b4074010741d08003d14040e105010085480c0c0346002c41c01016540c6540c00104040e00401407440110350001404080e0702090321400c0d0500a02d40c012135180c031543e03021800400c08008540b40c8046504010207446000320222080072000d1800c040c0c0740c0d60305100044c0035030700401c4901c0e907441c0103403429588010300420341046940d140c0c4400c040480510041ca1142c0c1140c03050841c1c280c400d00b920341d00901c0b42d00c1c1c22410722607042e025072104448400083c040c04180c114180c40000701e1103002e0780071100c20003618010f0821001c0a4088052000b8100c100c004000d804540c00352a80f0a83c0e0700c40c0560b5695400d292141e01c0150300402000d0518170410b1040d0842c4441034943c8140c3c50450801d088015883c0804018510100c91060b0404070701a08000e0a00005075106410346200c40d8018042410402030345102600e040c2e40c00c4210340b840e0b428040e00000707164204001d0318501110780c0f21500401000801159900c1f2640038604521005200601c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 517722149 1250 517720899 517720939
    0x20a0c02100c1e120804050d030213170a030816230c1605030c031c0315120605160503100605090607080301090e2506120b1c02041a 58
    0xd4035a50814110402490f01c50f001c41c070b0300c415a0701031101c0c07a0050001c10000940360a4040c0c102c0c42c0b8040c0310a0400f650341c45d46903c0346003160030800d500440d10f0101c800020603540020220580200003414059415a4031501d00303038426000f0810040c00109088616a901c08600c0001c0d91100f42d00038030519401c1000d4011400d40c10164003d1101003000e000401c44030380c402c1040314071551403620307100405d4680141d0f510028042c0e00140e4801c0c07003411085503414400c4115007008100102607040701840d07101150300c00003000c82c0d00c0c4404002d02c501c5900150090700c3d28180700c44e81100b41e1a09459621040d40e448841004200041000510070f00c041c05000134010301103807030178184da00c5552180d0000e0300111442a034600a5087e40341c03040106814080c07818003071002040c41f2191903e1895550f1040138240300000a69007207052250b4031004031804010b00b0107441d143e9824440040ca202c092007280102d1400c0080c0700c1010481d07543c0104240000c114080b20496615060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 517723399 1250 517722149 517722169
    0xb2d101509170127240e010f06050306060a0e04120201020f1b0c010314040b090f03181003150e060303160f060b0609031902060714030304061104051507031809021b01020a0c02 77
    0x11080a91b035502e0690681e0023802520340e0744104000c0410083e00340010541851000303044144503d0103001e0820501c010a100c01e5409600703c00041c134952203413082640640b050300e440d40000400061102c2404074075035008080200c080003102c4d103900e036a0b80190304964010a40905c181ca08500213400124403091180c1d10280080c2966041080750020900c2d50708003801c02840f100c41005020024244000c8941c0c44025519040c41450311700850364202017081e0050341380701e040e4040040d241e920308004859400d1007441800000c0085400e02d4452600c0d070b1a000c4490368200072110619141a6040c5c81c2542001805000c804050551441640c103400d40226007000b000e11441d408142080241580f80700c07140051070380c0740f6240c504042154022401900c1c041400e200602c100d40725859980d501d06099040e0030341d01c0e0301608084c2c40600c101c4600000d0909240d402295610050300035001d5074001c20124144000b61030821401c2c1d00404085100252500e9420070146c41c10070684 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 517724649 1250 517723399 517723463
    0x60f080a06050a0510031e090303050603010926090d060506130c050a0c0c0902040e07020d0203070f0201051605011a0103060501080405060a180b2d101509170127 71
    0x5003c0c81185071001d1f80f040c0c0300107002138003035440c40307140203140d0580642c40e48104100c1c000c00403210290b0b0f60040c070ba410050030000310ba1000020580c00702c00f810807150701c001c008004094a03030f4146851405480100c40c614010003964881c03102e000654001c400c0c03046015141d6a080c512000401c4440c40c2d00804169101540d000000808a45174070040004d000c900e48611981d103400c9501030301e0088540e40c0c501c11948200300710000b0644100d10011401c0e82441c6c580d9451a0504100004080000015126520317043c6078080d00080d20144050b183c0302030320140035441e45c0b10010342d0385140444025150750010340001c0c44094080c1c2c01110500c2880d15400500340588d01c43e0b0034141c000301c0322080304440c402c0c400c0002c100300002c601c00554900e1075940141ca8100b18041d200b849500c20140780e00701014490308000d0081000c0c40180030b8800051403015140341215001c4d1241002041140b515035400074082c40d203d640ca40d88941d00305184a4010880706004001c0d00594000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 517725899 1250 517724649 517724651
    0x4110310030b190e0a0210090e27010c02010605030607030e0c040504021c0b0708060d03020a1419050718060602211e07050c0609030a030302090d0c060f080a06050a051003 75
    0x91021010424410781300e204d86440000d040016803441070000714554007040006002c910300c81000300514004c0156402900c8011924100c010010840d9aa000701401968103508048a482c50194154000c108a40c0c0817400c0742c1c266102d0020541c2103c03044461001c0c980c00250880c100c500381341e0407140e000b81c4058142000100e011184000c1d560169404440b4024050103114426a003c041a078100101715681e070448821550069070b1020003040003881c241d02504200c0f200304040c08001e907189000e82007800d01305014585603407104044e0141040401c0506000300000815102e201c09803089034004001c1d481c41e01c00207684603d004001d400340c2820411913115500c800c882c1c492048101204540e40700c11152070030724103102580640701e0103900c080c0041c0c1825a4001042d903500303505401c0c01030303a40d80e01c1d00104654034070340030014054018010300000c1d1280d0020340c4201c05660303982d4014168994040e0881968050312503a94420a50f141c240628546a11481261007042c01c2c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 517727149 1250 517725899 517725931
    0x6040302040c05040e0606120402010e040f06090f1d0a03180b1303051b060d0e030717071406060a0e270d0f020c1809100207060203010504110310030b 66
    0x40001d069800394211007000070008541000800300080105400031001c4800d6421301000c00581151402c006001074108112280c0e1340856460741da11003001442e400600340051519210035501608280034880b04551905191511070401c00043e00b0036080c1080c090855007845480841d0082110901041e002800308000148664520001c0c50f2780c0c16218100d080c440e195060480c10040301e913489441205403858104400d6440c801100c01010f5203020005140300040922442c500078410000d001c114a42000f201d01441320010301045845042c07056441581d0f410a1501c4600c26941c080d041807200b5070034001400148a410b522000c00c10440a2200150800d9a410740600240f0a030366008a21580c030380650040ba07c0d03240501c0c03030006002c80b09081000c207035800308080500c1c00400880740482c4241c0c1d024800e20f440d1407103100c1e0554440703165080c900002c2d4400e100b15480340d85051a2a20050055401c0d02d100d01e100104070010946152940000b10380010884c407502680740c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 517728399 1250 517727149 517727153
    0x9180607021509010203070f0516021c0c0f030b010b03060612040f02121b0409110a0618060f02030a0f03150f15030902031002070201020c130218040c120b060403 71
    0x640e00c601a90350003060240e800220560310048080c0c0000000e90040003089542500041000e03d82d0505213021595030420301d8035449045c4010754029400942d80c400c01d404503141c400840f4a070741c0198440b42e00035558540e2003c0d034131040d100007000c04c81108e00400034255103002440c2c0c00361000e0041da18103030302850050384100048904031811000c0140c0c1c00c007076080842c0381400c030502010040c140b0055841c00401034000241340144980d844220300010422040d00c01c0201000240800340301035111750015140e101e54030150240241c0e1a4400122648103004080844001360040d43c50100c0c90281224140c0e0002154000e140d1182042c404503c0080348130002000302040c0c10000c9801c000a22070044901a5054105030a0101090260343c002c40c001041140e01600141d6070400b0b03200503814404076100840d404202c030840407038800c0e01c540041c0205d00d0300200c20101104000100001c98144e00020b81c0040d800301c24103090740405900005810b0780040549081c03603503075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 517729649 1250 517728399 517728403
    0x306090a0b191508030a030e01051026150a0b03010510030f050a0507060c0311010902010f111002070804030201032d02090a0b070809011707023705030301080c06090303090918 77
    0x1c4c0e8080c0700c2c036905c0003071054207565040c0306030280032070a00000d10950401c0c1941c0702c20590f0354003800301207040007c4036121402c01c6068a5290980b00e409032081c9080c244544d044200003203640b29542820141034050702c1c5018401c4a215468442a101d11a41144c68500b00c0c00f407461070494061190b03558601c04280b0030400e00e00100280c1c1c0d100c88100c81907140c02421070351041c0080c1056030400e01300c0c400503a0040b900f103103003107020b140c105005182d191100b4608003a035040c2100780c61001400e41c0900103050010020340f8004e0700d0922030a1001c04c18502c0e080c0c0060040440d00042441c412101c4031581c00038829100010000391035a501c442021003980e10604046448000004181c140703546c0003c005213003144240d8100c0158517001e207000e51281500161455101c0d03810503d54400c074285a61441c441140e980100d1224030145001540c0360310070b000f000d13003511801c00307d107d503460150304903448082c014000d1800c0940c0a001d04c0742504025122030a81c0e0b40e9000c07040001541 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 517730899 1250 517729649 517729691
    0x2040f020d180804051203160c171b06130306021303050105010b030106020d050d0608060702370803040c0b03040b04060f0504051c02070902180306090a0b19 69
    0x808100140e4a0608481c00000c42e4802d007141c0500700a016400008543c40100380e400711141680c0d40f505081c2c80f01ca0060651149180d081089000c1340005010b000d4410a010280d5900000c1e0b644030740340071048140d590b019620000d04020f0b05c84c600e4034250415038050000611a603403061125522036031010143d8000014031104426403460070070602c0424054540105403120010740f4550501038002d40321604004882c060040c00100c0503607045140d4001030081010b001503170742c10b0418101c0252a0f030314955a900d140038000d00c8591803c100741d0014500c142020001d001820307010b6a800c5116000100165444c1201100c0002c2c5401c001c0005e501c5540f190390034911600e054601402106c440b00608015a4944030070800011400144000c45091800c03440310104841c80d0202e00d044858bc01416a803400451841031044c420900705210400c120103542d0190303109545552703158444a40a04800c1c24900461040302c469014113003485180d94010560b407000c42860208891 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 517732149 1250 517730899 517730921
    0x204080f0c10030204030510020705070b0a030b01080a0e0c09150a0b0d0c14070206070606080f03090f09040209010b0c1c11060609010e06040c051c050105090a020705031905070204 79
    0x2150341007110790326040020065420141c1421401c00e401c540301c0a41c0d5005035070740c0402d050f600241d038209001080058500400101440f5503444203081d038001c014040245440c0d01085100d804182d12000341d014009450300520300910021480c0000c2007003003440584030000356000907803e40c02070749550300c600000c1c0c5a030200940e039902c41c0d400031404580b041d401d81420800701c200f048299130344e00000c441902e90102d43c855181d0480e401c2c008001c042035489040c4a1040b100382801c0ba04010001e0a00e800c0201c800d000e00c80d0a001c284400310f902158000d40c00000003006002c508500005091416281006c803031044403c54010010b680203c000e00f00490060340d500d030902401003180d264003d00941f060380c00d0303525020250030085406080c0038401c50315004510441d44c03290b0140c134410508000e46140c520110062000140002c0c06000d00852a0100185904c0424000c07603c00503070090095203002c81811a800d600d0413411140c4040200c10400c602c0580d4560081c00e6a001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 517733399 1250 517732149 517732153
    0x6152107090806250e06091e03070902040e130c080a03020709050105030d23090a0f080f0d2c0603090c01030f0e03041806030b040812060d0f030c060204080f 69
    0x181410304007480d0681c01030410b8a448001c20b643e041d50502280c0c8903078080480e00b080c4020002a0740066458080c00b00e41c0d0b0f800c0751103a2301c401114446a24401c0511005074280c41d042512000d00f0380c182d04c03d6006c1c40350b2840600c000f041c054039400039944459070250030240a138a465442450421810031801d4006034050402807064030918411507004000440040c280144280005841c049847c000641c040000b88021110014010111140030f0340042a8a82a07074441c984450350300e203c2d00a40349640724070b2491300117005001a80210340402c50b210b50301c034002c1e19004c50000d9140c9000d40c0301d0302a901d1a0513076458540402650050f00280060b05085004d44001801c607640d0150000d945800c010030f9100020f404021581510042940c0c410100304650111000e452594001003404049004100c2404a46c0c1c0c060300d40310352801180b40c0580c451100b003214000740c503e8086d02c80310300d0b4406140040e0007503246a80d168458000541084d660302800d40c140011700d0010b00302c903 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 517734649 1250 517733399 517733417
    0x305030304110f040506030c010c050717010207060c0212070b0a0209060a120c0915050c0705030f0d030c140301090b040e0706021f050702071502010f0f0c080a0506152107 75
    0x1501c0d001c0c806a04519066130700700084d240c0100041e5407020505010340c140f004585108080c400d050102c0d401418102a60441c080e4001410314001d500c8040d0941c0c0c001d11300f98049240d01e101080b85000700040b091018200291911a00c03808a009085107000c00c0c1d003007082d680191551030160441441c07648402070399030302110186055a4411200c0001c02c400440240f202500d45281d6000d504c000e8503050780c84026041001d4a0540340d5000300d585032080b0110304003031010000d6022038000b420742d8144800300840101b9039000d0103180a8040104007800103000083c0f0aa002442c0024014000309050001c0c0d0050f904100041c2c1101005030000e14105a010b204110303000c0c078400226408010a2511300002904c9145500620040b01c01210022803821b200350042486080c1e403000402c640c0c00300500c0f42d00142081c003c1c86010030640e0002804c804010f1080d544581c5000d00100c1212803070800318186944a0441c1c445ea0000e001c0742a00208a00040c4601c141860b40704d980507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 517735899 1250 517734649 517734683
    0x10f030210080108030315191212110a0311150f06040606020312150a0308030106020102030601080114090a020a0504031b1a031b0a17070e120a030c1401060305030304 73
    0x1156510808400380002d0b0001009925070020460384d002004100001000c2e441c080000e52119a207660454007000303021021816000d8400108200e03031040c0d0b00c2d01d10001d200c0d1400e480c000c51003000ba01040d00645482c4005c28044e103800c1c1c04210a0001352015044960f85070968141c00307407002d1080403000790400020b800d15110360030140032075000440c10300d094001d0580b41140c0040034050000c901032010f988940754036030b104d0080c6601002c0c103912507841b80c42c004d000350011901c031800101d103c0300015500c074886400692045000d82402529900c1c000c1c050302940c802c0030090204082004004041101314114a16082d046030742d40204601d020f850f0000c04140244003208084100140710305510b040b10b0755080350021010f9507484d0701c00c80c101a1150100b010341000021110700810280e01d40c8080007203040c9404035040101c24081c091407558881129030001c000c503003104030b0a804550249402c1d8a001981c034000708500747c49954150964109650860b038400e040005500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 517737149 1250 517735899 517735909
    0xc030709082d0a0c0b0a1e0f02120313030327060203240d031b0c0e040b01080d050a0302030907090c0f110a0804060e0f120c03070801020a080c130e010f0302 69
    0x242d0b07100c040201202c102a480b02c54481c0c11a00c0f60b0001c1c0032000807580030300b900400c5009006461008030039002e1001c03400140c4092149049080140543c8003a4100d011096058a01800200c04034181020076541c0507002880030002000084c901c5030442e032260782000d0300700d00300c440c400c84000d82c0b1707070400700c1d610900e201d8580341131851440804001c80140d1141a1b03080c0d40281c01d031034282d08410b80c2040d800c014035103c820150442c0c0c61150040f038210b20703029205020340d101d61030210b803d0f079031000081d40310200014080c0011740c0030006170b5000c5200f50041c2d070300308a0b0b401c10748051641e1103606404880c10b0361100b50215201680760b40c1c48541203503151050310000300c050980d01485503210300c01c0d03200350b004e00000c0c000c0f442e010802644801012952480f4058800459070095049090340e414515a0b55413080c4140c0501140340101802a640c4068841c0c030740610300e403603144108000e604141002403601503050000902d0a08486046000780b6038400222401e50550052003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 517738399 1250 517737149 517737223
    0x412030e1507080a14040b03071d0907031d15070f11030913180507080d090f03080a11100605040c05090a06030f0e150603070501020f060c03070908 65
    0x5106070440010018120940400c4500d02030b80b1403030440d80c40108600986107030503401290840d5040c08940402c00a0640000b07502a80c0d0701e0301c03800c8044500c0e14107100c540a141c0c400c40c3d08a40c035903010038403060080c2c010003141410704110742e54840102c018146414220000f00e80a00c00702014030120b2a004410401880c103030713107010317081c00880d5280c460b901c0c031071401010b01070510320f03000c41e02e0007607954800110311449005000745c0503024140560388007a21b000e019440d004841003c1324980c01a601b540444000c800c042d40788078a50740b5400f6480d0040103080051002c072044400b0b01100500041c030003400c0074500002e0b15800e04041c0002c80c0c2c029921003040c058104040780312655442d207010102c2c1c9541c500869090304600c0b00b900501500082e040070341c840c1e009940d144048007011944141d5054003180d502941e100c004aa80350610a0710904030380100340031824200030440290f904c040305042c4444042d41d60840603281c0005d00040140321940700a21108902040d803601c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 517739649 1250 517738399 517738427
    0x1401020a0302071e030503190e04091523072f03031b040504020a080a051605040b03090106030f0b04060509030301060e040b0a091d0111031510020a020303041203 71
    0xa100300080c95801968032070240c040c1c46203140c0007248030310581c94800700b400c018552040940c0d0300c03180c20110a0304104a900c0303041005c5034511100500a05041c42031134001c6401c0418405080701c0d0008000040141e940b00e40c0210301030102000c80702d0b43d100006800313010380d03981f02000200b07141c002e05114003100301c80c11404040e9078003181c481c0740004290383e00301040081c5200c003040192540f244912030b0b03501a60300301d400407039800886500000440e1081d0302e404401e015956840f440076118128520050010030301c02d10081c000340f01100301a41e0303c14020030001500d26180e4581c0d030b0841415441c101c8400300d801c000c00c0104a100d004064008007800000e40c1194100b00020780200c48140305e05005903610f1240d201665139540b8104001c2030941001c0000c116007030340c14002d040f04a00b00c400301e0740c00c121400081c51480e004603446001861081101c149c0d03004204591615038603285c6046100392424a005a40d0500c0203100401c481c02c052100704220b440d0103000c0c3d03919074000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 517740899 1250 517739649 517739653
    0xb0f0106021911130f0204050a0b0a2705030303040c0501020f0a021f02031207022b0f030f09151a01020a0804051909051528270e030301140102 63
    0x3080d280b02220001c000c1e441070703005112034048183c0f20049038402c07440d81c1208030581e0518010b1100c2c0c01d0550300802c00e803a8182c40251240b0f4403060f4a0149100e50700211000800400c00340d20360305070251002131064403110007104803981d1200020300d960010749060381c0740107a42c2010429980c04000b140f44401c07903c0b005e40388400c03454000800110f6412030001404020304007682c2910310034404c8464040400490121504141800950342d0085a12902c40201070080d1a6011040c0805031400b2104541d144c2500107403000d81200508100715000b403005485141c640700003100c0d1102c1d40741e8065151400204e5152200d00600380c40b25803c2c409042d504030600d03100115215008480c00d807102540e100c405005117444441c0d1244480c0c0c00041d500d4500000d0140400c466075081c02d039401c0c03c4038030210b01c1020801e560810241d00104066148010360100f105a001103000380c0400d1031b0204069a071b010483c946001c2d1b0f01021001e06160700004018440d1545901d01410038071001e02c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 517742149 1250 517740899 517740913
    0x70503090a090e10051b030405070f050603011512090816060b0d020306060d0f0c0b130609080a02010c020f060a0503060306070903230c060d09030806031c030e0c09040b0f010602 78
    0xb0403e40c0350980070f03c002c0c2d4a42d884000041091104500000c1041100202d0703076500e140505126460b4a842e001d080e21071000b012000885143c1041543d05803081035040807141c3d00c4c0503000303894645411080c4500582c465004102103000903028080b0702440f01025030700d241c102d00e004012940001c200d244503a003810f103884003588000074129400b0341d050340c81860454160030580003988841c5401003449059420200390101c5480c042c10440305c0080d800608152145000d580d80324071401030000592082a1040c0950300c60700d00c02d280a400681003010481006002c19459030060b9800030201d00000180841d5080811100d580840381d45004112541507507500c007a8410240c1c0b00405040810440c003051a409111042e84110020003142d80c9100d54850440a0203103180141d0205009200240d11407d001c40d003541d50704400540c0608282c0f200300140c004013a4030004120038410a2188904c540341c010134940500d018100301001441c0c124007070018124140c001c0021500490 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 517743399 1250 517742149 517742171
    0x4080306240a0c0606090608030d0f14161e02032a0309060c010209090a091506030201050f0f1201030311190c0b030402030a051e07140a09051803070503090a09 70
    0x810b403031803201d4600d0141000c2c09a8108100038240d942c002008480c40c204c000105ca5200000805010300c0404052100344105081c2c1401c0341e0300c83d4501440b00702000c000038054030900014081e08030660030300c41005130700000300d2400c840880441c2e00240e400042c4001c20801402c80100140800040004407071036078040440d1240503007001d29000b410f010030307107110001c021b4050710300c0305401a03e142064a05040c0d048050541a2825500588d0042a40400070b600b8081c02d02682c1e01a1156031a040b120340001410343e10881c2e01c1e20b24140240840f109d407143c0c4035800e900a43c000c1d0384140300c3d000140105030070b16111814944103000300600ca507000a80d032010010484151691075512030340c0368000b2908140b40c2d0b140041180c0681c8081506580c8010101000c2d540710b0402c68024603220b00d0354601000c1450302d0f081c0e002158480400c00c220f4203400641d8414161084c81052050000c00c1b60300d10b42200390211407507080400d150385181407180d15900201880e04052000391889 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 517744649 1250 517743399 517743469
    0x150606120519092d0b0114010e011215030f0302120406140904060503030a0903050f07032f0a0f0306050a0501152a0b04060b0603041e110904080306 65
    0xc669840080f41c8800b00c2801303001c841c10001c02109500e20482e512041440e40c0c89800e000d210b80101c60000303a801c0046092184000300142008041e103a01c05021089001500d03205038000e00c000c0d45580f100c0c3e00207280383c1c10ad07591200451003126951102005d500e03029040c4a90031042c00e4074180140420488503070700c10b804030110000705006955980030000420060030980c0c00040d014800003a25810040e4000350030300490f4007620680d4401104c4c0202213403989c00c036101c00303421020401d494008004480300c403840303030013101041e000c0c1806284d40401c5008038160701880c510506030408000b4031905000c1d19038420074180c0c0030485981050034048540b008100c8001c20003050404c40d1403d02e07040000300c003100035035500d07030303111100d107407410001d0304108542c226080c50034105002024203221081e41c1c007071540f094820305501035040d1030145800d20400c09450750301100001c40c010347c950021180c061802000740e9075892170324000740640050f0510b40d8801c14210f00d04680c10f4131181c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 517745899 1250 517744649 517744681
    0x6040c03020a1d011e050a090b0a0203091c0507080313060207050d060c02010f020f09190302240904020a080109050f0103032c060c0c13140402090402010c1506061205 73
    0x20040c104040c0c4059040121104518403500302d807003260042004000c5c81d040005451100810b586448600d03071a0120724206010f40c1868001507842802800301c0fa02e4241421218548a0001261500c4458603240e141030425844402e064100041810b003520801d803804004d030a90740002c002080c502404030341e40004125001d401f1076510190200300070301c00c1d045031010102440d429901e95101280c44020f541c85040400c0c4501b4010f0094034400c4110076070181200d130010724450150b50450303102548001000000c40035200200b04124141d070f510b1007d0704400c200c555030394105606110354241120005442c0c1019034032424010000680d100c500a41c5881c50143c4103540320030349000d03155201c1d84804106d40d0002c4045001c0306281c8001683d1054440120b554480010b400c188000840d0039440c08201e0a800d080006009170414400c1940c0003071062401000c8401540c4440f41480d00e00c028041c451625501c040005690042055018511041e010025410138906d00034035444 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 517747149 1250 517745899 517745927
    0x50703080705090a0303080106020f0105130f15050a0b0f0f150912070914130f03080601090306020c06010e0618040609141b0a1505030609060406090f0506040c03020a 73
    0x140e01000594603622440039122a0f40b409001c030402d141e264900540f401c0d1003405080018410140402d00c043c80500a040c000c102c40040c410b18100c96480c1c11310340c6070400c03030141d49104480001c10045d042034481d50f44254a002e200145950b224000c110100015896841c07084000344141c1581381c0d100c884141100d83c4100c0840e03503c1000c08045424130103d1001041d45006074000080d000000d03801003803c201014030031001a50381d034442d1403a0340c01000380142c40d02d1001c4070340c3e10010703016014003038024005050002149540790348883c2660f0102c0890880c2c0d0b045a0010400d42d0b42c601448d40d000705086a4070304198030310702040e41a03080c0c020809071503113071100400b8007402080010546a010703a94240c5101031280310505850240c10310500d030181e403400400040201c644181c41d240380303190b99196440c42d1204420000d00c02000307000194046e58039030000440b100148203000800030b6078640850149000300030842200e07407244c1c0d220180360041000054a65110003a000700b01c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 517748399 1250 517747149 517747157
    0xb04060e072d020c040b040c050301090203070306170f0d0f0c0f26040806070c23100e07030314070f02010503250806030c0a0b04060c0609021f0915050703 68
    0x148480c0000592441071a10065003002e1540e400d298440c2d0200d0f2549000a0940d828401c0102c0c801c00e0104a0b40d024400e100001c8050005001e40d11280d001950010160719000c110300792240e1042195807a11404480b80340e202c4044400c040006000d4024004400d0274042d01c002d45925001e072100080010003000d00c0d0816080b0760800c004842c0440140e000180c100203680506050085554014024080c05100d0035000900aa00c60901c0240b415402490703100e502e48101a002400c54050840c0b45050049002899a110443c49407040d4800f0400c000c020503441c500b0085d24071603124990204010040140c80c02044842d801c000c8500d43c213280c1f03955644c5d10382e254032032184200c2d05225003510945000c05141c0c1d9104041c1d0340110021019242e001420000f0800c000900303108201c1c209100740301c10004c060113880c2820b40c69004540208400b441c680c002080c03502222a10340e600c80341c400c0138000040c3d00683e841e000d07143d03100344c00e945c2040108000d802c0d4001c1d00c00046c100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 517749649 1250 517748399 517748417
    0xc0424020615040f09030503060307080604051c0c05060a0615020303010b0a081e0c04140402120a1a04110d0501170a020409082802120a0819020408120d0b04060e07 72
    0x940c41e1a4030607162098054020003860f81e2511b070003042e03a40300b0b4031440e10038401c480001c24480000b2842034040d80c1c0c000001c0c09800f4051107403180c560811180b00050040c00819880801c00602c4068801c40c2d00031000607201d41400c8241407178590790b0001c0340c1154001c0c030040c403101540c4000c8800446035414480082e564080c1c0c0095010000c050075607070800400d0600800c88150340c068019500d50740d0ac102043c0740100b09000490103030711790302c000141c0f03110302142700c011003036010441703480e12942055000d4420001050a81c2c41110410015080018a41a074200f80f482514094492801c200400560141006583c0d528142d0040d00c601e03500c0070799104103c1c5840c11540c00302006448181c100c40064280b4a00380b0144240c900940a43c4007070018001c02d4200701c94000c5010b896525180d00d0310621420354481005040007860303402c0101007805082000b9055a0b540f00c00501a50303079800b81b401c00f0541d1920004030307000fa800c0020a10040880c3e11116078012010700d001880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 517750899 1250 517749649 517749691
    0x190e06150c0307060902030d0305070e040b0105090d05150705040510030b061e030a1508100e0f1e0d0314072d17011202060f0c01090b0c04240206 64
    0x114400d0341c086103500c0c80005521002c00601e508483c08184c001c0f416100318000100040e81a120b04032200000103c101410844074034066210520f0b869041c9801400d050b18900404da008488840980d01076101c0300e490a080207589081c00d501c800b0500c1d115017810b02c2d003030220382400c11010400042c9070711400744000c42d450365001e86030b036600b00e503580f1603a15020020581c010752040e110360014500b0403102c21786001c4070091210444801100401404001c51080d000500258078110500e000d40306650303c1c410020032515264065524001d4074140d0340440ca14902031101d41c0c0314052600344008441d1100e01c02c151303e5032140c414100228811100d864810800030003003065000d07848407192001e803240d0b01600f149218001039407644031607600c50b10881c41401c407101c0029441742040003040340050300280507000e001c5410002041030b030015501e003a0f034a481160784021359040406e0400079544000d40701c003e4850030311801801070103194002500c54400034007401d440d003140340380010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 517752149 1250 517750899 517750939
    0x150a02183a050a080703021b0307091503020d08041503141501020313080c040b030c0d080f071205071a160f12050f100602070e0f0a11030405010b190e06 67
    0x1075000d52010550301d111203245480d003140e800c401000c1d801446800c4175142c82c5100c207040d12a05980043c0100a90382c03508000c070340580b0f651030040540c03080c207440000041c0c07603040310000e0b600d120f4a005500c550a042d160800e4a6022305524209400c1503190b048a036400c03c8030980150003c20030550401070f003030050380742d407103401020f4400100180700002c0d1404003041003242600d085809200e9114180d0815071b868907040241030340a1088240c0c240000d000d00000c2c40f418112200381410002c0644404860300c011505000100b2000101c41003085084c4802c84212a01c80104540034104100c024840b00140c2c1e2108091044e160510b0165070b0042480c40105a2010001e21481c03500d031403200812402500c0c10403050300300300004900240082048011340c0c0446081c100d00d55101d91004407803641c0070b8211b14400b941d505691840c0c44015009510850040d000860b20310500014030200c0010360345142042c048158050002c5400715401603000002140da40f4404000006145 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 517753399 1250 517752149 517752259
    0x702010903020d0c0602070b070c15020a0510020304060f14060d02041506031d152a0711190623040e0103051c02070612020c150a0218 59
    0x2e0760040c0f0b411940c000300000c00b011001520041e5080c0e0b20079030758401d184c403440d0044203802418a90000c0090052078105102140c94044520440d0075440194a402c1d0801c1c030420321041905400000304001c0c04098010003100701001c0c3e03004c016100b00400c8180d41503070050002c6104034180340138501590b5a50708042884180c410010804a503a910080c00800210802d854015101c60b0003400030b000204903c41540314ae030b4844c00160f40d5103100d15030101c0070540307508101020f4400a64203040f01c14007601c0341511841d5600e168441c001d0401c6020300707803c07107000e640715101070b400c0c00b490394451040001503103102801e100c003480c039608400144c06980c0002d0262081c0100020a010700000c1c650380c10144140081071000308000101e8407041607010301c9000c50319040640d58a11019030003410076542030003d0f14100c40c414400020350701d109a80211100f0b0300802d183c0b000c1d00001005142e100c0c3c007203072039445070070b20740d00e080c444019800300450200c1a502940c04901407484204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 517754649 1250 517753399 517753403
    0x807120210032408011a06030c16031b06020301080f0a0804141809010903110f0a0f02032b02010c030e0601030206030907080303040807030e04050403080f100504060b0d05060105120a020702010903 86
    0x318030001d0319075290500070940f031408031400e022040c1002001f814150105c034050007100742601d14208000c01c43c6800e21003000307021020040c05401254800c2d000102c0080700304d1281101503070ba545412000313442e02040e04004406c540200c850340001842c0b08040b1411912a4545006140c0113080010968120600c00d458494040d0080109988065215a86452180c0c440070051000d500c400f590700e5642c045601c1841e0300aa410001003000090407041d114070040807614208072562000d00210810070101c401c82d0304065480210540a000b4041c00d21200d140c2044000f070324004050f6034510600c000390054100101080b9001410302842d000790032824100d035524100f914114071941c1c0300480580000d100c90b44200110b10b0300d4000d0034015501079596607655107451080714000000641502c101c120100070005075a01c0300e000d00001041c80114240d1189082c0d200c01e4182d9000078402c40c10818104070201a40c0c40902003583c10420210700141c031090f0510060f24080c81903000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 517755899 1250 517754649 517754711
    0x1060206070207140a03020a0909260a080a02090402070501061a1c020f040b040b0a0e27070203090a08070801061a0304080901090f0306020c070503010516080402040b09010f080712021003 82
    0x11071007072450303002054500c0c81130042d001d681c0e00c1040460740b40da20500c24802d18bc0400c008280c0c0c914400c0b403019030041045070340145805c02c40c0c4000340413030b4813064040310181d4503058204100c80f4030250513400c81c080e141881e03160001583d80c0841d881d500c1200500038583c080390504140c1004c0095401900c007402d540b035a102d45464910b803070f070740140706408001380b2417116802081c1452050142500250040c001820180b01183c860416004204408521051002008950300d0a0079580209480320182c040181451600703820b4a009411040901c600084200c500c280d0303940c1140c1d80235420940c0d040d16080c0c21001207a407100d142d4000314000c8403100c800700138011290300804403803140004580946596400341403d071a021211101d03417081c0d00940c1c154680c003400703500f86d0140c03000b440051000c42c20800540c08040030380000e5450282003c0611001d2000c1203050b01a04020200c082d02002a038001400c4103c114400e00c109a1614000040c0c40c0c01c0c0341c111400c0314003101c0303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 517757149 1250 517755899 517755919
    0x2100503010905061c0f02042a02060f06101808010507030516020c0a0b070807020402041212020a050606040c030b030604031814130c021002070807030801060206070207140a0302 78
    0x5085820a02840b0714981ca4100458003038a85010481300780350ba038100603001c0a000792140080e0440329082aa040790b02c0300181d650002c01c080035080342845801c2d2040020005090003407410800074191951408203006001c450380d1201d408605003141031034545040000d01940000c0301e0b295611041e925070910301805443c41d0190400782c481d40700d64100088140000310220f90300c0c1d82d9640c10641010082e0000e001011002009241450046a0342480c00c03040b40d02080499000d540b080c070448034640888400c0001074407484502c500a44002e01e10b90100d5141c1c944c40d00c501900491081c1c0c6d48608283c011802a04100e08402c8001c050f0303801881e140c00d02610f08030040c802c2091490100c070000c1800c2c103a00c00400305010000d0401040b245110400d00014440f629a21055214a03080c1100518803030004155182c030a0b542140c075108ac0c1c0c46c0141988406810850a40d04040104840fa543c002942c0048400707100d8100040307110310022031800f640c9170f0400380d00700c10489 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 517758399 1250 517757149 517757179
    0x201021e010c081612021b0f0c0a050a060905040504030903050a030e0301051b04030204020f0c070f080111251712160e15030601140d0905252102 64
    0x341c40001d0061090703c0b00c540c0c80c1e44a0711901c0f4030b01e51189020011541a00642120014903809002c80d0080c01c80480c02c489049403c1c0c0d85010801040514a540003200140c07060900644140007040c0540d11b41c110142412009400d0002c5800b0701402a603a440000701418410f080d000c0c0150740020a48400b9004ca090040191064441d0a8003039800c1c40c02103020629200d4400036440710701c00c591401c26003107900304030283d8491810320701c1080040c4507840d90f0003414403106000f880c810444c100003a20304000c0341d00f9204903101c00c0454502c180489568110543c044000305088801644c084144038a091345040c64604401c000c14036000c2214007031800035400c014011800c02c070392010204038114003110600b82c069401034000b072190300306a00040d220b601454000703905040840400d108018401039680081803084072840c0c841000c9e0341400b000344401801c1c4046a954606003d2a800c11404101e071303e4030807a034882d058a5401c00c0145456010401c015074000e000e410351040030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 517759649 1250 517758399 517758401
    0x4111206010e0a061b050106170303040c121e0218070507030810120f21270f12021810051e030d0f02011515031401120803040201021e01 60
    0x100c0340540424500c00300c4011918003c0d1400c0704039003850b42d0b902e00600d8071891144c20311021807000c582c15034a4500100d5107030f04803040c6010703020b900802180c80340345c181041c80d400b54403680040030020303032a400c04d808180040c503184c00c050401001c0b040c64203054804126009400c071006d0010391024814000c3c0690f008000b0a41240242e648040545515032000003009191003111201100f14100c000090f240f0620320442c10b001d0a8101d09542d442e815030b42040307201d0455400000c410000e2021000400f403071180d003582404c61114183c40c10602114070070401030103064180107421541b00c085640d40c035501a0b045c00b000300ca00f11541000e00804000706902d0040c28400c0d01c100f81d0300e80007400c511201d4020240b00a00402c205216841c0550780c918407410707900219521540e820b21401040c01b001d00007011000012441e0305130003030000b030031640c031849d4451040c1c00d4000100854004040b10010482e00544c1847d560344481c40181e28003003015030780c01c000000041c1240d58103241 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 517760899 1250 517759649 517759651
    0x1101090503031e0c160309080f060f0f0702060601030e0c03100516021c080414150a0f0204030305040509060103090c0e071b150e12040b19030209010206070c02041112 73
    0x48002c116001c456465250707030180f4044843c2288501c050240801c003201d41242da5807080d00074100402800c4e150b040d814104440030a016845070700210034081c0c00500c0b51202c96115200101e2519181400b003002522540e0181419042644030080c130503074141c01748000d14289400500f05c880d10030700740380038130003070003040791510410b801041000040380d00125080000e002d003005403400340b189518042e0395803080a0400da852000f51180762109a8042000095580c042c54209030325251400541c0d05644034050489809030046c8401c20010b030b000010b40d000c0d2582101ea072880c9a0311900103d000b48202e20380504044510180000c260711a0001d0901803d000da441680c4203400341d440480020b801c1000800450100211400e4501c29601505049480c1001e0710440b402400f9419201c0e08260441031400d0400540100042d1000320400519031850800b541000c0349400040c1d21071200400e14010300c084200311004550b00e56110302d400b01c0c1c14405298842103100344058207248 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 517762149 1250 517760899 517760911
    0x30d050103022e180909080705010b10090504050a0e030a120f1e020309250609150906140c070906050118030b0c070f2a0b2701110109050303 62
    0x1c8001c494500401c100040d83e8041c102a991003180110b0b20007110048071106030642c03490300c0260301241c0c1420a000e0380520324014880c0c5600d5650343d06243d400c440e50f9849481c0b0480c80042036410180d00304100c0b070220703201103034001440d0380c400040c40d01400140d44c1020003400000380e440b0102d03401c21110030480202d01070800441d00080c03622021a25007120041c1100003000d1081d0900400303030011039004200005441c0b030714514190040784060301285411414113401c0040c4200c60b844010240104a0040000800480200d014000c0420342c000c120411040c0c2c003d9041462056048402c1d6024050845100f80d070f071015004002c001a0040600041190300c130785252180c0018140240c0782c1002c62455551102142c00110351b10100e800c40d04526400144400702e04681c406168100a90300e0b15140c80282260091182843d6084100100360a0121001c0c01c441540c01c0a50002d07081d0004031400b001400603286440006400303c01e640c02c1c60306c43c9003008404005140a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 517763399 1250 517762149 517762159
    0x5090c0304140105010b030a0c050d11041404060302090403270b041401020a200d0b090312130f1b051e1203041a030403090b0309061e041a040501020c030d05010302 72
    0xc940e0098243d138420310503c4410388081c404251010019805108960b9550615924101e00811361009030303806507200b4411000082001c00c4480085c00c00d6240340342c02250100074190542d8009810030304064409020041c550031280030744040701421440007003a42110a134050707901d00c0b00a140d98028003440e46150300c107106203a2903500004200e0b4510364000c80c480003400b6090228203400105c0c00307101c0d41c8000c0c5204560013092010010034003030315250014503907a60102e240c006414002500508004220040c000c0c08110340c185016a10740e40b05c01e03442c5481c005008034940c042615001240e021180409018003070794036a03207205030101d007a18054410502280802d49034069481401c000c1c3c1c0500c801200c007100300e107000355445071090815074540c03070300c0340f01c4150705800442e0000150745c0401c06100580301500010286030340000d0300040186060350b0785540c00c1c1d500440c151009040207000c5001c00c0001c0d0190380000c4100c40460b5250400c003903824018010a21069010b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 517764649 1250 517763399 517763423
    0x304050f0d0e09041401060b04030804050f0d0b011403030912060f0630100204030c0609090504110d02040b033703080112030c0f0c14040615030e030405090c0304 71
    0x103000b079030a402e9000c00200503840f55510b036151505240304019082159540e2110003043e560000e030b020303202442c01114072945841c103100c14001d900d040d07244078600c9688045040e500042004010a042d2860030036560b054483c204046032031802641d1029501543e4501c400e2034400300040d00503c24000503c00d00300365140d00040c0003440e00014400b11101105455003800c141290030100c644414040c2219442840070106d82c00300e8205da04101c4290542100804c143c607072000050026144c050301c1040141000d5903590a8400d82c50003403070084612815060955075a6840645943c1d00a41034640a5003003e12800791684040316800c41000d10070314802d00502000c0b100111301e90700d5120340441d6401e18006408210500100b01c04125483c0da40a00003500d080e100c84210b845a11199449400e01041c0729840050092490090b4600b250030081d14801c0c00f20100750300c20a080c0007032081388031224981140300300d40115400080140a01442051040081d0f10940c024030340e801704 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 517765899 1250 517764649 517764673
    0xb0414011a0102251d0906150105040314030d15090e0a020307050f06070501060902040e13020a03060c050403290903040614090a0e1003060b011803080315060304050f 73
    0x10544032281980c0103901481d50340c440c10784116128942000700c009200c00d20745d541c014900000c0c900c007551601841c280f200344030302c0c03102c02c124494000747c201c038091031100591030000b0a18011840050a5008034006104226800b442210040b10943c00e050160240301402060700410724400c0f007403031034076101010840d40e10108115008542c010003500881e4540b008224400d080f4100c0c06a2001e401c01000d80010000d2082000901e40d05a015031101d1600c4280c000c1c1c10002880d9115450740001d020f40169280c090340001d80345e021400140c1c2002102003100c490145400080c691101800e4004046041c0d448841e103580c00c007901c070320a681e2040f240944901035071082070041840c030311114110105e044d000c0c005466005e001402519600c800c0c0390070f610401c0d551803120000c0c9410510610645000c0c1c1280d58a007800c140024003040c0d40b00c000d55404d1444007424002d408400304405109a000014600c200180015103a04041c100192035864020910515200e503c03600c10fa = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 517767149 1250 517765899 517765931
    0x60f0801060302090a02031506120a0b090903270d150501120f120201020d050f0910060b180d06020c07060305090a0b04020925110709050f01150c0b041401 68
    0x7565405003c414141d207513030085c40041d40000e801444c0c2802440c00d03150700c85e19240098007244640d00211001c505006000300200c5124074511405000e07500100017a0040001c00c0702e5402040310003100c00c00a9108100d00500c0400400c554804600c0b803c150038421400c4146510b1741c204503080066980e0f518400040200750b2000502c0f0900801140001c01c0c030201e20803611280d03a000141c5801030881101d42114030844901803001030382000d0280c5454208019009a29499010443e01e42440c00e180c010f8019402c405a20420b042907101b1651a01011952038075401b440079900c90a18030515900d0b99410f0040c80c1c000303840d10f000070b10405000103208200d142c00213400d501580b5660288414210003e00002c55210045095100250689c1110108103807503980d0408a003120b40c209401c100c196400b5039105418101440700b03003d9040c4015044581545a03007202a100701d40a8030707181d03850700002e06000007400411041c080300c50005402d07058188001c000c05001601010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 517768399 1250 517767149 517767161
    0x10f14010c14341d0903160f11010f120c0c0507261504020409080c0d020f010f06080c010e0d0b09070512212a0102090307060c08160c080d03060f0801 66
    0x82c06645a0900c110195100c1d84d41600040200700b40e91500284007000481032000c0107040303840c54884c41101c0706011302010030203008542441c202407111806d00004050410080c880810a03513103000e0260011300032402c02424036804006d071416143c0c1c502000180d40080103100540c4551034010b480f4840010074004103009010200316040c1c0c42d15000d00004004601c0202c681c900c08200c48040681d04000060a00d90203600030108080341881685c20760301c9a05401d4840740c140001030014400c0032888420a0100b07103480c0e101c00411500083d040b81e440800501003800c19014441c120001040d28010b0f0384080d209460f0031a1001d40080d514560400700c1304101c3d280f081c0181000d6120070080044040a050f43c01c4d413401c0b40c0c40b200024080001554a0b23aa50002c1c207030500342003d024001c003d12003410085001480f503103c02c01144112840041c0d4080050000010082d01550500180c07409008a941026241801030000d0a00d8050510b02404003940000c140505020312 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 517769649 1250 517768399 517768409
    0x231509030d060e010e0406020a03020705250b120a0b040216030804030f08070f0c080d06090504020a0807060c031101021207020309010909110423060f03010e010f14010c1434 76
    0x1003105c540c0c032034070354030000c0d0000c0160302c080540800111002c503104012598800401e20040c0100fa0400380d044507403a0710a501c1120b0301a800d20031410348140450360164883d2640d00e0214958441e1ba0000b4028850740d0285d0440002080e4101e0505500201c2030b4800c030311076240d0f10200c100380f01c03081c0d503c04000c55568000896104101c50800d2080007680c2d603d41c0b254055600f0408509245402d4403100d030000302c030080d13580c42040306605d031501ca98802000c801001c4d1541d2800c0c010b005111046108020b03041c01624129418140000d40c111441511448250162424030a4009403250f2100c2c0c2401c0c00942c060b107002c14581140e1003690201030040c0c512900c0d1a140200f105a034002c181c0030f4065510103840a84150388034035004006030045001d109035a9810924002c410346010f070000d221178110b140041c05855a9880c9260078a20f090030958034074400303490102c56143e214400e0080c40c0c007628422724650782820003440c403a2010203100070741c11082590156080d030110320070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 517770899 1250 517769649 517769669
    0x306060e0406110733020a03020c0712390e150f010206060d06060b040b0a09080604030e120102070210120c1103040603090c0b0a020d090b07231509030d060e01 70
    0x603c03881440c04581d81c43c040508145c00516034070102e902603080b03811495000000c29000101c14081800900c4010054900d4080301e009100c10340c0c80d042401043c0001003c2c000320043c12021410740413a001c0d049191481c4a42d011003911003500c1043e5580507100a0201c25000c03014100518162024110f40001a4001c1055584280400000314011901a2050303540c1c1c420119061100c00300030005480200d42680c4e0301c0308141001030034281c05501c10030483c1c12020034000000d51118200c110320400f02c070407890490b0300080140c024450703290002d40c0001401107240340e50741c0043c0d5238035052200020400a0120114003550085450320f4400000c3d08200300a12040b4003d40c4144540b41c06401d9064144d41c44140840d170a521524001c00980e020b01e00c400001c50744070782e02d071001d084010409411309069a540c0d40c03441100c0104414100c02c1a006a03240708010000300e940c51080c00806e00303450034240030554030795000e203a0752008070b41028804210005000314441c1204e01010b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 517772149 1250 517770899 517770923
    0xa1205340209041118070203090915090a0c030e07050d0b1f060c1b05030616020f07180b01140d0209150a0f090f080a030c020a0306060e04061107 64
    0x200e414150000d42580000c0c080080c03500401503114414000c0c400c511840b46090321850900c1004410905400120710f03510104d41044411a40841595101d0405580000f40343e11076000303908e000d83c403508880d500441010104070032901590003902d4100c595480800800850307288041e00c42140b4000c0d81d810801400ba4800011407020010b5441036200105003142828901030020340d40c100e0740300c48002409450b84000b4051200c0003e4000c10314100300c5252180741c840841c0e101ea400a000100340107880c6080b00d01e403402806090340c045140c206454899444100c035500d0107811440036450f0900e041020300c00e40d40560804101c503035403031480a060058081440b0041d61190b4010f0b40c000d0302c0d4055903905c0c0c050044c040c02664400d81c558800c40ca00301b40004186070020360010742c2e5201300c040704215a40022401c4806107130146880c3c18010720b50b0000c10040c504640c80101501d181803c000390300c0142340b144070300a904c0303118140811002911a00824010f02c42c002d040860010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 517773399 1250 517772149 517772197
    0x15052b0c111f0605030105042a0e0c03060a03150f11070b0c0d020405040207060b040c03090804050402071406040804050a06090302090105131404050601080c242203050a1205 76
    0x241c42d0048040c030221001c1100341e16070b4082804c0d0380064808440c900c403220f100f2261000c0d245a41c0460011610305c070b0102a180441c02c201c2d110300503000c89101e0000002045040e183c4e50001d0000d1a04030584102c91300320088200f0050801072004007e0034504246e8030f03507514454082390f05140d0010710000346034649106c0300905600422002d000503608210001d05511a40090500140103401c0000e03104024024441601c0c80317003450800b003614001680000400401c203650903200141c5005880e0400c614000f04c191000617560402441181e04000422401c1001401950010f8500114581e6034410546805c495404000d5010b41d462006005504094500c2240640100700200762640703a50514400780c18140d4095880742c00240050015000030464541c0c20750741945e69250701c07100c4d01c001d40d880c1032211004d068034100000d0a10900e907a89125180010720790a0b03a0264035076030b49052540c91920040c1144d002d00e20701c0314940883d01801c10b80c0c0b507040c1c3e42942070305021482 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 517774649 1250 517773399 517773433
    0x150903090f1906080a051e011809050a08040321020d0302160f030e0307080706021f0603140102031009110715110f0c0c0f030715052b0c11 61
    0x425455400000300161404400b0340840b2210007030505031a000c6803418552030345030948000074450001d000c034a103214110701d491070101c1070440d80e080021038012140202540040d00d80000090300d00e01c07401c444002403000d070b00001c10071a40700700b0134410802090b1403002462140c00c0c04400161700104190303054180642c00400e40400c0300905610b210200c0c0d034580860454484003600041c0105154100500b0104000000b4000300401413041c103142480003561802410f4261201d41070840141210801076003040c40510360064499000c8840512924000d401c02c03103052451a0304401e00280c490454880c0c8068821240707141c40c42d2044075100c140560201c03541c55070541e981c4104140d00c400d900c1c00503080341c00c140e0f0206c69a0300c04a0780c1c00ca01d0240d019040510460000340c1c000c02990300005d402c1c0407180d0107407005045c6a0147c2040d03400c1e00401040e1300c640f00c08085400da2244c4007030716002c41103c03d41001c000142800701e0071150407210503040c01c1144e120031401c100c82a01c2c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 517775899 1250 517774649 517774669
    0xc090610140d060b07020a0b031302210703050318040504030906030e07210309090b09040b07050d020a08090607020c21031b070e0a090b04170d091415090309 69
    0x5050000c1d49415110516103045400e180d01c000b095140c04030309541145403154a070b200901c2456455420b50404044044ea1401442c0b070083c0b180ca149800500c6a540c900c8000451000040646103010740c0c03410660740300d038070003a10120041c0080b40c000d94035281500c5128012501603940740491400c0c1801038000b010505d00c442c0e004d104006001a0280149100d80e00300001ca210300c0c0600b0880b403502070401d004030707041300b03140f6810050b29018540b1100d102da5030041c0c0002c0e804006450300c6c901501e10703100c3d00c1c1c0182c621900000740c3c040116001a4088d0042c1184401c40c0c000b5540c01000326100d040900034030b580030049405040340d4640180100d0803081048081d24600ba041400200301503102c07600052154101038010400781071030780803495101c98011001e1108031800c1d0f844502c038600c001c2000304101c0441d0704540c0a007201d00107451701000515410044d1041c80d042a014031021200b0f40c40d028451444410700d072613141c0740310600860030200110f05155140d0104a68041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 517777149 1250 517775899 517775927
    0x4061209050a0b04050717010e0319140304081801030513030806040605030f010507141602090a0b040510050901060e010516050c1807020105130b1b190503090c090610 73
    0x450310282802143d007800005010364810002005694500414961030742c420040074100e076490881c4c2041c6c0c0c00d0001c0100c504002d1a0315030344800e404e0b1860306444480d49180b40205d50000403041200b00101140100a0800010780c0241c0490700c4000450030b49108071950030400541501d1500000d000300d070b41c03680046009002181142d200c0000c40d2400c3d000c48401c1009039100c07000d11800320f0700a00e514603a43d0010450074a032070217004980c40356101c0140000c0c0500f004600144090341c4c99481003080040090050050381804903003141102441e025442c03048400c1c0000141450140b05111007202c41a1115410700c02d41c540002c01e11088810180e60900a000960100e540e511840d4420000c000400205504040d040282100c000920801c1440384082c400301c00304000726600c035486682d0280c4001014210800014036002d0b02050030f0260700025410342002da04800594890704628040350200c0402c6410800c54160994000b60010321100041050a1283e501c0d802d0507a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 517778399 1250 517777149 517777153
    0x40b070f052103160206010806010b0d110d0c090e0106090905060a09050c180d0201050d0c02010603061e0b090c1209030f070c0e0601110c04090f080a0305071101020406120905 77
    0x100400499450070114110003241c620341c00001c000700c1031060461101349100a200600c110341c1494103095031007406020764007101d01d01190003101da090a40000c17060858680129488980c03a000c40805052900098004143c04200c041291703c10501024100c540070b903121801c0030b00d45150103004207030240003243c1040700390714042284c40503400b40c50300505e1103400071640c8801c03500f00004004208180c881c4a5642000000050b0ba8480183e0360100c3c07800c04002444000c0b907009a0041000340c0c001042c042c1061122008803d02070154644a500b0180c00e00c0754082d60000c03c200804d041b100c0c4e451152040c801400c0704911601e4a40e40220350104980c40c107080c2c030140500341d40084d9022140251891011300400d141d04208640148083c2004800b07d01c0140c50b060311680f00e001601c0c000c66440b0100400d1000d0003a41040e9180c000303028650710805810300502501044410401141078280b2203000c002c0c0c1442150200c901c00c0e958034201e003410403030200261008000980e454 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 517779649 1250 517778399 517778413
    0x18050f01110316171606020a030b030a080a020106050603100303030b01050715050a0f050708040605100b1305040608071a0f1b1c09060e090c07080301060801080c06040b070f05 77
    0x30350001c00041802d4405000905807400301c038a4003800c01c09407035202420b100028491100b00f2204490f02551382c941c818000368840e91308c15000c0703004000c815001c0c0c2d81071042d40d8012043c00040c00c020103045425900034040d2a0302c5409001715440b065650002e14800800100302280c0310340c1c440901180b051400300d150007681d40350360b1041060740014035212a035a001b445116003080c4280008040901e1003480031385803c00001d403007803c00800250405407544000b07900d003e02514200090300048003d991680302680c2c00d90301d06000d6005583c081e52800901154040c000030320441180c0305003142040740001c4520080c0c194001a03190668400244009540d1850b110b141615440c440d4004104840c2180b0005c1c42d1003640701911020301203581c00500926902062440710f8003010f85081c40542c460038000045880b40701e6025146140110000c42d0556106501da4101c5200c0310488018020800400c003162180d4400c2c50120b000400103900040e042525884c5001c0c0210155048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 517780899 1250 517779649 517779677
    0x20c03130b1312020d0f061b02031902160b0d06120f02010e060c030a1134050916080603010f060b040302091614070507091803030c18050f01 62
    0x45500c4540001e400c81c40082aa1491002080400c0b00140008806800742c619a60041150b0020981c0b0151040d00c402e81070780d0600c0010741007070801c1580724804040317103499050001c5d00d80c3c00c40e1700c3c0d0440400d0080314003e0a140700103929000031240040c05603a45181516881c0f0341e0703000d00e411030765a90320340c003000480544500000a815014001200080c0c41d0351000511419000601d20311806082c01406000310001080d121404e1290501d1514000d00c001068a4980000307824040300c0318070340240d03aa00c4000c42c1e107140411002075802c03c60b19280d008108017210201e4505080141616010f480741c1d2181704000d0f003120002d40002504080c1031f00306015a03051b908900e00500000804008500702103007080c0d400800ca02c20390760942002c11005004e10442c00c500fa41d84140407564805114083c003d6200400c0e00320400c10407005403403920b00c41d182c80c401c8180d02181c940b001c407410700d9009600008840c0c031031501109032a81032104000d00c0c460400c1641c0e040100d034081000c0c1e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 517782149 1250 517780899 517780927
    0x60603020303040909050d1d040c03141501020d08060105250606060810080307110f06040902040608010501030e150606030907080313030606120803040b060f04020d0b01080109180204020c03 83
    0x4090440540049881d0300311b410014985007120f40403000304417155281e075102900e0200303203041c100801c4a012842c01520380b802c80140290800c0e04540d60f00302c0d4144030503258900308e001c410b2102030302516141c8600c0d08041e5059001200d8407070215504218089003102c807480c0710085000d022000301d81010042d00c402040b0790080e081100410074101c2804034040c900c000c0140107040f200011842c1030502e0b90380e00d10120061071110702407440d4001e0203200d0394a00040c1d07400b030011031500310f443e20f6899070001c0c002e890071310550340400c2c07038160709613031890340443d22047c3c820b9403000810302c5403210401c8c403650303900c014101c0030300780070b5140085a294000d000a04145020040d5002500e0941c10000700711642c50740481001c00343c96440300005844002565801030300240f589038203965040100d080b8042c0480741d6980300d0310020300059015020390091078500030aa8800300a0ba032199074020855403a03507000c200019410b864000103192540080c0f034000700c84000c3d00d04003056010515 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 517783399 1250 517782149 517782157
    0x90509180607030e120412060b0103110c01050601030f090f11010e040f060302030709091208130b010821040f030b0c070b0106080a0c05130612090b0a090507080a02060a0c060603020303 81
    0x400002e1321384100303075000034041100e601d00307002da0b42e500c170300c1c0610b882c01002111034080c1d001007040d9200e0085e103209a0095001e500001802101695502c1810007038a0091078211070680c003103803800400206890a52007400749840c1e00184d01e01410146032185149a000b0109543c10401c01514000c03140e2500d000310380e507503c040c0380085481401d610406092194581181c0221451325115101103084036600e0354401c1341d64200311100c0d880d066540c80400c50010406003501e101d4800008003110300048081d00320411003107040d0184d243c0c000fa1107003880b5920030300c80b10380030b80ea0701800400c406000d020742160301440d52510301880360707650003005142640164007241c965001c03c403805060b80140128000c2c6071501078603101a8106944400440d8040c0004002ea031a44540a103580e6501600f02503070006c1e005407884c035200080c40042c0c500f10320200d40c580038001b00054240b200150303a22103264007c0c4610305082d1801c000304c400c2c0b0302d080401e5607a984c0318000000541c800784010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 517784649 1250 517783399 517783411
    0x724060b0d0609140402010203031b130f26060109150905070e120604021c060207140c0102100b060a05210114120a0f0311120d090209090a030905091806 67
    0x100e1402e00d0400f00381c040350207a201e10000c01840e0703010400180c0c1d01004807580100080d01c1c81c01c00300443d0081203018001c1c10352100c1d5013103da54001c60100c03034100d062f804aa0003c0c0010302c40116499042e01280c0f1030000a00704e80c0d0103c40140011511500403c0d0030304d841651102016170340b00000d00c203a400a50703690001c030300180c001c1500c03414030207110800740b58070100400c813600f850343c0850384c207110754080c84105a05200c2e0704004c00c0000c1d011120f040d50002d000c181845036406171070b9100c3c2e10100d080c902500c1100c0209107450850700818003500d030020a202d0500804180540b490b03805503507011043c0c160911000358051810790554040d1000034040e0300e00300306030018070401c41d01c0c4003261b01d41c43d80804843c400152000050800d079603498135109080072005050240b4102c84c10100d00180d140124080d105603459a00c0306200034021521602c1d1601d45908058076004400342c05000118600b60502c81c601b44400c00d6500301c5100e207440e5401d40c1408889c035040603800d5400e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 517785899 1250 517784649 517784651
    0x15030a170414180105060a3b01140301050d030c0c060503010f09050f160e0d15050a02040503060412180311030f010606120e010b030f030304170724060b0d 68
    0x1d011403410303900902c0a411058681d143d0750506480d1030918103105102c0c1c01d01c40c803000142c00300914450350620000d04900200b04001501004a1038914031000c1002c8180d280000d0b58007c0542c89900724810800000ae035603803940e402c020901024285100381034041c0154450682c00248112070100e0090050b99607a40c4c0b254140745101180c200c0680c00401c0c02d508103000d20a111400c60b003400e8200c881c000d0803202c10b4010000540d800240980e107241d103d4503455680b01484108010483c0c14a4400010001030b0349490900089000701e00816030158071503800200040c260564540100109041100c00b400c64503504107034244040d0012100c00d106c11403c0f60a40c2410007201410207007503c02400410f003081c1e401844400707171440701d009054803040138081040c0b0a42c401c071255900941560103101001c510907680394030a41b001c40d20703080c1c050500c42e0780d1201c0905503103046a0240c0528070440005108168010031002107080341d50340d45200046004400004005081440e00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 517787149 1250 517785899 517785907
    0x240307110c030c011b030e060f0406031112010b280e1e130b040b06040305010c02060703090804050108090f0a2603060f091b0a023315030a17 62
    0x3000e9003801200c160050103940f000c121654180e8211070440350100341420341c0b2440d002c442c2421180c3c1461400080d0b0040c40008201d404204580018801e0316042d03201442460645290741c4400c0c0716080344041c428141d94014020348054200504421040068014009a00c854901c3c1071031071a21100300450609520304a4038207004000d180000c841c0714002204442c1000458048844001020f4059950341c5000040d50b860381e20401040300007401c0e2030b403030355100d00d84640205014904034015110f120700040d14544a4000c0d202e0059000b2001400d00d4a0800150341510010b8000714050091640d100c1e0380200401803032000701c1c081c2c0e43d01e1140108000d10459400b486003904d281e0018100100209600c030508640e12296054440070241e5440320b110b102107010f1000c210051100004d8503e1049a0008007140c184211010442070b02240d0041350125a041516000c8074406240000b400b141c4c0140d07448076901400f80c1602c1014407595204201d00320480c0c6880c1345502c000c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 517788399 1250 517787149 517787177
    0x90f06050f0114220e01090c0815060303040f0b0702010903050f0d080a1404170c030a050c010c0507020306061e1c06150b0d1107020604140f06031302240307 69
    0x83c1d1031000010192925000b200c1014a08454248100f183c84603140d100e400030a0301e10000d6001c0100c140d0481707084a04140c4409415440c0c0c09500400082da0380b10001103102031030040104d0b070440f00141c4644100c0da1030314403c0b40e101d422600c03099041c003450040c0000030840c1804014800100c400180140c100c240002508010303020b001815000d25049001d0702e480302d0329010b00d40240d00540181503032920003070b42c504141304100c8415800d0001169207148540c00c01e0241044030803560007402110f481410444490285c1d081c040c2d4150720a00c003007480340c24520241c240f5070031080e240810010708207011034905001031038030030441540101301c01b091151074030441402c0e01e8090700d4142d220f442d043c103008a9005060385000c2c030036581c049a00b040b1300000c0482e015654090503450f100c40e03070342581d01c444a03400ca02c0c943c040c0c000140c8800d0356180507401c0300c0c402c40342400c240302072402e10340900101e01d420081c015084070a81c22010694940d92000e54400c2031290360300d1451030710710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 517789649 1250 517788399 517788419
    0xb0c0306011101061d0903070c151d010f030218031e06131a0721020406110606090c1b0a0f0c0b1c022208030a0917060109090f06050f01 60
    0x9004400340e26407410b8000e010b00350000b4140007214111041750007440c0c07034049826003184100d560081140600325000211851011449260264191280d0180d80e108820b419800c003c610201400503194010000c6030724000d038003038110f0a50348884160b100b400c41000c42d213403001014800b00b000a0b048010b0a462a080048503800804d00e10410200c0b1100c0d41c4007641003a8a44a5103c64001800000c1b10b40d031180f107046080d044038250026900401132a404025401400b4000008444c00c8089821a1001810364024403001e800780446584d0120001b0aa8120005440218001611400c00e92504000c80c0200902402c54150031804601c2d2030000d91915520410840c081409203004803866040c0b0750391490342d00d008c09647c031548800712805460031a103454000050100010034103040001c080e00700c148503a00c030004120b40303d6260110b02a8651000d040c43d174841001445582c031503400a4124611690040220742c000750354080c1a02c02c2154150070001d100700041200f0030036 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 517790899 1250 517789649 517789667
    0x20c130f0b06070b1b0706240b03060a0314010f0f0e06101202090a09020d0506010f230d0f150b01120c0e0906031c0201050a0c051204030804020a030b0c030601 70
    0x10450b800b500d0102c0543d1408030850b801003000140404046000d1820301e00d403401c40d0394055004008014050512106020207940c0d01c02c00507142125100c0851504d0b03061040703a0003a6401040095154076583e0b071000d0708007002407400f0b403035500d9401c0c1800d01e4410f8069412510414000460301032403d02903a494024000c107001d41820f84501d04001401500511803009501038500148507a1100602c1c0013034000f020380250450341c15111402400380204200f8180da01a440210100c0c1d50f0300c03a5501383c85070035110794201c5424605107018600d014590102c0c514420b480d0740340d4800c62034581c440d850009005180d036403903c40e0000001ca6902c41002030514200320010428030b0311420b4024030760000060f130b0071f01940800b00810080c0c1e0303081103003032841d01c0384140303e815001186000074060b00007030390307112046800c0a0002280314010b400b5113000035584428401c00e662103840c02c90300c100000c2e1082e60400c0a40c4008000301d2208280746200c2c0e80140c04043c1e480c10040001421104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 517792149 1250 517790899 517790921
    0x20702041b05040b0d0207080412020a0609050609040914030309160807030b24090a094b0f0605041a06060316030e01151502120d020703020c130f 64
    0x1120010490741070b00107040e01c0656114648007610392416800342e0300248903a402c00340500902080010b8000d60340c0c1c14180c015413080e904240569503c031826180344c02107000d0942e102e20140055601420b01c3c1e4004100340f07000e04a00d442040310b1442e00b17410b66009445941c21500048900080300020810103401040d8604c01007041d103185454819900758091301c140000c0003408200006407d08020050320254001c1a082250030300301c0403900108032240342298842000813008000345000795200b8071468003801e00300508280c080e1200e0b0946038641c0d01944640b54480c5000114407101c60350421244101400a13807810541041158500654465101401902c00700a040e0b101d49041d0ba4201c420003d000300c050340c40320000d43c0a0644845003400e551301c0c1006032a1031580013550101111081a014001c030044031a00b00d869030312918003107042d030f003003000a901c0c48240c0350700400015001344180e4012618980c000347e2200302044c5840c64868452f00c00030420100740c4a250744d82d030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 517793399 1250 517792149 517792181
    0x50d0206070e030705010c0203010207060c0818010216030e01090f0e1905070c1506050915090c1305090403110109060b0405090a0507051003060e0915180c090703020d0f02070204 78
    0xd907580003982e03034400785c0a060f042003446404181152000d4040e2009039910520601c4080d01c3e03480c0c024000202259081007420054165048449043c82203400701d451080c41125084c20544040e151b9007081003203d810044210320005000c140c80381d2a90260000d400c12401c242024500c0c0819503407617060a585961802c024404251381000440100030303440a00304241c800da519861005180ba548543d41100710b04041141d10340da400034440746210102e89690301910381581170b031014010300e08100104169104144041c0c40e221194641c001e1081c0b618500d01e04005041c03600b034941d0078404441c0e650715111180c1c41c0d4031f00760181541c0914400000d00c0e10321500d072101648e6502501c1030358042d0001311051501e00344640c1014000e40300040ca85100c074184900d9480da0780302c42c9401d0b010744086100200c0e9103030342200c0310140300040a40080540030f0b416030401c85403a5000d4010004d040d420070502c42240f60314002ca281c02c10440400603101c929600500c401c0d2a55803010581003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 517794649 1250 517793399 517793417
    0x503030108010f0f0c050d051018090209070206071209020a03060f050a14190213050301021909050f09060103020c0c100f0806060703080c030a020d02270a060503130203070f03050d020607 82
    0x26a840010b44d0110707c0da40c507010909441e6058200480c19040e0400c241800c201e06410040b22030541100303503007034400d40d034405155580301000c0341c49038000d03205000020b1008010500620540e041283c8a6000402e0715070003d50340da4800e000c5604a80f482c108540e00e48040114102c807a00c00c00401400601c3c1c074400d245003215200e0307104c20103800d0814145038042b947c440c518030440d091201900000c4e0085658604c403c0401c005624a810004001343c101c4202040906095030b412281c003c0180c6001d40d286c0310ba0b80150043e40004040310500d10448031200c2e8240e0702e200041121503016101c801101c04074000c0108100d00040013540a80420800c55000a600456440e40081d2070400300b0344079200e42c004500644128040c0030f8100d4004640501114580c503201f1841020158040c1d8000380881c080c80030002d1170b88510f1000c58400e00005a070710403501e103103004e124401416240c4941d02d0b50311070001c100251300141e035a640000070440d40c168041102a4002134241448805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 517795899 1250 517794649 517794671
    0xa0c110a0303050f18030d030207150e281a1602030c06040308091f06060807020115050103020901120501080a030f11060402010c020a0b0c061005041103040b040f0503030108010f0f 79
    0x345104d07924802150030000900590030400b0310b10402c10040004041d10300302501c0000c0107019400481080e6080c001100040c0300c08001c61241d0548090510007800300c0c0200c1c0f8030b0b0b60310f00f94042040c030400914100641c40004220b85007040c000c01c0084a81c0503070703003802c030a04c055107915005040d040d9801001900c0b49101d0004d44150310076414944640381d96074421120b42042c1d07800000e15001e500d10b08428105c0b0015410801c1550701d590358028040e5070750030b812400c0e6a400c40d101000100502c0c81031110b540f0030380043c03141c0351042c1026041c001018186400f100c03002d0b8001c00c4940c0111810710101544030790b200c081c000c220301e461841c40d941840e09584800300540003c0c10721240b120396008640b20a030f6200000c0c03030052100b0351a44280c00c0b450703032503130310440f401d5814403210740c1c001c1414500b07480350700400c00200c0300c46030955546d0b80d10303d510b0300b4000d001958076035144107084c000103000700029400390a00000124484030304600210544003c1d0100526040c1000241c0300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 517797149 1250 517795899 517795907
    0x601050a030f0f0221010203010317120411040b180114011e0f0c0b010314060f1e04051207081c0b090c09040609050702031b1506060d0e030a0c110a0303 67
    0x100c015000700940841070320500c00035040c054604d9505908601749070454001c0307181036010354101c1340191009901c8119590300761281f8820741100c6041c154411000c100401e4040b021480c0a07a005030000a092456500155401240011a03200c6640700401841010300a401001c0c0e01902828440c0071011910f03032040034a9030241060041000e20a200c80c0524844c0c188215110742000c042e40607941c503802c0040d0038908804500d07109114140124800c240d0203030203076100e200d440c2c0c60b920344000c0100703250700c0c0010050000d03561803180105000045c05130340e00405445101d00c1503a036559501321510070f0010440e40461240740c0c90854809619220b211007654880d5092a031503545201d1640020300030441038124241d200d103058200029280c00200600b040c083c103120010f142204030f03980640d581064015020400c0b07501010800508003100a0b000d07500c021100440c44240030051540f07103421520349500042e5109a03543c0600010f80d483c40503440054442e0036205086440c00781c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 517798399 1250 517797149 517797173
    0x31311030303101802090913050d082203050417060907060f021504062c1006050307030201141b06040212030304260c0a080a0327121b03030e0601050a03 67
    0x1c0d00345444c50090886050480c0d044074200036000b4801d032103e00740542021601c0114141c110340c1c600c40c0c01c501840050207031a849100301350303180544402c001c42c45007500240c2d1100b84c08405001003404045095441c11604a00120000004207001c2ca001416a8540015a40000c0c203018050340100380e089c0d404620081019000180e0382d5440e291407820000921b00b5803074188065200301500c840505004c40c4a0060080f201c04588880098001c100103e903218829141d00d41e0008070100300550041c01c1142c1d007a08448880c03402c240f229000301703010340202080c08040d500300768108030441c50b1140c601015800c07000c0007142141780550350280c00c4080d11100060182180d041840190401800c80758440904400d03103600e51620701c0e141c401c1e60004101c16002c2802c0200c03100314206100701c45080c6210007030001a25a00544482184414000d401020001520340005010380304950305619144245d400055100140d080c090a0840c1a08010310a0114003001c1000ca08003a40c08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 517799649 1250 517798399 517798409
    0x70504020f0901020118050d0f120e0c0f040e03040504050a0213080106060f140306150c030c0606040f140408030c090a08160602030c030f0903100c17070305040210032003131103030310 81
    0x200002792840c800036038148482040382511103040c8440041d10003404619140124800c0c1c0f18054410004400c22095032400342002c90968030610040100d0b2410f504000d4201244010040c5000c007169007080c4224010b401c0158140e45807802088030f95809000715000c80410b203008481c20040c0d5603040700610010744407a209500781806c100e00206400100c98928a860086941e10304034019000d44500084600760f1040e071500d451b47c1044141c500915103040c10010b880c010030f982d507950b07250907600040d20b5496460001d0100c3c0075161a10740c6070001801e440c0c0010042d04004640f86070000200e0340044085400c244030503c001c040c00400c1d95444401a4030f500e44495005010a140c00607009402e40e50b5810405a0042103030001314800e540c015106600e450360307403010010707829a0816140203400000208a500c5064802e51040b21040c83c03a21110410104c605500400e41d0400c0d901ca050004411400c0010000120944103040100340c015506602c3d140300c110001c0701d028030038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 517800899 1250 517799649 517799657
    0x14030d0905041a03010f150503010c0206070f09030b0a0608010e0c091522150b0406021f0f0903181d06060c120f18040513020f03070504020f0901020118050d 69
    0x807400b860f80011803000d5a4064000c0100c4e4601c5403405000c0e01c50030300d88640140448001258070b0506008221510b40c41d40c0080c049a00c2d074030000c50344400401129000c00001c00008000140c0d0380e002103008400603400407074024204601c032801c49915102c800701a50000300704040584a0900142c0d10011040f90712904240c1400414283c21910a55000b003503604890324224440542c003020030a00803420002d080ea4940180483d10b101c1c0e4080c000159008400d8850b0019105d001000d0503c0000320100e9542c0d246000030301035074401c1c1d40031408203812214245200700c0c10001ea4008110040310380031028500003840387c2c440c0b0701400c040d006070b0b40001c413420780c4001000920551500ca001e0f50782d613003031000e68102d5aa0407001e0403840c108030080400040f441c29004d0036020304d1600107035596001c010350070400d0240103c01c4982e098080c0e61000215580e6920207003504250b5004900e0756400d2260009013101c07050000108407005170607074075002c2100021241e15501031424 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 517802149 1250 517800899 517800911
    0x18070312030b0405041b05030312010e220c03020405100b0414040e061603060e0601050315011202040e010509220605060f060f1206010e0d030c0813080714030d090504 73
    0x400701c0151400a19580d00325040005100800c00d245001d412205100c4000902603916481051307181d200798010049140789140050009501401140d9040f503000d811500f518948040c0051161401880c1540c02ca0100f003010010343c14540101c95002840e240300100140c20020341c8001340c0541d00071075104000034a00110070fa00c5075132041c0258105401100c00924000d40320441d0b901440d18a140000d00704900002e81d00c400320803031401814161505425960b44481e0b56012400100070f076810040324004102c46100c0c0340c0b000b00060200440d61090541c1481c0c01d101000354041d0940800358240d1104030402d0303003c03420160030580d02001c040b54503140e8500141401801008055200600044254240b049030740142500c80c03104007400c24640d280c80041d10f000c03258200d640c2c0c0000003001c030380c80040d101311207500d50144608046410b0041641c00d01190b514103404c08001940290340a0040c40c800c45505015108210001c080b400c0031600000d240c080a03214980c06251951 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 517803399 1250 517802149 517802183
    0x510080a020702150301152f07031502090120060402060708070b0a0504031701061e0302040b07030c0506011413051302030a060c0e030f060106140403080c010212180703 74
    0x501220b14490300181660740141a01d9034107002913100f07100300b03032000740c111505105047c054035014160748101100d5403003da50540501c8944035508094400c1401003240210000790b54155110880ba010b040050311180384c5000902440c035040f00c0503030f401d1001c1102019012000501c10f61059054a680c1d45900f00e5292600d001e00a2100041c41c0740c0e2403004014404101d60b0056108501a55401c1701111200d16500c94190080c0140c0d0005048000003941100040c400701d03007100d9103031400510301942c403440b41e881c9800041084001900300440c15051140810545014044903c6103900010318600000c004421052903814150307100d100140c070b100e1203404d4011101703070050182c0d10031841c6440c040000b00888114000880e8012980410508000903039203400307600100200540d03400c008081e02c08075844104048010000c1001100060b802005001315402140c00561240e10450740380140702d000401034401446000c03843c0c1e0160000041e00d104580d040151060841d5402d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 517804649 1250 517803399 517803401
    0x703180f0809090112030c03030506060705011805011d030307030b120d0c260d090501090804060c0308060609010509040b040609180212010c17060112140a0b06040510080a 75
    0x852005404181610441018040694000c1071007101c100c4404880307a0300d810030391900075400304010700000c181600c4130001070b0103540119000300c03004000c14140246507a495080d100c07041044e00d20400d00351030017420801d0900844814400f0340b0020900050580c2d04a6628080180391804054035503015000913150b02c0b0701c1004400001c41540c6651b18034a81c0502115210801110043c50107481c1c52041c03400d044410000031000000b0b98605411041030002412058078140e0f020356827040740e0800aa0120001d000074001070300c07110700e144440c1c140a840410000c082c01d000e0b0a0030000d410640c0e03404811208048021203000a00400a50104001301404c0e004051000e1034405a10150340c01e0b490340d50300301c5108550300c10050141500c2e050a03100049802400704041c0403010410a01c03050100d94807107410300d001190109510040000c0d241020300700704040c0040c01c2881804202c03401154141c502c1036803d107141078584070201e507400110350580300400106801298088420b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 517805755 1106 517804649 517804691
    0x1b0d09050607030804170a0804050708011103010504090c08030406090e16080c0f070f06091e030203030a0c050c070902040f12020a03030324080607090e0f0703 70
    0x1803a541070320000c102400440d00700f07001b2864144102100b8000e4100b24100341d03036a6446080c02c2c240300d4188403680c0c0000c0826410700e0340354210310b0000d0b42201e04552050320000f485228509000d054001c490b000b0170118000041c001a0881d80552401c1c190b4040e130300d4150240d161880003080c0c0c113913061440f00100c1c1c0711100040303000c80100e0140070702c81440c0701070f140360a90700e503210b103100164421304075000c1c1d40c0c500c80381d002d0000458022120040c0180070140f820120346010359680001000007440c161210505500c50740b01ea804e075070000f00b105084900706600c079a540c0000c0c2d0014003550756002e204071000103000c030940104c120304c00e8025001440450640c0c0b01203002d4010032103a088407070424480d01007074a5280304040000c0000c840a031002c2e04145200520055482d07110300e201d48030718003d00c030503501050320a030340042081c00c00160304c0001490100803004 = true := by decide +kernel

theorem cover : BRFrame.Cov 517625899 517805755 := by
  have h0 := BRFrame.cov_init 517625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 517625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 517625899 ≤ n) (h2 : n < 517805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
