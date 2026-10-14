-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2295
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:01.697219+00:00
-- url     : https://prove2.me/submissions/e7c6adf5-ee73-461c-97b0-09badc18b7e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412589928 ≤ n < 412769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412591178 1250 412589928 412589951
    0x30405010311210403090b0d020403170c060411040e0304090c0306210b04020f270901062102010203040f06020106090b090118050c04050307081f050c180607170d 71
    0x3d0082120351001000c281c414860703019249083e06400038030908044000981b614000d4125030841000d08a1056010504006200000c0b280e40c5040300703464000c525040f055080342c4d403903a1006001401d0b01101040c00007642c0c5440c1d201500e031158803003c1d603489946510100c0c0152001511510020742031550216440720042400aa4034405c01a002842651552070103000c0100070002c6e46e1082c910380e0101090340301c10f44030b60428000740d21441e640542038040d25007000c1c030184c410016a85044000d0000d0381030f1111808584280b00344140d034580c041e1004030f1961040e904000d0748040c3c0c0040024119805410040039510f0448040c01142180000d129101b242441560551704005654010840456200c1900601090f04544c540368941010070301c0c0a81541c048680e41d8400800700c58021000701c0034961b01c05105030280444e0401004403007403400f5a4055580f40700d2084102200c568070701e403c44072544d601c0b040c422021b074840000041d041d0022031203000d61500303004519a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412592428 1250 412591178 412591211
    0x3020a0207060f05120c0c15130b0c0d0e060907120317040f0605010b0903010e01090b01150210110a020c0114160606210c06031104180f0501080304050103 68
    0x4505803a4000c150329482c129007241d14541c250102c8040c000c042280003168140c006040c1d110700711a00000341d0329450500311500c1c04840d12400c0001002180a00410411281d40b034206984c202e03903096159144c40311155510b12402440700849860240007501513280418010300c1086854182c440040d81c0b20340c0c0c00ba1400064034024000345010310991131800b07203100c015130420300940003503803200c1c040e6403400c00300c3d0400e8202690075000800c8101640ca000d001d00116100510020321038007a440c0d96203130203a841809031007040300b01030401d8140e1324400c00446503180e0b04054240010306005200000990040070f1407001030045102d222683d500555461b94041201c4128528185036039034150140700c1006400c8582980350f1500191007052100816aa007402080c80c0b07e0035020f40c5003080c3c01c01e086a0206003418142442c1481c126104001d450490305e062800580d01b074030141a05d0010080e102540c1001481c000012032104400405002034900a072020031400c1e0b1250020107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412593678 1250 412592428 412592437
    0x30b09130c08150a05091f0b0406060c0f08070515010609031e0b0f0c0c0106081509061005040506060c010903090312090b03150a230415050102030d1a1302040f060302 73
    0x20f4421100c0810500380c5664040c0340e02034044000c1d10095510181e9a499207200303440307440e4426880f04003034400c40ca0b01c1e00c10f90b4000e00c01400d00e412528825603507004422110003016109800214401040c0070041c001e4400c2c5a00c0840e801c042d42d0b0b1141c602402c000100e0006035081c54500000103e4200c0110110030b80039000342c00002c040d0340e41e1807140c003081e100618841c20100248000050f40101f401028080d240c02c03400740204680d00c41184810b04402400000540d00010034003214003404488441650380550300810340d0380c2c500c0041801c0d446540c5036030f4508d61909888005041e48603111400744c900c2009807040c014118441101c4040943c0640a2030300001c0010441c51204c40e451b076080340d94040d002074426070b91000c4440b10110b0600c01500031f505171000b032071240c0c5000d100d140481d454503100c1208540c10140001d42e82d0240030017102c280c1d59520065001401c0b6032481846080d40240070b285501200c070284400b079007144c45444c0c1d0b000f4050740b0200f4010f002c0d000782c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412594928 1250 412593678 412593703
    0xa020f060d0b150a02010f0207081605030c1e1c080a1505060d0504110618010e0d06140115023903010c02101d0613030908030d091b1a0703030b09130c08 67
    0x1142400c0c084200c41038202c2c001300c4100c40070700c070410050ec0c0c0c0348014403100c0c506850325201c10103041101d6071030710f0418100309003221850015981404c00541c00215140d000b00d41c1a038005900810600141c0700c60000d50000395020030046042030300c101d01e0341c0002e48194131408840281140384014007881c1e000c2d6442d0000c08140010900c0801e52107aa00c034505800001d01040b1110100d071603100880d591054083d0300803070400c0c014085542d216007810100b8245100500e508003401c4414045101400d00400c05004841030070144060050100701c5c070f220000b4020003030394000c2c10300a9900d5600768080141030341005540c0d141c1c4101854141d0b1038520000140189540e840c0c250942506640c50480600c8006100030510410400c0581065210420001030002d41403c102c005603400b514203820030307010524240410904d152040602541300e003201902c52140303107815009007450f1009141c1114030f480401c00d003200340701c0040d2480d50042844054050719001095140ca4050649 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412596178 1250 412594928 412594943
    0x1503061017012724060f0801170a060c02030a0e0f1005130305390a0b09280510080106020309010e01110a0506180a020f060d0b150a02010f0207 63
    0x40004440f43c040d40d10542400f0402e03824100c8160301d1040403614003044081c0755038403241080482c032408070301410103402941080100a051054010200501402140c40e0100c030b1503540100207800300020b50102e80c0c016414003910a40b60402540c07074000064110001c1c1850051101d07509000111020070794000c0c1c58005000342a040650b4523900c41850b140f002c0291100010100d0010700810b0545083c0740e8074103081d002101100c004e95080c030020013103048550801c00d85a0303a514000002210340c160010303170f01d4072400c9000460180e40034200c54000103030000840490740070140d503036080e46c0040b2004201c03440c007501e0031540c80e0400d00403440540d104001c3d40c841e0358024101e1100788641450b01644443c80041034605045000700704403203543c080350030707c148128400b03000e80d000300ea002e008261040080c0c0004103807500620382c0074055000001c4020b0300180e590440d890044006d0485249a65500b002440582c84035031014019403a042c0c0d1115480c82c2c074021983d0081d000b108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412597428 1250 412596178 412596181
    0xc080604140c070c080d020a060b0402210702160e100b03041a04080d060b0903010518070608180d02070801050603061512010b1513050316231503061017 67
    0x103440b4992000c0e5054865506035440080c044804125010f0402e0096010345400c01d040d151036401d441d070074441d0500c158014030102050015151441110002d03403001d14410b9290700341d0590030001d80b010310040840155101069850500315058050300300545100c003080e0b503e50340210302e03000c04d480c001d12080c0c00b212f80659901c0d00e440c0440d00070f401207082c6c030301d007048001c01c040032100c15601c143d415810218148104d40360078464039900c4030020001c002450846003980781c560300303640107903c1484a484d020039041e54560b402c8003550740600c400c866000703544500195480026128104003582088000f0b0b515007000700d92980580c62284000805001110030450ba4041040c9403218565807480c4005a568449180c206165481408181d841c061117540c03401035401d0b078004030b02a0384581200306070118003200c150b00701c0341200110b86403da2501400d0001d80281034039243e00421060b51100701074466001507010350401c45e100c51000544150079600101d1440355041905101c50 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412598678 1250 412597428 412597441
    0x32c030f030705040e04030906120e1903020a020414090f010204060c030f0e03100501090e0a0206091221041d090a150f020d020d110f180a030203010207060c08060414 73
    0x1001c0e640190b4603080441c00c10751101d010244403002100d05900080c21181d0801c480d80d00480503e030340001e034010030721510680a8115035110904020104a14500c01581c4203141c4284000e4080b10350081c0240506a0350300403220704d070b80080d603011080d8010040385d80c41440c0c05100301c070102c8489440392750344a80b460300d05980b242140c4501005003d1909030a000395035040c000d00d0302c00100c25000041c60350410040b0411142c10301d9003c00306512900003240540e40b0081a181460011990303c4014880011102e041c0200c9154500d8040810004140703030301c80344006003040d54500740c0d140034280394441581041d22001c0d9241d1840d80c200c5544c0902088480c041d51007200800c01000c034441154540308003c03039101c20120300b01c582e4007040c81601c44105010380c0a404022510341411300500040c2c207a45031044000900f05010901034400300354840c039034031100864008000b1522447d1504201e4041c00b1140c0f00040081c003124009200d03490705220b5400545e440c0c4c21004841d55451 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412599928 1250 412598678 412598707
    0x506030709030b180d090605031b07080408010506030d09140111071703040302030c0f011205040f02100507060c050a02030a110a050a15060e0105060703050d0e030a032c03 75
    0x28140c8400c00c00c07558004004101804030031402000700c00044420342d070042c81101c0c1003061800401003000f507007140030000181d0102c152500400034000107075401490b00d480b40202e01c5142001005410b02042c00501d0720010350100d03225000a07000c1d24815000c00f2411110002240502c40040301136026102240d441480208071400c4400d04880c41d10f0f448441d120309640164501c00029480041c01f4801c40c1414002c403541003005031307080c0340c248041100280503408001c5014030082d0b55200082c0500c01a0043c0041d01c0f5009003c2e0f00c04031031140d000070801d601a00007a590f550501d5120340d00c1302d110b17008071003080304507134083c0d810890741c141d04461140011000380070a201d87c0f44000040b501c1444840300c1c0e58820a1444c0c1070041c40100d142c15606241d0ac804a52000c480c01005540c82c0c08040b19404c60b410f1411a40d540040849600208020141d801041c4400305220030b8558043e40720109184101801000105802602e8050614414034a2810782c02c140250700d175801e10b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412601178 1250 412599928 412599931
    0x906090a020c0c030106151e2a0f11040c0206221403030109020c0609030f0f0a05120408030106090b1303111216050111010902090f100911030703111201050603 70
    0x1081d060724409144a40004c1c21b4880c90342000c00705100b030b0401c24902903085050a4603503000040c99041c6440d803403a020313240e580c11210344c03842d40f848150f003401c07480700c044084662241c7c01214000021800d040c40312200120f8210a405107250007100104d5600006010b4850562242c945886042e408158185041c2215084584800d10048010010f1080c4086e40c0a01262100140c46060480b00c281c50480b01a00501302500104644c0214147c03c008803040c0450620703006550310620801290a0b120720b44102c0c0010350b11030705000c02c0112800096040f40c40342e0b92906c3d002c60300d8000c0328406200d0400c80c09141c583c1107904000140030500121488032000f0802c030140c06a0040c0141001e2500d14580b410700107050042c4000d42e0004004d2140107040d50007080340c04d01c80d90204540d448050102600800820001420030500c0e521680c05030144010a101e074552110854080381c10540c2c814012070708144903804ca1100300816544141d4450b6000d040c564a0303d0188107441d0710 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412602428 1250 412601178 412601197
    0x80f060612190803160804050307200306041113020a05030f0a060b0703050712050c061f08010f050105130b0a0b0c010f02031602070509011d0a06120503070b060906090a02 75
    0x14480e0b46030704001a81001d0342801d4001d0031415980e1801c000710761070103011043c0c0382081c403034507400703020104000006642d0001c0d44440380180d004074a018100c00305038200700c440e5062048408010070090141107814036510181d0301d4155400c1550103641c03c2c1d01550301c0038000200c003400001c403056030000da00e9403c103840080c0041c1e05500d0f000d1032145a07015010940101c0c100003007800030400503082a0350b01c502d1501d410382c20506c0c011242e03915810080c1c072203543c844d03010710080d00c07032501614250000c0400800070000b1800ca0148500070b00f10074070455102e5010101200304500c1c0b0740c014289034031401001c0c41d0347c6c00e0803d4412601034108142e0f11100d99611030002c81001d003d403000310300910b1500c81c0f0341443c22480308008c2c50001c254020f1401060070b4401000380c54070b024441d44410780250f518060b10395555200c40010619907201c0403010790825600c0701440000700050150a02810050b04c0c01d40d1807005100f0054003e0311466040158240051a5409141d001d48012070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412603678 1250 412602428 412602433
    0x628020d0902042a090e040303090c0e010603061d06010905220513060b04090503030105040e030f04060302090306090c1c0f14010f0c110c060f07080301080601050406080f060612 78
    0x2200d070300440c044601d4019040c00781401901c0020641c03100d80c50031824000689884030b0070318280b06d002c41018001800040a05440d20155001c02030702d100740078050502089504025a51801e006014000e68464112061140c54021004000981c031035842060103071503441d1424680300900c0045c80d04200c51100c0030350590014124048075000d842e0088080203410a0040e2850030440d0403202c1100380035200d20319040040b00060780100503203044420803500011a10b1003500454110b2240c04403050b1050000140400c906130554054681000c041c1c00315810359481004840d074a02c0e66005a0740d0004c03400c00302c000d0240c020b150070524144203645051040f40540e980b082c40440d00c505800e12a515004150b4440c0c0c0d440c42520704100003880c064800741000d072170300c03030302c075004203d090740a031030000303005a040c07101d4100700e0320308a901840b481d0f5207680d1107522a0f04c601080c00f03000c1c0300d135040000005000740c00144150280900001402094031a2801c222444e40301c641230305d1990 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412604928 1250 412603678 412603691
    0x60103030807230703080a1415030c0603090708070b0310032612010326070618020d0b091c020c13150e151906080702010209040e030c0628020d 63
    0x30f01000da080f0001450055940b00c41952401402d440320050103000c0061402d50007555400701d104e003158126511001180b816403030b920219040c03c2c2c3c03400000c0c1e001040001440780442002030404100d4000d0011b481420341c440d440404144401c2d900280e641c4203c01040c408620029010f100e00d10007910380300e55041c201801416180c10a420044d20224140c00400c180300184010200007a00c20200384043d0704440e0b600300c032034090030b90050320250f940c84615500f10380300c000c10802e8607001080d0181e5443c151a0180c01480100d490b8000350007080e2441d42d1001450303d05480c8030215401a081031a01c91041c004054020065605c440b9103d0070707074441510f00844140301a1001c2032810700103140900b02400708110984c81c41d4041c9004046041c208a010a00401518600d1814802030b84504030120702901580c4101d0383e0091a0072a104542d100000090403040d00b40000d44480381d5074401d1102c14102d000303281d10895030700080002184c200340d5009108400394100d001030ad5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412606178 1250 412604928 412604957
    0x6020a0c0c030311010c081608130209090d020d0e06030f071202040b04090b0a080c010c0c08061801050a1a0f12030c07030c0911040b0c0a12081603050405060103030807 74
    0xd0001c66009501041e003c0c0720201d810740e001c0c0500103040110f42440f213201c0c00c1269104011481000c03401007000341100c0492000d02401707900488080e002031981c1c400e0304103008401d440b00020040d100c094400c3d400f10200d901c4c080e1150340c2e500a40284201c0c15503503814440712485000070f10041c1000005071040f42e800100d840548050451801e84039129800c0007804002c0f903508007401c0d407003036001c00d4042025100000303070080341c641c080c60240016412481c211400c90700c20340000301d81d400740c0810000980352144070088003c00c0c0c20000c0c000d58890820040840d410410030b96003c4041c98860362485c10120320117501d12030050501203d03406d0082c4c2c02c6044d90803d950541468101c1e103003c009001c0c00141c4c001c0540781050b8100011800080c0c3c1d101d5500c1030b0302c5566001c542c04500340c050746105010000f829a040012404806400080107103200407c80c2c1c8a5440b0b0503180c1200d2509200b40314983c407465020008090690860310140d603000c00080242080105000d184600c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412607428 1250 412606178 412606193
    0x15060c0a030207081204050a06030b03240a050109020c060402042301090e0606090c0313020a030204180b1005090a180f0f031e05190201020d0216020405010e09030706020a0c 76
    0x11128020342c050f014450030300f1102030910704050b199082090050006001c00da480c103481008560590900180c18412100444e08051a101402682011144607000d4480742c100180b03104070028041042a03a0725030807e01c0482c013904811240f02d910907000580141884d0340440d2015000c034910030540c2100d4004400e1600d03098008140750780d103504540c80001c008105854200c4001c0f920704046140010810005000c020010b0000303c1e100e0013554207544a0f40c55800285401620600c42e5107820491440700103507541c01114549041d43c002882c8a020075140c00c150362008141880a859080343c92018060034140003100d60040600000002d556000d41e00f0a98400c0740c1c1c2801c0003c29042c00b9105071000708400741d00b12003181a071540d05a1250403115071050801e42d00c4159180d1a034102d00a000c0d542d4004c4656100055250405101d0108110403d20072241441140c0c3c84039002a10103405032011b86240d40240b000030000f5142d40c0180c1310750445442d008108065035244c030322 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412608678 1250 412607428 412607443
    0x60a1214030d060801060905090c010518210318120703060b0f040501170d0e18040f0b0a0b0a08010b0f0d060902031507030e06190f0204080d18060f0815060c 69
    0x18800c0e9503d06e002c001c032480b940140c1d60b0010009001d001c042c100880080c016205000c0140320003582e410760311100750784001217554240c0845000000011404410503902c0d0300070504030f641c1c01d0010382014418a0115000c424100005001d803400b2850342d03480c04041e1078240b07002030780074014104910b425115440b48500800318220031042e9030700c0944d409414080088520810042e00328510511903e601800740c0d000041e1601190840e5030307900348141444070f803030300060040078480c1c01d00644041d1500401006401100d100350000d5503000a542260120b0318520703040f62485070110418545409041103940c05040003240211455001a082c019403001032641c1803040bc00f440341082c0d241c030609111420303544c001e00c09410443d0580c554000d4940d04ca01d14a622050000f8400700181c05490013022808101c40b00080070700340141c4202c0300d00c2c0d08001c8116a000300042c4052160311002c2844203980c44041007a140c0c11482e01c8640f0009400c00e420000030045580081c03402c0042c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412609928 1250 412608678 412608689
    0x1c150f110c06040c06080103050309010503130506040506070207061817070b0d020a1e09031205070501060308090102012d02311a0c1506030703020306040614060a1214030d06 76
    0x7041e0502d00f500e044403000c0f042d03402050412455600510015400200700c07202c04030242080c0343c8031356440c100b940321000305000c010910301500d4244020400c00080356409050260240c0380a46c0d224030081b07642c64010001c00ca030185601c0707004c10141307240c00080c4001105540a962401e5200c100484082c0d22240c0104942507000a80c541e0242c2d00080240600c400c6030041c044505c4c00d42001001051a400007500c2e8460310030107c0e40250107202112062a4050001c0c031010759207003088586500801c1c0300341e0265013000e80444050000701a00440440b0a101c0c90b4040d90001c06840025001000c0c0a0356050800d20219048440717226440000461500130f088000d0400c40c0310100c02d40d403401d03101c440f400300340001000c0d0030000c140f10220480891288055583e2400043c0c5410750ad68000b94150040030140300030311020343c00070040c9030503a11702103440b6254903003440b60a00003882504c0038404100e91510001e0b0000381c0d622641038043c0f04803401c041228410700d00311025603200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412611178 1250 412609928 412609933
    0x4030215011202090a0c1b08071a040f030809030d060b0a1701080d0e030c040507020a03030c0c030e13060e10030209010503010c05040e070311120103021c150f110c 72
    0x201035080103090618050110100d40700400152030b4041035645034003a02d60005640c81d0b04c3c109030181e02c250000d21220b08107245e041103900c00d074105083d0507400f112056400e075410101960740c42d50140c907010701540d030118042e040300000c1d4404890345200135003100414041044640c8402825002e4500a40541550946d890010120152a0381e03000c11004600e80b02031001000042408520307440b4005180c00d09042550320f2400280c24041803141960b401031074501482142070740001c02c100300394403d480c20480f0311981c01054507e00440080100021501a513a062504200240d040c11550b40340c00440c1c642c0d114249019000740c21134121069844105040081d894402c029900402c800e9000300003010005034014128844c1f401039004110350f03600807900091090748103031028210094551340301c4403090200c45402c40c003813006901c1051600d110010204c108492442d849600048400c4030002d9032045101600c00c2e0100307080241da643c080030000805c45030061411008001c00f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412612428 1250 412611178 412611193
    0x5010306050711160b09040603080d0203180307080a120f05040510061d16050c0111070605161e0c0c0801060303020607020303090c01030207020f042a030207050a0609050f06040302 79
    0x1002020f41120200c0141e00c2031000c00207804481c008801901d202c00d541c150740b007034040d001c54040e0407158001400120300092904800709607070b0156000b40300c0b4034429007806a000086941c3d0f4020403d001e02146030410090906500900703941e0030714802280081070300011043c03c5001c5440c101c50599468018075080d808004840c410040a0805984001c0c10b200f00c5141038199848020403400c1024080b0010340c55481c01201a50305141d4400001d0180000d100c4640243d0b0700180c104880e101d0614002c1504420b012200ea204030103103564001d40b480782d21520072070005070000c0b10b40500040725426008110703509000c0c80034203505000454864a107140091500c0e5005240d0710454000784103020b600f080100f221500d503942403070050780700c00d407500000c1d5003007200601080d031003407800c040c6070440090711403e800c2516603101105c1c241004c07480c0035010380c404d0280c0200250403c0c0c002000240d440c1d031020500b44d000b03008980304042c0c0100118070304181030b82d081e400b5a12801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412613678 1250 412612428 412612441
    0x3090501182402102a0309081c150e041b0f061e030c0206130510020705010f06080c01171503060f091c051911030f090a0b0711060a02100501030605 65
    0x410302c81955010704041100d81070800f00b01e040b01402d2171903170012200b1713001d030781c4081031080e08034280181d04030001554031850701010340a04150307016001c0140d81007040400c12000011103520403038118129000350340e6103990701c0c10140e4501c10501c442c000214400400c0303404c00300c0741107006840070343c8070b0002c5025040003155130b03000000c64450030075080c44ca884503d43c0c1d0215240e900b01010525000c654155440c0c12402e0002d4003c4440c5d1091000c0344140621805401108040da0401d01c100582d907280c0042c16100d010344140035000c940b80e05042450314040704031107079100c1c400a40d1080701c440040000f03030a054081e28100c403240c5081080c800307400000d00502036a8407004001e11101c50440c0c3d0080c4c200e002d40510031200707060b1000039002b030500407000c0305031441005054a03510b2030000f0300e0a000703811050314a400707a1440c500c0459802c08041c100c1c3d0000d81c0020020004540d114200903641d4004000320301180280c850307590b41c0c0c800b03500507180a11300ca50004142c40c681107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412614928 1250 412613678 412613683
    0x8070f091a030a080a090e07080f070206070806150909010308071a0103030c020618030d05040819050705040e070905040f0201120b0d03031109060d050109050702070303090501182402 80
    0x9540224944803074480001c4659000a601646540c0c045000707600ea251048041d6010800da5101703145061450f0200440c095100321403038030405440c01d42807100e4440c1c038022070b503554003200d031000842c06001c0400c070186844240c502124440c0c00c1200e1400001c0c1020034070b900e03820b0703000f00c0f416000400d00000b004013401c000a803017028030403103000c01d6143d924000d04103041c2000c040d0107014002601406040003a4015591074030203021243e01284108001303240380d1041c07142d00b400c2d0103200d909070200004000c2055036a50400000e0040714240030402c40284145124080d04d40b042d442e000800d0100c500a03e803003079010340d0700741806410900014181611403022000c24030714000c0a0071155036201d16a00d107854040c500090b000003100170309800c0d4402c101269501c68000300384904aa070441d08030505844544906001c20348034008240c0c0c1d182c009000c0200814840c0700f0501c20703035200e0b01d209140600e45003120b0095665074081c0910b40200c03500c69100840d81d05816501d2107404 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412616178 1250 412614928 412614941
    0xc03070302150c07060515061216110304090f0e12190f2f0a0807020a140915060d110706140606040315020705240105150306090403020708070f09 64
    0x1c0b08280c6428940502c5104a601c181e1000130841590750000c03c58840c105010301c06080300140140341d4485c000e44400341d1078041114a440c031186554140310030544601c08001410a9142c000d50074542440220401703000308500c0010503590b01c0040c0c483d9a4030400c124041042c110695a643d0b1350400e0038020020108c2e4403030b2040c000341828540d0800e1380b1802d0900c2000050f44070719060b013400c0c2c0b118401403600540240192041006000600c0900c10082907000d00c2152201016940c0d03000790110391034003041080e40200c443d0002854400c9450000f064401d0060286d0300e01b84681100808070382d081040003c1200012075401c04010a600c200707001c03118011205000c6140c10f030000f6000344207900005210842c42007210801110a0f0180d581181d400301c00c0e1000caa01ca0340c1d2040c460140140c080c1080505403000040c03508145050391803d038070380e01d4000e2030350352030f00180300e589400500110114407039040300003083c1100f4090000030b8125040700d50309841c43d042c00c01058942 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412617428 1250 412616178 412616203
    0x1a09070c06110f0f0c07030501050114030601120305030402061b0d051812071401021603060e10020304020319020d0203010903030b040e192301020403051c03020702030c1c080c03070302 81
    0x70401c81e4503c00544042552400324240005030354600349501c20324240341e40c642c001010381d82031800209058020740c1a500300c401c1c0540031540c80340c1e81d5402c1c08030241030010000d004544204081009800c1c0f00000713128902d541c200031059102c100c0e26440c40d082d0414507240016601051907905002005124a40e00c1d10848002620b2a803d407419511421a4451004800240c0c182201c85034020b001f11551030004c2e07404100d24540c4c82c108030018050a188a41b00c0b4014049500302c408202d20949001301d0700a401005000240c4548140b900700b01601642d01c008400e80500040c0d03000d00034444103030702c25a400700340d0a605006100aa410346042500c0c590010b400313040c010005505c280300e150703410440c5020004545100c00e03042c0c204c1d04121071455400000c01000b071010000700381c8e81d4490700215030441e007416035908400328029100000d5042d04080d019103070b1460504c18505801409504c1c01400c0440d50342c03145680c0e0301c02c841c160750a400104421040c590140b1a5071407112 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412618678 1250 412617428 412617461
    0x5092b140609120c190606060e0a210305042c010b09010c0b070e0a0f06080c0301050907120b0406080106080c1f030c02030403330e0307061a09070c06 66
    0xb0040715081d01c801d5040d061240da40000f0036003400c18001007024210100c40851503031039060242c2032100183c4114000c100200c0e1902c0201c030040e040000000007107500c4950040100814110080350b103600c41c407415404c11105200100c0c54408501c10a195510641c001c41011880e0754841c16090384143d1142c03840d40c8040c09620b031244d030000c0403041c0081d03011017404050340c3c8841e0195441c01c0b0510715950007100b0b041e400304880010b041000306a400540f56403a06541d885078810082c8801d01400750440c0f042008200181d01030400b011034440d44102c08510b81c1282da010508a40306544810b110303a44804007000000d80c00e210000342c0780f0302600c1407403102c403a44028014000c0d10350301304020180c0e50840098418424400c5e0f501540e40304441c00c0158081d10300000f0032111a04072001520803041c82190400350034032540300b01d00c3c4408080c60130000b09440740300050400801c807050305a11403500365110703580e016a0030301c45c6143d603c9550501d40f45060800c115400102e0215004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412619928 1250 412618678 412618681
    0x20a0b0c12181c0b0c0d0506040603200a0504020331030e21031c0c0c030f0c0609020603040309060f030203060a15021c210b060a05092b1406 62
    0x1000035140b400906903200c140000180030021085490400040c08504070329081c0001e46491500038003845d08152801c0c4195120001040215111444001c1c0070306041d1115600740b0700900040c0ca0364041c010f0442410350755070004241603a2003210050111040c0c802c000305551140341d09a0490140c00b000070710000c0311660041e10520301403402500c03924405011126454410030800c910343d41c2c0c0002d032500c0d000361f1100e54250f0310381279003d4059a801c10f5107140000b4441c80c0348082c080d8155443c030502d110001016210307140399803010759105895402c041c02613150364008501580c4695a00c6528a141c140010152090200403070101801001848002e9440d4038808003512030102c10030800021101003a07181025011680501000c01070f401503a894203c50b1000c040844003016a04084402408000311410380300403a900c084240f24000d190f030303c0742010300079900025200c600c00300c9171304401c06540f103140c00c0c45900b00344840003c10200148103480d003912004020040196 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412621178 1250 412619928 412619947
    0x23309100603051c0e1c050307060905060f151003020306041811010801060908060a023103020f0d050712020301061806060314040201021911101715060d090f020a0b0c12 74
    0x508500600d94046c04034158400301c00c1c0702081c01110b50b0b080c5d12185c1000701d04240c0c0707015074644204584000c00b03010b0340f100060060302120391240c25403e0080180b0b0b070200c807000068009400281c4045d801030364411291880704030310040406194010164000804400e000040109605800c41410480108000c101c0300500281503600413807016400340c1c580c0c002d905070300c003d009209404120350041075409080a0b0100744480300341c0b0300945180142c1040c48061041e1901e00d400014410f0f482000e080150500e5110700003140e610080010400541d2540540c011941800b4040e500c00da5640041000c2d50b01440b4100c3c0b41d50b088000c0700502e180980010b9225a5000e84c41221038070070082c8501000f0240001a2500000601904013144040c20040c840c50218946407000c44d0a0702c0840c8101001885a08100100a00061424104042d4180500044001141c440f0100440040140d849500d007801520f540c920f8aa22401816025480e01d15684031440b50040c5c1003040568 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412622428 1250 412621178 412621189
    0x801060506270d2a230909030403020301050115030f090c1202040f021c050606040305070303050c0307051009150b060f130909060507023309100603051c0e 68
    0x1080e8141450540c4520040001c0340710340e1a1048014200d4518401d10310725844aa0000c205940c9452825010139881d0f04034241085841c14145a90542101c860400f91500800d01a4410480c4003500d00b030543da54042400d40700207030070520ba40e003444202030a60544c548158890f011040e072042c0588007031912403142c0880703240201e000200745a07004c0d00a54850f89c03c809003803070396014115980c0052a0300f007121074000c2c140c81500b450074100401c036a85002429503040c6ca80000c094506e0034036607642500d555100c0b8076a000d0718041170144c0404607100742f2041c034500e15100700101d902e6051307280200020440e1088215950301e00005040c00703880c1c0038141d983d8804c6d180041e81c1d4680e40c25a0404100ca07040d4000403140b42803c40c184104440c035044140510b07840d8084581e980346c0f660300000506030400480748400c0820201d500d8089852a5241d0400d0a2005840c40410014495010307200e003900241d0b2240c1c461030081e07840c10012a0f00c6c0b00d801c04140f40a0222100760b80000c0c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412623678 1250 412622428 412622467
    0xe1009060503150d050f07050a0f05030c0603250207050a060f081b070501020309030d0b090f0c0703050c160e0106050c060a0b0109151d01110c091f09060801060506 72
    0x107000b0050884050b8244d02c0d4074000c0c0001c290002c0403289801407145c41160b0301c1b1514002e0794022090400c1c0001c8040c03c200451050314001405030030050038090600607503402c0240305070303183d0344424902d50f642e054848486c180c00b0125406098050b080c0814000400c1140e4031060400001450095059a0224100b038015242181003c17418244d5205101240610340d006016035200000340300031050b00200801c00003100842c1408007000e43e008001d9108411a0b14803241d1454000159800c0e4148004181030391203800c2c91401d001801d448586000107070103480e0307200c001c550014040a5182d107090f5004085500d40300349042c8a0307111b02621000064103074a516030700e58a08580907030182c1c4031940902920809180da404404400900e00040c094407003880000c0d1440524003548a564108004001700005080c170424001c140100c940000700804000141135581206147c0e1580d1044010300e03580c0030110311035042059903401c55415a01003445942d0030400c004140c4820020b14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412624928 1250 412623678 412623691
    0x206011d060d05160e01080f0a0201050711060d06030501050f09010c0e06130b0a02061e0f06061612360e040309080604080d0e2e06150e1009060503 65
    0x140c11050b4a840c0180ca4541050b0070f00451390200c0700d01151521050180d03a0486804400301c82e003449600c0c0c1181e441e0f220100010380010400c001030700200e140d0748111040c008000c1c2c130152900c012141244210384568004a8503079459a0520140390309007131000d908a1481c00003045810690000074000701484112180078120115082c04074010114a41000b8440a0213055079018500c01c001d403a007070b048071150280241c00c0010100341d0300b2601c00ba4410400c12043d10306a44610040017020b400691840c10920308550010700061200050b052a1509036111101c4605807403452070a4007c82085041201000c0e1401c040505001c548030000c41d960b04051305001d4440381002c4814280340c0e080403009100c0c4500b0f000420083c0002400004060302d001c00c030f035504010034140c40311055501c004c04500321054007002c8015810004c25004c1c0f0051b0005482541c2c2ca084914641c1c007030130030b0008107038020b03203070b488606200305000c04080513440c1102810703041c554003529600015004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412626178 1250 412624928 412624939
    0x506210c0901090b0114030108060c07020f0a061d09090a080309070f0303080406060819060b1c08040906060c03020a080706270c0b070f0204090302010b060c0d0206011d06 75
    0x42990400090003a0828444003a280000d03560310389011a014101c1c000f6100e0000f520099549141146503050700d041e100e440001c0c01040e10380114400803030300b02c02c005aa200041860842076540d807070040d10014800c03a150025681c2c0e80304e80304900500311600090041c0f4212040254402000c5045010b03a170f48410032503180d41350994102d10708505508002d03a1140d00f000c000c0103154001180a202d24480c072014130010752151213894a40010000003d44103c1c11010304e0006905900881c400b007001601c8600000c0c010074403c1d00781101c558043c0c40700800020240710700100d9000302005840e6901b008270ba807940c07994000707560f4518110050304146020030b00e8001c02850342c00040315202e18503018815a95051030819946805080841d001c80c004900050405450400e482c0c400703802020543d617841c142c0d02030001408851008500315540d078001d1440c9a99468050080d130420300c0010102c00c4518000030780b9004040e0401ca911202d08040d00100c0c8030703481c0c0d00561081d8240c64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412627428 1250 412626178 412626229
    0xb0f06070c0b04090207050c010f020a020d240603020f04020708040b0705190b10060305270102040e100e011406071e1212050609070512090c0418060b040506 69
    0x60400000140782c11030880c2400008001aa605a40d00506a180d0143c030540d070002940c2401550460240e81815000d6002408030002520f8014000284503000315200c4010400080e5840c40c18600030140400b05640c40c02d0500c19810011025521403c1c2603d04500e80296a11040c07014000c3c2e200340c071400c02001403501c080200c00c0c400519200c2001042c3c0051035054644107130211002c44840344d0525401400040c5180b00e0f004503400782141c0503d240000c5100d400b144482e03000300c100036034150740821000629680784003009104000c0c0c160014100b03424001c0305182c003c0d060340704400726200440d102030f5507a11441158416075100c50302c400760090300d410001060b440c0400141c02000003e0b02698015080b81c0400c8400281c1e840400003507981c1010081030b10703010340f0751400284c02031094410b2651032200785500041075a084a1803050b52200040680d10401c45814222204c0b280d400100300041c0501c1042210469090180e4544500400c2425502c00c140040c01c103a030342c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412628678 1250 412627428 412627433
    0x605040b0a02071503050f090d050313110a120b0c0f09280f09110c0a02103e0d021b010306050a030605160c0b010522020d0c080a0b0f0607 61
    0x1025000f40810040d0351000c5004d9540a0f00074282100e17080d000006000005140b000013042a50f40e848070754807070f64110344410407213140054072010115449002c1d0000c01006076282d4011350002d05800d03014a04140c0360b07240032800350501a1814800c880140801c20b254205c150681c1c02210b010750300d244556003200d4500050f05800c000454803210409008101010051604400d0741e0f42244d0502c00c010240d0020740c0140f01d040f20403200381d0026892100146061000004d401d006441c00247c00a4a034044039040c5035524040484c00e8058090405181c43d1070b6800c075503440c80440680204541c405d03005e51988044070812003010881900451035030b0080e400940940700180c2031070500c2d81c0380c0ca8070380b008140c2a50b58030521081d450003503080512607400a91502d80c4466414801e03403800d402c2c4080686031000305400240e000d482202a442c080c4040e018018880340302180010b0020006441d24a029021710822814002a08196216151900a4040161520b5580781d6150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412629928 1250 412628678 412628683
    0xf0602040308030a060906050102031e160510020a02070e0108030d090c120302011a06070f080d0207081206090f0106020304170309180901050c030420010e030105100815010605040b0a02 81
    0x1d80006125500101c1800044400d96000c4001d5800310b03c010061240c41e10016641d034001c1143e01c3d1035005120042c925072411247c00741c84e9221030064001000c0d0910394403141019688128109110340c0484d400e00c40c03943c10440b80e002403050300303c000c0c10303541072240954481c0300c3e40c3c050300c0045032140c2484041150780e240c22802000303800f032074101210b2146002030103010203000c500001c03c150b100b50441c2e40f800c4070850391610307401261000344980c1d540e54507004c1d0f004003402c0c089041e42846000c020414800c010000c075121070f6113001d96032a0020400c0f803900c0d0083c0141000c40340311b4005002441d0004211010303140440100c103440548026481e10f0361090360b801da074000002d102000b03245804030741c1032406050190028405507036240400691030100b154040c10183c044a50b14441504000c04601e440d907041c0740031035083c00c0c81c4c00403030b0a44005a524040603d02d1800420040c0801c2c0302e120604055044001042e524000c1e00810070300450055256100e400240702c24401d008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412631178 1250 412629928 412629937
    0x501030b060f031005010b0909010e0105090105130b030a0809091e0606130512010915090201020c01050a03020d09050303061816111509030d05011203021b01090306020310150216030f0602 82
    0x3114002c0c011744d0386400c440b41c05a080814414081d0841c200003261402e100c0009505890010f0076581e04c50b071030711003002140840c2003250360206507100003036202a01e041c042c120142e401001d1169680c030300c040c280541440c00504035400d05000303d81c60540900844040c4d80c0059080707540304c2e103501881e13043e1a126451580441d62007600da2142000010040d082045500d0003070102284406511200c0380983d0322021009006070052184145a036000340003500400309039280041c248420495070400b00d0380029802c2e65154000700c1005598078001031880a40c017500304008045040030380c414002440030400810070301c0b0070910b40700810f0740200700d1000f411011002c0c1d041503060184186403603601c044112000141440004105280309400c045071896155008020903d0250600b540401e0308230441410440c04140010200d00c450000e14000e141d45800f0003045880c003800d08849034180074505096402c521a25201440701c0340510302165000000c07010203041c145003000080c400e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412632428 1250 412631178 412631203
    0xb03010b0a080a0201090e0c04031b09020a09032f04020a05071a040201030b0a06050d05100f091a011707030506040207080703020a0b010f080316060e0d051c0501030b060f03 76
    0x111201c00103650040000c14007002c134000e8880d2180191184110341c1804021501c2650141041100700f0000390b40642c845169001c60600300340d00c3d921803500340c041c3d1340041c1510001601c001c00c00d005101120301c3c100e803002e00c525018041031904600522044d15040e284034403070380d40880e280ca001d0303010b4402caa040ba03a11180120300902c0071034596100d190180c0382a80000e1410200180e581001d241540945e4480d84900b420821003503458006820001c000b0b00c6441d0500e200090a90348808000c005800b8018010030841c00301120380c41e030800314018840c104400d1105504100784403201c0c080d0007039010302c0c0200b181d98035040880e02030f100c1d44900902103540003a810301031541c0423614004c1c0610920707003007039139990f02c8110304105000b600640600c1c1d00104106c51500c0071a000070741c0b901d40b08040108251100c0c000d401d04000260360340701d011400008000c2070b4860a105407a2411000240c02c1055505503129003010810041055000b101480403ca00e81d6800300603552040c0c8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412633678 1250 412632428 412632439
    0x40203070c060605031b120a080a090602122508070f0c060f02010b1e0d08120601020706020a05190f12050a110105010302150f0f0d09020f0d0b0106030b03010b 70
    0x6000c0e5008240caa09044151072680c900351001c07849140128948040c01c0205000001040d5094108062042480d01151a41c480d80700601c0c002410074001c2c0141000b01d0b00c0c0c0203012440c04e50041d041c02204d45000e0f0720120104000ca03101202c00501c41d4030480b600c002c1c10b4015126182410b428460300d100a0011a08900c02404100c40403928005030b07051035403078201f2011019400c8c2e00b0384803990001c0b035201403611190081145180402040d0300002054122039400e10380700c0c0c451540c0300c90704011244402d0410007115580400130070300101128030042520200f04d4a861b51900c412161012264030b030004440188071103006441a50b6801004200042c58420000b8041e40d00004650002c240800c040405040e018410b05040380d4019020100102c422a2602c0c0e41c1e601030911420585c2040c401015080701d081d015152549080c0030004600000740108521542c0c520815031140310208040c0b0700041c80d0009283c116034050401051514100700080c1c090300c44543c521360001c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412634928 1250 412633678 412633681
    0x1207080310181b05160b09010f021306110a1a190c020109120504030b04300207080c0a290d020c0c0906041103070c020102010216050a060c0206060a03060207050c040203 74
    0x61180d03010000f004111140c2850300708550704141c0e6107020b03070785809402c10018800c50300495403410805a2103040301d000060310305009a000400c9800611100b507149501000500c0640d8100e00c01520f50300e1001c00a00f90030440780c0c0d03034480320980c0c00c032152413004011011600c004a044880103070300c84040824800ca03141c655009000344401e4905444051340c80c605040d03154010070494040c4c80e003001c16544140c0e2140c450301e424000b1042040d0011076401c00003030441c140d91b0440f50914800b907015002c0240b509030841d1512449440d890302c07580d509081086800040c02082201080383c6004420100c0003c0303800049008071704040707050b2400083d0b030000d19903000c40d0380000e00d54102c42c0c0b003a0702d444550502c0110f0311030a115240e42c500c2000440c10b21805400700c0e0111070b20510026260218003c02e10300804180402110703542d114010b01000c01206005050050f250351004065500d820380000760a038200e0310000d40090350002d003000a22400b4000040b00c0c0c08090700c20b554a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412636178 1250 412634928 412634969
    0xe04030309051204080c010309170c10060503030a17060f0a142403040b150a030b04021804050706051c050c0a020f0c010c030324030602090a081207080310 68
    0xd4000301c84101e60300e01070500140000320f403550a99042d1080a00108104014140194020040185d040c2c40003e4448080c800c490001001031001303040201c05081c54114200640d415030308103411a0348641c0060000a560f50347c0070310314a0440320300584207030290300c620010590403010072044503002103540d4404108400412960b0707194003001c0d13600e0324a25036481c1d00d48400c06036141d281e901c280002c00108001c50361000e4400d400155401082c070f51204c1e0380c80001c860307040325442156901032603810801036241130806000c10468050235140c0d1071501703a50700d039120307906030103140c2c00d02a000c240400035104d64080a0400402410304104908041140350740035009031040800502c42c0c0500520202000310341ea4a08407010f85410217107040e02c1c0d078182c02410075404200c001d40401881e81c0c6509109500030001103002d41c2c030050342c44c00d005080c840855110342000300650b1003a1a0b4080480c003503c1199144c54010a40039226103036551000d540f12141c0e8440310043c840401e03030104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412637428 1250 412636178 412636181
    0xf050f0102130e06030307230f06040b01050607020f09070509030a110306070207030b011a1c06061e02060c0703111b040609180303090c091d010b030f030703050d060e040303 76
    0x8500d5070850240d00143e580c0429900c501d20458499400da0010302540001440e0700c07c170481d03450350841c107802038078881c650b4281c0f42500c04c101d41c0301e669000c0407d10040c400c1c0c02d4982d03400f4240c20b45085280c145160041035820900801c00b50251000d00b002a5040b4451825500d00c00300c0101a41d201c0590b5050110b002d542c11009603104e4083c040c0441d0b0f11a000048200480703501c0f40c00d021303040c0c2c80c0612181d002030384102041c1d0840c00410041402391750300c1c01c1c2400310790000400002c1442c1030080c01080c003524800b60140008200e44560203968000841d2640884c4e180c00540d501c6200d8601215140c1546181408900c640c0990700750310240113245000e02002690101700e40340d501e031084001e84521450715684181600c0b540e10100b4404c1d00b0101941d4080e18960220715a207404107011120814507413141141c0700340503804028000e006e000c00c01d00c0110300a2501900290038179480b481030f00801801e0000028099014000d80c2d0000c400800c8404200140751070181400340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412638678 1250 412637428 412637437
    0x20d02070506060102010903080f1e09030316030c05180a09020403050721030e010f02011401140112050105090609180607030e0c12030a030c0201060e04110102071406070602070f050f0102 82
    0x481c280100b20008900c1c1d4414491100c0954141d62051248d481e40003d084100b10007a141d030b80d1056406a40e094501d00043ca01d0b4007680d81c0c08000d542e24070f0447e042425441090104004141c10711440c64460b50f03019042d1a40d4850f1892034060503000c070f40c001240703402182e201071222400810000144103011911004464400c41c59140c40001420340f03547c07004000500070040b40c080d1105864551107840203000f403c0c2c103400005001c403075000301e03117000c030109a00207401c54010181c079200f41d503070000b40c9144002200744e081c44103505110000d4080103005103c41d005d24540c400045001095801c020041d040540941c2e40e14140110010040c1c080b20070515254483c0b2906520303c0d080640b040c9100d0b01c0d07000003450509512440460142504c20107180441d9216500030814070054085c0324040c52040c1c814055140b5035000282c2060f90f250b110f4426100c28180c5490207445410403140e00c5036100d0300050303482e041464a41a44010310300041d02c0f912440c0490000d1000550082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412639928 1250 412638678 412638683
    0x602030714190c140601090e0c03061b0a180906030c14150c01061a0c0d11190807150f0b0409050a020d060605060a050a09050a05061813020d0207 64
    0x200c00307001c91405040d0310842101059460280c60940d00d894800e0312001ea03418420f15050f00c801d40400fa1491a0503001e800982e039070703a40c4840d031407040315041150700010b11064000d044540f51900d0031100c00d030050440203403000c40006880f60305910a22000002d40718100106001d02d464001038801001640002c0340c5094a00b03601044031402002c02c1c100c3d01c00700400c3c903500280fa802c0b00480c0d9822460048070302c0e40d26500080f80c007180d1103500f00d50b50781001343c0c0f10f0380319075100b07003081d203080e500c002501c003030203202c1031070740c00100f4041068100251095000f1180005074900403803903100d070601c0a030001401d104144205612600000503120404209115504500c4100000c44208403401060355100914840060404000081c1658001e05001810355035690200c2c0455101c443d4401c0003410000703e0890340d40e04410100701a21096680b680520705101c00316196201340b02000f00340707501407003840803190b4618400d0400030f60001401c0d51184e0003214000c000c1d40200321f08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 412641178 1250 412639928 412639937
    0x70b0f01080606010c020916030b060d0f0b010e010f0509031c1808070506120c070b1603050108060c030103030c050f0d050a02070503010b01090320060307080604051302210708070306020307 83
    0x228905611421805005c02d800030f040c500c907a102d41e007280b2601c3c01054041c800741a00c070500e01c89540d44520281c03000190b0140046441400d280e030f0101220290050103040c0b000e444800c107400d9901039811541040282091540c8121070b0001a10700a11010b000c0d210380e442e0b0721481c0446c0d52040080040c0d010603460146100d4903074580e1501c030210350054540101050143c1a040380c4049107854001d01c1240941d071805006485400300c0500032181c00c0310b520305052b02107403540c0e81407003030300c1c010310202001c1c140b103082042618010744810703c07025040041002066007031040038000c20751400f0501e000c4a2a1044518016050f90009070700c200140c0101c52001603a8101070044c0242e019050351368084840c2103990710b00840c4124141c45a0b00400f104401c0055200c50b0300550050704203803183c4200d807611000300410384d100101036140140407441c14000584074041c803010301e100c6c22321070f400c0048104460281b415146900104d0a40b1a1000001c03d0202035401140500c0b1107581c0c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 412642428 1250 412641178 412641181
    0x71718030c01020a121b0515060a23090901022a121306050f0c030a0306210201020604020f01020109020a09150e100e0a0f092f06040911070b0f010806 66
    0x6a0702c0311001300c8040c00ca0542c120102240902c14040c40e04001c02c04d400140c0f07041a05d85a40745800800c00c0c003820703801c10304000e103c6039240c21142d0034000c05082003e04280420701d290901c540804035513040c0140c10081c04117402d40801e4040d102e043e400f01c001400c409190034511450141403030f0400b54240280351540340641d42020403a194034031481e20104005203418000c854036071001680c100c9015043c405500b06500a00007096524041d0f50081040b0303040204161300c5400e10810589003a1980b40c603100117036004601c0380d6001c1d40441e14010072080440050b400f610445500940c0004282004946105182e1001044c0c07490001c000c1c0205417118030300040d130101516800d2109022440400085202d0038015030702c4942d0460118031185e40b40900025124109800c452482c0c0100350380c00318054581070801b003280c402442c4030b009081c40d030101d03206201e42d0248061144e03c980400d00048000c00c1140c0c030362680164180058134202c02c46110058080c012200b2500400e030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 412643678 1250 412642428 412642453
    0xe07030b01110c0906060702060c070605040303120504050d0305060a05060f0c15042301110c010b0111030a0c020d060e031309050c030c030c0310080106060507020103050604050903030c07171803 85
    0x649a40011400b0b1300351407198444004100c19a040414100ea100740208141c00d2004010f200e5007004190301e44506854504511740070b40940e0800038124070031850541040041500024821424051400d00248039181c01c0c02080041100303800160700803000080008800c94400028410103100354241c502c0d20342c411000c03c0e100e44c41039a0140c6480740e1032840e41c00c4440300500040e200440703203000040d1045241c0c41c40c9883e07044a490001705942d03403812003046580001c0409d0440103800091440c180083d200038000c5482900302901920010388614100200303075020051501d0480c0840c0d80300c440140942a0b06040e60080c05911800c4c800030070504000030041d81c0c002d2140c60f420364116914000500582c2e00000d0800390f00c0203c4000000e2022028420740c1c0103408591380c1d180e03a9009600014083c2d4030003401c4240240d28160401041c10300200640f5045804400c1c1030740e0b941d10314103242d21241035050110880d0b0a0014107403041644103403c1c41e80600741901926003088120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 412644928 1250 412643678 412643683
    0x2070f0c23101403100e0f070f030606021207020609040f02071401140c09011808010f1410060c29241e0d0c09020a020705062d040e07030b0111 63
    0x203040440403c0d04000c0640802c02c07039001544d480443e04041140880d42c48588001e042420703920050341c003443d44203001420b035000c000348041190509013800241e140c140001e580340400d40c0910700c46040031400d07004660700c40d1304507a04068020000d1250b016180b140744000e60040074202d4010108090707101c2c40b4201801015014040d512a000460759203204c0302d22182d1090728140c0c104030081a1039100d0001300801c030406080c60000016800b80950000001c581c03c8401c2402c2030a40503042003810720489138401c6c04c0d996241f400e154154034a10307101042c1001131070a0340b42a01e45405495008030703c8000c407446548002c0c006500303c04400046a081c0702170034082c5800c0004500c0300307a551102c800782501800c8029054038595105502c81c6190341e0f035983c12150345143c0019903080c00c6030b03040080c03030f0103000e0444545140200c610098010110760703040c0342100c4012402e28294806045c0251401010451021600d51411180040c002e09203180420302080201d400702d14803c1c0c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 412646178 1250 412644928 412644949
    0x106181812081e1603050711250e180c01260c040909050604020f0a05030703060b010210020a0806090c130608040f080a020f061b040902070f0c23 64
    0x910840d1220740c4049840c0c210080c84040e0406454141c410404100d09200b40701c0d60803d40d402006035000c44004042e00e10190030b44d41040121840141d80c568007094030780c0d1501d002c0f042240154246c0e40c00d4645182c03958010344445a420b800c00c40b002030b6052100d00701d2030b80b080c10740310b2045c880f40c0199980c40c041314065550002200903403501083c1601c11a40000c0c00700c412600307161f620384150007034600000c0c01b16a41c1d0040810b000850528a9480344105012644004914144400720340c0c0c64a8510000c1c0a650300d420a1640c00d9009002d0400e804040000c15590b81d1001c5a028108000c10707140b0f0f500070803410700003412005100003a10a4448131030602807900e490110101c1d4003a40c060010b0703c40070000200030002810350401445003d00350380240c0983c65500300f00c00d0a04400a2000a950300f0a4104c0a5881d468000300c405a03040703690016124801424410219046100c004100c6800401c3c08920700b081407180d04c5000c0455400d8411340e1801c48144940000b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 412647428 1250 412646178 412646183
    0xb0403140115030305070203070506030a0608010b040b0907081518180a020a1503021b070302030708061012030c021002060114041806020a140409050604050f07080f07050c01061818 79
    0x25102c505000281c400c00081c0303841c82c00142220760090f2120001072141c0e00545a03003d001d6540c40040144940a008100440c2012181000529491004658205d00081420007004a902e000a615201c0e07404020000103019014006424182c083c140050710280c5507010100c60b0501000700228001072380200c05030b0f01400070140c89140100480c0c01c00b904a0746081419001d2280d04441d65101c440022850b02a40043c00d45619600626091002541280c03000340c101c0e1081000040c2c401e015070701206c5d4401c400b070009101c2d40c1070440b40d0303c1d05e51000a511241e5071440301c1d000340d400075500e416145425001501940c400040204a810040ca130400602c401c240c1e91020402c42d41c060040c420641c209000440b00302c00807007120b0760050308454080c558032020700006091900c607180d4024189485c42145052069001c3c0c030440c0010030385419141d01d0f0002500e203d100e603041e90704a01803007001388501d5440b05020b176015500d45600340080307032400580030642c03071514045112454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 412648678 1250 412647428 412647461
    0x40609050402011e210903170103111005090303120108060138071a010e1305030d0e010209040608071806061b020604050d0f0b06030303060a180905070b04031401 71
    0x10341084480c441c0c031350340d10885040c4540c41000e83c4a0462a00d10194803512002c1c0000f0000640c1ca40600b00d006648010040102e6500041c400141401c9500f58159001c560b00840d0740d074140001c42d428864004400c0e00740c0030200b5918100440100203030f059840c2041980c070640c1c0c8035a01500103540c1464003c4060584845002d01106154260a0f002e040741c000a40341102913100c00340c0c0c41120103442c24454512400401070315169282040d001a0300c0040510500f0007502c5190f943e00614480c245030381d603158008415800c00350704490320132101910a01020b569101110740760400c03071280c2e00448042e0510140028194450314056400315200e81c215100c02c0d18901203201c0c01d400c0100e030401c0c0700304000308495546010440c2540d00c101418104841c040c0b40c004011540a0320503402a402481400390f25a151400704090b03600c0d01c01c11580f9444910162409082e8501d8058060302601e0400b180108040b0011310640307000e00a1981c213501060125800c88042054418202 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 412649928 1250 412648678 412648697
    0x3303050414031801032703020604120503010501170907030c080d1101020c1c02100515010e040b060412020a03080c071523090310141902031012020a030503041404060905040201 77
    0x540c0a54030049070614225000c0001b000040c030000f01c1420651001e40143e030003001088104082442c02c1c80101c41c40b460007600b15407411001a0400346022540314060141000044650404210b0300d002150881050200d0a56a0080c6600c4500907030080d00051240907140c581c401c0140200e40342c0125400003081d102005104130b401980b29034100c541103005031844800094011b028480c020304840d12034200035030a1100140011142c0100756000781c0c06d0801d07182655039908141c80417180760040103407410510748000303010008280c20007000154045075001c410b010018a501c29224101070050380e6000340f41082d140d03a201408035210a8014120025891510303402500c4102005421103102c4410503950070250b41c0c6449449032a00c0601c4208003410120060a01c0d4801c54813070708501d9801e01407841d003810a56401031240c0035511486840454031503001e04001140c04c1000d0303d8440380c40e644c0b02c1d0801104400b1b15482070b418100b010840700b516110300c501996050b102d41511 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 412651178 1250 412649928 412649977
    0xc010c0305010e1501051902030414030c030601030803180f06090624040f020d02210601030908300408041412191e080306040510050a330305041403 65
    0x7245a0001805d04005090291080301804000d40c5403d5294980165413940c2c00c3c203002c110044460242107229522030030913001d541d1800707d03180741500d40010606a4031341d511740c080c02c03441021503010f03200ca200c1c030103441540c41404110359000fa1076903c161995034403101150801440c90310040d80411088608203c25490550710200488800d41005810b01600204031000c13a00600710488206003070322480301f40e0307940241d100c07a445007007402e0810046d031854450205e20702403418102200b480c18161220410101c22400300c0002c505000036526280528015843d6049132240184542004082ca034043c42d10f040d004003d42c400100400c1c1e00c8050004078030f10030380621402d13039a124030303500359050114a14800b1240c43e802a4040e079520305006c01448111180108003200e80190190705014964941b28010100c40c032801905200495210381100c80d1040c0c1051840300b000707890110340c02c15406800061055014070302406010004003011600d9100b103221100d811118a00c0b052070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 412652428 1250 412651178 412651201
    0x6090d1407020f0a09091203021809130b07121503080d2f07170705120309030408060a05070e04200c030910021c020f0a06050411040f020c010c0305010e 67
    0x1c00074002419a0104040c1e807000c2002c592070f5401c800d51803516541020280721428603c0e020848680c0b408524050803800c101c6424400d403a50503100c0e00300e0801080f403a0003202e6000324807941000005030681001080984898400e4840016041c204098003000f4a02c0c03081880440f0740107000b5500d081c1b4403405420041454190719004114599402c010741c00492081c401505d203000003441d9101522705012150041980c15040c19203010016900055000704107000306030b85654245803641c0320508600e003503003e2a00f101002d44201002c01107803520f240c00090203540c95072520844140c2400c24001956040002d2024580000010001e400c0318107000b0654102e05100303403414440c4030400101c10006046064006030711408a8801c04904407144c1c00c1014060300040c0390040c41800402e44813100004044c1110343e13154005410303c480f150300c003070001e540200104034071103584461000a405c0183c24401c00e62800d0740c1d08050340d029100e1903040e40c561100003404e0395142e060812 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 412653678 1250 412652428 412652437
    0xc0224040b1915050102010f0e03040b03041a0a0b281406041a070201032403120504121202061f0b0a0c0804030804080606060301030b040609110a1706090d14 69
    0x6140c0000903511500d60b2840d0721031a03040d451204000d20400c1c0c5800002801e45602c5506181c0f410301d44000e440392518008100c800701c5940402198496031036050180c3c3c00260000840c2c0c2c01c10180003040b455032590b60003584208003c80302c0c6050603000c41080b02c5020a14030500e070180d9540c0710107118012a2030260540420001c02151603c3c1c0c9a10035101d829101a441c1c925154000c220401150f815002d941002118584003001408200c011607004440c944170142c50603850740058090180b10310300b114003402d140c0040b60754410042c43c0c944105008601c8440050285001103081c15000c08008000072803000d0813048001c0c10720841c2c6913154042030840041c410342c215180d0000c0c18003400f40004601038404030740c03141d2600500700d0a0a02c010710701403103050200014000240a580180e070060b42005000a401406181100c9225216880b841e84201a60302c002140d043e01140f002c000441c20095035216110000501d59400519040c076012800c030b070200396803910b8408082c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 412654928 1250 412653678 412653691
    0x4080703230d020903210a030506010e1f031406221d060a06060c0c0e100302060301170f0712020907051306090e0f0f18030c010f0c0224040b 62
    0x50034614080d0801241c282d1040c42c611600326004100c8207400e00d03003400f02c0c0c400c511039441e07101e05281c1810006032051107101e03502c0f400c0c10303503a0307000c24000d91098140c40c100c1038000d4000003904084550211304c0181e08417545000034207040b44000c6082d0700084903800707844040d24060481c0000006040c1c1074100160042e4401d82d14a01440c41800402030b070305c0e0041184016000318244200b18805030340c3c03076030800320511400010110014007079401e4042180c3c91011203c1003503c0307005e0700120001043e400079510000110000c24054001500000c04179480e404450310759003c1502151159034900c180381c0942e40401104001d42040541c2d65880191031501500d0260a4400c9500000c0700d0340002c1d0018204860038000f0134070142d03c890704144002040d02c104c0c54120324850b1150301c0104440008883c0c51050601c1c0c40d820420303200c01c00340c400300a000303036000f410b8808000c1540000c80001071040d600002100c41b00501d0201441d01c4680100c021a55507444000d0030304d9010307024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 412656178 1250 412654928 412654967
    0xc030a112805150d090b010e0c0301080309010e01030902041a3c010504080106081c03023405070e0f010b031303051e03040c09050a020a2111040e0a110304080703 71
    0x4081132900a02c0360f035031030611a0700035080c254146400c64030300c3c00d8001c3c21202024820401030080701000400e440155009203403040e012079004004a002d8460904001c0d000380c10070200c03e85041e1800248008200155040f00044c04802c0c01016626524440641e40c07441c0196070800d5480c5050f2a6280c2001c18100986020390354202d10742114902e42c804072640c0c201d14503034640c2d80c2c5640200c0800c00610310741035040c28819805120f59400c00248621919251101a8121b004891445c0c035003d4100c0207039021955614a40c803480c8004850344100e02005100114542d44444103072401840c090141c015180380c0e03903a0a8441d41e00c0424146802d5020350120810b80c0040001140704610560410424a192520382c8007550300103000c0309400c2d40107001c0040d4607544901030010704141204407403811403488484200820301440c0c801302c28a00040c000c2003000c01214614001c404171141001000d10400690285005c1a20018040801085101d0110303210b81c002c00c8081101740388 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 412657428 1250 412656178 412656187
    0x90d080702040b030d09030302061501081f0b0a051903020a0801091e090302100b01020606150d0b06070c0314011808091216051206011a0c0c030a11280515 68
    0x6881c2c110317110b03448000204030400c1441090380c18040da9800200e03040b640380407101a0400601141070082070030070442855141c447c560465903024000512219030032694402c48418010007030b0788440c2d5402c12003425060041d0340644207101301c4041006a984480c00d990074000070802504074108680540d60104a070300100001030320500700300a1003a001410b0003080400c052094603c030224044c1990403081c2003019545501c2c01d000000b1340d55000b120342d10884402103070001d25400d1203054100002007180d000b00044e090840c000d80c0d010742e04910032402c1d07000119099500d800e2040440740001304050f0b0014072407038040c24501c600103148000643c0d0103801c051401114000e101204400c441d020015030501800c032900034168000034203000d40c10141410004941580700c41d0009000040608011000b4800764601042c0103080d40d40b0701110b03060108401c40f46100c2c45129854490a90360454415000e40c0b14908000300c501124034580701c00c011040e4140c3c1c0018004103010807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 412658678 1250 412657428 412657451
    0xb101a07051203070305150307051003090213110901120e0a030c060e060408090a0905060612060d080406090608060910050f03011e0510081b091915080c0303090d08070204 75
    0x60340c42040c0070340e000103803890035004107410b011f05098418080c1e04004414032245d05c520b1580c03c541c82060501103031414651020881c80600311010908140c07500440810340c070b02903001003100b91400d036201e441c0123000682d458101d581140644285034000560540000d02403920710100700d001b40d00c0000c0840e46024114200101154120342e42c0300c002a65200310700d800642c082c058250001d041103180791130400b050f2184203c5900020308400c4c0300c0042c3c06581c03441100158281e11402441d120703681c0e000051302c0c551003805214003148290000540c5410424085481042d90110510f01c5c0c07031a02042c010640d1143e01801d406540307800701c054900c2941000b036101824043d41c009240e140001e40020841002c0e0041c9500340c01c403004a420001c0102405504031078115141d043c1c0e030300d0705100800950107112080400300c0c00d2006102c030301c0d0705450000c0c00b00da0440b8141c808a400e45c0d410907071170344610704880fa400b41025200101103101c0c08094400d207407010b000018400100d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 412659928 1250 412658678 412658713
    0x9050a0201021e0d180e28090507050402030606161202190f1b05100e03060c0307080c09040605130e010c020f07090e01020918010311090c0f0c150109090b101a0705 72
    0x1c40b50712044421f400d179160b41c042000d4402155010b000c01d01000250815640d40303032910781c02d108480c40782d80c001c03010545540c8d411007107030245070300c40301c0c4403608500368500581085544000000035002c1c504491000d000c000240d0b1512550000300c00002400581d40d644040c402d0302800985000680c00108180c1c80303901c9000207206181c3c440c0b44400c01818101403410710000c2101020900520a1100c256001f1090075000610b1850603071302c0b0801c0c040442c004100c1c503403019034029280200c102034180c065100c455140c0568000b8480300101030010fa907100c00f0004000c41c0ca0348010300c02c004084a41d0b00401d200402e440015103840c1c03242000403640000e141445c43c01000140041040050302102890f1001003502d440c481807601e0f0000e80180d020308154001803d5001400381074076202440300300f02044031500400d007196111601c02c030083c440e5413402c40325065000c0105070b9840d40072b4501c0302142d6032082032140641601c40110025004000c0464840c0300300c0c0406c00c40c00b40e04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 412661178 1250 412659928 412659931
    0xb010f0f12050702100e072111030d03021803011b110a0203160609120510020901020c0d080c0f030c0c0d0203030f030a0b0a1203090e1909050a0201021e0d180e 70
    0x216030044c008a0600e031710080c21103941c076040040ca41d2040c401042020070428014071071580b580103544c080720842c20300024220420300100d0303041c0180f02002101d950107034003a110400000b000005540540e006250803222000e4014040250011240c04c0b45846400c0c1c2054041001055502019007036001c01c3c0751a444d081038225640d1703100810b02030030341c2c07040800c4010302c8145d0141d042c002554a4180d01c0749034500e20400752135000038030040785034003c004081a40703002074014109040171b0309200005400c4048500d00074000e454400c44040700000c10741c1d401c0032801c0c010b07042c0c9145900c20010b524090130001c9806001c207100b0740903280070290245100722000680807900300440010030040279620341020071644030107240040480e41c0b01400c2800d035408140000044d45501000781126a40c50b601141c043e81003480c40310070081d010603107401e030901c00e800b16a0800b01020002c008403002a0644005038026a4070182c11031050005030041e903000b810120110f5141d49080441110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 412662428 1250 412661178 412661191
    0x9060c030a081311060f09060313050609070b1c060803160506071b0303050709121b0e01080607030f090807051b0102060709050402092701180b010f0f1205 68
    0x4042200600c550700001c00550040038450200303d01140395544a41c403070103110b0903e019850110301980c1c0707145407801310790421070003c010035102d1030720052001112508000c115690300900e00482c2c010400010b00406035184002c2c1c542c208038000c81004210b680102508660a89400d8001241a0b06000031304c24110b00c0351603480303003103842e083c810302d8080b000c0c280c1c4c010001c2201c00400b6040d100500b504005926190100c0e4035210a034040700c003c20942c104850000c1058512400c001c1000340b003259031584107100c14501c0b030703a5990200b41c90000f4403e45026070800000609001e1080d407004481001902002131070302c00507110301c54141c00030b0171b0403901c40d444440b140c042010443c804054802e001d100030000b88c90401c1d07000b042c80140d07105190107190049140403260343d482038001e0072804c29509403480c10003c10f0440c250440b082c455042c0201038481c4102a080c1a80034000c080d15041e1643e0b00300020649084401144200007034082200000c18082042c0c11030148900032003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 412663678 1250 412662428 412662433
    0x20d060e0906060d02130c021501090e06060a05060a0c0f080304111c031b0212010507020d0908030a02150a0207140106090b040510120f060c08011409040f140309060c 73
    0x14003600400d00e44800505910700c14000c0710740d98801a907802400c2d00035052009000300c7e01c1c228400060349016108280f1250200c0078200100c0c020f103c0d40d00001d41100d80310100d42c2c086e00c0d5503050000c83c03c6030340a101d8100104000c0c09500d5405011000c403038602c210403c1c034030300310320f0348500c0c40031740041d6401c403050204a1040b00e0203144c4081d80c0a034800d0445940b46c104040356801404003c200ca0140410000240302c08003035540382405540e590004000a10036032401c848002d484e480c1ca485002d0105030240e4021601420000523107031003011310340082a80c1008149003c2e0905001807412740810380801414001595104900724072464420002c03500b14281740f0a941a2802900124044c1c0e1411042200e071035802d580300422188503041541c601440d41c1400c1c0f07072003040d400e405008142441c444000c49a8030407181d504a585100481c402000307051b0803c80800d805030741c050b01c00e980706c00b4110702042551800401030b01c41e41c800c030391803c10f941d0007080307158201c07010803071058 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 412664928 1250 412663678 412663681
    0x171330050a03060509130615050402070f06060806100b1803030a02010e010501140f04020702060f12011401030908121005030a030918020406140702042d06231201020d060e 75
    0x3a018001c3d8030240004644e404c600e4588035688071030040014201800050b10364105120f1000700b80d804101030310014005541c2c400300750400300007102148500305c071003a1411400040c110800b0403068020f40b035400d107a1a150745071074254842600b03c00c040245611800355299180d40e01000208548440d580001c40e800c200480690f08683c1c0580c03000e900d4460060064215135610b036405007a07260100c0740141c032000d40d0300200da098090800303000340701000069031803104032041100030304803501c0143c0584000c4054004405440a00c03800034915003003880b0301c1840304a031800c1c803070348042d051082408455031a40005d1810325100d9007500403810281741809210155100554000c1d0743c0708095183c035140c00d030018444d200c6c2ea802c0b4100f511001c19130a0441d942d40d08600c10300c960000842051100f0042070380b82008651046510480c40d205000408074040b003001588000603562001c80c05180740203108160802045484065500300710141e80c0c941700c0d10030310025000d061940a882e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 412666178 1250 412664928 412664947
    0x307033603050a17040b0a0302032d01090513020616030e060f0a02010605030a0f0b0411040c03020910020609060105010509040f0509070312170406020d090f0b0717133005 75
    0x40c00c01142c20302c07810190400c4240159032682c821921091f140385001a5230340c0d00c08010f0807a0644044c501040c82000545004007040b4140b4a80e040c1c0c1c8010408129a0f00e4242c18030b440340c1c20706400290008001e0014a400d00960180740c89801d00a08144040140c00b5001490560041e420003051040104002c0095942403240001130300c801e80040c441d1480f26201d001c0444c8449200502d40d03807411000804200c00c0d100c5013034040501500c00c0c4100c40b00001d010f0084d4024100160158140d054a0128944000b070581d0240c1e038030780301505569080c40011952030b031010f0406a00580c50b48032116141000b8403805204101010240c0011400d5140068400301f61005200c01c004050601030b100e090b8980b6010782060340000c00580c0c48901001001c080c10b5a10005898401c2c103039080300c00d005914818034881d5121f41c0e1481100c5403040c0d007103134175440140c644c50b40c10b24048150038001aa502d00f41550314140d64800300c401e51803074103041d244010050714400096800b0480350300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 412667428 1250 412666178 412666193
    0x212040605010f12050a0b06060c010c030603020f042a030b0303160b0c0414190e0f0601140f04050603040f0b0916060f0507110103020f0f03010f05030307033603050a 73
    0x140410320354075400044d45495a5598000d0800d025014040300e001103031066540508984800407410020f00103445440c20103402072119110903402010500c140e00340034a4184511141c0900b88000f0840c100020b04206240042c0264034405055503041d0724402907904002802940220180c0e2640b0580b8a2801c44800e00015000311080401030000380300404c01002034004c409400c2e2480015001e04856a0040e400301d9440303441030b107100350180300c0b440c82c0003200244686000e8844e005d030803031042d0030500381e031140715031410003540280400d1180d460b00304000d603001f501aa00300448413050340c9450340344c46d41c2500c0d1401942e210b4042d00c0b0f103400145c184800100b100b4100221850340c1c03180090110300c601c040c01040d03000d0320010031040b40c2c040c1d4160348507203019124540d1200031900355400c040d0700a0280c0810321102d5940000c0d1460700100701c1c0c40065040e036640c110f100e0b03501402070200654080100c150304500700442ea80b0a0040b904400440c010f0380140101240c60802d00b5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 412668678 1250 412667428 412667459
    0x607150606020102030709060e130518061005030309010c060b1206090f030a0e091305030d0204030c0801060518040609050a0602090f30101b080708011a030a021204060501 75
    0x1010b590040c0104080c15030450004400c03101241000500075448200159030164440300d038864841c85d140500c00001460005041c001803441c00f111002e89510190412a450510801c7e0b4198002c000200d1954452f9069001c600e1140c0b101240c81078207800010504105a86a00d20580c081401c00540400400c04c42807660540d50145290080d00b4800501c541050540d85003e07540d0040450008014101294107c4c0d400c91b082d04e458400a010250107984244401d40300d000701a000030a0507107062103250122000100710b400f0318035001482c00041080204190b820390303500e50085000c14801e101c0b4015036485944010703034411000040104420340941024062031032004100b8042c441c100c05204000d4041246020b00c540c10680146042007821001c240c041c180a070714200c01c04116442038400f03445403074103080f546e01c9080c1151180002d100e1255440885507640064000780c10056400040d2000c0141c50040c1c1202d004041d0107007600d0840e403295544004108000c0b540c038500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 412669928 1250 412668678 412668689
    0x1020a020a1a0105060406200109120f0203030118050601140c031b0d0e041d0f0a12080f190204150e040617030f0a030603050a06020d05061219050c06071506 69
    0xe440b550401002c5882c60040703010b800f09002900311408082d120904501c0455a03a07003000740000d080a2506e00b401c52590384224000c900401c13454913180340003205981c1a507180f8210002e042250380603800c090407001c2c2a49042c440346544190f07d50004d5002844491454001180da0710b904c1c20682d01880504407043c4000d8000190006d4920740c844070400e4074400844010440c40c01c1d8800d004010702c0082c11030b4440d482401201d54054801280d2700954501031142540700007400d10058030700078421074035440103800380000218401c04a9402440c1207143e03800042c10603407110445240300300b02561041c00315171a0803941285207490b0003001c0282421603126540440c9104016070360780980c1a000c0c0c0390741000f203914800c0ea40709610402c0195004401c031030100d030007800d01c00000d601800c2c03900e80013400c0c040041c240b41468801c04900c44040c41c0200307405048003c07000140990000115003c3c0100e04401c8825a03e14010f040340f5801101216400c20500c240801200d080380d01a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 412671178 1250 412669928 412669973
    0x7140d18030f03080408090612180a02100f051b010203090717030702090a47010f03020309010b10110709060f05100e060d05090d0e03070b091201020a020a 68
    0x784005014103900ca285641c0c503060a01c9152218940340440e400741d92505900601c0c040780c0703145140d80a200340c03800703050039180361451a4020b000b402e880d22407101019401c03840b40180700c040c1d244101d90025010700986011130610304109500d00d140032a003980c000c9180c1d004418030481003c2409508018261044812303130031034061400315200c0c091400040c0c46800e0a00014500c102d240c1c01c00d00b00f6004100eaa00c1420000194848420200003040202c030f000500c054505400b087c0b41c1c1c030803039080585424000109101045005c5e60000300304000039500d543d41201a611118203a0802d00700c01d84990340c1680580981500e40750f4076034000c410701c900b4200c08020003a0211003d030142c0d07000b500c00301000a408038043d521050251440c43c1c002c1400030ba124100c0c0543d520040c080e5040c0b00540d480e0f030512240403203400c0a9480080d034907030000c400800401c1d8200004100130340028000f411094002c0d260182244c00032040d200250300050007a034100440c24034140803600c0d070200f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 412672428 1250 412671178 412671227
    0x5010c110f0f0d050a17010303030603031403060904061805010515151c09080c10052202090a0e0a0b010e070206010b0406170a06050618271b07140d 65
    0x4242e9507500700120400280300c0009081c02040d071141c00e03001c40e1826070282c000580d503528980140101002e00c01074000656203401101d40c90035001c200c9004501c01009400c10340c85070346505004080165403208107501c480e8400d07001030828095548030351241700d040005a0807140c1840300022450b0350001c90000c08006011071030034074041e04403800040d6103001402031414500b500007480303103180741c1d5910321900c0d405030210520307500141d100e00c42c40c8240f080d5068011200c1c041c12800c50798001c2d802041d040020300c044a00e6480300740d03000e444008071003802040b52180c1d201801d082e00041002d80110040000c0e00c1c2d0104440da00400139500350901c0c1a2412100802c0e80d49442c000243c48000030000c142c10004c0d03500000003a0000500b200d46c0c91440c08070b440010051100c005010f0003224a500000340b45040c1e620035046c052000760f0b0226a6010200c060700300080020700aa65801d0110790702140f9003c00d2070400910640c0201101908403030003400c201400350007900d46440e04003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 412673678 1250 412672428 412672453
    0x1302101e0c0c0b0706111804110c03030f0a0b1206060a050f01200304170a1406060f12120a080907050901060f030f1e020d06050a0e041e05010c110f 65
    0x3a000c0f43c0c800740210740c56005038541440030b0412948031a01008002c203000312038407130080c0907080e60b0320f00f210300f00407045da62806484a40540329610909800501c0058a00550f402031142d200d46000300c0051034407510400180104110380b6100326942c06401041180e091424002003c0c01040f18203100b10f50b12580001c10b03d51520614078800c0200500380b00b01c4030001c02c2a90003914000107904070503450610b40c1c40d503400b01c02e042a192030023001c90488480101084176802203a0140c605070200740000184814110200000e010500c6206005c0c500a00c200c0050901030704969507010190070041051450318007960000c52007149210010054207400c003800002d100d485040100310100840d4801c001051408407440308a02c440c0480340b000401a4028072944046110800005845a041c001a04014010500c01e136900c07c002c140410400d200c15440950810040e0691242c556501800e645081d2100c1e0041600c202041d40484010300043c103030700700c4110041c01d1655070303032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 412674928 1250 412673678 412673693
    0x306040803160c0506010b03071d0f010c020303040b1308160b09040525180608100501110307080f0405040c050304050a11122d0f03070b1302101e0c 65
    0x9000b001910120b404a84200d50041010700c0c2000e800c40d060700c2c065a550f49044080741e0080700c4240c0022040750704804001035000d13030403004010140000d800320700e01c4001503810128901007039078148000e0200048045002004110304c1d68403080701130526151843c0180341603610920340301030072500309050280c10440301c1940d0411008880c0452030707465895140d48001341040381d00000e980c000c0301d50f425041e0002d40c1ea010401c4040082003450340c0d0742000315008001030704c11481d00c1d0b2401c00108050f42c450702229028040c00b00c196450581e0940c1c400007554803d20496500100108082006103000c0c420480c44a501d030518501e54a003950701d840c0c80342c6895a004000042664100321180c807191408140120724200f2a82049403c803048542d45200d1b0042c0078030381307440004000ca030a4002c10500c0e80489000002c500348102c55950806a400c020245100401880d481c4805645c0710351010110f169a61179011034016542814401400003400705814021011103440008144 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 412676178 1250 412674928 412674931
    0xe010c0224040602040b0712020f1906020d0b060c0f0d0c0809100201020c0a081902071d071404060c03091e05060c0c0306010611060907060e040e01090501020a02010f06050306040803 80
    0xa10300062142d511850840000e010f2034000450f1702c2c101144e400204444e04801743c50402241d0200d91001819181090791030600c01143c901ca01c0c0319200060024110341c0113040144c80c3e1400c040b4400784a2004a64030b50030a8201042c00d07840546241413005041c022110015458501000303100c00342d80750ba00342c5101d40100d440c010040c142c04041c040c0d10070b46c152051482c0751015203220f017040c0c1c20610107036084000c06c194541e819500d24280e00d0300010321384003140c0e030f102d11401c45021030010652070b403c0700400344424081c10a8106d1060f030200801480502010f840700d0b410810700b402c00400318441c94120307107101c416100c141e200d1030320680d41000403100101ca0b6656540110b000c0c0500704200c2d8456150148503446c004a00c2540058002d012190400211451659512601590344080e88191008140000400440c071700b0180c004c001c0c9110801c00100740a9015940e4a0881e8030560243e40140d42d038903200da0942900c2e02070180140307400c600400560402c1e840d203d070309200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 412677428 1250 412676178 412676233
    0xa0915050f090a0e13050c1c15060308030c0d0c030b21010f06030b06120a022d090a0b190b040b07021513240e150c010f0e010c02 57
    0x841c07075081580c0d0790700001004c1d22030010000540d0a08200080d50078aa602e011609405070030310001d618244801d04030001c4424141102c50740060f80c0355104103d40c00c035508025540c0794640840810711803001540100b142c40c3c1d01a50301c07115410300000f151164200d400800d41800030240c0306640303a517841e00c04491540f010301300324001000c000e401054400100d01c00c0714182080001404a91041c1d01c1c42030780107440d40e030310815094407040c0d21030740c45000095104011860080c00e00c000c00c041e00c1c0c0c0e0f900310000280e440340d043c50b000800d0792204441a802080d143e409120040c180506146207985012032500b1055003080814003040c001c0e402425000e81f400300b0343c1e4065580c0c00c40340d544490000d00720103070f6401d046211500d000440d0b00501600403007691500c40c40030840c0c040031000003490340c0d404501812080c00c1055042e011044c0500011060200c0c2000d60020300c01d5a0704c0c03600c5d035100000c10201c2e20001c1806e4500001c1e20005541000d42e414400000420303087c0001003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 412678678 1250 412677428 412677457
    0x50f04060e0309030709151203140a050702041e0e03071a1515090301110414090a1e090203060a060305100509030f0c150c090a030f020604080604080a091505 69
    0x101c66603462491409083d440607454480c0300d40000c2c910420754414001c0a54012682c501c041d22102c404002420342c40700100012201009001001801c101809031201186003d0f880c0c00015000202900c07590200b00e131825010501d000c031010000d1040c1485141c00c50701850402c0e5080c2c0701d04a400903110324031500b00024100141018884103420441c86c20f00400b51a641803546140c0d9503250030000c1902d00075880c140c3c1001071442894240d50841d043c807400140e03052413100c18014120009481301e01e65640301c0c1c141e1b4200101c4040481e03990300e0001e030001440d0b11075004043c50140003920a07000d817803500f80300348041140450101c2c0c48920700b40002c40c2680318215400c1c998420940e0840000e80085003500c0c031840007050b4101c1c401c001030001d1409458030b8040e4649442034003030003903100d04446000c100044280070307402c2c111800108000d0a00d43d5603030b0390900740785044034116000d1900088810055070002041005040c800a26103140341020038080d00c0ba02c214944614030b030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 412679928 1250 412678678 412678691
    0x4091b020c0f0103200f03011406040b160302072610140f04031707030509100c1b060204080703140d03092301150b0a0f0c05060c0f0705060f040b0a050f0406 69
    0x3d01c0c42a15450001c44001c000c82c0d942c0c0c1b4000f00680d10f40d0420b019200c03c0120b100030180d1685440010386096440c11405140307030454501880007404241c0c00101e00354003950400007400300030b441000c034042541c40481d81c0781c015003401c658107000a0080004d03c42e4540000000300382d9405074241d61041010481130f0b02c54503941004c1c1c5148030301c810b611140d0b62000b010800c1c102d9240d0081030203000600201c400e4900ea800008042c0c810324100c0d4800501504d080da0240035100700c20402060107071100520345500d600700941400e88a800598190a1a07081100940b000304000c012070440303031408115940343c035943c41c51518100a02d41e07080390407550b00c01000242c2980b042c3d00c0c00d095070306080c81d071030390b01d1030b91359100c0d0001840200803070801110760200b80d0140070010742881e8050068503040d0ba039031100c4c5929400c09081e005040130700b403283c480000d10030005607001d111100c80f0f0202d140380500e072640b070081d4010142d0b0310740c1c1d050500344610b548240540a811603444007020a00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 412681178 1250 412679928 412679951
    0x6320109170706140c1c0c0f0503090102061e010b0306010e0d030c020a090c090e040f020907020304140d020f010e01020c0a0e0604050114010c030c0c0b04091b020c0f0103 75
    0x6000d180c11116112201510103104a0000520326045800c01d854040d8503510800d0041104c1c000c020403d0788542025400d05c8415a9006a48800000d2414403005482c203d4880c5080a80404c508441e107500000d003510042d0f80400c28203034000352800101c3c0c030042059910105400c018070601001a00100200300981e000e26002a2140400352241d4416141402d0003003180001d407800341e014004c00030002c01d603225a0b000d03011469a040e121004400d143c03210040c40600e000700180e91441c40d11452500680d69544004e01845184d80210380321804c01901000740e07860040941c1c0b04103034550342c050040e298803103815403ca5003402c210100c0c400c1e0800503424904000c070f009078050340700039002c1812103080142c540226800d43d000c001c56038075180c000035485049403000e404144403120010010344214085c1d01518482d1008426007a81c540400d0455005a0000d200702034a03108124048040030b011800b12550910003880c0d100200c10114181c0140290300604050312060342541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 412682428 1250 412681178 412681187
    0xd06090e1f11120a0504150c2012070b01080f0304062f06073b060d23041103070302090a020c0102040b0d15060810050d11040e030409063201 62
    0x4200c070324140c2410140c41e0013680c0038014107044804035010100380060fa005a86188901310b85010700d0703115008842c01d40d42d0302c0900380e4552806050345114031201d0100c0328000d2000340807a2441002401e2a55040481a904008a56416031700c5944140020032201d54000400f00c0e540703002c2c40c284400c41ca203e003d110481d124520440c140c0744a0a030600c1034482d4416260324814101c24085c084100c81650b000040017451f144281507290001038001d4946401d500801880e03010350f03400111000303814000041d2203012101c01d403020000c0401c100502c041c07072202410011044010380601c60440c1e00007041804064450f0003040e83c00f0807208801c03c0250304941c05401c06145040d20342e003003242414060070b140340b121070711410040400210203000e414898007621750a031741c1010f0301e4208000e000c031201d81c541c82178a01c4110036001c0f01c1661224803590b40351100305400b46940b10700704400002601c059070710a56240705601c1080d02d5200c0144114812191040201084203040b140100c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 412683678 1250 412682428 412682437
    0x7030519020a021008070e011706040506010c0501090501090c050301150614040909050a0c0b04080a0303051312020d03060605130302130b03100e07061b02010c020111030d06090e1f11 80
    0xd402c56079070b001e044c140036004a500c1c1c0c40340703c5c5070781c03000000700d140001104c1090354983d40d01d0010300400045285c518082d040160f10404c1854000d00751412922190709403240c03280242d45036550380026406120072003074243c0c00740c90164000e00280640100320341c43d00ea918400d4170308000943c40c01c0c0c0e0803280080e080340c0c01448107641c00c1c0410720039410010b407150240241103581e240140b90004008801000f40e07000c031035401c00940100401500c0a4014140083c01d172040d407250b01e4041000100d404074440061892076008104208040c2c5018080359059080300c3c0901c141030002c5084200101e5010f025281d056800c50040100100c20001528a50500ba94140204083c0d0107400003d43d015004466030207044a40c80303607403804152100c14210501c010010080800303500075500411120800c0c601c189098110105e8450100b41550484403000d0103940e1610003c10000e0800d019804045009501405000d900c1540e1a1860340444e0549001c4503107805407401070000f0003055a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 412684928 1250 412683678 412683683
    0x10503040b060a090c05032203020601090c030b0a1403120c0d051605250b090901090207020a090c031a03011103060114040f0f0611010b0639010606090b07030519020a 73
    0x140500c64624802411b290812140842803188403900c0c132140491415101d403103541c0580141c102c0d80d0901c80c0c071070040c0c043e00c00c5003010300d5110400807c0303e4885450000060002003c0201a207900100301400c18185040c2048001000c2c01081000200400d601e0800d060310704200c1d03a0389402d0803000d0410001f100c0054194010b002e03180f07612005500500c461001460400c000c007a403100300d14592805200c0030503411401000050100b0311565000705074040c00181140a026a9402180c095443c0d0b10340704000281c4071314011010b1040e2030544da103500c00c21030082c00300700316606105280d40030080c07a29042046031142030003003034120812203014009003034848891603103410200e41f034042240703d2a0001a109490b03041c0c141d406100e50f22031031000920300ca146c01070384200050307110f818281e00b4419003030a01c201c1c0303c14200c180f1132082100c2d4000000c00c5151401c240030745801820391101001e80f4040080c1740000380c0c42411610510141c4080d02d5191056107000c034500800c1a600 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 412686178 1250 412684928 412684931
    0x60f050405070e090607021b0102010905061005011103040e040f080403060e06010e0702030a080c2212020f03060705030c07060605060d090605061e042403080909060906010503040b060a09 82
    0x901050020201c0c0b03001c2940d41c6400f40030704603250710258982d12201160030200581118000c1d140c1c1388a404184200c1c4101440046048501e58480c01c0c01c007102514010042082003000b0429540c2049035000c0c0c0034415009142003d1600b00d68582c0088020002002040c40442388820024070b44251400396422500c02c0203805031244c003031a6240801e000e641c2c0c582181e68001021a480001240c8100041d80c0d503440064460550b04040c0b43c000d0b2425115000d1101166404a50a10310031001440c460315000000503450052084e500844010306004c2e07008101003003509608501100d0304460907c60340d41e600c6000e030400344018240c1c1c1d004580d018000042d400010f0005030051443c03140151001c01c00da84500041203c244250b007810440e417010b0078110300c13103482d0544c44802c5d940c1002c03024070303032000d4621040721028241da00100c4401c030703001c01c0b04d006904108076a1a071280d800d03940c0402c0d508007503001030000c0c00000c100500e90300649000a0762511458070f080000c00d00100c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 412687428 1250 412686178 412686181
    0x30a0e06010f03020f040603021e24040f090203060109140d0f030e0f0a05030c090a020f0714070b0313080703020a051603060b150a050f0906040303032f09010507060f05 74
    0x400c40b600d8201d48410b03442494520031100c5189402c2c400d000072241c0c014848444810350102c00031f021150468001d511440420305002c0c0780901c0b40e003201120f03801c12107056669003803512101a014003900110780319803061003040030690b04070003807a080d034400403481000604180005801042021801000d400020f8454800c241d04a1113801c103002c07080b10405484c01d814002d00c91203154070310482e981903005020004040c1410309246070407041900000d0300e80308103100c030600c1d00c4d0b1005d102140c0004080c49028400c40042c0140e0b0098441c0d005d265240d070801004404c5000c2c0801d1003d81781c0c940010311101058000c1082d41c0000394403030182c0f40b1803403480941100c103861038401611680c2c1032001c20070315032030202c1804041e014080c0b0554102220200100c038240c201c03400c10045c800c410000c601c0142d940c4006000107621030f950210b41c1c50291901c80c4460903503940d170795001e10408030081100354000010703a2038115003071800d15180d01850034110007402443c107410111918150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 412688678 1250 412687428 412687439
    0x1103070f060504112202180a06260c0f0d0e0a06150602120a050a090b1617180405130209040f02040605011701051504050907121a0f06030a0e0601 64
    0x400a40c030450088080824034030150302807000c4207594171062070f240d07001c1280d0486902c881d03038054010102c601d5004100c02070182e0204e41c6204958220001040c0e00d003030300e100a102c0c9000c56900f0259400b0352006a070403c0003a694540c0510b9071502c466210100303103440d41d0202d5a01c003c2d0306059880840c2c81c8460741e41010b4000b40903000440c20110322105012901070300004034244810340c003000302440c144c1d00020842e440d80080d030b020410400690b02c001008115200a0200c911070f2030420b140182540c070300032242440c02c08089501300c1080c4000d40c50081c020807000d04940c800d44010410303070f071047d0141c209800f28800003035001504030144014090600140078030386109580400c90f00b6140d200560341110103800490030039100d6801070125041511100c2c0c2c1d5a08a07100140c20a80c0702c0001a081d48001c5903020300007002908010015001400b9098030003a83e4441940300d2a030580c00302c0c035010700264045001d0000000031803e510403d5112107003c1c04400103032586540c540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 412689928 1250 412688678 412688681
    0xa0908030708090c030d140c030913020c0d110a320703020a0f0b040b0711040c0c02010f080108070e091c050301090c03020f0702122b021014071103070f06 68
    0x1600c1588992003142c0d44e034135003802c001582a01010f420385405e02c980c00709609140e4140e005040c0c88007680401c0c4560300d008d44a404d0180400380c6050030140e1210320b00342c2d0152030714480c2c15400c004c0101d10f480b409600c0001140240c401900301c407429842540191034010301c12440800031012001d0b822034908081c1001c0380b140140c0340300b2244030800b00d50300c004501138221a801480e5001400300820050480030340000c0138101c1c42011441c064060090000d41104c0e04d000050020030300d10b041c0300c0115a44490000c1c000d011500f80b40c07281e54141080b20780e4490850160880101d221000b00e01c80784030401010b64060f001e10070040c5010558000185a60428030440810900384200006a18000d0007600c500c3d41404644e281881c1c1e80b5003c200c0c0ca100c0301d1150843c2e0327008080b01c410500c807d902c040910206041b000d152500107445c0005d1410b1120361502150a2030113405205200b240008070f40c1000c090b20f40420031601410915085100c1c0d140300070034450312000c2c0fa00c10003005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 412691178 1250 412689928 412689931
    0x16020a060c02030f120306011b060614091006050f0703020705100f02070f050f040902060d0e1606020105090d08040503120901060501030f0e06070810051207090e0d0f080a0908030708 80
    0xd50541e40b40040d0841045d9503402840f9031142600028800074000394403603d070750f010990720845204c9c549c4983d520b1701c1045a0440d088000111181440d1400904010300380a4000b2500020341d0806440c03c03800a0150140f400c84101e8180c0014507001454800c0110401421004001d44441c40001c0f03c0685140f0361800e59078098081c09070000341c9030003240344e01e0b01104e2014114001340b0036a10200002014000c100700c1e4000340602000c6805446842400c00604482008040c010003074400180250320690000c1c0840e030500040069803400030411100d0400e141c140800c00d61910b283c81c6096001e45011542408401000c000001d00d05402503030494078280c03020050700507030010910649400c101200310583c00b00d030200b054a403203551044e40c000c44080386003128946071800a50203003509004464107510401041c0413044151080d010030040079030003010700c8000e128015000928924840c3e0501c0032210000d0412040c1d500803e90096100c030406a0b649444200680b5a140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 412692428 1250 412691178 412691183
    0x90120150f060109081f020a030e01020c07030309081b040c050c030d050f0705210603010f021b060a060e010e28090506012309040804050d08040315020304080f16020a060c 75
    0x4c1c0000011a00b0f0301252015003c082c180e10300b00001d0508180ca00a944220800d80c10140e03034000410300c001c800e101030300c42000010090500c003803075820000c040710a203030048259600218440c540340380042a1000e02440140c0d0b01154446404005403002d02601200c0b4050340000616810740c1041c56020300e104001c4c881404881c0d8840c40c1c41207170507010b0400c3e140e2013a800d4140c00820b50068512480d8031030f00080011135140010103528050380c01c60b000902c0d0034109250815101041481000c2d0710030400c0c0010000c1a00c6e00080100e4203606100305d480c1d003007204011a5502e20a5210184030001c641c41011034600c0c0819080000d0404280564007800b83ca400410b41159000308400f0160400c1c2da2100c58500c1c2208011a02c480030300100c900400c20440000c0a486c0e500901c0c41c8180642d10391a1070f80d1860600d480c0301d4008001c150305940c0304008010000b0710040a03250305080000d80da544a11003000d00701c00f8012003481c003950005100d240040c60550088103000300e5403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 412693678 1250 412692428 412692437
    0xe03010605030a150e03090612040606030206040b07060608061005091e040b04030206071706010f050c0f060601080c0a08010306050a02070f110f0603040b0615040f090501061103090120150f0601 85
    0x20b05546211b5143d020305c103152a80044c3c10040041024200c080c040d400c180541e034005910740d074a41c000703402a8440c0d40180419240403d030305050000920a10b030040c11890080e21040c070301105d040b0781042e01d070f000e13103440303110b5120201d285d8140032041c1d949800c400309011501400c0c1401e045100f200300720340450041c8590700016201c0d034403400710048032410707021110b2215200c410054a140400100c6001040418010b403071841d50208400c0b408008404060425400c104000618000c00180110300d140c1040250049907940300782d040341180c1c0c00140000c0c1c01e0702d902110310080d01c5440c03c0034102c08003410403d010b00024101910543c001210038454005801041c40340a0204442c042c2c08548402d00084507820883c040d400c425401c082440d00d0280c940a2508001017241c200a0410b942c41c0c00501503250040d000c500d02c2c1001c2c600460400c03401ca070000346045003a008103004942c098041d546031080401814000b201d11500e4209907207080d9007510380221040710080e0009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 412694928 1250 412693678 412693691
    0xc152703021c05090a0b030703140c1209070b0711060d15090c0c0807020d080f0301080a03080a14060d0201260402130b060706020a0c140a050d0801080d0e03010605030a15 75
    0x41d000f1803c035803d0080c0030302107040b03681ca4810080d4441c0c000500c0d200500da00c1d06c0031a60700506481d9900c0c8204400119103845841d5100340994406006002e1440e580c0101e0080c0801e00151041d02c44180d881418a0b40350340502d0007003030040c0201d02d2411120740c14201c98022a05000b0f44200944121400400030b2203004c0e1404c88400011080c003400c404410000040542440b683e810f0640d4081e8122501e40f01d0b03111b001841540c0260f2007180c050700a50103010130594028600d5412100090701030001600c11569126030340c4001d0708a81c4603207511075150046900480c0c4520160100e030005c030b40b08081d1710564180b100c00449080344521403450814440a10710310502d003000a029004c40d0074100301d0b0352136400a6000c2e056000034489607001e02d5000800c110304030184d12414901404803d40c0515110f403910280d0718440c010302940d00d0043c80104400220b01c880e624562404800404507040464014241c980207a038150241224100c00e000390044030f5040301c5e00740503040000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 412696178 1250 412694928 412694983
    0x804031d010504091808030f070824010e03070306020c0c030c0a08250e0103030309020306100e0c0d09060507051309020c06072f0f0106060c15270302 66
    0x210201144180440e009000900c4101100d905c801e01c0c07801c0ea18214401001141c540041603042100c030820108901801c200e0b8043c5d008210b250170250b1000c01846581c01400324170120300f088800350b0b0400404441580b010380e0200300001c011a0807000865803440111413480c1c0314140c0030003003070207441402519021814000000011154400060a95190342c500a1400c0501140841254014001d40800c1c2c00100502c03650085100b61030026208520f4410325081940041c6505c2145806100070010b00340d102400b581d000000d045503698580c0740020b1701000b011224030107081c0c1450241003245158200300100b840090604c2405015a601c01b200d0040e07204003444001c0315000000030404190286c0059440390085c0d8140c00303080b50780305103005000043d0b5101003015601038585400c5070803013031040501901561502000071095921140079010601e07481404041d42c0d00581d8102504130541003141800010411210654900b802035031082d014500c0302c42010181d0702d0b1030a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 412697428 1250 412696178 412696217
    0x11d070824010303110708150109061e0504050c0f04030c05030f1605130b040c090f050f030a020f010525050601090507080a0e100c03050f06030a030206040f0c1203080403 75
    0x1c4516411500e04403a821690129082071880003411514821680082080d0000740086608825035400c18051513144c40380382015103803c3d502c00075811800b580c250400c01c4040c90b4070425200152404115622240c2c102101407040c001000111100840c0220412944250890456404404803406c0c402c02c0342c1c05545414521001c1c111454a1400402082c1003910540e40a1004080300240b00d01c40c00001c54123540036201031400040c101241404050b81c844000c501410064417801010141d500109641c0c1141c280041d100c3d20000c614122141e12840440b110100b10b1001c20b00c030003280451b220004100d51000300c681d0b003e08400414000d101b4030815228041039a122401c07034a076010b2910003000010b802d01d01c00d0282900d48d01d00b2031001d010f44002c401246e03500040a181c80c1000c419032260141ca402d20030341001b116400480d500040694100d5005105c0c4000c512242c074203903170081303010b501902c843c2406a00030001d258010400c10700c900d02a4440152000446000aa = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 412698678 1250 412697428 412697473
    0x40315050703023105060a050a090f0503030a050f07060c080403020c010527010309050303010f03021503010521160905040b09060603100f02090616030906080103020906060903011d0708 81
    0x2004010126604c0c800c0c1d000e50f00e06140d05021100320359210300e441d000071510940c00320014101254000074480e05103680034100100a00c000b098210307085042c0000a80c507031061242e02000c1200200c0c601584014030011580c40b80d03404541000b50700d028820290049808480960250041041c41031295020b42e0480303880018400040d80100300d00c00c81c10103441d000840950415a071034034050300294081000b58040c1c4400e0441820451451041042e0203041004c800d01e000d100380010440364840c03c020703440c5084107807404d1040b00c1c0c40c001050318146840320058615a0312440006007005641d20403070207540070320300c0c45180381d4030002000c3d82e0b43c8042d83d206402d03900145400040340c0c40c50380250081e180c840d8026140035400c40001c2d11365040500b0404944a81541070320405821003101345c001c12181c1485041507155400241040f00300900f0340b801008002110b03039040c0c0e0290320007010600300d44981c224203903100314604d076200d005001e400503034840c1c0710b22040661911035031078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 412699928 1250 412698678 412698697
    0x30a080f010e13140c131e021c02070206070f06020d05060d020916020114040b01080601080d02060a0f0204050316140103020c0c0f030c0d12091403190c0b04031505070302 75
    0x5141d8501644c649004801070f09142c40d2501030103c07074510316983d4200340c4441d11000d001c0071601c1c0d008480240d2001d000c40540b40f1009104003c5000b0881c0c2000d000030b0300ca0300782040162280402c1c004600c5510031540d000300315135001050841000202c0e400f501040c3e00050040009540d40c4040c0322003490b0500c0f02941c420ba4942c00103040707610004155140030240d10011404035442c039000a03207400183c0e13044902e200f0010052050031400c0141c203004000d440c00501c0082c01c0c0c1400a5201d40d07010300032005036a2103001030b20318503000e90111401010058112a2034050003045c1c2c140081841c010382003400b030241c81180403984a402551141c1031008042c1450700035a00c10031141040d0070900c2a054043d291031940b4035030310925216417090080c50b20401501c150240144110340c95001140e881602d4200b4040d03688000804000a00003081005420a00b81c2804065401540e020210507080007802100300302c0a4100100900d103192014011910b619209400368044c01c01407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 412701178 1250 412699928 412699951
    0x703120f02071a090405060604080f0307150204050114160c060e130203191d0102030f0a05060307180915050c27091b0d090303090b0f3303030a080f010e 67
    0x95004c0e00d00b03503001c1c5410140007800149813079a52441e460804900240884443c1c00c003245c2e503010f120004400121100324a00c0c110702e494201f8001a0414280c003c401031540b40c00308010760051600111000705580190b01c41c26000c1d0303101c10003025401c4008025024542c00707203148141c501540241c038011807080d02c1501881da034054002c0d004002801200c41d180c1180a0034940e001d00c2032000707501608080b01001170501e0800045421345d040601039034025480007808010300102070a28032002c5a900c40081222800341c2070200d00740c0c2c1040d18402c1d600d458a024000c99604a00c01088405040a8800450f9006141c00b074205207039140c0441e0007814400003c0c0c91a4800750300e801c0000e003560103541c140708140750104101e400b400c0040700030036504c1c595130342031107000040c0681c051007a0107100142d180103d0b0702010851500020000f00d0414001c402c66130668034000442c60300042d046a8a030703c9040b000900d00c0800382c030b0034010740c0b26200000c01c180c07101841061040c80039005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 412702428 1250 412701178 412701187
    0x150f0906020309060a0c0f0302010c08090d0c0f140d02100f05010f0504020c15190f020306010c020105091c06050a0b030a0804060c02010e040203160e01051303020409050703120f02071a 81
    0x284121176006160040402c481d40d801080040e000e80b03e03011045000b40d00000d003c000300c0d00d001d0108078014214819a9020031b18159010354802d000b0341d40c1c13550046113400d00b660145000310302416444040d5407980a80c000c0c0c2c003070f03495002601e40c00ca0035030104203002e88100c0c01c5617942190404c0c040c04c0d056442c0b078002800b003402e06800401e00500004125013210300244034903c100101520000021060b03040c3d140c4504096019001c803409010308118914282480041c00301d15007804028140500820841003540e640720301d2640010b0b24406440c1c442089142000c002e1404807910307a4203a1a0150816450030000344201107151300202052500e424070070165504003203d40100c0c1004500341c0703003005a854a0002d9406059043d0703a03114448034003c000fa00c07807084540300604101c006e00a070a020090001072078100e0b501900d00142c0b00016060140c02c2010301c0c0c201420031205103a030440e8281d80304aa06440c0040c582c20703602c1290700c4d080c1461842c04c00500366480d20a0500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 412703678 1250 412702428 412702447
    0x1050603061f0c030201150605070615050a240e0d080f04150507020f060f0d050a020c01050702030318070f03080309010b1302250503030c07061401150f09060203 71
    0x1001580c002000800642034a080c00030011002102042c0d01c2000942c0c51801c04105038090140308038000500c0c260441150601c0c900030424010544041c0489480d9894041040030b80d4004002616018000400c29900d402d211258102001c20b400401c2940c0d03001c000102c0d2181d0585c01c2c8205008000f00d5501c1a2344e120840240c103c2424608054401c10001940440c2c03400001d128403155241c07640c4582241c01089000480e08152034083c2c802080041181c0c150340381116040c1c0441600024a5116820030340006d001c3c68034512003961070642440201c40e0004081e62050103c121643c3d5044844110715407500d403148600b01c00c1c0c0d28032000500000320030202444d4030821920000a83c0010600041d0b44151409a0b060b911a400107001000c200501c11040e85540071420340703131800d0010b940d4290f49100046c81001c10348004940c08d02000807a420011100c11008881041546c40d1074000b60b043c9043c100c4c1c84003040600c0400180c5a000300c3c23002c4120740381034024506180c181c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 412704928 1250 412703678 412703689
    0x1104020307021c020304080a0c1d270703020d1a010b0a0c03050304021801170c06070203070303030902032118011d010f14120907210f03110f010b030c040606080105 72
    0x74900340013503000500021541d1031082010706c80d154010340c2e1081c00c4030300d0201c0c0d030614800c001c00030680e6078059004015000500c0d500302a204440211000c01660002035603504101c0035400081d0f000b0610341200040c00b40724a40e0042c101000c103400d42c55a46c2e03c803004ad1462041801a10100d040002c800011038001c07006540d0003030015120318001100c10310781600f9003d098001b00700401110003603005489042050b110400e41c10345d0070501c3c200742c40e0001f80d9582d82c2444010304140d1120340e0380c01152014048000c644507000b441109040039008481055001600c501180020325001084107600c640310079002804800c5804081070700f00c600444000c4144483d51043c058410b088a215101540003810001000d00410b0365904002200c1c81c2031480303a40c491303c0c42c801d00c100034403180700c100c0322540d003460751160303072192619079520b0113607020614a00c22422501515084824098040d00804450320049096039140d504076010841159043d000d914000b400b000e0040c0b100b41400b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 412706178 1250 412704928 412704973
    0x4030c0308070f023f03040e150d03021b010305010302010c0b0a06120506041403071203020a0c120f030f0203091b032506090506190509010306030b090a110402030702 73
    0x154404140c2c60702d0a80128201d02d10110030b080301000b095102c00c0e0f00038607552800114200300c1c1c0e000c0c511707445c8200900307603240964040d2040125516000c0752040242039100540321301c0291094000c041c007400d02946800e84603480101c440f00c0d94400740b005611030300c5118180c3e030f4141c64402500080b0f80710440703a8000101030b10007a0f03695060114101c419030500c8140c9a100d02d00401103842d10b40b4040004851001441c4119442400642d00040042005020401e03003403800503222101c001088500000101001d40a0b0310446440c002040d44500c0c04040d500c6140c0342444036440400005080380f20807110020127030041200400d00c10180604030759428001001c84502d4a4100700ca40b424410025060002c0e490500c03080102c60f410003210001040c007255281c2c1042c074041c02e0300842c031010100d6041040307000a501d600c1c0d80c0c003a0380201e01030750704020702251600c0c10351201075030f81c0c82c1d10070155100031810903103e220303103170a0080328459040d075409003108800b40814401c2c030b10034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 412707428 1250 412706178 412706183
    0x41a0c070e13120c08040b041a040302100809010b0607121b0c15020307020915120f151312050301060909020c0a231002030105090a0e0604080a0302070b010905090c010504030c030807 80
    0xc0028402c008a045400904013410100055036903a6180000c1c01c1055039444427105400c92051000700090703501c254030071050320303400d00b450f480640c0c1d6884d92500403d402d00342c69a02a42c0481c0345010f001d07100ca0841d84120894845d1100c0940003101341000a44030b40d001404460001307024800c3d56044140303580b5040c01030048909100803540003810030b482c121841c0b09c616100e01180d242c10b1074000c8200468188000c060001d000b2403c01e419190f40030070712400c00080b0742d1030105101d035403007020350100190400440c040e2821900b80003400740d8000e115840000d1400b0340003150380c1905200b00e40d003941c80407004140c02406c4e6910031001d0301d0149141401a0281070118161010500000030402c0180d0b600507929810b12040203c1c4204c0900320787c80346807910315041041d0740e00242c8150419000108540c07203101c0ea05080700640308103100241288845800000e6010140e04054001d8400600382c801c0103034244d004480782e004a01c07019128880380042040441c0300d90000385821130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 412708678 1250 412707428 412707437
    0x110c09071d03010609090606050a2d05040c020f01060b04121401150308090301060b09031b06250507060206040503030f060a0914060901080708031e041a0c070e1312 72
    0x280000e0002e401c64200e0b13404481c0080c0c1340c03800401089081d11540004d801c003100d402c90058103040009070044654190710580029081c04819071b843d03149000001400c00801c1800700204001c0d0083d11108006400d08a540c200617000c04c0ca012200151002e80d0070215001c20204655101e907021040017002c002d2855591f840304041c1d540200034141d0140d070060300003a0303075109500709150842c1c41c0b40d84001001c02d0305002d8144030f0f940203c0e0614036160001c601049041c60000080d000e8461500c00140701290619a41c0d1605c0d20210b140100300d00520607100102e5869100340d841701c204503801040d82d082000012009000100b4080c4c001d480944108026921100d200040b1480ca00708244100314140810a40d45420011207025000080240010918107014251b4030f0017500c48040d207a2440304101c3c0d1451034502c09a41c0245842d034032030814142c4580300035200d41e11080d00c00c0a076001d440004500b0001600c02103024440d000301c1950120707040c0e1140182c49010410240820 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 412709928 1250 412708678 412708727
    0xf010e0f03030c070311010302090d06020315041e0621120c06020d02030a0e0f1b0123071e051509010e070608070f111b12120a110c0907 60
    0x545080010344040300303001004003201825801c2c0086c3c03011a200b0300e0380c10180100304009041c2c9554040092103980a100503032245c66040103c490b12503100d03c1d540d0010f24181101c0001d18504494039103440451600700105519529105050074851000c66046003071942a00002551202c94903d0f0700d02c10f1901c000b41382c9181e6240400d030380c840700c1020401da130007005200030440c10f4442c149038000c107680180310a00c10041000e8039098081d03002400074200c000d100350264041c81070308000c990340b0281e05032000000b2003441c240381c1122400b0354443d601d8a5903404803e54000c2000030260700207005080e07444a13409542480500203101903195500d4820715845030108011200180146031111556440c104400500302c0d100c0401140030050300e51450711542c1400300e00000e111785e030040f008411306101008101c2c22108410002c20900c42e0200040701105814040d095400403656020318451000c0280c41e41c80c41d1b801c000d60707807018040700030603000b41c001c0c113000c07030090b4003c484003091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 412711178 1250 412709928 412709959
    0xd020f03100c0c030807170a05090c0316031a280209100f1103040b0313030504050a14040f0504030503070e0a1703131d0705090d0b0a1e0b0f010e 64
    0x2d58004000c40404148900c03034070000c05070048141d903400301403441c00c1d040c03003142e030484110f41030000740541c1e104503903903000709055103000c3c00768100842d0040d007103885090070790300c8d013810400d5103100650700550102044504c86050014280c0694281845000201c48001c00c28401c2c00386441c80031a07442e4204185001d0380c0350310216082e402507940740c01c0450003c2c000c000d000740443c15007403c81608200424801c14411400b500c0d0000c09a422140064032685015640e501c01d5401132540540356035800114003000e42d10020948500761014050b0710030410014056803010785008001c508144000f0310003d11600d02041048001000d0031142d0380c0c3c44002400e504c046014103001354100040b4008200d660154820007011b0180b00c2c003100710000c801242e101400039100404102001400301c04590714540c080700026040780952000e400d10500802c010702c83d40c20150b4000e5640d054100001c14103106012070310401a0595070904441c100440e400b41c0300015841e0b000e40043c004566 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 412712428 1250 412711178 412711181
    0x3020c07050d0b07080604050610030e0f010509030a020c0f010801030605060409080c0c1206010e07050309030d0612050c1002030313020406080d030518010507092309040c0614090d020f0310 83
    0x3401030040d1503010040c00c04c82e000814200d0000e000d540614141402d000c42a1030301c101d55400540740c0e19002695404040050b82000e501c1001d41c400303982460203001013210003100520b48100c1e036408a4140c5c4000b9414401d284c0b402d10012030110300c0600041000c070740c6680006e035110b00c0003880040d0040d11652030740e0103a00f045019540c2036000807800b20b11424031101414a40c0a02402003a180d032403c00c940c410304d04001d01c0d0328200940800400c000490400c00d030b54524a05184c140000c2d03880c0d00a0707900c01d84640805440520414090300981d05040034040118181ca86c041d40c07071559104080104a445640d04a810556640740000e01003002d005842c8001180e40c0d021a81e820100c0c07a0240745411100030815607458201803244403901300803000b0803180700c01d007801002416035400032071080c1c1c0001400c2e00210060204000c21144001d00810b440068542504101c440c178500e103018040c3e58a0780c1e41100350305c8060005032500c10f07440c00e4400c00080488161241d0b0300d03550350 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 412713678 1250 412712428 412712449
    0x80a02070606090e150603122212110414010603020313020909160f0f050904020a1203170106020d02030304080f160b16111009140703150f11070303020c0705 69
    0x220050f5032004e80c1000c0850520980b20f050f0070150594085040c0a0b0009403200c0084448038900417000072201c0642d0f48040ba5103002e40301c425540c2c03800541d100214802e000741c1c50011a10003520042c0310080b440c252240029900d030410036031880d40e003007000c190001e60020b81f1313090441e1805000440140d4806449a1081d103068001e000000d080b010164150715094008060301100000c0501106100c03070441c0c02141e000b200c0190b1103460720300208902d05901c4d0444184860f15030300395810b01d0303003011030030340244080c901c0c504940c2c0e641c620490316001440641f100580040020030b0126545e000a444900d14005456160a8401411000d1007064050459641d08c0358010801c480c1603200d4180501441814101c1d114514858110f031141000c101c0130a00b00e40d00c0a41805000103920002c1580c4200b4003100e42e501e8407070810000ba00000032040e007609081a20392210503405010701e4001410262000d03051000654042e4080e400101d400600c030302c00c40d00005415540c0c50502e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 412714928 1250 412713678 412713689
    0xc0607110c06130f05010318080d140f1f050f06091f26042d0c2d060801260105040c0302040b0a030c05060f0702040e0705010f020a0c06080a02070606 66
    0x8a00e01c0ca80349001080d03480a900c402c6c18140340231028403040e00101222a5800e0303222098954a0490210040040949560703940703800184908110000035a00420742c0100451103064800d400c00f6075010780801d9003400b40c5904000c00032000307002424548064250540c00502d0480304004035901c1160403201e01401d80000f0701c22850928040d00c1200038402805054444a181d928094503032910203040904040403845a04521090500c0c0c48001c0050f550391021000e1591641d807074903485040d0070800b5100840c1da91501c41440b5500741e0244104503001030f00d403a0083e0303103010ba000c0c0c00502001421810086a02c0e02000740e44400c0c800c1511617071081c0202c0e0320391410b50051108441c030310920b0700c0c020000c3c0e003003d20100703d429049404644013210707010395801c20440000c05034001d0642c000e4009040034100681500c010406600380c5034207a80c0c4100d9030b0781e00b03c3c08030380e44d1140c0500a400b4aa000324180b10342c80c40361150a6001d40483c80152401c1350031741d594800c464096101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 412716178 1250 412714928 412714957
    0x9040e0f03072405150d061410061715010c0c090e06010f09410408030405010b060403150903030905101a04020a051611060417070b0c0607110c06 64
    0x284803500c985100d400e00000c07043c00400007441c00501d2129030b001c071078800e28802c119100041c0208403460700065641d0744008180d00e09410510380000403482980a02408129203040c0c98061104202445d84a108001c014500318110000199a404040d44003540e5180c011100800c0e0021140a800d65618500b0021b203000c1d850a14001070b04500c541080318030b41d04104e410042002a000282e400643c0341c039203d001448a2082c00d00a62880b05c100c0e07071400340f80300400c02401802400b4601c42d5000e04000d1102030b405004208142c800c03800000c101c41e440c04449840701c0c805901500c82c45109040000358504140c6840e886c0c0140047e030cc1c0d00254844a0007960815800b01800181c0780598003907003082c141090203059405800380c08651410004030090900003181e0603044044005440d860351242c803000105003c281e4612403403030078443c00000155a502c0f80ac101e0300d5080e001d0b005840d058907500801c80342000302d03811305070b100c1c807407030b4000d00c156500e140060000b41c204586 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 412717428 1250 412716178 412716203
    0xf090a06050901031505010c020f042007021305010b07060207060f021b011d03121b0a170705040617040c05100e0a150c0b1306320103020609040e0f0307 67
    0x50a17158110f00a040d181d140342c40404c0f450344c0141d0342302e04580d411180040b002d644680818020480d0001c52512110460300b241603000364440109810707402500c0c0d00e04c8442e01c0b02e2510064403003e2185819012081014801044095007d0280684100d5012a503407056012500690304904088070304501c0007404511114002d1244100080c0a90320724608158a20002030301ca01403002001c1c0360b00f0140b400601402d20780003c0512005144031a25281c5600510051502c1d09103c540c0b02c400d20204042042e13140107205036000c855950359407442d003610348650000c50715070141040b920780110640104c0c060f503444180c01d4076858660703910041e0405c0c2004000e01d5900590106000358945d166440072103a10600e11140940c20564003801903d840d0a00c13800c56907400d00183c9000e04d4409490f220b500411506204001d040203e00501540106081c03004d070700038840294081f400308a198070604254000c2e2f110b1001e003005840d20307083c04c008050f00310390160008a440070301c00308 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 412718678 1250 412717428 412717447
    0x3090b0304150e0616030f0204050306010608010312020105190e03090a060509030d110c060a0212070807060b03010c09091e0e011d060c090103090f051005011401051c020f090a0605 79
    0x10864800c007100d0703c010300c160300b0b041c00c5003490801d900c00345208042d2074500c22405070125404881c002c1c403001e8112032607582e40300d03001000800d0071700040f0742040250780702422040c814001c0c0b80c019002d4940c207011180c0e000d008a002005809030310000d0740001e1206c490140c0c0c07055540c800400c8181c0703c041c0c2e40c000382c604050078500b4541441080c01070003015114080701c00207032102030100980f4070316a1003c0594060703142011000d403800050034002004030401c40100c001e015214412042400341d402c03603208150913541c04448800014a884400300320440080c2c100d181d802c0c06824600c00706490005004040e0740029040580680d11440380d241c4a410b9220102410a5550050411800c2482c151100b906c03c80d5a428101500e0300391020610801e104590311065000d4121540c046588900380040c140912462013280d490742c0c035200741c1c0e5001c0c2e0204c54605281603041c00d03910000c00c50f900002e400c40a1540c6015509215200c882d03110010701101070207007a2161504d0707030b1565 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 412719928 1250 412718678 412718681
    0xd050613050f01090b0606030a110f070210030b180403050c0106140a090606050412050106170109140c0303040e09030f211012020405070c0605101d010e011203090b030415 75
    0x20100940342da0b142a103000041107600c00021380000781150303441d81d030340c41c2e0100380c0015141003144a550b812002851180d42c4003004000c02070340d882500c00300d80708030564009800726240701340140c0d00a2482900f040202c25000b1140360711500c40c0c101681004850000f1a084608681040d481300500e20003d01061070300c00c92102c01440040c2042c0021824508002d101d03008070b11440301c03220154070007041040030a4000c00064070300391a030710303600d8801c6100f0140a040b280708240c401982d103100008140d81c0200300701c00380240240045107841d191030350104030240028070114607400705200d12144204135100900500b07583d510703a20701d880c0000c02e407035210b650090440d0303901c840f496004000c003201c00c2c3c001c003004a40440d0b00203104c2d941c400d030580c0d95032000c2b9002032200340f0301742c10001541e1424600b4020380e6118900030101102d14074011450010a006684101c0c0700400100014491036011000c21403103460141c044a40c3c0e60100c105030b0b0000d540858007039440c111500780c100305030f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 412721178 1250 412719928 412719943
    0x11010c09062d1416030e040507020a021e01110a0305220305070303050d1509020310090213120309080a0c06120903090312030b150a030c0c1707020d05061305 69
    0x140c0354481c104010070b4449210301150010060002200140020081440a481d0440b990074807400044105140081410348150308980c132503403034000030030003c510001c0e402144a602a21071040b40303407171003444c40d0044c0c500d041700c83c10032091618018010409024043ca01440f98031840e858191900d50351003440300940da403850b1061010710070070110300006030000807282c143c02c00540c1c8414004071200503103003050742c1e54100c088445c4000380c030b1362155008620a5a800440c3c880c2c00d41c903440040142d1285001c08000781a80c0c0b5400c0c031680c3c40c0c101c44414140d02c1381c14a03603883e035a1284101e080180d000f9064803040500c20741080465000040e82d20311011400303003080191030300d0390082c0c03030224240000751007586921310302801180690b20210300b56500410700c9149100e00b2040140ea58454148000024101844400258020003080046a90280209860001900310200075400c028805e1303034010311500c502c8004c0703442804100e0140708542045203040c107160a0061400c0340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 412722428 1250 412721178 412721207
    0x902060c010b2e0c0309051c03110a03090e06010314040c03050d141b01060b07050106030611120a09050c04050423060c04060c050304030501060b030a060504050114060a11010c0906 79
    0x244601880c809003e512042003211280d0624012050650070100d071400c1941d002150090240551a0000404a0340f40031030580301390b07030701054503008000441e1915041e00c00100410420201402441c250036110780d400003040c5800070355802c042c007500b0954030f401c1d01e043c0c414046c03e09081c0103100301484200d02d40e041038203091440d2100005c40702e49a102e0602440417401c146e19072101944c10030742044005001305000948c481e20181856070080440f40300c119903003450020741092108002050b5000504880d000403e01d5680344e0b0f46d58003500b0345200c00c035403501610201c4c2c00b540d0354620400c0d014500441c105400d5080c140f843c14181c4006c0d0b1001d024139484002048900c450a408640c180e415501c0c3c0410408106c0c07074107a10314091604014499420040c0206041016001452040060b902c083c04040c0c0e03258144001c0310401e01032005108262800c0034010304043d401403628950b1864120440152503000508503400c0f0001c1c840065854241000260741c4191202011031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 412723678 1250 412722428 412722469
    0x200102010b060d02070f12020d02010b030c0a210602031003050606010c02060a0c021302040b12011401081501110d0207150509030604021203040e0703050703230f06040902060c010b 79
    0x440680041d40500903d40905012600002c4940402c1400811031104560041440c3d40c01c08416602035228100050820015864040100d20b10b18001401c01404080a0401e01a040c104888040c0342002581011038442500e5210b0300020340f24070095110b1600000c95018640c2140f0740700381041c03405060039040040c5003082002690301c03e41102c5a0114034140204d0700e005510124001c0007401c1e090b29541840072a0000d0380ca508100105000d070b680b42d28090041e0389034400c565500c141036241c070f4002280c090001c0d030480803141845e116141d05041c40c5034901c49480105141c001304900031001a0860b07202001420350a8031100d0740302c402390420f1410704040402095403080d004001912600e48620649210030301403040303401428890408818070310f040f24018010f004c0603500100000c0c940b900305400001e1800c055010b1110140540c42c20703468180300480441c1002d85407652081c6e480f281c001c0180d84000003460f907550000d0010500044d150100700d18540489072a52035603 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 412724928 1250 412723678 412723691
    0x311010e0603040c0e06032e05060109060f0305060f191a071a1e0405070e06090f1b1c0902150309060408030a090b040b190c052508040320010201 64
    0x5a42015139800791041c165502000355038607000689400003009144000782c000a040c0d0180e400e034056801314403810707071b0070a00c01d54882d400111540130891140f076001034412400d2a0302207100342c004540101000745089400325144c1c0000360f0094800c0000b02560584d240e04000e43c144150108012107050401a400c03d0000d46a010710107945552003070502204600280700c040481307030101a20601d5008200c07291405142159460140e8010b0001141c0c0034030002c1d00515141150350310800526841c05010b44914400c1c140500b00e4542c3c4a00d11036040c40020408e01074050f5060003800300c9140810f41805e580188007417107854441d00d9042e880c00b00204120703d00005036054010340e0105500d6980d64030a1a214000c0415180c0189000301d494107202c14072a100c4610340c05124044825045012112000012200c01101074004a00280041082c41c100804000c5100c40300302e00c04d1107010940d40c0c0d0740d441d43e402030300200c5e4a440c440b80c00301111040300b41a66801502130008000c078 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 412726178 1250 412724928 412724933
    0x110927360120030702151e04050102040f120b0906100e0603070b03190b040e030301061224080c0a080c010c050717160f05010e130e0a12030f060b120c0c070311010e060304 75
    0x1511f01a03402002e249841c0022030304000007541140d0080c10480381c1005440d0301c40d0507030300c2c4c1c804050100703598002002002c260282e030302140040c020030070540b6122640b0b24000380294039000042005506000346c69000500103c00ca00441c0725030b203000595032213040200d8076401215032080d0090b010318600010140705940001c100c0c1d0565540d420040410760300b042410020340008000116041120312a0060a0580c00c25500581d030f0050700342c85800c2c10710380502000700c40e944a4222241e005150b120100e50050324094043c6026405451003039441e02031040a1300111040c41015034041a00303005c040400f0100304001e0413031514605502490701000038506880e500c0c20701d00c00c00c2c540e8059000194503030310509124881c0c40c15034038107502c0b909200c54031900c41a003220119007800c1808441c083d140c81180141c4c0c0e18070304140d080c00844001c44406040082864010b200300300710f14410f140c800c0103004000c40c401e02210364900040702c001460548058a124054842403090000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 412727428 1250 412726178 412726201
    0x3190509040c171f170c0f040506030c1315141207080705130b040c020604030e0a060503160302040515030103020114160611092736012003070215 64
    0x4001300d0400c0900303019801c0d02c41040c03000250b03911810159900d80740012040c031021580c80d0f4062030880700006002c50040600c4142c540c00c1315001c5d03154020141050340d918001c0301048a044244600003025050903003104c9000c00e4a07004818692310841c0c2683e05450203521140c03c0d000c0a2000d80740103807600802c960703113029a00810348102c000c0403042001000685c021106040c00a2050208000600700a91a1314082d141036000a000d150520820300b0982c070380900315181961524135603514066690b5520700000c410b54201902004000f0b510303a100d030050b03080281c00700150b070b940c0e500d144005448440841c5001c0711b41c64090003218922000030308003215590308010040f44014410b462441c140c41400050340c0e21681c019013031544050601e000411041c80810751686035282c4010032005110013803210f944034444481c80c0041a11040c2c2e07110440341c04480003241d0031099084212084911004024440ca0040b007001106a070402c47c08120000711180c11300d087c100841e8518 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 412728678 1250 412727428 412727431
    0xb06040f0515090d061a06120702120a0c060b0a030501110d14040c0b0d150603020703030b06070c031b080a030806100801031e030e061305100905180903190509040c17 73
    0x105004d46d203101303001c25806e0040e02080c01d518000e0401e0780e02c3c215681141b80e5400242d0304580103220b000702131024240340e44210b580c46456a12400b0f0142815540c010240071402040d98000b04101000000103d0902034810040c8003051000e890360130780410031003140c9100c44500c0301c480c2007500744004186000f02040c141c030032000f81280d440307180f10b41041c081d0140e01030348140c01400c0b502c0001c17050380c140d000d045528484c4e601800000550303800c010840c003460f400605158200401000007070810030701c2c0070b4455400f00d050f4046c99660082c0b5414031084460a4000c5107201080240d40d140441c1c0c90303140740e02c0344d05081801d9411500da0002900c28004003014070340140c803410081c180180e80f0803c0ba0000100850354480c0752880201300c80d02d240c82605d0084400b690741e0340005000d15030f04000c0d11400380c0880c00b070036001022001c0c00d10001d8144e04d410302040080245400c2c0c2004c04240b00d0036079803100b560b03404148090001b15200316401c4401c2012080c071046e040100d004546 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 412729928 1250 412728678 412728683
    0xc21020304210c0b0a1a06030417070f0611040f080f2a030703050708071a030705090d06020a08090610080a02190b040e04051c120f0b06040f0515090d 66
    0x442c41d415101c2655244402c0b940682200d807102c0801a5024040d00440804170f400c0c094440102d28110a2280b43c1c0000d82c1d00034100039038400b902c0c0010b200907000e401130b9402012074807180f40140e00e40c00c045805040c20080c04400001342840380c40e0400e83e40400030301c0310740001c01001c020a4a90381d150140303a642d040740810b0301420800744910050400346804002015a0f0703c00d130390791600b03560b03032521741c0310b812024040d507400003420103000c072000d64510303c403248070902d10764400030101c4481d030005006641c402c1600c90081c020407014405490000302503100c500f15410a103462615225004010618101ca076441c00c0c4688400400d8000149506403003a40075440340b140c41c1030f0505900d400898410101080001c0e4245841001c2801540160150754013030641070301032b81600000b85070301000f1814000300d007080c040b0107912460b40d541160000050310006000064029440340c1d101003004410401d080c0402c4c036000000400c060b41e030200e01490910303408045580c880788101d02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 412731178 1250 412729928 412729973
    0x1e1208150607020906190f090e0d050c0601120203120409150e06061c020f27010804020612072f06090c0d0f0503040b03040f0308090a0b150609040c21020304 69
    0x40d800e00c6c2d10390403088018241c14580380d04c1c0e403912210340a004088003641c4d06401d104280401c04072070f0061045981740400d041c00703040240c0c00c0c000700406003401c3c3c030030407a054030400210300070f0046204081d00c06041456008612204084101c608290482d088070401c400008144031080d41d600c0b0440391064000e22800f1706031440c0801101c002e0103a038405045000c0009564243d0400740040d04481c80031050f0318240741c1c41e0600c01140d0b400c01c1182d0094114008002c20115400181c8091764040c1e8249000300510091a04d601202d40c8100007030241131500382034400030004140400350344004904002c103009010700002488900b418640a0001000e80b0001001e00c4014400c8270040c1800040b0140ea90078240381450106801c43c100f074001900080100303140610206100103c150004500f04181e00c0d040c400c40d01001c07040015640c0024200a4045251994043c8000100040c4c80c0c4150141e02c0c8403034036a03405030940384076510764810030401002907200b59041d001065038688 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 412732428 1250 412731178 412731199
    0x5190e01060e030f0d08040c080c0604090e01230a2403030e011205011d0a0216031101060e010f0e010b0a02030d0b210c01020c0f0109031e1208150607020906 69
    0x100b1300b01161050200c00d1030265014a410301500281d42c0d501a5205001d01c42139103540b820b01507211182503804642c81a07003008100005a80c580240ca14038007050000941403107202003080030706680f40f881585480182c0c0820001d04030520610b1841c001c0c8800624040881540403180d001e500e000040a2000307140700f0052507407003401da902c0b101a145004002c256100d82410341207010140c0044100100c003400110058268000d0340c0c170038160409056080c80e82541c0540c1c0603215800c406081c1e640c0c0c0d40c800030709000c0080b0850300030450510301400060811016580480058000c0c250f92942001803541295000048031030900b4015030000d1036801e482e00083d0440150030030ba44800200c003c2ca40c03a8108041400b00e03510301c00360201d81c5000f02d02414092000e800200c03141c0480c68880d420404200c2040c95a005402800058130140f4500e684d52a0040e01105090001414110400460410030341d01c45410f01000ca407070604002d00780c5c0c0080d047e010f0092145018025850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 412733678 1250 412732428 412732457
    0x20904020d0318060309060b010903030806041a1e030c010e0306070807020c060f0a0905090606041202031905071d19020d110d0e070b03061c0503121005190e0106 71
    0x1404503c003041519a0f0002003503031000c0003406094244025074034107244c000044001e41c094a00c0f0001c0303a41c1620740318001e03510070381080010010440a80703400100c12003208103035034810042030201000c6000c5514002c200c44141454a403429003614140507402031040c00e03990b80041d09075801011440e00c8409950ba4080487c10070809105041c0c1240b008500400000c1820016206211450341e811019695034402c110700050180e07804e94106034204000d0141510040c10074103402c1c00179007120b481c0e44d40c4100e01c03884c3d5020850103646a80090304244845906c1203104201c000c548008004c2c2c1d030410300f4030001e07150402c0c011540030f0b90740001c2e91180148660004414207540074403a54071110302d28021405062410901c00d540d000319003012403139100304004d59000304070282080d02b1014600381c20815040d8000c4c4190b4580c030092000001039869001030b203210f0703010707540c2810040e4500750600050b000c4103403604a042c01d0014040c400d450f40744c0c00281c1140c0ca1403401c00070091141 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 412734928 1250 412733678 412733687
    0x80d0203091210050c04030210090b031b0c0304090b0307080325060b15030702160b0724091203110c0c090705040801020f09210309090a06090f0b01030513020904020d03 74
    0x4030700b00f03d11241043d04004240382c800000e04212802940d0900f14100b6400044510740d0380380c0a018205403092000c556002c125000030501084441201807605c20090255895908107601c440c006684a02001b100b82c101802004011b0940310000d50602220650320007181003c2001c401c142d01821034898148040c070b410800c0c80102c09030989610040082034071905a0045507000098410601d000615404542008049951104905040c1840d0f661007a868020b40b80820000e0700806015295802041c840c1c200c1d89840781e41c8214009240f03450107400e58840c00503110003070b00e06002498400e80c0201d000302c110141110208003d5907001000c1d02c00f40180e400c0103c60f5031011698141d12149a8001d002c00101110903060b03003603215450340840190f4802c059415001031000e17020a04103415610b030400e86d180030100e400f0392988003c00c212034200d000070501c9615204051179558041c402c0766007010051880905881c207031380120700c8101740980020b004040ca1407d0200b898400c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 412736178 1250 412734928 412734943
    0x9060c151d01051f0509070e060a032003070819060b0d0e0f0d0f051c0c05070b0a0b060403020f0414070207060e0301020403110603181213080d02030912 67
    0x2103050420400444008105440a006692030100d610307040203c1c0f403c0340c1900160703102d10460b0041810182c109000d000c1170060140c910001e0242d0000a03880c0780d0358003c00340c041e11121750b41c0020150918101a40351024202c0c02002e40a0704000f484a540e0780580ca490b17200c03041c20407411464480c180307200000c1c09c071513125090b4010081800c0c00c0ea295a0b13081106558200700c200c030016000d0412030380d1180e21700c0608001140c51160a5070156002e0405000070001c09590360186035400c0b41d0080030f5400c003294980020342c00103030031800c00580c021400e4105216210070031203030074a1000b0810038440d5000280c4907130204101a03145980e5500410400e400b04420302034181414100a0340e50400b074040c0c1e001003010503a00001906051081d40e003103e40000360004440c2c1c20740b050110581c8040c040740780d00150442182c0c20b4110400c00309000c4420f00250035a211500518a641c004940c0c1068040f03030022608110781c0d075030010655007600003c80d03544006c0111405903d02d442d40707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 412737428 1250 412736178 412736213
    0x902011101050c2d071407050303030708071b05070504090c170d020f01151a1317010b190317040f1503140708010b0a020f19061104030309060c 63
    0x801082290764021680901010341139184c66645609007212044070492400d510850b10740414440e44000c0b581600190422000c1c000035120060345480220f41164021144000421a1042804003050b4131690b086010307c912116026000b00ca5034407961520f1042c81414402d5882d906510144916840307614004e008040d07940f0090800a40c2041d102c8449510100150080b0b01d03580d16000c0b418090707500c0c0c03070381c035081e003040e80e1030400c1040400c0c3d000d203070700704008018140604141032841e5006ca2018158050042010500c8801c6050950387c0d800031881c021080c50f9060b000c0c3d041006c62005c0cd1701d40c07105003915000c0e660b10346280540a564400c0700c15076a404000902c08c030700c1c0e60250800300396580e010701031080d0124520603c84420f03141d00300010310300001001104400e17009403c9488017403055030f030850503221205c1e281c01017901d18920150310901c07450301008001e1044031855144190041c0c101451510007401c0c0341c00c0d500c2880e0501072140540010019036000c110350004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 412738678 1250 412737428 412737431
    0x7020115030606080c0d0b0f07030f020307091523160f140d030204080303060108090c060d0b0306060405101503110c0a02010e0402040f051e1002101b0e01030902011101 74
    0x1c0d5282030110241800c2e12442e40749001e900b54070b0340e0a08241d03000c1c00241d600a030b1442c00c03586a008034401710341402232200b400c0680d2107840d45d10500c494001107004010b1681d90100d905c3c01c24411075050024000702d8401e00102002da004506900c06c40b0301d00780d41b04030401d03940700d0b80b06880700190304490740710040102d001002d80c2000c0007840042840000c2c0804101c81c10408048403d8049100300e006107100b682c018000100550712921070142d2000c029800c0d162200185004681035820007140c4000040d01d0300540802400e0410a0940c0320034212803d10003070030315880035500008107000c3c0007010320b105041405a80d0090b003290b00c0a4864081c4507599591210801e501d9418941d001ca00140484044007500c0ca000d009480542c6e200352581c0c0c0400c2c0c42c020401803002812903200c501e0401d5504040520350782c6038050340b051041d0780c028200104900303400c0270454881c44003a0440e16548903942c410700b44c0c40346060b10307244420f08001070802d405000503101d111030b0041e44a05507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 412739928 1250 412738678 412738721
    0x3101805060408040602010e1605040504030e130902030c031b0108150907030515041e0c031808071b080703111306080309040b03030301030f0f02060d0c0c020a080a02090c03070201 79
    0xf0b400001c0003244c40075402001091b201a400c42d86075a820325581458042050060200740f91591080d0742051013800d103291031208680c003190900308609840e072100c0355107564500a6040502c56484409804c40143c54080600f00000800c6800c1071102810400c4a400298418a040d0a0340d010588020617081c1149801340c0003d02500741240d4031208070b171000e030540000d03080c00d0140c44408550916035039000344180d000711004000f41110f1004060b200d0042004060000880028030f5005a20300c5a407040c05007071040041c4080940110740c030328112000c000841c00410141c0c1601d6020000f40d0000c00204000f610007d46454211000c628009000035080030010041580c244241c0d828004001c25404040d00c0c3e000074030000c0d00040e8020400e000050040c407520407900d10040c1030601300303012503200f0411561040c000401050392403095506518112000030000c01c0004018016180c2030790101e038084501804418144a000c4007060700c2c18002e4201800941d40400101186c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 412741178 1250 412739928 412739933
    0x1d0102070f0c05060703080a1104031e03030b061204110f060a02010c0801050a031109060d0512071716060c020f010903091e0b0301140102070b0406030b0307080606031018050604 78
    0xc1d860706960031a041d21458100050b5424490283c800d9550140c031041450307610800001c029141440105a04860800c80130000402d12802c1e01050241c0080f120001d01700c40c0b801604450304002030320f00c0f41c0c8007800b2307608102e070707088030103951050f4030210031500040300e1400726040c0d24030700000b998802804100340214550551000c8980311043c0d440c03402a9070307a00c090241081e01030101414500d440401d003206810301001d496084840500b5407a2400d40b10b031107190409841314811804240b001400c5800d00100d00b0910207140b80a0088070302d01401900b41c0358848244000003896103842d0069804003074021302c007000d61f194401000340000b654901d0000d105034841e00401c1c8520300c2010030340182c100d00b0780142d001e44210096480ca540d00340300210701c08030b5582c08402c0c11842040004a08040d0700c0c0701400040181d038501081c030313030b14001c101410700e2440d400c8600650f0107902001480e0340d00281c251115040900e0001d44000748c000321040ea1020040003800c68404c1000f44000c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 412742428 1250 412741178 412741193
    0x61c26030a05060f010e030c01210606050a080901110307080712020d140a0507020a080c01020d06060305071d2b060501031218033201110d060603060b0d1d010207 71
    0x803d25040341d014000840c00d07001590405902110317943c16078000204000796502480342d1402c00e40064200942d0a03224140d10341c26030b000c1d40c0029002601c00f2806881ca2500704001a40005699000384450183e140101c400707400010080420051540b004c40d40f06070154100340b0101040c004150346c1c401024042c40c0c0504010170540c030980399810000b0b281e400461046078025441070780074007810300c036a450701d61454002c81031400d00c9550800274105511054450003000706119100803c491800c6d04010700003036813201e03244910804460703000c515990f84645946000340240c2e0449005028441100550f01c00d444000f404030385007a002200307010350310250201120b026651501d800042c40c40c80441e4007080e04c801024030201079404d20700c00218010240d0307003800704466a07281c920340340044d50a4800314111b08082c51400030b0103010628440c0a160090300e000d0070301f40603c5280c800302409911540032100e51203030391401900344101072249900c2040703c45c0d400030340d1185114200780c076 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 412743678 1250 412742428 412742431
    0x150c0705071e050d0b0a05041a0406050708010b03070e04020c070b030103060b0a050307030b0109020306040906051008060a06050a120503090d0b010509101d101a12061c26030a05 78
    0x1000c60031000c400905868544a81c1004075400b031001e080d99110006c120010b004003800880d8448035801c4000e040680c812100791282e03009100c0418a030601c06030207040c0f40302c181c10154031003000300300300140c540c1c010710031189041f0f0507640141e489840e1154541020101c1c1c000c4480784d24000000024080250007034205520f08844042200343c1d508205565000c1c81d110041a20111000421400c803240e0b0186600140103400441e2070b41007640ca1004070341080b20400c85040d0406000d00000404200c003a9020300c2c286002c100c801e00344030029085007260b2103142542c80307403155124104001402510103180020f44002030810185c503014028072000d0155034040c414040005811000040340401294070700c03000c030754032042048031004103900010110035009030b0f1010001020340c0d400c40c12000d00c41d0116a0941c80e41c110085140590304044d1046220741c034a400700143d64216400b00b00e200e583e02101e840c01c0d00c00c904a45004000d00e440d46190250780101c20086007540c06d400c510b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 412744928 1250 412743678 412743719
    0x3070b04081902062d0109021e0403150506100e0603040218101406040e13020a0503061801050105030705010e010c0507090513020f15090d080f03040c0620150c070507 73
    0x30340c2d56103480102d80c4007017695030405100c02296004106044280e030042c00b8141e4a018000300c56a0b00b03a6403001e10b41d20a80c1b080703c0300c01140c0d00c0100d0014443c41102d801160488818a21040d00316005015105440c079040c40f40c100080494115a109070b4124003c0c2140400014a8a4404010502010346214201c20070540d040100c10503d41130003110241c0e4554103010055450360740000005803a0600c0807a003005070b803540490307142d80800c06030303206102c1025031080c0c1c901d68003411400e444060388894081d9006a108fc441a03810412481f1585401c1c64003099210460921501c1c0032100d03407182111520340028094880c1c00441c41d00c411600a6070202640008402403084150243c9110003110406000f1031a69280040c0d1343c16040d80140239860810602000c2031a403940151000c0742c450304440001c124040d04002c0e103824031000b415414104c004407241c07040d15840290b4402d00e000700c4c507400080d0524034800c2036401c29038019040f030361626129010f4042c07024040425 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 412746178 1250 412744928 412744951
    0x20c0406060903050d02070f060804061d06150312070209220f2307150905031f060e040809010f0c05030c010c0306090204080a080309010b151804020a0203070b0408190206 75
    0x1704e500749400042d24600319600000a541c420346031000442c0c0d46180a003080319580d44600100940c0d400541c03040081400703c001410301806c100418541c80c0140c0507069019410051004480f5125882600c40054040d00d00e00556581c03600490a800c0d4109142d221001c40c65003607509201c680001c0c40c0040d40f003024004d20201082005600080c5107507030440d05580540c0040c42070841e001403e24065055080079101941c80e0000a170602c40f2944000c000020800e01003e0105c880d4040c010090102440000035410a0380303030000e5501c030b60440b5605000341c2c1460076040d2031048440e00007240d002800e498a548403645854040d022076003880700002e04014000c40e00300b56a10885007226503040c000e245024080d13442d507450350401030800003155030b100e40c0e8004640701d0740024200c03412410364641c0d4809444d0410302003552207a42c0a401a8414420034002940010460340c00d20f4000450843c190b8841c0b90004161040780120007112039080c40b000c02e490f40028000c2e0040703041811 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 412747428 1250 412746178 412746193
    0x901031406070e09070e0105190206060a05060708070305160f150c020606030d030e1603080703080903030402090a18051006170309090c0d0225051005150f01020c040606090305 77
    0x1000c685141140f660349900807407801c042031800b4050501200c032614181000350801001008103003054100000c4440560050030030000c0c940340446020300500011161715003070040984401c3c5c194040c40e0030050a0120005012000212100080656552200e20f0040850051800500c1c0380b03010520b4114540c101800c0070f0b4200d0002c6038070f510038007015000b420307100032115044014004519000c109030241102140070440ca040303441c4040e40c01040e0099958026141c01041d070b03500101320f0710440c2c0042c000c0c40b006a4a201005030452013100c000700d402e04039140705481c40c80f03070200700404612420342c041c0c5503200641c01c2a0112503d084c401041404242141d54403407162a500c80d9000d0070310f9002485e20070282c400f400b80d40008a000504100311001e07200001c4901008076016009905100c404024080001c20a00480480300703004504081029000c0c890307091b0009071107210350180d0b07100c1c6640308011500c00c000c001802413040d1541d40d00c000c0c00e10496404141c5032801000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 412748678 1250 412747428 412747441
    0xc0c1536100f0314010623070515071106100924030c0f092a090b03040f0c08010c02210d1b0f0807020c04090305041e0f050d050705040207020f0901031406 68
    0x1400c0303041b61040d071104015100b1002c1e28030b500d41c603c0050524030f0305051111a01180c808c0010100041842c1800d0186051402d006000c0e4090003102d8440c0764014803c21060756850030002d4201c0d20010404900310102c0c442030416503044001500140707484078000018005100c00c50b034200c580c14201c90181c42d4458010005440904160741180c600d4104085140d8030301c107aa6242d250410310b4018020f5880300d50649241d40155030645481486038200c00500412040d04401400c42c44001c01c503001c1405006900c1d0601d8001050000014802e1022181c00801c201d840f1900701050802c180d02c0f5100d5842c10b844401342c030701c1e0001144034840210040c041c0301580e000d407003d03400401c2c0740c02d010020400170b0824200110308105003480002500c0c0c0591881d00d107218a40d241001c0100c0c1080188840300e02c032644180c0c841e02024070503502041000c03500f44107880d41520702581c0c40056002290501452502c40b54120000308000402d201c00d040e05860092600c20a41d00980c0320318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 412749928 1250 412748678 412748711
    0xc0f01240303230c0f0a02190302010c02090424020408070b0a050d0b1c030e03160605040306020903071a040326040b090d05030c0c1536100f03 63
    0x41c08001d0108564102c1101c00c0309180c08141c0d00c10401c480c0403841c154841e90b4207810542d00030003652255000300151421441c201d0806414514040180300085156400003441c1d42803040b0082e01400207000840c080c440341c0d070240d000d40001d0301c10035524a00c0f0a50722000a601074802c0081c2801441c0b400310f5000d400b0400c84810104985e43c2c2802c12a4030f604080090282c8801154420554a0240303034480c102800440700c0ca0113615040014403d510600d814500c0c80644282c007034080c082c00744480ca130804251020f8a03000000140c6451550340403d10f0703c400b41c0c0000c081d940d018941d0411070b440e0b120052050340e2143d090010218025038202508640303105819030014020b100900c149003c1d0b401500603000c0c001d1035134510f0600341e16454290341c8012950109900b010001d4400e030300300820172213500c0013148016032800240c13210700684555806101f0b0041d803105002c103418181c0d01071030384019200062124a1200d4086c002030310b0400040300c841c000c2401c02c49000a800740340e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 412751178 1250 412749928 412750001
    0x11040513060e01031b082d0c01081306140a0501061416030302070609022d0f0a090c09080303010e07030b030f0a02060a1b0b0711070f06050f0c0f01 65
    0x216854800680d0865550104940602c0c0050a801803112000280134508015221103c11000c0c7c82140380b40c02d034a5045109004201c00d010154040c09100c00700d03903071065000360b0001030307444c030300251032020f15150003e828251960011101c03600148007440ca01175100b00c4c101c1350326032500420314820201d034484d40c7c09403502d140c04243ca91106170001c20701a40060469074494440012007061650020305028080d200014403049500b0218a843c40300045007418484100c0701290071030102000159140c4950007101e40c42a100c1c172422048074005d0780782001501000d415a6265030b120138075403840c0c0d5021550100040c2c10304607201114100440c640d01c032500403502a0000c2c00c1c85400b8400307940e2014203201e0400103013000d5500071a11143c00044031600c944034000807820800e01c02041445100581d11460300854010016a10209000012500c160900c1d580320440421500c14a0280c000c2c03e940ba030040c3d9100349030100c010343c001005000d17480c595800c40c0418501c1644007641 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 412752428 1250 412751178 412751189
    0x206011d0c031015170c090603040818030303040b040c2403050c0409020c060604050705190c02040902120d0809030c0c041107060606050d060503060c0723011104051306 74
    0x901801245200041c0d078019039004051404565038180e840c42420745240c000d040b0b080c001350000030b0801050b500003c006800c602124900c5007007054150004240380301c003420051075110b000550b1000c090800440d004140001403d4940368685030524090003a400c840440303504043c1480441c1440c8005000b0310004036505202980c1a1200d07001e400070003010b0b00e40580320000303200008680320300d4002000e100704828080c0000d801c0920030b0005032800605100b050020500018079036201d11020010410400d140449084900e0700102c0c0061a18482c081d4019061100d40b485410300010030a04080c021390320300110342d840d9006543c81c0d0003200c0c075155458000000301c10076480c00c2e401031700c20541d040180d245040c0785680c0700001c440c06944844081807010540d82d440c803441e41710302d800400c1d068000e0180c0e803504060a140b00c1c402c5000040142c14a8a50130208184810301c810f060074412000304040c41c51030b0703100c0c01d85412920a85210780303c410f810341d181070064001c1008807030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 412753678 1250 412752428 412752479
    0x30112060513030804020d030c1509030305160519090f121103010b010f0c05070e0406050f0a060303090302011b0b101502010b090103380a0c0305130b1b0403080a020601 74
    0x111755a080040007030b60154190304001c4180505004500980051800c1100101d8001108203e919029060340c00040c450b101c8900d40b14505a58581c000c0d040342c4074100b0079a24148000e50900090b00c40c207005401141003240c45040125121803000b06820009000305101d640f074840740000c0500f694030720801c40e40050984006441c40901034801c1014262252042c0ea19890f220602420405070032034040e0b503031030388034001d2200041c00a5560b941214000c0002d210182c01e644003d480c0100300c1c0300003410001c1d007400d0800c01052600007038610380d0f031103411001d09082c41039140180c184940200c6000f0307451459549409401482a0f042c48000a041c0c0a0103070f1840d01c545400e20880308040c1c171000d08042d002000001e4408103a011000342e54019100343c01c21185450440c0c403101a100f003894644018080ba100713102ca04494503035170000300320080d5540c060a50704452001030101502000101d0044200100c1030003401071032800c0d270300300d403101d80e07950b5601c01102c59104c02420000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 412754928 1250 412753678 412753681
    0x60d020a050907030f05040807022107030b070c020d050a0605062d041407030504030e090c1b0106090c05070b060d080a1116030302030c011406030714150301120605130308 75
    0x341032502d070b101d030310a030942000540d0285a105090980f141218201c03110100001e00b08114600852a564084007001c0d558643c0380080c250150346404030b00004c2c00c441e145d080000c0c0442d201e440c10191131540502005c40d1038201c0c2c580566560036881e8122070041c01c0100089903420080c4002e41041d2807408060060781507800e01f803100ba0f0304200c00c035421130384801400507884202d141081c05045907030340000d80344c501400e0043c4024000401d9138070840703c0006100403240c440c0706480c00003200c2600c94200b0303140c0004107030040980b81e0083d41441d08141c20300f40d01c240c01001401482d800b4103500b281c0b90303441800300800321000790001001220305111040c002ca11407034207888040d45070310481d00d4805602c82d03104107a09155204034014ad2000452600800d000c1c050421402c52141c4d8a00a40c03c1000000e5128001e03805101007015030844000d00d641d45a004d504100c07410403900301d82d2545c5943c043c01c41106c0b21681035440390300f89804150381000c10307101070003496003658400c2c070107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 412756178 1250 412754928 412754939
    0x1e05091501050d06050901080706020d020312070e1818010f11071b0513060618060806060a0504031a070f0f170a02070b15010e010306050d0303020c101112060d020a 72
    0x10f40c00800d4501c101036610200441c0e1610b4511504d8040d100c09002001e100c0c0c9050310092500d42142d02c2081103400603c03240e6649580840e003141c10100600300189031100403004502e58440518920301e40c25104024458101c0c0d031074200d640c480c040a0300034040701014900c4001581c40700c1e500c0c0322021004010003004100c0011000b64440d000c101141c42d2aa911400503d25042c11030060b00090b80e2036008000880e04148a00e18280351800100e4006d46420342c007801c0c1030401070091b80030308000210895001d00c10302c01c890103594011082110007698004006000750304070350034000b2070150320040c0e106034040e01300302c191075a19640e0706c0205495101c121080031702c094540d00900da000e00c04034000030070300243c26104200f00d000c0c2619000c0443c00042800c03003181501c9042c14680a4248560b440d5000312500c29a01403c0145c1d460001d00d0805107802c0380e80841e0100c4503c1c1c034251074440c0741e6080c020103141800b12210809522200c0400030407640c2010000d40c40103541104100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 412757428 1250 412756178 412756187
    0x60609070522030303050109230c0327060702070b03010807210f1208060a030209011406041e091a090612100603030903050f0109170915041e05091501 66
    0x21546000708021100700080201e04040d401c032600f0840101c0d0301c60b001409880b5282c800c5040c10b03950200545c2c001b85c28030721008807003840545020401078000000802c001c80ea90003080c2240070341011600c0e0120700b1182c00d91200f400780e60142c01801803100000746d40030103038142ca0680c0e41c5d40003c4c20340645401c0c44046610b58443c104185007071155000720208104084503000d40340a01201c000c05662440c0c01801282c008000c1407040d00c1d01503060000d0b031200c3d4a56030559184c04e08101d44c2e2485500000d20600843e808006c101640c40d00f03103405045802c017054116070307004500780030000211404042d181441c52013541c0011402c0b000a80303503e8041c4076003000f9440c50083d100250032003800b0741c060351903640007600411070704001001000340802041e408016004000c00400b03145540303a0035089242d100c05d80344460701060704c0185558900030340b052051904821591155150040342c00740c40050f48120b0168003e10000540d400c105000c24801c1d440c0c80440041007401c00010b40c0e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 412758678 1250 412757428 412757437
    0xa120203030d2a050307140412020411190215092a040603061a030c06040602150912041706061504180204090203011212051606090201020c151b0606090705 68
    0x303a40014203c4070308120903141a083c06140b81c0340d0b189607503840c00307900150800004002c45c122030001044200500d011048001080b540d0480340814803030061414507185010702c0110340e5403600160000800590001034088882e048003d0300b0b683c9545510501da102c1c0010340712030b0740700d020340a0f1b0510004051705820800240007000040c0d090740341c2d1140801c07506d43d80e898172403003140071b003580900b13207820000501040c10850b2aa8030b0282002c000a44411144502da0b4200b50031102140e5412410b01841f2542200c2400181d111550b4503800c69200a203251034881c03900954010440504000c0c03945081032071510b04440c80c0514221035950003444640342c13801c0f030ba40d0900c804900800240000c50082c56900d00007980d001107801e09081c4c00415000240500404002c0c000560340000d00c0303a0207807034010400152244072400180e0414000c1f5540d95840700010b03039078004071500d2501900392602c0012420070705070150030905940e45070603940c25905c4255800040c00301e510810060 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 412759928 1250 412758678 412758701
    0xa050405100504140d02061e04080a0806010507060509031201080f072d0e0406050c041212050c15040c08010606051b010b03030301080f0c0108071e0201020f040b090a120203030d 78
    0x1c45032076190640711401c0c801914030140040e0896001e001c69611088601c071418520a82303d20070300e0402e6a00c04155110381750519051214a00014185a001d10180d40320603030040d605100518024a01c251682d0100004070618030518002090301000060304540594500008140c541d013456081a8440c01b00c4544140400840449411070407070a2460401480250280c00780c6040624018040e201c0050101c000c502051001f0400888210f910a00d0309401c074003401170a254188044a1b14070480b080004248500005402007041403004244202e000b0442c1c128010345410307019080e2645e81c401c1c1030000d1010300034514041085012062120108070000690301c0c186004242550803da21151050700598801c42d51440207004400000c042484c00748564070b0030080182141042810f1405041b002d100c03885401d50007541100e02c0141100d5040761030755550101c00c0e44981c8441f001600070002d81c0c10000c0c00d002060340c0c480065a000300607509001e0040700740d000600940840 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 412761178 1250 412759928 412759943
    0xf09112208010e0708010b0108070c120c0812043809010b0d051b1c0605090705150a03180c1e050d030c020f030c010819020d0f0209090a050405100504 66
    0x2a40c041c01d11800c05070600300c9014100c041d190290301400c5464200032a414045040100031000342d210399020b15807603101c3e0294006025080b0304a54200c06207030010180600012840003200710481018440c82c8607003910311800c50922003004201000c0c0c3c40304100c0d01e40c000395a1100038034900c0ca07035900100300b400010341800e00b0800038244517800704064a0507040030a150320818000c801c0c00480d40c800b5107110728898548502e0b00000021241c0c090702150751100400d1004800740103031802410000d0101c0d04e021420640c40203150311a010b04408a481c06a1101d244008a068803813025003210b0048225458100040d0100c40b503205401c0345012010030110b001e640310340801400502036500c10320341c0d40c48d92040c011240d01c0d41d2545c6211758402c0d22201078903030b4054101c585c0705d0782001e56808501110b81207000680541000044460700300315a03005040032550190540f0b1508558104240e00e80e00c0f0802c0498109036009405904411650b100e52006038101c2600144030306013 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 412762428 1250 412761178 412761247
    0x9120e030c1801030b13020d021c1b0603060f0b040611030c2a01021903050c0f07290c0d03090f0803190515011b08070b0a02040f0911 59
    0x100c0c251030009405403402e810400510901c000d011105520a14001c801000030031560000b0704011850365000740b190214600000d60020168159204c0c00c0d400751100308a1541e0400c402d090745064007494000a150030800503005010807048400c07070b80008012842e060a0210071141000d0081c4101e1007071100304000340b0070380c50400c0241c003413039a54035040c44070781d0407a10b00000401480c200d0314115445034034603403298803010410f0400030b50725060950b580c2140480d0075080808040142c1014040c1650009074200c0c4103900e119030b0944640040c2c84000d900300c881c0300900400807411942da01070441004880e00a40c040000d0320b000e241206c0200d00d00c1c1d540c066680e402114000000c01d08a03500c0003101d4820300074107402a9001203825060582403000901c2d40c20415480c1c2e20000220400f002808103540c02c81c0c0034107401c54003403001490102c1500c2c0282d440303485007034046503810354006102c0b000384c407414035400e4100040a10b000c4603034084251043c1041d03003c0428032200707030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 412763678 1250 412762428 412762453
    0x1501080c090103110c03040f05010c03080a09110406121e0c0b070602090916080108070605180a17150106050f190e04020d15050402040f05011103190e0f030109120e03 73
    0x138003900f01c210ba03190003503036200e050030b0b10002915083c0d80180d0612020384d54200000e5005280181c1c00300c414080050064843e0900c95509020300c6a1103400510f03046000ca181c94142c1d19203415580540c80500c0d0a40c0c9026056a141c586200054100d0610020034406812404014100c05005036000350038800a08000b40350400e0a8540516403185400920760107500b00100d40c2c01040b206c4040c02c0e8041c41e103c0007425901c1072100380045000c65044440503555694522005084c402000c289a1003001004603903a40c200e051003040310086000010b450b9101d401100c003400700313000c080350505980282d4170090000d400c8150082c490310301140d0039140c03a00d2014101c522035106000c11380b001f40201c640d43c1c8a45540000c0d0180c0c0c0100014842c0520911000342103030f800b8640302e00105c021140103803c0d23000e4460305081270182c25858840c4070364072020f4078900400c1150703100c1d02003400104040c00c8403540800107083c1000b41c00341e514154090510706040480107002e5844080344d01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 412764928 1250 412763678 412763711
    0x4020910350d050d020f1303061d06070c030503180a03212a09030c0b0a08090616270308031605070c140f04020c0709051501080c090103 60
    0x420060540d0907a1910304070355005030710341004800c440003a05400d00302e140000e00078410015401000368001510441c3c0700500000c40303580c0d4440c542c0308911540c480c94814081c150b102c000c0b0919102d4940c01d5050390301d01040150003020f060702c800300409203da8080c2c0c1e517600003c01807035602190f06000000b0810030301802092510903030b582c108552400581c3d40200d0300c0c141005142e00d10700b00031030035500000c1030300001d0100f035070460108088070150115000140741c0c1001389260720070031000895040c100044d201c450302603112010b131035030340d003021541d1500c08036030003101d501c40800507001c80c500070a10510600340900380300d59904c0c90515021104050750b03008031001100041003200c503c0040c0711442c210170b40f0b403074040d140484540301d050b040c454a000740d440c9403c0c42c454000f2a551035010032143c121001d0015902d4420680304d42d601d0316014411001480d007000e00007418a00510045640c4107816118002c194039406690111074008840c6039041c90781d05d031007044800c40700303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 412766178 1250 412764928 412764959
    0x112021920060a320405010e07080c0607060617070f060c0201050702040c0509030f071508010b0406030c020a060c020f060114030d1d0307030516060201050118090c241407020904020910 81
    0x41c0400444d4140340c50f1047c02c581c2e0007600008281c2045905006c2040e021a1554100404445490300c0d02c019050010040510b5448108949600b020b56142c910010800c0411144184003e034540741d52003509452440b1161030082c002001000803000614042d400440c2100907071800c58240382500021a181440ca0350400080c5c0d44001802c0201c0c50b2800d00200b0b1410030b03450020140d524101e0b11503014040c44c01181301b0300d5115455100540d108008551413560071403000d000c18402030b403001e51980e20440640e4003e00812002048100380910008410b0b000a00203001d0403840a50484555400c0138410000211055440015550820982c03000e503000704041c001e0f0300004601c10100100561201040da41490010445845615040c08001d0410100070840307114030b02d03060003006950f4210044603003500f001d8095044131060b0b891042071160302d9421401100c0180c508150103203000007540664100005801800c100400f0707908060340d01c0c40302d54400d48880700358100900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 412767428 1250 412766178 412766261
    0x40f140a0e070f060c03110f0712030e01110c0d0503040b0706020405090703050f0103020906010e09010e06120106080c0d0f0b090c01080606090f09060112021920060a 73
    0x3203401c0c40ca0400001445250014907040c0c40b030b90070880c50400d020f840701002c845c015040c404103102894a5050034858040e4804404061b60841522000c01d00e04602d14400300f074001400814000d8104d50181032010b50f88107a0702d00800400000804006070840c2c00b0100702c90034003081c040042c4202c2e4100103401458071542003da01c4a0902041c0507000c0f100a048900b01401c00060190440c8a550b520741520f8060b40c049800c2d84d02d010068600944280c4070580004000700009603a41c54405108c2c00b83c401281e80c01d403084c0244010320700362141406058205d40041d281c440c1a4035015014201030340c0b0a00040040110310f846e80c0c0c03240c0030100d4544c003464200080104080d0b0340003800315404001284d00c2030400d4140d40210b0704c0c01e0b000c940e071a0b0044400c2c001103010ba0380100824205041001419540c841c804a100f08407507100101041c086109107001c2d00c910a00b034480b180b010940c0d60f00500c2c4a541ea40701400c01380860105101a00b10640c2004035101543c66900300f0a5a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 412768678 1250 412767428 412767431
    0x3140c120708060f131106041e03020102070b1e0c0f03120708250c0236090109150c091701020a09091a011d210129040f140a 55
    0x6103003042c074078100702004012850300da200a08001212102040841c1e8242e044446240503490404c0810072501c910780009184600040f20068150440380c6e010341920310070390036170788443c0c1d8562000910380202c125041901020b17a03410310702d000c00500a070004071b40c48411280800d12107c1c000b802c40c1d112003000c211000e20b60081007080c1b42c10085594000b820060480001c0700e2007175865851407100340b0a10100864102104103640d0340781c44421200901701c1181229101c6140d51100e42001018030350b0301610040c002134004a4181700d40010207410412640c0d207410b410390980e0050120650400501103e942d0100303030a500300c600e240039014035000041e603038081150090002c042d1039021910160810300d60030049200c015086c0001c403420700f006802c60010140f06580034111002c902e130400340360200b05003441e1807443d0b0300082112181c003c004d054080c040040002c85d20040da201072041d0f40082c9007850030550f01c422030852940714006100854000e403d000800c003600d000d078065 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 412769784 1106 412768678 412768693
    0x11030c0d1103282c06090f061b040801050a0c0e0d050c010c080f0a030c2703030813050d020313050901030b0f04051207051b011803140c12 61
    0xa24400c1c050050701e40d501c04c07114000401d9240b60fa82c1d074400e180104020f01408a03820261013246005814a82e881310202c0090f1844803410f405803900c101700c00903140400307110f01802840c0081c0c002c2261002942c00410701062440307118440c2d00e44042480001303600041601c8800020301301032540c08060300f004100d071b004401c40d04101160000e026100c9035410351103008400100d8807800c40c100314221405904c130104d0f59805c05030000c000c42c02e00200e8002c01030103501c60312511030700300610303071075610f441c1881048410000903900128194080169041090014004c181c40c1c03101e480d0701d15101c000700c40e2006030010840c010400c2c00301d02070040034000321030000b0700300640c66903a06043c500165a030200d51841e0300d449501d00d0312502a5803141800b041c0200f181142c454030f460554407a0032145c02e407010080760300c0c8251202e001e031b02d803240310116403103034051005000f41 = true := by decide +kernel

theorem cover : BRFrame.Cov 412589928 412769784 := by
  have h0 := BRFrame.cov_init 412589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412589928 ≤ n) (h2 : n < 412769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
