-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5263
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:17:15.194516+00:00
-- url     : https://prove2.me/submissions/2109cc2e-7edb-4ca2-9e94-2afba654dd23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946402877 ≤ n < 946582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946404127 1250 946402877 946402889
    0x70b09120106030b010608180a0204051909110a15021203101a18040c050304030c020402041707031502030c0f181509040f06060f0e12070b1902070302010c0b10 70
    0xb000c010b4507890305160060003031040340003044184000c01c0715680a0f42c0751061280402005040c001a95020480508005811000c000d41185107120044401e8082d02c01550f01030074141c20901e0499060060340b03081684020581881414500b0140740d021401c500208030400b03903d07407641c07100d40a000e0544400e500c020a0710340200b0700241c0b06180000900002d016000c1c1300581e42c40d21109000585488150394000103404000207000a03000340c850141050000c0e0006051540b03071403080c1c621000181a140c21903004c0301013001000024001040328030b0000c7d00030b50079401c0143c0b003120075005078409509d00200104039040f0040e0415504c86070910021701a84110080c981c0c4040940d1205200034051820300a0443c1940c5850007a50f040350b80c2c91341c031030310301020001d0308413054031a05c2052540a1440f18600e40e0403102008060003525800320307441c0d40c40c006024100a0000d2001031071080d0340090742e003000540e8000418040546c0c11405419441d81c468040d0030a4011940002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946405377 1250 946404127 946404131
    0x1201180f17070309090501140907122c2a0105070303020d020301060905030f060103050c1905060705241005060c01150303091404060311063a1d070b091201 68
    0x4410325038014504000c85c1d50300f840800c03480c2d0700c5d000c48003200f44050099680103503860000c21001c5200e2503038840c41381070019000940d1f2852400c6000354410014034041000d00366043c000880100344140900d100e03192100b2000000080c030020000310b00c1c0d180c568180b140c0810041e003170501a404a0b82821450241150b0360340e190040600720b02250b0060038003174421140040541c07a40001c0141c1601d03000402000f440d403a20013000844080d40e64030303111001e094440060036441e070314080c080c060300c00c202500140c1050380c2018641d0903010b0943e11703420420001d1001484065110005564054650603550714500352400d01400d8009002d0602100b50301d00003007810741c0010407109a0b01c00c6921510b40c0600c640800c4251420780c0070142c600c400045071032009241100042a1403c1e040e60140d0035810002903000203482111954195944442e103802036a81161007021120b412652104a0003100c000c41c441d9144054000c0020308040091048810f44d04e0b0002030b0302201d100710003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946406627 1250 946405377 946405387
    0x211b0e120709140105033705060a051f0f05060304030504031406010503010f020a080a020d0b030a0f02091b271302040f050303030403020307061109041107021201180f17 74
    0x28007008083c140c3c21100e007400582c001054618002c10f080e40c03150350103004007003035a008980d0345d2210b0004082100000f40071654142c0080d20901007140b007200c0030070000441745440114610072149600a18000048110042c00b101c1d25001c0c2420a6920a0310300b01e442c0ea070b9a280980f09480360760400f07001c1c001d200e140540d00e00c000045440c10399906800071312200050705080f4060f4011a0010b0010410a00000d081800c256000c0c0c025080444000309142404030042800c01e100e945040d01c1709041d1804980c00d5080000b00f05400111210404806034201c01d4034803480d009018803200174105001845020342c4200354010b80c40b450040414440c102c9001d5014029806403003a5203920303c10090000d194074000c802d0324800c60b0103401451070301d260381d6900740041012030305600b0042020b012000c13180e1a81e2242c50340d050807030118a40d40707440b00c1c01000301c9000717070680c19001c9038105244003000e406221407080302d030350f8000700c0240c4c0809185000c440011080701885030101020070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946407877 1250 946406627 946406639
    0xb0a090f0209030d0302032403100c091a0301051804050709020a180519180e0a0809120703021f111005250203040620010c211b0e1207 59
    0x40100003020742202280c8400c09030b80c0c1300f54181d010031250803014103e900d010891f00200d04040410743c500050070f44043d01010700d88a4115014164140300040c2e20000c240041900d50141085141b0035002d15415580b400300052920031407042c141450701e00c1c1318040707030801008001500c054080a00c003552a4080441d00420b60501c110a4048580201000290909145825152589840301c081a100c0d0a124a14202d0103400450701036143e0ba94502c2000c0180500c0210381540c41010210341c0c1d40b07000300130008041d40034282d529060300001d00410059551a10b02c0e1011004100f101141030f080c20801d483c10b62022082d035086005510801d0452071317266202c20300c10641486e504202405611008404080c101280c9000da401003205010282c0a4044c6943d22441800502c0304540850400790a5031001040440441d04400224862801c3c0c10409800100745840400038a00e200c009a82c1401c1c031121450300740407003010900074a443d042600c0490f400000c08980150f0b58407a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946409127 1250 946407877 946407881
    0x5010915151703030117160b0a08070f080a1802060706050121050a020630010e0c09030c04050604021303050d0201051e0a1a0d2a03020105030403030b0a090f 69
    0x9100505106500100860394144400c0c425582c200c01d4002582181c0c209210300c140820043c01c1ca80d124070540081007240390880880304050080c10f41010f803968455440504a414080d0140050020308190403280365484440c00d64400c82840c4040340240700080b031001c2c2900c0080010390821030009030f04041c0716060304610b040b2410010000b5a4100000d049120004403002c000c0c100c1e00500b0581002d858040f01819036890941800e8603003404010301801c144001c280c100030800340703400041102484c0400e1942d84030320341115103481c140761040000c4d15142e0744038485200302c0d41c44003c40c070745880380e0b07050b501410700070749481801030746904025035584045843c0d07000548c2088005100d100024034078112003410052211142d4503070114800c003420820700a00b1600d42c3c00c00201c1e016541d0340c11100055801001128071100d0045c2c0010b404540807182c05080b10280b070790410060764050100ca034004d426240000c1c0d0881800000355070340c24554070401c44c00741084075043c2141c55503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946410377 1250 946409127 946409141
    0x2040602010b0a080a05060f06130504050c09070e0a09051f06050d0c0309020a0504091716020306010e0106080f0a06030203030d06050108072d020c060c01090b07171305010915 77
    0xc0f1030366400d45546001250b91614168002000b98101802042d180b034035110425400087c01041307003000403000c4182c10200c0d00101c03007d442e2039200f40d1440009052010700c058000c0080e15050090b25a46800300749a40c807e40300c0c0c03010391a074a00c0090b100c0c07440035125108a402060003104210781d5070100030001c1d0000314003030000601e00f00c200c00c030b0207010303105184007540e02600c1d0190b528a01020000246140b03002540c070301d5844103601c918100104010040907084003501c00c10324441d4010705181520580106148420500050101c00c0d000f1581950001000100080942e40e03184c030034000e0485540000d41520012070181100344a6421140943c2c8003030341c450325159101c130402c0380c0d0501c00701d0201c038444c8561507940c2c207495001c400802c8013a00a00403140104030580c0411003c0d884040c1240e101c0c1d40d45d00d00141004142820160489500e1408401e2810b18001c8200c50081c00f40800c04040500c0c0f18070380030050290008092140c028050404042401761000064501 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946411627 1250 946410377 946410379
    0x105130b0d0f05160608311410061202301b04200309031c1b0203070506283b0a020409060b060414030d08040b19060902040602010b 58
    0x240013400034018011503c0300304640e91581d603007032261581041c2e8130720203ca513240301c0550002d8040c03a003802c401051860819500c5a490280508080010326003071440c513034941d4202da400e100381080030342c0c55410071480280e012036003600d094444452001d41045144d0190004458500e540c400303104010803411055056015030414001a00d401c200c1100e0b00c0d1302d82c001192000c4c0c26160010019807024650182e10706048915103c40d800c10894100d100c004114002a100e030050690041800305070030420086000840c100001552a503841c0e0900412510703104000401719031000d400a18564804141e4140800801c003000c560701400d02031014518100488481d030b0700242c0e00d880791448440618039005450104040c2c0e007004068407140300261041c0d62030700d00380051655020024001000110982c1c2c0702442c1403020b140c209107088003a1014803800404001c081203504d140a944942d282d079030540700712044240f00b0000c0c403041c2c12a00b4070502c04a0007154040c0c0540c42151b14140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946412877 1250 946411627 946411633
    0x30910030c0e0406080a0b0a0f0f020c12040b030f310c0e070906080c04050a061101111608031b160302060108030c0309010c1401110a03140f0105130b0d0f05 69
    0xc0400b0500050760303000d214808496020003000c80115003a425141e40114500c14042000b004000080080e1643d07180c50048059000a44114103070302000640600a001d0601b142418a41010071080d40001440c00c441d1b10364403800110606001451a4000c002d4071200c003281b00e0392105403c0405c00418000c4508460b03055001c10040c0d290400300307108210655849103094180f880442d4140409000c5a007151800d0101003066611480803901605480e80ca0283c1c030440030380c00ba400c0d1000300030340c03120b04401004600e294101210180000581121f55030b40d403034684241c0280e40031400c0c1c1d125410100081030b552030303801024043d514010b000741e08039815a62108205916881088548001640708100220480d4000c4c0c401807441c5008118106050444240c00750a4a0804215100518000400e003044607094807070385901401c44d010700c40a515000c000741380e030194103010345d5118001014030750b1a0050b668000200e0f0a4010f0a2800d44141515140c101b4910705401104d00d40 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946414127 1250 946412877 946412897
    0x408150a050717061c1515140d0305070f0b04051b09060f0d0f050703110a08030a090524341a0a060803190e06041a0c030910030c 57
    0x2920a40c40f260b0340390700050255000e03845810410603038100020120190500000c0848081211101c007001910090800407a003901c085c20b82e080c40407202d0300f043c0c0018520211815081e100d6071118440380d5454245160b5980c050304204010f10100d410041400c0e07184010007041010108800706107101013000301418041030410031400b01d80450b0030580202178504d00d107a0070315000c1c48440d40e503401002da03440710701d01c44d849203410720566400580c1c00114203103800e000b5041c003a12840050003c0d1000d50700300344061400802c904207610490b441034003050f60070f103149181501200c1c003030b11a188040781e032544458818848150310111011200801c080c284a120780b141c1030404d280303540940f58480d00d0114030660380c01080c0141c51201116034801022038420300410080c0b2a000140414001e0240d103c80000c007a144020101c6007c0c68081c0002c019800b20502045151801c00300c4032030702c07004844d02541c9540910300e40306a100e5010b00318a0741c01340d010b91144460001941e1342125203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946415377 1250 946414127 946414141
    0x1b0e01030c0c20010302090303070305090a0b041d09070915030b01060801030503030f04320c030d09050607020f040501030b040303110a080402010e0d050d170a0e0601060f02030408150a05 82
    0xc0b01a408041d006030000b80c00281d0007a40d21040c102040b005040050a103404140800c0c5581c000c001c0031404900c00198101c881d14044014800925101c04524503050078840890288000b40c05c0c58403852003c003000c640410400e20a03040070b002281420051a20114801e601d641401c0c80282c0e10304110300004205284640f00c83c2c0c5c10380350040010743c95511042c0c0c0c0c0790200200100195603181054000b1240c0e071500840d407001184800c11b0b10b520315801015090300b82007801c007209200e40d10103911241020f070800483c0702113030800c07142c042d1646000c0c00890344185030001c00c0c0e9440340c039120001c4100315a80e12500d00490003076508111028140381020314511030000002c0214045000040040d8800d091014600a010380007a88401460740e51602d010b141007051000b02d07502d803035130010301144040601e0780590030300424070080031602a43d50702c40c0c2c0c0c107004450411074100d200051080c02081110f0080c1001d1040395404000c1460000f0105025900c00c440c9600b060003003024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946416627 1250 946415377 946415387
    0xe0603010905190303090206030f160329011115270304150c0501060b0408152418070806150903060109050603070308070f03300f1b0e01030c 62
    0x142c1c1c804020301620681c0429003c22410040c0304404041c1c079114840f0058031100c2c00b460050400c1000544c5604189525119900610030032100701450a0000c041c10103452140d08030403c2a060407101030752145004a58095a10182e10154410140000034030504500003520503201490740c0d84000d00d5000e040180c1c41140526000e640d80306010a0240340c8144641d84d10412850800c1c814020040c5d4489094070240e90200010031408a01001901000d00640702c141d00c201628540c0d030b140164016a4004a0200106107502d040d0130b0205591550b00c1103018045103208803c01c94a00454000e1200004271049401280100421075410002c24146c4442c2d240083c00341c80580e003040d507800010500240b074187d05204c1c40b03c001021590300c42c014101c3c603006d0180840380b05020300340a40606d5200303a5403021260012220054020050300d10040141c00d40d0020404d040d2400c40c00b4040c250101c0100c1401c0b00121110715026049166000c601d0020b0301c0500917030002d0441969 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946417877 1250 946416627 946416641
    0x12303070206160f1206050d0c211a040f0c03060b01020709050408090f013b061e030c070b090a0210090b040b0c10050c03090601080c1302160803100e060301 69
    0x101007144d280542000c1c81c0142c00c0f1010303061030004000f401d5980c600000340e0400052809862000c5c0440f8280a2500342c0c160709640c3e01500038620102560300e940b18550741c40290b002118205c000300c0454200105600c000503041e13040b43e1005100d503101d0400f08001c00720f01540a02622403c500000e0911041c01020701c034076001060607007054850010f1010b4041c03001c01c6d00d41004611050381d015450090080390070b064110b8070080386c80b01e513000c001240ca02c070a008184103ca081c8103d04c03621400340400ea003410750b840e55068481c0c51304c6428100c00c1c054210001e010400c45c008104501a000406610050089600074203800403180e00380d42017030340d6014210b4162020031040c003010340c000f4001c3c810f885039a011101d0755841c4150f850100c4d0f00c02d8901040c4118004140100107104100c09809440083c01814030317407803042c00144c1c540985101010100c0d070081803801c90308040c244d17001e140a801028803640d03440c1603000d40364000014000c0440c80041003000c03d0442c101441150 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946419127 1250 946417877 946417921
    0xe0a0b220f091e030e030d0e03061e070507141212150a060e03070f080703050d0206070504050d2402030612060412320a0807050a0914012303070206 65
    0xb541807240102015101d01c2020f090301800100b10065545880810007508000c04035a01c8140c0020403504240c2800400360418441d01c02c0c4025183c0c3c21b008a804164220b03541e400d0807541d9000601d81081c0c60006864941c2d03140c040c02d18a0408a55003100410303000c00b0f0380d1400c0501d9070b42c01c813604e805603035413800740c83d0041c2520000b4000f0701e00899468a2144008003124100340da2104c84000c80102174008030303c036401a400030020050f08010b00d40140d0410b0019001078940480d00520502070703131141d14401d5802142110078090b10340d21800c0011490342001c031540c00600140c070017135072090340c007580034038080780b04149840b1022407000e000380c1e4010b004855506070711804651b03154841c600404100341c5c01030210780b001540179103485c03d99045401507440c2c00b0109005448100010041c0c01484030400181980e5680101d61505555003420030b2002410244012035016041c1c9001402c0620f190303c149142c1311004010b0f40c8569240e9084074050381d40e20201c8a45000700113120 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946420377 1250 946419127 946419143
    0xc0e040524040c021920060a050307050f0c060a090c050d050a0209040302010605031902040c090e070c1e0309030203070b19110a0f140609010b03070e0a0b220f09 71
    0x140110b442c080e0043e403180f409901c121440c10f0300140c540300d440140850304a502c0559285a01c14806092120210414007280c0c460b003401c80441e406000c038803009240b0020001e0015001c20103040220550b80601d0340030f802c40d0070514200180c1c01c01844042001d6a44003d041c600256910b401c11601c0015544800501402401c45c1d003840036045002d0f000b2015552140c101160b640c60800c02016105d50715400480544054010301003140c4011690804201440300180b1900b20303100300c0c0981100d46803400300040480c0e4102a42c0007c0341074940e42a4101d2081540e0505030302c40380d4402580d00031415500c0d080d5803a0844010352003200519200160000c09000c045400340a090103036848040a45045c80e246641d0300030003202d003030002c132110700d098054090086801c1001d1544914501c0080250326548000281d0390030452262400d88600000080d5000e00f240d08240400003000c0d007160100c0300056102c0308074140964181e0002032420343e4225a41807a4080c4140c0181c12480d4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946421627 1250 946420377 946420441
    0x40302060601121e1e0e1e0703030f0e0114160c0e010305060c25030f020d17011203030b03010f090209070206060609041a12100e060412051c0c0e0405 66
    0x200805010f8402040f0a80c40520213590b1110703200d070044000024206c400762020404075003240c1d410704c0200c2c0b00c8841641c03000001f4000241c00c40d00e0180d4500c110300300780c00700000303c0004903407072484492402c540040100d1200221140d80d8584d0540d40e2050010240403034a40c40c202d20460b4003444041c1c9140d00ca00080760b00b00315141d00408600b140c503a10710046818a9507210b0003c40e01340f0f022000910342001c1070517001d50503c1140402c002030301c3d00f07080e5042c1120780c1022504c0306000d43c0900c1c84150380750008050281d4080c0c0d60b8560040c0090190b480000d148070000d2a033810240e0140314090700090805101040d020b2003550000c02690420000341c0501c002406003011071030f00702c0360003244400250341c1c051007518801c01c910001c000c2400941500380a41d203c00c40244140c0d4002c405000003d188481c0b9044085c01929040e900d448004030791100390150700300c81c080060b140c4840007a0140e40403109409402c8262014045512400444501c00c071218644600040708600 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946422877 1250 946421627 946421681
    0x3030c030f03070c0c0e0403030b0618010e040b031906050c0c0a060b0105120f010906080d0c06051b270604030503161b0803030405010c18030303150b0304030206060112 74
    0x1e542c010400746005825022169101c2a0305ca0f07042d00620020031141c000c000415915001d601a402015159070f800d051000300441c209800440010b0305100101c0001c40701e1b512150320010703020b60000d044035101550900d01070741c441c6501c001500c40034203002c00201c58100000494000500307800040c041c0c810151034200041c2511010641000310401284150408243c0b40798050145902e0403440d42d40f600c0480d200725031043e880750010303400c004110302a80d40c003d520500d0054210380b000c50640c1d509424250520070703080403c84030740c0f004260340807d0704090b400b00f001a01100b118840c0c203506e40c0c0c204a000e0090b448000e000b0360041150800b01e017106003d20340d001e40b24104004e0030445000c201412000150404600d03580048108010f200d001d0107086000c51b81410440e801101011040b41a880b00380000740915480e40714051804514410010003414410001c944a081a150082d10b0705001c1c1e81d001c0c005040310340e113420030407424031031803100300366152a0710072802c0006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946424127 1250 946422877 946422907
    0x7061119031b09051c0309030b07180e0603030d18170a090e0c040303120b031e07090605010903120207030609030c060b03060f1902070f03180e1311061606150503030c03 74
    0x405c203c003005100d100010001e22210005400f488a5458a01c0c07080c4410030195404a11680031000e02041c00b418810a500c0110031140301c81c2c5a140c0201d03c00c6400c04281ca1480ea040c8802488078101d03001c0c0030000c4810305d0250104020b203a0310047e080d070780c80001b105512410703903c0413000c1c4002c10040002902070b40b070095500910754000701e6840905000070f81010210442c015501c2c001c803c2c01c0601c1030b000e000d0800603104c602004c200340341c144000203042d002c903030100170440d5188000d4480300c54020082c28000313552140c0d0600032000c9500c1d00405034403420104070b0f02c0c1402c183c5041d94516000c101c05100b807908801d00305c410350303800496160760708c004c0c111101007641c200070107004914042c1d030b90238600d0300903294030800000c041a95641c0070000d90040ea0010105014440840e08800507003404a0f00400d085c0b1401108a0004005105150000c00c1440100c0d211404008dc0d9030040e52482c0c84181c112214182d58200340b540741d205540705402d8030742082042d011580004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946425377 1250 946424127 946424179
    0x130b0a051e04060b0310090e06070315030c03231906150305070e0907060f140a0311070b01090609020f07120e090108010225030507061119031b0905 65
    0x5040e18400c80140100401d08440c4184c00c00c850044000080208100c3e5903030740140104009401000319444500700c0903181c900c09440d031810191907060306a04041559980805960007981c2481c0080d0780e0300d031408150000741a469080d819075001034041c58800701d00c55265810361144da003050341041e905c100c0280022942d003808800d10890100104004000e82d07009000164080207c5c0c1c11305810440c0341c584990302c0318040140101c480120a039100c100407952055081c001a11111107441c10703030192900700c0d0302c100480d1020a1007418401c0c03084080381210341d20003040002c5903c0b90b6100059101c0d480c3c60340c1403501c041203800006414940c0350041d0322910f25000c00c15200440005002000a80c082c010756900031071800007100c07001c030842000b000340c2c510398804030889a402a22900828001814a0f5651410070103c180c0c1d10040780c510002e4900d08407000c042549010b801000d08000c03852a04d9014445c00d0401c1d03005124420503a03200601c20740400741220081d84800d05c00e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946426627 1250 946425377 946425409
    0x506091306060b120a0b0f0303040b0703050f0d1b020c180901021b0d0206100303080a1a0a08030a08060427080706140618040305090f1804050a02130b0a05 68
    0x142e418001224800400640840c2d91120214122410b041486205540d68048801c1c030801c100700c640940340d6000821a81150032441065488501a05050307480e40944146101100170020f6007007030a4a6582c005619030903810303480305c800341c40c00000300d13500c00785998070a40007030072030f401d04142140581035140e0080c600f20015152800700aa40da4060391030f4000c0824551141d84804074507501402020381c41443e202c600d10400d0324603140100405009443c40c070425658021a81003580c4045060101801c0035003a60400d9944149444d6691b1020350a00001240580428a80d15140c024401c4c540c000003038900c10490f000780c001c4014034002c0d000b16105081000101c00040b0075004e04240d80d6005c143c0c3c100103207010300a20070b41d50211445080800c2c024010840066084000d8448006043d101c0d4804515030348089020320701c0c40d00d20806a04810000c000170008001070107500e00344242c0d202040c5c407040c1c40f11001035481c4000f100e0b13480308240740c0500041c207119081c0412645 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946427877 1250 946426627 946426631
    0x1602010c0e01092d0906150f02100c0e0312030a0c1e0302090d0b0f040b07020f07170708070b0c0d0207240504050907080417070c1703040f0801090203100506091306 72
    0xd144240701c104c5042c82c1d00c40701e241611000d040000000180c032503118940d0b20708000c4a03000c0d074800c0094403031001440c2625032641d94500000001c1c03141d60784007800c0c180502161124881c0b0214043c00f40c004450001415003070000b80c5054a10800c000e400003003c2c040010040804101d05170301075044403030700b1a080421202018040741c039410302c1d1ba0040c040042c40b1112820103003071148190400801d40800c0d984000401c0d86403600001c1c1c1002200c11005c054104e451070a4840c41c2480c035681d000810314400c41720b02180d06801c00c0010f18000300300200300c403045900b211007681c03036104900c20407a010215102d4611000c0c00c02c90010203601c1145011443c2540300c0c40011058136090310500d00054410042004020442518801c0c0c55800183c65044c2880744c0d030340f1242500c41d80120000c04c5850034021407407900810981b00500400c01200c413815895410300c60081c0b6056100ba0310912404000d288255402d20a05000b4000980044400e58440e515154554001401181d03866 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946429127 1250 946427877 946427939
    0x90604060e0610170c12071b021201060915053607030204030609050c010221040302010e060d0c020f0607080714160c09060e0f09150702151602010c0e0109 68
    0x25043c0c0300041e00c10406107119030b4642c507044034003821442d002001c180170700c8000c000c00c01c42940084039030700b4809d0341210032070400c00c0c907480840c0c05888558003000074281007140a0300d060f6010000d48003603804c1510826500300310390121a0031295030b0508103003a0640b00c1c0340101d00003028012700303a100b0014140035207041d90320313039400d000c41d1501042034071250802500390145603818403040e0f41d01c0302640fa60003005140495146540d10951100074184622400754100507220b0b4000e44403c2c2c3e0000320100403840e01500040d4a60200811100d050b000307550000d1306141c01170142e58000c03c82523807041407251009214065940c055030150400702e060441920019106030160b6010f0511000d003c20000d1400102e480420001380c0040b02a002c101d08000386001c0028500041d0701c0d001d0941000c40d103452074181e0420f000188100c400031440360070845042c440c52155450716140c0d40c0200700e94001c07500308640d05219070f44494001405c139002041305011139210200800848010354402c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946430377 1250 946429127 946429157
    0xc1b09040f0318090f0e06070f030b030c0d050a2303030726011701110403020612100b0a08160c0c060809010f020c0a03030e070b0d050c07020d060902090604060e0610 73
    0x10384003a130040c480140c4941603121400b00d0790141801c65024940103016505140c0c10103880754145981c0502095914003850b0100d80d41003222a041c41405004512043e5503804c1c41c07034641a44480c251a0245005102602c1172104560b00141c0503424010b0f505644854800301e039100800b20031000c0c00500c850205c0520411200c6c3c01c7c0c002e05442c07415150364070950000c5800e41d0700c0310f2000c07101410240020001350b01e440c002c0352403015180321051841c5d0b43c1e280b680031071072000d504100e04503d0007140011049400003015030045480d0074070055060464201150350004e820401404041e0402d005c02c8514080c008498200c00400004580d58502e1002e00080f40c0000a0310159035200000d04030901d6010321500214010080c0609803950400161220501c11082d26012195a450000d500d0b418000161134032180d0080c400c0da104443c0c0c5c00d0030000780888040580c424040c242c0855400d28103441150116a0f44d600000740e10f40d202402c0051450303004c400001482607042e801c04103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946431627 1250 946430377 946430417
    0x20c240c1e12070807140712200303010816050f040c140a0207050a0801050106080c030a0b091e010f08100213080d020a05121201030f03031e020c1b09040f03 69
    0x4405202d1600c000c2031a1100008003001d00280104040c4808003103254900c0b00c8a50031615150340203507500c2030305003500743c0407a008481c4440a2840c00c4007080521034600001c0010750403039081c501100c07000200343d505a614100075114165110942503004240b80c00c094000c07102c4917405040c50000900b6040c030b10b210380d40c02580c400d00180c021a00510040c80c0074a00d2030007a005510080045604140001d8056040030b4140c007a4010040000780704614170b5008918007241c0542001e1440c10050261501d02100c2206680182c01c15000411030f0024080503030200c0304484021714008642c0c00c2018001d501102400000f42d50005020030a01d40801004515140a90040141c03095a051950402c0303020b10240030001c200701b103410403015a214280e0705480e0004a4000300025502d019001041c0302c1e11080300003020314402c05142196640905004503c60b0305840340041c0d807001b99030483c030a090131145d00c0100400814007150103011454100792003410111171660747c0d8003030024 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946432877 1250 946431627 946431637
    0x50a06020d02121e220c031103061605160c0302040203040c1e0501090501050904020c0f0601060e04051306020702031905030d060e25090504050a020c240c1e 69
    0x10815070000743e03030160b0240305480640e0005510301207079a900c4941403c005084009448240000c09007180313409100442e550282c4529840120340150300d949203041042c4901c0d03011407502c640500d40000301110710984004044101b10343d0390768a000402e0144104c911850701081d983d1180034000400181c940e80f00440c012409101d0310400c50b4a8528a080c0103600e03150f281c018010410f504216503600b0642001c00d480d02401d140f40c40b6200307000410020f00420001005074403c02c54250104a0007141c8981071701c103c2e81d12400b84c0900354050106869068500f212203000c801190004185142c1c040d00d00544014141c2e1084035000b001d43d21903910340c1200742d581d900300180b6195812510302c074031002088a00600c4840b4900703050a41840e2281000d0305200760a820b0310788056620414440014160040c030801c07007400e11800401c000c4d00400000301151142c003051b44e2051108410440da44140296029840e0b0b50706010120030390444003000d0550001e00ca0441880400340014013 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946434127 1250 946432877 946432897
    0x90f06030812040501110c0c010804032d0e01030213090b1522050d050a14030c07030c152a110a030f0b180d0503130c060f0305011e030f050a0602 64
    0x41100c0c105414030a0840c0e441c0010103055410800060700c4004000c2923900c041402400d10350b503995618281528025030b2030204802c8841403146d80d07402c6450021340303040e60032142d40e99091120f644400540c100e2089444078074002c1a03004e010403600c41c603600600e0940f0406081c4149950309448100c116411100c4441070f49650014481d0007108402480d400070042100c242d050380100c0e442e61a100d032125000036004e88110700c1c43e610fa001040003200c5902c4800740440d40074a540c1d0030302c1030315500070740900300d041443c5507000d00781180b08803c20f81500b035102c0709210040418110a2410441c69041203841400c803c0c4140200d03030700e1110101c011070054202d441200b085103080c450b011801010305154404048142e40c54001c000b807260400422400c003a550b03521094110742005540034002802801d11240c00b05400398050045443c00e0300360b81b000e00c40d60362150031011001c20a120700651006100a0410200f041090614086401081540c00c1d610064940d40260383c4500f80d86 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946435377 1250 946434127 946434157
    0x50907230409080c01050405100e01110702090402041b0f0e03150c070c030602121816091d06091614030330090d171b0a090e161b0b01090f060308 64
    0x882789508035405100c2c0c076041d081c0020404032002c031456035081c1c003c009000c1c5c000d00c62040000d00f15184d6a0001a0b20881d00c00c03625103c101042008110588201c2240b0000e015945003400341d080001c3c0b00c01400004001c0301149640b180d00110603603311100c00c2c0d4066021800002c0030031450710041c402c00740c0c038007070f144060301e8061900c51500e1010110710302c00e07500c13100351440d110280280300411f6038505a4003007021507039411070b401080d03c45071051085015500a000741134000041011011868400c03100300d581d42e9114901c45201d0604c10705030503800c00c2000454001c1e83d11034030121200d250040400c0c07a0171401d402c800901044460908942c0a00321001550350072441d0384010107580b0b81a0b41c11843d044070781c0300301d041c0030041002d0320140109844c4107682c01003402c00003600003d203001d071462601250002e0011510020300300403070307910340c1d02c20b00c10b14410001100190304560780c10043c0c1d11f13064086004160542c643d118203692440c000c0f000914090040c036260541001c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946436627 1250 946435377 946435393
    0x50a2001090503060f07080901200414060304080a08070c051632040b0609060304030503040c0b390a0501020c16061409010309080d050907230409080c01050405 70
    0x9030035484181c110b9071003580303ca001c01503448030404a60360b01c141c8a103080304c481d449020601d805002e01046101280100d41000005c00c071510018104603202d00010450b02d03103d22060181e581b005680240c14200100220443c0304d001c0c40c04145c00601038034000d1865803964072614242216048041020300f80008100301d03100041a4000068003101030407580e1000c1182d065010110090000f0301881d19040500010342d10001941d101507005000d16581e8174003845c0040442c0e0040342d0844082c071070103101040c031086003020340c0c4c40b04202001148240861500d0308142420500307100403c414010120320381010184181ca01e100e100d0400541c981d40d10340485800c0218508601c03000b03031446481003203d907601c450356010716244090a2541c1c0d40760000102d01405c03203041e001c2d08510b40010501c09035040350384220302c60f90802c030507508529190140e00d445a41e056079007154001d4031151072144c52401e0f500180c01e4034840c850b85454504151101c90030758001715010780c1c441d081030320 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946437877 1250 946436627 946436629
    0x412020f0a0e070e011d0f0d0b0f090f0a0b010603050603010605031009021f21020f1315080c040b130806041208072607030f0f0b0406061e0c050a20 65
    0x10210b010002400c0044840107440032606d8014103c0e01c800c1c0c82541055031045c040d4407064401c6c000780e03400072031600c85841c0200c0303107409a10041d21800c02a00c5105131501404402052801c0c0103a070000c4147c0382c50346040c0c01140646405810f103549550b83d03000000b2282d604124038003412044c8080421101030900402a40765142030b5200320820003070320720a4aa81e813150030406068944102c842051903851140002400707a11600620400c0014032950448c10014426080300c10200000509403071604080b02c1001041d034101803688800d000500c40070040d100070740342042c00003c810038056600c441440c5444001d44064400c003104500e0f02032a240d110031a90341c0603801d800c0280786100210000540d4038103620640c0000c1102d00003003071a0f036100741c001401095608009200001d80981350f034005040d80540380f48550f280c03940020341d050088089024900202860f05100840c1c407100385c48441007050304640c58041e08141c072001440d4035040c101c88031941c120301c00040102c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946439127 1250 946437877 946437887
    0x2010506280302010c0c0f0f0e15010f11160b0d06050d0302030d2019020705040e03190507021c051e0d1404090608010b0a0504060b0412020f0a0e07 65
    0x5a040c209100c15800328541c100382400110441e5420b2904d0b074104007490500804944554000007a0b00540003c00188603441406010994918054120b007a40b200e103490694089089031960200e012110019419800b405040c180442c4075000d40d09152012940420341c4c4030f140d080304110501c003003070844c84078610380305043c0a4582920320300029001910041e64a0007161114080151a900c46100100d810b82803500c030301400681403521291340940d801000c0282060040042c403a80c0b030002a10703d064042c403003010b41e43e440a10301d000300030030340c15040780c11200120342404400c002c0e160043e00c5546080e1076150b0000304d4541c04402c1c40c54a03d0420703052a48640e03c120300444407046120010842c1c1c1e0034101941411400e0030841d0100e101e01e80a5540030116452a014000402030019008568041c0013240c0d0072000d662540c0070002200d000e8041c0c04940b40090000380306c080c0e00d1004601d1003d00052030301c0e070300541c08000034060a007540c0240544160729000d10510b0743c0c003d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946440377 1250 946439127 946439149
    0xb0415110a2316080705012105130f050d120605060a030914070f0e0606040b0f031005040c0509190b030103080c0109120f081e0721060e06180103171c0c02010506 71
    0x7441c0c2060294901701c04040081c5c0000c0703d04403034907035800100b40300001691421150ae40d000000364419000740c10280c2d260644202400080303a0f00e8064840004082d01c151003d44d44003d2040b4284520700b0011001041c4440084805061121801005c0d40303081090030b004080d201c3c200d41c486420120000d040380c4000e0b0096003d80380a000900001303200000b5a04010081412035440340e40d015008140981141e02041d0024079007001c01d00c001d58004010f014244080d101e40010011552028401811610400c85c445405000600004142d00014041603d0620011a9120560311038003050040010a1400b060b0074501c25040940c200100e240d1080124144480468079100b0fa01007100008040c07038100000c5620344400085241398a0514800540e420000d00c0c4e141d01072851008400c0c1c0c0c0241c480c203010145c018041c18281c64040c1a40d9000d0700701c0600e54030383c00c81008150000701296901002e40079070762080c0c124038419000140c0480d80041220b01380740007880610b4480b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946441627 1250 946440377 946440379
    0x16060302042105011b09150e09060d03360b0c0c100201090c0902040501020c15041202060403050d030b04050a091e020402070c0b0415110a2316080705 66
    0x50000b0460b4840280328804880300c0044114040912032070a02c0c010541002405180c0030340780001d83d4481d511400401c01c0c1c4104800c00c0007268400c40e410f8403c1d04450110f00d5201304402c00140707080c00c0040352520080e01c2810311a00c5850f40041d10406807240300101c0341d0700b201e40080d844019010702c0074400142a2501c4003481c06412004041d101d5100444090143c0f50f400401c1300c01910035400b842d42c030340d00400b01c5190644c0351000c24029500074495070740144203840c081192890040b40c4c10704121102c0450701c0c41e00f450310310074a94001002c0d03001e2703911040c03d00000000c40c206200100740c440717013640d0005101000408000403a030014000100d500d140201e194001048001501c841400b001e803420002e08840c03000401a21860700c00800071200c205000034552801400303401a604541030100301c1c1c00144604a40180d09002c2d018003070350280240f000440c40319040078a100d085240992005103200a80c14076004807c00c00180d01304c50f07028100003002d0107000c05409000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946442877 1250 946441627 946441631
    0x405010303023a020c0a151e050d0903051e090a3003051c0203060904080318162919091a18030d050f07030e040905160603 54
    0x1040d0340340255a48850300c016603020034040342071803240d00414800045118424040e0750080001c020080d2a402620442e42c003030b0b52503580110301100c6141c041d0701250000e81e142061384c00d00003940c1d00455002d480c91418800d040160f407450039134030700508103c0d074081d40302c180e901c1501402c55003c1e0301c00960003408001c3d05000058240e40c500e422041103c1da03241441d0b401c404052280d2444401c5260505040100400b02d00d04141c1c112019007901100010980300e0b2140240503c0180d2200b140c2c00b5500040100000e0001141c0710040c41c2c102d524251000d04942603429400d01d01150301001c00615100490104031800041c143c0c012070106507404100f1810580ba9803164a0080030300a0201981400031114a036220300b19203002011071400c0100d0341243c40f580544c0c1580421411b00419151060900c01d9040014124100c10601d94841d8501410507107581c090340c02070882101007041407050a05180e4850280148090160012b0300f0060040d4a400e4807020150b403020081c18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946444127 1250 946442877 946442879
    0x90609210105180d090b160215030106020106030b0f010f060815040e010209040614061b10020d020a0f030905060402060336010507080405121303060e0f0708030c060a0b1203160b06040501 82
    0x3008180079035561180c010211101f08034244000341220110002103444100e000c03000040c90b9078150042c40451340200d0034210309803204480b050b10024240140d210441c95400100041072049410542c01555000e4240d41180c03030f40002020740361010810304060390045204180e624040c0300d030500800600965494440c0100f0104085005000303014201c3c10030001c3c05454000184640380d00518164021903036402030755007500094002c940c0c42400200121456550b0a02a01c181c0003416001001480141da441e400c210060340020038480c880300640003c1c880214544a0f810454003540704502e09032003c8000c00303030840d0802802802000098000e020100f00302055114030090100c2c41541d803001c5071200509030720718980c801013107546408290458a107002c03400e0030b454807010f801e075105559200e610315500c0c002c0070fa503240341d40c1040c00400d492110b40c0d48582841c08000c1c02c030002c0d420355420f40070304542000c0340314202040f101400d1400c02403444890340d4094800c45080000e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946445377 1250 946444127 946444139
    0xa14010f0b1c0212030d1a0108131203110406050301030b06040213120f021002060402090105120c0609030709020307021b061201062019020a0803090609210105180d09 73
    0x2a140a450751040310400c1a00c295181d0104c2081c1c1d82ca140400c032a941c1004c0400c0c40000c00340440c01d5080c050510785807005661003941590f00581c0843c4881d4a42110f5407105000b50305e00382c0114050580d035211a1000c003d110003e88010219605c03080d0700d035851820640b500d4500103242c144520704c100711280c3c24034280c02c44002940c40d034503000381544245103049080e084d50582c0107035010900210b8000c825078009101c51041d407081e10307120b5550341d8550a1121000800c80b80d0340e41c0b0b07080b0040651942c145030000e402c1b42e620050449800d1590341540c00101c0c0d00c265203010050700f021a11004141185a8221880c0001d172102d07440c0856241d40381c510f448040c0207a0042054040d000258103c1d441c1c402c056040c02c40c0300760f841600d40800ea120501c900d00328228019082c0d001c002490310800300c06e449150380040d00c0c003440c3c0f080c100100304041500000d2910000381e004041807600c0424422603100d0120703100c803a5901109480b1a502d403603440229202046001d0301c0c24402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946446627 1250 946445377 946445389
    0xa0e0a14010e0106291e030109021b06062809060807050907050c03040b0d020903100b03010c020a050c0f2101020304020a050f0a1802040506070b060a12110613080a14010f0b 76
    0x204003080d44ca1584444000380c0b00d03265941b034002014030924012001040741e0b0081d074020850701149a1038045a11411981d843c1c03600000c41b5100d6201407220280b0300c803007050008d8110b0420b6001030003501c042d1115010f000311006504801d5440d40203090912003400c1900107130740c2002040c02c080381000c22100a44e9503d100700d002e510455400401e030061062150b07016200c8541c002000c6c1c821065006e00080f00034001620818072960922850034882c44c0003064001d241c5401001600c410500300b0244040c503400700c207100f0340244e20200d500721106d211401c0000d050b0110400582d8a08003801008422103003500850f100c0d912100c540c140075a07915040d801210711041da10741e51140b041001c0402400340b42d200341d1b00900001036081c104444040b1692043c1c008880b102515a2580004694001b511000820b50203c225000174030380f8180021344120300f48043d4084a83d61a01d8905080142d07014085410404c0d120b400e0018134801e01400415003040982001091004400251 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946447877 1250 946446627 946446689
    0xe0a080307050d02191e0908030f180607050d090f080c091b07030203030103061a130203040c0f0339031704051005190302040303080a0e0a14010e0106 66
    0x5200001070194510040354060b2070551174041c0300a041d00c03859000181000d4442038005200c10b2080c6107a8803903a00074208181526221401981014000c8440400740d901c1150006100c919544c102c00b110756600b0000d0218612500c0540054120b201010744103da190308601300f0000c81440911000f0070024a05071403400445800049031292400006044c14103600d11260400005a4070103060300000154100c0344a90301c01c024400a4603215410711042c600141d40c00b021451105100861f02c0d009950060f000710000303d1459901e1001a1080205a100300ca80c04030144211030128140c280c02404102415281207461410076045104400980401850241c2207d4149696803000c4143e074040c0c08040c000743c1d0641102c40c0041c00d940c01900000c213800310b0f030500d40002e2910038002c2c0d40c200d1754580c40343e64690311807410784c0015009058070020036104142c100c0c8040340c0500e216480e00c4040d603000061012040c2c0500742910b44a8000c402425103014420b07881c094140b070507203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946449127 1250 946447877 946447891
    0x2040f060f050711011815110708011107020d080d02040e0411030c091602010f0e21071e050a05100f1404020a05010f1707030c030e060601090b0a0201020403150f0e0a0803 75
    0x80401b1500420021442c0b016000703402d0840f08404040051500b11003401c0c1001c2940b0304940c2020f40e07883c1c41d10300765410041c2da1070309000280080f03801400c0039500342100500c90302225051400c0f5401c00004c0313030095845102c560070316800313110a216801c040906c7c18482035000d4525001940301207040c10001078049240c3c206520103c1c691680b003035003c0c403841078a120f4280150450178130b1007a80e40c0d0f11912166200348038a5101c50f0b102c03076802d04503070364036500c5001802c3c42d180452885092941400c800d4070390f4016001c0103800510244008165011964030016005010500d00ea04a4181281103030420b1546818440940e030341c407108604840d02440d1039030b140700102004a42111a01303004088954640d424440c1c40c0750180c0218544026030f0794100314404060265540c2c0b6417041c0c440501107522a2418806c403008280201000c11050001500c0c02d50780759900307004c0100710120500e80650f142c20f41c8403030020782d008100d40c3c24046002060340c0d8507035454055407840043c10380 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946450377 1250 946449127 946449137
    0xc050a080d020d050a0b09010f03031d01050c060406141303050d0b1c080918070c03031d0a06060e010b030c0f07050717031803030f070f060f02040f060f05071101 71
    0x2500001d80030780454902000d141000d000c282008690700000e480b00054591103034501e90000b007a04c13842034103d04210b9800da039601807545010460300d00002014a403141c10020208002584040100b0196025a2013031800280030000d501c1303010100303034010f03081c1400c800a0070382260229a00038181d9030450041d80700042c480c0d2010000980e00d040c2c02c1c1d0f003044884c61854981d07007032205030303030287c01859002d03928940e16080d02c0c44504080b800071512980030401035003d0034041781c8a84e000c000364107800c0e040510664038541d401440c01c102404c0407662103851300001d0020a909817000342c01464100c420505505111001034140d003e00c5a0031042e421000c21040140581000000d000301800d9400c2a07481c0c80281034a0b031242c0c41b010340071001c1e108800c22100300d030070004220361140031018811410a10f581d51224107041042d5000c0d640262500d4484001c40250320040000b401e41403507081015207050381c09802006008010801d00605224190100e502c044000c4440100fd20345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946451627 1250 946450377 946450387
    0x203040513021612110114060a0b0304150219030605060306150c0709020406050306180103031b0317161b080d1d010e010606030605120a2d03020d0806010c050a08 71
    0x807082e0720181200501a8803805150f00c6a0f0707a00001a00e0301200c404000380849050741d107c0301c1c482d550070303103420380c01ca03000031010802e15050307401035500b251162081d4040504515800c0042c1e800c5100c0710564100300c2d20410400640610500340101801e035092821403605600188003503040340390601c0c4028002540b1582d001040c0706a101030041c41004540300c80d140c036001062600111101c5000d01c40300702186207040c4c207d0b080c0301c0c120382e41a590144185a80440c5600d030b004064411020300c03201c0d85070043e080d005040d8035442400b080a0401210a400e03800500301c0c51260440b4007002e010650841c08100c60700116210010014008550607443c500031504016922010000c60752a0006901c001030040d0403000c221262a6020700049840354100b04600c0c3d26408000059804000100d0000e1b03100c030100500c048564401440c1d02d0440c40c1d41500041e600401203006030403000840c25065000b07d00c05030000f000303181c8003020046940d01c3c940d075101d0302d5202401d42600890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946452877 1250 946451627 946451647
    0x61701090c05040f060e1c020f040e07120807020117010e06151c0501030606050109180b010c0c0e07080705090f0909030f0708041401110a030305100510180501020304051302 76
    0x3044800402040703070003641c9030359110300042007004801c00039442808a41c480c0c10b03c000c185e14851804235001418030b000309a000341000018041ca0640705124010038000041040d00c02031001728442c000d00305035540381c9852000403c0307816083c19001070410340d140180004c00f000e42c00a50301c03540948030822600c04c0810851018084d5844c108011400c8840841214441da0042e40c104c1e44182e60511080e0b8135280103461001050169040b800019071001c0401c41140d085480800410b05207141a21450346404030360400c5600500401100c40c3e0a108005a2200300c2903805851858031900b413242e01c60001c0c0c50100405085482829180080307000003000340100d66036a5183d40e503a950321111440e000c08180c10921404c968680010540f100c194011110748008074549005441c07003200a507801ea0041c0009001c02da080070b1001c03000b260a8039881c2e04010151b45030307110794031409092900d40d00109040e80000d41190020b00040000d81c4514910320100c0340986d10150300da1012741 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946454127 1250 946452877 946452887
    0xe10080703030c080d110901120605010f0c1e1209061706010809011b030b011806080f1b1b010513080d110c01111918060503090c18060a061701090c 65
    0x41205c64900d28003840b02450201110040c83c0400007a242c1011a81f400801907044803d10320030540401e41003920301251a02c1296a082075511a4907101224042100c08506802c2090301c103d800038100e0040b550903d4120f00d0800041c0402e2030521001485ea4200140031803000d807856062203900004030301410400c1d0001e0401e0208c4000341c6035520721822005000d8804181c1e5036003c289488080c210b0010080840f0003a0341c4c054440211584810146d445412001404c1d0340c16844090f01c01d106012264005103951940403580560303940c80c44080d5421180083c242070401005507107000f002842c0307901500d80c10011804005520700c195003407000c0741d1284a07094940765103441d072040840890710015010b80915860f41c5c40341c0420108042c0e0f101400a188092078001c2ea290410801d4400c5c4000c40c3d10940c10000da071103000e140c0011030b0780c030741c0d0f4841010310364a8404100180c90420321090b100070641c40c60503950f1001b41e01c800c13100015040c0602d9048179101c424590049002d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946455377 1250 946454127 946454137
    0x1090b07080a051c150614030105060415090305070603061701050411040b0a03051204032a15050d150303020c0303070201090302041d0d0503060301050a3b01060e010e10080703030c08 80
    0xd210103100004d158401041452060f000b05004600d6802a80d807458000a0503032741a40c1010307148a2400d41403e0140c0d00380300c034490000c800c211b00890b01000046043c400c100007060300e6100818413606201040314bc8000e105000c440981c0740000b0400030030b81113001d5101c01802a600000c2c2100e1900201e2461000d580010748140f103060042e00f0b0341201c6000a10071030f030040007040d00c0038004c80031003551803120300c1b0710440d00d00d8203076011301c40c03107080207880c0c0a61144c1d810203d03d0b100e040e43c0b160040c3d404581180c0c100d8524054102300b0f0503014001e202da03507001100a140f6000142c0d0010b0301e00354070360101a020b15070301e1404803070200d0700c603030282c0c110724024080315118110004000e0041d44121541030280d401c00c408540030744100c0c000e41404d00b050b0540460300c6464650039207804074503420020b09606d0340c00d1402c030203c003082c0b081002411480c22180b40a41c1425000c140c02c12028001d24950311a108040068000104041c0c2c140c1c1e605190568802c600c44c10714114078066 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946456627 1250 946455377 946455427
    0x106091d2406120f0601020a05030f281d03030307200a02040207120e010905062b0609091a01080a0f031205160e040e0304120f080d0b01090b07080a05 66
    0xb000804070350801c00081118401e42d0008812074017550f031440126166140f520b8000c0081c3e00a0144402d081c04480c00307080c100d035800e41920103290445005900406901c100a4082031404034140e650042c50200c0500340d81c020380c0103618604007100000c06c0141c0b648488102003820036105405040240584401250014002d540725442401c100020b14411136a00001c117112104071000d07540105c1310360007201d0000340002c1c00d00d08414107554860012041d50f00c526641c0e6408050b61071003d100d0000503202034240000d0311400e42c58001c500c40b080b44140258005100c004000780c02c40024080c94940e8010a444034a1115240a64640c240b00f45042201c2c0d00345020080440280b0040e140e0307120495840360140c4103600c0070310048580d800540e0b5490703003040106002521030303400e007010760b140f080521040050060b1212451a00548402c0c0e03000c507101e0f082c0100542e48101007401605841820b64034007640c03550b903000d01d8800c3e201c070740d42405404600744140100c0088d10340e0042c44 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946457877 1250 946456627 946456639
    0x304080a06021b07030809040b031c033c0e15040813050d0309050120010e0d0e270717090606040c050408150603010207050d03050106091d24 62
    0x11a80c90701d20060b40105001240751000010a00350350303280000c501c801c8076001403c00c1d01c2c24080302c0c00d000c040d25548038800d40503c202445070030003001501c14114080255a40056600c100488d00302045040352503c031820070303290010020740843e15040d00b40c80e000710040004c8103040702e9400b07800d2802c490180008201c558041005100b00d000080c0080c019924014824076120402c02429040303e0301e002d00090702080d0305110a5000342503402d100420f5a00b00ba8910781c14414070f900391842c101c00e140c40340d00101c126003000f03070300003650352221103081721100c80c2165561601c1101ccd14035007280d00c842c051004080350107540228548508000750345408605072500490b19075032543e06854040c0100d01c2c21903205c100520074070944007035411060281c014030003018040030858601800310395155508203d07180c002141002400c41d0151140c801180320340c1f600d48064a20350301688480602a036a805001c1101b403070140340d6900c59a03292520b9500d0105001d1031510300d0086401c6030f0011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946459127 1250 946457877 946457893
    0xc050d1a10120213021905040e10080a0605100308071208010504291302070b07020708010c0f080711060903071707050c010f030b031b04051b0901050903030408 70
    0x409200d0104100201400548440341c940c807801c04500c205074801d182c203400492119400620306030030480c40c0070030008001760500000c04828201c0042c00d450010104030b000504000645110541c01d070f00c64802e086110003580750041080d116085a000182516940c4000820410300b002040f405180c120501c10b44608283c07400c0d903219580340e090340000c110881d00000d018a003e0051342e5690b00d4005640c010158501c0407110240411080c00740c0c03020884e000288035020603c0070380f0010b40581c41c40344c01c038100300f103020741001d22a801c10046a41011203101450350440c2101c2c00d000c000d883e06400c6135694240466983c41c41140c10302c224000c8a05001603030386c0000250031554000c01041da20010a2079050b88548036411004003d03800c00008080c1c00c2d0301490055055a1040c140411903150100010707042c4942c07c550030030a200860341031441b03400d15101e0b003680080030b014000d49140c0400c0c00783c181b9010300244603040040c0003542001c83d4a0900c2690010040d07842290864 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946460377 1250 946459127 946459133
    0xc1002030730030f050f0403021b01091805161103090f06070209070f020106080307020a1a0d02072001020105060d1506031704141903030c061d06040b01080c0109120c050d 75
    0x2419411004c04410703820701021a1a2002400d00070380903545c96002414582d002030b40b01841138105900c80c80c18000740020002d65815007030081d40010000110001d160310f05080307d5081300070304400d800104039440c1c01ca44e140c1c990000032200d0b00c10045a2400d10b4a40c241300181c902c0c40b070300c00300a4000300c1e1402401f141c0da0308104d0b65816540745030020b00109850740e01295407801500d0b000307540502101410441d01d2000755100b004c10411021081ca0324550003800000c0c0d9102d1142240c0c1e02c0310301c000ca500d0380700c07035003142c283c001c1070134402440385041100000311080c50201c13002d0a00d580400702e81500c0310341980407000443d84100704681c0000303d0719006441c0d41042c418030352000c4050744001c9080c68400f201700c2a040d88003607040d80b210b0964034100e41c1d42950390b60032100d0301d5517000c56003090011400c0e0207400c0060200180610b20f020b20380800021010ba019514690014044a54036a042000501600c2e20003c040b0301d58052414001d42000c481e9210b00d4006d07103541900c80034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 946461627 1250 946460377 946460381
    0x702030a050d0813081b0a0507060f0806011407120e0406030506010e0f01032a3204021806030a0212071806080c1603020a0b01170c100203073003 64
    0x5000304503141c82d0404d5031040001800c8491002004010000c1040f007404c5c0035030202c40301e907080300260044555500645d035401d032500d98250000c0c408150000c4400d01d90b564800d00080e80a0f0003071900e00b42c2e140905d01482618080c2080041c0b00002e6041050039503845240345080c245002007044c07216507640d061440e00c4d503000780945200540b0340c030005040400101c0380281203d03800300c28111282801e480e003101400b29050440040c1144400010344421141910404990107003000034456030142c41404100c001c038413500d800345005001140c1e00c00c0e4400e224005180303080c3c41455403171340c544601c81e0003442201c961403000303000e10b418085225444001c0d20b160101e00c107580b40700943c9441c0d05a48841c821100c6812034441041402c0008010004050400380709004941b8106215a40d1982200090300025101e620344a40840301d03c904010400003800150b50310103040d030000f10001c5d124480c00c4000b07020120031494000c040c1e030b184510205403020191030006811040900200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 946462877 1250 946461627 946461643
    0x3010f0303030e01050405030703110307060f050a150e07051c0f090215190c03110601060806131104210c030b180d090603050c1215010215010e0411060702030a05 71
    0x30320b0403d403442040b03814840e140c050350f0420000c0d82400001d903000c546151100e0010f100e140814048070b03001a071035000e071185011110802292502c0c3c242041c50440e0304100c5000c20707020000b181000400f002002240c2c1001d061319040c0d40d151440340c8070703140e402108801e000049181041d04020050141d1003012070324400c0312106030050b01100321002d18000c18a540100b1850815500303101801003607192034442c442d040600901808164403806d00300240e2040b804204480c0c00c1001c03d140c0946500045089504100804001403859201c2c5000320302034032941c48864204511400020055028100d038007014204846841c0c1c9030820340d03200142c0c0c00c50701c00b4603542c0c03402942c41c0c0082920440401c00d80d45c2d040f400c40c40d241c1c0c00c4024103005041401a00010001106143c010b03c60741c612441d040410316050032140000240340682c90006420681c0c01a401802226070401e07019800c03640151491101240d00400181c0701c0c8102f08000313506101e9514441c0401c10041313142c407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 946464127 1250 946462877 946462883
    0x20708042c0408030118140a14090a11060714030a020a0204060e061e041b020f120307050301061101180318090c020c19050d0b0a06050d0f060e0109060203010f03 71
    0x205005050600c5462010300c2690001c2000f8414001401241c1101c1003101c40c405141030301080100f8002031048462200351041c603886a103c2029883d500c1240e03a1240e04240003e0080400d510640c40e1402c1c88210b68480300e00c2080001005401d1011031400035600726000c105032a50b85410740c001035928401e100089009a00b440340004a00010b0087c0e24821301e0041c1070b07000158202441601c145400201d09079002c0c1e51410076002a00c203605500b001c0d620590020710f0040e083c0d009841c5000311a24083d0f040a20801c20003547c55404001c4e41e044175814200708510740003001c4480d000d4690101c400d40c400c0d00c059030308011715a002482c080040c004419900c2015281c02949054407501e1100c00056407264021000904060703040703c1400c04e00c2d90040f52503907280c1001900c0030a00d080103a92050350101440141c01140c440c80d40101400c17502c0c81810708043c0e80e0031550320003919010703100aa442000000c039035020b4100c0c684103580f00b4021540c3c0d40c0c6601310541021520b000c19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 946465377 1250 946464127 946464179
    0x41a0c01050105100804030f12050108010b09090705010c0210050424030b0301050c030106051c0c08090f01050702060c071a0702071e0b0f0306030703080313200a09020d02070804 78
    0x1c1e0b0b414207a0244c2d030b50381c400d55a603d00d6aa038546003a51070f1007030003507205c0400000c410106200c1880d0300c5418040d00c800000411000c0c03102041003c000c002400d03407a800c3e005144104840da03080a51800d81680c143d42c0310f19880603064040e603ca00860b4401c0501d007400343c0109007035102840055103400078545042000003900024142205c80480f1105260f60040005219442c0540082d0a000c415440702e007942002c508105030960f9007148806c1c01151503802030100f4184103021416440c1e0180008000d145800c010003561460042c08003582c0000000d550814041601c550b04244208004112002e0518443c001c1d41c0c0c010030710034505192030b00400e9006011007140380070201c800908000d402c2ca001c140080c0d02951015080542c58420f541c1c0005c0001da4600156100300d440034452034500c81c6900f0280d0500d2140402c240030307600700d44202d03006562400444403d03240c1d5035100603210704030008100c00038840c001000d040a8070100700001c10404c940c0c1e201c0354104500c855 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 946466627 1250 946465377 946465379
    0x90f061206011e1d01261507031805100510120308070f02030c1216050a0818120d0804020102070f080109060b060901050f030702030f0708070b0105060f120c041a0c010501 75
    0x4004480f9486901900a910100400a81b24206c480b2a80c001d0180f801070340040100500500d080440d0f058101145105d0041201e1181c01d403103452103140c1c2c0640c4801c503101381030ba600c03500c03a00d400060b410b80940d81c001242000007c85c050300050a460240c1d40154411070501030034401080310500700040040407451240d61010041c0c40c4429500c500805802c0c0c0600740c4503d00e90031218031810041030303001410b40828010440303000361500801300f103030355543d0b114910b40000500e0742005004464100000d0800780c000201c00070740b55203516040c84652100d10040b801d140e041d50201459003149000464010410351205001c244a49000c101c03228118080c010030380118402c1324007140c003d2100f8003c00420710021944500284140c0346040c000c0b01d0050155040001c0545d000803001c60220104242000040d026140440c3c480e41001e0031840301052900c03d143d40038003513450940100d240c0c8404e043c1074501a003c5500100345a00d03454205c0c1240d030300a000004055824840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 946467877 1250 946466627 946466639
    0xf020f03092b0e01123c140109020c0106080136350a051b010614040c050403020411030601021209150315150c011505090f061206011e 59
    0x61002c202a45500e81841c07002c01c0f5070040d580035002048080c00729440307101c1d1241800d030245501da0b5150304152100c440c0710f0210400108034150400c103510f21840c040a10042c000d03650f002c02e04403031000c40701583e6038121001031805420035501c015201d600702824031010944500c032004203910b001c6280f0706d1907400b0791074400c0010720384080503252300a04c00f5107224203902c03150145400300300b00c40d042000c550b20500c0310810f580000d0300940021800f04401070414025a03d8040c0c041741007000b0312109042c19280140c05408100043c400d554540c3d010301c0d014060400d440c02103030002e00c100810400c0d5010084d40c3e90003295240d005015a45104100603100f0099400144d00541001400f56800038402850351001e480386412464420756003025a451481c0908080b207806030b51500c0c2d1b00700d52011030a45010b40340b6601c40b03900302c45050009841d504202d07a80702001090002c5240c9468003c246041201e0804841031b029100011506804402c026a4105507810350300d043c0b81e070341e80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 946469127 1250 946467877 946467943
    0x504050f1c17040e07180806240d020603010b070c0f0605030708060d02101106070201020a020c15120103050a11040504030509040b032a0301180b04060f020f0309 71
    0x214400a060714071030420000c111501075240740c94480000c2c2a280c661107482d50f0303d640364102e404c2c40008000710403211140b81c07071400c40e800401e1079070028842410403e1400c00038aa0b850112040001c1c0c640009000b59030308010038405d0b9401821043e520358681041900e00d0380042001d481001c081000000c640403664502d400310f42065440e207003141c448060496513000c024042680c4100562a4140543e495121607101c40b200350b165003c202158070400c5041100040c40784c0700b90391040c42090700c00c40d00840e40c20a0448200c03425511007501c160980f545000d20a0f040c0d030b41c240014004000c001c40080c940035401d0095802026442e200b808000aa80c0f04803402000500c1c00c0c0240d1b0f2290030140c0040c03401d50b01c0182642c004189020222481c1c0341d42c5003585402039000414030350359003400e00ca07007040586e0740000215005003d0306c40c1840c040026000401c61035a4455500c3c0e05001907043e210390520f0680d031181d890801840e9555a40c1c0c040400e122421104e5180e030461036020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 946470377 1250 946469127 946469149
    0xb0309011d031c060506120a05010e0606070206130e01120308240405060f1e09060a2d081006051342060f02060702030c1005070509030d0504050f 64
    0x501e004500d02403203081e003c11855070050b201c0910350b484110101c0d40d69900300241c020070308a0311b01c0f40101d00e4031554003070aa42c0181d00620040c00303124140b1459484000403640c965406a46999171041c0324040091401510f0f1b1014171403c030400000704203446101402400c03070340259030703081260301c6009001c004181e8603204003190b600c020b01f114016003403d81040d9030005004080564041c16980868110070100030050031640c00003020903040c1c60f05c1030403d80c0000c4241c07000740b036440c106001c200030f0315101650054410800c20001e9003e26001044e000500895415580000c84515844020303062601850f40b05a0074950035101d160304900c6100761400b04c510244401d10a090000b0480c0001c09140d1060111500e02001c0c0881eaa07036008002070059a6a544c00d0001a002c0241400c4000c0c0a520864000308002c800c10302c0000f80e100001c3c20060742c00a100d0f114501b0030342c0d842c0f144906a40d054040c58040301c08042d0081c001d041118401d0302e10440b50002c06040005070944 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 946471627 1250 946470377 946470431
    0xf050607060e0f0a0b060a0e010b0d0504020307030f0b240f0f030309040e0601171504120e040f0b031002040b031f031506180507020c011101060902040b030901 70
    0xd0000d0004102070340c000407081c10582d010340b07a5150078090a107007810464801525080785680a014160a0012051006154105a2816550500442910034400e90401111b2b0035205c10109065580c10f004200096070f002a02407100941850710b40c0161404945591140c813650a11300740103d0020583c100f0071000078621507001203007004004004c81c8154141d9054882400b00c1150382e01c0f54468620007142400042c41e244d03241c621410240c03d0710a42c0c3c07030640d0f0484c2080e101c6503c0240001d94005500c102e41500c2d90034204402c84030a48203519030b50307100d0700f0141501b010340030707c8c0d0255040d620190309443c0d0b103501100000c1e09a120304e2103822070f402401c0001448508007000c0408070149450420114107699490f987c003a11560031105400d155a408204240805455030000418090006000914105c1400707504c03480c0f1b040550f4140724503010000c07000402944004007030411000304540f51526403042d244c198004a03600b844641c60005100b03041188c1e41d05800c3d29550f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 946472877 1250 946471627 946471639
    0x5010e090604110408160f1a0d0209010e040207030806010e060c150c070203010905030334030f1d0a031803050c010f020a02031f050f07021e1507020c0102070f05 71
    0x4078841800000c00c10a60450001e55040c8000310b5074090038000d1400e8003942c0801100c8284c184103103807001c081d0030f40c05200803460802c40103000c1050130068039071030900e042c40140c441c030042d40141c42c140c1d00750301c010f036015200150503400c2640001110303004200070381e10502d101c8280340900281c0d108056181345240d100013007401c1c40052a20700a44c0c0984c41240860800c10707140e0200782902d81e2120122010f80000c42001508600c51116510140340c2e1610301c804d461007041e1040c00c0d4507021100004040d00e4500441c1003800642102c119010721031a07003041c0031301516181d601c0c1c0ba6050800c400240c8a941070131000342c00c0030b5100c07050300d80000180005001c203400648440c00018040c50550042a503130b0409a85e007400b4800007090210480e140440c0b1741e41d1400101d4000629034400c100301c56060102c2c80364006030341703141401110003503082d00408489542c58201c0c2604a480007085203030401c6120343c1d0104540b40c1d400b200b03808440c51076884401c01400701c00b4501a50390814 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 946474127 1250 946472877 946472881
    0x605060403150c1119290f2a0d02070f200102010506090117120c01050f1f06180302060304050f1203090a03140c0610030c0f05130207110303041e05010e09 68
    0x4c000000c075a4030843c0f00352101c450700c12400c0300484000001114540c200084142000100c002e00c7c1d003030783c0c1e0014a8000c000d200700c10980d008141006180e0000c9003000c40411681310446613541110f641d241c01800310070810402e0301e02084112011f0040e001081030614007211a0b50050040c0e074011000144640e1880c2e00307007054a900b4050882c003030b68a61080007003440350041039100421000110304000b00e59450000b00c521810480603141c08816241e1000c03013202800c400c0e42c2c140c2a00c1c0c0d14503002c00503010042d4800c00d0f8076502d41002e5480980041480308006000a000c0d03800b4026100b41c4e407160380f08029082d100d001c102d900314070f42c1d00310003185000a4420781e0300c4181c81c6003449401c0d04007691000d80f14644042201e0b02ca602501c0035006005204c40406603800078200c1c5502d91707500e5410b050219090080207540c0369912900401c204080201c0003004540741c40024048070744036a500c2005001005001e500420b904102a030049602d51140c07001045200300941040700039 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 946475377 1250 946474127 946474153
    0x7030e090a02071403071e0f0b07090f080102120f1603020a020a0b0a1a101205090c03060f010f0812041806170a20010e10030605060403150c11 63
    0x240000a19400341180d08005a4000411070b64a0031440c440070b800035030310b0324564500f4000d807a240c1d0a400503800201c0487c50001044250381b288880e40c032824000c49500c0d440c6050341c1e1411130b80c010011003030032604081a00d24056018050100c114030180d003594551595860403c10103641d1507240c4842030f00203610b15030003034004100041079413040b60044011038682c0355900c2130a0b00c4070007130070f52524240200c1c0340805c2400e40c80c24604960b1240054007603000540741c0c4040b01071001c0102c0d10f940021740050310610030280b9012003d0306503940340ca0940d840fa0990a4240030f00c0b075120030442c5012071104170019480c0d5101005929161030a03092030760744450ba23030b55143d0340240a9104d02d004250801c482e0250109005c22078000c0c8081a074510f854044021040f00c14980b2901c41010840a83c0e8048800361417014259203031142c01042c490110086d120607040140c1141c00043c000042110300314010003030f0341301c3e180100240ca01101045907000c09410302071810b68402c999a140c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 946476627 1250 946475377 946475389
    0x1061703271c020108060102060c16050a0c060908070906062f0f060105040c0e030706110319020a03030b1815030109150b0424261e1207030e 62
    0x24203038203411100c040401c02400101d40c046a00b0b00d10a20b038407948030b61011540c222141c6500014240054201c1c4c2c50552a013040500a12000c200d0701e4030707040010024082c041c04204c082c6600043c9101e05213031110f80c050301d0040d040c413842c070891003003000c001480c40c050f05c500c4080d148590b60f088181d038900d9540007400b030700340142d0341045441c4041040c950141001003000608400d4050009580361500700000c4075400d002c07460600120b054100000e680124480d025210070f8184020b0720505400d1481ca14011230b401c1c0411240601d5804a01c59000128401040e1217541e0510213061030320244001d500b41d0320f803a8a01800d85101203040d804180c0d555040d03901025000040b50710240d00e41600b403602c20089001541e54856107003586007041d025050610454094010410102114201c8440c0703851180205c04001e50082000d0300303080d0006128205803c60442e41c8c444103c4960200558032590b028a05101e4426101e0341041d501d415101180d4240c0c44803069020440148a0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 946477877 1250 946476627 946476667
    0x70f0201081b1e09130f0b06071509031403090a0507091b0c0204020d0609090c0902040f151e05120f06010e040e071d15011706040902031507020d0201061703 69
    0x300351501303000d020f605440360304d056403015408000119240c1075130700c405401c0b40c410240280c00b45000700203200114801c240e40d400e07499006e030350010340140681011a0f242d111680c08030b84202d0000244252071100040d24081a800303003095900c125500c0403400c1c1140c540454042c4003005150041940c140100381000714540068070140c5460309030452070080710200d800c01308956503510582c4040c840e031020300c80050120f81e0000c520741814140c22107058a00c81c400c5079802141011030095040c49228548a100e95a5183e200c00005012010b132003900010740b1036211102050000d65004c0160030781c14002c01060b101c000d1503041c03c000b0f00000d0f08140c20456207a11a52000058481400c442031500704d010101010050804095040f107620401049504028100c0600c032400345034610180d030000d204940008641800c1c0c4082400c120091601822162014003080062500030078110000c0403164002c100e003a494135441d440321003c03049000718a070304c10b00c58291100c0946e00016 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 946479127 1250 946477877 946477927
    0x60b0405131d0f06060415051e030d030c080c0703021203040c050d1a2505130305060a0519060b0337020d14040503070b0c0c06090d0908060f040803180102070f0201081b 74
    0x3046049c0c5040100e8074105004008800299480034421401944110101c0e000144600250b140100c685c40c002d598403030082d06400f61000000c0481c1c2040400000700c4002c0002404606160190b81407003001c507403054414141d110362060000e8038501c2e20506201d888400b0b00c8075030740d12040c0210100c4154102800c040106907000101102090042040604c00c00b01040c022a0031b1500540f2580c80c031100c80c40342c20303850b8105a0240500c1203118162079100c5c80c0c0380860003a80340c1d00c15441503400c08a00b0410000c1c01c3c3c3c00c04040180d50650000c15000d060448140000388010700400411001124003421a1f0401d000500004e21103034900c60700103420b09221401e000c3c0320041c00d41421026100d400c12070b404541d10790189074000d28524018013022000c0c00103840d01c1d000400c1038500c0104000c00c40c0e00f0001c0081c07a2800840341011402e6000d400854a400c110b190103094000104016070105401a0015803d042c00d00100501c603810012042d0421a822400008509800f0403030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 946480377 1250 946479127 946479169
    0x80f070e1206040c1d0712020f090d20100804061812051210060e040c02160b090a050f031002070302011e1e060b0405131d0f0606041505 60
    0x1840300d840d08002c0341e0301443c000c00c0650091464084020100c1814460391080580c148040060b055089910101903030740004000d130396102c155038103100c039208441c0d40640c0010400c10200c24040b801034464040032840c1000c1e1b509043e17010401400c0c1310448420381c0003039180c0d0001000a10250441e0510349604d241c49044404169110100b0040702c0b9015000100081100c0f444c50071061101e6801c825140b070303514403072414001d00604548951291a004940b5884101d0145108004141142420740e0141180503251540c2c0c0200c0d6020a000d14410120550301140e02d2410030324240303000342c00800030401d54143c01d05142c0a500461400d90039550303283c251026540b0403e2454018030703208800082d403441e001d140c45600111030b00c0c8499145181400c1404601c0c058412102998800c88044e00030650410004024003486a0500b000400d401c91820030241c0010b582550b4035005410b0340e240d55070f0f50007408212500c07403000020b0040701000400860800300309503c0e41012440a17 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 946481627 1250 946480377 946480399
    0x90411010f05181c06110c10021329180a0e07023406080406050f04050c042705070509090c060306130212090706020115051809030d0903031a01080f070e 67
    0x1031482103600d005007100318050300040707d44203c1d00500c40b910102c1b01000b011030800d80c082150507000030b01401a082410006a2102144495032840710b0403c04001c102550b80c8241e81c109602c21740c000800240600c0ca201404980d0095605245100b0a01030303000b40150801d5103030032005085101d400c07640420310503a541e13520740d0f03d52120902612094449804070700306482c014003150001409a034070501e1910034000080d501082680d075114048401080055560181ca081401c40c00c2c4004050718100408800308803000c524203040320303003c8450781c003646d44155110344c88010494600d640480100700064051401106000d8440c091200060820189051030100ca0100792404001d40d4071651080001caa424041e918490458000f226580e900c2c10300480c0c0403e00c412041482e4010840010303411120410940301540c240c8030b0248a514440e040207802000e442d2480c41e00300a2400102c001540a001001e0003206c0d2000001020b544400040b5400c4010b249519480310340009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 946482877 1250 946481627 946481633
    0x13080c070608010311040c09031101020309030a0b061f0e1314070e030607020c03150604110304030512010608060105070303091b030506090c010c030912020a05090411010f05181c 78
    0x100c1400901829100c100e099411410442c0010000c41e4078540300310f0034400100700b40d90b441820103003117a500c68002030280e894100140e0650017035500c0c09815100700c5c030014040c001032032205030058400781c4107404c80d504400300c4107110006205a00001c92a0520308400c1410000c080ba4070b81e4141c101e00285c0180c0006035001d0704007040d900301c230000d1400030020400d46810b12106420044d640000c2445000060210391034500c41f00c0c6181d181c06900303001661075207580c0c20815040d661021920303920b10f014035020700b0a4111030f0b400711400c03d4401c00403800e03034040c840560003440141c60f184d0415010b6079046010386188581290300391a40c08160b8080c0301090440c4c40614480c05c0940b075946010540a0b140440b0340e03c0791030402c54408248000310b50010420070030f40d21a840c0c20031840346240003080310214507603c09900a40807404000078003881e42d003a0020044c090340c0f00c0303104603503684080320b241c010341c40300550558281311482c8884c0f6003001100c400d085009004900c81c00180c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 946484127 1250 946482877 946482883
    0xd0e030a020a290a05061516031101020409020a050a02060906010f15200703050c03011103061c0f08120601090f090c110a08030702060f131112101d03040e13080c 71
    0x5135101c03030f119840742d090001350701d005001400840b161410250400b4000041d11003180701c1450040e00384051002c080e007d12800b9012603014003000c450a55580018080c024121350000008400500800c0013050b4100004101c55040300d419101c805009810008100400304c0380344058800e1182603408a44c000210718104813981080c600604800b500e0350074501d04241248442c40d129074940b03558a00440c0968068941100c0d0a540c0e00d100c4c9008981d8004000b0425400600007805000c0100c00700403886d0004d10300401c400c5040c1c03034103486020041d030b54490b982c0503c070111b5082d010b0500c40103404d0b91055024180750329140f1002050f0402a60902c40f01490607903243e1000070800c0926601005100d40082d840c210103070180c601400300643d6180c80180003442225418106921651030381d0307400e0103409184054903032a82c3d4044081c07004200903c0800d00114148410340520000403060310111138202071419403d5580302000c102d00301400b442120b80070418091489001810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 946485377 1250 946484127 946484131
    0xc0c0a02091611010e0304150c0c0b27030604150603021201051006140d0c03020405040213050109091e11040e1009050a0c0c030c060b0310020d0e030a020a29 69
    0x1491006904840080c801040c00f1941c0382c421845a0400c044c0c02120100002120300301d4500113004101d141034090f0856480118000241c03074410b2000d004204010100020044414050030440e4086041c1c001451001509003071a40e25411880015010400d403001342c040c5050f490400103002510b0303900061004249100a40c80c0e0b80d5240100b00074204120300c2c1c0800f502450509059042005540b03515510074040340c940c0441c2c80d02c5428985c24080d805980251200078030954841903500080078000600748186070018406000000744a0f1090ac101c81c601a251603460501a00512480c40a4408000300400d005020030000640e464800c0441c1d004c4c03200ac130740d071901c2c19181c0f1442005546024102075000c40c90050040d45582c0c20191450301c032545420041016182810954000c040d0303901a0364060060a2200308042c0b41340e07006050902d0103a808010032908079080c80e94a0090044c0100541e1112008201040b003d00d01880d4503082000c11456000c00660410408030003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 946486627 1250 946485377 946485391
    0x503090604030b15040618020706110f0c12031902031e190c05090a060305090109140c0102010612020603010e180703030c03020c0316050114090910051f080c0c0a0209 73
    0x2e8203202c0c038107913140b540d04075018080b2800e01900c0c0c1441c80100000007422600d07040c081d400100c1d00c0821210340c04c8080b0000c40707442c0c0161104054442c0c0c90300c0f82c2c44001010001e0152400d6082103010040680c0d02480301041c04511100001c12240000c4d8400b400c40340f90b0940d20804040c2001401201c01d200e1041880c02c4030100f12001018030943d4074406c0948c2c00e004090203490510f480d188140b6085854914010440d612410403e60041401c601c002c0d005170002101d2240345080040c1c0c9004480d002c0c1e0081088664811592004480084c03000394452010401007000100000185410a0b118031001c10390301c1a03c12280c4c0340500a9000320082400b600c00c1d98180354041c0b01701c2c1a03018050700070704058608004c450a83c01503d000e0766040c00441124070300c170301d28007200350341c00043d018140c1110340c18247c40e40010340807144100740c442d000e55041030850f644d0305416420003051645650010362240f030040071403030308400340000c501d2246013071240260307564164103405020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 946487877 1250 946486627 946486643
    0x203030a1e0e0102030a031a092d060a1401091e0320030d180e1015021902040b0402070f061b020c030a12110d0e1921050309060403 58
    0xa4004540c9081e188141c440c4418400522071080281c1d8022089424000c9140340016820389403d0040e0040740c0d0000c0180e800140507000c02c032003400340c0d40300e112a41c854500030b00311002195a40c0c800c42d1404490268200349014010008240108140c0142c160141407018005454204441040b581100c0d1030340000f005000130810700010248003032002c0c40355503144c0c5070b5642d1000441c0e41c68105c070740040d0400c10501a4649030700178104da40c2002e0480460f20b40000c0c2014620311500060310300600450764000c801c03245440340001a001c0003004922001e14045000f5001c0000401181c00f81c2d541103902041041c000502e42898000c20034840c080c00140450b0600c03c014000440311104001d40d0f02c84030079441c03942c1c1c000a0078504c096004015101924842d0b0041324000b0255030356a54911541186e000d03055089151090404016111000c9288071003901034140310544c070400c00540c00700c004c42d404000303413103524802060080c1c04482c036000408000c240c196000307500503101d0300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 946489127 1250 946487877 946487897
    0x120c0d0305090f0103020703080f0403111006050901061e0806030c041b0201050a0509030f070215041214160519030503030106020304090608010504030e09370f15050103090f0203030a 80
    0x40703071107060320f070704903000386011400d11703010f07550107841d01d08098100e01c010400f000c00281014451910080211a00b41c00e0300c5501d018540140c2c064150360040c1c42c0300741e040c000081891071140841210b01101c0340c1040c1c0d1000564071043d50070300e00140520790140981540c031b40d940e46444c007030031011106002c0c80a407001c89801000b821030b4006040001014108824004180d4000050381c64404d4429125651006503200003115400f00030400700c801d1501040000c2da40e101301007140b40c020f02844200008811380e0100c40c0d03c032920034a030b001500030f0805082c8203504100001c51003c440024420b400030361243c8459107503800991240005920001d82400b22007094000d400040510310004d200034240760f5800b40c01c40c0c00110405020f0842e4070700042c10110f10036416074150b0042800b0b007414645191a0701c4052a003182c0f80c3c031360366003810045402030115201c2c03010519901c88004a41e14140401100604010b81c01900c01c030007640d8001002d070b0b6040c0b00415046481d52038509541e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 946490377 1250 946489127 946489129
    0x712080c15090c010509040b1306050a0e04080313110409080a0e04020f030121060c021011090a0303050904110301080604030e0102030a1d0d2901051905120c0d030509 73
    0x9001d1410103860122000180030141c1d20000700d4580c101d00908080d516402d001e40464010100d114600d0ba10080c43e0244030085002a4404001c3d039000b0358011214689a101900f82c0d00741c19500200b21800400c00158140d43d00c0f41224280c41c46905940e8000a2101c0040c003650030403a001d80e862400001c03103548107a00000b64150b2044182c6055051020302c02e50660240014400e07840c030086485a9401015100b404190340f60b0f6018000f0442182da4000096031601040003c10800d464440601d11078914942601d08070003000b01401819400c41d0390440e961780001707400303030707002a1600651408102128007035806004140c1c010142842c2c00e0034001d01003072450300c0e910b065400410003104400c0d80003003091030716045000e82c071807084a0600820180d8003800000b80a00c51000c03846540f03000c0e22000c0d8218000c100860001030307602d9104200c00e08040c0004c11504400c5020300300102c3c10b00b0809550707042805001d4401803007920000ca0f0000d0b00c0400101c000400004042d0f6036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 946491627 1250 946490377 946490383
    0x10509061f060203030411013501050a080a0f1e050a02090f0f011a04050d060b040f051315061e061103030f0a09050c06040f080c0405070e120712080c 66
    0x10990750103a001c01d5051a000c000b07516480007510141102c0390000d010307201c59000c5d5500503040c1408411000020103458807082e0185001e4251409190300c2c0070001880d4504a4910000d4441c0740002c0d100b08421039032510b5508002e881d08803402c1d80f20a0005401194100c070004602e8080c00103003009003004d03c100318803244014900264021260284010384640720700b503c5c1500c00202000d102400702d00b043c83e1540c01140d20455100319050301c11070401c0300300d8101d0003c801d030640d8203000e850104082d5100750742c0b00300c481c20401c0c1944240c41d0b01041203c4c00c1011846c2031710100091007515100002c02a4540c0380680e00c004e00c82500412611303500516813803040c0039003000b541c00d40c00c1420148840c0c000250045030281c0d02c50001d42c0c1401000e1003007812810006121940c0c89680d441000000c41c15446400114080c0b4180b5585504081c01110320814503a61000c01e401e51500400441506400e0100168402d964011848044183c0e074400d8107400343c40d4068030b0b1900b00060600d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 946492877 1250 946491627 946491661
    0x114100e0603011b110a051b091003020f150405041103061005070b060609120105250c0804051908100b040e0d0206061e030a1401111c0504021201050906 67
    0xb00a07031600000748001d600080c8940c1c02505146000f204003040c210105143c078401400c0a4210300406500070000c50300003200040c007410580d5010101d9642415160b000580c0e4130000e9001601140802c001c0c6c94182c02c440c03840c40402a4007410725071210003040c200d441c0f0b1036005481500000900c440c0c0d00c2c286121003d10440c510303140c0d282c05955650385081d003201030301250007003202007a560050780d60381d0320840141051400802107031614511603210035020103000d0080d1210035410070f50481c824040c06581c10340150101d80341070b20344002d0141401c01611140318401e207045021a00000c00d002050382c80ca800500810010340c840c08020446c1c1518030002c02175400140c0000c1e94507000300c0c2c1507900040c11200303600d42002e0b601010704400000480c0d03030b615019036905030003008282044009065a10f100030800540550021650381c819103c2c280c12010013072408ca08207038426004a0340c09032001e4900070848451408071829144103031840c4115030440c2081101005212440741 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 946494127 1250 946492877 946492879
    0xb040306060b03012102011101150303270b070203010207051b0103050f061f020304050307082401120602160b0a2009010f110c090c04030b01080d051b0114100e06 71
    0x43d01d554034026035980c00d164030607040c840b014500035210007568054046290702101800003444018140040034010064a0004078042000c5195024411903d20400c200d101401030b81c0480c082d0406400e43ea240d0086d41040b60b2540d001c11030f50000030b40c14043e0702820072580301e50380c1c01032403d08005019140001d000c828921100003c0100c00d1f40d402207050b0b8815020030380424210035240c1c04034203521468011507014410705a000590850010300781415180302103041d204580b5a801e45e0070075990030312840c1d0f0503200c211a08400b043c400c3d40181079100c200d43d4807007180005d81d0342c2e9030301e07034003044034030000040c1c0d074200c94010300e045e83d100e0740e03819582c407441540350400c2480043c020fa1148518001088061180491100000c011311220b080c0014076102c4076203010204002c441d44140421129500041c0000580e640b002807440c105003443e031580c50a10040c0308071a200e03103021034011801ca41d2181c01c0021310103050060240545a641849014141002e032080c2042d0310140c40c2e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 946495377 1250 946494127 946494149
    0x2b0302071a0a0806060a090b0f0a031b080c0a0302130b03010801150602060703110408030313120315090c02100e01020408071413020705120a080615070b0c0306060c03040b04030606 79
    0xe00c220f5001c200607a00103000c4a8a98407400518800c035085842900504100c50740042c0300801000110003808180320166410702034000000e540e8001086400000c0020a1507180414801644003000d8103c0d041940781c01810094401085c01810328581d01c0f203952a8400001400244402e018001e1300c035006c6400c40c0000b42ca426002503407124000c0466080580d115200d40c5201d00300d0084500030030407842100d44071b04181680740595042404201c501c1c0601c1000c0d54484d81c001d0088007000c040d10014040007920b007801c0100a8400d5401c0c07202180030b241241079418a5a2098040c900c1d502400140c89905265410740782c844070341c01c000100d4192820103840340e5120400f5001108080300d001d600c80300d0910b426885c00c14031600b244402100412103801e41a880050148100e60840b800700440b8541d10411f680303841406000350040c03040c0d1000030108401c800086400100c054551031a140300d026506085820541049801c0a00014200180090f81c010240540044954 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 946496627 1250 946495377 946495387
    0x6030c080a0e0c01030203060d060e06060a0509040503090d08251b050609060d060f031401110708090108150d060e061506040e07030209040603081c0c020c2b0302071a 73
    0x10b00c55071444075018190400d0f4002000400684a41b90440380b01d6038004800e014030280b03603034110307216501200e030300c0d004a0500714000740301c1c54050522402682c019024510301004401801020884504183c40c884020403404240b20841002900400b050b01401300803100c00740740c00503140e045204c030742c81178281c6000705028a0303903260201c50b01d440d011681940d6441680903001c0146c24154010310b41c9c004501c1000040c03004012500e4100b40901d4000c02024004000c441000e006841028200041c03c2c0480300c200d50007140f0042d00441d00c10000030404500000081c049881c8000448a0684917855403861590420569030130442a0003030880d000007d5000c1081e501682c4200c08000c2400404035444500030b904440d1000c2001e0420301020b600c03400e046041e54850946c0c40511001600340c01d40d0b40009224045003c5442d5024020311801d00301084040c0c0c08241464000c00365a103a40c0071441c1d40c107420041142d1094016200803445c0003020022103107006010003082c102081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 946497877 1250 946496627 946496651
    0x1020313140a030506180705040216080912030a050a080114030a02221104032105030a0c0203091c1a160305151905130b10050c1606030c080a 62
    0x6851400c0d074019015144548a210780020800401588040e00600031902401501003100061211742c10b100c02c04c07500c01990300c0040c04100d04c9041b4418050311a2402e0810000d51200000c0c03e600800030310340b03038075412143c042504640c00760320028046600099074010031a040868103004081c191071040e01550400c0201e0346526030b03241c00a03c100740e20308820554802d2005107205a0b403000d00104450341305082c549000e03910a020989030720b4820000c201402d240b84004a000c0703d1269100f50864440a200380060b00b111151282980018440034010707484444401c440c0c004840118040c60125042450406140051080c01220380b0000c00c00200301003410003840031014500015565189000004155002c0c1d200c00e900054014080400d001c1150040c4161801252a4130b810482d0140070307001c40b2540c40303130150001205001125007a0141010b401411107803005d8582c04482000ba0001f43d9000340c1010001c03d54a00c00304c544103a11007121984040343d14410003104030a04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 946499127 1250 946497877 946497907
    0x906080106180c180602070f0b0306030c040b03031608120f041205131806030309120f0f0c05090f160309080d0b190306020c0d0f1d010c1505060906010203 68
    0x4a0a8801192102080345842d8810306050700369403501e42d13080c218992200c00094403050248101061001c0395100800e0718040e41c400c40303014140c0200107044614400c0300b2302003d44401e40c2c0f807652600090141c0080144280840b1105901c102401070b40c074411008000c0d04120085c00c0001607104410800000600c0003090070080e03074407420b0858840a4030308544608448036040b02c2280f80f91a100340c4030f24071054000c10241c1e840b03901c451842c0381c2c84404490b0f0482da6000c02600300c0180055080101b143e0550401340e0324054940004080c3d10761010454443c0155500c040300a022810400d1003240c00c10080704000d81498240507010701c6440300c89040c0115040c0c500450fa4238151200d066031010030902c0700101a000c0c41c40701a90303c2c20200000d410441c003071415800f840c440312070468460a0303d00550011900c07016034814001c0000441d25803d0802ca6060103802c94000000c03600b4141c5c40300ca1007404000214075854100140a07001101034002815580113201d003d000e0031140e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 946500377 1250 946499127 946499159
    0x16051324052706190c02030705040c020c0402030a06080327041e0b0a0510022802100f11010603150f0510060f0311030a05100e15040c030e0114010906080106 69
    0x80e000e0303080c03425100000601d1600c0794040d400780b44c84412150f5007580d9041542c0b215100d0088080c0c411013580c1d40c0c148420b480e1080c080c2c40041c5c20078000880103180641c00345800030089100002c00030b449483d40c0c0e285601558030014280e110b0f60104001d800041302c0d610103541d0560b01840145422000544078452501d0082070303058a0b070100c940079440c1c111400c5c1c010321001301809028070184402075280c401b4a0303583d5100f46030703c0600800c1001c0c0c079180d0109030fa501030085251400305c01d000311002120a0705640401070840b01400b2456824010302d00a54000c40d10290304613107910f103640c129880280c170990040c1c14442040103090b80070781810300310303045803c01c4019115070040c02c4004125111001240c1c1c1d4010050046400a903445644a801d034103c00000b1681c4542d412581604103c80c40c10b002c0d41d118100c8142c03410190803620b8040658200411212837021919007034403100380d81c90300b8070282d09004102c6c500c031034003407000101095002045440c0c00d15008481c4050a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 946501627 1250 946500377 946500427
    0x10060605040614270307060201051b03100b030c04170604030e040e1011030109141009200a030b030c221d030d02040620061605132405 59
    0x81901059a650a20121034102c40055451103142d180b02800d0b1031001d03840e944e514003901c180032001c510300d4014420781c1e004d8900d00102d800c0183e494092012641c0c0300800c00b411701105440c0008002c0080b0001d075000d0710748115500e48490070001c42a12010b24071a031034419034009018000481d812080b0303025501c0741550045214501c04581a1038041e450300c84c181c02519206c0b0100c0c0003c400c1c8043c5d41a07a07022602030000e02002c61121442c04800d4941d40d12101184c101002524034076440446000684030018449c0a42c070040001103411003100301c4003103501d4104007421440c060100b81d0030310000f1200d090780b1150000c103404282c4401c0044001c610b80e80c04405c01c890307401500d601d151041781011a130380d5003008a8005c1c044c0d08580714440116285282000e28150709203111120081a080145016030390341803030340c2c0c5281c02c21450700244038040042c010840c00304030404c0054040241400785a10035001c6203007081046501c071a04009080c081c200d5003140524a121401c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 946502877 1250 946501627 946501637
    0x2030f0c0f040605130f060b07060f061401050d0944031920041203080109020304020906060d0f06064d03040806040c03201c030302070b0c070203100606050406 70
    0x250906400000305844d400c2040e8400300414000704000503508a070240406090bc02e03c039240d0340342d00c6070820200441d14980414814020312404518641c450114a4001c11100d039018844000a0322a148410044d0701003003e004601e01c0b8200310102c04003102c05850811514601e00f14489800103464220b840c4229a02c1d403007600b06c140030011254050b250103180c459038481c3c3d00e64441c0401f01503100100d000c50082400000c0008540c402d0700e11590700a0001c400710740c1c40208012180d840104c8000089546940200ca440b08078403403600034011756144c030520a074420f9807041812038200300904500303c51042d00d244030724900c0c41c0354009040da503c0c0142e0b42011700318070900318000c0c0d81103a512440703040c00308401e2100d2a107600341160301880300302d4100e02c00c05824404242404107029080010060113080911640d001540b0690091800501300340304ca540d0700669400a072a0140e8032240480c00405602c3c0c1408811500c2d00c400c10304008103803814070054000c2c00b0342c0c40b425003449 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 946504127 1250 946502877 946502891
    0xb010801062a0b010f030308150d0303020c0a06060801022a0307020906130c0807110d0807050a21092901030201050f04090c090618050108040f0f02030f0c0f04060513 73
    0xd000c001c00c10540d00d0f40300020002a6849104a20004105100c29000200302c3c1003c100e00035400c098085000c41e002c0c2000c0c51041c0541c805034041c0d0b2110f8224102031041400400205075903101d81c0f005001c3c0d1000150395401d5180b2103162a20003080c49240d00d490400403020301002c000200c0340b00b075074140d480c0f11451742d1300ba001944943c5a0100c81d20254100384a207604a98030100760392148109454040b148030a054040d6134401c2c2c10407207400410f24100c08500218025009000c10b25454039003266060803008443c0107e8150103010041c150304c0d11944010010701d8007000c0d0501e18080aa03103603101c103240e008440d01da010711010341803103c00500000034208850460300a002d41100a000e8406002c0008000c113465102da10002802403240055071a244c440900132136605958001007600c0356101e00c11440181c4408841c0b01c1203940f03000c0c005031030600029200b080341174041c0c2a12001542444105000d86000601c0f951421805000598400740c88505620b0740f03100c00104a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 946505377 1250 946504127 946504187
    0x120f0a0603050a031e09080303150301110a1d0108040507060804060b0a0608041109010f140a080712030927050a240f08060c03011206020405040f020405040b01080106 73
    0x5181641018000f809402000018180c001e4030a5905150384074101e00e40340d01c00b03441190700d00100d0050001035041080410007030301c0003950b07501041c8030040002940c4261500340d0315555200b8410744c2c0200c2c0500300700c000c201c1800d00540458030030070308062905150030303500e00351074113400e0080705e042c060b2a00100741880f04507402131801c5003028002600442c3c40b00c00c06042d00100b03e4040f245284000f807500c1c9113040001180c2d04842200880311003441c00c00421060190b056880241c0001483c0000641d44204200d04c0006211591600100030103d0a0081c01c1101a0704030030504c0003068800404100143e013a11000300a005000078980c4402c1181006042000c2c0c42c011000b25071551440e503407541c0b0314100e0031a25038903c81641903a41d500d950b03450b41c5040719a90b640350350030b000403c202d400e4007540840841c4507540044c686030700c400c00a070480340a109220f56040e40442c040c0312074105885203c40c074440c00d0a02c0c2d5407030340c07500300c0c0188250600c90004500d21164206980d41e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 946506627 1250 946505377 946505381
    0x60f050c07050a0308070605060f0a231e1c0510050a02130b0301090c020a020913080c03030c030403140c070b0c0c033f120403090909060e070b120f0a 66
    0x30b010020b0030603008075560b0420200313503080300d10160740092606c804580e283c607102c0c9030026424000740c28407801e80c0c0b8000b10b0040d0042601141c503020021502c2c064929030300c00a241940721407002d01c0d030f40d00420600034002c0d01b0f25949804071000c07182c400c92301c0c0441c0c00014056000c0650b9031021506541d0011014042e02845104034802551501c0110301503407800c010314180d4055103410049152000b200300d0f0b48841e001d50180d0821880400f00e542c803100c000342a8a031034002c06c0b00e245440396551005203598411600c81f25454000320500080541c420001d45000003120316003410038803440b860a0f101c0c0c5c0148607c501802001500480009083c0118610100010182c43d80440b421908a28504a210400311410070100c110003240c07151055032540403120140c0320341000100e1024201c0d0b00d501800a400380046410000b41e106024003071002804e1041c00c1c0070818040d104d002d07901c0e040d00c80d000b569500c4014403a0004c6107112560080c0e100012810005150319148031102c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 946507877 1250 946506627 946506629
    0xd0816050714060708060d0f020d02061605010516030e0c240d15050d3306030302030a090608060625021008010e060f0f06070218100618060f050c07 65
    0x1c03401e45120b0640690b410007044107882400c941c0c59051aa513100010080803a54604004000100540c040c0e0702505041c4803042c64588007812091030400350b90440940705040c80360890395607440e07908120440a10120a04041203642410b128040c14040d003161510039103001103026810644d164541e0404a00210880c5000c0c1743c0d00316039440d9590105c0c0042e0080c1e0040c560b0710010040c0015050820890046005030051345501c0b0030200f10108510f0082054028036002c009803500f04018159031040c9001144281c00866403040f550401900c40300580e8058018441c9013003c00040fa1110f00071150390540719180d240c1105420342c4103031544407036031001035003054030703d0000c5085640081015040c0d800a0442c400c0642d10081044919218070390083d41003110800c128059003000000703400c205200800e06154a51005c81d40e12642604480440505e40c00080c100043c035000840c2485011070040e48030b08060414401620310301c00044050100031000a90104510302404028 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 946509127 1250 946507877 946507883
    0x201090e061807020c121204030305030c0f04060509100e0a141f08060a08060c070f05031216030c02120406050307090b070602091c0c1a070618060e0d08160507 70
    0x226a0401030030017541c9803e02000f250107004010401902c0e5040080d600003c410281c000501e0701e42540d03000c03160f580026120310b64003a024403e407000d12b841d040280001c2c081955415031500451000c101c651122201d00740b00b0b0046040c7c2124058507042d000b0310940d002c6980003030b003480c240004100000104400d8480707511040c000c102603940d01600086c054801100d075080705a854041c02d45d11740c0d0040c0d0706409901d90405c00000050500c0d441c042a050140c07003680e080c045100280d24240c83c0482300070010000001016034072a8141c81014400c844510040c0a1440004c1401c01c00e80700b10702684040c44004400155168403d11071203020702416800c0f9a103400c400d161003000780d0020040140b01c2c2000840f1103c0058007a100c86641580000b001a101868420242501400c0d6031a10030360060400180300070591900900d6540d50022640c00c0c001d250606080c402c07143c5520b488115a0071040300181043e910504058210100c40740c4c840c05420076504c180d6491144800003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 946510377 1250 946509127 946509169
    0x90506061e0d0b01051008070f12110c2a01020c041503020307030b1b0a12091104110304020307090506010c111c05031b0c060d0e01090b1303030e0a0201090e06 70
    0x140302088500c3c2c56080c101c0700d054503100d00d80314030242d003075903400800c54100b40000e40000c07030252210b00c07400310080014101400060f084c1070440300c542d17640d4881d00c440206603011152001642c020309560002a441c40d100850303000d0706860000b501d80315960b43c44c0c0e1080f0340350701d549200c42c000803010038000c590060403500f81e2917480c50038a100c4602155020040461045c43c2c0749441c202c5000c8074041116550340c50600d22103c007003c80101030040040c0ca0802074202c01042c1e035129889106280001c45040b90344030f2801e0f10405207407681036000031010340e0400050003da641c100000018a40c0d11408205518840c00c0214600c42c540c0c03403001038140344140b080fa003440008002032007603c10060381c41500300c08110280e641c4080d45c022142d00101c040141411190f0540e00240c4054a40c0c0d001040f100840c0c0c90300054020107681184202001c0680c0b01e08040c7c040c4100000355a20714041c2010110355000030700b021381c2900c01c00868214032030025006d5620b5400141c02d0032541c002c0703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 946511627 1250 946510377 946510399
    0x80c0a030c0515070c0201200f0c0f1002060417120103030818150622020a051207020a03080c0d0e010f0b01020f0a1220010906140a090506061e 63
    0xc088805552041c0e60320300034500c0e007907007040090004a103d41881c1e1500703040e2405c42d0b4011102400005000c00540c0e43c07402e030244162905006000d40e6010b004000c24003c0d070340c08200809900c088042511a0080e45801c03c9012b80100d143e41c0e016400c1b4000c031a1a1900c0a440d40c29841034092403007402c2c500f240013000301600814402d0191840c040c01042626600c21129903403414501524810f00c2004002140c9207000c0e0307240210785401414000745c08a01880a40036038025450050110708081054222a401900000c0d8403107a03504c01410040707d5502d0140c411103004d85050340c50b680029140034030700c441d170700b10745010303085030008001c050150b4808800416014500300c0c018050032a1842800700001064900a500109500a0000800d600340c0c2c1d2000c401c2034209031071450211a055a401c05e20815100314098035000c2021a02455128040f180c01400454158500018100440d80001e0300e40e600180c00c2d50740c0302221303540c18041250f00341700c0071200ba40240301c03d071 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 946512877 1250 946511627 946511633
    0x20c160602010f0e06040f02040c0e12070905100e040201051809041a07090e220b090f0105060103022d040b1b0f0a030f0c020604090e06150109050a03060504080c0a 72
    0x2000300c44461401104003c44445804e000362989000d0304c018090300c080c109020007614050388030198000301414500c10510045c400b01f41000d0b12180d550905d074000480c1000b860f6041e0041c00c0d80503026015000d140e608007200c01040e442c024002a041100100d040103031041c10848034204a0401002544d0610349858400b00040c2502800c000501c1c0d0440070642c00c0e03016640310b0054074002a1300040301d070380700c3c00c0903003104d121000d099141e1980f90a04802050250b0000303800b500642014109030200c140d091429030702c01a02c49410103104201c10b401c4290701c00c2e500b108581203607621032050b03110040451503074041c0340c001c1000c03a100001c200120808403444005010100350603110030040103030881e5110003100c00c1c040c0204200c00c540c50401c41c803403070242c0400e87c0f00404045c1402d8031104c2e202c0c211241c1102003c60b079480881070045199082104141800092800d070302d000303081202040640c001880002c00b01d6843d50301040402c40380c4001e0303d0268030b600b4221400481141 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 946514127 1250 946512877 946512881
    0x1206090618050706050f0708030a090204060b03220305030610021612060f0614061308060705071a011a0c0a0807050706090f15140903100605100315050103020c16060201 74
    0x40c0c225043e108034440001d01a000303000742c2c0c000d241a040c00038100310f180e44544000c1d80c0000c01d60080346a5400b00c100050f580d900c5080041c1c03001000d095120301c0e1061200e24200c180101c000f5010780a940d059001950007030403640c3c41703481551003130b80a07005841d0076840c2c901c40c0c44031400751240306200440c00c0020783e5116111140115020b024101d03161180c0f4040340c0c0140100c141c3d03601000070f18482810003600800141911148610f00140e0702d104241c185001030301c8840000da0001194400e0108010703e05001200c1e0014511055147c500c50796091400030840c0385210340049a50401c000c01802451581030300081c440b5500c41983c544182c440381d0500880020405003100460700084100c03400c0306540303a080405004420010303080d1010b65005401780d800e500104078500032030b141440002c01c40181759101090160038032081280c103410100d880c0c800c0600e00140070140100e10805541112028200165200c1d0448032036070405c010a61840030325a50038200041e0b4607415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 946515377 1250 946514127 946514171
    0x40b1b06071112040503120a17040309030c050906090a0f060810020a020d0c03020d080408070f0b01091b0c2607030801050307050604060c0314040911040e0f040b0112060906 76
    0x81594407003100f9070300750351483c011809156055842402480e0412040360001e11001c1114244101d4001ca990003a68002404a03000c800203054010304100b000b820b51140780260204441c89002c0c0e2400b0404079005000c0148910b2545465110380340389512140c0c0b01a014100540a4a640c01d41c801105c0005c3e61180805030010322441414101240c1f080c80c007590400c0d89540a40400007181600701c1c4c16841c0074005440707194040142c01c0000c0c200c032780880b115030f128512410596140450800480300941c4002c402d940b40312f04526444c0d0360140c5030081032503010103100004032405501c05d0004207980d00300c1c849003000082110625802c1060281200c40840490741d119031110107100c0580500d220b41c8000c148420207075000640918401080320300d1850100e030130300759501910420b440824060031107440000409000128841003241e6002050504180b21410300e80d4601640b004144a406050100000140e080050542285072916041101440390412455410340301d5842 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 946516627 1250 946515377 946515407
    0x1181a130207020906040b10030903120c030c0e0907270905180f03091813080409091a0121060209211e031605010e0706050403170f040b1b0607 63
    0x400205e81349010301400301700c2c04004d48804c07604801c4840a501030a07004200703c092003803004031807981078214495940c040c1d00c1c550300802c1c15140002e001c0c089a0383c0c24146800740c6034601c00c000e840f50304600c00c006504021400d05182c2140d40c0011308114099801c207035081410001400302c2c80000782e038109210360010701600c40400c407591302c0c0c3d40e0740d101d40741ca1160080440940350022030201d94a46600450303100403840144955601d482907544503801c4a0000c696406d543c500707001e42d00c4103e031120700215101c2d04265060400c0d0301c40b00b08151140a05074004005058200841501507550a01001d8160759640b0740c0c808240c80d1012480c1d079070200b41d116404c0d844c4484201c0b00040b11041180b100a1483c0c415009510b84d0b40d1003c0e0b04003525999280c610b10028214200183c800902c41e558405455a00790b00d0b01803c4403840700c000440d80390041c081462070210307100842c1c0440e2842100541d6501c2590f0f100d441036902040c0c22000b90182d101000308958200c0003500c1403840d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 946517877 1250 946516627 946516639
    0x106031b060c0203060c03040f0203060a05100506070f110303120f070f050a0c0b15030609030903240604180614010302010f090303080c030c12010803040302150301181a13020702 78
    0x1881e054122100550050065499840070010400e50400c410080d9080360060054448800240d00030a280c6102a0380b04111644d4880c208402d0a02c444541e00141c48122185890300c00c0d951205800c01a02c020046c20014206000c04d18550b0100101e410720959909480b10b01c3c0382c51856200180f008403846000319003d546803408061040048801d1b1303100c0f5440340c001041c0c150b103420015040003442240d24100c1d003250340c02907075010492544114030f00700065556404400c145400c1c0000174140810103240d804050700c0540d18000c80e15449a02a500020030421400541c8006016014003400191511007480e0292114558240c1a00e0003031725030540051510310304403030081041c480500001c1c43d00340032510342d4040400441d0090782002c811030521030181c1854444041c02e1344050403030341c0001420030844c14040c7e001052141d02c0d4047c1810344d1705d486c11403803004410000e00201c0759540c0240b2410781004081c6440c1018018091122070030170018064000d5110800c20392140b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 946519127 1250 946517877 946517879
    0x92b1109060411160507082b1e03020c0c060406080a110f0403110d020a06020609070b04180b0a080d090612020f073c02100e010e10020a050106031b 65
    0x2c10580102c4003075000d480401450000800f042c07403010011814100e071203006401c000a4030740f80400c030400014001412040200da004a8480711860030214120144111900b042105002c1c4900ca23012402139401d0251341c5044106180b414031045c3e11500740c2c008004100801c8840d03004060520400450004204066500c05480d00c1130203800c02e1024030040411080c80014544101507036031b104090044010000c01c1c0d400280c0003c3e2582080340140d010f80200700c02540104801d1004003d9148a1071402c6d0902c003008a100203000c0c111001151030320340000603620340a2200c401482d002c400c2d6990110b10302c500034280c0d1071a224403000544405003822502d95140300311005885110b4510345000e980f0343d290780c2d00981400601041000c3c58880200380300004160403518541c8c0182c000c04001070b481003203420180c050708030041007805582c0303042c9a60016070304005007000711040d505108000804901c1e00240210042042d400d090380001003140701107a850b101420150034404c40b0b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 946520377 1250 946519127 946519129
    0x31101050a09051e010f1404020907050702010c171308010f0b0f0f0409080708070302101802151606110d0e030c03040e04060603050f0c010801090b06092b110906 71
    0x741e8040c2c5000b43c00354201c101d410b5503407003810003d40d04181103407001040e554480c080110841d501c44100081c1c50900300104411803401188040e44240f06090080c1070405d05c0d000288281e0070042c00910b6644500026009c403250441036550f00c4403680a017400d00c40d250705d0754034080c244000c00b4040050410035030f04000e2400c1d600922000c000034149021f084c11400400011741194502555a403008100f50001315103c40d00420816020b5001030260002c00444001180e0f041800000d00c046680712900c0181c2c1c41942030408490728400c102d0b1140031010001003004a030090061000d842c1c4000c0c1c0d00b00c1420400a042802041603042085030400104103849124500d11b95045030410032003806420100402c6540043c00745c4400190f140e12035275110310f4070844518585043c0d01c80306040e2890b40c0c2c0500c4080c0036001c007401c144190405200420b00e00d00540311484d110b01c1a400030b92900c41c000151480b043d510000700740104030f405090050264206080d182c0c09403d05500040342 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 946521627 1250 946520377 946520381
    0xf0c050303090d2a140108070e030c0d06020f04060c051509060f040303150b0306150406020721020d031808030f03010909170301231f0507030c0807031101050a 70
    0x7948010b0a0200c5409084e0f480150080000300c0070540c030428070300c844c0d11080e0399460000c0504600801d000d0228010380c00034158a00081120b010400a0700c0204207948000c07510300c1c0f00c40c105031507801c00c42080b440c080019016408440141e03d201090010f0f80c00c4e486a000d81100780241c0545041c007449480d03000c03941f80200d0310f0b0038103075106030081441248428005a80180030385000213403150074600d05502d08526a2004a604a010050081502c0c010071400c00c1c01940e40d40c120314107460b010f0003039103c0504d0311800c0813090004841001d4180507100707590075140d00900c401110009490701500e1500c8000c0403032040001028049820100041200c0043e0343d8010068110380c03924005102400a2703d90446e01c8212609644207102da00c0c01c040c501900c0c80d4a01c061040031040380400c0302c090003910141c13144550041a1000c0440e00300d0081d50107000d413400a42e591303964103055030703541c02c6848000c21501d400600041410343c46500005807440c076000038401c9444541c0c0c1081 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 946522877 1250 946521627 946521637
    0x80a03110d0f1b020c330316020a120302090109090c0305041a0106081305012c010b030c090423240f090607030203280b04050705071a04060906090f0c050303 69
    0xd45e2200b00402050315103035042c1500001400c0c00302002e008100134041d445544110180c4a40f140401440800e4920400fa456242003610060103402c5643c0c0710b80f446005055440c80038158002141c0140c1c2c1d11171107000020b840139a40a0040c1c02801900a0090038100c2f000e981121091011006425400780f1141c104c821030342e0340b480e03691945204190281b01944041303506644c0e035040410100031b94200200140001042482c4409080d406182512082c0c018180700360448201a00203950701100290041c1d0001c0d01088540026030984a02d1f07008003201203840c3c4035088103642511201c000d004001018044401901e0302e84840801c604030042d03c10381741c03030341040c0001034680b0300c42d50296501c915003500d1007910310340701d0400c0480cbd2000164000e901c15125a042146814075015550700301c081031816901d800700c03a80318202c41e41031b1000c41c540441c00b4980858140704107900001500c0703800c1030040203011940d207000e2001c00c1030404219010134220340001110328010090b1a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 946524127 1250 946522877 946522931
    0x1228110103050c1207020f061810050a02091302040f1a0306102a050106080c030307060e01110f09240904050604060b04081608030a0903080a03110d0f 66
    0x52412000054020700402803072000600800e1001c1900c59a4100c6a207020304850307000b8003040c2c01c801003018140900200100c4060505462414066400041d800895070380001d00240a8480d20391060181c4036032a1025442010720701c880c3c5c0e1060495000b0411142550810200c0c0c0d5903074610b8186c40036902d00858032405050001481790309044ca420402240c161901d0b0175040d04c00303c03503116041d072050ba0041c11b8141282c0c004c410400244506070241500000508960000b02c0000c0d03074905c1568802042e0545418041d141c1041c00d4004a41100c1951000c0707844140350700d440350142c2c1040f000e0030321501920501d0304000e411a041e5200f811403001c00300c0e00d04100f05080c04058807010700207030b4006035510000100b22000401502c0984610800303400c2916110b050000c1307400081d0029002500108280c0c0100743d0081c0100007100d0380700218584030080040700390018208101d441400345000241c030000c181455108054150a11008218044c095100044402e42c013450348 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 946525377 1250 946524127 946524143
    0x1060608060103051003080309010b030c060403050717010e150403120b03060c0708120705031e0f010303031e1a1c0803060d29060108010608040b010b181228 69
    0x20400da94400e0300400d0348282c40f56017002030b0f140c2c1d0f943d07050441d92080300c0d049a0360750343d2110200d1600c0c0a001316002140304941f82c81c10a07003140c54a039200d440a10070002140c00745040003216200a401c01e0f007004030741c507040d48c54041c0c004803458100c16044404400058401804000d200203d03c15180c000740042c0041c0485d94802c1000500b82d400040103541000c02404150303004014480c80340d03c520000c0e40c8898480c02d05204640c4158528a80d00854884110400c49418401c403022030440c1d40610700443d10710304206015141c4007060700d00b100740c1401d000c03008480003248404008501016101003070629810030079141c0c4516604401010440200301141c16450452100701b021405085018401f46540381d9240a44000c8601c04050351808000c010a03581c101c0403550041c5154200074910303203441c0e0b81c1c4104000c0d050103250760451010410000e03090443c1104489044d000e0b0504500c50b00d50540181c0d1000030010145e4003154004a5441c11072422460500380c03603010000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 946526627 1250 946525377 946525381
    0x41a061e07230102120c09010504180605210c04020d0b0409030e03100b01140a09210516030213050405190b010806010f050a06050304050a0218070e031207020411040e01150e0301060608 81
    0x6c06000e95114528090400c0720600011500c1402880070056201c00c02c14009001842d107400e2100032141841a0015013940c5c00075100c40d00d0022480400d0b19008a40043e951480b00420303c00400c0055126500b0604c0c0c243d440d0200360b008000b02075180c400301c04851800c14800d18100595000803415400114000e002d184002094406800d00401500301030b81030075298062031840c020b10342141000c443c80071448205000c014003c0200c01c0d00901240c00341c050454001c00c141c5044045a105400e541c1e8001030207011045c08500c401c600c1e0000c074882c0003682c038204026116403e0140e0b654900603040005a403506070032084080f190058605955249012001d4030582c00081055500d401840c010340010703950400c10903c40380c20140941661b081c1040c0060111034078001c0c00703020b07600003407014035900a1207041d030381c0c1d0360b0b41100c022032207100008003089540100e9020f2b40a400707482002261703901030030180380b1440701580d0b10300148046060416007a074110344030710f4002c203003d100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 946527877 1250 946526627 946526641
    0x30c0a1106070506131b060503061306090c0513050307050d02011809150608060a06050d09030909020c06011e03230a02120105010501030605041a061e0723010212 71
    0x6408900c40401010340d8200305058072200d05080b0111003404040160f24182420071042421883d658400104102e0420b400c02101400d14800903114611800c1d644414002902607904200f0103014503101c00d0010303200da034a001d807564001c443c040d8000b2491032030208080c01c000500380304552004055038a00c0b8141d40054514255020390a145c801e900640410b50003100d0041d0f12149000303490480d03500d07183c0700c0010850f84014002c14030070118480c080001550010960700780c500c508100082c0c04010f464280c03071941040e1f100891150001c21507000ca5607000c0b840904841c070300c072826404c00e00306c40c07100220484032b400010310480e1034010040341c1c0c541c0410f404081d011440221540505641c00007000050300d01840c00d04c0b030b03444000500903540c1c035018410060100741c0e0103001001e0300342c0b0052804850040410300420000c01c40c02902c80d50701d161311114402e94160703d541c400e00b0341400c0ba0940b9100440341480c251b070107205401c5c290305100300c918275040035018030400c3e10703142 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 946529127 1250 946527877 946527893
    0x31501120311010603080d0f02030f06130b150711010504120303050a060b16031b030c0f0f08070c0305010606050712110f01020d1416090315060b0313020f03030c0a 72
    0x400d041c1d04104086141501004007446600e01541c0a03c5039140c13901d030051803c90589401c0c5444400560040c01400a5409414422500701000320f03000035004181c0c00030305004000d90112254081d50030011001d044160100034220b003405500420910f6004d0f10043d03a00d07201d1880340b0800302c01d50b4104040420f109522564200e02d110201060f210380e41c005414550704400964140d002c2800f80380c0e0105070308048041002d5440340d6a441003005103071409005010407050180000003400038400030003503d001d5080380346502004043d121030315801e05002608181c0800c485541c44c00d603012030b01c82e002c1c00541e41c1d03c43d0322694040400c14001c9044807804035412402030584108620305c40441400c0c0040d0410740f4100200140b044281030400100390b030042d008070004800f0b42e411716403040e4401802000c2c1ca070021044010200c02140c2034004059070340c4048144900402800080001e811003160b0303150085484011070848101016102c2c864454500159030001c031107540014020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 946530377 1250 946529127 946529159
    0x30d030906021b010b040b03061003030c1a010f080118020d0f020301061a0a2d0f0e030109030e09060f13090206090406120b0a1a12030702042405031501 67
    0x10780400350402078611444140800e5800070946565102d40d09110242021301c00c0c64125a0100c0c0100054200083c900740d44040500001e400c000603042100184a5120040c0c11103010402d0403034003d40e500e030b80e070121001550181014550030002001d02041c4441200210560002c0040d05a050036075507880c075807030b0540c801300c1c2c05540f00c0b000001d89010100c45040c88002406641d030707551a1000c4000d0950030800d400040318070031701c0c40d2982d100c1c0001441c0c404d0414582003540c500e58400100b6550060f00c4919944d041d07081000c0c4004240d40407607042c40b1a0000d81c1c4103c4151500c5d01000f405203030003140c0c550414a65040c0407a403800c690400c01445002501c400e00d0080e101b40031605881190f081041c0c81c1401c250154100841c10109560203040d0010410101e02c900f04511504030300810800c4c855054141c444641000900899808541c000c104120b18100e00c03981c451244e016070444864440d038420009818100810185080199015403c01a80c00c0c612015910405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 946531627 1250 946530377 946530383
    0x16050f09180c09040c171f08030c07181a010f120504140c180a050c0412060f05010605160206070804030b1306184d030f010209030d0309 60
    0x251401c6000c007054078916540519070804806aa8807698024082a01d50000c161710030005800c0071118529a10062590040c1210306007001200c5a52a6401e080300f05402044c19400001385c096003402c0001003240446004910300c541203180c11424108603882a5a84444a9100c001c20841b5601c00c02c0c4030190302003903003000389070705048941c8042103030380803101154488001007019107001e60070440500f0070303003040310000220424003c4608210703e01402000382180c4800200f40d08090f21000d82c2e000e05149101c0880c2da2006051a04c0036028600019540601d480004226184600c0488584007481403014800040fa0750a1043e1036010510039988450107200110016030f006102500400b60614070200d81c0215090250484004a4000940f031720000c1420000800c03444a2060f0001c1c2d10100e240a104110607951403240401c901056070012104d10000602c040036421391502000e13812503080c4601e04481034201c1c825900c0c001d40c1540101840003600340310740c00072403010b44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 946532877 1250 946531627 946531639
    0x6060816021923071d0606091201020a1106010510120216080406090603090c0510020a0501020c2817030703020f03150f0d02010e010309050304081c020616050f09 71
    0x450b2290b5001544034165003290100b20850008041d04007005201826040c1c41015080c6103241c070400c031010b00344101880c410301101d000065450743d00c2400f03030790701400080c1c9030f00d50000d00c84034814000d61281d082c580106140c0c0111945503800000d00506070340001e024107000890090040ea00043c0c20f42001401076005c0160b0720108100b14500f10700700d07100340000b81c3c5560401c90050515549500002c00f00b41c0790100880224030802181c4c0c044501c291103054580411071802c03800c000000c0d10260081d8000590b0580c264800940c441d10031811020314800342c5010030344070183d4500b00402a1982035200d508507071200b0200019a0071401c1c9040c01440e141c0c0d294612031440d04204c0302d9500c90f0003450103030000350506050501c0441000c0314501503040c0c1e268000780044c9408500b00741010b6885910004025080003290040c082010844048410f070103e034030540403081c06440c006010310000f18801720700001c211250002c0503154a4106031541504003950f07002a640154810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 946534127 1250 946532877 946532893
    0xf07030906110c0717030717030a0b0405090708010f0212180f062502160b09040b04020706050912040f0605091809011d0a030c02040905011e0b130606081602 69
    0x12000b03400809600c000003010305481e03460110700181c0341d140466004d8290300104011070020300003038002515044200328003030b200e4442500c80c1004001101000c0d4005c0e28080070300107a0040050906d0490b000b05000b03000c1454900070440c10390085d40480c403000c152030000b0a0b990000f00e50050320010101c03046400825500c203c203441e1a2094131039403142e0100900b132146c400813000740000181c0481c0010004501040402100601d01e8424403071a1800898803e50701d59032034021141d1888024415500e4006034141980100800d446d252030b00d2103540b1a882c808034000040d901142c41d140304000000e031910100f69025404000f032154441d2516404584045420006174081c01030f0000004596040500c2c20744040603810054080c0d0780840b8603000000e601032010050300c0c0d4103590100346210301e81340c0103000d4100c1400140c50209064401e00c2140b8403907000040c0310900301d07010482d041d01c82e1402e808480d0b40d401040d00051031030300001d41100f0048182c480e106181c2c41100c2c803203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 946535377 1250 946534127 946534151
    0x4060b0d09051507030c02060c0307050316110307110310060e04080d0f02191701080c120a020301140703060f0b0a050a0e0301182319080d0f0207050d02060f07030906 73
    0x42a800c444d0100070950341c0100c107102c60b6041120551040144511502d5424041409080381c00000e10b0700021030810003403004194420080911140180340880b0f0b10384090340303022030309000001000350007403007004100e44103040170340103c0b0201c41c2001060a203540312074851061681c000b0720300c0b00c900760726a00a20a02d000310700c0101084a1a4405c203105070f110f14100600250360220b80103549091a03006219401000c44c94000ca174100301e642052014220411074100f01031004065899440c0c000094008a103490001c0e120b080507680400c80d440d241c40500381000420b0040d000c503400c050003541c05560140c00201210081d40c02e206210807000d000080c01c0d50401000c4440000294074003074100141c10210f807428810640703801c0c050b03010084100b0341d20384a981c50114900e0b12241c5842c01c2c07080e608200c9068498a03030303003801000b0200015801030742c851201100d40f48210f22115000c00d00c08030b02c040c02502d20b01001c7c01a81ca400504134054180400c0588a007592580f0481030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 946536627 1250 946535377 946535413
    0x100f0b031323010b09040206090103180c030b010f080f0c06090f030d02100f0501080c010e0d060204060201051902090d1401021201030f0c080a03080601080403090e2404060b0d0905 79
    0x1a42e650042040c0070401056425080d5010110311501401900c003d110040e56000300741c6048030004e10340040c450310728181100010015500140030100da000020052100d442c02c1e0314181e95a0078640c44085030b0320b401881d40c03041d00740d41c00c4c207a940140700c140fa854070b446001030144100080138007041c1103175040001d042c0f05508070f042c030244e8041441c2d079a08141030301411a204074041c4040100b5807610581a44401c03401841d00e04020006042d4601582e40c0e0303011b5172199030000f50440d192506c91001900038030041d01c070000d031140f005803140c24122a90007140c004480290004000c210540d64641c0d88006080200030b286d5000d000c2c401030b0342d2000c0c0e1498002c60141482022903045401c09844102040e0480d11f541e420810480010030f4020394204c1e04110f0a1a28030102c0c1d42c0d50400700c0d4020043c5d00b10041d01d00c0960144003001c82c9081800c94404021681035411000c203c04100440c0c8240c440e40b4103e40c3e080c80540b50791440d560061715410700907002e8550420124000040e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 946537877 1250 946536627 946536653
    0x12020f031912180b010519120819031401351011070b150d03050c0a0f150507080603100f11040e01030605010b042105010e03130905100f0b0313 63
    0x83c1d120020602020301c40070303d9020f801098103840951030700b1512004a054101c2e2402250024070441d10304104001c1c114007260900c803c41c14055020390003100004000d815400d61040c0b44526402c00030448440c504410403000640c01201c1c880c10800d080e04401e0300070381c41c0f600310840c00b821940b002c0105490007136400c21885210002d40c0c4180e9803610443c800d502400c011181c4801040080d03054995102508885d034050508544540c0c914200b94a48078402200401208030710450b6402c100c1030090560800b49807000900c00c81c1c0d246c11040360000b40486074036078981e00080018110200b10340c85206040000140403a02140400c0304640e540e0203030380820b00100f151401001030148521866000d00b2690010615241c44c01c035503962a40030000004000054808640c401c00c002540581c100c4029202a01d4440000c4107080881c00d441d1300c5008441410040016002d084200045098070407096060440904105004500781c1001342110140102e45110344046110a01094 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 946539127 1250 946537877 946537901
    0x1404110a0305390a0b070624080d0f0e190e01120213090506010e15091503071d07050705101109100c0209150105041206050412020f031912 61
    0x51803281400341e03400303034078106a000c64850b243c4000111520b9512400441c080f200b08016003519040c05003400402440d44c0d00102e1246900b200c1c0f0403003d084403501100c02c031200c0780305032960143c005030242c4071000e2443c04003001032450b00b1440d65520f0040d401070000d025001100951f503490f0301622a2400c805c0c1c00005048818002140843c82d103002d2251084003422024071218480356205a03075100107014040d0346100070030000321940c000c07003040e0780c1ca900d00500990746410302d0b00c0a9a0780c81c4603002098000d001d003c90200f820310605040202d4103591002103050780c1c0d26410101c0d850740100408591900030b0f405250f6148a2a00416101090f421210f80c6d031404200d082005045001001a0a20a1a0481d0300140c0c2d02e1401a592000c1405024003000e5420001281e25200b5a000500100300070500d0b41309125159101f2841030380310701081c4001c1d40034902c040e80c0c0c5201540e10a0000e40c0100425649400c02d00d240c50408802402c00921504080340d00030300340c800410b00c0c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946540377 1250 946539127 946539163
    0x180c010f050d02070f0c0501021b010e04020c01020d0906061a0711032a0301140c0d0b120d050408010e0303330d031d06041203030e100504050601060f031404110a0305 73
    0x1003400485008800181f009000400403000404544401404070030103c0c2c0c140094154a0402070b202c0e50112014408c4001c0210b5580c4c252141080c001c0120010650f0458604040419481044006182030b2003c10303000c1410002d081e514055014003200309107402d80114100f5840d0000b01e2000c0700703070074000030041c6800c0d80040307070034142154104c8140e026480101000e10a5501c00300c021103030505882c0c0c40204584c9500c00c04a0b60182c01750800250510942104541185d40071002c5d005841e8050002e108015001000799520700094aa1541820700602a425420030808000c0a240001508803860044540015400410410040d008600008100e8904440710801b426581c0e004a41c0d5905207801e004200c0c00c9040600002801c1c0740e52204074941201c030400040c00c0000000720180018502031034402e40361714080c410000030a100f80c1040c420789009002d400d00964003071108003040c0c0ea550304d401c0600f071007445c0220f0300614040408000b20f64180858100840c180c400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946541627 1250 946540377 946540403
    0x2030c04050a0312500301091a0906090112060f09060c200c041d0105010902040f09020f120a1d0705010e01020307020a14150d05040605180c010f050d0207 68
    0x4051300800251000100307400c20b4807298480343d600c003120104d5a2091005081e1400e01d4485e0082d20500c64010310900010003200005200940341c011030010040d0302c0c16240c02c08603d00900440400130348810fa0b000c0d0101d80103010740c41241c403044068074001c81c4003090100b00340c112002103500c0c04609035070050301c03200c04c581001e80000c00c034140b0b6488451f0702034100d01d0030001103450b20648110644200c1e02d4200b400d00c00c03d00001314150000c0b01030b00811003945e40b0740a4400a5000788900c12440c4c01208001814810910079100303400ca0300e25440740f510b002e07041c0b01c03401c20200902c41002503030f85134615002e040707507000001c501010369070080106909040015009a00680d480c1d811075004000d50401600c800300040b00325203c9110b540441903080002035100d1040380302620140f2000314442400d1003041e00017901803809401c081206071120f0b4400c0c003d030000a0180c60b6613034000c0b580420154412100d2550b00d00342858024204140c40000310241c0e0312400b801d076021b03010064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946542877 1250 946541627 946541663
    0xd090809010e0d022202070b1009110c030d0b0d12030f050a0e0a0206090301140906040c060f0e0d0303060b0723030c06070f021e06070305090d1202030c04050a03 71
    0x10301c0000110040b1404420115598009481c184172242050301e120580c2d40b481460040319016102d00540c003032103890b40b6160110010180d44481d100d0140d506041c0031000320601440d01c00c50b4038900f81e00b000781d0318190040700f0050182c0001c02010703410540900d502c8001c03400d4050701e40b010104941d008125800c81020701c8080c5d0b41c0c05010316610314034208904001c3d2000143d030554903981658015152240000024018441d8a072000d2641d0054810001400404105c0c03038491885220301c6540141c861500322513141900a06a002c51038400140900f850940900c4141c4ca2081c540862415101d14504600360060001110211a920702d019412105421404004c1e04140011400c14425a00e1680e48600140c4440b003030022a50680c411248240440b400c001802819441c8440c1640b29960740d81004840030f000103031030140850601400465004003a6080703030389076402e501e42150840002d40c0040c0610340380034000c110004054803502c0003540214003402070b9131000130140f8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946544127 1250 946542877 946542887
    0x120c07060c020c0d031404241b03080606340311190b07030f18061b02100b0307240216031a04022d1003090c0b0903030d09080901 57
    0xc0190082d50000c0d4000b03140340d103640708211210354051a1481110807150f41080304c2e4031458000131414154403242e0b5100e4403182d00d85a2a40745140da411880d0452038203940c60009401c0d030010f0000e141600402c0061134018081c1c024200c40044400722050b00c48018100401d00501e8520102d0014040d60185600902c0c0300721500003020140500f081a050782c694201c000e110000c000000c09000b1426683c07080d800240343d801c1c4080c0400203c03e035041e000c1c40b001440c400454a0350300703200b0520750308291001c40d000b80c081203070000e103070070781a1400800242018810864041c410000300280c0307408440f804000300504104110400480480000d0414003c101c0511600292010800000740c00c0d803080007100c01c44608400d42500c80c0d00c00900f6620300c00c50243c00072886140102584940600000083d403012100b50103483c89105091303095811140c009080481445020000d030b400e0003001f01142640141601e2800c540c07000310104498000400340d417901408181000556004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946545377 1250 946544127 946544141
    0x82b05040c29160f0605240111100c031104090510080604030207030b10230406170c100203040312021506010311190e0607150b040213031205120c0706 66
    0x38510050b0200c41082000c00610500005004014038061144280301202c508a0310b00e961000c003c0c03096080c0340c608044455543c01416941e00d00c54a159040d03503018481c7c9070380c1100c801d0081e000b0921072190801c0145612210030007803603242c40c0140710811005000340050801920000348505003665103643c4c89150b0341014009074024010700c8040313900080c05078110307a8000701c0700c211a5a80109411420070070b81c007140c04041c1c080510035449804850b00c2d00c02c5103050750b003048120342c1c03026121514801d4052151a503080000e56091390308100030112040708490048902d41584e81d134031840a00c0344601e004006070018418030b86034065031100d094000f80f0910301800302444c4042910050f11803130641c821040118085a00901c0c060940c03904190350040450392540c2e402d007414000c41030a11078040c3c5081c68540c03809114941403003540d96001041820198050460307403045424100442120203007d410700c00035020003810703041148104a1000d6450310b8001c6131038050b0695480d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946546627 1250 946545377 946545419
    0xf1503150f0303040b0a050f03090312060913080904020c030f030f07140d050a0f1b03140103050a02010804110a090c0206100e06040f0917031e0103082b05040c 70
    0x107450700d40c1c00a560000150b805480540103159a50083c0d0756098546108840c68220711101c0482040400f2801001601490782c481d4075401060f0743300010804070324000c840b420403650903d5803690201c0c0b1580041c08140c400903200501c0c0c89462aa20752642e0404442448560000010010810b18401ca51a003105040c1032580b00e009500704180598001e00d05080102d65230b800000340803c0343d42d00b1680781440c0c0d000c010010441404881c081c164480c1c0982008207040401d030865003059449000d04a07900140501030860642d0300440c4d9100c0003410545999450380c241c0c0c100c83c0e03550032000004110f15034000591640f030040180c10708000a0124207680c0400001704401f01ca0f5000a0f60702143c11140000c509500b59000c40c010401c00300042c03c59440080010342520742800214040c90044090380c0c8800c0380c2307080450468000b400001c00700c400502a040d120400e10b10800084651454211218451840100d08454080380c080e03948a00701001001484000c249075807425207 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946547877 1250 946546627 946546639
    0x604060501051e010e0d11090103030302030108070e010f0501030903021612020117060d12111c0216121112010c021005060627060c12031906050306040609020f150315 73
    0x4000030005e800322255800300c0e40545c0c0d540610720704210303290080450044009007299a1540c44e814000e00030341090060b584c80d881000c00100e56998600c4c400e6048400030700c0b02659540c02c140045001c2c0484c0b2004034154400c40d801043e528400500d544081c0c5034010200705d1404980c0001080e59a0a1040c00380e0744943d4010b12000c1d031076140d200d0070101c0c0c000c4c03c6c40f200b104154204440000c079003050482c042c014202c1c258862004151252071128031a401ca40d4198103124090300400780d14402c03425813480115185000a03003a58000b914140001c11640c0d841c4a40224035007910050380c40800103030027075080300c540340280d0b22600b5002541074a8080c20324900c0f44500c0650b140c0704e0028141c00400c0c0d803e045141d80d07032108907040504403000703035070030b02a0315580c021840e001907072948076400c080c080d0103903a10340c00e20810040b9000113009100d00d8840d81c441400420f01361509980016101542d11403d84136900c1c48040c0891076541070341d0740c2c0b6100102c1d608090380c011659124ac5 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946549127 1250 946547877 946547929
    0x180506030606120c0c0111030a05010b030f07111905010b010801060509031b0f030f1e0d0e04090303060e090309040f1a01051804090326010b0f0c070503060406050105 73
    0x5254001650200d4164003601942ca480310042c1c800329021310305515117a9800c081150288680c5000034600074001d140041c070869880760001e8225000c210b03109004555140c1c0041c0c0450f00c500e0304145101d046500752a00350b220309400c00030460142c08140c034140c0d110544204156407280825005110358074091381130401d0600020745510b0884528009903088180344102541d518041710303c40a03009045400000750158155140e00c0b01c4520080007070991010390880072004900d409810145644260440c2860340401005200da04400d5080507a1030801080d08000710086030301a03a560001036803074107890010001078032030f490101c0d00401c0c14001601001c06c1003442024000e80c09080c110f4030b85002c1641c2a4809600d0303180341e0303805400d20032040203058000003d00b014000140c80585100c50303010100200384028810182c00010030042000380403203110180c8060102c41c0241ca6541e41d813580020300c0c10070142c505583d0030f540d0f580100176500c0c080b0614090403401c100d0b040050707 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946550377 1250 946549127 946549129
    0xf01020d0e010e07080d0c1a24040c21060b0301090509060106030e07060f0c0c24210b01050f0708030411040c0f0f050c1e01140103030504030b19020c0d1805060313140304061805060306 81
    0x220655141c4ce00010b461884546000d40183c2c100070003401955800907103035a55000b4141c041e000c01d40380550107001c2d000001c5040e41c400e010354485a02c0078401000712174900748084501c418021192410840448080b03000035210210400041800d1000c0c1c0884480c203c1452a03c0a60a19014140b041200d4501080e240d440c0043c080300d065007100103109030000b001a1818429880441d02c07040700043c0503410020b00101942c06603000300140c2008007080002c3c0011241031380540c5000c00c8004005114881c414901014081c9041c44c10b68103005500c03000525185207000600071070314548802000c107190911076402d01ca14003284c000501d500d0354402034941d224a000242c80c5000d8400018010f0301944a0629083c01040c011551501001a4941c46207091655140000d02400301014164940510740003a04d40041c00e451071a1104880103580264500341151502c0d42c21540240d4460b0a0014000405540e00e44844903050400b00c0e00c640865508450b106040c20b1081c4255 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946551627 1250 946550377 946550387
    0x80f0601090203061507050106080705091509150414010513090c1e1203020c0406080606011709011b020618011a0d050f01020d0e010e07080d0c1a24040c 67
    0x11191101c10050b520385804002c95907842c030340071311094034400000d20a420004154400c03811605000c00303480c6d42c9915a8100b1881c282d058424400407400d16100391081e01d09401100d0b04007141c0d00a0034a07507000200494160f0302141250a0000f10703e500401c0103080c0844100a888000d640421203440702d50744100c42c10020b0b0140c404644036141c101c480c1c00c0d811105207006092413440d644006aaa80b070000e503150510741c8000e0040c0c0c203060780002d001d00002851401584140c68241440389104021041c1e0351300100307061265900d41c00e001e1032141a2000246009581da8083c0c00b007890708940c0c0c82c2c8400040c00f250070490389010101c4034000c01c12080c898a5030300440d01c0190f030070b100f41042031074900036800a40f41c951002a80c400502050380c0005144a05040280011380d031100480c1d80b0341030284104140c0f0707006095180e40c0c01c0d101d00d801100d01383c8202607044e207040456451061101d022100f201c0301c0e0400b00c11202d000040c1402100ca00042210706103d40c540c803140040c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946552877 1250 946551627 946551629
    0x10f1a0a05030a0b0f1005090a0203070f020c091906031a06121b090603031c0c0905191703250b18100c0e030105091b0307031e080d0f090507080f0601 66
    0x80d18004031401b0880704c4004e5000c031001020000c113448203078104445030754000d41c01901d020700416940208005400d00220342c0c6500400020700c04a5a42c1d5044001c2098804021308100026595200071000448020426000801c4203a0280851500505001c6c0740080108040c030310f179000c2c0103141c500190b42c10302422078800658020301f650702c446002c6850340c041c8a44480d4000400c0321580b1170b0001541c04000108502c0d5514024603030780310180022044109a2508141d0000d030090141c02015412500c543c0060780c1100c0c40d00040d41145c141c10000040f40f040400150f0030004240040014106c1d04140e0702e12038505804582c01c00a9500c242c409010343d010b544803410104003a00480c1e800b41240c3e8050000d10151409943c0c00d9240d10403503043c507400c80302962100c549820001110303801e980d44158030b070201c0e042820203841d244d83d101404691140c0100403481c203500c411b000d40301030b48460400200368454186400c030308040c502d0304401c90702d5103c4920781d8445000051428 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946554127 1250 946552877 946552891
    0x80702040b01050c100e100e03030f1b03010801020405090a020c0d120615170a060b0a03090804051c021e10030b0f03070f090e011503020f03010f1a0a05030a0b 70
    0x40c81c1d0344010040c1d03058041e00c00101c4690103680f8070801c0d00005d03900005201040e45003941d50a10203603800310304035806005201c00d10342c4103000203021085d010028030382101400884107a500c1a245108100303a1013608012003c3e500400c0402c124103240d1000c40e0440e900c54010360134a9001001180e42e0750400d05244200516640f04201d4440c16a0140c0c010700052401c244900103d5070000d082c0792000e1314003070340d48010f103c0051000002e078800d10085d1030034890a80c0c949030f8856400c4000d091095025500e05c2c00170000010107590b2081d142c40341c000c01d030051060042d41801000307143d221585002008143d182c004c0360302507440e008000309060380350500080e01207100c00480c800c604440c2c0160b03054030a2200c0811a41c1c1000041402c440a003101803012000c417280745400c0e14204500c02e007030080e00310300500051074100341c1d450248401034000102000030304c400e030058034041103415841905118a0100c181001c01c1c404025046c107400a0000d031000c0e540d4402071040041c841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946555377 1250 946554127 946554131
    0x60e041217070309230d270626070912060209270a09020f01120e07060e01020c0108010f03060216080712030b1c080901110708030c060105060708070204 67
    0x20500203008001440441c103006444400c2840c09250182c01020356000c142c0e41049120f400a043c090300c0003816128200c1d110180c9200c2175151030541e0700c1c0520610581c01174859440c162034440c0c00548000c000c02d450791f1406418421510b6580080c407030300040803440c802c00410801d60541203001c2404030f620003030298020706041c3c20800002d00811074400d51001d200c80c1c6420005031101b445813141018180a0040c0740c44100f41c8108039404801c00039000f00f24080040c0041d03006681c0186598100c006c0414103d42c540a09810103c030780d0004004984c01040e103c1e8696070401c801880341400382001e240650501542c003000d107409101c0100f650303400003103401c2c92884071440032820030341c400c101589491a0703180044180054102180020740b0b071810401ca549441c1c0764915451100d2005040b08122544031000140c1c80185000d0500c600c000741180040000c04c1600006d1030402c002d1506c0700300c0350300c02c02c0c144501039205c0d80c4a803206000500c0412880012101404c0c8e0407600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946556627 1250 946555377 946555403
    0x170a02072d08040b0304030e0a06021203060f090403230a0905150c1e150103081902070b0403150c020708030a0e030703060f020309060916030f0f020904150e01060e04 73
    0x16800c4541c0380e80020b220b000d001c070f40055414064406035000f1442600c80a07100312890081c003440d55524411078005901009084002c000c0490055800040c00341c00e2440c51407044010500c96402601e044001440322244c1042c42c25031001d190b03a4989180007101d241c0078130b03424010318415035402641e104044014080d550140c1d41030442d0241c1c100d1006030303035903504c0684400203403018403114000345004030303d200344e480c614014645058907403103100d150400c041c080c00840d1030700510a880055118200012901d84094005080111710400d054002c1d4241180c070542950300d0281482d00f590f200d22024407481c5808070550300c44480a180102040f13000ca03000a2900c0da442d400504014900801c0b00012000394001318400d400c0541207854a0b15540c41c0f00b80e03a601c01050b030043c010a040b00500000e00702c07648001f0002c0c01507810f08500d811a0b000180490015501142c821500c00c044411904060190403140040c280082001e185005800203505034003d00040c403806088107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946557877 1250 946556627 946556693
    0x10240e0c31090c050d05040f200315040b0106120b040c05040303021618020903030d152301020a030813200f0603060604050907140a170a0207 62
    0x4241d80c460991005440050685058000c10090760511a85080c210070300010811451902800c00e41d004a84d07250b40c03812402d441408014a006081102c45031540d40178800402d20444006c0d44200b81056460348030b81c40782c400c2600c0c1c01c82c1d50a100b070704042505d0420010034489441a0304556480c00c2070841512554500d10040c0358800440d54401c0c54103202e10307205030b8440c01620070303a8460b800b290112420340300d4a41100440d84541590303508034a044440301640707600900034508000e4222420400041451421b0741d81e0112a100e03140c45041c6d04000301d03280302c401e002506501d20b980000300500d81c00000c0d00d5140402e800303070038007805070007150b2070300a0a1200340c0c425400804d9400031041011028005c100f010800300c0c0319446e00700700081c2c00d14150080f6400f698009100a15091a14040c00b00422001b0060002e03c01c610a0490203031101000a014402240d541c074122024402560031015201924241d00548113215410001c2e400d154000c180c0840e034103000c5001d80340340d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946559127 1250 946557877 946557901
    0x6090909020a12141c030e03090d020f030705031b0306060922171201080616020a060b0d020a090e100507020c0d110a03060b0301110a020a150b1210240e 67
    0x214400e071442201e81005031180b50004105045c0c0c20f0365000d220050030050415628003612058580c80504401c10308014070f0110010743e8041c0700601075a540a54940009003091b10310b000c032200c19456101ca001c2985801c1c003000b0350040e0100d80c02c0500f401e003490080c1d4030041824150a400c00c03c08091000e11090140c030703045031011424400e0761410000340310032047c0d9082c0314a03101882410041420410031400005c0300400982c020706e2040d02540303070030303001c0e00602080c0c80c2c000ca91400c1d040d000d61103030740e042c030013a03d13410354086102c4401e0300c80145070000742011031026a10700b10904c21216400f08903c41c1c10201166804e00c1c0311520300b00a0044111001406d9028520307040020820115400064048000300d00801c42000c218002d4413882c4500e048650041c0c01465100d00065100c0340092081030b62044001164013084022900d03440314070130150f00b254810b01040320300440743e010703075400b0011014421309a460240118403950040f070199039259032032100005d81040c506 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946560377 1250 946559127 946559153
    0xf0503070e18070210060609080c130e1207050601050312070821090d020c0d02180702070504060f0320061b010b03060406050412020607090b0a020c03061006090909020a12 75
    0x1c60410710f4100000080d5858140e00c441c13040301410860005102d90190846070120b441c44000f800c0081c0881d0104031014007601c000d8280c07a60341e14003540718038408001c501400b07240070411a640da82d01d0708100d4500b16050b4060307482640030300500400000f0103000c0e540d407103511030384180c1c4400c02402640194129000300d01c1c5010034441c1044443d000000c0d4104900203a5000d94840041040600864604019010350020140c0c24a080e80c8c600136080b655000c500c0c0e10540345450344490000317003a40c45683c8080d0001810b60818401e00a454030385d07200b001c80c811007100c18200c00c0d10103d40c05020302110300c1da0f22494039105d8003001c0303420b4226041e40383e8024180c1e02646010310303205005040c103440030b4031006a000681c2841900028400b80120f440d5156200c4c110f01d0f16000781d205a0003c0450401c41c0242118810b4540302045a02e00030040d8584507101c150400c500180850410382c402600d40c0d080410710030158440500003005e6801c1408100c031075034980d08140e1800400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946561627 1250 946560377 946560409
    0x1f09020414190b030105040206070f03090305190b011215020c16080106210b0a05220303050708060d1127010605040311010305010e0708040302070b0a0504150f0503070e 74
    0x10000400014481c1505500c821190b400e4003041441005000d1500301c8108a50080d0854010020880400c1c0d1508000d80300034864a8091103142d129a1128117000854142d00c81201401c12442300f000381d5818018050f2400b10a42000103030780b51609000340c5641c55003403020950000d010ba0305081c1c140001e40e113094404503448000e984d07411049000b01181c0c411140320501c420301c1c0581503407075801d00d00701e620340000301208183c0b542c450200092501410807010410090f0b408809010f0134014032203001d000351400501d5140030740c800307400c2a100078a07241c070a40d4400b1121001400c80301040d801c000c025070704c80800754030201c960711200b00c1002444910301142c0000040c2103500200500c01d0340c0c800d01803a2220340b8a80300543c19210207024404e2880b40c90070019142501c05c0c501075500900910448121b680d17a000c5a000a0303004140c15800150009424008006061034088298409142821604034040c500509078080074100da010445e0107080c103400350b9541e000c20485042 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946562877 1250 946561627 946561661
    0xf1e200d14120c150106050306180601020c0904061a0324060a091803030b04050f0403030c180f0501090806090c1c0b1e0a0c0e0d0c0906261f090204 65
    0x1807120966a40c41c41c140c0009a10b61355410000b14540e8842c0e030a0300c2c01088080d0164208040300b030012201140c0041c40241180304030a0319100d00c1d6074400c03020340203a00070100041e1800340760543c2d40c8030745c0004c1d0b0014080d50105180109121f0703e19250248041004d01030500c680300c990000d10911010b51140480e075050440300c002a0700440049044648603443c10440103400405000c2503c608031040000225144000b6021900036007200020542c04c0c98458400002243d90200b40f543d00d400c000c01d50130341a0001d205550b003010801000c1c20006004141514144c00b64943c1d441aa0365083d0144e8181e07001651500920038580e41c005034402c209801c50711b0810603d16480c0000d0341c2d440841c18a00c0c001c1024850329120741c0013100e41665483c2c000604840620010078070f10740d0215540200b8410010b16248030748522005403565845542c1c8054203c41c0003501d14055800c8030105401c44c142401c000070340c002c1d00d00c804e6999100c01095600c1140000b81c01040c1d00d143d44482a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946564127 1250 946562877 946562887
    0x60c160c0e1012030909050604140108010c140306060304110d0f120905010e032a0315042109120f140a0c0f061b0f1e200d1412 56
    0x9520301181d603101d0b000940040305030a60b9040091150241c0c840d0190110f5603000d41403040700041e800c41503000c140548040f40100003d5401c0110032070980c0841d400f44d5445582da05055400009140030210066a41c0e08508081000440620000e00010841984000302d1440f64490b2100b101c505504481c07291080074560500b0740149904226403000100c1440000c5007542c0914640403c0f10b00140c0101404070400420390022850302d0012400c1d0200503442c19200e680c1008022994030241c0700d0400e00d0b041c030b480e12130390160100c081218800081990242c0d4280d01040c00d500300c449010405400030b9140c14050f007620b1041c0c2001c1c1203011107030312503c425180010201c1c100ca07c606140c14801b55503071110f1424803454007554000807001e0300d001c1201c51071404103407000ca02078115000560b5542d503c0a81c400b5034201010591083c8189840911041204410805a0421807000303035041080c0003900040548800a0403494900d0014074200d00c00c00405050760f583d000215524 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946565377 1250 946564127 946564139
    0x40c05190602150106020a110f030a030302121b0a08061504080d111b0105071b03050604110a0b07030c060902211b010807140d090606030b0612060c160c 67
    0x214500c0e0003404090310a43e00700b81207066403005154100c514130743c098003c1c03402a0399002c81d0461500025070b88a600390042d10f00c0c503501401901480ca210340c90041c2d860395240070419252200a103a00110050000742c510031810310411545045c01620b459a13103507030b0305800540c50810901c0c10511400d000b00d000301e00407800289032650303c4d10503140c900c0e41c03000310f0300c0890ba1035050140c070048001500c92501c1088d40154040c216851103154075006111440314588160502580240c80d6544440f041c4414004690a01d42c42c048050f1408284181400035495261107103500007010048000c90301c500f031203000d511103030380c2d02c0c0c0c010100c00310480314054039904508170b0400246180151610800c40d50003810318a031028406865090941c8d60f65081550403d040e0841d0142d054020030454004078080e2082080c940c0c41383c0d00c00240182142481c0301803040003003840f8010401aa40d4040030b05002805036406908001c05a944442c06401d203442000b4185000f0510203a031030b804070f00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946566627 1250 946565377 946565419
    0x15011206030b0c0414040c051e0712200309030606010e040b18071209111c0c090f0c171504090b0405010b09070c0c0b07060b0d0f0308092103040c05 65
    0x1c0341c0ca4800e0505e52100800304000031210144146000b00b00708001500428414011513201070704401071081c188030b0191648410b8140c0d8203402c10000361040748241e00c841119450101c500d0100d0300a608103200080429a45e07071000e1b04a034140300f07003c10107500350303a22500b1814200d04041e110361191030b500504652280010b440150206900000c08006803007184641500180c11170705c001d04c1c20b40448180303c1216460002c041d8002ca551104102180908240034001d01d460040010b090710304800300812940d40c0018901000500c1030708120900c201c1c08210b0304503040d243e01e2142180320100003001001d81c400000c0c0001441407c001c01d002065111203e4043c0030344241200d942e4070f03041283d549214250082a8010102c0cac103005c0050204060500c083c880d250018a410354000018800d0940003803c031091b0741000c90f45170030036070b000c640c0c0d47d000410a00140030604115407640c0c0d8000910701102c2d0100c20100c00102400703070440c0424002e041c00b03000101e00d10b486103030400ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946567877 1250 946566627 946566629
    0x10614041818031e03090f141203010e010f0f0806070e0604080d0306051513061b0209041101030609053106020f0415050901081906080f0d0e0915011206030b0c04 71
    0xb80340c130001c202c43d99503030003030169010a941c80200107070f00e41d019030796000e0f40c091590a01d003260300c40c400701c51103840403581c01140038103602c4002070042e42c0340c880c1c03090081509401c01d40e0311000305241080f80761000141190040182d013044030200110401140190199520202d44d620a0707000f014000e6815602040645e5002c2d1240c1084254041000052b4032406600080d0404010001c1007050310441041c94641c0c500f00740364442c51103070340001e000101c3c25142a10489200d10f40c5165a40c0c0520885008100d442010300051800741c1c81d07920039501000c18084907124001d4082e40d100782196019142d10740c4603100f19116880d400580046030001d019200400d00c16800f07201906001d1000d940c00c1100580d65107116030f98400e050001c1d2140307500d050035502e880305404905090244290441da07031520300248541003c2030310061190310400d443c0c5020724101e90a201c03100c1c5c60f0a1031407032060030a082880c1c3c0030100c0716403100141847e46c0090114004c0200f40078040d00c2c1640200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946569127 1250 946567877 946567907
    0x6030b0307081204032d0c14030708060c1612050705250501050c03070c09020901120618020a05040905010303170601030510031e08070b090601061404181803 69
    0x1d80407522080d80b1036480c40c0440160140761414041000000c0401070b071108103d80081143c201002048002c0012480c00b00088440c0c00000c44140030503004010782035800d140440003001c96030b2030301460a80302d42c0b0160110f014514000b0f20902e200c44803100f0811065032140300381041201c4481c00074100e400c0711308104c6060080030143c0680388000c07100f00c8800426800d000b42014075100064446a001040120141c002481300501040001a880300140302c004405030340c840707030100010401d24965001c00000e41c030340841840108158400c04849501c01500103949640006050350035000d0366200050150604001004242c4c2c0010303401c000c00080070b02d0401d2034031014019815500121507404080700e8001d02000481c00401c11141452130110384400182c600b40c80700300c0b172a8000241a40d0508ed1041405061a4100442e1740108918904034451a000b50301e0104103205038840c1200036226102a01c2081d00b240c0d100c200441d00c11a060394400c211854003504c20a28a1001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946570377 1250 946569127 946569133
    0x10080c071b060e06030405030a3501170a080f0f09150a091d04030f1101020d0203090607030626070e19060803030613023004141504022806030b03 64
    0x580e050402a0981c6c3c0940ea2000185007041c050135000c0798184846110660490060901340087d288a0650f06000d66000c44020060b90705180040300c444030b21280510b0b1503070100300004081103101c0c0545c0d0b07150010303500c0641c1c0e41d028404804c155001e00891903911440150303c050410701e62400401782c0b00c0b03040e02c4009045680c0c2d285102401c0220b85070707851602e8918001000a4810ac650605c410700c50304144044252541100c1c1c00c9801031030032102820b9001080c42414001000a00da010303180e803509204050901681039958070340d01d1340c03241b40841c0c0500e0750603d9803018800840903005180b8007000600d0040c0c0c0510303503401603141080580d4a40710001c5409e0801004982c41000041c2c1410f40f4172050360242002944000f480008456615110109040f07030035446841c0d400e51400000c940d8100b9091400032400300400d494000d1303009032041410b91792910001a0f125070101c40d90310b0003180403e0703040d05541c1e00d5600c040600101c1e40300030038169090b078092080350350b065040b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946571627 1250 946570377 946570397
    0x20f0d051f062d03060609050306090c01050c0709022701030504021005071e080406110307110f01020a02030f0318010504081c1101021602010f080610080c071b06 71
    0x425400300c069000010082010034082c0318040c022440182c100032582c10206120a04401c2e0414500841c442c00740040c1e22207408000813540030740c04074082d28003200030300704e24109017203070301c0e521440300e0b01aa041c0700c2d0204510704445410310500c001062610000c0d0342d1030b00705080950001710803100050307940b8400103029149511034070906108540c0074040c00b00030200140280e440f900112411988078402400f4a040c100c207005030b02c2e41d014440d0240f60f80300c50030b10341d02810019515000b80034a600c10b01180c000300300314608568031910191907400500809c500100e0414481150194041c800c40320300038190b490000040081644c9840c00d4860584400d00440fa035108602c1101c00300d9020304081c001c0e90b07501541e080071019050805405070b050b00302e019400d98006d040300b00c01c13245108070440c09550b0080c010b266081c0c16458151000d10f461400903030403490052900c07080250784400141d0b20809901200c252507001a00c40030305480381c01080030010403a000390380002d801c0c120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946572877 1250 946571627 946571641
    0x1507150e01051006030513020307030b0a050c03100b0d0b04050f15011b1e02090702030705010f181113060e04210c061509060303020d0e0118180b04020f0d05 69
    0xb04aa006910b045640300000d49451402c070046c281c0588030741c4800c9441280c0e02d0060f40c04002080c0110310490500090b45080c9450000b2680014265041e420040080109180c0942d0444c402e0340d400d292040d03111804041311800900102001e036411601d44800c7c8055941044010341c4591046501040410800801150140030810303540300740b1a03115043e200041d80b00007042c1e562003964500007146c180e15400013801d0402c15202d210150700001010b0080c84000c0c020880c4160000c0350602c0000a440003151561000403400b0307190b181c0100340032985a8030400102080e0100a5003805071580b42c1030f0800c0d0403803080d501103d0351100d81ca15030519550310031441c00c501c041034503103d2504070681c592034090282c8a280d00741c5041101804074410b00280314000240d4001e0380101652142300784090154051342600314180018940381044880d00c4540750b000b91074150001e10038000c0122100e0b0040c1c881a80a20350240c00484c030401400603120140c814120900c01c14086515206 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946574127 1250 946572877 946572881
    0x307050c0f1c050d0b0a0b03190b010e010c1a0c040905010801090809060d0905100c0f08060a17100c0c05061b04050402071a01060207140105030919021507150e01 71
    0x1a0075107444190b80d1008203030700c1d0140000d41001544940c1c0072071030f8408000028400300440c1c00c0205580000b0080c030848075106180225440c524030070411000000030000707050403011400d92410094442481c1c800c1105118a456424540f03810440729800c0801a0a6064029010343d04d4240d203000000030f0f081c401405001c0000ea048403c40303241c20704640c203119081d4041038507000c4e440d44801344400086c43c10400301d0002d820078900021503c0c820030f8002e210703034500d450f150204104041030140590741c0018440c116a5500c0f0320031210455885030724145000c20782c40c610071515002d01702c003904d07410507001c920403840341041e00e07070507620030904000b12960844103040320f960505c824005820250300800d0454002c4a003244c03036044064190700c1c4424240c020100582160104200240c403415100701805404d08000f801e510b4259041c0381d40da580074840400c0010ba01d105031007552607400c1007481301c0d40840e041e80d554420700d0500381c1d10226902403164183e072400403085c01b542d8040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946575377 1250 946574127 946574143
    0x9120f0d080606071b0b1303060b040209030c090a140c070309050a030312020f0417160501030c120911090a0b19030b041112100b040b03060f010312030609020307050c0f 74
    0x401180c241805174075070380040207a21048840f03100c41601d0105103480c102001d06050024202144606429498004299010b40754024010790062081040c02c0e9000f0a841900070f506886400440c5d5499001a01401e10b0801d03002c003110035441030000200a00c4000c1c0115802601c41c10a074a9654003806069100782c0b0000e0700080028040115862641d001411444a001c401c14102603d071500d4440c0c10340d010705a0040d40e40001d40c24000c8512040001e80180303005d09080050a04502c00034100038941200f8860856582c0b405004101c00e47c100c40d0048035018010103401e00e004200c7c00000d00030800a40d200d03030040c102d038040d20076003440c020b419203074025031058641d00e0b141c2c0d0b08a00d0000c1c0c000c03008d9102d099500380d40e41c100010090780041c600c1d0050b02058104640c1c007440120381d485401c0500941000d000c00c4201c685030f020a60460f648510090398881251900b10010209134000b0040c2c1c0c0e000006021001e41e0000207000d40c000c00e03000b07560740350880c00c0b0402c2c0c4d07541c1c40b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946576627 1250 946575377 946575379
    0x6320a0503030f033103030b03060c090402070203010204121505011e0b09040b10020312010e0103020a0b0c19030e19030c0501200d02030721020c0904020609120f0d0806 74
    0x800c4550050400d0f07001858018044050000d00c0c20990f03a11080340e0700d5031103000c841031040b03031040c1010302d03a160180c00c65625040c0d0252242c2d00700180a08010b102d80030f80319004580001d85501151400d60448000b001440d02c3c2001480300d42c43c0004454894920b542c0c95241043c0011441c1e003560300e00c1e034541c44115601d5031501483d0030407006658006d12a0150300c565150308c0461543c543c5000b001d500d0000d0790203160354400380b44a030404000b068120780400301801c00180016111202c419003502c0d604200d40780c9400c00012064900b0100012141a030364401d2812020540c0211044000c80011515101d40300c1032511550702d00107513032001a2446075000010085940201e048550074800055006181c40b040340070145010300505041005070310004807001448000e0080c081151000c0750107010701800340b600203689100c0480c15501c140c03134013000309045583e0703c400c40c0d14065002e40762150003104482d60381e4440f80084040d0781d26015810064101900c96044140710300c4e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946577877 1250 946576627 946576633
    0x150b030708040f0620030a0c0221220b0904050901050601080a0e10020708180a181e0e0109050f0a021806010201023705120703090606320a0503 63
    0x5583d03151981c04820b505800d44949960700181e0350761000002603140c44034a16035015640742030402c2080203e5012043c20011908920445c040b051102c02c0411281c405003d0201d451f102000111141101075010241c0001203041000030358800d024064410800c2c100c400b0001a0360b1030345610700361542150600c0c0040e5a4200142800382168882010048424105c40d1070041206142049900441040e10380c8600440d020070b5046141c0c2c00310552900a1ba95103910a141070307140010400b901d041107003032075103c40700c032b4200c43d0411042c850b18030b00d0301c070301401051420b4081038000c0501210554050240820507080003034001145041180d001d0241601003080686400740f804004c0c1c886411550200078200d903812400d0080f201402100c01d0340442950b0b40c404e60b16004036041c80c1101030080501800741d00600c00040b0f56800301e0942008544284180742020044c109030700060b182c0c801d1070905e542464000c1140c02160480c4ca00c0075104604407004100760800c0c03620a60b5850340c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946579127 1250 946577877 946577881
    0x519180903051b030c0d110d020313030605061f0806040609061404021b01060608070e0406030c0605030711030d1a0402030f041202032a061e160c02060a03150b030708 73
    0x1503600000103c24815000690381400000032055040c240101c101d500050b8420401149400d005e00040340305e01038038001140b40011009c0b180060085610001e480d95035144000380f0580c40d00189501515500b00200022055600e40a080c101d03096982c54015481c004010603883c490307100e000b080e6442c040810b4420305114040201135400880307080c5400800300745028000702d00340541c40140c192502c40210500c0c2c0b40000800710444040024441c0f411300d40200301003802902c007034081c2c0b078032481c0172903495481e02030030780d2304050102400c465032100252480700c156050b4404229400c4a10a243d5000250800c0005a00040d100c0b909603d4100c0302007400101051500c4d01906102d0041e2400d0010450b00c60764035800ca0a000d05000c0300480d10980585030620046620028022030b2442d4507140f900306c0c00880718000c120452010000b03040d4135410740540010700840d9170003400559242d13000d1074024007800c0a16a1a4030b0b00e0300101c80400d540030f0100503281f04104a40d9902c00715 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946580377 1250 946579127 946579147
    0x22051c0203030f0415080a1404031d0a08101d0c040506010c050304062a050c0105090103110408011a01080f0406020313060e060601180b030f070306051918090305 71
    0x122860100320381c9448204503401c60200a10f000d0002062041e107a6801030940b03d2000d04100b000402c00300100d454007a00c0030010400c48200c40e08a078051800b03070103110104c2500c203e40c442c480800c5a1100800000003054100011182d0007003410581c24000c000031002c0c6894940700c83c0300ba0340c2d403940040382004c42c1c500b440d5111540c02070741403603d00020031080d19881d096600c00d40256001074180c0030701c0402c9844440041c0030600182c2c0d50031142ca012074949545911002c0380040c108000003d40f0380540e0300c01d4104c00c00c1c007a4580c08150780c4a07515074417540246030220549144045400700040c1c19805a50002d20500d46650280100e540e16942c0038001d5200038140c2c950000304440001c08105a0321800034095008401080c960030108009007948042a41c40c4201001800d0103000c8141c2c3c44042e00c0d080701455a0121040c0c83c0d2040550103405540c00203034204c503075040041d04081120800e03070100e4040c40d4560002030082c1001c001610f6000e00b0140100340204492800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946581627 1250 946580377 946580419
    0x503070b0714040b1b0a021008040302060c0301240e0a080616020f031204150507020c01090b25050307020d1208100b031311270a0203010312110f03030c2205 69
    0x504902d141c1075544106d200e90000f044000c090b655180098000d804001c10160100310b2242c000c2c4011a405055600d0555030340c21110280300015441c1c80c10794810308031a40502c1d0000f1500500503d030020060b01d800a4960342c840840d81041000ea280048540072400418084003d10101c0c1c06580351502c030300b4040511a01c0070300100c4e036500d28010921028007040c490540920410783c040c0036603020100c001452041c2a400c0200300900030071618000300f25144070030703d1101844640c469002c820f4181242940074542020350002c903214456410041984400410039600362039016242d15100d2044451000368003606400313070010000300d15605084511100c1d0107100c1c0d83e00b030201007100d8010401042c2d19810072001004800d410a186086950309541d00813111513003181558903607201c00d8456403510451130180002e1105581400d0750030f115509820014000700c90340d0b41445441c8210380d500c08150b00c503010780800311242c0620401e1541408641c0000c00340500080101d001d110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946582733 1106 946581627 946581667
    0x91e030606141215010924090c02160302010c0b0c220501031a0907050f0408070e061804050a1b050411090406061b0813030503070b0714040b 62
    0x8a0392803140007141c1158146ca40202e01002d40c6860010320300911404060070102c1d140004c07500b00201e4011b000c0030006030742103d0226110740461040240280002400181c40d0300c02c90300480d05c0b40b0310280d00041030110303da00e0300c510308605100384810b04026014001d008a01006990f0b014450204c44003803d01419010012040c0010252000146030b0400d0040204480b1800c1180e01c060707034054001402140c010301e445102d4034811000403214a81310700844c3e404d494004110006842c041c945c050020000f4540c20359071103507405440b551307080c2c40c2c200c600400503d80d5200d010300110b8070390a80500d030707840d14403600b808107032082508468188403906402107803001540da00e00320002d40004010361035045480c11041c000016501c090050300c400b00c0d400f4240102e19441501903141e0b42c9030300c060f1001122000303156000768840e420034104244014000c40401520100c = true := by decide +kernel

theorem cover : BRFrame.Cov 946402877 946582733 := by
  have h0 := BRFrame.cov_init 946402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946402877 ≤ n) (h2 : n < 946582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
