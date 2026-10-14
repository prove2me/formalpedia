-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1235
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:54:45.685042+00:00
-- url     : https://prove2.me/submissions/25dc1dd6-664b-41f2-8d9b-1f4d408b647b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 221942446 ≤ n < 222122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 221943696 1250 221942446 221942459
    0x6030c05060703051e0d0207030903200108010b130e0708060301050711100e19140f01090807080a02010603020a06021f0612020d1b090617010e030a14090d030522 71
    0x50040e4290982c1c444da0100c000380417140b00c1021105042602c280441da110b0107890701030542286800141d0b4641c9224000070802680c94401d50341088058407524240c0c2e103401c01c0383c50300758840702c0030003041101e5110019032524075800007406003006445207019850240181401c49400605810400414006d040044040031400e0090a21840c801094580c10b12003002e14101c251015030041500b81d024001c03e015009004959134000c3e50192243e1001c8041014282e83ca4235030f0140c0351f0003080003450006a8904001e00d15004203000204100d0365030340014111079800d038010400361304401085002c20072403034500d10000203002420800c050402d444007e4024501000134025060281e9079001e00902d0852102c2e500264140c4042d42901c607842000504000c3c420302c210361000014400c01080b041c0604006243c0e14001141401c00745107044546003500034140e14826000c000c00890b03500e03103d00c0400428042e49806075a112003c045509010090321000c1d003690407900c0500c0706 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 221944946 1250 221943696 221943707
    0x303050f06040b011b08070b1006020d08270f01060e1501080115050a12020705070504050a18200612090d05040602032205030a0302061f030b130807080c0106030c05060703 75
    0x550600000114421509103480e0466108012000c8c222038000c4040208403c01c68103280d094400581c00c0d20780c545c0b0441001d032942034085d104450044546485848884140c19144a102c14100308076804d8407a8408140d08480f00c680029010104040402055030501c1d407044200c02c00070b180402c0780d9850301c2004007002c01748510020070040c000421a01c103a01c00c16812000a01c41390781103603609441d1401556482241c4900e501403810b050002c0c03645800c2c0e00c03403d0496001d0b1080c5041d218000d545441c03850150030485030a0031903074425070003075443d11006000700002040032101c1c14181400708920306008940e10008000c8108000d004140e40402500c0050300820280c001000c2d090030303101915045034200903014032138401c810041c1540000d540380200d22010304151000c0046812900e502160300018007980e406201144000ca4460480b852250050785041c1c20800c80ba07840749031769400b5192648607691a00b000740203010301c0e91071500080c1404c03103d841c076000590b0341c050325 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 221946196 1250 221944946 221944967
    0x1031b09050405180d2303011202040b0a0b21010b190507020315070c060c081012060902091003050d02031305010e0d02032a0a27020c0a0303050f06040b01 68
    0x180b51940007003008081084488941c40602400f51005407031100e000808546d1400e140ca5404003805400030000d08491044074161608004142242a001e03024070011340b0b4401c11035a0000481100041d021001c800075200f150307003c2002c10400c1011025150340c0c0358041c4c0090310100d40401003000c100681c5055285410320314100180c48684600000e800c0002504d81d40154020007003c0010b0240c1c0300e5034424031548100c008104011941c1000c44031100308403800e24003c48001402c2c0b0007944482c1500c90054480c1d28007103000c00e900e03804282109000c2d24012a1074919000a00070860f0501c144001482d03280300940c1050a2921980c451509505c5400e0501c040d02d00c41011075101d515184403110b802808803000303180d404082e135072a21001000d5659904c800302c1202503030306c0c2151060080710841080c4004621080d440b26070f1a406651329603240035070811818500210500128043d6806624000760b249071400c00300b00440f8000700344a10443c9072203800c0d2016030300b00040c1d16 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 221947446 1250 221946196 221946199
    0x4060e04111606090f08070303180203031b0f03040f0f1a0301050409020d0f0b010515040f03060c12060308130902091806030c040e0a0c0e01080304091e02071101031b0905 75
    0x500b0001981000802030020100140c04030070744041280c14400c20000400d03110344241d504110000c100ca0b0079540e0290706100c001d40c9900f04001c3c209054a000c041440c0c2d400f1b4035015100c410352045041480c65100b079020b50349128030f0312410071880c04504256402460042c01c20002c0190040e0651107038481400f8461090369640c5454041d9101c10801c0c5200aa112160100c0102c06081000c42e0035402d1107042c0c890924000100c07403800d03045c0c05036001c8504200340c15200721700710707940d1602600300324507035178100810910036900c640202d000720001180204102031f500d8203118101000b40b040741c4c01880a0328010049046140c039442c40d1003940d1030120b42c18406d00d03150500001e06002d1802c0c842c991150510202c903025030408160000024400d00006903440d40d25155041039810074451421030390001d010400c002c000341d4202400011820410541c0c05040d12040d50490b0000e810907940c20000a00516680d40c15104040745010200210440240340f050000d002c01c42502406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 221948696 1250 221947446 221947477
    0x70512071d0303031509070212030f0405190f060b040e0c0d0602090a0308090405180a030f14040e060103111314150a020f12070309030206131a04060e0411 68
    0xa10103410280303803079039000c0001002d0320364905050300650203000c01608180d104800b42004212001d000190240800d290031071110b0440c2d07504050904102c0c0018800e90345030060010100c040519a003650000f14401c203c5400307a40c026040842c1110280601c11740100d1809403000d101000004010003030181c112801c0924102e40c0c9000e402a0084079107a81c2c1000d01c0300e0700842000340c490045c00340c054050303600300a0303a501d05444403400c00e08604148810b801880124000c02c0c03160414404501740c43c2010040c00040c0b1414008a0307201d0b030300c4500b00705034220a00c143c1d90781c58000d9105100725090450300700402d40c2e00d0040c2041d444c3c85180e610055180d9a07094a84821f100c40704c20f005034501a90700c0c4d1007604000394a8000c54115110035004034011540c0c51110708040d20400354240d655203e60b241141c1c207000c0c250b4801e000080c2c1c00080c140001403805035481034181032008550f00e450300c841c13800d000507010030f1000050710301c00d9080041240b41d42261005507900100c090180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 221949946 1250 221948696 221948717
    0x2010c0827010e0106140d1a070e15032505031603200a0f030e060402040906020d06060f0f111005180d09050f0d020a09020d0b03070807060807051207 66
    0x100030307803501c0e21222058554201640701051450651000046881080342130307281c107501c0c0003080b82c0407501c003d000b002d0b12240040d40300b07202502d626095002802d400c052100d0280358000a42c2c549000d1010601c0400000411180d0300c902000d0384400c150890046c40ba0300d803480c4004d80f0900000340190403459400e1020400c1500c250010741c002d900d10030035075081c50083d18958100740d1041c9406004a541688101001c0c5d12a1080a00402c2540c02624503901c5903803c02c0003034150101c06840312502400144a0f007120740c451140204500d40302e1200d000300d03103038000d0026070110015001388482c00f4810700343c0e1a40407030780491964020320001150b9841e16115103802110114001c2240700301c403107910007242c02402802c150380045a21907408280130003048000780e8203041c025004070001d10300300311618841c1c0107800706400344000400c0c11262440840c0c0b4000e0b40e81c3c400805a80800703170811078150405207040e002440c5261252800160303500303456041001520100070800700710036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 221951196 1250 221949946 221949991
    0x111516120215040b090f03180405040602071401051b070b010e131a22021f140a0305010302130e19030311030106020105060117160e040e0307050d020d02010c08 70
    0x1428011102d0141c2d0000d0a0908081a4141c02120b112005200d844407440e5203543c00000d88840c4526100c030068110081004c1c0005480040c004413900d580910482c1c0c00681e441e02d07240811050400002424a0491b840640014210800b078954140c10403004010848400e41c0c14195803c00180242e50344407221108040b141400c2c0180c002c2c501e0280242d00d00c000240080c0c020580b040c00000302c00b0383c40c402e60601490750031009600102c4d03070019034608080780212000c0c22020b4100400c54010403c8820420790043d40010f00083d921001801140792422f100c6602da802c0b40d104101d003025054006070364940030f40404e101c1c03a04040004042500c44e800150150052550040e16541e4500c03000c0e000c0c0205498482c0420880400e032140d80041c204800c2c4550070092481d441021904030030b48206440020141d04a526a500c1000c205000c0000340707209840b4070020300b030b41e414880000741454143e1500c0011641030501e18003240c0d82c0400c001c0c4c1c0245080c091180700c4010180c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 221952446 1250 221951196 221951203
    0x2030c16120807021302030408040f050a12110109260712050c011b1e02090a0c0504050103020d020903010203040327030c0510020f012f090a0915030602071115161202 73
    0x81545c09094000801c000400628101500440b030100c2c08041d1801c0e2074104000300d04c0d0076409a001d95400d54030004d4042803041010311903081d8103050000e00e254a54030403c25180040300c641034001400010120442c0040000c140140758128114202d40c10681d80d4039104d400c441d4103107040000b81c031401c0d1420b915003152610303920b6010f6401c101d00240340320101d080b031101c400c4c16445144100006101c07121030340900488002c4a54841345400d00b00001540290440300e80810266424400320b565034600340300647c00345019488910503404540c0b201ca22089107580c00800000b03500c1d50410001c4c0f101c030f06030020b0304c13800c40f6010000190b03804100d151100b60b8000e01ea80e5820a170850380c18014484070420001c1d02410024040d90441407218007500ca5103204039042210420100504101c613482400780114003441c0f41045a42ca0310340d001660007a603403c0c0d40300990014031060902d401c500c0b0802d607640101c2d07198101001544040624108024054980c100c1c201000b1007007071091 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 221953696 1250 221952446 221952469
    0x219140906030702100623040b0108040209070e0306150a0b0a09091107080304030e120a0b160309050609010b011701081009050718150603110d09170a02030c1612080702 74
    0x1c800c0200c00c2d541c80d40a242c0001290b0403120359018403042541d1230070280224000001306844032130403510b442d4288896400001d180342d0800070014400040c41d601800f40501030300c3c0f01032165824102d941c00300134856480303500003079a0b040108682000e491b0800b41c10400c0b03031070401001958a030021000c3d03005114080d4010300b1480000700300f00415410400803203a08a0958900c04440c041c81c02c20740c0d40c2c600314074003c1e121000d0000014201103100c0c00310465140b25280201e0407004039aa102d28020b0103480d01400360351580c908503419603200314a0a08124a000400c2640d450000c1d01603c0301c403003000b0300d80150b4580107100107110003002007000070090484040003c020301401500242800340b44640b401100000000d85148640111034001e616280c1142c5002c40c2c4035441001840080c130115202000140c008042c40d4400c40030b41010031883d005150740e01380103407140b41000303904040000c00301940c1d2024403c220b041c0c0d000c564520780c048401d955402d5240001394072012103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 221954946 1250 221953696 221953723
    0x80f04030213051005040510090e030705060112120503010b0f071a070c0b0a150b2508120f0f06010302180307060507200609010c060b030601090219140906030702 71
    0x400021009030b2450b41c00310b0b210380021001040040e4480003040180e0308143c500d03c450f9102501e003403020426035800300060720b1600302101d00e0f1920035079481c0d090803026440a1610445940403d05004130310040ca0303a58400d170b1500c0c918543c1059030554440c005c000141e440302101150150800c0b28405030f24006107105080d032190f5103001c030001001c0c0c90b2111400c40b040203042c404108100018002d4804100c0700d0341c50241281d00345001c488060700030310041090a42140070050455000c041c100811034040c0c00f901b5a11b142c03080c108a12910301801c006c030400000d1007005401c1c9108414071740c21441c2441c000d699135040056100109141c8100c3c150305000d44040003464075042070080c01818401c140c440050100203040c0300340104000203407600400c04114000d1950703c520b00c5080050700c42c50001805c0d81c1742002091800c0c400741c00c8000360780e60000d442544510b0b11000503215284a00e42020407044224028006004101340c00d8060300d004804107625038000e00c2410303e000c45 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 221956196 1250 221954946 221954959
    0x503070506091c020309060d02161212050705190807020a08161101021f0b0a0b030f0414010b0f12210d15140d1e1a060307060c080f040302 61
    0x10316070482900c58908000d01c0483c140c41204041c1e100e40044213854100c107004003590b00b0052484541c1d8043e6108802100c10355080706151000651050005060781d1380030390b542d1085807070001c40da008484001d0130300801e0000501000d294204d4541e07581d20104101c0c641010b83c4d440d442c1d004d91400c904142c004100c0315000c1a440c103080b13208464108164080c0910070b002c00903483c01642c0355102c114181d844034404103440440c3d4a06a005030210080240c00c2d903030001c1d980c52180019070025a40300507030680c0401440144021040f03c50f500b80f050f0b400130020018800000b6a544c2d21a1000c9400b55031003010b000004801807201050303c00d80c8103003441002d00391307500380c0d00540d0286890f10a03d5150464a0312152443e9512009440a90400c0700c840b110080801c02075a2584030b04a5800400403c5030308400d81d0782841d0b024a0f8460024114508a10000e811540384014075a50096200c07040400c81c03541d022001c3c481ca40d80004429507100954142c0340c2d418031544d00069000030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 221957446 1250 221956196 221956201
    0x61603030b0a270e060c03090a080301180e03040803090409060902150714070e01050d11030d0908010501051804020907090f0f140108061011030912070602060106031103070c0503070506 81
    0xa030f80d11010349a601e005010b955080e00d88007400040b981d00b0628680d19070f11540c0003c40903e0100000e5400072540c50488644803c955181100b03036100f6000500800503c150740040c08485000b80601040600c1c041c50415041c01c0b00b55683e03025024000d440380f612820035005111700703680707c2c21025030007802481031100021007144680d030010300101ca60128602c0b5210107402c0114042c0107039600b815000d00d03c0d902e00002c00504412001c0c4c16611030b100360910501540e800c02c04440c0c00082500d80d01e0515240202c40c1c0d08444050f8401e07802601007510380b1001d0004080c026604c02ea040740ca0107900d071a42601150302c44150307082428a90252a0007080300c11012400c2d80444041d0012525014a43c80044542c194180c0300580c0001d040581801040c0c00340303288004010916040302d05003440d8200040c2d010948020b800b03c550099242400a5035050050601404550500707001c602c01c0000c003002544402400a41040109000b0408000e414421500603a4022040f9901030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 221958696 1250 221957446 221957459
    0x207060204090605011106041707021f02010b011103030906070309140109030c11120604020105031e0117070b07030c060c1205100e01080d05030f090313060507060c030605061603030b0a 81
    0xe0a89000f03103400300348180321841c105407000495510489d840343c2402215207500c0b00f141895009000300300d034400040d40d003d1031509804000307044000a40d41c004146407030b40d40009051801c1e034848039502c1d5001001089546070002600301d801c54903904e40020741a0403410400014120f060b4603503101d500705034111083c107a1000c51080705c540a8548100c00f5241e10040001003600d100d426400c0c1d0b08504000703400b41d0b0046000d140d00c030782140403216407002e03010b040301c68031902600071194160442e412100ca0350410409200034001c008011032030403590f234a0141022218640c024629519100b20220700c520400200b00800c544c503009002c00e042003e040341d0300002c28003507402d841803148000120f0020004480c5040d0b885d03034442c2490b42d2111204543c04000003050030000380700402c2044031a2820102c14001000d540e5106030b21201c052031f1403011746450640000806051501c18052503a40504440c2c04850b804c02a04940066280035400b0300102c0c0080c0e9440300555000041d103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 221959946 1250 221958696 221958701
    0x70b0a091d041a06010f030b060405181b09060f1e0703120e011814070509040c0819080d0c120615020708031305120c03010c030b010f0c050c0112020706020409 70
    0x80c51090804000981c1040708030412500f00703c03041070004483d0000c3d030103428002d40c404100c0c1c54001d44103a01c0c1907112008a0703c040d0003050780504034542c4008000d61102310060100b02c80e85040314040c170300140c3c00c000861901607034804403000200040c40f405d504031030400040f514900079007140d483e440141030207801100b401032640d40b92414016000c201c00740600c958003502103100c58520f0441125292650341d00c03101c3d01c15400b1031003046e00c0030855075250790005200d50300c61410340c88a09e007032500c032a0030000023200d95512035500324407180020740d035181590755a00306d40900181150745000d0445a800006142203152450114041140c12825240d5243e401484d0200d0707402c0d41d40e0307000c00d80c0d0360b1041e001484603a92095500380500c1c5040d551503c10864040c04803902c858100340061300b1110034028100102e6500c0c0e8030407545580003c04072074880071900f080c8000700c10f580c95117074440031740a4101d81040303440c0c22806410022681a1070701d440d04080308540711030b22007100400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 221961196 1250 221959946 221959951
    0x3110910091a031606120b030307020603090c10080903030c0d18050c040c090b1204080c03030f04021c151107061d011d0c1e030f0c1011070b0a091d 65
    0xa001e01d5440079000c0503901c140c88211000fa42e505014400c00031b078180010700c4e5151a150303040c0010888100965103c001950140d808800070348003080300e40e030030000c0303428820b2a903006005241d8100500c0c01c2001c8107990380907503ea10b00940e610800b100010003001b20740b01d0f0890600c000715640b0140a400240c000c14030005513030800ca00b0580c94410340b440302e0703148200c1101c8a000c1040600c681008014150083e10444c2e0040c2041311070300700715007917800c02c503041007008107a101007005526040070801c519118030303041a1041103054840d1480810004020400075455500c0d04040c03c100c00c0c1102c450541106080000240444002401d90a0000030a415600300500054010003505030f02a01c1c4030a0801454208a05828041c946086132440c004008c144010541c95407000c0c041061000780c260302600c592210601003244050451850804111414040d6224070100040131b900341d42e404036074640c94913004007046440c000c65400840140001e102045421070800039032a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 221962446 1250 221961196 221961199
    0x1203110a0b06040e07080c12280203060a090816020f120604050d0801080712030c062c0309060405040b030328020d140d020d0e2a03060103110910091a 66
    0x10200f51580650340da9005c5500810245800001c01c0d10311070314040b0003008222400700143c03001011544c0100c81c5030383c49040e0301804100d88050000c1140b40502c811640301c4144c00081013003180700e032103441c071500445c0960111284441c0e0b602c002c3d50b40302982d1101842c80286808001180c8010306a201e0b101070302c04462030312135001c44815140c0925001c2c1e041c2c0700707080001e003061444e01c135402c000c07203c03455000d4040c45800440000411040d0040504140307044480300c0e040764102c0c07405045031601861861050301b0900c18010582e480004640807558210343c04030724146c42000080c10b40c403804107140c2c090340da040e1480340c07894200010040b441c0d003641c09032400703909604000c0c1c2d0030703d180c008402420ba408000300802c001240c0c2c041c02d8032200c00a4006003d15250214a252400030f20b040c180485100100700f901e403404900340c00300c205041c4c0c0600290752540d07980528512034000803c1c807800c0c244001403011120140544024403071000c085c809841e2504179003240500181006 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 221963696 1250 221962446 221962451
    0x15051b0f03270919020409290301050105090a0e0c0405070f1b05030712031d0c040f060b12130c0608270601050111030403060501030b010509010e0c041203110a0b0604 73
    0x403042c0601daa400d61030191020301241c1c415540c4070310140381c00c6004031420302c0c6140d00384000304444006106611264080400700d130085d80c0c90801c14074000c40a103940c5071080c0e0500d40180025180c841da0590001009000442e0783d512151550342807483e28020030350094540000c006480d03911178072400515095840d1050f140140003080c6068090b8444081c066500030461040001d102d80d607180311060503444e000804880140341c1602035032000c0740140b02c1d40e20007582034565103000d02c15100c001b816048100201490041c501c042806070a01c802c020b000d2a000280d03203000301e4449102200d620601900b505078648001402089003500ca40c0c203a404010740800d1040f21000c051095620844006c01c80380e0b20f081d0044030b100c00b00840f0200a4002031000000043d8203000b51800f0310320500368145c05604210900a08410580c0087c0390306210509000380402000111820b4840c80c5440c80c440c850709040645600c01c1c0c01503910130f507204e44520301040c001c611020a00034002182c0c00d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 221964946 1250 221963696 221963737
    0x7080712020607051204060e0a0b01030b070306080a02040510030803010b13140f0907091d0a0c0c030503150609060408030702120303060f090901140124080115051b0f03 74
    0x1ca0341e424040b40d0b68004100d041014205c3d860861072031950181c45038001103907441c0500066400c1410b6494120b86010380c200052040000d0004070582c05800b6107001c008141c500491560399500415001c2e00455480000c650035100c0300381c1d00805150000c10150340c80d41e43d403801209076480300041c14101200d1050215030203040d00414068400000d0121010000c0722042000c1e06d0400317414141485901580000ca02d03182280c0c901180308a004080704929049030040d0990304064450800c01101200140010750040706581e0062001d12060321030854800c0130644a1040c8403609922002c0844c0c0003a48040c00001404072500c2a1510a4250780300303c0203aa6900058072078650100946031300781528240800c685500030121400805c045d6103036500c1c0c81b0084000c0c2c000790500c0820750400b14141101c0b41485c1103010407407516240d00c0d0300d8100038440e00305050300e82a0401c4000500704032036240e25040c044009800c44140c0d215100d8a01b507071545c96100b070f002180e03e003210124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 221966196 1250 221964946 221964983
    0x1306020d08060a0b0901030f0c11070e010501230c0307150b0a15050a0201020d1a030d09060f1b060f0227090f04020a0e0c0d0617100e12070807 63
    0x18140e0150001510104140d41000c0c070300e139140d8000300c2100e4101951011242e2200030140110800418107454058046110900881c1010324a81144034500301c070070010045640d0008001c0d18514240c941c0e0706030b480c25808100301d40d10540301080410300c00803800c40c0502c141080c034a03002c4491031008115106602c0305004600c6450712410701a5034141f961a01040c2c043c03001000d10b00028800145892801100c440c11608000242410b0550003010036800c0d00341005054005d44413410142c0e07400c0e15201c1d0050400c1440e160740c81c1000403441440c0e801c2817040b2440c1a00716408034043c0302c02c03008594200000d4100d50030380c500001c83c8927034104c00441180121506042c0250507490380e6514040c2d95590a80050710032608032a040400181d07182395104410f002d011003000043d6a07540314055603040e201141c1000000d40c1c2408018aa46413000441440e800151900400c1200d980c0c59580c0c10300d4044003d10742403003400100d020800065400400d0010b12a1100718141000200d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 221967446 1250 221966196 221966207
    0x3030f270706050417010c0f080910020d0203010504050105090f0105101106090d08060a050303030f040f02030f07050f06042411100605030d030509030703030209030c0a0e04021315030204020c030904021306020d 92
    0x3503191f0b0108010807030034118540304a60555004480070300702d59801401c1901d00b400c0343e02c800c0f9403c0300300ba4040014031451405004407030043c14200c0340d0005506048500000a48062249600c56203004081d003501a01454020900c019088281e074454540f00108070b407220020510100000d8081001900700e2070701040460030340e43c02074011803d40c3d48850314010502800741080e1188000d4411140c01a40c0c100000c024500c0c4071400382c0003c6d80342600384000303180e5107000c80388150000c0c04140144a00c021a01e02030104200141c0384410029809a41180410b52450014052110303408a851800e41020342112000e0741245c0e10b000c8012012000c407581034072401100d820802108010070712940241404079001002e485014a8100005082c1c0809030700400c003c0032400200402c3d85814001c412260446180074004982c0002c4c95008100c41400002d100740d5010940b90303002881001070300c0300054060000c548c0c07400c0700fa415040783c8143d0300c2100010300c01c52008150082c03149 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 221968696 1250 221967446 221967461
    0xe07080f12031801060605120105040902400905061e010501180e04030905091008030405060a3f02091c02060d0606030e01060803030f27070605041701 66
    0xd00074040c0701c51441000080d6500150419140045200f00c00f65202d83c02c0c0b09520081000ba29130b95590715824403960700c5588140d002510891a120121002d0380310440041071102c03148044004820708200c51100340710b00e0102d00501e540b00d640000310740c01102c1c0c2c01218101c0c001e070100c450760381d1086100555044076040004000d40028010840c5501175510800c4c46058140c4202d100c2d40c407407140000440d0221405d60006000700410800350405800341500813101c406130710300d164240207220f640c0c0d1242e4490580964030024110a035a44070b449074003040010b0300c9030f01c10010386001c141c010303000e03c017854001c080c512103c0a80c3c0318070403482201d80c1408081c25486031a1240c20b07090880c0400d020307090b0f0f0440410001c4203030401d00c62060001034030046d20001024144400580d08454850304901800e80c01082808600034074281713415070000400c070022a4951489005a0001910800420540c0700302080400c1e040e0b0480094800d07140f00300e08503229007010b048041d0988605 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 221969946 1250 221968696 221968723
    0x70816050c012007091d100f0506030a1713081c140310060807111608070902040b0d0213080a06021809130f08090307030303061a0702090c0d060e0a0e0708 68
    0xc1d04000302c01040d08120003141ca90361206c001c81810b1151036041c001d00002d5030211035903e0b8845a070508640c451190021029802044e4000a07075640404421100464200890f03011842452a141461404000c1e02c014030680d02030000c800c4280100c200711255020214095040e2550005103a1003524030030917003d0fa00c1e14100e40b400380190342c060b9000d40804200b01041040c1011004204010790316240c5141c010f1005505e880d140c0d505100403071300808010390040008022200c1301c207040e1351003e240f0310001a030b590030f07400e419102104554400072550140321512418014241d000c6c0044848100d04507920020140c2005420f45089400a111007038a8040d0340c0807416022070440100d10600c1160314000041000078039154082e03204500003a2120400e001d41100540c0e2440500308024850b807d000d110f500045c0b8214005180d449000b0011039801740d49600c6400050050510700070120140c2000e00410024003124402c4485901c60000b001403111000618900d05000d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 221971196 1250 221969946 221969953
    0x70b090a060c060f060815280f06082a0405010e160905030118170a0207060f0c0209070e120715050c25030c0602010507050f070816050c0120 62
    0x1011002d031102614501c0595030595034071009540c9003c10712502c2c01801480d4014034415014170b1030b4904044004204400354983c1901e6544080800b00a400b40380a25040c0468641d201080e9080100010390003e03d0a20800c89522020f02380303c5526001e60b80c80f0410155080311250a001c1660b60a104002e0010401c0c00065800e05144000d43e030000400c0c83c1900c0e0303003552500042d003507542e115101c042d0486800004010441d078441074103600004204818182201d4240103511500d03d80308500503c80408587c1515900c9580d4003020b99500814140c2c0fa8100039038010803c40c8101c05060084035200c43c2800d00c810005611021201d900440301d004c1080b03c00d080f01c007508070800039140303481004031001c0500b40c0c944004401d0341840400001444c40c0d0f0074184c0e0518410361000f002d5901d4007003440b880c2a40002150008141902420346c3d4901038604049640710703140c6000400a101000081002408501220046001d0340e0b010300c42586040500c0410f185d01a95500070b50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 221972446 1250 221971196 221971199
    0x30b0f040209040b09040309140406140609060d02030c03040c0603150b16020607060911090103030c030807110a0606060201150b0912070e090d021203070c0b06040b0607080309070b090a 81
    0x40c05800400c0c10403000340c00869181546404186140029901203020071150401403050288010200755004400c540030f010321490b155441a548100850307660141030001742518694540c0021144403e60201d404c540c1c1b40341c041d01d9580941c0058800b102d1108011400207601403181c0681440d0040003040c0551032460701d031008080354040241c00881e00c400d040b1010241e51000302400c48039001b1040480c0a44103841e21240015100c4281c80c407c1c01c10784018400300341d100340d010f11210f070f05013407131001901c0f00b800944030503214101c01e1a40d8440c00410008201c2c40360080003c07100329030000c3c0030b4141e0310303114000e03090654023030400c200b003060084410030f01e07244941c0d100c002118003d89030620b07224903d1510040080301c00224641c804210980380e16410061a0030904061000074114240302400901e0389181e03000c023030004201c140200d0304d19500c2d5841500d61810040c502550f508051800d150590411501d1800380d00806400103440d050103411a02640c100030b040c3c80c50303103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 221973696 1250 221972446 221972449
    0x40f0f050d30050402120706080a141603050604090f0f0210030c020a02010c0602041a041d060918011103070201060f05040c1b05190b18012c0c041a0907030b0f 70
    0xc050040042e680316001b2051100c03040c2c000c0c08080054440c940c0d400352140390911515060310078102e500d40c220b66a0034100040000e4548442d041c80000745000304050320b030400000d0181ca510030340627000034070100b0002d04104a4408400f03a95100707407058030107203501c2c0d42d043d800c4550260110780942c1000041000540c8039101e4088000c1c0704030001800c241e10385508518004098017586003d03e0005803d111107034401034000e82c4c400300b001069074103251420108030b01c2080030300000c1038800401400b410a032800c0d002140200c0444814545030b2810101c024080c04d036a11441c1e207400340e240d2000c13030203052130300074800f5512940d159400054410042c0070f0b04000c248209840f540111942200e0601c08802c2402a19002d9041c1c1c0829041502d204803020180030f0f04541c16a240502c1c224031200d081100381c800d900c442001021540b03009844030b00306000074009030b034032514024411740c00c3e00300205003510340700c030980f8841c0b2103540301c91040e0100d40f59000301030303400700100310008801e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 221974946 1250 221973696 221973701
    0x2100305040201091806170d0908060402030d030203090f01110d180f0f030216180b03160b0d060803190e090903070b070e041404051002130e040f0f050d30 68
    0x1d800c100b1740002e0a80d9890040c41a68244450003074526000032416410003907024020340082d21245010300002e0819070b00084d95103500441c8032041c541c01000154810009100c400905180c1c10003e01031a001400ea520035070340b141e07010107230280c9010000e000e50300780141804055980400341e20400c0da26516480a120143c480460840c8600b004800807104100d074840e004004408040e60a04610303080002540c0000c81510b009034400c0008584030481c140a0100f201c95002c030380e556916032810b024010f0602908103c03001c0c40005407000d44a840c000b56131030b244040b035540e20f03500e4002c14104904110252010301c1154418049440840e415001c255002491803c00c1a4800000c8000c82c0684001c1100050a203142c48200720910409209501031401d03104011407401c4024000032103255844c0c0280c0d020540031200041c00c01107281020864260400005940e4046500c1c0140e40d80201100200004100451402c02c40e001a0498041c021042901380e0900f408005071000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 221976196 1250 221974946 221974979
    0x20a090c0806120c03160503120f07110303040519081c02030f0a0309170a08100510030b0f0d140127020103090317090f07120302060f0406270210030504020109 70
    0xb0f00d00840780c1a140c103a03401c1049004d040c00d80d010405055152a04050404a081141c0c40000b401008044600d51030a130071140003943c003c0c00b14884040300c8010920714061074000d01e8100c0c070403491480082e0000740e603075001c40320707038500300c60b01c42d2034101c020704142d26098001c4000d64018000940410441e0006e481225198a40016006000c0d106c2100d4070401c05a4051614030008103104900c2d0b000100561001e404940014071526000c0400c0340b42c02007501c1102096542d400003000d969600070882000320300101090301d584001e041214000c1c060004042d0a5880c101110240c0c0580c440a00c0145034035804103420a8042d4006402134030680b08103c0c2040391a24400f000c081812800d2800381000c3c0c001000012405103882d850070000ba00514404030010000d000025070001d0915840b0412100f102e84a07251440d194000d405036140542d200e03a404400e0613110054042e12211a900855010a061a0502042d0211202501e0203030020f0001070081c4540c1071011440e00c0d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 221977446 1250 221976196 221976229
    0x1091415070518031230130602090901091401270c020c040c030203150604030c030305130b04080102030a0614030601090c02030d020d05040c0e010b0a080a091e020a090c0806 76
    0x200d83c002080024100584103019009940c00403032400d020b00c04001e1508104038030740d0042c0c00c81d000152019401703280024840300c41425581d8007103003040950b4041c0c40d1005800b41ca06c7c2002c1d610307100444045d120501c132032101c50201400001e144603c14000305009a0000b02031314150030804850070241c032215102006506c1034807a40c800540311407044124500c40c5903001a1203042c02c0c000340c0ba01d28180755010f1b204200c00d2006002161884221104072641130904655860812040020000550340629180340000c280042c14020640040d032040d003010400700600303626224422139210f101222a609a80030707100501c5090000d510281490106004036404c210341408140e007643d100b61403400d02c4940703e00500c0100050b609140c0050156011600340540c10b000c040406030180d91040000c2103450000300c2c450300316070b0748000c0f00d1f1904405440d0310390203c803203001ca895030011001c0b4011100c074640001e001200c0c0c4a02080d1610940e0750311101d8a4090411004a5aa14020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 221978696 1250 221977446 221977477
    0x150103030e01140a1101050c04060212130e0f070909020a210b0409050a06050604020306030303040b060a030b040530090112020405030601170606030c1c0609060e010914150705 77
    0x282c80d5031089000740c03500c0d902941e179041c0140204022103081d190054a110b0300c0400170322045c0f20954020441c548503001180350f80783c486540c10074140d68194241d2119142080c56000c1c00103192000420320307ca48160789503401e0080e518801c880492143d89111400110441000d001c0c800c035400c60809000e10619020800140a100007400c03139180711030889003580300031662000c0041e107002302e41e03106500311011801d5242840210762030348001072008012402100000d005550307007a00103000380d900002c545560b45854600b466070b50f42990b18039043c1e0398502d50740f11038028000004400c541d180e0940913003400d030000c1c01034840329100101ca1111725000d00020900380c600f008407d00030f14806c18000d640c41400f03581e40b402c100c2c01400140c081d402c000510062034640540081c1500c510303850303001940791141044030042c40400f600030b2031780b0b080200c134501c1100150407005900c3d0050404001d80c0340b181c0da55940d9000074121b58241c0526620020300e5241c0540003038144148101c0e0322 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 221979946 1250 221978696 221978717
    0xc0306081606030b04050708130c0e07030608060631090f030f18050604030201050c1f050115030608070905060a210b0a09020f0f0301020922050702150103030e01 71
    0x454204000000c0780340091481000400c54641c1c18040ca01d007905003500d04000a08200c0001400d000c030040040300451801d0f00c040040020020303400c00148111083c07070610313080024000f000340115120340f038054810400495803034540f49600385000d813010441c0341582045040038102d11a403a200221510307031b907081c1342c001051844c010b820106109541e8001d1383d0200000140801943d10620744008075642010b001d1030702d80c0004c44056a130242019034481e100401402d1418040c848140d80c0208490011032820426801507070594440408401000006400441c112051072180e000540c1c00100f0400c8005d825501071500490050011480141c9908061030150300940b500e51601504040c8282402740c510308854000003c4d55044c03100030081e4001885071001805032a20071161030704040b440c1d540950480b104e110002d4111071201c5100c2981801001000b5007041581e82807400091001d4804110381c0d0641e030518800003441d07421602c3c1201c5608100c20142d0501c040c0fa40c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 221981196 1250 221979946 221979959
    0x1202010e0c041a09181204080309152206090b2104030203040308120f070c02060d05070e1003020c0c01090501021b0102031218151b07020303070c230a03150c0306 71
    0x4217200b04945400c401204240d802801e10b4214402c03000c1b40b00d142c0a100030b001c3d400d4007104980c01000129515564041d90001304040340c03284082d0300768001e405100c4d41c40c202001c1d1002800319080c688038a51502c0d030b24004024540b007400380d6111412502980c6402403c55500744a8016000b84122400c240d202da41e6200c065001141e50641440c0d20000c0010b606203c01500368400950700c0c00542100c07a5070b0109200c0d0040c000410246600c81002032100340c800c0000c030f0714144005000082c0d80c1c90f40c09010300254000c410102c618000c0c015a0501540110051822603c1c180c4c028101e240889444101c3c02242d44c04541c1140400c000d0320221501030070000c0d000b007070100c1da0852a1020152080c0ca01407035404103080c0350b0f100b00b04210107a0381b1500d94400407510f0901082da0f8898901c0061306622036240c0040044610000100c0c0e6202a9440760511380c3c4900e0745d21a080d51140300b0880c0868842c800108100000d01c4140000c0700c054000500d2800c1c1c0e1709000c10001e4951a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 221982446 1250 221981196 221981209
    0x100b13150909060f030c06110c03100b0301050609090304030b04060207021305160906090618030f08070209090c0625060905030a091d0622050f041202010e0c041a 71
    0x40c0500155815006200b0310100c1d11401c00180480404c010381c03030b031a40e914042c9003051031080070244a4280c0c90f2054928081c01380c80d110a400030b058600c11400144144020001680b48078029842c0000040711800c041c1686070081c2d903480c000350f0500c1d01d10398449681400c0140102e913103680901000e0016115003885460182100c14081100e00d4510321083c00461040c21100c01c025140c042005125003140c2c803403040c4c0e00b15281c84640150040300305248000250300040001d20208405018865408090800d503032080350440c0f80da4950002c66503403003009038243d9a01038001c020341544d038001c00990610a00011898054011090719400d0442d80344070815203540d080055441c940950001e00000600b5980d074100407040c1710440e030385c40181c40061015000300406416401c0d415514540304103c40e40d503480602482c541841c40c4444400c054034200c0b01c203a54065900011401800750b11440c40c803110003450421a071070100009008031145006414441604080d805d07255076 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 221983696 1250 221982446 221982479
    0x905031308030a081f090b030c0303040803041e0e010605030712090302100c05040e010b03060301061703090a0603020a052a0322050f01020a0611040506041206050a0203100b13 77
    0x14030140d511480001c03806450302d98000c000340881180f4140c1203141c10441186081503840c21280003071f4507010080843c2c5052003c1605d03603854407000c500051800300000090085e42e62405039542160641a150500c1420600810710201c05110040c811144920082c40d070203000c600e8452500007860b4405000c0301c410031b20580042c1c00007070380340b4206d0f4524010701041000da40f610034030b401e14101401ca840b403c103001d8808902c0c000030204005950942141000c1c15800b401c8428a100c0c0e1880a50790b940801c2c0f00c107024031150321000a440d802442a180702c49016150b4900c1c100c501003c0e2035001703905070000b82d0b000e0001448006045000c2020b400c586540307400f15094440440c2c561800300d2095403050b03200386081d01421003543da0208100701055484280840c210a1000e550820313402950004c5030400e030003280000b6816140b40d60007814901a200400154446404240c05c0e8441100c202c41d400481c50700811901d00310b0f038018000200c264020702645502c5108403400344004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 221984946 1250 221983696 221983709
    0x11403010207080c0d090515040302150f0a0f110604110108060d05011a0109050411190201060302100807110d05041502010603060603030503060306070504080a0201031a03064609050313 81
    0xc00c03880d0720701d00e402c0781b00171300a41822101c401d568030399010b40301450320403400b00238000d405144e04540648007003415180c400b03503001ca14644424050320002c010002c41d1402e480060000300c0e1040d6140c0340414018080d94014823505180021200155441c59010b4006600300035415104404a2000c1c491401c4018a54132307032045420b0420001032003684560003ea11603407808503c8071104500404840b03d07004040c0c4908480280b9100990040c80e680d84081d410901c42d00d501204c40d54044440c034071642c1075854103001450301d54030f02640d9922180b2140c0108a04110510144140803a40c040c401061703c00400c0060301e954650041d900300303900441c049400402408403d1a007400040c0d1311010030b00e406810245451165a07440e05401e10280c180343d510b0401d00340c404071125000c800484e026044031004d00340070405403440346450703280c441c200821f0b281207034049a560400e00200301031704916402452028807480001c01c070030041154144010410381901c28002066030b0b004004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 221986196 1250 221984946 221984953
    0x20f0405010e1b27011101020c01020301051f020d05030a110408031b1b091302040c020d030e070513020a02010204080a030c021f17041518020406060206040803011403010207080c 78
    0x4001005403850f000000307800403281c070140040c14644901c088206601c1c03086028291580d101361005031686403030061900e8542d400091640796009054004604942091f00c280c4070814414280140c210500c0180c8401a0040302010a00903c59030107142c00941000340083e0040139050490903079885944840b0054002248074440844949501c820481c003403805460000441e583c20b862046410006601c100d002402180410044841280b0f000c0e501070070070004402c0001c0065524442d10394030600003400c2c989150f560382c90102e0081d0840710301806030992407801d444124065000787d0550403c666080c0310004a20404208115546002e40c6640b0487ea120340180441301c1e0b108029134680e407116041030007285a000c1006103140110038001c0d10700c0d484914094003040b40303004038540b800741000005841d40c0220540c41c07009a108880c01c1000a0b660307442a601e840c011100070300345420900c01001029403600402145040c0100014604602603132100141d07040003000b40c40650 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 221987446 1250 221986196 221986201
    0x60c050903160f052707030920040501090204050d0b19110304060501080712060216061a031902010807080405073f020a060e01020a080301271116020f0405010e 70
    0x35100c5220000d010b096031002c8203000400c003100385d180d1a010402205051250020741220700c0ba501030821540c0c4241021091a08603810040c4040210007039032107945010000202c0030868400c4504a41d00600140c0e01c042140d120421142c00080034601100011030210748440361911464040682e41c0d0341ca42c0d01c0e814a4144041102c82c160051500c0b98400c40b0103100200d13a4103031040c0e4203036111b400981c0d02c004120124480702141603009021905001d501c001a44d00203500104812095040712500c44454030102101c080c800c401038081884000800c0003d442501070561203400380d406c03600d041c0d90360fa40381e80b450380d86004070080c251407402c00c0c83c074060250007071001c0306004c40307542c00380301100344d0006010100c86114000c14000750b1024062541d001303006d102c4603075030000b04c000c0d01ca44c2e44855003001c600910302e2008181500b0a0001d00211080c4500704403c00d030300d0309107410101c40b1100d03403c10b40910320040e6401620324440010b82d55440c00b0740e6010340107800c035141850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 221988696 1250 221987446 221987459
    0x408010504142a12060702060a0b010905240f0d0207150e070509090f060a09050d0504060512100b0a02070801270b0c04050a0603060f0b04050d060c05090316 69
    0x80d110021442c080d03421150307250b2002c0301c0031a1140c90100301031090b00e00000c121800103489107441d00c000e200380e001d81000c1000c0550080b6180d40708a0000700c0502005400c5001150310348010301a45501601c403000c600d0402d80c0340c80c0b2503022200c18410350792800d240e000341c45003550411010104c45580001e040c10810a02290b0100d905482890600100ca044040c903a121003481c0580d60140c0300304d900103a80920100042c003164098001554580d040a5a401d005000c0d40c2c032042da400d1042e1a4040d0781c2e10301c41d408442c100d070080e64985040030f0701100d10002c0890040e00ca1040000e20780400324054000000a010b00100360b0002c0c5002450081483c0c2035031095120000c02200c00c4c85200d0050f00e00d91007411a8551103090000c071039440884200700d07800b49400c49a002200d0f80380129403070f50981d01c660181d0395421003034600c1556440c5d59900b28400d601429403c0014103202c0b50000b64203810002c2103000034180380e81000c1140f004a842d29035124880b004040c44c5c408108001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 221989946 1250 221988696 221988713
    0xa142203080423030309040e012903060c0405150703021f050604050f0601211d0607080a020702060d0504020d060e0d0e150909041704030312050709080d0507030c02060408010504 78
    0x503e07444104555860241d100000d4a1740a554074103405941c44900e0740d0729a400030341c80301046000304030141c05410380c1d000d918625500d00700c0002c1c1c000d21032034011465405001d0203490844400a0544400201c10343c4d080700680c101903800c40541c400c003405000001058054000d01c060a079100240310b01d800e1040100f5694040c0c00d0340710b101c218009004150b40d02a6a03401130039490b500e00c90701c0701c4600c03e8840040926409040c48104600c017107a01043c408036415000e034550303603100291500c07010011b1040303215540340254080d4007046504403180c070541040b68880e000030000b2034a0040782d201c0c1c00a490312012071000340e0700454607201e1065000b00030005e4081041d01c00c08407501d1800d03900b144500c0f9604c0c5103885044800300060800c42d00160b45682e45100c8490181c80b20f03a00c2c54003500c601c1d8028080c0b0411390a1400065842c1e10803138901044403045001480d401118640985c0c16078021030f015010444100e1041000da11003000510050024400018003440c20b4104400f4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 221991196 1250 221989946 221989979
    0xf0d0f09050706050c1005090312071107090905011d070807090203040b0f0408071712010605031006030c09030f050a0302060c0403081e09040c020105060a0b0a1422030804 75
    0x26414a4000c1210104200050040a90311141811395695150190f100e1404013140c100300e00e4641004200039010901102410010321034402460f81500c5507038054481c200e20341c22a200d41c0e401614100f03e00210360b0071400010740075200004652040751004100c660250f5008806540208401c0011042c1000004000c00221104505604081d03840c544051000b8107022003081700c150104050054420458007083d40c0040c0c22007254038103080207006034100000710000c1c0d1441c08000200300c3e000e00b04407441a0800322a0b20f03841e07030078a41d0540040885582c9035042285850011001410368080240403500842c0181812115860024130700300009044406c3e130201880b08200098841040c1d80403000c0e14003441d01400c4d003d0300020070074080e0707014880d030042c281032801a01c90340641c8490300440081d20020304081c0c540410780480d1040920400000303000052241e007032562440a400c0c0342c07466108203801e800380b60268601061094000303035540c40c0d00250030080702d04404a0442e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 221992446 1250 221991196 221991221
    0xc090302040e0a03020f070605030a0c170a0624020616110d02010218030106050a060f02010b0409140606091302010809031219061a0a0806221a06030906010303050c0708030f0d 77
    0x521f141407100041041c00058105001c15888600c048502401088030011010381e44140d08401d10302165540301501c5d191240c00011503001c1d403e903081c0d03915055803140402c0146c00030503ca0300c1c0d200302c0351309501100808404100d40040d03800d040090501a008402d02b41d6400540ca03000d030002961005032200341d545100713038501a001c02254503030b444160215085800c0141c0184034001080c1c2c05004402580755103e80381c623461808000020008280e01001002203038000d548000c140071100c10305071110300d92a051000c041c00190b125922141e8042d8110382560304100e820302c1009105041a00d0000040307645510281032444188903e078010320030a520b45071040e00b1256601e9540c03150f143c440c800c2110900004580c1d4540340241c102c030420000d895086010448190f00060190024540441101c103180d0909890428140c80c0620b4200c005800d0302e03481d56805894a038005480c505c494001d1400c0020103520a0010b000a920b010808980d20b422403d2181c00301c98148000784d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 221993696 1250 221992446 221992453
    0x4090b040605040b0306010b0d0f1b0e030a021509010e090a0b1801030f030e0607020a03080c010c0801150804210816030203040b1609050303041503060f0b0d0c090302040e0a03020f 79
    0x44c6003030340c00041442c111011565695540c1142a01c90005440502c00302c4941906049060b95800d2840c0640c02111145607280e0b42e417110300e8410107443c0e905112001c2d40c002001c0d6007140d0310805e00401060301c0e41050419000f2840541c0205800c8402198188250307550b50440103c24100100c51180000e415034041045605580d00d40c0246180501c010342000b00180005240e42c136120125090a03070010031a20085a076450200c0941e480309082144950a003170052948a0080b880b0718182c44004a035281d414503800c00441c0d0740f5000800980e044000000740b510500c090709500220003035035548080840c6046581105011100c0645004062040003000301150140309a00e82150480c51140a12105101c0884a07000c4641203590b00d0f0000150003c2c550018407180c0c8000c201c03a40302400060340c0e81061101c81d031301c1c1c0e00c22036038910b004000d000002c0768143d000144c40c083e941417000000307480b07401150448000315407240090f031000c00c6183c2895010801c00220b408100d004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 221994946 1250 221993696 221993711
    0x11060117070b03040f0f020f0d06060f090903020a0602130e0c0304020108070e09070c020105090a060314090c0a031704091802030c06250f050118031101020306010504030b0405100204090b04060504 86
    0x10004864403c59000d4408580c40c0d4031b8004554545d94204000e04000f011407800c82032605106008154920a44801c0303c0505000207003c4e420b0b0040c03101940e050380207410403203441c3d1201ca010754422861134032100101100854506082c000d0700340030b04665500151a86003620015264010150854007407001580340380c60140c1e0780d01d0103654444603901c2c0c5000c2658941c8010384141c012805140d62060014001050352645036022500d0150781c071034000941d448281010b40c9919005040a4100340c51010a01c0401e92510503040300380c03a0745401901e815524200307901201c0b040b4070144170000780c85800350158038041044403580a001c882c01450b04200740c200c83e13660800854620707041212403042009022044210203105078021000707012500241d2101c1a200d6001581100481c20880f94039800721414400d41e403041c1c10684034103141c1811600e0304c0c072a1250007081228241300d110810f04205001d40003400060880c1440070611071681d504010544d0510340216008520b0f0801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 221996196 1250 221994946 221994953
    0x1b010203010e0606071106030c07020f0a060c200a0f181b03090201030923240118020903010e061504050c040303050a021905030702090a0b0904030f11060117070b0304 73
    0x240b0750049400c03600c8960b150032030302d03240c003040500307100c1c0c40d40c040130100c2001000950080240003d0b8400c94030b01407042ca074041080300d00000b900400c40010150310407000040e08030070b00c456040c11000a21a680040c0d140001c1c07258200da044000e4000030b00404028241c1342c03035007001c005000300d4030511540c0003182089080b500c0317040745402055210702da02425640030303500014003c3c2c0c0000d0400e120f1000881003042d50f21422600c180e041c45510381d595110b002d08030380000c050441c16820700f07150b441d00e910a0030f10381c1402080920f0b154204001600c07560244282001114a100941005d2500040c2c01c450b0442941d5854016420003017000045a210b0f0200c800b60780d85814215190203901c0740891170911100c851b008900e4612181000313101000000d0150203100b1201ca07107456840200181c19905e00541c0d450300b020701c02c03011800090094100c0d860104d154a00360032001c1c100c3d09145d2802000707900a0803440940c400b820030088040c04148027610703404070b220740340d03051954 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 221997446 1250 221996196 221996219
    0x603060f0103150f090e0c0303070b0609100b0a09080c22090303021312060c110a020d05010e0304060e03070b0310140301140108030a0206070e01140315151b01020301 73
    0x34205040650341c40c2d0307040824a007401c480303000e000b42100c03c1c07480da03845e0038414005080410a40030244201603c000c10303860004116010f49500c990034a405d9103c40043c401c030643c0142091a043c4078034500800c8a20540c00905041001e60780c0f440d0400b481c1180d568104000340b01c046000e41140c000030701d40314101049903400120103200004a004c42d80c2411002400f466048030048480380d4000a42803002d06883c4608a001d17903c10031402100d500c0644000d2009140c1e8001508025040c00141c0f50410130f0740d480c0b50140001042031500c0c00c00b03a50460b0300640000f804101e21242e00179060074104641c0020b00481704843d490f504007074400f900f02405621803804400c9881c842a280ba40b02900024001c0c030201070012000c0d40c44080d0640c40350082c11580e4010311400f000211000d10580100d504404181c552044091803800042526440145828407402c0c1d0f400703020300d13192107080010040825014a0985407030b40070ba4031800704c10940c07031f0b52030840e801030005100742c55101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 221998696 1250 221997446 221997469
    0x60609130209014a030304060914041b201903180f050d051501120b090d0806130212070906320901020a0611030a060906080303060607020d0c0303030218060306 70
    0x200380030300807000c0c6910031814501c501a001174140c0030101d000584140c20802c5481036030420030982d4038601c2c0800a0008861081d003100b51038005c20070402011600505240489401944c000c000d0901c0540c0c0c494a49810818035207003020103100c06a080c194401780080c1080358551208510a25049020040841500a052003880241100c00c1040360030030040c0800030200104911541e075a010700e40380000c4210042d10310a0782c10380064264140800c6281c0040d0141e20780c001562179000510000390502807403848850360800121204502c03a8010364410030f22940c5500d03860f41030190050440c6803a0720a49158884140030f4020800b01c0f60f1450f041846241481c0e03190071540e00100d00e000325001002d004546010502520680c01c40021481940d00c984d09004056a415104044803100c4c810402560428004100e0f03524012009080c00d40c0002c08004ca6485183c94001c4400d51070751080340400e5000500350790149401e100e00c00e00102c225080d90841c07401e4400304245a941 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 221999946 1250 221998696 221998787
    0x14090c0d051b0d0c0801060510020a0c23120d020d09060806060306010309140105040210140912120a0201230c030613021e07051203010f0b0306060913020901 69
    0x1078640d450a5202c40c3c2e120000300390803281c80e80e07801d039031a0246402842c0e14020b1602901d208400800d42c280001085103009a10800d2882d41c43e10300400001d506400c411903030210340a50b8500c8a241c1e44542da01903103c00c110b400741c46084c040e5000031b881c0c810404191014072001c0f0300200180c81d00004400d50243c0107650b500e980f075a8020040b4000c2107002e00c002d06000000280001e401815400207116038030035140422991103c0c0e1003600c405a0007032001e9640c4104001304469420210398044041e07804d60100d40461000d0b40c6400d4042d0000952000144e5480000c0040e460064010b89125000d519030b490707607400d025031802001c6c80000c0c8560b014402002103c0000c2d82c40ea41210301503d0b003003413010540b0000f0744800803141c0c02140191035500c50785a180c42403081c8101100d0403100c00000c0070502519042d81130b20b298000414481c1d1000e410310201b00c150300c5100040c070420f041d0600c0182d0f0340d042c2c0c90014080e10b240045440318984100341000c900070911a03404041100d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 222001196 1250 221999946 221999983
    0x50d08070b15090a0b01020d050f090411160302060f13150e07030506010b0703080108120304030c03020f011104030203010c031a0607060b0d080c060c0c070e0703090614090c0d05 78
    0xc2d08a14001025950555240c00454036000c006440300140c1c01224569000d030300344c46a94030003000c104c4550140c20704004200310300f002541c001e0715050b8010300e20480c03240e001c5818a0504c011528485651040650150708000e04000c00c00d1444480131740d000d0031107450f4624a0182d611800030760402c83d5a06000280e0b07501920b818007004200c410004c69008089608a40e110141c4490f20b802520044020407680d80000c1407000c00401d50290010b107a030012401e60f80d407902c0c222503860f9030395010b500b90b0041001040c25402c0030301503508a08401c18110340c0d0359265106050855018440312420035151a43c001d01c910001c2d1509805007408458032501d03403c040c14030800400c0006105603000280c00048020008d0300c0e00940b85610680c0300352003031903036440b0340323000325201b64545501c207070300550014400c3c202c0d0528855008140c0b0300d0002141d000c80ea50f0203080310405641e52139402140c0c0208664110100100d00030b08800307540f40b00b0310320200d0303507165958501c01c80704540026 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 222002446 1250 222001196 222001201
    0x70e01030602032205010c030e06090604030c08040f060306050111060609010920030412020d0801030f12090b07140d180e15030a030c0b100302010c11030106090c090e01050d08070b 79
    0x3060a51104007108184580228903040303031030f011b40200b6116090b9800329083c05001c01c41900c2c04940c8911440c00381c000b0b818541d403655800c0392000b2900f44100d910722000e00c0b0108e80a1001114100601020340740042c1072410800054425400240e2184041e4054000c000ca1520380c1c50069044a000803800300300034000341c0b00c40042861020041640e250040100001c0c841040d00c4166243c11917002e45078014040f120480f695a42408050700810001c012000040c4001000000048440c504000d42a46a002c20741b42035020003400d0f80c04d4000da00d0509450032040c003140b01030200a003400164260b50550844c6140f041c0d1140005480302032001a411142000c4492025a401000e4035000314082c58043c22418508005231940080680041e85d25010031300f00100782c1350140c541c3c8288100381ea8955814004801450b40c0554884500040f450054050900c7c1d0a403988c0b120800340e410000703204407416050f80401d00c0360081c01e45400c08908007404440744982c01074a0885183d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 222003696 1250 222002446 222002461
    0x1051309030e09102714010605030c0904180b0a0c0e01020706111005100f12080d091a1003060f0501270908040e07021c02100c020f03030f0f09070e0103060203 70
    0x801e002d40c030004481030a20940182101400b9245408081217002088008582c005c11594460240601404144104082071010305001e01a002c0d82d203004002040c0c02c2055000d1159104001000700c85411080c4d003800301c3c50b0140e006041d2041c00c3c0746071508a4940d03650000756201101e00c1602c05108c4101c0701c44501410910030700340d440340311420521407410541e40042c480165845000c4528042c603d0102d0030b01444480d008a541e0030042041c18241d050b00e15400811403820100c900d1301e107414130a60300020641d14148100d03241080b1004e00c45c41c6062003c02c6e905c00c00c0c00124160300d414018012000000300b0045514402c28030b040901441c115a03500505403c0005010100d0104000800c0c4110700c0d4142e1040090307500b1365000307400890051201091035011300f000740c0c02028600c0398200c0039510842281803944100c43d1048520109542554400d8406880041c4254108140140003032005034101401d20002c00c0034a2404a04407130b81441804000d058680010108114 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 222004946 1250 222003696 222003721
    0x4030e0d06091703040213020c0304030605180a060e010c03090c12051203241c080310090f05061f020a030f050705030a02010b0922080904090c08010501051309030e09 73
    0x419501c07504030700c5604268010314100fa04100e504034032841641d05868000c1f0191b00039030380c0b200100d070015820035055903034040103064003d04011680b69508900c3e4150340081000350f1040340241e0340021042d800084c03c40c01d403006515080245410311200b0b4002800078011907045500183c00501c131444a49002400c0c00089001780141719804400e1100e80002e80d440344141041c02d01c4003541c0b064500050100e0845211000d90b201c4001150030008100e00d400250b034800c211507c0b8508080c1c64201e44000c0f04d0014241e05c07101680c0d04200030445c1080700301c0203e1000314200b00007003000d9182000f55100d0300c900008042111011034030039a1402401980c00b42d640c803070203494881c00071000c001d000303007180d0f14039610030300c812000316048215043d10046d204022603041020b2000e0368441051542c080c842c901d0304140c2c0d60b84008081203284080c0b4000e084481c0000c146545010100039440107a40c00541e4a549840545400241c20401e5001003080c15507008070a41d5916083c01003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 222006196 1250 222004946 222004961
    0x140105151603080108060f090a030e040b03013809040f051f090c0b09060d270b090105090328020c04020406030204170316022b030504031103010504030e0d06 69
    0xc1c1040e98030340003420103400140040c16110014100d403000c1e552103800d4910043c0c162059031803500a0040320021030310680300d51140c03d1018101244070a55400400d00f15a04e005092803401400e00490721500d00b001003c075500d00043c0c5200844540f03420008600480141c0000c116621551a20040007018005e0002400812409002e0105400c1400015003c014402c0352400c02c5810702154140d020003d030743c030b07080024080fa4104414264103200400c0000024001902c820003429201140c0e50344101580d48180205c12803400c2c6051807070b00313642018050103113070740060140c0541181034040c03003c41010410042d45186882c02c4059083c20701482c1c0003500a400003c0100312203815400800489054022103400d0102d0310071240d0322409841c0e201e0501384445403050001d46440f591007800024002504400a10701c1e074586202400c10890880100b8004501007043c02004814888464410f40085c0050b15140d45c006200507640f040080c854440e007004a024090a07512030603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 222007446 1250 222006196 222006217
    0x30d0507050f01020403060507030f060f050d030306050907030c02061308070b06060c0d0216060503010e16180e16051606020a0203090301020d270308010b1602031f050105030114010515 81
    0x645c0e13a42c03a401d144018080888462004c80d0400d00c100981c0e000a05c541d00440d1544610303800110705004c02c100f00807450b540c050302015100c4c5000709041d03a41c400c0890040d8516100054001c0000300d001c0d0030a41c2c02000040044814407074040800c0c01d14080b00c041c268401900e500391b507070303160018204c0e005040f03880c5124481d044040705260740005411500c551450405601240e8074041102d251000b4099400c0000d00c1031b001c201c043c0c0320307031000e100e0105050504401080d031400a0380048055640804030045291043c8440d00344441050f020502452500c00d00c1d04410702040d507403800040ca40145450760004492014174801d2040e2503607100300800a40d500e00c262182140a0301407030144088000c0c100310f900d0039100500c20501c903035590644414605a103003000a8429030042c02404000401c0d441900300160342c01e102c40410034041c4000f130950004031f4104c8d0022200e0503004180a60b00d056289001c0492031350010381110801c6030161160140d80c002c00c00140200f40525 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 222008696 1250 222007446 222007451
    0xe10030807062301031704180b010c150c0806010c08220504090f020301050c0c0607180b0c030c0d03060f0509060604030602130e0a06030309050603070207080f012009030d0507050f01 80
    0x4a0501c20f04500d41c0c1268010003414080c450740801d440c41c07038426485107440212081085e00c4942c02590040140e00e0014100340b40c0b03078140c98846000c29a84407003034102c45981e80c442124565001841ca41c3c00c52028a000032911b60305a5440c0824412212007040b00c001100c0c4424800c142915030001620020304240036280c10b03440c02c0d503011980d089040b4030079403c0400141004400c0c10980c3c0c01d401020b4001d22541c0c6038608141d810942c080d0f48130705410f010100108215104200410703140240c0e40007560340e040e8100d4981e09108101d19940c08049c18000c040002c0085089180241cde4000c6604600a44440c2c0000d841071140384d00091200d8004541003041c40c041d0240d0f20100c0c0e85001554200d40e54558030381e001c41300280002004034108040522090424002550303000d55580102c549254a45070a00d1809802c40b14207c100c0e910b907214001038100085401907030034000a0303802d05080b00380b00080d03200c8043c0c0010340d0030420041540803e12408200a40103044000001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 222009946 1250 222008696 222008741
    0x5040f0f260d0501081203160302040b0f0315030a022209060e03070b0f0c0a030b03010902090117070e090318150a030c030513020102070e0c0c01060f0306060e1003080706 75
    0x1411101d4100b01d6030940150700c1c20000103080100411031ba440b4100b40c00b0800d2555450400801b40914414040401c140c0e080c440400c5a241180c01401c00300d40c5004600e0b103d141c0003010142c101035611100d40240c0040c1005c00058890f0101c07400c03031105401c8404e9400007144040c00c000c2010b4080079041a0404030b1203009100044024001240140140700050750f5084107014803000a407400c00200e50100078100300700c0c0c8603901030344600a0080c00440c5441c125000500d10300001e1f042201ea4010308001902084000c01c00701c40200034011108441d0f00d482d08211b41c80340948041d21020b44407600700000c03995154510518407a010801c0592224200d0000400416421041c1d4011918002c0480d004001004454140d036a05030700411105050802c0154031080140804030b10314800d100021881c030080c060403019082d03030305180850a2840c00c007581911020b502ca404c00d00844000e108201c8031400d5000d056030342100c180c3d9a52042d501e441d5004200802404590010a624 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 222011196 1250 222009946 222010013
    0x309011e05010801140114060f0f1c0c03090201050301050915030f0c03061012020f0609040903050c1005070215041b08030a090b0301051c050f0102040803120a05040f0f 74
    0x1c9060b590884000c2000040c45064660880c0d0280100072504503098000c550070700d004802440340354041d03105182454403090143c0c010341c011603c200c440c04440d000000e0360001500ca5a4901c0d82c00745000d01c00d0700745030b40010340a80700601a40e0b0051100c2d600082445407101c0414032080400340403160000020814951035514070290203109000b20004035104040c0c50400005465640c0350000500309668208000541030003955900301c0030a0007106a960380303601c244c1c5072a90007070b100c2690315404001850b04040d41700d0700c0003400300c0c6000b05012003180d00003144400d41d907090388890940c0c0c07100d00b045001d030722070310410310002c2500c000082104c00c004000380038040c10585074181410740b160450300305800b09005041d08210110003100c000110340344404601406102503a0b4189d11190055003664802d1b08521200da000103102e400650130714007400d50140d15005c2c10001400e00b59540450784200c183c000d002c8241c81c0c80030105110711110707040d44514158080a4003020651f1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 222012446 1250 222011196 222011201
    0x601080c01020606010f030506010c02130b0a0b040b030c031302030706090513110904021602311107020f0301180311011104050906060a0504120c15021f020309011e 72
    0x901086401082011000c65000282e994010705058507098112a80100304030000d040c000e0110b810040d403210aa00561109842e10000c041c65084c082102c581020500c0009002a4443c5580640400080180a9900b002e0b2a0007051a60310585d50352034000c0e170007260381d0b58224080d505000d40d6000140042d00494880103c134003c1d10304d15080c1007400401400c4a5005e0340e043c13800c0e80304200b50581458503500410030155485540609501240c001c1440c90b41c600c1107043c2240d08007001003c10407400c002003010084800014001108940e041180c94098004000d014900c044a16880c1c2d94080d0060001694500c01048071403286007802844001c90b06520800b9518040d90f90036008000b400300c806945020f42002c107143c4401c424040e940d40312400c850204070043c00085034410401c441d00706128000c0701c483c80a14149032518824030a440f00e41c6040d035116800d50070800504012400d0301104900740107840e60380d060b001e02c4c0074100416940500000c102400d100036051039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 222013696 1250 222012446 222012449
    0x10c080c07080a120228110715090f090f06050613060c02040b040504110913020a14030115081b04020c0a0b0a111c0b03010c0804080307140d0b0f0a0506120c04170601 73
    0x1d4042c059964071002a0790132100c87c00381c1021604055000e010348007001600c0044c43c3c080e413505504165840c034084030241c0f080e4016042c0d9607140e00340300035103d449005010142504581e55894101801c0280c220344c08148269000e0007401c17000c1d0782c1136503034540c1b20b00340080c4007500903c5a841d040c9440080d10a440032464461050074000c5180c0c0101144060321080d07001d84480c003070318200048201144040d0b20407950641d01c5800022180803e5280c2c14010700325038000304400f04003a440030351401c061241d6980503070b205000c8030011910018031910b1a5030488002044c58449080d0b44000d4040c8802d052101c800029081c2d9a21150000848242a14a004000051440081600381d0b028031703590100050400b0003087c0030504c0d03071000b55000807280c2410401d0280e031500d200500d4004429070910720390f40d080d000d481c0e030904001024500f04100c903148126070401c40007400b28003440c51048a099001c00006251000000c00c8501420641e42c5040c1011030300d028559681809 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 222014946 1250 222013696 222013747
    0x1f09020705061603060503122505160608070806040506030f030a05090103140112290103030503250203160309050307090608070803190c110d0503030108010c080c07080a1202 76
    0x28086003c6400c0c4284190001c3c0d5000a0107442888c660b8500405980c1209011904402c1f4885070306011007440801034103041e12a80c0a00750700e809007005032100c044250f003c0e0082c42040c034104942d0365400300f078050f07015900301c5002540d501c490b000300340b821003031403401d00c010305c400140c2001142c6c2100140c030769000309036010300020060003241040e43c01c0a00c15503412050905000000451a41c0c0314035405440843c4e098240c0521110030440030801e03403056003c90000018495060580c0043d000505a00b0303042e8143d901100d13000a42d81d2203016521424040a0001c240c1050311840c4640c0007032600800311070485888030506002040f85118603000d80c45425800114a0350100582c0c0408811560340703003845003401d0055621540300c0c80d0480d800d0071500c0500c661079441d074005400c0d02b4001c00c019034480d03040c030760342d04c1c00c40d10f0000c0c118050000c0d00c020064030004035400c44600b150700011840d1254480d000943d19440302c0103108a210b030022591111542c050120201034060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 222016196 1250 222014946 222014971
    0x9150106080a0e031905071a0406092f1201090b010f0924050411160605070323060415080a050109020102010c080f15130e01060e16081f0902070506 65
    0x12071440c0139502d104002142c06005901040745a503d0700407009820a64000d44803003404929600c80189400d1040740c044070620382d900541c0c428011804a000c0b80880d0348190010070f540032070796420042c0c440b115900d00c6070b8103405c8400481c00d401e4102c0c9105651060f6100000d517103428034901120000e000d084105460301032040419505c8442d00d9110411104003000441c0c2443c0910010703104031120041e01c030344100880c40701051351000400010b806403000095a0a10900c005d0554944504008046d00007881102c910011041000d4110800f202c1c002050b0300314000715403071501c842d4400310860145050300404e01c070040d0095031406100360300801c0010b514100540e02c55a058800144c4c4144810001c2c40107048440390148105000f030404100040c0c0315113020655402c40f590720381694462401f0407203401d00704140c4c0c0d0002084240d50452440c2c800300180380820060007842d032281060f40e017144c030b920b100c044200503000100044d9a034486504003070365079180c26500071040f000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 222017446 1250 222016196 222016211
    0x30e370302150a020403080a0c0602040506070503070b0108010606050d020904060503010e1006061e110111030709050a0902120705030403180603020408100623041118010921030809150106080a 84
    0x10454130031641a6a0700c1016a410b14030048411580c602003400c2c21108981e0030000440c5a5640c1c0e00034110300e40c0f1a40080d40c1c1c42d0000d00e800c442a0f0410703401440c07940e0514505201d6950082c00f9100003552414005071114010740001d0043d14056000c140c26500e08010901d07420b2000c9070114030002006418450b1a81d2800b08882025907030079071880000d00e020081d00024030545192340041090400460b1b0380304407280c2c1c1e09030740e07005584610101d18988010001030034070348804801040110710460500741054100280d822000b0f00301c408102d070010011301054043c0c0c0041c034079108503c4e40440e4a41e01d4802c05402580a40a0000244500e00c0c0d5001c00d00440e002e04000c0e941140c3c0d0620188800380b1000d9400c14206607081d50241d1185100c035220000200078056602810400b02541c0508000251083d0442c0d00a080329102098a101405405003403110341c2030b50504d0702400c42e40da0000000d0400203100514039002c02541c0001560aa00014103401281c00c12810007902 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 222018696 1250 222017446 222017461
    0x2c0a060e010f020f0a11030f0d0815090609010605070f08040b090f0409030c080c100504050304050901211e06050703090618030c20060c010c02010606030e37030215 72
    0x340d400780c0404d0700e1648822055400181604001000d51802034102d03020b449545000a00300454409040000b9582100b0000041d0001d26820540841520070160030700300744010401001d0140510028810b000403070a003000100e000ca20041a00007041a4680c0d03120040d80c440c41e804a07001511541d101c6048069170314043c46010151a81904d46280f0810665601106500800362008103030184c0c1070320540c843e00318011641706521810146039650f0600b4108019500b060b0410784007001e041e96480b20007801c2280c5008026000f61086040a0641030780d0940c1b1070040400820711410002400040764140e00a40c100d2485010244040c42c040807100100c45610380018001801c0050740102240340d092aa042c40f040304200521102031101c0401d0a59210340703414007481c6e640f6100300d8038995080c86801c0280c5810301d0f050218682d11541940e5801046048011001c1080e181400d80b07030108243c00c1660020030550100d0207028100030b034031509020f1480000360719440004496 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 222019946 1250 222018696 222018703
    0x513030b061806060702010f02030d2c030306100e0301020d0612110f130b151606200d0507210608070e070203040e0711122502012c0a060e010f02 64
    0x9210050004c9007041000d400448010103010054002d501042007003286581050040d01d200f0f501e80f0b8110340e04003c82e00780c089144095040000e00c2d941060042c8410755071000c111110420b01890101342c0c2c000c0c40c1c400a0300a01c21665050307045460304400165100790b82031152381c014000d844880d800f8005d4014014404003501510758070506402511403074110590003105082c03800b2306949907034400050060741541c0107500708144001c0148118003045154050115100005190303540354442a4034000b5150045142c0041450345850000310802c5c890307170400c080d108140e00000100c01c12803401d000103080c180241a0103004580c00800d009a0915215000d11a10350045203441c0c0381111410308100d004d1710240c00c0002581010300e0800040050300c0183c08007030f428694070383c002c18030305400150f5003090070300c4038204041e040003503a042001101c02d2024a411515080088031241da103040e105854540c0c040007807000403070754542c405116080d007030081e00d4400341001c40c034000341c6c0d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 222021196 1250 222019946 222019951
    0x5190504020102100e0109050d0203190306030302060403030e010b0301050c0417010204050a03080c030f03360d030b12120c010506120c0d15090303090b060105040e1302010513030b0618 81
    0x96804080301310803006450740b0494192080b0000040d90b40f035a40e868030305080032000550b005a20100e8608085020101740102018003820108101c07403031980d0194458000810141c00d26644900410030100290800200210000d008010340e1400980c91521600603010f485802e1081c00c80b0700010160500c200c0d000e940c0010a0904050310310754a41c2c0060f8000340e8000c042e40424490f0704000304074000558051002084c845000c0b40420403040004c40d18203031948070340b4800040c6c0301000d40d4081035010b60050240b40c0401e000740c8540c00f180c0c4200c0175040c031041b503115401d50243c0ba5000040500610010b1030000d0103e92a000e04101a20031910700180c0c1c0c0e44c005523103100c9507103000c0070100d080911a60300c1b02490003016045004071400220300f5000309454800c0c4d0340401408118482d40007809080503030416081001d1680f00c160000c0841039003000b292181c409581c0140152307001d01d00000142a009605c901e8010781c03008080d00c48a0051000390404061050003254030361 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 222022446 1250 222021196 222021199
    0x70825020a08090303040b0706020408100204180b0103060b160b160207090207020103090b040b040204060e0c0a202e02090f010c0201110708030c0c030c01080105060715050a0519050402 81
    0x820141c094545040c1d560005484130f606100400001504100c2c40703000d800e01038000c00d070041c1c565203800034690030942d03046810200c4a104100c140300b040c5843d840701c001d165000388005144084100168000e001da60803607200c0c81d4001c20708241310103420a900000c944107103c20380d040d07103955000416081e102a640c1d03001d80c0203024240308980040d40504502401450045400500d41e103494108840030382c0e090700c41000c000204815801d007406107000402200d481c440d9146010345440c2c1c0702d800307440c0103c0100700410940c5607400d01146c1c0c1e03500d074500710242aa07004421346200c610b59142d141e030f512101d44081c2420321010b02c005100380c03103040c9000340c000540010344400448070f120b8080d1007241440365002e800600c240d000c100c5030000e480c0e0b1500844d0b540c0c040207100c0f0b26191010a103180b19502c03c2d0100304c3d469901c043d600c1d04440054403c6500c03800d807460218000b81c00000d4060300507261104002e064040c64016502035000781442c86404030000e41c0740026150203c8019 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 222023696 1250 222022446 222022453
    0x10e0c0901030308092503030305070e06190909020d0501030201170702030a08062106090106120c0b070314070b010e0c03150f0a120b0a11072607050607082502 70
    0x10030220b402405130b41da11a0110007600c8030782c05c417400e13441c2669100d400c801c0f500100c52076091007055094440c082e00701c112030401e0100108114002040d500c5180d1142941031300b404c0d2802c1d0001d0207040700c1006810040c1003952034096510806008140920040c0d002a00d071120508207240189038a50190f85154041c1d407034601c7e1201c003910418006400c90303400c8208240c03070500121806060352005036100300039004504005098600303486050b0422501c010107214a0b100180e04650081c0460b1282d0b004c05889000301d04040c1c40c50840c07003200c210500302c0010043c0400203088400c6059500c1c07003c1d408880c3c1c40d0401c2842040c0030880351440c00e01d0321001502c150386000c505088021200030036104a140e06c0e6200c01c0c00107148024220313200798006050001a01c11800380d905606048040305042c003150f40c0310300c1454a150607903403d8042c40c1600411080c0d01003001c9074140358100301101c09504040e0f200030075031a03084032040c1c06440395006021001224a0100e0801800d50780103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 222024946 1250 222023696 222023699
    0x106050901031509170a020a0c060207081f090b01030c030b010617070c11150d0e01090b13020406050a0b0d1401060c0b0901090506070c050c090c2502090901090302010e0c0901 77
    0x3c01c0080c609050203490807881820290f680704480c400600543e1000c0e4045c00c0c814115190040715818550080015500f0555090014070000144040700940002402d516400100036040080c10411405007402e8503800012051103418084141164400d2052004603a80d528040341e078800000c4100c1c03200340155005c6100a4072661140c0c0b6524011005844c400304210005510070700101d1808070041c10218801a5004240c802c088030142d805009201101282d0707119411100c00802c43c03a41503010100103025911241d100740701911010b0b0a6080668854458200c250400440c8203149030808030440c4004202e00019030484140b92600319200c3d48039617580182c0d503001040008150f50361205d01c008281308002d040d0251102d0b4440c143c0004040c1415400e107040403080e0b900694840c804e216100611400312a940c500c0100c8050b0200414060703801900400200a58003100410621020700b4065220b200d003e4400e40080024407484900302d61141c41c0da413211580301108100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 222026196 1250 222024946 222024983
    0x10302060714061303020f0a0c1806090c08040204241413090c0f06020a03050405010e1306060e0a05090402060a03020f0c0703031707110d050915030a020c010605090103 74
    0x203010498810702c005600d01018564a074600340e000c83e0a8000c80c400d1041e49024182c0611001d00004100c201038140e0b440240c81d0b881c08031301144104034960000d8500d03054001c00643c001c20141c00200818000135501080c0240114000c0d9000d070301c181e2031310041c8144d0300d051130500001c5000c0b031039080d0301d980d01c1c01c0054021802030b8550113420050301701c40e6850400c4544540444644103160050629050504440d003414154000c00c0666002d5a118004a50040243c40c1250024a8401050301b041d201280070305280c22681c0d03042c181088408940e61790480c2e0b0740480c204040d1550408907654104000511005550280d0407d40c10055600c83c0c0e440b81d0014008154100c42140c90080301104c8140361070400e60083d8001450081003880002c1d101e11101d4100460780b07003062400e02c0c2d954884c0d450300020f0240c842440300018406c0d00303d840743d660300d072140c25003021460748070303e003080028010790f0080c0c0c00e02485500c0e2a1011503149444418941a00e800031121108240280b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 222027446 1250 222026196 222026209
    0x106081003080f040302060d150602030a08040f0f020306040c0513020f0301050616050703030903060c090311090603100c03020c010b09280906050106030e280f080f210618010302 78
    0xf0420000e03000410021016841d040010302418190440018030a840700c002d581d403440c0140c0000003150010408404c246030b210401582007030300300100350000300706454040350001120700000e425010385c204100c144014407c0800c115902030707034440385003601140b80c02c01328071540000306040c4d030041c4010700541c10010042d0141c61100720b190500700340daa81300c0300e02e04641c0340c2c811800038409c03070028400c002450048178110006810802c1101d81036980b0360341e5105001180501070803082e00000c13040d07a020020300300e010000850400418404020040180d401261800415070a0024250792030601501d0540310310051581c0080216880c2c1000401150b030704180b61689031034210500218600d4484c00e8020070a98800040e0301c40c0c0140340c182002290074120500030b0704501d20302d25014800c000d03405200e034080894001c10b0140c2c03800000f9805080320b10040387c100440c4444500300751142031484501150144c00c4950340385400c1180070300b84060130100c1441e4000c010001410705d007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 222028696 1250 222027446 222027457
    0x7080108031b01060f030503180a0515070f0204020d0b010e090423030706061805160e01050c0102161109011a0a031a0925020705090f07090b03090105040605010608100308 75
    0x81c008134800d5550808003103407207402d4005a41c0c0e600b001410400c5130007a4203240030605001e0303559100c0149050005803050389402c00c404848a4000350140422000443e48a9110b500030000c64880aa640b0044010400f10400d64040350100a0541080c81c0c00c0e10100d1007a40d012180d910f01c000e107107001c440701c410352110410f058401880320b04001002801030102521a0152041075585029804422f4401c00b400794001c0d40741e410303000c0781140c1d4424483e000c900828280786a5500d44c4a2010b80240310b0541c440242c544161004400c00c980d07020400303500c1c03004840c03210890341c84140d00502c00c10020740e03101d01e03e00c0400001c984140250401005445454011030320014508041100c541d8202d1b00b4107650358102250052a440303191442c84091040e00c0107002c0e0900b807502040d104100078151f038035003811080010f54a03901c035003400400b03001c0704074803c2e41301e06010f52246d01170081598115400ca00300030010031a85e20903403041b441014403809440b5220f1440e2110205940807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 222029946 1250 222028696 222028747
    0x901060c02120318040c0f0801030305030618040602030a1104210f121107080307080306040f02071a0712090218040501020f130302040c090302090a0c0e0405041a0708010803 76
    0x518182400500b010300c0034000040a50b0301c228480a034a0b41007004640d4011201024055105601e52040e07500c40350003030542c1d41c182003081d130b02c0e00c034000056100c00f414543c4950400050040004020840c2c001d14041d49200a090001c403c54401c601d106006a0184a1a0030f59500424088140301001c10300000d005d8650012952465103c40740b4800c4010700c0c00020815280d01200c0700b00080103204018001c0001031828483c566403195960301c0050081803040d500c1d007680e1011129180c2c1240c00e001e60000306403190403000018003810100c1111058045100c031182c074a0703c0c540c0c5000741d06080c0d500070411050a5000110700300c440001510070786503590b007401900314100c0703590b000b071500010702c3e01d21070386079481c40c8100700c16290807103251810813103c003000b0401a1910042e02e074104074900d102080c44102040c00f1181c442902d04a036a009043ca4103000611048070000101d10801054000581d50350110a965a100a00c00d0103040e038410005004070440202c0000c1c4001507 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 222031196 1250 222029946 222029959
    0x1c0e21030a09030e040e0a05060c03010b04121509120801080610120302160807091b020d051803060a2a050a0c0c0b030c04170703050a240f0218030102090901060c02 72
    0x1304401003022100c06202d40381d03607a440140410f081c000d04025041d4071117040b030003040c070f1503040c9013038121140590310402c1c4009100f040d8810030400f030b81d85205001109800100301e05d010364180300104003080d00901001c20800e00c004101c50300c0c0400e07902e00c40e056a01c0342e030102e80d150030144a07500c80c070f0904c190304501030321200c00100003108403100700908400707009041e0ba0381050284d00c100d40b00700c1ca1446030440344c2c0207002182038000c60581c1c810074442c104030b0340b50f00041c02510001c1c1d40c210f1640b6071501620081050709055903018001580c54199000b030502e80410f0a9072007144c1344400703840810405e101174070000f0300c50031303415140c24400c9400d500010307501c0c0868800c40e0025a407c201d503a202090900c0141c410207514a2075800c000010042d00d40b45459043d1901050440509511104841030340440600b80c1c200b0403034015080108103a868200342c0100a4001c500c0512002000341e6400c0e8081c03405000b5501000c10007010b26540c0d03441c1800503524840c2d4003c00326003218 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 222032446 1250 222031196 222031217
    0xb06040e07081c09030b04020f01090f0e1006020d08010e06040204080307050a02030c010807170a0204081f0f200d0e030f0d06120f060c051c0e21030a0903 68
    0x6040c8030400062500d100100003040300b0001010140180030300307281c1004413840041003c100252695900940c0541c0c04d00040201c100040b180d040c000c1d044418006002d4100203a00e1100d041d95a102e045104801d0007a1a16404201c1e2111552501c0c040007a94010041c001c1c02119111aa04050001e00061400d6078902000d81140c01c02c64081d0740c5600314000060943c1418014000c0c185801d2038a2103007850008000b41a004007071007000c09074040400000d070300b4820342e0f048401600350341040780d0104400b80e4603520508004102013180a06110b0050500c412a008152164603100c50711112404031a502c00c11503080f2150b600d4520361140b0001c0303030424042c001043c200e000700c002e00f580c034402e040d0b44405940d5203610465040120b242c015000c91031301034107040d00551000c40403400b0b14030082d0848031401000c00300754100d681003642c9480150240d2004d040011030b4400d69248000f9903002d003c054101041d40c1142441c20400100c4100e49a8000112144079040003081e50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 222033696 1250 222032446 222032471
    0x30201080c07050c01081f03050c0f03030f1b010213180e190f210518010507020121142703090a0303080c07061407080a050c0d15050907050301051309020d0b0604 71
    0x28901940f080c0d89c550020403008545092032100804010b07015801585029a000c080403040c1c411464000201c030100403266480041c2901116000c02000c0c1001400c6034680d2013004689850801071078506140c0241114500300100d0000f60300c0c0c00c83d2a4403183c1c010540c40b02c1c42c011940001c1110440c0412001261801400b00401903441080d514680c9886421300318a0441403600e2506041c000d05000180045c2c1e1702200002142403801d2420448040450b850005030a485c2d4034410028078500402103240040e00404000c48460b4070140190450907001a89030320840c0c51a0782c01104841d410320200740115980c82e000f50342d12803081e14004d01a201c20040314011455580e01100703040c144864140c0c00240c00d5000101032a007080320b402c04011064882c41002c411031100c0391503840d80202c410130300a251004181c0644000200d00d056071004115600900900d0b1059001940703610302a03480d1310070301c400c00398041d08000024006448402c1c00324070041c40c0307030391198075904085000b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 222034946 1250 222033696 222033751
    0xe070e03240117030f0306040b04020c0109050c1314060105130e24011b0b070507050f01090201031b050f180d03080103060c0302090f042a09030201080c07050c0108 72
    0x41070141d0420115410581e0381a800d4903c801100c65540c810300a407003c0001640880ba001a000c0b6400a02c612000300400c5c003a0281c1d120011495103050241c1c03040c0040490005141c00d000c03120704039415001d0b108001120348107a140e0140e84840d0b00020480d5014000508078148100004e4000b01d544201d00d1600b90300c11900c4044400b80d02c50b81c0030213014181084606801c003400d208018122910754428002d02c2c000e0041d05400b0720f50081a2598041d0048402c0590410145c80d181d80c11402c3d0030f070103840c5d0f00c071040340041d18001080c080e043c11190039585014040d62030500e0140120810f00c3e241d00139410442400c6110b40c907441d803660700c1d4a0080303070942c031a417074044003503165060001c110b4042e41110000d050040045120030350782c43c1c40342c0b03d000804a900060701c4c0460005030300c0b8030300302c2d000f18074803103c003c05460103041e040001c6600301c078400d030780704185552041b0070385586014407140100b039507018184107800703580a8804150b0016511403401c0c0c4201c41d02c50781000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 222036196 1250 222034946 222034993
    0x30a020a051b030405100503070e190f0f0812030405030a0e03010605060705150a0b030a020603041a090601030524070807120501060509011808120310030501050a0c180e070e03 77
    0x101548001802c0185d0300309142040080710090804604520780080301503c480d4940a20070b21803d181c0c65221220521480120060903520601c007000c580c50303071050004e000e0301e4010780c0741c64400d902d9900d24401112086900c11640f103006142420350a41040d900110f05042c0c003070780741d522000041741d40d8075a4070151601c240200001c0a20089800da190070f20b01d4060080740b00141400310302280798500048003100b080c0e060b40c0195880e41c0384d0030308003113040118445420442c9841c0074030003401d000140c02c0741130b02c1c00b49082e0f40c01c1400708803813802c1e00405107a4030743d05c26102000007202603014844d069848002e505140c0070080401442204480e0241c1280c1c001c00d0000c240281c081d40d0111040790300840c1d44901d003103000e0603c03018a0b80c601c084842c481d80300500200158540c440300034807000a59120009000710305081c9011070207840e070b5104801c00207400e143d88184020002c04402c1c1110000f444c100003546459000b180c164141d200398640503c0341281180c250303600d1402d01c41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 222037446 1250 222036196 222036247
    0x10212071406190b03060103110d030e1002070302012601120f05011b020c0607050303040b19060b07021302090a060503130c0312080618010902091807021b0409030203030a020a05 78
    0x142c05590410f001c01c07030303d1250409019511280050000442c0f08611428012085602e0600030300070345411160115002c45050300000c0c5241440b1001e030b000610841521700c02d880c6c1c5600180c200405030083c03104d28001601004000004001200d40740008806443c003c480450700c0004d1038844a0954810502183d600e82107141c2c0e0080f910b078140007089808408485e041d01d4003241e9100c00340d4900001d080a00304000b0f040110b110808821285958014006414440255549107a42007500005420781c0248680109240012120320844020341402010303101d8041c140841183e4a40004102c119035045490136080898001c040c50001180f0402d990030303040a1441c0010301c580006003145005250307011801103401c40611040303040d583c40050040c0c80b440003c1c0002c41106c1e60b0021190300580d0401804201d80d40800d041c143c80d650a400007400c0080802440100c515100c07000d00160428000303d0b49500030340e002490705104c1c5250060030080c000000c0b0480b02200d01e1410b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 222038696 1250 222037446 222037471
    0x1052d0411041e050f041a100207030b0c07050c01080415330305011a030712020f0d080c0705100c030302030417040806070206070201020304030c020105030718230a05010212071406 79
    0x2089149050012080410340964003401f80c00c80f1004a4515621a100d0031489640313040c5e0101440b030302c2044000700460300301e0203242c01c0d41080365243c4019800850240c1e6140240c0800c503026500901907640601e0380a00c09041ea07460f10724100000300640482100d03103030302c00702482100f0245045088040942c1c0d07902240c1561031850a0740c212030f5440e015080d1841428250702585d60701003584d408440c0341840441482c9420301c0000d40401420400da64030045110090b001d0080d03002c06403149040e907008a5100980b03c504011030f050710031064a000400144050700041e1083e00079580161049141c0d820841d4410520b60f11034000b600090f0440e8072203420095110340c108000394000606d400210700c1d6090507180182400508000070341270150003c041008603110f140c60003030710241a01c40c0d08500d9110340600103501c100d140c080c0403600b00242620b020b480c1c010982002c60744141c0061852107442c0d5501c4185410004065903401124021542240b0052020a110b0038000010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 222039946 1250 222038696 222038699
    0x3141c0608150a0b150a030b060a0305010521060c090d020301060b0c070608040f02060c0c030d02160605040f0e07090b0a0207032003070e090f0a050601052d0411041e 73
    0x1a10580c10051040c003820f030422600044036200d40c011101055468000c4543e211b4204074240c01410442e1075181d044113001406d4003a80354194480381c10ba42d011510084055420b045070210f100316a40680e49030340000e004242c9010030340004244905010b00754840d800e0365a0000b0382111050b5003c151503110000e918484400144540c001409150030a4180ba00b4262101c522074001118002c0c0280700011715100d070382800b00110386102500800319480c00b00c42e024000e4440100c0412081502421342021459a01a44c1618155149d040d5201d00c03080c50812800c00741c0c0000b414800620405050101cbc86840368001003031094616001844903502c1c51905c0c0c00c41880d001c183d0744664008001c44c000a6801280050890300741c2070241001d501c0b4084554207103488480009035034429201c80c01d003040004145241214000c4a1090700f54003482c100440d036509900c0568103640d071a944036601c034941a406001212159203500d8103203138585101c040c1200e102d000110020512110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 222041196 1250 222039946 222039973
    0x3051002070b0601020307260906030a0b090115020a0620070803070905040c0e090709080d03050615031e0717070518041a0d0602070804030b040303060602070303141c0608 75
    0xc000e0f03048802803004600d0070186d5103914061940007001d013261825449951100d1160203005e481002c1c40085c42c2503564289580700100621200451a014004030070000400d40d000711200428404650041c154450603940c034440246185842080c48013010160512410000c40c0030703042c1c4902c507400c519901d040941700a0242d8140d0340c8214801c504211803603c1c8194801c01c11064600b0a80d0035001035102e0007410386d505c50140d00f01d001d091007242012079005600d0707004540036940c247ca00c0090003c044600c100b840c4802c03142031030b0b659040b507050743c032000d5480a0b00741c0c803580c00e00c0c01c911440740740003400e10b5220040d42c2d03040000d03d003c544107913503c442c036603080d80b03040e0f0880d8100151568010a6181c4110f04502e01e4810f91a02d14620180002d5070101c1d004107070b2021955664645a1900075142801a1001c0d40020b14010000c80e00714000940002540d406455a80025032070700c04120407076004003020340c0741044d01e42070b2061032901c0c0e0280030054002c143c064450112503c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 222042446 1250 222041196 222041213
    0x1201060908031c05090c030f07140904080403170c160815040b01140a0e04050109151802090c090a03050c010f141b1501030303050f07030c080a020d060305100207 71
    0x4109003a10381041204041020184003075031100f400d02100800c0690f60f41c08000e0410f12000754241d01401148000396002c40c01041c8a001c0e2110564402e10001407501800710380b8400322402050440100010700c080b503241805200b40390b0784080740364540404022030741e003050080c0d803613030313109a1a590041c4035030041809080342001102412030224a002e403250100d04c42c040c45030b03407074026012114200300d8441c0206031010300b511040031001400c00f460114001e191401d0306565000700350544124441c07880c028942e1340a81080420140c0040c3d40070840d03d2400605075104e003c50801200009031101d45600d0000c502030b901034407000105100241992288242030030400c000000400102003a040948108485103408440003501d40d0248500d0300703911030005904d11100d50000410147e2641001d84506240c01000650362503a070029820345d50754880c2840030404e40b00018950144036400b500000e441c250300841c0041e80c0303449460405120745a0028141d4002842809111180 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 222043696 1250 222042446 222042449
    0x1b070c030228030201083c0106110a0206030711010c021b010f02070b07140609010e100504080313151802040c0e0102030708030703060902040b0d0e0102091305130812010609 76
    0x10801d060b000300b8060000d07951000a404020f06111512000c1001c4209404500c45490800c00b062030098407108000c0c243c10090381c4d0214000580940042800341c8122030552b92503100400402d0345078115070030030a1a4200a101c43c0c1000801c030b01c5601300e8402405446140300f0540c02809017600d880d40343d07200e0301c031044107468140203840301005a001d038005107841c125101103121607250000d034500002ea2004064501e05940f04042c05c0c0841d41c034040d0f05c084410984070f001c842d548501e0208441c20b84200b280c01526040c1c00340700240c00c1120080701100114070030910780c0b9076910b0003000d040894074641600c180389036003001c09000310b0600d44100e0000e82001d0070617031419541000000d40c0c03403040c0000103008a8001c400f2468447c013070780014000d44400c88040d501e46803100700c000c0c040d81000300d003140d4107401c1103041a0091018400c0300c15440d0050500800d40b684800008085c00025210b070000310ba0358a408c002041003900580b12480c1010b00d010105d52401100501d00101c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 222044946 1250 222043696 222043729
    0xc1c0b0307092c0307020306160e041a01030f060b0408150105030a020a0b16231005070509040b0109180b0310050f06010c020d1b090c03060317031b070c0302 69
    0x502c00440d0f44500ba8401d199030001c1c000e4903001d0140d19400c001401c500038004d000350580f055005000d401c0b034501500084c90000c41d44ca003030f000302031403041002b500c0307d4a4180100b0110a00d0001c030f154400d0f00f100c003c43d0040d1202003083c81d5148100741d0b0aa100354051200782d0003000c0c1f2000c3e0b903030601003940e00510007100123010340103040d00022a08802d82c415006003042c0004d02c84070307825419420103030950b042125441144007064040480c1c4c0d00700703d10044a4007400450069940c114412140510803542e142170801c41000306000c010a00c0700202c41c1806450140026584040c0a001c5003840800001007803050000082c0b501c1d284410b0060140d10f402c00d01007006000101008a138005424a0100c1000a050010901001c001003001e0411141c5070f880c1110f00c0e084640e91740446811010410140c100d80344103c0484a203400010100305101c2843c410103280b0360003441e04640da5503450150303000309006560342a400002c0c100e4100003001400c00542c03400b902d1182e2a01c07035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 222046196 1250 222044946 222044951
    0x709051c0b0703021b01140406050c0a08072001060b1306050a0503040201050f0706050a050403080105040905100e0c120a0201030633050408030a0903050616050f030c1c0b030709 78
    0xa65a00714161400810500406038003144c64100401d0b8041c6007000d812440d002007004860083d04240505012582540c03903908010100b29001d550008844602c10181c0d25035aaa444008044640a034182c0d4a65104401031002400d031a0f420301c01d04004180846a1640c2d6070203d007020759808805510181c1404030501404605581000480e680240d0901e04551b455110300f0402041e40200c5130050100342c501800c2000f03029440d402280618003a8942404581e41e6070100804e58a4110700108990010084078902038025000705005d810807034240d4204d11381d814089412442d000c02084095440051540151350b050721500000d4a000c070b03803044030030000c400c0350f4018800d034558141180b1288001080c1d003922a030141d40140012034162541d43c40105402030825809000a03076240c019a804581d10318100768250300c2d4814680c4500b4100780010440b034406801c000d04d0880541c4040000a0210884070761200c0c0c1c680303082c50001201c0c0341c8101418600100b90700144243c0e031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 222047446 1250 222046196 222046249
    0xd080705090406081b1504060c1505040f062403020603180a0813140a03080703090f060918020901020c0d030306050604060302030708100f051e040501030f150506090f06011106070905 80
    0x91ba0104481c140c0344541400061074000f40341400c40305104000c0d0b003860500e03020901c403c00206014014925000380b030b0601072000854490400003440200001605400440070801428044003a507800042e160015a540b400c447c0313580d0400781c0080c001c480074940025400408540107402c0da0141480026000c5030700d10700c8000c50082c00b40350002619212002c038051040603c64110f1801500680828026443d41e90781c000d480714920740102c003880070615510104078a800e02c01c0d2050a0030503402064050240b00601401244150041d0708064950340042510b468290040006119594005940e4509480018420003002d46000c40b04a143d16080047d0366480c0040000d8075011100500c0469030420002c40340c00f0a03c43d0540c000f403c1100000901c02144165210320f80180d5410a08640341c1421004403001115556441300b403020101320f5501c1da00d00d1043d8089018100072085580c50799031545004000c40f09200003a0040d2010721545c02c0006503c005030010042ca800c220307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 222048696 1250 222047446 222047479
    0x901060501020d051b1605010f110d030b0d0501140a0c110a0b07031e0906060803040e0408030714030a0b040e030403170c0102071a060103051003050d080705090406081b 74
    0x2c0d150b40d2072031000c204000c1a1740ca005030b9039a00d1400d441c018142100e84100700c02c684c0c0e0400424a216480c0030848c0c01490700320150044028221400500011340380704100c0c0d040c19401007680c40720142d04004a11500c8000860034440c1c18069505100317a001149130580b41107081e9030281c0710032000c210001c2000ca0f0446000501d1101e0240d000c6061000c80c1e03102c080840040584035440070b00b0990784a012130320f00102c0d50003001154024901808501d498241065030b03407142e403052010502345200040d001c2040000603682051103843c004121249068100009410590741010740719940c0700d8070621450580700b2a80341081c0b040145090038a180c032040b20540d40c1e096014100000000d554210a81c01e5048403100781d440307000458078078075452b9802d121a8003280c0440c003182c50040402ea00018030101c1104481d4804020000d59500d44030854034024041c04100902c502801480341d65a02d42c029600640328050003460841c20701b80058064516080079540282145017405000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 222049946 1250 222048696 222048703
    0x40b030606132003010317030606041a090a182a0503090f071511120d02160b13050c060c150408040306110901030b2e030905030c070e090106050102 65
    0x124000700c0306110030840181c2801c0261905049441102d0f400c03002d0443d00da00c9040c0514181c9000e06417a10301200a03000841c0300b032000340e425990208050004000041e64007074030301c240c0d4686103034250412a40300c01240c19001d280c0c2000350084030101030407580c00541c0c4500000c0005048100c100700b0f0031414410f04580d0b09400311010000c0010000d0f442c175104000c0c50005d107142100b01c1ea035040e9625584c1484c44400103024000845099500300000b500003501940026220b4882c1e103040444054400294444c10340103a03d0642d81141c0000320b1024904144194a5104041c3c010a0b00c1c1c64002d00303003c08404607520410b414400b850089000044644070005c074488884400d40b40e80c2440c0b0b0b000d0146a2005046074104141c0e00d910202280c00381441ca802078074141300350107844080001400c1c00c00c03000d0040c0001c0803400e108000388034500c1000f40500e81000108080705489090865105000102c842e80c0304030f1341000346c9100d925140343e0041e802c100802c461400c01000075203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 222051196 1250 222049946 222049951
    0x10b0d0b0a030f050105041a0702030a0c05100c05040f09060f090b0109080f010c170424060801020d060f0b0403080d020306060f0705060105130c0837051005040b0306 73
    0x805540c0c0c0d00408105464407a0705101960f0840301e01030000301540b07002d6011342421601150b55195540300300100c4081c0c484554000d40c0c468001d9401d00c13200c00000c076181d800059056500344140ca0b10f030902003856200709100d212036690303240c1c1c2e11400d11007040b080c290b00358000b140712864030340e0401c0100414000070059803804040450003103e10401203d50f1151600b24034043e001d004040f550b0300b0015440f5110480d41030310380c5504140882c00f10b880c402401c03280905075450a4107811401103408440c10001c0901e41c4000a003c1c1e2180039140c00ca03006203212103403070f503601c03103003032007050306c0300c1d021100130000d03044502e28003411071ba2060383c00c2c0145d442c030541050f00130006c01c81c5995441c041d03880c2003440c000304036200c148608006a4034a02807003844d00176588a1010009003403127000709072546a0b144c0780c06101d80c40c2c04096174481d201000050001d0540080310311b100a150820801070521000004111401c14108030380304840303185d00c40762107646442c42000386901c0c017051155 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 222052446 1250 222051196 222051217
    0x509150a0c0903020924090106021e011b110c030102070c0e060f040923120414150c100c020a020a060c0213150603110306010c02100309080a050c0c010305010b 70
    0x28080301040000d0380d4034010390f00001d61002600042003101041340c1c51124000042d50303440c00300102c0540c18003040306804e01803040140c00a601c00c403010001d400385030724008001000000c01c1076036291149015046000e8079400174950b5400d034040a00704002c400c42301c50b4210006c40c5844407aa03180700310303c000c0f0322403041080010400a40b840d80e40f40c3c01151080d42c080c009000300340c0640b40c408505010080040c54044019404002c0390800003484840a4040e00341c041c03405007460402961804408004e507417050144440d820040200d5000d0510541c024008118040440c0c0d141000d441d0390301c104108550103c010b0b400544c0d03400c409681260341034103041c1c151480d28004038140d07010710000144028101080031a4181c01010314801f11943c40da070404c0800c1301c0d2000c812041c44141da002d800501404100b5000d464450041200d402c03180c1000242511150780e042e955400c1405098003080010030042c03502c0b13000340090030003801c003441d00700142c0d03040400e0301656008444606 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 222053696 1250 222052446 222052451
    0x80d050306190b07060c020f07030c12060f1406100e0927010603030504050a05010c020333040c0f0608250c1a1b030103120c06090b0f0402040509150a 66
    0x42c030841112101c480042d20440c24240da8074811820240060403011140388018440e040240100e03200100307801c000d507940941c0182c4c0e07c61418210091030421003c090f141e03644c1c0c4d5240400681c40b1071041545203441d04100482d02d190000820010f01c1035008032000707000290001072180d6695003102c50f03000310100c240b0b064521021a241c9094000d000e0a9410340d07103051000300500d40c020014104590046401d0300c681512600116980044044029019804001c440c83d03c104c00600c9884603841c03040011007001500e48400307040c048140c030b00762034000b10180c0030b01c041e525910390007002e081c081c185006281046841c444900030300390304041410744048440503442d4841c20f114584140c0060184400b0441080e148421100540301d42506a40341d5038062802c0d009a000c1e641201e4111210700d00c1c0700180d0f8002da0300c16000f4a000c1700e0760b0303650350040000250341c0c040f0140140b1607040700c008503107420320501088400180005503690300140c9401c100d25070f038a004a500c00c0061202 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 222054946 1250 222053696 222053719
    0x6030c0702040c11030a1205010f03080403060b061c020d0c0507020918071e090e0a21181715060a06050f04090203010e100509040206040302040914010e010c0801080d050306 76
    0x1100c8100d41c2022031300580c0000180102c2c519808006407401c2130007090100307c0d59036249456045810203100090941a0030300040012501da035010340400d201c050000e900c1c00c06034480120381c0941500107a02516800b180b68912484a0f20503402c5808082c1072403807070080540c000070300000004210705400307158141c6843c0b07940000d00c405070040600035070317072903d0380c441450891000c0c059000d040314551031710503030a0b8805400503290a6140e0800d16190440c100014802c401282c4500700405000e00340000ba0200080c0c09500e13001020a0000350900c059080795040c244000c080d5845000b20955040c805560703988003005044641504285640e00d02c0240c8440541c02217a0144014a00c04000020a1000786080c18132441c25415450f20540e207c1701084141802920040c2d0001418801880142816480314034141c0c080d2119070b10809205054500b0360350001d480120507511140d1600e80580c2200055000d020144050314180f040d001c03008005000040c5030a114207040c146 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 222056196 1250 222054946 222054971
    0x40f0201031e0e01050606071a0702010b0d14010b0a0f090e160305060603060a020c0c0f01050d0618110301050d020f011704080910020313030602090102010f1e0b06030c070204 77
    0x46a00c0d000d0302d4040000401d5480b955040081ca80300480d00d40d254201000141140703004021201500e520040340080b11118100103920700f1402840981550340c0c42d000041665649045180d40d140720343d240c200c05c3c214456125080d10800306400340941003401c002d011000d40100c9060907078004c100001350061000c08240e140890303c585890304088046804010310401140c1c29100c1d0405601712092074481850942c2203100303850105080307400500841c04585080c50525041d0700051410a051802100000b4100c0d656641b1021502810355103e10b00640c0c64050000c030450030700c0c1c19a00350340c98000400c0c8070030100700000b8440c1210b4200140641e001d841a2070b121440d010349403855242c103180010295000046c0d103031107a2a00900001400d20010403a0868810718500200aa19640d41c04000e50864600d40b4159500d50702d405000ba116441441100c0304a981c6100203c41c50300c045004403104041020f008000c200204040100039404540d5169410313200096492400304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 222057446 1250 222056196 222056201
    0x30903040f09020a0206090303042012030309010b0306060301060506070f020a08030a02070602010b0609031903140a05040302190e0708100e0906060108010f0f03031d030d050703020708070608040f020103 89
    0x401010700480084404102c020b040d50103440e0003040d94003151680c2d2221148075560740402c460003026050100f1100030701e02600d54804000701c10240009000d1414040303d81d085410482d0105116075492085241300e00d03042000640044050b40200801814040402c46034410450302810440c207001c600c000715140d240c0d4000090880000303072500c44449100094403014244074550041d801e0001d800010b140c20403c98110440043c002c19401c601c121081404449000003038007441542850300301355003223202c0200b4410149580340342e40c9508510400c204903d8080c0c0544003124103103010702503180a0301da41504000c0c0c1c1e0401c002d01c0e42c0d43c1c10442d060248160003401d0400f40000030b004003040001000750107014241c03100e030607617030701d801c004601c20016101d45d8032400400c0d1003c00200e0700408038a40344084100000022038100c001080c5001c070b0758940345000807000102c40d0141a4180704003000b03010304e035000c1c0035001d10b462401000800041c1c000751001001c7c45110f8216030003503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 222058696 1250 222057446 222057449
    0x7030b151012050105040510090506030c0a06090e1006080c0705071505070201031a0102030315030705040501060503040c081906021c06091506030e10020901090b0c0a0c17100203090304 81
    0x181807109240e4142001000c1110301c121041199007003000220351031805018991240368001000d8014515041240010304005030145401d8007606a08494036155210b019014007110f480c1c0030050740ca4081c102d81461402000400170f600c00790300502c40540d10040060300503603200c3c01191520320781d003019418403c266002d000c5060050010343c0030b0036040b0010305680c44c001d8808101165014600e0b1105003402200e080c0141c0041001034540e00014034049070007100541240c80b52174444010038121882030b04200c1c0031600200800042000391085a00038020401c041c0c004400b030035102011200e2003aa0003400340343c01040c0c40300c2601e4680b1003000031900001041c01815600e5121400403d181c11201e80601606000450014000d003e0300514107203031402460b0100f00c00302c2e85402500728464960402118080c00107005030000050304031000d400d80684030031082480c101060810540c00300651405c1c00100d00e040303c00120b007541030300a08100159896540c00207650652045 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 222059946 1250 222058696 222058699
    0x1060f03090f032d0810090207120311040302030307050a020319260d0518010c05041d04020a05030304090e01061a16262106151c020a0206070215010807030b15 70
    0xe108214180d980d00c81c1717100740900b184182e440b031000d48036448a4240d2059000245c02d05201d280900c158a202c3d46c002d00348100c80180c0c0d02e003050345a5000a0469001440030b80d0542c0c4140b044001350320f0103101c2c0c0038800e420410306c603c1460742644c942c2252800c48440700c5840480c41c60b601d602442542c101c828102d02e460082140d45800c1c502d0000740c1080140804040d840e00801c11000c034011030850b03090314000113260001c1c2c0c070503004200e2940ca000300b0813604032802c0d080028035a10100083c00c00b500e43c0507800b04271254102019800c4682ea5485001200e00408462382c00c0c01e800000c46001d003407072084015030743d05181001003144244110922880850010050301d0b1451540601001000091842000c0c0c1e41605401c0f22004203803442540101c03045501c0c24130480d01c130010a51036003044601900a0b010034084003c13a000348000c2d2016800030700421035080c1d4141703c0f00304250000400d0b04907950500221036a070720160f010081c1114140030210b400c18282049200e2221070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 222061196 1250 222059946 222060017
    0x7050702040603030804110415180b03010203040312110406080f0601020a05070602030a030e06150d031b0b0a0b01030e03090103020c0f030c1e0109023a050601060f03090f03 76
    0x40d20300e0010031701c00341181c09488070198450b07000d04510f0280920880b01c90041140d07511281481030300c0b800c08500820701d0680560741d160082c50b0762420b0001d1885240242c030380c0d102e80c0b243c07041081c00341c80c070f409481d00b0b240c24108814000c007030b0400543e6820403c80360480b4995035aa03c01070345401030840020744a0312822200241d80740e8004014030340410580d9060003240f4464080a036244000d0303805c0400c03183d40b034032620010b0605041050b0458002e18081c004110001144940154094002c3c5d41400310074007000401d1a25004109681c0000c0c60704000d07105c1301030341c180d89034010b0740c007903034101074000035081190007040056414403102c00c4181d80c0c1e9540c1e0928030542e03d10722503060389503030100d40c0216080e0320f0042c0700e40d0450540143c00800c85c0043c16207080e072668151a036003940000001c42e036060440c10594001ca6441c4928010100d40d4180704024000a481d0031f1800f00b01410300c03501e0f00c00114070700fa0803200664076041c03401842c0030040e80c12201c50845450209001d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 222062446 1250 222061196 222061199
    0x225030302090d12110309100809031b0106090605030c010f03020927090114070f140c160503060a0603030912020d0215030601080c2b150617131703070507020406 71
    0xb51010f0092958144d92038410915401c0310002d5120301443c0d0000307510541d0040d10383c1942e802070809541c03240454050301d14040103030321260440c2000600d050442d0b95a81c0c1c00380070300c030028032850014240460080001c6000200020310300d03500004550201a00410f2241040c1c035805401c20400a04581d01c20300c541020711030f02181c503c200d0701810302c1e42c200702c0c040704100c0000389000d01078405661410f054000c40c5a00b07a800038070014000da8200000c02c911341c403218003406000301c0d038032030071200a04892030030b0308042c5028005021400d0040c60920100002604089403034222404006802140d510a00001e03401d03080700c09006e03400080944003440b0000740d000003107100e072401362900d084035115096650001c2c06a04402c03400040b06420303480b040d021040c810843c07521411000b15091001d100c00e200400d820364801400f01d006499895290070419031100e512075821000103140300001d886140c152072111000780c03110035001001c119218420412100840d40180062020741d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 222063696 1250 222062446 222062453
    0x1209081b130207050a11190b07080d05090a030201050c0f0405040e030c0109030809010c05030c0304020402090301090510020a030501140102190c0e040b06090a05070e0f01020c0d060b03060108010225030302090d 92
    0x3510220700c00c071081c401401b0a40907925259540601d8825118030120140d03007030480e42c18250707000410a5410440912000d500c035141c60040c248101c00b144040c0615172810b14000e0b023550f5000d07200c5a1042028410151b0301174401041e541104c0d0210740114002c0a0000e45500b14800d00d45c0b200141d500f81641d07102031581218426009030000b5008106100f40b40c501100c5901080d1010b0a90751000c1000ca805890103802414401b0001000010615040e542c0c0d10300e4440fa148101400c5034020076040c0c400d540611510340101001d181c10702070100b803c00001d48898038058080c01d80b5113403d030b0b10310620450b2240840902903204001c41181481e06003951108021101144507800c1800080d52501c07542c045c40740101c0443d160015000219410000505070040050341180f1034441001010b584a071440400d09004d0350001662058907024181840c1058000d01c01503801080546050084034039491b02104100403204503008842c50b00f00c000e071184043c156800303580040b116051 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 222064946 1250 222063696 222063703
    0xf0d0218120601060f08150a03060f060e010308040303050a09080d0221070f11040b0301051602011b02150714070b061c0803160318030c1209081b13020705 68
    0x805000311096028991807800c615a92082401980e0005441100c0140000e024880c000e400445040c502e00c008408080425030505103a88142d6050b6200d400c40d094450052050002916407040032120960440d260b60045d807240307101c0202001070018440c03600c00e1065441d82c01602d690410380d140f030983c60400079518500500702800ea00040d50b85a006004140100d454943d401201d6080c2c000b201c2e150740340c11080c0d580c64160815100c070000761076644d0a100311441207640c012a04410038446038000d086442d50000480f05400341d01e9034044981d0006040f010205038519000315996441604032050551000303210396103000801c000041007100032859108007802d40c0e8908401340048201c80d070180b010700d0003500060341000410060940b5540d84903440c0c03028200407400217100e034003811a100098074198001a8488694400c001c41030014400c083c00038980405458141202079440d003e0000441c3c56018004541c00780d203846208060502541c4588115207401090a00c07984 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 222066196 1250 222064946 222064987
    0x50f0a0203071205090a0906051021020a05040f0e041e02010309080a051b03040f030807020a0f120b0105030109080a1d090106030c08130f0803041a010b040e0603210f0d02 75
    0x6c60000401c000c070311b01d24103100d042d017205d1000f0012100880b807a941961000704c0c81c9890710903044a20000da0179029180001d0801c00003035030740c0569952914403208105070765508000d01c212100002d102c04500200140811400c6400c1004c8048441748010390061900c00070040080704049400c940c001d4203c40600754480c0710294000c20840d02d41d41c10f54407803240e03001d0601444004e200c2030012802280c013401e191743c40076202001c659224610420603620961040081600812261041060507030340140140000d4009000e1a00c2503034401c0440d01414120508100180d9544801d01806a10000300b404001e0541c0c85c039943c6401c0014081e1146209180c007003000680800e43c1c0520742d03000b4617a0142c0102c0719400703a1009507110b80c050f40c8003900544105414080450a510041c418140200502c009030f9548603e450214400b40030004c2080b4401d4021209070584a5090341303ca0050443c9552065034640c8060002035241c0075031803440d41044c0c40420000880b10001801d540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 222067446 1250 222066196 222066199
    0xb030a0f030206160f0c05070f0f03120201050c04030f0201031e06080111030f22051b1c150203090a050a060c020c090115050901140715050a0c050f0a020307120509 72
    0x200d40b07075a554071a40800000f446a00300045e407140307100c0c0d0300500c5a0500f250b1203100304151412207642d880e43c5402414030b5000001c04010110f0b0030020030100700c000700007080d403034002444103281403580d5100724000c41c070003d4410f0000d4800310046a200e60f0189060740040c01c40480701c899000e181400811107401000029841e16014900310b0802c082502e01c500306443c603000d0310b03030f03511441516030010100d040791007001914980c0d0001030040c01960804198102d20100e03c2d40c02d8000c2103007142540700d40f1904444c2c400c1691010880401c44c01c024001501800344c2d89844014590340703050b0600300e000c3c0050140c14400c0040200c1600021881c110643c212079007007201c0010000d01540030301c90503118013940c0d50b000c000e4a0181d805000980d00505103040d114400807040b007003651142e2021103d46943c0d6402180641d260f04c40d042d0440000c0c0800c10080108141c00740c000d01c00c045003890990804503000c1c2d0407500c00c2040340c07020b55011096500080c1d908001810340c0d0052050203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 222068696 1250 222067446 222067453
    0x60f130312021b040c17040305120604060803120403140d0209040506010e012c0607050607080115141608070b0406050a05131101030603080415030b0a0e18010b030a0f0302 75
    0x1c10303200303200192030300c0c40d11210300184054004400401004110117030781070f0144401c0340811041c580c0c1e5401a00c3c40346019484007075840c1300c040c0303584003e40e100500591040340b42210511041c0d400105035400202500c3e5501699101c5040135195105140704c421441380c00002c0445100c0e03000d8010784810141906c0074010780e1a100015034244400d545d00310300050b83c90000a601d181007a001011503c0080340c002c110000c0c0c013012030015402400705880c164800c000344440194004055030040c140115070301500c41112200426407410040450040301c1c002c120348840803860340300c0f10000c0b540908842d41e2641d4030f01d850a103221003114252645440d1400140096481e400740320303c00c81c0d20406441142410303035a030f14900485002d9644c1010350740c200c088009500c40000700060314200700005054072400300010300f524894210b6500030b01056104000b86030031241d505400c02a07249040310203080d0884040d00400104011030f6242c811440c0320f00600442c83d40001c4154000d03406c0c1c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 222069946 1250 222068696 222068723
    0x1b050301060315051207030212010b0919020c150618010305030a0509060c030408150c0702090c0a02030904050702061b070809010c02030a08130f050301050403091a040f030c08060f0708070e060f1303 87
    0x11034202d82d0410949034004240d00d001910f103402002e01cdc0b400b80014001c0060900012a0050781382500142da21340c1c10103042d00a208103890710010748a12414a901c03009200d42c1195034468072400b501c24284103010300811843c0481e070b61a0b0540741d041c0e89104c04c980c2c44654901a00390b58071001e0010f0941d104080c80401d4483c19104210751240e5000b52107000c40352102d0820040d03c0c0e000101c0c1c0f208500051000ea84030799507030b01555000701607e80c002e01b13071420800c002c143c002c0354a04103540148820443c1800081c480001d4400d10642420300354505000ca002017414503c900400030200303080018999031004030b080c441415110600c01c002078113074841c1e041c1400c840040e18041e000c111804c8081207001c1d0201700d64a0704404240200d41440d41c3e403004007443c540550001c44d107402c080c000034091000f041040c81d90061400c03600d0500c504165401030990a4060403040403c120030461103115101c2000320343d001149940d03ca69180c881c1c107400d80d589155401700b15140ea0b0304008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 222071196 1250 222069946 222069979
    0x17040f030f02071d0a14151c031707180b03010f05180604090201050c03041805090118112b0c0602070803040b0306030705030f101b0503010603150512070302 69
    0x20720005590344008108840c203000d122810748110f0003081c82034106c1c0c07198078080d1101c034203801140c0140440350440f4480750640007000f00d07443e0903103c4541c00340c64500080780400c1e0f00c000707018041c1440106114003a1a05103003181c4100342d08040c40c000f645051030024145e503000000b581260034443c00c100300282c9503410001b003030010342a050108060500442c01c030345443c1e40020707282e03481410f090f8070b04003050301d0560554000d44d1044040310051a00c00000c80342e00d002e590703031204a01d0700820500080c550440040c01e00684060700300426842f410f10640c03070381c680000d0421302803045401000c2601c1c5440c2429030080c0001c07030b010300c0f00306c030001a0305000069080580d090400550708103820b04901e003980350001843c00d5803600c11a4800600f0762010f02c01c0841d68804071000c0c06205c481303004104c0a5400360000c4c00e4004540d401c0d00410b00c0d610a0070780f41554000e1601141e408000010403024140c903820290b800300c0d007828240c041000c00522082104c0c03082c2e440e03601c40c2e104000f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 222072446 1250 222071196 222071203
    0x2906030703020904031116090209012607080c1216120603050d0c060f021222020109050108070c0204060608090d0503010e180f07091a0303091302030717040f030f02 72
    0x1c00250070400000110300043c4c014280641140504000c81e03081a055210b940781186040c0c0c004c0b070141d0b50002c2d0260242d6400350440b030102600308600b510701500741c80c00c90030300390004001408104040c0c0200d00300340710150407118441010b60101c80c0505103155100002d10310f140c403100224505440200c8414010b024410449421074042d20201d01501c40642c1c0416440340100d6000741d0350020410400003504c041e02e600400704170201584c0c64143c1c441c0d42080340100d482d0307039080710910710440140e030300c9003100301500c81c2843e200710581c43e1801305445803410464029803007410504081891940140d41a21801c441000c03901801b50f139201c00e440c144020b0003046001b890720b5002800c02c400e15414065442d1900040782c03c410103c0d442c1034188041600000b8480d070711000300310395080c03040c02d50828044044002d10701d807a006000041100c40001100040c1035008070009907240c1c002d6030090780602040d081d66195103030914101d80d862f8560070f4203c0101c1d281c0b4001e85052032002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 222073696 1250 222072446 222072449
    0xb09120f070e060d02090405100501080a080412060906140a05100303090e18070905060f06120723040611060901091208280c090504150b0f040329060307 67
    0x1002a0031102d003401c00c80d440c94000100010b030442c1940b815400141c031520800c510a40c0a81d002d820401d03034201c134603000d41d0740c180d001e07401940c40460900c010400b150211130441d11052540c0316100c801e0702d0001c0103000d020704090320145c070b000c0b5038140301d035112040c551007100070100c00c1180740c1d65800d940895051a00024000410410043c403042c18078000e201c2d00214000c00040088060460251078943c40d0b41100c1d40154680302400b1890800303160244119604661481c2070040c85d080a80c210305008105104002c0d49041c0342079000319008207400c5210702002615a11603c0d00005400c1208001d1944030368816030300022440c41d8103105d0140406d40c45449800c1d9003000e180e00b101c0300703030010f41180350a2414810703500d0029808566888024a00d43c0301050250b030000010b40a2034196200b5030040e4104403d8400106400d000b60080c0c0703c110649548400160400180034000c9410041442190350070355144044441100701c0400161b081070003107591042e00703054940d440f0b0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 222074946 1250 222073696 222073723
    0x1120213030624030f0c0f1a0d0e0106060e01090503030a021c0e030a0b04150b0a09020c0a0203030f03180309010e010c0303181b05030f0307080a090308040b0912 71
    0x46400510005031960054410030710f6680510342002c041070540c00000c1c0841d0301c100d40070340050502004109079100c1110081c9107012400c1106881c24824400c40c030441c41c1c0b412030722200000c43d41500403040d480f4001d051003080081180507150f0201070603003941c1d0b11032240402e010180000d80d40c50b00008441c6408155400383c50662102001d2140b007a8811150324140300d141da0110b58152800c005100c9090b0103000d465003141018144070442c030301c010500c410110f0404003c0701c80e43c0c44803140c450031070b01c0c800001a80c40e14001d0046007004113030040258075000004808510000c0e04001c0d500500303610020b0400e0402c0c01101966903c9203041541c08140c602d0f03480c103d198011402219443e01900f004125690030303400d211161100a60200c82112101d503612201840d4244242e01070314058005003203082912541941e20300070b54900402403800090300c9280203105e070327803120003c0d90300150380c1d40c0702c1d40c85201c900401d8008040150040c42030942103402a00c002030203024a460 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 222076196 1250 222074946 222074977
    0x40f05030109080d0b0a030f06020d14160e1305010b0408070501050a020a1b08030703020d1d06030a0c17040501140f07050d0c050f0c070f080c01020615040b04090f02011202 76
    0x15140c4d41c401030810210010f5202d0390404002002c681040201a0003500c202030041c5d403600580c40b10b5003122010f6107202d0752a81c490081181c2e032805030400010b00a00c50400c00710068a000015030760301c442c1101901c0242c144800000c50084010180080c0d90111064a11080c2c603070004603194000c070910040103a0101c048040416401d40344080c80030f405c41030f110b43c0103494181e172a03c0c6038010308086006900422140c06e429510201815104e01d0741c0d00043d45040c035050020f645808054454074005a540550543c1c1c18020598104a540c0e03880e000c404c0e038a404d040041c020024514035a415119100000d003c0a0540b031503a441580300b44c44003410001d00384104001040c550900909200c410800d004403440305202600800d07445130024040c20b41003d00303030321044403035030310030a02c0754400418610184c0c0c000c210396500c010320070704c5507400b18a0500068058030200120302c0e00301d458004c4550900c81c2d64503014565600030388954900780e010000032000c0340b050342060b010160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 222077446 1250 222076196 222076207
    0x5010f080a17130e190609050c040605031005030d09061211180301090c12050c04050106020a02130b1f030b010819110f0c01050402010207090b0a0521070803040f0503010908 76
    0x14407800780c01c1d01d038000715011041648581c050444c0b05402e442000d102c2601e00c228884c1c9240350300401000c0d1203416401e009508000d100c030b4416015900805052160210000320050072015200009080090884000c110000c0d40135104107514002c81001500b900e042080386400c901905040300385641c007180c40d01025100b03c1c840e52950a814a900d9521162100c0c0424658200783d0302401d071000301c01c0d10003892481d04034500303002e0300e031803a001d03604040040101c0398012403030180c0390b5015250000b001c260758a03114020510154003030b40c8091218032451410311040014141035500341c40400c403c101e1a0010b440e11b100c00c070391106c00140b14a100b00c0d0071174031a8000b2880113112010642c00c00f180403c03101420703042285203010700d80d965000c001c03d540c0e041241c10001d080e5030804116a000c18004140450f1082c00f515001d924040203030344200341551681c4104404c00815203032000c4e1244c280940340d901c20320603900781c0801120701044500c0c041c8036216180703a0220801e842c01 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 222078696 1250 222077446 222077483
    0x302010e0f12011407110705030604020607020604030b0c0d0e21130b0c0a050c06070b0a0209010905030a0605040303050c0f180f06040e07090e010305030d09081c05010f080a 76
    0x8504a0501d5040300c0b003a600140c04500901510304107401c440074220892804882c028030b6038900b0350040e403a60303110160400042c0c6011071503507081601605c9141d0384896a0010803814410350744000c0091600808024482c0c0c059000b400b80085130341d20600440061000480c0d8a0440c1816010160401d0000e56500010400100b0307000d4a0554510b014550f601200d04558219151039030060300304c0d407042d20030003805101c0400f40c06400c48038a030030680b07030b40c440d8100080700412502003d07500095003210350b070140e0301802c01480300030202e4403070000c1458000054541910304501003414040031604650000041d030306030a1000611508040366008010604c0c10300c80612600224044061a56034a07060014006030200c00c42203815406c100c0c00051200c0f03926400503c100900500500000300b020040b1104802e064801080d0240c04c1d041094062043d14600700c0640451030110f040c01207181c12160403103c1d5200301c01d038900d03030700c1d50301c20303129556510000e02e401000c8600d900d88 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 222079946 1250 222078696 222078709
    0x106050a090c050910020709110301030c09020c1c021504140114070f120b0901060f0f05040501050a1817011a04050601020303011e12031713051009140d0503070212040302010e 77
    0x7840317861049498959455903550704646d1408038404c00000d0020040c804d0000c3c0074682d00040103a400708500e0304201141c071a4030b031006088411064a29203143c030741010b20030404040b40c1c09005101e01301d541003030700d4407600340c0350a40150b400550a24880352500540940d4240c464001030b218502ca5042c480c01c103c40c0344001a0841d42c6080e9208403c681c0741c0c5031180100d003e031545403226a004100c409014103045400c400b0b180802c48100424069660f010050310130498a509103074441500382110703000d40f48901c1c5c100030300664000d00d012880740710542008495100b049200284010000e05000a0720002c80781140542d00800041015600b040454003002c1c40c22000728030840c0c3c07221800003440c030050a041d40094a0003140c600c0d00040580f40d075400c40407114105040644d81da55003502c400c41c0000ba00c48099441e410141449001621190070f1101e60090700d000344013140002e07050780c10548500c8014854030614003400c5011100719015a90142c40794030702480044200940c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 222081196 1250 222079946 222079969
    0x120309020303070501050a0507021614092a0d0c02010605063901053403020a02030927010e010803040b0307140c0105181f091a090106050a090c0509 65
    0x1c06210811420002c18803c0c4680c1d4004c10340f040c0007090b1800c241d103000749411180101003d000a44200400200c043e540c0c01d1a8040c1042d22241141d54603086003e203400740030f4400d200c42412110b8407072280c0d4007110041c4143d02c03000c00d0420020040050403070882c0e80303d000c3c0380e80142d01006240d4404140300010600c10b060002106001040060014981c9a94072031070500c41c1c0d1208244031198203101c140105000064400b42c10310700000700360003503000502d0b01b007000341540041d14a0071b1610a004448240320702070320f00610b0926840141d00344903a65020780e025030f0310b882e001168061500386228100c070040402142842d0a110341031805901c0586680300744140b85401c0310038408814090400d00628100000780346c41c0a031004541d07043c2d803000d50765541c0c00110068080300c01030001c210112001c03140c001803101d02ca00e810b00e20401c04030008131a5008110801510150540001059038415106908195a40d0254400759141c2c0940c84000c10002e00c1600d01ca800c01208904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 222082446 1250 222081196 222081199
    0x1b0f14060d060305031206040f0c020303040f1103030c0a110f03071517090606010e09090d1812150f020a0c0305030613020c03220303081617010902030403170412030902 74
    0x30b12159aa42d801d85158015410740602d180c01c8010080589030a104e028403204907460203224040c2920802502c030320004100804030713498071503600d05203e05200344c1800040041c0840e542d50000202c0c0c40c1d61740041040840354600c118000c00c2a6003040c0c0e0102e078101c00301500802c981c50901d1160000500c8103449141003000e111b008454091200d211240100115405070000b400d002000601d001000c1020500070344d9884280030500c1000a641c0c082540c0c0c41c500135504241901144030503060640c0101c803c610300780310403401d0009144840061500d0003d0401c0103141502d2084260b020740801d6002144812450202180c050401164002d83c0241030040d0710030310071380d0001243c00880040c903d680c008a09407090082d40719008504145061012016030310310703500206003280040a00d185e580480d1800d03050b5900510640860b403100b000b55590307030340e120711328000290402c0310150002040c85168100441128044901580d0006154a0b0000034003109030060f004a41d01203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 222083696 1250 222082446 222082451
    0xa051b1923030d0902030c040501060e130f09080a090f0f030b090a0218150103020f04060c050a08190806010314010603020c160b0403030806100801051507050a1b0f14060d 75
    0xc1042400d10050010075400040050100c095005043c44c06d0800f1407140d0023580b807c4014400c1540088142c2c1c2c08110480303e900383c07051014086400307080020903662278942000c560108201c0b01a014080c0c01c0c03d25511101d04c3c0307a850841e00420390b031500c500c030b1501c022100180f022503801007199600108000c12508844510b44c04209000c6207030719181ca11003030000c10b0142420b04000e40b114421030900c0e0640c280112a910ad0403544640d00ca9242400302034030a078810403209120151040350803000141c0c07a1082c80a494664100990b40300000410a0300003403e41c3d8024070503080d9441314900003003056824800160000e501446031100a881042d181500c0c0c00c03103100c543d801801d603590640740c94a14515010b0710450001e04018418210807520b14006c56000e4030150445070215101d020b03034600016a01c03442d02c5800c4000e412401010191010300032103041420443ca18a41001070880c3c0d40c080c011007900701400303512150755502e0a411550714152010f01003804695000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 222084946 1250 222083696 222083753
    0x6050306180106050312091c02060c0705090f090307031107050a030c17070518101706040b090d0c080d02370504030f0206071104020a051b19 62
    0xd24001044074211071910007407510907850a000c0c011040148070a42c014202142080c25110140c013508160501880080c0c50303411029002407221f0300d29603000382c03410355132781160030f682a103502540c02810b000b0001310002c203030158000786442d0302c1031203544055420030600da0740031917404120301d800c4440c07880703040d5001c5800c1e500c0c0c0710924000c510074081c0990b22440e240620b49039070780c2e4000610442d00490020029903c4512105405100300f6841055036680d41c40c1150140d40c840c1c02964440050030050074000c0c0000501c980110b00030151541150364050180f85d43d18078022461000400b100300c00000543d0f03480141650148051015061102c01600d042d004c9409003601840300c0d44641d151a814840d0f00b1480d4100c00301450883d00d0300d801d40d2541c05c92494250700003800383c1400114542401080400039010380c1c0010415550760086582c010b0454100a4250141c040c1c9400b064444800000d40c0c401c0c00454103078500201482074030713002402e0441c100d096070301181344003c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 222086196 1250 222084946 222084949
    0x3080a090305300304031e1101020a030c031d032b020a02011d010203090c0603070e03010f0203071107081002070c081518060714090301060e040c1a071e02040605 71
    0x3e40d810895520b040711004501c08400320205200c080784001d100c450410a10001c6a0311410300319014041407002030201d03400c04002c6450700081c4040d01d4071944040340c03606049a05403c1109000c041e50b40600c241098010959a5031803103a9040701b10794000c102682e01c4013a103048030034071054407200b08040e010320104403100383d9011182c20b20041c0d42d24102282c240700c918411301c1c1d81c101404000c509519041400d1136035416021881441a034010001800240c80783d06046c40b0850040c0080c81554900145040650001e96414000c10100b0b201044548000110b07101141d42d038800405c0b02d68505d8400350000d50001e00b040e1241d0074a4400841d1745441003145201400708a4204001d40c0341244a09404100412030710300144c01c0740040c484c4142e400341312805500d040c204101e43e103528540c002130040c205680440800d0208904020a000c03c01c1d00200c00c0b5250300510882c4e0b8040e05c802e0013400d2180f150018003540080810190600700c0450b0800360520140001488a86540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 222087446 1250 222086196 222086203
    0x90406030803040512070c0905041401020a031d0309011b060b0d0f0203060f070c030f021018060b030613060509030d090b060111010c090501050310120f0c0f0308030103080a090305 79
    0x40007651840c4000050000304582089400040081e0260305414451555030302e60034001180316060031661110081003d02000480d180031049284008540d0340b05a614094050080805810030001050211090080020040710040788050f0f4504410013500f0858030f20b0f94103a80c0c41a5a142d60f9403c244520f5100d12080e0070034580180080200c008603441054500b01c001410142c18691942c10302c4900e5402c0b01141150035071608140031100d007810f00807480c001c0c42ca80c00c651900d04142c41141c003019145407040c022405104140140140c02e0107060703039004142c80000d4221000511003000c103e0075400f00d07030071085210a503840c1c051039a01150545491a10648402c2c103c07409008596800006200100305502d00902607440a05000380280c005c034464107051000c0080010000410504101c0142000c6407211b110421542400ca03043c1d0406101110075583c0300b500070980354852150281160f80c13014800c0d28503804c50741e4a10f0150405840041844251800400051f000b071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 222088696 1250 222087446 222087449
    0x905010e0a0b0c120610020c0a0f0806091615020307240b09060f0103240b0703021015030f030507050a061a1c02040b0315010e070e03060610080c090406 67
    0x20401049004020b0900c154141005024065410340410004209210b00e0000c1644404202d800100c2501c00342c80c240c3c1001880401103503c11040c0402180c00e00030300307005000380c5002000f155496a49d041c1e40507540c078030101d4004800810407500300228004100b55443c1c5103141c1c41a00d081c005d26581d9050400310600303c2812031000c13810861442100e510800c80000d900700c1d124040b031700f4600082080305561110a504058851582201010328040b8003840e400078824421107a6958500c061348540150000300c0c0140200c2c40c681ca00e105a9010f0301810f07403800c0291f10381043c61039550948005602004806004003807000702d002c92010f000107100c0600030751011444412801d006401201c1300da0304144180b5179a1806241a04080d0325400240e60581c0c00007241d15001c40007a16060445544822034550800007084a000614141c0d0050314182c840d985503080040c20192102d00840d44c0d07642000c12071401d0304055102d10b05940d00a0b0f8400602803520a20001160a4030031a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 222089946 1250 222088696 222088721
    0x4290906070809190209130203060f06030d090e13060914070f061409062214012a0b0a021306090807090506090f041e030c120806030a15090501 63
    0x44810051100d0b00706100d107a101c255030001c1c141007040140d084d0000d440b51800680924110b00c00114034a442d550342130030300c0d0780040484a462504101c03031604110300303ca1441c020701030601140d00300c03805069803400b521007207851242c15603180c2c041d511201e010100162030f05600d540e1a140442d4100e0444800107285d0005000070905100b030300306085a10b944854100a44122030f55422210503081d140030040c2151740ca0382d543c0c840c00948039801c100f1141686a810840d2000403082d0404103440c001d08020b8845070031522003a203104032408100e00d42d00d2810000440390100240422011503449010301c080141061466a2031200c0d5a0319034011001080040d40203014034502080341200500d5402c605105601c1d040020580c10380c4007802400c150b100c07400c0407900304525102d007026a48080c02040ca44184941402803c92040c40c805485001c5240010341003584100726161103000060006c0184880c56654600100c46c40100b8030081340e40d48500e40f00050b000c2c098500040d50 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 222091196 1250 222089946 222089953
    0x809010212010e070e03060c040e090106090c1206050a0e060402030711010c0f1205250207090c0302091207080c010f02070812070b16020703030e030c0a090f11070803042909 76
    0x1480720000d080b1600281d045c40c403903030200d0b04000c58030740034204a8041c1d40110142500329140c1c2c003071183c05001141c10200445083c141100c4001d80e102c6414025942e4550f801d0004550b9202400f8400d1207502541007003000b9240026268200381e00119044026407a1021074004071610380c40c00c484100c95500001142c0200b4444040c4d0301c14000c80300350607004005c02460600000c0c010403441200c01d450124a00001c42030401070081c0204001000b01c00d03010b20503201381c0c02c0000c000b50300003052603100328030200040507140340006903001030b603024200800c0c11080d940015101d5800040403201103100e42c200100b82c044041c8000400c000c503070103049071155114600801c4000300200700300c00c00d4503180340c5202442d03400200c0d007040b250141000903443c6e20480100b400c0000700c0d40280d410000c40e4000244142e0560700407081940461070401189444403110302c264860058080c140400c14008140030079a0382071080440507180d40c2944000101c1c0d52030039000300049039211010380 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 222092446 1250 222091196 222091201
    0xb0a020d02190f020102120d02030604060909050c04020d0f020d050906180a020907050f07030c020a060e0607080a05040e04050a021806090433050a060e040804060809010212010e 78
    0x1a0100108520340816001601e880466025a51001c80340400c02501c10f10030f4907103d0041d079000384100f103007081449086e6595914805e00602c0607600c140d4a4a02503031800400040d002d406200f9408265803000240110496000800029402440c001c00c0f01d180e5681203048040001d1008154958803548007103294500394054500303022000b071001200c0b84211240d80c3c6900c074042892100f003a41101d407010300f5228048112210b020744400c6680d40f0800103405400d0680283c1c810007070f01c2c8200d884190160301d81c141103500300444203013503400c4003041c06440c0000d6050400f4207862002d528000c0d052603911038078000d1a1000369820742c0c007a08a000d400c0103500340200f0401500520609140b6a0300f440c1d004100c1150b00144060700494801c0601c2c6d8010300d240d615603010400c0000c0603040012031036041802004266100f80300c1c41e140040010720301c86d201d800315204a0300111020304140c0b03002d2081c2d80450000301140010b541c01c004082e0000040030725070b8040c1100309104074507071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 222093696 1250 222092446 222092467
    0xf150a0207052103030403050c0a0614190b0109090914011103040b070504031101030e07050a080304081b010e0d1106041d0a051909140a03020c0118050f0405040f0209010b 75
    0x120002c40c4000809042d01030300f1580c3ea0350001c100c980065042c980582e50f414600000c50414000100080500c0c3c104070120320452003025a0038001c41807000b60b12005106140b0900494041c043e4a0b4040f4a610314104496689640240d03074181c007410503050541c8801040038211804900d41d00800d910110522041c00b10020342c06600500909015161a04540b2a00044010003656504164458043d640d500b0000d0002c0001444054035081800391142c121070380b2900103000341860307441071135103081da41c2c0340485a425050354180c56203c0306104450611114450350030041d81c0b42060141541080d4a030035000304014038005035038203504a525040440700d1800034141c3e440080c14481071021145005210003c140400c40700003406152a14140203c090044400c81c164010041220305064001c0f44501c4499000d0340c6102e00340c100200960008102401000d420070140e0703141c51f01c603041a074426500316003e800620f8101585a00065242c1c200340c02804048102080e2103075003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 222094946 1250 222093696 222093709
    0xf0a030f0309031d04020706060b18010929040b0c030405040501050603060130090602070302010b060406090b09010c020409050a050c1e041a1c0b0f150f150a020705 72
    0x102001840c080c051010b00342c90060031803401c9284180e4510031241a8100d42d50b4940c11954026445034050150560319009003d685c0c110311907401c2d00210200b039200701076204207982c0080e07036543c00d80c070030840b80300318092454154105542440745004110124001c0000741c00b91180040c0c48000310360340e138140005d01c000d84506034080c1d80210024018800705a0b0400d1003405181c1100a030104812603e050340005400d1141150343c8003860007501d0700c24032195400402d04140250028440b840e4844148040ea21452150a000403210002402001000d20040c41c50703200501d00030160201c180c0003c1d04481d039490f801c50f8203500c5802200108401844010070a0600b04c41c00c0c060201401e241f460340340d1112124600c541e50355091104504101c013450308080c41c000d0000c0b0341b1301000b201c550090000d0a10161003018030040001d00c401607144c2d4070313031192544141380242801820203210071600f078181c625602083e41e00281440b0b0740c1e40c5025041c8090030f0350050000a1034001444403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 222096196 1250 222094946 222094967
    0x90112140f0606011d010503131106070305091503070f08060118180c032d060306051e06040203071706010c05060903040918050a03120603050102040303051902010b010207060c0606080f0a03 83
    0xf2800c5c2c0c2004442a80e81c2000c16254000c41c04058401d0300d154515006050b071010039590380d4458030110741d4500b410b078010080c2c1500c3c5000d032410414040802041d14135800200c1e44800001c000071400300c080f5200d0b9008640014042c1000404003200c01316104a0140d55001441c01100e04191414150b60074007803a00001e0b8181030800c2304001c89200500c030540403018402031703400030100f10900d115130750740814011078000400300321034200055000c181405c44076450707206104240c003084140c03504d407003228060300891321161540c2c0340a40e18140c0c8820000c1c2098188003c3d0035019001ca1400d0001503c035100c84009140c0d21070400030020100c03400380101503401c00c00074441d280020000100b280400d9054107005404200305c503407820207051984c00092540d40049000010141c001d0302801c07d0b007116002d00801a07104d01000ca08031410b403444140164403600c01084500d0050410048460280101154440e1200300e00380c0f415450905002417941308090403000e05034811000313070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 222097446 1250 222096196 222096227
    0x40203190c120c050405090d0f030c051b01020706240602070302060f0f0d020414130e0601030b0c12090c0111060115082d15030705090112140f060601 66
    0x9245407900c6080000c0058015030108451560300c40c01448001900c1c5402400004d2092001d4a4042861525407000e40c068401050f600300001e030485009014100e500c40c13940e9101c60805040d00741409481482841c0f000442d5402c000d102c012a00c18000c28050b9000d4151465000305d207401c442c20b11101c240c0c024011900200010b200594410080b203500da070090700071640751030b908000640e0611a0f5a07032014010300c0020001103031400d89892544a10301107806588401c50384000c42c0c183c0310701780114041c0f60428401400005d024098140e0444203511080703040165600c0f0003004a082564681d5056100300740810041d039020f0001d49065200c100600b4465240902524080c1400a01c0350113004801c00082c200c050f000040c1110003a0507026410301c12450480034a0160003603c0381d100f44400f610900c1c081d4140000d40800b1140050603c0d049a0b00c0c08580750000821528111124951102100c01010041111840d03024284000d0013071800c1610001d810b4808020307444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 222098696 1250 222097446 222097483
    0x9290105060a0503130c080a05010501060207060519080408040f03060209101e08040201021c0503151009030206091801080f0606040b0109030809010c0c180e01060e0c070c08070905040203 82
    0x30a680c0d0300009132500090074100020b00040c5900d00108485019009940d031446055100422302030150807242c106e0b541a000d80d9441503e40307a0417540d43c405c25a0508003440041c00c400d0760075100341402076000307010b10040f505064450000c8804001c00c0c0d40141c500e940c001c40c4901c01841c01c8001d2880c030f910141409040f4001041506070750404182d040c1d0103101c0a18002419a40288038003905c40c180382c04000c00004041d00d000d0a40d070030540d40031a040c01c0c142d01e18103090900d4401400450401d0f142c043c0302500e15801c2025951040e0b50390b60704031030f0789680358010350000040303075018082d04001350454108140b421880d181000348120310131400c01d07407958180e0b40c1000960044d650000d40d01783c0e40d4096513005a40c0b080c0e270008001c011481c0380784000b556050400b1009149064420240440001400741074280c6100c2d009143d100a9440007251344601004010b00c000d622400c1e2042440340e44d84401410b2810b42da1140074815140c00030441185420301c02c002202c1c4420040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 222099946 1250 222098696 222098707
    0x170604090c03081b1603140d12020a050c03190f03060b09010309050a050a0b01060e0a0b030a0b03070e0a0519051006031e0504110a0b12040201120929010506 69
    0x210310000c0703610310015050b81c0c4001902c04c0051101c0b03030851010005101140c03446001c00c600c00b803200c0c1151000751038602d0b042d5104150b81a005c1030031602030362a0760b02c3d0003038840c000c0180402548160580d130107000d800c20080c403180c40133201505050007000b0060140014075080505024a01c0503c1c41c1014a0450b041c407403100407100740d07841c0384028070300000e8090300341c41c0861038140d901e400503081d407040e42d800c0e40c2007010500b0750724107076461035071000c8450501c0320910214100b01e00500c225060103000003481d014807940704c01032410005003150030b0180d41d40c2c480ae001003000e232002c0c014030b80c4941c1040003800f0385244649050b40c000c2c5003000a444c1c0340c01400c2060700c1c2c80c05407004054641900c428600320204201c40312801c048020001e174186445c0ca418a15104491107000340c49444000480000e00740a5440184180c03900741900c1d03549034011a003118400080e04809692108004082000c810300c400c4c101c0c1c4800c0c10950b20010b1a210304940e0303041644100d1003000308110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 222101196 1250 222099946 222099953
    0x506030d05041505070b0907061103070206040509090c0d030504060206100506091012180b1501140c032a1216060b030c040507080a060f14010c0302070f0617060409 72
    0xb154219020001c203002c803c0c2c40320b02e0841c0c481c45490710181c400c03c46d20050041c00a0007040c00301c103d4a86480d91144d810031241c030252240034110010b03601000c103010400850410917112580a44514244d5620100c0c5600040c030034142c0300d00035000158042002e0103429010450540c0181e24450302d004070b00d00e06000280c3c1446084a80c501070355080b080e0072491405003e011480001800c4180300602c3c1140c0602c610310043d1006a9842a50f42d02141c020a40c0311400701c2902c0381a03442c0c12072901040820001584011000c000c903210030041801034a1440076115800c0d0150f2440d440c40c2c2120403c118a401ca00c1c060701110702e0f80c1000890055507000e0079040129901500101f114100341c800a0701307200c98810103d0701b040c20402004152944564400e10402180c40d08000d0316850301000e0800c0e9945002d5903006500c017103000e02041d8010701c808042c0510900c1102d240c1e6880786410086500e56500040201e0021000301c0c0072001b05a420300c0d031204098a0400c400d0005e40c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 222102446 1250 222101196 222101207
    0x30301030b1501140406030207020415120b0414070e2d1b0d0609020a141602150d06150906020c09040303020913060f1a1804020310030c0305060a0506030d 68
    0xd010b54502044400503400d903074010b0201c02e109140e4082c100e6152659200050040d602000049100724a4241e492024a011170024010398881c3d0b6191405400d0310303901c0071200c2e10064405c2c0e0300203c2c1c40300903421034502003101d10090a00f2070402c811a09080c84074008145d03421816124207d904000360300440c02c007141107584010700b003c503401420300c0c00d11055003501c2200f0a001e50542421804540c80419800030300c0030071850385e11408800f400202481280c01540f44c940d180c0800d003400080585000002c268003111503580d00b5107003418115610080f60341980c40401003001400750058134940008186c80180074a0020349180c884210000d00d003a48020001000e140d40070038034880d15203480080c00041c0040c5042000185c1c1ca0304030080801700944170b0204060700f42d00880b094040e6200c04c0e200c41000303442c52403030520003040400001e0740005108a640280244001001c9203031644010005d40c0240c018043c2810b00081c804150b0341c00612031806503101494105109078040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 222103696 1250 222102446 222102451
    0x141e0118020118090e0c1516060207081209010f29090406061502100605100e01230720040501152706120b010219021203040306020a08010e09030301030b 67
    0x240f07009038803440800c120340b408440b81d0300444101c41c034040303011400d00000944020310300011913152040c9554041d403145a44a0242d40c0c6090b5000c3c043d130640050b2184c2c001c1c010842c0725020103820120f28445100841c1c60441d0302c2001a0344841000111b428603102d0748403d00e142001d444000c011416040004200100d611030258440b14005428050994440805014520b903111285c65010390000d598900055401c0c0845190150006061a000c5258940c01c8200c2e00d454001c4d010000041d55243c07980c1c1072504242c00402c03500c9d028040050000c004140c45500c9000841c44000d1081050043d4100250b005520301070062100c80d4a1000038623245100e481c0a0312020514180c000c41c10310004491070542e0f102c40d0020521300c1d003014500200103031103041001211105d400480c2c0d620900341e409003a00861090342c20240c06c0c1064000860826142202c0c6441c0d41e07079850001b2139200740d0f02040010740d083c0c010310003501e10b40e01e2140c000705244011411541591910907400001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 222104946 1250 222103696 222103699
    0xc1c03080f011505180a15020c0102070f0e0702150901090605100f0b03040f0210050c010c021b01030e07030b0c0c061b1b0c1003020c010f110906030402010c141e011802 74
    0x10030103004011069100505d5800054010701d201c0c1e80d1101a40c15941d11a10384030058000e00d40c04070b2955200091190444240a007180c119134649500c1035a003071070292069003180103444140707500605a40807140034001a9000080c464810b00300041190000b6000104034101d02c0d004100300300c40d0b0380810080d6110b01c801c2d1a500d440b00d03d4840d2200312440d80003074203c500c07007102601560700840036146100f2513500911140003207880490f1035948441c1c00c89004100d4408400070755200340d01032007074031904000f1140c00d65242c0e2240325411100301c80200304504001000c10804e00700748a180e40012071405d005400320500100b4803461300880b402c0034204c03078511122460307600c2c04010420728003801609400c1550021200103010354802c00c1d0071806582040f040c01d464180c503102d075192421040c0b0b641e50800c003280007000090340c80030388141d04112204e410f00c40456080441c54001a80090082c14040f0001140c840c1d0b900441c8109941a4540501720140c04004064031030348690 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 222106196 1250 222104946 222104957
    0x1401090b040e25020102030f15031c050c100b010207080d020604030305040215030a0906060611070510020705031c0806011d04090203030c0f06040c15090e07020c1c03080f0115 77
    0x20b8500c03c1c100001034050740c40503d0400d00f440358184a4040d4011402003c5040c0c020080fa500c2e6000c2c1521030100219454042d40320300ca074182011b000840c4000c0001c0e091402ca8a06440b07441c04610f4000030a400d000d01079907070850750200f0b42e01003010000a01980015150301d40c104040a9140c007030042029041c1910307400094110368031003000000c43c10000c444152a070a0201411009056031202240c02918200c00855100d0080c01c0100c00c06140a004145150800d0188074120101907043c0c400d43c0300d0160049503540d028060b13603007541505110004a01c0c0c100c1c00080500c0c402070f080c1414000300020203244580f540314201e030b40440656000c90280c20600c042860b41c85146450740081c02000c0010241e09804218140a54003540c0c03029807680d140c0c0801c01c071241881c1104004a1b0704581c0410004000b01001341d489885030040c1c5500010b000c001c03990524492441402540360307a00340c4010940c11200d01504030310120f01ca00300799810944040d15804a00700103400303000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 222107446 1250 222106196 222106201
    0x40c02280b040303020a03060806090a080d0905120a120209092a0d0b03010f0605030303180f06011203030c0201050601051b2a120d0804170d0c05041401090b040e 71
    0x455104044003159400300c1190414503090400034000c0d0070100610000905101001860000008445d80202d080c103010303156800b241d5039000010707070064441c00a020380300d00e1460040345c414005100980490307981180d892030120b80042a01101d8001720b403202e841031020814940b03036040c40a8bc0600d4801d08401c00540409441040e808043c030060744503c3d0014950070341440340c5d0000803600109a000340300c1c07a14503190705800d4820500545030994014070008840c2015001c40d50000b80c035040640d020521100c000301c0c10000300340c003ca510890160112010198980b040307002420b02c5100801040c103042000a0183c421703035141200346082011400109038090002045884083c6064280340414a204d00311180e03544055602c0b580038414100c004a001040720424015566112507090f541c1d90f03a012000c0742c403880c2c0c036143c100050002c0c40c041582e92085006030400c0c1e498040c8ca07186003001c1e414030312030030b401c1480c10405442000c1201c0b003900420348040d00d5010b680ca4401d603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 222108696 1250 222107446 222107503
    0x6090414011509200304260703030c0e120d201603020906150906131e0311010912110d08042c090d080705090406030c080c040c02 57
    0x15549030885081a51070019024890800060740c00129002d0010911414032444000d200c1042d0301900d1880c6410104001000560314103407240b418484144000c00261001c4854651a0007400c801c40119a030384840b0701e00c450300600b0441d10101c1c02c40b100e441c03081f01d410380e05480308036031003442052222041225403982a006000700761440501d08491105d0000031064541c00308900c41640601c100b0b601107840c0341425a0a4034808100f05d0955107004482024054a07600c49281c6c00038046000c0e5000c1110151500705004858811507500c800a0540c10310720040b402c12078120b03044c400c0c022001c00060b5005038909036083d41040411140fa840113000c20030074900c000000701800c800041c042034809180c241401c840d98550300c0c000c4003c10485120001a0040d10041801e5201010a0607400c3c4600c6455900070a5490042d04101000e400314080c1c803000c1d0800c45005c14906400c2c03029000c20440d45c9400c010454080c0505040880041c0d2100c40700c2c4d0015038005103a00704d50024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 222109946 1250 222108696 222108713
    0x6120b040608010e1606030b09070c240207060e0f120705211801030209010516051f090203010e0c0f100203070b07080708060d020a1404060b0a0c02190e060904 70
    0x40c48680001d00c11040040d04c0e8a8175828040740c2112203002120b00861414860f11803200080c0c0044c0203102243c85825090303c003503512080032209000c0c06148013130740c00b001e01c2c21074041561441015854440340d00d000400d803603d4400109459204005000d56660f0014203941003e4549520b0760390741034541416410f041c41c04c4034844800010301d91301051030b09864000c122440000c4000c0040c003880703000442c140d100c0c0110703440c0058018007920f0b4a0b40c000380c803900303102485041100c040441180140c1103c28842c031542806035904e0720780400354242070142e000000e24000143c080c4030001c000081665031295516400f9480311541aa6039900810072903400c0364000010303078550710781040300078500c0c2012159000000d030044081007107418820f0348080003d030f0041c10340f48100c0c1024861200d6521010000e81c0c0113440b5a00001d0801200005040100499962451030b42c828010f00c640d01d0080b201d0950520211001005840703039a00c0d516812190403500ca410f15191030a0441c030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 222111196 1250 222109946 222109949
    0x40603090c0503010e06091506010c030807030b150a17130807030903050f03030402150306090109050a1e02031501090e010510050708161407300503070c060e06030106120b0406 77
    0x2003545ca00b07102c0410308540010500d10400d4100211800300c04015078021404405035107a03030204240c00b07041c10000c1d010350f0545030b00082518001900c4c002170303400208183e080d01505440383d400040c2c890006c81e40309070308001808959211408038180f8001c5030011504450018021200109401c400c040c0b18203d00c3c4001e54024088589544d01d0510890301c03a441554100d11030381040e00204251104042941e11a200050001405070700e0100d125001c0c0100818003075000c0c0c0d9a14030b0f0740640c0e6902c0c03802801e106030f82d43c00589904e0005032207020240c0d850521b41c180100038000300710b40a80e8280c6241500ca0503035001e090b403081a4426201400b45403402040b0070804210281e690b0f4489140000441c045e0131140d0004015541007616940b4a000d15100422a4600a998920240c8101a919502e0340784510148030545a45045030003c060449034640140000c01043d5802482606074101c1110382c1440d552614102400b00101c201c0740d82c40c056280e0741082c145640c1e81d80682c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 222112446 1250 222111196 222111199
    0x110f1c0311120f010f030203060708091c081e1b0d090204020408010903020607050c0309010c020612040507090e0c0a143f033a110304050f0a020303040603090c05 71
    0x7034540c01c60b1000010315107000ca80d0300c000000d40400000d400e8401c01e0701041100d4010b40580710a40f910341c0112054100101104410722070380c040c450081341718220015400b189070703488040900b0115084120007210f001f0204a80e401103042c002c1c100e4483e40b4044280f00c00084242d50f0704917600a100141403140b40184d0703c0391010900056005064110b810200c1c03099083d1021a52004020b544501595001030307850381c01402034041030750040341c080308081e00040c582401c10402e150020340280f0101c034201c0d09038128a10030402c10320305000301401d685010000d031519600340b802062000c004c81c0714801c01603000c00c0d00d940454036010540d01e04507891640303850b40c0c9559442c01c01070042c4064403810900a44c014110300780344012095922030312060098001103410080c020803410b122448560041032254002e2a482c1c0742c1e40303e50490707020611402a12481c190403e01d050584023410140e2039080700300504010ba9000c001c8405490550800281d02c5103a424607074041d411681006 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 222113696 1250 222112446 222112481
    0x301020403080714061b0a0302040812131521021603020c1005030c0708070212030a0309150203090607110106050307030c03020405060607050a063306110f1c03 70
    0x4402d1042542c010710a25001d102c1d004951900110015500c4200319001103404411001046002000380d00500305600039207409820140c4800d8085d0800e401100c01501d0380000044e942c480d00740d00d180c40b00007402c0221303110504070352026020701407441c5454911104294809803190a600c150706903030100d000b80440c492689458500613544040380404103100d2300403104c200b486940704104aa110303034501c070034840c180310746907469115641100c142207038031429040c2044484481000980700f0300040755000300302e00d01e183c03d19140240d29400707100b280030300406c10001480b1f0001a029040900ca1910701440c94041c40c8150051107141c10880d410b0068070000014800c00c04020710589000711001c000549614042003070720f2062210042c1740360800b400c10030200e5050307402041c0d008200b0310042c000d14040c1104c0d0701380e142205030000381e0100404081c0001da501c48483c120b842c42c800700411b06144401d2406a0350400300d10360002114a40c9200484148250002c4c000706803110401d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 222114946 1250 222113696 222113699
    0x80a030503100b070c031b08070504020a030204120f020411030405030306091008010204030501050912190509042d0c08060d0809060705061321090519150c03021b0303190e03010204 79
    0x142418031800e1000781c7d400c020800d12056070080708120041212141c0c00180102807401061102a40040c440102456400e01c030004001603c141041c2c20741d03106012078200704195204020480340e08416004000300140704001c00108008200d98001e00c04803222803080e41c17281c0e503010502d4410742051100754004a0b002040110540025006054000c1070310103006034808032040b28040d500e0504214034280c030130804150301034001401c0c0340700040c00c08500240050054400c422420003443c4c440a0b141c003a0404018a0b031007070340c0c020000c1e85040082400c4c8200083c50046100101604020b0001074a1240307945540c22074140c203034040291041441c0080c1064441d45000750140c5035403c0180c10744110a440740c102d5404c01c2d40382e0315801c841ca818042030200704541600184404010154040340f0558004c0580c8144482c5170303600301040c02141380c0241000700800c044450060705e0310b00035440c0d80e000b02c16280701d28241b800f01005242c0740101110344e500c42c040b030143c255200140 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 222116196 1250 222114946 222114953
    0x3010f02070605010e06010c03080903090d030504030219030b150415080109050f030301030804090b0409060906060504180c0504050402180c0a0f02031801030f062d050604080a030503100b07 83
    0x41c014280c0501400c1100d0303030b41c6200c0c2c54040b540841d071107170000391b956121000203800b4000c010740210300c860480703041010f003201252400f6140341c010b902044d00441c00f04114071380302c0b00c4880c4460600c04c50f207200e64039559800703040c0e03040588840800001280001c0e4251140d50080020410000c40c0001540d03031144014000d01c280a406da40700e0007030500d05c0495800000489041f40c3c0d0260485260a107010380b0440144608460544d0058640c008400869600c1c02906c20b600d0040000089251500c010402204c030420384100300a42035010040c007269080442ca0100c500039100440c29984600c0020b01e4940302d40900d440d000d40070004d0113060340000026014483e0b680d2a10610750504100c03d030390324010102d501074031020000ba1004154800d41122080342680200411402d4403482c0302107403008403000140c0030041d0200c254030306600501c1c200c4028401520698642070510540c82e23147d94410340041e042c810000045402640903800345002085881c06103a00e0741030030f18 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 222117446 1250 222116196 222116201
    0x1b01140702090f0a0501060c0809150408060a1a030c09011404020705031306020c0607020904022112070c0e0103080703111203070203090f100f0c08040f0f1d150d050a0203010f 77
    0x65003c4c0c0c44034139207400464202c1c052802d9041c00d60b0003440180c10200b0000802c590f1039050031030003070006420f00c8001000e03901003028a005201c0c0d80380101e08100c0007656854040540b00485100380c4c0404410560798032005001410f641c01600301e416210006408100603100d40e120041c400d103c0000d102d078071183c0443c42c3e07400b0f03a0080c0e070a03aa820401d000800c5024003940c00e0107544843c407080846e0052508c5a4016552803444d001b0225001c40d9505803400c0c4035100c500c4c07649002c8001400f03401c0107080403145001d0b04040c52400c05950441c0c8a801c402d02881e000203007405807403801e0182c629170070045481c0c0d051021144d965280b4281c00c1c000d4807900020340d06070090040e00003501d81483c040510600020f110b036240705000c07091000858145040e02e0040c0c4101408101c0415001103510100c8042c0a800d030180c14a545805c0c1994161a92036481ca040c2c9680c010501a0703c2405507029855880111142c0300c4016440c14102d04041a00e000250700d5864a08850b103008601d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 222118696 1250 222117446 222117451
    0x3080a0504030308130c0e06010309081308250b0f0702060f0d0b151e040305070605030108060a020306030303060d06230901060e040f0b10120501021b1b01140702090f 73
    0x9584d41d0041d80c071340313a81910005185900051200e2054041803100342407000310301d070340040d0502d00030030f400c003c40c0c4860885034020781561040c00300d080428400b290302000304291704481e400c1806907114400c607404481307007024000e914030020001081c901c0c0ca82e22209541c982d0750003d0504e40c5e21003e41184400e6a031003100c0303000007141860060384251078010240c824150651403a107161815811011000000d11300303030f2140d1078030300380000701c0418070070001c8401a18040e10b62580c2d07541405003080c504000100340004072401001003040c0c2d5100841901d410000036224499081102d1500310017604102a1441108500c0892040d19165401c4450b000d00c00320402041010303125904240d052900710b4000c0c1c045140c00d00c1e2100081c888180e015800111880c3d03e4604503140c00301d40741c4c0a421080c00351080e80d004680050b141210783c1e20f1132402c422210051200f01c410a000302c6e5990070035480c0303505004800281144554035a1b04a40090b903000f8141c01403480e10800595190388103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 222119946 1250 222118696 222118703
    0x10207031203061502010e3715050c04080c01140408030309060109231504021902010c1701120b04080c010204030302010f0e0304180c020c0d06050a051b0d0f020403080a050403 77
    0x13208200305030a8018410003c890b0645c20150007a8200d41c0c00c00791030085640c070300c0700d40100c0c0f045030080e202410030f4400c00c00714411035207286480c000c6000d20782610005082c241c50000100000c20045200252a182d010800e0030700e000e07400d840901d0504070303000c1c5611540c02030000000b001f003150300114241e8180e401d0340200708200c40350011216402d071000d50000b01c42d4175000000c1060003030002d038083d0000b10003c0000d841d0502d204106512814442e0005015130b4662003814204e503001041d11400c0204559210f40c01e40c0741c01c900d13420b050311b40f1002802c1ca0031008085000c2c00101011601c00000000080d9500c5d552850003e00809070a0b600420652070f10f10841e0400307001004940848410414001c8000704400c3c003040100007045417a000c5d4400c4030549540f5884007403503000c040e4000d0100003050b18100030b080f401d407580108208101d404403030369982c0b404031581c252241002001c0c0c0000340001c2c1050740c14024031490f080075002e1031000c40d008500c140c0c850700a0095078030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 222121196 1250 222119946 222119969
    0x60c0c0309080615060c0316050607081b0f0d0e0111130915051e04111206011416240603030207090905030d020c0a0b1005040608120d0b01020703120306 67
    0x16240109a00c90f042910144506a00b004034504145003042c05050100c5480f01507038909004217801c03807121243c0000840d241c1d000141003180b81500850340a50100700d40e10301c04140f10398000c1000c2548a0018010740d8900081030000d2035805a51103040c070741601000030010030100c0301da50750681d0005d07141c14100407110080460300340d40601901a0f119070301180342d244c0501f01010070510b40c4815180b400416617600741d5899aa0b11b6004085050500c0d1440541d25600000340310180f100040800e0b062081181040040742c502c2c60440352846c46000c0b1240d18041c1d54604026515110345000c04a00c209540f250f00046040c0d01c05411207100e50222800941d9507001c80c4140d42c40c071031000e8002d400500449110003200e0300100b103014400360070380315105554ac4d43c10240c1081038600301140031000000f840f06040511488014141e20b0300101106858400e00280506c0754009da000900e8403001c1c00c0c000b69008025403400340d81d1200c184103080a000303a00500501c41c51190941020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 222122302 1106 222121196 222121199
    0x30601210c0902040603060503010b0109031122020310081504081305030607030b0906061204060b04020f072a080d0f120f0902031605091501030207060c0c0309 70
    0x31520b08016101c5080c02c4008084a07500c2e004540642e16107036100807260b070064000d20460b90710020041c40701040e00d002c107828a0150b0000c026400a0412400780154aa0055445120901e0170360700745560f10281e8917a80c03564013400c0514040d4880124012414560060800076118100744182c280c0d6040482d2902c20300310740e04000250b071000d0000361884c00394411600b00b00c046442905080710003003d501a0f5030301810003403815648580a880584451b0159445c0c1c91106040c82c2e00d03040c440c1401501c4035801c5007151f080c241c0307616800c0c000d0320340c0c0e80179041998030748402481c01d035600c00819284130650640c60018015030041800d028040b40c0208200d04084020208a40040d0320500d0b03d080c1408800c4840d00c21380d40b80601c034076110400e86a40c021001f049090f410504840140c1c028400d01001a2242d418040843c40d0aa04031140d204d400e0b01c00c0d9288004903 = true := by decide +kernel

theorem cover : BRFrame.Cov 221942446 222122302 := by
  have h0 := BRFrame.cov_init 221942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 221942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 221942446 ≤ n) (h2 : n < 222122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
