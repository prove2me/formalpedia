-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1285
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:10:12.476235+00:00
-- url     : https://prove2.me/submissions/10ea006d-00d1-451f-822c-ffb322d562ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 230935251 ≤ n < 231115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 230936501 1250 230935251 230935261
    0x40302061803030f0a02060f0708090607050c030708040909061406030a03080414010606020304061101050c0304020618130f050c09010c020d0309050d080408010e0f0c360105030706031103 82
    0x1810301105960746406000600440881c41055070280401c001c1c01e4000e0100c0b03152040b04002c50084c010695800d0046807410700c00410300004009601c845c1e01e062881e514049907007414598041c00c00000d0425000190100b1070800580098640e00d124000c00c2c04a0150310008194038141200c6c40c2d80c1540c812914840442c0c070600c0e100e80c00502880403039402e0f54504006d2400c1d071741650069405a4400582040040e40c00100c00e11403256030380080101d03060071542c5041911010704040c2c46160040750320100c40070309041c0c0d405a40c500400c11207060b4241400b80307000e000d0b80b50380411614035000004009401e481c0440b442c940f0140e450320b600c40d03242d80c02c100382c510504c002034040094081c4042115120415400c1d0114001c0c01401d4503030b071030015103070b0a550b5000392440d02600000c0c07050103601400503418034403a1041f60320720f1003280003404030744808201c24900c6290905011425101503c01010541070700c0c01501581c0803d92201d609034261074a06140402c3c80400f000061 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 230937751 1250 230936501 230936527
    0xf1502010c11281704170703030e0f060c070e1807140418050a20030c131e09060b03070803030f0133080f070c030203030a0b0604170f07050604030206 66
    0x24110f07011601048918030a56150400c102d00580b10314412004001400d10503101a4038210346500c4400004000160540c0d900404040307001c0550b6024090882070356040e0307554202590f000c1009441160122079584650301d0b0b8a1800340c51007844601c1502c560740c10642d000c14000c2c20f0310401c000300b40d001035000090000030304800c2058880c04800c0341e2080300064040c001a088540100425201c510303500203841b000e04640c4c00700c1c0e4030981c0499541404c0b0b46604407170070b98005910400003030b0504500804502d0344c480c0300d00007205c14030b446007480c1004910760110402c40e41c203030b0454040e55142c1d0162503480c4000e0b101121901c0c203107001006058000f40400b5903500c1032611022010009014013160f810b0000100303008512140701b00801007560041c2190310502c240740207102900c50b514003039102c3c480944500701172521114100e01c01c2c0c039180704807402003207080500002d00d812013074a81d456210707903281101940500040028035180c4030341a90252074000304458a080d61a01000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 230939001 1250 230937751 230937793
    0x1b14090d0303060b040b0a200607030e0f07121406071d031f021e030c070609140f0a060b030105160305040201020a0b0109020903010b03011112100f1502010c11 70
    0x1c07401c243c2c0b0fa01012a13081002c001501c0109100ca8815856020824018101100f000c0b036000c54000d0070760000003600c500090f5a0b0f003004680c2000144240080c60403800c201d41ca4903c0015807145140004414a40c05401090a0301526028a0072000d48113122b031907038070941c1d28a0008035100001c2642280101040080700802001c4400b410b481c0d108280c000807074800342c882440d030302158180d410385401c20820035401810b446a4034510300710045124a0040260140100d42c0d2030110358104000d8005001014102008490b8503200390b29a06607100c4030140e08031072302401c15518420f02c0c00c5c1401164002c2502c00110010303e0000c19040b030082400a2050741144510345040020552500b00399003c0c10f203207440569640c049000340750071760780308800644c0aa8940050708951100c0e40c01a070701c10b035028058202d040d0700c039600741a03098080c9800c602c0070600c1c822000500e44003841181100516160000e0140028240d0182d850300a900c1c00715540e0380010404508088100f00c1e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 230940251 1250 230939001 230939003
    0x3006010528080114100206180709050a0c2703020409030e1201020d1103060901090207080d0e0c0418030c14070909050c03010605120c040507030f0f1b14090d 69
    0x46403041890290070711140c8081c0a0340404281404010300c003110380e0f040200102c0303e007a80c84a1040d062018020b545100081070054500000002c1181400f4140010001810350300c0c000c1c009230800c000864010064039018030085074003124140d43c1504180c00394041c1d5400200003004040c0740d9024803014107000c2400f1010072110301a07201407940c0d0b400c0316910010785900016140c0b800c6503903840c1201c0590400c01c103009014002c00c64103030b940460403819a02d101c54090b80b15800d91400c1c1030680188041c003854241402500802902c00058506510804480034090b02c2c000e45050640c4601464014001407809540e00c2c2c04101101c0d00c074070303035015418211075039960760324200c2084600518044038250040c00c000000c1d407034240611070203404201d4a5848042491441c10303a51584181101e01550f2100c001680550295004001e2501451404d00001b440b03245030000420341904200d011000c1038509200c501c0c070a444151305074190000c01c0b46411140c000b0406e80310360300c40d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 230941501 1250 230940251 230940277
    0x90c0f150d18050a0c0602010e030f0d1a130203040506072c010216030605011d011212020a060f050402011d0607110607080a1d030102070308041211010e0330060105 72
    0x310010000c0c80c04c11a000c00c503401814200300e5981400c0f00203082d5910800585450381c02440500c4198030540200d5074002c1080d00c0014180000c1041c181d2000c4000040c1581b00010100c0c7d03205040080c1c006500c113500c41ca050b0f80040d41d0342c031015100300a08191074641400c0a4800c90f05c3c00718601d01c102c080344c00500445104a4040c2099000804140c100b180c2540d2030740010850740d0a041c0c50002c5c90842849544541e41c18642d080c444007514400c05441410007400c01001e090082c800116040d4001c0c20078000301c180305500070050a0151412030004d1300c8504442c290440c030000c41200c0a2008040701c2c03032715100d9216468003007811280b10385d000c2d804105400c001021100203010107440791710346881c003081414450100e6020644500e002e64010010280001d0f4040141c2e98020340c0a482c07541103a2031100c085030322040141080750b644d0700c0c0090446d072104000001c0c01e030000c41064440c088400d00c11122480065460319030150380a1800441c0d03566001d0790150502d404596 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 230942751 1250 230941501 230941541
    0x315040b0303030108030c07050a03080a120b03010203161701031e03030b0306041a0c030402030d1431050103091a0c1204230a05070605030c040b03090c0f150d 70
    0x40d0020382954802c0c1d200804682c8001181071140100780103010003070800700c4007485424510740b608001da1207441403100821500700c64105010109502c40c060031100580215103e180681c41c84021101410011011030b143da00104904811907001c241680d900070002849205a044542c12922a251003101071680b2134901e020203442c00c1100e80d101d1805811001c200161348602185a00f030080d00094800001b00200300140e14005075050b90042d0b40d241464111554400014007401110b0240c41013074400301984080e841800803903104a40152501c400160303962005404882e1010b000030080300780841c6c00380c00c914410307905a600c800480c5040c1c0c9070541029002c030b0910402c0300c0c00ca903140100c4a108990720280c0c11811040c40044004010b00c0c2003d8075095901e01051081078104000000040c0104408509070303401010310341d4110780c42e404c00d20ba221307845100f0028518000c440201c1c000c2a20b06c0c04501c078815210700002c40b20314000340c4540c410060402c41400e82c450100032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 230944001 1250 230942751 230942771
    0x50a0207050306040c03060b101b02043206040939030606031505070206180c0604030b0f130b1501091d0708091c080402130c0206100501080c031504 65
    0xf440301500c1039100c0e021700481c0380c0c254601001140da911100c0ca0050301c004022031031240e0081103000ca1800d942410140c03c0c0041d02c001b0300039085842c60712240800001e00c585010090301800100f10f80c525443d0b0580d5510102400120351032442e01801d51030ba80c001c40e80c14103824100c4480c0998075010300901d00e445e2031101c0d000760b8003a0761080710304c0d554810782001400f40819608c4810544140c0511240c103014000942c7c50038041c105988080c0701d1a107403c10b10b0001c002085170039030041e04641c0c980d03aa906060014000403169400a66001760001e002c0c0030801401502180d80040c004529171034103440807000c030000104071410b000d01c0d0b031008128142500c0302541c02120300000c1c61010f103440301008040c100c01a21101d040d500001240c2082801180e0214074401c039807411180c2c40d6164000a98900013681c000c42c40301e071801c0704252850b41c0c04104548202c08502003016859a0342004440281080364040d601800a00c0440e05910b00711240d40000b0398000e0000c074440a803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 230945251 1250 230944001 230944003
    0xc0305040311060c0f0d061a120f010b040e180d0c0201030b1002060106080a0e10060503160305031801120501030309030309080615040504031e0e040b0a050f09071b0b0103020111030c0a03050a02070503 88
    0x23200b00c0d46088440490b03920030081e05080e440794091000d100081d100d5142c41d04070b825a00446c0100c110104903a0000750311403914400c4a400710b000c1c4401c44405103070280f001b81c40c0c02c2c0e500001781d00090074035104c017845007814039204164601660051045e40e18050048900c0c80f8050413171f809807a221100d409021104101041c62481030385000258240f41804041c031b0401402c00000d02d0703a000c2e002c2000803803408000c0d030301c0c4403140500c2400141ca84500407141c244030205d001c40107074179010012090540c01109007095074402d84641401c1c640300c0044035950380307048418440085080707400c101c150800390400da411a100e410301c0c3c2d003150304212518030301d075101e02c079400c00107a00d980340c6804604d000d0059990a0805981c4000c0560400b40410f410720640300801d40513400140c0801c10651180100c2c0c2018040c401341c034034046041e81b52103000018284400d0b4000740e80d030180209039010210841c1c0c0400125401401d02100903078085c0e489070402c1049605500584a000985881c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 230946501 1250 230945251 230945279
    0x6091c0b0109020d050a0e0703020405100e010b0d0e031903090f051b0307060906020c100c020603040c050f01051219021b0609072111130c0305040311060c0f0d06 71
    0x441030030150f01c032541303202250200c9400030205440c403030801356005032594021619605880e015600031407955503424070a50a814607030311620302e07002c1c204000a1f40800c10005440f00b401c0c031400503c013100301d05c904641e0360300443c0703a8050030301413290514107200c1c040c1d40010b90161084e4100401d40003039071150f90a00c11a01c03401486149030b0320800d1030610382848150003411203401c3c440c0020341007800080d41ca1032020b1446008001340e80e070f42c11a95005074080c4002550082c100c40c2c0ea480c1034981603508002d00d1084034020522021958100d6004200f40c0380c000186180c070481981c1c90203260040d1a070b00c0e8040c503074442c1c3e08101400f8a410208194070388080340d00d00800c06800c240d29004d162844991100700c00940c0414a40309060480d43c80800c02504072540c000607183d05d10000b0b0343d051281c02c2032030581c0c0c50000ea448416030507400c0907201d01c6c0203868803400c101c08180c0c8580c40345e10072980c0f2114128108003800340910100c024003c10001090001001d40c0c0b40c81d514070800e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 230947751 1250 230946501 230946509
    0x604120314070506090106050102030309120f0417030703080a02040e06040f0b090108070e0903041508180109030309290a020a05040f080307021e0d030c060902030105012409030206091c0b01 83
    0xb410020400c185c4520900800b00201401c0c4000d44c035525200d182140c6604a6080c101e81c02680006d160700300e9605802a03030050141620203078294070034280c026a481d40311140480105040d01c0005100d11b809209440031206104210107407aa207440410008200070580c011160340e8520800d03256444813040310740a0000c00c00103114031400d02e210319a440b28020901c07081640304000900103a8079044080c00307000b18500305140c0c01d032503560080c40080702070031001c18558600000d01d0103240c2d154202c0356415001d4441d03039040c80300220810000051000d6800442c0300c244000c2510f882c0c281d030041c01010640c0c6400e600b09170f03d0311200d103003000b525408180c150b40045400b0081d440c2082050603007450214806d010001c014000c580200309031400901841540c04c000c005002c2e1582200343c1066009000300100e41c1c4030424a000c40c0c1080070700c0640c0d00b0100d6010420280921500f0b0150ba070000c00d00d504005840c01000395505030140051002e05800c00a4000602e19407a003d01030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 230949001 1250 230947751 230947753
    0x50910121424061305040506030709050c040905061f080a1805060603060601020a0b0c0a03060306020d05160f0c025407170403110a05010608060c0906041203140705 72
    0x8000c0c151000040342c02102062140c0d4040000034692051030070600d084900075540030505584001c00641420380c01c5d8003100000e41004100a507a1180c04020420b48060000400c07180c0c0366001406241035806203480c03600d440e40400700c24554090400c0940c410385104011811407554110703000030208040c1c4c01c4415510090901c0494502070104540c07246080c1700800203194192902100b1030300c064000200d82c2d0700055a480c0080c82600043d02035508240c09540e01c5014221800042c0b07411924091410010362800340f9080c8204603102c140603160342c61201c80949074007000344484006d64241007040082c205030350306540c801e6805400f01803aa10012048030ba00300003c0c40e152240c4926403030002207504000045400072021200346080441c014003a65480c84c054440c19a00f00d005183ca100b2143c030401000310541011007581c20746401c1e02c02c543c440c201e940300f8038002c90b01e038079034460003d01082c0000072a00c01803000e60360080c81c1c44002d04440305400c15080c3d00c404c2003602c031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 230950251 1250 230949001 230949031
    0x1e1306030e060f040807080306030a0605070c02090603071a030a06050d05030a14030c400503010e0706051903060b12011401080403020d0c02030a050304090603050d0509101214 77
    0x5007150038410998003004000c03e81c609454207a03140c00301441911030003020044080040356403034404000c0f013584264810305c200f10600740f5100103002490042d0b02244164121030001d002410003154010448210303400c140921200030032541070940005100840c1159151030014595984000c100e056a000c2c03005541e50310b0101030020255025103480c0000c1c5c6408000340002032010303038100c404400c295050348aa442e01e080922200071407012003410b10a021441521180e581040c10100f11035048008200004200d82510346604e410302c0380b240070bd4424000a82e502200c00e11942c00c0c9451440c00240d1a600c500b6170b0070458001003a6540c506180b80010700840c03008007500600c040302400d0801b0903150940d13000f55910310740358820301040603011350340d07007192410410441100d41c04020b90341c0302c503180d401074401081c9520043ea0359124600d2103d60541c0214102c43c3e2808010b002901300c2074007010180d50601091001c038401e5a59002e011101c403903d540d038640900c0d608400684 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 230951501 1250 230950251 230950271
    0x30b0306090a0b0a02070609051e010b011115040c030b0a0203060f0117060f03070504020304120e180103020910080a0c0f06030c08060907020307050d02060105040507090b1e130603 79
    0x11034010010070400c19580074120a101080f82d0300d05140e4006007907200540d0b107680c1c920b445c101912000100829611401141890302d00344002010142c2101000030403240f0074010045406100303009408070150404071422100c0080620311641c000d000b00c03100000942c1e25519001401011100300020307941c08010b100b02440c00c91441d40341014246003134480015107050042903520040c05c000d10400c8042d00702402d0391401d02400c1e00509005108540724501420f1030300346c803a0881c8042000810b030b00d6529a0030b01e40341c0c001c40c020f8207c050354186242c2c01c40d400e104910707001408c004404910703800002001b0780108651010035200384280b0003c10300c1c2c40c4922104181c0c94000e20306160501d038154845a6101e00ca513584400201d90084181c0c89040e001d07411482101d4000d0228090141d44030040d50b00002c066040b22020b0383e0030025690313500303002c40d8416510f004410145404101d109190a003041d9240e900c1c09840d01010702c0c241401400081106065000b14003290712180c40304 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 230952751 1250 230951501 230951503
    0xf040e19210806040c120c020610051207090c05070c03030f021501060f0e0d0c0e0f0106020606060a0f0e03100c03110403080f070302010f050a05061c030822080a030b03 74
    0x40d001c2055040104248007034400041d001140060043c0e001d681d80c3c8505007012480303207055a21094404108000120080700000d480300411900c2c2d00c107004a5540000701c90600e00e0059078401c03218005405020304102c115030180884480c1042000424454680856003490010005512a0b03d40d0003c0c01c0e01003001031b082c640085070680844841c0c40041240b80c1e04035108611000cac2d141783c0240780074446000258000700054000d40103451008002c1000b10110f00c250780205081721658000340c1e44c1d0602242da5540c100e40c07098000300e080c00b0740d111040c000c1c503c0d46280c2c3d2546c1031001542000d0310120745402400042d0546041d00d0b520940e41e6183c00d071080d0703401c41844090b2217203024210340ba5013120348555140702107100c1c0002070483c10315100303611140c4440f11896060169083c220301d0f103000703000107555840c4520680c000e600c1040108107a480610b560640b80c00c040c654a45030444048042e015620200308104103003100000d4000c8000d2144890a031400159212032034285 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 230954001 1250 230952751 230952773
    0x20402030f0132060d020d020406200304030c050616060f0f1d03070813080708010605040e06040c0e15060f031006020a030816090801021204020f0f0f0f040e19 70
    0x1111203860865010f943c9440d142c40c00401401040e164aa512030404030f140c0024070455520088445c40424042405a80900782401c40d6162081c0a040c6e800044100c5803203105910008181c07a003441001c02c0641415006031141400c1004006400e41e0b0f2034540341d0540310901c0e141a0610703035405658101100c0c4c1d1107114074550a454041030646505280c00e5600c0c891240c0181100713001041e9240c00c0c0d813100c2c00340c4000e01034100070f4520b06aa11001d060182c811405810700c0380c0d04202401c0d8808000054040c07140381c0181003080464500b1005298008002d84040d800242c040480c20464850000910001444006040d0b8900d08800003010900454001e501107410044c000030202e5880100c40c1d400a05542869010710040c0e0816188002a9440203603c5d5001041c0660007406410415100358000d441000140c030742d200030070030401411824250311190407d0075600c3c504140440d0081c40c00e010307000140c0411040407007403518040d0030403a055980e00d40b40f60f00800c2100290 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 230955251 1250 230954001 230954039
    0x30204060b0705100506041d0a03031b080403140d0c0c140a05030304060b0f10110d0906230d0603050303011502190b070c140f061308090616020402030f01 68
    0x3189040c5036190b91202c0d11348229410002e000e07511007010a40f00c0d502c41e80400e04002c000350205500c03a81d40c2c00711589a1840020540c08240b800444a042e89020741c0100807000290341d64620a540e03542d82510084a10410b04080c400c0c24404546078400602c40d440542c00e00751a410010403043ca410305602070100920000350b000620a14009000041960341140d4001008500c5d840c0700d00100b0030011482c0340907603011030140c024944c0140c000d49440c03003080040e0140d030070001d00444203035048100c0d485642c00089030146107440b6a00f80450b0110b0310544007400350724010810302c00c10103403040c641003500d00350000401000b5011601e00c90280f00300d000d0016040448645601c101d08a01d0010098545030b949400a95032600c00d40c03500006590145481507502d0f020504a030f551821071038a183c1c42c2c814003001c220000c82d50a205030071a5030042405103029603a20901101b50481040c010082c0603400319107006948e40c0c0055071042400140c4070100790714120100801002c0350003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 230956501 1250 230955251 230955269
    0x80c0a090b06040b18032b0905030c010309050c0607080c06070801050915011b08090a0e01081b120304090903030501050603100b031b2206110c10030e0f0703020406 72
    0x3a501030301c2c1d1900b2040d20200e4000e40c00301a12038013200311000800d1308007030115034940200c07140411206841c141941108410100045080345100c50071b96050100c2e000c1e0701c4e03142c0d010071065401580309410107000144600142e5010b8007542c80890f056400590b0308841460021807100c401c8101000b0803588500f003864420055403505010661010024144500040841148043c580d000b4081544661100224110b000750b03941000002074000055040c806d220070a000902d4000150030b15060310505000340018400c103200c9400c54080d500d441c290030001c43e44c000710320f041c07083c4081c20052440b030f080421000144d01e0300408540058100e94407400301070060208120340e2608030400c2c0c60a0b04855903407602e4088011140212001034034105440000703800d824000d40f20628554803107404d80c444420743c0c50b000706076254400d045038000b0355403040b16130f02c00030318000c040d800b0500e1301c0741000291000640c0d84c0c02c5c1410600c10540b525a80120002c104504061007004000c0034510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 230957751 1250 230956501 230956511
    0x321010e16080403140f16110402041d1806090616031a0d060f021b0d170a180b0f0601120c0f0302032d04110603060127030606080c0a09 60
    0x104000c2d0031000c010384043d0802c000125038900307041c0c0741d000300c0d2a40f01c000d400b460340320345401c126448a43e2080c00202c88201400c00d0600d0507041c20b000b43c900f92800c040d149091a031803034040d5540320f031004000d420804084000e181d603049081c0b0030720f80a643c10354050724103450a0650b490211034144c00d070500301850b15425003028240700302e5060544808507900d01c0c11800030700700003025018101c3e16000052000442c02603080381c1e42104552010b40b80156503100c22103280642c0c003804201061854020220000b5042d0203582d0b00c2012102a101c988401c2141a40c41d48804044c04035414400e003004e020034400d5540e048a1000c500c1d0041107028804400342d404002c0429182c0c1c600e500a054022011541c4175204a0f0841130120040160ba05a20b024035840b1494a90070b40f030940d11070102c03980111043c104082102c0c800e40045e112043c401ca880c00904c0e170400340c810949a16803418100101c0050580e001d220000d280680042105140c104100111141c0581c000e0030014600 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 230959001 1250 230957751 230957791
    0x61a0a03051b0d020a030e01020a02010b03060903042105011e021b06010302101b06020708030403090b130b030c19031b03020c07060309050304031e060f1a060c0321010e 74
    0xc004440c81042000b002684814035505c1c250081d002090300048103500100c0ca15240d6681540300f10011041201150380301e81b00c0e10030355a1244034601410054070899030f07606800404001410703040398852030000400d200624600c0e0464002d0700c254850182d00040e1545030b00c0045080042c420503801c000d42219491a4002044507a4994400302071000303001c02143d1488245c00a80010b41d0405800d5641d54010f241c241d0440d40216001c0300843d60000020401c10300c0002900d00340d00889400f803c1107800d007a45244590030041043c50700b008200000c1c641542d04050714010b100b07880e180480c690742c848030080c0c0c2600140300908101403051004c0440414002030030022070f04c1500303000620f408141000c0d0300311300c0b40f40c001800d0012241f64841508003206081c1ea8403501413403040144000d22030440054a2403034140780c0b803c45001000303080b05d181c050f0003010614040c404580c500362030152205059081500c90444060070100100f00f4070040050860748584103003401d00b120106 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 230960251 1250 230959001 230959051
    0x90106020c1f020a0c030b0703060f03030504060e2206030303050a090f060b030715020601060f0507020306061018030809180f011208071e062a050904061a0a0305 71
    0x71181070b145030440c10484800b4040c024410240466000030004603c2901c034244450449000c3d1900e00000349030400c0051549450313842c3c0001e07690725584051400c0c0c6045030449610410740422907000a0080311511201c0c0c007175000b000006140400407a240d4603608018044a07401003403644200d05041c503030700c0007411505001c14a5035101c0c0300080d9440308400441d01c1c03c0b8554120540c19210100c0301411142c0004000d0704a50303055481c44803090036440e003101c240c002e82e04000d40503800400411030501c0c0400c001d040d090050f1400f511524401a07291780c09036000c1d442a0740f02580025a0240b43c100800e2094120000c9200032805083c0502c402c2900c0d40144134440900d50415414020015140100c4050907040030348a22200750940d003180c800c20721410f00f210307003174502402102c00848d20628040ca9018000d1408030050401009485952100b5003642c0c3c025540e4030003081c4001a0859449444010f1440c0303501c407480f03484044c0481d00c0140007080304c0c4074407000742d0310707400c1d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 230961501 1250 230960251 230960269
    0x6020f010e01360f050615010f080a050a150b25080909130203030d23070207150e04020a4109040912050a0f0302040f050d0503040801020f0306090106020c 68
    0x1641030841c1d104040944004090408010001464900305030b0445003407040c0006d805014000e4884102e21203400540152034041c4032030500f802146000001965072402c1d0703484180e00170031040c4049000300740c040002d910159070760400c0026580100c0d01d0700408461048248403d071200040c02c011640360388805810340502100349219103140300c0000c507140203000c2c1110b51154080c0450361950b000050030b10107403510180340524056140e01d41034988000d40c2c003c42c0540741540280855a00301002c040d54004041c41c06c01c1400002c1c6440394160b2102c0c030007032820300c2c460740d02d481d414214010801080246414400c94140c0801d46002d05409a08039600340301c00c0b8410a02d80c1c03855004046800b0b403841c000040e04900c1c17801014901190010000c014145c059030f201c0d0781c2040300810603030490042e40941a041c0501030024021400c0142c00b030303100c2c24051021a0b043c030303540312180e609a034040801e010401101005000d40b605104002c4c03409407140e400940440c882030000304484003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 230962751 1250 230961501 230961551
    0x1015080a080d18170703031a010e0f01020309030709050a050709030c0608180a0303090303180c0308030a020c0f0304030213060b0702040b06041505120906040305040e09010f050106020f010e01 84
    0x26564509083c0c024882c0c140b0481819480883d80010091140d0322410035004904160040fa08040642c000001c8050704a004540c05071280900c518041c418800c408175046042810741c07004226280086e0340401c031000051030f08030004601890143c804406a40000e40380c030017072201411007800001c1c0a96200c0040d2442403400705056035030820041c0c0929040000e80c0124018881c0c1c601c14140c1c1a041900114060348052240c403161410030514010005009001840c052005100190880700203580140740690050304054046040a00b042d21600d00c0080b25440010308000310b050623624000e90000084013040340c41d103040041c5815101302000244a99954074810b090707661500240e4000e03001c0e001c5030040111444801624603800041680352400004000a9500c00c0c0010307454426a456030711642080d1070090446842d80380a80451001c0d521440c900550329010b118490007809198020301020300100065401c50b2490150b5907a180d041c840f45214049150750070740105 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 230964001 1250 230962751 230962777
    0x501080f150406030b2712183012160303060305100f110406050703080703090501090b072007060e0a05090406021201060806130902010e031015080a08 66
    0x19a5280361094440c011408910382c85807411002000380704010108602c210500c5008038229000e554003054000541d202d509402d600a0703079860103451200300a407000c890a449040410380520001800525049105000d50f51141030142a41014610b5050110741c0c2080602074408042565506520035030300388228042002c1080c01c10075100368001e400641d0000196181c4554484084010705050311403510007505028103c012106004125000c4070300319144d50f860589030780e0301581c076047c00030f108100707142d658650040070410a0188808403403040d01c28062a01d006407001d0031440f0201c0d8110346076160480b801da540000020034000366511410950039080404001809400150f00030a4011080b40148400c05c4039640140202100e0035540100f00c5c0e0b210b034000c0700c0180f421a400f6501c0049950403074071060455111280035401850540c40c00745025021a14120003c0d210040311a03540140c20a03440003809032502804602000c0c080d03407580c039201d00540d805000103440356 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 230965251 1250 230964001 230964031
    0x70302030a08150a060f091406042c070906110c09041509060f060f05090f0718030821090d02031b0c030d030209030c010302030103150b042306150301050108 69
    0x83d1540d0500741e20580c0d0002c0001d0106500c0c0d4030024504680950031b440440c2640501088210101698203a40c2c4000340246007040d03e03080140c1084854011400c2c5074401c0002c0300c0000c680c1414100d441380c0701d80c2d2684000940391490040c030740ea80c0d41f4042c0340d403a000120702c007484e0350310076094a8006802281140031281154440707001441c250b42c00500c80e500d80001c0c09540c48890f0030000468a15011109009540d00207200f51910304840c034140c96141038000800e298042c81e803e482d18410300c9074031041d4940b6031382d41500c03646c41022560307401d150040c2480424521007402691049810000d40ba40354200407001e5503900600140f80326101c51890000300440040040140b4208002c040f2900c0e000300c2c2c40040d00075070080d095140203000b80d00710f603003655009001b2039040b0703035004500b0340c441d1019000a00003003d901d4249070380941c49000c1005812182a01c4038040e52040c05203540303a0400404003c40800c403c4141b600c0704400b440104104e0383c0100c1c84641c4141656000d144e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 230966501 1250 230965251 230965261
    0x7050c0d080402030f0a060b0906010c0305041701060b030129040f17030d05131b05010804110d170d0b030601030b0606030916091d070f05040222030501050f0a02070302030a08 77
    0x1007011408203806002c1d00c40c0806c80001d03c02c007a08809402c52080e504004141c4401004403000c010300300000e400300340d04002c01c02100191494048501981e0070001a945899814540041c0c1c800e0b4400c10b035200004004201410b1141010f008041c84401402d04c1c10385060309000b003204140c403411184d000385042c0200340400c24000c503068140072240c100071524114129000c807030034a6000b40e5014221804568426806a00031426150145c5502c034556a640e5206500310344880c070082c2c0c10462440306800001c41c60f068150314080b900d0700c00d0740c441001880700f00440300001100b42c441e5010600400129110203031168000c00c09072052562030f55026003040c90407900c0554445c0f480586a800655014a40e01c4400c640180142001440c07401d0688a9652800b6005081c19443c0003034041015242c290f00038804034101e28140241c0c0101c80150012284c9140d105841594481c8100101a54450942d43e071010502c0030071401c051598030025680d0045d007241c807051042c1700c80420f03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 230967751 1250 230966501 230966503
    0xf0916090902180702030703020f0604050606130e0105090d032703081803030c030709050409111003141314071415160317070c0b22050313080607050c0d08040203 71
    0x2188100003c012440c003800c0041000399a50b0210006034011700402e1100c1c49085804078007030340616040760081081341c40b48000c218034400004c4270145055519140310711003441c00e000785849100d60f14040e181c03441d51008007409460701e407500e20514180d042d000701c460a8416000c11980e607090f2510070816a10308200e074807000e01f543c1c43c141c0c0900c80071040000d00c10344c1d5402144240c41d50340d40c0c122200d03941c030148401c0c0c6801c06002800b15000d04041049820f01d076401c0c0c039241c40389140200b245000406000c94078003051742c035130761180e0324504040c06009200c000305103081c581100411400e0318002e02c0c3c4003041d01c03c00b511441480c9003082d220200ba200703010b44841010848184548040500e40600003892040740454a61060000070f2950341c0501004801103810809412956039411030b074802d80c0030790b1018055401d440041c00c501007981003024004210351982c030480380b0f904000c0b60610f03200c0c000300001c2c100041080004030342c03c004903c1c0301400441d41001884be8072144002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 230969001 1250 230967751 230967769
    0x70507080409020f0c0709020715020c0a1b150507062418090602030c120714070b0402040912120501051e0906180a1401140303040e040c0806040b0f0916090902 70
    0xe00c0c1c0352040c480c6c04100710b0340c15402014242d100d518400080c660291010050b8042d140c0c0105040d0000c904c0d50001c20030040422070700c1840607a84555458640c882c3c9070000000340c582500180001c9408410022103115800e880004406031081361040c80e50007500102e005c0c01045080b190f40140204040d06603005000d000b40d02c114250348a1910031b40d00710701500f0854464594a82c14404200b00d140a0241d1900140000d9509860300d0722070b44440c00c10031000740c001c0341c001d80e503903910002107164042d881210721a2a80c07401544004860302000b50b40068101c50b1249003400d800900030036200300b84503008141a50950781035a40c080015202110003907000001c6e40800c820000d85070203d5200c1303106080303a003643c1645030740c9964035581c41000b075046958069104200c140260300d17036006034a5015120700381184c0ca01d03481d10301c0d00c0c0c18400151400c07119404440c0501100c01c00d00b07000703254000704802c0203004880c02d80441c400c541405104140c2e5155980c3e02140543d100ca40303031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 230970251 1250 230969001 230969017
    0x31524030207050d0e031b09071d0303030f0702070603050601020604030f050d060f05030f010510050607150212010e06012f0a020301060e07140f090103020904020c010e070806070507080409020f 85
    0x82d95400c0201d00300180c020161402803038440e01500c81400147c81c0081d034040f00d40c12000d400c80f01c043e40c0340d50050301c505211042d09142d408e085011001281d07410401188641e91030307014600340381010384019162055981182040c18200341c01c00646903800036030164400c0d0541740c01000f2510300388055070144144401c0f1b100d09400c000010034244081c001080849005030300b1149895601d544041c22680180d0341d41d00c54003c0b025040207a890000050a100e90240180c02018403514803118102d030700001c9545030340e4640e800104010342c500740e0f60b50340c000d1342130a000d11070306142c146240800503400841d4400d8020384024408260041002420495014001700207494550a11480e00041140c000d40000d010100c501c0c81d08600805840c1e41d030341c01800346401c01c10740100640c040c3d0090011982c01503800c1c41201151442409024512601e1402404807641440d90203400c01030000c020105004040000300d0000c0e140b682160304031001842c00581b60780054100c18003601c12095 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 230971501 1250 230970251 230970253
    0x17370501090f0b011d04110103060e1f05041a0d050f070314010c050f3c07020907181a07020604180f090f0f0f02100e0103152403020705 60
    0x79010040380300030300742107203010b400d61071100d81e130354804400d00e03950382500d41e800e21840202140010b80e4854001540c0380d014100400d0300e9440c2d4000c0340c06040308480d503101c220151101d88402400200305980074002c00c3c1c0f000c1c00000e0362070b503800c0a03140341180d109014100090040b424030009003d40341e810000502520029643d80c10501c481e24031a0400310701551a11008400c05405002101c00c241c203001c26403400d10502c0c50642c2542400b40c03903a0154055a9000d410000c00a0100e9520b00368a14018549500b003600600012a000509a0080c0100e1400075101c0403000b0156000719907810f40d2200d4401e02030499407685001d2050029044a07020802158100c0511881440800baa01003000f8031041648008261051480042d2044001c0015900410140d40010741c40034014101202802455800700b00b981c11071807030800004041d00c07803501d02c1c2e6905011f1486244641901c4092542c18a00f002014107842c0014980d80345c41c00300300711080e50003034054980d507640100c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 230972751 1250 230971501 230971511
    0xe070c0c080f0c09010909051c020304080a082106060d0f0605061305010206090a0f111f0503060a060309020a0605070f0614010f0509040c14030c0d050717370501 71
    0x1c0c5150342d884507450104d100d01000000130413910000c1c070410034226040710040100e50300300344040c0010341c881e00c12442180400c010108034218100903410540c0d10a500c0255070b800c01c4c02c58031000040409400c04102c40d43c809105c4265284000d45e010001039910020b500bc2d02d80c0c1c111402000c0c140d00c55600010b0108500440c003050341c0c402c408a03102038003615503d81d5801c025584030030040078000c1040340310344801c1002c00c0082c1d984290b210707005401007102c10224035034071050080c601e1280002450000c01c100c414203180180000800340d41c141402101110b900044c09420f6500440c03080110120b02c2e80203001c0c040382c1c0c0001080e00034004202010141942011a180900621002480c1064005401c1c10b201080b148038541207580710070b031541844a5540d00454180c41c0070b80c035100d14080311000e595081d0240c0380c800d1081c1c0c01483e016103442e100d0301403000d40001141ca035070440c443c40080d82070004d0300302499901190841c8a00500401c2040c408401100041c110b5840c0c5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 230974001 1250 230972751 230972773
    0x204050a0e060f010b0d05270a05070602030c1f02090d05010e010627050603030423040c0504060906030c090f090c08060603070f0e060c030a0203071406010e070c0c08 73
    0x20780c00100c04000c140c05031059a980c0e8482202d90a0081c424003040c0c40007005007910614032a03000b2a013240a621004458a07051400c640404641c0001040941c10004403601000400c000c1e0000602c0c046c0051420304007401625911507980700204000100310300640700d081285030f070403558810740c018400e11a162007030501074000c2c10800805411503190040109080345051124a80b00403100a01a400b00c04020340d140a041c010b04500d070148010b010102c1d209501c840360f43c10a03090240c0f101e05a0302e03c1c104200660f60444000414132108210610001c1c1c2d2116208040d113001d0708020403400090003048440070290303031100c1c400d4441070201040c0c1010701e41000d1706560450341c1d000d0f103948510003080320b17030301c41601c540011461042c1e800c0c0742c0d82e01500e640125428010416420b0101101c0708500315407080040b803005801c0050110204000c0080414404032200001e2400f5030411580e40d40802000d4400c00601001c2c0c200c8200304403005c09aa0301425448080d51107117000d17 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 230975251 1250 230974001 230974021
    0x606050901050c07051512070e06030c160b0c0c06011d040803100b0f0403020310140601030e030c071710050403300f020d18020303041505070b070f08070314060f0301020403020405 79
    0xc087c45190141c5014404101c250344655403804001000400310b915580b0f5aa102c4040c9901c401c01244000b03506d1452a0045260704007124841c075240d081e090750714480b5081c25814108141c201c00210f46040c84540b10081c040b0b41a10303402541310300404d544e9122407010010fa181c241d80304055143c0700082c1d40c5800136843c400b80040300e2082d812201e800a5108803501900c864203041a0322070403003400510150700c01c3d0001903901c1c0a201c15285005124188641070a0b810307000520000f005a00307142c2c403039004110092104402140801040c10300d03540081c0545584003404103500c480d51402003044e00d0400c1802804940d400d010008114800d10840194018500c5c0d107a08900d8123900c4006060f50f81c0b40d40c0c160070782c000c02551500d4280300b8502c0140c8410351b5100100030041c040300002030f2090b101c460040e07001c0d4454051109101e003008003850401019101054100041041c20904154070b254100008442a45141c0c1d070f044c010900902a50740302a41c40303810b0409000c0c0c190301c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 230976501 1250 230975251 230975257
    0x30f03040602070e06030102031e0a09140d110a1110050904050403030b010807091a070c0e0c04031104061202131e020c1005040c0308031e090606130606050901050c070515 75
    0x1031007040d00d0300e96505c08003010b00702e0008441f2603c42c00060b04010f100c40001c91111540503c81903400035544015407602460050450844d02d52070740b1120042c091243c2140700800010140002040c07001c45a035902c50341c0342540034109004028603100d00003454054001d0b02e1207800091b10801544c42c09007801005410600c03400d41c0810400004541c07040d1003550204141d0360741c81c0c070000354900e0311411110b45d603004002c1501c0801d00c0002c08100300b40900c1405000384a10124a51540d00310300345821103050229000d48034a10700103040100c45403041640c0030320358040710b2403512006024080805440c0000185041c960901001c4100a1242e80070f04110b1082d0400c480101c0d0841ca4020200c400a940c040e09958045500b040010400b0006661040c024140503018441c000241e5a4100090302c1002040c0c101da0100249400c2c820001c2c0a4400e280a00380892032400c0005401031040040203810440005244e40184030304211040080102402e0f14506000302c00d1282c0380c0b50 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 230977751 1250 230976501 230976509
    0x20a1703070e090c040611010906020a1101050105040501031101030209030a080c071409010e0c0a0c0f03030906140606090607030e190f06021c050d1803030501050a051206070806030f0304060207 85
    0xa402520990350908145910511541d121513186207403030b007050415181414443c40040300c80d0b40307031100c800c00600b0030300250210b1009600d42c807211604600d0300c142503d20581241d4041d07807900004002003180c1d9031000005180a08006942d81150000b10303090420f03505000d80048000a0200c460620004909080350181c849042c3c2c0384032440c0400401c07a03000e02c80c1070307500200301d07001c9801e2242440041c44204080d04240d44240143c0c0d85000800b035440100741c02103a62017240c1d406010301c1e4010b51801484400004401d131904000041080c010018041d026207008601c00c1d04040c018826042c5900b0300a0110f0410b05041c0801142040701d4003402c404a18801d80002d0b10f40d0001648108070765016070300041303a000a0380d0450b0031f9005441015042d80d1511492804400c5010003c850036004c0c2c1d0b00031072607604007424800b500921358811070140b862481c402e100c514004c41c01c5034200e88141340503043d03500c1d20800285040000380703a0600d40d0100203400580f075900010440701301c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 230979001 1250 230977751 230977757
    0x50405061902030610080606070b0a0b1002010b1e13020c0a02011e1d041e0c0f09080309040203100803040b0307090504060e0f0408040b0d090b0f01121101020a170307 73
    0x2081c1c1c44a107000c2030f40002d5403032030b80007041038a01640e454003820007540e104201030251424245651035480001400ba900c0030040796403183e04001c54181500034105580740c1d07000070f001c8140c2c110301007054407c2d055201d00a00340040b00d4000143d84942d888403111810220a544030941407641c07070703152540003c0c03c902050010141c0601480200c4403083d150000703485610303410707005c822691f81c184001031155a009950b40e10368600c84020100160004254400010744280c259402425620040c8a8a001d00040e54010441800d00000300e4808420954015840ea15507014170200b0150a80002c6941c0c003000c6004a010a80da4000d10b200f0401a030350b800d000742d925007d11088508501a00c08800003000010317114009510880c0d0b00240318120300d07890700c0e5840c40480101d8103c9101110080e8903940e00b4000d1044004200750800c900a80707549840d4035041d241c64800c851044001c19003020203e02181c00e038028804142d003da00071900142003034203002c1150055008650200c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 230980251 1250 230979001 230979031
    0x1020d1508070306020c0c0a060809210d1a060715050109090c050118050a06020c12030c0c012a0b090105131212060807030c0e01140a05010503071205040506 69
    0x1902000141140889040e00702414201d415600c41ca8043d6000c0f80d10079240d84079003966a20a51181c010000060405a81e45240ca0030012940b90800e42241c48075850110740c5418407031050340d001e04540c0b0035040e403040052240b00d160340c20143c500e2445421580442c000c2134440074171020b2840c01903446c00301c2030200081e80e01c514518040700c1e0707050400b500d415220305090101d94082c44032103180180d900d072481c2046903110000f540002c40c030703001240141c200308058141410b03c3c2c2e0780c01500001b18800307141052808051700e5501c0100110050400c01891003414000f003482500080c500c9244000c140751206d241044118045d0603030700900b05600c1c000000701c03521151060507203002c2d44100d920080d00d00084044481c4103038044441080350f5125030004031444200403460003144144a00180e091400c042c0034a0030005034040c0d4542c1201d52403412090303444004c818240c86003400d105482e5101c41a00b1201050900240b281440c0703080c00744000e1010015107140300b80003107111142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 230981501 1250 230980251 230980271
    0x618070503151801020f180612070306061101020711011b38060a09020306060f0c0a060c1e08070e0603090a12050f041203051204030504050405060d260f0c01020d 71
    0x400c034030800ca04000803210a12000d000c00955441c07a00c61f00c0e900803c07550504203441d074000c40d029002d46656010a5407100c040110301c1d0424140d50a40601c28021402c01050b9102c46038015018800c041c10862107024020951165168182c1c0d199004103d124104444c070840704070400c007802c0c1c9041040c1644031045150001c60340c03220711518001d441004c0da10725140c0d4a038081d41014092988c40304040c030100fa40a6600000340403d1200700c1d0040036010260300f018400c888001d05004100306017000219010305400c154000f43c502c092600b0ba0072550f0300101100c0c10019107203002d910000000500031514000500d4000c414050244140020380036941520b0714490049094000030301030104101084141c40e05002c6e10b0700908080e80340c200c2459000340703100030489080300880c4010405020a0403c0d21803194081d4007030741d600000c00f041d904c518108401c8045027081d807100c803201c101e0383c100c200b000742c6107001409043c1c940c4683c0e5a41d242070103904a643d1201100e460134200d14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 230982751 1250 230981501 230981503
    0x2121e1e030112050601090516121107030905241602040f1b03060806060f010c0606050603040b091501030809060901030b060c030730050705030403020612010302011e0206180705031518 81
    0x42c01a040b270243d000070804500b0302079820780d0320f0005a000207580c800320070404528504c01071106503c00d03940d2020300c500380010444280501840080c000e18000c2183d8240c4001c032040b5009040b1240024100403603910002d40a491950719296500d0f0030b048840c440e001d80c1170280e8001444644090140d43d445401103551020708541150f480304601c4040301c1e00d54028000803a005010302d2001c24030a0b221400700f04147c1c4141c40881d481c0100400300b0002c3d8000b4009007c50750404a004a141c0d4503540354038025014103c1c100707204900c00a070443c6268029032004800010103480306444406c00a00d1030b40700c0c0c001d0301c4183c4040c1030070291382a03816044820748007243c00354240681b408a5000e42260143c1014a003258140301c10000807001d40c0d540405455044848015802550306502c00103050b02c0b00c2d21140d44040c07000c1c0e40740c0c603140c540100780d40d6402140600c17401e0702104010401840c0a0940d44200c0e050f0064984100504040000345885960721020001000079074102d41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 230984001 1250 230982751 230982761
    0x603110414061c0213060b030601090b07120e0301140f1801110406050a090803040801020702040c1701050906060702130b0f120607051602120604020102121e1e03011205060109 77
    0x115801082507a10001a61451510042e0640041c101c5c24491040c0010401155026000b40c10503a0011007040019039100070781c10060484850480c6c28807009035290380030a0f4a2000b00001d118005803501c80544095012450444040f10035903414180384411300c2c04003c0a480c0b030300641d001030064107c951414000c00e0941518030941c1da2429107410000c0b100c0c0c3c9c0004504004000007060300081400b01000a00045e01c42180010f9441000344100000c44025800301400d0200c02c201407503c00b041540003c0c111482a641810117030fa4080c000360341c038440e8500c000d5204414101d00c061190032a803040111240075200b0304a0325203c101044485011016182481e80c461000140b65901c0340c8068001040740664031000c010990340040c450800c14126492268844001c1105560b030401900200058000e80300303152000c14901c44410008a201121600c0340028206208405500181400880d040401c50712075071079400e0310204160201e801e0b11240308950010540b02b41034450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 230985251 1250 230984001 230984011
    0x13030303150302011706120f030a09150c03030e030d020a080a0b01210e01090206030f070905060f040e0603120f040603111c09020a080f0f0709020a0f0c060f0603110414 74
    0x5d1202010540d040d41c1e0310004024200d94000303044940c00611540100201a00d40e50318034003454980e011b140000b81a406c40760711481400644c448140e82c0e40785c00881442000d605480c021070b54203281c442043c558031851804101c118130006a01040907070041e800d0380274450b000e4060001c0d40400e001101c4004c22110804105c120100c18a9000c01c0300d6030044c1c0c0f0308004030300080340c81030007500010280d403c21611070218981c5a4100403880b9841081180036040c103e4071182408114450320507203000ea4041ea6a51604107404110a540c003080003d4550310031480540d40d96001003039a1003190810704c10782c00480d051845002e86904080309a9220320b070300020444481008428041c041c00400070241c0e0088400180480d42d10014170260480d90000f90003420201d141540003442c2c500c0700e0307018070101c40c410f00ca204d111036070002b03001010901c00e03d0310b1102205581010b500070041c04044000d841e190403c0041000003004003603180ba1b0701107070204030030450040164000401258 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 230986501 1250 230985251 230985257
    0x17100b0a1808010c0504181503030c111207060507060b030607020a12080402091302060d0c03051812071202190605060103050c030f2701020310080c0a1a1b031303030315030201 77
    0x8400e200c000300021203030761082c1f0054008951079105402922403408031f90000d4000502400b56035003030000900424004440c113985001c01050040907440c0c90325414018031017044000142082403002c0d80d00046624a8001c00392000e5080c610302c041d40c3d80708015007c032482c510304400c00c0829400b0f40304062103540c01510801241e5201c40c101c0b036088121580403070f0310041c288104100e005052150b11038180032501c0004003804d0142c8814058a000b8003800c84541c40441c3c10041034110f601903880c80751f031040380d018684000d00c80603420021031000003280f40719410b10400902c800341d08594080c4c2e000380c03070810641e1907030b06100c1c03182d210442d130440c00405842c000c01e080309403100620008001c030f550700e940300000c4d00202c40e00fa81d1040d144c1649200c1c0710b6000744004a8103212140d18400c080364051403691900025400c00c518400c088192130780c021541c40c1e11a40c2c4c1080c070311000d003c000240ea0303481402d9041d904104102d400309400080c42c003840c84a12204003855082030ba50161 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 230987751 1250 230986501 230986507
    0x504090207020103060e0a1d0d05070602030a140c120708060d0215090d08030603241503100606200304061b08090d050304030b0a050717100b0a1808010c05 68
    0x21628006944461412410150b0f11900010740e5000400303014020100c800700818840840480c031074050081c206c2d425940c0e007002c05145000c1d0f070032108648903e81c3c018400740c3c60f981c03218000c00c0200030302100b80818a48100400c007070303510404001c149100b0343c200300e0207441e12100d504940140741180c100d40c0000007050142e0140c504041c810b07492281c0d000010346080c0302c03600031500d081c410b003504441e0700c280402444203500e000e000c000030195690341c00030f00b209e0f01585032914420b0090443c0b11040b041c81e4800710540c406000000103010b01e5075040c08010f40d940c0004001c81d44015030303840607004589000710411404000c403000c56026a55001345079aa1400107600d41c09084030840c1c1c142c80401c2820019200d051015100c503000300c001d552a1407450030b100d40c080400400a03655035160904004000f500564210544000d0a1202c20b25640b2421649038903c2c103030b000005c010b01d0100b41d19030030303039070284140002c0b518600000080581d6241c0c01401d031a442c04220010410074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 230989001 1250 230987751 230987759
    0x726030106120e07150e03010c0c1b1a0406081317131a07031704050303150409060f320601181806050909060603060106080903090910030209090303070504 68
    0x280c1c040c0d81012007244400280d5800c83c0c05a140f8103045944002a44000d103202051855001180c2400c13049041e40240441c5889100082941c00807610040104622103000a50343c140a1411070151a24040c801e11900500801d00080c0e0048d100ea0800240903000080740c81c0e401041c070707500031a40310388581c0400089400b40c03006500903150200f08081100400640001d07100159003136003426484407541e9548509000781070300094000c555000e0008014480040d8000080325805158000110340c08040c00340041e01900c002400540814202900d189005a91b5030040f00a4140d50743c04582d41a9602c14541d0b01807155001030450740a0040080c45550207440114032007008030051004041d01c1c0c140f9003100b00c4012080100c102e03654a001d0100e42050540076401040c808014101c40c501800001d40ea00c00500540081283d1361020504240040055600d180d800030204c1c1090700c0c20842d011003e40c140d10050b0303c00c45585d404900440380c0130046900407803484d6503113072503d418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 230990251 1250 230989001 230989007
    0x7031406061e0d150e01030303060605040f030308131a0105210c0d03020312010305010e0c0607050604030e0604050a140907180b1e16020316060207050904080904050c0726030106 78
    0x1a001c2c640949448094101400d0f13410103554018283d01103884446504500f001000c4480c03070307000030080c400c1c200000d21035400c1c10115042101d50603c3c01042d541d035211600d280b850080c030740040c1a151102c0e1641040a4228400ca0584001340c0d090144100200c100c2e00e007446014409589a4008203044892030030100304059005029004a81c6040f0310f80e510b40b100f40381d00340d200340c6041c0d43d00d1031500c08112050000c1c00b84020200e41c0e1b142083d4207515901c1e10340c8030180009061003a480c006015607213a82041d100140340041c04415555a1100c10f00710b49050021280d201d1200000081d246a0007020b070034500003100c82048140754240800c070070305944441201c0e080c1c03004045222a148001200400c2ca030030038942d200201912900c103040c504030514410306c091035003181c2d0502071194005816400c41c0e1040701c210100340c4403820a180300c0d1080003001c0d6009030511081003190b40c01311000303182c410301c01c16542aa8001d20000051101c00c0307105044c8280304100300400803d0700c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 230991501 1250 230990251 230990257
    0x20f01051309020f091801030b09030703050a0806130f020406030f060b1c0e1e0f060708070c060e0105010f03021806010f030e01020c011b02010c110c040e0f0607031406061e 76
    0x400d00d213400b803030311150000207017204071034003180020003407410b00601c10032654450b102c1c1c018441400450802100e41d0703000c0d1042c0101e440d0001040100d400084066413450170000400c01c10800c1041007400c8206a1000781d80079029030741c00300341070440c3c0c170001c2034407841450222055400c0903030800070001001c1c50410042c18140c034110f80c03141d41c1c0720303114101880403030070b070844100e860444151203ca445080c40041c00780aa204e0304003408000c482c2e46c21001d11503121070f951405103940800ca190240040002082c880220762070540003003014410a207805007540c2c000c80b006400c07180d01a510144400d41250a2400522000008a034250194200007071a504c20070002d410912045e41d00c5003103540c0c500810b0301b28100d0840d888906a0280309040d482d04c000d103046942c00c3c51780c0d14041d55402c0081c10180c003c2c2c0e070701c611003400b0070814400300001403030f10001d540d4582850f9400070007030803642001100300100d4502152551500700c0c00c4032001000c84180302d400c50440360720040190 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 230992751 1250 230991501 230991517
    0x120e1b040b1503191404020f0103050c0717090f060f120402060903010207050607080c04051c03030608070b07061107020310090507050d0503070614090601121a0106020a020f0105130902 81
    0x14000322a04101e2245880a584109044d051449048800403403038015601c16564000904004505110143c1c41307a1b0180c0b90242000c1c03c000c2407540307418115141e107105070b0724080c1c400e5030007243d45214180a00001d00540d0400c48110703a40500d40401c20003c1d100b00f5805501c500802c0003484004414043c025611a0000b4500790030040d1000202e426a07000b181d04446d40e401027400c0104a641121140d03410405880d0f0650910f030408000c00c5450181401501e0032a90108945080611135000b42c005000004180c03580281c0d500304202e03070340d0410b41080b0341041c02c260003880c02c0882c6409072000180c0040c010000780c40040b450380e000f403569500940b0140030300900481c40d501c034445042d9107148181c00642d692621820701e03c1c103c544a50044000403590002d020707540340c00040550544106031302204002c206443c00c2c140903000d00503c07103907070348800c00002061500030580307842c214000e4910083c0041420011169803050003206500c1a01210b400d000c5101994080c0c00c840d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 230994001 1250 230992751 230992759
    0xa08030a08070c17091e0f04090609060603030c0323180409141509010504020d030f1205040b160f052a010603060203012606161e120e1b040b 62
    0xf10743d944450413120300c64118a990b0000028000c03809083c440e44c120301e4030885803a80302c043e01c40840044c0c41c800170103003124031039926016403d00348107244d80041c07c19035105a0412525540e407031701905035804154290042084000c00301c4025040e28050070320380681001d01443d048000342400400200d404000f5085552808000001080d103d640c0c2c600f400c03140c00404218640300c07022101004005c125a1203030f4145414400162100c60300d0600159142c00d0485074036480660441c0c41800c8844d0700c0744001d082c4420321050004048829008410042046100703d403001d20a81d400085080340e1400100d0030055845200c401b40c50356030446406100d030300f00d000d203c4031800d429140d5603001601c0355940013004201c80000103800070042511070b0116615003403104a2542c41b440001c1841c4c144d15140b00080717286a1084100b15508a5040f100d181507000003507000b82103000742c25000e0150780c9404074001044000142c00702c800b107500100649940764101c1031201610f0780304500b90300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 230995251 1250 230994001 230994017
    0x306060313150509012903060a020a05160308070e09100b09040e010f050601270311040204050d05280b160219030e01091a12070917100b0a08030a0807 66
    0xe81c0109001c3c16001c0c40d560000800d041c40c10180100480c0f411441e09841d58018401c00009502c0c04500107502011200c070041e201c4071103040590700c5104080301d80500409540c08a420540c00000c0d081c05904156076003200d151070703441801802d400a881c07012801c83c04c0c15003000890440c0c0c2c0202080d102c0503001050113841d0312940f42c03d41c1c1c00c0c800c8020080d6190402c001c20740d40d000741b80004800c1c03888803c0200c02c8040d045500e0042140c040504145101d5078014019140d6030110343c0140000b40c19241d03041d800c3d00b04661900c0342c802d8410501c0c003038424100d0380707114480c0c5001042a000021409182c4031030409164108a248200c400c3d40a010400e041c05060010107010750f50080c0c0b500704110030315000040c4850f03102d81200785614902544d441221288500340c031250444908500100d46450005503180c00d165441034449100c0c0721421581c01c400410840e4102e14101c400f4400201c500b0108100707440203000e1046030307600a00401a40700c1c0708071519a0081c50904040e80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 230996501 1250 230995251 230995283
    0x1e0201021c0809150c030f0a090f0501020306040b0a150c140607050a03051e040618020603010906030b0a020a021c03110d0204060f0f09050d15150501090801020306060313 75
    0x2440300120598011480c10b074108021880284090100e8442102ea030499605d003252040c18680400307030503103e94903001c000003102e00e611544058107503600005500b2170381042d0725000340030354811291280503c0c10050006024149202c81e0005d035820b41da0355914090301d00c841101c414440400c250b510b00c41302240c40c0c1740104d0500901d4010491907988661719180648007038141d4401030119851000c2140d2048030300319000c03201d01d801030340c000e078040360f181c2e0381040307401600c034500700080c0d8001800400081c01494039440301013100c4c8103082d0000c5c13966459100c5401c03401001007940c00368101d800e90420031009032100200303134280307400d0000c0c1410441036100c0036600041d80c1075200d1940010140004ca41240c2d001000310203500d04040340c1e4040300401850200d22b88500c9005110018446080000340c2c0611405607101d0700c401c100100051040040c000700c03521800e804a07911a1011603c0001030080b284161780c0a0003403031642d110b0000e10510880f10b018142c45600303500079014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 230997751 1250 230996501 230996533
    0x11070807050303040519170703170a06091103060d032a05100b120a0303020318030304120906020703080315040605040c0908070510140c0708030c030406090e041e020102 74
    0xc60403500a00003140c507854180f07411454803910450024101d10b40400c4640003c826900c1440e0100c8403030002500d4004924040d2100d2054054044c1a8240c1d01c04015110a00d03901604c22943e40500610090700203030400150791000740c461503040881d0140803030200c0d000f071020110168105500401010948034400a100461314044441d038000300c480500e905c0c05802200c000b000c0480c1c5010740405200046d940d81c0403c858004c06040d00400016003020180380c08180080c04e030001d0365528506840d1605100074803c1202000c0350729140041181c034800181c8034162544031951078074541b10701e03803e400442e061030801ea0740075031102d5010500f61180d010710104a44c058540307200503801e00d146503042030500d8114a01411440e030f0b041e00170751f900000c245001c99661012075542c1000304545030902c100c0390800c0300584070000f00507501203c0000244200c850790741d14448240d0b2100728a40d2a00300a48001e06285041c0843c40d03a01c96140f15800303d130b10310500494191154100c201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 230999001 1250 230997751 230997757
    0x40605120c160609020f04020412060504020103060f0308090a15050706020d02040b070f06050106050a0509130912050409050106030911060310051203130803070b04031b0503040e011e0302090703110708 88
    0x200d40b41e80d01c4c0c008070411420301c00200b901400080b42c042d400d00e4104a007022100918000140c58030307031120701040c10341e4020352290000c1d01141c40800449038980c108401c2c982c0c4444416802a001141e0000710328180c1007040040485980c0c0e075514120884d1134000c003a4101d928801c0a00f5401c11001800201e04802061400e202c2d2508230003c070442d04000080340c0f0305a21550034004100009150305e940301b000c43c0c6541030111030b82d08082070076802321030007001d05401c002d084071107680310720314a1078000c40540225517200301d05002c2d907030304c69508034107403014844024483c0715071000c07003001403400c1e8000d107070700c0f0903081a1000104e40d242c0c00607403510041c2d00754030280e8100044410030440910f002401404401c4000e600e0320b00c6c29a6104600c400050001c0c04206811a00070314035480c400104280c41d070014112511076440f40e1245403119020300c2101c0e03140310300650030018510000b004504803034000701070030f03c60340d41d613601600603020b40400740c004c0140c1003001e080060160340c06 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 231000251 1250 230999001 230999003
    0xf0303022101171513060b0604090e16060c0f03051912060503011401090c05040803030405071d06031c14040e0a0627111b011b05040605120c16 63
    0x714803103500d4035603400e860402c46403000003582c006404a818169001e0303402074205c0b11070036121031200c0743d9041900c002e01c5298003a07580712000040001d452080c0b40c0000305200126802d441d80d500106070b85100c03a641e184110b0000c964554a42404143d01c0603440b5002030203410001c2c6058640540c9001000400460b1000b0075200ca490044110982c8551030141009030300821042d10800c208a40054051181c0135080c0d07181d040010382070b4400ca06640080410724103c0741c0705d0a00b441c0032601c661860160010065056203d07140c0c60711420703420b43c040c140c007a010b01110b58581401d107083c8402d8866100a00c86007110f108031036484040100b00524030f0000601150070040c002c5004ea0b00c1c10341c02143d080440000000d4641c0043c400300c00d0750002c00070700261030a12180411240d0045a58581a050510001c910b015106401111034200700030080461140802d0081d10305020361f0007240b0010700d040c852400a000e05480454001d81d0b5140b41c1070414111031180c4420300810341e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 231001501 1250 231000251 231000307
    0x50903060711280212031303032307120c0c150909150503100e1603080c21040603050603070b0307021b0406060507060207060f0c0905180402030a0f030302 68
    0x21840031814070510111220082c1841c40c5403003c08502e0000d0300301590140042c4c8101440009900c031500104102d440da01e401c4414404110303600e04001e00340d15400007100035150310041c0c60381044074910b0126202e20341c0c00400d08044000e9014110351030f0355240c008540700340346800b01050714611450310a031450001d07a00c0a0040d4101031003801034800c3c1a20740c20324001c02d40c01c188865500810b40c440e005820801c002401000070320314901c2c0140b41001842c14002402c8017106008080005080c00c0100408945210110810080403500000d100e050207190500040c40400e1203a0072558100703500504451070144c68129014880d40281c1c0e2180143e03204a8042102c0c510380920303212055002c950030404140b4048002c3c02e02c0c410301c20000c0c00d01341d0001e07103035082200c0303a0700194240800900810090703180042c09410101c480c02994440c45003081140c215006035031019125130b5018000d810b01c00d03540d950781035665901c40700031400c1c0b50b002c2c0904005900e002d2541414905405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 231002751 1250 231001501 231001517
    0x22805060408012301030b04200d1218240e030d030204030218060117090118141516200102130f061e230c0709050609160507030509030607 61
    0x9186000c004103002c0002594013081c1d00100081115818074942c859040700c0c0f04940c0840c954801400c2121030205e02e680900c0780c4801100307010420b08071440e01e400a48a608641118680b1420890039621071001d5200004482e40640d402110340303481d82c4401820310450400d0034400103818055a1403003000081d80c041010004e40c5084154061060058200c0000c24100800000c2401d103401e040401c40c4c403528008281100805d5200800c2c0e91913030f1014515080300c902e4902d9552200d40d40d00403240c45200c001c0194042080c1249010b1007842107c000380d11100074060720401600d807034004510160300208a1180403e00043c03843c450000b603c4201241400518060b09259402030f00422800b220401d008031007c002ca24440e6100e41001420040c400c0d0500d112a0110801541451004a030040340b44200040800c1501c2da018820f00965980c01c052002040c0c0071554801c03030030410081e503003200b4001c9004161860091034501e1030400c202000c246484401d5415000195542d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 231004001 1250 231002751 231002771
    0xb0109180b04180308070c030c051e06010b0a210b0901030b040b0106030b0d170d0c0503180109050d03150302090114030105090c01230c0708031801090302280506040801 74
    0x3074401e0700c41c020340f43c0100c8203026549881c0113044405c0200b003101401403071003681c400d0600031420700b101d042d8043c08651140c03840441d11300c041554400580c0341172280c000081400c2d0a02c005880794042c1941d148074143d141d03140300f540d15282c4004045003003a0341e2041e5501e03a80b0b03108083c2e80658080c8a541000c1d00389071402042404050b44007008061510f031104109658400800d15040d400071101c1181c0c0d00c1003203841c40d00388104945009003500d07040c1c11081007904100558415500841d0030805000001c60260a9501200004000741c0080100ea25100d010360b0100d087c5030f9000315503040140d02e0f07a020501980c800c1e00314914002100042d1181d42c6001d0084951004030b600c0503000c3c4500940010b80318089005001182c0418000c41c068000c031402d0a4881001d032560450709080d9441081d140c9a902418a014445440034812481c48d40509030510132640c3c05000f500c400303142c0c54040c214844130594881c00000400c0740002da207555000107003001d031210400000701c600d04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 231005251 1250 231004001 231004009
    0x15090504200303041212171303171003030807090503070b0903011515050c190606061202120109050405012004090b04060e010e06010207150801180e0c040b0109180b 72
    0x8540d070498801e520400050140b150001c980312402544000b4078a5801342c40c8405442c1040a58542c05144503000c08001140d0880c00c54818076038001d0b10750300c1504004003100340e007524040310300c101c00725203400c001c100081c840d41d249070b030240080c079203d2440743d11b81000030304156030b070350221440741c0c80800c0a004600d000c0c82030101d03c01c4800c007441d2680d8940440d00900c0125400c2c004144038012a070006100e1003404420007111600350308503a074026518148005007000d001d403d00041002c8400c81d403003034031071003151141e030000180300046da0300e07001e000b4014001c010300849055480f42240942440d1882d00f0912650001403019201c0c2d051030307144400c5800c1c0d50031061065003841c20800019482444060642d2201c010002c2030f69a0840140c1c42c024040d40310080e0303406003064040995a12400740c9068851483d42c00202210a45540040c2c4001c07140706201b03600321008508061500c2d0703101038a6140c0604003421940d131743c0c10302c403210341c9200559908115101d0030200118a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 231006501 1250 231005251 231005303
    0x41406011206060b091e0102010b060c060f060d050a06110c0307060f0c02010902060403060908040803030703020702040c030b100c05070f080106090b010f0207230a0b0904050601020105060f0415090504 88
    0x2110090500384070345c03100040e2010020a0302020f800c1002c02030f0720306a9100f900803001c250b001a0000395034482c0046155a1010101c645198850300240410900d1616045a00c0c04582010080500d42980d8640e040140316200141118404c02c0080c0e02010100344040d1110900039540000d030025600b0389041a80c3c903001241045915100941c001607540c01d00381c1e400d603074000130000b4444401c5d00d00f040c0644100d07009640c282c030010042180341d40c1d058000307120061080d2800d22440030003840030350548100242c101d07400240720a03060800307031190314003101c40ca0040d000c841a5039501c001441c2c003000347c1d800200382c59454440c1407042c42e1180c0250100090280391020040c10602c0000b90ad40605000e41405010f000649010074075010b2482140c3c0c4000030072407a10180c1d10303a03624000d58090b445a0740164205000071b5031641c0188265032003420b01903c44100140c4603005c03c001400b451000c40750b10074420340040f81100c1c06106151145100b07c42c4005c551140d4024581a90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 231007751 1250 231006501 231006509
    0x80c2d0a27031104020d0e070825030308041b150206090303040308060d060b090a0504030e0a0b031501110609161e0501050a0c0b040c0f080f031204140601120606 71
    0x40500454400512803035031001044a03001000d000500f040080000c0103032050001192219041002d5600c45040110304a0112910b80c021210044000c50f2103191411055503074120001180f0400c001082c040c08070a54400d12841409046000380c100b0002c085401e604030b0b2549481c0c07403500e120550b03010016650000d40900041d811481c05a80007004403000406a42c01920102c1e00d810811455800c4000311200c010100e171864a064828030000b84001c07901a400150501403c0140c0d061812000f0203403046101400d1a50340d40320000c024503ca1501640d0401c0314403034031921200e81c14041d06000f1080d50001d00300940300001a040a8040ca4012502200303200840d42c0200c02d04a4002c400c40d071007800d01d40d407030b04103541d42903030a001031040151090b4a00c0c1e08001c204201180842c0580380c810000c032102580360002c1a507a420686054a000c0c3d10030095401964074240b00d1551082c03080c00c0b080c44441b40e9030122800c10200380d0021854800400307001c1d00f002400c2c01150058 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 231009001 1250 231007751 231007787
    0xc020d08030925030f0c080303040b062b120e060d05010303080f15091b0a020c1203070f0609020f10030b01030b010f0f0c15090c0306060501050a080c2d0a 68
    0x2052000000001c070310b41c10301c40189210885da45800130414040350000003024241c0a480d228070b824146505003030400c0318407603c207204c001050324020261030000c80302011400c82e82881900265a1407011b16051100d003030034040349000e0304686540341c40003010111101840400d20b540340d0329010b0590139000d0510f0040b14a40000c01111940061040c0d03140a012180301003141c8801d560820346010701c4103498420300e00000c1000c00540c00142d2071200359410355100c2012829213038884c1d200c0c001c00c2c000070101a04884010041803454019414241c00100042c1180380801c0000d020202403114a0001c2038840c0608081581c252041500c0b620302070901e07051202e1a80401070850348075041550520414441c20814001d40c400055803007010320204000080441c2420500e01405220440702c02e0b0400d000464194481d40c161861202c3e179448203051070316403140912041d045402416144501c01c0d80181c103003180318a58141041000c400242e88440b1440000e10155116002002e5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 231010251 1250 231009001 231009043
    0xd17010506030906043c1101020714040b030709060e01030c05150a08040303091b0f091503021e060708040311010207060f0f0e0a0905090f0d050d0c0c020d080309 71
    0x915030012070303080c1c5d01c584d0200f042c00c1900171040c01d1080744540342800c100030b00d6010040302c07030140403000388007507680c000c0c1c1c540072610329100012a52001103001e0443c40c0c0d6041584804141000e400c8109000740003025602215107035005001180c030305a0200181c503440300010004e001e840c3d0001000703000c003038404407441664990600c07224401c0701454010080352030002014540320f075001c80c80841c0e001901590642d41c401800200c03860500642200f403002c040300180c3c00556106110709040541400b01d04145181c080084c0824188510421020a03100c0c070601540d03044018070505210300c0b103040d116800c5040111400400c801941d0556100300001c1c8400340d0000a00c28203401c141c03620000864004208403403081c6c4401c0c8907908010355482c0410082c1a07071300302c0781c400c46007030080700e0050310002c59844e0744140d84021040405c0c8100140ca00b103540310b4001ca01004481d040040743c61020382d000c29050150a003003580c41c0381003c0240320802c02d05000d501c0c11400b0f01014254 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 231011501 1250 231010251 231010261
    0x1c06051e03030403020f0409050703050105091005010e0105060a0504080303091b060c07170106090906022104030512070306051018081506061602090c04090c210e0309030d1701050603 80
    0x82c1c0c9100b40e0101a200b40b490300d05030f18055440d5040390002560000c140d81480b0b03500d10f0028041c000668008006008010050305040c550784030700e604882c1400272800403a440c00c0705000341c3c0c2d44000884d00410030100b20202e1100310800c000d5015203014401031100201c40c642005002029401c070900c20881040094050324001030608141c40691300700d0201c41440520642c010502e0303500000000b420898a4414040583d01074020071045c0410540300000380480ca840051085a0040100f103052000010826024656aa1140e2141800a0701c1030b00c030400548502c0413000103000103044191511002c0005040380b10040c00c42d80c00078103942268158010307440034010b26060082d000072900d030081c01291055000c1c1c07140c02078500407040c240064880065400341c01241d9601e401c1400c0402e0140c0705120f560719042c00740e0300c80c200860943e600c1402502c0c085001010f00c0c8000e106d0f51030150342c14414500390301c1c1d540c1c55514110035464544e0035103c0050b44514890002442001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 231012751 1250 231011501 231011503
    0x20a0203030609091c1205100605160203071a0703030e032a192009040f0204050402040e0709020a020105060d05120c0a0b0406021206030604020102030a03111c06051e03 74
    0xc1d004a02203d2508003981c442c240c2030300d4103240d0501c80104e00c4c00a070405280c039030440114000f10004603010310181c1c5d520326020072600745c40c0c4a8000014820403045036641c4043c00031007100e920003015541d05ca0b9031341c0e0006446100428030140c544100040b1241007641501c9524034000c0c0a8003e1418001142c8003020030504146428112856071340c1c0d0401c0802c028008810320041c1c440b00c002000d8101c0c03d01010f82c2c907074144a0070f0100f00b050000c0074246002400b07a84500da00410000c0341c11180ea007800068034001e0300c120b8219803605007032106103a00303015031070182540003001600e0308080c1000a094601c05080e90780100c2032551000003158000c28180c0c0141d1226486a6680402100c41440d00e40c5005010704100c50940900040002640007400400420840d5002130384800c0101603c441d010f1342c3c003c1c090303441000958041402034104000080882030300034109020117200e0551103a604005640d802c1da01c44080c0304074030f03220080180391500d0503640941d0038044c1c3c001c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 231014001 1250 231012751 231012757
    0xe0f0601120606031709011706030a0303111e0d140411060714010c0203040306060b210c0906130501183006090c08010b0f0303041202120f07080d03020a0203 69
    0x703902400001c03a074018410242c00540085612134910207442503604600986030b04031751a507e0010702c04404035074140e05594216406040014090304204e05c6682d0150b00030200001e90011140c01804100d0005c2c1a0780f0950101c00c01b844040f5039108400050202220b200076480340c09a60003409000105003020181007008e88251400d42d41d901180c04d11024088000d10901d910b503081407164200c0e81d0b8040050300449204860500056071203400b0082036000b603500d180d00211110107801c03004c1d0380c1e1014403070300f2100f0386810520b440c910305e001c154154000d400da61450741c01c4013010451540d0000b00c40c8000038052035051020360130324824080c150a158081080032032842501107080a10024000c4025032104003009101034900d422404114a81310301041546000302d00d03c00c50030028a040503464005025600c2c00303040030500303400c58404002c1640c00c100200007003c0c1d9400b0800940d440c5440c04401005118602042185405070000200081500502c207400301540c0000a07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 231015251 1250 231014001 231014009
    0xb01030e0f06010e0606041a1201060302040506180a1a070b09010c050a0e0103060b03040b10050a0501090302041104090204030c09060902070b04020919050c090108010506090102120d0207150e010e0f0601 89
    0x407801d03091710b813038002800798000c43d0002d43c80ca100c1280180100801440100001480c0c408411116179079080d080c2c080380180d100e0715400070410440c40118000000494980c07480080c0b40d00125a01d415003505060111600340194000c002106000c1c402052601d07540014500001c1c05010045507000788140540303181030090082114540c0d03140e0780a500075402404220303840d00c0c0c032494035040c0191140350503203c00540d034050f54000726076170500b540c5680980700d041c1c4440c44c00500d51b50900c00148091134005c1c0e07030001c040c000850442154001000110b02400241442d075040c1003030301c01150300950145020a10401c903c0e03000544035040242e0150b01164201c4150f680e1011400c3e040c25070000c00100b040ca090100700210005401030070701d1a000380e079086041d82c0c841c418405079110f0303103881a000d6030104507070b03103d0031102e24010080c98042440c05801e000071941e90014112281d91070115554451840c841740c0e260034490303d00740b001118010146240a1603600e40c5420041c05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 231016501 1250 231015251 231015269
    0x91401020d050c01390201050417180a0b040f06020c01090911120c0408010b0109080a06021c09030306030303140f04030e0f0d11030d02030307020d0807170a0b01030e0f0601 76
    0x203914110303002c02c2d44072404c40e12080b10f02e81075140c100000307000e00d00314250100c80220030017409013100510520501d4440c607404446124441c040781010010381d00709007000d62116150b40081481340d00d80d00c41400003420403401035070300c13503041408499464146030803040840d80110321b80c400c6680d1020760b020844076500c0d00010401c10109072000c00c0e00c600c01c10307003450700004001d00440e0ba140000800c11141100000c2001003140d0b401102c6041c150700c1807540c0c95201c0171001c004621141c0c002c1c101c02c0191840c4000820030350307080100303840c01024181c0c0400d50700c0d8000c0090642500900d900e412400b048401c0c40e250030168a02c651101900140400c509420000015202c050f2002011000100784092149007890984880090141d00c180240640c6808040d168000410740b805030886402401080440201c11a000d04004200301c040005181d262080000d5a5010901856004c00041361040000c0005000d880c4902c1c0d454081d64040c001c2040c0040001c0b03509419241410 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 231017751 1250 231016501 231016507
    0x80d08010815040f29010302150c1507021501060909060614121b0c0a171c09020112020d020c0705030f0309090411030d02101a09010303050c010e030307020a03091401020d05 76
    0x10070000209808040801d184845c40303403813542c2801c5800c04141c102d80c400c44510b042e44500c00d07003d02041c05809141d00c1a94880c814a541c51644020490b51201942c0304454442014a01c0c0d034130040000c0e40030001058020000b481420b0071401060050021810011240482c140a104d0300b48141100d03e58034210120100c2d038240440c0d0303014000c0b01400002c458841e0311064207661a004d101c801212501c80d0021605603041e40c1000395500440161403100c0354141890420001e00344200c3c00b03d0401031140307207001088580348090b0000200d205001038032104800065440e022154024500c694070118030b03a40c18a000004440100c101070340c41800b43d454514140741071a0f00078100503854002c4d500602041540022900c0e046501b101c0103000440c43d40001d0b4050b9128840641c0e08510707490014808a070084000b0710484800800000d140d48011f021b103400d41c2c1046c0d40c1400140c21903a100c0c410f1650142115025020034150024510b400d500003035a54860301c400c201c00d000c804 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 231019001 1250 231017751 231017753
    0xf011e0512150a0f0b030601030b190605090f010519051014071401020a02061b07120509090a1b050c1005130c0803091c110105030a090c080d08010815040f 68
    0x5102c40820410840c56101c00b609290010034003600c1210094164a46440c601103506e103000a101c90480b42c0103884240d49860301c01e80150b080e01d6101d00e40d145a512648002915100d2001d010700c40e41c80301d01d880c200c65040ca0100441044441005420141a035806004c1560b43e040c0441d00719202d070a05202000d017506410038240521140900f0072158860507035040081074004241b9040c1a900360342e15a55008800c1100023003000464000d81418005a00010314013200781c2c01c5071060342420350038090820000f070322505d01210140ca190780c852112a1010420440301420140c0c9810003d0401c1840d40d13210ba038800e0706c118100501501d403030128071500100382d030b28013119811011015101e1303102c69142c1e940303038040c004482c04ac0c0321603c03030400785148400300c0031030741944211501d82c0b0f09900030045405800250051910941e154035800014950b40321200060482d01c028012071036884901400c14401684084900c0d0044080f0a00c01e1400540d01075201e980014032410700f6000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 231020251 1250 231019001 231019003
    0x90c1303051204091508070902030a021c0e0f03071e02011e050c10020f0a03090201110d0305010512030304170a0c080c060901151203050c030d090b0f011e0512 70
    0x81940040c18a00800365202994158040200300740c5925100c00d00c4040c00d0394803600c03450151481010b02e00c0d082503000380030040749500150f0b00012025030140c02c00c10303440e01001d2000781007440c0305001581d500020354000028010707002c62060300c201443c01c0024030b445402c205188880b42c024507003150a0001c045a0040c0701c14051040d003111062604002c14501a00c558071010100443d40306020703100c85412082c5c0200c0e200d04125401e9030307080c4020307440140d000c0c046261049051003001000c81251102c00c0001b19481401130394040f4a5504d880d052100c41446100c0041454008004001c00319001003070410351000f1900b007440d560070002c0700c00c641500030503000038820100040c0c7c0329035007007000410f00c5c041d402500080040900c26030320314485032240c0c03042d03403408c08041c2d0381d080c04a80100081d064810300340c41940c0c81c10303030702004210840ea583d900860708441d04c2c0080c0120108040c0840b400f41142e407510042c0b10703030b064403140c1c0312440904c6914420015400c0b44800150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 231021501 1250 231020251 231020287
    0x1e030c05090f030f031c06050a050d121101020a0c031202090f010c051510031e03080703090510060806011a09090c091233100504090203120a17070c02090c 68
    0x180841036a07111455068010410b202a55030b86c8903543c10070501003514501160301c10212007004103401d41444855440c0f40700c00c003107406440c092204c17000380303001032039420300040c0080b500c50307030b941c00e10254149006804446007004418a0034410310100d1103e8440e85031180450000f42080720700307106d440c40c0c11403500003188196800000100244480041e8004c042c41c00d591040f1170410b01c4020400306818403107580d0f00080c0000d85018085403c550081d802416068054019160006900c5290006072001a403140065502c00d00c010004516031000d0003244000036401d0500c2d10203040b0004050300c2e005020016202000100980700356241c00e0031b80e81055000c0f040c2d0f20180c0040036008220f40ca00103020a0360042a0714294004503c2c54009110741c444100846401c2d0038081804003c0ca200803013280c040c4240303219040c0604d1810040d22001c0425540c900101000d20300c1c501c00400083e2800c0280225401460016640d10f040d1650002c00d0002c03c80d00c0d15048056203e03407203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 231022751 1250 231021501 231021523
    0xb03040c0906031a0915070e0604030203010e0c040b010212030103060b041409060601110a0308040b18070f050f0f240f0a080405011a01020d030f02040b0301061e030c05090f03 77
    0x5140c01000000c00a48281407074000444500c441321503503a03010203c3c0c903041c18030896441d00500f80c0029808600070805c0c403c00c0c2c040507120b41d040075141c0d4042421075007031152004c017a903c01d44c00008546014000c0c10a140300a2015100b541c4d580d40402c500e03400f040c00010001a202c2c00030310003940f1140d00001d040f91050180c0e00c010704009400c643c07500f1042e00e801c4c1c000384180c44201031202000801140203036143c0d80d85481d03903507151580450311801800803100e943c10081e9001400320200215001340848890340001c15181100b0012182c642c0552140121b4412507041016070315034220941c40156900f030a009410115200321941c490040824074643c8081010340643c0d03405140c00388118800d4000f08140790f110f80074000340c1c40902801d90700690161060000091103a003000030020b00076940541003036102e5070398031240d40003600301100082c0702407660001c50b0a0050381c0b50300c84905041c104250045c10742d0091040c030556024502488401c3e0b407104040d2001c0003010511 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 231024001 1250 231022751 231022769
    0x3110f0a030c0306050f13050c0c0105010f08060f10090b01020111040f03030908030c0a0f03030204050a030b161814010e060d0b090106020c090a0504020d0212031e040b040b03040c 79
    0x14111031401400a1100000400002e458000080f500c0e0030000101c58006a0007402c02d691079035031500c07000141100a000000c1400f0502c8a2803c041e004d0198034007a090250b01080c1007070a000940d464001c00400000f885201c41c4188998400a0350191041c1c45072150081461141d4900513409402e08080d40356182c02d0001d80041c19010110324001030300d100341d44004c1203660301c08034699a80200c00b28501d443d00980d6625000032a40401e442000e03100742805420203a40d080056424980c07079005903a04502e070002c105100408140e290400541410b1a1400001030100341c54400c1150180c16020284111400c4940c1e0045034000550701005044a50b668090001c0034050000d9805040c051200040041403190020a40300302c3d201c4050055001c03582d501e0551800360001501c00e98002c641007202601580ba0034103100f2090801c00011980c61400d0848420500c0071240d9060003104180030901000c000790341203a08882e007494115841f03884e0390a007130305d01e0400d691080c150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 231025251 1250 231024001 231024007
    0x90e16030302060132010c140f0105070f02031e031003080408010b030f070b0f1c0e0a03020709060b030f07140313110d11100203091203030a05010501170703110f 71
    0x41542c0010100d05842c1c0ca01c40e90216180f800c00003062603401503e004031040e2416012454952103180740c517000c0c6000700d0b50b041d00a4000151103041141035405412a65140d00c100840150441100c4240c00d41d00c2c802940f07008440a8521081c82d08410380012801000002c070f8a80d00021041e00055500584225070780c9690751541fa008040001026019000ba01c030b58400280020030b03154103d684200c495860070505030340320020340c3c1c080840e51643c103400b228200706003101803007003130b81c80003041000300340302c40003410003070704e050507561040c00124104203041c89031024490503a0b4000240180c5084e01c3d03155004140e61700d07001080c40d4000000302004111001d01003514200780305002d000707220103a84244e0103101c2424810000a0080900749100e034649052005041030701905d43d20680f4148000040080d001c40003203049000294808801e000042070140306150040000342090b4207008550784105201600050a840c1416900c280d00c3c06041003140440e01c1031a4040300e40c43c0d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 231026501 1250 231025251 231025253
    0x3010305060a0b2808190c0603050408130b133023060a0e030f040b0711060d0603051c0c080c01060e0103060c1b210903142410090e1603 60
    0x1490513030328416588207105e0401e001c0a20380708030f21000001500440070184850412409501500c4050001c03100001c2c00c0008440d089000c030f80c0e00010b4811005150380d0f517105001c1c09009924135800c1440720343c60f81042c000002402031191207803084551034407036041006040140c0540b022043c02c400603c4002401140c40b800420600e07c203015242d400c011402e0281d00182d9240a041c0e03071440041d004000030b01c403441d200c001401c2001c1c4140c00018001c941d05001c00c64640011580c924059207030030041c01040001d011003122403441d4001c58a9145986100506481d80c010707002d05400700009000b01c1481e401e410400103450113845c140c46a50b03603031a0600080840622000020710000c100c0003c802070703040000c10041e04040c0f00148021440e18418040042c0c04403c414040c1c80032000000810180c40c000340d15843c58060700b03820506d03580500751881100d2030401c24403042c90400041c0c0320103007401d805a0300d5000c80000c3d442d000e88901441c041443d1000d0801c0022110004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 231027751 1250 231026501 231026569
    0x3030a080106080c07110f131109010905030604110103090c030b012403150b0c0f06041124040902070201030209030109110102010e0313090e2109030601060503010305060a0b 76
    0x14100d0340c180d40d550f101c40d80c5200101070316018a8000414201441118804030b01d0f141d00c1803103520314010070100040f2000c0d0b03259402c0f245440300c9044a54000303c5c00d641d4568200940f4001400190003515040c0b510360342e8140303904840e02420303041c1603076410440140410450740d00d018607030010b5140b819585502040c8840704041c102e98521521803c44450324600c0380c001c0304c0000c5201000c9c144824148800008250050711413100144100c00b01407440d00810407046001c4d034000c29401c946080c0c04401c0c86045520b4419401005003040002d130700200f41042150108c54891340c0040c1c6075410307440102d01038802d800c81260b0544c00c01301c2d180b0a020400d0700111280c4000d0700208203c0c052500016120300403200480c005001a07101040180615001491065810815552240c1c0110240481100038401c0f884040c40c020030404000d0404002c1540035021504140b03003998915a95a941c42c40d00611007907284c4d40b81e107c440c1540d12034003440701f02070b080482c1c50b65074800c00113568 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 231029001 1250 231027751 231027767
    0x3020312010608010f151209050f01090c050a0e160c151d010605040b060708090d0c12331e0608161508070c0507030501021306030b01021f0c05040503030a 68
    0x2d0070340c48184440022820b0034898403a24030300561f210a4040250000303104002e00f1000400da9103801603140348141c3d054288944c0701107a205040c154400c90070b210612034205e105401000312241f011040c002124078201040c50004018908494440d10503d0400c00410600895000440c02c00ba02e61801030307010004a444204e03200c2c001c00803103554008020694101c60300c1c02e80c2244080204001149000004218001e030103001c0000b400e07499510560814032592103080401829003044080000f00700b40b8a00c0d25011024100c6403c00b6851391b40d0040000b400019011035075072400700f40c801d41d100240c680c1403546400410090303035074009141e03d17000c0c0c1400c14000b960f8660780200c0c01161045411025140b9a03440c04034541c6ca00c03105484202002c0d4045c0c0d510f1003120030000014500340001d090740070074080b907005001c2c0342850203401d03205464030301415908040c42050030400420882d070303400d04251201040c80d4281140c160b40920603604010703054000042d070b11480d0b0f6048011f0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 231030251 1250 231029001 231029009
    0xa051c03020c070603240f0902071b060809060f011406031f06050901030609050c030c03060135060315042004110702030c060f0a03050c0c010c020a11010314130302031201060801 78
    0x1410b1b526480c07058115580d001401052032441c51200305120f440b0443d4054900b092081c154200d90400700c8100002c0c0c1409944141d0024880384100680e0607000d05c0340580041036200c0a000c654100b802400710b5411141ca054011000880010030304414640302308a40122840c0b4118690384401e001050350740481042c80c04a4100000002c40303610390301c6aa0700c659808501c1500b1525441c08003c001d5201820140c100094940c03030b1030000010340c1502610b44e51089041e01c005205d80e02c503022040c00200200d00c0398200000582c1d401e1280c45c06c055126501001d031101c0c030f6002c00d100c41c1e45040d541c203807070740c01c1490000c1d0324a0909810000323040b414000c80888940c144142e0801c00b141c80b0b50100035040600500034180458000c0e00b01c25048040311010300e0820f40e1300313103500b42143c51400303c20740180e1000c5290360610051441806160800303203800c1c050b0b10100f82c050100c00f81e001d882e00315507203000458070060502c00d200b603034041c250f03d46116000d0350f501c0c1c80081c4400c1080c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 231031501 1250 231030251 231030281
    0x6020a031d0627120703030e15010905010b070f0b0a0612050106090b03010e030a0c02012d0f020d090e040816051e0313030201030513080a03020c0f0a051c03020c070603 74
    0x2401c0950481c2c01c0318000c3c0c03d030180200007003490560310344010340211104509054594106540c4240c2c148020303d1890414001000ba941c90b008103101691010303448400390103401c204000108000346a41440c0b0f9401142c2402c054883c95501c10003022640d2007041c401100d00c0800381040010f40180b021102000400e02145c00035004050032507554502c000a683e0080183c440c0e00c41c05110840b40032801410700e18038100c00c01a46281540604e481c41401d1624103100d07071030b03660700044500b43c0c8000364801401c00406440300507011103268000c0840d000d241e200050104541d110071075404c6c000c1e505495401b0052450100c0d950f0000c203049032100000d1041c5083da4100c00070079941243d440304d0102000b0341ca140c005400620010340130580d451007054056010682900c02403000351410f0b640183d8408000340c01034140401042902ca05400004000000c510006030720034101d140c00c00400001e9055420541c024480c07c1c5e0644890300440c007000440e1074165104601000402c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 231032751 1250 231031501 231031531
    0x303240b0714070503030910020708030a0504150804080405061b011a0a06020604050307140c0a0e1e040c0306050c1606090c0506071a07020c030601030b06010905030303040b0406020a031d06 83
    0x203165a8803a1440e015054240c3c0c1b0a00c40f050662038555090000e01e152030040d02c02003078590315024119403042301454045a0300140802c0710f000300c0903015007012420724041400b0b013840d0b660701c141c4d40304078030070345101d9a0041a8035620408110700c8001504000e802005425004d04c0d203400519081d8a07141c1c400c58480e040050101e00100d0820711981d80000913501e8200c103580c49642c06244182c015003c0d1041004002c41e989442c64080090185c0034010005481c025020b502c42c0f0828103482080020304000f031000064120000b2010782c1c0c3d120201203800d98655101c1400c500909803546030081504620809200d040d82c4812039640c0107211403403041ea1a80e00b072101c103100d1074000a20002900c1c5c1d00428a0b50000400360b084103d070300c1a1000001c1101c0024a03002d000e80069440b05c07103000522030f031580c20484420044c4010b902035420742c54a03440c1d0030324800d0020700203031802e5000610007031158880d500c07480c18010700c4031100d556405002c540300d40c0c07a84d0485030354111540701c0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 231034001 1250 231032751 231032783
    0x9070605030c0702010302130e0709240c021e180604050a02120708060a0906030602040e16090303081005040504120f0201060f03030507080f030903030919020108040303240b07 77
    0xe5401c0340d100c1c0040d0040d507454010590b0044000303600a00440c2c511100b10380b40456001c604803030341c0b07024120075a40c44a0300c90038181c2e0220b00711042c0088d10000d02a000d01c44800130f0708601c4540007542c0464020524030902101121001110002c9a138407403070022000700c6200500350490702440c4c09890400681c0c0d00c0040c0c160880c41103003020403012400d040040c914610605415a004d2006007442d800350f50390309901e400351025a001260703199008101030118031010a4a10351040080c0c0300c1004c16000b10b08058002c03986400041c0c2001000c800041d01020103030280301c000c0030054820085444c3c42d04119400e104103010714000242c0c100c0307a035503007184140030340c9007516080103000c2c210600d10360b030070750b8164001b541c1214009414400ca80c110000348002e10305c40c1078140b020315581d1034040601703800c010140e0a491500c0c130000c05c40d80c0140c0d0f440030249030302590600300024421800d50301007a025400e907508144001c070940c1d000c1071051401c4050184c251260221181da00c0711 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 231035251 1250 231034001 231034007
    0x4150801060c0807021206090a0b0c040b1b07180e063417100501080705030907061b0f03030c0e040e060a0b011b030f0f0305060f041a0612090706 64
    0x81c814000000c00300c4903071102180d0104024900c10f480241021080e000e404079460038181d003194030b181b058000120b40810b000c03c0c1d0301020703840211042d05501c2c0a042c240c4004041c0240a021100b01204070654100d5100400681010741001c2400c20210000143c0407005007010035002241800f807400880c98500c4015012903282440203500d07101c1440b1100c6102011100702041030812442d9948040410504000c482c040c1c0c8000720026943c504041c005411700401a048008101c000c10401100c5200440d0744c3c1e080d15170500d0100b03101c488600d418000384085060207000358100740c0410b004c164140d03002c44010f04840e02d41c805035420500400044540c0410130303c1464000900003442c0f480d01e5440051105014100f180c0c8a614165680000060b034603c12000701d4860380104074030b20340282101e1100b0040b46002e000900c0c1140104860344000020240520b4079414016a05503071800c0c2c40340705140141c4000c0c3c48411101456008c241c081e901d000c02805402c50206030544 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 231036501 1250 231035251 231035267
    0x50d0c0605090103060e04121b050c0f060c0f060603010b0406060e040c05040f09140a0903021b0a090e01150b04061d130606030504060c0f020709021b0109080415 71
    0xa0051204046103241180c251040ea011580ca641015503034000400c0c1c1443c000b502c1d60059001c0d0581c00b05895200c103002d001d1303060170f9811a40481654045c1400039500280da8105400d06803003c0c0d5a0300e41050114140d401019404040d03402802c6503000082c0700021400d00c02c0700304070000c4c0800341044040c88111201801608001140e821101c025814150405114421240352103460148e49060031101d080c038036040fa450990300c414800e003c3c0b1014400c03098001c402050100305284403a540079507520400fa40400c200d0100130300c200400d54502902c4402002e00a0307040c401046480d021500806400c0c0401401d4045442c002c00c10a01c10002d40b0159069616161a00d41c190290303a0300e42c00c524844542c0c0a0507092001d00008018096032004121940340441c107410640380bcae8040c0ca0203414494108103950328651407161f80002c1c80021201000001a610b000e0140312a0b94905018500e00596091442c00010001c00e0301c014021101c01c0300200e030408888000031a0841 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 231037751 1250 231036501 231036503
    0x14010e010b011b1b031b03110a0f030f03020c060c011d06160503130203011506030e0d050f0a0201060801090f03091d0705090316030305030a0b01020718020309070e0a0203040309050d 80
    0x10003030b00810b8001403040c402080b886105940c13440d8125540e564110000744202400d600c4213007004820020050700c444074100a00084030052403a5040c0444207401181d248070142a0070003102152003814002d0203800c0b040710300075100076a14000081498080e0560307a544000e040c10381c5608002031140807400500501040b120910403400c540000c8501e508013420800c641000107000000680d0300344500b50003182030310810000c807443c00030060210307840390401c03000f560461225040003941c0202101d095480e00ca042c60b1320340400e26000ca00600701d50708403948540c89c0010280a00900880081c4110f02c03e50340c42e4400313610b0b2890f5044405650034040f21034200c038000301e1800b80c05800581030410015003101c40f07401d810741100c2502100c5600a80214034001b090080d0b00559010b05091550280000d1810b1841e15142c8000721200500b8195850b034017101145904030140311000040441644520690a21044510003035209a400f180807641a910000c0c0b1410702c16031034940c007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 231039001 1250 231037751 231037787
    0x1205040822060212190c082b0501090209010f120605060f2503020c0f1f0c0c08030a080103060504080f0c010f14190905010b031006080c0a05091b0714010e010b01 71
    0x4038545d41e1090759100000380b001c8901d200244482c600a000c075028050000300c40c80000c5001002d40c3c01001c0850b001a00300300c4245004106810721641c0011148122440728a021006240c6800c4d0034001050141c1107175610541c0003a082101c2c10444001c0c02a054211065508109669906007000e10b85901f004016030001d12103207a1600c0c14150f21600e12901801941c1e8000c180031248405c45840b900365004103907412000300074091140ca41c14040c0c45220020740c50517441c942c1c0501030301d00500c0001c20603621500003800300030301c207801c0c0ca02e0b925600c51880d88941c00b0700c0d02c25001c2c00b514001102607520b8550304e424803c030400c01c0e9501420401110f110300d40034071959100039003149881a610340d0f4841283c0a51034800b044100c028074012140010303458100001141840d04140d8050703c03504065109221942c0d408120039004200340d1b00540d01d08110344203442c91801001d0010b480c2c0c3d1680f5006140d03080c01074020203441074407203008000c0c405240780191540010310305082c0d25 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 231040251 1250 231039001 231039037
    0x30702040b04140112050c04090302011b02030a0e0402091309030c03080f04020904060b030c0a06090518070503010501180e0114030f0d080c1e030c0a0f020303071205040822060212 79
    0xc558180d6000c5040d90040087d240142c401c45c0125040d24141d0000f2070041c0c0d5501e0703038aa00c115040c25a080d40d0b9001d440a07500d80b014003d001020501d03482d040714030455001910603110b59540711000b40f04889100148550308003802d01820b140d00821040d800b09850800180d4940890b04409106680c014003a030981d440b1500d414006200c4c1014140d0140319083c0ca01c6265610000010300800321503039100c2ca10b900304002d00018a4144155111481503102441b040c944c1080a403410b4460a190410560003040f000f40c0120110354000400031400d0b0700046800301d50304042262601040d811900c5c046001103080350361741d4421080e800045e09401c00300300f556040d100180050713001c0703607032030036980a18042090031a03000340ca4440c10303083c00003007040145800000c05603907420640091803c5180800025040690b9411806c80159072407001504005007001660300d141000c0c0c0880ca407410703d20246800f01c2e05280500c2c400b5201300c85410340b24658030b030103c0b40607040072a041c3e21 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 231041501 1250 231040251 231040259
    0x6020c0d0201022d071a060f04150b16210e0d0201120b2b060606020601080d0c06020d020309070501090b0a0e040905120a03140c0309060f091e030702040b041401 71
    0x2959180600c0c01c2130949000700500c0e004121001464055170805c031003a503540d424860100000717440f1041d1864003c83c01c011101d6111041000d04408070750925040c107a440740f403080c102000070381d2120001c288102000e041c0810241041e03800030107103100d884c1e25400040441c10400000413041000b4006840c034104861f0ba00d640c1e4001c6801400c0c054035149000c42c0000d88420003202c080f01c940700e0011600140301c01e00001e03000e104c004000500140c1406d5040c00303e4a512100401d2000c4240100d140c9158200720655040300c00d2040c00200854890070304919a94440e2010b00c5528005080d29a01054043e03401045401140710f0340c84100034440b03c1020300000d0070a4203010b03510f40c011001e20050440c5044010a60039031540d078005011118064800145080604010003e0f0401d1080000000d8000340c1070350403012200c00d42605030703903070318910340b40c920b400d0448840b4014a4a0040c441080040076001c1144200c1e41440781000003070502c4211060b603000a41e142c010880104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 231042751 1250 231041501 231041557
    0x2030408091e0d0302011e050405060c0c0304050405090f070f060c030c0f080412060e030306060f070507050303040906080f0105101802040308031017060c03150d0f06020c0d020102 79
    0x808410801510b546071040000c0004150903c070000540240c1d460701c4a83c0c040c003950090048140320050740421003800c050319000d80c0e03030304000c04d40000710500250000407070004106690003064014403d100300c0c50044040c1b0b480e20200000600740c2e01c1410000708911240060900543d881941e8009d50303031500e9101190706131070391074007901c4000070340c3c403118080f03406100140040c00320303460b503191030101524002d02100d503914081c9040350414002c4c08041d070795039011240d140a520b040551500307070301c1c101141400f0700703640905d600d07210010303000640610540060046864000a54100c541d4040390a400d903181100c845900d500c28000511403100565503904031032a078072a0050800d601c0b81d981c1c40c02e5500036103001d2025014008104030b110030084803100d0120042000d03081c14201407403d001140005010201c264802000c01d62040d00c55044c46000e494101040608000f201d0034040000d51044440120a00441110b00c00050050003240d43c07099031285400d01d6404599480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 231044001 1250 231042751 231042769
    0x24020a05061308070c090603050d0507050706030902060d060e0603070f030203070b0c0715031b0215010e06040b0d08072d1203020c011a1011060f06031501030b0601080105040203040809 81
    0x483d0702d1482401101d0100d80701ca071816015092100c00061590b0540c10910f10340307044000781c0020400308000c2c0d00c0010368017007120401c03141c1a045c04141c00b861840001c800e402004140c94a107498504001500080b030b441c501c1c0640405e60654003100e450724061100c0d80030a020181d0554403a1204202903685a03004102c142205000d07100c00980382c02d818080e80800c88000400603880c0c51071a511080c5458000384402501d00060a459481c1c09825401200500c82e6407a140b16a030000361494442e03422903800014014981c280981d854580112550806807083d240c2c0444907448440089030302940205018840084032980d100769074515030811444030055080607028030204076001000d0041203000b901c0740c072154010024003414000c1c030592458008003009004a40c0380403544000c100282c001280f002c4081042d9101008030b4a090000d04801c00210b401c2000003040c0b04400080e24010502642c407422243da8990800041c2c2c0410b48025010400400890007180b07810407031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 231045251 1250 231044001 231044003
    0xc100f05130c1401200d02010c0905030a06090203010204151701050f1813080739091a12060f160e010e011419020606030102070804052824020a050613 66
    0x100041c0b4018806410460342c00310300800505902011b00f00910540a015096a101c0545400001c0f2860301c3c001a0303032142c1ca41005800d107903a4041083c1952800c0d0100c0d0050141c907007110fa0f404000c1c480c0100300010000008161f000258004a0310340380c039040c4241c800720300401c4011041102c102402c944c48003d0440c42c0d1091502c00c5000000741284080c21005028020102c00140400b120400c1030b100300600b00740c83c04480d41c907444200b10010001c800c2d03a1142c20002649006004002040c410051a6560085001c8086070301c0130b000188072441880a020b510101c5d4450340100700c55012041240801b051140c3e296407003a500c25012400c4111051500c0b001c0740d00040e24a4401d98840b0b20200e50b040e008143d986891038041014541010042c0c008500d400c4498a44084d030340140e0160a1080d441d00e0305090300c40703070402c0f411a03106400b50b4903102215640e014548212905a5000d4081c00c0300e0079a82008900204030b420301c03160000c002d88890303980c502042d0b011411030303d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 231046501 1250 231045251 231045257
    0x20f011808060c090447090108250513020a03090f051e06040b0a0c050705031201050406120f1101030207080316080f0c1206060c100f05130c1401 64
    0x14000072555410810140102c402420443e681d8a121080c88192061036031303103c0c0c0300300403410070b0710001001140703c1c1c0320719011180560300781280170b07070203500c41450584641c1c1c0040c3c201e001042e100c5010503608680c0300ca241024844502d013212900c45964244200390b481504410f42450000040d0010030400c6884e1800160140086e40c1d0740d185041e042a081d185580120202a80c0c40180b240d8070b42801903520040c4a10710702961220030302400144881401503c035184482500e004c2c40503203504075230000680351117513110604411032400034032620348264200000015201c0140040d0800c180d0404883c180500c1551100d180341c60000001c1410140d007044a140400d4001014600030926104400b5940341500c1c0c004120340c101401c00480360b8030800920840388095021a40d040d201d20454034025541d0714002800c0c0e011318280d09916000300c0360741000f2841285e0140e450305049038000c01107901c5004000a102d13080b00c00080210000c0c3d4810300280202c290301c210300ea00145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 231047751 1250 231046501 231046547
    0x90a080d080a020a0e130e0c030a0f1103070f060206040b06120a02010e1c08030414120d0b060d050f0907060216051c050109050a060c030b010c120c080a091a07020f01 73
    0x1102040d03100306d2066018101a944c5c0042c04020102402503042e040400c030002c2c28200840d884180010b02c10f42801880e400c4200520f0780103031418001c1000405100e86445020341d605d000203134640b101160b0460b52005810000f40c0240341260b201c011002d8018010311140300c80f070b401913403104184241c0c5d45c0d111440d40c824100d004030712801007a4031032140c11183e03164145498010540122030085800036040203800da000030f80e2840542d17100d602044808180182e520020a0440c4540282000c9140c101420010405180f036a40d9005280c008220b4211a0340da00b01243c4611141074421032654844108000e40d152500442c1421000040102e0041c0c00c03d40e2514215183c1c60b8049516412419907035042c040e00748207045030040e050406100050741070000034541c00c40d100c8028a0b00c0f40325102071046501ca07040074103d240d880036903143d40c0c0c444400e0280c0030f98154405c3c0101c0d000e904101d20640340c1060145c4507455409020540b108025400556000d0404190044000910 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 231049001 1250 231047751 231047777
    0x11090421120c050a090e220303060503010c200610060302091c03020a02011b0203030405060c100c0e0a050d150225080406090b160209090102120c090a080d080a020a 72
    0x51040c0c9401e0861503c070750f9070304c1031125006819201c403540268800e02818040002220751800038003030b00900f00d0148100183e851605a00800c040d0700410303055842c005020ba51550421240c4031a1842104110300914040700c00c4c580d9604200c0e64000072a05000381001504d000350090414600008c11003915461104040c507a0b20360100750030360059010041300f07829540c00001003109440f5404490000c0e5003160042552440b4a224190143c480050100204001400300d14ae202c0c0d202131061114003d6501d00a203054600d10303e0a04c5044107540004041c40e0202090003a964800410350b4410500d044480003074000a642c00090480400e81e6213880c024801c20b40502c42c801c0b000300f51254240741d0000c0c51010749802c0313145007010810208461700b90307003a10825090341c102c07103650039640d9200e10240a4000c40540d88982800401440b40108200b4050f0007040f2064405134141c5946500c510342c3c902e14290960081040300010070180e2805400620b00b401e0a810440344031449 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 231050251 1250 231049001 231049037
    0x40e03030a0609050108071202090a0b09040f02210616141b0c0d081c1107080c0f061b03040305041d04060b0402040b0405040b0301090212060411090421 67
    0x3114000c40741903440d4010b000c0d0480d030b449640e0140108600401c011030506249170f040c189001d90180c840c1c0600c00c001a41e0020541010680310700107064010542043e01d4103000806d40300c2d00c103c0c440e01c18101700ca0303002c03d0355803d0100c814800c40d004141c244c031200d104c1e034200c88030740355a4402c2140b01d10418070800340100041941010120401c1c80710007a4444040c1020703d500b545070700c10102000040c001c00c4541c170940e1a921020390000b0008e20840032014020220f110482c4a0554003181d50420f001441001d0b100050400e0700791001c014140448540303403441194805440c0c01d52800e00d2a030100d0f21400f0350760151003820120700d01794840c0100803002401c820141c03000d14000d42084100b000b035001d0900e4290040c0c5d030540c2090f08107070076036465016500840d4041e0390344a128462595003500704251042c0c000d00050900100d00da002612070101721000d4aa0b9481020491098102074041d07510590308161013405441001040302e80960070f003c01e440400c407140400700e00001c5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 231051501 1250 231050251 231050257
    0x13050408040905012120100c0b0c0309070308030403021f0b030c0109080d030209040b04050906071116030212010e060c03060307080105090607030b22060f0b09031b040e03 75
    0x402105496107407071615038042c0c01d48005810031095440038196202d11a0244019041242d40c407010012036200603408003001681c20440c0c0d59840000d00c500072010581010081e60010b01170b02a52209544003a041c414a20080d00d00381e01c980c1c007080c01000492038520145070014400c0c41035440e01047c0400b42002c41c3c020001c04002c440d0359403042d5066140800070301c0c1291a00382000c030789480c64a1291910f54a41c69581801d00d900000d01d0421680d480e40000481d0703800401c10040c40c102210500d42d1040d0469214010903048001d50b000d001c00000d0a40009041d00d5140c4000e03070965003400307072150850044044940d02c82c080300549020134080a0b1041140400b2181c4a00e0154201442c18085602c650b015074503002c00d01c0b5041d480810940d9000c2101d0602040e4040a1030120740e46030261484441200c2611812814000c0560020022aa240e4450341311030b9403119100c001502c03501c8080c6506900504d00c50401e42c194000d800fa5903e002480010783c4409522140e055074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 231052751 1250 231051501 231051503
    0x3120203011503060503060708070f021005090709050714030406020703030f021b0115050a14030f1006081203060f1201020906040611011803090303140904020f0a090e24130504 77
    0x20000b010490301a0341446040000c05045000300101d0401a5018250b600003900c1d54040000c007180d040301d09070007081008168024410104642d160140301a07860310070343e0280007461400c0c800031421261080c030742d0081c00740145611914644856a0b420003e501c5100110306054641c4d01e0390000c2c6505201178034404001c1c00da41003c08006d14403a90031110f5100b19000c900300c0300f0405108944500114405486070407861008020520000038502440b4281284840c0305940d0080b400e008260040d404075400c10b0103c800320700c4500813204a0780401c994043c2c1090f82e0414038001c525007e00140c807083c050100040c50130110300c000c03580c42e81c81078200303502007401408008081e000901c5601d130152282a03141000003079941e001003041d142c0c0d200141c00c0240000c8114468041d61085030402d64004204550310b018000800d02c481e007140710381c1400f1540d0900001a510b80d25030400340b2844208000c6e6404082654500c0c0184c00d501da40e00340c1050300441c2009282c01203108450103a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 231054001 1250 231052751 231052769
    0x7060203031603181b171002090409060219020d0f1710050901060e1206011202090a0e070e1e010b041a0403050106030b0402150a020c010804020d0b1f0602030903030d02070312020301 80
    0x45003071160b158000040303d904c4004000558010012200310100e080340340e95107200c17405032781c4d030054000243c041c101d502405410702c1d00c0010740504504c141501c1084a40b06602543e40112508400780c603240300050030b407804180c048030485074140c24020b41581c004a1241e02d149210f40f1840450140c4000360071160200e048052014190714010344040e4a40c50400c0080203958140704c0300040e90090150028000c250303040c003080d182c8055801c420001400c05c1d040b82c003c1395403083d006c4600f40040c4d603e1503141c1c5041294210310400183d400741610240081240f1b0311307240808415101101140760045079005100c0400000c0082c0101c070004d50044081440e05c0c01d090040094220f00c1c08901c0101c1c000c01c1000c104c010390003040030130002000742000340075035035180080740e924010454000d09103144070041060000c82c1d00a440f02d06040c03501e200760440c3e1224001c1e80da9209600d922079040c0d20501c229075140000d03400030031809200e0310301034030481d1905000340180d820a03044460700d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 231055251 1250 231054001 231054023
    0x2070e2e0603110414090c070b04050a141b060d15120309150e0121141501030e060c030907180218040b0105030f1b0a030911030706020303160318 64
    0x5540d454051070148441190b150740c503062501406220220784070300c40e1801107801c40000b461f070382c2400040d500390756005103440711280752910b400381c4c4490500b00102c401d500742c1e402e8014008000520750203158080412800d9101384182004041d412a00001a1058031003421707152070030070b040f00340c0000e02000d1411500c491092401410a00c101e400440c8a240c512040c28603141c1e1003003c3c48800602802c1c407410010605c00d115800501508103411400d041c20514500304007a05051031150b401c4c00042120010b1650044042e41d4814550241075403211001c644581c050303100541e08000540b044800c0d99544601020b00d41c07406118442c5401ea012610303152003c2e41c078425008a007011031381000304015010001c4c08a002c00743c50560f00507114000034100c460858401029942e40000040e1584501c01004000c0c02107010f040310000d02d0f1036100001d90a00107628030940f08190055411651650040014001001040420035407030305041e811400761308242c405402e000b07c648140c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 231056501 1250 231055251 231055259
    0x130302150a0503070509030102070605010602031c0e07050f0301060801240f12030c031205010b0c010f051b03090c0907081e090d030902241b010c02070e2e 68
    0xe10300303595540e06100242040040c0740e6039407003400c49030301140c01d0800700d4585000b100824024050008000c00d903520300382c004502950008003030418010600c1d07032914100c66030b440460550348a81428440ba500c20b4009204515143c0c00a81c014074000d0000103906903500c030900c2c251641c0e80f500c40c40c210b44400610008049800f842d070081c0828811000c0010f2900b8103002e000100319a0203402c01c440001190101071050718000f141c010359000901041d40c403100301c031078581d011100303031142580f90190f101a249028020140308044441060301d0446a00d0090102ca500c000d000001c40c0c02a851103414a42d01c403060540100007075515203909141a0131482c800c10034240d02c84464541100c100079030040b00003403d0340d01082c00d1401140f11400342c4040740c101c5003400300d12151425405085d0704401c02c490b003d40100c00039032110b10325105084804500326103031034000b0001604004002d00840f0482131a043d080f207880e064043c1d005000c3e207030100040300c0c110304950340c00b120048200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 231057751 1250 231056501 231056509
    0x105070903050f010603030e010c0f1a06041812050c0709050705130e090d050c19060c0212120a0b0a080d020d02160f0905070504081203010305100212040b0a0b06130302 74
    0x20f482403004001c0045500750f4402505a655050040381040015145001080484034981c0350340c1d40d0014200151407450810100c150000712070440c040c6103840c010350710390f021a107921701401da080440803540744000001100c99a008081c0c0340f46500c02c00d040001e03410002c2c403519100b06802d0303031281e40710f08152510601c251515844428132035089024404000408580e90008401038184251354050080c09681044091664001c004c540b420206c01400725503044003072a1402942a100c404401214588840c00350b0410751650040b8080003d07a20f1b9026806648200c2d0010522041160b41d1018203241c22620716500d4016040b030b80d040b40304180c0410410842280b01c50410036403030f00345079481c40c99100500c5250b185685400c0403e00e2140034800702c1d8041c100590594000c4880c4034810304841e4804e200807a502c1c410800700064000708c520070350b040500a91156401c3e40c46039194070952020103003d206e119a91043c0b46002e0b0f0341d81d0001040c450100035a810a228a140104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 231059001 1250 231057751 231057763
    0x9060f0510050a030c0e030f03030f090303010e1506131707090b0105070204270305130503060408040e06032b110303040f021c020d0b010905070306030809150c010507090305 76
    0x68060302031248565000da80100c156a03861503c2d10700001c140d200c06070101d804850144506806002c4c51132440002c280c003000562242d8400d840340030311519010300d401da070303884248030f040d2111041c03601113100040034181d07560300d03080e00808031400d19a00340b0303421090502980c81a2801c90760b001018524040c10b000440082c003046600300804040c08001808a2040b103e000348901c0e03980d140512280144401e486880e0801020740008c0f680501e400f918030750044d02d01e5580d545943c0c3d000a840d1500041c61446907a001c24030a04051908803485010031000c1c10450303260046103851400340044940d5400c80483e80c05800e0803290009002811010b45885442015041001000041406580712400340da034141c4044c1c00c240701a54101c280d030401c0a2000333510100803081c103014403000804043c1644c0045d00308100c1a00c3e802016800c8030142c7c400141252403c1c000c0885502d4000d00700c00d505516000f0f41071a12207058001c4c0e08550007143d540c2c002c10309411003841404010454 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 231060251 1250 231059001 231059009
    0x40e07120b04050c0d0e031308010507090f060c0807080c16092417030409090605060a050306060a0b0901091806031a0c040e06060705030a02010504031e09140409050709060f 76
    0x308424182000e000d01030f0b2180300402d0348496262901ba45038110304100303c0b9000c00711003504228403511055014041e0200350351180005103404070200382040321007110011620241c031045400740c0540e55404441c0c21260007550f05440500540e041c0c88010301000103044a46602580b801c0d041c11300b0081150980300354003000041030468482000c811541182c03d4a64800c25606000700b01d881440c13940c03185070880d0b1b903403504052a1500700030040c1c20040c0031300307000c41d00101c0c80e540300c0b003d16030307110012107030540d00001c0d0300f404120400c0700314010108504185000c81c00640c0b18560321803600803080610300480d503581c004005022140752302c01c0081d205c1118419181c02c0111501107180900c0c05108040d4035102c01141c07107a0784070310448503500d074400700362625401015030180c020701d8101d0303082e0042007001c03040941c1a0b01c4140c0600c0100390603103c6040c0300341001920700d40c280c040d00d181074019079521030840200d9003c018030001013440210203c3c0d40c50401e072103ea480752140d0300c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 231061501 1250 231060251 231060259
    0x210206040219080a1104060f030f11100e12012316140f030705090a1e15022503020607210e010c080702040908030c2109120c03040e07120b 61
    0x120500040f02d01180902c3c1d11a0800603501e14402c803c40028000c0007281d001d00300c04001c0311800810410b072041d0b1a481e0901806440281c00000c03002e0040580b4020031100c00103240c1e40380b401443c0b409116100c001050709d03000142180d154a0079139803504d0310417211036910640204011b0011812554480481514a40040c080c885044090f1aa002e0b001d41c04242d0200840017526503031007201622544440100071581c01603481e80095140c0000c0e01c056058030702522000b003000c0400d61070b80820b40c0c1640e4010a000c0c00d445040014001105681e40c0400030112400005070b528500239000c40c502400d24074420045074202c5a00c058900035080c010b10840240d807642582e00301201c5811550007909160f82d0b540316200180003008402c100506811010081c000d00e007041c0384c042c18100501c0003000c0d0600140c01c43c0040c03180001c443d24030850703219a500c2804c84c0c0200024001918001080743c1c289030712030405090035074040b14008001171403c0c0036105041d55500450703c034180309035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 231062751 1250 231061501 231061549
    0x30905012307080c0d05010605091009030201050d0207021f05091908060103060c05070f11131109150c030a021501050d200303040503010e250e070c2102060402 70
    0x6103106905440c0200802d040c86001000650050090000c99420040000c410402c03507855040142c000e810080070a07000e041910018008640901e40031070940b03170161a01814200f074002298041d502401d01241c000f00b07903041a01034000710400240540d109030b114545c546070700d0401d000050f0000305a0b104003402c00303501000100c2d80890034506613a0032010200b031940044000382d48600c1002002014541d54038031202c240842c0f416400400c170000c446403180c1c3d1303490321281000d4079448a0754101a44042003040c603036140882e40f510040c2e140c104400d041036015a401815604400c0d101000f58011041812400094004541c0035140448005100303180646401244001104854158442c2c00d8440300a5680030000d5400030031004001744048501680c0094543e00c9000c0590801e96405e0180d000c51206446440150358840381041c8860340c460104950750b40c40d50105940701c900ea50b841322345c80038000240065407440c0b90000e14441c00c2c50310601005000580148200c0c0c8514 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 231064001 1250 231062751 231062801
    0x706050a0c0f170709030209040b1005042c070506030a0b0414040b0a15050316150f080403121b020d081005030717121308070503030910051308070603090501 69
    0x4a1004059090383d1880b03041c540c0d8558200740c80004154002a42c03190300d10f000c100401c00c0e144000f0b071094504802c141c140e5681c0e90180400e4845052140c4204254031600030b030002c820b40c000075030f809043d0045409440e0b07920045401980207503401000d1036256040b00509013068007401c04801d00c401d001d9106450b0613110410006800750003402c0703541d1243d45010305c4800600f1528040c1000906459501501c940c00e140148580e101d0010b81c0407066440c90100390084510407001d00c000c1d228944680d03030780d03501100e0f0344840912403450705030354418401105084540091a50103107800038038103600c4520700582142001090301c88262408036082c17040e0307103021509200b22403240c2018090341c2c440031105410121190311240040902082020300031020150030012940d00c0000d46403941d8481c1c2c107143d120302c180c80c016504000e04014400e8005d1181e40140814805500307102041a102c0304683d0800c80315602030800070751601410810b100003071060340d22038004180c0780390f081414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 231065251 1250 231064001 231064007
    0x1050a05040b0f04020313170a0903080c120406050c060f151e040e0610090e1216050105070206071803020306180a0f0b0f090f0a11060702060706050a0c0f 68
    0x110300800740100c0c0c03038984072100c1d511480c8550003001001003003507440e850120780c0109410050700301903030074910040c2e12071420041003046600240705030361007200b03130b900b15100c202c10381d84403024072000ca210340005088111100307000380018010b9036503a0b5030740305a0f455079070703242c00009020106c0c80030616080c080c40e0400745404681842041c0c2d0034280c0721140b14403441584000440058000382803a5120040b5600880c1c424403d03000c0c9516a1001e40d1501c40c81c2040f6903a07074411445a5101001444454941e000035101c00318403025460281440c030364800b0700b03440741a40c035500541d1100d03090003400342d000308000f21039150003894071000f80d1031600041c0da0344101400d1211000c0c40703461345c0c940303a1105204205115070800045a9448003910300f22050074800c0b82e0070340c10f541810000c03d110490105c0e9482c01805648010b095540254613020303109450007000380e6004104111140051321110b000c0c03e0703d00e0040c0000140703880d0100c0c514081c2c540d110f440c403081050b10301c0c0c588401c42e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 231066501 1250 231065251 231065269
    0x70608061012050c042105190b01033815120c2106040f110f21030c160306060e04020904030309050a08040b181906081f0807090c02060105 61
    0xb2002800318440c1c43c1d486502c0042e10894200d00c0e00c04081c141080c06c07136044a0a501c510701d00c64021203548a4481441c2d000000710a20010200704589e07004102262803203680141700d04600480380c21407001c1d000c2c40b4018109010708410f8440071070741040001c0ea02149426003180054807500b500d2100d014205071030f000c10042e040c0c440e4200034080ca00c01250340135060b00b541490f0081b13498030b05050400390f042c00c020b000103d1b0300c40700300042d022a5082c400000b400041001e09554450300340f6451750300f91605103c0f0211040d10052040300e40c654000c100701d903190000142c5100000f821400c180c0e058840c1c40d0080d1083c0d0440006010040c0c4849103403647c82030b054500003800311003034607240d03041048212000c0d0850002080c04100c80846800034011290f050521840c01c95406007801803100c0c00b1440d60400584542c01003003218001c00000390301000710421090703401c1206210b1b0b8460b04854114a0b5950b001800500101900b84200900418180000c00071585004001401c0700 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 231067751 1250 231066501 231066527
    0xc03031c110d1503050115050604180b0402041509090504170304030c0609060b01080f01030c15180f08070906080c0d02030309150c070504060b07060b01090b0c0706080610 75
    0xa03503507012000780d54400400755003030000410b5007400a101c51865101090045000945941d480c14807124080e00c102e078910821250007400031801c03c1d24088103d505880712480500c40152242855150741daa14401000502010111402d20070800c04000341800125007008a0302d62902d000d0002041103500d1401c005c1c00c1e4142810b43da540c9914045030000040b210040c02c045c20440b03100700304403031504501054582a41c400c0300c503554001c10384c18409420720000d01040400d100511a000070110045c0b0100c0d00d50900300d0300e00004940e9403100c3d1156a100003681c5042e4181442083c800380301803030060940000c184802400c00000e103271154070480509108240000c581c0c0c0464030184140d54401030001c0540b241211301455044407644030755490316030750064110104040c07426115820503076001c01c048600346422603442400070890303000c0362414010f80b1800000d01910000c010210600580060907141c1c1ca842c80107040c03000c1c050000e83c4224020845000060b070320400c441551 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 231069001 1250 231067751 231067807
    0xb04060504031701090609050c0a080f0a0b090c030405010b01090f0509060d060e0703020102210f03090f1b040b010806090f100b0d020c0f060f04150605060a0807020c0303 75
    0x3911039103401da0b24000c10f45503140c1190001000007030381d101d284c1c0c4941c080701c60700c000c00d05c643e540c0d05211440d50f02c11030540e0380210b09100d000c50450019840230303585c08407100700e00140c42106803001480c000800c80d10103005071400010042045028050301641e41020f0800c000700500700f00b00b00303207030712150b0090901070502e400002d255075807000b0700200300c1034201000f00038500c5006640350312000580400c0e130161051139510b81489600a070091034859101e4002400d041a150358210654809003003140c052007910351400c9000030600000c5002c600b0390884803500810a0300b4482910200d004050501243c07004200c05600c6461758198882c60302c3c5651000d6544000c84010240980d401070305800b0400b00701120044940d5005081c041c40c0d07201100c0041c00d5000e030055584400711000c4011482a5021400142c648a06410b60a41002c800f080707240d22800882c0c66504806400341c005040344050000098041c040781e00020f5080e80a5445d14090340c125118000300c8584400c04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 231070251 1250 231069001 231069011
    0x103021309030309140d0f1119051c1d0315011205010906150504150501020a0f05010609021201050907020f1b010e03030d05040506010b13060e0f041508010b0d0b0406 73
    0xb05842540a01000d5900c804011698130b1011012555621314040c0034001c130b0003420b10104d81c41d001e1010007400011480003000e0001100702c540c03990fa07051440884640c450380c136103201d9120554240020710105961141c00340d44c100c44059140c60141c41c44107019400c4545880c1030008a01326140c10f607214018144041410780c03410500400014074082c14072450405460321034040d289000c0d0496101b203400b8410149944100341840751144241400b5a00c51540b500000303074180304540ba141e028000015045540d06032002c140d0744507c0030902c520241500500080c6414801c043c1c00410510040100880c10b10140c2d07601d01c5c1d180b090040f07003044900030404d540c1c0714003c0d8003480c200c0a003e490b112a1a8100381c1d01070175050364102c03660b0140d00b0000ca402c0050030103443c100545001e401469038544101501d0106482c85e0301508030813075803210100da13100d0b40140880b501c0011450b020740c5203407c03031307580c2125841c1104a04c200e00c0c0e44140c03004100c03054009900a47c00003000a1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 231071501 1250 231070251 231070253
    0x3020a080c0a1d120a141524150301090501030204060b0a020c19050d080702010806120c04020307032a12020f0711010507050d0807080606040312120b360103021309 72
    0x102031a071024200a491242658110400c1200200c0203400b1140000700c4503c6481c80c040400844c87c101da1111081131042c01d42d14654000405500a0740005041c0c8006d0b60f00940003034089074400d8016900440e1a0001002107061910501000309440d092141c1001b068810007500e0b0401840301c075110704d5034034840204606081088000414000b000004c1440c02d501e4001070641000000b6404580a540000d015081c0b220490b407010258402800c10202e0314001c0000941020703090500b0503642c0d0041c007a060b4058401c1110710307888246401188407400600504604041c0c60b03005015005009050403440500151b44245070b120b0701d444d0310b02001034012900c0e07004d001c002620922484915400311a004080c8a01403140d03682c03141c03003542c0c5d04400e1020900c55031000409940802000000451045014500c1d411b01c9144c049019501301002420280c1c5006200e445208000d21a00c042603480681c1945045c000aa0030082d41c510b80000341090300a15503012095100e042c0c0c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 231072751 1250 231071501 231071509
    0x120c02011206091a030312070503130f1103120c10020f0d0504030804061a010e041503080c1b04050105010207050d06060b1c05250f020c030a0303020a080c0a1d 70
    0x10903078024a003400c121107951900c0c2e400c007030b1001c0c114204203080044000306160070040211340c5060350801e8401801e48581808507901c3d44010210003050b603481291320009250f4034400044107010b0085620713544c03070f240d0400d420708a0352107170f101008908000f610410000481c2c45040810300110058070b40b0344400c40440b6520900070701080386407402e0f00308420550001403c6019500446040009020740c4140884c0c014000c80707260302058900523198540e20b40740d0051030203400c400c164009280d03503c0da13800400d034000b1340365202e480c0c10102440d1091050101342c15034964080320b06214652401300003030b465120030701645002d80c02c100007600a00010760031250040002c2561070342c1e20190050880307183c6030800b11040106083c9030210320340c451181440300074450103241200641c1d00b00b11058070845020070080c2d065002c2c078491030307049035014842140614007035200940c0d2042580c40061060400528a032480c91041c04090403040c0e00003100710302c94141e1900024441407410000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 231074001 1250 231072751 231072767
    0xf01060f02120a0206100b040b041802070b07030b030d21020a0212190305060904032c0d060504020a0b040b0a0302130b310815041103071d010b0403120c0201 69
    0xca80b4440c0005072081c91941c00030300300d481041c886180011244e2192100090307440f440c801c1481c8040140b0084c40118580c0440441c00d807101800107140c90865502c107071444c5c0044600c000880d64904008034030382002d100d000308070754083c9040400c1c1c1c14040750700160401d054103802040c40e8081100c115640c005c20010008811680d8640d0721162a040703442401c106682c1803000090074180854014204801443c0c081c40e4107886005a00d41580240215004040c80c80307075140061004090180c0c03240a00d500b0481d00840001c20240b0b480e0041c840008a00d91200e20b102d83d080108005540c019415103a03507030000e00c0d026940381407003000364000d60010f4021504074000061785114810300700c5881c0e0b2117045140c07a031420303012a48c641341182c80d00a10075010207800c010395900900701c113050103c0d800391007403004042d4400c0090100e8030340480d0b50002c0c00c91089924041075000b4007980d11070b004000b07810a031454a8295a00e80c0e4010080d619850180454102807900b1a80a8004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 231075251 1250 231074001 231074023
    0x302042016141c09170303130c0f0e04020f010903030212030a0b120607020d0519030203090a0f051f1a041508010f06050406080106141509030706090603140f01060f02 73
    0x3c41c0e840d007000800641900140d1020340001c9010b03030900082000c40c290010300a61408005141581d03509185036111000e01c580c102c41d02095a0004551030007168010006402c1c1d8015010403442e0600c14006545402c00e41a13040c044100410000641d00248103083d220038603e15070b440362940000b200242c18141031940d880102c221021441030000150203125140a5086803c05844600240e4003031060507512540c60b0380101e00c40c0f2185019400450300980d4040881d000a00d40d511a03601c000c104281c11601500869810b80c804111405602808800e01c8070401c41c41403206055030030184450010b5019945034a0400d0021703000802000080c050030009105802c88116070748010320a85c01214032039441e081c1d000c01d2241051041d070060354011f6144981c110b0020040000d64084041546904c840070024454182c800780680401490b0075240ea8001e1410004064207454154074052032000c8440d08112140c008294051304581103814460303030350800b92800700d00300740300b00b50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 231076501 1250 231075251 231075253
    0x23120d110f0a06050f280e0f030f040303020706050a050d0504031101110405100c1a09030409090f150e06070503061206100303020c1906050a03020c0f07030204201614 73
    0x1442400f40807840d08400d02c9040708410844859440c4000001102180c040403d17292059a40c1d09490400300ea10080c1c42c8142803080b2035415050107101442c0d9800140764280601c1c2c080740c100105030b01040711801030680b60074818140507a6800c014954011806000700e916100c038080340a15024060019075620a80028411171115035401200c030f43c000e121b068002c15101031544500c6101d401c486d51500c1c2d110600500d52208042e052140300c40140507200d640c0010040015012050310940408502ca11800d2101d0189820440c014044130010b264039181850603966500d0404144180e100c80607042c4240c0342d03160100441c880d0401c010030010603204941c00d10848000c40700805048a10a07801c4421920b1860140402022102e0711070326010f060a000780201402640a8418040d0500e0010b05260000d2041c81ca800325041c00c1e15400d4102c0e80003802541024007644920369200c41c0d81c407000002606001815105150355030f1141c99410700c07200c00304541607840407a20309482d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 231077751 1250 231076501 231076513
    0x51e07120209030321070c0203031b01110c070e0601031b0c030905190302030c041506030b06090a03060f0506031908071406010303080a14040f0f03120623120d110f 72
    0x705c1d020f00342140d003084c805070030607840c0003d0070301445100c0680c54940e0180146003041010381c003811003840c26030287c15840d500c9600800c3e158111102a10000036500001c152451508002d000d000d0405803132241018248a902c0e4007040c0c0d20044080342c99000d03c0d01d691030111030304084502c4002c9070817143d4800400415030401c0c40d82004a003095030700071410b8800f00c19080041104548403201d1071505103403040401c004070750286d0b0001c40400c0c4003a200a1501c064003000488a1443d07170002c813201036485030740f1103031800c0e139104d07080d413016054005141030300440d03220003084440000300030035039000080d054042000c45805c1445d000d80724012031341c0e1940c6074500580441e9046440340c016038540120410b034281ca442c001d60199800c04d0400e00d4085990311420b00c0f004070380d04140c061000000c0302c602d16003400c0c841d4400511500c1064006201e5681059982d100e51240a03032040341506403070300988070003095500b141d21103030900c2500c8850049441c0c3c00e00148052200f0301e40a11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 231079001 1250 231077751 231077767
    0xf0c0504020f0903060a09031e02030d050a0c030e0c060f0c0a05010609051603090206030103080f221505130e0711061003020913030e09070203070b0103050709051e071202090303 78
    0x504050b15280b0f50880503501284e40d09412801242c61400000d40019070300d03c417000c0b03e0a0000b0248a00c0d06641c4103480c5449402c442c1102a90000e481c9110300942d00c00e403884100b94180f141700e00172040f0001070802800c1200c001b80142c0141c4110401f498400101b004540c10100204550b841e44a80281b04103941c50307480304024601265000c17803074078004041e10001072191203402e1038141c2c000c0c40c203410769086884045040d08040104801560104042c5541c450f441540c5400d0b501d40c00c0c3c1000d00c1c0c80c01e255610303981a644c0444d8005100d8107011800ad03d40c40400780405840f07610409082658450000321803550700005489200d01448040c4504098050120382c00d9a000740c407210803545586051071482d05850304003900081d0382a145c0c0300319181101c0c5550300050940304a80c02d100c101e0300c03250807848007030780100c87c039901a040401840c4e545020f04c50b448585a41005070b01c0d10003180400280100904840c20442c00b40c0d00c1d80c00c031104582c169008014080c00300c903107030400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 231080251 1250 231079001 231079027
    0x5280b0415080f0c030706021507030f090b090709020702090114010e180106030c3b10020703020906040501150c150509100f1a060d0207050105130c090c09030f0c050402 74
    0x583c803804801d0081c032405012034180040d03c0d030210b841c07550060038280303001000d40c1070706007018010804140e243da003040c0c191005070041041d03440c040d0700d004a60b424051600742c42c0c24029404074100b240188041c80260f510b0075840c60440b10036508012140381001e0048171504010322840b54400102c2888804c03448218000c941071310015241001100c0f4120f80558150348100c8443e0f00646012a04001101241481480300c0c01c42d088215021410000082c00580016107800016807000c0c00130000d5140490a1540124054130100300c19410400c203078400464941041c030a0000c0200b0702c0c01000300240150019115641c420030960034149940c5031603a510610010b100e504250200507080828410408000f000028610400351203405100082d04811605e4900a90a00c58440401c40078011940b007030f084003440200030202494407506002da00d40120360154a440c050740b140f903801400b4402940e070450303484010a205803400c000c06070b070b042d00165001800031986100c1d07021 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 231081501 1250 231080251 231080263
    0x9020f041509030b160c08040801020c120f071709030102030703140a060e13020103090206030115090b030f041401020702030d02070602101a010309020307031703010905280b041508 79
    0x74280020700e4251511004440b1101c4600018002c040d1200116141c07078594402c2070102265070070025414080303500e0f441c20719009030f407043c126030b50002015031072a0418464085507011a041c3e071410000214903d045030302031440c0003000c0b091a40107071207502082405450001c14024001e550b6032608060050103402200c000d031600e90720450200703801611500855050354040d030040400355842c9901205003280490b4280d051507034a110b044050703161400198041d001d20012140c090700c00c404000c081c1c5641d03902c00303400c0c0030b424018000f04618185a054000c0d801030381500411300c001c240c103402486070b0307a0001d50621403c030660240640100d0f00408a40c0301780c00350360000041085c4c00702038408540243c081e04440008103841580241c0c4500710350b070f001504a40380c868403a40c0f05035449280f00c4c8888451007000c40108030401850161ba075010139442e4240000c0d07888440c0201000002c40304021145444070603031145629035a201145204024043d070705103654401c00c1d103407112 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 231082751 1250 231081501 231081509
    0x3190e010c0e041406040b0d050708011b090806060d020f0d0309210b0103020d0303140a1a010c0b0f04060b03070905190605090a0207080f18120106050f04050c0409020f04 75
    0x42c44002c00c406031498540b15032580d60f03241d0107120240790740701e008000c010b185040100b030740300c0445000040450420800000500741690001403900c01203c00c4807010412400010104140784106114054020500940100040d0f40401c4d401d681071000404e9040010009500030000000040c241540300d80400216550344c04698010110441241c1c00460300a02c05010012040010801400c00d500040705040c0289000610940001c00e202c0105030309172424143c0b281c954442d504c07446d0003c40c06130300035102420302244032846d0741e840342d000d09002000c0d050300042d12000501448182d8104401042c001000d8407031903034460590300003d0500352101260100600700e09e0480c140d45208440c25584010701c070740c04950307400007401c1c040d60054504540d49a02030100b40400c42c5803c000c0e040c9442d0503400206e03042142d0050105101200c50141d03056070400030108440e40310245483c6083c14140c40101d80c1e9501c0c06040d81e120f03c00da0744034400c1d0f140700045021080010340c3c0070340161 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 231084001 1250 231082751 231082757
    0x6090b0a05010e1506030a020f0a0804120c0c0e09120c01140c04030c0b07030504050a060906020d0f0906052113140604050c0d02030c0a08160618060503190e010c 71
    0x42d9894250350050300404945001c08003004400989503481c1480155500140929015244c00210701b4103809a4200c00d8060010600714001c6c0400c106002d2110740300e003c80d80c9412000303d1107607101d20b80c621800780300e0342441505d036401181070250b061060b03004640c40e4a00141d44d403500104038034001c003098040900d81000c00c00116001c0c0041000310303403c0f01d4021040600846c1081d203400d860b87d106a808070180001000001101e858203500d0744020285500c134108403503e8a60041c0c2404403180b640d500300703d26844400f11064001d20850f00b92001c0c1e00d800d984a0481c4400e41c08440000d151380380100306102c0400c00e04090040349459401d01c192070700d94510000ca00040e0740c4800a440013409500a4400340c03a440c28a0301485e407019000400b22010365000d40046600120079405c01c0025400c4818131120003040100140010400303480c040c032202040c44001390300c040c280d0040c1000c200002020940540d44059018003002e1628003c0105890600002d40200154035000c004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 231085251 1250 231084001 231084011
    0x110d081e04090e03090f0f06070c0305150c0703091418010e04030f0503040503030106030513080711040605010905221d0f1204051e0a1707030204051506040308030603030706090b0a 79
    0x10080c003100b5101e005d440941100c1c80340844004108011407101000d54100310240100d038045a41c2840d100c0007036009402810030310300b10b1034200d84403a000619821503130204000000029502000900494919904081010fa0503800146844007010101c006071010b40001241035006101c87c1c500a80c4a0f0b26402c4442184040640d00b074001150054680d80003400100042da0107038010940c491024242d00810810136521007105810942091359000900505c420890906100301000340c0424200080d81a01e0140020030640c62400e001c81d00900070084915944855042a06509840100070b4003c401c00e15081c4c0da030f0751284924110034071aa40000741c94858501c200c409841000e45256949035400d414410700040b078100e00d40d0031500b980400585070900840c0007403028410405084481c1c80c500400094600c040d002c040c45420284414048d0b030f0301c0794200c0301100c3e409100f40c0c1d141c1ea07604000a0030b50080c114040c12941c140b101341401c20410b052802e1240345000401c01c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 231086501 1250 231085251 231085271
    0xb040608070e1803040603020f07080705010b18191a0306040302060a050f01060c021c0215090a090605030c120106150305070f02060402150702040b0d0c03020a06020a110d081e0409 79
    0x42043d1081004280ca60010030007800514469002855809040b144140c941040c540d10309156a01184080d6503607559240c42045600d40308065040f55030422102603e1400c1c050580d046d869603050039403d105507250104452a800705c10459021755000701540c80c1858035090294450308101c9180040700c0c0782c200000c08071000714800d04c3c103840c46595158540c031850750a00c000d03291503020a51011081100c2000103075108198030301045440b840694484850302e0030711101030b82d0794110000440c103101090006840004c2ca02d0892042240c2d0a40c0c0503160304070681c01040c05030010300c5015486105810100c1d0903130005802445179603201d481460a20300700b241c6840b03054400030362005039140307400041c608010140070700d503000600000d814420200001e0106075882d20440c0c00a40c488001c20951400080d01c00041401c2d0001d40f03800940381e40e65681c1c030300601e280c203803181c1c5403140728409001c4918240c8011301c270039161880d0b290741e00590041041d009031080b01c013400d0900b25204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 231087751 1250 231086501 231086521
    0x1060809060f04030c080c072d051302091201110901090e091c0311030a0906200d050411060c070f08070617060316060f020d0504030807060e010b040608070e 69
    0xa80305800d02c1c00e046000d0f031110395044a108032070712815039181da0306100c2c0d174103291b00600c6400003d100c0041c40b503140d0001038010a0344240e9409121500c8202214208025151000c51800f5010a03100040e681da840c07400284141071480c440101e25807030004003141c000c80500041040803400d888101d480d503038800b0000080d4504498407813880c0c00c03112605522640d142c081c1240d070759850030f010861150100c1c8201070350f001194600d07081d41c3c60707258540c140072071440742d0380d02c0c0b0640e14004800c1146501009419200e058222800c003a5a03100140900542c0061000c03200d00017403615035100032214030599203010301d0007031031401c154070400014841c0300003503c0800c554840d290188451945000302c00a07050091510340c15001e14001d8109d42195032220002501581d110b03450030b001d07508002880c1070482c05071041400b604120610201300e040056841ca01da03c408085090004a51b43e02d01600c0e42d5081c141d040340c00d100f8045400d40003c200d85050b81d031503401d00011075030b07499409 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 231089001 1250 231087751 231087763
    0xb0a0f0b030d1101020408010c0903060e2116080f1306050c0a0201050c01140903040f0905041110120203130b0603060c070210022109040e070807180605060301060801060809 76
    0x194150b004031220454180544030469015445900050405503181c4050382550038054030680000c3c40e420003482004010300c40c070001c0613101002081e81096003294601803a5450f80481c00751007020415180d405681c0340341c405800e600500c00ea84400c0ba403480350080c0d800c4a01c0c110354580316a800030036600d10600654502000c000000c001c004c1803500151101d40c0403c40c0c40e01d455482741410000d00080c0590a4001c03861a0021135440d407828403417894020301d81d00004917142c14201480085094040301c41200c0d1000c81d802c51807450154001c0d28882c5449211000d814008001c00050312250208020054094003040f100c95554004147d00e44108645991000b170043c08420050305141b024550210440d00443e8104d0a00d818140405c4141231082002088000b03407145841c1068000c0c40038034104000141a00340c1080e40d00340e2500c540d4041c1ca032444203240c40c456440b0500da0407803001094060201a620358403030b58020220700090141101103680c040105003181000924 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 231090251 1250 231089001 231089021
    0xf030109030909180c080c1906052a070801020a12060e0c1e0313020f100f050a090b0c06070f080f06130f020a0c02090c040305210c0303040b0a0f 64
    0x42e452454140303560000140952a1000d4242050340350050008080b56a4003026010000040c02d0b500050380c20400b440c81c00368111074103081c917032604004554001d4241c4917252001c6910074040f419a0003450891a4661a42800d0744540c0300c00141c24001036000b0540c400c00c2c0d55070700800c074803103082c1c130416109503210360101826030b4000100d21901c00c202426400c1d8400400020010200440f020075400030340d8984a5000c0603414442140707014140507036500000d4454100c072101c000e101a14011200c0001d00900400180111240344540006009086500c910a07210542d0701c050aa50740c01c21100c1501007920f040c81960860300a44c542c5101e004041d240b1240e654589090000e0020019980c1d0705450f258a40c5101d01d41203800908400400c56881908003841c43c010881d148001900f5240a040200014030224202044148010440e01c50102c41e10540c240481820700c6800040a41030201100b0302040001c7c02c58041d0140030002028000340320f003d94004111411006 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 231091501 1250 231090251 231090257
    0x10b0f2712010e0a060f0b090411040513050d030507110a0303020705070603022502030312040f060b0f010e1e0a15030e010b0108011e0305030c070303140a020604080304050f0115050f03010903 84
    0x2d960000900c0c41d802c0000c3c0743c0c15000700840c08100700400b08d541108140d500300d404a40c6c003c8030f0760007418140700e0300d94065aa01c0208a00e03241680303611b5192281e241ea031000301504c4c0da000a0740b0a026440d8202d8206030502113945410170303410000d00940155108642038007aa50000030018401e000b42c80340e049016007540829003100c409030120004010040360140030602c54035008403591088548076074015090304454011514110040351907003601c85200340304c10f001020803030b640106450054102602c0c00c02914404204004100800041c003640c003540b4140045800810103400803403001e40f41d142444800c100f04002800d1703800583c1002d000684103801000b0415801c2d0300112084c0c225a041407146890b0f490b80350859008003524120380c0d20848042040552009104558020240810341022213406009488500c007400252440e0404408503040c44020700c00e21a842c0f1040c4020032000f90b180d010b003850041c051040e20b10688050502d0300715420180103032822030364155 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 231092751 1250 231091501 231091513
    0x518060a020d1b080f0d0609050705070312150b13030f05160e090a120c1703061c0f0609210216091a0103050919060501050909070b03010b0f2712010e 66
    0x3d5240034280c12903100c41d03986c0307601d610002031035440520800c0d000d0842e41d07840c16a40c0d43d082c100500342e101c40312407401140c4e1600035031350b51002d42c08141905032001c24252030b40e602c40d0128150b08410302c58102402d00038250010104100c030025108070344624a24a1002d0583d0740e8074a0341d071000c402c5401c0d003d207400580070180024010050b240744200fa80c00c080c0c41410554444242810182030f50201170400001880360b50f02c1d080070070150311441c44400c034281000039070702c0041100e03880302c0007131240303864140803c02c1040840c5880010040b50003802203070541c188000350b99881c081a400040c108a18000c03030f0418050082c02c04a01100c0c81c95003240504200450041100601240d00750040d10703d9800004682884411898002d41006c503143d4101070400c0540030001d8005001540681c10410602c10701c0d2080d00c0c11201c4030b40b070741c031b89a6445c880707400218400d102c80c039000d52003820b41004440d80002841d50124000b5510413080c240204111406c0b6441124503038134580c4a2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 231094001 1250 231092751 231092767
    0x60503040201030c170906070e0a1404050624070201090611031b0709091b05190605090d0606060c0b060924030703060606020d030e120a0518060a020d1b08 68
    0xc0d030815014a031091400c50a804011a45c074803140030143e803244400c2c1c00c02000d01c107020741e0041400b4840381c41240d690605618001d034200101840344c404d54022a110f030001602980c40c102030100c50314440340740314a03201a00f80b1307044499200000072408a0f81c0000c1c08103100d8862074111514540c810000c0d8078260041c802031400031151380302807010b88140040419509842d015424942d82316040344d00c0c2d0203000049070481851582c200742c1c0500101c2240c008100001007140302202c029080c000d990304070751000706440742d6256401130716043c10180005003155100d404214401c0c09502602d0494881c2c0013000340c41030003502c1c9505000034080c0e92103030b0b004150a400100010090031241401c0c0c0d242e40318026034510303911440158020b40a03a180481d014001d03081c03004076030405800004c0040c3c401d94910b000f01410741d403c020020407071481240c01926800080c000081070b440e241c01e10f40d10300070340e1003001c10300752400075510052151015803210707900380310a5400389005060480c6 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 231095251 1250 231094001 231094007
    0x15050603060409050d0e1e03030304080a05160c0e061806150903010603030f0f020a15050403020c0405010e07090e101703120403020706110606010e040c0224100807060503040201 78
    0x54412544a5900e6520000180e0100140c030300e0030f011740d11160100300b107000c204038514010302c0300c00f072240484054000c40c0e540d000c0102e80d070144e03101b42140c9e12850400703c12541401352104000c038000e60820200140104d0109103070440b80380c0caa02020079544c03001440000010f0715480c1d52011000030108005e440c2543c80399841a01041039281070000810020313081d120349074815004120680b050080c903a80c02002103921205a00043c8111402d9170744d40c4d8200222044c40080d8546d4500120781018801e0003e5184914020410300503542c4808002c09115401d9419801041b00e0960000d81c0f11a064681c0b0700c18040c584980800900d4130a04e8144e1140e44c9c3c088138001d01080103020755212401036041e004a000364000c02041d07080110203031007050303c0d842d039480e6684000708000440e0307449802406c1d003110660f404552080910300c2680307040489605102e0f11031649001d01e24060001503418808c11040050360411a0f803095580c0c0ca401c513501440c0c00141d41000001c004d940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 231096501 1250 231095251 231095257
    0xe07051c0f080a02011409030409090f1b06090602010606050405090406200909060904020d030c080408031206040614060d0e0321090106170d030906270308010603150506 74
    0x3011100c11803090a035030740340003501d442a03000b01e44426001c590212082d50911401200c01584000c0803194100503401d190340340200c0c03280c0d0502540702e0300014104032260300a4840c00d64051103e500c1d0310b416520381e81e5a80c0840c022400002c0b04502c0004150f4814059102225041e03156286802e0034141403042114004000391151a112800342e5144050646511801d41c8a8440755403980c1105042081020b0301400b0180306291a000340405070361080300300740e01c441c2c0c5820b2100943d00c0b2440c1c40c0c402030103075600048942c00041400c8400707034a9181c44902c6884110307000c0003003d1700c801c015407580d0081e80003290000c20a000a0001c402c0982c030980307424a60a0459040040350300a81d5410621080c04030700042007242800800300c17003400ba14000d4100c1e80c044068851354040d40c103540b0304500d101c0204068481c02d100c0140401c59010041c400c1c0c07903002148248880d40c810024000c08488200d001071003080c00014514805d01c80d515411214154000b0740925101c01c01810350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 231097751 1250 231096501 231096529
    0xb0402043c06031202060a0b1e0603071709070e06061222020603132003100b0a030b0708040201081b03010b0a0e04050a06080c0d02030604260a02011e0e0705 69
    0x2650b1404040042048040b0a0124806550043c0f80c0340c94086e80c0346080d240e621350000d01402030a00103010360400c000000f042e05a0590302d258681da20800b00b26140b090b0100f0000d11141900144407040001288807019a510280c2d0103045403500c0302400124819003480b00d4108a61101048170003404442624250444000078210b5034420340000d802d0344e0023030305c1d5580a00301002c121400c02543c0700451400c2c003c0b600403101d001c0b03c43c8010035151411000011400c2d40c2d6440c0e8400b4903078829940c80c01a68104a2901e0303e0300e0b0140d00075140c14002da5083e07011440d80d03c0000c490580081000d51680328042215046034a000b50b41c0c104c07508228844414410340c60110f100300c1d225441214032480d0100f4010070511320340000c450400c46a07141c040c2c0511403408600c001f58600081060b00706902062303200400394048414054104002406c207088403001560081c0c069054000040400d0f000000b0030141e0580121501190020030f1040e050f40c10a580130022480c092074040345039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 231099001 1250 231097751 231097871
    0xd051f0b1303060b0d060f1506180e0c041a091504060f2d030c1409030604200303031503060f0403020a030f030e0307060f0b010e0901030b041106070b040204 69
    0x7060850342e071b40d410389011400400c80180d46180d802c410402c952402401065103040104400040d0340315103100d0f040381c0c06440c0649034060701080c01002400300b05e500905003145040e60007604180d0710505a80080f182d6445081104002c11b13411851100f1281255202e13180c4480c0030443d035000343c030085418801d1140c0150100d940480a60180501c10800c440c3d564000803802002c1501904428001e0241e0048200a1203542c0f120b84001030815041500060f604174003034401d1450300041039103c1c6600303402d4000031050250000100c2e65124443d10f044054950760b5540180301c54006004807405001a4400510140481c3c0034403585080040d00f071034007103000714001000900c0e40d82b007800201c03131550352403031000a5040e152146031040002487c000050bc100703040018155031040c04080d104104500102c1d0800442c002c1c0205130394005040580c032196682450500d9a1040300e06a000c0c80c00c0014850141c100340507001200005899818542d4402001006070607054144440017 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 231100251 1250 231099001 231099019
    0x80304110627130603051501060201050903090d020301060902070503180315060d0f170c0f01050708010b0a0c05060117060603070302010f0e030111070c031406070c03140d051f0b1303060b 82
    0x4807030440d00903c8013171800380c0028015403000c82d07492170780d0410582c44941107900d00024026080d001104903000002c04a03091000995140002070040486503c581c0702544001070740000c204c804405003000c104c0309105041410520020305461b60802075071004c0184800000515130328045001c240e6507400340e0402e013000150380d50303a2908807007401c00e0060360000102d041c440c021010007075402d00e9403206009004a04203840003800407601030152a455020201d003031225030384550070614180350400c00329200c44d41e44e800c0500c01101020100c081e40e000d0700c00010014200043c00d2811642d042e582c00d604c0d5804039604417803003a85001c182e545035407541e500000306200140903000c6940a5440064150319510f071107186002c01890701000c40d0085030400480036045403808400382d8050402055041d600d144d040c04c588030300b500b4072900c103141c81c05002c03220420b000d04c0740140c0d0259012402c800d849140340c5d4414010113504000a840a88080c00003626980180d44042d10107000e94030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 231101501 1250 231100251 231100279
    0x406020a05190908010b0415030803060303130605031006030e0a060b0a050301061518182c0f070f030206030a180506040f02030d080606070b15030a080304110627 71
    0x5002c85080860000039911440c203210031340d400e12548054100c2140c0410022119105099081c0380c00d22024103034000c0840042c07040e840034801c9800842c0c501001d6808070703840e002c0141068000390342e18442c0e042100d00104c0d05601900c210419400c0e00f81c003d16044001d9070703981c0f024051790503900e40c12500083c030019064400740100005000d0908486980740a11700008140e0380002840c6150801000030801c516160903055039270b50322080402141d10018040450115221400440a030030501440302c0d45034480410400040c251346801c1d80c03c0180c0e030b800400c0680d03000b4000a5070020081012034207200450340208580010081115000b01d00368443c103003004000c0320181d5452450450403000c40c9404d0104000c0f0407102e003407003038070b905040c0d002c94192b0150003001040c00ea8400003240040000b40d102c00350004c0300070300b1141c4000071440c0c41a516001030704d01b108e000004190015061600c0000d03110420180001c0b0900501c0d1600d88400860a000a20b9000703000340c10051 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 231102751 1250 231101501 231101527
    0xa05060f1f06081b04090f0f0b03010501050105070f0204181110020318190504090f0b010906060503040f060b0307080d03050a0504030e090a1404060207050c2b030e1e01091203080406020a05 83
    0x30507d400d28800a20f042d240003000c002c1d40c6454503043d1003030340340000600240e80c01000780e81c502c5c0d40040d2481072500b098030204000b440140d0a05c4900e400007005401040880c7c0e504c00c0c2624401d0320380c8102400812000d81c1d5a00410794130750100405103801c5c0f410360410f6100302600603007100d20340b084140d80d1b00c04541103071541d075410760b030210040345500244848040c0f0a40106000c1c82c0422545107080801001c600003c0c1009044140d00b400d04401c6c820b041e002000006801801c1d1212550780354003559807194042550004281001c00140002c1c03558402d0303074402d9415850f22411080c91000308481c0303106c011300940080b0782d21948401e00c101c031003041b10300c95441003200590f1038075141003440ca00103044010b0381c42903800d2558164034102c1c0ca0320203501002107c00703a00b0114020324003aa107841c603d0609a070065482d003480c10f000102d0f00c01050341010283ca55180c419158001e10b4600301c102d031400b4010030880b0010030000f40640d0700402c80d030300451912a06294029100b0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 231104001 1250 231102751 231102761
    0x1707022107060c09050325050618040606050306040c02010509191506030f0317070e10030b0303031312110706080a0b0d030908010f0e1506030a05060f1f06081b0409 72
    0x150005840304e04103110302e060412941a807000407448200183c0010086030480002c00d004040c081c1d41e0104441d00350901c03000140c0c00c80c1100a00c10703c8026202c04d00103041e42c0048a00c144180d05011121031154018802c0c1c03400341002c000548008025484c01c030f0b800c1c88014401f00d5a42e0816401206003440502c62580603504c11005601e2501103420020400d5213101e080c10204c0541105211882d600300b6000301e112481507803544500c3c2e650403000d43c000c04e00100c056415000000c104940c0d42c000e4a229000240704d60680030074084050021100e03012000c40241e401d51005005001d00d600403c3da461344545060804141d5080c40c00101d107003000c030514101d01040d1140400d001c501400e0050710a03441c0c0186040081554142050342e86401008075011113400300c2c0c01007a03940e1024403218a8480d00701084524030305100c0405d0412000850380b80c2c0c04031501c000c2e032603082da2010010300201d072030030307944c5119a48441d48902c3e0024603079500046c03030a008000c0001d01440d54069 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 231105251 1250 231104001 231104021
    0x40905150601091a090301050c09010e1002010e070f05120606011b0203010603150e07050114070206090604030c03050619050c042304240506161e0503070b010501170702210706 77
    0x21240c0c42d084401c05047c00c0d52409481040c004c103080c040c040b40c0366484010302070070000480d6820301c2d460019800382d005042c030761544e514500421401007924212030300e1050032540c003601c2a92444a5600f207581d04c9103400e5070303928001107040014200213440d10549001403070004000240c851380c5d030b5031600700c101209003400b074802c0d40b1000c10010015050240ca001404282801c3e407aa90381e4140021040c803c43e04000e100380404228001580c80b50380558024540c080411082e02d9102d003000c1d541d80c40211000d000d455040c6500302d2040405005042c066114220440e080509104640405481589c0c80700341140c2050729800c1541e4545c055120040f4905500c4c900348000b50a41d510920069000035019507400c10082c40411413105032b00031807a820032032041c080e015201c0e0041070021034403006041440003007981c9084c8191100541c1c100d400c00d803241c498546031006005061081260301e900540c010700c100041498943e000c5184950307188407464580601c4e039440504403912195 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 231106501 1250 231105251 231105299
    0x8150603010e061e011b1502041d091603020906010314040b0a142e080d020d08060f03100203090f0708060103020907020604080924030a1a04090515060109 68
    0x105102c03c0d8102a640095004004607951071a0f1508900280500001c0c038800e1101c00c18058100003400b209441c160030060031440b0640d611940d501480003000c900040c0c4901d0680542c0100d052030038001402404120000042c110b031624603000c0000d04031000f030095041c1074941d032402284d10100902c140c030443c843c00d122059410041c8100c0e040380c00b030341e014030790200c00c40c02448400440b2807a03110312080440c2107043c0e01900d4400100708040c050740618143d102c1c883d07266030010303000308289011a19a50380d502c015503a1604110b0309103009401c0c030790950040d02034003500803460340096500010400c120f603024110b0b2400035180034000e6000b0000d40c2c002c5030040c03003185000940180c00c54018402400107041580b50019903104039682907106c0c1090320f803907154510403401c4200d405910508196228589284030b44050301d200d0420303c03010000032068809a1425120b801b0321355400030018211074000d005a60391520014040a0501c6000c4c9000110780d001955044820301c0808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 231107751 1250 231106501 231106529
    0x703110f120f1503030708130305060106020609010b0406061e05040f080f1212010e040201120204060f0f0f050708030a02090402030c0a0e06280c0605070c05160608070815060301 78
    0xe110b500c9010000c0c00c091140181c65419005030f40e00003003a00d965507000113034650f0781e0003a040d40100290340355000401c2d0703016240000401d2500440c00c1442151341c0c0000780070010f400f00070401140c0c694020070f008122601e0a4039400031174a079005245042d0390410310b140c241c50b00968803401d000c5030f00c09038031035101850701100c2003814050f810540b42d424128a09220707442d4002c1c00d805205000d0140e04045040010303055a1042070801800411094219503441e1210300082c50500e00c4406600880e40c00403000d110588241044403171040c040d524035090025a940d902c030b4541c40600b43c01c005540a000c003012130383e19480218003a04100d9006503030f03510705480c058040d00c50300203601d10501c1c0500c209150394100701d01643c482082d0418800902e511890141c0781500040c2015000340e02d40070402c01000c1d0001c80d100c0c1c15a0050040365035020074102c0103034019526000341000212180b0108100c23074002d0104c29000044a00551803c441038000b040c00741d0400d900920035000705c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 231109001 1250 231107751 231107761
    0x9070b031005010311071a0403051e070501051015031805070803040501141305040b030f34030809010f05070f0f0605150108060f0d06090b010503010509150703110f12 73
    0x136200d1038006104410610b41410303c0d5449051198030410f904e04501a600000581014810411529150f81542c480c0c500083c4400c0c13100520b800c41401150150f2034603010a000c40540106141110001e0050038407400400c0412005442c0d01c900002d0020900075200d40091414404034024100f42e60046440d03900d0300000404440015082748408442044140100b0080040c00703001d548081c0d0300400c0d02840503010926002c00a40d8441650044a2104520b00141c2c0041190031071051000e04200d5242d850403402b040c45417000414146d010482c014095001e41e281d01c044c4901810442e01300105521070000c440340140080f168407102280307610400030309205883d0040e02c01c4020202490041c400600568405014588558240703501e0003040c0c2c1e00d80000d040e0360b42c2c3c0041c040c040c07240213286c04045a602806414444d5081600140e090782c0c00152480c640f034103000c00c0f51070988800c0c10039401004000e468450707024040101c0c3c000c00807031600a00141d000d48032100f44500e41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 231110251 1250 231109001 231109007
    0xa020d090f21050304030e040c120207060b10050f0415020705090a0509061005030c090a020421020f0306040b0417130b280917010b0d050604061a01050a050309070b03100501 76
    0x142d2200e95043c0b10050084c1310100760b004400c5040c054003580c00103690305507440305892800e0b1900905442500010f0580304102c0181c01c510307207211041d01c10800b0784680600c26101405010700c001d82d60344043c0300c00c1258103003041641c3d4100c0000c0c0140c44e100e075122408160408170803142408071a4407101803010700802001058ad214401a00c0c00204a08060001c0e0f02d0750040540c080c41468024041580c0e24420350407030f00100761801c1c1c050411b1032180300c051074045803401c01341c1c07054108040d6072034a4180400c0e05842181e01000040440d81d03143d855415015401d070110340c6c4080d0520910488100018010016186035030301c1b01e4542092600c00711000c0180c031122804801400c80307810071181c010115000385c4460b00d803070084540c0c080080500515480c0c07503896001c03410b06c03404c00a0090110740140614003030007052148803050003520a9007001c191485001031403c00070107030720340c0c400c0002d9078010304050240e607243c0d079a40941c0f8885030001d8903000c4211005540c1000150f030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 231111501 1250 231110251 231110303
    0x803040807020409053003010902091f21050f04020d080d0204142701050f04020c01150e01091b08070c0b040803060307082a061303060b0f03150a020d090f 68
    0x107030038040211b001d02c00c1c0d0441c1c11a030006128110256401045004007a070740c0080c0301440d502c11102c007031843c0700d03401030040045120a000348018850001005008031300350041910590941d0b880000d035072070382da0920200b18807252041c3c40303c40342409001d040c901c041c0010001803803007000c0141010b0320001044034000c0740710034144084800c5801000c401c1c87c19420b060440d81c08944001e0082100300c00325001e4400d000901c0082e520301809000404828000501510101611446180e80ba01e41c107130112420074a2004010100001d00102d0501c56045039038005070602d0140000e58150384c3c4c01d100301c076056904460404010003040680d081c20000d140003000700701c2c010641e101c911000742441031390340e0940007610005081d60203c0303600c0d88002c03075a84107810201208220340e00d0828400900e0380c0448103104d000c00d005107036001c1c5030000d803070811030700c540342480000c0c0c41d11412100290700410740005c0041d218001040030400144024141900591150b580400c04806140d6407107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 231112751 1250 231111501 231111553
    0xf230417072019030201030c09080115060e06040b0d0218060309101506140c030c0708030403020312040e06130b03030a110610080604030c0302190317070912080304080702040905 78
    0x44045850b0803040000e800c0100311313902801c2c0080d640b4441002142c00d0b00c4d10703030008c035450360811440880f11844d8140e00c03000c581580d134804410f40045030030800c2c180f24601c59521050414054144445896801440311b05105406003100c1e03507041022445c7c4e6001203c0203c55604000344040d045a8107002c0c5115122414865003580b6040403000381480460703040988054501050200c001081001101e01ca9410081120502a51030a4a50303a9034040d0000b02d001e40543d1a96440c84100c00055509450340000f141c01d1598400090280b020a1101200703416515042a4209a04c1c2400100f5802115a60f41e601c0700c6400306e10180b07054070181050209800740442044a500702240d00c3d03402c03135031626042c1e0220b2030070f0030304038644040b020098030440b600c00080c170201a0800c0540c848600c0c80502c001580d0f9400c101a10041c1c0c551141c640c54030015500840090f040000a590041c4608000c0d030500c80d00e90045411030302e103820102e445038000f05000440b03052040b1110b20308 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 231114001 1250 231112751 231112759
    0x1a09040f02070c1a12090a05151006030504120e031203010803040303030e0705090601050d02041d090d09080606010c05010204030807030917030c0d050307030b090412030f2304170720 80
    0x841c1c003800e505541031203401d170484010810a804180107640a101207454035421404030352090210804a40056006803030f03440350210b200da00099203034040c2c018a0701c2190407540711aa1203508800c10703200b1240b0690825071602403913130842c491615600c0558040c190903002191a14150310307002d01181d44c42c0c031650000d640100403c2180e550340d0f144840e070104003860455140c111007400c00001e80141d8011400e00f10715141800d0242e6103030303692301e4807601080007110386291031700740103071041c08131400791381d8081e00020001000c41d4090720552a560348603100040c9800d56a84421480742c00248080780081c10148040200321a880328001349020303801c0c00341d460407142c00c01e25135440d03e2984044081c001c2c0400040d450900070b90010302c05510190000c85545001d1405681400742c0c1d21460000c039107094205000c0320300510429858407512024944801a1080000b400e014014021140c802d51034405071010580c6a000e40031851140160f00c201c010404444038042d01321080450107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 231115107 1106 231114001 231114029
    0xf0d0f120311070b060f032407110f031c060503010f0f0507090506041e050a150801060f0c0f02040b060c150c030105010203041a09040f02070c 63
    0x4100c1a076410002180925482c003660300440d00050003400d203020000701d00c1d08000e03040c20400b00f4001c00305c40c0b61104002c003940340400b80d422081103440e04001803104554000c292001c507595814094503c1241c402d5a06590b40030740103101c05540c0c0100c03400b0380e1803400745d4030400251002400070701001d500d05030764101501d0700c86005681c10f071411001402a6100d0401482912001000703a0320b841c0c81d2810721048605030f440d110011521003940002c00340d440300c142c10000d10907080c0360000c6908800000d003013403d059000754140414144140440e80e0301840a009055110102c122400350600201d0010503014901c940c0114000440540340280041c81251121024220301c940350344103080d9000a00081c41820b016034410302007401800c0c514800207041004c161000d508100c03490001030181c5541382c0594400960025404007403010b040740304000750500b1010880 = true := by decide +kernel

theorem cover : BRFrame.Cov 230935251 231115107 := by
  have h0 := BRFrame.cov_init 230935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 230935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 230935251 ≤ n) (h2 : n < 231115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
