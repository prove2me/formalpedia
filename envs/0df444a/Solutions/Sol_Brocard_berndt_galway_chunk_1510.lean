-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:19:17.93975+00:00
-- url     : https://prove2.me/submissions/bd50098a-d191-4d79-9b35-e1c8557a710f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271402877 ≤ n < 271582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271404127 1250 271402877 271402933
    0x150206060d03081f060e01021b210721140a030806120f011b02011506170a0b060703030c08010506090a0905040317130c0f06050d0504140a0c09050108 66
    0x8046540e40c42291043d01d00c8080c04d10f884200b89a4002034980d4883c0b40e803082081d00382c1c2a03842040c0d04044a10a4640e10b051442d0700c0040707115545141d08228802524034500c010888041c56036507220203180c2d040741550440c800c603184a50000f07004107480b0030000300c0d11003402006100e140c1e031002081c0a80150403184640329040c1c07800c2c5006030810143c0f0f1491582c00081001e4004c0005510344411506000740c0507500709222200024030050407a030440f074183e00c848050550015940c018010001c1c590f141c034940e204105070003510b4020107050a00e00c40c0d140022209102c110103440040c05a0120f44980002c2180c0140b0341c030340003044c41c2180c001d4030012032262114502513a10141404407085489414000c0014088510510751684c0d4082c0040405041d04c41540c1ca000b0480ca0107143c02040c1c0403c01c0305200c0e04168040740e4403a00503102160f4058400002c40e08003a40407a05840341c3d00810414448a1041c2c824a030041c0611401050949426080301d075001e10303040c01d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271405377 1250 271404127 271404137
    0x8120a0204051e101d0d141e01050703050f152202071407080c01050310032a05010302030f0402011b020301060803120604060e0714070209010b03011401083106020a02030301150206060d03 82
    0x3500803c0045080f042d02001f00700300741d46280013039007811554500c1504482c04550f080a010483c458081d101b00f60140e810340013407030f855681d1552140300400d4040340d50307a0064400705007000509078081010420304010040566070760610300304010400c0c280405c0d1211608000010403a1030790000b42010310107001c0c01c24907100d917280c0c4910118841d00d0f50001e0007144078011030b0068400c00c1e4403410009482c1c0303034951600c0350700d40c0011170480c04201c0e010906000758501180156014107042c640b06512554696122100d603070109013520200d5000300f00680c00820745102c40240307a0200740d884a016a0100320452070803218944104001e030030031381408070004603415402805e000701d410003500940980b07034a5a444054400660003485600c07449600030312426038642c402c24a00e401a025000c1d091030b060712403007041c000b2004e500c90460540ca80301c0e02520001ea1070b07002038882740c6002c2c0c010b191a5890070f1140e1a03c10302c0a00b040085410950800c11190342d4004100312068042c901 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271406627 1250 271405377 271405399
    0x10e0a1104090c0c050f07030b0a0209030f010e0d030b01020303130305030c0d021305010f110706050f161a07020706080f040201090e1f090908120a0204051e101d 71
    0x1050010312860300b0241c000c50034240c0480c44240c2054000e214188a0742c200e40721600e0111205490b1681804000d20091030000464aa030031190083d00403d6002416200f8034101800320720308580c100700d406483c44d0000b90561203569094400e50425001c01e002039407640c50080a10b070071080d012000181800bd01002007048a00f0701c1d03007a141e107501009d81c00c5685140300c28610b08800201c0c850745002030086070304101c009101d8030500c0103198110b0000c0070f146060203025940c0b0b400806903043d40380700500c89403900b0310b0301140c0c4c201164001c42c038102034211500804208060007e00c02c03400c2d50b2089004105041e40001010303801201104034030b03282c2d200c03031004a600070a680d00c15141d004105041c094031108a01e0300c0d025003182589030707610b03072540c40501380d09171594110050030007402400208441c00313012100b01e0b48520314030401031034551200c0000d039850305a504880301000460440da08903007407001d0895150007640c24005800c40c1090030b040b100311010542e40f40100a80381c0c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271407877 1250 271406627 271406651
    0x20409061407050c07050d0f02150d060f081c17040515070806010e1c021c0804030320010203010311130618020919080705010804110d030c1109010e0a 66
    0x200c0480d089101c0901840740d070802c00d4004201e038000d955204058010280700003660f24002c20341041265001e05403c52400e01c4e13408008003e0304140f08041198403c01042e00303501d06a124080c040c12030709101240031401d003a062880d224040c0c05415101d022401c120130110782007085500d5207146144641c0441d680c07407421600f860506d06120030000021010300c80074641000605102c1d010a0366010090b42c074410802650051804040d00720364010121803005d81020140d80c4005c0503101803c2601c01400e0b6903181040d1302a42c000e074002550000242c0d0301c0100950303005500300c0420300940c1154119140c5441c0c1d01501a421072045081c1c4601b07011800d8203801040c0100442c006442d0f42e54000810342c006540644411482000030750355072194480400242c1d0199035280008000681c01d0800641d542a40500251002c04e60001d28404540d00c0b40e012041042c401d5641c82807000c00e40c03070b06802883c0c002c8911407081c0001030051210200c0c4411196011000c00c602141d0383c00c07190 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271409127 1250 271407877 271407881
    0x6010e121207060b04051006050301061b050d030203090610080304180b1207060f08090d08040f0f050304030314031b030601031805070f150207091d060f0108010b010f0c02040906 78
    0x101e054501440c00b00311001840ba443c0c2c462401c008060350b040c809582c540d0410101060b0718024980880c00a100501180b03103d0015002da5002c140c3d411140ae00003901c41502d401902d010341000030340c00104000d98181c0c2403201c150821202c0c008203404a0608140540302d000d9801400d00789c034000322800c0342a4006401051480304080e00095842101c41c02c0c6a0725501140507010200306080c9034001194800e010745489211454090141a005100c0858580c4009081036039140c10b4442004041410b81a150000c544510b00031980c039455450701404121802c0b420403001c81e4140104050ba0317002d021554001000c111149a40740d40303810042e80203000802c0345616481c0c440f0340326020031000040c1202910004059034114640c2e0300f140410100d644000000141c03c602002c10494603190441d00f50780300c0403d0f10071400361540c55440e01d40f6004442c01c0f06204414401000794480a11601807800800c1c6020f00400c981148041d2034204001002802036507074610392804d122b199 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271410377 1250 271409127 271409143
    0x8100b0609040f09030306151205040206091503070f17060108040201090807091410230a180203180102041a030a060b0403080309100507091e150207140906010e12 71
    0x600410900b020f01c480840240440d4108402003850b1007008650b40780c201c822482c00b074205a40c0d00a0090030560030303901400c0080c0049030498428003226116a480c8603148008500c400d80054480c41c102500906143c014030344a400c1c1710140a040702880d005e0191a176001c4002e09181b0307403075140c0c1d1004803040e91150b4440b511a000d10440891000040d8204295079204200440640c0e26404c04540d02043d151080d8244640c0400e425081c140480c03e11041d0814000d00b80c4030b149075540c00f004a004490512051110350000c10040344440d40c460700415800078200031420035040065640e190200311900842c40e0f040440002c1c42a100d50304610090241d09219070388035075981c5407441c51070f0400d4894840314010340c110254030036800d2081074400d01ca80d9881000083c502089592100020009026110a21783e00428041048509070444c170034143d00400035a80343c0b041034a5a03a00f100005d130300c02c1b0706000900c1240e0780e001100c0c48031403000310365403511200c800100714a04000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271411627 1250 271410377 271410379
    0x303181203021e120115030b0d0c05091b041202041107030c020112020a21090c0f0518060a090b310e06040f0602090f150a1808100b0609 60
    0x60a01814400c55042d00685107521000c3c0d45415442c030032051014803070081d00c1c070040c0d40c0c000200c0104940a0014849000601e0604000030038038040350218092114980c0700707469510409030104824140070888035407000101c098400c214013116200c6d8814455480769642c5081328614182c103540e5107910048242d0a042412079581c002454064180c081d0110144e012500144484c1a040c00314000c40740050182e07640c140c90600701e030f0700803012514203003080080140e48459250020b4120714070200074004903103505201c0e620713050070410310380251549079403c940000c09100d174984030f02000f02c081da0880d9034003149074111b070000f0560f1201c001c2ea0710a55401e404908000c0301c002c40480f401e40c00c200c040140a8011542c81c1d4564440b4185d8009040300040c90380308000c505039501070410010000d00c00c2000c00b45400001e4008041c401e8881d0071024005140303146250031050f00081701d41d2507464003d11919100c2000d49503001032000c40342c2c0580380d00c419000d6070380351011260441d42c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271412877 1250 271411627 271411643
    0x90b0627010f05040501060c050c150c03120a0c020c03060609130c06050d0609050f060f060910030203090c010309230705040204032301051b0c010209090c13061704030318 75
    0x7070740d166181402c04540c45241c0c000e602c1c0600116803548078650300c15041d0340040003001c41040c5002803100d031108884010030768610900c685141c805c028030003000001940b1001c6001410040007000480e81c55281c600b081d54030040200b00a9280825180e6001708200c42d52103565694105d80c180e404015040145035051840c004203210750464043c1205100e546410014036481d0744001045400a59940d8148030b06440005c0c0240380034003184403d00005880581081000c2000c80c0b41e50b080300d214500801e80210030810580c0301044000c1c02403101f464180301e102a66180d20202c01d921500342d901d01d400c6585d003099500302c200100c50041c10068411550340ea078034207280740204a0140104188091202313551130310a03050052500170030340180c04210111040451903015030000d030400440e950240401003880d600c4600b040e208404c82450f041da105503511410500305469041601401090000302c45103008840351140d10960600380050701d4001c0c0d010103140400c1000c1c0007003040c0307 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271414127 1250 271412877 271412879
    0x3150c0f0316020f160b0a030e1b011d150f0c0a0b0601080703110316020a15021b0a0f0807060914010c030b1c020f061b060f070201090b062701 63
    0x154040c000d001c2c0040780d60030340d0401c851008140e6150b12540041082111244005005c00204d510041034103410608001408042003404e0a04000600b10f982c6820b45185450b06a6940c1240080002401c1502c240c03000e40c031072000248800c0f0140c006622646004901e000c0284d01480448460645440488000024520f00096894001c641087c0003607461804120001e000f0301840710740e1059070030031900b03507030790040305604005084000c08110f10417000040c0204c0c985446045000c0b09400d0056550480e105842128200703264901c86541d001400103000308002e88801112075a00400c8156a0741e050308210003d004048006000b20f01c1e03c1c0920445070905610280c61900c180d20140450b0313241c03200b00080b140e02a0194100d4400407140e05005150404a0380004c0000034001810950344000f50310400b6006040580150301c0903052001c2c2580310448254400145c0c802070100d421035aa4100020300050301c1d25000714070180300303094090a011003501c0300040350b50500840e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271415377 1250 271414127 271414141
    0x80c150f160b1501140703020a03050f04030c0b030114060403030503010509040c0302100e040605030a0c090c03021201060306050f0a05130b0307120501050123010c031206050604030f050606040b03150c0f03 90
    0x41c40300c83d030405011641d41084e01c4000d144c40c030705803050190182c018114005554506585603400317882e8014413034402300070102c0010780c00c0d500c90700070305070b14440240c9a43c1404100303c0722110394483d861183c40240410800a0b9100080f00c0c15143c041d2443d030916251440d200d80e846071107810083d48107010352041d807012540480c0c03442030300710121400d00c1000d84d69002d0546405041c10080c103c1000050305100c1c82046420404811815240040c41e1080403070040c010396900703030003000000b511044100481d14100440032102c04088071001603c40c030b480c0024201000c001c22903400c4648407038410b00300350303428840b000040079810050030a01340185003440c0200000d000302400c046030706060300002810b0070800403010740181c4540503050103d44040c0d0300248642e8005030710585481c004201501c070235026200442c0305809202030020249000b03401c002d001450316014510b41021200203540c0020072000f5800150510b00068844840d500e15901c1050a006071222000082c0144 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271416627 1250 271415377 271415401
    0x3060203090312061e0d020609090f09010f050c03040f0203010b0402030a0e100504030e060c1f0905010e0d0504050d0206040509040f140a02030c011d19080c150f160b 73
    0x240814511001540d5501c2804105c1549898040350940c468442580c0d0313030f40e052401c1c040f0302c49800142100e007000c3d40500020f0b4203c00407103400c40510b68007800d100d204078003405100100c0f0214001486140380c804502c000c02d000c0100301514881d0803002050941d10b003944070074101600980155528030f04910010041e100e80081c0071554896403980002828461044c24000e55040c0d44084500ba83c0800300b10480d040b1105c00043c0d40600c0d600b24011034290001c0302c2d5400001640850150b05600344182100c02c8819226101e801030383c40001e003103a205089600341c500494801a02e940e49001003000f90045800540d0025922002e000501c42640c0c5940360161140c480103800840100c1032a880d0a200e0304000e41640c09000340c0b160ba903024680342d0403a060a181c2016120f1101c1c400120109a80000d580400c0701030070041c03054410620040c042c03201c06581c500388805807840c030002c2320b02c20302410742d40d8004041190002d803c210402c210406810119085080c2403000020407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271417877 1250 271416627 271416637
    0xd0b0a1506020f120f19030c030b0d1703071101020d02181822080d0b0a080a1a070507140d03204008070b0403080a05090307030602030903 61
    0x2020002011000079458400184103064030030700c001900850069841c01c04d03854020480e034001a080901c5880e00e0719920180380440d4100315940411501e020090140c200c0b4400c00d0054081c0180e0324010012400c00c4220205101218504036070780d540301c01c021905030ba4940a100502c2d40000307440e140d00c1085801030200c044640100030308202450042118005070f41c280c0114107101d203000503425418100240b8020300b04c3c440c501b05031004554030075503070707601240d2140c0d402c03035035110203500d1401d01c8040507003c1d1204000400800e1025140c4022101405034aa074140c0c22031300005034014454020380d05180c1e40030802d844400042c03490952680009840100028074000c512480d020781da1506c824031910130303550140f40076100d600d5a20004071368882154404c0316102142100c0c0101107818070031196801c0e1341c40c032039420101f681c1d062050551000c44880810b10090010441000c21182111241e041095072450240c01003402c2581960010304a18404020000541030200043c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271419127 1250 271417877 271417901
    0x6080303040c08031c09020415031a0601090501021e2e0e010c090306090f080309011406030f03191206030303020d0b011e030b040b10030902100c03080c03060d0b0a 72
    0x81c0640c840029075628020341a40084184500400c445d110300c00303038080c0c141c65001034004a21984045041916030382c4a0780704a60720200000514100408040305a8020301c0904c0d001c85803a25000000f07546507070010705189014400c1001480302e401c1040301000541c080d841c0b1044c0d00d02000d00c0302d00c00c0b8040c01d103452800c0d8100700c4290485a01071003803507170b0003d458641054440c116100c103402400d8402044480031245d56002c000b10307141c2c9001e50f01c038420110001c950321741116051110114090085070003a131150306a405081000301c2960340d603580051030050325090550040314070b4031b100c40f441480c080c076020300031042c154190001c0c0ba40e20440301007806401e0200c4011a440d62950b00e402140401c40803c0c612064440d030450304200c0401130012484004150004641e04401d01510b800300b84d40c0c416080441c180b20800280b03551184c1040844541c0c2920068100003005000d06d1704190b00100140c5143c1c0c48281011a0f5500400411310794680011148020310304941c400e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271420377 1250 271419127 271419143
    0x10324080c031608070303052b02042d1a0d150311010503070f0e010302040f0806090601060801081b040f021204032003090915030d0201061d090d0f120608030304 71
    0x80488100000203c40865105100900034540341d03450803152900030281a1030703800001038074125180340d11881c0e0103600d1611280142c0d0b4910f81540c900600030380705101440e54040032105c0c2619029101004112149404801d21814088041c540948140050301d0707002898000c40c1c85044206110840c15244141c140701e00203500407006569901080b9030b49c0c00003d480d2a0124405449001243c40808040c1405410a0f490714600d0750b120015800c0340c0d1150b40078904022101000b005980c2c0103010504110a055052440d0561100821040b20040d102d08400321417540d2646e80c00668062036800c411074581e0452500017a00040545042c1c000415003e16150201001041a000c001001c80114900003425040c002443c1004207a40801c500b40d9018481a07141880110012446076000140e5582014030000180e410748a034440800500410001b11000001d22880c1146541c1801001e86000f40c1044481c030495980b118841402d01794001107010b00000a180603600c140e1035 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271421627 1250 271420377 271420393
    0x705013818070309140a03031a1002070905041b03051b100c110d05070602031e04060e040504111903050f0303090c0d0c030501060e04021009060e010324080c03 70
    0x10441504403110300520001100c901003003055000307503c01c0d102a441740740110750341c0781c21034034a60904840200540100b5183d06060802d0a5234542d02c440030030041745c035034601a1701400000c0d80e0390494002c05802a03901c130b0124007441400c14202d00f11000c210800b403085902c0340781290b12828460203203442e400d5180f0600b10b207454180e440c02d4070941c99980c0e480c0484e91540714803403450322031503207a90400c8410810501013082444080064445500299920110150402502308410351703954a44a42404140b000a6124002584c08070048501080a486d01d091040b14040c1c07040d185a441501c80395189140c98900890070110790141050758808101507802076124801100c0c181c44039044065200c11518110569000b0540a907640001e455101d40da65401c4480c00c0e001500890400801c0004505d040000d114001c0d42d80d20300b030401c4501d040d002408544200006a042c1500c0744905001c0e0b90b440702101107980b1030040d800000030341e251003403a140e03d880c1c81118002d0086400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271422877 1250 271421627 271421629
    0x304060f021b090a1503060c090602070e070206150f03010f1e0209130915290105070b010e0a0209060d06030c0e10030b04140618100b1507050138 64
    0x4618050302c9001d40401a280c4c0c800307508100500c41d02c0040250020101d0000c00801c1d450300c5203110524807500e2340900c0c242421070292601441c0d40c800d2113030080050401400076804141c103504190604107100c00c1c400c11038001414020034061540e0158a881c500e00b2590859810200c800403004500386c01220741c0401c9a0264400c10140b44d0b04801d9030507004040450580c448255503000b8411018039007518860030781680e0b41105e45c03102000040082100f04100240b890004400909000d4609404c540d1142c84e844014031134a40a00301850021f0219200d540403542c0141d8010b24030ba90f110f60035402d44009180d540000e81c0d0b4000700b02d00114010101a070760034015001c044402000034950b0f40d03207070b00b080300040c402c40d410948031000f1811740008001e07281c025181d01074016000e80041c80302c945040010039020100b87c0c00c142800456450340329000081d0552a40c0380c07641c601361403d1044c0034000d00c50b0600304440b40d25610741400c00c1d50340c2c00034001306103c0c80d400402d100c040c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271424127 1250 271422877 271422913
    0x41a2a0618070303020c1509060c010603030305060f0907031104151d030a200d02180618220c08030a0f18060f051605061501080a0606020601030210050c0304060f02 72
    0x1c040280982d0100526200710316018440c3d1f1580c2c0320386202103180001c4007011580c1c07504143e0003055039a45400d070501c101505801604d6010314140c90a68000240400090032054060111003d2541d10543e40f91106110821140540f00b8900e8100300400c0950004210444c41d590340c01a042414802504a00d00460301164141e04270001201c00c490b807009081c011a0b00c4c80e0226804401c600c4c0610041e1507a01d1480f19180e01c120a0703403140d2030244140800b0450869a01494542c0103040000343e109842445100c140440c61740503050f110f0345010b41d131884503500810811310000c55a5185154414001c0c1182d40b6a03540701580880600a04826202d043c09401c010807540142618258840d0003e0401e51480c030300480000700c890349801c3d007015801d42c0c4142a0071945404550b4550704030410f00d0704200590000c101041c6071100007900c0b20b0301800700038491030044412000c8a4443c8050340e83d100f5042060f269101c1d5030300e0000c1c1c60a028040300074003600400700c405180c81070603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271425377 1250 271424127 271424129
    0x40602070e06030a080c03040305070303030e0d03110d180f061509060b0a050708120403030f060503030306150306010c06050705030106031a09041101091802030912041a2a061807 78
    0x1030001d02c0300c001e50f85d45001c01a049945206131500c401d01c00000840d0341004584011402504c001a1003503a80114a05250403601400141418603070445100d03d1000c2c121290310040c0840003904039000151f0031010001400d002d00711045001c4140144190b940c40030100b00c07408003949c484644d8ad020202d0a40e4818450f810645401344892100729001c1d030000c003819441130744840d2820391810116041144140c3d42135000039a11000042000c0342d41c0318000141604800842c118507116000407205110080058175202c008400b0805507400762081019190748110b09110a00d001c8000400d103401c24422031001070f0400030900840151800d91403081c60000e80340780c45942d45d030f4a4615488040e101c41d41d041052070000000c000701000080c0302c100721224005641c130308000f02c4803850140180030310780c44000100001c00a01c4410f019160901c0e6091018a484801c485400404015501c09194442480e001800c50f4420702003034251003a200402135130904000d0028007036842030300b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271426627 1250 271425377 271425379
    0x60f05100e041a0c090603090c040e0106050303030c0d02040f060e09070f08040f02010504080f1c030c020703110d02180f070216061107051c03030e150105091515040602070e06 77
    0x751645030065201403051131307000e0f07503020742d141c981446100480c1069104503201e13409070b0010181c04846141034000d505050340c11000a10a403424800040e807240710203442c1c0c609110000070071034584070042d0141e40c007c00345482c07085030044c0d4070b1a001c0c18055090320341c20b00c50303020000040c4e03d19000b20390f450105c640e00e9490700101d64441e5100c2c04c48a5659200340d050080a02c030000d00007208114180382a00224064100c90140d0501d0710501e0789000f80c05424503042c04010003800c0e90000d001021642c019200c0e105400c00d170401700d2840800081c000c2e40005001140c54103881d407001001d8082c0c0040c08845080350358814080b0b0f1540007018550070b0a08908104001d540c0c40b6809148031500100103503446969150005030061000c0070300c0d040103010101000742410f40610821080c00380000c00b07400c01107030000c07800390100414001c8138412540d200c08207075100c00d49030600031210800303841210b1403404040200380703c0c2c003e882060014072075940d012401c10294107506000b410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271427877 1250 271426627 271426643
    0x12190e061c0911031903020c03070815041a04060b0f0f01050406030f060e1302100306060e01030c020331050604080307020f2806090902031605031003060f05100e04 72
    0x207044070440600100a01541d060b600c144035218203580901c0f800020b100c41c1c0704000c0300d150092501a062800c0c1c464998402d800001c41000b0500c80854035019010000010210301d0f652460004985180281004814080f240405c400c0001c55840700d041e90b0030840f007007100c01e004101004803d00501220600140f01407100704841800390304481c1a2082507003012412580b12401404840c0e0700f1a034410307141035600202c1081d814803c1c803940441074203103801c1c400c04e401c0010141c4441c08088030107041603070344c2d012103610034030038420340d0135045500800c4580c400340360000c1403011900145401d52481000710019551421104803000c40f0703801805903040104640800550081081d1b0098000c58259131000c1d2010802100521040303d2164076100507003008401852302c1d001c1e4101e88030003031040060090300901004804170600c8a4a002c82c6c3e29610400907003084425540028025801c0c0704030501001d4650700158442c03036646107002da0a0b640d131030200448060030307030740a4641c0e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271429127 1250 271427877 271427917
    0xd080a210b0a051003180503070b0c032809050f01090303060504021804021305030601060c050607080118150512011a09100e06010203070213020706050c1e0c12190e06 73
    0x104140e54044e695042c42d0400042c07072010911241100101d0141c1140c00340c0001829004001c0105140c80d0040b105015076030031441c004480e0122003221200c0e010680c03844003206030084000350040c0701502d0303001081d64800215030040da0f0180201d14022008039060241c0860681454400ea8500781c0303071004070f050114644070512009520141240f00c007030643d990046695241080103034001e110a1f6030302d0a850f07010342031090624401525640400000340010071060120001b0210f801a00841c0040c030001c3c42e030218240300280d42e004640002500103c1300191030103600c032460a0070b0401180d181400c9100c100503191034210354814064043c2d441c01d20494070f00c120541d0f0b2006040c01104e1810169800207071003090207035000d07510183c0000340c00c81000498020750744c000242e04149400c155404601070f005081001e24042e20440c0400c0710203e007e001c0120030303490034108203c5952261565095030104016041711404a81201040907072820100c040b1600e40110030300c00d140034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271430377 1250 271429127 271429129
    0x16140916140702030f0304030b0f0f0f0402190e01270615051b011107050f01090803060103090f020901031a2505070203030714070807090b0904030e0d080a210b0a05 72
    0x82e04020030680c2c2500c90300005075207284082000b04080c5000c0d074283e41031031415040306040f04400405c4003415060b104244818840100b01075500181d04480e00118142c0c49001d198281c1042e50203617000144d902c000154070702021604000c4000c20002d0102e500c04074042c0f0b00d041e542903200704800c030000e11440c2070742c0c2403180300a4144100c080007411040040c0141d00c50941c0d040e92001740c000140007620400700403080155030004120003000703000000381502c4260103400010510340c18035880741a4001085181c2e001c0c00c1c85141d00804404581d6101d0800521412400c2009c0e10800c203c140480c40b0500c00c440e240346803100c00524804a00e0065404503410707000131401300d1f0103102c28003501000640e4240c070080f590900200420b215840c103402340f483d1007016400951b000e8034094150030240c44249410f9482034140c20220040c8040d8404039a10305224080981180e42c04522484256400300102301c0c080c41111207040305034004c9400311700316102105402c0e44801a4541000302d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271431627 1250 271430377 271430417
    0x603122d0f09090c02030a1e0206010b0c070503060a02180d0b01030201050d02161103060606070b16050720400608010f020d0501090506060a0503040516140916 70
    0x1504a4a002801e042d60358a03003c0c02e5504200500c0d0160b080814001041da80c0002156503000c0300610000040003181006034440074180601003001400003802081102c0401145c0000d290107812100e451425040c5800250051f443d03003504c10016210300d8210346001000003103419040364540d03020b64030716401528640d102c4888411071640a120040f010b0b0240038001031600e005d8668800a4047c02c020942055001440c5c948500f0041c045400881d4900000c6a0301909443c3c0300f640000d04800155854007a035080140700c0d58030402c140d1114a06030050221050040d202d00500c1d01c2e8051600440c001500d0441d0a442035508184170300c40e08021b0440c050591039040010030f50340f14220746080d038071941c5140c51800d400246031143d248c0d407841030500500f00300c0810045824a40002045403003290344540400c480400030800340315090200112624407a4690701e89103607501c951459600e10309281c944103445e00070001d140e500200b030705501019403030b9440484070614250200d030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271432877 1250 271431627 271431647
    0x30606030a050901140f1e010b0901051803011508060603010c17060109050603011502060a05090c060c01020f0d05011403010908040501180b03090c10050a1e050702040603122d 77
    0x1220740d21a002d425114480d01c00301d501074500108a00e855140001850110617080f04140c1e001f1500030b030041058141131b005451480d6000d01e8519075038400c0c2c91124801c02c91082d50140e00d07500c1c094203414403c1c0440d808000b00c0701000162106952034004140c01c0b00c0300088400040345e004005420842c94410106600000504004912039100c03008140c50350070907041008022004050034034815010010254024000d82d0b060000703241100900d912610798401560050700c000c68242d1201c1800e4042d00c000a01801d00c981c0c50780074102030700015000038410420700490ba0841d6001030304043c056020503030341181ca2107180c14a041c1c01100d80c8081c4070b0450254090260011548224600c0110300400201c00101810b0502d8020000070a03c1002044140070342040070340b501c03035007011140e003142804943d40102c840b120f840c146c1b0640700d8180020b51141c5405c2000c01007198040c08088044256910f44030710f0342e02500c00d2558070946402030071500c04002d09058404c6c3c81400011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271434127 1250 271432877 271432891
    0x1e0601051204151113080a0f02061b0a05031b0114060907030609180302070e1b1602062101120515090f060a0b090a02040315091704060c140102030606030a05 69
    0x25102c500110602c0301210905282911030103000030301500620b21990380c4001a1a02c01c011f021040c680356150016041c00e058000e010358008528520084201c00c8407a403007030b403002c0680d407c1c41500c2c03412603113030f921024050080301503074400d40c5400c040501c04c800003040c64003280c401c1c64882e20104404400001d1864080549176040407407010200e00a010181004446014010010307180190502075607405c03107100c040300101081821034101e10300c103000d41500d481d4950381da2a8920000d40030380090301c004e5080b41c40042c00d500076030102e942400140001d0750070500c0d40d0740c907886140310ba031000002c0036084d544030400301c2e03540310f0b1030486031500003100500302c9076a400250200790038a0021280e10406603540d14808403207040c080c074690b50100310b03424114a0642907680b011280765158181402083c1d80c0c80f41a02003141e10241004205c0050003055140d684d180c2c0018490005240e080703601d40360303554044401d1101402601d002d181d00410090031342c4e4480048000811004186c9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271435377 1250 271434127 271434143
    0x306060801082a1005030a0b100f0c0201031b110105010504020a05040905060622090b010c0f140c0603240a030b0403140d0501150e19050112020408070e1e0601051204 73
    0x41505030359194a0381204d80f20390349402c0d440e4605840b2040c2154074801d20079014410a12200020a0b801081004407451a050440c1c44018a00049004022100b00720071076038003c514410900343c01140e041780950944000344401e83c2ca480c00c1c0020380c0204407449001c90014041400013074030f9078000070761004001d00b6142c28059110041c7e500703010b00c2061080c0c030300c40b841802e121200d0b00340180e0000c01000c1c02c0c4006503120030b541d4640c0c100008034010348407a980d0075004018640c2417140c21880c07940100180d40ba400c080901c070008000000601400c00ca070700b0b00c030800a00f0120082c1007142c1e0040540303000e0f680ca07030718195100b00440304445d100040401c2100c01092144c4a254040c28000d0403810808240c080c0240072400a11b0341e082c400c01840303a2200000b414102d110054600a180608036010160403030000307401150426141402030740700c0810a145801903036807180240b8500a00c50368646411032040620030381d00c0d140050703410032016400030000e00d44680c00078811695 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271436627 1250 271435377 271435453
    0x3060b030610171003050d020a200105091005030106021603171e040603060906060305090a080f0c0609150c0705060a0b0105070812040c212009040b010303030606080108 74
    0x601d280f503c030449050740d14122800060040c048100a103c141d0405400200301109464a828502c210f4404038100300304000d02030101580d00c01c1c0107a9a061801520b102200740407000c0190058000340136000051084008240e0360824400c6c04e042140c4e000241d5806000c11031014281c990300881c038a58025403105001c0300c6d050b40e940f008200921007541c000400d2800c1c50340f0442522250350120303003018180340c00e02a2401010501900103940000000d035030388a1802c0d010400d014840d800c3c65680511030801810850201c1c1200396000c0d08001e022060342c625189140e6070080440107801c0e9171040d400204410001d9028901d27145050401a08110443d61030981a51120001003211100c00060108110051401d0b00181200200500380c101c822019458041c190000240a8007008180c900003c102c81080d07036603807000a02041d0b00e6141604180040060a00c800c5000034640b0300e001a1041c8a00070160507941c0e2074001c0d01c00380000081c03038013101031084000c1d9120109215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271437877 1250 271436627 271436657
    0x3061b16170705030408010b0607021c240203060420120402132a052b060b1614060105100c051501060e0f03010209150c010905070e0402040c03060b030610 68
    0x5810480c3c81040290784d52030800c011503080d903603805c00180c02148180886401640c924200714100c40d040072150701110620b061020040030f40c442d1898907803005040111a104082d001548100000e49040c0840d5001401c0c03180b5458403103401d032000034000d002052a00240c0000c4980241c001840301a405007080031080442e408860f410099010641d80c0c42e21000310000021000c00300c41c1491130801d02c0c200c5100c4110007943c8003c00d5002c11214421031080207542c42100a0f100c60082070386c42d030150403005d00282d0150081998058005030446101c6400041e10906031003011b000300601c903141c07000c1545c000c914820304603454061494180c40400e0303003681040c000e115a41c3c40c480c0c3c2c194034105000012514140c0180640d00401001400d5140c00d091918030400d400c0d00c4580e07640c400c40000f401401800c07402010b42c0110f01002499085440300a4000c0d4021101000740c3c10b0000811303070443d1010b100306054041c049c0b0024544d40381003218000d0407500e0341004032807203000342 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271439127 1250 271437877 271437923
    0x402150726040510080402150903030d0903050301050310050114041802031b0a09062103230a030b1801060e0420030109230a02091c0309030203061b16 66
    0xa21a0001d400071038200001c0c030340040d549070119401d00b0001440d00f465000f0411003801c001c60100080c03c00150a505510b040080342c013504a80c8800b0046a0042d1a0041039035100b03100300c4e0f2091041112524000c0c8940c420a81216203540461140003c0b41c014080600303200000707000a0710b01198500056103080c4404000801c0040314805030a505a08103d600600340d0402d0f43d0051910f10103120392103d01941e81d081d45002001d101c0f403c1030718035044520f0305003842d0080103440f44003150310040c1d40034005803c4005450700d0910205200d00c041c4206e4500a04004407038880d29001000500d025201e0905a0340001d000811000c2104000440b601c0900300c800f58905000801040001038500ca100359552201484840800400d5113800d403e01c005400d441440c0d0740040d00303c2482d51841000105807611302d0720703610401703e54180076000035aa84030980c00307401a50009911b5604040c00740328455804640c80e07041019030b003041e00006240f60301c215003200f0642059181100301c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271440377 1250 271439127 271439183
    0x602060c1c021209060106080c120135010204080c060a020a0b0a0209030d0e03060702010e1203190c0302130608010b1b0a0b01031506051f081009021902060f04021507 73
    0x160002c10107175251180003003082300001e1400707810751000c0c00b4070300b01e003d1062042411120717411800d0740207210312131110300380f40031607600e036000b65503101d844602c0c240040d0043c100b21800351060710030415181c014041c1a120303a0b01f801c0b005801503854000056107d042041d044899140010b04080082010a00d07140850b1110004542002d440c03000c0ca10b000c1000b82d501500610090207121004200e00d45e0350b408010040104140c040005402c5c03002010101d1300c400e810400600002c0c1d40d408028009501000340c0100c803401c480404226039026110071812204102110781c07a00c9800c0c03098070580301c0d80ca81c4600980c0a504111004a020414424040c0d030141c580c0f45142003106406030210742081c0d20250145c080a4895050541d91103244030916200d814600c420b035648056400e00d000260f045802424070101e00175844801b8150b11185180880e02100c001e52078900c11602020400c0314001c2d44008444c0340351454444030005040c20724810341c007008030701c2e581010405846040b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271441627 1250 271440377 271440391
    0x6050c07080111180d120c21081f08070b0c01020705060717010905150907180b0d0f0e12070326040c060305190c0212040e040c0602060c1c0212 63
    0x40807031300c1c20030302e440c1c101503004880046505450392060350b43e5005541c5d00c05004d0b0f00038000c040449074144000c041c0e028591410026080c14003602c00000031b00401c0d020388200940c02d2100b8406200c0180c0c14034002e0958480c0c3c0004d102c481d180000380b190030740c0030265289555400340080d00008104100302401800c5030303290366030310005045210540c0101640404185d03400c02013880b00380100328442c40c1024609480c00c00069803070b420142d44e00b800d030602c00005420000310000e00c032841e41c0090480c0ca065070409000703002d841d0034014182c69501c00507410fa40c02c1451808040e0301001c00130f224052003410200f049003d148040000d218000a6004031240007104000402000e04128000f6200c139003403c00441c1000320180381c1e05001500e024950b90b688015a41711305000300b0070007400042c1c5030310b4039075150348541600d500c200c000c0e1000c84101c40141c0000c201d050012511500c00c65083d40014280b485055030008d1150400504408031507003000010048120705032040c0c85090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271442877 1250 271441627 271441661
    0x509040507030b13060f0c030e07120605060105040b1303021906020715020f0d08011e0b03130602090a1211011b061a0a0605070209090619020c031210030620030106050c070801 77
    0x30440008c3c003a00c102d42a840d10503041184d081c040d000c85d2600416880303030802d0300003446a4401c0d0042c0c440d4070607500404418040403802400d0780f01d11000080542c0e209840c5041d116003080e640e12451011800743c40c016821014080c082003d89082c20080003500c2d10440301d000000429035810710a4034144200043e00840041c02401c17141c0c42620400f4000e4a481e0a00d207280205050050001900c0300289820b209000000c1c0001d60b010b0346d400700c9000303020390b00751603071680d010498035003048084914107a50310840d401c0d50302070040b140ca84600700800400500c40c3d682c501c3e004240c01c80301410f22010403001083d07151201c80c0c2d200050300c0c1c26210640c1e107100d140104100080010400b5102c0d500010400003c411000d4280b28403684903a00540c580c400c1515043c118050301000c01d0401003840704002843c1160300c0c1c080d04407802a941000100c2111051034000e5024103281c4812417010001080141c1c030541c010300d070b00716080049e20745003510b03180d00781e00b526042003140003480 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271444127 1250 271442877 271442891
    0x1e05120c101e051e090a03021f030b03010e0606062101120303360312050703020316170403120902030d0201020409060905010f030f0302150118060509040507030b13060f 74
    0x46011011094a20060800c5030400360b07050844250b10303004c050380f40da0710407021aa4a04540724644110301441d40284800382c0d4001c0302007610038100c09030b6038120000341000300d103a02604040c4101c006684201029040c42d9a41030140201c1c2c1e841304000c50119002d081d031514852005507011303030181003401d08260300d19036941002010342d6511214083d40102d08203d9079588a580c003454041f603080c8040142c1c1514090405540507110462074258250404040144e6558150300031031003410400e1000c0d00710884400103e4601a0a03540b001003c00140089404240529110740d440d19400740041045440703680400e0030140300840d0980540e40210701849039842c130303006100192511103010849580b5192014030b50700300b640b20180190840c05000d1050500c00d110b0400c11200f150582c02c85569076000c1a0601806d1091048440345403d0010031a0301d04140d045024641050003403614500f140c852441000014003400386c51300311507200400164450203072005500c00407100040c0d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271445377 1250 271444127 271444157
    0x10c21020606010e100e09090a08030901090507080708070504090f02031510140102060103080d0209090103050c0103050c040506071b05030114060a060206070819020d0e060901061e05120c10 83
    0x994000c00113284038030715801c2602100f03540001c103200031120440e40c0401070744070143d000342000440c04010348804800001c2266034141504900200c6200303c04071400156151003064a0b035034240258500c0360048802000745142c20340100002c1801341002c03440001039540080d03d4015026000f8541e0030320441088441d400310b840840081c6000d6821500d000c2c4c81c0e4000070748805050100400d041e0000c9042e240c80d0310b450341610400b84028100c104e0958403420a180d40348020450680003904000000b00200720300e0b400d6904480003d030256040c50740343c1d40d13444081120008203444e00302f215000020f5607902400740521b92048400c1d03001c0c683c244901405480307c25078000e1803d550101c0b0500082550009150342d0000d02c0070b40102c1d103021411403403c013a01ca00d0200071902800c1006819282c40c012410b54003c03850358008000966803804080f50714941c403042c107103c1d0007031040200a14200240c030b0038100700c289400d50b8440800200019881401c01459100043c10482ea00c255 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271446627 1250 271445377 271445387
    0x40c120308040c09052a090301090b0f09070501050405040f0e0d0504031703090c091308040b031906060e06070309170106051005070b0115020307240f020f0702010c2102060601 77
    0x41c2040351010b002c1494580710f602d14a034180743c04031b00c110061040e100c0d100c40200d0207803500c68000500a2008602d1414100300384881a150b082c0661514400b050170303424001001812510103848a6003814030f0300301040000c00a410000795032a8899100d06141c10b024070006803d8081a07c4007038550782142041903001e40c4541040c22424001c00900c070390f019000440c84981c0e603084455031100d542d41e48100c01d0a450740c8400400400c40400d000c03681501c954042c40c440c0d410502500242d096040018040d5911440f41001160040442d01c446007040001400700b02d0003800c0001c0f03d580d036402d5484091300c8400f1226900c1c1d5403040180103030701d0100742d980c11102c898030344941401c04641303c1c030341041418030500c21301915281740d00303887d68020310a4604541d0480e58240c51041455984e2003c0c08666002c000900c0c9000c2e000c80c070042451080c1c07664049901075007403c150f0307994010b49900303140d46420349014018600164002c0c0083c0e4941000c80c22913409041d0b181050400908 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271447877 1250 271446627 271446629
    0x90d2103140903160f06091a070e011205090102090d20010f09050409020a0510020703110105070b0103060e190f060605060304020d060903030b030d1106011d0f040c120308040c 77
    0xc080c44032100b84466120000155000050780c818103031003010041c03401100308040d20302c0003441c6c541810481000c0c410411050b903095a6121840902030740daa1904948000c45c401c0c0e503d022408000300f6000a1010754003c0741d00c074110400051030000c01c90001582106c80c0e200454442c103505800c0604c0314000ca004500000003801c1c0700d032810982e1000a801c50381d80e0300079a801039030756802030380c00e554680c03510310001d00c80684103e44405031050000c1d225140c070701042d01d50002c1e12141410b294403e00450703400f1600300e0007880059003113aa41d03c018108003c0e003c0014840c001c0c41c90502e8200c0c090401e20180704a408040c28501c500d0b00c0010f81345560300c000d00c1400144104030240c0c0351031016008c855840280002d4212541c07405a004000d2400300682500c00e0302c10383d900c1d880d0041808406656004200d951583c0da030b107000a0308107034205c1c4941d00000d80b035022810380402120241d811038400d00d01400c5207174941001c0b44400700034107401e40000307900314184014402241c2c5008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271449127 1250 271447877 271447901
    0x1202100206060a030618060203041a06120c01080a091407031209051e0a0308030a090614250c0b07080610030603110609040b090405010b1305010614090d2103 69
    0x401c600d0700310009101d1554074030020700101e03180d0102429480c8045110000d0300da0280c0304544a00345420070001307900610800aa001e407240c800b08a25140804510b04030001c0c800c01070240480d104011100700078058064540640c842c3e80420024a8040b10036004111a40003021250b145040c011b8022081c01042014052041018000d90b02d6000100c6140b501c5001008200740c20400451180c0c000396201800c080f02c007100b40455012207030410706425004900502548410984400d0005000d8805650300840e40c041c00101d111211506000803049052504088440d6200c0035030441c0304594250000e07144c0d9081000a140c0840c43d4a00403a0902d402c1000c58156a80c6c044800d1410003e944940808a00400301d5a15600901030120010301240f0042c142450014060806181054410401003071305084000c3c0b20b01c0b480d4105c591035510508840000d8203205055032180701802d4000c0d08003005e141c0841c0c50300ea0081f085a09000c0301742600000070000604071b80c4840084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271450377 1250 271449127 271449133
    0xf0b0a140901030f050c2e050f042112050306010305070806150c010b0d050601052d0d03120e15060a0e010504050601050405100e130e0607030e0f0712021002 69
    0x30a005403929001241520707484900c0e010f2045803420102c1c54036102010099028003640202d0b1140c65520003440035090042600040d030203142801510507000d81e009204640d00d06210030015580c00c011031600c00c00c40d000515001c2000c40e161050003120000c1e421003c50000000d015030707940c0c903209160b8040440d03e020541800c0083c0003c0000001c1c4810601004001c12440c03100d4200b0b6100746441d00c0020150b544103075043c83d14586030803091080300e04c2041c4584180c40d100c20f05003640c030242c100c88803121080343c0804003006402c0441c00010390401c0007a100c0c0080e0100c4a108954855200c08001c1c038111218410300100807400809050165494203000c10120b0800700701203041d0b62080390045860f655075030040750385001303e81c080c40c2d0080c000e07440c2181440c3c014548503800102550200d0b404524100502c0580b0101c50020006500003400110a030380f00741d0046510f420000251501c4030514a04c0501c0d01c40c1d160000e20380c040d00c40603e80114078000b51940b01e002c803c2e0003d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271451627 1250 271450377 271450409
    0x306030f0b16110c0f1512010305010e030301050a060507171b010b040b010f030509030d05010f0614070312020901030e0706110c04150611010f0213060315050a17030705010f0b0a 78
    0x241c0e1521050070400d4001e010b400c2842609a03503100b00740d000e00d1005111503444998207c2c5481d145803007880262115481c0030f602910088011003100c1c180c0c1d4002d881d0071a002d1034000221600c3c0d024450564011460f41148060300c0c5c2083c0090030070145c0c40c108280e18ac01080000b60850300c40072201449640380c1403841c1282d9030400300d60100c1c1082410700081c607540c0e52024608510510402c102e03958a403900209907882444107440a8402580d90701e00320010f00c04902d4018492030300050086969100340c680003264940080401c01010701d13000c140c000d1b40b4180540780c8a483d0300b00c1d5003c14246444d100552800f080002200142190b081c0003100b25a102401014107a00424080010301e400c0504101c400350412a0b20b415001001c55446645001101c1301c08a140507840009040810040e405019038030604203540000340040c80c0180303040c1c03a251030361180d0940c2841d00e01040c0311046c01f00c3c10a1058a9584600700c10114010350b038101008102e200d9508603408420001c0c81c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271452877 1250 271451627 271451657
    0xd060608060a0303091a09030d0323100902030c1b0d1206050f061e0301030b060108060108090c010509010e0406030605060424030204050a06030f11120c030307120306030f0b16 77
    0x145c01d00072241c014a00c180031348075a050700ea240384584065070790588512142c2d4000d45238140d00c00d00aa8200b800070017402001c002800c20165400e035610410140d41d68010303ca017903115030040d034001c03800c9600c05103003001100d9090210440e80f120915079821070a4000010ba0f0850200c084d0443d4051040100c64100170001c3e01800342c1002c494003422000c5848074004a60200201c641e00941600765200e41e982c0c9003100c1104000c503210350000301c4c04000f0810550003035407468050811a800b402c81d201488004507429007000607200d0404c2810050388145840742d21034240618020b110129141c40c040d030900c07041d500c40410750114001303d021105400302c011241c0078144c0c0e03030440300402c0a03212200e84c14041d01007500040c0807a01d90380002c1d000c0240002480440c080241e40d003200c46080d010007951290303010207080790950000c00c40a0005280c0d00d400098007120fa040015015480391a50386c012a2007010888803031794a817003444010b070340c60980c814941045240a100d0b0602640d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271454127 1250 271452877 271452887
    0x703050705061c15030c08030a02070905061e0a0f0e06120a03020d0324060507050d030213060c080d0c23130504050a091203021810210b03030d060608060a0303 70
    0x1200e9841c0d00f0741d945003003d40c40100f04690704010f60700300c42d01d803002a0300c61402a4803503004488607405482055400220f6804a000312803260b007000b0104000340e000e043c20044142e004c945041c0c2c0c4407001d10008500d0441a02c2150081d00f0350700701c2a40d5502c5d0410070702c038907003080000c82041d540c00000840c1c000b0703a0000300300001c2103681c0780101700005c205000b40c44100c0800800044034070564400303e0107960005c06008450b002d80b0840310f0024004c00203030300300c1c4208150030292107030b880801e03c210341c05640c0012245208100d6035240c1099640641c0c100d5034142200c400142403070080303001c04400710a002d890f040e5a90a400e180400c0010030422030b44640c402c4034000c0742c89500042c0c03428043c1d440204003942000c600c1e940c030390751503000a0096100c1e40760080c403005c9418900d181c0342010307006554042155182c83c001e20006441d001c8076042c4180c5900489600c42940e400e45450520150040541d9041e001c22030b542040006409008014046400340b03400460401c04284e201c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271455377 1250 271454127 271454167
    0xc03111317070302040c05071b080c060714030406090302130c0801050d030e100207061107150e030304210b1608011a04031718150306190e09070305070506 68
    0xc103951108040701c1d502509000345540060360080c944141e0400c0c09400c1401000054030414420f07130150300308a05080602086c2c080c00699a00007100c3e01c0c0c050400100400505c0d01444070b81903035107a41d010080c596401034102030300003080400304104604100700c180c10711b4251500d0901518102840c000c0400d4414405c0700d204090081042d401d040c003a003911040508064501c04540407006006903076a90684249000a80d4180359600394100105407082030342c040c03084a80d0959141002100e41d51060100b555050000300030025816801440b00d211040c602d84000c460000b19080c0705004c2ca0700140013082484280441c0411183e0020000741590041c0b104070a00c504403040a944170700039600020013590510030401e205600080150604105c010300904080e58641d0a101d61080c0f02108402440400e10108010307241201a02518a0041d03442001d0f8955170512a0340381c8000303a076000000e0301b291105005200083c08058003824082c2e4415180c41c6c01c02010000180c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271456627 1250 271455377 271455389
    0xb030408030f1302030d03061401020708030d1a100c0302101a0d05030d0606020a060b0a0b0a032706050711070b07031409040c021c0e010c02060304050f0d030c031113 73
    0x282c4001034442108410400040e500035088034031000541802400900450203503003540f903036180c0d0001e4550703c00103504094421750f80245040118072003000c00580420340c8040781203800045050000d48501c80b0725a41c090450355182000c401e00c2c10007070705003c41401a21101410421038003100c1c003124a42d490000c83c1555410f801c20600c0c10701c14154050b0401c4003245e01e00301740000400d95800529038460a001c0d01c010000706c00e50070300700658440030b0310451585540030f00c042d41003a03000c0d030b1140c26602521750646881c410801ca070b0300c20822031003000721502582e4209001055a0100c00118841e805900402c0c606041c1034400d10f00d401107072801002c115580c801020660350420a445445801274801c4c854610243c4001c0d40b1459072034420b07483c07a4050428000700c684141800b0610800c1030316500c400a40320723002d00c03d041d0300040c0300360340b80e110388030a4000382035081040d404102110f9400103200c014a45000302528003207001e80c000561f0600542000c080c90308501c0c0102c8a03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271457877 1250 271456627 271456651
    0x3050106081006120f18050c0402041d070201020c2a031f0b0402070c0f060f0503130f050a0c030c090606020705030d0305041e0506010e0105031c0302220314070b03040803 75
    0x114004c103500a4240301c0601000b050400c00d62180900d10402000c0300140328000780c0703508a1003001032200700c0c001c5208581c151b6030542e414800315088030004e81d821900f070f480007624196081641614095480848008080e400800308034070781048152220a40c80c12805040c0340c1c0d418004188441c401e60000c041c5507556952041c07603a139680e07811902d641e81c2c4100c04101c10365584000c50a61400391080c5408500c01d0514540703994480e074201c900c61001803403001300030040c030344175519a0800d1040480700c44c890b0030813020102c2c0108100130000d61003242014542d6042602c13030b1094502551040c0255031090708203002541d00815960708071802440c00041e9540c0d1800c1400340204091104074240541c2c00f41c990604c02c1c0801c405040c0c82c1c02e103070010036030703660352090541d0b68003074800c0c144d800700c8c2504403046054440d40060090380c048140c00c10b20440f514039404074081180d80111001300585800c030800c5003041c000b08000b42282c00b84036003185040d41b0343c4141c9100081c400c541140c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271459127 1250 271457877 271457897
    0x4051503120a0c050f0606010305090a0b01120213020d0524010c110a03150f140c310602070512060121170f030601030608030307050a0e0d120c0303050106081006 71
    0x1c0c3c410358800c52025088401c0715460030841c084e07240c60f03842c00c2c0c0d0900d00003030400000451100b000100c54840c0f0f0380c081c03030b14030340c0da03107809112040c080340c14000700ea1016941c0121080b41d50b0340d001800281544980004050600394603e8440e0010051030301c03400016440c8242c00b030303038101d080705807555088125000d112a09000164a01046070001011548501c5a082861059610451003808038030070030480f07603901c410343c05482d000c2119910404078040244141c44500746010140c03408440150281c4011400b810450311170070350b000300b40180c2c0811810403040c94244412954041e20303601411032035050514a1103201c50800e580710007c1c241a442c8010003c209814070b0b0000c0341003004644641c0841d00b0354182c0c0c0d000340c410600190034500e000c1058000442203900418540d12064030300484188161142d108001340954049a03440e04500881d40752050042e14031f20560341d1300c11012080ca03010307007181c006802020400116200704000e00503046c02c00000d480300790801000076 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271460377 1250 271459127 271459147
    0xa020c01112d03090a081609090c0b0702030109140309090c0f0a1d0406030b09010c02010b09061207120323070302070306020d0f110a0207050f030606010e011106090c0405150312 78
    0x600c01c0c66130050f042129400002401e020202c0c22140c0b03000b0110341c620203595101010825501b032448090800d07941800f0030050801c0c10801094020300c064000300358a40c851325041d5040c6440d2444250301e400004003034071a8901024050b6000f21524a511700300400e8103021285030291400071001d100350842600140c2d55101e8021060490003070091112944038038115034000c80549480c035a56080822000401780180541d00b001840500ba80c0c16980c1c40e0001c1200d03082c007001d06400540030b66000450007002d4240c040c041ca0f0f00a465240c001c03140c15400f5034403001118142c0c202d54005000e40c1000a40c08070310380086980050000da112031041c8122401849540200c4c0022440d02c0201030310008824081e181100554084da080e46984200b4031104901001c12587c2c950001000101c040d070060343d141901441c189050b030040181c14030864034008090b14240415800684086014541070181c80c0d4040006010000d194407002c0c00703e50340d04501e00720810101e90201c1d4903551 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 271461627 1250 271460377 271460383
    0x305190516061206090203040f0314070602160201020f07030b061912060605040b0415030b090a050f0a061b021c030b100504150e0a030f0201050f0a020c01112d 70
    0x1000d605a11109542d5180c0c2c2c050f0070540c0f8145044034841c2001ea0000d0f1450045c42900d1080703402c005001011190790740c080320b06414030503040030300350010301440c80412075903c09442c01c2d2418010301d0384044240e0001a00d090940d409103407807039101010910000303034917a000c0350b00180161070241a00030600034442082030240c0114046012262807903060114030b400c104200c4101382d030108140702012082c002074540301d060100c00c90180040400014501c620180d504c4100341c0b0035103501d481559a610308204d82c00542c40d24640c89180c0d5501400020301c1026249001e140d503144122804403c007130f4603400c1030307070b100420414221000c51142e801794001c00e030071490060a02064880d4100c001d801900103024001d640f03c0c521441504c0b01d40a090010651800100f454500d90304d15034405410000840c4100d041050902107100c1c030320301c2100030f031018541036005822842214030004004803040c6420ba989a0b00a00c3c110280c4514440010311900190603e507600350011184140303 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 271462877 1250 271461627 271461643
    0x10306030f0b0a0507031503020d0507050d030809070801061a03060a080d02010e21191704140f011a010f1106090619021207050313020909010203061903051905 70
    0x140c09401400e0020031035206000c912983c0407000800c9607440c0c4c0c040840845004e1690010000d120410510240c0307001c036034458a25104a01300c50000d0384178000720b405244202012004280454107105181505102d1a0040c0260034000c01005140088802040c221424107150200000000c1140b60b00c0d907100341e10142070041c08070b803290300a00c40028002c081040c480102c500648581c280e08081030149803502c49102107070300f41080f1144090500d50305a8484010900403500e0107014100e0074000e94502c00d50044000e00c240c0012440c000d82002c0305082d40c0e0440b44d15129504441c1c0040e4150380740d91007000c0c41c010643d20701c80001034400031741c0007081c00302c030703200d0041002159400015050300ca000d0211020006240305135421060b40900c0c1d103000c1d01c03141c0c2c8100007810f0303501ca00c001d90740c85030160b40ca60b24011081d801050407480140e441280e26500042080b00c58284040d0b8494034a00308a05136260390f00e517803038141d1501d044c81b810030f001d004070010345070900c042046260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 271464127 1250 271462877 271462883
    0x608090c0904141e0c061b0a0c0e06090f0f0604062402150906010311011e03090323030406020904090b0f04020f0d0803061915080f0a0504030203041401030603 70
    0x80c0c6141007030f00704400b0fa6401c015201c3e03541c2c401c0070600d808124045400d188041507140042c212070200100b04032480c1c03c190440c081030107001041082000e001c0060b030044501070100151071a09015001c4840f40e0010b211901409c085000e112440c048115029441002c00d00300e001c040c0c8805000502400890340005500d854441021548040500703180410711441d07002c80d401003058a5045443c0302007102c035003d032604550010000304401d2101c4600170101450031220061104900194080402400d200040c0e0390f6080c80041580060040e140403000174001420002e51540d80784003032000a00040040e03401280b21031294541d45c018004090380461880034615003000d18074411041113805900c5101d41401031039407400c044c0d002c14015a0000983c604e5940d0300c1042c08286199a024448050040b40c0005510300c050035102414100d1540c036800c050500703a40c02080040090320350075210b0f107014207200000742c000041741d040303408440302c444108a2010041e001483c10340d1001d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 271465377 1250 271464127 271464139
    0x20910030c0e19050f040501030312200a0201020a02060c09130b0d29010506091305040f020303030c0c0f030c0604150e070e0603060f07080705070203100c090807060203130608090c 79
    0x3c10450791800b0070801c03d90f0401d466550701d202451040005440c828400540490101d11900c421080190410703511041d200c160742d601c0313412140b084140da40c000c920110050354045016540a6414003a041d08120201300725030074074000c580040c04180100015501c3c0c990340e01030081c00c2d921500d0417440e0780d039040003103031280729504200250541040c0c418640e05c1c402607000400e0034134001090303c2190304064001d0700014142d902e64401084050002e8032410012404d4100607541080118030409406004c1a2500081011280b515040e6a00210381e40c00c107100e110b240350030010340c107035101e500001c00c1c0c8806915004210300509622000e44000c0c01164000329461458003840741c02190700303078226034160359040f08104d60300c0c0301510070500140d5030074041503070301d48200090005070b80001c040d628040c641000201c04c1b21810300100d40441c004150800c48490244403190003060f09001a5190101d5129805103042d001d014003c14401c080e07000c2a500002000314a611030409444 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 271466627 1250 271465377 271465399
    0x31506030603020a08010606230c0a1104060b07050303150a0b18010f0305040c150e0909060403020f070303170709030803040506041511090607060b0306040312060603020910030c0e 79
    0x80100500010b01040e8000c00c1000800582020144100380031142507030384c3c0018022107401c0301b0038840071070101004040700501c1001c4030044184650b441c600e100e054498a00140032003840180c9505a00c8402c108c0030074080035000c1b850100490350310000380360344201075203004800102494290f800c618011000031468001161001107218868502601c0d900204103000200724156403003114000c20307032503a14504229090301d0070b01c81084c07189075060040c5030440290118440b10422030300c801959100400307000c241070301880803444400442c0080c0400c14110b40700a08201c603800078100c82441b40b440022001c43c0b0442640c0c0180d50712864040d540c0c01c01c1e091081e030b2800305580544113501d80c800e40350f80c00079580c0702c1c1e1800c0c030103002d00c0701d42040145810070885410a09060f580c0580b620303080d45d120354040c0010b0340b14038480e8076003122900e4500001070450b00190048803c0c1841044100c01035903c0c0e958142c0b07020054a03001c03902d00032610080350410300100c02d0a81056070302c21 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 271467877 1250 271466627 271466639
    0x41107030c0b100506090d0201030b1903120c0302070e090c0402071b0b0a0e0d062003040302010c08010f0e090f060c1b0d090b0c0304030804060f110a020907030c0315 73
    0x5400e4007240c0110301c007051907100d0030301c8450818101c0c481c4540c02503080207189041d0401c140c1004106005050000b01c0341405000300c2c0444100003e420041000d9071414010400048421310b8010700038548021001c3c09a90040d60311150b41c0602000c1d808070f41c00060b40541c04000181520001620654484480d40f508011020b81c800d040d0166000610022a98030455800d80c1e450030820ba42c2c0641030950403007400802d1429901c2a41c1664658005640180b000396904d00444003410b1059540e00d0b01d420020f084581d45c11700001041a002e00412003103444a40d06402e4501c0201044459101d0328001860700000d100c1707440450168030208011144002d001d010241a80c1c040958011030030014240c07903203041101c50002c0b40d2412828003a030300c05c84001c1c2241007505800c69140079100c2c2c0301c1c43c15039006a842038002030409078608050541c4540d060440508032401402c14503841c0d4009002c10400401200815980c2c42d8a8400389109400046c1040e2a80844240c1d82d503c8034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 271469127 1250 271467877 271467887
    0x2104081e070311121b030d090b0618250c0515100504110a0c052a01030e2a031510030c06051216030905060f01050a060e01051804110703 60
    0x1c4420340210f01041c000703203001e51001c41e4140c4103c148000d4146401e1202800d500c800052880b12502888180116a4100d505100341001140503503506401440d00d42c0c100881202c07074070303112000d680002d420b00103403241004842c1170108140c4003501204200c0744003216480c20903c0c0c0500b00748954403142906c0808101401d00850119001007602c503102c8040c04159039066008500381c20b81040032032401403140c800710054a104000303a9158407000a0740f82c088449210010300e04070403021303c030080c0e9a01403003000080c0e1aa0005484038000c4241c9089405458560800c0b1401b0204582e2003240c1c1c041c03004110544103000210090b0404a05010119849000407a140036103034801250141c080c100356140050f042580f0a515034501180c000808140842101814ac4440034400025428811148901c0f00b40c404041c2c99858a03040290340382c0c0f41d62001040c0603024403483d5059074440c04440d034446c44483e5038458050f100c1d02050060186800c41c3c840340038042440790030141c5c84 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 271470377 1250 271469127 271469137
    0xd1202060105030307020a05040b1503010f081b01050a030b060d0c0203030a050c030906041101050403150516030e1915061e140105071b1703090a08032104081e 70
    0x1650031680c481e81c803003050590380c0c850b40b100a58480b41b00031081100e0701e01074014911049002c1c2034803510f03101100038105681c000b81c0110000e042061401d0000310010401c1044012100124401c100740c03ca0020b0940e00c6034055100070503440f01041400d075201c0408403011001c090008114140ca845002500e0f908107a680720202404c0c00d002c180c050100000396402010a1000b9141c240c58603a548000d00d0304100b0702d9814482d05200000c0820300b80c400c14070a5404142c00498145480074812100c45d0b080141c13582418507104064082940010390344d0009107991100e001107220300d00b400101c03190100b128801540c284200032900b41058011602560100b0070849811034641040b88a40c92061140c0c2d80014000d00c1800045860003408a052024069004640b6610b030b0f0860348071142100b02812896000240340c111504006080d44018070b4a00080c41c14409020300402c2183c4111103018400c0c1c02840109041c0100f82c0100c940001041c0c900b5040c0281068041c1c48a0b046 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 271471627 1250 271470377 271470413
    0x60409060306140906010e0a0b060a110d1d10030b060c2b020c091806040c06020f2d070801090b011701020c0c01260c03010306050c0c070b07110d 64
    0x24443e40810b602951aa0540600b51180c040c21440e8202250402d25007801802c4601c170541395050b103495500c80c50002c0c0f681084954030f82c404281960038440c541441d529149003000038040680b00c0442041c41c05400e80c86003110351074006544140224080c1100b80d01550f484080000d20030b1002400080405500e00c600d01510809a51b0004d490640c0c2c2e10740a400c40035030000a002d0055280002480ba0b02c080302c9040103421846c0b080c1290f1a0a10846089a070844070f03e0061241c02d03010094145503e003c01e004044501000a080700258600020200c1e040d1004070601c1e070244e0240302d09809450440300030800c000b500d0410008450080c801d482d0011600740d04d44502c41810300840f0121640f400c02040340d0b000810044a68407240c0700018003800040060346072804503440041e004d1051407000c251a9410b5040c000c0c00c640c005001c40c0310008040180644040010034080300310342c4000c500782c1e00c9124509011a401d41d0800320140d200e8400c00d2002c041085000f0300b0102281 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 271472877 1250 271471627 271471631
    0x5030c0705040c0212041e080a0b070e040207170705030f16030f092315431205120703021e041202040509010b0303160506220303050702070302060409060306 69
    0x100d6000603a100c05045c0c10326045c1030010002030101c001c49004000f0959900c500300340d80942d8504070f071070810801440c12200030081d2001d100303a065102e2849600408111003c510304101a61488400034010550420b07014000c02c060040c03200a100390b43d04924140601696100c0841c0b861000c510004c1d4124081403000e440b0f20003070b9100e0b2103050f003503c42500f160715400e601000d903da04080c031302000b02d50114509149500ba0410f05000e00842c4442440100e481c0388510309201c90902d00c501c2442424010b4101080905450182560301a8110059400090f04031204903891300c100310700703050807042d51024000f0065065004002d101c3c10880520120030200c3c4059180d07100b0380c403428a8401246900f50054076059000582001c1007000014000d040040860b046030844883c48400d411440a41c0041c00700900c102c0b84e11500e116101d00f003100c2003a11600030101300031005020955a40c0004034058000c10810300a990018012034589560b8800b500241103d0301003112264 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 271474127 1250 271472877 271472891
    0x9080c0f061e07120b130f0b01120903090e0a0212010b0a08070f050f0a0c020901031406011d04060f150e0930090a030f050127052805030c070504 64
    0x900000b41a000f071650f0350326005107070040c2d03101101a080d090701007540a02c428485001b200860b00c80d9240c40c58485501090041c100e0002410318002c0f4000c3e925030038105040c01d40041d621011280541e0110904110103888402c2c4820090268620b0300f0808403041d00085103e0100001030003650b8810781e501940c2da40c500004469180d81286035602086d01482410502c004007005400324144525025400046540020301030050030380c4180d5003d600c2011941c840a4140002c0b0701419070f04510000c801e4080e200c64901b400024030113803140d0766035520440c030041c01d48c0081a8000300300910b46462501c41303824180b40f15003078a5144081c440c03101f504910510280e10492041e2001140c0100c150060054154070361100e150142d100180c0d21021000075281000c1948040c0200c1c0000750b03d610084454420440c032161480c030362401e040c4c070300d00095000100e42c1d01c2c10050346042c001c002040240f100c40c025104400410601021a00040c2c0110004c0c4041c2110401c9500340010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 271475377 1250 271474127 271474171
    0x609030e04271115030a05010303091508010329190e0c03070312090512010b030c0109031e170a03140c04050603071d0402160203010f0216020409080c0f06 68
    0x601e40d003000c5a160481c8021120012906044503c580c044028103402c0c080000c6034550300c0d850380210760392600b0542d24401801810703404041403018007180071145d0303072030306002d00f01902d03c00c03051000824407048200800c9481c400380310050480408c40c410071955040c50740000c440150461255400c644c034080c803001030380c00300040801c1c07d00405800b604400c0d0458039100704001d80c7c0d005603c00d0250924002a8513140d02e4190346c62012268000140560300c8000c05d824440c20f800090304000066809101044404008003800300707500c03201080b00d41a9207080071400c05c0706851404100404101d18043d40d816811610060a88400103650b80c1e603100301c1da104134055409444e400c41340a000080b0903600402142c3c10b0385c442409400e4003d0340020006042c5d034021005580420384203d111b20031400c00b40a8400c4200c21640d055003400007001c0038005c011040e24000e0f01c03441c1c80309005401d1040c41021a290310301340d10f0944500300c0003007070701c070303507615401d49103806449620b906c06044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 271476627 1250 271475377 271475411
    0x3010905060909031e030a09140a0302010f05010e19111602030105090a050d11070305190b0f07021b040204030b090105010e0f070c030c080c0d030f0c0c050613030504030609030e04 79
    0x13400c2030b505c0c0c15400110a007441d48265080288030049250303451600c40f01080c589412a440324201d400184003103411890002c1c25030391016404e60086082034014401d44140000c0719034003c4c42c210414031500300354031106000e001405000e1101004c002151003114101d4545d41d140c041c0207a00901c640d85550900c165a044a140c0c0508a904004a043c802e244640c0701582c10303170911030403106455201c0d150241031024240000340008210f105d08410402e100d654168049a06803101c4140d240c603007000b0b1345402c007000e0107541c0220a81c2408015648607810346001c1e580001d03115160740b42c5854032030300034070080c002c004050b4455400221540000300c540c0c4d129504940da19804161320340d40c1038803102e00c001c40480707404074107201c00c400841c8100b0114011120a940c00b00300482d5100000f0200d4480b03001031000c0140c0e101c180c101050f0009000d1b0303046000900600e10403141801c04a03440d000d607070002442103040100680500d6400044040c1d644002c07202040140ea0780d01c21544 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 271477877 1250 271476627 271476637
    0x11407020d170a0917070b07050a0b0a0c030507031b032c21041d0a0905030304061d0f03120a060812130504020301030210030e1006030c1a04031a0405070b0301090506090903 76
    0x1510b1b400f0001c1803041c0c4d44040050302c2c4a500c18000c90b5070310280391b03503404210a4121108035029513075204001806c0e525010300c5400001034141000303441d40401070f14610f840f10180c18414540c5608060511610742610b041c1d958a2803100000d9543c4000c518617110307621074041080b006220103590551509940844007159400001c880704011a00410f042c0c00100600149200d59a442042c0c0450818001035100d075200305c03400220b4114807a20040442040f102045541e4861102c16124510000448a14108119a078001c640e12141408007500301604107000c0c80c0228108801c51f2100d00010345074184082402c0e047e036540360024002240030900c8082c7d484650101403c5205000b0761080d40c01441e039805403203810400d914034005440d402c0d031046500680341c2c0000c00c000b9010814220b040d0b10702001d101c2c582803a6440d05541814190215801659040301040030044204000c600910340e01d001591a5a9210020001010f0841d03207103000c1e2080000250908002008030f503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 271479127 1250 271477877 271477919
    0x40b0c03010b0a12110703050706060e011802090307030503041d0108010c09050607020d0602031608061203041a040509010e070e0d020901060f030b04021207120b011407020d170a09 79
    0x40e0800d242c1c11000c03681800d500342c08411381c0d030f920f10052010048038001041c00358081e4480b40c2d600c0e119460400d08856032540040c01191303c4d180144021090002159114030301c1d40d90150300e4005550000b8240495980014507a12002400290400d04001d6210200302184c840c1c080e02d13a610810b06098803100704054000445001042c00300d40ba189003d401c01c0c50016044902150f2a07554031412a4000c0c0c5410740103200d24508240750950202401d41d02c814261500f2071700c0e640744141250b5a00490060345959244031400c1c0c00119044030903500180f100600c28411540d50340c0c00840811410343c1e6040015045503600c1d070050414003480030f08203502a00f400d00d1680b80000485107000110300000405440c2c00c8900703e5551540003816190230850041c095500740442c0180030010b440420710505410245011031507a0801d504c000150500008980d807105640700161821a000d400148a80301c0324021490301c2501c00003501c24520a502c64030140341c0c441286001304040703010301c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 271480377 1250 271479127 271479149
    0x3060a18020d060b0907050d0b0607082a0d0302190513150507020303071a1803070209041e06140c1206040207032607031103010503100903021c0503040b0c0301 70
    0x1080c01030401600c8441c1642c06a080000d01000090000e001c070300066840c0c0000a01c00304203420074100f00e1040d218440400c59800e498034103d5a5945030711b029235402d901890b01440d07081c054400081541044010844c01961403e203102c03480a0000d401280030070600c00c4400c41400f070500d0080048070110b034a0402c9a2140610b48000440d0310345038500440f00f04801800369a0058904002800c82c29114120782119040241c001810003903009107450b0414441041c00485020040100d17a0704913015a1661415603880c201800c203580c400c030300d088441146c5c505610902c41983c1c0800c0c140151160100d1b40c50b26561051501d0b40075210410031000c10714404a03440d8a00303a8010040107100382001005601489030800d405080300b45107458200c0d1400810015907818892103c07000503000000341194100303408270341d45e006008030420b00c00d9a14680041494001c00030a5185207061004158541e90340800422a82040d40e08403800c103450008181d1305d054000503641139075110300c21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 271481627 1250 271480377 271480421
    0x706060504110d050604060f09020d0509030717091801030b060f030d09061b060e030c010612030c031b060e0318040e120a030e07090e0d0801030503030c21070e03060a 73
    0x1010090034040d068a502c1031f80ea04000444040344c604100051007650710041e22410784241440070b072030005117884040c0e0000c105100000d6030b081c44030311314034205039000760310b4031002d070049124004480c2c40d000340703008902c0000082040901c0c51600c42d12050716028038105609040c181c0e115545403400303000c103454020034052280b1900b90840c0c8011404c0040007440410f0f203805084407005032140301d0395000010040b01000c401d0082c040104202d182c044404042910002c0c4200c00c3c7c55002010481e0030821800da00c18109102c441c8582c000301c08002c0d00455400c10b80d40c03a41b044414188494040c11300000b04d1030548284420300c01010003130010408032410f1400326a106000102c02d0554603080840160002c004600c060012100005407401111150078036108542654004002445005100140011054079003000d00e25107403d865208036101003006403056204101c0102e089810445200d90104c580c0c0c081c2c02044c1d06840054494140b024190b4503440d03040d680c11444020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 271482877 1250 271481627 271481647
    0x1030209150f04020a050a0810030b04080903100f020a030b01090f060302031b07060c09240f020f061504050117030f0307050c010510050a0b0c120906070f08070606050411 75
    0x34800701c4140c010314901d902640c400000c0d0498026801d0500011000300e800301c030700350704000081d03042103864220600786890b5070380e100c200d420000c0009000440200d2030070160f8904000410101446d036605014102020741000001d4025014200000e402c0542c654041d5010b040d140065901a00c1040f8425007012810750195002400c0642e00600c1100514007050050000d4000d40e032149401117462107050303030010008115500110f010303070726081a1061940c1324087c0c1c4240c1a00c05e041845c1c80880910082c0e0400c0c0e200d444524060044604200f4a049518055007482804841c10042c50740c079514100d00300942821490b20607031041003104102d14204001c4d40c2c1c001c4162a25915000010800d1401c0d200103540c01010b00700644424000e528150031020050b1032007400290408110100082d6912200546228055000192504a03450b4441100c040c9504405000c0f0840c00b04e00d050a10b66000380300645880d440c02102003550314082c010111f00680b03060b00c041c14000084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 271484127 1250 271482877 271482901
    0x11070c0b0c030906030c030109060605160209090c0301020705010509060a020405010206150a090c020102071205090f091905011e08060f04140106092405100519111c120501030209 78
    0x481401540d100901041d4001d503107420082d440742066070740198507075151115080c183d40c580e800bc0705c10b00109100b0004248600300101c407000341c0485076400c040d00c890070b04a0034144030190b0950554000901c100c00d11205400c03080c0101d03c02011510f40703613501c4100b04100c0c000c0f4010540103812080201d449460344050000c00420000c14462070980d861180c18212502c0010000160b50041340c008288403a10079400c02e500c901e03040003840c004a0400250890308800c500d6449805404040351250642000001c040ca211080030040c958403881e0001c0340f180314420b898050003940e00c011542d940042030040c01041c02c003150f84601c0d110365035550414480010035449070b6584040c001110034560040c0721888508881b81c4005041024100710382e000c00717411142c01071581802c0e400a01e54000201e441d108225140100111001790303048880500a003a0361086100301c0e035408118070881e11000400c07054a48543e05044800c009600a80d071007440060b40c0300310441c0001c1e034000040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 271485377 1250 271484127 271484137
    0x60903080a050c010f0b0102060f0c1621020715030903050d0506120607030501061d0901090e25170c09061c0b010e0f070c052808070b090111070c0b 65
    0x981060350803c10348800d2a0308540e01c2070040d042450b140d00c5c1d200e89030758040c0240c40d04400d03820345040d141e1400210400403440383d02000e00000581c0550201800201118600075004081c054076654107607510080d50350600e0b01401400c0e0202a9998264a0092040c0d4042d0341c2c0c1900d4260a04c0f030540c580d4801014005c085a130000e002506600001a00b0b0180070f105443c1c03074500241d6941442402000121910103072500c1c116141c02840065480c550b07503904541d0050404100060682e456608240e041c03900e48c41209042c0c00640b5120460280c1e00b0242c5100000541007070815140703280da41d082c800301150301700c1100c00104007142011007070341c070b5203814805120408010543d81c20400394000d03840740700b1280062041c0901c0c9100d544543c0c0d040001460024a00c220a4440540703950340581c3c0307244214154000d041120702c0c0c5003244802c560b00200000c1e142c41c49130900c85201c50040399200e000d9441e01f80604036214207141035420064022082050041c284000c000065000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 271486627 1250 271485377 271485397
    0x16050a0e0d02150a03150503030c060a090f02090901050105010e420a02010b0301060501021f021e12070305090f0d0309050312100311030307031d01031e021b0706090308 74
    0x51a85480356440700a00500d2884c05035940010a140c1028000d1061315060700602d10a070400c01c42030980c0ca03000150b15400c001c800c0c40c0059120040c2ca4084e40c40008490020f4001c81207030704201d100c0a065001904a810a80311504204030348020014190f90b071800c04c80340a4402000316010300c501d0718100d003c0c0d41b400340d0b0f8040516151003240781c440e00006402e500603034451660750301e1802c0070300034070008003028002018001e229050641030700c0c44248a04446503404100b820071020003a00710003101415102e1556544030584001b1802d03041117454002003414030000c14048030300007410b181e10b01c01e10300c040c11035000e050004030040d00c0700280c16034681c030044c8401401003004800d00c038062141e56200411561841c035003100444041c40c12076110341c000b8044c640c082078000200c3c0d80c420380759401b414441041100142c00411b012100b481081e1100040b050140c0c0f8594003c0045010b00d0010b0241054603818a0ba80c800c00d5004131000100704550400004009101074450085 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 271487877 1250 271486627 271486639
    0xb011a1209120412110d0515040c030b0703020a110703050d0e040906111b0601060c080a2c041103011805090a08120106030c08090a020603060102030f04030b16050a0e0d02 75
    0x42106141e82154119400199480b08071800701310401c400002c20041c075440030360b03100014800c1a100c1c942c441c010f11000714034003107a020001e410400f0940911004c0c691001e03104426040280c2c0040003908031003a90780100c1c84059440030742e40b4000801c042143c4d488401042c40c804c40710000c490b00c0c009014000d4205444510f03280000700702c1d0041010000820303074034540f02d007030300e402c0c040c500c0c0b404001c06003e542140b0300521040e80d20104001407107400c40c25496440c103a0500446025444016820034000e800c52002001600c80c40080c07283c1038115001e104808900b116611148001c0c41181546042c030300c2400d9035004144c2080f5030000400080e150b0401d40c949400031164041e505035240e01072180d0040c04000c1e0144105094081b80380743c07004092803c40d10322070303035aa1070a001a00c83c1c60040005101d50b03100b0001c1b924001000072249407255964604402034103426107003040d4201e1440003d07441c052241040d02c40c0c10720175584404c0800c42c80400d0001030b910070322042c0d070086 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 271489127 1250 271487877 271487893
    0x9140a0306110417030928060f120c0806150f03040204090c0503030408010b0310060b0a031d07060207030231050a090b090c281406041707030b011a1209 67
    0x3d41284e03030040450103a000fa560301c3c00b001c000c002c02d1a86039007440b2048100e210540d01c0111040e00c52106481e240d050402e000030328000103448010707a001d080301c03884c0d08100150a401d40c1c0120258090304044c0c030000c0500284c040c10f0403c034010702804c5e016141040c0002005494183c04c10b1110500641200c45619281c001103400c690080d00058044ea4607180c00210f181810059a800c0c210210b00c1003051a0519001441c6403007040951003c158854442c5040c521844000c030104000a40071a041d840d680c2d400a5101d40c190b110aa03c5050762408442050031100c0034400e21a640c24068940780e07607804001d00050001505200403641d0b00c594520008018946460280143c00010103036419070104115042d03100d45c80d441c41c0c50702d80c00c18010b0130341412070801c002e4a941d09510500c1010110218060f40113591000c400510107510038424888041801c000b940c1c001c804082e02680c8802082c988186a0200303101d4010041141c3c1007068100b00c50543c21000c1d41081c0c0d5649 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 271490377 1250 271489127 271489139
    0x30204090506010e0c07030807110c0a06020703301b0b0f0412021f02180303072102071503050c070c03150606030506060904150803040905060109140a03061104 70
    0x40d092a902254030381e111500500a803841c03100b2007940291000080c51800f015642c005021a201a04140034000d06103181d01039414248526141603001808082c03005540e510002e60700c2d805032006552190344a14101001e041150310f100c00d1002e00702c50284201803040003201c5e80341001c000c01c1c6540203041c245030009a040b0510f54041c0c4991218141d01d41071604115820081c00107501041d0342c0a21b01080c03070380c0302c0c00e41407a540582409005031104036a40c00141c00741c0c2c40340c0b134150741404002086010060049086400802c81d074080c4091480c0706c2030160b907034500b41c1c01008a12a0a001e0f00c046441c8a60411507001c160325100605010301943c03040014911604210b074800c05601c42c07115039414901c10500200154071f0280110b081c450301144051094851040c011611042c07605071211000540c88000c007003980440ba61182da03510094024001501c00d00c2c0080c0441c800090030102d00502c4e2005228000d105600c43c83c990760f9913070020000c0c0082d06400c101d0512000980c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 271491627 1250 271490377 271490381
    0x1401020f060106020d0f1d040f0902041d0c091506030a1805011b0e1503060d0506090c1e03102007060516030203040c06111204030f0308060123090a030204 68
    0x1e0000d90024056070340403510140c48100091046c004102c001c0241c145c03441c2c1c813001c03a68440b0b03005544c00209000014142d101800b006c2c0350194005040c443c0c8a500384009840380c0300d0302d43d860000e50b4520f450450400114410940700405c81c204e480b25030784082d180c550002c43d081920000000340062044a54141280c1522010740340e036590348a50100c20202030942c0346071a03030145001444c2e040780c0303800200304441800100c80b20804c00300014015499681400040c50f40043c1201d0f114542040c010f592950038031303078540c081c43e10300c840703001c90880d903581c040500c1e1030040c058007040f040d401005005180320701da0b0081d45280318085200303116000c0028140c1d280035200209440c40d101d11303030050b200740042c208020144100100004946240491015505a071501d403280582c0055500e20b000c480440c508110304001134000300304403007c802c0503030081c860340301c9070090365491005441e09110750360f9050411100c0710301719030005401c02c0100b4030b00340000c1080f41d003070b51a40c0108007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 271492877 1250 271491627 271491629
    0x20901170114070f0801090507091205070f0e010f08060f06040203040609120c110a03080909040501020904020f0903100c053109050f0c040b04030605331201090b011401020f0601 78
    0x1000c04d8540541c420400c2d44104031328054071200c02c09222509101030b0042403c0f0781485004041c5d0716182d0940d040050901c005d0307004101c00700000414030780b504580b01c10b0b80403e01c610341c02e144040400141c07420021603580c1c4103802d130740503440d05551820300b804040c0d40000c00403507005503540c00300000110000e1070034507600070998402a8048640c580780011100142c0003074070603095120f08200040c210000c81c0c101c003900340c0380320b00940c0b074624049000e1300424549035402030000c40c0f0706110004440c00342c0403e40c401c42c201c1c0c3c41e0f14404070042c01104c0c0301071340c01ea00091040241c3c4500341c0c00d10701c080e2a0241d900640340680303120801000f1058009800c0303040d840351100140040011100c2c0c1054110a082d0403d503d070501c2c2000680f0141b0070744c0300c01002c982e10350300041e015443d007000c440d0480c00603260021210182c171000d10780360b081042d411449031980481e01e0515034414410031803055404400c0c44003071390804244103c07000d4401c24550440c410351851244007601806954 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271494127 1250 271492877 271492891
    0x812040512210d0c1b061e020712030c0503061e030f010e011b050408030a0e062505070b07020a0308070f02060a110607081909060621060612020901170114 68
    0x281c0320203c0b4a509816603814055030000c2200346903202000700f038440f08001109a005800180c5a01104441614115850044003929101050407000e0090300303000d4441120321a50100040c180c104001d94030740c08141e68841d0850032240e8503102a10940c408042e02000040071540303c800c0307004002d403e50b0f030300790700c0302d1104d9444005035080b0034142d0107420010b040a05000e4241420320500700d580340030f40014401080322006405500c0c0c0c8480f801c40c2c4200785045080c211501c00180300309000d00440200301c0e22440f4080c0b0000c0d00c2200c00d015610110b500800c81041e081c42c41d19544019001124250f8143c04205110001a541c0000501007040f07651a9070420080149107a4101800100044244507015041113400c16030340c861000820b800503c00120f80c2e5050401100401542c1c100d0b02802c1d502e200140309403a4002881c1e00d4003441202c1c1480748036240c003058141c80071100002500041e003030300148030801104071140f003c2d5901b503000141d0b14840da01840e411200940b090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 271495377 1250 271494127 271494193
    0x21905090307050303040b0331052a0f0103050603071d09071203050306040e070302030f030d060f141011010501030803090105060d051902130e030408070812040512 72
    0x1005507400c0c1884882c004110403400f443c241403030406c08501521009044034000c0424040003502c0204940ba044030301c13280b1002c2460301400501c0c0090f550001d0a4008284103007030010040f0100c0e0070a241e00790004054140401c01c1402d4005401400014140384e501d03005490700481c4c1d004e00710500d0f029911030b05810040e2814401456810328801d41c11a1107400c03100510340707012940020860360488400c0e9030004000060350f181c10b00706005900000c0d49400340300191082070b00c0020140c014609450f00030001d0a41d517013420042400144a4401103a030622070045191500e481c11688141060402c201c0f0700002808090031580241c10071610300b50048207011b0361710024442d09078000390995101c504980c0e1920b4007559410200c003000c1860302120000750454980c074669458030309110b41c0500c0030088402ca8592650885e020700d99241c442d003500014031a800068040841400300d007050f2505003002e0a20087e000841200b205601c2070611743e20304001c41c0c3c0007080281a681c0c400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 271496627 1250 271495377 271495387
    0x114070305040503030c011401060203070b0c0901020a050d080108010b0f0312030907120f03090e040b040b0601020a0b010e180a08090f010c020d050c0103051803030a050403020a05070b072d0f0204021905 89
    0x7031000c80f86810703042b0808550042c0306142c002107165420b560070440061b6425203c000c0507004034134018011000411501031961004c400030381001e0058182c031a50700082c0904080d14080c0100b40340d01039071840d41a801250f44100c42e40c0804001d58000308404242c0ba40740382c44406100c3d070345101c280c0440d80c040c1d00c074032040706040c0e0011000000c1d0072280f001440d81d0501351200d0a8000010b007000c0c1408001c00046001030780204816444c090b8401d0400d58590313943d900800711582c0c22550420004240e552100301078034045180d047c1954400b210b1801c1108071810f0081d032407200c078904ca040c0400c614880002d41d442a5030401124420402401070340c0c00350340010b0070390b000174085810030b61100101c00e5001d8404802c2c0e07540410700380c0c0b002901c2d03641c83c2000c030f03c0c1049802024043d4001c211010139060000001410882e004d11a04024010040050411802c1801000a8003600c510040000503100c1c40400602c600040c0302508010383c40d59041c00c1c003c100ca215102240300014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 271497877 1250 271496627 271496651
    0x406080712021c0c032408060c09060a0c030c0b010e1f060c0f08040b0309060f09071d180f0106030201030b06070f0b040611030c070303050a06050114070305040503030c01 75
    0x1e41c0d82420007030765105600700500c0c48074403224800c1105000104641315081281d145110340d00040284d40b50000403400340c101d400510140c40900c0c0590708090042c2c00000701d188601c03d04484098202400c11841d026680200710340b1114540740480400445c1e00601c40806e00803183c00b0302805101d0041966810941c466120000e40d44035207075000103003864200311054000114021540c1c1040301600074038001c1c40e100c0054401c50700140790b5004084148040102e00255a03846503a03d408103503680d0300c50141d0290f590760240320b900308490400802544400c0c0d0281f002c0d070400d10008142a59010700205103051070554010310010341c0d03440c5020825582d1601500b01c0820080d0380c007a1a01b05151689480c81c01040340240c02440701901180400c1140d620650380051041d0089489003849842c542680d8000c40341900005c1c1040c0108607030010501c5100215036050310b1f60115003401e44503c41254014503829401c1c004140300001c0c150303c0602c02080f0a0004000000d41010050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 271499127 1250 271497877 271497887
    0x30806041506080c1e04030b0f0c0702030a110d0c0303210519051801020d0501030c090b10080c0c0f0d2a1112030a0c0605070c02030a0f031404060807 66
    0x400c1c08084000c098010440030f60481009500b010303003c40750640d81d41c4060041311040e07036189124000f42d80000703000414082c851046501645840030002e120f511080108a10f40c0110080070707501d504004003041c00a41c0d80042e01007500005006000c4400e0f1135103942c1d10b4144c5a0740107a0200e94030781001400c001560f44091141e42d1180000c0140e8203088102c10b6440460000c040c261540d6100403c2540014410250060000708000d560b19580068810007901c400e2004031804981001c01082c224002d026100c1802070141000010150400c400c98000398082c255200900d020817054030340200600404000741014402001894895040144021901140c40180d2000e2042481501e1520b1090030b880702e0b000389003d8100d81030f5030001202140542002c102a1100041c4c070781c141a000314441c48150f011300400c010f55070700c0345000c1c0e502040c405030080d450741004e96000c0c002504184a07c041e039000386130041c0c19864003800d04c450333544141c1000000c03806007410850803545c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 271500377 1250 271499127 271499141
    0xa0f0e270106030c050d0506011806020c030706050a020a15150f08060f0103031d131a1206060d020411070804030317151503070e0613060e06030c0f0c071203080604 72
    0x680b80070130140c00358000051107802105040307501c0545490215030281e01c52640b4008818074640a55040d42c0e84140c04ae5440d034010184601074003030300100051480c042c0d400d031140303011076401401810307509550326001d04010040321180d481da940405a91120070304800c0c006403030b91010040f642c90400c072240745040c6005000740d5402e09460014000240c1c02105c1b80104080981d40090841035140002c90301c0316001a820100d03843e05070b2895880f9905800c8000c0304070203030b803031b04080100e112009860b1102200c8654100b007030500c200005050940c4803602c180c00c01078050b401d1078416a1944869445640140c0019030102d800040d44a01220300603009030000300f880301c0b28650310f0042402c1d00d0424a4046800c5804000a400f80d409148416400d5070014046942c0341c0d5500c82d40380d2400ca45005400000780040d180300c080e401c0850440c5d015050f4a40301e40e003401c070000c0300003940764007000f54940c0c2030140d540d001400300e010030f064002480c802c0e1a44019441d18200388021a001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 271501627 1250 271500377 271500389
    0x110d06050f0307051302091323040305090114070b0f040201090b090d02040504021315091a030a0f0302100f0203150d031205090c09040803010602010b030a080a0f0e2701 74
    0x9101d40020641e800150780c0c4111101900c0341194124001150070090003200e8819400040c1d00144a0315511142d1001850150360461040c000071491101105000c08490080100b480ac0140d601c00b50302545c0c400a03510001102149040100c3da910f0a50b4034068500c11010000f03041407204540e00148040040c0000800d41402d040100700015400005003034064001d40e5140045010342d21600c42c40c184040c0c4045c1c05200e07410003e804007010025501c01d4540b018034001504100814200b030000c0c0c0f04100400520a00000c2c0d00e0305814034401000480c01d40c03042000c0308028034182c0c050418100382c20f030b40040e124505410304065004003510183c0c850941c2d00783c6040083e800a99115150603030000c0003480d980c0b82034866203041d205000c016442021502000100180c1c0d50007941a01e82d198002d11448070b401092643d00c00a40350300502500c401d000e003079240d81c4944403506240010380390620441001c000466003050205100f41a03d885040302907800342c007400041401040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 271502877 1250 271501627 271501639
    0x607061d0106050102120301090c0c0f140d0512010b0c010603300905182d040c05040b03030f0703020705060a121a0d0b0a090b090f0d0f0c0b061201110d0605 69
    0x1200e40b9461106c0d200501a8020f182e5440050814941c440c0242144a99000d11413202c092001d003003031920160000071220f5917101c0c3c1c03140d2241052203030040e56419020021410505d03424000c2d0003019820107040e10f005590307900800000700d5075a12000042a407101e490484684a8105130a9031803086031668060001d14801008181c607008040c240701c02111609801c40d4440704001c043c841c4000e0b20762084d13401482c01010880382c4207200c15006a00c10702625040c2640c1d882400291a481720101d83c0c076400520600c0000c403010001498050310a1058810a40e1620001006034000802c20070010b45072030b10003110031050f0311407503501901403100038207404901c00c00140329a1500034010704851050307000c6080141d03950002e45656a021015a4192600307240e959901c041001c001d0040340b054042d4401403034007820b00002d04245c903585600c85034006848080900101402207a00021545079403042410207104500e42c010045031195a121a080d40030300c113440c00c07a0496403060b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 271504127 1250 271502877 271502893
    0x90e090105010b04050105090a1e0f0e070c080309030408061528140102010212040f120801050d0308091609020a030e0c0d0308070219050304030309090b090a0b0607061d0106050102 79
    0x2075000f40944040303410034a000d41e502c01c3c0040200f149814142d1000c14011221450034400310103552030107003641c0a1601003c076203aa50800b2200300074040d5016404035988420714800302d11000011540a00d8940443e440c0c25940c400320b41c038041084800c91030034194205040c00d0361402610001030525249203c00816030602030192695049100b02c1002000d90480600e03140d0003034060310100310180340c14020354946810818005510b03c04110303000c81b00d0083d00e01903e40a500154103940d40548850507402c52554207844010000d48110700c64419072103825200300321491001c02a0400c4100543c03038425548c0d0240685541d50505a182d03046421108410b841d43c403040c0c0260f68040c5868089030300c40c1142a400c0c0341d2607102251000d5400c04007034060040001c0107000300e92081d0b540c0503240da0703141c01c488211403400c0c01c2c59500c6035482020500c00210b07904841802c40000f8280341c80c064095603100115604204181e14600069030b41b00b40c04c000070310440c0020702003800940101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 271505377 1250 271504127 271504139
    0x23030f0a0218011b080c0d020c0a080709050402130906090302010c03060305031207051207170f130b0703020408030c060414060105101215230a08030a140d0c090e09010501 75
    0x101242c107481d50401c104201250410006041652402c1d60401030340c80e500c40c00121500d46650b00c4c100f00501510440012071b40a09041e2516800c90365214064425542440c01d0f40002d424081e1059a000344000d401e240d6a21480c411072610360b2040c400010140414500a0709603624025444c1c10305181040030408240d000c02100c141e104130640c68000c955030000196007502843c5503585c0245403c004001031160000204014450f4444145d4002d640740c0201c40340040c011115261700e1141c00d541000091212016181c00402034203002d41020b07141d140c0d4600d141c01102c40340b4100c2d80a1000c0c0b00074045081c14180c5603002d10750181000e0342c1040003141d0f6841c0c450804500f00300480640f00102245a031180300d000c80882042c08140e9a50040700051206241e12000201d9105a091481c1d01d842a820350844800d1400f0b1030502c40310520560f05140c1c407281c0c0e50b154244c104041c6490a28a00c00d11000060360380b903003405a4100350a0f403102c528018026000c0d41c1c540b0b801404a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 271506627 1250 271505377 271505407
    0xb0310060b03061203192d050418020a0504231e12010605210c0a0306020403051c020d0e0406030605090a03110613061e1a040f0209060d0c23030f0a02 66
    0x281d0740d15092030a80e000d4a807110403800351028800087d8480c004001c0784800d40e0200080045541d5105040c8002c0c3c9042109400c900c960000540480c038200010003c804082043c1d18001207a10841e01004200f1f00105404000ca0b100c05c0f44c46074002c2051081d2450850650602c04010380000c202c0c2c1400d01012511107104040b420004d1002115076980d840010401c041202c80c02501348051b0755961718104019402c140800c0700c06005401c058422040c4080009004680c03542c02070200f8042d400c010303900e5001c3d200220b9007090300d5040200208016001b0a4001c40c01d0500400301780300d40c1d0078010114105a00c0c021040d40103c014043e2064454400c0c1058039001000001d140461004080c40c24690051075042241002c4100115001009244211110641d270911080c0e0012200008034030130113414940c0b01605000c948150b0f081e640c00090748800310305080e0b0a001c2c02001c40c5000400c1c450714010207800000400507100c00446500750411a40c3d1425414115242c840c540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 271507877 1250 271506627 271506667
    0x9060606023919350f0c13020405060c0a0507050616060209010504030b04050109020a080d020a1103071d010513050114010e011b0f0221100b0310060b03061203 70
    0x1103e4445070b00001e5446050840c0c038801000c00d00c0340350310b034240c07000854404e04182180d0040c029513074031045500303104081040c0301e40300020809040702880000801030140c0c10300e80c6141d0702c2c0781d007400b0204143d100c841c024031700781c803003d00284103c840c0c501d002071801400d508102c0c0280380501100503c10301d8040c1c0d00b2080c41c0e12090260321342400000484040c0110341c0042d105046013018841800019800302c039142d402543c0c05e07000c05d0780b10a8101e585201c494403031001a4044161140401c614042c1030110031001002d841030311f592901140640810340c6102c031000b20000004100e589403020484051007042802070207258585400000d05400765501141488481d00415810b68451600300e010b0b010100207180c01c2ca40700e800e01030540c400040041307004110604880840003140c0704e6220700303003001c000146042030803400701c040604075a10342e0a8140c491311500f600707400040c2c01010043d0003095407064a92a00740e04000400c2040701e5604443c4c0c008004103103046403c405140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 271509127 1250 271507877 271507879
    0x3021f090603020f090d1a0a020a2a1a07080105031b0d0c0b0301080c03010b0306061f09080d08070e04060e0a0b010909050405010c2c010e0103090606060239 69
    0x1600c40d444d1030102d110501c2551001e03544090742c481040d00300100c41003a44004802501071151b9503807150040001c034031503070201001042e04000d444203410044110404251f402881118080d50159219021102182155001c0b0101202004030740350340b054450f40180012030091241c20102e600340c160800841c81e0050190508210840c01d201994200100400c81542c0c40b555070b60307403915040e40755403900000d41e22a50901d0414080e920b0001002d60044500510403d2002c3c003881082102c10410524a0b0a0003194080003174026014403505c2c0b04150b0a86840d01c00c2c1c0303091840241240f090030a004c1c404c92400d6028405014104909903000700e06100029003c0708403001030740e51000c0341d80421300441c280001c110030844103411144114600e521081d030b05040102d80150040485040c41d601c070481900c1d944550f62142012030303c1803106060000d0b840f8000c0e250a4252615600000090f03400001c4198525404e0b00341200d0b040150303e418011200249040c0307c060003011821 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 271510377 1250 271509127 271509131
    0x60b18100e011b1113020c070b090a051009150512070503040510020313140124150509040209090a090506090706050405040209042711040506130509160b0403021f090603 74
    0x11100300400c90881e0b1140e804020402441d2418034074400010313501c00d011fa04ca59014110700058509a14001d03035035280402041d0300032681c10401400b2420010b40090001c00c85140e400090f80d21904400b22410302240d65210344d500e403120a00c0854400140c9503400700b1804004100c041040403902d260a0300c038150740540e42e51241c41d621079000d1880f800103001e1280102c806e0304a4601580725103926004441e454809076900c90300314910680394496425030040941c03d078134409109074024908220020030050420103500e011480601084404010141e96a0342d024184035041002c00d9200110000504a03213041040c010018003c5116550040f41c011808651035503503500910031b0064400b01c05440c44a1200703881c002d01190f0f0130240c82c03011140c2c00859182c1000e0056900c54540907100400050b0403020000040c0b01c003d000b12040d003c0d040d001c4035a14045a00d450080c000165207940700c6095004020040e01586101c4101d1032440700604c011076008203803a8101c40b014180 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 271511627 1250 271510377 271510427
    0x6090405100b190b13150903060e0316121103031005091503060403120609021303031b0b01151b0c03080705070b0a0302030106120627060b18100e01 65
    0x30840d141811890308200041c2c10300c010079144160b60141625040c88400c0030fa6140e07a03210618446d00da00280c090004201ca20140085004c9410003c00070310084200d03403030200705100100501d0020741c6d00711201c0b0745c09041c40040c00d6202d6048002c0031484006545075003000a0300b400d42001c00c1c8506401581c2c034070001100d05110311102009044040c00341c403031a25003403400034240f6032035008040c140c601d002c0020030b59030f00364030a440705600b184d1074014906040d51019a824091400e2000305c244040903c02e00091020f007a5500034507821140c0361031038050140c0600300320040d50711b007803a0300c602420143c003244100540f001100c2c2c10500690740c541080c18261700345556900905403c080000d4029420f59041c5e00450403a001c0e40d59030170260030b480000006a5401c3e205100c9a856084d032151030406420079440401d00e0b9280c40042d41599817040c0329015003140c00584440d80000e0226081401c10b040008007001980c5411820710848000280c241400d0346000c2452190340d0070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 271512877 1250 271511627 271511629
    0x50418060e0112030e060c06100b03060108040b090a0203070f091112060609030a060228020a1a0a09062412080a050307090e42130908030406060e06090405100b 70
    0x17002d503100820142500360751365041c07210300303543d46016912240058860400081c0c0501a402034a000d038905940384030f6651201e8454000da148054081c03a4940100e044ca8001a86c3c1008100c0082600c411305c4404140b8004000d070071590040b410321507514007005603100c00302290342001c1d8403000031102180c5070b0400700701092400740c12241c01050103100240948201d01568040d4400d800300140d5036003002501d40089031201c818040041180b58801c00c050380c2e011504c07848562000a4100000e1020041d44070001070313981c00190003001c20b200f4600c0707121440b944508a00600180d0f41e00003200505a6104e200620901041e6402c20002101140300070380b140c52004000d00d041039618001c0d01f0020030741091103800c1080c0c001c1d41e00c1e04035103032500c41c20000c044501e10383c68080d000308030000100500003130303d80c10100b82c8015a0b45074503000001e402c81780550700450060b08005070450810345580d1907000042c04040c42803c1d00e40811000030b0001400c154540703d495004940c40350707014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 271514127 1250 271512877 271512887
    0x30a021003060b0d090c1d06090415061e140a030b10030212031801030606090b07050f06090a060e0102070f06020c10050106050a1e02030702120708030406050418060e011203 76
    0x34000d203c8200001801085850329500100d80d0103015040c0400450345d1600c620001401010a8076a0144c000002400c2032600550030b9511a0103400aa13041901c00b4000c0000c40b0400e4009054500300081c00000c0140c541c80710001900c0c0d2a820003007105060030000b0802c40517884020424124480003e804501030f903e90340045501400c1c0b0f200103052010b00729200d8101401c191802903900d0002040d643c802c1c05844c0c122012030702e07050300075410001d4590301c0d940040f1003a01c81c0c0c440c0c00034910314000b0422941744200e54040150550b56031620300074098401c101c42c080403c2c1c0c0144603040104002c2c3c1c800c00000b9074440c20060f914184d410307615007400341d02d9100c0d07411700d85048000030300140c00500034042d00340140da40040120045001e1100221162008401640203005070401400c0c041070001528203124202c1d8003481c3c0c0d800046246034403d40214000890200d41080340821542c0341c08003c05100e0014005542130a03500b10ba0400c0522541d05001c5489038400c041c10b02407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 271515377 1250 271514127 271514129
    0x60b0901052d0604030609060f05010506030606070f120918020307020303070e01030e0619061a0301090c02030c07060915030507080a0c090b1204110907020307060c0e0306040309080c0a05030a02100306 88
    0xb400f0151075582e00d0034250000d0464102c103940003401c14104c240440c006102c0c45050fa94001c01007070441c2c03111020310010760002c10084985024040c4400c021580111a00c0500c820540c2c51009050802130801c0d0010620900c5900309401131040c44031f0a030300401075a41c000f0007854400c29003105040124007404180d499240d075405903d090080800c0754103040310b80d5151150091212903a61001c1c541002103e00401d0014002840184032400c0030341c0207500d15801d644102c03401c201d4a04040d905103e40c0b640058081101c04c4020042d144200400300306003069402c04214524000d40d01400d1200000d2204081503510609040518043e03d405006008040c3d4896201d000140400a0b140c0c01030324103450f020b6813000000807518000c2c4c5010b00c1101e581e40a18208012581c40c000506402c8035188148000c2e80d194280c40d031010003c441c82507001e0340e181c4000600c0d1a03d920700b803500c1c0b0224140503e1b00c1c5502400340303807000510a02429411b4611550515405400301e00410b21 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 271516627 1250 271515377 271515379
    0x121a10150e0a08070e16050f040803190c110907090906060306081002030c12092410170703080d061e0303110a02133303060b0901052d 59
    0x8120305540c503a0307840008246441e400b92010300c16103854021555603070300284104d415450039400040c0e0001807039000502007000c141442400c0040c400303d107140701c0d001074001c014280d1001c00c1c3c2e6484109890080880d100700c0742041400d52030070b912905400980c140d1590f004201500200b0801d030b11545c410307001451116002c004103916428001d016040c1481074981501c01c440f01030494a205200f200e026480c01c6000d645440344102c03c004402c0f100800f200114010104d105000d04004c9806140c0303043c0200f4802468500100140c40c80c00d040e41080300c2c4481d1003001d5500342880010f5000a580e0001c901c2e82e145c014140003180500180d810050820059229501d030802410031a08141d80c401c1d00c6504003144821203199543c00c100c04060f600130031a0202055030742c850741c480c4150040c000079074902412a000303851030502840c6120a5501001c0b1004c0041c814584031702101d6140c100c810000311751609000903403609010200039a00024900320a0b60984000c030051f07030b0240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 271517877 1250 271516627 271516649
    0xd0206310302031e0304120302010605030601030c061b05210c010e1e0111090402070305070203070f05031e0606270703140603030313031d0604140109121a10 69
    0x1a0304992009500305444100e000c3e21607007a400c0340c4002d24500c4000704035525030003913040900e0100f408981000c07640007503055551750708000c038007601c1c1806914040c0d402014800010303481e000c2e00800c1d0344100080d101c40ba00c01d404101d000903d0205e602203500002c02c0e0020305407698100f03540420311403400881050344c42c0501000c0340310000300c0d0036099120705030b4002868227000c601103400d0311f80301681101c02400c100203070402c61a082d805443c01034024503200b03040000c1e03640860b00c1c2130f4140d0800c1400d940001c0082005160030402c011003c20302c040e80700d11544400d0505030350780340c002c0c0c103961160a060b542d81a200b01c842c00d003074540c000d18030340346082c1e4105840064000c0c8a24042e58050f800480b0004125003400402c90303018100301c0142d400c1041d410384048070104403000600c5a214109015240180c0e03490b00500301511540c002c0c0103403035250760700240c85000d040d844180b00721811013055000c5502848900c42c0001456010341c0d0590f182c10590342500f6041e00481c000340 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 271519127 1250 271517877 271517947
    0xa0504020d0f1802030105061002120a11011e0c110c12030712170f0f06010c0303061a0d0506040b1c03051204030210050907080706050c2409070b090d0206 68
    0x1494070f4280701d03241e0094008004940b1170710140070310560110216000b5034004040290591140c2c030040020019900d0b04248480c2801c8040b0701b500c641041c034180314508820199148081849012024803043c2030002030250030100f01c0b9140d2126014041c400d40944404046445007402100d070841d074003190510f8070440080b0054440c2034280c1909141010004c001100c1562082a0706d006526032203240030180e8030007004440c1200815400c408154550800003130b1460f0080182882c1220b02ea2280d89484c0c0c0740d103101c412628010041071089003411500900c2d41c443d504000b5446081240052400800342010703151481540300d68410b03205518104824141d001c6820500d5980c0c0c904240020388030034075965503414a600880900d030304004010041c050107a00200b42184012041e00c00c43c9a002903210b07031812842c10095068015241007000042050001d2005003061a44040c20002071101140c2250300b0410020302480c0002400c1e0110440d1500b102c0b4420f4100c081c0740d043c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 271520377 1250 271519127 271519151
    0x80a1b0504060e0307030305030411040f05090a020102160e0c0a090815040515090c010f031b03050124050a05210103050f010614090610090806070f0e040b0a0504020d0f 74
    0x558007901c105400602c03055442011881c3c0450800100e03a01036452030b040d602c481d12030a810001010402e0f80c030541d201c2104040d5541d0340203551203580c8000143c09804818000641400c01c1113200709161140c00e8801d20000000c22042c40c2c000140300200350b264400e8990645662001d50070543c2c2c0d034410301e80c84501259107860704512680c490800d5a10403565a040387c0325915040c2c03540501c40d00703d02003000017544101c00700c40840d0001d00e004079904e610040c02d0380d8046c8202a0080000f500c60005002e90101c84a00040c1507201c413040c0e00b001140c1c66001019405500013140c10003c002608220700f4041702c08100103000442040c01555960b441d186580d4984110032600650a044000800ca40041d40552640e0b42c040c0200c013155440c9402c01c080b0f5900780d1040800d1005403000454801c3c0c3c00c116861140c03074552101700c201500360f40301a088030b03c04000307a4801d0b410b200210259854031002401200d209840145c2c90b140e03400f880d040506846d403038014100d03180040711554 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 271521627 1250 271520377 271520387
    0xa080304080604021342030803040c0501020604120c0c15020c0108011215020702030a050a030201091716141e0304090c0813080f1603211506080a1b 65
    0x107641308a5000c82101d500858560070740d400c2019040f103212040184003070010410740c589030511094110138441608418512202070f1841e0026107501001004200410a62500500181800340001c00d040e142070703510702010341400c01c884000c01c004801010100296506550003400d2491002c1c0a080704e0310328000e5480200b00c2807240003aa0b81d030000985100d0f40202960700a81140040d8140c05c00e840e1100d0281d071154404a8140c0305070000c42010032014420118418071070350010074000231034141141e1010107698001c88444080110020800d6841340f101c1c0c031507600460f08000d0890ba0a0001d082a080023000741905a1040900c506400c0200048c01902d000c45400c01c090401800101c03801d9904072100232284c0c403c1c600100110340440094042401c5210845251513540580c1c5043c824481c18210003281d044a48500513021640146082ca2001070082220107140200c4116072101c40c810002840010b60100d074074420250002d50744003a0004441000c01d002410080c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 271522877 1250 271521627 271521631
    0x60f03030c050d0e0a05060c0a05010204030b101d2409010902071a09031e0d020d0203150d030518120a030e0307062607050706050405031c0203011a07020a0803040806 73
    0x402e4014100c282240501075610001c074064080c0500c00c0f954103000030321403039500105040d4881e10030302c50007100240c0c00f40000c0c00074610031000c0300f2a9080c2a0400071500c10f103600f02c0c6105181e204a0007502c000c103c6006d0b503000042c4907180f10342150301200307503028580c0726540a402106060002c10885072540040400780e20440c2e144044081058a040a408096501d1105034104001102d880804011415540b0081044040c50b000e80d154060089034886e160071038559801004020120102e1a80355101000c1560100f210400f16070b401403452081004090800c011030402c0401502c0300203442601035401003c9642141c0142000740000032080c01181c400c3c8282c013404138516200300030140803041220900c1c42c0b249e04c01c84103c0709154004060404000c1300b8030030382021170058002e0701c3c0158010303005550b03501048000c2e018140611036040465130300402c010030000040060407100c49400b4607074680c50307405910004085080c6035228050381d120214012804c40e1000c84d1a42c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 271524127 1250 271522877 271522883
    0x506280f1b020105010e0708041b030c090506030d141308030706061e0308030114040f0227010c08070227010e01152f01060b0724060f120303060f03030c 67
    0x8048150742503012402c0c0c0d0310901641000d07400e001c1c08074030254003980c0303220781040c445d59102d05d01c0b036600c190903d5034028661055408a00c0c65404012942003845020f400840980142618224460020300704451140c00c070000d050b800240044065150750400300600042801c0c3c13035894a040c01d11001501c501d00441c442c1607070120049900804d012040811244d001300c10604682c03030300910b10035080340459a1a041034544000d000e8516592008140089460025040350030b0b002c90b100d40300c3d0346540c1c9414180100c001e0400081504581900c0c4007a50440300300c025891b00d20500300700000c42c0519a1810700003980007242c10300401150794141d81d000c0e4030760f0615011103842251154001c400c080000c0342030307042148489801e84589c80400c041040040b41c402e1b42c0c0e4950980d07940c04688152038801042c0300001d88a14401c1044441882c000c20500200d828040d00a8808010b4070440080040d005680d100b094040d030400802001100320014009660f410060405206c4900031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 271525377 1250 271524127 271524161
    0xb1e010509101e050a08130f0f030c05060c0a020712020d0609080c0c010c030c0f020f0901090b040506030f1c031b03050109290f030a14030a090e01030506280f 70
    0x1d441ca00e03210f80d0640307a0b0104161b4910400d9160308008400000306130030b050350129841008100441c540658516010f8807942e901c0c0105100e5042c1941400ea01404502881c5c01c100b0951100b203070700268002c1601d604a00c0010303844c41620004101440c0610010900b508100d00d0f2000d0024110190030403c14500c1600c01d901c0e8000e0044402d03690140d0020301150016211030b02049400c1d80c020040c0d40301402001260845500042c0c0e0010260b1291421f035464000f501c500d401c245c05240d411a80035402001d088150b808400d403036040c61310160440300c00c201c1d9034111541c465000000e41005280a150f032010441d00001d0280c1401d0003860880707820000700c403c3e00c000a51351409612502d00141840401240130032418a60f0048850390510800405901250040c1480740c43c1c1e0040200540c2c0e40e08800e280642003000341c5d84140e03140183c101c010008134401040e2190702403040c121b001d20203030726844841041d032400c40005044502c0c10074007603407051030f0741c0c001822180c140c1a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 271526627 1250 271525377 271525427
    0xe030d0302030601080c070807020d060c020d020a0507090c121104030b011d040602090315010807050f0108040804060c03170f19020f070b0606040509150907030b1e01050910 76
    0x40d0168401503600b00d0004900c0400102c440003607030050155181f256080c146031100c3d540018100e5030020f002075452940d102496001940c04000b0443d089486002410800f8603c0c2c47d500d8440360300e4441d00e11881d844900030f01c45148244020403803000e11910030800b0420340e8044006030f410500048900350100e00000c22241000b64072046449010310881030b0315503540d5100d134081e41104804030f405100d00e11115044841607140356010700060401402d00901e00000c002203002c0e280041c0f81032103c00428440880c41038801c07182510001c0c10181080361061404986c0f0f610819a940031084011050010070001000550b0050442440549106c1d4074803158804a21500d451201d0300740c0e0400000c0d0000380c50040c003640c4a10020030082c241541c64000c218400c000721500d1a20401c190341501881c50131204454011180d8501088236220140220b04074002c06014900001030742d03a103203070b5268410412111750020151075203000c090b03192409000c00000c03000d8205c0710102191 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 271527877 1250 271526627 271526653
    0x405010f021603030b0604050a090b09071715031e03031b040810050a02071205190306060806010c061b02010608100902010801060c0501140f061002070f05062203030e03 74
    0x761182032481c0d2150450b0110039035410780080504c0010103800110501000034141e64005c101c8004194029010450b60b60407820040b15000c0205243d00b401008441e118110300c0c4c10a48036846070314003045e240c1820b104d4000a10f02180100c06807490a81c0d00b44009449001201a500a2000d00d0886041c0f00c828400c0131194010b42c010128a6400003000711070300c40080d00b1280e08010485401843c042550300e03603803810344492100d000410390000b404d103600e40c00d001c8900e00a81c00ca10b402c004250030264014690700340a44a01d0410402440780c2040c0401c80d07100b845002c0c50b0460400c021100000045d000c0c00c968480d502041c080e00c418002495000d0080308041503050390380040f90380c00c100042d6002814400155203944d80c5604c2c41e10041d82c070011180c0141405444a800d81c54060f00f004140e40c0c403090040210b40103034400f001800703661008401601e400b110501e03103480e110000c00300d0080c1280c2900181e401822400428550030150396805003900307609031081484000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 271529127 1250 271527877 271527881
    0x4290a06080d0819021803010f060608011a030708060414040b06120f030d090c180204050f0d120f020f120a0801062c011e030b04050a060e0c0702040605030d080405010f 74
    0x144d114100d1986100030846600d000d60061080c071205404061a203400d01021a003102d4000b80220b882d00c0d44d80c0703010301c850f0350040f02240c014450300040e0100d507402004200c2c2c02e401b02605610501c103c48000c5035440d92103401c0380c0c6103070b010005154600d10f06400c103101143d1062321201e00030f07004c00e0100303035030404042005911310314260000c51408054154076002840b03002026175000504003000300c1d507200d05440b00b8640100e640c2015071518105400c002c1d21403508258180706200c450441e0000801d100840716802e40a8140242d514400f8141a030410520b60300700b4442e402900156401c040c4130f075000d401c00240682d1910910380e03c851054580a174035461a4a0010f0302d40750aa00f6268002c544010034801850084244158040c01d580c81400e4080c800000c070b600c1e0807000c040d60400b4420954000c250003000d01020b490441d03c2c092288028000528030000020710703100f592999000785d402428040d084801e1840c000400a10f8048185c034101c5195007000000c0c21041454 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 271530377 1250 271529127 271529131
    0x60c1e0206040f050f07030b0a050c07150c091505281707051e0c0d0302160204020f07020904080a0f090e0a1d061306051e04290a06080d08 61
    0x540c00500003034490b40c071051400c4101d001c084445114140707400b40d01000c148080c0d00110320480c0e40040e103060102022050b603200425000c540c00050107500c0201d510b58401648800c0e000c880000d003000302000407191203003d40c0000d5410383d00400c0403441198450007c001c20004c500640f40142960f0340c00d000c00d55031810341000010111480b100e00c80b494003131125000481d03424054903045074103c40958940d0320201d2141341c00404070b107109200d202801415007035280c030315003146003041ca411a4118000079806c040d02a5902050f0556501034040071541125001001003426240c1490403c20300e511520503170b0001140040700da03151a004602c4c11043d81d2601c3c0103000550750b229240001002030503e4406100d0800910f0030402c14188501400b030307480501c45654980103030802030281c400240c0240c40900c1c09078210325260034860126508603a10001a04026001c44906580142065030100e0010300311030070f201c0c41940315032100701241c10000c1030316814401042c00741c91070034007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 271531627 1250 271530377 271530437
    0x240302092401120e0a0b070e09042f0307151701080d05031512030a021b031b1201060b04032906040b01140d15051009030204020711040504060c 63
    0x200035841181503005910081000001500010f06004c1018400e0f1030a11707a44800c3da4015000e40c24481040d6114408083c0d2001c02e031843d1404d41425603c40442c805903145030500c141c41c1401d4025002100c4502c3ca4001d40010115000315880700d901c040c203488034a4401c008201c8450180602c5004401f84a04a902210203080064404d036801e13601035000900d0102d000030007080c4000140d64481d6100c0e08900070034011501d0350100b41d00a440c284a81c00c8403030741900280503007001c1e0b540004c0d039001311900000a590325a202000802c480e400c18038902d020b40d50030a0004140c2c2441103025004480c020501345000d80c88200010100714414590100c01c0e02880c00000e80238100340d0805010303000107140c9614611000d08080482c3d403c080410349000b41c41319050782910144da40c002020f4030f4100d842800c200308074a80a0000b502d1880000d00654010603200c00b4004c1d08003100d000100050424407161421385414002031000c00000030100b001800c00045044040d5008a08148 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 271532877 1250 271531627 271531681
    0x13050705010e120f0703060f090b18070b030703090c091103040b09120a0315090b0303120901180f020a0e130212030d020c0715020604020d03110124030209 68
    0x400c2100441e010307480c10100076000740c030303038595210380580800c20030342d0201c40a80986011400c40c6031200660b00d40f140c00028217401e042d450400305010403d00c4d03410049021b98045120080308045050143c20b40c01601040d00210401c4400d0b50590440140b80e4803403808010f610340c0310003074581200c2d02c0246000c00040e0070f0002a00281100300c03000e4000761298112041020840d80030001580f144061000103515901d011481c400031038084405802d80c0c2070140318582103140466a03d01404c44801c030044041310201d42d0804080d881700c05c812000391640180d4020b00c0c00c0c600100080703e002240210341c02200000e121484000c0a801820034030440c07000061030340c007040545c110603409011180401c0207002c2e04c44400c0d00c020118444480060151945401000ca140800030024482903421038800c01005a40c1e54100c075068a6141c20100c18201803502058010100d0b034000760240c030201071030500c001c0007004140e01241d100b116003182580d14250703805082d0210350310880c5141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 271534127 1250 271532877 271532879
    0x50a05062505090a05030303072001050c07030503071803030e010f020d02120703110a0f170a080c0d090c06180b041a03060d0f0c050f0f0904020103180212070806130507 74
    0x1602c5103005181050005014000070f545a01c000780c2580e00641e122030118030341c9a00104680564004180c0b1211044000c000905e8a001e0000640c4038102c2d00074104840080040e48039401086c0030403400880e0100c14651a84901d80505100b0380108442c0c045140c0e040d4041a061000810028020041d80608400303a00544100226040607000300d0030b000c0c4142c2d0110f001041008000c515501a00e200d40c405602c03400c08054074058006914240760003040507201c155001b0100c0e681044041800c10303907480c0c282410b600100311a480c02898540e10103030026006034130452038450b542419141d03040913035a9501d000003500c114464041c0e0050208600b038080c40c0140c010390384c00701c80903020b1110921303130741d0324400071080b984000c940c1e02d19040340500990502ca494201c0a003000ea81050b40b140c01c2100080d40d80750000d000070704242c0c9030b0404039040481c440106282c035901409102c503210841409a40310324890084032260b1180400251070074100000d11080c0e01c2c0c001d0003a104c22 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 271535377 1250 271534127 271534201
    0xe0607030b03240910151d0c0901080a2a090f0303090b07030513061110020f221502030d0e03160303050601140f070c0614120414010504050a0506 64
    0x3110001d0160b035043c0500d1000c02c4101c1740a000b0480b41c8000c6000c2a09454180140301506480c01c2502131259030821040110100400c0e0803950346020034280ba20310f0b60f44048802001d001100c0388171102c14084010060000a580d80c65820034a030390701d800c120a42c0320041c40343c400301c051002900080303610304100000c5e5032407401005203d020f880c0543c54030b482010345801460940d4130000025040000070300000c4e07801c0c0005e40d9084021407080d45054400000c0090381e0090341128103591b01802403041d00480d004900c08002e00c2d405284076000300c17450102079100d8100d200040d07881400c0680e4420ba102d408003c842d6081c103220303400300038507995440c22001030600800c51410303ca40842942100c3e101e0078041c0c24402c3e4a801010713510919440c11020322002613118200303000d551900700c0c1e0106070f0101510030b81541140111019030b110b0a001400440c0240c0e1005c803540703003006004c01e11001142156089008000316000b58541c03482102c0f00b1041c1c0901c0d104548111200c1e181a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 271536627 1250 271535377 271535443
    0xf1302031b09010c080c15090304060f031109040e0f010f0906060f0305030703050a090b040306020d1b021f021c140c07020f010f121d010f0207021e0a08010e0607030b03 74
    0xc6c1008204555a2601c43c840c0c84110900c10390381d10701d1680c00070908024059002d5143c00b0b400301c5a15041c01500c404440c500220f010b40c401c1c042c80b03a500c1d070703580c02c085110070011300c45051403500003845000429480c0394020010342c1c80c2a03c96a08001001c0b40d15000c400342c440403a075010004526100d40c035181162281c100385022810802c14074030001c0e14400c00700140c40074500854005030f9580c0d002d00700c03100300c400390f02030271800c410707051103c0d40300c260003040c8448406003001c3c1d8070031505074840295000b4403503c143c2616039041011880045202d99003e800d15803100705c1400364036150380c8880c2a960164410003544042250241c001651040800303a0200b0118140b04043c04103140703003417080d01d0561a4500c05418513900580b0600403d02922b0302121f00220110314043e400d802060500081d04140550b0b544813012222041d00e030642d51100501540c8020000010301b0031415864200640b517800010382410300001c070601d000310344806c01b2079502680d00b6034000e2940070b1000e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 271537877 1250 271536627 271536637
    0x1908040e130b090309091501020a0303020309150103060b011112041e120f0203011b090902030601111002090a050114030601080a02090a06180e071704020f1302031b09010c08 76
    0x11181141c4285038009854002c20601600606001c0c64031545c0395001d120380d0f000020704110483c0540046a0a11390b0046032640c50540c1600c0c1c003582c1d90351102e00861030450011600c1e0390b0421840000402e205490340304c500141400d07601c404080740c0351000d82ea507880041e03050902526081100300002c00003012080c0c12214800000380103544c0c1c443c11740c20110340280301914000341d005491001c62034284a520ba04c50340d1301e1204c400034800614000d003128824050905010f42c00000304055a009181c42442908548200c43d6084100040c0d1001780d0480c0400301e000b000320703a8001c545076005131031141c8204181c810301d5007140e58002c01120f040c10302a0070f042c01d01c0d900300b000c08400d07104c444045016006548a24030b912070707801d041940000c0340da80300030b00c40c0c01e40b0400e102c11141d01048215400c044500700c3e0351a0313217440c00003860000d036028050360700040740d69040700c401c0c0642c4c000c1e51141030603201221740007801300710103440c40c4581c40a4078000703420007081d000003501c0400602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 271539127 1250 271537877 271537891
    0x31605130b0703030509060f090a0f0521070302010b0405010b070605040303060b0c01020406090e100501180f09050115020703021003090c030f060603210807261501021908040e 77
    0x484a50381c0e42520900551100800364000380d00c80c0704111100c6002c101054200c0d000c074034900c5c030f01e1400c012040d8a41c109542c0003000c00307a140c1d045005101d000c209030840780201c05403014034000e048148284036445078200710055402d01141c03014900e010301c2070904841028940782c2c90094103075a11002450010000ca080c50b0ba00e004c045070000304180504030f01d10440c0300050b52076051040141412600da03104003c000315400c00c02040c400781c150140c049074400c0c280100500c82010000d28003030459006201055041d000008826001d070700318904881414188018a00c01071204a0700d54a040c00013039000841c503e201d01c0320078800d5118482c068015401c00140030b03104d0341ca000e0f000c0304000080d120341d84c40d141c051040c01084480c1c0c0400d2004200681009064082d000e00580c5000f46580213000000e805003c0c0401c044a84001592042c0080141840c3c00c4401c0304109005040e0b2900502c03c90900002214060800381c1103207801c07166079401c203403411410076000c0100820322 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271540377 1250 271539127 271539157
    0x6090303200912070513020c03041503021809100e07020a061401030b0601090f140111060a06031103121b030c0d0906140304030e010810050d14010f02031605 69
    0x84141a006181c07110365100880c6540c9a64000100400110203500c0440440e03d07008500200a9940c075071a45000c1000072170070158480d80f15034141800e50045130f114520350250700c0b2054500b56810b90040607020340c03001c00421314100103000d2024548044030041c40c0e4290114062080038002000310b07a000f2003610454441040c13580e140c1065a00e4000104007002c1c10000500c20001c0705030a42e039001c4028602440064a4402020054a0a446201c9441448246059680e40324010031040c01c08840304480301d600303000030500d005040314402900d4030481c2010500c0d517407802044040405940024850800d0b01c11041d010f9404070703009801001d84410008543c80308000d008528036601c0300c2e01c6d20145549050000b41c0b100c0350b44d8159440b010310030000c200000740c000700049603c01d801c1c6440b080c15a00c4a1a4582803852034102d41ea105030641001b01c20044070741e101c070f012100744000138003241d001c90060100380e0206561040e0b40c801c0f003164401c5004c1c40303000645100c4141c0840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271541627 1250 271540377 271540391
    0x1b01051b01270b011707180f23070e0a03031d090106090e0703061d0a060e010b0d0e01020a2a080406030c030b03071401180e070507020111060f0406090303 68
    0x6100c0d0340b980d0203100c90508020400c58400748100c00c600a80100102e081600800c00280030007034480da00385c0a07460141302c607004120034203c403550100390801c198103002c04c20101c13180c502079400d0055248034068170680e407001a540a124600040141c807020b030503140b060b0b04640c3c0c00e4401380628160b51f28950088000381c0740700d5a0b903102c014000d089980310084c040c0e041101ca544e003000e00600341c1e000d250604c4400c1000c0d24480c042141010080516242d003038980030891000f92140d030b4000c0610294050001c80c403415a03400070000504105000c000c0c0c2c8d02d01d02c400f0b40c242d00a079606103000c10040c030f841580448802d40d040c081039006060408184d03240d40c0e298101600941c00040020fa65102621400e5400d846040076480e411001020114904810b8440018014a07082e041001d0800703d446070368a800a158040c280c0c1420451040c03074540c03001002034004007000da0014110600814848402080a0380a0703945140c4440265545031614005808000422000c055039108 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271542877 1250 271541627 271541651
    0x3050d0f02250b160203040b0a0e190503010b0901030b0103060509030d05070306030b011d0a021803190b061008150a0e1611120304060b15070602030103051b01051b01 73
    0x1040c840c0902c400781d000030400480c20140407142c03000b400240d0000d52503800018035900001a5000c80b0303d6018890f41d181029241101c480c00c118034050b0300f00d58030650b042d4010803000020016034200b6030003080b070717003410908200c0d8558082c8005020078074039000500110fa00390700480e6202c0640000c036403518160f1a0108100c0700100d81c8040000ea441405000304508202218014480c04411394030102c460580b4450807000a40b000c08020340c0043c03030703075408041801c1030107125174000c080c0d0b4440d24601c01c20406150a2500486400440da80000c44601e80450f010101e4912a510030a4690b00c4101c04907265484030381c0d080e40040f1000001811041d09500c00f8800c07001c0c2102d5440c04201020003414910034404486295040100e084490740c591500303403948243c00c402c01060758025080403400382800c100c0c0301d0426000c0029401c1c1401103c0d0002c50407248608200d58072081040c00000c0c0d5060314480140c006402005558810320500d840b240d00340c00080000a0014240d103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271544127 1250 271542877 271542907
    0x1503210509090f1e0c0a08060a0b040e0a0c18140f1c060b040b0d02010e0d14210708040e040204110c0a050f19030804031704030e040c0c03050d0f02 65
    0x3c07242041d41c4241c20410848189501c0b80c456a480900010318890520f9105541940203100c854810820f0b0000026010f80d200314503040109039007800a991076840700030801000c102150403940031400c4c500d20345043c500ca140364000000c0514080341c442c50801120012041468a10a5228040142c018243d55132103080040301e2110a408100c084a249452800d45140100d40d512641c5001400c1d2004d858110119401b682e0901c3e002444190b00c1d00091b4a007003010b0806011a90030b441411381042001518003404415080c200400042c154001c90543c820348100609400c800d0008011440302188041d0300680300034804100c852711494540984d4012a07258281c1d6805564441d040c4a01801a200f40300c811001401c0400b000d16280807404500a0005003003017980b400040506101c1c0940494144c0801408402800c050030010105c00d000d1404a1159283c4255aa01e10740504003186034654180c0b03440341000c0400028800400e072411500403a00e07001c10181d40d0f02480b007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271545377 1250 271544127 271544131
    0xf0903070204140420090c0a0507080a020106050108160e010e0402070506100f0e010b0403030e1206010605030a110a020705061b19110105070b0a091a0a090501150321050909 76
    0x2201400380349132a06251940036103003840c550440b0b04604000070541c0b2a40c61507940150308030035a5035074200380306044039140b01d01031010b40032207004601e420f40b40381e040d0001e07012100240e03540c203015140c000040903641d180c0811500843d910382c00107299035010311000a03408030010801401c2c15040e4880e103041c100103c6090349a58132040c41030190300140b0711401d000d0031042e54050341c1c07503040020009991160707000207030030b010a10313840d640940d45450078856032807001c0040c1e810729603468802400380c0c0c0003512a001402d0130046110000340420f0700b91034480f10150300411143e403504c0180310301c41d403000c2881e81d45001154208a9002030800541006004090303a040140c41d40b42451407108082c0900103042101c1000060080b070f5240c21040d40000f003c030700004008103945005034020700c0310103003440c00c44000e40401088501e50b511007610136000304028080c1139030440c041015040f5900009141d80119980d0203a83c1d17580403100407214082d41040b52900c000c51000684003241 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271546627 1250 271545377 271545401
    0x30807030306091a0306060d08041a09130203070c0f051c092112050c2a0f040c0f03020f1312060606020304030804030f0c09050a2009090f0903070204 66
    0x103030a0b0800030030a0701d210381050021110700c1c60b05446a0400020345174080900400d108aa000b29038500340481442210f00404501d014107100e030040b40440c6076584c000c00c020911074002c00100e0503c20450340200c81c400c0380b040e500d401d603500700d5039149088944400404d441900c1540404400d440404800c05104600e40e103c800d0b000d0302e0102040c0007a4003901c419101080c600386482d00151022100c918403407224108951159018050071303140120f00c0300300405258841c0c210381c41c000324281d014888c115040d0f60003600102481d00340f1041c1c4200340c020500040720740142e400618420741c080c080b100c900861191030151011858000c548042d0420101600e92540c2c0d9010007040c0d120300c03030050010340003543c2018030319182c1206600852102a14641400351904204078102c100031000d445c5101080081e4100702d00701200810b10460440050885501c2c004e00c4801110140e4881500003003440d00f41e03642c0c2c1c080582d0b0006000e06a095540310502c0032a0069817036004101160306 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271547877 1250 271546627 271546631
    0x30309050d0e1507050d080702010e0d0905180705031b090405040c06080907050a0302060a0c051005090d0905060a0c0215070506070905120c0609010203040e040c03020a050907120b0105040308070303 87
    0x81c41a00f049141c51110882500c100303c01c00043c030028001064140300c02c0068280396959581d8114140d0250017040c0485140f8011919100e100d6900709200a0940e08160340001c0d2040c0580c4103000310711401d8640402140091000540c0d109141403080880d03801c2c0590207003810491004981600d2013602c00301e0704801200424402141d22184850b44806040c00404043d4a01340c0400c21240150101900038040014076182113030080c10f07200c00c1d099120044034408144011208002d05040d03c4002190261500c044d048a220300c500303005a40000b07001c24540450184151f440300c640303580403a0091251082d18103901c43c098080d01d8564010381c0509258505400f00900e9120b031608050304c00e40900c0f8003074402000004040c080340000362407681d59100c208005171f00d580129440044031010040c100410004d80c10441c0040b24400d48001032000d44030000c00107010b10454040d40092a0241103410300303081e82c0c001009848040c1052032401d610b98540300580d03030205504ad00865 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271549127 1250 271547877 271547897
    0x80a0b010e0f01060912020402040b0307030609060f080c040b12070303050a0e0d03020c0918240703020313061808030f07090e060117340905010c080313030309050d 72
    0x49407030400c40341c0c4a14203280d00c00d5158101800070302445064054041c11540020b007013011900c450707040700c2c00340c000c45850750b460f4a06520000c5c00780882d40682c14002d400c015002031082c2c41141c00b10180c0f160840540304140c1e140041c030000388038035800780da0710608031481c031005203106010000c041c601a40d219031340c6850003100503000030070089840e8002c3c040300d240391000ca540410700150041c001c882120702611068044c003041d00054600b01300c02e01420ae44be407015000b5190305104854880304c0401255503004040c1c0490204071103650840a40d080054005140c0343d01280780403940500740c0306c105940e52106940e6400440300868606185001e0028043d0800b0b903440040842440064641c42c181000800050322070480c000d61804c0c03c00426800c801c00042c12485c2440720b01c07010468001c0814514401c00c00c3c0c5051408584d14150100b00c07540315580481e1502e4000120504d07513121150f40c1c844030b2813050810f408040d41e41e41da2000280051011801d201002d564000f014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271550377 1250 271549127 271549139
    0x1309030909050c09011e090312090501230406050c01020f2b0c051c0e0d0215100503070e0402010203090a03050304060207080a1a180114070905191509080a0b01 70
    0x1524058a6543c0100c1c040c000300c10700da81e0050b9420b0742000c803040c6403014154903039002c0e0782c2842190802440e0300c140194046549601c10488401c46009907500c640040c17120881c0401080384561a82c841081000b01f400b0302c0d8090300c02840300310301c8400014901700384201401504e400c100c0180c0c02040703001c102e0344024001c48000c032140c443e000c0820000c800b44960050b101d846910740c01c001982c0c40c480031401c407074039035403001020100e04010f444286001c9000291515a0004420f0124443d0408a520a0000c1daa030070103442c0041c0c01801c0b05414070f03160b41200e1600074030803411032200300701c42c0b44140c99555401000718401c2c0e0013107031280d04005020b400d0070700e940c021900039440301800310040788264140303c0022552808280d5580c0360540c0d0300304868290710f441d000320b60a00d10012008108206103a2184480303075101000b071615901001320403800d02e4100072001c400c4441c240303e410070030103020148a41e98181880301c2030751100c0742402c01751022000d84418003054010818 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271551627 1250 271550377 271550381
    0xe0a09030f0201020c0c041107060e010e070e070f120609090f120314060904031704050307060b0901030b152419052106010507061a01021203091b1309030909 69
    0x1407088640003d60078001c040c0700c0c0b20341d58100c07144070034451511240c605604640c0c00c0200d60f14990800400d02050b00c88000490183c1003181000300c25100700e403000a40c10501c2c0e940c40c2c0c0521580d950300c60300d000d4207540c111441c503540c8005802c0e05503515400140070605118180500388600481000700710305040604075407000010b11418075061010380600b442105c651aa0720074030403611031400d900c4504085403d1070100001c0c2078401003003014013007171143c000701030142188501c02c00d0203117102c2c64040c811020400c2c400280120074081c0804c07401401c620094260140c05070400d40c000c02c100c02d01c01c000c0d0380c4403440040d4000c40022040c00f40140c1001d100d050300b4207070400500e049220006064070402c0045c0a101c00356210010a515a10680c00c03101e0068214006001d02168126404100d031300d862091405072080000c254120071140c41900d115840010244c00040541d00c680002c0e1032f0010a4564803aa440030384100b00b004500c5402e000c280203540d02a0300d50f080c00e04001c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271552877 1250 271551627 271551647
    0x50c0406060e0a08192d03091521020c2113080c0a0515040e01090c1b031b02150406030203100623090f0a090209041a0312090a0e0a0903 60
    0x14550090074183c101e1706001450b140319176034015a0020341c40003545084035410070700f000c00c401c40d988121440041c540d029202c1c0342552110b042c01590a902640300380d58038200c6045243c3c60410420700c1403480304d61540036207804454482030b1800d0b01241c0001001d00c41800a401c280e120011a40855801120690b140a45421401400da02802000007555601c45e0712400f4841c0008034549254040900700b0b8600828903011007611a5854200c0f640140890110b081e0010380848541d6208040c060b1402d0640c50301610382c2180401c0c1d0301546a05950783e1101a0307080900c00402e400b400c000c0030001d10091806640042e2030f0b0030000e01480300391a0a82c020010000407141088080700d0181105141e210362807920355444a15030085031040d59402e0b6440c0e8130680c1d1080018a01083e40c000b0032080340210b404005148585110a1756554030041c0c8503051780c080030b800585051500018442e044005000d41d02ca2661005180f15040d400c450180d100d9031a001034108058002d140c01ca = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271554127 1250 271552877 271552889
    0xc0b06030c300f0304121505040602040302011403060d0605150603090c030d020f0601152c0301060b041404050a0e0f16061d01030507030f0903030203060f0a0b16050c0406060e0a 78
    0x441c4070014a050f550340c1c0114050412116015024181049100d21401c0100303040707160240a2451b09080c88802500b003440181c2c003180d004403c1c00401503040d4126413140700d00401c1d014966a03642c403a00c008050080c0b8030140c01d55134101003202c070b40c3d850001d9441940c44400800c8010440030615040009040317034035041d035200275980e5001c10004611541980e1400c07044414060030754000712901d002d110ba051a081045c1e6111000c0400e0b91f442c07404a81034250000d1004541d600030120180c4034038810b0003c100b0b80704040d10034500d03003030304441d812502c00c40c1e01145111403200000d05207181d094070f0111641c4030391070403940100e900c0400c100812050038410f42c6000400d1405a0b035200c0d4031981030415603240b00040300d040c02544100d03c50030811000f04610601840c01800950050b0340e4188280c0740f500c0c6001551030301090036010707200b0810307a6900300710100791400d2020004000c1194640255a11041c158440b48182e900034480c0c2e50311405541050002d20098075000d8200f0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271555377 1250 271554127 271554133
    0x30a0c0203071e03090e040f060b03070b0d021608030c030907060302090a0603050712060f06030b1c0b2a0a0809060103020109060c020a030c060f120c0c0b06030c30 72
    0x42c0081418910030105450a692030740c0f07051481490101c80d01d0303001341c00031401c0404d00010300c002d0001c06150940e007117214403000c00180002108040c3d03102d0182c4550308142e1750811101107607100c1a00034203000d00508059404071205070b501c06000b5001156800d4a6910100400c030360f0150402800004082d54201146002e0380074000c10302c00c8020b4001c2c101410380b07a0000c17030744041c855450311100d071070040c900704012a1625000e15841900e48590000242414210703d600e10b003070400c89220310b0001c00c40101207055982e4580800d440144841c0c10359603083c03244040140300141901c1c0010b841c1e1006541c90803018009004603001900000455100da00107100607608841601e040d50500e08107000d94120600c00941d0071001034100a22a04d0880c4002800540029180440091584900e0082445480f4010449090007520340008a101c18003401040c1480c0780d042e04a60050140d0307030a07400c1400800c410701404050000703440c1800e44070b840301800320444540c03005815405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271556627 1250 271555377 271555387
    0x9090603030e04021810020c030c120a06050c07061104030209130b04081623070803070506013507050a0801060521030702120c13060501020a060e010f0f02030a0c0203 73
    0x20040940c2c404a003014003956000a1114000050070101014201c00815120a084482d0310083d00c40d0400c41c40d541c0240300d0702c162880c3c00c0c5001000720105420301801811041032a03241c1030050704010f08120011403003003102c01d0110f11240507440440704d03940c0d0000d680b6851403040c802000001841040d00b03a070000c1e030190001d0140103201d0340241e0803d44480c3c0340c0c0e114007404103400001c1c0c4001050392407280320101840700045d56070100c0c008807200b81d0b90060340c0c1c1c50841d512071103018030040c19a04000c0c0140890720714001d03031a071004000e5600c1800c1003609058404082e0001301c0540c1143d100359805c200e1460714600001c003401d6450002d01145281c000403032100403038a03100841002c14111a810038850401c02e030303140a50002e2103e8039a1242403191030b1034a4100e102d09000368081d82c0e010310819068000c071001c98078107900410b4071103201d40383e40e40107000f0300c0c09044140d503d451000c48010014085e8501207d607800d0013707961304100140c0011078410000200c20340d041401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271557877 1250 271556627 271556633
    0xb0105100c02040b040204120b1806040206040e070c0b01080c041a0604090b0402120f0906070201020310050616120509031005040323040e0109020c0d0801050f12010e0601031209090603 81
    0x4400480c1c01da058a01144189040d00000c0181c021504000310020302c06a034a03003480840c480c01809181000d0600f40c8080108128035160081103a020750007050801003040840c480c2d076002a800750181c900600240c10300e544130f0003400c01c01e0340103e003290300031159141513281c24030a24420701010141c0c400700e00d00702c030042500703801948900c08600d40d46e140b2404840c0c4881e01120300b541100c0203901d80f20b1400c80b010042070001078440000070301c180c10001e12028014401c89000c1c0c107081c0c0010302d00034075001c10044960f200e9254406005980c1c3e02d688000754040e00004904101c540f1380319150f81400d000d2526000880000e91105810801480042074015a42555100f141c0d42c40d00ca5080b62040f09450601c12a40301e218400e6a0303200000d400c0303410f54081d180e20354205050703804042d0012000c0350442d00a004040e400140401146001e20b04040613404808140002251a0b01e0a03c010f0741006d0f0240c0c029036481c41c4024500c0e401c1940300d010720001c0c0c54168400c102c1981161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271559127 1250 271557877 271557887
    0x11010e030d030b0109030f03020f0d0302070512032221020a0b010b1b1228020601170106080105010e0603010c021c050f04030203102705060402100e090a090b010510 72
    0x91000c81c181651901a41290b91140600ea03001c1e581004001c4215021443c00941e1403645903000403071405070203e80e101e0144603000f114a8142c00134014840119802da0504181d4000b030001c5502204112a00c0c4050b0400c07600303064000e0141c18206501b6810994071060403d0f000c04240454010360b40410014030303580a460305484a00c1d94042d01d4007402e0359000030400c0b1140c8400d00700d208101000590300e02103401040c08000d1688203040d850004010801140c821508440250300110014001c402e00440710400281e004800410803981d01e4146500315182a084407082a00c0e010030040241030900444035180e40720b10060545065407860204526141d200c040200840020322201d00100e06094a000d144c00809440d030408402554000400390401610355020403000c1c00c401e03030f840c200c005448141d001030145c021907803940e0070848410f0b2122101c40520008000900f155112600014483c1c08401c000264155050400e5000810142d2040c0e11038480c551850190907401 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271560377 1250 271559127 271559143
    0x6060d0b010e07170108010e011b050702090c090409032601030f03050306031c110d020309030a1b0905090f0105150607030807030f110703090509150d030c02060a0c11010e03 76
    0x2000e80708182c0e8880c00d00850352083c01950100c3c005444d14008a1844c4040d880041810200c46c020040d803403003034001400c1400a0303d40f100c040b82040c04503601600300041c815901c8401d40001626020403d000602201d014480175000110304135100b03113400d03981550b2607544d03808588070000c043d85907070360740e03418641c1e00e82d801000c001001c03002c40c48946040180300c400302080034a10030a4074464400400300b0b180507001410350b100760103140c0b80440c004000c075844401c01501034220520350340c440c1c880d4120400221480001007410000d0990722900c18a0f001304007031405000d5803e03003024140e003511005010190084a02080750ba42991000b04480c0042d52500301000150b64080c1d0590050510421000e142c904144d800348540d0104401810014800d45135030009075118014803488803412210040c11407080b40002246240484102800d54800d18001d50b038020240e000c1103203900428652004654540d41c41001c0084001800c0690704080c039000f1203400d040f0002958a40340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271561627 1250 271560377 271560389
    0x8030105010516080d090b240d050a020d0f26030402010804020103020c0706090510030e030a030b150d1508010209030c0f0102010e151b0403030534050a030206060d0b01 74
    0x10f8000041406820000e41094000b50f06540313941c85000b1042c0540105001144c02001950000d886810010003045d00c66016806094119500c034040c46101c12003d001074403207106807000b2800603500d18506a40c400d07c00d4a0840202e0b4040c5443c001420119200c05103100d501c03100c5440c202e04d01420b50340d2085c1c0900c0e14840580707880c00142c00038440d0031850540d40c024228045a03183e0019039079400c5900542d080840d81300440c5044041304c080d0520007409410401110036801e00c00d4101e450304610080c0501a200003d4068a800ba40600c1580000640b15007102d0440d400341c1001d00018442c4800940c40c003450507002a486001015059211b0b5800300b400e0112a4400d5015500209000d0204c8054250942e40c0034211001241c00000712162601c02200c0c4002c80001d40d8200e03070349a15214240b424001104440b05103990115000c04014401516828080400300036030718021f20180010384110700b4000d0070704000820a6005503008269180040d11803100c044c1103401c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271562877 1250 271561627 271561637
    0x60a08120d020f12040b060a08120901031d0607030606030b0120010b0406120b011217030c0f07081b010c0e2101020c030d0e1c21020d0b0a120803010501 67
    0x1045603401402070250581c290f04000300451020b018245110210b03000c0c601030007040e80141c0d592002c000c0c608816002d200328a4000030a0246503c0c280b10250442d09030506000c0350400d413441e030b840783c0840a1004240302c0c1c0e11090a001c0750641520880014011070700e0f0602c4031821000010b4069400751500c140c224000d0b42010150f07020a6110440d1103100400500c402c964810080010101e00d04082e07842203604000050030381c40150300320444552281d0542c03009084401c4170a0903410041c942c2d85428000c01c460b108041d1050020811244140c0040751a8420040b98107000d0b0008402a0a82da2419641c2c03501d6a40081075a0b81d00e00d001c80e0b000702c1141b050502c44070000c50780c00c0024410f40c0003203518400c2030000700c00b078030010fa03000804001030204940d0055442c8401c15010144607540070300764000e5480741c01d00c0c41c00d1050380d80c9407200030744840400070120313440f1051389100d035030340c94044241c5031410300c0520f0001c0402080107140c842c3d0a4441e520144018450241404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271564127 1250 271562877 271562887
    0x101724060a0509070c0309241409040908030a0509070f140114040608160804031e021501030308071107050307140310021602010f050a0c02040c0909050a060e060a0812 73
    0x1075100361018020341805004454181042c00002e8420f6034080030840209012400c0031841c3d03040d90341d03a5011342c40c3c45d2180c00072668080074251840c82e114000c42c14550400c000a500a40f5540652080588102d40c0c1580d00d2409000c0301c002c03a1800b80c52202541c00c010300401c80c00b0020000e00301562200c43c5c654117158020b00050380c4101c448040404901380100e400500c0070307005914203110390780c0340c1c6c0d00000f041c050880c04c5440319821140200840d00c81010005045008202600c0e00080b500450f907503200c0780d40824403444000d034812000109010b0800901982c8000c82041c0280694020040c15040c000001d80b05c5010b4041d080c51036248440e41940c036a000c11800c901000c2c601c00c115602e00800f21000401070360b00100b03038085544481c20310019803080040301d2188400e40e8071141807901a500b004080c00e02040d517401000000340b0701044a0380c05100d8207004140690340050410702d00b5580d400f16180041c40e1500c07a61b20307460100035464000c10004040070030003005030350350 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271565377 1250 271564127 271564129
    0x6040b010807080a0627060b120106050d0902030f0a030210060608131109040303020d06050603010e0a09032001020403060b0909030406050d022b11031006141210172406 74
    0x3040d03d6403083c540300211404c500c24060210541c40800d40048009101017610740308d038030b141c51151400c51105000382000401c2910300c01c1025203014088a80301094101480d0002407500c0800701a10b80c15412a5070200209501000060f0200e100c82400340521441c024006e01040d60040104c4045046c17001c2400030003080080d110110840141a0945401d150a00074003c1d00940001c01c50b6a24280c07000c640780c030f0100c055a0482d175116605044550320702d900c12010b080328040850502c0854041d8555030502410486043c110920005840307500d581422003d41d5001c0300c2180c01218110240442000040102c5003528040d0030040e03503e160990340e840c02440740c0808a0726000301d2500c40b51342004000e0207140614003140f01840000060300070700219100035a044110484040410003185000d4086603402c7c4d1a000b003c181060301d080306402140d24100c50940d5404d2a4803400d004503a035542100000780f071500000c19519103920308020b1640e90095a0900c0810301500007085 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271566627 1250 271565377 271565381
    0xa0605060d0b191716050904030c0c030b011d0f070c0b180d030c03150506090d0213090f05060a090201051204020f100306050411090a0b070c03061407030506040b010807080a 76
    0x2210000701074400f00580ea885903003100c0c0301004514000d6006800d040c10030400e250300c000c1c1c240c0c1c0f0f00612090054940782e5090740c800d041ca9100312039240c050b120010200f000115010300030a001d40d40d81040e5101c007004040f2008004152105010080c01440080c590050400c4030050740403517140165102c050380d125080c1106252440644030340c00c9c42000c1103916410200180c1c090b070f107052000d140415407480c200352190003902c0d000b02c0c06215101c098540a250244458000740c4440c95141002404000760b610005066036074110340d1030706504102c02001820352012041030b080001e44e03000e42c0001c28038450821803a80080c2a100403605568800c030200e03c041200070b021005a0746840300180c064002031194501ca58a000c89591042200e9000c031080c440c00204a40825420041c0e860b40c950005a000c3d280c00100e208003100151403441008104141c4a42c4000589050507004007520f00c0140390354022410120001c41eaa604404400d810100300d08040865a0302e50310b0900c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271567877 1250 271566627 271566649
    0x3090c120a0606030614060108040213050711060405010b010e01210906140717010f260307080d0504020a05120a030c050c031006030218010b03010b0337050a0605060d0b 74
    0x700d0b8510b40a4000200b0070564419502c290191100b0180c0c6c2e41c0d407030015900c441c421078003e9001204202804600582d540c4900d80c80112410115240b502c0011400d18007001182c003103405a6541904c52425a0032450704c080c60402460696890f5081d8030f00038141202c132801c40c2144a4603489a0410840e0b10703004a41081c48ea40410344851500c0580104812001c4a450a015040750f0000c14038010b4208003200f520b41801c03c190380c400030100c0440e820000c03020307a02080d020511210b400201044000d00004100340e1000c145400d041c010040300056551103a8420b07400241b1a110441c000f1030240304403a058102200c168060b820002d0400c42071a94a0f45c0c180103d014442001c400d50b0f011100340ca00039030710300c1d058840300d0460810700d420a0040c207540300e506000420440f9042002103911256040c0b07041215841004078010850140e5101e2545140208820a503401c00f440703540d07400922100107102d0240b134034020881610800030f14004554a424140d0125102c00c00050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271569127 1250 271567877 271567883
    0x51603030b060708120105030c030309061303020306010305070e0105010509100309020120030a03060b03100512070312051b0a020a0603020904021c1b020c09070e04140709081203090c120a 82
    0x40d58802c0c42e0300c2d041000317a000040c1502e149000d9000840c0038140082c012110203400780044d0710300900001005801d030000c058040400700c685501000607203007030100c0380c000c1d80305000a281247c10000b1407401100c0c16003100f410400184220320031940ca002c19145001da09080003d60702a0a000481d07203e102500800c003200700c81d0f00340c203d41d0bc00c004014489108191780401c80180c0701c040504661000f40d481e0764444040317080c03e00031407900d5000c401a07802000c0071904007030354a5499100d191802c00030364002c12000721702c401106644c0210002da803080030380074041c1d06503290700252488155010f102c0802d0b038040749014150321650b040741d1906030300002000e0741c4882c0c0210b120203080c0035405001500f030940c900031819400061039815141e00100003e0b2140d8607003900311034000903981c0103a48103480300e006140d4a00d00182c00e90090005aa84183c024103082d1918606202201d81c0707500391000f0820410042400b181540c9072900880d411a0300104c048551482c11090000103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271570377 1250 271569127 271569139
    0x1120f0603030f0306050307030c0b0921010501030b060306040507140303040902070b160c05060a0f020d0e010c1b030207120501060e0901050f0109021c09080c1504021906051603030b 80
    0x4002d240c0c1005008200c08000d960500c4600d8a500c01d0584500d024400101140f4085809010489a42d2b000e032008890242100d40c0d503d8030030750f8135103058486030521100d596440f001401480030f82070496500007020390084c1076605051366840d55509145c4100c110301d81d00040c203950240c0c0c051045500404a00e1010364a40368030707041141500e00e0544912924031402821000d03164000c080c070351516500100680115a00c11020030040c003002d81e6000b000c9071b400c0152010b055403a114914920990307400000710201da145000d804403020610100e41e804400240350000b0394002562019070701c50490342d0f6010380702481d0041c05802d958002500c2d040d40300c410000306801c154011445486072108030511a41e80d44030b941c0491007511003400705180042d1300c0164a50043e040103a84610440c481450b0801c010301403420f110f801035500e41360311013401c144020351600a11401800301c0803400b51036130514188001c0c000f07100d40030001c140b4082e6052544185130082e40105e914484c090300b2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271571627 1250 271570377 271570379
    0x180f0602011b0c050d050304060204050619020d02030c0304090e0c0607080a0f0e010e0f0114030c07110402040f150504030503041202130507090902070c080708030309060f1501120f06 80
    0x1038003a00400b000400d21407000c1c1c030390070b081c6803107000d194401e182c1220142201040d041c02c1158190710041c0700f652919002c00000071300b80c0b5100000c2100528508001c41c80e603918a07030081c2031194074980541154010f1056440e5250b0200486e0708480321024005400c0001d002400d08000d071100f1442da0003c40880c840d030921210328020614400565650826402d0062054581c3c0044451860000d500080192001d0805082c03201044405042021464100c000c0c42c840aa004440c0600240300102e928803c2145044050900754001c1b2810b504040c20500c1c040040c0400c0e106610003021b03600c0c20326010170700070b400b04d0b8091904a8196a83c4a4481c0e14142e1700494012040b03008000800e01c0710f007581c1e8144560b6000c0c034108e60300c0003072041c40c207922400650403403032041e030302d0415010b000220170100300b041000801031007001d1910b13481d00d00803250600c10014400d0700e1f40b4001100700010b5804000c441a414942420081000a507220f29000203042d480071a030f00440c60004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271572877 1250 271571627 271571639
    0xc02030406140a0f0815040903050a0e04060510080c070f1a01050d0b0601120b04020c0615100c1227030605010b12190b090a020903010b09010b0703180f 67
    0x401441558030540764070300c4103900e2000c1200355224030b0590400044c210404104d10502c00c604040d081400c0c0e603424a082c1c0b074020002000c443c14142c045000c14030000f040c9030001c0d00000d10418031182100c04103e0b4030f00d00000b0903081c0a00d800c00c0310420820400165289510400392000c0c0c0c1e81000e00c6213804441894100b40840e42c1080484171101e42000008040c50100e060310170147e8803029036007442d00d404c3c0056403401140100c01250301e0321083c1c0f06000e502c86101400c1c54079058001410ba6050030401080c5160302e003410703903000703070031100420305aa9004180b0220145c4e200070041d0481001e0041201c0807400504e108142c2d00040d06480c440000821485003961300804040280c4d90380c8041e8074105d40328600d0203001c20b10a03140000d0441461107490501c0842094004c10828030389800207618120845410301041d83c0810120207904003445855410842503500c0d82c0d00d54103002c6041c41ca4061880020b04002051282a00b090000c40c2d0366401407800c00c9510000c01d440d12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271574127 1250 271572877 271572883
    0x7020d17070216121a06031b03031b0102030a060603180b07030f06060807110f150a06030c0b0c0c010512060f0f03010507030b03010e0a0b04020904031b06090203150f22060c02 77
    0x2070580d11120b04040e0070345608000d17032a86004200c0140181103c0032500380c0d5001c04003140883d254540070500110000030b0041a0036607003150b80d00f0005030707a42b40603840d0300c2c100c0c0d41a80020b0100340c54080800d240020940e02c403c031268110882c2c915581e41c010084000d00050301c1401d842604000f40000c00903000201c00b400b035103898655080022000880a42e100d8140880d1039244e48a801500604480c038000740e508010506000b0501c19160388a001041240e58441e1545c03210000f08ca844c0c1c19800d00201c40d04c004c003417030410f113400c03c03016021005e00c2021f04075600c41c03001c120080e03800c4c0e0b4445050064203000036000b40164900b500000e0002c02020410758069401c100401507290f4000c44d104c688164400c80c120b0f00c60b101d68091060120000b0000c5080c0b15150703019250400d400100c056895116520104036000726206160070802469006141880c2440a103e0a0700d80021029031202c0800703040014a5003200400032103d007049805007070030f4a01800c00158640c08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271575377 1250 271574127 271574159
    0x130e0f0a0f20220507080907060c061104080a031101050f07050c0c03010c1215081009020102030c011a04060605131a13030b0f0105240d060b0d0e010507020d17070216 73
    0x80c5100f000545da90741c0c0705131402c020480300101e60ba0490308041c03041b0f900a050380607000e03000701c2c40022501c80c3d4182015499006400c814000d502c500c0c0c920080503408092095845642e4000380401c3c10500707140141030002401810034082d01044c3c00314914010082945120304c0100280501400031038041d2075450b4204048811f6801d01c25072400441101c0b4804c0d0443da00140281040c400100f5003000074104c0748030072811800208410380010000340076042d210340318480e02c060807040359410403003101d4032075108109100003444001d24a6404580180845803554031a851100e400d52800c0b0107445080e144502c0c10b00741100200501030108000740c491080c480c0e0b0103205988a00401c008480c400030100f482c118544880b50310410030f2001350030343c0c0c0742101e000701d08603858501c03540440c0c001000c40c1c0c2c01e044d944c2040760b03400300c1c090243c9508540940050140c440c907402005108800704003a00401001081c045540b9600c00c000b4602c45061403d180b454458a4140a1141900d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271576627 1250 271575377 271575439
    0x60315010305060301060b070b0a060e041514041a0c0c0d090302040f050405060a0b04090609061506140f0c0c102c0a05041a130e0f0a0f20 61
    0xb034500010002d0038144100750984101201c420308004843d82c50580b00c01005000d40c2c411303604c03050006840304003510305d68001c51043c05100b2814a0303803800d21044401d0741c40c046010032600350903c00030071001d030310411819441c8482e001c01d07980c41c01140c1d0003a2054041d15103461140310070594400d03901c40c5204007070324401c0fa0b051284c420215024403e8407400d40e0090070a80007240070801c0c1d070845a024560008001d0008249090191034580031214180c40584603142c8a0700700d48207003030701703259100085c00300c85c2850007106400782c036008468021501e1024401c4d20029154445940803c2901201e550040c00c0b01a072180c40080203000311269210f143c201034001ca228500300316500c000700301c0c96001a00a071a610302e003108200203070222004410b4280c00c81e9611000c19107420101e02c00381c60f1000f8012900c184d4a203040d038a080c68140a03e10642c00a54a480c0012900710030fa804c000e4000f110480112000350200f00014805c00742103502c40c0403c5c00212454110126030106560 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271577877 1250 271576627 271576631
    0x180603090209060612071b021003091a090303070c02040204050a0308070506091f18050114150f090f1b07031805010f02100e070b03010306020409060816060f0c020603150103 76
    0x111902031103c9030240d58410310300821508002046d4038031502c0d00c10f4100060744c0d809446005e031a00031030f0225141c0c036000400a81c9409003801884030200101c5d0b030001c005141c007151843c00410564813804050812001c010120500030305559958042e180680b0300101240c143c0c590300e203002c4070306a00144044880340940d40005410b5200401c034007004080803403c041880219540070402070840060311301070341c4101c0a466010a409124100345854003c02c0842c585c00c4c4580003108031804421241d11418148046400036151408900c0d044410495a86055100c03d4139202c005024030f400c004030450041111024158450513003030400300701c00c0383c0c1a129030b101d80c01111242d000101101c0940d020031080c0320b40b020302d035000144103c88003007078641117501d904212506500a0340180d50040d0045814030038000700d4030800b40200752034402041e04d91f1400700c4040c40c00c14113102c0c240078050017440061072203024680d0364219960007007040d40d59241ca54019050111406c2041e40064 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271579127 1250 271577877 271577881
    0x3030b030303090705010c0303140703090c050411220e0f0f06090601020303041401020d1a0f0907170a020f070b1501110a081803070810150b040b0703180603090209 72
    0x400c0201c1241d0003044401d0280c042c01e03040c10019112100642d10490405503621401d181c100304c06281c1c0c138000d890710b503004101210f1a0900c6103030094a604641e114526044000c4040c07408002200d02010a265500e080990810b01c11f00a5000c958000c0c45038298020400000c41404140a403180031070040b10000c5807150010300c00c0c6010b0032250f150160b401003003c01e0100b0b0703800701100c540d00b0350280050f240c02c400145100c25034101c01d2224680c0d1f0b02d5150015a503191803d8020154041955101041d11301004010058904001e891060f03e01140c0464200091601160b4100c081e00c0030640d41c40900e4900300c0000f1004540d00c042c2154811072800596108000b031031004c81101006000c01c00c5c1c240c07549521070303004800d200441410448039141c4c540f001e01458000b0880a005882400c001100d80c10989103a41c440340c000300001d001c14894100020f0503070302590340c0c820b103080d240d908038a001d0b070304d002c0d127403080812000c80c600000844a50681000b80d24034801e0355a1401740d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271580377 1250 271579127 271579129
    0x3080318070b040b030910110d06081216060f020403031d0a0b25050a0503130f03050d050c01020d06081c0c050a060e1c0314090c010804120e130903030b 67
    0x75240324000c522021400300010010398a110004e075800400c611b00740c03840208040018400c5901e08440c034040c0324400305003000068002c0c4a000010580e60000c0d10b1800b241c8051808240700e01d0103140300360445641c001086c404117a2086581c001001800c541d00d130303200e0801805940b00008443e019007040080c4880710b0502c0740340801220740d480da9090600c0c600344a90265120a2506c2e1407682d0740120300b40d00450020000340210501403005550b9407218481d602e40d103142c20780c01440c965203500710100f00080001452600260b110320b051500c80c45800216406482140310301e40c0030758102400800e11810101d0b00c48110012100745600d0040d0105c02036494600c103c00c0a0310365081400008080340c6c2580146003820000e03030540f100c20ba50080e0b140140c46d0111850000241d88840350300983d62114042d94125035140d004084036010080000c0c04a500100000c0451010048600c000c5024041021884000402101c1c1c50562400c00034003c1400b14030603400213040c4959200304e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271581627 1250 271580377 271580383
    0x180207030906080604090204060e100f080606010503070915020114070c0206180301090b1006020c1c15060b0d02190c020604170a02090103052104060e0411120103080318 74
    0x903625803a480803252400784152802c3d54024501600103882c1d116030001070782d90b840f40c40050024404560b40d00e0400a42d0070ba842c40c110f800c00d6a5582e81c0c40400d000c002000951603a1048092801e1540c0b9a50f11008803010400c640c00392980c03020003030400d6140c035010340000401080c540c40c042d03c0307a60b0311101155007204950713029420034800c00c01d00d110917040540314000c1c6400a070010402410701d545030f01d1400c004031090300300c8030001c441c140041e076414890803a556000711200c21a820300b5100e10b039107249901400500450b6103040040c40c82c801c40d00f0403401000341c1e6511a07210780c0d02d004040003a5020006400383c2411400c45998014029400b803615160007505107070509080c442c880001428910100010744038032400280140d5a84000078007a52164001d40820440000341803004020710385403800b040380c103000c00d00030070798003c203e0b01400c44112804a0b0750105809080014440c2e21409007800800074008024494444010b6002e84d05650034540303410140102a91 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271582733 1106 271581627 271581637
    0xf05030705030327071d0a09140d0207050405071e300c0c0519020d0c0b0c0f01060303090506180405010f0510080906070c08070b010602071802 63
    0x460a00c000c60306072076606051340107000086c200700058000100004a81022008800005100c1203041e004030301d01a81000c64180c001d020210015128401001c4910244c031800c000003406082038031841d8407074461980c902481489a00c001e460020200c000d02080041c0c220b4289400d201000d010400700549204510510b800100300805039182d006144c42441820000b84020440c003265413503041da4075011850020501e40f000030341c244c9418002500e40c0b81211000300720004118011b00c2d6944030788045030a02c2251850080c203a4405002c01000501150003c00450034140c004e8194600500c164200c00c112110108040b140241c0c00040b0304462088100043d050024129110346010b290100407483c01d04050380d91000041c0800302042107060040381800b54040075500d00da03900100801055940f13001c025a00e060724003a121105407010645804a0101d200b1a6 = true := by decide +kernel

theorem cover : BRFrame.Cov 271402877 271582733 := by
  have h0 := BRFrame.cov_init 271402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271402877 ≤ n) (h2 : n < 271582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
