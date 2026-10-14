-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:27:02.850315+00:00
-- url     : https://prove2.me/submissions/311b2443-433a-4762-a101-7932e9a1e386

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 240287769 ≤ n < 240467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 240289019 1250 240287769 240287777
    0x12031409120f0c041104150f050c160504050601030b01023316200d030c03141006020c03060610032003040803010e13150507030902040513060b180c0a 66
    0x140010000d010701940502d01001006401a07032031010900c400d17140307800d10b01c21130b04808000c10071801410a080c16944c02c01c5150004210741001c400300e130035004401c02c070155405040341c1d0700015011801d165044030400c1d00c051100c0d0341c4040054049801c0c401480e0b0150b000410842c590850381072100c5042c0c0d10f03a24500b035101540c91404050384008803a0218034910540e840d21544c0d4000713010010301c1c2d10f0001c6110ba1480d8040d405030301c492a01d902501070540781d0090048550180d0805004240d4051120501b07240404000d52901014495500980503d0204152505021034124031a04000d070184680c0ca090b075004400500b104000020465204d25095404818240c0114007860180b0049901d95042c0342c80c44c8074580c00500b24562401c6401c0302040041c1945d58030300021401004009459514414190040d010740c0d00c0081d071003454402044041c05403c846801a18042c2c04200507421503442072000911640d203204107600e00c014001070010804000a0800c00490705d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 240290269 1250 240289019 240289039
    0xa051f1115090c03150403090509100504020c1507020d0e0f120a030206010e01050904030c0605070516030302030103050c040501080703320105090d050a1b0224120112031409 76
    0x35591112071058508100039001507a0f00d1000b85003c00c100e200d41402c40c40301918070300745a540505448a244149409000d0220001744585c41c0c003840c013401000043c00940d610030903903901c1900c41101085650b007a40c41038002c528007910018454804404a03101c0d0030303a05040008000f40c0080c02200790341d00c041c00e00c0403403030401c1050000491646c402d80081200354140038184915400c142c00131402508210200030100340e03c40d00003ea401d0f040040010207840d6400220380c1481150644080302140c00e023a1020954554000c0d4104c1380258240d4000c000e1500400c0182c0b8030038490001c003a0300162090010900c0b00704040c10060314110100485280c801010168184c00b41c0c116146035524400c200c4c841c10140040c580380d02c540c0c0b8045103003140111002d0708407108060078584a41c603541184086483d00e00c079080c070f002041d925080b05480450b000500590114040c540001e5081c8000240e9505d40114848041c0e4191246041d0000d060501c102c02d03080714084d6540310600c0d00f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 240291519 1250 240290269 240290293
    0xc0a0501020f070b091218030c031f0b0d121b0b011517040804060c0809060d02190c020901050114070b090c040e240402060d0c030504020a051f11 64
    0x440100494035541840b5a2030b0101820f280303510b00001410f9081c0c54000700300d05040c0003504000c903110560381508840300040000301107894190b00960a0b50140b0428098515103031594889880741e10158006005403401c100a006080d81391003030082202c0421961044102d028031506d880c90600314940750310b403040340c0e02e40300c00c034040a81c002988800032003201030300c81c0d50200c0c0040c010790300903040400702d00703080e503a48050303200e180302d424108070040c4006001c04c000e000403600948001803296480f108402d00303180c02580031a00000c0342c40b07189500c2d00a401e0140c2482c03e20650020085d00160707281030015280881310200f60811080e080101c44002a0140c040d540507000080050101298174018041100d0381a07126507541d502003090034030405401e5000802e07101801c0081c4a66444e544003003401c80c02280b440403041414250b00707071562541680000d20560086541840c1d140d40d603c2404080d000090b02c2003428494a980d9005540c001c009003091b12941c1c1c02154070700d90380c503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 240292769 1250 240291519 240291521
    0x120c1c05280605070206040b010e0601050c150601090f06021c0e0d0302060403120b030a080706151d130302030a0e06040f09061a0408031204020d020405090d030f060f0b0c0a0501 78
    0x1070484865044410600d0003440201d114040d40081c2c00d0005201c6804d203a10b5003004100c0520440705020b81e0742002443c1d07a4803079401e890301e52150070210b401c1801001c0d90a800001c045415500041504030000385114244421400b01c2c1d403142c003c3c012000035444440180c60380d02940390140f040f50610724245031030301022010178030700903400f0b4282420700745130050105075400c520b50003c034207200c41081d45075008100c08810960151405d40da81c9007070300d0504083d1440c0300651030104580c0000082e00350303207084012491400700e01c8104065a4000d01c501e0007a040344d00c0500140e109105080c01e0354003036408071a150400074442803d1030b03620260280d10490540095032066203c60007044007206040c0480201c012448041e41450705140c00345643c5e000d80809a0102d444110224003035440da0303005095056000340061101e4900320354001e40e611403c21400300080d1400c941507070b0403d5540315907015900c0030400b1110440c83c0256030070090b00200a15807060041a500800080003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 240294019 1250 240292769 240292813
    0x6013014010c02010f05160e0a091401060201381305070509040b030102090907120e01050403050703020c0406030c120201020102040b0301081c05040b040308071401060602010b120c1c05 81
    0x200c03500101d075401c1464402070a42d170b045c058406850b420700d01032103180d142d140705610b0030351260715000607200d00040000320064450740c8003051451a12021015240981c5101d038180c80031a0006d01c20323260f580c140b15840703595841c040081510750129124010035410707e0400c100380003d15a01c1031078041d0381c000d821503005844410201e2000610410710341411b0103145165101100218100b00c540404281c2a100003003840302044000c80e103c1041403001e0340030b5116480380000800040c5030620b80502580d100710b10a4025110f68140380c03e0600e454015101941e40c440041c038501c07440c4c0b50241240c81b91815040707042d55000e000c04120786400b0f0010b14000c00c0000000d02210484c85070101c0c1500c0301c0e5207800100001004244480749103013084400b100e034005986075807078110382441c12840c6240841c4101550800a002a4181d03054000b00e403000801c031890441c0c02140102d0303a540e180c1100460350000642c1c00402c0d0f030b5070307802c42d800701e8410701030030a03203481c500c00000381011600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 240295269 1250 240294019 240294053
    0x20a030f0204290411030c0315010c060608010b010801090b0d060507020c090411091312140c0d032406020c040b010324030309171e0f0714030f060130 66
    0xf4010220b2440ca29060052018242440b80014954208500703200164440108410028403d07901c2e50f4005921401c81e21f417256400c603c0802c80c05c0e440d005110b018111890f800c50002d01c0513000400e8a0700140300e54201204001d201603160b68207552194087d20004103108194001e40c4400c4603d0780307406520078442c40c4640303461411160380000300404040c001c1c12440f06284000300300f4002444a400c0070800f503a250501c54a90303890320380d01a41d14401d40c14481c403a4003402c8200e0980700d40507000404802c051002001003015113606100b0045ca15225110050348400390201460030b1a83c000c80103090189404110700012904107500c4282204030b9400b0109107010070020714ad0b00c0002c58000e044c101c00001800d0920001c81581c40007500c4c841c070b028000c40b400414056908101c100004c846540a9070b03041a601d4460400c01c400604440380030307018074400c442095001140070380c169401174000c410600c0745001183c1c02400c0403002e000e1103a9803202c5500121342c2c48548104002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 240296519 1250 240295269 240295331
    0x905040e070810090b011e0b04030b06030706030b0609091e01030503190e2110060f061b170c16030b04030f080601050318070f0815090a020a030f0204 66
    0x14038114400e40b6140981c8250f4240300d20704588900020801c01c40c00381110080104200200400389030300c10450440d0384080203440000500104001184514038401c3e8000c40650b02c2c1c0a94a00c01034003602c02d1450443d070f1041c0300304000fa0032481c00054064101041c40c2520021140384250304080d50401c0c1c100307031545e80c004a910200041920481d42c01d00e1031310300e86403500840040100b651021640701c6074212a400c10045402d40c84100300650507000e403200c0c24020f0a588814070f68101d0250f004200000301c250035401298120f03102201343c51540815500000c00e2082d010070003980110b040035005001d100c030408407180d01c503100c0102440c09030101e54114106450003070503074126a02c548051081020030000c040e80c000d400d8a81c054603076a15550783d125121401403c020840c3c01c4000710104c02c10300402c00a000150b03544440d2002c1011500b5621a03011055982e07404202c0250300402c0070794280001806810480c02d210700c0a040400c5405511034042400c1c031620000c10841 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 240297769 1250 240296519 240296533
    0xb0411030429010b0903031306030b01020d030212010b1b0615090f040209040213060e090f0105010b0f0301050609060403081b0c040608060a0b010c0b0a06150e010c0f030905040e 78
    0x10003204504004840b400707054001034003a0380c0e190041d098105200703a201c6800081680107541c1c401f0b100300e81c0c0112041c00462002a210301e0041c00805500300c1281c01449000c2d040031902e0300a101304d804042520b80074602c540c0c0b800c0241ca10130b52003212180c3d4000e01c0701c1007034024154108890f60081298840d4500340070317410828000807100040c00844050f210302e0512016071126003086030015015500000743c108607103030b4500606003603400010100240c10406c8010360300401d0f5901220440e1000b8803450343d80d04c060201c0c41c0103511180c82d10f030304100010480c602e4a4001131007040d00c060843e03810140d03241c4801d2070075085215140c400080d4040150141c43c820b106218000c00701f16420011182400d0591766a000010690065541c3d1410b11f0540d582c0100300e400000b40d44110400268540151207201405a1b4800c10b101c1d0081541c154120714040e11000312074000c10707940c8a145444907100c0400b5030350034803010750500181200200c1c2c1c586441c040c940d100080c0b0001403c030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 240299019 1250 240297769 240297773
    0x70503151005070f170a030e0c01090f0e070c170a0e03010507050703080a060e07020a03020d1e0c1401050705041706040201090b0c07080312070806010f0206010b0d0b04110304 77
    0x401a4903092252180140c8010350310010340140030344203601e8120307400d500403d6691902100d100305051480c281001c0104150170700a9064101a520407204402da802141c200c000640701c000e550b0040d41040418440e0074029124100402c45d8010554980300141440e03548842030032001040c0c0201420200043e510311254006205a041c194150020805480c001c400100140034501004003082a004081860340242380c0008c409001550301401ca02c1c2400207019685800c0d160303040b0058040d10b10320309139090003010224854004030f0f090190304200c1d80000c4800100c005000c80701d40807a00c4514400303250910070180b080c801d90319407030381d90785c10800044800315403103c40314200c0d80610304200060b684070080e28110345101c20000d0b2501d9003880c04c0f1f0b00780390868009125070300c00414036218010200f91004c2c0548840c0c4c40d271500310313183d0000444445c0501d183c5180035905c16401041100300e0308008000c000200400040d903e1036510002d82075451041032100000707400300c10310003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 240300269 1250 240299019 240299041
    0x40609090603051f180c2108090607020a090c02010b011d06030c0306010329121612210e0f0102030909070807090e0f010e0c0403120518040509010f06120506010909080f03070503 78
    0x3e00340d4031840c910342c14052540c4d00c008e1544200300460f0300450f0045403e10864807441c1c00e05019020b00d060603c105000d501c0002e0082500d4060320b03000908400b0005115814031464420025015004514655540c3c502178141d50001d05294101a81e6502c0211011040021401d00b00c02e448444046000100104840050361b6014100079070040f00401c0c6551400f00d4010045481201c0304e4100c0d141541465104a00034103000c809020340ca41040240c60742c401a06241d01c030040b00c240c00c0302d07100f05004a949018202c4960340182c011008560034031302503801603034031504600c0c150003184e40b101240400c011060340c00066691485005006c0c40c19911001548054014489824580f0b140c40e464010201c1004040c2400310007c0d80b04264046003240b00300035400548140081d08210302c0d00b0340204103c02e00d411810389000b10108a1750800b01000c0c001541250080403e80d00705812003004022807103084400d010704020302c0c010f602c0035a0103903200b40301649a49849140c0742041d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 240301519 1250 240300269 240300299
    0x190f0b01021e060f040302150a0b15040e04030c0203030c0708100e06070207090207150e0c090a061208030606040302040c110708030a0906270803040609090603051f180c 74
    0x169260401c00321a02c07003800140b00360700045500102625469a003400c1e410080011540e0031040d00707400801140202c10f1700005c50300c030015104100c1d8100c0017003a80b0001e0280f030050010404031500480c020a2241207010746180c0000c040c0ea2501c28000100c51825100358089016508034100202c44020107200f40001d4603640f0011740280e19050b40000c0d110041c0b030180c281066400308005040c009a030003165085145c8020402c1401d690412f05952140c220000070f10880d000ea000130301e166000c1c0981400c88240148045401366a6a251001a000101340d07580020741800008050398032801000c00c0c400160b15540d103041a00c000541c1401440c1d00300054030351040000c8124240d00c40b40b00d9013211030618120900788041c1408d80006030003405440e20140040a003c201d00c0d101000400858142e45c807002030f4141d4031a9441d06842080c44003501940002ca48440796801c201644000c0c40780310000080d012800040f0301c0c1008002d69816540480c60b440103002d1801850a42 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 240302769 1250 240301519 240301543
    0xc07051201050c07120507051e101109012d050913050408070b15030724111b0a17060601030c0e0901051011070e07030b0a03050d0305190f0b0102 64
    0x3404945000c50b42c40803d0703c40d6441c0103001c1c094229803038680341c0c40f42c0c0035034003020b9100d016100c0c000c01e0f04100c0219500c6001144000380078407528014048003510030261011001d0401d075003840400d2006646c0c090580c45014040c44a800000c5d461481c50309041103424001d0b10b07819141c00d0740005100d0000040b1000804e40e92600081c0404217030000c042d1800d050f4400345004196880040c807400040610b003580350103100705040404c42011004802c1c0c0354480c441608a188181800200c0c3c9040d6070303509543c0d085e0002070034106400003658281c1e600c00009003080042030384c1c035000c3c03043d5442e91030315408890f0070080038041c240da414002c4600032841840c00e1080c5e542c0c01d0380040d00da2070041c40317460b22454544100111aa01403074608030031380410030035070b951580d944c460485111000c9030a10002032410032100d0117803810980ca0000e41e6000380007001144a1000300340d00414025100300c22261034000c00740c0c0341071028000e151400103a003c000c0344178110100007a24294020b60f04c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 240304019 1250 240302769 240302771
    0x8130f0609030f02130905101e0b09010504020705010605120d081302010503130203010b04020a0203070210170103110a09020a0507020f060c030a03180807050a0c0509010b0d0f110c07051201 83
    0x100003155540f00d820843c0c036011103000349000000c581035001407011b0000108180210010048412100c4d44100c0d1450340b0126010b040d0b80e981079801d0115010441c541d5400300c41c050043c403140c1000d602400010307104000000b280750b2624009040f95404080c4c4030351a070f01c4041d02c0b20301030398400c0c50315030801546952106e25888650002e40507000060960141c1001850954103554003500700384030051000d4021503682d04075140080d144d91008606900070188100c0004a61b4420108030410080608407c0456401c41e0382d80c5aa50f40314089460b80019804030120ba00c246a200800d600c5001c1d84510303603150080d10502a82102c083c0d280c510440083c0002844a5404011114401c650f854001072442050b140007404190050010300310f180e000c6551002c02400061178103100d40565108042c82e0380c1c40c0c04026030502c09005e40605103906004000101c0c40c035400420040c42c803e90082420f11380c0408000003034201ca500c2e05c81540c040c001c2040703d0f0409070240e0aa01d4a1040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 240305269 1250 240304019 240304037
    0x4030212040605090103090302070e07050405040501050306070c02060309160f0e1003020f0f0d080403060501170105090703030e031504050303061c080f1e04090203040605180607081308130f06 84
    0x10010f0518058908568107040c1c84490100c2054030030701840c00076126180d0300300b00ea42002000207105400c28011140591300d07103000405c140c0340004030b00b480b60304075941e80903000713004d82d0a21806400103001b04055200e010445489660100241d0000d806144103c1031040c0c81c098070345214000c050b040020114111100b4409611254420080c0c450181c1d110108201283e0100c0c103a08009140a4103e500100e004401c12409410680c1281c00d1000c03203800f4403002100a908a820a03035444502c3c0e80a500c0810000f4040d003010403c4410040c16607a00c0c401a2402c0d090100040b1400c030340c16000001081524079042c100310034111314074585041c0307280035540c42c2400343c8505910384a40400c00704031058658120141402004801c0e001c2c2038903180c2d60180758010f90002e8908039141070030580051141001002961b2209104034000d02041d29403441c195440c142c058000880c1c2e61030220003501094105000f800d40440fa01d010300d11262800e003115100304c60b550400b00400410807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 240306519 1250 240305269 240305279
    0x31707060501051c06050907050604090c180e130c15030e0708120414040617010f0506090402090411061306020a05070f08061f03020904030e0f0303090d030c02040605030a0b0403021204 81
    0x2a02c00d8560705c0c0d02c018006015191040c0b4603291132035642c84917620900025002c074512150b50400ea00300b110903210b0306002e5411a818200710900790088444508400000404143d001980e036514140140c000054558a4084482c00d0a0a149804c0040782d1141110300d02000100038150052507490060040c4002c450b202040c1d511851041c0330581880c0c00c0120001e13920340d8010710003844620490042003e10044030360191076148620401039140400213a01d40c10301040f03c42c411036004001000756655583c0c1e2400401c4d1b00900d42e03400c030500307200400000041c824620080c0010b40c00400c0210003500e0900d16050464101507000c216403081006001800903802e600300d414507503502c0d9900c55000c18024024100c0d03002960108501090009142c2c2060030844c110f601619650461100b2a041c990780c0d1186045058012080c07841c1c00010a01c070b0021040c007103100801c04282ca59840c0006403502514050a503400d03946101800101501000518100e0001840315804c0901d13103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 240307769 1250 240306519 240306559
    0x110c0706091d060a150c0506010f06210609050a0204030b01050d0305030711030904050c1c060803041211060a020d080f09120703031b18050102030702090105150403170706050105 78
    0x21103008002d101e507200201d02d640c3d9401c541030001d411110012503c02641c014020400140700d101960030b801900000303d9510210030055003519101d031141302d00d485114184c8221000c1d070712401e800301551184041020700481c0123160040c128860050f0b2034030300f03504010f80c0c5410b041e0b008078420120f030011100026084000d44e603004c032080c00c210128000000c4c40718210320480c40a590701c17902d400100113002d400500078003400c140d803030a02c01003400c401e50042c0031a16940544103c5174400e110800074111444001c3c52540c0c400c02e5200f900241075070114803d5001101c0c01c4004d40c001540000c4c0c6264003003138007a840b945080380d03101c2905040c0709068440511103112040c00e600014034400f494000e800040d4100c02c1e1901e4079903602e0401000600c45032014021000103200040d0020f015880001a00c100030740041c80b0410b0b0740d00e08410455507409000c85086201000e00002021900450b02d0408402d011070082ea03585803145068412540140c10061040e18910300d800040c1c484 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 240309019 1250 240307769 240307799
    0xb071e1407051c0803180a0308010e01080a171c020715231b0906030406090b01050a0605030628080a021f0c030e0f030d02030c0d020c0d080d0b04110c070609 69
    0x110440c0e5949807036074818402144021202500c00f441703000140c80408d9480484a4100e9040b004003102503601e864100c1d0700c4801409000d0607070220305140c001c0c00140d0b50018002e003158000b0307548112400c4503c010a90300071190035201c2e80300301e07511446d40440b6805229101c15696441030640c04c00c0142c000c034500c1c4050920540040c13004001e80c40068110111521030000401c00f984a281c0b43c0340c030300003912481c1340459180c40c001e4000a400d080810048051325410b0700c441e411503880d1400e0000e010710607030001440c40c40b59441905070610520380440a0418000600071110460045c00202d442d12a256002103280c0740460072441e42c482000c0480e550b0602d41b90910390001c40000d1190707402240e100d41d15000740c2c0d862020254000004044584205099981c0e466128a00344e880d18036102040ba000725086845000141194004200c0140303400000101d44030000301040844d10918501c00d0f0130b00000500c002c8142c410042e070300c0240058038010f61a00c1c100242202c003052 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 240310269 1250 240309019 240309023
    0x406061a1902011d03130905090a0201080903040905090d110a030801090207020411041d09030c1c03020c0607080103150e0d1b050f1606030b01090b071e1407051c 71
    0x109481880e41c614400c0d044084070b003201c9226110142d081010b25501c9901140d84a00307a00111100054881058060baa2240741910042c1c04254826001950070540040c0b00500901007000042003403881c6108081c0102441e0000b840069000c80001d4080a8072000d02100d13036000d402d4003000a5800b0324428103403004c580300036840d0034061010502030000112480070640380410003044450101100f40c00944042850740095200c11580c01d459200f040c81c00d1696030072100a100c1000324081c10782c2c3e40c81425160040c0303007604504800d81400c00aa40590020705510010024001241c040c0c058003002c091041103825032141c000ca41d40d2091284d020306002d000c80b460a00500c00c54140225190000f044e20002d41c0c2c031181e05501d80b404450700ea41c0c040305440b4085152840380c4291040c2da40c0c1030b1a0f506201e420045500203a0f002103c0c103c4126140d81686500a1079801c2c2d000083c520680002242920302581d060906200e90003050007401652290100c5c2c5d203ca0260280181e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 240311519 1250 240310269 240310297
    0x23040206030a021810050a02070617040305160606030f0312050f0105010e010e3a080f0d2307020d05121f230301050709060c12090510020102030406061a 67
    0x10800c522003040c403410203044c0035813004000320074403042c940060003840901c13503d5080d94605601c0b00f10540f0541c501d5540c091f00000500c0000340043c1c00b410042880c0c1d014607440d04003580d00d540d201d01c29030395142c00842c2e066171907601e043c00301030f000381a00086108519050055140400d640e403030b080c005105031410440194820500341e4020000c00c3c081c03a101a000400d0042d8072985000180303070700f00080210b80c40800d00212039484c42c0301e50842590b8000006842c28500350424641d98100b8482000310b039a6440300c080034071800395450703c60042069008115440d000c00041d041951100c400d4062150400c0f00848901c0c0c0d44c01c0c407550007010064a81d12081c11510208108010f03a000043c0b0b8407410070308407008251804000038890400c5000307100d40e944050084500c00007620604010420700408200010f1100c0c01610400c5004d107001c8002c1903456000070940e5880308100360150f5400070a00060007841d008040140152a50303203811000301c82101469131242c000d11007444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 240312769 1250 240311519 240311527
    0x4021611060423030613050303040303022104060506030115060905010c0507080609280309030602090f03030313031206050d021012090804081011030a02070311060a23040206030a02 79
    0xd5520042910040c0807030f112008803500d482e283c09079461400410b100d100303214400c00100408074254a00d06000c3d4003130701560941d00c0d170781c2d0103034065004003001407a0003050407448014501009081c03841a03006000200d11400d0a4043c1803c644841070041403540d1595418410b05400400c4401190f07800c1c40c003844460002d01f40541000c106411264942c01002d003805164880000c10420301c40c5201c0c00038200362602429402103000740350004001c100012810004141141c1c0030740301d9850060280d0380802d000c1300000c0e083d580109c070410081010303170050070185940000c08005004009104100391418080018520800c0034002445540c40740d10160789684241608103034203602410030302809090f460702c91819085401a40d0061140c03401400c5100e0b500d0048200d01c40c3c1e8070610701d184d0749801c0d2101340a503014006c150248603441c40d5069410808000003480f03100703103a40000b201c1f681d0a0064800c0200118201c844c554920240320250341c0700402c882c0c005c46000b000603030b1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 240314019 1250 240312769 240312803
    0x1e0504051c0c0203030414011202120601031a0d050304090b03030304050606091003050f0304360209030708060f01090c1d0108130b04030c0c06050715050402190311010e040216 77
    0x11a542c480c00003501404081400154140520750f5404000b4090f01e80c160062111174000c8101c0c000c082c0348100150104011450f10750207036005400c0c4c614840a00e41501d50160041200400c80c0001156198000101044052024801c00c1c004540c101d002d140f42d0b00301070303c1d516521880500b0062040080c4408201501d00c4c3d6a840801594401c081d50034a0700d01d2284180c0340e0700180700d11a18824405550101c110700354030420f0a03140c16483c2c0328410500004064001e40104400541602c00c000022921140804c8100e00c14030703107038250307010940c103200084c419109103625220510030300d0782d41540ca07000c9450320b80c000c441080c41d10000b141e407905083d1441405082c00902141c10103c1440181580001e17a070103584e001d040c800520700d940e60402c1b580d80c030440e50050a85034280e1600c801c0000d141e00941c0d00103000034442c0c80c0c0020011001040b0860507442111580c01d10300b0310030b0f50341d40c0086401c22440c600315000c40c18000703c01403002d1000c9800100405003041034040d001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 240315269 1250 240314019 240314027
    0x807061815091101030204060804030e0301021b0115060f02060c0f040314011b1407060f0b040606171308030412090314030d1103010f030b0709050d061e0504051c 71
    0x8058100e40020700c0901d8100052009200318541a1030b0f8000304000501c042d4003c0c021101101d540e40d5a02e0117545e80c81c1c0b0111625039a6518465141d5000c0220170456101c01a0300a2107120301c1c000003500c440c0d9118401000440e540c0718206100881d2040c11800f50041a41c0d64030280d4100050350702d000c10341d03101c00c5512490b0001020064980598030080605501c91034070b03101c0c9050603144600160500b90382d009681d920450010070100f04000c00101c440d0030400e000d03020a140420000c011600040658803150030060008050b01d40742c01005110000071a00129100c8c007404c00309202d03840d00b40341840f0041001d001345070341d1030500072118811130701c0300c00550304405600000c1d14504e40c001d40f6a8850040e0101440c00c01c5051525080c022040b641207407500d0102e0221039155503180f80300508000c04000a110b00c1620029a51722074111290a5520400b0000303401109203820300849113150a040201510382406c0200040700000c070002c11a0b91441c91641c110a040001c40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 240316519 1250 240315269 240315311
    0x9181b0804030905220b030106181d0d022b05030106140705061f06020102250c0e010b0a0305010b07050c2206080c27060f0a0506121f03080706 63
    0xa0f0001445481741412031841480c072901042400c03428041041420300309801c2e604d19015102d1102524080110b5816087c3c2c04465a96a01030f1401000d15500c4a11401c1191480c540c40c0503810002e104031915800c01d0b510a40c00c05010303003440d13088076a210010010b010500940c810301a5442060a0b010001e0707050300d0702a607001040b640719240c601c0000f05039002e8540036804080c0d0625021503594010f00994041c500c5424598400ca00d00f2102d444540300c2c0c6032000d0320510b014000101e61000300f03488084c042d02100310b43c141c0d500e110030402011030358141e00c02c0c00f00d1602440180000b8002084040750410f0443e8a405da400c010144503582840c00704000d00d03070500d40f10001843c5840403501d1a500c44046490110804010403144400203d800749032181c41130040c000345980c60442c81800704410040e0041c40416110030102d001503104060181030002c21404000701c2c0c410400e0800e1618403068503111000e0729683c0d50145030f00414000400803030b140c4001035000341c4085809 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 240317769 1250 240316519 240316529
    0x1151206090e0a031d06071b05090a02071b050f0d060f020703020703020f0a031a09070b0f0d0516021e030c0d05040608060108011d13021009181b08040309 68
    0x81040c480702c80c028035a00c031407008003100880d10942101c440c943c11030070ba900d80d64001518440ca031862a0340d03621221140101a07030500740c0b8030000810245caa890702035120f5582d02ca801030740d41c4c0550400e800c1100c0b0042c450303180040c11000611a41c2c0300ca01e4140b100c020300396070f0707048201e10501c0d20801510382c0ca0000003c103031001c60313074005055000640004513030080e208030303034030048060074031001500600005d841d00071303404111400c40340c20f140c8482c0e103c2c40d98420382e119140c8800b030030746465001d0700d640d002000001c180d14041c2131807480f40316000186404001c40c56482d491020f919a00b003041d2a06400070402e10a040307403102071040314225159142a40c05000c3c01c1031002d4410f8105000e60400940400300052455010380031490580300c412440500d658068120804100310040c2040b4024249000200c01a10b030141d002c0580000754840480312414030340c8a1244824035080c2d901000d0910050032407000581585000c480c94900c1c020400340c1e260b0405580a0450380d100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 240319019 1250 240317769 240317771
    0x5160204090210050403150203011a1b19140a0209070c020301110d0510080106030302100506010512042301290109032405061e0105090a03020a140907080115120609 72
    0x203d0038825a21200800580b4070552050301120450f100d41c5049000900034450004c250004245d81c4803100c1014001039a078070181102c1d03650407100142e060404001134024a1226500d843c02003000c56070801d0030791040c01c402800030810310b40014804910250403941070083c1c0b07060380400c2d501c00f90445000c00d251524416070b1034017040c0b45040141790440d500684818405000703c3c01c52010300503c030450b07030554010401c400024030081b000740405003131141801000c1208202110284031400e100d035000380d400303100701d0054803910052035100d91810011645030071000e042c425440740c0e01e001e0f400d5400e01246404040a401610102143d8001622041c10405a004150004074001244440398070090015469100a0010700b460003294001001828841000c3c0f0307500c614090070310394800500d5444c0d9103950790086a1812501e421080060040b001104d401e410442002d58001416140880c2c0a41c940040c004007640c02e03404013020840e04d03000102c2003034181d4004101820000300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 240320269 1250 240319019 240319039
    0x2040e0f0303040b04060513080405040c030e0109060905010e030f030112050c03030d05040507060e01051209011b0804020901051f030e011401060206180303091207050a080313030801050303030601051602040902 92
    0x20300c040711344021141151030500703180006201101003c0406d80c0c43d42d210312040d062070f013031904201c042c217072101c482004c266441c509514100001d024106130640034282c009510003a40c1007003401e440e00444020341c294400c101c2c802c1d507010b401088070b04480024200c00340c0008070f40380032801d0482d007a04482d4184404900710441f403810780d10a0b809540308404558500d030b512401600c006506038110b50100d80d052015a42c50300c403481180c9e07070080c40e520000640b01140e0a22650411649440ca000613100204001c11400c01c10001c50141c03408480305641a880714201ca84542d0025200300c017055118140304401900940106010608032003c152056840340b400a41d85c00e000ca84201c0c0310400d24640c4e000c00c42c804402c1b01d0082480401402740c001d54015011100e5020031803c580781d100e41c080d00d00c08502605c003d94090352134102100c298044d2400c00a00411040e08814480e800c10420b06c42c00ba0f17003000c101da03107592643d0503041c56035505000040051070f12080194111003480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 240321519 1250 240320269 240320273
    0x70212030a110106061e11070302030d030c0e0904020307151407080d1a061608090a0e07121407080a0b180612030310031b09110417030a0c02040e0f030304 68
    0x71100588902e00c40d000b0440d1640d54001140e0200c4150244140c040c4003a1168285510401d81a0b007000e401c001103416045e074a602081c81c09002d25062000259500740842401394021081c880f4141c0451300100e070760802d6000a0381b600c4040c4107803441900e0705803100f2115400345080492001c1204003440c0c484a940c00e0240c240d82c0f00c1034400100c18134021f4403011030b40840c0300c00ca0b81c80001400007800c3c1a82020b50300400040c1da4415128031100707000c40f5000e59114440c1c10050301c240b007041580b40c2003882001d4403002103402c00500c3c240c00d080100415105031240d03d07900001a140844281d22800500002030491a800f203400610b141400e10400300400d20307503401204142d80410031890b09035601500e80c0815100c240810f840c034041000882c400324800c0c2d80b104c00072040e012107955240703281000c49140700882c04101d00042030030058003020100500340340c2584406189040120840284a04008030000344119a500354000100004101091401180208495903800d1034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 240322769 1250 240321519 240321527
    0x607021b19030209060a0b0f07260703082220010507170c011104060e1009081e030f070c030b15030304121a042105090102070b070212030a 61
    0xd8010004003400001040c0391810010890450707032000782640850103040d0b038208007100d0009000d4503800f6148990104040ba0450010310b10890001080f0b03a59819a217881c200d01e43c5400c015061040c3c0000510030419904401c03540c01c5a4140b0300140307103584666a0307240300c15200703a042c1004c1c100f4076003902c00c22040080c0052002001940c95004250500044503a84600800282070b003441c00c1d48803e0046078800a4031ba104c00000010941681403104102e4a4119600c542c0c00101c001c1e40d9080c10307081031034600c5d640c0d081c1413070301c40426400c01000f107940c0c000400030b8072260f0803209100b2900b000c0a10548041910251029968200d242001d080f44ed40340d0005803004602c4101140b0301c018100c04440425130082d0140d403d01d482c04c1d80f9a1050404002d0a0f605011070252030f81c9000340400c2044d2051b4800c4403401141c2c0701d40410400049500f41d03003042400380170068100d0603a0001078041c201ca0554103429900c0d641031010451740f60484010840314400491041c080d243c05c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 240324019 1250 240322769 240322783
    0xc3405010e0105010503100f020f030903070303050604090c0e090705030f3a1425050607020604020319021305101d070c0f05150103080901090509010f0b1b060702 71
    0x4100900000c84090722103800c8902c03c1c4181a8103500101d007035441c248182d00100804c240428005003402e54800c0345421a40c411a007106070368000190120825825110329504a07006407801c200b58000d942e01e46100404030700550070764505ca02c0c0040c868440810010028007000340c2a00d00107036113801560b5607031140842007403820072a001040d002400d458020501002d035854040410b0103415000c0c0e912031309a182c00152400304010000c070242c1c10601c010b500c02e001740700d01401c032a0541412070400201501200440d08610207010260350700080821368144009910503241115100040c8500c01440102d0a40d42c18001004541d004480f0307001c00b240c2e0f181404020400610740001031164040301c02101080f240103010011920400300300021911035000c540111402c0c0030400040710b030991080310000000a010241035911600d450024501030b02d90b1811541060a0311805428901408403a44d501080d0540c0e0004018040b12508240500f642c0da80d090505000352140c078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 240325269 1250 240324019 240324023
    0x10c020304052403040b06031015090612050a0803281401050a06080a05040f02030a0c050f040207030530130515090307061a030102040f03020405060105070b0c34 71
    0x10103d61184203210349aa01028012201d1502e861551190745001000b04040c004a0b0144100d008884202c0010f105e121078180e9050f417270918040c1303055982c0301994207a81141c8811200c9011250001e8000145204610340c0001520340300c6d40c0301804074081042c4001140f9403007041f08500280541103502a050b00d1011100700c0120f030780c0b640c007481010b03680381c07007018000340d180c0000420076200c0ea80a0b0f504140b00700101e002c42d5080f500042c0c5411151541601d00207807401081101c0e1404440c001022141a6006d43c1803c0058401801e076028406402d04154a5010030004d140c1c0703804d0a00030b41901000301c41d4510305022105005c1d140803207408840ca841891002d03174801d09480c4500b071240c841c8030300451070996280d0352800940851110340b0301010322b03800b443e88540da0030b00152000d402e1800d119014a45140100415200701030482418014200031140208180d0801d0550100c2c42090032a0b8030220b8040c2c400c04914404140754154120701c0c070b14030a0340062042c003a6101c3c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 240326519 1250 240325269 240325279
    0x210910030f0f06084c02030c03060f1e0d08090a0f08060a15050609010c05101a060a050301030305070c0e01061d0a060203030a0f0f0c0201020703020d020106061403090f010c02030405 80
    0x314940c102c09168141e481d41601040392007211400c9106190400d404511780d100300610b44075030702041c03080c140e8000380da092087c00304c08000c020050802003205100400111a9460921001103c800802d03002c21091401404880010014407000104490305000087e0103042402d503601040c200c1d900391409122805e0041ca40890381d083d1090140c0980110182200000d0610300400c10109030b21600109051141048030fa01c040784043c000c042c5e010b480308402060661071441d02010b040e000300308140c4a03403014030100070342c13960010503241500d505090180d0b48140078140040651a59030001d41c0c400d421b000041040c9a00ca0ec001100001da075203102c2c400c003c0001000002c0c0d68a000e20b8006074424800a011004140c0100f0381c000d801d401c0c001141d607450304104046c2c9804107130040150b0b400055090402d503041015100c0c0c43c42c9480200001d60a04500801400000c81090728600010021a0301e103a0103201f4500c42c0340054008001d4031004c2d00700039440360403034400c0a00c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 240327769 1250 240326519 240326533
    0x1f0503100605010f090305070b0a0215010e19020403080301150207080105100e0603010203090a0305030612070803040f0b12041101110d030b0a0b161202010b0d03050705210910030f0f0608 82
    0x31300e0044081c0c42c01c1d41d0b8840040e0030300e1810100a151180c02c5021484114441c184601c0c00382030b40d03178404501a100800b1448010b25060b07608529140d1040c0c60402d40750f02c100020004501c03504c01707a0b815640701880b040c25400b41288105e14100c5280c202d61960b51819050004d40340004000004443d1160300605087ea1414201401c0740021907580d41c10390001101c41c03000038400c03030082d40e02100c0142f0551000e0382c00b80485140c194684c02c42a440d82c00010f052110500380b00003000100140c0064610704824200000101103001c1c000802a9407020010b40c41a8090284d00c0d1004980c2d0301150003800c80c591006020b886a8a901c50050854a1012500e0103401003101c4200841c03070b512510071001603950404801c1c03620041d204655803030422045c15520f22109030b08240c000d660faa51075114500707200b411308440740744c0c10540d0305c06038005041d49608032040e205024805c581e26019884c000f0003c2c0c018207041c0d105029050300d04102142c040f030b4694040020303601000704880c14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 240329019 1250 240327769 240327797
    0x10240801050109050f04090201050d020a0809011113180f1406040608070f1e0b19030e0606090a0f1e020a0306050d0201050f071e030e1c03081f050310060501 69
    0x43c0e0700c0180206034000307494545035125803c0c603400100d080c3d071040c900103142501ca034004508036082035800b00000b9901000b40414503c0034003d0402031910041039030310380307007200740c00000501c5584220444034400d0780c90b404035140d16600400030198503a6081c0240340c0001510154000121255407066140480100c0c42c101d00140301c00945003020180e0b1680c40c20030030001c0c041c050413a00003504103a00180802c900045401900c105081c040300c2a154051a8401500f59015403220744540e030f01030300401105076200e0f42441c0d0002c0070824009004042e03040210003405041c03442200750b011b066080380002040e94024181c106055408112540d141c101f00903d01c030580202a000070818851440303d2201c040040036240d01ca070b46c081840c1d001d0b0808205640d1070078502034010500d0305081105c10304080f80e85820040c2c1d0490500703484003290358054001c500c0908411030500380c250101ca41da241540c100c9029007401401c640400300c1072030600303000c0e00031802a030340011175400301192 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 240330269 1250 240329019 240329027
    0x3040b0412080403020309010c021f09031a060a030201050313140c01021209090a0c02030408070605070b01062f0c0a0b18150901081306051503120a0c0b102408010501 73
    0x4050b40c0d045d4061843d041003100115440c0300d14000999000340d4203051410301d111100c65180229040f5290480420319508010341000d104152920326070082c0d00030000319035214800c4030103485c0d0908000b80c9a03111000c424800c138404010080c0b030750f06810140d1032540c1c0c00155552107040241d01300c44d104111118095001d0040c0290359800c0080140401c1030007000d5000005100d031584112414540d03a01355251400a85600c40008103074000784510900004056907805400b0700d0030190b4412840070341c03403405038501502d4000110710944600349a001c05018a48140c10300078464610181c4500c1800c42d540d01c24485c02244441c40204281d4500345400708005181003810741d98244146007005561500004054503502c0914960301070000c0c200d0b01c1081d000311311000400e8007400100313080c5442d2011a941d6116000c1c1c05001c500190340d48186200c040b2035009504002c1d0361603080810344070441c0e60f00020101d4485910f2420f8100700740c0402180d840540e40c0c6e200e2aa43c0c1c40c2c0040d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 240331519 1250 240330269 240330271
    0x2100e0108060609010203070512070c21020415051002010e1e030406120209040c02150f280e120a0e0a1203030209011e11010b1804030815040203040b041208 69
    0x2400305140c000011a5443c100016000002060041d0380c07a0036419511075081c000e4020100440141c0850413a05000c480703104103020f8090000e10540182c030702c01100c0340100104000038815600c8281c6011107102c288409001004080c5c0005400301030003e029000e08050509043c4a10403900030302d489402c0ca030a500110441034014600c2c040c10400100c942400030003840800607003c120b400010f0b151031040c1c003804449503015000d408a64610b40d030b4100009010f481c0c6002c1c00c182441900d01250040d00d072483d041c0401601e003000d0441420300a0220701e26507000a005403401c1c1f54191844800520212089584001700c0c1d1200301c0401103001c0d079074084ea000304001e00400d200064040c0c1c1c01003101480505000c40c0401240100314041c447c05044140003038000b0402915511090140c00146902200c0005d550200028060b140510050001c0e080101a5001c140d582041d4840d498140c007010300290754a1400d41051038224806660454441c0802d43c10801060310802e190307 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 240332769 1250 240331519 240331547
    0x509060a0f0501050f1e0405010f030b030706030e1603060203040507120807030f4808071b0b03010308030412020c090103060c170f010510020f100510210210 69
    0x26240d400c2c01d240c0119002d42248404080800d41081a03000408a225621040300f800f100718503903ca0401c00010b08258101291800789400c080301f40706c0a03640800d900c020b46080f498002a0802d034204158070301440c81c16200c07156107c00394007200740150b98004510890040c42116503055540c508040782011b0307000060107040c010300c6104002031092840c907850340340915008165140244410000b004000c040f4030051000f0014031042440300d51464512112820b07a0703040100c0380c3d0b2101032083c480e8010041407203c080340c0342c1c000c3d100c031286010082e1070500186901c0707607181d01d0041d010354015501540e50001c500682541d2902c00650361220100103000030a00b40d10b950740300005040b4010303961040c0410380c0f060075200b003103000616201d01301d2a528821554540b9003070000d51940d905200e0210341002c1c210f040c01c50b900003203900c80d5800300b2800058036034451401541c5001d140c1c2084800d0110708026004582c0b80360029844103000300c0c4c03001d500400b007441c107071f0b0552403071400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 240334019 1250 240332769 240332789
    0x1050f0d0c0603020f07020306250f0915020115030302070e101d0a020903011401090e030f03040308071e03020a030c110c040905030714070608070207180b041506090509060a 76
    0x2400443e00c65005001900500214a405c11550b680080d0415a040303490307011110820031482c0c03510030028501e80309100d19050235264800500c00080c04c0d03000c14064003480d402800c582d00e400384d200750300058034009902620400e40b9200c0c07400030340328648d901c98821049110400b26605030815020841110311300b09000900104108800d010b0007401018044506d0f4203009007001d940b028007500150300303501092480c41e9810300400300700315000303150042c070241e100703018002c4420001012203070001e82508060541703940301d030012118105505600a15040d0035560151140d4040e0041d0030105900d071014000103906d00d4084a90369504000d070705003a0302a40c0b80d10714604041d4000503c007800b81c002e03039103400b400e03460380300d0310000400c0c0800c03041d032180c1020404168480c2515401102900c0642111480c140000e1840034000c88400041540e8414a42c6166515031043d450116005400802a55500000f13410b510161050a0080980c0000900e4070301e8540c203042c054a20303d0708 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 240335269 1250 240334019 240334043
    0x1110a0f0311090d17040605040911030108031c090203070b030f09010b031c0c08040b12011703180621070f030908070602090604030c030c06030b09090d08091f0501050f0d 75
    0x204004c10307801075110a890001203800d50380c500480790310040014280c142c8540d40e60b14500540b4104031500c1c0342c0f410203141030510040c003200c00080202e034034481320050314100c2840541c450000900d0324580080d0325107e1054009014602080036610404100304020015554903d03e5803e03148000c12840d4103402c009a154680409800c2c0c6030610441c40c130740801c2074950765845403025841a045042e0712800400c0605e0706c0044810218058032a5803c43c58404c0030402e003080e501d0041c1400c0905190b1100c40040c3c0c42c0d11a41c00740c0d41e4180f000700c20325049540320b00c1021911b80b0180c0d016000500400c4a44903c54000e01a003448240e022892500d04085c0b620307418001d4001da6041c590001d400c2100002107103403421440043c40c0109259210301d0725000001d4116503402c0a03880c01151110b04004440501080b000e10881660401d42c0650303413505040c0381021008988003c003145040840018444164003140c141d030015603001801d80e4420040280c80c1c92000b030001d08090102c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 240336519 1250 240335269 240335287
    0x90b010308030c0f070606050f030703030519050f0304030c0b090c0a03080f0c0304090506031005011203080604020f1803190c060f030f0c020a0303050a0203060a1208070501110a0f0311 81
    0x100941d0701c03489903000541001051352107200b0300e0340312290694010b43c5600d070612451070060284070b00700708120300074601a45180e5000d400c1d03005003d400c4140700f07043d800c110441402031303080326142285890244d58914261a01909854a100702a110680d650300025859040010341410500004000719815440c0d95900000396010080c0d01c42450800d00040c140c0382c200304040e101406080c80c002c1507a2904106040c03a15a00342c1d0b8051079241000c1c01044000c012003081090140c00d403825022030b0742e414010034041c0c8681140c450400000041512030103002000d2a01940c00803411b845a0782c00045200700000c09011018040b4016044104a2540507040003841d920742c608001c10007d03403070503040c42110702010401015030026070001c4100356040c031809500504ca10811400c60800c1070101c1c1c07002445014400d4810101c1d00f1180070300c221941680d43c8503900c18028800d02e203080c03041c01e4082e00080d0030400802e81006100d25071038000d01888981000115600e41001c00f14 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 240337769 1250 240336519 240336533
    0xc01032702030f030316032007080a0201090206030c270105191b0606050108060a0f050103020901050c0105042301092006131509050103050906040209180a030c060f090b0103 76
    0x41030301241c0c588142050145030788070a0001d0343c030800704410500086440000041e0544800d50a0a4085400d900818040b03800d140706443c01c403034000300c00688540304c150050b801001c2d4854040d610641c0071013000407880c18040140380341030889201241c18120a412480d5000c01c160721203012032024010a20b07602c0308040310300007c1409242800901801c81a6110705400b000c0082d96a2619a002400301756000b1070060780004050b540410618505014000c0e03141c1e480c0a01410103400040550b6140e110360306680b07041000030020440e0742854a4041d00744070f04207810008400280030b845821800601c1030b00c02d19a0030400c0042d0291100810881c2c42d507446100a174020000d12000c070708044c00119000250241d00c0b0440e00525030990003070418280ba034410f038105800c110801050980200301c640d0001d5050f5202002e6486d81c2040325a00d0803505003511240c071a010202e0141544504911100340c000c040400c007130102420b0349010785141c010050b1000070002d00400001e241 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 240339019 1250 240337769 240337841
    0xf0402040915020a0f0e060306131109180406060f03080304080d020c011503021903081602061b01020d0609061412010e0a0b160801150e03031207030e0c0103 69
    0x80391059071040d42c1906109000c82c0c1019501c0400600850101c10003550000c20b03000306c8100c200c0d40c035429851300c00005100c804041800e68400c1791540074205400035440161041c061008001440e4100703007a2003a0615030044030240c2c0d00c1402c3c1030700002c000e030058601c02d007680e0300000040c0c910b581c1d68030740850561000450681e0590708010b1004c1c0c0e07100a01c50305148850300c244031800c441c80c40c0100990301031003007441c00074014003407020000152030714101c0721582d06070780c0b03214120007040c00060b455000e15403000c001c00d00007180e000035003001036005100e010f04041c000c00c20a619411050b08907005030050000048a18030b22440500c1e140380c01c0e04036500504004034005401a01d0941091070640c403c80d14400b140c03040c80404019440381c4064242c02d450819005d615220783d81d403904034240b25200074020b0031900c10078143c405004a030070910043c9400b0801d0704107101c000780200003006d540c01c02c50140c2c7e040340c2900d42c401e001c0d14021a03e42d06901103200f0900f600c1b0720005203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 240340269 1250 240339019 240339023
    0xa0b16020315010306090b0610120b060708030103080d0c030902010c1e061803021c0206010b030702010e0619291c06060b0a020d0c02030604032708030901090b030f04020409 76
    0x2c035201e0582141c4540e081050302841c4a040042002d4645203004070341180e010340202d01c10300710f0000011010b42d0084090320142c1ca0b0384008912405c050020407043c0c4120000034140000000001c0705200ba04401048580d081041c10000710740003c400310103c401c03440000b80003c1138200000003007010701e001050040600740640c00b1001140d9121821101c501c200ba41c02102d00d0185030042c1a014001c80880f0141072682080380c03042d140c0000e4403034405001b1035150b80d43c04400300d08054401d60001e40a1000e980840e00c040c10040074090100d07071310580c251812810002c1c4091001c05081040422071801c2241200505a410402c002c0c000006950640755460710101404160709000316401446042403071550340000f100d009050805501c0d11009000842000c5401a1000120320394410340500d083c42e800ca01d00348020841c0240a21240b007442c3d038a903070101d6440008002010240002d80740c502c3d40703654414000215000031640407500355079106c0024007504140d000f1055180c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 240341519 1250 240340269 240340273
    0x3030507020c0d120210051003062c06040c05041e20042309252007060206070f02060103060b011106100f0e01122607060203090c0a0b160203 62
    0x40b859601003a5a81c0c1562015039110f000b80585584071501404a5200e10b2404c0c003081c0620b05c1c01c1c1e805400e0440381444014031480c0d981079a94081000c462180d000c68040e6000e91603039003c4004034980e02d0b9801c3d58181c4952002804c0020715103480c0c420400703803854020240f074130202e03c2c0d1081c1d03000b00038030044600d00400d0f030503c0d14140c0c01c045005002400904000c4040049412003080c05070001e5041d00d8001d80d069402d0043c4085404070400d07810f801c4406c64180c800c40e13440100c0d40c17040c03c400d0050302400c2d20300e01c0c0c40105030041105d60946130346600716102c5948a01c01112660341e229000405604410014000300d084d0703801035541c641c018102032441c001c0301c40c10700c0d180030b400b102c00c030500a41c0403100b40984520b504a0038004c0a600c007401c1c40d69410f0540d85181e081c00320b0002041050900c42041042580030f0a42c40c800481e51100f07a15000a424000044d500c101c440f503c0c1030040180d0b280c001d240924018082c4c640d0b6a0304a41041000510030324405854501071340c1c14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 240342769 1250 240341519 240341533
    0xc03070219030e12100b010203070c090c030f060e041520070512030106080a1808030708040c0302040e0a060605030a0c03140304051c05060703060513091109040606150905030304030303050702 84
    0x54130754070298805001c030000280300c801c0003000840e0844860300f40413411504200000800309806041c44016282140d00c0002d070010f8220082d402880f540c10506415814000c00098542031001c000b44164041c0c0407484501d0900790720380d03046640300f18841080a01e003034442c018504e40c540241c450140b00d4000c980d910080c0d00b4062101c1e800980c84176000071010f00030802e410740781c0e00540991350700f10f006d401d035030005683c0d0b40001030100400c3c503000c100312200003500f80020208840010754002d8010400d42c00d0600004d500e51524010a0303803901c1c1403103000280c1d0300b40024010400f5802c4040107084d24195580c105104070320010200f82480b082c40080b8695541c0e040c00341520034120411002c048192800506000008001d107007854a012000c102c2c589515030340c5080f0180a13034000444900c5460066000032841012540151134072003000704020701ca1b032188081d00d842c045090f000480d07222040790120080e0040d65010f80080c0000c10009009070001500003e00d07005a4004c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 240344019 1250 240342769 240342797
    0x190b04020d15050a060306081515120601140312370e010305160e0111070e0408030f01080604050c0103090c030803040501061404020a0219062a080c0307021903 70
    0x1e903021100c00840030b8040160410480c5801c01c1840e000b46402e060501001c2d1500400a44441c2038541080d906000400002c543e922900d980c0030401034000d016541750f10001c11019070b07a00c401d005420503006002652000d615000070303c0ca400c8214962214540490a07140ba107886404504e007210803098204096081003600307039540e103c5001d955995400145960005080c6e034001b4101e10307500c4040940c081d207180c1d484021060f070b14800f0708104882056440d03895140034229840886881106001d00c4200044d0f54021405040a100d6001190343c91340801511a01d007558021714551221810702c0295010360001403409000d9841d42209641c0d0751100807440e48110741c1121265501d034000d10110a041c90380d0b851181003501c00b18140100c51202a644022650b4241da46020790411402000916008903c82d070342008031804c4409548a041d11a0303803c2020180c000c1002400010080c0e04400c054901c5151360364000c00c008114803600308114001100103804220a40843e520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 240345269 1250 240344019 240344021
    0xa0f0c05061b0606010504150c03120204060207050f0609011b021504090c030e0f0c1201061a0712030506010c110a0504020f04080f1603080d180c030303050f190b04020d 74
    0x1000d0300302d0b4440701e00b810458600320303040c844020103c905200d4248400d0003107000b2040c80d02d44020032400d05084140340b6060030380b20750500d44c007590035540c000180031a14550104a00080340c0d001c0c0d0307210010004180802a2501806810900140d18440c0f5542c0b00480b0309591030040d4005094641820301850000700070b5409500b00148071502d07505c000c1d00a55140c820100c4c0d0f84003500140c1801d108044003984c03140035006645218120319500c00c80009029409007005000005d00c0c2e0540c0281900e10040c15040100151120101c10041c1d04a50b802405102d00c1164169119200c0d0300442c0c0e80c0d0540188070802d01a00801440008181601d9a200a040814034080c2c0c6540312481e01d4a961b03e0003143e550100d0580e0400c182c001400108071460380146c0381d01c40c4e102501c2d018401d41d248010030725603070400140300b00700c80903005010030040c0820076039000340d4083c4142d60f200c2c40601d16446c8141c803c4001d031460703c4a070601d6005290301031102d014004002502d020454501c01d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 240346519 1250 240345269 240345277
    0x8041703070e120f0628050411031005070203030606071104050f010801151802030702240f150f06030622050f070c200f060a030f0f0209030a0f0c0506 66
    0x8408070b0408008035042c0c1c0f4110603540c00280b00c0030014015250b05001403602d6542c082c01004400d0101d410702035060b00e100c106203010a00f58107081100745041d051000410420002580c020b00a4003051080c41d0224010b49104e0251500114031b55211082408450760260700d084d03074140118440060141d8450042e140078208107105070840b541441c04443c2100c3c1c802d113900b0390729540503c04001e002c01c2a075a15611100d20b1000680301c1d501c6039030580c103000c02c1c0c5116400390a0070360109140e02250400d050300902c03070134418408070307070341c400700d2142d0310041000740d0368030844200c004820340c90104015a800203005d0211070811102d89200500031001c03039081e066094070788041152508402100e60781c01440d5180401e003141d03154947c030555902d8a6a4107a0044412140c05450b0701d40383c845040310207002e00f05a55801e581d0400800a0041d824000499404d01c200501803042c4c42c000d490103020001c014241c100429903880c1c0d500320203500129400501e4010000c0d240e41d40802034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 240347769 1250 240346519 240346531
    0x70320060402130c0905061615050406050a1e05091603050309030606100512040501021207120c0f0906080a110408250e240901060e090a1b08041703 65
    0x301110300342403040203420508607903002981441c00300c0c0750610315407100255044039800d485003644c600e42544d9020016140b0038020b41600180514102a02002d61010703102e507000324401c0100b602ca10380b114080d07500141c2c20b580d071700c40d40301101079120748140c5c485038010300c104040700ca100055820100e201d4480c2d610075110b603080450840302c035080c1031014986c803800450380804040102280544280904210380c031400030030400240030400254103c503211190041091f070300d440e14640003828240100c0d009051581170548000a030350123030407090a4205640c507a04045424001c0c2210114001030000d501562200c0a00c2a0b09802600900142c0444c1000e000c403d0b0018048000d2651074075640141e13001031240811910701c103080b80c44d800c170422590710209403121401004110300d41000040d1310450f00c000000c0d190350803080c4181c0d9528162032b2040e81d950303500304440481d00001d018030201250101a15510b03446628001d510501c200e020b980341c048000107508068104580f2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 240349019 1250 240347769 240347773
    0x50106050d050115020316060204120b01080c01020105040209060402090406260d09081c020c09090d020c0904020604030201140c0706230a02100203060a08100207020111160308070320 80
    0x5080741d00310880c040c2c1c9000d0541104480400c3ca06100000e6030b07846410044000c16000d4960403080080f55011600140804130310113041140c60301305141004828070900b011481021510102035006014141c8550303001040c1030025514041400b0181d0711502030b05602942d0307a600815880009200155000c21782854003001c00064000c0614281d696907400c07083c000180d200300035400300040d09003414108481c680c450036200c0d40e41a0310708040011600da014914201304512401d002400c1101040386a088842d0342c4110402d111b0110001c0c1d0740a500418200028000b6502400d8800c12040510200714a03200780c07140f0f91800c0410b160040400a030701e9015082082d00f90540200100c2d10b40c0d9a014501843c504019540c2c0c0c003054410742043c0c0d0084002030880d603176030f120744000704070120940c0c0140a003040d100009510480c8200c1c0800c0c080032010140501c0000d410840801c10141d5001142c1591902c013141d0b0402d11040701000f00d95010203203000b0581401d41d00680c20040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 240350269 1250 240349019 240349027
    0x306030a08071a102405091011100c050403020f010e031b0102120a050711040e01091514010b030c0c010f140414030316050714061e0a05070504141305010605 69
    0x40c10952400380a032481e03040382c803842024401103d94505e5510444c0315002c481d1501400400d00340c0b01030244144040c0e0003140440c04400e0300340c20200280e101610f00082c0c4000088600e900400c803030454260b980019824002071005080242c2e10701100f04050500c0d0381019036480004c0e180a103418140c810030f50400320b0501c0c66503010802101c07400007644c2d54034201014210003e11a005082014000e00202c2c0728260090726280e00c240541c441010090011441904008060300202c24260380028030f0b1041500b400340710004000e048c0d6060b0068145036840c0da5405007a950082800a00750b5560740074014100703802031169100414029a10403d5407401c0c0c200610a104800f13103041180e0402c00130001401d03001c1c0410000500ba5041c400d0700c070a03c0d0308101041d17010601ca2110300b8421081401441c08006c02c40d801210840b11410700a59a81c11554080e00d105803184004a401803109105100e11080075115080303002e44003008082d49140b4000030780f9402c0e4044000f05500007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 240351519 1250 240350269 240350303
    0x501060c05010501080601140d02190906030507090c0f110304240f0c150e03070b090606090a060b1e0909010303030501060201110702030d080702210306010f0e030d050306030a0807 79
    0x8001c031801001700070060242903250402c4a41000c030401a440d12808518859004550f12012034583d89021040b210109a484540e0030004249038001521075210380c4c000005d0ba210540035298108105550342010750108039401e0345d41c8482e0764680c45003404103010114402031456550982565007150b000d0b0100840e190103401c021030142003000f00035003500c40030003149520f54900140f050f604400103082c51140e402c10304600807150018543c101c0b210500c0284240056124040c1d1401c5418824603240c4122403012145940300d51059003205220981464402402841003404400c83d0709103040e08240c001141414242c0044010030b540b100140702c01a42441651003610304040f01d549840d40b1030700040c0e507800d2004174030740400007040001250f4520070301c8850003850202400000300381140b40d01c84c455410031110680024070f60300d0b40c01182071061103001a1902c02602401c07080050b101c041b9500c0d0700080900d9014807a440d607a400045c2c60900800070310b0b000c1e128464860801f9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 240352769 1250 240351519 240351521
    0x503040b0c0c09060d03140d020c0114071107081b060408030d06090501140a03060c050c06040606030512121302210604020405010b030408030a2f0703030c02010c0207090e01020408010501060c0501 86
    0x2801399401000c0c0b4007440800a038105003403040251211403910380b0b13180301442c550041d00c51210101041c3d402e15071524441e60440d100300c3d02500050300c0306582c0400c00d4540c140d890000740700703070912a8008a1507009030391886445140000020b840585080e4594420615681c00701645004c0c96030358080800609000b80b1495000d05410002481c805902c0b00c00a24040c600340009000b059407042c07071001c1507000d901203030300d601c0c3c250040c0d90070fa01c0c0c0307401d0480091641d03100c143e0715405080c060500c1c0c146580200c0e036540c440c0c000040f40742d40384c40c245130344a5000c44038102d03002030210061a9101d007015125500e06c1446030020240c80c5010b04c14401500c506038030070400f0310014428000000c4000054a41c84011380c1d200003400444d404d2818010b191440d9100c01c5000009030510b0009060300080c004903000ba2010310901c242d0400c100d003214a03081ca80801a0041c0d40c013070005070b5aa410a0011000c0d24002508190310f4501c82407c6802c02e071700104c0800c0a05078100d08002007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 240354019 1250 240352769 240352771
    0x4061e030b0d02040b1c0b04110d030804030e010e13020c01060b07080403080a170412020d110c0f2b051009020f060706023615160503040b0c0c09 64
    0x91440c09100d80d000304070100b0705412207108001d1069844803581c03041c0e601c031201e407003900600d2038020b50161862800d241001440c00c0d00e00395102410500c200c030403400d01078a902d041541c15a510340311592107840803500d81c440d21030024104603a007508000c0d40ea59000690343e285107000d80040e602c14154412908507541a40040c030221018407030000401ca21030296421243c00414969a480c0d4165049404001c4102081140f100310300900c0180f00907500d000c0e842c90380700d400f1079600c010301c00804da82c1c1060401309090f036a03005041e240600e081c00e80481100c00c03406001d0b1304648900800d0b081c1c650210000e40707107102c07900b80c04620602c4410003d907a034514079224104003044464010031242517202d420140a20030024010b001c01543e0307412180d04111692054012003464180c8407100c5070303250b0501d5000229134042c41d85c54600350700b50403036115070a00a2440c1184441d4000c5011144050645150000703101c0010301c00c0c3c81c18001c00284080304058915010010100103000d14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 240355269 1250 240354019 240354077
    0x207050604140c15070303021b030a0203180607050606010e01030b041a01092304090314070b010f08011107020f18070507050d0e13090507050a0f09060b210a060b0406 73
    0x3181040710713031a58805022105041d80510b805030341d40803034007014084155140c00d26000c610001500000c0158044068075100c040507959058540389101004218011b25801400c0f54216401040303d81d801021211510841030501050291100000804803034501e900c40c1510341d10310034425038540e1300c024681e02800080d00103070110b50280c4200902c00c414000028000ea0b510300c4024141405020000081c1a224500c0e540d82c10980c03401007810003007031042142412240801080090381030040350800f85410100c2420103c3c01d408004a4030f100880d81a000018511044501400c0d02203042c4103203190b858190355082c03680b43c60f500c0d11181c100c6035010014002e5004060340c0e40e80c1c44100c01202001c2000c180340700142007990400400c2d40c040342d0300c090084400618030680c0c4034804121844e03e582080029901c4815903040e05c90410032502c44445813039802003094100102c02e8000030159400a000750b15103040c503005902c503403c0000841c1d011030718070900695031360504444ac1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 240356519 1250 240355269 240355279
    0x60b18120609030304120e0901090c080c0c0d0e040b09070206041208040b010e250309170301141e060301140301050a0b01090605070303140103230a020f090a0207050604140c 76
    0x101c2e04010321030300d80c00040c000030700c3c424003202c0403e20507100d990300b0f1954800050040d040d41d607499080900900c44190700d58049941c0c01c000a207000c4501f029a105104070001925681614035811100c45003007990311a44555143c105800c142c661707010482c030421007030b0000c18044c2040d0a28030f440c611020749100c1008010f008001c0011101c3c0d1203503045902d14511820340d13071541c0201c4451442031000c0c044501031602d400b4410141d0542202081034000d218180700704a00c0080c90401e88024003e4544846e01004a1601814181401d5403401c0078010180040000080045c2a9500030b07840075140d401100d900022a00e401c0c41901d800000041041240140c10310010708801454132807601403100c003040b20f80905019410005204030200c0141da000d40c1c503441c00003165a14005d00c4645400c0582c404417030a07400080d0038152603001403034960442490010400403000041141860075000d0100800003542005064002c1e0300c20400822203241c0751f800989441040040c2d18810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 240357769 1250 240356519 240356521
    0x71202090a15020a0506181209120f010c20030a0807090305010608010204050f1c0209070e04051f0e07080411010306030807210c02090a020a0908030433120c03060b181206 75
    0x404000902c5000000300b003042149c842400b900090003050403540d81e050316015034030b00a04003030019030007410440d0954036088101e9460382c6504142c0406044900c0c0700c0d50003000220302031401182c010381c0c00400380c038241581e50340329921542581c0d0f0503031004946a40208052040b407800a07448599402e060b03504058185403110050805030001da8080d00507440040850b071620b2107440c2110034910081c0080c4801d0404001d03006d59040104511000140050400300b012040880071500544465a030a1000e440c0c9803138803040a03810041450526954032800000508103902400040c1c1c0154500c80e0f03420707240c6101d24440c0e504031003010308010b90000b0710401030b80c807a410281c001407810001611048202016a8000007582005001d84004a8006214900c4082c00051000c0354100c0b40d5110140554444c1c08161031051880800e07102200f14058651940c84131202c10268603003c0303083ca075030b8a0808480d03803042c40c0f000e22400c0e03c24008000e6082440032400400c90401c020a07031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 240359019 1250 240357769 240357811
    0x90e0a091505040206160807170304032312011509050a08120304080d110324010503070c060b1f0306080607271a040815071202090a15020a0506 63
    0x42038011698030207260b03034a401007401d540740c0d0401c0d07a06070054802c0001801110b400c1c01c2886812202c0c0407a00e00d9106506608840030020549001310f5040c0c542c0c20110b10380407004a4200c4044402c0d03140200d042c44017074010102d404146009100e0808170404244110308010300c1440346401440c064050340b81e040040710800a6412003032010035681c3e58880d2124a010700943c421014660341307003801c00c0720080042c040480210f0040c1814284c0c2d0313401c408000301105132409422540d07404038600f07000060b804c600448d91000341d10710075500001c0c2e4070036070f10004541c001c0004000260100c880070450080760144100000703032240c0c4000702352510740b00700c008100310101104185031001c6501e4039140d49040c90040000340c000811174080e04540b4034020b6805030030500c20401184560590282407500c0c0b182d00ca4001e0001d61b40c3c2c85010303901900140040c2d440001c09542096180d00c0c0003442c0c400c00361443d280e03154180d020740040e0803641081380c81d00d00d0161400c0006c8144c50100c41c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240360269 1250 240359019 240359033
    0x9140c0a0303020715170103080a122f0903071e090b06030408210109021c0c020606100918021206190501080402010302040e09010605090930070f03090e0a09 69
    0x200b10754411703c03284c81030b910140f01100e403014050080b161408088001104000e09240a8407050409544da4121644150380c3c000560f404c2d581c0d141a4a400c101d1020300029000000c018030011030140310b460b00c0440c1020a242184030750000b5810540901c03c0b414ac0c200c03100000b0014a4940c0080c000f040c0d0400014410748400b900060035860001074103604e050880f00c000c141f001e02601e80c1803032580d441c0c0c6130401075403040007010903100c000042c035142590703a0300c148450490181c3c002e03c0302d9039880e03040c088255480b1443d0740500000300c1d400241080001c1084807030305031700b00300581c4131701c406607d880600c0e80103401c0c0c0307114940b81d00010030154110842e02003103490900e4420426103550006030000d1140ea00010080700c000d00410014020540050044400541d00d40450b540c0d8007036210f072146d00350100c05010000040f6080168080f041d1110364020740703089400d15060b201d55443c10012070b000c5044000c10740801c820820500400d480c540e110540c14002d00416000343e480e40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240361519 1250 240360269 240360283
    0x3050f0d020c060405090f041b0807062307060b03120a030209090f07021507031b020309181302130b03010207030807031b170709030606140f0a0806011a0c0109140c0a030302 76
    0x2a1645000b4000ba007408103800310b10301c001e107009c8090002140c03501e201d50f0312005280906008100d01107100000041d040031680c024980119205040a00d6540c58a0283c42c40c02411a4144940c46480c0d500c5595040204429480c544006076658122800d00c840002d000748164041104241040704454010501d290090708801858201e0b0759a03210036001030030560514007018100030007a005660700000200301a1400f00e81c40903000502c807060350f05e00401103801c0841034030220b03403d41c01401c0c4030b420602002c00c0b00780085402c1240300c000c070f42241c001c400281d000401000134000d103c0e8040c031809181d0f56401c0015032209070b01980107084005004600404440c444d000103003500d100790f03030040140d0340c400018440d81d544c0e4a41c802004401c202d07880d04c9504900e00c076100c01d01c0c01d400304804481503580a8130091f840c050203491090040d000c042c0500d9400c02400807070308000c1c4101103910784682c0d143c050500000c1c20f203c0c6440d8170a4011070107010203990900200f50006404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240362769 1250 240361519 240361531
    0x30f040314030c070608010302091b160302012316110a03080402010314011e1e060e130e070e010503030310151206031a0603070f03020603040c03050f0d020c06040509 73
    0x4a01c441918180c820b02d035201e8044214568014540c0108105e44c3c00742416040f07900072262080d198a47e03210030120f0088850b880351640d60104000d026581051861100aa0203800001020203048001090003074107050740713480e0075096004106031101000320600703100e0034515060b20000e51b2982c250344d4071900c0300740103024408400001402c581c440d800220b203000c04523640d4403213941e5030844858424501c11900001c24620000440c0c8500307a560303524032001d5107403405481320340f5004045c0c1c2c40000c24605140c09c4144208202d030701310168000c2c80c01d07052444000b42a117074505483c1d040c006406801c0b65210740c00400503c800320130807160282c02d80e1108a5201010308484109132003001034100c02d040d1650501500101b48200020500f60f06050a4801952680c4031010191600110700524406100860080c009030901030065640305100d00400b495040e00c0e9107540b071804403040f54500007a80003e2005001986c1880662102d0300169a103a060a0410b80015403c800c028a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240364019 1250 240362769 240362783
    0x2011b170408040504020a0c03020d0e0604090c02070b03090a03260a0c091814060910090b13020c03030412031e090f0204022101060c121112041d09030f0403 69
    0x109050282c2c40e0b0849004020003001103580740c2c01944d02504480320340f4000d8015000b0f00c0c1003640010701415100481c0d681c000c101500e000e00313010030f460081407030450030300440c45440310100d21514104000d5005100031030040c2000010f6203030007001740814160000e4a620300035003008001644800c00c0c0d8100691010108480c8040341003203e0518241c4d001da140c804080071402e40391501390340580c0c400040103481203003907640d030402d11100039415034081c0c140c8007241c4401c020040499200c802903071700040180c00c149130303990300d14402d070f810404d01001141c0001091204003c1c09001da54003800a509040c000c0c121100301d0310030400e00d261000b0305050f46030a00324040028210143c007115500400864585101507100341c09580790564110212011000200385030f80140007400c0c040d54030274064008600c0081c021104810400e4403045c140c0304d5001d28224005649000d00041d0a00344a88090120702144d0000f00300f2001e0610881c5410400040344c4080303d85d000c03202641e4100d20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240365269 1250 240364019 240364021
    0x7060834030e0a0209071d0907050708070501060f0e0a1d07211b150216060e01020c15090a0506070f1b080f0706120506010206060f0301290102011b17 66
    0xd0041c1040c0701c3c190000d5100c01808100010340d038110341801180110302501100e44035404040c891011000d40300d52002c210240700703c10004103410010503c0c18800d03000850420341d60091420800d22682040424018a50411090180920139403860004141040540740c3c0036490b2349031254080d00a4181345110010107024803e0007002031145641d0040c20358109074050f220030350303001c040e6004000c11640c0d01c3c00c0d8003010510020722895240400511030020b0352414170f00740d0340c0c518943c5180b8154041d2080c400840d40e1840c0400b12500c104070007480d610002c50741000100e918030341181d88116418031201d80894050700b2640042e40e4002c071441d540e01e98180001011024a6000c2e08203032140102c426540312001c80d40d04200c41c00f58407900d01540c2003510140942c0c104842c9640142e00010000700f90b4076061218200702600500001022100c4003502880624880001d403a0621100150748065909105a80070b01006408400100d1051040242003140c4001048045140b0714 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240366519 1250 240365269 240365291
    0xb22120828021308030408010218030706080a0203070c0803040605040303050106020316140c031e010b040902100e011407110f090f0109020901050d09120806030c06040302010c0809030706083403 85
    0x2103c4034090031000b8102c0e62550303612403441d8040c0d404510080d00242521040d8101800c002812100340c2c0c2140c1c03200a003d5807403c0c1d901000750002000441042000d245590108031444011801103024200100d5246800d06014040d00e03010380c403000c215442009902d211031054070741c0c0350040341d010b12076050001c8111203241c0342010792420b030f55060059220f8151031025040c450001d4407560802888880984c800700000c940301440060340040807544180070081c0300b4000118070140505000440603203402040c51a5001316504a9070801111080c138420301d41600c00850900c811141d001040c1342034080d41c0e400700c006202d422261600456203140c04da003d4029140e6808921404201c0c0f100306d070401c0301007510803164680109180401043c0c06060106071001448805000d2600e07051840d4011204550390141c240c5240b0000d0180000c2603030180306000041a040d80c03242540c2c2002e003030245000c009400a401000304100b0210304800b514812090b01c4003e50400203441c81180c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240367769 1250 240366519 240366547
    0xc0b0a150e01300203070b071509031202160c120203010e010903090e07020c030303160e040605091b0f0304050703021c0f020d0503071a011401030209030303040b2212082802 76
    0x5510b000390305d40600e44011540c0128440a030001c140142c601740306c04146a69500100d07952204003600003900c22070001044080f5800070412954108601110b03401180c0307a1001c01150764000c03800d9022240c10100a600d0700740030754000301c0c0c11940204900030355a42c000c0c1141065118201c0b80c2d14201d00041d050600900c422901040042d080d00da40380761000f240c2892681c81c1c0b4450011840c5c0b071000c8002402c0a00c00c2c9025500060861102510f41f020080c814600d42500c00b05000020040b510a000c280300c0618002ca224800030000a42540f04111009220032841444a400e0b820408081020859020021a01a900300040d0030590500600390b2250310301c0600002d142c3c456010218440203200c0d03040302d80a00c10700b00c013121450011020392050a0707509915500510218010512910301c80380c000d800c4110303902034030b410a1001110350601c41802d445082408503254083e5400ca00d540c3d50010b00903040701c110300d11000c0508254045a05283d0a00358081803480c044e56036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240369019 1250 240367769 240367859
    0x270b070207081203010e07020a05060f0c04181a0904050606010e0d0f030815190b03071110090c0f210327090f050903070f030c0b0a150e01 61
    0x31400f59841440c2c42000700c0c056030300138400c0076241215180014401032010403d0580719502c10080c10280e11003240800004a0150081ca40da80e8200000169503641d0303180030798020903000d800305010219140c1000b40c403400b003100c28003c40c036100c10000000d5002c665960300007400d0030042c0f1001444804100c01c1c040100005040e4076414003102d041c5a0041c802c40d00c501c03191400a402481480240706248105046011189030f200d4014040c1c26141030265901881c1d5207440c4036113030807180f1807620f08507407103600480e003554810000c0309000b040365484010f0000417000d030000d03600d00040f80078a18600b405074000700141c401880101445015505100030052030110380180e064020f40541c5861482000025444c2c002c00491701c01950003214403820034040503508004c841d031154458a8410f01c0102c00f0898103140c203100048180e01458002c00011000140c2080c1c0d04514040462044d04208114031000740104100c0c0402450200c41001101107005d072040c0c19a44d110303071240 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240370269 1250 240369019 240369029
    0x4050a0b0c030415020c03070f1b0b1b070515090409020303030a1a12120a05040308120a0b150a03090804080109050a05071e060c050c091504270b070207 67
    0x280003810700c003046403960055401140140d03002800400c0319003502040b4440c44804035120341003800110701241e003094651a0301e074020310380c080314006148800c281007100d0340c01000c500300b400700c0c025564011a0100754012100d082c01060618200f40000b04e10458400d8071072008980007925090a4a0700d800084c1016405012240c803401c0c02d12400d009064000344520045c040003691400700e150000c8900814520000605140c50740012010413580c4031456000511004201c000000344460000302a0b850800081ba5400d0070507400150130b8508680c0418880c4020180341c070060310009048940e01c1609050000d0203442502c0c08504900440d4010809035103006000001c2c42004116144818802c50a5440040c0ca511201050b40380c0e60090941c280d10345801448054060f046490100d80a84222038064050200140d019107007202c2c0d0100240401d0621282d6091034011200901190940c3c0700100710b050003e038041303044008000d0031440381c0b60b02090000e40240402000f0308 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240371519 1250 240370269 240370283
    0xf0602070e07051303080c010c03022104170d0c170f01140d0206030103061512150504150c0905040608010b01021009030c0b04080310090203060d1104150801140a0c1704050a 76
    0x51744c81c24182000c5c2c000c554400010b500f800340441d03800f4840e01c21103246020417040030748003803030f15003000c200041b0040007203c96546005402643c08014000342007421113071348000c02c103104640d500800140d00c0c250700100f005c84450901c486107c0303000400e41500c0a001002d0424001500020000083d00bc00650003550010000c000d20015802161992816400c1100155580d404050140c5211000079140040d00e003480e4240038180d402c92030b045030064030780c0f0303c0b00900b10340c0707507012a40300c0e00000c0302003000d00200b00180d007414014400140b001000030868007400c0c10020b5255121402a0b010495982442804050040b407801d401c060f049540c0000c94038041c507001800b0351050f01c080600b0050741000260250050085a10484001d4440801020a503450000e542c1e80190303050b5000e5111705602c0920b800c5100341c4d0780100207000c0040f40d005401400e900701e45d20050040c403c0141043c1d41420916082102d00b401d0b6400c0d4403d00c0519034407420320b6402c04040f03441c01052a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240372769 1250 240371519 240371557
    0xb0603040f2a1e27240603020909070201060609030803040c08120a030f0c120915050c18030c06040515130303030b030615010e06070201020304090f090b010f0602070e0705 75
    0x80084040000115001c00c195034030050788030f45002e60701c90b401860410500300300e005038112400751504684005ca19081e03200e014000f4802106650050030b400c0030000942c04640214030b46009500b00c0c6d0000d44500007000000c7c14508001c1201d512400050240e001c000082801c1118419010b00109003035001c1c2d030b0480e07080202d07840300c0b076114254135130020307091a0f581d4503820040c0c4981c1d0010f040580b1a045491451140c99000e4042a901540c194440f01c00746075200f0f0250082078861030040c0d07a001e9684150300c0e10a603204019042d100e01030385c82059059420b8640d801141e040c0c0d40300311051140001c0d4103081103410703c16108100f2424905000010030150150410600b40d441141692020f07a120054040f03c15854104c0c980058149401005c083c100000100540d90061050303e2a0a03160302406080d20703841642d5981c110350b00c144010900414a001d14050301c061076485901e1490404001c0d41c0d59581e0190070a150b43c0c030004201c80902071380c110307542e040c0d40f14094a2a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240374019 1250 240372769 240372779
    0x26010528080a0516060504090c021507022118010e0604080703030c0c17060114010903020d0b25020303060103021612082203021504051203010e010503010b0603040f2a 73
    0x9420002e5000ca40520071040c41071080c4000b40e1011056402e95078400d4140742c5400c21403005800c01041400079400b0380890b0100000714607011500c1081181c004011541c0c642c040761070007098180910240b00002d110084030f1440d58503002f0382c642800d2034591039901035000040d00e103209aa00024551250401c000100741d0402081c00c0068040e030608050190340e01241001d03400300011000494002c940140042c0d21400401c294044062401458254507a40072400345124010142c807041c48900420052400d05c07005c0255405440c4152410249800d101070b607280005006c05051603000f10380780340c80010942022600e2a0000f1001b200a029240302503c4800251080780080f000c0c0165440c04d00c0200800700072065140c2d005024992504030600e5030480007070021501c50098100c054601c000c0440a14068140086c0340e01655141c4070416007111401c145090003001c00707208120100e88002402901d541c0c1080d10118800510030002070319458038082da040150402c040420 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240375269 1250 240374019 240374023
    0xc0e09010b090c03130b1009020408100c0306051c150606031401060f0c151b0210060609031a09010b040218041404080f0f07020a1202012601052808 65
    0x3000071815103816005803241c58010249104c102d941c40161000200450001013220000340c1e4810780800e000c070800c0ea151759940059070301551003411154407400c14042c01003c20701c01c2d001c400120382001c1004502e80f0003c1a0a01149400c141179201011062401e02c0180700380307501c2c1e4032099841000b0164139420068010800034074500e4003409484004183c4030300541c98910a43d07110f4803010041001e661700e0551859403ca098100142c50720350303500c000294081958425400b1350003a0005c18000010201120400d52240d0304201e085401007010584410301641c1465250101c03200c02c1d40c90000240c00340c0026444903030031a100084010480040f0601045841d208460a02465411b0b00503408590001c2d140900111002c000081e0300f041011700501c1200c2602060794140a010340000b0801d006a0713200e843c1c62403000045000715a4080d089040c150800109254242c071900310907051034005024070b60065036001c2c3e0282d410320f00500d000c10b0320703032208a405142ca9111003d040e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240376519 1250 240375269 240375281
    0x12011e0207110f0a09090f06050103030c15021201090e0319030e190b2d0a0c08070f1d03010f020304060c020d0c110108060d050f060601020601050a0b03060402070c0e0901 75
    0x642d004840e5600d200c224900040d40302442c1900400c00c940c01d5003402a04030003005500001c42e000a04c0c00ba4040009605014140c02180a80c4510b04c42ca440f07420304000141380c0c140310068452041002c01645059555082e05641702c2c62400a02500610b02442c90341c8034180c007040d440c003401d014009100780d050b00145610000700c0c00f03803000d040300c03214620a4550740d074000400c1401c805000400d104400e081000702d80e181455a50440c486404a0005003401582e911440f1130705d83d11117948494114400c150030801030300d01020f10003150000100b50702180d100d6041900f071802c10600841c0c0d025045002c08030800b52003156a82030a203810300040010780901400b60040c66a03060b02c0a00803514401640e0300039801e0308080000000455a28800420071030784046580314500202d41c0c00c01c00c910010003c200145030347e040c24000a445c01c501640424410130a07814140003c4243c8026250084002c2d100544c58000c90700d0703c0d58403112140c000040414081c0100004190150052 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240377769 1250 240376519 240376523
    0x50a1704230f0a0803030109090c0b0f0d140403230c120d0c0e0901090203041e12031d030703080a02210406050615030f0403020c0a0f0f0509100512011e0207 69
    0x18001c2c182d50307200b4001c0b0441d40384078042850300244010020104070340c11030700496110761401800c89449101d24442c503084000140705c092400300b241000010203209000c40c0c2c0e21001054002803130305660060401c030782c072a507a0401140d10003050058803040c40540e12050704000581d00305800901310040c0b0754004200ca11080ea06140c100d8000e00e000352110324036001c000c0c0192607a0703820010a00040d61001e00200d0303a1841d114408002d40c1c14034119040300d6407241e40e609200074540c00f401401d880307041c1c081c0c01440c40c0380d0f401c0e411401000021582400d6040c10704201d42d5983d800d54100038091800942030403915202072074028498106294492485070301c0400c01034070f42e04140401c1d07407d0814a034170000803c0000c40d40700309a0860407a40031f8842c0c4103c5041854541c04101e0101c41c9030301106800b101a0300c140301c485141c0b100da5001c0c0506583ea43d5940c034220460340d00e03660390391041c5400345044c1105141c2d403d00a400c100291801084d60001d0400c800810b00c1c020760045000b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240379019 1250 240377769 240377779
    0xf170610060801030f050322030b061509011101060305070306021b0304050d110d0218090d0e03030d0b0d060c02030a200c09100e0103110301050c0304050a170423 71
    0x944940d54580c0c003081601c803955149038141e030840e90351621907440070400350b50f207100030700850f55149008d40c0101d0090044100c010350b0180b1b54a0441c0c502d11020b494140300380516102060034101d02400c1d1540c150302403808402441c14401205c0c01031040f0741002e04240500040401400015002000481c030088040c04001c031042105a807280070f40d0244a500c80410384014010440014000c0d5804100501d82c15880d081a80040e00905940354420192000300040281028051003041581240340c10420039040c080b00000e81c40b032041c1c015003090242e8a5068800e0364540040111140c0e620000c200542070384254065a242c111103001000a0100c105040e1580c92070b400030520300314008000d03c0c1c03e85025080041c3c5802c001c240101d00c0702441c0000070b88660009050b030003180161910075020b00c405040c1800e4500040540703003400400c0080c00002800040c00d00d0b039180d000700c40060a60911025800140300726481140e503d442642010356240d040c0410322000001222 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240380269 1250 240379019 240379021
    0xb090a050307081207150504050a030e010c020d0215160f021903031d0112140f100e0a020a1803060507020609120906090a03020607030504030309080106050a03110a0f1706 75
    0x1c040e690b0402d4001c00006801030414034013410010320180803000d10544e440410741e20340b03494a100f04c5800f10707800da61561041d00c040c406e040e0441c83c0c40d0340740c01c821718181714803a0300c41d004503030b021002d032030000d00071100030f54040401d200304020f541026035001c201d4120f2564500b03000381240444102030780b10301d200c81c0303030600900345500c860821258513458241043c0c1e4141e0060400101610380c3c00e051003800001c91a001d0300c1032013000c0b40081080c880c01d101c2e0a0020b000485080014900319850304080c0052201603241034003160300c14150740c0e01681e1078807021802c4070210002a0a068090f018903804000c11400e40c100510030a440c2d8200ea11903914008000d40d1528102c51890000c2000c000003203850134110000c01d00080b02134000c4954582e2a400305a05612024080d00001e03004a8140b08150b40050b102006142000c000d2000b40d08100c001a003441c454030008184600110901601e502c8281ca80c0c401080940a4260030315940ca801c20b07070b031011420040246010b104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240381519 1250 240380269 240380279
    0x50d0c15020613020d020d0506090313170c0d030909020f0304060b01030912030b06041a0c0609010902060921010c09080f070e07050c030408070603060510030507360b090a 75
    0x480d280316400c1c640148815030142c0c4c09010711030500c86400e9800407065030851020400820041b03005d0700a41004503601d04450903465a8207103140c10251524000791201045600e00013032030007076001e0458042e100e1030158a015146125190302c258034040c004540c41c08842d5042c409580728502500050004c6081c000044040720303202000102039612a0f0074400d003003480782d800840c00c24405040c0900d80790311400c2c0d03210000b14800c910747d103d490000355070074088014801c0c0758004c3c6811009210b03c090b5540024a240a000501e40c05014104100032040c038416001c240d84456400c020088840280f00c020103500c0342d4002c41c041ba100e82652184940d0001805404440d49000d1f5244651266034044501d035101040900b0030744402d00010403500001c1c4441c000600250310300040c55481c00c1d084c016440101c080c800c1c01e061a00040003042034014014211003240c21110312102c0d8041c680301c02c00c0a05e04134210850900020f17020a080351010003c2250140486030400031958803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240382769 1250 240381519 240381523
    0x50405010f1a0904080f0f030906010f060206010e150f060c06040b0105181302040207080307020607021c05090111070f081b040618180f030e0103140907050118050d0c1502 75
    0x1481106800100d0440000c0100ba030417005000552001c842d4140f8002400c4862101e44c0c01c2518101e2031504941d004200710084150907100424450029040c01d40c904076a14100c404001c0c041421303a14110129805681c0700d03001c8200c83e0100070400340d01c44140e040103a6446e00110f03022290030030850000304207486c00f02026100300500c00c0c107003403c99070350924400f242006014100e800a17008c6c400c08002803202c48c0514841d84a41c0d0040c981032401001c000d20b400000c544000312184a05006030030254400c0440c2c030030f075400b82030030180d004580d03c40d00d28100f150792200b03e44d001c091002042c07124000c25803043e420f100003c0d05000302140d0b410403048480324801c41c2c4240c0904a1200111081a00b0245c1c5810405012034030448003611100c40c8a283e12001700c00180e055502c2039025a01489070900a01c15401100c02c546007450000396980c00301c1c06001d0510919180c4528041c2c51280000081c18003d0400b8602ca02c603442c0409070500580156400c8070204805131760350500c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240384019 1250 240382769 240382811
    0xb150415120513080f0f0301170607030b131a03030c030c120405031504080c010912120605012003040f0605032203050301030303020f0d110a0e01020f2e050405010f 72
    0xf000c203c62801d0030156481c42c0b07240d813003a4010314038100180020345880003168043d40c001c110303403000040038041d4190703c0d5040540081440041c1841c0004580032511503800807507100c000d00380001080c0b41350f030801e414000e0084a0701940340c80000f504100311200031001d407200343c42840840d0000680c818203400d4501590240c40d415500415540f003104400c01c0c032594019018444142c54103207003d2403542501c4000100f91000c43c0c01500c0c0004080d0b02c44080034160340318450030070403242880c0c002440022007850740c03480da000000004140010134000c80e130003800b16001c0303182090f0391030b40080c0a0390422100d0502c85070403401000c0b0f10b00c55519024090640c181d980d540f0310f82c255070b0b007640207400828070b105103410180001d4940450503c00c0846461820395200e4030380c0c0880c07100070094144101079504641103402c040f040c0040c005100300c2c07064010308801d0380f400f41c6148451401d42c402c0500f01c60403030030041403000340241940b1070401c44000314014040e0701e114001d04190454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240385269 1250 240384019 240384031
    0x1020d060b0910031d030705071401050702030a0206030c220e010503030304050303130303062706050d0b06040b0d020d11090130020a0f0915050301050603030d0b1504151205 76
    0x42d01030860348009100303900803000c05120030020320703000c2d403130b174000600e1604065811644c40d407101070280704d079499040300d0044160302440c02602d45660384e170201c1c1d12408002402401404040041501c61079210300b502c4040d14058468200e84002038150b844000741032090300382c0011004004255810f012003124821504080114510b485280140c072001144010607000c1541e00c1002145519880030502c1d0444c80003071205840d203558242d14411110325a210521907a6102200d400040880112650041c01120001800c0001da004500010074002c4001d5120ba0031486500c100b05404409003080401540c09801d16a00c410300020b402410300e00c1240e20107003518100207815812042e107020144090551460a580c510b800c20b042809500070814541d06c1d801d0305038001014003d920020704084001303101500b070050101c2e403644522808070322041e8035150b80e0300254554080b01c801c44002c04180654582c3e0710f24422404486429250002801d803003070381ca00d00c44035070107001d0042c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240386519 1250 240385269 240385279
    0x30309070608040c03021f030e01060501120b061207021b01080106090509090a05070920090a1802090306072c0913030908010203090d080709060504030206090f0d0501020d060b09 78
    0x5030070500241c0d0352580060003201c400b10461004801a22a404100302ea2000110002e2002034100405403c0c0c80d502c000c2e141c0207a03d4801c0801c1a030780e212074400c50011b403a1000084422490020502c184108000400e07140c2200043c442c40139800184107440491440d8001c451107020001164490401e21646c400a00d50050600880c43d106180035040302c4490103d0b0b03020b070001d9541d0b6080c0183d6501141c00c95641d40d0250084400440c3c18500c0c0f101d200142d1842c1c000b4200005e40d0341031140c02051141504070740780e124182e101e40e04036404040d0040413a4030500d03200500a00c00500b030000318000b581007410812256195103100c400165006080702c03e15a241d01c1021600f2902d0b034815030030040201d0b40018001820310041d800b460b4050058503c41caa0400064640e10024100604011000344100075083c0e205040e20107a0782d04403070007956071003200e0020780b8009003003d2142d4810210f400510410505500038035804a0541d030510126681e07624a01c00303406000c100355080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240387769 1250 240386519 240386533
    0xe0603061b07020306010f061b08031605040305060c030604060806100302040509030928060f090b09040b1c060e241b070309060305061c02090408090d060b12030309 72
    0x41c40d20760364080503452514030490802540750006072801400703910190503a140c00f1010b00140340d110684242d159002040c0b00b41c030240c660380305407092100074140d51412002c203500c854454455022140119005007c0740e19034102490101496070041e25400d102e41e103020700008020304013080c524401c0d03c600110059807443d607000c0c030002c0c01c401803007040d00340020061048140d8036542001034040d0400c8500e124401941000f182482094006600b40000f12607400308580d4841c2110003510000d0131542d448120800c04500681300d0420511740c0854003030009c0b880c0001d040c21004419000702c1e024440704a001c1c131004d03190500a040000c1d00c2c0032181000000d00150b045164115506080820000f404503a440515811002c8210300183e52200c08002d480e86c18010182c100030304490601c0e01c02010800c5040310002803100070300a00601001030103001070101900c1c00850040e1940c07400400915003000200310b40742045105814000e9135003c21480002524818641c4034028106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240389019 1250 240387769 240387781
    0x12140d0e0117040305160506091e19081908150609010c02010e0d060612030801050103060605190905030304180f0c08041401020c010c050c0c1f0f050409020a05130e060306 75
    0xb60300b00040090307041c8842004403190100040800420450242005e0070413828004016424a003103120848500240c28a5203c1403e902240318200d0107034100e03201c0041e1045240851207806810306860600030b44000e11015250011005885191140e00c05d1025910b04030410500d40217614006000805003420640154016a11058200f10042c40d46404200705ea807920b09440d050303041000d5050788001c114081603000700c0002d0140c2030900703050000900b4500028500e0140c580c41310704c5c0380f070f40c000b070701042c640035008180142002030213880e640c50f21030341040c0c1c1d003003c1e200020703a0a42c41e00c02c00c002d103401d8510600d622205540d0b103200c256255a110300c000e0302c0920703a60416039582000b1041000000f44101400102c00da1506912469128034a504041c51104018016076260b2900001d071280e4403012910002c01d405d0070f414030450090210380c01e000c0c40d00010705080c8005603801c0303040c2e000400740503102c042c140d80ca4000c82e16403514961002c01618415059400000401c2d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240390269 1250 240389019 240389057
    0x1401020a21050c180d120302071a0403050304151d03030907080c06090105090621040212010c14031f030b0f10080a020f010e091f06021b1912140d0e01 66
    0x251340e0f1000b000614400821385800c11000300b40007010700461360000f030703134000c0200101021140d22120507503511245020380f0080e10f10b02c03000304000c2079280300814090f088110396100c010302d09042d241d0703e030b00400744601c5c503540e81c2e00560b409451403154140001e001c2a00203003580706040c02505050810804800642d2903030000340e2282d50001c41230180c92020f944070000d00b103440e02d2100c11f460160900d4014070a460002d10315141459040c24039400e11280c0110641c080c5803242c0c20213595964070900f112216264203140c19098506283c400814406140d00c0388e03006041e00b081c9581561600e11241d40f04011920070031b2190b030081c022900c0503190442c2a100c1c0d8041c103040c401220380b11140060145a0201c2e0b200d501c150304c0300000600504407901c06c10180000303000518803003412025022829885141152003481d181c12160901041c09100340c006000e2a0b6091044900900c1d04501a0a803450580814402c084201002900c50480c000002d901a1119600c40c0c005e8001c2d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240391519 1250 240390269 240390307
    0x3070e090304081c0e011412040c080a03080906061c0b04060b0a060c0512090d02090924010e0708040f062c010e160f121401020a21050c 60
    0x44001d000034007000030640020b01200344070400d0200021981050450050b010b4248050041c0c1041702408038540d0612010741203aa82d01e0722a16012000d5031103217440400203520340c00905003805145e200310101038000080d5401400c021040e82c29560310481441041c10307a0500b00980d105000c60403001050b1074910440d0064091140410941c11510102e8400318840c4d00141c001040c0c1100b040030b22105200390210171410030311407880d1149001c005145074400e024082d106e0300c4490702280b5400010003403030f07000b000017928034440b80399281d10130203500d4400d100705082004158006400b627442242c1040c0700d158810910319410381130b521071000500003107208124400031804141c0407078442031030b414603e1174880700200f840d115010b50a030806c409400b48a40c5400c0b4241d06114410510494805030741c074a810074540c2642c28205402e0b40551201d10300c01c15480003501c44c080c2c0b903210010840e144001100404000300d403a200390301710342080300c0b5840d05010500c040c6c030342e140704540a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240392769 1250 240391519 240391531
    0x13050103180b16030603051b270c0a030204030c120203070b090303030a050411091906050303090d0201030b22140c090f040b0612100911040e0106120603080c010c020f010b03070e 78
    0x140c666142d5690a1900010300304039041203050100c840c81d50f1030720180c0c1c4427000c2c0600e0034000803403001001c0012143c00140c5036850007030010403003440c0c061007076050ba4015500621004c0244d9a0b0758040c03240e081d000a0268000c1c080c1c00c4000c2009900e00307045808007000500118510798840072014010900904101c1c1c00d4401c0210005103a074402903007900441d282d00d91405c2c1803074003640c00c0d0b0450b10b00d03a03c80d5010360402c3c08804e9659550300b400c0c1a007181c080c200416510b54a4000603032000c4000038a074803904070b20030803030307140281383d03111a040000040e03403444644c03203464440c2d0442c05500001540300684521190080c00c042d00701d50105100a41b06070300b420110038040780071328000c5465a8000c007610500300718400d82406910000020140c0c5145020b0412035600c481c8603050140c3c1e0240900410b9200d1000c031181c1c0458021030300140820340b1440f044140a0290100d410402c00610812114503410841031240d8095460000c00621540349032508000d4405401484 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240394019 1250 240392769 240392771
    0x13060207020303070b060307060c030504090515031b0108060603270120130b04030804030b060120011e0501050604030b0a0b0303070b040c09060b030601030f06080313050103180b1603 80
    0x800340042e103040001e030800c10310550321003009203802000d251402e82194020001c0007100c04c00400441d0b00201110140c80500f480828582d071080c2e044507501b1103181d9a01d802d88105041ca803800710056030000017412013640c803d990760b2102c0007040501d000580d8a000302d4404803030f200ca900e81c11a02040b500d030000500118a83c0350300c10004124019246045031070341c1001071308030f102211051400c0d0140080070401c505103415074440e60024001c43c003009045c0d407105008159968001d52480b40c0c004210381e4407903503224964042e14003030f00c2c50044441003003001b51000c4068450070302505042e542d010f061107003400e01c1c6845c0c403050710034040e1002c031010390343e003069403000c4e1018030040091074041c6001b1503850902d482c01d00900b5005a2000420318501202440305c0d003100401c403074104000740380100d00780128444060043c0001c1e030208040d4030000603a0310824900801580885100362002c0020159158842007000f691110040c442d00089c0001104208103c20442d00601d1074a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240395269 1250 240394019 240394027
    0x10906020a030b181501050721030608060708070f27030c03031706030a0209072c0103060902040b070209071103030109020720010f050a1202120702071d130602 70
    0x220081264402000c0100103a00c40348001c12505003407201326040c0107000103040c02417030905450001c00038030710401c5040050001e0510144000b0b1181b2040740072070300180e60b04615010b80058000c007034030310842c0600d001c0c4500041d10140250062407040700b9a48030030340a1108088111482100001098a100034013041c00584415000804010b148a14407507a000b03411414054040700710900b0342041e50b00c40008200b0103032004030b074289140c3e074160380482881d00c600303d068a000403500303100003180400040350010030011a5850280200c01e03201044119119040703001a1310482c01140300681c004c100910044c180008029808001482d040c0001820045405d0459000b0303072141c0000c039004951401480034244026400e006c1245c880c25a00070b1000019240078a141a40001d0200100317a00a42e180621516404d40320203035802c55032002c40746c0010210240a48140d001807080d0440821a010304408580d0044c11030f8a40304a0744d031f943c142e400c810314010340048840e15002c1c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240396519 1250 240395269 240395273
    0x120f030409060611060121030e04050f040201030e0a0201320711101d09150a270507051803010b0d150e0705150c1c080a060b030114040902030109 64
    0x880a04090076407100c000c00c50302d16020004280c4600810420340582052004110020314041e0002d0b100d00d0350140741008000509091b0303074440002c64a1074001d41400100240311200b03c101c0c80c41180300740c0b01001221003140c0d12641e01c082020009000c5041b0720201c0440c000b030500c10840b0b0144280c410340c2c500c80c080303c204070a9000743d04115030b44044c03001c650201d8502280410003e4010382f5180b01001044500c0b211b0040c2107015660250341321401107003810311000301e00d03401c03844050942a00365541e01031a207442c0503180e0301e204600280c01d0701d0b003501ca04a40250383c010031035507592506110003900072404014103162425030666940c8500c40c0030382c540b22507032280603008400046074602c40384800e00c2950740c070040307204442d000f5210a00c225600c1b2440c4002040d040410f081c0c0701c801880f8103616000141030355048445c011608580a982c2c071142c1d80f4072034480102d060010340cde030310300307072404540801c0c010204441c45c2c2184c00781042c1459031001410500080000c21516072503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240397769 1250 240396519 240396523
    0xd03030209030a0f12021504030e06070201030b06370807110c03010c0801062712020a0b0f190306050904080a02101a120f07050906060f0a08061e030c120f 68
    0x1200101c1e00c5e401d0561200c4290f5406002c914103a07444540040114545a0790003082e00300b40c440da4500c101c0c4045804000d69220794040c40300c0260182490380c2d111020140c511322444041034030000d04ea140400020301c0c4414000c000005649600c5608441e121004250703807007103594422001d1403188455900030795809005641d4540440e071107003152035050a5000700700805040541c0e400b803004c120000c11014110305800101e50503148090356180991000503094051035025018100012a40700c440e11809070040806039000c004c62011640c580001f60107035106445110303400503e2800180124090b40c006082c02007444c41604c15005407200034000b10703041220107e0030040c41c2142105182010049200075401d8440145400001c000321141c2d02d00c23050013503d000358510f07c0402c100c2c1c1c07100015900001004200d07203865a050b090700400198080390020f1140343c01c01d99403005d41002c0440303040b809101502030402d522500d01403158a141640c82c0a07540d200d4584404070784001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240399019 1250 240397769 240397793
    0xc0b011710020f2802060a0f020c030706020405040510030c18090203030c1f020f03190e1b0405060d020f0111100c0c060c020106120f0606050603040308090111090d03030209030a 78
    0x8003d606070700c5285020650684110840110806000758601c0815094001907142e51003000c80b9800b040d96010a28034502034001c5461240e914030000c1441c000b000090f030050030581e45c4c145d40c03c10040e075600c444039030760140901c0f0180c0f803a9220801071003101c6410303000f07840b250340c00c200100c0d03c0d03516035000c40c0c5181d0004c24040c1040c0c010010b80d920320482100790702112444401c0c254200880c410042e40030740b0001e0a504000190311010b41d10107400c80d0031000c0e40042d203005a4a101c204680040400022545800c1c072403840c0c240000e40c28608080329415168026125805d041c0c03070140150380e0041d203c0303003800d035601c00c3d48000f240243c003500501203d604c184c0e98032000e07580e0b0343c5481400e5480440e014801d44e41050340611610610500fa80c20940e00b201c054059001e45003403460040581307401150f00301d0740c0001040103041d0800e01484c09150188020014424450304c0c04c04140928041c03160710808840742e041c0400d20a8001e004c600c83d00030241c8160240716070ba4014039400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240400269 1250 240399019 240399037
    0x20732060403140616020d0e03100c0809101a09070309050d0e1503130b190516020d0908030d09060605030d11100b090705180a03060b100c0b01171002 66
    0x10000c000380d44500003404545d4206264402400a80d2181d440207502c4401d611035010030085483d0600d040340d1780800607c1021880340b6420820140070b41d0300240105801c440c8a02e10b441a096160822000c1e44103040806540f803801c0402a41d107101000343c1607002400000800d80c03208400f101140381404070501b010020348440d0850610380c1c09011103002e22180503a8020010300401141c903a41e6440c0c400041d5004501c00d003d91350314184142072600403c1060400da01d05010800305510800c002080d21441d9000c031400c40e07090380b42c2150010814058404c0c503400600441804000c0b6400c0700044601c620310100360b10351100c000c00c0c68100c1400364440013544104080c16802c8c4144001c1c0b050b0755490909001c2e03044418003180403024060244010801d0009030712401018045564400c020003d028162595803810810084c105c50f06100344100c02d1310b903060f4940c034010b041d00c030340290b404914080d07141e10300030401480d0445001043c0c980e0181038007511000e540d81c401000c00318 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240401519 1250 240400269 240400283
    0xa11011b0201050709060c0506060607021309050a02121c0e0d023303040b15060d1802090703060509060d260c0601090e0a02090702010e0703080301031101020732060403 74
    0x440c200c20000c240c0310ba01d522000a00000a1f61000411004106075078010800d440d003c2d50344500748003161046802c0e6405000300c1c1d2a11a80c03404125012070104100d5000712040d00040c5c1300e0300707400c81e00d50104058118a0b48011014244114083d505900300d200004000764140c501e143c000c10b8902400e4002e0303945024003070f41c56500b40070320408051980c54081181a0551078231795101030f01c061000c0d00c4580900c00108118006565145c100d031468140c82a0a000312920781c0031b0600250303d807c1c4124032130202640020502440f900c54402220303030040080c212500c900d02171101481401000343c50600600c802c0c2a680030400a95449818100407116516030209030030310305007041a00120a010b0030210200900800010040201501192040240c0c3c03a20b46c0700b0382c010b02250404200c40c0c041c000001042c000344402550490b801032034003140c0300305050012030300c50440e4010b1400780da0002c03003070101d0511020418548070002001071144203200340700042064001e0b500c211010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240402769 1250 240401519 240401521
    0xa02040c02102c07030314180604090219050309070512100203070f0e0906060304151d030a031508071707050901090603140607120b04020f03040308060102061b0a11011b020105 77
    0x110224800d8003c0385240e0102030450380c4e0841c1c0d0018042080300d0049808448042130b110314041041074902d208244c0180090f6030360741d0fa440319102a4001140181440440b080040c00241c003e0003260300c22800b8030040c104090401040160000465003100b040d4480d107819421000e4091004600031005911030f500e0416400070f00408031040e4112030b601500568050140585800d000c1c1e1b41c1041c0c4c00825440050000c002800041c820b1101400035103d00d42c1040300d038a070000c00244a26030320340c1d906004966444105450059692140101ea80d104040410a0400e101c1d012158100c070bd20585143d140e44600160b940c0000b82c20108000756503000410410440f03104280003282084040c04061030902c40207072145ea4520845003899484806034012a9169411a01c8032069940d1f996140c1c07c00d401d004046100848030f07540940704010108011651030402c00344140c16443c0c0d00c52800e140411304503131015080740c882c02d00d592914800a150104000300300704402d9203500010305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240404019 1250 240402769 240402821
    0x240304030216170709050403050904140a0f020405030712020612040b06100f09050f0a0f090f0b011407080d180b090c0105040b1209030909010f0603060b0a020a02040c0210 75
    0x8001c00e5900803800180e04282d081c4105802248513412035a1941000030f81d035480e8141a01c45102d40001c040d481807500120381c6449002250580c09414a14000c09c131840c040c4005008030301c02d5014141c0c1c55401a4020440019000000b400c014406441581098488a0101204802900c2c1203802140c01020001c8600301340303d1070002e2508514020301c0c0008240d00140c0031941318000c1314012500c54025020340d8692106140c010000710000c0d492503a9202c00300c00040146c040b02d4403886041a5a054244d0300c1011070050490000400b6403410102c0c1e0b4a04000340d1104c1031860b940e03511511070715090351b03450660441e4140601c03010a4145807809c981d5003481d00203c102418860144018800180c1190644810310f4586400752425115540d184d0b10710b00540150a44c400d40038400070a900746003609120440b4016201400801d0301d9440c030480310301a5445100051384044842c001520782500140740300450b1f0700595003108401c50701d2400f40c034440300c60b0844180d280034081c1c103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240405269 1250 240404019 240404053
    0x501030210030b0d020111012004030203010b060705060a0216060218040b03240c040510090608060402040e040602160b0a060303110607020a1716030306030209150901052403040302 79
    0x30703a01540d8681004803d0443e00003901010380701ca4080e04101c03800340c1d1a500b01d2000d62000501004842e01c81e6003010901c0039100d440e60050104a011b9428445c5c80c1070381e424503a080e60b001c01c0c0d00c503015002c1d940d2260001e230300940224240c42c044c0d1880941d2030000c01e0051006050101203080c11401100010301840151352213075401d035020340c5c408280e01c04280c0c0380a01110582c2c07117071081c00809440c2c500301c0c4046c0d40926000702d41e100490710150300c11150401e40090440d0f010340c6408901e50340c0c03c410003017203000714840c82c070030740000c400021f0000341194021b00042da80b03540d60103142d2444d80c031019030880c0304480d490b030201d589035400d0042c1a040179829520b01c1c00c07034009001074903252070000d44a06d1034042c0103240c503440c1002c40f800d0480e140c0a4800101507128000f18912403401d000f000342c1110301c401d80c010324034000031807107648120300000c0b490a8041c100a56030b905e071105100012040900500c0400002041e03c6011200240110b02681c020b6001b0200c15400200c204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240406519 1250 240405269 240405289
    0x603010b030f09070e0a1e05150108010e010602030d0209010c0c0603050a060506071a0403020f03160b0a021303150908031005031213030314160501050a050903070308010909020105040803070605010302 88
    0x78203d607116900420482c007840c071000b076112101c03000201e001180e040c400c81c4041100c40c40e00c503140341040104241244101c0300103802e8442641c07040c0da00e9999441011120340d080c0202c8006070801c1040300c094440c103030010409080107250003001420380d078481044088194200c00f0029440760180525185036001d801c0240404850881c50282c513907440e00c0e04e000c0c0200a00a01d8445d42000500381402481041c506056141c1540c0c0c1d19007a04038125024001d040341264060095008203003005006d20990b00c100b00440f100451560458407851180c0503440034010b100c40c1c4541c94403000603a410069130003010710318004e804082c1008205424010041003142c1041c0040c42503501400c00925000202c2e905800c058002240d03041500d1080c0c4111070003a014070195000e04010480154801440b1b00002081004541c4500d10419128416020060000b80c1031078018400941039610840d2000d02c14180f41e0328050740e90885e03d085421a4074291412943d5400400c20f508004100c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240407769 1250 240406519 240406531
    0x80106060f020705150423100c05060a1d010e030705070b07021302091507080c070803030702031c150308071104061d15030102041202010e1206060111010603020603010b030f 76
    0x980680940d410082d9034010f40d100d864030034404070300c2103401126044129030250526840c1c01c8250104c0100c1c5120080603030404602031002840d6650782148155111042107520001030f101c02e0300c650b02070304060305112070002c080140102000056400c01d12400c80b80c60f4210020b180c0f1002c55090072400c0031810b1f8401031241320100f0050005a640d08070b40d00c441401c40340016103942c031388004119141280760071a012844001200014001c101000d0003041950500310352403151100b035641c0c5c4900060791351001503402400119246180c0d140d41249021240c00001040c80081c4906001d844166109550381e41000030110140300c8489035400c6c1103a000e94040c0400ea290059050b40c581c0914041d00c1010001c5000c07540d140e0302c01c03040301410b1000400943d2500e880b4811003110f0090901c040b4049420750301641200d0a281c891280300d00840c0000d00410b030307035000065800100c03d1442c6600f41d5a50f0402100681d6280c000c4e45c0a80b2000341c0d219107070715012080312002c041c05024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240409019 1250 240407769 240407777
    0x70609090e0304150c0503180319080f0d0b0d06060e0708010518040302190b090705030a0b0a1812032c06041205120a05091504052e021308010606 64
    0x12400072990000200c404541d4410b0300b480c8a6849000120350503040a40c0041c101e010010b000c507007810380701000010a4100324141c0700480c1c6d01004040e200300c0b842d44010407101003400800e0320503540302c02074200800c4010010410080680000c0d42044140a0132503000b55161414003d41c0c003030780044c41e400402410446c1036541844001800f520303000b50500c601c20a0040001d04041c800d00140070015040c3c8441804500540343c4003c0c9c846084444a2661142d180000340614000a104a82c5074002c852030b9566112910720801078110703900d4a4402c01e041010301c100044240e9207903800780700c0694000070b0301c12400c0d0606000d268107402d004220b1441e000400025400031941640042d07104d51521030713915200b40150382c203024810b40d8144032800d07881000101b004c40c3d04010701c00c078800820b82e0084150841800c400c1392043d6005000380d84500c00d904d10510444624244403402c0039a00d280400c100312580040c2e038031001440142101040003000200c8003402184050405810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240410269 1250 240409019 240409031
    0xa0b0114130e100b10120203040305090405090f0f030406080f0606070512030a05010f051e0111011811040227030c0d060911010908190f0206030106020703140102040b070303090302070e070207060909 87
    0x5c1c01001d42c00c0040e0700000c003079400400300c0d08146c0607000b00c17840205c0290040c080c5e4a4604400c030746901d0740741c0b00782040c2d0080700e856884480022080394140d40c8144c035000c0350341d207441444600700b9000600c29030300102c08008a00c0811010441d1041201c807090400f5542d20380305056000b80d0f20180d01c00c000700c110041c0244515510114411002482c0101a090b40c01a200049510310450182c2c200780d5480d1070115a5130303c03c0003001841803805800304203c45070400061000328407451403450a060b06c0a2507100c81c0d20006180e40311008001812035546030304000c0001d20b1030b2040401210a0b90b50341803001304000d20700031100103c0c03400f428141d0f13600e89400066038440d000a0220501e241d8144500c1d0f081092001508001c940c02030845512982c640030080d644d082d89000c20b460030800010b510841080500846080e5003c203840f960400246903000e030054026170000310300b54040c0c0c503004030b841100c4404240c410901760f40280381152600c0fa01400f040942c0e00010000ca003012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240411519 1250 240410269 240410299
    0x6020d0c1e14120a1209061b03090c05060414100909050a0603120804020303180303070501050103060e250e07030914030406110105090606240c0a030306080a0b0114130e100b 76
    0x5104078004003c08074002c18480307003902d081c00048c000e003c0c540074030031561885030004a51551008a400b4817032040355070401d4481c0b003001440c0c0220722078407400344401190800c003403c0c0b44200d40e1a144490a007000616103035504001524011500c0d104d00b2a0740d4041001401040240031500041c64140b8400c42d09058011944a101c6c0b4565040c0c0303038101e0003045100e62410401c03904403580240003041035503141c1c034000c1e0242c04060340c681034074819654810070322002028405120304a5000c00c49955141c0141a209144000c00c02e00c2416554104540841c2c00032408003200700c07807107001e103a6407810030002a12010001c1c4080400381e15080c1000000e0700300203403050308520100d8071508488103503407040d4600307025150749501003400801c522a85000004a03001d589100780c80611440345c40b61030302e0f69038401ca8175000e4040101040100081903426545201c4040c02810805030354404403044419160b80d000d0420059001c0d10940044412600ca000389a400803582c130326003180d01c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240412769 1250 240411519 240411527
    0x30a08010e060a0e090a140d1403130b060607120906020615030a0602030402031204090c17150d0618050c13020f04150e18100f06020d0c1e14120a 64
    0x2800707113107141407150300812211002000180b010710741c80140d41c094058500280c5441d6410355250a01140d04040303003448804044054030300c100c00c0c00e0100144840300d5151a140c8402c003821450700000100071000102e0392001c203050f1030315100d4440700082880d24800030700d0100c0050410311046200c401e01c0040740d40c08904250203d030080700140c0c4070348860002905100703106550802c03e2500050000d502c19184e0413040003107041c0d4403022214140d41525141c41c960413542e00390903000c880b07444803491405460512141c0d0082000003040d02644000120302c41408006175403541c080b01310300483d032424103021081810341031410b43c2010a4242810b172180645e010f04490600f5098245000394450082c91098490003042502c2c50701102c1103622100400381c8103088240c4509101003405184440424205c07500340d0300401c4c2c16010180e003200c0d00b0000d444125013815040c440080b9181801d400412900c0c043e00c007494403003d001d07400518101e007a2680c51105007040c80b00e85001508 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240414019 1250 240412769 240412789
    0x109030212032811040806010f0501020109020a050118080706021b12030702090c07020a0308070b130309050d0303020705160f0801110306120f1b180906010317040e09030a08010e06 79
    0x104650a04006121030116009013040c101c50b088840004140040c40520015100d03040b40d2009040c5c48600d92120012400d031404200080e41200c0f40a404000f1944610803041c141a80d1102c0c0d0f00a498a4041260400e0025445800141d0280c0000d0900c11162007041000700c0d01100c031b6082741d0840805454030fa0003010400380c40f52005030000303180210160110303501194020308070308405440c3d20b06900503801083d0b046d44e0840c180390000720300c15010622403485a4042c1c0300c518040e0701d00070410182c3c21000c50120200354090000344005882000035071f9018042c0303070180d1216401e1030140309022001e0391298805070b040154590100c00004200ca411038010780d030583c00e032580a05154500b41001c2c10038882481401e040303c81207807800c031100c404034604465200b98400308000c01e03203508030107560201c9190051001080004d03094890303181d100107040c1d80981055030b81d0002c452200d10451f6103a003503800015039000c2c0d80d03a10421541c0980201e254112860600c08080781c1f00000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240415269 1250 240414019 240414061
    0x503040b011502030717071a060d0212150a090b090318040f09080304030c0c1403070e0907030c1805010911030a0c030e030a09090606031404030503060d1202010903021203 75
    0x1c1c003001a10700c443c824002c450495822440300000030300c89102409090344265010b0f0780c4881d500e001e20405511004155024003401848110700a409408211100c0c40514020582d48680120783e28144110758aa038468440e800c000220040c09003404512900002c103541c01381d030001c1203000750301c03a0b0009034840504810345000668522001945000340071940010700440e60220801003015803000540c0c410350320031032454000550347c8085030450076800c0a410b0b49500468014041c2400d81200b40340c2c054110030480d03842568980b00c40c050201550442c01c244070281c0400983c00c50240070f402e004014002d0300308001e5034040f040070b21a00000d401004c00b1130f1244400f80c0072034400d410090492918105803680d034500300e030002e8401e1503680708031083c0e40d08001d400104d5501070700c00d00c288a01820b4070428655510b03070342242c0c00d078001001c03140d0100c1d04201010201c0e6200a02ca00204456000040d440800c0d02340a450960100e00d1502150020010001c4d0454030a0341c2810700d00c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240416519 1250 240415269 240415289
    0x32912010510140a180e010e070b041e0308040303080114030d0804080d0609050703020912010e0703020d0602041a0309011503120c0314030a0c12110f0306031c1e0503040b01 76
    0x9140f10b400107055084aa20444d01090056580710000c10b490f0b00030100b0b00c0700c000007080079044044519440e0700f09449902254601803000b00721585103210984003421840445001c4c40784c50307a884030303541c1c0c1043e007081d40042c08507c0180704280741c0010300154800c044008052880d0081d000074590440208002d00c84140450802c07041400364000c400581281c0300c0511903031500b014001c000b5000090702510649280311500d6403594180301d60301c51020704101a0280c18215001c1c050b00003203170304044508070750801c0700081c035000491000711480c0d8800c8003d6540e080443d00e880c02d641140c45008500613010b4000c02c0000c0d402030040b03143c08950300f01004d0004107400c080d914190781c024841900c5c5400400c0220140465004050955803070300e950314151b40c07403c03c4a007110406d40500907407850400600c2e400d0f07814040596401580141105c0d5038110103007070a00c3c00c8240312401c2d0041200001080201400000e410341d004105251031400c519042c0c43c0c1c0da020b04810301c1406010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240417769 1250 240416519 240416549
    0x6090105090103180b1506040305070e060a0b130f053a0c030503071a01080303070e04090827011407060207030215100e0601111c032912010510 63
    0x164002c3e0020184d8004152100303c10014070b00f04410030400460b101002107251003400c0c602c81c42d01c64107907000c2d80c2d0420000c0ca00c1500740301c20b1111402000e40300650040030300c80c2c0090540101c0004103100340108210035a11460007450028400c404e802961240c032034030310164005180d04510052a4002e42540c4010a0a101200180c0240c8000c040d00b200d08690001c004e1040c00002020718a12400c040c04107210b03601c00b22060800203004100ca503400030404607030060701c501ca5107094028024030014402c01300f5a183c2a5a03032050084021900c1d03545004d04003000f0780541141b401d802800c00c41440440f0301010b040d50f1003181c0c801090141d01042200c140351007009038250000694503c5038540c00c112895a000045a10a102d03d08000e2000252907500c211107141188020400600340d0901a03841d0000e40030700d01c0055400c069032004601c1d4498141440f050a62080441c1c80b1000e0300300d9814000d17200040320b076007055607050009000c0780d0100080c0f583c0444465007001c64034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240419019 1250 240417769 240417787
    0x71409130606051215060103020a0c110102101e14010522021201030f06200d051f060302040509150d0b0901090f0b06091b0a18030c030507050a0b030606090105 70
    0xb440a90001ca4024100701a607020742c80000920084a401003241c40c421030396031000442c03c3c0c0c403030b10440c040050000000000082e101140501d680003050060325600d10741c200703205040381c426911a00744030701c032134400c9036056403940300f800b4005400314941405176040c507000c80d240308880b8102103444115600b00c01503030001d65050f2612451100e450070300c2940c1d00c1c00c19040070703881503100fa00c03075a00c1c102d480c001c220340840e0288100020300d20440d0030181c200e074019008200003410100c2401404400c41702e00040040080c0c0585542c2d10016100d81c14002400201170005041089100a01c4403030b92b141c5d81c8a40c0c0802805500c1300b01d1316400d42d10206601d001d0000c0e40f50041428268200850401940080e0184944001c0e240240d41d69100030031145501e05000112406000420002c400700e48503070540c030b01000c101042207803005e640382d0750003100316174071f92050b2511b800c226018020380c68142007190044c050f01c0212410b5052010004000d40708100529040c06800500b07810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240420269 1250 240419019 240419021
    0x11401050c03030403050715020304050d0c0302012c210d0207080f0706050a14071d30061807052205040b060901060219020d03051b0f0714091306 64
    0x56503840c880142c0e81c890a06180150894100b04000c46802d507650442e0595154075100f940d110380c0d00a0014117044007202821740d10504c1e018000d50865484d1505401c2200560754503050501030002890806035008080d1810008004c130003650203405203c000c44911503003401d44400c0b1901400060341c412203460001c003035100740d0080700071410001c00c08400744401648a540300e1800040180318803d034503128840c7e00b21049600501280a034000c80f5072700c030010200c203440c501020b4802a6140080b00d21611155100503038040b10020f5811011b100140074440e031038008000001c1f8290304400801c2c49900c0c0c0525008681c000c000541044030141c1800c1056140d85181070420003c81c1824103115051a0007111800e010300c00c0c081c00060054800030701031200c50700c1c40340103140003400d076802c1200b8040495070980410000740300310f0520026094503c40c01d2042c01c00200410075031607a0f424203102865003c001c079030511003042000d6481d20030706036078810f126581c1148885150b1500c24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240421519 1250 240420269 240420277
    0x30c06030c1207051917040b0a110408010209180108191e03020a0611040609050d05010e120d06050102030f030a0c21020901140702030a080715050a1406040501060801140105 76
    0x584909001c1c024400150b4001008081700410800380481d0500c40d400309582c03c100c00c031006807408110384c0010f0040342455040d540c00c08a50703c030200b003c11006c2c4d10119560491b400c072600c1651300242c0030a03585041001c80c140c1c21040c5001c2d4040c2d40c9020000c586602d483c01001c00c0b9010070000650812800c07924143c0314500819035081e01c6040c90800940d64260100d0403100c45180652500b1850500d6003500c0c22078180b51b0b0780c00c45986c00d0400f03024900c0915003044600790340320180c18088038410b11055401203600c98130551588903031000c0c01c0c280d90065202a066400402000d02141700110403a030380106413080110314004030f11000c81d41903907006086900b000b0030020000702040207030010f1801c0c010980c1c032450f0a94090203806c07558403401100a506501c2084070500281400c170280040c41e0003550340640018401c0188800d0350011116485101d80d40c8010340368200d038000c04150000003e980801566040000c090484030060190b24419001d00414000031781c0702e00221 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240422769 1250 240421519 240421537
    0x121e070813020a2d0e13060e0d051c180f02120d4404050a060501080705150a0c03081008010212011410090501120e010c0e1c02030c06030c 61
    0x20a0f182035a4408400100a4100d1548001051000002e400180b1403001e1000ea80d444c0424003200e072160702d02021254500001190b110343c503480e200c2c4400b40140404594180c1030788807a5910700340c643d500c0c0b01e04425010700566243c5016424609a081c2c00180d400583d07004c80b40400d0404180005041602859481810351084554a81300c09500240710400112902c008484070404070820902c885041e22184030100703498000020042110312400d90400d0103582a0f86c41c107052a00e5079001e640d0240c002100c5507115170070801403801c20501c01d542511104070520b0400a410400900010099001808008681c1c0c00b00c1d40020400c00d07014010034043c0d00031562541d4a00386030100f12024480e80060800040c5d408080b0705100704240e9450055036030fa50000d170304240040d2000e00604698501542e83c4000000d041c0c0c90910070344084402c40d072110881c00b10904100030100d04584441300c2c040311a00c840d1001602d00280c1d034070141604036034298880d92540b00240c50341c010b030345a03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240424019 1250 240422769 240422779
    0xa0f0b0d06090f09051902030c0d0309080d090305070902040e13020f12150108030a0206190b0a12022b0803040203030702060304200102010603080a050304050f0303090102121e07081302 81
    0x3c42000e80a035010042451040c07040d42c404282c5205070b40c0700180c540701d01a4164002079444200c6140091002000c00d10a0403c12140c41e2140300ca28a814400c6000201048158000f4000c1c80130030010b480041014400a6180070304040190b00c44080251a0110303a84600015a00b1962402c240c00d1070300030094041003002c40e070012410b41d5035450104000e808811180081408030000c8121030041c1c0d590b4000305225191010044c00300c10310554039101460350781e5001c00e11952413010040c000c00000e804881a400c0f1801008491200340c50581c08242d00da44100c200003c840c07800503000f641011310151655158004241140300c2c0560017503000400200b00f10420150039100c0d000740618000b5152000394407001079080b20244c1c080500501c20901c01b558138a8480d0300110790062140c006c1d0380c101c110700034800d46550001c0c1c58040c03040e50082509070000248495540e400000342ea206a00303107240e070b416104446009098142003108600020789005443c1051078403499001d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240425269 1250 240424019 240424031
    0x3010603051b040f05130b0a110304080a12050121020307031a071101050702060a0518010c02030c010c021b0607080f0403030c03080a14150117090106140a0f0b0d0609 73
    0x404424440d0b00c050703500344914900f102102e0342e020244207a82c0318203010443c00700000000e0701ca060411000a02c01e19169032035003501d102907141c0b00040c6000e01c2c451003140f0b80790300076003170301400490143c2c411440301854940100290b070181414103644c1d00d04400c8042c50241140042428244030741c00140c44601c040303110a03800c4520660b941c1c0b04041c40c0d1f0b90401034085403c141826210280c81c040c0c0141d0069000c0f41c40380312940c2c8a40e4124682c04001c55484182001d070a09440d800d00265005d41c10210307454104202c280039140c1541001d1028007190102c080030030280554480c0950b01030030707001c101c60381004a1982203d0346880f040c01942d480b140c1e04d10f0020b101c180e40c0403049000901103004640d40c54914090701c0711020a1b20b04400141e03031007040040302140d804104030704000000302000f007240c2016400ca03004640c510f0001ca0740e00e05200c00c041294070814083e50041d0100e0b4000c0000c5410047e118081d1007000502a907205105c11703c19024041e0f607003002c4840e42ca400c1d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240426519 1250 240425269 240425293
    0x20c0d060f11030405030918190b180703091e020d0b0601020a08040b1903050c09100e0a0806010311030f07060806030a080a0818030406141b0109052a0109030206090301060305 77
    0x102412011000f08e1781c0c400004964607540c401c0c12000c1d910b00b0344629400100301a64046900540000e1f440a44010721120040c003200105210070b8070342c800441c0c0c1c1c9003552801e11040d01d11010b290344000200541d00021070380821900c030300c20400945140c240001160f8145e1080c4450105903820046254855840750420b2140c1c1c0d01070300d50069000d4410f0b580d000118000e0154078840c8202943c00343c1010b540d441444018075100200d0310800c4150b44075040c007991100d404a02411581c402404158190324080c080d44000c1d003a054400d0b0f00c06030603652110700c0040e50f079059507520710b4001c601380c541402103481c0c002002e0005050030030102e02061100e5008006c90b110b00110703110400d1440c2e01700c02c51510303445180507040000f49504510450600c804c001050021481254070354120445102d0070b08594411000f1107042d00640007001d064003040030041c4500103c030500d03444000c10000042e14034070043c031000f07021701c8000c0341e046042e64080d07010000868114040c3c418540c800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240427769 1250 240426519 240426523
    0x90103050d0314010b040501110a0602041e14030d0f0e0409060c020c0f060301051009030f050f060702010606020d0e06071b0f080f070306051b0406080a0c020c0d060f11030405 77
    0x1a8102000283c500044280401070214206040350000c8000a25050500004403080c03a414509050342d0304c1040c0c00d840c0003c140344000c100030800c001a01c9990b20940c485800c20321403035849641582c13880300c0c207911182c0d404918010390400c0e0b810308482d04181e1042c10303aa02c84802c1c2c80158050b25041d840360a001c0b80d60444e00403811140d083c0e81c405032005082181019140516940205060005018900307021211a14002403418014402e554a549184103541d90b2201101d658001c6205911150300801009420442e5400280921814164001d5640c44100c844808000c010000703003d09480701812118208d4100450a00340030f0041e6490240c100180f0507044242d28191000401c0c807800301d1240741c1c08078010050030046155407a80e4000e132034043c1207581c2203040505400d00462000009000a00c00350b2960000f0b442c1c5010030408442c01c100402066401199800c03580340e0310142e12070320166000b840061f940b03007140c000720f0040094903080c000002c0004107004c03d2040c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240429019 1250 240427769 240427783
    0x5100201142712070b0f0712050606160503041a0f09040209010c0204140709080f07230306010e101d0a1a04090305040f0b040620010f020a0c050d02030f09040b0f09010305 75
    0x28202410a0340758100b486c1c3d5004400c540000004106640680d0b1025142c0c00c0160400401011075040c08032070a4113088d038250244088482d030340f00150070003902c03031300390400d080746580c030001c5d02e00b840b03180c2c04034160b24032402000d41d1141c0da00203041c0c40b440c3e000d01942440f00f90081e03c10009825504030000346c041e000d60b000c001007000c0d10400105a50001883e03102c542206e000b800070249400c64099403010f56107224076040884208401d0380703440030082035000713056a80c580d035160b0410b16282990080d19810a004074000b400e182401b844981030300e02e0b00701e006400001102d0f01c201c0902c0c14080c0441d286070ba400307400d080c80d801c02d160b1b001d005481a180050b014444a43d501c8072900c518cc403c80c45504045040d90f400256001c84501c580103401c4001070000c25000883c04075401242e000030800c5c1c01003000a40070600b4040c003002403441064290006603d01025101d590040b4001c680d40c6520807916035010b4020760f29407001a03404c010700907100f11490350b1a85025034451003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240430269 1250 240429019 240429023
    0x50a020702010806100e010c02060d050903030a15060e0105030a0b100917010605010f180f0f03140d09120c050405070329090402090915010902040510020114271207 72
    0x3d5400c007240040c0341c0136140261606540c1c503040c4004e00e6600056400811480007640e01ca0b200303020040f407000c024003910f84074841400180d1b6492401000d00b00c00c950208410740b0f0fa0442e00c4009010141e007001858503250002d00307085890359a4208c503440500701840d64a600401c00040825055400120040c2645d59030800c4500103183c00c20704600320fa00310300c1100d0004d40c440040d0300d40b0b98041d0344800c0e01d01814002a0703161030344036042c0323014000480e4406d00182817041820000d000303013a03201ca803414000b4006812401118000102920700a014881c0c24060750022002080041d1803442e00401000c1d0091015243c00900a8000e282c4941144150843c0d68141c000304ac1c0c142d801920501002081c520b01619250280309010300c00801500c82c80c0304085910440004802400b070081c42c0b450030261341c8070304000030712038030003050202c4005581c104100c140000320211080c0e40c0c441d016031000a01d500810980c0300a12204081c03030070300b50040448a44c4212100383c000d0107894 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240431519 1250 240430269 240430277
    0x3010e0c0f0103092012070e04030f020319030b04020d1103010f15050d090c0305010e0f0f01020405130f0207120507060b01090803030403080702010b03100e01050105030c0a120501020d050a02070201 87
    0x101c08a00150b080c0d41807194014105c0301c2d12580c0745100704c030010b075101d40460054440200300300069105450101d10b6000351219494a0f0b081004060740992000d403080c0303451001d03604101540c0864030b03001a070300340b041c0305141e1158502c0d82191282c2c4d042e01c240502030f90045c0041100064100b2045c1e0084c05200c429400d4040007003400009051b015000c5003c0e90340307030381c6801d0702002035000030074130540c08070b80b09e4110324000070200b0024025006181c584201070056210008201e501d0004898001280c0e81d0040c00100070503903422000c400304607c0d0a0020030108007111100380240319904001349816520340d80101d5080d84800540741140c0305410800070f62700d03158010f50b80c800c010f1060b0341c1c01d94070810005001900c20801550040c203540000b0440744517a10000341007030400980140303030130341c1c1303076594052a5824000d03180142400d07006040d9841e10305001c100418002d00038480c0070722102c07030600100b04c000d50490f03030900000c034820003043c00c0010000d0b000e90b00c1108264009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240432769 1250 240431519 240431539
    0x60b090307050402070b0109050c0f0f0a0215090c090a02040e0f0a0c050415032a030e1005060105040302100e060f0d05060907050301050d0c090c18060c0206030703020c0102070203010e0c 82
    0x1a0403c1c2c4215508039810030710300020fa0386800d072410041c001c01010300541d014240540813900f000c1c4405844000400c0000d00d4450b200d50400901e056184405030158007010030504c0034071680860100f800c0e490035a0446050394802e510030000e441145e00421303140c0c0740c2c1c00400c03480c5c50605c0700c03540c0581c04450050120001122080ba902d005501600507021050701c1400c00c2d0502960150311283c148211628050f40c110299940306400b40c809840402d8890241085030101480881c4400201031010403680c285040028030a01480c04000c1c05500901a1401c405016501103e40c2e004010003050b61030a41e09104082500f200e40c5d1510302605200104d142c40c40e00c540c0603441179070550303207150545e864002005068036030088240d554040c00040460282014000d075074014105446414042c0c3c25180d2400d1520341c154061710400403001c07a07040c01661070b101100d0b0408000c2c9005600c030114020f0a0b03009206000000b94158608141700d0a0707003001244500688100322450006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240434019 1250 240432769 240432779
    0x50615070b070c060f090c1d0c070206090109090510061d031c111005090f07030b0411040b03031209010606020d09050909072c0c0a02032b060b090307 66
    0x20a01801030000d141652110008042c184a00004800380b406440c002c03c0c001e080f10003240881300c0703043d019686446c64007802c1c00b115070103181313645880d00000100c0c0341514120000303403100d0058060080c49014006242c5400b41c0c41080c064001d00410801009107003485d4401d21401106403141601080300c02070000c000e10885410700e003404002901901c03c2400c020310300c261012200480c0800c1c85440c110b00c1d011000f04004080314807030007200020b031600b07166070701070b01e019140355542c40b02c0c0d8050482400060450300c0b4203a04290b0100900c0070000d801c80c0060082c0c10510b490b241c15200100740b811480b040141e65600841502c0c00820242d03481d0102244ca4012455101c008981821010032080c140801d2a662140c003900c2540c04440e15146102d00f031800408180782200060929002403040f90703000c035500701c100500701034500110010080d4903070050311240fa5058041001d20b4418844502e44402c0031801c41004110702610781e10705c42c03420341260141500910448402085d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240435269 1250 240434019 240434059
    0x90b040f02030f0f040305042111040209010c0b06030a140c0f010e060724240807030309050904030e03100212010b070b0c13080115060314010b18060906030a0506 71
    0x1c00b692541c0f048407210f5640a41031545808040e0080302042410400007070300150008800316030303400141846140001d541000785c00014104082445030f44108010358481e038121a1006245030300441c40703280f41d038400000a00780f818400f4007803d0b04001000f01d80d060304001c0383c0e40503c80c0d03003224020745105c1c1180c01158000500214030380c001d072040000728049114400d000304030400c100301410b90806411440400c0e5060f800b002d899803d002d0704041c444514208480f0058140301e00105000340c07850f1402003024000384038260003020710b00003040034503125655071000350f08003030b0403100c652605140c00d10007948046908422408010004180b4a681801300c40d520341c1c01c0020b0181a80f00e0422154450740086030084440f40b4803407000a0608080c040e12440200010410300c8039480c1c458007030252400300d00426059081400144140300d02d0606581070100803d40000c82011a000403035254072825029507032018022042042c03c1c00c03035030840c1307225020036907144000d0142036503540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240436519 1250 240435269 240435271
    0x1209100c050a1203050916060311130e010513020a05042714060a0e040213021b0703060510060305040203070e06011b050c011119020d1106030405010b0f0102120322020a090b040f0203 80
    0x310465094007c208182d5200b50804946106015440342c5020307020180d03810072000035031200c4020b02d5402c004000034a05000c40550315414080150b01c0c14109138002001c5205170300a01507891400f01e1515001080084a0321004d03d5072901000207000d07c3d010394184940407903805125000c0c06002042c10318864444600840c3c1c00f80c41c081011021400c480080d4000e00b00e1560802c9140e4002031801004000800082d405820001541c1c10a922100501e004a400050a040c00e2034107110041c0c03000503442c811507810140f60312003901d0307170401243c0c02850b0104410750210040414414000f0219440c8800103003600d50320040b541c001840d68403403070790810220300c4020b64000d03400903080044100710a18032070b0240d03160141d0040001a015042030340d042c5d44907959500d940382d040c14803800b21040c86034240003c00d400385c1021041c000521008004c82d0210507070000007214140000c0c040030125030f0051030200700c00e88824040c40100b046240c038510484c2011405101000540300311307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240437769 1250 240436519 240436543
    0x40f05031b073602070812060405070c05031b0c0a061106060108042406091b18080d030b1c0f1e020f10020a0507060207060806031209100c050a12030509 67
    0x50f502680c070200b0440c4049070f41060a807054003045950001000c00c0010403540f06500c6403900d07070707080040900c002c03104000c09034412700c00140c40d040003017013000050701c6851100d040c145075481c40c0c19450508110800382c2c515085209282c021031a190401c3c1e0100e441c0a1590803034545983e80700046071890300590340644019aa21210b040e050740540c514202c11411440100300d00360b8503e00c19088a51851203542600203041d5034022440d071060548903185030982c0492401402d00e0303c10303511400740d02071003424969903060700328040e10744400401c007650f150350303803101c00701c1c0d80341860320300b04080c0701c400c481d9050f09100c125801244a10044200c54002c1d1207038414540c140144440e4002942e01c2c842948102000140000c40400c4804007802c801e44c0640324803450044040d1401c1800b800c1d0b1442170300100200105440c0d0300042d00c00441007160b1905a07204400c50030354540380c500c00098001e001c0c4600040c1408040d00c1c0240f101a5260390030401135031000c0d40e15445030310f04400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240439019 1250 240437769 240437819
    0x150a060e1f0e060f040b0703030912020a0825050313060807020f0a0f03020102070f06020d0f020c0a0611040801020c16080d2c0612040b0903070f020108040f05031b07 73
    0x140d400070300300f04000c1c1640061466441d860f054485941000d290441d003400c50000e5150074800c01000b01c0035564903c2514140020300342841c5c241d0301c421160107070041d40f500c040c07040c00303000c42c0b07400c6125079014003244c02900352582c642d0030140c4405a80c25a019000c04566a9004034010740d10010300c0d03c0600507414040c1c01c940c442d070341d5070f40f222403005001a01159002d00c80140450000454040c0c03040c8181da0050341d8a0701c125002d01690601481c00322107070b10500410841400201c1d8070b21110350b01110005000611a004640c140a10707044a42030b51700c081070b2002084400199104030108411244450540d10031846540d12102c0040b40c000070040302103c0640301e82c2402031414030018904005060411b217001c502c903500a040c40c4507110b10074a052000b03209041007203e800040c800017075891f200e00340c0c40d074115600c283e41000313041003800c40024061299034084101c98a0344007003a03a41d206400c62103c84014600c414520f80c50240860000310344404591902d80490304001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240440269 1250 240439019 240439037
    0x206040c0909080909070f030f02040308070f021804050a0507121a1012110a060903050601270f0e1e10020d0906110a080c090a0e150a060e1f 62
    0x140c98050000d41d44100c90345242413000c000c059444804e1076104039647d55407142030700d5561a0080079079110261000c400380c4100710a0000c0f4019034100c6025540081603041502d90601c00708031024445800d001440c000201404204000410b2560440b80120221080c081c0c8494422005c486a014028002030000c019610320040c9020110352004418680741c46660741c603240d0020240011204640301d403c100200c1d0350134907040c0c0c1008060a1f031464103c60b4107007981c0d11503580e208103004501c10150000f0200a4080060080001030300c0404000c0c8030342e4031001c00601c068040380c404120304d8060a180c80b21010350950760703817a81902c801c0080c403c140c2c4450404000754000c40c0c56040b000c0d1103180342c0010981501640501c000d41c80f440d1a82c4a0b81d0400081001320080d02d15411184100b000340f400d5903d0070700c1c150075910303c8071441040d901ca000c04a201c484500400300d8004500c000b0000b015500542d0300d2861031001e590f21036000311001c0c007550225840f80b0031940442c0344a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240441519 1250 240440269 240440279
    0x100e070212030406200309010e071e06110705180403030b010216090e150c04081c0509090619140411040f03170d1a040e0303060117100b0f1206010206040c 68
    0x1d04040d001740350f6000311400104509041d8107040d0310841c1d820055a45440005010903410440362008081902da03070340056020309401d961503030307140c07060404210b44611604c030f201d64140160340c02000010312017491440d01f009a40040b84085805501103803808900d00020750021417000e03070309040d880140800505114200300140300d0007c410384d4603c2040308072602018800820350041500c0c0003602d407501d14002c0724038a0090101c10312105483e114480c00a8107800c0300a82d90f640c0b4041b9084003143d903a07400410000001c0d4580ce1403403000b0703204002181400092800b05881003038034180250026003900075400d03c01c920603075030481c0d81140104003082941c1c24440c4164650702040b80382c41240c4003110240c4a142600610228820760b010aa519141c4546c02c0285518030180d41145441c0d40060101c08092803a0180d07070510350000ba0030580141c60200240003c500b1207505d4040404140381030380c03c20384084c40301c40c1220021410a600001e84144100ea1011003140414201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240442769 1250 240441519 240441521
    0x6080c130c1e03090803130606051005030a1d0d08040507050d020a0b03090f071e0e0f060f04110f0702040b031203010b07060204090c050304060f0e0a110a0e100e070212030406 77
    0x2c510120806581d060321400144160000314098045c034444c003410f0342c01d5800c2c004100e40050340801d20130011803810f00c0d4140c2d0420309680d8095181d08000a80c0d002d213402030460309a40f1846003015001e910035a116442d0031a0281e07004a000b00d0403200307019100e00501401103507111010390303c003500100c1001414007a6000750b078488400015140304145541e2503d01c0e1580681100c420b100c4002450314014400c81240380040c03560f01c01e00c0c252070070101520406590003405550046d40030440c07046540c2c50b0354001c0714807090304580745969003001900040d000c1d00581b03001c03445182040c44070741c1c10b40342c002007212130110011005451039282858a055035400120304480070ba800340000150f11442d44902e20b101c1020340c842542d42c1c50b0a1401030119014100400d5a0394948100036008050008407189820743c890000c0035036070f90200c0096640c0315160b21644001d040030080001040b80c045040003107901c1f0082103441611044070686e2580d0501c041042c04150a00018020840d0307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240444019 1250 240442769 240442817
    0x140a03060915020f030702060714181f020d2c0105130914010314161503090b011401020d0801030803040807020d06060b18040614150c0106080c130c 65
    0x7040c1c0e199404018580b4005050380c00445200c4c10442011080014040d0144800e80d400806498030216904007503081c548035000b510000c1d0300e040c60740590f06055844220021444602d178580d001d01c401000c200083d03440c50f1030051107002661403002000c22028000d500140005a4458058902c4201c0e00445a41c3c120106c02885d0b41010100050550304510070111070508030065060700e98154100001308104c0b40a4040e80e5038040030300b0002d08600c58a10344243d8070f00c08080b441500469404402030300304144041e0440a4950000450500f50120314564075020780a80d00c5500442c98217540c2500d0900c805491850704100240001c2c6030803008160461004001a4041d00f1079101c8800311006500303c444014400038940003042d541040302c0c044900100c500707000700c40c181140042465010160b81c0d00484568001c1e41050000c0c000780c4401c240d1803002040107075507406016990741802e91030f9a000303c0b001d1810a40c0c00c49a405408000750035902e4482010341305807000341d036a1003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240445269 1250 240444019 240444023
    0x30605130f0302161707050609030a1b080d0503010806010e1e07080105040506100c020904050705150306180721180804030c05030c0904030e01140f0a0801140a030609 73
    0x40d90360015000400d4080140c4800c1e0080d401410190703a07504065030204040d41000c032000b0742c03c0c80c0150340404c00040c000159242540d0580d10781e20340002080c58100c00e400000c20400c4515441007100c001488181c1c119452081111b20742c110620065070144400e0041c0c980603080703100140201440303a01000c0c2c00080b903c51209040c2d45145031801c810300d045c3c0e0b6603070000705402c00401c000d1900780207043c2c001d0001c1700c0400107064440030203042c4940b285402802100720000060610109002040007480c010302a403602c8070301031a281e034841c2d00480b0007034800c0d208025008805100c07418a18800c00c5203403120041d8000640c1e41580191411048a00d015207484075aa03c3c080c5c03190381810b072580b08114241d02c443c1989890140d10140350000da000f544494003805203a52038032490b84d0026014140041c0c1c0207000e900482e1303c0e40f58400386003040040080d00e100010b0040000b0080c8416960390f00b080c84e602c420183c0302060a0000c4158080805007061002c41e8080d8880005a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240446519 1250 240445269 240445291
    0x90a0615030b010303021614030304050d0c080105162c090402040f020409060f090c09050603040503070209071205070c050c010f0504080604050106051c0c091d060901052a0301030605 80
    0x35076250359000000a090b042100103030010212251546484442d000c041c20484001081c180301000101e41d42e07005903c0b84521030f088141260043c415480106005842048c0080c00b4902e007600c10407103002c95140c4c001002400301e460716414004203c0c1c0380f28480c2c1d5840c00100c0486108800c118030400003500c00e80c2d0180e502c55aa00d804e04084c4018001000d00050214105142104968070019140e00c085e4115041143d22140103900c0065002030f500f0807190a0385985550404500c3d40c02075080080d00284180705004000342c08c103005120791600701d2402d01c000d913030780e60302201e00d01810f10740105250310a543c01c2c1d03050f40c01400c2a940364403151604070301b0702d07654020051400006880075103030350b55a5401070025041540c403005074558020582c0c508042c076640e504402400d1841896000c940d900c600e28100f0281c800d4010700d1800c00d00c02c54585040903002d00e402446d0503a20713102c42003100d4041c5415015410806c1d0320070307400340d02d6441c11a8030b0f644134140130b098010a80d010f40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240447769 1250 240446519 240446561
    0x7052e0c081f0308030a090312020f0405040e01020a0f050c101103060102010c080114010e06090d0309050a05031b040209031c02010603030e0f100c0215040b090406050405090a06 78
    0x48040c458030065203640da035103000c0d60030507040541152100040078401c182008a0a20104240c00100da80241e4404c00c00110448282002c45d0001a80800105501d00005108490303a03c04005041560001c039003c202d200640017440d400c070300c1071100b07100c00325075500c20350381c0c003103000740c000d4401c10039100c0503140082100c0b9049000c40e40c00070f2564001ca840801480b0995a0911900102800a0a003c038182d41001c1c440c00c820190701185a041194004200d4120380303803801a40e120301d402902d228041e001515004d031402a5030702809001d142107480006443c640041d215403a1503c0c01d807002101e040d69414403001c2d40c052a081ca4242c030135140001d620602041600e44900c107107500024550381580b400501d0001e41c2c2d240300e4071420680ca0a04a02c0e03403034a620344051181d50500072003c035540c1c80400c07043c2d030b21030540f00c1895501080029024000d07400400184408407000c01ca415292420801210802d50f0841e0640e4400d00e05030000070311036800200341000c08500d003140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240449019 1250 240447769 240447853
    0x2c04020c0303010e0a06030b040f020310021b15011202150c0a030203120702010606090605070c080709090204050a090305041a19030209120f12090a120302030a0f050705 74
    0x240d034459450280140c1c0004010041c1616031000a6000400401c003400203c0c44c1d0784440b070380680c0c050005040010781c08a8002195030400c400c42c44147d202d18155140d0340048811180100c0b098100d45450044030040c0807100c072242c00803030594201d84000c050081054007404a101c0100d20030001e009000c010014441c1c6040220012952081d0b0040d941e850908117201d4140d0000360843e010340e0704150061102c142c1001080040d640507151050f2110080d0401c41d07003c134001c1d80540300c02d000710703003021400404a40200c000d40c0e0003690140205c0d01c4800491089650754440034001a03020f010901583ca512043d14400d12000704800307040c4440101c0e4003204183c49076240010075800940c244130b6051210041002100c120050406c511046a6440d01c0c0c400460742004090703400107030003009982c0d8000b6007002c2e25185c40110584007080c0303030180d030300d034004a50240480d81c100e8242020070f204104070f9000707a41c0403014084021003e0f895001c2c0300e4011584000115240c101505 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240450269 1250 240449019 240449021
    0x10825090509100f090603020f041e110901032003070f020732010503040f120306080303010305010c30020a0c061410050f06030f07170901050114040209012c04 70
    0x1020b00c1c100152800124135081c1c00120754511343c1d11055800e402c20300c080001d65079141011005440944000c68003804000702e011404802d00c41c204001441c007a010304014913444042e210200003a28204103504c000c07500c0d0705242d5200d01c0c100c803101008100046030540300740044c074400c42740d0740101e484003a01c854943d0403c9104120050030085010000b0300c4110380030000f00310022007801c4c807600e1070510352980308158907007020103410013100318141c194083c400d600c4900100683d0b010b603500c03944c503440c1c594040d054038046000050301290189000280d0440140400d00c6a840203108502154070301d14040e4215410030b0090210003075821010401034010000c00012000c0c00403607625003c1400c0200c04280e40000c3e0142c86003420140c103980703503101100d0308004d00039010b20480c5c4c0c8034101120350090354040344002c140e0040a201959a054001506035000307a903026055100b440c091004174040c81072028002a00c040c0b55003007194892581116036010035020340656103500020034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240451519 1250 240450269 240450271
    0x200702150415032307031d0111030f0a0b01050703030504050c150a020d050f09040207020d051603050c090f280e0a020f04020f0a0813120e0f010825090509 68
    0x52550360506115040b403940c584602c40488004010800700c251940002030401c1800400880c02d041d602c1c042806000c10703500058030f001e00030780000c0c499403040242801181d00203031800c1c5c800780d910b4008034003008401d0082c0641107906944540c18010561400c030b01504000c0c1007074a075405544c81041d1280c503402103c00314558901285030b03498926601c020300d0040f10146d14800c001050081e445c040510008a03080e07034504640141c1c5a05160001865840445030b008002d8850200809105d20314050850110b0f40614259070f807501140c418001148411502d2074000c1c403c0c46e00080d0b080c60b07941c121500d050440d8110344422159803030210304443c1000d060800070b601c021550300441c5406100301c81e140e44192003d6042032440483d40045001d02c007500380c28001c25000040d8103206140c0410402070b00f050307104898840c0340b41c024181400401065008a001c20400402035001e000400d019842e91039401300d680210089131800d054416250030700700101c0ba000020035686003403181d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240452769 1250 240451519 240451529
    0x210705120c03012402100c120c0915090302030a290703050108011802100e060d1a120c09041202031b070608240105030a0608010504060903020607032007021504 70
    0x959a54102081d4403c103054034100b61190180d40c1588541c040e07808a0340f243c46d42034000340841d1803030594105680703186803004280b4045280ca0309804155901c0302d80e0004032460000b42180031181580101c0344a4020302010790154800381072000060405e0480c900040c0304205400303440e014140d12b07548803420603528080000c0d2540300502001000381310310006070342040b90a1000744003c0d40421000690301c410241405480c801d0204140c42c0c0780201c440c00019000c08024010000c0c00308a1014105a14076020b0710034414141d5980000040b688180213000b01091000c1c0e0300c655410040441000511003140024071104842c111442c2c50170020652040c0a8011581801d03c000c1c0744041c018020a585000414110094501d1700c408401a680a180040ea03981c1d40010140186c5100d600401d1190300c1d2408110034400f560b80035000d010712030707801d840a030b84808800301c00307852509203440354010540482c00c241e191010020320003a80b014020045400c0d000a10801ca0f4000d9484 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240454019 1250 240452769 240452791
    0x80a061809032c09090705030303010605130b18100e0607060501050301050705040b03010b03100302120a0b0606090a0e04170307090f0602011104060c05011d07030b060621070512 78
    0xc1408041d000300100b0100c03204801a02800c00e103804107000c4150440c03540c18004c40b07a440c0842e15980c0b041c86808003074040035044958951351444010600e0740708840350700c107042042c4070100d0808201340407104081c4502c0d4440c840c0207400010800045d010007101c0d0280024441c401500d41c8401014040c907602424001400307624000615094a40c0108058104841000240206580300e02070b241503411803101ca58480c2e6410744100428a201d4001962065040544003034a034000030344814118480c51b83ca6240340c41d002d0901c805801803218030381d880301c17460700e052242928101c01c440d40300b809100200c20f00c43c2000b290304080d500c2541d40c98000b0741c03440380c00c1c082e44001c1025140100650310080100c03800f4580d440391507000700d00400007008008221081401400d4200c03d10040c41c0c0500640210a9140c041d90f0f00c030003903c4111403070a08640014403600d0103a0a648a090068048400d4a40c41a03120610001d00902800a0100600440720030014851000d0f125100b400d02c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240455269 1250 240454019 240454031
    0x72d03020717030105060a050a0306120b1503070501021209031501120b0f1006030c051c020301060e1507020402032a1b0102130315021b011517030901080a0618 70
    0xc2054503030b6a15010151410b81c200010015030300d0f203000712520000320b131400c0f544400071140114080c103010f5200042c1c007040aa000b43c14080030b0f00e4540c1c001c604000c0c000c80804d0382c00f81031540700d10340340c07103424056040103641c00c0421990b480100030072036000701503c5000b0500303800220440020380181c1624801200071108100b00c00420310341105d003402188103641303848105910710f241d0500030a002c01d500c6070301216549000704260b03400c410112103035030340404c0c00703102d800000c1d002441610002910159001c0c0d07a8100214021072200c40224001e180c407100c2c0d001c0c80701a6102401c00c034400c01c1140c180707416001d0600f0801c4c154040d07031400156100c0d072180a0b4100080245011080b6034030400140e075009103132003100f0045071b501078009401b1003014003400c0002d0044112510740c0080d5440801910901940100c0003071000e8101f0410301034940c24025144580d10300710b0700a5500c20400c0d6502c1e50b004407c490b0b03000381c03105004910291900301105440003181c60740c5c0a001c0e2030300e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240456519 1250 240455269 240455273
    0x111040503010c0207120215121303030606090501081f03080a030c080c03010b1b010b0301020a0905120f0318150403081308010c0f0c08070b04152003072d030207 71
    0x8001c0030b101d881d4504c000c00c03034507040912406420700d01d080000e120742001d040d0440462184401e41c1d26040d203444503800c15140c0325038074110004201e08105e0009103041400710300c0c1802000c5070000c1e1070041e5075085885e51240340700c001c40c10b40c07502404100b92080200000180109000f48030a505654010950304813910b009041004042d1501e512100107000520002800800341c402404002d41c40c4409002003441c0d442c0100042d803031168065000280e10203090ba00481da00d400c135001030303c04502c80c90f240801244c450307000404a038030340e42007000481d414500d4400300f102c070b465008007010b0b800780e0b00d5002c05801c1c2c0e015600071100d41754041a10130780f40c4100c5200f00001e00c8010003c1c020413225a10062028402040043c24011010040001e004407e0180da131075581c440440300c51400d2a00300024903040d010440b95200f41489c01c10407001d007038800d0084400030003000940c00c6440b2044240c2e0400c10394802051042c160003080ea205003060925403c5003145038074016503403607080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240457769 1250 240456519 240456521
    0x3121e091606020307030c1e1e140a050307020d050c03030417010c090609050415030501020304030e2107050909010e060a0f0c03050903092101050702061503010515060a02010e011104050301 83
    0x2d07800324040d0341061013100c0100b904006241d03113060380801c509100b07252480e28019509410440600050182d80c61204031441440d0440701d080d0140d014280e07071500001510b03503640c14070f00009009800905c10360005051210040d041a4030640c1900d1034904e2240200b45982c0003540801e5132000c4089422403030700c4007803081c80b07103101c074900e00014828282000501800c44074441c86000d0340d551403c00c0c0c400010304040320041c5074008000d40d1b403400c090030010500301e034200b15507120320301c4050340380030380050690249903091640e4064242540b0b49070412400d0705c8020114500355481e5170030b83c3d80c205414004544658000e080005011080108100c00c81d060300108005051a020038441840d80000554419200440d8a2002c4001c84640b2030080109a00001410b42c00c0000f0f01003500c2d0046411446030141044141008030702e40d04060907540309443c044190031481d50034015908120004103544001030001007a00e0980e0000c207800c45200410440003a500414240010315003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240459019 1250 240457769 240457813
    0x40804080f1e0d0906080606160f0308100f060807050f07030315080706080606071a090c010e040603020607020405040602130f090c02013c0c050913050903121e09 71
    0x440b4002c283e41c4400c0b98001d448844140141c409020a00e400160f01d9524803045602da4200b048883c01d0780e10903450404400c07160480e0842c0030446900000d594100344600c0c0004640010b42c140514038588541600c0030103010700400100310040042054042440e0000c00089119503400204480c0c180645011010140c0007201d01c2e40041c41c04102c07440e40f0018240e04120101e44a580d80c178070625045941e00100c01080e0074100c0802e00b0896214004580c1c0d140010003030b2030f03d80c00c0c0d154002c208002c444503400700a6114806008450160500f075004680c07040c484c020051a040a030fa40e0410403481c10703071020156031103824081c80407a840b80034000d4241c1040c0000e00054058840b01c031000c03e00324030110208405049180c43d90360850441280c40044500c040020f104405d10091266111108060042522006450701e010f01480f40707070310620024000d54142248092030628001001d8031401030038540100c440302a00c0b0800740c550003054138600030280c103500d40780e5030591004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240460269 1250 240459019 240459073
    0x2010c05030606040e09030405030a05030a0e060708030a09060605090a36150f0216141605040905010f020c06190603020319140a1209050a1d040804080f 67
    0xe0510501c55280c844005640035641801001141941c41228444c9140550361110350305101d205610014440040003c00d0442e190b07603144001a0500c0c410300c61075200b0920010043c420800c0024138011081d441420003a110340d40200c2d01641d0b4000241c01e00e101174a40d15005552a4a02d01000340d41e01c0554000545466840d54100842850700d080205c01c404041c2222100c907d800180c40d0740c5610048500b01c1700001103455450240c805550b81424020889250044004060680a000a4a02c0c107481e400269540e40c070700f80404e00c000b80412803002c48a0390749828000c1c021002c02e001a0030091848802040d144c0707082081c00342001407810910500c10b18210080c405600c0106400c0301100d1807000c54494040d140c60150700c8a11001c03911402c0d1700805840f04204130512804900049440e07559040711901d5408122044289102d0803800e5580120011000c0c03d940d641254803034068441e69040c5542c500d1900d051082442c1004190b8100840c42c0035448995008101408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 240461519 1250 240460269 240460277
    0x106030b040b0906060906070804030309030b09031e160c12020120030906070201090302040c08060a0f05092205060721050112020f0a05130f050106020a0f061e060b0a02010c 76
    0x311071100031503503a20001d403066000d501e0000b559110f581f00d0004459840317600c50441176803203640e81401803c600c010b020490321000507a01091001340004241e80d0291800c1c2c50311501c460070b102c01903841b580724044903018000340582e8500880c1400d02c128004060142241c5206250761000602c032120051068010072008151a6400303d0000151114020151805955000c66000603950300441e5032000b94414140b00c007081240d548211400d005040c00da460200343d545982140942c14610b01800c3c0c1c0003505040010200003020b0040e040c08803004510348020800c40c2c44260620b08102d901402041015090464940601481b0318140c08001d504004c5035040c200c0d8456861061303003000c3d00c69217405080c0c0c8880da41e040607510040100520104500d40003d0003400a401c100ca03051035480d2605c40002029030001c901e400500e80d00c01c81c8a880d40d10240d0b0343d42d004041ca0b2050448180c10172010424400d528801c0c50082c0040c004c00729154020700000030300307641c0083c129030100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 240462769 1250 240461519 240461531
    0x60204080d0504120b041a07030902011706010c0314071b140102060105220605040501090903090509060f01080417030103200316150e03030d05010f0803070f03030209010203090301090b0106030b04 86
    0x10146032013680710403a0740031200c1c4038541c5030f40c240b00010301521890140204100401d0106950301588000040c520070f07200c1d090300318640324050b42c0004048403010702281121943e507001038858a015901c412594040718200500c90f00c820000003945002e0280114400405000d00700d68080b4014169100340300402642d0305050202c0c050b00c00e9007015159031014076549400060460300303d03101800014204000f87d40e03590490fa03000d44800101580032484004022442c1d04001c132a0900c1f503034018041180510219004440c8660010010344903040403444a224000160300154004c5014045036107081213102c0c05217a8643c2c0c1c040c4071621943c0214022001d1100352003000080310350b00d1140300d0b046580f5500036520080c07104c5141d03900d400000340842d04c800140c0c0c4614140c1e14100d1204050070707120500d00c0d41d288254040500f58819000741d0324002882500208407010061043c1c85c107181c119804242524440401180c60f414440014410240c1c1031050800b0050111018000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 240464019 1250 240462769 240462779
    0x5070803040b040b0703030b1302040f0e04110108070504030605090c0a0b1206010f0306030503040e041101050c0c0d02010c05150906060301062306040b0d020c0607050f0d0e0f0109060204080d0504 86
    0xc41c031844c4621035400101140b44020705020390700c02440340d0b40282c12041205208081030f00203600c0360103015484541a103010030003410358214588601d030701c998030a030711a40c06001544c1080e00281441c0400000300f00120003d0818051b0f60b020300c0201c4002d2200708a11000c1100c1030030550000728100704240315261800d0490810107401410038200008508800602107004e00782982000c1e0081c800040c000410031540c503403e501c00d50145804008003241030b401180c3e184190540c210340b42c2e20069052a00340350042403614040d105051498911225644050600b2005c3d81d0390385801c81808104101000140496a13100d0000c40007045618101865900e010010120141a0005254a02c02c880c2c40d030004540141c108020040c0d11b071040d404180007e54018038401c1c94a00480c03010449442c02002a156a030045c001850300b0000041c4d0004024141c0000000491285038019054568284540c41d2800c0c0180000350380c607070a00c6031562804001c0340c011010044204402c05c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 240465269 1250 240464019 240464039
    0x1050c060619090e06090d020601051810090507020c0a09151802040b040816060305040803040b0402032d160303080f0a020d0c03050f10150f0c0f0f0507080304 70
    0xe030000c01181c6900b03824180048402d0941030b80c2d004824480e10303054401d0711075000040ea55204800c18801c40e0201c1e00c0c2c1600803a2510420720035590080841014007130465080f0700807550011107400001c605c1951110020709039803042d1031203000b60b0442590350307103d0f05040e81e0000c041d008502c002e028411652001c4209880c152107919505182101c00800c602c0883e011100101888804203803595101d20650391510440d4044016010310180d0004402c0e009006a074032603a00001100d041d139685031180f6020100090089078540505101a5408051031216601a010321818004500c0040500902e02a4200c1c0c1c51801d00526840403c0040d0b8080c55040d80411810742130842e548403600c080020380074070701c00129101e00f841c1d61041c405625078003c0340301c2d551104407405039440300c0916416004050103003030200d144064101441318015504180400c1091400b4800c251503130315a41d2030381003110340c203d882000c44400001400350402004002d091160055494180b40240c2c505e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 240466519 1250 240465269 240465271
    0x203060109090c0f030309050102071406070611070203070906151704030309170d0f0c080714031b03040f05060903161707080d140901180609140706050703030b01050c06 74
    0x4a03400d80b0341c160b010800c07124250b44401411603800344444c20b40c8a25001d44112000d000d01401840f400000192580401c0c81c40c02034402c020308603920b4024291600006000c03411000e07401c0316400c22003040142c03403c211410041c582040002070160030005ea032500040c182e06800c04100e000342403290406e000031040e45c2c0150f803505002035403035028504040444601140c4400c0190045928060b0036a40c0c1c0106011000b00102004000040700c41910703c1641940c6500005062060054600c00031800039504501c01000ca0303682e060b0b15041c08900742c1d0003103504039041012043c2c41d00400c0030170010700d0317004a6506c01075402c2c00c0b582a03100c0c100f43c44d0040064503c0c0c0a0b404d484c1c041078403007000c481406400480081e503d405c5c20040d14060a030313030204100719859a41c0060107410040c415400b140e0101c11850406c1c48140d1540800351422100a490102c402900450120403c03c0b58034010080ea8666588a40030740c2000340c00c50b01c050307042e03d05000b010015402a004042056 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 240467625 1106 240466519 240466529
    0x8070803061f02060406200c0109060f0c1e03020d1a0a050102060c07031101062c0a0203150103091406090a05070504060e0105010c050109020405100603050a0902030601 74
    0x12010030002d002490010303000b82d00401c000917031a030409446034040d0106014080e80325404824554043c1e5942101e40e03540780121400c0010f030780034090b031607004040d040208190021000e041c0300ca0001c40074901c88a00300e01c12102c0340c041c1e4140c0300141902c075020007528881000c101d0040c1c2c10142c64600c1440d040c00d0025280d0701c0082c40502c00c0200b040c6081c00c01007590740c10750300c0308010074130200319548415002c07580302c040c8880f00a4840c0b00008101e010700d00441030f030240070f001074950a0350a0040003000000603807541d44461201081c85c00040351401418085402014108660b0341d47c091407052081c046070000e0140401030103801035035096030392901008200d0f00103104601404802d1401004250700900620000c1b40c0560008902403203d41e0002b011250301301c49242c82c030490000c0070b000141e4544600342d8400e0442d0000c118011403900029030b544014420 = true := by decide +kernel

theorem cover : BRFrame.Cov 240287769 240467625 := by
  have h0 := BRFrame.cov_init 240287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 240287769 ≤ n) (h2 : n < 240467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
