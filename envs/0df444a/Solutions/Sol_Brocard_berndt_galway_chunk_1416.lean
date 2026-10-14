-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1416
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:52:49.02281+00:00
-- url     : https://prove2.me/submissions/c549e5b8-b8ea-4796-bc28-c9383b2470d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 254496402 ≤ n < 254676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 254497652 1250 254496402 254496419
    0x18031a04080c030a0509040f050403270f29070b15060717030a0b0108010e07050f0d050118050108031c0f110310050901120512030a0f0c0c02090a0b0604 67
    0x180200200e0340610240181d019901c4104060700300b8038140d49489441b1110300080c80301f01c40e002002081c80c5070a100c00d10010940003850f96a140c01e0400c02d12300c031810741c5540c0d208061090340c0b0410002011080000c1c201013540c50108094010038002d80b41c0d800310011200e4140543c40000d0061014440403030120781d80098801d03030344c0401614150901074a6126424030301c00722504001e501c800001046801d400c81c0c80381460020302420a82059410103404140301280181030320103200c0005119854031845000f82c0d2003240729410140903e40e162040d0079080c201d42c45210f01c80c0340c205000410030301e50110598610380c1502c50000103110445007000050701c0100305030050a551a092120055910801180700c0c0c520414406c1000b0719003014052403c0d0305a06c0301c042c81072554454000910301140c0d0381c0103580039a0007180c8907198181c44400515401c5582c07040b02e85001d641d014079a421489038590170740201c4405e282691502c2c90107003900c103110308055003c0c0042005015450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 254498902 1250 254497652 254497703
    0x815060d0314090f180106080603210310030b1801051014210703060b09060a06081618030605040c0506030601050a05030910050c0301080706020c06041202030c09070f1803 75
    0x284002c2c59a4100702c00340700171500400d032200b060741040804100520805400140c1c0d69000072080d401030070701b10312266551155440b400c1c480c0c900d4031000408201d407410020400070107141c004107500d0841c206913054481840c1c106803400e03000e5081c58001342807a030110171250f0840c2c00403007580800ca50904100101e407c400c2c078808003840e5542030000c440300c004114400c013440c40350074001000301e418000c010140000401c0140304281e0083d0a00c42280d0010300c03d504801082948420000c000400392913800c4e075000b220084241041c000010720242e60840c90050380581802500d0644610a000300f078481240d80074040b450130494407146a1242004590200403081590000c140502003c2c06598041e01d50380074801c000f100500122206115400082a00340000d041040950001c107815001d14815080c0d000c1004080400307545007801003400800d0014140101c1c1d1a00440140c0f2140d1454407200000b020261001a1410542a00030549030000f00201020b038210f080d101c2c0c800c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 254500152 1250 254498902 254498917
    0x810050a150c0c1716050a0e090f0307060b18040305220806100512060411040b03190302030301170f0715050f0705010b013c02010b0303040815060d0314 67
    0x122159200300c0c00f00d829028150040c01c8150520f101c400c0e081001c95284c0711070403e4003000501684020000c903911184044219858404100071301c4d51824082c905081c003103405108107000c001640d0040000d5503105503e040c81c00c540101460b00c241542c46110001168005d020640400c449000c58401c000e4158207030300c00720a25208251075030301d03103405c24400b500c0c81040302c10031510910403854000c4a0b420b19868075030042140b440c02c4c0c5c440d5580105824a0103006030303503601d600c08441e01c040c07014015004075211004400d144a00e4000e5896009120703043e2070780300204c641010340d00301180e180060020b040c01400d049003000c0000100c40800c101c480e007440410002c1e442d02c1c510407000703855102d015000000b140d0090000141c480c040c445c0390481000b040c0070400c018035815031211445000d885e000074007940b016003c00e0340104200d40c4101e40c180710101d0005003078400000c0d803080f000201c0f540b402e01b43d01d800041c0706804e281040b00401090243c00752000c6c420110b0041d0000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 254501402 1250 254500152 254500157
    0x51308030a06030f0b0a0507023702030d0c1209060210050702190c030c050409150e16030b06180c0301120305040f15030c0f050403060906060302030f0604030810050a15 74
    0x14507550313039201c40d03035000d45080484001e901d120403c00e0603482c4d846040c0d44480280042d00c07101c0e40385e2103c822116a29600b9a09041083c10502e85c04000306a80d100d500383d010f4221050b030608040e0181c01e007100f0348811610070a1800c5100703c003c3c8a0034101c0125400340c0c00a20340b115460b0581006450028400c2045102c0c2412051140f58000b590096807400303080e80c00c03282c9045040007003c0c031009400c501d010710304040c484c2c00021000780109980d038144150002d031603090210401d040000e000d4001c0d250592112008c0b06000c0314a01c0540903500c111903040c4008084440340805c4801121002458841400104248054440364064040c0309180080c5481d484850401803031300d0360f401c1082e403204403007040e0035415010b2080c07070100007283c00c0c00340124501c0c001c002e003107200e40c0c0401080705854101c1441000710b140c102001840d8014182c40040c00505c80130b569034081128203500189001000c600701d08420b1a10b4401e66101400d800e1416003002c40d50f51100d5980c1824404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 254502652 1250 254501402 254501411
    0x60e0301020d09032120180a08010c0806090408030c0310091b030510150302090301020f0f07120e061801020f15011514180d170405090a051308030a 65
    0x50307814107072080800e01e1344a41c580c0c280c1c141c2103080011482c205204002d400c04e103031201089406503a9501004030070340716040b03603650394040301c00061840d01024030641c000200000102e0802c1064202215090059440d82881d64505080001c800019100a803001d44100045078040340624011a846128621090307000d6603194103020032140040418030031501c2500110000c15490300a103a0802c041085001681e030400d44110b5444d0314001d8520149940000c03242980d440a4060355420301c04407403c180c41d180604103411503a840f030034048613401c0340090501a058007802c6941030300c40d030180c041d0b41172000204800420b80041807050f0306500c00c1c001e89494000c41003240044a0440d800c09804a51514602100b4840184030640070f003c10051481e151280000640e0141584c0b03d50215007152102c0c0442d400303c80241c000b5082c400d40c41c848202d6690b140340100101c800643e0300c3d400c0e56076985424405c0b0344c001c0d500911280c400103001c0e404102c0315405540c000b41380d2440000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 254503902 1250 254502652 254502667
    0x1801050c03030f150f15031812070605090601120b06010c0f06061a0a0206040224070308160518010c060e010c02070e07020a03020a080c0a06050736060e030102 70
    0xa165400480340000d540b40c81000b0840661300108051341070080540380382098200840010302200c0020440d584903031808030015040315110f8a81426051480040d82c04e070100c16002d82070654032604c0142e91150034000414000040000e03503034121411039203504110102c45e0b44544a0341c2015000c28100111114800042090401d070500001d2040c58006003035450100c40a220503100d4001d100d0090080c0141c000e02600820368640c403a0303046441142070000e481c42c11461551700b00000210500c0811410101070300514120b02a0340d58080380b000c958408002103400b4400c04040b01d4a000c4400b80500d025400755540e049810722450703003c611039007a40442400c4a092182c1400140d03c140410056100800420703a04800c040c80070f0482c0c01a03686001c0d51314594036100501d0410005080301111318144410300e00d00364840340c28091401c12480003410101c40c1020138443ca08460000d0501c00512640c10300ea00404614a04005180c12816529180b660300807a4055400b0000382c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 254505152 1250 254503902 254503927
    0x906090106030c090e19051518061809060403021203190209220b0a0e060f1509030105010e0f090a150f0609090501021b0a0c090b240c10060b180105 65
    0x2d41c4201c0c42c8404040c8040941c1803500d050301e070017900523481079001503254230050700c84c0c04110b900e8504501d18448951203160200304591880c02d0441d40442281d001c0c00b6000c80d001c10200d004a010b07038200d42c001c034071000340c288051009640c00150780c1c21884141c040440c80b50040c19901c10000e1001e03451041450000b0442014446d4021010b0784d10760140d62a41390400811000d0801d042c03102585250810105681440c20030340d5a2040707d510351000e4480c42580c049a01080001d4005d00c15542c0da00c41c00b203800d4105031089041100140000b5150400000c1c0300110070303400140d044084a8840d64000040030180311000c0c0a580b152000b18494096000e40500c86129500050780e5141c41010101c2041d00d410700e90010360088025000899900c48001041e02d040290002c0d5020348100000c0b8900c60513026882142c1d041c103442c030381c03402c1d100d0050545e91914401381d81840c04001c80b030f5412980c9901803a0000b9078140010a000507021100c00c1c8445010304040e4540140380400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 254506402 1250 254505152 254505179
    0xa02011b0b0115030f0b0604030f08070606030c09050105030f070501030507090305060c1e042706120308040210111203180609030304020a1d180102040914150906090106030c09 77
    0x2807000320401e00f08100300940d01d4410310324032a10344101041403006c0703540055004d00c6a840098281d0100b000401c042c41103c804603049070754000410041c0950700c1c6000d0400d2a1280304142009240a0001915050200b0402c440d4030490b00900162410a0015001040090001c50401140b1040400000c0c42040400e015004c0b40004c03d44480d40107070a0040b42c141c8603285040c0d0801481b00b000701c1074002e00a50344050780c203030900302500120b0190070001d054550080c40309400980c02d41c0d05058221440034050360017070720300300c6545070070100958516a1201442003554442c80049000304588406160003814001e040d200048910750800d140c48801d4071251601e4200006103c114a041c0c0d03408001031126611100011020030031315030500310001c003454520070103080c041340c1504003941104c1c00fa005009003000369000340808030f01c1000007100c402689031002810030074186496050b1a200321801881551180c0c03c111040303019100b100b00100901070307071030340200307050a08205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 254507652 1250 254506402 254506409
    0x1424040c020304090b01050424030921180513020c12040303170a2003060a0e090714040b0d080f070606060e01080f07200f0106170d050c0a02011b0b01 66
    0x2d6403100e041042803030843e204683c0b10b5051013020402000b00004a5400c044000802e000c1005412101001034003d0710703680d1401401c0164413a680480c1c5085018016595038a0340d4562258420b81c0c6c00e82220707049a409074035444184070f1091071101c0c001d900240600084541a076000300b01b07450544001b40c219070801c030081000300c80078003844d05d2078002603940805880c1c1d00707210b80c4c02030005501d01e101c544c019a80c807803540040040c001d0344404910300000d001880c1407461a1510140041d11443c060141409105e001c10803008030749030601444c4010440180720200c1040300d079844545c15070003030244030201c540a109440100d451403080c0700052a00d1b0300d070055031b1300d101000140214401401c01c400340070b1110a0100303256200180048070403502450303080c51044105102d01d0a182503a0904d01c43d8240400030402d00c0c1400c1940c0c05a8001004580c500380c0b140f64140c13170901400c3c1c2c1d00c031540d912062158002d5031040b400b16025008151540c41a07089a445103031842400f6003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 254508902 1250 254507652 254507657
    0x6020304061e050c09010e031501170d03020c1b0111070b0901110303070206010b090d05100b01020708210d090501091b0f06051e040e01080706121424040c 68
    0x92051554a46108400100e0304070b1010400161400064102d01800303005103a0f8104484524802401d850801040505050508079a1074660703507208d2140c400444404611814010340c41c0e42c06103280a0700a5481807020300000e01007401c0800c0c00001e4900036002d00f44d04205110060440c1008244140c1c4c0c00361060303102240e51030309088009090703c042c541c0c0c0c4d1000c0340e06c01c0040002181e4007144290556884c1417041c1c0e52010840000b8540b10312580d405030150040d1500c0081007480ca40c440c95001f20301303030269201150f031011402d40300c2c805401c0d10707000814a04484006142c000c0e009060409054a0014104901d0b450781d074212401660304564011b084490b40c030700071400510040090490400003c00a424403000038194050840e1900000846000c0c410303510305001c06a40180010398a0792410351b03500c4d41d025589160034441c82003c07c3c1036265009031550b060003034083c106081e0380501d295031611080403800700000044000c4801045400034125919805080d1400c02d80b607 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 254510152 1250 254508902 254508911
    0x12020c01020f0403050d0215060913060209060c010603050c09010f0608070c1a1b1e1303050d0203071a10180906020a03020418020a1403181504030e0406061d0d0602030406 75
    0x450041d00c3c05034808000612008c150f81004825034650b48403c3e41b01b40704507002c105004161038480017a000384409a0761005004c02d41d5400c1c06815031120040f60b0180085039241d0510106002c105502030050b81c8181840b5001032050a000da05c00941202d081d18240e04003880945900507480300d0f800d445940030007120140245540c0d091800b0160f17000341c42641303107465902e0034805150700c1c08030004607060001044080281241c12501030095801c24155006aa02240029140d0b40280021520f4040da54200300d441504c0030026442020350f25000422142810a80300c9102c916901f0240d2250319500369000141c080c0c005040343c1d031030f180c9002d43c42d42e003402d800b0740015019201a221051050114424040d40045100d0001d502e44c090f40d543c949514500401500c4080c4003041c4030312903618400f07559000e490501d0b00c00e9009569017403c210010042005540740c0f4480c400004480c0500c0382c0016a2424020308800d074002e00c841c003041c0c21581c0f0601660812203094541c1540c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 254511402 1250 254510152 254510173
    0x6040b060f040b030d0311072915030604030e1f020706020c09040b0c0306030a1e06050108061b0309070f031a060d0804140609130605150a12020c01020f040305 70
    0x600714151007040754144401d4281d900480da45080d403000c400704050b103a2051424000e0648100d4201542000c00000440043c1e4401010200c402e041c01158051607000501d41160700c1861188101d4002d014000303e446640b4115214010301000300c0d44225054038002203440070800c518a10368894000d00f681d94900798010b4100021203485030700070300103081007000081043c245690301242c40342006440f0307218000401d10b881c0c5d1400d00106884032640808a81d411510341d0000707554410303c41440300383e0b200c205c801d859000980300e106014010808540c5000702170f101640d80002010101d615040d51100d140082292662082d202d018110154078440919407070880d91166040c0d809000185031507842d0340891042d841904a05c0c071400780310340681e03600c44080f540105401800d0005400c080b00220b03000b052140f16130352007480d0503c00300c0c1902484c1d5050700c0721980d09464411586140c104440043d602401d0956036030b5600b0410111b0380c1080303002810155024000500c51010b8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 254512652 1250 254511402 254511409
    0x27050c01080603150f040303020c0607090504050c04060e0103110c0703080301050907020106060f0e040603150b041422060b06042616050d0c0b1c14090c1005070506040b06 75
    0x401805680c004d13000481e80d00c49030524441c0140e00400b84900075071260b40c0d1810114002d01403590094800c0c000c42081c4020b01e584180c00c00d041e5141110b04000540b1115150070300751040f80300e8000401e50b207d00c400282d42c003039804071504010048110b0b1801d180024440d0400e417090b00102c40303c10010005100d9410140c0d00a68400078a0000700300c03c030b00b440e1000d8a010243c04011041000d0745209030310f1038840e41c201500540c0d0160700f852003200400700ca607000e4005940e115000c3c0d843c002c01c3e1910000d00f0508240a26140f2240c84440001128040040d020b48801511007940b52042c007012034848000400c010f203080c101195002c2d50741c840c2c07072212240e08880040294852020f05041807080300a802c1100c00442d16002e228287c1e241042d0894000d1340541c100c140d0205001040b031200b4951a5407128800208200c1e65004100f0410048025901a21580d028000e00415402c00301101945800076080a50a11a06603555071034204201d404440f5445044140301081c00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 254513902 1250 254512652 254512667
    0x20603070309062c06010501021c2a02011b02090c0d0e03180a09060506040b030403180303030b040c1b02040b120123060108090a06020310120c0608011a070627050c01 73
    0x8500217009194944130000390b407460486901d10344000500344041d09140608901840042d1600c15011030309111800c600740a401044240d0210343d01c02406120140d885107804255540181400840c0d143c0d01d40120054224207580c940055641c14100010f507000c001030025842451011507900d1004000d111808250381d00950344513040240600490340e44c4410384003521100909683c883d42d070303402e0840b01d00102c442c103002e4a00c020600802450782c117811009002000761020722460b0414101107404d240b00c00c1800156510003181c801c014541500054903d8000400da1441d406811003030300d08580a00541202108400b000c200000c210140c009078058407d090540301440e08002213078450307817001c5000345043d90001c0042d43c90035506400d8405415643c03800c03151101765240c039015a4a0754000c600c040340b20b040000441c0f032039101002c0911802011f0203410f003011030b51000080c01040751240b040c1800c0e41c10414035071034010361240c0b0050241004040ca1b110700800502001c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 254515152 1250 254513902 254513981
    0x8060c0a0e0a0b0706050a020d0510030b0106021b060702010c0b010b03090d0c0308040308040222051008191b0320090f091504020604030209090601090c020d0c02060307030906 77
    0x344140c403000c00803c400c10050740d00c480c3d005600860150346c0d00394294020300c00d900ca04000781d4038010910203178041d2010381e402070300d10841d40040941d884e00720036039658900d64000b10b8002e14101c60000300d030406202a200716403042c10600110000b550b580c0100c040c098010b412685400b00070007410110800103100c0c188140d04004081c5440358030001e0550500401c094140246da0010808640b00c1c0249034920301c40141d507260324480d9035001c600c0034240a8500c1002c001c2e0f40c1c080898281c1001c40c038211002c103144181c0042410070354071410810344550001000140e02c8800001190001025012060100f0a03d107951010751040168101c40034001503441c26a05040042064001400c0c15000c0c0403050380d800bd50b5035910002d2018451504000d401070210400d012090070001500e605a541d5a282400300415141040b650784000d5460040000d04c00b400d0b120241c1005801142c12054528010a0003045622050709031040204003002d00c1c00c4000744501d03036103581031250b40107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 254516402 1250 254515152 254515159
    0x1104080307051009030905191a090a1703040512150406020d150501090b070206090d030201020310060206100303050c161403070b030c0706050c070b0702010902131b081008060c0a0e 79
    0xa030740d030710b0301e000f440c0c12218090140034803180c16000110036440001140182555027841d42c1d05200d2174420040d03500050002401025488008541d43c40e41d001c40d0799035400b083c3c009604062401d0200120030b55000d42d00d41c11800f400c0403c240d600e03c46205da038070460060f8400b590f5640340c2e640ca00c089801c8600001c01d141803440050046a03070207e1000200c0c1c40c4410284e4440d1a40d00008500e88035840e9815170146c50031049c2c508158064002d184522244880000e116540c0e1400385d840300c0301181d800e26168181c1d902480001c0c041c4000e0700070400d428040384e1000c100094607804c6012150440d086a05e0703000d5011710706280401402020b0b01c01d040d0f00c1421030404180d42c1c200c0707000e140b1004098644400004580032810070a6603001504098800c00c0341c1844a07000c2d00070700c150f4900341d000e51864401003190500c140141107082c081030008000091030503a00b01c07480b100161038030a0301000070304000f8030000100702030750003016960070346581c800d10700c41e024040e0808098010301 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 254517652 1250 254516402 254516411
    0x1526090607090b0a08160302120f04170304170d060503031c06060509010e0609061c06030c090504150b06090d0b0901061d0c130e0901020304020f0316030f0611040803070510 76
    0x1440d03580145001d070000421500003446d0610401c0540103805001e16104a811603481044507609246c1161800b40c0d00510408c0880010554000b44c503200c202c0c1c000d000e0210590080d000302c0400801000341c02180b1500203030383e54a5200203803c551240102003050000c0071041400549180f042d07a00414490411500d0030781c0100000e00380c0016510000c1c406c04000c00e040389a074031188201c8286a810f80710051030b081c000c00080c402410a4001a201040b21002c042101ca816100b070900850b0030100110400134120444409040480d5100d07420032410311901805840b12031903540c100d48034014901841c40c00709006030840c3d490380c0c4160211140381d050201110b1781840155044007149038006d0313440080700306110440b07841d076000c0711552100d0401c12800310419030286004030b00c200c901c00707103102c0321400301680c4010100000306104185a000c100199000c1420a1050f1141502240c4042c130020754202542060707200703000a400c00150714082007402d00014281918040c800c11 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 254518902 1250 254517652 254517667
    0x5160806031905070f0602030a110d0c02090403020703050f010204140d210504080d03050a0c0908100b01030e03070c0609080f0c060c010207020d0303020405040e071526090607090b 79
    0x980d41c007050303501d20000b940424104010b226081c000500902001c910500203580d49010080da00d5001c10a904001090882c0745401203602042000c5150401e030b0780c40f0350a80c07c680800c410381c0800b80013202544035034080003000072414804000060200000140c0300c61401d419021380036155080c2603c01d00f8455010400540941050440400400c40000e080b2601c450b081d80c49104503001f06d425031040d510980707101641600b00c1c81c410f200850042c0002c001400d4207030b89016841c014020541c0050002003206005503125013101001450042a0001e894a0990440d0b01c01c02040d9050044080180440c9412145c0c400003480350400809280042d0303807540b5110210340e1100c9110380070004060000c55001d4040c0c13405c0c80c1e0000e0507141c0522082c80c001e002580070b4030800740101e0600c205445424004111101110509a4a0400c0c1ea01101c0204c0d200301070f489082a04048814080383c655101c007821900c20403000004080038101044050080842c50388020000b02c01081a030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 254520152 1250 254518902 254518909
    0xc020703051002160b13060c0219080f070f060603020306060108090d0810051009050405070905130c0c050f0d080c0a0e0d060e1009060e01060819080906040905160806 73
    0x2508444854001a116018001071300341503c8084000f0703098626038424045c1004215a80b0f240251091a0801501c105c114060340ca420307030b00f01c0b400c440c2071038140720b0000b250020b4001d19444081c4050b0358500b0007580d030303240d055400c002e105803115661418140210305003089150f0700b00701d0908108800e40382c400380107a982e00f80e440e00102040007a2001c103051000326603809000e801c000b002290074071015040188110618861540b0903401c140101e030106000f14510300a54102411251031241503840da40c0c09080214003060030030074000301e04000f0030000c1c4003030304002040744c0203442d003104108001441c0a802400780400e40a040242e810b502d60812618221161f09403404482440d071400c0c01c4005191051018145000d2403080043c40741c1c582d880001c801b13100d03c1c002c000f42c1110380403d900302e419034010090b0795031200302e1802107418404a003600162144141e2071030010800b001c214290866400140d842e1b4407882400350300155000302c4190025585492034092074010f000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 254521402 1250 254520152 254520163
    0xf0e071701050f1b04181a0105030712021608160507090605100309020117090a210905011d03030406050a120519020708070507030b0712050106050301030215120411040c02070305 78
    0x201c030050f070032140b40e5070b0a084c0b5606490007131142d240500001d0801401550140c8480703001c8001c95180789848500f20740c05541034034060b06e0079903210102d130380e0250350400080d40501c0820812140c440c0c40007000540e0b4030010507140003120011b031054409464400d1901c02e41d500480d0701c4900b001c106001940307511040c800346040078500400c40c034285000584a901280c2106001d441c4032400300301c1021000100140b8641c03040c0315a001000004510903d4641041c0001000504921080105600c06c0403035110504030b04c43c00c0c01e4600d510000107490b541c03207030344040089440404c03000d0510350081046160344210130814003491401c5154500d424100791000c0d40304035400f040c1042441a1a010394840b81c1e400350844420a450341050940f4100444440b0002208806007581d1032003180280c504032104d031b07241e090450342150708001401c05000c99440c0010703014803440b01c19070385d94a40c8038061030144ca501156941c42006210544405543d0141558001001000007440c0080c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 254522652 1250 254521402 254521411
    0x1021b0d0e10200616020102031005011103041205070501030e0a0b0a1104050406081c1701030f080f0a0804060b01031103040f0f0203030711040513020303031305010f0e071701050f 79
    0xa0642d84042c030307042c042c2c0e0124001c10288a91a03e000300008052a0008489020320745a001349140112402012402e078841182c48800c1044000001c000381d5010300c09500076410f6900c20380342404e840c0c00b6207006001c0d00746000d4a25a00c200400c00555070140306003196284110007500410489071144184100c0107056403410365580c0c00c0000500c00e03c6001e81d00900001403061007540e41e15207600d50760b0f4415801e40754007110941116800b85004d51075070310041100c0e0760140126840c2d501e0345500c24905401c25501e0443c10000301e0204145907009055074105500d5102044c20582080011100820401c038103040c40c090a120f0a01c013081e0a0320380c0154448440e070259001e82c60038884980c080f41c002500b5120120f081010807201000d1102603420684080109036244c501881726071007441d00103901900100041040322003005024014540180000704592010243c41c204461a406464031141c00515007448007490380054408150340c144000d0115040110038405030031030240 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 254523902 1250 254522652 254522659
    0xa0308030f2203091802070c0605070503191e031e0b13092f060d0509010605030601080a0512120c0a020a0204020a0908100c0206070e01031104030501021b0d0e 70
    0x41d46542ca01044091441188001450482d91500d80502410040c0c040c00302003143d848100d07511440544251407141340c004084450b2940b0b41141039850b54003940040d12640001c02c040c2d04864400c1014103901240399076100708510034445034480d03c2c1e02076100c00f4201420160806e0426545007009000c0301e5406800042040d44d03d17000400101498102c14130041c140310303501017802407800e006a4807541c0303522890440001700410f0318a810b0a0000241e0000091140c1036100000383c0c0429409209007000183c841d0310b44d00064034254003640044107940c0b003050000100541844051242c2c0c00c104c00403403d08001031042265a0390007048140003000201d807038400e0318800c012070041d80d900a481199100050070000f06407402c01e00880001c0d00c240419400c000a151003001d10504c01a405000c7c05e48030b22070200c40e410740e0360b081181015151001d0740d03140b03c0301070000c00041d8858400140e80d444a4143c04100a4102d003402c1d20941003220f00c2290150041640301411000302d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 254525152 1250 254523902 254523931
    0x2009070e0306070e12010603030302090310020915030c0c0a0501052d0412050f030703021918060302030606090406080105090f0a0309121a0426090a09090204021c020a0801050a030803 80
    0x180c089180101e500354005c00030341c02c24400109040d0950300400646900f58180c0740e0352400942d03014240d10540c1841d5800540504c100018000c1030409503070003000110745d981c600f01e01c03201c6841c60030460890541e61655250b09000c252078038061285294045409068210007030b03c843c11600e03440041002d000035011800c2004094400c4081f00d0103c07140c008030340d85030b081140c0c0080c001d4110040c0080000600c0381c3c0850b1241c050a16400c504c68000184850303942400303406c4020750805441d07560001402d101560542d95140180009002100000616407410000d502e02c0d005242028a245402c0084100046540100130703106030f900c4100c00700d80704c800510384281d150f8000c1000c900201140428441044415000c500310982c4085004071100c0c550018000d0901c240d841d0303180d2040c0200020000c51400c0e8009000e2135000800050914402010102007031140108203101c10340d0004000d155940c00071a15405002e042c0c0d90a194035046540c0c0c000c0c80d120180c0b10341c041c50071a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 254526402 1250 254525152 254525177
    0x3180a2c071b032105010e15040b0a08010911060a02071e090603120f0203031302040f061208190e0d06151a070c08010e15040f2009070e030607 63
    0x82070700510060701640550b60055030350034010501c4465901003081c3c0300c50250042d00d21426405910b041e00e06440c113510f10380e140c08400c9a21000304566058200b901c4088540701555040034140041c441c4600200e60558640381a80e10107c6000380580320fa9401c0c0a19500d844d8001034003c142d48842c214664000c000c0030000710214010b500801c103a9041c00004801c0041404445405040689501c2d84101844800381e84a0008642d640003003a000361a25002d89015003084002c90062100001c0d03898503030100312186015000d00b52090340000035101042010101c075042036912030315000344856048030001d49844138188014101e1034417540b00d18400c05095201c40000c0601300b817440c0103900c0a1744604001d40021030140c41c00642c0b4100040e1000041c05400120000040540700846002c000400390711000b401c00d440300c2600340001000100180240518114000c50039080c0f00c0a64040100481006001d0303020020000c064020729200014070b150421003500744210510310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 254527652 1250 254526402 254526407
    0x308040609050307060929060f060705060c03011503020f03041403120106020f010e0f0a0623010b1822230c070501110a1710030503180a2c07 62
    0x74805000780440c000080e48a00300805544011100c5e0311a5005005a108010081d00d40441d00d000a070700440103000094068030300030100550030800101f80c9400d000c1c840e00e5891030402c0440c0c0e88403000c20004018401500c00201e8007841d660545010345c038100c0f0510401045000144c801000c540300f03c0c08011300e07804c050060304c031400b000e140071840c01c2d80c2d01c1c54001e41d0f4200120000b4925442c00e50514004d03400030071851940c100d00f03001000462003079a10b240c0100f00005e060414807015401b00e050041056119900901c0c10034009a294246448014000300714401c8003481032031099400ea03500e850b09445104050140c0c81d0018010b80d402e1501d41101c0702a0703d141d00701c55860410031003804210800361a429025000070000c0c0e011901034401c080c403c9507030113404950780054a1504a0700100c0055000c03e0603100340d441c4599959400d841e54004207000c20400c041007100c245541403208243c001040c4820040c41d107962035010624928440c4008024251046800290002d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 254528902 1250 254527652 254527661
    0x5091911070203160501120204120f0201110d09030308010914150a08070f08060f09250b030c0c01050709050f0103020c0c0a170111071518080a0f1803030c03080406 72
    0x70b40203420b81d1000c00820800c0740c000040c070b000769800702d006400b48904d19646482624151425444490380c038102d00c2c0c884890002d6009000c0381008071f0b03c011644041400c1c0f00864a5600540720021024110b01d80500b9030101608840d00c07251130002000301e104500035026400c500034400004516a000c0c010828a804903007081070244aa8000014030307090105205084614003819210340b600d1f10b60702e806102030f041e12803078220b50100d83c2864554a09050b41c3c004100c0c51384107011540e42e203186507045600120303003603040118003103101100c115003801003551016280c40c01d102e06034200070000f09243d607000b15081c100760717020800401c03902003004500525203006008100c07007550f0b841e074140011000c4241e00c045500344501001c50b0072100043d039621a600806003102e2140c0e04091000070804003c416079101d00b5401804003050310b06000b401041d02594444840d080181c102802e08405280d0710009000400ca007040400c1e4031445803c040c50f81481c00c80780c1a241c0341482405003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 254530152 1250 254528902 254528917
    0x2011803050304080304081b18150405010909020f030606031c0e03030309010b1003060608060904062a1b15020307140d020406080c0712110a151505091911 68
    0x20b1000007004a0b00300c1c1c0000281040342d04003011181c2802d2100541d1503074a001a10540c0c001c1601e0440ca40088106a40240c0c41104e1a10024082c41010005000e48000380d21507500182c0d941c3c080000d50a00039540c41c04104140d00910780c9003000741c0413a40e00c0160303403040082071640c1c00c1c0c2d4a07800c0380b0449810340b800200408594407404e2107071115000b041e004e0b5010b0300c16844c030003001c3c0c0ae0341d01078000c2004840158130744042c15585e107403e00028a13401030003120f90301d41e1580000c15020b1800303a810600c0d120342c1d9542160103000392020300300701c403020040842c040c40c03c400702c2c001542851240c1c1c0c00c0c1d2007024000da16922a21016100c04c44c4884011f05000c85c0411251400328040e80604212140b1ba40e075080f0548400400c070f4002c0c403884c0000b418507920300e48015442c5008440c01a49620058200c50352518113480d1a02e519100003464100940c403103000d401404400480030b00909000ca96541d558144107a842c0038910019802002044c0c8400d11041041036031020303902031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 254531402 1250 254530152 254530163
    0x3090605041211061504091106160b01060908030d020a1e030203190e0307020103150906030b0f0c0c0319021002040b13090c020709020d06120b0415051302011803 71
    0x1401c081c80c001140c40081000d410008440c00b60b91500400000b60a80c040d014070001c241e500c100203014030006d041000425a41a404030800c2e112a8484500a2499a5140c04c0000465a42d0301d000910700406901c01000c0118030302d0184600b5202204a540184115600584c0d80d02d404105031001d441c2013443c050301c0010104422029900354004501c10340a161102e1245640d0041600441d800080520456842800941c006500030341c015281c481030501c841d51055640c940c2002030714081d800c01c44044980b01e062040d40b102031610941c00080c0d1800c40f6041c04201e032031003940c07401543c05090071444104941d41185000b80304a1600c0c6000725802d5559a4881442d8030340c42e40302942402c1c61130500307000000d01072403902c42c100c4020304507805071414a2400103c540a90045d501c500505075550720001102da10548803000594032629000d82d681ca41341c20329079100c8882402c41c1d1342850400c001c1060441c1600201442c09a0900304140503d801408090040c512600001c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 254532652 1250 254531402 254531411
    0x40605040c02030307120c0804020d032003040503071a16080904020310060e150334020a02010f0305040b04080708091009080d0915081f030303091e03020c01030c030906 74
    0x2401c940c040000c5200301c00545446072410107080d030050032280b411241800280c06207021030300502d481242c0405050281c908170820707039040300d64139400c030369580c142c070303180b540000303002c1000d0704041c49904010300001701d00c01524188a2024071a9100740c00c450320300020070030032040c2000541002d0320712071403014004544a1074001c8609060b84404d020740c10100d164800c20b0307030300c610701411400c208107030241850f4196100c40610100c1d0300ca1840752180741100c20304072450440c40c0144014030700c82d0264000c1141d08421b0001404000c03e1107180c1041505040400c80803c2240110701c1d08141d1001c2c00c1d507583d46850420b05214018448141c2d8020150755000301c03e250f003d49903c0030b681d08101038511196040f40c007501c0b2007880c2c0c4684485060030044040180d8004d43d2040c7c0d12546c14050b414039442078400c0b1188442480e0401c0700442c2e9190301e10b00500894045802181e424080d04e42c0b002c0a950720080d580781d002040d810304054a84000d0410244207800000d86998400014003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 254533902 1250 254532652 254532671
    0x30f03090305060c030123010e12010915020d0615090302271302010801080a020906092203270602060604090c050301090b18010b151303080c0105041412040b0904060504 74
    0x3c11781c2c030a01c11301d5042101ca415038a0802d000e2101002e032214141c44003090410010103005420540001d900000d5689103410004104112245c41c1840008400140c2e2802c082030b01c031044800301c0d000150340b9003850489410598000803100d05803034048880082103504001003200d00c0d452950000304414061003440a000800c40c640e00e51b45200341c964800ba40c1e21140015510045104040d40c0002c204011403800e04103000c095070407580c00b046643c5090f00b169140814003095a40c1180000c44240310070240c042000c1a80f034080c00d049020a110038030b0004002d54410020300380030b115030fa50b44401400c02080c404954020003016000b4007030100d03613051074070b41c4440440740410003039103950019070755071018403c404942400900060f07520710382d540c40c42d01030b81001d083d034080e82d4803007100400405c00300e03400f800842600c44004545854246081d0f001e03284040560045d07076110101708103030103405009540030f4400c2d0f0803109880c1c0d603112000502410076940841e400624015400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 254535152 1250 254533902 254533921
    0x2003090a0602010c02070e190203060f1809060609060622090c05070201080a1404030f0c0209270109032709150303140c030318011d1606020609030301030f0309030506 73
    0xf10f10044c182c003035621566455081803025101150868640c1c5101c1c0d140914040c0c5a502a5401080c0900940c4228080c031011480002c003a074100c00c98000c0000400100c860304200d00d82d40154203a44c16065424800f002c901107003d860010307110442c50404080c01e00c04a481c004000b09950a002e01c42036120315405000c2da480408141d0028411b01c0000751140d507540101d21085050024492007030307640b9201210002610a440030801c1700143c00c2030701594078112000e00a0000310914244181191008904030041106083c07260b41000801800300c0d80220310080c0240f2000c44d1601c0054a410894052514540010103064945081291818103c2101c41305582c800c1d00da030b0184207a00078a07003039240190301440045500070000a012000300c640d410228040000022500505800c12040c110b01140000107199100c90210401d6440d42d4074000001d20550010301045e00301160b20381d88a100501000e04844500c1141c03404040c1710303c008500550f004810744000b0b050404c011f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 254536402 1250 254535152 254535161
    0x90408030a0b0904060f0c02010e0c061317070608011707060305090c03120a0806031501030f0816030f0e0a0609030b0603160807080c090c070f020301020c01021c0c03050103032003090a060201 84
    0x1031b0400c1c00d240407803001d41c0c98014450340ea48201080018011854000304111040d84140203658440c0c403858400a56025a0003201c0f07409402030700600340450070b10bc8020b1151205901c1070b030f00c0b40484107845248140200703041094940514000c2429580c0c1d01100c1c3c500310200a10300c0e0544200c100f0344000b0780000c00034100102140c1d8a1a82d40e0702c4403010150f41d540d0704084540d4a580c00b2004200040090b12410001b42c0304403012800c1c07140310210b0f000d01c560400c03026000305050911480065501c401c0750000c0203000c84109080790301302403005216100b540001494170310384002054066508104d00c0c6c9030f80005001149010b034071100025155801e61180c11040d03c1034400701200c40c54001c1d071041c07254400d001008c0c10310441d6101c0344400b02c0d07050300aa030555820810090356800030700080191255103509081c90382020440c090446042c003030707500d0400d0320340801031002990100074070000c40c181d0051206000c0070302c5401e03070840c840c40341a10392103a6030000010754681c06400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 254537652 1250 254536402 254536421
    0x5060a150324051e030106032907050313060203180a120f090303080c071a160929180301060e0702010e071a0a0e0d0308060a06020c090408030a0b090406 67
    0x200300c400c04007115030888549110340986548580e50000004030b40b0032600130030040340c50003000410129505e484903001c0344407084004410f0305000900002c00148508095000743c0035151540c5580f4040c45101c1103c103031070400508041d000404141010344000108040c004c0343c03c16038100c1c136900c0c42c000c03282d6806111481c010070060b102100c90580902ca00400722a01500c64000c40d0740ca0301d100c80100d17403000400b140c1b100f920140918a10001c54a180e11400481040024002c041080946510543c2c0d200325081701c8580403841e0412068140001d40c1c0e00d41d075403d031740c4600d00084441410340410071826090b42c039100000508048403564030b0302130300320b0303070000c002100010b040143c448010340140f8120b0505d10211400424070f810007041c40000c1843c214441c1052803000400115024000b0350010340014140701840c40c0c0340d0881e500030040740c0006c104403480314000c114602030080015104100110010720320f18010742080d81c042c08000d080c007120b40350a1420300d004120001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 254538902 1250 254537652 254537681
    0x609020f0301061209020612071701090501060e121506010c080c0705040b030604020109031211100506030c0a1d060a030212010c02010506030a02090a051015050403110a05090a05060a1503 82
    0x49260313030032441c54402c0074040303a000744c291850b1508000b20303500c04003c050a29020804038030b44650511250515060203401e03030b05004501549040703402800081c0803501c1c244a6604506440803c44c4000f503008415029441078001d00d41da040012795280d00b01c11000303054018009400718481002180380015110100c4d400c2060315060030906540d00b10480d402404103403404804d00104d030f0701d0030404a142004e46840301000c2c00d441e41c85410b02c0400441c0408440d02d0340d041c44914078040c0711038246590140c94150388640780240601840c040e181803010b03005c200c1004124591120300041d0091034000d030080c0c0c080b400348007000c0c2c0200040805071005500e00008200c0d6482c001c01c1800001e5002080b041140d21140c95500c01080702602d103e910440411000035194103640681841400689519840300e2441c03d0001c0e80211a88445102d00c29044c000d01480d43d51200c00d9030810155100040c0070b0750354001143c150501074105000303002c0c56046076884290f1642096441c611400e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 254540152 1250 254538902 254538917
    0x503070b0a060b0c03180f030a1a01050102030a0801090c020102090a08061b030108075316060e0f0a09150510020316052b02011406060a0e040609020f030106 69
    0xf20101c1c0502d0140b0400740c0b100ea0010014010303162a50046040e04000041c01c0314240382010000a15103814800700711010800c0003c00c0c00c40d8581080c12038014802800594a00020f5039002000701c2014014081e603d07030b03110000c41c0e8640c401d42c15900f080e80081c0c641703000c842c2c541c041266a07080441d402d00a00500d04500a058820304064034100d4121200411380749041240c05000844034030002440703140d21044902031030340c2050000b82c00d0002c0940c11138161041181e11808160b030b8130030396030365603101e580c000e24000c7c403800c0a6021240c05140074220001908001040c00d0030a428503540040c03c503d010901382c1080d40044050aa40f200040a6076610360521203411401c00d6442d000da0018880c00c0c9000484c4803020080078450015580d1107044440e03010340e010002c0b29400d41b00d83e640044030ba0385c0c640900c182d000c40202c1d00030b44d003810314042d40015024482d0340c09034010442c010302e1200064450744c10801c082c0904a00c29520f85034240c800d010300c2e8209105140014090 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 254541402 1250 254540152 254540159
    0x927050f010806060d020102030322050a03050c0d020606090c030a0e0106060909140f01030605040f05071508010801090b070f1103030a14071815120516030c0504052206030503070b0a06 81
    0x40417504000390381038020314119034030022603050119220762030000f0050092540030001d0340c03e01003546414402c0e01d500703484d05210040307189481041c81c0c1c61010f544c403100500003140d540c0c0581c0b9034050301d0fa4101696a688880462000e031000d0081c2c00a50341c00e1400201e0301940100300720080e1404200308004c51070740301c4d02e0100241415640310b035048810074010300c04030f9026048982d0040c0100100c0103142d02555a9614100d05c45c0d0000b080341a07030a04461711568031105c85401012010020300549500b84c4074803945e01005050350b07080c40350709010341e4400d078010321549040c00c002d0400d4a4480c641401440042d0560f01d103035500703020700100003e41c0e00d07014512448030305c80f11140000300f2500b41040a90380510340d80c20a824458007400c107100b0308001c0d0141c2440b07042c02032100c269603c200704015041d9040c1010b414107000042c40f090020751a40d5418610b030b1240b44a2540c002040b502c5090014005504060494040091620240702c4912100c07806140901400c01c00b2a54 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 254542652 1250 254541402 254541409
    0x1202060402030c01320c240109060501020c010810150908060906010e220c0603020d06080c1507020f0d12020f0106060c140c041505090c03070927050f01080606 70
    0xf00c07000c08000c01c41c1c01504840c00ba0785461075000f0240c0030141c0174a4019400e5106d0700c0d0003680c055901c0044007440c120b903181702c0c1d02207085005100b4180240200381c00c0c030001079181c0386c0c0c12244c20304208801c0001030151641000460080c0710188070a80b0380c0c02c05200c020f0101c0d0352402030103198030841c000314401e00400140b6038101e8603480080007135a11015844800d10071028001501d4403071642d40500400e140ca404900100555200141e461007551a0442503410550100002e50842c16550780e075903d5405d610806c01a0440000b03903902c5072440000d4102c560b088030302d43c01c50001e4200f007080006058005409084da41c003220750001d992104182a81c005005440002d481d4a03515000617a00d10110760302c02c044101501c444c8000600440e040711105035050358110490780e800c0105007041945d191304100c4200c0540d246107003089000d03000071303098801d5482c031841a514a01512034000100c0002288140c0180841d00b4004041401c2c20420302600c4114000e03180410054503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 254543902 1250 254542652 254542667
    0xa0e06040509180f06070c050c01020a11040e0f060108010c17060303040320040c09060906030501050a0e070212030c090a08060f0a05060301020d020d09030314010b0f090103091202060402030c01 85
    0x240020503081c0140d0798081c501c0f141c210740f0348545040d4400c00c2d0b51481d002005108040c4145029511454006910f040c040e02e0001c0d482015419500100b01d40782c0401e0244800c60420031040d1800b1030003035011603240786401003074509001140038680000c201c100040d0480c11041d02596182c40003905040c402504488065603502d503d81e008110400000d40b004030f8031405110aa007603000c1203c6050042800d9401d440b8406c1c0001e2032528050004ca40c0180244000e0a0305242c100507541c10701021500103c0301c0e000f054089801c542c0003d689904c00c00c809040e42c1c0107030310820340368140b0045189558000007001c1d88034072000e9102007800240040c03203602c600001554031016469001e034110040c400641210781654082180300700101c20b40c0010849a070051400140010190600074200e0342c4c85a581c00401004030010410034041e0000d45007052425074a20b0350742c180500c0180c5c0141010403005084981c5440d01d00031146d00859841c0c8201d00036003d85545104a200440d4803e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 254545152 1250 254543902 254543909
    0x1170708010e060f10080403090b2a0a0507031b14030a062a02100b0405060604090209040f09140d050c03070b090c040207080309011a0603010e0a0f0608030a0e0604 72
    0xd45000c0042001074022030354250800009000c0384d018106002c0840d0440348528400404140c071901030004251340061a14011302d80c2e110180c1c18103000c2408100d640f2071204c030b0ba040b4030441560303440c1c1414040c46001412684081180c0f5025924a804220400d00c0c001c0d010295890300030015880b481903a21003c100c5d03004010b06481c003050740d5060014903001d020110741c124001d103025080d03801a00c42c040700300c18680007422000390001140061321645c40b609805207003000c05206450725180d05075030a48035519405a10741c001d860204006000d4103513603124090a181d0150244481a400f200c000c2c0b0200045da030048900110a5686208101c2c40c1001039004101761008078504100150700280c001c0e09a400440f4000c0008081e60010442520b5141000040c480802c00074452240c03e80c20600302c0500c10004040000c40600051060f4001201950001100c401d12a80420108403c00c034040040c691100c28055070394002508507008501034208281c803074a8044265004c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 254546402 1250 254545152 254545157
    0x8010c0c060515061b190309030f1a010b040e06010206010303051605030409020d0501051f020d0509030a230c0613090207030c050109120e01030c090e0705130e0105011707 75
    0x40c000e140d44400040c54024400c0c20000301410180c0d8044d078929004102a06003541d4503600c0300d1800d11441e0810200c010501801e4285240e6840000d4100f0541e0044a030040308445260180341010041e070140084490306010160b4004250036031045d000d0000e8880d41c01403001c01c2e54441c0c0059070f03991428040a808620140004198013804c0f54000300403030f00c21001d480c00d00340e482e1280400ea030000f1fa8542c00143d150350042c806403c01900e0a0444807505461400d4800c2c1c1900181d2a07404007820002003000000c0c058040e40c400b0802c01050301e0340320b843c11180095140d00072080040141001c00c0601031511080e40034584a02952000801005203102c040d282c05001c0d0001c0d408084110140901d0040c1900030031400e2061022141c00303000c000c00500d5490340c0c0282288008a04503042c5440c00344640c51007079120f00d04500351103282d04042d2003038030b8840b020f0350503015241600500ca800c0c00b1010504580f800c1245049034000e0700c2d51550042c0701e03070420780e1600c81147d55100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 254547652 1250 254546402 254546417
    0xf030218040b04060810020d14041109070e09091b04090201050f07030c0b0903040f05040216020d03050d150810060e1f030204050408031b040807061412010609030c08010c 75
    0x10300d1416034048100d24900420020310541c1c1c034501c282c1820050768000404550128010901100d50700429101c07910a03400d040b10751600307544080f042580014024004e1042c90700040079107000314040b07100841c0082c229002440c20308140c80d03032081c91188914060800e41c414510f1403c0074001d0794803c07541611200c5c1003002c604034000c8180c000d820305804100d060a18072022030b8010340d9a41c020071181001d07558903801d10700759410751005680040d02a40c41003180c1c0c0204054803440d044881d504447d20500d507a0a400c1c04c490a0007190f21144d040c40c50080102003a034403030810502150340f00c205807040003501080c400115092481030746890185200010301c01c41545d003801a0030302d02d100300748848944a802140c1140e0085808450b03110000007030003100ca080501007003070184500c481d0340c689400c00403401e4a481a6200b000240050505882c50100c16001546d4007080d010403c22480e6030b5030707a40240204542d2000355046031003054085002070042c00f900038821800e880e07654 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 254548902 1250 254547652 254547697
    0x2003100e1002030c040e0106110f070308040506070c151d0607030906120608010f0b13050624091c02130c02030306060706090204050108160b13030308091006150f0302 73
    0x40d5200504e9400807900c108008a0091511000e10b8007234111395503a03182000700750007034038074101c0003024108141d030003c5030400006444404031015944140d40c0d0380e032264072614100560755125080740841c5000e460500c1c5119a0280300b01ca000c40703040494440d58007410051200920403134101900150104805000c030f1030003404005510030076040b0005102d5510714107142114141034251103195141c4041c0b40040c41d0403444e0309444400c84104000d81d003880800910790143c2010003c504824084240f0030201414090341d45010000e03145001412501807000d1a409041703000b02d100c2ca11088140c81e0420f40c0384140d030f07000380b42030f002035207581c44000421030190400003041b5805621898071900584170b41c0186030081017007000400c01d020004180e410205078540003007400500c1070194080c0f000c01c805800c000c485e00f60501d00700b95200d26031103034280410807c0e0303402d0250a042d80024421081c60300305000d0b14682c0d450704000c021107034046060b4842d2510a0398034420900d4681d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 254550152 1250 254548902 254548933
    0x50307020603100305030a0306030b0c16030807170a051803120a0b0d12090e1302010e060a050408060103030801050415030506040b2805010503010b0f150706092003100e 74
    0x81d40c03c511116100d41e0703220380d25958036145070f000d1a04200001d071500710030010003040c0040c203608801c041200d98284180805c41e40440001040c02504105d40c02d00803030301c80c5000c0c45041c01c0da4421300261401902d00803040c440500004c1d2901c00c080c4418600f4030550798004000d45514000310601400f0382c3d201c40c9403000282c1054425294414105a11f400008000c00d42c07800c00280c641d10f076552034524281c8800d1064400620100f82c0c0700050801d0700050b0b0703000000d24003e010032200c1c1603c4154844040750329006130307080707048140708800005c001d240d002503100e4105c542c01c44090000203c40d02c0d0b0040064030710301c030082007544840c000ca0002102d402c0305981c070a4103010042c0c1924075418040b4140307405c007100300420a0307039100140424102802942e10081080c1c2e10544414005000f00b40f100c2160032580c800810701013140001c110460b00a050055000b1002c0c110b80350030760315104141c0c82880c048502c41d101e03000071107403030130001c0c05141800704030100179114103c2801d541 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 254551402 1250 254550152 254550157
    0x905011e030b040c020105060f0102030f0706021305060a08190b06040e0403020c03010203011706180d1202221e081209040b03150405160b07110105070b071e0c0503070206 75
    0x2140c05054454520b0784058031144a100c5540d03046a001049074180001440010000695094115001004a0040780c01440d0444803000ea111a0040e44d43c11008944502d200c1c15400c070503403101e0002540c1c1c400e6a440f241e41800740143c81041e402d902c000d010050b0440f04803100d0076400c19070910040241e500b44c10281907126000780150b40e81b10401d000003d003240c0c002d070041543d030240c03070a100d40c0c3c82c44104076003a48280d00d00c515205c00402c1c0494980da40402803c140200a25181c2d201a16001501a1a086185002d00c1070b040240d103602c40340204018040c0301301c0d250180c4945084500a07401c19801c03540d87d80c001d005030700101001c040c01f035841140744c0b90b0082c1c1c03110114202524100807040400e03860b0bd4400f401400d0510300242001100003071802e100f90101d0051190301d000c0003c5a6155038064008001844042c0042e0b4041c0121000507104042041c10000003e41066800900c0701c990340c44110003015182c3d040d038511951841c09012644240859130060401400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 254552652 1250 254551402 254551457
    0x1201151209150e010515061606090804080a050d030f020a0804060b0d02180115090303080609060a1511070f1202130b0915090604060503101a150903060106090501 71
    0x220a1620016104844107560f0500c9096089a41d60b01c1045802103c02641354102c40c403c0307030228030340201c0040210040d984036801400f40ca079100900400c01c46d20310202c0c0d00400c10402614401074107414400d49a613902044800828148640e41e00c48402034400c0301e0451a4a8441d0421500da9884903001481d407a030341950419640014080581da8002c0000c0c20038102ca540c0c620158140096101e182014141c08010f101c80c1d00b0061000a41000e403003640044c00351602e1b0a6503840c0400951f0541c070700d40c4291042d8070003000040000354404801c0c03032540c0c00501101e90b000da4410109000c660103114000022240444000040c40c258801d200c030b00d0445200810b04d80c400d4400604988401e41c0d41d01001001c502054405003040e46010342d000b04115802c0083c145088086916020402c080400c00c642e03484424041d00c03110514031000071005132400125000703074103074140558041e06540e0310900c182000011100e01c120b074030b40f040d1601a507174014034001c0290089108682c149 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 254553902 1250 254552652 254552663
    0xf0e01030e030721030203090a0323030a14070f0906030b040e0712060f0c0c020f24040801050a0209211507080103120f0f1b0212031201151209 63
    0x18400d00329070042010b000141c3c054082d0000c0d00f10520100480c6020f94101c2005150046c420081d94080100d00c03400c10030340504018010b036489081c2d100107022942d00c840541d07040030040c494402c105500024400c1b02d03070740108a55860707920080d1500804c0d803000c400050401781c2c0c28041c440c800d4010000044000d003000c03d090102d113140c2810803600360004000300792424120030500840b0300440c0c40d0803900c294100020f10300d8034401888508240030280c044c0429a041e082d80792501c54600001c43d40d82d510041d400c040350300081210764030510a40d0502c0d82044046030300321502c0c2c0b00b1100103070700047c01d11840104c400043c80c01e0114003030085440e40524814214400c448410142c400c0b08a41d560268a41c19440c1408240c3c170080c107401c080042e044000c03c1003031b4100011700e80d0090a070403c00c004044421505031300b81c0d90401e0087d005135005c400c601c15a48008060310384e1107044446510960303201d09202034022082402a00050b07090400381c41c003402958800c0e10824042c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 254555152 1250 254553902 254553911
    0x1206010e102a05010b100306080c0130020903010e070e06090402150a0203030406060602060403020c1203070f0503030a0c1d100314090a0b06010507031d0102011b050c07060e010f0e0103 81
    0xb040d02d03403294100550159040d035100c1a0134032140c03805030560300d00603d807402e042000504001e0944e41d5049010042070621040c1e9058945074095200b0380b250510000040c0d140ca52152088040650014401c0da0701039030230911392890000000c6590307000d446201c01060304541c0c03810104030026201900683c0c00c40070f0101c806a0050500c0000c2804c01c20940085603030741468589001280c4080e0300040c21500000240b20010741d001c03401080d808421a40d0b10b801c000c0c451100760440c428528024040d042400c54002000000700241d0702c50a0780e0442003140f81b060500c140c500c9851035814a40ca0158000d81091600d0024038040c215401890001401c0c0304854541d03100c60b005441c0c03501d0542c003601c6500d08101807030100f981d02c10002e2904906003c0e40b5a4080c003445400c01c0401c03411413007511103c000307910075407052030105203950b4034800105059001505560040302c80007914092210302045c0035000e00746100c868001a940c2c40381d0340301c201004550520b600d020b401d0415468 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 254556402 1250 254555152 254555207
    0x1b07061b08031e070906170412031a1201090c090908041502030712110d051c090204091205030411010306050603070320030106210c0509131509021206010e10 69
    0x2061941c8513910b903031a400c0c442c50501c0000f500b007884400244041840d44000c00c80040c48010410f007180c041410003190703c220410205059030b503071700701c11600406510501c1c07445410540014880c45d000d016416101c584820011090394642c182c09404070500700301c20003950202d201100e00440080c81581c0c03c00c0c4840d600c80000c2c0c095020384034005486043c0304020014188a0000c040c0006d040281c60000d1503d02c502005003854100140745a40d00000801c3d522244c0001080303581c0209003601c01c100c120005000b5400c02d440030b0303604400703202c580c1c0225400317031096109132403000700b12a05540d920342c030480c003401c0c0e45a421600c0c68a1020f00042003194240910701900080d01c0b50280d4520800100c4c01520440300c4480c1d120b0b091402001d0f40c550003038100d400b40b50007965210301d100a12102300000c1c1000c01303500c0240e4030250400107290041680a0300504084562070096a1601401190001804040325500c10100580b40c00e0041c083c240c400280a410040002401030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 254557652 1250 254556402 254556451
    0x6050d0e0d0302071209030b01050d051c1806030e03070206090d02031b190e01171903120b0d1709030705151b07030f060209010e03031b07061b0803 65
    0x616070500d00402d4002c240c81040103c4680d03a480f003071111380b500030000c520b1a00d9001220704d040c803c0030302071607954601100b400803d00c0282d4291001c42284000d4503411344008108001c0301c450440500d20094011401034481d001c0d40c1150040e0800442c200303d0b2640810040380e200805042d4051102a04140161418071410075000107a480d069080c98440050003800f03150a141e40980c88101902801107140307000d001810b540c03000d02c3e20b1300e095803683c04161400403006421003410355010300300b50406a01c4014040e5000c0d1080007401006001414031000c1092400001d0020480c0102c0020131b140d01070292030003c4006040390012075540011600d504035003a8a035400303c81c00200905031441e4030007108000b0342010000c0603020b145403104c00345032882c00c03401042c0a13000200061180c2c814481030b42d544200500f52561240f050303210712001030b41042c8024040c00788140c0095500d00403580d00040722021060400c281455a66044440d80000c040d100c01e0044550080f11288 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 254558902 1250 254557652 254557663
    0x1050d0603150f060f0503100218150c12040b09131e0b030114010812030a111b0f06070e010302031f0b0309070e1302040c020a02040f0f11040b030106050d0e 69
    0x1820b0700e01c00644252540141c00a9a40980005124050000c810007198034006040c40081da800b150058680f103014101c4400130420814482d400000b90b000c070041030101308c0092400c07a40000488a0740c0d55440c80c080c3d443d018610034108029002e124400c0207050180405640c603180010000d20401c603841c0040b48240070a940350741e503598034051080c483c1024401e40320704e000c8810160451790715100515a545241140d0b04031001e80c007001060500c1410f81020302501c010054141d2590035000c002560000c4044842c80305100c1c00c010b0888814021503400e000341011740d00c81c41c0400300c80005401075400517001076a00264000e400b41503100300c188170b0010b80115541d00d1780d0b90510840031490812a5003140d80410303280c00c280102c248686002c06405581179401080203028010241d0406034040d802940150900d190130916003240d6020300b85900026a0401026440c0d40041c6a01d002e14024888807400030030041c007005001e48050130400383c02c4100460102d044551460071300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 254560152 1250 254558902 254558933
    0x10e0609030403110d111c0b15011206030b0a11090d080703020d02010c0c02150d0905030405030d020606030a0b09030d02070c061b210c050313050109050307030c0501050d0603 77
    0xd40001c60300f40304105112401e00364400382140c2030a0030b241c071511000017406801049900c034401404a0060400e0746e88900c4030360b00c0d00580c44040503c0e1070503031688a8801c1040d901c1c0024950040308070440b003640304000689401c041001d0003503075412480300050a404000d030303a00b400b050026071040e50700d403074208180300c0c4214030094030b0300c10310320b0b01a2815100b10070358020340e4181201c20855a074032a404040301501103845029031102ca090014151140e5140400c08506000c440e6080c80400001042140e00a40c100da5941500b0380c4103d8552034152500b0350f254214500500104a07220200c1c5d40185c1c03108242da02e4119406030f00b00c106d9010300740c200e440415801080040765000100d003c0c10034030341400d0030940c3c80280d51714490300d059017404030384000c00d55003000314040c0301d0a03c000a103540482220742c0c48503003400c04aa00340b5180315a5000449400c4080790314100421202d0480354812088031401d400e010040d10b2a801407080c030808195105800408200e81200c0b00b03141 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 254561402 1250 254560152 254560171
    0xf0612010f050411042904020a050f0d1a06250203072c0f010302060a0804080f0d0603140c060307030b0f090411010905040c05120a0e0d080708091b0d0302010e06 71
    0x1800d0951040c013091b511099505542c202c070184401072510469410340106040456005aa800211105544034004c1101101e04a1004281131944a07120350041d603403104488021100700541000300310b800e20810a00006001d205100042a1840940003c100c503100409803003009403a14050500748101d50f60b41840466003850084c0c0510303d440e07289811410210703480301c20390b0564021070309a00c0740c003410074104620200001c0920240b034041e1418183e50b40e00c0786907602140f042e648050480c40c04145c4000d081c0080e15024400d0002d008048000080c24141c01d40d9580f210a60003808055030050b04458071203202e02d190742d14084e0b010f226078424412101c0c8040414001804c59185402050040380b50895040c9026000340c1554141e40c4000b210345000d650b980340724005009120810301e00c80c8114038118000b01d80142030188101625680c4044030f58945550315034481071421070300b8413146100e1041c505030815644040c0000d00034000400c04090200c0c0f0780d4580322048520141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 254562652 1250 254561402 254561423
    0xa0b040515070207030b070804030905120304050f06070f15060506070c060201140c0301210c0806070212040b07060902040b09090601151e03020703090305150411090f0612010f0504 79
    0x11801d10108420307009440d40c4014a520b9003503030303165903c8860140c402403d1050f160002005c05100c0c0303001a01400b0b014080d040400d270003180c1140d40340c000b409407510403001c03403014414508143c415100000d0b0450203540100509448496281990407400f00c40c950322408007140c03503140d480003840707400d2007150116401882c21100030300b101c05034106000109040070501030300390743c401c0960741903d80c0b004184412001409490560b90b50900000706200d00b903040001d2001c0f400315616104001980a0b1209107a0020400390144181d008802000e6028004c04020030401e900074950944082c1002410414110000344d004108031644100c41d44888010b00015154154030300c803806850825a142d450b141d400f002030000341e07214480c00c042e80400c0340401d02d0f1042a20400441d046000d4a1008641c01001c110034401141d06a620004441c010402414001c1c01c80344245818016220742e0f498003001c000c0c0c07007512940c0d40c901540d01c03082410071030415849a68001e80c0700d00307031621 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 254563902 1250 254562652 254562673
    0xd050a0b190f02190e01411903050a0209120a060605030a0201090306090f0f030203031b160b07051c0e011109030a0b0a02040b0307050702030c1509120a0b0405 70
    0x281c6020100780c0404500502040071000c144148000360080710341402d40442c640d050040319440c02c4190a0718941a007c26031aa681303075204100701050445004441c00c010064110389428894507220442590503980324100c074620079406030ba0010b003080c40151800d10181e0004402219002404040f50006030106040000c80e100c0d050050500781d000e01500845900041d2041401d44409440070703444501c90070810040765080002d4550241a04038402c040741402550703604211101700c6010250034030700645141190039548504404040040908100d0391307807225a260180c400814040140200844040d0354034000d50701e000301007030004051610100030750940c0c0b18280c80075034a200401078510151004903d00c0591500584214a1622903141c100002d03c52540702c10b009550100510a0055000c4010500e10b4022130441e072181102030108401c1010280603411244070401c07059002c0c2c18041400d24981c01c18505803001340c1e81a8507199400390040798125a070b40c0045200c070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 254565152 1250 254563902 254563951
    0xa060e130501050d0204090812040b0a0c08040c0b2209020703030501050405041223070f0203060601020f100b0a0504110703080903120103060f02091809010606020f0c0d050a0b 77
    0xc00140d00100400c1c0950352401021034090b02c070107240a03000740d4071401c2600c1070101040c1110500070701111051b40d03034541410240b00c01c0e035054402c44030550400c6e40d85100540f08424090180b5004900c19000b1480c1c00ba22681990001510071a1a00700e11080107201c50221002e5004008110000d40c2e1100c25107001806c40d0016046248664500814080805c0c04c541c030f0507581e41c419082c40700e11040c040d1796861040080c07843c1c40094034000900304041114068102110600c240c049403095102d01005a807101810018400c0644c000d441e910781882464201c0c0c400750310042c2100d07601c15145d2003c00c05030b9640310390340340b039000c4006107080c01c042d030005c1425440060500a142424030080c1019000c5a0610000e01440c0d00c84525020035252541210001400105a03008203440519203581c1c1583c111815040c9510302035001400384e001040d14050f101c00c0d000235114424000c02000064812183c0c20303200c510a14043c100000c14920506026001c91103456401c0e440540c1403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 254566402 1250 254565152 254565169
    0xc0c0705010c0507060f18081b0d0f030f050f12010e0105060f030f060a12121e210603050303240d020904020f1f080604060602070f1505090a060e 64
    0x781081007a090351804034502040940075294035181c202ca03800180402120350050380c0c502280d4040100d180054080740000300054003030060410180900c005908004a04400c00d40180c03209075403580d10b40c0020301c1841c030409140d46a0074000c0c109616040e52601503008a5a2084141305050051085010080e44c150060800b210b80341d250400000c02d1014600000e40a00c001700515000304099a844e5128400a80400034000c407150b0b501d410042422801c2c0d90a01c1d02045680d4060700c0e084c0a07560340b11403800c2591712066143e11048d100249288118221000c4d110782d20140440000c0042c0700650203501048400825002c1507008803402d644001d12940c8242c0e24400b0b9400180c8030686416401a0100c03841900c640302a030100e1b094101c40421000c888440c414502c1d110b641100e4524002c1000703580402c00b071a1648402e0b070b0b50318143d000781c105582c2c041c1c408001c408131001e8000100d480e149803007410440e5100201d02d051030386800104c0842c0302e25180c0a0b2a0514a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 254567652 1250 254566402 254566409
    0x60b07171c0e060919060b0a0b0f0d2004050114090927070f12140609010903090503061b0703050705070b030103120212090105070203070e0a0b030607300b090c0c07 72
    0x58080c01c0781c0091004851115840c1c02400291035070785050003542c2d22003540d80182425040603035100000d16104400ba4041100c0051140c60018440c000c810b480340194800043c00040c0e07031400b41000b006440042988001701c00c461010410341c03c47151113640344940500d09504080031400c00d000214a06901707907581000c0694007403001000319600213441d00d03046520041000f06404c1c0749081c200c003141894440b4000520600040c80440d240540c03201c0c90a074007950300c1e01c154540710801c05450b20300a8558014903c2280d680101101c4440014000c1e14401c1c10100c2c6014090390f9a03030f0030508164808040004040010400d200d4100e454030509803003440504015620021042c64034082d4110080c108480404c1c8001191820000341c00905140c4180003558505400700c54007521100c400c0c94001d005d907001040140380582400d440c1c6c005030803841c1008160940b00c1580c0001014107030001c0d613461b00034602c41ea45480c03603c24003072030303101c0380b00c5a590800b0340d4468078040582d0f2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 254568902 1250 254567652 254567671
    0x21040902070b040221060f090f010507111204051e011704060c03050f09060c0d0603211106010b03060d02040f0905010b010318050309060a0201061701021309060b07171c0e06 76
    0x24110090400400c43c07560101f401080c41c426510381040861400030030440b48802d66107000140312000f40c0104c40c003c81ba41c4410b04403080d50b62200ca625105003d01c0c0308094209018508504541e0b00c0400c0d200390005041c03401103900075415500c0c021640094034140c82003a91014006040c9038103001c0d20f94044590f4900301c2c01c0782494a88150b80d0ba0300101424020040445e0f000c5103101143c0101d40116080409170142d0b452441c1c0e491600b144000b940c00105e250110034409243c00803a005049900c86905203007107944503800e000d502c204110b03040780d00c20340d240840c01100c00a403003195a01d074041c0000151441a6000140c00c803135202c002d0707807060703460740c1440c8000400000480c0c2e910001a01d413070352035428076001a409444180c001612a43c5104c44c1c150b44400154094641268003101840070fa03a52070311004122220b5016602c4407000c20844400400d40085025003413082c40a802403600090071610201400380003002d80d80551200319824031307104100b00080d040445034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 254570152 1250 254568902 254568949
    0x20c1c030b031501080d030b040b0a24090e010e0901150312181a09030a050d021005100614130e0c040e011a03041412040e0f0f06010221040902070b0402 67
    0x544d4884c1c460f1b00b0b440801d80c440750b00c031130745440b580c20001c8452409080001041d4890030003801500002d074000d0029040685040c0225210700b06501c00c944141c81145116401c0000c0305084080080400000d5074031442503e401d00054030600d40114000d05c54413450a03040c0c100100500075100f84c204505145010a216203e13019640b00181c030002c80d1683d40c1d4800c401e001c81d0419110001c0038200d4040c0301e018000494010861824200c00118104a15915011100c011281501400000440d50321101e113203140080018080d20058a0301c40c0e582940e6010103035580709080351180c00861001c20b01700b014070f40a46010340580000340003007000c224541d030444507034013004001400060750800028019001407003540304a070015008259100c2d103c00310030546c0d0030f0644401e010070101400140c00e21314007208246c084e1205034090409002000c00400c044a85032441e60800c01003000300290f500d01e0b5100400382c081c855407004119241c2401000003a04a120b0403040c4000310 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 254571402 1250 254570152 254570159
    0x3060c080a1b120b030303092107030813081e090a0e131b08010e030306010e2202390f12040e10080f150702120d020c1c030b031501 58
    0x6000310290b21041e20f10306800c2540d030500e008005000600380c581d030503000020521881c0e09000c1144c6d48004580040c00380c031800100c006842030301c80d01d007010307001550060100306842040b03540000c41c2805142072505010040c501c001c0020b5980500c80d0600d1070002e05056a400c008004400900b09608039030a070346044400c03450140b0b81c0980041403441c00b0b4042000c503442101c1010058842d140c0200701295000007825900c4c0d00680325940415280b40c13440c1d48034034020381300d05280b9032181400c40d1081862a03100002e07401c002e4a008010026640035400111101002030381020100c002c3c80d032042d50104085e06143c2c0d44204142180c0000d0045000000c0c600c0c12a0112010040c00800b269074580e000b140404050304054054040c0030801915403e000a003814101303034988a05016407200f1401341da4441d805441c51118410500c180b82466071164042d00d0724580a805881203601c001c0b01c0803002480141020000c00d45d00c0058480600b0704000513441c03011040c00032040d5504 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 254572652 1250 254571402 254571431
    0x100b0a0e060703032301091b051e0d15030b0106030203220302030d0221181b030a0b0106021c020303070509040507021e010902030c03010203040b061504030203030403060c080a 77
    0xd00000040c05007100080d0503042510941c481d01100f01d0071101404414041c44002801513401c0c401c00009030705140b0054103d8a01c2e444105050140e600c60034606800c0141c8030104980d1a807840807a840c044c02030241c0039010b4021500401c10340c1c81c045604a0540c03511040c00f00f010382284080501c1402088918a0414200c100c0100c0010080507600c01034902240f5622030250f40344440d900105400c105040408101030b0b0602c03030010a420290f40c4d20303c0c0714003101c0104521860f80d6220307140d804143c08400c0c42811a00314054282c84502c03149455004580c2d900b81d0105005912010f020300081d42d225031520b4000943d840554914101041c0040541c0102c06885120703a40c2d80021170005402000381c500b0a80d4a9468011074590078010780380208800c600603402405240580440e5180610840e88190762000303120034240c07245820f0000e18244841e2404101301d0811020015a034208040c2c030086100d000c0219840b070031000020081200a8a210039841c1841b0a421881c10f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 254573902 1250 254572652 254572667
    0x1103070c02010522060903020f0f06031f0b03090c010914060307120e0a140c0301060f030f020307030f050105010f140946050f040804060e0f03010e0105100b0a 70
    0x50702480c0060b140ca01182c411000c00c0340030344071072482c0c01040500240d059005103a25080301d0080310002200d15200b0288031a0010002c07216070711802c1080011450501440c200d506800e81c1d21200030059103d00ea00c0d0b6090703000796114402030f031000214108942c3d100550300060601c0c041501c1a15041c0f9000c240c00b0701018182c8020f01c0184c90320707500100190303800303807c1c44884041129001071040c14501c0c01c070500301c4481c103502c0c0140e081c0c0400741d003014040c640844a9541000c00d900c0d1035901c4e403001000c45034008981c180142c09000011030020000301100d00d01801c000a51035140c241c108940059070360124622500500ca004000da0f591103580f94000c008036100e011120318a540c010941c0346064402807510740003080a108491038450424035102550030402180c0c582c041015900d10048a00a090081c10041808814840c1c4003180410748090100074446a8140001e42074a6004407403603000e031354500c104441e9047c4000800d00411044200600c0c204030f0b80d10041c0940c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 254575152 1250 254573902 254573927
    0x120f2d0501051905040c05070210111b150901140406181a0306010c0201180303050c0601090501030c151202030c070c05010503190515040c021e0102040f03020405040c0504020c01020a03110307 84
    0x1da035280e13500c151b60f500400440b1a07041d40146007444010b00000083d000c2c0690b0003840c50f00e446a012031b07004005034203880c64442030004203000c4004c602200020107d600a121290401095029400c10f0742610030180c80541403e840c1c02c1403080f01c21049241403143d41e40516001500009030102c012002400c43c1c0d0005c000f840d0140d080041800140c5016910440752880c00e18060f40c0002410381c018003814076240c5440c240e03840d60340c1c1c0e003800105480c42800003619804d00d0020801550100c19907544510000d800c10717000c01d24011f103240302284c1040781c00c0100058002449010041661000360160109080c000d0460270400c2e0402ca0050366503003142c002d02d95031800304e1044011075900f03000d4450300900c00e01011141c500000c0d1030781e80214400346901613071628942284018000d0703030309481150044200c030f185035030200405064044c00c142c0342c8481c004800f00747c90700c641c00101881c0948000240e0388481102004088908178400c0e80840502402800041944001041d249 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 254576402 1250 254575152 254575159
    0xc090614090d021306180f050109060b031f0801060b0a0e1909020d09211b0f230a051605090408030402040b060c0d1808010903120f2d0501051905 64
    0x41303520b6810b50300d004190a800c21208004403150250701c41c0544c0d0050245007064080504c91030340d8400220080c0d800600416408600500005c0e41310401180c541c0c1c550000c0c01c0005050035500c0b8180c90071108150800100d118001078081c0085800420700500004291103404400342c2e040441c004282c1903004081205070001681050255a504510826504400c0c4100c1d2058988a416a0103081038800d001252150300e0040c001c1d40248950446141c02035488800100540d461514201c0380c18111512011f442d555404401810810b41240038401d80042c01803944802203121605a81e60013213104414810400c40015400c0703081e0ba81007503060744e01242e0042e1040c0000c0f406e0144083d6014903114401c40c80c5207465000403c1d000c001da01d05a0584e01365124282103083c1d404142c0d02070003240840b03a040304130030080d500507845254401400608120000144200c14088811800301302120030030203450045180b0516004020441c1c8520a401040c1c1000c00010401d1141c81d11 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 254577652 1250 254576402 254576419
    0x11132c070e011b0812100e01080d080402120a0c06020c0303181306120b0709060c120f02100609050906131208060d02060d02070b0609060d02130f0c090614090d02 71
    0x4841404800c2903503983d0007804d107a140d081c4400c03101003018088a106ca1001911140004d94000c000750300c17410703141c0781d401402942d22603110236614401c000e801241c010720b085091411080d02841520300c01c41c4a50021440140741410080c64105040b846c41e1003a042000303042054080d840d40c0366144141500c2540c94246449030000040106a11620901c08003404030010000d28080c903911582e8603460308228282c40301401c9440c410304e03c40c0200102c0017070940e07100b090b004148142507035a1078411684105610003488041e6901a4000407050744ca07541400358841060002e940c1c000c0e601c00e00400305a10342c2e220310040c0c0210605200a000c1c01030003164140d01c403040d140c11041c0d0080c1c41035558034802c480a000a5219020588044080740d0204809103000488680540d000030300302003840384581c00300004410403003200200240e4400c003420580c2d040380140c1c4004d07c466299284410703e0090080d050381044c0346550101d14007041041c106907100c221800c40e043d016591030340c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 254578902 1250 254577652 254577677
    0xa120c03030b011d011d030d0c06050901050f0604053c010b03090d121803092d09021602030a14060708010803040b0a0215040c090e07030b0105010311132c070e01 71
    0x11003980e986c8190703a014043e2918600349181c1201b1034680e13991261208002503522440b00030b08a640c1071f5113010240403614081580c41c0f509410803034001c501c41c1c00500391418101e40240307039401088028404402c9418482c28100031602da45401000c3c1e07d02100e10354076040c41c1454a562070941110140110049496040074190f40081c00303009803a2034901603d64141405000700c061232051300c5000e60241c0c0c00b1540301c120300c0395110101041101c1038a405003440b16000207500841091b07012060082d0400700580c0d03040108040c444d0203003ea03840502c984554840c01c1c6074008040030117014555004120b120400000c607000c40700100030071902c0700c1c0d00e404101d06120340c2144d04505148100701344070070300400c40594011190041020089500038525164540003141b00151014082000420055009410a8160711402e0801d40d180496400300005420000d400940c41042c00b500f80007000310080340003005099402d4911141352074010001080120070010050412a0745900d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 254580152 1250 254578902 254578937
    0x4030305100f1d091b0906030c1305040b01060f050d0c1e11071403070e100b0703050702041a0d021002160803130e0408070807050a120c03030b011d01 66
    0x541c0503000e24125040030315552004200110002128100c1d0030401c040800d100080010341e13100e10582c1081007008000c8170000304800c0307640041c2020303058001c10310012043d69400700036100404810100051600386070902c80c100e510143c102806000c104580d6400b2642c0290564051481c611008150103601c4002280c5913022082c1601000c032441c4c681d0403038250821140088c10700c1400c00c0300c005540e240b00742c2c505c0b92140314510390943c2002c1400c0c00300802004c102030780700070100d04508065595241030071103988101d206600141000c0350881c02c40c0b40c140280040b5001003220149207140700c0001801e0002e5102000f440f84899403541c8001c0c50091214888142c0c01d1484809043e5540e1501c0303840b070b40300c055034001d80700102001055452100d2001c074082ca4226225a00f00b098550720211103900809054400303100e240c03060400640341c2c6022600071740c619035585002d41c2d65450041d003501c0302003041d20b051181001441100700b2400080e446d2035103091800c0c426000900303080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 254581402 1250 254580152 254580181
    0xc04030b0a1e2309120d020306040902101d19090b01110d0f12050108060c0708221412100213090507020d0917030a050703030e060415060603090b04030305 68
    0x14010450420080030a946910403c40c0c000c0c82c07110340102d10036510041c81903210038000e0f5040d00300a109000a548958440e0b01546d4043c20152000030040615000100240100300010002422850a000e030b9185c0104860040960540340f005901803800181e4100300c109001c0c00b101c0070b5541c00e0310035a80c2c0c4030b840207641080a40c0c0560300a4003030004002c003003032450b040c1c06001c01c0300358400c0c501124151086904a90007240504190b480f440001c0f9055441440184c40a160900072490f00c0c03500d0092148500708900c0401d6242803400102400c01a034801d100e43c420070216110141140700400e4030416000c80c1c0700016a14200b01f044400d4000454011007035940c40d09040001d6582c00052500b440c01c83d41d113441b4120b640d10680e401d5101048410001c0c2d503013050066414031800f0300007400407503201341001f149884070b0880440c6031100440301038891411030503108440002c5071084001400d414902401a42c0150701d5070350f0244406070004042585d03440020b40c006051180c1d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 254582652 1250 254581402 254581451
    0x3030903121118011707230c070504050604150603050c0c0f0106031103060709060f050c0303270c0904170705120304020a0501110a0b0414190b0c04030b0a 68
    0x7400c12582003030001c0111141c00594241e0b11041d0000e504294660044580e8100c0b80714007001c0d8070b45079448200c1100c0140d034010b4100c04100344070800380c0c21414408094400ba121313001c01040b00c0d40c03814040000780c4002030a04c500407813920000b0280d1f0002c105d510001d542c018207000c1003e40b1980c5107640d81340f0445003151054010f05405100d603c40640291080342d004240200b030a408070410140c60314025200840410b202c0242003050a014081584100d11603040c0300382042a400da4140c1107034801c440c0b0300800c403120311500c5000805411038410440900c0004d221040174031001c602c1c0c80401510107846030101516000360b2040c241c2c1190358140c2c0c00000e4540801c0110000c114941081d642203120b440354401c0458994807652103050358551000090000106030384480e40e810401030000d6540a885203103d985042c4200b044010801d401001c8a2409401d42071685440ca0040c0000071011001c21041010450100805402141490300050091010030302ea201d16801e0343d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 254583902 1250 254582652 254582687
    0x1008070504181401050a0e3402160807060f080907030204020415110a02060409090f1e02180105030c100e0a0b031e0103021003020a03090206040902070311010501030f03030903 77
    0x4050018000b00b5400c20218440120800d00391641ca40d4204103500400d8007079071080341d0b00ca60001c0c685241c0200400005a81c800c5800700d488458500700c100ca0101d10072410169101d81140082c0c1c51516603040c1c000c1910a000c1c160381d13401c1c00c0e00104001c3c0070f100c41e0006c02000d80040340761454184140c03401554028002c41d90356a8070303403250040d08100300e00c00001c550301c65002d42c0d00d00000b00740e20801c0d9500819031444d07c4d08100d1284001d10002900f5a03461342407243c103000203003c0c0d5000103400b260390244440c4442c036910402c80138410b0601c0c0d001401c0309100040003c0d031000907084480000480700c0c000700c482d0030356084884c8410078000701c4d440102214000303010b5000c8070046015a5020005281c0b0030200314031003040e04000e2200039003200d240c02030405054413a80c050a40c104403480c02040300f14464000a80540041c0c104036415036002801000301a042000d0517407195500d0300070300c0b5541c50740d141c07140e01c00440034014081c907860380c2d011703000c141c8550302c2c4801641015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 254585152 1250 254583902 254583929
    0x23060408091e060408010c111f0203180d03051906050901060f052205010e030d020a02040b0f03010e0105180f070303210e100606031e0e01060b03090d0810051008070504 74
    0x14940c00e07002e441f07041010401b00d804806074030500c1102160b04461650440d0503110a001c0301c202d150000e41c002410840352003240052810503610a10003080d02102583d400b2409080000000030401004004509424075040d8200002c2e194011904e04640b124209039a0101000205561500c40c205000510701a03007690701c11030f8402d6103540e006032003080c3ea030300d00200c6440d42410f03074500f1102d10300c03005039104480d144014942070304091540c00002d442150740711420350229003580d8940416112030b0351034a0401040c5080154002d03451101c0380b00400b45c00d0a183c054603200d030035a00018081120701100000c2d4002c0940c041000d084d1079190810910855001c200d444d2a500340001902500f00b81d80012207511901070381785114142c0c580c9440d03416608a090008040c43c0c1e012544554841c4030020b45c4100a40281d80300c2c80420000e040c2ca1010746800134601c0710002c001c40450501c541007400141c0350840d1010f0010315500300390032540c5a0383d400383c2c0c5901482e8007619958001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 254586402 1250 254585152 254585159
    0x506040b150105041412010e070806241c0309030f0b1b18120111070311121e0703030b060c0109030e040507020307020910030f23060408091e0604 64
    0x10341126074407500c010039150030700c080540c00446852203070b0f1281300e13020f59940410125030b00d05a54800c400e001c1746000083d1100306c040d4000e0504160364040e8603e50440380c1048044c20300401d0604410812a030070720417001040f0300181150041e441c1e4a00e511020054540030035020b00c085802860300040181e002203083d03d070411110300c0c1100c074041c640802c02920328020290905413540e4040041031a03100700210018400d1207001500000303690341d01d80050b015402003240c01000994001d54030b100e181c14840900c6840c00104034081182000d041225070130104104150680d240600c01c660340d0b40f014181000c0300a003000146095106800042c0c520080c001507000d81c440601c6071b10762641c002c1f0340400300401c40d10215081c50241e0020002c8000600d4640b0362168050b0102540e80c6210352241c8600b0715241014030100d400c1d4130b4000b0b10714002c0c1c1040030840c54404d503071401404649815500c0d210b20780a040341c034a00544c0004100c4003080352408110302c1d140c01c0940210b450b941e5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 254587652 1250 254586402 254586413
    0x90b06040e0a0e07170c03010c1b02030a060e0c030d08060a0905041505070305190608060711150a091502090d1104021b07090b01090b121012120305071b020609010c050604 75
    0x2c03400a584444c41aa85c61b44d0803401c042c060041015010780f52103421640352060310141c1c0e0f40c2c13401c0c100da02d8095519100d00040d410b11400d504511094000c00f00742c2c08610906141858000220b030900c103103201000a036540300070321442030b60160900400e880c4c40c0e52911254024416480b15941410142001340095041c1e10082c818000c0c2c141001841c11381c0301c403100072102140580c400c590840d10024804601072040b4400e04002481100c201c6000d446138040611030503a66070003583e494811102c140920304440c2544141d00000840c50111039200080101645041c010034240301d011b4a59081d580715815100d84a2140080e0300445120726607068680c0041e010301c1e00309516143e0741e200c0a501c20160f00d01a10703485c0e46a24a07000c0f100001c40e46109000f0071075520b140410b04003040f070702040650742c00c00c18407440040d80710001010000e42592001041a800c01c804060344c006031107a94186540610317019181c40d40c0e13428024004031426504510050007510038002440100702 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 254588902 1250 254587652 254587679
    0xd05130302040c270b120402030f070f0e180607120e0a0303060314030f0315040605060d090515160503150a17010509030702010512090a02130213090b06040e0a0e07 72
    0x68095141401350348810010146800c01400740384017001d014400fa126902c40d0403d0325030414001011918100202e0000310310308016500203000f036802031201007000300361040c010354008041000303812140c07800d030310140d80d81c2c0700c001c100e9001c110382c3d545000d07a000c24951010764081085410398554036003505000d030140001d48021140c6100c1145101d016960203c1513400300c0703806500040c03942c0c039190b1407003029076500800694095501c0c0400501a501c010003402110500f1401080c4a40c490501a08082110054400c11500d80007001000480c036a03007960b1614640c02c12135166200c0044d141c50705220112002d810032164840031512045c1590b1485400c6840c0000b070207070343e0300e041030952079001310a8002e002c00c1007400650044140092469070180101e011134841100b29000503a40c0000580741260096000540d110400c00003500000509084c403030602410100340e010581c3c1e442030740706050f03804c858040070450114080c1c000400724011042101d04250720f9210780400e09 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 254590152 1250 254588902 254588927
    0x30c0d020f0106031a100503070e16140d0c0203190507120509010504091d1c0e18010306051f08030a0306090b0d1502090a140102120c0d05130302040c 66
    0x14400d041d840580400140500c2c4180d9500c818018420040e401d111582034401428a107001c0c80c60910105058500300b2425004201c184161080c50030509c445485144458013810104030313814490800005080d4204c0b1041d0781030140026080006010484c00c6001d8900d2aa0f4030b22403601c100101d00d40d0002c06840d4142c010000500d03c58800c2c10180e405102d52503400e17020035803c0c001007111002660040340ca40802841c202501713900840041d003440955101000171100126009003d21380c045a65500d2080036103004071400c108040501030b400c0c0500c4000c00440c3c5403c00a1201d0310301d04081000c0e41001c001d880b005a4031001010b48a802010000c00003d01d0078400044540301170185030080100680700c83c0820900380c507040a0300f1029100c0545443c1c0030441400c0984560748200300500c0c50b400f00480c0304150344002810260280b5a22031500b00c10b100e482e840f0b190224000320201c1042c10242d50f071b9401714192590504081d88065806868030070512002c0342c2010200681 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 254591402 1250 254590152 254590157
    0x10c031103090d0f0308071d0f06160303061e030809190305030a02010e01050a0203010308120417040b130e0705032a0301090506040b0a06270905010b0c0c060712120905030c0d 77
    0x345da480c240b007120542942d442450308da00b00181020918100039200035030a9a003d82010f1509056400c803c0c1900c40800d401c8001a0342c900081160354000010301c840e550310010807000162a544404030346000700012984034141010f0004000014400400011540102600e4840601070006030090021420220195080200084212029108590503260b000c40442e0030704641841c0303046183c1c0001c00c1124080050030285907840342040141c0020108090640c4d91041074071032021a0a4080e44030098100c0c101c0240721a42e50090182c90740660742c0710240e04002c0070030000c0341d039444e0805403181440c24000008903624045030851303441040c003a101400341000000501c0050b21075482138100040001510005503100071403000034116042078260358998850381c000c0d0807203900b030348140c405010008103500c0e5203000780b245101104044035180e041c04a0f64990410900541e0b0030702e4200b1038003c80305464694203078459842150450200c0780c80d542d00440b0365603580ea0ba858003102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 254592652 1250 254591402 254591417
    0x9060108060708071d09151e012c100804020910051f020c0a0b0403020a09020405061801031e1e020f1909080a0606031e02010c031103090d0f03 63
    0x14500400141140924502d550350529a95070150481301d00708551502c40f00c58024020001707170f0b0ba46101c2c003c0d0003036210300c6940b6101d00d216420401d10701c0026402184806021286d40c0e02c582c4c200750702c03040c00c49104100d20300505003000b101501446843e489039102c170320f50380682c440ca54040e00c001c1c490707442510031200b0f0f0707240d0800141e80d00490344902944a504c404480d284141032107500303031417882030b401283e204503034040004005811603000710b428507001003810025454451a40c50062a002c41c0440ca800c2c02d100101e06948201010b40d4084a04a1120681c0f40d00c039034040c5103003034610111140501c007001d4a400260040c43e10400010507040d4151021860718400c80c0c40346085400301900d89562001001124180f03203800e84240000712400044007841400844040c0c0d21501d80000d8040c00c40c54010003a204200214803c0798040d461000140d800104d503418240d0181018102400c0200c0035500e9071103481c140c03d800941d07507000001000044c030140f0038843d20030346071601f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 254593902 1250 254592652 254592659
    0x90c0b030f060118050603040f11090c070f110909060106030c030b210f1c02010606030903230405040c1205060d0f2a06051308060915090316030206090601 68
    0x806000a46408504451403004103480e98040c4002000b482e0b0106501da21040d030b60400666150002c80381a038189441a041c0000c0050b9400565038110342122002400c2c01c1107040f00030035002d801c000804000c50844540203016084040700c501d540b0042c00c40102e813810301440c50316488284540004242800b2500f5031541c0071340160101d201c0f001c0c062035062801c0540d072010039080c525044c00c007402451a06c01d846002440043d110b0b1034442d00d41c08003201c55210003402c41e00341d541700310100b6103441003480c0040e50000004010045900002d60311019495013004284284d511480d0b2040c68103420949440c2c100d02d0300003010ba54841c04015969404050150381740343c41000070003d00d41c1000002c009844402035407140740c40c4c015101410303550901c1c034161224150300300700302050002c2341c40c90303801100d100d420016045c0d001c082e0005003041c11015555040c00e480f2030060122000025005c042d0400070740350f20900c15005801c2c5521641006501d038902a198600d06005000012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 254595152 1250 254593902 254593919
    0x11090108150702121c0603020d05060103050d0c17090103060f060e030601050913080c03070c0303031a04060e01050616082a03040803040302130b09090d031a0d1b120303090c 76
    0x40c1e0405264203851034036980d001940e0703200322540d4910251710390352440400540c41d001781100c1d5040c0306030300400107941541412482d10051003001d01c10080072024100000d0407440e48503028440e06c0c000540c07150700b010b005a018010310703004038116103041c1b0800280743da8006146568420142c1c1510142d0b601c8030700b81300d1125400c540401e0070f0000e8510510001d02d100004004050840c010f403810007599683d030000186040e80141d0019071540042410f44801d1801c1d80503194040320100030040c40c00c3c0001070991814400c5910620021590b080360b901080280440035a104000c00d545404685003000700c564140d1540001c0c0c0e0219000603508580041102c00b66007001f002503041520f50307404c000740e184203d015004002d450b60040b940c0e0362140603805004950270009051301884454006040381c5d10310a071041c0c1390828865106051701c5107040b600e0003603000003541d224120901d041101c02c4001d503010143d03012440c41403205155051303104ca90410301c100c00c80b444403952040c0380c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 254596402 1250 254595152 254595163
    0xe06070210060608060a03030503130b010905040605070203070c060806030f01050103060501060f0c0305090907030b09041a060303120609070c05060108010b0109050402030f15030c030111070b0f010303080103030c11090108150702 100
    0x2550840c0e0b4611047c07000c21f002e0400795510007010911090b02c501d082d96180026802a4400f80b4110346410a1100300321b024041c42c2d50003410f610095050100b2505c807443d91348070605c10386041c404034001080741900c0900008151207a020024001c41d607481c9443c0008020900c24107000681003410b40d84018030445840b01c2440e00360352480d081c07000b803208200d050701e0301034603c905041d900c1c040c04010340c490014403841917020f2461811124001c00001c202c0c401c009202c1c0d482500200080c103800d9514258a03900043c043e03401d52101d546d80141074800800144c40901244038500002418840542088820620aa1313a010401d980d40b800e00c4181d020648411440300d413180005424404054000b15981800500315811100c0302c801003400c50350034030710102ca818400a6080305015620038402d401450758100d41c0d00c69855900c0c020f004600601004040081401c514824072506200c1c803560740320b0013824011304d940c1d52407010f6503e0300301035100708410151000050b0983c1c00400e8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 254597652 1250 254596402 254596411
    0x14070f020f09091c090302040c0509010905011806110102120f0106090803070b0a0209030703020613050a0b0304121202071e050d0f050406031d1005040507080102030103170d0e06070210060608 84
    0x2c01a10080104d078084104280358080c040064071100007003d6503c500903075100000b907443c0c40e6900d040c07060005000b029540c02607414044001c440707945c40ea080e8800001150458600800301542c0000030501a20904c1c0104160843c050144007042d44008201b5040740c0154841d030703450554946400c2e449001d90310300540540205400981054200e03002083c90140c010b06641c0e250b512580000d507680c01000c82e00e0b1079295003076014001e03820304801c200050800080c01d1760961070603543d5054010200703a903440802030101c0704130004a4998050303600039540704100c1c0ca403281201030307880d5101040010940f540d00c00c0e00300ca500005e0041441c400801c03a160f5540d89004e003405015400b411001d451580e40c1004882c00700c0c040f0105210f0781c403035241c40083c0450f01d0f0425040040c60074605410444090748100010800245002807440c550503400000703545850f081e0030f80b40e008216401c0f90b010140548e9003080038141d07003c0f0b400d40e40d17a0f40c418000c004030798890f50102c402c040d0803203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 254598902 1250 254597652 254597671
    0x314010e07021c050901201207020d0605160f0c03020d050306010c1403070203070e190506060405030a060b091609030206070602300106050306010e1014070f020f09 72
    0x400500030400c0c10198654001c503240101c5035680040056005140310410404002440c046031401056a115030042d90342104074503440744440e4484005900d8030b41140c400c4e92041e1001035000d0440d242e074044010029003003542040946007c102d81401c00101200302d8002842412410b440301e0b003d032072100e03500c0381c05500910000c060950103035025480940380a040c4000007040b0000559008032a104441000000d140c0710480d504c1414175001903900583c5c0c0b42003441d800c204410040c4d040314034286454602c081503d0701c841c0c010070000e10940e080035030503000f41902c21050003102e400c6008001025a82d688955407641002c00b4071340642daa01100040c0b04060810161903e5409020103500640005140c0107400c81242c1000d0b01c2c030b0580e00c3c4011602440280380301032404d08240180410300b4441e185140c000300091007807084440c0e66200c0d0700c00900c0401e007240b007526042501d465002605603030b840107003480c00c1e14a00c0c448040344030320b241c50100300f42d6003001d00c0c466000342e0000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 254600152 1250 254598902 254598941
    0x71e0203070302060c0f161b03050705030c0a060f08040609020d05060f0604020f04030803151f09090b0d060207050c03030a18121211240a0506030a110d0c12080c0d03 73
    0x290710002c7c0f4040c484242c0344140e4200714086001d09031030555005521900051107038500c1e09041c1401d0042c0c0d0b038010b0344541000c400810000b50010040c00320f186044ca414002c42e03130385140c6070000f01124800a5000f00c1c0c0740c030105040000c00150f4501034640148841c1880d911102003000b41e200d6101460071815040c0000c00019a41070007442c3c000c503519000201e61a00080494080810b03070f00a0081c984425840c0003005e41c0040703140014280702c81d0b080c0700141561001c590840c5003603100500c03a960000d8941c0c1404030900c02c000b2078000040959a4840c3c250000420300d0310500910811001482c10000e216018441440d0100783c0c800910585800e00c4401524003100b140c03614042409068042d940c1c2e034150082c03000c0c440800d582144ac1a0400d100060110786005001c00e00039131001c000980400c82c50700b0400034402080301c0038400c00106140105a1a031341d82d00240f0401c1500a4010030883c081e070140865800150440741000c50034201102034640851800540342e810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 254601402 1250 254600152 254600167
    0x51f0b1606060b0c030304031404210311071401020c061903051b070813050f03060a0c0917030405040e03120a020702040b030607020a050d0f0206010e071e0203070302060c0f 76
    0x1552500a40d550080200103030803540c80b5842c0c00103a00540d11803416800c000f08100c101038028001e0324110000802070b50825003408142c0558171210002d44c41100062444d103010180300d150700001202c0118141d410007a82c84841c682c4d00d41011000a0260189040d00100b5003071000c162860018045908034411401c510282e004007000740507800325100540302094010075210091401d80e104104c2035507500c2050030303684500b4100c0e40140b4400e00d00c490110780d4947c2c00256a0f81c0264075002c00181301484028180c449204c19440030035100c2c0c0c92500300340c00e0300020000e001100c80a540900c60340b10780d541d00c0e645a10071030442c9104008003030041000094580d0240a0941c409000042c0722102c41c00007901c1c0803022100840149c0c0140c0b4003900b080001e01040041103c9801c02188028050300b000c2d458400c140074201c1e441c28207500041c03407148501165240c00b509001046900003400b08000c0d140e9000b09020307809407190b8004100784103010402c07202400d14580720036040454 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 254602652 1250 254601402 254601427
    0x1e0d0e010f1505032a0303130f030b010e0403022d0a03020a060e03090102030403060b06040308030f180706020a060b1f0504080f06010302010e0d050709020c1f0c08010509040c1206051f0b 82
    0x1d0700c40781103801d448188070488040ea025003c0c4805421401c248a0341248ad51405150620050b0400d07081000007109003c00250001082c40e00310f4402d1009040c1c80540078044c142c08407219403039028501c5500d40314000d241e00850031080302c500502c4203020940b10f04031520364030f200f9080304174016401000100081035950748030200411004102910b000d0380c0c1d40350a4055042034502c8000710854005109042240002e0640d407429a00041d09801e40380c40c0c0065111070030004054083d640307030420100e8650f034008440886c522040c443c00985298031400074015003113030203142c181d807090780090707031b40340c200020001d0480c1c4e416502d0007040a80760091060040303003480d08032054030440314085060280c500103416540c2c11000144100140100394080e40007943d40e00303604039864404010580350307001c12641d064032403e4800601d02d0b01c0b546021f12004d41e19034840f080100c80100e1030b100b0842c041e00300c9402242080340081c05c001d41200401503034034244c450703038407000c5041041290152 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 254603902 1250 254602652 254602723
    0x207060e1c1202181005040905270a02060d0e070e01090b012a20030601030629090604050c07050303040305040905090309010917071701020406080c1e0d0e010f150503 73
    0xc5da580741039410175070303241d00c0601581c4080d910205507000420818042c100381c074100d1801c80d90044010146c00d085030300804d0041c031a00021050043c0c489030021400c003004c1004500070000100103c1007580c2d81d0001c81c00400901500d1800180c100030a00134108270071507105007010f40d00e8006400300301d1503503d42c642c40340880074084002c2c08035211401c3c199001e000481c002c0d03001e000d0100c3c2207252070092002800991060007010804d03c804007486484010f01c0c02c2d0f000c0310580780051203480d564107004040c01440310060651000104100c20182c4c484040d00072511042c206100030384882c020b440d00e82c041c0c0c0030072500103070510908006c07001500703914800e07181070b50013601d0407192038548031610506028042d940740d17900041c00b007044030317070211626900081c1711100d5030400241c40742c21103025000d40a6100c070507001144110144c0f01c0355100c44100b8035448000c12904005042e4440580000000b00d80600c9440c0070005060071b001c2a40951240c0f5441101940c18112449030010f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 254605152 1250 254603902 254603929
    0x19210215151008010608071b14190f051002030103080d05070e06040306051b09010f030e01020d020715140601020a06091704030c0e0a020a050301090207060e1c120218 73
    0x8030540508001030300e030744861076048202c40d03442100560406030302504402c030240c0607104014109503800d2400510307821940c0046ea003c0a2403d0700d0300000302489c504449100b0029890b484101000d040007580010074030700900c2002031320350444002c0e47c083d0480c003007403002500303002d4104a07099072404141d1010b0f80c4030301c6038102230342c0074442d040114286400a400854119507240284500c400c1d50350400b1601e044d080d0409417a000111000034030074451a000c040906888014049002d61300f03405a59400510b05000c540b562101d041c50401d05180454982e0303803601d0001000032007000610080e10031441030700100400c040599884000f000076040584074102a840750011007550100200300a60040d10000343d030500b00309420308246000b030302e0142420310401c490b20241d604031003580d044980f28500107072210b52a04080e8003402400744c1c5400c040c040c034210710a01402d40030411811004660761000b0f002140c4261008910401900e044400448000e00390305207400d18844450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 254606402 1250 254605152 254605171
    0x603040203010e03040b070c0801050c09010809010204080d0c0605060411030c0a09120506010303110307020907030209030a0f0503030a06090e0c0427030804020f09040b0714070519210215 82
    0x1100414003c007400c40e04650450014514001550003d01c0035a164400c00f50042034001c000b0380c103282035045180c0c41910715280c10302000000182c1d50080170b506580c001c0040005031052907080300d07001820440340c0002211540e1410020400a007403a01c204032944900c158014510b441d21480560560013000c612010070008000100da6013040015003d50688103d0041000754150320b0040c0c1101501d40406030b0541c0103220000240e070743c03240040d4126125003001651110890042410030602a0000e40f00d03000350268801000b100200840c4501414170302045043d894120480039140c2c04510125664000e03025440e051401d94000380c0f864540342180480601d4406803054540300c2c400040d03000c250580108801d504002009004d5140e04964492503807503d0380c0c0758890400003401e62420030400d1141c4264003640d00040340c0303005820200300c543c0c4940204400d4134030340c1c200d0740446080f80f080b0410b40c84180d100304405480300040c1c02504221500c154009019070000300003501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 254607652 1250 254606402 254606411
    0x31106090301060902130815190b0603090d090f0b040905130f1a0c0f0304030c11030a111005070f081c05072006090a0b0a150f090c0f0e060304020301 66
    0x31680e000d1061000500d0405070150301d410b154901e8450040f0140d02180041e0812a81c00d064100780d048459032110030b4200540810681e01d8080009051312004950002000418840031010001c0e8129003940b444d80c400440175101c82840545810074410540f80444c180300c280103202c06900080e07408555208000400c40e2940c54540481503110020741c1c6000034104102c010600411a0a91104801c001c00345090455800182c043c84010700103070030000c01c02060b4080080c1d1201c010718440c0010103c3d1602c034294101700c01e884001d141280e22890310216000f07101401141910042908002d40402c40d2119403966000d03a031260b030313000d8101261410b0051041c90544a650300031005661084582514441804c4000440a084102a5001c42c0c10090300201c000744c1482415440700101580751907003a4540050300ca00031510018000c49440480d0300e40c1c1507070b989001c40d11080414040030442d05010b031611111910300300002496141103010a0504e103000390b0b0041d201800020b03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 254608902 1250 254607652 254607667
    0xe0112020904021605060705250309051504060810080604150b060415081b0301050f0f06070f03021501080c09040515040c060e0a0803030a050c1b06040209010e10031106 74
    0x20201c1c4d00c511814410080b03401d805505000e010083d00343c0c44441d90a14074503040046041d800703a1400c040c0962407000c10244000708052203030611000505001e02501515000002800d032990414001c2c00b00184480000a04a803400d038402c01c12200c19501070300035501c407500c0326036509005604401503945c94036108803c82d00c030312005000030008440c4202c804c044074040240f0702c0c40082c0c6410300c0c0c110bc034041d00745c01034415002c803070440380c048400d8950070301b0035000303d4995100c0041d00395100e903001c140f20083c03181c20508403034000d210350b0070b0381e50586918941c4201540e0038023540d4016408500c1d0b01907141841424250020b01440440d040c2d040b2821001c01000001c6508890300112590200305c101e80040018881040c121228034140c0e044c44003007503584c0030042c4484280ca4407080070030348002d1882c0c12101050569011075004440c1c1c00000c5940c1d49066404034050000e1a00000d0040c28644199000b01c040c0b500d440920351450300e41105180b801041960701010411100c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 254610152 1250 254608902 254608909
    0x1802040b0906300106080601180501230f04170a0c15050705010f0b03010c0306060e0d03110604030c030e0406080a0f0c0f0e01170c03150a020714011506020c010e01120209 75
    0xf090700351003c02e045401d030760612400420303d1a01a04560501840031198551805043c5404059800a01c0c281124860b00d891014204c1a00300c4000010310780040c030308150400640060041d1544140f0f50303150f07080d184904a0361520540c40c050004440c400b0107000c11503c200d100580c014440c9042801d02080e070b00c7d06402c407000d030011001000d990307440c2c2035590700b000e000d040c41c20701c0750781010490700346801c41c06005080b01c419510b1033100303405400f00406000d988848030781e40d03042040756403525051502a00d10492200d0980126081c01c41034013180c5032034040d03070040c0c1c2d05c0003001e000c030b111580e51610f0481d40c1e425011034240024801c045000f41650a01d0001820580200d1046500d400400a0329445080e01e008290b0000348402c1095100040c0f00404407400080c010751030b540703440f0305000074002c0ca0b5001b00309141003600c0304285201500444c0903064200c0c003881c042d0741c0d244001d981c0c3c0d510702c08020740800e0311035109100a40c02001c13920f50080349010050302c3e10f0502d5001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 254611402 1250 254610152 254610217
    0xd0209091e0705090d1403071205070615030809010309030215100e01120b060d06020705011a010305161d0609280b030c19020c0306010f1802040b0906 66
    0x254596070035103103030041022030040c0c41d058110300c00c2e003030161030132540b20007084050343c0d80c0c00c0190401550b410f546e00504030401c12513410079004040449401c0c607a0030000c080342d00c120700640d1450708000c2581295000d042d02e80c0c048a603c54111468404004010760103041e842c4019025402002c400440c1700c049070990700e100300561007003903c94604085450307843c00c406809c10407408000801813400600182400f940000086030804a80d5900380742c410041d101d4100020495400c24403003030446508800d00c6603c091007604d0511041d0744556800b100709041d200940c0c00105140d50b01c0d100840481c40c3e02940c036602400061a0070002c401003a21174404103007143c244066142c00126141c180c820900280119071601850b40c2084100c48641c0d000b24158111052505034440c1c0d200e030700030402100042d10203001d4540569490907541c441c003025100d682000000141810200050740c401c42c0c3c1074641c03a00340d19041c0a015010301685810222003100800e0903429000b20840407003d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 254612652 1250 254611402 254611411
    0x70b070c140309120606060301090b130204060201021305011d010f05070c0807050405130b070e0112180615060207180207020307080309010906090b0a0f200c0312031b0d020909 77
    0xc55981c01e050040c0000c4c0d1125084c80000c641000c02030160655030142101e0445406d1480441c02101000006400059400c484450148006000a242601900a4140d0402d09501d01c1e0707803035a58500560349561100f45800070712610b50316041d03056000b07080c0c00300040300700d02e4190b05002d40f640d6122500c0f82e817500001410380c00110108918a49405000d901600441030a40d214003248d0710188000d00140c485e20034400c0f0320031128a213034443c1c01e641010342c503014400d000d1080484026014042e2417802514038a0034244000043c0741541c805204071400d660081900324603180c03000140e10340107280c26040175000c020100240c0ea04000440103040c40030083c40d619100c9400150040841e40c0c881c0e8180290300034208000b030700303101c00d445d004200c1d41400c800d4404441e0007101c0c584000300f0b9034559284000e103104031b04400060003980c9100160121150015410040941404100d071446003030301c07502c184550408480d07030140c041c510003602d01500b444503040014140c0303041244e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 254613902 1250 254612652 254612693
    0x200612041101180b07020315040f051213090209040b060c030322021c03034d03180c040606080f152b1208010e0912070b070c 55
    0x10244020700804080001010310300342468450a9248008441602c11034031401140c40c1c80403d600c01503480a202d0441c00c501c4000301c1d0b002a00c0d003443e100940d02c0c2c4510003600e0500c500b000c580c03002201d050494000d41c0d145601c107401a4500004074001e5400307105900c0c2c005841d00602080d41d200c140c050010340c545500999181c1c070f45404110011400c1c489048404104011703560b0260312071840d80356001c0000c859005a00c201d80c1029405001c2d130100d0030b4021004059007007082c071140135402605004214041d5043c001c00011500560065420311248100400110301120b00b441c501c42282d10383d100030faa0408043c0c10000b400c40b4842d034400004100b0034030800c10041e03074104800380d0141651809074034000c0e410002c203018400d09070b0240541ca00010088891019041c0c1402080741d004240f00c101c1701101070014101c00085c0700384042d1680c000c0114042000c04100b1a620980344040d0900f00030590312117002116014240700f0500444800c5170020030348241c10b4010b0401c980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 254615152 1250 254613902 254613937
    0x50108061902090112180b041101030b0603010e0106050702130c020615010807020a1401060504110c0705030f0309060a1407140706020d1202090609030a03020109061d0303042006 78
    0x49070003001142000c403410110030701c100031000c11070fa04525603462074008180c0c009941910110000c5030011051000360001c0000001c00007080040351074640028000c0c0e070144803281e0324a081c0308950100303000c1d6001c0f260041c0700500000d84100c004e0001507000420f070b18650b140a0994134202c801188410005810010401803090f50b400c81b40380c8603071000c1c07030034402c0c2c2e03e42141c009442d003900341d100605119500152250440b0309400075406020700038010424256034400d40a07081c1d02181e0600414080d0810000303880c0703800b08900d891580640c0145142c81245001c0091551000c0d07804001d02c4400c0084480e040510405400031700d12900226a2480104181c9450b10599a01210031980200360342100b02d5444035002c01c0807110404050386440e00301c00014441c1c090791038555018401c1c69040c1003410760541003400b145000700420001d0071300f010414040428540707407202c010344c0200b0100380000c0000181c1504244550700081e410011070b4002640c3c0d80c800074240301c00d007421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 254616402 1250 254615152 254615161
    0x902010206070c330606030209091006020717010609051305060a0209150d090204050403260f04020d02030703020a0803070c080714151e0a1b0203030904110d05010806 73
    0x100401d6420140d9810710301601001c650340c01407894840c03a60b2428109424007149000210805240075040a2000c00c0c0b10090321090010000d4200b50503003441545c00c00e02092202d070010f100d40c4240d500e83e50160004900b00a881900140b4690786940300750b60301c00c400034032001d041c4540c40c02011101220300b10074900f8100741c3d00c1e0100107000820514410803424801c1e03a45d403c807003141d90607140c0c4425203484110b100074008104d0440c0c040d400c81d0802003000105513100b900d054200403654002d449044507510000425081164140b0b6400d031030300081800b40c0780510044400c1d0b4401402c82c1c00050701e0b64085042e4020320f40c800d9080340e0003c1010010814a001c00c41c0140000e04000c090070381c80c00760099111111840e409004a07900e0100c000e5060204c070031198600c900541500074a680c680d820503c5500c407040890026081c001241550301d8510400c160041e0020300440c2008944020840244103148034040c0203082004a47c0990409025050080049a0152000d443d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 254617652 1250 254616402 254616407
    0x51804110103141501030e1009030f05030402010e011101020d110306100c05070512120a02030904050112020a03081308011803030501150507030518132004030203060a020705120d090201 81
    0x3050100e050500303002007144019200d21800b540b1200351542c3c3c1d84103c42010041e4000c0091341c007203110038000c41e6940035030180c05400c0b44a0300ca100e030780c6840140d0344001c07044400340001d80f4020f000030b401440071200e640c8902d900c6234440000c0b20005203480700c401580c00c00c45070295803208802d94044100001c40c90032202c13041803500d680c2131424100d142c0e1380d039403901c43c01035009803842445a801e04000d650710410541407041001030380b0a0392403002500180d901d07044107003807921079130030000085850311b95084d40d52070366540035080310489800d5503034041107500000d808060680c50b0100004014009000740341c6d85070413007201d20703c0c160810305004060743c030160045034013034102c0c1042011884d400022200f400d60035180c91502c4200600c01400301d40f4500082e1541310707a465148202c003100a901145201c14590382290000d0030041142c240b40c0103a200296140d0007401c0040c04100390342c0c0040030140c1c03042041d1042900090b02400f0726400c4001c007552025a43e01d586011941c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 254618902 1250 254617652 254617673
    0x20a050301020f0405040e070e010b0d05010603180222110702090c0a021e150711070806010506041a07021809010b04090b0103031d040c1101060f0803030f10051804 72
    0x2105030001e51808146001c0d1034030341e104d18454240560346c0c43c01184110101803068401070101c800100c0003650703498a112071250440c0b28801165480c1c90700010f23025000744100c01e038444900c01040c101a40540802100240c540c22800c1c1201c01030902c4000c40d00c092255020002881c2182900c800090050003411040217100506904c01045902d4203d900090a01100038020340c608184010343c002c039900381000c0414186900381c40340140b1103e250070501c03805807030004a040700e14940d40d590440795200720030301c681c94120340304120600070301303100761010700c066100100030b03d19180703155012480d8416929450a05001c4440c24041015000c2c0501c515100c0100c038184440550b0f07844512580700188401028843c40070b510b01c4000e0021005070480e908002c2c81000484206103028210340c4001014685651070601d0200750302c01e801d42c41c1030039101c00100450841d0340d00781d0304403030741da1025000500000060078009039542d030701900b4100d03c03409008032031140d08203450444003a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 254620152 1250 254618902 254618909
    0x7020a1509050c12071a120a060506030c0a030e0f030703020d080f0c07020f0306091c0503040506070503180f0706030513020904021e04050103110a150212030a020c0303070903020a 79
    0x5810142401d01103500050291114001103809441c0016042405403814401e42e0015070007260300324400345125085030151944c4e20440d00710a40c40d541d4407100b03004444481c001d040c0d2018040c400308081c410440058030032003006060000e144500319001d545008480c0110141e0f41e0300003c0c08008150703040c4901c458402a0303003848a15400c029101900205000f8200d004100000c140842035684803402c05032010005010381c1c2b12800c000c40c01c1a01d07600d90b0a40207a40024070f08101c2c00072032080e01240c3c0303d41d8000025100c0c84d200c2d901c08031059803001e000401c6005004e01d0308070103150709100240400d03200e50001c041c00f51038210f010741680c90080901d414825080101005a118a152241d0080d07049500d40c07162405800c0c0041140600401c40b50094680000401000300208903000040390443e003000041e955565006032040010440320300507040380d2103100e102c078540400b0399000140014054140f42c0781c210154070303580040b50000e00080c04100c0802c02d50416002e80340c0038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 254621402 1250 254620152 254620193
    0x3010c0801060909020901170f04200f0f03070302060d0501091802010f0804031404120204061e090515040507030c031109010903240213080f010c0c0201180e07020a 72
    0x9585000c0c8080c18080b041c0c851580145d4000610310035980c41210303038003035000b041080000c85007448074003c842001c040700c0c00c45010920f40e03007052a181c8660707140300116800504440c0054141d106104010041d041308a4045c4940000400140c2c2d03071038041c0070500d40ca0100058a9031514004c80c00796986041040d10185401c141c03a40541d078464461140001c99080041079904c0d2890102c8000c0e0492820441405022402203981c4a0709901030310311600884003404155103d08001240340314108480c25522008402080026442d0b00a1540003c07400b45000d000d13000350f0041b4055810071a901d4000a07540c2011614164142c468030301c40b0412080802d040c0254040080c003840058000035008440400a00c04d6400344002282801d2010341d030299220582c04041c0c807129042030083d4030341400b82c0301404000d96814070800f80009000d586024004207180c0040d50310f0a640c041002e102c8826810104100c0d902d12803060040e41240c0c01054040c0250070600508030300d02ca41c1c0d080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 254622652 1250 254621402 254621417
    0x6010e0105030c1c0c03020d0b0a0e060d030c050a150c020d021b030703050106090b150711010e03031908070f080c04091d120301140402030f01060e0a050904080903010c 74
    0x1059074098240d0358070115890701e40703540e01c40700041d90980602c02c401c3d00c1d0646090030030080748140d140e0064640101d28140501403083c0a100700908007840380601d1880c4104180083c1c030529007100c0024106000c1d0802c0d0f442e500e181d4490f5820140c850741d00b03030b98900200f21150400c4030140308801000d4000d01c05440316800d115070081d20342e201e0b80b101e171010f000310381108211136405000500056500400030003107140d0741c101d400c0140104120a51068000d844107011000740c400031590466030183d45a2082e0050b400107682440c641ea00c8660184003c1c803807c4c503415040b4143c0c070388280d5951292003191400100040c07600340041205002c0120f501d042c0251808414250790580d0170084020955040100101b8181c110704010940d030780c854102c0b010000ea52140c0214180e0b0303070380c0c2c1d4482c2d000e590110510041e407200355014035184041d90010850300b4403d03020710310b0f81040205078000c2c00741c0c0c0d5000110600801c0d2015100404001002110b900c5c0c00d2054030050748180c280b011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 254623902 1250 254622652 254622677
    0xc050f10021b03070815070e0901031203020708160b0108061b070212120d020a090909020603070804170f09280b03100312030c0306060201061a0903010609060b0c060601 74
    0x25124618105402c0901410304040100c0ba0b50601c11840684500b100f1201c01d1640441d4050f10f1100c26941030000c034040c0148c0c1c980900341210000d050302d0300011802041c094598044000794080e10040c0d0710000d00703200b0250307582c40c8032106120842c0661000c0c40c3c154144080719007044d1019003858010440340c0c2070820244041c07419104001d40440d40d111040710405501c50070111258070440c2c1c0000c0c00280c44030014038a50181c086041580d586071304968590201d80c003198440c0d4030107540940c05000140450784a0300507142d010344144c100507000c1c1d010442071001a00a010b410786078600204020041e4281702040788060703024407001014800c0e07400c030540880e941900400e002c60100100140c0b190a01412600095511100d005c1d405065032100400400380348528000103403c080001030b01c03503c1406800c00761916410000603140050404c0b5142d9444000360075015525100700060003e040d1290600511071944100e50316000c26030518204440281500c2c1405200d02d0880c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 254625152 1250 254623902 254623907
    0x90305070c210f0606120c0e010803120411030109020a060c02090f041a150303070606030308090d02070620070308030403200a06111204150f060e072001090c050f10 72
    0xc4085a04422524821441410800040c24640e045142e0b000c2180045034104148211000c7c01c6800000c0d40003500e0740c0b10100c0e40d81b03034403400307401010321954100420089215040400c092820050002681c440c465011485020307690b030010300804c0021511000f0b508025040b154045000c4190014900d000d9844d94800c5600c580300210211415000654007020400e0b040d4a403100101200c5d140c210514101026120900085001071101000316008140014000c5508030722038014212050400d1003ca039150b51b012051090076000d10226494140c041c040440074500030f8400a90300d1a0600300a080c0040e0b0980070085400011843e00e0603850100741090302c150301403004110140603071090b40f41c40c0201c40e07030b1102d8281100c2c1803104101800d000c460080250010502c070100500c2401000c855540c4141d050745100400040c88e680d00c100902d4071040c80e2800124510f450300705e581400c451098804407802c1c00b0f040e1040c00103207410918101407035001c444451640d440e15400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 254626402 1250 254625152 254625209
    0x10608010e2a21030304020a0e10050f06070f21050703050a050a12050907090c23030901110301090f0614010c02011101061508040b10060801030b0a0609090305070c 72
    0x78070b14804000019001159a05200800748102c801107008114088500ca80e459600c02c0d01c049200300c03c1128005402e100f2403000d244207001c9444501450340c0303810240b14914090105803580318100300304c3d0400003a0030001001000707024400e000780700e07030580b41420181c201c41d050040602030103021040009030f000c1c040318801c0c0d21914100d40ca85070890b0701a9000080005003410039424203080001c86480001c520040301c12029062007100e0580500b40d0361826407500d0700c0707400e0b440d010200403016105801150004000e500004d03c50802440001843c0c100b038012071003249d01c1d80206a0040032038016a000f8006d0b44c90014221a0f1941c0081c00044031810000d041c40356040c0085503407002940030800401c1640200210031020100051000360101d4040320741006c60004144016140380020060f6000d03611544180c0c1d0858544040445000780440d0341e00c1d483e0f85002c600c0c900180a1800300ca8429101c81e52940d001c0d192a196920f42c0750021030110303020455a101c1007108804 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 254627652 1250 254626402 254626453
    0x1c020c0a0f0302130b060f070b100e240303070203160e0a14060d050a06020f040611030403030206010b340201020607140a0509030c0402040618140916021c02010608010e 74
    0xa0021781c1d034a46002144690203800f446442e5038102141103400c0c8007076181e1481c03142c072000c61200c0409485500303142e04140c05842c0c2d850142c1c0c60100405881c1ca03401c8007803101440040490b41800c00f80d41c0003900d84805d681c900da0b1082000c0104200c141c40c503022a40d002a00c003007043c00f0315840c8000101900c4801032005e0702c42c8881d808ea00342444414885440c00d103400003000d41d07039010280d00381c07a41607101c3c1c400c610005081e00c00d0060009808000c2d030f41900e900d0f6015000e80c2c1d1030070303503007100c2c81c3c11a241c00141c100611511000000058425a080c8c800300e07400304000050b5400003909001005100e94240810250801c000c0f144880c00c840f50340d28582400f640750720302c02d000f0a14228030b00200b0f0707410a1001901182d039640208800c2c10558042040c03021543c0c641d45149140f407012644141c100c3e1200700070440014103047c4410040d0040d1040b07031050010741907a03401c0c03c4890050392001d43d660b20710a00541c1400e002e07004c8840700c88002065000260b10780405803a94000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 254628902 1250 254627652 254627689
    0x10f2301091a10110607030c090f0b07080f0d05130303050a0c0c12031401180606021606051e0a0c03080a09020d080d0b0904081206010905090a0506031c020c0a0f0302 73
    0x6103c111018007541e80307181c106884404840c410b1130b0440001d40140310201d203070400b142100706c00040e1090040c01550513a80001e00c2c2c10304002c2c1c2640d132218a07400c134401111710100140208400704000784500c611804001c03100c00a0802c0c0d44c1805412241c018052410441c10210110056a00620b40100b212f40c4000b2400124603500310031001801101c61052000030040000281c00b5090080b03000c100c2c5208a0400100b80e4030302d026070f0303924045155040d0400d26001d00701320701c50251000c2c0c0641050196280000b100c2c1c001d290182d507100007600320116681c01c042c0c0003816800070072640c0c4401c1d403550400c20861903400080310f00c2c44004008240d138000040001c082e002c1504954210340021300402d0180c241880c3c0054070340c2054040c00d1020350354500107042c56124802080c1110f0b406010726140b40c0700da81d03030503015220081060b0707054424014400b081c101c0031400f1082c4a41258058800b00707a8181c03c201034140f0f10b612200040d2a02d8400340003696403903003024041c07075200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 254630152 1250 254628902 254628919
    0x9050d03030501090b3c03030d0e1005011d07090b0309100e0f0a0803100807060f02010e06010501140a030b09070e040b0a0302061b0a390f0512010f2301091a 69
    0x150b1210000c00391b500740440d01800042003480070181680c000c80206038400054550205118088500b11182485504c650800188140283c8140b0150294015615107009000c60f51581840c205582c02680d104c1c015501c441e030100050001c030311503155031040100181418086101c0069518650031102600010780040811240021902e83e0340040040c80c2c103503241140d5030b05010b005035003407051100140d428814400400c5c0c2e40420380a040c8c0344143c6803580442c250100425503500440708000c18165509068166540c0d1450030a22849199480d1031107000c4110500081e6101007194601a0522060900041e0b0725602a00d101d424900d04401181c580100c191f071070b0400340d8501400c000c1c148150589070340c0004400190030040c0c00d100d504c1c3c2401c19040010301c080b0307a01c2440410520f01109104900d1300300d442c100308444040005c109140700d43c25520442d01c2d11b8070705070502c00c4094800c111308041c031140e042c0100b8003141c0400c1000d001c4c550441c1c480d0340c0000d40a21a030307031a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 254631402 1250 254630152 254630239
    0x71406070e0a050f1c060902150a1706030307051b0a0b070b0a0533091810110d0509010902040501050123030a1409010b0306060a03030504140109050d03030501090b 72
    0x115005d021945a03020341400c021003840c208580140f9440d403082c0d000d030541c2c10310089240c0303030340007250404107055480c041c4c45000c200c0010740e00c00700903020541c1030100f00400d0000c550f007040210501e1200c07150142561000200308050090a640408416041481840c0101d00c04220b041d070f100d0504100070030203a59940c2403401c9001c401c0c081100d0000c0d1440c041c441d07034000740100c1102041c29030703844001d5214281c0d0780300100e4484921a00590281000c5e00c5c03c120359800c10215032810844460070310180094410599030120303030289141c2e40d60000703602980740c680101401060203003800d14006100ca1b403401109003021241d22400e110000c04664500c400398007180400c000d03a0510b50460414403c40d50281036041040c910921600021038001d10b0240007500443e589512440d14040c50100803a42c012010b54040e41442822600000c0c55291341210342e2049100c0e40d0001201c2d0b041848400c129441794105138013800014141580c000c1c00078840c0c01081000724800c1d40c40856 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 254632652 1250 254631402 254631409
    0x102120301141207060306060905061615060824070305090601090908091c020a080123040606080601032303090604060c02030106090f0e01050603030f0901180803071406070e0a050f 79
    0xf940e0090340e00600c0759000c0090381d41c1d40741d80b020b0b003980c0c1c00d0f940d4181001e0740c500c1013000302d0044800c0c901000f8880c40740c0b40001501042680c4030304501c058082980c6913203142c913130300700485c0780c298809441c01c1213841c40a94040d464a00c1d0700c0149400e0810103070406c04c0440c0d664440c14081e052409a031aa1010240081042a500c1d0781800400100030040d0710b40101040d0340e51408124082d08a01c0c0c00803071150f03010b0141d554100d0040020810500c0042c1c0c5103295250040d10540e1603d60710b12000c149001c05222560195001e0000010100d001c080c0c4507040002903070455059030170a2202e901035550b24000c680c2201d140c1d140c02c8800021900000303005241582c88480e040d440c165090400750310540115034011240e10003007103155903201c20315031648150141c440049004009003201580541880c20400c4088610b0b10300a64862031081d10750f9200800c140c40700b007902443c12508101c1003014983c409880e2034030010001400b00414079644503801054801c24198a80106a46 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 254633902 1250 254632652 254632669
    0x90403020f030412110f01020c0d02040902090405010209010210060509010b0304050c04050702010b0a090908040308070c03060504030203090a0501022b0e030a080a02160e07080a231005010212030114 87
    0x10900420340c3d555654451540f503120090714001c880324a5000e10040325441e042e110030705081c0060700904a010900310811001c00194082207a01a40d01d0740045e02503190390306110303c242e1051000580d111021400a850017005c2481240d6150078080d0a0200303448a161190455000c00c026984940307545ca005400e250100351310f1070300140b0341010002ea840c0d05410003051710760107460240e14161512640c0c016070340c4910780646100420031003000040c1a0304010441c09000302d8000e03c1c05c07a00c82c2e5658090347c80544095006903c08500b114141c81d0680024005000900003080042d402c0302376240c0c4040343d000c0c20400502d528922101e040d0159118074104100241654440e81c080c4c0390901d2950000c1000000520400505854090060406c081070b11402d840000d42a52001c504840d0031b00014040440c1c15203032850340550040c04e0002c3c14101c0ea003112040c020386881202049109410f900044c110340c400a0b0178007503445900112810740b4800b151f50620740e5400d10103d0b10340c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 254635152 1250 254633902 254633923
    0xc1f0e0703030e041e1b09080d0813081207110606270603160605122d040503120405010b010201050a11090d0215120906090d120216120906020c031b09040302 69
    0x1811b2a00800c80300d001d0b6409100000c2254664441045d15030380035a50319603006100c4400b081950021406000a80080b1b107142441103585600d0503055020300c05505c001910000c000c1515114108032082081c04400d81c00081030301d80500342400c1e51100d090004109005882071a11325010580d41d440c24002124111562441c600c3d1850382c900b0300401a03801240803400030720038540815050038103221035140c4020400c901d001c0510984178200b034103a0700600b04403468442003004035050784a801600c0c2c03255026400019901061000181c2915002807003801402c0c1f070500121801155041600c030888800e45801c101004148086003075200c0c10307030b03264203a04030114201569440c0b0030516840785400034240c41d40f6031564240f06541d4070304000f64802141c8880541600c209590340580704e1100c144200c69078405194403518048405410300000040c40b20074280481d940400140410210075001005484550000074002000d001c4075035100e0001c030000b19040c14401c000f00d0020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 254636402 1250 254635152 254635211
    0x1603020d060506043005070612021c02120a0507080a0b0f03010911150708030a020306010c0c03030e04200f03090312070804110303030f18030c1f0e0703030e04 70
    0x5032500c801d044402c180c90060017210051074800b03040361030003c06203082840d95201c1c00512080f810709a0650383e031030010a042140c03907800d000b4401113100d42540900041d505120040c2c1d5041303000030700b25142000411384410682044c041c050201c2d4072241c5981c0c0804288000507140300950001407425045020042d031643c02d0204840c01e000315085200d04840c4122500062070740c8080d45510540120180500b144a050001550034165038008540c04071051400128102103603a4075100e0038003d41042d0009090501c51750b103103050511441040c080c80d580341e0721003c8024060b00304103115401b5030144030400071003c80d603454401c01c1a10349820060b23802c0c0780c452902c0000141812001c4405031420620b50214503910300b004070441340241085100c2e17035107aa0310092021070805e61245102a1407004001d80f003044101403080580c241450191034450f5000c0b0f21910040d664420240300780c41d0030801c0100b00294110b968100d41d00c509842c0403e00694001344141c000c203000f45c1c000103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 254637652 1250 254636402 254636407
    0x3050339160510062402030706180212010501091a03030711010c080408150c03070e0d03020f01020d0f0f060e131e060f0c080105030d1107080d020304080709051603020d060506 77
    0xc0d4030311039801c0310303068a0001c00c070618a081030f0481d05d10348049440342c1c83d01580040003a0404a0030070b4020341c10303420fa0442e0301c4240e280154049a05004031038040001d40e5036460051210b246607018407180310311000d1455a2942000e40004d03140d200c2c80d00e00801c02e11034030001b00d2559000e482c40e00072050300500e000b0b0701d81d0360ba507070403544581f06828116510b00394880080d070705550f0003007542d001da12180c2d106c50303040780814280490020004010b0302035118500182c00e200c5424001014080384408012452150356004c0500ba1036807111a00002c0342080c00c00d00c11350760385c000956070101c0c0c00080710701998204e0404401c1c000400000070600704601e0f14440a010054111100302c0140b0113080103840c20740d880c100c0c0c7c1c2c84800e0207026499084101c00002007441034038855943c9e407031181910841550f40c0700840c034160300f06142a0258002144c204507500f001c2c002100200000d0806200c0f515201d01541c5402c1042c0004e80140369000c2800d000590880e4031540240c00050156075 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 254638902 1250 254637652 254637673
    0xd0516061701080102030c09040b040605040509010f3e0904021305032505010c080d0212090f070614031504050f011a070803070e0616030503391605 65
    0x1405404a2281c420101d22450000039161005100b103c0c49011000a002d0038603032000200300203465040062988141c450310045515070740ea20032140101005000058000513209000040c0c425410a40345a00302620000ca000e1459100b0001c0b442d1650400c1039900d6008074407429240240154039402c40c2c408610001030000c00091038061b0f650840881703403110154019440443c14581c800a1410311940d01003106d54059103650110324415800c0340e00340b000c00000d05040381c101010034440f40940c0d805015031301205015103040341d403032900030308401420250003400300300b0300d082c485510002c000700103242010004101081141c000740280a5400c003c0b180c16034a0304280506003100500308500c1c00c5c058021000c03036890960041243c1e06660300c00106803241102c0312042c0d0b41014007000034000314071a028501650394442d4843d180c0700c0c20083c1d50756014103415032050b0502d0300d03442c86a0000341d0000c440606012050001c166852002e02d0f0000700130a81c000c0d004026114407070955 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 254640152 1250 254638902 254638907
    0x503070503040603050a050402030c040c050708190e0102120a1b061b0f0c0308060d0c0308030a060e0f1311061902011d010c0c0314070803040302060727050d051606 72
    0x108120b600f5550280401d445841307601c0e040760310079180203615a11800d0b072a091070600750006039540456042036402e1201035202c2c41010781c000c40980b00c94110444524042d907070813080701100c00c2c2c0d003072001b41504401c506c100b5580c0d110308504e01c814420f4189100e220804810620344005501c8101808414134600705000250b040740503104c00f00c0c400c0714508800e00c0c401c04007200443d82690344c40c03841d9298581803004000004a0542d502c0440075008004500702c02d00550041820a000090191a0148142460101610300d212218590701031018548004120640c001e4201c0f83c1c0c0b88011305001c0c000b51080c0f18125102202c45003141060b0000c1c3d1b01035000c0c841c690b8181c4d038682100b021041ca01030032500a5400d1f00c01007056003c890340803a114140b840441071a0a91151425840f0303100c81c9190341048408a00592114040000e0503501006e2000340d080d10900c80ba02c002e00c030500d158000c0c0076038098980110702054209050100c200f001c0410f001505504100242e11100e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 254641402 1250 254640152 254640157
    0x31005120109030e12030f0d06090c1809090b040602090d0203070603060518040c1e03020a0e0601030f05070813020307090513020111070506090f0f0a0905160305150402160503070503 80
    0x783d0101e0140001c15080d030400386403004940c0d034020061480c0901601c010069500030b040302113010750340d82e0404a0807250320310400300141d0264803005442100032100060b80d461307680151103080d00301250b100000300d2848140307401c640c0c80a00584c0b10000c041c003251806442c10006917141c4034001002800942580c021020394800365055130790510412002282010291070080102040100c01c00842100c103003d10074140143c041c1c05541079032600000ca0f200d0b0180c10440002c01190180040b03581c0500c02c4803003400110303c052010b4980b856003e006080000c1103d0000c0356238111010456405000c00b4024000d030b44003c01a07800e1400601c0742c07841d0b802e50128081821004075a5080400007629011214001c0c030315890300b00c859091112840300150b02075006501e0350206040e55444030100409000d0225000031703a403030301e00180c0e04940c410368010f600b458503001c24094099114021600a008155030260b900c0d031752485000c50306292881c0280241c08040317900401c1007400b100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 254642652 1250 254641402 254641421
    0xb0a0f050102010b030606030a0611040b0430031409010504050301091406061e0f0103020706180312110f07050a020604060c050106051002030919090c0306150503010b030c0310051201 80
    0xb0821140c9840178035550b4141994400d0381070b40710070303407070700000c3c202da084041c24400c2e447d812401c1c00c2ea51200203803203811070307000600e403080c81080580e4249041c00f20340d21881c09542151200840c1c0303880107011245060909a581400043c22404070b90007101200c0081201400801ca0341410f810200c009415902038914240501008204149400500700c0c050482101d03c880400380c9480811400c2581c1d406583e0500d41c091202c80041031052081c1c140446000e100032101314550304d001000d09904503440f03045645080120246c80d40d85c2400d507803840345001c3e40703141d50f200702c0e05042d458074003854002940a500050041096580504424500c0348520000d0049640300d0041000c0085600c20b01401a4801d0084440e00e1801c9001c0f00030800150342440c00042d00e0b03000d5107003034030075402921021030b031a00003c00c4051141040d007411760000c0e15142c0c0c115410712008040720712000c0c0007a0458400400440c4500d400c1c00511070042034024013810050080c0c0c2191070117002240d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 254643902 1250 254642652 254642657
    0x53321030d0614060301090504050a02040c2001021c0b040608010204121b03080d0947090a0f060f050f06040b0409080f0d091e12030b030d0c05010b0a0f0501 69
    0x540014000e030000000b0b10f41d0b21008107541d05580c00c18500f00e00038040140141c600d881401d0011015848a02c24100307060320a40c1c4a1446200c0d62141e100011051415184103030720401110f03400c1c1c0320056098446d680419804940040000c0c0050042c2c00590400c0da41d55200140c0092000d0601080d202103a109031a50000e02ca4819005007400c401448045c203004404c002401c052081a03002c00046480350704e5400c0e142070307029010f032840500141c00240c1c0d48000080076080d1180310b440850080250b45090b4240d01d0505102c94541c07490f00310051480d106548001c0401c8101d402442c0550140b44040101d072074044019070b07241d1800c1d113040b8080e81c0751495a00c11407c007402040e180d150001c0c549841d00050380c10400b00c603406101044032560752505103c00007130001c444240300c42c02d1030002c0c2083c007060741442da03026a020381010701490b240c000a072075283c03804940704c0032600b650b003410340f10380cac0032030500d1030150483c50350441e40090301d60800700c1d41c2141d1324014030558000383d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 254645152 1250 254643902 254643911
    0x601140c1c0f0c02010c17130e07022503080307170703060315050f040b060d02030a05100b09040c030609081c060806070c0206040e0a0e190501053321030d 68
    0x180155143c820030fa20281c0004d1000c2807582c04680700b100c80c101d040580e00c01003840c4c25407041e40303501400840d42180c0c11522809041c0001c46504012565001d803165035a41083c908a40c4803046149a0303100003481c026000c40003034469801013104000d40d8085419104032864440002001080ea078001280c200910001c200c0700301416105140c860000c000c0490744a440707d07151064200382c010a916402000b29482200507102804207004544c429001812804502e83c4000140d561000169014480140c20480030501f40d02e1031400b04ca8206100003494529410011042d03c11102c00c100a14081030004200e03010310b9000c94129000c601c1030f42d009480c4c40c80c04030f54034000d00e000030303500910512040c000040e684054507006070507034000003142c10144500742c1c2016003001001c0302c0e80c1034a0084005010081c0106680015000d4007869007031800303000461488072440c0560f0080c040c40400b907170692625001c8010500038810801100c482c038003002940d80d8041300f1100c1c00707917050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 254646402 1250 254645152 254645177
    0x616020c06041403101b0e04270204050105090c190302121303030c080610030e03040504050103030921031704050f030d020a14090f100e06070c0e130302060601140c1c 73
    0x8920a9200c00d40710300d401c6c421520b858510455400d81081502c2e03601c90b9542c041080c084042e40483e1000d01d280e24036540d40a048e60042000b240d0050780210300412000c42084a50541303401110314410401c191b481342600c00910440080c0102000400300800d0b04007400480d44510008014092080d40c0c00c0c4845000080d04594040007603c000d9006a0390403009015035020b0f800c450801c9948004903400c040e41c840000d4282d68081e030040c3d001c1742075000e041c0401d0700c41d030b0150303000640307941004231030600d040d503004108491000030980010792450200742000002e0000c0c0741c141d4080d004598680c0d405429000c02540103c80e82000301b485040a0134142000f10103440300e001000304041e2252002c0d8080c032a401c0340814640003085806d03000b00605d0380c7c07881c010300210f40c000c0c0703a0041020304049524600d404054150040f88040541990004c1d600044c0c155020100b86001c100615640c3c0d20048240152680107080b405240d0610304c500642068600b40b2688590303407070700d40307040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 254647652 1250 254646402 254646433
    0x3060905130203010507030b0a15050c010203010b130801060e072607020d090909020904020405041707050307020a05041a040c050418020304061d15070c140105010503010b120616020c06041403 84
    0x2302840e296000207880504001e445079100001101411a0a0003458a035100c4021422a40245c2100380e040380c0100340c464405082c5003000300a00780501c003c100081c1030048030000098000c0c03040080000d5106440d040264203201c0d942090030942c981100c6080c0108060b48440400100e0070010300d8645002034000140c1c010f050b81c5580182461303c064490390284405410300030401d031003440e00000c0030803800200700001c1408038048c1d00659181ca10b94070406c102044e02d503100511a07405e0200c1074400008451448060507004c840010f590310079464159120300075035102c601d04202c410040c00401210350000c1d4403651083c0700c100101544d0301d142000d003c007450a2030b4840e6014584520552a08118041e0003810604103044905425034a0a416001c88207a49141d65107980040200e414240142540d80c94101c400880d007404101010350744500082102c25000c8007030100b036241d1303402407245985c01240030340b81603901c2e5110300c041d1820745e1004274124028402c20740b54141882 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 254648902 1250 254647652 254647661
    0x40905100e0313030b060f0901030803011e081b0a09060609080c0301060e040809191508150d030507110d05031e0702010e010f092621040b0a0306090513020301050703 73
    0x8800c4220100f00c00d0079500c032030302291001484142c0290401c003a0000756074425003864000c41c412005030b42d480d810040607400a140100003c01800343c07400e801d1041801c0861000080c80008101000800d140c50005100350110b80c8105842c07403404401160031607000d000c5078151201102141d505081c1d0300300745401c03142e0504c070709130a46c5010004200080c0d0554000d2070400c40080040b0f002860700301512041503520390100748900f030709000c82d0358001e1b00181240d43c0480111010109071000001151589000c02c03002410000001040c90801901d1110000c0007540600007003040e03140c624181d40d803a031061820410b2a800c8080803c40c09181c641205e01039541039454a40d842e120800644125003400e0f140014010200c0010034000c4003029921407e01c8081141e650315410980f6150601c980b40c2010000000c03034900300f82d15040b1020803181110031070a56255982030409044005012a0b008416114108018000c410550800c90441103000314000c01407621030070030a50071078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 254650152 1250 254648902 254648917
    0xa0603021e03210c0d110d03050c030712020c070801091e0c14040b150d0c02070f060f020f16030b06120601030b070c08031602060c07030e040f0b040905100e03 70
    0x158401e5103030300000f843c580c07008640200c0c1c0101150802c0c1901e0401ca040031040400c60b00042c0d00c840e54100344d1807040103403008400d0142000c102c9414042218030131484002c0884080c00034480e20700d0601c03030340395044824002100b025200c400e82c5421184d400307014a403100340c0d00701c044185d00009a1054000d102203035940301030001d507018641044400342c0641070000c030382d10964842c240c1005031540f61b23400396103a40044d6030b10b035182d2206050108482c8030350038007400c65004030402d0054016241c1084107a480e40d0070090190b50134620101c3c03074030020800b12190b0380290011441000c800e01990b900352032191114100569401c018070a90328440c4400c81c1440d40010010000315440e030700440d82000c020310744008268503a850303c000d2a4420347e49a0900550220190f282c0355044c8601504501d0641500b440c100c15030720700410901d04030040900c190b43e00c813824489000250f0041c144c40d40701400078041030005051003a12009104c031450308080c02c2180144001002008680e0340c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 254651402 1250 254650152 254650159
    0x304060207180f091104050a14060d1403040e0109060e04050c01030e19050312060d1208060118081b01020d02030706230903030412021b090703140a0603021e 69
    0x140c614081121a1421020640d42d10701c90f9150010011400700e8010000320354000c0e5040350b00c4e1160142480220388004004415040c505507000686c010b2484e0002e0b0818021074066040802034145517000c0010801540d1051000142c00500310048020b450304032200a8410010310b9911340d810625000221001042c0750400310307011000790702a5005809900c66107003110b40c00100705460807a01040c080e01591950300201d0002011088400160303400ba406480c04001c00100c3d0703458078501d1030200c060b2410301041ca00081c001d079108115010050310162080700f01180e036141c4007900c075040040c84010f403400d0765010981035400050b601500c0c5180758001c40c9824000e0300c4100c000c01069a1540307001c081c01c9206241d280314074110344c6c000d04401010390fa036428146820141c4260075005403040d50040d1a450701e82d010b03030000c1110144025980220242c0d50014120020302c083d803180354495900c0c0d41400103d01c1941d110f0300550340709998134003841205100c242554070359400c004d0350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 254652652 1250 254651402 254651413
    0xe0708011211040c02030c010531110301110403030f020f1b061905090a09090206120a0e0f060601091205030307030c020312070203070c0504050610050c0304050411190203040602 78
    0x4406100c408031070072103004000d00c50340c4008400c0050300340d03400004c1290050b4004503503420607880a1207402e402400c122191100d803000d010040076240c181607074650002c440f842010086c09020364080d41c1c0140020020010b18002001d000c1903900240400e5002427581000c8481e25400001e1030440384060700010185189049156400d0f42c00c2001c03a244c0020341445651170f1103c441e503d038801e0180a480f802e454182400c280071400c0c21907070141820300e080c011860090389518049441c1503170f211801074110f940b0500300802501840305050b030710388264406031451240118000707000e10026620000c0141e81c411034909050202d550142c500d40042010440c214007e03400b40940d44903600690781010322242c04d40760301c15800c84000016800c001048010010703000b1458024041c04ca60800c11406d040001c101c83c0d0b040c03a00c01e0b4040c0480081d99680000041054500030311000b04144411030041d0841c013515000725042c110780d000500c0100b80041d001000b510195400d5070f0080c907 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 254653902 1250 254652652 254652659
    0xe0108060906032e0e060c04091a06030910060602010b13050405120304150b060c0c0f0a1511120903190c09060e060102161a1b250e070801 61
    0x14008000d0316032035151007556100402e0840302d00c0350301d48130001050103600c19900241e111080d42c1c2d002e018440d0a80000c000c0258000684042c0c40503290055000140120b0a20441d60310741c004050040d8480300200c10000861800201d50480446c0c4110030320101d0358441080c0d00703842c107001140782e00a882201407034651f81c03240d011a034081c1c00f0b1400c55001a4542811550b154825181641d06005c50b00c8070903036052503400781c0c1c1500803060f9140c40c07078054400da80036280c40050840c01e00c1044c0d00b0031800a1540c60310003040c00303405907900202c11900c0040c00980400c61044102000303004003c000b03588a840d0301d090f00c0c0310540c0a00609240000003540640303002c0440760480c0c03003184c10100864401b0207885000050003000100c015a030070040c0000e0b2401c802e804140007a038114220502c02e1400c9080d284240c000c951072029101e196121006111945117452041c1910840103445da2038241c64282150f40c1d1094030400c0440c0ba210a00940801011202500850007000042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 254655152 1250 254653902 254653909
    0x60b0a05061803010908030412030e0a020a030305280c021c0503070f0615171005011802070c03021f090801060608040b041a101706090d051b03120a0c0e010806 70
    0x402c02031600500010310400c240d80c07040040e07042600d040d13440c0806d15407042402901841071400782a2030f00c008282c40e60050f030000d15411402d0000404000300030640c4d21003055010000702c46199000626850041001402404034103d0b40c1d0a9114542010508181c400c41507200c00c1219002000b0310314043d001c1d100d020b01e040c2079490403105680e0302c1140c200c0c032a207045c14441c05001b030380c4501d400311a04042503524001641080c8410140f40000403c6000d850011010034448854405600c80d0828200341401d02c0156102a4100ca42c010600310700003122140008505102d440300c554564070b40c04610700300c41d0701e4011800400c05c2500418041030400350f072594442e1282544400303520130b0320519050040c0581c2c80c41d080401c034a03401e200600a16071045003086130f40e00200b04500d0000380740c1d991007084956800500100260220424200d03010541c1074282c014200c2e0356441c03061f000500d200c80d003100c240b0115403030840d4500034588202400b01400d02e0596030061a9100c0c403041 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 254656402 1250 254655152 254655187
    0x2d1515010c230307021f090302010e0f03030c03040501020609030a080a051302130603020102060901200306180c0304050106060f20030408010e011b110607110102040b0412060b0a0506 80
    0x3901c002c01d81080300c01440101003419080105900055903c44c1210703c10301401d40c00e0078810010340e075074060a802036294406d000d60110ba4091801081d025100d0011030a09000e0f000c0c02501400005001598600000010021218282e0031100943e8800b09100d487c2d00640e10340714001403250000c200b803030300070750881d0740c102c004011640d501d00c40507800070700c6003076001020700d034540d44442d010800d541c0c06000f202c0e8002d041000074461006440540030100f0f00c0300007595044078002c07012803050348541c020b2040f50004481800c0c0349082505201004c0e40089404690543c00d1841c0480c03254442c41c5240011000c5d03480d00c1020201c00f6140c9105200141d0030310100b4032003400000740c000800d000343c092205645c8000039061108110807000008000e03034000034880e03081c071180a207020019486511100070301e0541d400030203000e4014003a05c502e82c01850b544001040201d10f940c0101446003041d03200e03550412284910b64140084074000d8818298085018070050f11420440c005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 254657652 1250 254656402 254656427
    0x17060c030118020d0c0c05010f0e0706030e010e0f210f040902030601030e0118031701052b0c03030e01120c0e060d0e060f01030c062f2d151501 63
    0x2d01505201038030350a0b604442030f610b4200001a50380078014280301082c424000991043e00c001d00540c1d01d504441580c40c0203c1c440c1c2810540c1d2662510b810401c290701c100740c4546c100b4180c55003541441d00b0240d61314840c00e030f04140c91520754000b21510300003004a07079481000b07840c028100b6241c00e000b2402904000d29050605071180d26440740c502c0203102d003112422201040d41494440ca00f00146140f0301810b88910403072008006000c1640c410100b464940a5614101684c40e00300798058800c548410009082040b074040100804d034002a42c1c45e043c001c00c1c0d940c0d0136100074452045040e00d03080400080454a5400310604904214009107020105041c010401510b01e0000030300d020401c03a943c01e0710441c0034005004102545103218010042c1c1d2401c3c010075481412103450b03050300c3d4000c103246800b0081550304640d0061000b842401c100300740d1190b0205412019200710b14070b9442442060045210b503c611041849039940111100f4285611100307a1034010755505547c0a0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 254658902 1250 254657652 254657699
    0x90b13031701030834110607060c0f1d010f08060a0f12060605010c0506060904140a150c0c231c091508071b15090c17060c0301 56
    0x14008294503001c1841d2038029446a050f4036510055803041107820000100c000d00031030a0314000d8583d400184100700091900700301c0c49a21020040e0015007d841013110007090070b402c2151540c020381d0805034208581006844036070450002181198070000b10410590106009408184a00c0d2044c0040d50b031002020300650f41e4191210101500c40f03c041c0d0000140c8181c44a0500c02c000780c0d80a404000d200070308103156a09001d40e41c0d00d2721880000c20b03280c041d66808001405211408211121081c5030b0340a840e0031003a01e0074900200d5001c1004a0140e034103010480410a05c500180402d01d5040101a4041c0f0384021000c0a80113010f00d010750503100708480e462041100001100d10003443e602e40103001480c141042591185841c25481403040d034904100c0019041030440fa2865417080a580d00060103240010748400b90700001c142c090b1503c8494010040c92078004420b45500c0e20503061074040e01c1e25200e540e50012541080301003003c1c80100003200c1c110510310f80701645032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 254660152 1250 254658902 254658917
    0x10b040522060b120c0a06080103170901050706060e1b0405060a03091b17011401060503010909020307030c0b0c100c020c1201060e04080703120603030504140112050408071203090b1303 81
    0x240e00113818219841031001c541c0c4c0100e807881c601c901e056201e00c00100600d0402510a6145403a09020300b00c001e00f041c0380d1254000340e140110380c41401141c00c1c0c1e503444041040302e00d0b101ca02000321400c003140c082c00343c03005100d00d170010b412881d01500c04440000707001910f0800004070840182a595200300e030000311030044403240d081c030400b682c00a00950140780081554505001c0d0a45e5030048101e172840d140d0a00501007603503c10700720784c1500d40e440d8021a64480504c0420b02c0c00c21140c1c07014202c600e95031004103001042c00014044080e12008a56050301600c50120483d0b40d400d068002580c021680c0005606015561240100000000140141c0d40d100386004503d8125421100044d001500d24100341d00301c0b012180ca054020702c1000700d80d00790f0782e02400074425802640601e100301c02e41e01403036078490091a510984e240000b440582090720b000c0000e50041da00483d44003c22118444900b4401e00c141c0d0309582d001a0144000d80300c460301c030b0386000d010304c80560810600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 254661402 1250 254660152 254660171
    0x60e060d0c0911031e090c0607050f011506020d0905130902030f1b090a0e06040201080c0409020f0c06010515030a1a03030316020705060a081b09030d0908010b04052206 74
    0x948160000d0f0800d410616503607203440d070704601e0341c405a002d2044040c0300c00c20601032a8130001030070b004002000e844103a540d00103030400034038040f03070b0304255080748d800e1900c2c80c0c0f5000403040c50407080b9011602254044540ca401c192400742c15801420f402c401e40d041c241110007800e4111104250003d000c0c1c030703600c50150441904001e8a101c00207001400c40324003100b141014100154071a469400810049988042d84c1c0d03128200540060304011107640800c107801c10040860380180101c0d44110354802180aa6034056003020703801031003d0083d2000062141404003521800340740c201c0b1540e2842d07443e6502c0000a200e8407000c812141c4072045456515141000114020b801c5000854800c820300c040080c503005c0c0c0c1d1f400c041d00031642440b1405803540c011020a401004aa5110083e20104d07000d00001d4000d21411320790511483c02101190340e00070500b4020b0700c45080080c030040746403209100503224251002c0070074801c0b540c202c41901041e18161060144119000b00390b4030b16 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 254662652 1250 254661402 254661419
    0x60806010801020306130b010c030f02010b040905070e1b160302120a0e0a0b04060c0206090301091a0a0506041104030f030c060204091a03060c03070c0f060203010b031504060e060d0c 80
    0x4241c20640340380e0b41c000240811450815070000e601a43d00348184203e0b501440000c01041900c0c1c0000c040c030900554041742036000790400c540c500c50183c801c000c4c19549050183d074032021440380c08001414440440d8803072006202030344034051290080340c80c06180340881c1e981c003d8070000c20360442c020800050400e01888009056244007503071100c05402c070940421100ca4455400250a03a80c00c00c410003185070406914402141c0444405841d11403010209014004c08400102002c412801c00d0a0b0f4800422a80f4012034466100700410340d601c3e4140300c100d0311040801c6404103418481000021104441e41241c0b9100f0b14144007a00019941c201c1a41c00c075411480701203881d00340e41d11104d460000050b10001084004222a00b40007005103000e1001501000c1044007041941040c004100880b11005620450271956580d4501c1101c00030b400980c4d054003041900c9107071640a2030079009100540341240c1c2d54001c04c0d140c00040003800910102e04841441e0b414100290000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 254663902 1250 254662652 254662663
    0x100902030f01090b040c020d0c0203010219110d020a0201090b0a110f071a030103080409090c181401050303070c06030e0c0409060504110603010305030a1b08181306270608 75
    0x1480724400c1e00550511649400f900c1002c01014082c03441c0c89103040780030f03500040741c29078804035041051072a015400031034068403400001442c421b006030780ca002c0440d80544852074040e68042520019004014100c0c1c90341e10310b2101a0010b15007000a0100e00c60f411b0041c4130194003402c040601c0001c0d96802801c0c00401503d07400381e5008018100140c0e81108003c1e541a0b040d800044c1c507641c11591055554000c5003d484400d03690b5803c07a0b01005240103404020300b0340302403600d961454072040c01d8003a0440d040505040d85100c000001e8034200001a11113140c0e10800d0358650a00b000c00c00c070010f051040d10039115201e44114858030b030301c55104611840d4058440814a450142440751041c1c0d0240c4040380202c0041004201081010095550100c0e151a06080d003014119a815031140b44030b5026114540010b1201c1d02a4422048590811001e46400004182640c0034004403203080c401c80c84401160902c0300c3c00307801c0c5048403050b0180001c0c8002212500d444000f032406 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 254665152 1250 254663902 254663911
    0x607030510121203060902040501080c070302032101050f01080106021b030c060406030207060b01110a11030307020618040b0312160804080604030210050c0a0f081806190e01020702030c0910090203 86
    0x41e800d4242c543c1c81e003549400b4041c050401803905525003442c05000034200d0318018030102c1019000f1460008251080c82160b100000640d6180070b000e070761188070000e044081c0301d030a201e18903945c850841540658032450407221690080e041204031074444403c0001e50b0345130769905001b00c4400800e90b503a0b07800503001030031031a5070041c0c441c107852a080c0e0803910407890f16414480000c51450040e1030000351a40a07603400390841100c09001d1001c40d140d8000e08800a520100c0860384122014020040e10305039801120709000421011045c162a0301768005103800386c500801c4610060f22075080d0540c501d920031a40b0030302c3c0543c0c62023814103101082d00d0440040c1c2006080c000390342a00c3c0111904070b4621000140707014005000500311034521400f01c414000040700040152044446c0c074094800880150740c0c06181036440204040c6c07005103041140c40c5840003140b076214051082d121495400b5000b0700041d8014402c020300500000c00c080c0c00b44040c1c0c4404148000c0c1030020314003a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 254666402 1250 254665152 254665163
    0xd1b030209030c1c0201051308010f1e0b060f0c07050d0303090b0c0c100e0c04240b0909010b1b030c010b010f02010e070b0d14090303100e01030302060703051012 71
    0x44031154010141001001c80c81c075489240c0d03084c0601d4000d8038000303100007883e5090920598a805a0f01480d01c9904075030701403d455460000701601040560300918216029129180407140c82c8030301540c00c45004e0240b07940c0024050128501c1d00404100510f141d81d9802c044a16040d5540000342e03029100d010f0490020391561051402c100780d0440850700034041c03081407814030300b40054aa80d2401c02c2c02c0103030300c4951501002912004180000301d8403103c041c006000c80c0480401c040f040d1000020003814a2082400009018107014241c0d40c4c9404010f11f01c1d20241d2034031101c024590072840080558110005088080703000c20401080c3d414182000481c1c0c200f060030025001590811140b020359040805401c8902c0d000b0448100365222098160f8440b807061040c580101110503040d0b0402c81407205024486400201851244804e801d1001c0d6494644807a24910f203820301c8010050782c0050041a074440c081d0700017071b90200b14400324101301540c03071403006601540d40388181c65 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 254667652 1250 254666402 254666407
    0x5270406120f02100503040305071e02030d0c03090501020c0f040b0303120109090201032a210903050d0e010605060406030c1b0f14160b0f0705060c0c010f0911060d1b0302 75
    0xc50074091013480300c0194600340b2030704618258030b01400304d2040180003007141320507000501740400d10b004180010382e009801c503007001c203070344501170300001e02c0c410240c01280c0510310021341c0d9071000a030340d18a04405003030030a01400010a000280100140c01d941c5030000380610382284105003140f0f802007100b000085481001800090101c03640c2c0541c840c4010000c1440100310444042021055023042c07030700b40f0704100c0201e00a1824442a0a10001c25081000c00d10900d03501001030204400d8003801004040c1513940e045080b14801c5c0724076600140700b40420040c030f5000c0c0c1c0c000b203150021030074803503a080528060301e103072521400021118000c240c0200c01c2403020004400040d010020018055051800111200c404e150f208510713a075140010801c0c2c50107803030f0003520300d0b9550080c1120020300b04210011001d800400b01c01459601e40054801d0148950050186141d0420042070301500030809000c0d0640c4100c010700b003a03d443e0b031448030580f03028402406040880c0d03980141c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 254668902 1250 254667652 254667683
    0x41109031c0e0406030b060d0303061e030201080907050108041704050a09050f1e0604020f0d0c2102070b0112030e12010617010b0a0e092b0f0527040612 67
    0x10072201042c07903514010f0340f9166092000610746100ca40e00305038103c41c01d07684d101891600307c014100e00d8014510702c444e2002188120000e904840003520720076240c412580c0d8501540c169284214412a40040c0c8008046000b1482c8540070086941800e40000d02d041d0f02d900c040703150061a50f12107055150b80307100f0040b44040030b001d001d400c4001d82d07504c001c0003003410400c600141c0c400340006105690029200c603203022600700329401c12030720080038403200e43c164030060f11400c458643c0c0e0f4a0380603821081c0c20300c04440d2003155a4a944941b00f00d9403039090003407028000182c000e080703090281c002c8070280315503500b409966041c00710308004100c0d1418018000c1c0350540c03140081040303038189074240c11941d980c600c40c030054890040e40001c60ba40c90500783e80c617100c80c01000050502c202c00c8183c0c01e44000d00e842698031a840d1f2200110403000e01d4080b115417048420020010190a9a00095138504120740b008250002c0012039030649031008a0301002c40b4590071600801480e8165 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 254670152 1250 254668902 254668907
    0xa06050903030907050f0d0f0f02011e09032301020c070f080c0307150507080a0806030c010f02060f04051f05091203040c141f0203030a0501050901050102030702041109031c 76
    0x440c0d000c0554405107046081c404529992080d02d07000ea2482846994030b201c070719032a82c4070075080703003900009031600c00d0740317507080c0151040c9032442c080e030014a2146100d404200014261000c458150707a4a0004519645403440c0710400054281d42400003201c44801185c0c090006e40506e6240c00d025000241c6000d001e0a0f80d5151035122030441d4103c0a203070b11843e1b801061810403070b40c01c503540c101c02030b820b84400c90301c40c85250300090203500040366107900107070700c09001817160a0940c1214044007800300191565582c1c0ea2000b80180d00000000f00c0c80c1d1100c2110b180c0241c4180100c42010314018201901401d40d0210355107034603500c50400c845418100300e4180c41c52800841e45113507090644500900f0b40c0c00d406280300242004080000545500300d40341090500c26a1704808a1003441000b500c2c2c0d030050700c803910350794202000030486107030800d440c031b0480b01c05800641c40d1182590a010181819940717002c6460b105204d241201e48007400194440204944045282005a0400b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 254671402 1250 254670152 254670161
    0x120d02090a0806010f06031104031b0603140c0d0914010218130606050a05031008060a140f01050a0501030c0e0a06020f070e160e030102070f0b19020304050a02010503041a07020a06 79
    0x1c82241e0198004101360503000890380c0c10b80d0061f15005c210383d4000c00c030001403441a90300041c0410b100da600c0b20800e084078484002602c035243c5c6d0034030410501d2001084011000d4400108000e8200901c02d283c22480e4000c0daa8544140c08003100420468001800c982051b044480031540c0d804a0011519011012002c440c130f851030708000c1141800f000030319600a8000000a1010000200d240343d01c1c00341510b00180000f408031101450041d0400c2c000d810050680d4540603c5d50b004280352020445c580341c161600039000f00d1040c0c3c604001100980110801d01061200c08021000c06450312165000030301710540051040c01141da0055203450b140d0341c454000e1400c03490601650082e0004140c900810f10303c2c0040f2030300d0380d850000380240f1881c0710041c10525280404400c0201d02180c0300c1c8590859514010024844d284110582c8030417200200241c04c10b511100040d03004001658105008003200c0c01c03444903554031000c1c05e40c42502c030000543d120140701810002640075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 254672652 1250 254671402 254671409
    0x1809010b0d110304051504030c1b0513020711011d04061409070203070b0c090a091a010f050414300312060d051906020903010c031b0c081209120d02090a 67
    0x110703680f4518160700c0b17080d00e9011a0582d083c5150032070f4040740500d07102d19581c188031500300c201d00c2113400c0044d440d044031288920445004584a01c0d1604815501e442610b040c0303900200c5080210030383d070004448000c1c562000c269105500e0344000035586a03445a42c02410f140740401902e60017520801c5174072800201800c0031584100b01400005440301100c907006a41030381015103880340d013070024407071a08a4010103050361610104440c51020b030050a200940d0a0300c80d0112030194400441c0d9500c10f601402415000400100d5002e0a04060032103980c4c8400800d50b6102c8402c0241101100d50f080c4200a6a880820101c017002c20b480300c1c0d01d410000880701101c44420720b03900c09407144925603130b110034920f84074008018031840343c04507006050020001c02a8000101c0301800801c8040380240d02c110131501911120348c0210311100a0940001c0d00d64200141a00e018503400741c01000403245000c3c0c84041c0e8500419000070b4a0790200c8080003686030030042d000e105a01007140d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 254673902 1250 254672652 254672681
    0x1090815061908120f0909091507080c180406092d0b09010302040c0c0506070f180803090d030306030f030804060b0108010b03191506030e070801020408070b1809010b0d 74
    0x208022001c03002913488041c21040d2038980d15110780304100e100310700550700c549805c250403600300078050305c001c00c4000503010b00000044070785d260040c1c20bd50080013100c6c0c407a11054100001b400c03000589187c1620818020404200f00740c030f452085066034030300d070300540c881751020000300c503511038401030050243c604030310401200e0100760014020b42c0045c407020b809580d480c1600100705100c0c465410510b500402218105d00307280324010510340070102c807040080e085007031709070381207806400305e0044482c020300450402440c4c03810014914403452040302410390300c100c00400503281501c0152034a00a0b116419980380a04000041d100c0440c407250401000000500c04090400c0689810501c00e44c2412035500c6001c800100034181d81d114071520b0f603448040010b2856064200302c1c0b106e220343c010346050b103a88141e214280e0096000b00012500312030070030701c0409401c101802100700c100b50301c2d04078500540007048203000c0a0300004104600003543c0106400703140608001071000c035 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 254675152 1250 254673902 254673949
    0xa08070c080a030b0f063420040b03070f060f030e0a1704081b0a060c02090a02090a050312070c06080910020307090b0a030e010b03070f03170c0d02010504020a0e01030f03030b0109081506 82
    0x585e1070035407448510410546448c0ca034191102242ca075940302100c491006021600c0040d100d14504500c0144c0348105000528100d4520b0744141c07090180001e0400c14800420f00c03404c80750f44141203021f511481c0304441c58140400201c00c00d0803c5449074101070038104809464080c4140320034210144c012038103010070b01603903500603210170003226881840c03600d00580342d0b0030820025a01d682c03c0d920803030381489400c0c400d140a605400c02801251301c20000d1402140d0390f108159520501113403204c00b5904503010300703402c41d00e26400842c0c1c85185c52400c034080340c1d220141031100790424040c5c1d0000179919030010303c00043c01d00c01c6040380302d0304400500d10f40d858120220521190b074040284624401030710411194201c400303607034142d0f812006940300d9010b1003100900070001140c080e813089240d6540003d0380c1c00740300c0c006410303240c21500c801a500b48544007540031f0704902d900c00381000031841000803401011700010020703000420b0308030420b041c00d2007040000024610302902d0074400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 254676258 1106 254675152 254675257
    0x41e05120c031312020105120a09060504050a0501110c030a050c03090a0b030a0b010507020906011b0c0b1804022a07030204110a08070c080a030b0f06 66
    0x5480482c400f42d40d4407100300340c025030719070080c0c00b103170342005400c140001c4540075662000a80e038002c03440b00c956944583c00c5a808a0f01594242c000342a4030080040a0107042c80046061007079030306182c101440c0944034464101c400050040005413030415400030300903910a101e0041c5900e01071503039107841140e03d5000303d03400070b410b42c42c0030b00c01d50656004109403004260003400c4520b450b0341d20001550451403000c038051300c080508105500156400c80890041d103020f43d4410303126015403e005a1048906d00d160f0b01c547e0043c8100b00000c21030030600e20b03119100585904000415045460405c04d4580010b0b4005080c907900300c1141e40080010070680065594944440d514602c04580c496010103004101220810084c1103541c400e4108400746400180602e842c18031744000284079610020542000d0103000149001240fa814401915024010341820301c1042 = true := by decide +kernel

theorem cover : BRFrame.Cov 254496402 254676258 := by
  have h0 := BRFrame.cov_init 254496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 254496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 254496402 ≤ n) (h2 : n < 254676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
