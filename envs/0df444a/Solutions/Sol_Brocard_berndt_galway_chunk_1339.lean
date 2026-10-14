-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1339
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:28:02.755041+00:00
-- url     : https://prove2.me/submissions/d47a67f9-0469-46a2-b215-19d14dba25a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 240647482 ≤ n < 240827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 240648732 1250 240647482 240647497
    0x100b070503043c060e0303032e0314010b0f01050c060703150803161205030405150c0f18030c03160e0402190b090102010b0913030807120207050a0c0509060d17 70
    0x5035107003c01d11216030520055103d0f0400041402004400e60308012090700e000781c17a50400010b5100d01c15206425010b482408201070408100d800800f144041904034034034201000005803114581e02404804420300e4a8070781484002c11404044100c0003446d903030701660520300003545020b06590005039007065070001d0b0040c800403c609200390340813001c0c03859407881b034082c8248028426100b5180340c0400c5502070413540100d04c640145903503c08019a02103000d4280c94a000c094484445603a041584540d0500700d0742c080940036070604120710f206c0c3c21001c40c01040103591728541c0044224850140404242034040420210344569400d0307520b000c204504e42059503107076214080b081d00320020140c0103600f450300800841c28000d101c42c0c0100100444040d140b0b2544d20103030f5521502070006010400d807030044508000d4184054069948980d02600c5003038514100702d648420710303400541c45030034101c00b40481591080945034456130b00c241e500321390640f40c0050040318025607c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 240649982 1250 240648732 240648809
    0x10204050a0b04080d1b03120b0a080f06091209150d090f0c0f030b0105121005190522031202040f030c03060507030504020906060702030f0f010203100b07050304 71
    0x7a40440d00c1c2402070080d006407031001048038800400d04004880c450100d00188018600c000400004684906548800c1c0c048000d0b0200e22800c1910110f03001001c968041c4c2140e40080b846684440028050720780c0005096005085c0d01090f445255864866001d0083c0706034140b51080c485600400c0507501c0480104404200307403032441c20880f5174150040d408446860440001107945c00c0c005111400f9a5040141900c081c0c0c00e01d41400b21007011424403940e20302c203d2840d4070200180340075151299003004600c0303059881c010480302c166907025140039415100004140c81082d106400e400714240c142c5415a03c0d610307001c0940e00280f049801c1100d440500c04000700612403011060011241b160008214540c2d9103281142250750982d00258030091040104a9a1900b0409080b9003400103068924003440080941d00d4080340d40a00c0010381d401104109502082d0b0880c00009d180080140d450400c9580d21151a441680140b072802000e00340c0e40304556031a0007200c172040c8100b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 240651232 1250 240649982 240649999
    0x1091a030d020c190b0f1c0f0c112404020d0b070c031706150d0609050103050d1b050a08030a020d2414010c06090f17040f0506030108030a1101020405 66
    0x44000070348a80003c10928010014108141c140c03030429038140302242c00900c0000e00f0b003181d51000654607440341071069000503440301a40464000352088109030480c440000a580d001c104001e8101c0c82035025002150b04100310f04040145004940702450f01404140032440c1c0d202c2c80014419008000080c2c03210261504100180f500108400c00043c043d40704d4805041008440301c241d02c0e400c40d811500400c080c407000744411101006070031075258a56021034003584a52526040b02c41c240d10070707100303907124083c4074090b1a040544c115040c060180c10100420781500e5540d5982290030000703100000002c001080154154141c44048080f10014004095841c1e01c144540d0111130880514090807600015141c1813481070f02180382d010307103900b400322010341c6840e00203058517501961012a1030701c0c10340c0041c80d6050809423000c2152a92a1501d0410030f160609900c16004140244810001400400d100106480b540351a915095400e09068031000b40a80515400107401c04200d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 240652482 1250 240651232 240651253
    0x60a17090f070b18010e03010e0109051e060105150f090d03120e030306130e031303030c060e06060603040f031e0c0506090a0201050702060703090e040f02040507020d020601091a03 79
    0x10882aa050041c08100c6054070f48489100d0454400c1c050700040b14540004100180e5000d03201161003280000c000048488441c03101070300356102c1540072500307904000c4180c60340003001660400c0034080100104655030500d000310722000f100000c005040d10f40402d00c10401e208000c00c50f20b10b6000905801860700f4240790161a82044114015150b42407080b84e070002e0f03030008240c0340b156600424110015441991120040c000e0004818480c0400c21014001c90a03042085005500c40d640b14000705072641407401c102e50031410540515009042880700c15a941c0003601c6d0040d80092016515044c0d43c9010b0350400d1420003140c01c0e003c01d1400c00a0001e4018821f82c2186014006407141b03580d40c83d42107070720352b8404040240820340c20300c0002d0160500746d000c0c044440c824104000e40355151145281c0c200c80498080f10b402c9810b140700c0c030850419005680d00901640001c0c503058440d0b41000e900d82030140102c1944a98500d000c05c010080c030012920302803405015140d1040d42c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 240653732 1250 240652482 240652501
    0x10b07060908040603050a1a010f05091f0905130603030f082701021b070302030322090501090606030b01021b06030c04031e05010605120a060f110d0b0a0603140105060a17 75
    0x30484114807448e1074981c000d0300700300c82d0003650040b0140503540c242c03540a0510080c1c1e035a4011114190b08008071030300466076840318681061244a0944400441a14150800083d003400132214003480c0c1c01c1290410000f80c000d10104403262581c10100c83c50743d540708441c0e08900b448400d5241c401c203860b4003801103d1042d0700405448a1700001001c0d9260394140c4103035140282d110080d05980204081c0d265140c43d031134540d1000c42c2c502045080309a84c0e03820201a180f00381c03c100401c6548240400c005905403286015003102800030381390303242c020aa81340000b02e000c82002e0050f600000002c6010b0003110031200036692140c045203150802c40013058140f00c4000040318103610341030001c80c051924460b410350101c40c0d0402088144481d40e20030f0040d015400c3c0910301981c507076280c406490300302005001c1c0d110221000013201042d810400890840e00d80c415014103180813141d080c1c05600003003071415541d0542b00107170382d00b01c00c80d4201c51032004452241c05611040007441907208 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 240654982 1250 240653732 240653741
    0x6040f0f0c0e0a0e0a0b030a0b0403050c1513020f0a08030a17010506030108280209070f020c0103020910031107170712020d080601360609080a0b010b07060908040603 73
    0x4115668403401c0b41103400c10302040394280d002d012502002c2000088000f541504241c64a400140070f443d80c0915035038440407034140a95088020880200e00382441802c200042d072011101211003101070b041810852100a2080070080c1c05040d100840c1034250700c0700e03288080140404001c0702e59400c1d5444000b000000c0c0c442c4070702101003130000001070601d89503050341d041e1540030014000c19114440300c1d2110000e4031500741e060000180000c009681c0f825901803090300035441c0e1181c4500820340003802d15900f0806181071510500044000e43c039100b4200c41014140c1c100000ea91012191195490192000080180714a400c1c82078110b25240088c0003080d00c9071020307181001190a050342c0303450780845600d00191f40880040d00540c8500100b40094108004050500340c82480c104050002100031141403d24074004010840c1c0c050070250003445c005018040b01c407400d0743c03003626012040c0300311401074101007500414802c0c1581701007c1a43c4c403045031642c86946441c00380180 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 240656232 1250 240654982 240655001
    0x309030d0b09010b2a030a050c0c12100e0106080a030e0307060918090206070f0305040f140a14150d0b09011202030d030f020904020414090108030a020c0906040f0f 72
    0x103061020461260402d030342480d0503540107455141c10401003840e26514941580f42d0182c541058014400040f0800e100501030444281d40c3d240d07172810368075450791608030f84008084c080c5d100404030b04030707441011410100d629988030010594500c0c1c0d03410240517141a030441c1506016042000042503000500762104410580580b82c4460b920a0281d0b0b840c07030300d40f00300c07400c0c440c072a4003510451205500284805100034866420400c15890740d800014104500701c000c140001024010003194980d0a0000c00030708050301c000c2c24030080401c10190b550710855a0341e02d44103060454660340c4144001c08004200303040340d11442820041805003600ca02c01d580039028840c004a542035401c84501100d43c1c026004014461401408030024a0b07400604500c455081c00160341c0c82e92180001c1005280e0503164441800d01d0301e041001c0e00d40306a1002500303510800a22101340e40201f400341d4160021a0080c2c40d40d60380402082c0603000c0001c0c000820f034681011040ca0f240d1540c8480000d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 240657482 1250 240656232 240656257
    0xa0318030c1e060e1c08010b0a0f21050604050a0606020325050f0105221e0221030d1425050708040e1b04180207150903050c0606100c0b1308030903 65
    0x10550850406d0310100002c0c0505075031280c0c00c000080d2001c0c01032004036240905480c00300c1e04248803500740c1070041040341c1381c8020755440d1001e001842c03519010781c5801051500080118518014001c1e50b40c3c03040741c2c00440d400b1300c4090f00c1c85010820500c001c81c92904403003918801c20f8017036060b40c020041103581d42300050351079000c5803c2d4402500440c401c154024140075103010101c0201c1038601d9000b404070b922464800d9a80b44c1c80402c0130040302240b1035a80110785030b00d41c1c50b00f08010b860b41d1461480303d030101d030401c10821000040a983e00703c1a007070b41d64610307100344070f2049406114803007000e00110700026000800040c1448514400c290030200c86002e00c14603021548144a2441840e01d0809d21441d84000454250b005001840c4110081c140740840d45809000351010013a007070300890b82c04507040c68041c0b01444001da00c045e04880407e07600c004413101411001114030081e01d0b40600d034000035502203002c0940c100c00e60f0080401a100d103040b4038566500d03030110344038008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 240658732 1250 240657482 240657523
    0x80408060f100e010308040b030a110d02070507080a0c170c0402071101020606030d0504150c05070b04030201080a0501030c12050a0b0a0c1101110409050c0712050a0318030c1e060e 79
    0x3030341c0307003c495101e05a03944051440d00e4140303000030b42c2550750005010b015045540c0c81116072a623003120000c0c21f1810240d04003503111912401c001c0d08044581e405a500c0c1c2d00114106000240c1c141207a00c00e95424170400f1f00300d81400c1c500c1e1480c0a100014181d0454400203101c410b02c290f80281e1419050309901b03c407000d80e03c540c00e06881d9a5402d640781c01242c0144824041c0301080410441c042100d45041c0801c191036803912480c02031550b10800c085040000c0500a42d40d004400690080490380180565451a40c401840d000300d403140804441c58101c0b86010400c0a00c11b5048560700150200301c5420038424881c0140700d0700030078001003819002480c20506041c0501d0f081d440e01444502e00b010714004894020306130080ca441c105030010465040051044021400002510f80e921615064000000b07400c03103525003125003403482c8040c5420002a0700009009609902061505030402071154043d54492840340052507a0306000d81c0c0f90340380000042c0041910520b48401b41d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 240659982 1250 240658732 240658739
    0xd150e06010309030c0305090f06070b0106140415030c050706050a1a03010e0a0f050723010207090905060403030c09050a06170a0507090e0606040b030108010f0e030c0316080408060f10 81
    0x4088403d110402004a20f055014402080c05400a4a1009006400e10082499060000307000e9070044204450200403880180441c2d41d224200c9001a403c81e0307401460b0a0920403041c210120f800c0d0200201920344000408282c45901501d2800d41c2c00302080c806810000040703c042c114408110815017050705c45030010349414054588003101e140050030b44440c40d038480e0840d9080004065600c0e10810400040300ea081511010310001c445540e14601d54070540020708100541d403107001110f0500c01031101007103011501640050b41400c00140764000a80c09680306d40080d40201d80c0220701040003d41c0350741028020020747c13814000e00e9100e82e0742c81c411404440c8152031820014000e240240502d06c81200c103170350810401003610341429515030b000700072360713009821000315039441d42034544a8000394010381070440c2010015505041c0b01c7c0b8401c2d543e90003036841c070b045110341c00712032602408014821980582552401c1c0c40b25807400500000d414072080d104280345026084001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 240661232 1250 240659982 240659987
    0x40501140604110403020f040e0f1513030504090b0a0504060b1e07050c0904110301020d0b03210f0d06030213090c090204030503090904021801031124030a0905030d150e0601 76
    0x3c02051074010b0f4181030564080c0203040003103a0300d61303030825076034072904101d0712080050442404401d0001c19039502c8182e0403004c5018081d041a4440c014101507000080e08101654181d4100034070004080c0100350000e80b040d100c691100780c00c5841c01101103640b000b040000d01d0112954101c2c070310700e00e0100720041407520500c0ba024010342c01071070103005180340417040703036800500940c010100c1c2c106500020782240e1181e03a1809509646042d041741c2030805210101003071100142e0901d0500c20b404001a06228942c4050611000028041012101980201c0103190080e280c890640f22541e1400010044c02e5801c1d16620030460300001d01c24800e00072182070b25489405141040d841005000810101078400c03640060040547c80c004014400210700031030040600e202d031075190301d045c40410b0a40c0f140040701000c401c1d040b240319000f00821281c12404000d400559510241003c6096006000c4240b050314107081c8030125610f6201c099400f5124808030706143d0741c070ad91005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 240662482 1250 240661232 240661241
    0x303090302190b070e0f100503040c0b031905070216031112070e06150c0a0803070c0f050604020f030307020a0510020106170106060210140406050c092106090109051f0f0203040501140604 82
    0x7503110703502a1f400702d4494800c9010710f03001131207441d4100c0510746894a502064000700d45480f1411614144514424154011160400b100c2e0016001c1215000000c106602640c04040d000038241c440c0b24015494264041c0300d03078042c01c01a2802c080d01d071511418807403810740e4041e104400c2903d81030030304011281114500d0200310300504412546d641e43c8019078100030402400e00c0340c11400440804c492030190382d2120311441c0a428503203094030400101c1801c602d101ca020744d0044c00304c0001070b10350310300741ea05440080714990000c07121003004902410040d000344201c1010750040030020041500801e080d6034058082d03548000d5a220b034401201d880030030f20100704050b400403401090840d03111030703040546110385c00c0c6050500008600c1e41c12144403a45c080c4032500c0c0d0345401c0075030280401034203c03131180028400c844039a1501503887d84030203074140e8820200042c245a44003030b5400000c1007800718000707640300c0c079050521500800a41e0001900d81d00c1c2030340092000c0c60103124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 240663732 1250 240662482 240662509
    0xc021606030c1e080603150603120c1216031205151e10020706140301240c06050c03040b0702011401210506041b061b0303090302190b070e 61
    0x1102068a000001c60203400c140c2da2070781c107200c040c069044001405901d0328400f00c02c1a1601c2036281402c03800c0c140f40c503d4450340040900d84400070304c030050780c000c40c6a4000c004c402c07010340d0b250010001c4550800500016201150b580000c1d0202c00d05045401549001e000c2d4071200c40c104075248111003500c07001c4502880050610000075000c1c0340100068242a22180700200c812140b080030503106465600c3c06009640100c1d400c20940d54890320b0021264414002d030f90075540f51141c218807110110300242c003000189200b0102c40c2c1d1042513648002c5403c44001d0000e030070300c0229000207600a4074181d880b01107860004801e28014000e03c1d49501d07030409000090703860501d00100178000b00d0151400404003040203008a4000c02c0040d000301c0c0a104094001c01030602c2c00c090202c0558024030512404031144011101e00c460300488644e0142004511560a445c00b00d0400c0d20440c200c160310158240030b1010302081c490a68410021600c0340b0884410400400401d105220f6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 240664982 1250 240663732 240663763
    0x91a06060307030e0a06140a0e03040b030601050306120d050910030b010e0f030f030c160e010303050304020603041514070f110703081b0d11010b0108010e0609040c0902070303020c010c02 82
    0x1c0801c041c54429031190350f51403e481c0680d80c096002d9038448064415400720700e00c0041703081040c066024694030918124030b0262009528103450030f07040c1085400000c1070b00e8144400440000ca998032102c6004000c5080d03501920048001390f00050501e411001e00e050091601d801010038250203841900303000ea005843e04907007001c14004102c1c0084c0b280100340d030140542c0ba4019440c10381040902451001c1030b02400581d4025251280c1980c0503500c482042c01019004202180d00841140d8200d030301941c80a90300d54a80c2010010207001c00e101c0036405241c407030100c2100401d1510710b4003400c240d5a405185d040158403c6450b10b8110b103038607503283c000860400c0000d000d84001c100c0d0391487c070201044031110a65680c1000b4130f401100c00407039621000e03400604000c0c032508200301002d0030301c0e2056504181c8080241c0c68001d21041c0654a0f54002c141480f800c401004024013400400790356410052a0080c0039401000c0f50b8100c543c20041400707420380c000301c2c00120b00024030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 240666232 1250 240664982 240664987
    0x6021f021c0e0c0a0e06090a021908070e0a1413020405030706180e07020304060201060602191202012007140106060c121803061d0a030e10050405040f091a0606 70
    0x40c05034400a20b800c2d8080d10030b901c90618180565190780003c14014807251000d10703050b2401100b800f8043c14014800340c24188100850200110b0514407012641914600b16007165148075050703504000035000964002c1040800107101801e2055100400700305880b03061214040ca030311582a030040c0d01440358103410900d814450750b4810302600b007d00c1c03076030140e804c01c059950074040344502c01500d0703a00040e0070004003404526024000d646c01000d5510041119000c0c40c41c02070f440990a0600801c800e00c418411503801e4400d41041003072880454081030740e03d6000041c45482e0303001c3c107800c441d4547d0020b00c44003104010301c9084220303000c507255024041410743e44d0560540d0503103000014403600d6406c0c21406107200302c40d0000b41d0b115201c0090914191600440d4170140031034a0306113a84000194000683d002140c40303045a0217407860a0305078481c0318150703070307030301894018a80207441d20b03464040c0ca840c150005038005010b81d0302e0b0b00703810700303070352828042d010089540d141c010208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 240667482 1250 240666232 240666277
    0x1030e0a0b1306021204060b01021b0f060307050d0c02070602010606090302090f1305030c0a021c0309090f06090e100605010801060c0b070e030d020f060106021501091a030706021f02 80
    0x3010b00b01c49083c0c4100c1c0010b14011004e00d88241211060ba0141d50071a600c4071000d0007540c040240f00483c600340044550003003280d0000540403161648030790700685000c004100158020000d8840d0415241c0c014840a0002d4000030341e40c024a110703120040d03080c1040002c043c0c0c01032940c44252078001e04044015660401400d00814015010303020340f912401440c0041a01407010b001120743c040c0150001402a004005481403800302d0058005404c80b4108006608181c105084560303907500070800740440c100020040216512001c4408d06100b01d2542145c030100340541c121068840030041c650701c80c0d00440e49034409005480206440104032400310390190100c1d580600c542c601944c01d02e1074600802e06084100b420b02025a11410b181d20200c0c10510080e0b0240c0b000344000d0480d041145030000d1340250620031001d80035550145010000c0301a0b00407144494003a085609040d80c400c0000d6590345805d20725441c100384500d800300900365500850b04086041c000303142c1c0880300d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 240668732 1250 240667482 240667501
    0x11012001090302121c051509130317070206070e03280510060605040303030b06070f23010c05070803040f0503041716052b171e030601090e040c030206040e0601030e0a0b 74
    0x100030f04000c800c55218082810f40745d8070082c108d44070b41c4071f248013021060554907000c1d224461288a81d0710340702c0108104100a40e0004035240d05c4882860800c240603094000302e4100594482d62801c4d030080742e000e942c1c21201309040b41d9000c5100790216003c02501c1d40b594012142603004c2e030400180c04020801c0800d00c40d400100781a58010400c91070314200d90340f10342510350440800c03507003603a81e030001c4449480e0042080410104600c000e00000d40075071802001c1d41f00c3d0348401020381d000031011600f03100030401c42401040d80441100d0b40c4030344800700b0303080c113150030a240b01e4144a40c4610407282c083d03803e005000c40703902410708280c1c40800543c0244d40d511403803501c4489140c94014901080e001c1128000300e048401c02d8640d207042520390120041070158004008803410400e010207640e200c0c02d00411078120740070f81c2c4440e0b01d407440e018460341c00540c8040d60210001c1030120b0b26500140980380a00d209807020008034803421000d135212241c21030094018003031a0b0000d00c0c0c1c0e03075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 240669982 1250 240668732 240668741
    0x1a010507080c06070e030c0909070611010209090906040c14030d050a0e0a0308041d0c07260309030d0b010c050706031a1305060102250311012001090302121c 69
    0x34801c4070300a040c10303105800c0e14605141114020009202c6040000d142d0505110060502d84262500540c9182000140303a5070704440c0b148000b080304411111425110070742c15100c0103c4010300001e0030342429400c0a0b41ca50054070203845985083c54002040c52051095005510300070300274020a03114074200b95416000020350a060200e4074044803c2c07583c41c451004003031442114846d40722414070400e990107191070268464440d00d040148200743e001607040ea805c090380a40e64003490004001c8178001d8030300e800c9104044810200521841d203e01001910021540a0042024241d007400469070701148000280c41900041011320400744a40c2040d0900000310f201c000c240c0240b800414400b4100c6486d0009899560f03040c4252503038140400003940c10321855400d07400b008040d8a09801d042484010f0102180c40c500b06030f5640501088101c920200c00012a2440c619901030b020f03007820b4030214014000c0344c1070b000030510900c064640258078030340302c90381ca2101005098005d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 240671232 1250 240669982 240669997
    0x50a0e0d14211e071106041211100506040c09060f1d031203090f030405060f0c010605040f0207020f0108151c080301060504060206060409150506122d011a0105 70
    0x4140b100d00c90555501c1d041e002c2e50060491102e040c0f40302e2601800c10b40d90881c0500f0140810905640700741d0307241000111135811030740004d91010300c00105c010685110040c2100e520581c050070481701520403ca9100c1482450f00703079420f000320a5585008c03610406035000324008100b400608404880c407490280e102c91614460f403460010b9100c000a140241038040c0b510002d50010400c603001409018042c40105000d005604050a000019015000b178001e40c0303503055404160740300540d1302504044020400904100048541e42c0c055001a5103c0f09080c1e000e08016001c1c42800e522918a003407080c0c1a201468200071442c800f0008171402011962080f406120844004240448001c50082485841301a5114600700c0007a04107840206094412071402100d4404903803409102ca45007003601c600003c1a035030381400101110f66558540c0ea0610500542e00540c07040031546000046100b0410f088601103080034500703032410306404c4801d07083e6a100c8204554000d4000e000300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 240672482 1250 240671232 240671257
    0xa06050d020d1d01020702030c0d0b0402090c22050910030201080c090409060f0c0801080f06070807030207050a120e041b050306150d1a0d050705060d060f09050a0e0d14 74
    0x80b654402c0803a043d4040d0880f03003c841e540020a1421440c040116544682042c1d50a1820302156120401104d45c014806070183c95914001400c003c90402242c01007a40c480d500c0180c4600201c3c11310f0b220704580600c41c001c030701c4d07840441e40c542e01c200d601c8001c50707905079200c00035951072140e16182508030000c030503002030f214094000000d065019800040a00207400113000c802004010401003042c3d0214071241c0040143c0c02c8a10004070720980e2001040c1031110150f225590210000d103d200d402411900904441c10b00300050725241c0244071100d5503499550707882032402c100445200e91030400c00c17004445c0b244011180600055548407078001c01ca01142c40400318403042d154080c85107240c0c01c0b03036125001e03240740030950519080c101040d13a6600e000080356440f10f0765030300f440c0180c510a210100303402c42e2003800c940045010b007404007940d180700b598401e8a00080c060a8542102c000c0c00c24205d00e99407031001945040740c80703440c3d440080101040304141c0c295031210070310844 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 240673732 1250 240672482 240672491
    0x60806100e06210405010c090308220b03100e070f0504030b0601140403050616051c271110021207060c050d09030c1a0114060313050106230a06050d020d 67
    0xb0048114103081c0d000c0034140010f03583e80781901c2c180c1d0031562110003050500080000600100f5501825a10050003030704030306503107044030380504092200070703804030055600020801031182e235040003000c100c84449075061a251200401a40e444203481d060b4800210188001c1001c43c0d03810f298039800003010f0409015419004504052a50240c0c0042e5040d51100b0184180903101c080501110038261a041d400c1c8840802110300c140384043c40a00700032384400110403944614140d020004909015420000f5000d150602d80c0b0b00d03000c01c9aa106860460388140e00310300206003186c20400e03218016282010580d95500280101400300c001c0042c1401005000c040381d110741113031180691140e1190442d9803400304005030b2010b91036444039000500420480100d042a600345004c1142c2c2c440c3c03280d40e410007071031159108030005804e0390308046000803a2036000c2100101d6400009140350600c24640c03c3c071000029601c80e20b4001542004088140242c5901400f00e0711078841c0e0105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 240674982 1250 240673732 240673747
    0x140f0d060f02070c0e01060c020109050904060e1c0201141e07090f0909120c0203030901030e03271c11010c02040b0306040b07121802041d0d02030a09060806100e06 72
    0x4100d0f00030704000c980c900f00940040c418000e506150900601007032030200074044e165400201448000c0c40340d60b00580880010500700a0f0766048400384190380c0045400b90907810f242c070420f0040f0410700710003551a042801e5200301e081e5207514400d007001c1501511402000c0710008008400138201c40401c02403a8001c41d00222840d0400d0041c80b011101250144160400040e00c800440c09001030152180200006880100c1076130b20500003400c0c0086c051100d021854154400c54403001c4030038102940c412a4000c02c017039490a0341c44207546c0e8005054110b284501c00107030848018000c0300004000603001e40c440c2c210702021501c040c1001c0f80040354240480d00d403070710540d0101e50b006c0e0700c0001c000c0856070155041c0c40e050300c06401800802c030201c0c0d4210b04030540d550003a00558444070818843c03a86408401c140344031010480706400b20404009403280c02000141c0b0001c0d04e51600000c403e4412001c95010b1440149462429a103595003503c16260500542c6e4001c403040c403104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 240676232 1250 240674982 240675011
    0xe040209041b06050406030f02090f0405150a0902040608130c05190801092102010c140f0702060c0a02040b04060302010206061210020a080103110405041a06040b0a06020a0507140f0d06 81
    0x4500a080d0341e00c0d05130305c480c10942d000c3c05880c1d40c070b184128201d1040c42525400d45d905000c110803444103480c00a49034032000902038a046241d2452a084018240300003001c511b190300510448240d80c1e2840c500c0d032540c059800c10390803040e00141c00b01a0341c5600344201d2800038064804c0d010420b8890f08034566406403642552042541a01c1c02e000041c80a84104100c003a800da4145951008025552280b40c020b003c600e45800d41d401c08000104504007074581c0c003012145100c2d00208020f444802e13181c80c680d034858035203104038016410801b102809042900817401030781c2d4141c001e003c0980d1030300240042c0b0f06110b85004010b208104072108802400e200a16503001c2c541e0384c1001940c11401c201d50b218040d05003081c016481d01e0204000b1445c07158095035410310101e04c4005a8072100d0018010303010344103443c0e80c0100389880012b000c42d0002014052248642c0036216460399488602511540c0015550307040140b80313844210b140380141640403014840c4900013110060a40341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 240677482 1250 240676232 240676283
    0xa02150a02070905070201090c050102060702030a1407020612100905041502180a06270b0f070c0503032a0d0807050702010912120207080303060312070302210301091103010e04020904 80
    0x29070140c0d41d02d41c120b205000002271507101404080c00100700740e060051000359a4800c600c41841000f541003910400345c2141c901302e40d4941c2e001405a521880c00101c07100c4440c406941d0418036100c440ca002610b41558016036200d41d410918070301038410b050400c140039500515440c490400c1d020b21860095442200002c058209681c410a10800907800811790070115403401c001045400c1041101030303450300440e030a03850f42051240c0ca8001902c0e00106503142c0d038000550501012410205408a040508003041e0080440c1e1030144a480042503c0f840001c00c0362000030000070004241038041c000610f1058410b242140c881591340e0201c43e40382000e0101241c00f0aa02920640000c0d03041240c54054040d080240d4a0742c20070344000380d0307600c2c1440442020032002155280505000344034a94239485410320315001e90301440030050071036000340071b40c09442d8074040505000010394801d8a05031280d0f0746504c02c2d1929144c0802c4170514000340112100c41c8203220508600360510b40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 240678732 1250 240677482 240677491
    0x70b0a02090a05060304110111100515090a090f03081906090902031e19080c010c020105010f09150902030903040b0a0503091e060a09052505040b030a02150a02070905 73
    0x1001a00c46450070200046200c0d10b03808140f1484060041c00b02107012140646401002405e1924800320b05400f0a8100341d121104961903510304001c2041030a005004902c0f2401c00315986402c2d079132800000002ca421142c006040ba910021181c00043d0007150881d80004101940d031051103c00e10000090f40c22580141c58107640340c860400440c10200840c2d8110500d121090a00d00303d2900c031103944d00ba138902e841e5001058a6020320601120308200c3d14801c0c203010080c8042407400f070300a40600300c00c0c46422142d110450001071000c0142c861002100100003a0140c0c182c540021400690809080031030340d03002c10000061982c604000400c5107411030340f5025142d00d072911034142400c51138501ea06d60307940500e1240045c4400800c410340c0c0121406400900301d0002c1c02c04078508040c010712001c03103d55080100391440d40200214003222401c80c0c0500031030b0364020508d070300c508807004000d400c52101e4400c500202541005000e001c3c2c0f1600c1101c003425503482054082d0341081c1c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 240679982 1250 240678732 240678751
    0x1303050c09070905090406020d0f0203280c12020906090a0602070f120c0323010c021f1401120f020406030b0a05090a0201140a020a171306031505010c08070b 69
    0x110031900e0401c0726115034000030505000403082d2525012440514000340001c040c60390004041660200c9584410f607084500c000031916880c0034800b0071055424a0002501000342042e983c0c1522040d00814442c694295502c080305809442e090000e908124891a48541c0c01e001c410320b55203a030590070700140140d41c001c29600d0724143c40003507a541c41d81c1041150b03650142648011400d03650340101125400010f15140d0041c0c000410084c040b890030510769542030440e2001c0f80e550000b0101c0a1641c06100340340405407800d01042259800030000250f81c1480004000300d516100e20030000d503000e0a800c44508102d03034002401c0300c0a5800c125105070f0702c4020b1042c0b4040301e03c1101e030702011080050004144c3d0f40c0001e4440003e99440710b101c0740001810450003407081c0318401c4865400408454003001c001030101054124449005070840b118400003001880780c014600c0a01c40004001e003c4d90070800110313044614101e041d0b0706078800300b1120001039290800c05110f030300e054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 240681232 1250 240679982 240679993
    0x12003040f150c150b040e10110c15060d080a020a0606050105070c090216060e0f211207090806090d090b0703140a17040b010602010506150d0e03130305 67
    0x1072845054000d650408000d080c01c511808105580050f0350030389640c0c010155640c100c0b2507808510203014160525038102d03080920b05d20040c4030001d5040071444804400b4001c014003001103c80360301440040c5c0615038403089500394850804031455401c0303d0040e0248080b48000c2c3c40d540c0306640000d100710700591000c1e400311b06000f018070400001d080e09117003070f51401a194541000f0444640581c1d20841c0d40065500c0c08128404000031080e40e004d1400e0142c5800707294032030785401010b05402c20501540319006415444000102c1032040013014660030306542d9000c807408010001c1031343c010700200b0704010800500030030441e4400d15807030300100400d0300088170081000019034044800001c1c14452800020380200c400d403522040204016142c240042d42207075040012010b0240146002d4144414421202d100906846540d0000d001c9074071142d00b403006601d001c01342d40000702000e1140304804c00382ea4105603601c500380022282803d911580030a440c0740700b40d00031202c580c4003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 240682482 1250 240681232 240681239
    0x10c080a0c020f2d0301150303020307260301030f0f140c011107060c26030f1e010b0d02070c03120302040311040b01270e0f091509190201200304 64
    0x103c580c0c00c40c125080da0740140c0d50140e4801d138403920440c0041060f8905400000303070b016440943c02000b07039410180e10040300c0c541d00d003806900d0741c0c00a07005803502d60381300000381c45904c83d01403404056500180207502e168a991074405101c40c00040448610300302179510804929100c0c00c0041e804c8440d0042e2162070380503400503081080b81c00c0c010744136801992003000460f030040c0e89840300c240c0140302c00100185441d0000011002c0c21800ca446d80c0021050050940070514050320815000201143c203480181d64004040004d1062070140c03142000070b07603a2110507402a01881744240183c2e82802d0705c80e6120340119159110704000a0380c046810014845000b801c1c0c5e102078001c2d502000152020307800240704801100205010848002100c1e1170380c0200000e08006080c85034009003141025107599007454415151134085224051844d400d044604800034022000907000301500300088500e0001200c1640c0c099040c032105581201030800400c7d14940440306103005103a5030b606 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 240683732 1250 240682482 240682489
    0x3070e01020c030a0203120703050c030c01050403111501060c02031c05090f040504080301120309080102070501200a1205060a05090a090210050c03030a110418050a050a0908030103060b010c080a0c02 87
    0x10300d00c0b01901c69401214814007503140481c40103890781c4d450484035070350720a50070292000d00c9001c6042e041e03032000050f0b042d034400b019442035020324443c1e03481e503102d00d480012541d500c6000c0c00720928150200d40040204038040c50440040b24400740986554180ca8804602c4280c840241d8402282c800181e144c45483e0401c4038082c108400c84041155003020b80714040a070105001d0910368071824400503041c140101228002440f404c4025582d0742e1072480c002d4080d04041400a07810104e0000c4400c0800000d0107641e4258000da680c0c8135290b00c031049910182901804007500040100801300312900c0700c40b2403130303c101c40b045000b140c10083d6106200001e40302514400c100702017030003642c840039000b000300d0b5000180030700c0c04140e07900620190b61443c42650f01482e0f40310011001440300301c0d003503009070b8881c1c0d0584404008560714600385c40241c545110008014060802c01400040e5040d071080e07050b54010b00d00141841d100d0f0742e4400551380982590300200e212a41400c0843c41c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 240684982 1250 240683732 240683743
    0x120a09050d0c1a0705030d020304030302070b100f0f050102031801030e01062d0b0a031a0904030c170f16061401080708010f0209060301120f020a061701120302071203030608010203070e0102 83
    0x20003d009403070052192206600c0c0c1c001c01850f0012036400001140c1414400e030103a03005541c11007002c540c1030904d0092140c40101c9841005501540b91100050f031700043d50804088039410380180d85851550782d1030300a4420b89400480c145561065542c0c1c100d002403080c80080d20143c0b0f5201c0d00300c540000800c01c003a118045410320501007007428000707180c4010555104007868200858201009000158007090b5500c100f60090042e504200c2403550000380a84031a004000149141111684200ca584100e855088185400b0002001c3c030101c22100c0c20040b5029110010384003050380b151002c0f10000381c2c0f22160070b9200080c00c9c00a0f120a00c1044080c02040c0380c110b150400980105901e030105114070700806076001922130500140032081407800c1d90060400c82034580325040903244100106000f00c50b0340307040c0c0c00403850350b038500c841035150b0703815400402d0142d20782895015492640e140403410140c5500000481c0d1200740050350180040352a103000c1215128002454203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 240686232 1250 240684982 240685019
    0x40b03030c070e0a0f050708040b0a050f01060c08130305010615090e0105060705100f050a060608041a100b04030605041109281e06030210080702120a09050d0c 70
    0x94108011401e02a40000b5020303007120030312081e03818256aa07004010041911492018086003400b08002d512688841906d115031310454075400f89480e02c15001c8100c1e14111600c4103481100d00060102da4018000390700070038403c1e80e1207460614048440100c89506071300403035107a91580014081d0407840b0100000e64031036450607011103450a590040d0390a811b1003424040d80000a40f001841018441403105205000c0b0500401d1a070088100040c182202c41764180c501c0c0c00e03000f1800900c00c0c894140500e070803044031140c2207440d0f4034900328010050414600190340920004000c524400504002c50040c41d0018081c0b90904103178600328a8225064818504002001a224600c81104206103281c40003031060803074540b0031a004140740d0660040b51505030481c501c56040f070350005400d4034820303a10198118200070090700c034200d0588000c07016030003281050b141c00d904940a0414040c4501d0401c1c19155244e0108034496040030040d600601809810b0003a917921641c42c5000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 240687482 1250 240686232 240686239
    0x1603020307080f060a0b06040902071110030902030a110f1801150c05100903021e0601080705040207020117071817010b010207060509060313020a060f1e082a0c030702040b 75
    0x2440f401c03001c83d40e140e040083c04008110f0343c0702c401080c1901d5020503500501035800003196200500e052410000019125a51040c4030300641021074078424011106010360183c020240d08c9099a5400e51007103c90103c10f41054a24280030003c1c2d0303400c190a0154030340650341b104654140b1b03410b00a07402040c00e001090050440132600042c0e00022078141450361460002468034032403404909006075100d0109000b4641c840341c20821002090040c101c543c4901258011503031102444140d00aaa9000c0c0c0415051110303024406081607006034084060300d8580014501d0b1032280c0302c218101e40098114221015180307007010b90034410000e210000740000d000c101d2074000001c1140c420004520300501022010503803848517254546d9445500502003180c4c6600c0c3e1400800a56204150000154100ca00d040c05550460444146404076680301c0321a956032a86071492038651400e44030341c0b0005500380801e800904006001500c1c09180515900e074000d004102c15102c2070300400e0720 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 240688732 1250 240687482 240687493
    0x30b0711120306060a140a050a0908120912070b030a0f051806070318141510030812040f06090b100e0f06090603031e070308090c090705030c0c160302030708 69
    0x11a8081082d6903022008480440d030340c03229a00c045603469049005800c4401012075016250b60704040645020622551082d0b11188d4600d440c658509400030340e442d101c0810002400c3e40d09201c542c0c40e8003500c1d51811034035001ea0383d07018103005030320403660703081403070b95442c1c180310200a58000c1c030b41c01a5409441c5042c109030307a001c3d15142c11020b40140207040d0303103140c13440c100440041c12640d0708d90043d00c06a1000c1e6001a03064417011030301e12000d03254082e48006203a98a1244e101801d1365003100e5501d0810304454090560b020020b441030b10400042100070340052502e00444031481c0c803504d0341191a09250346044040c2c40150440c86d1807031000401c0208040c022100c29a0081c001c44990000e40c41c0d040101e815846511411039882400001c00c0341c810035040c00404400348030340c1d64a40c8a6886000b025140d01121184a502c400c1241c0400c80c441e111b48003940c0c02013182851149401003c861041c50121a4030f420341e40c0c000000401c1003941390a00c8042c0003041004044e24 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 240689982 1250 240688732 240688753
    0x130f0e0c09090606180909010207121d06090409060f15120201020c090402012001060f050103060806160504181d160314070b03070806030c030d0905090604090203030301030b0711 78
    0x41c0c84100007442c9a000c4d40c000304421508075002c07001c0c0c1c034254a01510552a03070a04400542c041d5008803000e82c1d0140585940c458554442c1c8035030300c049103c0407680c4880806110421110383c1c0700c1600181d00544407015607021403041d1140300c0120444080008444603000358004008005d940b100c0510a6205e280001507600820350b80742442d001c03a60101c107680e5034070060340c40703910403440048400c0050a03034400e5528154820001d441c004500c51245a58030380044090b20a980240300c0c0e560804030100e144007914007406011900c660402030b0406886408034000400100c2451068540703842c0e04074200010449031400754020003025048098080c0d2100401d0981880000c06040c440c5001e0818a40705012146c09802601c1c2416500c1c1428100144814825200c852107402603420f1122649400a901d0240400c940c65440e041490a01003102d108002464103401ca40c4401c4002d0050ba42400154080c600c0780b100d00590341801d00008040c1e00415084100d40d5001143d0203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 240691232 1250 240689982 240689989
    0xa030b0103050f0c0d05060a030b07080901060b19050c010b13060303030b0604031e060f05010603090516060e041a04050c030f010f03020105030105040b0f0301060b0901030e060f0103110303130f0e0c09 88
    0x5480303542c5d0074031000c102030305c6250210355060400d0703102802550001c1c05015206a126040e039024204d4500240310081c2c962110000310321600055204881c4180e1074403000a0280000c0e00c0720000c2c1c0300001840c0a40381d004521a4902d480da103201b2642e584206104054140c41010781d6031200f6240f542c2020309503541e6402c0c1c80c044555a007404414800c441e0100a80d580202500d100a400240641c0d650f07010050094488520304907124001e03000c10003100015080e1550448038243d0701c0380c2e050004c100078000140b40d4050000200143e0003407101c40342c0c80300d005090250a565009580d03d140801d000c441c0c920040c1c126480064041004101507130b807003003d80c0c1c1511402c450010300d00340c05100040340040c1206080e5015420003038002102003000300544040502030301d003807015280c4295090384507101181d0000c40001c28a006201046c41c3d203040340c030721100c094226440c0000d022002b0909070040e80c84000803102c4641c05110305000c00c1c0700715811041c00001c4506125104000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 240692482 1250 240691232 240691237
    0xc09040207020a1a04090f0e0c0907090305030f031005100c08030a06050d05010c031802090114010302040b16030e0f030a20040207030804050601080c2805060a030b0103050f0c 77
    0x6106a8000ca5084155a40c458124009121004a0102840c1142038031455504a8072402a52914081c08000c0780c0500d40582041034070002c003d031030710310036007001c10030401720150102d0b082121040000c00042d8081000307104000e98102503640302e180200815443c51002e401660244106401e4180d42541220900c130400b540060895280d035500c4244030002e00c21684541e91003e4030716101c0045c00019844000c144e409035405000304088000101c18101c00750000a400c01c1c29240104981e040c07440604d621014145000352804c0e035102680e81e0325401070008411940c030f040e900d0780b040541100c00160660001c1c1c442c0980d440c40440002e03110136413201c01810711340c5006442074040710388242c40582d101004108645407103141c01d000300b181c00c1c00c03102140c4a00c40e400021400d2200040e90f075840e03400c01042d92035546840840380c0c0185001e641302c021055804080800d0340c1c0e503904050300345c000032a03a0004c2c0c800698000103080d00c0d00a0a05040408580d080c4800d03813651303004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 240693732 1250 240692482 240692497
    0x709030f080f07061404050c0108090c24031609091a060a02010e0601061d041506050a02010f05070e030d0809030d0b0307030615150504080303040b090a3003050c 71
    0x1d00d00d072281d1210150001c07501c5802c0d0010115440c101d4160a002034032402c1c0c5004a002d0030880320105008401540c40140685041030158800c42707204a4070719154074102c000282548071401550a4810300380c1c141d0300299003410316042c010001041c29584170022030001c00c8600424809405043c003e050100d030b46610950084500180000445000b50030504002103400120360403903035100c400800301d0380c100d46841a800b0401e0114210b9240c0b60103200100c2010818148220f45860300130b440a0f88100301c0002955200c0803145448007491007124840c0740345440700100801513204150a00040305210350030b00007164144403646800005580458010090008580801c02d00080c5054103c0e1b000074802c0b420000415001c9440000c0ae204803440034541400760410312805880d140514041c800c466402400040e02003803980d0b894581003400b4030140c2c1c4444125480d2100640100c0c82c99988841000292410084101d04159072000d401c1c503003002907050051000406101d40d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 240694982 1250 240693732 240693743
    0x90e0d02210307141201091b02010e070b091801090b0f040203100e0702070308181008010b09010e060903011a0f1009050909031201030c0e0109180b0a060b0a0203040e0709030f 77
    0x1001c40d2602e0010008845c0c540f815281c075242c182d80e41d40c1d070308005090020f02403180f5000c020f02805c402801400b80d0b00030341400e2009019100e043c16041c203101d4000210031940124a045905020f002004005001c0e2a0903d070201c0d0310648082440404440995018000d9104100b045035030440801c144e0f05071950300100d1140b94440c10030491810003582c201400c0d1b0280000c2e507070303408079910003410007824042d1030714a1040c040c00e07420340c8c0503602489609000c100030001880950700c501074104003004020445803c04e034500000c242111201c5021051206142040480c00d01e04000c001a00f000c086440d842c00980700400188903144500c101ca008890400200d055544180309035010395018000ca11007a41e96403c014048082c248201010701c00100004940d02c00c042c011916040400c000180c24000c9554402c0000741d80103089860b04c0d03580d48030108180c4070110052801c00e072268002d54840e42403100401c003203500500340500384641c60104000142081004039401500503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 240696232 1250 240694982 240694997
    0xa05270d030f02282301020a0809120c120304030504090f020a0306240809010f090308010e0901020405010516020a09180c050d05060c0a090e0a061805060a1806090e0d02210307 77
    0x302521700082514070007071465540041150084254080d12040c81200c44804032035024400016018807071050410694054211401d4520002084001140c00c1442031034514038180d60b0302d149500300c8640c040c83c0408540c0001e0341c0142254180555009003010000007410031154090b01d2040254029800c0d05006131140018a040e60a50180e180c2415580c4103000318502440c00400c241800d020380710300038502c17001091042905200b40c5040d00c50607194189443c11101030109034034100f000c2240c5c0a6441e0a001c00c00300c0290181021075203100d805002c04050502d032600c828001e0342c00050003100350b948003401003000000c220341c220b42101d59003075540c0b02e907600c101c40d982d145401403680c0011743d00910000b4085588108100c8988904800300c1c2181400c03014144e0b0000c0d50f50a41c043c019000a0141e1a4443d0310540002c1034801d002600b1a9220102c506441d0015141d8655410102c4414051a01172000c602c415940c4901d03407a1850607a0102c07540c0340000b614810401218 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 240697482 1250 240696232 240696263
    0x20c0a0b09100e0a0e091501030507050108041407060e0f010201020c0307032d02060402010e0d0203060a05090313080102040f050a06230c060411030705060a05270d030f0228 76
    0x2924542c000400040d10350b64015171144000c10b0302d000242d544034218441e40312900300d00410780e500c50f81a05c0d8002c015203125413800b001103e0b5000094015501c6290848054007151420803012004290546030082d1421b01c00c0704101400e645851454156401000743e01d00d03008010007103c110307035030508002c6410b041ca40ea80300e6940c2c2c0c0418400102240081c03013013143d503800103103c5220754800d0340c1d00b643d08407a44d02840110f0710a03400082d05544440045807030400c85400055000b4045001c40c0d05101d0780c16a01c40c0e403a0f1035030307006030a16540014180280b070900604480901801c3c1d449038162803901c28004e04100400c1800180d000070907070103118110800f030807a001e03c01613400b100d80e20b050a04020341e8261064405503c039100f0280d000900b8108403083d01e40303c7c1c810751616420300700c1410100e4189666121003580d40255801d42200556480d0000c1d880c243c080d56038800503d001003c0a0300c0c0520141503920020707000c8000d600888207462900c65025401001582d103d0031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 240698732 1250 240697482 240697487
    0x3010905101a030a05060a0506060f090103050a020d060f081002040807140307030206071112010b0f0f0d0b040b0412140a050a0306170a0218270a06020a0906020c0a0b0910 75
    0x8002c0d80460b40350050920b280207001c2c001030f2a9001e00c5c0d10020411081c1c46000410400c3d1141d080d156240c5041404440c5d074645c060f900030390f440700700c05c080545092001f0b00b04508692407034014025480780500140f10207401001042c0300c200080b80e0440c40c150901c0e464a0760343c1103030700c40c8011a01d0189001070300398030705001c4d07100155405082d10740c48800524002a254038038610b001d0140518940c018111038050240c41880031001d4040f620054030702047c4034040e80918241a006250300f071030400002c0c10000d00c14451800303120743c0107142c101b601d010180d1045403515041003005041c0c004600c20110b1023101c0180c0c525040255a070342502d04240c0c081d03c82c41c2d10218044641060341441c80d00003207242500a803003145d4400d2404482c1081441c41403098900072407998880540460341c81d030300800100341c0410901150441702c281c0d038540d400d03644041082d0b000aa2060010400c454042050078600c1c0e50031503590807003d0901e00c02001ca401694025889080800203200c0000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 240699982 1250 240698732 240698771
    0x909010603120305180c010e010c11130e150408030a02032211130525021e07050f24090406050d050a03200c0609010e1215060301090510 60
    0x10350100100504454001002d802400c045485c0c0704000032140d81415902c5000c6800480302074140c4800442d9070004004480035035440c5800c458100240340805074594645035404c650030380b4450046030314004507150718101300e43d00d100c000502540c1418840003818500079254045500440140c83e0b6841c01c04a0b0b0031079030f40030003084481201c03091030341c2401040d0b42107680c0c1c103074242c40120035544c00c410346408448088512108151a030200c003001125404800b9984914610494200c204101c0422060310001c02091040707a1010350b00f04814242188220140442202d140c0744031106818210102010281c070811403280c001440341e156030701e991040e005080c0c05441a00b481002d46480341d40d494100f4400c0d0007007202d080c105401500000040016542100c0292213401011414030110b41c20080550381480304c0044401459103801101485101c0300030004d0451490003615851001070190507507001c4e9042c1200100860000102c01031090300140e000600e140041481d2004031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 240701232 1250 240699982 240699989
    0x6020606060d1d100615090b160210080402090c0307080a0510120305040801050609060109140a0e0f150102010c17090a0f08032401090909060e030a12150609030209090106 75
    0x3c43e451140c95800c0c040c00900308103a058482020004c09849560390050481c035284d90300001400b030f19090180c024004c001d01143c0d10300b041112000300c100d6000461100b0750742c0000000034503e0003008107501e80740b05095080501c80400610b50708211034024581c0000038040d0314040d4880021417070007a640c1408074001c1c500504e150008c0244d514000308940c2c018071840704070398203100c045405c40c40c069480707070b005140503120101218503204000303131040c040da01e031141d0050200c1c10000340d01c90605482c0d441a40348989001840c40c0100721810034001c0107a22604580c0740401c0e404111750001040039a134034000540701e15664a0003849858000c00c000c00501170011a02600100140302020710b00512408800110748809001c154104000d204c50090001e030380301c1381c1040300d540590b00010100d8015640030030368010f0303440141d00e15400007031a80d00241d01c12862050a007030a00ca0900044080c24000003154540751b4000c3c0040180d0001a1213004000080b980c2e600c1e0960088004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 240702482 1250 240701232 240701261
    0xc0324090106050a08090c03061305150a06061b0c050d060908070f200918250503010606050708040b09030a0b0a0b0108090a1a0702071a07020a0503030406020606060d 73
    0xd0340c2c54000c0108103802c02d007034100100398444003150000c0c001084403451140c2c0500100701c00d52711203403e4001c040d25644191024003c06040504030008200064400d01d0419400300740917180000003003503010101c08407542c555110301c04a0010301e03140c2d180700c11580e04030348045005002d42001c034000c0280c041d00510240001801d0340411400882183c0c0c01d5014010088101209a0080042e44602920fa607440b4440b00d000640d07003200e2102000081c807102045818260075440c9981042ca10410b92080031034071030800b00260304d0240a8070010741194540f01e0b081001554034440f01d4040c2d070003003040d00c00c00070401040701c2c1c0b010050107101e13a40151aa6055091120900c0010291000c90900080000000072000c0400060486072164048424802c80c8010307150403418000c0582071508600400c2400180072070740c4044084c420703800c0081c960f6500c0d420301c10481038002c40d0307010350f004c0d1300b0a01c41003084c1a0007082d441d0f0300000c01d0390360aa841345c458401c1d400400c03010714040319 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 240703732 1250 240702482 240702499
    0x20106091406030105131e0309030221061003030509060a02010b06030c03150d0b0f0c04150306230a061d090103080c0c0427060e01060b030403030b01080c0324 70
    0xa1801c044020035000303080c164000c111a4807603840c10b5031a040f08500140c00714074000b01c65001898031031115100c981c02803512480e0584c4940c00901320552040d4080f03030507101c401850311031400a01401e130304416000b00200e0303038620f1035801030a1401044038151080f000442e100c0c0ca0b040c000e40004942040042c6440c0d500e250252113103550b40c005aa826824800080007030504d411b000d01c4166030b050300540d00e405c05503200c0c9091310300c002005143c01901c0d00c00340000140100b041040301d920b0901a180810024101018403031741203140b40c40036031002d4281d418a18030741c03100d401070002d0714004d203807070900d041d012003001100c0f0b01213240d0280c000100e4000041444650310181c05d52560070b105650310318045100f04415900c5d0f5618942c110940350081149a00700d8502d00d2160740d1007450042508000300001500b1980070307034851401070500004110805a0611403110b00f90b109081150032410403041e000f00703c1c04001c0011400d84000080c0c25408460010180e04901c0c2c000e210740c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 240704982 1250 240703732 240703751
    0x2120309040204080706080609060d082a030408011802012001020903030a030203040302160e01090903170708041203060b0307050306040917250203060a020a09120804050907080709030201050a02010609 88
    0xe031782c1c041d00c0c0704071800100755102003000f600e0058407090007460010101000d40740b49489855039688801d840030503207002d4022028807941d56140014a0030000701c081d649880c900300c40d407400c0d030f520303080c40e400064144003460340140e030880d1300b181196007030002880c00203000010a900910601d9619a4036220100d6040c2e1002d03415002148030324400d900b65502d00c20440d150410502d0540100d9a01c0f508260042c00034480304c0d170108044034000c1c80c0680e0381c03100301d1407500b0070448240c9480703000031342d01c5041009000210910042001c00351608202840c940b12000d0028040640340c107040040003c007156040d9215048115029000201001d681071030341a50041681b120250354450055000071300e001a8001c2805120543c0141c0a071400d9510080101c00940c40002c40d14144201904007003a1400c006c400780a11303920903085960ba032414102001103542004010000700003610381000203050388110b1200441c1e80c2820510b0f100d140c4040c083c1c0c0902a1a00000f44051400b00c695 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 240706232 1250 240704982 240704999
    0xd080c010f0b09091b03030909010b0a14030705070605150907180801060e0c0904020f0c0a0209061c030e061c061503090c0303110102070605150a090b0d02120309040204 74
    0x1840d1400c0d419030801c00d500c000c5083c0202c007a400c490310442e035002008a11000d4015018142c0050070060540e45003040c0000010406142a0084107822802040c10200c0b103403c43d103590003650100c44c8035030651801e154020302520540c00c0091010303440714042564076044d121112201c46000340220b2032490103500080566610300418000503880c04000120440107110b100b00740e450440030007525036500002030040d94003c03e00c80350440ea00300548114910080094201a00010094401c2100c18010003000c01e80141041e4428203c0c11908184011141c2c06201c40300da160070714000011190001900c0f42c022020403552094203107584080a04c040d9000b01e066600e4486107014018203610200c040750090100101700050b02c04c03092000c01d015215861180c10030740005460088190f54070f40a64005446116041d04218003507956882d00507c074030064901000c0c10010060b22800040f0010305011020303000b060508054081c15005000321140e0f080f000e801559116a12180c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 240707482 1250 240706232 240706241
    0x50f0d05090616120b0a0b071a06041a100309020603150310061a070f0807060504151e0209041407050702011409010f030f09050601140f0303041d04020d080c01 70
    0xa600d1030b402210001102a03411006a1440d07422030350343c60380c42c4110f440014005029000080e5031120243d0b500103100d0894000500156100781209044202007400c10901104013038100c5200c1c07810080b0f0500c4009400713003510100642190340c12030070909104107030010b2444280103500700d00000101312103e1100d50440e1a000c10660031070f078414440000c0c51080711802d010750560a0716181f04031295045c04000341400500a2a412a0303203406a6291031065100c004201d5400d82c0350300800007131140981c10100f054404900600c9003500e50090700807001c141000f00311005a001c82c0f10031b403076102c580c40640071900002840c04541403a040181c04c0340c2001c0f60407400521040034034141c440b0040305444080030306841e240005d195050007038000c1c16100d40355580750390b654052072010420800c003941c02040300e03c45005410302030109008880031440a0907000381d2003000200320f1844a000b124810102190503071a041d00c5500c0051318046105d10040d003046000b19107180c0320394041d4071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 240708732 1250 240707482 240707491
    0x3020313020a0e100506031005040b420a0c12120906020409180f0f062712020102042102030705030a11030618190501060f03060b030c0a1212050f0d05 66
    0x42c4a02c4c0d81e078036410401a0b210885040480700e2038104200001d05268000c100b03034100081060b00b00a8111025001004218100f40d0b4010b4401028699801381902d102145000e060b80c00d03460074200b69000b500d8044090b4000f4811010300130f04641c1c15100d0000d01d00000ca04071014043c844d0740d802d14802079040b600800324603a1074824100900d480d00005102000d0340700511108000c101d4a9003025a9500c0b171042e40c8298031502207000701c80c288200d005400d800d0f24464024280241480754801c54064401c2c5d0540e03204010900241c0c0c0c0001801c0842008098000b40910340380c0302280c14021a0750106806100d031803481002c03c100c1d101560710f03802d02038003200c0d010b907126000303021544804850840d071078002c0318039034071200101075030048424080c80010460542e50488088170304210b60041d01d02d03a540c2e540e449454941442241c0b202081200d44002c0c082c105009550b0f4009440340c024003482162b8207c13403807680900c054031885210458929111035142080c2170103400d04a0f0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 240709982 1250 240708732 240708751
    0x12050309030a2106030813050a030506040311010b120d0f0302030108070902181824090a1a120a02130e0c01050c07150507060c03200903010b0d0f03120506060a03020313020a0e 77
    0x201f0200700342c00c1c405500f42c2182c1c0c0010041c41592520b480a650007000004000315035500c4034100d0f4001e4442c000d40075581c90007040200018050500024070540c0011540b00405004000401c9034440010350740d02540e51040c401a40c0319240443d00c101d11010002e841d80021146008038858035104800341d118000001c5000755484001030a03060030312861240c240d100340e030280420301c0c034a019840031502100d900212005410803000281010881442074126580070000140071814142140c030040300090030b05000076100480701e6a1503203060f0b10740c14100000492080c1c2c2440040103140700600341200d00b65100e11803004024141d0b40104020782d01d044c200000502101d110f4442c41c0350401c807030b001007030403241d50100398400c0d80d01402d51640c2c1592107400113800d540d40c07101096030f85440303110418001441881d014180061701402102981d1400e02007000c41c1d2605000c60340740d54450700d801a0740303640d60b4100d20344808402d040650008140640420420003030a0428046d06081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 240711232 1250 240709982 240710017
    0x172b02060c0c060403030c212c070626010e0105100e030c01030b180901020d050708223e0d030c060f0b03160312050309030a21060308 59
    0x7103141c6002403007030ba520315100e68018000100428030a6109440a469614001102004d04000940d80c2c084403003ca8500380d55400e102c0c11144078140c4031000b441c40004036007a2400c909503106403180440c4c494603040c40b0402d1441d4528a00501d450190104000d00c40c010958481480c0c110442c0e003405100d018000380840c140016000e004800d40d1401e00400900300c1c3c1018000460142c240c401001c1d400c54412040a16100020650340d0300c108101d20005031528405d002620660364040c01c0c40c0c0900040c07005100c2e004568130344440d841d200e0010820380718560340c41c110800300c0344034017518480d01001e4058410701c03000911086840c3d010314545481194000d0030001c01135140c031802000316010301c00c02000207180790407100b4401050300002030406011804030341480415010b5805c034800d404424410048c81c00035040c0905e070715141003400c520b441c8826569a10032041c940080c0701e13115102c4408034003511008205510040002c1c44802c1d601d1500000c50b801090b4010700e02c9294 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 240712482 1250 240711232 240711241
    0x6050603100203091c020f0102160b15010f111501060c0303060803040f050d060902060f1c0203010e0a0207051f06090e010e031b10061202040b04090309172b0206 71
    0x58001d0700e0081440c500a0030140b00d44920f540305c0502c3da4081e68056000300b03e40a444402c1c284090031000122021003240360301b880c5458052007200a28880b028244130304a0f400e04d0742d006c503020f60341c0c42c1e250822003c45904a010989008040300307100c00070980d034030000315080341d202c150520118403a48091104903226034006447c1d000c0c1c0e0143c10340362150704004002e18035100d142e401c03034079000d164001200d0003281c011a030541d000d902865114500040d08980300d020b1440801110502c0d01021821035050000b40e0410200c05071403900680d4004c40c00e1418808140900b5860024083c001c0074403041c0b0341718010191415100e07031002c00b4540f02142c42c588a06000d035000c0c0c0101a400341d40f500050850880c0680c1107510440c0c040e11070041c0700c10b01085d45105100c054140f146800b04615a41d10401041c0c883c121201c83c02503003413a120400081d04800302d20103031201e6041160543c500003003410310b403101e42c1010300c2000d03440f2031981550a910040e07100b04145546e0968040b40d64 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 240713732 1250 240712482 240712513
    0xb0a030b030118020916110d05190201060b030a022208100b041103011e0801060f030c0506090d020f010c05150403031404050a060c0c05030a0909151a18090406050603 73
    0x80188000e074005c080034000035401c0c0c1c0400014040034016081003030601c40c920644c2c81c0b074514a20300d100080f5a0025446c0d009003180840f48080308850f2000340901d40c188144c01d8641d0001800150001d03402045204c100000c150301080c022a1013221168025914007080e9910452000d5030440c0368038150912003d41001d024031180341994407040d910316468a4820700b41d0340743c000c1e900044d030f01c905a4046401482030003500000e0010300603854204e0f0441c200b440c1220200e90101d44101020404100c90b1f880d1035000030320043c0c04542c1d01c0302198841006039042020b03c40c000f042800303241080540d8818000c009030099000781c0d41080b44504200c800c1d920138a06a0b00540315074401801080002c0e110f4000ea0712031400c2d840c09110042c520b90750b01e0b25681201448001044140f40306000f40b01c20351150403103c080c540802705032071b450958407803403105480b20403070040c20b000245043c6c4809021410f030480c94003c2c00a481c580750504000004084c00c0d1100742c0709005e41e00c402403e084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 240714982 1250 240713732 240713771
    0x6030308090a0b01051207032102010614030616050c010c03090c0905010b03040807060b10021506041104050d02040b15130909020f0f01180602010b0f0301021303080307090b0a030b0301 81
    0x560026008050b81d00f0b1901b004000030b0030092000301d03031158002c0440041c95031802e0040c50440300b282811340280c1520081c1c25251a03812540107640e03c650b00382ca15660009209400c840218614841c032224580b00310790602c910302c0c000c515503003031815840105070b155204010550154450810382034076074a24006841c1c083c42584e24002090000ca004964414000c2419910a00c400210281d0396400308494507202410400541c02c1a107146840d06c820200c140e0744031b9400c503010003407141c14602c6080b03240079034000c0a0003080c031441c048045403075981c000300d01b01c04003c181d03481d203601d819914025036103c04844001400d00d0100000c800c2024003500108036401440e000c0203005100c20b0040c0c0342d180f21800d9041040b118031400d0959200030859018000d507900100b418070110041c0641280b4980101c0d00a078410012076014040072801e0b04140c1c0c0d4040c00e4a03550340c960420450b5119a00d401c101a0243c0008005c0340d0160190b002c66038020003a002400425501c1d0000680d42 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 240716232 1250 240714982 240715003
    0xa0201140c04260601170f0105060a120c0801091407060207030f11010201140a0b030106050a18050603031308010504171204080d020d0f0603020312070c0603020a210603030809 77
    0x6000c2032009001c4001910740410403420103400100f481001d41c00c881d89014800ea200420310f0405d26100c10380880180071650704401c40c0320092110b820000045100c4c0d0840348500d2841c541c80d030b480384040003580c00c01700006003174840080c4041103c508200f01c01301c0d04101e4426035449040c2c000240c0c07d0000c150300782100e400c410084d4122005d03881e00c407101c1c41e442c0b290034115540e550b40204070b82c038641162401189804400164102528181800c4600da50082031041c001c8032000c11004c01840c80343d000c0c41c410300360086400c0c1c90b4403000c00c0c0303180903101c03420a040688020110748402c05600039403203540580c000907148851a4042d030060b110381e04444140c0c40e000000680880c108100901340b04041801c0189001d181032004011100d0011052040c40d071078000410a6113070410841e02861041e4a1407860408035640b540c6002d907880c070504050640224508040600480141c0c44466046405074400100640f03030100524040c0400c80201d80107101017401c020001030418482c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 240717482 1250 240716232 240716251
    0x12070f0e040207020a26010b0a030b1807050a0303110d050408030912070b0403060f11190c030e10022a0f0d02060f07080307120b0d02010c02010908030c030a020114 72
    0xc09055003440080d5128076002d981090b1980000919140c1d001035400d0380558868000c4030301e100d01c121090030f5950741103950b0700c104510202030000c9481074080b80d0b044a1030311041869050b410000604040c0164815680702d81d210500000313158201184032190980881a5032001e010820261040d004030701411003507030b009100e20051814881c0800d100e130200308040360b504c40d5843d0010400c40c0d005d0b42044540f5604c524a0f0407401c41c080c040c2002985200924500385021038403454103491010348050304100f6080d0305d260505001d0070f01550071400107030102043d0340d50f0010280d9562101104084804a01882c045091681503041140280000d201c003010069031010003a50300301c0d210080c6d030b01400800c0159104a1080000c1901510840e9070507168030b4600e03005044504c41d100c9c0040e55906200140010f030f900c01d41005c0101c1e50900700245040d10500040300d40c07015a800600207480000b07041e00e2402d00020140001000c603500074051010070000701804418141c446444 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 240718732 1250 240717482 240717497
    0x13092406061d10120527010504020114030c040312050a081b0307140c0706090f0e100e0405010209040e07050f040207080f0a020a0b16090902030405071e03140312070f 73
    0xb03240c00c0d00c650404000601d040d8191303405103442c3e07030221002a6540782100c0404400c0d4084024013a60a03071008205400820082c5010380001c0c142c05110080d6a0354440c0010003c1c00c0b10076440241d07005560045840401c180c11010048d01f154090041c14000c60222400104095091420041e20b078011600c4035066440f640390aa5481c44000703212200104141300d22000c5c07841c2000050b005062565079408501d151200405c01000507402280020649004000707104408015600c200c0d03404240042003951503042080c024010351080d80d07401400d1070208002c0200c0014100700b0307920704480c0c0c8036600c10040200000c0380b09219000301803134002e1083c16142e4600741c2c0903001c158024015140105000e070759100f0401c0d01121300c420310600900300d540405a2100c10b607009420111002c51960900307480712540d51403240b281c64200380d141c070351100300ca0002c1e406010003035a10008060b4102680c811058a0ba0403210040071541e000d1000100c08503c140c01445c003074011a00c0d5000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 240719982 1250 240718732 240718787
    0x1151406090d0b0604060b0f04090b06040f0612060b191d010206010e0c090603011d1605071101051b010203010509130b04030e06070b0a020a02070e06010e1309240606 73
    0x40e03001c4001040e96174801d645003000151400450020241d0403125420310340c0e5039003090300302c00c00c450b1840354181c00789074140f0081c49a40d031000c5002c802e5861381c2c03c0110282c42880c2d900c90140120303410074000e200c0c0129001c4000c0b00b2030422400c001400351940d805116001c252806c501110010150059116100410081c04049007003a0414007030b010349032508040b40041090f660084c2d0100072802004490b00600e00709400c26240c110704a0512901d00d5860120700070003500a490b8081c0c2814211115007030381c5e030f0050084461708040403a0568071b4511034440e080c001d4009126107030007800100001040000f5a001e10146141e10002c91a42910740c2c1e00d04607481507100f085a03410580c104000340101300014841d0744101420500541e03076001d0140d0003410030400d68403140315051850180034591303070466500d20141c0070a91b0010364076160b4074204c1000c0d1a64041c0504600101e100260f41e800541c01c0081800b400b0850601c6101d59940d4222940d02c881030005181c000c01c0030051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 240721232 1250 240719982 240719993
    0x807021614040e0d0c0c05060708040306054b04080f0706020c011b1b1e03020a0c03051e06070203040909020d02032b0302030c03070c050f01151406090d 67
    0x120601c0d005400040d0914410100500d0f00d80c8514048010403289800213003001030540b980000381505860050418220f40d40307000540c0228000244030546880c0040d40300c0080c2207011031070307481001c0d04584200454040800c014140c4910704243d04009415401d180008600c0e94010741d480607245280c0210a42c046c1000d80082004446090702001f04420500f000d0256108000c1e060415131302140c40494040e141c50042d2400c0e00f4550300308224100807611001d00313541d00c950f20a2450380032481c1803800f03d0070091a4280100459a40400030090040014002140992422000010100f88078a1540e124030071541100140e20030017040c0b09503003d030340103042c00a1024044013180d80f8154006424060914000030140d20443c207026140008451004030b03001c55400e0452450403e02100d0b0f40e144002400c0f481070003116401001001020404000413045000003040320000761510800b000b0500c2c4207503a09121047c005070103a14189007207a014100c0100070b12091001e07603030f81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 240722482 1250 240721232 240721259
    0x4060b072402130e0117060114060c060c09010315030510110f0a08070e01030b010c0b07021c0c380a02190206060901090c02030f0c010b040c030b0108070216 69
    0x1400d600030100300d09100e07804414009010704038000034501e4a4541048040340440e03505910462000c0079030100310329805008104241503900d5488001c21143c18103011a0a900c25502c0500180c8503203410488000c10310320291407004800d980c10f00081c008008124401d0f41c10340800741058100c0000c1480c410450b0340302e207a02c00d0002c01c0007801c1c00c0c0007010905040d00170540800c0414291000c10140580c854480c540502c0c00342005c014450103c400204800c482c030f6802000003c0410100340428001c120b030400b0308001082c0d10111611842006104034400c0b2404c4981d04440e800005841104a6110343c0c4010712980740401074482d4246d0318961032014141880d80c50382044014254480c3e245803c0581101d40c00030016818158240045550164040e85409103080b8001e1015540803040710a84010980c480b6225040e829030700e8010200034402daa44039207040034142d58036801d60008064032000b62184500b681e0b5030802680c46c1c2e103900303842d14000078840c50700f4040c01100000703 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 240723732 1250 240722482 240722513
    0xf03060504110307171012110303130608100b0a050d0b030f070608010506030405060105130b0409030804060e060106020d181a030402030601140315070c15020a020c04060b07 76
    0x1408241256103001050440303110400b00714140700004200250325401c51011040c000c441c014068003460326000c1c200300b20600f40160409a64400200700070310a00800c580007502d001810b0fa540c2d5408440401000340301c910451307010a1008001895440d1000340d1038080340e0122203914a880892402200c0540c8040b0701140310f02d94420f42080359460400048400711256001803030510b080c02c4014006140503401944100c104100701300000308049003007411290192514420741e9001500000904040040303076400524022401060580c0030030440d000e103008003401c000540c049400342d6101c8100f4041c001c0580c6c007a0310794850b0107202c0c0143d40380980d04040e80010719030300c90420000f5006101d042c0803c07110301109200c15483c0500207140144000c4040c036050040c10000700e6240d40904200c5040d03a005640054251070245402d99a49584800070a10456002c4110002908401031440051240c01e99003c000d040c28841c04065515000c1d5580c00c1061590f92511142042003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 240724982 1250 240723732 240723737
    0x9010903062d060603110c0a021c050f1b030c0141040f0609140603041118040b0106030903080f0c0c0a0f03030507031a0f0102010204080f030c0601050f030d0f 70
    0x16190a02c5200c5a00020441001c0746004600180b421200605441850300d624103000c0f401c204207403c0010000c2e200c15981c1d41502c01c00c0065007441354500c0d044031036032405050341c00340600300004040c01082c000c00c00704024088582d2000c604050580d46c41c01e03c200c0c14082641e0080403801c1e80001005601c02103400741c1155009011020b514407050f003013424240c3d03000c0000c142444a01c1138650550050201440e00204680c60004030141030000310030900d00402001012806101500111a43c042d0014001034540001e14040344550728080f81d040e1042d00038440081980d80c402d0003500e00490309580e03178441a0301e405172014001c080207401030842410400103102044000e000400c05503018030903007a4000c54505001d000d8410040c0404205494210511441220001c1d100180f0405854006040381d4502c01030380244102d800030780c0705201d03401580120031400401007080c40300c074100b40c42c8a0f0341e880003481403034017800034480e51541001e041523541d2032091520044008461 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 240726232 1250 240724982 240725021
    0x1503060f120b0f040206090a1e080a0b150d1a07320f09030601030c03030f080105060301090e2107051b01080612012019090f1e030803011413020901090306 68
    0x10030000b80070381420783c00140d24645481940c01d04e03802d800c501c9000ac00c4400302034499840f555607180207070030008014020040403040613101c01e460310500341d0b044c503500030217044050f040f1400303c1404a00444501c40001d882010703490304003150b143e100c03406032b070301c4454085192000603500e01c25800210f440c2050003818041ca46041d9803c01c6810300850040700f045c45c109085090040058450300102c1c801e0055440040000d0340750b150840341151140940000c1908000680a082211000c50801039400810f245070702c4010400083c609984900f00300d0345a64410115803c2ca10f00c0c1d0b444290218407030034005500c81c105103030070604800001000254040021015140f0b0903001060b41d0030040c0041854803160442d480d2241e40e1171641d042c1a004e0518000030340b0f1035000382e4080d015a0701488100d01084103120011040030719405a101ca40342e40e11510200b6203201000e00240c03007034051809030034141800d0310840d445007806079581c00c2090304503280c0034068071065140c1003507600c02 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 240727482 1250 240726232 240726247
    0x1a1206041b0f0e0a09021c02030f040f06020c01110408070501110c1c0605040f0227010b0d02090a03050a210512040f0204050403080a060b091f03061503060f120b0f040206 75
    0x4070300304c1c200641120400146c440c249005148081105000581c0a15104209002811581041c059480b6922600c1e1000c0d14000c1c2c900320000c3d01982000c41015030a004016560340c1c3d0000c041c2c02030380c0d0031000321048517581c0c800448025400103c4102641c100ca0704101242c1411411103405850060040600380202d68860302211402c640a03640b042e0420441d4085180071150240041903640707000622085848105818900602c9405500480020045086c020540540d039401308014594003146659040854a0340e0321050111401e1303100c01d43d100f08580b550322014901c80f2842e520b180c00c001802c00200b1801102500c259240b800784046100140d6850003840d102d1840780d0b885034030a003082d56203101a5100c1c0c0e044441034090a000690b00c3e510703005121183c15200c8958180c00f85a82e0707005600821203a007000c411000318024004406401d600318030110380b01004980244c540d181214000203901c510018100f00404010170f0024a480c3c1010b034102d800205032501d803058 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 240728732 1250 240727482 240727489
    0x180111060a051f0509191d03090a0602010501061b020a0e1305060105060c0a0605041e08030103030e0102160509151e04060806070206040f03091a1206041b0f0e 70
    0x407500952110748410400c20108200380c4425032403208014150422030801000900842005002c200c0513a13600302425030800454009280ca1000c030124000303422808490725450384e004100042c054042c150300052028414402d540c100d440d56900c64092198070b0f100c071090340c80c82040c00c0e44d2000700240f000c1640740c030b000011030080d00c441000807003001d5545822414000c05902c1203110f0b600600080503a00b01c003003200d40e10079a212100056540d40c501c0c1252403202d03204403802030340502c81c140c04100680500114162406500d4011801c1651001243d450311001f5940001488641c070404c202e040c003d8802e50000c17400c51311711400d003400c503020a0180b100d01808007030100141100d20340c3e90416205401c0078085c004d001d4100c80c0392080010b03540d10400307000105001058600380b414180b01d20b0340300014007941800300140d110740440800b09078111401070300d80d416800c0c02045581c0b4003442050008400c240c031841558034000000d881c01003012521005000c0d0000d030404440d078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 240729982 1250 240728732 240728743
    0x303020f0f0a0e010c050c011116060806090a0917071103010c0e01171506030c120a091406310609060f0501120f060506010c080a0806031011180111 65
    0x2269000015120252998010103901e036507070f03038a41403201e91000f200206001040d101c1000c1c00a003000c00e900140b03615441d1410b24103032500013200c4c039902404034100b68040005030040c83c04407400c00300e40e21441c00260403544082e00c01000d508400051500d108a00005409040d003d10007803074610807144040303801d43d810011000001805c03502c83d40c0966030403400810740324607800d0410302e8a103482c415880765900061003051203010080005a40e030140d5108807000b81118811588139400d000d44c407180a031424403011907660b2050240740d00728100002d101c9204900183c8507001c8140d0f4290785015458001e007541885540c21803051000c28103902070200ca092003a00c00203040d00d84502104203c0314180c021b04000301820b420200840c0051403003020b181d800c4180068141c442100584078030303082500c014500d20b80801c00550b180d400407446c5108003020b505540580a0301310305101111a196075904071020248080e2101c02e003c06801c0c14600d030107041c11889091702030406032400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 240731232 1250 240729982 240729997
    0xb031f0815010e0114030a08070c03081b07090b01050306010f02240a05090715050d0618290117090703050303040c061e080112020d0b011203020f280303020f 69
    0x1c100c0600100002035a000364140140a040100700c0c01c0800900026150b550f42c6201900b0301c000460003170b05000f00ca00350a40150b030700814580e561034014801c5281d809005950f040746016104000940c14694003c03190703038040c16511203186a48d602d0040d5804030a4000c01c2c0118402c41c00d505441c0c184204040040c4d90550fa6191402e14011020500307503900106810313000c0d00003030400c00158040072070120305140300b070803c19140e0052503143d1000f01041c0d8044201c542401d100c0707040b5600079034821903081e540c1d1441440380c50403100c01c041c004110107070400e00103121400803a003c0040b00361b046801080312410b454103955641c803030514507041500e05131440102e540c0d0811031a50003800b181c03060440c042901d101c0341d240303010140140030148614503400c60130b038102004640d03c01e04055440c070703400b0101040f88e50b1580440e85090401c81000c0300584111080c9064110700007944400a40310120455000055050141401842c49100301c050540a0000d030b03445000c2d0001070141c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 240732482 1250 240731232 240731263
    0x1120e01020f1b0f0a03050a030e0105100801053402070b0a180e090604080a110a030e01030b01030209030615060c0a0b04150c090603050702190b010302010e0a0b031f08 74
    0x46101c8180408840101404000b01c02d60111320b14001414011820405168050808940390940c40340154040c03c9101442c2d0311035480c1000b0000c000c03842a4852054800400007040a940d4145c40e40c01d8001442000ca00500c0da0183d203207000701d500341c1441040b00044e1054a031165654001086550010b00018022412001004441812019104000304041840c00c402805c0c646904c0e41c441501038800b41ca010b00018101501c03e0041486030b400940f0b940444044410a09004048007003050002e80040d041071000151588130380241c03240400c009001d098261110781c801403080300d60141458003c04244403900300300e60706002440d05039018100b0384030145407a280400401061501c10b051540c90802281c1e28143e0114400060741c074141030000d00c07911007000c00c0e0b1800b4400400030090452080d5900100240c25101d03a049030305c00e80300c0e5884071062404024040c1c102d4064000c941d0001d10016080c0c0ca9803a40c05059545103d0300c6110382c5488002d650700300325082840307020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 240733732 1250 240732482 240732487
    0x100e01060e1801141312090b0a080108070f0302010e0607060902060408010207020405010909080a0f0504180e0106090e030a03020307120e010b0310061508061906021b0d0c0501120e01020f 82
    0x5907001c0a011310100c4204501842009103004610780010f0720003d44040c0400c009058104c490034000d00640025242070303000301d0b881c2d030060314001344401424010000f00e80114070b00007450b00191082d0a081d00ea0585405d91840d00c01e009104441c0c01c110410f4403410b494503045805a01c4617170080024202e00300c00035a031130520340144016200c041c0d10403412a8904941c00010600303400594041c0c0c100b5282c44440c070034443c18112203500903034101c003081c52410034414100030707841d40c080d454440e91a4000d1107010368541d50182210b01c00c6642c0302c1c5a41007040030f10402403080d030003103030300c60f5041c1000c14451240d05806011250b88280c0300c041607542e02a803c80780e141c10040302c109298110403e0000c81c0c00c2000e06000c51120f00c041900b03016101d40414801e594040c2d480101c607008005145070281d480780020750f114064a0102e000000d10f803580106801c2c640c0f8040303001500002e101d1800e41c9400c0c01100c028071141701da1783c0301d26501c3d148890444002e000138105d95000801158 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 240734982 1250 240733732 240733771
    0x9010602030c071a030f1008010216020901050f10112d10060f060c0314030f011d040b06061c1b1413030b0403020f0604050a03110f100e01060e 63
    0x1031900e4015040031030005a13a4000d1160f841401040302ea000199207021841e980340c1d250104200003031500010f115500200e05403820181104420360700030b0003104d00041c1c0740d0340c65003802032a510341c80c5501d4004000d02c0c6004440d60080b0559415404650100d4410320340c0580440070040c201c1c4503d42d50001c650131401c4001808000080c01c0d007900903003c0112a20300440e59842039503504c15034007889809034001d0107050280464903400c003c885130403562480c1c50b0310580304c001d17002d028142400e1030b40c2504810b26407030030041520541c1d006aa40b11291101c0c020054550030006059103103100c01c8080410180e071a011f0480350540392220700041c036400000281ca00b0125540f0180c0d00c1d18180003925490f4140d040c10360031a84c01c041e0603003040d140d03420120b043c0391211f072106103148500c0d800d00c42088000922002418081d40d201040c404042150b207480d1b00d0144039085159000000e02c1c5040c1e00385522101c030500c07040d0000600a270380d0385807124607500211803441028000101d0f00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 240736232 1250 240734982 240735007
    0x302030403170a02150a020d020f07140d05031f05061c051e011404060509010b03160503070f0f0216080f01060e010b07111c0b04030909050613090606050901060203 72
    0xd0b0034103200859894280740349010002d503110350040b400701d181402d00000c82c0070148a503045641c0348442c0001503581c0c01c3d8640032840076520001c2c040726200005e1104040401d4081141c0071200c50302e507142031071034413038032108482e031801a45124540999204000f0303259039010300512200c2e001141807604000d1a848090482d100240030117131501c002aa00481d841140710904e040d6820103028a103120702d83c0c0300ac24018030141e001140c2150700040003180703001899000c0e600c59000b410008408801c9130030100d07444d000c250b4007100410f05001451581b107000c0c600005c81caa0180c812030310001c804201d1488240741c154400791baa90452a2482d988003801e0180d0b001410b04c503101805254901404c0c0300b010303c950715028007120384546507448242c0ea41c1c10b010703032043c41c111404560302c2e81e181081807500b41e05807403c4000c20a800000940b480860151610840d002459089152400c04400303003e80510136040303410f50f0381c507840452680d4442000d02d002c2e0003180e005544410512020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 240737482 1250 240736232 240736253
    0x1140105030607140310120b04111c02090915011712041a03070c0f0b010501120903120c02071a03040c0f0b04030305090d020a0605270904020f030a0b040302030403 72
    0xe503009801810400c10456000100f0452007050001015035030360720118500001541500720740a442c1c8400d4402c814064080d812178000d40c020a946881400000704004501c5810360f42910400d10000440d4094a80100c405038892040c200707454055450000d0310803019030903003040d80d5a2040703210403042201e04205401d0f00d803106a00d202d2a1504014890b070303980700c009441c4040c0201c00000283c43c036102c0e6035610100d07540603800100e0007021345840d160060303090281c140010701c03124148144540d280104100320750103440342002c00c3e0743e030b801c00005480010003080561094030070000d00c0040180ca03600c0c2c6210300c008040d40301d040c41d240002c5074003169803100b1000c0074a0300e02401130300a09002c031400c40e541410b1580c1d40f00800f0021030742000408101a52001459600040c1130b900a00103141e0243e5000c54210103480d100541c1d40b104044030169034001c0b400100050050a00c01400e0300d001100800f00c1d40300701c0242d92410b0038140e00701d40440058101050810401550f28003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 240738732 1250 240737482 240737489
    0x70908010902060301090c0c320d080a0b06040b0c060f090703031b06091b031e052109030a0f020907090b0307030510181505220203040501021b011401 66
    0x34407802075036030005006400180200702c1001c0d03654142e01c1c0c51a0251400e20b8009520240e40700403010b040c00001030b8194031450041258007010400604000c003c290004190b02c00d40307401c0c080f0b46a90b000c407002071815000258000c1400c0002103041c40302000948001e80e0110300500d014949111000b0860401502c00300443e400550140000b035005448800c0507120b174902105490050b04100d4080d180061002d05080210030b480c2c3d2156003503d0442c001d0342d0181c030561000c070301141041c004050b800c04018005400050380d4410319410441d611083c00031960060382461400e00000c0c0c10144550011540241e8a00d0700303078114146480c9443c1d000c0714a0810184840c98000207441c00c0c40004e01040805070381e48005075000c03900c050200302a001c1d04108080f0413081000c088014001070610074030100c61040c000441d440c000000b000c1090307210300340c0c3c08901d114110a00207508041d004a9595400340580000d042e03c210f880f5101c40c00d82c20012030301c40c0300c0c65049050301320180c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 240739982 1250 240738732 240738749
    0x4080114040503030a0506031c1d190b0d270c050a030816050a0b13020a0f0501020a17160809180c03060d1106040617090a0c03060f0b0a030501050709 66
    0x700720128002000b40c83c1d2102d200340c004203a076669140040e081c09085851a00c01c000561a05048541d22290230302e40600c0401002a1541c0358404000c1071070022410322600c6060354100b403043c450260040d100b4102c1035003012480340c005440d0307411841d504019040300d180000ba029014880d00c0060840201815641c94591a0454031001000c1c070039241c5800c5000c00e100800c90410804000c060300707694120302d05841a00b007016050740074845034501070348200082007002c5140d0300901c0c05141103610580003800320480d40d650344242101000002c8881e04024009006410300e60b804003400240b1440c111a40c1c0e5441d1810855401c54041c00c05411036041e204100380141010700310b94112104440480c694025441c04840002404511a40001000c1000940705801180040f40c031010300404444540c0c51240701c5036240d45180c0e000d091040c89200800108440b42d0000c05840e64075a00494100c0d400f002159a26031660300849a50b9940c0041102c0747d548031500901500402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 240741232 1250 240739982 240740021
    0x3080c06010f06140906070209040302012003060f21030a08071d0d030e040b0303070807061b0207030305071a040f060b1005030a05060d021c06060509070804121211040801 75
    0x440000c184c88100200e11141040004440c0740513034400042d0b4481c0c0c0c1d0300800e40180da14027441c0090280c82164954040b080c1c1c1c11402350405940c04095a10440700500020b092030340000800107003110b4498034943c500c000c515050030090081c401400003d0071500da0b8107a904040000030807a0f10010b00c0380810301500307000000d0541d58010005e401070303018580002c4850003000024011316414a50552501c00010a80200007581c405040002d001e44e00403c041c0e82110b10103c5902e4a0040407001a04099800d0002030301400151500c03900550f0002d0303c4c0703ca14150a01150415038090311603c088410384000c101080c0a0304c00c0598080d00c0044000207030440180050101602e0402070588940000c0c1450300c3d0615403140c0a80c0041038078500488070702a510b0180c0c05220280c409505000c0007007070704d0a2104085d4040c05456403424800e43c1c50780c44550812031105110804c100304585451100c00041c0520011b00134004c140c0b683d21490103640608440a5160341d28005400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 240742482 1250 240741232 240741239
    0xd09120f0e10120f0605040608061b09010203030f0903120c0d0501060f05090d080d060e0a1415010507050a05030a02100f230c0904051006021b091605040302040603080c06010f 77
    0xb0f10191003521a180000c1004c400c2051600d0240c20150000380c2c0080c580340002403522030015460303000790340a603440350000301d04489501c1035103d240e1425002d43d00410114102100c007008007a40046800180c1781840c90554032004014002c1d111311080d624003181c54000c140a86c07203001d0052003603045c075034019068144094010700694003100d110b1410704c41d81105001e4a0300840e882020f8402c4100301c503039201c6007001a41b290665190b0f01071440e200c0428031031a030b4098218040c500070040c004500c1c150400448060788800e008807224010140048001201000a8100096240c0107007510410041c1076904884001413040e101c40d04122150204110f00c501b01060203141c04003582c415a140203030018a0b20031035801c103802074545010460000000c1c040b41055600035420303904029520150004c101c409800c886034084015808110381c9030301c21000c10900d000c80d042090a25030740b2b4000404656a541c01511071081c0010310055411090007410b006d00101e440319403101c0c3c01e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 240743732 1250 240742482 240742487
    0xd050d05090109120e0a0e010b0301031b05061602190e06030120031f0b041214012901031e0203040203010c08010305120901030b1905131a060d09120f0e10 68
    0x1405803c002d10144103442c00441c3c56280f1660047c3c2406018141e403940d403a031982c100d60380244402e440c0103100c17240c51030010700c1e052485030031540010825030401c40c2c074451113001548103640c00c9902c0302c03035066107501c0b065540840c1ca00400c101e41040c0c1c0c15241c604181800c0d10404250404420a24150b241e0020021001e4a40014503000840b580c82006032045011070040d070044100c00c000858009503071704400c015014003a11604241110000c50608182038030300140071620f80c80782840344c0b514060034030300310210301c42c405160204203002c600e41010398000e44e0b600740b00a056000410030055003006d0194114030240e034074020802d90b00d1a00d50f41d07103c50240c0615241c5089c0021060b071940e10a4005101d01c0000411006c9814104860000030289510a41d80201400070714403c1e900c03000c0c401c2600b01107000303440b18541d04e03800c000c00c413640d4464003a050410b561001000c01061200241040001050b220400d501421940c003601c880900c2403064410805501103084159 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 240744982 1250 240743732 240743753
    0x17070b0f0310360203010b1c1107150b010f14160c17010b030c0a05060913020c061b1305010c2a0501140f0405090a06080d050d05090109 60
    0x1408505161680c4805124400340c0c10154800200d8020200401d400d0030181c0f4055a40d01c1800d0340e541e403140b03d40c01880800d80c002403091482885041c04180c035500e003505400e0004400c0d1b55400503c2801158050492360000c041c2074030754092078544100305440341d00c80c130102c5080900b030540000303d8051000745515100800744803c104045100c054001c1c140c58101a0301d584145d03401999a00d51010506420741880030700019824640c0348002420085080720070114044c1c580e2190604100500569620074005590001c0c00203846008202d03592000d40b070500c0d82d0901403c01401c0080c0006120214170812840c0e440c0d04001c1d030310401c1c1c40c920140003229030a080403040c0c00310a0800030300e002c10040c003a20700d18068580120350b101407907819900ba640c09032540c2001c1040b04900080d0b42c01100d404030381c811820001809a0320300300c0500e590040fa0400085142030311031500509026040c806207010840124500c41950568041c03207500072031207402081907604a440c2d640343c09 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 240746232 1250 240744982 240744997
    0x3010501120b0a17010b09010302030304050d03140307020304051203030c09040f0e061503070b0408100e0f0709090b250509040b090112031e050307120b100917070b 72
    0x30200c200340181d009450341044818140c014081d89070540c0d9012a41e034600c04a9046207015480c1031170300000c80c507001d4100c074103032070700a0020f50615007460b00b0f0280d09407548509800b40000e0a0b0001403103030091008500c10a1564069900e4030714050074455540b042c4034682e1103540003402000441040365003a15102e1300100d40100d101000043c0b80c00c0144090f111121450066400700001a4600307503040108040543c12540791941c0d40c0030140050240d40503411540c0c03c0280c810346124040d0700244821b120042c181c5651040c1c03800020320b0000d065019009054a0b400e011060048003941640c0c85080419070003401c1840140f10074031421184003120a00c48003003084001501c03240d1140c840c45d4806007a0160703558440c0fa030b1241d540c41f4a1f0044000601d1000304808800ca0074030441c10317042241e203c960560b26070500c181d948604031140000c9040e5100311003100c40e80c403000004400307211500e9124202d07003030010880000480112024243e84044410400d00203542c04442c1e58 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 240747482 1250 240746232 240746237
    0x10b0424080a0b010c060c0305060f030f19230601080607030209010c170d020c03040e01060215040618060203010e07020d0e0604060804060e060c22030c03020d050a080406030204180b0603010501 85
    0x40d070b00c6503c0140c071090020400905940e00c0c0c000194085a0594422809034500b1184100708030594020142d94407161283c462031174100345c00748a41640074900c00303d211071003110850340f0680820700c060180070a03d01038403015444907004101814060103002c0e0855128541503241190300320000c1c1040508610007000301a500340402d40740c00040c400d07200340c4808030005540d64210714401c80d960750813502641c2d050400c2000000341c042c1c00040c401000c00e4003005082819a1281c81d150000c0c081480041e0b500c980c540e417800d0000721680300440c003805038100e101980c1d04141340001e1030700a881c88a0b00a2110760340711842190303075034030684003200c051703182c071041a40d2249801c80150107864010403c41c0f207440140302d11061070303d01411000d800a0030f51b24402c4100c2c1c82111129210340700c05818010880410700c0507092525503100c1550150084540e55091a9100f414a80c0550f00c000c00190780410103100c503200060759a02c0c109414802407012038030300701c0000e88921061052506 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 240748732 1250 240747482 240747491
    0xb060a0807020c090903130e0402090103080c070801020a03020a020c1002100b150a0f0215040b0402040c0c05070303080907091e0903110d02060601030b0612010302090606070b010b0424080a 83
    0x28000d100b00070700000f180c3c1c0078021550608110301c00725500d4000352001c0c0c031180341c0004046070700402c4e001c1152150380c0090012403da40f0b141c465200e203034005c00301541030b80036146005c00d24000900003400030f055641d80c0141d0320080800028144000799000520405442d006062003640c000360714200141410360014507402c07560005200c000481e07641402024000c511034149581140519410380680c1d000c0e50401d00d803040c03c18611030811a0024003441400d8007250141c2803c0d03009a4030101d450401d055000c11544620340351244603401140000e03070307a404005951400384000300c0244060300c8140100300b041c030311419002d00081301382e194840d500c1007940c007814031882008140a03216801d0f111015000c5000a4030344c40d080700c403e40803a00b80349500c9803c1c18030004440b08003142183c0c00c54240d080d58208401c1410188c82141d1115080c45000e0101c1c518040c80340c0204203410301d140d0748505e0004019208a01168482c1c03002154000740ba90b06a0841040c0c1e5004404600018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 240749982 1250 240748732 240748741
    0x11041b020c011115010b0d11040617040f0b0f0702010b01020c0906040c090e070906020106060c08220906080f0f03280c0611030a14010501050d020904020d0203070c150b060a08 77
    0xa10b0656121130030820a80e5000c000030b460a4034800030441400aa40c05010980c14484002e0080c8502d104040000f68480c0700c001405030400030380c41e0818401e221414081f070b00b0742c480b044202c10648454078450301d0b000038045581e03024400c00860700c00c28000781408061240c0000c0e10107800425080c09152240100f03441c2500c0f42c48440b000d09010b1544415500380b04d10002c0610340c0c20302940c0003544c64050080351240c041c014269446500c040300d00c1c0340c800f10030010840708650100d03150b040400818042180c450b94041c6801400604000700715000d440d8441918094007030000122a810400141c0d000540c01c042007183e07501900c88071020b8400e800000c079655002c00001030040c501d070085408118a490b80118001d806e6039105006010b40114082e110407800c2c420b80e800b19008100004800e045030b009040091402800103052590064600d003e80c0d00495041c40007032206542d240070010301c1d4400b40c61600c940f0b0380070000c5c50036040204046115031600c0c80c0c18403c0400008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 240751232 1250 240749982 240750017
    0x1d0f0a030f081b0714060702060327010c0f020120030402150705011b021015051306090e06100b0403030507112404060f030b091803040e0411041b020c01 67
    0x40380e80a1151030038061200f16004059298019405001c0b000c09540980352058603113941a9a11103400820b4185141c850201c0141a0f208091000c880d4085644204001840a20a42c040c034002c0340c440d4070007a140080b000342120101d081192a401c124664181600f103c1410380e58043d50603201c00100c000c56004101070b40c06a241c005000b9801c00d1b007141411444640000030000b071075001c403201036003200d035250184c6124100c141845203035400100320381c3c506020000c00c002c200310400284039880d4074403035054070407031139418007603030311020501c9101c000021070000184189800c0c14205420355500a02c2c40c8504074000c1c10b081c0342c1c031445000942e20700c40014103d42c08010324000d0380c4840f40720003080f900284214400710b10f001c000c8030070303c078000e015501358440001c1ca400a66692041203607400541c5014204451105100c00710ba2200711141460040380035509402a44004100704030540780b080030b290216101040038143c0058002504943c414002d0a0030701000c10700c00a0b2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 240752482 1250 240751232 240751237
    0x11030d0216151d010b030d1805040509070e0c070803060d080c1e060703061214160f080c01050702010f030509010b0a09020d06060c050715090905071d0f0a030f08 71
    0x1a06002e0803105110442c1c200c1c2d80704071060141114180b004203064440a4200c80c8203d0701c0a4054001801a0004900c612010f0000080c603404040610343c40b00007007002c540045807098915804000c0c188130043e41d81490b694040034500d440c515000d0b16a0720561280000382540d8010741c800041c45041040d02016a0507101e1544116268007003003c2001003404000642101c80d8083c580114003072a1080c000d070410f440040140c4071081240d6501c01703107078400c440c82c5940700d4050318510415862404040c10f00400010512034851400c103042541000c81c54580f003414403504015000040c4d801000380d81001da901d01340020641e031f8090f9401d01510b10030300300c154068400ca030017141c140824ad01505018084601c200b040c140c50302001c0d950002308010192142e4450380017081201225041041e1000e11850800c142566070350824042d00d1050f03d4403000300d103007075083ca078580b45003400d8843c801000702d074814550552040032808407131490201500501200700340409100b0074108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 240753732 1250 240752482 240752527
    0x4090c030209060f07060b011407020111010b03010615021c14030a0603020a06031509060f0e0a1407090519140103020a020a0b01030c051201020c060f090c0306010b0d0c11030d02 78
    0x80c0a680718106508a40180e1041700c045130507500c0c1811146841d441214015002d00a85a12030b150100c203800542c1d0714a2072442c5500e49640b690f60713150490302c0a0242038003c1c40e0f6100d82c904900d4008001070f050403082141e503055000c0c007051142c11079500407130450300d662a00010759544d0f2038106008020f05000e80010f5040020072000141031350303143d40003d00c42517150382c00c8019540c880b454441070725118468210b00e14608082400440c1d00c407082f160b00000e4151000540c3c40040d103800444c0f03c2e0403540d840206a100e0780c204102d0401c051140620f0101888201103603003001c0000890101e446078180c10140d0200c2c0c030502e030034000c1203850406900046810107941e96850085403108141c06070900030389010764405d038200c00500a0340e0f120310300c000c068851613440f102c811174402c10040c10100074bc03084039021022910180300c0c89010f000540034556031100b982c50000140d42445000e40304000f400f070300d4400e0054000c020760741c14800020016079103500c64141c402064000c0d50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 240754982 1250 240753732 240753739
    0xc04091a0d0b071b0c0902031807030f020f041b05130807080102090f0105040608060105090f13050405190b0103151103070302070203060a02090d0b060312070503040e010f03050304090c030209 84
    0x4207074606111498109a02ca03400c9650b0380500e0181d0b1200b42c0c54040c02c510303002846a0040d01080c00285015005541d101c03441004807014440c0b1903445c585003400c1b42d80182d07015141902d2000a40c1404100481102e409039018801d80100c0410020a01034448080007002030209079406015881d805d4030005110503002c80d401c071929620080d000354040d6480d2481000d09207070103111540100262401c680385500c8400c2141d551400640781a407080c0040781e030210680b480c400d00c6030b0f1200741c0c1c4203200d0784a42001500d171403d45003580c98041c1a030020201c0c0c04035202c2c4280085e0130341941c10f0540b54400c00b0306101440c0b4201c4c4002401880030358200a41c0084100b08c08039a060303000d0480d16008a00301d84940d00c1c2d0082000c104c2c49090640d03500a1103020002d4045280140b0042c2c10900103422200d90640b07010440066401100c002c451a400c002010445038841c502c00c43c2c0901218809808c5c03035450341d55060394034455481203c03601ea4484030316154082c000c3d4166400014040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 240756232 1250 240754982 240754999
    0xc0c010c030323010f0914070c02040212010608040303150b07020409331104050901060509010905041a030106051005031317042c0925050d0f0b0a050c04091a 69
    0x625030b00055043c2402001149141c191001482040a005010f282c800c040303e80704440c2c480c500c0440305c509085d101660040c1e003c000540c44105138814a034000d20350341d502e01c0428103041c50000c0a407594018480403804401703606000e0700304000d045030f5180d641110001f80d89410b40c03034031003201290032a15800d90104001c1400c06c0c0440850f2550001d0a0341e60b040085644e001ca400700f55005500810341c000e4601e4006100035802000141811031050400361640c50f51000014251450055410141400300b26a00001c1c2424010310010700b004454410288031000c100900078000100f0407031050030807203210000d01c0009101a00d690303625a1390b0381d540b02c1c0c03112003400c9000e41080e101010fa01c450160b10640300b020b50034040c013a00091000d04203401120800d200b031480107010100400078560341c0000c0a544d404002c041c400c3c8212004e5010368514200031074612002070004400c541008108413101c80c244044a01740c807281080020248440511701d00d000e480102c40b5500450031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 240757482 1250 240756232 240756281
    0x150c050c210114220506041118070207080115120b10030b0f100e06010e01050a02120d0c02121804021b03071b06050702090f07020307081207030606050c0c010c0303 72
    0x103542696208810300f0f54242422107940084c0c4180440181d0081d10503000380c80424005181c1d500f40780000c600080030042540901c4038130302070324081542d513880507034460002040b10f9003081c050610350b03c0c50b200052050b1444c00070b10302ea00f250106001401c00908100080313040301c2c0b4109d52800f9582101000a6074507041c0c01400607000d06452840710525061400220440603544a1744200010317520b01c24030301383d143c0041d165500414040000e500400542d240070218101c0944070000341c01c64007058500358020043d06100b800f055050010104011888a101d11845400480304040d680140d13940c2365139402010605804002c0542c9000000c0c00005000561102e0b800e026070380980441900c1d5110310903615803144ca40000d40004d6032030300081d0190402401c0ca90300a0250041e03d250800d0b60341c54540750b03030040b50501c0c14002c00c0024004003903418400d0401400c3c00c0c1c14007a1810f03524801495a90005a03034050402820b00700c2001014426000a03601e068030b071041410030500c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 240758732 1250 240757482 240757511
    0xf0d1202031b031f0f080c150c011a1503060d1212050703020c06091b0f190602100606020102030112060504110405010f050111060f01061125150c050c2101 68
    0x72203c0c500c500c4200d009070204580b85020308403400c60704044010100380341901d00313002300b40c3e901b048280d0fa01e540600107004603400c207000f8841d000c154400c0c482e82c5100c400341007141c1b141c1120403210040b801070041054503242c10f50700540b031942010500c5400151641e0850300502403240c0303030300c140e800c100500c002c282e0150090244500f041080c1d800d1a40ea5130031003562038440088039180304c0303051080c030113035810414048025103101801c100001e00341c0402c000b824100035844180141c1c007641d02c0c1e60802079548100009442c00d40300039451945131020a03600c0301c15020020b000b56a0300c80102c0e08000503400c0110002002400501807076a407198414080e45c0f66116050100b031302c24040090070540420050310600f10031210592603400d1650803900c500300c2c2c40c8800d041d1f00c5200b580504060480015840d9000e414600c19407040c20200340ea5064507504881c202489100032600c80080c1000c41c24540005040e034098035001c03032007134507034524215002c580340b100e518045414044d0503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 240759982 1250 240758732 240758761
    0x30905010819020f04060e3708031233120f01051006031a0d110a081606300c0201021c060e010506191b0503030a09050f0d1202031b03 59
    0x2038003500c0d4800060101070901c1001045402e891058100180748040c141c1c200414800b16100403400ca003500030b0720350790780c00c1c2b4540c40414903074100c0501c0c40c10010700c83c1c42d08144240d00c0000b9042501c4003550031080100341074079003400c6442a040ca09d501c014170b4004210348a1100700c07000081c4030a0034140701d0447c81d02054020b0b400000e003000f055001e5071080c411228806130024264000c00c030301c0c43c0c0310281c60000500040f80d10020801380012100ea04202131103280c0100824030840c94500b410161007250304507004264100000f022654400c003542c080c481402c0782040c00715120303445850403402880380388010301c04042c0c0503419454000c00e580c4004280d803043c010060b1103988860401c00c1c20b018130100c0c4060489440640c0070386601c00d25582c82d1803042c202c80c10b00d1500480c6c5d00e050454008580e085032965031000700d00c040c03010400038040c802400b20040c2901e08005030740249070b0305070416001c2e034080d000008241c8580400414038524050202025101c0c104041000042c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 240761232 1250 240759982 240759989
    0xf0409110102011b02030f0a05040f030303150905090d0e0406050a080109060f02071509060f0e03033c04020f030106030503031b13030609170309070819030905010819020f04 76
    0x40d86013800c3c61118450040c03440e884000580c000310700740705c2c481e04542029409000d01e981006030500c000101c2c6c529100d40b94000c1c3d4403c4e200840c405031041c1c3c80004114142c1c0c01b4201490034803041c0700ea200310105002000461a142604ca20b00002010070042c1c0020744c850383e04411240300c005400b41d019071203101c610b40300d85000c0c0f00c0c0e4020076422000307a00a0b000094400d6100e2082120a02c41643c041c1e65102d108001c003240084241c80a00106c8060f2080e0007071507040002000a5550001c0550f01d440011040b15101075807815160005071040710340d448040b04101010605640c4c40ba508001d418200800910500341c0300d03e4155141e40003aa190203841c4961b007140403684012800340c600d180c00303520b04039505900e1038a554001d041e910700141d40c902100b0601216046130040210b21401002c00100180d0745420042482c00036012005500a000e40c0d81902c00268040c00d40021500f00b403900100a84031640c40f540e030070015445030302c10148000350f40e100d203400040150044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 240762482 1250 240761232 240761237
    0x209090c070f02130c0801120c0e040c180e06070305042301020904050403110607020a031d04021b0106060e1504031218090b0f040203150402030702030714030d0516080c07020f04091101 81
    0x5a07688c0b60003082c20041d4040c00185080980700007070013100c194084103030b4002e02500c1d10003403032541c3c1c0503a400c80c042108041d2092980300c0300c03000116001040156042141860204040e1074161101458402d1071031045901d050699000001114250195810490700400420103410240b078064981000b5403285880d500880c00000c00c17281c004248541ca854040d10f860703903c030303400c009101006100684c1140e4800e40c02c3c04480301c1140707503116020400d5008400001d07034508100c0302601352042d0200d0148203503140458400000004810f840450341e001d40c0c1172080310505042a503c850900c032007441e000c050003800160340303102d1303420048030004207840018003024a9001d0100380d21044403c009407036480f0f10a80a5410b040d0b000710342c058903610560381410500c2d42c607220404209181030105a001103072000302c6e0800c6104e07854001002d09001051100e0582000c3d103869002481c0843c00200401e1a0040d521100c0300030200207001007040080303108a10b8030142144011603590b00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 240763732 1250 240762482 240762497
    0x16020406090b030d020609060f07032c0f0304050117041e05071d0403020a1b05060f030a0f090209070c06060b0c030304060c02010203100b0c0304030503031305100209090c070f02130c 80
    0x10b41d85c0081005c90040c0072140c00b1f0070f0280d40c0c2001641c2c111a000d006102015501c0da00c80c80c00d040000d8401003114081000c52245102a1071050b140a40c050340b038102d035410411041005a0b040101c11845107046000b900c0745a4440c10012980c800c80114245403081c212486402c2140200d036000540e42e0091058a040c41050780f02004107030308840080259102c40440c102044046094010b6071400903c41242d168a45010130a0345e0800c1c4011082d102004c030500504090a000f00035640755410b0003000a000e450700060a00280501f19506005004541d0018008a0b40000001d4218040855960311603103400030b90b250300031101a80e00030320309030490502034810f00843e40070300c80c440d0400c0400d07428880001420360140d880c0c03180a10003017200000040051001d035102e400600d2064036104000c2c04d020b0f0030301081d401d0007003965204120701403040d41ca40d8800341d000003480d04126202e030308034940144400c55401020b54499003034081c60f80a10810b030030804584959964090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 240764982 1250 240763732 240763753
    0x501140919171018020a0b0c010f0c03090b090c01050a050a020f0102040308070b0f10090231030c060f052505160504181106131d070305150d020616020406090b03 71
    0x2860000d44c080000d40c464400281088405100001340000d41c04010001418041e2410080c0464545d03410f1400841e480702c1602040c0400d1100c8954020b924501070070280f12403800007081441201e40240c2400800b04c0c5902c402d903c20401d810310700040c0c2c0000c5580782d442e410120165004006d0882d508901179002071262070481d000707180107a187c08a08185a41484541400394110202c45c0c900c0c00306442d41101c9040601308406007022030504007009403070071403e095140d0051078224038107100b0481c0c1c20b00082540141115101e0404800c0791b010020140210106500203450281c1207118000a0805101d6518214003c840040f1410400703800180103626094509542c00f4080881c0141d540781c3c01d0610b8070080c1000300680c14604081c0745c89410010150000190701d042c2d08500504101c1e00b60703010300c2041c6e0070450b10000748660103400000138076280100a8000d000e0300f404182d03c41d940f050391003500c150aa009006110700c6403903500700c00080c8410071802d88a40303d00e802c0350 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 240766232 1250 240764982 240765011
    0xc0f08030a140c0a02120c0a0c03111008040b060d0201120c09060905010e060d050a0e060103120e01080603190318060206060a0f03152007030e01080105011409191710 73
    0x180c3c80e013509500a01503400140400360250f800c41e1800300024000c3c90a50300c00075461040f07880183d889031001844d80070702c0d1014021109008008401400654018803011440701880e07180d1148040f500f150806c04240b00482d01a114428004a42d605010715680f80703980110810007a640295500d1810030750314401180e04100f100007143d000343c0c00304101421510b81c1c2d0402c0342d21003031001010960080840c166071411400740c1c8240e13411400d5000d26042c40340d1103d5042040482440c02103030310f040101c0025100d40c9108038a801d0074811080050426005e2b400e202000d0795859011740500c0e039240800794841c0c6080321150321480402401065810440c01040142c903040149200107018034031801000706018054143c01030a00c10406441200a00003420540d10a503034000d00794045000161808106130406c80c1407207007200e00c800000c0503060544076003001c00c403035180440d0079291725050015941c1c1c10012603020704490b2220710b00000100071a0070314003940c00b0820304c403050908 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 240767482 1250 240766232 240766237
    0x60b0303031b091f0507031d130c030f020c0a0308060d050d0804031b0c06080a05090613020d05061602060702010219030b0f030a11180f06010c0f08030a140c 69
    0x804002c50851092a211600c0c0029052007000a001089820210100c81018551807418a4009000010342004040d8070010400e5509100b91440d00103410340000180740c2d45010401c03124082d1744110464989100350098443c80782441d40465443d41d60360300355a00c0e07454120058010540000114009050080000503c1500310700680080c41d003440c01118020800340080d400c0003445120818040354108a14410510600f06055000e203041c03005000c14000034101042e062410f010809400e90104642d98008001c0d5090040a64240300060281c0f5a040001d0601d10030b1404110002d07030000720f8503403606001d03001c40399241d44001c401c074213034401c0c144180c40c42c2d0300d95418124124000d41041c030b4041c100619201d481e810000100c0c2ca0060712083c10f41d0344010f502055456401c10f40703d80042400c50146280b03c918060304072115610020300901d04100000030403200740312581400103142c1d580724a140d990380c240000e0751000303000c0002c6c409034000300000c0070450a90000c0d08 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 240768732 1250 240767482 240767491
    0xb0a020c18010524120c120c0d0513020d060f021309020307020c06040f1514220f0501200a050307140106050a05010210151a1308061b031b0307050304060b030303 71
    0x140d1300d1070811384004440c80c001000d040e0001a403c01d10848070343d0329070740d0503845c8181c0491224945030b03850f1070890f00559401900b20384c4009030702810030001d030b100d0b2050414060380015011900c494008902c40081c8200311a01c200040842c1c40420711075110f8005601941c840da00725000c2c80e242100700040343c807603841120301b10041140d00b0001a000c01e01c4a96802c1164140020024031740b190600b4030f40c1c40100806400184030b03122030a2480902d00d01c3c00640402c03008048c3e01414000080c101e41404085001200382501c2004e4040108102c0541318035400001e480e1513200c1850006800100c0680a039025400c22001041d64100458418101c8105170700501084040c2001d030340040100c00c2a00307000c2a00c0e00e4000c508030300c81818406104841002c07090b502e15180c00c9a4944200d50f40065889400c240d0501481443d00025040010b8803880559902d880b114100c4d40c24102d81080080d06460200030000001d0300310011354440d0f402540e0038082c040702d400c105030f200c3c802150b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 240769982 1250 240768732 240768799
    0x6131517010e061507050109120504080d03050a020405100207090b0301020f0301090b0d050106060507020a08063d0303031b021c2303040b0108120406090b0a020c180105 74
    0x100104041100e60240603000300d4050070b015a0122a0032102c96554801700302520a170f0344036040e100c00c01003c201d0141e20549203180590500d400d00507143d40b00d0001c00301003c201a200c1010950880d4141c0c1160000e000c010002c8043c2061440040c2d00d4aa02d442200143c030b140c44514505802e041c000c4172400c2c8507c1882c945141e0801551000a10400c00c0c19a0402e0303503051030400080c800d11605016045036120713580c41c1c0304c4c2441040583c1c06a5048061a80c000c2402e00c503200d03100e00c82000c5560145182034003d00101918010b08803014402480c11b1080040e00006242e010f922100c0211500c0c40e91a10002c1c191400380d03607418040e140c0b0100003c150203c17140452194240d020690312680040040215010000b00d140d002074034241e415034104c500421107420200080c0c0d414006000d0080e040514011002e4403c45d91031040c0080c5400003d440c50390340c0d1003805031010b50707440140002c00c0c60001102051081c0701c00d0103203074000d071021101c01481440c0e24107234014052512 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 240771232 1250 240769982 240770027
    0x20901090b21040b0a0e010e06010e0717010603050118050f0c0d020714060601020c100522090e0a021e0604170123100b04080a1b05061315 61
    0x40c007060a0b90088800004000384401d400c0284801c0e044894040d40c044c212614860074014413420441d83c0010341c0101682c90045808a42100491402d04441044651303410998030010203440c00407241c182c030300d61580c408002054458156001d1416658600041078020082810781021584242c071117402c1c4003400d100240c03680041034001d0a0003414540050300340035060759840301031a05c600303400d5031581000b020800700f0350741002061440e00d411107501c00c0d14844448054814804c0b520602000c10141030009415180c3c40e961340000d1800c010204600c140080c00c0c1d03529030032100422849003c8002e202054a6072414140c014072400a041601d42894041420101c04651086443d40e540715014234849890342220540d400114200407011450314000300f90504406801200b120442032000344103000c400994074003c1984030121000d09020003000340000c0819610442cad00000c00a03104005480c1840e00c6401c40d10301c00c07160000702d507030340c941602c030414160803124014024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 240772482 1250 240771232 240771239
    0x105060a0509150c0106030302010207060f022104030c020d111305150f1507031110020403080921030a02030a09050f01020a020d1a040f0203060f0c0d0c050d02030108010c110102090109 81
    0x11a10b0303d91084440780341540f07004516800c01d42910481e81c0309801507540415210103021844c0507640268000d0f01702103103030200c00211501711011481002d4418020100042e003014011411002c2803600203010300248a001d20380030460700552100140a0b5a5659200c000042d881c000d01c2d0040060700c101c00307002d11882040c016803034500200e07594400c2300640b0a4003c2c2415800903d5440d0280d901d882030b1203941a002407070300303000c7c5480702e910b40d1041000b04041032210041e0381d40c1800850ba2800c0c1d0028072a045010882c2242c2d410001d4000081c04c0341085800000820881d825900d88050441d6160100501da080380030b902d5015030400ca41110061420400c0450010b01c5600304441c500d16040d8006c2070040115011200304072000561400d518040103500d40c0841d0210400d140761400c2040e2255034000c8070040980c0300e03100d40c2e0300d00103131b8052429211b42102065045440303603510341c00d0718040c00d45c1110100c04202e0b04500800301440600880d48104010b07103a51840a14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 240773732 1250 240772482 240772489
    0x1505011b0807150c0215090a060b03100c0f020d080115032003190509160e0601140d0212060d03051c0b0301020a0c0512040f05100c08030a06030b0105060a0509 70
    0x115664200e400210811a8500048011040304003110441d000013543d0104998041d00d046007180f88080413180748003c11812440c0012083c4045074020400324000c98214080791a01220318180088203007401c0c40c05a0440d40600c4151158026500300e64015211036000e40f600d403002c1c0908801c007000b09260b02144da0007038010f884040c00e800301c1c0003d06601b1641c00c0440c1d40054641e44040305108854503030360901e44c0240c80c0c12410a0002e8100301c07030b5090943c011fa0b4030510802c90303010760f9a000200c40b68001d45c6035a5410100c20360155490203004083d200941c040220b0380c0d038a10a110101d01c1c01d050100824010725070503250301d441d28000704500c901c4120008104011707203489201380c1440391400c1c0007030900c0007099190507001c04113910340b090424218154050340300c0000c0c0b104014000101e01018111901a1225a040d44010000300d17021201050040c154240010034400c9412482c0d0250003101d01070a08800103988903030070410a8410350304090005401800040410b1a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 240774982 1250 240773732 240773777
    0x20c0c150403050d020c0114030603031605010f090b0610211802130504060605040c120f02120115020705010e01050702011d220b0f0603010303140d1e150501 69
    0x844040c1450342e43d9803064a0200300341040030040c2c0200142403142c2d604041404450300d8030802c3c0b2415450300e00b005c26524002d05209000c0318406840c1b850a0000a502400203040c2d600740c2400303071034124149102d07019002e60704207004182040001880c94031400f81a075078048000240c01d107168906c81158040e0a07098000040300494400b524010b03a200a110a10540a01c20118003468681459411203c0950140340030b142010484001c00e07030711091041e0504c10303a000001c1c000e840300c0c0484000b401100400d01800e04500004500c03a1105290a034207440385a00700c802054554004580310304800340d0443c041368040c8461001580075115210030849801d4100354452586c00014200e40c604180003c00703541075110102c5410094040c01d010f440085d2403480480c600c0030080340c0644014800501005180c4503204c401c0881c688c11a0121091107400741b1810100040003008100315001c0000d5640c1b406440046e44134645000b0b00c2111016101c0102801e040c00c0310420350f1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 240776232 1250 240774982 240775009
    0x10e0408070510020d050a1803050301050d033c0512010905070e04092d0203060103080306060706060f2607060e180f060306090a0b0703020703030b04050f19020c0c 72
    0x30300803042d8040f9601c1d1980301601020081900119003414450400d1048944411902441e801d0021410000c00d03044011070381140c001780e07210400141c650404503034807042609042007203013841e000c0200092400c0340700500b801c1c800203600075100f0340381000d0355a03118900491039103840751001001a034181d640055031000c514140002c100c03c100c00040c044030b4810108880c2403140280c005038030030784061604203004402580340f42800c46600001d83e281014400103000050000000c2d0860300d9002c291013000d40c0c041e0040c4103280d1196111800401c42d8020540100d06e2007030344042c46c808501c03c5056806485d0081e051b02401c1c44011504203280c0e400c00ca8000d002d481c1540c81001403c10302901c181c0008441c0540d13070074540101410500081c0503040380b43d01110403140030a041e0200d05411a166090041c1d40b1001031601f43c2c09494038100035035100345010700304280c41207032407080e0384900f20703021000000e68100f43d102d43c224011a4403050459001907000c0302c2500305060f05408a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 240777482 1250 240776232 240776243
    0x3021005040302060a090e090a0b060d05010603140105040b0a0203010b120c220e0c09031507021905010507030c030c0c06021c09080406110d0c0803250306140603010e040807 76
    0x202038594002c60b6017030340105492800100b045804000901440607a507800c14032000181001c2c0285441e190088003010708417134800d00c034860030b2100300714003580005c000b140d101d950611141c9078070003c2c40c000c040448040d9a101b1500c4000384824a2510880e13050340c00132040c0c00c2c20103030b0181042d6840340009100d4030b50500c0410003003903100e4400d401c0e02d03141c40b41c5001401c0d02c1410b1100800b0040c2000d410640588801d01c40780d001640d01140204c009110b418000b025a900d00c40e0072451325006a900d04aa03200120a031030500006400141c451203290b1002e014ac040c0309401201101c1d080b0a0007400038513142d00c1e07040000c1d440d40040c6041c86d450344018006c2c7c122007160b80100c2d41019030803a00000000b80c100203140c0c101c140a0840019900507040c805051400170f0091201500e004041d8071f030000000d46c48030802030009030060040000300640d4981040094001c1030715000d84004c4a03e01250b4001510b0031908403810b03500c05020b1401c158030340359603031495070f0000d25080300c0c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 240778732 1250 240777482 240777487
    0x20a0905061c0b04090305040b1c142e061808030c03030601080c0f090423180c03060103050c10120e0c09090102120601051305030601030b01030308010602031303021005 74
    0x34903503908005070961108031600a1241d107038000c001001c071014070050300d001c2d40c20061507102298000d400e45089070030151950f9035910f04004940c610094105042c45540c0c989698079104800f0b100c0340034440e40303038042a2100000d00c0c03800e10400315182c501101c20413034211028000140b180440d000c0b00300c00c40407001041910b076260b0314150740041008114951004c02081032540c0e00000942d0842840c207040c0f8039005040303080510603c541c0c0c880b603000d552142402a2410003821022942241c010b00300705980c1440c0e02c0ea07000f00e500c001a480a1481003103000c400e64a4007186180c12254004014840400803030240140c0480140d070710380510003003800560300c2c91740034011040d100c045140a0b28011a0400420440c868040c0108601d03a2042c010b441200b402c9064080d0442400d08000d41c88070440c81c2500c01078a9a500a1a01802400e000000b04066080c00c141a00e209403030340401a0380701c0b001280d03280145c0f451000c400c3c08135401000903080420701d90b81191071600d0b20a1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 240779982 1250 240778732 240778739
    0x3c150807030f03020607050a021c051b0d020111161106040b0406080105150a0f031104090e0604050c090403090303052d0d0617070902030a060e040305070c080606010909020a09 77
    0x5040003016401611000303220800b8000f050341c180700ea15801b03141801d00605106162100030b40d00c800e40c4480008005607034444841d0140100180c2e80c05c5001e0304031011509007120708050306c522118264202641c20701c910070559048110a50740d030034143c00c1104401c07000079141d00a6401d0303850301c240c0d00254104800305036401608000c001824503911036038055450802480041e00545580d00481c550512222039001d0340b1490900c00b48200303180102d030006e80d608035150b862242d9400004000c0c50501e4900042c3e10204055201c0c601500544010405407810f1100d460401c44000300006c940e0001030001178011000781c00807008000f006a880300e01c1c41c60b0121020603a1032100007140000c148202c101c4d45501581c005050422440185d1808020a0b2a6203801c0350160129482e0080009400e220269102d40c0040003d2300e0417101c039007000d05019040381d0041c1c1055910b407010140125150000040d0580200b0301070395035280701480d10407001d00039040410401c00b004190744001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 240781232 1250 240779982 240779999
    0x3201606050f070f050403080307051e22050f03070302010f0215040f050d021506010c060902030105070f0810080706050306010e180702010e1501090213090f3c15 71
    0x2503100303242c611014012030611203009860301181c1c1140c541009410071003440021600d1083d20b4000b03d4906002e5180d5600c11442c213035503107070604440030985001c90761600100103503000301041c40c07440c0070604079182ca03401032217491000403101a40503400b0450403c01548551080e48000c207880c81564a41c00e000003000c0e1908038161415212043c0b1759007100e0901c00705200c4070404001a0000707000d03ea400241c00c201d20100240150305200c01d194580c0c047c0b1500c1d40141c1d0303071158001c00802080ca4244005003a4030f110030880800035400100040142040e81615821380d03010301d0041c6003042c500101150b0740d0f0b1004041504020345001040080c0e1104442d4090541100881d4160352501d03100080c21500c0c0401112034503800760906445c941e040030b556a0568801d240c0c056520038981d880380300325000550110b40142d00e03082200d41c2c0140c082c0e1103225030f8596050140700c103410384c11a24005145140e0031240544506009028442e07256011841041c0e600c10450b0f9030a5840095 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 240782482 1250 240781232 240781241
    0x80a05120903070f080a150912030513050f01021305190302040921090608150d02210d020c0f01080f0604240e0402041d060109020c070b03011403010b0103201606 71
    0x520080e1340b04d1b260310003c1008910718030030000c1c01034004000101d040e48a605c921b80001d42600181580c400220346110380820703122412030b4000080b00c2d5032030b04242e5014000d44c8001c00841d149000c501c0302290030f180c003103c4000150225540c944000b81985c0030040200105041102c6181841e41d040c00c200708010410018000c1a0700c0b100520303440c000307024004100c000c1054041e02210f480c10300c01c540c0e41a03030300e0707000c43d030140c940d007038031708116079402c8903411901c080060075100b04040009a541e00040184018906580280709490f9034401580d0b00c0340180c403000081103070070002464500301035100c090005400e01e41d207100c4017003d10114415030b90301d4000168440d4000204029801e1171701070100494068011408032000402000f80c0ba50410301510390010b400103041c01080c0400c0207044080e042509407242d40f56500d800c0f44148000769403100d8000d500b0654034031065030103489480d402000d0072040403d4044101c420202d60fa010740c012180c1d4600d8110f0714801314016114 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 240783732 1250 240782482 240782489
    0x6030605060108010906080703110f04090f0311070e0a0b010e0622080703030503130503041a09010f080c030601051b0a03090e0c0406020c010503060301180c0f080a05120903070f 78
    0x10001801d0804400040c40c203001600011096400c0401c00c00400c2c00000e07200701200d03001840c490004080500281901403400b84003680642000c003410203000c0400c48030880248280c075444580150b040c1c05503211811486612811442540010840003054103d000c207014140b400b400c48c148804005085504480b0701500c060700e10b21500b80d10750004078002000b0302526070003415042d195560082491000403c10139a118079055001e08205080007070760046c01c4a4800c1c41a9048a0301c07900340d1070380101d015640080c990182d150400d40c0030307800c5980642c0d00501818515591900150303a141d0001c80c2c194003c06420f140401002003d018207950f15110b9039462007138500d8040328503c0988060700c82a4408404c2008000003600003039204001c0c2c07001e0a1054070386c0e4904001a004240c1c40c001140c8141c424411074040144000a540c1607031025405c1c03003501d80e00c45802503034480407a50001c1c096481689803a544000c07560281a201d50300808658002d9183c00205591610652 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 240784982 1250 240783732 240783743
    0x90305030114030109051c110a0b150103020304020a03020f0310060807060201060519060e04020c0604030804060c030e10020d0e0a0615060509010c30080411011103070803190603 78
    0x8014040d002d070b402403241c8400000c5009104090036a2141500c88030b002e001da414200c0d00c05c0118031501d002c0e040200c03040603410296003003201c041c05c000f50040012a890002e807005072008180940c000c3c420349020f02d40141401c145e07507055500f4040381031103c0c1019a814403072107a03014102c2c612170003403034054200180944421450480040c0c2514141c0c2c0002c0e01c6203500512112206003104441401c0f00e1051038108040303903044012074028400d4a401c0a95401064100024107800081090240d846410100140300c020b100450455003c003081150320f8002820005100080d0380180404d010200c9001904d0380ca00d00500785040c8501c041200c6060300d0f10200c0000244402031503000b04654103145151080e1800003c2107084104070044c4000030b000c00615904c41d017032440d000040400034103004501c24624010b042000f003143c0031100751a1840c14900c1c1d651085a01c50245001072008504180803075444141d036400042403038028128a0b0564001507004e40a060011401103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 240786232 1250 240784982 240784987
    0x120417091e030601050a0308220b0d0c080108010606021f0e0a051005150607080c0c060307030e06090f0a030813150c0e010e01020c060f070f080415080c2b090305 71
    0x1d400b41070400605070301051050022078001c2020401e99412134000c000784880108801c1c4190300c0320080342202d070b0000d515914010a8980c2c14285070350100e00202c203261105009682c0e50f05080742600c500d4064000180c219841481c0c0e40a0b018652419114144801040c450141207071750740781c15003450040d5150703400386260680c503403c14403949401082c82800340c0383c04800400807442910440c0070003007000e04001454900014140000b40d501030707008101d542e423401d10641c02009060119000d01c51f50107488003144c0c440343c0010b20081d060340b00c0d0001e40100056038030b080d03c2c481da0040070a48101c904549850000d41203029010784020303500e02c000380c9200c4865000380700f6056540880d05000e19401503200c1e41e80c00044084c03111038200c4282d903a0304501c0c000e00c60f450180e03c0c4014001060703800da2104110304840604161101d0504840ca009c1261404642c0940144e40e04c0e110820100035003010f8852a4254000c52420580807261980c1c20000c0203089a00705601030f400283d01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 240787482 1250 240786232 240786289
    0xc0303041a0a050603070e0603030d11030702070801090f14030408060a150e1302060d021309090611071e030306170c1f0206390306010206070512041709 67
    0xe1100c031641101c20000d04003c2460f06130b000c6a50381069002c1c2c1003010080400084040e0f90800c12240382c12110310080c00b4591074443c6004180c0c0058a845015020344039010650210510404002c5500101c00c1c180704e80580e180c0301c0905400a5490071180420440842d00c10820003555004420642c07002a141ca0400841c0781100f03c1d1303420411315940208240b000e00f9103103803100b01406804880f5507598140d444050b030300a00c03074040100308000c02400001615440f9a1001c41414081d1030280032440c11380c8200f503024842d90000a220000810b0085c0404600c04444014a4030900f00098656102c2052004104111800312101c2c0c1c0324a103820b805041c140c81d1081e6992050360141c128008001c0082d458640c014428070200d1015610400e00044c045009000c400660744a6510b0760012080d01800344c1c0111595030141c4a00d00c081a41c140c03042089480300810f04031124860740f40c95803841400e0769202d078200540b1806100e243c500342d68480c140f07a50200c1c44802d0b018070148 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 240788732 1250 240787482 240787523
    0x1e03020a08071a070209060103050907050a0b1902030f0d0c0504030b0127110f0d2a03062102040b240a030605041104150903080703050406030e0d1b080c030304 70
    0x1620b500d10700e0382005204040046c0c541950707a41d0069030900300840c4540d20024058034101090380070682c464a440c10005860690700c008154039141d041d1081c1c1d522000080c01e994134441c50b19158510340c420404c0060b54000c5920201e4640b0b00f503d0101c3c0780603901d448500e0041c0c003e82107442e03524842140100d9032804020040709200b02c003c4103003c890040e01108540d0b014088004102820002e0403d5400c20680d0103003c010401b00440045110040c245030640030302248800c0209150020100f03600c0c82030402c0445d03200c2c0703c043c5003640560b594244800340c6400f1401c1030300540c00e4241c08810314178010ba43e510132015044000e40b1554071540003026250180c0c800c5005600e0300c3c00350801515080c08440c140c2d8660284d450700f441100c04100c8000c41b440c1d0000c1e01c0d056000c2000b40c10554488028021905165410702001e0350411600703468060050034200810101641d104a449510700300a40f40d900510b403003810041403101d2141075500840b02140d0100d590101da018170034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 240789982 1250 240788732 240788759
    0x90f0605030c030a081c0902100215090705090115030e0723090c0304020d020303040b0d060905011706070f0201020d0e0d0f110a0f02132a0311041e03020a0807 70
    0xb48114000c0106a10a40300e01e00a441440707641e0042d0f54070308100d4000320003140c02206102d503014081020480880a000351110444100001980e041d100030640110300016224159100201200c0803a4a0140308803c40ba00c1c003124134003856100c03019040d007c1014041913000784002c000410710002407180071407505032180c403028411a204420311028100b22700c181c03580640d05591054043c511b5000080c42c6001e40d5015031843c0100040e45808104d0540050341110740b224000d00a503600c42102080750340d4503e041110607840000080c5000c0d1145c0000e146904040c00014a40080c0c0002c0f4010785d00c0885452186511a61585c0c0780160301034a995078050032441c00c03402c001c51000030745450740c0d45810041c104010289483c1c1c1503540e4044030b80c0384100003a50030000d120308400320020070801841200400240014081f82c1180280a140d0602040d082200c0ca014100075400c3c91144000c00000c6120002080100c01611800190005481d40000618005290229030711240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 240791232 1250 240789982 240790003
    0x70f020306100f170703110a0e100f0b091f140403140708030715020a02010b060301090e011a010e0909030d091b050a0302130b011e17060d03081807090f060503 70
    0x290030015013804010004504901070b244d100081c61004290800081c0004a040d0810b820b4195000180030201f01c1c01e42620301242c803c0e0300350302c812503500c00030801c40c0d00030100c50b581c001c00300016a0000c2000345009002104243c203100c403132007090b18021565900281c000301c90503000c0743c940e500e480004000c01c00003884584025841c0c02015681c2c3e07910040e10001100e103041d004210319180500039000f2104894000c1e0030079840b582c0d259064070150070482a900c001d54070340820b0b5400c0441c003040140c040541a15100008090102445214030707000740070804600091005082856440c003400031883d00412440c0c1c10440106c4003e100320b1500d0748958410003640c0d0003000161503422001d4108200050001001419140140c1c0c0a88102d40001400a2056400c1c98440c7e00064064552800e0804960103595203100b80400411070240103008280e6a20005256540d05a10402445c400a0039109800d41d0381103070500381c590069103441102e071251018081420b04104020b5032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 240792482 1250 240791232 240791249
    0x6061c02030703020a02011d1f14040c0312030c0822050604030905010207060929070f05100c030e06150622140306190e030f070804051804080f070f020306100f 70
    0x520040381d10711542c60710038289271000c02d40c9001c08840c4840f81d5a11400c1c1815000c4d50201080c84c2a29120400703425070f0000300c80000300d0b600009186440392045c2401d14500e038641900c1911110209110110035002d42ca5468600c540351400180052203821300547c03194036520000d0b801c0400290034503d85410100800400510400120951241c603640f501110030b59601441e00d2030528075201e03c00c0c02005090043c08295100803c04005101c90403201142c2082010111414003201a1085040b4040840c0c3c8400042614100b0240c05a8802440202500d15094600b103000c1320078085225628180709458208006071a9540880042d074601240503180710318001d450b00481c071904540a40d0401d40e100403100c03084c4810400c55800f0080d01c1e1006440346010720740003440ea4002d014180c05400302501c00941c1c188448003060045130300c01c004030709140a0300b4504440341c0000005035685d420b42502d2901580b002d0103502e01a00344240c008420750f0405421200c0d184071030f4003070801e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 240793732 1250 240792482 240792521
    0x51014040b04060e06270c0a09120b16180531050106120903020a0308071209060506030c1c03050306010306090212042f060c2419020406050306061c02030703020a0201 73
    0x22640840d02c11b107900c900350074809a1580120001103070808090381148c5840c0b4541c0711700205102498010b10320070110004005103443c1160340483e88290769208503614115000c106201d6458610130300b4882c091403070102810044031028080000170b082070040d98480c5d03600010f0240d141e0100c074000c2d449110b06802d12140070300d031798025643d45034046e000c0d08014641d800b04150038491644c43c81181c0c080380080c0500742c4641054001071005951030392080c4038005540550781840c0d01d0300e84540c08625403041c44074071552400c0d51141e00040c84903041580c0c50350086120a20791020b030211080c0e0303038000801c0d8542850302201c180170030107070444814121990014440c1c3c891401c0b00751120141c3d101ca449240b0990114902110f000400036510001c7d05009003c04081d22101d1040200180044561000728a150101c1c40f0303600420000030340400001d491030030010010034800b0304a10019082c208516801d00c1281c0080d61580006a00059001030466090140d0101c0b960142840203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 240794982 1250 240793732 240793789
    0x12030d0903110f15040803130501051005043e070c0e09012d020a02030c070608160302070804090507020c030a030203041a12010302012105070c03080a051014040b04060e06 75
    0x300c0d507000041008200d080f0000000d001e0301c02115508d00c0316940800280b0850074140c150741c590362494041c403030240d482c0515644021146c011740401c000c154520702280c10748010403645404540810241d6000310800c5014001500c02c507140008000507011402c5c1800d21101d036600b55500641d0501c6609281c1400104a0a11080100070041103460042e0b0381d08608005904500440c00020070f071740541d00b00028402d40082c10944500540d120101c2d084050b01f1050702207000f000c0014120b402c09010601880c4400c0c1c1c0500e404c10b00da40101e030502c1402400291610b081801c1c2100141c1020604015a001c400518104e16840d40622801c0c91289044200000c0051101074100210b81031481c22414035503070300ca40d4102604005004501d841c42d030151001035113000440002e400c075000607510040d02d00c10280a055001400040d03140b8240700d041d015143c14400725801551480300601d581da076881000c3c002d001c0c1860200b00c42c40c0000802461010300c1103800300d218501004070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 240796232 1250 240794982 240795013
    0xa080a0504060906030b15180603040f060612050616050712020f07060302070308060918030a1d06040e15030723130b01091e0506040909060b040b06040512030d0903110f 74
    0x140601401c4487e500d44032510311082c050540003103440380b900040000140014426550072401c40c0d503000b00000d201c81d581c1ca4110842e10b00c05490090102e801c130802148003800e405105000e40441460010304110349508c421040c82d4110011901603840441e4a1080c10002c0c060000200b034541000c60504010351005007078018000c01003445000000e00003142411120b1030003602003849070899845102d50000541400445001c01c501881080324641d0545848170442d0155900b8064501164464100745c001d071102621074a5410700880b4404a4042c19055011894a02075038101e4180036a020a010300303520012904418142080392114003640c02c0700c02c003801c8401c40320300e158202c501681c108103540c000e074101540c0041c0003d0001504d00e4690849052103002e000300304a210030364030400048862044025402c508140001c00c101d02d4841c02009020307400700c05a0b490980042942d40803103608503c00c80225140080241002c0800c020030100180c0800040c507003100c0c482c469 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 240797482 1250 240796232 240796249
    0x20117060d060b04021308060a05130f0b1312020106030b0a020708030c0f04030602040f03020f032e0905010507110f0c010e040b0619051818040602030601020a080a0504060906030b 79
    0x34050940f6112143d90603141d03a0304a45002c1819043c3d0b1100e16140c1c1080343c4c89010548114040c2c3c0e05104c04a980c0014549003142c3c0a54016021440000d00341e403014110b160040c064154201d03003c2e01200800d42d0070302d04c20f000342120350001610707604500d400c1c45442030180c2410755946c0f05119040000d82da01080b00c1c1c11882081045880356004180940070313100d03a40004000d18000700700094804400c10007101074901c02c441c028000e00d00f031410301d55519000d00101c0e9414401d44d0034810100109038141c112402d07d4640402d840e8080e0b12075609454040e52401e00007008104c0e0240610818810b4841c544c90300c03c040e0101d1120303400005c05039415142024843d5650301d0190030b19681c0c0b03104544da8904d60001048404810200140040c0c001c0000c00b002915848100b20451400800c084a1041400c02c1d00b61b0f641c544d901c404000350001002e690641c452103c0800104006c0d00203030413030009030350b103003540d60781021401405c0000e81d60091003454101014001d4542d1346400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 240798732 1250 240797482 240797509
    0x10f0e1902060408010f05060907020312010b030a150b0705010c0206070f0513031208010503100207030801090e01060b030a0207061d0c0108070e040216110f0117090c060c0a02011706 80
    0x100d11022800041e009100da50b000c84042d40c6492451501001c6580017103104040071110f9926940d030b40b000c01e80c0ca0344200d5030244080100030005004010241014640144000d040081c84a201e559240a00315a90b0010203403040c02180710b0040010900030407600302c441d480030b02820f040a52019107503040304002c0c101440000f14020301211040c011900085401c100d003071002c0c10366038001401d00c4d507080c01098060b0003900031070080358202d402214030550749942c5001481c0c0c64003031240010807403107402084030354a40701c0001d0306142500c013960003a04036200c010ba491544d0b141c032100301c1d903119180d0149201d0704030b49107402080104007624111401c0c00d141265036100c18003203440346807200082d540b052011804000c1c0716130941c100b0342d07440d01c22200540d44664040800103400446043e0078006080707008000c030041040040140c000040d201141e041c4a60080025500d400200000c3c009034403400c080c0040d03684c01405c1c0e00844004141048a40c10301c140403c2002c0c10100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 240799982 1250 240798732 240798763
    0x8030d0c1403010e0f09160b0913020703020d08010906060e06030709030b10051504051f0c202715030c0904050105040b070809030d1802130e010f0e 65
    0x4403a5102640200040880307201c04400c41a52581c4455000c040b1a2050301c40501e00d001c3c203000900b071040001203062201c00c100241c04121407510380d0840c01b030303808100259049a0719250f1603c41c541280061304407503109801800304142e0101005000600c143d101d841c0c01401c20004001141e04208a2221032400b074400580e260740b0300c682a1081c128a45c002090f41e0184010016042c800e00d440c079066078001c9404504880c0400501c05d01c90080c0e0042c0c40d0300411609201d500e260640681c042c1c11002420700c0150303005d65841710b4101d0540c07070402d0040c03803a103040c140c0345519106440c5c1301041c03d1a0008100107111801c4150b5034000103200b824510301c0c0c844004926a42000f0b41800e00d48024074814403450245440b502a0000f560119040e8095902260010340a0f1680c244509280e000450800d0b02c512100f0000e0000c003a1051035201e8144016005070b1581034643c04520b1031402c1c0440c801041103262821204885500d0741c0c16454054103209091004c0ba00714107100e00b10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 240801232 1250 240799982 240799991
    0x10f0f0c0609030e0a030809010e03060103170306031c030b1011071a0909010305010f2904020f04090c020129060301051201020c0a0507060906080c0d050702011e0506040606030608030d 81
    0xd28007a01e054444141c405e80c8010304140020407c1a0782d00200101b89003a61060705000c504010703d42d0702e031400c0c04020301090750b02031205603d458503800b4551045004044a5605500b0810380e10340404030044880003135180c00c0711000030b04046100258030542d5107802e042c4070404001c1907071030784000d0042d11124088400d16508400f2032205460700c0320780040841869503541d2900070300074426000403240b072509041d4140c4941000003c40140c03401d603001e152603100c09082c2040700039841808042000c04080c00081100d014502c11071200300c5039600001860110030448180c490040082550041c240b400703a03070221388803401502c2c1100c0065408409460303401c010107001e0b0042d042030708040d209466001c0e0600c0300006000084403026214036107010b4071a5421511080d045035120001b803c20002405200c00319440b8a601030070a03c0001422000d42141c00c421240300c1d4800c40a80c1c2d114424003102c2d01c0d01c0c0c070407080140310a0804000803807404110076180c8c0642d040046c900741c0d84 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 240802482 1250 240801232 240801251
    0x1050a0e070f1e05120105090f2d0f0603060c19110307170d06060509060a0c02150a0309030e09100506070302031303080703020d0e0f040c0e130605010f0f0c06 70
    0x103981c200c41c048a441d01440000341141500401c185c204017002c214138080750000041034202034200c28003840741a84c00721a51f640344141c3c1d40a031000c2010300c0c0019402c048181c0d9103082c40c07510340350181001d002080000e00381a01094175004003e00080c0311000100002d0715102444410030095800320306114010012270be402c1402c41c0500311010f412441c21007d1122554244001850b4503c00d08404010701b0ba213403281111a40100d030501078001004000e100b080c01d000750343e201810380c170090110f84000402003000e0103941144032214080780c0c403030810408050b040304215038a580140e4101c8114070300815100002062481014080c01c0c0006404051610a20403501398150100c0b00030b040c19a240b600c1c1041d544101c06c1540140684194119154881c188800143c40010010780c0c3d2460b611040000510403c0103840c2030040500140207240c503040125100b015142c0790006041e86010005031101c00f9400c160001c22000c40400f5007400d40028100ca9029000341000502500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 240803732 1250 240802482 240802487
    0x5150403060e0102040810060509130501020c0d051c0506030d180b040303020c0a080102030708061908011505030c0d081c0908070c1509030f02040504050a0803040c060801050a0e070f 80
    0x1403900050540c1c0d05000c1c10840000301500180100c485110441c2c1c0d020031800c03011400c640342d501806901400110200d0390b0072035030068200001e40900001883e101a1007101484c00d40245880c6e00414008140c03403104a91400c50701c461501411404e0201386001000240c42d82501810b00c018000c0c07942c1c2030480d07840082c46600140000c1041555655100c1c100a5901c50f042c200300741c440c6c080d440c0040f070092018001d0301e0007007206859484094071001e04110480b42c0c4441f410340301d6500b5020000f80c1c100c00b40694080d0f280702c4090966914100740c241400d0000740c0080c5406603c000c01c6080004181c0030440d04205581110405207200790344507100586407500c80604580e40200d0300d00d0500400e0310380507041340c03079098150141c000b0b00a819200012131303200107003045c00724504403030140c201604160349c41407141d0107548074514143c0d1150f005800941c0c0682d000d00c0c02c0350042c031040fa040383d421805090201c1d03012800c82c0c5003110024031510010819010000ca000d1112099030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 240804982 1250 240803732 240803737
    0x7080a1205090307060e0a060f021b060d0c0c020405090304060c03050d091a0a1b0207090218040908071106090d060917220506090d02011b0609080705250515 69
    0x4100809581381d060f56883d001341b0240c00440c0b0a8812244c4403000101280030b41e610101c100d00c260042c2080103210420000305400201c540c0381c000c6820030103502c070480ca500c01e0000710107054655648010030341c0188011114000c1000f2001d03807082105111098000081940c1643d0524080c0d03540c003000029000a807009038401440c501c070003c1c80700c15103100030120502c9403030b03a90020441103000204881075210340f070340303124003603009210144203a124940003002000700c9049014100003850003c03034211216090180c814000100c1c0748403c10200035103001103c0002c0f01c50505260740c0400048009503070920040910303503600c0c3c3c1c44003006214850ba8201400d800c0469490700003610807001c041e80341d48038074800e50f4404500428646003101c144d4065000141c800c00310b0546d01d60040d1034010302c00c400c41c030040c05480c4140700002e1660207a406480d11404456450380c0003490700e41d180c031a18401220300090f0941130080c6c1c440350304001d90300701c8000b1100800c200c01014510500303803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 240806232 1250 240804982 240804997
    0x609090c07051005040f48050303041511070f12030c060f05100e0c030a05180d090f05180f1b0c0705030c0904030e0904060605090403080a0b0307080a1205 68
    0x1282004c08000a00c5203003802112414000e01454010070900c0c0c880d40c101d420309403000c1c504440000d00350790345810000340031074070046403444003190309841c1c100003499034115510000158000d0b1000020540d80080b03c40c080342c51020041117030f2410400512080c4415015102c80c03944080750760720615105554404415030812400c000700c140344031140f009040c0844101c07a1121030200d0006403840d1000b05184a4410a0901c0303081d900c4035281d84020340700c0035007001c2000b40f15151444031030505100b10f54814402d9150030702401d14100f0551925401540f01510406020030304518654a9240300c550211221300550001c2d56000d100c0a11440d0b811241011944089100b03400801c00141480c2541c004400b1105050b0810b02000501601190000c0005807041c07020b004604004c4003940e0043e2045d040407034800d0320381022403800f1004840580000d07401100340181241544074000240c6001c0d07001d0030001c1e081c0f00006031f860300820801080d014009060144081c45035003554a80d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 240807482 1250 240806232 240806263
    0x60109020d0230090a0506130f02060a090305190206090f010219060e06090a05072108030c0d1508030f1804050c0a021002091c0510050106020d030b0609090c0705 71
    0xd00003600200c0600e5031801c006101000c40740829135030f40b000a000702540d544400284013643d0f400c09107149840003840220340d01c1c0c54002070540183c0c3c909000d403811160941d2220281441e5041061030404840000003094a1002031000540c45420895001074401d44a03c98112071000040f40780031141c2002484080055400c04200701c000e800c1420306182810848040c0c3d20b0b0619046d031520012413000708240d0189000f04540d001e6010415040503030900300c0101440280c80740c010315802200e00c051070603400104480380220728032032845159031081c801000141442c49c4c803aa00d11039240e540c4444240402c0c0e400c80460070080301144140080c20502a5081600003210075402c40403409001d4003508042c04d0400141d032003500c00109009150084e0309c82c110f658a2420200800166014003448146c3c1c0c05054141c02181d000b00305990062030154040c0d84010100d0380c1a404a61003401c007040043e02035a1500030b1650031001400c0c1140e07a41440c0d00c4d1107490601100f182c40d40c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 240808732 1250 240807482 240807517
    0x1052206090501021b0a030b0405010b100804140c030607030b0409050f010903120203060904020906030a05011406010e0a08031803070801052403060f0406020319090b100b040602060109020d02 84
    0x350280e0103807000048500a801300c0d04c04c00b0b25010700d91442c10085c0465604402e58640800129201c14040358015010f14000141d8004803004607104110110403e0046454041803004000040442d02c1c2101c0000d8050b00402101c080000e803038290182ca50380801da100c0d800380030f0b607949070351000d0300c400e40c03010865030110b04e004420340c082c0500c0c800c01d9000c01c00e0a076400c80c91586c1c90080f030303100701e40042249403640d5407a400c0290002016000c1605807080000328400106c0c240b084859440205d141f070700346440c100d00010711011190714214041c3c00251000c101c0c0381e000006881c200b28a1044240e0f88104040200345012155800b0149941c00d00c000e001003a24182403030080003641e20f1540004030040024103940d20816280d10360f005400c00c00040106645d607028582042003410300d03140c640c07192103110f416203900b540240d516161090500c0140801c03100b00c2030042c01800c80c03c60400e4a4414060346540c4144100b0410035000203110b41c8078881b56044601080c1c2d44525602d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 240809982 1250 240808732 240808739
    0x114130b1617030c0a0f050f0304050c091803030103020d0f080a0302030109050a0e03070f11031605040c090e0c0a02010207170703090605031003140a050f0f070e04030e010522 77
    0x508000111002d9442c0210004907001e001c0501c01100c0c812000301501c140f9164920034100c40350b40320492035900f0083c0501080c94041c03c008011806140100014083c0c88035890800c16018005441040a26130303948034a1200040802900d04694045030300c00180031581c02e20950342c0c048400c0060030300400042091aa80d01540070794166002d65404000580d1100d8000c0215624481c08886944c002c0c400140001c080905200505106030b0310202c2070600d0310042454048101094010b420b00c1d65014481c6080c18450064030742d109280003004a0300d0031190300707031841024140180f007100010302c0b4503240c0e0003501120400f13903010211090034080c98925908076003041400700c0015404042c0003da03203100d0000c0c4d90180c1d0321071300c0041401d491079a400b10003500d8003010300200c0c010608280040f41c0240700d21950300103004003426900c0c44c60060141058010b0300a000c84c41441e2040c0b102203548412003020400d000c1c00c115588230700e0900e201c1a1a40c1d010541000c0d0a18020f010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 240811232 1250 240809982 240810007
    0x1390305031503161701060801020409060503061b041514120412090b0d0c020a0b16110a0c170a020301060b130605032505070501181a060114130b 64
    0x214030841d4098414100750b100701080640783c101c010142490a070a801d41800742290700e4500c40c09011140000003007440c1d441d52500c2c00d90700302c1c0d8000741d2101e0f0780b81c90800c2982801e000382c540c400c0b170b54203000b4007001055405442c20300843c040e0100c3c402401c01c0044400e03000d644001c1117184113004450b290000c0c2115801002c00031202291505410100345403603502070100703401034030b030300004841c00c0030302072141c00d002054658034100452017880380f59004684250701c2c0700d010f8000c4900e4141c0c224000039014202c03261845041c049a480703040c00320301042e00d408515090700c0c00d8034409020340f0308048410745031070a80302000e9415482c01e4000203000030440000d102c007211040e11402101d6444900b512280021034001168941a9107170441046200310110000d40141c10110b040c0380745511a81c2c211000a40003000340503003070300c00340e003488030317004c840101c4014102c1c451100740382c4480000c0920380d00d65108003032008082004984111041107002c05411042d2065464162000b41e8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 240812482 1250 240811232 240811237
    0xa080408070306110901020d0e03030d0f020307020d09080a03030b040e0102120103020102010506271b030705030a1a010c0b040212030c0313060207030b040803071713050d0e01390305 80
    0x101c4401e031034061140710035404c0105031500510160040d1410605020081d02c0c4070189400d0a82c0c180420010040054994070550f5585105135000680701d00e00624042e207050303074041200c4140101400108400c880000344c44082d10b43c0b600d40418121000000304003d007e2000005900d0350000c15129080c0e1802620702c0e040700d000368000d0255445481c103000c12118124030842d1402008000301060362064603009810200181c0c06916044c103070307114000140c0090382c2110005400000340000e514460096090800601d0b03001d02c03003089440700103010b000c01c5c46401040880040009415076442e070808500400b140c41c00d4940d1044080600790b02d82e442510312110401d00c40c00302154452000401c00d0650380d020f40445003e461301c0d00c0c0c000054200521031f8041100d030031100c0768001c0c16496400d015002d8040740d00c405440501d0f2140c00d111103150b02004100ba11000c102d5541c1c3c0c008100780ca01070003000d03000002c041099044030504a001c801840501e4001182d80c105a0300000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 240813732 1250 240812482 240812489
    0x31101090b040f06050c160f06020d03060b0901030e01110d02040303120501050d080c071d070f0f0e0d11030d051209070b0d0509150a06080c030f0d03050402030a08040807 75
    0xa66082641d25408948258002c0d03000c0d454500203402d070207028080c003071381c0101004d0b0000c07030403a84225580c440d1910045100e40102c44104802401046940e804010500b9041d119041c140481c60500c0103903030590007403100700e5041586171441c56083c00000e5100005104400712440c0e994004d20400c90083d43c0684011070028009008500421910344541d0b41681c1008104524100036500c880f0540e4100d10b000030441d0107600c000080c1202c070345400240c81c1c640900107640520f0a008080c001c6643c542e5214248220130611405040e0b010088040702c40c4100c490100402d030034100004144c1d02e264103260584600d0070203542248d00180a8002c103c041d52100b80180c0d02c042046454039a64440c2e45442c00303083c0640140700d03540343c05c0254400e001d10101c0b5a40050340f150001c010038280d0300c801c01150b41d204240070030358043c000d00c9030940096004200020403d45581c2da21520096001c040503600c402080071581e0500c44141d1858200c2d54003900e45032203d000b582c884002d8030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 240814982 1250 240813732 240813737
    0x20105180109020a0b03041502040312030f0e06010312030906060902031006020f0304051c05010504060504020307120f081803030304060c1d0607020918010e030c0c0102060103151e06031101 83
    0xe0200503030005008a104282e4007030300c8018071500c1c001c003400407070b00060b200321620291404650152009403028000441c003d5084110f101100c01f00035045680070520a403020341002d60315522800300042c028110f90f802505241001003c03201100100701c40b80008012505003800014844265009140106601000e440306150b682c42c0036070713590b008040e840a150f0014001000310749060071050074039080c04080e85070300440580e101403c444089808961569643c0c0600040d41030412181d00500341240b03602c407007103500d500c442003810b64041006083d4440010b2001e030b107000c3c01e81000c0c9543e070007904594903428149042c00203002d0a4880f80001000b0203540c0c050900c0d6010b9026696901401c941e28051540d000e10400000082182180c202c0c90401c1100b07841c1c00f48a002c0b040345960010b5a01c0c2d03a550701e03442d410100d01c900b086045600a01c0144080f480c1d2541c401c011104200002aa081d1031003042900c3d03414200544c401c103858014000240401c4400700d40f00c0c503a099 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 240816232 1250 240814982 240815011
    0x1509100603030c140304081c03110a12050a020a09031106040e010e18010513200a140909060105010807051608030109091e12030903020705060c03121e06040b01051207020105 76
    0x41364000d43e20701551040715403552111400c0910b603c005540c0d503401e04420714000c40d02c0c9010480c6c0b149280d014014650028a00d810703925020308080c440e10346c01045030315095281c0450100020070103961408007819484100341c150074140c4d0b86908607030060490b80c4940449617500c080443d61f001d4211350b510170860070340c1302034006070304184549440b828040c400c8618000c91074403128031500c41c581413030b064031401e203090b2a6569505915070009010240c0980360182020091181c41a03000d00040c070941d210100600c9140c1e001050242d0003112031802541f00c04201580341d10800b01c030703030f00a0032000c40040081800465500f290002e1801162900400807050b0030039205003d12510181941001c48062090b240c400d411049409002e4812500d605889000081040d4041c0c0d032104019131000920a400245c4140c1950f402765042c0c12004210b48081156009000c2c01081c6512075540c03038030414456801001031381c0715107905402c10b43c414504010080d0003802c0660320415000b001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 240817482 1250 240816232 240816263
    0xb03010b0a0306080f010e0f07030506010b070303021e09190311120a0f05061e07020c060a02010e100902040506011407060f091a0a1a010215071b0b1506040302031509100603030c 78
    0x2700d040c100d0f6070010062089030b1a1009446854000540460130903400300701c0011405204111110b075424080403081d6503004020410030050090107010071010360300401000850416181004e40420030b48101199002c8403400c8e40c101000040000c2c802d04e02c1c0e091318030030303c040007030942d1103403003550b0242c1c541170103034001e00010701d500311080801640181d9002030181030070409442500403d00002c01c1781042409001d0a000c608030300d8881866441c000001586498003034103820010070308104281e04100803001065200c2c0c03903800703040183c9481c02c480c0703400c2d030652000341c425401900c460903508010f0101e5058417416144105074609118501d500c46c1061002c54030a59416001403000c11070304080c0c00c402c028000c0c103100a12600d90341c5904400c0c000d2015034602441000701292601d4180200040c0c4088000b4070341c000c0c2814003041c001620005a000e0140740a5982c00e8126666418121310701040141405141400c007580001010b40144072044010311071b07003610281120 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 240818732 1250 240817482 240817513
    0xe03190305011d151908100f06060801120203030d05010b07020f0f1810080303090604050f0106030f0803100b04080106050306060d020a06141207120c090b03010b0a0306080f010e 78
    0xf1003c01d109004078004000c2040c4820710489110301100c003514240d100c8400e217140480c115840d50000401d038110011800680030309116001c6280c6140004205044c1071890051110405015900c2c2009030300d0b000c0f41c10765404001b55283d040400c1402e00c111742e181c482109080d000300b00c04a0150010fa80303821034a00c0e282150175000100945a0402c0088400380e580182c075015000c0e2003224908240812100000d0000f144944000d80003051542058940249080e0204400e00b94603450044280b00050f01c0d15100010143c102003601e4580e214016840d80da0b110315808200503020010300022206d00c19040b010480d40101e0543d00c2641e902420300c86007030804c2e00c0003580014000004d115045c001c42101c0000e401f41800d90307042c202919503010106006456580c0410192035800550105134003a000e0007901e50303d00998038a140c186038520500060140c0140720801141180d8414460380c0086d004150400848000c103a00314503080c000c00c060801e030126070089001c82c8070030a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 240819982 1250 240818732 240818759
    0x309181b08010b0307030f02040801020c030a0908060702060406050a02131e0504150b07030507080d02090405011205070933030506060d0c05010309170c07050a150e06070201030e0319030501 83
    0x20035103001503113180d440810860040051584a0f000d0540c01c0c000030441017024800742144140203001180e5174002094050b02066640d400302059a0081c5d0800c0009a0b011555035009036201501048580b5a03003810b4000e409205003001510002900c00200c4d03c0801c82080608645160000e01841c0c940f020310017601e9480c1c0450101d40c0d0342e120100012a0b007000282510741c001d184c0b443c20800c2d182d880141aa0001d882c42549070b0300450704d13500b08d14061085a006050707068000c8170709400c580d0340e59210b242c0d5200300b010884d0fa861070386640060340b41c1a4211300c814041c0b4101c001c0f0000d400c0e8580300b040c5000c140c4452049000041460500003028030740c490b00807a8020300240b07003a0044001e8581c0f458201c50200a040440d540912803074064984000a0000340440508000912000c3e4209501640300c5011400300d80c000250404074690090005490060383e13248a4001a0094070300b00720b6010701480f0000e1000301c6490b003a901461030300b4855070207004a0360b0764103040d440003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 240821232 1250 240819982 240819989
    0xf0d0f0e061602030115060c0b1003050c0f1207060903110d0c0902030c0904020403150c0e0d060b15120a06080a02220e01021911060708070c0309181b0801 68
    0xa0040000415109980b6440b40295100030300104184000d03401c182c1e118445170340503d0218003202207203c204503a00101503403010149269005143c91a00e1f40341e40ca420b0701c81c21a0054078840c958030281d40b5203510903c0d00c4800c400807642559941c0c04010460205031005030fa851a00b041d40b0300d25842c2c84102c0250841e080b404800c0300c2c504200c0b10b480254406455044c0407141003248407203c1d01c40380042c200440c06482600034444880c40008262403410303c542c0200b120090038101c26542d40500f1100c0c032034000500081000001c004101240040b1402101050010038a072aa205144040c58414050103800340101542d032880d140e45d41b00103040007903000f07000081360400410442e46000310004808404610000380d1140982240c5c805550761614210072401c56007055001900e003d0581214001801b6900d41280b00604114000e00120300f00000d2204410a252003490007501624041011002040140f032000700105126049001c1d2890b40300346e1200c040b8001c0407114100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 240822482 1250 240821232 240821239
    0xe01110909090102130902181008160504080a060e0f0f030d02220602010b0406050f09072d02070302100c05070603200309060406060509010b0a03050a020c0f0d0f0e 72
    0x14080e40900304508400028460030b407940d4288610b80945200140f208002d00c80c00d03c00603a624803000200403403264041076580035074801d80c003258900c2c0e4031a424943c09290034804100725103030304c10704580900c41c80e80442c5951040030f00741014031501d5800b000c0707a105036a048a0310300c03520291803919100b00b200a0042500305002040009020341c0040070410b06d02004108284110040104154900c2e000680180c1d503d070412111820070703126820150808171540c50703036440f00c00c0c0090040b810040c0b1601c10011502c071845c8548080680400b1048004428409a0303091b01034000d540b89480d21069100301d40301c5ea0aa4100d9000c1d8103001501504031014000080c1094800da000e07184007031041313074100954901e01014003141c0000e1405105060050022800c043c2052410b40d8241e801c024800d0213141d004111201291007200d18804490901040f550303900c3c03446100070b0003564003208241c040c01050001c030300c101199864409010383c4a034030180164140440d0f00366003444a01d44c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 240823732 1250 240822482 240822487
    0x51507020d03140a02060a060f0317070201030b061606060e0603101a030304030b100801020901081f0e0103081903180f1401020a020618030702010e06090d05070b0705010e0111 77
    0x1504001c4241e418107806800d10600c84240c812040001d81d00c0f600607440140c2280d030911043c000d1034000d50008110344618001100e00310f0301c1c0d0115618003000a80b01c0c2ca10009000b00031640a6003007002c20207401491540c5550007085941e12008030088216a0a8601800810421404c61116000e008080c2c01083d0f601c2070128624000e200341c41084856103821030407042e1541e02040180080c1d4800c4e1441b2a260a02800d030001020a170b420031046c590040c040c1c406030366481000c0c83d81c0300080203c2aa200981c4040214148601d500058500f019520011090000a40c0102461040703490700141100c2c0b4480c0840882d000140050038501c1180356510201c0d00d040580740e149402040c0c102009481541c01d142281d01c948260000341e000b9a08025070f00c0ca29a0200134405801030241d45840da15030300080c51880d02c2d0201920581c1e020070313201d01e1b07070700d0311000c1c00308403503001c4201e41040d81c444030b10000350341102d81e08407500d40c240b40d44c102021a040c020061074503514a103160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 240824982 1250 240823732 240823747
    0xb0402070c03080c0a05060a020c01060b040303020a0b0a09200102101e020702010e030f070f080d050913090b09070f080f060a0c170c031b1c020f0f120a060515 70
    0x40c0350784d02500011445200b13501c010340115005102c01c500403400d03103030300503a40c0d0007844942d82580c0c3c0c190b00c10010b80c0400e21040000c03a4010412400e201da01030821f900642c0d8400d102c10050034500d0001c0c004007981140c80c0c1000103010401c4506503426000ca6008601d0348100300c0039642e0340360690301c0015490a00c01003440c45a0060039a4500c14101500dc0c01441d401007031504280038410281603100080c1045001c1f0745400c148040d0100c000540240154580094481d10444040e540543c1a031509000520141c0d0700000151340d000e01c121980e41081e060855407802640510358042c0e035007400014400701c002849206941c54403010b0026a80c0d1480c0c40001800700d03100003030a001c3c500d9a03030502c0d1b0150b00c003800e20a03050300084c1e03a1681400d0800303601926008000440c0864100030b0440c5041441040c070304003001c19540075a8500a111032088903000e450002e02e225400406d608241600040d100da00c41c0d00080c204200304c598032420403203803070f00c1007084400101c0c0c10050309 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 240826232 1250 240824982 240824993
    0x602030a14090d060e0109080d02040302010e1005070b0408040305010207050c011218060504030e090705040608060604030b0f101a07050c0301060b04061209080d050610020714060304060f02030c0c010b0402070c03 93
    0x600917107030610f0000496280d56140d1108907030041d4010300c4c4040e8001002e20071580c2150000000000580c3d14500c2180b060300040c143d4172a138100641403481603800901000700b1401142c0c003840d4000002d6454942c146020b42e0303589542011540480e070b20049295075411584184143c00cbc040e182d0400303581055888240090801620643c00c224504281212035111519881c0c01501c40d80c0c1d91039602d42c0307424001412944082c240300e20401c42000108003142d002c00c4543d810080ba460240440e844050803c510054254045441c840c0c4111012481c40e0429018002c2c46014200740c1e86440c0602041600301c4e129402050190700050000340f00b094400c80d4040b07000302c000c0b400082c1140701611030f004150482d04807440c0305030b2600d003040041d0419161101c031054442c001005040d040c11805911800c1840c0242d000e450044001014040b0a03000340c0c036010b20301441103690741000c1148840c240d01a140c00310b402d6090400100c030a0415100b1a03103a80e030007019020314641142c0d00e5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 240827338 1106 240826232 240826241
    0xd05070b070813030e01020f24060406031e0c0801060f03110405060303270904050715050307050f0903150a0203011503060308160515010602030a14090d06 68
    0x74464900f443d00e080348080d0754181171085440100c00c0040380380c400c1418200460340300c3c03c1c0b42d0900c280307540503500c07410742c26038841708859940720400c0c4010754540e488000c121a0030302c20b01050006505180c480414800c0301d43c00c00b0981d90740c42080c2964600c1d00710168914450a04108000c0040749141c41441c05641c1407050385401c2002a40b03900405000003600069020000520f80040c88000300d0365900602030a034505080c2072440d940c1c20b05004070402190740d800c841d01464002c2058a100d414a603540030310702501a0a0b21140b5081340c1e51440d01072107442c00700451034003103019a5114107405a40161203615150100c1d4002d00d4050060060600c0e10b1400d0002c40c402d02d08a5041641c40b40d01086501c446180180c5448142040135502c0b0ba445d01c0040b030030550210042078290400d5481071406910308100d40719511401c82d40b20740c004809040600040c1403a0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 240647482 240827338 := by
  have h0 := BRFrame.cov_init 240647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 240647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 240647482 ≤ n) (h2 : n < 240827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
