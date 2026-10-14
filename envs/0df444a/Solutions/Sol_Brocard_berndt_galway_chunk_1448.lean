-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:02:22.423429+00:00
-- url     : https://prove2.me/submissions/d556ac09-3e76-4da3-8d0a-34285f9d47cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 260251798 ≤ n < 260431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 260253048 1250 260251798 260251801
    0x605070c08031905102603120a020a080f040b27030406030e06011a0706051302090408030727120c0819050d0221090d0b090d0815011b030e0306 63
    0x30a003140c58409010f140c0c0f64101301c5915010324841e1207110901c10207803025031800592112040904200448190050840307062111814110014400440794030082c6540420f0b5a102c20703034086029070b004114080c0458903030030243c03143c0c080e9140050082043c2e41c6001401e02105401400074045085428141d80c0c550b515850000c01420407032010f183c407440360000214819102c0c1d00c5120034101000d080300d19002c91782d501e42c2e010301802020706000f1861920840050b80390319629501c100d20402c4132540d24a00b860001c2c240a01195010360950580566003454140c4d424a00098404180020030080030070720303200e021030000d40c0005099004030010510940c0460f481403544510900642d185000c90308070407a1382d66590545401d40b980f6040c4c14006600c200302c002d0100c25006000d5000059842d1990244480183d4038850190700000245004550040c0456000104d00344110020f0414400003000030841024030700c044580303400d1420825004e5a1001c442c2880501901c826 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 260254298 1250 260253048 260253061
    0x2190e0a02090a05091303120b030706320406030e0a0203030c07030b0703140610050705010c0f11010501050f040b0604030b0f070f170711070e040602091207030308040605070c0803 79
    0x282d00981c2d02140110103d0001164518002d110b6a02c500c50f4601244098540b80c0ca04949010803075001c80040b5070b60302d41d5944141c070140045c07009802a500c039920790300c100200000250340903049040e412907205420400d42c0e44442d00701c5045502c0c42c079021403040030300d082060608060b00c0f0025450321000031074000042000c105002140c3c068170f901405592005403e6003510070f09400b40344413101b07d40000d11a032400c41464100c910552405d28101041542d0f15801c40e83d030100303580f01107001c5c90310032a0704030340c4260040204040700e802440654500309c00701d58810000c4003018405c0307450715411840c45d1152026a802103420282403002e03810702102038100e142d4160f5160001404a400011199000b5004080030250005410040e030b41d4031501152206103941c0014258041c9440004019403104080350285001c0c406c0165034800d80001c0260749a03040c165200c182d003000c0402c00c042500b1007141e5a105800000c082172564800c0000c403091780302840010b00c0c0190210501c03c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 260255548 1250 260254298 260254301
    0x170d060b0c01050402100f0c060911030d090e0a0204120204090807050a0c05040c08060d1209150e040b0405070c0803060d0b0109050601020606030c1c05280c05041802190e0a 76
    0x1985c0262044440d2554901040341c41c0f4403000c6040b00851808014a00022925804220400d00804481c116042c1c0394001130300303007524080b0300400680b02c0c05040c810014800b000780d81054171042e0440c0352a2911401184290440c03102911071695400300340107100e448411070b803841c0e07803000036205880a1803a01c0707459000d07a40034a90103540b60485201354540190000c030301074000241300941b080805e07550400c2d03480b00b82010300100100c0c0b401c0003034652580d140c5048104000e0322004a00410201804101c82c14150001d110b507007031409129900b500a0040a4095005000c04c0ea0702c0d40c4a8020903e40d506184c0b005100b02c0b42c00b0000503c58056030b1209020f81800da083e112a40c45020406558000303e82c1201c5d400207090311150100741664205103a29440b58003a118216818600c1911644a01c41e0209030109100403480420a075182d0043c040d10f0304490411240003110328000713901c085007500038000c3e0012000680411107222820f001005802141503091610944103030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 260256798 1250 260255548 260255551
    0x1090c060903150524040902060c071d0408090909070312081f030b07051b0d020a050708160302040f02130f080d140a05160506100f060c170d060b0c0105 67
    0xa40142a840b414143d000050242d80e00402540c81080d0950406001c030000f4002a401c07282d40c00303980c40034500b006031255400f0b8101e00382050050040d162410072003600d0240260341c030b42170041e1400100702c0002e02c004241c070312040050360103034108d94490203450314120a5800181c514850601820b8816501c206820f124010709007000c9040c210704041241010405d01000704504000400545c0440c407902c00f40240703140070407a0844c00011300c003c55060207000940040142c01604003181440420496000109030410003001800c00000c803170300e584070060100a116a0f21141410046e9500390103031801c0d8282c020811011683d2100c803000080720620614900d40148030741d0385615405014109071140b00c801c80e0030701d01404148115000d601c042841914811803d0b0082c0c08514100012403041244148c0c3c0c8901c241002c4907803c1c280ea0a44c4154200411240c0d01c0001a610041c5042160180d01c0143c4c0c0310340400400c4005058030307401c96000310348041600f40101c0c40c15000745 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 260258048 1250 260256798 260256803
    0x3030c0414060f220b09030c01051e0f04090c0f0e0105090d1a06010e0f010c0b04170412020f04180b180a081e040501090317070602030403020105060109080d120e01090c060903 77
    0x130314044d6550b4821081030080145140c1d168014100310060340d401940207140000104d04030386904500c0800440c0540c001103541d4205040c041020f10901070b81d481425000209810110005580030600420850654141504114000c14150a50345a00380c582504991100c0707440442c0d95400d090060595007154941c1c0000c410141e045418205183c0c49507c1c82da042e0340300080b082c101d440d413450404000c1c00490780c820806015911400951002d0f10290242540000104915004101440c0b0360070b42e100f8410340c034002c00d80384000d80340340301c100034079900500078402d65864a0b8408155400143c01e464030340103507034640d0b080180c07500052049215446d41100e50b43d1031505a203065000718040c03203010604110041c4085100018180c45a443e60003034586000180d903100001da0300213035400c42c00f40c0c1d161414007a40e982c201e01c5090181885000400090005e1000240720944181450602613515006d418000310217412512506401c03000a071a580e41ea41001451462144410b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 260259298 1250 260258048 260258107
    0x50919140f060a06032c071a07150606080412020c031606030e0705010c2004150503010b0306090d0e030a05030a05130e06030703030f261803030c0414060f 68
    0xf2132401e010348100500c00c0204401808403008101401c001001810b40203083d601c0b5000000804002284045a1500211480b96144e08140c605504003400c0d6000c1c418200e41010014041150b00002141d801784d005050200d135040001400c0e82012600c0c3c00d041d4044c021072a980740c1605400f200d41d0b044403101d0380c041040d030140c0342c9015106d801e0383c01207a0008119420420100f15442d81440200340001c0054204103240720000d0200c42e4610154845000c01030f10800440c602882199280c11060b000f604882c58540082500d6403101044482406401e600c00381c15900c04010000100c1d51040882e66201c6407030b42c0180082c2c2161400512454a000000c600704960440c0d5a001d240040e000380300941c11913400391092444000d0038000c000d200c9903414415020108141c01400800300c49001c01d00740314400500b884051b01c001100d940c0f080007400315400302c0000715800ca51040d45240506100c01d000504035200d0a8043c0c042200c5c003040004d82403070118140107806400c0c540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 260260548 1250 260259298 260259319
    0x20f010e130f05180c0f150d0203090106150810061209020306180624061b0109061d07030c14030c0310020a08060a0e04200301020f1801030501050919140f06 69
    0x4400c0da42c5d400303820403a07070440c80196120006081c00070301c0051070701007401201d05000050100104903001154080c190b69100c030010082800352000c172441e010618604200580ba01585003046043c091043e0400c01490300d40000c4000039a43c17200b040d0940c01404c3d5165800c100041601d803240060500e4103d00540d004036052035455554950010280c0180341d083d8410b9004002850700594034030802c44002c1261080f080e6170a00c1015201e9108490002e05031000200c0303c1c6a001c810041410640d1007a4000d10108518075030032011201c81800801e42000e146010a092075a000010340c0c252254188502030800d00350080c000c01121a0340c0c0e5616941d690081201207907982c41103170f40e03888250005c100460760001c039000b041ca5100c107010320f1582a020100e400c9038402c542ca8081c05c1000300e4010300c4243c0829948090076001d01c0c041c0241c0d4141000912000b02c05003104912681c0401d180490942c0c0c0d8000124460896040015628001c40d1581d8140b40031115544200c00515 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 260261798 1250 260260548 260260591
    0xc050405010902070510090602070606060c03020d02061009020904110403030512070207050d06051503031902070807050f090403031104090218010c08160f05070305030405090c07020f010e130f05 85
    0x400d8032202500320b4000c01d4103244206c2c401004103540c0742d01740c0ea2542c0070407669011034418000d900040c00ca40c2e0341d0702e42c0c6040f18140241422400211801190054401d00c41c00b2600348240d0030031740314416801a41d9102403400280106100c1030440701c0701001150002c103164020000d40800050701042100310b0792414422a21801d060203055031103200c02120304080354965110650246c10440140c2a0484000010380345402c0305a41c41d100d26056041220110742c140150001051010000d210107410030001903642c44c40c0481060007118800300083c01e00d07200c1d80003003a143c8001850703680c0e229202c0920002030740c04000c03c0380300152011200201d0703501c10898400c0c480e80000d00141405084a10180c0815000c0416200f06240818074004a07405000060003107200b90000d5030358074030b03000170f1004408004210502c180c5042c425140542c44211480008000900e0108500c2d60140001400c0b071590b01314120095141c5403040d41d130b281061744400d00801c480d450241001040744c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 260263048 1250 260261798 260261801
    0x4051302040602060a020c010f06180b0d0506060118120807120203090924060d020403051228050c0d030b010e040905070918020619080705040605030f0c04080a0c0504050109 76
    0x80c0320b0080181c1c4242c0010300119856170180440310b0b8140c001044021486035544140c0c2d851780c102c0512052501064100c400e503502c00c07640541c0c010356150b0701842c442e8440e0740d01c40703900510180c1444100081009101c0200c42680090700c14050000240031440c104030300943c00440040b500c212502c1211100b00f8000420b0f103d0401004000c20300d6a40c6001649a05204000c0c2050a0402040b5407510540d2030802a100c9007900d00c400503255895828424a407a60b07030029800100c004200d0ba00708107842442400020084156900840d182c8100803210b0b0300c11041200c0690280000c41210180d01d42c0010013a80d00982e2440c0000003c0800c010490740d00500041c0207a00ca09400c101105407038001c01c90401c0202e4229040c14040d40102c0c58a40c0100640140c1900e07032244420020740045030650400440e242003030405003400c40280851002501401c3c000340c2c008001a107000050044901408151b000e60700c00007824130380440d001010b8000e4600c540e060400120710404e55 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 260264298 1250 260263048 260263057
    0x40201260402090a020c1e0c040c0e030d09060f052107020a110306012108090d0f200f091504060b0406030f0b0108040305030709050d080d0c0f0212130905070504051302 74
    0x1a07000341510201f10308880811884422240040d40124260b9112039a160321074804a140152a04940ca82c1108100350406003401a014140b0000300001d116a81c0d0041c0100051119030410a03541c1c0e540640042c00c068a02c40e040754503418013803c00c8100340c0d0200c1c09504091203a1a0361480d4420a400c15440e1402402240803101403d540b0b1040c500c03005000b405480e015452052500c2d03000e40101c0c009024420302500c0007031010070004c0400001c402c4254050788031140049248104400290521442511952243c211720b400f00d84083c841001e40700e0512002002040716940c0d841d001801604603108020100e8501040380038403103101d014002800e00141d541012036640c0e6075041c1d845404c00b600660030010400b0000ca410b86803820400300f034074000c007849074860310034011540950303540d45000c908101d030070300928450517000101d43c070394442c50011075600c40b08480c0103000c91150a034080401c075820041844490360b041401002a81c1c01a0759209440c203168078100d080e0f208 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 260265548 1250 260264298 260264317
    0x14010b0d0c0905120109050706020604020904060915090c0911070f0b18010f05012d090203070e0a26060f0622020c010507081003150203040201260402090a02 69
    0x1045485038000e825404014400c006040c42882e050320741c03000c074040d44130f80c401403c0c4c035039500d581040134030404000e92001404a440104442c0c9010750200790804006040201025102c290620803c01681096203040143c20010414181c0904201d8130b1402240f2030743e03030524a8105a4122540c1d45c80440e440d490700071704039003212035041da9100417482005150b030445040140a0006844080c0a01c50400010340350205195040c81c2d4049250b142c0d04400c1000501c00c0410783c04074a142503208011202d0301200184c6071f80d02e074542074980e582042407040c0c3c000c02e17604001c201341d012008900459600741001c034800380d04069100380c1e207407402e8803030f08444460700e400510f4038544555101c800383c400b1010808000588000c880070f0b604503270b419404d113944800420010a038080c0d0326551200c03a6002c0c5040707040c40c54842e0b000c0014803610845055030004005015a4003641080d600b5400381e8071849459920321960360f021007000d4030200c0c414000c83c0f000c90a81c4800f4001c0c3c603015038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 260266798 1250 260265548 260265569
    0x705040302010e0d06090b041202070902071203090c091409070b0a020604060b13050108030307080c09010c0204090c0e01080a0b0a0c0f0e12030d0b031002070b2202090a0b01031401 79
    0x42c0300400c180503807002c0084440d51b4070f8050704c000150f4060035803400380e44140071440310b070885488082d0528907150000410544103004150104031803a049030714009850030001900c070320a007030040b06104982c022076502420040e1300c0702c0c2c41d5481d100052154041c0400c1c2c4a4841e1125038108035803003905840c1c0d0059100c01c0c003140200301c0940c0410b10162008054200c1c000c4aa01c0a40030384100b6444480aa0000320070401c60365001008241d0000d846130403145052503150028104004452021f402581d40b803903201c0802c1803104107140130f442e08a0284000d036075120892540c4050400d0111065920b40c00031a0755000d80c1c1c080ca09010a00da00c0b0414031a206190072200081c222414651004101801c00018101800104640e00313076500c020501c12040c4091501e00904518646412841040264017280104551030307048003030171079002407000a05035084540041d284020390300c81e03200010301940c0101d9a101100c00702c0b0a03203051001b0301c001100341c1c8103e1002d02c01c083e22035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 260268048 1250 260266798 260266817
    0x190c080a0c03140a120804110d08030c1c02040b041e05130e10090b16020f120307091e051c03090504020901020f07030b0f16090b090406030f1a070504030201 69
    0x282410394801c1010f85180c00300d820480d2075440b5411044603d5025070086080d0900748402e20966880c10003429034182e41014014140382d59160340792000a1900041403008100c29800b84101e5011420714000500150f448945900c92200513030f0088c454000d81c070325902c1c5080c0d1516041e06145003141c10042149a424501c481054003034031a44484001034011600d121826141c00d106003c0c425000713410030451880c11080c10498840301c4000d010540d4032000200c9801c240000f611220280d82c544255240e49680d50151201d4002e50018681c5c3c0d2401c4405665001c02d13101e0b4042110b004072050300704800503e41c0c010500841c03600c081c1c00900031180c140824102a001841003031010303c116071b43d01c42810303100d40c10204607030422610450b6407010f03c40320390070030020703280c10081c1000c50346080c140ca4800689440e034180b0440c00385040c0840e484e1000c0d0b03921b910003002942c10801e44011441c0a150400c03c0c540c104400300d49454040010698051292040d0f4003640c1e410384499070340c1c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 260269298 1250 260268048 260268053
    0x10f0303030504020a0e1008070b091e060f070302060601030606111911060a05031b0c1e01060b03010e060a060e24090a0305100e120708030a060503190c080a0c03 71
    0x10b800000d00c142c2c0c200000110010702c03c0d100091841c0300310444900c8001d00c81c200f07d111410600b05900180098005001070202c5580300e540e50001800d441b0b00f02a880e0b26040d000c5512800303060a81c5800341d44c00b00d001d0060503000300e41648140001d9808100c42601d4440555401d00b204010140310b034040040c10881e83c121003002c01034180510380709040e1128050009526502c102d58020004a002c0140304800002e8040c0c1d0003500c5070400e5490901c0705507125a41c1c0c1d41d07198460001000820b50440c40c400030b003940081e0141584046481c0c2c0d03503842c0d001c0d041c0412001d84810f80226030020000030306500c20f03450301d2510b01e03004140c03071070048482440c8286600741003840405802c0800980801307580707215402000750310400290080e00988102d4404460300751204081d1074000d06074003001e2115040072283e5090b409400c1c152242c407139045810042040350016900f51086072641e030956080143e220410074403426980d6129a03c0b140c509455070706182e00207107001d50a1009000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 260270548 1250 260269298 260269301
    0xa17040f030810080709020706060e040f02151306080411100f0507080c010606020c0108091b01030903030216110a0816140d0b0109090c080606010c060507020a0506180d08010f030303 80
    0x208502d140408256094880303844c10705091040c1d0103c020158001145010011280620402494031614940e140d107410f803106100c48070602c0c0000d11821901041a000418450a803483d00340040c454854250702d985014260306d40903101a2040e144026684080f85803c45480c0745500300c03130740d44640c5148140c4059902d40c03c03c40c000c41c1c0310441071049091950702442040010302c035590041804421400014014201c05460909036401c002403141801e1349454080030307844020b1800240d0384e44641001c41c000e00903450038040004200300003000303000504142e400d40100440f0002030260751802c42e20340d540043c90040c2e485032110f4408001e810b01d60343e0418100c00300948407000e500170320340e5810706d1400b0076007102c0c1200d940c95003810309012003002c01e14080d082d40d0f0014009400d00c07500290420368501c00040c8400d4541000840c0280301388180c1c0c49003079204003202c03130a0801000049203c009510240c00c2841108002e00c05540308000d2281250601150001c40e681141c60440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 260271798 1250 260270548 260270551
    0x30f1b03150801090c090b03030408030304020d080702101d03010605010c080904140a06030c14010c0228061e08010303080a1517030d050c090109050609040b0d080a17040f0308 77
    0x10104090000b04194280540700341984035800c1e044209043c800c50760122003807920401d009a00a00090001d0b031400001c80790070a8040310401041503061070022018400d04d04002d40215a070a001a541500168080f43c1c031410998281e090003400030a0508036016072080174001003a03908840c011071403203401081d04100290001c110085909a5070002c0642a141c1d0481035a46803410001e2200400f00103020b007007900329025000c1c000380e0008001184840000c2d100700700e0050420b4070054030404284c0e200c1c8824600d403070303c255107120240401c42401c0c00c8003401083c1d402504d03d124400d0b103005068030344c10b464180c10f60316a035804d200204209a140c60f4212030001c0080f60380c10000e10030901c400c8124004594880b008170018054460291561540c1e60060040305aa40e8000341c85005848007664081d403074032400c00000f400792041c4803c00f40c1042e07020703410704c06105209004160782c01c0305807102841e00b4189440340f8040082110094481800244540c0009104041e1306 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 260273048 1250 260271798 260271821
    0x303080411060a17100e0a0203090106050a08070509010911031b090306012606150105070c050415031208071403060102011e060801181208070c060603060b01030f1b03 73
    0xa01201c2000000720756103900504007100814101d042c4840c000b0744a480007940b204202600e0101103162020f120f0081034090040e801694010002a941e540c1c01d5010000603c1d006101c449492355980c135150b10740d842c50181d02e001d0540600041521521400f482c0d41d11525114990710315554140d00c84c1008800c129190038046041103039035069503040207014060203d4400080c0842812500d0b006a02407409c01c9074000d411010801c04007070ba0a0b00c000da0020740c2820a1540c4580c1480c0041e0401c103c1d4000c070b40d001d407515040304240210800c0d544140c03881645805090001c07000256a0000104d074030800080406004403000802200510380000040c000031401a441640c8500c01809440900180c656102401c001a0109002c0c40c2c44c10517150500030290002038540c00c3d1502c007003010700e00500c10120003045000c0e00c2045603800b490707080042044181d85130710385200076049005606001904081c45c82002800c98803c05242c41020b0152a03251161100145d01800190112 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 260274298 1250 260273048 260273063
    0x1107020d020604150504091803080708100b040905160206100524120603070f05030c060304050c0d052b051b10020705010621020603190207080c0a0b0703110403030804 73
    0x80300314a1084120802c40d00e510b6017606d5030b00b03041503601241c8510041d030702d440c0752801d91a4040317a0840079994000140780303040300c4541e5410945601030a41070f48a881141030004000407010f00790740c00b09002d8400c040e02d4180385804c0c01000c985d14072055031641c1102410400c1009140303071910803045003820b0020303500d5500291400183c1d075030304140c80301c0343e10380c5900b01040540e140500c8124007510b445002060403c0c240b802107692440c0c1080c12901074040080032405004040061004201c802485030101c554603141894489200c55460542040c0c0001d081102c524050310030010b9014540d0351500b800c03030340710380c0c10403034079403644501c03c81d0040040c001f0a65842d400103000d603900500002c15078600c0c003c1c0d00c480744e0740000c1da40c8007002844500100160303a003004480d041031044400d4001240038400120081c0f05025004011000c00590741d1107a040124262040318040d01d0103c5c00c0d03030340394201a070540d0f00701c0454400b141c5041206200081c0600c5195030018080c418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 260275548 1250 260274298 260274307
    0x3030e2a091023090c090f030304120201081816090c03050c0306010f0903060c0917010209010e0904061e05010905090c0307051003020708030f0402030715020a030c020102030903011a03101107020d0206 88
    0x10038202c0c0030507a616030365000002441e1507a4100a0791022003201f00340c0c02946406e20300000c6442038020858002c5c10001c1c150301160b410126000241c002c0400901516000d00b0b070811030003800102da105611703501f8100200161810700a11819200300340340007003645955104401140d011200208100500c20001c1010000c210130b8030420800c070845841e22005507050162a000611003000043d41a80c010400e9440d240d83c09180900d030f985041d50569002d80700d600e00400a0540343c460300c4c0e90354171001c0e00701d84801c04c2500150704a98451030100329a071202020b064503a08800d5045401d43e2100b40100140d040c450070482c008521460014200a05582e860003241d08c04d42d0702003600340c4c1440910055150074000311000344620035000c44004440103010391101480e070b2713001c2c092003203e0000c0b0302564024401c403500390800500070448505205c5c84128508400c0030b440c2c0c080e2040701800b070242c83c3c052007910107a0310704144040c20f08105078200038103c8680c031412a00800300f0b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 260276798 1250 260275548 260275619
    0x414211005071403090c010c05031902060f130b160302130807030c0b0a2102091002070801060611030f0901020102070f030339030903030e2a0910 64
    0x11582510216880c00400e4a040000b0028880310310482e0110f561501007050198004001500c10444007003801d080c1860822403d19a0660181162684041050010421220750b011030300d24415031f40004d04007541d85502c403009400900d02031009154810300c00219100d18680340100b1000c4d07685160141c81c000c1c000380e4141000c50140c2c80388086510507401030080000d046040700c09003101403216801e10075184002040e17154440150f26200d0542105090704c1c1e5402d40484480c040c4c00340913000c0c5402480c0e0002d641d4050b030310411101d0b51030b082c0042501403281c0c40003060900d40100450070400d41d41031000559001c59080c90542d942044151f0004072540319402c90b542c0a61400035000e508001c1a80005141d15820302076916071812490071540d141d2500000080030b40750010700b0012515058004041850741050340388607249045a004c54286042c000b41101e01c0100c209403000034040c00041c2500790307004c140d000d007000414401c0d20704c0814848180c5804412081c4c8144035003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 260278048 1250 260276798 260276803
    0x503072d03050301090f0b011407020105070f0b180111120603010b0a06020a120905060d02090406031401020703140306011b050304090c0e010e0f030c1e0316030209070203041421 78
    0x1240300300c0109002100410101e40b95201d07100942000c00c10a100b09504000028030f01c142c010341f40c04030400081482400d40e4401e0781501d05040e4018021010b100e42c0742405181c41c0411540b10404081d03150400d9000d41d0107010b0180b40e0000c51550074108650031044008072000107200780e8141d940c0f8806809203a454a0032030001342034540180409a401d4101080800c003044505800d1200340041040b0686614084a2110502180058686014500090290495a2019007034107060b400c070843c50441076008202d2248251201d8840d800305c8000b03025180022168240030031031510303561041d002c445817000b04651007801541c0c40d0581b83c001c602c0480b0349201d08400065187c5500291030350704034210f03c1186808442d24541ca412620019540d150390440003801401c4550001d2030085000682c0403d404004003034611107400c43d450013110b500148016882118410f0100d020980080f0440e010b480c0110308140b008040203007800b0921110a605072002e040102006900d55001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 260279298 1250 260278048 260278133
    0x7090b18040602070209150306010302040e0102190e01110c090f040203030d0212070e061303110102160905070212070b070c0f02060307090e0a0608030d0b01020313030c030c12050307 80
    0x20b040040c1c85010700d0040c0095240c005090004036844031000e88200e55002400504407681160041259005002018068010820b0308003200ca41011100c0855030000481d041000084c2e851800c1040c59449040da1042c010510740d40100f84800418803503114000c03900e5009002a08403890b1200e481440d1040f07920013a4004e40c500d0300741c018003941e10740c803a40100d0703440c10803100b031070400c2150304070341c0000b00503484000c2010b15501c2c0140201e900034441d00d6031541110a0040c0c0c06079a0300c80364406000100c4968005006902c0e40c90b04420140007941e1030560440302c01d0429964080c4250340100309410140c880e2001e0100e1140180c0d80e00d0020362117403000da501c005103e882c0c010600c005000c090a111901c80c101a000d0020350b400100303941c41d1414845001c02c01c0120304006074118842c0110b01c01501c0340d1540b0100a0010040320071040f28400c9600d81511599210084200100318400500a410170803112021410040c190014030400c000444084035262103250410707600d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 260280548 1250 260279298 260279303
    0x1103010b030609071106061323040c08060702071406070209180c040e150c0d020a110616211104081e03070507060c05070306140a0e07050307090b1804 66
    0xc00104205481c14919901c0da0091441c0c2440c204803614801800c0d00c60303000814460140003c0b008402540003981c11000000210130b1051680081c00050210307100300407142641e40d074108100c005556070001600b184981265805010824244581800ea9600b9040c80c0e60f0b01600038486403015035644544036020308000301c4040c124a0f03c1420312400c2070090103d85203c1c91401c80c08035400d132000303d81071640307a90014860b251030ba110244e40f5440d000d0200b44248075880410380500203500300907143c00c80c1240200321000d540e64880ba1000142c81ea15a8000146500340e01c01c1d81c01c0d03808919072031015404080810080d03402c1c0307811811a00b007507001040c40d601ca5403004c1c0e01d00454940b01001c0380565000355143c00d108c3c1d1141d541e907848520540d004c00c100202c2d58400d002d8103114580c095580706000340030150f000206080d04040680e103403031b02c091a29640c0c03072215100245d1035003100d40103005070206d04c3c81c0c402d02030014140010075607000080700321650165000c50361031038030952 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 260281798 1250 260280548 260280569
    0xb28030201081801061413060608280c020303250507080a0509100522030503030103260d090c05041a221803030e03070c0504020313051b100201180204020706110301 72
    0xb180f1b58100090114a00543c03805989000030500a650340500500d034000142c0c0e000d242d8034000c4040c600070900c2c1c2e200300c40001a18040c035003842c440d4044021400f400e039200c030307504403800b6280c3d5848040300d14060707040c04603108100c0e000000b80c2c01c070091300b500400c2c0e003001401c019296001c10041c00140031040c00003400010403200920b046102507000a0100c40080b14403400c541e1919540d100c18080900101050080034100c0c10382500308044141f07106e840c0603195040342e05c4031401f42c003100104445034055000c0c0811542410711a41c1c070b110360800c00c0104102c0080c01400340b0b10040b0146850040b8101c0e00e400880c078501d002d20f40070380301c0100b03030300d4151030700c50a0080464400400102040e00101301450125074006a00401e40748203c40040c3d480d214112910300c41c10b4803400007030250240400960070300c20040070700302d0207080982d0b00d40100c04103004106d08807982e00c0030075550b1050307240003030300941010f074003405240e481000b00040440d200c40c0780c5d081c01c1c3c0090b803024200c3c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 260283048 1250 260281798 260281829
    0x1090308120a05010614070605060307050a08010c0305010506070b130311010c1d0301090305040b13150201020c010b10141c0513110103090c030201030902130c02010b2803020108180106 81
    0x80b68248601d034010420b9192041c1c2030301003480b800c000746c4500d1902130075841d00c940219900d9a002d22910004190007041070907004d0392502514003030f11184503000b011918003400003883e8200301d404c40c0c48a99000e111804160f917482048007448400c00c1d0240c0400041c00c0d0f6203440d42c4801d1203158800c81858840318441c0d0a000981010140d0007100a8061b904107540580029080f01c2602d0545405507281038481445040c01084440d903a4031284003588203880450400350107500622080003000020b10204251500348581d400510030a03000151040c00a030211011070000b8101c07030511822140700240e00513110000b41e400c240e402210442400600500b0003400c0c65201160810a080c2806440308984580807040003610010b4181a01c0d405c801c0c1c1155190f000e95007405224440130404a166640c1c000e0003000210300481c0a8013441081c2c0e8640d550580b07044045200d440f110310800e9045030300450b041803014012007601d039401c4403042d2000b0f00a0080303c0c0a0312401c1400041d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 260284298 1250 260283048 260283061
    0x10b040c0207090e0304080303190f0204090501030b0a0536060a06150908031c0905010c030515030303010312030b01023f1204030518130906050117030304110109030812 74
    0x440d2101c4d507084242c1d41c0104420001104048145d84e4484400c0b12881c1641c1e0428942401809549001d12071192000601142041103580a01d060b00d010385088442d42d0707200300c440c0382190340940c0c87d60490700310503500c6845c040558604041342444c5624a40c0e0f0b140010311424648441540c20b000b8a0b80c90341028018080342c200898480340d454600010303130f180b808046584038800e50038895104c2000c4600c0b140c11003420b0300703c0350145901200800c0701a00043d0002c0042c13006548078001000716141068861400205880c10390350807001d2015860010754040e03006080c09558181580286001000c0c1000312503140c41024403da80c105100200c0510340300f0080814a01d04601158240440340c2c0000100b107070a5841585401c0c107a03a5490314601c4040e00c420110315041d03204008000300090751840b90072100883c1d00c245414425039803207020f102101c46850622001a46c018000070b4041201d980c0f000443d220181020140dc586035200c8144a038006e01060b82140305200501c40c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 260285548 1250 260284298 260284301
    0xe060f07170c0c010212040e0601050c0d0810080a1703150d0311100606170402120d020c100e010f0c0c0e090c0a0504050108100207061103160f1412040302010b040c020709 75
    0x3c45100901c0500b9048505503c40340e0b00340070300e000350328900390f513a40020b013203901600c22902042d0b003a4080307802c0488241c00007007040d40d08031005c044403000c140c40012205000100d1080182c4c2c801c900d290144902c411003412504001c10191804d07103280c0224001c1e03118005030311a40390091369a1038040140c1c4407440c0c42d01c1d940040c503805c0c0b28606503081004e0756001d880030060600380340c0c0c1011640c850b0f00018040b080545c3c41c030502d500800c604a40c2c042d4000540b003408000a031400d042940c080c00081c3c81071880c803481c86020440e00415100f006108180041c03002d0b100b6910041c40e50b071652151030120004448044055121003140b00d243c0c80c210302080c0041004580911056040401458075801c518a081e2030040e0085415000c1003415003049211071100c400c1c854613490701e0100340510301526410310011036241800c44143c540b152400e10408681d0400b0305103004c81112a000002c40b00900c00d03130441d50780e5106040c0e90b0b603450146580140d80b990041200c103003004035000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 260286798 1250 260285548 260285563
    0x1e27070e0c090d020907110105161404030c29070f1a01080c010302091311070c0905060d020f060d060902030a060605030f040201050304050a0c03060f1b0e060f07170c 73
    0x401c0090500424000360349449000309110b0b816113501c0e4003a25500001c2d00c1c0314110110141695091208000042d00c1544801d003840c201d44d0b4429101e880c048180390701d54411400060100804e502090081d80c40000c5428a0b400240464010007071710100318052070703000900203c80c486088924082030202c00000c1c0e00c080007841c5030f000225407424200e00d554500c10401030303042c50b40104410410340d8880d03c0e0902d01003c0740c070b01403210b415903100b40c0445510000701241d6a5500c50808281c040541c442e0301e02c10b41c009401024106615020404048280c8a006512040800490b55a80d101d40140c80051807150380160301c0c4d0820080800603078a081d0414404c001043c005c1064a000d42c46d1035980298082c240541d0781d88460501d50b090420300c1d0300c0542911a44a000810824aa40410820000082c080000b06100409540ca10b09003103000400942c4680b086655494040c0060540c0e414108415150900d9641c445500348448100100022004601c1c0388003600d0500c4040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 260288048 1250 260286798 260286811
    0x1e06010c0c24050a17130605090a030305090304083c0d0311070803010504150302030d02241303030c020f0f010b040b0103111b0304032102070501081e27070e 69
    0x75414071304901c0000f002e4405c4540340b0a070f940100c40120b101c40490380c00710f16006410400500c12882c00005003544c5810f880800c8001a20740f0001945c0c9442c00b02c1524181d17040e51006d030480781581d40c40d42c400c8602d1048c54070250820340f13600e5045880d05081910b84404040c01500d81310341030900c050308482140300f29514401c1c0800c1002c00140c450743c200c07415904112030000382015000c000014044803504025003602c101c090641160f1b80000304010342c07a030301c0c0c02c09403c0c244c00390494003403014054800c48200140040710b5030000340640c210211025561049801c40d43d2080f042e585400c1c01640412542c0e50b40b011030340385d14101030150031450380c001e00f03040c0209007042c242e2591900c04c5e012140000265404550450102401110011740d000030b488000744c61800b003059440c0070801c18043c05807084100000301940584215441008000b0003441c80000580c00e04002140040c901c244021100702c001c0c3c02049000403400751044000c000300034081c20145031220110018104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 260289298 1250 260288048 260288057
    0x110d0f0c0e101b050c150d0b0d03050909190510050a1706240d0b090c0d0b130c0503030408010c0f0219020f011709010b181e06010c0c24 60
    0x44180c0743e40012221000003c41c9254020000e140d00304541014803c3d074940b0780c402c001000d000000101880501200328101e201088444110b1041007070880749894005d000c540300f0f01807029185001d151043d0f1040d81c40840170b00c05e0f480c0406aa04950044a019001100b0a0340070300c40350038485541000340c051401d08000c1c41c120446801e0751b0b12401880c4114000d140d041c1e604a10048019500440c10702601b020102c1c100b0f03103880c450400d02290b008045118200c01e0000038031301840305401054001203a801c20b501c604030310540400d4071a0098896049500b4006601c1e1001c000800042017401c000055102002800030311070480b144802d021548641c00415194175442c6600140580c11074141808100410045c0c2d5111a00d07040e49100b0f04050080061000d0306400501c510b1004550b095200443c42c182100741100c00d4801c0f0410b02407a1140441e0403000300000c540090050400500c407801d5a501d18010815682113140001128100031410714100910903a80b01c08a050 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 260290548 1250 260289298 260289319
    0x6070f17010f08150615070507080601080105150409020108070e060432150a0c03030b030303040501090c06050a09120204020715020a080c0f03070e121005040209070c15110d0f0c0e 79
    0x240200700850700c40306e889000019540100101042941300800206050f075440350b1751442c400b40200f50440c1e00f0100d00b51000c40d04841440c19200b090507243d0705031074805907a04c0e501400ca441104051701c184e001002000082020394203c1c40381400504060385c114454022030002810007901a24258040c9a0410303101c11400f0760a0240c40a41c0041c0c80d1202d08a4810b0904401400d001c102c81070301070000000740720610806401188219008860303544a950f5240c034210b4041c81010300c40000210f041200384003019190a41c00143c600040c0050706000c513949401c103555034a00c1d080e84180d41d0025441341050781044207551b10000d1800c6060809061042c00481c0b440700030070f54010451004005151a55050150b0300c82d17801e10000c81d840c882c04612070740700805059070103a2180c010400084c0103036100701a030a1402ea0300006614401c016145400e0160400031800001e81209101c25070008039039100307a100c4240c42004c0400d09829195010741408100580c05025894066 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 260291798 1250 260290548 260290561
    0xb0d0f120302040509010305060a140c0a03021803030a08010f0501020c01080a1542050a0f032a03050603060c190e03160f0f0806070f17010f0815 64
    0x1981500503810a1030000a2089034504400a21507034014590001040e4008824006d00051032481040c03440801c00c1140308400c688440c81c142282d00410341d5208000c100c44080c4030f900580781415407466080280284200060300f99000510000c000402c940010002290800908401041c00380068511048c2c0e400c0000c006c40001071115170441c0e29510214000c2c2c110741030940041c139400516a4003011206d801030905403803a805004c80901010351b0840407180100e0134113000215451f0f0704c2c64200c0031082610075030750f60740c0301c003040c10341c1c07995801400202e4080c0d0b0241d00c1440c0389101186034070040082c00b101d401500f0709010b0b074400c5c0c042121140464081f2540c1918100740550200100036080300d0720505010b4a0350507000f240f9003400001c07014800700c0181c8944e0f40074440602d803100c0d0415000e841c0382c4900b210b960710800c040b4080902624848004041625120101155031202a000404207901568001080280030400340d10103000d80c0004d5200602008620705010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 260293048 1250 260291798 260291813
    0x501050c0a060606183809151c0e03030106141b1005010b090f060c03040b0f040303020607020a0f030315050d0f0227041509050d0314010b0a210e0714040b0d 69
    0x942491b90003c050700540d250003c2e55068802c0c0c80c00051a2404030722183c000c2d0b5502e5080303500b041404510799901d90501c1c0303440d4090404e61034450001181141c1c0f911904030303444544114003c0c4071a004000f0358801d8010300086006401c1c80c00300a0502c2e0110321322500480c1e105910030309006205010402e000da44100802e2100e07042291840d407a0b00b80034139514150301c910342c40411f91000001e080e0300c080c3c4a40018004881c025000d0701d28035a04d03288140e840d403607695802480c033400508441c001034041c0e444420105800d107445401182c0741c0c8007007824502009415a0041000c1c0011021131810780c11700d204a262402d03a5424240f074009118105840160004104500300c05440d100c0b0070555108112142d04402100c060429001020f0010414031500d084c0402c0f42c18008a0445101e60071907010421540d0750301141c90080000220344004074894044017900c0f450742e01c6081d1410002d00026020314203080c61103040b910304110072918000c8005024000c2c403500342c004508031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 260294298 1250 260293048 260293109
    0xf050904060b010e030a031707030b0913030309020a03060e011a010c15090204020304150f0b010504060c0c090509010b040b030d08072a060504031106060a0501050c0a06060618 77
    0x7034000c10001080401030f00c20058140c600d41d05481042007220500d0b91003940c000d921260802910034640381c00c60202c00b0380d01280e100c6c0350441c10300c40114829038041c260302010107005e454009805d00b403607400902d0a52241e44180e640b81e4a4500c44400c2c0031003881112070440c8003000c2c418046880c07030000303008444803100160141e1500307920400034800b541c0004c8041580100110350307900d41440e00d940c4001e00140c0a902c0c1d0351800e1a010581c0001d03101e0101c0010050f1a1607080c18078182044038030f41c400040c101c901c22a00000000d18120b01d0040314041c40040002041d07a4440c0760a2004484c08070b03110706d10179407040710010302c02a00500340c0ba8020b060317440e245e0800c811001503234000201d405100c0301688100d9a5010038005d041e80814002c61181d0b40e0048445a00159990740301001c0d00c00c180d014004820400a560180d0000c0c60750492a0701907420441c000c0e15101d044641c0c591201020a120300c07070312500c001c1c01c00c0030b00340944050440e00c2d47c0c40c2c0d182100384050243c0d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 260295548 1250 260294298 260294303
    0x5070831030311071b080706080c030402040b12060106180b0d0c09080a05070905070e150c1609140705071104020904060308031f090e210c06070c0201090f050904 71
    0x450600c1030620a8001c0c0343c604101000841ea02d09440c07800d80b0f1081c00703c0129600303000c402c41001c140104d01141000403201507607280f402585808120004a0340090812640583d0359590320703c50340c46607039070101d00d0b5607040080d141c550b1405401410f1501120102183c454041000740000c80d21801078440103140c0407800501140180400c0e24400300030f8000c225184940c88080d4108180081c1032019101b03d035000748203545803854260342684040304091380c001c61407400c040c5014048005450108070742030171590500340b03a01880d00764125030341040d04015115000070154070000c41040d504031403030f45015450002251196000c490900c80c40321700c02c90b0001049015552a5045403000d183c105900554a0a100c038480c400208001c8140e0020001030ba000100580f10384a5200c21100440182c0002d49005101003400040040c0c0142d08945c01e00072540007400030441240b05201e981c656030851032040c0005020b000c040e502120007901c485405000daa00c6607504150800d0303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 260296798 1250 260295548 260295631
    0x301060e0a020c07080a0b07020709020c3c030408060610080a05100302060a0f03050703020c0a2306040c140d0309060f0903050f2404020a0e091002030109050708 71
    0xb1aa0a20a130402034a035200b01d41c01c0c410040b252043c0184444558007031081d540071551402c0d5a0070002d030580c06810701b0707800aa007202030380a103a45504044800b0000e07407400d040c0003009105c00981c00704001c04040d0344140d44081018401c4d0310b020052540c008008444805c2c0403a022500180f134102c2c028038540110341c0b180080343c040c95500213054040d540c010030550321034111003401070804244a41e034600003130404000c01d100714000d03c201d60504010101a120088440e00c0c0c00340c10070790790a0020741260701d4500c0002108424070040d40543c3c880c1294101d9a45020000024001060211031042042c02d104c2c000113501310907082c0072a1114201000e81903c20f603815148030400303500c050014040c1c05550010a40d01244032090050b81c4280844944074401d203a0b02d01d00c1007220f0081d002903219030103201807485546c469601c050700e0820ce4007140c4964101c141a40c0082e480007030820b8883e01031000f00c0ba041620703160b021303281c400c41c228407182d070702c012000c4154407002600902c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 260298048 1250 260296798 260296807
    0x20a170c041a0c0105070f0305150a060f02070306185f06070f03050f1f08190b0603030c07050105032208190206152e0903020a050301060e0a02 63
    0x1030014509440070b2203c1c14000b04803e10780b8100181032042d440302c0b0b050000e8580381c0001c0740d0490ba030400d0001c0200c050962000079040c0042a60040002d001c40d100750f106080b00000000d0041c0200c00c880c0c54080b1444010200c4e600d4254541020202c0d10b559180702004c10813050b03840f101000d00034900003904c0300031100d00401403c40c210312001c45041900440b050714400d0460024406024081680e00c01c2d00d420b5080c80110104c90703040d140070765110008404034105001202d0f48002d194120b0011004582d030f030300d40c4280341020030340005a60040342e58400341803003140d50700158054800e4015500e0540030070a0b003031b100c00c1103000e02d506000010020810116081d5404105c03450f4501d07003d02840b225041c80283c0d6000103d02c181903071030803004c0b04146440403030312600441080842c90f4005044400300040001422140790755004841d4030055036a00203100a42c5868982c0c84480c03050342180107000310418250400c0d0b00982c10844104070400c4000b868a81c0120b5400740144c98 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 260299298 1250 260298048 260298089
    0x816050108160c03140d15060c081617031905010b0903150c1608090f030109020306010e07050708030117010608190809060f030115030608060f0a02072103020a170c04 73
    0x40c15400d11210344804003258100d42e46c2d0041e440588413020500a44c07031300c070b07688440842d0103c5007000000e1100c1e0007031107140f07845584c00558226582c40740c0d01d0005122840c0221240365001210306511107034507041003842c680c1d1944511405044096009881e0521007000710340d4540703400361007010001d003207030001c1c43d04001002500d0300e61442c030b40e007040700064031f040c1403030980c001c04040c6201d0244481c5044c942e190500c249148964094050300c1261b10700b20049030510802841c1c01c081c403001308042000101c1c004015806061800102020101696002402c44110b500b102146a2140c40c95181c04001000d0404103598020031242c0d4601910020401c0c0c0c0c011040c40025a420110000c138800384d001c9440040418243c1d010414107986500b080d640d0309086e615194038025410200e8104a00d070380007000c0040c0140720b100000040d0b0300d84c4151040038550701900080d80401c0c45486107920400307400d624800600610060305050b04076115070322035845440c031840820820100c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 260300548 1250 260299298 260299307
    0x1020307200f04062304141603150e1503010e121606050103050a02090c031608090a0c0807091d120c0709020703031b020d0c0303180c0816050108160c03 67
    0x103642c0500180541543e0b0011070540d070311840401d00041806101450300c03800d151061900203080c01715504100d860309481066102c2074581c4040815071195200d021b1245405c0f0704000500e4058402c82c181d00d0130000d04044030b00d022240500c81c0c0d0600d03152044041001908419051482060582e2603005810031007010116500003000282003100000074030802092400c00c40d0700036110f1101541c2c40e40c10404003071004407092013003050781c0b8022030b424034455044550b202c0b680508403011982a511103110342029075001d801035a21000703050002aa49004020030510f1084040c141410181580e948602d81409a101200c2c80454880c0d401d0808000721001041780f801e0455603400f80b0304008000c5d00345100c804050001003003862404620004460b5080c074440d079190f10600002d650120b024060780e000a00301110301c8154000800c41841a01009140382401444181e544000c1c8084001890384202e05006860080204e0342c0004140381d0340b0124149020200414280390544 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 260301798 1250 260300548 260300569
    0x80310060c0b01090c11010608032503020d0e010306050306040b1902070f0206032a09031203070503070305091f09021c050703060509030d020406120b03070b0f0f09061c0501050102030720 82
    0x2c6c180d07003001c00006914001100070180301d5009050400d02036201c42d428021015110701c010b006a10600e121007000f441501002c010743d50524011030999541d50020b0701d0850144e6090b59100e03251002e0000e04449003c880110310b16400096041810b1621a0005004c0c40f40300a80a01340000028581200c40c1242200c1000e040900d404c6032042d4140e03032003032034106105e81030007841440e4152000001040503079104240541d10302c0d18550b29001c040700074280c060503500d194070030303542c0942a08807a0700f000a141e00244200150340d0040b4010040f180518600116270101261262008202d001c0381581c00e50740c10031070205064489012643c9144174014504e43d420f0700c08180801c10759808401da0602c03620148080c850903d0420402da220025880f6566034110b003000074503550002000a81a20a5840c800c241004850313000b0880d0365000c0315003580390100800200c03004080d14850f443c0504030a100860820009644e0140c07281001c0c160520001c1041051038690b580c1d090110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 260303048 1250 260301798 260301827
    0x4051012051203040327180b121b13020405030613032d0810051e060904020d020405150a0503270706020d0e0306060f0904031704080310060c0b01090c 66
    0x958130714060030014500f0198000c0540128405003c03642c001c0c98902a400c16185071180900c04140e048845d5802851000c0015400400c280b180c0c610903041032000d0842040303041d070a00300b455242002c10071907036407290140c1080c910500040c0410b80340003852035440754000e14903e1341c00c003040c2000d8550401e4041030003074050044222000760768074441c13021407415171519180742d99101c0c20b10200c0c010403a0f0169a0304203200300d044111450700034421001c0400c000d0000c52a014100c130229082c1d91018041e85a140d8000900300101c2c00c0c8008010141207040c06940d09054264100904500c400b0340300c00f4103035240c50350403100e0340224190110010304800448030410764565000c3d44a54000216101150110460b81014100403d01600c120401002004031074403d0b400c0155055020700190200820144d4440a01c100c0d084098081c9020b44140b0b0380340d1621701510141c07000c207030b0062000c11411900c2400002d0101035100d054500d8400041070341040f41c003045a200742031300c80e81c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 260304298 1250 260303048 260303083
    0xf0813030c060e03030a0f0503070c0803010e18030418021308030c010e010e01060b0417160b12070507020d140c0409060e0d0f051b01110705010c020c0405101205 71
    0x10801c05400c81d50032202142c840f4000345001d0010140c50340203a015400c003180c00008805130f9240310f00c00450303200441c0d0401e481358400a803901901034100b60000d0400d0700d40601444407171441e88000041000880006518181c00d0002c508050046080c6200c081c0f50049940e10f10f011040703a5000c058050700c0101ca41fa07211243c60680640fa4484104015510b04412481c80c0e44060003918142c0c0c1820504030b00c1c1a10703120010110034507450040d00d1a00a44101d0b60300300c2c8100700b000b00180f600c0c100c03040d140c5504404408172200043c0c002014040200b08100040c0c844014800d4000e07003102e0700082001110f04aa418808450021541b0501d445400340030011550700140030007540e0400c0300c108040c60241540c1001e0003100003008188144183d60340c901304500d203440c1a84024001080c0302802c0000066140c1001c4805c94050b5141c403006242e899040180caa800341e800c450078041400c1420305094000c410303000350302c94044060080b50611004110501d08180001403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 260305548 1250 260304298 260304337
    0x9120e031005130c0b09010e0d0206070c06080106090f15110a0602030711010509010216140f0d03020a121512030306030807051c17060f01020a05060c0c010c03060b070f08 75
    0x3c2c0030590110710341101c82c0200c02d000411126140010303109170650684400c10303035254070b10802c12020030004040707a100c20100302160001e004482ca10000b850b0544450f0740c59418980042c003400b445402c440380d020041501081940d601454403c01c1c0000c505101e40402003d100d801c2c01e000401074054507060000050003031299000b800c0b54a05151400200083d844041846090b4420580c1554072240c80c2002640490b0301050b0032000e1011180407203144030400798405d41043e2010b00e0300800703e0b40c003050103140150003010300c61500e00f00c442c04011042c3d049956552a4000d80a0400c244207884044010940240e004c4005142c01c102a9500d9151610b80a503070b07030710445d41170090408039030f41d1140aa40200041504030748624600788003503844c070042c04044c201819031903045101d0940c1e0305004c075600380030150050b50318600c00c030b80d155056400282581e0120648808140c078042080100160210541d02010307072140d01c40042c020340c1e0a0250b031500404280e41e801030717a51107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 260306798 1250 260305548 260305561
    0xf161706012d0207050904021503090f010612020a06030e0703080a0e120123010e2a0304050a05010506030d050d180c0605090310060503210d14100909120e031005 71
    0x1040300b030124281c2d600300c414240d140c0e800d204044d501550300940001070816001b00d5000b0140c050760b0301800842c02c56804030580300b0098250351041e030005403000c4141d4200d10540c10080d01c890084c03c1c103820140070440807004025a100600e22024114502c0802c102074a103215080e5000e051500400752407000c5d82550480e80208000b242848504400342c007035000c6200c0c6c03040c1d064100c0b085448510302d15581d001000c5403c400d01d0950f0441030f41c101c0c1c0c21581e4480c00001231030003140140020b10740d0a4140c03811500316500a00301620a5000489490b00c1c2640841100d240816204005c02e00700d42115442096003900320001380002c68621000ca112603020015004400048046a417840307804a01c220484115000d902d41541081160843c0c003444040c80780d418190601d2090b2400702508002c1d000c0300d4503045544c8042c0010018041c202002100c0400604580c1000b04594155591041307094920100130701c0034003410500385007050350244200040810482424001480c202d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 260308048 1250 260306798 260306867
    0x20a021e0a140a15090311130501091d0c03101d06010806040506010f03020d120c08131409160c050c0306070801080d170105040906020706140f16170601 67
    0x400301c0b10f00480000400003002c40c007101c82a10003000580b1043c00d40d0741161502084102c0028003560805c82084ca400c0c4a80c0d01807045900902c5524000107842e07001400c884030b1921221003121180d4421040403c036503030301040c0c0c01c0181c1012100000c40c0096007610316990700c020903951840d070243c04000203411b0b0001c02d19611032803160080e0703151a0380b108031020b94410035000c00380d00107515000c0e41000901c2c011110340000001d04041205403115541e2020550040c011998000c103201410414400200e42501301c2c0740c0c08544d110316a180140c1c0b28201c1c2d01980601c0020410602100c105101007800a91135181001d003c0e40e14516289402801c2221301313105030b2030544161203411695920422035010148401c07880c1005a03403034001004080c10b00c031403080d40c5c01039080100300c2c001441840341320215408500d400c405443d1500e0090b003444002003060011a0501c00c800781c0c215840200008402e4000c107032444a9140c0c1e40040f503100c44540e85001c1603c0030105c11030181c0002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 260309298 1250 260308048 260308079
    0xa080f030405060a05151e19060311070b0a090206301303020d080702190501050405160806070f051c0905060711060f0a0b100801061e020a021e0a 64
    0x2c0342140e200791562030030081112011110301078101c180200e03102d03003031410001c80c580b40c550150000c0c018a10320000602c0034a13000f800d400e4040c8855501300200c903014028070035038200c411135140c01c4c402e1948400d6401f0400505d5908500d54824545085650b88030645865050000d0407030f01091044183d180107c040c000040001072280c2d0000380311100200790301240d00da15601601410654044c103803119103001c0c01950560081d048445050b018440c40c010115000b80c0002c90203003000d00b4640c2c02c2c00112480c4a0014401242c02d1092250001e0320581280756460500402d0032451011121401642d001282e0501e200942503546115900701c0c00026005030250b803c141c82d2108140ca60001c1803840c403089401080010300741c0060584003030f9104c02065404030750100b51000169010304020414804900c802006003c0c490744141c02203607002d50110128200000a600a903440c0260800248503c00418480301c0700c501682642059840c0504a6080103444554103041e10b0103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 260310548 1250 260309298 260309303
    0x30e0a0906051f140d02030f010915060c030201020906031518060d02010c020a030609240b0a030213090b090a0312150b0d0219050714011505040e0a080f0304 69
    0x8402000c661031010344034040848200400300140a08002e5122101000340c070100814070000c80c04c04c3c1c020303016010080069a14100005030399151803114110000c2d01a00410a03092810307000180041f208019442a07500a05002c0040c1000b403500301d000e80308644c440342e0400300c080140010800b04501e00ca124003411601c0580080712000740700140101104c0c1b482d80208950100001340d405004c0206100c0d001900941d00540c803601d5840a031240c1d501d04840703030102985800400a130310500410381d40022030040c0300072620840019a5603c507800040d01c24510002944100000c540c0081c40c0e8035072062181e40e039440c2c83e020301d0351903088090007507000c1404d04040c030300e01c291244904901c080822045900403410120444040e40004400442940e420011505402c03400f541021320302c2010b54800c0e03903601c0d043c40c240b90f051020380040172290b810101c04403c5d8001e0821968255007041c0e0300043d83c0c518984c0103d1800c200c00304090402c2100050132925111a000110312807070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 260311798 1250 260310548 260310559
    0x10b0d0f05010b01020109020108130201090504140907061b03110c040e01240e0a020c1509061509100509061912020103051303090918121e020c1509030a0f030e 70
    0x12103e070016400d8504d1950024000740c0714a000420310b04a8070201c1c40740a006161409611b0340710382c0828200e441109001030030310040c0d010441d03441d2003003000d139000d1301c85898081c140b5400701d044100c075000d0074503004013805002e01101009200030083e64100b0080280309008104411240314000c12004841544603004401c0510058528080203804c840c0700d50742d100800d603129070401d0003c0d0480300030301289020b07519209215480d5480038902408030100540083e08002c12071464100c480200d0031b010f401c5690802810049454900c0c04640054070a9504ad80d54000000d004080341604065100f1030140007041c1101010b403000c50941c800c0c2c07020031031911500e24030822010340c000c1c0100000c000030020710906500d03070849100c094050700c0c0101c00020560b900c80042030040c05000000e9a002603c091096260003640c4140049001812042441402140c0c0e82c0f460030b4082d02c011040041c00301031549041004005c4541c0000d4280e9140004d498000e04040350110031030b00c600b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 260313048 1250 260311798 260311811
    0x240905010b0411040905070302120c0301050103061d04030f050c03040308090a12150b01030605091303031514010c2303030a0f3605100b04060f050102120309010b0d0f0501 75
    0x90410340314000e15025020f050074201841e108484010301380050800c003c16400344030781c0352507044000d68280030340ca0003803c154aa41c10000010211685640510782c0301491403100340d0415440380203290020b805240c01c1c101c2280d44101900c1510804040ba4213a101c000750000500941601a10343d0013404c8443c5240c4030790343c24551445428031078016014100303028060302502c1103079100c8a0f03120418100803904aa4030b90006516000c2145c600d24268003480b603200401d541032152524006110050195003824403c0390300d52440281e000605101502c0c1c048024042c0b0703025400c500b01052009a62020005d014080e101c0c0c00a0f41d0078002141400301251440d00203004030010056017139030f8405107099064883e940b401d149910102404580c800e10404200144501c0008119901011481035151802d20048803042d40c171052154090403070a0004d0303039010499013904d0032010802a1207407a40c81300c4a006000b007004066110b80d0740c41c1b0b00c108000c20660100b001d28090402009003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 260314298 1250 260313048 260313071
    0x1603030e060702031e0c04060e01082e0f020c030d0912030618020304061d1b04020c060705030408130303121103070905010f020a0206070b090d0c08030a050424090501 73
    0x40c1c06402c90080d4590044121003280e403154201c83c14444508400701c4060246800204040701c810b038002c1c1c00100e86000040c0180601000908070f41841002d007850180d8485442210f00c0759040769009404e0740f19030042104a0007030301561403241501c3c2c01d0340e0780c40c0407115520004204c60001200d9500d4100c01c0444542d00a126200448484441c0c601800350b5201e201e5000b903000800403201285e440d20b91101d86600301c4024012010b0035002411880507011149004c0712040c04160320072030040061441062011070010703001300450614548940765850840c032240070b91000001d001010303590010038158440024040181040e60030090604103c0d06e092a0f0301c01103031400d01003000c2400410480d4400d05056111810307920541e407514140b0380c00542c480d0f21403407003610804184428800d20060a10080d00c080c0b0981c00c00c4010303450b0701d42d1420a5404020701550810341e90f41c0005040c4559104960320b50b20a81c0c0101e80115542c1e0403180041801040540300f0790b1910128030381 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 260315548 1250 260314298 260314309
    0x16090e07021902120a060b040b0301020a05070809120a0804030b060607050c0108060301020c0708030c01110301051320040602031b060709091d01060612050601021f020307111603030e 80
    0x20382441e800b400981484050600395090111801c9070007040480c00084011801d01841c411148541c80210b104102d100c00c20080e20103a50900d032180c0d00c100300b030400030341d0000304803144680d101e40d085868030403460016141410f400a04c2c03515028000b000d10411920500520a40e803203800340504584030300040c4070305401a43d5009003142d001b110303036281c070390301a0b05503580c030100040015160041001c030980c103000c0180d010407400c1c2d0001c290500103000a0083c550b004080491240c119890000083c00308040801241445950b03a204000070303081c80d100081d05003c2d140ba40703558496841344000c0d529400207424070000e07040e00d072440440c8480072411900030100c0390748032296903080602c0203008102100602c1c03a44011207910114a04c001e0280000402c056114580f011b2084031004064540081034a41150031010303c09460320f1100c103800801c041d514500584960303500c182512140c3c07001243d1901441078034042c5500240302d0a00f0415280301b560f6171a08128064107011 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 260316798 1250 260315548 260315551
    0x1e0b0403020612150604060c0c0b1e0714030310090f2c01091707020909030307051c15230312070308060a0b07150b09160e061216090e 59
    0x82d80b01c10200802082a2403007400190401041041480c201e42450001480c550056006401140695108030240218060150014440c1c2610a80f5010703140b2601d042d0b5400502500c3c00d403403800b003265814403480e03680c006112a0800d04030782d500d09106074000355007011403041e00d06050415401060013452400707205592403803650003400035040003a00d19101c480060044141d50350340c090302d070082454001200c44051800900f0707590341000d80103107c0042c41c0200241a0340d44104140700e042503204048070b08200904c0b04901c003084c040e480703035406081c04001d85e5031340d0400c454012030007201c14203001560b00c064030f0800c803100c0d048409050321250ba510440c502d028080c000c0c030000c1307401a50303a00d40c8980300910301c41000f9111010004250805042655107103c10040b802d0081d07071030b200c0c15902038412110300c46207107030120b8141000303400114a5020843c408110f80ca1984a2805803840c07401382901085031807074182008100b0343c04400ca0800010042880000c071014552005c6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 260318048 1250 260316798 260316803
    0x20325080105060a122f030f07050708040b0c070503011803050f130e0406150e04320102040b13060f050d051012050c040c141b0a06061e0b0403 63
    0xd5141e0700e490200f188640000603803205004240c0316046400c4554440c0c002d0b5903201494a2480101d07800000320702510700c003000350003114200280000c00c0d50300e407180795200805240c502d030703140203c0c50500c6060003150b2010340400d0010130b2440d8002008108001520000c0d8020842100c1c1101d61004c2552859009404a2010002d04160100803001010420361428290b10001c1d92400c542104c49812a81030350381560318507079080401541100200117060720070081d4407600300b9855524900c1d2a90221807070811141c0507141c001884007090307400d0450200000c6403600c1e9a20848003440d4030181c1130350059170704c0143c041002c2d03009201140c070b03035080755450a00f001d00300000c14004040180c041405091009030015951000c6035016144612a1010b41002c001040502c019142c400c5580018000c10f8084100444060001d0780e20210b6201041c078120103403028900e050841490014043d41d081c508089100d400c038400b40b108040040d0206983c1641d245034006a0340541d0200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 260319298 1250 260318048 260318057
    0x80114060d0603051915150b210117150c0405100c0c09021c05010317071a010b040e1003020a090908121602010b06031303030e03130306020325 63
    0x282585410100080c1840c02005480007a034291252103180c80c3c2980b004d54000b42240998050b0100305084034161520300c106401801000d509100c907148103007113802511244a400b00d4099040802800d510804500c00c151502155846100056403142000700a400740e00c503041d03600260803e00003080f48520503500c9075608090501d0108510b00c0520300b049000c000e003080c04040400c4500b1240b6006103038050005980f41000a410006941c1001145041c50300d00401000450a040142e45514181404003581c814062034030000f055420080302507215900c0002049a440c0350000b0000d480306142c100c2d001c1d0b076461640000540c41408000d412009001c0100641e400b2a0030001849105001ea1800c00d0080f0f6504520208111802c500c40381103007428980c869020701c101050110300362070443c030718504540030f40d10146803070200404144e520104203070001e86c14015241682c1c0d00042d08200280e503070034204081c0d0000c0d20701310381e0132090000440c0e000340003244414280c18036445 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 260320548 1250 260319298 260319329
    0x801030b0414101109010e040b03060613060b07060b0a050904110d08090301090c1e0311061312050c01030513030c12050f0d020d0b060c100504020409121d010801 71
    0x40c1c10040186428920400f8442c90081002260441c05440625201c0340006619412003800040c0708003d001400ca00603458002e00d03c16644020032020340c84001510016069402c1a00b81401000164440111010302103450f500b0488190001050640c044480078426501d441c00c00140780c20541e030040c00c2c00d000408154050602080c0e85800e58081c0c0c0480b41005845804603080d104a410100c40441c40d120080c0100c4580340c240d000e0820040342c2c1860401d003183d960119080344403403420300c00d000105071045845c0030380610f08e02a1802c140c103012090454603083c5da680c2210b1007054003280c10700c03000400600c96030780303104038080d019602d81d0469080c0307480d46108012800031000820404001420900030000300a188020340c4071401a40e441401803400102c4540860390741c4151810018100e0700240007031403804034600c8a100140c2a141c2d0320002d0010400b200008203404200c0c50f07583d820710707001092001451050719500c2800320b0350600460300304000340102d0384403e200c081c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 260321798 1250 260320548 260320553
    0x70b010e06100e0f04060e060102060705040f06030902121e010c14090d020d020613060810050f1201090b04110907031104140d06090804180908070303051e010b0a02010c0801030b04 79
    0x41c04890901c0c0702500f61144e180307409012400703480458001e021180d4240c818440b865070b04121744c560000f103e01e0581e00781400c094050300c0c00000c2e03104880c00c054452100e0030555462800300541e078214901280c0c0c4000e289034045006503108170080c410365107051700d041e030079034011410850003912006d1024509048501040350745001040c00f070360802a44441c040041e15584000c010194080c41031108040c90f040c00204940c00081542c010051580000c01c4991120045000d000c00121a40400c1440c1390354407900610000398081d0403051200c00780014000c07600303c200d620401c01d43c0c280d0041c0c2d66000c4103070255400d12440031784201c0c04100400030f080424540040504004000119202d00e50303e51100342d4949000907119400002010441504292021405c51401800c2804428076503100c41c60507002d01940070301419180c0c00096001494007078ac030402c0302c070400301505241d6160100c0340e5190b000284408095882c210a850303003280a011114100d90384200d804820b9584d0342d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 260323048 1250 260321798 260321807
    0x180e0a200a0f0309050109050109150c020c03070504090312150e010503010b01230c1f0507020d0207030803060a09020703030c02010b06090f0d060b090106030b0306250c03051e070b010e0610 83
    0x101300039a4075558410480000070428014800601c0c00380c028420348681c0820803400b02e0328400025000c3d50b02c4030f03a4090142e1404501c00c1c00712081200d00040311306060506a803c0a01c0c42020164a49481c008a2107003003e080c1d5407054658440014803547c1e240e205050803100541012808070b00060380c442c0d03071915880038000c0341c1b20640c03851506146021030b00c41d10b0704860806d400350f06882d90312004c10040c4a40310746a4004081d00c02001200040d81001c0d45510303031804040c02c0a00b00000266440e00c41c2600381c4000c0002007021540c40f540c9050003401400110b1050f0700650814010400038500081078540c80c1e440100080c0000e807080341084000d400003d8202c81251701c41c1c0c02e8400650b929110517000b44804d49001ca42c000403181003606007a4000c003c581d0015010030781e21b031911503400c4070800303503034075806c0c40c0d90100c100d81410b076118010b0001002104000c10100e404141c0c01c5009060342e14400c581d8040c2c26600c40b900244c071303c082160001d411915903040c50102d580308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 260324298 1250 260323048 260323061
    0xa2705130609150207080306090702010504030503180a0f0f060c02010e07050910030602040807290909090a02041506020c0303041a03040809030111090f09010806010501180e0a200a0f03 81
    0x381550f001d5480c0610030641680c00244042c0d030442c0300032040150904090b41d181c1d80c0400584000c00540c5416034018095000260448017031864110000c001058100a5000400d03006800e60485102500d0324441c0000503410488585060141c141c1c807040c014050a00345203614405401e4250400c814080151401800b00700d52050b1840c000011801e0b9100400c050220071000e0304080e81404400a0b5a0131091054484440c503920700391100c00307146042e10b054a42c02c580703207401620790700082c038075000c00c4030406540b0500d0501e00c160000380020019040310842d03002d80c0c4030841d09908142c1c480c0128032803012a4641e607030a0314003203607a1030007c40e801071107000c5490074240510082070031955031000503001c1c1303c0e00241074022468446046100c49a0440b0051142d40c1030000d880c0c1c90321410301c100b506214002c2c0740e03c032015425420541c0507181b0302c4400d84451030031a07481000781560351021214880120a900d5200c8080811500c4840003a1a03042c00d59400c07201c00c5008000c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 260325548 1250 260324298 260324303
    0x60e01051c06060c020a0e010612020d0b120115080a0507060339031406030c131806060509091c1404032906030a0b160c020a2705130609 60
    0x1112a040241c40107500c203690240903a590742c081803041c544144403600505800442d00c00c8020310042000715072010f080044c85900040260f200e80062110700080c2a140030340340e03880842d010721b0360403a07041584a03010140c100d65440a01543c1ca1240546450070b81101070701c2d5420001003408070328080c0d000146141d40900100e000007071452465071880742c0101400b00c0628503c4d070390141840d850b0051001880c00c2c0010141141000300000f550b13640341e0400c050090128806540303220006520a040c40000c2c2500d8100781c00c05441e01c640140700500842d80304a20010105291210000f901c0901d6140d00142120004040c0c2d0182d03000140031003151114542000b0110002c0c14008440b5144a41d50340444001100301640c0030300308a0042c8114003d900500700c00000c58503600003181c020040d403070700204405d68120100e66203008440080d41100c02104002a400e442c0600c000310600f100703003100343c5c4011036540c2c00d05892b0140d960755280d00e142e112070f90104401e0740c071103103c441c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 260326798 1250 260325548 260325577
    0x402090102070b1201240c020103050601050915030105040f050402030712150e1f020a050409020f0c03130e0705090a031211070b0c0f06010503150901060b07060b010e0a060e0105 78
    0x10369680d00300300958064440305003154503004c01001003110b06a42055102c1101307074a0303100d483c0e18070b07801010505d000c90040d0405440d00d01192641e4052800c51341d113a003024003441d940454569170a08207030f0082c07045038092843c0082d1030100c00d059104480c01140d00a010b0a0a40e192183c0e141140f00d076510280c6140152090000d501c035668410150740009200103058543c800c0001e1444400740c4055240c2031b40d004010b0000100e80c070001b210160b540301f82c40180c4031400c15504c0c42e103c6c0104252084a80b2000840340d050b180c2c0b64102000300c030034180303041e4403039998440308aa89001d241c810b59001040100240005040ca2140000100440c030344452801e156402c02480c2c00b00c03682c020114140000b8038035070880c0301800a00312500781d020040c440d80d4513180c086030340c0f04070302c5c500010700640180100395071200c00c1d000a0300520908080315143c0e45142041c5004000003a203290107d0440c94222000c2d080c0400b0b80d40480c0d106803141e01c2182d007080010344881e4401c841c03030300303024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 260328048 1250 260326798 260326813
    0x30109081e04150c0614070923030a030e09130503030112140723060c1c1e0806040b0f01080105060a020109020405100f0b031302190306051e0109110304020402090102 73
    0x41c0314616200400310540e84c0b03500c2c2c0c200766400c06100302e901c000c0350300110016510400140031b400220150032900d50204030829080031130f07041400c0440c0e4405560703141c0215180038082c0740c1d20611490300c000c81211404a25251a01060060100c4c1240140360360414401085100b118420844556016440c2d0300c2c034801d800b80c005810310285801270313071b0072990b000205e4038280c0403031070100b11a0070282e880a2400000002c40c0740d481604100074a040100318400307a6100c0e101d03008807a400042c60102603401460706001410345001280c1e00ca001d036241c2a4600401e15000200e0301c1c2010040e126012070ba406c0c00d00348000d0b603115115046c150740d00c550014005031500d00c5901d228800442c0801d107003a0030b005080c0c0c0307100b9055004480c1d0304002e0091000506c0100311080c01258106c84401e40ca030720225100e94001e5083d440584224584001c000012008048101200411950881c0d150707803107102c0c15089070200a50f485d442c0f14140002001804c2c01c1d4000c02e10044140102c9402 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 260329298 1250 260328048 260328059
    0x807020a0c060c020112021b070506210405030f07030e03060a0c0c02010305150307030303023c070515070302030402030c0303040812030c0904020a0c060c0309170d0f050c090a05030109081e04 84
    0x240c0e400a80904207030042400c8412240e002404010054074049424510300301601888c0c49090b21031061000341c10554cd0082001c009082040b44d9014410b00111521101a81006800b04161001050190142500080300403840e44200b6195100a45034004060360301d400441c000c0000038480ca00044400e000103003941d4040020b000114401d6901595400c0d810007002034054050900c29104030741002000600258804aa4030441c0134a5045803a10324074140309141c015019107860b00c0e448050700b03100c0c0c0541e15400551185000360101c5102100034170034555030784501d03c1081d000d50405c2c034844d0103000034900110340244803031074110b003080c04260004003264411001e1401007070781a00d001e41002101d0082c3c0240c400103050811811000762580650200c40342480540410005042068840d250740444245142c6c12010042d9207410140420316a200e07162851055050290001d4181340c140110700c880d40c1c1c02400c0900b0841601807005100000b040c0c0c0c00e150013402d000c0800c6 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 260330548 1250 260329298 260329301
    0x60518010609062102060313080d053c15040605060f09210309010c030507051e010e010204051e0d15060f09021206091005090103080a0807020a0c060c020112 69
    0x90302d0856030003d00325140010001022070882030080d008840c810404002d6580c01095035849605001d002002c41c000d4505203400344200c0701000701940c03824040c0710300010141484400b01e805014800c00724941d482142c0e0707400d18400310000d40c07901080000b07000304900e041c84212080003d04041210fa48840000340303650850b0707454035254180464060000d143c00315441480000184e00b190016689650031a00c910a40302c400f818480400d540004140c0300f0012220701030b0304241962248803000c480c4620903400e450003610903600308180b00e0304200062086074200d0ba0000d080030006111135010081c0050300078a101d600c00300324446040454180401149e90034020080000c00c43d0800f03500c00360320611904140d01840c414030402d2403a1800c4001c01e50880b0f011606120282d640118000d480d8005410003078101c40c0c0880000200045400900139914264179801c0140d9907003402280d0768a040c1c038002d450950503203c1040318900400c04c0804240c0107142000d000d1451020200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 260331798 1250 260330548 260330561
    0x30b13061508180307061505130e0c011701120c0815090d090e0609060a050312070209060f090406020706021b0f0d08071709030c0d0807090609030f06051801 69
    0x4910741c140070440240c981e21038400c030303840180c240d151000c0d0980840e0803907480c010981c00402c2503a0b00d900321041005400800d10082030010054094203c030001d51078007901c0300d81c0e02c10751a40b14401d0741c2e200540c0070307504005031000303c0031a4400588c6008a1940f000420351401e45a641040e4000b1a50305414040010000c070241d000d0045800d00000b59443c1c080a40300d05c5040008410090181150007006107401800c1103030000070b0344e00d60f000000c91001c82030380b101c0d030b00d4840c0012400000d00c400d0094600705000301c90000107981d2380d00c188240d115180400e15800301a42000070b0005245501500300d0b18025074006003800d410441c146082911428035103516841038600c80c032034940401030004420b82610b03202116042245000d04204106900411070403c0d510001d862000100145c400e00c2c03201404540d40c5560f41d41d00a4801041624090001781d0a0000468818083d000307103821643e000c0422624034880751a4030008107400f80880c1000440007084580500e000d02581 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 260333048 1250 260331798 260331809
    0x709020c0a11060d021912090330050a1d0708120d0209030a23070b0d0c05071502210f0402010809150103050717070803040b0c03040e150406050d12030b1306 69
    0xc8200c15400140a010b000c404d01580296a013230490010000e81c0c4083c1030405032188141640c02c0b540440d10f24800303001031010321440c480c41c0800308000742510f40c004030200c1151840c401501c1780c2c82850070352103401c40d015480c02c030380c406ca003549500279051005107004aa0a0001030420403140300290401101c140b05841c0d0441c9107603459180c038a455942050035142d0001094020300d0000b9818082c0941c814040ca100c0d034030b451026405024204584480c3d901820043c1003030000c4000c18002e4101644c01800c20f0426001c01c200341054901d0385025110440b10550b00380d032a6801160002d81c0209050b006008022a548a400010110a000c1c5100d80e0107044003504000c0850351000016003100c14591043e0700c01c0000d074034040202c4054a0340d200c07200780d82e1101043c4507446c5114a901c4020040301c40d0f0104180400368088400c02040700b00c9051001036070390010880304802004000e02100b84800d01360509a01079444940b045034040c2280c0700c1242c0d041e040c081101d4507a07020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 260334298 1250 260333048 260333077
    0x507140a02040515030619020f040906060917070b09060d020a03050403030c02010605060904150806040507030c0911090f030f010e0a0b09030a080c0a0203070c06020a050709020c0a11060d02 83
    0x3a0452030540142039000302041c0d008800d102c0c0b01c03000660341b008017a006503019203c05500f030300d5106c41a01114001002003c040355075560b1020020b0080900e40710b0b01c2c0016110b00d4010501c03502c22810074140c801820010207940703045c02c4001d03445500c81c200c21135001c4410001c40c200c180c3d65001404460320552800500ea01d802d06010382070fa41d44440407400c69241000c2440745a4983c1c1c10340b4819102605e0000d03201410143c44c0881c0c000380d41102d00c41d0301c00c010811041002c0054950306482c89142083d0005941d07440300c0d020348000c1100c0d04414181403200710360501340012419a1040014100d030710894a450360603084805207050302060707410072040803060050600c510303604503d91800843c5048080c450050000002820504510314001404015103108005407804590004924070746242e503000080d41c4c4403a295011242409070440010368003e0510036940000c210102820122a45668918464024210f5141d12090a008082e41d060846c4041c000c025216100e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 260335548 1250 260334298 260334313
    0x50c21120606040b0406030b04060e131217010b0a0201090b0705121e04020105072109060221040b09030106120515090d1704020612040b06190305150403050714 70
    0x10620303000e00050040740500820001041015440022201240c2c200c7c0ba0004107045130f200000c002c3c0c5450360100d04042c1c240c106114003108240000c1c1889441031610a05280c0d0010040d540d50304d00c0800d241600c0c0031540100702419202d8014410083c05100011380b1001d40d03615985010801c2d1080c0002600c041208020a035504958580001100c1e52100b00c4a14060800345da02d000108000c1c1000004502c40781045541c01041070781d10b82c40034009040ba0800d000041000b192441b42ea0014401c00d0004500348840e81413240410402d410114078103400d100d28a080b643c0600d044c2c642566940a0000390418517000e011081031080c000b40503032801b07032143d0b400d158002400b040c040f6007121040001054101e13917149001c3d442d4903400d1106580b2400040c0341805011005150072505200700820001320714403103485401c045035183d2980d142c8444559451042e4040240b50340d008a05560f40c995046030003550051007850a81c0c5003e41300d994032403107140c54043c0806564800764 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 260336798 1250 260335548 260335567
    0xb070315091e0905060604151505030403121806200c0304080c101b020616050609190c14040e070303020606090109110a0e031c0e030c041b050c21 64
    0x2c5544160748664106115443d2162111074030b400c0040c0c00b151060355140c42100090711900f0000c4010000030b4000c1e1040303a2141c00c040c100d0f07401200c041340003880f41c0190042e00701d0188222560f2030190854400c412030310395103080c002c20340045902507103c104404200ca601c9054000e000d84880c1c03a018585962070040c5251a15540e14100b03841108186145440e1fa03074001ea24000790001000010034007203441c0040303500307072017000d062060b03445e4a01d0b81d600c24403800007045405150368200301c640700513034a24141d440c2404008000c052070317203030710b8104141200e21801c00414400180002035405000e02010300d0008550720880160700460108146880c205642d80d004082c5d0002c00d0006c04007008042c10507100b081e00e0b400030306c41d441802d480345131006c10030f07031004217881401c90b4110b10341044060a20248202e045201c5d00c40c0204014060a2030700800198611304172410103011140e07078080e40c036900035501403801881500e1030041c1c0700c0403102011780380d0111a042c0990714036611b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 260338048 1250 260336798 260336831
    0x5040603080417060705030a020d0912210506010c0303020c1207120305010b07021c0606181d03070309060f05070203010507050309061506180f040e0309030d030c0801030b07031509 79
    0x900000301c25130854003c0145180d0000b0889610050125005039039010a0500c1300041003c2c0d10050000d0f6940c4c0c54130f00b15075400c0844011420384c041440000a8480d0304cc40b01a50803c82c3e8603800100c21011a00c0028041c2d00a01a0340c0c0002d400e031402045130041c0c800c1d0a400454042da00e010f640328072a00d50a80510034140504845883d491400e102500454020401940048801605040c1280520461303500500180005142c806044988410100040c08004135098840000c102e660910300100004035010305030b05455068207a0300d005ca0541e1500340c13041c0c40ca130500c68200a01d10040e582803287c1e521540540d240c1640f6070a011050928080c002001d1412000b51400c410038199a11820f81d00503c012400c0e40b0500128240490920b9a00041c2590001c0c2001507074601e5401c0800984040481a0221b500e034140ca1002241074030507040f00500440d01c2c04e0010f00220701e00c0e4480315405415400d020030091081d0701641040303865544000d000030380e241021002403044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 260339298 1250 260338048 260338079
    0x5060c0a0f090605040605031e09070609090b0a05060f0c0d020d351005060c010b04050c160609020411070308070f0203130b0c0a0209090a0314030c030406090804050406030804 77
    0x500d00b4801440c1820000703080c40c842c500030241405000f2000958071702580201c48440328100e96201083d0402901c915075035207160240c1404107014800101e540d40541c8036540d45004001d2809a1451802c000d22101d82d21411803c21404001c005803272980302d08200d010a00c001a90041c80c0360215084000c1007000d51801d9001a00c21140c0400d1010900000c182080c0200c58540010b42e25100b482d94824002903210380d40003440891586801a019481140c3ea007400f9981401940d462905043c1c5500c1880c040e1280048030000b07150100f040c0344d0040c00d0591000c2c01c0010034402100d8064416040702e40100c0005454600300f000c01544005807802141c058001507081209282c070000c80c00c0131030301130941186801b058814841000304601800640c0141100705581010364510b522900b50308801c3d00401d100190201c500c1301c0d000f044038401c1c0b080c01c2000f4110744484e603544000d40050a4203070781a120238000840d05950740c0c40740070001c8d842402ca0703564807887d09582c203510b140d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 260340548 1250 260339298 260339327
    0x3010506270a1508011a0d26040b19030c0203031005091902030408040f0506070312020d0b120a0203010f140414010204030c0b04090b031b0f0d05060c0a 67
    0x403070350405000c0c40c55811150300011034201050340c140e41c410b80070000a10b1584441040c800c40d8040000311518103511210b85d14003e00d065860a0209000740b201000d600c0000500009044007455981103e580c0c030304603910b08a040380c91a140c1d480e403042e02c05811410039200d020380002c90710021150588159944070040d80003960542c6010280310003001160710806004150040019a0450901c8199034a180307900004540700d051500380000300390414081c17601e6490020344017040070b20302582602c902c04d41c19a2000c80540c0c420440e44080e410103040700101689450ba03501c01c80e80c0300070075990700380e010130010300440440e0300400d825284103c40b140107282c6001c44483d807510000200980c8160401d0180c2031182450043c03500a116980c0040d100040d0410003050b2401a003005000b152000d4005002c091194003c041c1c898144010b4001400c2082e0b0302e8038110f060110b4801d0a4840003400032042d4071464942d01e04080044901d44e041580c005852030301c00781c001c8407105e44504d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 260341798 1250 260340548 260340559
    0xa060e150306073603080304060c0212040b0307030c0e031b03010c030908090d050a05010f090b0702010218041808030a091a010b120414010c1701080c060d090501020405091503010506 80
    0x1e841e000a072a040035804141c4030f20108019000c4d20742d0510800341c07005540c082e0303020f9a81c0c60076003002002846e0000d50341006005404144440c1541c2c1d405880c2680c0021a14a10303540f5280415002007082d20f1000082c0500442d9004550380d05100d02c81c0e900c0c0120044c03c005d0348003001018210fa08015618050503c2d15a140001c90b074140169440340030160340e00c0c00707588206d05115143c2850110010202d6090074014600b5861540040000c240304802d910241d40303072080c1c00c1e03080c0d000704115001601549001c10b08540340c590041080c05503100c0340303c0341700380da5502ca070107499008461609070141c81d994010704110300c0720b0400d04204940d21401d42c680d41007100d013003211b10541c001d1040d0130f2091804641403101c0015800b001c07002d808000c000308090f000f809800d000350440d80400c00c584260000803640004a03000000c40c00080a06142c020119201002410450001d075a55175090002140c1c9844d62500c0c180245886402c040a04000f0420982994170041110f80100c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 260343048 1250 260341798 260341817
    0x507111306080d0f1b0f140706030f0e100b0a1205030405090603010c020a262a06010f060528020f100204030305040522020417060906040b0f0a060e15030607 69
    0x241e41c0041c48100b00e10418829070110030003070800c03441c41b8401540142c8a44803e0024150b50000018140c1c01c881894405000034002c040502080744c0c00c004120721a500b01c1900710502018540c44420301900042c030200f65581c0f20340301d903964030300a82811035143e80002014000d52030010b2a81d030f03221200304c009206109603504025222010140010240c0342d03000800007060100d81c0d406486184030204a64407048401ca0500c0c00d4007010101d450395442400ea004900c820211f01c05060701c03002012031600c50311f8100101c896034402900c00c0d10008049094103000c0500343c6170203071010900d9000f040c1400c2c41d4190b0074200541180f100c2c40302d030320400c030408c00240c1203420b40342110f0003142c2e41300e00f141500ca074100401c221581d504000030320020300800c1d2440c2d11a09e5402380000b00c01101c07400d550300a1280e654003000d4030041e05203081440021400a03152307451302e0388048011400320342d0641d1307043c0514880009039549401481d1902403a007013030a0401002d9484803461a081249 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 260344298 1250 260343048 260343077
    0x406080705031f0204120807020f011103040b0705030f040e040213090515090f0a0c0603141b0a02030c0f0a1218090c0201020c120405120d0806010507111306080d 71
    0x1901692000f0349241c510561100311001c040d0750560300141300c1d50680304007080c0f407440c05408541c01b0380c03000c030300c684210301c1518034952084500b5035076070552500451800741040300e0410b10b50442c00d03003201c2c0d40c4010001902d001024101a100a241c008086006410144104201c1204a0301c120345814078124017100818400561206c0389000c91102c01a02d1b29400c190508265444180c008c075803080803550810404442050b40c11560f080d5410000406070003071540345160103540c0e09864014000e264000628120000c1031499010300480c0d2820b110041c18504046034041c0d41040c0c0d0b0080c1d0b00d86001e02080d8064000c045880d46400e800c0b03520142c08403c074180c001d020b02442540e07280410044203000f5411625075409200441d600c44045181090b242d42c024020140200070790801e82170104c1002070343c801d0b0021643c864503429036580004640d2a004002d042c1c480d01c3c070884400c003880c0c483c4110507545640d060004078030700317050030185031401110601da44100007442d080e0032070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 260345548 1250 260344298 260344303
    0x601060c050d0f090806041202012d0b0a0312020604150605101206090e0a060c031b030902030a080304050303180c100c05030f030705130e010506030a05040c08100b040608070503 78
    0x2d05410310f00b441c22031000d0020382141c6422558105171584d102d55001d000c14040d8100000c2c5a000a40d4000d00c080c0410748103000000304010300b581e0042d0711594050f61172101e0f0ba04818015200038285036541562500c8030209954001034802c0940c002c001031000744801409400c0d20291014402d200e91481d10010a08070039050020404000481041014180c0385030031100040048403400e01c020014166100d071585140c03c01118414030b0010003002e068080d00901441440b400113007004101c01840681c090404214101e074140110b00c0d082d030014a44a0281d8056400740006544915240300c0c0c94584000483d0524620f900034500f1480ea0340c2d030904035034400ca01034078189e131403c00103181961950240400c080c8006201008105026a000d000350640d80c01d9180c0d055141c030383d10303d00800d039941c081c000e168211004000048101caa03603040282c003d44540c2d51020030036540c922244c2040c500c00402c1c41850348481e00082c5524141c0100b602800042001d00001440d2100003903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 260346798 1250 260345548 260345563
    0x906050f0609010c0501020c010e060f011a22031a0a09051e03070c03030c0309090e06151201060f082116030c050303010605041d04150e0c040207060204080601060c05 73
    0x3440784000203580202c592003220901440350340540250346520024107800e01070072041c4800015886030344002900c0d001c1c001100f0b4108c1d03550b52003c400c40c50640952040941c80070304a44013404c58400c4407031000180300304400003180114024840c200001e148400000000781c2001e130b0ac00d00308070b0208081040440c66071201c00300c0d452802103015500318010b00310f000b8440003a101c014030850010515400040c00045688266580e07841c0e1511829017000711045a27a0400040d440000001d0740300c01a010304501c3d14400906100181707400001c1d4500307681e2250068085e140d8407982c01c00148500308003c2200070b46080840756003d1f01c080c01003a0900900c81000c508565028120040c0360040600144e03140c3c1000070342c0e50b29070711400c0143c2170340e10038842c0d0408281a40d1984070305030b0031318a4040c00f455000e02d43c000c4010b88144d2a00160001102540c3c183c040c0b80d1f82ca0595642e5440106400307481240d025842d00e00d811085401e10344141d00440034450060095000034601142d40b070b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 260348048 1250 260346798 260346829
    0xa0506070f1709010204080114100b0f0705030c0a140c1302090402120103030305160e01050307140d0c090302030c010e010519120f05090115050307090b03030d02040e0f01090605 78
    0x6140d0403000074100c81c00b007a26498a0000049881800702401e8190000c006a032805002880421405101d02140400440341c0041502203030724107011f01040000142481c503101e500700c906102e1075485050940d8030200c0c14090960100d45100108010b1140c50403080111030060300e0814540c00108a149144c3c491503140503500003110a2103075500c0d410f0b24188034010b40000c0c1b5030344c0c4920700500207020035150603070144140c070a02c4200d28414684260000d5042c0d41f03107030460f12240c40541e01d540340d07800961810036041c4107410a6080c64801c1c004040701581d640b031802442c60050506151107151510304001c804000186280d0f001002c0f41d818096156a8440e50070301003c0441d00d8101d2485d0382010f80c0d00780400c000d03444030b5540266004560440c001c20204d80311004a12140516210307103601600040d0041001000c641c2c03100302c00c06006801e491034003064002c81005c9a04c00d400c40920f0800840900c110701c05207680e483c2c05003c900000300211400d100000b0021003800c40039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 260349298 1250 260348048 260348057
    0x21c05090a0c0303090f0b070305090f0d02100e040501080102040b07120c050105040b15040c021207030e030d0921051b060714030a030b040b06032e08070f0501020a050607 75
    0x314185240801142000035000740a02050341e4807032070020410800d91180903400c620760440840e43c2164a01140d80b015403503201c0901e00b140150500942586852031154004112a003240241c0c90b03000301c20719400100e50305c0380c840408100801040312010303080781005a10500080c0b18a500c007404407100d50350420742c10b40007021494800c03900c91b00003e000030400d5080c00280010040d07072507102409401882c0103503800c42d99400034041240d8010b210b190041c0e01c650b000440084002000303003407080c000d00c3c1603d41d0710f40000101c0c3c904046005d580000940100c01000180c800d0444010542c1c4844001c8001d41d48540382d669807030341c510400161000039040340300d400ea43c9070012540710b0f40c2d000d0000d4200c0f6441d00b08054503500800034000119043c10f55880301441e05100e44815054018069411501c90103a841c0206000d042d003c582000d403000c098160382540740c00c42c401000c1030402400100d040003901d10302d2004a50045040d5030103c00c030000010404101d02d523101ca2540791 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 260350548 1250 260349298 260349301
    0x1d0303100621020d0b1507020d2616031106010e04081804090f050f0c01080a05150d0602130b2106011404080f0d1103030109021c050721021c05 63
    0x403031898003040d1100d02c502080c07000582c0d00c03618000e0b03007258400103801c9400c0408040350b419a641944180d000096028590790012000140340c1103602008011070780e11007094a55100b4040c100344d00000030844105000f908160805d50b004007042c1c00e6100c01d030043c0c0815458189440980000944010300424000c20f000c0314090704c80000490302540103000380241c2c1c805007801141e040e6880c0c0103480b00d000e5181c0702035042c00c0000c1d06400c10b00043e0345c2c140c056035400c03400000420707020305000f540d0082c0e0951340c212596074024814415008003001a50340c0402e0711030499545290307019100f000c01c1406640c101c00722801111139424003000a2012079641c520040307802d41e582c2c400380c0640c0301000c80c001c5440f00c0700080040c4e841c0010000c071907503010300901c00d9840c130058001c00019540104010b00c8032281c01d4010b011003240d4070340c4082d4400612242d14041d90821181c40c0001485102103407180c803150300e110b80200400c10030842c98580c00c4036090024503000707a2191840c540700d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 260351798 1250 260350548 260350577
    0xe01290609040c0807030e1f09060f051f0e0f060103020703170115090b0310060f021203040f0203011b1b05070e0f06010f051305090c0912011d03031006 67
    0x42140c4000741c000300200007003499001d020b00b190070b00f9500740000900d050141c0100040000b000c03c1525041c1014046c030f1543c0c90f424401600744120b044410b2504c800c038482c11251a0b00655015032003402a52540b02c040644080d6603080ea580f200c4070200203807003404030200040300c250340c00420070719016a48440c1414250b881034208407540410701d002c00f000044185121201030341c2059240d48600c1c40590307804002c41e0341c2c0400c0c0c1d001d01013000010400c021144c095281040c00c80014015141c071000072040e15003c03500211000d03076071006c10032100001c46c6000c0c0f0815403140070240f5010034002010380010843c0703d00c0c2c01c3d030340450324804030491b040c000d0401041700200585514004039281c004503013000040c0642d0482d0124a4081000401c64010020303501f010140450384001e1514000401002860260a607d5400c004210110042c0c407181120701e8004100400401c0c1c8200c001e205118040450348080100d80040c4103220610f060b80450404450342c42c64002c1c11682d041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 260353048 1250 260351798 260351809
    0x19020612040f0b07030f0b1f0c17040303090501030e030a170a0905100f180f0b06040b280f051302030a0b190806060a030308060111010204120c05040e0129 68
    0x4000034085003c00400c104005078141c10824031044d840000f4001118001c3c18049620701008104402d11841c50080344280d200c0d40405200c44e016485040030401d102950080d154440d80013503000400000042c001541c041c01100b002071202801185015510074006111070400d80b010742d032820b41100031074403020840d0020000346820a066074802162250040000c1031469a01c240c41e42c1810031251040300c0812850b020550000609036070200c4c240d0710ba95a0140c0103104540c0503503100b0a482c51621031a4510f0180004070100da1500000e042001c620403516501002003015621400c2c042e586590030744103580220203c0160b00c0f92120071203613000e00524646503030482485c0381c1c2601189040390b028000c480002d81550029103991040c032800c13030301602020740410f0440c1c01246072544110084d550020480c000141020386500c044050009a02c0040e6800d1128840070300c1035141912600103170007081c000800c140091020340152801c1901050740744945204c000742e1150b00c61 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 260354298 1250 260353048 260353073
    0x160c050c0a090504110a03030c0807170409020309060604180204020f160f030906020604030e0d020f130e0606030705010f26010b0a02060604090c051002150a020703021902061204 78
    0x34054007416845207422001003500f2201a60b160003462214030060405816007410749406030341c0c04001c4080743c0c0390780f07030369602081d0121950034000d5891140300034101e0252014002820b009030703480c1425941f036442c00c4c0000d0b190b1481280341040d094001c0c11045200d02c40c156050f1000f40e150452010740c154140980403206c0c02e400710204690f02080303050811188004c1c42034030740462701515048101d0b0342d250100c1d03004002c0b403030f440002e008078a1b189407030301c1c000c500c02818090a00442c10101c0c920024040d4100b4a0a49030070394101002028480303030340e0103402500200100d0b860a000280300a40c03284009091080f800f0340c047d62511480e10442c40281001e914024551350340841459941c8022500001801450080b1394249000e02400000760b03040f00b48609802e081508011004a2070707080319080d4480c5201d001040004500102e10070030340c0280c016100d018605000c2e007085441c400d01e40000301d0610440006035120f809941c0c501c80360480403026650381c0c1c640103070400c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 260355548 1250 260354298 260354323
    0x206010e060d060f2a0e06070618050d11010e030903071710090506010608010e0907063e1e06010b0f0408030c0c040605060c061302011e0c060c0503160c05 68
    0x81038102175203a00c891038039621105d18180800c9001c0e154810031207061103044c01080d03000c04c0c02c02520001c1091604002d19102c0c1600042001005607030b1450310b040f403c4000040410a041540c101411082c80351103000310054014614011000001030346850080c0110b03800d1840c480d8400440040c10050140c3c1159851020804003038a820101d43d00c040c02d01ca4040014804400030408000e0b00c0543c6005000c0d40004080c800c1c249902030343d20788001e082c0e8815880e85081e00c00369821084164400d07a5040440f44900c544401040504000ca4074103004445400051006443d0f4800180c142c1110301140c0034640b102e1300c20080c00f406125552100059100208400e10b8000c00410003089101c0d086508004e025951010f1081a0059000c64400c030340040c4005034040c900042c0c1c07003244520514000c1409440c1c02080f80300e96002c0c039000d0000502c400103480c2003056602c034584064040b03003082421464102c0110002c03e80607280c00c400c109021102074100320003004503990082d07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 260356798 1250 260355548 260355551
    0x40315051f08010203010f05010e01050a0309110604030605010503010c0806030a06050405070504020406020f010e0106140915120a14070f0311040f0f09020406170c191d090d0206010e060d060f 84
    0x242d440c022207020350000e00035041c40300d1042e0310019196009460f000c10355003041c0c44150400d0300010066005100302c0100343c0b0b0320740c084031016440d43e454070010030103140701f0500000d295040c0814142124190755108091100c1441846699a40041c00000b090342c0280041501d582e030303107009414240e071907005640040c000728010641ca03401044855107000d5003402080b10705070b101d4105081c0c54442c4034080019080e023616000714102142c04561109040b20503520412400010442d182042001400150001d034030300d03000c00551700d40800e104110400200034031820039503d451212003602c4000e02c0120305c200b070030013242c03185d4000221501c8121f00422202e02143d01942c0a0304071514124461031810001149030503000344092402500c100090403400300e810b081c0303d507540e80721a0060000103a17080000c0c19014440070b1401030031514650030007504100c15142d103003c60800c040429500183c0040c012402d0140550f94480021120110000c1c49814018018440c8100005400d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 260358048 1250 260356798 260356861
    0x30304080406020d08061315170a030810080d050a030b0d0c05190b041203050d0c120e1c0e0a0806150102121c0b041b030609060501030204031505 64
    0xa0840058802c480e5a6020703600451142c0804443d500c900311000e035409451545c629099042c140c0c46850301c800120300040f44942c0301d040002141884900e00e02072136000b50b201c00c0c01c066002d14080d400c00121600c949105003410b010540794624814034404008000c91f003410310501c29000300030500b102914264440e1500d08158585080700d0081902030404c4070100b0343e100810b003541078200c809803042a820300342450041c86541c40c842c6425010400144106407800b107080c880c0f40c0060040e07440c3c407803180c61071910800603104060501807054005914214883d41c00545032000070f8440c0c40e2480c0007101759000100340102e40d8002107040d2180307804001600000300880407220f0700907000c8411480d40c5001c0707a001031160382500c1503c10311007584030701c03042d07500d800020004030001e20100d043d120050200d54180e03d40c0f4101c9001075110101082004094861880076240030728080d460982140c5662181002da4200445416621000545d41c0008948440a445170041c0269081c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 260359298 1250 260358048 260358053
    0xd0c06140d090f02010e03030c0307020f012105010e06060a0c120915020601080c03060925170c12060610050708071e030f0305010e0106031a1017060321071103030304 73
    0x11840f1007041203010883c4200092014a80002555501050f103002189050025428000c881c1e49007001d04d4140303c2a6400034000c03284000a50705c1804250303030b0010f20303503140ca0b0382c40d108944050b04581c00361604200c401405035010000d40c1201b41c21900304060601c845208451490035580702d14165003181501c0c0300669404100d1034121280c0c1411120a02d211000b0143c55a00a8a5054503580f002091822007034440e03400302c060980d52402010810358401c1440ba2002800d006004641c00581e80b02d0040d161842d4401019990b02d001800c442c9000c0c2c0c04603492091040b124410b000340810080d003000320071f508448100368002800c652410584119014078000200114040351010a00c4500c640c82403141504944448201071056460320340140c004000700c1c00c4882190390b00004c0b12039951a00c40300031110003880e94a2111003148144615480800580000d109030001c40702c0324283c0f25101640b400120015000361f5480c20b0503d8602201d0040c4c900594046c0400300402c070a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 260360548 1250 260359298 260359313
    0x703140304080c0a0e07140708030106090e10080c0111030d02040f0e010e0c1c0212040c050406080102091525060902120a05100221040f060b0d0c06140d09 68
    0x854444604071500400340070108a140758580c010100c038061744400040015124400013044e040d1000c0c030b510b16160064454010320b5000740c1094010070350b1100b04000120401c00800c0d4804480000044001d0030b040312035884504100c2d500b810032003600b220690006c0d042c0202c1c0d10081503040d0444d9265560000c050980b0540d104d00d081c2d615032400006540034607915114811566449468646901000005c4608880002c040c0c2119424808401046000c0360341c2d0340a6030242111040183c901002c01c0161241c541000b02a6401480421643c5d207c41528440c15170354900780c1500c0d040034180c0280c145000400c00d6101c281402d0601c0c4c103000099000d81c824900a403004d0a107400c00c200a02e590700036500f0300070a00d030312202c010b02405806501400c0700061442d03c1d080c0580c550800940844010354080d00e00225090241c001c101c854803502032170503000e55084c001d0703c00c00d441300301119070103200d0320090009c60311000030202d0300c1c08101da016580c550b10400440356103003403198 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 260361798 1250 260360548 260360557
    0x9210c16090516090b0d0204090f090b06030a03140c032503030b01170f090c0a03140705040b0901030b0c090a0602030d06090203130f0203030702150a081b030f0907031403 75
    0x15403503450b000115011805612086107003140c1a226090b281c0d00c0c000203842258000355042640302e500388804981c0c54068014030f4203d088218021075034a070b00c1d04100082040142100c2e100b5070201032110006500100f116840c81c0c9185291500d8140d0002020f0651294440b150751712600c00210200071500303000b0002105009990400413124007000641da0007031100340e250009030020b070006059a401408480d40102c008040d40d00c41c10200b00400c0444442e81c000b142c0303500090070400034184003006800c0040c80b048405220b84407100000c100e40300300600000c5c02408006000800102900085414a003005060500100d6035040700a4603904105c40b40314105003441c5c00080d0704006030081c0c80c0100c0d0100662a8442900e41d9200000000b86000304d801d03000a01491707015035038003d0020b840003500c0c800c00341d841c1012640103121030300040c050200441b0206900c0c44682c040810341c2e6200404d00d180c1c1045480e548a2a0b1401d10107500c001e1080c98495040e560045000c009071 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 260363048 1250 260361798 260361809
    0xd08031003110103050121030201060e10170601050916050702180f07030c12150e1e0a020301061704020f0d05010c090f12030e181f0e09210c16 63
    0x560b6020401e400440c03c0e14401e11507200d100c01100c1c2107100141d054000c0c001c4c0c5a1007400006029075075041c4120724904200ca0740d22000710081d130204200c4800b4101e9102c2100780c0c03005442251304000c00604a400d01412001e0403035414815501c00764050000c6500140d0010401d140c0c02040c1e5a080c42e1211080380c07154024100b5602103840c075400b034010b8040036101ca44801c108903070058441c000500c41500c1c1c0402d80441c0007000a00c02c451302030818014604004400380e155020244260b1030701c8081c21850030f40d841000100603079075101c0e0002850b007141c15803000e42922940006640d40209241180d40007100c0f80c0d01b4020010158400b40b5180c3d00ca441d10340003e5a80c0c810a80160074074420900720040458483c00000e102c4d400300d2070207000040c4040c6c3c20720009100311414520480d24580030401c481403440130020b00321846002400c1d450211402ca1406c0b1221644400c0c0e01101c2c000c001030960903499074950000300742c41e11075a00b00116001d40c26000007016080141e880360 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 260364298 1250 260363048 260363063
    0x100e0a0519142d0109060603180b04080f041706040b06040c020a06020a020f0307030e040b0607020f0409020111100203100f050d080307030f0e0d0306090204230d08031003 75
    0x10510466029856202d40885801c0b551907071210300c0740152040c446450155600c2000140c10702500d0100c40d82d0181c659010000350060030428082e00710307000070700108481140c0c240c0440c0051344c2e440d0f2896120340c2c0495500c0e21646440c1140d02140200d402204984105d01c2500420007000a140ba20907402101740790140c0d140c2e0424001258001c501810060700300c50542d20104519400030801c04079544110303440303101c49000050664203c144200d000036030800400c0400c0c0f6040c007038140721007070031221a40b40149650000b01c1070a00d009066010745c0e102e001c0b03407080d6030103074080d0901d004682c1c0980d4941c000890402000354800c13034a402051015000104640000540d4802035640103021800e800d810703516200c143c2d8000400070700c201510303000300344250800c6004502603107a141c1c00030080c41a40d07400c0901903d15a0f009942890310602003005002050300c2d4441102c101d00d0002058540200081408d401600350050b0840000005101546000510070001c81c0d00443d031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 260365548 1250 260364298 260364331
    0xa020c1201020738060d020a0303170f221406011403100b10050d0b0d0c152c030c0415030308130206040504110702030d050301050406050114030f100e0a05 68
    0x1c200840e2184e45440d0001103896982070003082803a2041d141c1c00010041c45210300c40056030005a10382d03416001200080c1100343c1c01c01c20a03a440340c0300740e003044d5001e01c1500280307001c14010040c1145000528000c030b54070524a0184603642143c0b109000d0340d201911410360311508400511320018003031034001d220b150000d40340030702d55110701801860010540d1543c0d110207d81100d041c3c01402005140e01d5031101c64000a070744c0d8100303000643d071086040101c05450700030301458005403105060240240481c0300d80102e04809000200c40c00803000008105110700046490718030318134072150304649882241b40c0c0b6403044280500403284207070340301c0d20720341e40d0b408240c5201582900001e4111100340818050351400b504441c1c6400c0c0e507016120b003000320030b8001034a010001450007010030000001030003075042c2790150101400307007030070900140181c0400390b0b019480010710119108192402095290950040c4039008050141c0180c2103801d10401c640c0080c1819030700520341290481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 260366798 1250 260365548 260365583
    0x9181f090504260d0c030b01091221050d18110d03080c03190513020405090c03032a070906140108060306040b0a0e010207060506030d02070e07050a020c12010207 71
    0x910307481103501240e1040183d404080c204031621103034112450602d000d2040f0f42135000c25210b940c1114245070b60106925107118009014160641c015030821205603032030b00c000c940700c3c002c18041401802440b2219200640086510340283ca40c2c0840c858140101012180c20758801c03025664002c1210801800d8000f0400408861110004000c07034003a000062640d00980055548101000401a40314172000c15007002c6540456180415080040c011015800d051040660010304c64004001100f03504000036900d01030315001540021419000303402d144100070710060030303440c01822a12020784506540018198600400706168a01912084598442c0444502410307016019143d00e0f00d5903200c20944483c003d0010380f1440c0c551040c410208402d00c002e054480c056000020300d810703c0410181400e45214030003003154042c80082c09035042c00480c2c1c0342c100c02d0398145260b4a841d020016814560070440c6c465020320f1401601c3c04050064000b0b140c400d1080380f012610b8000103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 260368048 1250 260366798 260366801
    0xf0303010602060408180d0b0405120408120310030206041203180f031401091b03050705100503010608040c09050109020405030d030606080c0702010306080a062a0c0809181f09 77
    0x921810740142c0c030590104000c40c0aa50042980c1c00842c8034410103c1d55a80114039800400c0b001245c1c07074088a400c11060043c00d01c0001c00d01c0420b510a81d2829280c241901c0d52050712160000c94114008040b9400301c0c0710749c040700003c5038050101a01c850b550065032618011800b810703000b09112180c600b13030403004114a40d05941074200034185540c210b40b10510a200c8541403c80c19659a40d0540007084200001c0130300412000c00400c401811071410701c0c100300135540b1003402074011403120921242c024040d00e040d01d40c54507000c03019035100c1c1411110126103078002d018091800002241100f801d40041095550076000c58030714110009088045850f9803080c08000b904d240040381040c000300c8001c0081070300514001c500a03841ea0030040c02e00582d41c50480c0c48a9403001207a48115140320380c02284850740300e814014207842030700078061090942d0024846040002c05000036600e6006103d84502c1e00c960003149e42ca800d0035041c2201040d00c00342c3c1600e4800c800d0005024034203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 260369298 1250 260368048 260368051
    0x513140c03070216151d0301061e05030c090f0903070807030309030e220e101503030f050c0c0904061806090b100f050418150507030f0605061206030106150e030f0303 73
    0x2145c00ca29480d940380001c9840d01444003811001340071540c0080c5240d6000d00800c1c001d040b400300c1143c1920110078406202c0050303a0300c1a802a04021407413040390740c8041c0d405502c400c0450442d8855590007030542d003148034075034008041d5140812140d00b4141d25505c43c08000f031094450028076030501c000c114a030860850013410071010b00307121042c0303909186c001c2c44141c4020030441d201d03150310460110594004481b418040c2d02d28103c20000e00d9405010100403845904119151200000209880300c00103000c440c010344025000c03604101d85a84039415030070134034100d481c41c490a8500341e00075085151040e0383c820300b00004141c01f9071520780c0c04001c032800d41002e880e2003480d0505200140c43d800d40c40400c0c0e00d07441280c1601066501d202e404801c000074400180c0345c0342561020703044070200d0b0b0500d00120304e03241003802240c5801301102c0c00715070501c494480307542e075007000240502a0754201061031907105103210b0602d504140c6c1150f0f007500031029900e00d01c4c0c041c1a450303500d000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 260370548 1250 260369298 260369309
    0x1050d020f03210d0605150d1a04060b0d06080d0905150408150702010606030209010f0503100b13031a040c0308160606180f0b010203040513140c03070216 68
    0x1080229005140841180403122405410f07258000340000c1d0390000290321008403519107100040340c0e8900c1441380b0600003d0001251902c0ca04158110105070500519102d4103030b0030ba803400d0740e1016603c5648505190807008000784a0381e83ca4214500940e000302462100300380c1450f0f4003090b00d01020071402c0105843d80c1d2204480341c509400c0044000140c04881c1e40390340104008141c41400303001c9201000c010940c05100c0d810140300003400c50301254085000c151040c4844045603034043c21001100e041480c0c0142c8031f88810091008465850b8021090010005489506d0060400c01038080703d008a410300c02c10ba21101ca00040d0328002c0b04d00400500d40c501c414400695030307201400c80f0003007250b01ca9180c01900d50301ca500300c4080b50400300040742400401403524103207018080050003581000c4c0304401203200083d6403400745008240c4100c07520510410a0005640308441d4550513100080d6281044d03428207415034000c2d200c1e4001070040e030103100209624a54500101ca0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 260371798 1250 260370548 260370559
    0x21f1b0e031b01050f0a09080a050109031115010b0318150a0b01090305060103080c030d090f0c08030a082d0a050105180405070905040f0501090c0e0703110d020a0c0f08091005030105 80
    0x210068400c100c2c0e522181b003d0040c45482e00300451080c804109507140381c2d06c28000041c0c03204803401c02811115143d83c001c401075011302c10b800c00318500c1498a90444010a40880e01c030b49942840b0030107650591005841803281d280c49813000e20044c03003058012129981d04002d260b82c10300046600e502e643c0006401d6038060310042000600c1e2600030b01015081d0700a503801e02c03801001d00005d031207410304161039088070000c00d00180704280c0903040080600c03d00552420044150140025000409050010710b400702c124801240c0348200c1042c2d0042030414110f1481c050301c0f50b81c020319007030250500604000d006c0010244040350071078010343c0c1050007003004600c2c00ca4081702070900104112514170316006004000340090290910b064803480e0108103031410b03c071001080f881d004140108240c00c1042c1000c4110031003003100d6a003640d10102680e28416582d041d0741c0801c01d41402072a51110165890a01c410440500390842c1d00300c50400f640c504101d400c69540c0403c2c024a680301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 260373048 1250 260371798 260371807
    0x7080a0209061b010b0d05010615030216020909030f2802010b011e0e0d121d0a030b06030114070906030b041e0509120c011a0a06021f1b0e031b0105 65
    0x144076000c01d0600f11001030010400c689090085912156103550445140e916400207011003c00070200891215182c0340850400d0010034800d0340e070020014019004022500c081040c070301090040342d4010184294041d40c1e06402c050100e40c2e001107000c100303480128030310700c44092803040c0100004008141e4544e024807a6000e51a1269000c0100403803d102c0030303d84600e05512514410f0103464090b01c051500b40014070300240111086402c0c4440581051420b01c0c1c80e555001543c4003942d8200503403503403035610900072900500342441444400d102c11400c0003038032603010801e43d080c1d410b1550141300030303041076017440305130307820b4203004060102403883c49035a01d4000d80c032180e4000300c2c840854041036020350b03840c1500d44c404400c0140e0382c2d4581e01500d21a20042052005008061b5001002c2c2c6180c524000d4441455045a01c07941307803080d890a84250141d0484000001c82d200d00840800800384090300e4220302c07414550203401407203802120b1304030444641320350b500e0603160030341740 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 260374298 1250 260373048 260373067
    0x301360203030a11070503070b0909182d03041e09090314030a140702061803040305030d0504031106011212050a0e15070c0e060f060a0c060903090302060c0607080a020906 75
    0x4a1050701354052048040000d0503603404c00202008100d41350030301d0347d510030520030306c140784000600d401041400c03084030525454001881203104801ea0070f03138010254482c00e00b0040c0740d0008071020078520001c034001c2800f405000d005e141c0b80d0311080c040c1586540e1104260b06480701440058081205034144503d80201c050046170f000d074030320400061209495444815400e4150b078040d0060b4051010000e21440c2226a4800d0706540b0340150f0034541383d960740b15900e100386061801c5803500c0d40017003010140034401c59000301c8465015030308a5a10f52002c0c803003424201400381c17010604081e00b03101083c02641110310b404119956140c941600d0f0043c4135100364841940d00c45d1a10801848000c5207206c0b250501030f14919071090342c2403d00404220000383e998240c00e1090300200000030784540c04c02c51103181306a008902069804031410203843d12040360380060341000c00061030080c0076101046191044400f61036028554440e014000c0c204d00a080c0b03486e4101800700940342c01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 260375548 1250 260374298 260374307
    0x30201030b0111010e070e060312030615071a0421020c01080603100c0503061503130f0c120b04020406090608031b03130f210f020f0307050301360203030a 68
    0x221042c105840c40c12a80e0f092142100c4280c940454543c121302010311104422400c5150000301c200c008041700f800104059110348005444244180090a40341402c0d04401003074489940e004903404100e084801c401900502084504480030b420300b520307816000d241164101401f100030790080080e01d4210740103440e0b02001a1056a0501c201103010030050340c2e501402940d42d6880c1e81d0280c8a0400c5c500307010031085400c4d078907001a130f802d004001122040c1c02000c1d4201d80c0200c80105a51820300702515003c2a81c1c11020001c942140541c003030003540144140030b42d1094404001c0655141d1841d400c40c5c100c1c5c002c00e00c03160070820140901c414226018180020003406680c034002c1d800c1030080c46000958008050742c0c0300004100101d038440240c003650903d0007144d00c035840846075986e00d4078150700300000b03101e080131440e40317410303510204803030303000f07090050000c0102d000c2001178482c08681244900c0f42c4200c080500c00da20207800b80c9210586580a4001c1d400d00e4007080c003c0d01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 260376798 1250 260375548 260375561
    0xe04020f030c0306070f0e04230a020903061611010501081c02070503010e07030c081504060207030203070c03060b040e150609041403070813060e010c11040209090103060501090c081003020103 84
    0x15070500c1120071004503a5024400180180c0031500ca4031880d21900c100a04101c0c211403001f80301d246004440c2d05860030b0740c000c2000c60011140030028580e5003500042c000e0040305103803601031003040100100f00303840441c1c2405502103170b1544200b96054085803400d0321320900507480c054101200740713004852031111014007038103580160381200780c5640100c2d08403100c600300c03102c13554003806003001032144850b401c101401c00c1c100070b448442c001d81403681102d08050801000a40c0c000789000c203041c82442a1641c0680c0458680b03da03a60b60305002010303001c0d10b40031620452515000c1101044000743d01c8010300d012110341103440c2c3c0d0390000c001c1c4011004009443c144145605098034040a000501d00c1c14820403885442d03000012100c400743c0c942e50070420610824503c02001c5a800030341c00005036a0110f9441302440304413010070060f000b11400300343c03c0044030001000308060303600a039060b82c994607410043c4400c411004c81d0606420b40303c0351410700f403110040c000f6501c01d07003011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 260378048 1250 260376798 260376829
    0x11010b01140a091a09040b12060c030601050f1b0d09030b150307050901030f0507120312111608180103050105090109090501091205030f0f0105100503130c080706080f010e0402 77
    0x1a11051380d01d8900c0340c0b59007841c0071000301400c030000b02d40031103141c42c0c46540102070041d42d0b5800b242c03c914095507070b030f5600981141c142641c0800022000e0388620126103d982040c2907040e15020600101071a5200c141c84404243c02204600a02d40c0d2081214004403600301c0c00d59040c0b901c41da81458008819000d503d9090700492001040b0b030784481c0c3c20340e4000d40c840c140b281a03c0d082820020706040e11500450700a0040501d164040399005040d81481002c8540003d840d00440c00600d1040c411001e00501030300e00100c02c0000e0140142c05003581800403c030701030700c14034100f0044040b11003d00132603600c001e5150060250b0301d00313640440c2086100d600002420600703602e82e1901600810104070001ea8000100201d41c0452000c07560854034600c14180c2c0343d410900050396100c0c5481c210000c00c003005c000520031060002c00d0661480c0c108071007605040e162426203840701268010100441c80090108418444001255040355291140200d40d0b4030703503a00b0410107000d44900c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 260379298 1250 260378048 260378057
    0xd030f0608010204031b080316080318011a04050a0b060f0703110102070b16111b1903030305090609030a0906050d24050a0501020a050706030e031b07050111010b01140a 74
    0x8076840300244000c1011703600031800140c06e200100f0156414242179040a00503410a0007112205000c0f0010703204640d50114059449035503020307081404110200010302c566081526800c0740c8d00d8042c0c002d1044074010b540501150303449960180c00d0350710010b28242c11000070001d1a10101001c8d01400700b8611a00d440505170180d4000c40f0f0a9800c00305c4280c2c1c005030120180850304000c44081c0c0c414070f00600b02242d2000002080c15142c0781400e05501d0340341074004c000660340c0d035014266948250808100d0302e1858680c240140102012600d6411a206590215286450000c15504905015600c15403000d040640482d030907080075031010a55625209642918400b504045083c01c08245002403104c1c54101041840c1f00342c2d07032040d415500421400d001042007c039252041d1403203418007052090032b03840382502d140301d2801e0692002c000c00c00114031040001c22614100d032000d80e20b1007584100658210701b20703003c8070401800f2407440c0e000030170b02c40326a202901848185080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 260380548 1250 260379298 260379311
    0xc120304140318010f02010506151305031207050c030622170304030e0406060c11300f0c060301050d0605090c03070303021c030203040c030809061606050f01050306090d030f 76
    0x100510b10b800c0060641d0b40c090301c141c52041c903540c0c4113103501c0b00c4c04402c0c070080c440d905043c0007141c82840005c40032501c0d02000078040d40d810140b0040400108409000ca61215a82040c91500c03a04503110460749401100c0c040360f0b05250000d90a4091042d071078070411140c0b00045003a0034081e200200310342a010b50700307003040301d0001e40002c3c0d88102d019864504900c29110704010480342d0f543c00800034071120034841c00c041400c00c940c1c00d0b1203070015204800e903200005181c400b040f410046008010681d2582c66100d21404900001407000d42d00417620907404400c204402c5000c24010aa0002c102c00c0500d008503145811468000c68042e00361890a00c0c000042400d1524603041074015901001000c0d403602da640421070202c040340c0c030703085086041c160740703841405402e440043c0200e600440c0381d00040d0382c0c0d14200c2e00140c544800b60442c107940c0380b074088045c04048034500c40c06a80c0d100002514240441d0440c41410044042c0c00a0b0f100020305800500c080850701c296160f440e072 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 260381798 1250 260380548 260380583
    0xc070b0109051909080304031205010f03060b0409020402130e0a110904150e070f1b0f030c1a0a0e1c1218080403050c03100606091211030111090f010201020c120304 72
    0x104204401e80212442a86c902d81420054100d61b006091310740880d14000040007214000c01000054030790050001ca1700d0114440007601030181c4c014041d41c00380c800101e0b141c4001004020740110395a186002c146030781c4076040301d0304031041100d540c40d10803400c07c0f4604031407415510054050a01c501d521a03901d85810710702101c540c048560201049000c518610129004031960f10356440d114203004a0804580d0340c1249280030b00b000030240440103084100f0030229441e084102030b9000c5040b0614500b0030903140c06030514092810607401a2034450701c5105c0313910080c41c0c288805844000606105291000003007403030141c0ba260700043d40400c84001540a03008000131805180204008845007040500300b280c41c64400c04214500202005115007003050366046500011902030842c40c0d50a00c2c4028550000d41c0c1c0703601d03520300700b00c250080b8203000203440b004c10180d4001880b1112940164200d2140e4070f0302c12599030104407a82c1d0858201d0008544c810b10602d29200d903440c000c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 260383048 1250 260381798 260381801
    0x6030f010f050601020c0a0b0a200d0c06060503032d1e030109051006080c0f040302060706050405190807110d050a0609021f08130602040b12010e0c070b01090519 71
    0x6142000c00a0389482c20b000043d03138108032070203100c1401c0710045401c1e807030f2500464140c40340c02c003c0c100340042d1081078441202c0480e28269040400400c2d69541d500c41400108014242c681c03c980c03440c0b510201107000d05000080e90304148160718141c1c014043d410f5404148c041a146025102c0d0703081100e6203070400c643c109220b402100c90703100c41d100c0d41030814020580e07c00078001c15141c004c1c94010032990750f0180003681c0085204640503030f680b00c41288089a13200c0e0b0340020750804000100c42003040f4040d40070303a04c41d130301410945194490b200000900c1001c40328018104103014412400480c42034500601e10302001001002008110350300d032810034403140c105440c203c3e561650740c800d5060404201102d030740700103006254903010403070281110f1405006241006000c200c0ba400f0004240d0403100a00f102d02c41840d00c941412510030340310f07030b024080d001042407150080340070760300000240d44106510103140032841c3e003040201c20050400401142e414500e0360700008501c0e000b13 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 260384298 1250 260383048 260383061
    0x405010c112a21060604140a020901031808070308070306080c01050f070c1d06042a090e151504080a121b120806090105090117030705030a08090d1107050906030f01 72
    0x881800f400c3c0c4024101078101500101014000d6044c6403112604d101130303669645d40078060310b10046e02c40c0480ea0040380103240b2284c492004e90342d80c004000601007140c014003c0d26219079185c4a07155510a012400e8413480c0c420000e49a001305c1140c0c1c4150301403000382c0f40c00d103111116a42400d00380d46800d44001c00310782c4189010011844010b103414900f100300c643c070400c103403014058900c64040f0042d51180d11440d551040e00e0340882c480440e031046a4460060020200b01222810503940400451003504031030b604c030368800f05030a10202c0d48181941e048a840360064003480082c1d8541071800041200500100100c1c100c02c40c90404030346d170010105034042d00300324179100613812000d1310144010301140e01c07071020140100202d546101400c0e0541d2602c44550b150b96140c00206803450060450040c25408003298811002d90300c000028801d140b2107089403000c071101d06043e11051103035850308071240c101041c00d10903414040d0f005a00070f04041c003103500030340c0e04175500e5086445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 260385548 1250 260384298 260384329
    0x13110d090f02100e0f09070333050f0a060f0c06020f04140402090306040206090d05010f0e0d050304030203040620012f0a08040f03030219080405010c112a 68
    0x2111281982000342d00c207601003c080c2001ca80d605030344c00001c1c10114a029620784030790801c1002600e0580b00350840c00140201c0441e00b1210001800d8201000441445411640c1d03402c0100007814a01002080020300c000742400401c82e0414208030f520b20003e007208801d00c41c01c441c00c00c00007840351000309010038214445a44071418814110601006200c1951286005010010040d40e0100d020f941140d4126a120f94510307007900480c04000d81410060029464a001c0e03e40040482e00454040c0d2130742d00130344003400c480300d5056072180819039004d00103901c180300901c941c43c011499012806425004500600c00c03100c119402e444407030103080c041c3c102c0300060030009a10b001480b601d207a68075080d039041616400004000180013031020b840510405a0141454043ea04861078412000500d0750246500d0300090a0724038250349c00c03100c540c60000c01d407851611910f503807401a40f0b2840500340c050b01e84011000b42e400541030404012504480c135524070742e200d42c1c480c82142c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 260386798 1250 260385548 260385563
    0x70207080c040504020105090d020102011e020c010b060c0d08061306180b06090d030e150708120f040f12120c03090309120b0402061c06031a100513110d09 68
    0x24186840a81454210001140518100300a000060ba002400c1d1200d203001901c0c01c0780c449c031082c00100e0140010300c4804003030181c04481d00f142403909800800e07180305c03071038001d0114241c030005000b624842d081d14240740c1c0d08a20100c1983c0c0344560040c942041d80101100b046c41405c10720001102c06031350008222540c03040303e4001c0d0442038000c110403150b040310064101181b40000c200d42e00140f100c018200841c0520412483e920440c00301075a80046102a80702e000030b240815103a0f20370079800b50801107200c0012a800c00310001c40e4400e13640320300903040360720301541c0d50001503001d403e010090100d0105169003110f80c1d44680070000034150303404200001181005090713554242c0040d4481956800104045411008016006a1f06441048e83c0304030f044100c541d1140225010826681840c00c00024040800309034000781c20ba41013084403640b45d14010181c4c0749503030704c42c03507800900961803071040103580d134049180c0311a8180e0300c0b45082c0303001a00740c00f1a162190200d8010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 260388048 1250 260386798 260386813
    0x1305061b0c1005030c0a230319050114060315090f060f060c03160525060314040c030201120f0908040303020f070f0324020d0630140f03030702 63
    0x4000420035840520402d403101c25245200c4031000701075100c014916078244000050b00b0309600e1040b4542408418a84580f10703408060310903015081c2d1003540e04d00881c8510144e101c041c1c015520074a070407580c01d51842e055050301c000a108440d003004000401a0144058a030348903196504024440c02100141c80d001c0d1401c2c80c200002064003508180c000d000c00d00002002520000841d1a1400700300c820699002c0185000351030100c0500300c0d81050744841854002c22060205144152101510b041c8041c2d000281800c10310503044078064000030000c0c0c01040035502800400d040e01c0041000801c061041011080c1a02c8003420201c41c0e8050008040040c5075042c03054540e560b01d00345c003401d50a40b410300d248002c51000e02000e410607034025000c80303840e00d0600381e41c0113001d4011020b540310011100e20b03900500e520703c12030796203034400240140521300012500c10088443c3d12514201c4d9015180c0658184c030209c4010094440c00001e4030540c001040030354484d01c20755000b00703541e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 260389298 1250 260388048 260388097
    0x10c0209090f010c02030a090302091f060315060c050a11150403080711040b030d121506051c0e12070809091617060a03022e030b33130506 61
    0x131251001d10000440d00244810350034540d00c4810784007200d0b0100c4e80c440d020b48684c500b2122401c0c854088004040d800d401c0000c91036099000f00c203282003110a0000b00a07580d4034141c9842c96220401440c581105075018001703405055486070100014006009a0b100044240120741c000d0700b027030b03c06140201d4081c040100326500180000010340d001e00078011000080313a07444981e245041d0503c41489442100000542e1148100c2d40307070103103a04405070f40c1e128080c1c5a640312100746141c401c4800110718030300d0384a020b0102c8000001e4002d0151030480d40c1c08080c80c1d0801c13542100c01c05004c01c80b4604507030303076618a180102254100b60a80c801d01d02806010128403e407005d011081c01400c0011a40d01c48103020220703901030b100c0c80880011080103143c00150585a403030000d060030180c0700c440c1d51642c8100410342c6c09480070f028040b00c01000030240810701c400101d2450354001d031901c8080b1354402410781c0440508003820901d0f02c80000a80580180d05040c0d402c0e10200c80e148071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 260390548 1250 260389298 260389301
    0x14010b10051206120d0c080906070b0103030e091b070515010303050a08010f03020d12050909040302070801062124060b0d050a0c120507140c060901060f0f060806010c0209090f01 78
    0x1c1111044590303070113005070180b4864903042401c51501c14410050501014002610100c8410110040c480d03a80c2d25603504d4281001d0300d082c0001d8001030445141301d072090401b200300030b0040c4940e0401c01c2003c50f00b82c0d40c014041c0c0c000c20040300e49001c1da0080750803440c500c4031080d01940c403d4441c0c60b00d0306c0c40500010b010200c1640400400701c000e05041015031117541c1507038991b41d04903182103c0c81262010948881c0718004100c3c0c0c0100c0c01104000c14994045020816a011040240806c545e03403180d10262041c0e450300c0c102c42080d0b51010304006410325480f0744061421501e4488900c0c82841c1000c101d9055a200e0f10420800203019040c503841441500d5201d02c4042c4200300d1101c031010b00900c4d540302e00121010080c0e481d404211302901403484207004440d4402c05d160342c2c0c0700c0110302c2502e901055031a03100c41d6081c0b2901048030101d0b5820354099404c0b14228800403803602c0800c4400140141a4a0520504c8100e884c0581c40d550080c0b403040f00c962006081c1c0103e070401c15070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 260391798 1250 260390548 260390551
    0xf0207231501300c0b16120309050c0103090209131403041503060e04080304140304050a08012a0c08072607032c0906040608060708011e030b010314010b100512 70
    0x500e40f54081c1002070002d0721400729001540d500114464551900c01200010b4025a00300540400b49a801400c2e0383c2e940354104500f410b210303c0550b01c1012503100150141c0f0a22407000354002c0c0202d000a2a84502d110b100300c8890160701c031030700b034a40b02105190940c1d00c5604480340c2d580d0590001080e4a4040c06500001d0111007540e0a09182545403c8058000a00001c004403a50009083d028500b04203681c080c0200074080020f29039078580310340c02130081c800c4030303803000003600483c0c0c0700ba912002440d4001811620b52085400c900d0f0f94606003540289011a10300c440003e01c11030328504503401c400d40140314003255581d90120b05003d441c1a1111680002c0b44414941d61000150f29025040b4120b01c1a20303141d02d0b54031040002000b5019a0704a1f80340ca03c42d9004004001e0381c419500c3c0e0481d80c1c0803034840704d81f09900104019610f554040070301418a07a8004000017503040340105000c4c121381000240c000d0282e40082ca0003030114030745500042f80030414444004071f000106 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 260393048 1250 260391798 260391869
    0x21c0b09070b07080d0207020a1a070605090102090102060714070f08070201030e010e032a060a05060901060207052b1218170a11030717010204090f0207231501 70
    0xc0f030500e02180c1c0e0351507051050b529080201600495a54115142c480d6014003420045119015403041ca039940e206640000b20244e41103424600455007401040c800c80d0070405041c1d02524880d90380c5041030f01c420036a0010b07007a02010400000010616004a2014880c481c000d0250380d9461400010180c0700c5a629108690b450491036020b907280c000126550488004d01808425403e1100000203a175844210f03001d5008030400c06ca245010f5500c0b00d841007404a80a2000740d888540403651002e80740281034010318081c00300804412620136036140081d04c3c0c4001d5581c1d2460340e0764107404084280b84100400c81000344246210070070f03d00d090103480000e51320903002a000d48031541d541d4085502030308103102001b810546840134800100030740340c00181e05c0c3c9803d5410420a0017580a88074403a4014030f820420a9010300c1402261200d80e00440404118100c604160003052041007604441d40309038041842e4062021004500800d014084a09038150241840c040c501200c41c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 260394298 1250 260393048 260393069
    0x80a0306090e06161103040e01080a1703010b030c090a0b0a0206070905010e01080f07030b03120903150411040c0201020c0f072c070e011809240b0f0304021c0b0907 72
    0x20001226421114041c030790003589000c4890303505c1801030a0a621580e0401082484039100205a1200c001109042180b1a80810b941d40c2c80050746492117000a000302500d080302000458118682c040107031021440080002d4016a51004003000c00d83c0300030240703130160304a101040710403500304c1042c10042c0070a0a180c141c0c003ca690009140c0b02009042c96001c51961340443c9143e4480e500c05100d03204c0180845680040e00e4030780814580014400714842e1041e80503440e0411059036200d4000c5a009003410b03441c4080c50200006405100c20b1b140844d9800d201c80209408100000b00c606100d100242c6180d0307051a108c80504801d02c000135580700e103e0b180d559050503420808590100c00da2401c1c0c0400004000100c4401c01d007210141c03020322240b08045404141a40b0840c0503600c070303109880030304000800400301c2201511400c070380c2200610070800c2d5040c0e030301e0040d03500501c02400300e5001e803606449030340c000d01d43c11426a00d040346441084080e1030100a90809803001045 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 260395548 1250 260394298 260394301
    0x30b1e01020a030804060b040c230a0507060c0e04020d02040807170d08040507080d081e0402030d0302090303040b070506040308011a160f05010c03051005040b09011202010c080a0306090e06 83
    0x42e54a41030903400504011410000905025041d4007500c00300703000900510404100d2000101844442c031980312220b0b002882d09204079080c00c0c1101c401010540f2014144002c0f80c407120000d0070307134078184818013030704500350003040e80d5901c0100300741e10800200507292400c044070b0a14108560b004900400034000c0c182009000008442001a0702481d0000480c0d445240c0319050200c0c0d42e000300c0c0c06209a0010303010054100c05441c0c45500d030108007107208982e400d41c2c071514540945029406402859400c011079100f60004d0003034003800303400c49140554070b41421031942e011417002d82e04e5400082c10300003015440b0310214010151419440c10440050058a44500c5101c0c2801c1400c200000c0300000c002c2d6803281c1c0c0380c2d1590803c00070807981c00401d5028016001c2200c0c0d0a070f080e050b00b500401e09203014411581105006083c011060b270806101480101c406503059060082c459000000600c40b44000c1c040e8102654003ca10145080c03050000d4446224059401d41c02490 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 260396798 1250 260395548 260395609
    0x12004050a030f05030706140a0b0117070807020c03100606020c03070315090f120e0301060f080a060203101502070305060f090607230409091502040609090c02031306030b 75
    0x508a8040d20382000383c4a00c10f200c1c9140003440d40c840c2142c010511428165290540d8254844641c41001800d00c1800442802c400448070840d8182414449002c0c0c20b020400e018445c0716240d42c80041401201c0800b41c1c0340000034641100403201c00c916030744900083c068250705025070040c14505078000d00030141581d035003440a103124440001c3c140c1e0384410000c2407000c070340100300c0e0305500030401100350118150014088020750115034003d60070420005411a19041c3d01c004683c0c82d00701800b8018041d640c0c020282d44003030300140a2001c01c1d0b40108219050088920402805800401d101c6156280aa00f40400242004074288420302048042c0801041d22940842245040c45a0700640920300402801c102c0300f101d991000810041181e0f85030ba400743c404c1900540c01d01c6920812844c250099106600400d000240c00000c10440c900c5a50007201040c440d900549060203004001c410100c0c3c0c3d181e200e040040e8490b4003104040c1400603280c1411360188003481000c00c004d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 260398048 1250 260396798 260396809
    0xe071a04092a0e011b0303021801020c030d03050406090b18100606090303230c010b0901052b030c0b0c090f040614010e010e0d0b180a050d0c02060c06010801200405 72
    0x550055092014103e0030301c2c402d03846110180310441c1d4500550090304000d00b4000c00a40000b1019908500e600007034417100c0d0300000c0c1aa01202c001401002c95500341e410890180001401c03c440351a00c40722038100161112030003510609002000c040c54200b0051114a0802081540d800251420805001159100c080c000580341c043c10451081300c0c1c03010281104100000741500e081001041e090001c41d81904500002801204c440315641d888030300700102c0c02c0391403c24011703000725411405428a0409440f1051034064288070407684000d0701c2d055081c1104454450003c4c60000d100000c51406e100e6680000d41d003620104152810086041103a0003500e02c0c041c180056000340d007660b68414081308a01c2c00c03010308210602d00080c503101030802010b6440c2c00d80440c2a8105008c8250001140d203c0c654004008082c069174104050f18201075005090340c001e50b0400c59a0a071100410005000341b00140000a1f81002103000c2d49012414a07404201c01c1e01c1044104100c1d50760 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 260399298 1250 260398048 260398121
    0x51002030c06011e051e04050108010c022811120f010203060a0608130605060604031e0314130b0706110a080615041d0603030403020a09051005060a080a0e071a0409 72
    0x2e8030300c4c082c80c00000058071b49041c0f08410b07540d4003500f03002c0041442d080640180c2910749468007142c403c2000b010220540450198480c40310b0040b4a0803500031400d0412000d500000250118100041d05601d072401c180d02146070a416a400205101070340c14080c0f03d0710000c004604e015102402c1903400304183c080340c418041e100d41d4641010890a039100300c105c400640e40f149005503111100d041c01c010b07044044405070040f42c00390030004c0542150700200da0a6843c21954407000c02c2c140424802e140d003200c01d054400a64849042400070840001424858003e0b101d1481700e04d405410007a440c400c0700c005008010042c84108506541949068070448440320380601a41e04c40c40401e1940c00303141d00c06540071044140c0080c640c1d01d03a40c1702c240517079440212003171404e45034420311483d482402071080010b40a10001030800d8140d0344240ca8501c2039a003030f100d0742a52042c0000103c0c2601c0182518060006010842000c0c1449a00190b522640e225512294640c3c8030080034041e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 260400548 1250 260399298 260399309
    0x1306541b05010f0e210a0b0a0b0402190804030309060e0307052b08040f0c0609080f0a0321140c0909060d05121e0301091b0305040503030a0b040204051002030c06011e 73
    0x542c000c800352418244015601928554001c4400107902d504002c5c1d07d01e0020359140386c45615200e40340e259810036000701c034400d0242807069032030b4080c90142283c080708014401d0b810181d8685031000011442d0040324105c4001d40300039070f2149802d040075401c11580e8250215000c1b0542c036400101d035034850054010b080f80d42400905507030746050506072038040d107a0007000403030301400104480f40c0002c0c0304820345d01d100e02140d00f004c080a0074250f80d05a5103502a011a0b40703000c1301022402c40884594165101d400003144200034400340c1748010100395600324102c1000300313080382c042c14030300101c039400a0115080b0b040201c00da200c003502d5129140b074000449600103446c640f1340c0d0110052802d02081070001607030701e40c5e440003110000c100c0810411221181c4c199140e20070ba12038082d05001b940c03c00050f6166854580d18100100100b01c18190416001c2c440040c0c0c03940c501c0600d11200c0740795000380d9900c0001103001030401405802c20064451425140c1c080e00f2959400c2405030340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 260401798 1250 260400548 260400559
    0x3061820060408030f0703020f06071e030902040f0509011802061801020a0f0302163f0b090a02090c0304080a120e061306541b05010f0e 60
    0x80d203010129400b44641c0e00040401d110004801c410700103004d008250300c6010358240c44d24182208503407500c400054801c80000b5009209110081c000402110000d8509003400190400d40e503002c039040c1e030100565480b645985400b000b00159080c01126544006614080b00e42081c40e0b0000d44140145a5500603042050140c1c0403d079000300000d600594002080d001c40841e680780003507076402d012000300a001003c50000403024144941b090f49080c500d45524203081c40901030000e0340b0b40e40c079209020820040b0100011500b0f4140050050f5152805084120168014840c0e82e4601034617103200d90300204100f0000c2461041a2a0156180d18240c0506400e0302d101d00050103030200ca6056501030030050202c803000034003000808a1160100b844040310b400c20b022244001c0b64034007444407203680c0c034034032090b48464015800a0450415840340c0044050181c041c0b1104000c01c99211300c110075910030040341d8a8a0000411007468020303000081807900400d0300f0002500c00f805075 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 260403048 1250 260401798 260401853
    0x13140c010215070201090b0f160302031608191d061003050a08030712020a020303090c010e3616030b03030405060a08041406070e0f0405090a03050c071e030618 70
    0x440c13003900000c55064010025400301c0c08c01005107201148203990488500702038518400c040c0c0d01034000d0b648680c03180c0700c04240b540f40c104402c0c1e0b030b140402060314075546182c000c3e2003621078444c41522402c10342d0104030b1403078410441c1c40d1850000d000c0d08814030918000400c000207400042c403240d04550002c0040d45a88580900307643c1d014801648900007800860080d0060f503000000d903101e0b401410480d006800910010b5070b20f0040001c1c010342041d01aa030401c0c01180000541d0300544030030324000381d12140041825030301042031380c900a59180e20b910034480c60380e0501030030307a00386811005145020702e804001a110300c540c00c04c07a002e02c4013400008092000040c450352000101405584c258500f00100130001c2c20088a464422400b41d0fa40d8101c41c2043c2c072600b44149020401170100004549058900742c100110b4a0701900c01c100c00400c1e074246582015803900d242c0e012a0411a040d89008020f8034900d40d4445659003984c814000402c00d01410f00300c0740c22042200c072148 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 260404298 1250 260403048 260403061
    0x60d090b1504110c071a0f0d020304020f0a0e070f14030907080f1c0807020a0507080106090e12040303050306060412030207031a07020709020c01090f080d0509120d050a060e13140c010215 82
    0x11f0040d011718011020010688041e00496a0000c51049200b107590b8000c00116208200000031640240c903403120b201d00004210b5809000c2c002214813081c01e110b54034040450311003085a00840b0030b01c26075001000c0c01c21011b00b040201400c0561440c0240800200c90391800c41c2c200c0c06004108208103504010840c42030091050a18041d00a000e860410b0f40b00d03d0b4090181140d8400c841c0e40310314042d4540307a03200c408204080400502581c5034500b170310310345003111640c2020308803e41c0054108400034a03941d809441203d00d80c480c0d0003400040d03196080c803100001c4078400d81602d011050041003a0b02ea40400d050043d80c1120400680700c2c0c201034403042c0108010100200202694042d40b410321001c1c00148c030b240d000104040c803595448440e03041e01c44000070008550b502040c011501c201c1c440360421a40b003030284000091982d03a0340c2c90000440020b403811001c0071081112901885680e4030700c00d81d0304000c0d1000300305c0442100300003076031041c0d00582e0f40c1e02d0000300c2010414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 260405548 1250 260404298 260404349
    0x606020a0f03030b0d050a0b010501080c04050105220503060f04030f0c0b13050709020f031602070b120a110403060e010f0c0f0309060b0607050706080f060906060d090b1504110c07 79
    0x151745420008486401c02c040c502a580414280901c6010842410009883d1070449044a0968034180d503600c2c10311004000c0c02c040514036104a00d03200d18070180201da581c40410a5034800e26940c1b00a18040c1800e0802a00000f03850000104114650030410301217070ec00c1c81c0d515048a6a0030954060002d6400c01e82e040100f1500300503680c80c0001840341ca00d112180181d805040c0034180003041c0b0124603000c2e40d46030164031680b20710313140901c041d0541c1e030f185040155108684520111304850808140700310395100e0340080790020350707440c035034842450244164401d0780310b008000c204116071404040d1000c00903c0d2107074105a1500c06040c2006480e030440d00360004040c080710788030a620b01c1d15076218195405202d0001b10243c000516035161b105071701e409908003070403205503a02c842042c48040da200030060300c2600c3e124001040010038880000d8811501320b2402c174071009003402084259031056000c5402220240300c0c12020001c00f09850040b00d82c0603240040948880741c0e09103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 260406798 1250 260405548 260405569
    0x120209070e01030e0d090608013006060f090f0513030e040216050105010b0a1202030c03010303050a0c05070306050a06090204230a0803030408030a06060203030403022505060309030c010606020a0f03030b 89
    0x131940602160b41910755004841310046c5d4801b6101c1600585e00c0301c4a070307008180e1408541e080441284c42190b061441e6140d40032105000f60030100d981d6488290705010740865901c14601c2d180c1e60501c080c140c130011700c10706800440c0d04036031440c0e9050350388004114103900114203109590000f000c0044000502000d40d0169200c0d009000d90b6a464110746041e41021401034049809138035000b00d42c50640c402c8a00c20702c03011030007504503400c5403800c0303a00342c10001e044000e210f60450007802058081101000a40c030803000411035242040701001034640380d0380f00740450f42c0140001c6c13050354801110394000c0d8807001c0d40841c2010907100080c4a43c0c00e5a809010b0300d002c000103100078881d60310010b5200311030114080c031510f035030340d101213a907844122030243c0182c11600d21900c0110f001c0c07031000209244000c8444503141c0312000502d00b50302c2624410358550001074001c600c0c41c2d00380607030401401390303001030070541e15a62141081d0250f8540002c00701566502081c4060341c442e1801d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 260408048 1250 260406798 260406821
    0xb0907030c1214090c09010f0b1e030a05180d0c060b0d0221161521020c071e030c1203230a0e150a05030907031a040309120209070e0103 60
    0x500801070000600b0780c1401d020f9903a0761340c40c014419105480d041c0491840c0c101e804151880c1d49080c0b1304183c003c1d00713410840c40900b03c0311129040b02d034229041d401640c015407a20b80300085c40e0030221448008004900d038103c5043d0000d48005080715000f800308080301c0c1c0c105d500450b203002030390b0000c1c001d68903c00000350320190301c00f0994a844100a0b80d200a40c00401c2242c80400000c0701098ac00360540c424601500360f02c0c1e450362802d03807080300c5d0010040551102c071440c0300d102d11080d1040c0e810100b5208032503403007500100684a01c0c542c090800c40030300341c0d9040b16242180c0381c490b000000c502880100a502c1003060082500c6405141152032841e8403000b0000c8981e0016403480d440801c0610000d00d4000c54809240fa01881481c01100c2040c2c0b0580b8140d19035000750750541004006014500404100101042c290303c5001000555440081694682850044c00350802a005245081c2c0c04140580050b01c81150598100c034460402140060340c440049000e07240c208440b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 260409298 1250 260408048 260408051
    0x4050f010c18080c0d03050a111c120507091e0e010914070206061003091103030d02130e10030201050705031b01020903070801020c030a18030b25030b0907030c12 71
    0x45589160b0154810100c12642c040805400c1d5540c91859501c4c101c444200e6072110008800e007000901990084c80c0e04049400c18984422080c00851b00b820f500701d14100b400b0f2454484520398691004c400005000007070380030825030804c600001c040322401d0255140011030750180c903c40440a134034540041a0490f00c02e569580c4800124016000b610001030b41c2c00c103264003091040d4004502e043c030a00c400380090f014084064000c030081c00b46031005498000b00a2080f02e0350382c80a0006050f015021480940d45103403c01d22805042c07082d501120505c00e00780103005280030b075204008200c9409190054031114503040440c150311407550003818504c28565901404041034000d06400380d012000d448481e642c40d03086600703078840ca00b415222a0020403000084900502e00324a0652401c42c1190801e900c0780d580111080054030440d42c15030701800500100c00e00f0403003030004560140307820301902224801160906602601d080107040d1603a00d031b4521a4410004421802d164550 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 260410548 1250 260409298 260409311
    0xb0310170c040c2309040204091a03061e07030203190f15050406030819110604060f0507110a12120606030203040b0f010b030a0c030221071e02030a0804050f01 70
    0x1240c0c1c0d00d1000d1528140070714145480f5081c454003481019440c0036042c8400c5018000140d140e211036801859040c0d03006900784400f0403071062074440d21100c1c500d00030704808044508010940791150042c56400601c004070030042c1e041a50a19407508081e0b1410096181e0b1030703d840762160203600c0c020440d035461610a51b600d011042d9000031303240e1401c2800541105071030f141400103554050201400110041100140140f50b0680700c1c0c0906d1110b2030010b11502c407882c0200d0a00c403082c1ca054405a84488103680c141c8094402c86030000342508203c4000d0b541e21039401d4840030101c5001e8011001c4402c454266801040b19a02100d40a682042820385a450142c02074009035019200400018009110300b00c4903c5c49030305030340b0341c801c10500f0742e03946218280c0985482020401055000d00445e0304665100c0440b800505900248500602d001c0a00511680c1c4c18010408a910f2001c0d046034201d401008a550301055454000003554481c1401c501d040440341c000f26a9610708903 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 260411798 1250 260410548 260410589
    0xa2114040f21020a14070f030c140301050601120203071709070801061202010c0b0a0b06040306020409200306040e0703150c020d0f050d09032606030d05030906010b0310 74
    0x1501d0000c0c0740302e24800300301d54210741d021140440010a003100540d102011030702c081902c4202c42003400310b8131401c9820361900c4440740c1d64031180a6004a0b000c10442005210070200d00c2d518101400055001b0800f519108000030541000507800c6900103a0004c0424030f03191168000d1060350316507403801c03462810100b520b01c0d0b0301c401b28468000103510b041c40100b42117401d80b10004080d60140e60300340c16843e61340c682684246014006945056442c0800156600c40710040c00046d4041c3c000141c8072803030600c04070190f07a241c1c085038410a14020b03481c8011306426054a800a00c00d94000078800315400b03070389291181a800107003c0d800a034060301c0681d083c0c2e4002540b0080c09900b46c4038940890300041d21510f0501086d100810001c0c0000c03034802c421b941c04140c80340e000349050344000d001710b0020203e0301e20720703c4131101d4280000c0c03c00060703050401c0b015208080f6440c000e459841c20002c12078980070180140202408000701240c400074000200f0b10107400c0010000a50882c440c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 260413048 1250 260411798 260411813
    0x14120f0d020d0201051b030907080a0305090a050603061e01030f090c1511060a020d0912020703030f0905060301051302091305011d041a06010201021c0f0b060a211404 73
    0x8600c400040c410340102074401441809402e0190f21402c400744240300444100040f6500000d0001d4803c1c4910140050320080c100034000e41d49009491b0030303a40fa000d000a02410340565000075010700d804106010300c9486182c400000603050680f0382d9040c0c065540102c0246c10b04d03505140f85581407294100900400010481c01c46188094000c6400f40e030740011740b401039030300100150740e0f00444002040290b40703030000c05a0303120500001402c0c40040c0e40740314407000d42c480701c00c0060784000d0090007096081403001040d02c40600b0034081240c50400020301c1c5200c1401140d008011010030020003c8160301520903c000042002c192070b070354603d104004001c248200c41c03203480b160903620582d2421505017800b072500400305042a01420072003007400e41c0003034100e904546d42081a11201110061344141d020038141010811203a014035103400d8510070740609104440401140e07800e250000c54210100009925010301500c0801041000304027a8103c800481c1f0484208020071828 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 260414298 1250 260413048 260413063
    0x70909080414041b081312030c1218020f0604170d02060f10090b1210022a03071b0b03010306061809030206060105072918010b0a14120f 60
    0x180c840312a04819107400304415904000652800d4101403004c0480c91032080003d20b90000c1c0700341c00255170151030780d9070700740c0fa150144203071000036980c0f051405034640c841d50024400c41c80001c24000d81c2c00030103201c411040d003510000c1c803c030754605000805454038000d9030f0042c42d07440d1070715045945051101c3d458244c0104503000602072540000d52613110700b10f0b01d80c0070b4002c8031080d1141504107000c80c001440c61003c081d0b070001c2410f545a6184070704018402c000c0c002c0200142e01c0c0c400c069a07100c40c641079652003021600d00e10300784107600030300001940c0c00b070781d084100d101c502208800305101a0a00c2e8000e07000b032542c000004400c0c000703923410000407205140c4008030700b440c0b6a50040101d85c020709000300140c02c410040f880c59849107000d09100390040141340480b030310740040c0c042404183c03050018128200c0707040003400071f200c600c0041441d000314001c2c000040d103080015006c502c0c0c0c0c001c2100c007402074080140191a0042d074000b0541c0300404450700085003001c1c16a80d00d88 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 260415548 1250 260414298 260414309
    0x2280f09060e09060f0a0c030902120106060e06091509121c17060f240c01090c0e010e062b0312060801020f030c070809030d0509030111040806040201110709090804 72
    0x480b00801c84840c1c000540900c14140f00407403418540710140760340081c101340712070f8000b01515510b08102517951020712201028602000041251030400040c2c01118010402c6101d44d00038405901c1640710782c0503241e0040113500c01d0a0341d135071460300014503096418852003210720800141000091085641e0702100050707440d981da0761404d1000c440380fa030601321480ea170070521511500d5424100686800c600d90041a002100d40f03140058629064019484c0e482c500e80d140c040c14001d0011290403074018011545110310b03107606041e141c0090710740c00740041e40642c2d42c0e15543c03c010741928047d00c0c14890511040c855503400740c02d0060901c07844010a03816240b5010001802600510858458036036a003421800c0da6500b07007000c2c006d5000903106807900e80b01049852207541c0c0c1480703c0d5003c04101d44500b83c0320b200080a02d421540f2101555401440820051150350030000783c1d107034000c1d42480c0118072641001d49090804540b5800103402d2411300248034104460140944259107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 260416798 1250 260415548 260415569
    0x2030a0201060b07030210090201030b04020d0506040c030c05191403181b030c13020c0105010b07030f0801141c06050106020a1a0708011208070b0703050618010302280f0906 76
    0x1070f22004801c40314410608010050380c41080040d040050f00c0e085100900e0050500007842d00d101c0f00400c0c01e0fa0b0100ca071481e03681d60349004214891500307105010380d0000d1807804100300340755004090301c64030490a941c0b64154181d03151990840c41456580141c10703101c07503084d8803402c040c0c1d400c40f140707501c424030000103006e142c01034625008e0041e80060034600003402420011801c806100500c4407041903030030159000c0018119601303090040740d00030302c41c05e0324075a610b0b403250400810b5245150382d244100314034400100182c000c58021204a40d000715555914100e030b02200f072131244900070008100c20b0400740000b0746250041140c0700414000d0381800d0803040102450103800e10215400d0000c01c0002c0700521075480e4064041c400381c6c0c8200d0006190140a4842c4211500308440520000307481e64100f08160411020b62000c0c201014010b00b882e504640c0001c2c009294403030451a24600b054410038540091071081005018900c4d000c24165110324916000d805035014200001c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 260418048 1250 260416798 260416811
    0x90c0f03080f1347030a1d0a030806030607181a130e0105280902090312040308130914010b0c010204170f0721020d020a0510080f07020705150903070f0602030a0201 72
    0x356136090551082c20281e5180e899030f036881c1725500c000c11001603179208401c1015030810001138204680e030000d0f80207880b402c20600d0200201880d0410091800c0100100003e0b0500395022070340000301515007214403103020b610035030342c810b04a003c0c20308000202000c0f00c1001401814031181341d41656010341c0da25a80800d403a203440e07484451610301004c030525103a000c0203803e0155002d4202c0c018000d05540d18210304103155544d981050b003060300d2003030340080c2003200d030038403000d03000001c1c103128100744940c5003041d00420b046c45051051490789140050300b03200c000802e50480d0b0140080c800c000034100c00444100755519406203425001c1d02c0782c030308041840c40140c1c09046401d00000820303002d07204aa4280f00c2d82920603c41260801c040c40700c01301b1241e845e01c0141198880c2d50703440304605d2525804922140d00007819690070f40d000030b6000c0c4103944400820b0700b8030a10b02c0e580c1070b907a0080c200c0401c0c47c100a5500c103442c58208504049125903010000300222207081c0e000b1b1244 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 260419298 1250 260418048 260418149
    0x2010f1403100608010803120a0e0703050f07090b0a06020d031d0d0801030204050a0e1b060d110d0f0501080709021c0915060e4303090c0f03080f13 65
    0x341d10480420348460702c0c80100059900d0125041085402c61580648401682e03941e13528ec81d09880c0c196a01482d0031910702031102c05198800e1140315001124000c40c0d00381b4041c0041d44030f100901101c1e040503201c0440c03020012406041242850811044a100c584c0d200001008203c081c00304034803680c14640480c0300c6c1c003500c2c041d18055080c1c03c8050081d41c09042d2040614412100303c05400c50024000031084070203074410b0314200c0c651000e082d940e030b0b42d160040100326900382e2803500e01c0501e070400500591100066080036180b41c7c10005036218004000800b18003d01c4200388040e6084c0511036082150300303010401c03160216281448400d03214180b101210345d0460344a0742c2040b948050b9080c4c3c4880462400d03403e44030006154498680100c2194400340c80c861101c042a02d60701000b042158150461005141d04404c0c50740c11810355450421510036858841a0000081041340c054039120182600805800c601c0004284c408000a8001d100e03920240201c2080034040110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 260420548 1250 260419298 260419303
    0x2030a090b07080417010e15060909070b0301090b010905090703020417070b0d020706180507051302031506070203120d09020f061c1a03030d0f0e0f030702010f14031006080108 77
    0x340b03140e100a0541c00c040c01c4c0f84e00c0c0940784202c480c0e5045159240c10000910303c03010b101d400a10011104200e845113844014400c40d5070380604100b240d40e00c010b00401002041c0300075641507034102c61001c00e02c07039071040040369080e80580144d54003003d9142071084994065000f00115820f1101c80561a00512465502e4204e44d2103044550f080412442c1e021428540c0200581e500c139000024a144c5420000100b01007144401c9445600021050103503113031510508541040c501019491450601c04809a00074a0a2814000c40000c44c00718115541071200104440e500804151100401d03510b03800901014031003a801155100b80603030a42c1088412115120f0980120316485010155110010302c0f0031a494280d100004121401036903050008142c03907410740001251642001030400219080b500608a06900c80c0925201860001c0140d07015a034090a28148540074031300c0030344404000c11030b40300601d0000020480c0c00d11035041110180c03440c03075459031030583e2038620321a0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 260421798 1250 260420548 260420557
    0x60e10080103060507050417010501090f061d0c0c100902130b0108060d08090d0308090606040b010c0b0a02190c050c0415030213021b030403050c01080c1c1b02030a090b 74
    0x60000c0c10510040c07012454940007582c20403428903020386481d560300440b82081e5980070603ca001d03511240100110a00350285001e0350802c00e4041203041d142405190300d5012000380318200750410342c0000c110300c08000c260343d9001c0c07405040d02c1200009200c010002c05102c20201c0c86507040c80444078082c100c6215015200c8010f2311462800d4503410b04022003004042c0381103407014000c01c0040360546810341e85000441c8070b601d41c10024103041c681c0a0404400404090085185c00190045683d0012900301c08582203c407641c101e03259040040041e10a42910020400c007080e40070241d1980300c10b10080190080054440354540d0000b08810744010102503010304801000038000761034405030391040d01c010394500500c0d00f410400e4000c201360009181c080b46070804642001404000d11501d844a8800d207024000c80c0b42032440c0024500902c0c1588025207000c110540c1c080c0c8190b0b011b4a810015820907034618211264001d660760310110440c0f001904107440010342c04907000585 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 260423048 1250 260421798 260421829
    0xf0305151005010e031c020127020a0302060c01020d0603030c0b07141e1c06170a0b0408090d0506181b06070305070515010803130803070b011a090910060e 68
    0x300480d61811004407041e1113840c82d103660602400d40d200030b100650700d1604004040a40001c01e1101e00d48031482d075184811040d2031030050b1144005001603403a041c2d820f09503581202c4c030b0f07510790010502c00d5009015007001108410f20f01480442410b4100e1001031145105002c001da00d0703a903002080703800d01e020200e640c1c3c2c86c0100f80300320344542c001d880000c0c5018000100380350618200c01000c00c0283c043c100e5119425035910000e110581c0b4000510301a401210300401105595580b003c1c2182030040c809094001d0118030b02c203081d600d00940f951031030f0f04481240ca4174180b01c0c1203050f00e00d2000741c40310b1141c400d4061203210200d44003040403401000510b900e040982945003034403203030700450b0202e8660168000120f2150003103040719010b460040000c603100d176600e00c0c00303407440c0c85980c03c44415607100344a204006a42600300c18150348880545040506541040c21140d00620350001c1c3d03c01440420060301d201c40081840c121140b55035005081310381101032003085084910803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 260424298 1250 260423048 260423071
    0xa1a03070b0c160b031f0e070e0d121706120604020d03030617010e0c01210e030927070e010804120912080a0f0e060a030b03010905070f030515 63
    0x800c103060719400508a4001004251009012030b2040154400c1240d08140c1c02c0314408018885c0c2c10502d40d44910188a001582445035820a144402440c40040c20a407c0000c10484622280c44894541c10403640c01503112044401400000c2d103140f49040f0880d44001c400300006440c0d01d0080959500441940003074261900d607034081c80400c2140310010740c01d1546030640000c0050460703040b190240413840c0000b9141d00c4d102e060030f0800d581410024100700405030780010f0140011007812001403480400160b000c0c1c0f04140600314010800000d5011400910440392785c0709144030441440c20010465156680d048411345500000f00d04c09030029000e0b90005001400007048041c008242d814a1400320341c2d5410388800b902259142250450008240b42e1810343e000700c540c050840f20307402c0004111408801140301405001c92410030035440d01c00075062a2020350203800041d030070400f540c007966102c034060424540d0780e100c01c0382e15100d103080c030580c0459100c01641c05509134158 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 260425548 1250 260424298 260424313
    0x20c0606041416050f12040503040611010606090504180606090902090606040b3001120302191115220614090904021203130e01050a0501140706020a09030b09060a1a03 73
    0x202129580c20010f0000910117003041652080c980b00390300c10740b1840c402e1000315984d5060280007400d012052078901300c0c0c0e03070600c02c0034410207400900c050140d9005650001e80b500702c025007400c1540540c9800b41110303291542c0401c4009080c0c00c144e480c5030090f10001050b89504060002034416442803c400d21014001c103198110780402030b1400c161400c8107803190800300403040308816030a0740311004100a2000383c000b05074050017040d41440310440c04040c6802c0503110319805c0311030496071501c2a980f81040300c0103071500c0c0c0144c0e949086402c501030600304012880c50000c1c50140160b20209070314140d01011604040211401102c02404561840d2076a6003808128200c0419903112030109000c81040d400c600342c00c002c018403081000021ba54508003d01440c1901d940026040040d03801410307030107200490440300e607035520500060351010080c01c1114038000d203070001400d910320401480794a1100081160003170079403a00030070a150702c0009110300c0046c03180000390141c02c0700c1d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 260426798 1250 260425548 260425591
    0x2210405240d02091807050a091203081902221406041a070c080a060b01030606020c0108040803221202150f2e0306060810020f0d02070c09020c06060414 67
    0x2001390188050107031401c0c9402043d04000136280030300f210144e00241d80810100d4496510a50110041c14640c82919910040791402055920300031300040b005603040000c14003c020ba50b04071000314420350f0360f007140d9101052200340c1c103159911510004088603090a1050700d000300448007240c44614007254001200214030350150003814080e030310701080000c0000d0705201440f259855a101d854001802c545142c00034040f500d09801c0310046520180b40c02d1a50398101f02803039080758020000d19105c0d0b03190f48401c0204801101e02c580303c040020419000c104180c0b0260302420082d409551112801070b0b506000f540040f9001e0180404c880f0110780b51541228083c0888a00d00008050002c40020507900c03402c801ea0003264556554901000782100074070086ca8030b40421001940b03821100500751005000f60042d40700d85550000700e400c10021150240e100070001458155110031007482c07156115003084078160b00960414040e0303245022507003c000d00c02c0e041030490407884030008 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 260428048 1250 260426798 260426801
    0x70e060607030c0602070b0705070203100203010803250c03030203030118050c18150c0d1d060334030e0c0f010206071d09010f0302031e0a030c0302210405240d 70
    0x6039004d0703402c15401c000441c003040d03249220764450f0880c2d46a50750341d440140b06161606800710400355425105000522101d6400710440303054075550360200e10600c0c00980b40c0d0715280d1107004004c1203803803440c20000400d07801201550407110100070a1040c1003038404800c080e80d81c01c540030b003014181005540c00340c0c0c00c00100b14041c850080c0c1900d25828041c0c602c3c44403a802800040031030380c04144d924449a60001072400c442100c0640f08407284000c8010030b42d03e0001812140040f0100c45102c0d5800c66076030798103000001512401c18800b00001005401048906d10700021802030214090540c1041c481091400006038001c08459072a075008480100c6040680800302005030030018041d130365995814082c00c0481d19000341c00e884d6204040c41c0c010782e0004030314503201c1079104030740300040490414070841c1c0505220148450900c0c0403402d010031480301d2000151f1889400c1d080301c4000014106466066a2003281c8403c0742041d400c046ca001140452494020011455580d089 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 260429298 1250 260428048 260428067
    0x306050f090a1b2304030f0807030c051902090903070201091403070909060b030d1404120201050c011a0f01032708091f030f020f03070e0a09150503070e06060703 71
    0x100000600340385100c1c03100600c141c49903d1500065100944220b40400b1040e00d6255151502540381c94a0b2450b82c4040c10070083c075601400c890300106e6440203050080b00c0c0318031001c1c0d0080648181c641105002e01c19100c032200107038015000040001c1e08204000122810240c0503110344001c0e601d0601d05103441130b035100003d509070180c2c1c02c0008546e1080d005480c0198819100410070256240c1450700d44034402c0e0180040185c6082d051121501207421a01034406420044030001402d00058a89115100e0300d01031540c6010100c92000003016460700c0d1540742107903034008211102c0c004409076104030810080d550036414411115045e40d8418250061140780710904000ba0480020034800c2d02401d503080030303181c40706c078070701600e17454031400c2e000f5607048104505041100111542a00004198405000c11910448201d5a82ca1282c00080024130000d00c8600d02101290141c0211403203a10301a05c6100c1c00820202020304034030703100e8280900454142140b41d1002c0ba207400b41c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 260430548 1250 260429298 260429311
    0x40203010e07030602030a050c03161b0b0a050f0906070215100e0705030702060a090b0613150906050906030d0f080a0204030803010f0602101b03090c050303070b090d0306050f09 78
    0x1681c0341101003000c0140040001540902c40c0140ca900c1c11405c1081601c038010f0407140080000c00801070749840081048130742400350324060383d4080801c5102c1514404095010305a40e20000801c4a002620b4020f0343c420310181c81c040005032244405aa41c1c0c100603501030b0003580203003101101c41ca80002915a10502c0b0b4001c03000030650f42c910856001c1d2064850b24006940002000f18568041103001c0d080318400d1020003201c1c0c141c0d2500301004002520180c81030701002c0300603981450940100251300040b0318410052a80d0300504401010381d446440d0082d14008000384803454081011680005103464924000003460320844598000078610186e45900740000310203e00300034090750103086403680ba41405030500b13038041e1070308401d130408a03603140c107040140e0316145164030751071212003280c2008148101c042c40c0c401504013150f08060340611007c00d1010910000c3c0382d0240c010490502551402c4072f2600045041ea045809070907042106840000404d00b804130074030340d0003403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 260431654 1106 260430548 260430551
    0x1201030c06180b0d0207050d03052202060d020c0f030304050114090303040302070e0613050a02070c08060c0414010c02040c0e03160513150807170c0406030807060504020301 76
    0x84030300845500f40e5022540c2c81281a031601a100102e50081c10340c4e0b9038800084005004040072100d20600c101d0407070903803040311403102d0808242c030b801401c038516094068143c070b03000e035000703007813481b040e11481c076603034842807810b2004c1c5000da4856000417914004c8003005039400c0001810081c2144c0042080c0000a5000030744201100c05504000e500c640c1d1301c000140c0c500d82140c104120180c2084100500c10b80380c0c1d4000e010301440754a200c410385480701d00040e03440e88203d86109002c0c404000600c03083d8a5000c104e454000140341411a952040d400324064071030344201c007004120b411001040f203240c20b2001c01200c80c043c0300001c0750bc514060001d03510305c107018121207109640310045500641002e00d100c016051540440f221159600389081c001030107104541d07810700a0201240e100d00c0c19000382d50840780c10011407810049561951402028043d004a0345507 = true := by decide +kernel

theorem cover : BRFrame.Cov 260251798 260431654 := by
  have h0 := BRFrame.cov_init 260251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 260251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 260251798 ≤ n) (h2 : n < 260431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
