-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3724
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:29:59.653429+00:00
-- url     : https://prove2.me/submissions/d03392e6-6e83-40e0-bd8b-a1c5ac131023

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669604316 ≤ n < 669784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669605566 1250 669604316 669604349
    0x405030406020111210411040e1b18011502030f030f060405061c02060d06150809010c080112030c0201090803030a020901090b04050114210a2327100213 67
    0x100007041750f5680c3c2d00301241e07104c444c0c021140070442580140045481101a0780401c0041da0f503401140c40580a4002521a640d006022103ca02480404850245d4001c020750221041c004030014110340031161038104a0259803802ca0851103070700c0d51000e03106004010b200360b801032800074520540081c0d40c104107a440c0c1008000038440c51501c00c07600c844d10344105000605000340905138101240720301050081d200c4504510709040d00c00c00383c00160350403007080010300c000d01402c506902903080c880560b505000c40c401003078400000c05418018046011021a48030310684070080043c0d405403a00d908001c181e500183d807100c0303240360018040c0c800c081006040041280c0c1240d0051715504a00c040d070328020300e41c035000f00380702a0707804d00f00040040401c49100960782c801d91555100084040c1e2005600c40c001400070b140703486102c441d4041200080d07030b0f1401405d8003008030a0107a9042c15407610a841c00001c0c05640313460750b00201e20b03107400980880c0c10b20141c511681c005003010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669606816 1250 669605566 669605591
    0x9090705042112050a030e07060503041e0b04020d02010c0218060a05031c0809030c0604030207031a070e06031503010e061b0f030c0a0c05150108010c0203091305061804050304060201 80
    0x5440d009011441c03643c40c2500081e00900083c108a0750342d060128902c050803210905150340340d800107000c5000041000100010020088a00300840d00c03a986011b416449081e56803000400090140d0001c045000c01c0d0780c0a21010010942e000704004c101405d08094000c0520041ea0400d02489580c2401f050514000c1103031346071a10600400c0d0020306004804955102002e82212110700082282028960301444041e118501a4006049031850b40c54120500c00072070203200d07907401c0803509028000f40e200162414001041f1003040c0c0366298a10b140c2442d030201d0030010303450f40c80c0050701d15101101142c100e2141d101c0c103514202c00d1415030b480c91128420461148200e080400028a01d00f0701031000c1c01d030388040d9141c5080b190b205540c07103900d4542240580c0d0002e1a100c1d0040000b201d09014651284000e84091030034a04a03038007066500320136602d01c0e030840f52980c0009400d52911030041443d50003ca552025a0030305007000d94881d481402858010750074140d101d07464 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669608066 1250 669606816 669606869
    0x20301050a09021c080405060403112e0309020a12060b03060901090b07050309100608030304020a06030c0c0b060612070f020f0c0d0b04031106010f0f14090f04080909070504 76
    0x1141c0182c44600350051320340740c841030141102e9040b540e446051101041a803182409480554031408408060065038070411003007007019a10b010798503450710a02200c03040c2c2d4006029541b2101e08012840d03000601c0000c1c2103a00a4000b45001a403900c6607000b4480241c200c142003440c1641520300325140c1c100c107207003030300c0c00408040c040c1c084a001140d4401e04c603200459002444c10190381000d004848080180c4003540d01c00c0089a10220901040d03103003560300c41000300254101040300d000320000242004245070b201030710b404010800104151521011290b511520704841c13a2140b07458800070f8828584804000014410b454094669400000b40b910741018002c02100c000c400582e2450301c400c200510480400000a601d41c040c084100905800380c090100250092804c001c00407002c203180768031072000140384030840285600c0720140c1e942c104250b03190483c80c507641c0b4101000603100721002e49402003010010024460f5118024000b1f98026038012000f09501e12100c0f0758 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669609316 1250 669608066 669608081
    0xf02120c1201050904030c0f03112a060d0b1002070e0c0309150603031207110d0503131101020a05060a0603061118040f0e0601080d09050d030207050114070816020301050a 75
    0x94001c0d400c0c0148440e180280c605580288a890840c40804070380d0750340111110301410072400b00b03621000076107071020240b101b1032403000d1103940324084c50301c0807210711070311403070030982d1401440001001170303226865410645682c2d5000d01400044d0366003601c001d6445045104841e1501c064002164058140f002101c0c0074003000d50003403420f2401005030282c503070f5000d030020f03500d84420042c1080340c0d042a100c50b44100400d88845c9000b284e400c136018281b070703440580081008030810806c401d030480101292590b40d00190703000500d03401000180e281451007500502a48141003c000c2680c100390046405d0302d101e03181c1400000700c2d211410b55140512210790030b03000142d02e001c4140b41090f602848201000c050081052a980400c583c02c00d00c0a03048040070781c0001401c1814070790441c8183d0014141a01d025034000056100251203d01e90b0203640c2c10801c90050f5500d0381300071136003035400064005034a140e49214124007a010110001c000303c4c025400c040025980e45c1e881e00c01c101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669610566 1250 669609316 669609337
    0x6130e10080c060a030b0d05010b120d140912190501140405150a150824060901061101060902040b130806070e061b120406090b03190e0a060f02120c 65
    0xe0002d104007002004d4111070025010150344400202c1c0507036074040424200d600800001518040c00018440e000c1c140051035056984a09003400c08540c0c4001c4409018460100c2a600c40103514005000c80c0e01d00034860255208a0300404000c81da2641d042150b14490302c000c11405081c46e50340d00082c5421640500140c020403103500c49906149401c0b5402401fa6000140c0c49003c080b0450801c20107400541140d400514900402030200c00f6600072108041d41207903c514141c400665140b0050203144100300c4000a000c03405042504958042c00b0708038019502c49847d5000400f5680110040c3d180113a8035203400540c5040118045000348516a10001500007050600034a030780300e403c2d0b9840440202d03403101340c140418084800c100718564074a507921483c00034001c1c82c04d1080c0e081084843c1c400c00a002e004080a800702c200013001c4140840c2d09901070007401d081203441380700500500e0034032080030041c520990041c40560500400f00c4104c0d11110031190f1781c0d00030980c034032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669611816 1250 669610566 669610573
    0x609050904064203020603070507030c120c150507080123040f02120a0c02031b01140106021612080406030e161212080f040605090a0206130e1008 64
    0x901140c200055001e5000e4002e6501040e031988248103c2d00300303030030511010718803560260b503000030031854180110100703846044a640785045030001800c1c0d00c4041e2401051108c00549402094000c25200102542010207080d0b02248060b000e49507000d0000c0456105c044a90140c401e481107200d0301c0e0080c40c00d0740d41c456413a0700780f50010006190f940a02c081019100c9849106542c89000d00b4104000d1460096260800100100b9403071001805468810303040025800403103a0001c103442c026803000c22104512001c074065140108100620f1030811107003140040b0f903554001400d07143e001d04400c1708030f900310758521510a205250800c020200d010800c002c1020621a4000c00914000f003070503100340c40003544406800c41e01ca6884003120307a130200d107401c09000c48a204411148664141085940742084001c81d40c00c5006000a003e290358002103500362904004031404694094000c036501d0312301c192214141d20403031081d52941c0380c13030380e001444010b031055042c800c940301003004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669613066 1250 669611816 669611819
    0xe1801050906010512210415050a020a11060c030d0b03102c0304080d030f05060406060c2d05060402090c07050706050a030207060207080712031505040e010f020714160609 75
    0x2009043c891986044440b0321480c0d080e81d8074009030031640d0888086e40c000c40c0345e440345051844504030143c5803004051041c113110b441101c40c3c0125184003141d0b80540e4044440b8a034500040140c002c0c2400f0300b03905d202c007080101b030301c142d5507000e00142c19044013120701d071100b40090401038806c04cc4c1c012800d43e04c0808845507111044918580d2011140c0c1038074200f64030303001a245001a00e48407400060b0710382040000d28001c0d40b150581040040d18280b04460600e207001e03105503034030b070402001d02e400c4140d942403180145410000f6101e40c1d82490070301070981d0500c01c5d0783d5602a03c0c268032800c001c0c03000ca03a015004030103d0f0f407042d5101028204461621700c0a03229a0070050802041c95020082c1d030780000d400384003e00300103120744036142e110001400c1c0b4940340300c030a0358004241460900c1940b46c0d00c43c040440021244100d40100300c00740c0700f01c940c4d4003605010300070b10a081e001080406c00c00c9080700e41d0b2609403000340121110b044507214003c21b0408140314000104403041c80 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669614316 1250 669613066 669613069
    0x70909050c090607050321010914100b0c01090203010501330c12020703020306010312020129040b0a050a030b04150b06040905041a0711070b07051203070c06060e18010509060105 78
    0x84c200e4580a5002d50f0700b030000e400301c0d810809114039a000170071990303940103210790350451091102920819059011501d045412032a080865006611410703c0c04981c0080802d425005560619400740090000d565500b500c0301c1e01042e5844094104005565680c0ca00e40c03105181440c03000c100e03600d010740b020341c3d038444800c00b1842ca865030045006c2c0400200250728108803541c000d520030340c600319079000209002400c6500701051354201e4103488245601c000d5811103065000d003412a8002107240c1044001100024140d210f10b4000d444140c0c00800e1100d0355290381d01c01c1d4010214007584102805004040f03c3d9001112580550300307000920080c0d00907400a03501c14441e0403411881ca061207180301c0140012185500041d00658038480e10400070300c85100241441014242000035a81e501d50702c030884c4026090b0690004000500740c41c0c070650552040680003001084a242c40b911000040d1504442c0303045950501180c103001c1c20700500c0b03250312450903030014024513400e140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669615566 1250 669614316 669614329
    0x31306050306060d0e0d0807081302040f0209090a230f0109051504091209050a08060f090304030213020a0305070e06030a050604110a031a012c15040806070909050c09 73
    0x2e000303d402240610030340503510510311079844143c11307040080100074000e01c00104541d43c0102071004200d80f04e011702880381c404150000340c80ea070448010401304500c0d40d154000340038041e03141d9803001104041c0724078442194807401c984040c46a50706194121213440301d0700b02100707950007041303502d079800100010403203a8061604818140e84400c041e000400016041c0c42412074160341000300c02801c1c03a010764120f440500140825122180e22503e401c54042d19078500070700c009051091a000a990310005000301c6028640c0140754070054035102240784003d4010400b000040303850000401c5446004810400000340e00802c4280342d0340d00d00450708040c150150040360001c0d105c2c1003000300a1000c20203081d2030281c0b41d400052003620300d10b0102c250030280031214181b042091084c104c0005140000d0300302c4404400d181d41220081002c05c803510071444645031a010017180c08220340d43c0100300c0a00030401561006c00d020f40307071481c000c200da00a4404d140c0300ea90410403e00d042c1000d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669616816 1250 669615566 669615571
    0xe100516030e0121141015051b150907080109081c111803010605120d180f061223071d030f010e0609030a0e09060303070507060e030d020313060503 65
    0x40c0741941901c4c11201c203555016054030704003800380c3e845100460680c2458100d03958040349038130040c505107103440c90000e00703c822428400d080040005030441504100080d41451004440840e184102d0f81003460095000c01e54480b8407a0081e00c1c030008581405003d9244096044040c0e00d10f8004e05050304c620300031142840080b00b80d110000f0600c150100005031072090307039603001459070a81c14020542105d900c1d40290303109102c148900884507000290030520380c0181d003001009030344c0e140740c801c01d0b068032907000342915000600c01281640d44200d05808000034100c003407000140c05842c40b00c1c103545030000303401c0200c8040001800b0030f100c2d503100e103014051210b0600400e103c86000c40d003002010060103a940c0c1d180c4038500215101000342540c44450f1201035400d0081d00034004020003100d60403a4031070070364407001c5a49690240203c3d03140e107600104841c9010f0341c880026048880d90096240b2901912018210040c008012507040400c682d01004541381403080540b400d0704003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669618066 1250 669616816 669616819
    0x51c0b01023403031d010810090c09120f0c0608040f060506010c0501110a021614010807031118030706170c0304080f0403150b1509150c07060e100516030e 68
    0x304041c4080200c103100c400345009179110080112031079903071094145440c100030304000c2424100a0080115072604058546031000400c4c1402c034000c0c1140d800c07407103400601c44c40080c4603030182088558078410711501e2041e607400d0900d41d07440c0d1081d070304810100d0f005403405d015440250000f9816500c110740c00101410180000806500d5060844280c2e41510b0a891b4002413901c50507a0104610945042d5843c0751144043c00c01070552004002c1c40400c606011040b00400d0441d8000c1e0481440814021411901d0300070a210ba46046031042c65a58044d0203020404200144152241c2869046a1140d540640c03218a2070b02d46036400248241d0380c04000b8003401615586400003080110301071804a0804d040160301d66003200c80d10000f66104102e1340c8214880521801c096612121003142c2e04017000c4490806420700303201d2150000168000c5c0d9001003400c1e45c0110b064405620141c82084c41c0a4410505840702d128104403617074241c0d5107074080d9001a02c941cac10071200050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669619316 1250 669618066 669618133
    0x50111100905190804080c04150608040809060c0a1106090a050d1109010e10091b080406060b0c0a140d14070503130902040303030e011a06070812010303051c0b0102 72
    0x20092000700c41e064880c2c0f403c644549002a0410510301c0801c450400d440d800c950820171a80c20784c0c0b25003003440c00741c4281c2c410f04c0301200c009014030a804098030f007a01806807041e590344104428040c0c6689410008441c92484410548082c0c24484180c0d01803090142602c180306051000708115121040303011603440c804020b800e240c41d122a02072900800241c0b401450038203100c0900c1c05070b1239040e080300300b4182c80d001e0303400c454285180d403046080c4800d0a042d11a030b180c41c00c1c644081c000c9900030a040c50301c0020307244408440010545040360041003e24020750f01107046030307155807860100000041117550300c01e0441304004000c2101c0340c810b83c116441d000781c00b902000303894066400500c2c1d195010408006040d014092400841034210080000c3e650614090303140238003450001b4080c00010500320200420314049582449444965280d603607542d281c014507961140002c1502200704005a450000060042e0002c3ea0070580241a49055045a006003840d40001040c051007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669620566 1250 669619316 669619333
    0x1101020703051b0d200a12080402010915050304110f15090a0605090d031b05012d0203190510090e0a030e030f10020a1b03120c020c1e010e0315060307050111100905 72
    0x10704602d85000d081d29640c64250308c07881d080c000540090f5159010f482c2409080903407890b074591240c00c99a03caa4401101c40340030300b07041b021078861480480700c1038000900c4009581006c1c500b501404000100b2260380190588604040350356016406565411100c28038103900003900038245d5108403100c48610003450041c0e13444090035100e5a444907402d0840070f41780c016004818803c3d00e103501600783c7c02035103513060682031b21002480403640d0a40f815a04c101240189188100030780080c21503a0b07040c84000045404140c96140c0340e14100e001c180c0b038001d132482d00d013400b0a03a9054940d0742e2014000020110901a0296004200c443c0811044031410708201e40700c1e900c90554a8025070b10494501a144103400c210707403c0c03050703007130540d032001c42020900e41c0d5000c03280d2640700909904221003c0c0980050304c0042e1010303400c1d175150045401c401c5402901c9440244158021011140244d6075040152108040085807034815080694807003e2200180c200c2e0103a28403485c1100da004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669621816 1250 669620566 669620573
    0x50c0d0203030f030f010e0c0702030604111306090b0f1507080726070b060f030c010507060e01060b1c090c0b09030703020604140307230d031101020703051b0d200a 72
    0x250b0045407026403c0051714014400c0381c40c40b248003940006425001e519040198001030754501000300f00800c0c071a04070040440780c2e2a112915060071140c1201401010f48800303e08014240b42641203015401c601d09180c000d00d0290f04401d100200c80c2002c0b842e22400f5112041258030481080d90000001840c4000410b2341070707003c40518134147c401c180c9a002074a0420200f140c00303400b403072180d05100104c03a619540402c0da80220602400c10982d91041858034402408100f10b00d22425460509c0001e80a58031000501c4000b851b240b0080c1100d40c24400d03072045415940d80640b14030040d03031040c0403c182d00b00090861180007021a01c04a40d29400111030364400d403c59810601c0010707008500b81820031a0002030300c406480b003825400302c102c802e21425070b20100e1500c10341d0301400001c1410301403805540a9000d00000303560781d902506024216a11031100110500054091079501000c0401d40e0300404a5599680003550044004070f1014161110780880f01d00070318180d400007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669623066 1250 669621816 669621847
    0xc0b07020a0210030c08061f03020a0c0c0e040201140f0910030212150103180f030807050d0e03070201092301051b15090114010b0a0810050d030c0519050c0d020303 72
    0x2820f40c0c6540101d100c0000000003000e010002d003078035000b60105541d02c0c00310340d081c0110306d24807500741c070b401600d90308001c60442c1c03011120003001e811610f51b018046480411695154030a5001313898005029030740070301c200300318458a54140d00242c4180324444462610b04601003007c0c40d40d29000d410f2080b0341c41c0e09050298180e03001c0f80303146500d5017050b0295801d4010200c0300f1503074072942481c001e03181d140c22101380340720b0303800030304012080000a00d0240a40284c071160402018100306503a00d501a0550b2030b0301405050380414a03280c0c0000e8890044621982ca010000d401e800b03030300c42c02800550f01b40d0460904c9134681c00e030020856480340810000c82c4034060030000501c207203040c01c0450500316044134171407043c2a40000b0040c04500840421584400a90301c0e1480071965460391f1940c0074015a007110740d00584010612040c90b500001c0341c03640c140680c007a130304541909010982c01c000342d03041c0146240c006008244040c680040d10158160020b015030785415070440740c01c4403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669624316 1250 669623066 669623089
    0xe0f1302010521060406080307050705150f04080303250e09060102210301090c05040305072309010617010905270f0105040c03050607031e02030603010e0f0a030305060906010c0b07020a02 82
    0x4083c103424040000c0361405018000c0103000d584043c61800e04a42c44032a112280c901a1030f000d0102c0c18a80120003e0b1501140e00a5910229250b19207889001c1c5036102d910640380f11001d01c0c00c1405091004010342204500316006031907a20018010f003013800343c0c0300c6000f0590340c1507010350a903003101c45102082d00041c00035040040e0350b40b58140030300f0404442565000d0010060144010320002d0320004144007510140d007a807240d2460300d150010424080c1d5242c2c50380109080c000001ca0641000028402e04100d0382d400c451681c80300d6041049070411107071240c43c200035a031850701d01d05803c01d2500407031a20500f41c1e480742900607403050942c0e42c140c1c1c0844400300740304800c0050100601c405c50300581d02d45414070610a09800c0131100c20780c03210300c4000311503002021075487d03a0258800000c1c0f1604405465200b6400c008454942114040540101b03050100252161404000b5580b00d5481615030b0700080700c1c40c0e144e001c600c1c50001d10300000d40c0711b901c1d2030401580d10ba001107903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669625566 1250 669624316 669624367
    0xa300501150810050906010506030406110d140a2c0304031709011710050f030a02100815090415020c0a080d0501150203070c060810051c05070e0f13020105 68
    0x201c08524010400f442c109052074006803080c640b9060043c2104c0114000c0e0458104841590701ca0310745090410040000b50f24098111000141c0795a5156064210100b8116901415a15a550207240e001030f15a4003014588035004200030b0411001e039845a80c002c5810f0008070307400e007030700ca589083d00a120100d020448010101d24400690707485005a1144035400031a01d1352420705582078452595140501d5100e04119a50301c20180c81c200441d403020b50300100303007000c0c204000030b014020341016a000140b0355600300036204c2c2070810a8510b802260710501440d100c04204004100a42100048004a0240307420754004510f6800161101e89800c00000915516160000012110000b05c14096400500c0fa82c4041620900b480007120b50034200b900380c40d56500d440b054941030a40005500c0808012801108519126001c139414440d06c2140d41140e120041600c1a84003114500d0b00b98035594002407400301051184102144181030081c2001d160790103c150701302003010b440c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669626816 1250 669625566 669625601
    0x703050c0c0a11031213030b04030314070804030909200306040b2107050406082d010905030405100903020a1403010209040e0a170406050f0f0f070803010807050a300501 74
    0x460f50324080c01412075501c03048540b186041c100d101405000c0341640f0000c2d00071900341c0001010301d8001e800c04884210440000701c06032405241c0504807503001c0c1c6e0140d0010b2003408020403884010310900036003103c012030210340041c40029041913a40003e103c540c000d41c0741c515844850b124401480e0705003040794404054485e0078420180b074204d041d404184910300305907041003004004246c00690782e0001e2081d01c0d00c94020341444d507103046002101d20003503203030103103000c203001001c03002d0000c0c0c4008542101c04400d44030350450f4414a0f501021f544070042001c2004040d540b840300c00c0b04070703001034009401d00500a00041c03c0300c0c0381c040259555040611981d08000d108400c0000200b0f4010b80b083c102400d0800c020090b02070303001d80c1c0041041c00150306450325907043c141d80101080c1c0c080c09035a462140f40203501038001b88142d400c588904d084c040340914100c83c018040c0c64120240c4c1c0341800c644082203818843e0200141d800c503040803000d01c0801e000307000e00008581c4480f400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669628066 1250 669626816 669626843
    0x70c031223030c090d0c03200103060906141002010b150705060a0903050a03090c0e0a1b05070f08091809030a0210091e1a040501051902120703050c0c0a 67
    0x29a500500d00740340d198100020000c0041a5840c44192100030710269204240010540b03082c50720014181c0018103c121000402c1800e2041c001e501981c624003079805110392a9523052100c00e42d42d090051591001c02e50391141c0302410b084044400c00308440c80040768400842c0b0224034000b070015060f00740406d00140c0042130010400009030018184070007000321090944004040340202c1c1c510800300354451802800b44880c0301000000761001d00c0304505941081c0220070000e221000c000e14440d8070b21090345201501840c03c0d0303041c0030b4004036058602c81142d80c841e11a40d00240c0250381c403602014200048031929620688600c01450003550b40341241c5030040d00e8002d0181d64407c40c03034140080000080d80d92185d100c54040400b80019042c601c80c40c106039104064804007140d81c52200400c0240001504014000c041d01c41e24842400322030f42041c1c00340d115483d04041d80c6c901c1c880204040510a6111951010160804a0a18906c202c0b0030341010159075055403e03131101c184 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669629316 1250 669628066 669628097
    0x1f29241603140a08041103160b030403020d0f0c0807171911190b1e0a050f010609080d080612010c0201050405010506040b030a030c0201170124081b070c0312 69
    0x20b4090082d06101e04a0403d411201d0051031400003c0004000a28118203100c0503241004980c400b10300074a1030402d884e4850200b601680c10880e400d0340188194a0200015070082012482c0001d0302d0381c0b05099170480340c9621560b980440800c0360b152050b140000f0b20b1004100c003030308070f201042c098035050000880c070090103103001c28800c0c003064101c1a5150650119081303030840300c5030b02001c024119079451110f421003d10750580b8900e440964020002c003c9169403000d8869a10041c0b04241640c0700c440403692280c05025201d041c0c0e002d8000d80c6a00c9000e009010b40c4481c0c000d007140348903040d0700c04a500391000c01b018040940e44460901c42007100a010340d60744a031003074408000c0d2280034800a50784442c1100c014041c46a12081402903910517203e104000d6138014260280e569a0911400308107500c0010700c0c07400494440502895104070701c0c0301d015178101c0101c01b9503800e015a4005c1c040e44540f004036030b001c03849003002001400901e80a582a1820340300e50b100310000b181c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669630566 1250 669629316 669629327
    0x7020612130210022514010e0303040b04170f030a0c1103070b0409090b0903070f02090a09060213140904050c0f0a090c030c020f0f1f0207051f29241603 67
    0x10101c2817515a052203000301084150410b00342c246484414003d549000c68210b100b1038020800702003002601049c1c61010440790500c0004210480d02503401c1000b00644900824140354002a2200c211001080b00428601c0007101c00506a8410581c0c035040752600d070f80f05600480034541c44400c0e400600c54092045603101c0c001c40095032401c01107603260200152140780003481000b02e500440d540140c6c942c09118100d0740020119038031007000448a1141c1a00d1160b4030b400303814403903d07680c507040c40c0002c039000e10340c09001001d0841d415000c01c25030780500008a40c01c20b50310381c00011400142d00a050390600c05440000782c51715041c00090418000d02588102e035400354112291060b4002041c541e558901e1840316290302840c507500d0702074854450017031f099200350500122550300300c540d90000c3d03011480c800c12092503014204ea000b00d0b00720a605404d150f0400f4040200c2c200040e070784404c505804202108950141d260203170b03035048038511003080d070541080d20b420142c104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669631816 1250 669630566 669630613
    0xf05090106080c090f07300b030c130c0302070b040605061005040f06081b1c0c09081020030f010302011704081e1306051e0702061213021002 62
    0x1520903580e010011513030031900501045000d070601c40009042c40e05c00d11840d1642080000112032044580513450400b18540d2103180c0346600c0d00345000d105107000035a584404002602400d640706e052243c0c08010035140c20f808060603020000d100000d40d0740707104d0380c2c070552154000003901c0c101503040c454004114200c81c0d0902c0b204101c03d100b0900f0796001c071001c854652501c050903503607074580e130660241031000104a580740422038005400c0101c008200c0b5034400c0c4020004400d2042e4121803c0715140319414084d04440d4a280b020002c03a00903080c0c7e03071911807440e82c0c464107040c42c044980c2e004a44038003041c0c005400600842da401820762600c0c488074041e420060a25468402982c40b80400380030011101d00d200406d000c078800c007901d0b1180841041054440d658010141c42a4400b508961002140d26601a0380881070340c2541c00301c0c0e4000c2c0100d82080100e100c41c0d1011000501101803224080301c000e40180c0d65401107031101040365000c0c08222503002c45249034042c0a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669633066 1250 669631816 669631829
    0xd0e031c09090506030d08150d02060a0305160201180204090f0b10090e030a050a1b02060f040504050c070c03021005040b04030606141f05070602040e0708041b0303050414030f010f05090106 83
    0xa02c428440840c1c0c084c85454020085c00340300488c0c00355000024080d000c00030b01c029040100499695401a007691103a8450b000000940103420b2030000128201d80c0e40000340a042ca01d03007990a0054105980310180640c4912001982c01d0b5260301ca000b9034600c1250b90144c0301c01e034145c0030b01c8528102d00070000c0b000108030007141801e800a81c09070250191150b403404201c03000c0788010030200713001c0d546282c4940181036242e4880c02ca1540500640c8540180f600179800e0001043c1d4401240302111401c5030841800359455003117908110141500c64651802c1100070301c0041a0403a030080100011807103802c001130001d24052101c01c1031404101c0b0b461040c0c2c0c1e401d42c1d202d06207120704011282e000c0c85140032340d5a040c480c94020024042ca800c00e01104841c4010001c180d504200510700840c02107075804912458052208072b0786856000041c0040c206000c2008850703045040303004050401415120135443c5103031020300b102c1c444060340000d03580350000d20452103028030a01e8060700c1c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669634316 1250 669633066 669633073
    0xc1c0615170f06130902100e0307060908100b0a0b0a020d080a02031e090f030309070f05090702120706230403030e12090d0201031803020601050114030106020d0e031c0909050603 78
    0x8180c050490b040307200820042c0180e10b0110030400741000b591240e6001780d0f0003040d00180810074040240500c0a030340c1054040c1c8944c543c0840c40701e008410394012100b0341801085099180054640a0a0054807007074100080100214507003010754054940c3c1c0b00e695000f44a180c00c100c0c0d008101d0302020784620303003980c070402c280700d004442c20016840c28034007088d01c14603075105e1501c99481d142c20072624401c580004000d101d9011804100c0200b2511050540380c0d1703013900c5000304054a40140e8007400941c3c8502000d40b400381d0300300c018284060241000041c06401c02c031680402c40b000c008050199099a01088100358042c0b01d5462a417500000a00000003c050194580c0c0715014400c5d11904812a49a04582c0b1079002840a094a0b4460f13104003001c501d8086d5440301c0a015180c041010107560500d12007071102542d040324019030040024126101007982c03580301c08080d403600360084c00a00f0110003072030542d0032090a116944d18503042c0c034210591b011500c4c0608030350300c20780 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669635566 1250 669634316 669634321
    0x3041a040f030f0e19181103010e060a0b030106020c15091e040207052b050702180709150e120c0904020909161d160203030c1c061517 59
    0x8010006055006905003407002440d0b81c0c1c41c4044d564140074090307442d404402d0602030f584110380e80000200300e540210008403414260301400084d00c103442a540c4200700240010001a000c5485280d000000508840c09482d00c1e030140011740c1d0700c2604030101503071003070070f0341c40b050b040c0b41c1c8000c1688068058a1030402504000081c0c02d01031450014290305940848080b1980e520303030441d842594054121840101c0a48500c86074040c450342260011a1824a08100500603012103101641c0140701c510b40060b402c4804010301c002034240800c1282d9004040756030080710f0300d0007440342c810340c6030307601102039800810600c65040e5a01041d1034200c10211840c948038038001c190800d9044139400328640e1003441d0a494500700c0180060300303d00f9a02d0001d107a00d40c10504d07000c01208840c0700406556150b01112265015032520300059008000082000040c8070140003503880a0004803801390083c0d0310103041d40c5403074010b008801e500703030640c181403170700540390321062821590f4422203403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669636816 1250 669635566 669635573
    0x3030c1209051009381e0a030c1716050c030c010c090f0506070c050f01051e0706050604020304020f01081e091501150903060f020c01090f050c01021f180b010b03041a04 74
    0x4c0c41842e00c001005c03030000c95120703400d42d28504a02c0c80581c09503003280c0c07509400c4000401808103174034000d000c075100b14154094107001508030381c800e030781490401d44040010341007110558051a421844c1c0e000038414070480300401c1c0504501e210382c1d13a0b42c0114040c20300200400340300c130702d41c409841003004109a80c00039900301e4082d000c4520413503420303e50001c4100180c4203881290f89194200d44510107095402010101034890903010701170401187c0e03030701d005000882c801540c01039803140f00341c010071040d58410913005910107140401c0c214403400d020002c16942c5407daa8508a44e040040101d0000e0b004854150042c4055500c40c1c02041c0c961101500c4100507000140000b034071001d8208409010750111510740c030900c1c0c0200103400c0c841c1040040410381e074404589a0081c00880d101a620001d03100c11050950075000e0043e6900d0f1103244028060340c403051305038400e2881e6100c0440c0100902034000c1c00e103a00301d140c0d42c2c40d0901e0002125812036000008803d111001d00010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669638066 1250 669636816 669636899
    0x803130c05040e0c040b01050424020c0f0303030a050c0408010c0908010c090e010b0d110f0703030c02010b030d0c05011d0a03030b19030201050c0124050f0a03030c1209051009 77
    0x2079a40070b0345c000440b08401001260103104075005403901c400c204218200c81c40d40d1295092102d4419800c1c0d03087c000c0d00c0e50410101c80c1c10320074140e6040c0d10901c0462032202d800e87c0655041a0000500c07460141d0f01e41541c0d003950421104480811000b410030821950207000d030914180603440c084140b03900f01515051100c4060084400c00100400c00181030101035102c08640d081c0c0011090f1a911808a030341020b0780455811400607003810310070480c460050082c0c0e424550014042c0c184a902c0d094129102a4101000c1d40c00b99200d048070b181c100290810b02d07c0041c00c00016001c0c800c140d050140c03c2d02c00b5000017078000e080010f080c0b8401001d18a00c07005690707092030490b40d02d04010b0500fa0252071200002040303003602c0e4100c1c0000707100701c03000001290400c3d526107500303038400020450807007958030014000ca01070481000000c0c0458000201035501740c20310140d0262a500860807002e6140200b41c04104408001e1143c0c060a024100d0b04131109000240c0b1101d0410a09c02e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669639316 1250 669638066 669638083
    0xb01170307081b0615030d0309030806010c02030a0b041b080d0206070503180d0e01110f0330070504030c0e0402150c2401091805030f070606030803130c05040e 70
    0x442c0c1010440e00030a901620210380716034500421585079050280c03010000c804102a030512904c1245024500917000740580710b5a10341649503009151b0710034005440001140000300c1e07040c014500180001500700308150f0280707008800e08844540c4140700032050b4029500110115840401d041100d507500042d05507009285161503600ca48031401d52004490302c810a10b80c0741d018100107003080300d030302a51184090b14242c0e91041d0742401c0e04142919054400c00340c00494208101c0a891035003c0d28650f6800b199945401040394140c65034407109a03000d460620000f0800141042400040e0184801038491012100340c2424981e001a038501e601e401d90700101080402c0c040c014036014000500c80c001c0707112000c0e204164084e03249141c00c01c240110a442c074901b100420100c03003100510760401d94444001d40c0740803d00e10b40781c03406401c05030f4107c600c1c0c3c0d01c85a0100c0080c17220009540645039502c40703c002c1009500c0c01c008203403140c2d001640501d2078003a41ca20b41c1440080c0e00203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 669640566 1250 669639316 669639323
    0x120b06040911030711281401020a020109020114120c0a1403190605041a01031d01020c0102070507060c08030408181c02041a18040203101d160308071119080304030b01170307 76
    0x48403051a440c1900340e8603044440b071f141c40c2d48041b95400340550190000382a444c401d0381c4040f42405021449506402062608480c401307488c0300243c1c00c03003241e00040c03210b5080c504040d060036166030800c1c0080c3d4012264061000c407200c2c414007603801c0c1405143e000c0e00c41110305000e400040340d40514000b140807640740c10141c68100c880d090030414401032803803507446070095640d02c0c1c3c180e0182e0301070350010800710f03524451204000380080c4200c20740a000e030352103640b440c5952920386814280b9000504640d0100d50110208c0d41140d07181c41412036020505012918142018010841250b4000100d1070608076110500545603440c0891818060301c813604e00403454403640042403a101400405001e218640b41c100c034442c420841903d400e4086540403100100d10707480840c0b000f10710074400241008824090080010000d1242041b90700000e4200382c03100145400032004102268041c030303e03030741000900340f0070700c03142d0b90761079004d892480c0111101c01c6030181e00c1a5284122580079 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 669641816 1250 669640566 669640633
    0x302040b0307121e02120f070516030512010f17010506060313030c0611031f1809021c14120301050619090b0c06070305070f120b06040911030711 64
    0x2100e803002a0381300061200c06149a007072420098480340c002980300b008040000300d00c80c3c0001c0d6042c65002115403040401da0b807880d0410700a841200005048031300100e044c032205010300b203030200401240d1402070a16103d1f0380344803403810070000d140d10074000d122122030f410b0008000a98983c1c00c2141d0300161498841d036490030160800320340f00410a48020146c40c107000030201c0d41d00e07110006d035000c4c5070000e490000109042c03000c098285030900c29510070003002d64810a01c80e003d9806000c5050001c1c110020240100340500640a2180350850720b03190f102020340d544000030400072a90b0f80c0014940e034030b0740d41040000b0702d490040c03001c1003034459909030041d41d02611820800000f00321600a054070303000c0410950f600d034042115007100080c98240003901551068202164040da541c4036050031943d200740d05006000005c256941010040000181541d4140f0a888048184140b200e4580c181100c00800707030184021208899400525031b98840d081c0e04040800101c44a24513 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 669643066 1250 669641816 669641837
    0x120d09050f040905030d2301030b0a020d060b12090d03060b0d05040c050a0801020c010c0309022107051206061503093007150c03020415080a020d15080d0302040b0307 73
    0x2400f408941d08014a0390001040c80221075030580c0051003002105002580003c1551034003001c00071007444041d26103881000804c0031112140e0040811034480d06021421903101c442007003041e8012840b864040744000100003e14034144000454130f0381c1d900d41400366918000e403080c00c9000b0301c040380c58915078807404a020000190403840040c4005000c01c0303485071b0744d0301d1024000d4022510040f029428a101d0711880c0b0301c00e03c03404040550041514851031106480560180e10340501d11082e403169000200b0313036980e15400b0707440180c00000144814940b00b01844003042034420311b000c00000074014011130b5140482c20601d481600e403c611000f034039060b503c4d903410341003900b04072501c00d0004101062220800c42801e284100003800c0c8294000c1040403012031046115048100c90309040500d01a4490351050360004410040542000b91281400c001c40741c052081621550700b002c0204910402031051110460503414214141032510301401c0882c40001c042604008030940c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 669644316 1250 669643066 669643069
    0x91b04330f120c1410051e040b071b0302090403110a020d0b01091506050d020702042304050607050a1e021e0601170106050604032d0302010209120d09050f 68
    0x144400244684180c8801d02aa0b580c0c030262038514064050314400041c0b000071401d881c03225001c40d104d8801800c84d84034002c00b45000c88442d0402c4000c2c0c2c0d400b404d01e828000c503801602c40940f001c2c1c14803003d15a80d071189807410041907144001c40c407910a001d2071040025981e201c84941e841501810101c040c07400742e5480a00b4484c49c07000003584040038280080030320100c0c0780e4150584960f0340c0104600f004c030382040942001d00d44a2000060030401259000641907000b4181651000d44007180b10441c0100d102e1540d11b0b03010260f10041d0070301040006010007002855001103450601510700049090004c0c00d0524031151180d111900108142800b80b081041950010500326081c0301003807194076150b100d1000784185c807210400305078194140c00d418403441e802c41310001d210310315184c91507480411030341105109210510b40800011080c0000c48114440d45101c1e074001a60740030b2980401c816517400094811441e444420071090580d0441c4020f015a801150000205480d550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 669645566 1250 669644316 669644411
    0x9080705010c050613152414030604060c090801090501020d0506060a0801093612050901020718110a0e0a060806030618011b03060f081f0221091b04 65
    0x103034144035035281614a681c001001203198100c0e0a01d01d9040301f98170754844070002861441807225038913800c00300c08540003a5559102d168461450301b0207041207950780080d54216040c8800548642e50005020507504501d80724051744407d0480702581403080d20540280100c0b070502a04110341e68403004414030031001908040441000c56110381c3c4207011000000c00242221411101e518003c2d4880058a01810a0368951304040c0e000300030072484c011840343c0c440103400d420780510396980300d8610300700301440c01003a441c421500c40000d0900900144801030980703034481c808004005041c40300e16600458a160005045841c5400c06960104c44500614a884541021600802404403000d40540007001100d90070354244a03195940e48416841d541c805800e1003c0180e0f80c0e94170300320440700d68050128580c1007003c4170501581350588510800c0701390b1700154607603c0f1513400303511410154012200448181c0f07003400047e005a50002c0301ca058444ca9201d500c03c18502026114080f1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 669646816 1250 669645566 669645593
    0x320d2703031a060403060218120307060b04060308040605040f060c1509060f051e010510090303080c04050a0b12090d0927020a0e0102060705031b090d050d09080705010c050613 77
    0x3d0505640d40c0c0e0b28a00280294005444042001012000180140740100100d40004907403400742d0710b0160705c1d581d4440107010561020b58440e561351408008240104003800140c282a124181e460b81407002000341854268080c00400c100526900c1c001a00540040c06201c1c040c0b00c042440d08440c5001009000c41401120510b80b401d0304009071821052030703104410480303000c0c0c082280d80b50020700850301c2d65000f6400c00310301c03a90070400010f4410454a940007060f064070608242d16000046e0119460ba4071280d5011804134041486d001411002500908804014018030307a1030a4003520705d0303d0034480c03040e190f6000c402c0c0e144101d500210448110810940456886110000103000310b1421003585005202d84070004510500a03821640070b003a01200d00c40f0b420070008072180035a4030800c41e07540c0140081c52a00001141040b0b414030200141e101c01c0e01990130206110719228041d4409810410700e46428008940301045e015081481d01001c06009103072414078040f0b04107030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 669648066 1250 669646816 669646819
    0xd020f12091f050606070b0709030f0b0106030506030309011d060c0709151e051005070209070e011103070305030f0901060302150706200a320d2703031a 67
    0xc2002042400458800e0800d080d100b6842040701c1008407240489100b190f580d1303003000042200002003982403420301c1e44200c440c64030503103a40e102e6590140340131341110115a503407141030061000c1505801601d901c61030a500850914903403200003041404190014121004841c860f61200c1d1201d40454130042148021a00c5603540c038071100000703004005064030200c54060011070761a6a078a4502440b6221008900341c1605003010017400203007040c400000c2c070130300700034140058440900c1641b0441003502c41001c1c40b251100050008003040c6041e50694008103c80e4001a03045820340307822220100c441e2281f80d03501d2107020300500090b04003079802b6004418107404044008001d0000d0340c452034003406901202c0701c80c2d0141d81c51012a4001440b401e01000f91410700c519100c00690501102000c060041e1100b141201c1d00894021102c1e41000508600544014003d550fa0860344e20240d2120450b0800140a01207201900a08150b280c207481d0035013000003030150140d0b120 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 669649316 1250 669648066 669648097
    0x30d1a0303070507180b010519051b0c0a0506160f050f0a050616050a09050d0314030a09030e0d050a14030c1902040b030106030b010506070c0e0405030c070e0c0d020f 73
    0x141c40c1003c0e0340d41d080f40d10805040038070b4180c00b0421103810380202e0001e440103855090900340c40380252600307510b5030701041c1e00b040701c144804039902c0003100c0c82d0407403402202d0180c10406c1c0300c481404100034903501f0050080d002044103042c0180141c03210420580c008034074220001c403519202c1d00713040e0300180b0011248103c00406050000210f04180281480300140e40010342480040d10b81c0c0c0580a003480110700d144004105d00d041c0407032002c040314401d29150444030305440b00c00406410a5030401116941c6042d404109500a0010b00710400200c81440c0c681c0031b10ba68040c0d0340c0d140d80100038200f0894030381407401250b040080d541000d1040e4207450703454503036244101a00060311800d902c030b5401c0c0000b8150760308042c4030700c00a41e508070030404556800c0c6000d00180d0b52003000d0407203401c000541c0000c0c04c0300c55119103a0140c1d2045024607a01d488001c502403400708150004018104414180000c064a0710211007885d28520002741e2160115000d2403110b00035145003416248 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 669650566 1250 669649316 669649327
    0x504080d110705010e2d0a151508031e04151b3309050706050f0c07090504062301050f0112090b07031b02070311030a2310020c030d1a0303 61
    0x701d0034521b0171070b04075001c01c2c0b8840340410403038a03406515091800c80c0c100801000224411803002d485068002030085420f402c000c485000d41000c0c1d500ca908250070118501d412031206410b04800c0880c02c548050a040c01d007000480f218000441001c180040c945007640c2020300d1019001c400d0ba0401741081c405034008030039850890f804e4a641c54450894413a1444040c41417140c0b0303d1468000c5c00801495040607402e0b41c0303d50110307182d0030044034140840b481d090410030a88002d0464004c02041c103040c00e03d03010040d00c18500c2c072a00c40800c421b0710b03103805071007550007581110b01c22100c51042e480c1c01d400503100b4060fa105900d40085c00c0040c0380050000c070034030450081b402564100520400400d030001128030940142c2c0040e04050400c01c007144062440700403981d0000d068411110075551b42040f000d1001d40064500c0007414402801701c602400103040080c40c541c01581f501540c4d8800030f45030311070401e40000b00f86c4d072454200240c0c4801e82030310840c1400502183d903500d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 669651816 1250 669650566 669650591
    0x6022a0102010605091302040506040e1005060f030d02011e0b01080c0d09020904030806031203010602070b0d2a090503031903090f020a0909020405010909020d0201050307180f1502010504080d11070501 88
    0x1b4060350b41d05900460030300003c14181c0c02e040c4071f903050b80002c10018107801158442c5880140001424859000e00c420041c441c0c2c1e40e5040c4619005c041080e00006041c445804c20700300a148040c03100305100c0c0c44c01200e0703182c698000020030380c804c0742d12210a59881c4020000d030028080c0400180d00403100c50f040104064004115a000380e0307040342141c5412030303640200101c0380304c240a804010381146000b00041d0f80e5180140814442d00744010610350032400302c0340c0c0d0b00c02040c65a0103c000a103c02c110b9800c0e080540303807000e410250702640c41e10113406407000040c0c450840300d01c10166540000c00911801c4060110782650081c03840916641d2980c000c0080c003000d000691003189480000a4580303110f01c2107880c0e0744c0c1c0c0a0100c3d201c6c8822500150f074540c100801081c02d0103090b600d0010385890303040a0300c01405403d0725054149050410382c81d015641090480196894242802701003501d1109a4424491102c404940d1107100701500300c1900071010300410343c0d800d003000c1d10510b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 669653066 1250 669651816 669651841
    0x101d031b121b151506070f0206070c1502010c08010b0c0a0204050c090f0604080a0308070203070c27020a1d0f0303040e0108011415010c14100f050106022a010201060509 74
    0xc040030b402202c450600d030b244501e54500081e90a41e044c0303101c0743c50118aa05009024101c0303140603181032203000b62a03402243d056800481c080340d03078140000301442421a0210802d8038500e0b244002c2007014000a030144c150305060050500801020503483e9200004000203080c0030b078050700620039401c0005044d65660400400345204d20756607425040340e03003861000d0310100d920050007880c05e0301c01a10300b9103030040090688001c5000c200600c0002c20001c11502009150003051311501c40144207000100350000700c000c2442c54010001e044400d0380c000003108107603180da0802d00003002c05100168030710380c0301c11090f6018003000c40c0c001030303500e111800c8904941c03209000340701c02100f03034100c4440420304a07a642030b400088030510160354403d401e0907040c40e21920100c0000c0020706075591800001e5008609425102c488a880502e854081c80307005110f06d0000740203a4603040f4110000c071b0749600c003a2120f00c00c00e002911441c1e01c00d4012400900c4007612002c401c0c181480c44801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 669654316 1250 669653066 669653107
    0x1d041b032108130c0302060901050702090f0108062d0603010204090e0604060e2d01140f090f06090304170c060c0f12040f03110307050909101d031b12 66
    0x1060821000031600f84a12541e030100035030280f008251542950300304011a004181142e040000601411b00140c40d00348200b07018221002c1419003542c941a80149010002050146510254039a0b01007144c540c03040d050504c4001000603c040e51940e0100e40280a5075201d0340c0050b050402e20b180500c408543c0e035000d24043c0070144035240701941d820765100d06054115001140c0180c844030f06440522051850040440c004600c1d0301d40ca20308016008000c2d0b8040d000101001d080c050480400c10954101074503110281419152024025441c0d000754400c25941c803c0c1304c1506a04c095090102c40a0b18400418090702c0b01514601c29640d0600e17040e1700400d51055404c0c428599080d001a581101c0700740d201d0010382c0d400c5985585941032900d00311038040c81003010229169403842c0707005224070340c200020088584040012000e0711400702c2101c0003070314030000c040030b404408022100e585100850b00849030055a04031886d0250390326801c5111200813500c00308980c1c141d1000c04 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 669655566 1250 669654316 669654383
    0x50718060c05010902130b0f0d081b0304090203012309070f0e0307051002070f0603050906010611030c1b040f091205250602030403090806090706030b0609091306061d041b03 76
    0x2208491238401c2c0010480c1284000c0c10090043c0086030400080c03000c100c807440384150659081a5039000070340c060f030304203810100008444881c64605a15840c80b41405490100c40000c607070f003004640035100011000701c1e0300070030460780021211920200000801000060001e40003241d580798025110b007a180160170143c0b0313014000144507071090240318000d0742558013030040760b46007582c141c3c0c0302c5119211405032400103000a00d85c84c1c8040c00070008600c001003a040104003000100002c580c0d1b6444a08402480c010001c80451040d0810011440c1d06041071540c0310064402c0040d8a504039828401c94100012078004200481d006540921300c0703900d4111003642ca9040964a480c011521011240d018860402005110350040800d814010b40324602c2c2c0140900400c0c00001c0480300d0180440c01c2c80c6070902000420b00c5280001c00303007c035034580c035107031300002028420002400140003c244082c8021014018640410007542d2040304010400000030020750f260b81002e1190703 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 669656816 1250 669655566 669655579
    0x71a0604021318112812051302011803080f090607080705010e160b0316050d06140907080f0f04111c0c0e0c07080c030708120901050718060c05010902130b 68
    0x31800106000f041e0b0301c50705c14002076400d07200403440e080800102c418400404000101a10689403956441483e00544000ea0403e091096030300014050003005400780003449d14103c420008240300e1400d90f2812ba059900d0150794402c841e0004085000b41d01003d0f0000400082c00410030405500020000300c00c8001d8030f080240c2d0302128502020944500070412808000164881d40307051a0301c1110030450030494201b020005d46401103500d03581111250272943d079041c0c1c48a01e000c0c100c0c039600c44514602050070341b070303d0b075080e1060900103024000142114004102040004c0c040d040e0072003c041c1a0010009001943c1c00070202a50400d40300741d800300101141c800c04055401d8460b501180f01149008144c5d56400d42d554040c110825103400184604000180302100900556541d41000303900b40c246440c4040c01c41c0c00c050300e80340070300200c050308201507134007500d8136000c44a180c2444e240c4a01f80d0700300765002d0304000400a60092501209e0503400d111640855040c0c0b8064915 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 669658066 1250 669656816 669656831
    0x6080312060603070e0909100c0c1406090a08070816030c1109070203180a0b03070908100e070302100201201c051015050d0c080a11071a0604021318 65
    0x14400c2d203200a403821400921881440c0307203542801c640c0c29420825034000c94001c40048401282192683d450f035100244403d808441441030b038000c540a80740c0d950b0050020350428000c01540c81d60f0f20500100034140214561050101040c181e0b4204014410400885011441c00a01c804452903007152650740b980f80c04034681c01c01414032403007420150000c0d442e154941c1c22458029626403070b126800001c095021500010b0700307001d980121400e1701c84043e201c0c00d1040c5541001d10704462161101d2400101002d80c410019800044a4054a8189a88650800881c0906514010304181c00100e034400d07455940880020040031700e049601d100359401c41080201034600a480d44c003558032504c0e2051050404851040c0c130708143c1403c0c41880c003001c4000820a5420001105c00410515000c000388600140508501101d10a00083c5014010340d116003c0c49680a03501601070301140001e0040d841e15812941c100c1c841e80145c2d00079507520b0a00000d0900c6034801d00f8140c1c7d040549 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 669659316 1250 669658066 669658069
    0x9080f06041502030712050a060b07140106080609030301061218050d0906030209150c2a0406140d150f020d0608101e020d0209090106020105160f0207180b040608031206 74
    0xc2e1390054604d5a100c0c1c140c00c048010b6440500006030000d405242e41c4c0100181c0000d0a0000b032110611582c00009155000074030142100c849034810207c5400000030019080300c00300130ac906642d01410520a01c0d42034441080042a211050740070008540d00c070b00c0140040040c0d4031620b03547c242c1d180c1c5003507a11250300b00c0990254410042e08082c2200c060000c2c2c021800c0a8038010800408a5924003400b00f00345102d00422940c010100080030303941541800e040c0541c0b40944072003c1c943d15007210042c0400d0f0b4035094a400a40301c8079400600c40040c503040d402140340c2e101074102c159110040780414600400d40e9105004c504c0c0b140c05007083c41010140260081c0c0d40454817070300c00140d00c8054100203981300210304250030741d0800c00c0c0b00741a070f1808071580c080d001c2503000165030300d820441c0c000040190580001485190003100c0d46076640000c1501c1075075090f00000c80c3d03036228080c032031010701554111190300600301580481d2501c0c0c002701410345050304109100301500e54a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 669660566 1250 669659316 669659321
    0x60a320604060618031e020406061106160e0d110a060201020d0501080d050f030c040308040b0703020f12160f05010e0c0a0f05090604091407090b1203090d110109080f060415 76
    0x2c9004d04000054070810215a603820300c0143c4280202840140a20a600107000c8801c076030000b4001c11801c00c1e01418500003005040d901c06002921310700703161414035000d015281070b1030703445104031020390400041241807880c81003250406008a0485600d8580107400717508504145510301d0300c2c1200000b01c2000020315080611050303100c02c3e2a1043c110014403941d03100401c1c110030302c102041b0010001d9a118000c3c0020304d21100096102d44442c0b50003805c011800031401c3c1d09500060011001c80c00010444240c100c00801c01803c054803807400b01c01203203485ea400b500c1035190210011541801081c0162064402c0320210b0b612030721568415000001c6c1d005854018000500080342420076038000e41401380202d050704e40504000c00418688281500601c000f5900c0c2c2c604560719003806051810210800d1001e14107114401c0042040202260703c0501410b1900040c294140d000d0411580500700b20400e42d201032040c492182e07680c1c0c20940f000c4812020b04c614a03074800c3e9051 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 669661816 1250 669660566 669660587
    0x20a0b191d1506090f0403021504030c1406190c030f021303050d0f09030305250c0311040605060f031b0406020a0312090b16030f02040f1412060a3206040606 69
    0x2032401c0c240e502e070200c5c4d40d210860010000c80651060708800032450001d03071600f501c128400d80e01e048452a040c94001d2102410018805a07130744004180311420314003640e81003a00c18036100004525840050480242c045034541061051001070500a0340c25040140c200303880c080c2d011038101010081c1c0840750b09452041182c0050003080040c40007030302c07400062035041c00d8030f42682351000c1b000138114100001d09000f198160301c0301d4010800c2141150b1840c0318002c5c02c407000c1004dc0c0c03a00340130502c10711a0030384148070400c00000007110318000508200f800c2c08154040340d1a41c1c1c81e40c80107503960b20480000da0110b10102c41001141c1901c0c02001c2c5020350189843c036554842840500e4480240601d50007419244da14510005200f4800381c0010b10704900440c041d986420000f44081c404144500e02442860043c980d8180d8005902a01700510400009003282501801d940c0c000e0300360a401070003600300d151240070841c444071440c041d03082160b003000b49540e07844040c0c6001510 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 669663066 1250 669661816 669661819
    0x705030a11010c02060406020312090f070e0c070b0405060a050c030c071112101a120d0503040c03080a030504020906180723040609080d02060601020a0b191d1506 71
    0x280c5000015525001003106650103040481c1403800684c00620507801c69080240140c3c0085080032036610341010b200c4e045504034020b055941104a441d5840d0503003070040300f24003a164008144018135030001c07140c0403034010b00351014a041c60b01d480c070340f01d040035038200e40750318109400701d103044410004413401030301c200d00310300d141c02c0c102d6881288030481151400d90200d001070120721195030910402c8410300e4900300006003051000084c400c0758007a0b400a41c0218208408070000300e50008076200c180b040c909203107860703a52302d150180040c859508010051540814a04907071509900280e0080344225880b04035039036140d00b4030801d020300381c0d05a007100e2804008500d24a00400080c01c00c10001c003804011000482140212580f1940c00303a0000f4041200821500a050126000c40180c900c0a48164189100001c3d41c0c0c25001c00003810650100c400b01c0c0c2c0241c20343d07001f000b04000b04030040c0b10300c0d81949110b641d100d580b0030038450b941c004c540640f404c1c210030601381445000e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 669664316 1250 669663066 669663073
    0x3040f0801050f15120a060204091409030a200d05040f09050402030615211b15041809120e0a0906051c0c08060c030601020d0305010b1e13120b09070503 67
    0x840c0c1d510b0072000c001084445030417030070358450402c1c4e40c6800d01c480c401d0203010f0b400160b559481c1241d0707942100e0700c01da04810303004000000c4c0965a0f60101c00c507042c480b40351a00b018020a03152860b0f08800f400903485805200b50b1030300202c0580c002d4040c00455840100ca4105665074010502c107603081118000d505401c06000980b101c050b01c2c0c449102500041d005084517a416500d445102c074201c0900d20b840d0303000c00d1084004d00c3c4070454141d1489004d40318082d8001c0c10324030000c22402030380603100c000161100c0408030102981d109840c6a500080c80001502719044054100d40c00c1d006e07007a000341c880708400b0604035100d00901080311005004110480c030300b16404030b0107032074090b07080341c004009032000280e101b01007107818001c54503140c8181d80e0f0b0518600191414203148031640030b0608100040000d0004202500c460900843c5d241e0419500e0400503400c5100d01c1100018035401c500010030508501040445564810050b100300e6881d603ca00769034035661403280319819807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 669665566 1250 669664316 669664321
    0x7230a1a010e0114010c030909090b2e14010e062d040b09040f0603060207050d02010c030501031109071e120e07080a02010c052118040606200f0d0203040f0801050f 72
    0x501c240d90046c1d9241c040d240101001d5294075902c415900c2c2100d05440d220010320501021880c507000066012800b1504030f510390304034222000340d1040038031640400f100520443e01280e40100301804a6600080016540c1c0800d1b0b120300300340e602001d80700070513403158420465500c8409070840e4141e801c6072400d1420008030fa001c000280c0b18004017071038040c1c0c0b1450000000f403424000380a45521803005020480d0309444001e0844008040c1d000c201070915004201081199650601c8071506071880940303562050019107a00121030714034198070b064210350640c046d90048407a94281d1461005018254010784855a945d5030b502900583c1d03041140c8460040d0301910040c0f840c1e52180081e540c0b074500d1900440e1031100107521401c01d00d01d00154004110060029201100c1e404950420070541010001000b4160800c02c0c840105881c031200e140c082401c00071203004680c0324040358240e041d41d20000303440b07800512503078400718450400820070500c103000b9075105d070900c5a1403500a6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 669666816 1250 669665566 669665569
    0x30e09091c02030714031c0203190e160e01060e180610120e01020a091d0f0915010b04172a0406120c0e0601031107230a1a010e0114 58
    0x481da8495401540b00820000300052180700e003141002240f90095600c40c1c509180d825420340522000281c598410010000203801c1030b1007204000b214510005200001c0002240c54001404e55a000f200741640700018220121411710741619056603441200400e01d00a0140310038000100b0400c00c640040001c0e1542080081c2016142c90392400f41c0070900407a541c0300032903032542c0d1103108594000030303844141b84c6c100181c0e034002d0401d200c240b202c010a010420709520070291010080e01c00400100d040e01070b0800c5070146038100b40c60310605075656524514500d0b44544510801800700741c456009444000c20304c6004191288040003180224a510781b801083d50710340d00303a01540d60680400c1c100d00890751400940c2c41650070b01001c6041154596140e07100030046030401d42094001010001400240d0794415401380c1580508070341031601200e150202c80700e4020b140f042c0ca01031424170801c401020b410140502102446980720b0a11541445007401029400c00b0991180c4009 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 669668066 1250 669666816 669666853
    0x2130302040510030803070e1f05121f0b030a110a1d06040e01081609061202060318060708040b07020706080c03040c08100b010207050d0218040f051207030e0909 71
    0x4811810f80407076000b601d80d034a107901a0020749a0100090140350030b888682000140402c03129101c280c000300e004810302e0010554881c401c060440a46420041541207101c0c41ea104000d814024200701c031281c440d1440c203c0c0d90812111030403190304101c5802c51403440307101100c0c3d61000c03507511510645898210a80e01e1214401100d403c48020403000404018440125010b0724090010b000c3d980035140f41441000c2c0c150b0000c1d031001e440d080c420031004520303101d00250383c2d5060300c1858403962120a00c610700c1c1c3c004010300c402801a541003185a40e4080011032040348034202d1058141c403900e804a030365013220301030880820355000c0031030300703010f8800003542e030161003800c81130010350b20740c1d801508005c1c502900100540c1c4459104800390780602140d00a09000d072400081c031950703500007403400b801050b04140c50340da40c030000c2004d10448003d000443c0360040200d50501030000082a070907070000780180d0000d0601446c04243e483c001000d203000e00807002c02072151044008001c0714 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 669669316 1250 669668066 669668071
    0x60e06090424090c030b060915010e0103110c150c0405090402040203040f05010c051b0105160c02120a150b0102010c020d0807020c0a0902030915011505090a1d040213021303020405 79
    0x140d00d002c00e61680d01c400080d000d0392008510481418000500d149403c8240c1007014210303e12607512442040f03180258811ba40706198401d19100c40c4200c003000040c0d00030891008c40240410000800f02602c0c9400101d9103640d4806654802d859542c1d4100e0340c44d140614012180d101041c0804a405460182c014542060049000f003d8688150b51850708441d401c0f2402c0c00890404100010201030080c7c288611a5001c0300a00251610442410080002882132000c0c00304004400d019501c4800054044503e14411201000300f1170503ca16540c0e501c4034185042c50610a095840354418000d044070401903400420500343c0041040d40d1490000b07040c2790443c070401c02c100c00b207a520014208024581540e0041e0399007028001c01d802d184c80018212244004c1d1401000744800c0c20000705000c001c84e10300740d41c41d0440900012504681e035882224031150f2900d00c0ca01040d81c002419000c2c0d4402c50f04003000d203280188030800c0e80650300c4840701108002000f040035044c2600a160b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 669670566 1250 669669316 669669353
    0x100b041e170d03090809031603120314040b0a11030a0902040c090602060601270e090c030106030c0905072c18010f0e04020f04051e0105060f032212030902010201060e060904 76
    0x1d0400306c005000c64030705584000c00102940c5c9861007001404101703000d01145410078941440405100000d04d1305604010b0700090007101070500185520402d52320284052401015140d524141040c8000107000f200509901c180d20b480745240c0d656010b00112000c91704641c014140030b0f076030a401951004514000c610005803400c03950080800c1404180014010b0130081d80110300f0034901c290700c0d001c16503640300e0103a03240c43d03401d00224010410100480780303c0c25010403103503100d030002c403181010140592405030b8600c001500724151003811501c40070040c0e58080c0a50305d0860340d0030316040207106541e241c507280c000611030110345e0302c404c991190019108201031401d181c0424201c034400c441c514501404440c000040c2209502c00a00400044826504118250804a1080c070010780600304010300c107100c0340c907914001092640304541059036a176106d011508041c0140030034040803401540303000d0000c14010b400140c40c44c0180005480ba40b00c9070344174de44002400c5d01840881 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 669671816 1250 669670566 669670583
    0x7020d080121080408070f05060f030c0f27030d030605060406030207021c03211a060702040902030a03020304060921033b010905060702030c09100b041e170d0309 71
    0xc0c0007164440f4003e2000740f0105004280c444d1070450549000c00040d00f1070351107120100704014141708044207607038000d2081380746155034107840f101c2c25403244205c2d02e00c0d000100d51b04c083c0f00f4038810403146100724172000f542a01c2440a0b0b902040701140c4850003074a43c007500c00e0009200b001c0c42030740580b0346948003030300c0d505058680c00040700420022503001c1740003505580381428580400c107144a440d07045010140a0005030a04200741e04520700b1540b03000740004a0782d28151742e40ca030040384106801406860400f02d40e810000d45030783c0240940004503081c00c070300103154650070701008001f101300c1d00c4020484486940444008810000840d2403800d20801440d0210719105281d803a0440280c0e06d02d50100610000761515800340c0c0050b00c2a007040c002c14025890104001c1803400040b68600181e031340d0b001d91409140200c0c4c01c50506a103000c80c0c08100e84d031072440503618007510080107082c16a568000c448151700041d40c1400b0b01e8011605140d80140250407000b500c0d4032a0301f40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 669673066 1250 669671816 669671879
    0xc03070311030f070e100905060f091e100e030c0d03110712020a050a030201082a0703080108010b0604120809060d113609060d1e050607020d0801 64
    0x84115001a5592908044035901384221190800c1610402c284150348065900d01030f94800381100d50213118150041000040c1d8142c0088180c0855101c181d0003011101190202841c403000c0c41c4000300b21741e01030032007101c0c50700391a80941102d4140400c001c008141010185082c040c085246040803418060511050350103114140410400ba00715145103040c00300f0035004011080740d00b80e21044c01410032490074000740c0d80c8040c00d554082003548640c6a02580112201c40c0c40e480302d1b1020312400c0380422070004165114410300c2c120f82d1110001d2003143e03040801c1108a00c914800c66590115407540b1200003176003030002c0c0c00d02101c014095802c01451810304010b880c40390300600002c900003c7d503d0b00220440410301402108801c0c003418544070f0340c1006003500f800f03022051003040381c1000181150356110700d000c00d83e80e0000d144100d090010242c10810b540f071a1048495010302000603510360705c0000c04405008140d070340c58050364600300880c55920346060001100c0340c6002038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 669674316 1250 669673066 669673091
    0x31d06070f1a070807261303120204061206050301020301080a02190f03120f08040c090b13060b030f070c0206043011040623010302090a1502070303140a02060c030703 73
    0xd143c400d480c0350b110314a8510b0134100040c60541222082a0003000f84900345021041c02d001c2c0a900c00c0d1a98010200c6420354103041c0c42d842503010380500210b0000401050071584440c2c01104208440006c2c0700007070f21102003600340d000034000c0340340a40c4844442c3c0003510784407848201450510f03180b40c52080e1250700b5562000055001500c0784018032111505140d80840248042c1c103007480c00039071a04095039400c1800601d40710344501c0c0780c0c07100e2103000729541d80d642149041000704003c004840c1e0380d40e1100a56001111000100384200c40000c0e0480c1c010001c12440a0740280071314580b900300a44c410600508a4446143c1c007a48058980f401c0044021180304500408480d44541a00b05c100000d46d01c45070001030f503414503c2001c0c0b12603000e6000c20070050350242009600c031403140c40419184c0e609940026842680920104d880a8010030b40b0010303030340250b0b03420b0b51000d070200c06010700b807240c40b848100603800b803000225041410b00185070402010300d408035410350301e80d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 669675566 1250 669674316 669674363
    0x60503030403080d0b060d090f030e091009150512011a0303040f0b031e1008060108120409050c160f020a0605031611030f0c15070c0b0106110c0901090207031d06070f 73
    0x2340e046a1042e00a1900814075801502d02403400c0070881d01710b03c00e460812807114a0a602d0300c10000f12540b9242c01054251044004001a100107080781408520b040c0415020704141010130549401d0307a02d81741c03e24200803049609995000000014151038070a400d4030552004003c5403601a03c003104407034403081c51403001d0046012141641110341000305590400e8030691001c07601d64028004000040c01c030009540c101ea100810010309565a901d0740180d0b886807403040001c0e1410800c00e5801c0012510a07150302078029038101d02280c3e19110f00307031828442a6100140794a4103410f04450750311810301c1702c15040c03003541960f040c080c514944405580000220310201c0d009600d0b902c14094003a01441c1e840b04151401031880c1d40d5540f0752036030341581809030004100340000e80042c01902044400603081d006040d00c40302d90381d03840c80a0020340045008600103000030b08403c0703054540758400c52095a00904c1d040c40c10005554584d44605107138011101e0344180481c03d5100150b02d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 669676816 1250 669675566 669675581
    0x2f060f090105070f23030c100513021f020c010201020a05040e13020a090e150411120f07060504050f0d0507060e010c050303090f061003170304030203130b090103060503030403080d0b060d 82
    0x201e540c1d4145ca001a5032450180511358400381c0c140e4400d104000d1074079000144c01c400000300110000325900c1e0340060a01c0c030311814601940281c0306a02e540c80c400101c0d0807080c0303014512f60030307540540c800d50300480c00e034440c50400703100190080c00107000c0041e0704001c858000724880f51788907130881d00c0e90220310600307050f40c09415003a503943c05142500d24144100030224110407040d5030146010740d11044060b8040c1450341c040e5500000083c1010345c2045000c3d0310f440200101c44a196690300010a5540140074550155401301d620001500348210060220380d4484003508070b0b9402d0590880e0f0004003601c07454100420b500c0801d001c51003c1c80110b014107a140d015103c5841482c072101d181c640040c124080c02c2160304001c001058840c48462907460b40d050b1843d03581c0d110303030500301d2840c040c82030360060b00c1410200004044030540d00603d00342070300ba20b003071003071070350b64000c254507030040d440041d01d48007080100c8410039010b540241c07a2194000c011074105540e130a803010848506 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 669678066 1250 669676816 669676823
    0x50901120b1302090a0609050612060109090e012310061110020c030408060c1206060307120e01060303120e0705040903020a08130e330310092f060f090105070f 70
    0x355241c2c4900301074520001400c6c10781170100c0b4062070b003400300b0910304c9852140801c2c04020710214416a209405140c024622200309220f231403280025280200761803008415040c003d040c5900f0107290f03000e01507105039400e909000eaa540307454400d9a10101031041030b8158044c90103101440796007440039060364071074207008640311401c0a03503c524060000d07140000c1040c0502061102d84185c896140d801324081c0d551545a4403118400d881d00301a03001824096420300c035401024072415031061088134003a03901c00c8a8a070078032844400300d81c6c4118004071a90820841801182403582100354024424811a001e0100503103c103141034102d130610ba0703100f46981c4420486030702c104050716040010124101a810808404049203a180d42a80421a03400c400d40700816a802c0c0120449107080d40700600100080c3c1c50090f14012407000460180d03014440403480d810b04030031040000e0b81d00501607a24116400c1c0561105811a041140c10003908020b171030700003007040f1041410f281c030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 669679316 1250 669678066 669678071
    0xa0b0406081501090b0f070203031b0a0302010b040b10140d0213150203040e040b0703140108030705100603051e010204031703091b0907050c160602061f06050901120b13 74
    0x300000802802d15840b100541000741a8900b0700c00300c5031000c100c840900702d12628990b07406da0303440864218000c1b80c0c89060342d00ca100c07528000c0d10f1004907010064502c01c0d0f00801003880e40c1c800304000c0710722000300076800c550304040e040c820602407020340c00d072284007001450900d02c1c4401e009080c1d90042d00030342c64801180c082040f00740ca6000350b4060010840c0040c40c281070609070fa045c283e0030010809042d203403d58012480003406a03124144800c02000b50f00c20340d60b11202115500e5121540886151142d104044240c0050303106840541794404090b2180e0007012007419402041c103154a0441d550802000002803500c00e85051020b032260031960701c9242c1440e00d0344c01c0089202c10440c8180c2492000c60003591010107496101400381010740e01c031002c221400b440e080081c0c0e00314186444a40d400304040e1b070005071040c49202e0400d1260b41401c1500e02841e1058180e10484011440900c03021016600500b94150f160000d0346000800a0b0680002004001d410400021f081d5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 669680566 1250 669679316 669679321
    0x3040812070c080307080304080313021e0a0509010b0d02070227010f0602030c060a0510080a060f1805032b140f01170619321b180a0b040608 62
    0x200e82c002d0074000e00c20341000c3c60038841152511540392000420061503190300000041044801e600072050454014007040c03140280d0356944890342808808403407151002d914001800d2070800d003450305894481d0141410510480b9140029401002040382c2c408140c80c048421845c401f55a0310410000d00341e03120203549401c040350014070564105074119001041100d00c010000100300f5080a0800380c0050300c1d540c1c80324958503d0341d6580210846005030b8401d507040c070265400001000c800c42c801000042540004a0344920301c406000b04690024403444020001e07412805800c5105a009408500c8035003c08608545440f000c810100941c4800e005101d0504040303503024044003005d042c4203000b03030400c0315a43d0b200100b03880c000c4181ca24600358421096081008400e840c0d48400641c1c10b021807000c1098448602103240d181c5272440007500e041401d0170a50040c06495803020701c0c01c1c105410011171502c1c1b6501c8150042c4140303000003108415a80200700914840c0c0c0c500e0200e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 669681816 1250 669680566 669680573
    0x130b0c0706030c050a020a020d05070801090803180705010903120c020405010e091605010e0d1719030b0405040b060d0c08060112021306050a05211f0c03151203020304081207 76
    0x486903003815008218050117019040c980024071a101140c040742c1c03004c030a042c28a0840c0c40d00c12160840d03c43c40d420f0400d48002c010300c400145001d02e00c4101c038031107014032001c8940c2e038034100c5205140c00200842c40800110f031940d0780c2d01e04514241e18001203080d03426000b00d0113036107080c0e02c280e01d0514864108451b000b01440403420501c00714191464003440e0030f00090003650603101c1a40304450b524800b108010041203d00c1c07008410b40307c0561580514240c6c40b031a050840b40701d20200341010304a4629140510801d4862940041c81100701c1d21000c0510026082d00e00003294a8160200042074442003000154000c2081d07100b02d400102e4140705200140402c0040d00c0c05941c10a80d060001e60781c1c1251070f0068980c280c1d0043c5240c4510384003444e200041da40c0b600003602130b005401061011700041d80322100f07500074042c0000e45600030120100d6020701c00d03810300c80c0d0401070f0500100720300810840c1d04078007a20441e13040c01d0b00c039004241850005112405186000900385040 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 669683066 1250 669681816 669681821
    0x120b0a030311160e01060e011e082e0918051005060127061b0b092a0d080a03021e040e090d0503060603070309050a03030e01151208130b0c070603 64
    0x201948110442d40e00d46201c0500040701802450240300100c00c030040c040e4801c5910800c07440307032040701080800030031402074113488069668501032040d00c058000d0041340342f107401049021520383c010b2a18030304400d02c402020000341a003ca1143c02d1040001702c0d8040280140e4030954502c0002c40f410400c0026044030703a000504030013580c040818014200c3c4100300002100c40b10b0820b0303410180103010002c03206280f908020000310500040c80b0710500c000488282004c040f1845021105049078401c11a510307441070325900c01100700d1000001000b0300301405001c20282030140c2000c84da420f148106100040004004a002203001c1186883c0408901c0d0490581c1024005000030244002d0141c44002d050314000d007000408120950305c26031244001503000020741e10321030203500c2c2c01406443c80d802c0184441d130030300915020b03c0d4495510f807401c80380c520901c2c901c0d2004907522144c464200c1d841281e6840060f034800070315031a0782e2004040e480c261038041c4c81014100b5001408 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 669684316 1250 669683066 669683083
    0x80301150e3118061a090c030403170622020c121306050301060c1e0b0a0b0901170304090e0c0325060219080702031e03040311061207120b0a030311 65
    0x9490030002e41e40850315100d450f2034611904036802007030488070814620103005c86910000d8101c0102020850603d01880c05180103c1c800c0d0341c0c1c5249020b0540307050041c110181e484907070240789075012001030034290b8901d100b03000300c0510141c10300a807000c019080040d41490407242c0807000070038160300c00103182094041c11b0581045811541420b1b00100840003010b401004c000b05420a140007030703407121003003106a90040c0d10711240d1802c807555401812480d41d24500070281003002140c0203c21061448103000c880300103606261500100744045c01d4100742ca0110740c0125401c10565460030f008803089103140100003007000c45008144000300416030712800c2150802c400415200100c841340000c1180c00a0503c0d4583c5145c0c00003d0a11078034118000d60304040680c000200c8101201610880b4041c2c0423602c1005500d8060040a10405140114200300a40041c09250042c0303405a8035065006000404032500c3e0046101200342d9042030340490035031484034408078003c110142c2c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 669685566 1250 669684316 669684409
    0x306031704060e01050f0d1a270601120e12090901140102030405150d1a0a060914060c0f070605031006050720060906070804030b0f04080301150e 64
    0xe1a142c0b070404010900511524514100040060030400c150b00381c10a440018400100411850202d410120310040181c00c0140c0a601518042d0860102c0241e560701d01c503400c821180c00550390782c0c0044a0146140056200312030f5a0a000b030140c000400c0707422080600840702564503011301040151201050340004d09210a44491513a80d981c0401513030304540050b180d115100051440b203401d24000c040200c0707a150300d015000701d45040401010060424150303011038043d5100e040849011800d4007070b180060101041c0000300303041040041c01500a540259000c045021300d5560809516921179400202c01000307000f00c1e04000c503c5000140008c1c1400c900c0c01c00985d5481d00c1444400003e44c0c03030007031030705039032240c0d900c1e108103c440d2550010304403681d4000900d00304c0c480e81c1250106654007512a80051819004550313130741e00468000000c1802d6030b19005004000c1d4012401440800c0301962210929846030b91801d82c05154220701c803c2610300386a000c6440040d02d00400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 669686816 1250 669685566 669685613
    0x20c010207080d050c130302010503040609150903030e0c06070f08070c0902070201080f01030b1f090c09080d0215040b060a260f0d0c0b13050f1506270603010b10030603 74
    0x51012000031b0b0144084950a00700b040c0c0325500c40c1000c0c4001e0000c05d03030180040d111024a1100748407941d101034000e40c0700352410442243c000014a85c1c2d00c408070b07100c6800120801c60003000c5542e101c070031000284a01c030b050780b40c189240d07158040324680d07600a2000c25004540d00c0d04541c7c1166000f5070003001e040741000150300d1a10713080000b50000c0d0440846080e020481c001c20348000310180094158a4003d04c030900113814003d02801c05849080554090b070b02c01014000e1012800d201020020009041d1540b031340d0711620f0008202500c819844034070042c0001c0c0d082c00b142070100c0740d07542401380c3c08100007034451010f00f007201c1549081c40d241c205901c2021030302e0700310b600d03003491a4010310415280c0d88c9040c4840e030301605006000d0164803030055034050940c00003c50101c0303403d070030100c904161500814860440409844c0c01d03104807262101041c0c21300e0ba010050762216000b400485c0141a820220300c04003c00390300c01d0700190f110b010500500c2202075020079110548000d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 669688066 1250 669686816 669686827
    0x8030703050108010c080a0f0902041b1709071701060e0a05090d02070302100c03091214070f12080a1808160602150601030e0f010f2702100f03020c010207080d050c 72
    0x4055160081280d0303107c81d5203aa1a442201c4242d01410b01c80d940036004001c1213040e00c4454000c400903920410000d90040c172400c01072840d420b81c890080100d60000c2245504003000c0004043d40540d05158035903072003030300103450742400c82d5460040d10340d03220020360380c00d002d41d845003000d0300240d9580030344d0302031f250400040c0c4840518008610700c07460150620041807808440281d030315405808000101004d100501400c0030501920840324012104400d9542542c102c68010612440d24110701c03603440000820b2032900200ba066001e03180c03070804d001c00000040440300c801d40200280d0b5224080101a11812a09800c00781449000400c1111144400701c0e40c0100014400350405440302c00c1040210300400000454900120080c0030a0000241e400000e107e0407400c150810041040c408030350141264171182e03150090701004469450a900340d031100c070843d0090082540c00c11003142c3d00c2c00c00b803019004180c4107225056031285d00b20340700c8080d40e1002e0207544581108010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 669689316 1250 669688066 669688091
    0x509060d14100207060203090c09010b03070f12150e1b1b010e0f011506110a111216091508150c0d1404260a030908040807030803070305010801 63
    0x400ca205640c4141120408159592042d04120040c0e808180c241e0004c1003080800503140c02840c40345600c00207c0303150704041030400c55000400c1c0f00b00070480c002000810101442541c5c0320400c0089801c0245000020210030b00484011142c0e515846e03240c1d82060001f500d0602209801a64030040700840592046502c8503078800c3c504800c4022202c9544120848401c1d0810b450061650741540c125800408001c2c1c0604082030000400044044012444a0040001a4000d03c5030402400607a116943d00c0104940da81c603030316070061500059900d90ba80421660010a829000c131600a07032404120005030307004140c8180e0041207254080c4804880054001142c100040c98a8495210030b0100c1c982c42c4540100c000d205410b1000d000b03803140213001445d0103144119202070080c1c11014003c01b40e180640d0010400a80400c041206944242c101341c40315401442c485103404d5541100f40e2030060a40d10071502401c000c01040485601441002c0c01481b04800906c0040a03045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 669690566 1250 669689316 669689329
    0x412030f031401081e0708030301060c0b060d170711060a0207030b090616180306090c05090708370e010608060c0c030a080415091515080601170a0606140109050906 72
    0x4040c890314441e0b07000c2d41008504020f1080103041fa41e00342c03560781d61a00340080c0765111002c010b03947c01d540720000c030f0321606120b80402d9400342c01c0040f0707401600100d42c1c1481241d100310415a4007120803030707244455542e403200404800c0796540051078503e103103142c030103401c2c0c4000b40041e56031b8002030b0400800300c01c540404c0002050703600e1f08144000b81d01422408000803a0405443d242c80c0115000400c00704ca005582500c500329202d041c180d032411001c0302c1a2104a40c604031039002003220001511007000c4000d00d0f10a401803400343c200f6828521000c403030124003550202e80d101c1000300170107542880b107140c000182e946024a480085903102e41c1d00d105454454003000012800141030140300740880e00e0b03540c0890301c1481110820304000c0c0c03091000440030758481d07141107601102c1410910034041141c00200140c100360b03107006c124081601d120407540c0d09078002c4200640000301c09100c0c50001e003690a005032540403180d0001050030401c0c3d0401409102e11a007440026642c60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 669691816 1250 669690566 669690583
    0xd0c2106140d081b07060e04090c0b181201150509240f060d05010807060e13110909160909050f0a050a1104080604110d03090e04080412030f03140108 66
    0x3625220b140681603d8854190f10519200e00c0044c03401c40c010149504022540404940032a03617400702c1c4810900c100401c41d448200c0003052505545010440016400050005641d00c0c5800034442840103001c1800c036540100e40e00d5450b50f44a140b0700240800103414409450705503a000404d19045032540c0c40740049201a1810381c28801c80c07d085542d031b50b00440c0200380050310054480030f01400c2000a0310b400c0c090b5000702e00a444010980d1441250038a030b034807900600b105d180004c0581458020404011101c00031001081002d605460b41c28080f80a9201007005007200750a2000081c12044581c009503e00b60a05050084001c2c042803503542000c0038001c0051941c903161000c00081180c04c40b804030218011400240400c400328015200381e0040070a80342c0918038030200103408034040c40080200c0c402c541d05005034805040d07410307406845a407100e0300e060303180c0414100d14515610124001840c01081359405503050050360020f0f07480725030307005255040401003511001398 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 669693066 1250 669691816 669691819
    0x30d050921070312180f05070512030c01050619030b06030a0203010519202506050112020414010e060d0305040b0a0f0f020615040504080d0c210614 65
    0x21000851046803061180c4954050034030101d40c1c0e1000c21145412080d04041400e0300450507056843c0b00c1640103004003c40300711403820100c4844584c0d91070701405003500d8401c0c1c545105500c0c0205054a41080400342d0b08840b000030b540300e5007040801070070364000a04450150200d00513104000000700f0a0800352988413002c000d1070745c0c9140c0480d1170010000310182d410760a00c41844424400b001260a54054054090090f5068100641c0000c6061161b0350036001c0d08102480a4602d108015442021f480f403008040403055250384094490030b80001c001520500480d008515240c0715803080030b96843d1000c0c61315850030030078244d890700c0186a1402400490000401c0500c04c000700c501605084c1c1c0c1c41c03a19008510360050071030001103003100108039400c1485440c0e5000289207881218a2403800d07565400c1042030001801e40038000f200c81171010301c040172101c20940115000f810307003a41e030281600f084030001c400c0b8449061406440c03502c0e02c3e0044c0507608065031410301c06d0f0720 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 669694316 1250 669693066 669693071
    0x30709092103090f030906021e1b01050408030c01050a06051c121205040c03170f03070e040e01090515010f0e04021512040804030512040e040f06180f0209010f08030d 73
    0x120068142e014194800005000c2c8440f124150300b0141c201100d00140c1d482079080307869010011921025a03402c0350080c0d215648155020a4651200c0c02044460300c0107140560810f1b80d9030200c2861038100c00240c03070407651103000700451400c1030b03c80c21000304400c66217a0401c9841244920b104200700402422591398601c404410368099441040a07100c80c603001c02ca2890641042000400c181c00f0483c2d0111490209001016611007610f29044041500f40c0c9503403101a4187c5210329030301000c030f420540f41d6949449202c0288500751006018401500107241c4045038086c802b881600b00d001400445074051226140c030052041d030050b4182c40c0481e410a03c2841d0091b1401555400141070205004000800c084240500100ea10072001c803917041e0341d03283d00d1032040d008134050300784038100c09400280410820540700e64141c2c06000000790915802c500d02c80e2922000d4010f0b10340f407003168008011418446880c038014041d004030f18034003605240d01a52a0f21449208109564 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 669695566 1250 669694316 669694373
    0x4080403050c0a181a0a0311091303052d0304050c0109050a080a02130b09010f09050f0708040b131407030201120b0a181514090a060f09021b1b03070909 67
    0xc1c0d0084161401740c000801c00f0b184035649142c192010704200207070078015100080450811074161009000c51075064607144c1c242080782d450101104184003460706026070b000503510048071248002e5000e14061000390480a03400c8001400103001c55009038020343c40108108202000410345400140d4121281e04144403002a0b40010340b1300840c038542e203c1c980d10000582800c03040c11000444084400501c00740ea02c2041d0084514001c541d440c01003001d007000a00050001c10003d40d200001404c641c038000000e03100c0c7e00c0c15009044107404140e004200510540da00150451007089080318180108aa804049440a0054801c00c400c0003509401d0141d401801e40080300c1c55000840060034460f42c4170f007080c0c030b944e20045600f07005503d2400070aa1140382d0340a80c2081c0d5400c04070a58415280c40885130003903020007211002c108800f5031803c00c0700418031483d02c40d41c440110660b07071500740324100742c03c0c0420382d408040300c0c81c9003031006400100b04484100c030302c11404aa00030b464 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 669696816 1250 669695566 669695591
    0x110306010206180718090204110c060c130302040c17010e0915010305030f070201090b030708040606090b010801061d03010504050d090617070c15091b0f05060f030a110304080403050c0a18 82
    0x2043c445100941c454100049c0d5138403410b48901401c1116060b0048684a03150a060b646040c031540c4880410450048070a00150802e500000043c0f5558500040da1582c0c22500c216110001e8001c1202400c6050502405070b40030007441410103505440c51519525580d82c00e40d50348124900c203000a8000309204040d6030080103120010640c81002030755a01e8416801400244203e40440d00185054800b10b2402100c2c800e00d260094103031200d482903401c104080d5001442c140090203611845c0040e2145500d0a01901303002c0c500c50001090041c0b03c4801c003405d1100c030b540040c8200800c00d01829099400e800b46190008a541003a0341c40101505000ca043d02c11414089401c0b800d2a18000411030013881c480c441050419108011540315030280380d143d0003921a45600c500b00707004040d42c041d80075009641280743c02300d00141c2080c40b4004103503141c000311800d03190240049010014420f06100c5184026000c0342c4107008141450114060181c80c5644222100e950341e0b45031090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 669698066 1250 669696816 669696821
    0x4020a1b0f080c01050603071202130b0a080a0606031e030f0c061407050307030b06030601020d0518090906101a0307051309020c03070507050402030f011a0409110306010206180718 79
    0x903070002c42c1180c0e5910440c46650180900386c42082c001d200d91800094805c102520306520181e00030180f00280d142c00301d049010f420302d0001d0307e600110a000000d4038500030070003120460702c81d401c041400792850900031021681d0758a0030b05010200b11101c000030764000d02060b0040c40c0c83c10300510402c06810042c009040124425100241b06c4c010700410a411a01a610501e040c1e030b0280400384c03518052200501060300d2050241c0c0c01903000c00d0b000c2e80580050580c44180c07a15010b10030b070760007002503a0b000e8250350003006504003105000080c06285ca180b0301611000340e85180354401c0041d4448548002444001045004601801d2203e40c0200701c400030001120290744681c0703c200c0c03094907070340f20710001c071642d00c51a2800a07140c03e01d8020b507032080900d003007400c90680c40c2c08030a00481c25001070359410808200702c0071039003034030510802100d20046d0141c10340f2840c203000003904e4904003a01e00c010f007500c14101118180303c0041c1003810780d1404006007504403c03000b0207101 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 669699316 1250 669698066 669698093
    0x6040b0a050c01050a0603120921170711011e0507030c0206270109090501080705060a02070305030301060302040914361f1514010c08040302060c07060e04020a1b 71
    0x1855080900344030b4a08240c0d00f2240c10340340036047d10323100000c3e03010702580c152125216013503400021040ca02c2100e1001d11494a06a000316401c030100103094200203040c0d80007030000c40f107405502d901c48000d560b00610380c5c1c91413241c2c4407818800480200c40545030380955100103041110344841401192a03003c10345588464807980c403184440162286c403001d01150100d1070003c3c0303418600268041d014007a0300d04882d80302c0c0107404002d0510050014179400201428154401e81400000140c0e04000440c000d141965005880350700384000768083d6984000d861100190903c1440034180102c1410800385a41c00348148070864401c0c0f5080c0710710b0320008644098003640b0b94038040320002c17000358a08422600e808002c60042d040741008002c80a008200d001654031007840c401e54000e54410b15468010703510345084c213559500041f07443d8040614508603400800003002aa504102144d41c800800c490039401c08a41f5200185400e403208041c10002c43c00080c448140004905d4100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 669700566 1250 669699316 669699337
    0x5070b0f070204150e07050a08010b07320709090b27030f0c06091f0924150e0c180d020423010812040b030702070906060c02040501050402070206040b0a05 68
    0x7030154034000c20269000900c2417201c040725050020b5856403182e0111840782c0d6894451210300d9003007082d1403d160b0019141124201601001e0000002c000805544010384654207940781c6240204101d0030030019500c4840e14a0520001c0b00024040d891803582c401000455003103002c0180320030341010900034002440701d01000980c50480c1c42400c005090994402e000c994040c0c03560070749107541c0c000c4802c15144a6045c141c403080310350040e80007820b0140c0540010300e10b03a103d036092041d8080010418039400e0399581d840084011140342801d005160401c07881140e80342103000600c00d4030400d9040202e0400a8480300140c0d610201d203025095000350003080b0051045c0c52802d031000381c5141e00855500c84000020302aa00041c03011000c000c0300c0d1480782090b01d131101c601c4a0b90070252680065004149000c110440c1c1e030301c1024010301c029a81c002e0704100340d0042c881215010b81005028a004022150240c0c80d020115401c65050041c01d03070340c40706045011110b5004580560 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 669701816 1250 669700566 669700571
    0x1b07111212030108012f041505071209060f021c0c030903060c2d17280f0c05031017151306051e0402040509031c0c091205070b0f070204 60
    0x200785020154461015055209420546e03000c0322840b102281d50b2503a455180700f43c0c20041405001c0c2411034a00900205040c00c0b0300300707509a1b4842c03131004041c1003000005a404841080701543c4004290944401e13400540594900c19901e00304060100064a0a10030404003440825204c7c0314a1002181c10080402c15180c4440700106070b6280030b04100c110005c66941c03500e2242401c101c0c402882c141e030300d07900c1d140c580b003c03003800300098001d12003601120104440c200040710303c2d4114040c4160100001450910b0520402c00c03106606801d070200312052080003004922082d502c4152144e80426a80c000c285003401c5140c05004503119960b13000c09001c3c000c07014150020440307220300c1a0810700081d618404008008041002d914110760420804140541801e900c0b4640040c4000c040e00d2601c1c000c07550181e080014001d00c442166030380d082201e885548001c801000d803510b9102014a00241c2d00e80ce0755030b01060041c034041082c00a54131000700840750880398090b0703024005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 669703066 1250 669701816 669701819
    0x30e12061801060518011404020c0607020127030203093304081005040807020d02040e1501091401080319020a383303151b071112120301 60
    0x11400ca41a50207189030070340c00c05101088030b240c2030f040302a41020104c021903d03617190810f4940c0011901c3c450755001607080208049900c005e020f194458070580d0000b0921001a0620b58810a1001c8429600003040055030000903404405c440310b06008595003425501c1c0071038045581114100300252204415980d00c0e040c010030701c041e000b203032124402d80d0345d6207000320207400a03104112801041c00408106890051034038081044007180081c100041040c4145c01046c0340a4002d000d180302e10700300e01d0041100c13030403c2c000c90b0003804001d03a4440095251423020b81e075a020f504c0c298004020000700c0c11102c18420421802c05541007160b844450303000034072940134144d0041c4004030503400d011071004a4000341c4241806219042250f03012805840030200594400760b2003440a4124501d0003802d540d0100100703001d08809090b8403105090030700100e0700c42d5031001c10030312400f20148509030105400c0e15130841022425503000c1c00c5056400c81850a21440280180e002701c4080300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 669704316 1250 669703066 669703081
    0x5030d0207030302060c0f040b07050705130632011d150304060f0912030f0f05010806063c06090d05101a0a150c0605011410030b030604030e1206 64
    0x108007003200c2c029000d503001621003111740e14482c40703980302c1609110003c21082104aa0f4140245802800b41c1e041d136407059107887c00906002406804a0409500c81c141400b1012502206d0081c9240c0b8240300703e040d0310501c00e00c0503409941d078100f6040c004403d882250607040c02c0741c402e5080310000e140c070246111200307120203d0b030400d65054130b50310728000c02e03040110001d2080990300754104819181c000a00e001c2100549241c80310920b5082e2208940b100039065409454081d104001c0a04250710305074090140c68944545002691036100101c0200c640c2ca0001c0e0120784031040b407400034030041d000c010600b07030302c201f002c0180c1220020841c01d00f40040441c1406581441d03500500024500640b2002c0c0b8802800030103030302043c40351041008031500130401010281d0f905015030b00d116140c03920b80450b9000d030302200c000c1c0c0203041c1c403078014a0002d80c0c106c40e02500b82010040c0b2030041020036510307000103200405015500c907002c41c250791101d01050301c5400c120100c030f24a140089 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 669705566 1250 669704316 669704323
    0x20f0a030c0c0e1e0105010e0a05120717010207051c0504090b0d080304260a140d11040608040b06040e03181c140c030607141c0f020306090901060f060e0a05030d02 72
    0x2421000d0503107004d80080f403150300c586820180e100c1c1c01800354009600389020001c3c150340140300c4a2070f40c8035030030000820b000c2036442c055441942d400010313152002800e00b10309020071003d500f1880c40120480c2e00a442d040fa00b55019243c00070000103400080d08080351443d14101d101610f81c000c084201700070458850b410400c10000804102c800c2c8500b8160404107001d8403841d0008640000c4c2e072041c00344070390340250400c0c0c3c502480104101070902007a0503603a005400540000d55280208410b1000913440f8640294040d41d08004880c07040040a0316070083c1203029411002c6c8c2c0001d0307484e6541d0003160602d19204540c02032103410451070008414500420030035424000c4a4040a25240c046902442080291150350001880d89035040b1590f2001c540c0c00350f091403800c1a41082c110b5482914449110b00710016a6030404208108181c5001414051a68102103062201120b43c21403542241c480303042c0425031030032000005400d0209608201c0d010b202d0889503110242d0f002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 669706816 1250 669705566 669705601
    0x7210204240b0a0e0105070501140403020f1203150d0c050604090608010b1818031303030e040b151603050c0609031c15050f060c010509060a0b01020f0a030c0c0e 71
    0x41c1e40005045544003052407107400b40100341d90100301100c3c11a041c1d94050b8000385205071241000181280000000d0040c80034242c2c0c0640050380100038041e850388013000940d20b0300c0f014075005401e40ca0710564003101c1903151b00441d40991140d032600401c101030000d920019100081c919a203ca03201c0e504000102018815a000f83d82001c0b91074805080c5041d19070340851501203803d92550b0745c130707030341d14a8005844008245172100300000c4071049012030600003d0340c40f0b5a50313082a80040f504001c252002a50a1481005905100882c000e101c01c1180d02000729008199a400824141a2583d000344a24000e440c0100000c0001d11507001c4000c100895191284d100d01002d52400d01c0d0441d120610307403407070051a01380103200916200b8011610070f03500404142c0b0f002c0401c9030076401d6030820b88626401d035000071b041c00210f44243c0513020a51100784000c00425002c0d01496540d000c2070300c0b0190501200440541c14040c406680501419a9100e034207007500f440d0503000e00c291200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 669708066 1250 669706816 669706871
    0x5131e0501031214030411220905010b0108090f0607030e0c12010c0f0c080a03050a09020d0b07021c05090402030a020412050303010e01150c020f12190215090307210204 74
    0x3010084144c8040d90090724010754105044c0312156481500344201c42e000e41c0a0380d04039104000b07040c030030709045008407021940700b4000070400019401c005400c0c0f46000d0001c903030702d41240c008a04010000210399034007401901e00031885042108105051400008055410034040395501d01c4030001500800844486607443d001489074032903044410030300342803008003100402c100340c5c3e0f4521311a170002a0400440c1d200001c0481e9a980020701103020f0010850301c0e44004001c000da119014040340c100c15602c40c24007800303031218405c0200305200d5011081d02c11503000c404a10168059419540901500040e140850300c02d802e080703550b0b0304244608500300000c44004907145141c0d411401d111105500c4211001c600341d400c01c0301d0911003215181e00440809a100b482010400096554031030a0060030048005401404000011042443c0b4440000c1180451035100010b011046411a001045a8680d11147c4018154403103038040d6009042c41d105441482c580d03c00312030340410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 669709316 1250 669708066 669708077
    0x111070e01030515070219151e050c16030311071202070f0b0915090103090503040623070f081b060a2301060504090905030c010504081201080705131e05010312 70
    0xb1080c051031107104111540401a0410b20001d038007003010460040b2024070a0a4482d6008014411001280e40e020709c034845410442440201c038901c01d01c540b51b0010b4035098041d180450342c0e2007401c2e404454610007000c250383e40b50000d0b0440f0312079042e00c1015900c07804403158040740c14070007591504103005420351070040d140d002844d000008116440da100203440c2d14503400301100d0a01282d0000400315060503111950032002079401d00040010305025200c134202d4045800038a41c1035415200c0d40004c551080000c04003140d42900b12170210703580000d6169460303100345142010041301e050701001c2c030700c1840c0603c0300303c03c0c46400098040100d41181b0b107520710340d00c140044000d020f01c02d40c40803403001c2209000c82100d540207105c105010b01c08481c03404050000c5c035400c5641c2141d0607540d48101041c00032040091001450040401e00020301056040000042d840d03501c21400e43c0030282c0d50b0306c842c1e06000031440303101c010400314901003040f2345e0341e820030f50706c1f4108139118440020b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 669710566 1250 669709316 669709333
    0x1109061b0f0a1704081c260712180209041703090a02010e010305070e06030604060519051203031009052e050103050702030f09040e07050a090f1802030c0409020111070e010305 77
    0x2903802c1e5802c07a00103c0c000c00c06c2c2c0086003120f480030604c0b00d10000070002d0a6184030b0056103c504500640f402c01500342401c0e05d03001c1d0000300182110304a14410505040000121080b1000d42202090301201c0303400650722940380c401c011285400c6960081c1e4400b00402c00300000120b801c0c0010790007070301c2e80d0103ca015440114111102211900041540070410343e10354185480915406000540300060280c0c40e00c0005a885002841030f01610340105802e00480c03d00041c240340000c240002182542003c500000320180c00340180b84800da5500c0000d4203449101961400c8030280000c0181c1c1c4c83341c0c420300510381c940d6600540303001c00e0620001c1605103200100b207170300304500780d40d40780d040c040c5810801000c3c19003114401c041e4401c0007401f040f5940c4080c6000c005007400c3c1000078541d5000c01054080e940b18000c903241341e01590b030006016031008148a4640f00040b100015000181d10050b540c0c100c1d04518654140300e01e800102c1c0001c0f03041e41207410781b8000d804071100384c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 669711816 1250 669710566 669710603
    0x405090115030516171902070c05030f010621030c0204090b06090601050315093411010c0c150603080c0d090f1d07022b080702011109061b0f0a 63
    0x10b4510b60388400011845000910b40440081c800c07904141801ca0030201d1b105820b58400a903008036000b51442011000100203a280401c40e00101603560b80003404080d160980b0550a54201c000c00c40c900894050f02c10304140c071030404c040110303900500402030004207080803000424107c503100d000d503045c8404030380c440d0301031011341e4800c0e0160441490419030078800d00851440c0641601114100c1d81d110354984000c0c10388804140702c40306c05501044070005802054a00c05503108805a45132803c00044261b00070f180300d00c0284c2208080c0e41c030440184241d402841c5940c806080102c02003011142858040f82551a54441c0e50b2030380c0d452070b29511010048001d601c9009000e500100040d000807005c10044e03980078016005460060802000c0a9800100b950701000c00190710701d82d10850320f401042d2a9040019803008000017081800c1008541c0311b012086031081303c01041c03c282e8118400001c40e034100c4080c0c140c4100311007070b103003503681c41c00402400c0343d242081c0300090103007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 669713066 1250 669711816 669711841
    0x50f0a08120c1219030f09050c040c1103030129030403090e0403050702030109110f0301180201080606070b130b180a170705070e061c05030304060c170712061e03110604050901150305 80
    0x2025001409030424030350720010000105107034bc90300400d0014246203008540d0051015600804100a501c007020790415441c040a442c1c111820051350b00910a12000c82d9000d022003082c3d0b2401052030b0425121410240c540703009420000f5030560034901da41c0c040201e211010b50351400309072404144c84210008050a039002c90350600f19001c0e10045c0d5802562003010420342110000c1c103070f1403428229072260013000e207007115010010034031008288100010545d00e80da0065402440c80725401445030580d80f607401b0309030f000d0051001c0540850410321340804440354140c2c40b50450f0342e81c0360380303400c010074a980407607070180304003441d602d50031090240342d002c0d40580e40d05c03002031461555a5031b03c1c81d0051035101c0351f15080000200021710b032800b00700500d60064040303450752042c4107594000201030300c5254005448001e110010700c5440f00d545001001a250700054003d2440750b0580450301501641c4e206540c460b181c8000050221b5030b28a5070304030340304c00e030350280810f941d2100700c1e020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 669714316 1250 669713066 669713081
    0x61d01020c07080d0f0e0409020613080c0312070f0311010204090f05090d020a120809010b0607050105183903010525020703081b01060816050f0a08120c1219030f 71
    0x22840614410406c0d103040d9201421103440227001c1401d02c205d0954178100c2c24800e07008400c4907442001c0c42c580910b070410420800c0c040200803203207001115034610031382d00c100600040520213600e0a01490110070740648002d0511344204100700300840340c2c00c1000e0a4242c850800d103010fa40329284425101098940541e60072100c00c2401200c2008112402d400040c0381c136000f5503803198800400e1baa103000500b503045c06140040740e5400c2480550b50384524003019a8425070001043d0f901419400c0d0102826816040524400d2160720125800b449060800c1ca03030b00d9460314082005100ca1844c042e00d10310911410071042e11085041a69904054000580340c0202400b4084440d02e40e0706c2c2174241d80107030f64004954941d4902d0954138144008050307103072080040790f0a0041c5d0510244401503200c040b1141c243c900e1404904607201c80312684040000c200c00100c403c035442c810488843c0d0803a141141d02e5039100c05110000307000e980c0c06400000282000111000c05d4428003a590 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 669715566 1250 669714316 669714347
    0x41a010905151b030910050d0b031b04020c011d160902041a16170d0c03140f061207030623070e06161401050906060d0f061d01020c07080d 61
    0x1460840030018030f55950100d61015007861000300f04c1d490198030f8181a920f43c0d807542c0d448403903d4120801f1600240c9465445950290340010b1445402c107502c5c200389602142d0581c0c005a650030781c18800c602410f1350900d0810204c0071711122140e080d00c001440c4d514002201d8001320000d03190b580501c00e0f48030f1407082810380b8a200445c0c0d041290020014081da1205000790b0060484642d10b41c22107110310904042c0f03c0d100858102d80480c49400b500c0100ca180c0d14041001149041c06c40382e50040103040c00030100310030f00000340151034541400b1401503890303085440c2640d503483c014002d0140c041c850150610340350035035203240000301481406441c0c10344501c05142d0221041c81410b41007402c0340010110701e803030540086400340405000000420001168600d4030403120f42c07418001410107400340c804c4a8a040120310706d06900940d480d480280460081624240d492103e4104011040309500c0011880000d00c40041d447c003c43d411081aa0303080c90004800380c4401c4612a4600e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 669716816 1250 669715566 669715609
    0x40f0e04020907020a261b010f1a031f090b0c03041203060305031b1903030902040b1c06020d110d02070605061c08091c032c0a06080403030b041a010905 67
    0x20000d481040d1b02000005070040140f41800c10703252101050700310484da403c0722030b59100c0116030f0100850040c800e94031100803c2000041c04d8101190380c802209105007980806402c0411070140d0a410404440390044c403c41224105110131031b145500c02d40d030890f0120ba6000701c007001207029001da102100e80200140d030400c6100310040c0101c10107619000524015103480980c500c1101089210290091b43e001800c1c0c04c1900c1840110703514000214494000d440900c119410003c10042a159020202588031b022420301c00024003110365000d40788004c0490310b685030380c0c80c2d81e01412189028881c14040ca48a03442070000d481900e015401e031421103040044003040100c001000194005030041c0c41c9040b481c1503080c8087c075010403c0f400140054001049032024054001c480075000707030081c5001c108440080c2c41c0d00c10500c42e01d0306020b1102d0002c0e0500d40290301c002e00314803000c1c0051140d10b0070032804944014161002d58003049141c880031825041c040d0014031700c0740408401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 669718066 1250 669716816 669716843
    0x306050a24032c060f06060a050c03091305040b0604090206030a02180612160801050d0b060d060501080f010e0f0c22020a0206010609060f081b040f0e04020907020a 72
    0xe2211140340051810306042c0c0702e248a2034640c000701d150041502640030120311900d10400f5140c00d00402400c0072011205003c1070203a00c0d03460404848440040b41001580c508011008906500130b0b202031660001d00544003a0001c1c0060700514400c1384613241c0c04200d591070000300f10841d01e106030701a4002d203091002030466009a4020202c00c10070200d940000d0a0010020b0400c0c1d100c5c58015185c4c03201c031414002c1207004052000021031103420120025814000440d0448060b81c5d0050181c1c1c10103c041225034442100d40c02c00b554000700c09020640c2c54025095031540221600c0b4507540c0782985108034410081003043c01001d1502c0074000032000c600801949188400010360504148510408030401a100401c200303000c50b00540410f6251030703009484900700d541320b502407210000d0313801003940e8401075090740020b840e04a003650301b4201400d504280266007121420042840c2c01060030780c0800500e074407480c801c440c0c0281a6413100c0d4203c0e01c070825000010107071a00c0002 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 669719316 1250 669718066 669718109
    0x1050906190b090a0e01060f030518250602190209090f0609071d0403080406150b040905040b060a151d09012606011a030408070b0403020303070306050a 67
    0x1105800a034014042562035090040440c038030710190380124180180050075410381e00700403208600621081450361025894184054a250840320900381010394801c00680701c000c80200c0c0f44111550b420480704c0c0c0c260480c224030280d222078440b4008056525600203003040c400108014011441e10654281b1480c50b4240001c07880082d0241d08280560590030b03030340441c1007020710300c180415801820007500e410f1034243d0008442040003401040f40c810013000c030360000c013a903411030ba11a0780002e151481151020995455402004940c00f0024000810b030480e600102c0c0140c2c080d00603052981c50345401c0140e600102c1c4a080c0034404c034608900a124050364034070f04080b583c6280c0f1143c0802c1680000d00e03002c0240c11840d00c18403c02000e8400098030714031900321400f040f0042000b54141240302c260b541c1c6070a000c0b524001700000103410443c0c0e5206950016511010900c0607042c68500607441c1e41048600c9000a803900d0300020703151a022840703404070b8004043c4070100c5508000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669720566 1250 669719316 669719329
    0x51c060501020717030f070b010f05030601061710270e0109030906050d020d020d0606030b040b06180d0204020a020606030d17070804031107030c2c070c0318090906230105 75
    0x2c00e4010580803c3c00101c4121b01180010400c8510034002202c0ca0340c1045140c00c2504030a4000a020f40d1214006102c3c0580180c911604000241c0d401c0c09c5540d210761043c01961025006105a011441904000080c1e03603824a0040350b44c08105200039081290040d08075906818043c000403c1c0840802c4240c1c080c030b0090010302c02c11800546000462017169007031780d00c500524241c441ea04d50041000541c1031043c0305080d80c00321010310241c8001000511203000d0700000002841b03003180d80b150341c0c1e03555008103010b01342e01504c20354031b034165100080d4031000e0072281c65000c0e000341d8510103a041c1c4116000d11201068195411440d02d5004c400c5402c07aa000b0700441c14040c0702b001d90301d4034107400c10203c0019886041b02213852820140040e40150b44a4070b50794104488205803418003440c0710b2655484001458182500f0781c031400d04030b40c80b5001407807841c08100340e09808601040190801d00f1214020300082c01a90000703644a090000d61420008800c680c5c0e00040c440c0c0d14001c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669721816 1250 669720566 669720599
    0x60a09052e141c08090402040e0c0c0f0d08040803060f04020c0a120e0306010b0706090f05070e100b03060909010e070602060402040e030418151203051c0605010207 72
    0x10481c1c9045204028203001011104401100399842501c400300164041c4815030340d810003007038920030485410240d4481ea848100301c40140b6803580070980545a0711150f050f44d006000803040d00441c0e0412040c00f0640d40d01c80c49809800d400f503042c020ba41000005014000040c0550f10700c00303e50380d2525440071076003000e4501030b0310845954030181580d07030301d0000d0b0840c0340030080a0403100e400307171820b0551085c801000c101485408443e0b8100b6580200c0c0080c1100d0079411007545c0d80d5190b24003040203003800710004100c001c00302801c1c0144440060760380159035102180c80802d440e020501c00180e00207104c1c1d1200c0003020000a145420400c81c02c1c1d0b084084d44001090b2410123411003802d000e40350b00080c0060340603504000c294905400341d01c0340c090782c80c0b01035842c080c01c1c041104038401107012002c01d800d484400d0000700f8108040580001d0821100220110255190090140d4840902580e0908103c115607107100080d02c03400080321016001400e40c940340411501391800315 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669723066 1250 669721816 669721831
    0x306060512060a0b04180c1805130216080a0e090c300c12060f03070509040f08030a0b03060618071202041d0402011701030804061d0a0308030a0b09060a0905 69
    0x40c80400100420701354040e1016100d40d00c803041d85c181d84001400c044800b500c11013400c01c600c4a9044007801d100504500641e80c040e18060106014070f451030020384141c40f8400c400740001c0c0300341c44c10f21401c0809010810fa0787e0b42d5845c22032466074200091b2a5080d03800c41004c080420001c2990140c8220a42095900451407400b00194014081500e08100c0e20041c10080c0001c040018449c0028940d42c416800c0300c404440c043c92002003907490406016150195100c600420309118100002107084c5a00c210724660300d243ca10800070150400c0c013155400307407147c5404035a1503d03022514503004015814402e0346980d40d02c900b1030740b65503241100c6680b00d80c00c00004c691440b00058011182c80703880f14031034840c00c0070308c001465101c10b150013207040031000300144002001d14040700d00b11139480c50050b50f40d4651110720307080c0c0c06241e060b1a500c8180c6200010030400d00c00013031482a04120030401c1080c0c512424403213641d104965003a0710241060003030240d010302e135000035000b045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669724316 1250 669723066 669723079
    0x20703110115060201110f0d0e0313060e01140909060105091314041205040b090415081005040b06030a0816030e030f0f2a0d0204020d020a11060601030606051206 71
    0x101140003400c40380302d0110318848600704078082c881c1039024043d180e00311a14818440c500140c126000000e401358803240300c1001d0301e500b40040214800c00036188801c0d040380d000c102c040d0340c640c2c2c080d00e6196808002c0d80800c0400d162035002d00d514401b83c4280c503030040d0913a07019544090044440c0e5215090700c0e07512020507403c91454055602c690842080011018040b9040c64200f030380a8005483c860f00401c0410030040c000c0c0194036064a50580d070550b00442e8000000e60000d0003080281c1014820b4420781d0600030150289401150069018860111103600c0710400c1c15140ea00c291405004c5031410051642c1140e003100031400074502a24010405503030120001382072600300d105014450307005488209080c1410300038003a000141c6041281d10400c507018203100e00b601d070015244520130603004041036448c0d5404564120f584003400f1950303010100c4000d088084c6030700000e25103109010000d06154024400c000c20f4440325200c0714100700500381402140400240129007040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669725566 1250 669724316 669724337
    0x305010b010c0302102408014508040b0a1206050a0605040e0a09140d08070c031d0111071e09060503030405130b18061305010e0c0d0b030304060e030f03040612020703 73
    0x2c21004c182005092440300205401c0da0500c0074014004880030b481702c3c078410f11807002740c9101001d10351034154001e58018140304441410508482c2c0200c4c0c2c44003c82041c002008040c60b54485c1c041481440e09120070005103481f41c1c14070070301c45e919005010104000308000c1c4600c80d40c040c3c81550140810b0300200d00450039540d41881c00c2c03150040c03017a1940c42a01451070302d94011202c1e0358001da8078a0b000d1703061603d0740c03001040354640000c0c030528a2410f04181c8016403040c5600c1000c14000300484060660380d4139031918921078940000312011a1182c00318808406000b03070b10450b00d00600460816040504202c038003405001103403100380c0c0e11090b02c2402e803644084036400c1d00d41a10607580a25045080c000f403810000d142d01c000c9850a00107001e448412550660400341880c0f405803142c8001c2e8030b0900811000042d00e9041c4400700d40080c045030300c250b01d020000f01c181c0503680781140c000f905a9807030007035004440108030200307a8102500d200764040e0088034060310f0800c200c3c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669726816 1250 669725566 669725621
    0xc09180f030f0a0927090305070f0302070501020d0311090405180106120c1202030d1d0405130c0605040e060d1707060b1c020117180f070305010b010c030210 69
    0x107620003a802240b0200118400100540000710180204001c0080c076a2030040e20300c000035442074500c0348541e11540e5204002c1454400d50655460300d51240800c1c0c84450302c1c0c00c0113542d03407031240306031070040c0300d0030355400b00c1284240616480c1600780c2c03a0310b40c02c14210f2420080503000040419540d40310800041da140602401100010018803001400700752840c00d128014210342e13007041c84200d94084090740117803800030301380c18599954603040c1c031120f0150388450f40c26030141b4201c41c0d1190078802070000100a003100300c035145114405402ca00d0b95107410548481c01288100d0300c2e50340b00b000000b000c0c0d040602c90040c01c903118040c04180548003a4903c07400d604920341c1610740527039030510700d5964207190152609503041005007500c0d400e01c0d540000d24101c01c0e85008030300c403000100030030000555403425070101040c3c07800f503c8190f800003101c0e075a16605403000380c841c0c0d802d2103004980c650140b0407a4658a40550150036110325441c2400050100ea402290720f51407040d6005560 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669728066 1250 669726816 669726823
    0x2060405280e0a0507320405040c080109180c4b06030209030c0105070606051206070806150706020a02070b04080102040611032a0703050a060207030305090c09180f 72
    0x80c0c50ba6961001d424180900510220741c0b00415000c00d008030049034201c4200704402010504040c3d9415090090385000f850701b1900a50348020741040c1051090408150080301c464140d5100b0403040000d044a0380445480200302d01001c2c10a4003420000d02401d090b80c06018090800c41d405588800248a450a20344e01081c1104154100c1c4001d4803514841c031210541c0200010701c0d0544c180038014000a895019407840d05042c0100003842408100c05134000d41c0040000401c0d590020300b11101c030580328a07040701c0100c009180840050b50034030b00780234113407203000c0080c00d01810f00c036160390340b00025804414520f00f50720511308001b84e000460001480601120800542c54515080b03003d03001c442050b510241c503410901c066030b1380000005104000d001030700e40e40301e0b07088044041141009100d0b0000380c07041c01103407080800d0000300c1e002407a609100796030800c2a40d0354440e85c030340c50321035500c40c840d4000d1401020460004240321115004c2ea108000e0b180c4110300406c03031918 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669729316 1250 669728066 669728069
    0x9070c08040f05011e09120201090302031209011e050f0702030a061a040e01110d021e0a080f090105040201020d0e010e061309051303142b140109090206040528 70
    0x10440c222640a100c0c0b942d11682150740000845c41401ca814482c1c3c101030f004c49400d028a95044480764034900540e84600780410083d9009001e030341403899a15002185075020360041e174003107480800341610760a40e07040c01fa03074003031800c1d0340d81400c04c0384507036003000365a022040170f0340d04d80b00704092100414803500c1031041c050030035001a4020444801480191070405000403496454404c01002c0951580220f511000760b0b0b00380169211484010000c0035909501c8442e42e41d05c011a1440c0015001180d00d805030140e1409940d1656031030000e2070907514200c800074010b8002c1040500c0d41802045041d01120741410100c0d441196580403c0540c0c114120001c907003080160200841c406901c20560081c00240e00e070440d80c030803074401408100b224031044500c0c10b00028003100115011624038545040100c1c800c002071802c0f02e0340d0380a050100c80d104c125070710300d4000150703410041c42403110f6613502521842c24586414100301c2447c0302c040e6942c1d9002901c9558411070b403010a0b0450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669730566 1250 669729316 669729329
    0xb0309011e0216081b03030a020405041a061804060b28020d0c080c070b0d0f0507030213030204050a0f0507080a05060a03030c14100e030a0311040e040209070c0804 72
    0x1681515000c41c8401ca08404000412054410000d0303502401c1da02502041d1150090f4600f0340e05c0b559140003050540c1841104001d81c0000310034013000340c086030014801c035041143d060001d0300311000380720071400f142444075078011030810103c211f60403103030600e6118440c010000144150b54402002c45c2d0b610140320703910042414882030204040e1340040744951034040c402880d110820101c081e01c200b5014001800043c004191700c00303c01c40c20004a4094500d6000c425201c03c001c4100c0000750401e94141d0030780500300800105464868429624a490038180901c250380c82d640900005040240024091540783d10000000d100b481c02181c2c0208003e0351400c1062500180c0b600840f4400380085104101b040410404240c1c44185d0000301134001a100300c00e03181f8516500d251130011a001d81c0c4042c2000c0c2c10b01d03100c14001c009400c9005250700d051006142000d41d00c02c1500c100e000e40d00b220555a00840c000d4200a4603d691025150404000141d0785441d8049103400552103039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669731816 1250 669730566 669730571
    0x161803051014011a120405010f140402030105070216090c050c0712020a2304022a070602070b03090a031b0606080a140c0d020f01120501180506030708030a0c08040b030901 75
    0xb22041500056032401000740e5a01c64428018142007407980784501c1aa03049900189404a41840350a500c031802c0340b014294208440300c00040000340c800e5003110264844d500c0d0800065013503002064a0700502240c940030543c2078182400103009040505420042000038082440c0503001000b440c07000d8140700d00240c2090034548104105003645800c114100d00042114021600861280300c0304004119400742e2115604c1d031115514155089806c00c0c00614801c1c248038561003c03503103c00743c1d88603a080d2081952200e07400055484203541d4605181e00042080c00468880c4081d100c9903c40e500c00c40c0301c249000c0d00e901c001d94103550880c1d9020740010303024034200400c00c001c90323001c07110010240c440304140600140c200c070342005001c0d00840403461822026803045102d000920342d403100400c05541c48485240c0e07145043e418044840b4900030200e8010f180005032130044504000003180390904080c800c8501c180d980308203d400903800c0c04040781d840390310340186220f02d1640000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669733066 1250 669731816 669731831
    0x311030f010f0b041202040b04020705031803010501172d120a020c09010324020f160c0803040503060c090a150503040b06040b06070609050f010e1b0103051618030510 73
    0x301d140b100201d51148078400d00030001007150000b1500101d10079038046a0004448040c90301040180c850360400920b40c0c0800a02c144055080140e21484080f064008021982e2540300356100403003029071004071640070742501d5002440144180088069860302e0425000c50010380910b8a144203441c01e0360900702013102c1c1107031503040007000351801045601080715450b6449400448070a6840c5541a0311a1107003ea06800c454040f200040082c4401554801c2643c41c60450540035031400c075140d0348854400900e10340000251010348070010041d1985844040407444a07074041200b403504060f5000340010b0354800050300c2d8901d151a07484031641c84c50540303010310351201c00426051044d441e000d940319458035107005650341d456201000064450360b41c1001440c0c9000315824032280d608224031404c80c8800490003986004a15005049010028006500b0750b6002c40321a242120848031f054181c5108980141c0c20740055607161400c01d072647c560608082d08031803000455502c03200c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669734316 1250 669733066 669733079
    0x90f0b07020d030f060b090409050a120c06050901050103110105220b040e070305090304060e0105040b0316120c08040b071704080a0905120d0c1e0302010906390311030f01 75
    0x4c0d0020b00807841c10801c03ca41c01c1c10050000c13401110141405255101885002c00000300b000c442c0e815041440302c0126030703076158014104001240c0456146e8188004982c00300d20500900707040c1daa1004288610010400c011103a541024000d00110b4012501e02e0341001400b142100207445680c0d0340e0f03035070b4a08083d0180d80425024064408161a2004011600d00e0100a80e4103036245850254042040b002c0101c0303c50142c1d4000e021885400014001c132042c04001c1d00802c0b507425201d40751000e80c0030414904a50304141040b0109114000003000a084580400e510070141d040c000780244a0789002215168100c0b011075425000003002410743e40c00007a000020901202e501d8a0408103203880358889120803200001d1050006010041094155034481040e00d106460103074030781c690400a010b002c030341105072152131074072603848241b0420704001502e21802450f000418158810034581000480c0241d80c100356503440c200c001040c46a00450181d0081a05803406504050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669735566 1250 669734316 669734321
    0xb0c0f040909021e030628050c0d06060f0915260603061810151215140105030309100201020d021318020c150a0204050a030f0c0f18090f0b07020d03 65
    0x1801807410080081980c2413580d000200668040c80100704a100000c1034040d0786180f5031500040314865040500300480c4580110103005001103804041c8100741d81c42e84141c4024080c00c10900000e01c40300b0b01840ba000e0384400c0113030001c82034a080744200c024183c00703a42441b0595001c0e120035201c40d0901000d440c0030881c15070045079410760050300c1c000c07021025580b10612220301604a0311222210341c01c40c2e100d0b0703240000f0003d108200b42c50138018135085001d000010414046180703040031001e507031411314031224166440500114641017980301082142c003000a40c100440d03408000410130038202d070000c0d00448500814903202c6074180b0380c90300300048881c0d1654204a10522088a94690008200d1a0781c1205004c21145480d90a114400307031189811098102e00304000000c1006400000341c081c0780d000301e90444086459a100e10700c5183c552041103001001802030420515240d0300c0b03042039030b104082c90829850a41c2e252040c40200f1510300300581c10207508210401e4050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669736816 1250 669735566 669735589
    0x90b071b0803032404111c051510180b0d020a2d260f07030515030714130f090308071806050f3901050609040b0c0f04090902 55
    0x14000d50300f18506092030414460300070b1800e00343c0c090080640410b0380c56540c400031102c5811520b16035101041c9442ca810768411040c400340a0345080300040d041c1c02c0811000c2c5180390001c0110724403800981c802c41d550800b0013140307094064800c00008080c1a0240204110280c540b400b58850300708031004ce000b01040702d8204400300390455900c602d0900036145038025500c5040805030300401e140012b6800311101000c172070803134000d03050211540074825007902c02e07160f603507003400241d07900c6180c10003030340c40244107a8169101d80c1341405140075000c0010109070020f08002091f03a000c50801064a21a00801c91b9030341d61040080c003816404410183c2c00358590034400d0203e12958007079105d150b19842404204003000c190369011482550465444000c00c03c007891105490200340c4640b01608040041220025407000c44480010302607144501d6000f0440642940e0380c0d03c502004007002410440905410020f1056400000c0060710240a681c080040d40c02d002c0e105212103401075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669738066 1250 669736816 669736829
    0x70f0902070b06061c110712020d0207030605090c03100504020f010503040b040303050c19110f0d080a0209060c030d06061202160f111809060106080c0403060c090b071b 74
    0x10007804010400d90120990416426500301d99206001803020030090003d14020800508080c4803032004d41b4540003610340c050044042c103500c07a02d9080c050b41d0781d00540003030f4805600024810000704055501a544c465004419250780a1910700000e007401100303203250070610307a036000f40400d500b0020b2500080400030709129180d800c2540b184490401d009100400305502d520014112550801c10340707100030640b0252407086c91706801c0c081c01c02215600e40100c58407070358503614070840b400504840207101540fa540c3c0113880d418882c9010758803100708a134010204200f00003654000300000c2100e0a0720b1200000d01a0400e040202000c4a00e1205102ca0740107001c443c0740c1d800c601e021b00659030351000300c1c0c0f203140700741d850300d1898540e000004c0c41d0301c101408403c1d0b1180780d188401a1094201000f0303680307681e0f03c0c1e400540d011103060301c0c001013101d03060109000050302d80d170103401e4411040c2404040a5510120b001580d40005c10413116400700e05101109640010460005080c1c0f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669739316 1250 669738066 669738071
    0x1214060f0705040e060102070b120411040b060a081305030301170601121a0718080d080604180f14120c0d090305191712070207080606010527040e070f09 67
    0x749000300412500640c0200b071107642088011a080f0b80c02040300308010074050386440d4650006e0500c1e0390308000101c030280d49507810510746101e00d142601c101642150002d1800d400d100c1100401c554011000300404092024be1000a0200d030080000c0e500034550103c188005010400c512801c00b40e06a0040c01d807007152030b40040000c0e07400c101000c82d0400e6040210703125038500c04121011140c2540c081c411030340b41d84003c0360001010420305021107503900e885c80a911010f0030700048070950100091058114a12000094241322440300c00034007541140c804c40e09120382290901e68040e46010741e50500248a1000010502100204644a00b018601e0030300d16215075468040041c0c40d001010280c07101e400800c030188446d0020007046070140e85e1520030200034000001025910383c0050700c907000340059a0800011020702c42c21042c1c0d50303541080c0103d0a50b0503050214141020680d02004c6208880d85491084180d8138440d0401000f041d440e08180c03802051041c1c1148440e00d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669740566 1250 669739316 669739321
    0x23130b19061e0e2e090810020304080706020a0206220b0115050408030d020409060506130b13080610030b1509130602041a09030613050c0f0a1214060f 66
    0x640040080380050604100000488800e8404841003043d416a482d03120304030032440440300310000908014901124500c200480550805507502d511074401d01b000340d8002e010440d00d94040d500030b5500f180c4143c40b02418a0302590f14041aa007000d6010740041e80030303a04010b0021036050240c4488038868070640d003515031640300c06101d8001401380880c01745404a0400b14070344124110b4004100c99007d80b500d07043c40303a040f8000b0b940248a240d10396800c0c40800704140c9040700403030f0348080070401500d0031103240c485c1144040e0000968140c04640c0c2c2d070710018901c007007408098420510240382015041c00c61400302e59008018101050001d0354000c800959195001e1340c90f0000744d4003101c6c51003160340746080301c046d00c00e50b080140d25500816081100b034400201070401c00310101c9c2520780d00d0703407042c800a0700c01c070124801914590141c20480350754242104180d5440e00060712128401c0c0e01d9441071040e86444e01d400700d500c03000f030804460700c103042807002d942c11081d84d07002d03101c160 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669741816 1250 669740566 669740579
    0x8030a0b0f010507030e010912050c0906060a0c17070206031614040620121c0c140d05130b1303120b01080c0c0f07030f0b0f06060423130b19 62
    0x44c0114031004041c03204012156409a000d0088040106a40402034100c00240c0c90000d444600c40764000740901030000101c1c804c0c0c0383c50b00540e052403c461350751400343c507840d489400d0080780002404030b02000c100000409a02c860005502c03a1548140300100f4164441d001021481740000f10501d859040c40103200156010001c3e80c500d40503454429403103407000ca41d090810f60700360011030f110403000500c43c00c030001203000441c1d000043c0307008109031601901c054540015236004010006003c1248848400c4d65a010603000b0513400041c031400546a80c440305003510645a100100e052a9102c0d0205940001d00d41101c4030700e00810302102070603d00103080c80d44054625805401d0105a00308160300410009402200780740c112070b442e640c0c0313041c11034003105002c0c4d069850b1848040010607005032040c3d02ca000300c00c0640020301c2c10340382aa662031003108141c2c081542144c0e50100c980507a541e048207440d41c0f8001c810000b000d038146000c003e803140200c0c1e1050400041d02d0070400c41c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669743066 1250 669741816 669741827
    0xd02190c052e0b210c0109090c0504061b050a0308190e06070c08070b042303030f070e04060308041403070602121207090302060a0207061803051f020403080708030a0b0f01 75
    0x12050180780440d0140690703001900000c807100d400e000755030000080c0314410400060402d170008003030303c610005540b51301c4680c068402c2102c000b0f0115030304003c1001140d1040c0111509070f5940c0715800c000380000d07503c0c1030916a02d44410760000b900703101408940c55030364002c1c1c02e842860720790030011030070242001915100020556000d2080303142c002c3c401d105d200d1040b600041d80c44070345d14082e0b280601d42074921155006034200341607400ca138141601c0e070b0004101c0f80500401d0f650340c8800d81c0d84010844008041e005c80c1500141c40707d4000002850102c068000740c545020400b03100c018031030a01d490b0021a51089003158001f42c0449085060b5074122500404403980d142629a1a04015141058540e1000f5002080041c22000a03039010820300143d031600c1d41d46044101a0615000503001640405440c0350045142d52280c090419115444840c4250001d8100341d0340e911040e07116000b4141c241d0b80d42c10b00004000d1000054402d0b40c400766400c84100120505843c0001d01c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669744316 1250 669743066 669743143
    0x201140a09081303030503010929190b1201050f060a080a02071e0503070507090606090905041b0b180406030c05040e0c03010f09021e150d02190c05 65
    0x85540c4110701828001d0036022105855100d0382c15080c06560b80c43c0c0101264024401c00140074078252441394202007450103a40304140c0c00c0b40d41008402d400c1d0030419504542c6000e039244103403600c0300040300481c08000c0d101da4a1401d40c0f160840d03160409201094031185481172146000b0403200d82f2075038000b00e440b500240800401070b00c0c0c066618200801020310b6030709090f01c0764184400300800c5000402400c00a2051007a41e504039560810340d03042d981107005180204011204c1030003049041da110343c1d4030038098500c1845440445213100b81424540c0c00110040e800040c11006144000d17035031030003c08068074200001891a203554074001024010740d0700c1603480309201084240d0030002c181c400240280200301d0003a440d110100181507400e4204d0281000c40c1c070043c41801000da011004507800341c1540925188500c00080b40e1f0722401100c400d01c1d900b07009051038040780b9210217040403580d80341c521114000b410201c0c9084030714000f00c3c0b01548250801100c014a0482d0601c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669745566 1250 669744316 669744331
    0x150e060f0a0603050601030804060e1203091012090b07110c10030f0b03010c0305090c090108060411180907030b011e09110f0f04050901062a02010e03240601020114 72
    0x491034850392880005019070354409801391140c1030006c400c1c044240000d0044460b00d441d8841c2542c001d1041c002000750b9601c039100c481d0000e05c0544020709004507000000007a0f0328183c031640c0a082d0b4103104407414188103a039031440d03460800007101d8002040c0c40c0400705640040c083e00840000013140b03440c82000440030151a1404031404509603040000260030090081c00b2000020314020f00a0004030303040b0781c6910444000c4407083c144a0798160603a807480d0080d200c81c0c2d9446e01c5411024114514050300540f0780180b400c0c1d4460b113045010300400021000c0d242c024914241040700540c1030f0048846254000003080d1840221140202110903500012038580f0b000041160345004d11a040301001d2400035a0240f01c141280c020030a45c0c4044a45a1159807201400c40d48408031050700036042c2198419401c00c1da83c3e00e9028041c461052400201006030400440e007030040c0203143d00400d1940c10f4a0540c4106003001c03c9901c203d007032000700003195801c024144203503800780024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669746816 1250 669745566 669745591
    0x50f06041e210e01030605010905092e08032101080a06050903190306083304020607020d14060c310906030302162c060f0913150e06 58
    0x5030400c8200c56025403103016800d4140480c2d0b0480030050254441c94800c940000c0c0303030584c040b40642c014500a0180c0c0c0001c0d1142030380c3c1d0b035100c1420060000e0900d0740803451744500c9403030f405e401d07101e004c10300a030400c11b010b0758490311812040c0d60220443c41c0081e034071505841c0103020708500007a00b0141d00ea007040c5d0110b2181c9035900b015056101d07004c018a03d2065860002031482c0d0150030040481e10306038210307504080074241602200802107401000d585c0f4050100c0d20202c1100c56450b00907000825503803501c801075002444900d0a080f04603181c0c49800881510361070140607003a404007892030414a0142100c840340030081c0c00041010454240d07900348044901c0382c42d01400941080401003040680324100a9a40c42410100d100c0d164402100880c105400300601c01304000e4040c81c2c0121405520b00500e82d040c801008642c0080c0c08030444602a071780e00140760700036064040c006980c3c20301401c159140b02816070101c0701142c200200b4603640500014284c0d030000d92804031303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669748066 1250 669746816 669746873
    0x106050d120905030717060a18020d060b1e210c01120e03030103081201170c0609010c15051012020a03060b0303072f011d1c0609080403050f0604 64
    0xb920440c055802298161050001c0403914004482108803111503800072104d003641d0300e4407800251380c04070740c1e102a0112501006801400c1c44840000c04c1481007074081018956600480c0c15042410450240180380115280060800100034514000d2014020341c102d03151200c200d9842505e00341d054104051803c3c540303560030b050303400b84a800c001d0000740e030794039650317800c02174002e03000800e800540c04010400040e5069800c00680740d10008600a49440c80c0540200000c64110717044030b034140001d10951100092000f07008a40b0103001d400002058201003d129981081c641c00016400007054800c8002d0382d59011f608084943c00903000c01c1c8034602c0760200c1e0450041200007000c0e4190781503000c0c1e013000e80f480d4500300c00d200d20120403226014200110758802412401c88507554401201d83c840341086d01e104940003d5500700c0c510b44c0751803035490710200c8800c0d00065429070b4002c50203004011041c130070101141e007200e0080ca0181002c0d03e80020000448401003200380c00c01d500d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669749316 1250 669748066 669748103
    0x3703060b0a02151306181a150915040221010b040614030a0908030c12060603131b051207080c01170a0c2105041502031b091c030504030605090106050d 66
    0x542e8001350b54843e8041c01003000342801c0504204a48030125420540202c9001e100c00c400c0849521034034200c480c3c2c850540a01d014040c8141010b0095117140000d080b5181068840f030000f00085400a42c1040c01030075908070028140b00306030010b40071010100420402036900401d03c40700074101d0750146980e903c6010101c4010300c22400020489103000c410400d0100b04e040c0540082060b4105144079a5100c00230443c3c0d51004640c541c200801280103540455070b0307065450414042d2196029203284c0360000550405106104080c150b40304e4001407007101d90900c411801c00c002801d0441c1c3c0d250f103000700307401e00c42d400410702201c00390740d0580c540509204284007413040c614852501c0d114036440300413a01600c0101c4090380d05104518030240303e6642c80c800c4038490786250441c0e0620b201041c000c0c0e0103a610070141e0b950300030111041c1d44640c00c1c4601a484c1018400e85842c2c1d516851807410750140c2c1c81c002c1406030309914000042103203499510112007140c0d0302400f2035050992205 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669750566 1250 669749316 669749341
    0x4060312030c020d0c140312040c23061b0a150204060306050a060507030f090308070803061206070801120312020c0f0607050703020d03020901034205030706053703060b0a0215 77
    0x2e610b1440382c40e101c4127000074461136840503002d88140301c01800c0d00f000c0c009401c83c081e10030820801d03000741041101e2460490380d0b0301554241300b000000e40304600d415846201c807451002c02c00c84521580010200074051301885948004d210546103200f110b8a0b288004e805c4c2c2c0119180901800355050001004900c181d00840196a00004113900e458145c108120700340c20455001c0c1c040c1400c0103680340303c0c00c0c001445500c10340541c6e642021903820000464000e20504500314203204141025101103011800540f21000d203101c0142503003012002800e00d086805845074040c010100114000b299020412004080302820050790340d424140040b0028600700400360420398201c0c075400d1203d0246042c0003440d034130700d40380c583c0c003140c222642c99191001c0307114031070745503004003401c028a078050070140408144804a40500c500c0c100d000e00b1000d524980c40060181c0046107018015805220b85406072151500e02c03420560b01140182d03480202e503130105117580049001500d407101d0741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669751816 1250 669750566 669750577
    0x10608040309090501080c10081003060c020a02060d0509071706160e180403020105060f0d1103012a180312080402131109180c04031401020904060312030c020d0c1403 73
    0x43c804028560f50780f81520344802d5030048080c45108105000303064039218140c2e1a010b25004401c40b0700c2d107403550341d40700d0040030550106000c0d401981e41441c05a0b803204007a282d05069176801080620f48101c0e5a07042c1802c03600681070103421081c3c00c0280c040c0000d5110351017080c1084105240003408000d4800d40030543c00300da40b11801001c05c40c0025550a041c1d80554440d8000b441300d038603110204140d000300d12000c2c0b6000400820214042000e9404401641101800009803ca0384005034540c0c503018200301c500e03e800380303e07401c0c44980e80220030742d1102132114001e80203c2c1c01c41c1d444280160008a00e841084142d00102d810343d6182030302c5c2041180300c0a000c11006603402191195600580800d0340700c0ca01c1008051988014803440340e108001640429140908540e50703c02c080f4012100d49038959800d100311901903c0e01d01ca03800186006035201c000b410980003005003a281c010341d0342004c54000c02d581020880e00040300f924456071043c10300c028112401001c52841c05074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669753066 1250 669751816 669751829
    0x20d050a050307170915061e1912050f0c040b0108010e07020715021609020403050606130b0603100e100303141b06101701050907030311010b0d060b0f0f0306010608040309 75
    0x4e140a00108000000301400388a8030041154040c0e55420108002eaa01901c1880d10600c0901d140c0441c0e0314096031440d401c0c9555070031003400103484041501c0c1c241481c0504036402d9104181c40c6900c040104018402e001c400c60b000d00803405040002420004103200c0c6506e0500c130a00030a0181d0b00034030aa00c003810105080c50351940465000941e2100407407200b02210244610100300c0e0440e9000726011b0383d411030000d00c0c1c191221b005005110450652141910b66501100341c2560741d1705005500800900c4c510040c2d9505045041524502c054054000c240441c2c404000181d04401220101c00c600312803561036040b6014040342c082100001184140594000c101504245030b05a81c180c9101c40002c40401d654040c0d42d43c03c85000f13441b10b160035804000200000380c403c3ca012400c203c002c0c400130a64486050110310201015501143c004d0b8541e644411035040080c1142400300e000c6030400080d0802c000800e8803040180141810002c0e00c0e0700043c00e15005078031401c0180340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669754316 1250 669753066 669753107
    0x10b0f0f03090c181005090c0a11071820070b01050603060607020d050114060114120a06080303090a02011d09040605060d050a03231c0e16060e030d020d050a050307 72
    0x8000c05001e40c15038040301e407a0702c01708402c075001c01c217401c0070700c5401d2140c00210082d5180190718a020f403554803640d41c901185104a00011404886034024440284040340001c240030160891001015840d6110305d84a420300b40220390205595101440c111a02950700d5039590300e494000c5007680c0700d00b0340080e402c050300c80021020040158030441c10114030132500300300c1d9201c0c0401140c98030704030304945810714028014481d5524101042642202103040700181d61a900c001d2242150411178200b60705401144070701080d540c0041142daa001c1d034080c80c07640358240c0d80c400904a041d0151010342250b54560014040c0c0c1c03101044420f540d9000401c42c2c2000002d4030f401805c007100d49000c40c1111404282c50414a034005013500e81189120f05040c261001441c0c0c840c00030080041035841c20310820741384c41302441101501d44090301055031180c01c682c0c140c0c02450305c2c054030156030308110750095030090ba0b4564007800b43c8590503a0307460038603529110503c003150003046219071690080c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669755566 1250 669754316 669754339
    0x6030a03140f0f0d0606020a0506510103023402090420061318091b050a05030303040f020108041103120316022e14010303090e010b0f0f03090c 63
    0x3c0c500c0c00500410030080d034043c0906600c41008984400080200a2203503100401203000c0030f50345265071000f000c200301d035041100303203416500a12402d120101100603411346140203400e44c148462054011081c20103502d003900320b8405549020070400c80300500100306582281c45503104aa8002240d0020142c11513400c1074102240410140301040140d141070209480720b5007441c400359200b5440119401581c0c6151809081c1800b01003a0208844c9548a03c2c080c0011240c2080c0c1c17a0042c1e407a241c0d000e0841c01d0038180491040d254100c10301c264400c1c000c00c000905c441c1180d5405031750a1802508640351031416609003051400c03150b6060041d821100d4503940f40c08091885201c40b40070007802914030703141c16a15110f2006440490744c1003228445400c00d088031810040680468001802810401c0c0885400f10b080c0c10440015010303c00801c41d13007031100139040c0035103130b00c1e008146031504002180700c071b511841d5034056507400c0103c0016040c28041c0302d40415203001401200400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669756816 1250 669755566 669755587
    0xa0203210603060f01030503090d02041506110d090e01090207031b060f060b03060108180c031506011e050315040209091509090d1b02150a0201020c060a0506030a03140f 74
    0x1200d003190040e009104060000c0c80e400049080c95040302c0c0c04c48003851400c202031081c46802c02d00e03079105a80181e142c038603c44206641000c0800109080e0b80c034112131a000805080c03e002c1914410410042000c030f041c000b0640c0340b084203045036550140103039500030354074080e81c072145c14100b20403482c4080b080d05818010180c00110800a207000100580740d2541500c02c400d0100f80d8007980000d00c00030005090218604420200243c00000c42d4546184a40001d00c0c102e000036241c06000f88000900c5000d580241c200c424101160a00200003007100c40020840d010040101202040844898006448550460b0303807881029100007c1840e0000200d9208900341c01300314041c8030a00300040a40201081c1003801d0380c40359980c80e00d00008030306081040c100008083e41e000d550f00ca080303901209810002c00c0062000d40015884000c01049c1c1e50404100a110078191400c100c00c024881d40c002c164001004e506081070040d01c41a4a00d011480c010007031502d0a034800000d07541c982 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669758066 1250 669756816 669756877
    0x201120e120f030a0513030c170d020a050712230f2505100209011d0a05040903020a05010506150a03200d090203070f06051615090609021918020a0203 66
    0x45070710704003e1001b512440c1940b515030005040207400165030800310000158940218415592000c1090b801c2c806984001403c81c0d0001c084078003c00c40001e21a030402a0b413031039113502001c05040c40713010300441214901181c81c540130580d9081f14001034000d6106c0d01034090350358602c00c40100800d0100000d400b01001c603500002942e01c0d2140c808891615800c9000719140450182d5074500c00641c00e0000110454480030107980c000c1034078801141a8543d8810b8281c420f00036402054441807134105a421560040c04e01c83c0a2600440e41c141e41c1007008003103819106492400051103040c08a541c0c80c0c280c0074101c1c40000c21000102e0382c000616941042c4034240c000c03000c4d502c40d01d640d240344400280043c402e02010410078000c20a081c240b003084410464000c41341341440d070064029400850711082c3c0300310340c040c1c0d8804040c015400e019100c4581610641503010440d42480c4103103040d003107074844485940c0d0700003400280b40b91090064511032003030f0700c801801e003034141c5147c101c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669759316 1250 669758066 669758071
    0x60106030903120c0905010c03030b06070302250b040506070203010f110d060807150309080705070e0a05090102030615300703050c19030207062909070c0201120e120f03 74
    0x12924000f4101d024568411840c10051540b500d0945918107401500d4203201107005506041c5e440f80240407503200d900041c00d0440c4694050609000b03003014105000f1100c0d0362108086210400520030302c0d902c1c80032941910350071103903e52680c203140f00003405070035144030b20580f25043c002c0107941d008202c8050140502d103154103010103a241e1418650710409445019820704e4031202c9a80e100e07000e81c0c01406481d01541c242c514020303268441c06d103454034503440300c0702c5510840108001c44841d0f20640f41c001c0842c0d0025855418000c002502199003082e10f00032a003800070b51650412246444030303203021000d14049a040340219040380310441c08641c4140420304000c00250035104070b004031984841100d601c0c1d0b4040c04800f0046000350403615080308c40c15902c0c280841c401850440d680c03c4640c030f0200d51501c043c0c0381401e01c030034030340c020340884240000c4440c0742c00140e070800c0c1000110708880c03400054038614034008510b4580b1100c00c400c1d5a0b0070004d000782071580d64400070342c13 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669760566 1250 669759316 669759323
    0x3070302060108010c0f0e06030705070b0f06100e101107091e0501090c09090f1e0b0301290904060906140708010609060503040308090703082b0207020a120807050601060309 76
    0xd41030428296a81e404040c01d000014080e0740e0301501600c8c004001d10741112103490900d0600d101540c2d00c1c0b54002c3e06556070680044003e0030031245180140002442038240e01e0480400c0d4220740c045400e072945005880140442c4000e40d002e0580100011801030012140622128103540007006850090041c1071410a0401c000070422000d540503508400320703140d071040b810324504244440100020400c0c0c4050707035220340646d034034112482c0900b02d41c00002e03030740020740f941d1040c100742c01c451008119030410280360038140d5008000c112552600d04090340d030507210b56100c0c90104000c14003039400610480c178108100c0c11486200308814072600d01c80c0c13228002c07642c0b1803000760b8140c080c0344100e80c00110104002000680b15144603604510028200d402c03298999503001c00e10f400c00d28280c0b04240950040880d0318071032001039141c400226408518092990700400c0303200c40240101e403052061002e05804000d070348401c8030956030b0400e0968000d96114000140a03045107081034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669761816 1250 669760566 669760571
    0xe18060106030b0414060a0b0309031921051006110304030c0b03040c2304091109070518040209030a0f021302182b11150f030106020f0d090302040f06080307030206010801 75
    0x85c3c00f54110031010714041c00b0000d0400040500d01001e0810a0b03000402200c224003003800781351204d21149418110601058590101c1d811940d0040c0c0b20103000340500c070349468104810b0101c2c00a559903407405644a900d4440107805030200694076600c9294001041802c044038000340003441f88005c1d5000700c0c4540c0030741c140107540781c003401d6070a42100d030314a850742c2040c2628103c502c0c0541c000d0044501c90b80c8501c90590f407010000d41c078000115800408201c0028803241040f0b0206411034810408590450500c0025000f003030359045503902c0140000d81d12101300c2d0955544625516010700110300c03d650f5214060440c210307410901010a018a49241082c001002c103214040700741e44100e03079051103800a0f0386a07030b03448c4c204201010b90004c01d42000b05030300d8520140141041c07002c0d60901030356540342c0b0300020315060084034002031980140307443e0359195070b202d080c0b0710880b07030110b8000c54070304400c115078001006541d0110341d0070322000485808064010517668100d41c14503008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669763066 1250 669761816 669761831
    0x70b096c040f080303070f1b15091e050a061d0a05030703030b0a0e0604051503120714030c06150a0b041206141608040515130c080a0c0e18060106030b04 67
    0x82135940c0c002039400c100441d01c10805c24412a108403a00c0360b1030b44100380069031500403078544e21194501030142c041d09613115400801401034421000c01c00000d00b11300c1c105800515102d00c0e40f1b0300c60701d14000386419119801036a10000f900c480b4649184d40000b5a42c030300009141c030503602da202c8134049011a0601d444c0c1282440d040c0703098401c80d40c0c0d2403001d10842e500c2e40108402840000d2020200c070404400840f0701d83c4041003400382100b805003416655000604280200c2c03412103d007606268400c009041a420000c952103412170381e001c0e42000c1010b18100001c07202c4801e60404c0407070b80e40205002464441d001d4442001c0e82c0100410003007895070f00c949248900048501007900001801800d402074890b007003150740309004900399005079a00c8a441548240265484840c8050159611042c81030340a01000140b1800e0018404801c2650b03403030094114610903c50f80c003030500c0024950700007107244015802800c03000d4501e03668440d6406002082c0703c40c469401641341100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669764316 1250 669763066 669763079
    0x1914071b030b160c0615030b010603020403020a0b0414010c11091e0a0504020f190302150c0706080403081518160207090b0312030c070b096c040f 64
    0x103c0710b003c0b581e503102040001516901c004e418895900c41d40c01c1c0d8000000008540c01080342806032800d5900581d0711403441c0100110300c4c5140e006440f007444100004c001c1741503030440745181c0102c2800d081c01d6107410340c02c22201c5617050616030358000921208104151401240080304510702000002854403500854401c60707800320f070000d4000341d00340d0031060b20389802d040010520108802052140f0788960105401064010002e00380203c0454002000c0d50144030074000f40105142a00b03580c0780544008182c083d000c1c00c09004020390f110101010340f079118155160800c400302c01403042c01d090700c1030300226412402040050041e034101156001503401000c004000c010700802c220310070546542034680c4050008614100104000400900404519071245580c030b0050078988452040c1030762401084031040c668440c500e120120058004101407101c460b03035841100c40d028080c001d0510b80e51800d1b00c0ca03490300214884a40c200740c0c601c8000c0c02910140175901c640301e950340704c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669765566 1250 669764316 669764341
    0x3090201270b030a1104030f060e030a0e090c0c0313030311070b1803010618020306010e01080c1b0313230a0303090b0903100606030506151914071b030b 67
    0x841e00c10003001c80740e008200ca0b0403100091038210340746050005042082d0210706010340e01a03441180c100420300c890f01c05114440c495804044107800145240400b030040080c1080d5421290324440c00c0e44801044880c440307101030325212218441126079640351401c1e800d4407099640300413800100002d4917490780030004a000c0c012a09030600031030500d82150400029440000505030b019946d4120010351850aa8015207031031800361740041c0d4a00f010800106441070000c004da0610401d0000d010341400418100c0d0320117401c0503030f00b0200264100c08241103120300440011090f00758040400d1100ca0b5100e400484c1d1901071116818180341d8040c0904004039120260100d05138000403c000c0c016100140240714006066600880b544180d007002c407412600001e000070b9441302088080e042281d1000441c8000107003150900c0003000c202035100600c620f154007042029200c003410f0036603a0003964200383e07101700c03905480070011071150461811480103544c8203e181d808161f0300304610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669766816 1250 669765566 669765617
    0xa090905101e0b0a06050a0e12150f0f060a0501051e04081b030105060603010302090403050408030307170604060803190905210d0f021e0f0d020610060806030c04180b01030303090201 80
    0x1034a80c181808847d4006036200d21811000e40d4108546502c0441000014405e03103007000c00da81c881160707506000040ca904014024001c001214200060100319a180d2004000b106c41c00d107411507440108a1000c417080742e0980f40780b9840da10102e0081002180441d0009400e00100e016180102c6400d0070036090301d03002d90b040c2e41c004d00c00300b0042c0b005d410703d80c20322644075000e820128038250380d505503a4990360088440c07a0004241d007007040d0f400c0710103925480d0070074011982800001e04000c1c06a40342d00c9941d0b4200541213030000412021340c018081e190007000020034602c80902c40d032150041d41c10f02100b04004034010780103214030550003001d00040001d80780c0d0041241d000c0107420f101c0700000c4805030109a2151403445081f010003001070310f4059490b40c1c06442d02d410102c0f42d5101407078554003ea02440040410031051740c03800556569404c508440103c1c44070107481c00c3c42c41c121000d9034098410440c0c03000200925826030482001c151003a80c030005101040c179145103680c20316 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669768066 1250 669766816 669766829
    0x9090114151c020a0512090304030b01060804020102060127111909080a02040f0902040504111203041a21010308031902090603191d07081b0a090905101e0b0a 69
    0x411000b104440701e140d01030075101d01075003042c6180100062800d18982401c442c404a2540001014010000c80354040d5004210b2070514440070b04095002039100c03101401048502c0e10311720800c3c80420b0801030480c00c6441810b004000500b1228100205540110350540000c0c481d81b403400d07440c500c2180002c00300c41124000d400c100d1166420400644034050b18a0072068484507a0000750f0b669110ba2030159204400f40505290100103103d0091001e40440c80913800030b200820902d100300524150ba08801e6442a41d21501007004555603100e64424121900240c8000300070819184d000354011a9030140001d401603c004848082e441501150303a00000709001159602c1041040112030305c07045013010030b00c032031300c0850342403004060784079104a84c0c4540c8007000340d0002400580641502c100b04240f207100c4c0d080100d80079400500c140310b0a20750f139210704811301000703100d819040e184904007440340c410303811001124140202080384d8a0b91629a2118040c030f8005140b4085520 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669769316 1250 669768066 669768097
    0xa050a030f0618230a0602030a020310050103050c0901030b0a0806040b0703110403120309060e01050c04050f1e0d080403062a090e060409020a0801060306090b131e080909011415 78
    0xc42c4003410040601648603c01203115229171a40040c42500146100c3c0c00e02510040c0c0324500400205071190306903024906048c41e00302070001ca0944c40c01190341942c000e0030049006c8125501144d0f2081955000580c240211014442040001400349018105c80c1d541030050510760001c00303002d48118030008110080c1c00c00f481e804680203804c01c0202d24010100081c6585554604d1401e40e42c0031961104100b00c000b409001e18035100451040c0802e003900c545104078844050f4030704a06c0f4002d0344a00c036180c0b884145080040318000c44020310b60000741482a46c185001c4c0341040d0301c01e00e104152040f482003a4900480c410701950f011a220048000d030951141e000340401801d2703014080c1d8003c071071601c0100b0a000240a96001141b0034100050b0490007410321094090004d00200c1c425038907140104080b945401c501c401c10a000c0306040c2d0b041b001c40c80c24100300c1c403a8080c220742220428000207550a040745403255628400d441e44025450306035010f103405e21410f80403082944 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669770566 1250 669769316 669769343
    0xf05060421020a0e060a060e100c020d0503180f03010c02060a0c0201060e101d101a04030506040b040c0b0405030a08212a09011d0a050a030f0618 64
    0x1407090102804000d51072001d00400c0d1034001c1214110b682d0050710440c80c2c02010f2005505044101c82c0c000c049034603010718200a0000001e00c00c0001202007000c03c24908480d10075503603005001084d4540c05001ca039035440c000802e00e10041e20b10b0340050f200380143c4d080555141018022003110740032a9000e082140c0c1c0d0250414010100c1210400c119907076801701050003240414032500076502c01c444440410b2501801200104001c00030700c07400360030703282444038100880d4008800d0321618299544121407060058040e0f00030303640050a503205001c180018401c3e40c0000d1030003240681b0a020320340c0d44071031011400f44500d100d80c0340c15a100c0c4409201054441018062801300c8040740c00404103210747c428540314080e10f480c0c0e410410320080c1c00f4401100302214450303280f00600c150901c030300100064071030141c0e40780001405c0046081d260042c0d07140c009880c0907048c0100b030600101d4990500c4041030440240c115421490680c00300614400c2000040c4001c0c1e000219007041d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669771816 1250 669770566 669770579
    0x90b0402071a10270e1203011413050f06030d0e01020c0f040905010509064c0f0626040809060c07150c060c0c08160809030f010203100f050604 63
    0x42d0003407401c401c1c440940408a000c1222a41403004007040a2840b0010100c07949000101c464901d5420707a16448030004024600c011400d07a81103a2840120750980d120440c0443c1e0038003100450b030340019213030800300451030304400b002c14011802541103034081c201d080740568032448040825405644151050740300307894844080400904080c00224030001e40f80d40d1682900c03020742d01c003407280e08400c0c1003004940f26078034010520705e082003401d40350710fa06201d94044414099160f0012243c00742540310080881d441c030b6001480c01412520203641c0e650001080c80701c10b403001d010b001d00c0000c0c1030302c0b012244003d018000d942140400d0703d0030f00072408100982d0300c12460203145029641c400180a443d1001c0115081e001da100d41900004600c1c0150465245400c6642030180304221703280428100d41c01c1e00c588840c4c02120000403482414481910302486952581c90301c01c4224180c0070b05019006035018a80f2800e1a1000035140c450302c103030741900c2c0d0064940001040c402003110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669773066 1250 669771816 669771863
    0xd0c0225180e0a05070303120504150f0221180106050312071b1503061d0403110f060414010e0619150308070b09070803070503161b0807090b040207 65
    0xc0010302400040001d0381020a07820503c04643c26240341e00703c9001007040c10341081d005200d0101c400d01c104a0ba14166403040a02020700203041c42d115594498624907014aa0440380f02c00180e40704035180d00600b08101c10360b05422540510481a8400003c004031030500405040d07440040160502450011041209412844c2c00b070b511001304100500e034202e00400507030041d2003400f20380c1041c0555003501500391a500d51003500d0306035229205043c0d1b100304900f02500a076140c91b010340b10585600b9411304c1d0082c0fa4101505d6401440b050108216100e203400d203c21101c40020f0041d405090032098460004450b2407401d895407498084403100c240c1e11024002101940c5c2c80f00240e02e075102c1943d6504000c0c021121944000188006007004012403002001c011000710328000869440c5510781c01200c0f00310102c03142c1c2e00007900c1040394541c0c80c80824801c81a021000a81d103181e066940c83c0940305004080b031811903d0419802c1a0089a0703000340c008520002815074000302485c0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669774316 1250 669773066 669773099
    0x712230105061c080d05040f140304050f0a060e0d031202040e04020307082d0307140a020405010e07051e3708011409070e030f03041d0402030703080a050c030d0c0225 73
    0x65142101c180c2300000707600074092403010350311040111740f228140424014039117156140c241c4505402d1a04024807680002d141154a809035a032500355603161405840200340e41c80407080da240082000b2801156102d081d40c41070380202c0444520541c2c0308400fa44800c04c60242020314610380b005103822580d40c80d041c01c10300d81814220792502c040b43e2240314040404800240464000c42c1d914405c0d468030380111070142c10649080d0403a4241404050501d209101400c40c04005038101d440074900001c4c1600d04698000d03440415042c1400140f4010716000c03072070110420111a0b000b07402610813000b0b503050f11100c49811003001c030220100607022000a0241e0200084440100e805407014010180ca030300c005401551a182000c2c600b116211256072024944c610340d03010000503980001d40c46081b6600100e4072961880420001c42d928070403001080160300c80040ca514801a00f540440c1043d01e0a50980391900a500024000204140002800b0420954091220111035404040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669775566 1250 669774316 669774323
    0x2407140f04080a0c05040f0e061315050c0304020108010b04060503151207090e0d020f03030403030b0315010f0e0601030903020a03270f170604050712230105061c080d0504 75
    0x2414250340c2c2994610f04030701c200e030854050f44c0c1440e0410a50405014600d400c042070f040c180459032080188580d030b140000d104180a181985001090000b601034011101c11440e85c180300d540b40011688030154070a907000c80c002982540002009004281079506944040e41d07441e255480d8000d019aa00880124082d400348440d5034004143e102040490003c2c40c2e14180450b49110203110f0a00f0600007400760380c203541000c036000200c1e0201000300c0b64030580c14140001c2c50000f0b0404039207083d102c0000d24550f09584c0c070001c2440c01d64861000111440744145140d503917a43e400450036a01407240003009684040300b0400004d00505401880482c907030400314038103210703040300c500a00c000d40c4165a146d00d88002840076000700745952403850b44081c0284403130f05040d0b850310350300d5600c1e102d11692646900f21000030000d5407024801686095900c0e040d01d003610700001e074002c08056a846110341d801841000e008c000c8003400a440c2a00128120309041c40d195a074000303408000c1048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669776816 1250 669775566 669775597
    0x6030604020409020a0f1214130516060e09010501030e0d120f020703110105010e0714030603031e09010207050a050a0b250503040602060a05060a14040e0d02240714 72
    0x11588003001e202410411174250345206504403100710103411052040c0d00094404d06112500018607040d10324141c01820702143c1e14400d25443c01e1580c00c01108107500c44048494a10002e64140d1111040c509442e04545484190340d86400540c22140c0345d440301d901c3c03070700240300406000c1e02490360502c2d9010417100200d01c500c02d0112040490340001011030204612108200c18180d09214240c05003051050703a04182c104903401410744805e80d44c20004c509000800109282c4090081e10702480c0e820b041c008240e0ba030300d8002d04064000711a07240c014803070448001502d10304101d25200b110800b5040060384c504210390799016a0000d10841000d0b0050064070f040c0c0100140511980b0b8098409141c40d142800c01c02400d01c400584840c0d861810482803240310340d524902c546c100e900c85a1000c4a5040540114010b415100889039240c000d65070390010301600460913468010018a4800360303078140b0480c4207007218003502c19a001440781c14402514103440001802403540c0303170482 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669778066 1250 669776816 669776819
    0x3040201090302090c0d0e0d050301030f03120906020918011a0c0a0503070f0312200307020a0212060114030a2a030b330d0b1506030405011a01080f06060306040204 72
    0xc44c1d13000805840002100c8000030302c0b0070200e8094814a02e034420b0420250090640c0c55400400030b020600000e05122180034545c0c0405000c1c02c0e04500aa0640718180300810303890801703030000c0d0449100680581203240d40c4420a11640410380e05a4032240c000304000c512030101080385400a03074807007103140305509614002c41d0f002c0020f0040c03580301d003140c50408142803070000c000c600c0c40040d182c2c0d0542407042c5110140341800500d00d03503108040c011a20f07139460010032460300d48850800b0390800755a100140d007018000c01c00c0f40c103072a0741d40b410030340c0756101c80e003410355454050001500a4102084504e20038407505030a103034481e008580b88150707a0b142c0c1c40e40f4842c0c510a54048a04100b040c100e80416200c900c54400b0300180880488501b0518002050f190b00c40600000c1040051800140d41406130f08013118880c07070054401602c0346087d140041c020420348001d40328000410210300746070741c425007603280300f1089103c0c410007a03100c000030700006d40c101401203079002c4d409010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669779316 1250 669778066 669778069
    0x301020c1c031401120f0c090f0b010e0612010902030901020403080c071505190e0114070602030402240703032c0a0b0604020f0f030402040b03030309162903040201090302 75
    0x121842a0406031845001200119006021140d42c1c041540030f80c0c4604004000e42002017000000042d0008001d00aa00217441c1280d010501e075000101c0c0580341200300ca00542840c0d0140c201003000780c9510701251804410807445014202d85200300c4543e840040c001d50f000d6402441e000500c0034000360406469590708203c7c7c1d04000744460050b03000c1002080f07c581010209014083e550a0040c070b0008503440003d040201c8400d40024000781945410499218000e42c4640b1008500318507160300141c41c0c500080d50003510141c0c850313491041810007044c000322844105e0700d80c5500c200e151910036941900075045e01400c00c141c8482e81d854407289294104a05400d0401030000b501e98004646004d804804024081a00031403043c0400e103900e000382400c40f1080b0203081151900d0303640740d10005010f0540c40030850707018000441405510980015600c181c00c1e05209146041511f50720030300b41100ca005054801c138020007810401c4a00c00301d0056401c14010314003024000e44a40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669780566 1250 669779316 669779323
    0x8071809080f030a060b1602010c050f03030112060506091611150a0504200a050f0f030d1e0c1203020f160309060314040b0114130f050106111501090203060301020c 72
    0x240c4102102d08004204100600c051045401070b0a0a00c00e050500c4001c22a0ba000da400d5428001d040c4540a402d20080c04410015541921503100441e5034030b603143e00c91070f11040141901195441c0c204008211145004030740b030351040d140010055103c0124200c00c5500941c216540340590241c8481c6a001850741c5440b984207048403600854542041c0c508070240c0180010b4900c01d0600030388600e410369441103030900c1100c034101d0381c455040a45000041d03103100344070481a494807a045080c400c0743c2e0000141000f40031511802d40803282e0b000c00035a0740c1188903800400080c080c640d003803c100c0c00395000d4070061005280c9981401d0009100c0344034442d442070b00b600404d0300c5410402c00c5036403500030a111820b000c00c140d0b102e800d160307031912060081806080600483c034440075055031264411051550b14101c4284007009140c40f00800600082c0a078100040e548080e29024410016100040041c0011f0301c444070b0f031a0810680003500f010301500c2c0e1554080101c1c1c04801ca041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669781816 1250 669780566 669780577
    0x905011b03051b0d0b0603041109060307180507030b0301023c0910050723120c150a061802041e080303010306020706060f0b03090d090807180908 64
    0x400001505044036a4180344800d004088442010304100800c083e00340d01410702d00c8040c5405039400c0d180c048429081000d0300405038416000f60000c02000180241c0ba85941403410050711084103d446800505840f104240168694030140000d10384160f1042c1d40180e6108089150000f594440341e0002030982c0e000103810300c0c3d100414605103402d0008031800c00c1840151107400382096030001150b110701e01600f04c03428482c41c40100150900c0340035a00f1103c28540c000010354000c41c0f98180d82c050782824008070290791044912041c42401800c1c02c42c1c106210407001030100041c00c6240c01320703d41004016032801c9460303c0002826a2500c090700344154071b10003000d6180c908103a500c0319002481d0b541d103030310520700910412228ac00442180c0c1582c1d0800c3d4007680c1c944050422401a0045078401003e500030910001001c2d400d0001941c040d080380b10541c0c0301d400500c4801c8401c80641c0c016480b00780c02c08001044201d51001701c1e001c016202010119901c00e09807100f510345c1c0c026 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669783066 1250 669781816 669781823
    0xc03200c060c0604032c0d0c03061b0909230915090106050f03011107020d0c1203030903020c12071503061508041a0c0702040209061308031c0912200109 67
    0x708042c40109504086d5440c1544604095803000250382100d400b80a160a01e4060040e5681c044080502801500f103070041c5421180921135402c0c01d042c08500940e000d1300742c2e000984164008101001d1900400d15159071300400b0240303c2940340a681e458240151030001035104040c207852140140400141c8140244000061403c0c41d00c002d01c0058201c0c5030009200e80d141102141d0201017440c140d80307000b40c047c0d0b21a1040c1c682460b00180c02500c1d504402e000c06818890382080640c190441c5000314440d500b601d400c9008a002e1054400031102244c040e60004441840040d10580c1c21942d4000e5a18000c503401e5543c550600d13107507110904a5001031411410041441458142040d03689284140c0007030616000c91035070300d42e0140790002031140c0d40000f998002e43c2e41e4441650308081400701d240d2011640c07401590fa1320b0780020001c075076011040503020f040040510a0003802074010f010243c01d031039003410864030f540031100600400803024602c0481d08100f4401c10004c01d12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669784172 1106 669783066 669783073
    0x30b0f060310020c0604020103110c0709020a021513211b031e0e01091a03060d0c1e0620100b0102010b04090f0c060c03200c060c 57
    0x4900c40c0c0002c1c5400407503041c004280102d006809a4800d8804004d08a00714001046a000700c8224120540080d01c080040002980090003010001e02c1500d100e000e000c3c11b40c804286058940e40d58003007006450340d0400251568640c0480800315145141100555005041036184800071072803444040f440c004040c0642c80d03400106811182021141044d044010030108501408a0014040010002c0c0c200c40d2170f08816044088038450707a00c1c50340c5a206225440841c0001228001600d80d400503840e8907c0c040b070803c1400040c840501245841c1c4010b00074101d60040c120358072089142260394070000038180300142c1c0e2210012403402158070050f4010000700c140b043d00309040c8402c5a04001000401c40f40c03042c42038108003052500c9000403200b000f50304100501084510100355010b00038240c1c2081d042c1c8009080315180d1850354081105904a207050341c00710760 = true := by decide +kernel

theorem cover : BRFrame.Cov 669604316 669784172 := by
  have h0 := BRFrame.cov_init 669604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669604316 ≤ n) (h2 : n < 669784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
