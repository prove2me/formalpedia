-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4631
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:14:10.695863+00:00
-- url     : https://prove2.me/submissions/edee1e87-90f1-45ab-9874-5bb51b0cfa69

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832733812 ≤ n < 832913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832735062 1250 832733812 832733851
    0x2130305010c180812091816080601080c0405040e0a0501020a0918090201170901060f03350910110a030e10030e03030604230a0204080d02010608070b130905 69
    0x40c40f26444180001e6075541c800c40a0120355400250b400081d80040d0f10203a440c004900042d0307203000c41103140884140100c04120002d00d02c60600e82c0000300f1900c441085884407001554466411280400460b10a220402c0640340c40d070425802448814180c801040c07030758944509a034059864400032440c1a41e0801031000e03c2c11841710042034401c0700300542d880320b5000804040705e6080c0444034960314004562422401e6110000410202d08e0844080f692072800b42000c6c000054411200c5481280160520003034010300c00100c02c8040c0316510300120303601001180f070340c1d81040004001d085204507074010b400f00005880940a915800001010502044044a2041c03c0c03101010701703207000c01c001240c0000c203803a0030602c1218041001400301c000a415460010910606047d01005202034094103600920030342c0c111005940030800491000d0b400e0302da4a21030004241e100c8001002003100010207480c40d01140c010010505584210340003d0714803d440c20f011400750780c610030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832736312 1250 832735062 832735067
    0xd030b121605010e0f030606090c161a0a0903140c580309140114040c05030705060415090b0408100b04091e020a080f101401080a06020c0102130305010c 67
    0x5184d0b90848450400d00d103001d0220740ca0310006003e060190a060000c1040030100e0300c2960403c00c00341e05102d0070141d0506003451aa0640c990708000c45d1001c1002c40c03105c0d170300750003130340005901034407505482006c0c40200407455000408080d45801610140800104404028096504401c1d000e044410355440000d0403660f0501181c10242000030a030074019481000750b85040d072460400103140c07926802c18001c8580e510320b00003190f500e441c0e00e00403500c4c2e503494984d0040d4010b05800b00c2042d02c820906980d1440c5003d2070f070f40904180403c00031800740d04060b03a404985441c04413005595844d0034003041c1c000360824108c40e00290340b8030002c96241c0c81a04100741d81110288800e0302103849222403409003c03041300100c848408080159180c0103020001030128408560184000c1c500d01d80d1901404214010454200205900c13080c5500326001d050343c103c58042c2c4004821603036500001c0d400f03400300b60144d5400f4010103a100c80c2041c2008002c50040d000446c03c8480d00000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832737562 1250 832736312 832736327
    0x131b03051005010302031015031103010b1201080c06090f060424030c0306050a05010309020a080709090c08030408031209150c03070e090c04060f12112a0d030b12160501 74
    0x710f0402d4814130070001e41403c2d01172940112407072804a411980c0031a0b00490140c4007400c00001c0c201000000098007409003001000c45007049808502640d0321811299111441d4020040e40004d0a1091b01040d250002c0103070f25241c00100f040e880c1c2656080040d000c0c280040300390303000b100740f43c09100c1426014086d034000d910182c40e04000320fa041500040c08086140101410141e442c0403036400c54554695100140c1400021240d03690394950300d041c06000310b502c0444840d20403110000301070400000b0744090f210080302560a02e04101c0240e0f81407440217101d80342d07a11502800d81103070038603082840c0c0240c044040d295901d1410060250000c4c3c2203408041c054064001040307040f00a41c0d00340c038140e9074285412032903118002812038101030703100f40b119522441e01e03940003100c0c90410000c100704138005076070850000c0e0070701150b5025458048036007070300c0c0c00403881c03032494a10075400645042002024040000800c400b940e00e00603101561510300c0b0031900b010b00440d03800065 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832738812 1250 832737562 832737569
    0x6040914061c0c1802130b030612071508090307080403030f080f090601030b0910180c060c031e0c0506090d0305010b1e090409081204111203030402131b030510 70
    0x10841c402942c1c942e15042944042c1c810044900ca0420b901c00e41c80d25250100c5940c00503092510042945a0114000d80d45c400d652041c815162007050f0402580081a0302c4121600300604003d8042119025155800e0080083e00907000401000300041d100802030000b40d802aa02c0c82d4402081d2a006000c0b800e014211802290840d0100720b01100c0001d02c1c581901c0d840f01000680c2d44420b1304541c507182c05040002d52407824101d0708480010340d100038a81e1140900c1840380321581d640b50030b1b52480c4040b035000e0009880c50110b04c240802c0c584080c0300c010031a1425800300345040e00c0341c80c2040c0d420703100d185075600310964550465915000741070160103e41c00191401c4114032203031014030003122400180700c2c0040b07038002c1c082e0303155801000a076070001d01003503030b41021008010003020100da0455401942c02020422801c00a241b200e12a0104d4000c510755250384d020000c0c01c8003d440c0c5034260079120314040c00340942220140d2200e14468901140600b041012203550b54500e41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832740062 1250 832738812 832738849
    0x714090a0204350d0e040c050903062a1c0b09090c0d021c05030c0f06041a2a071505040f030c080705070308031602070305100b0604091406 61
    0x4144004480b0f0310184403181110700c035071249141201418090400314110758040390043c070409014264000c2135901c1580c00c21a4100141c0d040d411043c0c6090180000407500f5502020000303901100c02801c5a5101c03003641020440d03e4200d100300741e1640d05c031031001001c0c0c180440d0040354034900c0d80100540250119450328881c944070700a070b591b40d2560300b1114400d40c0002210015519103001075074480c00c00c045484c000c1c00f141e05046039668001e580104003807040140081401501045140c060b550001814040414a110780f15007160b014051110380c0766880150b03004a0285c1d181001c45240741440c20341c8072003140c2812030b400004260101e1003e42403100300000030b03001c44c01e0100590f82c981000241c03040c460410604a000d400c500030584c1c4a40d010100070301c40024041c0d4400c042c00311064078002d00c0c0000890303c0d2203145c4001000b0b5403040300da080214a00741c2041c1800d41001d131407203050035034846410003900e04a211681c11f98121a050103078a040041980940d003e101 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832741312 1250 832740062 832740067
    0x1e09020f040b061e07020307060f1706010801050904110415140321210901061a09011e0c0203150403090605040f0612140708010e2d1302030714090a02 66
    0x2010440034072038010914110324100b1103001c15003407013409a40348650060126100d40f91203003000362074200ca508500740821030560304c800304016950170192203084182d541030301c00e9181006101d64904d003e441120ba03000791101000060b2982d1241c800d002107008188074019140407003c0c05000503101c800c50180e041803402001005850b0102c0e81103072078800d0620340c0e400000c1000310b00000d500340803040e03841051007440240c000540003401500d00c0300c850030740da0b4000880c825045104d03040e009404a003003d0544040000703a000c00b60b4036180141880410790625038006400d000d506800b8496a85001e0300780410300d6130100005000c1d00c85418041c0c601400d11241d10440c0000303101d0039040008804c82c81320100602e8021980164084021001da07080908028082a509018028088465000269143c01c0c10f24040203180f0701e0b518032604524801b8246203038000c004110440444050580000580703003006000002c0603407030b132041b001004501c02c1040c1c2c0400a40700124140c0103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832742562 1250 832741312 832741331
    0x1b060402090703140c09190b12060603010e04020409021909061a0901020a06050907031a040b0a05151905030f03030a0f0b090c0d060902030a02040617090a020105030a1e09020f04 78
    0x4d01c011504100d20324161a100e00034080010302c40c02201510301c00014041341c0c00607120004c071018000840400070b1001d021b40c0d078030080c040c490109104490107904000b01041c05424550320241d0b030680094140d1400342851350701001d038036249902482080c3d5842c8030400010b8280b2510310658000421110b1903c1302c4280000d54800c0d4440002d80b060740c2d00c8000c10341520040002200542e448200710104054046115801c040221020342e20544803600041c110507203807040c0c034400d5201107084a00c002c120303c03d0050046403d80022000e0309200804111a075080100e1601d4040c11030084d0755916002c01c10380240c0e9100c00340b549241d4188070554140750340d410b046036400185004945d446103448040340000c0c0c4180c0c0c0c843c803040c500c0002889940e820b16001003080e84c00c40d444240d1040c260800018120400b115907229580281042200540c880c0f0000c0d9040304c0c5c2c0e48400301c4c050766141d060114520050801845181d51102c4035421030402219400c0131480480d07042041880 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832743812 1250 832742562 832742591
    0xe13050c030703020622080a03030902030c0a0501083705090d0e2d040609020306011d1c0201110114221109061305131703040f0201050f1b060402090703 67
    0x11501b0014105240c40707040c40d550480381c0ca0040080011038111005402c45040160051003543c0d001e070300034010038a00c000c0d02d0034880c2c603c200301c4a0680d5901582c1c1e0701c0400031100300c4542e00d0414902d003096110035070350050090411105210792280029142040e4a0262420701881d44d884c045c46040c40401e40255200f4102d480755070219802009402040010089801c003100406984545840408148885039a015611845007a00c8611a521992284041d0400b2400402e68402040d00c05201e807100346480c61580300344181801d1341742400700d50045095503e46528540c01d008942c0c1044405041c5c442107604000030000c1441201c8100e440e8001c800e80c5c0020701c58020b0305030fa40801d88a482e2140c98082e071f40b40380d034000c00250a22038021004403003000400c2e10420b07081c10f4034110b000200d90440b0b0007654405010300003031106a005443c16044606081841e0340180064010100c6550035022085281005042da62800788100401e014000e0108410149440c9402d01100c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832745062 1250 832743812 832743817
    0x16050418031725030c02010c0509130b040908040b0d2313050709021804050c0408210714030a0f0504050d1401061a03100b09010c0201080a060e13050c0307030206 71
    0x400312545010140e4070000304401e0203c1103190000038070404000785221540c5540580036102e4035600a22003000080000c440303600070711110300c1c0d00510380b0f013449052000a500500c1104405040455105070f143c950310f08903002030340180c0b020b0800007503101c040006031052002100c00000403080d040a601e00005030320b000102124850119131b4035a13030902c80d0402c040030040ca141107040d551201081c089425500c0c400000b00e0246e070402010400c0c3c01c188605a5041e0b808203c01000d00c0e81a001c807175240ea000365034004d61044010131807000880c04c0b40c2903500042c9030f50320041d947c0b410841c00c020306191110500c0c01c100801448144956502d0300d03c41d840341c43d04401c00c00540383c0319040c524010a02d5138403185420120300c01d80d0304039540f110040d40c0706a50311070b10ba0211680c3d48a60f41028482e090f5070030300141c0c80d911700c1001503015442c40e6802007013900c03002603100c0d1650700c0707011000815200c02c0c006589120f2080c003000310412003c0c1e000ba0b0146c020301006031440d800f113225070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832746312 1250 832745062 832745087
    0x80901050408030f042f0405060909150709120f030215192a17090f1f093201090b011403030c0a0b040b010b0315130209031605041803 59
    0x90090801140a1003045100020307803881b088410b0400603003040e07030265004205100e090203141000b0004006140120b80944101c02020140100c42c62403c40c0050095000788504140400c0c0000070231000e40300b8400700e024610521a16501c65070505000c1e1524280c03c3c03825040690b404200000703aa0814100b8412060011b0302080c0070205a650f6259400525403400c0e00c2c21006c00900e09003a4407980110316009640c0707489e440380c1c8a04c804c464542c1285292688150f2240c5041e5150641c03041c0051a00c040b019000560003010356505085007510200070300028a41292410f00e000c00070b8119407a00a000008002d2201250380750806081d05200f040a86081c5c180b5042c0161014411500100c000b10142c800e000c20070301e05581c1d0740380d044e01d05490710a0040000700e0714540075000c1f04e01903140301c41708080340d401c41f034100421600a00100d240c880e4003804603007101d0314104180d20311032200385880075405040000b400115000681c000c06200340005400e8003003504a40050340d00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832747562 1250 832746312 832746331
    0xd020d02042c0c0f030f0705011d0402070c1a04050a0b0708040315090b061e090702011e021b0303010b0d0e01060e070c02010801061805130e0a030f08090105040803 72
    0x42c8071003000c841000c0303056000000e5400d141201101d5908011503003c40b441802c80e0504c1c81c8010507000d01d90794003001c00c0c3d80f030030a07070040c0403d2145600038080e881d01e00146c031004a100c0000b010109081c2c1c0c001c0c80c0b0855940c1554002030003460f00c2d001c500b0017103c2c151315400d03003040c0c544400155203000a00c40d2594070b040005200c81031110060498001d560080c00c0d40010003902d031221801000703104000d071002001c481c041000d501d8203101c1e41000007041480c520a4000c200100402120302030480810340d0f68614400000b8182c3c1e40280000c6e21115a00503110080103c034100100520f070340419854004000500410f48520240c1d40b4140b200b0b41e001442c0c10764644840e00510b0103070041038920082d03500700815941e00c403100400e101e03c00e0340c030840c031640d85040c15200b5002c070a0000e4900e940400060101d030900b0124102030102001d0041340c1c0d070541005c62402c100b4030034000d070b0005070564000c42856030006806600712100c3c030002c10040c0b50540380d110301c501000d000342c4003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832748812 1250 832747562 832747571
    0xf0c0507061a030717120c0708070905010b041701090210030903021002040e010b0a1211041404050c040b0c030d1b0906020c030c010e0420130e0c030a0e0a121701050d020d0204 77
    0xc05003030130003042c0c030b01101030342c0d491f681e42886c0300486a03241014801c60145209070343d00498601540d010315030403100c094000d141081d00381040041090344007030b440c00ca19985c900140e070140c0d0b28001c0180031036142c2c4c0c40020780c080c12400c2c0241801e060b500c2c05458035004000401c040001034540c14110b812860002d034680c6806082120042102140d0404550a140c010100007000d02d00420489452a44601500108030244030a4030b9048441100c40b203802e100400c060f1a0800003020304207502010740b454400c3e00001a030440398460b04000f034290005003006812508441190083d22180c002040e031a6441000641d0301c0c01c60000507410046c0500301d028480c1c40d250800c1c3c03a2441442c180701040d0703900c40046031841d007100700042c0300b60b04101ea00240b9440c04600c0310340034280c5404218a1a51964101c00150104c00106046e92041f48c440c080841c09054004924141c507036a080c4500f44c200800b664540d8068120324402c2c034400c444140140e4030100380100e515410f541c00304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832750062 1250 832748812 832748849
    0xd02010f0c0b010602010609050a09021003050c09040e0601030b070801140121050901050405010f091109041e0303051f0503100507200a15060509130203010f0c0507061a0307 76
    0x55201d080d2020041c100b01d00003001080a40e0190099402e485403c40c0c100400d5954954072001c0c0d0300b005102941089210258030381c11807080e04200d03031001e810888186815089404a4111019030203108820342003203005004008203200480d811516a241c071160315410060741c0050b000d607000140c2c0c1807003038041c40f118060380344884010030021200030402045c40d22816644c042c0c0400ca42c110380b15480c01c8803014500c0070340e11036100c14582142085003820054418461140b4014105a0b00d000c140e100302c283c12298504214812803007a503011449040c050182c0b04e5050250010a02c0405030f120203200c19180004d600a820700d409401241c00c1d25980c109880c0c0c01c284003c01c00d0490508494414030703000005214510300d1040c410700d10000c99901d0900300312a114040c0c0c660040c0c0b55404100380c441100c009203800381c001000040c4145481c0c9000c4120344840b4a4203000c1840410010240201c41c0324107144808a14031411130080c6110000340c41c1c65886c02003203030414035010000b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832751312 1250 832750062 832750067
    0xf1211030d090f020a0e07140a120e07030b04050703140c0906010c020d0203120901020f151902090a030c140108070806240714060a0209030309040f150b091e0d02010f 73
    0x60f8415401502c0c24550700d49480d203050703284c8400c45448011a441c0c0040c0a0075840e22000c0b150440c3c1d07181ea41c00f5001190210401c080c0002e90100c1c0b18070320070040f0101c00300f0b507106851070260340709800609000e031440c9041c44c100350107212103801c0f90700004007042403500c4600c1c0703140c2e0080c000d20b0000105101e52000596484500101a400d0302c203c04a00c082003015100400800c50309800704e80051240c100d04954840803890451084000c400102d01e00745070640c2d030304411300402c40ac05400d29000d0808074290008507481a640d585107000d041092882d01054451980020710b48419545400e410152844401a24060058245031444c5004240e83c04942441980d07147d56556a0a40341c24003005090700742401c904240241008240ca81c4a54405c40b0101035028003d9800c00e0409410403009191250340b40e044152500390120100a02c542508007402d056402c00317880e016405e041c4600284400b01d800c1e0000404c01e0840350030340e0349040c041c040a5092820703410044c440c0e0f108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832752562 1250 832751312 832751333
    0x90c09060305040f14010506150403050c0d020a0b12102c0a0608070b03160f091503060819030e030a1e080714060403030b0904020105031902160f1211030d09 69
    0x3809290402c0d1744c8008074501908030030b004010803520040d00d01141144403240348210301c00100280e004800744000c6003040c0c000f401445d0b0000f0801400c1541d07482104010b40e1110406c100c002c4500340411035640d070551001c2d800b805e115400d9910000b901d24001e43d902d10526414101c2c0401030000402081c1560426006085150203442d09580d849880c0740303043e04159000038100c90080001588240700b10150790000d0320554400351a14904442d000c04041c40c840140101030301d07401d0100e518041001000300d03a44801d0090f060b4281c00d07040080c09074962070007041c403a030003500a003004214058603050614040301c0d5480607000d918036040030f542c410340030000c0030500c0e240c0380011004800700380540b01d00c0c080d480a01c00d041c8200d00f0041141b0302100c00902055042c80854039180d55451165034900107850018501203000c37007800318181c60018200d9007141c0082c0340a080014400c1c0340b41e0104031505001c0d50150381c2c010111703200d010301030039120016514013400c4180031502c040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832753812 1250 832752562 832752593
    0x913120c05010f110d06050306090616031d160801061a1b0d0c0b090715081e180c0a0506120a020f12040506061203041406040b03070f0207090c0906030504 68
    0x281081250400421808243c105c901a11100380c030708240001c4505011032614030424a42d4050b007201e646454640001105807c0050105a5501510300d20103520400c0080d044d4412001000100c60f08200c0a95200042d0064403850f4100741e001c120802045161200b0b0310b00940141d610703451401210740c40071002410701035151082c0e582c9401850f0700b00c03031101750760b80c0141c3c40d0950555541e00c03101c2d81c5095502c12841c0c0030342901c00400344130344580790641e0020309030124295003000d00c80310040b00100c01d8a595242ca501c0d9048000c1c003040401072038000d0f11007a6130300d00700b1515010008000d03015100301032594040e4640042c408440c543d0403146c0710311048440d25150307021528080c0c2c4465040707504035003920507440442d040b40760444c0320512004d1380704025454603090004c4103c2c500001c4000907040300042c04040f0b5003081e03010145109480302e544e4848a02c018001c000d1038184907030301c5111007d09e000903002e481503002c4041c1c4151462818007240544807440c0c550300070b0001c0203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832755062 1250 832753812 832753841
    0x9070e070c030c0b10061d0105040b1b01060603020c0c010201090c0303030509030f0c07050a090227060705060c09010306150512061c050a030305010b13030605070c0c0e01050913120c0501 82
    0x4007089100c1c090144d01000391509559450318007452100307c019403016514400b804142c1c2800100b00420701c4000030000c2c20100840c20390b071105100105402e580840d00074001107034000c1422442c0d0039041040c003030b0f015424402800042c01540310b10803080154000981019100c8002440d401001c001721211031328105541c65482c046040426290704090103101d00c41e1544200006242c0c083d8000e80c1c1110500046010448009900501018004103030041e013005043c40a10042201440824811140e812217940e80304601c00005089070a0740d0005042c08865010941000c1c0d4440c041d45e40255103c0780740c02445d112072001070041c1c100744291003135012010603a02c007000404110b4503455442910248030f2643c84800584207401603c1580d1889071040508001043d0744e608015004003050419001c1000700d500c440302e01700b83d00c3c1c00c41001c52049900401180c00e0070700095a01280035a0340d68940c0c2625a07503c600440040e03049800c005000d05c1171001c1c08002c0d4044400d200906 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832756312 1250 832755062 832755083
    0x30a0f03050306130c1b030207080102040e0906070c0f03030906090803070f02210f07020a05090c070510050609011e090e010b01090504022d0705071202040509070e070c030c 76
    0x51800502a070b1003164002c0c01106408032009a18049020b050b60b131012907102e03040c800c03c2a40440300c500c3d010701410b8007103100d0600c00040c84107003032000340003904084a41c8807261070000c0c600751411401414040411503a070210303401081c0c0c1080000074840c2d251401042114007030070000050b10b014280609821b0300002445000c9412a0806003003003066020359040c016800e002040c000c03100c22030346640803010401f000144a0354001020900e2000b0069212144c43d000882c0c5809800c6500b040020800a41202030001c10861114038600482c4203004600c1d1480c04141c6c498418071075600c1c07202d51042d0601d41c03004007600c07040107422040c4c130802c07600008080842c0602940032015000c14604080171520741018000c807400101c06c0030328403050034000c00c44907960021900c514030f2022400c5c4081e400299040c001140240814540e0703801801d524010001181c070080c09168144e80300f180100039000f17040702e140b5030125541c240714002c07120901b0192042c044a850081102000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832757562 1250 832756312 832756343
    0x40809130507030c02060903040519090908040e091b04020a020a05101a060f07080f130e010906120b04020f010e0d0c03121d0d0c120c0e1e0114030a 65
    0x280d078401ca12598142d41e0500141c07074900710503a12054180c070440f000b60010030040c0003d0078030f98061100ba0203980c05464100c1d603651080c0c0d003111032210b0f0880d490800018100005114441d40d1900a801070f006000325500c0c0b09a98140340c0202e20b04507010b0364001c40c5075415940203110000e0f0b0076400409450000328040907500003003022102c0c0c040200005109000a07040c054141d8030030202001541c0d28005e01030302ca40c0340c0c0f0380204040604000d003c0006900646100043d40003e10410140c10042d5040036407401c29195181c0100d00821070a2414102203803180101607041074040d00c1d02d1160720951030040300d0f801940f50349542c01004480740d4004004e046124602264013039010140060b20080c0b0449540030f5901600b004030f42d02816101491030711400050041c4d109542c00100d040d50740420642c0c0760401c80c401d441c000780c0c0b60800c0002c54001c03400298040810725002003101d08001d003e002840040c0503900741c501c80700d540e02400343c80030009044588e03002107084075130101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832758812 1250 832757562 832757599
    0x1406070c0b0a02070b06040510120503030f01060e011d030309061605120a05071712330a0905150d0521032401170108010b01030b030606090f040809 65
    0x2400c000c941d091444400500780110610a44004940c07000000c04a03448120800c0003038540901002c88904c030290001440b10b89440101004074482c2000d1038803803918400480010760140d10450500ca015681104144c3c0e101101500d51a42014050020002a80400e1071401502c40c0c1d60340186000501100c81030305001d43c0b0031010b1148048400740c80300c3c11000321580c0035010382d441c00f0860134000000001e6608100c00b210700801d01425042c060805e0b581824440c09a56829110a8103d402140c0c0c201c249030340554080d103003400c82c19804000c408142d010301a48240501e459444020503e142004c0c0102500808024850122000f00c1d040c01c079111000e843e030540800c0b01400c04a1114038901003601d00c0307050906800c10103000d44100d65400460f44500301810484000e41143c0350303801840036540030304004000003514848803400541180c2641d4a07403442584042c0400c0301c1a914800115408000d500f052800da8480e80791404450181c115815802030310200d003281450b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832760062 1250 832758812 832758827
    0x80702130b040c12050a09031e02010f11040509090a0302070603021b0f010e160807031103011503060518011103150d120e1302130312090302040501180606020304080c010c140607 78
    0x407a450f020091038036100043d500700d0350300304e2008002c030f014207227002c0c0901601c0c50361030810415400046030084140018034201c60b055145003454180100d400c1c8003908054441c11303800914036000b0b00081d40030780c0300a9601c00d00c3e8810034040680004012410000214a642404039403400b100c07103d00c090101d0302e010b03180070b00d000403407485103101800b000c56283c1c410904a82d0030901030946035045841d020540c0e01d03106400d64044d0b4072030000310600e20b40c0a083d24002d40c041c0000140c3c0f400c02c003981407501c02c50340c00c0072401c980c142032a81c04800340303000840e40c0219480714025809003000d4086001e10040c8040503220481c5a13503050035040e008668052121406c540c1d002e031950701070b0081c100b2402081000b262000c81c5100c207000080e824241c0b15135a01103400e007608010341e40c0e4001000d84000743c000c003a124107079800034079044000b800340802416640c00a5424941048002d55441c140483c042d4100401c08a00400340200300e814440600041d006484071440c00b0140901a103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832761312 1250 832760062 832760087
    0x108071d0a050d0c0e060114071209180509010b03030703120b0312030703050901060617060d02060c0111040305010e0106060c110d150c1413060806120105040302060919080702130b040c 81
    0x890782d54000411b690304c1400d40410101000c1343c110300b48030058481a0700e40740b0504c0244240030329840c010a41c800c1c2140c008840200c1c0490108403071074070107081402d44059840060080c0e0003840bc4c0c00002c2d4200e807901c100301112071000100e010941c0006071608641d04104044150008144000c0300c5d0301d9001248141c030700c44e0080c40200d540d404200ca10b580d021200004421410010540c10b00c3c08800401c0f0aa000504c61810700250a07002d07030031a1840c03407802c184034200040402c2080400e000e508424030b418030013040780030710780341c0d010344540d00d1458000c242846500e01c21401d540d43c6c48041200513040070944e80a4121402d818006010100003800441c00c42607501c0381c0040044106c40640054414010300e640c5410300c19110407030050240d0b644240c3d890b800b03480d0440d09108203445507009500404040c00c01039000c5090000c0100c100da05004801c02c801d0101e0454400c030351406034180d422407000c5856201e108010a080580d0951050800071b85510302d646c0409a01d10b107 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832762562 1250 832761312 832761329
    0x20a0b3f012304021303020420030403110a05100504260a120605030d020307291305010902041b030e1504081c0f09110108071d0a050d0c 60
    0x6000400d98009200c8140850040460585400502400311150002400e03a00c4094080e80780c1081d101c0018280e0300160b02c400300d48050038204005500d854041d0140c0c0320380e41c0404c0c5400b03500040300c40034640b2004002809200c0b03554002046103c0412a12840c260804152707014a45200c01c3c500c0905416942a145e103804507000b40510340f00030b07810f103042808151403145040140789081c1c0344480d04203115201e41ba071300c0304002010b46040c0540610070b5100d40c099036880e08603280c9820b940361074120104138007040744484a01400008806070300116400c0c07001031240304c6440d0150143c000b081c0d0084d00142403040f00c0382c0c0c4000342c80d50380305404910740741408200c0d0440c003015a1040b103032003201c0d4405004004123000c18007072001461003201750b40400406206800c0e259063700c280403540d051055031400002c1c140400b50011444280017443e15410070b00705034100030003174402c0300341003039509a2003225055642d8541c840c000c02400c020302002138004081c20048211001841021003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832763812 1250 832762562 832762627
    0x9060e090d0f1b0f05030d050907060f120f140105010e010228030320030103210e010e060c01110d1d061f0906080a0501110405060405040207020a0b 65
    0x300d001ca0440c001e0314a41d900d0500c86458040c0032100800500380d0641c6204003d1031040c0800c0e2000100c840480c0210b00a50f41c60401c1c1000604a0300c1c0102410410f03007044900344181d980c000012000311243d85004002242c0c201076030380007000b1079000c6810341440c14082c041c0c800302005110b41244d0098840c441886100703001aa2218490702d100a50460808004481ca1240f01600d202442c0240b030005030000d000c540b0800f40f03204415411070705a00c04001001003091110b0301091112402c050700c241c500308200702900c01c03840300101e1814082c041000200d1a200c040036108071101c503138000e10100c3c0c80512400500c1d80f11b95910018903040c00d001d01c580305049034a14075070080b050000c012580d109a65181a00d400c80701c03145808219a40008a41e10a4003a0a01810740580507203214401c1b864240c0c2140c82400c440b10303184174180020421641d807007040d03404544080d100540e07540359601c006204420305400c01e900d0400040765003241c4051011002c4280304c4901d00010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832765062 1250 832763812 832763821
    0x615120b0415031403090604061d010f0e0f1302040b040501140309070312091a0c162301020a06090804030b2a0c0f0d021c1b06050907090609060e 64
    0x206960400e4032940402e401014100005001c1c51055000a0603c006503402d0000d070a0014a4560140e88020006803a055842030303944800702c090000391100742065860306112480160803c0c2e103230011544201c9640010b400a030321000c1b1181540602e0050031980c4580b10340748890181c015014583c00181c0c1081d1000c00410118126030054401c040241307541c0740b85030355054000781a0207100080201e0a2800100e18010117030114030100c4244849484034600c408851030003240d001240c1c072078907a81c0810460300e4034030011b50100410b1405065401290100141d10300000b800c401804030345440c1041d000d004001c406071094a100d0304091440d502c840e4181b96580c0084810740b41c0d03551101c20010035141025004103002d9044805507104ca0003103240e0756040504083d1a00c0158000341040e441002c08120700d1818a00d81e8100a1072607000c00f001e00c05000507030341e002000781b6135031804071310030110400c07440c0000c15034030b4003d008aa0702c60f10a9005000988501403e010150002c01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832766312 1250 832765062 832765069
    0x5121501060f180e0411190b0315060928030c0803040602011103010b09041503051b1309241b11010f09080316050409020703021b0a05060d0f0615120b 66
    0x9013240e1140007081e900e621691500c024140080020580c4403024050b140035014902c00e0540042c0030180000b45c0300e03c0c1182071481c80407a8801001c0c0706400420501d0003580e2101e40e12880480b0b080185607070950506884443d00d030040c0c001400300502d0410015100c0c80020003081510711560091050182203527425030940802c1c081c0f2610440c044c041e41a07141016030283d09100035034000426a55900d8498034102042c0c03a07034a0049122100200002d07040180c007845000d027000000f0840880a0b4035525000c0e40007000d05a542413020300071602d20401034001002c906000900000f10702c40640015100100fa0526007c0550030810115040d14981c0b00302c01c20349800c050081c2c5599194000e19034500c4001003604c0600c001031202099139150b13880a00400340c465002044144025140c0e4003101c90f03c6942180728450440051025454400c1070f101032103102c00c00031a840a15207603250140a16070403007403003894840d13004180d107988800d0003c0300c419184001c10040c50010f050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832767562 1250 832766312 832766357
    0x3050f01091707030219031d0f031504020d020a080f01110405100f020120090f040c1b0c08190b06010c02010e0d26040501080a021305121501060f 64
    0x60001026200303002e107110261030041070414403d1040d41c1480d07400d000a10041159000190009081d068924104806d0401380b5103107a04200c403d038002e070b00c0f2007000954540c0c294000721014403407a00880d08544844940c00225a4010721440384592201c0c940d80c1d85112000500515600706039150860000b2801202c00b03584c0041c1404118640e40d08094907641c4011840c0d40442d03580318000700010800704407085600181000c10750341c4855010401c60f2030b00c0806c400078452490411900002d9030055001c10456482d40101c003998241e07410005012821350340101600e0064280740b0407803013800440340d01641d2054404250f280c03165001195010011100280860280c0c0b508101c41d00d041030008903890312540a4801d44902c16014034903e4680300c940c44840440810107100960f000360190741d204c00650341c110f04110202d240044124014401d0900900001ea01f40f0359124023801858145d40700100d0f60310441d655490020300b181e0701c1094100002e01207080d00003170400c403540b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832768812 1250 832767562 832767581
    0x3030f040b0c070b0606030601120501060201020406090b0301080d260906040c060c0b0402011821050d081312050903030712021b01080f06060c150403091a0307030c02030903150103050f01 82
    0x1510000350343c071a0244406c50340301a110360306000c40d401e00c000e500101070080501900d032550016844a103025030241c849041904100c82002c8240014440d44c41d0010b1030003e5414189000200280e440b10342c54000d25601c0402c1054801040810440c40f05c00101c840c0103c0c4668002c01e1803964490f004c40c1c000401d10f00003000310230001d0204000d988125590f201154034150503203d16030f583c400014000201c081c0d8451115001042042031002c140028902c0008a0403e295240f40c043c04500f4001c00c217000050840f900d401144060790320075019110000409000c40707a4582e0320741400c0800399041140f0200603c50000203640d0b00d1290140c401c03040c041a198101c80d84c0328040101d5011000408550300400c00b4003014032500801c02000d14500c035144803440c038038109424014883c20003030b0028004592041c0c410030850856608a951000719460001810044c842089003940300d44a005a4103124204ca2195880340024546040341c0c0b01d00122503d0740c1181004d00d007640c03140031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832770062 1250 832768812 832768823
    0x60d05190507171012050610061b060903030605101d010906170a0b1807020d0518010e0102070f14090f070e150c0129030109050706030b010302040803030f040b0c07 72
    0x20f225481c81d940c1c0d41c1081d0313000038500ca09002026118084605030700c412110503203855100c2400d000d0b14108440185016044070300c1c0440eaa00071103041c1000c4064034000003005240d95820140525220758402406008010035201c1d40c1d400c100ba0040280543d0300c09a01d05140403a1003d00940c040c10a90048440580b01c81c110341d00c0540fa1303805010b04c0100174244e09503c8044215441c0d42d040f0909940703590f8407409442c00c2c20651b000900c1c10880f464820188034080081800c0c1032442400d0b0242000b007480c08000aa030140700403410640c02d40d1007a0121604400701041d80d03200441c841c43c801900b40c0b08662a6a038486012058500c103441000c089040d000c2c0d410302e1404d02241680c8007110015841d49008108246903003107458807481162500e001d0320340c0d50000078820700c644810440440c003d0217207800c6511003944074403c520401c1c040c1a40c60082e4110741c0d000740c0640300202180c000762900c07450310303c0403d0714203d81214200c0d001c0c80d400380001c0c0c0105000c419194100d4114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832771312 1250 832770062 832770077
    0x2c010f140d12030f02091003050405100c05030109050c160501020c0d0302040b030f06030a120c030809030703091e0b0403110a0f080601211401141602030d0f0b060d05190507 76
    0x400043d0010304a071040768080ea6000c220b40b20080c0c403260b00c145000c007400c0d500041c06160a0510f00e0030108440300601119041054080a00d0740c400242da042d50903503880003c16807950030700b010540c49074105515011000a0004080c0041035018044400b016025102a40e46100b070071022440741e8001c0e09031400d41400420f940002181e1031f0340c0c0c003403000340072960706035095121101c0340540340f15400005601d4210203002c150b84020507907041503560380154103200041d039000d441c800c0c9601a84010318942903901c6160040500d55000400c580d00c00d00e541c2e04d0f01c5e410704200090740400c4540c00f80c0d55680000801010b048460422601c3c1107000e0b0030a84d00b42400d60810008080011201715940400c0c0f4020908032969032210300d004000008541036189540151360400074914010b400c15114000e91194001c4100c50840d065041c00098200e02803a56100400508030a50780041006c140039414001541c807141c0106042c070343c0812502c5c0103150301015104119001d40014500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832772562 1250 832771312 832771343
    0xf080613140a0606030c170c040c140a090305010e0d0504170c0a1e0e0915060d08031f09020906070605250c1a010501092c010f140d 58
    0x10315440d0001849420000d8901c51034601c25441d1012031102507454075941e120400030000000100c40040c089010f480c11b892420380480c940324850401240d00840d04d40c4100c40303289116907052070150107a090107644681e82150010b180c4201404204c075250318059001300c44040008181c4140785036980d03601c0c50981400800a05003407002000402c0c1c1c440c660a0034025076400422501400d011811010804040403403404c80e100b507603221007451580207060103076001011840040500203030301c017000315031240300c0407844444807480c0c0a05110341c007105112901d0a951001442041c2d009407020840362a0bc0700c0d6000c901c1220700440c1e000004202203400148550801540000191503146207007142c0f0040710b1142c00c100041d14001081090900d0070014010700c1a0388400c5220309010840d030515001130041c450a009000e14119103243c2a0a444104003d441d811400c03082c40800550356032260b8070000b07045010343d05001400c4114800c55040100c16110072903040b40d01404450320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832773812 1250 832772562 832772581
    0x10e061b070b3402011103131814311502030402010207080f1506040902120106080d0801030210052a15181c0207051f030e0303040302070311120d020a0c0f0806 70
    0x4441c45412a00d02050000740310740365210180390002c1c4000460b01c0c0200b02c00202a130111200200701842d905048070a004001d00341c5a0710b004414691058110750800c04182d1030010300708050001d144c1040ccc0c01e0049024010364001d507000724400c1e0200e40c85186c565034000d846282d80e049969655001e001c003483c0f1901004405a0803010241000590660355000301d1440340c801d020f03241c1e0300d0b9100d0710704000001c010001c9210441040c5000241d40d411030b070010f100b00480000780f41c200080441c258a82058200f11101000505903920008121240c502500d5556103e010b132400032100000429140028902c24003440041001c0c052072000840c5428407241740240c54030451103074405c040707059180c007030051030840c240142d54501440002001815159404c14901058105005100c0080d40001c0c40d0f5058a60080315400c0303030f440d5000822080d155240070f0510743c0c402c00d62245040d907000314a0441960152030707140780e050b444400c0035814400c41d11400d4815445480012040344 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832775062 1250 832773812 832773827
    0xc0607030203041e0b07080a060501050d110417010c020607030527070512011a150f0f1207030c0e1c1e060203010b0301060f020606010e061b070b340201 67
    0xf4418015038980440700301c61303201403d008410481e0000007100501246a400803600e544c0012600400e01c942400e10700001c000740902c60b218100541c48103000462412910203480180915404c1da0303490080100d05640600303030b01944c550140c007988000ca089940f2074020b0340c0c8101034050080750358401040c44104c0400c11814401c000c0d000c5c60f207001c04c0995444964564001c0b40400100e00c6000345080b0381e211110b02d15030716109510004940303410900e10000da032198091710302c01c00c3d21182d1440320f028052048031440034841d44400c04201807903400d90b2240c00045032554030890b81c118030805100032031410441c4400c0c103105906c07031000020040d665024141c15612450400c0200980d5020203036002038000140315840800180a40c5501503400c1c2d8149800c1d1000301a80c1c180343c4006845816060f00303860142e4170015200b952107044030801c0c441200808120b80d41d866860000c02d0b0950042d400004042180c0c1107010112a41c01c07403071403030a5140d00c1c5021a11002a40151140d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832776312 1250 832775062 832775071
    0x3010e0c0a2304231f050903010c0302040801050604090209060d060902030607030606080c0a081323070609051203041715010303050d14090a03050a1b080903010608030c0607030203 79
    0x11408501c00010001d90005010740288000b1980303032914100000690714200748141c1c01000508404c3d11070490b9102012010440c10082524032041800c41c1c00312030034490341c125541c0540c00c0c050007022840d8035500400440c0e18002c003c00460f00c0d61000c0005582c91410040d621403540030201e2845d1074a5642004606c0c89458000346109040c0d0210341040422542080402c0e079801e8100003194001d0001a4004211000e0718603281d01c0385030140c2003203800f406405407803460056031410800c0d00349039000001c005010541e080e0700c50070943c550b140070078011a000982d03ca180000d030350901c4140b04e0043c0c2d10504c06075040c01d0400d60a0030308213808040000341407240054a816a00010103914082d50180d6641c8d50340e160b604154006848003950300c40c840c4200002045464800428800d6189030315282541c2ea4200100088810302c6080610b420000340c0c00c013006040000341c1008041011042e8000d102d6030303a17515500c4c1c3e248d00820200c40480d03045080003a180c1442a402168403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832777562 1250 832776312 832776317
    0x14010204170a05060705030c041511030304050601170a110603150a0e0a0b010507030c020907050d060609080f03030108031e070c1710050601020c04020d060801090c03030305070503010e0c0a 83
    0x8090703607800c008681c00424008503a450b00300d0300c0341005101c4180080d650101039170030140c0c40c5052a0003020388030300c124400c0c0803044202000031844240300d0014007042100301002c5a4681c20f141c1000d03030b181c81081c0705100a280c200030443c3c41c082004555038084513003141c2c2d500a044280011300c41258402040d02c030340d00d40c02c6014502070b035135251001e80c083c0c210481000158030f46407110504403100031010708e06003c02031029000003503119140c44c2c405a4141d81c0074043e0345a24900f91541e011b521048804641070076401309500758000e00300e504441c3c0b940c049411202c0706120858882c80207004607002c41d0810403600882e2240c4044c04e642c0c0f00e4503040c0306841d24410b52500000c0300c1e079a8002d410212004648901008000c01a0020f00d0000c1c40c010005410038200103569064401d441c0380c0103507004070ba040d00802181c1e010000400c031600003841400035919059402e032416000c11000702e803030000410009032007101aa03041e9403840707062103071586030b8500811a540003290440c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832778812 1250 832777562 832777567
    0x10f120f0e01060b0c190c06030c020c100c03090e0f0714190909050610050a1409120607120c2a20040b01030b03120325021509010903020a140102 64
    0x500000902c503d0f4000e03d02e180b005611048804111418035803444d080600d41201e48409902180c01e040d0340d8000c80e9124140010f0842c105403080c0e050011aa4015a0040700f01070b005070010b405c4006440c45c0c0c1d20a50f1404d49890322070201d00012041a110300443c0302d107600000315a80e00580c0841000028480d05506186030310122500362078a044282d00003038008101084009800d0291079000001110300c1079540c00e24a20060003400341c0c040030002c00c407076078a800b03003001d10340e40840725000d01c05000002d00e180045505503031090203561290005550000f141c04003071041c03042150700b00703669031340f882c032003044582c0b0a141500d2180303115561251401c1040000d040700784000c0c441540080200c1d440040b00c000c110468121000c60381c1410308024218110340d9001c11000364014620100c0e540302c0c2c4074070600c0035803659003403140c481003a120301c030307840045400080c080070503010340040d0300d900d55030746401a082c0e9005050040160340b00c4031001c1c0c00100a86101e50001070b07070400050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832780062 1250 832778812 832778831
    0x50904150e0a200a0603091502090411030a020301170625140c01060503160302030c040e0705060f0705060127270309030213020a171504021b0705010f120f 68
    0xe0f0f035125504501d948900720043c4401c00707007454402d100040940b800c08000d80c05007a100c10841c6d4a8006045080d950300051880195a403648401c000c0c4044a01083e124030349009804001d500a0140401c2070900c1403410192040004640d440f5504200240303991403030150840383c0f107410086000c820b020301059018020400e003400b515400e00440004100e103441c02c01410308049030381e1101c5a5032081d0103420f20240e00c0000344416412400c0d280018030008048000d030801410340c0226600110000b2007031079421818000d816541d0085085c1c030003c2c2d0341d4018284042e0503001b00f000f507805450f018602034410a50092080400a1306841d0607440391841440800d003042804130007040b07a011043c02581800306d0101400e00310300383d007140f900462580181155480202c80510a204800091680305456064600a22001c0c00554817000c0400481e0302c0c103002088200024481c07c400012070398403c2078122100d00320350319000707a44225000c0080241100030004d038091900c0f1900c10307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832781312 1250 832780062 832780073
    0x1a15270423041103060106090b0c10050415051f0909052b02070806010b030412141c0e0606130f0b0303070f03120605010f030513060e0c0109050904150e0a 68
    0x5000500d005460710500c1c546850040211048036080ca4000d0384402d00512540b03802100c2d0509856a811070181c80700125800c9600d4440c9418995030010708140c240310070018640c4040030402c1301d8001c1400950358442600e210100c03034121801e89489580300412101c2201e50146100c207001e60300b0398070160070303a20b070324064202034850650560720b0304411012410f9041c0b080d500507000c0300b80901082e525182c0b03046201c0c00003600260000c0e9031241018645c5000d0307a01070255040c00000591541c010810030000500071a02040c00c060a2440b8400100008126144200d40040c8000c6a0130b241e080d110340101120303811040107599802450f0b0745603904001074182c9522441505038004083e140080820f1142183c4034107603424600103100701d03178001c1a03205d060b00e06840c00180d00c0d03070b5400d0302d05103100c10710708050001d030714007215150f031100301240d500c410401c2078880b41042641c0d8418030040420846000d00110b00f080c0303400e07184c80b0164001c1c0c0400794171401200c80350344058490 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832782562 1250 832781312 832781351
    0x902160b0c1b160314070e09010207020f0105030601021f11040801090615120201030f0b270606040b070609020a0305120702010f1103031f091a152704 66
    0x5242021a021600c9010125001c00c01c0e8802e00c290000b4080510038001c48150040503400020081c0325800d0726a00400c1d02088807600801704403030b0b0400d00303041040c2d1490003540280c0040c1c0c0586038186d030031340065009104981c02a84181c2c028111445400030b030352034012248c0d0603c620107849a00c48200601e042029102130034480707000103040c404038a0048100e490080300c0003030000d10144200103c41c0700010414981e40c0a0a000c1080c20700c0e500e2150040074244122980140801e600801d40000c0503034001c50131200e0b03480e1410300d4861500700030032130040340b003684008007040000000049007a00200700040c40a0080c48000e81c032681c60a041404801c200c2500c614045400d1065690054181000c2496420320401784028120259181e2000801040f40980403004d040041c40e24411410000d0100c03000400200c5100d690310020720420b0b121152003030751440044902030000034211075103000e0065140d00c0b141241010b210400342d201e200660310650b04c86500380004002c044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832783812 1250 832782562 832782571
    0x81e151803070c210b0c0703050904050114090114060a140c030a05070b0601080c030f040c08030a020f010608070f060f05091504030506150303180a030c09050601080c070209010902160b 81
    0x8100030f000d05022000014242c0c0c501c0103a00c1d500d041240304049040000080d030400c07120300c0601c3c3d94a4a60509442e5840341d0728905030010300d05000083d554108240580100c6821191b107900d42e41c0ea2a2120309030003802d902c0f079600810030002c00390310718000c660003403600f82c2d050707246424013180d00c841c642190820035141010400005980382004640d081440c1c1c081130034204405142002c2000003603c3c0070003010240a06183d901003418001441d11300002000c3c4182100c1d80c504800c68000d486201480840c0982d609003440491210000b089003c195000705510030020f40c038043c0c0c04c4900949188000d010310004118422481e244e6000d680307075410320048002c0e0b42e1440c500d020b0f0314004009001c1401d404503444845a55a4080226030448500940d0000e212690000141c0d01c40210743c0010302945a44000044080c05500940c2c40360101f6280c4604a65070100000668494500c000303502024590040c4011405036010300404c84041500c03107502841903440c080000410398 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832785062 1250 832783812 832783823
    0x504030e01261302010f020d020d11010e010603060e1902090705130e04050a15140103110411070b091e1c1b0308100909050c0402031b070606081e15180307 68
    0xf0502025560040311817820016188010b150900000000030340310b8410b04141010080410101c03d0b078903400b50820030344680010300030803080b5600e19004008000e8003406501c140a264880e84100600203c2c420303c594026048660b56a600c500468460340840404034085141c08400326440400a943c5032045128800800001d00c407400c0811101c034100000c440c42a003464402c0b0800b00305000e1442c1103a9011040c4001c1c3c0b820000010080c01d00307429000d01c00700001c1b0b00f00050243c0c80c915a4050841c4506856200000034000c8550840017a0000146d52100e080c01907a4071059148084000c03031490043e9503114184c8034049080d80381c060030760020b4015814040b46181c52000b40b401003d204404210002041d03036080c0e240d5140c10407a07445541d000c80001e41c0310b144440d0303075003107441442402a6a00c10a1401000404070303130080d01e000e403103000c3c2c0061143c600c0301424084244e804000b0202c09141c807100e8044240c00034409503038145c000304503103c5040100098400980b096 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832786312 1250 832785062 832785091
    0x150504290a0e090d2d0f12090b01030c08030c151005100302030a050708090a08090301090611030a140408180a09060b090102060c0a0c0308040804030203160302040f0504030e0126 78
    0x40d82c0148500c100800780015501a0180607490100365071080d05e82818074240302000900d118030507103501c0340c8101000107042c02c0204520402c9601000c69060b03074440e1040540107030301c40d0f124942d00c1c040c005200b1813680c4104150400d00b150700c03440710350011821254181c0315882d10046001100c6c040080c1d0040b9130084203020000807140122079020096282201c1c0a15100501c25500c031000c40c0e01400000e8001907003104c58400303400c000e0a90b90041020320102141618402c1d003907100301d0701400351518001c2c0401419401c2811a400360340c00000c1a810074440f140c0501c250f48852a2035070f4020805100003407079082500034032000700607015042d511500780100280c1030074001821081010340030000e5400d2542c210341c94085240d0140b804900c1c0303554238a0000c86034450b580020b0351500c6000b0030420756480ca141c0000c00c1d40c1c030a07141070060880052044040d104251002030124603041d104582079403150150040d260940c560f0719142c40c0d1400800e4522440c20380310080c0d050410b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832787562 1250 832786312 832786333
    0x412080706090b09010b030c061b03040f0803040e070c0b2d0c0423060d020c0a0c09060f23120c09090604020f0d0b0a020d0207080d150504290a0e09 65
    0x388600f0706c200809402070505800003000140302417140030510080300d6001030039031100c00401c0040c0c2d0040d040b49001c2c1e448958a500d0f040e65a504039120b030040c0c200ca42c000181540d0720031240c00d083c103644481c0f400207a4991100c0c1d03446020800c1d07074000c1c02075451812020076604071711440e40a405030624070b0340d80d2070610610f0540c0c0e002e4542c035445618444c84038907880b40c440380d04440b102c2002d18001038849580241150501609000103050010020400706000556900040407688410f005805082c0d036540c00d07118040d020904811070900801107608942001c0452900d0440103600340c450702001c1c04000f81005c6400c2c0e5140419a2001040100f1800c15400c01d103c0190304581da40c440212554411501c2c40008001000c42900410034220109058041c0e80c41e10368003070103241c1c4a48082442000400000c0710740d81200040040009283c01c040c82601d00350f0540e0f4902001c0440c42d030140b100c01411400000d0b800c07001241c2d00007402902d50102c0c5019980c040c010707020103003030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832788812 1250 832787562 832787581
    0x70306090b0102030403030203030a0207020d0b0127110901180902070623220503070605040b1611100b0f060a0807030e03130509040c080d12060e0601050412080706090b 74
    0xc1d49000c241c15540700b00f2003800841e03000020b1b69881019a0405070780e4040c2440840c00013034801c4401011071130010004504040c60700f0b50750641c58a07a03032244500981500c03010040e40c03454800001d9041b020800c02c0c0d402c0d441802c021451050038901c11254a5581003400c04a030300030a8280d40381c0e69184c014080844100c807072003004152600450741e071814803021181c99400741820303c0103040c42d00420001009030610903100e0082d040030040040345801d00705244054070131611000c0d0038040241c0e03030102a0080c0b8861070f000d43c219004003444201015254010010b510800c1e60040710b040c3d444045940e208020181c01601c1d40e204056030600003070280a4900500766440d1680090201090045140c030301441118400c40306a0495140e0b4184003084440640000c1454014540c40008141d080214650b81d44601c0c0c1c02003110036902ca110108412095414a001030410017042200d4402c50040a22250054100a01d4010b65950b00c2084844410048421581c0744040041030b80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832790062 1250 832788812 832788821
    0xa060306060902090603010e09010603050d0c12110615031f240b090103111210060e0306011505030c12010303080a241a0d06080606090c04060e100509040507030609 72
    0x44030b42c005508000e401400940a40814082c0700268207101000803801c1e1403d4214400960b00070091321035664203c003000749412058101a58081c55000440303c21510907030148040c550740c080a4220b0b41c0310a00c0b9543e540c1031003509168140302c0c0c0032140c040008002204a0448280080012a070103000d038004641c000e80300c0401c40d1850013000410400c0303403545c104d0368200c00c2480c000501d4100810703a210180540e8122054042d020010800410041540b00041d5555a03ca82042e44511820503030388070303424004d005003400b541d0140d442d031501410203950052401244d030390800303124814500008500764003e41c00641140c051100c80e0380135201f0744501c60f5a581500c0c450303050000743e4940d81d10312072047d00b02031401c10b0303824403583c425801610210000c824082c0007481d95164a150749240584a90340b00c0c4004002190040c01400c0480c1e003180d80030f03200d14906880384002c11500da0b051400503c140042003046030f11036541c501c01c452041c0ca0355240000c0f260b0814a0040c00c54 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832791312 1250 832790062 832790069
    0x320303010e090727051308030f01060306080a110d05030c030c0c01080105010c0203190602210f0f0103030c030509010311040b031e0c160f080712030506010c0f0f05010e03030a06030606 81
    0x2000090350281503503040c1100000d04081c00d01c404171785501d91000d080c0b00201c09400c060450b400c04800c1c0b01884400c0e4402034126842503409114160b240c1c0c2070240c075102000402003403030403003040c44981820100c0240d22458014030aa0b810060081c01460a69220101403005504012081e100301e40c0c00c10b9000340940740a1070303c5030810350f8035800710303035142c0308110082e420300f020804c080c00b000282d80440e10300424041d00c0b440c2980c603000c6140041542642c20f40d44007000325002030420b13280700c044181200e4040c1d88004001c042c0d518113a13402d07071055110504150300e44103100010a0010028030040901101d156664904809110742c810f41000902d42c7c0c810642e000d210818454000340c6100001c058110340c160580e030320700000081219000100720090100780c680030300c00305403107080c000d0055171403d01c50740d5a00401101c101c89602c00040036010f4100c4d44001041031a6406d000d40d41c4120000207a40322030a810902d036810484010702c0054841105104001c1c150144d032004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832792562 1250 832791312 832791329
    0xf1b080f1203070305060a2301120207170c010207080310030b1308091002071508400201020c030a080904060e0f01060c020d081206090c0304320303010e0907 69
    0x56681c0306070400311920001e07091804258a03a80440d03000c1c0d6902440800502421840841d04000326840d0040e998650b540140410007071883c1040b02000c90084480195004102e43c945151421007a075503900100004155503509100b50400180307507000540c01020291201341c8194690b01d0004040c040003400740b8244880d081114000551003030682c0c0500e64212644c070100b500040c0100d14043d0b0359070000d41c40e0910287d2102c20541c20005150042c4040c140001091a566100010840d20240d565031a001840e01270b06800149102c40741d03142c4e1052043d02d01d2003818000281c6402c20942d42034500300d000060544091910748501d0f00140744041780c019951501da41209860801403250340280000743c034101c411907494002c0440010703445406603880703210890868402d02c03021030714140a06240c80110310b45000e03d000b5284a41d42c03110001042111107000000030a149004070114a01544c100c1120380a05001860180411a058034198500310480501d0a19076900c0b4a40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832793812 1250 832792562 832792573
    0x30c050d050714120718061a0a050711060a02100e0d091502011407080a1a030c011107051206150d0507090203091905030a030b03030a1b0f1b080f 64
    0x2070070110b1032030220b41a1400e42e0b605110041c020802840b841103c07908a406240f20214898210390f504924001414104015654070748003c540301c814061801d01c1d00c01d80504c0b00800d65407080000f4624981300d41c00c0030503c4015840800d5103500208001c00141c1c100402401c002c034170900c07a864200144100502c1e0480c20345c080a0404106802075142180c03050401c0c001182c000d40100041caa4404420b00603417070301e010014501501960000480e40c1003403081d0170440680060402a0040203015000a205d0351005440c8101d0f41d000c0848140180d40740084c43d965601110103000307004801404240c41e0842980c40c0b0704013604030051041843e112010045000059903900303841004030010303a80e44554403610305d00030188040d04844c01e410740c01e8104102c40400a019001c60380d8030f0511014059030f04041c5c0380e0050604a500050903488103501d260640810210118051754103190307000019103802d141038040e002002e14070f22100b60708000308402002030701e5043d2041d070090f08 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832795062 1250 832793812 832793839
    0x2210c03010b0a0507050c0303030117070f030305120621030d061a0f0a09030209250f02030d0207150f0b120601050907030c020c0307080706030e010504080405040e1510030c05 77
    0x542c052a040f2204200020404100b005020400420503901c0141226225a550b0ba18038041d001a140700c000c181c050180000f07103020324808488166641032b164903050610b03c017411440c00800900095000c0009926450031700c0204420595100340e11000e0b540e949101400c035401d41c3c2c016405480c98543c9145100c902c245030f80180c49001082c4032001e941d4540d400350403280082e080d00701a500950410a0281013444107811040540f103d91000040d1541254282c8601160504040250308204420b203c4041070384d005101040c8180720342051034108104840845118004e0341021664a0514009914211052045c8210090300801c160741c18500403900c0400054002c1e0306050700e580314040240e0007805550714050020302101c4480d95a1400300703075518001d110718404280b803c0c4904d004040c0c103004079441160030150307081c5014908014400141380020341001c45000c0e54101702ca105003802805400341441541501060b07085007840110300c0b03083c1e070086100707407254001103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832796312 1250 832795062 832795079
    0xc060909010504020703123b150916080c010e03030403110d060b060d0c0f0e1f110601080a051603030e220207060e0118021e040f02210c0301 62
    0x181c1510426100981c481a0901d03043d60705484020000903102d0034070040b0341c0c240106903103c1079007160058119002a0201c44100c03038083c110340162185400482d101c00820f030138404a20341040344003041b10480d521000c401090104150042c000b1508506411006580e011030342c0c1c859075104501071450249950758001a216002c909640101044201e960620449901101c035052025002554481a20700380310014021040d1402c0460200380404603054070503c910b4443d004060001071000c1d5840e0208641d0003070311800d003c10062203164010801c0b5061008134000c115101c000c110200c0c091078600d00308048580184101c0340240300810100c0d03805606c0d8004505d0a8030101700801c05071600309515600034645c81004d9000041010800121344d0190b520040100000c1002241980510081040c01d26000c0d40c0190042040305420802c0050240700c004021b00010f09080481500b900f41c0e00301c1002c409071b40c07500c408032980c1c02c0500c02150b50700c480000b00c554034541c144100c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832797562 1250 832796312 832796329
    0x708030a080601030b040f050618010b07030e03100c09150305131e0b070c02120c0d020616321c0c03030b04050a09030212090d060b0f040e010506030c0609 68
    0x80c008000718000070500b0799020340e10540340d101d0050410700040c070b03c10f001500600f41c2039400d070780210440e0700c407001000c28002041d8103070f44032035800c145401c40b192001c80d0072401040456030725000341d01000c2122101840740c00f40b800072549440500d1072400e240841984100c15403041418184001c00c50307074540b060740e0100f50540c4404c1034051081041c03524603c61041103001440e2207000f100303000c8a250000303541401d451003141c920300d0340c1c00200807040e00c9503a482c042542207540c100c4c03084014981140685178100701851050180041511041c8036519907038071501d2042a000b448541c03944205110042d1007119034010820313240d24102410081a000c00c0707082c10091746454100401d8826005a840c0f090001c105021704d0421141400050100200460241c80343c07044414481c11400706450603000c1c0185590900180c03601d8101c080c264004919030b2140c449101b509056440d4850800c000c240b8200000b543d1803d4000e151030320f04e0707112010384942810b00c84032606641704001c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832798812 1250 832797562 832797577
    0xb091002071e0503070c08030c1605360103031701080109030c081b030304060b040c0804080412060212041505091f0f02211501051606091401060e09060108070803 71
    0x103060044405080013815030040e00c000130149480301c0d900060991000025002441141043c1c0742c5400b04005508000c5c070f42445030a4100036500c3d12a10170300200c0107241c9030b20908280d1405414002004d01f08072603026041140858203584c1c0c43e40500c0040d070300306800350491030001c1050480350785020b1b0117512101c100505454002407541131100701d079800e05034002440011651a82000c0c40c02002500455010351301880c03502a080800307501c1411354501443c1c010204a01e001c0c1001ba1a1701c1e41d8030001e40907100c03582c0801080082c0c011000d10304d44200d001d03510000c1c4a80d0751140c100e0a882c0c002d801c18030340d40d000703111040d5058074025010025000e0b0a000080481400403200c01a02981111700b050098049001c84000c2c015200c02340300d02001401945007a0f069401941c03540221613041559030040824000052407580c05800200d02170010b8190000051380302600b910440d411481c9188958414802c03405800c05c5a6405849800042c2424900f000040c59680c000d000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832800062 1250 832798812 832798853
    0xf140c0a021203160c080609010506010f050a140d02070b060916050c150c180607110d062c01110711150c0d030e0d0906051815070b09100207 62
    0x405502c1440070400803248109840c4400001c282800d0130b154400c11054440c0c9501c134040d000010301280c03418454a48180c00503144e5210101107203178100c844d80c1089a48809001d58100e84000204005014102039002603101695440c1c1c03034900034075503032000b8081c0345c050b81000d014080c46450140f40502803c0e200e240180e101c0030021000d81c0340c11940d9840c0b02c007641d114818007000400f030314001e101654158a651011380102c40501006105a0b00c000c2c26092407085805038030319100c070006c15a54000e00300410044408241e5a1101250000c0f8401718003040b10688080c860038081e003050403a81b0082217050198a450b0030702200b42002c0f441e480f902c00310320107a0340e80750305000707481001c2800412150303400041507001d0014003c80e8880039061040b4127100d69481d02c40d12061091b540705aa40c0c1d8205000b90340d9000381d02c600f02001680c440e15030042441c01807203983c0a40351043c000c60300c07464181815918203003000755440e0490090b500400c08800420301c02c00d6401c01d4140034030b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832801312 1250 832800062 832800079
    0x4021f08130206040302090c030f011e030201201c020d0c08070602070203030409050c0d050c03062b0503070501060302010e0613060818031b071502070b03060102070f060f140c0a02 79
    0x2c1c40001c0e41803299401c0203500514050600c519810b11101840c8035100242ca05d0b013417079072100d100d6501348611440c2140600500030061006520802c854041c610908014413100c80355003507000e040201d81c0c1541c2451941c01c0360030010f6141d040028a40114050a080f031043d41c880d01e80349034a11480202424468000500200710340b02002103c1c01042d4407442081541030808665040b03601007145420380d2410319001c1012041139004070b9001e904010040401c04418407911009005001c01c0448010181040c41c001b04805000904e0030074800c0000040d000e04610000d00307003c020a41c2c03140039079801c0c0300b4000c5a151600000c41940c1c541c3c00d00901c04d41d9181c10310035448802142c0241c150002252030a0200f440b00038a14505000400b42c440c82c81c0c892018849202880c104000141d000381d03020071650201c0c4009580011040c8140c0d61515100e034002c0300740710100d900c65400101c55150404989034000b01903056800750742541c52420104000700d96903404200c0000e44281c011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832802562 1250 832801312 832801351
    0x1110604050d27120311070b0405030615010c020d020406260708010501030320100608010b0906040213031704030c080708010b060f0a0f0c061104030b090f0d050a180e04021f08 77
    0x40c6c5285400700580104403000d5948401d481000c582003407050134003034480c020208450301c015081d98540408180e4036091040707129000c00c01e030100e02c0c903003ea030869a942030205880d03201c907020a1840b211703519144a02154000d00038034009840c0d00c000c050fa45400d00610009511100c0c1452403071100c12a00c94130541701d00000e040c22041d0107100350080c0380ca0000240544190045034a0140c211240403103907440d0000d11090f4070400321045d400c1c542c40788040c80002d040516803000c901800e0600e90030703e5102c1e1b031103044d44e00c01c03031b048440c45610180d0f080200b0b031001d01607555401c1e0240d07400ba007088203444954250b80600c428810a2104181e0644190341c401c04120070300e40d0b0840424410344c51540d5100032203a1003400b05039140f5881d07000066800f20002001041001c4034001418600c07641001181d29030046411708040029011000314000568034405003d00008000000345041a1040107840d2841401c6000d0080110b4006209190002e03e4103500c15003900a41c9030b65101d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832803812 1250 832802562 832802567
    0x50105150315030709060e1018110d0507020105010807120f170d0c030506130e060c0307051c0b1f0e010806060702120c15070b011401110604050d271203 67
    0x100042c0d0103401d1300c2070311300000d980241350300f08004880c1c4000501042d61074284c0c00d1845e0034035500070484040e1600d0403201c606a12903100408950340300e056941012034030700c1030405a84080d604c2c0c00040c0c0d1503100500c50300c00144031840c01841c03100300c0340c45400500c1c4e654403e2684000030241102d41e00d5240e483c50403280074100d441800f541d45c400c2010b080705480c054018481030340d05501403114403410000c0034419105041a542800004100307550396019400d007180c1c03008052108005041c0b01c500701c01a20301d0828441030205050101d450395103103080c0004003400321945046070300301030360840daa03130780040494222038400c0c40c105403159550008200c040c403580a0082d00b11882c58005803200002040c010300201044600e083c0c0e0030410001b0f01d8a500500c2ca0152080781c80a0041180100c040480c50281c2c106050603206140c030659010300305801120150b41c0c0e5000750b180a00d001d82d00905003020031100c0707604445584003500c60442205228050520900d1a4142c0c0d00300385070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832805062 1250 832803812 832803841
    0x504020318010612032118050105010e0a020708091005070b0a09050616051603110a06051005040212010e27030d0518150a0e070f080d14090d060e030a0e130501051503 73
    0x5021707484440c0350203248c3c9401c6000340400d106107580c040614001c203044116600071035180c0c6420041072801d100c00007003040304500c4071040b240c05107e130030041400091a1103c840d8480c548aa100180c60a030904001d400d0001c020207104a04040c14100c80419800100740c4441c220540e01910380344005140607208013034140950846886252040c40401c0929040244540c02680c6940d0a040c1d840301400240d0040100d40f84400390081300503c0b40e0140b45101c541d000171021486a40100c291444c14500c40e002c18056500d07400019114414076424020b41d500502c5800c60320071455581e90256448520001004107000200d0001c0362a10b01d02d074009100580c140c006480b603896031000c01030a10003151103114000c0c00b92602001089004083c100c44c4034490190701c0c1c0c64501040104030b482000010100c0d100c660780c0490f0841d258040000d401c0100c00394a41000010700031007001a02c1c0e00c400c200a41403400e060061090f6100c8800865042840e84010350301c1392502010100d840c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832806312 1250 832805062 832805081
    0xa03060b24040302210703031101150e01210c090207050f1c1b0507060c060905100507031401140607150507020304090c0815130605040203180106120321 67
    0x500219000e469a01e8100200304481c82102c1e65017010b080060201545d024034451171072260440507080002c2802501d0110000d060200009584241d54201e080083c0e05a00028149031610005100c403400001a040182030240107007400c0011a079981044002d1500850a080d600822080104a03003005620310255409042d105a40b0b420081d461410301d03004803210009002c0c0d0b2040008165401080002c0e5030080042c261850a00c2c00c1587e0008011074100c80055407034616001060041c440c0742605e9122090100f860700301120000e082d03541d03a041c1414402d0294004101110180705100702174037080d2950b9403901e403181000718401c0790740c1002d0381c8594142010003042c07560110052041d1034006908008187c40040300311000380084030114000041e6000c01101032401034614411502800c5001c5002c0340c031100400c050b6002a1f804d4854003010540d03a1902079028003400d8090642155000d2107038034070303441c0144800001410170f50392900082c071701d10101e0601d0b080000b59 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832807562 1250 832806312 832806349
    0x60c0f0203031021060219020c0d1e030905060a170c090108040f2105030105041104050d02211005041211030a0e0a0e1510081e0a0b090412020c0307050a03060b 70
    0x9030b9480d20071650401c07400703249507001809129681441d0389002c1c4042d8102c190030903803800e5800bc0c4060f144a0602040e0020340c00c0c0a0601000251030342e504d80146400800d9036202d20010a8903007510049503030142c4144040d280a022001243e46e20a000703d610903004610409070344014142071100e4010075810081130b80d80041c0400c03900381c00900560407140156404c2010701e1141c1074990690141d8012541d003d01c0c100c82c0103000d49007803404104808844a00380010344801088075117818010f50000a0550715042004240032110081c00021f01e61414080034030111044583d40741c4c45401c500e001880b13041041150940c5806040030050138040d601c00b00c490902c000744050315450050054440c480c4605241103240c0710310131882c01054a80001e200355050380415031004070000b00420007943d0307541d8601d00c407655940510760040d030040c02c01e461030300c44106009080040c1c0030030060017a48418801c108648865910303100b101d410040009503601c0c81d5000030306080164440108 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832808812 1250 832807562 832807567
    0x60a08100f060503090714090a05071101050a0b011e0203030105060a17070c1e0b0a0c0c0f1406070509030309221d1501051f1704060c0f02030310210602 67
    0x31103d0b045401140a900f2400031203080594892200c030300500c0b1042d10540002d01d81000c03030a0300c0f01c1a006503420481c54181700407986001c114060844808940070400240c03a0449004596040180720840401003003d00400540c0900c01940e41d10040c801c80e4010000002d0203003060707205490349440c0549180004900d0700703184600812120b03103220280d4050812001c0310242a080f00c840c40d030312641c0011f00b00f8071a9280c812101c014240b030000c01c0c051150b50040d0300c001404840040c1c0c0000e100d1102c03500a04d045820852070040001c0c0703603800b880010400344541c0e903400015100180000c5030308121070b503409203c04e040c2504401000e030481742403c1d805804582d0061103841c070180c0c01340854980203a032000110304000c0a109144e0040c00d50a00c1f9810043c0310410034100010f541000581e542136070900b0071142108440c16250581d4030701c000e101103684485861000c1c0180d02c011400c504005000005007440c41c8920101200000340011030300d0009411074052a403c0381c021034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832810062 1250 832808812 832808819
    0x11b0611090a1203090e0a11030f04032007140607080a0806040c030903080a0b04091a0717070e1e0a032103020304150f060302040920030c060a08100f 66
    0xc80c9604072407103640c4100c0025201160018500c040c0c00c00854241e500c03025103900d0003403a0742c1d6000018205290745522000400e03902e54101c401940107c0310085114800d01e82410000c5c150500f0361810050600a903a4000c07407400c1c001403000648854541c244045040300002460920070702000410a0f240415950034407170300140c1319485807500744c5052000d0207079030f50210b080300e446000041c003141255000c103c2d8801c02d980401e580c44405000050780d200c043c1c4460841c210f0050b040b0307194444540130042c101e0781c040c1e00c0740891703030b41c800070103420b800e02da0301c0038040d102240700313450141061400f41800c0b000c44841c0c124007014090072006d03c49071281425000c40104012245250b28030404410201c0d01c00d101700e03440741e60000a085030105800c0010b501030300107640740c02e40d49600e6003c0480965074074810b11194620410217a103003807000096041c2c1d0b40100710803c41c4a03401206040d00991035080480e80c40c3e15007071500400c2c81d0349100c200251000c035504480d581d00360340030011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832811312 1250 832810062 832810091
    0x60607030e1c05011e0c1706060702041506090e071407030909050c070209090d0e280b0c0615010e1c150203070912030507030503272a030705011b06 65
    0x8505d130f9860043c04000002103101003640e901070114000100e04c2c80d0308410f80440032440c0c640240d4020300303e524000c41a000102698101d000c20201505400f03010440c05421074000310040100c11186041c603e890903016104003818500410740e01400180d20f01050300c036481a0001d0400049c00308807900f404054007210f50804c42c81280030b10944000300d021010000344c001c4512509690300f000c460504c10500c007018000c2d03803034401c1340d0b03581c2100051100728a90724680609121031800382c58000d80b0b0441403400ba0054400d103c4a07560240c050b032a030b43d001d1141901544241e445015601c2c2010000c0c4c5012248078001c3d14000000c1011203502406d50001c502400301a6141604070b0303121341c01c0708444403900400030003280c41045401c0000c1c0c081c074041c56004c0c0c0c0c00c088404a07c161000340711440303034041420784640c0e00550107c081c6100300b0549199880000901c0700c01071040740000c00d964401a020f5503042c0521398042c0c0000820b020f820f8807002d540300409001c4183c100c0d828 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832812562 1250 832811312 832811321
    0x200619020d0e010801050325081b0f06030403080c090604030501020c0313081204090c03020c030c0d140a0806130b060d0b0108010b07050d0e010e040603110f09060607030e1c0501 78
    0x20000910003070b5500281d620803c85035041c1e500c010302510807100c09031a200000441500088495800b84000180c179a20174030070070040b081c4000f0282aa80344100800c0560306100c0200c5118460900501003c43d42c0b000325581e01484900006a0b01c1200e540003030f00324042c40c2d100811940c00000c00400c0d500c4080050120140c0c411040c0c0791064546640549030741c0300088031845594240001c00654006800c0300450600328140145480010080d440c1540c2c0040302541f0030340d0001c281050219800040344600200e50702c15241004021382e4010250f10010b00010301c00c8500110344924007005500035070744554014513240c0d0701c940d1241c00e000603001d403840003804100c2c4040005010b02c0d088040700c1089a1010180c1000400c4031000d45000d1a02900a810808000c1069145485900c9140c01a600070035042c04030218584c10480b50742e0034516081d0080b610a002e1000d00c1d1196000d03280c0f815818103062051800e04404503100401d1030101c0c403408140d2991801c11b0101c194007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832813812 1250 832812562 832812583
    0x9100f060203070b1003081606020405090c07050610180209031203010e0906073912030911040908091212030411130b030706110c04020d0e061320061902 67
    0x34a0403031965100d601e8175182c0110f01c0064540d006c00c10103c1d0760400c080036a44111403281c0001410192201c1c0450310080007154160004000050b00c1000c0c00010400306610040942107000c5060510403404da2402801028a018a401183c0c001030f542d801d000c0c059814100000031600e960359840c01410f4881c1c10f84090f105ca008a1001c14661407141104405102e800c005800506e4481b040290b12140c0410314270840713646615441c0e0000b0036072441c8007100c1089940c045200100c40c00c001c0c144d041241c040900c40c6282903500000610140309440d4800021105101d04240501c01c0d58100403800f00b04506101001082008100e00310b00c0c25049010306464200c03160b61102c665000316603164243d02d038103521011080101038401d028030300c0f110003040701b0345003580340d4200440c0076600401c02c140c00c0c046c1c4440100040080401c072840d800a241d410500031005141c9884011080f5003110b41000e0b12440405100b60302c41d20116043d10600c240c12a158051202009403120a5440e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832815062 1250 832813812 832813823
    0x1406040c0620122115130c09060503040204140928120513080a03170c130509060a1208040302030c01020601030b04080d0b1f0306050f0a0e090c180708060402120609100f06020307 78
    0x203400b408030a0261103101c50b081f83c00d4684007012820064140d406400c010400c0764001d071510f20a2209480364095036004a103440010b0602d411111143e0f07400c1c24201c0d241510024008042401064403680c1b50382440e40d05040403580d0b41690030020580125541100380070341b1410440204040d030095a01030a1101c3c0b0040100d151206250060244240600ca0841e034005100500c01c916015034020b811410003048000f280f036a40360900b03103280d81640141d6130a4004035080055080501c41d55544038000d2001d030a0f150304641d2540c5503110082c2c005010501d0206c1c030480e544040b54418640c00c0720040c071240d280e001c40b2040102d803d03411085c00e0006400c00a0010312800e03e02010410410010081d51101c1e040802c941c50120004080400d2841100b80111160b12007039500ea20b44c142c02c152001580c501220040c00d580d001406540c000d0b4810040202c0c0e100c68072a0700c540041c0101d4180d021525080e05541c80760401c3e4011500600b20800001501030300040100101403141 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832816312 1250 832815062 832815079
    0x50303070801091107170d060f1d0408030a020307032c0f030c0d0806030703020621220303090c0b03010b04061e0c02010c1406040c0620122115 63
    0xd08540c3d0503502c1800440c400c0c2e910512004001070304405000040c400c1d40c0804506242154240e40305881ca1070380804840c0440c0346081c09111000001d001c81d148001c4122005410640d030340301171520000b441078000c0f03035000c804148018440e4004d00c20404820003e1418180002c07005094891100618900303803045803a582881e060100540f064010810f01403c2c09801a01c0c0545036000000e15a41d81802107403400300042c0d0394440038000c00303003a0300d00c0c1c01300000c90125030701d0718524050600c074403925203010552000f0800c11151421203030b16140124a520007850000b80350130325500300c4d20301100c01100100e81d00800d00d01078000c5800950310480d543c158145c11001c01e0003000088030004040c100c0e42c00165020307440401d00248100e842c0d421401800010030b04003e016101103812540010003003044d0750340000c144030b04034003010700d80e000081500c40c91030b0303102d85a0740c0b0590102c10118034140c80c4402043c2000d0402c0541130b00101c01d1400e1410078111030161020148501e040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832817562 1250 832816312 832816319
    0x21e040f0501211a101d010f0b0f070f0302030904060f0305030706150306060617061903020906010c05030c070305070b040b0405090c0c0109050c041d061302041404050303070801 78
    0x460180c18100c4041035074a403800c034054143e0360522103202000f41c4505034900805080380242c818058400c8080c0c0c0c01d2502c1c900d00700801c03080b044401880d003030b00c5030104c1c00041c400710b54483d070f1a00071210452070340c03551040c6000020185010308900900b411a105149006050b0088001c142d144000c0790100301080c5c507000780150104c1c0364040500640d10034844080000c0c680d03448460303901c1039040005204d558076a280303002e5035226080400014100303100d0840d03505803600300341d400c90b00855003c48001444072210340341074440d12001c2d20410700d001c003007840c036405010020807580d04141541d07501e038500c40e01e0b00e55800da0f80c841240c5620400c41e0004d031455800c0f00ba05c050380c950f10704943c5094545800c021340303003001803e0040001000c004a00c0b00040911402401a2181014000d00310b000d400b00011900703080c00c4003074844a03003129540c904502050080d0f000d44c0800540a4050740c0f8004a4002c10174280d641d5521452141030005010b8000055403203015507980b01081c0f60789 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832818812 1250 832817562 832817591
    0x60b040c0207210303061703070303140138070501050115050a1b02062703061f062006010605360d030311040906050310050f22021e04 59
    0x40b4450f0700501074441804241d00002c2d801802e46860191a01080071611007506604003103c14401d04000d502c00620f000c101034043c05a421087c43c140e450480d117603d0004040381e0b001a4015404c4041c0281d200090b030710304004d03013482d10028924a80742d2203003250302c1c1250081c83c00f0701500c080340c104002035504461084088a00300034003980d03044000151a1109a0708040300d01007264410302c10f02201d502c6001e10040984400801141e000600d00030100b8942081e002034000303411030411600800510000d0b1541904440d01c514024990100d1110070b00a07103002098002550700506000260345036001d8051708104400400b643d005040d201c0010019417540000c01c4000c4504600065091801c071130510384444c040e00b808102980a5004040590f10641080100d150b5440091003641020031034011076041c2c185041000703007840700c0000040a03004000c0e100c8086c5030307001d0385280400310600340308096018008190501c050309040e911442c41038000d6005034a002d00c8820300c41c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832820062 1250 832818812 832818823
    0x12021e03130b0412120e03030712030b0102072304020408100b2707050c031b0706020c040e061308040902120103060b030105040b2e0e0106021e070909020409020904060b040c02 77
    0x40d018100c0c8204d9401030340ea54032154040150890900a000071740c2c0820b03450a00040821603c04c0030800ea450800f03290160480f44880b6206045601030b8005010301042004004601800304034007441c901e4074000054041e00c035a81182040c7d020b111300805110751b840c0c00c841420303082100e580b2072108003203c03c446851a280840c5441c01c0354403002c2403d0740c1c0140010322501d81300d8801e4a107000b00d110070180992120404a00d0154012001001a2941800036221801d011107051115074054948141c5c4ca03400070b040105c224003060019400c1000f80e208540c02440b034920150746404500c2c040320090386003407105540c80c1d81030011140740c6144c18032a05100f01e40c010401c00860720790a40a09a1810001048007001510b44d121801e00b4400c0301100010052140c44091541c14024001c0c1000011090120810082c030132142482c40041048815121042d40000e110542800005d019102251000e0340002c4110280300500c5103640181c0c0036100d003a41e00740180410800226505d0303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 832821312 1250 832820062 832820069
    0x110d060f23010f121d10090c09050c04180606081302060304030c11040905033403180e1302010f0906120f06030b0915070f0c12021e03130b04 62
    0x99051803012040c1d5030055419103800f03903d40c40c0240c00920714844034000c0710700516084042e020ba426064007034034010402e0940807219958180500142075550000d50013042c01907500e450b403698001440f81c8000816100103100c204541020387c9880409000181760354010007001448041c00150038000514440c1c581c117601401d0b051551340c0e80d0300c0c2211b1003031920804840c0280c641907924a01c1e616400742020f01350044001e03590b5500480d00c0c0031940d1951a00042c648050540e0181000e120a40000e00c1c598140c00c1a00020b16801e405002501c0160041c400d10131252007880070720f003000c01c00141068403c0c5c0303504404c02c80d500303001d90303850380b1a00c1914001512101082a0018290000420030b0741d9000082a459203076030390640c10800c211488c5025034002d541600340316003040c1e01d20350009801d0a003101f445880083c0208100034900024021000d1a4440d03440e15200300889540340440000b09000b080e96641090307200d81c0921407600e00c46c104c0c540c020582080250031034044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 832822562 1250 832821312 832821359
    0x5030705030a0e01060503011a0306100521010f1a0f0405010e24060301140108010e0907030b09190c0503101a0f03150f0604062115110d060f 62
    0x4596a1503201400303090034001e40d0f034071552504400030340f94800740201045482440c8064221103441000e242c50508001c00b000404410342004201980310310f03440342104407440c0100034038040340c0c0e070455007d09030702001c071045c0b01c1c42c06a0340c0c851011034000311070840030100d070340e1a00c0d00015000c2000340e072001e010b8038034116565004102c1580d03030803424841480c0749102c4081c0b071140440004006030401d91000b8030408211114085640c4d0141030180500045002040c00c0e050400c40301d43c0e82c000c10302004002d1030f104c0010404d040010812034200c50988140b00035032030085e10b8028100052445214024030900c040410074041d81e001b80318100700050b03c441546000401001560000c2659050301402003400c0c0b40100a105c042c001c2c030074449056035082d0780c03c1480074032044905680c800000940300b03070107410110008030b4012072115042808030002c000d406c103448009000781c246401000301f0000350f8092902d166000107003114000a001845250f0b00d40c1042e00492880103134500303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 832823812 1250 832822562 832822567
    0xc2406030d0305060a03020411090108010b0703020316020109030609030309060e0c0f061b060106050307020c040b010203120a15030f05060a0902010203030a090512070f1b27090b13060c05030705 85
    0xa02510039400365078050002840b17046030036560340106085561010341c0c0411032200060100d02546c01402c1980180f500044c41e501d85041910007c0d00c03805840d9079542e00d080c072a000e550a582c8281007210286800c00003c01c01100b10385000b8005198030031045409038140240b4070143c1202042d9803000b003001400b26441040e01c03034200242d60b8403002401d906e08000310852250410100700d06406807600b80c5800341c0d41d0500040207441c000b05406110f02c2a402c01400703443c1640d020054542008890394034100f1070300d4550003100904040c0000362004800300c00c0000501024407090000a801442a10120384640321048155022014083e001d80e000300007140c4407d1540c2d000c6800d1501500644200d041040b85035880c0b0351000e4010b9604c40a07141ea10424090151011044c0700400000c010110b07151510745110582c0300d00b171a22044800d07400d44802e110305030300040502a801111410f0300c4c40c158001e0303555000040d2094070214a041807514905005008407402111750b41c58460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 832825062 1250 832823812 832823833
    0x70b060108011a030c0d0203090615040203010b090402090f03030a05070b130807030f0203070b0f250e0f030a0b0703021306030903021507020109050708071d04020604030204020703140c240603 84
    0xa41c41d0340081c5c29444010010450001c0b5042c05101440c00362070807a003d0082810a41c1080c25295420802c0c184103c4c07040004000c2c3c07213100d500315042c69200b55809a00e4420b4900001c040c642c00d42c01c480c1d090300000421000407030784480108091441460070f01074944844800d05441895101c005001850400c507281c042401102d03000400790300e520481c0d2401d4290f54440310b09010985045240620100511140002d1400c0c1c0070158030081c0080300000040e060001d0038210050f640302e000e80d41c020010b980f90748003444103810050f00001818614100158000c00035800942e00c1e0b40034280c0c07103e01050040c031038002c08a51035015070003400400010340c102a507103e40500704805542d078441c40390000890500041c401030030300704007400b000c91500000c80b080e0038980c80f020044820b0b207020400103a8580080c1c40c01d0741d4064500685550291401790f03071440061581842000300805c40c12120080016940b140c4410150740700d059030100302c403020524005903601d0364590812015071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 832826312 1250 832825062 832825109
    0x803030103110d170403030f030b1f230301140603010e010e0a180f051011040e040309360b0603180c1c05010c0903033c05070b06010801 60
    0x2444203000c000c0c01a08200440c4d914080b0800c20030100c158080300124080042c150003c04000030000c1034181800451050706c00580d844200302e8001ca03a0130600c48841c00d10034411036490380c141e0940210002a010000d003d030050f60400d215080e4101034a00300b112481c28450142c03812185060b5011031240d00b09049040c180100074518610030303681e04443d0280c030f081c0c8403404021303a000c0c04118020305403509000b0300b400c1e518544212801c0c00d001c0c03580030b0325500108403000c65845104820003910b40e0b20b0120b440c0c010641c480202400c149503220b811310b104400c41c1c16000b40900c14481c1c3d04c3c000c8070100095460183d00940e100c41c05200007041200b00c0106041d40c0c082c1d13541683c0500032410f00058040c115624030002d05019280a00104102407044d41c100d2511810480412031655a008150f904001e400303600c25440c070700d9416800045c4a40040760030342d0142c41d07686100b052040080250700700709816a5904502c10100f54194011146281a1075880006c0d0400d415a490803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 832827562 1250 832826312 832826333
    0x90c0501020a080a110c0a0311040b0a18150f0305031c0b010819110307030b0909070b16060e070b1c0e1216060e0a0c0603020906030a110913061e0803030103 69
    0x406840c01485004c100c1b0381c4d5650050006188282a080c00c10420310040c40700302c03640410780c81d0003170711419030030f01101820f46000c4045800c122030105000b641d980d080c560740710706a409a1040e04071100017008108000c8040d1007a030b40013031a800c0f0140e001c02401c40599429425082c081038080000c1041c141c941115040301c00200c07600412421034065547c021940210380c07540c00280e4030030000b03800e40f900c2204d00c0d41140741c0d07000414505051030400c50180c8900c03626101050520780e0b01e0b00400103e030300082c100912000a03298481d03990a20650030307a0020381d105005c1d00201c9441b001b40b0880344a4100c4240c5520001d107481162503030030016030341c0710708001040a035011490100107180b50040700c03022101e0002030940d40d445850811001d600726040101450300601c02108907840c0d410640c1c0e842000c4010100b21745521a40300c1c0e07010b03c06c1c00d040d10703004046a90349115031880760304600100c6015040ca05c1d4801c411100300ea0400f250781c02190900d800400042003c11b945042c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 832828812 1250 832827562 832827587
    0x7030b010e090a020c06090706090e1509220602181c0303051b0d06060f05120402040203060a09090f030f050703080c030a06050a061d06120f0721090c0501020a080a 72
    0x1005281980092400c2d143c4641256030147c40c2d03114a0041c499241e2004001c0010b000d00e0640d07142c0342c28510550481d02c1e4440c881d060203840703060001010540a20000d1015240d0040d460011480b24248900070394000c200074215039245644a4505045c00c840111a10079503151400c2491003659048014001c040e01d1504164886100d009040f416140245150314031400e00080c1549402c1011b40650848000307402481021710990b2001030034103000f10383c000c0d0304807001a1f03a40d42d450b0009036504c05541100324a540703481000c2d0704000e091100c0051003402034446a8444050b82340480365849500030050020300e040b808100c03850100c2e0007079500030b4503072035001c5580d60b194008030741100e126500c40700004503140c0703c0e40c10004036003910706c280c0603003034420600d0b01000610f00c61210102802c4581c880c428500080e4a181c4a40810460701070350328002c040d400418548013020300904202030321a008040300c0058190300010394090b47e182c0c0300e100d59013403c5007014107603030b2052180c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 832830062 1250 832828812 832828831
    0x140f03070e03030c011503060509031603050a03020f030f041b1d06030c06030f0711010b330c1b0418031d131a120c040b04060b04030f020907030b010e09 67
    0x85034a95102c0203000da0110000f031b0032030307007440d05103581001016a00090020001c0c1c0c0c0042140d9000d41416505d104030458060506544e01c52940e00110001d10070104c0381e4042000100610003d007603c041518002c90044820400a40048594a40100652285541002c050814800e131200c4a10f08103a100600806a07284e40455501040b07840e40100c0e2480042c00c480c40808c40e00076044142a22902042c00081008580c240013244110220920070508050500e04a56540064260841046980a80180d16001d0b11159196248001e400700d01c48002c0c2d8092000b282d061030712420304403179110410090500b0050b24207641c0c2c080c504c0d1450780004201d11014000c1c0e00c0d6927020748012030714042c00041c0403925640c3c00303450800c041c1c2c240b0700c142840621844900300008101e40305420480d00010038980b0000001d00400040e800a00c541c00042000800d009400100310103490007500d18022954801004031304596102014a0206074040a400d0b081c0c1400001141d1028804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 832831312 1250 832830062 832830067
    0xe0309151204030201090c060e0d0201050d0b120f0d0c150c05070f0515340c050f030702010306210b0a02070605040c0f0b0705061902090604080a03140f03070e0303 72
    0x1011a101d1a508a60640160791503646000c1085040014031006011314a44207208215a40000d07242100d5550040c1c100000400c18000325900d1358001c6101000c01011562000e18552501e070321100414038000c000d000701d45c0307103401c02401407091002e2181c1c018400380080280b803811000800900003a5810804280280c0c2d00140400709040c001c80e005100400e0810b50020820300e00c803000801000c51103900c4038103035540d100c1c1c4810500c030707481c00100e0025000303040714004c944030090b0060103041c500c1040d61030422060701100501506000303990602c8800d8803145402681107440259405004060301c1c0c28020402c481402900462401c43c0903103000c0541e01c0d40340c06d031442030754140c1e1140e0f0855401c01013000c50355420780041200a99990a2019945900ea250070000b488582c03c92030114030f500c6042015030488681c18802003015480d070f9150b00c0c01c10703070351304509408034042807400800100402d00ca00503291003903039200c40745207103680b2031604403a044810452941c052009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 832832562 1250 832831312 832831327
    0xb0a021c0e030a060b030c010905030316030e060706020c06011403121e040806070801140105071b030203010c0203030907060c0f06090c0918060b100219080d140601030f0e030915 78
    0x14012815804c0c01480702050b0381d0f1151040604190030034103021f043c0080c5450070000c0d80c40210942e1150019999600170580e180c0c01d0644615901034031490340800002880010080d16074060f11641c0312903000c9421982e2501d02c0e80d030001d41c2290659a15a1000c0380c50b244003401c4000420301441e80b0813004504524542074510640c120350440c1802e80c01c54030030030404603446000c2034014410140c41c1403a69011800203440b0348520131300a400e40016036917154003200c40b50280001582d01400801c45105c10176402900c0b90130583e410303613141c010010001071181c4501d400d401e8aa4000d5012601c07088240d49203c014007000504880000c640305c400204040c030782c890408411201e2804110402d11807800c5070032580095036842c4030780e540144198119500107080b0300000703e02d40b480c01201d80c5070f0410140703030301440500c00360350340c2001e40408503603413030010701344c0130f04000c0c1c070180088441c662103071b41a41c02c00350baa001254018403011070240345c04885240002609001c0901d031809 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 832833812 1250 832832562 832832569
    0x307171302010f020721020111030c16060206190c020c040c1d090c03010e0402120102030901150b21060613080c1f080c03040305090904030c03090b0a021c0e 69
    0x400311000400e580d40a1001825940c1001184184100314805400000e05000c40070f0a030350802142e48914800c09106c16045900420340c0e0092500c0740001c0342c0d100c44801da80182d0b6614681547c00300d514206c0e00000f045400003408034082c02c5c1106902c003510705c15002c00001842c04100d00030442c8100314040000351504c6c800c640880589544001100319040200c40d00400b00c0d610980c0140303200030400081e0b1480c8000e0b6815100409400d00c0c5903216400000c00d0160b50100c1008103500c0001031001d8108158400c5d18292040b452400200c0d90b11400403c590040100c0300840362070340f4400100859a103092940e000e0750003404607003440485400003210800303c0d0024141680f0040c440b440300d2a018045841c820b051a46002080000c81d400404401000c0c20041e03000c5404404103080602600c1a80e20044010346046030b0b602d0305040040050412707050503400700328165400300d4825868070840c5d000c21891340040400107010031602103403503488441d141c1000406c514103e0241d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 832835062 1250 832833812 832833857
    0x5040611031e071b060506010201060e0108070f060e090f043e060405010504180207021002030307080a0204051018030506131202070e0609131e1a04050705060307 71
    0x9550b50303020b034040c00b107904070082c41c400058440c0701807002155860307490302e400b05039000e8a41d0303000a011500351104d10041c0d000d401180c00c000181d407882000810030550004050045540305652030030142e41e1107605031904410304850b1074010240800180300c5284045005410520858007140420b00480c100c01c200c1e40c0495517610b44c0315145005030b030580d0590b003010712040800c44d011450580750a0000c1c0c181d1081b8410030501c90b80030000c1411802d0381c0d80c15110302903006003098580102c0d5907402501da500803200640801d00d40c9012591002d118800d031415510054180d500d034102170b0300c0c1030b03030b020300d2b4504620b40c00c01c440c810120004101348030b4a400380c21800e140c14000300c400c1c901210881600c0b00403008651000c90104400a03840c040b0b40c1c2c00c18010780b01e2003100c0d00c5002a000541c0e690040142c80484040354945900551013140c1c0d40103800758101241c154440d03242c1041030301c025180642503500c50318040c0300c0d1346000c2c4020768101c6240e041a1400c0c1241d81420a040d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 832836312 1250 832835062 832835071
    0xa02061c06050612160309080a1110060302150715060608220506010605030405160621180803061c03020d12052412060103140d14030a0504061103 64
    0x14200160006466098010280a0002242d0b40303030400507490203141310742c0340041c0208814040000b50315481c6009601c4850b0312504051319580e501d0680001500440320804007040700c1c031803403891410150702c5100e42c400340d81d40180502e0039022000c60134103440d00030113400d07900078079000c0340c01d50380c0c444620501e401072501e600c4a807114a070028a0006004c5003d51500d0307000c48169451703001540200d40281500c101d424200d0f200d0711030741042840c004a001c9010788601e05400301007541074100f031714000c0d4042d5402c11100600581e101020541b01c582400c10200c0c2e00e8800240300080b40d91016540c8a0000b030285d000074488100161945c10445009402580200301d00c101300a03803240203945903a441c814240600d003080c58000e40c8140e0318500300b14084d038091184d6a1660340d4168000581c2c030f03500d8116113065840b81007030074040611350482c009038400c4060500015004859845841000041c542e00b540e846d000300c50003522008000702c0d181c0e90b8540031707030320131600c08405140075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 832837562 1250 832836312 832836337
    0x2090c040e0f01140d05190309151e1706060306040915020d1406010c03181d180601030c120609022806090b0405011d0301020a020a05070501090609120201020a0206 72
    0x75504d45841c5882c90410881507600441c0c0d220a0300021620001d5004040c14011101a20110b09410122268255604040500700b200314141c40308a81c080304240804100c586010b40460040300b0a890b08100844141400b013110000600701e03180920145078001c601500201312000c2642e01c4854018000005800c0c40790f004c01c4882c0201081d00c07a0050205144070401814201000007a01508803c070008040140b00b070200c845205507501c58200401800390201d50f00c00c13103030801c82c22002d0108d560210070060b0040c84030790340c3d10010350380e0b040300d40104160148a042c50300e03e64004106000a8801980f1400700c00c005031034001007140051160307003c1c4074134085128440308038881c1070381c403001c10002c082805101c40003030324084804441007404d168a60442e0f031207912654103c800c1045901d540f0100789140030390780106075103180f50b2080040d0303a071440d140e50041d14914200e0007500700240d0010018040107000a1034420f01138014011039104c050180d0004006500900ca180c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 832838812 1250 832837562 832837591
    0x203130e061311030a0b2b11090109090312060e060111011103070c140a0206040501050705070e040c05090a11030703111303110a060311121b0408011a0103051302090c040e 75
    0x240c2c5030070b8452001001c6c022030b08441c44072440000134000d01c0044400e052205070503d2294204000300f4004100044007400e0244250303940c00400d0001e1548850a9000c92189a15080c0d201032031f2159205072010342c0002c81070358031120b00468080f242030b600001e8a640e40c0700070f000111a048081c5115001a540744c0c4220545480c2405980246803029a05a400072a00000582d1030f1410b9500f078400078038015450b001301d820007500e01601ca5000203007800e11441403006100181c00c01c1e0301a01d6069131044240d031101d9402c1002c90700000d1f4000e500201c02e0004c184200e1080d088440101442980c840c100080c400e403618008469030301c2125001002100c254040c1070040244000b0b2859080402c81e1101c21650b1031280c5c4181d1501540d07a00c140300010307001095222101046003102c10781991110340300c400c094024901304102002c02610060444040d40c404d00031144910700003048403009503215803e01440da000039004006141040c400402c5120404606602c0340070324030070002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 832840062 1250 832838812 832838821
    0x20d06060b130602030a020a060c140d0c0206060303070c0b090d0b070c050d0201091a04082b050f04020d02040f0f090305090f030c0105070f15020a020309100203130e06131103 77
    0x45140343d00c0a404d5420a0044620881e008a401102c0700d0b0012004031f0a040c60000c121640720701e40355a0720354654080b5000c58a0400e170b0303020080c10b072440e0b001c132060340e01c41e24201030b0349004402d002004180202401e1010300c141801a045a040190040804d03444503920f48a00700c5040341d1200c0050301842e800750a20404210411131825540000c100c0c89100b5102c00d107011458210441c0005c0420000c00c040003811400c690007030610615207806500c601c20b9880c040091204684540e03802e00003c644807808020400d0700861b07001340013100406081d405e002c05064520b9000c500703190340d02c40c4c80241103514010034003003a00c2130b0382d91941e903412042080300c2e4640340701086000b94081e0344c00401a903000401ca0301d6183c0c2110100720a00a54501000040d220710301d18112140041042419240c000000d040c42d08021201004c0c40502290203d81d030340070f03000c1d14000340c0203000c2d4104140600d030310080e500100c1c082c0142d140d526502d51a2810f541c1040101c13640800c0000422 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 832841312 1250 832840062 832840087
    0xc010c0905010305070e0f0a0b0c03180f0117100305010614090a06060f1d1512060d0b0613200403120923040f0f0b01030c050c19020d06060b 62
    0x340090082400d040150b4140100000c0407036002e6400680202d000e0003513100300d41d5032080028014003480246a81d146030070502c83e902e07901715800001c81c035400400b02c44818504403a0002d54042d06950310940c00c815005600c407441c00c00b50140c04c1e602e404500220115900f0b0107002d000d4250741001800c41e0002000b070110001c0000c040440300c0d4038040c400d00090798003240040c1e4105e014540b55404c0103440d007440d242d07404001d4104da07208a00740007104107a44203001402c00070000b199661810b5488505010480c6090507004012995102c0000c5540c50b040d1140d000348644114000303881c01c01c0410402012030089401e00045001103010802c001c0e004143d60380300e03036a034605901000d140003c035903003594940c0c05128510707103a685444c8440d1100c2e031100392411000c41d4107202844d405200140180400c2007541e0000342402d40c008001c50040b4201c41c400360704e1000070828070a400300485c018010701c5608a84c130a929124040200303103107004900243c900c051449941e400f510400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 832842562 1250 832841312 832841327
    0x201050613060e0c0f040806090606130b090a110904021b060106090e062b0c0e06041503020405220303050a0b09040807170903010e0f010513120e040902060c010c 71
    0x102481c03410014103100c00100e6140345030308101102c001580b20a50340702c200b2454000ca40000c002c5100d01004c0210381c0a001900500554040c0c2d141410150302d15189800e640303c880409410850403000724100d1032081d0300c9180d044c5030701c01900307003023440c6400054207aa100d01a101646c0c03034603201107103640c0d2040c014603006144500b422101c29244c20913410003c00c008107100c1c4100070150041411340800c01031200e0420454028007c41100d40c90060020a100d00601108540c0000043e1444c00c052041411140d042c003410428145103500b000060f090007032030588031180340380d20b041c00180384000e101100ca1091310045114039200301d400381120303a41111180301d40d00f038a0900c00450708060440b0010f90300321910200d10491b00c0b10b11000c612070382141a400d503180c45540e01d84254081540050b14003194020b004588a869413a2000c80050340c4c0a07207410052070905042901441c0004812240503101103083c0407260006041d942040b2590304040c0d4440d41e02c050303003a5020300c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 832843812 1250 832842562 832842589
    0x30302120604140403030207051501180c0305060a120203190c08060a020f0708131a07030e030102070203030913061d160f1b0f05070f1e03031202180d0302010506 71
    0x3801c0041c404007450f030350807001024101400703240d030002e500b2081c044140100780c0a03021f01040b00c011035950b20104800c80000d03ca4010344507103450a001da10368400c1c003c090003440002c1c40c0305512401e01410043c814017420341242e1500c2400400c0c070304a140c070328a10450b240103940701c0001603d480d0382c150034400001c080880540c810420003000c5202182907810303150f000400b054480f1b40320f1907142a4180d40380c001000da10710400c0f1184c100c05803900208000c1d4420b80e40c031441280410b0615090f40223032940203505170028040070804d800c2602e11301028108004000c107d0a6443d90003544030401c0b0031120914411000c02c00c05003030046100c044202d000385c50001da07074410f0303644000c04840d030400854810080012100c418003034031b210000c411030f80103000c0d40c14240d5a1500d80c102a55944281c40889241011b00190030203851a4181200e4050715481e910b0000150214000e500c4114005120f0013901c07580c116035102c0038018050715100790000252428140108100c00c0410b0b030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 832845062 1250 832843812 832843819
    0x3021b0c030f0604080711030f100c030f050408041521060923190b060c0307020f0102031c0f0905010e0c012c0d060e0d0225060819180303021206 64
    0x10f0601c40002d002c0811118095040351201c5800a51040068200249002950214424a24080c0307800f6080c0c0d1041000200360b460801003100800c440605655003100c0150508409020400c10024608581000a949458903402d003040b20b45201c58035803040242c3c1d9150303a691708010302c09145a88603400034000c070401c003541c1300f0041140346c20140c41d0050416240a50841c01c05404884a03000f0590b40e18000b042251071b40f514010440c1e40c0e41180001341e12520070041200010350011045910840d00c4009540344c46850035404800f17400351040005a0640d141c2d03120300400e10030300c170703031084d0300d94003400b6040c0e284902c0d000400748229565050304581e50030707448290b102c3e91070908000e0b00c0c0307090b40c4285400b441ca091100040016962103003031401101c0703101071220b50100d41c0c8000010500110340c2107078017118000142009600801010407064008603e0b1130a1052000c48400340a42012603071403051030402d51414a410811008282c01180314028005403809040e4400c070184e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 832846312 1250 832845062 832845073
    0x9012004030218061c0c0f091e06030f290a090605060405060607020909030702061b0714060901030b0307090c0e0102100c020d120b190e0a05040b1603021b0c030f 71
    0x1800011580c1044e4802091400c1c1c01080d20410019251061b07401402c10382d00c03007903500e40e80c0e40c0d1000c050100307c0030320a080e0a40301902d0038807023558400c0c102620341086840a490304940d481c01c103400c4040f940040702209092241c1a156142c803900d40c800c0184c07440c040341c2d1030388601d03103030041e600081d00c1c69103d20705000421002d80c0303440040e9500e0b1501111081c019840c1c11f61078604600c0341b80b0000e900810002820b40807a41504500c00c1c07074150300000c0750040c41d42c1700006030340c9465a12145a01c82d070100076580c1d003988603400202c03c0c59001030964408540d1144100200c803a0844140c020542e40031560a5941e010b101a803861003080d80c0620440f0b9180030003d450307451408034034040c049010f004201101040d44140640400036214a000c507100080c0658480702506c105410340c0d40034800621740b01d6050140038001d542c0b102000c0c200c0e848888808018901e40c0b01d03040700b0198280540700c044103205425128241400000d00340c8403181030189420b20155503c03890295100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 832847562 1250 832846312 832846321
    0x20d0906051825050415030b01080102030c030114010e04051614030f010b0a0908150a0c170a020904020d05100609060c1e11030d0f181d09012004030218 67
    0x4a000554a840c066074020b40c51107103c10001e0806031604096000b601e84041c01208504175214001035034054110103c80f6030380e030440300e800d034442100d401c048000c0504c01001194110211402030801c141001b07007142101038080390880748200c82c0c90b0a50b002451183c0b80180c3c1141c1442c0150985136540c91440c904808440e4140c9810700c206800200700041144030b0703d101c1c03c0194040e2030a0400c0e58a00d01d000146443c0042066802c1c103081890030240d106114051054034810300c0a0100c0c81490751343d0980d40303030001e40221920341d400c40d0702002040800450340c410903210b410058004403c60f410000003c0481c009504100c0900c00f00001c0000800c40c4800c1501060b884001c210800343e20f1850320b586440f10408001c0d030540b00d9818503459103a04503003038281c00183d541e00c8140101e0402038000e8020300500c2a902c071012205410500d807042c00c0350a0768407202100c0081303001c20007003e03100640d0040c5220f4030403400c000b2600344110b00e0141000c0286141e1a0307600800c5060 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 832848812 1250 832847562 832847611
    0x70b010e070f17060a030b04060632010c02130e031c020903191a0c03090c0105091c0c080303040f0b060603070e0d050708030c030d061706040215040801020d090605 72
    0x120f02a20540003014800003d81c1c940e20019014040c40d4400d2410350141480d10b081000380c00c480c05a1145900c00142040380f15058000f03162100034115842e5505008020054488241450050340c00c0407100480754101c002900405c03611007a9000250742d10710b01c8000b0342c00807030201d040100945004121511240c0e80000b400c2c5400a0711a02c44d40e802440c41c5001c000c0d07803000c0c802e20643c13522042d00308a200131684c0051032050503d001964881c0c0749250044a0900ca0411020b602c404008504803007039000d0103030030001c3ca00c60300115811a1b16000710910b141c1045500b191011020100070080100411f41681c12201c16200d250860529510180089900709071490007805100e00f0399042c000208960401014100203682d0790b8050b9107040d40d01ca60042d00020b00660414000040310b4001400c40400c0090020142c40d8544030381d820011102000d04281c1010b440601020511070428030007000441c88410000611460307c0c50030005445008204c4035017a222450400744007070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 832850062 1250 832848812 832848827
    0xc011103090f0907050d0908120f0c0415090308070c1508040f0618061d150912031e010f140607030c12020a140303040c21080f040308070b010e070f 65
    0x2e20440710400303181d440c000201c031540103008410700c2c4142442c6420060156500080c152041c407011f01040030741c0d4208416070103c0307058078181480c6408100c01c101d0a501c80311000003004c03041c034103110403581c3e0341c40f8415030b0b03000046e050750300c110020010054200c0d4000a04440c0c0618104942c144c60541c41e604221680300101030021038851502450860a24100c40901a4024170422803510268408410000c04001d0340507144207410a130441c001d07400c24400d10a0f4500c100400804c510030496a4041d000a0621032440759000c818114025035a0351a84c040e122074000c43c24118034003000c00703d5130480c00b80c0b030500600d01044080c01103a80b240081940503005045210400e00d90b4204901d4840101c40141c407110700e11580d0002c80c03101100850181e0301914a40300601d0302e83c0000c2c4100380318121120010321ba400d002c1000038400d038026002030400e2000c903d06040e50783d22210000d038001c01d004c032101c80c101c4005101009030b2100c5250420f0f45460480020103d00c4409406030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 832851312 1250 832850062 832850089
    0xf20030d0e2802370909081e040803030403030b0102011112060118080a15050c040e18011d0105091b060a030207060906090f120f1407230c01110309 65
    0x10400034071100299107444c038041d440c6503544030315400f469400d450f4881022000041241d507910030134a00052038090740c021001c1c00f5070020402032410720307400318842c07600742010079041500e0000c1c03100295200341030014610542c0681c80106d281c0c03809500090848540e08905050768070180680340862080f160041d030b0014080c24242c506150600818280a083d40e100d8201da00c122800101001010184082a60300e00c2e41c0c01d01c469200c00303980845070b0242d402184c034411240c0c00061080b2610b40f00c00c820044042000040c2014260803400814041d05080030f07150b07448e41e080c03100c0d03000c0402002c450a026404849452400c1400107001407289501007400c06401194a01c20b01c4120360140e00b00582c00a0204190481440c00f10b1a40030300d480e0a4480c4520182e10382941401000307000d50904480d511038201c860186500360503908100020385100004458544000610b0710008042c005440010090661124001081e61046a1000180c2d400600ca2040640c84024a00740d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 832852562 1250 832851312 832851373
    0xa0206091203071d0310091b0e2202040203100810060b3f04031206080c100c050a030207080708070806060d1a0408040f050907020a030f20030d0e 64
    0x80158139507540941000e05102a900d406041109000f1b501e9550106050b54400c048004030010b50030000a101c0c41d02e481816078145e1490000b0f0801c62140d4a141000d20701c461140c400e60460b1f030082400c9810031600c02012020b51a024030240030b00304481070303180341c405900784070090074814a4945809030f541480449203042803200c005020705041c0084851400324054118003000c0c10ba4001103900b40c4060b0086108100d4504103007000f8010401550000c40040a144404005000d040d1810500712001c20483d9a000c40c0000c000748010360402d0301a0340205950b0741449103c0d0b08003d050360214041e5400490100312849000c136140b0740c4188103e8111403114240c0c14945607040c100c03400c0b044890017070001c120800030540090400d4404051512120903155428400540810345100300540e0104129500080c0b0401c3c90749444d07001490040e440038140400f83d201c40f9800e80308070200340c02c04a403c004682d03071840f6500f002c04c4190001d0001400a0328445408401c0c4a6017224 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 832853812 1250 832852562 832852577
    0x603040515090f06040c06080105010c0b1512010c030501030308090a0317041b060206010303020c01050a0e210a0b0f100513020c03040b0a120f0b010909051b0f0a020609120307 77
    0xc1d041414080f01c0421010801a9a081d141c540341200e0070185d02d000701c1c0c01280d0301500100b07203548500250302e46141c0c4070400b0000ea0b02ca494007207400c409083c0c0b5083d0b0040c040c00c80380d070001801380a04c1c146203119417804107440d411403038040d040800040014481707503c89000701c40030030350004560300210040e80d03900c0700325100d07400d04020020000c03c442c5001d0040080c006040340d4005505070407079002e54203803a00d1030744007070046409209041a4170300103007409100c4289860102c0c14210910307003003179009011090b80d41d245810a11260825510300c0140000c0003600c050240046130b00524150361008070707500300340000d200210120781c402220b0794085100107007618204212409800450075040e100c14241100804003440040b03602c4409050017901c51500b0241e000b00d0040e404161150030009003086807403401002d0050904d44188800249800302c0710250000346101d560b8500360660310050340102030325025001e4801c030038543c8402c0845c0d4107052840240c2c1c0c0c012845190400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 832855062 1250 832853812 832853821
    0x5090603190611210702060c090105130509160306090902090708090709090f02030d1706060a051309060f06080f190e160f060c0c06030e1011030a06050603040515 71
    0x10000c00510030194000c3c18001000f9028010740381c2c020543d0030018070ba9000550b45e5020880c1c4401090b01e00340d111404c2030042c02c44940c055000351034450824032800c512165901c0006100c28400d903010140210410b81404059505014107406010406024090203829034042400380d040240801d0800c0040030204054810501c1807000505640c0c606001c1d079195030400020b44240910100d103e8850b0744c0903c1c1c0040d000b51001d80388240815403409981c1c0e07a410a01c51241d1088140c40e00b041002c2118820202081d01c007038001d85003030400000c8041c21318942450713104264000c0720920a070001042002440c4d844150307403111a4514042a00300c40075041c0d00a000300c2e44450314a4014403407040c40c224005910343c8100d80a03000031b803181326583c44082c4e0740c80172030940242c00e25903801014403083e0701139080301074a40701350b100701c50f040d545400220085480310301820b00504000002d011070200c841c0140b00291030103c40091460404d9590300e85c0d100440b46030384503100b01c3c031030009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 832856312 1250 832855062 832855073
    0x30301060f2c1e0307030201081f0e0a060f030f061116030e031606171803180a0902090112051b0d02031e0402030706051312050c01090509060319 64
    0x40103449460b42d4500c4034000303840045030034240400c400c6008801202018419110400403001040c0018018240c1a415900112024040109550721a01c3d0008c640e412442e180d80c1d00000401c100b43c0407040c07605042c800714041da903690b8041d1a090f800d01e4800d1010a1401003000800d903400100004d40440001c401e002c54001c9240fa0b82055a560362044140741d0031004440903008106c0984071084a1032610b16104181c1c1e0161130700159510403c48181c401450b80c8641000c005034903070245001c2d12801c149154030010700701c4107224461524080c281440e200074405801c0003e015030400f040d41d00003c01c600303011464000101d89810101d0f6180c00481181c401c0342e01c0200e80c00391f03103110445000001e03500c1a1400c0587c000034081c841c0c6006182e021190049034000d024110540c50303c80100c41e550018001d044107051340b1500042c002d104580c80003c0d85114402800b0b82d80007001c0050401c5155a21103405a685a420080310355000b28400c5600c0500b4106010680c807281420f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 832857562 1250 832856312 832856327
    0x45180a2a0902040605090a05270901020405041506090b0a0c080a1224050303030103080703050307030b42160809150304050f0f0304120f06050a02040f08070503030301060f 75
    0xa0101d80b440040c01080440e4000003d0401032020303601ea10b041a901c41c10b102c0350340c1507a882011404445511032102c407070080c100c1d5170850307584030015082c55183c200242c1141d40e0060910300c401c5140104004564105c01404000d200c0210340605000a030040a040c0c40703000341e80105803010004040300b0301130082c0b001080d14542a0b200300114800000d400035208035503442454280a40d807070000e5145000030869068a500038902421303c01c0c01c0e0380c01c0e91a0f400103804203061503207410703001c7c8a50305c0d0700180f12440a2005010050046081081c200311884101c43c00520302c0800711000c08410309201f02d920000103040910410401810100054005c0c2c5a206601c01011001c0361140010000614000c41c00791007503407a25400c0c801e400b56240025039a01c2125081403104200100c02c07195021182801140710301c48040c0669a02c4084800032038031030004da68081420700500b454180b0340320184c004a40141105c03410840000c1daa400305201d64420890ba0002d0140300300e215018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 832858812 1250 832857562 832857569
    0x1050304081b031305121005060a0905040f020108070e010c0201050d020927010f0e0f04172206050403050307060b030c120304030201030b040203010545180a2a 70
    0x111000c0185861070120f440c3c2d403000c54960007039404260082103614111149401c440f000a004000c000c410b041240d000e88002880103602540c4200005403240003030140c940305038820100103203c02c441d48000350420350040c0046c820401400280710440c0d8012655404003502428110f0300c030700d5004c610034040c0c81401c031455000720b24000c1502e80142ca1a07129040000c1c107568100141e031702d840180d100091305121f5131424400e140007003108090010072164100c4c0c0903201c41c6501c0c0303001c6684c00041d5845445a9413220000001a030f4800e96039149040103440d0503d03206140901d9519001d64a00034600d020704000c1e581d010030407090740d041185940b8010090044041000003414407070b00c031381181c4026800f01707003041c00701006440c0a00c02c0f0390698800615026050b00400f6066403c441950170003041aa006540300c00213407940a009031125080c02502c03180f074905000000b0750302180024071070703240e401400404000740ac10144811191800b24203040a140020842400d000c00f5a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 832860062 1250 832858812 832858837
    0x9050c0928090915051e0103120c0c0b0306031501080c01031d0d0809012a0c030e1f02070803030402100c1b03060c030c0c21110f0607170105030601050105030408 71
    0xa951040244d600381e0b910f04000701c0501001150348202d50f00e2445800044014600709420005100044c81081d02d9500ea000e00d181c104440c4140c0d40e0b0700d80403103002d6003003160200804001c0000300c0c60108001140c1080d070200c1185036516216200c0d51702d00815114030b050548032500d1600c21441105045007000110045400d0144080e0015181074001d84201d4100d508001101170078072860080905a05001d132407024031031072031150440e035022554000302d08001541412000700d5441d8049141001d20742400a84010042407010346446919480351045410610400002d60740d80d038410b49403180541030018624a051400700e803415501c036001e0010400c0d5040110a2007003581c0325240c14074564038200598035000d003050755461001500104415412000c50718804141c0008090640c40c40c20001c1039030b212940c160b402c03c0301040c03000c1804cce8000b00070406040ea0002202d541032044c14030360440d650410021036110f00701405814144a400004142041052400c135041c102614 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 832861312 1250 832860062 832860071
    0x11a100c021c211719020c12041815031412030f06010e03030316121508030a03050619060509120d0207060f050c07090e070806090709050c092809 64
    0x61030205422001d500c8043c000c03618041038600914001c2c12010001d10794082e0002c070300e07503131211819490245101d0f8a0b9038142c00b07008100881e6410480745200000d00842e2035100c5041c418013600b207400b85410b6055a90030480d200c04164030b10030b101402d0b643c005040010844414a40c0703490b00340025140d5045080000800c8400c11200030314034001c0d00b09030fa6291185d100c0004140e5680020746c1c0c0c0891030f4200e40303031f00d1401a01414800701426017000303000c18242020b001c2800c81602c99030010300f1581001803072075401d5a252150300d52100e82118000541221002209007a02090117807106102d000100a00700b41d490b03c4100020050718070885800d1a846000251200c90510032000481e42c107030302491644d030044081d500460f007850000c100e454a4081c00501815070b040c0210703080d00940174040303941d400c18802ca03482840410000c2c50250710300410182164002024050313007020601415519580d0040100c8640b05403010754184854030012144440d500c0b58003203050705107030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 832862562 1250 832861312 832861369
    0x121e080903070501050715050702010e1e0f01020408031206030106120f0308010801050702300310230901050d23070e15030a080f0705120408011a100c02 67
    0x2000100015030003030301542e6400c0d81e01c2005481c0740c0551800100300b915900c04610844481d50b11007544808035100124000f5051017440342805d50400841c038040c00c44a00e10b8075110801c00c4201c0e04821100000c52500c1d140540d110f440b4068040711054141c01c900114900303940c01d402c080d0161050031500c07001c1c0b00700d40c6484030031a413192000301c0205010724000241c0b01018465144141c2c000d402034004c1c020820311300c0362105210a080c0d4165030712040c481c50442074900166100300c1411205444a5007018022103007400c2400c9200040200b01006448545841d06842d0454206072090390200000d46001c200000d442010560000a00310368003640e038000040c00c000302ea9840780501e41d50386440d0300f140245550b080d4002d406500004d401c2000451403002884800c450010281c00d2160650340d00c2d04001c0441d0030115010000b09007403200755000c1c828501c500100b145051400f804400200b1011040850400c007440351102004042d0345401101ca4080c2c040707200d15180c480f50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 832863812 1250 832862562 832862573
    0x15040f11130509221b0b0a0210090201211116021207060c120c050a031d0d0206191b2d0c09052e0e0906040812060103060e04110415050604121e 63
    0x21051001005109d2074810381440d1203148505071489070180e4884044a48184109800e000a14140800b8030340e640c80d0700b103a0100d0745010300300d840500000107800c40791500410403900c1040941000617044444100f201d142c0100015403616480b005070001806002c106407080031004030060114007404801d9800c040d8018130400d22040841b01c0d4894034880c04090248505414500070f420a034100f01c04040003454221300340c0030504030b14042d0395034043e150000001036a03d078021560039945840d41207214a82d0341c0041071447c0d108021004100b1151128a1410345134400c01d12003175030301c10100e02070080070290071010081620b80c036441d05c0c8003001032050802c40c030b1040100c0d030011034000c2454607001040490085030881191400d10841c99125020004044c203400c1c145503507403000050603060710451a100c0c0d0300810f44080c0009400003400300b61074a4506107000c04e84140320a1000d40e5440c070a507820358080944561002c0700e00d160106445448202640841405608007410000e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 832865062 1250 832863812 832863817
    0xd300e0d050a170c0403200f090402180402010e0604060801080c0118061815020f0111031b0d0e0609070603060b07030815040f11130509221b0b 63
    0x1150201110641034200000720750034060b541e010800101240341a50404102c0040d442d0402000d594880c030702662070380c0d0ba4501000307800e680b001c260142d505c0d60181d4504031721401d03444007040c3c43d04006440d059001880c1044007582040c40070040c10081004c0d64030944000e10700d00c001600750360355161149030140c826842449801094407940780e1f0800d080d4030401206020084039800c003810141010300070307928051840c1c0034020040540e4000213526245080b54415442213801400d00741166030a1b242c251072142051481e211010001d00107000a50351280c140c002c801d82005446001d880d01c150f02030300749018100a9440351138103002c1d00b0880402c490080300c00c9a01c0170030100b69038a034041d51900803400c01902050070040002c030000070000c603250610000500000b41c1411144000c8204c0700d101d503650b8001107022031480b06581000d9240c1000e480c01b21483c02e01031078100e09445e001400e25402928035603a480011080003003000000084950b00d452808085841d01003111503038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 832866312 1250 832865062 832865081
    0x122d020319050717150a020f1605011401030803070f0507121e030c080a05070e090a0f0b0402040506030103020f010908242410090b16060e0601080d30 66
    0xe01520720000b51613100885100c00e810b041c400030b4041c00107040300302c456540c001054003c2d861b4003000315000403450070005000c0c01c060310307180ea42c0403402400c000382110303009190003084407008001400401c000c0c0055945c1308003d40b800b03054200c01030000321414012030900a01c241c040c02c11b004001c45c1c1280032507210864441c41c0704655800003008409031056254220003240e40080820300e00312040c0c0243d0360010355424105003d044010206401d100111420140b4980e5940d007035044c1c0031640203220074a4021541982000c1c00e100006401780700c10311000b445100103100341c04159002c1e42c501d000801401303090701d01950307102c0c5424081103504408102000e140000056260300101d00107190601070803409641d82c5070500c103002c10303101007070603280600200d040e0000324111803000030212010f1554501403900142d00d4100182d8000a01081d8542c11081c014080030f40006056180840035252203122300d200003c4841c0603004819280c0315441c0b02c01c0f0008840f00c1217810002c0f45 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 832867562 1250 832866312 832866323
    0x30c09140601080c0a0804022d01020c0a1a090a050603040501020301062d0e04200405100c03050f03100504020d0213241404050424122d020319 63
    0x10790360318401150710903011903080e401800244508107801d4421000c17650301900c046c041610203400d80d5210340b00c503500208503407900390b00b0750564001541e052200c010383d00425102c0310303911400c01550301d802c103845417803034500d56a01142403040b82c1d442001e82001030034003401341e075a242410700b4424042d5009015030310109404d24058103595020100804500c12080701c0d01e4003904101c0800c8074600480c903d05a40541c5450f0301910354030f0b221030005007103807200b24442d680d00e140000780040c04c00d00c1c46c034101c1800386040c0c0020210341c1080c110780343c40d0045817010760389a540c21501d815810f0960400c4e40c10034800710380701d0040886a8014158440407204001004d0f03550f9000c01441c107001120148944151403200807054028041321080d41c0030850f105051a841720042801ca8041d400280c0190000040f0641d0014100101d800500740d020040c0c0340807459501c5480b041d0401d40e0300501044c42c03040400e41d0b10703482001e503024081d40c010117840545d0310031580314030a1114140c0550b82c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 832868812 1250 832867562 832867601
    0x90e1312080a0b090f0f090c030d0f1e080c0706110441060705280c14030d050c2103061507050a0f02030a0804080d08090102160b0702010204030c09 65
    0x1c146451003840340700320b402c0c04407043c842c0c6e03500e100c9158141000e44100c9007072184400700031240c3d4052185418001d001e644400940650307840082111010023129240301c0000e444030202181e0204145078010382401020381e0320091864000020080b41b000c1802ca083e0210f40883c07030007020881100c410002c091404046403120031841c0070f080c181801a20b500c0103c0740848101e00300b100150200501580036103046603a884502e0074546c51000610550350a9100c2031002c0104403aa01130181100580b910b40c80c4400102083e50f90b03a01440c0f0005000020402605014040100000402035a0700302409520b11030f08011044e0426250399128000d080c0c82024920802804c2e00c0580e03070000000c108521150310350615250301c6071000e0341c00d4000c0c450381c20040f6030040010001400960028850f4017200c1700020100c1c14090b05414140e40100004104600022901000340340c2029144c4841d440d00c00d02a402840307a644001e20785894283c002414104079031084605841041d120007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 832870062 1250 832868812 832868831
    0x30304080d0e0c0f0f0d0507080109030f08040b01034d04110f03090f0303070206090d030603050303040201080709120c0f0902030f01140102030d050910060501020c01090e1312080a 79
    0x43e11106045482a0800034002401c1c041c2c0c035010b400003030348107400741c035015080242c0e441e82410400284c00c181d907180e444024810415600115041201c2c03482d00d00303c04035080c1580d6031a9100b0061002800c03030052101c0c42e0312002c0301c2000000503e064002d81700d4541c903090380c84090040d00c00b1030310b100c00031448a1b00b0520b824035005007070859082400562429107204455046504080c1001300288034090115006d6541000110b001c2e03d0b040d0000c00b50780c503012000501e02900020541d0800d41844c00420000f1800015250002d909080c00700140c2d8401808454a0405910023001492031300c0112b02441042c0d29039409a030b04246000107460f445600d03005c02c0e0320065070f10f543d90410030702c010844003000c05020442c80c80144162854030802683d094141c034010398242444d42c00414015015000074810b4000501080c009813810401000000e014642c5030b01c164400041490300140b980d154090300018165408260850758a224110080c0700304001c5595240c0781d440d018104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 832871312 1250 832870062 832870091
    0x22020a05120f040c0e070e01030e01150f0e010503030708070206030402190f0801110a08012304091110110c061b0604030c0c06080c090112150b0309072c0c0c030304080d 74
    0x21b00c00c4140380c40b1981c01141030001180201440300c1a03001956890048040c985258190f050084c290500c0a000c810304090725041d0088060340000d1190b03108010510000340c00c24265800c1640440d80d0584a5641d800410840c40c0c14460301c5c0065041540c0110320301f001e200603001030b01d1007203000300201c426910705003500340b16102100000c60a0f62004002c8600c140894011300380720035802d032080e1003410010805480602d00220b4141c203500f2250019820980d40b504807650f05481d20540d83c502d40580a603c81640c0300c1500e0082d01d00061280700009110f003120283c05907034040b0b07859845d10341002414203600303140443c0c1c40b012981000540b64842c001f42030182504d41003041c54804206d0045da0b40c400c1241c15804200c0d00d420b1480a21899041c3c0440184bc00221304c0d5580c1c500400080d051607660f07004201050f50364140f608801000080c1e030320360300040c8801e0440c5615080c0740380b105c034043c46c03003009501d100000400c010400c03072601a10b04000c001000348505405280311 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 832872562 1250 832871312 832871339
    0x120509300111040e0112081905091513030605100e0406020d05010f060f08270a060506031b0d0c180c030b0904022404080d05040503070522020a05120f040c 68
    0x1c458002130020014000000b1820008a500d031040500034904056410380000104000300850041800495103034058180a440b18400184143c00ba40c60402c000b401490038a90318000174141681e104005601b04000030088006010703483c01e881c00c3c0745002d1902c0c0700a0340c0020014032070070f820000001607030b1200c01600700a85003151103d25001144200c101c0c2c002c04014122a6055103c0b10405010b446850500c3d80301d00d0310401900c0c00340b400381411002d80b200503203070034003e0b8404c1d00200911180308003242c041c81003c071403e00105c10141010440c07868640c2040c8003d0303000302401101c81071140d01144c1204d031030f5141886401203a00030441d02c040f003260b001c1c1d040344100f034543c1120541e20580b00d540203940021982040e44070000145000401c01107600440ca0014050000d0b2404000c82d0009007811208480160303500e00b00c041c009840174101954064002c0f64a14016026405071400c0203e1061403180d03514000c1c0c000000100c2c29201031354198240c0780003091182c4904038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 832873812 1250 832872562 832872569
    0xa050906030706080403020c0d0302060a0e030f0a1206080726071406090a031b0314031813020909040b06090f04200f030714011b12050930011104 64
    0x604901807501c81c06513000d4000802c02c80c01c40c0504900060166a00f80c6036038801400303a8000c002a252041219044811341b00200b51168410b00002740c039084040110b03540310545207040c10040044452140280144da009101d46004503400490090000c04030b41e1864803540300c02442c00c0581c401d03a03c0d10b40080d0300070080306141c81000645641054001012003000260109800070354a80f1202d5841c03811200400340c003640b460b410024131411610f0b00403070003240409180b81c02020508880c99003950000a8001e00c1c080440c0d0608201c4c642c192289110042c014100c0345c41c1c185081e88006504a40e1180b185110001044c2c80d401c00e00500d521456000106044459541d1107940b1900030409400d03500c00c050302d804100e952018013400009162490011016000c0240050036404030002259408551159074001152003071101c100c0f220305c141802542c83d0010342c081100580c101e00b01d07000c81c00201d046800d054841003060340002007448000c1100368181955141c080c49a0321 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 832875062 1250 832873812 832873819
    0x2c0708030a02010b01090b1323040501030803180105011203030e1207060914030a1d060408010f09030e0303130308031902072a0b0301260714010f0311180102120c0c0a050906 76
    0x140700b400082e03000100c4041607944270700e4001500b1442000a000e6513401d8100300c44100000c01030022342820031041424028006009000560402003210103440b0002005000c040d1900c0c08401a10800c0c404a00071000d0042015901c000a007003141c09854440c000300e64150020036001000407001c41540c0401641ea03071148520408599464000c108203420b4a901000401000541e440700f4894003100991000020401800340c2c02c0250001ca1541480d17402034104200c034007a4407103c1300e88c07642525805031165442c0d884100c1121205010303040f041202510018884061051448661010030692905041a1142c070040d201d010072451081c05142c440a00050041c41c8011040c14900207400810101e00642142140d04e808440e5010741c2c40b280038204940c07284e5074401c00c1e4454400d0182400d200304540845c003880c9900c0765801240140210801c018a40da2007032004601c0710040c400300c140c540412040e0240c98034103100b0b159107d00349900700040c0604014049620508004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 832876312 1250 832875062 832875097
    0x2718060306270d030e060106140a0f03141e01050406080a02040504020f040221090d35100e06040e0a031b0f0602040611012c0708030a02010b01090b 65
    0x8a84078540040b000c08410b20402100d0715400503020400540e690290b540d580850345209200c60b5609016040e0001d070100b00f041d0411119a075401c004076002201a40740c800350440c5e00c00022030051590074a0041d44c440384009010b110701e011200381c061113040801140340ca0741d0324020841298014820790149070030404e5080054900307a4011a030041c0064010b100410041c80040d081344d00c9812035030fa0000d00c41c012080c081340b0a1a115502000303a00040c800e2040715103002c2c154401c440c055030316100700244101c100025010400d003240e0410b0100300f800d41010a5110640b4802d40141c107150000c11001510342c0c079190081c4516001c188001d000e8611090b1001c48581008440030355909007080b07400000510403000303184166000e0440141c945003445c0000f0065440450a0101c90b0b0400c0c146546c2e08a013104a918056204440358072580d20a1081605200065105901e180408030b104034a40742c06400441000c4403da0790608016200c180c00303200e900510240d9501500708 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 832877562 1250 832876312 832876321
    0x310e010e091614041d101401062d050d1b11030708030403080702190501020d050c07050705090a0902030307050609120703140304060f0e1e0d02031c022718060306 71
    0x90340c04440c007401040c0e840d80f05d2400104442c5d1034107011142d1074142c5a039501d85500b01c18400102d00c3d0150500e0b281203485848442c0b02800740401c0c040500718161300719040101d501e4011402c030b4410036a840000c0c008003845003851545204c0705d4030080c0124880740a040f080b05400f0045400d220340c400d9050741192160b4501b1580702c50000c192000398814a14042c0b4441c00201c3d003150290322400001d84e6070360000e4514010345d0070290071002e1741c10080c04504002000856080d05441c002d803410240c680e90640399201034403811901079007501002540b082270020116095101d8020503044071600340401251900703038031502c2d00c003600265600c92100036802c0845c0046402c18043c41001c9440c4025001110440c1d4003031070004101d030300c11001040151b00c82448040c2c10010035024007070001c580d40000e501c1e48070b40350b00c0341d480d900160005201010142d043d51034180b40c1c91042c02100b100071801000c03518040d02118403404040f2004444400e120582610401004d00507180c00e4a8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 832878812 1250 832877562 832877569
    0x9020414010806070f0516020301060b0f0304110f100e1c0b04021c02061603050d0c050c07082109060c0d09060201050f1e06031f0b0103060803310e010e091614 70
    0x21f80f4200d80c507540340c034000038000381c84502601c0514400d106650b0b0780c0c10f151400740b49060f1400503407402003003450fa15015981c1c40c2c01c03040384c100f54107003094140d544082d80000c1d4100c00380c1c80c803d4802c49200e441001404001c0da81c5601c2540b00380c60303090092600d01400003004200c010005d50100c0200f220a000310301c030125190300c080c030070704005040200d849508010fa680125405001820110701d8411448041010314000c21107180607128002240070032000c01c00702011780403985800050300328080d0b201c81007102c039111255425140c1d900c0d80e03650700400fa05c4a9204000c015800e202c0400c680e001044102c034080d08080c004400001810f0018a00850000344070302d5150040000b00c00b540c4210046031000122641d40008400511400150440d600c0390802c9500340c0c0b040c03006065440c1c950740c4089291040c13209580d00e170b03a401c0e070318060040c1e40c5030043c26241c0e400000010342c0290320402a402000503500703941c202400020700c18900c04283c4902c0803a4000e28091085600303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 832880062 1250 832878812 832878847
    0x411070f120504030f08031e0c0316050706150e180a0209040204020c1b1801030c0b0f0c0f03040306060506090310360501050c0c060a0f09020414010806070f05 70
    0x4000c0e040c0035040a41c1d1341c03141c060ba580105c0c41a158003000204109920344410030418000305a411131120500701051300c00481c2c0002400015080f160b83d0348107200c68014000c1d0381c9c020741d220350203000e290207000c600594800c0510403540c0c01340742c103000304a2a0210003070407482c0d0604100240b01c10100c94003086019035001d0801c3c1d0f00503a081100c1036040d401800b035040021521844400d69100303c40621040d420a412200001c486240040c40003d40380300001084802171212151107881d003405885030740c8650881500c00c0d04c2004864407520201102030701c101c0703000380d030100300c09903840b03060041ea4030400c80702c141e064100651540020000350301400e002220100d039001d01130300b0300f0380641035500d404006203182c110703404d60300003040802d0007140e81c0100710b00845410059138102c103e41e900c20180000e4101a11a50b20807410380301644664030190f0014024004d0003c08081015184028010800c080c02040e0004040310301400c0c02d0038841e0065624640391840381102e448414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 832881312 1250 832880062 832880093
    0xd0b0d031202031308132904230d050106151e12110a020c040e010c090312120f0f0b030c01050f070f14030c010c0e010806040c111b0411070f 62
    0x2c00d101000ca00410030b4172000c5c00144a0206101c011903060545190841c41081e41e00c0c241d20303a04100b01c2c0e140018038415141140c07a01803a44c540384480b401d0301c2927a0500041840d8000c1000b0044009004054003d41c00311440901d251403220f455001c120b8425500c003451a0088074245d2001d405988240000304106800010003d0901041c0d96a0040c40c0d000c01e4610b001039000500f00710492801d445034440c200303100d030b000700802d00d0300c00781c040c02201c5144005040b0402405442605901a8081c4441d0300302c4610300b048084020940e03140102809040040707610b2810030103010508001820408190058582d54242034500c00c0311400c640c00032808486107400c0802081c0001d01000c030b401221400c0700051074864000f03105071403c61303030f0700e040800400070f121801036134a90f0410300c40b42c0c00420640e004038000c1ea100c1d03070035070f50400c40e01e4003024203115400c108607040e110b032140c003852084129000d0000c190341440000f480c0c01340b4800900910307550003e04001076424428083e64 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 832882562 1250 832881312 832881331
    0x33915040b0d15092018060a18060f0e0306040320030705060103060207030810030c06081f080607030e060c0a110a2004050c070f15140c0d0b0d03120203 67
    0x1a441d83e1901c003800354010381e003d4103015860720400c01403100c1050218103040c00300201d1034280b03130700c941a21040c040c00039042c500469001072141850b41c841d41d00c5420080d20340c0c0c0a0100f05030360faa03000700101071041d0050002516a09071001d1443d010a01c503000b1501035840b4000b03c081c502e1032703040707504000c0d025203441d100c01c01100001400620105000f580078010050f07c807001d40c100a01038001c000c1054a6a0024110510029440302d50030f0060b40d080c0d203440d01807559441115000201c084bc8203036800412002d00080c1418005030651044426503014000500c013840e220340d441d2020349080800480901c008268144240000103e0001d880100c4102c41c00315107a9030104129503050580500510725503507801e003024001e103904a2841d403402e610301046078503a031002030b0b0808402000200403540c10140d10440e6044040c84106a01a0348070720304100c045204594031400f0090315080c2403000d4213480d40741c089034004826415846072064000d000100740001d500c0140b13801407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 832883812 1250 832882562 832882571
    0x180111070941010f030b0a110c0a06060302100306080a082b020406092301181d04020f1807080a140114041a13020306033915040b0d 58
    0xc2c0440d00c1d41012080b280b410301420080b020744000240d07410140c20288012041520800c00902c54004050b4481070342800010031306112104034410b0304c1080071181d4188200740103203007404001d520a00c2161b07c00c83d410081007007520004d83c241c1d207840c890304005030401412180800d9861006000c840e00d0100c081905548402801e6080383c8a00c43d42c4213580d502040601165030007926003001b80c409144450844540302d81005103030700c002c0181c1410000d581c1a0390340051115441800070f40b541c196041001d904100008030072030b00407101648514003450800c0e00c542040b00740001e40c10044095140745a9442001390749055016100d00070180d6115100015843c82181e40c5018004c3e80c410400e40c1b001190410080ea802c1c0d18001910400a62452a103030791044000c000b042016007002d6260355a1000103070a000710411100d4130b8100d0368204004e4064080c8140c0002120035183d015692070180900c117008031080703902030315480208402c0c054401c2e442c014100e2507804850116 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 832885062 1250 832883812 832883861
    0x5161d100804050712200406080105090d120614091005030105070503160f1215080d0503180303070203120603190b09100b030c2b081801110709 63
    0x110085808100c0c200040c0d4450300344401c1140a000748001890500e020290306846500c1c0c10091340c14045200c0c420b121001c1900d901074843e50040d5000303054110003081189401a03602d515074950f450000c0001d6440904500030414920401c020340d0f0b00c962024248508503c1030041e191000340108600b45606000045d190380c007405800d01c100340e542d0702c0c1e0707490b41000843c040301c1d014440700c0c10091202c1004284e540c0c95009510205100d00600701044800c204101d2040721009030300540c0550084070070b0b0005403500400118028400b561240d00e5200200b80701c542c40f400240d07454001a0020060394100c100c0310904160400d0b001020b8645032031202050089054142c0d10803120f510356034003042120081440800140c640c44c6106000e100c4013000080e1b2100c40003054507126003040680203ca20058182048001135880943c45500495040200700340c0c00c99034951040d51014580c1d0525548110000c0540f20003601c001c02009007094006d0303021340030a103070900c0101c40591907030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 832886312 1250 832885062 832885069
    0x9010504030b0a0606110c090c0d06032f060f0403021e04050a09140a020102070e04051504050309041503020609090a0231080609060703050c0d09080a03050a05161d 72
    0x15405446501d03000038138685064400b40900354200e05032555034101070b1080308191142c1604940c007168030b0080135680c1c0036a80c11400200010f420103407610740c18110315021351040440c019003c0d8030b4034840031035040080041041910030702000d40d07149801804104010304000781c0802484001c811100034146c0850041804c894044400160841d1144507000a0208020030083c0c2e44582c80041c0c5241c0800d900040e6072112203100303140001c0c10200001e8280078051121222a0250510a1840782046c0c141759a690f04440b0070340c0c1c490b6181c4003039580281d06e602941c400700c03640074164074284148102040403668004003040d50700c94080040c65200c1d03881d94500880144070703603c0d8201d00300c0103c44003811101c0381e4000180b294019014081440000203103d5801742041ca800309070b542d03400070903407118003a80c1420141c50b82802d52180800095001601404500340e401304070300d80d42e240c4d203030301510815284603100c550518100c1140a06c500119201801c0f8044811360030848400070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 832887562 1250 832886312 832886333
    0x307091a0f0a030203060f0901050a2303010507080901050a02030106080403050a171f0918080a0309020a09020a12090c06030b01020a0b09032a0309010e01020a0f050d09081c050901050403 82
    0x45a0020342c0c000f0406c803041c50038900d04521030b101a20802d140c0d40c1040c1c003180300322070307a4080c0704002d01400b10014114114034030101e842c0c0300007500030700c03941c2401c4401414070003050341c28001c203508260010302000614401c1c1d030304841031950782170026103450b28152955840308800708100500440c8004003035543c80030503401802d080c005c030071b106814680f44400c0980e0540020100798281081c62a154092038207006449400100b00c656412418105a0007811241c100941102c1c585000203141000e43d400b80c0071600240e107903e000301d45500701d03400458107070b070400401000810b1018811a4483e40c0040842c10701070040700c0c4081d00648402e045c042c3c044a03003c0fa0740d8000505202c4034907002000603907640083d10345030760125244000a840e40541c0004a0402001c85182e2203a1780c401c100f141885130b00161541c4034020070b4141552900c1854100c40c0104801030000206010001810f00d1403141d8082e640720202c1400c0011505540402d517000c2c1041790500010004c605503004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 832888812 1250 832887562 832887577
    0x612010c110f01050f0103031b060507020307030e0d020a17010f0e0705100f0c020603060a1e0503061302060d0b0d080406090509010b0c150919061d030307091a0f 71
    0x159000c91900d441c01d5186040c0504900221590500c0c060107005401e40700c0040c15681e160400246440720115191403800d400c00c40645424107045c240480550084000c0507114020303520004080004001e0000204000f5070080d040302c140300d020030400c004e0041c01c1006000c40400070840d00300c059061408c3d510426644401604041001c010b11300e080b080c0305500007010b08000603010310f01c4038094003d1520703100282c000d40c000400152950343c0e0740300803c00703010303111111703100f4000000982040c01d1b810302a0301d010b4840e90001c1890440ba0401d841449680240040e1801c1e003031404410207401c204915903002050034070140001360448014201501c503031399821004520340000c110407040182d114100d0740d070341046408080540400c40c0804040303070145034161608c42074a0300340f0b0012400e0343c90f0116003840000b6410481d01d80c000013003c616011036820b031616404c50b03242e103030b1100780c8464010810400302000340301503907400e004030721003006182c03030070030410f41300318a103039881400c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 832890062 1250 832888812 832888817
    0x80106060e0a170a031d18061e450f0f010f0303080601140d06140f01023012010e100308220306151a0c070302090612010c 54
    0x80c181d164034200507003000010142e004900b403000d4a00000c0c0e03511400520800350400c506d40c0503401001c20700360f800943c980005404555401c628844180c00b400056414078882c03851031f41d00d0b0183d9000055131507401b0100a05140b51030300c1005000d025a02817170200400e004100080c88856841c1c162100038004120920180348d242001100725264401840f50300c0d4101c0703150040c4041454410020300740e0380c2c503042c08186a150100161141044103900303c0710403a0001d0780c860781c2071107034100c10216550300840d01655510b20040024403a5104000790060b0300114000f40d10a41000c03400d50038000e81c030143c440710210b01ca800c0c0c14503448682011601c105000040000509c295591a80042841c440c484c0160070750f940c0d840c1c10b104428171044c40d00b80c80c4006a01020742c2000c01c0c4011036211104200e84074050945501c034952a21901d02c060000f900c003501e0250006040340c0f55817141401400d65641582c0c20070036030343d202821150304030001d180c0319100b02000740b0400208e02c0507038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 832891312 1250 832890062 832890077
    0x50a0504020319050c04020a0e03161d15040c050706020c07031a0f04031805040e0c090106110c04022a16060906120c0311030703140a050c0702011808010606 69
    0x2030040c1443c00c40c00c1040000c880c1c2501219001144020a00b0245d0b52021240580d41d2040c420080342c000741120541c0740c0c140030344400360b009508400c04d00803c072040c424015122524601840406a40c102c51002500042083d940c0003450240e02085061020741402c909040c041d0f1101404c80c2c016001c0071045500c0101c003401403101c02c10381c414140d005540380300460702d845179903601018030280c03006062010010f41c6072118200703860001d01420014008008980c0da00c40c07402c1d66070f001d41c81000d008402841c0045080fa204000050381456900b0003007603c2c01800c001c1c44001d51140e0b4043c41010542c941000c80d02c08081d00320781b00b85200034010200b1240700c81c8200c11303182d030540c4040c1c00e000c1022002c010094007c214100c112051139400284081407090a5000d00a4030602c000c0c0c0e4003000040145107a01030384612000180741c424002c0075502c0510f0007040b00d1040d0b0300b5802c1c07030780244415030056110b01941450985135540c03c010300c6664240c2c503800d58000c2c0d0848000310f60355 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 832892562 1250 832891312 832891321
    0x1303030e07090509192307050d060609110f040b070203190b0702060601110a0615031407061206050a031b0521060a0b01080115020307050607031b03150b090310050a05 73
    0x42003501c1424a400c0c1c0040700102051b600c510710a480c181d9003101301005d15070040440c501c2448008003e01018200640d400b00e14a4003500501190090506142c40d118226004403038201c00d03200c9466a201c682884c042c20209810140e8007c00b200700e030305114841c0c61001c2520b42d0490020028410201482c542c204450007a04140b00105014100501c1ea088601740a200180c090103450f00458001040303030480c0100c2d43d5807204d9802c083c0858484a03c848100d410000c2c51300100c2e5266900c4c0a4807005000c50354080d40e940780700701680400340f00c0d014808200f10b00145004509000b80e103c20050391503000c80d442c40350381c2c0180699960500c1880050350402c1c0706940c0d02480008040081804c80d40020b042d10364180115444154098001c4508074000c1007260300f4036800004840062810034401006060380c6264420071801c1b105180040da8003d0241c2d0002c2580040c201d064182004c0d9488402c0c0c00a9000c5a07042c4600102c0691203100741c49428041d940022010403e841d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 832893812 1250 832892562 832892581
    0xc030a122003011e082506050f0a0806030a12180905040b04030c0215030a06030c05042a02030d090b0a0e03031e0604020903010c08040b09151303030e070905 69
    0x3603400703070351070401091405004080a0441100e040d0342806110848800040c0390290100032a030300090410312880541801318100d0200701c0442e180a4500100040e80364a0229540e000b019508540e058041c04007840e240c1c007880c4000e9100b000541200c6c0703140034a85842445624442c10007010a911420844c2003180c10030401018000c500710070b2195080c44e07907030002c050000074400350070010b9040c0e04034215a1a96101e695003100040e01d240c607810002da1840061031544800c0340c8500512000240c42d0801d40600102c031203290510340754241141c142c0b04c2c07503040c0e40c0700e0480842c0420018052000036612640c5d070324902803060910075103407064240044440c2c000c490f00c043c0d48280204120f00da02907079107620800102c4c0c08810305d5280c0c0340200700640609440580c0c19424030701130751000b61303114142034810350048011300040e8468a4141d501c800c602c1d60a2030303d0800010015241c0303400721000040d403500c41d20300000d10107003040601b401d141942c0c019003400c3e0b454000380300800360b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 832895062 1250 832893812 832893821
    0x10e0114010507020904060b0a0305030c010516050306190801020d0b150403051c0512011805061e0105070c0e0f01030c060905090103021306211e1a04080c030a12 71
    0x304a120203000003100c80041c0083c014201d0081c802d03840c00002400308000c6800914079064054100d4000c0e81e140e1070001d441c1d404c46d1100d1041d540c41e01000500c0400712400c5107a607000c09859140c60f5840d04c006200003101c4440c490341d5010050b910003d6a40b13400d00c01000e0049620b40c0006031060198104079810045050300b807641c1c242400248045100401c01401400308080c18140c0e03140042015941b82c0074403030707090300761205010000031182c03036841c807064007ca0b501c0c0d0b042015944600c10882d02d600d18069090702d469060018039002d5001d0001054081e0017203a044803515034850201101d0788007220b00301c4035118500010402c00495400c02c102908081c01d1481140d42408042070101005100182c410020301c2d011a110b4520703580400003a100c0c1b1004200316500e08020020001c036488000c40306002403120b001d0020720407103c40d603400d960080840d070010324035904031155180043d006540c40c410400141034500c60400040c015660646c841040b10b00c8607412500446 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 832896312 1250 832895062 832895069
    0x10050c0120030c1305030307030905090601090803040620010606170705031e060f1906090b0c1e03131d251404030203010603080301081c0806010f11030a08010e01 71
    0x48078155600c51001a03880a407580040c81d100550b886021004100c1c1c1100c4d45a40003c0d014000090302c202899031001424040d82d5003030340c1203102c07610344900440d500c4000f44501c0303046400600041c0f14652051410b0103010b048505502c0500011802c0142118403da12102c0420b01074001880c01d00c90460500c0d6120103142401429440d005500b1004501d011614256690020000408a50391100e10860101000c0c252a64490002ca420484054940507101c049100e42500140040c2c6820445904000c0c00f1702508001c4803114550705004000c1e0000312480c002030000c1400309040c3c001800c01064440c88000020f948601c0d881102c0c94060b04044c105484000c4c403a651160303401e254840c4480134504204c0c13085184030b10401c0350040d1f4000950650a008002084c02200d4010754166842c0c082503500b81225910701c650544c40c5c8003480400b0a81040000d001903000f20020007050302d950910003030000b29220703014210350140039018041883c1ea8010310022142034030b01e0340034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 832897562 1250 832896312 832896341
    0xf010f1a120621010e0609010b15070804231003052701060b040806040c080118030509030c061207030c0e0a03021302130821070b04081810050c01 64
    0x100c42034035031920361040c0c8194040940311840800c0d203d4440741115072208522015442100c2003586506000c0d01c00c0d4014210f4921030140420490702c418070540c6c800c0c80c0020210340f00072584c15226021500162000d403410344081c040054039050814004240101c07109041407081914010001c078120300780c00359401c06103007508102001004807200c840a14030328404403014a0303c5450386002d0103164202d0035402c0d101090000e207107031000860602440c41500c0395401c0030f440b031940500300e5030010100c010800c0d2000504000c01d00a000401440e032020b801e880096030303c1008588a40c0c05409411410000f0303c040186c0c1c1c035454801e0710034031012440c20001d0401404002000d404580c040648075070110010544180310a40c11240c0350b8240790703030482446503074502171500d0b000d8008104a031401d560200b42d00ca81c2c00c0c40210f445050b4810340c1461192140c1c0c66442c842d0f0460b05810180172200081510a581d071811100e44d04400d507952140c0e64030f00140d5450075510f208902494 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 832898812 1250 832897562 832897589
    0xd0f0b041716060218030717120a0807052119050a0b0604090b1f05040609060203040e1305210405030d1e0804031b06091109131401090b0f010f 63
    0x3502d0708101d02429186402c501d0158071a804a070b552610305008100543c0d040c45546c1d0000760300781f440c030b5046803042d50a1042d81c00e03100d0114241c40c501e1054001ca0000075450000048101c2e01580243c26869084003009402c20081c103406010030006072242c0200540c803084040c2d40126034011503601140341c00b0140000c40c200b030042209070045006001c500f03a2035204105254498054445000c885085100d038070031604074001d811940030340644000181c0700e01001c55143c0c000000c590844540800d940825a9000c8000000380c10300401101c45009100160400350001181c01d4600c1e5410320440740c1c1c070340c5801d04240c81d1604090042050188078910401c00119270209136003a807210341000505a903441c64102c83c0c150401c45e00c0000000c800752440c0c00d10803154031402c0c0041c414640c2c00c900280380820800340711001c82d80c1c4144000c8825002d00001ea0040d5082160b4902c18008208503449a50b0703884400000c40c0c80240340c0e600540104801070150030004000d00c00c5031204070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832900062 1250 832898812 832898827
    0x5041107120302030615031905060a0f0b03040309030822050d1e08160b0604050f2e0f08161202061b0709020d0c080f0601021b0d0f0b0417 61
    0x60068506502003070a1681c08800143c00c2d45481000040c000951240e4590b2454111030800c08807001032650040c651401c00000c00c14201400a034040d40c180381c1603102040d1074911041c029900082045081002c1c00302c0c00000101e0178005010f0a44000c07c0c001c00d442c4880c10541a280c0881e4000c901c11000304402c10040703842a80900940380307900c0c08804401d1031030b040145091096290091a80b05204568801c0c0407070800c009000e00d8080380d05108644680000c860605402d45921104045481d038151900f5140500301c0b01e005e441582020041e03036103511403000d00006501c0025940c01600c0e0a200d040c500e003d192018159804e6030198503015500400e20034024100c020811030484400541d80400401c4030600410319240199039070400080c84c003000e01903842040f008113560401040c155007070340002510609040e40203004c0f5401e607100f003250002d00000c03139507000032901e072201c008500b04843c2c10180c00d0140155035072a040c07a20340400d08102645162404a4040c040031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832901312 1250 832900062 832900073
    0x190c050901050c01090b0705130f0b091c050607050d060905090304260717060901050c0d0b01110f0a03080c0a020304141306030c090621060c140d020405041107 70
    0x60314441000e19001c0d440d69160042c0500400d10f8140c082c048101c01d02c200301000ba407002c02000c81000031400f907982260b650385400f1003100c460241d1a42404144110000740c2080710b417141001d02c2522040c03456648a440302806c024043d584240040d1000520001c84051400756000401a110040241d460111100b41c0c603401540030b095045101040f2240110141c100d055130300d00c0506003500c0d100e596981118080ca042c0c1d8204800764080c901c0003c00144041c0302daa4810501142024a031043c1c000641c4010517540840c107042c0060003e40e6004090b00700551403002c1000002440300300c0d51810003501510700141a2610404204107000c01c107517002c4142e0301151032030380d814900002500c0000742c1c0c10b480000c0c8a26190300d024400800e110604103180c0031106d2111007003203140d803180042c550700300d059160250183c80c5981c018000816950040c0d805160034030b803880301c92604962418169110905004486801141c20300180c500b5116102c00000540e211500e00011507568 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832902562 1250 832901312 832901317
    0x18030c030601140607053009010c0303020d02130803030f130f2303070f020901050319171608030412050c0d11010219090e0705030105180613020d05190c05 68
    0x510f03e9124041d00b02ca520f07504c403c026a401d070750b800f00c150380514151348a054110805049410300000e03046204604aa40c54011a0180c5c1410ba4031450147c82c0c60b2405e80181d80080b5910b080789a003042016580700c24a01131401030000e9001940d900d0074226060090080040d1045c112511a88000400181c03000950210507a1080807c2075245144850540852104108100a000000e455403c120308540c44604142c400c844c5416580d89031400c0c540d58210003503001c0d200398500f0550002240300d1104140c00d00320740782811440c0c1003115401051008040d1401c581d104000300c113000070422aa42c0c1c007140002c0900d0007a04000410a085617220030354040641400902c09100d98404000e40445241e01c180020346020b15054440080203800d980c410302c00310000042c08100740c248140d040b01d04031a03004240c5082841d0f1101003c040080150039954041c07121040800201c04a0002c0c01181c0a8400009220718021808100b45051b064401900c540b80c2681c441d01070707400109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832903812 1250 832902562 832902569
    0x614040b0405010815150a060f080c031003020103020c010b03012f07080d0e0c10050a090b030405072318040b090105071b11120706120b0612060103020d05040818030c030601 76
    0x170814101e49524000b01240351035a9201500a80e000c0e00102c0c80b00e4000401c20301400c5541e690701e0955580d00702c0300d11f0314081078580351a00e00c03950500b08090b40c030a4020b0442c1100ca000001884884800043c2c04c42d8850740d452519401141020250007005000c911107420300200780919215240d658141144200009502c146588506004103000100030f10500302d0406000a4208a007507003020304250000d0780000001010008040b1fa021031480c00e90740500c0d0300c41d0040c50003034244080c050389500310419107800c0c0c25684440110170355a81403030340e88041aa900840503030410b82011400340d10010f0001140780c2c10542405007203940310460600a522411f1544581c008524080c2881e04a4160070f81e80401c1e10803003075850000205041c012100340b41c46403507441460103a4030040c0c1c0c2e1040e030040d5010a0034031000071240a5903035070359801541407400519040c070300011003040710820380b026110b003080072980400e0b280c3c42c61350038800300c40304078000e1504040b0600025070700e480501 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832905062 1250 832903812 832903843
    0x307020a0309080312071b140616090f0b0f0c1f0c020c0117100909060203010f17030415050c1b040f14040f050a0210030903080a0c0509010e130614040b04050108 71
    0xc40000300b6411f881d0841e103841c0e80302d12403600c1c4490380041507a45020560b2125201010003800780002c84c0202042401c07601c29900300020203141030200c01d56a080b66420406c1c05104200c8409074030170070320a024082c0d14410502c400c2c195880601e10403035602a95107800c0d54004040585240c0e000b0250b2600d5600c003481070310a994929602c0d62407040580d01500c041d03824103041400f0420550061810b84084884110301581c0e82c50030300d00ca91960001d803003080c0c0c101b0002403100030f01110002c1880502400c1092506510781c0d92240b5245c0d03003101c1148000c141c100043c0a0f841c2038001e210111719040340a00562840d0f00301351544c0741d00548003e20420140b202d0030104202030042100761034009040705946040c9680160140200ca81d00f1000201d070300300040d450344500e01c142000c80080b03655140c10000e4460041d215503130410005648402d05454801441c3c255024040c05004000d007a0140a90004c00703110a550303980700d4040c802c60404c4010310603190002a43c450340700904 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832906312 1250 832905062 832905077
    0x15071e030203130906060e0f040f0f02030108060a1e05060f060c03130b03060a0608190e0601090c1403160e0a060f1827090204110304112b03090b0307020a030908031207 74
    0x1070f0004002b0a0140c16410181d030074024017280324281e42c0d024504845400099a0641e644e10744440100c51000545184421040d17140084082059010326403001c1c1c05045a000001880300142168100302d41802d40d0750b10001e0303061440383c1c83c503411500401d01601020b00751f050400003d045c3c604c1c54010b6504001d025000145c00416400d1038895030928640c0400910031101a10340c0c5034042400340e92441400c01050110840c810410b80201c461440a081e007507440700340d140d11545071061500420000aa403010030140d858103400c80090949d91550039064428900c00b074403c00b041c4040424402c0090801c000800d00c03c00a501e02014610741402d59404010b64003000b00701007440a0740003450842e100d20b007000080c000354042d40c020401c0c0c404211406c8100b0869105c00498512591404500c410b8801103041e140e003a100c1c400c1c10640b00140c1c80b2900c03400c2e00d800407180b07a00141e10910f006c0e401e25400c2504803010b800d0840c040c615200c440d48081c050214060254003c00110 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832907562 1250 832906312 832906339
    0x102010e0d021c12090c0f060504031509030e280503060103020d060b0102120d0902040b09040c0302100537020604050d2a121d15071e030203130906060e 67
    0x10541007408005820f01005440c0700f0307040c1405264828050175040d215891404030740c8c42d00039029101140da04c1510101594920720341180030b0321011000314207002c000c210318202680c2c2c80c0440e2148120f01f04480741e14a0300e203400d443e00e200703495000c103010340c004100500160b00c0b946141143e56030099804200c20040c0c400403403400d0074004010440360340205980d40320f003da681260400e00e000312010300540800c1805c0100c540c4054900a24408015204200500b4031a07101306c11182581009800c00d11055280e010031050719860031400b03011565030b908a246404c4503807581b45542c0c4010002407130300d995402e9540d82c2541c03c0d0004c1c042e218403008003038890101a01e103440b00c035580b0308503511a00e1a01e4145040540040301c0403e0206100192000700d601082c020554000d000c140c0c29143d80703020340060340c014002512182c4050006401024250034100b260500c65802581d5031021040c001c043d540003600516400c03400d0220401440368000e1a503006180105e50500c035000c030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832908812 1250 832907562 832907567
    0x7020303091c0803090631060506150c06010306061401080a09080702101e0513050108041403131e120308090f01060f0317040803121b04030b060102010e0d021c 70
    0x8100401050040000100186410041541401071001c0b1a401e1440481002e07e02d4600807220580d5071100d80c2c20140b5404a40d80780c002542100018020f0100107448001000341a030061070700040350303400a8010020400103202e070500803c90070142001d80444200002c224410203400c1301c0d44035403112410130521030040d04451400b50300500b001e100c0d00903100d0140504141d0b080e61180400085d4001e031415005104071000440420720300c21100703007000c0055410540145c0241c600403d818200986040c0400c0141b40440c4501e00c0100704900e89240321442d050f621007110309020743c4240800810ba0103140d40c000c9039916050924082d904c4881c1c0510308000b17822014240c0d801c7c400002004021110500305503802103100691300c002d504802880c9110707512030910550310410801d8152860500c0b01900103800d03049a40c1c02088145501d40c6e2030700650000d580c540d03051010702c80e0300e680920a403020401d111000d06500c100780c000180d00e03103560304106010f9070400082035005c280b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832910062 1250 832908812 832908859
    0x1103030307051b011803270506040603111b030319060f03140c130b0a090203041106030910060e0105090f090c0f010306030f0807020909061b0a1407140d03020702030309 74
    0x907140103105c1081c0102c2d043c01802e40c1909074950703041070002070300f02c411b19904400d05803c1d520040e0120b458075107001d01c201d0050614003020b240712041485640900c0d0780c407104001120105500071520b9003080d202c01c12a0301441c1d00c1ea02c0312341d40351880400410320700c04001d004aa8025021f24560001c41c52024103040242007069441404079840d00c007074401e16444020f401c04242c0310100780d15210780c2c082d07080b4072058502410010340300c00308018030318007800110341c8402594150f13128042244000390075100c4c66001094a510403000501a5040945040da0b001e40858040d00440c10202d46040e141e0f22000225805640c045040c0c100c0d40e40650000c400642e8030103180d2080411508000d402500700e00e004a11500340000450810000014654014518000110300c4501d084141d24050b0b84440300c4c0c82c0900180c3c00b4204201035020016090f164010302d51040a41c46091486007040a0140c040c8249841031002c48050f8400000351501c80c607090f2980302c0442034071501c000504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832911312 1250 832910062 832910081
    0x50a1d0f130807080f0c0f1c2003041508060103200703030c052a120921150a020a020f120f030408280e03010c05070f03091703071103030307051b01 65
    0xa10f0015069146c80350010300003949600740400d44040034007801d0b4100c1c8540001a44900082481c0c1580751000801c3c40d03400c5080c2d0101e011079242c5517444000301d041e041e00440c20804034017204104401543c01d80901c050103006800415110128001c250b01503009000d006810103035180961a0300600170400c03038030160030a01640f9a07442c0300080d580702c103031400b07403401e207450041a58244104c6c0c120015a05080002800a50400021400543d00b00c270300d11000c032070b9449200c00713200190380c00da030101c0d0260500004c0540da9804c24140646009010029011142d11640d01c1c8250301c03c1160940c0d17048190182e44598035107035801c11810a018482a405840400d02d1449140355510703800710240060b10740310514040c00c181c080608848600340b030240400d204000400c000340d9102ca0907104a8800e0405a02c032944601041d403104801c000812600c1c4e00008168090021099142019000480003145075240240005007640281000d0b580b03001000400b00302060001e400030f0015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832912562 1250 832911312 832911337
    0x3081909051c030e0604050303030609070c020a030c03230303150a081006050a0f0303090504020706020c01380f190b0a080a050603150f10050a1d0f13080708 69
    0x54060100340d940c06100361030070441c080341546105001301d05001040c0c0b411a10002d01641c29541c80806120701d540c0001c14000412004a007606c005a60324040c0300301850240d10b844038040c0c00d61034200300309a138150fa2060040f0f0482e5401285d20b4002044a0348581302480d2007040601000102d0420f103000c3d040003107107018080301d8520540d13040e0302c24021200c040701c650304456a5412080c01c8454503001c0500002d00d032000500039400d040d001081e0140c400d0a00605d03001c80309418078216080c29164055030404100c080400a04800e00900900c060094044031500346400003000030301c0c141c072941c1c09030703145c3c0c903000c01074403c1d0512a100070006140303890350702c01c0c0c950390013000c009003125056034481c901004a846070800251004a0342b0244999030041d4403100c500c003c0861000704804c03110001c0c882c01145d540c469800100090912200340074501c4440c6d8103071036039214020020501c2103070041c20001103019003502201826008981c09607200d05604200c415032040c030000c1d0b440e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832913669 1107 832912562 832912579
    0x11060105040213260c060c1c030e03040f2102010503060103090503090406030f260a080901110327010c210e1e160308190905 55
    0xb90510f03a407030112800c640e20480070700d0303610305248403444910340415100c0c0025410811040c0703640040380c4036418400b410b10007a58a02010109034855001030b40381d50381c40d074040e034003508401041c00107599549840f0010030408000d180716100201c05000113020f001c1020701d031458800c030780c1696070346e2444e151714004401502d0300560984043c0020041caa40c2940c0394030a220055105a0124640783c1807418912107074001300e008400c101901e040000042c20800c411954101100c0c00e140d040350b00d551900d04d0041c848400b00841d411703030020512109000395071400c6101d0a0020f02800c6920b550050a0700386d4041022031004540d1245d0b1981e1440340540081109085000000406000f42c40203286840d52400d101940340811803008502c2d6502800880b82c00b90443c91003a1030b05141d41d40f070041d40c0c4100d89030512609900340070b009a180c070400d000b10080c00c2c024481c0d10f = true := by decide +kernel

theorem cover : BRFrame.Cov 832733812 832913669 := by
  have h0 := BRFrame.cov_init 832733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832733812 ≤ n) (h2 : n < 832913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
