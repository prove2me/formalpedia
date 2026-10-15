-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3866
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:54:34.160147+00:00
-- url     : https://prove2.me/submissions/1703d60f-d582-46b9-9c67-6e869d9cbe90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 695143884 ≤ n < 695323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 695145134 1250 695143884 695143909
    0xc0c092408010e0304090207110604091a0402120f060f06130e0105010503040302030417100504051506221d030406171303081501090315062c01050d141b 67
    0x200a003c02070700b00010075900d010714014068600d50001d0f21004011405000485040c800307000c082c0c98550b201c4600380108103610101c0180096250884d0240c40d040c801c450b501401c0761746591503603c800d0a07000d124000244495000000000074040035510a0302401d00082040142c0c8807450034085441e041d0b06040e4021414002d0074000c0c0800a034000c825103090350100e0007050200e0801503070a0380f60428520044c480d0750715242c00c0c0002d010010506014856988415440c5516214140b01c1e09200010b00851500720523100c820a0340c0300d40d00050f00390b402c51485100308815420000b0f082d6405984500e020860002266078481043c0d48181d138040e0304280100101001514042c0501100920f61400b41115481128003070b07000c1c091140c06540c000520120100851050400070710a50203200e14072031240801c81034440b4500c054101000701031941c2a85079203401c0500522518100044405400d00349802841020400401111050b0070850760901500d41003400b03400480380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 695146384 1250 695145134 695145149
    0xc010911031b0d030918021801080103080f0a02010e010e0a050d1b08090111010f020a090f0f06110a140d0e040507080610090308030406060519030f030c0c0924 70
    0x2c0c82c086010250340d07800c5410304007042c3d5030800942d1980c07030212220500ea80065400d0018048000b28012040d405019595248a003480b4502842001959100405d110041512008001c01c0080801c42e101910714082280000b0030f21100307500046081d9034010442c0e108079406251504248403040226481030760351401c001141203a07454484002842d100000350041500003980307801a440303100c841c0e403101c9203e40200f02d018800d0441001a5002044101c001010414041007041039002d1000481c0c403004401c98a803443c1c03820648903901c18101080c0c550156113208001726840d0401425400e0b070301c4010341400580084050a074071a01240c1d80d0046140c2801c021400e0b400024841e081981120349014100c414201200d1840c81500010090040402803104102407074001c081074500072200c002c41544801c5030056420301511000d420825101032940c040790081406a1825020b468513100d9546c82e114007109079045400c10034101400c050154031624110380d8171300e010b040d12 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 695147634 1250 695146384 695146393
    0x12080411010507020d15090302060601142223011b0b0a1d15060a0510080a0c05040312110607090f06050d090b0f07020715270b0c01091103 61
    0x68582210400e59010524180000066000151350701c82202c110207590201044d483c1014805200c00541010802100948100004108590300680e003011103003810710940d13420700d90061002003035410380d4022100422030035080481c00314a4506003241a80a040708a08082260700004103502c201502c400410101a1100400660300b01d80305900000300b00c0c40803504200c0c810364100d500e605000104602c1c49141c10a6400e0781901d0441440340d030f42182c40c041c0880d501c42c2440f080304055175601000501c400005440e40c000c82d8003602c850311113031070218201a1030f9510514000e01016100000c81d03519001c2e00e10080040003410b40c0001c031490184070242c605504500d80003564010701d014400c01040707211844030154002080303250080001c5a00b400e1840515102c0328068078140014000c1c0840819a035104c160300c0644000030390f4958801c40c14000700e20025860900380c49261000b8603600140010f01c01018161900351080005401c00240c0f40000c0e5104c923030000c05000780c21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 695148884 1250 695147634 695147641
    0x220e09010209180411041a0103050903030f1605040315060503101406040c0e030304060801151806050304020f030a030f260112051510091113050112020d11071208 71
    0x8aa4081c04540d240c030f403210101d151180d2502944102142502640041c940a003558003086c0030320314100040320070b8804003e151541c283c404d0b164030048a40340d0b0340310f4070900803034030540d80350100f400301000ea45040740c10a80c5a0b41d80b01700c00302d85901881e02464603490107102a04e0103020001d0341110010342003200035154a45800800001421580300d036940d42ca0900c0d06500a0503c0c210310140141a65952a1140c1c00a400503000317000e85080c0d2040801d81034044ca00501454080c092643c0040040a1130301e40210b51580c0020400c030303000603e0002c10141c688080003a00381c220321035124140ea82d4840c0200810322940a10445085203138003070621180c2d603001031003c0c15a484601c02c60b0210086041c20f41c43c02c0312281c244903142e4856401c001800d103c2e030319101c041e9400800240b2149000d20440304d880e000e02c140d50500c02000c0c1904121170360042c00701550901e000c0501505003201e85034941c00300c0d0b041800c403800005000a1b42c000300103008100b51401041420601143e08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 695150134 1250 695148884 695148889
    0x30702070e06010309080706051608040302031801110604051e1b0603150a060c03021e060f04031214040c0501050a1b02060d022a010b061e220e09010209 67
    0x180c45126612070450040e0102d00c0d140d1207904075184898100000d1a6150380500d4400d0040030100d0b60349d07034508e00c0400744c2c0c40824800d0007920302842d0141c1c0158100700b4202d80c0300b02407000420700241480b0711540c000c20104824003001c0d10540c0540c003e0010701c411284000480300645089507007541118007591241c8004084039000e400058900720340301d60318840e9101a5008908500da48104842c1002580d503030b0000d02c4400880c401d9003900d154841403400d2011888641e860030041e0740091001502c0401c640e810745030711500074500030324034044000002c003c8a52001c00c0144141c4200204003c6c48004c0031100c00815007844c025180106500b8002c0071503c0c917124032000a01d241e0101015541c81038161051400182001c654071018000e00c20305284181da20514030381000c0b01003c00c0d00d001842001402038018040c18500380c80342170503500c107071800c1031224030b8100c00340011510440f0300b0036416101d00d004940d81c00300c00e06100081c000306030014079128140e8010844000c164 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 695151384 1250 695150134 695150143
    0xf060310140a033329030c09070c0209060306040804061b080a03092603010b0f0417151b190c0605070302091908120703180605030a0c05030702 63
    0x440140c0c2092038510201e40000350032440c542d0000c1c080410468001ca02c0741c0800e40d03007440c441d56000c505040c00118100e15400d0340c803074207950f8100101019081004800c3d11542600783c0100500703072007074003054030b0001e8013003030b0292850300024420032180c504505008a0490300010110001c01785440c103541c0c0c407407541c13103180200c6080001100b81d030312841c0701400a25020b070b42d015803001e45404150030002c005001c070f01402e8402106c2007404156803600c0b41e020101d8060b0415160b03207103a00f00441442241d01490402c00740c00c01c10000001da22010089402c0790b075152030050b0107021561110102c1c03000e4060075600c140f48106140c0c41103000d01e842120b50403c1407203443c580300340c0303001d04c140c4802c03510000181c030081c100010003185660503801404854000c682c020220410b84000e0540c2803802c1c0112070b40c940c000081d64024222082c00f900c40f06d40b180c03a203501800342c1d031003603c0000c00841c2e0003200030a030301009009100180c1e01a451a10050345005030952421080082d42c0303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 695152634 1250 695151384 695151389
    0x20705150304030311120403020c131401031b0f0803070203060f07090e0406021b0f120a050403080d1e140a0c0509010c0309260d050918090c0d0501020304020f060310 73
    0x340342d1760386902d031120302e54902600d070780580b030160308001842c081c28003030341700c58009460501c1050a00c910f42001c500354494030b51802d41401111aa40e0b0035980c9242c2a001c3c50100d030103600032070000002e81088105410701c080c12200001d1604c4150f00d105052400e10041c2004050601040c20000400c0d4403040f01c1017152050b14000115803218285074000740b180d848220f9904c6144068122038050015100a8440741d035001c882141d036200070800d00034080e44040c58001201000200302182810020380003512241c000010400050400c000040042002a0001e2911100c0006080c41071038410741d40003801802c140240d0315a001c0c000d02c1c611400e242c05052081040d584401d251084001401030300c640b0f5081c41c0506501d949000c100c1d9400b010150852103034000080c03100348180152071710703e0760203000300f002001845202c0070113510050007640301e41301740c500543c00b5079502c00321002c1c401d018000050703807800c0a006003c800081c602c9100c0c0510420001d1012522002c0b032003108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 695153884 1250 695152634 695152637
    0x206030708130605070809122703010605030d020a15020f030606130503012d2007080d0203010308030108100b090c0703021e0610060e010905010e0102031c0203010602070515030403 79
    0xc0903600d50840e0380041005074000b0b050f0764070b01001c1110007a005028980118803420407501c5480f00041c80014038401c0c0c001c240301c8106020409441c050303144024894a10300100041001c83d03e84022078640b2040500304001a030003109000180000503c05400000c5204c0095203854cc5c003828403481417202525240c055280041c1c200c120202c802518000780030014024022408041c1c201d203000414915240c40420b04400e8400c80040c5620031351f1103045421030f1854080030000140d410641145109441224041001a84a000710b20045000e140300d01e0456440e541000342140c541003c2c6c1d4a6070f0701562030b002c03484800c5c0d50b4822001350300000c401c0000c0d0307a4620900d4100e0130b207441803440c000024442ca48103100e11601142c00c80c4107404496a81d076103503527542811200c2c03036400c0b04801d0214060749400d0040394415680c0c0b410b080030600403207242604902400d0219014483c10138225980800140462076052101f0401400e0440f81102a03180b8109c5036007603403102400060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 695155134 1250 695153884 695153897
    0x91e01080c01170a02071532130327060e03031201030b18070b0c0606011e030203100b03040302071503060b04050907230403050706141206030c1c110105030402060307 73
    0x155114103d804079080300d0703030040e0f6603022000c0b0401054040d14000550001c5c1e00c23a032401c035110700b1141c50f06091400c8402d403858031843e140c070481c0b40c0d10140d100e2802e60030400302c0d0b0944040180300c5a80264603096101d154200c4078a4440d000300103102503441030b44290001c00c41e041001c0c0c3e00041c503906507500310304100c6080d00c6130540b007044414160300f0a081e41c040c405000596900b003c020b448103181c22000d4881960f03425004545040384508004010142003c0307812101e84650b002e5039110f40000310040f800782e152505400300340c00c225400c50050340b200c0e00501104041c1403d1a482c25141d003003e010706418803120760818051030044c07500070003505000411092094010406482c0c92501a0a000b49100081c01c19544540015103080c8204440090724074407a485400300500b0750b004290034075491052904600d41e0103481103506104a40c2118001e9980c10038600d017015415102e08600c0b0700b145405804c9092548403681804030a000308805030f02e81c038040381c1d44584545440c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 695156384 1250 695155134 695155141
    0x108132103021b06010e090102031303030f0b04090f0203010606020609071217070f060c02072706051315090b0a12080f04090e0f0609100b060405091e01080c0117 71
    0x100c00a016074102d84041c1c03010040f00002806000ca412810b80d040382c4a401e0450703450808180c245d20090f2102d00070680f1000325a800701e4800e9000010b031800000001c6054251140010159060340c102541e0700c00f0002e005100314034092041030010001c6001400e16490245e407203940b104030611506044d00e00704014201003028402d8007111003a003d07190640c9403002400d00b0003004051381d100300d40c0d9926010b20f115010780006420001c650341c4c1c03000c1d807010310020b903001959080030020422060f51941d50105d43d503614020404007a10343ca0308000f0f01074071104010a03503817006910003512036140000380c221030f45400b9681e170241c81c0140d0640090290340e02e0700c0d020782d2044a45e000c0342a28081000f041152050b0440c8200a84501c1142c1c02c100e420155a81c6440c015036100c0400e80c0a40c0d486418186103402c0006001c0000b81010b05240e992000701c8c24801c4100c0d0621000c1940c400228000e040b883c1d0304501500602d0001c0c580400f0610002c1e0402d0b5590f10130710b16a01c0c490000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 695157634 1250 695156384 695156387
    0x601120611180307270209030a12030213091506051c05070c11041509050c1c020c0706050408071802071b1415030a1107020d0b040201081321 62
    0x5520740c8490480711580d449190103460070a490718500603120b40201d0000007045810000840140907000024110400642d20158000d60061000d580c144c0100001100481ca2421084500804503140540c2d40e0790b411800041102064003c40d594034a0085581000144190704505603045420190b0342e450100c04410148480c1403c2c0c4510182480c040240c0305038010351400c0900c1c4111a9108c00100703d604110949144c00e15442d80c8800640c0700304250301054015641160840c1e030078514000d0716407000ca4441c04221809800c0a800080701401c1110404c00c0740010881450039a0405040c1090503440703880d2031085218012040c103031420210150380c11a260f141e0712450010b1043d603840114500c0b4810741c030641004640c0203a5100c84e42c141081c80301500c0e20308446181c55582c13a055014010410712001c0c15050005101c03020040c0c4429848089050207401d02d185d9500e064400100b52601c000d0516540a001600100005900c3d0005078000c0320041a55610f00500050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 695158884 1250 695157634 695157641
    0x6020a0306051002070302090f0f04060902010e1e0a0504050f04030e040b060a02010509060901110a050c0316080430021e0a060e01020c0303040602070b0f040315061d0906011206 78
    0x829503000f4045150252003d4000030701c0390843c0d10035107008220355646203568007040c500f00d402a0b94040003100260004070b080c0d200d1f540c0140305040100c080c000380c801090308007103100c85c0400068045940e0940c1880c0011485008040440e424071440c901002100b01e01c200117072004061104000240c1d4242c0d40c1c9811100c0c03040b6000e01540d40301d03001c540c0c0090190a085c0c43c032100d81e00401010988034030f818042c42889010f1108458944507a00c0c40480f0340d0303485101c000c0e40034041400010801c0040b0341302d0400c010b001d84101903c4030b083c070301324415107203008507102c0680101501003000344122200340140c0580496491500d40400d440e94000f42c00181d030710f0b5500c0354250001088464001c200d48098650030f031b00302c030445420941032690768070641c02440056030210404108001c0000014244241000c40d228201583c0c3c0d61040110b504120b00440c0c2152508401c0c03040194034030000ea881001e218002c001c0323082c0400d0403a01c680c0f06000c0d2200c00300c0c110650509000c0681c1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 695160134 1250 695158884 695158889
    0x130204030f080304021f080705180303190207060c200103140f1602031c0e030f0706060303080a05100605031b0c21030c1215100c14030c0a06020a0306 66
    0x4114041c1065450b1441840e0f20443c0d040b03204070340c441c40d0f91400c8414140c400e1b001c15040d032901055a120090191a6501f1030200c2d035002c0c0181c8180b140182c2c50a1002e40084080801c100202101d00440642884450b0b00b1860070030000100e05d82c0811500c2240c0b0100107444030807100d60304220710040700903199000c0e000d400000817000340000c404945d0b0301944103512086000103010340515040b42c683c403480502180482c5522513000ba42c22043d84085002d81d00c0c40d040700c1c03404880402c03441c041d821049003905c1c07540c0e0360f000c10002d25170404041584048907400402170740c0b40c081000c1d0307000d07807541c000c49003000000310028034064400030360003284112000c2240d403100c4803140d0301603848102269141c00c61054034030000d000100a0f085c0c80c0107940c001d044609105e04001d5800780c500c4010442200b1a80780c500c2041c0503211540a9105440e4030b03503c51003105843e04200e0b00340c41c2c007562007680d5688100950803001d440400c28136402d80e4004000750741e5801440b0300b2009442541c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 695161384 1250 695160134 695160143
    0x11b050a1103060105040b010c0219080d0c060c050f0d05041e080c010c0503091c18030b07181809020a0503060c0423100c0c082a0405040201050913020403 68
    0x152250000c0c03000c0d54101c4840440124110b8006a80b610103210030350b14129007181c042846215264018a4681501c51b010820600340c11100780d61600e140d840c041900044030041112400385105100d5180282640200d0701e08004d4074041e828a2a0b40a034450b4000c4140a640d40f03034046410004060f20b902c0503481c1980070340345a041a4102500320707a1000905510962801006800c858010b1055a02c200c0c541c601901c0414000c281400f1000100506a02040b00c20048050080401c0311010b018600665600340c075807a00d090040d1022640c200c1001040d6044038042146106510f0b1042c68892446c40125285c109071003c5003065a035500701750b42c54099141008030030705038000900215041030218441d441c1e1050303400e81c0c488410001c810b4110500d24588150103001e640c0c00780c1214820261020005d030340720402410b195500c21031090224071410361401c40c8003004c5426000300b104550411981c28250700281451084155103409461200c0ba0300c11142103540c1520010344e0032 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 695162634 1250 695161384 695161393
    0x60907110d0f03060e131b050d030518030a0506010b1602120a200619050c0703052508070e0c04090501030b070324050127080d02070614030402011b05 66
    0x111101030088026100b038140020724181000510718220401e05004034200490064030707a817152540d0040c0030765040b601101160b03020000441d915101c3d00701d8103081c041e5503416114604130755016407216055022601c0b03648140c000300701040001c03407001c0c11035982425860b03075507800c0203085042019203103029510006a00000045407000b00e00400c1c03080c8189034008400195180390344002c80182074103504180c0a021640c5000c004224501c8814040e061150800c51007603803044c0f9214103500304a0329504450394081e8405c83c48003220500413030480307440c158941000101d5a555182d8480c078500c1c0b0135030801003000404401c3c11a00036150f419004d000d80d42c0c4030309010307000c80019200d42c000640340891030000c070a80c40214480b0500941c0320500300700d00e001d0045440043c00d16804a2503804d24518004200030b001c601710082245c40b000e00300300940044080d08100895000307009014010300030510408040003181e91080d82428580c982d4205151800c0d223680d030150009286215 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 695163884 1250 695162634 695162653
    0x310051b190201060503030a1e0c0b090c0406080c0105030402041112070201060812040b03060103110d1d0d0306030209040f0609140309040c05132d15230306090711 72
    0x40707592091100c4005400a104c080e070790300107142d564410a5095400500d0a40c22a142504041c400c0b00c500102440c00c42c006081c55100c00b0014142079940490320342c1700032005586410940a503e0003001d440c000740145080c84030028150340301c0100000d108a45c0c0301c110300824035846081c0d400341028802c200c00c180c540b042000c1d000b0312a500a41c900c5201c1c030755001c0403040c401c00407a015190007208c040c0c29038840c040150301a0a1303641081c860000306000c41014401d852141d0000e0a64441541844d104030419041c02c00422016078001c2500340807080c00543c4a2103000380d0402e45c40000f22036000600e00b0144c0051603030003002400c0560050000c0038041001015041a0800701c408000640060206480c20b03c6400d00515062110b04000c01c0541503083c08c0203503446410285240b00c50140a0403d401031258018020ba924803400c0066503503400314025415104041c0712003c480b084a03c07000c9a40030041500340b14030200c02c0040c82c401d106d5100d410820340800f084540045 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 695165134 1250 695163884 695163907
    0x150e07080405071a090118120b13081b0f030403020d060507090314011e050112030507030201020c011d0c0108070f0c080408010908031b04030b0123040e030306130209240408060f04020a06020109020310051b 90
    0x1400071220b33601c544a0b400380c00e074142101104440440b07a0060a02082e01d54565440c409850b00801480a002e00c1d6900000840d900d985650b618608001c00020300c079a603403480e44c0d5504482444203000500e804014000010500081001c1c607425080c100d8442c0c0c020304c1c04034068450058002101d5080010600041e4043c84114014089400c20707540b46030841c4004680030310045500703500050307000d4070499280c1c2c01404c80c0030b1721703500400905203040c0e2160801400e4a0040b40121000702e400020414020f003040c0d4442c184032121150a45070a18540b2980c0c16004180503112040c043c0209440e03003080d81190b041071410300031304244400058021002d032240c00440e43c090099045d140050605251403003114049203004014030b4000c0c0c882c044a100783c0c1ca454100b03402c4c1c0e55041001041d104001c1003401d11406ca07006804c082403030a40f041c00060896507000300300356030602c2c540c8001a134001c100b5417901e00c020500020107542d54122640c00b0784110a403076445000003e80d400511 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 695166384 1250 695165134 695165167
    0x6150c07032907030c021506030c03030721090f231206070f090e0f0703090b090609120703120902030120030901150e07080405071a090118120b1308 65
    0x24900b0840d400081c0c0d25020180c0995000f4a44040141c0044821605504001075041c1d08510050122841100364001192a41e40a86402c3e41d004060314410100b4081e100501c5100341c0c003a15000100c5c5242145c2d250905415004035003020305444026520208007001d031404050700201030744841040590960348506040d50714200262000551a10f540d000c0d0152004640903a04170309901c3c2d5406100e00d08940000d4800003c164451210001107209151458040c0200d0006400b15041100d03525241198510503800300c001d0502405010035000341c41d90f8900003010340041006000c51000a00400003e40304030718100382118080b80700000c084c099481001d810713000700302d80c00100700042001c5207548594403440c5007400018040c00c0c800d02203160040d03c030300b040f2540d15445514403100800c0b01c1c00c451428403404205400a076900c5000c080103100c01d000100000303070a08500190242070504054089a6180041a1000514414103000300d800020250f22034074442e40e4120301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 695167634 1250 695166384 695166443
    0xc0f090409030c02040606031a0d0618121e1b0c08060c130f05031c0210050106121a0102030d0c0504030f080909010815040f241b030506150c0703 64
    0x41d0700d046004228123010303101d400401c0d1400c904408090350880b0410070601c1d8070500842e040da499041c0520b050070b801421541c110b1241c04403c9007040301d00300003070500b0f01c01c000303096040e848000c24005d0345800c0300010106480083d9048124409070800c9107100f803040e13010f9280c40c03003031408200408031010b01a010140d106803007110802c0d5598070280040101c0e0181503490f030000f0506002c82005c20f0394101100d1068010340d02107500704950b4000715102688a00046124400803502d03611940c8904040c01100203c1807c1003a22200000d540b4069607107540c503529a101003040c1040d000b1400e840095601802d1346005003143e1402814542241d05003900950005001042010012628060b100070f0301c10801c115a40b151151442c4c644418025200c8400707918158084204a9a008140b8142010b0114108260307a40744501080310130b040c4410580351406201e242d68070402e47c00b019200c50000143c58842200006040221903813008005044c030f0864007111008035040c4550 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 695168884 1250 695167634 695167639
    0x1403031909210b010605071a070905091305150711120a0e030d020a150608030307021614060712110f0c130501050d021306180504060b010509090c0f090409030c02 71
    0x2040d4114003902c070310107034510b02c010300146014005020381440f440107080c0b170074010503021604906182d088902810240c0c0d940001500d130704024000c904094803813981240d8040c19035036540900392034071030300c544040b82004800e200840216900e44e200c1c850180145884d101520b0190031108151503c3e507101c5201d01000c10080008a0100d01d008241d00f03084c50059006420701e11aa0b030345420242c1100d28410400c0d1360f4542001c540100d003000030f54451800b075002071402c88019800305825650301e5000c01c030b500c02000801c6009843e240309549000c0e45c004400714030100820404ea881a81841181600d4811480544070128000030102400501542c54545142c0b041c0c00c40d605840007406031503040446000c21a005060090b00107030582482d440000f0550b8646282034022501c42c995040f6903525030043c4024002644145d51520001342803207440c1c03c02c11400b148005900429803481d06101041c1023440c2c0052340100d4401c618010020010340e0501d02c3c001d0300320f440b9100c3c03da0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 695170134 1250 695168884 695168909
    0x906080d020319080c040f030f060f0c05090f0f030a0320030f04050d03021f020c0f031812010b09180c0f010e0f0316031103061b03011403031909 64
    0x4000c40e001000312841c20f103a1500600704510240400c0d01c0202020b00928002c00303040200003036840c0b8683c0d1a50241d803003070210190040c45400c0107000c0e03c0010946404640c41c10818000040d00003044542d02c81c010340d0408000442d00000400000f001c01e19203401d030203500100320806500641c120061802c1011468480101d0980b040c0e0700e000c1c954a0380c1ca5201c0400c1305014515200f250350300014402e20403241c0c28071041c100c0f0700c620a00450303903095182d0007250300a41020203104503d030500700744004600700414041001e50700300071003030040d014420071510303048051405c0d0040c3e0400403000c0c1a1101608115000b18084e80da01c0c100c02c00c0724007600c8012459460640c0c8103a035805416511060b6518544041104141c6110403070b030f40c18402d080108810213a0f1809840086004122140f1040001c8003813600b000c1e4018a860041e0140a007004034040e90300055a064420f002150380000c0410000b192841c41100f1921900010140610b83e599900c81585800e0f2059110f015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 695171384 1250 695170134 695170153
    0x80301080a03180311060f19120b0105090603010e1803031f0503011b080901061e05010305010509010e01140d1505090c0a050612130f1104061d040f02010216090608 72
    0x14040c1d0b40b43e50000600c00c8500b01d000000c14584580038040c1101d44003469860410001c44050201e4101403602d008501588030100e006201841044091102801c0c290f203001e48000004005101c140a510307a5421040042402c0d1201003581c1c222040070742e01102e030350741007085c1c0c0c8c04107074020349000034011000f083c0d0202e09400c040c003868610880d2031280e15089222805c0a58200700010800070003503680c0c07603000540708580c002d80c0108a0442d540446100e0901c000141910f105070800d034000c0064100410040d82900011411130712450180904000c0f124005280009a81405005100040502d0701d40b8000c507442540a15168130440f0040c01c50101440364403e1644290f660200b402d101c101180c0702e030b0001d00f55020300303984003004102c8059504c2d0a0503090a100a031141e10310b03070920b2a82ca09043c424680a402071100422401110180141d80380b400104018087d800c0c00a003d02164000c200b44028544d5140140d11400e444401e5040200f0740c0d8070036540184a006900c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 695172634 1250 695171384 695171417
    0x13180c1e020708123406050c0c120445110f0d200f03221a0f060f0f0f06030a14160e010c0807061103090607031a1c080301080a03 57
    0x504032405c954042c41011010b5844107030052500a1400310812402c000201d4012030600c24441d40b80b40716180c09031a10b06084400041c80213020022600004020b41480c0152000c611603140c1100000c41c24840300201c01307460054181d02c032400c070b4a22070120354405c9103c848000780c00840c00c1641e003001005010703803c0c41c2e900140103880d0000000c0c00c1102e0031544000600a503031148981502410104010030345240d62041540700b070322141c081c00e01014100c1621241e01e03420081c2800a200d075400c241c40014094104042c0d41441840295804130302600ca45d0000d45244030b005106640300d00e4680c0c1e6840c080e00c80011500620740c01500003600381d014500c0d2038850f18105985044203428588019134031030400c1346098404030014040e6900050780d03406089900002080460f4a030300b0b022071014903001c0c2c042c0c2440145030500701c00c80b01285421500c420400021181c881c404c2d003907994600050712520601900948001001184a00c0000b4100d07001911954400140d445150701 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 695173884 1250 695172634 695172697
    0x70c1103150619030203030c150f0f070c110d1115180405190504030e04050114031b060f0708030403021504051203061513180c1e02070812 61
    0x20701d520070980802160701400c005200607589002014040201a12900002e2139a040901000c0d130a0b44030040c050251040702c1b14490300071510507480d49007401e06098903071440c24020104410002415131031000d00500175110318003010085c0a00004075101d092440d61401c00a80351400707142d0410310640e0071355211003128070f49940030f072441001150f66410413010b0300b805482c001e224000000061085440c51103414081c03807090301e800600301180c00038070059880503405240e40c040a0175500310552000304500084030300703c0c206040c0c00100c070070014242d40200c0d4a2190122000b045c410100203e080007140154025000c175038010340345005d161a015421074004059802c40c00d4545813892205002d0760b00004020f107248a524403081015000c1c1d04501c485184c1e8030411102082280440f00079a080c25200c400b092001d1945100040c01046200c0681380e1008451002d0b17280c0c00e4401d024001c041c051010030340d110910f01c0060302e85035401c200406003c0a104940a4840503000700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 695175134 1250 695173884 695173903
    0x40f021f090f0e04111906052503050702092203032301081009030c1709010e030f0c010e0307170d030b030304030f02010f030b0301020c0a0501051006090e070314070c1103 75
    0x1c031404040d65695078171341c8141c0c988441c1541015413859504000031001c1030a01c0a0103196440d252142ca00ca800c503440072000c010202c44032448000d00034080303540001100c510030b8065079003840c5c9480d084259504c40d42904020b80b05002c0211941081642c941c002c0d442e002508441c86100100d010320b100c0c04044c00b0b1282030f5403079000c03207500f61041541c0d8000e840898060b003002d0240d141c5176143d1507111008495882c226500002d51414991b030404100c02c2c07000c400303800400441c0e921a0080d5981c51203055082c1c10310102400c43c106170b075020059400070741601082d101c414100d0440c6955640076102802005ca0304210090038682000025074007180e030455100c18110000d074006540140001e40d0084c209902c81c1d50060007038800740018002c85031148024080065075082160850310301a141851003a040b01301004003503440540c8206840c4d09003094121074030b035001c3c240d00034000c2d150110366901140c02003040c3c454100d0f142ca21100d00800042c8407502400381015103600c101d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 695176384 1250 695175134 695175149
    0xd09020a1d1b0c071502060718050d0c080d050301031a060102070314191506140a05061c060e0609131a0903040b0f13050d050a0803040f021f090f 64
    0x15484600030198040700b0b854010620315080340d2450844c10079009401c1209030010000c152030109a040103002d038080351529101181d02280f0403503440d00342d401d21a00303206240869070003003445142c0449074000e0865400b140c66500c6440c40c090020b070000d10041d030b099000050381000e0469051001d91007858141c1c05030482e50f0456482400c1c5445070610308042e841800724045003044c200b41031004a0380254200300f0190444880c0000f83c0d16503401448840b01c55000142c056124241d00f1401c0c0c9404641c016100c048006e0200c01c2440c0d00b4144001349802c01c10002411500c0381c214900a0f41c2c20303280880955120008502c030b0200209000b0040c86860003050440007070542417035004000002601e10300350340c8101440c95500540b03441441c0360340000d130090300c0d1004028400010001518404101e0005448840c5c454240b40d0019049a500100090411141c2034000315a20750051134440c4644c0e80d02002ea0703a48640f042c018000c282450004900301c0c031507644a000300e51070f8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 695177634 1250 695176384 695176439
    0x3040303020a121e12060512030f07051216060f050c070b071107180507030e12160602040306020a02100b031b0604090203070503100e01031e15020d09020a 68
    0x15030f610352855070424414001000540c102c112183c509401c1c1c842107484039580e90341c440150b00102e08086840e103512203032185200b02001808640084281c480a010840c68151141c10300d081040c00e11081c010101e8030640002501860898054400d245081c0250010084c0d50303829103c91040310015514040045418801c520002c1c000b1084141c0c13101140c5403064009561081c0e00c0d15241d16034000c0012042e00044c1c402da071045034450306602c22030340d180900002c005980061380321000420300c83d0408030009a001c100080341e0b241c40c2621a48901c045641d40d9a908215000350000701820006000d90141d2507100358940c061764414400050103070484409181d40010207079501c40750f05801010a20002410440c07500c0614440c004c1d40d15007036520320380030140c4118140280c003d48001c0351803a0040c404280c41116101664620f044540d400507428200302c501c4401c1080043c1005000040e013807090b040b580c108407400c0b0b1099a501a025031180c4105004005540c2115003040d207 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 695178884 1250 695177634 695177653
    0x2150604050118020d1b05040801180206071506080d0c020112270f020a03062304030807080910050420150a030c09030609121202030f1503070504050f0a0606020304030302 75
    0x8240d005240c003110510700000d00c49840703018208100000e02c004000300d00081010404200c007802144204402903031992f484203400d6001403028014000007030801102d440d02019000600c0c0c5c131000203012104100ca140d40e1503210010840f10314458100d0004091045c00030a98030b03240280b8098810b180708071198108070941c929860391000c9000c0d50320b200600d2001c00945ca031020640b01850003804041100f140c1e12078050307500c002c9a401501d070019600108030219612100310760308081c6d103103403001458540039045450240c0109441c0c094900c0d01d014001001403c40001d1042c108004c0520300b507000030810000d03041007038130824030800707020040624988e02c280e04c610448400d9041c0046c0c45920380e01c4140486231050f0045505180c1c490452100d02d801c0b0f03211860740086601c055180d4501000404c0802c0300241c0b038112801003240041c3d80540c3c060111102610300a00208041d1400386e800d2150041d0070703689044010701d00366001c203409101104035020380c1c0d0540c00411243c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 695180134 1250 695178884 695178929
    0x606030a15020d060b0d0e0303250903140c030c01030903080a2a05030a05060d02010c020d2102061b090303040605090a03230715120e10020703021506040501 69
    0x5400c594071074840c950802c280810301ca4544203800240085180c01501e800710a890300c07003107480301842000660f01c240304114134110710400071a64802c03401c142e480380300c04024065400f605550001045042c901840c0b026900c070000f122114480300300c0444a20810480041d800c8400300d1502400007420304001403614402030308041c0c1d1100000e100302546440000c03118000100488800000540000504c040500d1a000386500080b044403c0c01c68403480794006004060103140c024010315041c1204400d20104d41e001404a0318002000007a0b06a202ca000b500c07094221074003585070181d00d01e8008172810440a0b2803820b50080d0045141606084003503540c5e80224400300c1c0d0001c2010008000503010f41d03100e280b080c44000b0000c000c0601c0b841000d00b403c0c030329005100c11028490150f04150f90100400308a1750800900003082d540604800341800c203049034104407940005100300403d44d001030205240a9805401040f079180e900800050758000c1c4510404c0c1e54001c102c1c0c00429 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 695181384 1250 695180134 695180153
    0xf1905040503100e0f0f0313060e0901030f031101052a030108030306060f0705100c171b0901030b18010e0702120f0a110111091206010b0d200309061006020606030a 72
    0x8003101021218148015012280751940c0303504406d0b1260400b2400740c0d100440300c4507403400b0b00503504190001c5520702c4040391243c041444090080f68540d441c003003d15000f04414108040054002e029900d0a0440000c1c1c2195180064549a14142800e540300d1500c0b0242d80c140c7d00c07800e0117140355444900412501e0b40128007128009401000310400107141000004500020f02c0008115203a40400c050301e0102c5504580105c940c0810401240d0351209600c2c40e101c904140350540c40d00d00c0800101c0c01003940e00c2d482c507080b44c44c009055811108070003450741203070820301d415412541e0396079040b030f194806d03400c8032021048184101b40d05644079802074000c440340380c0b80804001c00032811141c25611f864003600005400010401c044e41801e610111340e00c151840140300b15450480070007054824145071215059541d41101007200385a00c42500301d1540100c1181c407414030808280d113900c5d083d10001030706c0c0c1c0c040034000759640c00441e1243c46688014050003100c0340130745404000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 695182634 1250 695181384 695181401
    0x5040b0105040b0c0601051c030c03140f07061d150103020616120806100e030304051c080403050c19060f030e07050d380c090102120f190504050310 65
    0x610030180400318450400f40040c0844840d148000c040a502d4242400a164a050240f2044207120f0b02e1001c0400c1e0401e92000b000c90381407a04492908031f03040840000d0264603902c00c942e07180040d4500030f000c40d90700452510200080860417a01e1181d281a544050046d5074104411094004102502e41400645880c0c01d400301900507050941d6102c81041124010020101d0040c00611101d07080110030307504040034a06010b1a103900704d4001130341e03e000b10b11840380300d0440c0714180d2034064850b6441850f0181c0c420b41c400d4569459151245e01d0359080c520700da0090101007840700c140a03039500480202d41c13485e145c1d007414a400000441c0a0407480710303405503e1107048000550340d211000310040e940c3c050300160b0000f440c012810512120218010550701e03132289009140b401e441c0540c0c681284680d103066645031507040050b4200300030106404050080401c90741e50900061004101c0b031100480c602c0342d040d0726640150342d0b50060f80034641c3c25500101c1150000c0002c1ea1100c0700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 695183884 1250 695182634 695182637
    0x180921090a0e07090501180e19140a050604140114010207050325080f030406050c0a02151810020d11160605040f0609030f032f160603051005040b01 65
    0xd00300544011494000156101101030181e01c1c00304080a6400120100641002d00c0c00e454280007170306c9914000d284034050700004500860100c2d2041d10640c80305501800400c20900500c7c58402c0508161034003121111511400c0c1800106549403a02c1903228200229030303d550281d0900c1c0d06141c4200c0030300000d6056100f000c0000c01c01d5a810000d070003100075985a030702c1d4003903410302416225080a40c40700c05994465010313140250000b0050702c0680700c0506d8115103480c19210510314100c0900750180d0404108030780b400c081400c0354001c1850011308980309508010b020280f000030100c020034200103070401540582640e01c9514140c402660b44c030300300c0c5c920f81110080c0c41d8268203907501540c00b1620000d401c0182e51032020803030006013030390b0404030780310b9281d40c85040500c00100402010800f10300c4446c2108601c07041400300000040c1c3c29000e80c040280d621a0750754a00d40980040341c014100f00084c0c185c46409410702c190210003103400106e18000c20310000d00001c840030390 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 695185134 1250 695183884 695183887
    0x90d230703110609031b03041a070201180f09110304051e07030b130c080a050607081017010b040e210f0906030f07080f091c090b18180921 61
    0x24031010100311850050389141c000d550f841300f220711806804081e0002c0c41c46c0d5504144402c00c401c59005562004501280b8800784c6e4604540c40100c6e50a0242c4e0b1414064007600380d00402c498241280305000c5c0c482c0040d04001c40d9032030aa40040c1404222070040c840d92015040000e40c0d41038503407600c2149259030840c3c2c1c4494895842d40516541101c030980c0c078403802c510f842c040c0080550010b00429000c009011841c10944a0343d441d15401001c0c10b080c0300c201004610030300d841002c41401003040701140b4290f0383da002c15603030107440c0c40442c01d4440c0d400c1016202c84108041030f4581e030611141c2c08003134404580100101d01e5048002850445542030040c03841700d44030440111320529015803004207a150290000d040035130b01818601010200380100980c0400009036084207a0719145e010701d2124207018110307020010394105100f4050301089640ca040e10349082038040c040111440820003501c1c0c0406000c51303201720384404481c0e10254030701c075800042031a40a40d0120812032903 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 695186384 1250 695185134 695185157
    0x9030201020d210b06130617060a0609061412010602030d20070201030e0102040b130e16170405120f0a090503160b031f0f0303020c1806190518090d230703 68
    0x10b43e074400d0242d0101021428030b9440b000f02301180c0103400e9000b40102c80a107401428550010040700307a0340940001d02016070741104c00100640d05440c40c904000c035040b02c80e580c59440094803504110503010314a03052036410107204140901a50140c0c00448909003001201d80045015241030361461035995070802020070f500a00c0802000000c031000c40400700c0c2c17407070541c5842915000400304103681084008500080d41c0c03014504400505421250580d074856080c0302e4148981e86441c0140000c0024000c40e4905001024041040c1e05848031271540da6100181511130030103000c0c00808804002c010b20203034002c000030b16008a95103005042880141904c0b00c265402c0707400200300d03800728110400070160304001c010020781085d100d542000c034103d00030740c100c804080e0669104400303401c8d0303000b40c00503111102c4004010041c413112541c0c1d88891101c0303490340309442550480c0a0f41189600560044411201214150b500c0006405100c0f01074811034100d41c0c4c0441c00c201440e400d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 695187634 1250 695186384 695186407
    0x182a0c060905010f020309100209061803011508010e240601141201031104050c0a0905130b0d111c0506070f050702030d171509040204050a090b0709030201020d210b06 73
    0x10544d04180d14040181d0340c1c1800c20441e440c1c40415000c15220301c2c010480c0f14500e032a01d105881443c00101032050011700c40e200040d001d0010100074080f601c1c0802030024000074150814900d0f81c07001d4080e208c0d0002d102c40100c5c0f04c4c12041c0404c0c54001c0080c0040351481d445000c040c000d501120320b0b2941084480c040b400b202080a03442510a030000c040d81034030a1405106d280c2c0c01c03540b64141070b4500301c0706140240041c11207100322417190800c0b40f40c5d110082825040060707603580090180d4044011480c107009900080008207010f000d00360106215980d00720300c03a120141e0400014030941d030303c070007040341e07122440404101000010720142c80141c40070445054050328986441e59035103120450a01030030b0009290304261210403540000980724502d000e03410540540d004140782c0c2e82c00d07180c44054010034400401c0804d50404201456a00c10508015a4400d0703003039440c0c881d862401103501c000f030014403041200d090500e03030325188142c1e8064101908082c11130750500005001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 695188884 1250 695187634 695187641
    0x7032a12031803080a080705120414011107080d0c0801180b0109050a081b030705010e040923060901060e061c0f06020d020a02011b050a0c0c03020307182a0c06090501 73
    0x3c1160b901300701041080284d5000320701d1a038040294a46541003201c03031000c503006514050409404a03004480440c0c07907a4003900152020003400200329980c0c1164034000130a0341c0290402129240f400340741d600c84d144101d110038102c921100340440040d480307a800d94002c09440310b46178144014030304005102e8654102050081c5a000050424850309820340035004500360384061003604221418422613802c0f0301104000c05094900140c0700c20780340340400c991640401300c1510b011019088400d60300e0b00042062113250320300c000303100f19540d508600e43c84450a84a0135402a1400c4481c1c1c1914181206451600c1c0a100114902c00841d00c5090480e8045620340b410a600040c45840407502400340c5040c503041d42e0480c284030011000c0040483c002c07041c0b00c200304400011000305000000221002850f0000c040d56601683c44035203d101d1000c03c0b4480c014941401c149810012401c1c40e0f00841035480307031071422008079580c0f08880e00c49006604039403a03070307480e800c45000c20002d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 695190134 1250 695188884 695188889
    0x408090130020904050a110a20060a06080d08060901030605070c020d0516050603060604060819240e06090c030703650402040803070507032a120318 65
    0x7100140d650003100280000c0d24002804014801c0c149000c1e12140851034003210500001458000c00308500ba40c62012045503040c07210700d4901c0b441b003e020f100c20980d803054003212985021a15121035100060302c17101411500e00d0f90104001c80100b003c204150059a0700410310328085047e900c0c0d0364002a5a000c3d8840191110780c05852600d907804511401400501011149a41149484000161144140e02510302000441801305190855085d0301c81d002c0b0103201d100740b0109851580c0c910b07007160551440b01014084450003d444400801054001c0002600d12100c50761a00c040c1c16183c0e00140c81c20080681c1d444c00c034909013460241968229002500020103030030050201041d100d111009120b2602003110351042c3d0141840e030420281655410311403424401d00700050090086038481340d078030700000601a040003070100e99181641d00c41d800351030210300311010040400b03401720030000c030486903900144140c4000075071028083d4030900d01800344407504030b00c00ca038144195 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 695191384 1250 695190134 695190227
    0x60c14190c080307020303070224160b0c030108030d09030e040f020315010e0109060c050c120f011a06090607300806030109030f08040203070e10050103110304080901 73
    0x9590400400164107101d6009000c1c1e4002981480c1d0340790002034480c804c15100a1084090042c00b1603044904160800200c2201100648601ea020001468505040d404481081ca00c60014003200100d106403810707942c02074011410640ca403040d8100600b8444001ea0070701010710001c5a0941d2140900310705c2900401d405a140d0501910181005000c1da2000341480035412050001b40d9000f644001164000d1030f2080008070036003041410000e104c0321075500000040b020301009540007503134000d9800c0c0c80d4000c0001039a10b9040c2c1160340400b140881c0e0003030080054803c1c80c0380c40c401a1600c40c2c01880340640d20b0034401c040c0c0044d80c00e6401290700c0d412060201e944030740d40041859600403000d90080c0f06034403240d03a0042941c12004000c40c2400004c0c00820b00f95101005500c01030310442c0d040c4c2d04141001040f8002c025000d1191303d00003400d050b1490f05001d81041034a005680c08000b107802d04082c100190340000c61400c10313442c03003e00c1010101c18500b81c0c0c1840340c00613459 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 695192634 1250 695191384 695191423
    0x30307050703030b06030105150307050705011d210307050c0102220609120c0603110c06101806180507020f0a0b15040b0f01110a200909120301060c14 66
    0x182c540681544c1081121511450b820700040005444000082c40d540418103851a0303243d50700d0328280d071325001b0302e20040c2266181c03c0036041440d25400e0b44d02300b03254514085500e804d90340c20b86058055070080e0782c542c0251081c000b1035000c90085000c1d0124a441900140c1001c02480702c407500d5444c0d0304200c2d815084104010810550400081c1e00604003010b213480904c1016111694030b5400e0b031041d40c040541c2c1e45056201807420304284c5481d05502420b840407810320304115044000e490107a901d0074024071404c0f408200c824032510013150740c4403100c00b480110600100303006050007400d41c0b095004246500a401d801441141d4850384a8a010586410700b406420540d000d90b0301030500031447d00745804002d9490110f2040649000d281c60000785290049150030041e10040040c070420803e0f040d12194060300c41c00b0281c5407400d9030405200e07911048200c0e44c803210840701f05c5210320104014000c2c44d2191100d140194005c0202410180e26902a00e19000c41c0c04103d1404018 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 695193884 1250 695192634 695192647
    0x251b0f06061706042402040e0a0603110f0315070203130305010c020c04110921100603120528030603080f090a291303020d031101050604060f180b0303030705 69
    0x26039036500c11080b108000208840d16190f0b8624801c810b1880e8548404240c03841c1c442d014030300c07507012100a82003102c03080328607040040300000a0100c60200f00c8034840c850502d10329600b08050305a603214001002005011710561000c074101802501e11006c5000800600030381b6604221007800451242e4000160481c2000e002400c00c050941114402c60402c2a40102d0f000a28140c56000a0480d003046035244581c40d51602c03800032210000b098010041100c8c0515240e61003001268041c1c41c140c1400104144220303405e205404000410b40c03070424820160380707030451605c00c950030f00d0b0600103030b2241c580c0ca900400703400414130189a0000001d0baa800c1d0700780908030200030000a038802d541c03580e0111040120302c189030b80f990f421003004100042c0c0c4604d0891180700564002d042c0c81000401420000c00c0e90300c036801d51803030960a00340814031030f040a10840e01140c110072405000642426805c1c1803402c6000600302035142c6420310223a01c0e40d411b1000794054100f40d07c98565505 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 695195134 1250 695193884 695193899
    0x24040801020a09030516050a0e0a0920010e0f0a0614120103060519052404060510020c210a020f190b031009060e270a08070b251b0f0606 60
    0x1010485107046e885104c503c2040f49444945010098614009078684141d59182c1c100f00181543e010140c00c54122000d030070011442c000000086400a90750046142c10f10401c0c485001400c01c009600008560b40420810b4802d5046804440012803002d10b080c1c0e90000c5508040820381042c0c5030b050303450082c40034485460b0720070440011842c605000520380101000510f041990912900303240000705d5800702e9445034000400740100a21940207000c24060080d613400c0d54094050051600c0340206122020440303010000b8a00d45004000281641d0f00740030900a0100310107402040c2090403110042401da0080c003d000c2084400e6221706d8003144408802c0c00c0341e8030408020346002414480031070341100e5613a018640d240c124040c020b00350b0707144018414000c4403070024024041c2c8401084960801407440500907004c01120b5110081e800d40d082c02c2d11320300b07610120000ea41000b0902c1c001c903c2012182603250f031085141c000c603150103040d810304035402c5803400d544403c14010301 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 695196384 1250 695195134 695195143
    0x313061e0506040e0705041e02030f0702011805030a032714010c23030402010527010306091a01110f01060602010f140105180a0219030903020d0302030624040801020a090305 76
    0x301200c3c10700c2424580182540c480003030340122030049445600c0900300440b1268442c4841618440441d603900d48a03880c0060300700d0a440da2401542041102541113075044072150702c0c070790000d01548c40e11014a000b58010072401c40318034881a4000540c40e404081000c0350078145010b10302c100760280c1c10110107803c5554800140301030205242c072075048409c00b80c00c500703030050840d421241d0726200c500068510b400f1390742c501651401021440104581440c1c0b0b8001515420380b401d01c0900d44410100e4192842c508000c0f061500c108040c7d5099840703464801784c280052000d4540600003280b56909582c180c2e080900540c0d111400e14210008510503420782d07040307018059502d941441c000a2408907011407a10503041d4082c085540c52205604a13980104511003203000c011029002a014100d41d110560250080c110500c000c1030090003140e11404000f0b0030010180c120345141400e582d40f0b4040f1065030002404082010b5609100038002500b040d00c4160f00c030f41c80d500e803581ca0f0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 695197634 1250 695196384 695196391
    0x309020619140f090105071b061d090f0a0b13110a08010f06020618010204081c18060509060706021e0910030c08040803090109050a03050a110307020a0b0313061e05 72
    0x70360104180c0010030600d000340c0e11203104c02d180807595080c00b0308102291031080c074402c1c0141c02c0844400a0f80580005002c2125407210892a403050008802c102d500070b0100c43d020700880701000000c1d4042503d60040340703040c200034640800020703000503075402c80d0806511001138241c0081c0d005032080d04580742c94014040041c03810310f41420890700039180c020151a4454034441640d141d030160b00c00b901504c001d40607070f104035203e240200c00b46408012541da07030072021505a0310b0b40c00019400d5a4003405903000c0b5111185410000d030240b018641c011241562602d40c00d00c00c0307001c40c68035000003555040c601c2c200c0640b9071050700f0030001d420420405003001e00d860040c03d904419044501583d105070450442d0f40c807a070300c1c18007180c0540340d8460010002c0c05420038074000c060704003016218508180d5a111603c091f40c60245940744031f581000380d4031511004040240158030001154000314001d211121800b42e5a2003000383c0300010400d420340c804450001120980900c91a5030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 695198884 1250 695197634 695197667
    0x13050a0c1803020a06080c25020f04021e03100b030a05090d23030c07020409030c0c0f081c140406020705040b0604063e01200f0f09010309020619 64
    0x51451650340001c60030003492245d00c0602181e08001401e4128040546031261600300800c2c6180540c1c1c4050b03507015a07005012880b81c84200e024020b2810300c0e109840300d64240ca9210750003194007158400158100614090003221b2400002c5540910580a10301542403400b0102da24100120000c0c1444043e0f0307517038030802a400c1d41d001c80c00303000750400500030705440001c2940e076141d150003043d10348503c00029400500388103004007050391092a2080c0b41d4001c0c1d42c003034801a1030b0ec40e00d1103542c0d030350301ca58111a0b0141c81c2c6807440e9004100a9110a80071382088442c0d03d010340001c51141d0410b51100c07026800c880760410040c20680a1141200421121240741a003803c038081d0000042d107440c40d810902005400948588040299003032008054040005007912807a180c06003038010940c0011000398101d2800740700c00a41614580c025100000303040c400c440c1c1010fa900c1d00302e04265810161960804405038030388074000e1911040c1ca0b203075100300e0b0200310300207807e8185580100e003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 695200134 1250 695198884 695198927
    0x18010f060c05060121020604061809020309030409050a020909100906080c09010605070302010e071e0b0301060507030c0609020a15110706140906090909010e100509030307030b13050a0c 81
    0x6001440214030f16040d0b0b400e2081c01e011813615040140041e16101070001d401800c00180451140c2d0001c4d4005021203c1e02e940c04030154584449406a000c00d03a00c20713880c1e500c207210910029040da00000d9029010b4103005050400c20000900620015151610540710aa400b8004007a8038001d0310082d00000009041811110006c254001014440e4008000001c40e100041620030b4002e240c260345001c1c1240c0f08039465103041004500c421000c010142289200020810005c00640c0c1c103e41083c1c4501b820160b20703071820344407082aa5021528583e407584a50010ba0315901201c01401418800051100d01d030207018204200c0180b0b5074100c4c3d4007a2078108516076025920741490394440d84020740303c50b03407000130805900890080f15405400c803410082c09580c1540103aa06a01000c01c0740c54544400c0ca0075400c0b11800d03110b5007a02d40042001402150290b0880d000f4060003900300c51544103004803c00480b04151581210305445240424245078020100070300c2800481c0c121 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 695201384 1250 695200134 695200157
    0xa02041728140f010e0712050d110304030c030b15010305101707090615031503330f050702160503070e0603031603030504170909060d1118010f06 64
    0xd00c0d500901d8041d800c0300d560314540c810410038400c80c110381030501101254148080c111566001c1c2042c8440701c1031901c0740c00c0d0001b038181480040780034034a411101500452000d141c04031240a180044815103200411002002335030501c2035900441c01268540c0060828a6000c600140304c00070140c109030820040c44010708140305c01ca411100c1002c031404c58000c0c11910a0305142180e40031070101403401100103a6001c8041c4c07000442c2000340e5041220006521480c0c00c20442800040d00c4000b082004101c01283d00746030b07140303c00740c42d0320160744103041080b494260b41160440003003558450701445010f41e0100b081200f00c0c502501048040f42c140f201103503550304c45215144800511802148031503c3c00c4c01111a0300007101107075522843e090402402038241030702c0840300080d010358604100c400f910b06682c2260402803030004107444400400000526580c6c042e148461082c07115101d6944d40c0100405031600d21820304140d41c580030008401640d07070391010741444082100ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 695202634 1250 695201384 695201413
    0x1c0b06040b060a0309060e2b03051b070305090d030e04050609131511030117060105040c0e0103020d0b0910051503090307030809031e030f07020a0203100b010c08030a020417 76
    0x20741d000c8140f07611380061864954180b01c1d0280a0002c001d08450041001c50301c211440312220003500d00c10405202c03150518510204d003181c2040f610801044010311455905611900041480e00d0080c80c05a080c00c000000040300c180c80003408a0104001700201c40c003a04080c000c07180d011808640c030300c0007032a008000061aa6803108021b14440f140040021280016070244102c0c150f1910120b0712980c4032403980303194a0300015040100d110350400000c681c0340a014001e900505a41d801c4419140071b001540607410034078001c100303103813920300c0c101c40c1c0d4403080d41c014031a0070300c611003403445031400741480030030107104400c80001c020403c1088407000d400000c40b0078043d414a800b4440780e442010a40c00e6004100ca0f00103580a1603851903250241500514042c01d034010403100f1030780354a00d042c1d0361403510210007501074100d03005042504c0e019a00c69101081c0604040c3e0b4800e8003942c585603036500486056050943c046030078410745410b8200d9542c2d6205841c028a00340e40564070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 695203884 1250 695202634 695202637
    0x4120e0a0501050c070e040615090c05040e070e131d0105010b0414130504050d170708010b0d090501110d180f02152701080a20181c0b06040b06 63
    0x81e18140603001803029207964041040c80010400e0415401d12030800b40b40c0300c0060004d01e158a480180030047c00300344140c041c4580700015803152034040c9000e18000103c1d040c001c00600100070f201040b01c10700c2c015201d008100300681e61280001440440c240d890520188400c400306400b80e16150060003544110340845d0305881e4400701e4810f0000c40c0f0070009607000c010030540c0d0100d41c24802844100000025050000703000358407020441c02045004a07043c001c11075004000403518001009181000d50082c1440f00403240d0100701c818491325424250342c060007881031030610000d040d002410082c890742420a4044031040040845c0c1d48842c4801450700780d02900c00c1d1000d40301001075004030070881d904200c2c418510741d802c031f03035100e86945503000d02a2820f0208401c01c00103070116415120301c0100054608801d00000c050b0581110f8980000001099080c280300d41e0022598a41e075110a0601144045186250780c91421810b140c5010b4103a6001d00e040c006070b015a03580c0c4c0300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 695205134 1250 695203884 695203889
    0x1051501140729061804030c0605040c080d21061a0906040f030f02040f0209010207120c09092d020f0118090c0c02030c0907080402100c080a0804120e0a 67
    0x40034141c58219908056012814050f000203110121040050000300714821951090300704841056a418030100036201e0b940d001c070b4008001942d0074618a00203411940308940050107942c90407015500e070f50615140c511855200300126801d18000d03103010030111140c0e107400c0003010f0117200c241c2c50298082090315080f07080303d02d0318801144400c0181c4071002580c00400f1443e446d000305695a0501110003d000c0d4010380c0581e040c0711080300c03150504d00071102030300d1040c0c2c003d04200b49091030074485c1c07496040c1c003180c500d14502030029860b901805804c0c00903020300801d805018940000361200b4021100c01520350103026540000740c0c0e14000070381e40181c030a0800f07800d0404000625088803505d0b42041e603e8915180f00a004990b01036a0183d045200781c04590346014054100008060708071207001c0054038a40014005051032020b0401c0d0030302c942007a120100180d565600c00b80c20202c0c40358001000c0701c0030070051152012804200c09524140113007a018501d001c640807440c2130 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 695206384 1250 695205134 695205167
    0x6030305031603140c1b15060d0206040e0403050408071a0d0507030902040e250e01030f051606030c1e02060109020a170114040608030a1b060e0105071101051501 71
    0x4560b42101c1ca406900011004c070b04038018400785141000080740740d90071449041d910880601e682644a400000f08041c111241c0002c4c14101d540b60070421042c00e001510882e004901840700040c0c21a01c4003110380142d1082d19483e480d01d06002d0300300c1c038101d0240d00160020103e1001010b1a24224003214150361140f94085030740d581e20f00c015006000f41400094100d4a8a0320010481801013646107180c1c06068449040200c00f00707003034240410134001c1c010441d014100410014440101e8482c19520480075031b000740460140407524480f0a6002502098441541404107030b40104110024061703140740c401c0a00c2d0031003000b5540d400501418140a600044144010740610094003c5400ca0034010b0b03032a40e101c0081090305c1032991003031b0f4021424007102083c0c5500200c07c1e182d803440c035a070342c0d05680c42141c01c1410071440709400c20340744e190759000e00420511081c06400e105100719104c1d000b100c680240190f086a00041c41e2071900d104440320241709a912800040f60340050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 695207634 1250 695206384 695206411
    0x10603061401330822140c010c150c1419090608070c0201110f030403050c030f030405090f0408070209090d120204140d140303091b040902060901080a0e1209040e010603030503 77
    0x10048540840300c19510f60407a2003020511000c10080001031060585006c801905d40000203030005490280c1039000080c0058107960340481c0d525040c0c1d0000d02c5047c0580b800002c0d051031414014043e80c04001086044812154800c050a80000900000380100c0c070f400740b40c51819420083c20320511710402810446810506044170340104444105000d007542078945c0e95960745030490392a9500c440d41806401010b054190800d0040143c90440c1c0c0e010f80407144544d6800440240944024001c5501c5034084c41490096140d003201580300d40031004c0100241d4000c0340020f00b103d4503001d071b004945401003000303004254402815580023030082e140f8407841700c105d251008411a44140030b00e02c80c4000300400203283c10015181c1030034800728041c0404032109800340004d482c0d5101001e50012000c01100580d544199030081d4842c001100016001900a2416040103003107041c0502c181404644400305140511031a140044018020400c00785541c0e00039040d40401030440f90400311 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 695208884 1250 695207634 695207641
    0x41b050a050607060b211e030403020108071101150f03020f0406030c2303100903110a1110050d0606020106051c02180c1306090e15130e0106030614013308 68
    0x110810b03450303030501e03441c5a03242d18212034121b016034070940c00c8844403a8034000340b1111308a2501102300d50680740c0680d00c485660b600d6a1098511428032620302003250b6952950f0084c180b44401d0b5840641030000c2842400c03403031801001030050006034003a21940c0f41800800004a03000d07002c0044480903032050f496a0078100c004e04840400d02c0710303160140501401c500c0c560345681c0c4a02c0110b4441e0300c032050104956000160b071400c0d00b4a0040112440201c1c0e0081460850100b40300307040c0505c4c1031440d02c00410000010764406600100c00343c0e445150034891450515030b02c001c4149804120320280c2e40070b400081036803902c451005112000000131540d81c851100450700b40100a05009800550f02c220082c5800280e1003003e4514a2035030201d2517060a90701d00800d4048018a04105c200400300d8038001406201480182c0c1d44d1384000c000002251801034580d01022211001a2503150000a1003a03441c1d82300440c12440c1101428440d40d554811084040c00792480d01120595 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 695210134 1250 695208884 695208889
    0xe090603070509010305030306040c0c05030426030a02010509060c36150414010813020907030e07060e0f03060601020a0807020f090f04210903020126041b050a050607060b 75
    0x1e036420281d0060542c90000c0306101d4000001d50003610140c42c03c0042103000070044030b0841c0b480380001c246810410081000e1400d80c00b4946100c507110440b44441d004031000d0340c1ca0f41d4000c001c43d5000d40d450f003040006a40c4d0900a0580c000c8059120078600b140c101c1014a01c0f10500c28941d403130044003000016400ca17140c82540021001528010075920180020364503500a889520301c01c0200c82042f020552043d410745000d5600e030451034081050550030481d4401c001041d2004140c0c0c1e5150b041d030106000c000c000000c2100e80c8890441117107140911660403c501041ea000b03074015403c0c8291030740e0020341c10100e03603003160b400b60701c408903880042c02c0761403460015907009401c1c0d005c0c80503c030b10a40a00740154450400c90504004500120190b0701011001001007516224200095405000c0300d0320f062106000b1311060980350640080b003400280c0b030580f65603443d10000d07403da441c6c4d0341490010700800c540014045150030300051407440b44100060120351510034810568 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 695211384 1250 695210134 695210143
    0x1515050f070f030810091811120304090b150c06240303030403030605130c080105010c0c051e0108071d06090423150d0506070507031713060509010c0e090603 69
    0xb40d204402d400814a80d0030000d0401c3d00a0390b41c80281040c0042c005843c6642e8416031400600c00300c03004000030856198401c120450301c0000b07420a00d0340d0302229840a090009201034184910005505000c0505100b15208210380c034a0020b03100b08800440c045002a91030703032012144080031130003603010039010950403845e03446640610021080c0400c054140d0000301c03d4a005031001542289080005400e403104148034002003402d25006000c25403150750084105406141c400010325500c1012400501b5102002940c40c044008150071943e031107840d03103070013008614000380d845120403443c0380c1c03001c0701400e100c0c40f0701c10010b5580324035141c0e03802101448030780031203000d8142c0071050844c40114003280c1c08004c80d05800440c01c3c0034907060040e810703101e4002c80100036075550510240c442d0b42c440b4809800388a8082e26200d01e5903002c0b0b001c98410340c2c40311a0302e0991011898070383d05440c0c015001100a07414504500f4543d40c0c08480003011000c22210202542c0792030700400c2c1070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 695212634 1250 695211384 695211397
    0x402091602030c0a0606090e2410050909060103030e0901030308060f0111060712060801090f1119120506160c06110c0712110f010503150604150c02041515050f 70
    0x50b0040060703135424011590700007012219003e0050002c0214407900944510b00700d804413120320091044e80c12641c00b40200650701aa01d404407016503912440000d03110601211600e850f54880e13401842010351114108079802026214040e10707504503a00031303000d203800402184c05010046040354981e0b2184900902d544200d03401c0c2d903075a04088800600708280c0d440740510090170308000164502c0144500a001c1e60002c000401c1c0c1d2280c0d550b10035040000d1a03040354402c3d100b40d0210007050404075a20000d114405180b0302e02d15031171a0090074010020306010003009030b0201d5900540d04240b40107805584a8030000b0001d400003031000d00e600806400340920b10981030007041c3c0d26040c4040b0820b07240601070910302d0901407400c00c24981d151003503580c0040c0c0c0c188003041d03001c0d0440c0d8800008100c0104036500303168071001c1000c48980c0b24808840000d0105243c0d0003541400e105468150409401ca52022402d1884031940c450200c41c0e10740420000149010314440c16100b42d451 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 695213884 1250 695212634 695212657
    0x40b1228170c0a1a070f020303070e09090c0a0f170604020f040f1b1107090b010912060b03060f33130e030325020d17090c12100c08040209160203 64
    0x3e02500c41540c0304d012110840e44170300401c680d0206030701e5a40c0008140c1c0e02c00d4100d0740c1c030081c3d00c1c0f11207024000382480290000829100f0402e10f10103d035a101c0050004d00341c1d51146400c1e6510785200c84030884030b480c0c00700c60a50040c106000250722141da21407201e07503050320081082001c507107500008055096086103a5201c000814500383d03440282864203032020b030100c42c045071320744400c441281c54600c2800d0100d41c8440707040100c400725860b40045640211000034000048a0100b4100002143c41829800c403040411503104580503400c040ca6900001c0c1c1030310b01241c090b150703d00f0300510b80320342d1049003221404080300d032103a001040704890580559072641840744118010384100552201d03106907813041000c80c00e1000401403000300c0305513101c420f000400e1481c2e000d008000b038000b146901652200b2841900e8003166003800152407001040d9108030603079580101c0d081d01e2010010802c08009100141c2d580600745600990f62504007086c040c01000180e165100da120180b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 695215134 1250 695213884 695213903
    0x90403020d02010c02011b230f0714010b030a030513081b24040b0f040b0c0709052a0c070e090a0303050c030906040b06040b1228170c0a 60
    0x201a40072034101c041c0c0485800900c03841d0200441a400c1e941c41034001d904003400f01c0001301540d4410000190140140c0b101e0404518820103141c68680c4100b912220307100000070144104441c0c0c3c400a080005050700800009010400003038035055041d0000c0e0400102281c0084000b40c1200c99000410442049901d00d04d0201c419030350b0038910151443c42003060340d500c01c5203070161044002e00748202d43d2025152038103040b40400f00b84c00081102520300c000340000300c0d5038445440107003482d01d1001c4c002c08003580380989020548900a00d8900001c25440e01645250100544140c0901440c070126855544249940b443c0021540c06241d103a02c0090510540800200d581c240e440c0c02968140126a00c043c400440c0d4401919914010b6011398001004650030440054109800900110300c8a0003400001d98445004400c1c80090b00510142c003494411410840b5500b404e800743c590f00d20399103441e9224030384a00310103440c0640c0006000c030b468080c24450180c90aa1007907004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 695216384 1250 695215134 695215141
    0x80a030801091a1f0e0904030c06110f04050d080c06010308040e1e16020a020603010b040e0105040b183106050a050c04051903140d0807050c15041109 66
    0x101a03840070301c1110103141c94070014120700c0d41c0c00300e00100c00c0e61000e001d05582c150038016030302e0340c0c041c4a0080402c02c4243c8010148541e5500310843c0928000e0751484aa00034500300b81e0102c03110b03598a001c1680d4204601c40304401c00e40c007968100c850460f000ca10101440c20311288a114420b207000290140c200003001300f04015019109852041100a005543d042c421800c40000d41d4540074040050354002a20741c2c0920340f4100c01c1b1041031064034001401c03503022858030741003a04441d200800c042414004040790304941801000120303814060020754101107582100b091044184151000c1c00049240c80070442500600030b03141c2044100d00001d130300c120f1101c400d80c0c200721801c034101004580300107258007440d4082e28056007103500c0e05181000b04036030000100f04640c1d03600c08001000011400120b0750082285e9102d001d40041a03070719200602c0e203c8024100380070b00c4024441940311000014480c800042c5c42c00c800c80907611241020550814004c821541c03101911040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 695217634 1250 695216384 695216387
    0xd0f1e020114071407090509070b0a020304052e020c040f1b030905150408042c060f040f11040807050105030c19030608010c09080d0912020f042c0610081504050304080a03 75
    0x145201d08c4c240c10507075044c09d8480102d48074921803000100d0060b072040c0020b100f9031400140da005900c601d00310040142d00b0310100b010740340400c10712080144c0c01001d14480d250920340240c02c60001092410003d461640400c0081c1c8110f11900e0750415566400740000c005080010108060040c29605c01030700d8240b801507459803060003a0400c2c980b00070a0500002c901003a09554101003181c030400390340d5003009100301c00034070090850b4803a4540d14402030120321031003440da07280b9100040c540c1c0c81341062022481d0101a600250400004200b004910303100c80040c4e6140103006403c80c101100c03658401c6000c0c2c070300790704100e50315442e11400c1041e1130740286d60310381140c5050f401c0c0c0d20043c858100903960001607200300d4051100b411030800041c0382c01140ea6030801c80c02030000a03060030580181c90409014130200c0d05041250600304030b0701104224043e44490005c4194440d9030801e2021a11010541010302540745c10b04042400c1207400e105540140021004480402d01e40d42030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 695218884 1250 695217634 695217641
    0x2422050a11011b053c0309040c0f05030a0f0605060f03093306010c1205030411030607021504080d05090601032d0308070c08031509090c01090302011d0d0f1e02011407140709 76
    0x800c0c8514900a61703d03440900ad00a07901c45030b0342035201d0364190f54490340b0b864060845d1842050700705075500000315281d960300d4050100480500c1c87e00c3d89074582165101d01c0c100740f04032441034007034121040c401b40000030b0b9800e1050340c014444c041c01980b00d04d40160340c030130320040700203082c5401c0d40f032051020b42c1d00401440c45507008e140303614041f0b02c602c010705844410641c1d80e0ba0042c0c000403034480c0c0038007842c28242d41003442120418a002c52001d01c2d08201e81e015980100c20780c1150004000348102d00102541204021070741403c1e0355065600074000001252005040c0410300c00080c49103805440e0f0015441e80110140c0c0e80c3e8070f8555488401e050100e10401c0c44ec800e10004500c180c02e00242400604a060b10380c031004600303540040d915174a911103640c0e24001105580030341d40d04e4101c0307542c6e00c1d14458000c00c030703405003e40303080c0d01c4828010b4062900c0130510458840982c0e4440440c26103002d44080b80c55035003501d405c2c86924803605000c5132043d4030402800140184e02c0742d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 695220134 1250 695218884 695218897
    0x20d050115030b0f01080115050c070312110313180905060a0e0714030d080903041205010203061c0209060108070c020d0b07022422050a11011b053c03 66
    0x2e404200d2007000504100d1080c808412542c0001c5201d001449046028a4900486099400e103242040031600c00a45810000d41003107820303448035071200005540210354140300b500305602642c1030000180908071103440b02e1064100c80f000f0950100c44840d51a0711480b951604101990101d1a1180382d01020380007100070200203103d188400160141c1b5151480800d40d40240600103030036800318101c8610314042e02944540c00100300004094649848502c5014407950026840e45001c4c0308104040004103a1441142658203810300142d6804220341d03031001007402e0000550b00c1e80e0030225011002100029040a4015401c400348010718a01c0b41c4145466800c41d0103d04202c0380800b042403280841546100c8031a01040d25400b5980c03212040b4080d141c05229041c0341921003d1400444820aa0354031011050391840c0d07581c40030b40501c40102c2403d00450420480e84c0d982d41c0c40104070304034524a45131822000a855500300c410b44100b1100c10403001007004c1000c801d40707076400f00d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 695221384 1250 695220134 695220137
    0x20f06031302030c0f010203092b060c02071505090d03091d0103020a0504090f0f021504030b0f07050a020c01050f0c0d0816020105040b13050f010c031505040501030b0712020d050115 80
    0x807842d030702c070300e140c203217134020320804103902a50800c460b81050095083c2c407810f00e4a48401c242d196402086020b8500f115401d0080c20040340003180c030366010342040281d402120307030038500e41030f210000c0360020300f11181540180ca00102d0700480d42000c640303490309038001c3c8980d60329802d601c00c0800b05501e100780c1a00e00132606001550303580c908000c1141e594102c02000d03004641c031001d011484441040303000780d001601c44442800a00100c01c0541c0c800d0f04229a06000c00c4140080c41445400456200803070307003003051074801c040c1c4010f59180c041c1c1e200b540c104600001d0b8901440c50180544143d404114100c4503500260341000d40400e0341124000c1041000a5030b011209105025040c060341d00298075001c26100c0002501241802c2d03001501c103489241c06611104000b48201c1204000d25500000c05091301c000f002481c0480303911081c400c03420a80184042400300d01081d4204005080c0040c2400540b10100b01a010301055081140d1070440006100819904c0100300042203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 695222634 1250 695221384 695221393
    0x190605060a030c030e01090c210204110a0e01080402012102090a0806042a05060c01140a0e0705031b06090a0b0715050a0507020a0b0604020706050c040f0e1302010507020f0603130203 80
    0x52451401c880884101510116540300104410380d80b103100d64003c1245440e80012030b0702700781c0215080c3c9000c25101c03e626980010170304400c40d0302c03100280d2554003d1078038103600c0c181a0002000711500202411030302620012203e071244c000c1d4100c07003803050007030805103100743e81c0d8450a4035010200c500351801c18a000a1805103114034080358211120924a0340b100d0303040409004a980041d4054107856585101d10351a40240c070f01c00c980304800880c00424031100078a030850501c034850f44414000da00502d50202501c00f05480e502c1c150000303903074841d103c41c804c4000480801c4150b0040000340030000b4044148052540c08548504948601b031046444801c58181103032000c56003000141c02030300a83c0001518200c2c01074104000600c09801d0014070384035203044443c2998a081440c074002030805c030b5101d01d803030b0280003064101001407191030128074206505440c118024100300e0001041c0d011550341c61428902c50703001401158403071518189250044003a1602a482440b9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 695223884 1250 695222634 695222651
    0x240306160813080a0c030302070b0a0c0e010f090918020a031406060d03050703030f06090c210203090712021318050114130308040602090d0506071e08190605060a030c03 74
    0x41d0000c180340c90580c040c0f1064908400544100c4060b9200c010407010036408003c910042940b00d40000c0c000d15040780c0000d00d40704003800181004124143c0706050103812203900480341d802a08034401c0760111540401e00c40503860342111a071454250007036124106441c0030050080b000000304a45107030302d0446015885080404c9200d200d0040e00030300040040001c0000240329804c40d4003000040c08000c514a519000c00c1c805491400c186800050060802610901f80069071216455100d0904501c4d504021b0085621480d441c001c42e01190b12a035002e030110340341d041400501500d0050100280100003200402040c20b2001c250740075801c01103001400c60010004030f000b0940c0d540019101c841c41c0d078003a075095800078420b54a80b0b500344141c0c840d0751a90300481e0805403064002c0c0c16103251802000d0181c081c1c1c414040e80142a0031107071580680c216400340d4001d04008400300301c2c44841d0302d83e400030b000c2c5a082030350080c50210344040000c0c0c058008034003003401038909020340003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 695225134 1250 695223884 695223901
    0x6091b06080408181f0c0203011404020901030b04141606021c0e040e0709090809120c0d0605041425080f100903110607090f09020903062403061608 65
    0x4000307540140c101c80f0208580030450390038001914060303402400c070840e2072611200c00d1120003140003210300880c101220302d40444c5000e10414846120321503014402c1d040035008190f141c081404000d105070b00304070200b001d0040019422000030502d174100e0b0140001e800202c2d02114081c03044002622032071400451490712881e040703096a83c01d0b075610174003580500030440074100840d0301070110b006402001c503400155000f90307000640100902d603600c101d103409124904121940704022600010105142e03544c441e00030103001900080c0c08103143d103860401e00c4801c0d0800c19854a41e01c0390b0348075620741186910140c200c07540c07941000946c01e030f80c826105455100301004403a01d904101c0740c0c01140034443e80600c04c1140240390141810230a41d030201e00e07003281900c1c1c00340400d06030303601005100c41003100c00002d400189415410005030402090351a18003404000700c40c451844055090360108046001208004040b610b090806080e10403400c078442ca1007400207600d0200181501 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 695226384 1250 695225134 695225147
    0x9021201080c0d0618021203030105011806020309010e0609030f0601080c031b06030a0912080a0b12060a0b191d100803041815081f060f030b040c0306091b06 69
    0x400941101c07003c0c42160750b0207004092809884100c00103071024103015131500c041c00b0385100c800600030342d0780394184000540404603080c10145240007140060003480c1c5e001c8290b840c2e1007400e00341030078402e10040c001411400b0f000607890705480f43d15100d01c1500070004000f41210454802d60f0002c102620515407925040018a129440c0c900340007e03290810400940d0f20110010703001480304c81a56920080300b12868009001540507018080415000d10420b0100e0104582c40320035413815400e450344940000700f24003442a41c1d642480d4503a102c965a01000c4c1941c40e039406403003911103279294010503549620300c1020600c280040c11524030200d4000035603030064011f40c2400e01e81210003004000001d900c170100d9465154020075004a025030350040c00003140502003110090a4880300d59440a00903010103003403a404008810410200c1c00650342c00040c5100d4569813401c0c100717801205135200a050303929241c4a14144031000340d215180c0384040e03001c4040c595440d01b049629 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 695227634 1250 695226384 695226403
    0x12050a1401110c031207110316112d0102060415020d0905161409072003071e060524010c0602120411120a02060a03050a0e0a05070f0602160b0a0c0b010902120108 71
    0x319031082049904c1d445060a9180034141b040c0302020040080d6404912400c6109a5003505803a01495170000d2f403403100c0e04034140d070701c007032001745243c0c42d043d1551503288076107142a04103290300158445014103e6040315100720780000c215000381ba0041e210740d0740c058403403151a054402101030b000043c500849550b016210b41c1e0340c7c2c0305440300c07044164400045041d1a4032014070003040041e000524038480340c0c0a040011a0b206c0720440c01e8240070741903e1000780000101d041205110030b01c650401080456141b0a03c1d000d003240361700e840e00c00c00a104002203d04800c0391541000100300701c0d03250180000900381e8441c5640003032948210f49e940000e03003000b50710000a100307812405200342e100c80e500000b1400046044010321160600301110300000340e0742504800d109101c040710b00201d810090030780344000c0034100d00d450740d40c0c1c801030140c1c010161440000180582c0161040011400c4103230050006406540e403001110020360190001240c151780c2040005206003001c10050074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 695228884 1250 695227634 695227667
    0xa060e0c03011a0a030b0c040f0e061302070b0c1308060a0b040e0303070c0602070c050d0308040606080a050601090f0b060f0a080703020304081207140708031012050a1401110c031207 80
    0x102500710b549001c60700c3c0d0000e0007400e4240044c40001140c00311a80c49c40c009000c01240360030035060440c20701416600c040310b4502400d0040241c980092140d100259000704503000c0035442d035500541c280c0451030395510880441c4a00c80a01148030071581c004041a82d00321000c2003c00903194400f0789a0008079500d00210b80d014420b01c000c01c0c03464008007a00c51182c0b000c0c880e000c1c0c85400240001f11f0f40700c010b40003c1c031950100010080244501c00203040d480300105003d54040e40ea07240d82d600140500d8a05d1500e43c0d0b214650803510342c100c1c102504009140907140c1e00f408220401c0e9401841c45540007920540104000502a01c03c0302d018682011270f0a05d041303900c070701d0301c40b01c241c0c068140010050f41c603004500c5015030401a055651281031a035642e4200304030003045030300c52908412041c0b0030b0f083c0c0d01e500040c400502540e030b80da40300142105400c00e0407901801854442c3d440c40785070740b0006000f644e00d50080b00410b5142001c000b051250b0700d409004480d00c1003024035491 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 695230134 1250 695228884 695228899
    0x20d06080708073c03051b04020f0d0e0c030f0a05010f0203221109010b040806090721110604030303061511030a0e030a060e06090d08090c040c020a060e0c03011a 71
    0x702c00600c019076044801c010000041420130704900800303070143c0c4940c0305503101e400c04009080e40031252000c4c200c3c4951308a60035414540240c0e0116128440e01080e110502e56803040050720039014045034a15040007804d50b100a90007544986d03c07820381da00704507a103510700752030100c1104440c400c2c2e07070042e0a030524243d169000a1021060040d20203c06c2c0c5850929003e1040ca90341c4030b102650103030203a0b8007141d80703c501d8100300c0e503c2c255025141401342c1c0c0000e0b005100307000c0034203010100c0c54542451403100e00c4003801c0104100101044a80e005240001c01200b4550142c00c40006c0395024015854003407001c071401c039100a0304904424107504100b02800180342704200329820280010151420040c0700e580d00d00403548140125012230b0002030821200f50028000b40b1414111350900d0440c92401032003ca45a070a200402e61180d50380e500c82104280c800c002400c00b5507070041c0c007041110820600659030304540c04101c3c0c40f945c2028003c06000c030188580c100703280c0e000342c14103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 695231384 1250 695230134 695230169
    0x4030906050f070c0801021905160f02120d020a0b07031530110a050102060106080f28090501050105011b06020a02030c030f07230a0222020d0608070807 67
    0xc481641c4248a402c00141040c82414041004c002c051030040803c10001a558400e400c4003d03030460b0040245070508c4400d00c41c0813a600582054241c1441d0f11054510bd01660b40c0300040849004070b08500721449000031400300c03d03400203030f1181031902070340d404180c0380d890080880c10b03154000500f040d66400c00300c0400144200840c185141e01110581e202807400c0894440a6078034200001d4601d0072007454485800d040c2005000058802031000d081150f0601300003078030310b0708090030485614128100141010750103406506522800d041088030f4400c0d203aa80c40301400c0c14002c1a9600e5103001d00000b60f56014084101107440074450984199040d620f8600003904941d11610540c00100110f14003031109000030201c0c2c003480070f1450340354045c40c10000c205d189520400303001f60605514254000c503000861001c0e10780e04a68180e2030440e501d102c0c108030320205090040007800030400758032003007494001d181034030021801c68080f19038585206a513001244981032042d200749089 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 695232634 1250 695231384 695231387
    0x80114100e01032715021e090105090a031a0c09030d0e04140115030b0904030903020609040b040e21030411090c040506041805161b0c03150b13020304030906 69
    0x1499801c180504001030704c0811244010b49901500e50b800f1460308081c1d10f103a0400c07080301c03801355441034407000460400782900c0c020640e01da40025031400e10100030800c00e01d03a80c8608201c0e496140090101e00002d507a034a001d2015102800310690909405000101c18007020802c1d1100c110b0010020050f541010006a50000c03004030f2598001c1e440720341c80908405907800e103500070020b4022041030300c40d80340c20080c2250082d850881c0700700044014000401c0d1300c40c84200550b90100c90345643c8501200c0010000c1113015034a0342c1150800102840c1504080740c0ca07800c10302c500740c1280c510b20010140162500c400c590041050b040700d500750807682001d101c010741c400070b01c118052802d82c45000241c01b81e041503008032420134107510031071100101d034000c3c03580002034100700e0242d4070000321014100c200507407040b1a08080758141c4000388084809c3d204000c5400c103010811f6140740c02d110368068018004881e004044611001c2c03200d440c280300b103030b1107150965900c20000307061050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 695233884 1250 695232634 695232647
    0xc060e012904140f0601021606020705131805250506071449020709150314010606030b06030f0106030b041413020f061201141c050d08011410 62
    0x28900c1c0c21550f02e0300c043d5410b100805582e40504400b404030007043c80c001c800203117002e007220280621230412120400c0b0f0701c0e40004000d401d40b5021201b1903011035401a080d4001c1c410425580c0c444058003600d441880740100d102c403802c0301003071222100d894400f21005201c00c5240701d80c64001c681040040040b9000d0b0000604d0780401c40d080c1d954003501d810107500e84200380d41450a50200785949598024020f407084d04110500b10300806004c07503000f0029460b001d035072003500d26003612013403069004681d41c21008051a4080c0410701c02c03040542e9802e0081036903014440103c5d1804510400b03920b040000c1c3c0c1d00c20103002c0b02081041c1e007000c000f28060712184c10f40d150403644407030a940901d141080294403501c0101d40084109120b80100038400038041c440600072801000b07010328001e50b01803964151010203a1040e066000600031548500320340340e42000304c5040d0a41c0504002c008504804580c03207907a22820541d8803800b0160105101180099012070b1100d80200b900d0302800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 695235134 1250 695233884 695233961
    0xd030b01050d0f02040b04090f140105091311180a1422050109080d0504120e0f0904050a020402040b1201090b090415110307091a0a0c02090903040305030a0c060e01 72
    0xf4809814035640307458102d8503803c25040140016165401158000003608c40e0042c4001c0e10080d02e00903501d0701d004600c50701005040340c0d8a0042d2401c01009002d10044944020320000d094402c60445030303498207120742c405640000b01c082c01e02400484242c440f0703081074021501034620075640c103191a00940c0b5104d42420441d015520381c8000c40110b00d60101600200e1010840490140740500c0d08200200c2d10307402840a1000c50851940c41d611a0030740b1105404099440046984590400e41d1402c0040c030785c002c0d8020300002d0003290304085003000d04010904420100d60307690700c4580354410f0718803100710660000020350024000c6460b800c5a8505103240ea070000a0520200600c1c80e450750049441c080400c2580380100803403160b4107820000081031000c1d081c102208580300030081401c1820281c402c490380408a041140c080c004c0320001c41c1d0000c101d9540e854000303005008484c0c521030580e02546420b202d1035400030f0601881d04800f03003040394900c0c8d510000c0400b101e10380d80203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 695236384 1250 695235134 695235161
    0xa090b2a0a091e05090603010c0e040f020f07050705180f070305060d020409030503070f0504210201210b0f0316150903051209120a120302070f0605040c080d030b01050d 74
    0x12440015100c00354100e04a141c401208010f080505180030700c5080503000e0b1a49001c0d0780340c50307040096545d00106003000c8a0302240e001c035041d0280c540b020080d00611881200383c150015200b0b00700007000030342800712501075444107021040120042004036086a040680f1003030700e0001080305200342d00c09075001c20000c041c042c4050080d00400e00321000c001003180828800414846410740001d501e4005030300c0c901c0c0807440c150800300c0301d01c2101415064520f403080c141c0d10850441e0301580c0700d0000381d00080c01a0218601607101d039400307014032010070350140350410100483c0d424017140b0f0750884102442103421140c9403d403c181e0751101e0144070304c100640c841c000300000f0018031a10380d0701c1c601010f846440f1100407081201d45080031042a8690740a151082c000a01c1c070900b025050101c3c2c1001a100e100d11309201303540b052111002011285000b0800040003108204101500c03150421140c0841461800380e084401c04000d9a02140040c481116548169001444e83c208034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 695237634 1250 695236384 695236397
    0x50708190903120801030c05100e0d020301060b0706320601111e03030603060a0615050703090f0e0703051f03110a030c0e07021c08070507020301140a090b2a0a 70
    0x983c2c80302038101c90f100070050002940c40c0010010b20003010a02c0e00546403c8442e041c1d45420f031000a844110200308060240c80d100404009540e003e51104000b801d404803090740d1840c1506e058002480004054400303010308070300000c01980c001120300c0140c0500d1102101715101d0340c005580d0030004c418001c03003e02c1002004c0800e1561030714405404e018050055840e400d1500405040c8400105501d003e10b18100c0200100c11600c10400e080020a042407591684207007021030740c142d0036400c02604010700080000b030301072103022a68800c14455908000640351142d00304640d0341d2150451701070f10240c040500c003041402c83d08c03001703010004100d4043c180d500d940d00c010f01d00c02540544010a4000f0030050000d8051090000c4200350200d01b4002035100c950180c01d90001402540800c440464014119102544105566544000040c01a1400c000070740003605809400b00d07500c21016000c1220049117030042202102e14140300443c0230f8420721011140d800c0711605d4020400b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 695238884 1250 695237634 695237639
    0x7080f150f13050d0f0905090c2d13090506010801080c0f010e0909070608011706181f0c03060509010f0314031b0c040515011211121003050d0507081909 67
    0x1410014240340001646800c200718241c400064201d035100e03440180248c44900410103180d030300d18200c2e4203040c0d24898242c03c50406a1400c194200c40039400d41020000003a4041614088010130381211004035042c41982da070380004413450f103806e100d001216400356204405d2072412988032003980d0410305d040011a400000041c81d100d100755004511600981d90601002e079000e1186d90151041c00d885003040d03680554103c2d51610300800000b0940d03e811441802c902c420310074155890001608051009803096103040240141080f24020901e01600041c05061040742d043c121030301c049840340400e00e15260b42200b812200780100103408100310030621011401d00c54003040c1e000710000c10140a410081c00211440640781e0309103203141c0007103801a60782c01340b10300c1c4158800e401c001c102e540c00c2c609503006d00d0143c4010001c03245005001c10081b20061114241180d02031021112a100020b07015680c522a10318042c1c1204410050458800e004140030b070b2440c4002c3c50b11240c007070b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 695240134 1250 695238884 695238893
    0x2072f040207120e01140d0506010c0807030305010f080c01090312031503050726190302011b030e070f030f030507020f0d05010222050d0b0c091207080f150f13 70
    0x740580c03000c84850019100100029074050704844c0110828240071a85c26112882e600c650f00440030b42c00740c62a101c0300021750740d0b4411000b4040041d409104940c0781c000381e103400340c003403c000d0044a040d03510382000000c3d182c1c00001c506584440c1070b115150340c242103848003080c4011103e0030700140b58544084001c0d0055942c400002140544007070004903081228a980545000c81000410048401064050800824201080906d0b10141009100d80303180c203034003501c060402c258842d440d080d592104039800d504248520400e260a545026480b2002d07000328214078000a46418902642d420000b40a9001003401500090643c07020400f01e0b1f00003008403400e00c9003201c080e500441d41300310364480c0e00c2814041070001943c054180f414907020803c4800e0310400544240f602e4404600c903140e0040403943d98100103400e0303041c80350790410703a2503441d8054403500c0721030f2150004081c000d0802107000000c0d030440000300015502d420b0f52071582404050110400c2c23150fa507540b5000207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 695241384 1250 695240134 695240137
    0xc0607081308030a0c060f1a010309140313030c0504020703140c10090305070209150f150d061508010f0612020703050c01090b061504080a030818060403170a02072f0402 74
    0x10003680d20004003000318901b000541e00c0000184000c207003003541c0080c403141a580c6083c2001c20070300e4005070070310490130a0011100c43c15900062800001440b58406820307212440590740035400c7c540d04a035550301480700705d106841c005000108503001d4014000c00c0c2c40020294113040c0303011030b8040d012200d801c0c011600b10362411004210000740d21011400c001c00c05507440310106040c0c2a401d18442e000c0791f5600d003914003551140d541c44444400c4e2060030340581c1c400000c0740c0fa003000080e4590416026154510b0820130204001d840002514885990b100b001d030760132507860b110320f0003600c042d8038080d4100010440034427070113014000071030b5030034810707800e181e4040e10080c5100c1c10243c0c1840000070400380300304001c0718104414441074400180c450320440d414030305480075513180130321405400c2c100181c5c08414022001407005255100c0c2d042524030119511640300350305c8080811041340305021000740301c5e948982100c00c40c0c02e40f56024031884141680078001e0700e00c4120000b401c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 695242634 1250 695241384 695241397
    0xf121806080a0608011506082d1f06020d12020d29060c03040b0c03192118020415170703050606030a0803010902030604060308030c1b0c060708130803 66
    0x10080d4040002e8403a95000d00402812410000c001462003200070100350749260054406004001000c40c501b420f252400c1102c4000e00806108034203004960608641c4041d07a82d0340e6502140120000781d00203a1490204881c141d40003061001c983c001c0954800154000c000700e100d500b80007035600c48402c0e008a610750107608503141084050320000201c0c203156159143d010303541c00d114411121a0020441d01903a110110035910740032083d4800b403451246010070741e408080450305818258200810210303403008620784070580e1034002c00b00d40454402c02442c00e40d40b80e41e01001d0001d42401d500c401c0e08100c0d070552080d106034990715020040006007801110030340c1b241108000b4801b05018607504100200c0103484142842e49440c0c031a40018050348100c50b81c0000803d80b9551503911020045910510040e00c4e850241c030440e81c603800c80c03468603e8036514100a1000784038081901a1250b0004015030b0400540d5140c0b41006e80103129058a1096004400714648500b04058400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 695243884 1250 695242634 695242637
    0x506010c140a0201020f010204150c020a1d040b160f0302160b1602070e010f03300e031c080c1e070501061502121801170a0b040c0c0f121806 62
    0x4410b0700c075200092422031011804100d5034410300003801065100b4056480d25446842c0006044846000040036030360240d11000c2910803071580940d10760f0380030101500c2640107030042c030350b19655101d02c4042c42c10540b2040b030001d01030b040d101e12040d00942c042c01c4a11811030380d0343c5802d2030a50b03030f50880d41c600b90388200448000e030a60715220343d030400840d40513101825280915515290b01c102014009003c010300c042505441021003600300c2c01a0441c000c0350070704601c0314a000c03d6019110070340d03050310039000740a202c8a11188401148442c00d42c0e500a54510440d951140c03101550381c0c200d00031035982e071495012011286a030a00107071840d14060400024800c0c5840065050b1408041000d01950000d000401c052032429050320a0f404003c9010b03049801000c0c0103c0d9441d000320500e014207590541072003880300c4240d224200720751040d502000032030310032402901c1c560a070700c0b00202180a490034080005000c600042e8410340c4a044c9080701035400d00807503032041e2240d0414070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 695245134 1250 695243884 695243893
    0x1050c04080d0504050307060809250f080609070302400b03070f030b070e03010c0e0436050f0303090d1b0305030411060c01020a021507110307060506010c14 69
    0x90a44140409840540c42e8180a0b10341450840400d8540e1041d21642c1c06001c285000a1003510060040300c2d0900c032404d40c9d5055400c150f606600e04081c550040c14200305103008085200e2070000754145c0142a5900105840c40c60344e03080103449903442d4240d00344514040110b0300091100391103800e4958510001c450072a03400d2048008541d00d50746030502c03a500446041201c0384800003200b0503650040f21403a810781c1c0c0c01906842200d00034030056090b42c038211070f5245a55001c48100b0300d45204403414030030401082003a07000710021a03403175100904e0181024802203107140c1d100624138406d005580701c074109031300890705541040700e40c0c83c070316080300c2c500040f01540281800c0f003c4880c0182800e1018181d01e0040440c000203000401d51017649003a0541b5030ba5900980e40c03038045d050020b550310322405c540203407162106412800108119001315440a000c3e0001030503401449005505104258441b0005081c0141005041c481150145004200526082003e8150340c40041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 695246384 1250 695245134 695245139
    0x390f03030f030a0b04061809081e0703030f05090304170a0b0103150c021f02030603010e031603030e0c01361508090a08090411040b03100f0b1201030803150301050c04 73
    0x143c00c0c1c0310301442e05842546001402c1c4540d84682c5190b0003480302804000514540303910b071001d918482d0000050480300c02005042130b000c1d11400a0012600c2690144482c9240744d440005840040e04d00f40110380040c0014402420710050096420b04103a04131031640020346c03039540421200703070801d42e0491034100000022002c1c134050f42049070a45d01c024000596034080c0d0f194140b11155005143d0760300040407512580d025044860552205825240d0f00c03a40019070004440e800507040700468140b19003d8807841c80841c0a45d050101a140da4000c25012181860442d80103141480c46041c10210121403c40c4010444042c0c100a14040a00e101090029008000040c40c99401d9070200c10140300254404064501030802510045560b01c244a4084810701494210301d8002c07001208100c0308211143c09481250900041f5100d41900c800c030f00c20070b078412039072107942c8079001c40010000115600019540301050040f9244c030490b01c1d600003429901c00b83d82c20315200c42c1c0410103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 695247634 1250 695246384 695246401
    0x1060b040b0c0d020703050d030513060c050c01140105061209030415030903110307020d02191701061508090628180209010609050d140c0a08060702390f03030f03 71
    0x119940040d103000174000140f035541c1d12035442060485000030181c441000c1401c0c80d42c00440c035001c1c3e9a0100042c005600f000c50020b2003a00311010800c810740c00c0051503003840110405641c10b80c1c5020300614500f100030314080781a1100a0302c40f01803444104400101189a60360300c2d1b403000074941c2e02060417441c0341001070120b0100c0c244a00603420070061070006a4400700da40450030740c1070741c11020b6115103020451800070b003a80800504980c0080c803014440b019800041500c110310a0707101b00406042089580440c110380c2d090582c0d2005010400040040d21085c113a900c0d800c4a842c0f000030351983d408140c0c3c126940000304500c40c0d111160451505840e8107025004d1031a2116086180000003510507401e6000075111501c80401c40c904007000380008800100007a00c040c484594070f0409503558181200c00b84014020035100e283d80d000c41c000752002c0d000300264400c00c2040c0e4100440352294425050603441000c07849242601c2d01e0a0024100800ca40741c85103442e4541a0300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 695248884 1250 695247634 695247643
    0x4020d0b0f0f180a12051903020d0507080f04030302091f030e100516050c15010f030b0f1015120c05090f0f010929030112050f0109120e0301060b040b0c 67
    0x3650102c04082c501d00400340e0f0009000b080c056000100c41003c03ca04031000d4400b4843d4140004071910030400c070f0500c50b9010380041a03c0020607104000650719002c0454000a060f0380d40d40240551901040200f4400d40103424041001003460418202c2d001d04007511800200300c11002c0f940b21806402000e4080c440664080044082481940341451041c002c1d14640d05020003400408141000e544508000550b02d24512651400840d6101c1a094141c1c0200d4441180c070342a00303030001003204128a01c0a406000900d0724803103914205800d0032404e180d5008030404100710741d035882825604500480d400080c1d10f403905a0742e00c100074180310b00584161100342c0a26814400007880366800b030840011103200700780d11000708403101e000c1d01c0c0100400c2d00e0240720f91004400400c40240150310700540d40c0c0314400b11074092001c00002d90903113401140142a040318440f0080c0080e0107804a858100f0006000180d00e43e19114050720640180d0400c48080101054401c0075210400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 695250134 1250 695248884 695248891
    0xc0f0108191118011139040c0201020c07090207020d12030f0f0c020c03060c0a0807020a1a011d040b0601030f0212100f061806030f0f0e06040b0105060a020303040b04020d0b0f0f 78
    0x1070203401034500f01489846c800c0340302600168840e0015021340c109608201014022000c010000c1c441c031800c004000f4041e4100601c0009a40584200014060740358421074108540c081e000301e10680c0070340c45105490143d49030040a146c5c4885001400328114070869046002c1a080001da02e60040d8009103029240c1100c107010380e11072014404054003640550301c1038050b620b0848490740d202c1904a05040070104c000b00f00c800c1020498008000c1e40f0001410b07109001508088904d2640e0f01007030403941682c019044203220340204805511a82001c842c150034841d0144c9020000c076254080a00e003110f01c0b410500400800f03129880080602c84002e12191820484e0b04490b200401c009050a200b1002071507540c200c490068800d81d0001c07010403040f00c4080182c0410b52096544941c0100c07000c841e0b80784910000701c0c80c0d2501d40b0565401c07040daa4002c40c01c40d0784560390b0600151020f0000d980c8405042080400030b07035461469071003202c204059103114140460f13070612240025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 695251384 1250 695250134 695250167
    0x6070f2f1302030907050307030b070f030203010315111c090b0c09032a0414060405061e01081803040b190804170714030313050c0f010819111801 64
    0x141004403035661084200030012186050059403a01c0d510805403070302c03c080c0e10080e054001d0502c00014402181e6a043c070840b480d84400c5d80d40d504080084003240710900005000489251210350381d11155805288040744d010000da03c0c01d0b0040c4042c0e0021880c0c2e800d51090552206503400c00c004580e15055000f060300c10703106040c61485000240c60390071105d00030020300b5100000c4c4092280c1d07a0f95816500401801c10021048034140a04032140d003100d120780617a04020101e902418803160503086541b05581e070031062440c0c4001100c0c1803e000d032040043c08000704c810602c1c0003042c80148024070246800d5644c4040d032103042c8903040c0c1a07403440000d02025108100100f00501d003050701e41507602c01641e54403001d9282040b03010000044800c9107100210070003901c007480d0300a203c8000d014030110362244034954100100c41c2400d1443c41c0c0010b14010101c4c0d044140c0400c00707807580304030004c042100815110300c1c00c586d80202d49081c1072140c02400b48051941c00c1102e905442c04030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 695252634 1250 695251384 695251463
    0x411180a0e06090703090b041208060901050a1a0702100c02270a0e0f1c02150c04060c0f1b03061118270118051f1406070f 54
    0x1026240c01c03145900901e01c2d402500e400c2d0000c3c2c900361190344003801c83e50b0701000314580c60519041000724407403202250400700e604400443e1991510243e1141207a0f0001c094a91403801c24100105d25000c144929000200500511006954070a10000c1100340c075600e200c800c2c16240101300d2412080a0500c5203002f41b020f00c01c91581101d180c840e4000c0b1000408548031000928451402d4043c003016030b0a8041c0e9120840f241d000399030501c14041082c9c1c22a00f0218045e45542c0140c81c5c2500e4600030035204004c1002414020b0800d21406401010401c14500030b54642844d86409003004040740c1804081c280300f01300080c4070308d8145040c4403143da0700303003040b9422400c62a14031206042c071a0300d03203000d2070190b0440d02a0050450000100d02c80055035140e260070601611013600c45560b03401c2c013001448044541e41d010441d9035107850b20640081c603000300f00e004a0802c051458100c1c1013000603801007200483d4940481c2e2003840f040301009144500104904020591101c0030501c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 695253884 1250 695252634 695252639
    0xa1803020307110a03080705100f020a020703021011030319060b070f060b12030c0105011409060a0e19020c100c03020301080a02040e0118080d0513020a120309050411180a 75
    0x60001c20b49440e55070110403144640507031000a454251158030081c003200001400f24200100801c41c03202400a0b030406010081c0f4000122090740a40c001c2d11005038031a170802c00241c41c0c84015408420120b007056070341e070605109414110f07803007151240040b0218080d103c0c08400c071440380400405084002c45e0030448650703260155445181000b415440c0c564100f210150383c0c0180c0012080f600c00e0171a590b8a40001e0342c1c901a103002d01c81d488020840b01c40920302403c08a180b54401c24004090058143c00c0c0380074400c3c810b2021300208100e41020310040007806461004003000d1400e04001d01745e40b00851a441c00b0385905129030300405005000400442000280c0e4030b100d41c0d8100c0300880c840300e604110500601c9004258100340d0341e402d042005022060300209484443e4120078861507a4058120100b10340d448802500b0000d20b110400c5019400310300c00340e03143c1c032929011142968800000d030a035041110a4564000d00150400c254014480c50200c5d8200c282d80810740d00b031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 695255134 1250 695253884 695253887
    0x31d03070509010e150a29090f13021908040b0a0e030a05070302030c06070806120102090d06090822080f1203070e0630010905042103150803030a1803 66
    0xd8180715483e0751084810108400180925240c045c10001a00e0000043e6880340341618a16806e05601c1c01228041c44202d00c900c481821100a00800382040801d1101d11090103881408503600080301c0b582482035a407840701500000c0c8100f46e4555908081c0d00301408e021f4039402d405041880503034907003841c0215000000c01502d07010003840c00c1240d00c900d0759040503070451003540214134007400392504100e11190050952800f40c403064800c00710000d4101d049500f01d02c51317400e80c9684900034168000c00200d41d81c100890301c5c0c0c410780900b07040a00345030a00f03162040c2092205000d55210100748101003040001d10102d8468000809841c03d030302100054070b00c809440d503c100305d2418a022b02a880d1034003202c800d4030000c155001e901414640d4003103c4c0300c0d007002c036040301000c0780000a08000e00b07006040c091074001418003250030800d44095011032410348074405040c4c4038a11401058020321a070402080f1140145d5a20310b8000354001c204d40303203210803a03440c440d0f203a003200209c7e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 695256384 1250 695255134 695255149
    0x40e0103210f0e0109050a0b0307140a022a0306040b07030513020a03020f0622030312051608090115032103150b030c040509040609060c0503130803041e031d030705 72
    0x10120390400200c3c1c030200c100100c4a141250300700b07c1c1c00c4541e0f8807000030144078100055116516640c0d40c500801e00c2c400402d5031078400c1a0801c5c005a200d070500e400c151540104100c010181d44000c0108002c030880824200300007240d003640c81c0501002003100d10b035014002c0e00c1e480007204c03a000300c07508640d500203101c104090101902981c60003010301110b442d110200d40c8001c0000001c2d40d82405500108041d112050208800040c1c91100c0d240b851001ea0081502603050408250707050503610034102d9507075900610032a680d42d205e6141c201e0f1840015016406140240b10141580c240840a22544604003156604161422401582096695007020f0a031607805807603e03078940380c0c2c045641142c01550822540580d048043c0010044254440d036005c5200320780620540050342c3c0300396168081140d052140c10410214200080d01c2c450007581d10a100381c2d0301c1c00c8508526043c80c5000000300d5400c80101d4541d005102d180d54148140880d03600b000c5000700746c2c49041c4404603004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 695257634 1250 695256384 695256407
    0x10e16081207020f090108160605070309060309020a0e01060201061a09060f0a0905090f09010f05060f130f020a05070203100501050f09041e0b2403120903070308040e010321 76
    0x4055020440004660340c81042040c4108000c098605e29612803405036159021a076072114914982c00000807418054000d807070300260540c54440607a482c084081d03002e091490380c1241d000140d43d101155044035059454040d2036140e000088807800c01c9243c1c5155801d1521201c60717543c0034028407042c0c0d907e034030481e410501c20500f010303240e2000304020740c3c1041007500119030161f10304081002c01e10481c9103d61080150134004d204281401070040201c8a05840d02500405c40c13018142c0780d803e140c03003544842500603a0000d004139030486d00d142240c03c1481c0c0c440006400107600790940c5010070403121401d000360720420643d403500002604400380881e015000701c41d0703140000c050140c400b9500e600446c0c00940c2400340b92161800c002200c1e41107514281d000c1c0307050f0b0108800c14041c15941c0414034042c00405c07803410801200e003910341000e412035030f062054030320220005104901420041145017900c44040d4118034044126907034103600300600341300824001c1d00e00c1d9400758941c00c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 695258884 1250 695257634 695257663
    0x6030e0712020f2103090114071205030916090203070314010e010504110d1416090e04141609020403050606010807050711030118030509090c0f1b011508010e1608 71
    0x241000309001c44e2074444201d00101812981c000740100c8158040700404001d102681e401c0118107000443e803149004008000e480903490341c03860340c10750f4010001550810314020407a00721614a0460301010700c156045038003900d801205014030150540140c0107400e4600640e89455030400e202c3d283c550005128503842541ca4510106240340d000045482c9184100c034207116481e004400388206080582e80741c44d20341d20002006a1003441003211105850510f491010991216210051140e100010300403e41c000c4410a1a8501540c4c2403400103040700e1401584442c650f0402a0038403000522407818040548100b2000310703440000c41d01c90551140c480307008500c90402213401403007840d4a6606018070605410181034000002d004c5846003240c40c2480742c0d94600c010702082c058200002c032509002d03c0390728a0341c841900103558200ca11400050130789110700e9005c00c545000d07480700301079941d03800000903183d00610802020800ca803003030070045072070701c0003856544e00303210364861 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 695260134 1250 695258884 695258899
    0x302070b0c060f095115130f02091e01020d0309150608250f0302040c020c061303050f01060e070c060e1e100501051f05090a03050106180e0607030e0c09040c06030e071202 75
    0x1a06c681e115082c03c0201c0c49442c00801c001901c44008400039841000401c3c42107000b4905404141100072030a000031f0410707405000c3e0780305103000640180030030182c01c4402401c0d50510203040c0d409842820010554040100747d4540129203154000103000e0100a0750b503030b80304051040c440040117040c00c896060f200000c9440076200c01301d083c052824040d03503118100041c40c3c005c0ca4002c8000e0b105590090b42912103800130012240d0881d0362510890340d1348004000000d424070700904250075881d0040360085404000322541e04d05100c07440c030b2180310a40140c500d144252100308910741200c40303110003c002c254101000a9070344c0c003003003682c01401e8043c0d20515000c244140183c0d0030402000e4403602245440e0f18166010300034500440a880440c8046c402e0482d016000e0031a008030000c000c1e00741a10b0301e12040300030f462201c03503800c498420045444116110200e0b4503200340d01918034078252500f01400142503400084e1442e905500400e010320a194241c64079030700d42e40c0e0444190 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 695261384 1250 695260134 695260171
    0x1509010311060c12031503070806010303110a080304080d0b010810030204020a0504080105011409090703031b02010e030d0f09080d0909050601110d03090302070b0c060f0951 76
    0x11101c0c815a0300310800b500448004c00341328114103000e140950300100860401e030043c0e600707040d990301c400d200e20103141e40f1680042011a0040e6580640c405419069404005250320349d455641d0042e101111311080008012545815500c10ba204d201800d00e0151440c1c20040002805d0f07080e5408040e00c00d40c3d0002e005e08444e4001c1c0100c4000300f41a1000344072a40e903501083d010481c9083c0014003880841e00041ca210300041031030f01c103507a0306480b400d50740031503521802010562404124180b0a810035607106a80c0c0801010081807484d6554200c50012000300500c2d081c295030140300f56a00c481078150301e450704015031400381da1290740c0000e943d07501d21004a805200d00d8085041500403c289200001e5040e0054a41d1034003940803903960326507071010206640b14501c00115507401c804040344600c0c06040c1c103150000340b8007007141c00d500b01e1400c503010181c40c4500280000c0c00090115000c0b0b511071a031400551600f82c03800c00000143c100c0c0c41086d40c02c000c020256a52040418 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 695262634 1250 695261384 695261389
    0x30f02150c0a021306081204030c0f0f0324050c03061e0d0602030615040b070308101d0901061a0c06240910080a0b37020702060f0f040e1509010311 65
    0xb00020030300401260412202d405040049500a02081d500c0c2b000b030020205a04c40c1682c1e0641c106d4000f048101e90b17451668031398503c1d036003082c0c80c9009440c00411402d12054501e000d814007500001068994a041030000c000200070031080d0311300c070110800c2011009540e90104503607038907040203015a59a07544c1001a0580e40c3c6c00c80300900c824000b0901148040110000c0c0c00750910940382c140309921b41c01000e118030317141da00c24800e440c890600024107480f000c81c1c1c0c2d80d40103144c00c0c00100b61152601c40e00c0c4595140103420b070500380b201207000b46076030b40200700c0c072500a8250018070070300302c184892108480310010b4899004040b11004a030b00d0708154500c4500a05070380060f140e4480981c504150070442c182d0b03849000d154000c10301150352000c2907243c025045d140804039402030050252401a40107004260b030300002c1071054211408140004001e11000c00c26600d07590790604480507001c030170191200d4844008030103140b20a0315441c058a065a41182004c6402c0020000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 695263884 1250 695262634 695262641
    0x3050d18050a05030702030f0c0904060c05090a03060f0605010e0906040e0304030b0c07110916030509010207060e1c0815010c0609060905070302011103120a0b0105070c030f02150c0a0213 82
    0x1003482c0301c0d01000c401800030100140c07030b0b0380344201c09840ca00c1040030701a0f6691201d2800c1c3c03c1d44402e4540c0400d00003000e40e4000c2c181c0404074142141000070220000d0700b0001c05500030b8800d16124140c10441c10031a105203c050207090801c047d041640a000c01c00c0c00034010f00e03660040d039880c028040300310000c1042c2c800039175100e1300c85c450500c2c0c20381c1d140c1540d801c00141100d490881c0e0074041034611340004024460b60170404281c1991603058011800f03400d0190042086550810ec02030101e0054001c0315a1303c0c00c2d010040070f000c544d8807601c81c0901242034004041002c01d2050103140c07044203c08150b400003d00c1c020303403140c41c5800e041c40108544076000700000c1c5844280010030001007600d0044038006d1720303203840004011103c03c0d1139105000e03454080d071503000c001911011841e84030004800381890001d0802c507032961001d040200c250001e555426140308881e04500e49007058080c0c60003805806414410303103407005955140301550080c81581510745145200026a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 695265134 1250 695263884 695263931
    0x30f0932060310050a23040c09121a0a09080d05040303181104111303141005010f0e0a02130e070c121106061e060a120c030204170a03050d 61
    0x8001c241d590510121103c40a8a03902c210360280550500010316150440100039503005c2c0c402c204c2e10101010030804c07005011100041090011501c03010a40b01c01400c140249144035030401d40c3c8003e050110035200040003031401c4103040c14165104002140c8000396021445056000f1400791030341d10f400ea02400007900404170211042440109000142004602002060350100590440000610101c0c401d0b141c4100c4107500d1072a0400c000340039900c42402002c00c0348140c2e4210a0015a504242c407030a03071110000d005050310901038101c880c0f100940111001d602145403160358400400341040310720401507081c204100003040c0324010310915186c60b0340710032803200c08198950060242c0581006076a014425000000c41a040061821091054800c03581414200560400c81150302803101e8004001440d490409140810701a17001c002c07202e901c2c09030f101d6003480300d16200300324191242c01e0540e21081036807010940010840d0603840c2c603168003190510204400803109000b04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 695266384 1250 695265134 695265139
    0xf0c01062301080703050606030c09041107030503010509090304030507150e1305090d0e0f150c030304061d0a210e0a03050607080603070305060f250c030f0932 70
    0x401e1140c0ea0142410185041400076203a1003169202d01c02c00b201103078001c4500ca0741140c0200f0100d803024540b4000380102010044c40428011464180605150084201100807940100045c800c503c2c08980349503118140d20021801c1c141340d602c641e90ba400e060310501d04030300c14819544944620541c800702d40c0d50f41c05060100e03644001012003004140c1101d1013042d6000304040030314980e2003010003101341c0c04001c10700413440030b41d1810000d0443d000501c482881c00b081211040400051010314807584c0611000125041c001842c0e03024504807400310300a82d04900d2114000451071400204000304068441d00c80c102002401e0380c914041030312080c3d001840c00e07000010444005103c52040324659220f402f0798a6990a26a65023054000100250030040000b40c00303441d80d0845031780c0034180c84d081244240b00f03450340d6110017400204040008080c1500c0e0014582c12108000c031690441ca004000c0914069000e40e000d20170842c60400d9400d55000e070814880341400707519029200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 695267634 1250 695266384 695266409
    0x309060703090803070f140a050304090c030204030f0b0603060106030b01050316020f160f05010c02010c080d020f0408011407020601150e041b050403060f020414060327030706050a0608030f0c0106 86
    0xb6041c01d100c201484c2004403800c0c400c40c410b5040c100004a03610f07040135407100041d03040c181400cc07642c0140c10054000d02c100b40e4240000004134041404850b42e0501800600341c00e0704100303003814181841604440140345c1000d903800c1071642c2c00703400c503030380550022403120390402c03000700c1241070102c160100c07801031180080c0c100101c05901c01c4802110480d8000d032000f035548400641e0072072000000039010909140d2500d0110305031000410050320065001450f0039040901540c0d0754001e0f420419550307560701c2c641256410b2701400030342c009815000504140d80740041b48015801141c152008010180c05580d4940d00c0d5604122690702c0d082c540da010182311424010810380041c88159041c0b0b08101074040c00b10090f200319401e0380d0b03011180c42c0c14064803009116060f4009008248003821030b1400074181458010618040c2d03202c4009955242018200b0005a98002c0c00c02612940b0b803401c2003110400c004101d0700f05200074140c040c3c680c0c0d010504a4010402c0341d0098690001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 695268884 1250 695267634 695267647
    0x50a080718140d050f03091e033d051519090f1103040308091e030315010c020a09150e06061602060d06030c0608090d0c020f1504090209150a020309060703090803 71
    0x8000741014a20136923070307078051171104030041070410200a00950160003850b00112960006550500a00f495003403d0508440006c03448010381242079480303e07126664814041040c02e50802c000081c00121441c040b03003c41c194041901e410300744280b1030841e03542c503000180310702241c11282c1c1c86110380c2074458580c0781c2410064805e00f803c44010402d405007940b148001e8400c0b010f07101c5042800d0000b1410b594944e68140341880307031101c007541804512035280340142c2d00d003040c40c00640a1958089424500000d00a9525041d0b41004000d0341e550410410180c84007410340e91600442400075111902d06e002090f440e206807a99101e100342004000310900c01501840d004903142940c4051055860741d001940f80c052120b200c0001940c284020b402500e0b00100c5001e520f2030003000c000c001100c98240e50416030003980030300d8102c0d401007510610b0303251403004c1d4034040c1c00800b18a481c2800c0c00c4070082d120704c20481e4113846500d0108002080c1f62060003694060031303031441102d58648 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 695270134 1250 695268884 695268913
    0x4050109020904240e0615031f120807080904020403050a060506100306050d0209090102191206080c1005030a0b090718090b010e010c11040c050a080718140d05 70
    0x1404109903d01541c14204842240418861084803651821241480403070824a031031400d0000070341001e900c5a40c46040c2040351101100a5008802c01e518587d41c01c07207500010701d285080e03503210f00c11020308a0581004113038001c1c22140020780c80717070b401640c42071000005002401250400b808920504140e40c0410034940c0c0040d020b141c04880c00781c0c2d4000b03101412000d50b8424041d2980048105241c071005041907000643c0149200e400541420300c21360040c0a10030384180c00c50001100b0681412214102e403003590302514034070380600f101240030404620f60116404c07401042020000005154000c107601c04032407084020890801420501d10081601e01141c444860344452903800049015240c03140c04c081c0e04045c0c40346645480d86000541d201e4600c2031058900ca00656280b00c01d540c4d032413250f002c00f58140c0d21115250b624408004010000c000e004000340401040d039644001008046001220384000d40400780d18201004920a045c034020010110310401000c1803880 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 695271384 1250 695270134 695270137
    0x90328030305010515040b16080307030c0e15030106050d0609110a030b030a030e040b1c08120705090a0510020307051203090c010201050f040b13050d02030d2f03060d020405010902 79
    0xa601966080c40242d881e9010409500d00310107907080400700c00c04c010415490100050450151081c4500d003200ca040c0c1c0724241203500440e164000256100c81d03082d000364101c103445603404c01c16200040d40180c00a820310f018441802028107011000c0398030089e049107034010002600050005024503500d650400300f0f40d420691380c10f00480c0c10498852464100050720409454140d03441140c00150b00301407000600712410b501d608803900c4410200043e03045080c101c1201d200714101d81c4e03900000c9030310b9416002c1c003505c1c10042280410200b000c650394a075202c1e0645004860751200350240c014140d20f548134036400102140139800c11800c85481d424003451003040064103649503070ba80e50004900329401100c1c003840003103a00307002c2808510b0b400500b640c0f0120960328082004e92a841d810300d4210b58018000041c0d100068043d01d02078540111f008102d88911948400300c0802c40b000301e858604000c0c0c04c0001f10101c0011510790724903010220054010348104181d503124030003280039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 695272634 1250 695271384 695271463
    0xa0807200d050703120e0409080307020f030310210b0901050a0f0e060117010e0312061f1e050d0e1018030801090507030204170d0801290903 62
    0x104a580c2412a860308100141e0240c0d40e521030041c0c488581580d0b61080c0c459145030110040000746008012952500d01c42d07030000ea4040c003c41916458aa0802440c103101c22540c8006500180140308200501840c0389041d180f070a8582003100011060502c200802c00e01c000d070901018506000380e00a041d80060701a80705040e0521401009034403010540305000c00c6424a41e1043e07004000c0c407c0c51110707070100705203500300100310101412400f51640c0c01c020400c207855031070b2506002c02498050b0b0390452002c1005600d205100055401415103043c0d094050300c9440840e008000c50b6100d00c0480341640016941000415190140c4c0350340c0c2c00c4804009c404046c545408032640c0801c0d40754800c04a941365403607091507030900001e6405000064102030602d81c0904c001702d042c00c100e54510602e41e8085c002880d044001c40c9009000c00c1060b4031220300030084a2544201d40c108000480b1070800d030340c1100745d443e00207401080c90300c0c86560198013003174100f0094201c1e8081982d80d2040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 695273884 1250 695272634 695272673
    0x904090f020a08010509100b0f030303070914040606050706051312020a030908030316050d0b180402240d0903090e0406060e0c04060903110d060e06010839030a0807 72
    0x80b110388441e480d500321081655294840c1c1d200003416044502690013883c9094806020000305100c074001281c5503070000d0f241103011543c8410140b2505008901049412504907000c0c00038901c2d10038054203a10403801c02420140d1a000081c1d01c07455084454a140c5520400c00c000c0c100c28460001e445018000c400c0300040d0001e0000038281e0400403d49002d481c030344103803445550b216a07040e16541d001d0f44480e070780e86844803c800102d0391110141e008810000408071f15505d428410054456454594510079030011426100101d0342401a51019a44810005003c51541c00d00f03541244a90b408424150180d50802080210bc0d422010840740048409074007512110b4059643d0702980c00b58400244800c04104089614826080103c4030080c0c00341c034484406441e00406c1d62050300c100fa81c90b60102c40100050301003003045400700300c0d801d496110b020b80204042e11401414044040192942200c80c10303083c3d9090115820440e841508031740d80c1c0100e450801000b5035225038081c1e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 695275134 1250 695273884 695273899
    0xb100e1203030907050d0212070b090a05040207030221090301051f0e0c0d1d0f1e0102120f04020102030408030d0f05070c050607030f0f0c020105101d07140904090f02 73
    0x304108800400d0703a0040803818041d29050f03083c4818401c81600b119002c0e0b0788841e802600301003040d0b05104203005002c0d004420347d55008440203001c11210765500c046c0c0201c3c070400011000c2580402d1001d480d100c03c100d580c2d2914031042c0000345d9402620955541075203850203100c2030405000b5003103001103400e80842140c5a807a401c001d1441c0c000c4a240c0e4040c07004000b40c07030405071540d05c4820108180295400c9031810300c0c14013480e2003036060580e90240c0c88101c01e659098043c113511420100d1042c000c5d85440d040c400c050503904006014449042c3e100b0b0007241c1107a0003801524050000d0b0012a6259000441c0381c0e03001d49000c00540b0491880c01001c240010f200f41080ba072001d0300417000b46401d03261302e1000c40080103076000b80404503a448150425015480c010902c81800c1d80c0c0c0081590308103220042c18000d4075900c80d5030105402003050071240b0a001419a00030801c2c00c10714101c07818001010b5040c4134200b142d5501903d001c10303480400042c3d5000e006020b00984014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 695276384 1250 695275134 695275159
    0x8151b040e1015080a02070c091a0301050a0c0f0521100311030c060f181207210c05012106030b040506150f120309210d0f09030210030b100e 62
    0x540707030a083c003d0403000080e43c0f40c0024000b228075400401041d031168410741e80442d82c402d01c0208403a03400c00300054401d074054601c101481d09000ea80e4002642520070000c641301d55801400c00c15824000d00c06000740419003020301c04034102260351001340584150014a003030803460425110304d00003216800d100c500130781e02e80c1c00c0c005103500d61040050211450000302c240c641c0144c4d00450402e41c1441040003602e1203039120400c00d400c203400355000900c4d50301e080800203c074046200780b160544000c09041c0c08082440c2140303005c1110002e0030500c0011a00c1921f85c0b821594002014400c28284500082086206603a00c0d100f0350040e825203140303489440c4000f40d4401281845d5a000320094101c4200d4940303200c100d2a0780d180c4a044030300e8507a50401040350440e05030b240442042c024190118002070a101c20b010800d034034504500a262007103000740c05c10b0014000030b0f00405840003801c140f140680d10a18107002c0040000c840001307180001448040c944100034020740046000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 695277634 1250 695276384 695276399
    0x7030503040f03030f020d05120a0f0c050d1409070302040c1205161403070c0b070e090a09050706050708030a0c05160b070201110405060d0c05090a090608070f08151b040e10 76
    0x1410a02ca03800d0323039820320307041c80130505c51180038000d0200e0510313aa5544440603a41e82602c1820b400011507112540c4400c980c0c02c40c5012a40301e8a0007100d500304440400c4200d1002082140035690704407000a401300c5d480804441c0410301d442c0c050b018a00d4807080c080100100e03036086200c0d1304550380324040c3c004a100201e1590000b40d440001140719149c000c00024045c5039903ea1004113450702000d07915082001685c0c404054407002a810340d900c018009108080c4580c40203804a41006032030304030f1700c3d6035094003480020708050b0641e42d43c1e400404114441c038200c4d02d04104105032499001d455041c1001600400d0b15020003540c038008492030400f0300c41055030200c940c002d00090402c502c045580c005045400740c18820044100f0403101d007541c9180001d009401c0203140001c01c5428003081ca4a030002c0c039041000d8100d2100c2007080755000009414002c05030b502100030305038456aa00811700e00f04e410900b5001c5c64042000304100020003030007071046100308a00c90b2015954200b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 695278884 1250 695277634 695277643
    0x30d1806030b061605030c12130902040b070b090a150e010506010e130b06070b090a030e150a1803170d05060a0308030c181302040311011107051207030503040f03030f02 74
    0xd405403c01010300250007411000091002c40320f000708180c03850410f1250b200c40c24984124000880c400c00410300b080b100015081c82c0002c0c0c0158901103181a0800030790380c4190041c96030003880b040c0b2002c0050740d40342043c0101d0401c2a8018005c407800c96480c135114014085000b82007699611307103000079074290711134401c20000c844050b0644010350501081781e40501412180342c2e800040c00c2103410009040c1d248210b200d0310351180038002203086407800506007603079405001d00ca040000b44648004445108940c0114004d042c090190b40204103c0700300520254000b40c4085204400c00103650182002085141c01500381000707903503500070401c8007103000d80c0409804074000b0f0000072100d4000100500daa0004141045210880300c00010300c004994044103681c290081010001c1180c40d080040200d234090070812040903070a09040d0b51900d6510845101d507413111880e1800c101c0a0004074041d603004400d81e039940740c8840e131543c140e0065210440004000840d5408150710205 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 695280134 1250 695278884 695278901
    0x70c0311061b1803030310081506090105060a20030c070605030103050303041b080703050703150209030c1e04050108011d1b04110c0a0320012c0102040302030d180603 73
    0x12040025000740d89510802c0b904070310100500340b41d20340c0d06030b41e040c0c1e82000614402c801440f01c0c1c010240c05e006041d420301817001015802c80c3d00100501105903114550207043d10070549245e42c5941003403408450100c03c01048059a141d900b44003004104d002c8005c2402e0010102210421503440200711a0382c842440080c0c01c540084c408140015000084145804204035107144041d446030300345070802c4030740d50040300c0c00d80c00341d0030030000c00c0086018a0010382e10614114184410000425181c8010341900b80c0f0036201c499212010044c0314183c0000c084001d0300400c110342c0c5558060380201540000c8000541c0c0c040c841b905180400141e20f0341d41100814030001d205908030a100140441411804c80c901e0107001184141808111401246000f9503945181c0a98a404007000c410030805060059040c00c07058135001c0311500360441200c18020103804d4244961060307600902803a08001d5240c0100803a0b0101c40303500181201001d001c00c44014036559071880c05070304a03010303003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 695281384 1250 695280134 695280151
    0x150e0a11090919050c121302010c050d050a0f0503091f06170705090604020304050304060c0f080703050a0306050a050109031104021b07152c0103090803070f020714280b03070c031106 80
    0x110011f1800b12225070320840c824811304184250800700c0d41d450f8100f0f04070f03ea1103030000c4e901050349d02903030740c2c4088520a248090b0a00a00e0340c10503c1c110b0751a140000404000b00603040e10324031841941d540044000e180220f007056208407440703983e680703c08403845200c3c4104041000b192042c41d00b072080364003590b88280114075182c9005001d4468141051045e40c03096408010a070125810a00034040c0314842da64841d91101d03090000350443e02c2d81d400490042038011820300ca01e90b0842c030031078185c980084003029007560800008000c0d10544842c41c4450235015106141c0910020b18001501c1c0306624541066081d01c200315824082a0800d01d13134480940c4441c08103020070080385001c0101854046140c0700c594444015651040c0c0f09540003a103590b5100030f1180e07050190101400388100800b80d210709240008441200c05038400e00c49031040c0c001700074041f07115aa0035004080c0d0f90911a100e140200b006070040069890507400305145103100108a000401c085210b040754 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 695282634 1250 695281384 695281417
    0x21050c13140a050d030912030503010302041d060a0216210f140712200c190b04050f01050c0f1006050d02130f02090a0e0406150e0a11090919050c 64
    0x90500300a6041c0c280e0134207a05000e60f5402c0820104182d01c00b1015050103500e5940e665403551052208881001101d00410b1048101c80c80040c0d4002c0340c8d04c1d070004112100540ca0721480e50440c0c01600c0c0c44207000f4580b0080511044800312041d59140721252142c82c0e041082640ca04252800d4050303070024042c04200300400400202d0418440c400b0100c145000d46440d030301150307940204222415907540c558441480c4038000d250566440c8568500130f44139868180c5081c54a208174010750064038131900200058100c241d102c0c4090b13844d842d0800301200c6051113540c80281d2105400508400014204080882c5904011303004444580e030141036001d50902d42c09001c401001c0901802e0703a600d4080211000c1c0303644440785440a070290020f0410a81040d1411004403910b160b000300846002c0340d0f00f0810841040c8409510510f801d5020600301c107428074841680c464034100c8c960001e2028244a9a115001e2801c407808000150410507900c4885030380c0d1440c081c0d4078880404190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 695283884 1250 695282634 695282639
    0x3070f0206030c0d0203040609020a150c0f020d0206030a050609062209030e120f060f0106080c09190801020a1101060f0b0708091f09050f090721050c13140a 69
    0x1407400041d54852400c898840c146000425804203170390007a2404e9442e039884803074200a40c44c003000c244004240109107101c0204a400c6c0180542442c5000a4000d4498410800c15519040c0c409040c095000f070106070390349424120a802804140d4031140a0350200740014518109440200856450780c1d101c440b0031008030070818041c1200580480c00c200346005010700c00e071134042402031302d00320303a01c00791180e038034014102490702d48014001182c010542004101040d00a010150441110380c002560b90344450089540e110480804582c2c0005a000000340001e041d40905240c042590390610f1442283c08458281d50b01e9004981d00c41000500401c00424420000c1c0f46880c45814403074200901a00060000300c19801c82000c03802ca043d01140045500c030722088040d1104503400880031103604085000104000c1244040c00691440c10072030b401541301c10700798000718440622007481c04091003001c0390000b954440d500c5007980310116210300c00c0200002c40d000041c160151151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 695285134 1250 695283884 695283889
    0x60503191103120d0c0315140d0501020c07150e04060f05040f0e0d0207170102031605070f0b010b0a11030c060408160b0109060e06031f0c11060a06080c0303070f02 72
    0x1c25a03129182d00d03108071040b05070718000d40406006203995690000480c800814009000d55100c2858854440c280c030320148642e00d40100c2036517a002c81600c868800ca04203162183c0203100c1d48500d4440707880307101000034190b8110100c81d0081a80d5903038000f660399005090200750348140c000c261124001281c180701506003948070110b81c482611300410000030f180b04903400c003040c1100600060300308a00138071040b204100000b02d840304140c0218554130b00b003000742d442c0c1040745422070704011001503a081806280c0403034641e400d400c200c0311012541d64441c00481c69105001c507401140480e48290b058410103c03d59448481d4038020300b0150b0707182e0340d42c3d0784280d0200048000c000001c0000c6008260841034150290003a0600081c7d901e0078000407146003c0b006040710b01c00e034030404d0320402d82181e040d0807415220b140304021410110b03016054070582c404a08029051041d5810480a526107820990403159204261b07807040d40010b040c1500c03846103e10180141044108010050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 695286384 1250 695285134 695285153
    0x71505161d010806010203120906061207030b0c090f060d0603060c0309050c090702070b03010906080115050303070b090708030d05040212070602070e04060b0a0603021b030307090509100902160606050319 89
    0x1004c1441564a00f082c5007560b41e000b44000c0c1c803075288540c44103040041904085060b10b45a0118200030270741a45981c2c1e9010351480d000741003991640012039884200c3c0c80d045c40c100740c0700000a2070203890300391583c406401091248400e4807643d06001c2203207e07140c081e2092000b0035030880080c3c00d1902d00142400f942e0307180030300100114491080e00148041c941d4000e035020341501c07100402d2a5251441950a40303c0317291a0f500e010141450401103030b640042141d05542c0e200c105240303240d80302104181440441c4d840120760f8000051a01c1401e11103070b021510039482142c19000704084560300981c0e0365018003c20015900a450038441c07441d2440c4150f80c854480c0b01c1c0490b1846659003c10403042c0b142e0700a2f400b107500032a004500080e032a11a076032043c82c000042d821444c2203d0b0003080d041982c4112400740c0020004600da48615804040140400010035035685440403644012042890300646d19245000c4000c82d49240100b490400c603094201c225034031040946903616031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 695287634 1250 695286384 695286391
    0xa0f0e0304210606031b08120414030c09010b1b060103030807112d1c0509010c06020706111207080c19110a120f0203090312070503071505161d0108 65
    0xc500c1e840d402800034410f4012000603504c500903444910001d03c074000380201c147e402c207101641280d1440707030304003043c0b01c288e608403640b40080030038499005011a040200d000d0350070390481410400842c4180100c0010101400702e11200d1030444150b0b0301550b00c0d0a02030000074000340c1384001203418a841340e1271602481d500441903501c42c0c482440101c1e0603541401c0007415000a038844149096411f0104002c445d08034071031890b00b1441000c00034402e00c60080d1450500c03a0415021041c400141d040d110251b50200c2e00300001840400900d42981000600c21040a00300700040c4085125140c50390050042c1200e044c1810701401c1c03401c00341a5140785440030442001020500088200410550310703000342c04015082e0040b50000700b0f0740ca0301c14207100c195401041066115100000c0d03141098500c00b000b00d403121001d14000d8214031a42c14050050300c151007244054000550025001d440d503e4040e03540900900c10541e5160a1035800503a00000c0302d962100e10750254010326032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 695288884 1250 695287634 695287679
    0x506031905040c05090601020303040b041e051002090a050a0807090f0905011b020c01020c01230c03030709050f09010e040f020f0d030203090907141806070f0b0a0f0e0304 75
    0x5044030351108050032104202e900350b42e120741c1c2050801960403c418440d030131040030f2001c3d41c0b07540740c02d13281c8110319030b0003901c020300c40f5120149040c0c0003506180030142c1d2690200944048012048015000e900204034840c824444c40c00001030070324001c481c020440d0300f01d0003c0c1598620f05207685008181c20076642c400103880300308120000340c1c284220711a4148581020000c5007134806d00a103001700f01b115050565120b0b4100f140c10b684c0140c4440c1244201d20407645034198000103e1030140500310b42c90106104c0807042c403090681080e40d01c4142c2d0400e4510b203440159150810221b13890a102d103164484000002c68049044158113812007400a48006040802c0c4004114460781c00002074005030004110219a0b241146940760840c00f1850702c10b80040322040c600702c00344115404090f5503200c9580d00145030f2100c03029101c50325086068000e40c8000ea00704510100c40848540442d54507000b03c05000c030b005032003048910040701000394206400d11a4690804221050304803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 695290134 1250 695288884 695288911
    0x80708040203030d0507210e071a1201080703050d08070522030818031504050d05130e16020115031205070c050604030f050706050901120b010e040507080714070c050603 74
    0x101c400c1c4130b80202c070b014903110b0380c60400b16100e112640440d101c840100162103402d00c1504842c5402c002854000d40c4c4070002da82c0140705030380c03d5030b180703920400c0071301d40d1346e03000d00d4000041916000c2401c00c101d0f8040c2d416035000e4052034200b02ea40c50700032103600c0f01040040c407020031004902e1105008402c50302c1002d00d210f40d22521b13020303600e800440c1e440c1c0412900b00e1003000741d414180113115804109602c01811400c1ca030b502c00c0d0300c84110121070b004010340031030340c1204410104c1d6800d0040001900c0c401c4907042401003e80301035078120f0120099805c05816803a100034100e0000f08494200e400d60100000d1420b04584540c813102c0242ca02034180200420603a84203001030009510400c045442002107140681c144049a4400341c1400001e020175042a40c00603003241c008001c01d280098210220303c01651100c0d41c41085a800528010410010f01c4d0000141d50141c0c50700d49404a40e100d1640318214203214004000b40004d06100c0c0030015421705501a5070002070074010701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 695291384 1250 695290134 695290147
    0x1b15070503070c0b2503140a11042d050f0112050a0e01020c01060603180b04060b180f01050a0b21070c02150301050f0402040b1204021906031a010f08070804020303 72
    0xd02c0740e04016a848203110a18801008a081060101c605c08130041c3c241440030358110114201c18800040c5070340640360302c41708001c074401c04450844000d401c0c805401d0410b0024500120035586620001014804000030041160b03d05440700300c0c2003010507541c240c01c040401c86004c003c0c150103081211000c0e11601c1043c4a68803c0c0003a05c0700b251444000100700d45411b0005080e2150003c0d2018548120800d2802180110201c81d074403d801c00c1e40410340302c107410b000c180c118074915100e5030415104018040c2d224003491065040740e50440320311421945540c5049070a204840c01480c003507104201c00c0c8112004a1401035100009042072510300301190040399401c5205910b0b040d08600000060100380f81000c1c1051101d50151070850900d810400640030a1180104040080728010006011555104000789540c81c0f0030643c81c0ea40d543d140e00113000746c01101d001080301313000b10a04801c00d5105030001c0005d40303100d039034680058540000603640c1e40c00c060003d9070140400c1185 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 695292634 1250 695291384 695291393
    0x50306161e050d060902090907030c021002180a05060f0a0c0f1704090f110f1309110c0c060304050307031805150408010c0207150525081b15070503070c 67
    0x62203078030215600d420380d40300f100b85202c10451340075403c125038891050022450f140c43e40ca00ca507a000c00c05040004064268110aa1900c10134080c3d8888203400003400711112220010b20348420102a11503c000719141d00c1005110b00445d500c0d0a410f074800e04c4031049041c4107085a058250041c600c2c00b4809a8980344c105c440c890031085840b001c03c000404100c811043c1c802d1903c201c180c00000c01a240204510a4840c810018421015007022404110408040c85880f00400301d81070200000c1040d02c001c1445900031030000f4a0300d005503550b980e07050412000300d80c403e40d071004c0690701e00350b0555416124001c280e41e4000c14560990303404106501c1340503500c41c1000c01500030b10384a03071800304400d00391400340032404219081484d0070002c1e98584a4150285032160915a494000c0803205041852600c0145100ca01c2c007101041c0c148003209001344000c00c1001651803214001540e419a142c6112607029140c000000003d01c1a034440c40155411070290b1915500c0318915844 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 695293884 1250 695292634 695292677
    0x16050105040302010b03060f150111100f06230906150d02030c030114010f0807080c07060207291003061d030a03050108101a0f1f050706060e0105030616 67
    0x1c0460250b0340d00e0807401003600e010011036520440080d05c4030b01c3c610b0007042000603122344a052a05010606005080d650350901105c850519001030410075195900c040c0c20281c0181c1c454000650300b90700b2880000d03081c0c50100000f021004e0484e183c683c0b2401c042c0010700c54143c44c2490801e0061140d05c00e265100c0c001075004000440c641c03a169414484450071001000500340d0605c0700b1000903107402500004407591202c0141400405581c0d5940c1d82c1c0c1492181e240010b102070b100240c01d00800040200205640442d651a030807403013141c9040c0721111030241c4900820ad10700d06c0d800c000049031504818078681c508072003540403996001580d80365402c040154000b00740c40b43d005210340307442040b8456003001c8540d414059030380010511011403c010080700d009001c000d030758802513100c40031080801e5040b80c0341e02002030303410780c40200250402c181c115001810a04001410544280018160380000f001b416641c1c440c0d1080c40d242c101310300b140106201034000e0904c06c0411021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 695295134 1250 695293884 695293891
    0x40521010b091f0608060d260d0e0c06070f0f020102030d11092b0f080910020304150903020f0108041112100e0105040b040308131b0302040c0c03020c0616050105 71
    0x960495940780f407089040f2116480d40112080003801001c1200075602c84d1900040c89401c101c0b5071652061807580ba01214020101406c0c480d1000900500590700c3e81c2c3c0f011034060004415111810350043c1000f034284030310710004d0322901a9100c0c0c1408100c7e00201c00c105244140112480c0850b02004030040d11854451000e9914011031200c086042000c1d04160308046010310041d0220000380c200902581201d010b0107540481ca07188040021b04c5c070480d82c031954014025000c00100c000d00940e60750281c0148d9a0700403594800785581800b0f098480e082d80e034024031550080380508011200024010010740d00303019100e0b10034040e9202d80c01c81c0000240060003604003124516000015282d0308880c68626a140c002040041010b05a0403508142c0c5031420900a8a400d43c0c140705100d2084406040482c240455511110150a904040701d109880c14080c01d070b544242500d034024180070140240e0481c1a500c0342d18580000141004480206500ca03007c0094491608559088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 695296384 1250 695295134 695295151
    0x1701081f0f290d031209080d020f09011107030c0b1c0c120605180c0319240b0c060106050a0201090804080601090e070308120c0409050708061203040521010b09 70
    0x104400c0c0b01c807040040b4802d040d81d00707032008904560540c1c2c000305102003601c0c50f884215500c140702010051401c00300d5648203400c40040d500c403280300030070012540c0035011880c0401c480e00303803014070094042a13280880f9002038040c000203103400743e40344090740000ca05001503541a004d00c400d240c4588104020080701d59911035141e08040e40e5441150016080184181e031400c10b24810303201c51000a5a1202601d540d543d10f80e200c2c1c40140e401c01c09202c00d00d405050034402d4611003141743e40420f8980001c10340e11440c81984d078250b4402d0a01c50f500390740300c850b000080180913460040307000b05419101c0380300004c1c2d080501e450b9801c490300960405101c0da041100100246079040c05086d1b01c1c0d07801280580203041c95075a8100881c400d462070f101400009100040005004000b038a0050400000601c0f03640f5100c04003d1500004458440c0b00f010b100a49070007a4400006903000d44501038041c210360440c1c2c0303c1a810554601c05860142d42d06d80c202001e05803106403405000b12000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 695297634 1250 695296384 695296421
    0x18050403030c051338030a0c0804052109190f0609051f1b08070209160c0201080604020705151509130204091b14011701081f0f 56
    0x2514005040c0c0d5888011a41004010f0000902150340c02002808903644654a282d0302d41d00316401210141d40780c00412020b030717201510301000401035402503210300d290030000c100f07018402e40140c4042c04d06907406090366126001c4d0300015120070500322180c100818506007462003141c00268000b10b044000c0d2440d400303400c42085080a601e107484040c2007a81046082c01c0e00b010046283d4048007900b803401d4011481c041c8190324056410504808580c0590001000c0c0c41d00b440c0c5007550115004902800d0a140016070070050b03175680f5400160207949141c815003ca03001190340c04005408194480d50800c4850001035082000c5052000c40d140000181d280c05542141401c1c0d050074214001c1e108441003040c0184100c1c1185a43d40c0d0441e80007038040c0c450709014002010684001c24545109000840c1099554002c508000c0003680d500004032140080041040c20038860003002e0f610071500702c804000100c100c89040080c514000072000400e91058003130303501d6002c0301c40c94440f5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 695298884 1250 695297634 695297641
    0x6090f0b0f0306010305030a1d060729280b03061e010915090207060b0a0b091e06070609021f0c030807050c0604030e0310240f0605070b101805 63
    0x911001c00040990114080d00700e540c0355484040c1c881c816000c8410407c90495284c07091521817031580c1140d1640513001c69260364003442c00300451010040002d50381d10002c5196400c03006041c80c7c05224000030b2499580d82c680001c407000f03025002c01c03c0c2810307007034646101c41c1040c0c9080203028840c401c2c218458102601103600f05900050680050300101d0a055003006402e0074400704104964002c3c500507500c2200e0705002d0f000b00003203207c840c0c1c4542c5480c1c0005ea2041144080c03d20444125203500d01d000c030041000c0c04684696070440d420201c10300491010540d527a012442c0e860001d410300003514050034410154100b40354220001c100a1500001859400007101d07034055242d05103207107440f40c5084015038524000300000c0c1080302c00e0420b06881c3c1c8081c040c01c04d20024003002440845588002052541e2140c020491064076100000950550300d01903e0225130b0307161280c5150050359240c81c41d4680000707014000301a8004000200c0020760445d87d03000d420b28040002d124103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 695300134 1250 695298884 695298889
    0x20d12090b2118190c12050c1005070507150c020a0303051e033702040b1903020405090711010b090408030403121e090c0b0a020d0f020a080706050a06090f0b 69
    0x1a009449070142e5148621002441c00340080c01c0e0010070302059141404c20814a4400b60a01c00c681000000d900c9643c2140c04001c00080d00e440d4a00048520806a0030038500486190094010243c01a8041d1000b00400c548014101000d144070345000d0035070212a40114a00c070210394411800600005035600c4030a00070780e17001410208064000d465428281003e450011b00c9007200684441504806000c22070a050710480c0445180c10564803103036214400d60168000443ca201d8150f41c900034200b201e0300c00d01c226026944020b01280c00c94840c500c045400407480036480314a50740e01e0f03010300ca05545500d24a4861481005550b90380d01d814680100400c0361500e410190b14203044004507900f11080c0e5543d4906840880061620024201102010003a41c0000b01d40c079070000e0120a09076010980101c1961280c94007100b841c200c03c4200c1c2d4502c8000c00180030101d0a00034007001841c141c01c1190001010781340402e02d141c44405440c111401c280b40801220303900c2e00c074510341c0e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 695301384 1250 695300134 695300197
    0x30a0c030306050d0221010b300f2802090c0d0b180114061b030a2c060c01020c010624020a0f03050c12031009050f04020d12090b 57
    0x1418103450016486010b91701040600c00840d6000300b01640303444884503c4c002c25841118003010080c44100302030044001c48140c8012001c01404003200e035490f00350400c0c8005401e1011029040061200c1c64114100005201100700da50038100840f4410781d015940d4602c410f0701030504203280c25582d40701000c00700202c82d090b0041c0360043c0303600303481d403500118101900e904650b40e6840a5070b41c4000c0e000050f24a03c01e0004a55050070120050080c00100101a0207c4041d41c0c44031103503060b1201c0110f1101d90030703d40222a103902c3c44026070b841d0074101c0150080071210000517051800c41001d1600751a09600285100c3d456150850316141e0101a840006003a50014107410100307521841400c485d80d14000d01030080000d10354942180802c41024541603c02d501d64481c00c0610f1603048903a614416090f48908020208000702c811044031401540e00400302882000182e689180d600400003402c024041c0c010000640081b6070740007400b256500c070004145030040c0b46807143c1007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 695302634 1250 695301384 695301389
    0x1060306090501050d02130f0b030a06050603010b1804080703051c090201120b030a0b090c131a1e0d050106120c030b070c1a0919060e010c0203130620030a0c030306 72
    0x283d8840811701c002d82c0b60140c620310b100203026401b2070007407400c0c000380c0d0150580018154040c80380c8000391040c00401d51009018000490003840509000700c01c000a01d0701c0c402056100d401c103040410001043c000040c4042886030030038506100301e2441d60100c001e11001003001e107646a00c200070442d84e00030300c44003640b2100342c002c020b20300711000800c0d510900307000300900315494800800d4064038100705400e40d0460003080310102100d04207000300601503180030000300f44550714101c2940d10b88101c10700c0070010030204240c0fa2507001c1e02081100545210107681d2075680b2400407860000f107100807240a806800403506d0355217545420084440028103040c10000d4034280b0000003542d0707106102c1003560b0b00c004850b498854043c00e030f05000b81030500c80301003400034444204100454205400d18a00070000304891111068141c2c0c41780710784001075854910f0850b040c020140070340c1c801d030b1090f07105a1245a07426646525503140d580410001c60100c2c441c40b00d2039003010340c5800350002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 695303884 1250 695302634 695302639
    0x60b0301170c0a0e270d05090d02030604080417030915090a0801180b0108010e0705060d1e09050c011d0607060e070807150c081c0b090c0a0e0103021213021302030106030609050105 79
    0x108075985c0004588814010341c1080810a000409440d50342d03e0341c03402081e542c2c0080554000e400c142c42c0564155101d84584018030300140da921600c2c00c8040207981c002e00010f00100c01e03103086d081da09100d65201031407041e03001102c080046035400d800d11425480d0081044a1042c0c14254204001400350590009030a0707810030810343d0304480045504411100f00f80c0e920341d280d20400c4200805030003440c00c40c0710f1904440c15208914580368004960407805007040ea80056420001102c005d4251005540c0d4802c40c051403080c3d508210780149070080c0202400076545080e100c003607003882a15031007022550f010342024001516115800942d010322070808050b103000594a00e03078140038020707500c1013040c110601f0941d85140f030b8100340202d580040c450302161404c0325103183c2580241c07034004000382007029a0200c55000348200d4408401400b00c000403a80c50381f0540c0204c65145908980041d901801840c101c141070002d54040c1210f92408591581001c81c10030840d03e050380404e2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 695305134 1250 695303884 695303941
    0x204061d030c060c0a05010c09050117060d23010212070206091b10110f01141f0504021e21070509010c170c030a0203030105090a060b0301170c0a0e 65
    0x554075070300001c0300246904190388260b10b550340740e28018240780152002030060f5081c4030070100825800408501500c800340c07a082d00440c2000408066601d0031100560003044880780803020071841148194071200d00c1404400e2940c030408c440d42a82c0040000bda1086603c6051140c4d035030b018007000768804807030300041c440310260401e8445004241c40d01a40603a0764000091103051085081d28a00304414044404400302101518001c0c40e4581d20700030002d1400e000318020b502e03030614a59899003180f101460242c105410007009500104074200e100e48441c013440c5a1141440140400004040300041040c143d400e80413868400285501c04002e0b0800c030700d2203141c0c0c122082400301500500041e040e4281c41c00e43c0c1049104152413911140b10100d440b8402aa00000031416038030251101000358850100140c2502c401d80101c0501e14010700c010310078580c140d401c1c91021a47e100c122282d440c0c1060120700742ea04180c10404040e00540c0401c00d0745044180107070740e041a14002c9030b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 695306384 1250 695305134 695305187
    0x40606050f0607060908040f06020d09090b010c020112020d1e0c080c030705090d0b01180614060f0a0207030b13030f080708061e060415091401021009021210020406 72
    0x510503210f0244000e140d10b64412003401805044c100303880181a41e04080e100d442e442e80700c00303540e43c0c415440100c0010142c0002040c80181801440300b0018180c48000c414a03055006445480c612940c00030340c1f603800e0004401c07014a50180308641c0301404440d010703601c02041198248e5035024021014025141c040c08040f030f000000b00e0754080390a280c50381e00c60344c4080000c0d03100c105596018200b10006000810f600c00041c122041c1071103201c0c010130800e80d8031803034140c92044d8801c9a5174071200504c2600051000f0200401c1402c3d01841070b11204c58407950f030714000e080161803006005540c10401001c160b00b0001a004403071440c2045000703443e004500510f001002441c040c0a203a61030081d6182011003c40c00c510054010030140c0c84684035149040b0740031400c0d414000041180c1d100040300000e841d49040b04c81410707030181a81d82040c00106000e00000e840403600204410070041c01c548080c00004000f0205200140e07445280c03000040020900022818414600c1c040d503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 695307634 1250 695306384 695306389
    0x501030305030103020409060b0406080f01151d25030f0608030909010b090112092904030206041b180605010f05040e01150c0c08071d090c15040506040b03040606050f 73
    0x50b00d04507541100c0c045040708082c0b0701607010f00981001d05402c2420204081006003001c01c50718890300c03002000700b01c840705c00100e00c0301445c0113204038100e40e00c0d059215640f070304000c031007240d10140301d20510f044500084080700e4190724000c04407001270b0383c500b00c08c1c09102040c080d0b2001042c02c00010341c1400d08980000309802018481e54802c01e100080b003400d180d0107440d4011000320310b00e00c00c0250001d642040e4010240c1541c0c09107008003170075400726018031064845070107030750164003d211a5560360384280c1c03070070600064802c110100050015580481703003d80b04401d80110800309070035190600140c50111b181c9050303400c1c0700d420301003804500780c15100e80303044031101d07460315060129440003030b9020030500d500a002d65030055808110a600080c581c0d0484403629184000305c181d206019480e81801e99050741c40380c22000518200c2e2401802e040528414400850301d4140d9540c00a90725610561100f1171000c1f01004020a000141c491580109401d5a20b480c120425800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 695308884 1250 695307634 695307637
    0xb040c090e0c0112060911030103020a0b27030a15020a080c09010f0518040207081b010c050304032d020c01140405010206010308280c0618050d140c01050112150501030305 75
    0x91030b9040140a11110520700384d41d8100e00010403003540c00300400e1040300c519910781e50003400180d018034000f0700005601000182111448041c10180c030b00c0c0003c100403000d070070110700b5414aa00d4481c002d99500800e501128030081041c0540300103950300088003002c1c2010f0300c0101a008402c40600000e24aa604280d203011105a1071401540da00000084003400d102000d191680082c0302181c00000c04c03d016004080c0683c052003c1c11104401300e80c41400c2e40c2d00c1d0281c42c80040c42c05d2012034000b901130f442024103460300c0d512034481c05002d81d0994841d03641844000d001a485042507010550300110041d002c52484060545000d00b00740010703540366018800203003026400a4101c440c101e82200301c2200040d140b0500d0b9600801240c01400b0240b1964123581c12454003c0703101f1008210b8050900c4294414041c0c4000d08000105548020301d21900408060b010040105001000c0c403982340a040400010001c4080c80d06100140240f5000c22190030b41c03601c0010300100e5003200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 695310134 1250 695308884 695308903
    0x203180d11030a0f180b120a1107081b0d08181204060f020f100f0f05090d030b010201020903030d090b010503070e0f0403110604050c1311031306090f0b040c090e 71
    0x40051030008584130848420a030b1407040c607044404240d01081170001c500050000b041c1031483c001e03403502c1e000303040c104a034544a200c44010b034080007584005046100900001c02c40b52100701c2500b42401092410141e94420700070005024008010035282c1e00d052128400000800414030040c0c415055203035480f170f41c00781c07105005110903401c841c1c034401c11804801810070f0060b60280305d80c100203103010b040b0000c28140d074181406100c0f04250620303c11548a01ea11100030141000450000e40042011140a50465400f0440b52246807030400043ca518503071070310300041d14000c601b051612808180c00852107600080020009070301800c982580103285a042c00318070303450318a0160b1350100003100502241c0192b03400c00050040200d041e17800c40720103580d08680ca4180d400d42d07a00715131541e085c010f80b1038801d00225030380c0c1d002c0d03d0000e201d451144400241d03580254031109141500014100c1b0160711500410082044078a20040108007460040c000d440381842071546890418 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 695311384 1250 695310134 695310137
    0xc070201050f032802031e04200402040b07110f0603070804062301060e030f0115030b04110901030b1602010204031e170c210c031210090203180d11030a 67
    0x2101183d00400c490070451142c80000b207032141d40d090800700c01300103504100d540402a84140081d441d4031100d40c1d0549205603403003184800103031003c079a4401580fa0341d14805030016420310010480141c2c450040220900582d059070845d41c0030010400e4110302040070500600b414024072400ea90012411900b140d4000d50208590107880d142e04408440e54100010030b90b03181000199690f0401144503100c031040d0300f91001074501d07140701401c0e40c1840703054005c0d246c807882e4200089022400015002881038086080c5126403e0000d030340c071030003a00243c1d11a280402444125800d95841f1000030400e80000d41c100381c51500c7d01c2d10f100950001f0300f0340d440101c0b01c0c2e100401482c5c22031411100d210304459500c032800702e18142e9550070068550600004203100f200704200d280750a80b5200301c07500e002545062918443e2119018000d0640d0500f14a80a40070855200c0c40c0003543c4584c6080390400c1c2e02030782d0004554585810844503c0c14403a80c800e99500008001c001c032460140b45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 695312634 1250 695311384 695311387
    0xb0402070c050d0311010f0b0f030616110f031305090708040c030f050a0b10061101020708160813090902040501051009140f031e120c06040204091109041a0c070201050f 74
    0xd90905440d460f80454018000b5440d000c40e1519040c034591000c10b02390030940d54012041055418150303140000d651030001501301000d10001e05104030702500e622500315080e00e500300043c00c1c695145401c58000c030000210605130a02c42410880304040d448103c510303040580b4246511600c00a0841e4000070f09003442021545051017002c22030f59100c43e40c04a651030300da00d001145026007c0b45401a400003403a45030070071506c03640500030303585444d8001c040d5510300345800315600000a4409011a80b400d0b003402600041411203c0c41801003001c6034000c200c40d00a4810401241d105810444c4901041090300d40069841120b0300300340e40c1041740c0030041099000000300c8121451442c0c5605108031800322010340d00e0170810043c0c200c2c100084130b40c8941c800d0303007983c2c2c140a01a0200141e078003040016000d480c080d000440307502d000303031128880c0c00081c002003200001c082703900f40d502e00000101790700c2c820181c0c12681c1d40492000c81540c104184c07680001d01c144152030003041c0c883c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 695313884 1250 695312634 695312659
    0x915060d1a090c160c050603040f0605060d050309040c020a02060c010b01030b2b03030605130608010b0a03050a0b04020a03060518100509070b0d0608030c0d03061a0706150b160203010b0402070c05 86
    0x44854174402034480280b48546900e0315281c00c0615056030202101c0c0e0500340804504075040604540c04995401005981024480c1c41404018200014040d085201e0400d260002d41c4076440106051001140007190320001400090705640510b8410b500400746409c1f40101c2010708400166504415a1951f0305100141000c901070030450f085503038010460002c10310b5120740c44c0d11140c225020423000303000c1600c03a41d0400405c0c83d8140310160443e00008103030b1000401c9034a9882e4080e10041c90107194540382d80f5034030100d8200b214a1065101f1003060240b00e030b00104844940c241480c103040c0224903104084d03030307140c0c0118420f41018140101d20b0308500002c0e50419006810300e6400c407600c42031440b00d2150384080f500a2000824a00a4046544203100d0340950f158510005450311b05925540c0d0071b0002c0501003010764989081e0000070901c0001c602c010101201c0100107521003e2550040500b19013080340303103d10a85c41040201c2c0010044010391003250360440d4034140141 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 695315134 1250 695313884 695313893
    0xd050d0203100f060f081014061c050103061410030c091802040908041d04081603020118050304081002130b1e0a080a0507020118020915060d1a090c16 66
    0x2d4040d00b007080c2201d414a40030484a50103403064050400d103a68250103510380d61020011300089004183c0d07000b60003d000001420134078001e04080040c5070b44d44110b80c03a03281a0504440003a0400ca9072580c860040381940f12001030880d4102155400e481d900500c0c0d03a44a60401d03140f8410b030080302d5212100e280c034a52030605001c12642e0054000c0c001400146400d114a51040c0600080b00410000e0120b40c05009c0c80002e2241307604c11840c0d4905205800c401c3e600c0c8200403000c504642d25480c0054910524400300c01816210384003c1da16541850511800c03c840b84000c035032103610602800c500d611211030320004903040c00b2145503480400b03205a450002071b0003801c00308004c00052050f102503010203024825040100e0422040d1180a0224281c8100d08050444107544416003005403402d420b1650300a03041c1c5e40f4160305450340c14041505900954919120240d884400d8030582a034800c60302e03130220342158610755502d4072080e5204580107415909002481e40030100c000c20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 695316384 1250 695315134 695315161
    0x1d0703150503061609080a121809021605060a0b0a15090e0c0a0e0f011d1c0f05010e1222050a090905070602010c0e0d3f020d050d0203 59
    0x904002d42954800e00d0600425400c05107552009000200d0008001440c0c900c04192241803940c00700280c500c0241c1110704664000d100e08a11214002100c400288080c1e00c2c402030240702241c5c0d44d640c0e0000300e6170034107608186005004c2c1d00150308044405190783e0310580340d042074425005007507003216969981142c550740e145c1c01c22400848002c061200c20813410018001d22030071540c0c1c05a030102081c3c244142e130407909002c640404d209000056880b26003c00010a6442c00361200b2640f01600c11702094080c810401a84d104d0505000c0b2006d1190a01404e1490840e803c004c00a00d1034006441419200782e40c1d40d040c00c1440c40020340803e030940c41c106801804010a62407010b0740700c1c680c000081c100528210b40702d100f4042e0000e105070047c062210083d200340c642015840c03260090048019030000212442013007000750b041c40051846030a9001300f650086940c150720041a20942007104180d101d0075580000e030000d581550120864002103a511000760b141c0d2118107040c50794 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 695317634 1250 695316384 695316389
    0x80a0b0117070b0f090a0833010501080405010e0303072d0e01080a0b0d0b011e080607050d0f0212090d05094c090605040f030209100f090f061d070315 66
    0x100440007a03600d400103818800c0c0681c11412601d070023062440381402001c24001c0501808492004000a600840d0f01d10b902c50301550020038201c0d42c0d400042d0455000320389100114100003903092903144030a601e03800000020380e0480a4030326801c8064440c442c0c001c2d200d410011440c00054107100750350400304102c0c5000e0242d506521881c034112413000c009020316060380d4035451603904c20780030750031000d0220380f21800900801d49801008a81e0341d03100d8060116081e80b505400050180b5900c000c0c4001c104002e003a1166041265540741420203110342c0c401004024480c00c001c5903905003130142540d43c030030034150088005080002245080000306011400300c0040072507540b11608006024a1041e56010b01a80d1501d4055549000d60f0242c00c8040d600100184010700302103552540014206403007800395540c0c0c018a182c1d60255400003035010351186402080150603005034006080d1500c0c0e01440c0c0001c001000c4126007004007900b08140d1940308141d04e904182c02e26801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 695318884 1250 695317634 695317639
    0xb0604030b010303020a120302070c0302090a02120c09040c1706040225030e0918030301030b0a06170c030606010c0305030f0402040609141b030702030714010f06080a0b0117070b0f09 80
    0x7040da56420003949810581906a450030f80c940614256184280b00b21070071554406a01500e1505580a10941c070301c0007080201c04a60800107985c600025150103882a020011b040356909018000d11013030b904c6480180b010f000d50b80140324806121072041551082e825100140c8400d000c0d515160010f502d48007120f81380811040a030309069103e00e54901e420b078191460341080c2c03a0003030380b48403c540007801c18085400174801400001d41c000c1300d41c3d0f0025170824001c9000ea0f10b41c0c44600a00400e03460006196110806c1403400381400e00c20a0b41c0040c00b424070100d87d44140e00d01810070700c8024104c0845a1140c000101150740317903401203001d4043c8000030082800c00c0355080c01801c030140c40c0080d414282a802c0c150807501c16084074824029940554104501a90349418032182c406070719840f5500c03469084280304141c8070710b40c01001084000d214860f1107003464000c0705030682180d1008001c40e0f1107020850000603100c0e040714140f040d082c1e610107003180510b003280904d00d00300e41d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 695320134 1250 695318884 695318903
    0x507051612020f030f0a08071a0711060a1e18050303150a0803040501021c111203011401020d0207150c1e031209030c020d150603031d030304180b060403 67
    0x81d001015840e071a158a2083e140d58811108040401d81d490f0220141c041041d404200e4190001e405280640005480748a0050080c0711001c03546007008022142000020081c0d001c00c0c4000c1c1041007540c4d08980360040030013110724210400903031401c419250500264880310301401e084d80c00e02200d14140e4100d0256501c0342050710302105401b56007030390180310b5a0000d0010540c0308002c8115030403500141c0007845202c11b403031f03003000d07083c52190406005c2c08582c298402c50a001403008452010444070103030342d01d60501100c01c1d40450b0420800341194405072441d0342c200d400041c05004d541704000b05406500c0140001c40e600c20203018010a0300c08240b48144190980c6020025841c9c42038441084885411f01c81904448011001a00051102c044d80b070144c1003a400c2d00701c040d40140814084411180c02500030340b881a40100c0005084500100c2e140224900c2c6001c1802d048019500e05403800c01510104ac80d00d050810351031340c0d42c400702da03d240e40742d4044800460b4000d2004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 695321384 1250 695320134 695320139
    0x301030b070e1915091a030a150306050f0a0e0105060a05060d0e03070807050105160c080901050409051009200403080906091809010f060302030618100920190605070516 74
    0x15003049103012131040840e540c81d002068000d0303e0409400b02d0508018885d0460750b403001d0041c003425018580340c060114000e400320206420b809254414030700440542442e040011030281120096024281c0b1a4903200601032319a03241c8200d01c08403801103c035607440f10950300c101802809860101e82d05031200040c5c80341003102c0280a404107034098002040700f40d86100e031411802c801448120300154141d16800d0014803a40c02134400c50340107240890406403a2080300c811201d09413410010101e500400b08440c18442c0204020810511403080a2514105c2048414011804020f01b813003000300f03403103000d0380741c040503540ca0b01002000c19140c8120b014046910400c280d500c1e603410b509248144504845501444040f650f010700103028030ba843c2030003020050f00b82c0190300e0160160b80c0042004031120700800450b103000ba100700550701c1d00c1e584103882c245002030402d4085e883c2c3d066041350032204980854200c41c09810882e690f42610310742941842904100e0006520703581c1d501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 695322634 1250 695321384 695321399
    0x10e030106081f051303181206091704050d020f030a02300106062010020c0d09080a0302031b0c060304060f0b0a150e0d05010f200301030b070e19 64
    0x111615440d003101c52152910a400c3c0042030301c00c205e40240c681c05003801440000ba20801d0408220840300c02d01030010383d00c4420742c64240d11802000e4400b02e840d0b04501080c00850107580700f901c81c501003d503241034940360120314001126000a4400c00c824818400c5a850a00c18081c5aa80c020140c0211107030f0068900c0d00030400810f000d07035420144240c0544018144180e200743c0c0d21135111f01010000c3c55019404c440c0c80c01240d82d909005250009000101c00d0001d0600aa02d40300a0a04101090b50041000940c2d41c020803869002c9058000480e4001c821110b104000510800d15500d130100c50a1410f81210046600080c000082100340103603030307000d01101c03064a83c042c808000c1e10806c1000003e0b850007011580d40107800300d160018094002e1200c1c03401e0240403007440c1c0c3c881da1a203500715298103d00c0b00c48140c88520003500d200039460b09108102c02c585000b415541952034003c00c010000b44100144065803508441c20381e11010703928500c295036000038000030313200c159 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 695323741 1107 695322634 695322643
    0xc02191e060b1009060f080f0a0c020f100c1b0b070f030b030109120206010b0f0904020a05120a0b030d09080c040b0d0f050c0f0405040206090f010e03010608 69
    0xa102e154a484002078608241e1240c0c48006800f4a0701c4d00240806200c183c5500c10850030008020003034030030109144c2c028950304800110817002c04010782c6041101c032102100c1c0d100b0318144150401c4690404081c00c1456582c0007002c0000e06680c00c0e180c0c0000c640100303601020000100300303c1c0301e41d20b1005000032920700400c180f4900da01003821107441c1e4400b50741c0d01c03d40120023400283c040110314014004110001e00d8110501000000b9008100c905813045400003030040c0d8040c400c42c02c2d01e600d84070145180310b071360030480d01032310041c817210034054000c3c0107104000541700e00401c0780d80d0031a192280034201c654804d00810000300340086c2180d512000c10207415002ca80203141c0001c2542c071400c010040e940007081005038080c20088081c2c461820541000300584455050341c5071070009807000d4491118134001a40c1400b1800f00301a095840c1000000342ca000024 = true := by decide +kernel

theorem cover : BRFrame.Cov 695143884 695323741 := by
  have h0 := BRFrame.cov_init 695143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 695143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 695143884 ≤ n) (h2 : n < 695323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
