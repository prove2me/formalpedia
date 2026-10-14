-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:09.624189+00:00
-- url     : https://prove2.me/submissions/4d5b68de-feec-497f-b7b6-2ea77667200f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557014388 ≤ n < 557194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557015638 1250 557014388 557014399
    0x4050c0904030f0912020d08130801060f0315020412080c010e011e0f0b01020606040b0406081c08090c03031917010807090605040b06030a0b0a08030403030f0306090e07050f 76
    0x44422011038a825022a002d40010f0340c00c050080100f9046000c1001800b40c42d4855190004590045281c10200ba50010000100040c5034004140098101d101600c594070003444800d41c1e80b949001c2d420214003007503454134154074004203406003900c22541155404400031083c484a904c0c2c1c49126045808508c50035506d80014034054603081c07107240010100700c0262050060078140e44001c40301d083e41c074150348501e00000400303260b030009103a69100e88100c4011403042540801314000d08030783c0d07102000f14450320100a4864a41c401502c0700c1e81d5066450381c16036136440c060b4076500c0c5441c1d01d502d5015001004640511170100854017440c01513410464803010001c1c03441d036010030091703001c034110f50004041405409207034020800104411101032180c440a1000580148005032220500c02d035140c1205840d504c442070041c00510f12502520380307465490a000d8107203040412904006898054042145202c07403240103d4100c0e244000c1a4450a05040c400403a0404040a43c400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557016888 1250 557015638 557015653
    0x3180203060403082d01061e080402060d14040803070e09040b0408070c1806050924090601140d0c0315082a040c02030d050c04030203060a1e0614030c0a1d0405 70
    0x100d188510303120741d000001703481403640e41c9810340c000c02d4000c060354140085801c103522a02d1240d8403050254000fa011260940c1c3c07a800e0305001d200a080030030031504041c1c1507000b00002d0111100103180324500c1c0d91942d0080747c7c8507008000d540d900803200100804140000f00703000c40c08a2014000240c49200740034401d94440103034103819036046088440d00b1780ca5440038061400c011000d00c0e004568011000e0b40865403040c040b000c0c0340ba101d502401003401c00001041c036072098400e040303a81c0d494130060740d0f00d035103001000c009030112280100102e41040605c00741c8448800d1000115007140c00505070303003075404011550030752406420060680020380e40710000c0d500c0c3e100d510000e8400750000c503a5001c40c40380c0e007415540e001b00303e0301584c0c00a000400150301c0200f20a5405010b006000808021f465058800c000c110303a00003481d586014001304910706070121040c0141000c404403039290f1110010450300c0320003402001c20300000c50030700701c0300f0848140c200340d045413041d4280d8800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557018138 1250 557016888 557016931
    0x50a0c020f12100606020c010e1210050f0405010b030a1e05070519080c0906010215090a150c1205040c05151b0105010608091c0507081e030105010318020306040308 72
    0x20080c000780004180c0d0001030b002c18001c003a41c42213030300030840c0d4005000e140310708900103082040307a400450b0107082101001c0e1342c401410702c804419010801d60401250030506075000307529a04907000c49080d860a00e500038107243c005201200c03194062112140c140025050f5401210f80d0202150184909980440c480e41d8120780759120508c1c0c00c10300c070080d6280c00b03520341c50300408141c803c0c059080039040c03111503617020410b03010204811030201c00c2c0b500c0b10403c1600d80030142801401c0203650030381c100040b02c800c0d0000b14100c9041c0d41c0789039a0300007078144c4100721030040c0d81c0100380380121792041019050250040d00301030240140305013800b04003480307507225152a01181d42720740d5440e40180002c2d5000315105800c241c1c42c00040410ba00a10008541d4000007101d4200384a40800c0c1c83d0304000f180c804840701c05503510108100400a4442c05600b17400a008140c0401c0c1000103404903416564281106160010001d0003562240c0d181a5042c0350302800130b0800c114070f0b0210f00341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557019388 1250 557018138 557018149
    0x120304020a2d27090209130503131415120f18030304060b0a150507030513030203030d090b0c070b01050f01020111130312050c10050c1c090b0108030a050a0c020f 71
    0x10403012440080d103c81c403031030601c3c04014031003804015514210076a00940c603112600d0340c0c001c0c3c0d60142d4025028041c00c01c00d01e0341c09441c2202e00c0c28103442c40c2c04501031082030342c44900c2c000151340d58a5200d0900160095034011403a201c40780c14108000124445c1c1034004064005024a1510900c40148a00300782035501c2100c050300c400341c0703610300d500890400c00325007c0100f0440d030040000c00b200d18401000c40c421500e01500304480481e40601d24200400307000004c5900a0849543e0307010f0044107000b400706240262007030003103000081c000000e071004440071541c5c03100580d8101d0303003442c04001d6020040c10302281190740e507035507041022078081c1c0240201c03048034610300000361a40c900900c124103030590030310400a0600980781c80c07010024100302034035001c2130007207040c2d42c2e0002e081e102c50240d900c00b620542580c071105410010560b0011200e58051184401c0c02c0c0e03200d0746801d81e00c1c4030b1040c50800045003000f1000c500b84c071903840064000d10081c00480740d011300100085 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557020638 1250 557019388 557019479
    0x2010519080f0601020105010b030414120403050f0f010b010e060c01021b06180a020d021011010204062c1008190903111c020c010f02070323120304020a 67
    0x40225a0034402c1c0540e1960060255501100903c000d000b558113245000d0000d00019200420002c030505090f0200c040074004002e0a40c08001d00c991034558904069a55010f0300c0215032040c050301c0c000e59454074041c01480301840b0b040c5c44080c41255088184899a4454030164826541c01c0c07081b06800680700355030210000341c0800030900750610300810f03000356001d500c0d45c00165208078025001600c07400f82ea0410990101c40201c034840740f05c080cd441841d025408031300194030000b804200c032a00056410080c0d1540c1500b1190450030071000f0003204900400036510610200442e10030a1240d41d5107548140800f07108890103448000102c00ea4245200440c003148000d10510509401003080400c2c04080311007500031000b00d9a00a521442500d088504000d40b900d80c0e2070b1024000c2209400556101c0e60740c001e201c1c01140220030401c4507131045d080380d000300c4d0300300140d038290f01c0c4c2520f0045070000c0c01c00c02401c0ca0490303600500d940008400b42d140c0011296441142c803c0768020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557021888 1250 557020638 557020687
    0xe1305010e0a050d120204120605070302281b0512090a0f1508070e0a182415050406020d0507030c0203030c1f020412060f0905070b070605070921020105 67
    0x404031020700700030142480c1039141200001c03c6c4140020001e00b90001520090b06070820000266902c442004502900c1070505041214407182c50003200040f00c5d4a2810000540c4d564050890840501c4e88014542c419070242c010b03800980c0c9100e80140b000003d100c0c0341401003034000001d5a481c3d0b1020394a1580c0d2050350410741503c01d51140e940c218440690140607850861407403100c2d0300005e074040400340900344000c088900f51404c00d5810790710111035080326106004051110007010100ca1000780101500644045c01001000d400b4009640c00d85000f82c0160002c01091075085a55402180c01902003050705201280540c805100800c0a140ca40024000c2e240f844190103501070b41c20300f0900c208a2042004002101c1d640708030f000345581c0018046090b800c0c030203100014100240028250b80618172001070010074050060612510446c8280181d42e208042a90458241d2080e6007513110085402c0344050004006d0008080c4141403103410201101b607040700d440d030783c184003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557023138 1250 557021888 557021893
    0x306130e070e0a0501050406081902040f02040b0309070602060601080a05090703080f0a14190509040f02271f050a090e010605040603180807030804050a0203010f0b090a060e1305010e0a05 82
    0x380f206000440c0950741c05405c069905000c1d05213000c032003030354464440b8020b04880c101c2c81080c000315907860b041a60601c10080080d52a1501d07907041c0601980b043c1d803410b6143c03203101400600e050020408503c5120161038030140380d921010344001809000b400e9002a000c1d20002200052050000c0c16220550302c03d00390300c64820110280c8036100114640c115407406001a2480540704e125000000703600e85020ba07101e40205010501900320311032070380042d50000c42c16000340f0f00d03501151a50300a500e034090031030000110500c529140c00003010411041c0d14407640c1002030003039008000610042c508150520b9846d07003801c68011003030f04885c00003400007404215140d40350250304002e2112405510b14480150b03074030314407446080c0e0020181b01c01000003c1c00e004092103503107800c5070054000d10900900c4440e0b88010b00310000142e00c55243e0308082005220a807240c1d00c1039900a03030240c035668480d0340211102d1014408100c44642d02ca8082d801c10030010712143e415540f080c1c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557024388 1250 557023138 557023141
    0x90c0f0a031a1f050c0705040e011b090e0a020304020f0d050601080f03121f03050f0304050a0905100311040b0301240611100f06030506151f050306130e070e 69
    0x24000c011801102d00e6900c581d1946408100c0f201c0380300304140f0200068100556101045d100107814624954000c56206140c125403840e903c0c010f400c901c011031441c614014400703041c05815103c00203980140782c405185100018502d150581c0110380280c0000c08581031186244d000400c5e10071684800c076016048003004204404082141d2107820006101440c100105074200c10102480104039071040300c0341e09030b04504041800141c50255401405039124071082000040d41c0c0d520030720809028000c0070f000018010418828035004400c0305c1100c0c02518955161201c29819004c0200c3c4c5c05a07544201e13100640c1d0034031490301c050040c030303480c070103495003941040303e004000341e0118003840703124542103851100100c1c0c4181c1d04040e020380001d4081c1c0c1b8105803c02041b2603080100075100340d0080c88513804c2903c0240c14841c5048aa1000611b10b68032004d000c0303040b044181012540c01d00101c0e64a290440700103480c0c07103040e400020300d0710f42c00d201985402050340c40003540308400c80 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557025638 1250 557024388 557024411
    0x6040f05010f091e03030e062d07020604080106061e021506150c070e07030228050f030c03091018020904080f03181516081e010906052409090c0f0a03 66
    0x21007d10200790103c81003401d020341c1e410820440302640d82e5600400400c60787d4840c0311010b00043e6100c0a801030711040d200da48a4441078000c0c81c59019640214040c0103202110803a0720b8494840c80601c1c2e8040d2085e42e880c00918452180081d19582c3e01c0032400c4503007503c1c404804045d00d4507074400310082042924111440e0350600010f00300e0010507004001d003190349034000042800240c5188400940c290042c1350456a0f40507006035102c28010001c00d100440c7c8400015501406800e4255602ea0320402c060384111007a05101500d65001d100e00c0801614240d070003550b0190180d4015440d003003c05810300c0041c0c1c4104c4074000c450402c02000e41000c0340030010720a03003c8000c89002c440b800d240311100782202603461444104106500081c0c00700122440c5540c50714410500c07503419584a8980c80040c2c521806039600404d01200617494400410810114100442c03900034540300c0e154040c0000da840c01406a804c0307000030001c00c40ca20b143c500080c1400d0711540d800051104994 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557026888 1250 557025638 557025647
    0x230a02040f151202031c020a0503030f1509010f050f060909040506010623030c0a1e0f2604020f030a0f06051006020a111003090b01080f0c06040f05010f091e0303 71
    0x103402c86141030f800301c3c401e4401070700c0c001288025a082243d40000a0085000891500049800040507404003200303200c0311a02d100021401890086580700c8203201c06020b01c01a08004d00c40e1030b500300d4100c0010011404c021841018030701c0058103662410240700c020800f84101035500329620341c007110040000d00d501c02030000045440c078070390706000010511900c4160002900842c52500c000031500c603800d0003210f170b560000381204403e8800188683c806061600c107102a840490070340d401075427117035a1000c03211424480020003222181c6680e020301201d40c040d164140d030540b1035410f107030b0701080c560340b4001e4101d881050040f0f0035140c01d140e85401840076601401c00d5502240c9024005118402c0d049400c000a42e1800b000c031b0b1001c00301702c026105049014019050740e10002c290b40c08041010211000d0306022184041c5440c801d00009120354801c041c1100c485031001c1c45158801c0892004080403458050815a19040041488031100000080c0300083c500c1c10010123410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557028138 1250 557026888 557026931
    0x24070609051b031c03050c0903010c03051506070b150d0c0b03042609042007031701060e01120e10020301060e030601050f0a09200a05030a0513230a02040f 68
    0x2034001d4a24000d000c02d83c4c13100002c0000a42e0141503c0e040000c0c00d10082c04260740c0759000c010004e101c81100e000000c0c00425040c3c8640c0040008480c0c41c034440d0400008440c00c1c1a4080400783d070507900d6011074000c1d08a00032199502c170508104450120b0700615000d0040d100181c907403941c03030038603190105030104c007038903c0000c4000c01041d541c2c0c080f20340c07401d136001844103481c0894420030304500700c51103280d10030050307107003060200c3c80c0d40034146c4c040b03110707500c540031040200b0032641c03291000c0d6404203103044802d00141c503401042700e8034402600f21102c050461000c40d2401c280381c140b81c20990b0400d801180010340c156603411114a41045903500401c2c05032002260b81d1842d10100f0302c801d003070b0300944600d59100c030b007031090210034000c2e802901c00d00c050545403104000e40c0700400990050340c41131070586c200400705030360400b000b000f00e6807a9031101510440030901d12100401641500300b500d05402100000300145c0c46d07a0140088001011500054207100d0001d0400c49861 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557029388 1250 557028138 557028193
    0xe0402130b0c161e05101e0c05013303020607030c03030e060c12100806010b07111e1f02060f040f21120203040804030308060a09090803242407060905 66
    0x715200d15460403034004201c400038849a80d440c7c00050b440c90742c20740341c0303141e43c2c403000b00300b50718005105410a011081404007103151800304c01e001d003031000b1045405c2c10140006988107208105400000740102003e406881c40781c100030400e0600035410314107110084892810302400001c1e655248020010000da2100d000b0152144180c02d1913029580c800301400b824402d00d45c00180c60080c0440c0880000071010008d01c3c040314100080b841c0d0a80b41090204039024181c0c003500120701d410800401040d00d4143d82c0100040d030380d00c9141c1c01002c500504161002c0000c2101400071500e800c21029100058001c515486e0700740d8a4000c00300304161003080d48540c410b000788000a9422400c43d03003140c0d01480d0481d869211100001d982c1083c5074460000a840c20251104101101c005144111017014500c610074100c000e2070002d2000c4162a070764003035004112503400140c4d034410341031074102800300582443c0150360381078103e81c42c540066074079030300c81c502c110466250103920500284 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557030638 1250 557029388 557029399
    0x1e03070903110103150b090a0b03041106090f040f1508120702060a0e06130317040b0d0509030d0e16151e02010b060f07030e0402130b0c161e05 63
    0x25044000816210660000030305846070203441003807a0303219070000c031200121103281c0000c1c4c941e0303100c80d021954803070943c2d5030140310006d030000703400c1400e101030364406c039001803140c00b46071450010000b03140d000d041d0244e070144618204064076100c51040c01d0320b035000d5080004140001070030851560203103030711500140d803001000141d44440601070364107603030b41234588039251250700d5025194802520019030b0800408070340101550030b052807d100700c0c1e02400120b400c441103001c58103102c0c0b0660140300740d140c100f042400303d11000d641c461584020328600b80ca080045400f90b1205840c120009081154010fa0790001d007180e4081450005156519540c0b04801c0c48070f1000d003000c201501000088000805042c10088c001e401c0211501c0c40242116501c45800a181025030001c42059001651800800e5490305041c4200d41c882446800c0c40300135035181c0000780f00254040d80480c4000c1c000c244400801c00c2e882602d107006801c20055600503840d049449014000c41e0703900c040c2c0b095 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557031888 1250 557030638 557030641
    0x20a03031b020d031d010c02060406060905060105090f0a0b1605060a1a06071a07201204050d06060906030b0910090c03020906031906020306010f0207030213050403110d051e03 77
    0x150009000c8200840c02e003404030780c0b00ea031500161179425600520388403650a120408a149a02194440c419441550100729090305c070005442143c0c81155410b011400420046245150144c01c1e02600940104003d102544402200f81c054116206489040c2c00b0000c01c2c0c000c1060038481164880301d1481c0404c40c0221005501144801c580011030241c0e4000940340d00307020004080c000c03120550407009416040c4010010100c42042480040c801021122290b48842c0403414820b070211a01883d81820305100030040c005076440012a1482d9407104e000841c1042402a50010f40c01340852407002c1c6050071005040084030750b040041c9601e4088000001040c0401c03000540740c050303e0192495841034042480d201d120040308404c0c020101d1184100003543d00194841d62080c0d84140e030562120100380d0740c803005400000d40c8001a080e40d00f0a4000030780c480c5900074002c1ca07000d88003200c4508400e06000c580e0906d180000c400085101c14140e66081114a2014091449265 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557033138 1250 557031888 557031941
    0x70f030b0a0314151e060d0c031b0513060501030c080103170d060522111222020a030b0a050f060d12050903070f030b0601020607023703020a0303 64
    0x80510900000f40075034895801c100a8003810407071110b06103004841100c540c14034214645440f900303c60300a148414010018045003001940a10b00a90102c032440c802070030765403500384a000061440c039048c40804e20004d50b40d543c0c0c0804c3d5003c00d0b9a28000501103081000040a6031000c8030700d0b07030505c00218010400504404049003402070320320741e056103030010140d03004003408207940440c6d402480003048040f07450444048117010340d0010010085a0242c1161900034094090160341c0744003070200044201164800041098199410401c07907110345078000786240310542c0003501c0c40100741040081a24052041c550400301400840f426454400000351120444072002000c4003101d4091100c003134014000e8404c0a000101511110b90302c98482190341103283c4800c2e244640504041042c1754004110715005080c90741c0070300340d1006070754003200040d40b065080110200c5e11500c032265544060140742400b034804c1e805042c3c90350141c100201600d40e91115050f004101601d070500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557034388 1250 557033138 557033149
    0x30d0e060304120527030d0305160503041112030d050c3402040f0221040f0f15050f090c041a19090903020a0b09011a0f060c100203070f030b 62
    0x9219612900c503650f043d0f80c80c4030489581c0501321910309600c10920508000055660800c040f4540580c100c07040010364410460070f45905403259804064071040c4040200d01c02c0340210b0740580500d89842c021a0706a0124000c4006146034402e242c101240100041900e4003400d604030a00b01845414209841081140008031086090700000b00c11480da01030781c1e07490b2000a40c1ca800174810000d0100031110304019500800e0540c103590510030404000041070015503004903003120003000c01d1101f039524001c1c0451302c01800c1d03134403040c0018034004071010390082d1407281e000a41c01070042c1c2003260442e4542240e00107a503100d1801d012048241e0200b45d62101980c0c24202c0f41802c3d14800355041e03c038242110780003007031010b0810140c03009168002441400310380c0700700004105607543d40080c608030340c854002828000c3d5546441c000500e03000000c9501e00c0c00003400ca0703250022203010706152590344108412210f801100b001081a00301e0001214070704142010700808025074001790 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557035638 1250 557034388 557034391
    0x207050f010605062b0c02030c07050105130506280903022719020c010e010c02070b040f050105030705090907030903111f0e030f03091b040207080316030f06030b010302030d0e0603 79
    0x14011720307000c0d09400318405032000010480d400754100301580506200a440340e12070448802103114000000551b5407080f01201d401042c0418201c880500b400b08212243d8410200b070f20030740b05010503071194040d0420301d01c4500200c0c5c0d10780c054454030b10301c10311028131540400309136882200d0b81d170740d0701c90750306950000d031f128410416107181511700040c2d540003406001c1600310250328140103921080703015405055081c10741e800700d80c40e003541d0305040c98280c800c4d402544a0705059410400240d40248043d503005506070400c5401c0800d240041b030a05130003290b610000030740351013155041c190862594044100908044d05c52032016900100e9100c55246089140c1e650720740d9a050300100c20310540c0c91520343c09410300e0b924141181101d0340c6505925150f060801e1207400d0102d5442c091003103444207a2301040c101d003140e8074000f018213507884a0040700c0504d6280d0310340c460300040d00e11490024520481e00c030400c40d4110b0052500d001968480c410900c940c0d103000803400d507100400e1300e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557036888 1250 557035638 557035657
    0x2040606030b09070309020120061801060602100b03010b180a0e011a09130b180607180303120603141b03010c140304030c0c0905011d0606090d050f07090207050f01060506 75
    0x100c2d0b0031050f1f10040303411000141d84145030280c0c4003207000040303402203283c034011809003400d03003500c250f02600301c1d003210501d103e16409030b030045109281c40c0025410190361880c004000098400030b500104e1031000d0700109a055403407000b400c1062441282c42010207420761030000704100b004015081180c010741d07200b0700d841600356030005544003800c140b88445030b507440640d0307a0b0241884900d8500c2640782c00c811380309600664000070074641c41442108142c000c0c1c5000804100c1c603580b02641d0504040603441001c40c0ca4000c04404100d00a00c2010030011010040070400e00455448c0d050744214480300f2703c00c5c1d0407c4100c7c034a82d03a02100512107403c910000d943e0b0390705c991805681402d00c1801c0180b840080d4600003030304000540c803050488080345c41c0460000001040452150000ca426507840fa01c00e004441d91030801c500302c0390041d032050045420030495916050304d00400d070ba10010085800040840c1004001e010081c04401600c00038069642031200081444c010f43d01032 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557038138 1250 557036888 557036891
    0x3080105120a08070b010303020d210b040b2116032018100e010603051b0d1107080a0e0901030f0f02060d0c200309060d020708070b0f010302040606030b090703 70
    0x141e111450610180c4506039000041d680e60744404e2404481070b010922080c0c0c0540941200000c4160242c401889400d2005500c4001c1d101c029038044001e058034a141d03a00103907612904002a150380d0b08800440501411511080d090a040c49161215841003028112140c010810008095100d501a001c0d0380340c01454880c01d03030b10041202c10f0b546d01c00030396029003c98244020604d0440c818400e950884658460a82c0caa5400fa001e075882640c0b601d1600c41039041d040983d840900c043e00c000c1043c2400800c05030000d0000c07080b1030700030b9001611b18513000110400d02940080300682020310035a44421558915122421141c1112034050183e1142c28941c0046540740d20491704034802d114420032520301d0484000340780c882c11820051141c12000b40803090158004143c4026410082001d0f1401400c10890406504140d80c22629244140155000034030300b0846035125041c500031007903140d0702d14010030040c0c401c59400b03002850300c0d100e08040709840f44428258026180d090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557039388 1250 557038138 557038159
    0x100e03040905041e0809040b0f1c03021e0709150e0a02030a0908042606161b1406100b12150310060b07111504030f081201060509091303080105 63
    0x14400c584031134011400884820841c03403402008a0781e006445510300640317003004800303190740500c591403d4200616920880c0b040c081da1140300c00703840c044a01c620038411795003554200c1c90745180c40c00e2901201006500108000d000410180c49511a200b6501309202e01c00c40c501f01090241d1035001d0040c481458001000508440c2d503904040344080c1d00203071640c0c1c6d0b555200c43e02c1e498082e0200c20020440c9800540042d041c100290a40c0250301d28020144443e00c2c0320340607500e4080854852100a210700d041102081d81c00220b2410305c0c41c0c0034090600c070f140549481400860036005080704c0b080603c44000d0440c4013651003540007a440b50300035120392010001a01c1c1494940640071141d08040f000b1405841a40c00761202d68460350301c1c4d0008404e81000c00003c80c00c441808500c00100f404100b0110b2240c4407a00390040c00b0b00031491404c940d004002c801102c098000c4000305034002491040743c1804018560320054840c1c10b01117058040c0d40c010071144041c4111845440d1010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557040638 1250 557039388 557039393
    0xa23043c090c0b09040510142101060305150108010504050c01050d0b041e0f09051b06070b04050703440904020d0f0e030f071b0b0a0c05100e0304090504 67
    0x600505041d0381014841c0c040c40da840b20f842e03201e42d0141e008180500e0411011652040c80c0b28900740544180d031114500e6015601c0c01c4c452032000c00700c080d06009403c40c0240c5c024201c20701c2200e001c0c5020300301401007c40b56007803440702c100040c4e10004da582e142c00108404500b010450000d4a2424600785a030303504000881d201610700105c0041e8428a81005401c68010082039080702840303190081c0091801490f080c0c04494800d02d01a040e40c00c81c4a030840ca0150041c1841000200100164204591600e43d098290350446085a032640480b90034000d016200c08031107030712200260303c5400d0308906019030345102e2100caa0401d2080301408400008620300040d81c170810f401420131522182c8060f0b404000d4a09414a0a00c007442d160602603001c0003c42156450900352060a20b441003070340d160b0484140c02d000e00c0d20320b00004100814211482070080111382d26a5844a500d084a03040182c18a0320440051000c1854401a4801082c021080e50116820404000f800d60340d0750 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557041888 1250 557040638 557040641
    0x5030a0c150e1c0201090807080f070507030302071806150c060f0e010f060e1e0a020d02071109010602060702071814090d0e090606030112020a23043c 66
    0x1118034070955041080c100d5410340700051001410306000c0d281c00480200c400141d0803503910b1200070b4120481000421b02081e0300000406c0c420071414806423a2440988842c1d003421b49030b400840040e00555001c1120010007251101110f503102e10820203189030070a0f90720f809071010300385000d001ca805800000d00c00c49a020a43e4242c40460a00014201da40b18030700030031640318203840b034a01c1c0180108105030703075101c15807056024080401c03840020a800c0d81440c04000d00e61040e5607001c120a004a40140c005405841d20070b000b40740c071900d4182c013044501031058001104641c041000c00032980e50000d0715008884810134026010116400305501615011905084441c44d60090000b5988001250107004026a81d400001c2040e00c04200c120541070751446e13408041400144112100c88460210320b80c0300400c2034140e6603031040e050800c81c0780b1280407251400540e0515000e401c160064265401c9002c00d0005c8190b50b9290040032041050b0b0a4001c820a101c41d81c00d0b420440d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557043138 1250 557041888 557041913
    0x71b050f1e032517010c0807110c0a0308090f040e100c11070e1e0f070f020114180c0303030408310b040f06021615090512030c120705030a0c 62
    0x8140000144903e030500c800007000c0c804c120030018940790103105648184210a01a0f6240e42c03002d0483e15060b1040303a0503401c0c0824a07503075016110070074030395580d20713850040154461036440f9102c04520003000756210419404d180210b007000c0c0100708a80002c103113480b000b440ea8000080191440204560100c084907240401348200704010a501c0c40700d60038540301c2c1c4400d1590880340b001900821f41c0341071707050fa075074205210740c440803c19881c02041d0181a12040d84000610310310309030014084484292403610b045002e8110f0340003110418044e401c004002900214a14103003a543c0040f6441602507140245150049240c15244603151901c802109460316404140d11802c90240641c81803003010034250100c540050018004507015107100b145000001400b40b07000d010b00040c2d420380003140308101811102003640d07550301c3c48120743d100d1041700a680b5814100c6101d80f4207a03804013000c0740c00c103061181d00e0000e40c000040f01c680211310720380310160990616164180294 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557044388 1250 557043138 557043163
    0xa080a05090603010e01090b06040602211911100b010e15040e1e0610050a030c0504090e0f1501050603041509020d0305090118050a0303030e12071b050f1e03 69
    0xe0000000650485200105043c0c8a0100c010070203081c811b0708004203442ba52080101503004000320004004c0c0201c0000c01c031a00170b00066180101504001d03100b480c0b1600f0080c046002c1c1c01c4101c92903041049840104103200d402000070109060000c0c2100301030686152017803110390f15104412410005490003070084082019503424003450001c1d1401d00340032410300c02500c420000b080d603c4c0004907528912003584841d8039116622034128043e002407581ca005118080000003046170143c0719080004400c200500640083d103d2442d052141405200e043d1001c2c85005000d9982c6010407640c00c83d501006020387d044081982a025100066019600c03000d0041d444052541000007409981da09076902800c5e1046c0002001044000d801001d82007440b06405000080c02a070041190400340011114450900e1040d91031076400400211240802e11100c2566038082d00e1008001c2c1404850441000300c8001c0030818141c00d003101c4200162005403c4441c0d80c4081c850080e207000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557045638 1250 557044388 557044399
    0x904021b01090818040c0c08130f08070806152b0506010f031a01031101051305060301031a07050c030f092d01021e0c01080403140d27050a080a0509 65
    0x4900303043c000c0a94000d098a202811607510881c15a4030b000d11038080e041e2419203418039a0b2990741c0303d62101d130b04a111560415041c00501007104642c4010440080000c0e03c000c014107810414120f04200c0e02400719510052144180e0002c0d0b51103102041e0840c048003501c0d2011448491403285c4a1801c030b5001c1c1507402104004942c9402e00d5481f10140ca020780e605c1602d20103010210240e0142c02d100240c120808814511810b600c144000c000340d81c40b201100c00c03915280c2001400d168000c1c1d0040762140760380c103010303100501700c680001e502081c9403c2190400c0e02d0000c20740d45a205043ca840000c0c680050b000710b0664401c040010820100b0002e20168140700c0e0410242122079070207103003d482100031030007014501c010b031050920800d41c00b41815101c10070054402c040c1c003030412400e1100c00041c0701c80c001a001c002d41003015443c4404100030342c1c0980390042030001c0440c03d105140c41138080d080420400201c0045032540f0040c580d90b2510000c1003124107000340c040305035011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557046888 1250 557045638 557045651
    0xc030c09150623160209011d18030706110c03210901110d02030402040b0616030f050a20010b03030d060302090109140f04020d020d03030c110105010b0904021b01 71
    0x1038680781c0c0610740c490312507020015007944800701915200959010f500210501040404498840002512503c2294210a540b8010700e0740080c4400c44d0076040ba03840f4001d0b8910025801c1101e904150300990509a9082c030446000c900507224440c1c0d000182080b03440d405204981580a0212201c05218809030307500c1d000041c00e2241c00301e11000401e60010008401702d1150201885103001c2511401c00d0180b81244030b0319000003039040100141ea003d40d5400071040d841d10340800078803400c0700a42881078036007898980038080c0100144d5150820905020001200d5000a80d07003c1290000b01e00d1010000c0c1e88001501410340c410080e600b500000c1782e0700f503490707095400c03060a9174403c40711602e003a0b8855001c40c04039030011048190311880080800d10300420b0100fa9a00b140c00540340c07a25260040c6c02040c058401844100c000903500d80f4040d8000754006601245015040002e02255143c5108a580c501502d4401445aa400038626070785007142c100902e0700b4070042c4000d0007007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557048138 1250 557046888 557046899
    0x9150906060315010501020307150e06010f0816260705100c050f0309030307021309020402070807060b090708070e0303041508010f120803040b040f020d0524060901050d0c030c 77
    0xc40c8001c0d12103502a11031002d8012501c21071030344140c141d602c10b9008500303140b003d4542c1c0c05400d02c0c500040c10b980340c4d80c25107108029003d00201d8081c01c1d07040c030201c0c1c400d071412440358a444c2d0090b14411500f040e00b80c0c180146805540c01206401000001031910102074143c90f0400d03e5a03485668421060709482150701c0d00b203c402d907145405401039403101c030351208115032a84103c034011035042e0010004000149089450504000c0d00d1410010345401c1d035601040490340408c2007a0340c07a1a001ca80e5008120b2356003e04003940c1c0094070004036a082042c0050300312240504180c0500c0904e0a9440701624208240c0d03004112512001540342d041c0301c1e01801040b0300380202c02c00c640a5844c08130711002840200c0d600582d10584543c40c550b29070b15002172002000d0300132124a2000c02115016940d02e1410074030803030290b00034010103d200e0484180e16182500c240d41c007280c0c0841042082d50b503840d03441c1d04481c0305917031140103040d880c42e0031400c031446034200030090804000003041 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557049388 1250 557048138 557048143
    0x41e111002060c03070309031701092a090b0c0c150307080601020a080d051003051e06010f050d022403091507080c030628080102090a0e070504030803091509 69
    0x10204040e034040c0140c0500800490b16280d0880340400403482c20004141414429401941e0341800f0346003495002c1e01c0c01494009104080e484000c80315141d9080502c07608034070303642003030034840c010387d03071030b90808000e806008620680301d02d054101c00880d00c041401c0040c01038035000103004060806400140c1c28400440d0425282d0700e00003809a0005101075000140f5181e2803604022202e09144807044010040c0c0b000400040c0205011034002001074010041c01c41c000032000128006c0c0301c00300310054030b4000147d020b40c5a40343c040c0c204001d03d446072191411540e4050b40c044000c182c1a00c10244444e000181d0300040c1c1200100b0400c02640c0494182d0410340500e0780f0f825640c480d120112101c0c1415680d604242e0000c0000c1444d501c2d04a10008000220b5201c5880d01400698620f0031030710250320070401650001103008542c98201000c002070300c1100545402c3e03041c00100200b98ac0501d000003420180000081800d07000100a503113107064101c03001103860700c4c0c03100e074498 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557050638 1250 557049388 557049413
    0x30108120c060a1505032517100b030c2e02030928170a0506070302030c03160e04110c1006030c1a040f12030314160c06020f0309030a180302010f0305041e 68
    0x3112440c10b8030020176040000c0050340142322610004003280344030115404001c18107940816414450304202300c005450300c0c02000a0300310240150351660071640c0f103210112011030142c0046410030800350440f95240c0c0340d00e010301314031014003581000305c2c0300c034a4464010642100020718101c5440c0b2200178400100e0b00c0c40c1c14402d2007658001d8550100c16003d030b000507500c04020740800d10003d4035042c0c4941400020b40c15030f1900d000300001c00000b04044440c50003000c05c4c602d400095007615240100443c503a29514500208070003413958803010380c20040b50081d1311084a07007078106690806503105503000740c00900e18a00b01075a949100c02501c2007880000c80101e42000e241d1440c4022210f60188143e000c1410f04001741c4c070703070322040325074006420b400c491030f40d424070100c4201e42110000d03600c981074440045503221040c41004c2c148914240c91100d5030700c0001028030060741d020140c11300403031441c100401d550301c4501d82022020780808044a04451295415042c03090b1f402d80403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557051888 1250 557050638 557050693
    0x210180b030a1b0804020105031602011407030b03010b0303031003240212010302010e010302090f04021b01050f100f03051906020c030d150b09030613050a17030108120c060a150503 79
    0x41440c00c3c4511019150102c044030080e0104200b030001919500b81890140e20040d00361000007104035400001c00498002030300d1140000e2b66030b038004c41840c1000d01c211620390504900450441c600545860805c44250000801140c600c5510100f03000800214000c11007900000355103511184605040c142400d100580c00034140800b10602c0e54028404c41b1440c6070040e05040c101141c19007400081c1d40812010410102e02410700c1240c10420703c1a24000c259020f90303036649090604800f80f803103110b900000c82078095490100001400000c041030190954a41c4446124103800c19030000d004503540442c0c503000000e98060040d4050740001403921920030346423900398480c581041240140c031030860305940b002006c20f440a506008040c8018401c0044402150700307580c8128030001c010014842288020006009503036040c40b210000380300465400b0308001240c45501d80d40c03200500008842d5507100b60110300540c1d190f10300b602810004d0100e5115210000315904111584030b83d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557053138 1250 557051888 557051921
    0xf0303050a06090204030206090103051506070605010314061e0717070e04050901180602220602100c02010c0f0e030f0304080a1110020312090106031a060f0d0210180b030a 75
    0x2243d820080d2003a64185c90700640000c0c104000900158000c00380580300c1c206900c00715201c0c480707640d1203000600e8003500c45d44000c03e25501d075143c0b100c9071307103118080c81c070300e03a0010001c22100c0102d000d590040407103940071b41d6502d900ea900d4141c0346404c4120303902c010175201d80d0402001390b401401c02c00c05a982030f80c042000e540e40044041c200c0c0c80c80303002565080e500303040440101c0c2d442c0d0003919003c441500146040d40030020507180042565000c10056000001d25900f003065600c581e070164445400284010701f83d130500148400010400b180074030415402c41400c54404000c03210352001c0800440396038913161485140d03a4002c2074001c481c80344422200034203e0416180d00051045290020740c10b2810401402c41c0b40c50b001001120740b50350b82c00f000408100e500c0602d1103907181880c1e0150040c1030030000e01004d2421713400c0c00e502074403040c0e103058016101c111060030601c1c2c0c0c2d4508030041c100e86212040c101d030710641c480c1c42038520120502001d01c0c910b511551458071540003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557054388 1250 557053138 557053151
    0x50c0d03060e0f25120e0a0b01060305041a040609050a050f0705061e160515040611070f0209070c0605010b0306010215090318120313090605030f0a060c020a0f0303050a 74
    0x3d622a00c44011070310076000701300003c501c41450308400650369024403e8180005810881c1041c80200c400d110f620480b590f1041e0581c1d001c2c468510305150242c040303440e081c040d0f40b138117881e100c0c40c04002c4411341c0139002802000400b4806030764402100c090b4440c0c2521010202401c00c2a550748240752510030b40e02030074200140d01d1a203181241c004241c0c1101114150b400c030041c0c07020031341003002214011810308911030000b5074203004083c01500c0b800420541410309003003060894070b00140d01d822100041103031201107045c14000400c2150b0480350705520f40ea50f8102201e04180b0f130503000740414100800450300a41c51005544101d101303034226810f6040310041c84d65651815107d104050300104680304104011398030a88055038040c050154134841d00311542d1440d484542c000300000c00040c000d100b410014010400105002c0f0020901c03a00444000f42d00d510580400030300180ea108441a14140240300030030031b090308100c020007400d4450a0141c0a05422282500300601d40034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557055638 1250 557054388 557054401
    0x4060504020a020615152101090c1e2309040f02070c1806150305070e03071409100504090b040c0e01030b0c03090c0913020a0506160f03050c0d03060e 66
    0x801d450350844250700130301c0c1c240c4038001300c0b07084580000070b03607a009071100030352140d10300c025401811500c507004240301d40c40440d221100d0000d10180c0000e009103080c8000f0035003d50b440701c000011481c020483c00341448142109a83c095006104a0201190481c411700d810a01001074000c040301900c1c18496012040c0801c2d04a00c01e000d0010101c0000301001e10141080c0300c0d4403040301c08604400904c4d281c8810103440d0b94051140302d0b40000f5280c50070811910752190f444003141c14117030020403d86060a042501048590038001c2c000e0388041c000070900c0c40e060100c50700519003e00300f00040c08241c00d04000d214411901034825110510300011580e08032446a41240d812040c14800c64845050000382ea80c00a80480511710407a04200346c0c550300c0c5140e060040250031860a0b100d030b460b1040c407000400f20751045101341001c0c00582d4420000860701c050459000c07030f141414011a15007501d850181d5000300708184a0171051540d00384d0154000c100343c9111030110100b554400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557056888 1250 557055638 557055641
    0x6050d0b0607020a1712131d190b0604180203040b012111010203070515090d0914060c16181a0f120f0f030a080702071a180d0c0504060504 61
    0xb00c00094021221007020090448100c418643d035124000a0310040c409001240050f03404c10348208034000d80d0504108a0152440091400d2003001d10301401c0d40c0c81d00303140082c0c140800e0307000c0c1e209658442e40c4010710b0390b84271000c44001c0e200707004020307104203000b580100c020f401c221002c82d03100342d40000109000301044220511207558030380315a01a00d059603043c80300880d04080e541540700c1404142c00060090242044000d0400101c1a032840c03d000514600450b901445060003694a014040e140800541904215027950600c0d520703040b00c0c040c903103444074031284155012840600411b1036201924200b040851403282402031801380c46d280a2a800681c18856000900c101d444020341006046025000c0e0701c00d040c0e030b1402c03260001c2c0b24185000a40c0307800362034200055800e181500840d08a030008071f036200520350a400e180310801d0014040c01c0410b4007080100300410100740038484010a0540980540e005414610300040301d203800e0302440e0b108034145003010440341842d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557058138 1250 557056888 557056897
    0x708010f0e0a111c05092401121a131511031302030705060a022d0d050d1506030b0102010b10120f090b07081b07150509010b030706050d0b06 62
    0x10315400d45940381ca004010041500300d000c1000d049041c005041c088802000c8070240c10502800842c886c90040702032401c080c3d070034214909503449401401030000740401481d041d101800c100b0a06400309080a40f140a20403440840c031444803007c116504c00c0c0728050314801d9100d11540d02c0e080c604045140162220b856010048903000c0c4002040c0e1402c00c002c0f8142c090014080c2c50740280c440b00490f0706c690218902c0f20259004d0044016280b84408501d42001c660310940c01c0d1840040d000c0540340d2a5030141c1d04100000400d4142241d2201d600940c03820880240f88071040380ea54901a001d8a0702d842101d01652134598681042c1c02c220401401404855071510b0300005c100100070018000c0c0c03140c020b41555078081c82d8001400c2c1c0c100301030040c1580e440e030440d40e107025102020701d01c0403450800e40201c000e0201d60001644450021603c04034860301103540c2c1e481c40101030041058100180d070605c40c02c0e500059a90b0020020290950b8514050003900a070b00c0034821644074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557059388 1250 557058138 557058149
    0x150305090a050a03260c0d02070f05010e0a020a0b0702010e06030406020d140601020f010605030601062111070512120a240303050c07090b0f04020c120c031222060b0109031401050708010f 82
    0x808000305501c0d1f1143e9401031800c903210340380002444400d500d4030b60841c2d09041c4143c0007940801100700640c075180f0905e4008002840026160458903400201080280d48850b801004084081400c000c5190181c8401c0c401444003004040700b8082d20036070099054038014054000d03483c0b0461014010b000d00c100342d41d0082d00424180e4070304041196240042841020001d1000907600e4100b180c50040203c2480320f0143c0e592140c02c5414070509004002004414075007080140703d0003440281072071580700c40c084c01c001071103960400c150b04001003208c852099520068801108054114002c0d0884840b4481240c40e400e864040c40400c0760480c00505a0082503040810010310300754008240e0128100241c0e81c800c81c10844160386504440107801c0c2c0c503000803e503c1c12612601c4c1c2126071040034058406170100c035034181c185201003a0040a0036840c5c9079414250580d004403115002154020100900000001c0f2050300030703c0255a031000040141c0300020360403055180000680c0c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557060638 1250 557059388 557059411
    0x90b09090d050a18090209030f0a0302070b09060f0313110d020109091a030d0e100804081905090d050f01110c030409020d0f06060f09050a150305090a050a0326 70
    0x1d021016200ba410034901c40d010048030381c60700025038007070b038195100a00f070444001d41c440f01d81c00205801c0942851054607030b0b03404141b081010990006855003103402921035141d030b5041440104d1124400d000c00180c8552000040c041e1885101a54120f4039000d01081c0c008a18440d040021544101740084e002401c255400d02c05540d5580c01240c0d8a4900d403a04801d139200400424100032003401c8800125154800070f0b15141084102d403801003031285001c0e4003600e80750384c56108c240552800300702144d20110b160f0345468002ca003250008000100180312525151420590341c90082070710704d80a50070162824031408103001a80c42d13816031100610709003410064118002e4001c7ea0000f104076448080080103160310780f2401014048903a0f441000380c0d4104001391100d00b4590000380150750b115000c001c0080103d050380345800841ca000310381510b60f5012280f424000303001c0508140076080c4c400041541101824010700c1041c1c0c00e5200e14004515007544041d0100c500030b000700e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557061888 1250 557060638 557060653
    0x4030e120c060313020a030b0403120c05071214160515010b030f040c05090a090615081b040b0a0906031205030603070303140c07060e01020106080c06040509070c0813090b0909 77
    0x245004000f0f1603000f0380c0c88080c1030450141d030f000503a002d079040d070060b80d242801905010600d07900420141100c0200d000510500d10050001005440785c100042c00c9418055000203031544154840c9040c1d0900c0b012294407103806001c0303404154440300e001c851601c5501c01109031407200c0c2e14141d0490700071074283d60450781d070300a12018941d00140215042c403003116000c217890b5103404605001301d5880c20000352107091440c1c03450071a25101075009000c02e10480411034000000cc00309104401c09006034400c28006010901821020102641c8160840d0020075001c0407036100340216800b0301b100ca034032000440320a036210f200584e4070513003540041c8410710200e401404c1a02c2e1303040c40c1d00c61080c5003201002d166801d010040e0800c00c0007480400840c02c243d81e0900800000c1d00701d50b4054071202c44801d0014040307120301d200da1801284140c0010f25054014030400704082c0d041200b296940107407000003101142d080c014003030303010301c2c00401c203005041072070340640324440600091290 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557063138 1250 557061888 557061913
    0x1903050312060303070f050c091e07030c050906070f0209010e0408180a051201050105030f030c0a120e0303040e040209151e120706090807080a030f0302030a09081204030e12 76
    0x3078001011942c05102c100880300005020b01e100c001881c0c000c20142200c107a8180c1000146003002d07159071820840d0015030440395110091040e0030060609002820602088040c0e64038024046c055501540c0861950188a4403581c8690490710854505a49a80710460a440c2c4481990080d0250740140f080c9070140821a4080c000c100c4024050515240d40d10005001c041c0c40c45080803603a5110401001142420000c1d03040c1c60551001540c02e09000011542d9685082040906071160700003c2d100c1c0710f4080c11540c140c242003d0162540c440d11000d01d0045c0e00010f4804034080c1b2588000142188030700382c891040303003400610795020040340b5004a130440b0718078800540e112041e02c031001015482004031100130021916404020788c0f40000702400c141c0e842e40b1108480c2c018081d007400103603001090090825403410010307143d856601c00c0c68014440180024400301c1c0c00a064162015000080d500c035902c40c0d9684056541110244031140811404115041e400220114071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557064388 1250 557063138 557063167
    0xe01020f0406110a0804060309060b041e230f0f0601020c1f021002041e0b09010807110703061505031614041d010f050718050109030803040f0b0f010519030503 70
    0x40100140c0102c4d00003d10396156146a944542d00071400b0954400251003040200e00034a89024400c80701003111943d070079400088024402c900300c0e03015035a40d10722401105941026040f142a01c0c8650350356142c00e8100d0040038034152a24080c1d8540300c00082d01c250f01c001440140c445c4050425110300c0524401081c5554034040030344107500482c0d0920060700c0c55440507000416004140c1e40c28400f00c4503104000700312682000c0a102e070100202030441e60040348042d0040c80915180f960143c64450a60600d985074100500c581c0c00c103c29039061600302203080b001e0780c000320151100440c01e061300400900d0a4032030510030503c018516003039441c0076441080301c00d0b011014030100c2c4406900d41c07821180c8011100d428190350b0350a211140350710950442054007552194115241081c00180c200001884000c28014001002400700410400500f0005502c8048482603080c41421a58600c0c424041c150044040703d9038800781090144080080720b4002c40503601d000d1000d901441d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557065638 1250 557064388 557064407
    0xa0914060705040b0304050102091e010e0102010614211902010e0d020a0611010b221d0304050d0f150501030302060a06030c0b03101518630e01020f0406 67
    0x7d413655030a1001405d2070300d6804a2400b2001211046451030300c0c0c400000d00254282c0c410181160302d4a902400520201d09421820300c40407039601502000c4e045400400300740300850100d4501400600c048030717800014030000454800d0325800c4090840e0300500c0004003260750301030740c40308081804019060080000c0001c0d046c10f140003080081503c00450410054202554110400100000e42c0e0151610540e400981000380a03641068030007049036685c0541d00500d44a4200080810b0400004034801c00740158401118034600d07085032500b07030040030b003480241e0241c000d80700014102e20700c81c410030040e650700c0441e030302d0803178103000c08818240c10041100c001503c040b1408100710381104a0000412156910f01e800464003270840d144030002c0341e2046103041d22a560780003204841c0001020104054000c0241c401c41c100c4601c4402444070030911400a01e6849011070f903118401c0511182e40b018030306012a400550400c0d00702c1c0300e00c0c2d00d24800484c0a0000744a41071003000001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557066888 1250 557065638 557065643
    0x7030f08060307121401050c042301090e0c0903060603060c0a2724030c0504060503070c02060d02091e0a1e09060e0711070506030105061308060a0914060705040b0304 73
    0x90f04070703503100c4803441e248804051064a5881010851a00ba41000d0160315448030911983c0b40c00e20745842140030340c00e98564030041112500c2c0b8907000c07407a4840e140c3d240080414002c40426070074401c2649580c0ea119a900da8003e01480b4000785040c240015443e00905201002e1703841c048500a007282d02c0e100c1d031014480424000d01100412840c843c1c1ea03100038040250042450080c5900080c1e441e600d10080d403018181008109949107800c602030301c08a80701410410f944c2da0740d81104603610400c4c004001d502c814049031070206580302d94003800680005072101250072400d000c49100d401c40c1080800c0e40041508420310907030b281100d9241688000c3c51a81d503045403602000802d4600d190807c0051001050402200d2944100c8446220442c2000ba000e40c0e414100811000d02c0140502030248a00041030b84021b0145254207005250420907610181018044c4401403c1f2001050710320a01140c0c1c05160f07c500811058041e13160798031403d00d80f6140c0300340c18400740c1005109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557068138 1250 557066888 557066893
    0x6061804090f05010507110a02030604060f0e120c0d0801120326010e060a1d0609060d0b090a03080f010b030f04020a080a03020703020306010b0a02070902070c083007030f080603 78
    0x10807002800e0035a4041456100300004039441c0b80010000b042e556a03181251115840b0403118009a200403a1403500550802c801003aa48818210728024010700e00910000d4410074000180140c015000f07014240d11050640d880c80031180d0b800c540a200a01130000200c55031250000001d0003085d49050b00d100403201c2d00c0c600c1c642c3c03050b00c0d40251000da12124030041c44d0070421aa500c0c1000e8010003504600003565450f45405448100481000b0200c60003076418502181c216078450120903a20f80d03000c512850645000d0041c42c3e254020301c40201c0204a45001007065591440e071031a06031014200107505550750030303541c403030b0f81c0f03802900990300182e10310008604001c05010560541740030b6002024964550310605152000592082808900a100c030303070110356021481d0b4044407000003015840304107900300301501e42480c5e80019090707c03d091810120000b4481d8031381c140d20a003080c0700b60b40308074800c501c1d05901c07604100800083c1c0d003d45128030746019064140d00048040d08 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557069388 1250 557068138 557068151
    0x91e0c05091302060c070f06080f0f04081608091207270b090f0613020c072d180f0501120f06090602180f1c08071401020f0415020606061804 62
    0x1250071341d40110080740382c4e0341160000b4040540424103600040c05986040d600600d05200300002c80d61000e001c80d508440c0300030101c1d00b4005880255100040540c0d000032b4842d81c5440c0c06140740e8000c41215002d5100c0c80072070b0750050380205410303044504846049070000188010705038040060780022001e1a030b15010100940c0b01d1030701840c89600c03c1c0c002803100c1d080003000c20021044110300c10445a00412440f00700b0b42001c500041120402940c0c086841d01c052100c4070034901426040307038007841c83d00d40020355101c83c0142242c6101c01c42c2342001070010301001f20045d41c500740586d03145981d14400001c006490281401e03400c6001d0400040c0e043d1055031010240e0703020483d92288080d40000f2041c0c0e5240000010340c03d66400c6408922540d03070041e41c83c84403032110102519014003c2052000e00c07090014281d6040c0050000b19a24000f81d01c41c040e007038006000e40c5803622010f5262a40076800010034502907903000380114281725080d454884805003807000c1a40164a940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557070638 1250 557069388 557069393
    0xe0f090a050d0305070206100302031e030d0203040b0610020312010b161a060a090b030606040506060c0114042003060c0a030b041e0c0801150507031103030406091e0c050913 76
    0x8401d802d00c8407a540401d5038140154006d160503006084c02d0480c030000007003000166000985008903144a0405060104240d40c03501d080d4001c041c00107aa00b800041040b007003150304c4030030a100d00740442d0030090704400f614040303030340303000e046401c0754070300507180041c401940310a020b05018080403281503110703002c07507540b076200c0c4504c1c40551440f0b50301281070018500e1300440c2000580070003181005070170400000a40c0d00d000183c40180520303910b801051154031040100c1e440406000024000d00196100f06900c10400303d5081c1c43c0041c158109148883c1c55590106003118000c000344416240c40018107110313440b40d910769082c90398032882d0301d1060701e4602620080e1031038100c809611603111101d080658280e060408100002540180400007009106c42c2c405409842c1c42a200c081d10b01d800d41d080340072600041c0e0544400f10801c41001825005140d280d88030707200e19440b0700ca499400011040c80c0040081c1801d190340c40038009414a402003d0303000913180c3d090580d10034140c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557071888 1250 557070638 557070643
    0x30304030c0f050a14010b0f0109030f03030209030a050d0f030e0606011101230a0b0d020102100207020a0e150a0f0807030b0c0d020406020304061103040f03060e0106180b0306100e0f090a05 83
    0x4500c200c1c0c2c959a208040c8017070072020310500403401000e849650a0b040c14400090140c03505000007044400c5502a62040c54402d90544030582000f40031600b2a02542c18040d035606540101c100025001e5181000081c1c80380c0106405905400000d2045859103c0190750180f007030140e01c1e02940d40c5240c10344207154148941400e5100840250240342010320681d0f098440136860306002d4205204c9400046c1d0740001e60300c025410103940181c0710705141c4000380700401c00e0b6200c028070403e85814001c0c01d00400701441001d150803540c4000c0c3c00e586441e03c8001c41c0052141c10402d8101041c1000450051000e01d54004444802c59241c0944d2881e54022a00260400030050b40041000d00480b0b8210207a5089685005c000314100381c03615074084280301241c00b00400140d104ea05841c4040300940103100540281e001184401c80940301030401425000d420901c01e208103004600054102200303401681c06403903111190f603481720500390a030040503250f40070904c9110301203030114400303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557073138 1250 557071888 557071903
    0x903020d0b06010e0a120312020c2802060d0209012003040b1b19121e120f060b0915030906040f140303240402031315021b100e030c030304030c0f05 65
    0x10b00d040a51811b1036403c00600d040d020100c035003c00d600c1000ba440a08200040701c10450b0032000c6044d081d8248954000608081d501c4029007145001c58808214151900940b002c1102030780c07030744400482000c81c2e0041c124030203000e54054000f000184009401e4600400e80c0601544c0002d00d101c4a0f04072151402e0907a1480c014210242c3c2e0b56002008980090400020300303d25000b001030a22444410760200070348180380034004010301c021300340c1c10150410702c9030013080c01c401c00896580700c0e0b820075194806500346d44900c810807800c250000e0b001080ea40156121402001c107540d680e6240811860064410385819400c0d150040401030100000c51207001295248840004030072445041030b4540c4d65401d101e58010310800264054045208d5501a0010749005407001d82080b040d00a102d00e020404200d0400c4c0b24203d1010000201c051003110480400c200401654012a403240620340484a094008002140100b80301380d540a004070b0142d80160000100d40d514580f030b00e801d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557074388 1250 557073138 557073149
    0x80c1312060e1e0705010e0d05010f1e0903050f0f0f0f090103051e06010f0504120501090506060306071b03020c280b130b030c0d060807090c0903020d0b06010e0a 71
    0x310b800394203404036814040c80300e0a021140f2821002c0110348070031a2650b83c9400390b54104a0902e040f5800707035032203041942c08660008020444030a9010014001d018880c0c0c0e21506140c1005803810201d042d8892020480c0d003580d2080e04000b050031a5000c00d0f403212611007540c1d8410301041c0c03103800d00c1d60010300d54641c2c0b142ca07069542d140003001400340c0c1c20040a6807100301d03400c401800712204017401254041d00c01d280111203070054520075103550003141c1090700d0510200b1004410014150b011001ca00e014500b2603034243e441c2001c2555900d8201c42600c000f411190034000c410080581c035100345446801580c806d16286400314800d4940038520b031000e110200b5400300c605a52012010140644215640c9811098407031101103440d28030030800c1d80100000041d6261074000159405c3d00d00404080c0101c9554a0729183d58601d1401018000e42c50145080052030040d10108c0459a0240c10010702001a4135031246a41c0b000b490306050040b0b90b000080980d883e844004040d28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557075638 1250 557074388 557074391
    0x102030708010f050a0b19020106150905130c1b0c080a150b0f010203030c0a02120703090e01060206040c06030c2106091d0604140316050c0f060703080c131206 70
    0x6141030030003e0000204d6003d0342c01100c803c1d4052248208140441d4400c44114052814203591198201c1c010101a404441403213072441e80e40c0b03070540e40400000f04a070802c50301010810b001200110440d82100c1e05040454ec091080d5031040a48800b00090540108840707110b8556500c81542042a480412521441c0a84c044000b1034010300c03076465455020744140000020b5180081e41c0c9101c042d00f00020000080f964690551082101900201c0a6a03400391201140c0c64060320141c000d01440420f038005e00c0002c00e04d46d200188441c8110b410091542c1900e1500c036007900100140d40c00041001404400e0840c0e40e06401c0c1c2d444540558034400180f11840c0560704000c50b011500500034031545600c9481140a00044154101c0e0b00180c0308030340340c9900d004492552155182280e1034004c0004000184800410314103c040e505a82c1500b60140a40c100955840351540007004104110089904000b2140260102c0c00100050469142d180c48543d452404141021103445 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557076888 1250 557075638 557075641
    0x40e0c09100e0a1e08011103041211300307020a02010908010603111c020306130606060c03020a150204230f15041a090907020f150106020d030509010e0102030708 71
    0x90600d400840a6041c103464015040b80c90400098080d010f18482e2500c94424202c0c950444aa4100032000410301c1d140200720980402050f86940d410450b019140c03190030b4944404528040d04800c075002e03400c0000790148a210554004204101440084404240c1c002e8000d5890340c000c011801791210703400400c2c21183c80d01c001807040c0340329001550240d05003002000096180001020b201404a50414049400e4000401010320024010b90315215482c1405001c00b40c100c00403100300d025801c140995500ca14003980e8050f0442c03401801640100002e101080c0041d000348090217001c207016240640c0d80c010080c0d0f001c070903001060039a02c03894400501d46010140801201c42c1030342d56091482503240c1c07819035401140714400785800700c0b0300a0031806961078116100800d00400c1c0e41c00c18203103164025556040c040d01140c0a115002c003d441d000071101c0218121005507004003041010f0b503004401600000d0091000ba40d21106c202c44101401e00140d88a103100d9070f01d96155 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557078138 1250 557076888 557076907
    0x3021e03060306090309010f0311070501021308010e0304060f111f0c1d0d0f1502070f11011d12070801020a02011b03060302031506011701030501062c0103020d08040e0c 74
    0x7004400f800c8858185d02c10042c02e0b04070707604459003c001d031115080010350000c2d82501003100b4414194010000e5200282c034030a40c0290750800350a4400420007001b203050329807441741d13a82c4680d000b84400f02e1880580b070203005114140c290042649041900c010301c06c2904500042501c0f1100e24100c40e0701d8070209600140e110382c641524100494544039103040f07010116261000242c40030304105480c048000c107000b02c500d1075454808030000c0031556580c036402e107944c03429a035640841d001c0c5031498405030150b10606c082d004400f46420a5252020a01c00704a1a04070001001815004410002484d00820310141c600d070442c54001140080040241d240c5004095083c50181491b00109002580303000890390070308140da000032240c50700d031140161680300300c0c800c2303e80b010a900d10010007044010340045044a090f050390ba482d408040001011221920080445c1441003100420140c03402000d6010303800d0084115038a42520b0b1074001d1500e1001b1164421284030000c0d09184 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557079388 1250 557078138 557078143
    0x10203090d03050103020a0e0702120a02030a0905010c020a0b09010e130b120d020a06180210031401412106061002030d0e0c100c17071e0303021e030603 67
    0x310105240307010441c0390705580c00100c3c3d04a150048020480142000030a03090081090307408205402f54a55101c80d624100259a9401085e0510014014140001c1c55501400083c5e18582d40100b10175850fa041c0b020241d0950049044641040480010b0809607140c80d05481c444106560000c80c0c154210018064001c1500c1d46181d0298440452070b960190702089a0001942c090f2002c29040748030301103603181d8940c0000c06507001e0071120f044100b26030103034061154481d080344010320a07a80c07404120300c11179486010f941c98500c498051400047c008106007400351510040f00000c8a5401c0481c07808110140c410403001d549601e031641281080040941c000b2049520840041c080f25000392240a00a24a02d0954481c5842d040e0702e9018005450841c2c2c6c080c0c81102d04840001c0018190301c2060780c15500d40740270a400700c00c0f21080788210340045401030800c20040213078403240301d0717141f08510041e0100740d030a2198252100d2900c80030b646d14041c0640141e00d90130440201030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557080638 1250 557079388 557079403
    0x60405060a0b0304080304050111040b0c0609120a111501081b09070c02040c09171f0c0203162a08061003121809020c07060908010e0303280e01020309 66
    0x80c0700e031603424420864080000102c80c0d2003540803041c9922910b4034905507001d84880c003000c800c100c0011501003200f00720100580306945640c8126821074407a01d241540319042c9038070720001403c0c108558405140900030300404840c6480880d603800308441045443c200003a000840c198110124004503954032400e140c0102d5811150103006080441d070103000000c0880c1c0080c0200d1f02c070071551030744c0c41c0200c00d903000415000c042c40320070700b0007107907071030f81301d00204403207440a140a281c1c0381c0c070408462040c800c026006400441c5040c103500800948c1120740441200d40111210007000c580d19010302e060f107140318240c40030440341c3c240301106003843e0300200003042400d81e0302001c101140c4800400040c02c0c0c40740c148007c08950480c3d0800580f1020b400c2940d140c1d0001810311204100066800e0440e42143c0e59019025190f04100d400e85910890640040e032003840031401c031000110316003550b404000c0c0914096030100764801d0070342e58002d0707810010b81d5002c410444031010620480d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557081888 1250 557080638 557080651
    0x2150105060d1508120c0d1d220903120e06100603050c0415020105040c05010804050a020f0f3015061c1202010501210206030c0a0203130f061715010e190b03060405 72
    0x40f00201c402341c04a481c02c41d2504030503403280c5140c21180c00112075070080f40400d070340c1d601003e2140340300c24103000e07040e5420703200c2203002c151502441110201000c1840c03030282031640500c900151034184114050003000d0160324102404000004503d001c40c594921030f440c5a8001050341e2615007801d00e10080164485030500580c00100b100045000c5031012802e503045039280c03410865200490080610004a02e820a5041500c40c0a0040401441004091034140502c03000c183c0003809481d10a0071001070038102c040e0b0003103003480c0b07405c84840c901d10741760912a101c0140d20307488120b90b0320618001d40380503075900c0f4010300030300d929182150000420100100c40700c1c0c100c1d5012948a01c4001d09040e001c070000328241407054824800c41d198900a0f9003108401510f550407910066401e01c1039801140e00945900720031081c1e02c4001340306021030b400c110040541840152911440e030808103034400442000c07400110b00c40f006050103090030f04d50454980c035000c0305000407a80050b045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557083138 1250 557081888 557081897
    0x5120a060f121211031624021201140904030c0201020309150c070504060b0a051621030b04050601080103030c141911090c030c07060e03030f040302150105060d1508120c0d 75
    0xb000804000106d0343d0b41001c009810440790710f5400c0140d0100080c682030315415203c8074022034054010b07000350003001804101380b8006d036a2941c00c0035203a4801a001c0703800540d0307000003401107401b1f170310307804285030060050382d203441003800c00910f54511080041905940c003140045680004101e03a801a140940c3c3c100011402c0800303402450040d581000100500082e003001c103c8221841d12600c01d90061351005c0d0300c950400035030303000c40381c9065581c00603182c122030031140d191900402c8c0c010b4030b06844500b07050f42103440440e00020b0034141078442d0343e0101071000b1903440811a45000d458240c95442c034001c000d01c0c100e88003808d000e542c0781c8207200110511070b40c80210812a50866601c1c05181e6840c0d04525042d805821240c90b0f0b40345a000200802071200092590035100300d210354280c400c07003030301c0551802c0e107010300f030050a801440031311030307840c00c00c050358854000c50000201810500750744405903440d0004401e9802c500704008a034014020030208002d91444c02d007400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557084388 1250 557083138 557083157
    0x13030e0108010f1505070210050418050103200d050d020f0f120a0507030c0503030118050610020601090203070e0d260c062818051c05120a060f1212 65
    0xb01691081d4a60280b6a804803544000c50000c50080782110080c031f5001d40344540683e03102401a0454000d4400c00b2684558002c4030f4145035194458103040c3e0340e10070540c868060507039a40e282c542d03600c01c102607003040c15041d18201180382003010454800b440d47c000c28aa0b40e4102d000b40c20308409000c1054540d103d000054010642c03c0203031280351901c0d00d002502c85010742070484203c4400840a40716010000000c5010440091007a02c1c0302c003c01d806000689988043c40070305030701400035200582110006000c1d0041c41d80003107801100501d441218080c118002a503d50120242121310070f281c0c003c02080100b4140c0310440036051a01042e00781070540c4c003810740b40c05008105441303206942c401c202c1040708034100c510817540030001c204200198002000240d88080b01d05845030700c1001c030910243c40c80e44407031800039007817665101d0402500010700c03916180060400d11420f0384414003c03800d11101411030380206000c2149042c0100c05c0d0420720b00c1e1b1440c04d4001c80400c400c141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557085638 1250 557084388 557084399
    0x60c15090f0605281a1009050a0803040e0c040e0f06040f1a1c0b0403080a23042609060c030702030d021c090308042c090f060a060303080414031213030e010801 70
    0x4202c100d2552041c6c03544010600f400301c08480d203661903001241c1c000e02201c6e02042580002002d0420f8400740022204580c41d40b803000e41c5640128400c0c4040000340ea400260501c0303030300000d260042006840400e03901882741286095400c1002110400014100c03c1601403801d000c0c425020380c1d0600c11606040d401e9242c20380510001040074041c0300078880030420b014095888034055488488016441029108d00310300380990644045d66070340380003503904c1c01007050346020740b00c03c5540d04104c502c1c00d0044400d009042c0c0121b1541c4040d0302041c0004d03405a1001c0c0b10070f10008050b44c0c0600b82021342004800606000e55102c1d174100500d004050000507100c0e0308031400e407902503448400e10a412045900d0030032000e000300480070b20000a00c0494080000c44408070300780071058410543e610b02030311040712640e10000e00022581030105001c600400100c1003c80138841c1a240360030034240da90403504405441103e094980c0043c0c1c00c0074140c1c09429240148000d19140c4220352402 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557086888 1250 557085638 557085671
    0x30f150a0905191106073906210c02060709080a0201020604060b04021603021e0c09060607080c0703030e040f020a020d0315170f07060c15090f060528 66
    0x90260401c1254001120080c05002c46104e8544840204880d54805c440c0c50200a007401714256141d0044885030300400c0d803402e403e0400c3c032620145001803142031a1500c220b804400b08a1514024407451283c7c1195410303900031250000c001d5001801241010000200a00d120382d10503150b903000380400c0d100507031b80465169041500094045082d48a400024009120710702045000340d1f2041d00031020140c0100c0c08140c0e44031995491100300f20301c40c64680d02e40308072114581d07208840e200080d001e032170f105000c0c02d98a0f00901c915410614680812490085240c00a0700400e4203081e10144514043c0200720601b19a00019400d0034111540a5039031190800f6070b0040c5512019900d4000c070310000103800414619034407100403c40484620340b24900014002001c0c00b40e40e4012500901888501c8411580825030150342d440e190200001000354401c216070040e030040b400300c0814464000c0c40d001e0102020303481d40e0040102600d42c1020022151418401d0900c109040d003e03204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557088138 1250 557086888 557086903
    0x8032a0408070302011214100509060102190b101503020d150503061918210f0503010b07170705030a0906081909020a1707031e171602030f150a0905 65
    0x2800c0c06d010300752801d21790401410902000d9441e05038410104a2049829500c80d0112001034031030514a4803a071004986408401c1c1c103041907009022154800a490000c50079400b441001b0f07821011604c403030680a10b40880301030300c000281c000c500c0488102451143d2504a0254592500380900d4280884d881d103070300400008036800ca080c044c952450440e041100030251483c0001d01103615881c00074110540e504200da940069101002145801850409048121500c4950450f0718202070004642d200e550110b4107640300700604a0505043c0010307107142841440916243c1c07002034402411811294010003c000c0b51030184008048100d00d1010780d010018000309004a90780080b8214642950200004403100010348401240104201054910804c0b55881030040d0410340b540c2c200c01810042c1402500b5401200d141e14040002c1140c4100e00b2255000503c01e1380009040039090751444030150032801310084140c40d20364105500c04581001044042d4154545580d180030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557089388 1250 557088138 557088143
    0x30604110d0203010f0222090e0a140c0d12080f0121050a0203030403030314091c0c020409050d09082a06030403120501090b040c02033408032a04080703 67
    0x1146028607056440c290492003000780d200070306540c2c81800010030a41c0170550b1810145000e40d400010031441100e008144401c1c500310f00070000c0088984a59007080d001d40b0340c4907814031401c0a82102901d501d0a03c540690007140d80845000248001400041e4010711000b88000030f00d0045c40f40c107000d441d0704442c2c10720072203007241c0e1141145807a40c900542c0d42006503040c44007140020415606400c40c000e0748990b000f45c1041760b10750091003907a88598080003903c4203061990b900020384a00e9603203003498001403011502c40529222282042c20400c0341d040061400081880235503400c120b1a0311500703902c0601d0a1107006407a42c15110091250691300c1680000045030925124076000c0e1100719105400b04a2569652004001040701005583c002d40c280f01400140328004802d031000c01445500444010314404281c00d1100100c0d101020650303100e01202d0042220750010b54810024180d5070300c00041c0c2c0e42810b039600070344410030440c9410100014842d01001065943c2101d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557090638 1250 557089388 557089399
    0x1050720030c0609100615051e0d09211d060f0c060c120a090b0f0601050c0114100b09031c0201180305070c21080f12180c03060411 58
    0x121480325034110b1054840d03400c150f114840600a44001c00f10b50000074503000d000400c4580d60782c1940e8034424180c1d00c10240480c1e81070012003d07101202c00c1c240801104c0e554007030710304000000301804407901c603001070b90010314040345100414402e0506407c50701c0b45051040740c003080000c0c07410a0b048905400c034010b45020031039406a801e21808e0b83c112002c140700f540d49903c0c0c00180f00080e60004208482c5001603900407500150041c07103403030941600108079074440d6450913140c000100003d0501410090f080220394003c220a2046041805601026001ca414003084c0d09020380055040032145030380c00c01c0030910360790307001a0002e0a04800c00703c034008038003840400d0380185024415400003400c0602c1803010180e103c401425070510600340b03065030035262200495480c8486401c00c00807883c2e8810080800d5400014244a49081d0102840c01c0d80c0c1100c41c408600c3c0581722646521240308842c803580e001444203087c2c00005070018041440d0a841754441c1203042c600c400d0048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557091888 1250 557090638 557090687
    0x50a03020402160209011203080c0412121103361c0c080a03030501180b060a030e10021209150c04030b13020312030a0c020f0c040b0105280e03010507 66
    0x3480001002d400f00e0b40c005280300000d41e510046460206482482100011000800988040c1c20682910140c0f008481222422001ca54809000c440b1700103004007030250641e81105091401c00c0241443c19019803160614451a0005103130b070100740c10720a20f04040e020400d00580c5805180c2d82c811440003050443e141c4103820300e01a00043c581120605008400200003030603015003015040f107045900f03850031000a070010008a035840d8009a82c400c030100407000301644641c20000d444101c807810303038000d00307403481c0070300103d910a0024211803c5000f041054000742800700c100050f070400d5000d4400c0c134005803030341128490313800005c010b900c4440125000c0044e030f00c030960b04942d014049480b804807883e1003040742c1c0c02c11622607100500b801030300c003100391001c00c4801e5421029401030548040c04030401018000d090030071410020300f4400ea010098400300d00100b800a1001410300500000000600c00201c5e8903603039019070306100500068a074840d25034004580c0c0d841c08080c24 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557093138 1250 557091888 557091907
    0x6020709050c2d04030506060108070806010c2913020a050a0b0405060a051207020a0b0106020a03120c02010b0a030606030302071a09131b090e160915050403060e2104050a03020402 79
    0x400c2d1040780e4030810b0f0040460084100140050568020502603d4601c0c10f40d0700c4c06812079003100d04903281e600050001d001c10300003902070840784081c0e20800c000c40399546601d4213907560304401119130043c42074840e4804425418650140f2029101c2964881c1402e4149203010089115034172030389025070000120420307003a1003582611140c4044c00b243d8000d509003004025940c9503820801e4940800706400015244e00000c2c86142c4554140c481411130f4020f81c2c1c5010081100b08182810742d505c5544072200c9070f50b1001d100d006584100c400140381421030800918240c40f903000b80c042ca10416100c0e2017245008000e4031003e5404481580821301c80d4960703c8060040052504d401d020f80002c407042c6560003505481c20f40c1c04c00341d054045540c0c0c032015422068004500c1c4004500030640a12007920303180e100702c40d0b080c200e08000b07140a03540e030756040803200e0440400b440c94001051800ba0714026407004c2840c0c2070034503000340c101341c1400001590302f46030f4400244100c5c1d00040079010b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557094388 1250 557093138 557093197
    0x2b1a1906053a150b090f130b060f030405100605060706020705071e18090b01061d032415060a0c060605041d0f150f09030c060108010606020709050c 65
    0xc1080e082d0071010148035241840905085615032002120110303001c41c24059500c1034903400203000700410700e0194803009110b4115010458405188e440f450100c0a40d255440200303040f020110302c080e601c0c601814001d041008a0149a010b80d0414400300320303503074480090780c0c00507400c91001603491049192581c0343c0223241d03204400c09410b050482098030310b42018407049928103011408035148038640c03001102c001c0c0ca0300600d1030101c20014403c1c01d11411004500070070002d40b0125100a400010b4a0b0101c0740c1520402c034000040c40800028480800715004000541c40101c44000640090118040d0183d01d41c00c001a03103814400b801840e800444c01440d003d08200059002280068150001c40c120002280301f000b1503000301e40b0002903210503c0003144a0aa1151030b10090000c030307140003074001c10261100f40b01d44100c0500c1800350900074400900001440d903c1d150b0040d0802c1815070000d48902c8c0f0744010401c90004070411600a20669616050000c845c1c0742d8001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557095638 1250 557094388 557094457
    0x1103090a0305011a0306010e010e13080d05041211070306050c0f160317040f20180906060121050903070b0106170a0504020102032b1a190605 62
    0x550040314034000000348107042d4458a40043c0c100b008040021410090503901d64083c8078202c60841e02600400c509020001002c0d0014010034451184c009180c87c1c082a981041d0540da80703e40c1e51318107200030000e2101c0c0414100240d42494892001e40c0d004079501c0700b540d44400760005440c0c000243d4001e14010440d00c042076215003c1c0c0c0c44641b050800f03100e085540408502003201041058807044641007901d01c103580c440340102d6004041c5d59140d2459021200c080c0d042e8070301ca00164000e40d81e61000c070b0300403403009a03411060315140390050714004010f005141400703014206182c21100061440c178041c0325032000071034140c031240c108915620902e80c2c090035008520001040c4c89910850421507940e80103038a80c00d6485102914041b144203460080c0035a00410a07017000740481201207940403103880c00d00d50000003992681058410900c1e01c4c102c9030102d5a141155442c0180040359002e181104c0200c84509000001d4854030890b40791407101034411114440c00b081009891 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557096888 1250 557095638 557095657
    0x908070204090303380405010513022101090c08060f0d0209040c030f080c01150f05100306081609050903090a0e0a0e03120603010b030109032001110c030c0f0703030f1103 75
    0x1105ca0003030658031005052031062206041814401c08002c80c0b0b0070f40203850682d20010500104030840100030f40096120000111910101324212140050f070641401e00a10700c0990200d02c0c1110074400411140c0010415803003110700d20000e8445440e071b014880700c40303a4151543c02d1036450781d0410b8001c2440765800200440340702181407081062000160202c0040f000007804080000800800d040d00c0350f0250508840c0c01a100700031515102c4110342000e034041c20700142c07040e2034180342e034104010072b1000b44105403234180800c4260b002d4401c0a5200341c000c000340d4140703600300700003c00007280c51103000030f07140000d004030300c000304503a10036005446040304490380c60400100d40516100d040381c03403d02c81e518200343d002490506000f00204035038565905080160091814426111410340700007040d0359520000c01d04045100041a80029410003940ca031421606224079021741005c0515a9421201007040040c0d080781c01000c540303c42c0e04103c1a0000110301942c650701640204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557098138 1250 557096888 557096921
    0x70f0e220914070e010b0f03130203120306150403050316150e0d08091b040c110a0606030b0903070b07030902120610030b09071214011b030f0606030908070204090303 73
    0xc02c108115a40c08511a00c600c1a07515844c3e6850383e0550b040030921680711040790806c0909010006d007401198407400c41840c04800d5403e90700070030301d4030303801048580040100006024007480c21101c0a91049040800c040c5058207541d145030301c030300403900080440c01189460804001c4142d12216911036094801c109040380c100e80a981d8503240c40406003c0307000200807400c1524085284c4540314150144100d10b0b00e40001400300401420748220104102c42c4000503042c0e0b0140945000240115400f003015802c504245581150182203440e4641c0100074030800603100e40d2030503034006140e0500203100c0c62240080358004054003c1402980162010481c41c03440f10521941600d000d00d03000800c07583c83e405510f54410300790103058030690b0300b203102e10002804d0192101c0d2030310b20b0000204200c0c00c0034404640c6c500100300c244c80400e499980c0020841d15a00c00c9000030807140c035042c4203404460703e4164071841000750103805140c407100c14000f414025040700c40c1a0880205 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557099388 1250 557098138 557098151
    0xc09030812040c050409030c11120a03110d030915050c070c0608090607030204050a14030f060c0a0e0a0617061f0309050106090b01020c060714010203011409070f0e22 73
    0xc580401d00800c4400703c6040341415004030341800c01e80f081004040d450784510a50302e015403111880721140511099000c3e403600d00c0f400000e8010720a4070015840303501c81d28500410000800c0c10611926119030070940790415034070205580207400c1803070345044500056151030318000016244284075025002941c41c0380000380d460743c00086c00f4450780e41082564021f4a84600c11416403089201c0c6540c4038942001c1400034481c0901c0e903050541c001002c07540d01d06450284a400c0507400c80340020505004210221101d400005181040c82e08803200300b1503c0c00c0c00c03405842402a080820148516600003c2d100d4442c0c40240820030443d000208103041e03440d0700240508848001110203500b849030000e04000a4040c202c0c100c40b0580140c6491480401800555081400c0035070314202ca1207200094004207100841c0a00901d079020700380f9008040502800b160083c2802c01000080c206540c0f4040d40241c005445401c2110950ba20b25116001d00e00d01400210413039840030300d44003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557100638 1250 557099388 557099407
    0x2030409021303110405091e032208120a02070b0904020705070941090a060501030f121e030b0f090c18100e13091b08010608010b060d0c090308 63
    0x240801140d2181c2d144e4030000d603411040c00140c82d4107503070691180d84441d40d10101c3c031071402c25640d52450013800316400c00e81d01310005071030100c800491031401c00305403100340456602030001700c01d104129203003180380c0060f00230000c0d500e03801845804441c5102240504a1f5915901160f04894020085822968035142d20304c004040c1c01d0229000590f0180701d0111712a120003910700f0701950107000d00d1a1801600494803131410061001980d0b01800d50402c0001e440c621031a4042c0d4010b215403060b002c4146440420074840d010504140140e401c03021850814183d1074502c802e40342c1c5004a0716a00301004181c0c00c0c852080070035400241302c400c03c59110031100282403c0a00c0c0601c2c02c8460b8080420b0200c1c0820f40c03450321001480710500e0041c1418142c9108011080e403901c0003800500f15164800044110000071906101869081200100c240204009031425100811800c410903002403200e100d100111141c403500c801300c0100050045031907070011608258010759401010 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 557101888 1250 557100638 557100667
    0xb060f061605010c1101110405090a061809033c051902160e0121050a020d14010b15091e040203010b070b1609031e0210031505030606060a0f0203040902 67
    0x15159000160b0170f4075140e80030000c1402011040c0c901c20500b40e00d018186401e200810400a2901e507001ea298034001903d020102088000d1041a00c000500e09400c1c0c0b070300400b4020903481c0b002d04e01c1921810090300440329000141000c5020314100f4440e44101c0042e1928003913100a01c45000300507441210041d0040b40300280750504691002c1e01d0741d200e08130b041c0326140030300400d4124071a05455201080000b00c101807114000c00440391001400d90014852031009001100c200300f001500403640311090040480b50700b812071380d00c0142d41c01e200790108280aa40030aa1040840c204a5200c0d0101d810384c1e0004414040c209640d25a107801403660380303038028041101e05804090000303200f000c6d0302c0840c41942c2c80c150b403003000e00ca01c1c1d910b484402c3e0454480c2c09a082e4074840024005075210002040071024540b008035803644412602000e0220301d0f48150b000390000ca0810029955403402c84112409504108402a4480504920b540215004241d40758400030315002c0c006d450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 557103138 1250 557101888 557101901
    0x60c100c1d2e18120c05100306051302090405090609060c1c110c060901050702030307050c101a0a080f03300a060f1220040207150501080d05070b060f06160501 70
    0xf541c09000d88640e135010b034014070000300440901800b009010074040e503c0c0ca440d001c50000e00515000c200c00741c0362800110800380404444090a600140080c070904041c042c190744080700c41d0180c015842d02024051301d50400400305400507a000640070a590440d001d15204202c1e076500c100101e152041c000704640d0b010401c00d011030b00c100300c0045e0001605001d41d0b0b1080780a41e020354207641703a000e0181e40a4003e12581203140c0035501c80d041401c50300f80300700c4000105e030109052011181206004040080740c010b01c0490f000382c01a400d0141d0008102e8001070090041d5004c2680392051001080080100c80c03c412a06482844408007403500302d00183c40c21000c070146c6141c2d50306035004580c80034403c020f100c000d6140b0f02000d22038007180300404040c0040c0015143c40800d03517a24081d82100102502c506070b4030300040c0840f10081028149003441402c10b035141510580307542420820040c0101c0c490102e100180b0919160030040c2ca0315081c640302e44000b005003910301503018068 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 557104388 1250 557103138 557103167
    0x909020412050c03070f0e0613050901051f0b1e04030209092505030a0303090501060819060e060403080a0f0f18110102070f060806030c060c100c1d2e 66
    0x420201220310300e0049050b608032041138246020691404d07c0034000840001c005a520071414240d000001000d401405d01c5005218000152480c2051100910a2284580c600310900c0503200b400803003a5003045842c40c5244080c0400d00c1c2105084207469449542c00c000c1d0824100c200780841c0c100c0020302c01c3c03003569440316002d94241c85078009074502c200600c2029850b070b00c01000100807034001d600c9112403502400010902c16210a0043c1c0740c8a0080581c0074501c00500c20181403120610403001d04d2070201c0050540d0341450b0300c0080500001030302503a03806944500c01c0883d01415400590241213014080c0110b00c00c5291340d400d0a40c8000c400e41c0c003800981116500ea40c8041080d2040c0d46003040b00742045800d0400c00c6529100c0102010382603c54401580d2480c0d451001130143c500d0b0600081c42c0c1c010003c00342c0700036291b240036a003080c0800c2e54580704416900b40c100c2e00d4000b109442040345444a04113005000c04c1d0458252a8080d81c5251089200e82c4408448000b02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 557105638 1250 557104388 557104393
    0x602030d05010e060a0501030e07080714150c0703080d09021c0203060f0630062d0408040e040302160e071d030a140307050105100905010512120a090902041205 70
    0x80e607034044030143d10001c503010359004206040500042d03004c3e038032446410306101d046540395074444032141e29009080d0807841c011101c04020a500b4585020425682100a0344107404d1141140790681d40f0a00c1e8000100307170800201c0e200e10034080715800500070036001000c2641008140c1c5442d0030b40c14844406034000d000e03540000c3c442e5644280b441c1d02070b15010f00042082500b0341040c440744040c1e101d800d6914050040c02442120b0104000c80c01070290142c520b15120007680004440807500b81c800c1e1b44080ca075000c100201c0d070000140c604440d81300c840000b031907840d8030303049007080c0d120414685200c01c0d000700800c0c00d40700c5085d102d203c1c2141d42c40300f00c00c0d48445e403000003ca030001140c255155101440f0100000e807011801c2840c0d06282c411a410585507035250760039a0030448141003001c0142d41c04006441c030383c0c012940101004c0c1c0e481e5038805417242c4216110640f00e001540c401400060615065124610000c010300307071000304544440d00c0d035038100c01201c02c49405903180d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 557106888 1250 557105638 557105641
    0x2030703060b03090604021e0a18061e15050c01020c10050a110f07030e09090d02010b1023160501140a0e03040603050717040b100f0b0d020304020a03020a0602030d05 73
    0x280b4480840b4028000320008111039616542080143c0c0b85c102000b080f64440d0000988058481040c80405030048400307441980052034107810841d000382d0312000918558210a00508280b40c0140e0b0584199005010784505104800e681d00e100c1c00c047c000040d07200280c4e0310808000030516024445824005020030340303403240440c050b501c841d58445c0544030104410501a911180201245031103420203003075094640000841655044841c07202e9504000d00c15445540d080c0304082600e24100c0b406022000e14a00080c820344d01011f6080265441c50514500c04401c442a40c941c0700c00e070250302c0d10741d0906190550282c220340d00b0010042503c4004900804058010485070a050500841c2490b02d404d43c110003401014001c05d0a000701c0d03500d00b080007080b1b90101440340c0d002d40304000c4540ac1096178154000c1c03550344a003030610740c40d000512840c0c5450b42100c043d0402e02d0305c0943c60752100e00001d040c080082e07100035481490040d0010301c01d900480604420660040308000d00e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 557108138 1250 557106888 557106899
    0x30610020606060904021e12150301061202131b03061a03010b090108040305040515180301110d0e19050105101202060703261528030b07050d0f0203070306 68
    0x46003030654026070f20010a00005115080680c01b0f0039a250901501403800e0154510b403070321540c0000003145200c504401002100c03030110030030344031010b42035000700400c80c03070040721505241500000a1207009510a080c50383c090a8000d842031047e2a5400300300c441c20f4441c0a0000c0c02e191113006004030300031116400c0d040c0001d0070b0700d040303507800707001c04d0702c1c201007070004540d680002041102841020310020501d920350900a0301c40302c282200485d42c480c040c0410140034414044070b584207a04002c81c148441c85510160342002410110108101201b00346840c00d010145a034000000c00b104000c034107020341508818060346010403140152a1500416181c441900f45c020750004c50410030a0002485040c20b2422a41c945003003200703c03441456000a10b8200b62450340e180000c00c0000912031030f01d422809109500850002c40100e0400d40740b2100d0543e51001900034003030440005c641c1c9010318100e0301400b0402c40204820011410b0120080d041501c880c400030f032030a40007240 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 557109388 1250 557108138 557108143
    0x3060103020609120712050c0f0d0c140409080c010b0118060c0b0a0e0d021606050903070311060c07080a030f0309030e0415090e070518071b08070b010b03061002 71
    0x5a0303401070304a616019204044c420344c4280021400082d209405000907440004046024264410006000702d80004010000d030807000a030b500748a594170302c44400009a554000000310780039500d15070300c0300034160005001040600000750400c5800103040003204d07010b41c0640f9818400362544103044000b1004040c402d0340034050b500108081d0b075800300c003046080c80456400050300754040380d4103002c0c100795401c000d5043c40d0b84015a00031001c6a150300c1c2d1710304034040a04594a400c0b03003403c00100000e0341d00da00c6032002400100795408400941d0300d5080032100d41200f03031411500100e50b02c214060340c4020f16035040c1d0004082080c0d280c0d500d44030b40a4204120741641d204c3d01416411420003000300720400c50481f4106a031980003400b4100c0340140550811018050000c41e403404062240c000480f0402064420b001803c014003160080700c0210b100000e605e45002e50509480d140364a8400c051020b0403984030f070b0000003844030078000103511070b0364266401c8140580303810040e603 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 557110638 1250 557109388 557109391
    0x20316030e1e07050a09150e15012f0d09091b03150f0b04050a090905060c030408040905010f030212010603030801050f06040f080a050d1d330306030c0306 68
    0x12120b800004110241803103409000c55020360040c161450990350703070700044100d0001d0b402a0041703600e42040d40444115507070000020010713100000034910740840c02c076051010751786c03a107030600100d1801144489840301c80f44030003072215080c150300c600035480007640e40c10500442200007001c006021511038218082d0003c110340341030416001900c00202940170301031102d10b0300c0d11103125020018070030302c04104071001408030304840c0b580c580c141400d011030041c1e03940091107030350b040c00701d44000518001091a801900d401e182c80d2aa01d442c43d15a040c0d20507680940081421b003000495a01c90070002c18007102d10885042541c5e2483d50728403802d0f68868030020380031a40000c01044982003200000326133440c0105041e2034161a40301c92543d0750380344d411950b01c81d030041002a04003c41000141c03c2a00c00c0d09100400b48104000c0b401d9191200c0035881c081d80701c040702510f20122000c13091440b0501d00044c0c807510014444410a25001114254880d20444081c442c0509011503a107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 557111888 1250 557110638 557110661
    0x70905131802060306130f060f0b0408060a020f07060e0102030106030c08190e0a020303030f010f0f030b16050c06070c0209160c0b1302211018020114091302031603 72
    0x8181501d81d0b80c0030028960401007040340c0101103850f5000c95030340e151240b000c0f40d840115000540a007010242ca1643c28650408040c01c4420071040c48400b100007080c56000392040d0015a6848040000144c2406194802001c01c0d0a0840c111781d5000190095410703a0b80c190f60800c6000e40012080326880f030306071406841111140c0c40d95508022607000b602e040d81c88001100c0060489501091031548101e0b0201c00e40ca07800c00041c402982c0c9036003a040103000c005c2c0d070080340b142107441c0c002e110800640b60f00c1b04051052401c400c81401a02528030003a031003026078480c0d20388a40003519142208604070701c90b001e000300141c2200144118041c141140740c0d10a265101c03203545000c400040031b00300084000207000c0481c0141c3d541d4101000b1610f00b0000b0000703001c1601001d0b4546410860150b51460424220410244000038618881d42c0c091074001031401070044281042d100302c007000b03a0042c8c0d049030b0b0110303003080380d1300254028040c810303c2c01d030095099a4101c04480c65824407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 557113138 1250 557111888 557111921
    0x110606010e0d0311161202090115020d030e1207060f05010b1c0203130c0b0a031b17040609060f0902150705030906341202010504023607090513 63
    0x1d94011901c16201104c0d91102d03101100c400241c00c6405030006000f03a800400c0051a0350168811400c20741e25003401012503111a0600b0255030401a40791104c1c2c41d61031080551b188400c0d100c1174800c00402c1c0f00c01f10010782d0250b49800038148035014161409013007090720300b03007000020f01d411014222991000582a04440d8400303042142c4081d50026084210941c800351414012401c0d109200006050320b080d03107580d82c4030036680034040c0c1c0d9401c40000030891000300c800c01b1060b0025040742c180d5004044125042d0394502c0d0080c000c04d0240380151032585031140340303c0e407842c0d65400601101e008a5291131643d100d141207600c244914180280103030000d0282968508040018143e04521641401814544103002100302c030075150f100e0020580c103400700e00034094a0100f0118441d12403000340018641a004105810002c2a00882c1155403c09800741030344502000308020060710001889400c02c2180201610340900555104110501d00c00410607450300c100034040308114007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 557114388 1250 557113138 557113159
    0xb0f0907031119050c061803040315180b090f0a0c0501030b01140c060402040b1801050f061e0a030e0303100b1804090f0b070f0804020f031903110606010e 68
    0x5049000e0720303401000b031a4040b010b004403078070342503030610540842d1800e50f40d890715691600c48203840e01c0000380002082200d00a080c080b4001c01200311419070b07400034564081c022070110b81c400144408440a22031100003c40c11041180004640340640f00490485041c218488003558641c0301c0b2910041c1850031000d0204815400391b00706c1d4104501c141015503401c41590303035078102c540c891103080c241030708240200411460301d44150040d00200f603403640c01801044150b11461a01030280c9440340b41405580c0754659900b504452585114224226505840c0505103c054100c2e03120103002ca8181001004220340c0003050300e01c221510b2142c0a43d80b4a0103e58503100e5120301d6400f034852495100000c4981c0365070085082241c481c403c56841c4202e58203040030b0421019241104010306ca443c0d84044a51004403d0b8000d0b030100d0f50420944a200300281c07070100d040d95403030300c2454817945110602d0f411800c080800707a509402e0700c681d40e480c10011070744c4c105c100340c030303664015582c03034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 557115638 1250 557114388 557114401
    0x1409060405090a080304080306011805010804030c150e03070204050601081017010f0612060b03010204142209030f020609011401060305040606050a09020409061a27060a080106030b0f09 81
    0x81100790881481410745a4000f10707911200055072084605032035544002043c40040c3d640000d02002d19007950061180490415000824088010f07001070f040110801d030303920074000381c21681d403d40702e8400420013400703000d0050980c07603810000e4240d00c110b00d840c000419550244035a20312404000c0055096a814910440300d20304001e51481559940e481001007c00301354455800603180c5100c2119001001f450020301742c0c0e00d8014064041d034010700c02044000d50a11603d41d0300c4000f102c491200807034600243e40324554032810b00500501741021201459040007440c0c024000306d50aa4544d0fa484e00c000b81e00b655401400d4003c20b0624000411016100b94022030700135100720720101c0d440313a07607100045000d1880e4101d220382c0e541c00038003049030191605c18040105002214401d0003611410603803224002c1c62240b85090341d224400da90b085410110700300d0cc6210051699403600e070b841e44020040c0d0000d0048201091030701031807154034036101c00ba00c500310000800c05820741d500d0a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 557116888 1250 557115638 557115641
    0x1c08060904053007110f041a042a0306060810060e0f0607020904030e181b070309030f060213170c2403040f05011407120b061b0109060614090604 64
    0x9070300000031080c0b1100520510340c1d68010584c05018140b058120031000c070401020003240700056200d246055213003441140c071210100e12041080341c0c002641010300c544809000100210303071003900029520429100e405038098401e48020b6940d00800791759013510042000c08a014620202e002e680035203000e49880305054111050240050b03083c400181d001c2011b4004c280d80840108000c504d03c90014100008000a80d021310384401006050200c01038100c0f00c040f1014000c00c2c00c00140c0030041c14042c64003600150740c048030803100110b490030100000d4002035100001c44800d1500024806c1407a60a460312440180150610442807010040c0c103002200d00402c40c0b600d0400c107004030254180142d8815030040c6024210003e042ca0410f084070005802090131600c100d040c4005150301c040085202c16041c0b400280c60740342e80380066203600400304101a0b140d03032a8082c0c0a00601074200d40003d62244e00103111540e110170f001e844c98a10904516000a00000055602c2c43c09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 557118138 1250 557116888 557116933
    0xc01110a080d1805010b040f02071106090301060803040f1806030809010c02040b03100b030606010f0c121e0c051b0f0607080f2d03040803180f1c0806090405 69
    0x10a840094241e03d041d861610031041280165007903596031030040302e82c0c20310340145e03041600b004c5002c620700780d115034a2114003e0318681050007001c02180c0c0103440e89096100324051300c3c11500b04c0b51a40c0d0744000f140070b8055236009204600850045200c0502d240340a00016298070100441c14480c0d0700c401103c0354003400105a81c4583c8a8010101541b0280902ca81c103650941d40030032148881c009045c0f40c42d0000c1c01c42c0e410000c0c0600072818541e80615030240c02031340540d04060001448500f12045e070f080300d62a80c0007250310045d0403611500150541d03d02445441510344403007003912002802c490071440c550700260510503800c060710300f05001300f00440c414200702e4280000044040c04a400001c100301d28000c0320464224420246020b80191a481d030085c0c0e8910b00c3c107562400b0311030102405684142c03a210340c5100c1070b40024030204102e598000304031130301010842c0c0303aa482c461039190020b010036000c01c0030617100e0400003603852055411100501e0101090030f40c03030105420 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 557119388 1250 557118138 557118157
    0x12050d0f1d0d120302310608090a1205040501080711060a0209030708101d0a020d06020703260a0e0609030a0806060f0f04090b06070f0204110c1606020c01110a08 71
    0x142c81c841c001c0054005400d1141c998001c0d034005890303669001c80800c00e0511000601c41d00d2883c00c2440c0301070b4019080b2002901d44e1860f0498094a4691140c1e107041c3e00c8a000806215050025998041c0c0c020050422540240c3e5441d606884441080d02c00c2440c1c800301c8801508a50009440255241c0090500381800f4080740c8401d540d56070385504203460801c807240d0b4191180840703210404d10448180c0011000400b50030f0320300d2543d001070405100f60703000420351600402c0003400e040c02544161000918006500c81305d01d00100442624441110b028100c03d2820038040003d01c800100144500c0c4000011031801201d080262403001004005944c032440c20801000103080801c060a94100066035007515542000e4411085d80c0301680b2090150205200090124542800c0c0000e085e805983c00510250300741c141910520503001c10701002e2003a001075070b41180d6501d0f1000126002d41d4262240c18200c04011200d003e0712512064542d4006181d00000c0b40d40b42004050220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 557120638 1250 557119388 557119399
    0x302090c04170a14070b03040b0402040f0203041b06030c020304030233180103050c09120118050f0607080709062a0302010e21070816060612050d0f1d 66
    0x155124007042c0594800c2d200b40000303400800ea904200880201c460240c0c00c2039101801d202400d142d007440e90f60100400280c115030440c00440c0c00e54840b07a20580b0341c0c0184590540d52890b06040040120780003500503090a420a20009071041c070901c42e021140b8101e0b406585498034580811448000002200c0401e4060000120302c0f107941e00c0580c07a00c445003904090303c0300048518801d62034407984c101414141480104000041c45104a070035000b01141d0481c0d4440101c0341c25401021403048075403400310744001c00818040001160600b1021311b900300e41c030603510490210354103203040d5401008540541424403906000d01400505890200490340c901c0704000f005e4010586041c1054001d43d40d01c00c840c0c0780a42c014272102da94100308141c04641140c4038028801c0500c00c207030005e881c50001203110000600944840124540c0044003071100c0d40c0c44813401803950002c244101e4481c400c4440d00700c0a540038038000c1500c2941901ca03107000841d01c0d600c00c0c4140940c40c880c1580300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 557121888 1250 557120638 557120647
    0xb091c0302091219030201050106030605010906110c09011806080d2f0307080301080607090b040603020918100f080a030210050408120705040906080318010309031e032309070302090c 80
    0x950040000c0b070400301c044d64181e0944900e40c10b000c0e00b11581a00411700b0142411828003442e60000c40010485003141303000003074244640303a503904200f052301c01c00768400504c01c000200811520b0103100303243c1104008000642e45c40718010f80d10030b016012400410100b541ea8071191030145c03001c8500040140c00c01c0d5a940d40442640d04652110310100c40480d000300061144503420042154003480600307089002c01d0500812011900540c402d1034109034002803500440d0f2201c204e2001141000c02c0e1102650130b0500c0e41c0d00072248030307028081901c4061400010801800030b1400c000740d8060f00640f096201c00f1100c00003400e03000303006aa242004008030701c185051a4104c1d03200e2012696107a48860071700b100242540c03a65440801c075540180924000c14000030000004450309003400a402d00091401385d0329003100900710b0001c808040001418540c140e0844003091451401c03030640e800900d507000162803425a001c01e4158402181800181024800c00e60400071181245081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 557123138 1250 557121888 557121919
    0xc08030304030f03050702010b010804200a09020c16060e0d082206180b190207030203070e010f0e1303120222081219030b0a0905130b091c030209 64
    0x566200307990403000590200900c81606030700d40b080540240c4580700034003240b106000000d04400e030161021704000084900956a41348140640c5548080078101e0a400ca66401034040250403080c406c041038003a01ca010150070000480250694180b9101c20003030034401000c2c0203034081c1e079000440e60204200000550090364500080c218081062420300e03550422000a1080030020440000040a00001c1c0b0000003c0e0046e43c010f101c010014545d003800c1e520080303191000a030300103501409416804514441d0501c500c0f41600c015a4070500c02c2640c54880030204402198281d030f0500840c4908130020323104950303905c00c0d291a20405400c0c0300d0031007020300741c0400301e011208409e4500501044402001c0c030400508100360f03010b850030b01c045540c07042140b004e00b0090500700340c3c0d0b4a83d5403003250b0310301e8840005001e4514040095103404184101400d041a20a84140c81c00000040c03401000041640040c025103520082c448032690054002e500a03003807071075020741c0d000d01ca03014 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 557124388 1250 557123138 557123143
    0x8101806150f14040b0901150804052404060b0102120703120603150605030c030c0f09180607031415010f12090209040606180e07050f010314091c0c0506060603040c08 73
    0x60b1801030700f465803142c140c0c2c0400c42203481c000d103491302031003039207004010070b20802e25180701014442c242161b07155594075080342008264034201e0b407044064046120304019460003c2e03c40d900c500001c10120344640300680c0d60f40720404051060000800260340000d1041310303d101131418080020502940301e6803040400e40401180c016070039a03075401003060b49000c1050349201c40007070340a84040744114004c50800c81c07280c4480ca000d4041d050200d00342241d1014141109042582075405a0500c9030f03009010b8628081842a40c111580c086001101d498400d10b0400e80161152515401d1800c020fa030040c2110342c140c2c0d01143d0307800c8080003684811800c40d201d107209400c0043c01c0c60828115101c2e002c224034029180c10301d48400520810000034282054807400c07100030402e4441000120042c0641501c94510422a0014060340c1140012900d020580e101e420004643c002a811100c0340004078001c0c02650024000c1045420240011038004c0d02a044c41140c0719110b004051 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 557125638 1250 557124388 557124419
    0x2010b0d050d020c0409080405040b060403082a0c0901030b13080414091e0609150618090901020c0c0d08120709062010051518010810180615 62
    0x12076a820056036074140681c10300009030030403000c48080110300c2082c0c40e0f410003800340d03008a6000e960b4424902d0304607521541501c001f103600102e01b9640307810300580e516450400300009000150502d07020340e800000030800440001020f082c1090030380c40c44c0c6034204c4849018080015041c0700b00700c404045075207400140040c003012980260512000030612240560007060158015060307040c11406400c240304d000d800000c01c0311801c806e500c0310f22040c041c6400c24090305520120004404100c2054804900e806000c22528000071b65121000e080c240d204d0240056499000b003001d1903000e192102c4c50046045c014540141804d001c0620004480e80070f0350350300c1c0030810080701042000ea01ca00342c1000744000070702080300c00005142c4c01da60342c000c481d0894882074480d0001b882e008020040b10300800001000b5071828000320b42d20704003d0400f8000c400c0c1390b0150103d806034485150142500c01081c0c41106155251240c07030300d000074241d0408031203004944210014001e04925502d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 557126888 1250 557125638 557125643
    0x90c0f0d0515030f1c0503040c03030c03030b0d06050a060503010b01170c0408070303050c0c04090b072003031306140405060402010c03050705030409240e010501050c03070c090905190c06030c02010b0d 88
    0xc1ca694050170b52101c09030f200140d003c100700b000400420002444203003801d81200e505040400140d0a5440c0550107070440007031003900403500f42103a2040c014990001401120880820406552a10b00341800c0e03808071034101703000c02c160410017403058588205040c0d0000c1b0682c8001e09054658503403901b844050360050300040e81c0425040c4a4a200740003030040001d08503410000340809aa030801e032881c00a00903c14401b040c0c24500f0f5100a01c40101310800b04141078940d00d241440007600c2030705800e102658814070309004e400f000c09690021a00136500720009104540d04c0703900440780403906d00300480400000303000d00c50000740204003034406000160000b08003017004148002e040f400204400c54500c0030001c00b00f1036512580c90240c10745000780b0380242e0f0381c480e04020314554464507400a05c031181c4508001990012640b103009503c0c4503005450352052009030304030885840c1c01018003942c10b0039030104078060181d0f04c2a60b04010a0001198811003040062000004001e05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 557128138 1250 557126888 557126893
    0x10e1303050c15090628020a020c0d0c1508011805060112063b070e0301060302060304060204142403060103090515040201080109150302040902040213030c05090c0f0d0515030f 77
    0x510011820038000a035206c00c80d2420040c0c9461403019021a00780b2140a0141241d800105031646510030f0280c8650380c44042d0061405090510305120704196034030a64100c028903841d0000c00d10301c201d001d541207a81c0e4802204440042c00030240060002038245814000781b29200a50060603000f020002c001d0200c50300075060103262132221044600705031000d90580c5404031200010300c02100354020003c2d14080300012407480101c3d0040031f1a4001940c0101d000c07041104010051f0001d20a03582d0030000960074000792014495520340403125504848074a40c0c281c2a0303125130340051075000c14145400b081901254840500b000c240f921221800c0070440300300002d651300542601d004205100080040110310054004a0b21075400002d2040d85c90741000c0041d599150140d44d882c00c1c84140502070a5038a16043c1c0f4840344912400340560300c620f0004074103001000c2615a0000401c4400e4502480c0714818401030400074038040c404507091060759201e8500300407440300e80380741400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 557129388 1250 557128138 557128141
    0x115080307050c04020705061b0f0c07080f011e2307050a030e19031101060806090a050f0307020d020d06090510020918040210260a0c0314010e1303050c15 68
    0x10030a0901c5040100e05010f01d004000000000d040000c9040d4489e500d41d80400c0303404030019228175030b403180d158001c034000300115120241242c01318400781143c814100b1a0282e45107824824280c4515482072528910440c40240d00420035400c6408080016405807100c100480090b4100b942c082d904000001c034089541000e294040c801d50a05d032100c0401020001c40c820310121110540c2c000c010108501e04c41400841d007801d41107030003c0d04410065034030520380505269a100c1340d141c2c00343c86501c5110414a613a000100413284010340181502c0c3d0000801d80900c1a100c441140840e8003903600c01d511400708806100ca040c00e07680b103041c0980d03108408410040181c03003d0300c03d0003c94030a14144001680d4164a5042c01009410804150078071b52921a0300b14015070b0303520316404050b10401014410603400248201c519490420500c40000a202c4200100b4060500da84d00d800b030110745030106080d6400c20481c46460314518010307250000a062a001c00d0800110484580 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 557130638 1250 557129388 557129393
    0x607030c050606010801080d051b0106080c01080a05100b07020f100509240403021c33020a02070b160c0b070b010605120705130e0f0a06080102090a05040b030115080307 74
    0x50b10b030880c0092070541c406504007200745031900c5140451006024001a5402440118501000341902d10390001c11000341c4c3d0380c804603101d0054074007917070028029000040320340e540c034840d607030181c07000150149007242841400f100303d9006107800d99001100e25094859a034030704c41d2000c1c0c40d08056950903260947d01080c445a0f05c421801c1c00c26404501000b10180421581910101c0360100c1d1104003209040188182104404401400c2c1e205008010313041d8254540551000b8058881c2c0755181c20070210b03000d0124020011114010380080008020024007000070b8500702911080075030341285c2e039a4034414405000c0e03000801c99100880c15134284020810064011304003414103030703e0610030f80c1e0000b6074154018211300a110000c51441c00c1620500384d84070150001208245d140e0800c0d080840d034000f0100c0d0034011141c2400800f06216106009a8503001000703000340d0245801c2ca01000094007040d80041e030550350304c104c40c2c0e00799000080031100510485006d156204103e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 557131888 1250 557130638 557130643
    0x9150b0d1a06011b0515280c0507050313031b05011e0519120c0302040605071e0210020105190b011205091c0c060c030c080a052502151501090312020a020607030c05 72
    0x402140c9011030b040c41f91000842990303030044120410b5280001c00001000050b6100d0141c0d4038060051b01c80490030840418800b0718013070589009001c86001400315042c0e5804011082c0201c50004507820310104007440152001e1003000400d09205041c07000c3c44020000c034060f0030340d500300080c400c09002c1218138003e01c2109040036242c6000d51810742898000f814600c9003010050035a142c00b01c015150100d01580c01241a0340103000b40441040d419000b0701070302c0151441c41c441c03040800c0480c052201072040c2c0b040345006071202614174281c06904001440020011041130180040d0301840100704500d803c40b24446403516040301115080c40801c640001440205061038920284481e581281039168080405100424aa60b80c01c00740d60180130266100d91034411404008000150080f4942001040c8800512942c0d03070383d0903580301c0c1c000402c1c40060200d141c10500748007082401e00b01018040e4240101d4113924041d6000c54100d60200b5000d4000a03941c2c0401810007006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 557133138 1250 557131888 557131891
    0x20303031501120203090718020d0f0903080901141f150207030521071202011e0f0b01080f040615030b16030c050a020c1207050409150b0d1a06011b0515 67
    0x43c0604504614101180683e901040e014000c8a000e451664403108030254040390034a0a5020041c8501075140e41c1e050041c2c040c524088004c01c07403c0d000110102814445c488800d60701c06101803580c1c0320b11b052503800b02c0602c114040d21400810380840e1244225074840820300b2a5401841e5407460b604120381064025442c4100d16960640301c0910450180c00340c800381a0000303503103800882d456405070300620380c86550340c4400350303201c8040010040d01d51042e8624000034400740300314061440111482078044444141c0e99214002007404a0003541c4000d080400a05241c00b080d07849403240281001c044458010789642d6809a2003001d030316018108000c1c5007810507a00701200d00c40d020b034035071000062882c055186c4505900070f1003020405140204005402080031400b1400d15114140c1d015040705105410140210030364201540c25241031900003d07030b925106ea00d0300342d0160020010708114100f04011004c013000c0d0a0350305040c0002403103003004280200d40d02c0f4046807c02c50 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 557134388 1250 557133138 557133167
    0xd021204031e1d0612180c0f13050c070f060506100306080d18090204120209010f0f0b1305150304020f061c020c100c050408150103080f090d020303031501 68
    0x21040b00040d500564400c8a500000c046151210388010101d500760040b4030174816050082c1c001c0c08100441c4aa804c200110140191001110010103003c5507552032030030b980d009841540c9410108031923134846908034004a00c40c03171a10495480d074034903900c829402610031507541c405124080c90000110203a601d280e04081c801c491501e05016290812181a24244071342842119000200c128801000e40520302c01191a0f81d2510301400c1c1c04440280d00f20300510900001103840003081518100302d540d81006c0d40121410402c0420442e000100503c130360b0085100046203039503070550203004010800b481c0c1070312403074240100150f55642901d40d5002d07407070400007840031820b601110346183d0032680303000da501e16a2481152400612603901d800c0a40b42c0030048070800c1e80200203104485d01442126103c03608030400d0f0342d50342000c1c440200300310010400d8546c12560980500584100181806500d0205402190850f0700031110b041035107480e01007031151907030089100071000c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 557135638 1250 557134388 557134427
    0xa0b0904110105030717010605070c0e10051c02030a0b0906060405070806010f0c05030f0304030f050f070209090a150606120504050a0b0405030f0703210c08010312050d02120403 78
    0x1000c0e00d90184903035000a0071810000c0000008850f00d0040c203031a03e010940001010b007035a59503800038401c0e00110021101503403502c5c000241c2020301c0401038069035114400b200b0040c5000c01f0015200c1500399155072000305601c0c0740740941e0b01405248291801401c09031854580a201103040042c000c003000c0c440c0c0d00d804103110381142e001e010140c0c804003c0c2050b5013488038440d400e4948140381100100300788030005215000c140b540c03000d540911300c2a124400200040b107800d45050150324405503d0f600705104c1c00000d45007805e8503d0708015803506541040b02c164032030a003410100e94005482544841080001580c410120318003080100820001410556a00ba40342d1401c0e5030003800041583c00402d0500c0801e00c2125100c00004444690782c3c030480c03502600c03c1c03629010032012005c20b6102d00703400702654090421040503565684c480c6a003590f4480406451000b900c0c410050180a91014520584000e180070000d00006441d18582407030002e0800e080d01c0000400034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 557136888 1250 557135638 557135641
    0x20406050a1e0e0105030a0209090108010212060d050c01030903031d010e2406040f0204050d060c1b051e070f08100f020f0d0506010309020d0b0411060307020d030207080405030d05030a0b09 83
    0x71584504203116040c001d1170410350300d0722a00129400b90103450004c03580044804000104c4101c15801444102c000d050304403055074803242004440d00703040700003900304e03044940440403540c440d41c0303e46051031190030002101c0a1901e044006200402e0312040181e44da00107141c8850007c01112055415004d1502c0041e42100c807040e40801000d86002e014a813264072514002d950754050390301400d000b4103c115500018144074002d00ba00250310340100b14101d4444401580c042c1752040c210f0340000003030944641c16000082140c5c2c130011510142e02031080080b9000b44c0c1841c0308002442207000800905401050b04022903868a604048840c41004407a144a06400650385261202400001c02d60303200c000603000b03882e1f40c050003540b01c2c9041c0e1381c000401c0305089900c1d0140c3d015402d00c3ca0350384030200c24850705200940308a0050b170f01102c6030508542c400c1c2c00400440740304034409030500d540c84001c40d00e07000000540c4408180c01008104c200c42e0a88100c4030754010841d0801041e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 557138138 1250 557136888 557136947
    0x1e03120f02090123070605040c150c1e030201090203030309160902040303020705090a0f060e0a0c02151302010917012a080606030606130f140105091f1101020406050a 73
    0xc40074002d19110072450f002210314104ca071a505035005a908054240800d281c545001076204241d4094800c01c041d200d046044014031a102504500b6402a20010f14100201140b803c41112500071011036480d03140140040c0c40c18800785000304c0e1840010602c1e0b441030100c18880b480c00ea004000032a10511040000c258000345100480c0c01c140d540303a07040d1302c8202c104005403002c0003048050600381000062000c02c501e0380c0314400d00034510100070188183c00d0498955105008190360740700400d0200b05100a05150091002d1050400c840c0030395983c0302007a9540c5007600f0242d46a5550300100d06103656004102d07a640826150b008d151400c2e411000d800050080c00c9180511008000200780392684412580d0809103c1c103500d6a859507540510035240150040101c2d940e0308502624082d401041510821000203001c01c8600035202e210300141e0000203c000108908036250603032101007031004001420b116a0740d5652120785100142c44603500000140c0001d8031140000036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 557139388 1250 557138138 557138147
    0x510060809070e1801020a18060507030927050c0c15091515040f06060212070b0109020906130e090c1516140d02060121050d05071e03120f020901 64
    0x9440f1203800d440703900c2e1110300007020084400c1d503600050751b2001800039291a00714180014100da14000d80c06019150001244c140c05003000c01000b1545449080c0b083e42144502c05459150761072942074003914101e02c42c400d464060380c8030000400002980300d06c1744001d1180d5032440c5a24003800003141864940320380c1d990a03800e074450b00b048051b40400d107040c1041c484140c440000034024070107003000d8a00d09004000c0c0d842a00c000d48251506443c48024107019a02101c1c0c21500c446400d07841c04601c20040c1d44145042c9511001c1005000b1801a80d00518030261032990407556503450300d880c0051500803101052403281c40b0480c0515131440008040394907245022003d41c086070128034200d941c1d845a1110411180164945003410f107600040c168100d8801c0215075011a400e4407071a000324201000c041d140360445041840c42c2c5002c0d400034056244509003501e02ca00d2036403040008640d0030701049000072021a2036210416940c0503207203000540010841c0707422403c000281 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 557140638 1250 557139388 557139403
    0x315050c0d0f090206040e07110d0e01030905010f0908040e09010524030a020402270609060a08130615080c0a050307061b0b07090f080f06040308040212100510060809 73
    0x8201c5031200750701c0c50440c0681c2c01c6100115405071085403111344440d40d02081000031151580094500380c03149451120000e04805051001d89035270786900a0640110081e002040080c1c1d0036640345e050140c044d684501ca40c040c01405115138075256801c0c075507035030f01c1040d01602004e000d81c104400d100204442c03640700e030001000d000c98074415405010200e0f007860380d038507000380d4050310228070402c002c110070141500841d5440b000e0002036959074100b1486c0c0c000d5a180d15001201031000420072802250b130190440ca18a120f003401078901d6844005480358504088100100000b00f08040ca00400c403001c40d00e0340848504070124204008a07136602d0a0348602ca042140011003003a02c145150380040c5a15001560f8200034a000040608088018803582d10b03190903502c0000381a242c04241e50f00100c2942e0702400882e00d031500d0440e50004050310680e404002034022507000d500800c0002282c03050008003007402d00c0d050500440615040c0c0c850f44c2440400c0b800c021061001050a1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 557141888 1250 557140638 557140657
    0x30504031a060a0b0c010b0d050102040f060c120318050a050307020a06031a1003090206122205030a0518060c01060f0b040b07141c05300610030b1003060315050c 71
    0x103503101c5405c1e16030795014180f01c00d441500980a40054001e0107810340051044c0c5500301ca40611966840204503100d1010381c02c041c0040d6807000406e205a8840d40120039a1005010700200304811600c40b20309100c5d0403070085404c0e0b840010072004508000c02014020322590904100a1126001c0428200401d021032031207005181001000c1500981c0001030144e0050305503174407680c414150113441c3d102a42c240030307071149164110080b49410401c4c0400d0b140d000c0061801c0480010090b5126003141c07001c0c0e0844000248018029282c110140501e00d0002001040035131500c060489065002d42100703054607802c00090010101410403201c2403644003421003410003244410b68106201207444416410b001c84148c030344998440c0203050464281c94425400355400780d42d40f250380c000c4400d1000800d940c5000100fa500e000200b10311084100e081c0070507810300c62400511810304245054002c40d55444041c007e00c070004c811100101000c4001700312908040018003a24020b83e0f03242d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 557143138 1250 557141888 557141909
    0x21010518100b042718060902030c0d030314060a050123040807060503010608060a0f140315010602030414030304211704030f050c0103050f1b0c0a030504031a060a 71
    0x450340c40d08000c05218000e140d440b101c20744481d11500807220702c060a50802e00303882c040050000034402c01d0300c500c140d00c1c03658851440c1500b419999000180680c8841039a040c0520851940c403900c5000d501e88406120b940e001840005401840c0c41c0508007404039070051007844e074103000c03e9070410941d2841d003410b61081c076a10920098211514400c64120000310302621000150840c0c104000c0d5040e1440c0e5101d9424580c1c41d0014400c41c00d5491007500161001c04504020300201c01800a070307503860150664035003012070250232031740020a07805800140d0001500b00251080341ca00c00700072a4048001e1132610b0f152101200807002c651804810a0701c8201800c000c00106220054030829a1929a6141c40c0d803810825038006400200b51218064a448191258800d12030940b04000c504440502e0b43c9801d55042651090704542c1d01e0b0082d000c0001c00650a002c00c9922001e500c680c3c4d8250350b4a0440c81c102c3c1c01250100c400b024840140c1d07080c001507070717503c1c400c03034050320a06041d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 557144388 1250 557143138 557143141
    0x708031e0702040207050601060f170105010807050d06060942020f0105010311011457010c02031207030f02070602130305010b060f0306060306012321010518 69
    0x15031034194822088000e40c4140b0000b11001005804164a4104c82c00c0352544484209111000ea960780c0150301c14030103050b9202c0043c813866000d0084142c11005600d40142043c0c45440b218048a500b9009500820440c100403c1442448540c04801c106416035410075031000e0b0340d0f0314030881642c400702c0d49032600b020b8204e41c189101700b0060020401c0312009101035692820070020296449503c5c2c0d0004950400d01c000e050508011182031503440d400d2403c2c034007825010402903900c1c02d400e003800500c00308046422500c90b460b582043c01e40440010146400c0c49006900b141e441c000f4075400d641083c0140020054465030065101c4201c0c100032030021414102e49001f80b00c0c1c1c3d03000511291001c90103203010701040880e10280e80c8180300070800c0140300300800255010b41c0b410754040180400004a403401c002c405190084018140004d403949400049504400c003000d805100040c0800d04140003440301001017030000610001b05069410712001c614448031803101050f4580300d540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 557145638 1250 557144388 557144437
    0x207030504150c0507090209090604060e07140f13080f1911061306050a1106150114120c120a1104030605070908030a11100212040f1a0c0d0c02070803 66
    0xd070703501885622070700780c40c80c4c46e0b01c2da0070b01d200a4102c101410b020307070300180015040d03003860b200310015282d0030068542156940d40048580e40c603120034680802c8003d02c200017080d90000080c00784505c2084811080074101a94285005295070030a16541d004442c11822080200d40c41c02c00c0c0c030f4210405155460b20100030074035600c201880300c6008414540005a007540c050301808120b8000e0b40d0301c030225401e19050307590b9014184da5002c0001407031010a0061340c000c503000d01c400c0760032624082c2070800d11910100c54500440305016625000106d00805003400c80d1216840380c000042040503102d8100080e0207805a4040200040d0759000405d85043c0124151002891440300720307990342c2c400c0d88004149200200c80050309108070414030305605003900a5400710701141c1c4580301e02e43e40d40d85a00f4020038040300301b40c0300c1c116008900c0c8071014610302ca032449514812200c660b20507a01109000f15154200c5071400c5400464092000c031700c0c04000c58000d450982c200041106c0100d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 557146888 1250 557145638 557145647
    0x2090a020c0d170f1009020a18031109130510050403111606090b0414010c03050c0a030507020a080d0c03030b0f091009051303050d02030a0204030204020c0c030d03020703050415 78
    0x3004054100c2c03050952070070a05030702482030803100d183c3c1d21440101d13031111400b659004001380d6215138200b64044084c03040d081d1590192101d0425845e250802c40a26001d4204120300d9410654450200b00440000c40c10202c154a40004c0b0000c802068001540c44081d1501c080c591031003409910754020405061260203c0700030500761600341c60900a001101e820701e07024622856000c6170900c41e00184202c0e509040d18101c0342914021804041f02a0045030203200c05241182800018000c407005034800304140992144252038040d5203142a004124000070560300c03400e02d96002c41c00001c000c40c1d1080410003080c0d41400c010425035082400100c8034102020303200e800c40013220030803045c0ca503001000c4044506101c810095a1160200c2c58a100e01200d40075000c20404c015403090041103034011544202d04480040c20030742c0701c0c0e00050682e0f205034206904e42d841401c030350240d85170900452003441001e080131403408500d980c0141030341c0110321031600c80b000d801c0d042e441190b005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 557148138 1250 557146888 557146897
    0x1805030f0a030609050f04050c01110c0f040e060f06010e100f23070b0f01050f010807140405090c070606061b02040209040b03060f040c0b21060103200a23040302090a02 74
    0x1034081804113282c030301603180d0100802c440591301c89c81505100910307075000300c20803298501c01c000940700030140344090080340c620b2902212f0b0842d5550b01e5415601c1e0060000c2405188207000d01a0759042100004181c0c0704916120340c81411485042190103400400024600c09242031003000a600790548052500c1004100d51102e140020001c04110203802c40134401d10700d500506000f030b40ca0f681131091142005410340d003c2a0301b100802c42403401000c5540390102040c001d00c0c038090301d031408282d0b404800d0b603211401c0300b000b0411a08006072409481e025200c0d41c9031042d41000500514560311280250180c082c80e400161a4607a4542d03400803a00c0a80c040c0c03c8401600f070205414000b008121016180e108102402051000b2440308070b607a50041041c40d0000780041004241100e440680b50310305041d9141c8555907208466280c8110f00d04140350140d0b26107000010180500b4041006094220702c00d02c24800784000502c11380d026a80c041d14483c006540341010724009115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 557149388 1250 557148138 557148149
    0x20c03070902090a0e070215180109080d0e0f030414030a0609030519031b03020c190303020a02070602060c120403050f030a0b1c03020c04110706090501050a1805030f0a0306 76
    0x9506404030341002a034000f03042400041d5050103680307954038103205500314140d40c1c80005030403203241c00401d080c14500b4690403041c2d441070526401d01c0d1007010350071200503c03400c45c0c0b158004038910f00800501d2095000500585c0041c0c21000423000d03105450f445240540ea240124103800c50b20103440810480ca5155808001000400090304024210b07401020110590204400085003040d01c00e00400e820b400040c00c00456100340b0401c107801a4002c007407158414030500011056190a94200782842070280e140140c0e16020f01d60020300f0000107800c10380c195803101090000c1403000008640e03a000d000c8448440c180c0301d6103001c0394240f240e00c034913032003019000c0b080c042d402c019070f48803048140d0704031006d094003d0410a0a0f8840c3d01c1140003401503000454880076a04054200a240703003403100001d858001940e68041c21501444015a4a80e40d108208121180709101c3c80440401c22304031208450a5070351603555910486e00352410000000c0707001003080b4080e8020501400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 557150638 1250 557149388 557149393
    0x30f111203010807080f10051e07030c0801150203070f0615090f05011d280f0516021903030c05041805060103061415070f230f120316020c03 62
    0x2510030200e003640d40c2003030040c00542d003d4050005002400040c908a003962084085c04800303854401d02401401d00a01c804d00c1c0710030070424a00444000e01d1182e1240b4240e440c001410251800d006058100c16007194a0500f20007000d408869000001c0c3c030401c0f540190240308030699490000c001e17040f0503081c0c40c403c0848800101d610102d50b00300e42c28404000d44200901c0e81d9855406800c1017511180ca081a41c5610202e528800024030b00c0d400a648010207500040e480c04e807480844405003403900c0e00799503d5050203019006004c5c807804644080c80101407484620100320300d1315000d140011b050594602c40c0d21480760065054a0040c041141c901c40c088485c1e821110241074100c0c1c0190000b85440c2c40402c810403d960142d04002c4064040050449080f501e803580b503202520035141808602504800140c000075400480c801480e803030103103464251281031400c0c404110b42d0380f0710307000624281240c41003813050b1381c0c1c0808030703c2e0031115010b40310740305034203060101c5200ca4060 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 557151888 1250 557150638 557150653
    0x1090209010611010c18050d020a0f1d010e0103080322080a05190305011413091e02130c0807030506010c1703070e040603050a0f0213020406080708070309020d030f11 73
    0x15044140410070704503c00090011203000034084440c0003015200302240c1c50040400c0c003050510560400001d44054022080541c96843c40006405190b10950131080720003212069821070201c0f0130300515034401c640c0a07650544e500ca005600000340801c03c50004c11146031201541c12a90151603508500000c3d602d08030b8103001001e550000c0540412692409403075283c203446841106d040311a02c03020501600d014100308039080b032940c044114521b8907988088003087c207503201341c4c40c40115143d0280694195205009103204005035500d000c3e23140498400f01139411060150f40a04545400529640c41c2001a14441102e10010b07050b107040b1070310300c100407850038015030155044d0344808102e0700003038080006403611404024030766000080104c0c0055941c01100821601c010a0000050100e141804c01c0380c0090348203800099582d018040c005030031070380786a00550f131403906000c0844541c021179110066448000e0400c0300030319816440b14415642100b9016001e400e40c0c440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 557153138 1250 557151888 557151899
    0x204050c19021513030c03080a0b031b0a060801060801031205040e09070e13020a09022b020301060806041103072109050a1118070e1305070309170405060d0e0109020901 74
    0x2c0b48425203051020718050b2022940004108200269061717055441400d81d0005070f0b02241d0781c00000d006907003111b0311000e10340071503641400000a5448500e0043e0b000442590030040221000e500900c1400412001032100c0c031b600500107070559800004440c5a210310b00d01c203d4003489281d00906603404840280b001c0c90b080400c01e00d044078030001180e004c50316414980d60f091303102e2450096220800321000c1046942c0c40d00174140c5040b58542600e2400a00340718108039610f4800392200403980040103022054000d1401a00070704151010048842c85030a0511a1320018100e00140950300c21301482c410000e00d01007810a0591f041031080400c0391816560b1460b08030011242000c0314a1031950605045014400c45a1040308c0c3e0066611400d0b01595031510f1007500a0b04400c1c0c6102c130120b210114001d540c003500e82603400280c0008282010403411400307451a0745101420002041709a0310740080c0d90031a105403a0000314405607100c054011b20590400a400171302041c0009003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 557154388 1250 557153138 557153143
    0xc1804020a03140a020307050d0b0f060c0303101202310f0f0e010c2f0a0b0601120e060c1c05270c011e03020c060c0301050109050303070b040204050c1902 68
    0x445180c0b8803000301c2d20340704d00741d11006a00080300d4102c0012401e00c807090011042c0e400010712031a001e071211a01c960301c1d4000c00d159a11441a2210380da0000091101c10744aa6030401300800b00407a403545002d0b82980007840141c1d04124204541400c4800c0f40640e101e00e9160005c5100c00320002c000700b500c005424006442003100304070303220b4580f03450180800c0040c002c054808041c0da0300d1809001000608459420219414400c000003c06080c441403900f0000801c10354025007201c1103500d0504001000f690310700880b20525070604026402da00d4001074040e42186041c0350240c0c6514400341248144021903260304a241d0801c0148290303070f031210400c030488201100d8002c9100b110b1700b507003583e03940300020010b000403103100c0704640512000c560714400047d1450054a000040305819180c1841503988404405000004200943c0c206152a0050000794080d43c00e045550301d0700242210000c0001e4066901d420029040c46484021502e441d403c00f00c00001d0415a40da0095 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 557155638 1250 557154388 557154401
    0x30209130e07060914061b01050403080124140903010f020f0d110f0306100c0506040308090c030a0312050a06050a080c01031d06270a0809100e090c1804020a03 70
    0x401c50107560b0001c01c82c184514100c405581500c111022080410403d001199000d411030303603101414080c11010700e5100380903c500070340c041c0c3c0c0c40c100030354104504050380b568100803055041a025400c526015004001c3d21088a800c0102c4c513107400c42180407034050100d15206102003840040c080c01e00f4941000944103a421400d4200540049805104281d21410004000c5404244001a4546055841d000c030300c1c002032501c010103481c107070303109440d200041d07508402048880040100941c0c0c100710085185000310000c006c0060180c8028114080c0b003a03040203216124000610981d003182c02c008014403014002c00d14255030790510382e848100c40705031540001c0c00c1198907a0303840e107403251a00701c40c4c1044001d0400c5403501c1c413510804c4003120020440340a400d011001e498541071003906005030080b0700b69a5209a140100440b8010005016043c0b04204615028507120080f4180d446546400364070703075901035054a9102094102c1e0a00e502a00004104422551640024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 557156888 1250 557155638 557155661
    0xc2a060f030f060105030403020703330c17100302120a0206040f1509030b070c1505011d0907031106030c07080f090f030a0521070c0603140703060303080408070303020913 75
    0xd00d0b030341c503000011100381c802614060300691154400b4008200024040c600034140034041890b1807030b005411629204511080c108050343d00c28034184a1900a9018114820943d06828051030005601160424a80406030280f10080300c048d200185c10402d198801c0e40060030a5110b0f60340f450303e024819000e005010190340051108a40e40d40104043d4090340d52104000000d43c1e1030388021a0b550691007000d440c020b000d41c08001d400f080500c2941e001c0c4c41c0ca0074422283c942d00e03040348001e03400054820040e9500641c01000441c0c240031000d22903140480b00c2c503982e925000b4910764103003d08180584801c000080b0210141001c000901d4207040a8540980762100d4100f0151184010740c4045d02d10f82100010780b0b1104149601542c2501d00e04000714106071a5031609407540c442030300040082943e03100c01c0031300c00c0c1d88801442e034485114901400200c0c20341c2da008040c2540a04001d00449021805070209402a010341da0002e00103809225800c8545402d40080c00041050b03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 557158138 1250 557156888 557156911
    0x5010f0e0303010501110a0308041203021c0e070605070c05010c0212061501080a0207050c01030c0507050f1015060512040807020d0c05130b330d021309020c2a060f03 73
    0x40f213106c1d000c0400e50300c0c60181c05490700422651a520349a040100c140c00b0038041550810000c0070111107407400e080c0e1032100460000d1001503060503e03140c4107140c1c2250041c0b10301404810009800014010700303503482883c01e07034440e0b0001e20118000c1d1402c003400300300c82d0041004210380118086180507100000340d0711074031551100c81e504000c9108403040130b00b1030740103240d110500754002d401c14605280546011843c00c00c454698506242811407007040300e41010805140f40324490144000d401815080c1c01c42e0710f07240020141151103000c032080c0ca007014000000e02480500c03801e8580e00e9801520320100341101c3e29181031064200e000c0c03148124410414800d00d241c1600c0350f604442d40151203036860641000ca02111080442403800c07101d04002c580381c01e41c01d100009481c1d8528401d00140c3c50f0050044e0014100407180c0004074014418840204001c1c00052181b01201c88585000c026001082d81c0081e100340b16041160416400607004a801c070403900110b20602c1e24540 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 557159388 1250 557158138 557158157
    0x801170c061303080403060b030d030506030d030c1e0503010e0604020901051e0d020406050903100c1d030111191403040b130215040b0702010207050f060f0a02190f0201030b04141305010f0e0303010501 88
    0x3030a132f08079a000d6540940550103111078002e405d009600420420015007426076504090181c0d45100d07070301e00d01d6650000351011004000c0c20015002c450f802042c200d90960620b0f90100000340180906d689020001c40a07c00c071343c205070030010445507141082007040d03565680f00c080103821a8440801c2c3ca00911070b100c05984401520701c180d6a8441ca20355440298400c0142d55140c0a81d00100e819030655035030703036140040d801e44402400d500c202c0c03841418240d540710718042c004808642d007403d4400c90400070040020541d440269003e0803d00c20407811101c6070010580d041c80320728450a40f40000100416040710706030241492034402d80c00c91344069160001c0c400154014908160440030a110301c02100c00c045025150903055841214000340068402040901749000241e45281180d4070a800355603147c010341da89824151020710070b80b4035282e51000541802030800b91501c140000c00d204002d420b41044211030074040090107000e01014219440c0d5200303218176804107003150f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 557160638 1250 557159388 557159413
    0x1b090601080610030207080f041202031903020c0907021c020102030a06082109030307060c050d0e0f070522052e0b071b0509070804030801170c061303080403060b03 72
    0x80103100d120003901c5030003100560740064020750402141191f00100501c04142c0f04542c01d4060001016044138401584000c0d0042c1400c140c4000d0a00700b10090216008003c6500041da417111010103503403100f015034403500124205000117031180c000d800f03129403602c41c3c0d0f60f0540141d40101460b80c002c00c41c580d034407030404da55022449010020084044601a1890007030000f8028001c0080c0c1600d18142e8581e80d018121200412a800814004540d8000f101d86d28400c1d0a00056140b00038410404808015a5174255500c01e081c4a141150104030f520a09000d2684050781026070500282c14490301080300048120301d040d0003101d41001d4242001015100b03181210480c9040c145030044584a940200d03c0d100c002901d40d2508040000b031580741c1461075407003a0610784e60128941424900180000c00690006200c8011081101d49800020901004e04082103401c0c50b50f903403170900004407098040c0d1010780f0b20103001c100082440030580181c0a00c10307044050314000065803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 557161888 1250 557160638 557160647
    0x1605010818030c060a0606021b1e090f160c110f0a090609090516030c0905040629090108060903090d1406130308090304061727150108060402150f0405031b090601 71
    0x2010151a030110b41c2c0f6401c03c0d81850004a00320400015003500c41d500ad402c045004100305a40310700b21701d58681e0421038560800310082c60302602c107140c08a207009042d11600c0807660100c2c2010300c1080100c01481450707135048040c10051001000500041d5540c3ea8018002c05032283d00350380c07500400103c2c1c00e01d00c41d000050002e07203602c040b441205506003803902000f44001401124000c5e80c69004d440c0c2501c580c40c0381e903108103054580c003401704102e40c140312400304103a10560169200300d0a200454a0100c10ba95005505458005800c03500341841c00c841c060790325041c50203001b0002800205040003440d00541402515075170901d85615819030fa9a2003584901000150016024400c503d40030b011903812480e030301c0d040f0080290b5401e058648900b44c52807032465034840f0800d020001020b280d25801040300741b0150000d46000e401060070440011902119034000082103088612600d05560103010058112440110303111030fa010040e800601d4588242e807000300045081d0b105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 557163138 1250 557161888 557161903
    0x41b020709060308030117030d060b0406110706120209130c050405180105010c150e07140a08010212130221060a0f09210e0409060903030b01021605010818030c060a060602 75
    0x81001360307145a1800c8001c909132005e40303615000d2400300304005820b030100307801100003804c0d040716102d551394603044001c0d14940401207092120b4021450130409a074100c2c000c902803d090301c4001d651060401c0002e813818240b02420102203140400307207041075600c1405081171320826140010b020036040e034408100c22007403081034001102503401e0340020380309407c07818401200e40d001184055031294614108031494200c100c45d002d10079030341c145a140c8108445c0041044d00000c51a14249549420f02c14400900e0110070400950180302151031f060030420300b003c40004103040c0404181070072911110182c441c00c0e8114140f00e0400081b030400d105444045501100c140b1488a040030325a4107035494030212340610001d504120aa62a54050040720328842d840000714404d00b45800340440d00140344040c115440a25000300800103521300a05450003404d0600943e51a03d031607000c51003520600480700d010200d00b0540311440000c00f1030149000c0da030306029107900c400049a0f034454 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 557164388 1250 557163138 557163143
    0xf0616110708070e18120d1b0c030e060a0c0f0c0f18052202010f031e0603061a0a0317190210050c0a05040e060f04060806190510030204020315041b0207090603 70
    0x400030092440c0c404070f8000300741c907d403a40004030750040505001e055000701100500007080300a0358010816512151030302014000300c07140360809244250051090410b240010101c041800c8210103006030b4102403c02030040060548020361615000703a00c1c01076810301e4002160600010032801c2d922000140649042d50044000400440d0011a0440c501056840905a8904035500344d03200e1480b103074050042000002c00c0052440c0391940440303080a02c040154080240c40174260b5440c041c0d11030481c0c0e0411711244401c1050f5500601038400d4840815030300c101d0140300341c0d0280c0c0200340c20340503503440c1000304203a0341d6100e0b102e0090f20400c0d12000000780100802c5c0186004024108c0d0407030809000400d1820b00c00c00424219682a00300328000e5200340100052710b0203000b0b982c000100180c41c240300600b0b00d004a030502c100c00c0c0c08000d00c1703190040005008400c507409810380e000e000030028806424141c2486002500050079030300140125000401c22070280d00070341040703031b070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 557165638 1250 557164388 557164393
    0x82701080c1809070c0c0b1603050f0f030109090b0f0408030712090b0a0e07060f0c15021204150e0109050a060c0908070906090b01020f0616110708070e18 68
    0x90300d0000652142d40040c04030706000c1c59101441d1200d4451400040c451442611001212205c44c02d100035032268591000821035020841003400c0c821003505441502e9141c145591a20f6610303608403054018010280259030011000081280480d004110f00f14011916103501e921690780c08074401d0780440d005002c50301d0800110301c0c0c8500c10200703410703075aa1620340010750b05001e03074410031001c600342c1d0075905450301c502280c40d56110a011140080ca07132420a07209046c802d003400303004110300c00d9000d08880041c001c1030307503894a550125241101224141200391500b45000395045103120b160040c510716003102154006414410350310b025402000410200034a83d07101c50140c20042440010400000e2000849401c2001054084d00318803102040e43d601305043c40040319100e405540c119070000d603c01a070740704003040703c0e030b0400c101c10314095060414507010303901c01e801760451628034454003100141006000c210001615484004440251240e25011040d11180380c0d001c2e00b6074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 557166888 1250 557165638 557165641
    0xa0b0906090606130506040902092706090a020c190506100b0f03130203030f030421051c1b1809090209070c230c1801080712020604030501020708270108 67
    0x18a4500d014040e4139000700e824a0f0299129004107070a500540e03c4141c085c1d4001c540d90b103903454082c1c40500c1d4a4a624200d42501d21041d002e19005400603181d07500918900001c103400d10400d40440c1d108441c903204980b420301c00c0172142c07207204814020940c5ca901940c404913080920ba07807544400c8075000180281060808041034104d9800540b1584074590407480e48001030303e041c07000c0d2140c5480701d040d60741c1f07031b240904005058020341c9044844540c550b62284507142e4100007a40c84481da680d4440c80c4001301d40d84d1140041441c40308042c443c040c0144d943c1095a03100c85115407000302505100440da60380c0f00d40000381e502d1640003d60051295000400c064884c1c80c4001c001d602410203041c800340b0001c084213280465080040c05a00070180d9804c560401c0103005181d65411094150781d580b528500b1a143d11280c062600f6000041d981c03601550340d12816600a10380100085550343c0c982d00e403408403a072080c0072800f1200020980344d503072842a420345012a101c1078440c04890f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 557168138 1250 557166888 557166901
    0x3021006080f03041a040f030b0f0606090d0305090f03060a09030e030607020c0d05210a020606010c1e0203030c0105010608061203160308040f0609050c040b06070f02010c020307030b0c030a0b090609 87
    0x5c11503031182070482e9038018800042c40c0708103004184003c50185158030200c0c140064544480c2000810290248000304142200380d1610103a1010f80b94061410b81e454003001700004072030000b21a01d2a601d8890101801403030341d242e0b844480b04500c030381c58020404100c00107142e12458201d0b05a0096002801e00c918a03003410980319a056204009907645002d401d4580c10003600360100c11300f541030300841c44049a60301000384917001102401d01600c1c0308900c0e90341e411034100c030701400841d03010950404421520308206030b45c40255010020301c43c175a1102c40050260b4011142148034901d5891200070640000c001c0721b00e468403c111400c184215902d080e03603025400340c0300702e5010441615010100e6107a11a20f00503500c280060520f141a90081009035501c480c00944510010001c80c000240200c3c0c981b9070f800d90a08140c00460742500009081c010107610203043e040c0f41200700b125aa180c00000c500c62109a042005100662028000f1f0301c1c0c002c903840c50300700602c54007280030f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 557169388 1250 557168138 557168159
    0xb04030204020f1903020406170402091f03020312090301140415051b0d051009060f05131b090e101508040c0b121e0f070507060b0d03021006080f0304 66
    0x30b464015010f410b141481034106113403070b1038040c000c100010b80c1c041703401e00c0039a90050f07c00701d201d11003080030f01040c241500051101c0601400c581c04250380050030000f001d16050b9104d000710b40060a0754000d401c0380302c0010a60307100b071640a04c03a5103807031031451400443c100c3c2c2c03500660b00700807140f0304070041d00084002444050300440b4000c401c90146000034030150003c0c500c0400c4c00700c01291908202d05c2007440038a543d0802521181804400c0c0a10301c5024090000c0381c2c81218403039008841030300300100429850401d0748007811040c0c00c0215440d048605007003201c0c030702124100c0c40e035108240801c460f1001d000b6400780d00c010142d01c00e121481600c400360031500440641e072100360384002c114059400780109109020451080100c40e607003610f20340c0043c403181c180e070a01906d0101013000b0b500c40c009103240c0a00c400490701106200c0154404005080047c211091500702d90030040d50307411036500756002c4e66003002e2010802d1640851004d100ba85194010741c00c0900b031032141c45 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 557170638 1250 557169388 557169397
    0x901080615011806050d140912070213051e010b1201030219090f0b0307120314030a0605090f01181407050a11070f05030f071508090a120806030c04060b0403020402 72
    0x30b0400001d18281d40b108486103440000802c4291a802d5544203010f250302d080c0e0384500001041684a041045042d00001c10081410f21300810302595900140c400203180d0524481044d04891401d401c10000e040d8028001d0001d00c1484c14407030445e070b42d801c16822203103c0c80d20680072030f408400040006040120009079035a60320a2030080103500c0b20000301c1111580d4299100d05078442114011900f01840300c07601a000309206184880210346018000c02c031400000c0211080010000c0d41c0f07040c6a620030005080018154401801c1c41155a01140d1080c002c441032481001c0100c4014416032260907025035402c0d106e800b6a40d01c2c0c40085d16650006840d002c02d002c980b50039205222401d10406026065a22000756820b0502c01491b01d005004001500300e9809400144503503011001420940d81d140e02e070400c82551455101400c040c440c0350300420800c0326210741000a90072840d038602c912025000c5a994020060400003560110311800e4040070040000b070016090030340092 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 557171888 1250 557170638 557170681
    0x90509160e45010c0f0806060f0a0c12020601300831080705091005041d0307030c17090d080705011d101b0503060f0118030c0905010509010806 63
    0x100c800410201c180126007002c80040603551602c54400e450703003014204004035070a240a45007803a02a01003809842044052004400c2c0400d40035161841200c14800165114003ca84203102a0700302955851007802004030b04001003030054000c82c040d01c5088604034205101514402603500d03081ca850f8041021040261014080010388521129442132042d000e2304642c50410b142801d51400c020481e041203224410708030a0002410b620200ca00550b0f800301c0300005d04c13031100d28611a03038440b0903410606501010514500385a000b035240401c190284591603c90051282100001c0c802c1c894605d6214a4400d03511000c1a108006000440d20581c0000340201c0d5048150324000030b80bc00c0041c542c0c0c08428032550806a9019a0000c40c1c52100c48a44400d81c1c4407010301603000040a040c0034240503490070905038490b44100613019000d0048000c41502c07410101040c0c4414060b199016081c04000170b06410314040417070403147d50202500f416241d00c03018000319800c00c1c008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 557173138 1250 557171888 557171971
    0x10804020420070210020d08150f090405030d0608030f04060534050c010302070210080702010f020c070f0e04080a0c0507030222050901060609061206090509160e 71
    0x1034030b88080780501228100c01080c2541d11064030707104001c80c20210180030801c64022002c2030150307035004003000c1d81081014011280101114010402c4c40819006055006c5004070a01051113400700c010540c405544005014090b100c5c0310496a900c5000310080c0c090310304102c1080ac041c81180605096030f004d885000c0c0064000ea10040224007400f4000d10fa13160f400c0780c0c0300030008104288040034400f8202941001a150001144222810104402d2124000000c0e00c40c1c0c0c0700f91310000c44100342c21000c5407121000503003e9511415401100c07503154180d8004201c40b02c02d031488030301c956408240140342c649406800c46409400160843e8144581c2c0c01c00301c016610f0302c1614034048198802880302c07150040a03641650790260103403903aa40b4000040c400d4a034070400031810707204079040049541e040384104c0801044198880c100341c6103000c0c2400099440458010040035005205010040d20f4100c8404111000c0d100311000042440510b11911614100c030048660300762070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 557174388 1250 557173138 557173151
    0xa051e100b1605010903030e160b0301032301050103030806130e0601090b0d06060b030a0f02070b220515010501080106021f09212c01080609060a181e0209030c0108040204 75
    0xf0780c507081d1805510103e0200b0740303c000c000c0c2a42010800401808a40620b5948103491b212081d5041d11060102400c00304962102e148450028107404815100f100002c12840da920305006242101c1901c1c0c0920481c44400c84500380f1220b4040c1c900c41d25055401342c42164a8020080014a81c910744180c012401e818210085802ca114803030081404291042d074038138060081c482201c20609008403894818006403003c60710b4515042d071b2095221445c000f040c0e000c03108401c00d2401c500001481c502c101c10450103588503480010741201c200384c88058050340c0712a030580c2c0310804241041000760410303031412605500c5030010848503000e450301d40c80e542142a0060b91107070345069900d022070503002d29086250103903c03007544400e0900001501da960054002401540b0207072420b8805c0400d1408601155a2584190014266a0382c0004c3c21102c8089000142400f0521b108814039015400c2c0036103c0d088c002c403900b1020040c05050701c105038100644181078054001d0780c0043c1d6608 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 557175638 1250 557174388 557174393
    0x1b010f2313031704050708010501051c02010c0809030a060e1c021207030c120e030c010e01140c0709020a1e021609050a110c010f0605031605100c0204050a051e100b16 73
    0x105280e000354091702c050a001401c001c48a13003590f5042c2d03c114061118920040800d50006411103000b03682483c00588108241c2008503443c0580a28140d041c00355a2154040007442c0e88458400a881000d45d451400e07183c7c905110400782c45005000368001402d680c215142c030800a25545200b410204c12301380e071a0701d07200d40400403903010300b011444800b0070005900d07040241d2860400d0034039127900c640c89101d0000b8a1001c404201d200c0066002ca10409422130a210b00006040440400c40d00c422005800034044001c2c1540c1200c2041c441900f100e040f48085641407540005260b03000007039141980000003400d008041078000c6594040383c070102080c090042c191012401c0c00450400555890201103c04582c4924400d6108100100254510170030710403c0321411100690515030303800050b82e03042d01c2c07001d000798024900303010440b4003c0310f41d1003580140080c07580810749405a01e205001510280c82c1c20b070a00000b94010801081080c00816200007050040d181145056 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 557176888 1250 557175638 557175677
    0xc120301053d0f120606022a03250918080919062f060a091e0b1005010305070804020f19091b091202060f1b010f231303 53
    0xc00b18000516100300014096482003507078076a00c00c1920b003080310510348100070f5540c8072115459030340c0c02c19031551701072940ca0540c80d07050070100c0617080c0c405584024000400741206a80300c141019903031940031890200f0b9204100300410308416070003084580780c6814006c0e41040c84040d41c058081d01c124414110354603010b4009000702d40390204041c5800c0d800445c10361590201d42041200b106100c1300803500001c040c3e400011480001408500e1801d0040c0025451040c1044021094a90b2810080f00c404064442c2c500c25101c1c0340002c0e1210011000d0318411345216000072040d8010078054640490a0410198028048051001d0001400c0944900c55000344502946c0302170001150141c002801c2c6800628a08854031500b400c00304070603540c2d4810040d01945011032004294512a0308480d000c0b0340c2441980b111400d43d01086d40a45109403071500d0351400e141e4045030341000f2444c8240b01c190160003590f030641c0c0c2c0300d8204a054046000030340c200001404180c1018841 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 557178138 1250 557176888 557176999
    0x60e210307030903171611040e030f0d062c090c0307080606040c09030b0703020f1308030c0f03040506250b0420010c020a03031d12030c12030105 64
    0x3a26540c0c2c4080c03071801c24407005c00c0000f080600b01c1d0b02c2007140c0408010590b211804c040d6000c2c5d186484c007101000858000e00c403210190001d807100280307030307181c00c000d43e8040c2c00c20f4034032440b06121490b110250343c0f194403110004014030003814000f2110f44105228407540c000c605204484140200d0400603142401591042c1041c0d00048144140f504060198181100c00c60800715040e40c9181d03110060190700401001c105a40030840f505151030b62011548140e058000450b90191038100064680c1d105e0f03003000b0b24901c00d42035195031181002c0251400c40b40002c06c4281444101d88000c01d2184210000c0360304502001d007100c0000301e4812105008038020000c00407900d003120149d000c8181007102c00781c14480260358080040c0e42c1e001590047c0d03a410301d0001d6003140304d403089003140201009a07951001e1076102019813004008060000c0b5401a41110402e00c00b080203907100303110a0250030b4104010300b02c00142e80b81c6d04155445ea01c0d01166100c10280322401d0440b0780c00d504e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 557179388 1250 557178138 557178143
    0x140114040f0303120b0607030f0903060504080903060703061a0703090305070f03151413020d021f02010b0415090207020a0b0d050a060e27100e1015060e210307 70
    0x2a001c0003071050660091194031400764401007007010100103c000392140c060010000c040000d41c1d10241010303485141c5482c02554084010700040c1490314014585800c41e821541c004d109841c0000d1745c052003809518100c1d0204c2c01d0660030401c6c03481c1c0fa004298803401080d41882840c020000004404020020050440410030f0301018254a03101c000f80a0042e0040001810803002c0c1042c51009103046812400c0106061110b045603c08162007412043c0e020754824441040000d013012f190703042a0002c40c06a0003040301c035442c0c03400c1200700c0300b0303450249a5000c003100003446204075581c000c142d22400200f01440c85a520034595007a9401444201c0c001034179201408075225103809200b016000da40b852800038541021189800d018210a4004500410400070101c40c014050305200c100e1ba41418405400d40c40c0c861982e824100c50140320a80c5440700030008641000f90130740035070327130a6651003242e425aa402c02014000d60004105048070141d106c86616070104002d00b5940e2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557180638 1250 557179388 557179409
    0xf07090b0c010f1508101a031510080a0f1b0b070609020a050103090b0f04020a050607080c070602060103082d04060c110906060904231e0c0a050414011404 68
    0x400807002001503d444107413070001c5403201903052000c1200030581803902d00030030400244152000c0745144440300340c0d00310f042d054007900c0c250321410701521760314a10421380101035010113942c84600c00d03510100b221000c0c029000781e2044000080c0c523510005280d00040910715612a1107031b41c030300d0b610341c00403d0454445a0790349a040860130303c2d0880714010318003403d0401207140c460b03c807400e4006000b002c0000300c030b00ea40001002c551310b20501202620000d030846031240c0d080d01c2e1a10071584820750440c9940f00b40640003032811b100140880c1603d912641d43d5041c40e00740710520100d1202003844461842c1300e07d0100c5c00144100001d80001d14146e641c00142410780e0408042105006800d14000c4201c0020058644c50300001c4801008050740c00181840d0541741da280944070980799044a58440700a00c13150b90150402082e07040200d030318240603a02d0344003145003540718642c1000e02246040c08200000904005848010001070402c02c0c1d8400481c040d4543c1c40d40160000603010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557181888 1250 557180638 557180651
    0xf1f0501144005010903020607050a0b0a0209031903050a050d091203050a150f06050c0c1801150201021603030b061c02180303090607020906190305070e0603150f07090b0c01 76
    0x451103050100d07103403580141680b5424140000e0000900b404003a0152038000750100401c00c04200304000c07250004450416428070400100c080c2d0700c02c0b1b100074840d01c0394003403a0340a060304080c007140e0603616468880c030302030001200741c40a42040040602c46540d40210401044000e1317450401c21403c0d80c1c2c002a680b030034001d604120750702c041c079691040f007400c00e040c032191807100c0090090b0390181c01c01ca0340b5589901415403402040500c0980c00c0417201500031800d0880c1a07029051380e48100c41c5140b140d4006c02c08234202c0c0079102c0c42c0c25200d2840c4844801084c0a5407000d07007940d1002d80340c1490508280000c046114900440c0c0020981c00102480400401c3c402e0381c50328003045000d03510f0f00d000745001401d18021440c01078442d4400c0c0700811401c0d039407099240d4510f0500c23000760064542d2410032039203405162240040c3c1032545000105c60f4130f000309034485200c072005003140700c60316402404500c40c1b400805070340c2030190b0302c1004200e548215001d482288401000807494 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557183138 1250 557181888 557181967
    0x60d0605190513170c0102040801180611070803060d060b040e070608011205060114120a060e0d080105090a0b03160f05030f01140a0908210f1f050114 66
    0x85980050030702a0010307204812000098039500d00d001404091304106468a40e513140d480c0c0240715503801141690701c0c15034402000c2c014000c3d0812458040c1c4400c00c07018003110030b140040d100d48000100308060030400104075290810940c40b2a5025850009401c40541b01240488000070b00804840e806613104005480d48409014098803411440b0400c3d8402d60b076503981d55038018003690381100c654441009a0707454004e4a04001d40c4450210340045e141d6042c554004d084144148956004901c00218024013800c169070403500d020b4491800c5a0390140484004d04040c0a034039031601442d41c85142551010084801038513180603085400341c03502040610744030301103090701426410000d203841286490b94002d903228880c004042180360507844c040c030003407060f500750382c12002407810490324005201c40c002c1e01ca1507403c1d41601a548400c17021038a80141f80c2c00c1c400001c1021041803103030b5407145082680c56066003a22605040c4036040f07403405044107000040519107909010440d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557184388 1250 557183138 557183141
    0x1707060501170f0c1507020d080307050c0607030204030c0509060a0e01090e07080a02330403140c0a080c0f01030603050607020307120e0a0e07110105070206070f26060d060519 77
    0x82440f0f0b100078a10040038801181003c070020075002e007441d10103d138580541d00c0b6140e003800c500303900040042c0d40340b5200c0d02c0036241d81c0190009410a1103580c00050202c3d01070720845045e00e4110106180041c503000130041118002000c581c1c000708440000141d204580f1005806450003c40102c0d80c60101e11969282c08121b03030043c036455114140d900c0160711742008a0300b0701500b03440c0c04240b5070740342c540c0d104040301200c038928014140094000240a411884508210021419500040f202c00d08110200005005604a540008100815a2501c84100c00e4140c0040c140490400d030f40e41c503094103110045030044d01680002034175608100380e4007010305d14554241450360064103400007242c0394051b14095040203404010116100c40e02588010003285020300082c00240380c540d00003511808280c1d43d40d00400d2402c01e6111005000d640c103070300104201c3c05110b81180101010080c1e580c400782a080d01300240b4056040821201c1c042c83d4880c3d40741808103090390444000250 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557185638 1250 557184388 557184403
    0x606020f0106050f0907021e030a080601050a120b0f030a08120112080a2003070501060e070f022112010303020309010e04020906030f040c12050c0406140904170706050117 75
    0x1040e40b510000f4481030742c94848010058005841040040c1e80307203030050b490205520710110380c0e0301207004519400c101c001300034000c580155841e8005030702c501c1e0054545008070800c18001c0348c1180940050ba43c00395200d110b8040b001403100b200d0081031004039042c0102e02205035021100041c42140010369004e040740100740f9400040072402064858008500a5003038410401c00104002c982c1c075080080140e2100245805990361f81040e440d00c40d00900c0300307100b41e00c0501c44480c0020030710360048246500840c3c440c0c01901c2400c41ca10138640019001040485608000f801616801d404245500c6e01171803003900210303940d401600000d80b0042075000c1b0706200780d00401110b212a21a6000c0c1c80c1c0000091016a44948980c605401e003092550405520318040c03603020000d1000008200004001c01d542c1040b0316500d07200054100c020050318103810cc0845404140007810b01c6080191418008410034205030346556030504bcbe81082e4494a612080341c071124041000500610 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557186888 1250 557185638 557185663
    0x60105010908210403080c0d0306050102030313060e03041e0e10030206120414060712110c0c01140d0f0912210b0f030a030f110604020120100f060602 66
    0x103000701d141c001c0786642c910450034404041c0514403c9100407840b8a016940610340c80f03035800342c8901450010994075105918180d0000303040c4880018554001300469010b000c1c1d030941c6012032516500d44201905480d1441e2100d4481040001401740c03000c4840c490b8803500c001c1203075010303180c1008074840c01d8024000040c42e4000712000c100507510801111a4460b40c21140f0041e070390345041c00b546480480045440350f0168004101c95030703074040c00b1003119441c081010014656004803100c0b050091902886440d4041d140c1d8694a40c02600c1c0b0000265920714543d00d0441d401e0f51100c1682e40c0c081041c40362545601080041100a2020f9060b03e0764520b03001010040009408050135503c01201001c60f0343e0b41003005081e00c0d8408009003090018045451103c1d807460f0062010302002c00034800114144c80c4000c49130404244140030700e0b016510b45504800c02c0120f54084640168010381c0b91041c101254000d010754000d0382c8065081c01c8000420030302d0914040d05095000025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557188138 1250 557186888 557186897
    0x210e040f05010e241f1e0f11011b03020c0d030509120903100603031e050705070e1506122208071b1502060601031b0813060e030d020c100e06070804030216061106010501 74
    0x811514961009105460380018623100209400d1805003070700400301441c0c081e0b0203107111034010a81a4040c0c0007404860090411180008804a400c408884055a0300e2201e070f04583c0c258401034048402920016100500b61840584c400083c4021540740354001c42c04145020074500c54154201d009800030402c90404628292442d80e2301b60f160784850040209680031007000c80c9111a904114103a9140b01814181d92800040325421845008480d84080ca1519018803018440c03d182502007050b44050110300f0001d40d0b5848100d203d80c01c0a4106480450398800144040d103640c0306c14a40601c4d801808140c1840030005003a5410240001c002e1490b45c01461102b580c025203566010f14411504406180700d85400b41c09003079111003039002880045440c3c04c441e005940181146100c14040b11900320611110074141c0d11004030100380c42d0000000600094000d0880c1a80b00d80310348143c48528459511544142c051500454002030b55103020f500407031000c1203000d0151400f400c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557189388 1250 557188138 557188187
    0x130306140604020703050921031b0f0f120304060f02070809010f1107060804150c0216050d031407060b0310020705010e1216210e040f05010e241f 64
    0x401400c144a00d1490a0040208095607584180c1c1c008c01100c407101707081e054a81d25851400402c4450303c445107064218010204150305e00d03400024540c03207162421000e883d010820001101d442d800040094942940325004003000144610040104078440c10000340c40b0021600010f0030766845411000502001d2010101c8001000484900701c0d078a03480d022031203590340e1070b100c4000001502003070324282c20990b210b0315594001c50303d1000d24850010a84003d5501d6040011403803810101070f02165008400300c0384144840c0041c03c00b68051100429101c1346000842d183c0782c01c1c0f0802044295011032544c04102080c040d18070140c070424010152171786003c815039654421201c445090a41c107c0740841004860505e50340ba00c07100c0304a00400804204005c1e1481d000202040d01c56450444100446025885840c1c1658843c400e0000c01d0b5456500001002d550000c41940344010180840c1c4a642d8004d8503400203040c00c0440c080b06260780c2c0002e0040da910941e0f17107030844d44540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557190638 1250 557189388 557189393
    0x301061710210b011215061d0408070203070b03011a0909150109080f0601060906301113051002030408060f100513090b0106050a170601051303061406040207 69
    0x600306441c8020086a042e4500c1400809002c212460080c81800b5080001920000c2e80c2da440b65198090705141c410380004242c500202c804d9802450307950410880c0303411154010902d001c1d4010300c20002c09203000f211b500080e1800500e54400d003e21040000144410320000d008000e54540c3e0190080c201818400001d48140c0300034101000c4003503c484021117680b0800c0c02400030240c11007500d0200108400b0951960802d0141c103021030403031900002d00380d200300035800750b210754215241c43c179101c3c2c1103074036500d400d80b0043c1c911000d80f200c041d8209503e402c00105442c2402c6514070321030625102c00c0c45142e52419000300190740003840100618400825503e91000c03544100c09119510711070485003500301c540002e60070840c40003418220300c5d415485050744034046c004c81545aa65803e0403030b0346204601d1a0780c0001e0500145105000140c60b91a401210505140c2d003000300504485842c10003540c0107944840d160000c0d03a540e61000529141c101c40d0a6400707518010903034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557191888 1250 557190638 557190661
    0x24010306080304140d0b04050d020c100c0b06031e030414090403020312060301020708071b09150308030a061a040e01060e0f0609030a0501020f0705010501080a0215030705070609030503010617 84
    0x10310032400d5200e0207007042e0043d5175074103500c0c3c12807a9000c2c0e10034845003010b0402c103990b80c01060505002d8800c0021080341c0385405003401287c54034039030321149180c400b955100070000c1d024202d2901071140c0c1c0c1c02d078030349410171034100c4141000d14001140c075946403241d400c11002300312140c107009119200500c0046540130040300e80c20506c0703005650300c640703903580464020320800308081e10000b804507200b820010002190f540038403081c44072014181d1164115821112104180400d03441010700c1000040c4001c0091640040064000100390b5503a071204483c1786800d805035209441e0004041c041c0c0c118050103280074084901e06441c011018801142c515282c81d500588038000105901940d50307405c100300c4400c903034040700a648643c891114240d03c0d4100344000c582c2942404000b04910344002051801d503030300280840d078075000da180301404952001c1c1500381009820003854021410a02624103070303620964a43c1d03625850b240d4000c020803141c4810b031040013295800c1c0030301d100c5c0300c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557193138 1250 557191888 557191897
    0x90507050a0f170712060c0e03120313020414130317060f060705030c10020d060b09100f170c0d181101030b0415120c080a0c0e1e240103060803 63
    0x100c2c0074140c2c03100c100f1404540b4100c60751384168038142040c2a04001c02c5101c0d0060042e4510603204d010109000c0c10405454500c50b9449600b120001e1001540644e4104108903007180068400500d0318100140320030107120440359410030300c5c0c4d0859940b0806600c2504180b802c07007513000500c882c0c140a000911500314107001d491090b107001c501030f424002c0a008403960354541038112119884604401c0000e5003000c903050302841c0ca0304000058064080007112003400004003841b0300c038034014009580000181e29207004200d0801400e1a003408450b820b05c0c085c100400e1a00d865000c0d0700d40600075510406846500b4030410b41070b04002441c481e8041d00001c0d0f0900340450b9003100c5002240082800c54200d48244401c601c000404105064620b03c1a078050003500071000e482d08444e03070f13903954104c00080915000000811205060181094002550b0000e6440c0000c0b10102d11001030010350300e1580d015050644a03810141c01e0001080c0c6174000e09060011903e482c14003510f1b8044d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557194244 1106 557193138 557193149
    0x1206090a0303110903072903071206060e01020c041109030a080702040c0807050f090609180f010f0503070e06131e0b01030513031d0405070201090507050a0f 69
    0x3c3c25040f80ca5540c001350080440500c1c00c4200e00d80751f400c504050312401c501003110580c03001084015802989180e4408000301018100d100031524680d1220b801d00ac40007140003116600070403041c41c3c029007141d00141144d110a0032031100d10031610801d905004400d5042d08010482d006800868000c2d901003000d131030700400540703451340140c9000002c18818041101040300c3e6800504e0140f41c040c0503035080c030300410041090f1103983c0680ca58582401c0c020002d550b41601d1249004040800e4183c0360107141c080440d4880ca00e40c000c19800c0c802c03040018449440b01c01041c511402103840810448400c0c10781c18208089071403c0405031030a084003807940350301c24050309009000b506a081d00d07007001c560f010340d60040031541c0300340c40f0544018422455515881007522607501c9400218840c44940341042c207000c0c15070003440c41101100b10510901032845403d00550300d = true := by decide +kernel

theorem cover : BRFrame.Cov 557014388 557194244 := by
  have h0 := BRFrame.cov_init 557014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557014388 ≤ n) (h2 : n < 557194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
