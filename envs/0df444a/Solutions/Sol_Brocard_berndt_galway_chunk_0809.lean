-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0809
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:55:37.25656+00:00
-- url     : https://prove2.me/submissions/388c35a1-ebc6-4681-aed1-223183aa4b90

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 145323741 ≤ n < 145503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 145324991 1250 145323741 145323743
    0x4030807080604330f060507050105060301090f080a02070801050f0403020c01030501031101050906040e09030a0807020d0c03080901140106020102130e0103080d05100b0703020106051011060a0b01020109050f15070c 94
    0x9549055008402c0b000c40f0101204080c413511540356035107a400c1c00206059110f00d00103400890702e04100002806510f802c91402c60003030081d80c2160726106038600f000c800041031442d000480301c103a14000d104050081003044000c0001380b0f0700644860121004660450042c055140d221045600911801c4c0c140c0c0d4002440b002245048001501c02d90701416407550b2101c4248000a1000e02d0031048602c00c6144038080d603194001888042c1c044800542840255000000714005c460361150084110a4242c40d0007061078458500b8180107058081d285003500c0840f40c00803500d550150010804103a2101e1000c01246c0d9503200c2c21821340c0c2c00c2c00002c1100c0d5081004110749040f941180fa0030040720321415075850b83c0c030401e0702400ea0150070b085016035140c0d402003216290200803008264000c2c1000c01050318a81d904a880d030000030424184280e07191491600369100354410400c05034480200e44401c1c0c0f42c0c0310714581d1104030f440814018000074000844583c450095440c500b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 145326241 1250 145324991 145325021
    0x12040b07081e060406050d0614010b0f09040f090209041209060905061b070e070804050606010c0b19180308040c0f050a030803060f04020d02130506030603071412030304030807080604 80
    0x610702103100b141003a44007500060340a9100c1070041600e90b03a04404030711041c41884002030107544d21894004611059001e284000401c2c0040121056508100d4891242c1240c0000740301c02903910840050101090280d000706400003000b041205d049007610000b482031716080386265660f001183e92941e14010300d90000000d0208118050341d268501340390301990015504401d807500d81390840050101c4101c000651160f0621003482001c0c0450740c1c000f802880d220465108613200c840c014900a401520b000500c00c1144540800c03c4c0c0c4641400c2c0d20b5841110880341c46070800400c00c010a03070301aa01e60040391000a0641850a0b079070302100d5010300300d040c0d09442c586800300c1980008000700d4000025079640c031455501c920003407140711b0180384010f840da1810002481c0340307051a0400c6000f62810018421580e074002001e10031182c9020078112400704080c0840e00d2006400440d203900e00c804030a0004240e0040c905520418150361003550795a550000c11040d120040c04c00e2490f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 145327491 1250 145326241 145326271
    0x30f0a0b10170414010c050a030f0203040206030103030503060d050607180806150d03050c0a230c011b0507030b0f090d0516060506061e1e12161412040b0708 69
    0x12210200384543c0140221407902c682e100c1d40c0031040c00d480401140c10002480021034504036130b050b1040309070750000408114214034080e40418190700c0b060002406012012001542542d5000030b0945d10941c001709036041c5080c00c0c0700c0513051117618800d584c0c8482c2d0080300802c11050025006229404e111903149090021605004215801d840700307408002042001c8d07a5841e000300300c100d504503c80c906013014600420f0081c204460000e91090342504045174040441e070b8801f9400300c1c4061520078208100c8020305e4940e2809000e944000d243d14814000c000d4400f04200c28903110b50b0008064800b0031805000894291081880703510820b00d031050540c0108910b5804903520403130141400e0300c0c00c003455600c2e0384546050300c0b10012803c0c00040344a140a802e0b034200c1040129000e030507050805510b851103415000030000c0c04441e00c1b10000402807071040e51141242001d19007100d030307100000160000b102204440c2907440c1100368011070311030380c821100a44a60302240104203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 145328741 1250 145327491 145327517
    0x61c0c03080318060c0a0914010e101209060204050901050303041d04030c1a01080c01030c0215090106031407050102060c0903060411030708030d0510050d08030109020a0311030f0a0b10 81
    0x1c1d50700b02410326078000344038069860000c0c9007000707058050f0f00d072181a03d48400110200401e44420742e0441c4034410b0020302d10100590300421b26184260b805c40313585001803400304080301c1c8901d40c03021244000d410070080e6003d0041035401003003980e1342030750b48410320b0b0380761401d140c2d03244902d200721000200781841d40e200440c50800610741041c441e14010403c0da9440d02d4400e20314000c410710200d01c2e01e821004100c926004c001c070b08503121003030806020249113030030003940710750200c8841c070b84c2d4409030342c005030071400c080d8880700103103038068000441803104030029680d598060094038054401d20000c1194600d040045e5081003170020000c103803583c0c40d03680d40310a0400c01518260103120301c02000c83c4c540c20500107001d29400c0c1840025041c6005900c03814105600d0344546e001c1c0d0a80445031000c20307000c5d2f04480c1500c0b012000542c1c2c1d04a031270000c40003046140f911034a100740c040180301d02d01c40402c903003900541c1da41805000d5a070340b65040014150800c020000400d130031101c4c9003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 145329991 1250 145328741 145328753
    0x60c030405100302074d2e14090402030a0c0e040c2304052706090103020f060a020709110a17010506030f15060d0e0607080f15010c1203050f25030f021c05061c0c03 72
    0x141c001408e03085110b0030070303580c003010400741d0300292010440303243c5501203090b040358000d08005d1403045c11203007031107620f162403006821805a10400c0a0140510581d001c9801110b0121030080401520402400c040f0202d41d15006204902c0c2400c0b084204000c03400340e25024203441d0680350028a03107101101c1c1941008629407001d2010000e5000b220000151400203100e980901000342c04050303545c0301084002002c0d004481c2013264468043d00040c825078a0700000e407940503c041c5902641600d90260f5a103145112080903a400500014124100c2505800070012041103004689141c0c032000c1b000c1e60252021112842e410803544000313401140384512076011180c041c10901c0039a2020303241c81c04941241a01100407a850b4020300045004000384d4582c090790360320511441c0840121000038070210a15a0b0007015282c0021305020012517044952030400c03100549802210700b171500e07020308010ac508900c280c50f5179a40c4003400f00701c604042c000c140d2000a04581d581076964507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 145331241 1250 145329991 145330007
    0xb0108010909020d05011a03070504180602090a08030406170c0306011707030906020304140f0d05030112110612012405030c0d0b060c030405100302074d2e 68
    0x50342d0004541c04104080781c020702ca80301903000e121521803100c1fa25281810326140c3c041e8425400340b032410b04050f4000040d0760711900302c42d5102c080540d686540310002110648641c002001c0e50000282c006038070394200040041170306010000c04820341d28480b07040010b01084540034042480c3d21031800c0c240f4a0100f0040e4003c555041c002154545612400c040703800444049801c620000802c03104200100100c0d159040307040e0003803403d1012444010140c0c0010300c81e24180402003d101010010103041c9062015000307001603464040303d079502d10718402c003031013006500e00030800c52400e00c80e28440c90700d4000041d503d82610b540c4070301c00c204119910003e550230059542d5a034120207982c8030f0b402000c818500c0310042d40c03070b0b80c02c0c04100700c25804403000c0306050510400025001500f80c025448400134492072208042214150fa4000801c540424400343d1181c0000401c14113800c5107040007140e0103a5a1054610104c809007103c544400410402c0303081d02000151140e100b0014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 145332491 1250 145331241 145331243
    0xb1c020405070219110f03070303091a12070206150a0b0a05130302030703050a060507090312030203090f1e160303140f091e1f050405061b0610180b0108010909 70
    0x4660307491914460942000300210b0b41120030354441c4645c24600c0c40c00c82c0384080003800c11070140c40c00f02e2655a01400c40040d6210310884a4203050169081980ca038007a6a0968800100d001180c9072500c0006d48526003250022821080201d00c00c0050405904800540b400d50008910b00700c0d0410080ea9036400251007100c80b61080300001c80140c0b0240712507030007140300f0002007c00d18a145411019203d008110404120f165002003004c546414000154084d030f50400603a240c03030f2230441c80d0400303600d540e02c000e043c8102642200301007003140002041000c2070048da030000c0c0740c0a0140303659200c0361101070300140d00c00170032001c4018a5001401e20018064409207030105a5010510b8a03006021841d02d80c00c510b074042000b410050401055140c2030290100109038240019100780203e0051900603040400c0400700808801c00c011284060b2208882d05032038405100b14000c8824041d10320a01d0f46c0800300c010b01020b6000b284102c44050711501141e07800d041c0900020040120 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 145333741 1250 145332491 145332493
    0x2040618050a27050708071e15050412030c060e07230306060415080a0510050106030b031518060408070201030b123d0b040b0613140307081009060b1c0204050702 71
    0x3000074600d0302084000000c00e00f05580200d244410340c14207a20b0852303940120340c5403407090340108071507034040304607803d5070390f0540022072070050382c01c0c01c4802e8802044010941d910b89070800e92030748000100c2e90215012851b0291a0294940210003010f2485c17411039015480403003c0340543c54640c1204010881c43c1d103410081c26610801c0510700020307a082a502604681500800c4114a02030580540300504040c030402080f0004a6901ca922030f0101d0280c00d071501c0420358000c80081812060780001c0101c59190400b0306000e94164081202207000ca840e204849250342042c100c2c01001c0480c410242080c00c40c6114403101c40c0c00c28520710303100780a254160460b203049000310003000c00307246000010041011001c1c402110040c000300d0b072040d0f509002e94500c000d42d00344000c06681143c5403060a070044580032a160001a421508850003034050401d1036041507444071010724060ba00c2400038408042c18031490500c24105800c0202c41400100c0245c05c00e50842a003112140c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 145334991 1250 145333741 145333753
    0x50702090703200405090f070c142508060a0902030a110303160308070801080105091b12030f070303060b03060108040204020a0e03070609060201201603030902040618050a2705 77
    0x519011264400b40b0042c110021000c2010b128906042c00c00d240c1c000751f403400c02042418228000380c0300c80105907008104c103104017070503110010184850b005c3c00c0703081905512041d481006403034042c1200c0c0110701842c4104000101001682d006400400d500a8082c2c86e40e05819103415090b0380c50181c095406110030400d88002e03900c51805044564000c0d91101840e040c9444000c10114042e4010900c980c100000e0081c0ba10020484014415640000c10608506600419036841c42ca031a0700041e0300001c65034903082c801c0b1200510b00300744079690030090b2917101c107500200c500080e2010350005464000040050030030f54024190154542130451446201a001a28108880d00036a000076250714003001001e809000c0c4c52203940c3e41824000c03154100020801c00d40c014a001c5000410400f1b41b00340a1500a912582c42c20360090024480a501d40460004840011035003c0140d880c01d0b00141c40b03107071140710382c00e00e01d809a9110401c08102140070800d1071019603054443c2d004130 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 145336241 1250 145334991 145335011
    0x60c110d0809040c031b1808010e0606090903070b0703020306040905070b0a02120304020f10050c070801061701020307020c09060a090e0a050606090408030a0f06090504140c010906050702090703 85
    0x142891032591040311072580d284488814401603030120307664030060504050384032055620505030001028200c0c6400039280051103041d403c41d070001e90040c0600d51a18002d10580c03c2e010400d2031241d00251181600b43c0c81d030b1641c07159207200d903642c043c040400003004558064441d8000f113400410007040403442000070b8840b1740c14038103d584502101d500010310191071940600100d0ba032046155030003800d503d05071f00400c1070f000d240320046200e180c61820b60401d160041095444488900088810340c540fa845003d0080585001d14806480c0030310403000d03051014001c0b00c6c413800b401d5028002101d015003d000c621000070303202c0c41e070082030582d010403024900c0c8070b0b070348c0705074818402889404400c1c100981007a1010b414903002d04058001c201c0840c1c0d03800d0403a9000b00500d5000140c4800304040e1800903d000d030031421400b030800c0e062005000300010f6214040c01340b0702c2560000c41440005643c0e00850744618000300300188025030142c500080e84070350003452424080386803950 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 145337491 1250 145336241 145336249
    0x3051e04051009060e01110604020609040e0609071e24200106180207020a171c020c0108010f080709020d0605030627070e0c0325030e010e0610060c11 66
    0x40a00782c100007031182041081103d51003014444c16410070300304000d0382003c0e0740f00a600c03140000c2001c2d00459001880100e140c0340c55026100b44000c90041d030f80c40341480c00034680c0b141c000c0c1c8908980894101c9080101d0490f070303030001045801c4400010000064848115941a1a038412109200c034510780b0b001840060f81c0b00380b641480103000019800d0509600b0046914a182c00e2494075106101100040e11290b182030181c0344004202901d0704200c908a902e80492000c101c00d21200b100c0e8200140e5800051381d4450203800d803035240c080da885298440402066200340300c625808030804014071001a8020030700700702c5440707001ca21942c5600110740351442c1910740502c81e01a1500050200f803186c540300d0020301e0f0352000380002078500080445848406003042105071b00000c04100485080c003c444610310568504100300b501c902d03405401812030181d003061550904e800848401000308440784259561008100d51030b04100d02215007082e41c1004507542c2680e00100300c030170f543d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 145338741 1250 145337491 145337509
    0x516030815040507030e24010e0c16140c030c10050a02071a0913090503032205010e030901091406040e100b07060903030605030115150c1e1205040303051e0405 70
    0x40d5180131580081d030031b40d01450149600760b515844000c0c1506010410440c800d43c0703044078010700c45000c48d03848000d0802c02900c560ba60604080300340820755000c0203071840260114000720002c0da4580d40084050641390391116030102d40c0800505481d00041d8021b10140c60702c22814411281c078241c0312610318031003848411124410540114071070406190030744803400c407056072040a02100045990b41640c90101800d004102c0b000b5055030f01f8013000c10f0708140400d81c3c000000f40301c49101800f60a441c0d034014a00307240060224400814501242c0c0c482040c420f070050440c518007440c000224800d001b0140119aa20111041c0040c0700100c13000640199800340740005488009450060100c40e020382c0700500a034100f118810007c1c1c08040a541280c1d00e094507190350710038507001140d0748404440018501140c54040d1079440181c5010b078000c844c072a143d102d00c02100c20f07605075141d02440c40020001003040000829040e0542c81b8001800940304240c2d00307207034a64000400401c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 145339991 1250 145338741 145338751
    0xe030408012007030503061e06120403031104030507030602090f090702070f1d06010c020f1e0f06040b030a0c030908040303020609160b04030b0907030c0b0408010c05160308150405 79
    0x30791070b0400c2d01400840d401040c070544200c5181c041c54850199400740460000400c030b54402d0051170003000440c1101c4038001e40004d0b0050400743c4d603426114003c04084030a88003607000130b180540c0400040004d0040b14180c035040402442014615900c040207540b2001c43c06400140c60001c82000b034032040000d03809414aa00a405424204002a240b881140c0d2002c1501040740031100481c1c50052250303a0814000c0c60010243c500310300100d4280d1090311300c6140c001c1c00329242480601c0082401c140f07030141c225211042d514154080010314010350003450400d41d800c00205240254542c0300400c082181d09001c601d209460300e0380c0b012500036500030380160304400d042003e00507040c0007210413041d54004400e900c509162440f1041e00881c0030082141810b9800701c0d040380e90070403040004581c4070019501454580a039411190000d1040043e00c1d070078001152003085c0070700c00f500d1041460b110710640000d0151401c603a102c1c0045c024040c0c04009141555850705c1341d0054078411 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 145341241 1250 145339991 145339993
    0x90306040c06030b0102060105010e1c05070b1b1209130b0a090504150603171308010501080d090f030b040f08071b050f010903050d0e0312070606050a0605090d0305030a0e030408 78
    0x2003850080083c00340c402c010070041c1107400c0000180060382c1c20200110900340709540010349400c9580908025405582c0007406920410400080036102c25000340b5240c40e400b564150a82c244004141e655800ca01c03010503030200a20004032181840d664440c825441000082040e10101022030310180141e04851405611541003000b4030100380205014126110010081580396132a8420803551001160205503400070711220210414140c040c09040714000804c0b00e0b5a44070100740e5600030b000ea060010400c45a00000c8680c940c0d001141103980060050800384d442d030f41c420700b1103003d8a1003221107001c00e000203400f24114900582010f0800003d0191a07030034902008150042511130f41d0401101010030300000c0c1c030102d00045454005d080c4140f10f16560070000341040c0d81140126618100425190701748251a04038400310780f401d86407090555110b81c0c08030307200d1041241d400e1300000103156600010344514010760348882c814000050558160303102c14215485a4404041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 145342491 1250 145341241 145341263
    0xa0f06020d1103070801050105090f150415021218010302070602030406051807030f080a020a050a08030f060409030f0f031508030c0709050f01031e022e020c0d150209030604 76
    0xc20400c5216840420110316282e50661500c2e9000030001071050003241e042200c04101c00049441f404058000c1c10030080486188806400d03004545070024419240b4003841070408801160000c00c1520300182e211001900c0c041c4040001c440c0b91115031101810554200044030124440b40b01440c007591141030b0104003030410030ba41126019485030500318a41141808100150042501c1500b1340c0d40f1a03201600c170070300381c1801c1c0e0400340794881c0074115009403a125010403003180d00940c45039101413030b111042e4940c5400d00c0111104864001c010510080d64540f18500400c04401d440c4034a103070100311459a840b80d10a050800d0703010014a500106401e000e0780c10a2180c1000f40c049140b0800540c6440418061001411710001d441024004d1400e0201c9203150242503404da000f038100c1d04102695201480c0554880320203410074111181004280343c40403802c9120300100400200f00000c494507806405041d040c0c1500515030308124140c000e882c140031140c401c074020000041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 145343741 1250 145342491 145342507
    0x51005180f07060207140312030126010b0109091e110405010e06030705040512070909030c0b100315020a0e10111006030c2d0306150603020c06010b0c0a0f0602 70
    0x22a010244012a9280e00080710074004030b84c0c0000c038a412124049903c1602440c0c8501080c104600c0c0c040035410802c001001050340281d0407020401e002c95003000e1036030a910462105d00700c0f401c9504950010312401000c2000c0c541d01e030040302c0b8405109054691480000807030008032422403241c01d10308240131404101542e00049131a141d00c100b5141b0b01d1442ca00108003d1481c42580201c07072240384100d04a070780e80d000401448024181e200780c00c02c900107a90038003030100d40c0b000c0001c58000403140001a88480301d042d84204499010340c10500031049030748164040d4109c18002c204112810058240303a0761002004001c0c0301c05510b80312084071040019506221881c079000c0c81440c140281000080e4050102c6012111442101000c14200c40301030700c0900181e11202c10402c04019000c014270610703600840c2c010360b0b0100003000982c2d5607001036040e0302a0720141081c5800510040204c4420000140b2130320741701c20203580307091560b50388034114070b40c10b4041030301c1c070f1640413501d82 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 145344991 1250 145343741 145343743
    0x602060a0e0309060702100c081303020a080f1e0c0616030305070f0c0b06061b0106050901050d0b04020d050f0303090303100b09060901030b0f030f1b040b0a0e0405100518 75
    0x25441100c0c0146290606a0010134054411810000d0080c9000d0304902e0a0910440c1041801c40d445076400b0303982d52445030811604c42540c0416846540600800203203494005a400342d82c681c0100500881c0940508012090301d902d0301d03011445c005e00d00c00f000d07140c1d181c40c010904114908030388412100f20382002400c5500051611040c0807140c90b406d001250051046000198450300d250340550310000420140d00036042c8441c26085a08180d003000f0f04107400c00c805a80c000c2d00e000c1d1483c2e03a01c00400a0b2801c100502500310303011385001c07c000d414408030900040340144121000e42c4104001d251031a0b20448088425030004003e1010744500700041130000c0010040f814140705c02900060914407914001038107059807504140340035201d0224640d003500d07008090b104a034001e001910307181c4136201001104035955002c100034070710b0710384200c2c450721001402909105040600108041002910a607801e105061a20741c61058070b001e110701c1100d1040440d080f40b0881c0b2401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 145346241 1250 145344991 145345001
    0x60403030305040618030c1b05041d010e010c0504031401020702061606050907030201080a0b040915090b060a0e010506070501020d050106090e060904080306010c08130303020d110708062701060602060a 88
    0x501111007501038120100b0387c0000d108010b1500314902d40c40b0350220155820f40d10406610640e042810010140c0035400c100344080039802d0650000d00c02a1802d203512401c0311521071075440800c1051000b44049603003200010303800903126000500e000c0c1e003600082d4ae20782000c40200103a2000d01000c2c0100142401825004001d480042c5052811176001803d225001001c100d081561030400c9407442d40c49410501000386c0011091005481d030340b0015003e002c4007a4259502c020711008640d042c10010010702c11151443d009520380e0f403c1008108a50f804048103a986640a022707000d00c0c045a445031034003d12617600c0304203550345031101c8030308400c8008000d2449070100004100c0801d600b030084a91044c03091810800c01802460941030900412001d1149103203071440100030140c001030301c05410b00e225190700082e10700240c0101d541d0003642c01140702d240c20800103e007400354100418120280c40600801c2c0c00030082d044c00e801c44040d52302c0440140e00c11410300c84914014414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 145347491 1250 145346241 145346261
    0x60e060f12010f0b0f0d0f2d060e0c04030f0317130201110105060a300804050405130515060a091a090603070303020a0807030507050304171204030f060b0f0604030303050406 76
    0x521030030145c030340d00303180214000c8045406503203460b51007905000c11703240d200d940064000c81c441e6a07c5007454815005d0700342000c4100c1c3da09440d054022801a548805031481030600c41a002d1509040d551070003000001c1840860174408003c0c43e04600c40a20005503201d410388101003070810604d4000108100c1c001c0a0305403599143c038050102d2602c1c3c0310b10b0307402131300e40d14100a403c1c2031000c074108600300f94802c1468080d51440b10428100440d140003081116400c41d000d02c855107851a00704a2407e007150f0003815076125120200f001c3c80c400d034406034003c02c02060f4400503940c2c1c52950003603c1c030703041c980d940c03540360443c10360440d142c00d50800c1d400c10000e400420f2900d0441e81c000e03660f075040100c0900007000114458040600c20000c03038444a40c001c003640c1d21a56074002400c0084031100d0100c403280a001000450030401c10291002c494118808040410058465000505aa41030036402c28028540e0415688a0344002d00003107200c0d84d00001c00e413400d070900b001250f016031a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 145348741 1250 145347491 145347509
    0x20909070302070b0621030a0201050a0b09240a0b041710110a05070f0f030903050c100f031805030c0709140114061b01060609080d02120301060e060f12010f 69
    0x801c203004100901c0c403003a4452001e91b200300310404c0c01c0005e44904074605000c2c1d051844009602c2c0c0301c04c3c1d81074000b240a00a0701800b4880c03400d1100800102c040c08503030b08000625028451a001000645400c14001d0090640480c19032140c4921400b03500c03070b0300406000b4003410840e45660f041001000c1081110030000c008012051012803118401c0b500c41208000011400905121242045643c644c3d031010031807003003424500c0c0186c5840558481a6224054023000e4242d906000003080c2d107c4030565150503440002c0d40041d8000d104060b400c01e580841c01d15402e00040003000180203007000b49008094070b5141c40b1801c42a074520f003444492101250700100b0241148440c07082402c0340864001d511801041c440c24600740084000411075130034400d00007000c90700503c1440c1030f03030825015500040702d0a41300340d9540340311498014609108200421605106a4040c031616500400742860038000e60010006500a40c96090341c80003000010800da0800390b000b0380041541e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 145349991 1250 145348741 145348747
    0x20907050324130e07090222170304050d030c23010c023f0a030207021230040905091b1203070f021c0302100506041416031b03020909070302 62
    0x1002082c0000b2081c0d825404a98131002e07654005901406130740c2c00350201400840d00c564411005900100302c400a00b50038150302680401d003044d4001022050182d040019407400e8035102c10300110901d696002d80805c0384002036100010042d10311011144c000085400c15083e8104005003101c1c40030320b880007598055010b542050b003494104140700c11a00701c5114010540250700f814045003d4400000302c03400041e503c0000343c165002d440445d000383e4500000b40903458a190340c8810301e00000c207003101c0c041e00d004518850000d400c0d50600007084060b0a143c0e07a03401c0341c2c042d994107440d840485c2d0001c03c00d4445030003400a14002c0c040c0d0403242141d004030703422442c1c0d40328811544050f0186a01c00828829510b904181c0c100348078195640ca500c044e45402d00075126003a620b40e40c10b80ca401d0002060f41d034507050091001d5540007494540454a03280510340705c07400400c4400e0103043d01c030b850089040c0014202c40092100369200580d0f901100010401410780080100090503c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 145351241 1250 145349991 145350061
    0x201050108011506022503120203030702010507031e0518010903020c0f0a061202070201090e040605040c30020d0605010314061b0406271202030606030a020d03050a03090209070503 79
    0x7441d070000040a102101b25680490f0040c1e0040307001d500050300743c0080e503003004412540080110300c540141d500801860b101e602048054a0340da02046410448548238070300c0d030b00e1072940712507000403444007410030030020100343d1429a80300d03000650268020310f50703541c603d00740303803034800c1c8245000c42e0305004103820500c2c050806c00880008041c02907003c200c4600b16402050303900081c1c00c00790200091443c040c908180901002c540c00c45051130170f4000091001d02d558003150038904888008030b240c082c690101d1910881c07206050341e11500350302c20000458681d2081c10b000e1030241c01141517941160b080603140960181c4000501d002d110144034059120806607003d581e0585855079015201508540d00f018a1525440300d4642c0c8600004070310048000020a4a01c240d041e51620313a151010562684801700703004e900002d81250480009110300f00515505c01c0c1030500003103131112a0040382d100c0c4022141c48000c92000814001040350b180c4400300c3e4003512040c041c6001c588 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 145352491 1250 145351241 145351243
    0x90609060e0a0c051605070306090b0105120d082a03041a0903030112170705160501020d05030c120414060403020d03060e071709030d11070303060501090608010308180301020307020105010801150602 87
    0x1440040c198104040ca85e0501044018841d16000303680104c01030140a18604003007045203428441c1c1845030342e00c02c0440d107240e2008a401001c0c40c94a03140e0b54100d0f512505244118404d80b41c1480586400d204ca500c15040307803a000c0e60260b405a6443c541c1410a03004525001401800003c81c962090004106104054804412282d8414038800100108000c074210600589900a0483c000d600f102c001e0109194084000c88500360f007100c011007a030f10000d40e0b1900c01a29a0242d1500402040108801d2550380c107410610910542115814084620f424004162411001600102d044d16030041d458003d00300036011600e800300319820042405400d10804030035184a240e40200001e20240040c42035410a4003043c50611401c1100124444c4030380c4007080440c0428a0710301e000c96a07512a1907100184c0c0e815441d050f610380d080d901d50764116040114280860003910701314407110745080c005903004a5080c3c0010031039505001100317083d61003ca0b1030031280042000100708081e4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 145353741 1250 145352491 145352497
    0x306151e05010509010c050105070c0309051806061b0d030504021302030f06041d0a030207080f03090108041401020d020f07060e2103090114010602070816032a090609060e0a0c05 78
    0x2001d00700f2650b00d601040058503880d8808001609079444c1804005078541c018140c1102c1c1403280d80c4442070162500e003044030720400b409801c1e0114282600150003400d000703000707151842e04824024614100c0d071101500d00b800d07035040c1d2800207072204107000c2141010724507240140042c0d00154110b160080040a02c07a00042c0f181e0710031510b5441c0e030240d4850b2016009068262841981c0001c135403801d01070350f540c01d00e01c0344400d40c0c4030b01d4956032940c0c0c0000c020744050010585d03449000b030300d0740c1c0c6403103640b0609005010a9550308100050140010b8802440180304401c01c1d135032502d649042a200312481c0321401486604034481e800e2202e01d40e5407140c9195402c0c186469240d8503100302e0a40188008411110708021210020405070340024442d400ca88042084880e00c44400384010280c1080d880000c00031000d81e0741040e03520300804469400c41d142c040701500025981e41220055604943c40003d885035108010300c042d0072107000e001e501c82c01043c000c3c00624140c0e0b800600310b00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 145354991 1250 145353741 145353749
    0x90c0905010e061b030c01021209010903020a0201080406020c011b1b020901170a02040203040614011e060c030e090a06080c030309090604111e0d140403020a061508070306151e 77
    0xa80002040002c42d00c01c04941c580c12600d00044940301d181c1c0a1051f4000d40c845203106824036030050009007561414003507100100d03030507800b60000c4561540103580e03103030f00508100c0b2595001d000e08425200c003480707640d01240308032240030f0071203010b9540a402c0d800c146820b20301020201081602507101c0319070385c5046900c02641c91094404401c1d03001d00388922000000c1d40301f40004107001c28000b59421105000700d0469008049990f90b640101a142d80908096a5048001c4040191a009803440e10304c3c0c03070082c100000da5a0200c800200d03004400ca6138210072994a24084c094428100300c0008035000c1503000314a03044c0c3e424002032202d400100039a20507034443d82d45a647d8041041030b074240311803006060a0700f100002a03141c203500000034505d01a81f40c46804200003401c6581c9500032074158018110708090341e15124064200b80415402000c04100001207003034082081c800218080e000000d680d8280302020428200780d0f920004e410442a8100c04000040c125a0400c1f1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 145356241 1250 145354991 145354999
    0x108090705060c0102120f0f1f05010509040b03151803040f0314070f030308091204030f0f1b030f050d0306050a0605030a060b0c03070506061002101509090804090c0905010e 76
    0x742108044041c060311a800c0c09081790a0780c02c00380007901640d810101c0c09a1940048c40e100c41d81c034011902101c603151854240001d00b200d5007041694002e038010802404042c0000c5940520000402d28125031241ea200344000c2800420444081c00034074004004441e80107145080d140c100d1500c4040d03a00e010162070002d40c14400e40d0101d0701000160024030541d00c0e002202c48c1d40b4140900070100440e03020303100c1e020305051f081f40405204206c8080d40c1d1701010301054103010b078903050300391119001c0c2199081d41c4425203414128041500e41700852058031019030f183c02c2407078903c0c20006d00405d45010305041041c01d1100703903546c0150b10140e5035180340c01034503992450030203c060107199001c2c02c10fa640002c0c428032001c801100070240b150080007116443c2c1c5854052104800e011107141c40140c001a07085032203129540c00c00c811000c0034000041259403185100c000f2119036030300c103c40d08840009d08110140c40c600a01c844001d2038140300e0032a40c6024006891510800011441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 145357491 1250 145356241 145356247
    0x40506010527130507090f150f080603011d0c0406090504080a0804080d0f0204090b0a14040c0c15090218040203031e1b0304060216080d210c0806010905010809070506 73
    0x554590810f8655009900c0c04244850700307210201404100d8036000704c002c404406800070030651701428012511030400d6440d55040442500110748081d0050307c0c00340d240d500e49000a0b400400794001e45540307820100901661aa000204412075030300d5800344407240d00345010030000c184c030a42502c62481e0039040c4003640d80d84601d45021940300ba103440d0120a0300d40481c1d03200d00d411a40c0a00b00355008600e003005441c14110401001102034031a24840c0061480f80d09030504041e009061803000d02d00702100086115030392101d000000c928010a8603a031540c444043d071410011212044071540d107008001d0400350007180d100e20680600c3e802c1016002c0858008002c50411110141d000d0900210b02803003440f01c0c0c640701e601c1403140100602c00c440800c580160018881070845400400410320985000c0054170a030781c4520203882e4015648101c0c849094442c000e425060165a0301c056544c50020000342148800384c02c41c5040020700d508002101d000091aa02030b11400c89910362 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 145358741 1250 145357491 145357567
    0x51503040507210605090105090604081308030f12060a030f060902011e17071803060c090b0d02070b01091103040b060303090a17010501050301020705060c0a05190507020405060105 79
    0x460030400d40c0c01400f4400710045202e01441a1a09003007410b07110311018029038840d051401d090354070070360301c2c030391150011008140024440f400400800c10b184803000049655224003904541040020b40000e6100044200d200ca0724a031815030720601c1150030000040c1107803114550710000385001809242c4d80c81c11001035a00175005410000c0c0c88400044021303180c014002c185080c0e2401541d40a8003820100d48240e000f01c1c04269100d102a0626848502e035440b403202404101c0f68a00512106c400c0200752412507800801441900000150780c4801c10320303102c0c0080b601603006201561030000c8000070000c0c036508690308030303800102510f00341c1c41d01000039096109044c10598040e001110010b0400c101c980c000c120b03112850001c00150782e96006140c241e03c036203600101030f40c22000005000740b0f0301c8000341410100d5850400d0604c4001d01610134050418202e942c0822000314070b10045180500030369030701c500f080c41c0c11810001425000190015003507082500c007070900121003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145359991 1250 145358741 145358743
    0x5031003080703020f060f07020c060f040b030c0c060609040b0612010b040516020f0705101107050d03110c010e1309030c08041410020706020606130e0f07140a0515030405 75
    0x4409160800a2a5902c07a031a01e8065a0b5481505504a16028020000e1800d60042507818403c0300b058020b03110042001c41005001d034070070700c4400c05100c1c0c240404500808844c3c00b0798810b540c8006140e6a9008400108d80b5003138000b028036100340002402c110003da0030b10011074001200f41c859040c174450400b000c03409400d1500c3c000344c0080c074000230882c020300340e01301c820740d45107907602642c0744280030740c06145d11119170b4002c080d040001211056500f070f20a01c4106121380700c079415215200e03111400145680b800c084160300082d90038018200a41061000c0101c0c1d5200b400c19017100e91390300d0046032000700075040e4604007036607903008141858080c1c9001e0464580c4901c07050f5850f51030702004a88240e8009020740507000100860460900000700304040d1407a0350010700f80f0707a60701c030100141800e030490f100819a45400d460480c000c401c004c840102c00d5200c0180c50a02c1c00c009101c1100400f01c65030038440d0305903030010003c5840310034003840c26484003a07801c8c1e0340f170751030342461 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145361241 1250 145359991 145360021
    0xc051b01050904091425050406150c0215040315050906090c091506040305010c140f090907051902280b0a0c180f24021506030709060611010b1002030a0503 68
    0x910740d004d800601b05440c0d144d451840c1d00405070358991402c140c2c40b0820f100450700c070b41c0510841d00800e2004c030030b45035009006070f0303d1541c80103082402c80920300c1000d94554106034800c40d80200c0310001440c5400e03d80c084c5503400303282c0d60001d03c2a07180814800b40d940380105052405801810086a00c40505454522001c04081c0c1703003d42e0385a503480c2c6180208088182d560011b69040b4052821a14590854581c089007a840c10306041042040010301000541042c0c1482010800706421050303511030310048103285e4008c4c02c801d40401d20510701c90240103080d6615001c9d040c103810001040a4529600500011400070b441d11036010280c03118156640100701890b8030510005500900390500c009444480070070b483d90580345540c0c1001022104000c0016800c0400d001d0001c0160f5603001e07501040040848551a541d100c160003114040c0e0003040004407065110881d09100b405501202e032002c1d2803025201e2903001000b5128002c010000c02005030000105007001c002d5844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145362491 1250 145361241 145361273
    0x503032a0f070b0c0307080c09031504080307030606231305150c070e0618070e061902060903070c0b0309010213090b19050105160204090b01060c051b0105090409 71
    0x201a81d6030030111038a112900682000c656041e41d070000201402001c5007900d0040449031600e09403a11030350769017007554100c0d01c000394051140d8165180d020103844034050145004008407030b900d05103c070004040c0c61840d040001802081c801c0e4411510460314850300c500c0c0800e000540701c80309052421080b10565006650100c00307582c4020181e21a0001420585048403c96079056910404080da0080031a41907500c00481e04440440342030100e0800c0c0e00043e0703417034880039100e20140000c1c901d030000212110300b117042d004404502c03030301007081c0b80c0c10a80303010046040001c265502000c1074030b07902078440f6000c404404156890070035015201a2011040c1c3c203030302c160300d8402480c024100300c0000c510640413032410504102c0d007400c0340000e0741c00c1079445600e4404c524624119242a0b404102d07003041c2d0302c6804078041880c98000354041c0c04a0780d15113048955604189282c01c1d1228076118106c60446030301c0038036a070800115820307124151408a02d00f0300300e0800c40c82d0031900d00c903 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145363741 1250 145362491 145362571
    0xa0f0b09040302010203010f08070303210f05010b0301050a0918061d0d020606040b0409030806040b150304050c0102150708041220060612010b030712020d2003100504050303 76
    0x7800704040c0c040d005507050300c16116214494564840801b80d403502c0328880600801c10601101c3d0660043d0300302c940c0c0070ba034002d101084001881a12400f1960300760300030065104048014400ea28100349600b005045400b4144010f10381102c45101111000d4401006241d0361603823402d80342c01c01800301d0003042584060701c005805e10100070752241412103000744078501e8054000c000b450140f00d880c41c401d401d80e8810301d09036112000c1c40b0040c500c3c0d0f0740050344400c419142d45107520000c4025803059100f08040e00412401c607001900c2d2602c2c00b900e8941c1c800120041105070341c0d11841e00359020307400c64050540d00a4406040d85c59404c92400c400900581c1090080c8407080003686070300444c0b00351401c06070b550340324108a0032a4030b040001a0b05400420f41000b6000340109261220f900040c80349001d9401640c4030407807003003040c115200e100705036a4159080e00d0103100000d074000d0201d009000516056840980740e02c401448500b40c40000b0318030f0844e03840e1a80d800d0010300c0d5009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145364991 1250 145363741 145363759
    0x60b091c06110304030c060b0612040b071b030302041404050108030a1d040204080607080105011e0503060301021306020a0c08030f0a1209062d02040b0a050c0c04180b06010207050102060a0f0b 84
    0x4240280b003511b500006440b403a050142440550030280102c40e0901030500300e03100c5036121555503907903803800a0300715010050810305401a10012121101c3c20b54401e46005075100e15000c1131890400d010201c075403066103000c0040001290200481d4914075491415449400100c0c1000040e9103e020000360490b10204001c241d0030300006042e402060703a51650300c0180c0c0e9400044800d094001c80d000e030250b40200300510014051400355410080041c005420a40b402600045441e03055000100680c8800300000a209001030144041c0c04c8070710207149010b40c005000c204510440301c921080080c2c081c40d0254540e80343c2d01014009034010801d100164600071038a460320900500858000d0854032117205202051080b00c04039480da1409a061515102081d10705030040300c96014a8012307900300a07100c1c0e41d50f10841800ca4078000d90302c40a008203041c003000c419401428281558001c200a218036070300054419130116081718085180c20482e105074000d401010b9600350020015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145366241 1250 145364991 145364993
    0x150f02040e0601020118030f0f050906030f16020705030307080a170103050106090b04060305190c15030207060b040209090f19021b0c0d0b06090c0903030d0e01060b091c06110304 78
    0x14007032401a04241c2c02071040e10761840b92070508072101000140410800c2005404007400b6140c1d808462030142480c509000c82d84012034520b9004035200c2440b85240ca00b00716001c010181da104400145200600006041402195891280440c09042c0880c003061003112240726550420b0404072070f100a00300c5580d2454854003034880b5001e1940707000d003880305030800c03805d2504c90402141d400c80024202e1040f554040780340f240483c031043d60180c942100110700540c49003a840300740c01d5148c2c1c00590710300c1d29080c1031080715034260080d0310490040040015a40c0c58184882d001400001540d8003511a4001c101030500900c0103200d034103001040341d1108140e40d2100c2c03000801903000f40d403200d0381e6103010007a40780302d4550010b002c286c0001c007041b21170514840d03640d80001c204d0307501c2d1701d02040c100004c0c0c5190081140d00704540e407555491200194280514070060003074446407400e00900e00d0000d403034202105424031481d200c00010400348522900071052000007140c03080c0d528185 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145367491 1250 145366241 145366259
    0x30b15031501050f01051806030a0912080609060d1208070302300f01210206130e06150301140f0f1011150c0a0c030c02150d0f0506030a150f0204 64
    0xf4070800e481807030004110262940aa42190a482c03c60180c03152101401d000300034158001600000745560703144800400076980d10b031040c0004003940c417841d03580d10b0f044080201c40f80005001c68003807001c42c1861400126641c0303404030070303005030300740000c40303a8950b10200c0090140c000d00702400f01210000841c035401d00107800003040d00039050360b0f100e1340d00e4440d00402e180c8203105110050200c0c01140d6503c21f01020b9000c58944000c0c5170501e0f14540742d00074003403882e0680060010320b041a00303200040c581822901c0c401c2085400b5103007150300d0110f40c05c0f00f40c5100040702d802102c0b0ba050100c2203656044c0c804245800090516a01c0105040000c3c19100000e5250f481c2d0b20804a003040303801105a000c2d0310828244002c540307804803d503000c964400310f2a60850074010700824034070069580c410a560011911104551a171120307400580503103101003107458526151109002c42510042075140c402504005000311407180c1806a1000301030800040e840c03035101090200317000712 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145368741 1250 145367491 145367533
    0x12040212121b0721080a09050a06081501110d050702030a080315030d0201180206090301020c07090f061202030d03200a0905090919020f0604120f050f16030b1503 71
    0x880c0300b00b1039040310b844040d40388441d44141e240d182c00d08000a444030000703840d0801004c3c090424988a59010f540d440486c542d816207800541c00b00340500c08008080c0415035440b50102e40c02d10703148607c410780d01c0000d0f4542c4880c5115008000001908800f035480c100000e070142c40d0321900310359403881e049030f000c40321102c0d0400d180d03c2030041c2900520094414000c03480300c03900c011003414010907542e00300318103540200308454045d5028030504211403002c0c85490000e100041e004a072603003030605c1000403a034041c0c0041c0200341581c2c900d02f000d42c80000340080001580d0a0018000076446011241daa00008005402c2c03c00020703640300540e84401c0020807a5019910214070f030b250f144040c2e0b1942000c05c0e842c0580b00749000d4044c058580400d001c0ca030700c40090304241c5056100d031641210107042d5034058550512580501003008000c100c907234a0790078110081c2c1401d109201c3d00e541c20400c1484054442e600c17280104000311180d100142d10000014101c4a46075840c0f000c40d12110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145369991 1250 145368741 145368787
    0xf03030c0c0a0f0812070c0314010b0111070303080109091e0f0b0c03010b0304060c0909060306060f05060909070c06060e09100c0224090309041418031204021212 71
    0x382981c800159000b8500f07010340a540040004d411130f0031054140c144560003c10080e108583c2d46440007000c54070404030801105000d8001003000180c6800161181c003141742500507903440000304001003a40726203090b06440141c07201154011850400244604c102d05101d01c03030340701c825499002c00202c81d80c13045e00f0318452101102d8a507209945044035002c00d10940000d001e04000140c0041d40c590300005480300a81814a441e5032214058400c48421340c0084501c1540d4900a000700c4400b080340a009017411140d0700d1410601c000071480488024003d40706100c03c201c1841c082002507000f40000d042c030080c2040c0303145072221425555864070250a80078520309200d01642e00e10104001d02c1c8030300c2c0580b803900c1020501e142d001c1080c100518151582c00248249803842c1d9460060000566414030a83c949003444940034000d00f105103c405041e600c204230b00d488181445c4111503005030100c07009030b56840120449800c1100c0e070000c803207091000203070010204681d091008600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145371241 1250 145369991 145369999
    0x30114070212070b0112051c0509030c0a05010504030b04050a17030f061002120c0f120406020706080708011a0919081905060a110408030a0521040b04110f03030c0c 72
    0x3000ba0340c0001c095440b480b50003400c50200034006102c1041044498880030703100e08101c8072800b411500d188010510401c010700006c41c00035440103075103000c100703480d82650112401250140380c080060000e20642c44010841001800010309020301480b898170880e80200c0b91280640c50307511010095402110991f2a20356000003103509410054498004c0c80581d800030704103010050b01c6405580c0100080101900c55525140d040c500c05000c441c62940b4480340303560301c0d85d0810704060304041041d002142040240d40401403640d03800480c40307046800c403070b84010030390340d851407140e1081c0b180b0b1940d240c001c40c109108454030380341c0c00c000b02c0446240005032907000390510a078148a21420002400c1944501c000c5600d1640c0d5910440e01c4e510110721151400b5910b1200d1425500302101c0074000c0f55004c035040201d0420140c1c0c0110038441c0760051001c038500741d603c119829202420152130078070000b15101690300d03449401c00002000801710781d119500c5600043d41c41c07026940041c01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145372491 1250 145371241 145371253
    0x30c060f01120f0308060409020a0b090301051e070c03030b03030720030109051b0301060e190b01050a02030d0507201b03160303032406030c02120a0e060306040b0301140702 76
    0x2c450b148030741e002589070b442500540324001c03e441c121130800c40139120342d40c0f180d80e41809500681d01c00c4042c10007085086c2c6150b84038051102010300b140d900508501001c0c0e00568001140e201c02034445a21040d1404c0c402d40306429030504600034038a86108035054880050808288030f109050121501c06110040c1c0d0a104d10704181400d07107013540d200505942c4070940500d80c41c40641100c2200c410701400002d0f41690724a0102410a016a0035000c542c100306407032000f44401e406410000362003130a0852610044400080da00d03c00c9100038490a583d03000410022803003101d10b141c8807503c100510008c80c02da00300403074488140603000d44241a15203c2d44c200e606000c00c80c048000224001d104041c1e103951010380180c921910001d001d1102c075184a8944100312000c00b01030070b5240d40000d080700a00300068544001803802010741c1c4000c4c4907111509038811410381c8400c20a80300350380c490311030902141c0545083d14255603d03508186003001d0148940300982e1040e0025070850b41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145373741 1250 145372491 145372499
    0x506040c050a0f0503090109050613060c081b030709150302091305100e040501061509090506030f2d070b030717060a0501030903050c1c0f050309030415050408030c060f01 75
    0x281ea00c20316141d80b01151220b968111100c0c040c4000e5540002c000001161703441c1503680780fa003070007001c5030f1000701c443c0f16008140a0004070311824040d036800b41484011810020383c0d81c4204641c10b00400d9210400100280d41244200a010000e001a1900300c0070410806400f40181d007084400704c1c003c10511403204070b8a0f240703000d681d0280b41906034054529007020080b000503080240152038a40d200c11000ae841480d21100c100c0c0b1003100e40d2400861409d081199043d01e1001d02410b20940c4800d03185030310040085000144403041200354040c00600001d6000200c2001401e4441c50003181c0000070641c900341d00442c0f05030074654414990488580d07090840350001d07511960071180301c007418000b9500030341c0400f0301d180c00380c2005818032704844821480c2032082880c0702404079a501400d0394407604031000780494200c81c02c044c0e0540c900000a01d9603400340c1e225004e0350f80c1454040d00d00380c0340107001305c402800c41607080d2982c4421140c0015603500090705da805800b07040700000a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145374991 1250 145373741 145373747
    0x3080105130612020d050a17120603060906070302161b031703070504030605191a130207020306040215190203040f1203050a0e12030d0b090705130b0304170d0506040c 73
    0x40540e80354003507114a040f015024404007100c4107034211084c0c0310780c88042003c01c1c4c84107281c640c0032404d007901c02da07100300710040b4804160700588200e00981c010305c10f0008824010070303000d80c48840ca1a0051f1a2891000760700d0030300c20780c1213014082e8403440c06c80280600503583c401c0b094a000e6850039080b1415020200b0840c402250301b0800200c06000074000113250350420382d0089640c00b00403030385640c40d00094003100c0c00580140c528440303c0154400500f0300c1042d041200c0c2400d00114200715041c4c0101fa15100014002803085034940090344039007409006030391140780608a0205490a0504003a550f940035000b50b400030b1a00e4200004c00c29a03104134003054030740c9070756103e0920a040346c0991b03880c80b405008903403040d840c0c1d44076081500100041e03c0550000074010441d2401c071403d101001c032000c0c0141042240410012110340024410102107440700e8844a03520303a1982400e00c00d1410011070820410400100e0150f011107a80105000d07840450702040058410320b025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145376241 1250 145374991 145375001
    0xa1517012c03031305100c030e0d030612080d06030506091516090303120e030a090f0e040803040312140414100608071e09090503071a06090103020603040204020c0a0308010513 77
    0x2803446600400000b82513803810600507082ca8854001c49454521002e030b83d901f69042e85d920303040040e60301d0004141400082142441350f148a040401a80742030160303112070349148040282031000c00060540c034802c91580001c00540d0004180c03001414441281c0d0388410520200c7c003922001c0c2c80104456000c505500800c02c0c400d6101c060a0603c0d550f02070701d81030500401c840d038880d42c5120304050218180002d10755103a140c0d0740e0179684e81c200000c02862681a412454008154034200000a00844206e82c2c11540504059081d20041c1030004c010302480c035260340000d60070703205000c20030480d1030b018801005031805071000191003080c100708884082c4a1000644d00003c0100004080c9942c0401090a01e620402600e5203501000003500c62016007150103510000b006c80030f000c1c43ca5903961941d0300c0c58104855a041400005101c500180006481900c1c0000442c08654442c2c2c111a07070b101d000c3e4159040c05d400b5050182c80401c0074401c060180b80480c09401c440c420364891 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145377491 1250 145376241 145376321
    0x11a1003060510080702150108060711010204081b03100603062012040b1503030f0a0306080706090e07090509070903060e210f0c12031515030a151701 66
    0xe0200e480c48843c00443e00c440e0040d0100c0c056000342810300d05541880115540680380c408018030250070003c2d070007031201c00c403a90f0302c2078580d1051000b48071075100030900c82c50244a8803410440c024091000038109181d030380e050a07030145816800010040e0540043d00d00240715814044240c80805410101d4450641d00c255604200c100180003d00055840c0b500318415801401a038120301d00403900d95404101200020040807031030920459243c010301d805011803101400c4400d181410103070a0000d680207002d8092071002c00076855600c9032034000700030000100b030041103040030800900004058082a40ca26040c040ca203841440f00003010120407030100c07a61031045020303100e0b00034190480117041c5000c9004002900c0290740401c041706600060160007540c81c1401540b80c10240052500b05014801400c0311507440c220f044252035200e00c0c1600081842c00d038564100740040c4d0b19412100070051954038410321398105520890403000300c1600040c2103c131021045007011101d480b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145378741 1250 145377491 145377499
    0x50304240212031504111e040305061303080106030c020a120804030e0a0b04060c02060c0105040c2108031f050402030a0209271f12120810050303031302010504030203011a10030605 79
    0x81d629400313040950025803902101c0d411b407800c0c0000700d0540d0710151b40694a403d13007408086014400d2040601060b81c10102a100c504140c20540c2d0f0040c02c6401c05114175428141d9800498005a00a0080300365090740100f8000c0d031180070b0900030f404c1e000c007030714180c000800c01000a2050700700012054207070340030301d4140d40c1802d16145017101c443d9055203040ba0050410f1001d84030b000c0c2c0901605005a100d2611300d111a41409656043d544440c95081e5032080782015a101103130041d0100c070780081d110500c403102c600020100c0e94220000303a000c01d4200788000708112520b21194040c0c52400003c0b40c2d40090f0032800480400d20690340d03034a0103048800070001ca414140c281205840610f070442c83c1c007854a82e0b07030300d0707100429519072401c0e81c0706c0c0d10744c0d5080242070740c7c407103c400d500c40f40b1440001c07a40d41c184808259607000041c05030303640c001a0328001c0203581c000c20684000b194024001e00101310510700316000c1046082c0a107019803890994903e446000307001c1d40701910b9002d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145379991 1250 145378741 145378771
    0x501031e1110090306052502031809182b050408100203060a0b0403061a040e1f091b060905090403080601030f0204120f020f040603051905030424021203 67
    0x1c10003403081030581c00705080c403440490000005400380100b611070003031035800c1008250001030021210300700052400864104024440c1c50203001c0801d07008400c000da894609503a980d865642000c0e04074001e10b0003d200b03904504041418412002e03080074030756103000300000a85c54068030b0038040c50155003081d030030104080c0400300041c1d0145034010002801960040c0e40e40c00076002a50090304243c49240e124040e1407020030f8904c40c2034078441429a41040302094002d4059128403a4007900e040c0150b46280d03072208071400c0d410003e440c5422051000d0503046400146030703900c4c0300b4440d80000c601b0b1058001050b103001008144503581503100c40c600c658900300110010b054003804030441360ba09100105074400c00b021719001d000d02c00c28902803107507001e00411110586c4440561f20071400d0040070f100003540031410003420b034030180b0109001d5900d450158114041e50b00103a2102c5c0b8062020f042103801203240b200d0b40e500305e07000da9081c603800500350f201922007200e524078285c4904d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145381241 1250 145379991 145380023
    0xf150414030c0a06020c09010501090e15061308071e0b040b070303090f11150f18130c0c0309140f01050c0c04020a17010b03270a150501031e 62
    0x500000c2011000003030568411000400000e03062102e40e070003a0700107a00200000c0564140f000425015010908160303400e01d1a1460a03244000018081135180404104000d80b0b521600203a4454100c3c48003e4020307a510340395000e40c0d407034044c03103000900a04894002c00103a03000300081c0035642d5243c01d0ba8902800d05210a0140e0b0003114101c1c1015030362110000801c0c00141c4c0d60704803510604440401e50490010050b20410307426980034248803c2004560480c1b4600840d04180c40e0010345103200440d8000180d900c80300e191035280000c1c1080d4520248070341c08050003060501c00d032200c1100580319480940300c07a13803103441e10340c1000d1440c0c00000c5540c0a40050210101c00340c08940060119001003800d1760071000c0400045680c6c046640c0d0240304200007540034007000064141540340101c0032100703c8130413000550100031001d100e14900ca1040c424110003036081881d0816248101e5100c000410b0244002d80710240c80c0700c0280500c010f40344255110700c1c1c00161a0281c0030003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145382491 1250 145381241 145381259
    0x13021f0c20060a050301060201051e0112030e04050c09121501060c061508070501090801050f010504050c0706140f060f180901020d1e0b060f0d020f12090c0f1504 71
    0x101c032030800312951201e0000340503616100101074075010b5580320b681300d51600801038295403010303100342c40c1903081c150203065241c01d070440c41e41100c120b414030b41d0b201c100d2401c05450f40c0011030200c030f0704103040c041002111180c0900170980c03014207807007409844000a030115141d0751845490403814183c00010403001d4400c0b03c4d040b60076400744400207a509104840824840002d0344403032442d4100034410450342d030f0403601d0407005014010080c402c5203848031104001c443c0c14002c49202c0d81d075503004074010504003401d4680c0386034000d5007040031900044066025280440d248e0301602100800101603090032030b00200800400382000c4502500c0040d240500480241000381c1c41d1360030302c00c1c802c03158280d02402040e07222282d0740c40b41c001e00702c460502c161003001c0e0041d4041c0000b000f20101d0b801e40e10049494208440c0700050301d070303070102e208100300c1d10924481da4a500c9150052100a8001081c05580007008561241280500c40700340815040c0d2880511815582840b0402c00c01003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145383741 1250 145382491 145382513
    0x10305060a0515040510150212030a09030521040c091b030507030e0111030105240d11070602071506060801051509190f0602010b06070c030807020102070302060313021f0c 75
    0x82201c0400c45034540010070105c07082100c5010000418000c1007000e40d21003200c1846906803072003d0440303400da0102802c190f02c0080c006110341d030707658075109050501ca0310503140c2260701c1c44603501012644030000d0308082c0044c1e8007500d200000345800103030a50b583c4600004500c0c03a901405070540c81a10640042c0760040034481895103420801c400600c0a2081c4183c80082ca0b000707507141d50409090004441681c135404d20000000303180c00e0005004202960040d01050344003181e442c0e15004480901e0041c100010a210f00115201042011442c240d19054000c1081003004603500e4030115101c040a120b9190032500d4258581c05a001020003071090450283c50f022142c0201a0550302d038004690019003104a4501d0900280da420b0040104800d0102c40355410b22086849911005507148070042030b034000002c0c1d800459000b80185001950000c00740750303c2e840d005015000c0701410f114200e20642c0c40024034140d01c1c2500a480003103008543d00c1c03600b032000781c0d59078a0f1001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145384991 1250 145383741 145383751
    0x207110907030f0608010603030e030f0c131e0f0f060510030b040219080709060806030c090405011407050c01180c05060a11061f270c030e030c0703020f09010305060a05 74
    0x140c44100701200b0311028000e104c024041d0344c0c0000391030f51450074002c08060519074124400d81186100401c8586c001552081c1d180d01192080141001c1150380340084c2001d40540540303c1c445000c4803c10521548000e0380140845414000c40079240c68001c100c8400c6d0046aa102400003c0c180301e441c441d90000c82d0b0400003400041c6032402c18910f071400d4040043e4204001103201040104142d03000b000c500c002d1a16080088a80c141040060340700c140541849000e40300c25800281070003001d4024040c0203110044100c007038241401e000b4400c0c1d100c4e01c08200690b091036600c40a83c0c1c142e0710002c90480d0005102903003941040700300b0046600c20407014080140030605410151014420a40034141d0042c41d003c0040c0d504680c042241000e83c0800c0d000d0391000c0100c0c22807290a060036039a82e403c14800164411140416001000707902c144450754030010074000c1aa613800201d00060740c6c02150790003189001c10040040000e000d0000078080d03008900881c00c5520190000742e086 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145386241 1250 145384991 145384997
    0x21c02030903010527060c0708132403050702070819080708030f06031603080a0f030e0a08030915041703040305120906040b06030615010c05100603080a020c03010207110907 76
    0xd0030340c030700090941d1015503e184141e00c0c49491880c3d95048203030384000f804501400b81c2014030344079958a00701e00641c41c018081d50f40018a006c100800c980e851400740c03807088244e5102c22640e0a800080c0c0048494040c042450f101c0440e11070f500005250b0100e440b0000100940c00e114100110307900034a0f18101d0f40d652007848031400081090020350301c5401280b00ea0101480d01c034007054940034005070a1981511041e40c180702080034031f41142d11495031801c0c082220302860004500a280c56050303550180540d0780c00c4010801100300850045040c3c4080350024070b00b140710065079440544000304100030071500c01165100a002459025003e1b080c49418003808130261310b19900c0842c0c10603c5031304a842000104581030043c190401c82c01c1d0300405a9180c825880801c00e403082d6015030601100801e414204841001390000780da01e038200901c007560b9030b460b1246c1541c001c1d2140c9405401184003480c4141414403e460055070003882032034030314070001d00740645510081d00da2420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145387491 1250 145386241 145386247
    0x20d2a0507030803180705010806090c180306090a2102030301061809020a120f0614210f0705030f03090306040b070201020c1b01180503030d230a050105011202030403021c0203 77
    0x103d4010f802540c07280c00e240002c150002004a110343c28989960801e50501c045102481001e4448680095004584900382582c45220200c07135042d1800642c81240d2500c640000c1005602c0041030a481e0548922100040c0d80407c08119078018031800d007002c0141d000703000420005120b804451041c0d1000c05180100715256072135a403d90380001e40c82030119194208440d4080e03030500c904020000080c2003040000d00b01112a10403d100a18007449410002c101002c0d04002007840055480d00c1000c0b20b00d501c1400e00302c90307102c80491040510034043c0e90041211118007000700c40010780010042e009643c0c6559900c0001d84004c0c0080d401c42d036082c0402c0303011003020407042000780341544440784481c0c2100c00042c2110300d034a1a02d071721034900d0070707042000303841c000191104800f0010300400d115440281c0310081001090030310b4605460502400b40300c0c4120350009050300d4003aa118101d070a86000440280c0c441905c0050050b0f21608000d440c2c040c07840b10300c00211500d441944c1ca = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145388741 1250 145387491 145387493
    0x20c0f0a0803032d070512071106040305132112020d0203070803150d03030e010b01032703020c0d06020c0d0c02030c091009020a030b03061b0f07080403020406030303020a020d2a050703 81
    0x3c0c042c44e08030340500226200080c81009400001e111aa000059142c6000c210317070b080d80219110407000e44010305011010035141000c00303181400301c02820030510036032182c071024103580c004510461400d4032150103180c510300c01d00e8400b00389900a05030300e0f0019482c0100c1513462503015440100b00342e032181354604034411725581d4095460552400b1307540104a011009100340e003100d00c13003144641810310b0301c92128a050340d1070108446200075200c02980c000002c2c18164200408503010581c000781c0c06500c44c04010140d805014085940000c880d0302c200105c0d0161000300c0c80d141e002e036055000f400c94006514200c080a41d10124544180300e0135a52030001d0402e9821000340c2c2c4001c240c0740c1035114160304040000741d03030025440b0004d002c421008150328810703105042800780210400a119400d0000c0001150000c5502030810401e00341d6a040080094001903080d100600820849505092040e10705049007003080c2c00b2803001844445928000f107513008802c80700341c007910710000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145389991 1250 145388741 145388821
    0x12030a0503041e0b01080a02010207090b0a03030333170c150304030e091911040f03080d15060809060604050f0a020702130c020a02030708030f0409180203010507020c0f0a080303 78
    0x14000e196000003402d201f0b00c81e01c000f9052003c6600210786243c54010741600640d507500300002181e4040c07c001814200ea190f1170402851440244802540c105044903a4a075011308428115802e0368401e0ba9402a4800c1c80750b21108980e50700b9503c03403010644e203541c400c080e07002541c1113407103410204480e200e0340c404180003050480b003101e0240c50f60310021258501c0d80c0500c20451509012040c5040d00709041307840d1060250002500003400865054444031031a03110034840c084008020459695812004020b81c400310350440c1c0da8011000803503094200380c011203000710b041c4001c0003c903a031098280700c001d40110317400b03980c04040b030030341d020b4940040c0c411412080701c00d034040e00c8005030394018145420310680c0070109560040218203070f00060341040e03406991a030080410b0001c006246000d03034000c0042d000c0d6141d4030b400107000d000d50b000a02195a4501540c00000b88400b030030400241ca04c0c41d11441c40150000c0000840c8004085449003543c03001030483c2040312000d00c025 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145391241 1250 145389991 145390013
    0x120c0806041e0f02031005040504051e0a0c030b1503060403020a06020c07030609080301050a0503060f1b0906210a0c020304031101050f0a020703051603260c011a12030a0503041e 78
    0x1801000c3c0e030005c14801868401a80c9101500c000d0303d050107a414159125952031000d01d083c91142c09a107201440070010501082c0c00d503c0e0000e14a041c0309032a410210100300c001d8400d034600d0018004285c0d22411301182c25440365405d40c000e489034441d152548000780d881200c4c44282c0340514140840050b03c2845420480c40c0180c0103541c0780c2d8145828810b80140310b8025030720980c0240100201d0540c4001580d50000d165642220b081a8444000c92a401350b840183d034005000306082056180311902c144030719035011429041500c90040c0303102141c0b0754510400040e00300700028804215409801d0850b0786040c50054030702510040c00e0710b0260056010b48006030400380d020818000100166501c0d50190b40781554021b00d11350b120203061494151b0305c450a289070807004052038680d0281d4821040140092029020b0b032032803040d8041c40d40007420310807910000099070100d40002540c85810342e50b03d985103562640e88841e1408056100780c1450b000318400001c00240d108124 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145392491 1250 145391241 145391261
    0x20c0a12110312031b0702090a0509070506162406030b010f0f0b0406030513050d0921030e011b0c030b180c0a14190b030403120c0806041e 61
    0x100c00c00d1045503160008659005404103032080d400081400744003a086012290008408202c9003061464410700c40e0442c05800fa010b94000c01c42030410010405075040a0b104040351000e81e02d020b500c036001c100c42c03401058401600c0c54283c06884e800030b40118003a411103a80d498680300352408140c484001d0f02c0f0550003c0b0f4100c120708004110302140000e40383c01910107040d103409050b0504c8112000360040c1d11400c810103441c0c00120705d01c400d4202c41001c1d00d82c1c100c0c0680f549604200c034094207a035142c0c46020342c0346005c44410810400141040c10400d98141d40355501c081100c001103a40480d103080f13601000520401c01d5000580d01d012140c02548164025140c5240240d180c121100301c1544042403500700501c0410300c0e90b954003200d030a40f200c2c40c000d14400407882001c5150040c58011803080402404004254030720904061440745100703646410710301c0700000c80113041c0d0b9113010402c0301007598440802d1141c40c2c2034100300c10620700c0609055110007022088400c0e00c155420b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145393741 1250 145392491 145392509
    0xa0306050303030c0c100605060a300c0e0102061e040510020301030605070806040902030d05030c12010305010902090702030c0a0f0303020d020d0c1112040509151201050f0a090819020c0a 82
    0x903217100d40800a0015540c1301c001c40c6000c1002c1460200800c03280c1c0310700c0b00500d040008200a0740301e1600d1400d0f40441c3c80f8102c1d8510801d010041911400401c807134181000441c002c0303070034012503600c0021000d03c1505c40a14228040082490094203020080c0044501d8054003103108405203082c4042e5009601440c4041194104180054103141001c0d201601590804d842c4401503103000581a21076420b52030f05680c0e80d40c48120301e98160003003c020202a044060000040c02015000308106600031101001031f61a08036080c0e0b524402c844140b1000d4020030f10003408181c0c0c010010214038000c0c00c026103440d02500c41141241d1101e07001007001551840001c3c03645130700c4210440a61a40d20080c001c000040d4001500c0c1d00641c444d6900c1117000700005032880440c0046a44035041c06030428aa02d1503940d01d9502a100c120780766218440030900084804213240510a0415000000b10b4900500322418503a03000c2c59203025000e40c4982d14042c03606440b038030440d000921941ba = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145394991 1250 145393741 145393747
    0xa111602010801151d06040b0d0203060f010512070c110406060c0c0504020a23090d050718050c07110102071a0706050a0203090705012109060204080118080d020a0306050303030c 78
    0x8800586001c4042e00b140102c030141401030044d6030b41102c150500b1030761a00304000c3c0c0450f00720004486d449070381c00c6507007516170108518040900d00c1d006903001302012220000440c1100c801150030b07010b24910340290250139804907044a0107080b110030124054405a003c001400000c2000d441c52903101400162125010100780b0074000032000c09817804540c2580350500d82d1100a041002e0418090303400d1107800c28a00b80b21000c2011503c10308409031000360f42e13605904041c1d8075030420788200c1a03850700c03d61100c80714107124442d4a104465100034981000c0c0c0b5900c401c0c1d80540c030210558154400d0350b4002c21445c058080c3e103040d140c1001e400607a552414502882681c0b00038068000d000d0051051100d81c1c1004603004003512020319040c44070f0700301140102c2044215540903442203141c2900c600031300c8125002041900e0101c0004e0107407001140001212102412000c0c00c200c009010801a494107500146010b425516000c02d4440e143e80c0020300710381c0190b800c504410000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145396241 1250 145394991 145394993
    0x6040201050910121a0f03010c0509010e0a050a0303020309090907050a0306050a090b0a052e0510020718021b06070906050c070503030d09050c120c10030e0a060e120a09030b0a1116 79
    0x2c013110351b12954150001e0081d10a00c80015106025881c20039040c00312002d0710230100d496003501c0300000d110080c410387d540c5689080c0651258004c08495004640042c009681e1010006030346040300c6028045080301482c5032903c01c0207140262030500031940700c083c080003003034020443e507019180701712000589040010551248080100e5000740c5516103a03c80a862202d016166040b84d0043c1e401e0350030192051803c0b410f0414580024200c58095400c074421980a03031b026007400c140b00341381c1003103a08001c035020383c1c2d030b035001c640c3c1800050b4000c1080c014a84118082c202e090389031001c1301e4007640c4440001c1c2c01c0d074212031004941107030b81c1e0013000140b002c01c02420611071016107000c4030403502c00e0701003611406501c0d203d0707004030b2601c3d04011240740b09034007001580401c94169000b0340003a1408074090803000e03d080d0400d20803440002000c070704003422250b030460942c03940e40c40d013841c45d13507101e807950030062082d243d0a55850840480c402c04500030214040084c1c1020704100103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145397491 1250 145396241 145396249
    0x12060d2406120213091a04061b0302030c0a030e0309030d02150609101202060720040606030501050a06030e01020405030d08010e13020d020607020d120201020a1106040201050910121a 80
    0x1081c2e20000c4511207030300305580542c031100039403d000707624400b01080010076414858040122108068003a0807010100002c0c000d0903072044a103800e20309034868044c03c7e03281c0c04800780e003c01ea4002d00c06800400244980d10b0081e44042d01c1c44c1040030170b4030704010800340041c0c14040c0e095400c0000d0b8018416903502c0c01100072126600c10003c80b2480aa4102101101c4185c9418006d040c000c02c41c0b00240300c00d5503900b0058a007059404040c03c600400341c00e102c2028191112125401b6905040c008540341d4003c0c002d1905880c805450f402c0e1176450303d2000c070043c0180034900d40055508200100e829182441010040302d84d80d1204412540f4044001001c0c103002400740350084590721110005130345285407441300640499515440300d80c00e000007010000d4101d00280706190410b02c0000050f010f4001c4d00e18210381d500c4075500154024007403901c0da10101e400900042c02000b034034099190403007500e074400c4a00d10789650321100c180c18200c21a40e51124034031900400c81205042490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145398741 1250 145397491 145397501
    0x6050c0f030c0c190e01181b08130212030a030209011215091e05040302061911030703021b03030c04030212030702011e051c05070305100b12060d24 65
    0x14040d0015860721a010001c41d440c0d080e1042e00341d01c5000150018640428013201c140c001d041e070410042e4413940d40d007000c1015a00240c61802c41c0904207240c20303030202c519120821400036141c44000c0540d980d82d00303440384134081c1841264816642054910031040400242203020310300d4400681d5803d141c0009401c0a80e410b642c01c204a042c9005549281070081400085030201d00d00400c100c80280b401702640c5105001c002c504614280800040c140c3c0000c000c3c0c041e80715044000c0148c90713000c01a1094686d031a49400d00d003031080022844452007603009000b42c0c80a985000c4860400045403811584141d45161112501003418002d503d0b10004010646078150001c5d4a05009a400640004c03005c03541e031010141c45950050000780070314100d0361f8101c03014440c40c0300c1d00c1c2e0b44036040c0c004210a03240d880029180100141ca0161034a48080a4a054034803940c2400102440c00040d8800245520b40081c00300f410900080c8514884918507103442100e0700401c8008039041e01221 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145399991 1250 145398741 145398763
    0x50d0b0415021309150f0b04090c050706091a100308040302100903020d080304061b020a02130f090f060b0604061d0103110c060f07081509130804080f06130201050919090606050c 78
    0x41044004100e1f4568032011102103445103034010548803011201130302c0074000d021000e840d190401c1c01450401051841c2c200b20140e5071004a121a00e030426805800e52803400010510201004244090b140c81103484000211038580f080d400e5460343d012600c0b000c2d00240458500e070bc04020712041140500511549036000040c600380113200250003962001d199a019028103406841500d0181260b0090310b030905444e042032202c841c040c5001a0304c1b02d4820016103115203480607845039071401c8021907045404a90b00d44601101c003c55164407c4030090099041c0b40d940d0913913040c100cc200020309822001c44000c0c2c403062500542030800f6035002841784081242d5a400c0004102580c1c200f41d1503944203075031070320903035641c181c289440c3c0081150140842d00c010a00290781100003680301001103450066500da515421010b29031030114640080c08124180045c1860382000706003418280804181114960b540c1c6044004039181c40d0031410002d5000590500030321010055408a4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145401241 1250 145399991 145400009
    0xe060108060a05010c060e2a0a0503070303110a05120702120609070b0703051c1b0512010e04210306051207050310112b06050d0b041502130915 63
    0x41c90710000240c054103140c011503062081d2101000c1c240300346c82e03005002c4404208100d401c00541480c03000c0d00d4560000e9000c12040c0220b80d00a202e092005086046490180090021f5420355806841c00c0100070701c0c43d0028031900c090a804030300100003410a00c070028001c03c0d510700140c01446031046406071061000d174000028000302080010741c00080351080c08103241c5a12442c80c00f1a59881045146000d180d00c0012000300c007009a0b00c00200f10f181d4100c804d6681c00380700015109409104144050025079400420402500e041e03400c0c0e106220340c451402d40da135800d01c3c1d002000260940707040002d58926007403003241001041c21482e107264000504103a850440000d1f40c50580300354403201c0301d03202c1340c0c924242c01c607004c281d42111030f6800c15600740c0040b0b055480303021420803040c00085801e19400060f0307400c0c80c60f81948040d40000f1251823594903178440d420b6420301603102c8440280d08104605250002c484140e01034040b40c0008030754072000120400b003d440607081040d00c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145402491 1250 145401241 145401257
    0x30906050609090706050f091f0314091c1b0303090506010801020c0604020d030306030f050105091908160309051c020a060201020903030a0e030705120606010909180303090c030611040e0601 83
    0xe82040004d84400f01c0743d0341e14109a50340c000401170101405030114840e0840d0054985500b54030450080c00d09844450741c041001075030b031058005120405984120142e0400c4500205d0540034211142d01c003141c9003032812110501c045007104017001d504080d00000c1e9543c0d8104200314082c4003090040c4187d40080d0305002c5290702851f101d40020780000c0c401c01c080d150140406001e50010002140c0107800d20049a1540c100340d03010317210403903404249000f95005103070051f107c16065142c1c1600724509178241110240d00035001e600110f815814402242c000007050350f02d0384144106416080703000466141c0f0ba2042c41541c0781241c0150b0156401840341e131040352000002e039210303d1000c1c0791400951010b200820306144094001c00c1c1c00c1400d002103002c400800149441c002d0b0b03420b17030ba00403140303035036040250454a2998036080b00402034030b13211010a2094022002881c0200f00008000c0c0d0307030f581c50f40100e800051a44062100c003003010448220014134142c3d002d40d003800c5c0102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145403741 1250 145402491 145402501
    0x7020717010903030c020f121e0a08040c0e04150509010605040e010b010909051b0315040c0503040302061302061b1002070309032f0907030f09050f0c040911010309020d080703030906050609 83
    0x23450b42c1c00e00582c0500c0e901d020803406201d403885444003126035100001d01d555031205403001800500e080324252000311607503c0c00140403100c500014821170f000a403050030001002c50a2010b00809000c5914075925004085000e5450b481100f1460180360000508101c4243c0050010000c980c085043c152030402000110240d41c15090744030040c040c03d840e620fa664103c04092080304c5108190001d14040707042c03a143d07400030001c41c0180c5c000d4003201c103140d03140104000d07038800f10742000790041c0741808040d4031006000c10350081d0380b841e0002c2da1a03c0c0440c07070055040f82c000d52401d070000b641948082041c4188050242c4a0b0500f91044252068544544054079030b00400d00d01e000e4482c0038005604107210740d000c4800389901c02410301044000c2d05210b991115030200c261018080e038051b00911346801c0c4610801d2907403103a082541c00a082c0010b5009045d607180591f0800070104000c00011810001846403a12a460015203189142400380c1107980041c0034500070700c190000c3c06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145404991 1250 145403741 145403743
    0x90e0603070515070c090504110d0f020112060e04080a0305070203070c030f02010918090201020d0201140a050c0f1308060106170609070e0312030402030606030303060d0b07020717010903030c020f 86
    0x240540c2c9040c1d0303180d268200c1c07294040034244641c403c050020740041002080c00c81103034014900490040c0d690410455072103041107107410094000400c0100220186001035000e4000301441c020401400103a440e174400b0480307003a000880e01100c509600180084a1030b03050f00c05c464210101e88015818484242e03146010704180b8040500601400d42480b01168400c01046004e84940c01110078140c0c1c1e0f00c20840054a1010012805400fa520301c1d02d800394414403900c20040406d0415802588a0713171083d800600303000e00840c0b130681040241c00251980d00c1d000344590135070825402c518038a0121414102103041e040340d0b00300060032514000c443c00040d402034000100b11820952a107860b90241c0e0071000740004550540540d041c035014038201940654490350090f420b84106a5440d420143c0341d2208a4003a0341c4100030001550225044000140e40286940115041c0607151240c6200c21051058510070380d81d11100366608041d0300d07000340700b0640c2c0c2c0c9000419000310504041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145406241 1250 145404991 145405003
    0x60108120f1c02040b1c02030c071707020405070f09060503060a031202010b0301180201030b0a03050319030f1404030f2d021204031101110a050a030c230d090e0603 72
    0xd00880d036002c600c0b00102c040307200110303280300d0702024119662075a0f8004d203d0550006031080041101010540c10090024000c0741e220707400704002503252820503612107903520010340c1590400e48090007410010384441c8134007409500795445d00c1102c1840c2c1100200060b8544d0806001c0010a00a205203911004068419a1f0f48480c0c0100741c5020340d50704a0040030a5118260306600301000240c49042240400c3c90040c002c1e0390038400303240752030180207090050f884000e02652041024a501c00c1c800c80e41d5018405e15403801159403050051002c0030341c1c001c2c01c84400c1055448050004054000740c40b4205a04607003030442d0388074030340c02070b2074090090501c0030029201c82c4480201320610034448511041003103158030b5111b50300d9041c55042040c00781c0640740842c0c070041041d103d1060010785040959441070041807071010681c0d045603d504032400131102010703100d0b0a00c0c02104003032a0002400351410047c03030480600440144000c0c0380e940706880a400910a015240c1c40101e05 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145407491 1250 145406241 145406257
    0x10f0f0303020309040e0c0a180b031902040c140705010204050a0509040309031e050f06010e0903040b0304120c061d010c090e04020f150d0228050a08180708030c06010812 75
    0x100080c1c811846c0c006606140c8100295a41304110031004260b41d03085580001c004002000200000800a000d244e950b98070204a01e9500041c00d03103e10041ca4190006081d5120910340f005038800b0036040c540c416009000100c030340341d40100c1c0900803820400340110080a00302c4804456090648000d040300702d080c0805444000b0040c2c4aaa1540364842c600d4090381d440340440301d106060302c1e601510344000780950440001504003040c614900001654285c6034600911491a00c8590700c1c2c16840341c224045005100d03007000c2180108443d03119022000301080702580040c20150140d6007100c090b00d50100500c0148801030007000000008217034825810344001d0258101580000e0000107014a40002c0c2c2d500003c11513003814480d00a081c044907000100450800741d25280d1281c51210140200054018003045070071a208000070b0360090103412184038900d16241070302d41410001d4010145660000500300404c8004000310388c01409205d01a040b0041d0440b0001594866019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145408741 1250 145407491 145407499
    0x11040608241c0c050303070b07030c0309020604060201050406050709080c01030f0b060703180e0408093007031a01120311030909040c0501020d0f08010b0a0504050301050f010f0f0303020309 83
    0x1442100520340030802401250004111002260010700d2400c03040020442c100c1d03c48154000000342ca0a0001c00d035100c140c5e106021700215514040114001c00341d141404041644540f0a0005621001d00070400741040c7d5001040c40e14050400c00c3c01c0d0307000902160108000c0440410000c0710204850091031002d00e0049840500a00ca403c007074542c0c000020340c03001c030019100c0109900900540b880d141e8002c0c50301003041c0c0d01c0451a0911008940c0034001581c1000541083e1410401c607100c801c040001018402003800d8424605d1802c6003144400d603441b004061003803140140015461900f242e040c20100d40c184600c03502c44c0c8882410040900c60f440104c0c90b80220f080c004d40d03605076000740011541e4502801c084c0c086004611032603000d400348060314850540714980d42070052419440d1b455407a483c11184100690014034003404100c4284000b2035a030b5000c0c05028001d00d468290b40119504001b01c58184015a9101c0c0490f41050319041001035000701c195a503a9600715 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145409991 1250 145408741 145408771
    0x50c150d05060d0c090c090f08060906150604030f02010507050601030c0f090225020a0e0403030b011715120709050a020a0e010503130609060603020303190e01030c0e130b030307110411040608 84
    0x5102915644c02d581c229440e4035500c4407001c1600711000071450f1050848908433400c0d9140c140c441404541d0304000b498100710100024000b00d080520070581d614418903089240205e15203c450030010282c004882d1520051410007842000c050761901a240003501149440701009142250110945103110311002c1c582c203900035580c0d044078a40041c101580743c82c2e09031409180040090661008440c007292180d0860041d007601c40320964401c41c0f0103ca4001741000340c00c2001a40f40010300c0138040c0c2d11a0740d00100b00256140211401240340c49409601ca166454000e842108c0d001001810840140b040180400d00040754960b529080100020403400d24100b52001e0403403501b020b034152100080300b40c4540d1914050405194a85e60307a042d130060700000445c1640c140d080c090740040d0001d0800c00c51480e21490010500c2104030001078801d00341004a420341c1c01c111801e94110200194420403420680100d28003120380c0c40e00c203407400e401d004004d0715400025110f1084800c41d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145411241 1250 145409991 145410011
    0x70e070207080a0f05010507030e0d0c05030c01060e0612150c0c0a080a050a090504060f030813030210110d050a0504120f0b010f1a030121050c150d05060d0c09 70
    0x1d01910000e08084003e443c98000942042c42d074035000601d0840302d6600c0d04001800d11441307440781c041c42150450180c280205811021a8003110302c42d810b88940c00200041220050240325480003001d110f03a2011152078030408210009070260090744050f007060010f00c1070300c0d10200b6060741c0058000c440c070340c4078040c201c0b20a1a040b00707810000d002c400000750702450950040c0103841c50880b15616150300b152502c040c44180c903030307d10407001c810351810400e1000a4084011b070541e8801c0e1100c0d01126540c940000e5025010420100045a15040711040c0d202050100c01540e503607500b80185031200c9001d00401a01c0780c0c0c422400c216000004480410010348a840306881e001002846107584035007210b03111443d944078000c15100300c0c41c644002d040700c140659040b0f0701040d4240320710807800c41a2001600034108216101e002d110210501943c0b20f21800950011070480c00d922040f00000803011070704c0140042c3d01c5603441251110000d13207140c9406080e01c040e020080b4013880d01d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145412491 1250 145411241 145411243
    0x10923030912031306090509070f0e040b01050702180f090f0a0809030a05070b040815010b0a030b06040b0307080a0b090402030c0103020a050d090f05120322031b03020d20070e0702 79
    0x1081402400075804e41000109140c0c0011404162402180c0c84071141d1540c55003581d11030400c4100c0008501805101c3c1300b5071a155204101d8003106050072440c1c40d40540c0001e950724260800a0a410008014011201c1c2c00c030003150792249005008100c15098210030f240d036035035941c1c8010300080380010b251b89651428010954142d80c4001254411900d5203400449508140101d0100e4864400900400b00312415203504031034032444014a03144803554120064a0041c0c0300c3d64000608100006603400040c0046100d00784544e0b464440d810700c840c21005840b100004c0901c141816030a0101580c0e000c07424000c194401d00700140e031031045000503280341c0180d8141038405498440b00106004400e140c81c15554810029108450303d804e00324040ca01003038591081001e070045c0582154105000103800c00c50084c24107000402c2d007080b01c6016012044e10450050308107186130a20150081010320a000d0003086c20aa401d00b80c02e002342d9070310f045200d050388400000020401c0140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145413741 1250 145412491 145412497
    0x40918050a080319090c08060705120f060303040305070905150406060807082703041a03010f03060e010204030f03180603050108190614010b1206040c05120a14010801092303091203 79
    0x40651024003841d422820481e1541b2000d11900c0da080c05800c00140e4483c0c03151085a45200101e01041c1054032000b05035141c460f0001c00d0306400d480100320200218070f00300700300b0004140315403011800385413200780f003001101c101e005940114244441800310503004042968440c000b0b140c03003c81c50780c8995104c00900b01000001062205803141d0282003500840104280c40f081c1003d42c1190411581229151000340300319030381d0701040c02080c80003a00d5904050480d481c101c00142c01c05450351600610180f046100710b0109041405115045544d408500014075440c1010007c0c0e40c54503040c0f948810040d65803004518559100000b0060943c0c040d0501e90140780c4270501668451f00031000f140d002003100b50700d51403654005140ea14003800f030401003c15035030300d00b400e00d80140100300311400007800100d481030301d4032081100c038805036280f5402000880c0c00800c2030580c50524541041c003010850100508241003101c1c41c10001046803001d940c2a00c100c00c07561a1500c0c1c3d541140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145414991 1250 145413741 145413781
    0x40f050402340b070c020102120702010903080a0507061b032f091203030408070506090f10020f0c0109050c0f0406030b04020f03070b0d06030c061803080a0c020a0b040918050a0803 79
    0x110100c2c1444519170b03201c001c4c4a0b015200707800700c5112050703a8480002e0703805040f4000303000486030300d03041c4009502d210160031707010b1550810b51b090041c940e65000984001100111040001030200403200b6810b02842140c403009a46010f007452001e0703204840740000c1d45120031513400002c2c01c1c14090b15511a1392a000b0030007002c0d01d45a05243c64a101c1550003040300340c409101e08004100101d001041110302c0182e01d0b8002c120007000c08000802941101440f00040c0340184408c0200c2c0300700780070325440d00d40300303001615002a24404004171a4204000e0f00c0c0168078003001400010002c1c01c950f030b007003034040711113040e24420540007c0c41c1c02d50a82125140e5203010803415003256640c0c00c5001540d00c20080814400c1c0c1b10441282e17030301d10100086419410720b6600300007040c40080100b5044a19180102c3d000046402080c1800601d030702541d448000001c04210310249071080d1483c03c520006048590b5800d5210290b85110b0050058800b19002001c200a030080000c620440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145416241 1250 145414991 145415003
    0x1e110706050405010603060e0601150f091706040507270e120403150f0c020a0609060b0a0f08210a0e010504031403090103060b1c09150908040f05040234 67
    0x500e860f10300305000c3c095070b1000b00d541ca0f0510702c140e0401c902c003042d028161200031841c00c3c0189031003a0210380d044880194142400425080442d01c2c030281d0000c1100b901c0a10700400c1d00b420540303001881e01155a004060b01403150b60754140e01c1181a40111981e060300d907000c14030b143c821081d1814041d1503510005000800600001042040094000c240107481002c200010000003c20305580f801c1e10104016000018400c00040f15540070b0000b2a0150100050400d07038400403400707807152508035140c0502c0c0d1901c101300303150003004590058051045001502c0c1c1868013240e5250158071495018421004460925644900d0039500155040481032420510300c031001902c96101c40071083c00a41030403070200f607800c6141c04807000414a40b05a940c510050340c4000d00418001c01c1c100c03030881e429090000f440d18980181e65046002d0540c140d0b603603103070010404510f41e80c1d5010600450050004590001000c0501c1d20310002c2e0726005658260030720008001244c0d4090700400c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145417491 1250 145416241 145416251
    0x12160e1f060f030c02070e060d0609170c1009240f0515030607092702070210020c09010e040302060403052203030809010c0804020a0b0913050901050610031e110706 72
    0x5580c000c2e10703240c080324940ca04000030b503040300049840d01400e000d50310b108000e110104d030907400d019041101c0c1d030707020396000100c1071011703550019442c0c1d211200e81c4120034007281e4100c101c036060114031203e182e114010090280d107651005482e14941c881c0c44100d0401010411b03c0c4409a040030441c808402420001450b20340261426409041001c900a1052400007000540126620810740303001800d041d45111000d115032100114403920140030740d07001e0100c3c01c016240c066065000001d940c0103001948403d80921240202c140d01800343c007400f080c103001c00f003500403070304507017094052500c0d540e036807040d00c11681c0c122844a0f17003007404d40368220004113141c1d0010010340680e80350710080c8105a001041100c00c1c00081d01c01075884107c410040220300d13009001405845000780030100c6406a00d090070040381c60458140b40b050351070b0320402000749000c90200300ca450342800c00f00040707044e00c010110880f06107002081c200740c0e503012054140001d4001e9600c0e5039400202072003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145418741 1250 145417491 145417499
    0x909082809090b0a03120e030a0b011a0304151d0a120306051002100213050a030b0708010501110a022103070804051504051509010504120f0212160e1f 66
    0x241680d008400000100c5811022031840c59500910691550040c000c0380031a007580c6030541507101401d141024001010400d6030240ca0a00505844901030b00030000790358909039004030190950320f0324146843c000c0003004005810512442c10b071508004d0005000062040d080019207050041a4114840e03010074000300002c810000b00d030030312117503000d001003540c620501100c012092018409030708012080d03503800c3e6907903001d003140010200c40009825030b03880c0828404085604156420915841080b00307594020900500403c2c0a1074050f001500c0f030710040e6240c110420f0020f00c200b8001c141001d4513a05840043c508034110015240c0d60b18241c500042c2e6a8010310600340640c94614001c1441207408040c2c400b1100c02600301c60740c1ea05180d0300e4896590008046505004003400042400150b0440d0781000710b00c40c0710403c441c0c074454010001541c0c8000340f007018561081284007207003042240e66204542241d607401c151901c03491803506403204414036612110703040080001b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145419991 1250 145418741 145418797
    0x709090503030405010608060105010c081e0a02101b0801091a03032205091e09100906020403020415080d0e0d1506030c060302040b09090402011211030105041a0901090908 75
    0x140124030139402000301680d02c1000c29141c150034400d03240410204951140442e030780100a040750184803041040c0790314a003401813803e070841101d40c80140c0c00290071101080f440d215892400354902040c1d45660110b0b01d000f0585281405903001954a0303400e002c0c60b07c0d89a94103c5001900141940d480f040d040130f00300380b940c6100e80385102d1020140f900003090300b00aa485030040b442c50440600515051100948104000e040c0b40b81074422070180f00288403c51042c074008622500002d42d80f14a90f0040009032401da42c0101103030240c0a004001e20350740000c00c00034000c418144180082c1000000440c50385d00820040d00181901c400d46c40e0054840c2e0250080d24420340300c002600d62200003c40490159002da19050a1304010184083c5403000030140d00900c149003140055548201c80341c1036506c681041e030481c82000c001031001e807800d0301034944680c2a0a404640091980c4000b03010001c043c41209a0a42d86030191414407404001319030500c4034400441c000c2c030240144807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145421241 1250 145419991 145419997
    0x209040906020309120c06070c020a15020a120302130905090114090a170a0509150f0a02060709121e030504030b010807030b060d030c2a08010506190303050315030709090503 76
    0x80c5118080c4910040817141d07501d05556911030a1706c01043c00e0f9540030003d507003002c00a003060340d03c1044800e00042801510590004a09255024022400041c45c0c0b840d01a401101000d00307160040c4034120034004e401062400315180d11001040d6515011b00160041600d504a404088103400401100d003e001a08a0409100710344410101000c11000c99043c014000c0140001c3e004101c100c4491900c00d141c41d40340e00806811390702d8110b806005144541c00f441042001da00910100011a0303085008200104801d00c0000044009580c0700f207034407110a282d2000c1041e1031810881414441c070199000355078000c03080210765858007a030700e0780c900040c80115103401034400010300900301a40c9400c08140d050b103401c0039845103582c400700c42c0031144074092910305482086040c1c0c42c0700190681e0007010040d00018150a0110902800c4840011107022a401509040000aa008040700d0781724003100340345540d080854001a051045a9029000850401103d082880340110007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145422491 1250 145421241 145421251
    0x190518030d09020909010506090a0209010219141b15130503030a020a11150f070f020310060302090109060f0501080406110706021b0a020109060c02030f010504051e0c0d03030c020102090409060203 86
    0x13900c0341c03070f070f444a004d02c6c2664812503159401a40817030205921210301e40240000c80c105006032006690f10640c03285d60300c0a090400c0c0c5c0c001d0101404038890b40d0301030000000d1078038003030305140300c044114010a0003048802c5000c0441c10b800140a0021802d00100d4005014006c09a9a85c7c40d0fa0302c80c003d44d82d028000c0c0a03207907000400b00c400d20518100154101c00800c0320007450500d04001d41207119900701c910241d420740d100c0c18191005a40038070241c00030b10101e2000091071401e60040c0054254141c105103c824605203040c4090105107565004942003440c110145595034540300014005403801070303581c800046000000c000c95a005002208200311030354014100114500b03541b40210381e0040d001c10703041d030400e000440c8a51110039050740007a0407601b25030081c0617a1403c5803c00c40d010703140da4018038001303500344201c252203401108182006002e05c203400c00009492814080006050540c2c5450301c2d40000c2c000e406560100c20300030820403101040d4103007a006507000b114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145423741 1250 145422491 145422499
    0x302070e0f0103050a0b070e0405040605090106060806060306090709090507020c0f031b190b0708120c07030e0105071401020309070f0801020705031611130221190518030d0902 77
    0x80d030400c01c00c0c246034101c0b90041d0003007000c01c400f038075103e480020203000300707007000401c41d04809242c5440c021140074901c603080001d00c5213031444c010360840d246071b0849810050220300340070040d5160000c0c1e03900f02100300c07034600701e50b210340c1e2050b00c1000995020702c0106040c41c0070020200c0d0040f84c1a1100d4005a0f01d00040740b51483c10542c0ba0340c0c1c411000c030104690728105c80001d04040b04102c80d45201c100c00c0f02e5000f0f4403207591030026040034100f101e40e100d001402c10580c0480e00c0300a80c121031007842c0d0608111959401400540200d007010703041000110b007000900c8407000071120015003e01c003c40d500d040070403a160f107404041c0185090114080c00001710b035034052085500140d0804051414a0007446490100d405122010b580040700e51210508030f5490041e0324001c2445900c0040e500c56845440201d1840e0100c0d80100090040f42000004152100951100148414001600d6071190403144140d801e2840c003112600c00400c084140c65003030b501c450302c5c55008031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145424991 1250 145423741 145423769
    0x408090d1e110906010c11040209220c03050c0417150f090f1c0302070c0f0b0409061520160b04050102071707061805090408030a1a030d050a0c0f030207 67
    0x8082c0f000141d401d480b66030020310301c22a0400481c035603200421040030001c00144c1791110480020346800ca61228042054001d4110401040441c1c4078a0740010fa480c103040c865864038211000c018003661003040d4041007000c20780e21920030b0500038292900909841c100301070034000c104030000320f4201c8203000c861042e25810300420744002011403021050001d501050740c5454000c40180d04072010840300c1c811440300c04500000b00e41c0850019224140b0841d03252840d1514040980d98268403039a0100031444e0320074202a401b804142c0380c49003001401460f4500700e81001c1c6441038000c3d00d100034141c0705a011508203d140f00620440398240c1c2260309090306c1d440302d01c01d11810840d500a041d8400b43c0b007085414080e500c1c0403401100c1c0041c081800e036030b0f030020034060641160b007103881003000010001e10384240d2041d01d102401400c140e10110982c03c02083da40c00c0b4048071101070200100b10b41001074030804908803960342c814040030046803d40b50103556007101d030080403c880a14 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145426241 1250 145424991 145425023
    0x30b0f0108100b0906010e031005042402160303091112070510021606080606040b0c0a060609020c060604020c160e0f061903080304060e0d090302030f070e0408090d1e 73
    0x180c02611100140100316824170b48885005403150444092080d4050144a0b54800c250540d407007103902c00e0740070309011100981d800200d1094100319114088a942c41404800030500401c0c00e081580c90340340c00c4c0001c9103c51820021089280680c44a40c001ca00c169491460320022070310104540058440c0c20085004d41c0050381c881040b0410171400b1724001800f0004948034058540d003110300030b002286029110055040d403684190380080ca590300590320b100c10888284141b100800e1928401c6041450f603101c1140c5038200a01130a224540200b0900e0696006101c0340c181d058a064600300703040e969001642862004079000182c0c46400750000d0070034104509190811140c88400122003401c5d5500d898164001400175207240c0d076610501038443d03d041084003003403180380d01c805408070b16620415182c01480c04503c1200c4d002003208120b08502c02400503006940f21903040d407900b1508001c90072050f90448041c00d191000301d0503400b00d48501400d12021030165500c52807001c45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145427491 1250 145426241 145426273
    0x302041e0f12081c02070f0606050a090c1e020705040e0c090c2d0d3b1f0207021908010b030307110906010c0c0f0e090a020303071b030b0f0108 63
    0x45441c0a04100004c110149000072180c07018254041080401800e020203900c0f003c3e2440280c0d503007201c1c17895a40200707008500e4001048401008010804d1003681c050040042901c542d24800d40c071750304a000a608001070081c040f034000b4010150080199000c006c1c409a910640c008090f8080d8108030085210503000380300b240c00c14580014080b1000740c6c9030840b18129540741079580d9404109212074000408603005e800c0c05000320550100da14816200c03400c3c200343d071480c0c3c0344005c1401c0240626200c100031410402c0001105026540b14081d0f48903070000c0c0c0b20301c0b40c00035842a00180c0103d002c02000f81c9620035a1040d10003045249185002d0603503d01c200e0342c0c06012406124603160702442c00959007644101c0c10700d0b241c0f0b8100c1c3d0300c2c1d13103040761000160400220141480e00034003070209001e49055024421a004055a4015801090301d82c030030280c2c05441c1406014141512820034910180110383c018001490b41c54040708070540100280606101c40c003560150148103d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145428741 1250 145427491 145427519
    0xc0e060909160507080307051206091b090103020d0c050c100608100207050307020405040803060f0108010e01050118120302030702122a040e010e010506120604051b010302041e0f 78
    0x10107480986aa140c5248048845890505038000c202c0c0070010f0600040b6540082c1d4000c0c0d4490300e0b02c40e160b00c0341030300703562a41c07500401403401643d00c0000c20003025100c099282c5031043e0352b000c1035501c2c014000100c1c0644682101c01d60b4081c103064154441c66405002043d100e0b0a14060341c0c1e007881700001c0308050751510702c00c101e0240d2200410a0344400c885c0c0c01000a14456011240741524039404503083e0f500498058401c404080100106402c0601140605040074600880c0c65810b00821100142040c05900c0c10001c01084045407052851580030142580b441031100c00340e03040c60001d60780d0b03204200480c090200803160311000c40001610501a40401c2002650a42d044100200031840340f00e246a1040d101c007069601c490302071050760301c000151000441e05103810010701c07070200da07101e28905450b0b100c20108004254045400c6505214110f4121141035030840101c000c0d000340d42249440c000721011a02d03040741d007044800220b5416080d1030103516520305070851105 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145429991 1250 145428741 145428757
    0x1005180c0306060f09120a0303051303020303130218130203100b060306010c08090a060c050601080d170a0b0604060305041104110d02070f0803010f030c080105040309090e10050a0c0e06 81
    0x46030038030102c0ca5500d010800750a1400d081c90b034a9017841000b130b0000b4508100744032000c0503a0810941441403660602a150340403120f8440b00d841c4483c1340d03600940c0d0f480700030000144c1038640c4040340119520448200003c8a03074000310301305414068a0f01186005c1104100c4c0b180c07003001d10040516540b03004482140500420b03050840e901c480c010345d1030311140032080b00c0740c1c1d00c100300103c469900c002110340a003c455840042a1002b071508c1458010182c10810343c0340d100411082a5581c030a21a025040301d069000d6a50707111924820050050400715070fa0004000c0382c08120b841d81039001c0e901c140d0003400000403644076501400110341c82482801e8241404021045c2c055002c2d400904007503100700f1080f00001810f807581d0a07660002e810a0a40d1100407204000348051a00564068803401000300f280f170410742c0c0c010f07207040c02a20400d4501501c0d50014038034030006210909020301c8400d014400ca241248004000300710004114021070401010b04219040c0113040e03d00309 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145431241 1250 145429991 145430011
    0x115031404020909010905010f150e0603121e0301060509011205011a0a0e040e0c09070905130906090501050f0105030106080c031513050706023306010e03030d0203100518 75
    0xd0349450b000c0c0080c2007002400310f81c5540d203d01e00725000030024400c82400c001e01c1180003484205080c140120701c400c0d5885540d600040d4010b00400c0e07500451b2200c0c04240d0740d035881d590303100e04094800c049042c40f078030a10800c402000010f003164000c80104000300c02603941a0350100340184502c1198000c1c0142d100307803e00401241000c0d41d1000042200309594241601420800400102503841c940b2002032030381c008148800a03400c08890302a042009400d00a441c5800c12000c15611140b12440040c2c040d100d500708003d00240307501c0380b4035803074000009001030b1512007052404050300303108060096107004000200703911301007600ea06080009001d171440380b01c1c0400c10312000ca400f5014554040c02030800a00060301042040000d040c81d801424094041038090040c5543d5140707a01c0d1091010342c41e00a1041c103162017a60310150909006100b0400000402c7c0b0314054502c000c40094130000601c61200c0c0b01d0000c0790300325441152081440e0f040d601a42d0f040640980d4074840c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145432491 1250 145431241 145431281
    0x604020c071511070b0702030d020d080a230a050117011119031e09110103021801030e03090a0801060311040905030a030504051c0f110304080a020420030708011503 72
    0x2514000034802c0000700003d00d48141086000d00c1c0050618401c1d910074070f0318804c001b0345d40007141020b00802e0b03541c04803400500401e80c04810050710ba0b510040c42140e100d5940c3c00c034040030800c5101a903114020083c400d00462804901d0980208000e01600c2030460344143c2480d50490140100189481122126810b0242820422006188284070202455214004000245e180f0014401c0c000284480401c84550310f0030701d5142401c3d50550103040500401c1b05444030740c1182c2044c0c02a040a1030b00169a0a245030500d065000ba0f11b80b2a91141c00300d040082c40240542000d010340e0f010b10368280d00980900e04100032a0100f500c010080e400c1440f4074100107010f6800554441d0007034065800101c174494018024410031040d440c045030700d20b24a5080c190307201964101c8414002c00643c40c05092001150350751100ea000284116115403410350318a544031505884a10344107000368070f074104140c002d05842030034041c0c141c1912081911284d068420b00558150710080814010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145433741 1250 145432491 145432499
    0x19060b0a080402030a0803040807030915080c18090a0f05060d0b06090405030903060f07020c0a1a130b040803220b12060103020c1501050109060503191817120604020c07 74
    0x307065100030000da9060040301c00b0038010548000041d4400d61003084a2641c803240b03450090f00480064014944c1c10703907038a072400400c540044415400910a4207110307142d8000920301c4d00c12481305d510140c0c01030581410302001e081f040e00322030b0a00d0008402400583d40361001d114001508000140c46100d43c88082105428040d1000380c12034051419203203040f8003080440d14242c01a036660b041206004108409168184040e010161045400d030801030702d00710b1903074114000d145a100c215100001c0205081c0c508440070703001003220702062600c03556952146c9441e6009101d00108035031340c00300001108403142da2484290f4903402445800e094070030640b0380500070001c10050506900700705820194404006580c802404884100c01a44c186000109421600c7d40040c1c14010184203000c3c5403480079010b5403200c160800300082c40804041040d00c40301820002800600000e80c0911800300e0010051071000d0344840c88030126119082408128031841a00c680e03a41c106040c188 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145434991 1250 145433741 145433747
    0x3030403060209030f03040f0302120a170313170c0c0604061b02040f1d0d05070305041401090e1e01050a030519140313031208042d081219060b0a 64
    0x210003d0400790803290807001d10f8150500d150301036042aa80788001d0b100800c11072400c603680102c21800c035000b801e40c039242075484d4400417071241c1c01000c0134000440001c600540800300d494040b9001450050030f030b00a01c0f00b40345a41e00c03000b0000a207010740d1070b104205003400d00c200c8040710225aa14590744000703407038069400e6000a0100d9110b030715020708241310103080c09401d405074461810800104c41080b0241d10704460080700105000c0c00b80f100c1c0c4042504007060350111003440d10200e0b500c560450040340d9017115a08410031070200c050500c000350144141101050104000d000240e90f01d4000b00107070400d051000401d40d600440003416101203a81a900034180f0640050005c07184400c43c0030b05540040c00d00070b0318020402410014801d01d02c1d0186000a99030a00f81507a05054a600d820030f00300c02800d0150610003100c9035003001ca0b000032604d00076001180b00781c44580c0c070303811001c0100041d00c05651030750401f0401c805800e042c0c070451044810040100b4a0100078100036 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145436241 1250 145434991 145434997
    0x90109090f03050a03020f0708090f0405070c0206070501060b030702060a050f250309080d0c0201050c16021c02031c020c0307080705010e06070b090c190b0a080934060509030304030602 81
    0x44c0c0c08050b005e0104843d16000e4001803e440c0e441008240d03101c1c01e4540500005414520180348554144401c1c0001160071109441e0310603010349101c0c1e031310425414041d000d40455801182c90080000410004560100b040e80c010882c922082c056615020307407038034001d002030f1007551070a041c045080d04020203070a0203030390003140e9007400300c0c0c1201103896058040c2c0101c44e0307400c0d0a58444810326602075080c400c40d540700150320081414683d0801c458a411110680028000c00c0401c1426007050002d02c401c80c0d145500408407019809055035841070150300f40c1480780076200300b449406d558500420b010003900c038a440109440e030318200c011100c001380703d01a90342050040110002040390039018070300c509003010081c880c0c400124140080d807062510fa02d42c14065020080c0110900001241c00054035890403c980c0d4651480c09401d04100c0000e0082c4024400d10903a40794148201d0001c540400a4541004966490f015a071600c58590055490b400030441070000414030380c09 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145437491 1250 145436241 145436257
    0x3080604020313020a03080c1005250507061107020a05010302090d02150706020c0102180111101a0405070305010303030e03070b13031103040f090b06090d030c050309100806090109090f0305 83
    0x201443e0045560041462044203400641c1d00070300c00150050341035070404c24a51099041c607000c02803407401140031050307480d80c00090529546000750704100b0318441e00c15074482d5a080303401041006e80007500107140744c2c001402280100c41c1504001660741c007907c00d40d864444040c0c0030003031640d40380e801c0020001e410b2a071044e0707102042c044003000c2460341c40a0304508001c1b5000598030580151b40d6403242e00b42d1035036281084481d010a22185801044440c0088100040810403249296601292402171241c203504140351a041110181d850b800080c100c80c06500c04100700c04620400903100e104621015040d8039282c03001c0b81180b00700d0710314414954001d2500014549c642c904817402c6600c142c1c0441e03481094038000b404200c04038450313008944011940c051a1001590110765031640c01c0c68013500b03101c2400070040c2800740900440e5a6600d0062400142c00d51923072000d03250080986600740140c2e40e5000103c2c0e07196a41c442c1c034000d2504035515410605156404855540c0b19080e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145438741 1250 145437491 145437511
    0x708010524041701050109050c090a030b07050403080f180a2102030a0501020c060103051204061215080d03020d05090c09011e33030506150a1119140307030806040203 73
    0xf0340400c400e03054803d140d802c0d60002c00c065240100980c20303a0b002420801d400c040c1040070303404650307407520100201c07540000803154070354417403000362801d0195500103004500005900307540c1c051410028104602e54151149500c140301f0f0900c040715900380180c0080c5040e00c0010107000e0040401c43c104188001c04403507c001a65661030b0990f00080c00001c41940400f0040c02042022303c1f90404c1325180c110190b040c640380040050072420344040312a00c1595482505074a21580404d20700a031240804881c2c59140d1184000d000358005504001390b2407030180414403404001c500d03031415440040c13001d0345030303402e00003c400d03a0550381c1c07061803800b050500000380d084a042a009144001c0c43c1030013502d00000c00d5003003100f0b0401812241014a40403c11080d40d84914000b09103450b1040c1042d101d00c0340c120705071018214581c3c0803060344500350fa140c100055151505200c1032040d0f454008905400481035680e01801c0c83c0180403811010010b68142442c0d405140e001110135 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145439991 1250 145438741 145438747
    0x4060c05160306060509010b0304050705010e0607060911100c02030c220507170711060c0306040e070b040f0518070c02040912020d09060c08092806020a030201050708010524 76
    0x44140040d40407a81d00841c0c04076210581007181c1c1ca44202158010620803c0303c925519056541549621450260f203040c040201c1187c265501e4100a6841650380108100595181070070410301c21071407000c885210f101c065181c0360181b07100e4001415905e9000e001000101204401c10030142900c0000c402c0a08900c200c1411090140c0506030251441c0d40311020444000b0300c020411034001031080052048c60360b1200c4102c000010015400340c41400b049450303441e0074000802a20b10b45841c002144900c805c0440c50f0360f2003d006100310b4050400b8a615640e440062203940e41c41104400c9201000a00140c0d4423070041000101d000d04c001c000181c0c5100310f50740d090344100f40d2140d030320040c1d000d68407840442e60401c40f800c0143c01c0c1402e01c10300749041c40d910f2001d03501c10036800d01e024546164080501150605050204007900d422403801d41d0307160b81c0003d6a0b900301040039001076003014003266190307008500c110b060714000751285400700001c90402c10307442000341c45003034410010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145441241 1250 145439991 145440013
    0xa030b0a030b070e06090f0d151a030c0108010303051905070b09030a030506060313060e07051c031205010f03020409020d0b0a06090f05010503031c0b09010605040312090b04060c05 79
    0xc429004080c5115569451840c146600000c1800d00d520552600618041088031000d50300d42e100f4507010748049410700c0711619245000240b0000300e40759a080c40b41001c1c00303490116072441600c5001c1d41c080d400c60b8403280342000111b800c280c0c00e2001401241c801c100f0640007550181d80e910708030300e43c1d060040c0703041c503556214030741c0d0041140c44a1098001203003091005900d40581a00304a08850250450411000e0036518020b5000020096941c0d00c0c0700c4840360409100081c01800c0c000c1011f000b501c1d0300d5000107280b041c800001c40000b030007082944440a158490275050700c81c082d40084802d41950b00b8040103040ba8442030364016460140d1100041d41d800e0300740d2150308020400309010703180005440507a4074001032012140d051100500854a00200756240441801c0c019102c42c074001e02108001d0540c81d50007600030b2840400428201c1c2c101c4010021244504696035080800da0b03004c40310110107014015185200b04420064a8031450ba04a0194011420340c2c1080c0c100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145442491 1250 145441241 145441249
    0xc030f0c030b100806100515090a0e09010606110304140127060f0e030105040503030402010804020a12030816080402180a06080105011e08150f040f06180c05180109020a030b 76
    0x8483d40459850100c1060000c035505012068102c904030143c44566070804000560f51f000360910b4000400000c038899000d613480000c444002e080721078a000c098108440000c0c041d10490042d900450b40b46072000900c21303400401c4500300ca454203100415400d605004488050107152a007100304413924a00c40c00900299000f03005000c00d4031000c1e210034010b40090101d420310344170148241d00d02130170800412000310849038031075424a40010a50380d40c0c80080e5140017580c01c00c0034144c0428514500709030b04405020b004101c1843d549a1010121004980386d4900300c41c002d4105081032000c011050340a0740c1180c0002030100d000c22901e85802c60030b402c48109901449a007101c0c10843c1c3c0c2d03103686040d295070191810f200600204002d200d401d003101d42e0003400070324135244088000b5007408001950000907690111042c40892030701c00c0c40021142080806440500001c000040c0718a00140001000d00d1348540441c50341c0c1c60890310b00020342100d1520410b15455820060880e55 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145443741 1250 145442491 145442513
    0x60518010203100e06100503010905040203030c070608010905131e0203030d151503050c040611120f09100e010e06070218010605070b06040c0c0b040615091a0303070c030f0c03 77
    0xf5419107041880c64140031202092003d0703c480d004121030b500c0240901c0d846022281900c500c1c41c40411151074902c0400d107907200700180c4802d0380c059007070302003440d03507000741080d0480300c40c030b503080c01980c542200181046113076800041880c10b040e00c2000804182000c030070042400102540c1c00d06004100c6041078a808001500f0021040401400240803070381540825205c186810000ca141c41c1342c480d907140c07049001c0c02c01440200482503900300420800a001c840300310800d20f880700c003000c0c0d564a154010704811440350022202803080e0078030400c0c2c0ca0707040d107005075551640b0351000e00912031941d00510080c3e801c9100c14405034035101c007040c0700c90300801c52075aa450740c0700f2250a03c524030120240c9568030807414075580219495000c0482200b15802c0380103520191690301e03007034000300301407079620b4181000c0910000c0d2a01065000442c5060580a1400880c00b42000c148e1640310b02c001c0106028480c1c001480400e0f52015032600c01813094100040d12612502c450940366 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145444991 1250 145443741 145443751
    0x1909050303130b100522230610030c02031c11071208150d020907030e12090406060305012402031b0d110a120f0c14010e1513060518010203 61
    0x181c0721120b080100840f8514041e884070640088154290030100015003180c403007a802d0700b046c049201d041401c1815940f0000003a20101490200c0100c051fa420004500c1101c6c40e6104044418504207100d020340203692841c44283e0207035260468a00500c00c40310115400712000d9a69010410f00d01101e000c01001c002d030090342003203420f0141030402000c007100280710701d680404c203254468654454060101080743c2c1154805080c0e525400d045004104805100100e4410b600901000020314402044004015030302404400e88411040c1c2c00e4500a206444190811601107000b1032000606881601c90380c2c81681d1901e4810030001d681d40e4084191a14582c1044a00220b16a0000d408000700d0f088000a400c22801b6a00e41c0034401550032001018056180e01d0b1070680b921400185691710750100c200040c18100b40c0c1103d00070261079490340c46600c220411014000d880254641c0701d038a1007800c0440c0c1c0c1c20b00c0e6079010003524018100403013080d49802c02c07000800382800554030075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145446241 1250 145444991 145445011
    0x170702070816030b01050d08090d1a040f020301110c03030604230705032203020604020f15070803010305061f0b0c010207020d080c060606090a14030307060204080601080607090b031909050303 84
    0x3036421800e121a413130006034800740c8500500e440243c0010121380a4030644107048032040401c00741402c5c11740c000384803c0f2000c2400703001503081008210000c14008400c1d40213034000c20401c0d450b84207040107881001d0300c0c004240c1c028030000d1061310302608441c554600b048580c1080140e0341800711602c110a03105180450408810401c04146410001071000c0488a21040305c1c90f9a44000c0e4885a01601c068050141c000803c20301c1c0e26851080155550483c001e1070380c601c51800c00942c150801e000803540c4d4001d0740041005011034600c1004000304d4002d0301c9841c07524014076070489510142010724195003c2c000d000160340d0390408801094007a0040c1d580c0c40d80b104541d40d060000c020702c01c0f84580e4041c00b500410b0740f036090102054518000301c400e280b0102800007490342c021848010001c80c000500410021400704009040760841c0c802c580c000c2d00c42c81025911042c241c000c46090304014030008c1c1c00c41003180100300200398030300300029540c109900e9060856000300c0e0801c240d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145447491 1250 145446241 145446283
    0x19050114070f0216050d030e0409080a030209030c0f0114070c0506070309080c101b0206040e07090317090d0803150301060608060f010504050a0308031b070309060801050409031707020708 82
    0x44990180002042490130080b520210381c2001e0029210728032440000d800c014a03031908640d1354503564040d41109800000c2d0036150b0f0b4007220000d000e903100c0c0d29218000d000c1c00041994505111a403550070301016107440c01c04040b90b2844080c0b58215107001d50b00c402c0c001c10006184c0c0c441034010b0006500a9403030000311402d020300c6510704001c486c5180d0003103602d9500444020303800454007100b2080e0502d440384501d00703400021a28000e83d0014481c09c021803061040c0c154104d00c825044030300c1080c0c01c110030a40d14818136030a019410809401440300c00b0220001031741400196400081c51000f400c008503894082030854020313402100c04213500d03400b03111042c03404500066080c8024a0042e00d014180000709aa0700d0035440300410041c4003102180b40e0b10088502c028420010307070303a6140c507100107082c0240346080910900010070041800813070305040c40c0c0681c4c103100750581c861480f11100010203040c0e4013401060030f070850041c031034040f8103c001030004d2041107204007600c1039 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145448741 1250 145447491 145447517
    0x603042024090a0e2707030503040b0c010501050121022113060e010e0c060711120c01080c0a02060708041502040f050f03030705070303050d0b10080f0601020f1905011407 75
    0x31040d492a084a042d2018a41c1001405c6913400b500200e000c000c014034941c040d4003000d4852511200e0f400040641c0400708010403088405009040345004130002400710344d80c1d800041d1044a000d036020346402c444c080a03d4030820083c0c00070460080000148002c0042c0b42005110b4924240e074030020051400c00b1030b1040c41402d0140150300d02c0e802d07000700400d2204030700c403581d07410030f11131360034064a40803031060f052120049074602200ca016103410300035690400000d45414800300040d003c01c0d0404042048018544142c1d2800840c0e034008040f55103848005032805800100112550000700d004500c2d040d0040c00900010300712211030808050a10b42000000e59030803000c02d0081d481802203c010440c0011408204e907014100540c1c6e40d440d12442c10040c16407810540e4201201d01110f1203030582c400552441036440d440010301c10b031551801262a01800711080400c1e03071155a0100c0400013641c00080f8003807288000150244600e1404105c1d56000c40703d0b600400c4071508020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145449991 1250 145448741 145448749
    0x105040b0108160e040606050a1811030f040f141609050c0a0f080c09150702010f090302150913090f030f030905030a140d060906050a05060304202409 66
    0x107405040c2075800b405141c02c698110718989000c80c49420540c0403000c000c034040c00900d6022001800d00a08003000031a00c0781c5007000502c00305950354801c02e01c3c2054884c200c00200c3c081e680901110360000740252102e80703800820b21f5040d20151080c02c001812030610030010802802200c145900144809280c1030b40701086501c010041080c00800300018100e40e94041d8104000002c24200300311035417113040401040380514178689410030340001c9030003902070300c2c1c202a01540d80b007603a8103240c200196204440c4150b80348030094000700580d4902c40c00320000c01c05011040d0020300b0010300b040c1020902401c1c1d4a410070151a4000121aa0004e0552150008035208524181402000328580c1d44554030f11500b0101400c01c00810b1704000109005030485031086800c01052049988401141008260301c0c880c442c803400401800107079604007001034910403030308880726124500081d181d00222008066159500c5070f04e44440f03107404403100b00c0880d04541181442600c0d2100a4240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145451241 1250 145449991 145450013
    0xc11070e010b071e0f081c2a181502010c2a03050715050708011203090e1e010306062321100f0e1b10030218060705010504 54
    0xd900c039128003801071041c0c6000e202120394083d4002400d07020b0f1080300b00300121805911100820a010201c1c1c80010b101d0200050030445240e01602c1c180c190340307035100804841c84555603c6011608040003080003605081880420b00d20341000c195054440c0300c0c2c0007845e00580c01c050b0402c408181405001079091090344000111804d04101c0382020380c400380c91001002c2c2e61464071001e108074840416120700c00380c3c0c03042940000a00e508501c1d0801020107000100c400d6030001d1204400000c1c0422000507400710180c0540f1489080d50803d8089142110001d1102c040040c001c290f1420005080e40142c4c001d500a140015080781002c0e00000c0180b40070080070750a42c50441c5100f8255111402080320448400d030040c08142c14101203400c1414490380c011410345058000d842c5050a42c02a850140c000c00070b440d0710003292200c05450221500318207800040740c0703c0307419056000740e00801000e4814842c15845403000d00c0000c155a100b4481110355135151000d0000b0040380020b8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145452491 1250 145451241 145451249
    0xf060b010c0f110105071406060405160531060c0c09020f16030e0301022209020a0915030f021819140402090a05040504050303100b1306050901030f0c1107 68
    0x4011100401c644445052086846016100115205040300030780e000d00121102507a124140a85040720008090b49031401103410701d01032800c1100190740e049580714209440c00785510382c036003001c50404250240744003044103c08a0044640d0040c06078134610101001080180e5920104007058030381036072070054640c4410078541c01401f91074504d010940640c0c00100c04c0d90040981559030341001c640720381c00d003502d068043d480000c02124105400c40b1078140c074056401046841d56450074035034100d2160825085c001280c5210610086890405004041150703140101c1d00c400d0a612010490380f041c182501410260100904030b0304085900f9402040e130a41e402d6411482c1013410340c00ba100b1080341a10861340010b207206580d81c1d0322200c1015040c094410030070f82c40c0c90301c0e040350349500507645840c004806840010704d1040c10000c40303c070b0141c80c03106841000d00c1d209082e02e06802c030598650500d610f8142e45284841240f0840c144900c4998604070104410780c403080c1042c8941e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145453741 1250 145452491 145452497
    0x91e07030507050609030c090901020c0f0a08040519090c05121645080f0a050c0607080423010e1c0b0901020c030a0f0806040b01020a030c08040b070f060b01 69
    0x300049a8007080074001c5400540c1c040d540c035224140000c0c10440b17441a035644c850058400c1c40043c10301580030307121b403446d0380b01118003480301c0c0d40c0819a910001d50000b00300e02e004200c140554102480240606251240f441c00c030340391501005d60503200000d03a01c100003030021441d0350713220039840c0d00c240d00184440c0c130300c541154004100600c560100819640f105c200300010000b44d907214891048141c09014405c1040354142c080c04440110520903d051440b481ca1044d0034200c01003000c85406030b2050040015921040c1406415081090300b40e4100f03009020010301d5500b41c1040c44415035884001600d115400c8001501010025103004d0103130070010a03501941040c1c91800940c81c1c1c01150a0382c4517030311500002c4c0079204243c0c8101e0240004610307400c015401181c1c4404288c90f0781c42d0040c1d682e4801052008845440024600590101d0000004240181130b1503e52034080c0305c80740c1c9061340b40c40840866078080001121007130f603260300c00818071210b40700d0800030010900e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145454991 1250 145453741 145453753
    0x70303051008030a03110c030a050c011109130f09020d03020105060a060503010f090e010603080703210c080103110d021e0a080102090a0612140703021801020a080d09030e0306091e 79
    0x84840c543d24020100042d05142c2d82c0c40c2104442c29480b0141c40002c43d0032801c03a42c0d900c602c02c500a0407600b20741500805503007000d9405000d00200c8054031a040d50181400c0094083e503000e88000c2c101801c0c600b41525641c5c624840035032030703d588221013140641c00108490a01206100720000c4943c010380410000b0710040c0045622803a8107070031614080c0c0082071003c444020b46004126a074802884180c0020300c0404154111070140340100c9803020040b17200c0105001c1d9020ba0340406030b41b2002400d94001403000407458034500c00e0060001c1d145624000c0d0580c0401c24080c410741d0850000c1e481040694581e140010000c006446440b000f50300705000070010035003d160900442e0284420120303200c220051a500204607281c512242c3c040d43e040942000d0020350044014000c812041040c2c29025400003a002c5251948905200c2c5030010300c054040042804a00880c10042c0c00c03c1c441402d80da040180300e024007031007005098020822401c07a1060508034200c441c45030810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145456241 1250 145454991 145454999
    0x211c06080c0414060d02060405100801050306100303050412030c14010f1104030c032418140f06010509100503031b010e060f0c030a020d05071806020c1f0e090c0703030510 75
    0x1c101c050b0713001403003510150312031401da100107020390059421085d0020442d000711101c180d4844001c1d8101d541c250191412510f9000c0050358104641c007019020480400080104044042004c410b160191400d400415284e50318680302d8482d04a14101c039039125400300d0045c02461292110b20b883c0190602e107003d2555a87c01c400715107d2002030883c48507503d03260901c4210300405e6031a1102c1c04000c1084c184882000304009064090a071201e8034603074403010650740c0c0011504a4054154010322580e1b10300810800000340040004041d120001c40000300c6440c1000030b000c4c0144500c4d110079403400c503801c507142103402005050056a006c031091050101c1d4170b0802e560014203401c51250349688440314000603215000710801c9062a010410400951100f0350400c80310b0b210060a50340c542e0b64908907910a80407240d107901451884002e130007072140e0040e105100700d00d070034001d03507551035500000c120b40c1d412210341960311000035004040543c1480b0f490b911813081080303950a2810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145457491 1250 145456241 145456271
    0x160501030b0d051203060301020c1c0807080103030e120c060c010b09090a0305030406050405161401121b030905160b03010311010504061b06110f070303110c211c06080c04 75
    0x10254014034500001107101031f1000c0d0102e60703440e0341c000111040b02c0d038140d07804448403144032814000100722202003440c8511450145040340d41598400c00410094070400480c00c1d404041c2c001035118410302c18296450f494094079010008000000c0c402e1010424444034041c001c180020541100c007444000035000b030305880e0440d400580010321940c0e01c2c50824507021205030304404a0381d42035800115450307810f540000340c08083c0d8801245900bc0c3c5004400d90309440844500401140d141034002d500c01e0380411407450007202103404404240c000900310002a4000303200ba684000014010700c5503202860f4940c071002e02e0007600d4280340440091020300c140300100d52011070000d25005001c0560805682c05001240480d51105065802c000580c803003a41107012905081c1d250002c15699401d031420b0030f1036140600591020303400407407800040300e401481c1441050115015550412109520b52904400b0001e080da090228440c6050380c0144814410350a01c2c09c00078407070705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145458741 1250 145457491 145457503
    0x140f06060f1f03020903100501060e0901030c140102031c150e04030804110d060527010905030d020f040e07030f0509060601090b090402041205070302120d02060106120905160501030b0d05 82
    0x10b030008041004034241102100a4454001816498860f028541d0150849544140c1c12200c4580b5400d03c0046900140540101c0900c405803040c120300c2d604000c03003c440c0d0095180248140305507032504003078014600b0300c5c3c10b20b6100c0b028039a65450040c070464211050369070251000d0740d01c244442c41c150350010302024008200510903c1003074aa06026200c6881e410303599544000244201e2620191048100c503847d000140760514424000b44400c4042c0314030094260010099458849401665806940010140c5c00b00d144c040100007034050429010a014014664000c5800440c14003454182c2e440500107100b6a080f00051040603038004869804071030340b100b030f8591030320010000180280210f80c400400408000c1c1c245040060208940c001c4d00c0c400c071400d00740e0940540f680c543d07031540345c249480568020401840103501560b1908040c21014402141b03212903581c130301d0308041207a40180148051075000744001d40c0c040c01480c800b81c0c1c080c0c44c80d0300d00843d1601d80ca580d6070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145459991 1250 145458741 145458769
    0x80708071e08060906060a0510200f060403020f0d05180f040609060605130602030901020a0b041e061506050f04090207020418081903050c0409051003140f06060f 71
    0x2054020382101220300d001e484004003002e00c262141860040c0926403910011034006104440d291000f140342e01c0d010703900c841761050030396820903000d59035090381c021000b105420aa15100d1480d01402e0707181704020803881030b8401d9003d0401f0007901e02c0300a192198490740380040c003100344085d00b6140d04a0b81c182c6603440003250502c5a41140c0404180200041d40000c101a82000e00214690340c201c1d00400c09100c440032103900d156075814049840340940807040740141c01c00c0c812078010808100006030000e0107a100c4031108190311440c4800d000b007003941111039949404c1a0114600341c1781070303207006082604125207000031460405695204500a5280069010500382e055446941c000204104856040304820010303060a00181c0c01404103250170607040c0000000c0700e48a4011039000d9400c8400c0c2c2400e20f07003010b0302c0350040c0c50000d102054034140c02100001045480e09030b0000028180080c15281940030000c074180140100264042c070005c86201415485d03c14456040c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 145461241 1250 145459991 145460009
    0xc1a04021807120f020702031606090e0a020409091202010b0901080607230a031508010204050619110a0c0504060501020a080f0a02030408010e070603180f08030c0d02070605060a08070807 82
    0x2540c0d820b075064841826152020a18600d800c4403048554031640c02801c0042c000c40445440da0303403292440740440514001d10b4002070050404029100c4c0c91024150400c60026001d41420345402c0d0800031510010360580345480361152a500c903030307020b1140100890054441504c90b44c104000c66030740f4400039051108002070300c40c64030030a0041038402c40d42e800502c50499554015454000d000d00046c1201e01703144002c00342c1c000781d03c000501c00c8804a1f1006040e031350801118403020519118042039607030a200140b001e030101d1400510120204500ca59046d100e0b80c1d08000920040310202d402180c1036501860641021811030002c2d54440365103415500e654188005080b070031401158003902c10343d07003043c200c403206800200340348007514400e0382c04001041e5889404c140e0703000d840b040a1700006403c50b2420105500c1002144d0103450b490f81340e03140120455400049900018068403560381e540280641c902e4000e206200600c0d0240c028002c1e14104005241c40b0301461040800b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 145462491 1250 145461241 145461289
    0x411181201020409060e01050312030912130803160b0115021f061814070503060607110609061c050a090b0703090c050402030901020a0905012307060902030d0c1a0402 73
    0x2428250100c83c05007410300c030144200c66840410002c45107081c080c082c480d008441c1200702c001410130a492180030490f0003052800c8c0c0403540361055502c614100c060951040001080c0d0560420045ca034030340b101d820102d0036582c00e003424001c0510603013000c0d41d203c1c0c0f95030858440607400a802d00c284049803804010030182149050700910b0f0660000d0550070000340b600c4442c202030f900c10615600385251340c400300c0d9101102180e161108035036603039002000313101c1b0790040303203404004044101000d00349602c0c080c203003400104550003203c0b4980ca804400c2005190010885c0183c503081103036210709000b145145c2d0385044c21000014849020590b8492010083c82079a207517080040c03130040c03c21507481c200000558041d6100c0858400032840b00c0c80c0000d003951103000c600403e03001140c1c0c0c0c01c0039044100e1075103006038003040050b204261146041c0001da901800b114070010310f00d881e0805001c200d460f00010216801101c00d4004e1031000800c40542c89900310700e0680d801d10840019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 145463741 1250 145462491 145462519
    0x705040e0106120b0405010b040c0c03030c090f090c0e030601050a030803071b0305032502060703021303060c020105060a060512181606020d0219150b12010f0b041118 73
    0x700400440d400300c2d203124003000103c024000100441c074012802040203000b186502d00601081c0c4001c1c0c0c0d01600091010905480420321a0744080d104c07a0311807426418480c0d4410088401c4040d68008504080d5a81c1c403c4800d1034111440701d01122054000d068590725080000304404c00c244005004c03010b0020011304070303d200c0c441c480340302c829080092600000500b0000c02a400864203401d107100280d0075a40c1d10000140e520100c1412540206410b1b501d10340701301d007c0d4000c156540c6841527011000300001d00240103805080070207600004451820f13408000302000240d09c84400c2c8001000940c010149084415511140004400350a800e20920151405d040e820124600485841e40411095808510104030b00541c0c0e086170b912403440da03991868851030010091a9014005c101420359406401004c1203c1c0028040c4501c10003600c0d11600350b503075911460f0107a9036a142e454656250a21642c03e0801030031140313608211501c1d0385501c0070000c0c5035825208101c5103200c1d507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 145464991 1250 145463741 145463743
    0x60307031415361b0d021323010303090e1e09070501090506090a05150c0303070305190b0634060e010f050f071809050702100b040c020705040e 63
    0x300141002d0760400c002c83c0340038009110700c8004602c1da083d5807160800c60340c2c0c080040c0d002d55410040c042010b40032400740e4500088040011007001e6400c010140f030440056502c00a40c1200020f01d40400b00d550540b410031502036120f80402201c40004101c01400800d03448003140c001e69003816182c4a45444c0c203100d5503e0f6030540050000c881540c3c034108401a4400708511040360000c3c1c0329108000d03180ca040251a010b00207002c0d0300022200da0400580c541520100960151703250a0381c500401d003c40781c1d080d50300c1121442c0100c0e13241e1043c03003203078100c907400204210b200721410800c20451100044051041c80c107420001920040c4a074900725014040d00340004800307501c00001d044601c1d2000207003007132852086040d40b800c5a00d070809030050007031511840d5980d07940a0039075281442614541d84890400145041c504000715186c01c0e070303214030b038002c1c14203800070303c4c05540760203080e025140902c132040c1c0607604200c6a5201d00f900058444107440d0101c80c04169020002000c0e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 145466241 1250 145464991 145465003
    0xe0f07050f030a020d141b07150c0207060908060f0a0b010e030321100b0a1101111b0c04110313020d0506040812011d1803070c030302071d0603070314 66
    0x5100a088000280702441d210b5038010004440c05507401c0c0020078012484448200044542c1f445559100c4050b80e4000c05d2600144001e43c854014016100c0b6403542c4001181d20003244000942d002003003d0103455008580c42c4000d008080080950b40703000000c0142c403080c0944030451041c0c030390040180316805460b010540d000f015044030740f1400310300f20070740d5110240440070340c00d048041c020a4504504201c1102a1025480c01070320b042c03258601101e480310680d0049195542e211021141e03405504000c5c0f07904038441401c0906001103d8000e030074000d4a5500b14801c0385400c805d0442c0e0035000b01070b00c2d44222260b074007a121030850300100d605a0b84070103004050f40104030401c0100a9200301920354400000e5542e501d580e2601654000e01040004500c06a141d040000f2100c480142014503841c40b0482a02d06040c81076031810740d51900c50b0011405600100000d100410086100e50322101c0310300b420b510507003881e401003520b42e0620300000d072030360000801207482e4950800c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 145467491 1250 145466241 145466257
    0x41e05011d07120903021516110a02030a0206030c0403060504121124130f050f07050d0b0406020703031b11060a020403020114070309150f120c17090106050a03060b030d090e0f0705 79
    0x11f040586411624807039043c041d45480404a0080c0e5024170304894000303001a00e4682c0900204022007542e0200050360f04000c2c101312409004000c048001035140c000c03240600c0c4142500c0d00310002c0140003502010950711484415445121a844030346003a11200890110069902506407107416201440118403d800ba0254103016a0300301008400a8044518600300055804242c0c0f90010060f0120030941c02900800f400c001003004604c050b40280300041c8642400112103444001c1d0003680030801c094000810b00c4406100d0840c6001d02213651b000c00c1c3e004d0118903160031540013920104040d1b150350a042c80c003140309405c04d03016140c4603015190603540e81031010010440109400100c0b2032980020f014420600588041402660a0320001c0c1d103641c621207400c2240d51460480046c614541592162000a0b10351039540004c00070754066100829505103103420705282603400303a2160f080004100b4100230071100303ca0b0300e5803c0800d5240e4940c2075211036004459138001c080c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145468741 1250 145467491 145467523
    0xb04060f020904090f060507021f020a0504170f0615130e0c0301140103050d08011503051e0a14060a03030804080706090b0708010914070e0f041e05011d0712090302 72
    0x15250045c01240790400b00c8461045070144038a07915050b00b2170300d4081c00402441d0000d481c803455140740007590040c012114880c40d0041c20545e0751040c01c40c500c580d020390b00299400004290181c0c450a22105030b010410740c20b18850743c451036010600c24940c00c1403031940542e842c1c2c00c080b1800300030303c44104c070400010001d20950790740301d10001d40307584284800c030781c10701c40d1a101e40040b0b406540f8050490798030b800000c804540c50301d02540034000c0100410f06440342c0b0480c010b00404100700650051074898400500340f01403e54501143e0009802d440c4160400342c4204002640300002e603074004d62045442c0d440300f04a1400c04040d041800005100341c2c412010420102d600c0030201e41210300804081c007203420309500001840105451000014400f00030140c40341c20034060100981c1c0020700002908042030060034076510442144241c00c0d40c84400401844240c0c0d21441001c030034418002055045c910000386c00b4003030300954035444540340c018010501d1300910030302c0e81401c0f140e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 145469991 1250 145468741 145468751
    0xf120702150d0b01020f010c170411030d0206060a120b010506130905090a03031109090705131a0316020613060911040f0e060709050307051e031603030207120b04060f020904 76
    0x6140704020700000c03048103006104120060072454014050342c0360740751427a202c8510b590b8100f40d902c801c14400420a59075030601014448154400700415042c20800e0740c05803495017801020085030702982d5101480413a251000000824240741ca00c504646049a00039520761030010044a940c0f1241e20078585c0c28540800c11101100114184410f103100e40e80c02c003c03c501c0030b00007002c90b014200d200c5401c24501030010360414003550040c04220034051b0a004600d5890304500803a000094401031a180c0100c00e0003c0440c40034805030840c6090b001500703042c80c4c101000700000740c1e0b04c000940000e4444030720409104602d00802c0031000058000d0250308000e10340c0340040c1145200750181031103103a0001e0001d134441c4801105070b8400401909a5620b05003c0010300404040008400340c5030024284250341c00b0080303c1110051600c0d201e5800f8034505010303051011a62222499151b002c201c0400140310a14659000b5031040000a900c58034075400300007401144410354105e4944 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 145471241 1250 145469991 145470007
    0x201080c13120c03020103150b1206010e0d051b0a1d04150c0e0109090b0105040315180c0611070e04030c0c05061804150303051204051603060507110f12070215 70
    0x24510703c00e6074000c0c0c03000d01c080580055910b80c01c034140d104a501802e81444955880c4c54189030703254008105250103c419101c00001030b601200c9014115190b0384203105004483c07040c00029441c00398210703610202a840c00c40c00a44421000210200c8031300d844002030200b140d400203008459860040422401d0b075100d101518184500d89954041009980005106106c500a9002e450f206a44541c2828a1076580004c0c100d0751640c840001343d100e20000c0c003541401e04918031654026440d480b085490a50003074594400c0958115030364204010900203480386402403600291306140408601c401c60802d004d800122380c0005600c0704000407041413102c0c0c03c641010500c7c0c021136081000001c22102c45842c80407520004020800511100703948918121070154414094010344070f541031490000b00000d11640c0046070701c150344805001480d5801445000b615003450024130480c10218002c65641d84060941e00f80c0004c000b5000045440d1000c5840c1840b40c8100119240c0c0c0d9a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 145472491 1250 145471241 145471253
    0x705060a14090a11060706060512010219111c180807140108150906190303080f07030c4d0606100905100509030303040f0c0506070201080c1312 63
    0x60042011190407400010602000c0c01250f200c1005034401c203150101007031101406040c0d000382c03000781c40c01c580c0c4480004003500c800c4a80a0800042c10006030b807280c0c2d8000060407880e581c03d05100f0013460103885c9004080008400401c0150f001c100c2c201c4e03610381070307089541c0d484120003c0d130880360285c400501a0000126107083e00c544180088920b42c8900c01100d03182d00440f00b079200c0300e00c080da1220260a00790102da42144000d41010a01030f07603011000c4d1107803801d03842140051054010403403154600403072203402180f54542807014030390803c4018598070101100c0802d6103682d22041d506034a0294030032800d00c00b0a80580007501041e90540410102c06412a03000c2c06034000060240c5800d4101c1c017041d00740703030315404180c030f0500d800e00400c80c0171091003070203001e02001a407110303a4040024610440c49103182055601e840d19100642c259254031850080c0400d008040060382c1002006602c100c0e005141034803052800d06e0340a290f03140d940705041282c00b1221840511103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 145473741 1250 145472491 145472501
    0x4060b04020a030e060108030f040b1b07030515010b070809150c0d05030a06081204090903030b041d07080304150c11090408040e1302010e011b0b13030905030c01090303080405030705060a 82
    0x13100c5415103400303a0365640a15145c0c440c440409542540400c01400001950070191003d0510071881c0046444405801840c25a40f500140d8003030b48050380c84051340d0050700104e40902220213a076828410a95111421805090394041c410713804108040020448141a503001620708001c8644a0b9086100903000354015075280594906260000c1032044000a46203400001e0050311440c052410301144000d01e1f842000300e080584440b04025681e540d03001c2d450143d49100d440c2841d410003118483d28200c3c55501416031600f003440104142c11081300c40021349441d03400c1c401078842c0f5500d807a903d00070b041e0242c0c690003e500002d11041c0715a032000340c02a42c6100c12410140c2d12240e030001c0500c50101340003400207003a61025103003948642403010a440000500c0040550b195648440b0070b5021501080c4400030f008101c4145030f48043e07244020202a03000d041a01007410000300158290b00010b414043c240000c60208101041101c0c85103401c4020380c0c140d0304098441001500d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 145474991 1250 145473741 145473761
    0x30201030c030b030105070c110f090103030c050102070804170d020109030912150e061f120f060b040c03020903010c1b0b07091d180f0d030b030c030106030803040b011d010b0304060b04020a03 84
    0x40f00030b00321039a035080c02b69190140c209d0050038040d040c1e00c0c0d542c0171142110803640480d0595024025900001d8040010744045c0803030300c000110460450856a1a060114480c0b2085a040400075004240c000014400fa140c0c0840014060403540c00c0a010078014040744022140c03409104205810001c42d4141c002c4500d0b4864502451005a00080d140814042c0c044030b003c003d03e4a40c0041d103228407061500380714600c0071482620b03c0b0001021111f41c0e440c0300000c2500048e50094510302803142d4031813a2a0340c00d0403d2141000c0340f002130085580703400180100c840300c0c00f08a03601d004e040e804009294040c43d0116401c2c001001c2801604151a1003d00361480401c0c00100304000c10103808002404000302030400c1041c0044024022601c9144d8240c040c1200c41051600d081c059007001d113003c3c90b81c45669080034078010041c103034168007208610114546507000d00040c010001d0450b00039141c402d4594a45040100041c40d0f1802d41c00d134014400103840000355015003006000d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 145476241 1250 145474991 145475003
    0x3130606080a030509041a040509060105090901061410090f1d0703020f070605070908160311010503060307090c0e041b0207050f0105090d29160216030201030c030b030105070c 77
    0xc00d64412865070790300100c403402408250140828800c1e414254084200c9541c1e4420a0014409010202d82143c80559090701e00e03030000310044c012403d2840180c6d4000d03401c1002084440e00d01001c002e03644030700d441c0b0346125902e454400900d1620940c1f14802400041707040d03d403032a80d02c4c03103400c40c03001128499000740381c245800200301e24002d01c00c0d41c210003d51804503240103d13650b5400000c1200420503400d000111001150200f010030905c42d411905074154203401e402d5080409074501d090b10410b041210410422460b51000318040b011038401d500082000139101e602a1580c042144580e40c00510f410040c00100d0010f440d100c04648145c0c0907500a10b4030761080c00100c85200c2d400350302040c810011115a401c0c4511100340607801400c0700c600c0b01c40c543e00d00c0c0d28440303050070803440b4144043c414040701c4807420f02d0800740c14115000030070340c01108140e40d004c40b01d041d101c064181503803801158900c42c001e40001d0030390b00005008000a15060101070901e807061401a031701 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 145477491 1250 145476241 145476251
    0x73503270d03080105090a06030506011e1406120702010e0307110f03060106091a07050604080c0d020a0201021c050918070f091202042409050613140105010e01090506031306 76
    0x414185610100700d403a4150f621000703180e01300014840569005865007115590b699000404a841404980d0180500c40b8802c400005080025212003005400c010b04900e04868410070304d41c0c2c1e52040b2100c104441840351990f54844005900500700142684d40358040000c440c81080003807110003403056000c44982e2500c1d0082418582d40315001d00404003c50080c082c00e0000507a081c02076100c000505a4591501000e541c40c0d0b42012404d5504480d07140000c1001c0c00380d10000d20840801203e5803008100c0710540c1d400003541c80340b58841080014007607500c40108144500c007101c03082c01c1c02820b1000103c903d0a890720114004071103040000e119000e41c101b0107031003441c5c0c400c1180c4c1c0030610792045c0a4680c0810000b818121400701a0303889480b01c1219121011801c807005020f061030014003071410a0a200c40070134400f84c40c8100701e1500d80000303124100347d58420306603a82840c0c441081034190b40182c40d4510306401017507101d54040104200d40084043e05000240b01c1c18042c48 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 145478741 1250 145477491 145477567
    0x10c1e030503010f23040b031002070b100e240a0b0a0c11030f0a060e0a0f050606011b020d060902062a0705030309010203030103030e040f050103050a0b09073503 71
    0xb10301c40c0d0300d046864202c440008249898542030f04102140301c001401d40706503451074000b06080b41e2000c6811618021144100b2044540de01060002400ca00302800c0b010303d070005a482824040100540b0400c00300c0c0e0450f4903d80310103000c90080e10700d8020f050b40c1d4210700e4502600101300c41000b1503800526000d1002541400f10310903000c0e400140c02004500990343d40c00d0042c142d07800511480d4801c150003a030218400405441e00395014101401580c2070007000145800d106250000c3c049060200e04001629403003500303201d10341c010b44001009200c502c0000c000e0300c1611040c50050381c007102c0741c84680c401c3d5071608412105400031260b1190f552000e240d200e01501c0c0ca660301581040c00100040380c00790003038100480700100f00042000030300751000c1c200d034403c0e00103030340b82d0740000d4184081126807204140c1101c8168014002c40d8600701020071041c130f2000302000880c1c040c0f02074607540c2e580340049417040d100030300650341c80d03d41c0015451020310140c00164054000d85030111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 145479991 1250 145478741 145478759
    0x90102090406060f0207061110020a0c0606050a0b04030204050612100f0b0d23030403020409060c030b0a0b0307050a030b03030d0921050a0302180405360a02010c1e030503010f 77
    0x210861340141c000e0120145000000d66803240d46c022020b03060b0280004030400a0103501c010118548540c444d40f203484020b0400800701c41540e0440e9016440540c400c1c0401c0d12080256021207a040302d0104a40d80c1e03460101e811207062011001c440d00c540340c003030f1400400c2c03500280c40070720030f040c0304000d105007603000c101d0000d41d9450040c2090000403400301080c0c0c0c1a421083c4200001e00403a86440d56176404a0101e80c034079242035601594400502130034680c14000c00c001d4040407260207000c14140b401500c40c5200143c4a40240400001c914540e02d011340c00c0444084001401d070380d2500c1d41c005040001c6c0044a80441d100c6281030ba42c1410403c25140c0e0760303000040d80e035074642000c50010b0254000e40c01500c0c502c040c0c61031000d0004e8640d4844c01410700c15504034103200404581400d20301c80f800940c00d507400742c1600c242d56035021b000b400031b0032061041e02480c0041d18516581000d100f2910111808842c14201c54200350034075400030011170483d40003d00022126544007024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 145481241 1250 145479991 145480007
    0x81801050f06090601020f070321180b210a0b030d050f07030804020f040e011b0302160f080702060a020304081009021011011b110c0a03050d080a0605040509010209040606 75
    0x180c26040c41c0100828018184000203640c0080180111041014a07100035480c0c03940c0b0f03070320449018000c00c41403036800c1c029070310b10310855100703080180603038030b918001002141540c005e42900303003008121540c0c02c1c1442c16511603020382500020502d4289540c0c040081c007000401c050092150340002d0115601c254220346000640c08075103800c2ca1b0b42c5070740813075880313201400607648003050000545866803248542d103612143c180c000034401110425071000c04071140c4c0b908041c1841441440d000075440b90304000c2407540301d5041d0f2820406443c01c8101402440c43c040d40020000c2100b03404280c0020040059403c54000c4a0941042200c4c103010351b240500000e4002c40c11451510505000c4d0075207100541d1041c00100300710190401070754041c00707e6000080003906801d10340340e403a24180004240e80c0c0c8150b6624568a040d5211640d451084214001c20003010300d0008542d60440e5001d039015100040045c002400c20fa1407c074042d400403c10b00d44100d21300345000545030700035128 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 145482491 1250 145481241 145481251
    0x9010b030712020306060409020f0a030e0c0d060e0f1903090e010302100509031c0f1403090606091f0303080f0901050613020c0a062a03111803030705070608180105 72
    0x20502d40010710344009000c1e42001c0d2502c0d803c21010300c80400c100b400c07800a4200c0790452484103031148844800102561404454070046400c100000d250355291a0b00d80c00419410090120b6996035000b1014a07064035142840401d0066103035180380781290155140000340203030f9904a034161103002a95a071142071200950001c260001105181d00480c0606080e64005065130020240b500c0e81482d4140407028140c002a00c001d503900740260403042121010020350f03d0503007181b50240840c0d40d0f1b904060700242c0b08500c01000503444021010403285000006049010304030341e20714001e030161000307076003141101c1d45000c00140c1d441e0051007102e1190b00010034520710803640341480002588054151821409168052800f1804074028403009401d6001e000400d00d4800d115038a2030200301c0310701401c042c11300d03800c8050342c84482c080d1680308205d050400108030038480003900d0340c89245001090350040d281c4c0000d0840c2c10070080e502c100414469182c050000c0d035081800c032801155 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 145483741 1250 145482491 145482497
    0xa050a050723040e0c130b120c03030706092102010f05070f02150a020702040e0d0f1e080601111603030914011202090604081504020103060501110309041a0d0303020909010b0307 78
    0x150b9401c20302c2c16400107080b042c80f00c000e84075241c14040110722100059003442d942d560b01c440d00171000d0304180c801904030080c124090321503200c285001070303240d214040011b0080ca032100340743c0d400e1080c00072351040c0c40c010060b0100406e4040000180c007a125150b001c1c1c56103858400000d405074001ca0049100c10b000760301500e1800c40c0500d8905c0c82400241001c2c40095080c06003100589543c807030000510b003170b20018110820301501c005c2c694240480300e031040050a0198942a0f030070f00780d860842c000d031404c149915a40303000041700d500201604e000100c0c8115030100042d0425100740c0020b9a0081d82c401082c9a110250f0014100701e00402c1070000341c240001518545065000d070032402d000500b80b0745050342d143c03902e030320344981c00d8100c2c080210790b03605120442d82c040c814003000f03180078201580c4a00c2e42c009802d4a078054000394501641c0c450100c04100721400f4000c01d00b60800520284070f640c0542030040082d00802c1c0c4540c0903016040002c640210014281d03440361405903 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 145484991 1250 145483741 145483799
    0x504022d1009030b07231b07060903020a031101140409090c0e090d05031b03040c0611070b0f03150301060b070201170903090d08090904062f0a0c0f050a050a0507 71
    0x85002c40e20302e5410000f180c11300c94030030f500d01c521030300d01b5008020003a10074017880784d400c410301441801c04e00280e10030401d1000e100400c20050303c6c1e01c0325120440790071803072002822445c500140d40744407070349130041c02034140007401151744009640311500c164001d03402c0d50212610340d14060380e240c80580d550321441c0e11210010301c8441c0304000555001c02d45c031642d90074218010b01180d100303400c03d5804580301070480c601400959031040030740f00c40200e164001c114080c6024a140c005202d9208101d200810000000d040032000e1000718101c01340c003800800c0100d40d03503140c00340035400c45d00049000031304142d5102006010707001268001e604c2c59000e540340078440010080040000d1400715182c22082c4040740265582170400c9103e00c0c0222004910003030040d0a00e02008080909100402e6070031200c802031040030000d8418000709410900340030300c038030b0800f145207850005008086128202c00c040c20801c0104e12480c04500c260221019251100300c080c01500e40c0b401545c0c3c01c01d03004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 145486241 1250 145484991 145485001
    0xa030504121502040e250504030f06150b030105031504170a11030d09060e0d0c0201140c190308071706060a090e070201140a0209010c060504022d1009030b 68
    0x650740d10700d055486103200c5000701c100d840c0c00303409030780040d8094109040321004001d50b220888140f184003440802c031074510700540046c060300c0e074010b41c000074206d8140360281c03c0c10400141e0190701040016030202c07003040e50b98200409264824018540240200340110362070401500c4800d00032980802c00300f06c008109403080c440da80200c400d0004002c3c182040d0b0310000800e2009100042c0c7c11000482d1410040c105903013610111400750308547e1041034010806036104a0748911507a0910b01000700c1030f1300c00300c007a20380d0003204282016802040400c0480c010b040c1c2100d079031a4882d0319101c0700e60b40d8002080c0c5042440d1160b0200004000000401c1c80c0f4291008090061150034201c24203a2640d0303144078224011900700001d41c0d582e0050f01152500c410b800d580c0322030000801d5150248160009020044850006000e1740d00c0d0004102199160b0750910b0308150080c07041181d0741c03195031001c50748000a82e181c9000e40900c15440c07a01c00d10592a9500743d90300300c82481d89603162 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 145487491 1250 145486241 145486259
    0x911190b030c0a02160806090c0a060203160606080f0102270d0303020702042a02060f06030706030e01020d020726071106030a06030c06050c160501140a0201111314030a030504 77
    0x10343e541c0441c0550390070600398140c404420800b4000c407130000d103030310301d071065003c0c0c9481d140da081e02c3d01c03c8405e01c10400906034004100c403044400c41d401107540769801c0c5060b00203001d40f9000866540582104c11f4a034400550151284800001e88420b44041c507a5071521900c141030202d41d0406079068240700407034000d4009107450381c405400020450404100e042c0000a819008039036014520000a60311340c0c1088615005040c094040750f09040c802d001179611503c0c0c3c07044c0d00605858040e0000d0340c2d8800c0d41601c2c0c1c410090340e41956103400c245444003001d0390112540310031a9100312848050340340078080d00d142a82c8038046000d50011a03040040b1038200420381103a00c2c1d11200040f00007520280030000030115921819140d01070100400e040c5201d00e154003200280410040140742ea105a0100a6001c10710084d030f5603c0503908100e015000e0f1a6001d1700400307001a031013a0b00c000c0c02d0340d81003c940000a1960180111404068507540c2082001c0c0000304140014071422603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 145488741 1250 145487491 145487497
    0x120a020405030705091b040b0304030e011107051002010e06090705010906081306020c010e0106060315050d0203060f0c0f0309030409271101020a020310020706060b130b090f040911190b030c 83
    0x6c1d0880c14103010030081c030034048140e100b40c020301c40c00031021050008054100214100c05403090030445849003a4803400c1d076841801d4400c9030321a207100903402030344a00070340c0300050150b4a40c06403402440c004040329900c607000e100700ca0004205144c000795103440b0f902c0e5540a50303110b03090801a8000e90316020083d40007c2c503c104103560341c0ca9103202e003100910954000302031a803000f0070082d42403030042c2d01911565020b1405040311030012001a0fa020480c2c03030340b01f4004000b0040e42c2d1102e031180b94841c000c0044600064000000340440104000007030700840f04a040d0901004d4840f02903000102068022064400c14042440700094948070b00c40383c1450040c4112810581e107600007e20340080301c2081c0007aaa40087e41c0000e005140c020403015001200b00c00745440041030941c448544544940c03031000e0300101c0d4052255130703018405d10f03041c40010024802d182d154108a215010f4281009202c0c0c0c82450081903085401d1130f19400f1622402580d608684d82d10940c40c00c60380c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 145489991 1250 145488741 145488751
    0x2d010504050310050604110901090e0c1201030f060606110c0d14030711030705060c1207050a0b010603020a030b04110702060304020f0a0f0e070c11041508070902120a02040503070509 80
    0x42414000454a500c04002030340c540d086410340420b04e13080640521080b12041004400048420490024140d0300102d0030800c448141213941070696a801d61a52240035401207514403495034000003003400054546500f00324001e46007080728036a1000141c82c08002e07204c0f203441580284a038980c152901c0a086001540950001d02c11040c0c108a11800c562100104550000c46800d807054181800c000324800340006581e054502003071000170683d194840b13004503c4070f000005150082050902ca271105c9958440c168100039610f50364007401a4000c14107910029291040f440000d14044c0500301d003c81c00c0c15003a0380303003142d95001d000c401c1d07100400c240e0308820fa14a40e0509512180202c0c0020040c4103c01c00c0582c0c02c00e00340c0c034a1a0380280015042080a401e00d102198003030326419002e40b412100026203940708445000060082d6014903011701070420300141c05000b42d0002e201d499000003265032955284a803040c1217004030b0050035015409860140010f080144001d5048 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 145491241 1250 145489991 145489997
    0x906040f15090b0702030a021005070e122a040b1e0126090d0908010606091211130c03110408060a0c050d0c0306090606030902090f060112020412030e2d01 68
    0x10440d070b03210b90b440c0358001d5484e07200682c00000c103040c00c0e075410300c80c088542a15900034846030402d00002040039008401341403107000303c03000d003145d280c2080040d00040c2c114841c0b9143c6450038254014211b0901c128854000c905180f00403100d40b83c41003154043c10707450358010058016142c01154030701d02c82d024a200b00322844009954400c02c2030b02c024030903400c120003405d101070340c00c03002481210715501c000350340da050207401d1001d540c00110b42019515002149403075102c06040c144146040616141c3d040401c817000e0799006192608542d02000440d1020b012049420040c1c048078800c5111307181e03030740c1c0000c0d0100b0032029094100701140440c07450a00d0803d102c03022148200ea640d04c0c2c0040110340c6c0e44c401040001420700031000200300700d060820591800341c02056403d84000d086510038220940028041e80c001c1c2d81034440090054011515a03450705000440020100029400b290690b402d41d600e6240070703d91036080e0307805001019011007440c4c421103041c4000c8004203040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 145492491 1250 145491241 145491251
    0x60106110f0a08220b070201030c050c0606061804020d09060501060f08060609012304030b010e04080a0e01200705030c04150303081905042103020405030a1b0803120405060906040f15 80
    0x2841c45802c800e006440c402171421740c2c4d20380781d10001d81200c0040180c07a040c00800d1003100d108000100303031580c1c455070540ea00b65945d0300c800410300204d80c60982442d070003440814482400103035584000c10082c89004104096601c414060320740c01d01082e00a000150100005110b0b420031602401c04020181012008042c100200340405140660150046ca0003c1401c106000c014100c26005002a012580c0720f03013003a4560750581d1043c07450700004d1103070465544004c4c0e4440d080d026130704400d100b0911828683c0a4040b03450700c1462244030700c80e11500009800c50320741445a9100200b0f0310030103210035031460760191000840280103c40c9070a58112014070300001d80115403066101e021200002c42d0032190401081c208131024400300b52060100b40895240042d988001a03045505644000303610100708005200981006507603010200c0c07180089064401c40700c2c0030f544620283d400c170760340d07010038266110700c11240500000c1341c0480e03003000f1401c0e40d259007548482c40710000c21 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 145493741 1250 145492491 145492537
    0x702040b0d0519030201050f130615260705060a0504050d051f0b01180b04060e0f0d06050403020706110607110c04090c140303030f0604052502060106110f0a08 70
    0x8142020355110401c2043e1240d80e840c2015428400c0d81e0303221020388840c551900f003240391054800c1b080c010080149550f44081001500700896410040001146200402e000391241c0b50400e010352552103080d00c074001010a1900d0180b050700e10036825a41c0d010300707207841e000c204918400a44815900c1e4000d81402c82200450340b8000c11074070344a4180484d0170b054403800100078142407249180080005002403042001c0c00080741c04032000c0b07141010b13054101c500020b0400c450084181d500c00345102450040045503045640314500a80a6414403a1b9807041951100d07811042c4902d40d8200c10005402c050240c0712481d80d07224550201d800702e0f0011302c0030070100e034020328040e1050100350204010b195921180041081e805402550035402c040040d10102c0001030580b03849151140c000507100000d004000042d0b40003c1c1e05001c6400f1101c1c00a515a0303420300a080000f20218980704120000080700d0711305500c8070f8028400b140444c0c80b4941310f81c01c40245050b55160721004c0c40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 145494991 1250 145493741 145493743
    0xd0c020d150203040209060603040f06021b0601120309151407061d06010801050a0c080a1d0703060212250c15020c03040e06040b030a030c030909020d1e020f0702040b0d05 75
    0x72a44888a080140c0d281018010006200c10040401c0e109110410400000582008c048600d190f84220b0250301c0740000c0440103641c92a04050401c0d174481c0b8000020403884071000855040d0180e126074000b42e032295010245070360310f9240c0350049a04428118020220795004084d294001c00002071700340000c905049282074012000941648550018440e104080c42116002817400c40c00b080501c84801c009015510010b00c1d80c2041940d540049039200e4107020490482c054070390941c0c42c0c007502c3c0d24110000b9000364403075115900344080001c00c680c04000c00d02144000c512035501844014001c110341181040c60121a1703200c41c80304101c003414581c009440410b80c0c50b0b01454039582020a8142400e100900c1da0748910700b0200d03d05840c2e10081a18001d20b80c140c0f40c050000546230805490100080d8440c035901072001522150160595100342070050040808031195824a5400d4003039001e080b00305856100d04010080062030183d0002d210100007615100320f00040791942 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 145496241 1250 145494991 145495013
    0x9010303050304061d0a020f0406060e06070203071d0108060903071703090c040f06081614131401030303050f06180106030b040609020304030206041b1512090c03110415080d0c020d 79
    0x10295031b009180c00c00461401300c04100407610252420000e481c0780c0a002461000080400d60141c00002000c2041d92020f00c00c5401401858140d07001081c000d80c00f82040c42024401d044040c06100d01080e004400841104c00c101c1d04000b03011004440700044c8095035202800141d0140310700140c40095486d0b5008800b0000c07001d200c000703040361804c415941000816034021382083c1c503040c400c0c0b100d814000300c049044102996452141c905084074a40149105c40f884400281d20034000000c069040c0c0000b4414003000070341e905c00f511988144400540417a06203c00c03801d990005210a608c2540141d641034401400802c40c00d81c0c4180c0f08040760f0040e1000c0e03006811020400080c07204801c1c500410000b0501240d030f00e10b180c4651914891a5802d20000304107040d08407003c0c0c041030342c112071050340e007080c203400d00a5507038685036103502c0e0000c280e24040d03810020f40c5e4100903241244141100e181d0307005404a908030020841c1e44500c4200708a906c1500c510404011428140807 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 145497491 1250 145496241 145496291
    0x3150506030327030604050f070807081203090a0b01240e09041e02060c010b0a080f06010509060402040302191502010c1b021f0504050114031e0c0c030d02030f060405060901030305030406 82
    0x24003103801d00c0c0d007001030270040d490304004866446080c081000d10400100314401d1090f42ca0030340c0d2240c54400d9076504040c403180b0060151210a0008500d05003041c0903140e880c03240c080319207284e8020645c25128406d0032540e565111211074001000b0942403402920850302020503004040c0c0349500044c41d540182c001c0d0041e60b90b560050b4030807030502c080310030080c0c84c0d5103000303001e030052240c0069510401401111701640d032100105116484030780654010710350003001080c00c0f00c0c1007504034042c09824803803a08180702035080f0180d4140103106044c01205e55030350f0b105541146030810301c90249882c00890300700211014080c9659402c0303010500c0d41d032080e07a484d5641c5280900041c1303114900344900540a07020010f0210b1480d40075921940078010f1007040c49650783d07445a1305643e003e41c00841c10385001c001524482c002940d030080d44110114105020079480d040f060104035081214165048040b800c014404a400345000c2c55201b445044086841022114030102a9150703c1c5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 145498741 1250 145497491 145497493
    0x30f020c0322030206180a050402040b09010801140d020d02190e1f2103110106081e010902011407080c120d1a01050301050103180203010606090315050603032703060405 74
    0x5602c90700e14801c1c04264490200c0200b19614103003180c00281d071038810041e6400c021141d15840f03544585a440c8010000d04000307104545440d80c50030070003516801091051b00107501d00001142401c98030507030401e40100038110b0041008550b00307210b16811050016a030200c0f100b03107490704d4402817241000242280c07105c00d00041c204808219408400a00c0d0200700312040181800380d5140101004040403100115850030480c40c1000d8401094400c40c4a02650130118003040043d0001601c0d08480d08484652111a83c1019014200c4012220007800a1f2201404842e00c3c40c40d14040d10015006a210300c1c40c00030b40d048080c3c40d01c2d20b0a41c405055440211342510349040341d1046104c0f000350603c020b108290240c000030014441405264141340e43c92880020140e43ea00328143c40380d42c007400811465849000c041d01070000c0d4842140c0060300100c0e007203400c0e200c500860f401400d01800443c11314252403002ca0442045150403880f92040007160300c1c1940e010042180941c0c0118 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 145499991 1250 145498741 145498747
    0x30e01150902070515160806010c020a0603150503070b090603071101061401110303070c0201300e0f030a120b041103041b060201140c0c011b0203181503060d03030f020c03 75
    0x444c0050030162214601c2c44144210300800c0403221a002c0000034460262805d0030003680c40c079005030707038880301c0c107401942055404501054840d0540d000040c080c402119a84143e9561010140d9038040c2d8066820404070500030444142000009980c101840c1d06040035409070004e451070841e000c41d07004802c1011510303011041541c0000e402c41e40400c5503405980f0f14034100d100602a80180400281002508591050314884c0403966080c10100311400b420006280c50500c8094211101621018055076001000035640041220140d904540714298420000407401c0001c008080c41141c005803280c02c282081e00954004506ca244543c4149000c448034a035000e000c00f14a8003e00b0a5a140c6040c030b142010b100540264007004a024491740c0c0c10040343d1403400343c003440410b98a410900341000410980200c05840b1941c0440103449c441002d0b10b04202d8202c08202400100324400c0001c40c250342001c0580103ca24020b0030f0202e02e130701c1040c4122040b603000c4941102c9641002c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 145501241 1250 145499991 145499993
    0xa0302150a0f0e061602031e1c020f060a05060d081c0e010b060417160608012310050a0306030209011205010605030a0512030703110a1106070801080d030e0115090207 73
    0x206907410003400c00c91030a40d000e0031660f80855981c2c8540c3c1002d280c4242c410340040210740e010000030380c0400104000107518100c82c020503988018005607891484e05c40610744040900c00210070f10800c007031200900301c80e1580e0103144000d01005d02600c1e0001070a00322100440c4000f801804010042c0b042801451114812101100e400413062460b0344d0500e516688184e80d5501a90300b030b02c00700120300c0300003c0c6451a1038506160401d9000030100c010b240011800d4010b40345504071058000000c00e14046a40c0300000c10000c2d9407943c4e400120910500c080600c20000792070000f9180c200024802d40b81d800040001c003099100e501585944510501008001e01030305009080942c0103009142d940d0f41c41685410000005441411001c000946518826048680d20342500380c981a43d51902400c020001c20032070201030124860b010100e114144500ca01070304942945001d810030a03000300045024040c2100c039081c0750340d03d03600c8907800c17010b5804041004120001c4016034030a05 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 145502491 1250 145501241 145501247
    0xf0c03080f1804090302060106050a0309050d0806011b0b01060503041410020901090503010614061c0f052403070b0307050f041401080c030c070602161b050f061c02090a0302150a 78
    0x40d600c02c02d01650514140c040002c2c1c0008010b0b0540b4a503091007601c81c80c0e8070b0b508900030030714200068818424990414140d03504840598003a080aa030740714880d00f080c049860000410090080c10b02046000405c0402e01c90742c05150402e11a03009034221382c0540803201c5c941300003100c0804505130b001800c91015a080210b11000744025002485070901d02000f1007070300700e049190709005210000382c0c0703180741e0b0000c2401026542541800c00060b24000c070b03105d0040c07038102c4440340040711001c00c580340c020140c00c000d0304058000f4010b012050900041d40640d1300b001d0000c82c02d100060008034650100c110245c8003034540654240d40e40402c1400042030414040e001410100c010402c1c0014850310000321001c1ca40c0004000d82da950140b455043c1c00d4102c2000500445a804140610045e0060b14002280d604842011001400e00200402ea00c2512083c020003d50840c107040c1c2551260050504010002c1024960566036008500c204100c2038102403039030f100280d800071060f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 145503597 1106 145502491 145502527
    0xf030708010603031205040807032f0f061006020706050c0304051302030405010b040b010e0405060d140601150509010e12010f15050f090907030f0c03080f 68
    0x80d480340303428000e203141e00049002881d401088605004540659402503400c00e181900d040015034003a662108a46d450028000c0c40c00c540003071500c42c20358895070383c4040300080c0000d441409101e41c141742c00200025421480101d051142c194002410025250b240c00e10903034545000c10a44e182d0300603644240e600c014a0080c06074000ca580c0c010314080e51044009100b0b01134414108010740704107141c4640061401c02d0080f9851510743c01080e04807002800c000700f030200380d813250603401000c4202c211899004400420581281400700750480700c40d880c01500384040400002c100382c5001600621035201406110b034807003000c0d0301c03000e00c1900d4440208207891072520811260422403143c140314569403007001020f4105140003038440d41450000d002454155950300fa1004100d08080e01c078101d04030b80103c0001c40040042c801d080000010580f200700300916901841 = true := by decide +kernel

theorem cover : BRFrame.Cov 145323741 145503597 := by
  have h0 := BRFrame.cov_init 145323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 145323741 ≤ n) (h2 : n < 145503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
