-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1895
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:03:55.378371+00:00
-- url     : https://prove2.me/submissions/d6e6c192-d3f2-4263-803f-846ea551e4f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 340647482 ≤ n < 340827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 340648732 1250 340647482 340647487
    0x50306011b060b04060b040503190f06090510060803090a060c150b0d0b090d08071d01080402041b0f02070911090f0402090d110109050f03030a23131802 67
    0x55599010010090007200103005625501c400d1a00901900302611503641c058107104c80820384400d81c5004004541c1d0440480e480c09000da070302c004122003210400313001e0301108007000001c00c1094021164883c40f540507120606200500d6204441d201d4014407150b0340046030320101424890031030005840d26007003400c481d500d81c0c1d64040b09100e1b16007052064584900c460304454460020381c880b40e5034401d0f00324070785180180f00c1560303400c21800d02078009080304000c510308500503441040312400d005407032400048030500646441314083e0040740c11558645000401000c0c0d034040741907019035550303018002a1030036802480c081c282e40102e01d074149080d805030710701000c2a045440d00f100c00d403401801e42c02c0f518006002800361451080d081003203c00d1034410041070001c0500a004240c90310808151164103020084c48440700494040d8820403261010034082c0c000801d050038501d42064410321000840c41c038035044068040d0031700301e20072410b210109001c0950501d40780240703802c50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 340649982 1250 340648732 340648741
    0x703050103021806092a070311121201031101052503020c010801061d0f030106030308010911070c03060f0e011109010306140a060f02150c0306040b0409152c03040f060503 75
    0x11003010000d4460751020454210080514906c0c1c01600b4001e460060b4054481010b41406400d04106082c2100d09001d66090042045000415a194214181c2020083e6800c41da92611090300c518803641c1441000d00449410800b480d1050156100100c1d142f00d042095140191801040001441c18000224018040240e11803071a80d0b02c508075060700c0070200085004243c0c007100b07a242890f055424081e000c4141a041911a4100c8142d4201049109018240d81c60715010300140280403d1250008001080450304040c032100340d41c880002e40b03a29600c19007400c60f0100170b04803403100c10205080b200b0b0360b0940303c3c4000501480b4400c04a000c0308000203141ca0902d4003822081c024418242c801e154401c00010161000140429045041140100c04160400c880d203a00c62810441d0f103407030302d00b014060001074a0b404828210035008003405c0801900074100740b0181c200c070100328200f02142580c0480364a038404000b8594403400c01034400c400f82c01d81e400840c00e1003020801d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 340651232 1250 340649982 340649989
    0x23010507082412030c0d020d020c01050f090f10090528050108190c0804060605030a022d040f050406270b0a0204050d03021005130816030c0b0703050103021806 70
    0x5650340c040740c41c0100c42d4021034001500e546510161180600c0040703040010950005030881c0b1248039a02101c1d8102c83c401d00c126950341e000c601050002e00e00744001401c07401c403074016048800004000014404210b004610070139000c600c03840026031200304c00c000c14200f80b403404010785404031005c190407401d12119448031b10300d846498100f00801d40001d00203996900c2407140c00811302030a0248103448c403402000e04000f640c0036209540b0b40300700080e480ca4000354103160294050528000041c0c0e811000803517003151480051402101418000d00e681c5a02c20031400100e1000002150b0600341081b4049420a0084003200c0e62007001200e0a00c85003002038103c0c2d64030241003900f40d960141d51102a00990b0f00698110100562003010550003090800d40300c245000100041c2da10854840d00d001104180940305045c00c00c0415a035600e00c1d0a2003040c640039041506610095645d0000320b040c0464903080000c0c0c5e0f980040c030031850310f11182c041011080301d00c0c1c200d509210002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 340652482 1250 340651232 340651261
    0x10f0e040f020402070f14070f1d100906060c0b0609060603161814150913110702091f05100e210f01200309070b0d06032301050708 58
    0x141408007030100c40401c6542d01d804598495511407904803d09002d0300e001010b80443c101c8000150107a0075000c6003051403017030500304542d41000f02c008203840e40008000e520700050105c02401207140c40214040d07100c0c1c02090000c005e140d41c4c3c144d03000346a0509051008016001c244942c01790824400c0b2981c13404192a08000c030712042e0100400320b201c2c00d0b1012a100d205058610300c024100165421200d9500844488180d0301e07441001c0480c091140d480c400c01005560042c805c100304081d0302203c1d80030305080740c01c05908501d44441500043c96000b811602d855002200c3c103440f48841135082c807000b0007400300b40e1b039081c01d2480b4440045c2c00a42d000f6500c5000300c1100c6c01c89000c100c0912030302020f140210080e0b941c47c1d1942080980a0f0024141c3d03214401c06000c80800c03952100030440b13109181140207410300604002c100805c582c044a04035500c2d80d143c1c503012001c60100583c050604007071162001c42c20b020300788041d003550002800c1c5418000c0c280204824071520809 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 340653732 1250 340652482 340652491
    0x70906120f02061605070f051201050420040915050601110706090302040e0109150b19030221070b0412060f05070e040c0201181a0c0a0c110d02030a051005010f0e 71
    0x1034040d10750302c02c4c07a8100c0d81e021918501034601d1160100005030a00d0400d040420b45034280d80301c6520102d000a031a00342d0b0010342e80100400200f8007500140d9100c103400c000120802040841c0344202070700c880b04084040002000c5040d520382c2030040c0740d0b8210f030040312280440741c0502401c902d04080a040b42c0041c1c070029000d070382c075409160351000081d4070152249600020451203070170038045c00401000251011806005c0c0c0e50f254003421240d40c81540101e0754018440f80c80c2208a00b2241d06100014810a0303503845000404100201c0c100f0203030014046450007628115024201902039944625403200000d103040103005505034030022626946009035004a809054018100e005040454148000140030b00f62034041014800031039a603000017a014680340e868044440c00340740b2444c41c8083c04241d100c41044009545245403e00f062070040180780100c0d003d401003424035489074021121604035015001e0070340f17900c2c85014094540d03090f801c11401d013401e48503401114080e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 340654982 1250 340653732 340653739
    0x601021b010e0604122a08120706140403020a020406151d010e04020406090e09070837050a030206010e090a02010302090f060f0403060e0d05030a0b120f070906120f02 73
    0x41c010b080781e140c0c0e004440080260f070030710080312446420280f040324084802c070f0340170218581090700c00404032800340043e2030080b409001240c0210131005840d030301052040340d8507502e03855010750a4140185807031040b4046d030040c6c601c40126104200484c0c0480d0040013060403010320401e1540c1d030224411010203511950000300a01c2000160760b071605e50780540d584207000203008203000d40e00c603500d882100c840d40507487d440e85800661544504041c090703510316034480c50403221024403501074072070640b078890a004c3d464040081b00003110418440c00340c409900c410310100c00c069040203500c0c010807a06031204000e0401301e01d40f039201c501c0d50304042d04050700030074805140d030b03141d00009400c028000d282503541c0d40c1e2a040d02c44203070031074401034030f0b95403500501360681c50010904002942c0aa5125840c599038609448004c043c1d482105030810041d00001802030001c02c415110181c4000c020100c082c5401c8215007541c2e0700d070300444104e064101c59000041d900d19004003000e0b5044 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 340656232 1250 340654982 340654997
    0x307031b02030717010b1302040506160c0504050c0a0e01020d0210020d0f02190210020f030f04030c1406011505070f12020307170d06090b030d081e1e0601021b01 71
    0x303000192400140303403c8686149580c04d00102d5002056114480c154015607500c03101c0712a0000d400120702592164640012041001d13002458242c03800b0900240b154640c0504035031201c0218003103845c122a6081d01c40c5000a21030755668003c40c41c5040351030240300070705490300383e000e000f503c8400040004104540100d06004000c929411810449140000454440f21b494810221a44040d050840580907460b042e0040005070b0080b40e0380300d8269101c59165455000910b145c1c0e0390001d20a4007000005074074174001510b0917000440300501076000703040c1c5505103500c030704110104150030028403070708214120004406031071402500b6080300c100b500c0940b042e4400d0303065105482c1e0040ac0800c2480c855082041c1c2c1102074540782c80c040382d00f0000075440e00848030844001c0003416a2640c070131704028060b13500c141900355005001146a0384920328039110400304034800d0320441040700e01c41078002d607854001107081e54020340910060481e510031003031003e618804a11506c0c10031100c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 340657482 1250 340656232 340656287
    0x60810051c1b05030a11180709030807031707090302030d05041208130e0708010e01170c15130f0e09060c040303030c09030b09060906070f051c0f061511030703 70
    0xb90150940181006401e56038200000d10741100b15852550b01140b0034182030031304c080f4280c1c0c100340c080e00c58070040c0c584214a40c00d640340c881c0d490300008400c81c208030807814070704140848561440c0c000c1107203880b040341090441c4101414201c9403030b01c1404100050008102c03042018a02e0420f00d80c00181c0310781c0d00c0080040c01c0c42e042030b1070740050340e0f4458054148684039a001e4035160480d002c0d14440c0301180d072a01c51611030501c1c0d09050744800d034005c1a0311000f40c680746650602013000c40d20900e02c0c00d200c1085145001007690310030700c450180c042c403c0005000c85d44801d988003626801501d5a4584072124010707500550101800b09aa40c665519920740160000000340d504800c4002c840d181130b238080c5586d02022a801c1d891401060046952640203c3c401d00c680551912618144224003801703181c400004090b1200711901c4a4001d210081644910381c05003420709009921140d031060003510728801034542d9031f0710390703c1088240d0110b13030b00c10803450a03610000d8030500100710 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 340658732 1250 340657482 340657523
    0x1509060a08010207050a0614010f05120c0a1805060604120f062a020d020c0102060a0b060712030221150f03010e0f07061b050d08040807050601060810051c 68
    0x1200d07040082158400100b48040c450006032604440d4032810091140d08220701c41915882000c1c4074131150f0782c13620301080c0312a2415a44010354508000100d8441c107400c100002c404500590010f081203440c901180311a0b1841c0c092294842026070305035190519080b4034413040c80c0003a0024002c0c40c1a101c0c10070800826400c4082038098885d482c0c0390341d43c1b07031007007100c0581e00e6905400701522403001d01450480c000301d8102c0044005802508456850f082030030040c1260005c44da0303201d0350400900c0b001601d0400c070b0b40d40d50059580c6c01a118410314100070b4001000c0a01c0c40740f40a2080c0400000d007043d0441800c1d0300e802903503d401d000e850302020074054640314000315040c0c0038510301c4101d40400060305000319000307961151500c7c400e080c1082e00d034100d80000507001e0380181280f01c03507003400754903415041481406d401c1d02e810045e44803a828088203801c11000940010144031000e003c07003443d00064042118024415010001841c020040101c0300030030040d60400000071104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 340659982 1250 340658732 340658749
    0x1a0409291b0c120f031602010e1506040905070b0a031104030f170f03090105040c0b090105250b010305061603140402040b01051c1413050615060706020c06091203150906 74
    0x81003003041c261520300400e0060f106170011550440d040d90b048894001841c814002c412400308000301420307402c1e404042c0d8005062005080c941c00c075440d43c4000c00041c1c410001d420081024541c4191626840000101a9400e20543c0012440144401e10115410121000007140d00100170340b80005410b15422860044548034142c4000100820000207019000207100ba03101b080b18524541e02c5070401c010a000d45100140021014858006d07040218021035108540003180ca4a00e00700c5d0b90f40f565052a070907003080701e00380c020f042442003014111222460030720160406004010384800d131003192490051029202da41c891180c0c003050390140b0200d070502540e0207104065014218a94006440d0000301041003a291400048448181c492501700c815446009440103448003030b4900100c00e0440800713540046c040003481c0010b0f0b00c03031004000c0c6080c41d90182200c0e1400080560414000c1031003060501c000300f0410062542400102d2454a1b08440810003500c3d0400032501a8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 340661232 1250 340659982 340660003
    0x18070905090c190e0a151d0c031e040c08160f152c130e0606040b03032d0409090203060a090302061807080307050303371a0409291b0c 59
    0xc600500c001c160705900c2440c0700c4441c03a02c907c040038141c4800103007601a20040380c101c031182e8a08804d1040c2102080880c43d00076004050210a00d0348403010030f42440e014066480c5250340c0d90303000b00110301241455200030308070b02204440000c280702003e0f00c0303210081040056041030720721099142215030303420101008080d060444035101829018010520310750411060702c81c5a0000341c03149800e0103010103018010f40910708182c2894402c84201548610b1440c01d95103201c4454000400c1c900500000c0c144200c001c5a03505043c010307d814244c006d00704039070580c00c0031036600c042500020815000a21034580500f03000c0200000b5003003180c5504215110f000006000e420310800201544c003404419001d8242190060755a8038440207030034a02da182580c1d540c007003441e00d580e50701024408a03582443da03401e41600700000c0489126a404549903124004ca000d030642118100b940c410f0000700582e000d0382021801c80c0c4202c0b101c5000340d0302c03501000600d20000d550a001c4040003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 340662482 1250 340661232 340661261
    0x2030d0b041506020f0c06041203030b031002030f1608090601030209060d080f0415050a1425030903060b1804020f0303040305061315111218070905090c190e0a 70
    0x2d850f12034500035103800e42c507040080c1c07a21808592004900d400b804990840c0d249841d0720354034003015682540605074045c08103500d03004044104c0c5050f03900740003e40c45840281c001a000349000034074038110034204452542040f201008100200d00001182c0741980d4045443e09295a80c0c03000081c1c41300701550008044080c0840c90903881060400540203075011024084040c56603200304944600503024410005100020400d0040d04154014004442c8a404e00c3d008006550f5158500d086000d60441c0003491082c01001400310900c036100c1c41c40e6048903020712072900c40c0c540c860a40f0f0045c1000c0e101e8003c21035002401d543c10004c8034021a444000c3ea03415140c0144415510750f9044c43c1942c0950201112034040b40c81e81c031507494850059522981009520350b80342c007a0325001001c00d000c40c041303802459114001040100020a402e08011031646092407003170b81020240410280519012842c200d03140700716181c0381c016604c00300c46181c02580c41d1740c0120041d03c281d0240030769 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 340663732 1250 340662482 340662521
    0x30604150b0a05070c0e0c030406050604090204020f1c020408030406050d091421040e0112020f04180c09111b10050c0702101403070c1104050a0203060901090203040302030d0b04 78
    0x8560020090701c4045d0152034540c0d0425507030f1144040550f0100c42c0460750070010170026001880a0380541e8014030081d00004408000c2c0d40450308030f0340100601c0326401c0c0302160507141451201c0c212814241050303801c0d0300701460106e42c19641d00490140c0000c1c88008039048071600d0030740d03004d80300c000d0300460194410170a00c46515190100541c04840c0c03c000c05001c401d80360781c544100d40c100d0ba084030030190076a18045860f03c1106081d41c007280d00100031135503150640c2d6030b801071809501d00c2d9080d8801244880c82e0068a46103280c0c48142100e0802860ba2140400f01e400d0b210b007040656244034809140448450501c03039984007480c0014070b440b00340611100082d019040540c0300b0782d0b03240394103480890107a950114a03400c41c0030006082001910141c49020f07547d907040d106d14075000072031150000041c10ba50040f104c624040b43e001c004c03c8800e00e041c4054174010094040c0451131801d180d1802500c0340308004081070403544507001e2510360744640d403090086100455040c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 340664982 1250 340663732 340663747
    0x703023a0b01231c150f020a020c1f030b0109080f0c120609070b130315020711010906080121150c110d0503182a01090e010308030604150b 61
    0x50101c2030003038210303d210003a5581010711900100d00286a0300034291489614805641501c00c22103400850341c0d9120201c02108419082c080c03141d8500c2250405a11403100460080c508842240054810b100c4901846030048400d251419002c69a01e00414001403000050380ea1203481c0d03204948610641d000711100650215544000d401c0444500142c00c10f0048007036621401a0b45d280310f02d0300440420807040800a004241e90030b41030100003200c90b03480d2100d51010201c1490707803201940008441c0104580955030052100c002d0a00750311b000d00f400c0004064035014007c078000600501101e6031302003180080ba9003043d500440041b000b401140301c3c50050249143e812011480002250101d024007003050210700c0300b00c3d6505421507984411019413200340110b440045c0c050040342700040da442c4400803481c0c49618802c4101e00c0d090000040034540c1c164003000344080c000c001480080c140c4070803039400c40030407100866110320240800700c0304d01d405d42c011341c02c28000081c3c0303c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 340666232 1250 340664982 340664993
    0xc0102131805060a05030d1d0307121203021216090308190905091905040c031403070b01080102040b0d0c022a0306010902030417070c0b0d09050105090703023a 70
    0x16011941e901d07070140850b482c2d103401e01019148501940354140c1105203121a403c0c490400010741c41003504404040c1c0b520680407908100c1e03103400040401002100040030306c4801c02d042c0c40300d00c05914046141052003902c0390b020804c050720642001840c4101b41e82c030300b403013250fa542c040c0d6005030303499954140b40f12039619404c0c000b00c1c1000100302920000581460510303030a510814220b90050312261241d82c03040d009090007802200c0950087c1d20100108040f1841c0355025146000291303a42c45490410880142c4141c0c011200d130380c010002440562240b90540360f40106030103002c200c08648090503030400c001002003501d04199100d4140e030304048005200e001c0f0a09a0590f03810340d82301c18501c1c00b64401180c1c060102d8070600b100b0700310811550010b041d00d5000d20000d040f8280c4585510b035180c2d12a40d9951183c0c1e07180d0a00406100e03085c03082540002180005000c034900c0c0d580411041011110f030f548480000d003003069545405c07215000b00f5100c0c90307850302c000704070b40d0b1500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 340667482 1250 340666232 340666259
    0x30406030605010e01110c04021b03030405030301031704050a0b0306061210051305060906220c020114010603140615040509040f110a1424130302010f0918020c010213 73
    0x2d441c001603003100d11907515401350745070341c40d0300d080e0308042c00c143d01d001c1052102130740c0800c200f0840440301e000d01c2100b1203c14405140161b1141c3e0203141c5d80d52541c10405c0e019500e940c108004021708000070070280d61144040c3c4202c0d101c6001c441d07160740e10080024594003078044440e40d102c550344104a590035044180c00141d500450351070484e04400705c0c201c4200e5000325a555080251400800c0503803500d900c0d1441c48501c2c00c0662900701010b88103402c251248500b249015079180c4400c8000e115081001ea8050300a5190400c102c42c0d01c514801d80c2804c014001ca0300170000c90180c212050060700840300940030141008040d41818503050451590711101034505410a0340c00900c0c9213000301e140012070344840030fa407540140072000c00c8448a62607020441040e003542000c00b8004454015013080d02009180c07002182c13a500004d090f102040c842d040410407850000c0c030900341c01740503450648140420040c0c85210000d0040e0083c0300c0d008186244a18001d0002a1440306901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 340668732 1250 340667482 340667489
    0x303030a1506031109060706061503050f0c12060d03110f1e010c05040b0901051c02030609010b030c2a0a0506190209100e0f041a012307170c0304060306 67
    0x1110150180d48000840c100d0344c0795100c440a250080002c205103160030005002c0041c0280383c0062417a0b170744d42e21000880342c4c0c5510500030a454100300040507426460580e40b001984d5085407078030300d03804400c100302000100b1981c80382001908550605119000c05201441248115000054144485070380e4505d00078480440214031820815248418001e03c200f104046d2240c80c03e15060840c842482d412003800c1d9410001300740001e03075003840510410b000324403280c0001a0341e418010203004600c6c805070803d00011a040050000304080c1c0021a0340c01c1004803081211180764001c107a2150300c0e60100a072140c03050404007000c0c0400070035624021040224205e10b40410040103c0076401403c0d00640d01c1000b000300059010700a901c400001c0b4001002541110000d8000504840d280d0290a61909142955408a51b0071840d6420b00002c0400c4000842d001c2e210768051610a0b5040203100c0446080c400704502540d20a4420500c58002625181c0d07403a0074000b40100030034072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 340669982 1250 340668732 340668761
    0xf10121d010b040c080402011b0b0c0d18020a0b07020303070b0f16030923101b110c0916020304121209050609090f1f03050105090123190b0303030a 65
    0x5903015407403c1d10130f00341e80080f203444a55441d55107800540d0007400f00001042c01400402110f4009814050001c0c07003104c06180894444507070000180481d0007036506000340515120985000d40d6404154100f103c500300c110684c0c4408c01e00c00319041d40036505005081c02503003000d008000d807015403120300c550701021218901d400301c040c00320150f074803005000d096054412082144201d00e580ba09848242071004c484080448455000c11a41a0760069004040201a055080c0d502c803c8541c0b40303500440040070801da017040004c4034200017400d4040e844149114240c0b8550003402900d0042c550b18820f100421340380d042200003600a0142c4000043c0c450401003035514107503081c4e890020014054030901c1d42ca0000c07841d0301c0040541702091050420003124174905880d0a0003000e14466000415542071031303204a800d560701d00306880d108200c5107140d41e1510481c0304000e40e0150070941d40c1c00c0700f5110031841100500b141c80300d054050000108001081825401c850040003095 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 340671232 1250 340669982 340669991
    0x30605011e030c05010f03020c0d020c030d03062601091209030b010506040617040c1203120c05040b0f03060d0b0a050402090718090911060c0d030b0d020f10121d01 72
    0x9114041e20040900000340710340d140040030700040d440340c128204041708500b0010b103001000c0f4411031400248143c4d0b000140d001007a42d050508090100941c4e1500a08050055034240b0035600d40807a13511700700300da02581100381c0c004804400d4200180c2c25400c5100c070b541c0b41c2c90482c4c005200c6a018082a6280300c021000090f007414681c0864007100d50550710b807086c0410480c0d04104240c0040c1040d110100e4441002c186030710b51041c1c41426034440c1d101c5805a440031314414081d43d0b0100c901130140402030004102205000d000c844010700d0150109540e591f500e80003890484403501c001d807125401404000390324055920190140c1e000f12211102c9645010003120320880011640e10007a001310742c20401980c0da6000741d90001d100701d410001551a00780495519001038030303031144680c003541303032072a2a9801d481031070002441074501d00003d6060f80c01140e241c400c1c04134500c2c029103d0905c4002034502c60007120070294048981480001860180140100050740361246603501c1d2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 340672482 1250 340671232 340671269
    0xe0f120f1b07062a030e0406051f0201051f0501110312040f03110703171c050f0f090321190603030306060f05070b060409020d05060a0501361a0a03060501 68
    0x86207801e0032078244003e81e00b030b00d0802d02e035001c480c0030103241b40058202e900c404010686680d44502510350f4068405080300d460401203000b429508081c0050f49116220814048092030718078004050324428280081c0900001880c10714604c145608a002070442c1d0090004011204041d020414000e990300944070010b0070340c2ca43c4804880c8001440700640e00b400d00b1080c02010042c061511b546415502009400f1000c0b4041d19400c4401d203902050802c2003200030409540c1240e00250120029401d021000e014007004003a89401c40c440900c201d0005811072030740700060000ca60412905110040d9a40b8010307020301400d00484c0e000c140c25101c181d82151103a400d4844460b000421010075803540010302c4001c01180710305a0700114108158070115801700a5107002e405142c80c000340030b602d06681200e445003501001c032000c9442d29204003c0405c041e6071041a58101080003c01a20b0060380031440f109020362507401070650f03200041401071a0b4407041c120340d0907000c5920041003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 340673732 1250 340672482 340672517
    0xf06140603340f080712151a03011509060507111210060f05010e2b080417060705090102030a08070e0301091103010b0d1203020f130314010e0f120f1b0706 68
    0x8481c1c0100061b0700b079041c82030a04d030b180c00c0203502500d90141104900d4035001c1c0d510714503c1518000010300400001081405039104402400b5107a51030f00311010350501000500c01c0c811682d0250503052100d00c5242c1550b91444c03c2c486810110040315484801c1d0301c91240908164844c0402e074412885000403954024181c61840d01c100600c0070840f07100c42c024146481c80c0c4541383d00c410400e84d08030600090040c038000c2c80905403100d501c4108182c0c0c80c550a03e094801400003017086400c0c4450580c0340d800200350f81056481d030400e080140e607a45400c03640340d122024910f03415807c01d4880000e2140d40c1140d41c1000e10705400a12a81d8520018851000c008080042c4150503c419445e00c4601c0b0f60b01a000500e03020401615052134118401172004190300192038018070504525030a80b801d210f60806000104080c080c0c01700818413690300c2c0d100582e21601b00c0300e030000e20f004a000174682101c40d180208100320b40604524403a040d1b0351140b81c003500b800f00e015031140c10301041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 340674982 1250 340673732 340673747
    0x30705030a0b041a0717010b2a1f020c060610020a03050a03020409090b01051c05060133170f0f011710050405100f06140603340f 57
    0x200003500900d500440e075a601c070b0454800510a64900f107007a0301124610350190126402126a03070b031a40c8521071103080101d070100b0107a0240c01d19034801c02c1090311003510350390b40d00090310340f1421084101c2d43c3d4a03581c90504d115910020181344c4020204000c2c9900c90b8060088010400c08a0311a41d0b14181480541c003865045040583e000e00c0700342c000a8403840051084144030303e00581400c2d5140728207070039211000030460b08142c049005114904103e4003003080d10701880070100707000040b5140c2c1511454107000e5810340007500d4208210000622000100d84411600d03403181107810043c0c0200000f84c90107a0440f8000b10f9408109400319600520340140a0300c0c500001c00e03447c014509000040708210004d09000d115424242904c603071059511817801080078102e801c01c002040c104035003a0700084900307149401402d218078028410001c8010405440c01981d903140c455000001104114150039046010303105030424110015490001440340d460b240c01c0088499800e4030b008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 340676232 1250 340674982 340674989
    0x23010e0f03030c070320060708060405060d0210030b0603010909051203042a08030d0b0f030f1507171030030804061e05150a030b1315050a05090c0307 66
    0x41c0d0003403012410810510008100103442403d240309214400d03400400b00851101c46200b1580090081203113494101000c182d000d441181c04116626154001075124200114080d001e004003040c41c1590a000b54440d054000700102496100d41c0e407407d07540040e242d407a00031111402608156070810303c0000550703019542c840303080307284069514040c0c000301850864210102441c4000080c007440305100901c09148034041c0030585018100500010b0f030480d05046010741e0008480707500700e00022802020b403e00905403251951144c200c00c40da400045d128107030043c10a042800317045170302c0c16040c8084030042264465a1690300584000d003105540e09d6441007650701642100184c864031000d90b0062044070300080c412500100c4001c200c10883d001000307966550300740202c20043c0002d1000c09401207485c40c081600b03565416030800c402821a854032000c01c0308250803c8241051007d07041c000b4a403c001d2480c2802000d005000300b5500c500e0035000301500042ea0f402d02281e001e055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 340677482 1250 340676232 340676263
    0x6020102070f060b01030b1302031005010816050c010b0a0b0414010302091305043009051005040501110c0603072a0818010905030d0f0f030506150c010923010e 70
    0x1070b0003083c3c072044040d2000c19045810559074483c1e030b05060340c0b00d0b05040480415880016120320388000b0280403000301d40c21103030500141800300b103005104040000100a55454190784400507020410b02410388040f009501c20059000458000c12410140044504c0781c01c036a540b141d00c0301c0c0107408030710442e4031064001c100c1ea0207007400700001e50886034000b4440c1020b14072004529080b80c052000c0940c0702c1d200301651040b0f1444061740603070104c000d0503089810280343c2e00a11000340581c82030740305050500191503902c1d01400b1050041c080d170020040d190030343e41e181c9590020704464080442134500e200d0103a00400c8038280f040c201004581c8060301c10b18040d802e480c4007200021500015042105156001c40c51761828406d4800441140c1c4071080c6904070601c01520b58007501003550105440c000410a89035a420400801501c003201807540c1d803c00e04150b140035100e5408042c0258081c0c1007204c1384541c0b401201a45a2490002048041000c0004940715a00c1e103560325403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 340678732 1250 340677482 340677503
    0xd030603120c030e09091f0b06070605090a0b01060915020102070302060105090a020c01021201030b09060405060408090105121003051605010c141504050115060305061c050708030408030903070602010207 89
    0x118500500c882c860382800703824603583c124603103000583c0d03150741224803020f15042003c1d400c1076a50b500d0703160000900841010b1007170301c800001107400c43c06002c1e809022a601c2c1c4010541401c000e211158000e500926070910a6840e884060410700f01c600c95110f01d00c00a102812100b4418420780300c00640c568050a41139190808010540350041c000b0040b0350340c01c11081e05004403d00c018800b0001c040310550301c0f90701d141024003c1860051a00c10741e42c00603010040051000724215a0196000740c03100d0301c8a040c2d400482e0140264821107001c1042841803026002180c250709084920031800c6800100d000b81d1424004c2c8920b00c40c6601084041c8409000078448410310700010450320122480d075980c246403103600c044207440581d036603503541100500e0300c114060501c020307001b1802d041c002d50900c3c1020840c60000c00e51a5010400c0d4500b481003004000e0000d00010400441160348960711070307401c42d03200d030300c203012007442486401400100d03680180207913a207a54000c0c11030744 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 340679982 1250 340678732 340678763
    0xf23040e0f06310e010b0a08071d0105030d0309050309210d18050d060b030a03090608060a0b1b070e010b0a080f0124030f1d1908090f011e020307050d030603 69
    0x9010307010800c0749245175500c1d50f010180070707140c1c205560024001b0314000c0140616020b40800d0511000b4141004001d418005014030340f000220030101480d00c0c0340004018519040c41c604600484d080740c0d902440e0800c2a100064060400452404000d402e68404003c0341c00103440d2071081002070030038684009001c04c00d501d408050448110f02417840400d42484520000741003100482040380415404041404401e5003c540c65911404c04c5e40d54002d26810030000820a00400040c0201c546114090480e4060148030000007004600d0a1010315610b07803801850a80003103444800040f40800007039401030190b0b9010b4101d64140e08500c0030101042d00c1451314003000b00343d0409140d1150a81540085c10740308480126885444140101340ca00861504103008003140148400d0002c0030400410040b800715040c0c0c5030100d80040989201c1001601c914855010840749043c1c0b11605940442d000300003000c80a200b030041d40c403500403c520a5048030018040584a02524400032 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 340681232 1250 340679982 340680079
    0x50a090506130f0b0a020a0f0c051005190903120b0f150703230702100201020c0c0910030209040b06040c0f0504030303111216030c0f23040e0f06 64
    0x11240c42e40200104420f1140540351112508015254600c1c800e50024140340c4050303014081d82d40c030f036003e483c0040b40709000f51034440c0d80e2244040351603804d03581c80000c11280350b10b540c2c01d44c1c50140300030418811b1002a0401404012844815010603810300466111032711b00340c41281000d040003486100c209030b200300c19501a4018a030f00f1000c1c040340722846001c85021142410720341140f14030480d80c8841c103205000e0709031040c1c0320041c2136a005001d42074035840040b0f13020b0300c040340580b26503410b0354800c1c903001c84d044441d41c0041d4000c0c023845d0034030040c401140d40007841103005403002d10a11010040c1101d9131115030740080300180d002d03c42800080d03c07a0300300c0b0b0f51072280c0b0200103090011000d4800c08010341a15480c1d900d409a6040d081e4140e0980100405109181410111030101c2c403c06464080c0641003041c040d00460b0070101e00711024021380d405084408441e020502d0003403201c0b41c003800c0554505214540c8a5204500690030801c1000807501e0360b90f40e04030401816412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 340682482 1250 340681232 340681261
    0xc0504110307080115200a021e0d080919031415010602030a030c0203090d060914150708151c02041b5412023003030c1e0901020a080d0f1e050a090506 66
    0x5a9401b081c140070401c007400c0c10341d00b440040c40c00303196143f0351010b0001c149803805010100900c080c01c4c61a004004054010040c1d503101c1c829828042110b03d541a812402d600c601d0940340d500c40c070300b1840b041c24004954490012103206154980d80b1100e000f400c41da1320060303140c000c40c04c9801080060700462003808901d41180390b034000c3c80070540d0030200184a504007022900c11a62180e170340002949000d014104d49140c0406440042c2c00480100030700201d4000f03042000e0420480116601c261901c5500c03d02080c01c9214810304440c00f4851700a0a8151700d071070800856012000c01e01e180b0381003101007141c1e401400200e0b81c2141006200e04c0002e82c03403004c0d8850280c0400740070483c2d4140015841082c448100f00d594035882650300d04900b5403911141c2d0b8000302880f0422803a40c0008907020101d8004220710b032210384c00164840608150941c1c01c6101d41800c10300c0034074081e40000c0304a09450b181c018000760759020801d004440c02180054160344c01f900102c0c0410541528 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 340683732 1250 340682482 340682497
    0xa12060e01020d021903050f1614180a1e090914070e0a0608061512070f1401110c010e06031504090c0504110307080115200a021e0d08 59
    0xc611185500041802ca80101d451804030580004000c0c100c1211141025140c03001070800300420b0800d01040d03030717207070310010050034200b0708403410001d103680280710300348112a000e5034081d45c6440154800c002c10902604841c0a07c900d400c0115151010054080441c61200079540507039103454210000341c015000f0949541c0310075024642e100c0e001384400800740075900795141103801c100411408440d0140e021803426081903007442482d841c421402400e08004aa09040700c209000740c030750a0055650002043d100b1600d40002e81e0800d60040100300c0174242c0320102c0e0000c3c01400035441d2212180300b21f00083c251807841c000340c608030020319085000d0f482010000032024004c2000c0b5840342c20151400a0110300801c030b0751415000707213440480090007103400d5041a040248c910704040c0980031034004a41e8507660000e20404075580040d08003802560b4086e03035480c4094803501589401e0f40038000320401100002c61141403009819005803810502010f070782c0300c04159810000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 340684982 1250 340683732 340683743
    0x3031605040b0c01060608090703020108180c030607020d0221270301090b180309030303070f020a0c0b0714011a0607080706050108060a0509010c0c1e08040609080f0a020a12 76
    0x1001050310003002e070180240d910340000002d0441c0c00e012010b44402001402414260300900040c00140d07070011189401c405d00280d050320f04030141200e141404111f030075064051103082d0810010300c2d40040e280d0000d00290b020b41d01c151b00861003841525842103135510040404000c090413890105040c0d80c20107041c402e203a5070421380000081d00b903813000c41c42510405026414490400c40d00c1c1d03c000c4440300f001e40223610308540703080825140d01009101d80c013804601c12145d98064024000001d00c554803640311012a5101c034212400c40d04244000d4820b0080c80c20101001c440500c101c150610b800404441046c10140c10001264482030048a58100901ca65000100c050141034003900146c0d000d041245400c0c0c0f614801c40314008c000040d9030b8100303003940d184030b078003d28507a42594000c10380d2406072602c10510501c0b25102500204018000600007840951080004094403008010307200f24440c1500d01c0c590300c81591001942c04080c45108005a0401c24100b003082031055 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 340686232 1250 340684982 340684987
    0x4030c14120a020d02010e1c08190c03020309100c050927040819031802121908030a060605070503031f1502060115030912030f020f221703031605 64
    0x20040603203940c0250b4520005644a00c0241003d240c080c040c00d205c2d910500b000f0100100359035091000028011021001d0080300004200c107041d002c4200d440654181c0703401d003e400c1d03005100034000e6008079000c44041c000e150400e068a1403a005403100054956903a81c01c145d001d1040010032862283e00c90f80c1d41c411940c7e060001024008200e2080e8001d151658440310214007031803a0003000700da104100341c5420b0042c04a11000307031100e0000c07501900c4a949008000107000c0c94210b51040048100e200240c9031000c100b088001540f04142000d418000c01e03a440c54151a1030003080c0008103203030070510001d803c60000b04c000d400510103150001e4089a922a210a40007881c0b0f00b035000140c020000521600140c59080c2140500b41d10b410058100503844401031124807044032420191070300340f06188810780c1e4058450b0816030300e00c030941d541d99440d0b80c3e00a0400e49420401641041a80000d070a04d0103006040384070580409985556280c045461407102661001d8081c44400d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 340687482 1250 340686232 340686253
    0xf0201020705240714030714040e130204060501050c030d090314040801060e100b07060c020c18060a06050a1e05162a0501270504050f0a0506010804030c14 68
    0x421842145a40c8a041c03c003401070000740031500b880340240300f0024040c507054006181042e8904503036104004d0310382204d24110005101107184265807000000c4403a235814040010b50540201e5800ca02c00c0710308000c0d1039551401951107000310401c80806070010300c0006441034694000c006030340d06c0fa203004420020481592080c035005608200d0803a03642d54802d000c5d20320303105800c541084402d0008040149818280c502d00d1152010090a05841c0d080880900d402000500346411006154085540803000f505186c100d003252071034841d0300c2d07030b000003e090341c0500d08880c0860051b5071025030324000d40360b400d003465054061340000c00508100c038130fa0141161802051312486074200a0b10f248240101060a05000c140b100150b403025808100c1a0b801c0841e8078818601a42c85828008141010301030366246948003640050408040200107c4079502d918419a841c0c1d1003001241c50700401144c09000864000300030940240600c40410100780e0700b594151000801c489d008603e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 340688732 1250 340687482 340687493
    0x170c1903020d02210f0d0e06070f150e10180b0c070c080a061a0a050109141219150204030c060305090102091002300a08040f06090c06090503030703080402010f02010207 74
    0x6141c556503141c10030712040043c5c22080c02024442c58945c40c040081046800c0000c103184174070000101700c002c29030449410001101281c49185506840400080118429264454107800f680c04203551074450510300b0b00b0000c142400700550441c031400c4441d507074141078031110750042200355007190f0480c00020b0000c90800442104910030200450040c3c00060740d1030850501004e5144103c2d840203050080e1303607002c81c81200f00c1d0178060001481c0005100071481d0760300d801d80d815109004521068041020004e00032201c03509c00d90480b181c140c1d841012008034010760000804055144000b085581d00c00d41042d40c00982d608001458021440700081c0300e010580a42e40c0546c21040242a56001d03040302c45080489000c807458540e0000d019100280c81108e0481084c0680b03000424188140c5807507100308103a00c0072040010709414203100182840702c0c42003e0015052035000b20325420b02006071001c603039040e05d80c00c80540395a4015a1400d40260b0054219942030111501069 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 340689982 1250 340688732 340688779
    0x2040603080c0d02120a0e1c030513050f0907050a21020309070e07050a0f0324030302010b010201021303060504030e03070603020c10020a020a06091b030c031110081501090e01170c1903020d02 84
    0xd01c66201c45644034240080e003214a0b200e40e0029200340100c01050237651544031045501c41070602d4452743e075507500762060780e140700070340021305815550f40c104200b0307010254015400b400c0c541c801c07240100c1d50303061000c010710030440380480001c40901c00c481a040c0900d4083c003440145050214003102d001280c1451f10b02c00710460190600303103000c10401c0c96020700c22100401000e10080d0b14000c1c5828001c44290014440107100540c0da60019040c188a001d48040c039000c01015a41031a5944074010081d41216610b1901405601c021758481c015078404c40d0001015500034005c024060b4662400a10884800b81e075076007407492000e0005a2407000600145204110032080c00c0d041d41040b0a9840840c903106010703400b01c549100010380c101441d0f662119110f0000304108200f072004031a039000c43d91110408600e1303080045500c015010025481600d0141200d84e0588690100181103c0741c0c0a05111594491824005414110b000c1d0400d00d0001e8010800340c0c1c00c0841c6c1e0b00006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 340691232 1250 340689982 340690039
    0x506220e01021c0c03110f0714150f0103030305070801180525020a0c09020f091002030708030103140c010201110f090a0b0301060e090a0e030f03040f02040603080c0d02120a0e 77
    0xb04d5039011a01200358051140c4084880b20203c02030400032888085541e6205158020740300428a80319000010410008404498410380b084400c5050269104070b0051080c00b0440100781000000b8528503c0307408418101c2c1c410310010811005001002001040013821800641c840000500c4520381105581400048164001d01c0301400034103220329030324182e130010903003a4010800d04400440e241c0c180d40c00d00311708561018035000d034002c0a900c3c1d4401e20790010646403010000009012030300c0e0701200c0c0c0c03400c144191802046090012400c944915003d007168030410301004c2c4458404501400e4402405400c08440d251560074440386034100343c4c400c1000600204100314103050080340c242c0c2161041c20140402001240402e440c1c0c01100c90038090b045001c40043e00303000e56445011403454020b04108011034903824140000c0c0e1040c3c941400900c20403c0c101d00c0b061000414145000b0350321f00e0301d03090201106048502d240150103407a4005400440d80540b01c640c1d1500349000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 340692482 1250 340691232 340691287
    0x1060201110a0807271503060f15020a1401021806090306071103070b09030a020d021207030804061d15070e010e09060406170a031b0b0609091002070b0a0506220e0102 73
    0x711450440d0340f00c002d4804c410003204041c203001c409c0000380054000482074494010104801c90350310300040f8644030003968050a445142030302c14461000640c024009400341420521b4110340b50014011944540b16145405500480000301407078894004030b1485100003041c2c13450312500c0d8848100d038503800d40700d28000d41c02c0000c6103250380350108000002c180c8140040c14200016101e0181f80340160100a010301c5201c10004081200991200c145071010b00542c0303441005c1c031072903240c1e1459800701c200383c042d04c2040820003403405a590792032154416501ea00708060240248000003501400300340d00035440780e10100380da0500c840c03074000d2040b104001380030055080c2001010b4150042c0720059561440c0c8911020a41c2110169440f620940d6410495168054014030344400d140c44403c1c80c0f0720128010042125400400e03018000c2010140115290042008804507040e40b91050104092100958003011500b21030380301d1084000050400b0010108044090000411600d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 340693732 1250 340692482 340692557
    0xb15070605041e110a0e010f1703042103030605120717033105090103120503152214070c14030409051501030515060a0507050321040b01060201110a0807 67
    0xe810445244001401d0a606c5085103514180118142d502d1900880312086901800105110f1042044800a1401721003654800746c180c044a00491031140e82240000c1c00e002c00002c8525140080140c8014031102812016150510000d8502d51200204140780414800d021a0074040814001e000701031000090300c4005054115081420070740141d4803c0382040011f00c01314100146400000000c4d0400e0f641d41d49410030000c540c0f000b02d81c500c560104200080d0084542c411810150b1f41400d44c2c0d00340f01c3c2070f0b040b0040c0c3c17500c4042110380b000062500c10454021450003241d00103141c50038401d40c0c5c5000c1d110300030b0905a41007141c440c0c602403100000340c205075a141c800c0c00d40c09408105032003811410000001c00b18491506030b242003103004580705090210500480d107a4080b100c40d0050b40d83c4440412000d110170449064503100960800014024010301980e0980000b400c280751514045d0724050380c8484c000f030704030802c1003001c10188601c1c1c42c0300c2a1003a50890059080f41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 340694982 1250 340693732 340693763
    0x501080f1005090a030c081308010f0c090e04080a050c0105250e010207050f0111101b0c1101080415020703121b02150a11040f05040b15070605041e 65
    0x510703000121001c0c81110346070500b00064000d01040940010780d152600d0848103101c1d051041c0c2d14015075910706006242c030302001a2042d0158000700c6080e0790300340b00340045c061054082c1d075081054860305c2020817034500000d0000d01c0140c010040c5401c3d6090040c2000100540c181c01c49408842070703c60b8402100c411900701100c01d4810b0309061452030724500b8980f1a0000075111401440340701d00400b50503648250580c01a41c0059130480c092080303d86040302070b805074002e060319028514040b45942410708015214500c10240683c0001d6211010884c1d24011107001c0c034000c00c04d40315000b005118803a420214002003503098001d96600c01007130048900e46080b610001c44540354803030301c43d443c40314964010607688409041300700300c108241d483d0a46000a400780344051240300f040090040f0b60609040c0031035080d034105880420180107800180032111805681d410040141480b0000014920390409135100e1320800e01c0d1110b0380000c1c001c0f00310181400d202162050014440c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 340696232 1250 340694982 340695013
    0x40308040909150207021822050c100906080f0a02070c030501051b03010501090902090a050a150206100b091003090501020412020411070305191b03030504062f0705070504050108 78
    0x214021801c000c0845c07501e40d1075800a04203100d408504424410100000b501c10310480b100307d10319506200b00036100c04202d140a50b20f500401d840644507202c80ca85845000d032103a646607040c1c4002e61500304190703c8402d00c0c1c4045000051103a6003264007048907400141006504030b004500c00c0b800802d5a00b401c1248a00c400650303c2c4000308440140010402c40c0c1c3d0021111040314125072005a0b81e048030002700c1e4088519412054000c3e0300c10500103181540071850400201040d0300b07440482c2c880984101580031144a14080d801041c4440314051402d0030342c1e00e9800402d0f050009100b442940d596080e80c00640c0700d80322100d1040b00c2c070301c198203240c01403020509254000c2898880e00d945d014102d8001c040c00303070568a08240c0032400b0203015401b1019615010501080032000d00e10700140a42800c603021542642031081c200c140c2d482c0c80351a00d00c280c0151600711683c032034010401c03080741c10280b01910300d0720a840000445803180e225842c00b80942e0700c0a40074036a01890013 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 340697482 1250 340696232 340696253
    0xc03041b030c1401110a0809040b0409020a060f02061302030c011110050a02030601020f030403020913020312040b0d0f0c0906030e031b030403060c021b0609060903150a150305120f040308040909 85
    0x14217040340c0009580304009613554080301d964280c00c80e80052400c0d407140100b0020552280020b4100c0401c40300400d142c3d401420046d00c004030340e4200c03881542c0356400c0420714007072650000c1d05540102c044264540c010840342040e000100300702c414058290040405031282681e404041d40e5000081c0706165a050052741c21654000c40203500d01b40c036550202d80440741c02070054048540c0510f00c403045640c1400410f5500701c407100c8403921986c036200d4600381540504890190289070007000e1a220045000320803072405240c880c042c03020f18110083e406080315034000000c5001c10851a1841d601701c4c6854000c0142800c021621141145481001c9aa80043c510700b91b50024500c4ea100380c1c50b00b980246029401d0320340381d07101c660b00404102e00b4042d00f900c0f580d040c01203007902000310151401d8a440b903820008188000c030250002d000c01c4030404e004c0500140c00065841c05100e00360402000301100aa066915140c1e882d01c480d0481e4100c0c0c1c10000690303841d84180010300182d44a0f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 340698732 1250 340697482 340697507
    0x60f050604030b06090c0903030f1c0e150603070f03150f060f03080903030d0203190c05090d02040b120f0d020c042a141c140c03041b030c1401 63
    0x1040352606065482d01c030315410300104641e106404000001704825510015a2040b0102604694540303495145405807a00107402480d803102d4416055500800d080c0202410b00203004080c000782d00584a190041007c0144003a405100b48100060740310948a4000700441c01800300032502c592541c44002a44c0b440240c001c1c0c498140034060040104055405040f203911800c8142c0d240b11043c0801c0c2140900043c65624910210401c42c07100005444103e440c0405813040051820011082e9054015004d5054000d0400001280141843d0340310f4010810010040000c008030318106514000e02c0e01118500780e0002c0501105a98040000b542d00181c00c450a100070140610000350196401c3c950f07070350600384100078503201c034028004101c0c00c100080d601981c1c2c800303000301018407a40102000707501c146002e800903024510342d0034450081520503051455601d0300c0e1078800300c0c0d1548003500300c441c403d406400000522500d8610000703002c00401c0f0903084441c80c0001d00105201403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 340699982 1250 340698732 340698739
    0x1002030a020c030c10050724020307020f0a080d02090d0c0303030e1902010203070b0a0f0903030209180f0a0e0708061006201507020109050f010e0d1103030c090d02040906060f05 78
    0x11100e48899450810161908410380361464a5442c10300b058107440c41e082300c1c82040c80480480809507060203400841c41403c01e5022102c45070340d100e448550b50018040c02611075481070052a0718404950014910a40020200503080c11b441d2035031043d540c0720383d01c100c020a541d200f0880c2044410b10a041408450b0f406103c581c03000e80e00042c2d02ca10500300002c00c0a01c1460000300000e149034050542103003260800c128185162502500940c01030fa2800d01c582407010050342c481c101d1812843c41240e0f02503012840d034640c0307104000a0700000f003198070140920340d4003003200f000410001d0301c01e6801c2ca05141e541e9140c03400203040c82064190130300d441b040f2003511f1940070380e00086100c51013001c40858a040c3e5203005d41240180f4682100906901035440121740800c0150044040307080300000380c07610020030314816030382182c1020f51410640c20500010308050045400b40400d8080981a00b40011044d8002070484078400021a070b8140d41d082c0c107200003441580c0310070180200b907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 340701232 1250 340699982 340699993
    0x9040b0603070c030c08210109050a020f0711150f04030c0504020c0a1103120a0207090606180b07020d0606091509051306051302040905070608090a080a030c0c021002030a020c03 78
    0xd03500205a040201409405e20000d101c40f03c080001c090101d03001000800c80800c0044124060134400c0c0c602071181032101410200851200701e10b500c03c944107410880300181c6440090b9481d20b0130403104c0c4032a180e001c482e01d0341c40c1c0c00503c0b80900420540303600c2040150341e9800d62401c695200c04607000340303000c0c6105102c1000035500c0054490012a0014a10440c1040d8040000e05d0800300d0715100c039202070046000103000744c00003050401e0b506000400e210789038072070104039003400360301c032402c0120705070210104030b080390650080503080d0000e0200d80c0311001a440721003c1d2603103680304188141da42d1402440e09642c1c10704200c0542108807050006041460007400d0140c0200070142c6440da172740000c00c120050b690042c40400b0b502a00038401518a07081080d00e40c441c0d0310888000c50b02d05000a00c0044010403500011036018040600f02601002c00302c00030401c104814040c085115a40405a56180c4882d4040c461560007140d442c110000c0090034800d44205050095006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 340702482 1250 340701232 340701241
    0x601050708030a0b0307080c010318020a060c030210020f0a0e03070e0c09030705030a12090e01260c03120a02070f08070306200a0f08060105120a02090a0b0408010209040b0603 77
    0x404464000d074001d80d881c1e49a40b91143d01000a0100c005807a515105249000801d25404600c0c100943c5098070200140100d028000880144440c4025440580603006008030760049007540b442500a104850a02048200da203081340d00000c80b400007000c01090308100c413680301c06030154460041c1c01030003506140007010f18800002500b03c0c4400c48010598103101d807000c0050b40002d0034001c00701ea520b080030341044145280724070b0b0b210300040d0503504080f0303c442100d42c9140c101d4400a0b4071804081460120080c071040d080209140c078010510345100c0d9690030401e2181001130024042da88500d0380401a2400e03e007580140002d4100c400d0401613040c000c41e80404413500091b02042c000c1070040f000c40382541d501c1038407080c50408510a00c140354800030121040e03055860b01c00950329804019501c9024003540b000a001e020310000b100446140c004c2d0040110180c007040e14152215655a2036030041d40059840d40c2d8040f400703410601c1c3c0744c001c18118072016910546113081 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 340703732 1250 340702482 340702487
    0x10e0a0201030209060d0504150c0c080d0f0902132703090b0a051b0102090307050d200114040e0f0109140703050606040909030201021c18020936070e0601 68
    0x205440003a041c59804100240c031900c0d0710003103850002030764004000d549058071b0104801d403c1d2400360840c05e842d1240002c6480e010b000c807510a5a0403030306440c01c03c12075900d00000b4048040541555540321090040142c8581034100c20000b410840403801000c0700c40002d0040c0348051034030303940c012500c25900100b6082003180042d5014000150303940c891080d000c0c1d8aa1046e48120150706400b4820242042c6040d8090100d00313000b14159202c0680d40ea04215405800700c00280540c0e10404203c0c0000d081c0b0b0f030343c4505920042c1444d410840c3c201401c080300303806c00e0340071070702801c0d511081050300f01c01d409200d400b406900000300b103044103d0510000f8094000c1640d02410707503980201d4019a100c1c01500d00402da00f01081c810303188203150084c041e411064560601110010807034040076000d002e50480c4807004480740d40c03201c55a408003da1110003804107264100e4038081c071258003c0360b075003105140b500c0340c0b091001c0140031998945040061340c0711107480c0c4030171401d10015a0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 340704982 1250 340703732 340703743
    0xa020d0509300909010303090611010519020c15070314160206190603050102210a0501080d0c03050d020309070305120c07090b0103020d0f05061c0209011203110a1a09010e 75
    0xc0c1c00703007900c0301d08540ca031009243c86200381d03083c0d0000051000100b007540c08180e00080c0c3d101562030030300c0085403001c0d441c00d0f03610940d60021480e551070704412564450740c0c0684004070b050412200401c070034002c3c807003c4a005484010000340c031a1114041200c00d21441c42c1c020200c40c041c1819100308210087d15200081c1c40511900f98a0703045c0c00d0101400c0d00050b0103160058001c641c0e0b070103658400c0100d0000c41d1030058080121500040803050103103c2c5d241212503c0c0090f080707050035950201c80240c0d0b0040c044040c08402e103c000102c0410b03101451242000710010000b903410340c02c085140c090b004084000e8041d0800110961a0001ca2034000300c923030090012407e1010000142c001c0d0040702e0782d0302c06c40d901e0000d1072040844c0396000180640804e4900046140e0074140c03180c601281882e010303411541d41401000301544002c08030300454044d107840d5444c0e1b00e0303043e41c460070030f042d01b203050f1280701c088030741041201d181901d469003110a0704000c002c3c14400303101f000d4645 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 340706232 1250 340704982 340705033
    0x11030906071b0c06020102190f0210020a14030c0405120609070603091401020315040b01030608030f090a030c030b06040c0e03060622021b0106050102061e09150a020d0509 75
    0x1046041c0c0700d039801d0702c0b0101c003200744a502c202e400c000c040d11010001d00075000521407804034040130b07091540d69405001b0780107203860a9805840c11596150b000c00103988100329071010030144060300c504121060380618007403a001d0b400079503624507050030003042a0307111800c5242900b143c03092110300900000d00c041196840c1c113002c0b42c0c800180c1010b400b40c4034201800011075000000b048481c0031100a01d01214608a6040040606180044080750001d000d02d4585a000700000030b41003260002420070000000d12000d0019241e030742c0c0c44503024203917204030307401009001400360301d142c10f00903140800441d240000301d54018500003540e0b000054402c034010240302d05950700303420519480040808000e05c0943da140102c10f0141f1a103607050300344820b15460110f0101e0190310124681e40119190440c44080d5002000a03140d000000351844280380314100c221058002811411482028800700041e11801c100b4070300c10688500912203052900401100d0350b02d2905041403e162 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 340707482 1250 340706232 340706237
    0x15010b070f020d0f0302010903111903080c0717040e0a110d0e0a0606081513030206060105030a0f1a010816020d0f0201060e0129030105010e040c0c120801091103090607 74
    0x460a001007070014154020141030001444d81800901d9015000030215511a42e6545c41e900c4002520b103480d5890002441119104441e495001c240300b00000340d08141100c83d4a460060305984040400140d180804e030364501c0400c04000c2c0c400444070440d4050b2a40e84107100a1341984204c0005214801c070080b17985a4032141c100c0c81d1142008100340c000c0c0d03c514104043d545840d09940d4640d0488010442c0b0310726840040e5202c2c200045d03e402c0c03198550010329494903600019240c41d0070050600280b155078200794481500940201c0c9076240b2113085c0900300030017030400104015401098501140c265541c45040c4613070014115110440c40d1034041803950085000b24054a016400700c1070303000088002040850005515a00c0e000b44031038505550560980107222034042441414042400c49407035603982c0c282034100565260b00d92504050b11005daa4070700c0048000b07100034000069040c4014040d8038000c2c800d500d0b508400304910713401c5140c0144910341c3c441c0c0c0200850708 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 340708732 1250 340707482 340707503
    0x10806010311271005030712020303070201030b280e010914010311150c0c030f0a03090506131809030201060602010603081c061208030f07080106020c120c04020a0e0315010b07 77
    0x8040d90081e003280700107000d48800521030070311008440132201a03001c0c15102e8041d02c20f00068801e00034044126807507001d0081d5040c10070540040d801481031a070040d400c03614036107180e01182c42e005603c002019081c00b003e0f0a03070f0b0074805014202081600103c2d1460303d0402e85c03282140902036410b04480d0b00030420068041c00001158800e00040402c040802010030b212117990800314480c2041c440940842c0c503491455803805603030b03805450000e408513400e44028000e50800100800b84903245c0806100c1c1c4540c1c4d00400c1e00c40b4a42100001c1019a40c0d000c13000401d603081c081c040c0104042d100a00c00d560039516aa1103611681088414264224407140c040101e540c00c440700134080c13014416404400341c1001821396008a030000c039003c10303850000740514042c0030103e060b900c499004110340982d030414040c400440441d42c035624443c10111411560b01c82c002011900c416030b840b00d50048902040c14a004000c00d28188003110a400500050b00b8000549030342c1ca070407001000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 340709982 1250 340708732 340708759
    0x105031602010e0d1e0305100b0306030a021e09010905011a090d06020c07090605040c0e0d052b11030406020a020d110a0e151206070c0302070f120506010806010311 72
    0x2801040305121508843c060fa855210881345c102400d031101d40604c2c0718402c150025a1411000c4031011035203c8040e0480100a01c41d810402d0301566002d400038003241c01c61262900014070fa8402c001c90b03841080380b0000c0000040c241f110409006203004402440f2950500c0302825039050240182c001c1d600d000319010103195a050b1000000c160012001c5568081c0c8028060b1107402c0e50180355074150620a001415007403d100c1c1d20640d18060744c0742400c0d40044001c1181034841540107555610030402003043e0104000020050200010212240a100140054410850400b142c070700340c0c000f40010410240c0105414800b298100c07504607118002d8a4204405e800240d819504410001c80115403880c000022a001d400750300c0d0302d103070400710100400104114a000c28030702c580001c004101d100303001c1c0703860084040c81380c01a030b00301c01d803a100c0c4044018815880160000d84240004090003400c5c800c050260042d031001d441070350f04540719541c0720040301e500940154980100d65 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 340711232 1250 340709982 340709987
    0x1215040e1615051204030f111504020105070602130b0a1b11090c1e03070e032d03070f11040e16030b0705040e040f03110c0f060a14030703020d050601090501050316 72
    0x210303200c0c0300e00030f0109850700702400c0c0105071404003240900400c8d454445103600300400544d010302c00c81600d140d0b0065969503801120140c1003001c4c01c4031031940a001d40d40741040f6051075038018152091401ea200c0344c1070343c0010104000da82240400c804021810404100c1c002d200868161083d10b045602d60ad03282510255071003040117031002d00c15625034105011400d880114000e10b8250307101c4030a190900c0800da22240103450400c1480369070301c455812604904c0d91900d09880b00001d40342803a80e80d450b00d02c40e03001400c00880314402000c501610601d4541700c2c9000701100c80d002000c00994402e09a0440c03403090002624a613918400039440f5403082c000c480241c40c800320708096904151602c0c41d10b40f04082c1e411004682d54520080d000c400005881030303004401040d098038940c03100e0034001c81e984000300041c200000c009113100c42c1e07407140c2e0096029074405e50b40181d075003152640307420480d00042c204130b0400c000004200401d03a40030083d0381d001100140e900c2c0c038412440c5004d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 340712482 1250 340711232 340711237
    0xb010e060c060106180e0a0b040605062d040e070503060f041107060c1b1106040e0f0f07030504380112050105090703020d0b0702031215040e161505 65
    0x45602000c001000c44800c400070942d40e04035441d07a1a0104640342480301d41603820164051a2000030070b84000480700e00040e00500c04940001c0c10005030316032143c0104907180d2005a00d48145010b02112009081520000600c0059403070b40c6642000c2c10060794071600c45004d0002401c00c0000310124000350b072040154003d8480040003002100d22050f00d05a060700458001d17a915481c006409c034445029440c041e81070300c0000c0c40303000740000030707595600c0c01003c48007040d421250510020401c035010f42a5140108105503510000c0d1805d030402c1101d001009200034100b505160a002c005006614803107041d07001569014140b101d20b10022007407070172000074420381841c14000060808819811060480d011324024802e96031010b0081e82e9030043c601c4000d40068000080074041101041e40ba600059107106403450101e6146207507207295400ea5020300c0860340072000506503d89441100c0082205002800350900042c100d141c01c40700510070028004065001180da00d4460400c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 340713732 1250 340712482 340712507
    0x2071a12100518060306070e100c060e3901090506030a0e010c050c0d030515040903120c031505030d171b0c030703090503070b1c0b030a0b0708280b01 66
    0x1001c08018031050610a004015940580a80949004508298170408105003404000f420021890240e0271045031103031001c030f505450300d80c0d0b102200c24001c88144807e410204900700d21400010340b10f100700c00b18030300305000c048098242c50780059840c2d0b00642600101d034000c842c81500e90395040a01d601411148441500325443c02c4804164242c00501421406032003008407003a07540c038244141d01301c0f8030a07142e04da18507103d005c401c1224a095003010081c42c0c403900d03200030b40c14410040d103c151138007040940042521020510780c6840707001c50701c40041c10102c000703005954045d880a03140490465031301c64044000300015000560302c0014410080086200e05d684410000c1c0799a1071b9080940304800141c200354000480e850b00240c05002e41c3d0020240e036140650349106480e00c80c403005908070049444902101c400c0c7e406008513000c00d4014090303401d441c6800034004010344c0008000c002500c101041861110006050b21501c200b03408500044400061005170340c50440a036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 340714982 1250 340713732 340713739
    0x40f0618150f030b10120209010302120c0703030f11160303060b0a1110020f0a0e19080d0e06030106050a050304020a03081c0606020a02060a2706050a02071a121005 72
    0x54034205035129202c819400c80540c1c04001c0c02000108100c446241001d92000250564107051910312284d40205420301c414100146826813400c008150420b040710520400a80807550f14140340d0580204220104003260801241c2924034400f03c49014000420407000e0024000a04240c001c0d0721409c0130f0442c1c80701c110703110909004004c041c01204c54406002d8003a800030109540681e0080e91890b0b14820700090805400c050f08481c5c2400b5060b0701a444031000e0300c20500d20000c00c2105010705224405860300b141403900240c030380b81003100f429009100800041000503413200640d0b196041500e00580d40f07807150f000080b5051150340003d400030200080704400820030ba0b000c1070303070b0242c100002d11072159100700a988521913808069088001003001c013090764458824021041d8035805002200e54007450050b1540c00e00c0c2d006180030540000f40320210300d4041020030020720300604402060040440701601342e02500c810888645524800304444107650700f4164054003014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 340716232 1250 340714982 340715009
    0x1030603060216020a05040b010813081c0504030f1403060409080c100b03071406090609030a050609031803030903030414031f0c08060405060a0513090209040f17040f0618 75
    0x919400202c01850f5004030302c158034101c0001038504080c040d40c003507480c0503100c0011550b1501e0004840c1d1000c1001120450420006800b4005070101c0e40005010030740c074001030b246024500940070000c0314100d441840001101c030542490303000103ea51200e000d0f1345c049900f141600e4440700f00d00480c0e010b03503044e00030301407d0384001807203601202000d2812000c40340a99a80c3c4080c0c0c1c181180c040c68943c1004e410040c5c03001da81442e000600c40101d010b011a03405150644603039090200641d030a20a030f400018400c0c00e50081603480740f554201c00c0740a50b00d401001070019540344103901c500050b00070000841c0c9420740e000d10100041d10507280400d111401c803400c144008048500f15480458100e0000c10002e0a0602c0703202d1080324050b080000c0c050800007005141c114a440010000c2d403501c179110016150554418020361140800c20309015803403034050700c4200d43c4140000026070a00c030400070800304096150450300d150800d0241c071084014008092041b6400090411680 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 340717482 1250 340716232 340716247
    0x51209060603071505030a02070f051e160e0406050406060b0703050301060305160c0f022704290114150c030903010b010e030c0103020f0405150304170403120e010306030602 76
    0x4100c032441010704605480c442616160458110180b484480001400600c002441c0300801c4e40244541c0f80900c409080450503a5a25890940d65140030003034048400130308407810384100044003803820041180d040d254140000c0003c000e0006002030249510740b4082424000c5d07552041c1c010701110003845640e9a201c2c14040c0003684280304040010389014005805044400d0700c08070740c03440507a0743c00c019010700e45809031001801c01c800e0341d001050029171880710f041c0701c1c4900101c0e60345000c0e5620743c1c46c00e810070f1650306901404d40c405114134526501d001e5608843c420381075a2440442c1d0821081d01c0c4007081d142c0010b800d004880d6a00011319856021001024040302101180240041c646440044810340c00c43c2140075015800801a0f0b61290300a0700600310322000050342070f081c04e580354002420407803c02c0b5034284107200003061105012890700312001503c20103562074940f80c51903960a4110483c401400c08012043c040000140c0c481c1e04414003d503004202035454100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 340718732 1250 340717482 340717501
    0xf070204050112030806100507020d1b060306050f0303070f080d020d0f0605121c110a061103040c0605040803030a0c17010602010c0210150b071e0c0906170604030f0512 74
    0x45503c2079001c280100002605440c14640401d20b181465031107500300f040329400d000e810000c0020490b02110080049407003800c1d05034545001b016583d6010503007038175120070f11039521301c4601000d0182d00108184400711300990040708a003540888880d030741d2640000d008009002e21000c0e001d4030f8bc1403081b01462108213410580a50f83d040b929608487c0924010980d0307140314081d8280385424000344d44284078000c00c0c070300402240d2002518034418441d900e0804560314259031140544000c000e0105100c42060144040d0203c0d003409868582854407190781ca0000800f0179802c01d403100340340113a461007050340c4100e1004911003c4a15619100044d01078031090f104440103104141d420f02e03040755540241c041c160019803e0a640c14101200d510719a0302600c400e950300d41d42c00300c0300070006020310b07174405c04c4a000d11626580caa08000014090386d05c1da40c00312003500101c01004100b500080381c250380090b491300b086180d84030a100161854050400c12814140907482002010311 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340719982 1250 340718732 340718759
    0x6070e09060102010218010806040908040305030a0807020307050a0615030b1905060102160e040201020c0904030201021c14060108072718021314040213180b030606060a050f0702040501 81
    0x20003121440481da54580c0120300302d00861410011344001c01d02d85140d15406800d1098001c480540003241409480d1146a6154402d07030040f910384d0302c0001c004c030700c443d404000340c1d402075042c0c1701451905280d515000e039584005a80504465a0340002034600c00190b06440b00071584007584410a15054600700380c200e880e4113001c9041d41c01d240004d00d01e98400316541c08002c41c9a01400c99450904599a200c070030010400c034198801c5200490041c2d8031107224600c164840c1e030015035510404020004640c1c45084c240c82d589003007581e2241d035852015640f55000350203281006440c1c3c0d5020303040f0b5100242c3c90345541225142c10314008200c800030b000006592406041c485808803d490441c01c138402c01804010f85c020090303040c050f071000c0705400002a00d000b0409424030b068000c0501030211964013020b17803d0a110004221308445000b051140714080300a070003a845c10801140481c0b150b51035040030020001900705000044009884025401038000c02066851f100f46070442c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340721232 1250 340719982 340720007
    0x20f0d0c0203091e1302130803030f0103050c0108010b0703030203090c0a060302040e060a030b0c0f0c030a0f08181903140c0c120d1e03090501091203110f09210607 72
    0x44c070007029040e00c1000311040160781c0b03800c0501030314a00c0e800c0c004900000c3d00301661010810042040014032000300b00040e5024041560304034216514519001d46003a125400340c6050240b039200400040940c9410348040703030f4241c200583e6981c0d40101031828500716034651903210b507525a000c15090760581c05413056a4206481c0c0405490b041f0070484400202e02c0000d1100c1c0b0803800142d2200080307400349c002c03800d040032a5824002140e1100b810740c0c200c1c40100e40040c50380e2501c078100e0b503444000035800c11070001c5d07041c615910514516881d032000340c1503507141e0b0321180c181c5401c0501c98110040c1c850304480075142c5070400789180c242c0700c4954509007031183c1c011809404d401040803580d00d151440944440d000c03c0c040409490007114078095120a140c0d40c1e03e90000031801c06c2c0580c0b942640b040851580c16005600c010b0200d400e40d8166071817400051050700d0070244403100f220911032044481c880307000440c08503049200900b114003c1c03180a480280149650000c0702030210 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340722482 1250 340721232 340721239
    0xf0b0906012d03060b030a0c090504030f08131709060d05010f061d150d0c081801060608181f0606090b03090a2301140405060907030f06020f0d0c020309 67
    0x1d00901c040480c08229900c0b100d2104207241d5001080083c2d559800403103450405815252804980d40b90900003007040c4c1e224000c0c0380d44a9040100301980070440e034038140c1003401e04162134188550516460310a000c0c005229960112001300359410725016100c00714001401d282d5500220460600940f07803e100700e10740007295402c0070034144e00031482e900a5081100000c482c1402210822030046550032901078003074010801d40704120082c2c0203940084105484407a0203043ca210381050003a10b4204060150b45040c00500c8034a50050501c2d400440990740c45c0b100c8500c80d4415414013030201059807c00100040e200b94911031500000c3c00c40754162180d0f00150380e2880c5030002c42c0301c11103c4d40c8294000b406248002038441060300507150441600a6405140051035400c6072003140c46c08403102c0140b820041000401c001c01540002c2000160400e40e2441e03696030075514480741c0003004260089104008a0900d00503076038409040c030b4091040b003e0780301001c3d490340e201001d403500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340723732 1250 340722482 340722509
    0x6051201061409040b0c032a120609010803070623041a010501050a0909020d06050a060c0c09020c030703083105210d090303110406110f150705070f0b090601 69
    0x40a2418910320f9119503009440100302e0f650b030f51001c01140e07200401075100d40403698224443c00000180015410a403298426560b00f0000144148400b00030a61440760240d1300041c402c5203800720a466000b94480c4021035550301c048514603511702022540700101d4151000c01003801703081c1912050107a540002c1403000d903201d100440b0300d885842e030f541c0003007016044204010400d0341c1c024546032410040000e0304039103510009404052540c4000c2c0001ea200d402c01d0144910084290004c240d0703504210320b0302552000300da48034010408094107022031400003c50040d0f0100400c00d06c070500c981281d0001406c140c203c0e448030040181510795104084500d40c960040c0d1a0400781d1400206042c0d08101c4200303400c1026241c110011000c01d80c0701d812055528030200045d0024045603140c040c0c4000c41e04002a02d80a440716040c00e00341d111201001015440e0105079401126902e040756859895080c000341c28018074600614030341a00f410485007180200d8160305841036654400d5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340724982 1250 340723732 340723769
    0x1c0204031e0206041202030307020901060806010e03030408060115051b010603110f0a030b07030e1204090c08010e0c0904060e190612030e09090f0a0609020103060902070b190605120106 81
    0x100c1d0003a0100003e4001000f00001e0007240c000d01d641d107490a100600301c038030b0880319a0100d002140282d00c2000411000e2040c0601c035a0880719030780790110103400840c10700b450800c405075106810b105004c18030014180404080f8440e0084135145009030740c06c04d85130340150310790500922041c1700603144203441f403c00c1000e03840d1a07290f0340040305006200000c0c403401d58507100544180a081c0c002030594415012084090500060f550040e005440ea03840e180740c5699001511080c01c4044100608200140448054481a2030f00100d80181c0079442e103540401040c02407545c4d800408032082ca204c01c212503441009503102c515801d000040c00859600d44460002d880c9280000700030807100c525600c01410072500c019400035600c03045507055115016034505045410704151140c503100d070005ca056581601540d00144240b0004614048407501c4e501007510020b014811824101820141642d07280d030402005410010924064448542d8040d402002e1a200e240c00c501025015903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340726232 1250 340724982 340725023
    0x3160203010c1418041b020a0c0602030f120901110f030709050906010905040e071a0403060c1701090207051618140f0c070302010e030409050108190c0506070302031c020403 76
    0x2240c050070840c03045801d099421801d42000000343c00d103c0e0f04146d030f500103a40d00d00e0303194041542e01e40b00d68026150384075460030b080401d01d007540c21075002c0d54004c1000901c90540030003200c0341405540241c00e100c1c3c42d40300c0e80601420319140032995414000c542d95500007075000045001c0d2203507031900812190f850050007080c0904458160205032001c4041246e820540c100c10284104441030301d00142d250301c0c0c9c00d080b4a1070051540c414000200e414001c01001c1d1150809170140c504100b60300d00f220747c02618a61405005050003250040340b03c0d810000304010b0040e0b00d401800c907842e441511000c6403c00c503484114146d403482d00300005c46031300c000e84047c0c01c1d0149441d003402e13403450b648110344502d455102c00412000c43d941c4803c0380707103002d10500180c0b018140e00c50001c256540341035003040c07030030300030b182a998401c0800401000040703819580c04100c5109a880a4a030115810142c3c15800740d0ba0440c0f058910301d81905c02410200d5000b40162485a1101c4a01d41d0208820 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340727482 1250 340726232 340726247
    0x204181514041e02030103050309130614270c031f05030d030506030f060118050a0b0d060e100e010221070e0d08071401050f3706050303160203010c 65
    0x110810725074507004501007410550840450711112500f1160070742c2c02807801d0012680300340d0003554075400114011809240401090f01030368130141044c4007103407d055101d1031101c240400c10348980c0d00320039019881c84c02100b14a09880000c1c000103d58a0003c2e800002680101d6100c04084580e016040c2c15010a00850042d108043c005101400100c081940203000140c0466403600c2049403980c00706000700000c5029201000380050b00080c180c02040540f440505929485400e00101c4015a110b07407a0405040e40c0040d80404c4000800d2f2070181400034450702d2614150808005c007000007415001010881c500303081c148120012507208a507404021342d4848005908a1102641d5151000340154210b0203424180d1400e000c50340c03080f0102098403158901c41c0d440b501082560703481800d0303981d800302050540f40100103144440100b21729512030784031031142292403000107081d441d500040c050075001d0100d0b691042032420944c2d000190503001c0b4865820408203080e4548034881 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340728732 1250 340727482 340727489
    0x120117070e0c0f1603031e020a0e0d060b100801050a090b01020a080a0314040b060f040c0212070f0f0f05011503020604140d060515011103070503070f1502041815 71
    0x5840c2035403505007605600790f11118105034061001c0c009050181e01408403501c05038801d0728001101050000c0c010184008201e054030054414050160029000060342c00c003400c040f1441d034050711462800c9c0d0014201403110a40022a0b9880305c0034003604890b0f40346c1070320340840b400040c80c0d65a58600c8161844810242e0040e04412070000c0000c0d40200a0403c42e811402d0109007100741d00240d5800e160100d40c00d490400c0300c00c06004180c140001000c02886007a9014422000d150300d0203580c6440c07800391344807000360005000003840440d0b034080001c00d9002c0c48180c0c0250b1103007020440a01c1054040e03a26511b03101038020703c44403c85004040341d90180015040a01d01700d4104010030030001c00a03000304580007000b0000e4142e02c00c0764800d2440b103560500030664400014030041c1401c849a055900411000317004c250000305844c07426a004942e85120a00c0b0b00d0032101e40044800c0240c3c01c1400800c000c649106e1240c8000030842c004107041016601000094001240030710 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340729982 1250 340728732 340728749
    0x170301050d0f03051215040b0102011413050703020d0f03080109090b0403030f020c010c0518010c080403080309120c01050a0c020d090b0306010c02060d05060102391512011707 77
    0x7044400100700019084085000381040d60401c00381010f040c4424030202c68080503000e04101458151901e0f20440c02d50400c280b0007004038a001c030307419400350400030b842c04480b0140424140c08000302004200c3c040d40d0b019000e40c0d09020603103403002030301400c4101140890000000851140c4191041c02e01180c0c02012041040d11152020341c010040c080c4150f4410b0f408010000c0d103c1424002c00c0d21000160b6212640c1b000d9140803003106902c18038219042260208100000c07a9030541602c00741c9030058482d130fa50b0780f1056802f0f46400c0e0f000d2a000b48001021a0442d03088806512a5124070f032100d10034040510001d10883e1609950010b24010450200d03007400407030409030145500c003006041040c4c0010041c0c00207002a0407282c0680d034a00e0300d8608201d9156414003036400007400c94030242001c0000440784c11012403005031703613020b041c0f42c1180c0c84019556102c2404050440300300550365500041c08810b155010901030720990000310b4030310007803043d80082c0c023070202c0e480d0380c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340731232 1250 340729982 340729999
    0x18041d07050108151e0901080f120904140a06050a0608160305150a0e0a1b1d0303040306020c01140c031005220e060108010e031204020f151617030105 66
    0x4019654004064070b04c2c1000d2400743c268000a4a03080d0140c1c0c0d5206190b403408010b410010704100c80f000c8143c01040c031641100360002c4c90300900003080386c10b004070b18000340e4480305c0801c00302c0c0003003080c1051024a04054414045a2282ca51021040e20410f070b407415256505c502c0182d07500e05045c2c0d40c0030085519034080c4400d8522942c4071681259005035408030101400d00040e00c00e000c0d42d0842080e822003c41440140c0c0b109104110480c00ca80040003080740e5040809410b00d41c09808050804070180800070140d541481105c01440e80501c0454840d0048005280202140b61165100d41c1a800111350301410300300c20380303102c1c610186810780030300d041006003c44401e9402c3d241c2c0300c0c2e076480c3c121101170342c80f1230260200406011008100d81c2d03142c4851242500c0e00000d203401d40b0703001044100045401103003a10740c01601660948158407940c008642c0003003a0221403111039402117207076009112000c507542c143da03020347c1c044213440c040000e803080613210a104040d4400f40b41c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340732482 1250 340731232 340731239
    0x1504031205060d081c0f05090c010503090c031605040c021203150604180b0114040b04060302090111100605100e0a030618050304080a1a040c0501110a02030318041d07 73
    0x10781c01440d445038003d4a0394000302e18540e02c4920039040745e007804200654800300442101d40c507114040100d05490414401803c2c09081c890b1074102505146040160010000304064400c1140519071080a0708446900103404c140c4a01c00e40940501803040b42082c80c0c107240d5602c006006074141c0c2d040e49030189035444051509001d44003038009140c00034410310001500415401a001d1004004403002c01d120b54840001400d0b101e000140c4034591405010900950801c4000c0d103062f242d1034100165160142d00040c0c8607556184076501c1c1ca44610081c2800c102d0880d0001030460702c0580340504514140d0344d0907180440c1e0090700c90380000440c001000460300c190008000035440c4510300c0325105644d203909045511a070044440381c1c2c481003000701008104401200007022a4030310030094107169840301110205446000c0c1082010b03101030084000034024000743c1540101200c1d51120b545804181c0c183c000c81180d807149207081042811410301401c5040148190400b808502c1d04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340733732 1250 340732482 340732517
    0x1902030d0c0e0f0f03010e01090b01030c0e0f0402012a0309060e010e01120203040206040f0305010e0c040903021b0619090e0612030d050c0d0504080c0c10210e010c090602150403 78
    0x700c0f080c4c0c10390541d03c2c3c0c100340e100c5000c28842d034601d45000385c0c6054400c0d8150300300205811281d5002c00c8040303003004104008081c1c660100d1b50400d50900e0501c0e0301001000070205100407003034001d03261440f0024401c04042e00001d00d00c08507011a22060b0001140c0c40066a241d00d0f090300341804503490b0f40070380f44103202c554001d640c0f00b84010070003424942c4a80c80886040955082203510f60742da401701c008400010030104202c054111030910000426070380003501c0d51500ca1444500c441d803c016910255640f506440f0000750101d202503401d02d8000f002080604903108800c2c2c0354070808003094050402c1e60703116103002603000c000d514107034042c031511004100041c142d00c1395100500010000e0174142c01500d0003103004608240d00c2d00d116017401c2d4182200301c4502e62249807078440c0b400c60300350031502405211000c421640307660710340022004050400b0740b080c0303400380d40382ca88407280711a0890140025036070305500300c44000850b00881d400403031043d00e0190102d807010130180762409 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340734982 1250 340733732 340733749
    0x5160b07060915020406090806011a070809041b0512060a08031c0b0d03050403020414271504051e0703080f0c030c010603061a09040b06040209061902030d0c0e0f 71
    0x42c0709207400310303c2100c5140d078841280c00540140c0001229a0001c0120702810400300d03015000040800392910407024803455a0f203d2030100800841c00812010a6684c603540500c484152090400303d18441c2c0c25001005544a402110030083e40d0704045011824010542d005075040900294544001001001c29101e220350045038081d880343c20781651501c03002540c11410340b10761109921142184100000e6406101c0441e00c4130030304604200360807040c807907201704903003211643c02e170444103440c10103003481c0d070b00403807072800a480609000400c6000904099026049109011080440840c03107846030150720016080c141d041c0b168094980c0f2100091209000280869142c2b48030880aa429079000382c0c810740d0b62660381c40800c5108140c100700c42e600c00c80120345640203071034195920b082070303a030140284d8000c40c0d01103100300a42d01d0701e00454000083c0c5405601160030050402903580e84284036400c0308a00f00810300420600461042200c10401480c0322003985c00c1d0800d0101d01d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340736232 1250 340734982 340735001
    0x316081b1813050304080d1d010e120a0c080312010506030c041509150201060608070c08030112110a12051615121d0303041110050307030924050405160b0706 69
    0x40090b41d100c903000841c2000144024a0604040e04018822010140c80c4820042c80750044840411004040f0b130791003200f540315400c044498445006e440c5110743e1402055002c014011504004041046640000075020025030221407413411780c4c946083c080036010954492420301c0041c04140401e030b01d15408441e21403258501941c0d042c1d620301c01d61101102e800c40150141c0d41d922424411346034400c241c40d500c090941403460003801e450391140302c903120511590540910310038146080081281d01c484400c240286114509501c40303102c04181c48200c002111144600040400034440c1071000200701c2e800091210407034501c05070300b174440300611140030004039580d0750f5481541400c0800a40440381036001140c0702d14047c036055801904104060b44600002404a005c05a2100481394040c4961a0104912080d4505141c20364070100340c0200b010b0f5140c030700c40840e41c1c09a110741c0c480d50050007100e4517000050007005c41541c04d40100121410300b045070102180f03280c0c1040511 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340737482 1250 340736232 340736251
    0x60302072105071a07030e030c0a140c0301020a110714180402010315060906080a15060f0504080a03030504031b0203031e0d0504080307091403190305090316081b18 72
    0x7000f00325960828089410b66508820b4683d0005000d0030550501c15202da050141c401103140c0425100e5169640da0540f40007040384581c9501051411001e005803206031b640030300259110010004007400205110014080520400000007111220b601e07000c0e9440001800c2c0c50004001c410040c0321a0324000c2c8143c0c140b5458468981690050280c4800204103560b54080750304e0a18000415000c405403081c1356060a00e80d1041c2c04d00c8008152404035072003400c01042e040102c400941d400d00642c0c1c4084842e00a8994034001d00d501a0055440f887c8681e45404054000e4103950700e2100b52414043d400d43d2052008a4192500d41044a44d84040e11181c1d41450411314100059410403101114403143c003000344440c0e1500300040e80b024003041400000c4032400341000c03942d10100700c0459050034042803411303000d06008000300c40040350081c00307441c091802160900780004480c840c0c1c8549100b8042d2080401d0b485003d0361421071001000c280c800d45050810110b0160302501d905032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340738732 1250 340737482 340737487
    0x20d09050f0f19030501050108330405120d02030a0c022a120717011103040f0803060d1a010614040b04090e0f0303010e10050a0806040f050f0109110a060302072105 72
    0x280f0030240301c02007000303600c910004203056041c40c9440e4144806803481c000044507000c0c4041f400364801e202c50100f054030f0300805500b5592410300a140403080b0340f03851502500041d200006640b10b800451241c420f1120501544641240c200c1e030360348203017118507540780b5882c40760249085105c0d05002d001741c0040c10324240421a4000c1420401182e00203a2058100c04003a0050300c001c0c052070300031041461005081d46415110244079010300d101c010b01d0314200200080050741d039070080c0750003960003070126201c410f030701d45039040c1d007074070031302400002c580b440f00c440b0070604120040b14160356640c2c160328101450710015034090401c09450600c14050b00c00f080b10b4002040001c2c60091143c3c0300c951400c6d0816030312405d410f803080e800540c0102e4405206001c61800024000d401645c81144c0e440e02922034201181428a4403000307003015424602c5078018800036418450f02c140088601c068055980c150980480c0702e00030006009403900041da08200400d00e01812140c807031030400d01d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340739982 1250 340738732 340738759
    0x40501021507050d06140306010b03040b04170f0a0201090c0803180111010216050a0c0e0103030806010c020f0a0815090102310b0301060903050f010b03031803120301060807020d09050f0f 82
    0x40a0320540c6d040818030081c2012404094901000541c0c0100380c000489442e6040c1501ca1a0a00700001d1018207480c80e82d0078401311031003402040304c064101009660f900d42c603030100d000b400b810341d040040c0d500310010a408241440040102d0b800308007010203d541c0d92103902c006480311111170307001c0b111a56080c803070310309003c20601d010308850f40b044028180c15041d84ca13010752044810740041682800c6a001400000d4003c4121a00484242803403048812148009404040e800541c41d070019130741640002c0381800010003203441c0350901c030070340400e136546a100703400c0b03005a82c8840e8406035452804001d01420100f0800e0b420b14440c0300031102501c8100803e030b60303402a8080da0014041360810011b00c07006001c4a041c038000c0c48028001d00036040c000999034040c0303c43c0c8201081070312000c08502d55042000352080801c0d00112512583c1d0b40c00c0c090903280d8200c0d802e901601980d604e001250703203e82040c00a5400082046070315050b810148840806400c00c01604032001c14643c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340741232 1250 340739982 340740007
    0x10509031e040f0308090a08030405090105041806110a030c0305060d030c0f06020307020303060f040509070522090602091219060207080c0604051c0c080f0309120d050702011104050102150705 84
    0xa00a1170252140990300e0030f81e1401d108000000d5804050241c00c00d2200b840a075550600c5141125000c550104013030a21480700c1c1c20032000c4800043c0418549484003845032207500140c4030400389610200140030300c1ca1800d07000d5801c2110800d83c062003038000f000001c0d00508481214500902480709404103aa40d208103c4c4d10036100540940c2c000700c104102840c0100d4030b80040c0c41c1c1602d090115041c0401d0141e034840c1203015051041c4154200790b2602c1c0b0502420030304040300400c050000c00040c0c00c0c80e00080d8010080203001c1c00c00340042d9180d100d0002240303440084000c00d8213601540c961030343d000070b40111404442c094004c0200c007060010800016018501074005000b0740c00090100841d10f01c02c0314540d1041c0040c925078031010812075801d41c1d0f9005150f012b0700d95261b64100c2c041c2d0402116140121600502003503007106100c440e44024807545282e0000c0020031213080380c0810078000c601c02c3d180140d102c900e95951005e00345203881e0f04150343e41400c0341880e0402c28403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340742482 1250 340741232 340741259
    0x90812030912031305100e030d05180a062403020603070507030909050906090d090f0b1c060308030a060506030c03040213060314030c1006080309060c07030f150e010509031e04 77
    0x10314a090095801c8810f018061100504003202841c042002c03c105181c7c0b07a40f030780540890b40c0c00c213681e60000941c0800c02d40f101084520101030660340c41310100d143c40001070074072a0030403040c0b242902021600070140310448082e030350028480c0d4110364805808403500d502000041f01000502500003e80b455075001d4a4000c4042002620481ca40504031a1500040d00491410403030808402c1250710903012480080d20f22040d401c607580c60801d0075403081c4012301120310003514500b20002040c0f203810400f45000300c14044c01405899a50f0b01003200601064400c822000800c10120300145020040408040189100814000c0d07032170300e40815440401d5007505507a000000c1d82007208809020945c01c0c2114000c3c10003a85080c41c5034990741e8059240541d001d0800060448000c8404000c203500840e0b00001c9400f02000d546402031403a1b42c0240c1c5050203d050010442c0c0002040c011180f052082c1c0000794203080d40d10501c400380400d0403414441c1280100310200d0140d11040d113 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340743732 1250 340742482 340742491
    0xc0303070507151512050111130305070b03010f050f120d0f09080601030b0414070f0f03140a0b1f1a0a1707021b04020412140c0109081203091203 64
    0x7180c58035440715040c8501c007100d1601ea104440c91400061031500480910914241e400c40c0398648402209454000d0041901d07681032004483c0c0450300c10000c41480141009580c1300d2010b95001c0c5a0304d1a40c04103c0c0000e029240f21310030080c0040c4842d0134940d40040c2042c0d00100050002442491524104429040308000258a10303c85071281034000030004014035194004014641c50350f140e02c14a054090b00081281d07401503010ba582100410070701024046c0805d00041c00740d611030025100725880e01c41210031210403071400b00d103840301186503103c0700c0d04421180410396804520f01c5040620215a006180070040081850340e81c910861204480703404040c1d64031092444050824240340c0d800c4500903014800b08005241c1c00315100b44520f00701140c0e5202840707404000340281c0125040510740488459481e8144440b00c59044c40008400d1f00766900c0c2040341c4011030f54280540992086a84124900b0080e08000381c000c40d840000e4101350350f046848c61050038420f600030744 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340744982 1250 340743732 340743737
    0x70302070b15010311040602100507020304032114030f1513060902120a0c0507030810181b0e030d11030904020712030c030b18041b060f1e230c030307 66
    0xb4840d151540c05104120311102d144150500307103803034400025941d1003480d03c0340300750549a90108002c3c034001c000b95006180c0c0400840d03451000700c19084120098036814a0015540224080c504007a820031a405101c07000c16000c802d6549e026206100011402c4064014248007c01410702c1c1c0a84a024007404406802503590b4030001d000a604a501610340b2a24526050740c1c0c4010503045021140c500f6814103181140d5500e86c80410907049090b444000200f9030391591b034101061a85c8444680101d01e210103401ea8145481210146441801e2a8040d80003860441c9924043d80040d01030103540400c6a18011042c0c0209050380c100c044112400740c2d003581044180c5030117005900000c1c1d0586001c1003646403600c00600002d000c00d015200010200d00402c0500050310680746000098124080009a0700d42006040e0240c4615207000603003000c40600119112072440040000749942d00d00444400d5180c1085076070154014904031a0200400818004240081c512688094 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340746232 1250 340744982 340745011
    0x8090a20031c081b0d060303030509060f0c030c070c080307110a140a0e060301140906061912230703050a0605010e04050703060513050109120f080f0609070302070b 72
    0x144207161400d618000c01c8005525080580c40c40a0f034095100c5600200e11612003c020000e9165202036114a07410012800e0034040040180b50b0035410071401045440b0440e02241c2d5a0017207040e8159003a187c0c000c506a04102040013641458040d20903240108260448507a5424003980795902540040310160b00e5064445002c1c5001c040341001420b82010101502140300d00140892105d8060a000041c124000c02c01e140c4003540041411045d0a50150701c03400c0c07094a10769220380032203c8500c40d40842c40302e60549404010392804980005541c400c403036409590396203000e0303101d036102403040038440215a4417007810442140118020b90180c06014641d0900c08141d40301600300e0a1540d4038041408002200000c1007011203402c11000205601c810300d503440b500c0c40b840f0003e051582884050401d111256000d803041059036151000c500786014801d8500c0c8400b15000440e400002c0001307292410029030013680106149401490b01c45143c1d1400e84100041d20361900b80b0645 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340747482 1250 340746232 340746293
    0x604060503070f03060c18060f0e03160515090102031617031303090b16020d170d0501410114040b0306010e011b2d0f17070309050108090a 61
    0x180300b40d00030342106180546030301002030802010104075110f40c004220240300c541c0c627981d214140d109400e81d0000d095466031400c0401120744c0c6034440c001e5500c54140380701544100c80c4d120b0704846100d08103070040c0d410408803180410b0b80056056040d03030800300042021a43e01c0008000314494401000d00344900842030030010301000c1c00b41c100c40b0111204018900902020140200800b83d045400070380e02c8120b072070040e20b0041d140b8021b0300842d00100b00e40d6064240c507040b5038142d580e8903a819107804c03000140c0340749214513810ba00c3d0440c2403844400d02c81c0c510395172b102c01c01c00406041c500341c6411242018600c07a8002d6104481302d440c003009205031907038801c4003030150781d100b441c00c5030900c0010ba400565038081d03130500510307000c2d071900c016040382c0070191461a64620b2142a107142d107161304156002c989000400c80c0da035910030b5440c0071140012001e031000141c16940b6420450304080c01940c089101409030503c522420840d03e001a015080c3c0441782c3c5400c099840310083d2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340748732 1250 340747482 340747493
    0x503030a0f05010b032a0f09041407080417120a0c03180314090406051201020c0d11102a030e0f0105160e1507110f030114040303050604060503070f03 66
    0x510800311641d46090200411841c4200720076030b90040c5c03141c50030700b01080d0f07412141c1281c07180b52040c1840000011030a0302030880004003501d9010b4041c4c501f4172850708904142c10905000302d8804011602c0c6a01207408503040ea00e60000d83d000c40d251451604001481c00700030000221140a00302c3e440710160414541d2501400100c002d072403090604e003c120790b40140c8070182ca50b1071610190008201074065944e1900080024000601041d101c100d059852a020b5071000e0b5010a8903c40d2081c840e20b1184031307142c195600f40300000680075040002c01c904002e4001242c1d00c851055208640078200440c01d402d8035000c6000b40ca0024008007400e070020f0400c0d6408401860f1645441c0410003200c09141c200402028249040010051001c001505210020100d0403114034041607542c204070b154040002c0340f1070101d83d440314038100d034400c2509031138203210421190441e0002090019001c2e03001140c0080000740003040050321800880d00d46102980101480342414404000340507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340749982 1250 340748732 340748741
    0x70e01030f1101050a0e060d0908070c0812040b04030602090117130c0510082205060702030c0106170307020f0105040503010c26010807030308190f090201090e07020709091406040503030a 82
    0x36801c4c20541c1c18940c4400002e03000003144100c00d80114800600c410134101705501906109621964603070719201c00781090020050035000e1148548641410568040c80c12020386080701c2c15a25520318250865441e40041d4003e85500d03414465050781072640d80c00340c140880c2c424282035486910114a5040c2403c5240040d44400c2c012008011003500e51940240190740c00301001e8031580d0503011f01900ca01d001c1c2c200d034002602600410f024480100e901000901810500c00c00910080c1e48030740042c10340c001110303000340c5117500c10441c25006040c1810b0122070141e0504000703084c15510390220b82034981001600001541300020a00c82201d440e00981d0f402d400448000e4075581412040c079030322040b40c0805014440e9060019200140034442c0c0035801420050a0090040400d0208044d00c0c0c80e98049000c50311560f0301165156001d8102d900c40c4805038006c0400c0c51905400800801c00144159080d03a11820110541034042140e28000e030b04c188021036407464079841c1c07201140d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340751232 1250 340749982 340750013
    0x3021005010b04210c1d0702012703180b040b0c061522020904090f230613110616150612031202070507060e040f06080a14070e01030f 59
    0x248148014403052843c144031944144c40f441c200031040c001428019082a41e550218152101c401c10440310090850030b514021a0a50002d02c002000d020212081042c00c0184a04003449480031201007032080c10b80e64036400c0004807032040c964907081ca40880754083d800c05445a20001403d04002c0004c10090b5488640c414506001c0b04a1000080d14803400c2d0300b4081564020130310200701d049880e81101c1702100001c00400401055242030000b00410003c01d60b10350b025044101c1c40031907900305882d0001c50000162241c0da41c1c800866010403441c130001d69603a8480195410345840b001c0041c4410750340000501510f032494034006500c6034024103112400c0d420038804014000122105601135541400c0c6503490a20004404009001720807000d00140300c1c001c80090843e4001a0f500800d0b031080d9801c2c00980e0b4003404100503a1414406d110b01036100b02040c5000c5945c24681c04c0200d45098140c5016540e45c040080032201c00b0380044d5504130f0300303c0f214401c00c6001502d04a81 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340752482 1250 340751232 340751249
    0x1b0b190c02030a0f1a0f0412030c080a1508030403110a0501021b0d03110114180a030903080a0c140f0d090302030c150d090503071203050402060301150e0402070302100501 75
    0xc40c0d05035030100380c0310030780c400004245009074200c4008005800c256121420411000c0f01c4403840c000e0b001d54115001614145c1e003504903000c0202000d0700c00d001d0b012410032280c80700c0103182c03904171114000b0503181048105042a03044081080c90041c0000c1c0015401582440d001c0000d4000b000780c0000540d200d9815580b12903c5030380d00c82001004031681002c101e50128003850b1b5402c00340d406400e90455034119520380380d21000d0a000c0300e20034900804101c0301c2040c010180112366a40c1d04d403114809004100311000400c0022040001010002064540540500e0f03076130b034480d02d428400009119040d00b000c0c20310214017000b00854020613495213450314030350f880c607004a0b40310000411050f0007807924440181241440b00220b940340d5920640801901d07015046c07807a1660862507003101e85c0001880d144078510b00c6802140d000743d8000f080b29103103900c3e2048021048104103d071805010340354004480580e11342c03000c0e00d02c003800386d0058607510a52000324400c981c4146c010102c2e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340753732 1250 340752482 340752497
    0xa02190e0408090a090c030f0c0302160f0512042304021201050609040608030a030b0f0a21031b21031e0c0504050a0603020c0f010c08131b0b19 63
    0x200d0820000362034101e03402004150743c0d140e100d000314018050f580c0120384800c1c03c1801d07030902194107034041032000301804d40400001078a07070700072001da1040304040d01c0304c0c0c0c207044000408510800b001e010541d00c00d00441d140d4038022204206907030441da000500c103001481d03602103004500c9680402c046070886d0110724104004c440710107641018010280600700c0842c4240051315198400409410070358200d0b92030b038820290003005060142c01d82c81c00b03014003c0010340e0504003059a8800d550b054405001014441801403480c01110302c03045c1d0401005010001001040f030343c840150b203016000321131090b1a02c0001d4510701340520750b12000c140c900501c00d403c240700a04800d02c200e9a07080301260070709104008413a5800b60782c100300e60120a001001484640541c0240f0050145200769040e41c82d036000814202c0b0000c2e161080481c95100c00520186a20042c0c040c5041c8074850340034102c0000e0a6004c2985101d40125102950001e5400e401c0c00083e20001030004582c0381280 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340754982 1250 340753732 340753739
    0x402090114060903010501080d0e0102070b07080f04030b15041410050108061801140a0b07050705010e06040902030708071107030213021e030a091b061b03030605040207050a0219 78
    0x204801814490034a404200c150820069a915400c0725803c040043c001c0c421541c50301070058541c0d09520565002c20011802040194004240d0204850000880f80e0034011292100c00340c40e4440102d107240803100700004800159005141d43c027502c01c6125503003261443c0c406120407608030f119228040d8450108005000307081c0100c0c0c0050707540078a014040794540801155001e043c140d0b012503030300c103040f00108480315803050141d8110002c03101c03d102d066407042140054400c0210181035a00603d409011550042449440801c03000c1e126500d0141d41d058202c0032a0025034448000070508030500c250f01d640003840c010085c5020002d4034040d0701d1a400140b03109552010a03201c0754020a55400c41c000b03d250662000000c1340d9815901d103000c0910000801c01c00c00120340d4603440c04510704003410b000c80f81005071080c940307800f0280803580b0200e40c3c450341130540850805484e03110200c1c2c10345440c0050154244564001c000359a900d1040205806601e05802c0c4030340300040040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340756232 1250 340754982 340754989
    0x11030903030403120e10090209010501051c090c030b15150f09040e03040806070c0c0e070815030f10060e01050607030c0f03021c210c231c0b01020f060402 68
    0x120740260707041c20400c0440c80718503901000340551421004250103146c0d11840450300036042006100c1c400c81c3e0b02c1c0116a2a01c1c015a10385c0510485032041c000e6580703403010200c000e540f0207050680100ba81c6407009549039144100307803d04445d000045504080e956445040000040001c050002c01c40c50500180540e0168a80100100d441c861500c86883c0c0700c0c0d001040c4121400381032280b050300c07407624200d0710107400281d02000460365a810481c00040040b100c40f00c0c140911215600c546080d182c0c090150780122181c002598540030b00089191802010081044944d0300650042000c3d4a07004220043e400305912031070080314200003000010f0b50145802c80d480b603221200d800b444e02c0e1801d0803450b250300300d0014542003d40d40340301444a41c100311207101d0703501d10031407400c40c00c00c2c40b0070345a0503a500542c041c40498005050741074005451039070202040c0c041c000680c2004034400c0031040c1d01e07010f42a1080392a54a01c58940d013540c1c140070614600c000200101014282503010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340757482 1250 340756232 340756237
    0xc0613120e010306030c1418040b0f18011a010f0503061014190327030801030b3d120c090c030605040507090f05101d04021902010203090111030903 65
    0x240c00800c420001100c000381c0c0aa48180007954110015002070354961a1075011030035500c603060301c03944605030482c1079400f2092001348156480004001c550f12060002a43c0e900d01034034540f464440c02e00ca6141c158000d119204114405100148201011740005420032407051903d404000342002000311035280e40d04100c1940c066850a004008143e454103c2c903800781e1405c1d40501c0342102503815a20741d143c2c010b0302007802014030104a5000c20118904c0c40c60300701c2c0d4002c0105000e000104042815001420b03881440c828203123060340648580710002c0b48103025442d0028901c00030415158034040031140c094403241d100445c0001042d15034000b911072912803480090384883c55180da40b4803c2c2c00000040c50054014045400c0650700a000b600e07060261090b404d1141c40c00213661700d40784540382a0701625813a00390000d21070340c01c00d0700c00f500c001c4c001c1c98019400300198a0303250001c1c0501c5c44400c616600044e1207061a98801d800e5541003110215034100900900480b04004401c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340758732 1250 340757482 340757513
    0x10207080c09131202030403110604030f030e040e010c050c010606050901020304090b010306050a090f0f0203070e06090d0c030b0106080606040f051003240f0b0a08010302011d10050c0613 82
    0x1521941942d032036506510703030f10486100a290801e48070004076560b4000010b0801c1d64414200d02151503010350502000b0700452001030403014010302c810011070b001c1d1100c1c0c8440a00034101040040201405a00359540700f4007803800100d0020b16400b4080c000c0c030412019000a250041c582010440001e50b00d002e1802010000c039510202e80320941c3c02948240010880074041c0729500350748500200c0100f0012030085c0381c2d070f81007071001c4c01340300401d108907031040750746444003145145468140059500410301d451307001800c03a40b4032000705804204400046100c1d440540d41c6605001000b4420200900071a0186030144001d00110303421240c1e54094500070740b50f4280104d04650200d0141010321408242c003003064110540c80c0355081c01d11000d680c0120b802003061580c032150034a0394443c00345c00c0350004000c4001480158810561401d50b0700300410404510301d0405d00142c46003003408484c1d0b020860000711000b581e0801e100070356010444940c1c03444101d6940e1243c8041810040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340759982 1250 340758732 340758739
    0x60d1101081905010e0702100c050a1121220303050306060708090409140c091909150c020313080606090a022209020909060604030804061209080c060f06010207080c 72
    0x40010145814010042c0c8001da0a45040c05030356540d9040102c00001030740c0240042c054071400d0503e8041501490380c0313041c110356400c0d00d0045040c408569150414851134454014040d100d00d400940100346100b40304012070040e980d00d0312000d0182d1544a00080360400d20441c042000420340000c00d407540003000344d914a03952015460250040d12403c017000c0e81c03041c44d000a10003485101d80012241000003400c030780c6003032100341c00c018003150120f407061354504040d03002c640c0e0510030380c02c86a0024443c125400d0110046400c07501991114036014005900103d5086152003c009048004128180150100f800c09602282510308000c0a8aa00c182c00084245d09050021103140500d100f80c1c4004010380e45036800c54010390702c030000c1507100c0c2d804200030030f400f40341401c200c500304d903071181d040c03846c1500d00001039a50046c00001503c0301d555820042004c82d80f0304d001080d1142034100030f07021910b80155400c1c2991800344c601d030f0441d880340c40700f0b10503014005813050140b038045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340761232 1250 340759982 340759997
    0x1815040b0f04140907080114160e030d08060411070b0a0e0c0d050601031406071b0204110705010504200307051507061b080a09020a12060b210105060d1101 68
    0x51021401d040c03181d100c0d941d0050700e0042d01d410909821280c0500a0f2401c20640d4401551042c06a00ba02c05081c2c0ea22200c07a22800030402045100d20034000d000084d05000d035180048800003414804c0048205002c521200100041f078903044c4240c9107503400d440521410441640c40d001c01e0000000c29540100307a403444411081002003041689500c0000d1610001c11a2840c01e20741354042031201b16402c0304e07034501c10031317209101080b5503124222681d11040304030035000c101c1e41d104040d07400690708207680c0c4007210803440414004103c03160041001041034101172800c4502c0d4110512080051820000e8056180d039020406004407038044a00c000c03210032100c1c042240380300e0340100600c01803804d19103180305614001c10302e80c985aa0b496002d141d50301c0c480420180d4855440c001c0d44003120b07510520180e5110000c4040503401108001400407405d008100d048541c4400c4a02d03d050209140108000074002c40b07500100644400d10b903d6120b9403584c060a82082c4407a050003a40b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340762482 1250 340761232 340761251
    0xb03070e120c0301110d05010f1d0a0b100e0f0a0311040213050303030a0608071706010608095101030602030402010c1506050f090403020706050a050d1a181504 70
    0x100010340d00b2000040c000c00030304440c0c0813069400d41c4590726070341810b030800000180016a0038240002c640c5183d00d0001100b00d01201d180b0003500007040145d2141e92580308010586034034400761507100c42a2030b881440442c9001304230644508810203441640b91120610000d055000c154966103000d40d005a1204607000002c40d0b040140d410a58041c44040f04000317800140340c02940450b01c4050640c4d81480e182c0e4180015042d0380001a000d55000c2d00041061921600102d42d100741d045040d0345040701c3c00440010303945900741c09902009003480b1110115018082c0482c529a58451070109075008054004040d400503c00540a50350200c001010769001e0040c400f0025402001d03a0f5049102980c100004c010724055680120ba22261005841c213101404034041e5826070028444107281c50700490320356010b00c4408080000901c0900803030003860040800c0382c00f100d07900210302c154640c14411a4091201e00c6c0400c06104400e0003540d5032141c40390b00c4144020750300403d11521 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340763732 1250 340762482 340762519
    0x1201090f0b0f0c0403050c210a0302010609050115021c14031609050d0206031b0c030c0303010512030f0f030a060e1602060a06081b0310110409060b03070e 68
    0x960440162000c00e1035400001003180c0004014840c16804482503869207601c1a014102e01882c04014044c1e03000201c8882c0d50301d0181d24003800540f480814810007054088414288120558200c001d42c0d181d2906219928482c0610741c00f414520a000184400101c1d0095071440c0040401e014108070b0304d02c0c0030720140305481e9180c0620411041036564200f0400740e099010207a8020400100820780102e0240f419105280c80c064005054a0868403903400b552407248012000d00c85010040210210000d418000707000c1c06400c0354040d5499625000501c0b403200700b80e00700340e0780783d4100b0004654160070b001c0a64203103100e203107845902c035550380e402c035030082000d4ac1010740d451058800304038038400c14100744024a100d541c00d841050701c0340c4490b04d046d51003d00404100d504080715800001040c40c00c00e4200e281d008080343c581c0000782071100e04540800310107400c4000c00107410f1100800d240200b400900b100e860302451841d105400500f2901c90303d607018410740e14483c9441c070903803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340764982 1250 340763732 340763741
    0x6040b0420030a15150216030f060b010c02090a1401080712140118080a030f090c0b07110a0303020606030d022107050c1302031902040302030c090709150e0108011509051201 76
    0x140f0701310800012601d90b40d0070400896841c248100611544502d0381001011540f003104803640300c4030b181031580d2240c0c2c500000d004600c3d94141004400074802c005039840c2401c417802007035880800242c2881a000f580f41c2400140c2001c880c5501a2130100181d4409500d90400c10390400030a2001260042d0f1250140c5042128068a003e16004007414070203507800502d00546241c85c10401110114000800c4c2d031078040016100056860080040f0040d110046c103200c0c1c801c14041414282c0440020038000d0300d50400d80c01a0300400822000d41001c0040c10f030071800c103000500656903e403888600600040100c00038407480030501c80100300040049e4a41d450004102c00c12615458070322000070b40048607146140300c1501243e42144050b40b089509684d0098040c01514690b078050000d0040e01410060801802c4180020485060034441e0018144c1e41d0b40d49180480801c001031904d101070308159120b400c041d14408005030000c84600c2154000c3e15021407034085041c4c0c050050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340766232 1250 340764982 340765001
    0x15150108071103041d060306090a02040e07051c0506011706070c080c0d020c040f0b03030d02070f0b0a0905010b060a08151906080907060e0109360506040b0420030a 72
    0x74440860040b41c11105c40e244120306105005504001c0d58540c0105651178009a440c00b149401080a010160406030000c403128003840d0100ca0145036503001140e6441e18040c8500717640c1451004070341c104003051020a00403c06460985802a041e071a1151070300d001400020a05c0404a025000c0080d0b980681c1c0a5103030210564500d4111803030f010351119000d5030b08911036803070110341010001e2540b0801ea6004070260085080016a411100095001ca101500c1c1081d0402071900019030360904d1922520081c44003060740009031900074292440c0c1401070b403107402c085c4181000d061b40160056800742ba071141903035001c45003801142156950802949411110443c00b00700c103074105c2a42402550a6012541d0403a0388000460700b141011402c0d0740000c02505003009142400403e80031202900e00f41c3c04800c87c17066008080d00203c0c00b4807140e005880e082080714926043c440c160310484142d0b0f05000210403080868900c50035840c000442c441d02101203240a03c036940001c512 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340767482 1250 340766232 340766267
    0xa080123130b0a021803061303080c1e130b071208071e0207050102070b0705031605070503060f1e01060e1005040e010f080d020706020c130207020a0b0306031515010807 74
    0x1241090f003000030107580000300103031401c6454003c244507401c000409a10842c071010052001c3d042d01d9a0441304140041c1c26905182d4040c040c07051100601031810000c0560441166500c40c1c03054080080d20285512145440e00c06104034000b25468090210440019290052059544200c195081901c6841ea03c08001c001d0b4240c0310f40503000070b159015140d00343c08031941c1c10750303501c2c07a0110340c8101c0100400c143c0090094468920003040f0442c1ca0a129609035000d00703468502080c0b030840100e40004c3d43c1000031081c8000701c950000c05440114100011200c3c1d58184613020300054102f1110501a08800350130042e1980701c0c109460186c1880c01010034256942e1034120004003a900408849001d511300c000880c0b400080d15004032252038002d005252801010407540c890f003000b014900c0340d020410070006a440d401ca00014084c02842280c4901702082494900f0b03051518101c1202400c0f01440003881358024591400e0710241381603211943c460400315144c3ca60150401c15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340768732 1250 340767482 340767503
    0x130f15050f09010f05040f030c0201022a040b1206070f030b04060905070311040e010e10031407090608010603031407050312090109050d0903080304030305220503090a08012313 77
    0x8241c125819406420000e0003440540200c810100450300c09032070090512005d54500b400080c01070306048040d0740140166141c60212603c545110f203200c1d0010300280c0d160116030003c502e498031401190400603100642d0311003c5021a66031440017404450078081c0401c4200d0a040c800d801c00e04101d035015006121407642d8160780000741000365000c034082030401c080040c40750552015a003c0f6074010003003200d1030f440e02c10302940c219409496921501d10b0703108084041488404007103280b09044000b052a04e140103000c40440e5190341202180d641441004c0001c25070080701c01d40c0700f44403444026540c101918009183d840781c118990400c500420401c540c410065005520b21801802640e107004040e00049440030306500008001c41024408140840e1099100c258040c549040010641c40034100003420408141c0c03044440e50300009005c0d4007400c002480ea4018204000280020300c1d4034401080300d08042c804c0c0300c2c801c108042c00641a07400b02211072107502d0700224a01c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340769982 1250 340768732 340768741
    0x100e1c050c010506010503090d050703030b04050405060718060504091e0c02070e0c0703080a0e10110c0f010209030718060b040902120601080105090c07060b03190c080105130f1505 79
    0x20038540090189407125442c1400280c02540540100c03881500224050041c2030b8038104181c4594000f2502581016501c0c0e030364410b00c0d2110320405000e140a04024032203440c0030a00107040b0103914541892507030401004100079030b00101581c00390381040d031000c14141c000c540030000d81d00b001443d1103125400c010005500640110f07039038040d02c500010469240d80c55009580c542d00c150100100066042400a5030f0181c07240c0c01081c0c6416020701303548412509445940956141c501c0c013070507010001901c1c0202c13100c1000281a2551000000d41c00c0c9180000000c0d00e900c0c240c807441462007020904050190070b01d0340541e0260a40d0022942c5503601c81003944029001600100001c2c8152000b16006600030b40c9400d04940c0c00401d00c40c583e548011001300326030080c40c01180c01e251201501c403150b90701445003981c024540d0400342c0b4003aa26042c501c003805c03620b62006009e07034504804d2003807545540380c1070000d00d078100a0315441ca00041c50000641e0040c6894515001e00d40030502 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340771232 1250 340769982 340769987
    0xc041812080f07020109030e06030a0e0a03051801091a070201020f06010f05101d01030e01090f0605061c171305280510121508101b090305100e1c 64
    0x282c2c040c26682c07050501542d56000300380c2c04c03034014500140204c0c0300491a0201031600030300840e40710a082d440484d0003200e400c4c580e0315005500c68224040303080400c039036007444440403550103810404d10300b4014017840d02d21195981e822592032000304803800283c081c01e590080186c10f040c2c20000007120155a0748940722000c80b00b060203245c1c41203102000314400c0d41c2c420300504411041401031140c080c620701e40150018007420710f150f0b100d95241e08181d400b143c1c03030300903c0c28940d0140302c010a251800008000140744442a05440c40c031030880b00e031021420404040d5020010322003c15a96601d06211462170203d582c0041c0c0d0004441d818204104440303464840e40800741040701460a44034810004415090840c810015400401041c1e401400341c0042c80600141c00181041c3e130788440b00203003007090601081485a4549941c001990300082c2c441c86619018900b05021030706542d11151280302d20301c201d2119a4481c45003010204050100c81c408005006c3d4601c031405410401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340772482 1250 340771232 340771247
    0x8090612071d1503060904030908030a2304031e0507170c0a0f050f0d020d0b01030f0c0b090f01030905070f1203090b070314220f080606120c041812 65
    0x4491a018003982c01061900342659940c1d4038002000140341560348032401e102c40650f0061003941000f070010300000d132045051005008031941131b034840641c0e00d002c0e25840a00d82d040b8104286402e02080700f0000304805408903003501000380b00909034100c02e424118504501500060190254890b244203a070f0400103102010700c1007550442c0310250750703001c0c0d08055401486900d41200c0f550710500c4091a0280c1c01c0034089100800c0100c580000340c03139581c0500000d82048400c9a204102a000e200840150600400084400c9880c10007402d02090944801c20882418552102002400c0141c18014107000d040c9100c80c030004259104598600c100c1200025800f080c100640440d40c000d01404176034075a5019190300e58403603141c008460762a03002032803200300b00c5800420801010310340d069000007840301c20b400300c8810f0300741014181042c0024007160720500258080c613a8071640030031001d01e4503004540005041d60502030950b00e111100a0040c118441107140d11842a0042d90 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340773732 1250 340772482 340772507
    0x60a05070212060601140a0908161805010303230714160f0e1602030c0f0d090803030709140a0915210803040803070c02030d020106030b220809061207 66
    0x7980071180c10303000c0c102c030703190301041c3d50041c001256111000c40318085d503401422400100c1c0781c044041c1e40c0e140c9240f420025800c240302e0011885e00d01c01c00000400103d4204014038241003001103501d9650040d0607110640600d42907042c280c1085040b081d041007d81d50080e03080025002806c1038502c1c3d1039114903003803042c21075210151201050640c02d12401000b950a407800e0313101c26403034100c0c10510422000031094110f00c42040f24006140c002d0140b1441d0102e848014601041d6108001d403d01c045600b10700e00507030060007041106540320b641d040c229210756031100491150003001c0f80096209801110a40d8101030800303c81c80c1e88038100104688106410010840d800c80100300304403619100901464824400300b00455100d01c011900702000c2d003403559070300c1c4090b80403d040400c0300c200c00f80580d54074a8104207021504840942c04500d40c08600807030000e82c80070240c980b0f142c0b0070141414001058052980e01e42e003044981d43c00d184142c200041c80c003054014180c00c41c606 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340774982 1250 340773732 340773739
    0x212190c05101e0603021e030319050304030f0e0105030403030c12020a0503010509060904030519020c0a06030e0c060a050f0f12010f0924060815060f2802060f0403030b060a050702 79
    0xf850021904a244140f00541c0d034020b2070740b10b403e440400b400220300c0461001d130354140400c0000c5854036846000544804400e9101d09131a403909007406002e070304018220f0340c24031500031fa181c1801c1c0e901c002165882070307142c1000a150540300b04221010701815110320801840091303480da040e42c101019504070b410445e0300603025510002071010f01481a02c004000c901d080c04440300020415203281010300d110f01c102e802d0800e82000181082d5003991003600880d45e14001c5501481c400d020300045010143c0d00c6a1400c0002c030401462803003003400e01802c042011603400303030039010314040310458603502000c081e90356100d4a003442015014814108440c1c60144615062503441034080074288440000800d05440c2807020740d200b102c01010440c050040d00c030300b85c50550ba8840540022040d81200c103032103d10402c100c1070000e20003413038031101c1c0c1e076040349024039154002212580403045012020007619103160a6024000012202e5807190020401144266110b405064190b0080f03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340776232 1250 340774982 340775021
    0x902040f03061b0804170c061302030d0c0809130608060403050a120902060d020903010e0d03060f080712030e0d0c0b120a021c0c0c060603120f0212190c0510 69
    0x14620111400e80f001070090124003000c00160100d482107180d02e420800d0009407a1130324210100c50f50414208445100c1101b881003d00030a40c102040704000960141c24000082c010507225000e050048045552246e1000d10f494180c500441e000720009120400c00c40b01a41014540030b4120341051803030764001104503407400c44045080c0101000a9005000c0038034001c40785000c500070b5803003036014542540d01c0d04000c040c0b42002f084251411b0b00f4a550018040d41882c0c48014511541d522480c00c547c821740703080c0503140d552020b060030a5814100482000a01400300b40703e500c3c0528054498480c0b0a800911034204c0f0000f0000c29402c0021958030341e0f10b00e1200d008078003d00c81001d00b180741d09207800c5592212540030134904040c6040044070502e40340d6070f001c142c030616041140c2036000d0110b64031569411090350800b2071141d002400b104082c07034145181c01e00584200301c08100e1b000c4c03554440716006d40301c410b0b0b9458000003681e0b9810445240000502141c456603800030844 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340777482 1250 340776232 340776251
    0x30f050412230d0b0103020403080a0c060f0606051b070f060801080c09090a0224070c09060801090213091104050a15080f0c01120b0603250c020904030c06060902040f0306 75
    0x4144202c11945010031103182040d0341d40f88908000d00340060b03590706241d420800440451122000340990340c0c0715035640e58250302c2034941013087d550f510400151450418006200d4150030105691449403c90310403d6040720050300790303190140315807200158442840740070920070f6011581505a504210407a100402e605091005140c4100d074050007075001101c405c00180b61000700030724100180d00400001402000c01500030303501280c82118000e820b8682000100e000c2d004c0c640c01071071450001c100354400c030707000700b00c81c080201e0409400607a01c00050080058490f81e001ca60040548200012310340f00c01c030328001740102e04446c503181e048440d001540320000501c15984102c08070184c141900100c00544200b18245140d0720520307210601b1075002e45501020303600c42c29070090303521003c400040000401c00d007514101001c100700444050f001d80c0318221140d801c070b94035183c040000895414650020206500146801400010005030000c0003621000c2030724061601007015414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340778732 1250 340777482 340777517
    0x10219080f011a160302070e0109090b0a060b092202030708090118020a061103040b0c0645010902030105090105011508040b06040209010207030b010f061d0d12030f050412 75
    0x10b81c00c2148614140404c0b400e2030a8640c9426419550b1003070049a00040d290384410a0020090308689451584d0b00740000910011a036a180c010040314001c11406007007070b240030b03c607110b141c0b1031a00440f4202d0801d41407581c1c044490070a4900100115142d0400d144001d015000684100c0c00542c01c003544100d58005e019145044168006e0000d95403d2070081c0c1920644001c00e55000180010f00000030f680610800034401a550f541c00380206281a00d65012026600c80d400000c2e01c00f071a28403031440f9844440c1001c000341c0344108501403801c020856001d0300a540c0000d405500f04414040110015007142c7d042e10042d940e400c110301c125207802c40b20608101c40c0681091303030080104030746040c1a4000c0c208140180b054900150b20390726041b00d02c00080c0d2004586000c488000c014071b0380d0080c180b0031a100c2d00c080c2e02d803440c079010b00003c610040b14080581180003e11a400160340030b80d10018041c0b45402e001c3c0004e29103800d14000d01c031945201e610108290727440b00c26882c007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340779982 1250 340778732 340778759
    0x242a0509130b0103140903071205191202090d0501050601021c0206040b060a0305060408040f090b06070b060609120c090903040815040503071410060e060a1205010219080f01 76
    0x85001e401081c00303503640031184020302021280903050541d2405484410303402ea00700c19110360b81c0c40c0f0056580e05120b180c041c040c00440e0201c0303c1001401d200413209244100040049170030f03035150180700346020803640b1000740305080e50558409566002a0b0400506410903442442c0036001d031031050360303050005990300c00046030303000050700510f001400281c811040940c00c1070b80507240200a5403039642c0d661808106440688104102150401c48103050505090280010150900c10464041b020a149025400004021700a11800103260b5101d09060381c10241d401087e680c0b100c2101302c8280c5c4c4402c2440c00b820f0041031504001083d401c4000110340840b00781c0d034000c1021022080d038003204200f0140045651b13010420080300403c0c900c4180d15203041104001d840c80e00e540c1070380a021151194045841c00342510104242a92000407410032240c0c59808544002d00e13a180180c02840341801d448114141481010602580440c011303204800c10102558980d80307c1d4540c00500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340781232 1250 340779982 340779997
    0x1502070806060117040c1208030f0709032112111305240a0e0d12080610080606070c0906030c050a08150a0b010c02310e030403242a05 59
    0xe0100a441030444c03000100083e841343c00f400c01044090703210451084e201c85643c2c4156401b200200500100d142589141d680000da581002451203284d40d651b0062406500c207600703001c051003070403035440700d001786d03400c2c4104081c0d40030800a2042c0b040305401c003500034000d0343e007030f50f800700c1d001041d10b05200440e905680c1c1000c01d142150000000300340394aa2041804c60104290448015a29150001c0c0b40260070701c5248010740701c0300b040000416440c4003c002c58460a64a8184100c20703400c40c1c0d00d25080202540c103150b03552410b0805400303240c415403140c0c1c0c12900e407010010a0101e0b4410382410740f5400c03200c944000b6900c500042e40c49541c4811141c1181c0c20300d003c00c80a114662029441c400c2c1070608000890640e00002d25aaa00962090b6100c040404500e40045020a01c0249502802c0e00f044040f164164041c0e4038002c40c00010036803a4043e40703466115690903065500520031003c01d12002c1880c0071040c09003c0100240c3c10b40310781c1c0d07156a01406004e5429207102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340782482 1250 340781232 340781237
    0x2010f050c1b03040f18050a1a040c050720010810080303070c0614040308010303030e070f14061201120201120e03090d061d06102408071202030115020708060601 71
    0x5007a00001501c00700c0c0c2c04852101c52901c02000b001880e0726000c1c81030401072a0144211840400c11201403003610001040c0b0490b0b0f41c9030002032140c0700b2090300000034018056500090040c1c4054003a1350343d120b070001c0a0136840c54418491000461231100084807402030361066025160303009030008850f052f01076404250400d00015461500c00da05160320107008010205a1004030754016000c0303142a6070603000100000c005109041d05409007120030304a00e40100185c9180421020018116000c0c1144491600b580c05045607100c10030b44140e201c0341000e00b40c165954031460030724074080a4080780825011001210210600e105182000c4d241c00059440c4c514942c041150300306086500701d5041c0e90303d607807000a04000e40c28002c08450704400074000c500340800024400340459004410f00f80c0c00e080d0580d135107001c2198a4018594600b45900140c690306001d48510090800e00c0020b2031011000046804081e0f104120307001d0a80c0a58103032544031f000c6186c41d04001c0700c1e00c602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340783732 1250 340782482 340782487
    0xc05040303050418020706020d0203041a06031b06070204020a0906111c03230a0902010305090a020a0506070c120f0b090601150507080904060608010e01060f0f0309030e0a080d02010f050c 82
    0x1c03071444020100c0c6007201d1307100010b181503940c1d41c50000301d811100324108059808001c000400c08102c40d030b80c40d450040898a802c91400200003a03071a00b00000003205103550101c0e100003030322180b09030760266034001d00640d20f440344150300a01815a034030441c400104010030005c4031481c08144d140304030000100d0000b0340a500351007640076200341c030642071010340e261814000030401807200601800380120045402081800010705586001d49894a142c1140ca65100180d90303803490b407001c0354016100c0c5a01c800c014100303001c2000c059070001008942180481080081704018648158824641260380b500c820300080d0382c4550900071608961000707038503000301900920240441d2489048201d140400a8000c00c040d503295a00003008606000014003558000b102600d000d0400d40c5040884e400c0d680c0380003498150134002250925540e45400006e00d4860b10001d0209000a0f041c01481c07030317840c032030b82d03540e020403204000042d464440c943c10742d500280030b81c40c00344981069050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340784982 1250 340783732 340783739
    0x21220b010303140c070e1801060b220306020703030906052217131202041407170a090206160203010c020c180c040f03080a030c2a030e041e0c050403030504 68
    0x890001040840c0c0355080d405102d4405603080070048007000c2c10606c068422541488640e0840e4062003040d2101c580c0d0410005010600c102825100030303d450624034004406080c055100301c108540010b4040f90001558809041d05500100351481c4200c0302041a80e030780b101c84126481d600343e00348034039000c10460030002c0754074140414842c50b02e8000680c40c1030340010500e0515000f50744605000c2c1d159142040542c60035200704803400c1a24150f0020b180781a480090607980b0340301d0501943e504030004580b41007800d81c40400020383c0a080603076688190001c800b44140c1060040740710390301f0840310f250740900c081655a070061024040b03c8850210181070260024003c0014015007c1404000f81d2044191881001107000f0a0500c0e0b42d40ba5886004090356103000d50403051220070345083d07200c2014845881c2c007555004540100303001891604551081d202008035a0190800c03881580e080c52251a2408003410f40400b0029203aa0b07030400d850034052440b010307012032001e10080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340786232 1250 340784982 340784987
    0x2031012050a12050d021201030b06060301180e030d060810050c040602071215050403081603060506070201120f020a1107120b0c0c162304090c0b070821220b010303 72
    0x40c043c004460500c1824181403440a0040360007800b1f9207800c1014000c0104248500010301030380046050391090b10b1581083c14008550041e00034950119540348842c1007148400c1c400e6500d4009140018086140e440d40c50381d40c0c4d508a00000c2640500c0d280104020b0310300c0208803411a1240d4015080f06864210f004500b50740141c42904d40414150a000309001144101440740c1c0c0f0a440b0b60303100781007110100782d0413034510900700c0c240f520f001001d121580d42c0c00f040d01c5c0516424a00302584425815240c0051704146861404942c0003003041c6008a42000c889034080f40000300301c0c0d03036041c0c4d03881104601c04480c2c04d006d4a14100000400c243d89121002011030701c500750200c40007501c0074142c00c1810b0b0f8007a0702c0315100551007682188809000c0c29402e1a40307504560030307c1114100e8440c42d05079080da02c500703240164001012000c000c0c04e40c013914180885414a19100c00302c1800202199008503181c2c07909003800c2584d00f81540800b003050324150340152100740143c0c20355909 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340787482 1250 340786232 340786253
    0xe0a150c02060705010204060201020a120b010c0b07020a0506190c051c05041a040f111f050c01110c01060302010816080402090601031103040c050907050705120d06050d03020102031012050a 83
    0xd030b811190402200020400900040c002062540e00050307892141c140014104020340b04190710180c200341250b0030680e40b00c0f5613014090f4000c0705501c03054417a120140d00d03200c0100002095402800100300b0644407150050001740c49100c01880101d60040301141c40b88036010340a00c010b00b16001811480607207034001c541c000d10451003c5504d48038000110080b8500301c0d001c6882450916140041222642522000c00025640310510010340e5200700301c0d0110030702520040080c04500306c462044250007441c3c0e10981c200e1a15610000300c504a40a0a0a80402c0c1d000c074070198003081c0a040c00692449007800e860341c0c0c9018944031030f420001030b1480601070a0406443d10710611101890400460081d0320a070310085416150405214264030000d11040910400307012800100310017050040980c05000303600d5136210500c0145900401c0e00d82c10a50f00070003000400300401d80c05500450241040c2100d118229a441000340a00c1e520f9440061080d000001c3c0c4400245000740f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340788732 1250 340787482 340787507
    0x435090d020306010b130b0906030a0902040b04110d11120c1e1804290402090415081f020405130e0a0605090a110d020906101101050a05070e0a15 64
    0x510001000e600000e207031500c01c1c0c1081301800780000d2035206075200c40f0030741c00081c03002d1075001e4205445400011054040100b007800210b44500e921401c41da40c3c2e40c408404000c00600c10484400c0d45102c4030741540240d80c103410410314140944c003240802a0a8840841c1858a0b498042d6903050034561140c0144070403170802c50030a040400828110743c050000e621000d102d042d58403100d941000700fa9070034207850b80003070031010380300201e03819601c1100620048113540c00b6a071003030300d440860000c0041c980f01005a0787c81140125000501191000024580200040c2201c0300204c0707001c01c81c0f28600c14254018018070303022549080c030740c01000c001075411007900c19050107900c03194123030341040350340c82e02507040854182d0400081415401181005450231000503502d0340c0031441ca2030001d84910700c11203080c089e0b0700104d4070031303178000345404c001303100078801c9003004031a0101508050b1003507404521482601401c0f400e11907100070454680e883c84003420040c2c80c0342a12040389010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340789982 1250 340788732 340788739
    0x290102010b0939030a272607050106120510050601050901031a100201020c1203010f170a0f08070b1303080426070503031b0408060105012114043509 65
    0xc0e440c40c0a0f02d403510282d80300300740f0380c1303008110034106040c03904020368840854815044040020b0340030849559446c1c2c1501c081100c0720300040000349005041d4041d1740401070a5600709800890400441c0002d0341c1854403400c201e8142c054140000800e0303c004958542c0005c0041c0941000f40d84a6000340f945851001e512591605058000c2100c2820718546080541e400040b41e920740703941003050760740d442d040d080f00ca030840d418004000800000e6200329840a280c20002212910040c000e20101da40e020f80c402e4901e400b0b074580011550414a0241c81c103052010014015480c0101c0740b42c0395039030541d1420307030a5580f03070303580000c12001c14003101d04160f03080b41501c103591000c001006003030b008000540e00d0b440c140820b812000307040c21005036000780c00c0c4401c11140318000780c041d0641d81c0900381040300c018200b004200032071810019141d0141010f001e030018168005600d40507034005c40000141d042c0b0007160003a030744078a140540205602c10104919402000003800003480000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340791232 1250 340789982 340790071
    0x60207050a0506010f08010e071502030c070e0f01060302160219180f201903020f04230306100320031f05090c060d050604290102010b09 60
    0x5449041c070700500500d00310790540c030500040c440c4e03015000c9003000034050b240091150300c0710903441d0b64031444580304030f079114080035903d210210300034015a90305426240840360050327a184800140c001c0182c07444c02c00b02840800201e0f416120f070084540d007140f5110101031241c1203609005030110100c6101c9500fa140c0035010174643c140e03002445103d0802403011500c5042c0c3c0078480c0c101c0b8540e080c04d01d22480e1640d00e6440d40300c0403000b5503440c82c1e080d414401c1c4130f090b0301c041500644200c0f01c0c2401c540701c0001c0c020402112000b44894801910010110070301070707510a0569500c01600d0a034007203291a02c003000080c00d20341d01031030f8480c58405108044190840030901d09900324408140d00543c03204030403c0e801c102c3c800c4640c44008040208801201a00464000e00c2207030405000141c032040050281e45440d0006000642d9100407181c0709085611680d50105020803114010b508250b0307818243e140000041d03001e0f20b2035800e640030141148091096000d40c924900c0c0307000621 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340792482 1250 340791232 340791247
    0xb0106230301140a150207060507060f0213150815040e0c0301090503090102060c0f030c03090a050706030b100815091b0426150f0c0903030309030901031103010b0a0c0602 75
    0x1110040e5000f489091151100c806903002084142c500c160031030300c0c0640c5040d060b4184254000354000440d601030034070698903280f60a024000d80012001180054000201d240d00d41c20806000b008584c4100116074120703104240c100e074182002d0360603106515040c0075880b850300e0160b02c120107605020040f1043c01a12401090a580717040c80262041c0d000424406084d58050208030307440001e18000314030b013180354103d0907800d00001e061014100340100028500b184c0420403002d030242c120b030855042d5543c1d2000100600700701c600c80d82c0540c0f50702e00c0200d030623030248103100d0103451030400314008001d0303803418004200e500600302200c00d0401e49601142c3c2d46144001d00c041e010304c582ca1200702941200400a4401d10300310394486038000007601029103980480147c001ea00c090346c280d91901c0d01c200800c62405a25400c43d0715010000c188050400000001c04e518002a2814070000840f0680e10100340401d02c0340170340c2a8010450010042d2003240f4044259100e04001400c0113030703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340793732 1250 340792482 340792547
    0x5090307080109080304050c2e20060403142803110309070e010b03040b0402041518020315100c06110412060902090603061003080304150c020a0318030b0106 69
    0x7000b020a40301070800005200502c8020b01c8503011580c0141e92480d20311080c19505c20b90b41c1320000301400c0c4004058275038055107200306900c031003040903c580e0014004a8081c003d849442c1600d08402140d2000c0c4070817048503c3c7d00c01d841902c40b019902c04401264400c0203222030000002441c1003568450110306500501f101031402000b1110091040700e05102b00515624810303082042c0b004024030070400001c80049620794803c0c3e040d200421030aa404007911200c14464010b4145642800346c1001040c1c0729601070761042880303040c01124010b8000602000e4001c134918440040c005000300408107905410003c0004050400c0c035140c0740e030b1402240407c1190400c100c4403141c40d44121410351801c0d500e220b400ca03008802900380d60402e00707600d04001f41e6a00c0020080c1c13001000050030300c031180c52015005400c4900c1441580e0450300c4c02500d4160781d02e01200802d42085000c2850a91440400143da074802c001000c942d013480c4040c0d4100b104404182005007503100344840300d20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340794982 1250 340793732 340793741
    0x80c0d05041a0112030f020c060d020d0902060f180d03051e09040204060305010e0612071401030b04020a02060907090908040e06030c10030617150403080621070906140108040201050903070801 84
    0x401c41300c1c450103040041c60000c3c080301c132030109181194480d070091401c2e9500c13101140c5200c24501c0300180d5584801b40d207238020b8003407070001941c819000b0031012060340991000300101c15402070500801440801000050050400c01a0004a0600000a00d442141d0441540c155140b00d854240507850b4006010b0341d00039001940001e458a0041021a542d00303141600840f00304c0380b814026806906a82e40d40c001489490880380d0f03100c0381c610050740a07503c01840400f01030320965596400034800b0359034100c01c0d12740d03e20764858003900056140b910b118144040742c1c880c810328906440e200403071302d04001c00f8264a5060044402000a96580d80401110051a5100400c5d400c0c6410050303842001d100c2045000381d0000c0120914803482c200e012684207606040015132901c0d9500030440040c0038007145883c0c8280020341080c4000c00080480c100c5000c2c060a20095440c1c240705d213600c0c03610800c0d03e80400e903414003040c0158041e001400c04500060115030a042e940d8064a0030345 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340796232 1250 340794982 340794989
    0x8041b090c080a0207020d030e1c1b1d340809060a0b01050403170702100207080d03060323010f2d0603050303150f090403030b0a0501080c0d05041a01 66
    0x11035948915421060b0404000c42d8005440801103040020700d801040754541409001410001441d4542125035030b0b020703446055030b5020024a001c8440d0341713804181c80d48081c10f480c0003040454000180e40c000c168917490071a4140c498048a41c40b00382c901120141c2da103060b260b48048295400a08806ca058040000c1c00c4a07035411101c4d05002c2107950400c50054450303030f100b40c1407410380c0d0083e0340c219049400702c90384141047c20601d0108551140383c060301d0030013075102013096800189154001504803e594400c0c06030f86c0702031010a0250304980c19403000808200c0500503c4007100c0b1a585030042840318100082100348040304100d00f20f03030062486041c4010035210100c0644000e6485c042845482c0c001004007a00319122035540317020040c81005010780b0140098a02d440b0340c102c03400041009002c080c0281000d18018001d03000d11800d49000c0c112401000410350700c5162500d014100c0c2000359440c11000404c1c00b405400c000300155490000c400f400d00301d02d0900401c07a0b008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340797482 1250 340796232 340796249
    0x10b0d030f0906050a051804020f31030f0b0603010e01020a03150509100e041a15041a06041a04030c06050a08090f0304050d02030f0105040b0a1d060708041b 69
    0x5501d80140090014409900048200001401004a240d821000301c405130000000f541003100300110015000e440307000018008a50003003000c0310101c45000301110305210284803200d40500d0040c1c0c2000000480c80041c110f4403c51503210041000d00d2107072600000b0140012802d0081c8a01b05420380e4007020728072001a980b503040d48042c03c69a641c80c07000d0401101c51044c5404d08100d06410511140100845c1c00e010301d0101d002c002e03a42c84440e86140d19103e044500740b070491610300f4481001c40c4070f05c2c0150700f400041101c0c0d00c2850304000e24403c000300050308090600d5621900e640c1c0711200c00c1c0302c03a8000c200202c041444490031900034201c81c0d403810f0303440314521002003240201a090000740d40c41a9000c0d005074070040140d40903110151600c403000701550000918009000028950300e500c1e10040c003091210400903503200d41b11542d4180b201c130454a50b41408407034221944080c80e00718202085501e48168980e80d002801a0b0f03806107001003200448000c0f542d1603104161 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340798732 1250 340797482 340797497
    0x3042312100c0c0510180b0415050a090f0803070c02060c010b04110304050a12140c011b0c0201090e1005210610050319060e010c03060815060604031202010b0d03 71
    0x2a0200d003405490080b103940c0c58071103003214030340e0340e02551403000741604041c07039407120340c0e01705004145203c0c800401d0f001001b01030342d400c05085c1000c01040040e0358641039400c00000680281e0107000d1080d41692000e1500d403010119280c2c10f0070b45e00050150030821600400140c00340c1c0d20341000e8200010f050340002184007802040004558030880741d4107003400240200400709101095180d881a00080810120045071000315080c0d0f0703c480080c04810008581100240d00540c488001032061141078500241d80a1051712814505400240007448410052125905103030189400c150965a80c3c0006070700c074000500d00002c144d41c00a40c17501c1c50204030410a604000e007070340056074070000140150a000c04030b510340e00b40074100d100354a151960001000003d5114001c0420000003c125424030305000401411781c0d485250350901c60031a081d002c0000b080c040b180200d030300600640c602443c41d981c0320301210041c198a400d555030b41c08100c0045e11422501410030380700f41d032000d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340799982 1250 340798732 340798753
    0x42004091a060406081506180f0f0705040b0a030e0a0501020301031b05100c030e180c040518010605090d0302100f020316030e12070f080c010c09060c0503042312 71
    0x90240300000e02c003911850402e00c1c10071505001041e114008074108011188a41e01c5001082011181247e00b803242c0c1c0704031040140307100b40803004074091040380200b01c000ea00c0d000300448150060340980e9007895010044041481d0003035002c0801d450503070064516001050f03c40c2c0703013241c100340e2095800c5059014236200c0a0308111510015050444020100e102c10880007420012480f00003401d2050f40b410b2140150740b04e91404e2012143c445042c80b0624000c50b1b0110030350003610440340140d0010074000c030240910440d0f11b0580e00b41e9990315040030303001000c02542c01050742055003540a0044940a2070f8202d014200c0c0859650b400545d4030b007810304040d0301880512007034204151511701c01410030790001c500304c4410103d0b80701c000c0c2c4508041c24560191002a80d0080451500140300c40341c82c0010f42041450703103c1c0f40c6444038042e41da660300780c502500c5d07000000c1494004000c203001e814050090078100f0304034140220070303891440c0007007501540c40303001c02d007290381c054201d94 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340801232 1250 340799982 340800023
    0xc1a09010f1b0605181606120203160e0607050601061d0103021314031f05040b06090f010605180d03020f01060506210402061c0608210304200409 64
    0x14a41800e1031410b24040071540c400b00110b031410a900502054603a0302140c0ea0302c4105081c0c0810044540c20345111120003400c0d442114214800c560106203400d002c465205154400c0d00d01c1010812503882916510040c112124840300c0341c0c440c0c0c03061040c011040480d104008050280100ba22061800d094a404040d480030360a00d07179504041c01001548400304400c40c92074111f43c0e14954407114805140006801c9c1074a20f003442205d8100e0110b04018540507401903170150780078903440105a124181401440902201d01c5c0d82c200c2041001045114031400003032002320764140400d01c603080d034000000c840070407844055005900140c41280d80030002c0c82921700802d000c0741c0561400c6c04014240c1c00000503400c0707030000c80c3d040340001811f5480310401c890320034480341c449034000341d6103900040c0105001d008100c014414010b48040144140740c04403051500b00c0c400508695403599146884960b8003149003d851034030074144029142d81c040c501c500c61044011005000d00100c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340802482 1250 340801232 340801247
    0x3060903021920060405100207050a05030102041d090309041406040c08091b0a030507032001300e100903020c0a0f03141f020a02060a0b0303090103090c1a0901 70
    0x21070220b0115010072070008820280c40544000c411081091100a100008001e40a01d0303010b59006442103c0c07000299074080ba07400e041d200101c409400c0140c6480030702d401c034099030080f002442c1141c01402d41e4850100e13222070b8884400400c592030700300c0d4180410281c0c0c66071001548401c2c41720052022a10b4a802001400c2041d480d1004052821030a00350380c070052508426609240328201c21013a40361a0b06110155801c04129110540d036850003503074a803811035100f0215031040241000a40c801c3c00c40403c0403150768008407070b8444a0300d100320300e414064803024286507241c0070b2410801d4144240319598652400000701d144c07480c10301030700344010000c070580b08080b4010280000c003c130102400582e500810246102002031085a01e800242640c0070781000c0d1581510070341d041c040e00240314070041c0740d094030420780310b001500b0f0640e542c00c01640e0781600305121040640d4407943c0528a4107009143c9403400700e654200e003076690719007610f20400c42d00002030f5244441d40c21510 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340803732 1250 340802482 340802503
    0xf0c03141e011e0e0705032a030703020d1805100606091511030f130302010e04140115030b0603040501051b030c070303020d06090e010b010207120803060906190306090302 75
    0x3034118059114212007500c0034050280031800c549240712140140151550070000d003809003101c02aa0400e404090500d40048503614000305181c0c42c1080d0082c0940e0340550b124008011084c19912100c400354065009000764811780c60b5038000304c05100300884000c1d01c00c20b000e14041c00300c040b040c4400105562030743d001501803008003401000b03604612042c48500c0c601c0e503d030405216408140301411442064610603c2e20b0340442c600407282c00b0180d880089034800d8031411003010b0b60105001c240d882d0307117204420258442c00104a07500f0301d4141410040c40c940780c0051400000e000051030380d041a1010342e1181c0d503c1003000039440d44480ca1300004c602500704241540780207442c040080c070503890300408040d004540e60b4143e07000b83d001071016103220a802c0c000302c1d1982e050300d0b009103841c1c0300c0103005101c3e0400008540750704159074940f60ba0010300292030f41d5900814406c04640142440d0342000000c44c15256400303c00706508050f602c200f101081d480c08074100241341c00819103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340804982 1250 340803732 340803751
    0x20721120b0f04020c01090c0605090414011203030b011b0f020406170607032a0519030c02070303031a04180303060602030307121a03070f06090801020702150d0f0c0314 74
    0x24181ca0751049203000788508111005a91072624100782c0d805803040103401481001541404070303555030000c015042c0e0100c280c07020012405600c01e6070011290a1060030094220001601c000c60710a800803a0b4811060400f110b41809902d036002005000c01015030300d540c56040140d00710304c0c05018000c0103100c10b02d8454500400c4102c0280c60310005440e040c00c1c035540381e88a503a0104400d80350b003001c60440d0181d0115010243e0050180d41c840c114020703030801802d4012401900070311900d02410b40383d6004050075410344d5400d0303004005016072040f03000b0300c40c202d8803103c3d551401201500089d6074035454808142d4074000d001c1d0b501b50307084502590024000c108040358002222086c0651005000c00c002d008014006413203001c000e006030301805400c5000c55005640610320040b20100d907519862550f071603482c0da080b8041c480c0000c0d48882c0c1e07080498010456140a4003400120345000119145c00251050032500b440c408440400d03103800d82d070072142440c10b190981c01b11150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340806232 1250 340804982 340804991
    0x1d01020304020a050111010902060d091505012403062409060503040b16050c011103100e160305091002132c040210110102040f08121c0f02072112 64
    0x180c2c00103104018501400b8108a00008070f038160141c04d40101040300d80141c0791560b20317100c014841e006001c45000566010b1180c00000c6130090a52082c10304a41207085032190000e0990315051074803c00d0503015080540380c08011540c0b0b101381555086211980c003c4901e4030050b040007a0012815501840c1480343c28410400890144100c650f486000c03c51103205031294034070b0680b40c9000d42e100307410329907191100007a2000100401940180c14042d00c04401c0c5680c1c22001d0508241252250700c0303618144c0744990103500941040b50020120010303240400280d035400801c91300403144409414a02100c00c10a9128424100c40f28200c10641244d651030080341c0090484006003000f4014042c82c40070302c44a80c411070b502c8a2413480d80000755a55a40c0d1840c4041d01d41144c0241c6540d40a440022030154144900315003801c000c0403414426144000b074a031004000b000d8815012076000c00401000450f05901004c2e0705070f10702c61078442108407103401450505400290449286030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340807482 1250 340806232 340806241
    0x10092309010f0e090d141b160509060607110405060d12020604030f08010b270604030602030402041a031b0d0b0c0a0e040c02102c0303012112111507031d010203 70
    0xc40c0700501d00c006d84000e080da80d0030440702000c01e0301c8081e9808240c10302651810303c203111400520082103400840384008180c480d5810425944103006008160044a20340c0c02820304240d0881540044020423902032000c84d5166600ba003441c4081000060b00203800300320816070010030010404080749080c2200390704021040c1003920401d60100d0341046015424100180b41d00d12417001100081c0030591900d90b02e1408030302a400c20b1b58101d1045081044940e1102c80034800545001d0b03004005189a000f10745021810100c048401d40c0c0184140f203540380801c41660010340120660501640d03034a001a00041211032640c4503544904d00741105080303d01e500168070219030038900400075050004030100d502151030810050016a070044902da4016408006141214142c1541a094034007001019282214108005000380350560650140c1c03031013a4220b900c0c0c061100101c49400c041416240340c251b404440c050002070301c03040c4414907074088451354100188800002d42c210b050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340808732 1250 340807482 340807487
    0x906050304061d011a010801120804120309260105090c0a1406222c01030b0402030a0f0606080c01020304081009030909050106020d080610092309010f0e090d 69
    0x15101078050394480581c0c462074000180000350980e410f1000b00320070f0141c0d01002d15242c801c407003070502240d4004000284086400540d002155020b14010b1500c0c0c105182d801d104030041d20150700b000f0300408007003948080064000130481602d100c41030140280300100e030039601700410058054001140030303131003500c40b106580d050318481007040e40e030720101c0380c040b80b418015031043d40001d40d412805459849001700c206415038420070350340040d03010103003246280040e03547d090500600e500e000410201d4000300b10380e030f00a88002c1c1036440440590f00d48003000340e5000402da0b50f5640d80c0d40200140c10081145500c0002e0a00103541030074a01780c80c00b900d43c1d40351600400d8090311070480508040c03085c18120040e04c0c100c00e08000b55612004002d54406010303540c2400700d5050000b007401d034a00341001e020340b01c2841c0d40313909850781000700c400000006440b0301d84200c504103c0c44800d5584461002d40a86051a10400382c0d40c5000e06010300000080c1920646400500e144000c095 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340809982 1250 340808732 340808737
    0x180603090b151003020d0e0703061508030a0f0804020a050619030b040c0210091e03030204080706090305030a03090c0b070b0402040516080408070326100b04080c0d0c05150a0f090605 80
    0x150f036040040e283c00c01c260f5031030090000402c0000c1a80900c0b240482001079960180c0d140080c0210120701c102e032107a103e140c0e01d02c142c05009002c5550790b404400c080c0d2050003000d501034405042803490300d5031140030a03505d4102c0040850b00d40120003880340c0441c1d152040044200c412201030080e404002c0c0003944981018000882240c0c45069840a101c4048050014040030310400180c864031410700030002c0d0040c0c0510b20b083d0160400c001181440361045005407504180a9441e28a200d10143c00510303c11200f00c1d80d5803c034080018800319950b0140000324000c003204c407020310305441000111940203020304840071604828460a5a0040380070354804d50082400c1e54900d440d0038161059640646000a840c0c4401c200700c1c41001c6001840e80142a511400d1017801e4540e00c02c100140034030b000d10310440d44441740354201403804d40d081c00d4407540503200400c10b154450000c101c001002507041d0103000d2000802500e25580310340040d11004451810720b11031818080000d2062 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340811232 1250 340809982 340810009
    0x50a0c0f050a0f05070e06190902031312020a0209012c0c0909131a010305120d09170403030813050606010806120a14100e0705060a180603090b15 64
    0x28400248010800108010408002e50807100ba0700000c0402e14044d980c40659002c1c445c04c001640700825040e080c41d0701e2100d07203c4618078040b506241003240710002508010681c001162400d1040c03170124050214440d82100140d004c3d05881402d4014041f0700503060340900d00001b0000017080c2100f002c8107940c01e5450352440d10b500302e61100f98600445002d4400000d6100a0350340c00d100110341803c100d50222485001d58072001d940b046048444a1000d02c00908942c10064064031f1503041c0c01c00400c041c1c05101400140e005140e1a42003c030090081d1880c0300400c0010280289034000782250f5102c5020405145120b980b50ba80ba621800040d0805044c05400e0000c00e05694030086060001c00201d407c641d8118524148406220700b2040f11000034018403002c0d203051400c0d4054a1104003000c4000c2060070b20b000213000c896445010b038007003000b411014010003c0050280e5100601c042c2c1e0340410380820070705010074444006030003e49254040040c041c0d06844240c00c50026 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340812482 1250 340811232 340811243
    0x2703070609020105120901050132010e01120504060b040e0a151104051c06150602060112021f080403020c100f030f0f24090e10020d02090a060c050d050a0c 68
    0x3104128801610540504180142480305100030020300d50313415030140c1d040381d14ac041c80b1000c080302240702c1c03488244869001400c070b1075082c0c0d007005654058036003018034580615040402d0896440d46004443c4c00360b03002c070707a08c0d03890b801c400e2010b28146c0242280e035502e1340094044048556144213002c4400840e04d036040c0e0320740a11365168250703034041ea0010b0a01503d4005940c1d40c40c1d1422050000e40e880c101d4980d854032915001210225503140c0507100c00346c0061403a07074240740c401800450b00c4a0b080380d00043c01120f08032000712003c10140c00407a035445203040382c107103480c01900b003000c003400140c0100384841c969404298000e00004a19a4500300012207810041090019109500e000c0c03179201d04014000e031b101c0d54198200b0301d0140d2100d003100c0e245600c80d00000181e59503140c2c80d5a903076209200000028100394001e0030100e070f0b038a030b0052a100c040000b080c0c201c5c4540d484600810031410b200d8090001c14841c040100155281c036a2404096003000340c003403e4001030251a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340813732 1250 340812482 340812491
    0x702120a0f092304062c061c0c060906050a201006120201140c070b13050307030309081e071208160f020a080705090408220e27030706 59
    0x1c0d114011099840a01107800740041040d034049034080c0010504421180540d18082d80040c1180c40780e1a0b1041c058002c0751410703071404a10034070708115140a40201d034850ba8201c42411102c140c88080d0703480c03602c07800ba18681e2514020000c0c084410702e80c0039070244502000442241e5910800f8010b070b4011a2103100312002141c07003036602d8151440e40006400d0300d00307003000c40c10300050703000b4914646c400d91304c8264556550840408501402e0140c21a6610840e01400301c1040c0c200030700003811203507145c00039090b60b8000007480d000f82c503071050700802c0108a050040440c180a1542e03200340419a42481d294074107200c6590b120380d4401c248654100d0303442081001001400c03140c941c03c41a0040507120840e042004054a45d00d9007203101d01244000040c0c030150106622040300c0000740f00341540d65540d119100305034002c5844030300c02e04401403881d09000c0fa4000c00d0024060300d039240c09481ca41100c00e00501c051040c224080300c5c03030250b102c2405003030000c11034001d030b5071003d030204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340814982 1250 340813732 340813757
    0x6031009140703060f06230906060d110a1d101101021e0307020c100518060408010f090b0a0603020f310c02010b01030b180c1603030509060702120a 65
    0x30901059000030141c02000b074000140a1242c1200441c1c04501404024040d5602d01d001d089400d0122442d402100381d030520081454400c18082c1d0005000d003915180224582a110464191803000b4012410100f010a4015031154895251440303804040044041582c0041d54100000b200b000801c4030342c021110309420207405444036032245810015042c0c5c050002c08500340c00441d0281c006214480c550440f51901ca072159034055003a4940341e2502103400c0c0d601c0300e010f04101c1c0c841d40000b01004009403101003445445800a065400002c4800d010f142081054402074400c20020f400d048040c005030b40c0e1040303104010351080304c10100681d01589544c0801c02c54403200f818055202500038400d520701c2d004070f80c4400d020382c000c104030207908006604640001c03203010380003800b070b0745c00b802003d0642941e03a40045144000606000c00822000007043c04448100c0010b91117205004001e2170811826821162900140c500310303207600455403c50052060080c200414801c440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340816232 1250 340814982 340814993
    0x60504060b0a0f150201050c0d11091201050f0108010606022509050906190218010c02030a02060a030605030709021e070c03020a03060c020606010c050705100302090618150306031009 80
    0x9958140000c2d103080c21031555000114a680514490040701c0c1003102c401d040030500c18400c40f4800c21480c00c0c00760600154102d000000c1040740d40c94203600c4000c000c1c501083c0d5500c0301c402c001c120070740008100c81c0740482d441140c4400680c00369005a0515100b803040b660007003950a01c3c0c030340501e416107801103540c01d11074010510750f0007006568500024070100c800f000c94164440d2a00c402c0f441070060500c402d0000f00c0c805c150f024440c00003039a4403080c0c0c030347c0b02d46c0304808198001400c0782c480c170304590005043c9038414400743d00401d566180401190606002c080c00030300080408500b4070701051217040019546400c803085d000c0002414000304039090b00900e001c1d6401070450380400791280b8202004000c0c80c3c19080144c4103250001c0d210b503104209899200d0f0b400310140001031302c0c0c041401103400341803418000b490b17028000c0384101e0303d9040207002e0800d55001c44066844a075003d101c81c80300320740b842c208010010020400142c400150960000814020002e202d00040c10308 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340817482 1250 340816232 340816241
    0xc0102250b0a0507050d0e030a0b04080c0d020303011e121e050304030602091e0102070501050310080613060615090b1309050a0f15050109090c020c06130315021606050406 75
    0x40c0c0d48101e001c144010401e500c9070280811910800c100d40c0310360b48142c0d0075102e441c52020300c0f551691001c0071000c0001d070304204994019120340c00c03990030081c404a6980c1084840314034500140d002000400000d08500d44004001909110517140d0f070381011103000b051880194040d240d411a903031144101c1c151808843c20f10f0743c0003030541e03848946071b00e0000083c2d030140c000700c0d02c12980319904502c000d07508150f2804402d0160010800149408010340d8103800050000440c0c0a50706000200300d4824410140703c4c81c030001a120b10400b85140030421150345070013080c48140794201c1c0c22030242d00044a20181c1d06118044c0d9121400b0407902411901c0a8105503032980c01c02040c800c0c4034045402c0000303015100d41080c81822165003a50100808901c00c242c00100803440c03c026030140d40d84001d4040c50507206940c03a5801000100d00582c0c040c1c1d206942c00c9040ca5802c100b4400100c0c0110000c4501a10a42c540610307981030241104042c0f0015141c0741d5501d001c6410040503610 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340818732 1250 340817482 340817489
    0x1051c05060609100504140a060203120a061208130f0e0c0906090d03050c010b0402160803060a0b0c0a0308070201020a050d1a040e030414030c180910060b0405030d020c010225 77
    0x1041d001340120303030802440c503082442540c201940f80301c451601441c101040c4000d507090b03070b0300450a00d2148040c003150b42c000034001400c0540d40c4c00022440c000380c07480b0856594062004640d4a406070300e06030144040d00d51000d10810505e41d0103000b141c031010200f80d004841450f650703842d03581031000946d0703c0c49028410796004004a0f041e07410143c100c0d01404803450540c001300840001042444140d05c80c07000284250301d8150324480015180c2005160800c02c050300c2820515150400ca141552280000c4000b503131010058000701a0702c100c07101d030301c000e0358070003941041c0946074007030240d00549140d41c1d01c0b140c441149120150f0301d103041250500005005100142c044007449480364814001c0c00d521211035000004036042c001500d200126020f44189000034100c2001510043d005d054402c0703a00a0061080c071050081c068080500101f0388210360300e0b4a003004243c81c008000c00200155040008003240c0d40c3c1c3c01148040c60103041e14062400040b00782c0d03965402016a80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340819982 1250 340818732 340818739
    0x50d0302070e011202030c010f020d0c240203060901080705060d0e011506090f1d130206040306020703050a110a021008061210060e0c0c03030406020d09050d0f0e01051c05060609 78
    0x1000081c1050144c104840998002d500380e070210805a80112150700038141c003c0c0c096442040c101c0d13113070707880b81d0084110f081c080d13682918000100d4556400400d40c484440000c3c80d00030081c03040905e020744820340180901300080000514100218000303026a0407480c0b07403666641c1c09224000310a400000700125007481c0e803401c0948990019100000034081d0300102007140002103400b88804680c003004d200e031564043c04981c0c0d00c240406103012180c004a80203c0103000000010b19180050000107120391a52500c031001300000070000d07031065a030700b41560b005088200258481003480003e942e02e074035169905035034000c00305100091844002c5c044c1e20515004003004c40c0e00364000425680384003409001600c1741d0040d01030502804440300c1490b0002c001003000070710941e005080300c3d039401c000804c41640e55140c150034480d80411140114803ca0101480c280c0d2003800841051400d080050500040c00c003600720710244416400a034603a90404511269505015901c0c0341d071005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 340821232 1250 340819982 340820009
    0x70b01180221040302071a030105131e06050f01030612030e040b060403081e040503030d0c12050115020708010c050a110c04020a120608010908070803060d0501020309070602100c0207050d030207 85
    0x4280c20400b008807410ba005000d003003030100f80745881d800c120044000385088181540d00b044104840711540360000a81741d07540e401e03080111a491158180c00c0e02c911980003c03194617001c01d2000340240d6405203410103250810520004000040380010703a901032400200c1400010040b1f401421080000c80d40711402150003c00c0040d00c600510300c6010440640601e0071035100c4001090140c0d006480d81600140008141036085500a01000f4942d10700303032241c00c00b01e01c0e5143c210395003a0020045a100d1040601200390104010001407201c400200a0b00a000d0b600400034003c00d4110020809410613281d62140700704003802c1d5038240200300b1580c0d442446000760a201c030103030303c954542d4184a030000b402101881460b10303c5810928041c6003034001d85d605441a80000c1609074010b101641c1100841c8013440551b110b40b5080d80100032003402c00c42d020389403900c0d039000c954103c0d04110447c00655800b00d00c04080320000e035510b0b04201018074060b809d12840390411508104a07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 340822482 1250 340821232 340821277
    0x7110409230f0a03020a0206180a0b07050114100b090109170a05060f0403020d0305130606230a0b040506070510090c060e011814030a0f120e06070b011802 68
    0x1000000000c0242420071035a025011000143e00e03810421001350260f0490301c409400f508040000741080300482007450644103000c000079581401c81c1e005003804d0600818004200007091003100080c3c2466001034002d4505103c9181120419001d410050200415a00310a901481c180303009000e081000007051740614085603961851600165135911800c1c02142038000300c00a264041d0f60103a01400c130342c94006205801400010301180d40a441802072100402e60030b11440d005040700c407140c0041158411041120008002d148510800f0300d0001041054051001c9030200d54050b2103481d01c0300c6542c00e02905141400202404540c1800d80c2d84040104080d04da0b0140c81301034490002414681c401181c8004d40c0c00c502115021003a401071211a03070210011008800003002c6030032000c0d4581d2803c4c0720001200048440344410f086980409801601e41130030020140c070b030241041d0307058039418042a410710a0060504160300b071241a1043d980450344050403c44807031000514 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 340823732 1250 340822482 340822523
    0x20408150a060f031101031d03030708040b0603030913150b1804050a0b030303060d051204080601090501050d0302030403030c080403021017060a081506040f0c020d022107110409 78
    0x1240c1c0c030480145020408200ea4a1000080041ea6009000d54503924114001900100040c42c2c103403c0141d0603484201050100700010342c03003084076076200d0350300741007a107007070341c40b054019008a04c69002803000c248103840f107000e800000c5201c601e0205030141c180c0750200c110074040c1c01c024010080061014400041600d56402000f011380c0c3c01c004c1e9036501d5083d1021900403041455042c0c004001003a00d43c03a00f60b499030b1090380684240d6440b03ca120183d15080e60040c0d110044070740013200100a007140c0342c0300321170040409840f9003a1050551703030001c0d264411808020144490920250144400001910090b550181c0500c1203560004000340c0400240c007071401c0c00160840010b46142880e52400044600d06801800014494104e001c0800030040820b5000380e5150038400101e8403034011404151429000740180e01c202c901c0c0281801180388200c848007000a91a01c098900076003101c04090300120588801d440800001d0054000054041c0201a1400d0207000c0d000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 340824982 1250 340823732 340823773
    0x90c090810020301060903020f0a050616051b01020303220c09020c0c0f060306040c020c0901240c030f0e0105120f0613060807030308070903171b1506040f020408 71
    0x80c44803040701c1900515644440c2640b00074000c0300e00180030070700104018203007100c0020b00d00c400181070425083d211300100e840b9410000300c0c0e0b107140301d8071980201441310500951403c1d020000d5001c00c620400b50000c2c3d541c0c400541040204108525000c0a003800c1100b4030040300e5201c40c03e907a1059440059401075040f001c003030300e0b40780100c0da40c0c1030f41d515151179130341041940030740001e05503581e8408010007032501080e080c0942c080c08606a0442c0d0741c0da407506010b00050320340a44224542c01d00b4070b08034812000307400184080000c0410100e908407403102080101031601d0b0003904101001260b090040e0403900d0414840e07182031240118411500d0f41c460b40c416034064241071440030003601070b076200c5e2040c0300040d0040581400420f12a03014250301803d00e040003a41981d8940e29642c0144001001203c42c0e0710200304c80c0000100c82d444615001d80840c01051041101001480780703200241c80c8606c145c0d6500440b1180d12001d230141c400401c0c480050b2144020350200509050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 340826232 1250 340824982 340824989
    0x70c1509030b01050103051006030c0921060513150b0a12030f08070f270b0408030703030c08060108060d21050d06050607080301120203070b0a020d08071b02041104090c09 75
    0x10b0b45803800109295101e40704941c03080c64024254031a9620700302e4190b000307242d0010030a041181480c000b00740c6090110500000b4042c0c902003074035510060807c03030200c80001d48030003c07024481c0905004142e00b40c200c8180d003020240300042d080840400540e00040a41c00741509501892600c000d158104007811410381203925005415916400300300e03a0840450407030004074200740c4241c14a1103586546600d0385500d21100c0701e000f900d51400a0700340d00503a10200b01340d0702c0060001c1c201941401110108046424400002d003031180010300000001001d05d406000048108410b0006081080800540b540955a01d000b0300b00b80081c03656001d04400004942010b40008032130904008503a2025004030314182580d0030845c40d0b1045c0212040142d038144036100b008104070f0b158a00410040b00660000d0004052004010300b292100078000001c0c0324401511140d260402d81d0000c0440398111400140f0a1584104000d140100c3d00449407071494850455181c03070700100080c003035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 340827338 1106 340826232 340826243
    0xa1e0b04180c08060901051314240303040b03190902061215030a08030a110c0105010605072003030a111c050d0606020a050a08070c150903 61
    0x140d00240c008012840120421800841007881110701018107410220312919041c000a1040c045c14400e4074028952851951b20420745940b210600f41001c1803030200d01d040c030b10012280c120b408102e0055010703060300251ba00d0303d00007080c4c80c2115521501d55242d0365a01103035902400b151140030600c50f445120110041c2d540c1d034040c9c00002c1210b2544903580c0350040d00110107404001e601c50103508038040e03c0c400b0480e00400c9980c801c0035501d0220700c1c0d502d01c82100d1510b20075035080508075443c1c170f8004104a9031003c0189506806800c0c0c403007050360302000d172102441801e0703c0b480d03240c0d00402c00224841c0c05070120b6000e030b885a00c04d0b240342400d10782c94080c1441d441800a000640001040c1d050400984604405003042d8401084d1111042d030b1034960b108480c0b0000341007204003068200c2080035144841c4054070b00d4110181a040b5400310203840c415440c00b04590 = true := by decide +kernel

theorem cover : BRFrame.Cov 340647482 340827338 := by
  have h0 := BRFrame.cov_init 340647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 340647482 ≤ n) (h2 : n < 340827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
