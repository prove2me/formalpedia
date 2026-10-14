-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2771
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:41:26.813982+00:00
-- url     : https://prove2.me/submissions/4a4fa7b8-41b2-4f69-81ed-e75c9bb0856b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 498201438 ≤ n < 498381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 498202688 1250 498201438 498201463
    0x30f0601051807020a12050a02100501050109180b1f081f031202031303140f0106051c02060f30092d0102030c21040308010306090f1505040203010c02 66
    0x149011007402002c80101401410300b0003188264032202000c15000000700b6517404080e542e5a55402d41c84000a00d462100d0a9240071146460010040c0d03a0300180b107242121000c28402407400101180e030300c010101036120030b1304501448204181c44c07000c1c04014100e110540c0f9107010303603181e0307030350704072000445a403103c201c100b662400744003180c00d072121140d035008984122031404800c031091405001c1d03554006c59041800001c004520074090103030900300322100c4020010300d4640380003e0300c1603100c940e05440c1d02e01a01000c000b50b48076541240c0e01c120304c06076099034402d02c800c0c00d01c4140d0900741d10302d80c0c03c07100c0c10140040d4083d58480c150042c18100020715a10300d84610820080c1c43c140c80c0003280000500b0f03540c103035007401c0c00918415100d1420310390b180c2883c0f941540540001185102e590f038203040801c00040c2c0c000e20303c01d05503a0030190000310950326143c4543c91121041010700400020071002c8915032981c1c0245220b18400e07402803011240c15503090742e8070309410703c0e070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 498203938 1250 498202688 498202699
    0x60f0801140f0a2303010c0e1509040b100f0e040e0c10200a0b011a0307030504020f06040308090a0b0306060d0e01091209030302060106050f07060903030912050702030f060105 77
    0x3001881d18020b2011084a01c0061880c2c000c41e64813040030b909904003510381c2d01d4050b00c2c503003400010f1600307205480d0f8002c034030300300100f02620840016101100701501c2e4140100c0108103e1441c1c0c4881d4405003c0d141d0140010800031003107500070b0b040e04800e2601c0c0c1d00046002c04600c0d0b80b81880d0040d240d0154100005000039103070281007200140040d05801c040000711102c4803450b50b0390b090140400800381010b4413060b181070412400b1810140c10015444400c6014a40c0b100d8602040342d500030003134600080d03161154400958540c1c0b05144081d1b02c440041004010300c1854001440f48540c01c90380600c18954030b0500b010140001c03210305a03c076906120a10b51b558554102041c130400d202e0000400d59066920f04000c04007a403903800000c2c8042100384109601040000d004d005030b81440d40c1804a0101b90884901c0350300710040215440380e21510400d030083c0c020040265010300c140341e1070104800300410703507040000168440d00c0f500c5000620703a8004500700b810303110701510 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 498205188 1250 498203938 498203969
    0x30c03020603060102100f02040303121107140c030d05040519060509010c020607060515011103090307060f031d01151a03060105030405030408010f02070b070e030c10120f0204060f0801 81
    0x1c01040d6080106a41e0660144601503509080d441c400c1708a007010115006850314150306000703002c80049107585060302d15240e5070001015161040d070341e41650041c40307a00301c030708042070450a0402034045180c06101c0d8280d1a8403064002010b4801d1755000d0b181c618544040b1071041042c101103114020200780100104521544602c0342c0c884841e001038886403900c030040c2e40d480100c58044920410f0108601071b03900079036900c0603000346c040840742d00460034601081d000a0700c94605c0e124800a200c8a841e441d000c69002e41c201e000c0e240000154041c0080c0c42c440014003902d1201d5121009002c0020003103440d107003860740c0600c100004c610032403c41d070703901d80151610303030020f03200786c480784001e000001c1c10031030900550040801c58003000d85c843c2c15916050b81e0700d2001901e020305200100381049600d850010710ba80f100d060403240701e10360500303111080d642062a200c5443c0c0c071608110761010009030a8008008458540e81c94241c1c1c443c00d104101e842c2207080c06443e40702c072000103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 498206438 1250 498205188 498205193
    0xf070f08070807030b060f090102010c080417090d02120a050609011e1104080703060f062103030b240405100219060f0b280b090312070f0f03020609010b03010204030c03 74
    0x3041183e00900742d09000911401e200c00243d45508201c82c1002138542c002200725041d603080c01a03518120850030108218102640e503000081701e625001d10104002041401159640c618407004154014242ea0042e60411000740c2d202c13002454191654440c100c0462a008070511401040d4480780203202c450421040000000e0100c40c0e101440082c414000862442e0051045000075171207040c001038000030210904e8259511948644e035040e5144084003c01c1000100ca82002a0306140000c2c1224030300b070000b02075401d1401d80c90640391440826410441d20030b0000c1c0195901290056481c1151810803039484181040c000450200322060400043c041d4210300c0840307002d5500820680340103c04140c8010110014903c5c0d00c190358003071420f201d8200c0c40311001e00548164140f6010718080071907035505100c014803640340c0c40028042c0500c14241214040346030321a041e10003200c461300f002513507254280c0302c3d03416651806242000e42d107414400c0750300700d81d800f951000c90755107541c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 498207688 1250 498206438 498206447
    0xb03120307091a070b100603050a0204030206041503060f0801020d0e030405010e0d0c08030f04500301110304050d0e13020706020c01050108031b01051012140f060f070f0807 76
    0xf00d25115503000d0199a0002d030504040c03074440c04201004520b104c1c982a802000d441c000b420402140e0300c10403090015071030740707002c035016035031108070301c400310700c0000b100f2401006980c0c80403071011403604d00800c074441c040d0020001443d000e1024000f09403845003142c0c5034400c2d44507080c007180c20420400102e00303001c40300d1170030303140110006031450355640301c414215030000144452030303800040c0a05c561080541500003060700e00034004d44400e40380c01624241c140180c0d4142410310102c3d00000011941100c95009003000740085c0b0000080f02807a040fa50020385003124a40645107598603440e124083c20170f403051004106400d1041e56004070310082d4003590040d03c055400300906420707444240240c038024440031000315507420041101c131640031109042403034241d040609004901c50b110060200760313018045812401c0405d4034094201c004250032540c00b80c002c40442c0310305900085101131040f0840794004e2965610402d0031600e00c80310b00325040c04190010046200f683c0314 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 498208938 1250 498207688 498207719
    0x5270d27090b0315010603140f070f08060f0a0e01140616060507090819060f1a12010b15040905060a030209071812290705040e090102070c03060b0312030709 69
    0x1900340e540c082140c0018004040313003604484042a01d40d41140e400b400c1ca186003035408010480740301d00500380070000602d2030f040c0c4500742c810890600701051099440f40000e1140800003400039000303950704c650801c4040b03c244214586001c0d0307400080e0403130900b5821220441d428440030249488150740d48402031101030008801c02c44400804100c0000c208401391003009050028440558546000c005943c14460101c40c2241400c070b0300c90051040701142d841314101290100300d400401a100c600500d881ca031490b030311a501c42203800b0f014026800400994002e03000a000607903c0d001485052881d51000a4000b0b00c06000110a076100f10a441c0d00c000c010701410030101d07500c169210840701c007480e05a070292a800c6500701084007900d900d03480d28000c6506201e0b546010035003d410303400b50340b0401d0707450103800001a004a4080d8100c88505030301c1015419625260b0030310f02d00a0020f2090349010348030340d0804481c1d00d042c0c10252803040b041c6507502e03507155041c0f41c010082240d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 498210188 1250 498208938 498208961
    0x50901060c02240403080c01020304170901020a0f06020f03190f091106030a0b1e18010806011806050303161115180d0501090303020a1803021305270d2709 68
    0x10a000110006d0300160003170000c00008000540c0300d0405082083c0c2511102504c0011400b007007108021598010400b003040a8110300103400403892030070328001070300c038959105002100000401c24403003801d043c4e461081325a80410000d04050007014011240d80c4040944022440c080420762849c2120007182d000e06a20f2001c070ba0040144042074440f4500e034414000c402c0c604000c101607003404e120b000b000d03c0e08440d000d21f1a5140c25003050b1150018000e001c80700307901c8805608000d001d0b42000000300b2014003182c0d525040303881605c1403110310301ca00310b518040441002d122803425543e0040c81c02c14254030707589401140010917004000314a24690850482c2e400c00000c44c1c800c0c80b03681461402500d016a55140103c8020320010051520910390024100b003840541c03038040c59010125140c00300003440d515000d40c503c00c241c40c1c5c240113200700b100c4017000b0b5261a00100f09901103d100ea2140d4a0341d02e00500070445443d45d900c08881c0c0945a82e03801c1140d828543c100b000b0010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 498211438 1250 498210188 498210259
    0x30a141e071a2a012f070311071221030e0d180902070f0b010605030c030411150304150b010908030f250507050a06031404060507050405040213050901060c02 69
    0x207410300700706155062801c180340030517591140c4850b004007100100c0e40030a241d034244007003501c5641c0c007001442e00800714043c042041c40022150742d05400c2024402502c1c840503c03c2c40e9404a10380040c54401001614425040a00e20700c80854040e015081050107204c0c050001d28100e41421610700c900d14080d14a68a400b43c40003404810354801400740782e01848a00602c4081800c0000c7c103820f044e4081400c1140070030811080188400c2620b401035440380811044105590002d941d8518500d90407420000000c10f00041128a107560107011035058024030100319000d0054802c10b0380e0b449055000d4204200c0c49480701d012038014030b0b44803460441c254864000110743d80c50301c42591400c5426501242c0305106502d002c003004002400180340074440050b50040e40c0c2000030b4090801484c4c10388400210301c48901a0042e80e000d041c1c080c100319190319040b01c0032104254035202e140e00401801d800400c500784150200c4031000c1d00134101082c51415500c0103800805912201e60f040d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 498212688 1250 498211438 498211477
    0x150a1e1a0a0c0f05120a09090b060913020309160611010522020103020d15150219150b0d021309110612071b080f0c010b0a0f050609030a141e071a 64
    0x220200c000c3c058085240d5907c04c0030324101002e06084400c0501468800c4000b401100705558600d80e802d0008021503402588917121903800c03d2505056048038246a1024034001c121941d01c10000d0500060101c020300c440d0700d80310b429103041f954403584440030f000441c2c000c00155000b50020b054402c0760013400514034070280410450307034409030080190380b501610740144e216070400c841c032660794620001d00c1c0b070a0030690340d00511801c41e000502d0b6041e16002c0035151580d440c90010020b6801800311240200039140d40c03c01070083c0e00342180c804c55041511f603800c0c1400001d440b40e01e5281400c00700c40303480b8600c041c3c2d0240d090b00c1c000240d802c1e00500900c00103401170040c18040740d21a0307a1988420201e03112030709503420009603600800c00301c40d0812040c86175030b590004a403010386006940c4ca12540c00302c8c0c00e00001240107131180c12403440c8603041481c005002d411a0481c0806a00c03010084030700c058541519100b2172501d4504102c0c05030101c0f00c03040c002d00300f504411008d0980c0303 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 498213938 1250 498212688 498212713
    0x90503090d051005041a01060201050c0d09031809050a0606020f030304060509120f0426100b0604030606080c0f0603253e1203150a1e1a0a0c0f05 64
    0x44c0d03001200c0480341d071503081a80b00714168102c1c1039a07000d0700890000340320910304601800c03845c1c0540911064100c0e01d0340e0b600c109146c0140908268070f0314244c503040c0c80d181c0341c20090010300b600340e0711034504500e0104009280751000c1070184c40026440050341c81c50300d4a03200d28000d132138060000d01c4503010b41206610f000c00014018040c1c072050741c0806455901c0c2c100722101d29590002c10850b58454007035042d1441c20b000c103820741107540104000614480b1319001ca1000d0203245c0000703007a5450141c0100b20001d00240310411208104d50082484104005000c60743c00b050f6a0345100940441c62001e03e449251100a480c80451400d032405060010b01ba400701c0006040c0a02c9280c007810200c516075001106550765001020014802071200309069910762200a0648a90f901040003e4505564444d080401000340000c006c000300492902d00043e00540c0c030074400f61074902c800c00072040340d8050a450103c0000c0d01e070010112900e0702c444181240c2c0c944102e406010303100d080d000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 498215188 1250 498213938 498213941
    0x30804081e0c01051f030348050c01030b030a151d0304090b180a091a04030806030706050406020717070506041d010608100b1608180f041b0f020304081203041104090503090d0510 78
    0x940790381c808c10b80c440d540c0c0d0070001d0501000d034044604050501581d00d100f074600041c0d90014541c0001070140103050081110010013681710810b500f82410640f07207884100010103081620304150040001404500c2008591548151500f0840c0c2c4801d00140c2e05c01c440c0d46c0140e10242c00b81404511051914465003207401c000ca500f140400c10500500005090411031000a8685070504500c1d00703007003000203555a0558802e01303039603e480a841c4000c44900b4801480202005441c00341c503035450ba03468070b24102c60700442c0c0d9000825100005030315881401040d000c1d000c2000c031125130030b051020705d01140e4803042103103810b101943e00034400590104020310003180c07001d80740807022134030804100300c0904005069100e6070611060051800d22071142c1d01c4141440d080c000264150303441c0590960256501c00b154038040c01600e2110407020074021481603100d80341c81001e0aa02004010884080c0360001c0d10503403007404a101039003042070b034035212035003e8003c6600c4070040e49900300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 498216438 1250 498215188 498215297
    0x1703040b03190f1a040f060b0301080a0b0906060d17070f0c06140f09010e0114070c05040b19050609010e030604210c030804081e0c01051f0303 63
    0x2001440c5410128064140c648540190f00c0301000c41800b01c040440da0f00c880b01c00c54111203912a941d10150901c02070300c07030790012000300702c142c094640742d6039198801178440c0003900059459142c01c50004959520208915105100040c24031580e03880644841138607200d40300f02d110408400300300144c085410006450700c01303885071103590710090400ca0002d020507140c101885401b28140107a1903200404001c0d10001c417000c1c130f440e80b419548a40100c40b84880252146200c07600000d004e02800161046e58041d12800d40382440621100070070301c10a0080050b16407051118003505100ca0b1518000a04c4a2101458118030690840001a0501109440440302d40c009628140301d9002c00c240c014043d803e10341050701064006840180400c48003c000800e21040014000a404141180079a0001c05010343c0350b01d445061300303164001d100c103941d10021044175410b034006c801e9002843c03a09890f815503c01d0811384003002680110080201e001902c48811052801440361070384184 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 498217688 1250 498216438 498216451
    0x20c06040c0302030120030c070602091206060f1807111608030309010501060507120f03110a08060306060a0f050105070f02030a050307140c10081302030f0d0809030a02071703040b03 80
    0x207080d06403862041500f105e5032150f81c0c440d00b40360f040c42c1c1c85111200f032094030752000402c0010340c0e0302d01a03458408000d1003441c540550003408000090041ca4000a410784070ba42e051b10800201a00142080003405407210035001800d1120b000030003240c4074031024200780049200f1503c0d0f403000b562078a0b40201042e00004480c0d44040200244a5000d0050600410050421174a09101520388400000f03071b5000ca201480000720120340c0c842e01ca94814400503c5c140310040d01c41d210f40348018078005c0d081d43c0ca14880c0c810480491010315065004400301c410396015000c0d9186000010365030394200303040a556024540000c2d0f005a1000c0c0400a0164400c2d40038613507540d2546044141d20061481e5800241d20205000ca4181c4500040c41ca4040281c00d102a0700d5440750001035800708980300003901801045401c00d11454001030710040b10100c1d4885060702d41c1e46203401e42c0e89000e0008204010792000300f0800041c050f0a41160403014a582030341d2415031036610300741d15503005403142c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 498218938 1250 498217688 498217703
    0x1a01050f120a082b09031709030d1a13050c03060f0f0307030614010b0405030a02040f0e10020a14090d120909020301150e191e05090c0c0123011503020c0604 69
    0x2400d04090400b00c1079034013a041c1d280c200401d1155441c0182020102ea5500380c0071581c1c400802c02200c010000d40d0314141c00c502040c441040c84400340846049101c807003601545524183e1103010741c040c00f07440d2145811591303070307411a520380c0d08109012800d08076441e00801da220403403646803801d106040c0954062030022400d940307641201c00101c581680180d075040c1040c0010f0080741c1d000b085041b005d54044801142c030040820303652005000688080300c0a1080c2c15500301d5201854000c1c03d903608207500c03044038081260484060742e10070a5000e5901c051140d40d078000007403068a449203c041c41c1d261044000d610f82400304102d9000381c1100c1c00030311840c0745290559030b005d413038a4064a0b0503600144500c04070800249501501d010b280740100d030044044990406020020000303010042c000015030412059020385a031240c01c00403184e5080504818014410020800b69010301c8000301c0344603880e080011300491400310000041540800014079038140400c041c0e40a01e005495 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 498220188 1250 498218938 498218977
    0x13020d02040815093a0306050402190905060708161a0f010e10150806060906180f0901030b0a0b0301020d060e070315060530010e041a01050f120a08 65
    0x4d0949484002e4620079002c9541520f1220704000d812120860907070b50213144805101903000640c0503084a03002540c1040c804508041c20782c50315043c101009896443c0c1c4841c0b1600c0f042032103102d1060300005071001104120b01e8100b2940040300c00005805910b1412004499980e1034940002c155013040d04603894800500c60440c0c140a542d0700701c04c5240d5541c142600d80850a0ba18507441c0c0c40070424030084c5c0f00010415282c0310203c401009000b481c140c0d40e401c0b4102c2031000390001c4851203004a28001c000c04240c1031845410341a2074201c96403010980d1003611480c00303800032608254265400780304901c44180f08ac001e28015003442c000c03813074640c90100c40060032038560051440a0200f4032a04010840c2c0000444a0054030150311a402040d03820702480304c003a84009a002481d40302c000050440038080341c0c1c1d40120702c10582004184400a24200030f004207000700c42d801400340e04000d1461a20f100b01c594000946001c2e1a4904015110041960042410309031002e1a00c0d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 498221438 1250 498220188 498220201
    0x50304080c01030902090711070e0c18151903020d090606140a03020906010e15032e060206150f1305180a080406180803030106120b03030913020d02040815 68
    0x1d0546078442860100242e4000340c001515100015140c40140015243e080c18010018443c1d8409400b5100072200740d030810a6126805074084c0075104455003024008181034940f5000070050340d0f45000d00d05050500c000c41500c298001d02c0544428950700300440103803503440380140c5030081c1c02600b0000e4401c2c82d080e26880600c2c240d000c0304d482806542d0381840141d0f2420407198000c0c10070b00c8c094010785000d02c00b0038442d00b6491500400300001008100314580d8001a05c40818007400b0041103014015400d018480e000307015410268000c080000d407800110180b007044010002c1115807040c0404010a1009c0c0924829015468481d020040d20580020b6025440500300009100307041107612898403901950088004001c03c3c2c5114030001900320348204003400030242541e40c4d959442c0405403c40310b09c20000c2103001d00305607503030b50140780c08402d544500e6009080821501c41044a03071000794088c07040e07080f100e5820721000c030318800301b0443e060b00d900e2007001c1c1300001d0420740d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 498222688 1250 498221438 498221443
    0x106173c061501030203100e1b040306050105011e1706040f14040b180303150a050306070c1a090a0f0309080d03052401050f070303090803090105070809030903190f02060705030408 79
    0x401010f052500410070301504841c42d50344801100d06125900c3c5085e111120b1840d400007034164411480d01005c80c010050040583c0901c2c1242c0003621040c21100301645802c07202e410945558000c01c8031005401040025a0725156102000810000302c2d04451000c444c21111f4044000c2c10380304a4504000c2000710140a0366040b040c02d0f00c1c0e54840e100034401c010b40c0d81c400240414100f40f114070341c01c600341d22039840907000b800000303003a500c44ac03a100b00020101d040c2864141c80c0c101030205d000c440038420f50541d034042c40c8204050200c0100320344400c00007560301d05045041107074002c8001400f00c000d008640168200f0b070f60110b91401c103812544185103200c414141421355208140d28260b81180880d403140b000482c050341c59211504081e002002c0700140544420000410040c08400c10b512040c0b01e083d09484460343d0303031208151a0350b24000e03000015056404803003200465142c0d6007880b501076204900d5000c524110342d0121385590403040741140c41d80d0001c02e0503c0629003e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 498223938 1250 498222688 498222721
    0x150702210a080a1107170702060304030809010c030207020d0809011101020409291c05120307030207030f020c240c0304090605010915090312121109030106173c06 71
    0x2043d8052007031030a50340d002c40d001c1c42402c0004000d00389a603802c41c240032111040e101d5440d001028192030b89050b0401920712138003221181c0340f5528049500403540d02920a4903809500501110341045c4942d5544030594841c0315110705010a103403015561010900060010b0b113494440858184504400d214548024010030006500030580301803070741c0c5461064000000c0f03404074011200381a414800c0c2000c2c0c0d21001c11303401410000810007403d400d41c0080005a1091b921800c0c0400c401004a89481c1c02c895041c3d403081c1400070449204e4641c1015441c0d600105544a2804648022041ca03540c010340c840c8005644400d820030056800850752001048c91000304203541c5821000201410341c140402000c18060000d0301c0213448c8600703844280f40318001003c0103682410608803040e80c000a0701c4030722940c00c01c40b02103091204c10701001c1a40360004014402810503c04c800382108001c0c0c0a06101c50503c10203400d42c903400030615400c0301281028000500700a030b804400c1014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 498225188 1250 498223938 498223951
    0x61903060b120a0b06040506010917010203060a08060f06060c010f180204050903030708040201030c05120406061502070305030712020f060c0406030501060e0607030f090b12190509150702210a08 85
    0x8401c543d0004074010344031440d840030044400142d01d030744180058a0381e05032500113001744090240030310385038041507000b5801502c0483c0c0c41c44000307a440c509156161000c850a1301c520080b0800314990b418444050504203800c100007042c614012440f03001100c1c400022000456007100380b04055013000c1c4900e40d0405000d101030340ca14a0724181c0070740100c101500080c109940d480304801d0852140094070007072003224880c0c981909245c2003600140c40300b03000d90303001c3c2150310003441051400000e0100440b980080514200195911442d400c0265004141c0035401411a05081800203105080c858041424410380f540d0a050340201140c0050b0080310901c1008200c1180700d0380c40009840310207602d8509100e8103d1003001c21108440e041d07206101d8100c01151642c01840a924680c0c8202040b100509030824070f41d496405a80e810b650040868001d4000350781540038140381140e00040324011544048071501c0341d04a03804205447c03076951000420300300790080c2d12540d100e80000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 498226438 1250 498225188 498225193
    0x5060307031a0c070b070e010e03060712090213090302060702070510140c1e031b0c010503010e040311060c0304050607140d02090a170303010609170c0108061903060b12 74
    0x80c1140d480b14086018104840d44440c9180d00103600d52961108036100940e00c01c0710300c0c00c2420081005401d860a000a05000c103400c0e40024016040c00034001c1d10940b55030340ca80203850300329110320004040b80f07601a40c10003819a8aa03a40328018094070454038400d5006290078641400b000303042001c1508851b110340208220b886003281c1c014108485003001030b80a5548810030444039141019143c3c07040c81030765000d20810441d103c04800750004000248105108415000e1100c1e141e5041456050104206100500503404104051030707000b4824141032203c94000c0e0351312490b045040f50444114100002044104001401101d4000400d424081245201200d40b90300130b000b000b540f44601580032660540550b1440440c000901c2d08121081d294000140001c0d2241e100b4041c40d000f2426404c0001a040361034500c4c15400240140034007090a0803c004564501000d4070302680604c031862071401029041d2080d900461040100040c1a500e1400303100c2e04816640c3c2a01c09034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 498227688 1250 498226438 498226453
    0x23109020702060d0e15101a0306031002090a030f1b0e0411041802090406020304050d110d0c020109090e070501021b0f0906010c050d120f02090d020f060c030706050109050603 77
    0x42c0c070340c0016124002402480422000c40780f806540c40d103421101043c0c40c00c80f2806c1413000341c00308541c070780050320301c50784007100300d01c0081004e00d2942c03005450b0070350180d000c128070501e41e501c198082e00b50290001d00000d072050303980e00c1d201e10a43c203004095440c11942401140c2e1b460540c48210700610320410b40c4107035890541c0b62542c060300c40c038505030301440c5c03540f0301d12420700c00b0305101000f031640c002c146010340c0c00c10b810700341d000307400440e401c880307920a9201c402c1b503032409600b81c400e03542c4044000f01410750001c0300480f08081c0c50321003241400803c080c0410403411901070250021401c0000307103c50b5241400091031b00c00a8101400c034460884500710240c2c9580708200b101031025206003120743ca40c940102c906801100000e440b0713001d0788940741c030440e03400300418025401038034080c0301503d00c40014000f00d03c103442c240396016410358401001418000d04182c00034400070111410544140001800e55010680c00c9a9659070340c0010300100002e0702c922a0003c1040c0c0c02130013032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 498228938 1250 498227688 498227693
    0x131202030a11040f0c0c02180103020a2706060c0303110a120e0703171201080303010b070b070c141f050132130e0d02010c08060111010231090207 64
    0x9900c8800070180c503808111009240c0754840360080c01d4001c500000402c444205c28100034604e80f040c0100b24805c400e45551244030404601e038103030589030002c05c0400c29500d414201000d0100d159170340c001c100380405441418543d0780c410706005184c0c0e0340300c04000794008c1c0344c014111213071620620300050051204102d100e5020b0020b2036640c030300850008002c01c1c100381e018585007259000401203040c001510034102c08001c0075000100d54060b00c00400d980718494603450b40001d001c1c02d000e41034140804808a1500001c1c6a0892288d0800305818942ea072114400c0001d00282d07100302e40e00c0315411140c0d000c801e100da800001010301e402c01565040000340780f0903454085100600c1d8034034180e018019621041c44016811b401403c3c0b400c3c05195510302070240c54054200240e034000e10302a00840e500600034000004641e60792031500c3c1c4e0310b4000542e030440746206901065035092000031081c224855240c0352050382c00e80e0f0517000d0100c0c0c0783c11040b000301682000403250f00511106e0700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 498230188 1250 498228938 498228943
    0x10c17101a07020307050301020d020c060a060605030a0c110d0306080c09061503221b06020a050a1e060504060e0c1203090105030c19171f0e040c0f06020313120203 72
    0x41d641000e0040c41d0303076020180002450b080c41d6401c00c59043d440000d1a41000302c0fa035004003412818a01501c0c816034503502c0000840380144034500114004200040d00c81146a00503451025103041a881c4026100561032406440049180110344e49200500ca011401c000c503100c0c1882c1241c040c4420301d484404030341240f40c0b001d032558094201101055600140200502c1d845070460802c02c00e08000e0b00706004401c81460280a07031350300c43d1001003180b6101082e8003040c141c00000a01822000c0d0790b501002c8065044030315050019107180303600040c010b001e194000c1e4011400411000840b2800600b002c40f03c036040e6205050154219a2844010050700c46c229000d08190761a0303a1740e405119098850140704a03034112454400c504071036003206106501210082d414840ba80d01c0c09603008108900205d09200c000c001103003044040e12030492150311600c41c0070103281e0703190f48650703445070921150803641c00350b00082010482020501c1d50080140440d020040c1c05c000a50086034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 498231438 1250 498230188 498230219
    0x806040e150a06050603160801120b15040b060d090c05010f080103080c0703080c06041205161410050709080f011a040e070510051e03040c06050d0905010c1710 70
    0xd281ca401030000074107030b20959201100510000e410640e40e451301904d034010140580944078007290a0f4000420340041d2021041100355000c40048000e031545080c640350140e104000e1039003c1e4540c294450652156000b0b04519505d003500816a03003858608800480078a401c010b0402515035038404030300e82c1c01309203103044075000045c95581d020a9049207003400c0b1a6000500099000107404401c0318002901c0b80c402d500074181d2410700d01002d8012202c0340305506100d09248150401c10000c148441e01a268511a050443d41200d02e402041c00c19203004440c040302180c100d540400c030307541c010b0103400521000039001300540305654224070a03105004040901a554610401208400811220340605001009400c44d1507186400070510b038040103e0040300c9901c102000b1a10349004196801581c0c00401240754509202d001c40e040d070030411800008588030082c1c40c020480038403c070340345007180745c0e2541301d003200100c071484d41080058080b40c032a8410901c104010400d400824 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 498232688 1250 498231438 498231463
    0x606170a02120609181c110105040302031b0a020909010e071208031302061b0c1c08090d17040b03040204140f15030708030d150501140a0e04020d0f09030806040e 71
    0x505171203c801d806450118100d02c15200d00c10b04542004e0101d240c803a081007102c0b10f90741c13803c0701c034501e01001e400d0700c10954000b80543d0081c00303a901c45002458512071820603102c110342e02e894280e0001408002c0540740d082050b5500c408220310010709015a070040e061011200010071440e0f0358141c2d8130300c4010034400c6103500300007000c4115070b50f071412105684060010b0710208581189015126030b49415154411640740d001d040040201804000d082508030440504210507a4284242c0328002d10742180c0003d8205a2200b0341c200000150000d0848010026202e143c94814841124020182100c103c0030b0740040007104c004c01d0307020344d600c101c040210040e410005400320749407141c0c5400c604000d00001c03a180246022650000e294980c0c41519007100c02e81d61401512022110704e0744660b031803400c12070305021034000d000c043c09040f4040e00051804801c4160b80c0220b40440c844d40c803410351110404814580e001c3c013507940003013040b60704000040c0f2110000f6590038040406 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 498233938 1250 498232688 498232699
    0x3090531020c0604060605490f0501060603060f14040e03131205060a150603020c070905070c0b060f0f13021608030403183203010606170a021206 64
    0x5048000c1540c06035011055414212010350403d4a004406018180030700e40c0a03980c00c5030505948030b8202e40d0907130b900d10040031199103c0e00741d50381c1d042501054504148048403050364000001c0c103040030903c1e600d000f1400000c0450409034003d017626041e500100e00e0142082e4240070600c4141200311618208072000100c402d0f4804025065008170210300c2e034030483d05400012100706205084030410711031010f40716903548010040040351006454400c12003500b060502c1698040d0740103040c1c5415002c22a8076103139850a0310020358204941e0000020395149000e4200a014045242c10000803903c0144621764000425072840c52400c00c140300304e43c1424101e1110a00c0d604640316034500e0b25075074072020f2590501c28180c2d401a5400c0f030020703000ca000d110449003513807554004d03529030f88107803044a606000070040c0d50140c0440301c111941c031004a011140d03800d10500c001010340c2e45480321660b002c0300c490174070114000c081c02c2c4064010400947c0c000100c103115548404111407 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 498235188 1250 498233938 498234019
    0x9010e0414180709020a081f0302100e210309040908070c1203080f010f0b030603011b020d030e03181207030c32100809030c010f0207030905 62
    0x402400e4603a210361000c003060010b1101c001012a44405480250021240300e01d0351003065004a2055100d078500003007120000c1614500070091020349002102096014a0f840e82c00055209000c031f420700340464201028800103060602002100c1d000e030f251010207010041c10035940304d200e2106d105124076540c030801e908016201043d2000c0726080401880020344800303040f00c0b40e00112303400380c010600130390003d0a02e03070300c0c0c6074014181c4001030003081d82140740003406c603400c0d00060b040315415502ca00b907005080880c41c1111010003229401000d0710507800d140982240c014100d142c249400030401c000e4071085240b500012018291005840b845415600070304204641e08000d2511144510005000c0c90a540d000c3d100610600701820305102840070f020055425880300390060030315103201a0b020301900c119540440070106a03441c2002c1f1104140c04c59040e40010414280c0c0820214145a80f0050180c054002901d01407110b0003450461200c040c1541c9000d12807410054 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 498236438 1250 498235188 498235217
    0x1a06030a1707080c0109022110050a0f1506091a030c0a1707051c0e0a0b0601030b04060e04060c0f210906060e0a0506010306050f040e12040f090b01140901 68
    0x14111501a500010760355140c5151484c0280039050b5040c3c107031b201c0d41303c851010f0740092450724502d00c40b1010350001c2555081000070b0401030100208038580150b900c0c0f08078000c0d640f0342e000da5111211500400c2c003006050000207403181d40150040094190030300158402182c142c03046130342040c003040540d0388a000031841100d52582c07101c524407002d94007000344804a0b0b0020003600b1301540146061100150540080e8200c609410442110303620244107000410001c692003a0804410714020940f110322002040545109034802000300300c8480422007840b806100b80c04521900f450800007004844170010140002d50651251858035601640c0034207070f4540c0031240040d8004001d207d1503503290f40343c000c03003001100d002155a0401c40091310b19132003880b802090742c1006200d02d81145051061000400b84a00c812141c0d2007441e0b580303c408110341019000030801c0501c0300754010709108a0405840107056214144a0b00d2814085000151000d0301e0329140c003880e1800c1d404004e035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 498237688 1250 498236438 498236483
    0x306080f030d051f0816060c020a050f0112110c01051501080c0f0705011a0f01090b0f0f0909180d020109030203161110020f011a09010311180f01031a06030a 69
    0xa813a020075007483d410300181154012400382512280c1610322404181d0b1660143c5a6284808000703501c07065014041c0214a41b0119854404c4010716042c40105c900b02c030124100c0345e040c0c804082e044c90110b40400810001d00a003644000300c0f50342c090940d030300789002814102014001070941c2d000414010000c5101c041039408a5410a000748903244400900c1b01002700380800d100e000703005034600700c01154001c00781101210440a5807c3c540082c00c91011500d401081c0400c0f09070100300030036113484e0344000138140521a030074148090541c240148a00e4001c5d4049600c0a59042142800129030044165000b43d072407040f010308250b10303a00e440161640c4404500740d0046281c0160342605a00142045000213882c0082101c2c601d103c0341c08110640300e2500d540d20901c26001807000424118503034030750900281050240c0240c090241c1d030549001c9582940c400178036001001402490410b1441000c02207012800340c3c20200c01007902d0b40702c07254000c0d084500b509100c25848446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 498238938 1250 498237688 498237721
    0x406181d060a060e0c0a081803040b040f1409040816031101152606060d0f150207020a05011b0b061909051e07120e03090604090207030306080f030d05 66
    0x6000503610780d440d0045141c002016940101c099503154030000a03c5004040c0898582043c0d0ba01c6101c1142e6542d600030310305101d054044c01c0d80340410f1000003840c040c4680a40003810b854411840010309000c180000c1190440c84988079110303045c103000200b0180c50413601010482c00d0072400910076401c2c140c80102c035004501d0525031a04140c1001100c9030f4900009451940c00342c00d8800b59520000d00d01e02054458060b01c541000c00810080e24001862522052248888864885403601d42e4003c0c0d509008806403040e40015503841149803405112025083c02d08058050840154203070804140c44100145400b00440215a0f640d0314414010124003140c12307425841c1c1d446404041c090302c0c0a0340c0c0c58940b0244c000c0c510312560071081c801071158246036500c0c00292490032801c000380c26049103040e000d00040141a883c1d480354130091029100c0b100000d03a50b21428a0010202d03a51035100c1c2019030401b1640582100000c41100e007040240240425591038200000301007140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 498240188 1250 498238938 498238991
    0xf01091502090613170d02011a01050306032415150301121103010f140a200a090b030411010e1504050402090609091602070f0e010611010f0e030c0c040618 68
    0x2c611200003803000c10705200c2118801100c5c1a224200070425090742626038442d001c3c14155500200a05154410303c0990340c440310060494508a09404108682c6a0314900b140d000e075180c0010440c0d460b00003046401e1407941075801640c0d207c10b415140308140818000c0c02c0605141000303031310901680d10012040070030700500030003295214000017130003816064118050200d4170360004094a02622034905ca07c00480c41040150358150010745803130f4415500401840008070000c15001e0044002d5403065100f60002e2600c0403a9100140c10701245c002c0d007074421024280c2e11000d0021240503541124015a000b51310340c1000300000701d8074002c54071003540094150701085000b0000c40f03000011190307681c00380c0300c1080d21480842650440740c050300700c8913103044004002091256500858a540c500000601000310790398503000d9030040d59849010750310220f1120f80009091000d1400c4210488003041024502003c12a05028601c50403140560300c1e007440d61105e1012101084048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 498241438 1250 498240188 498240217
    0x3030f061401090504091e150e3702060a020309032d0604080304020f0a0302030d110c01050406020c10020a17030a050a05131416090501080f010915020906 68
    0x2501c410340c0444500d26014900d000440b490300c00200707402d0601c40c4403000e03504048107140d8035224161808403c2112002240e01150320040c0d20035913600d80c40740b081100030100c00b5040010300220303428804900d0441519103011000228141c110003581ca51422681c1070324816200c00b106203003139003540500f01202d030f018054401020207040c0c4900c0203c2c1d50300c41d2003038008007600075811000d9607540200e07002803181100700045000b518042c1c115200c040c0b8014810700c807461304d0b680864204800c10300c020010400c4030b40b0030404c090041c88100c104d804280b0381541010319020b0029903c40f0050301050140c0064418803208520038000402d032942c10041e01d804000e0790a00700c118075030040f203038500703514903240100e83c2445550260314040d070924103266429107456241c5902c020b03503110104d0305510405000c21401920000004010115603000150f82c1d0b1400d200c0c0d0341016528940903006901d04132103100040c04400c125901601d2902c80140c448942e003000c00e606118100c5114a82d2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 498242688 1250 498241438 498241451
    0x40f05091e1e0606120a02060f090a0308040801051918170408060c0c07060e0d060506030a120903050c090c0f18030106030c05030c040510060f180303031d0609071203030f 75
    0x3490b000450703e004800580f00c40781c404070002040ba88440d1000301c0294000c100f00180ca82c40e06441c00a041402d4000f4401400315a83e961460800da0040c2d000c07140703603515582002010030b4119450100740c51400014068800396001c00704040f80f180b10020104c2058508148420358402c0a46010f00200d900700d83c6541041030190490f50001480707402248030301d00c40030480d14450100781054078805841d0400c60111a91b40d600501001050b040d09403140e65030b40e002241040500a103018880d0702c580640e203040d41401410036480c58400ea01a0b02d000060081c0480c803c0c0848860510f81000f4944402200701c1d01c40440c2072000c2920f600d0b40c00c0030404000d00490f040164102c880460403200c4a83d010750601c0281c0343c0c102d8070700d24a040c3c0c40c04c0c1044500c1c01000c0e4085031007000d140041605e080b2059846164800d5002038000036a1850011440324015040c4240044440000c000c28601107104956680b080d002d80c0c1c20b02d6403161183c0c41014002d80008a80c0d4a5036141071155 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 498243938 1250 498242688 498242743
    0xa141807150215010807080604230a03050315030105010302060a0503090f150a0516020a0204020d020403060f021e0c0c010f09080102030a0b040b011106040f02150a0c02040f05091e 79
    0x111464041c01c1088403c0c108000070f90b507280040c01e80d0860b82120080c0005640f03a440b50008404075200a40112440310a8103440d804d0500ca5203a0315803082d00c0b200d031a824412012991203001e00e902d18000da160800504c090303074499044c0c1790200254a4199560764859403040d06005c00401c010141d0310a40080401c0800c900080d1071160715401010809507a82040401560401032024400360b006460081d01504041d0010901421a40c0c40545001e40c3d99840b00201c58889880c44030496002c1a102500b0494039810041c40503020000d5040048012600b0b031198268101581070002c00300301d1680302c601542c4c108004000d003078000c540707074507000e04100c1c060300e6100c9a442c03060380703000341c8044158000c26415407840c60341c1c00244510f5a507a41ea80c003602400100c140d030300941c40010401c0c8030006800404c0d00e44400d54411107814045c3c81440151142051450762a500700383c1006004072001640010349161800003911190081c0c61050a0003050082c1c0c064002d802c2c10160035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 498245188 1250 498243938 498243943
    0x4050c030d080915060108061002032a0c09010627050402030a0c09270e01090804061d0402040e040303051305070f0612110313150f0506090a1418071502 67
    0x30850141060307840211480852041d41300d400c854403808111103034085000c60900840148030480b8a00481c1c1c50708910f01303400c03c0e841c10100140d82d5007443c2d206085e5103408007440030802030390055912009035410080081c0c409200301300144d40d20784007c4d90b14100c0403040b15041b4003e00d4050401c550360b0030300b0140300d005480c1ca00c2d5030394085030162400042c89d10490701ea544d82c1284550101418004441a100c00307003456180035042503403503c1c0c0d02c00110b480007000304001c0015488001c0e0020781860118079640003625080e201e14414030040244030000d085269109505180000d55691002c20810084a107040b0141c0715200301e020110702080042d1682c0140c40090b01c0d84107860810006020a0303640c031500f051030b00306082c0042410051454030007501c036441100420001c98102d004c25086a01c05100c1c15189525a81446540c1c02e0810f0919042103c1500500c45450855014111100c4c0900148590b20b0300c5040185511803c0c014500a00400007081c140e08081560003503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 498246438 1250 498245188 498245191
    0xc0c150904020406121a010f0c060608030a05041509050d0f0f32061003060e0708010509100c0507020a18020d1103040215030f0705090103020408160603060503010b0102120304050c030d08 82
    0x255a52908103030074000b80e10100703906c1650b40140e6401d201c10403001000c807515540e46c8011070701140c444074042040d43c014000741081c40c0f255500d654a4901c2c200400e080d050701c0c620039400740a1091024000c68548055121003250080785001002c0114030f405000000c00c81000703400309600c540e92a01c0c1e002d111940c14030328202048030521718080d14650b59202c203010386140080b00040c10342003002615941241016210030700035511101c1d554100315080d11411030702d01d109600002c0e640038004040348241542008c50349441402c00c10a940829089030f800d0050400241c84011078900500c4190115248001806c00074842610403401c001ea080c0c000340c0707089104400203505498200702d440144da100f40c030b071142040c10300d40b503094003a2031a030310815500b41090b8003007201041e41c5d00104095840003030104000045a4540100281101c0c5940c004910a90402c0100b0160ba81c1c00195000e564001d03182150b0b607a01c6038505549001c1c0c0c1131401036058000c003014014266003000e4800d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 498247688 1250 498246438 498246467
    0x3050412140c1c0b0c070f0605091b010c11060d09050f071403060a0c0302070b1f0905071205060a03050607050a03060902071e0302100509030a03110c0c150904020406 73
    0x42c0c407182056410008042900058120488060320422010408000d42660000c0e1000803541c6000350907200c1d240043e44000003507d1180d2284288690002e00300280d0b0300008a4201050700051903000080003408640ca000d86900039060540550381d0307803802201c1e07a4521441d8204041ca580386400303510365a801905074568000c041000035a40300e001002d056142c07000300545219a80c541a84008104e00c0701482d0070150300b07101c0440007811900526004000b40032420f107503215064085000c100d01900321885140c1080d09004640760000000525031000c1e0001050390380d602c41c04601060420351020b02a4810301c170501041940040040150000740c1e41c0074000152030780300d0b1405a1043da61700408925640d0100e40590104041e440c503020304c203205907000e03551001e01d49000d465095034403100941001541d005142d41510442d8405040e007442c060400010341c1c440380c4c07a040480703545c0d4080c1b0040c240118503034020004680d170000c0010401c6440e20b8641800404500c0d418108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 498248938 1250 498247688 498247693
    0x603051501050607030c1a1509070e130c05090904110118080316030315090b030114040c03080c100e0307141902122802010305130b0c070305041214 65
    0x908081400d0311000c0c142c6030b016058610744034496400719400b51208070151811031072000c50040ca800d200e00020701030100c074040d40b8440c061000c10810f2003503015189000340038000705002125100c0d03d00b0b503068a0307d59440064042a000000d42c0c4600c180d001c3c0030360044c02d600402041003038400c01801c040200b84e94001c0024000500244680d901e8040c02c10564014040252200c24104060b02d034103100e450082200341c030072032145401701803941000844c582c444a2040150800f440350461841894081d044070782041e88231806020007501011b01910000a4840d052160400a0840100c1e200400304016007001154540320b8211000c00c4038507900541e00100007040000e0031100f040b04004501044c512983c2c200076108800302d40908041c000c110110529152001c001842c624819584030240c041c07501c001411103100a04c13880b0a001c9510702080881e003210300042e401912580782c190b4982c11410150745034052035104000c2281130702e0000042005402d4034224110b000c504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 498250188 1250 498248938 498248953
    0x3030715150e0a0203061201020c0d230d11090607030e01090b03070f08150d05010221040c060507020d0209130606092d06030203060705071109010e06090601110d0201060305 76
    0x3900010003040d4414007000748018804556000507540c021500886c00924121018044420140c01da8102916098258000d5801c200b401500b00c80d01e42c082010304031012156600350340781c6194038003400d51500b035010368030440a9031484481c0b00301d406803007009060740d40752007061600034190500c1610701400030300103010000f2080120425203008281c00d0702e81a400c00415031007114100c100030a6040134043e1a801e4201549851032405000e600907800540d844541e141a01881104c8000c800d181180100801004c6080c01c141e49040d920b1170318160b40e072031120f400054000700c500c0d400a94480d0004050144141d205010140d40c64400c0d81c09200590707032007030b1404c101c41e08800649188200301901c0800c0e0030b4021000104056160320000740d00352240c01092405a08440709001316900148510500000c1143c90360000d801f203540406540c1030180d4040310110151400380103410603004601168000d405401211844104941514210b010001c0c060b02c1640f0080e1940c0c0a80f00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 498251438 1250 498250188 498250211
    0x70902032e090e060a0e16050f31150b09150702060a0305011403070501020601060e0109030b150a0e0c09040908120c03060f0409020639010c0f0e09010314070503030715 74
    0x1030700491400704005480708091414040c001d2a03603040301c04550001203210b407034004200d81003039003202c0401840ac1d401c0200015004800300c520410300364500b08034a62040103242c600c4c0c021104a4801556076100d0100703205020195030207490303030096100ca00030403101c0c0c0bd540c0c941c0c41113040b1100c20801300541174420b41855280d040c0345c058940113030070a800601c5040d014082c4454811410301d4841e28680e5642c4642045640135103002c0740320350318004048014902034501c0c0c070242c04060702c9051142400542d096007446990400c40c0110348a500440a000d05e000130ba444100c1040300c408004d103007000c020081039104030340300303403140da1820b0302d40d80c640c1000d200318120960302070407942c60301c210191100c1020328a000141c01c100d140302100e41c500c000990001a01e407201c18008030340020043e50182182c00d4203c144002c000c1352030202d030426980d006029045a4002e01072180e0b215080c403249007060003640081e0b805100000305441040862807601d1182404600300304404881d18 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 498252688 1250 498251438 498251443
    0x915050105041406011115100510090b04060813020306041a011215050a06031a0f071407061e06060801080c03060f07050901020115080a05070902032e090e060a0e 71
    0x3d100010900d0f0f41c000000b034240d40500c00d6404001013020480d040c0f1655104d07812401709046481404214105008200030b003020300384441d03034042c1c0341040601582005400da4250241c0c0c4903070002c1145000103d122030b210066144022038015083d10454500790820300483d00c21004030342500000c03680006a41089041d018095540c810303923a840400c950003404000d1310300900584081c41d80c980b0004005191035084502480c50504d20b030f00245003202841488090040c8544284244102c1c8030705603241140031072350b41c654855000074400c1440040503828110019610a05034909000882c00300d41240800e41203604610803502064610405d058503a482a5030043d0b100b4645400b099021780507e016189562042c0b00000e206031407080740310302200b196403042a0030b402400c0c01c001449024032050018041110066140d410040b403a0380c0c0d056440400c04580c0d04ca94449910b1019a004030440180b1025000b4400c000c0d00d143c0e5a5243c107820348240e010ba41c40c0802410300d42001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 498253938 1250 498252688 498252701
    0xd0f0e0f070609270509100b010302070f02091e010902040503100204061704050102130308030610030603050d050c010605090103061401090908030c07030e2107060903151e091505010504 81
    0xc0c2d540d43c0b15840c0781410882510302084803d030911403c600c0300d81032414062007014442d41303400c00185000c604982182003100c120440407810107004008000226841029081e03070241e0640b860071590391641410840c0d40c0c12203503460308940c106d01c00003c120806801510130b41d0400c4040d203000d4040110110105d11903407040c0c05c0403901d40300c029100f0101011015a201e40a50009464003800314034900c004900c507082180c10a0000c81480302d1801d01c0741d0240c04408003400c5c10031415013540c6400d581c03440c242c0c50f80b81c204032000130840c50011007900158024070016140340c01a585a1401d03101a224030194a07118600341780002440b01010301414040c2c5400902c020b285881c0e1001c0c4d51051b6010314015000e100c0c04622041e81501c3d2076442c0201014616043c6e08035503250511300e4103102c403035442942040000f40041c00420500c120b40c402c2c41100c540c001500c20244004010400c101340034400d083c51502407000207104c02e1003803001440c0080c101c01c000981c0c0703480401080743ca0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 498255188 1250 498253938 498253949
    0x501151406120109110705010204060201090311030c07090e100914010525030b1f09090e0a05030d0c02070b0d0c0e1e0f010306090906090c05040902060703030902060d0f0e0f07 77
    0x110b4000422000d031503030303214080000003988040c2c50300302191212401c2e07a02942c0711400503951200340605245e0301c580700010b55901c40000d18030f082d24031065682d56110314060400c41325606e031000b241c03010040100d603001179100001032066030007500700440a01e00c1c0c444000d04650070030000030880c40c840c40322100801e9000c80c90394524240070130304070000c29074014a2508802c41003074980c0300301e54141042103400e140d580e582c42000d0410700c0c070005480d43c0c40d44206803580010196400141c010054640340d40e0400c0c00001d0100b0100401c9203011101d900165500f078000480400b0782000350040c3c21a1079294907181141c000200030302c42c0c2401c000f01c0f2840d400c1c0d020100a441484c00e06000512041d051501140050f1549001000c540d42070f6000c80c0c503281d81d112031400b004583e41c0000c0017014111000c0090200b60f80203d0000c0c85044070090070199905003a0085542e103005076241c2107143c000401c1043c40000850b4020000c130321762002e0034032845194001a00e030000d105801d940 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 498256438 1250 498255188 498255217
    0x81806010f0e04060914061603050c0405090c1b0a11030705150705070b0406020a060509060705030c071a0a0e1509100b04110a080105150301080703020d08070501151406 74
    0x1482c01d400003030b400a01800071161180c5a00c2d02c1c5c0085840c0a00304083c0b01001c001030482c0d4101041d680c200454400d9184050504007010004500075110594045071410b46040d1106d944052110015204941221821011034907480d58841000900c0202075071081c0240d200030141d0508159076070b001c0c0e01c03c896004500311108030740102c482c009003440910480c12501541d86404080c0319580181d0400c1c00107030700c4401884c06008403401240c1c0c01201100103854a810075074001805440020455034161000081d02810000d4503000c000401c400c880c0c02c0b50300d9045c05030320030b406000100c0e410f82e40d600c02c0c9568489002800d01070b850081c1d1060000300345c04056415800050200c3c0e2090303a070301966a04800340c108190b1401084840b0190f034a8038055810507040050786221a0704640c0e00d0002480140a440c400091240549030120341801020980d46002c120038070a1000045c141d509211140d986030b80e454000303c00b900d00c907007040d01602000340c00b840301c04d02448400410f500c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 498257688 1250 498256438 498256469
    0x3060a0b1207030c1803080d0f02030115050c1002161122050a0b0913031704240906091112030702030604060b032506031503020108241008180601 64
    0x243d0082d4407070b0302c40400034109002110481c0e040780c00380711029803007030b108064000351145405000740320710341d80724079203000842c1154109030708000d4481007007002c01c00340000010001c03080c60080140106511042100390741c3d41811101450f030302000040b0888115584084404031752030041f40c1360105a1051522501e060081011400034120180605000c603950340341c04c4102c1d13203d0b074007030601c00c3d949060902070655892500802c0031000e203819106810303000041c403001603c501c00100086600c450841081d00b1585c40400051810309401020703240742c007070407400b00804481380043d4000122505111840350a0240b601c0340b2880d40020350681200c000078002458542c080c2030710400280450300801200c03a12030940c2c8208000003104121a404204403065250180361400340a1041940c00c1628590000e1f00d00b000280c88520494404074040c040f05940f81404d15500d4070040261420005020303025091000a50306142d2001c0b080d901e91045d0303400019402d048412001000c01c0c0d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 498258938 1250 498257688 498257701
    0x7090602120909192009031510060305071404060c110405010b090607080702100917070608040b060d0c0605131d010b0c0a08070b060316030c061d0301020a0503060a0b12 74
    0x54213103600000100c40c2e80e0740c02c600d2840714821590fa0803984030350f030783c2591807229604252a08030003680141042401078100000102d4500c0d0388011550302e803e022a0319100c13050291602c60000c234800c40785000c0460006502903001030710f5180240201642c03040c0803aa0000d10007035450074011855107200410095100b4201680100b991500440c4e1a40c100013a9500080c2113212101898000544951007803001c3c0c0c4401000142403d0008001c00d402854450050501c0000802c09010620b04e0700c005000340c2c45070b01c815000d503036114461003485c43d22140040c0140d0800e0480d4000c40e0718501d070206014880405201c00c42d108081030b1441a807034140518110b0380141e914090500805000400043d0702c50040c101041c4501542e501d185420003c0c5881c110480c0b0440c5403c0403984001c02c003003650105410240d8441d032402d10401000030203120458100e03114100c0e0190310020f1106119035001024601a000031242c890800d03565603d6400305000b4030300000020301088001c80c05c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 498260188 1250 498258938 498258961
    0x60424050d030c0203070e010f090504030e0d21081611070b071506140f03031309110708070b07020105160f08060a05040c030c0e030304030c0e04030207080607090602120909 76
    0x465440b91421103212005980072a0904100f075000340001081075005010001c0d509030003901600140104000c03a10302514010718070301d01c049075035000303100005c00c020500940244440b8010003010000000e11600540100102011200d80210854016195600034880c2c003449a8802000d0000c180c0b01c1c0c200902d0704010f03070202c44e00b2039489070200c040c41001d02c0c80c0d010342c1e4014050505190500d140003000d00c0450842814520720a41080090b0603825803000010003c0d92241c80f00001c8030800c8004c2c10250303102c1c1c80006030400201161500410070803014051259141d41c0c001d0003207803603546540c104151072441309008660003244c0681303003038420b0502c0360740404010000498169a54007040440d00c3d52800da4000944900c4c03411402d60304a10300b00031081c02a00118581461500c0c1c40c564040c080c003402520703c48800204d400c2c1482048103501600e885825102282041c440c00b41003480d003031040c1005809800b40c4000c0c801c461109032410004041c0c2242000c0d0307121100800e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 498261438 1250 498260188 498260209
    0x61c0f06051e01080c040c0c021f020309120313060801030b0c0901020115080d080c0c10020702180907140301050c160302100e1f09030e0603180a080306042405 70
    0x10301000e95201c0c410b100c00d005281d1402090100050480d214000b424002581d051644007028440c502050b940141c4413020000310308a0590802044ac48001c40124110712900700b5140d4070800c8049540700d40c500202c000e040c4503500c0b00c0c01c0ca5803680d80740c1c0d0a58843d81c5c2440f0140c01802e4a4000032452030a00340240f108102c144000107442d4205012800c461400e5001240640d02c50b4500700300301c0d900030b0b0219401082490b03005c2c4c100940c0e8003446a030790004c1500003240940110b0b41c2400c43d00e80c0200303000421072038419015149071a1040079603402c44d91140092050020a1014290a06100b154050060082c140e85403202d5501303031034541c10880300100d04600c143c1c81d0f64520302905115181001700502c0c007421142610100c1c0707000038441d0700e440403846440c1c1101c001c0003e804c80350b001c540c110203441c0244c0326910340800b0101e0349945118580c69000f1a0103000810042000861040d44c040b142000060407008680080306581c0c255200f1102c01e0034000d02c15440c1684004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 498262688 1250 498261438 498261451
    0x120201110a0f0807020a170c010b0d060213090203041203090305090a03080319020c0a030f18060923100e2b0c060c0305180a030f0b061c0f0605 63
    0x1040080110004a0240d884112050000b400202d015851194494041a0052514070050120010a407100c40c101480409501034159001482414100c0c00b03412003002ca5000a014001391072150074508042c1d03009220201c9618000180811010380078400d80780141d4010700c01c1c0c9010301e0901800d40090070b049505806010b41803254802c00d80c0c504914001440c441c420040e240d0614505000c991421100306415050048c41050080320001802030105078041c9041d0040c03183c140780660b16030202004003071100150300d402091a941241c5c032101100d41c0040c0c101080032205907450030070340c07a4a0b05580c4c41070804021071001c0e40f0605845000b81402850740c18075031001c0400c110360f940c890307804002044554140000313000b1900e03541402445e080c20118100740003580c00070214407031480f400076a02986003604026031510607030b96007d19407005001011418900348901d005504031074040c03048001003a20045507282c030a0b1784221550200c610321100c5495a219005000020441d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 498263938 1250 498262688 498262691
    0x30f152d1a07030c02270c07051b0607080406080f0a0e0a03030507110109050c1005040b190201180318080f0304090509031306080a0e061501030b042004081506030a120201 75
    0x20070160f46c030120021103603d09180b20500d529009001c00d010218010f01c3c0c3c00107404180310b00b101144010031a020110751f04969445c4000407200012a035004503440070b02100310100c1d0205000382c008821034050314540c820031300c0c550340c0c1003050016564030005c80e20050b08140301640c0000c0c00b0381c00c8644c10010700e060040903951445103090131610480025616176100c040101c2c480d0800366040c45080e440d0b450041d10b445d0a045080301280325945400032242548800103090074401e41c088590082401e6882040f0502410010b02019801c210610008096540040d008600161088410f80710401541c24030f440c050703100009290003408031501d800100020801403144100000182126468050450400c0b050100403291850f0078064954404400c1c412030064403045001101d40c2442d01047e00403101001c10003800f0b101c1c0d813040340c8ae800315520004030036041004e0010384002008035444108194612040383c84207950550f0035803c801c20f40000701d5030270900380340c1c4070a69000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 498265188 1250 498263938 498263957
    0x3040501050a08090a0b150108090d17090a0b0a1b0e101d03010501090e0f010b0f0f0d0605010e1f0b030406051b070308041101020606030c01030f152d1a0703 69
    0x4482092110845d83c0d00356490701d401e1140660745e00209c07455080107100008000c0c9000a1001034516082201003465505001c00002d0070503d04214070f5a0140d84003d01d490203052042e00e09026101d10366001c80a500c58901382c2d10441e00c1100d155403185001041e0110910040320151440403682d00d882074010f1a802e00c0010702d0b102405400d0080c03109610015983d01c240038080c0c00c080b8919044200c03641040204a45540e400740280320490b02158058140107860b40085c428240f084802044141048000111109045d5400740b240c502c8407005110031503011075103000c00049010700410b403c0d050020401051040d03200591200d00c8282d00c02641031001d1880301d0300c0d044080120006220710b8104800c00000300d04560300e000080c0011b1078039080c003500194071181100c4403141003590b902000d040804903508210b8140c2c14030040d10010315103071460714001104091100d45482107241e4680c196120803421402143c400c0b502c104865500300841c000b00c0c2d03205031000d80c1040510130 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 498266438 1250 498265188 498265193
    0xa0b060403080729090d120f05040606050f121905030f0708030406060b03010302130905010204150207032d1b0302041a03010e0f0d111912090803040501050a08090a 72
    0x420109000301106810303040c0304405051071000010306640d03440d13012800d200100d070001404071088801c40c200320710045400b00d815002005c0001d08143d0302c9050005000a006a56010105940044d01e582425000401c10b104070340351004903403416035100e5a4840c0c10216818030b00540184500c058a140220100c0c3c403e0440d000780400340c0e9001000002d000801400b441404000c1000505031421585541c00081c0401710016480960680301c0d0340080401c82c0039030445e40038187c1100104601c41250713200a544880900044504041060f071840c070030701491407404086904c4088688403650a9511120f90f03c45c80110000029000880840183d4550207a060400ca00c094400c43c2c08443c90101829140000541c03985500700d0020401c030880c0c00b185500b042011401d02c00b03c02e110002009190200490588000140c0c0b9120340082000854000b11400c8060f0760307100c0e10546581c00c15440348150b20941c0d000c1181001040c0c1c03d9401068190ba11003100d03001c2d203c04601c10b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 498267688 1250 498266438 498266453
    0x6020313231917010606050d0506010c0204022a010216031407060f2301050a050f060c0109030e100e03030703030504030e040507030608010609050c03011a0f12010e07050c060a0b060403 81
    0x1003100c2c070007100304600148107003d400d007206040301e480c0d10300900c007032881c0c03150281c568424002e2284100740c03550006440c50f4002c47d41035a010707038003400c1156103901c410742da220b0035460089840c880c072440f541c0502141e4414004d8620b9003c040c0b402d6000c00442d56402d4905440c407c205d0b601c90326041c004440800c0c0c0612a4690506a0280200e82003121400e2010181078040b011200411b4400042c4029160103a1103020f541c810707600038100062060008409018080c070552003507091140200415074081e403080810102640e03554240d0031140015228240914096501076005200c40300100744640c2203960020301070b00340403210000e41408501940c07403c58111011030f8648104124410092250354001c03d001c0904001c1418010b4480342d0760b11061184403c0c0d00d480e1058141d48521900454003041e00540401d83d60340460114403211500c24030403238440c90075010000d6201c0b0f00800441e8170395074038000a0280c0781e5070203100c280100b1443c0030507500309600b4400480080c544 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 498268938 1250 498267688 498267709
    0x601030b150a0309020a060c150f150f030b090d0509010e130e07050a0605090603061306082e060e18010b0307080616030621110406140a0602031323 65
    0x100c3e40c02141100c0c0714014040102550342c0f001081100c40980ca9010071001c1d03004290300304072010081805144080b03000c0160904000b03002d1700c42d081d41ca0000d12492541143d20441344102040e50300b03a82e400313140da07499000070800000072800400c0601d2007503101c1c0c200310301d0070300c4024013401008030721304451030454064501400d1958055074081c000da28001c194400185001c0c94a249440d07007190205441e0701000d485640540c0500107018450b0355030b0381090016040680850b02400c071040c8105443c00c0c0c03405207a0303911034041d000010a10485003d401d040c0c032005000850386447e00256112040f14019610101d035503242140c0d40702da6000d00920006042e880020119810318503409400c1c68108080c80c4249840c25008000b000b1541082c1c0b003070f00301812101c0f0f100000d541000d429000f00b600125a00038038040010030744045c20340c081c00b2809800d0301c610100300e40f00d500580ea40c1c07040030200b507100c10440d41c040144182111210700c1c01b05074422603000c92500726010132440c112 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 498270188 1250 498268938 498268957
    0xe01030f031403071b1a16111207020f0414090a03030b1f0c030e030321160e1203040519031e1a0c070f050105060f0a0e0601030b15 58
    0x1454900c00d414540e001045494001201200300c0c07844c00e00e41006000816082c48189640039000440c20502800101502e042401150380b2011440c0c041e010300c00711000c448184020030706040d035080b1000400140c01035402852103da510300486030702006009914500c01d2a44a0b4075104012000151540800c1c001d107090801071003010203038a006403c0e240c440825500402c0161402041181711782d10b404400040b50030000d442030718906040310100c12a01207543c02d4440002e801c1180d80305040032400204c41030801c0002910395101145510141c5005000000c800c0540040070b481c2010101c403280c40040101c903c2e00d41e498021403e4105a44040070400b02806000c0051000b911403000d0f8006040b007000445003020f540f40401d20118a0480070b98024000c0040c0d1a43c0316101220102900301603007840058a03494400c2c060801180d00c14020081c1803d803c00e1070500b980c0d82d1041e0303400032081d20306940d00d1400440082c215000700720f9001d5460001542c1c0108401c0007444d0000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 498271438 1250 498270188 498270203
    0x21b0706032003010603050907030b01060c1202030a0818030418050105040b10140a09030812010602010c05090f090a1d0304030209070e0306040b15030706050d0b0f01020d0503040206040e0103 84
    0x240381800c00340c11601480012000305a41c209941c1c1408590401c5034150340b180c0c140003846450b87c40801c4e15041aa03000102064081000030541d141c1107490817450a10541c10080054401a800ca8503070181420f9440410f12010100e64840c5143c0399803041c40c14440c1c100c038100b65440740c0b8100002c2416400040c213030303550360051209003010f000e4001d400741c05131042c03071152070481001000242440f08001200394045900d1815500c100c0ba640000d540040ea06070301e82516884900050360f080c407503400590320b001d44c1800c0b003e004205443d501340000700450345640000f014003030880c500804c0034a5041c0c0d60948410007003500411116404008001162501c2c214410f01004030b0000e072540043c000e044500754076599000072220b80c456880400c1c2d101a4a810b015515004408003043d40d16002e070580c007050440d03102000e04402043c407042840412143d00510030050010082c450050b00608080110240544001c6410910250200c0d18050391070302c07a0000c030582070f0030444030a0b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 498272688 1250 498271438 498271453
    0xc0403120c05102a0306050303030114030a06020a020c040c09052125060f0e0a140103090215180a0e0708190603060b01031514010f0c02030f060906010f0f050f04021b 73
    0x402e84c001d1054280740d0681010000b607414480042d81d41e010511034481401c2d010084090541c4003400560903480c1d010400755118101404040d4450141001003400745242c0000741445074404c2c00c55404846000d441c803905004e40071808181440760111800b00ba10400d4503043d49021003d1411007403101c0c2c281c6400119092200050003d00940d10a20400c280c02a2041c1d00d580c412903d581103418200c504004400710304c0046e0040d10300524003039440f008892402604698200c024078a0380a41c185081410030040704004401007d801024034103816507000452090107400f2841d0000e08417143c0c0021443d01400740e1080d50800e40044a6650710340e480d040c003d50b01401000c60240301c4000c818815820708003104a60199954001c0c100000e040c901002c0038054103424034000e8019054503a40d441d84901c1c00d5403068241c1c0c6440c0b42e4031403d0000190f0070046540c14064500a5040710003141c90842000100d858456034640e10035800c0142c2442d4980c9118001c200701162405402d14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 498273938 1250 498272688 498272741
    0x207050312090a14130911030d030b0a090e06270d05041724060105120115021903090509041e1a01050303070308010302060318030403050f060c0403120c0510 69
    0x10800035501280700000c944e8501e610b544d5a6501c0425038107051309002519032400c0c20420344113658000040d4141c060740480c803d4440c0e261304561410302095507110341207651145004100c41c020009110f8079086800401c0688940700c060000290100c41031417002d200d601000c03414003a03030034503442c08540c00050421448040c00c541107000317074800340503100c1c0d900c054009c5800404d80301c11a000b22040040001e106030b00078001d43d048590741b004140241d40e10380f00140511501072003100701510881e4651000e0b030b8800c45140d0415a0706980d00120140ba0405010604c03c0181c41290078011030044c442000300d000d60010341e42400307107844540a61007610009509074040e00124040e4000b04885008030f904620290304603a8159081542c84c0c1c0c2c0c00c84a1100400200801e5030a80030011300001408000208032054040081c2554001c0d100c001e100340b000c2c030951000a113600c407103501500516008a100708580c6010b402030b1600034007400c051030700710f0304442e09a24001d00161200c1e0312 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 498275188 1250 498273938 498273949
    0x9030705060f01050306040615090603080903150105011e0e0d030503060a050a0506071b080102040e19151205010b060a030c270e0a1b05070311010504080d0c020705031209 75
    0x1080003442e092000c955040001180c0c580c140104040c1c81c89854000588289408509000003400e04240400c50251285041641540000401c0d0710138418907002c200d00600c0322440c1412900161203201d01e500340842d0940000d01e11518031070603c9492880f04070aa120000c0209016100e55283d96582c90210200181000c0540240d4083c04212000380525102c113070407602e00c140c001c1e0502e00c0b2000300d0044c59200d20f4003600001d400c1d5001250018885a091a24034001c81107240400070100440b9400303c11176807003500b04216030788840e84c100007080c40440c80500c1c0d1400b5000109190b03110102042d01640a200c1d5100044c3c0e65491458106a100b9035540d032401d184024215111030001d1051080141d0f4011152560651030205142c0034003980600e5802c8015101e07030b0047c543d04040a099904002c0d41500402e420f0800701b94140c1040c0728a40c8299030003140740d41020219000b000c014003040750400d041d481000000708803980c0030007800ca02400b03611140381d43d628404c4203000d07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 498276438 1250 498275188 498275191
    0x5030d050f0a050115030e0a050d02030301030b1f12020f0406080303010f05041139070e07030c020a110a03051605040b061305060915030a0c020f0307081c060e0903070506 75
    0x82c02d1400c030060014004403404002c8000081c500420180010726007142081d90070034004041c1d02c00d0741c2d1800c602c16008006035048034000d03d082d46440d580c4894071145480111010411006600740030700c14050101481d4614a00162070004107a44081c04601103464942004c10300f43d02c0400104200c071100c000800c003601f400c0c4c500744110388002843c0c0c0c016020306000c0d200e0029420344ca01803001811281c00c101150080046100c030848500291f4031450706004407018007800e10700054a1a000703000340c00d8000c0269004001c0c0390300644441c040a1445600c860b030145080c1c01c00408107208019403a1003070308400480020f070307103808101310031106020001e60140c1418407040007102840000d802c06c40d0419241c2582e990b404500142000070421040340f95607201106003c0812001d80c081c99071103281ea005c441c0358800d0006915600c3c000d086c4001d1514004018a000f140c945500d170f0401d1204102c030104804c0e48031804040041001c41d1400055400400e42100f48401044a103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 498277688 1250 498276438 498276451
    0x41e050607200312070b040f080f04030302071706240315010f0621050405030d0f0902030d02280206040815070e090402010e0d0516081f0605010807110a05030d050f 72
    0x40a08203904c00540500d070188840c00781c5480d091030b0014090140071a01101c940d90302c01c003416030340c90721521039201d030760420300040c2c0c0144120072010805000840b00c14412148202c02400300340d9440f0600c402e01c1c0c4a5000e009020040b0002054440e1010085e56808846c4c00140322250b6040101406a014443d80072070200400480b0741083c07000c18241c02c0040c40c6884201040d00da980b81031071481c0d132003a00c4205000c0c0745484d00030340d0900090780c000e4420900c201d0545072220031094080382d0f240c80e802d48580201c0c1c103026800d504102c03103002983c0d0140c0b001e400b240c10700d0340e90080d607400e0195161700100701e590610704200c0c3c1641d00c20034400c001d4104880da040305040980000340303a0320400c41002e006070b02c110030000c01c0c03041c1040815101d4090484994103180c842400c0c0e500c0381c4890b901c5008150038281729800202c441d010b2001600c0060391505034a0741c40004c01c80d10b1221759042c02c1d40314000c0344801c0c03001c03d1060005081c904040c4a02040600301a0300030442400000c058 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 498278938 1250 498277688 498277693
    0x11010e06061503040c03020d15050708060303090d030c0f0305090a08030c0715030b03012a020105010312050a090b031312030203060d032124050d0305041e0506072003 73
    0x8200c1d03280c0c1c9810500080c48082e0303403001d071265540c1c540794200301c0d80d60b00040c0d407180c5404041010041d41c00c5148034a0903c41d0814070284d1a409030581d40c3c01c10a4440e03540c581c0041c4903c0119050a1000014440c0241790000c0480c081e603d60103034801c56101c081d0001803001645c9040350920825603170052101c4c200441c40c180c3d05406050b01c1b1440b5004031044184030b14542401c0754440d4000d113a0310301004008204c1400c1d407101040e04c0107914858011501d106042540e0711500610845040300d400c440c104d080116108012604c50340410300150500000590108080c003004018507c02c51500644584400207414042c8800b042001e07501e08043c0100200560782d00c5041c1c00105050b418248021005051050310000d41c0a02c074184140c40c0c40c0602800341da190b80c403032a104001e021900348445940390b4003840030300c40412102a0110300300300410016091030500b601c02c80c000c40c0c07a0100b40641c494001a485510854040c1e90394044040010035a90a0200800102c0da08400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 498280188 1250 498278938 498278941
    0x30c12020a080d090203160e190912080402040b010c0f0b060d0c03033b150405060c03030a06090207030c030e0319050a12030e0a0201030f06090504081815120a150611010e06 76
    0x4000710704810050502c9c51203908080d08034814030664020b442c000d80e010301030402c40c40444000070b180d84000ca0341a445035040c400018945d5001d011032820441d000a41c030700003041c45840c0c01d402c05401400d000c1d00081c1840264000c502102c1400001d580703c0d54501e01505203521800c400c0c045103607204400819940b004c030401401405400c06000c505564520101c041c2c030110b01001d000c0c40d40203a4200038005820604c40f40044000d502c070f0200280108482919800c1002c124011050b0080205800e0401480801d005500414103c2c4c001070031200c1c1c1a41c1706030201095a005003003100c040d8000094841042440c030402d4000240c10f180c100440c506000c0100d640e401280406814175658001e14403030007050b50410b0010700341e008000e00260500d460911050b07448509440c01c4030048409940003860100d241030200c0c05840503113401c1540100c12810311460180280c00203d075280d0743c0c210113110500314000145042d441c0d080104c0f030200340482c04d480c891400c614a541290b030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 498281438 1250 498280188 498280199
    0x706020313210c060b0a091a0a14030c090a09060614040b040510060c0512030708070906020c15090d051002090a06082a16050109020a06020604030c12020a080d09020316 74
    0x120f8140e8050300054003041644907a00031501100d00b030f42003420458203000280a003000c0320039a0002c110801e40c0d05100c0e07180e490003041d001fa8034105d8002d5042d081188044464540340c10130541080c0c44c52400580100c40d40c0c0d40700300320b4850303600c0090094590000b05400c0d10703080c4034400a00c030041d03400b4005403419609991901c078060249409000c2c551201200b07001d400c1068011140f20181c1c0c507a52814444409024041c0855001000581032200441c20500c0851681c25010b0050305100c2e0403440740d1254821a0016020b0a4004650f8080d1001044003003220000c001403440d80140e581da40034043c402420165000407043c03255000c00d004824078a01404048000798460030309090301e40001502c17441c8510409206801300c0d0116100c28408198014082c0620840350058400d035500d0007170f41ca8450413a070142c00b08409905003000316001d0b4690454031107403403050301e00d51035055980c03402e0303074226450316155556a900c40000314102006814201900030034540440e40c40c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 498282688 1250 498281438 498281447
    0x110102070c0302270609070201020f030108060115020a171b030a030b011e08150105041a0c0709050601120c090807060507020a050f030a060b0a0f080604061d030915070602031321 78
    0x5001c5e00d0042c482e8034000b0b09460b101394103681c2501001d146d625a2540d4640e0038a940d02d0086c0100c00700301007180c1c0e0035038030f80d0700000341b59070b5036940070004451102d0300304040c1c0c001c0d400c0f44084214407020600391000150060004154044043d1400500800d2520005190000881d0107461094412070301d0300c1e5040e001f20380c09500c0240c0c981c800c0078600d0713600012555801158001140c04484607074160f2010300d044050030a07154004121340041e40c0c4c95010406994040d900320713002c2440d005980c104001d0640114030400c4440c01c00e05107140d55844981d10b0906c0030707400305000880200c0c0c004110700d442404d14006060031902c0c01c410a4034000003036110854044000c101c00c0d91494a0651038444110607c020010038004800031a40c50031801d480e0001118126407551400c02050003001e40103451010161424004508001c48071007440040201c803811400350134014041640059240e000440c1714108014500c04c5410a5150110150801c600c0c40c0300d444107540c00c01c0c10f100d03500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 498283938 1250 498282688 498282691
    0xd02120d0207170703030b0d11060a020a12180509100b1803071d0a050411061c050403030204030314040506180103091208180c030a030f110102070c030227 68
    0x4410440d980d610200c030604002c1c82204401080e070010609003600810101010700421402500c050000c8600c2404228079800e21072030050844100304051051418444050401c00005d4011240c2d040c2d8107894009054500c5100600011560001c0e4021500038107510701c0146002d40b400f000c0c9051503860107041940c136000b081091840824200c0305040030b8036104103038440c0036041d0b83d0801d0b240d1510355070317810380c0c0000815000104004200c0410303d80c442c244c840d07900700d000104280c25000800c5005c0e88408040c51030f0034061004100030a1240c8102c50040348a61130040e42e5916610300a000101c92002d441d80604040c00708000e03646800c02143c8501c030784001040301c508075010050b4010702c48480068001c40c26444480812604011898050080b6581c0c4540d8400001c3c4c0484c0c2d90040348140c00d400d40c02c01c21550700020b0092703035a04440800b60030600c0700e2002c250045400ca0704054002e4401e02480441081503082150041e02e070304410b140d00c2c5c00143c81520348050074540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 498285188 1250 498283938 498283963
    0x9080c0f0d06061d010b0a08070809031210051207140d08070b0a0914010e1c02330c0f1903060b07080405040605041b180e1e0601020d02 60
    0x801011400841c0d84403011450240c1e8404020080e07a80c8030410000c20f841d1407145418140748100010502d61545015211440b4441d07440c07501030f0341d810b1011900180041d081c04020700c000d000d00c030820705050301c2c0c003440340d91100074500c2051315203400c1200606a0340501d907815001500b080c4840360080102c01c2c031001080c2d40901e50900d60703103401282032081000c0504610088014084001503a40007188481c0c01249800e40c600d0501d0802c03402c072503c0001c0644640d20002d41c181c0103240c0c00c4031b07140351581c450040e01c03065041500307105501034201a001c0c4501015041c84086542128403260700066039903000c5060000035480c0c1100e40c1304a00b241c810189015203c50169442070300308002400662008545a01c280c0c07501e10000d030014001c02e8400c0b400c2c15404a8181424483c000000f02c1303400c03550b9510f0a00c0b20056550640035007544020400000b800b040840f81500c0090252040440d0300702d00d040c0d81000d03842c1c02ca034040c1c00c040c112342281c81000740e0703143d0000303040c0046e48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 498286438 1250 498285188 498285199
    0x9070206010314100609020d0b040519091103010504080a0207060e0913140712060b03030724020f0a0503040201020c030a170d0b0301090302070e070c020303030f060102030909010e070f09080c 84
    0xf00c0c00c8001858a402e0012940e5010708007940030071214244c1d0081d20280407460014000011070b9000c00041d22007c54007900c01d11b844003500d11940a9542003074040c0e50150503c8a20395030001c01007030130b48004541c1600c91900015001698580c100480c00081c00c840c5045c030100000703400003810071075000d030040d03061b2418100002c0c24812401445c000748001c01048130602030781d5555150000301041c40136100503107000301c0486e081c14044111050540d04c0600500401d01e180c0b46401540c03040d2030700d00801c95083c45000c11920010004040e5021142c9a0980b00d142c5440020325054003648101e010f604010003000000f0201e4000803c054817410350280c482501e0296071004011000a1540c590b0030031101e407043c140c0119180c825121080109603403641e440707074103880024100400a4040d07100304001010b40e0310354409540c00800500c1a41e240c80c60504c0041c00400084c2c02c2903000101c4031003403004283d00f018070940b80c1042c45c203100d1516883d10600350303196040240041e0080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 498287688 1250 498286438 498286463
    0x140c0d0e010e030a05061b0c070306021e0703030f0506031902091503070b0d0509030301080a17270f22090c031515060509060d0b01110a08070b06090702060103 70
    0x380c0c00391035800b5200790054100c481d038039418200aa83c0d03440075901034400d11000d0f90605200d011030012580d0241031a001010350f18650f658803002540320424802c00c0808070801c0c43e90b0b000d960002000264000da0740800c851010355005c0040b5100648428400e51204a6544000ba41c000121140e0354044036110111f59030304022185c3e000c1c845158a50501034094007080c031030524400b400c841c000c0340030100080d590702c1c60750030741c0c0307100030700a43d5466070080500c1070010302c1030a00c01021004091605007030040801701d140c007901c0003a80744003001c035503990080b1050030401c54a82d282007044520440307144200340d4581c0c8610348000751680c01030319510b0041c1072120030003140c00103660200d0b105184034085004c9000070070f403a15654a03642e08100f80000e0503031050080e6880f41c1c400520080c80d20b9005441d18001341240e10010303050150510100c03040744000e01003044802d004040345a5184818a0aa82d403600002c0036113100c1c04655050005169001074400d0540c0d6100c1e0084020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 498288938 1250 498287688 498287717
    0x30d1d09150301090b0f070c0c1703190518010302040b041a0c03030415060803030c0435010f11031006110102120a06030b07020d1e05190e01140c0d 65
    0x4034615401d500b074156003400c007868100013000c2000c9100d14045402c03080b035500c40d13010451f0340c1c103003d80014050024071501402501880f0780088101e41d2607808481c034101c4404110b601e1006038915440206502080d10300c0b911100341082c4030102e1003440e08601e410308120030001c1078016402641c40e00894100f000100c3d03100c141c11103403600041e07021241c4074035061410345242030034442249a46070400c84c00142c1540f000094070300034018640c00500b028140680d0741e0400d8419214800700c4800c000d0100c19a4003c0121201072090180007c10302c81041c10441d01a40c0c05134016000e101c4c403c1040000b407925400c04102603452500d0704546030400030703c3d444c2c003a000d00781100030400042d90038814201c41c0c9a0203181100d10810030090b0681c1c0e0540103984504100400f480881e402003210b801001d002042c1c415441d416080c140c5c240342c1d481520040e1070348020402d101190403401000b00c550303080f035030710f40a00e4000302401c0d280019070030415484050101c541070502890400e001e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 498290188 1250 498288938 498288961
    0x1e02011b050d0e03031003050d020705130905160303030218060c10021e040914070c0b040209101a0904150f090209060d05090a12030204051804050f06010b030402030d1d09 75
    0x8000c40100f0460392207080151000000100622088a00744260600d103103503140085131140458100500412807031481540c400050f0042c83c40c11182e80c0901040c0a140c88103100c0040b02860081da00140c4a41a6415044031030040003030303840c030a020920030106076940000c0c40703214000145070b01507194010143d40310046500059100c0d01408081000700301c2c026140d00c07150110612540f08402500c1d071000980e176522250340050b000b11071500015015041c0484560340200180701c28440c110f90320002c0a0b600c008080c0d52005035513000818000078a4603010b501c0a0007120b1185070420740c60400c400d200c1030010700c512012550040340303220482e5507440070f41d41400b42e441400c0c043c41c941490403e0302d90101440c102c0346c00c1000d07102e240c5443d100b4400e0b035054400103488070254441400a101d134054009200311400d1065400c132660071201800400d00030244154450303180e081503c109420520000780000c00c2141e6250100d68482080d010031605141c107650680003501d07211304520 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 498291438 1250 498290188 498290201
    0x10204081b0306070f0509040903091203020102120612070e1302040c03051e010510110c100f12020703050a080907081f05090c0303091905101e02011b050d 68
    0x94103406a450480001d01d040d0504845984044050310b1240e1341d40d080c03d0b60340085491140000417418847d54001c0d050179440350304498024203045449603900c5e240d44c50314107a0707800d044006075008219411810b1008001c507800c1501100c3c02031203070280e071000c00d0351040c56200d0441c5580305e1602244031184800b840c40e5881c1d8015205100c00301d414134019000d000203841c11039410728a00c81c44001d268a001116041c1c0e4402403401c2c0381c458071132001b29003028882d540c02450b0b01845403410b41540c0c0b6410440301020344c1e921103203403003520783e007020744a80e52030f0211002460040080e00c0c0000c0d8081308030b0307201d1a41401d1800d03454a42c0c0394058608030b0150004801441045a850041540b00c1100a29050416020b11007552020f079204e44450080341d0310798141d4010301804aa502d404401b82c00102944c69040038a1580c61000505140c610014500840c8150f81c04032401065a5541c0e1101e00b07860000380100502d41440d01a000e1120b542e000812401091240d0426880d40044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 498292688 1250 498291438 498291449
    0x60d0c05030a0c080c01110d030c02030f070507030b070503060a0501030e0c1302031b070f061d1209040f2904020d1d0d08010e0103030c02062a06070c050309060c010204 74
    0x42c1c4503407200385407584100340c1c58007603000e0500c10b42c01c2d201555881280c980304500c0756140544070006150307106602408010301e07800b0a42c00280044000f800c0d03184003810b002409140105000c40c614141060111409842c04007006420400c00c00c0d16211442d04e001124400e10303000840c04035003c0140c2c2000059450070382e10802d41c1d104603141130010740246025500600341240507640f0b40d824190248149440101807040300c183d04404034625510860b074680450001c100346a0428440500f40350b420023140c0d0b0354810200e0502411304240c4034201f06855038030410051030048010542d04215494011107404c414090302081c29140c5805580035206c490009001041d0100d441845d01d0701490a00c3c611486500829520035118840090407200c8e2241640c000740d003103850482d0f25044501d0140d030802070401030240348020349e0301100c40e1090804066030000c56040d088900b0f040020304584100400c3c2c0700000c0c0800d0010080340c80c000c4c070850300030b0f40e1500001002e50180c0a00c0d80710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 498293938 1250 498292688 498292693
    0x8070206190207062a12021e01020c07060c110906040e15010e0703091211070b0403050c01120c05041206060815191802040b0d080301091508010c08060d0c0503 70
    0x250707010680024224003a11825102c0c0c044511a0540c502049001554075010381e1211101040100300302c20700060b101c1241d48141c0d80e40307821160107004194101d01952540c2d0f90700140d4106141c906203c000040c01c42883c02c40d691781050784079200c1d50014800103501ca80c1009021886541c0d90b41c0c095002008020281d4031070305d2849200b14a041824869882c0c00c0b04000001b861251080c8211b002466016401e9020013088800403104000c0e1110300015922904801045046218002c0c0004500c00c000a11003000b5040c0010100124103040543d15800e0421a0118a4201c019907049d84d14901e0340d51858181400d12a010b40034581c03208005001d024450031500b030710244250702c107039031a00c06400c08600c5c1400f03210451316402c40c000300c82c881720407c0034018a001e0300030b50201c20000b881c00904003000c0d22101601e0303001b0b0348034807405a03540c0410004102c0d4502d01200074080b8800070045581a000c0c00313802c5500060209104c0c0e070302e180c070460412070310000b07000180002904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 498295188 1250 498293938 498293977
    0x90a0f081b060c030403030f050408010227040c090506070204140405060f0f0402010206040201050714010c02030d150b0d0209060d06060806090f070f030e0f010504080403020405070503040f08070206 87
    0x5410380322846041180c803861401d507040c04103401c09004584607600440011490a85035880451396001007440d008108842004001561002400500482212451105250b15041a0102d01c0c8a1800611400b66040c400c0a154564100000030100d843c1940d155507030355034510000d4010b1650303100c5007032050b41d00024001030050000e840c912074181911219080c0d00ca030403000340f95460841d0000e0060f400500003800551259001e000b60307e2040c800810382c0c41c60760440900395000e4007031003c0103900c04a200c1135482610f000711141c1c04a10200d030300e10f00e0b0a0407005921403040040c80c46895400281d104031030f8541404854415100d8802000101d071144801030001c03000341c41c4188a014140f01080400702d409480c20700450031070b16059420440c500b0154043d00e92802607044a00600c245a90500300a014880c801c6210b0001c90741d031a0b0544c410070007280d402821180c10801d0601c2000001441089201c031802d810001c0152100c9480c80015110b00c1010620b0350010000320 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 498296438 1250 498295188 498295199
    0x17070513030b060114130b0d020712020607020601090e120a0e1c020406050f03060403110102091207031205270a090c05070b070305090a0803060a0b040807240c08090a0f 74
    0xb40a80d0140d0801da903901e03040d04000c046011240222800c1204c5000317000810400340380c00340024400d124071f054025042111a4a91403092003200c14000050307000030307042001c525818802036000d006120810010f078078440303400c0350b40c4040c1c7c9001441045030009405004a0080140c0304189400900300740f6007000c041e100c0143c452400750220f014500307040700031425283c2003895506114020307005160950310f40e24200e400341d052841507499954200304412190321842c62005201ca1403a0040c50340c6c40c40c40c40e103001d00102c0355083d00108982030002c1030418008001500200b20314550181340603002400082c65001b6650100410754030300409900781c1508403010f4051980259580b5006a6880c01d065099410403241125150085010603000640d08000380d504048080c10b441c01054640864014642c0315400103074156104001c200a030b0401920301205142001c0104054400007601c040c0084800d5600241007181c0480c1030119601c1c0c050302c1ea0010081c102d81124426075a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 498297688 1250 498296438 498296453
    0x90f050a022703031b030c0c030d08070521070203041a0405030d050d1e06050f0d0c210203012a180308180d21021b21011b08010e071707051303 63
    0x60071107d14091812041c02a1a01013074505191002d030300d442d00740340d6130140304a90310740c0003000c0300c41c4403501c21100c0c1c21095890f000c20340c8510110303002141c5e0340382052446201170303d6400710400144410082448182c50104804101c850141030171615608600c1102c005008d91040d040300c5400b00407046021075180d0707007051040321001c0d00c841c0e550328003040a2000500145c040079108420350ba408003c83c4100301125203013891965022002140703070394006400c0d614100c041c800b161401c407400f50189407080348206011074040c10311003400740300011040002e2010f807101030b04003900841c4840100c1030404004074107040080980d00003010b2480d003031580c40070b602d01594070700c0840c074040c440311800081e2800c0c40107105400031803c0e4a070f940400c0b04444640380d403080110201e04000800320310900414210000d03200d41c090380c080d040c2c180213140700816031180341c840c41000140400c294020888411084031030590011316640c0000c169818822451400301d060540d800020510515 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 498298938 1250 498297688 498297697
    0x60c02150a0c0908030307080f18030c0d080c0711060307121b02060705040807140102120a031406090103321002030a0b060f040608040f0c090f050a022703031b03 71
    0x126242c40d03e003d5200c2071440d03a00e0004640f407501050381103001c500c046022022440c0c1c0010f0000c051011000366504d00d6040d5041034001034455405458607001e5180c00c5441c0729030203160001650300b000c0f00d6485607480640c14400590040c80b00001003100184250707003440001010500501c5184101400d08100c01480d1240000500900d80816101c07441481203d04403400640240060390401c003000c0c6520709512082415480703210340d003000242020700603114990860f00c001855102114420403a420000c20561051600c0401440010500f050300d0203010022046583c10a02d8883c0c82c000303aa80c0182d140c02d440c8180b0921035044845034000b1445414040f00c01d0120a10310014080b0a0003a11010115003d0a000501c051381c440c01310240e0150050440c900317200300e142c0302c00e026a080e6800c6070502a0715134001c0b0504006c41d0007010780101084508511705010b164040841e01082c050358030400b94054062881c4c2e513001c10a80c0c512000011010110b00d403603e2031150780741d02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 498300188 1250 498298938 498298961
    0x1e0304080a02060a1802220e0303040312050402011704050c090118180305030c0309010f02130920090402180306102102010c120302070f060510050913060c02150a 71
    0x510f07000502c0c101d18034007034646843c2052000036003881e01c540c20820050701c005451040c500094056010a04e02800b0780301c8105031130700180d580c0e800e2a080c01098800c0c40190b04075010304004c24400144d9000101020f204c1d4205080c00568550740f801070308040600064650140514001040000034883c1c05441541c103028100028132245850341400c00c212180038010034014000140d00740c202c1801550b120811000008101d0f105007210000c03604a0541625040301602060007108141d203d1025501885240c1151002209042100a02c608010b0b117000f541c0101e03124810301c001d4081422500402000d0b10307041d1400340301d030820000d110f12035440713108401d55100404514048002e025103070107a47d0170303008071569201c5869000d140c0360f8160416034200085d80108080a215440c1c0a110310b60208560908c0e80712051141038030340041d0b1190304064140300c8004038190002c141d10390310480109044600e03150030381c2000030300b00842e802141148200034007540d180c0c0c45900d1181 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 498301438 1250 498300188 498300193
    0x1202100608010e060703050c0c0f1509010b0a0915180b041506050901050a14030405060403091401020a0227040f231b06130b131a0703051e0304080a02 66
    0x355181607881c00c3e00c42c00c2511807070f180c000c040444c028901c02e401099010846000301450030141500f402c0c500002502041c03074a40000100d0b41c026480e03404020342002101009008104680b00019007150b45481090302082da6040207000d1001e00c034810100400c405c80706100c51984400420014000c1c001078103115900d80704002c0055007a07121000107503556581c1c0c81c0d060003620001901d540c0c1c000d00841c0d050161440711103206400000c0110f20480c4a200078180a003440d28010b04800f0b410742040f0460310b1400c8503000c10740d900045071103490360115420501c0e280b20310800c00d801000010380c9034140d807d09041209111100703908869042c407409050002d040344841b115407a00c651429101283c1102c0ba40c1078100c200f0300301040e01c14030b00900c1b4900d40040300300007201c00c02c565849014110300200b031100c02d0003100e90340c1030014076105045441900c04e03558545007a2003803260040c107012010441114000c0380d14600303581a18001401a500c0c1030906140b103280e045034100c4801031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 498302688 1250 498301438 498301451
    0x8040204240f0e09060c03040c0b0a0c06050a05010b073002070602070b07020a090c020705060a170c07030f200a03111b090105060703170a0c0206011d0a09020409120210 74
    0x7000a550700b6840f44404031301409864443c01c1c01c0d2102548080c2c015990045480e201099040c080700007080448029258080019198079100302230fa46c0082204150514000c010410b000440341100e12040e80b0080c040820350707061400c1010760500301048150b40403058042402c0c1171300020310348150303010383c1c080b205126514a4001003130301c143e101c000e4005000101c204060785451f0040c0c04641214019a0322007529440481c0054000c1c01824000900140c101101c0c00b040b6034a40350402503220b201440c0c00c0c0651000351020030051842401c215807410000c241c0702e15203c0030b06d490f42c1920165417a28490b400c0040404000b40e81d440414011019116002d10b01c0314204040380c100503000d000380342c0c039010811405130800340080d0180075600a052140c10f44a01f44680300da030041c04005030f0042c410308000c2c5420fa058200900b6021140c04070713007020b603080e10101d40c85401c0302804160000c007071021170b010703003110300008240910740c9044c40344075600070404a0000764040c0081094 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 498303938 1250 498302688 498302699
    0x70908060a1811040f1a0a210f0c12050a150515040f1508071409040803040b060117190506010f1b020109051203300708040204240f 58
    0x11100842c00310380240100c00c1203040000c01d556518201c41200620004003201c85040840c1500e0141d44a0000702d001203038408400d00c4c0c41060240907066556807600030350814010f915410402502c094070750b088060002c4108034a42c0302d600060039501c0211003c0d50503034500035503135002c4520101d580c03400ca107280c8001080a4414144140c580c080510201409841404000c140b184102840281c4038850040b103007543c0d507488d80007001080c000703241103440c0c60340d0a81d1144080b0606031180c0400818400402c8608050b6600690000d81c5454191103060060ba100303500c09084421b04030104e0100000312420440d0715503208501c940c05d001c5540c40d0001100d070300d0314201000c000310f80040007200d60850105000340006106062000e0820342b00c50010303040e1700350302103000d0301680001a00302c100070402c0048101c0c14100002c084118126007001c000d4450010070807000c2141050014041d0f69654009010130072030040035502c01d4402d1515502202007074041c0a09800020310001907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 498305188 1250 498303938 498303941
    0x2030a05030306011e0f120b28060807050d02030709090c0309050f0c0604030b13080412060b0a03080304030f2705090612030301061d15070b130b060103020901020a050105070908060a 80
    0x46001555445a88106a410301a0340000340d682103000e20980e03c0100d9283e41d12149d8803801e40749105820001e49807003101440400c0000d54020f2402c020058050100041d0010140c2e00c502081610158882e520b42030f0484011000e544001042414420ba1110182d01a44160007603406001558000304040301c6140e07850400108258104008010400200c0c01c109011600816072051041c03005021b500d0b09000c3ea04180c212103002c0300e0311015402004800e01c10061707040020f407400084a0300c0d640340c00a6900005002506112510a00c5e0004610981103105000c807440380145c0d0750100b403034441c1c0700c03c20705014607400b417880100414001c2c5441c88241405c150510300451460703080050031100758880081d000030000721241d070007600740e0b58410141d04468580c1e000d40c0d211242030a0050307030410050310f445901080542103002040f8000046c81d4818400c0c02c000d43e5031400440102d28102082101500c65442c04042c08500c69215440c4000ca03022001160030540f1645500300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 498306438 1250 498305188 498305237
    0x18010c0201080612120705012301050307170a020406030c14041104090b0307030c060206190c020a020118050402030f010e0919020f15030901090302010e07050a050f0301020702030a0503030601 84
    0x1e01241d110302c0014118a030610204440c07030b801074107858282ca04010040300740d030845a000c4035a651624004404208960071080704449a0400d24045501d0040840e4a0b40441c0c0241030f050085813184100c2100200012014168041d008001050f924186803000d0f4455024030708504048040340c15052030140200315505207a80350003464189441d10050040c540c00071a00d815001c1d042000000c200d40c0d43c01d0000510154025200d645010451001140c981c111203500309450018040c08032540081c00203030850382800c0c4445800f07200e0f2164400340c034481e03101d42d900c28000410004103404482042d8102d60030300311850111340301c00211a80314508001c0c0c0010142400e103820000d880c1030510380c0040390028101d010360359030080041040b0341c001c842000d403d030344030f00320030b420513a092150004c00303540300000c1c1c8485410305000482081051050703500c140305551008080e5907080d81125840359004040300e00351082c624015881c0e03002210210302080054000d01d00c040a8000441d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 498307688 1250 498306438 498306443
    0x1003020f19051009080f0f060c190f11010c12050609040f0624030f03230d050c1603080403090902040b030601030e07080f0c0405150603160309051218010c 68
    0x4485241080180b20710100f081465404028a2003000078040c0390500c0481c00d251040809080b008a050300b5003803070300710082c0c03140e100700d0410400c0900c00b1650700102d403a8007056240ca8015095801000c030f614440d12141007806520307200401103115007140c80302980c80e600100038842591a601041100da9044070044c125410f007030301682c0020000c1d84030b1204410800700036840345808880c9094200d0b00e41c0c200310342444200c0b0780001410340211280300c409803500c0001c41c0d4400c04480b400700f180103100c3c1d0ba82004d40c441c40800c144d0300300c8506846c01a4654801001015034500b402048290b00369415400308a090307a020a0010369802101c050740d0384400440d281d51641c50044004101030b015916250041d5800400d01c80d405006105001012400034102201d14004000450b00094038020700845000a9a186070300c0e4036044e0307540700031214001041052001025805844819401402402880b120742c14031505c00002c1c0c40804180d001c8810f400b00781100648400362080c602 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 498308938 1250 498307688 498307729
    0xa0c140d03020c0712122102130303020c040510050d020307120501060509010902250f1b05010e0604030b18030f0c0d1101140606090a0b0d0209010f020d0e1e091003020f 74
    0x24840c0345406000e84403905841805a1460f09100d4822501249c01100540041840c1c481040050560402030405c44940c01c0360100301038144a825407a1082c200c0c856180512501c404110540d07800b40320480003802c0c8190110000f881600c0c00e81c1c020201030040794450010385001007402401c034800d654410300b00145c06050f006058901070f40f030900507036080341d9a0454408100024640c00f040c0c0030840801c0030a103280c0e40c00c004c00074010022410348640070f40700c24801040401c40c80d00380c0a8120006070a9010303480711144503141035109080d00d0a20811001902c1d0300d00705000250100c0e072103080c1d80e070700c6080390810804a080c3c46038420151115034154022038001d2801600601c2540341c02031100e22126500e60416100c1d0708050310700b81c0590740c08130369500c00356004010f4140d00e12861015002001a108001d88a00040c4032400d000d84d4000c14031001001d40c000c01c445881000428003905807402c2c04488500446030f000481c060403004880700c41600f40b0300810340f070850301c0c0b070351 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 498310188 1250 498308938 498308963
    0x30c100c211503050d030c081b030f040201020a080313050c1f0e030c0d08070b16090315060e01120201021002130605070c03020402030103081e0403080a0c140d03020c0712 75
    0x407800242022204900039000140000800a6010815800c04110b43e440201d0105400310000c0d21200b07004091a04200604c6102c031a0101c2c5e64003100da20031142d440800b4180c40d04e00040f89802002c0c20010400480041480b069013007a411514400d84101704403422110408240800000c47c00ba210495594101c07040c50103074001e000191400401a088406100e00c0000145407071313442d800161aa0030000801c0313002c3c0242c940001b5400707080c02c0f0118003054091500148801000c0c07102800d00c1c582d1825011a02003550410b0004024014200c4da030341d40c4030803000010840e070050490151064104440522245001f9a4081144405440030440c58100b003500c15074805001120000c00e504030120040e565440994080d40c00740c14015111074603010160390303400d0400d10501c00c09505010800c0040c50880031111840024504912284200c7c90032a4030b80c00755006040d400e020300480601915415400761159001d29000c403110a580d4060600d5162600600a1300e900160130 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 498311438 1250 498310188 498310247
    0x13031a15100806030c03060a062111090c070b010b0309010507020a0c05060901090e130c0b03060a050409060b040c0f02100e0705010c03140a0e040c0806180c0408030c100c 75
    0x44460703502c2030700601a20500c0c5d0750040024108101100c00850181d964501800280c9050300c1d840851364510041c48140b101c941c41d24120303034000c045510322814901e1f0002e1400c05140c401c0c0c031885644010305800b0ba50311030a103061550812a400b0449620f00390010312501e02c0040c068100c01e80040e04080321a00300002e001240c0d210701d0403541484400c2e840010380d42c0602001c4c1c0d11414100c0401b003449080b92801c0c1405002952002400c3c10040c030a20040350744070240c1404860089074005004403c914100d03002d000d03a080780541c4146440d1441442030b4103c42000c44025442c1c2c00c3c0d401c0171000301c541c8422640c400c1002c28a5a100301d80c01d01c8194021454402442d0103801c05250520040100c00d16981c00b000c0b2050005044124801c040d041500030454940303060300305104c40d46003000100d016011908240c07084040102c0200e501300c0c41ca50b00b1100940b4039070090380c0d50398418402180ea600003880f80c0e10a118070341101045410301c40c8460038a40500b4841001b120306615 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 498312688 1250 498311438 498311447
    0xc141507020f15090a03050d020d1d01120b040e060124081602030408070b0405011724061306050c0615130203090c0a09050403020715020c090c13031a1510 68
    0x4040903d01c822003080350a0b0b2a90729240c03904000d42c4501b000340321400314894002e040003c590207034010300213004112403200c0c2c0b50005401814100b8030b01481070140d0032950602070070603a245150420300d07000040c2c0c140030000c11401d060301e0b100121180c1c16410030001481c1a40c581e004d00d4002640f0300701141c50400000e01c020120741c410300c100c0703040a0b260080c00703040640c10761040014107000a81007249503004842008848001608900e41d0301c2d00f1843c691540ca000d0007006403100410f0003050f0b99a0f1200d05941045407a0200f1164254540b440909198468601941d213803040b00009140c01c84604021500e001c0e024001c0c02c42c0703107200e00440d0007a40001c0c100310400c1c09615140d09240d05c5a150036001820b04480100d400c0c1440c0c01c0207800c04480d90420f00200c5034104088030181c2d0009141c2c2d08d0018141c403444080d03035840404c08214015003080c1c0c0d8002542c40800010720480b20320201d10b6526202c00c082c810303146da03811820301201b160012034002004020359040765001c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 498313938 1250 498312688 498312709
    0x80d05070804081915270501060b040f06020f0f0703031d03010903080412030509030406120f0e010b030d020d080c0a170403020607030b0d1502090d0c141507020f 71
    0xc0c6034107905140d02d0345449030504800300f0a15400101c2d02d151030b02401003002c1ca2040403150407404201c00c0e4400160100039501c004001010701400c005800f0821009500040040800d05202902c56440e44040b505104a502c9440018800d034501949028004070300c2d0000040c114000342260f6103155429500c0d8905204400b0b180e0845e20140d00f04c9860130301070180c0280c8030383d44003641450035103824401000030300c0100041518040c10046c0c42072000080350103a440c2410080f590062004420380500000c1d0100c55103c0e080c845010b011b03c105400c0107004c4035048050340d010321800e540490f9512040450007001440940c0490314400051009007401d01061818908400e006200402980d5080d1021401603100380704100c40c85505108003408901c0440d04844c488000352902203100000f10560b41441d640050f6283e9035960b07800e031103480c4940c410174107100d07160782e4076070070f285500010f16480c09100301c00440300150380b001e0119100c460b40140003a04000c4500141f200e203520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 498315188 1250 498313938 498313943
    0x6080c090603031603050417060403090306021b01180507211b030206031f14090c0d06030b0405150105090601170402010905130e070602010b011e1407200a080d0507 72
    0x410520103503000144001e5401350003a15170741d690314030b4140c0b2201c901e070704107400601c6500301406000c0040e5010144074222600000050703115102100da00b0240742d4071070000f44503586805c000c1404440041050f0074420300510551340e58a0f40d55200d001020a81030704900c1042010850000240310184450302d0000300380c411503204c9440341e000c40c003954002c1d02c050508050488600c18020030008081000c1c201610f041c407401c540f0729000c9200b8100c046d0210f0030a810205519800d41c0b015031000c0011600912543c401b0b0409041180d01c0e481508102e0190020201c00030030142008035209005038010b070341c0c2c8141e181d000202c80501c044043c0c0100d0402249100c00103855442c0e030300d8030545622100340050b054884540a070328200e40381c1c0c030510039a4104591150143c1c0c02c0703501e28081c1c42c41c0c0c2810721100c034000d15007150251140203002410500107d908018400d0700c61000326003c40712024207007650741000030030030750b0842c84c0300d083d101d030b072004c0c003081d00b11480b03540030b000a9071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 498316438 1250 498315188 498315193
    0xd0f0f080706020f07060b040c0516050c0a06110601050a0f0501110f070b120906150603070201021911060601020a0506160e0307060e031009050706110a02120c030c0406080c090603 79
    0x45142e0301e4005030b81c003c084054042c10007040c21414000300e441940c0c0c610400321401c00c5544200080a07149000354034102007202c06426048050150520018000c200000e100c03130500c2307403500340160000e400110341000d98030a110000c41c95040208501007690009210001c03043d1411004503060040790840c940140a00084003d14020030481c960140585102c210f4651046641da0f400b5007400824040b403e5000e8000d1000e0001015a11b02020300280c074103568a61755601c0503400780c454001615885000f11302528489035014075048861007440090b110103840d10401241c1c1c45c0103d50010b0055000301000ca01007024100d643d14988019080005003103650000107410001c41e40e020f00082074188004029038a0148000410303001c00010070824410592109a60303208a8010340c0700f884000c5a1204641908018502105a0040000480c030f40a1240d5544540d900c410a50291044114030380032843c1c6405120140d0b1038000082a119082c2c200304060020080d00b0581c060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 498317688 1250 498316438 498316447
    0x906041e0c0906030e031c0902180a060302131a060d0603290108031c050a0b090901090312020f031501111606021606170619030c0509060d0f0f08 64
    0x80e6601a1903400005526100d403940d1414001030251804100f050955400400c43d0a02c0200010800341d0b50300d074881e1001403000301c1440800c526840140200745401c400c4810001000105e0308560162071007981c3e071a13156885014550207403010b403010301140940c004104105810800c1c00340c054418226808075045a40f5101d14403948060700507140c04041a844803c0d2403403007100054014100071000b146019090b0064041c00c0e11094080d403007403a21400460039800040d0007030716201000402840d410304010111314000c1842c090300f2404960180800041c03d111882a42d42d4194aa41c8180c5190340e400a86990818014196418480061702002d10f030001007001a0071409503048150286050050191400b10000041c04041c1c0700c02d50203000c45544062000d03601045441d044a03140c540000150301d180c0720031308442d20801611000024041c05441001c100e644c2607400c00240e031100340900103104500395003c0d0100c4414401c3c0c0c000a100c1d0001b04001d2030080150301e060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 498318938 1250 498317688 498317741
    0xb04060b09040c020c010503181e030a1e1d15030403021b0d0f140c03010c05090a0b070b220602031303020c040e060a1d0f010501061706090604 63
    0x445899400016860102041c0d00409090600c602492030341c0c5070000f031100410001c0001e206c0d1000601000804401c0301c02610410b000300000b030350802c580407030050300c000f01141c900e94a800515040c800a00303e482c502d00020301c03101c06800e40c8074040c0c0d07402030b84105203500307004103401c0c0ca01d0885c0c10420030a1002d02d00101400030314050b0384641e01400020000c2000d0303d102c61040581207104200200c0c40400054001c2c1c180031880360b201c050144400952034105081c03400c031400c015019401c0c1071f040960030303074001c00500a64038121001d4515039150744d2a20f800c0d0040034001010842c060001c03ca40408a00c94150309407010400344a0645c95580c40100b42c0c0c000b5244259041642c4113960308041d01400503420424040e035080000c02c0201e04425a0b4820283c0f40e4004d6517961080c800c504049120702d000040b640c80116402c03043d40210450081c5002d10a400000313440d0b81e2244c01204460920310f0007964000e020320b01e0b40c0c449004000c0140422100c10503821300c3d40700040c11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 498320188 1250 498318938 498318941
    0x703060b1608090316181a0f030a0b010e0a1503050a02060309030f0f09040c02030a0e0f0f0612150a0b09090c0403052d01060e012d0e1605040602100504060b04 70
    0x406a407110701d690406c4c034000403040d0322002000c108110383d04040c0d107450003491a8440c00900700c82199070070014000600401c0c204020300c0740c040c040c0018800040ba03c48520341c0b17000e0080d618000100145500d4401c8005078902c0c40c00000c0894101a01d8803025150070805150072480d020240c900d885422400d40c030141d4004101841d02c0ba10200d200d0b201e520703040c842c0c0d24600d0b0050002c0c5151100c0700f0750080c401201c5402640c4506600b1607448401e4907416a243d1221502a010aa0362002c00b200380b295200304035944081880114500c01880c1402c007061012104d680035614205000103040000541004254050343c4200380800408190200a0b15611498030240e034100300720302100500101150342c1340411603a041c4041000b0240145075120b0456003100d504980b0881c151302c00f00804a0204540002d01201500201d0b4565000320440e000f1103801401c0c0da030401d482c0409440c580107612590b00980c101183c424090501c03a008158401d01c110070005036840040300180 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 498321438 1250 498320188 498320203
    0x60a0218100e03100b0603061905030102071401060501171b070c120c05010315060516021f0e0108150d0507030b10171b0d140601031101080703060b16080903 69
    0x1c00044180c204000e0509043c00703c903203810707003000040c88500d8281d00400c0342c610014004501030381281e900180f06071125882c0c2c0010f008010001c2d540c4424070305291009c4485429100d4003940b03840740c006115806031301c2c4000e40681c00c41503000141d580411040c180031b0204485c0e01c140c0c8003000381000040700700c0303070300c1300641a070440c078441441040c140b1220b03a02c0542c0049060500c0c048080d854400840c0302e10f02110841e14ac4282da4054047c80141c1508817510004e401416617200d00c003107060075120103c6030768100e60307440081504060045803d0042615404400c00384540d1200603820440c07182ca0466014808880034a90b413aa20340d0320701c2d03208882d00181c40812840070b00030b0000206900344a01241030042c180c400441030b00a00d030403460b5110510403000344813540c041101c820380300b009010701541660840c2d0b039a030404100400c140c5100500003a10000099510341c060720524050b640800b0b00503040c844041989000390703615600c181e44c1d2810a04c0709003020356040060a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 498322688 1250 498321438 498321469
    0xf05070e0a0c020115060509120312040803041401180b250905031006380703030204030209060405040c0b0a050d0f06081c0507030507230109020307080f060a0218 71
    0x50b190428210003400c513220755800d00d006108140080100d10307480420748420240884091780203104603240315140d841001c01511150320410100814001040050741c820341c01741c4000c054580d0ba0302001802c9980b040c42485180e00980e03200c82c08203844207515944010010340d1002c2d820190360b603049480c8043e00040c0c2c0000c000f41c20612886c10b05010065518001030402c1c08101d00704401409407540b00b4a140c2c44540c500c800170380440000314150340d485104502d40070390b81d00c25414010065030140c00f099000d1043c0308003144c000d00702842403911807900302c8001c10301c15007080001d0003182c0c080c0038135504000c014441507c1c010f405200b132840342d024120001400503d002d21407420108500440010110394a40d0015960b400030b0884030311544c1440c000d942d602c01807911035a03910401544641203003190007003c054400550000c0c9125000303d0441d0285665041541d640b688071030140d140e41d03007000c004101e15544d550003810407050403480b0b408040f264507010070311540041580 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 498323938 1250 498322688 498322691
    0x1303051903030e150c03150604030b0603121207080603010b040c081806190203091005090d18050f0105090f1012060e1006051c021305030c09130f05070e0a 68
    0x2000205505803142801c0d40c035081003e0310000ca505244d0003410403004061808030b02002002800c0c240000c120b01d450703c2c400420850310b40d0380b6410300340c100c41c0c0704640d101d0080c03040a500049140c101c130144d410090400844038601d5072041c9003100c050401800ca41d8040d900c4d2103079644640d0300d42c01840c903902a1a51075010600d0120107144804038101c180d1100354000f082032010304480414400c0b4010440b520140c2e03a521520101c0e4500701d082104040c4944c9030000384240b44102151a00280c141a079030a01b240b111030f0801001213200d80700e900d5118200c40d80b91601540036102034410036000501c0810384481c2840410f0500340c018811000082030301003038201812062090a001d04003194081c6c2c00791900e4181d000d03410000e03001d0700c0305001c408a0300000c50a00050803914140b14030505644036000e00d2440a10b000d41409041c0c4607014409080c041c07805e01414003481011542031707200388800903480d54070030b0410f4400169258010f080012030826004040c10340151200c940 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 498325188 1250 498323938 498323983
    0x209010917031e040510050a0323070c060b03011407020d11120d020d0f020d0b0405150411130e0a1406180903090306100608071b08130305 61
    0x42030811690001001501078110146540c10000160ba0140615020b07021910b400c0d51489412030196500c6568400d41c0020800ca0761640040944184105900c0601081e00c0a00700054002074100b07000c00c04103624400150340070300c9800b00c2e000308ac0c040c0b0740004141603088086825180c2000100749081ea070344051040541d810454410260117903e007002014500c1003606450381c0b083c0c1d40c0e00380800c10200c0c60003ca00082c2d4111030408031103807410000d407400c842094002e90416a500701140c0c5c5043c691010605141c05160701c0342029805040200014904102c0106103200d1000000d0100b40040c04580e0100c040040180c10480d00210480c5468132040041d81c41c80b50810249072000c07010711807503031030b01000411000060603459402e136840c02401440c3d4000c5c0002a0307858814841804408540c41c03040d14282c0e60640c1c2c034103050703607503a903015242140700c1a105800803825800790808103071400040c11498001215260085541e501c5003403034580301c8074605002c2029940e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 498326438 1250 498325188 498325207
    0x612030c08390c01090311061b010c030c080915060910050a060c110d050615011e210c140a050904060b120f130308060d050d050a0305090606061605010b090a02 70
    0x806092180910f0700c002c2240c210351f100b0954811912611740140404510b084100b4001d454456001d5030850080280c11a000c030003e0142400e10005000304a5120105c0c1440710b01103081120040208050700e8561503d070b00344040742c1c00c020f182007545042d00c2d0000c902562402c2c20840148110b81e61811400740c20304103072981d03c20f03400c20070384540c00380c81d51100000c9000c9000b60b0710413107800e03a00c281856440016a800c9945070403144100c014060050050750f00a144000c460362034001c218250186684030301d00300c4012841400104021070f00450103450040014281da0509190180c00c1c4104039000c10706650403a0051100d010f070104078004030000482d03001d94810340c11020303082103003018044034194100014001e010440150002007003a180c00c1c1ca06446203520100702c980100798400d0040982d0449100100082e0a150201340c2c030107c0045e51900a600c02021140307050210031104a6810b0791050803110741d5201e2000d0003596a0f4904854443d09035240c003d81c2d21100700303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 498327688 1250 498326438 498326443
    0x603050108010630060608100f0b0d0b090a080d09060c030c050901030b0a120b04260f21040305040816120b1e0901090201030612030c0839 61
    0x16080380001d41e1608000300a0080d4100c400d80c40901000740110500050f075003520401e2041070350280c4540c0c20030b000054000400141c0b10f12040740300d501044181004022034040e51070140b400303584811311048603400302d0300c03c0800c83d81020210301200c2000b002c40d074904075150031841e00760142c1075440446105110f59809915185440fa2408100c80710b1000b2000d0024000d01f40020304060762401e40c040e00c0d07110089202c0c0030b8046a0561301408005162942c182c070710442d000c590826640100c2480e1003200031112100c050394201c800e041662a040c400e185400a54030401440d0013940c205070004400f0000718000e6000e030b95040c4e0707a06c4c2801509490311250020b4030204500c5010108034440f480c02c140b0064990060545002d030700d500d1140075000b120403000d58a050300740c4041c40342c0d800d81503101c12145c510170780f4107100055450010040c45d0003859006004075203020600d4002070440d500604182a214a580c600007002e01d19228103546450903c200b41d4052400c4e07030000003000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 498328938 1250 498327688 498327691
    0x30804080c12070e0718031211011407180906030503091906090e10030f110420190201020c0313031a0601020307020405041e050102041d13030302210a02030403031a1014090607050601060305 83
    0x2030740000e105440011222f81481e42006002c4810070070540007944911849400c01c000403c03400806012154070303402c00c19269806038400b5803140104400380400d454900850408840c01790b01c2e2490320903d03010001c000c0c0c1c50001c0c81c40c00106800d850100004070409000c254290261000034048a00d02d0f0038407044918288100b0b142402141c3c0d2300c511200c3c0f42d4121030400520455030070b040040c41030181e0190040c1c4080c14003902007c1070b8003000c100e1007260803080b680140c0107034070700c032010445200e03245506903402d5005070401c000f8580507007005e03003215800900c6200190303108070308120308110803000d501040340c06940014040001c030802c0c540040740300c0e13141025808503090694940b0314106031078a0040516401181e0150644204020381502e2117908400c2c1300c0c1807038135640c0c0d80004d50088a00720003082c601456071461903410090300410040191140001d464025020745481340f89032a00c91500030204924413054981e4805090014400c4000388900d5041007406815500b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 498330188 1250 498328938 498328967
    0x5071a07080a2c010e031b070905010b0307030509150a0207030206090606060304030c0503040e13140a0b0c1303140d110d120b0303090406030804080c12070e07180312 73
    0xf40001c2050803d61010306641844140310000c0792034018202c41070140c00b51200341d0216000119441c44005505842c0300c4000134800f059450385519616004129078080c068402c07003210a000043c405400b9501980d08400b2030f4007142c03030350307404605800c01441080b02d1460036141c01103410303420107404101d0641c00c400c5640c0036008515014011030141e0100620140420199480358400e015091040724003526550002d075400b890191203100020307983c880119111484c0c1405540801c40c0440c600c0c016990024a0f0519a124440e074085241c1000c0103202c400480d090000002440e003074010070054102c40040c0c10b440b0750340e400107045603a100c008a0115040700082d0040b40d03502044280070305059000c00124a50114040f92843c05040d4030981c000f0710304500072050040c840041c1044540300e00c212502101c0007014840e111340c105c0c06691142d401144144642d0150600d40c40d44284a8980101c040350b255540c44c0302070718503600c290381c908070b0080c1800302a9400b1100710002d84 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 498331438 1250 498330188 498330191
    0x7030603031d03031b07170601030f12092102010f03020903071a09090414070f0b0a03053612090d12030902090f0106020118030f030b1212040e0601110a080a05071a07080a 75
    0x1891030302d69092f01d40642c40018100c0c12003070560300103039008ac8034100c00342041055000601c070182c8119500108903403800d0b40490381d401101400d45210340216948600080c3c00340058610302000c145070b0050a003e80c008c0c10f074061210450544880211500c2940942c03403120b0f03044012401a803e100d0687c111803c4040650300500040324280e04880041c05140b81c006030300c0d6103a0030742000c20000710303085030320209543ca4140500200340b5600741840030312505803035001000200c000c16621032007071050f402c2100c05a103031010445428400038485803508011551141560001c0c8620004aa6847c40d010304c00c4018884540c0c24420980c081c0504480a2055211500c02501101949803040105501c400600ca00d6031036640301d03500450010011504800d000524404c556002130141454045060001541641c0300d691018009040a006070130300903041d0b1140080d903800130302e0500038002d08112100000300f44481080100910103104003e40c1050078004100d00c10203403500b42005d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 498332688 1250 498331438 498331441
    0x21009030206040b03090a1719030608071206110c15010608040b0f04030c1e060b060909010b1b070609090518030307052203060902010807030603031d03031b071706 72
    0x10303141e0400f21030540da01c1c411010344035070316800d25034a003074266072000340111000c15130826032905e002c018101c5452100b40540700080d20361030403030842c0d25911514013a90300c89081004190402900f0605160003141c0c0440c000c0d0200c5800c07182648444100f40329907011161020010b10399070089409000181382440b0b1908103500e5440504001420520920250401090403d402001426090344c0d2290541b43c00300b00d440303442d03942c41c1d8270900182d54041c2080030030b0304140b600c00c040304e000400091801074aa400c1c00e00f6040b0070f810644505040011160308903c0d81d0000300f00100c010241c40e500c51007260b0130a00b03108150f1382c002d0902524260a81c0c102900c210010055070390103c954a00a600c410110b16906101164032869200c0700402550100a00c0082d80007960014001c5c0c03541403294890041c00c03400c8690510000d80001c1030502c001e581007040790101f400c43e4800408681c00c0c20303429208820507403041421079134142e02041007089400b2125140543c94444032020f071445 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 498333938 1250 498332688 498332693
    0x41112070f09301412040b07060902011b0b010906050d150b0a0911030103051903020c0103090c0905101505090102070e06011b061a04050610120e0f010902100903 71
    0x241c40140507500203081a08044140c0c1c01403e60428000354904030703200c02291a07410140c4c0400c0c900c0c0703680a264003490080e940c440780c28900b00c408444080c1515885c21501d612154001c00080320100c1c1000003007030344030f00c400c0d105420380d047c0d00e80143c00684c103075403400d43c10900720340b00341c0d000500440d003aa110f030000c6031001c50007080c1c0d035621a5000c14032000c0580088c0324080c941e006000700506e0041240740420900d4082c605036031003a0201c40d0500c841c9005001c0c00d07201c003030000340164417500904441c3c0d44245c02a03081c8510420070340301c04913100c038060403d45504441c540c290102684007002500d444c0741007296044420300700207140402c100e000030740b00e8041e4000d10440711404c001040c00d50b41b103075100c40030480307004035035035160401450312074040c00b1807000d40c41140c078600f100030180e80350034401c540c000ca00c000e0941085101c2428180c03151091313030881503501c50f9074401d0b401c0c8a170820702c4040d0b1840b2400c40005400280c40c41007007582c14010301d1b20800c00800030010b000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 498335188 1250 498333938 498333947
    0xd060b0324250f0f14040b040f0807030f11030109060908030604060b2a100c211b0e04110c0a020310020307082e140103051311010e010905041112070f 66
    0x203c0403107840d2450f09145a560169000003d410306000001400500061040502c0003c0c10a86880004480155648044450355413110340006026021703000d0340d40700085c80130a05440740d04005400858000b58589481c4129070080e08240c69007031002040004034a4a481800d010b800d590100c0342c100a031610300071a80468500c0d260079945811110401040d0081001c9285803203460024003154080d100000d05200504251201d90710f0885500c4404111038040c02e18040c940c1c11024144040c0388004460b0b52000c580303d41e402943d07030302c011488000d00e80f004000e84050080100043c80040c4103140c0b41031220003070300d0f0002d0f1041c07091014460340305901c40c9e000b00343c00392000d069800c1c0c100c0e14a100351800340b1008042d010003034001a601f0101140328442c4600362020451566010441146864080030061424494450314003096010350442d9a0625061602c0c060701d0b07898902041c200c4424111415102402241164001b01c040101341c0d1300026a2528030640e4000c0e010150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 498336438 1250 498335188 498335207
    0xc01140c0c0c011416020102010908070c0f0b0406050d0513020d080c0d0e1810090c12060602010c120c05040b310f27150503120403020d060b032425 65
    0x17800000d94810401560b10035080021616000301045075030701e4141c80d041d041c00a03035200e80b82d022101054000391800701c20050b1002c9602680b52507280102880d180b00042a004100e00380309120f03040144056146c1c0d0300022034483c030070380c08a44d90701c02c0790b032095241106151105041001d41d020451817900c0e40e1484542139011a629110503460b09170501f01b0b60002d54100009035131405040105080d84007101d03032062903010348200007094903041c04030b0a849040d81e484022170030f13803000900c0071b090b5940314560128061815a003015115051104994002880c45108082003100f01c00466001c00d80c942c03000c00002410001a86007020030982946540308245600e904094030041c1c05041c0c10170600c841d00b000c00308000c401210b0420740000e200340e0003214000d104401034408000c040504950650f0340051200558007550b6683c00080c2040c00f00f080d030140202d0200c90226840d0030003494030200b000702903108a10304030003a810b40c159030381410751134040c82c2d40542034500d03000140301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 498337688 1250 498336438 498336457
    0x30f1406071713020f0d060e0d030b010f0f080f0c1308010915020301050a03110402090414090f0706020304090b06090a08150f16180e01141905010e060c01140c0c0c0114 74
    0x202c0c6c0201c1030030460000c1840482c2a45540a84000283c03051b51690040c05a000242ca5100185005070821104000c00f0403c0c2c00114160700003280074003400320043da074000404109103180510030400c61101c8c03105070340f0508a6079100c2d81c40308100540d291800d031260030f0040c030031411980b400c0000f44002500f844080d0880384a0300c503104080d00d40f901154103c0d003000d4014008020444c00c0b507008180c017121440d1060280300e40e91400715001040c05022270b00c41d0f0340110308181c1010507000040000c2400c0c01d81c0000200014003c544980d1038000c010070042001d030020b03254070000e00c480c0e00380040c07a0344640310f518001c000b8a01449008030304850304d240750064640d000d0b0142d004401e04c1980029041c3c00110000048044851401c001c101d801581d0701c2c0504c0200202016204041d4002c69020901145901c0d07410f0038000c014206003c0c8040001c00d105002d4890400030f80411b0f14a0681c0c0800001e03408240e110800c0840c00f500c0007880c080510000d02d0b460044e00d4020300c6500d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 498338938 1250 498337688 498337699
    0xb0d0e1b06030a150e04030e040b010e0f01020c1f02060703090c120812090d0e0f150f0d02190917070326030a05070306150801030f1406071713020f 65
    0x410440300890340724002d4044402e156140140d05c1d5544820451000c660131400600020b1110005040902403989000301c113840380d00c20f4010031401c010309103440008850444c40340781001c070401d980307000c404104c0743c6401884070703004a42010000d0401d100107203030b103040c14181000680000c403100d5800044500359030000c6158081c034500800340c0e100e0074401c00c00c070003c40810f1106210010440e40380460044d103d2110240e405014030070b43c44d0851411551001c1003041c92140141d90500900b118010080441c1c90050203051500403a0442c100c40c2c080c601034039890000142e08058140068500c00c414082e40020f48142665a42c0c402c3c000101210580c000704030007804038004038440c0040742c10061351649005000c0000404c02110707071a000904001000031102218602048903c81d640e036600b026a08680729040d4403402502e040710f1030307076005034143c590b03440c103001480c041c006a0303076070b090600c003c98008158040007400a070490380e01c00c0d541c000103039110711842a19580030b564 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 498340188 1250 498338938 498338941
    0x306020f07050d02060603100b090c0d0b0603011202030c15031f0b12190917180409050c031006080a061d07030c090e03040605030c070f0c0b0d0e1b0603 67
    0x124114000d401c0300405078454144810003c0d500441e00c54031840060f0200c5d03a10000b00000c05007a101280756554000c091140401c4281c0084030040079188002400840c044001d075010404591099200e00c044c0604d080075001146410b021780850030f101121101e8400b406000c00543d00d11000e0451807600c1c138440341d90b4481a00441c0704100620804501e00c0d1912071445d091195450211000010765007801c400644d04400e41c4144844250861041d04020076045100c044035480440d0b40160005001e5840005640394000c0ea0b030218424006410500da19006041c0740859600010349840c2c10104180300c03440d800201841c9070303600904080f410295001a40903200480c00c410092801405008414480d240d150501220301c0c00b0000c003c805121850a9240d00035400b82100180e0300f0004035014000110103050058040c500d21540d000040c1c0d07a1900790300d15540304210b51072011030740740442d02a03441601e202c5800e02c0040c0400201c50204498400403070101c99100b50030100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 498341438 1250 498340188 498340207
    0x8031f03171e09130f182f310f060f080d02070608070302040801150527150d06060b030420010e0d020f030a0b06030c0904051504150507030605040b01030207150b0f0402030a0c0905030d020304030602 87
    0x2020f00c6500341201c4020064a9105c527422000f6100502aa000e0740c0b000c1100064040400203c1000030829a0301402483e81003003012079181d64050720040c2016024040030130748035000e124031070078a0f404130a4454682d04d03003002c1c007a8018500c90386200050080b000d11401e03411408101d94040c1c0e184600d0000003009400080100c0c2103554040c204601d0100d0100e43e1040510081d230007a405022002e06c0303040240c03281500c6130b4001e005240003904403107d0184504004c2c3c808082184000c204c400d601c2c0c001c8012030700e0482010000d4924004800a20850782411302802c0c1580b01d042e01d02c4035561034076490300f44d0760b085020110080454010000703400c2c81054110150740500d0442c0c240f140d400c0005001303022b4401130180714030440c82d0070741050071503010f442150764643c1c4c031141d0854800c148800c48402441105189a0080400080d4601c103641e90f1000794425400a8000562249082c00c010a801c115230003060107940304c05c9034145c000d1340000c00d8a0450350301c08000f507aa6103104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 498342688 1250 498341438 498341509
    0x3010f0524160f050607090e0405210403050a150f062405071703071d030d0c02011e09031104050408031f03171e09130f182f 55
    0x20101411941c205210a0f08100b40450b4641c00358030309a8980b2800c2c0c2d118004101c4050055134000c203941d02600205000180740c403c1c0c49007002da4050703440e0400e6903a8480b281040041c04088601c014550101c103800d40b05840740001d014001c1104200c0b1b1400c14000e09200e00704030045042c405841c0403100341641c41802200c14641c0d00070300c041111032401500100a40064500e0b40204d2207503011b0a1018509540954058030020010b050b035004480090340c16184040059042140101d040d81c807480c4c200307843c0000809507644003d00141341d4108106192445d0000c40c1c400c604280501001c5029002a82d40001e107000804030709262110704d40401748015070008012100b00341d504000122458041c1014008241302da0040031100800b089680c403840c440d5503801084a0f410b08060106c55129614401c140c8c000040c250741d0000c55131100202640c401ca0392010408001c4250300e0143d11300508082c19203003001f440d2a0440000b4081d0b9081c007600110030090000340b046208450b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 498343938 1250 498342688 498342727
    0xb1e100e13020a08040302010c0e0d08090109030b0c09120d091701140403030209100801030c0603020d0b090103060e120702150309100e030a030c080c0f09010c05010c020303010f0524 80
    0x80701d00440d515400068041c150990864054000d940380c00c0c41540f409010f000b8191a070403004100f500464003a954255194100c070141c90b040054a41010001034801c64115000d41044502c1c01c0e150001e1380c0030400014007a04070316076150801400c03207105c150040442400e90f5104517141554081142a0300e00429100c0f05a81c6048030394418002810b401d940102406001030324075640c81005400c0689030700400780300c001e2101c0b1751030f0400c00c40544250b0150054030402c0401095611005000810300f40742a04152074160b560b200a0b540303841c0c03c1048240c0005421b03480c3c0c0c1085607a80006492000004640b4081c0b4400400030301509014000c0c2e111489050794100048400b61616076902c1e0040d40200c004680340c2645610310a0140e0595071041c0b5221700d5283c86c0c00302041a603511500b00108142c180244a4aa080003590038010b410114076554001c0d500c940c54003c1c5407000301040d60060340681c6d42c0c116003502034041c000480300c1b00c1c030318190700c0b5a55141d00500700b00c00108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 498345188 1250 498343938 498343969
    0x109112815020a1a041e050c011d0d14060919061a06071a090c090c0717041203080a0b0d020d020609060d060f05060a0813030203040e0106030b1e100e 66
    0x2100304d090f041841d081509640101d0280095415032070150410380702c03000e001c00c4c002e08141e1122085442640c0308658856809248100c01c040300d08140004c1402e413148031004540041da03408100300d031100c00300135495000c4c000500401c4050b0380d5101100c016035a07204068400d9031558404c032814003514804610320b29019080980d12100350078400340c00300c20030b01e54845d20001368011070310300500050a4948014002c05071420364582050000d0564130a600489080441c84e0905400e03540e544090001009041902c13003030705486240040002c1e100406025080b480d004400105844002d0240c3d48654103840728041120b85000041440c001c100d05983d00c0600025100581006500090101c58040041880c8143c0354020442d0a00510302d9005c005250440042e4498250800a850280c007a0041e21302d4591104e5003503010701002d81016001c6070710b50350980d03080e06020050782030881c0310302e000d2070090310b41c03c002800780b4410034074500400100380c92600c0742c4d55404002640d07404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 498346438 1250 498345188 498345203
    0x601030204061d010327152315030f030c01050702012d0f15090608010c08041b03060c0503010e0906060a261501230d0204020d0209030109112815020a 66
    0x1e480d040740710814600035034200c8240400074401e0343c1400990040022400030401e59a082c1c0c5044e41d030064440038010700c40b10001158a000c284292001d01403074200c0e03c901d4010399376a204908015007944e4000d0010403c43e03140000d494581d420941400c0390094680307a100d80c45644003281400a000858460300b0b07200d05c2e000325907801204141103a07013103801002e010b011403030b500c0483c60b08807002c038000103002c00d82040008000414403265810904202c00391a41001e03125140e0400301d8290a25450100c2c4002005100c03887c08428201d80c840100380040442e80303400c002280b541243d45c82060103211200110806020580c140e2914582514088a809150511440e91242400c2c401c0081c1c83d00610f5000312b00c1716011801d4506190046c000c0d2031b01c100c0c140e0038400294070030500200116824400b4041603602805402d02c0ca601404010304440c00540800c040c0900c07411110034402c00b0348051444211140c58807100300d07400e601c010400d134441804243d0408080c00001008403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 498347688 1250 498346438 498346481
    0x9070b0a03050c120c030118020301080a080708041505030f06040b1e01020708100615021605090423100501060c050601030b07020705030607021011180f0112140604050601030204061d0103 82
    0x4d00b501701850486030341d1500d800c843e003842e201100483c8420301802c0d841d03030011a0020081130741407004080d894840c8031918902940c0c0c40c0c9140711342a0049050000810000902c1186041040b8564000c40121001c100880341403001643c3c50280c08017190183e504001c072003404d0b0f8001d102280003820784c801510740200c2400300400c01899a0b00550080c80905054035001510004592413600c64000d460100d003420041004010030000f8000c8803104004011004001040b402142041819a0007011801e444401c0c540076100e050304410304100b2140400760100e00002440f074110b0760044040c5441d41c552040c01ca0030004c076a040300350184102c4091149140e40001c030b90f502c00c0003100c801c0180401c10b6000078102d215084034504242d940c01c51103101c03842c18040ca0003607000d05040c500e0302c01081d031290100343c88540c0c4054034045542410468541014000c040c0c2c004c2e42442d00314a018186400686440c149000141c0960000c981000b8aa40a580301880d1150303842d0040291 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 498348938 1250 498347688 498347701
    0x2041506030b040e0c01080f10050d030c030801060509060702061c02070320120724060b070309050a1a0307180e04260415201509070b0a03050c12 64
    0x41c0082004040c01146007030880014a080410040c40c8100c050307460a0460700c5501f6100c04031803010340500002c41038027000181e9682c0c0c6c0800c03010b82c0d91280e22403994080d01428084c040075030590141061100410410384680e071941f08440c45254111070a545420f0070442e079054171000030185808030703440060981e0900d80c200c4001800440c100e01c008900c02158540c003030319501e0ba09580e008050342444080d00003110b25450300c02854980c10560040800c000031503090310490b602041820100141000a01d40d10401c1c02c40030b020140c9500403498607002c400c94520f168082080c00301c5401001207403102c0d00c20300241214140c1c0c50088030445855000c0d41407180c0c0186d400b140c0f074040001c1c04815a211004400041c0b4000d2000c0c6401c19280c0002c0100038030300d45000700204201f20140d107406000b0368060b00707445203000c00244415400f5002c6244031030405014810154044802089140b40d40d5040750f44480c02c5107000b060356200c1310280a0940150f03032811002885407801c0218 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 498350188 1250 498348938 498348941
    0x30605032d01090b06031204050f0d0609051204090b06030c0f0f1e03150d030c120e030619061205030406030f0605030105090129013e030405040f0b1c0204150603 71
    0x4503c111b05460421801c0c0010316000d108a100d056004035820f054400c16107040300100d010f40d4061800415030001039910705082c00d0131041140040480440d050100e00045d03c11444403400c00c0e911a45036042c008601d0101740030307201d074002c080980052180c10568408040e41ca5a80340c1e040100000f01e09240846105d4100302d0f4820040d801b03000c3d080c003440c074003e402204101c0e05130b12990b08200960315510b0411708051584e0062151504d01c00707403981c6041001c06d200704920f21220320340002c220b54050030340b40664090190390005512030404504044100ea048070901e0400141007061f0050300c002a100e07903071109070705519010420040a0064000441843c00107003003600b0343c0e43d84074900500741da00d10705090004070f80d0700e0301400411110680ad038600f100018007140da0f000c04011184914001c03103c00b1550f4002140c10484c50a050140307507501c900500040c05882e400788040f40c0e001200341c00359042410400e200c4010b648655101c43c0503034802424190555490324405070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 498351438 1250 498350188 498350191
    0x2120f070f090c26090718051e013002060a02010510050109080c091e1611070605090f0f03010203070504030b0c091507030216060906020d030605032d01090b 69
    0xb400346041c4002c100f002442078080d4604031008424001e10102e078460020074064004001d04080e01c82e009011030b43c01412035121211242010010442d0b150007a1040b110048806540d401c2244010060081c991402c4100700f000641d0719031050150900944468203480c00b4801075005603000840c8881c0030307810b401c10b910650505800c030402c50340e9440110340818240c49041c0c1e2903001940c440780c0070319044403000d401928103150441d0220b6045030344824420161840311340405005aa14a007a0708040000c4155017024040d25040e468248003610720b1007031407400ca1081200400c1207003603903100e5070603011541000e40210f40340d04c1c11080141160b407140c002070710030228900c00030720f590f44031504561a000300a020468004a0403200d04150340140800310250f000d6170304030018064696400e10000d0016648400e0402d243c034401a0400c20240c0354542018100b0a0920590b01c0004804490155102c00c0c1c640c200300310019104842080c0300361440365401c0813402020700c030361156246d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 498352688 1250 498351438 498351449
    0x306051503370207060f0e0c2106180f250b090d02040c1103071208150a0605031803040e060a0815040816080a200d08010302120f070f 59
    0x2c1e01215000e1400412412005500c1c41140b1a0801000e994049607005040c8840c400c02010500140c2c2030319140c2601d011021026190348071003509401c0b072030a2071440c3c0040501103c411001405200d003680c03034800081c00c0c900d00c01e03012081414032600c00c12484d0304c3c903d009001c0d02d5400754141c1d055100c511404081480b40b040c8500089400031041c0c0496580b6980101b13405800c1469034240000b500d04880040140001034042d04490001813005244583c8556421154072000910191070213070040c0401d8144000d600402405850700010130013660041d0410b1600d9075200040007404455030b400ca094107000c0443d001491512680d032090046404a401c05101e80c0c41d0310303e0b2070f51380101e000c00c14401d6003603170082400f09203003c0c000c200c682002a40c211000c0425202e5030000d40c89524400002546000e16880030707406205001d40e00035412024040201403918028540f40307060002134031a90182c0380360300624a04206003900d00e0b00340415200190365400d184030104d651032159 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 498353938 1250 498352688 498352711
    0x4060506101403011e17060f0f0f0a200408010e07090507050412030c060c0f03140903180301090605090303160509010921061d0c0603250306051503 65
    0x2150301d900580900d0702d44a07a0464540c1140c0c41d26001c14502c8140400a203450601d0a00c0450b940c0c0542d810f03010303c100380700005e0410b8180300c0c10489040f103004084004107003146081c00742c00f00151120ba03402160403400072490480900b20700d00c1907140b204141c2c00c07600380020005030111064210201c00200c1d0019112a581d561810801740c038030844031040041c40420061000381c208030900501c0500034601200b07000c08030343e04c0804880000ca81ca07400f2450414589515603810b000304072100c40c0f40100c80805040c2010050384e42e008211800c0c03150005070455044a0f10300358401c200c0ca60b00b025042c002410304a08040c0c80394003c1e9520441c81092101c0315000074099000c503800600306075106140285070840c145402c9400b144090b900503005094200401c0032809000c40044040603440c250101c8c0d02d00a40c60041001080ca02414082c01040510000152480c100403030076401a0515020303804124020203243e00300c503511400200701d107a840003441010318810595002c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 498355188 1250 498353938 498353959
    0x1080d020124061b170325020601060e190b190315050603060d170a09090614061b032b05091f021605030903070b0310030f0f050604060506 61
    0x145089602c00e18105035022440c2031030420807103200703000007481140454521562008607590318112928215030a054401d00807007800f600040300100141c0d81d2202510b00358000e010030728082d480c2c0340c0500c80c200500c214004100700f95101c0c402c100d4502480c003d1000ca01702e444a0300000180c2181c90a800d030b000380d8144001069000c1e10a0702810001d407005140300320304c3c000400003203500c014082030304203004503220030005d282d4440754176000b035030210324036100c19180e80d005081d10081e80c014810703c0d040c803d08000090101341d1024030400f0681704036a6078030071078818040c400340b40d0080703101c6880005500b000c6652001143d08040c000d6002c1c980580210ba04140b06031003040c1c0300040a40c01c0a0309240c666021a1890106800c103000b000d4140601030b101e51006a01c1c2c400d0a4032150800100c00000d841c080c008580544001030580f8194103000c4241141c058090200506da0700e08049031000b03020881441004c003951040803201da5160925124018142c15a0342034041d064010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 498356438 1250 498355188 498355211
    0xf140708100f0c14040e060411030a0c0f031a06030a020408070b07021e130e0f1f061d040609020a0506041e0504110906090a0e0906011401020604031403070e060301080d0201 76
    0x1424084001607504065003006c1c105184102010409444560f0059861050751172070041e00c4007544c0b081a0030b400004281c0c266100180c20b84089071000420145001c4a81c01d0120b1040d005406d41c60003541e000c4e0300ca43d07403104010001d20568005e00024400c11000050a4600c0002088001d00c25103200c01ca000305801c048608007000f01e5074175400510301b0325404040303502d5070203a020000404121181c03a00e6102a0310f00b000050180d4034002008200406406000d50007214004e00010705008240194801e041c48802000380000740600e0301c0c1da41c01e205554a001c091400703064001d0100396500e540390080c44042c804403001d19a590714070030000520b45001c1c030560f01100d60120f24103103071807180c03020845c00360300000710302d60300c80d02605010801d1502818035034894002c50000706000d504186407801d21400800c1100c1c1198000c80400001036400a010460407000c2c030348070742d141e4440310b00c1501e01000800c441e5401100103c000140d0540000d482d45007110242c000308440302c0c0f040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 498357688 1250 498356438 498356447
    0x120601240c110406050603070210051e04020105160803250207030c09020f0c0105090102070507140604051005120c0a1404120f030504030b0a0501030c0506070f140708100f0c 76
    0x8004100425116101040401e9690b0801d070215040100006000b03a224030000b0120b40068500400607400702e07604150800840c4500c40c1c10002841c10701400e0301c4040c44491450700000c00003410000003040100549034114184205140e0003028551280340c822252103a56034249103e1010005940288544600100742c4070f0a0300e030015911500c140c01c0200600295202d40c050461102c001c20034030300403050a20440340900c01c50303c009640c3e5141400d001d840c05d40750f5040035955600c3c401120b120395590000300c404031082902c014200f43d1110400303a505010740c101c08030f41030030180c04000009490000801d669081500c0e0300009a001840d1104036000e0303801200e203c40c1510340a0400314070340a2030b030f08035184070b0310b40b035403400f510703543d51003c1c0790b000382c1d60030400d6900c030001402003008a444101c0a060259075407402d01945860b02d0302c205c0b681080250000300800301e42c640f40b41081c04014082c1981c0c40807240454036441007003000700145001d40c0c0d5020b24200c0c2498105208 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 498358938 1250 498357688 498357749
    0xc030d272d15020a210506011112030609150d1203062102040b060c071202040b040e0c0d11060403080d05090307050d0e04020d0f0b03060f13030815120601 68
    0x401c921041e107000428411000794401c908510501c9000785c10f4010601280005070300c245d0041101041034180840050440308803030300c0e44c81c1c80b60441e0030755400c40260f51050341e0348402c00315524900d68481400821641c511000340a400020030540c481c10f019803102c40000e5400c0c1130317074100b042666580c1e092405500049105505115a05e1120003524054208020f0000c00034a1145024000d1712120b1400f1440d501c000da5619100584400354070b881e21410200c004161802d01612440140711a110044590b010b442104088912030600c41d000390b1880c6010b0740904103a5603070742c403402e0808064004481411a40707041c00d0000c0e5055102100780e452407a401402001403400301481694513190059400790415030034440101c00c144a40200c890f180301e0074800042094408040c10308100e002407200340076003d010140210b041078001e00e072105640502c0c0a05840c0c840c180482122140c0020b040d42c8016a90700d0001028008039880b030403540d041c4194500d4a90504800481c6540c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 498360188 1250 498358938 498358943
    0x10305130f06061502070f0e190f0b03251a030c0d020d020a030f050906071b0f020d0b22020117060f130516050c030d272d 54
    0xc00250030008140c0303001621001e101d10004076007552036100c1c0c0c3c039060f81060300f1000142d10140041054840c02c159030b4000d0101440061001e01c0e06141e098589070825140c5583c07142d4814600001159540c0214114840201650768422070314082c4020881c03414508009108016070000d00409a80d8030a09540c40c5140014150790b9140c1031b65002d41c22000d41c5c1c100d5907401704030071a64120b5504c000d01030340c4684d48001842650000154084030002480c20312990f0005080c40b04560b00700d004c071040080106404004014540b030200814000341074020740084000c20904100b080344080c0d9403181d520419000e485006403001424411480100603000c201c00345400d90381c944042902503400040a8001d83c00f5030350800c042044c009044038121040c1c6d43e07440500c805000c090a074041000b00c2c620700315050040c001080e07901d900c1072a00707415585940e024180054524a000462840d42a1034025205112810421043e00e11040c607036584568046005040103a130001c24050580c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 498361438 1250 498360188 498360211
    0x8010213091401050d0804030c06020303100e090606060a0e060f0c011104060f0c0218040b0403080105060403110d06110408031903020c0309010815040204030804090b06070209040f020607080414010e010305 90
    0x134a00030511181480c400000d94022004010110100c1c0ca013030318440092000d0744c01103940349010000705241684c250403400e016520841481460b280014526030045000c84049070391303841905064811060b150859608400042044008024810040d0100040020003844140300040741e55607607100310b006040c0030034204100c00c4102c520071010300600a01c068209020f40341401105425404111411520031042c1003c0008169000110717900409054030303100c0c2802c0c10340d074070141c503892500600c0e03000d048403000140511101c2d40241c030304401c3c58009140c2d540e4847c080c3d184c8136801200b10304114121111a2070f5014841e00c00c8501d480c5483d0055410700d20100011a01040c001e402d201032074250400707000c040e6540d403005100541c41180000d540303502e020040c03800c0c0c818001388544550420300c4228056119088501e50007607020ed04410000d1052000a00c140100f10002e0050303080810301060029003070951880c044400d0b03c802c460400c4540c011002e4400031541e814010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 498362688 1250 498361438 498361441
    0x40807030303090510110a17070903080705100903090e22020f0f040c0201060503010e0d0c121b08030a2d0e0c100306180606140919080102130914 64
    0x1030b12070b5204040e501c1c407890540300304560b040e101205407001050828a88500025410403981d00114802c501070100313880d602072403a000f40b000c4c00003c120722008d04208030004168041200920030400c240c5082042003101a60905004260801030302600c0b5401032144085524160700c41035030519002407010204aa5000d40d0034402d54010004030640c000607aa4080e1342c855846024116400715140c0c000104140f43c141003509440703006100403800c0d0806a505041e43e5800a42002c0e1103030411002a60f0292400d0100c071506001c034620801c0d584440c40c00401c004240d8011030184071410010f200041c20003440b810241c2c00016080284c0d25050707600f000c905200c0d04205250380c480429190300703a184001184411007820500000690b48045c20302c04025495105e10542c000407038104450340c10060040c0661494000100b0094004140c0703000d2a0b80c0d07041c10307505142040f0300d809401ca5071079101a020b500007a40c1c40070204801c00700410052a944101d2180c1d00170700c415228030303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 498363938 1250 498362688 498362693
    0xb0106090e220302030705060c0d0b0a1202040c091d18030a021b03010605090414011d0c01081b0a12050c09031207230f0105160e090705190509040c0504080703 70
    0x20014400c82c1103007903000601c01c440100b202400021310900c0c101180c02c0c0d83c0c01245408400300c4000d0784111748107038003910042c09a800700c180d80f4205503506a40002c1c0c41645107209035885500d59122030382401c0010710000c100009154880c4c09100d0003000c020150a040170001d44034044c619081c40142e10480c040228401c215400c1141a0b03005400005c0054a07403003c2150440d00312400c3e200712541d011280d1203071009104400c10085011061015001441c9006488280c55030a03103041040407004220580c549490303e244554003000180d6540e0401e64004d071402039003002c4031200720b252a0001e0a40c0d94450101d0b02c5405008000d00f89481035100a440e0303d8100d00c200381c49840d10840c800200c0d000c00d2501c000841882030080c41c81c0d034200e103401425950014050201050104220310b45d95810620100140741d003290241159902c110301164240988060010403044400c005507215400c880240900f42c400d23602801200f1403820280d48900ca144101010750f4400d0404002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 498365188 1250 498363938 498363991
    0x120912020108042604031a0a0903080c07110405150301060501080c0a080c0c010903111009020d0b09010b1f090906240c08070b060f03060903041a13030b0106090e 71
    0x10705400ea003d80d16040c04010b40c9641034210b50000c80c6d01f8104200e5501c584410704421035803064103070a0a00c0041c105680092114002422001000c64046084010002103608281c042d4002400c200024984240071008104241c05864007035480c1101c04103095201e0482c0e07611600416100e585003000d4480304a41c1d0000c014805907800c6403c0c0503c0d448144207004030507029000340e950341101601001340310704003121403d201c50845d2030101c0d920016114030136000c210030b410840c10016641d400d641c07180500305203100315601005070740034a01049410f0080c400100f906903148034140e900c84440a0448405008142d080d161040041e00c40030445180080707d5840b0340f0345205a85196074600d02e65400441e01200e007122810104130361410640c00c1c01e0b000c000114003c0401e420047d80140e180d109034003400f04601041c0b020001170f0640500ac03242d0194061021000181d900d00b04400720480070300a250001e58203001c00182449040c82183c042d050007400c0341c3da100790140f030030352 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 498366438 1250 498365188 498365213
    0x909030a051b03030106080103050601090204031e02010203130807150e0d0609172d0703120c1110020406020111070c14121504060b0301090f081806030412091202010804 74
    0x9065200b036281c0204280030901c051402440151181622035045181c0603051510582200070040d1040c001040031406510002d04881034000d00c0c000c0c102102d00040b03003944a0740b042804400c411200004050100042240403a59135446080e003c0090a60803130303c060754071250607400320400e80c00341c0114949901030984a4403810050407541c031000482c403080e822a883c08560f060210894a0140203c168050b441a8020061a00d030403c5580c001d071680d00401d00c040c04059175801420f010a0055001140300e00d15042200c01c1c40080b031180e200a54000d01600700154200306a03108607101d00c100b9144100e62002540040c5424003e03460704c480030203450f542d07001900e9000072036180000d00c44c2405c40030303002950700981c1ca420704000060300c0b0701d840703814081c1e80362800907400728060051010009038004220380c0c1d1610743c030041700c0da500001c51009910000000900003005200540d8400b481c01ca519455503995a8030403004810003080ca01174042000d840000c0c00242603c407942 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 498367688 1250 498366438 498366457
    0x3120c05030c0d0615050403020a12030518030102221406030402150d0b0405090a12050408100e03090913031404150e0424080f1c120b030303070314060909030a05 71
    0x4100e80c1d071743c080c1842035644450741004207000180a00035414220348401c00b502082584a80c0e4001c1d945e801006403060080c03038040180ba0601c0000540da00707404559104d41d000c0c011161030f00c4580d0308a5840c012621414030803501b10081c0500e13900b4003409480c8987e030001c0c40c15440003424290750401d98031951a10b1806075944051110302c0c4d1b00c5100d198021003d040082c46606c0480c80c000c100c55014800c21002c1c041c09200402c808000060781c004070011003c1c000c1201c4682d0f101c51860360003511940e1b5401039110303081141e88048844d10228240c069500d00300d0b10703071258803052540e1183d4011480d000c001203544844d03150052240009039a0041c000207403445004402c0c042d44c0e181c251000034030319100401040000e908104c5401801080320280c920040103240e010b1200c0c600d11000b405005000100c282c02c4815640181140c00014080d01e46d20702c0d0010380100105000c0340c0307242d9840e4040000c203202d41042e03960180300f100c2c02c5000f503103019400001030741c01d40c2081940 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 498368938 1250 498367688 498367691
    0x503091009060507020d0c080306040c0c29100b1204080d0f060510030b09040308041502040b03190b030705090a09080f09010305010e0405070308030c1b0a03120c05030c0d 75
    0x4840300d505441241d200078001c510004a5080009000307082c000300f08030000c20030219011141c0412501400c4907009001200c00040200d8a4101031300c1403610a40c0240030303125441000d003074840800055110202c00c8001e0035030340c1e41e11141c0a0b070138140310380200350323400c00288884044030304000803941d007040c015280c00d420b0072118104101039032440100e030b07100f1549820040119050018240c40707a600d00381820701559681c0000326402e004000d00240401205101140601001500c0c80d02442c480400030f5582d10b03142c200700340c1c00354421303982c10711428406980e2051480e054072855940c0c20005002e81540c500d00000c00c070381c403200903002c3c010740c55481d403a40c80004c03030709002481c1c0340300d04820041c0c440c104200058203c0e94142d002c854245890b108210024030b01007420030960b036100501d0b036202d403511843c03040715000e0300590725076050004202403105480065201c4c155840380d075500760400d15074440c1005661070401d41b40080f90061001c85d0071204400054091401035600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 498370188 1250 498368938 498368953
    0xb0a0203030a0213180608010b0f1804060b0d21030207081803070506041404110903060115351b0a2012030a0c03110a03020c0a051e060a0b030706050309 67
    0x1175401850305220354038581c450303482108100700c240a005654005808030340280c200c444400100d4a8801158800503031000301030f0001b02002440d81c001950303981c02425407288500e6074680040404040d0401243c0030020148491040703102e0b0080301c1c4210381c0040c0250074a0203501303a240710000a8665240d260268501c007080c3d42d12000060310052244203d1a0346080b82c0109001c1210080c45034800c07601c008005d004007607200010080c1c1180c41c540501d2892400c8018110703801002286c2c4603290000100744031032041c04807581c0f144000440d480030101d40c0c4405d00e000707a048070140d031849102c0b082800b1300026903018410303240043c40040c0ca100c03401e0f492149503034140354401c0138a5103104004407d10181003030070304c500c012740e000f03d040c2040703a40d440501c241641c1c00b882203900209034000851034401d540074400c800b9241d030f100b400c8410251210300240c50b00810101000d50612070280015120308660240c40042c11014000d004141c2c101316044916601c01000c046d00d0b446540e6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 498371438 1250 498370188 498370199
    0x6131b03050d032903030901051309021602030c0108010311010f0302041706070f020d0c170c010e1b0405010e0105010315080609011a0402210a06081609060b0a0203030a0213 76
    0x490303442c0300a142d400003500900c02032003242c1e56100c0d1803400d92000140c0302400484d140001100d000309424205581c41e140b5043c138600078501c0726001410304a00109004526803ca8140300130038074802c4090300c03c00c1c0c09aa0044030000c800b480081d103240d41c1072550307840d254010045820b28850f5842c015182a441d40403540074000c0d080143c0350350380d002004000b08603038050580c480031030b141d00c090a40f00c9448880105084820140038294070812001324035007940c8441243c41d0002214002d00c818168125040c0c0c0b20f280000300c154040035103d250400c50314051160314141c402080501034030380d080c880110020300c4c02202d00050100e00010100309104c080280c140f06d080d008001060025402d1000b0054403c41080240190300500449074240205810341c100150101c0f9000350581c0d60740f1065000c2d00d079a520091050003510241402c0f190b06c0e1000f1003d4803502401070061999031501121140f04001c42440103070418030200d0b84d4140d00341c00403c45e2040c294101d400e06512036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 498372688 1250 498371438 498371443
    0x190b0d050f060103020f1509040513060e0d030e0a0308041101030e0a1101090905060f01030e1f02030609070504030203030a0815060a08100603180209040501090c080a1406131b0305 79
    0x3407480380c00c0d64800001001185410b00c0d1400c1e040c0340984d000d040c103210280c942d40250103084001481180c8500011f058043c1d0524015074064100a0038028241041c0da11a142c001103c103010002e0f007082c103140f4010800086500f00c0c06d44c1039445584d0b03640c41c1e485404a481c44048000c0c10151617012503480746900700300108a0b40c3c0903000e900d050004801c00503280076a9903010319007a5003050100035040e9502e41d18a03540319000e007000718910703d801482c1d07030803c2c503590f100000a0015a003024440800b581c0a18450b06003514113542d05d0b15070000c155803a004920000394550702c01c0102c000700c64403421015821810244408030281c0001d000120305422820340d010001c3c82440c204080c881c01500c40e0001000e150404100000c81d00d410f41c040c0c0c1c082c4c510042e00640f851301c0801c0422600f50300a445060700000c00c3c0b041e560b202d1b011aa200c81c1000d4081d41e5221414615910342c08003c00c803c2c0c0110b81c540e0f00c8400a14003903a412940a540a82902c80b06080f90b80010114070203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 498373938 1250 498372688 498372703
    0x2403020f1204080423180912040f050a09090b0c13080106030303020d1406030c0d03050903010606020d080702030405010c020405090f0109151a060a0e1c05030a080f190b0d05 76
    0x65076401d034a90b41040090000401c0e100d05030707045482e0038022050940c0f98603a0f0050a010788070300106c0180e03609041c2d685010b0f000c1c2c0b12282400c03000240052130300d041c144490180c900442c9d103488003d03603900550041d0f0350a444080c282d41104000300e20101710b5000101b140c0900c25420f8030f481c0d13545480d081d00311401584140d0209400040028081049204044600c803100702c50b0300c11400e200002c00d80c0c52402105c0e25024040610810342458002c805440d11400002c0003440100e8960304c0094a030035031241e0680100d140440400c1c0ca680c004015035081d2001a50307064042422a02048041d000c0603000e6002409203080c80c40d042d24082c040c02210070300603900000d1145001512800b124005208030301f03102c440114401541c0d48902c200d503016030041c0390100c1c54040c110006450380e5a5600424070580c2101e81810401001002500c00000717a51642c8034259035034102644615422124402960100481c41c0b461002c1d07640004400c2d41c0161282c0c021102c02da4400d49806030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 498375188 1250 498373938 498373943
    0x9030708070603091103150c0d0603020901080d031d1c120510050a080309030a0809150720090c0a030f0f02040f0315090309090e0c150d062403020f1204 67
    0x2c645090405028108003c292104020b1b00106070081440c090104984005081c11415a0001400b94020549608060003460700201101c2d0746503922500c188c1d8036800f0a215002090a100c0c041d07044034920340400b010480600060300200071103031221005140c419a44500784541c4e0040750b5510003041c8252407250686070284a01c1ca4140020808400710990100000350b10401c0f1a20b06500d0104000c0703c03884c0d0241c01207848200403400a80f000fa10030341c0300b030034504e0041101d0040c032180000c0711000c0c0802011341d60340f001c1040284140320b80200c4400345200020030401440b0752003030344030030403102c11450f0000b1400c0c0403030702680680c6c0c0300f940502e5a401d08110140148940c1030004117201c41c58030010080c00d84d59640c003030840f40c003901c83d00c4100d076910010001c5c2c070f000038445180841307402010381d826100c3c1d0b958200c01507005000c1403203981e0315118004c50b980583e5482c90149010504809050b29a00700d411000b0b903000c0e6403106203916040c011440010101d0840d076000d40d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 498376438 1250 498375188 498375191
    0x40213080102071403030c181c1a06010c020f1225090608150f0702030706020d090b06030c09240406060c0b1f0b07050c18090f03041a09030708070603 66
    0x509074204038104d45411107100910307400400034840062200021074421000c1905c03e804d05e160700ca80003804c84000c80040c0710000f03400044204c1007024110a1807030303a044990190489844a0004659941c51030780002d40004803d01c100501c5d10b8000e5400704400000320481c0c011320300c00282c4036074041803001580c40442c0032400c01e00040707449000d03010160200e200240341400c4482203081c007000c0b010b0074036a60103001d040441d0550f40f00380101c0e50400d822541c150768403845000c81200502c5031030800c0d07403904c9032400030a200c2d01d404204c603d800c2000178105d181c90344400011484217492244d00702048440d4102580c4140c9460148400906140d01c4041110525080800900100800030720814103c0034061070388501d6400d4010684080503a0541c540134075250481c1b912110b02c0000780c1c8041614149242e140c2c00320003e92055000500380d8911181000c00e0690b203026900810100c6842c2d10044400400b042c0003401c0e20810060072211144c2d03444182e0b500703101c03064001070f0020303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 498377688 1250 498376438 498376447
    0xa050601180209030d110f06040c050909030a020a1209031506030605010e0403020d05070609150c020c030c01122403030e100f0c0b04060e010e1e010603120c02040213080102 76
    0x80d1041d48500d4441c071264a000d616014403d0b0020b030700c0f8080101010103000d4002c100c1140d58004014400035005040100c511906081c200b4022007901403140718801c0c00c00700000340703d1140100a81c0e940665503001090311460fa1b65450500e495885503000802a11000000105034954401c18840c81c940c1c03030001e0354a0650a0400030303210141c2000c00c030034010b0003e00c00006d0b0300203910b000c11040e5245c05a191482e602e07250014041e56040039000e4400442e841b0700006095102c600300324916000c0f0390a03c14031005058a80c000b181c00340d4080b80006004900082c0c15821070082e00b6480842c240d070300703642041200c0880c100e40d001500043c1030640500e040b800c0c1184452010041e604010061040610000340040c0c210403008041300c8084002c0346c104030702504030100000300308009006000544440a40e0391039500149403091030480b4030390104c0d20040c81407506881d086418144d9510200005503802d40c8004012604a9401c0140c852100d0203405642c01502c101000960384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 498378938 1250 498377688 498377699
    0x605090f060f0301140a0c0c0305041e090903030e01140606070f060b0303030c04031109040c06030c120606170a060509040b0414011406010816090911040f060801170106080d0809030c0a050601 84
    0x8a03047e0b8000c03081800644040c090100390000191011281c018a110089442806c0c0b042429100b90b844508181c0c1880103010400d9010f4000c0440d0035035000081120615507102100144011364000350004030420001d0003044e146459585e00900604000c11446900c00c00720740f4540c811281800c0020b0701040620404c240740032203164802c82200d0b80020340c1420707224820141d01c2c61140100340340d40e40070484441400741078000c001e000f080344104100f641e141406000d9040601034080c1400351000010292009403203440140d4002503c038072a203564560304c0d5012581c001c0d0068518240d900000d40488609020b0300e074091222204244d200e0401a0014101d82c40292100030b441081c003401c0d8844a41c820f00020444032503c40114801101c5000c01e40741d80320310f4110b008081100c0384080340700c80d00070200340e04030b80c0114584421501e070000308508982090090340455001080080d0001d0303ca107400d0350300142010103a0b40b03005074038a0a00d2400b40803980071140c86e04444010801e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 498380188 1250 498378938 498378941
    0x1021c02040f08070b2a07030c090c09141507060e01090201030b01210b13020304080c1c0504060f03021903140612070e1e07110d030605090f060f0301140a 68
    0x82100d00000c16440c0d042c0000d150340d80c01b401400c5070b0101c048050010340554504501c4e42c80e031805006951038540c40f400c288183c41072034040c42034128108040548a24443c002607021100c242d440c18050388101070411405900c4800000210482070100101240341c6100700000103c100000141c1d2000c00c1c0700240603a11480c8405041c40981d24184402c11000741000c40d200401e00f1002480500302000104804031800d5140222071010041100300700d10701e4000c00914540004070391031400301008041031899182c0010001500c00d220803c103803400b4264410302000a410051700341101d8204113201c41300b8001c0110700180d1280340d20801140291811500403209403847c0f80712290b6162003a5446c56284610306000b00880c0000f0899001030100d0401c8e00c903120682841da007410034008017846551600c88600740117802d01050502d0003880741c001280c1e005460444c840e0784440100300400e10040c02d00790071955141540301d60f6034086c13041d000b03403c0300d0004849050418004840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 498381294 1106 498380188 498380219
    0x2003220312110705011508031c0605060f120105060903070b0c15070804140d081504140109150506090105160501060510091509062001021c0204 63
    0x20110640b038002000d165000780300910091245508208505000b44160b240340d501c204090320155003103203d100000441c4800c0012050768440c0455010742c409010300780003000014041c50f2080d10b580516002d8002030b617039035003490414004255110b485014441520701c020071001503080c0100300b01660401c85c1001550103003070040d0042c040140a40b0110382041d400704116554a00c00118071050701001d40d1070751001c1d2101101d110600d03412001c07484d0096140c0380462065903184004900804c80325000044030540d600d580e00084250341c01c03d0744a9107003001081e8403aa8010700343e80042441d074140c0c000d0456603241650060216502060700007100c050010b00e0a03800144101c02c42d08030b001c0e441c80c0c409100b102117607005898085d0038089100905e21220404000340040030040d40c8400042c50659003c6503030004402e0080d0304c1d080e0b1b0350002001c1c00318410704110507 = true := by decide +kernel

theorem cover : BRFrame.Cov 498201438 498381294 := by
  have h0 := BRFrame.cov_init 498201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 498201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 498201438 ≤ n) (h2 : n < 498381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
