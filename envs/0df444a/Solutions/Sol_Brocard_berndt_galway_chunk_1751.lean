-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1751
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:32:47.57719+00:00
-- url     : https://prove2.me/submissions/5d3098ec-dacb-4455-acf7-605b17724902

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314748201 ≤ n < 314928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314749451 1250 314748201 314748209
    0x2071b03020330030c03070809010c020714010512040f0b070e0f041d0d08070f0219021c08041202090619030213020c0f0105011d0415090f080307020610 67
    0x44005149907500103540d0380c00d940580c400c6216101c100070018000c0301441100c8021281c52180d8920f0b08140c0110b4581c000c43d03205001c9070500000c076046042c1485840342c2003030550024005035003452001910381c46c2d4184c0365410482e04000d0740d20700c44d10300c018850080788a804280c0660109241c800e42c0c46800030306030000c201c411034940410b507503000410411540e055400041500d008010116058030000f207205241c8146404030b5251544609424030990455035661134503803082c20103d031124003c480366000002140078800152919803030390300c19500201080e1003240f070155620405a0070030b41c010f40d0101d0b0383e6504001541003030301020780c0c400750480303e9803041e090760205441050017034040a03018054090a04d41850b0a03641125415448001120340080c3c1560107640a00400d0189448904008071103000741d07030020960341d0042c0e078010012121940c2481500009024405050380d0411410004101141c5020015030142ca20766001e0301c894500011008407140440e80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314750701 1250 314749451 314749493
    0x2a0810210302150408030c16120f030b01020703020102030415021f05061008010815060102010222140d08030121060207050102120105031605150c011b020f060c03010501050d1e0207 79
    0x410000043d0f18041104c0c2d0020204400589034a004656011085004203000f80041004000790192680101f41c400c80ac01d02c949d001d02114034074000481c3c85071fa0390f00c0002c0c05a03200b40014081c8205182440141c20703801d00c100e076440d580407015a80c044042060350300c00c01e903880c0144075450805105403a15141030b42420616540b4010443d80c0da03600b90000c0310300400703100d404981076a01c02e4040750241000741801454500400301c0095070280e46204100162105141c2101c0341d0401c403691035009600108414210b81c60705039842c0c910316a24220a07402c440d801e60310703400584036201400445000300001600c819001c480d0781203242040c0c000511070360101d40d0917002e00e41d176004a40305540083d110200315800d0700f0100c4106000d9642d16030710b55400c0940501c541201401c4030184040c841c0c1c2120300c0d2001000007103844601c20345903040025001c10043c859540a00010b1401e80b881000c00610b030710391411500311403c0610600d0b04941d40000301d1900380b11a01c0c0e030800307480122071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314751951 1250 314750701 314750743
    0x120803040f0c170d140a030203040606090608100e0a080702010f050d14010e0901061802090105090a060225061b031101151a03060607030e031903020c01032a0810210302 74
    0x400d12001c06d01469409000301600040000d04016103500401c0040241203c1484410303101e0f21019142c11a44102001c5207181c1308546948610010f100ca80490300140180e01e49060f5400440b2030841034102041070040402c007601c00b101c41481281c1008505a404500650409040f48502d09000d411350030030780e0414000748841c04041011009608030000016a81e9002c03000589031ba02035401500e074041d0100100058064002c5800751860b15043c3e1032445040c00003d03048000034181c01f42e40300280f03101102507a0030002ea550782040900030704005c007210344004c481d031b82584c1030030341120305a4200e40820480205948005804503003005001415813505102040c40c0c2d01480c40e02404204031711140000c0342d202401b0741c54030b03d04004a1494064094140a503980c425256000c0c0083e142c145624004412060030390103460045407104045480b10f242280d80d880068484081404402c00000d03500309101600e0400c2c40740900301c50021400c605012303042298912020900301500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314753201 1250 314751951 314751977
    0xf0605070e0607020a091a04090605060f0a030f03050d110c0a0b07020a2004110d06180603030c020409110414010e0a020408030403120915170105030106120803040f0c170d 75
    0x80c10010058034880000003501c7c2980031081e5020f0703403040d2411a00180703031103042c5041c0056500850300c01d440607180c0400c41000942409601106480050200b801c0000c044002a1150b4020f01d02d2092a000220b00f8049960101b15158010900003450307621082d130074030410011440f121350144043c0003504c40c52401c1d450310002c0526076103025810700070700301004082d95a5644403596181d400850301f0384079080c82c100c0fa4005c0190303000d181000e400340d441500096800303004a1055a506603140010000e095080c08042c0c00c1d00401210300006110b10403010391203070301c11100d0b508118200b0000b103502d400300002e91080040c0c03010020900401060140c80400021a000c403984025900c4001d4904072048400c540141c0100200c0544c002040a02d0365100401070804030030541000e006980c1c0d03100b054200c81c600d20603003600900d8200ca01c00841c052202843d03020b4060421100401c0c559985e85100710000c0e04495540c0c80d004803011901c00c01003040b034081454505001240e0840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314754451 1250 314753201 314753209
    0x30a030e12071b03050a260703090902031008010f06170604020a060f050f1204111002060612030f0c03070309080d0c08031504060b1c0510120201020a0f0605070e060702 74
    0x2030798601400b4815440700b18403030f00c402c100b4540c004640100580d182e40030103261103241800544c40102402604855035084d0040d140e0031035603050383c192a01c107402843d218112000e50802008400700203061040007414040c00e000308041000f00c0751000030f9070341c1445c00e816024450f010035115a503101100b004010b031511010001500c040342001c01d4040c07070030903080b00d182c450310f20005002c203c0400c507406441d000002d4140500c3c8a2946002a908041c0600516644480d440d0005a10000c041030050409820b404170307141030b24003940d00e450941903810f0942e41c052120071360789900000c2c80300c05269100034140090f00899020309200a41180f005080103490100905502400004a00413111540000c0014000504140034a035a204000d00450b08881c9034801c9042d45582c07408070707003051480b55512447e2492181051541001c1120401c07040550b012415849031b00082d0000c10440011141624429140800c403460032040040c815158103030900d004d02020701c13442c00180c1d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314755701 1250 314754451 314754457
    0x6030d0f200f12250f1e15200307020102070206040f0e0924070c0209100603060803041a0a02010608100501030501110a0e0f0a0b0a020105161b0b060a0f08030a030e12 73
    0x400421040041d13002e08196810482d00d080060100408020740701c681106003042c2040d280c0074142000007002d1048101d0251208281120000c0c41d00c03190703007100700b100d140240d84c0000c0d880c800141000c200f980410895400f9400c03402a00307040b030a04004041c80d05551701d070702c0311074180544000c806074440f400406101c15200c07240d03903084200082c0a60300c2003039a601c05540040900800c2e0905042c8481c2d5144140550341c00a4101a008107442000200300d0301100c0701d103444040414041c201c0c03419203811180c03000381195219403000030402401c02120a8501d654074000405500d145003a0f42151240043c0440641080c07040442041d000108920707014030039550002d5403030320b01c40000c40e00d10481d04110504036000c02c0c010b41450341580700e18441c2c0c0c0340c01c12501500c1136615040e60b60701c0139040d01c0c45003401000049000140c102c200190409009400c65410688464640d419040c9541050604d036001107010a034456240c01707200c0c0314042c00740141a103034150303140e108610301c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314756951 1250 314755701 314755747
    0x1305030312070813020d0b06120c0d080f0403231603080306011110111b0c0306011701020c03030a090501141b0c123006030d0f200f12 59
    0x850f04000113540d60800b021030480b6598010318128580e0f1091802c141c440c0005c0c0e174071138026000311071000700d11076000848070b4540100408020035950695035052280c1d00100491014200501001000616800412a01c02801a03c81401080114620f0b1401c884110944c9014107001e030b0030008120f00130202c0390021006e01c0d103143c0448964059034949824102850085480c1004028507004140b0181111080704902d403003d0340e41d5100300c141c2d0781d803030b412940f070741138200500401a8500701074108404a030070900141c1014200d040c00c0303045810483e1000040741e00c501907002000403c1c4982c84a8203824000380765030b42070501c0c0c4101003200b01e000d040101040060110002d04080143c15104982901195515500c12f0b44003030710600071520306503001000c251400e00182d05203146038414440030b0001d01401c541c030101124901400303040d1005000301c0244452105902004c402c0203555510b0040c598460f10300c2d400c502c1c00640c194040300114062061000000c0350075607100e811 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314758201 1250 314756951 314756957
    0xc0c0504020708072406090203060a0e040f0c0e0f010b0a1215050a1410020a030509040504060b1c12020f0a0b0702120c150a020a121d0d0302130503031207 68
    0x129030910700009184900745018050345c072011088500720509404500546411840030320100c4c0c2d13503014032000d9000685226500c49c60001c0c0070f00c40900340d202c0c0c1580c0640070301c4036001e140c80f00e0b8403035000e108004e0f00303d9520b07141d2030810017402614440140b4010315800c54400c1c0f1f480c44051008140d9064140d2801d011a1582c1480580ea40c4860541d0f01070302d03004000845065490403d41c14501c49021240d0191282c2101c00f9a901e0001c0f80016496030076403601d0b8505410002088018440100f08945a0360784d118008490f8603182042c0c18102d0450702a00c03154031640c101312000102e0b00b031f0450f0441d4000e1044108214021560b0603c060340140c100006440d841c005904024403a028115070b0b4001090135680143c00281104040000c40ea00c04169110b4190740380c1030f4800d0f100c2c808041405141041d00d0100c05500c603510000045c02c1b0b461007003503104005414821003000c01300009070007150030b0501d5602c10740000c2c02000200c000754549280081c101c604044010b10303042c28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314759451 1250 314758201 314758207
    0xf01140105030d200f010f1104030201050708030a020d020a050304050705151c022511010e0f10090b030a0c083402010f021b10050420010203160605090d0c0c050402 72
    0x40102401c8240b130369508070010b0707402d29000441c81d28001c15070542c0701c14000703091050b1320812250710821a0103603501070755001d150900c0c51f1189040c81d80702400c03c541c401d0f4200800c0c04c40a1a510207401d8143e03c80d41c0302c1d652400d0034100b4500c0c1880940101e8030030484451030325a00c0200d441100d0b80705259011005003c40080c003414001e002c0e501c044240c0c040030104da403003080b1480c041800c4140c40740c01c4c079040502d00c2070011641c085584d003a942d0401011500e0154520f0320181d14007008005103081424180c441d074007200070350400d039404d1564a495100c5820102e8000c2ca25030350201c01080074800200c0000d245458008403c0d00f004080810b2105001a0701d100b03400000d075820410000f59950364106600c98083c0440100170380c040e000d6805902c00c0e1203814081d0a0040c2d8010b07600c201c01d07504103910103200b00c2001e918241584000c00112074441041e500100c8443c4c002e440008607454110030182c10003004070004800c0003817154541000500b8400e940c000d4507015100107031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314760701 1250 314759451 314759477
    0x1050a1205070807060c02010801081b012007060806041107020d032a030503010306050a0b0f01030c0504090f140f16030902273309060a0f03050f01140105030d 70
    0x800c144081d0480b0f2424002da00c40403c003650440303c0d00b25924400e070303295012a0398500780b19480300c2500e0840704640d0541e43d01d00c04150312034503040442000401c44126010704924540d0b142024980c810008901c010b01082200e1400d4400c840d618a41901c0340f070318040713040d4009044081c0d40d590050500c2001418002410780034249850072500c1e4980c407081c031039031608020b03105030400d200440e040c50030240040c4e5800c007640181156540043c08042c0c3e041849001500a000202d151100704202488000745880030350140044128010b240041c501072103854200003031b00000c1009444802413407d11645e50200e0342100c4181c2c03005d02c1c0000c1c52101c2da00c0040d00c0e9201b4915060000403548a000e20a07000c0240407030301405c0c0000000000440814900c4840071841c02c10000001e807101d5610400d06007040c1150b84407800a004c148030b00c0c1c6611704902000a5908192000d80c024081c080007082e09100340e001050560540e118a0b48c90000041c2c0d403140028250400c101003c0c954035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314761951 1250 314760701 314760703
    0x18100b030304290c03220311130b04091505011a0f0306010504030b04030e030105090c2d0a0e04060506041512150501080c1539030703091d01050a1205 66
    0x14280c3c2640070f04140d0340b0000540d00c4c559079001451020b0040301050398145654208036a40e00841ea4070a41c01e604401000d01088000422000e030343c11602d032510f00c241360f256160b114075980c0034450780301002d0304c411081c0e00e04111201600181c0c0e00814543d9103d0511083c0825103144e088141d4400d581c95642e00700488a5010f560300c02000035a012060100b01074100621850700c4000350000c0100340c0d1008031540e41c620410003004d402010681e1031802100390800b01c014107445218424000712045008144220f003590700031031206030301c0c03404c0c07104002c010f00466421190480d001d10000301d0000c026400c0b030071140b241a9851038003450500170040b80b411420412030110400300070540c1c3d2192280d880329180d51425100e4089c1c3c2900c242d249580e5401d030b0380c1da111a144c0904c08861040000c107100303000b0b03121102d148010001001ca4850b010002091254070076550340060303910340360390000c5c14050020803050400d510801401140c0f1aa41d03a182120516418801c468425042507 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314763201 1250 314761951 314762009
    0x16030204050d0b0121080306010513080d08070207080106360f0515040e15090307050303090d090b0a020a02060a05070503040f0509070906020c06091818100b030304 72
    0xc01e030080c0104502d030082c01580072210b4100c1d0705652400808a00c4011030700020204075900821525042c03020410700d5105030003605402040d061072032000303070b1201c4c1c0760b5182019a1034035400240c5080708000f0201d606103c00c2c001000004000e01c0b555081c210180350f031018001d681120040000c030403ca0030401c824181c0c0e510606032200300101130908000304043c0000b103a40f00c2c8003900f500001c4e03010781091320483c0d046c1450603000c1e080c08801c01c4002071204c100075084044603c0140200d001080091004600031a0104000c0001c00b03034021000e80080d81c0c0380c0c401c122280c02400300414554000c40e0b2088131940c1110055640c4680c88010ba5040c00303003110140c020b210100300030075108203a01c1000306541c0110740c0115550340c2c4100032500103003240034030001038100d05203494a41c144007029060891005104203c894105442d944084c4001c4a442e08078003850603009104500903c0900d448484041d41407215400440204e0303507030710851060030050b00908110b07c5247c01e01c078a007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314764451 1250 314763201 314763209
    0x50406141005040e030412020d08041a0307022b080702100606030509150613020306040f050702160602030a050414040e010c020a0c0503070609050108090c040608071d010e16030204 79
    0xea40014100204a256400014011140524035003c0109840180042960104c0c0e00307002203000d1051803682844610a01d4000480700038106201c0442c6020b200d8542d00f1184446d00785042c1c4074070300914020b1508500090f080300c3d04c40d03010080e0301002c406443d504210301003401c09501a07280e88078101d1030b20500c0a00c0700c3c030491810102250069168111074007401c07120b0304669889480e1040c0c0c6020750410303250f05074407002452264015070020f40107550311040040000408024050000341523070401c40c1e8448c0140c2040100b990040180b1a180d4060b100501c001c0d4101103010340e02030680c1c4110f0140781390540d800c8152207190f0303030340d0317003101c01c00e4007203107000f480700d42d103450b03030280d50380141d0314088440304107140c008901c50900180c3c10b4100c0b03080360340c0c00d02410700d00030055817585009000c140381e9008540d540c648a807100d014200082c01c055009281c803d00c2d2107103245c0301803184200204024060301c0108440000d03c414a0342002181e05000e03911025440f05500a1066502c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314765701 1250 314764451 314764481
    0x304110d0516080d170c04031704050904240905210c030403061e020f1213020a080c01030c0305100e07050c010c090f0e04020a26030c01021306090315050406 69
    0x30041218200802d000c12941d016031035048410701c40c503141e070303072601c5c001c81e09003203020410702040010a0222581001e04600c0c642c01518050f03c0320302007584420210707401c0da0b9540041003100643c5011015070b90101000c01030800c01f003c1641d4850307850b406080701280804000e131042882d00001c91084a005a5511080300e950750b90f00c0ca0072101074030309a10214000c0701c00401c10035500d800ca0085960200c8041491032800070076103031243c03000310060068050841c00c102503900580302d0000003809041140700400d40e1a8108000505944418800c2800c160070501030041418a140c40341c01510410a20f0704070719640c0303140446240c0038155050000398205161910803a4010720f000d405c3c1e82410404213011a01c51560945250054400a4214103031640400040441034281d4401480b1a41008012000000c1082c555004506140c085960004a000351164800301000090100d418041c01043c619120042c000c1d442d208000c0c0103e441c2d10001d070401120b58000704070400045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314766951 1250 314765701 314765743
    0x2010b0301050a0e010c3b03010911032109060a03151203080117030904050a0f021210080f1e0c0d0f02100302030603031b0f060f1005060304110d05 65
    0x83da00d2406400040342e65940395107170181a40300f580c0301e0150701d04d80b80c0d030001c0ea43c01c10000d0348612025540c490804c5071700060380f210f500c05ca81e54080c007a81c1d03105c0d8001e418030150100c07410701305810f10040e601445050482d403500500c04000c0301302590450b0030212103c2d034644140300c1c0164042d280f0580c1c503503606140035202048100300c1950b141c160902907605c0302103c0e038941c2803d0502c81d00881e00d0340c52691041c4203486e00e515058001e1640b001c014900071803449a01c0021000b0780e005806103010204d00182041424840b99080000801c426030081c203074090802011a200d0388892803140ca01031611800700d0301a1401c105260070044050140c0f0318111150900e00500c055149040744500d12a0309441c241d43e100e4000e4a0042000401452911013a40800304030140c8500082d0803602425040414600050000c2403050000401d401e020b4606040015040350168000500c00c240500500020030607408007045081000c0c3c60b445d0721690907050840c03030118140500307040c94a040e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314768201 1250 314766951 314766961
    0x5060f07060506030a0b041415091e0a120503040609020a0902071103011a0120060f01030516030f062414010216030b0c0a090e01030303090c0608070804060c02010b030105 75
    0x50010420903029007801c0006803038550401d5140d4a400c0c0e800f03030040428001160104407102c094451541d1a0310032034569065444010042d0581210858101d40010044031403484500c806180018808000740a03d8030060780c402c03040c2c01450b840c07081003060110008081088550100c0904ca400034804003055545055a90103940009012920320800c00c0ea00c0e0300c182014001c07401c0881c03102d1300c0030b51090710600c0119101a144007950190200c120030000000340305000c02c40c0075110f8000010f070301e5070450516070300c0d003440b104010740c0c1c01d19540c0e002c0020540f5001040d40c029844400410517a02489084040055544076800c800c650f0002c000741d012014a081310031080f003a02600c11103216426018600c5d8028070002e4500101d80c8000382c00201414020601d4981034108a003040e91038003185031040c00260803c8010950302c0100b942406990807000000703000300e1070242c07858a0480e0b00100b81e100003900041903107403507566a5014500070b4201c041700c150081c000b08564502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314769451 1250 314768201 314768227
    0x7050f07061b031a22060906080706021513030c0b0702060601110106030209130201050c0607020312010f08190203030405061c0b0103090203030a2307030305100f1d040501060506 78
    0x80403107100c0e00301d8030001041c00c00c2d40a4003071641602c4080320b00f1000581802e081c48000100e616102000207640341e10705224010314032446000e800c40110000e8140d0514010364540406030300003a040d0340c4003204101e200005480810350085041500d038809680e24030b0241c4041032200030042051980804101010380e000035441d101c1e5800740d0743da1002c00220000c00d0308aa926010207500b2103070344000120003021008080580501c18988549000c400001e030b6800d00000380c0e0404010303080001d641310501c000780358070b6001d0a02d08040501492416020300d95034494950b8002e13403103801c3d440520543d58140b0980f130007400c0107000340b55101c80c1558051501e03030400828209182c600744884925500c644036100406601400030f40c60070388084425030b841010f0841441c03080b030002603034007044000700c4045c1c1000c40c03180d10041040d04061070f85c41e444607420307008500c004502c0b600400c0042c103020204807441c0b00715200611103455a003441405021aa0001500007100140340300b20485 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314770701 1250 314769451 314769461
    0x11e0c02071206020310140102030a0305041401020307080442060906082503020f060d0b040606120c0c0332030106020717030304112e02032a1507050f0706 68
    0x10940300400c074807a21f8000b0020700d05442c000c0140180e01c14070440d40514001da00c11a00640122004240c064004441038203a0340300700c41d9100011104024801045100c0d03c44092202845984540c402d014545401c103400031041d885440100c00f6150024944541e8403200160108003024008a81c80b20005660380903d0501c01a107582c0303491280180806d042c25000c1503d03401400c9105080c020b40801c6400d4001c000700140c210ba5030380c0f01d2420707a5140c1c803030703800100215201c100098403004071400454128801010902078860508400280d20610008941d03410314403240340b180c182c11904900020011416140503000000403402c10340025200040300e44079403012111a0422941a44034002a40c0c0104003884a080c04006c92805016490589540c1d00300b515030f00b1517240000102a40701d48510025820004080c8140c0d04203085904606880e00042c038415502c0325484e6580310909401d1600c03e000880c0810000d0f84100121580d882c5400704003502d42110b070410b400201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314771951 1250 314770701 314770711
    0x1b100507020d2d02070e0106090501031103160f0201090204050117010501081606050a030902040c0309110a03081209150a0e1606020a02040b0406050406120212011e0c020712060203 79
    0x881009000c500b601d01c00c0c400648440018100640c9034203ca10b0203000806501c2030708010750040c40400708502004040d900d00034690703552885038107440c1500260495011000c042012403042040158004185085501112940c540340c20800300b0400102c0c01000c4600c0c0096116003050000a1003041c0e4900d6136883c0480d11000300402e1745d0742c6807001d6862490754460a5490141c1e42c3c100f1031140500081c124203038043c280401c280789142c0c0041c040300c10340c05c0f0702000320703130342d41d140c00203000c1c40310310412503500281c581c1046213066031140d8105008d0400440001804130b400039810140501602c400258601600000740c1032052495001d00844450380d0b103184105c81c0845d0300ca40043c1200380c02c90703480741c0142c00c03100410740030300000e0849400a1030f005074880c20005000d481d6031003050000c02c088185c3c80c290306080c2c410400303400f1110401d40c0d116030400e00c40c00ea074403818034220aa108080a40001c2c0744000310704c183c0c00c141d00c50340000410a0098460b2081c46a80e80040d841030b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314773201 1250 314771951 314771953
    0x20c011503060b0609090705091311031504020315060904061706220213090507050306090a060b030a0c120f0f03030b01080916090e07050d0f0507061d061b10050702 72
    0x83c121103000e000e07050040c6204942c0c4540c1d000003041516009500038070a103a00500780c0d0040e07900d4039006105070788040095180d100030000400c030502901229215400808407020361441c200038a015aa00c5410343e0310702d11a50000841301c00669032548500b00402d86c41c000725462070351284c00e0540741c02c0c00700c502540304c0c940e40400b16820a0b031034040d60401e071350050031191807110b9500100000d10a800d0300b11501d02c00c2c014041003d940401c0001d1081410500500326040145000c800351144e41020500a03030285090b0800926600120300a0346c03081c414007002c04c0024100b0f800f503540800d501030140b9800100603018558580c1001900c203800780c86401c0d45d9200c0c03014181c0d454540070000c02400c0303050a4240701d0710035640c001c11090106d000460f602d258540001a440680248048440034800e5641d0000c026091041c1001440350341070101503002c03a20003000c804c3c05400da9041c81044009105000c1c000b42400e0190b40c01c0c44001140c00c2c8900805d580d400915042e1140005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314774451 1250 314773201 314773211
    0x6090615080c070302031905131e14030604030c050a06050a060e0c07030f03021b03030f091207110d032006070801050d0c150e060d0c0f090b03060d06020c01150306 72
    0x1440340200407500310710340c168000d5143c2520304001e0041c1307c411040400410000300708801c0340d6020070070903201401e00d041c4400400c1320018a102c0710550181d12402141c810401c051a80b60b60110700c01e0f034000d4040c1490058804107251040c2405420b1100030242d51402e01801220b1415601c62401e503202c6555640702500d40414007559800b5907600240003e40c0301e0302c20a000d5219401a01079502501222000d60411400c03090858200312481051040d940080001030783c02041850480d002c81081240303403820903103912104810031907032180118080030205040500ca80703107450118052040740b2002e160050601510341758140c07011f17000074011070000b080600d05081146182c50740300c041c42014030301e04901484204d0000ca1890140950115105101d880700001000c2c141d50580b80003400b00200c0e00d000d40004d43e0941540300f0444000024418100c0103011a904080100d68281c800324017494110082d20600c104000c0c0c550801174188000c00380c402403801641e01ca6103003441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314775701 1250 314774451 314774461
    0x6041106070506040f021c03050d0506090118111903140924061507030908011a01120515041518140106110f06040f120906020607050d0609061508 64
    0x14050090740c0e07000c0c0058202c640810005040c6090600c80148040c214013500101544000702c80d1500140a40215a00007100f2900018620451b80d00180845100d000c6504145c1d8141c0100200c1082400040d602c0c0e070890390701e039602010399020002140d1850645c40c2c0240c0c004000c0c0a0203280d40148002c10404070310700c564046421620400c103500c5542e00f0101d07a030301e1a2400e0001500c801c2d0404418202807011040071390040c08458002d0700d03540b10ba140780560840c00c544110400da80300502c8004154902d80e03004039034841100280f100810143c4524002c00039249042c2c2c81203500a00d44945c00d095603002c0001d80040724070131440e1165407414144040f041c2e0300610b020310310f50340d480c0340180807445c01086003040300039804040314035040031200030302c7c034013002030310165407082005410008100e417031300d42c00d00d11403140c2c504400d0561a1101c0650782c1c00001e00490140b08010030031040d503a0b1250310940082000b031000703116240d07071007507040c42c00510002c50070005205440011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314776951 1250 314775701 314775709
    0x6060c02012309101403010e0906010605210414060405010618090809100c1509060c0507030c121b0809030607020a0803010513060512012a0212030a020f0c060411 71
    0x1402100100a0740b41a409a0402c1040c8040340384001c203122004171341c100c0c8140b551014502070107064142080c1c60512496062600b04142d05ca042048810040c0004280702d8103040704040c201c200300c1da1042d80300c5203080388640f030180388085035a01c100e408120070310405410500440d07106030165410020f05982d802c0c1503900c540c40150030048104000032050411001c15440b0055074941130380d4040c000d0340c80c007003046070381d10b1200f68881d00c5620b00c41c00c0c8007140c400d05c4912155800c01510b0a202e540d00a0407025001801602c4214000c0300b0080103801150700c1c422201c3c8030f00420701c00d012140740036050745d04030f190801e0080c0720758400650b48a000294106100390840411800c50703181200708004043c100d040308002640390340c0006019142c4403000341c1c20301102c130000700d2940340b9038030044550449421341c4900a174019590024180e00801c00780101c2c80c41e0092075540b45da908100402912440d01711884440c0c000410001030440410130314011407084da0301d07c5100c1c40c2c0c44100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314778201 1250 314776951 314776997
    0xc010806040b09010519050607110102010b0609011d060c0d0203042402030f0c070b0403082106060904110c0312010f0f0608070f0c0204020f1b12040510030e0106060c0201 75
    0x15504032481c41c0045c46149007a416142031141d418403806010754640d00400d1094205120031204207001c07042c0d08120b51f8083c080c0c080c0007c01581c4c407034245540b003070009020b6514400c01d5586034080d401750561545031078040b0b5032810402411262417514040c0000d40e41d80c81841180c030341a001041c1da40c0512440ca40c4010154126401507040219000108032181c1c002c99020180d0310401c0703000540b00d00842c001c1c000840c05102c1d15500c1c1d0022a85407c0020150220260000414010480c2d1a5104002d9840b403100a40300020b444882c2290b2100384d20030030190b040c2c18480400c014a01075002000a81a1280e800c03181c03400740e0f61111000c4a914250080c040840c00d035100050321248500b4802c42c0e540103620b0200c4450030f030f9401160480c2d10030f04200490039800940300f020308406006005000000700e0082240c50f031710341249a12401940900e9116a07000741c800381c20a84030307400035544c44240000030000741b65110b00140403c465644203c0c0840d03810003c1072200c40006001d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314779451 1250 314778201 314778221
    0x3060606031b131d160201150603020c0709020f040611060907060f050904110306031e0c0f1f020309090609040b0601050d022a070519050f0a0302030f0c01080604 71
    0x1080e2075141802903104850f008042008246800721000103a80d0881c40c04c0c08000001050f802070140c1003050500340b008181e81605425a81407481810707001140c10303800743c11602d0a240040c1c5a403000c2d41054108045a4481d07043d250003c2100700704000050300034821205903840e412401500e0751503c5c1c3c0c0b6104c046500c1c14050b0070003c4200600ca00400e1011101c1c1c074949000740c541100c00c00080c00322400045020000742000c02000b1007400c003000980309204140d0682048602255001c87d500d801400f0002d0103009070401e100301d56100d0b44a03804900d0030b1492174070718903e40190300a41c3ca820094500d4442c011038404581603041015600b40a03d400020b59246c1ea1303540c01c010344965003c481d0300480c0d103500300100321100d00034540c01184c5001c9c042030400244041d00480e403034050144c101c07501c81c2c00d865010401038881e04105c0030882d1003d40c0c140401c480010000b03070b421400ba07030019400d0f0003022000c0640723010100d41507204640980b50102c0e15110001840200e0f2002f01c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314780701 1250 314779451 314779471
    0x60403050711060c1b01112e1d1c050306100305040305090307090b09010e010b03071409120a060e0708030a110a0611070605010608100308070302070b0a0507020306060603 75
    0x10860001c20307001d4440303100d201805088245442051541a441c10003900480b1149204a01d0a0005c969100601d441540c0101c070043c0321103901d4031809410246808030b4400d6140400c10140240d00181d0442c0c08000340c0d5005800c0210102440e05443d0707122004540c45641440f41003940c4507009030256030045138013602020b40d00120610035001001d0103002a81880418000c1e84460354082040501404100740046881980c00c1c05008a030176060304000030b110600c80050000c4074051003944d60046452a10029881103851400854030613080c0e070b00e4000e029400100092840003450400c2c041c071400c000c006146580c0440c584413642401040e0050300304000e9511510721840003402500c2d000010b442001c1c0321a5112421144078003d00454000042010b2003481042d120b5203004115508010007603240a80310b0036806101e5000040c8a14400316003041454420051400600403901e40396540d1201c40b40701070403540010408070302c2449900001005810148162405550164 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314781951 1250 314780701 314780707
    0x3060f0902031f0b0c0609011a0d17030403050909160503070509010504080a03081806130206031e010b0c01111e071a010b030f0106020a0b01062109200306040305 71
    0x429500c082d510260212040150200c1d44848406440b4800001410300c004501e0b503910200d0403050900704001c040700f405900d424a041404ca1500214021840c41162a10f0078940c0310318020503228448803d00000a40100420040640210003008031510403206c5003c0c07a55000f124100102c1200100c000081e810300225803894080c2003d0030203200141406401d04da220041c0e00c0c40c100ca40001a400141c05d030041c00300684000b6003610709403030010041e00381da1812424080ca07011040307500900400000001a020120350b040441d401c104401001d1010350b500d01d0040714a410503207a110707055191445880b07400c4150400c480040c1e199115000242011002c0b1040e42c0c1c010400030782d44141c8005126076030340c040c04c0070380d400ba00464001c3c03074590410426050703103134005800074015580017503007182c0801c450035040b604403000c518140351001e240c4280520034061020710020043c0c1030030345810801ca0a2160b0501c12007044001546540c1074a0802d84d49200949015006c107002b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314783201 1250 314781951 314781959
    0x507020604030327060b03030405060f040e010608010e0c0307031d01050103140f0709090c150914090402010c170d0e030306091e0a2f030a0b030303070e0f0a030503040f03050c0103060f 81
    0x617001b1185400c2c005080c0e82c2030170f6540b4007084d8164486004d4800f180c1d4001424004a40e003019160302600310f030b180411a0f58108143c2031502d4401601007034402c01c01100003113086110742c10044c0301c6805da02ca4039401420882e06140a02000c0c041201c403510343c1d201c00341a00400080600c0350400140041c8190303071a24a40d01c0c01003481d14401d0307482302100803020a8501d085c01500044c0c01c0203545000002d85401900c000c1102030000ba14030454401c814070000d030380d100d2a403640098000d00e005000035820107891300688604101c10580c00e003403940c0b8141e10400400039601c240019285075409654030400b900c040d2405007036514004489a01180c3c5002440d4030128030a00e2a00c40c591701200c0c0c41d08855101c004031494011880000800c000c180c0c24540140c0c0483d032810790086041d030500c0c2c0320260070020f01e080d00034000c00c0c10301e134410520f55454065500454009c2c0940350b44079182c110151004400340001da650f4855150140782d2540300b84035a03000c441c03040c0801c210032818 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314784451 1250 314783201 314783213
    0x40c242c09150904050618010209010e060a110601060201060317071a0c0c1e0c0108011818141c0903080f1b010e0f011401050d0615090507020604030327 67
    0x18140c44801d004156480d0401c1c3ca40000d09400790340290300078145481c01180c500340d85149903d80303030700d83d0b401800716040e16600009052420001241d00c1368a07842d000d8411109000c0c0c0001101c2d8070b105107000018a103030198401802c2e01c0c06a60580d40c04100300f070680c41c051080b01c4004180785e60803182e42019520700a00640c20050b10385410740b400c0702d558649403a05410500000310014010000c1000a00801042280050a00b010582c540c0b402601c2c1094170106613404c90840e8a03400c40c10010711410f81c0d002949940031140f1882c281401c840240d4920381425010440c05181e101508420f02400c103080440b6070111140c5d1030040e0703030100640c2c0d907004018101040214a69901d40070303002801146d8540003008005c06107105850f80c40c50030340305400102c0c4014200500140000c2d00e0f500030340c80c40c8580154000c42c0b1200d240c1c4489070401060b0b40030f4840345140000344484140c1c04036805006502960302400841101c0303645e07e0042980c1607030501c070041c450f1011000520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314785701 1250 314784451 314784469
    0xe040213050f03120a0917010e0c06130305060405010606180f0306150e1602063d08060403050c0d090501170601030b031603150204031a040c242c 64
    0x11020f0182c1c1e281d100100c0d0242965084008101c000c6010510301f8449103100c1c034200c0e0724421001c002400107100000d5605e48801844a100e40030b000000740000510070030b03028040c011940101212040e14060074010300030b2145000b1600000ca00307400070240c01035000780841c01d80d1f00b502c264072200d038616900c130001806040020f500c0e1098010000800307a0310b40c40d000e03209801da80c11219008280400090501078010034001110384078522481400300690611100030503c3e0040c4e0003402d0340d501d04540c480400b03620154051041c841080f0030907074808090480d100c048412140d90219400003510401d000e4000c090000d85500d6100b00d150349229170464000c0018100000e8401c1e0f800d0100341000902c0c13010500d0b0100d0401c0c20020032143c98041801c4100c41d443c11400c0c941160344050802d043c4080c042e021191030f0002c1030511802c0301c0060000c10f4200254800d0b0b032000720041d520341d801441e0180c0030400d80084082401841040c0da004800680b514140107000601040320b002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314786951 1250 314785701 314785729
    0x6171c0c0606050d03020f0c0303210402030a0b10140a1518032001020c04091707030302040b0d1b0e011b0501020c0102030a05091606090303110c04090605070e04021305 74
    0x60b03254030000800703888400c010075606001c0e6000d04002009130117014039256000c086d4601990040080d8000910f5405501007483c0c161022469503172514000030749802d4410034060204202e140c10b10000c0441c09142c01c046600c41700070843e08054840402c20b07104e0561266100c2c1c01301030581013040b140f080301d10703501a02e200c0c0600704010f920f94031f52460b403203c48031004c0000e400400c10740c20b65603010440d00022000071182401b441209643d00c041d1001c61005c500810711010404004050003074040d240a40389450640303448500514094001e0491801c11801580c0d850f11440d0400b4442d580d0103405031010b031517040100308152007456403118a1340d402ea6a55500b804042c55140c03007070000b940200780780d0001203490f00f84121001c1c2810381c0c0c4035042c02c50f045814010405c6507085614401201c0e0141004100701e01020790780c41c01c295040b001140c1c0285083c03264030411a0b2a44410300445036561480f42c000d054170180030403031240700d03800300390341982d05010409031601540d603000075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314788201 1250 314786951 314786963
    0xc03040302150a231b030711150403030c030509060c090105160609050106060c030806130612050f06100303120f060302060d1e0c0f030e070b0a0306171c0c 68
    0x120111568000802c00b0b4904151198845920301010f04402068218095240b410301c2105d0030020700b4800000c8028a50503071402c80840010003d6004500c00b100031988101a501180080340031402900003c85040300400e01d080c0c43c03004d8052003032241610641101d07000380126140c0090500d065005010151b0400800704026007007c21401c042021b580c1c440c41001c96407881910b020b600303440e902c0d0005000c01096104140129078881c5030650005800d450100c2c40961003402c030009003030b141e0040c007a400c1c00b45446000308040002c041095620140954055450380a500f580e60b0310070b803002400080400fa0b90700da80d40c2c4143d104080050080d2000140203503260302240054101162a040c843d40d0b4050703403611a440c01002e194181d030317980c60810003103019200203080e003c0803051728401c142d41c0b80416004514200104e8015001540086489001141e00203001c1e00c80d60140780b0514034a250012400000000d075001c1c2d0f440c41115511461a1080044032140d01c0d83d5000d40e15 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314789451 1250 314788201 314788213
    0x80712021902060402120d050a1101022104020906100906050309031204080a02060c0a0c080d0f050a0e070803161401200901081003120c02010e0306070804021011060c03040302 77
    0x124501141c03034211626000c1d0090202c1d0716090040150841080c0d031025043c1d084641d60405542e03000c821140071103403e0401c0c10fa613084011406009003e103043c441340c0e0304103424040c074941550040080c03069200f1540e0607526920348042c00310801c181c0c0e008002288064006101f814020f2020b56880b140320303c00ca07030038544e98414008003d801514155619800090b18903481365041c4141a8001e8401ea0403518040c2c2c02a0000c0108403c40ca025003c5400415248d20004258001960f0b04110709003d10007424040f43c0300c0c00901c0b804082d503040c1c4c072a40c68001480c2e14044180c4850700d4003d0b500102021094079001007200e00d0303100869081d541d80044600051450381d8106448800007080ca40b102c00a1002600130301e8040c0c903025140550440801c0004c00b50304032104030303842914001110b07801c5840181c507128010203480360700d03018007010042c5107030380010102d1103903001715501103e00f80b0000c070584400d111101c081c20160003500000308010510b5000b903422a00c40c1c41103c1c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314790701 1250 314789451 314789467
    0x40f0f0c051306031401050d02040905060c031602060609040f0215040303051207231602090f06010e120d1b02060a0f02010f0b0307030219080f030d05150108071202 72
    0x11140d2586125011400210302c04901c0c0075140144006031406041c200b00f900b510b10b039045210101442141d110b415510840790864469400c07220040d40d01c1001c8881c00e09040c903951110f5007048802020500c071348250901070740c0c40011034034055800900a600c19844540350410608101201a600325000207010181ca0800400810040d4000c1d0b80d050345400c0c469a80e20407007840030f0015410404044009000f82d420b05585007040c5e0580542156202c00381d9166664581c14058069804440582004450f0a800d1a0b045c8501c80c240d0303070604415105010090441900c801115071503025000d650300c2c15004076100050480d44510b01030b0444c0040d070004100703902c001428000983c42001140509809000b0a80645125981403203000b090101180e5a18005e03c4007074030030009881c8c07150601e40000d807048050480c481c26101a008600d100c640d880e880905055a61841d100010b410f090b400038602c1c8020030141d6030002e01d034449074001ca482420110010041560810002c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314791951 1250 314790701 314790731
    0xa0e1b0f150403080d0b1e1e0619090b2212081206030a06050901020910090501052b0c0c031205040804050103020d0f02210f1605030a090f06020301090b03010e0606040f 74
    0x4047d150003071040c0c019900700105100c0d040702c8660f51a1200f250404180301c05507100c4041d40c001841c52191442c4040d21044101c03000c038038980c03200300d104900140320300e041141080c412400280d02081116502c0d0380c0d0314100446100da0001a0124500b0700442c0c1c40214031004103500b00b28010115401e4850320340f10441225000e03140001c2c241e600007406105410109211945941d039810014401ca2511001806c00d1144440301c50b040c15100d514a200305ca1421074142000340006000c000700c1500a0b00a00003840c5002c041d000300b05441003500c0d00000600520317200d543e20641d440e040ca0316140055002e0f4000e035800a10041d02c803001d1959890041c405070000350b0078007040411407514030300e11020000000d4a0f002501c18000100000c0808a6841031300b24251850900d41c0c81c0d44001e0184028002c49000074620202c2d04440000d00c99036030040c605889401c40100603d00c10350301054221803007900d9814880c0c0101c80029113504c1c00d80d201100e41450441d0125171500c40c0c05445c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314793201 1250 314791951 314791969
    0x40f06151d060a20161502070303080a09140d0c050712020d0803091e06011403061003140a060c020304050f1903030305130b010801020304120c0c0b030a0e1b0f150403080d0b 76
    0x802c00f5100108401c00c04000c46d500002c0c1c583c3d0031800070384089401e40d10b0003080d03100001e18207101d8030707110f0700500100050006815004402c0c42c003070b2404040194001004048045001d0314244210301c4045118980f00c01c9440503680d0060a10144144c0b55494075896000180f03103045500070b13030440c012880c0ca1f20090542e001d5210000c2c0c4240d41c14076282e0090081030042a90281d403100d401c10400c41c0200b03031020152604a03244404100801400c4c0c0e2411210801c0101076a0502e42d40c001c0c110740010103002924000c4480d01d00d8002060700384000022003034074414a2806040042010902a44c8a550801c045c800981d4040c103452301d89210b501c0c000c5c0e01002c402d80d0300204110501211810003403030714000707248c04c0658030710540f103c0a0a0030075005000001c0c40010120380358422550180760708483e11000c1d1070055580340c40096100303000035580c601490a0b00081203040c5001c41c411500c0001410085060500b9510760340c10903005840354140484c1d0f18024811166611070003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314794451 1250 314793201 314793223
    0x11060f0415090c060f020703150207050a1532040b0a0b03010c0806090f0c04150527030705041104090e0c191d0601080c09040f06151d060a20 62
    0x7040012454034200800c5d60401d44041021500080d9040c0000758005007148507100c4074090142c1c0350301c0d19003052810441100710081207949002001c04850103141c0108071002d4004000002e000b04010748030301c010681090403515001070b840003c0c0080c1502c00c040c1d4002469400001c1d09840c444082421242c207602400040380046081140c1c5180206170399a11440c4109101d00074240f056040e8540e01490140304d80ca807803608451603846226a00b1b0319580c0d0004280703001c8410840001043c031140c885c0300103000b0b010ba1000070545040034000d000c3c01c0440084010325041c904101000100342c1c8200d000c4040c01184070340ba0b40381c1d0303030040080200030107001c03404541c901c0c102003401d6080440d100c1c6c056640207041040320a030313002201503600c840c2103184103a4a020500000380180000756620703802c40e290420104a404045020340030040aa40310b02c42036103581284402c000c0000400254010010131549d1000f91041e210302e40c0b44911046000303003010150350721038180606468 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314795701 1250 314794451 314794463
    0x60a1413030b10030503070821181504020a17030c07081f090b01031203090507090507110304080601050f12070b0d0b01030b0307060809120c060603070611060f041509 73
    0x8001d00512120100050304149807400314143c2604c1c50340c41d5600c1c2e004c0c0110240c030503400030800400004a10400044507017240088500c2440d0400c3c95150f882100c40d0b541c1040c2c4070b0355014034800166103948601654000b0700d100005444c040013103004d000c0f62044000c142c0818409a00207140c1040103001030100e034005030228244c5501e0f90031300301e12004030280b040c03414659450085800c0e2125681543d030010100400c0e004054000d8018166020000301144034854000502010341d90110380249496034804041c0c00c54985802d64034015801500c4164001c40010065440c4c0110501d60f0404050714604000c2502080103060001550002c1e40c10003002a00502c080781c18858000b80501c2401c080100c42502c4022940c1c8180b50701075082400b02d035401203000c8450401070303040b01c400d41440c61a511010143c0090300c8a40c19100c0a000c1d100c0e4410120320301b802404603008004d00400200042e69403c00c2240c98010080d0013a22000300c280524101500c04e40115110507000329 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314796951 1250 314795701 314795737
    0xc0314061c02090c120c0427020c030703020a17211b04140108060411030601030b060d0603081b07121716080304031202040f050105070501060b04121202010c0806060a14 74
    0x45c190b80083d4030020440b4083c40020070090004030060480820307020f05514001980751082040c0340c0c0207200b244d1320600144004180401059070000c0c0d00d03080c2c64401c0480340d808810f4000062842e009511000300c0c03980c005804100c00d11b04003004164400300403400c1d50a080d81c024160240307580320303070021030b00c9030f01b0b44507000c40c1560001281500000d09850801c1600c0f006588011140405490300b0304140d101c842a8440350b80d407609440107804038080400000c1e83c0e80c0344c000c800368060f610701400401c0e8001044003400000c501c420849009103900d404020351543c9441c40c650001000d29828901440b508a59812052150342100c4c0b00361006903032402c181c2800b034a80e03a42c3c9c80c1c1d000041030040005115545030b089048040760804c0c02c246032124404d150080c050b255135000312100b481c0218001944402c0240011003480c0900d00681d04c10b851804100e007640c0148850001285a5801050290804100503d114200742c07401c4941c1d0300c2d4030300b41001d80707602585615a2840d058 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314798201 1250 314796951 314796967
    0xe03120405070f0e090d26060d170a03150602030304081605010501060306090509010902031f0204180902150c120904090b2e0515030403051c0f0c0314061c02090c 71
    0x8200c17008241c0f0300d1f82170407142c2c40890401d0804800c5010040074140e0a9100851026110a804187d203140e10501056a0b040c2c50242030400350440e904d0307440000c0c200200d03401481502d581040035507034942d01851445c0c3c0ca42e210383e022580b0101016004603208024100400d80c2071003441c1c0079040075a80031580b0351403c080501a13036000b500b8a61542d140c64186c0c0c005130360004903183c104171079581c03904203161403200b080006e020b1030f841104000d010005100141d81c0e5940084000c0d8400c482e00340c400560750040004500a6904070100c69100101c180d005607124000341214601c01080481c0141c40b540e580348415505440c209449000003034030003a030354a010704521141481c18031800c01e41e840e1000140e5590380308040320415400020214080c5481603084641408001810400316030110380c0d010000c00d03186224490041ca003c5424081c9442409243c40707040b051550188030b91a800b0070400c5030401c07261180400e0400c3c0700782b0001078440e84601407140c26401d0740b00d5125441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314799451 1250 314798201 314798203
    0xf060603020a05060913050601020109080d06060215070509010e04020405061204061109010206010e0705040e010e10170a14071220010c0213090f080f1803010e03120405070f0e09 78
    0x6580c000504c44e40c0240058145a00c404241e00a0001035240100f51030700d034100182c1c014101d440380074102050015490101d2034080d0006011100785500300c1d00801200440e100c05088140c6485001907010084504150f2245070007200c49800240300524282d540d10010780c540d0321040140207209543c5041005000480c03082030300791310810702260f1074080c3c0280000d46460f014007030788501c0c91000e1f01240d01c3c0780c41041628040c0c071a031050213420396110000300228400459141580180428000c03a4140143e03400e400324445101c020400e0340026030f07417000c1220882a0540c06845502d000007041054484400b408501070035501d02007070f98100d06800510384040255040c44810000d0100580320a03414001203401c9070030010310f422280ca0640e500e8151800050b01006012546603090304082e4000c18041139182156440192510181826904641e42c1002550014410612007a20002296510502c12400d41d0703d01c070f448020320800070656030000507110100d50100406c0400c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314800701 1250 314799451 314799469
    0x4180605060f3c031002031504050103031e2606010311042603071a1807090c12060e0c0a05190509010215012108120411030d140f0310030f06060302 65
    0x2c1aa60080c20403c601199a540c1d0118030418816030000009030740310304001c007180c003640008005200e0f650392420001d0100310359405203051000500400800e050043c02c11440b00680345071130304440f0a2208034448196401881141815141d41c404074084080d8401040604180100000d41c0060940c0c2540c5400f140c1404500c0c0c2da20400504007c500381154483c4c40000d415070989035540c0303101d0103120f00b00300400d4054591164441c04501c4050f41c0d0442208880280c0c0c0e0080380c1c00089072240c0030388005200c0c5374412000c01003c00d0703c80f01020010000001c140c00d04618044102d40e2600c1601a8000c02000003440450420f00075039041c81130103054501d20452803003d50500c100d144464032051208030781d04a80302c0c1e401d410008940c1c02e1381d10141d000d114950507840c050828401c504c06d400e082d40c0c8a4010480c204001c18044c40c20001d18005031100c0c242000103500813080c4543c0060000100d006c0f0400303000000440c40e410181c81d02c1d12070040851414514814807003508 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314801951 1250 314800701 314800789
    0x3010c27030c1a0705030c0703140c0f060d180507030605070f0909090c0810060e1b07060e01111909060309050309040b01030605130e0c04180605060f 66
    0x4858003000700042050080254141c50648005400381800c0c204011110301c66004000c00c1400081a104043d1901040e2101160b0007180035207450707410391100d941c55070707212800c540e44002c1420300700c80141803010141c101040b25290005906841c144e04101200b0341c0714088806611a940500c10890702707000f0326030000c050341414046102101d40142a076003090154091041c0e071084500c060060140d00100108040307800e50701c61a4171207c048c0040c110a005440060040340081940a5020300000c07201c400d9955616003040c0320340d607daa000c0c180b00385407140d55640343c0c100c0a9958848800410950800101e40401c0700d04460001d01888401d500c0482454601000e25000c102c02004480c40d400c000c59000610b038150f01d00603002014076403c8a0307045050f07150b100c10685aa1340c0718180e04048001210781b100d95020401c03096074000d04c424841c580c8a07403648400201d450300040c0d0402c40c0241a03400c1c084030075000c54042c1d00030030360401000c0104220407504a20a1301d110400b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314803201 1250 314801951 314802017
    0x7050c0a050708010e0c012a320304050a091113060c03020f0601140405090f0f07050406051c15060305011a10020708121c140601120623010c0203010c 66
    0x607461440001c8d09004c10340400202401201181e070124540c100d841600d016844296458480d0705410800d1300341902c4101112404074415070b1841030b45d0000162001c80d000100701c03064860a142a03030b4080d103484141ca1f050010244401e50307510044800300c1d405041c1e103a40351001d200d05070400030f00d40b4043c607180e0006500804010b2000c0d000c03100c6180401c220944000ca0540c85e8854803c1c42c140042050003039a005030800ca4807a07140200301c0074102d81d01141c0501c40c40f40c4070000c11601c10b000000074241c68106035420380010394400300b41d22100400c03010026040790703680c40755401d440d9001882d1a5040380941035000030b1a0024084441a032548010306c081402c0400b80340d80e0340701d0402c00070004000419202c45000d250a00e808039040c2c95181401004828004001c04880039541a80811007a000c0e984030041c0500c0b4038001c41d90503050302201400d40c4100059808a41c80c621410044200f00200150700c0c00d005400b503601c055a140b440128240c3c40c2c5010340d04401c0c0140c1d981c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314804451 1250 314803201 314803213
    0xc090c02010c1701240203070c1e0602150103033009021003050912090f0616030e2d010314102907111f02060105040c050a120507050c0a050708010e 65
    0x301e1441e04058007104174040c0c80c00f2004c0c00540000d074a18000c1d0340d00103110403441e04001c81d07030785662001e8041a0b1250003ca0030360f66106c100030780c0c44006c0000d0500c100f440a400400100c0c1c0f0a4403410303040c0c0030707404100c0d20038000c080c295803e400407603640c080703025201c1d11004114142071501480700302844c503040060341846a40b1503101c0038001640411880089843c24050360f485101080b0b20300024021650b4581501c0343d80303051000b10340141d003c1007100c4050811410b00e4000318281907000020110098031a00344046e1340803c1005027410165685604074050849243c41e80c041d60a84115001c03441c40d01030400390700000b8103c3c0000342280c85030748164091588041d20001540494600340041c1c1c490081070714444412a04030a6801005681080c5038011030118113941c011f96003407000c103414520a0340c103071061880610008054041000e2204125030080703400c40200d1130301d03619101000c00003a107000c40a140a039401e401400040203160b400344100e042c1c140250007e041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314805701 1250 314804451 314804459
    0x50703021501080c24070f050705090705041a0f071113110904050402030a0209040c09060b0f18010926060a060302060306090c1c0b01080711030a0c0c090c02010c1701 73
    0x1440c0c1c954549804e0240b4440b82d4400f40b80303503407690b4044840f000d11214a849081c0c6041c0512200d210f47d6085d2901d0050b10300104c3c00e8146404024405c402030b4030384c0b600d054500340350030104e421504800d01c120f64040c45001c4100144000a2004c3d90180c0541c0140c83c100904102c0c220300c241c11000d1900d840d05400c10102e40d00c0c17400b9983e8546c42290001180c2c0c1c3c0f00d001007030500e501614029486800001040100440b07000020300b9240e041e8010405182c545000c0350103441400030189903200c1c240074403545207480001480c070424041c50014032103a03407003482d07405a0b040d100c80c40781f09200b404445180910f007040711503801049500301b440501d181d034000c128980300281120780140d41d028006620316044208a1304149240542007140b48500c1c49110010050011101d00080040c0c011908292080c0700d0300001102c0c54000e54a0404d00b04400e942a0f0002402120008001c1d00e001403800c450b8030503160400d80a40000c2455030301030f07000802c9012003111015002d2034240041c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314806951 1250 314805701 314805703
    0x510050705060711120a0c0c03030521010501050d0b0409120807030b01050f0d02031317090f010206040c0e1f09060905011d060f220b03010c0201020403020108040f0c0305070605070302150108 84
    0x2e0003405c0b069a1040d0b60701c407010411a0b010956078405419250151800000c141d8064010183e21504078003020041c4042d6042201214081c070031079002410600c6503040900983d0705c0010280b100a1000441c2c285540d101a02c0c005828280310202c2c0c01c482c200400c864240c090f007554902d007460100e00e840c8580c0c200c044117004044c055800690701000191032034820313001802170189c100c011540a8520b00b0352000040d407101c010f44e030148039207d40000341540000b440c0c0c4e003e258022050f000560820846080407030004100020801c1013034107144248455400c6d80010b01003105021900c3c03420300b0900801e441c2c0681c0826040041c0c10000407090251407496a04001b04490441080586000140746800300d151103c0303840d401108003101041c21903000540e14042030b0024401d20100038016400c0340260310000e8046000c00d070000e00007980400b8a064500c0c8203480001005449488040c6010b20940288011801c0004c0c0d200c28036404101d5a05801120b0b13284030159070500100f6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314808201 1250 314806951 314806963
    0x42a0509180102040807080102040602070b280522050a0510080c0901020a020402040e04021011070611011820030303010315051e10062304120305040510050705060711 73
    0x503038286801c00441031030500039011580200801000c071616141c0390f143d518001e600078800c0e40d0261155440015861003a00143c0ea91445483d2a60003001390170b01e00c024030391640080007401c201c000c001e0b074905d079028080c88900f070142108080d851203081105000301c54006e5000ba500c107408084c0389203840f81e07201481c1da5000f08031b04011a00c4145040c010b03458041030341c40096000740003207008200c07418080c4440e44524000c50303205039801001002a10600804410500c403034005130824031603180100d0b00350002000002c00007555072401c00d11300204510091040b14000ca904150b407c0b1070759078103405401110202e02442c9903500d95500c41c400784d0000c80d44800410740300c02c0001c0d010807642c1000007080510103074481d524a0700b1415440310b4160f40c090b42d00030801c416968216001c2a0b09040c075099080300d02e440c5010f080c600c1180201d40914130440c03c04c41d0421000ca815210b01321603014000090f00e4058650301c1d80e00d07140e42440703c000e1200040084040320403c000c5800519 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314809451 1250 314808201 314808211
    0x10e1902011d030307030c050d11030405060f0405060c0c120d0509040e0f0109050c0a230d080c070905041502070c03150f1d46050105042a0509 63
    0x21055a1914140510450300b100049155143c0804a03064082c1a0070050141c0f0031403244060300c0b101181d104084e11401c8800c9802109a4010310051041d41002e400801001e4030004003d800d1541d548000381c141c1c0d002d100c04411580000138000024140303e010503950003804400740c00340000850340208140a1000314500c903584841d10b00e290f0b50000e2182c02c42c40e1003a20028044d00421f402c2480d82c44d40c114103400d00458123500002201600c0144102d03010250410390005c01c41c00e0410011a5068040103550101c810401c80d5a0b0180c01c0202034014940554041041c0c81e19042100e07c20070444540a8154010002a000a4180f403c60800c0e25442041000b4400500c48000002d0905c00d44d002e155610744003441c4070b401140758422014070070b06802c5581c010505c042403249900000744940d14046892001c46150b03a00c0203010031500d00c024204000b0040700d460742401e41d5000d46080c1c41d400401d000e1594810b40000300700d000022110f070581000e9141901050300240c00500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314810701 1250 314809451 314809457
    0x4020607060b0d060c08010b0703050d0506031c020c0f12060417130e0108070603090507060f050d05070e0f03070b16140a081c050610110c06030703020c010e190201 72
    0x800c0001c01c40203a02c03030102d02902801015003429a071800800400d41e0b172404401040b0b03403000000304085c6040072100c4545d0705079510750806010644c5880070702009898558180142c140511414400884a204900003907000700610141e00050001e1031002500740c43c0602c90f0030b00500200040000c031a50800e50125440540784103c850a81880c040e106050549184440002030b80003184202c1d141a00c003600c099643c460307903c40059007181c2a03250002c00310f0f0044082004068020071454140d001d190a00302e02e41086000250b040ba08200c0320311001c90203072503000c0300700d0409c5050328510a809400034981d260400c060780c0028000c0ca1109010483c941685d41d081110a5034a041d18219405c2100d0300ca09031703841c04582503040481644420781940100e09149112406646d0103104040d06107400842c1101d02120307255105070358114988545441c411280e03c40c00009c6102d130482d640d00585560300704c030701c15007510b00d010f04001c4150700c001803104c03079801850045219994242 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314811951 1250 314810701 314810707
    0x90f020f030a14010207020307080105041109040c050a03031706103203100e0c07030e060a170a0f1107050d031d0105070f03061212050a030f110901020c18040206 71
    0xc2e2401100e0b500040611031400014201c0d214150003a2094602c01c400f541c40403502c50728010b080f030f5021900584401868404000c031341c2001650300750454019550350848036180c0c03002c40c1d8500519841200000c498484408070800031807840ba0308603004990071050f088071302500418000040950305070301c0341d00080e003642d0800c50341440e0038050000001c0b48d480346014401c4901813100d40c407800301203003d640e0010703100a00340c2c4102c1e16410381c1511030841d4824880c007031044d242c0100641100740302ca003c81e11301c803034020180360701d21400404c980403d140210203040000d030b84241c1c01b00400a24180203204c001000811800012000c2f460700091600c01000348080029110301a11181c2d441d050901c2500c60740018422804182ca413401cac8021607880700403c4581c1ca45100180030200c003e4038804440f40b1400040511910501d404200300d03442c40b101c0c000304c03510016140b0084000083d01c0130302e560148034044084104403032201210340541540b040045006200a2140b0703c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314813201 1250 314811951 314811979
    0x1f030303020310171606111f09022107080a080316140304030c0309360204080d050910110d230d050402040506041109060d0b030f030a03060504090f02 66
    0x602c1060000301102102e20b5404544c0c840f1444d00c43c00c0007568844030300da04036004a032250140c1e80c2d0200414444006207508211444812041c0b0b00c801c8004c03448503101c002d0100540c0d81e40c180f001250305000c12a0543c84120394485280c07041c55480340290b50401100b21011450031f005407070788007001030f1800824448900085490403600e084034030000f40e000c0309206c1819484418015a9482a20f50303801168441548140344603043c031014000d050350b034803c0c04441c00c1c1c2d111000001c445a40000d4209521141228100200d100d400382c009440890101c519150141d008605000c0702c4c01c042d50041d0081c0708080e00c592071330100303106120381c00000100341200800a061411102c0d003000f610f40200a500c3c030050074050b20141c2c490350030304002c2440761900344a1190a6504900780070329141c0030605100c01341d045101c2001100707640d00c0d078007103813a01c0038440501401e15640c00345a403000b0306903019048400b1a040940510701c2e00c003165000640007003c2d124159011920741c9040040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314814451 1250 314813201 314813221
    0xa03170705030a05030a053d03080f18091005060c0a0c060906030c170a0b030313060c02030f070f0314030d0e0106140d0206030103060216080f070b1f0303030203 71
    0x503034100140706100000c2d503e60f0300c41c1c1c800090f42c000c00703001e4014483c1d0f841e120a020b01885c28200303548441008540d81c180003045030a541c0498400072140504401e9903a118048150840002080039600025212504009405410111400444070402035041868038007002e140700340140380c000d07000004d91100f004020004500466885040f00c00030603242c402c010005842403045401003410129012002801380c00e02070808414082620700c41c2c0d64a20b0f0400c00740408414113501340c00b0400130070743e06005200d520703406003850742c955a609040d03d105061600207105600300d840d802c0030300305102003600005a401100d8114800c4003644d17140002350b905500c1201c240c4030300175181010080d035103032064101104a550750ba01e101c9180c81e402d0103100d1401c40c118070007035000d8810030044c0000340303181d07014140741c1d07032002230758180070100d59103501841d8800c9508aa00c000081030b03e608110413022582d43c84200700329504144401440c89030340c0a00103000041c1410b801200007001010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314815701 1250 314814451 314814457
    0x140910050d0c0309140604030e010819150e0108061e101e03060c020c06030c21010f1a0c2d10050108120c0a0609060b0d12021b0a0317 59
    0x100d07031030003001204101c50014008105000d82129003c5613208910309641d00840c03010b10454042e01c9014500b846400116100340c0020903c1d0b003a14404421030400c071040c3d10074a41240e800c0d028032000142418015504c030740f0146e12080f00d9034419010480103154440c001444a5410040f03010103894030410b00c014021a6003000b01084440447c94101540d5401510203c1c0d001d804100300c11210075030200d840f040110122600054100041014800e000c002080600c52540c0401c43e445c0505505400c4403c00b07902c4428100086802805906040c41c5c0310340304070582400c11803900c00d02a0546480c4c040c012481002c2640c80c019900c00e051146408040c51001c000985e9031049031802100001c0900b030003070319443d2081441401e0b0442807481151018541c1600428850340550355840181444440072220369484030040c200750380b6841101052a407180210702d16524140704000e141c0000b07402010b0f000900d816010b0f40d16269410304009880e00041c854052903100e0703443c481070344 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314816951 1250 314815701 314815717
    0x906040302150d0b0108060d080d09060509071502070509040b060a0e1303020f0a02090f07050d0501090606110703080904021b030a0f08013203210405040c14091005 72
    0x710780c0035003503106041e260008001961150100304040c00d4120011906e0031800c0f5800e40d0484180d400c041e005c21440303000f411101c061020702080500c0c0380d03582c0c10103591095a8a0000e030f404490300303010003022207800340a0b4005600c0140300c0315103003600080480102a00c0540b030110160702180303654807601d200d18080d00032040c226140e814003071400c0150b001044000c0c0c0041c0203503610204400c0b4041200d4141c07603001000d4101903101c50407140b15020010b00603030305000c02040350002040c45800380c9402403e400e0070020f06145454409010310b803c40381d0030705581c1c200842c1400020b20030025108040c00035039005888208005002e04006058810186a480041007560070a0b038400c00021160b0700a83d41e5032120b076130b200082d0710342c8900f844120809900c1c04140c491400c40000c04114902401011948a0840c40b4201c054a003200c00c411035104038009030501c001e0a15020312803200f001880c1c0020b02d1000042b44503024002d0000e5148982000201013507814800e0b4244d520701c2c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314818201 1250 314816951 314816959
    0x20f03182404090b0303040302150c0a050105070c020108010801200f040b0706020304020f150d0b0a1806240507020f0d140a03090605070206030711030c0714031c02120906040302 78
    0xd07444000c1c81c640c00e4001d4400d4210745810241481c030a801d0200c207840890f81d024180d03030f9a5401b5141c114250390001080c004152080540b0400850005d0140b036014941070707104d50300380c2c1080340001058034005802a65040e810600400369030564800c070f01079a14600440b40e0b40702da082108194003881030307910a040c0a00c0c049441c44c140a070550013140214400c541c040c01c2e1003004014046071100700108a2802201801400c0b00c1041b560000c1031203405c0103154010341fa84600e41803420032105040d40889958510b020720440f80c048101c0900b0a00025000c01030382d080e80401803507403240803c002d00801000307000c00301a403251640d5525065024158510b280500b00070b25603a4110800e0039000a402c0031400200300d03000d04200d44155401900141c40c42c2e0722a9003c2c0c6040c400a203140c11107200800102945140c24852000501480c104140c4c440c2000b40070503182040e120011503068902039031400126400003010200d02c040c5034511502e81c0a03070400140346000e20b910207500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314819451 1250 314818201 314818249
    0x40308060111120405130501120809151b0c04060f03020d060b060a120b06120406020702010c021201061a0307080115030e0a0c1d15060c0a06060f0312020f0318 70
    0x103800600913200380c030416200d1010240c00303042468151082803150540d444228100d040105000030001c5c581d04102400c581c41e500d06500008925a00000f504140000c49003000052410f05100000081d1070440d4144142410302c540043c4240f014030000b4441c0903030b082410108117880e0801c6440400061005454841540018125041d2010fa14140302d262143c200004c0c60004196441e900c41064141c0d030b40e035555a9070100030360001100307905000080900400503a00c4010203a284409000085109464048800c84600c80512030100160082c0700f04010b00d6032000390340f030469205411042c4400d0920f00c080d4020160b45800c0b1901e0f0007034007101c03020700068015240840c0d10031a8100030072801c0b28100e01d203081c1c085d500900c039140325100c081180e2a01102030007aa003010f6007501c01c5007409699030070840e81075a200c2a061078000c6030800610613200c0142000c602e19001802e032145100d071245460380720b1112b401d0300200c09409214055240c07440c03103016a8520000c5460 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 314820701 1250 314819451 314819473
    0x90604020c010e0a12180e1302030c0d0c080c010305061008060111060703020a1d010f080702161404110c190305070605070305180d02031e130b0406021002040e040308060111 76
    0x5c2e00d042c1501010501c2050010100144c0071181e4085400e00b11840d0902c0d1140301c26049401141031050764540709892000f20346a03900768054010600c250801d807000d038078080b501414403052445a134103044c0b400301000101c2d144d03050010b805511515200ca0300f991907800688010102d454001c0d242d1062030200031500b9010340c020010100c50380c40e42d128a80710901c450104c0983c0c019402d0004032200203100c2c12500600d101da0300100540150f07044508a2085250345da100340e4414001120b1003110840541400c0c41440b01c0780e10045c8400745804d41c8030b81c0003655912544175481c4000b040500c3c0c942814440c000b5141c0240c4c2c40881802541080d80c8010081c0c2001c4d07c0c80611084d035141c84000d490f0001031400c1c103030010394024500f0500070084c411841c210940600c00c040c1c000300131031841c9081a08448015164205c0b00c80e0300d07076040c6034000b85080948910402d205104000511001c5150607030141d2166143c90042d80d250b590b1741c0100c2d581c100001240060740f0640b08900303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 314821951 1250 314820701 314820713
    0x9020f0c060712060f0b0a0804051f140f2401120c080a0b03060615131a0406170408030a09240b1c031407050313060c0204050a0b090604020c010e0a 65
    0x50450b4240d80000d2081342c0c0c0361305c81001d280405201d59001044100002c400c03841c05261210750260040098072800722000350000c1a40d07007a180910070441d40c6103070602c803000314a004942c2002111001412600d0207640c071310b1001c602c880c410380302c0b005540c443c2d00150f8400c1924180d08412400d0601c0010b41d5200040c068110684807028114182030018104d41800188944030381001031602d82c8668068048095a034800c80d10002c2c06070700c4ca8404103402039910001420182c243c900566101c2c07030b002f0018203450300c0c0c000c086080c52001d400e2001140041d4160780e00500d03000c1000540f5146460300040b101174081d80300305286056050000fa0710100e501c40800060142d40450364888600d5400d0700c41c0c118424024007003448074050004400e02039001d0b0211522410403a4a04006880407210111050740060002140c1020040c110700b02800381980104000d1020301c999441400082c804080041c00c260149501148084203124250446035910021900391948a47c05003070207 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 314823201 1250 314821951 314821967
    0x20a0b0a090b0f13060903141b0f010c02090115080702030f07030f02031c06060306060206060a1710020f030a0b1909181b0302090c0a1704020604080312070f030b0a09020f0c0607 78
    0x41d204000130888028904201040300303279101806402401801d1030860400c01c0c02d5006c1c012036130420850003a00401a12880f00b968060442c600d054040e10035140e5000344190300003480c110440d001444442628034404050354005940342c288407580c43c80804040341f85002c2c203101c43c00ca64011007043d000b29180d6900240c15103038260703400e112954840b10266611002038031101c0d0030166a410030040c10b00901201040c40c4200402d6580748401c500100c5c0070303032b00019541d85036000d0000901c42c440c0c4141c81411482c440640307c6010f080e803074080d814840c1c5040d00c01e004200b81c0f26081c2241c051107ca010114080e032041d4030755400800000d2500340b0364090f02080b4001c0c25804041000d074205d07542903420034242a990904418443c201210761081c001e0812600008103101c08202d4020502c09801d000191a001072054902034000400d800c0d026640e901c1414030b000c3c8040f85a80b038006180080e0b0304410341c0580c6d104080e444d00c002e94440d4481144980c024481809012a071040f42 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 314824451 1250 314823201 314823203
    0x10021906021c15090614090702010e0d090501200a06051f0b0301030203210412060902060a1809111b150106051201080312060d020a0e090307020a0b0a090b0f13060903 73
    0x80300c205141c940e0341304012108680210400700b420725100c0d5005241204031241d028610344004944403180c110302c02e19018480294802040440d0000e200b6564424011560f20440c0d040103803071810315010507925021401c001510a40d1628002022390b000d1004080c0014074554034000e07030565a41c010b410540003030000720301ca0701541d443c0841142c1016502c031290188042c22514091134840101d400980b04041210010b455450420160b80d4000292002d500c1544891103e042000503010304008540c102c1c03800c1a1400f00c05403030442c400000c0d00c141c000d911030707031101d00f035100e90206190000200051340e5140400001003800c0341e1240c05040c0c4110240c4580c056039890f11640da03120b000300103a42040b01026000201c207882e102407501000d80c0003404900c502510340411800a0340e0403158414030780e00c0004c4c0c44d01107040c68a80c0d800102003610b60141060700002c001080181144100b2180d00001700c2c4010902c40d941003124158401c90070000c0007941c2d143d80c00f40180f1aa440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 314825701 1250 314824451 314824481
    0x20f030d0c110d0e100306050d0c0312030c0509010c08040f0602010605010810080604150b030f0304050312040e01060509011806020c0a150f08131403030f0610021906021c 75
    0x2c207020b401e120000d0700219400e002d846001c10515204c00f800240d454440300030f0101900c0d010005040d03203a003141104402c0c01042582006425410440800c0110300000c000700341ca8101e00e680c03c1940f00303095a00f1003000346021718180c120340c10300700e04034084c035044030b0003a090b0f106c000900190154000000ca420a8071017110315030302c800324485d030580c0c0d6209400313064000c0800100007840303002151414401c07988000070040c0343c50780460301d4000a19000001988001018401460200b201004404103210020702d03041c10080c0c2c459400a041c071542042c0040850600040d070702070814041445410303521891041e50303801000b5501d00d0034800590150fa42c2c1080402da00c9100c0c15801501007450300d80c080440c2100004841100004150942070301000740054001201511070034812007804d0015034490902800e07880791000080c003954803481c00c9200000c82d0316008104008200b18111465648170f5440c149000030307109560412502800801d0710f440e40300c0066012a043c0e4201310 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 314826951 1250 314825701 314825717
    0x5070201110f0301060f1b0b0a06051e04050405010b09040c0e13030806010f02030c1504060e010c121505150d0501140d1518030908060a020406080403080601020f030d0c 74
    0x21032011140c0b00c1e1110510710b050b0308000500a4902070840b030300c0001c1c03076450030708010503842c2003440d400c031001e00084400c1c030740075010b02140040a0003914050042100d03000e06030352541d01400c0b4480c459003001405a41c0311400902400000c1d0b002080051019040c11070902d010700d441c1e40c50750201e001c0c810285100c0c0c0085a41a480464021201a072688580401e074070341100644050705c850118a00b1480204000202810240b0640301d420540040003110b038101481d2410039100050302545940c1e02d41201f10300c403540c5c41801600c80bc00c07a5800054105062800141c1d10841c5811442c0c22a45003081c50680e0301450000742080000500204a566200e454064882d81e0444185921144180020300454101d82e00a1452400070344000303100140414031941043d4408002c3d800b10741d1002007040b440d881408919408905400110720305410080c014149071030250015080000344030025525034001c10001401c507001c04102d81e280c44014903680003501050071800d00082002c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 314828201 1250 314826951 314826971
    0x6080a02030402011209050a24050a0e0a020108131709030d0c051c05070b0a06081014010608060d0b04060506040f060b0a1107090603050109030329040507050c0f0105070201 76
    0x60300c2640d02070399050391042e036054800c0c414100500302882040d6918000c14140800103000380c80006809940c58011040311200050207408540e4000c2244060b035003001d03500c000c10316000c200144056030900b00850710740c444001a050300310a84000600580540386884546c0300c01102030241110110102c440b1290740310011160884142d500410a07807000f03901064459088040040005a07407800c1d07820041c0790f0301c40401900c0c041e6000b01000c3d9603400c05115004080c0030119031890342000900c5004103c4e442404160814072030b40c01044189008280260768540681150350b4002c9444440c1d0300f094289200200b805580740b42c4640d01c1d094650244070340354000c0100710340340b178007000c0d082080d0740c2010b031141500300600b401c142c02400301c0810155131a100c1d00015500179000081e1b901402d19002c2c0840714000100d041300310241d02d00300342001d0001d10b000242c2009440c0441c442d140d0390320035101805051500c1c00a8054132105502e8a441503002a00c1600c03198001d220f95203030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 314829451 1250 314828201 314828221
    0x507150e070e070c0b1e010e04111005221e08031b160308030907060503130f02030f070b0909060a051503061c060c14030115270b03010608 61
    0x202800106560300322100802c00c201c600780b56603502c903043c0d081001d4900c00c07036a207500301004229805514002d03201803000e02e40130401902409810400446552402c080c1ca604108802415119214848031020401e059200c0e00545481c40e00b9202003c01520040c4800c016444d00f5000b10911100c40c4403c0010500c4181d880c00100c2c5c0c600b401640ca060300007080c1c9504409041c801c04801e02c039200c0c41c225801080100000294007940c41d4076200d0500d24042e83c240315541d0700500803c0820300a002000c0700c1607051007010359120201d1840c1204a20100b801c054110840602c10b004001000513850452001080d030304208581440d000ea0b46d100800201190718020303075070030103105500e646482e00580c0007180c0104000700001428032001c5062000c14418980c110f9906442d82e0f0403600c61500060748106001906603024159070405112400c50210b0f042850b040000400c035100c00744044080300c0d6500e040c010742419406031120b00382e0026610030702c111000a0a40000200c20b942 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 314830701 1250 314829451 314829461
    0x303021e160b030a06051203030103061404020906101715040f06030b061c0203010614011d1003090c0513020a0210020403150e0f01090308010504060b07020a0330050715 74
    0x340600105160301d05201002035a9007000f450030020950764400418581d0b215030070582c071f102a50300216900c0d819440c24905540d05120390243c0250460107000c0140da40750301c0c4581c40f40c0d00b0f032080403002809540c01c0b02c000140c3c05200301052207120a00c040030b84802c1613040c4208040d5024040201034424113421a01c2522001c0c0c0b4501c50a400314150386030409031542c40140403070a4818810147c0c0000303084604a90002ea03c41c0c090105c4c0c4220303940c0000380b680078040c010800410458800c40420b11b6642c403000188105586c5a421404000448444201908015042c1c1c901002c80792608402540b00224541c007501c180c040035035222200340204c1d420351f6409000303800d0401c002015400509a0250001024080c0300186070011400b40314035010140256103c545a52501d0203000c215240c0f500280c114040412070080582ca070242e84400b200d41c0308900101c010302650907120044c3e000c81410403401220709488080c3c9a01201500200d4010318051441442a0300e0b0402110 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 314831951 1250 314830701 314830723
    0x602030309060604091407060c0b0906060112020f0d05040c1e0f1401030f0212010509010f0501020a0b180a140105060d0201120b03210c060705030c04030f02030c040203010303021e 79
    0x203406800050950704260704540342c081d01c203160310a041d1b5036004070300c2d007404040e41000c0b0020f031142c40300209110b500120580c101030848040c00e101d0030440002054802040504e02003140c00043e039454036002c02c002c0750344170039190004000c1820070f0b2402d041031390305511070071400d801000c4603041014040364003c0704450f0704000103405a860074000b0b194603052944100d0600d47d480c22041303100010ba00007012805c05c01207107481c90750b046c00d007003048131403040e004038031b00200041050101d42d800040e901c1a03d90056080c00c82d03651406405841c1143c1090071080c07030300400051000b000307606140c03015117000010003401107a86560a000310100e4961002e4005440924600840f40d0554004107540720042c0a449000745088130107142e92140092180e80701c800041c000500020501045800c4203151801e40c3c5541840107010344203000700d000150401149410f8881150b80c10406003000f2000540b081d500d0b1360352828041e46640a65510702114454581400034100011900c0d100d40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 314833201 1250 314831951 314831953
    0x5010c05032203020a06060b070606090b010219050f07060c050d0f0801090c030b03031308060a020a140c01180c030b0f06090a0e0c0415050a120b160509120c0102070602030309 77
    0x7140c41e40400c42c8034141c8030300050b01503006021400c2c010070020702686024145007100e156581d05907281c0a4100e400c1d40d408003c841d4a050780824243ea400b0680341294002d500501c1c80d00c000e01d0500f6810000d20005035002407140040c00034046801140c203448650040c4151015850802c405a4003600c209082d4400101540014846a031065010004851151030f0004d460005000401d02d5580308512564001d00782040801c0701d044c042140d940d0010212800b03500340003000e000900000c590080c0d41d425500c0110f8858208042540140d260319011070441a880d5054200b0051042d16804192580c00d003100001c1c01e066100c03c83e8038041c1902604001456541c695124001d014a05a0b806103005d42e2815410700d54880c054001d107815500da103520481c0c54002040301c94091079106164204240c030041c00400c80b040700c961307030100b40040207400c4441c221100712150300c0b41d2200c0c3e641c0008080d4100d07481c018005107240010301d0130b808640b801919024180e80d640403c407903401d91 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 314834451 1250 314833201 314833231
    0x51b060f07170103020d0b04030c240608030408060406020726042402060a020d09170309010b030d0507060b0a091a090603010915150b0d02190c050307020f0604120b010305010c0503 79
    0x42d07c40100550302034002d00e0800c1070780b0019911040413502100c410002440014401600b203030141c447c2100900700e501c010b40c54a0311342507160340c5030b85c80180301170400c1e0b502140c14014021701c8201c000c40c0050002d041305501e09034443c10750780303500326015050f80c464000381030200548460703c0307107a90b04105800400e4265200200d08010354043c07070800b40383c60b0702c03085813500154a0220391200d4486106a45407a86082c1c001d46003142c5690503c64866802408078241085d008000c80b0b90b269089400810a0342200021824415059100d031052603e2706030100620b480c0f92101c103c8400045400c40e000f91a060101030a035807100101500f003080c001d0300e550b1540c01950080300001803009401100342c0e980d002025a40d007106508900580d00003c3e400005c001c5031035025803034540760410036800501c0da10f07a1f1f6900c2c01406130007402602c0074444550701e42e0340c81065400405254003446074264983c42c1c42c03903240c0402c0c402100d0960804002100c4c90340910140c0e0721412501f074140078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 314835701 1250 314834451 314834453
    0x70605030a150303201c0815090103030906050307021c031e150b030910020a02061b070c090509070b0c0a200f01080c160605060f120706051b060f07170103020d 70
    0x340025000008828510841ba100c3e5100012040700c040092502d4aa911035494079280110080e109041c14034411348500b401071002a070401e840e142a03c2562408030340380e039a540b0741649050052960072514411820012807903941c5908001c146503248145e45840b481a003c221051700c42c10541401000c611030401c0c08820398503009541e000030500708440741540d000a008040343c2c0580402d0005030041d0301080000610745400044a820100380a4a401070341d44442c00781c8200e90040014241d115400b18002400411012001d411000d4029595603884840079645605542e003c552a03504144070000d04507020b071038517507469805050301003041984d400441d40c0d280021700581c0401800d02050140c2c401441c0c5403061144905c800044d541001020000500c00c40d82ca454030640460380140c04c584000300e4140100c44c91030801c01c0d00c079584100070000500f50204030512a1085500700401801e407520300c01d018070300e10345640c0407803800c1903a08000000c00f400084d41041440000d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 314836951 1250 314835701 314835737
    0x3061503061d280b13020a1a0304120c0b070f020c03011506030203041a04050d110102090a1401050c100f0501080703030903080a2601030b10050901170a05070605030a150303 76
    0x20603e0055607078400c011400941e81d1503680402070b28595030b00240481003400310304104c1c041c10040d106030390541c03d5410741034850440502c0010401441001c08100540e442c1c0c1c05481c3e500c04642c0d01154030600c6240c001c400406400e00e20301020010b1281510f12295410184a851000001200c104030110704210b810340c007950000e07004a03425082c010103040004c1c0248092801548584060004150159801003021001d030046031043d074410040341d985075440001040403200c0c3c4110008814070038100596081c01501212005406a803070048615842030303110000d1001240e504000c6a40c981600c50b9407010300303000040c0412201c0105202080302400600a058114500303011658444a1302032102149202c0b01c070502c1c1c050000510800164520444d031160000d00c01c055290f1501000071004041031103041c451390800d2546048080081c0f000c0c64403240c00000301d492141c2d0392000142a9031080f2401036086161840d9000095501500746003207940540e51401c0402c0158004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 314838201 1250 314836951 314836993
    0x603110313080f0f120c040e160306091a0a08060103030c06021303021201020a090915090207140303040b090c0405070509041e060801061a04030503070807050703061503061d 76
    0x10342d0300041c184090700c040500303403001300b0b44144410351140d00e4000c41e03511800307100c10241002d102000c05000074081d84a006095951142100c40c0248141602507002e030024019a0000b002480c01c040301c031010005104440c0304002c030f0541d14008072a03500c045e80360300c610080c000140003600d604140c0022642a4000c0e221440442d05500a4580d90b54001545200500c000001c07503500440c0c09144240c00c103e520004212050b0148801070034401c40b040044201c0c0078a10185d58003040c080c4c28000380002d101c031544d00d00c030222580c0b81411b00b4603901d4102d04031016000b61007640d201034654201070140034010701240e21858107154198040202805901c074080010200307400c29180c4480701409550024403402c07000103007940c00c201121003803904c0c42d0311007940340c54200400c000143c40007044881c1a9044200151500440d140c070074100119603001405007070030803401c03202d00c41a10b20310204507807107075a041151044d4150700d06071001403010111101c3d0060066106041100d00784 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 314839451 1250 314838201 314838203
    0x910080a0f050f0a0b040b0a09030f032004091b1103030103060b01020c040c030e010b06090a0b0325050913150312020708010e0a03020c1f0e040e01020a180603110313 73
    0xc0e07500c6500d0030403c0b40e26101d200c4405840b0480060140424060810481500045822003e01458046440c09004500510400d0f800c0564031001c1034400c2003941580f4001c00f40c8070384283d5032590341d044040c015040c0308180c0602a01411f6a10b81c00e41d01440c0d900d03500a4200c4080e44c29a0b196803681e20040c20145945815401410400c4150742d60b82d05c03510310fa08190341c03030001b059242900200d013102e184c084014010a01003010042903590180c00340100e42542102654940c1c0c1d9060b14040d40020440c1042d46a600b0b0120161298018000e03244a000903610b05e0140680c02c0d00c41c1043e502c5400d0700da4041c1c0c11000d07080c00444c840780f41280441e25180100d4100c107684030700503421141010040d05054000941c4102050b505201d0303081c610718101c510640c0c0e11120740411044000d90f01c400d00074082913088503070300e80c0c4a07a00030b4101007202e44000c640f920600200a0500503c00ea014001c041e460500411094000d20410303200e8075003000d0042c1960355001c0b0030607401800c200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 314840701 1250 314839451 314839453
    0x303080c0a1707020604142406030c060a031e1a1219050a020f0108270c0d031d04020c0a0f080705070b0408010c140715140705090910080a0f05 63
    0x84120300c2c01c280c8050b45004040e140e005112a18017414854040000910725200c0c541001c001058440c00c02081c80b04200c2500b19030f55419110040001d107050384a200580e0803003130101c1d4107400e15426600440c240340b000e8a82019010306162050200c0f20322407400408000d442c2c461110500b811244511243c80c20b0048813001000103075600041483c031442282c09600c5103001e00210705001e00040500f40082c2408503241c1054000c8021804580c440c07226482c0444039156801c00c400c2140003640303107010b0040510000c1d68103008088410041030200c03941c0c403160510b0f14a007003030700c00c03111403121007405001c60035450742d98490034215580d025241510103002200102d03070140201001071400001c0c10356128904410582920088200c0805110b10f0001e0801c61090580c1141c112aa000b4ac074040560010300c0c400004100e5014085041c641450800000580082c001d103821142155211203d80d00c40c1a00c4000c440d080c0030703440f041d4126500200018010401403002e1512440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 314841951 1250 314840701 314840717
    0xd0c03110a0803181509030403170904050709091508030a0c11040203071707020303060d0803040213060e19051b0322050d0806030d020c1203091201150f0303080c0a 72
    0x500c4001983e001a958440c04418aa500d080e4000c020401c1c1c2c200b48814041c00360385403400300c030455280e000d40d200250842406825501040b00000b04946541000620400039400e1100c001007000200d8003602c034003035240c103542002080362007082c00c048424071802035150120459040310805c20081e02107549405c2813171a1143d13940c42d40080c44c41640300d0b9840c41c1e640300610004a1200e000607007a1405d6410030000d20000f42c071103065101c4019040140e0075070701c0c1c03120720226180002c0821604941c42c03420302c002c10700e0300344042c50758029201c0e807050000d526a196001d804a0b00240da0704605423100f002d5402c4141c9002001d5a8403200000c41c4e180d1109004030000319400990400f1142034000c114032001c100c1d04141401c1d0800c50035402060702c401c0c0100701a584107079103100540700f88644038a008100c0002c008940103081c001c3e01c20340c407001d20210710300c2c041d01400e050105240b414840220f043c20821382c1607012650503907150302d01d41e207a00c0d00005407940b00d0900d10007041068 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 314843201 1250 314841951 314841953
    0x27021f030b0604032d0b01090203060f0301050901091b0b12060a03050706080109060f06020c0f1f0c2a03150603121d0102030c0a110d05150f090d0c03110a 68
    0xa20050b0000303602450403007170000d91a441000103e0b0201c031800701c1e21311810401902040440c510716064500031080107a0340e4407504002072410740c501c0b03082c40d0b256080000b0046454010340010301018410400f038141658642e00c07503600704200b070064501d64101403207080c48800c10030000a40124020345800d035216243d40754181800c00682060300810040c00c01002445c64500c10388000307001d07a2003200c04850420000945805c00700320250301c146c0500c040b110341c55030351009900c500c10b51801c1100700205004405040c900d4410401e9038156000f07100f0210200c10400110300c11010044815151801c5a4074058142e040450104c1d1a560300c40d00031000800500aa9820558549441e410f400708103d640b450b0100800c101c0c0e0441d0400e00444001050002d22900141e0303100b0b02035608035210f000400c8034910059009080f91040c0400881c071001c175500c6660180d503070080100b01a0365a09074455403005940301d4100000c0031100c6810100b0711035102c01c6031901c3e0103015110156070f2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 314844451 1250 314843201 314843209
    0x3080c0409061509050102030a0806101419030e0a02030604031112030a02190201060b09010c1104050a0c0f0206010612091a0103050106060e01080408030103080a09081027021f030b 79
    0x380d03030002044044183c41402e452508540d4250041070b00344000c5140184202004241d0080508128064190003081400d424011a011480410030b0417801e52a5108210120032810190b4004070101e86000d102c1c074200b0002040e0303401110303006401000b043d100e6580440b0402d090540d11503040c019000700c0b2484000303050056000c0c08102d4130158079211404001000e071a1400510b400350f81c54003004000034007408043c3ca0840c002401d0000086080c0c0c205907400910810329584d0044c540810804014200d500403507001a040d80c801e640e8001c4003800303a917145028050800450074003610301c06100016046100503e106111002a04000442e030000c0b2500a8008884594440c80c0502c071241c0d0055447c24440310900c1c280300c01d07040a49039903540344018000541541c00004603841880e008242e40302c02016100210f45602c0900d94241e13004115041d501207041c08203031942000075624654041c002c5400402c40000000442c0c0c44480401544400c04240340d11401c07403080c2552 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 314845701 1250 314844451 314844461
    0x190c0803150109050316180f0e011a0907090515071b05120c010503060d06090c090e070506070b0f040204061a03090c010302190309030302070204050108210c0a03080c0409 75
    0x81c82100000705034100001520800050700541c0c040e40c0140d046c403401042d112940000c54480400c200800710b00343d4400130203004806590394016042418048040005600100078500b01c01000203040d9004410405d140740d09036003010024104120a005c05d1908012448406034503040044c58410655a04c42e40300001c002a580d006030f150302d040216040c0b116640c01d260980300c000d070820b01e42c0740b070001e4200d01001d00080c1c003a52038800d030201040400c1e4419800c0582103401511519611014440a00032090072907941c0d0040310300000e03041c2050425503045541c00706120303580d40d6941104124810b00200140d030301c039458000c00a015000c4d08070001200310b0703014a00fa5680342111541d0314101c0555401410940304000300d4020710b202034403200840300c040c40c022819509905003100030740a0400065030140ca018000101d490f00040c0c031011100c5150542101d001d1602c2d1200f40c11301031800e044d60181c1000d02d0b807800091040501c3c0e0350084150000790308050f21341b41c1d9941192 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 314846951 1250 314845701 314845711
    0x40906030b04030201050702030c1902060f03090703030207080706080a0203060d020603130308101a0d0609231b0409090206041d011d0103020a1403011e02031f0b190c0803 75
    0x1a1410207002c1030550a001d41540982c0341c0c001546401d4000115036a15440b2206102407142c00040e04070840d5100021601c00c646c000914039100d0500541c00c40e00c51502c2e00c821000340c411320310000740e1a034020400c1421201c0640781c0f84400d94814150802030b50000381680e0340b10034110700610042c1d070b0342009103020b821006101024041c00b0714016000071000341c60700c148401148010042520700f040601d814011503242251240d1040c0c130910b01030003213602302405141c03c03d50582c1005080d80b00b061380001c0305854035803076a12061081445010340308108030304850f00b084240540403494110608803032016090b070385019038030910352101e284a0700c1c1c81000800d040004106010701c0d1160b40301a006c0705141114a545103a00103000054507109000c071180040102d946140c0e402e40c44050401c514141a440030540464071400075030040b03c5a43c10070007090500f5842204440103002a2248100f10500d410070102c0342c0d05440d5400c0d400c0c1c02c00c22503014000000105280f021b103000c0c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 314848201 1250 314846951 314846963
    0x1505040506071107080307080703112b051c0e03042111010f05070615350115030807050c0607050c1e10110f0d020705030d17190204090603 61
    0x1900300300c0b8009083c10f80ca0401020180c1c001c01c42400f01c0d2001108451545506c40e180582d40c4880e40380030f82d0040358801000300c4038001c1c501855030011070038000d1481ca00d400c01c994a084c0310174982c1540d10b07019003545e4186200d0b0040c4064498829a4001c2c0600a010740450b4102a9075040d040b1507221000030072080084000c3d9a142004103113000a403601c0782c242881415001d0900d0020a03a0082400141407651101070110078440c0c100e0003800545101180c040e2509007010350a031108001d1b5100d003a139004008101c1302c044030706100710014cd0f080b18054446507455900c0f000750b507402c07807002600e9074011102c540541d03a0703822000b4202e042c41400a020240180c0342003100940d071001d21214644088030803020996501e4204480305002401d14802c0c1c1503aa40d070f02440c01c1e001c060320320780034450000400e00e07250b0002089000c84104404503003100c10050400c0700e03503091511410748180600c001040b0704051b9070001006030300710341c08014206a0768540a6083d01c986038410f0b152 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 314849451 1250 314848201 314848213
    0x3060302040c0203071203050a18060509060f0105180c0903010203130c0b120a05250201020d0e070b041502010e0a200901080601051e12010b0a0801050702100915050405 74
    0x1141001d019800b0381c0341e220300103107080c0305880d11900740c15620031320204109a03507407000034540c9246034050500406104241c5c0120415842d080004040640d030302c020f18845c000000f6200c0030780c13101302ca05841d40500036510240b568055000d5108019207450301203441800705a01e05c0d142440a18483e4544100380c292100c20790503c07603000d803070580058800400402c402d1441c8a003c400d0550090141c0c400040c1c40d958402c2d180ca103403440302c2032105448401303903940300e2469415005015000d51211b0304001c50804062031070b6a40d18107200d05030854400380010440413114041d0340403525503030300010581c54950101c2d24180002440c0468445041148032410800da06003081050340d400c0e51844101c1d41030000d01a66034005116003481011900c4800d800b01c0c20303600b0303c0c04a0200241c80b0785025100000864080c2010741102c9005c1c03440726000156080050151502844540d00070b000044090100c00014002002013a20b05c0e4016282c2e000b280e0440c0d201d218400da01540103010303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 314850701 1250 314849451 314849453
    0xa030b2716050a020c010f120c08090d030612020607021807050301060801080f07030b09011503060608060f1302100c05030714010606030606080c090f0a0b0c1203090a260406030603 79
    0x548030516151001005414807000b50ba441c0c0020f6075020685e007d0800c40c04140040c0412100e55000d1544108514104420700606641101502c0d0050701c40c00250360140c00310000442c00c540046c030691074008030a007040f0001d030278100018054240007401ea5000141079a0701c8070302003c2c00380c0c1c23944001100000100710310380d0b10600b2140035102c98000703460b2100c1c49400d055038802150002502942c0c104000c40d248034400d6206458a006070410818180e40d41d0420368010304145c881c0141170f000d01c500090000700d81c112540d100300b05981c80d903943d50b6182e4003802900408200301d00d041c054400b07844801b29100300080d020041c0300c0d0349400e007200a1441260b0030b43d0707004d500c020180341c20403034107111098000101325031045c0d02d243e40c03035200c42007100002c54083da10302c10150004410a008914003240130020403000d07920508946252081c411004042e100840e0814156044694000c0c002014040300c285440074090301122051401c200d00c5080d0382c0154481c034003090791400100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 314851951 1250 314850701 314850721
    0xb130f0f0c06080402060a084203073b04050c0f010f141c11030a050601050f0702120109050f0106060224010b0c01060308030709061808030a030b27 65
    0xc0041e10040c581210f07a0b041581c00304105024040130182400303071580000e0095581080c00e42752081c5410401ca01481082810f5890300d0298510401c9400365151940b95a0500182000445040e802040310b0a008980b414140d04000e100002e01441e42ca28020305841220282c503000d54040c0000c0c100e204d003080c1c200414007081d0040e6905100180b6280703816650809a01d050888110f12559603c030005251000c014164400d1405490b10340307225591883c00240203903104e103810382c0003008185c49040040d50540036540903641c2c4250108080c40c0141000064a0002d44a0000209100e076066480500f44034010320200411782d510401000745a904014142c240c5040409000019a1322401103940c640140140e5403003003800035940d25615425440702004580184000703490f4101403c0060941e04c0c14401c00e800112042e89640701e03090042e445004a9030004015803a05109060550140c0072508030650711402d80049104000d07481c1001e4107038445400788c0c01c4058900302e0b04503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 314853201 1250 314851951 314851973
    0xb04050703060e06040f0b09040602070b07021b120102070609060516140307030c05040909030503060f0f090105090a0e0307050d03051008060112170a0804021507020d0b130f0f 77
    0x1403030425003030400400018100101d056000001520013003004e04e100341c1d103c0c001d4600700030308076004100d01007000240300720380d40a000303c02d2050000c8882502d6440040740c0d43c40b20324800345400100c400e000707a81840c0c00510801c80004100000d4140750454583c170f001c540b10380d003007969003a8a1b0b0040100300303000312100003459401c50405000103400c0b581ca600304d40c0002440c0105140e9216482c1500c1c034001c10940b801808404009d1000c1c0e03000389801810303034005403081307800703a130142c03227100362500c3e01d080007110240003c2d08005a0342e1038602089115140a0044188143d4440d6040046075042c401021b005010700e004192842c03074600001d080b644024500d040030701d01c002c2e052061400109445045818941c60040160158101a0030710704c0c540c0ca0947c0490800154401a00d801800180c8114002c90f60b0854540054105814921800b0002075001b02e60b81c40b00c00004041c0811150440d540001a0011000030380d901800110f91443c1a528080040c40d69401c004140b044 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 314854451 1250 314853201 314853211
    0x40c210606090c21090f0f02011706060706050601050f0703030b09060d050a0803040809060d0b030705060a021e0a141006050303090d0f02030c0a06050a02060a1407210c030b0405 78
    0x10070001003107500c03001844c0e508a090b142000c0c10b9900078003250f502d07040d00700b040b03081e41002081c40c402c10107241420602c91000c80480c089101c1a50f40c1003030080301c01d4036500c80c400241c84a480e210f02541c4450090400512035030501c038045c880c0c483c0800a00c03010b000b88501c241c50000d1503055140410411450061030306225100c181109000648081440304180d58412500c40d00c9485610380100c0d0350040c0c507803ca070080400700310b1440c0a0402c0d0820007007004294142e456840c0c841050044503c00c07503503414090703401075038031248010011700307003800d0014180c0940d9403048540c0c0e101038000126200c264059404403289074440b043c1ca10900c401840110021460720801c2c04c0407420501d07591070040c5c0200d040039110790030740d00c0601c00301400090060020b840c0540f503c2010b800c41d00980035800051003088001000000ca40c070032845281c0c0424846030860382c99400c201c40e1000c20841388440724545800100294105016426000e90540c802103081001981448116080144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 314855701 1250 314854451 314854469
    0xa02070615121209050d080703030b010f0e19080102070302030c0d020a0f0204020a0507060e1c08040b011e0308340b040204050606090909010b01090609180203040c210606 75
    0x11080140360100300800201d00c3d03010107140300a0f404540280c40200040d4001a00b103c42c42c00c0f41010810190028102c25100781c5041241d000041c00441d1159250700141c00031030402940007500746000c44d568083d50b0034640380b8004007910340a085003a80c000c1441100542d20118a014442e0b41c01d000d144030819461004100941654480e00c1d640916840302074040c5500080008040717110b501212030306c41e0071040c107100650080340034940d54030498440c0d04480101614081071144030b040d40d140505e8011110364031076402c04800a600700450310300482900d5102000000280d40d0001070412915031108481c07026111801c0c40b0140d00c411800200285004d1200c40009150241100d42280d010f4400082c5643c0702c6003c60f88901c250300309264031a92170410040c0380c1005400000100c0000e030b0301e00d2101550340d00103a4a030100c50050120800319201d8075a410085503002e10f0340140900b12280e00c555440c9506203102090b03100c018080d00c850b91152042c8211801420020041c40ba = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 314856951 1250 314855701 314855741
    0x60c1b010507260409090f110402120c0306030307120206090d050406080711120706060f09050103050d0e04021303050307170901120905070308130e07030b1e0114030a020706 76
    0xd612441400c0300719000c81c1c8000025100c035801d503c40700055402902e00c41c2c034100120795040c00d05050364004a0b100310780e800007240c2980024100b60081c0c410107a280b03d000c01d40c03074580c41c10a1160360001001c07160103100c14030100003c42c445000c3c881ea40b441540103081306041c00d20086040c071042510030002c1c401d080008110b401e070b22080140e0305c11802d1a044145008030301e001808c100849e1294000f107840810f80e001408101c0d0f103c0c008480001d1030303200800e59140031580658000f4030020700b054000e03c461005083c05079450021401000340010b01d0428203100c0c5100078800c41d00203a80503407000c103110f01008416052040140c0a880c0101c2c101b0799080002012140311004103050f0f10f86405410081050800c42c06015650128031251540c2e490031b100e40d5400349502c5110b5a000011001c200c0c030a01034070503420845009072a0a075198555207402e40d114607404501d5041003038044c0290b0586007800091805600e0b840c00140ea40c0070f05017002002e03190000d2800001a40385 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 314858201 1250 314856951 314856953
    0xf0a0e091005041d011508011d0604030c061407080106080915011e0815040302070b1e0c3c0c0306010302040c120510052701090e0705060c1b010507 65
    0x40c0c284040b540100d82c0070aa04075030b604094036070500700300010901d609003110240800c01c00c0c0400710542e0700d8a4001c020340b90381e80ca074540c50f040c203810883c400b51f0810390206021a04c2a83e644403c64041c200c0498200645916040e0110089940700700052041005210480c5d004c404c0a4018941e90001d0450276203100407400d6801c4c061090345c502003000e44c0198420054540c00300c0c010000c3e0803d403903007a512980c01080c513440c104c6040300180200b110126140070710100340da03811900c002d004020001c550103241c48661019079038a959100d1050782c040303030000049500108020301000300d4004d0300ca803002e101c3d03d00c11452410b40260041000e07d196501c00080041c110b0760100c801240c1002c400d041030321842c0c04502401c0e159400c002c1009040e440140c590310480318252020881070700d250004098136145220002c1010380a5401042081c002d0b400004203203080c441030b1095107035514000b0b06240d006441c00320260f04011500494a54000443c01c14450282000c601c0c005035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 314859451 1250 314858201 314858221
    0x15050c060c0c01090c17060f01030c0915150e12211b06010303050a23070f03020c0604090603020a060201020903190c03230705010311090d0203030d020f0a0e09 70
    0x100a50040800401d034441c04003000d4201c139007200e4000308031107082c42e00c40200c810355095802180f4018401c500100e0480c00c442c0c0d50090499030840d105142c0141848030080140040000310815000c5404000c140c919614032a2000c0d6a440d85410450030182000e0054143d0590b101290301c1d04001800d01c0030138001951410034040f04180643d6580061543e12102840460f01144520401001008254001c0003c004540aa4031003060090402c0c2c652942d2504481c0749500c1c0090500040001030080d0203150034051090042d1845421948046016600994071084c04c1944600d810802d60411000480123002d940c030080d4500b185c41c1e00440c1d902d103203000c2c0402c480b9140d001c1d040244003134450460003556000803d401c0c64011000d060243c001c0c031125180550003017a1000400f0346c0248030310f500300035030051910f0270015041c04011460210170300507a0103020410014190707408034170082c007a80c3c4171008215200d50001030010005080300f01110b01400103402800b028800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 314860701 1250 314859451 314859463
    0x5190c03021e16030c080403050f1e0a0c0302011b06052a030403080106080a141e1503060601050a140a03061701091e02031e011b080c1905070f030201020415050c 71
    0x240608140070342417298601000d16100b2540090480d003e00540c41e50488000714568441c4441d280c03565844082c404a01500d404410740c0080810f005100b0400040d4007484075005002d152048400440149469200035110111040c04075801c01c0c0b42e0150100303048030206001e02c51030303140c0c2c5411403a040d500074281c0784041c0202d6060158000004900d21510b1304a884080020a03030b040d90b60034001c071420b41c40c1e6243c50004d03206580c22000250b4028128410400441c40100108641d4035900c0040d901070740800c5a1000b0081038001c9844e84400c044000c0c0301038200c1d03603400503001d49015160809003154000181e20340c2d0400c040c410201c2c01c0b003407160000501256918804230201d10000c4c2c60104290b80700092081003600c100184001940442410294100b40c000c1c80e0510810482d5000011204050700e02e20a02490521b159091400e080300c02c11428014a804510385950031003503464101140180e4001605200b207951003280318106550504141c0e051a40b03a103081c0c0d440d07003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 314861951 1250 314860701 314860703
    0x30f06090d02071d0c04080a0b04020405091c0f11070807080f030c330f0115020309030a0b070c08160c0e04053409050a0c0f090905190c03021e16 64
    0x5484c08184c4041049045030000d02d08201202c106112a19100c0040d18089400341d101e50318000006d148a1404226002c0c0c4400c1c102c9800c0585050b48410303205814414562820014400e910114600e41002a50081e000d01001040c0c0d4504c0c00580343d2400c00d00360080703000c6800500c82d0000c8143e00140703404a4164198042c480025540136001c520040d2a520064825004091010842d8840030150586220015088242f00c0b84032043c0da80c0d119110900f41c00d5800700f8080004104404c0c038054100c04a0301d0540741d04400307502c0d000c000390040ca201440610004030311404100503014800010100801f00128038901a240e040c0c440180c00b010a40c0008151413501e48400030080320901400c950354024400e41c0c64140c4800101801c46044908a16001c6104002d90058400600103a09907840d5140242071401a90103400e000d010041c45d44040c103900d140c00b00c0d0601035080fa41782d0075500180c84014504180a049010f615840c40c0703403404100e000807004400380205099 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 314863201 1250 314861951 314861999
    0x605060423041808030a09081b12030c0702090615040806100608010302010c0204020a0306080105010603060602010b030c0f2205040f05151920070f12030b060d090201030209030f06090d0207 83
    0x2540c40c50486c001400c80f42e400144118800503515100030302101e440041c9049480841c0c8507400c0341102115140700a49411001c40d805004c17450061501d07054640d400100688a90b0f50607001444084098100750000d15a517000481040300702c9000c00381d64001841503180c40c0045503d541c0002c0e25034021428040e020b1900059441c200718086c4d0090f10081903401c00030821585d40d07030700003802454a03001d400015403c10380b54030680c0c0340c0040c40814241c0c0c001c12200d081c1c00c0e10000c0000940b03000e1405403440c1d40010104081c40c48c68800c2d94440c9006d00c04546a5181d10724015040c5004031b0f00d00102c0200c81ca01740b00c081d030b26503144003498005e0302d40c0009442e50803185030a9001104003038141400d10000313060b0300704120359850a88036407041807100901c402c5940240c00341d51a40d40c91a4200c1401c0c0300c48034031030f9802d4002c1c03603819006041c011320701001d48010a0034104549010b030702a41c03002091100b4400c04004c0714514040c00e1000d03010050a040c00040c829a100c01c4c00a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 314864451 1250 314863201 314863207
    0x1e030115030f151401020f060c04090914010f060905010806040302060403050307020c0d08120601080121060f1406015c01060f05150316030605060423041808 69
    0x1940300325400743c40034400b481808940c02e590b0f8048142e01d510000380480c0140107036401010310200010f0b80c2405603400351070042c18141040c0702200180b40b02e11050b07902d145000104280ba220070310890641108125001c612141801070700426101d042e409100b190f8403c80400020039800700390990000c3d407603d05980c3d2034950140032490081c1c00860030368445c0194103c1410801c1240c02002500002204200142c0d82e680064a5554003449a02003486240300340119400300d048080b483c06200d4140011503040391a0341008035403d079072641404d9510b10060169035a08078564540b5004440e00305100748003450701d002c0345841804062076900000c9031076001141e0b400c520f400083c9518903c58070a550030502028085e24052048009440f403001002c2024107110030106079510380000396501e50f0311000b446101c20520200320f81d04140d654400172415540b6031000b00003c02c407100031070074a00e09032904044103041c0c40d01900e1140c1c2c07a00320459102c191000b00081c9681c0c00c1101d20b52 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 314865701 1250 314864451 314864471
    0x1805010804171317070f080703060c050d050901020a02010e16090b0a0302040e03070318060504030b071404080c1c0c060f0e040501090c08060405010311040e1903051e03011503 77
    0x2c5240204103500c00d504401c04404643d20391111851041a11302004030b4440076500c030f09103e01112603000c1c44c1d80c15002500e003032001c00c669400094001c501483c050f440d103803540e01e000007124025140d888869400041d0380503416824019a400103403518003801c00074038910702c000303030007442845801d00c1f50b611182e000d4000d13941c1103052001550042c1040c0030f60340f0311040081d00d0b80c0c01114102d000c5100b040c1c101800040b098800c1d0240c400e90b881e06032404d410340e1180078000000030f0080007040030b0326908480c4d85c1c0039107001d40000c7c19441c005141412549040149507200d0a0004042110722000301000c120281c02c2a001c0312585c0c18104c0a80d689400c003211604c55002c90300b07400c20b08140000913114002e901c0b000c0d030740c081565000c2c010380b5490b040205640c028171001e072030b444e00501c5085d168549640200f005031001c800f207a0707941d50070620019541d01c144d41c00750007003040441c0d001d40030113200c070030041a001c010051510310341c104a4103c4108007240024000c02d5907840b5411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 314866951 1250 314865701 314865743
    0xf161e080705010c030507020402040f151106130609050709020a0314060a0e130803191109090109150e011403010b01090321030b06070c150e090f040203010204241805010804 76
    0xb081f840e0041c206550340d5031905d401d03010003400c511070080d0100172072a541c00c00c188541d4090701e01007903100150031540c480f0a0056507085180d6010368825564004440005508001c4203009248220000d40c40d170070800380243c205c1e6810414240010000b10400502e540c984080e0000c0d10501e01c050b45958694418520b1320b4240110002d02041c800010b101c00d1702208030448401d000c252509202d04160926051040c0c000c010103103070065a0940140111051904103101e150100295012450741c0c56a92514603c030a9018208850305899000c0d000e060070701035104503500c01e080c00c2c203030f0a146680d107081c11000240a250072201c0000d20b0032186220340c100302e0032400e0041109464484901304080042c8051085540d80c1c002d181c02115414004c020758106203500401c011202d0740c4074030301144080070040040307a06540c00c11001c10910b0303850071500c0c55110603104d00401c2c4860340304c0140080e200c44521100030780544070308004c00d80c0d0201c041c03981319a0000d818460100c0d000c40704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 314868201 1250 314866951 314866957
    0x5040302040c201513020108270d080402031603080d180c0e1501030e0a03030504020f04150608070203031b070c0308041d060402070f0209090f161e080705010c0305 72
    0x90886541c0000c0300e0903d0141c00140c404800320448040c00312922800181d41000c07140800c020301041d0400c00091811340d405480c00c109031048810340c14801c2d11403007042c3c02d00003802a900c0c00300d1644d009110a50600b044041c22003a85410481c081d181991191036460055601d28090583c41c0c4049002050000d95554181548804600c468036100e01007060300c06c00448101d40c00c0c80c1d5140740138103558841c1c0694140e03024150007500d050a002d40f011005000003c0c0b041e41c011940070442031a40d1181d104001800703a103420303001d40341070410b41d000b403c100c1c000e042d00381158014400d1120507030200c584410240280d152642d6100401d140002c996212607101910250010400040559a41408002100d10084002d61658412040000b00e000b030400180090000010715401420550045600034500078103e074480c0c01208140c5140c42d540c0c40000600c14150103041003000b810600c8444010101c100700451541071510450352071040381300d05410011840006001c3c14010303070071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 314869451 1250 314868201 314868227
    0x80705010e0604121d0a06180e1003030206070804030504151b0507080708030f031617040f060f050f04031803140705030d02030c06040303150905070c0c050a0605040302040c 76
    0x582d0b035030b4078082c1403491081401828050114081080d00c0710440c185281c2003806903c014014403800d410900c08031501ca40c2d485405100c1c030a64940800c0a555441010388110309a4810380481401c42ca8000d040c500c0140802e0180000f2000740400250820251026a030303c40e180b42c0715200a10307904540c00d410310106600549011b80c0c0c480103200e80840d400003655460012507142c5503a0380100e1b07541c0d210719403059640f0300061000c40d03581d00d101803c1ca40003085500e013440c8551480c07400d020b4070072000d81c1c0860301c0f912140800030422925000d01c0011510a02c4200f01c1450704d0140246c1145000b031008082060078000c111107002000c00c401c004e03503044010180c544d0150168550307105a07900549100317100e80c0c061094120320010031a03403a03a0440c800b80460352070340d540c207501821109030100c00310b00005101150074002803180f1807284400c0d5855a042c03002a05102100e40d00f51b40015006200b40b04e0b050101c00d400908030b130202c07941680c0025092100340412200b00e05a461 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 314870701 1250 314869451 314869453
    0x150b0708032d0603250b0c1c0206010815041101030b04110c0f1c02120a0207051005030604060b130308070615060504060315151d09070909110304050307080705010e 72
    0x72a80d03914242c2c406101d0b2140500350100e800700812140d01d9080321407941c10003002402c45c0740081c4002e00114014103440220101162400454520320001200074a114540141c4c0404010082c041003084080001100b1402000581c1443d4a400300c040b40091000c0d03040c180c9815070382c1c51a480719805503a00345d100b4008140c4800041200725264000301c1c0c0c9414161040c0490341d69021100700d6014038865858005043e87c1443e044418403d4010000714010350040c0f0381c00080c2d40e1641884883c42c00c4950795161f40d00e03d040c90800040721451341049800c24024002e0180303c6a40060607010341303801100309030700c4198070b10b04107028042a00d488100000d0a0798005922500f01c00078005458141c0ca0602007802518946903046041b4460240f001000b10f0221101a0144802e501c16202c400095520101070a011409083d000e9540c14001070354180304208000c102e10034018a4000844080d140d81400d4171144d40d03038014001c01078204800001c00d4810488254001036a541e4054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 314871951 1250 314870701 314870761
    0x2103090c0b1624060503010b0a030b10090c050901030e0c090c070f080a090303021203070f0c080c070e0a150f050405130f0b0403030b0102061902030c0d02030a0207030201150b070803 80
    0x90860480352940d100c98110141c2044c1004c500d83c034042c00340f400058809010f072041c041c9183c80b0303140301c0c520160403040e00f01d50001c0301140c0e14500f40036035084010141c590a64620207200014210f0300e040e1040e0a00ba0040700315030001e641c881304000d822001030605a5121103290400341501c298050008214a000240d030b20484c0350400c000c40c049a00a800f544c20040a046414a03188011240c54000a4421b0640c008090061140000c1c0c43d02601601d41410041d1030001c0c03911040390460142d8148080402c03a00b40c00318001e909841c1c1108070320000c0c0310300d0120000d000307510302c0c0200c0388141c0c1c0b2400002c04244061900e9025127401c1050803450b183c040c1051442d280f07064900741c00090414841c490300d540001115401200b1000c400076020420354410780080d00050071000d03854408001c40c8110301390500185010f500d60180040c0d8540d6640350190845080240d5102804240182008000705202c2038a0045400080150341c1e59a00745031147c018141101402040350380b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 314873201 1250 314871951 314871983
    0xc061510020616120b06390a230118020a060201020f042c0a0212010504050105011d010e04110318010b0307060e0a03080a03150f0b1804090209042103090c0b16 70
    0x6001103a40100e001040010700d84103512400754001c9055080d0300c07c41d0b00140a92002a00c100004414100341040840c60b0841d600c1000303083d1011000d03414450f8042400d02c2044d840d0910240e4001c0c805c9000840c07400010002401e1300340614458081c450003440c1054580035800c1d400c2c50b4010006145181b8180b03071125040000303401c50340c650a0340c2000007001040034102031154034180d4005841e440000115070b84082d044607481101c00c1e040220201144450b5101da008001c8001448112940c480c50802c82c013084440d11001100d266030b0416200e60890346002c2240760030759481d40b6007a0660012540480e42c651116480203000308000240e00411692542c0158085041170b001692aaa6035800500000940380241080407008011481d060031400040d8410b150018001080350302c104e0300000c03178940c4201c50a0310000d0a692800038500d86691904082400a0400304078140f020744034550345c1d42d154090711034202c100045511440804503205003440340e012400241d80341c0b076 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 314874451 1250 314873201 314873227
    0x1c140304060f030204050609040f0f1518090201080609180d031e0c08010603022206031b0206040c06080403020c0301110c150c09150c061510020616120b06 68
    0x611036078000a0309522a104128441d008540845d58001d040300e050840d48000c00c0010300102c0c83d500b117502d58034120104100082d0180704600a00321710b144900514259800429030035040e10241c100f03203090b85980041c1e8000303c1c16600a4000e4541070505c0c0e5601000420a039540f0701c02c41d442e48541840451825415044000840300020441040b10f81c05000b01080d22203000c0802d020641c03181c0140569880707607000d000e4608801e2900a00405081d041c18071590071900210002600c841e0074400a03042e0827401145000f0500c000e110b075107030649901481145038000c40742008045804113060500c04c010040b280b9400034000c0150500004c20f00f4001d51002884420f5400358503120340e0040c80d902070452003000b83c010403600d00a8580108001001c140502c0312207014140142c007008031040144901c141c46105d59140402d41c2d07442040000d014040c6076404550015040254101d030a034042496803400d4201144194401e1206002402c0d0382410f05411841c00300700740c41c01d01c0c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 314875701 1250 314874451 314874457
    0xb090d05030309010606110f06060f01020c1e0a05030a0f0807060608060915010b090f0402090d0507030b04051009030f0f020705030d0503010905070f1403070203090405010e24010e1c1403 82
    0x10701611060400ca8040c56043d40b1134000e2121030201c2e410200004884e2f007042d001c0d441e88100140b06542a0358416400202c00c170a110a4035120101c89801ea601142030084917840070300340c100d0003402121415500c9d80000140600020034007000443d0340782c2004282d401c60005072046800f566a5843d003c01e40954448055080ca00c61005001c00094014074031002c94500702c0004c3c0403100e10000e40c2042c030010358010310103590052200f040300c02c0801e0f02441100083c510400460105013400c0c140715103880003100561fa095440e20a00000280d045810001e030700c03c190505500074000520300f0780c01c0c0600381d40440c1d01030043c038600343c0d6400d5005004505a40d0041000c001503160a00c007107540c4645901c108002c83c403051040114041c180e4051548400e180c4100c83c64512010003140540d0002e900015520085100b0b02981c825445016a502d9001d81c814404034010b402c002062036a88060f4140102c5150480001e07000746c040000c284250403100c42c0020404003011183d40798 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 314876951 1250 314875701 314875709
    0xe15041106070606090c18060917070e0108030703093204060504110702132007050c060a11010e060f1302060f031312170f0c0c070902190e09010b090d050303090106 72
    0x9100c1c180b45142c0941c00d05810320a60321252703908120142494180504030301000a00151481084000180090b1030b656041c007130400030f00511380780e4811346000341070000182c1100c7c0502246007003090740302020344002d8092a4450104c4c46410b014200030400524040d00b08541050905003a18240017919004000c3d061007a2020101805151505d10450f160061000e00c055458034082840c45c10a002400708a4024000d603880c0310140c0001034403551003010a180410f2041a14134641082032066494190900020700714501d0a100300403000c0c0401410440d00300310070b184078820341d2901416030b80403c031450000c9560742407000c0b0709940360a0300101100d0000d907400d80547d099220321442c030030b4840540b00401050b04c8048545500800c001c08080003050188070340c1a255108000c80c0c0010078a048005036585001c40c698550785010507030440a124417040f40070b202c3e1b1141220181100d115038400c0b41c80301d1110000449e140c00d881c5002e4004d10011007070083c01078040d4044421a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 314878201 1250 314876951 314876957
    0x3190e06070e03010603020303040b03060307150e0a0803120c0f0d050a09020a1d04030516050313030c15120b01050f070605090105011406030f04150606030e010e15041106070606090c 80
    0x8441142e04240c20fa84a5010003501a0014803003081200650b40282d90031a50003816079030325949400c42407810403c200c401c40000341d5440c0c42d105140c01d1008400e00945800c8000e94a04a07c1c0180603011a501a125400210000500c0400d081d00c0c0c900b9209010381c044424405401c01c2200300020302000241a44250f01102001480c03009003140790090112041c00780d00c083c3c2d1103850a80700c90b040010450043d140c14940c080001e10240010b00480c20b058010541503070450518001aa400b42c1224010320404600c0e08162074112041c0c04d89c0b9282000f0211301800c6d5600100c0e02130040202640c3c0b8800d0200c0c000c01080180d80002c4d03c44c2101d200200000c4ea6500e0010400c81190701d01c0c150809406c05c003090003008204441340e44140a00140c80c03c0d8488040b24000706c1d2500d61042e000030781e88130707082901c0070020b00400502114100080c000f111102c510441f030858042d10003010741c144410425185c0c2c8402094400c007903003060741041010360300c410003805040c4107481c031800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 314879451 1250 314878201 314878217
    0x22101060906150906141c050a1a011709010f1d100216020d050f060709030b0c09032a0a0902030405010b04140c0c0c0607061401090507050d0203190e0607 68
    0x45182c008961862140c0b6568890456203408016201c2d000d0f00b14403086d1080c0200100005d010502441340710013501554005a18a022003a035030840d546801a00d92a580002c02c041c0c0c81ea900070440000c1650220081000340c458904480c01800494500450386082c41403c00c00d54808a424083c480140d0302076540c1026000d9081049200d0300c481040d2880011510101500f040365010049a03c03540442d480001c400004034905181214007070009414000140b007007155200000350070a0000a1042c18581c0170b000103a16001c041d11404600d141d428001c0d0800e14a10700c0489155070041c10a004c183c1c0c035070640c00c1c0694030880c0c09072229801c20103181c209050074400c2821440401f009640385455000c0302c001c203984520b0300b0070182c2c410b032000d40c030740c40d0303681802040891700c02d61000a210b40319403425003a0040c1640040c844618003030401c40d1716508071040718500c014140c030044c0e50765070300c20038200400300340101d10898518000340c500090200040c024000c6925840d802c803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 314880701 1250 314879451 314879459
    0xf02060105090103170c071e081b0103020c3c030a170601050f031e1807030609290a0b04020f0d09020a0b0d0c0314040b040b04022101060906 62
    0x1998400a224842d04120003000400210f0800c07100098007038004800315141c050746550507890502190001d110070240680040380b80041ca0704903100500a10000e040d1300ca900d50626510310700380c0c80303d182c10315400040e00c11030450103100d40410341d03864011652007607000e000d03898110b1202c0c800802e00320103104000f08440d18000281d50f800051a034030b01205044043d00c400079201c0182c44241409000d000740400b51540c040914440e0040303c0c1010509504000c001e0b2034008042c101c8200f00c64080d5140c081d04c1c1c0c0101d0b090080e690410f8020031070614500d07000712803500701c0e500100f0411744202d80511100c0340e01207090050800d104140104410007003040202d108d980754240c222034007040380c40c42140c10703604a00000d60000b040e8205281d03032180588620ba2010500d065555950000102841e800d031007803010f07103488a40f80c0b45951905a440028401001e04098000c500e172900160031903403030309801d403100707040038103004a954450b2043c940038181c43e00503044da040c00c1c07a0000c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 314881951 1250 314880701 314880703
    0x17060106171b041a070b160c260c0a031119140f01020406080f01290313050d090e0a0203040c050118120b0f1308090f0307080609060402010f02 63
    0x85190303110648001152904900d01c2401d4100c4200070030406418000040d4030104c10510301003a50071921007554540c10340c85d0034402680300800c1812101c482407402c40d03001c0d60115059400a52000da90707014440c0424880300c2c03d4503c00e04512a4844c00a511111240080340c0e200307030319102c0d40311141400d0180da0400d03142e640485204085003c445010408a0b040a0740824109006002da0700907012104406081e41d0181e0410408a8001000d00c17a2a0b1200c012160050443c021541401100901c00c2c2c0300765141206240961040032021800180c8106d10300d01041d80d119080719111440c0030000f0300a007002d441004240c00c28000041e080401d03a0084a214982c003015040c802c508080065522811082c84405201034658001c2482c1c4040c14011850f1030140c01054800c2c07826010900c074544008104203485060034041c2c0300007450070000e580340528201c80001108613164046440e1841d00d60021a0500c030310000d0000b50320000c07407a41e0056000f139131b9121108120780410307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 314883201 1250 314881951 314881967
    0x6020a090e070c051b01090b1902061807030f030314011502010b12031b0a060609050a0b0f18060f090406020301030303050f2a0f0a090603061e26030417060106 70
    0x540150840c4005ca00c00c0070350304003500d51140050501403d40354492005c2c10303464009240020340d00380407242514600760108051075004880000400d240c03e0110001e68442c840c62100410503910541124200341c085e070040b04445d840f5040c1d120041d80d50304a02ca00c80301d02400d0007805546811010030860502084556944c03010000a5281c42e0503911040c40b40004c4003a01d582e103000d0404000c0020340903018800003070045070780100b200d00381b902c000400c9640044145109420703102a0f258991107440000801c1c80d420362000c11f03a9920a0040307171a8925500c0d1881e405a18102040b042210076030165060324000d5404011035520001c1078001f20714150390302c4052150880252460508202260b100c030f4041c0b0410718201000c4061240392030f00000c809001090b12030005225095051186a006000f05280e41c0e1101c4c002d801414404502801000b03011070385820342041e80203401c07000310201c4004404480c0da0325541c100750754840a851040c11400d0059000000324180304580e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 314884451 1250 314883201 314883203
    0x112020a0504051e1002030903010b090402031b010e03030406080411060301030803130f0f031e050301180203090304030209090304030b01090b0603070537091a09011b06020a090e070c 80
    0x60a490300f810401005680100e08000c1d10081d9042030a20076244c8070482402013000094009540780d4108108150940340081d49080c0030385034680400000d40e03000501c55009110400080000d0480000101d80f00d5028441641c1c15100000b00042c405512240042c899802349415400209840080102c544400e210240c0504018008034030800146c03030700e4031015407150380c1c80c00b170ba41490760712801c10910b010010307400b081010346140c1c1d584065452002c0000e019281c0586035605250784c005007100900c0c41e04204603400320004400d904200200c80c080c5030000c04400c110b180c04c1c035501e07a0341da210780404c48070100201300024106005008503209410028841800d56960840441e0141c00001c4021114001440d10440801a1014515000a0b02d6650f0004032800600c0540f02142d20740c048084c018212991004201c0d400c070170f81d03010000c01d20708280051407101c1c90400f07400c1c410f100940300c1440000c20302d24854108010310112420440d102c407441e92002c600707850b030700703880e0704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 314885701 1250 314884451 314884457
    0x60303030714030702160b030f092b02030d051503190201090608060f040501090209010311130e0603030c01060b0310060f080a0f0618050405190c060815060304030207050112020a 78
    0x20001a2a124540c055981310440340704945001408812203803800e0304640c08058501000401c0c4082041d03080c0c4900c0d0310120000003845016004d030f048c400300108590b80d8140e40c01c00d440c60300d0300c001c3c42882140d2861489610074017a41c14110381214260105010240c0700340714600c0552006005e883d0150440740e016110072012501d4040f0a846c0c0303600051101d680014010b0b80007105585a100f15130290401100c01a1900c11500c0054216100f40740c101d4180c075401d0219604a42d03980f40d140080e607418141a407816100d01020038550b00031444410307059401c003100400d04181c003201552007010305800d4600c040b680d0380740590b030030070b480310803100058030040001e010f0031341d035800040e4071107411040060380b0f035522005c1c1d80d80c031069050f5040100d52504180024000d0400c04180100f050141400c1c0391801a9100840d00c0454803501c0107011307240c00007810200c80f1108030076030020050100740e501c0c030f414640252070300e61900401d40820700000a48204078524400da681e0ba81e8203403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 314886951 1250 314885701 314885717
    0x6110616080a0e01020703020106140d0b01090b010201140127050c0d0e1905010504380405070e0f04020306070201051308090307050a0605040e0123010f0e030607050409050603030307 80
    0x1001101c007510020256003801d5180c00d040100c205091000300701a43c002d0340006604c07400c0080c109000610001d03228810b50041e109a00421055407006044544c154000104000c0d2800140d002d0b003c07400c964003480480c0780000030010510007150791300c098034184c0207891a4407001c0354001c81c0d4050301d0b03168130007000b401204041c008980c0940d242c2880007044502003619202e41c6a500d2a0100c400c03107269454109010030020751b00d0403003890703e01c0c201d044110340581c2a4041c0400d031840308140102500c6001003000e022041c0580d40180860440c000c2d43c0745481681d00700c0040c000da80c124001e00c9000d000844592040c842d0501494030105034804205441c2c45440b41030708540c60482d4140510320000030280d85240303501c0c5c02001140c440d191601e01c0c0240b45401d02134140d011140d20007200d5001c660b418a001d146000701107007420440d18601031400200c4411083d00701182c0c02d44594400d10150540140103442120300b0350409111594500d0145500d07400180c4615021030707161 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 314888201 1250 314886951 314886991
    0x60b07080301051c12020705010909020a022805070e0403082a0f0f04060e18010302030d03020f071205131d180f06010b0403060c030c0e130204030204050f01061106 72
    0xc504210300080c080200c1145003050340e02c4c5c030740c502c26941c80c107003003d0380c0541c008101c15600040d0803c02410060011810840e800702c0c0030751908900302e280300c1c0c0c0600020303150514101c8031529280d05604041250002c81d16243c651840c50000d450035004280a40000350426030481c1c0011000006400d52090788602c0f004240f165801000210f00290009c2c88000b440802c0d0001600c02046d09030b44000f95044108244102440825003a00d10304d0420130051000d6140022011490200c0c0d150050b130f10035104031222050b00510314000c1c0f40d10128a02607070015401300182080e02025403040510b07a03565555a09140b650b0740c5140e081c08481000100b06440726006101a11410015664400f010340500d50401c0703802d0f0400406504045014020b02886200e14070052036a800c003080510a140c0001d402103800a508500c100814070010038440c43da034060701e00444d406803042c8400e080c8041e4007540300c20240940400034200d88884007103d60005a100d005000d06120381c0048621 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 314889451 1250 314888201 314888209
    0xf0a201b0310090506040c120c0b0306060904090309091d1c090e0c03010303030516050d0902040204150e030c04090f030e010c08160c080706050a03050405011401030c09060b0708030105 81
    0x44a0196901d8010032000703560085460084000c1e182c0324202400081c030f0710b450640c44801c210741159074008040c0c030400000400d546400c50070351350402c2c081a143ea503030400044140c4030340b8601701c0d0000d0900030068109604000c10000b81c800d107030020301ca840d80140d2809038400010f1803070b00b01ca5008000d28083d0500314090050080c21501d00b040c115603c4d08600c0080d007030700b41c541000c1d4050002c0100241980b6208054100b0a01b00080c8414602a0402051402011130b4511345c26034600d1a4070840d511981120000c06003124444c2c04d00f0700840d009804d504c80c0110041c02801031032004000c500d442e01c10050502e60001c00b031511400241c608651200d03622021f14140960f008500c40400d524801411035410203a084180c0780300203142c110503006040d07000b22166807107040140480c1b40c210042c3e9542d40e000d07103000945079490b0304110f40503011039170101601031007030f5001100b4000090300340026118030180c14003105549480b20842d0348180980541688400d00c010700003858 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 314890701 1250 314889451 314889493
    0x70f12201b0a05030d0f0e03010b100e0307091a030705090f01061107091e140f13030201020906040602010e07140f1003091a0108010b030307020d06150b0f0a20 70
    0x40c02504030b0819075220f02c04039241541c40080100414003a10034420704a6100302d00d81c028220681c02480061041e1000c540b1440030100a8014030801e4042d404035070302d0400081005120341c0c0018041c3c50706160000015000c03230f46405e4024010b841010802d414075560f40340c040c0340004500ca200c0e82c03a1103c01c80d02f64100800702c0b01c0502840382c00140d0429240900200d2032501600d00d542030700c5c04c04a000845041d80018010381c01c44c4001c01c0840d041045100307034070286803109040c1a504528040b0300a1052000c02039100501203004144640e05501118002d4410812551201e454140140c2803c00b94503027039a0189000c020307103810b03040c15040c58003450b0381d03828003040c0c0b00c000d6035400008401c407031200c0500c9160000108540f000902417400804d100707034080d524007400740e000720740f0b41d003064140508a036444140c201c00503c51027604400030209440742c19251810944487c0155000e0a4944001010b1040c150300c1c02050101540d80760443c20010a050074217000c040d60402c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 314891951 1250 314890701 314890753
    0x1434050310030b1918050d180911030915160e040618090507050103020c03030408031e0a020403050114011503240e0f0702010908030a11070f1220 64
    0x205501c00000001e040207080e14003409803c0c0c452203120401580040403511150740f41c24055000c10003040100c1c4000c504400c04c90000d2601030006840348141a80b24540c0364400380003e0319000d40a500b804e01d4102640c0121311040c255094101000f0b10010b40c604241c0c0d86010554440080c10340c2e00d07002e5041081210300292002c1a0207a58510480351a24041d0380c007111140c40d0890030040200a21101e4050042401c0840c00e00f91a02c042596a000017000103113030140c00000300f404120a20304000107503c1607c0c4e4403115180440030440650014881103401d58205503248905941d54010241603d20011600308480344400f021400740c03000b41c0117030b64041d882c0d244110121034880c00403005003421248010391410040100c0c0040c131401490b000c216490600c00c800020000f00442c0c3e001600c900b0082a41c1000c554059041c0c840c3e00c1004201c5200168401d00b0000d11130844100111243c40303010071000a441c1046880c01011070381c81c0729800001c1021100ca011810181c000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 314893201 1250 314891951 314891971
    0x30417101b0f030f02040602030307020d020f0c0402030405010b090c0a110a0b1906081009110306010f03020915090f071b1511040b040303050c0601060309050709110d14340503 77
    0x4c49a01050442240c1c41078120800607040001003222a85e0100480005543c140c0700a00d4510402c1c03031a2030711003551418840c805c1c0d0b0000701160900c07100350401080123100074118aa142040e0818190580c00013110001190f021240d076503d002011480c002c109030041c150110596441d00000300400c0000b008003626661400040703031341e0313108100c8100e1044442900003022411420010000d899405601d0b12941c4644018421410b200211100b160f0341610300050580750700041c007070806200050329820149800412124001c208001406250b00d42c070b44c904c100303140100710200302000d01806098400f92400d25524070109a0000d01d40c150301c90455030910f1b4941240a00c254000d40c000c1e4001900400c0709050014140300d40b600400c2d40341010416403085665041e2180118030450228903070300c5503202280d5081104a03000c00420060810441100407101880d00c44291a203200c010715403041030701c0052801407213040c020b10112080c54580c408210894240d40010880428 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 314894451 1250 314893201 314893211
    0x6030403080406180b011e08030901051605060c0301031103030702090f072001020d0e03130308070222140a0b0306041106071209062a021011030417101b0f03 69
    0x4101113408042c9885182e901e402c951510003071049443c1c0c0000f99100382a6986010460404004100d82080341c003820120f44440040c000b200c031b4806000e034081c041e8014002008040e43c1d1120080d41628880c0d03551b06403002000c800d050752806488130094008007950301041030032760045202940030420b80b401c141c0803070071040240f094502c001c44400c1540e40103e005110841a4003800c1c1100194030000c1d81000868201c4401c4081103100140c00c440c000900c0c0015500d41c10b00301031091100110328501d108021003884010b02100d4540e90f505410311380496001d0803140603034540020024000c00c7e0549a076100c00924241c8401c003242e00c100100104400200c0c101008010740a03103032a41101e041c58460040c0820303482d1210a109a0b0004041c0320365200003081244c200c0d40c0541c0d8414211590307500c281e41c0340201220804003031102140010350b035449011301600c00d4802005482500d03040040171f5065640300c40e81916801c48480200b01d52030702c900c40180501d41e5920b0040380c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 314895701 1250 314894451 314894471
    0x904150b04080307050c10080f040303020d0903020f010b09011a18030a03050d0e0604020d080307090b16031d0901051507060504030915090b0a35010609090b06030403080406 76
    0xc41c0c0c0682c2c0000c0d00768102103020300602000b4007821b940f10342c050b18003a08851840c0c40080000c1b00003011480840b202c08040341c1494441e5064444105040400304540341c500e0502a680f4010105c2c918260760a00004c0c1340b003400d00d854141d04031900070b092100401c00b40751041c801078111f00710705038522101d1060160a03603000c101d4102d03000c1c060340340c0c1c81c0d40f42a00051031090f6803602c00c070050540d0040b400e010043e192030543c088140d420400c1a51240c68511040b00c105c507242e4480c198022000c5141d160001010b4120600d080c03098131070142e130311071003282d148420400802d0180d0000f90500100240e003040c0322981c29502c420746400c0c0c41d11105545503011a03009030750940002c0c240b080d080c850500500d000c05408403950038804003480c600410310302a4800c1c00349080c04c0040e0040a0b0142d100344030540012580340d070512030540102d600b1044001d14003445840c1c00035441c9000011200720030700c224102044040c010602e180c0d500d407002d90725400042d004480300ea9413644414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 314896951 1250 314895701 314895719
    0x40b0108011b0f030c1106040803100803040b0d020a110d020f070e1005150f13050a0803070c0303030e0705030102180a0609030348061d06360606040c14090415 70
    0x82d00c203500c9440043cac0c403400c200c00c4901e58031b05941c00c0303103c5507031082006004031203450054621452400c0400343c0c0e180301d100d000b21840c03070030b0494045951007006007020702241c010561700301d000ca00c03104440f02c0540d40c101c080e070840b41c117888000e0505034a52045c0703d41e0800815110140300700c20000742c58400f4844020740150300c920910040c808080800b031009192001340b00c00104850402582406030300d403281d03a4408594031004060541da04043c85550300c003400000000c000c01802192986002c82ca40c00706d25071311003520751042500500203e451030052500f5001d99403d99500e01e4501040a0b0803480040921404008100520203181c4101a09201c0c1000041e4828800f16080000c0c0707049030a603040710102100480c00c400d24410b0240380003c0d142d6104280c8044c3d09215a0301540b03503000d90302080490748038150402a06001c1c0d550000e049405007105640170001c0e40003c00040b200302c1700401800c290b440e000c1080744020700e860b801c98400b190721600c0c50a14141d941d0074070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 314898201 1250 314896951 314896963
    0x90d0516030c1a0301031a07030e010212060f0d0b0106120603080d0e0d05031303081815010609080106030b0109020714010c020c13050c030103031412040b0108011b0f030c11 76
    0x7210108028a0180448102c1c50000b05102e0407150f181415541141e41d0400000d5840c002940654020000039003842e109400404e254414a0021540e070030f40fa0384500300e054801c1b6034040c018022018201070b54103041c42540f06c500c0d000f4050110396400c00300c0c1201d03801104d00c0b070309142c5a201e1101101003030041d8000c040c544280300c80000c0011b210700c3d0182c1441c00040b08081400404d00800c142d5902d040d07240750313041d54140740008540d613480c1440c504001000d1340c030b01183e208070315406148003800da070000d0603110136403102c52140c0d075a01019820b0b0f0301a40001403c10009078010001c1070210740161806512402d990703186a07410842040c02c55072a0000380700141d00080c507240040c1005211001040800036091007a450801c80d101450b1006100080406c0000103c0580619256054031324150002400071610309150529110b00c1c00d0a02462050354a40715007042640d9441c80c203c24a11600e4031820f20311084000250700511190f51442c003405480024400c10600520035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 314899451 1250 314898201 314898203
    0x9010c0c031e0b06100905060904090f08070519200303190225030206031506040e010f060807050702150306040f0608010f0c0503100509060418120e0114090d051603 72
    0x2c14044545030030000c3e000c03000581410301400340080320408040d8440314035000c0d1001175801a680364400c3c8040f500a2040e808060014802c1002a0003000080c00081491034020b40499603440a07845142c400c3c0410b40304001c0409020030808912510002429000c09a0040503a420410a8a110b6280b116851000e0005030032040284c056821411001c011850104601c250200e0440d40403820034400035210002200701c07941e899240d60340750001c88016180d001e0762a01d4650751116130789048400c0b80200404074005100040e5404d100304191000950011300c481c01c2000d940f5060616544040c2425170011349070341c001c1c1e18641c02c40c0241c00c0104600c400008914800302d245100b218050f040c0d000c10404c007042408882c0c5602045142680c804031081c415a45034900054010424200344802010541c88520240460b0300e1405030300d1407241d21a441e05260fa034004680c0c0144000000c018000240004903040c1411424414030034410000c0f42c041c862030b0080e1801071004c80e80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 314900701 1250 314899451 314899493
    0x9120614070c060501060c02011205130203070306020a080f091e010f18020a08030c0d08070e040501120308010503010203070c23120a030c0201140106110a0b07050c2109010c0c03 78
    0x4002e010043d151044c0d0340101468600145140c4043c1d000800400201484811594540011034940042c06005c82e03480b0342e0083c2100d94042e0750f0314208019400c418800404602100c00280340400541c0310b0fa80306408403405003104254030888100b000d41c0070002101030b50358550b1481c0c0000c0380c6101e1010450301c61030541580f50103c0c810888002d010f90002049a0000c0c04211180e22000945219500a50600f45c0e85650f94120444058400384075546e480741c1003400015585100d52000001780b402a66221010303a2900706060a07803205807010f10001d000b9019071008911a0000350032011440307000e00d0940c15542564a1500700c500d00d14050080b400980070403420780502c03038050f04d5403040c0020b021a0300c881c600e244c459034051103124144a010071046440e50320a01c510b9007219404000305002c0d0401900c0113105811a0400d0481c500c607401c0c0030540501c8940c0f605000b1200303420304902c2c1464400045400014032a000c90b440484c005003c000111986408004041858 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 314901951 1250 314900701 314900717
    0x2a030b0a08010b0a09020a090e090307020d080a030f0b060a0c020f030a0c06081302030c0f1201060e16080c03010302040914010c1806031506031a030303100509090d0912061407 77
    0x42c04202d64500c0030b505c0200e01c0b51041084c03040c0c50350000c5172003040f40c0040c805082c182c0e403042c00080c11881a010001d60101d100c03060348040107900d5010b49140b200c13a40d02081010300075044982101c410703501682c2e10401c144118031110384035041041a40307201520f511000072081d4003081c64014000001c4440c1c21400b4000c0c02240c0d0301c0301e4990360044044440d1021070358103401180c1c40364840c003412402642c80311009034403a2a10461050380081b200000c0180e00da86011448400d9000e0f200c01e4041c03c0d0130700310a802030f4400c80350f0030f00031208a0f40031499a440c40e82013100a1031614022960f960301a80d01b200c003c0c00a2184280f00c8403075442d601c503d0081c10300b01c6c1503c0da0017034000b442403629116008a14040750590301c1c0589245080000300e0f25826242e1011003c214071002d03030705210001c00c000650450604980c00c446003540c1c808103a442d109802a240c4111050010024845003c100507854000031408140e500078000003503501000d2001004022085a1b52030115850b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 314903201 1250 314901951 314901971
    0x31b0302031510061b080a0206010501020606060a080a0221070302340201030c03020c1f0f0507050313061824020f0703050c01110c0d030b042a030b0a0801 68
    0x280280050410342031403181d8070b4904015400d041c4941801001304108000d5080160085880c00d1031a02540180610792101700b4400025a01c4000340602c600600544020490707030f0a00d942034074141400d07521018419556401203100940261304000459031840446188214041511a004a0907641d0150380c40d15900310780d10b410180f021120102d10626a44241e642d0024511207008070760910303010130f072400700683c114041c1c0250b1000314000c3c082c101b4000503201e40c4c0c41141075014207002040c49098140b54607002181e00813950381002c13550400011384117071403201d43c4200d054030034100000c0c0040c042c0840c924003044054120707455840d00101e0748861941c03044428210681c644107610b0000e2801001c1424094240018180700c2c01040380040c40302c0a400c41046180714180898503942e00c0d101981d942c200384140d110100745001c10b005101e060034064807100c002244408244c400c0c102550301c9050745549624410190340380741500311a610312024100501070000041221401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 314904451 1250 314903201 314903203
    0x19050d05030a0914090c07170a030c02010b100c120c20040b0a060509040e0f060403020105180601030f08030a0b041a03070503071d0c07060e010213210813031b030203 73
    0x2030303500031807803008130344503c24415170754840d480d54000b01074554561100014170786080c0d000030068160303c1088010450f180919810703440f0020500e560b500070b001004800c81400606400d400d010800030b14024107017000f00b105054210a4003200b031401880916440c1c545049083c2482c0c0c6884901a04241c007103494035203800349180c0d25500f16032175500c01d490f00030050b250340b140150482c0240c0c0c554012007850700061002c401031142c05810b0310711031718242c030300203000703080071600c4030940380fa0200b42c14481440018802d042e254018500d0326205403988421500781c01c01030031040c23015100c410520180c3c8560103094030300608500d00e00000c441c0c2204140c11304603141c001d03500035440014100882030b0000d0380208030742a0720300e0200c2c55403210002e5040318030500030007a10403400e0030303290304072500158028200306c80144000d5080caa119142e0001160f0040500f03a881da040d60840c0b004200d07048014141c400c8414901c181595036980c0780300c0181d04036404c200404d2643d040400c2503080c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 314905701 1250 314904451 314904467
    0x7030c0c1e05040c17060a08030f031b4602060906090c010e0d020402120f010e130b04060b0f150309060c04031e050114040605160203130519050d05030a 67
    0x40b04440910003103260280c001c02138020a0a417041e108800d00100b1060f488812000b000b904103a800d0781c0e40c0c3c00d0400c02c2c0c03801950083d0350800c3e4404890092040390341f5507800b920001c03401c1c0d401002898110b550500b02400e03800501c4a003048031210015040700c0151130b1164045955006030906291000e121420071000804000302c90700580801c09c1e447e0b90141010442800c120350300d40071070450f03002040c02801030344102c411038070080d400d1040e50715014051074102c4004101885882c4d0321034001c03004a80c04080c3c01000552040080b03000580716410034903082030041c1c183c868881c1d5140c002022590002c0004a40580c004103004440c0414005240d2040080020b01c0c03030700313107590355015828031851b025200c800008000d07a4100803084d000500d1001c0c9414121281d810705080c0304005040c15149007100c04001440402d68600106c207607030781c400e40c2000c0180954507090030300500d4490b494000103000360304400070035255981c1107800030032401680215219011214050200341d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 314906951 1250 314905701 314905709
    0x80718030b0a05071d0d1a090a060b2407111e130b01090612060801020a0509130b130c0903051e061503101113090b0102011401030c060507030c0c1e 65
    0x540400301c10589107821151720b5040000d0b80e0300101103459043c01003402c0320a00c03000180807011010b0012090000a1031a102402010104a0718011400f04586182c101c055034020100000c00c200318414007202918902d4065602145500c608a00103031811a44090b0040440d5100709412610308200b004c0c24015204890100301c200d4916001038a000201d01c15401002910b1a800c03040041c190412402000440000e45d150184ea03c030140250b00884800c1e40284040fa0150150500031f00502030315003070181202c1c0c034400c103501600010f0008a07050005112442900000092082294440001030101c181520280011400303040000181102c1d401c2c0b00742c0140a0025500854176000d10040b06000080ca425262154025401400000c0c64030b900c580a00140f0507402d5044009480d03c246e00030040d0880740080720844850a00029003240300410051008038060703002040c0f014060300f000030307070000b42d0f41e564440b003042c6402074900641c040202c4c118101603012040060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 314908201 1250 314906951 314906957
    0x100c09180513060914010c0c0b0c120403030c020f070e06090705120a0903110d110706030603030203090f060405060301120c061b170c01090803180c01090303080718030b0a0507 77
    0x54140b1001d800244400740034094101d668640046041040000c00c1030b070b0080700640240300c1e400c0c03c040c0103819501407403001e8940500c02000917810111800845450111000c04481d039521551012001407800303440d00070541c400d0000f2030401c800108007020040c641240c000c2d82c0d40c81c24000340303e0705042c0a0803200501009103d82000030a6070800c0c9548855000c0700010900c089040859034401c20901401c070502a0f0000284080d03440f07143d854407070074002c0c202d5800c1507580c0421401c4401c00c0c4800b500603001032044040074031300ba50941c0800b100c028001800d19417241e000524540c801c2e03112000201d1070b100000e08008125100c1d0006101301d06007441c2d103090400d042c000d480800d03500280854000303081e8045404140082d5010030080701d000b000181070070318101d085d940c0309440305004400300d00346e1101c000c400000c0c60085108180e403a0210b180c6555411b540340c2801030320200506c010110b104103050345204880f0025805008c100c450390900c0030420702203401c007030500700030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 314909451 1250 314908201 314908211
    0x15040b1e0f030c0c0c0d0f0204060e103311100903090e041a09030a080108030a052515050a15140609030c120105010f0b040e0117100c0918 61
    0x4480881d1041c0c070b80c000000700340c0c0d50341c03120f02d003000307900f0f0034030500f4040e51107240005410203203c101500701c1601e610940781080200d0320381402202c0c1c010f0450b150109064030400c01d00c00760701c3c042010800c8a010000d041615103044810703110200c0c0c00c901c001d0000b0408007400382c850340104546410320085c1c02041001100c2524020035215040c0102c07001151800046801c00508103c400303d80b40404603080c0890410440f40758484d4041038540001807002000815404030100c11200140456264a0715003d015070141010305031003840094040c1c016400310000c07800c145005034200c0c4229500103401c0c41c0a9880d081220b051134003c2e8503042b1420414016040540d1903e0909001101c00c1038840311500c00180c0b0b000d55108003150004040808144200415000681a62030300f200c8440b50079111044d10340305004a119200b281111600100410021840c141403084500c40139940c03030b10005035104003541d4000d10213800142c80704204118240e151404412403192150741840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 314910701 1250 314909451 314909467
    0x708100b030c0a0e0301060608160915030b03070312080a0f0b010903030e04151404110a02061b07080a020c0907111213030b0f04051204051c0215040b1e 67
    0x240d408020001100c0800009004544030b01a90072000c0b12800140248800c035202d00005040942c01d480884c04122044a40075046024140f40300643e28140c0e580115040100070440242000c50000c54041c065041d000c0080b414010b6011040101c0380c44042d1a8200403061030300b11490f03000410521807503c0e01000c4560fa00007171400480b909460024003004442002038020f1003815100090015000e0001640000b540743c1d001e000344c0102c0b0200104200d42a007000103209070520000160040c100042540d19409009109110340440c0e2908162003581ca03205554012203890025034451420264a86045100690b20190610700029404900d13501c040c3d40740ea260350340c11984032000c43c0042c400a001100180150b411118a0034182051015484d10044c02d0320709071402e001d4840d0020301e034a40c030012030301100c40161035401c001c2003040c005c0103000c04c5884101d0b0702050645403040d8480210001d04054044505200d940f168800c004981c0810300e05500c080130718003801409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 314911951 1250 314910701 314910719
    0x150903020a060c0306080f0c030105010b04030c090f020702120102220b070602030a15060f030b010516020609040b0406090e0601050306040305040e090c0604030b04110d0b010b07080c15070810 84
    0x88869a0700c0280481c0003c4215000d80203801203400080862145c09004003000100007655298084150002c0042e644c03501d180820f10b200700e000c007502ca610a0042003041840303030344c800854010006030043c240aa41c2d400a004c5041c181411051a9000302c0c600c406c0b0b120400258030f0541c10b040082c02694035004002c400c80c05081405001141c2c0400024884490b64001403104d420700c0c851103c8107038854101810009445100c2c400003460300852a486500510494078018902c078a102c04d01c14282c2e00300400c40d4459070909800035111103c140d8652203d0240c80090702a00308045142881c0222803460188141d1005c0c0c4070b540f2610501000c241c03c0001c541c1a500075503514001c607554070840038546842e04036002d0700020b0018001081c02140385445016038420b14417003240c40000c0d0f042041040122801900c2c41f027154004001041d8888002d00c07000307210f01c0b18542070509030003a0f075040101d203417450300e40c04887c82d0401142d00e500540c0b07161310940819410b100141811401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 314913201 1250 314911951 314911963
    0x50c0906070302030408010f0b0918060a18140f1006030807020607051e01020a020c030a0c090929060a08010209010f0503100f0308030405190308070509120615040e1911060c030f0715090302 83
    0x20901c240d63b6000c000b0201300640741002515a08844851100603043e012150b45e4814036181a00500480104445c10304007402040e040303d0308900094184042602041320030743c002035046415104804d464140f25420b2403200c00c500703901c10001a00e580501030084e081c6a80b452145109030010440107000070500a4440c05840350700100042040851400d208031040090113480b0400348000308011400b030a4014078810349054a404002c9035943d64400e00740d0140541d501d0200e0480040744070180d102d8805581c0c000d0082c444584050b80d10001218076007145c3d00b041e43c2e8860f0000402080c1300c020005002c3c01d040c8851785000180340c513140107098003c0074041c441003120000d24005c06684600700b90b606001c0b6403007941c15504000c4115101070590001c1c0c1401036040c65181c0782d2845010076048001c4030403030580d080340c100641d92010904c0201e4074841c0d0049050140402d101810405445603801d090341d400e603581400d0522034481400b03002c0c120302e001c3c240259440002d80c04509 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 314914451 1250 314913201 314913211
    0xf0801031203110711030705060909040b101e09060b04030b0f04020121050f061207060e0301023105060901050f090d060507090e0a050c0906070302030408010f0b091806 74
    0x809400107590304200c0c003412020f0080100721402243c00014400c542d0790429007440200c0880b900c3e6696402401103a0042e2000300e40e102d25014002000b081c0d6001a941d80014540c8075100140e44901030340c960680c074180c00c440c04204012090140c24252f00c80c40c2d02900c0080d00003820946540e43c1c840740000018041140c00702020003040840e4000e40210703110020107061404500782008548000305000c50f060b1b030f030005065000c5181410b010610582040c02c02003d00785840c14010140d66001d031120b0302640640d07081019540d4600d02e4191108900400d25407408440225556003403183c1080d08610300c070745010410850141c4c1c00408550042e50f080409a80b100744020000e06040740c7d40f540070b4401c40c14102040b5034282e2180c100019600301d6035807d2000d445042020044941c00c60b41c045c1c1100b402c000a41c1c452071f003035014201c1e9520030f00c112450191540e82e110700b503d0031500710040c5103480c1c12015000341303001003400354010840301c24001001505da11495841001030a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 314915701 1250 314914451 314914463
    0x60702060703020a0819020c09040201050a0e130c08060108090f07030308180a060e01140105031e07080706030b0f040c0207060806060403061d0c030a080405060d14090c040b010f080103 81
    0x590780c0c00c1500a01900d100b940c0c0007085180c944010880f05010410013280880042c016501c16074110300c6d0240d6000d001c4c58060f51210704142c0151810b030350004158aa00340c1c40031000c0041c207030204441c041e29541c1c0580751790307546c2c2900301240058600400034281e199150082c110400d89100002000805c5a030140340c079040da03440311501c018440c100e1150008070b5000c0e034034a00701404555044416001c038079900030021030300940c142c0c0c55106828000c0d0381d4160840c0c0108502c2c11042000000281e80030f8007602c58441d6603503100d030301d0902c0c01c1e070060b404280c8030b038041029880c007000e80110209083d60706000400307210360003d407601c41900459091002110104070350340c60b01c0050b20040c50740701070f0800290b0a08514410b5200b0483c115800620450308000060304010807600c82c0c0c0f60303000c040c0c14103181c02c0004204294020036009980c071035072112007802d841420290345005070803070030182004022034014001175514034a945c40c14458040094002140e01004050440c1d811031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 314916951 1250 314915701 314915707
    0xa02011812060b0d050a0516060c08030604051815090d050f120702100603240c020a0803060d0c0308090a0e01060909090602070b0f1501090b120403021f09030e030c06070206 76
    0x407000584c10001002c001d883c1c0d116071350403081080030000f40003c034072244002002c05513980ea101116000c86128000344038880a00100320203050540107250030a040503e81910b007521144100d207403614580c486c0f21130028800510401c000103001070000c5074580d2905514210404c42e00c00d42c2c0c2d116010a10813410039000025640324428011008001c000c00000c1c003e42c6d80c0e90800000e842d0030903e002400103c4031280b0032070038116104041162840c0c0c3c0240801760b00c9901c41548903040105059048500d6003a4500010b945142000155103d22122a21404400148100c0c5c82e030940010b80414207100c0103014680e0010b40200407540560b8000c41c0c40b015070310381100a4044d801d4001d044d24049400d02410b6852120128403810861000351505000d000044550400a100f84012040c04221280e210a40d01401a038000d0190040f2a24005010050841445654595522036517103089100c00c1640c007107080140c040c0110002c1000700c4002c1d0004040f13109000d00240300d00000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 314918201 1250 314916951 314916971
    0x10b09010e010f142d04080c0d0f06060e1e060901140d0510021b030a0f03050606160b0603161412280b09031c0b0d140a0201181206 58
    0x3981030813000585100020751034031a2002080c09080d1400640c9413440c41021181d1100030030002624100c50000740100402c000e0b142c2884820514000140c1d43c0524510f45440844c46500490b0000d00900d0710048203450420b00306281d4145207501d18145009880070f101a075076664002605440070003a00c4420a8038440004d0b0303e10200100080050180510742c80046140758083c025038200850004c01e0707444d00340035964580c40780b22000c40104d01001043e2100d03900c654402c0d540503402074801407900071000001428078110090403100012914100059820b040c0415140144208801c9100d5420924400180485100350742d0040528900404c00100100040b0010f003000703180070351401418074000c2c4d210000c00c079020f40303c0d40761000126540000000441307038074140315111419042003d01640001c1d0420002c0e40380e004180090a0f404283c0220840180513008402001d02c80440d2001604000f00c6c031910301d01c0c40303403d8541001140c80c21040003504d1580311100062080030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 314919451 1250 314918201 314918207
    0x12070f06020606060307050c030c011a045f1506031b070201030f05090106230a05271302030d0e0d0f05070f061706010f080f092b090504020901020c010503060d020405040f0b010b09010e010f 83
    0x800031070300945e134a07031298ed543c04c09040d040e1540071b86e0380001540300541000302480754908c030507a207903003141a813507140945882000010f0b051913841454007294424561006038140c4000f0f4640a243c1e0b503540304100b2005804c5c1d40000014424640c6000b603000316100014090070707903441814069030041920040c50030040c4020000c0c01c5040403003100074140a46026413844240c0b008078003d100b441d041c41c010300e01603110100200c80045c221001960700c0d03130322100360394a0460b08480900c1003540120312100d00041481c043e024994401d06145003c00c0c40401410700500410306000508000100040e800f00c170710391b07110031a400100e00d1f60300d0b014101c03031800c16440702c401640780f0260700300e003104a504580b508045400b07a5070000f030b02d034a40d01003200701e01c500f04203e40564440460000c6c25409030b070145070301a00c0104581041103a42c0c0101307058400448048074800c2c81901c00340100b0040c1c1036941d014080d0f1042003820005100e0001e846800c03600e11840c11b1001105044128900c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 314920701 1250 314919451 314919581
    0xc021510080609060414060f040323030916050607112404090b03010c090506030633190302070201140f0912070f06020606060307050c030c011a04 64
    0x2140c01e0441d01549007074040d0725220342e4256400c0341c800440c560b140041001c0001c2c542c0c001c1c0c98840d54510740c1d407100da40c1919401580c12200350f0600c0d1200f40f18841185c2000510303c81d061a6018010400d0580c02e02c000c200e0840c1c220340d201d014180280008a032410705402004442a1150000d030302c0304545892100d090003500c1c0d845098001004118844182c0043c400158180e000348481e111803a81a1007003038060141036007140d810700015020b85003011141408842520111130581022182050488450702415050140008604030641310b1040580d0807020f851904505001051340001e0109201c641000c41008012480c4410100000c00700d80540c00000c10310031844401410302a128225032180c0b05507915110400543c250000c198644183c80c0141102e24683e12040266080c1d0080320103d40188000d1002400000b024481c0c0403490300795128030480e104074182080113681d5814150b41c1c80c420510320500320039488040c41e00d8844250416442441c96010224900403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 314921951 1250 314920701 314920709
    0x110a122001022b090e16030f0e1603031e02070b090f0d150b0307270b0a060c0501050a02070519031206091b0c0203060a110706020c0f0708010c021510 66
    0x180c0f071122070744075105822954040e00c03102a1900200540e41e204058031604080341c00071303446154401e014a10700d120368030120362190800000261710705c040382554900a1903050010028041540a0082c1600f082c502c00c030207410740d009103100c0789610f031000751240f21034801c07104a0000410884002d5580115a502c002009072030300000c0742040c01c04184c406200628651658507010030181c0302c1c00c3c00b1910034156071031150f407ca9031180c00306000030b140304c0201010460702d50b101d209d80b0301036a415501400a124554422940d80d8403410b04908407800540841c000350f104000540005102044001c01c2080d41c00c0f118004000d141400d50b540c2d030b14550148559460404080f07210b52a0394020395420095006210b00550a84015a4050071480e4041c1d410383c0308000040708001207130022034100f00148003003820000c10759140340680c0c01c54003512480350080d0301c19010b807640400c290f400403c00c2c00001c3c09411490344d0060b48030700170142e0103204c00718034000048180d0117881e8040003c3c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 314923201 1250 314921951 314921983
    0x206011409071e170903090f0303040605090f0402040902030f25090312120f02071403210a180602070201020c0a0b0316090819021005040e070302160f110a12200102 72
    0x1515050540940340c7d4450041284601c04001581000341000010355042c0d5040d078840c5480c0170b80003030402c002c04201c1c482c101c0e030080e020000801e842445002950103900750104000365070503d00c030000760401001c04e800101c0d0103941340d46843c0719032001e04042143e0304490a030070b245110a1045613064107042401d0380c01800c00c50341c0c0c032506062740e0041c898640647d00d100004029a40501e40324401c48000c400c2c02001d0959218a440310b01c007049070090455600040d0060344460221420203000d003041e214258041754140a6507014010103a80b8482225840621428500c001c43c0c98000506101d007988423405070b1540c2c0c030b03004000007409032441c14121070b50340c805d0210441d10400310035002c0f030107444580c2225040b5030040041d1016112040440703641c40c0d40d01d0324101d009401094038101d0307241010038520041b86010004e040214000e40d50b8165030072545040c00040542503000341e1032020101c02c42c03c0840c03902d141030714646444a000c446501ca210300101d145c88007841612040c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 314924451 1250 314923201 314923247
    0x405010302031312050c0708160b1c060303050702120a0203150621100b06070f1b0302090a14090c0a031b03080d020309010513020d1704150206011409071e 68
    0x40c0c135410001800034203041c038084402c040e803200c5130380f40c940f070b0038005240d0760642c854000c1c02240f424901400d82030b2400007000d840c87c4060600700041e5003243c0d0007900811000070714102941132854501c40004003040040080701a5540401e50b2107004800300300392903a9078400f081c025a940d00300e000c08a60701c203102249203040c1d03203100c0361515078082003190b12500d4600740d20304600344a001e5030301c110740080121606407443d45600381561610308000c1018000b4400c0840160303980400309014040d400000111500103412804020101410221459011504c1e42010740d0710b80d283c081c2074a5024850148500310254101390001080e08001c00b000d07400301c0d4800d80000141e0240d4407403a42c1e10000d200742d4803140547c5030124200140650050100201040407072000745410140006101d017940ca85661180c00d0600c480c0c0000395000142c00c1400108026602030303031440c00204003201d0040c0720341000c94000d4004004030410007030a80112503610001c0c0c1c0100602200c030b00501d85002c41e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 314925701 1250 314924451 314924483
    0x30906040611010b03060903030a0c050f0301120308150d0f02060909040305180609130c0c060f0905071d0414010b030a0f1209080c19090615140f04050103020313 71
    0x85401202d452080140d03180c01082c2032180b80c0052520300a0059202441c50b5440d4440303201d018000c1d15005005015003000024803078001d00c4005e5000b0701d00e43c10301c00c503c0185494020821031016000b50200d01001506803100d43e101029880c0d841c0d07100c109610908114800700c3c80d00d0080c00841540042540304000526400c40000c00a050400840c02c10801d005000c0007000c3c090650101d4002c900e01803202c808012aa002e0000849a420845034110fa251340d403006039118003801c0c0c0c0000d5100c411040401a0030801d5001402e8002821400c83c50341c80c9800040d00c2c00240050f100000070794400242100030351003a0030303000e00030b400d0368000d0225090070b201800e240c2400320744030580c0c000144031040c4a040300c0e40a4035800809400c0201e1190b00300b0520706c12a000e9105c20459082c00061400e47c1d620403074006110007210090391580901d400380100c0c030869510810b0701340030045c1300648400a002c48060398024240141c99441d0000c4d03c3d0481d054044000389454407281f0310301 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 314926951 1250 314925701 314925707
    0xc1309080307110d0f0e04050a0b030d02072102030a170d0501080109120e2d030102120a0b0d050705010c03051603020c03060a0608060c0d1e0e0d0f02060f090309060406 74
    0x103200c0f00c1c603100c00c50b244001c3c4500212159240d80390300d0070014003885240c10052900e038010360b4000c0d001d13500c00f20358160401d000a04107220040071001507841140c0400c900124011084001c904400340c80702c041050fa00400e0700c908200c68000c107009180e4080d04804010402510f00389440148200070301e42c2c444800c2c60007030404010a0f40e071010301c01135100131644100a0844151009041c0018051612460a6106a03000b0440681d925030601103c4030b0f4409202034601803602c20074850310b030309021005000711513450011341d002d45d104400d11b101183d000a0407008603013081c41c0a9220880c5414101d5081c007404400d64409071407d64000145079000541d03d40100044041d05c81d0380d10340301da98404807000c611030029242c00c0640015001c400d400d015100741c000440002c03808515005e9618181c068180d0207420041c0e40d03008070001841c08110350329400300141881c4107440c3d09a480070395200381c002c0048c42c120003c2c1c0c001592020003071007503c8200e107010300804c0d221034482c4005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 314928057 1106 314926951 314926967
    0x1e090613020f070c0602030a05030c280c0209010608191d0d02061504270312020d0618090804061d0a0b030f0a0605030c1309080307 58
    0x202008040380024404140c0b01e09905a44010034a00b846192a50f0b030407040c21035100744656521039400c003085039040802c0c14941c6860f06000364a000ca911003412960407642c244071200e21415402103480031446208071800384e02c580c2c03148002c44a04200b1600e031017809400c28030600644919521903840f502d508030007400042003c891042c030f800c2814000500680c050820418500c40181c525a55480111418040001144642a12081d80d45000c19103d0107075001d10080600608414030741c41d146000c00d5440c6e500c03200d04a0003d000c80e216103040b4203011081030326501c50380d100d0144c440b584025410304150a06404070341c040c11a80d101c0740d981c9202401600710343c0c3c032080400020b00451212503a03d1516080020100c0c0000e00480442401c25400340301c00e41d4045180200100151480311070300721800200c1c07000e0000c034040500003006c00806d010ba60ba52002107 = true := by decide +kernel

theorem cover : BRFrame.Cov 314748201 314928057 := by
  have h0 := BRFrame.cov_init 314748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314748201 ≤ n) (h2 : n < 314928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
