-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1642
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:01:10.002467+00:00
-- url     : https://prove2.me/submissions/37276fe8-52c2-4947-af3c-a525ae371106

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 295143884 ≤ n < 295323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 295145134 1250 295143884 295143887
    0x1101090b270f1c06060506030a0e0f030c0307031b0501020c060108163819030f0203090a08030405030f0310060e090402011b0602070605010626090c01030207110d080a 73
    0x214048030160003080c0c000c1c40c2e08120b558032030f05200400100001ca9041907914500703034005002903009968407030008410310512110f26400020060a1031040ba1001c0c52034501441c0c1c9c901a1807903034006075000304510000030744100d48206203180c100c1c50030800b440301a0303280c9007641c000108807405548444010440301400304000b40c4116011f5a1525416081c0030002110003c41c803c888040300c1d01520203107013613103408040e54410b1120090b16450f40200c1c0c03c0c400740380c030640c0c00000009041c00d1010140f00000d2003101e00404107800188013800781c903510030020703410092050311140414000364042240441c011032180c80701c20013000109040c1480904200c000b80280b90007495580c04000060341c1010700d808500c41d400c84040403c03252840e00c10042e116108000b480c1c941080000110545c1102c2c81e0010206400884143c1000020110748a0780741180d07102016481404e5a00c03195001e58010404240160900701c2940c80300d5002c03c40350301007580d04650303a0030001141109076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 295146384 1250 295145134 295145197
    0x7030605150108180d05030601020307020d0605101a0703030e0a05100c08010e070e09100306020408010c110a0f020d33390c02031203091504020306041101090b 70
    0x1384491613000d441c03401c03039615942e2400305030b44d08002d010000001c10110b038000c200307841d00254020201c042901c0a481d01c40d014100a541ca140a201140004110001903076928003c000c2c0f203180103414020b031500c04402a01c0036501c582403500402c03400b14003042e0306002c032404800e2050f0f400f213501a11407000800000d41603100307200607010703c8107100c0c060ba404540592002c01c21a0751180075102d2000310010901a580020061440020001403004040d004040451b83c203032540a40c054445a09039200c45556100400020071200b92070300514025400341107071030003201c17481c110150740f009161a801160b010041c4114050500d81e494103141d018600c0208884040d070440d1040e09450081034105100e240105600424400c022035445084104031080d0003e08031103460302408840001e035401528143c8080c016468110511040c00c0f000e2402168042c00800180e40c541e00c40248040f00d0105040c1003040e24000040d00c10000c0010380105040740c0c0508008101c0703140101d402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 295147634 1250 295146384 295146391
    0x1030201090b07020f100e0a031407080312240907050c01050c09150f0c12070606080d080a0b0a23130506060307050711100509030d0314060f0307030605150108 70
    0x7103650030040c0c0f00c0140c490000082000c40c098492800b0380d190a5001d46180113210030560304942d0701c1c0340000a016081542400044204003603034141501c404400d500e80c41402d600c0700084020001080000c0000d1000103881205e074129040b25104003070000c0e504540c02ea90450004002180c880c801410a12902c1c0c0c1100680c11694a40f2105801140d10f484441c19540503008020800315020306e951422030303400740b02d42029501400110400000281c010403400d846807840d1403070225000400103900d80c4031500c20340b41c1c492280c0e240000f031400340c20000c0a02d5001030003402c00203502890310f00d0900c202110300d100300303081c00c80c64820700041c01c1c0d0305c207000888141003400780480c03525a002141d801c0203c600e000d540d5440c150500141000001d903038190446a40f003031000c6182e83c014040c10840e0307801c600703450101c4c40c094403c40954000080b803051076498040411414540174100426184015094421090341d83d00c5e400d080304c1c41220f554904070700e41404649070751380c0038507519070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 295148884 1250 295147634 295147649
    0x403020a1d071e0c03030b030601080715030606090b0a0315080607110c0f04050402010203191709150a02160b040602070224070803060a080f0a15180210090b120103020109 75
    0x8101802400f2054140d40200c5010030300200b2a2001e05051280c0c00c0211000006402c960709942d450728403640e038580314030640c943d020f82034102d00c5c0c0c070622174001d0308212040c3da81d130401d2481c104a84c003c030641c004101001419502d50680400070a50b0700d8006c01014003801602c4540380101c3d0140264407000038a40c0c0c0f03900504140031041d40c80c1014910060019507002601d9a510300c0140c1c9944251070b01000841810a0a020480da000907030042e07081010b241c0040c2e80e22100c041603038407001803100540c5000d251000134501209030340a0151948119107001d98048c080e00c0b604e00c1560113903029076110b60000707104010350070302e11002c500300076204040046400d90006441344c0d501038910300400040c4d000001c00c2c07090341c5844d41d210203040890140c071100540005203075a5031142c00c8085541402c90f48800c030800719030384a07003070207841d661134044d9003002d0385c1d800c021100b00d0110f0050284052450040f4080c5600c001805081c82d405251419039411800090301c80440342d401f215 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 295150134 1250 295148884 295148897
    0x40302010b030105090c090c0901030905070b032d06010c151e060605040b0d2a12050a050105010e01050c011d031803010b060f0306010e1201060504180305120a020403020a1d07 77
    0xa20f503100c22980c0d9178407a023840145500e51920714012809480e01040c00391062103480000320300d49491100a40c003c81d5802012407c1c59601007801002d04146480d100048444200240341940100c0000312002e11440e04404100188081c940c120740c00f2040340c4584445130058840415902e124107005883c03503042c200e0078149803038000300440c4030b0900a801d040d43c903580744031454441d4a002e2816048244401601c0400c0c0036802841c1140c00445004501e0030319000c2141400c4521a15042c0d82c010380da410500e04420700150b40e65400310062021940d6155100098882480d41c2843e5103003075a40038640c0c0d40408440745840080c01c5280ca440b9900d881109a2190b0700d05003220889a480d1000703688981d15030f030041e240c402c00d201806401108940b0b8400542c541980850b041d18002c541c100903c5016001003000003c0140d00240407c6080120324115a1001d0a40d94007400300c84026140c15140d42c00b1502c1140303503070700142c40400e00880701802c3c00001c02c0310542c0a0385602d01034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 295151384 1250 295150134 295150153
    0xb01020f010212160c080a0c1511040b1c0e0a330b040f090b01051320070c0803070516060302030709030b1024020f1c08060d0b040302010b03010509 65
    0xc400002002d0030710300030381c1403161010805038095880b544000307400540c680d8442c20030346009003442c8d015020490300100920808031500700907120307100500500f15401802c06003070003036501c07a07588210102d24014244854200c8015124000c820300904002d0140c0a0550741c0d140c50300d5641c0d0384081c00c080e08492104040e0b00b000c2c200c603014009401c000c4012070000025000308000301003000e00f41c1c2d80d09080001e21024095100b030717a9412500292000e10032186000e086800315034007000d4045000c0500c00322103401c60200005014900e01902089900d250ba8110a900d5544002d00448068202000c01e0000040c01c210000c024030b1075050546c0b55107040c9134010038040e16808000c000411060208400c1401100c1842c0580120340d1400305400d03550074000540c4c2c402d03020304001032060007030b5184004000729103140d8800c81445000b0200101c0b070401d8682c080010a06900000c0311004603002ca400c105115000314080d030000508107000c075050609603200203150400c160b0000d07500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 295152634 1250 295151384 295151407
    0xf01140403141b01021b2a0d020f0a0312030605010e09040f03090504020c0106080c0609060334080702010b060c10020d060306090c0e0a06050904080306010c12030b01020f0102 77
    0x30180c1100303211588560f01c007802e0a01021074020055100019031003c1548076162001c0320400300c0101c90a021241285002d805c4481d40d04012400d0b440840302c45032440069040007610240c089200420080c0585181804180c054078141d01c00c1d40c02403034941d0800300311609072181c000600402c1c0703020380702400200003044541002800007410801c81c00c2e440c105251040c5402e002400d03004205664460b4011200c5010340518040c100c158003c070f4843ca0910f140c09003c6070118000502010300350790b1150700d03481c0e0031100364240c2440070100d64611071003504a096803240c9100c8a44600d0000d003403005000f802c44180e080c1c40b90080d2420000d001140740002244101004044070141c0c3e24440c040c05000031742200d0340f004007010300302486402001420a4100f003a40e58004240700b0544d240484081602c20900c22950840220800300d004610204025640110181442c014044c010b5503103d030650202210500040c0c0d60f0102003003a981d050000c960140803400080d410003402000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 295153884 1250 295152634 295152647
    0x304030b010513090b0705040602010501081507111002040902070b0709030201140703030605030706023007060c0c020901080309041416080415020a0f08070201090302071404020403060e0f01140403 86
    0x18043c0708049400030030b608440c00350400c98074654441c1d05001c05040114001d011a082401a0009542841c00201d1002d034001154131815801100350301950b255494203440d0b115118000301d619000c0d4034072148040000b400240001c204803c801a542c941906203401001005030006040020100e01080980c0c0d105518404440000040550700c2c0050b20b0140d000b4585070b4003280d090b008a83c40041c071242c000c1600800d030b403000c038414410142e55164001e5903500e0b43c5c040b0101c0444c00c3c0079000228106070f01040c0c1c1940a4101140410602e8000800d007035001d03885845541d00000d501347c07c0d030410780610745151260a247c031419080902280c81d003c1c09030683c0f00100310515000406000e050310301c003400000581000c40d900d05803aa00102103507601402140424010b0011450962052040c48800c540542c00ba000300c5040c00b540003070404a4030b8600c5d40c415021310000c00410b6840c403c1c0d0b9810410700b0000e2034126104185e060940c1c0f4007100c07403e9806207110402000c00e40040 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 295155134 1250 295153884 295153889
    0xa1e020105090d0806034e04060c0606180c021b0117070302120a02040801320612190209060409020a12020102100f090308061f03020c0f060f0411030304030b01 70
    0x10525526550240480c3c6045c04681d40c00b03d0064190031103005019440903000d806550040141c1002c2c07000403280c1f02c1c000769264280c1d03070480d000c00003008181d1040c0741c0881011f02c234070740103d582c0c1c0d69085158030104c0d500d20b03641d41c41940c401c0c458110980404c5900001d4a468600110907980c40c030002e4044406401e41c04004401400050070043c0300794101c60410705821203040043c01d0421452000350002c0c016041e003586010145140303149102c0740481d00340301d5001701d03a0600b403481d881029400c1015100030341007034548000e0041e882040c0141e64809200701c0d200c010180d03850040000e1484003920040c05580b41c0070301c03000076850700400034040d114440c07009001002d241c40103c2c60441c84c100c03115005858100c10200c102d0140c1c00038441c1038000e545180305a1200020007280220300412035910a2440c4100d0000c54040c0d0050807100780d2400999524445240c43d031405d2100480c0e01070015003500381040b04100b0603c2660030000800d0f00190b00b03050071659042940c1c031060 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 295156384 1250 295155134 295155137
    0x90d021002130b0301030807060605030a02061b0f0f0a06060b03150904030c08070b07170933010f0806070c02010e2e0f170f0c1b030a1e020105090d 65
    0x5229020748944142c1980103140804005130f8035070b07407400d01c440150001d510407030740b003400c18000054514000851070301080c3c000301401c0c40c1c07604010540c0321302c070621070807041280203003c5402822603007802902e4402c516540604402c1855180c014201c0d062030700300c41e0060381c09105128910305a2188480203101c281c41140080d03c031414143c5504ca2030349401040c00f034000500b0340400c0300d01ca81c00c0f40608519220340c0d9504098001280540000716000906940004c41c2040d803100c0065070758186001005a07540c2004212480d485a000300360031201c494007080c5020442d006003007298a0340690507140c9160030b6111940000c15042020901c13030304c038a551811702300810001e821801c18084003048010740e49601c3c1100504000003148251010841d14091070031b54086070408140302d1141c0740ea174085c031035460100380350040c1c200c403100f081103000c41d81c040350400c0702c2040200301d0341d807145e11803044102c1e17181d899804a40d200c0d820a01164140020300c0300c030030800917034100c00d5400c9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 295157634 1250 295156384 295156387
    0x21f03180c0e0c0c0a080901030f180224070b060a0501050f120601030e0d080402100c020d1e080301031a13080a0c03030209130605090109020f0f0309100e15090d021002 74
    0x72080380c40343c02e000340f40c0254454040d142c000c104102c2d140c40100403152007a2004d0059400c1041c4003c1201c5456800380030300e0456109000041c542030000b00d0f884240303240004400c1c040d0044800d8960840d00c02103609800a50034410036241407802000101030910b4020b14040c80c3d11300a000c0344c020204680c50f54511100071540f41d030301a13004642021103850490705803100e034282c014602c0c101a20281c0c0911720100c5d60040d418460015000415000f17801d039440101c6981c0c0b10344c5850b1504035403803803241070500e100000404490082d0f0003035003e0007910303141c84c0d482010701e0812580a400042d44501c46c0c42d1000004071240700b40c455000320360506c6444522035080503000b80c03042c4c144490f84801502c1603580c148400d948007005891050b100c00c0c00580c0c8844608040344144c40c50599014030500004525100d501e00661707021004806503907040a50b0012241a2112540c064800342c2000c0740507807000c3c000580580e4001040c500070100c0d14000d0314043d40b0b0f0048802e4507200070380c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 295158884 1250 295157634 295157641
    0x302070501180609030f030b0102030f13030f0b1023010804050c0622080309060f07081204080c0d08072a051c1b0209071209021f03180c0e 61
    0x20b42c0101004110805206096420b9150980c01003034030f003c0031400b1440841013481060700c2480b41e01c0741500181c00031881c007926084245010341088140b03001e072020402c400f000050403d50400c1c1217510031041c0340c2c00c0d401d03c0f10b11801031001e0380c1c00c80000a04610580400080044400c1548400a091803a510748441c1842410201c030744180030b4010100042581d5504481100916002c03103c01d40c2c0d010482e180d0300250f489104809180781e001e8818040e50f15a6070180008100c024440c601903441c0050f50b14904021082c1120f0036901e0740340214450b4441081444101010f080c6840c05041920309000090440c0714646104107150f0102801300314007014501004102640001c1211034900462404603003041800c200380c2c000500000384c2600100070361b410700c107003140e00801d00c15195030b540e1022206001040c0248000d0303030b120000741c805078541d8944c00c0e12811074941090303140e4500c400081d0941e0441105040100c0c80110301202144162096500307540015414403003949 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 295160134 1250 295158884 295158893
    0x150c03061017071e05040b04090213150c0201140304020a090507050d061202030c090405060f070e1206071b050a06020d0e060f010603061a0d0b0a09020a080a050a1b030207 75
    0x10480320792103502d242c0d58010b110003241c110340645a48640380f03e4541800c890400115858000c501c5800c20840c802d0000b40a12009500034000704403403005503100b40c0c2d0365424492900540160900041800701c51600c040d0b50f03104180411007806110001c1c03541c1040d034042001040c1e01e00c40c140c161540c800200d180c061081c41103d50401c00b55000307011041c1c44140c0d04131001100a412407291240c1d200e0705032542001c00c4628410b907001400b4000a6858110100c0312860050110003040841d000308100f40e2394031000d00070f030102541e00a03d05450803410250240d00d80204c003140190300000013400042c000140b000172182e22000158550038440b10710b90103440e05154005c06070203800c0030082400c11208440341281c035160f80600003d030343d621034520100d542c0352582c0c000f080204140d40906c05a504501400309000e000c811000c3d540700307802022030b000b248240b00050310200500c00c40081034001c42c4d40003400c2c85410040200c0315150310382e000c0d440c41c1c86001415000b144003000d12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 295161384 1250 295160134 295160147
    0xe01080702120c0715030e0d031a0a09050601121a0d1a01030506070f03020703090302010f0908030a0203072607241a131b03020d0e0d0201020a02150c030610 69
    0x3000e10303202140e141e100003030409803a030300203005c0c07060240140c0110b00e103907038868050b0f51201010751300074091440d0013031800c07000f83c184c1406c200504000318040c1503407600c400724900018070714a580080c4906040b030005042d055002e100035a00e6052401c140c81c500400c548841058008031003a400c1c0328510b28107045441811040d4000001c20000000300303000000c10b40911030803880d584c42e48400c1c0c917a1419001c0b03014414010b03001442c141401e10040d4051000c8801603041390034210900d607507810b00589142d00000d50100160004940303242003140041180380000090180c042003184454801074260055580103005012001015840e41007070000070001201010000e1020003042408080b041003850480c2e8050140d451a107030f031041440c803420051140400d1865040344518204401a412070224080080d507940382800d03008404003c0141014a19000540c551070003000103400d240072500c0d1121100c0911040202c001d00c0300003101c0c1d0000c4112483d4100d95041a81103525 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 295162634 1250 295161384 295161403
    0x10206063d0306030515090706050304032106050a050114030a180b010e04020a0915050603061c0f03080f090706030f0b03010c09090b010c02010804020f0d0804030c0905060d030e01080702 82
    0x10780021074a50840550640221003540d0040c001c5840c0524a08005203c9082c1240d000015410035007081c88264852001181c0003400703440c185c031300e41e1034000c16800001c02d400078410b800d640d110001c01c11402e041c18840000c00090034001e401c20500e8131800b0f80c0740b04c004c4c0300843c0c45035111561001c22140e458400d080c140c11900300000c03981c50b01d0701802980c2090f1016440303000d00701d20000b01c5420b140252030781c8403e62013031070000501e4081409940e400141c0300310351102d81269a07101c441c076000d4041c20001d014a40c0340c20440490b090181c41508060012907400b09141c0400003034520010300d4008480480c80d000500c40c403c4c41040780185610307007040750316500340068200e8031350340180340c4820781e00d001388100111a0004015284a1403100e0000d0100303030920b000a0140c900096000710425021f803131452405884d175070322001640160400c44000601c401c0c1070001c80207511406901090644d81d11281c018507850203003108006036050f604000c41c0e100014a071074401c1c00070554 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 295163884 1250 295162634 295162729
    0x606062f07150201050108070f21020a080a08031506070c0b09010c240608010b01020c06030a02090301020f070b061c0b1e10030218040305030c1b03030c0a080601020606 74
    0xb940c01e800e0030090207401d0038814010580f041450101d0446082203501003101c0c1001e04000d418560480054000780c2c4e40003060307070300019400340095a41001e01c0781400884c410400c05541e4070b41584042c0a9100710801d003030140106022801c001580c0410ba4010f0300c0c4024140c60700d030405800100c6511100f42c40c0102450b154501c001e070171b26401c440e25444c943c40c4035010b0140940b80c1c1c5555003220642c0d112070340140d00503010f000090030300382c1c000c5030020408107000d442d02e800080807030309a81c04054460420100000d03600e09000403195480c0d0080400c0703e14100940c002c03191883c10590b02c00010344155007c1c0c02003844400550401060400e8417020840d8500c3c010780c10402c042d10602c400c0c0e000e21404424448016004c0c50080e00c940d515072540760440e12a01420070907038000010207410340b00f0742c03117205c0f015503800c101540c403c92481c1d400c1a0303101d602ca0300c000c09180000d130049055502030300501000b5511003000840c00050103240b2070200b0308524070134590181c10845040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 295165134 1250 295163884 295163909
    0x5030904020d050f09061902090d060c0203040314030a05030103200904030915020106121e0b0a1b110c1002190b160206010b071b0b0d05040606062f07 66
    0x69402c04a604514030404505815404035035502c4051a1989811101040f543d010444d00b07040380180d40d0b010b0304940c10044c1c411060140e5542c0c4002c12200346228210140e48082400c004006412091010080c581c402075801c0c0044140301804a0206001c01010121140d004180d00c1d214032036115240140101109028241405c0c0136080705c40502544500c10b81801e28a00d01070700501032a0119011607142402640d03968540c6c0481d441e849018a500307a1441e1400e601040020703844c180203504411740061564415540084800d00c0321400c1e0301480510345484100480c0401c0050242a007900d20540640e5142800c9041805040c44006068808030100060291420f01d5510a00041a04980c061a40c40059a41c2d4809100f071544503942000b00e40002041d615403a84c03881500c02041c00f0340c6480c3d214a0105802081e2054811039880f0b041000744107642c006d180041c202c0d4100003039503490344104038550141c15503510203031408003c01100c20000c1009050000c0c00c1c1c1043c500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 295166384 1250 295165134 295165147
    0x61d04140a0b01020a031d04060e180d0305190b030304050a090914120d0207061415010201050f060a030b130f0f0605090712062c010207020301140f040f0503090402 72
    0x28200c0d16800d440c40c8490710310b8518000615400022243d50254054403100646684403c0b207410f040030613000b06170816244c21000640540141000703010b501454440743d500b4041100080c80c00c0011100300d030030141008184414034514912a00745480a0800429140316410100b40303140f16540c09581c00032140c0c0000034000c0c00030351022200c280304d00140340c0e07440445d0100ca07540c0c0e0504401864100741c00c1001c42d480100c10b43c001d1042d90700c204004035038400295404404400c007100e4488030002ca10908000d551782c2886111b910403102d041c141d001d8140302000c9002d400880c08028000001580401c1c0c81c07000c045416195642d011034084408442440d02392451443d0716000c88402c2d0a29011a15600020880d50242e07018a1114294101c25441d018064281445914dc500000c0c04070b445c49001c45001030020743e9020000542e550b030b1395106050031036071059448410300400000b4468005860351039103400c0381d0071000594001c00c49041c07035030861003000c441d01da0051002421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 295167634 1250 295166384 295166411
    0xc050f03071505060102120d060f030b0708100e070c0606030c170f070b03040b130212071a1806130b161a1303031802030109150c0504030309061d04 65
    0x802801d480b580c2036003540070301e80d00e5100548100761140750168001000b5207c40003c00f0b40908801918000041005e907504c01c1210b40b00e45071900141c88481a0104010b18a03810008032b541010a00f0000041c0d94070307003c14040e0010000c0d01c001c0401803040040710034408a60800c0c030146030402c100c5141d0740c0d66107140680354400024020954002c1007020800401c000c200c9000721111201d01c3e614654541d685e070044c0080081c00d61440c052480c044d44050380790b048819149440e004010140e07107040140400c1505040201a100702d0b604100c0c02d040142da10b40c251b11058420b40e031140d100c2300e500900410240890304000514000412440e030440d000b10620040d4602800c2d5210343c40000c0c118040540d441152040c40c03801026010000107440b81e030260030400c0004005032140c29140c1e00103800c2d150491801d43e00d80851086112845101d441240109407150420074030713192450b54080c1050000744603000c14804000700b10341d4440c4200c2000800c0e034800070000c000700c4041080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 295168884 1250 295167634 295167637
    0x30a200306010306050607030c0809060723010501080a0809041119020a02010305070302180d0212100501090509030301120b0a06050a030302030c100618050a0f1b080a090812070c050f03 81
    0x101d040c0040d0503d180054517040032411100c9880d010760703461140c8000303520f032a40c4a50000c96a04d8001d6000c010f094040784215100d0a0360090078038400c54014031501040d82510410307084149203411111003c000901d4100448000900594010401000681d0717007464a00812200d0a180406c003044000c110382c1c040b400441c01031003600c080216444515044040707000c1c3c500011246880f87c0c5481c00b071031a007132410b01c841034801000050342010f5000c006042455600da108040b6480d2001400210300314000e40c0d900240401c000c3d030943d8901414408e10901510000c0c200041e80c42c003141d40c1004035040b4034080d04010306031300d030a1582c03498001c0d6644c0c80384c07918030401c0c018031507003040e40542405407500301c0e42c0d4074805800b58642000b1783c80c000c01c000b61a0802e46a542c2049001c00400da014411030750340c190b540b85810080b840740c00f03004514020100964540303424407450008016900340d603070364200648030104542d00c502059401c0c5030145006401403148011101c1400800030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 295170134 1250 295168884 295168891
    0x1030506071206060e0105070c05130608070b07020306040308041e0f120801080309040b0415080a0c060e03030a03090f0b1006140f121e07030501061d010f05030a2003 73
    0x2990820000c00c44002d181c22208980581c00000d040d007140340c83ea0350311840103000c0c41c901680c52603808981d150001518613000a9004950645a100406c0200c200b4084c0740010311805001624000c080c1d400280c85800003400203091110400c040385c28003103011500d0300b03541d45c2441c0c2e2605440705410611040d03a0041d4040b64106060b19500ca070a62040714560704039283c6100440c240001c900070000070f40b81c80d501f80751f0000c1d502c0c0448500c21501e803208500411804018044c2100541010700000c480c5810402c00c1c030510b10b1403e1802c0d03c0000031942e10b42c205240008807071000d884c10403401001d01c24041d01034a50b500034800030282d003034045000c0716070355120616010303040c45510312140a0b90030056141d4a05010300c8081d1440000c00b2941700760100c0c101e05074101d5002c1e20400c00364003581d4450029643d14014080c0a42006900da0740b00b80b000c409185031008100000c0030001e1702c20018040100c0440070603482031aa421910a1104030002040c4121404649040a42044 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 295171384 1250 295170134 295170137
    0x80f0306280306240f0806130c090c120c02010e0f0f070315062c060405090a240204060e03070b0403080d0e03070c03050a030e040605010e0d0203070e0103050607 71
    0x969160680c94015045580541000207403120920310788030803008240744c00c1d00c0d1000182c03680d501c14a02010024140c0604112440e0550243c00d044020749421802070101a80c50b09950040c0c020508034100c0c1c0c001c030703a1004004150a81d9095044485005841c0840707002e50610400446079601034112a1100c541c03903084403105040300d2100c0d5507400c20707140c01c110541c000800a002180c1d00380f001c41d640421120000c22055500c110441d040d1a90f4580c100c107450750400c0700d0041e5512018400c0e0080400c40d814441400d00402560701c50140e03182c001d000c2070b0b07a0141c200c8811515007400c05600109032045490b5039880c00064144141c0102c914400e01818001107100742c1c00c4400c1c2c0301500d80120031181040580c521640003003c42d1000c0384420311090058400060315202c00b080918895006440d011500349005051302000b405064403460601e4000d01c004e0743d0094a0340110407007210502225503990002c2410001640c100c054181201030020007806400a102805031090703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 295172634 1250 295171384 295171399
    0x20a0c1d0603011e05060f06120a0b011e08060409080309070f2c25090611010608030a050a0e10050903150402030d0509130e06090c010905030a02060313080f0306 71
    0x5076400c1500303d5401e1030400003100800703600704044000c4c0c0d82c001a4800000b4140c103d56183e1100040c2c6107400141641740068035540802c80c000c01c90307005d40071a00d0020b0a00d2000071507009000088203055141c504100f01016000507116a55900020b540ba6040020b041c1c1d88e04081241c5512900301c0e0040005e200421140064458890020707038002d0113420200154505003503004415800000c1d00204800720807071084034150f00424140c035481c101649600e01041e02e000d2001d0580740e03a0007102e440d036074036003002080901d0b401701c112064404649003555840207880c2c01507030504113810003540c021800080ea0f10b10107410400400f0304000031001c880c0c0145090050000d80313903045074001d4140d04a1111140081d000b08064058010020301c5040090f0784040c040088684480880003298820414000070070f90034000281042800c2c0703010000d030341c10080402d03070703030b820031a0000e003e40d90010008400c040d108400020303003903004815a0313a5078852580c143d0b075a0400e960052150701f9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 295173884 1250 295172634 295172641
    0x60f1b1b0d0209040206090d080c0a020a080a02240d02120a06050909030406200f0d0e0d0b010b0901050705120a18060f0c0201051306080108060c0a1e020a0c1d 70
    0x1070480101007065070081c00e070003684da2554240046500806d8072181c10407041c200620000711950040d00c1543c035030b40c008241c10a4180104007065130306a00200241c1c120320340505c05a10b03113108600324410a600000019600c505032046c0620824002c5003560f880881c8002d51000c6200c003d901881e4200010300c00551150100f000c2c089003600c041030f2580c010070003000a64090000c0c48012286809045400813000032000e040c0050302c20051300d5030704100d410060b05900300c0946441c3c50000d440d60320000210799104c0c0347e055010300445182c2c04010803065616841001150308407540103094540d040055030b482181ca170859801170300458180c1e03401c0045103070605034000031544540e903445409141034178144c071180c900d628141e04204d000c001d00c0b40401c088011407002032007180d403a40c4a66260056a030304000028040b0081500100086079405900144580c1721840e05a400341104030340360003d0345080100640100814400c00c03000810800382c002141c6c041000410080060340c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 295175134 1250 295173884 295173889
    0x30302071b050a03060c09030807060b3a140a03080a050604140c090d02100e04050f3706090516030b03061f05031504031706010509060f1b1b 62
    0x6249014440e0000c00498040020171403c2d0408991a5081c1c1000c860103900c81d1580d45a41c1d1040b9010780d0380075210808031200e810680180c00303600120300c190b095104035116a03020405450200c5c2c4009c000c0002d02c034001d200e655014281d10602c10f208856004d4070603d005402c0b20780c2181c1243e1920710341800242c80d41441c1c09100c200708656032208000da0f40d482c040c1c0700e483d003000981641240d03410300c9040041e2200207001c030520316030340c07181e14007030351880100802c0c0c9070001c005c00c1241440e14144034422800c105a2902450b040160702c00c210f01c0d903602c4001d21412030140c0b0003014140000000d44052a0340314500403440c0031700150a40340345940176400d88040102e56901541b00707100207400c451905035082d00d000c9205580d04806992500007078a003402c41c4680c180041d81e46001d1104050701f2515030701d141c41800104942520f032140019103d401200b100741e00494001401c04290038400c0304660784201071030040740ca4038604141c142d6072001c8058604401aa110482000b42e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 295176384 1250 295175134 295175183
    0x2120c060106050c0a020d08030a110c0c04020702011b0606050a06021b06180411090108010f06050d05060d120207050901061103070f030c0221060c07030f270303030207 74
    0xa004000400c540c1e442c1070380440d4658000b400c80384031030040400003001a1ba0341c10050010781d01440c0e400b501d030300302104010226800b54a07003c940c9141084517515840000c0345144c3d10030000c807070058641e1007500040c0d80341501c0c1c0d0703582c0201ca00710f00c0c6d1402c10400140d000d0350a8840594800000c55207451045c0d03038407040f4885000c540441c82000300c20514150b0b00a203015092821490100e01c0090042010b0b1451994000101600480c02d1051964000380b141d00600b2841c0005034250300d0450043c2c160711684000c014003a4517940040d4190325400e00029225500c000b0001610010b108000e444a209011b5503201e02c11b148000180c0320b114000007810180044080c614144869a404002800a00084083c015081c4051026980e038a501e8517510b40441c0f2440e0503200c0c00954641002c000a00c80d1140d2a41400000d01090348041c010507901a6810700314581140d802904070000000340400e20200801c2d0404002c042d4160054048144a0303220a40801110303120b55210 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 295177634 1250 295176384 295176397
    0xc1202070201020c10140c03032410030f18060506194b060e0901030b06010305190e0c0103060f03050607180f060c050d02060c040b0d020f0313030212 66
    0x160f1007520280000e14080c0c01000c0b850398182001e141d6060305030001c8169400c0b04200340701f25040881000400348a0010043c4d01161020b406102040b42800080400e0a5404000f08140d40d80d28810180303685a03019540e000d14080705046602514504000070304811034480e170040340070001c018201c0c89803103010b13410703140300080c58040c44600e400c140304510000201821502400f4444000c0b580c4801015001d1051890100c0402402c04c0000f030320064882e00141d00031030103440104003050030491084d400203000d28000c20151200746481000a0b1080790524100f031500d540c910010a00203040401e5083c02c0e04c06000585c3d5810789a01c1c8005280300207032890308524006620580700e442d583d5451a01d08907828401d5440d4250706084186981007000460401640d440a1100822207485620410720042c401d604c0c0c16150140c40740964801c84083c1107000c0354003078101000350141c0d8034240c0b00c00b100545a1900304d00503848041c000d1400d8015020f10300c0030601c402c12200031103c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 295178884 1250 295177634 295177637
    0x31e0319090203031b01020d0c0e0102070b0a0906081906090501062c27040f060f0e1b0d0501050c0316020303010b07080d0b060307020a05070f050112150f090c1202070201 75
    0x1341568107803100c20364a8106542c1045d0755081105094101e00c601c644141c3c2c00850792019080b034041000a40342981980004002d5081880316201c0d19900c050084103454a42c41c00450580f1142000f00100c803505410800c0301d4101080407809610950000d412a010340e82c6000c0354840030414240c02510182140c1c0418650703003940780c4282840c0c00100003900c5041200c040304500c032050100818001e13182245e2a603540700c6042c0910100c1d02941044084514040002d00641d00c03400c2d43e07031241120300e041488407002d01880c0580d551002c0e440c059400c40004c0c0840d107890500703a030035640100c40010f80c0c2141e0b11031507841c4500c00000d07641a00c440241443c80d08129890382d501e940c1010450001c120741b21846600d0541350f034005103015070002c0d001050700c0d945901d0102e0500c00d41da0072150100303a22a0341042a82c0c1d00030203d01403441c880d400010700b0002241c1300300f14050788e44c00407010050240390024404041358800c0c40b2007459961501c8002c0c040030300741803c0c4c1c82100760290 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295180134 1250 295178884 295178887
    0x609080601030b0c120a0603030e010503150f24041505030412052d03090d020c030a0609150e1e030301050d02060901020709110a170702030417031e031909020303 71
    0x21148070711a900420180034560170f291404440e9501800c1c103d9400300302c180c8800040040582207400c100d1002c5007404c109046103401c0d54076146580404081610ad118118440d0003980c5440321286d2031600701065400c21b1620100e5204901c1d881485581650743c2414008071001e40305a00341ca010740d40c0b1a1400014144614003203486c1e8201d80707c810140000026009080301c43e0300a02403100350080303142900c0345402e9003d00c0c00c0ca11000ba920701550440b4034201007568010813600c1c502e90380200002800c0100b030904907075504040010b1141d00d4600f5440c00009180000d151130345500e18854030000780c0900541a45a000c20f214250300712040884c843e00619004024142d0500184100c41b00c032561183c0700d50540c1d03024180707040301d000c0010348000c0c42a03002d00d000d062a5601640d0006604210100079943d20503803055603e4038981078200404500300384200c403800c1668481d003420a46040050303101640c42560200d0f071818414005400160480c000d202140350001c2c040c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295181384 1250 295180134 295180139
    0x90102130b030705090d0c090b030106030b0601030e030405032407030c0806120a0204140a0e011116170d14060415060311040e0a0603060b09190c050c0d020d08010609080601 76
    0x185142d000944104207104040c03089031110303210102400010740c0a040d0b0301c03410030b16107030003902290004c004050099051150030300120f02854000d41c1c1280c001c0c80c0c00124040010403c4e400e500554010690600600003602a019404154001d1751905039242d10308940b690b81069003140e005065580200b400c80300002c04038909410420010508101503a6100a080d400282159001d0000c01400b04111013440321180c0d0510459454192000003084100145071000301c4500903201d2020340c079841070071501c04102030440410002140780b00c0c00c5d5164000110250064950f000c00c0d00300c60b03000b503030001382d16150034002d02e804d01e280c0070900d148541c10322030200e010b800d4281c0c6454459100300700c005040141e82c50030602c2004c0c950700029509066203049000c3da8900307400300d88a040000c0500544c0c006040414001010703d603030000700e8003000c1030155114050105800d01c00d024403051541c046c0e4002c140f41080c84110365464840d40e8844405640f5a9102d000300c3e6010b0740940c006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295182634 1250 295181384 295181399
    0xb0403140303252105190b01020307080708090a122010080c040f0914010e010302011b11040c0302130522021309020a120c080c030411011205070f0809010213 69
    0x154070018050300c0e200d0344013003013030f01a03580c8007445503481040c143c0d1720720030480140001c000041c000d03850b101092103006201d9000075520302542e0805405c10800040d80e000f000155021030388560005444070315000d50320684104602c2182c40c040e50b10340720081c9180c900c481d12003c00b44a0200060030a100c03d45032100890741108014051040314804101c003041d290350304a42480144902d60303000c541d4020799026001101d206911040c12901400018801030b07030480a803c1c400400c0082055030500f01d0300b0f001d1a07040e100c00ad50741d0050b20700280c0300c0e1031681c1354004082c81594408882ca64990b02c00130302c5105413010815a40306100c0800b184801101d2b5001400c41048a4500142450702c0d0350315031007203a116001304000300307030381c4812000d20f10f45900440500c00800d007003010592405042c5640148001800100780520181003030403960b008174140d001030248081d00700304078501440003810001d540701184011462460010301101014003c40e200d040841d44402c3c0490b1406c0d03034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295183884 1250 295182634 295182691
    0x20f03070c020307030605090a0302211c06210b090a03081306060506040b03010617130f08120a0204061103070f12021e011a04021e0a0e0a0b0403140303 67
    0xc220f0f8140294540000805d65a000d698050011600600304124092030064a800c1c00744101d444140900d400d49c2c2501c4042d2001c0d07503116004a0b03110020034904100c031034010205c41c1c022111161161400f210031010050600161034031486126865032140003070141d0b41e0708180360007000144c03c040040d06500c0c48044c0a8281403040601180c215252000194a42c01542001c4030f01940400108905a0701c0004009010340c0107500d10b032076090540c004442440d00001c0030700000102000c1800301f03c541d00841d100e07806003280688150614040b100f029601c0b910958000905186102d03041c400e000c0b04440c45150320580030182c120043d52499080c40080c0244815805a4454a0314403942c5080b42e01002012100008040800b90403925901081400c1c1502452040c405084001c0403c050f1031444c2e4580c00005440d415800300c00c0f60b841c0301d0fa00c8070301e801440501001503d02030040180003581d200e90180413041600700d03080d641d240400c851002c039a61a08000c86d0302c1540421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295185134 1250 295183884 295183907
    0x1401050609030c0a0905040507050a1404090c0504090c050406090c05030613090f050601261f020409020c010b040b180a090609020a0e04050c06030108070e06040b0d03090f0801020f0307 81
    0x80c01d0380e1285a20f00300142210001e07500180c407160b01d44040108100f01842941c0190008032051132107542854031881a401c141b02e00c5138041c541d82d07034050003444508d9034401c008100081050011110600c0e18604400381c078458140150304040002c076940da040d002e01d403072102e211342d0790900b0369a40c04204400700340501a00d01000e55514084000b00b100742c804001414060001815554500034012110001c50110b501c039102c010641911000340109409810051000c12000360007844201c51000703203d1030740088002c0d84006500891418190000c000c02841281c0803c00d0055030014409404000c10212542c1700555000070301e40005680b000b0f40d41c034001e100005001101d540440d10707a030340507006040034000c0c4034108030410004111141c1404c005850310b6055500d08081c0990720f4100e8041d8200b051501d0000a116844941c0500d812800090001c2240d105504000e40081c0c07060040d41b801d80e54103c8042550601402128029a08401c1d09031a5603140c95044030080440c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295186384 1250 295185134 295185139
    0x112090f0203070e01030507121703060f030601260307020f01050d09060906062102301b0a080109020906040b04020c060f150a0515031e0f16031401050609 68
    0x2040200582c034100030f070102502c4105101d1906504508080d841c184d0300e03074410744e0952580e04060300010a0b8114590224941000440d00c07503d89a00240380390070f54000b02a0540b00c3ca1000140c020030650740003100c1e40300081080c071000000c50402d500c0c1c0c8541e1401941003100c5921000403544214010281d01c8500c1e60001088240790b0f035090103a8203160340960f070840e12010284001298200103040300b25080000c64002c0381c0d0b0b41c2c003198099100c0380805030070080002100c561340340c040031b441d07903840e60300001d803100c6180c0002280241c4c1500b0a000d4041c120706400030800e038005104c2c0c010100d0f00101200c50782e039511405c01024000314400540c1050b000d014024407000704015a900410f880050104103140c0658806510540c1d160042d10450440200704495295042a440340d050044071541d602d50790070b40e040c0380300d02407070041c00c011803103040800071612682c608540c010740f0741c0300e10141c0c0d00d400c0748012400c0d6082a02140581828600100a9481c00b40700602405002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295187634 1250 295186384 295186403
    0x60603011502070819110102010b1f03021b01020c0705030607021005070e03030d0b040c140301030f08281205190902011209050115052d012003120903030105011209 72
    0xc1341070311818020b00c001c1c0c00e8901d100c04402c0004001d24190300302c88146003031008008034000240012044200c5060350f20081300050886101284240c040f10303012145841e001e0403507956011101d0007540461842a014021100003041500d4040b5545001c2d10b015030080070340207a8a074000009141c003401103010320150b04108101c07900d09102404c0052055100000c511001c50184400e40e00d555003414104001d41c1e0000d0444003482d025241540d81221003031003000e40394501004103110341c1c0c01c95688100f000504080e58074621407840807a008a580781206c00c949541074000b030350419104010100301c0040700c0d40016101e90310003041175005141040c0c800ca100c90001003202e901c82e0040c3c540380d441e400c8030300404200e8001c500040c2401c0d41d202c0d60644038104181480382181c41515a4020707594168a130300d80c402d541c034405508495041c40070f0501d044020541c0d81c0d108504040c48040c454001410b01d440100a0b6812600c06848030a200300000180c0c1700144424031007180c01c000b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295188884 1250 295187634 295187639
    0x10302060a08130b010303050309070b34060603080d0b19090b0f041a0111070f06080a0e160303031802011b0206070804120213151202040912030f0605010806060301150207 75
    0x803040120300950090322040d0349d9041c202c040d242001d0054011281c48403041040d600004114113200348403101c0401c003d13003503610004910b0081145204050141c6051803800300078491140001c02041286000401c26014071405201e2242164181440c0d00038440b6010030400744282c2001d01d2050005140ca50820300e90400101254140344440f050300c410304090015958204072a4401c0c068040000c1c0003003498940d1200320050107005d00310401c10946d001c190145200d8001c100248198010b8542c00c8081900012030180ca61000b5070000341808444440e410181e01421019501a0f680b1403914140002241c8034205010049801520070007151000c581b442c80070388041e140c0902081c0803410b00c1d00412181441c0e03000002617041c0780c48030259884101d2007a02049035440c1084882d9402e003800010005c04040300040d003d54103500408501e00d91580c00010501d03040c01c810441d00e521ba000441d138440d022203140f40c00043c1040144011581285007203a14041c61049804458 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295190134 1250 295188884 295188893
    0x70f1b030509030a111203120711030c120a08010518041e050a0c0e0609090327040207060c09140d0b0c04120507030201091a16020102030f0a0801090b0108010302060a0813 75
    0x71600034041e00c85e0700c3d108941d000245840e50321940b101c800c40004605284080e8585004648040e14090034030101c169488401802801a03484048408084c0c4058103140c40c9150b401c0c1e4442d50300d03800001c0400001161038a000304240c0b1030901000e145100607580c942d1058614a140303820038140d02c0e0041c0f007100015600b040842c403854402d0b02d070500040d01d024118848400302929651107000710a0421075007140010030f80d418086107010003a81d00d0f45000c20846214038225140c0d070400c1c000202071302806106c0d0000680c1c03803007581d114403801d070b640d071800c00f030304106980c0307050313015100c14207070702c049052245400d420000a01140340341950702c591036006013017041011100c1e50440d00040080d582c001d80c40c400104024201c848000c8904080010b251181d40c4200400840c1c00f8107160969201f082620349000715a201c0c00d556070002080509095070911071200c0c16410703d604201e40d94460040241201c0c0c0c007404107810102c11650988031080020003c2140c060f101007100e000c103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295191384 1250 295190134 295190143
    0x61b060e07091515110a0308060a05060f031506041d0c090a080a030210180f0501060b1602030f0a02090c07060b031b04050906010f15021005150108070f1b03050903 72
    0x2c0d81c0b0b80001d83c04030300d4007082c14561401940c0800612003e0491140305940118900c461141c0c03510344072041c3d075a450700103264034030650401904400701045054840c034003070000350b005420300f442c4c031203801060030200140382c4601c0c0150014040101c0081400c030701c081030381a8000d400e0062584c20000e4a0f0046440c144c490b42c0f0a02459106e08055800c0c103806000841015400701c0c0148503099026030b41c0001c42d5401c0348000c0c090403d44100c80244070342903000030040c0085001081d40c6610184800d000d032212900d0980c400d01850710100341c458400035592100590142c6440e1040d074480603102c92a8118000c19036500362200710b501d0341c580e02403010308800c1043d02e03200d0081c500001d040c44200e90004204254651241d4010f10640185c00f20302001c031884c175030380312201103042c11040b4205102c080c007181000d4204800d10803403003c01583e803103c0981c05c0e40d81c100e10b6590032600f00c0b000c10a088503440418040d490707110300c14000b41e116520380d60083c02c1142c907084030200070a150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295192634 1250 295191384 295191401
    0x30a0f08071703090a0b180f0732060a17010b070308060d050a0204051f0803090103230a1503050303150405070306031e030207030804030804030c061b060e0709 70
    0xe080008000042140c0340c0070410b04220030500c0c09003586072940d6000e507500707000f40006d0829040c1034005203108903403444e00031941203500280d42943c9640f8005960700c3c1054080c1e5907140081c580d00995070303641c0846442d90190a103400040c1a1503031014010b803684442840e100f08400b06014031702020b250700d1001c0c006c24038541d8150781c0700d41500340102071b280f010b0003651207103000c03071800030101d1800107032009070740d070120f4002501d9107414107140480c40060301c0300a04141e0075500015406804000307032400c1102078030203000c2e0505080c9000385d84401c503c0d000e0310001d018030105905100c82c0c4d0010f280e41c01a40302c414145601c030b445091840d08112445414401030a501000a06050007400d4000c3d46a0400380005e40c00c5540c2c40c440001d403102090654a141c8000505062081000000540d00a594075603a1074403400c00c64040d9005010694180c1e144000014a9a111b00400c203950020780c3c00882c5207250030b594042c00740c100304500d480345215840000c285508a0b20031243d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295193884 1250 295192634 295192643
    0x10c0b040c1511060c210a0209030f0703050111070201170601140d0902011e17040f02090702030304060c0c08090909071503020706051308250b100311030a20030a0f 72
    0x74400c0807440f05134540300c801400070049040610045030708804120506040598200ba800c0740359032180d031001e00a008407280a40d040c07090340100b41158001250007029640140d00034400610540c420508622440c04001c1c005002d4240d04526080c2542d03103140c010805142c4076044a2180d0500383e40c070742102c80c00c00f032100d580b0903000c1c2c1190b07004240c10074140c00008881c040841e1400010303105141c100100c85980840c240010104000340c0307600741c5159401400e03180f460410900080d80ca400440d422248140340c617100286d904e026092071414550f11420b81c41c40c00b84a84140074019001410710138007881103400101e22290201000030307100140d80ea00580b214407506111040e240040d107419818480400303081e01084205088034010440300c0d421400c800020324000011401040c0c1c094906400c10050000401c0d4050072b1500302d0303020300a401c446800001c205030b2140015400108a46061040c1907005030384070b0095614040c004055800c071642985039400c07061f884030421a03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295195134 1250 295193884 295193897
    0xf050102030429040507171002210a060807030213180b06011202031b0a17010b07410c030303090a060e03070519080706090f061802010c0b040c15 64
    0x302c924110410744850460001119141015245c4607101c494501804d269081c1c40c0c192024840e008105003030010307803551030456803429a1402c1404003491000031007143c0b020b510102d81c4140082c00392001b82e031020005010760340e146500b044600f00001c0ea00c2c12400d91514288005902c0d00d80038410a180103c06c0c449280c90302d80300041810340304041e02c805840c4140144410341c4d01c084503d9130600301a45002b5035401c95075100f42c810302c210403c501c4608004000104440b2000c501074603645205a1280c090030030704900d40000350000468036590001c0c1e100c10300361510a054180f032a42c902560070380303000e018028042405c40d4012201614180d2042004e4400c201e414460100e220903444061170511801c3d5460750b03250380c120b40d0501c0407004280f0b4020203108290f0b00301e580c0283d1056081203100254038040d8101c5030041400e903034087ca8600110b0802c2d040400b807288807a030580d9100601c0c051642c5888000c030020b0300503507408900110201314410743c4589500c2d035142945901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295196384 1250 295195134 295195163
    0x3080d0510030b07113318031303050d0e011205040204390806220f0203090109020301050f010506041a0408060f1b0f030a0513230c0f0f010c0f0501020304 68
    0xa0b49400c0119146006c0e1100c09540600100d2420002410b01c05404251a4140c2c844d501201151000d05c40303401e01d03501000400c11843c11300c0758602310440c2e100301c080d910501c02520081d584510040e5055022417041c40350400241c501d584002d03070151000300001104070100c00c00c040341c1e101c200258003520042d09038444512490002ca11140400d030b191400c42072a004010808691211002d02d04c410710780310703440c0c149100707907082269403d5070344608540300d24080c00e1080c041c10380500705074000e52a050124a40c11a240f80d4503050f03c1006d018945060f00c1c02c007850310002411703e4801268030007444042940a424070040780140300d806000710040c1070041041004541c4204821104441000a9407281070800140e9500c08a406800a10742c1d23210000d00c03101030103001d40200101103c110003c03440004044e030355902240082250070b0f568041061084c00103031207506030342c00340385621034000a6200e03981404803140300b4800080013401c60b503135103400da81098608a403100c1001485 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295197634 1250 295196384 295196417
    0x9070b0a20010e070f0e01080c01090509040303021e0a03050f01050f01140f0403030305041e02130f0b0a06030501090606020106080a06090309091103180a0309140f0d0b01050f060403080d0510030b07 87
    0x2107002d41320100c049d180b01614000040d081c00014806e250080400c40005014580654141c2e07040c80c1100403020300b10851030000122592100e1b0050003c0307031030700010650f501c90b0441420305940015040301d101382074800054900c001500c0107141010401c0000c40140c0c12204040c1005601c40d860216480c1080d2800351600c16100601c1001c0003103034002c1d074001d81d072010155080c10400200004144040303c0307100026000c0d0500268001401e5030340000d08a034554440750499005035003c120098444004074203a404034803076807ca030f6108001d014040345899204c0701c000c900c641042c0200f560350724440c406444084000c1c903141c00e408030030441814410010481d0000d0b880c00075061000065401074030080c0e9600500f1030651800590444540390f0100064441000a102c0c0d0091034642c03515100c2403009029642c02500b00d40c1c07440034241401030a640c00e0302d074014429401c10a120302d001c401010300424510045c02e0b84480000442c02030402079006040a54030510240110b00320f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295198884 1250 295197634 295197659
    0x90c0310091409120705060402060d0216120e04140c0d02091002210306010813050316080d060807030c0e0601020a0c150e01080105060703080406140f09070b0a20010e070f 75
    0x600b078518113020020031000500100d2415031107541100d0098a03081d8031102c900003805a091404d80c185443c3e82050b0510012a0221204584507924201112644418801500e201d808480c808110440100300d1001c0a40e000d03202880d64030714010300744001d41000411007454486450056000801c0c89107802514042688901b031a0095862840c1030620001740301e031600030320a0440e000103000324800c00006000b240c26203040c1490700704400d43c050401c503001da4014151503c070781d0700d402d8000451000c0402d107001120303004104202154074005c6100000b04000f0102030450085042d0b050014041e0010310024081b01d03040150080c0c0c070080003800100c00850003034140126080104515564401103c0340c0070fa1620344444151a03524060b00900071030907880307500740c40100400a205a10781d6240c1c1c86110f5400848040540d1040c40b94524800c1542c1880010032001d400d20f0280f400d491480d4082d619100001008d402d045055030070300082c5c2c0c1001c16807940305c2c0b5041100b00c0e031088 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295200134 1250 295198884 295198903
    0x6060e0406050c1602060a021507050c160501020604080a0c0f03050c010b0103060308090103020903101d071e050f0f0d06050a06050102010b09011e0803040605071a06090c0310091409 80
    0x144402d00c1c05036480c4204d0206802460020706c282c90000b00d0840c0c0e83e10a001c00d440070040e0700e0054506040043d40500326402240568019120352207074909500603011130a000c460068000e0000341e120f58640c141c690740078100380401d000300403070350000050810220111070340c042c0e41c4460300c5408001c0c0c40b50035510041e40f540c0c100360414170240040745c407071402c0321100c00d000d01f00142c1e100c030400c02103424001800c0c4150300c0d071443c00d0060700c00442040d80c10307411420400d00f80c540c80ea447d01400344020b2221030f51004071581111050156082c03943c0005aa100c0003400d28442d900075400044e900d13584d0386001c5803010344800034000504510302138080502000d00003400b580b40b603103010401f14901442188a583e10400503484017444140303466000e845040152956a901c17078030054615030100c00d0480e460039580c8801c06031240c625040d5030140300010b04480d0b241d112040b0030b00c0103030005444569084034444000400b01014400d001c4143c2e1201c4580a4a20703108900500b0140000e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295201384 1250 295200134 295200151
    0xe0f0303090d1b0c090c020708030409060603050f0c182e030614180c1b061905040f0b090c061206030c010f051e13090b120102040807090e0a06060e040605 68
    0x103000c40c2000500c403107140010340d005020002088040c4840481c239088450b442100300f80000100480c020381c040d0048800d48500d52000d000703e80303403289100700482c1c04444040780721000b0300426800403200111110740c0403005000d141d801407440f66005012440041d07201074500d0510b82052215014081c20000300710f86118060303148102c070045000841c2c142982428280700100007071804280c603040d901140c0d9140300902c40402a03013101940c0d00d900ba81d5020391000d40c62807011020400c0c1c001c0522540e4010f00316848140c80d030b691104c9005002d03002c01c15a004480111050b6183c0c040076022100304002558010b081c000c2c00d00d4100420580094100510041d10048035504081152486204034190000f000442c8246251034000d4001e020346040440310005081c5010340c00020030154200c5680020801a1450a00b03d00c00e0344a640300e00d41018204201c600860381c801860303141c144069480d20440c60380c8040499a0a030881000d0300702020500c400d01a0360701c40e00b80e010042c17 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295202634 1250 295201384 295201427
    0x21902030a12050a090b01170105011211010f0320072102060105010f021c05030f0601020a11100e031608060c030609130203030d0e0706020d03060f06030e0f0303090d 73
    0x80800600148000071164189611140412140380041c0c5c0a02d500640082c00c111041d40c40d02d01450162542031264011982080004101c0301045440c4a6283c1da00000300781e80b8020101c01550618402410b40c0e040c150745a4040800c1c440c071604070322100c011207900a6941e00d0510f0328100c7c0d00740b010241c17030380c0311404403135451107070b40002d0614107480d42400c0c2100c01c0003142d41c00300c2c07500860354552494041c8681103400b5590f0400041c6000b00c000c1c2c035000840b03681e01001280e5134003441002500840c2c1c08010302000f401c24071050b50b1a100e02c0e00d4030750208400d42010038070300307099405e0038ad0380f24046000400c0100303000d02013180c2080500441520b1410400c00195401c0d001a001100340c80305c1c179610004540d0700300700b203070b49203103800d4010702c00918040b820300e8440410b0b20500f8058050004082085032182c4540010390708400d0440d5001804d00404500038101e035041c1c00224800c102d100d454000c42000034501c150b80038001014158808240100580402e4030110f480700030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295203884 1250 295202634 295202647
    0xe01061a040b0724020a0906081e0106050306010c0807050703020907110303010311132f0a170601030b0a030c09060906030b1f0f03030c0605010f0503060c0a03020d050a02190203 78
    0xd502111003d03500200c180c1c040c00c0e07143c81c40301480c0703c00c2140f00100620010300c0c0207403d600040010100c8c0c41503202c0302d4141c0d5518220605501c000f13100ba4808121030401130000d45c2c090800b80d034000c0070602d00440502e01c00ea440b000b4951000038280c92660040404104500e41001c50980c441124500310840085200c140c40d80c900044c0070042c908450307901c0511040d200c07491208000c198403c0140300310502000c021004aa2006038040019910f01070104041030910445d0310b600d409581c0d44030403811800c100d070345080700940071070304040c0c9899071000a0303522603415802a46c041c1204901c014902904d8900712561680134102c1641031030f10030404503a80d00c1c01542c1c0089108645038000c1702529000c2c01d2525560030840b00070980d240040300303045e8006446038503541b0518040007980d80703070440104a82c549204481d4990f110100055844980a018100d0701c00075060250510443c00e000b1800d0358402c80b03030f24100d294045007144181d4640d012203040800b103400510314140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295205134 1250 295203884 295203899
    0x1021804060b1801020102121503010b010e01051b100c050a02010c0c1106090f0a060e1806030a1203093905010e190503030d0e0d09140907050903010e01061a04 70
    0xe00d942240350b10000b00403d00c0c5a4002c0d0102c4510b900305825049583c60100c0c8403079584912041d072903020350b10f00041e0880c1e41d40544a040c3c81f80314140c444038140681200d08040c2c00502c09200780c802e0040800c0e108090115000d40d4400603403d03100c4544444034030000070300b1501900713032040c00c005180c101240462130540c49000340d001c0c00c0c0c0348140e580310740f0000700e14581c0d400d0381034641000f42d40c000041e10540c0400d04920507001102c0185095004441d4103030780e02d0059610303070b0741504042c4c00900041c003001c0c0542200b44c49814003107200042a00c9809200300b0b4281d0500c04040e24006142508180c4840d1080822031800b00c080310900300300000303142c400c0201110340100161500c20b00c0c02e00c104200d8038001c06d0003c003260780d50310b02c2810b0080903045070144a40140704031021a4041400390b0100300503159250910310715221450100101148054040b00911008010280e82920203015427942d5660315000402c5035881d0078400c9406414150741a14844000d120500c13611 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295206384 1250 295205134 295205137
    0xf010b011b0323091504080c01050c1522031805100f030b060403050a062c030f07020d020306100e01080c0105090d0212060703050103260a0309110307060201021804060b 74
    0x803c406045440300d40704040c2c00d0881d20402e1030003640841280e00384c00c02c8500160044c8151200c880581e12410400c07001514503010b41800e240c2550804008030758110b182426880e403180d113603c07540311b981c0481550210705100c0f0500550010380c2a107200c09200041000480040c071b0103803280c144201159400900c515942a15070040540ba41c2151007550b0310f4a041d0f501840c2c00c2000d889100205150100050a14400a50744240d08540c4501d035500e2a0303041519142561018506d420495040079511341d006503800c980c04a2000540030250701c1c01c002241c031610030301035621825400d20750108070000059101841c80e038884550a201030341d000c01543c03040481501d16401c101c03024800a0416a01c3c100d131140a4030603041008074a03076041d0403042c1240d010340782502c00210710200748240c038180ea8607040e900030340400c0078401e46886607020300c510303a0003007141c5001c0402150000c3e081c031a40c0d50141d00141e402140b500240c4c0044090101c00e5403086408202d5a0702e003c440c803616 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295207634 1250 295206384 295206407
    0x9030c060f0c1504081b030c121803010204050306010b13180c080a0606200a06141602070e011217030c0c19020a030f053c0d0509100306080f010b011b03 67
    0x1509500c0300246c030202000c100f0785031800c90070400c0d6503117200356417000030792500610001e590b455802c800c1040141010b100312810b4606c0a030182050740c0c20712241c031116034011840d00301040d404080024101c0310800d00010071f45030b0390f41c1c0400c00785000000200003060251500404c2490300204110f296044140103040e212300408003940184035001d002c0c00e010f1150b0700500014244104032020385d40c4224404d1081e106180c0030b00c221303100c00504036500e07601d40c0980d800c02c0035014018030080c14994207a45405108400c4181c102c4040c0035207015030b400c00d13110300410000c04156481510400c1c00744900c20014205601e035840d240d900020342d80079103440040c05050814614400f8000107000254000107540c10030412a0003c600b032404a4044401e2500c030100a1460714210580c0802c4220180151f40d80e654200082c4000f08031102828003014002c0c1039844400140c2c6860900c4a825400ca038480005881020040094184030300c072804808a640c0043c22040000d8012019114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295208884 1250 295207634 295207657
    0x90c03180307060606110609061605030402031c02240903070201200a030e040f020910110c0a030803100602060108100f0e06040c0603060803090a090209030c060f0c150408 75
    0x3100500902000d0540c8034040c4060001d6040020208106802050100324131003041e0480f4110354440503580e8441a00b0380719011840721403901c2c9065075100b50090350304180003d06440c14400303001050181442401d487c00c016800880c09000b01d404010b50b090307000e4070188007144041c17a007034000300e0f16442400e60080c14030440844584204065603018402c2c20300c100220340c0005c2030307400d0241c0852002c0924500c1941801d44081c9510100e0081e110482409002c00b41c483d10103078010780707041c85a000d200c58588506038200c051039403005011001540660895a50f074240402071280420752030b0422029540900300401660398002407014441d1845400000c420704542c6541740900080b420003a06880342d9001d03c0140040025000219404e07601d04000241d6150001a12800341c24002d036070140e985442000180004c0d0000c0a1005000301520b42c1004184005040ca41111001810310080464804501c503408c001110010f08242402c24043c03409a07141c040c81e02c2410035010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295210134 1250 295208884 295208911
    0x12020a1b06140703020909061e0d02011416020a0605040e0c0304080d02070809040606020111070605092104030614010f1203020f10020c0601210b1003151406090c03 72
    0xc0074401c0e25403100d0702218450035030030654280a08010044d401c06682c1612405400001ca4554035005041c98004131001c070510020440e45010000b1404c00c0102c10780c180210b0a40104401d00f800b801010f0400c41c03800404110801740c010b100901425402510034028104420721403250860442544040190595903890380c903483e141c6841e0040d9221203014900114002082040c42c90141c000c50030160780130082d05589240c100d080e11880302d00788900007000c00c0150080303180c0e030300210344c0080030504030380920b4a803514520840014080e034104404004c6030034000c0102c0d5025888880c031b81002c030049a0750402c145849080b04920441c00c000c00810140d0003014002c0c050b030101c1c9050303042951242559100f248010754050b050030307c4c89004200020407200c2c000c8298008804c04025107801c1c0096a5a0380303c110800600752800a0a141c0800070010300008241000016070800100d00611018008040407902a007024410f6110004000382c04042600f070742c0d03000784894441e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295211384 1250 295210134 295210187
    0x3170304080403020d0305120a0603030806010315030203120301081e07090902030a0204050708060a0506070b070f200d0f030509121309020d05011d240a0b1912020a 72
    0x1c00003440399034802900021300c41507500c145600a00506014441500040255990300790340100720b65050100801064a62010030025446035104a600401402841040701c1d280c0d00002d00c0c20011040184001c40c2c000018080000288007102442802c401000020400c50712a2600c5035014020307454601d591710a40c1c415903504121140e5416009002040a4101800002c014400c00c692050151441c400002143d0500c04202ca40545d04440020b0f059103031010b00300c8846240d01442e00410115130b0502d003000b0010032450041a99100c01008500b401c000301604c0300030801c007241c061518240412820b0180401c010782010112803855036100042200c1c0c01800009030802c8141d1440812990030501c400e0307210703130b040e83d200f5039140b014a4184182d1050425044500d041115194461156280290540e0b156480001003116001c15240c0a024089030048442d103a000d50b5002c0c42071892a0b0031401c05014860300b0241540381c0070b03100c070002c4c000050801c00c48104000e500389a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295212634 1250 295211384 295211393
    0xe190e07051c0509010c0513090218130905154c0801060806071e0509040507030203251d1c050307030e24090102120408071403010603170304 62
    0x8580103a4602c250048802a092041800400088501d20020741c40c103a03000f42158003c005444102d03041b00300c1019082c0c01d0940f18001f0350800790a031038111282e00080b072140e80c1c41800525048600c03200014030414603040161500100744100c5210318004d000307212546000c40d03641c002070b10030b2840707071a001d00c2100381040a03c070001540503101d10309800d2900302c3e2904101d030041141c421030000d00680343c40d903904689a403006d0f50108003040c0d80c20407200f010701c208403c464040410341410b90a210810700401c00781c500840b190400230340d0010800103a200e5507c8032020400d4041541c0d0b00255100da0045c0105404100520072204014040c5940d940c5200300d4550395906c0d00c1400080d00080c0ca840b954940110300200d022508099114241d81018600140503811000c0c40244907148103d44440c907034000c0303000a045000750392032115803400b810001d00c020031400f401480c80b00d02e04002c95144982c040c0e50f15200303904040381000481e86000c50100000b80d2400f15954a0f11903182 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295213884 1250 295212634 295212637
    0x903030f020a0210091e080c12010e0109030309051509060a0906180b1b031006120b09090607020705030309090a1d1b10030b13020901030b120d0e190e0705 68
    0x18020743c03004040301e50713070922a8081a288200d030700107898081076540a14010501d00d080e8002d440d55907100302c1016056117041c1c0c0c1c0d078545140100c00001103111500000c1c0782520910001070300441d0b101e840c02410008204841710112000c204e0380f2405007403440c84203840c0d00d4041c1104803421340300e01055040c002242e01000c404a2122444641c45400d45030540747c0340012a0781d910240600070b4213000d40300c1141d00701c074440d803011030020f121a0b0803c001544c02444600108801e940d8440c2c502410361208a48140a100900c00400e281d103020710303000b85815070503080a4083e4105100a0180f42c4030a4102034001c40c0e4000c003c40c200c03540300c61a0115414030069426a8420082692170b018045145140060343c241e4159800881c0140700f903083d83c0040b880b842e0090011010152182c40c0350f80502002d100c14540441c1c002e013a88001180342080c0601c000307450b00222141c0d01c00c6500500101e505600c20b0f02d08034010b2159030b10104103000b041c400c440c8107030650790000f8003642c810070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295215134 1250 295213884 295213903
    0x9041112040b0105030703080301120312020c1f14040f1410050123131a04060902040503063304090606120c1707120807020a080a061107030903030f02 66
    0x440580d11210500148a8440c606407000d441c5801c000001003098280802c0301004c0d43e40181d102c40c5540d03c2c02206080b2840150713420303010080d0000d5038800c5400c40d4001419010700b80d00040c0f44c000c1ba1710380c400307045028500000e5056880d20300c105032035041c400d840b5507000d6040500c5114080703840c20601d1114240c0c0c0b240b202c05d03005c1c4070602c004042c41076010794142c490340a000c43c0803581c3e01810032114030499244c11703400f615603a0460940c2d452904180312115030101542075103034002c00810b041e00e83c40d800c03000c4901d40200c5e05028500f0100003182d032041100c507242c5c2c456002089801c0409120421318841c20704604800c2e040c075112a0403014005620540400149586e00085008040820422180808407040000392090480494010ba400d9000a0310308240342500b0b258004106420840b03111200340540405079840101e17050040c4400c80240500b0601841d21034112003d462805101950500c6000c020950000800007501d515062500404c240110103038907018049 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295216384 1250 295215134 295215161
    0x1106040306021309050c0708070f0302010b03060a0603060e07320916021c080106180b0d150b1206040902011b080a0e03210901051c020a09060e0d03050904 68
    0x40c01c036140380f03455051a021285003000410054a600d0004149031142c8100900500d4050100b1030105103850558403105209000002d002440900444d05040003240c06c600000c0d80d4803001c0041c0b0049015500c2505540009861003034140b2400007088840403541d91034a082808402880c50421702c00c3d240c0d01c1c00000c00309103c51400500c0030001c0c466814140b0018003402412861445039022404120055912101c1540c0c0c01c101003204c0300d441030058803555a00c1500b0002d01c0341c541c0e20040c00090313405403010030449003401e00314004480682c046814140d0400a40c02c0c070a000180c216000003085501264044e00c038001201e440154441900555050b80307602010004100003c0a8049071619001800b4461310304141d21142c525481800b40b076188583c81e400b00e803010008208254050401c2420810201030101400c101c07030308400c48007030f40042d22641494020f140b2900420283c07500c60f0f0400d2400012400e4440d0f4200f005040c814042030300d401640c3c0e41d41090a01e00080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295217634 1250 295216384 295216387
    0x13140601030f0614040b2404140105040c02030705060f07210c080a02090a0312110f0d0e091501120b100503040c090207053309060414010501050d110604030602 70
    0x582c101910701d2440900c0807900b251621030741a904003441c41101e48240e411a03404600d9541c0e1800341600a050709082ca500c810000800003d01d079980e2081c0102d0140a0b4100d071b00301c1d8140300900089400d0030707850300309661007071041c440050800214030746d00201d800004400c58607884025586000601c6001d03039410074031f561855007241e0b2a8000c01c0400e10a0342c0326002a26040d080c10102d11802d04070716041034141d84140081034611451a114007010710b0700134003008602901c54206422600254901d4106c0910594aa54031101c201000401281c44644030f0611604d0146150f06904880d8144524514011b00581190780070321402032010300880111214008010b1955104079000c0b04c0e000e040460100380f220584c804e40301100e5100f001020741c888102c1c04104910f40c1d000c82d0080031055800c49004032501d80e41d40720b00400102e0010062400c0030303d040280e004d018002401a6807400c0010131179950f606900000d040c5e0422881c2c01d0844da8440440c600b8400c503040540703042d00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295218884 1250 295217634 295217639
    0x220b04060503040308060a1401050c2112220201031505132406050708070c0f1805090d080c13030b070206061002011b030b0409050109030302030711011413140601 71
    0x8101000b54031903031183ea1070250300e903502010483c0001c03050049103498024030115045c50f5010724001d18140c20709500b210a070f87c06000702050000c60f0b501d180d140f5180d002c21503000e22480d070002184c000d501004500082510303102807015138095070390043c0c105034480c489003010101c4240160050440503180141e0005000c03189405005030f0340169141380502003070b010302444000d6401c800c1c0c4034107a5501d46801d03c140c8500320b440d0400181503500b56101c00002a0001c2c0c8050034100a111422409000c031a9002d986400c90b18001c000741681c2d046022035048050340b04040030ba04c200c0040702240c840c4000001d446000c1040e80008201446842c140308101d034000825030710440d030840b0702480c80141c4420407030903145201003102d080d1480802c4484090f020350030401c10300310041d10001d01c2c02c103503894041c00c0d914405415004258000103121800350300c4150000012114002030051040904652800110090203054070100c5400d01804211070101d081d000981d80300211115543c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295220134 1250 295218884 295218887
    0x10120215071401020a23030103030e0303190f12051510020c031509070f0b090906060c0a0f060e2a01020a021009050301051e1303090f030f020f060c03220b0406 70
    0x14002140030f4041002d0a41e06d0800c8514800d004401d100b03004941c50450346960f07402c0c6d41c0c1054174154240c1c140000c0c411003071070f2840250020140501c0307540e00c9200c1051070001901c001d10b00c40f10702c500c1038189010400c2c0c0d202c0f00f54040013800380588484807500228001241405202040320380e1502416180701c0c03400202089040c000c0c2140740070b40b030403d5072790080310b40c445015114240705104180b20221040c40d04500059000f40044c0125280c0018074541c0c0d801c0c15000f500c04c684510003a414401800010300c01c601701d035441c000003015801203245040c03055405d000e51300c1042032134104400074142d2091001d10f8409030b024101300740010842c0000f0f80008400d00039a4025071800340054229112228165281c2441d2080f50f40640c8506111140b03002c0e02d10030603010b0002e01400003914800d10404c100055000b014480007250503481004034460441546a20450060000840d020fa001c02102e85030a103441e0941c000c10048420f075101a0705a92100111400c0400c00041e043e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295221384 1250 295220134 295220137
    0xb07031d07150c021f0216030b0a0b1e040b04020d0606022506140d09140d09090203151e04060321030c020309100e0415030b1012021507140102 63
    0x540004400b100340c1d00c00d910301151944141203020f0b5100c400c1e44003000381142c840c17500710500c28903071040c1d400700000d001791a95007415990040f0b80d601100e00400c070004443c1e11a96980050840c1d0071086a0101074407040800c01e465059449140e40b6000841d41c0c1c0e40348d604039480104140000d100b01960361070065141c1c4c500c0005841004040f0300d504003059848154041610850340700c070309001c41800007800706504003c3d10203240d80d42c1c5015a00c0172405c220741800340155580010b03d00c59407042e400800c010045e904c2040c000d4014402d11840c03204220006882c1d4900751019490310804101460140c6e9400a84540140c503000020081c481100c0220a0400074008140361505841da4110101c0303c1480766040140c1080c0129100c03460140e2800d4010701e0140741801001c108400083c044a51800c050346044041c507204000f080112542e65500c02d0040300d1010905281a0322030800c1c000c0034500038401c0940442e04e103600f22141003955102c0ea00102020b0521000c0541d0074000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295222634 1250 295221384 295221389
    0x4080106090225080703081801050117070b040815091213060305090a020108011707051e030d051e07031b0c03170708220b0c07030c0b04120b07031d07 66
    0x40c032405603075407500d81c15280021066194418070301450300440e6101182c0468014100b23081880c181c030402c24154409002e81c5020313250b5400c440415040751745215180403461b5100c4600400180010000c1480c049850f0040c00c00b4411204c84650300c400d130f404e08100c0203165900c40d1795008a0000324540000700c015043e2036494400300b1164407115041c6540c0d01c1c2188000b4005a20940140030301100c5a0700003025120b442c04942c00c082d2a08002080a0302d60003c0051044a028103442507150400100c50f00b401b981c10030718075014001c0c00c100c21581d0a03000c00c5090707101c00503580b802c241c030401050021003481e0401c0d01c0d04001c58a003103003107241c0c0c504c010790741500c48a883c00342081512040350140b581c8400e103107140405046146080500000090102070742d10900001d9110001340141400d1a602002e0700032107043d40341c00714000b0400d400c41104003100b440140301c542c54021203800429040917010099540c1c465044002d8035500184c01c0c045030f015404400702c3d95001908805 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295223884 1250 295222634 295222657
    0x2070302030a080a120b220b06070b061f08070509150301080604050106050f010e300d02070905040b01061107050604120c152a0206120402040b180114010203040801060902 75
    0x142031310301d174080209031468024038a9100c0080558520940d1130650703024034000c00700c0300104061701c0000000c0d00030740201905a0b00d58119a041020501c6c00c9030316a07152140403005003000240c820310051502c2c000800700c10034050001713009201590b60b0b01610341c2c92201070107095625a11a040581c03106000e4a04895542c03c040c00481d081c901220810511070040e555a01021040c00400a484001d410a0380701c80c112103011003141c06d21a12505019005000100b01d14880d070f05009240200d194440b0900c145813100b0300000030b0f00704254a0450f40d07145095880900148501c6090100e40d500055001900080000b020700070755554109150154a01a000d15560b0020400d558920300c01a40080c0600c6c1c1c0c030003c0e441c580d449401c100d20b11205c1c0c1000c0d1011640c04194180d01606a0045642c48081000114500340c051007250441c107460340c0071107611110007441a0358042c0038144510001c1114a400380e4130802c29a00184400c600a04c406582c90005400940c400c40352143c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295225134 1250 295223884 295223897
    0x902030606030a05101107120216140904030309030201150303110d05030c0702060a09080706030b0a08010207210c05060103060c0806010801140d0213020d050109240e0702070302030a080a 82
    0x1d441e403802158004109400c0b0014120091080c003040c0003c0a0036041e400b03080200341710240c041600401851032210b242d40080100e80660000d00d003000d42141d2001105890714051502c46032a91501d407504964581000b2440407254903059024145c14041d07a61310b01d01ca0000041032592002c01540c0c003051000648080381c01415040f01d441c032048410300030607a8204070384001411320710010141d0303e41078542120216203c4858504040c007591040300001d4039050300f020213203445c0550000410085008620346001c03556078060296094042240610032107039102c5080c0d0007000031001c0e407a4800103036201903840303282c940001e0038004014070002c0e16180c005140c550048130301c507040e00c4035074007140000f41c0c140042000780210990203e8000828690400209005002405d01c241c0f841c00007203400d41c105400c00342200d108581240d40052841300301e0008844803d2480159514031159005e950b035040740507442c000380381e0300c0203426100d00d603019014803004201401c4075025555500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295226384 1250 295225134 295225141
    0x4050d1e0801051009080709020903100b1804081306261e09190503180402090a03140f0a1203061a04150c150c0315080d050c0c0603070309020306 64
    0x1800c9001805100001040402006000600c3c1200002da8440301518200e0702d00e0b80c07103002c00750609205d94810f2000d103402040001c0c003450188401113000080745030030082440c0550024540d203102c0d19844581902040208050041c81c2003220000d01c020b00700a28860b5131003400421750000128000705c1c00c015440d06180e0001d001c00840d0148102c0c45003188107541d00c004101c12054050480c0c101489850018080341e080800c500703414a0084003d0354a4000b5a8183c180c400380d072070135940c8100c0c03040228010690795915042c054a070400b000c40b0300000104101e0303151500b070b405061880c2c0320711030345001000001941d88099030460b83c1e0030b000340343ea0382040a2541807081c0981c1c4d41441c091209014603d0211142c04880b0f9251074032804ea6982034580e4901e56524050100484c0d0b1139003221405d05400d4042d604c120b40c0c40050b201800f5180202c0541c0b1010452031400c200324000950a030012801c110002490b03a004140035928185544042c1c01890b054200b00c0c080e001d00b2000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295227634 1250 295226384 295226417
    0x30403150504020f010503090a0507060903020414010605030a0b040b190f060804020d08070201180906091512030807020703080d06050411090d11060c01020d02090102011b02030406080606040e04050d 87
    0x19a4003540d0b01601d4000c04c042404010340d025040140000071600c01c2c00c0074500891000c0103c040205066207600380d2140c194010310040c4d400f4503056401c0020030700010401160702804403913211504e8040043c40705840380009000e45803240c0800e0340400c03a044400c0c4480c0035100000c0484c0c400313501c00840b140d5201c9041e0f030000400c44010358484580c1000c00c01086000004001003481494942c44500004011600c01d240540012503140d5540c1350a2004052510692142c9107c8503d40301c0c0c0fa0f0301d044407a5120590f0081c0080403c401240800c0341e85008110750009150f012041a031039060300c5410600501491283c64801d50600c00811040071200003200c445501c094003640d45860180c896640c00e40a42c1a01504244104400d840400083c805001451165100503075910121000242512005030394101644005c0e031034441803640020448003107031001e080401c01691000001211402150b100a2a4190400800c4100040880c3c042d0f09072070036458814900158111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295228884 1250 295227634 295227641
    0xc1b061f080a0b0c0d020714060a0612080a03060b04030303021206010c0809040e0f010e0604050d050406020303150607171e030c0a05030a11070b071112030a050a0f050903040315 78
    0x80001035000400b6000200302c0c80c03540144e0001010344140e01d40001480e041c4102c0c0e01622098460075440044010f0042c42800481c0d00013145603000e11415040c50710f0412420141c0d000204031b80030000ea4110918000d4000000801405854a0301e0b41d03a40d05020f4003950003881c4803401a400d900002d0000d41c010000e2242d2160030501d0941492054000d210080002000b50003051040c201d83c074107111024051444510710883c054452418036141c428a42007026908a080c048140018880154008152603002d445041d0402486002801050701441754003030140030405010300c8000080c40c02c000502c0d9000901c4251410403583c2c1c074079400d150005452a10610004100f0014524400c3c40a15001000c072075000885101c1e540152206900c40b401c11900d80e0780f84410881015044a402e080c4207101c2c9001c0e0001660a40c4880349511005180032191542d0ba4003040b05410141e102c01c04040e0702c10b0042005003001d0340103640e02c1e0494402160124003540c800ea0b1006450301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295230134 1250 295228884 295228889
    0xa03030e030a0f030b0a08100b130902060307050a09032f0102060601020304140307050a15140903072601090309090f092616030e0906091303080c1b061f 67
    0x180e07000c00010f080c241c11009003005900040d4403ca51404c0420358100912030101e005a41d44e2000a04001d60400c0c05100c0c100b508005610794501000240075864010481ea4031807800e1402d107650703002105081d81c01900681000d00140549a01c0c0baa0070140008042c65400001b22030a0b04140100c0049a6810003104d0490042e08140400c000400050310040c1a11400409036210141ca400101d0062140d942c8040ca26950811201d010740760001503001d01380000001d45840c140e8100e000c0b0b6038880d0180316403802d154070308080d28012400940840c3c6c407204030b90001d100e04600c1d400c0050250070940075541c000c901e080210800c83c0054884d403000c803580110000b0101c0b954140c1410b140b82480c5510480c01c07420444a50b0f0001518a0380040a00c00c0d22030b8841c07484800140480d0000041440c1d00034404241800700d4900e01070b1210800c15803529000c0c48030341d030310100680a030048020784100c941d19100c80203c0e205c000310b0103e204901c150318440b0907107203051400c1b9060b039403032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295231384 1250 295230134 295230137
    0x90d0f05280c09020310170318010203070c0e070e0622210816050f03031509060f0d030509030118053a050f0706020304020112050c2212050a03030e030a 67
    0x4403c01c40566540c02866010407034108a200d0396940d864171041440907500d0403413940d0000a4801100c0d890383d80c03003a1410000784015070409442d0f640d5402c01d444035021300790f0b0b0b01d0740d01c0000541ca584220a00440c6100103440c0b0361f202c0e42c15011040e0104000003d0324031108000b8000701d112905040d05031001c8042c840c0d441d40d2100f59888040c601d0740320f50000c50120304403442000103d0001c00500c061003503454010b6569180001210303000300810100d2901c1140030740f00380407207542c5049000143d29822034410510003070340d1409845502c608803101c0e0f0154200303801c26400c80c29070305182682d9401003051b10340c18149022903580880c40e205008200d0401c140a01404144030381c0604241040d40c18002c1c40c090003030036140324030b800c4080c0443e885500001004219644100c074800e404403511414056801d0000440c8101e00131244008440344011103508080360b40c410b480c04c000d241200c4041450525414115203910442c1c005501003800c0510b4995400b0002089a80c004800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295232634 1250 295231384 295231403
    0x901051203090d050705090403020f0c06130308090f0a080a03030f111e0c01020f042c061c0b0a020c0d170c0d090b070e01021603050a08090d0f0528 65
    0x1401042524042410244c1e994456143c000c40c0607251940794034000ea00030780081902c1c0704081003030791401a12424141c0241403e01a000d03100d1400c07003101d01641d50011440740c940d610b4401060000074107510607075012410080000d24000c000c240f140d0243c0c0a55001d2025041050b0000c054a400321511000b4110420444580000307006413140d00c454018001031800840194190981c1c114062880d01c81c80002401c002050300340d5801c040700d084400700d40700e500c00162008050240002e240a003e00030b1800300200e040c1001074600d41c0b059000e24900d409062404000d030080d0400e21082100d071280a0b2403000460040b81004009800c000d0f140d6600d60314121840381ea5009a450519034030b407629000000529800821031040000f5952075400c071140c44002450086a0f03e0034040751541a00184003050012440c40401504030202c0c5c1d80d1100190003140d80b51401c2031024140e48030344084401001008212614032114802140d0498802d0508010b0b110400703400040440c0712 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295233884 1250 295232634 295232647
    0x11040915180b040809060d050a060e15220e0708070311010804080306010e1305040b041b030c1e0b0a0c02210604020d02040221010512010c120f1116020901051203 71
    0x1a040c014224805d000e024981420f0035010034a0948600307903000c61481e9110305050280b000b038a44500d5011500d49440c1c50300060b64004191304e00382d0840991600f060740f0305211000e50154120709140c851980850340e006903901192511800240022204a032010f22171100640c0308840721fa02854000040519603141e0100649032400032003e100c1d0000710350a1010350810152085911640c020700c0d0780d0090f454a454840d48201c2d03c61491400c1c1d410540307080c40815104034420342500d90355008100340010102c003480528501c1d600c04030b14103500294940d0000c0c0d2049420705464400c1c0d0f1021140b8070081008e1a50322045100c1031015806180000c01510340921a5000355001900052a0500e40521115046485c00c0c01400407000980100900d05206c0a051011a01a4000c2000045115000301805c0d100360061800039114880c100000d0181d6010b06a0702c10b41040d11940c412402c01a00b143d0405010140d101d0a10000002003074140f44001075200814403028502d044c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295235134 1250 295233884 295233893
    0x6060906110c0d1103010f050c0706091e05030d060503010b1f030e03031024080609100b0415110a0302060109090812010b2701090501030911040915180b04 68
    0x140740c128102018400c0400741c144a403621420001c05074041d2803c24030700a4164281070a485c0c95050000307810f40340c8020026100d01c0c1606990380140c1c0001c000c940000a41410f04003400b1321031042e106680c66009a0041103030000c000d20b1441c5002c10180b103042d940707000305803c840a820382c0c650401c1110f448101004520400103650700f072503050001c1c0449181d03030322600e99001222003208070b850142c010b00020302c00c9500c910310b080c02c0e49a1b004590307a038a40700405000000d0145030080a080010400c601c140c0e102e680c0c090007000503103580b607a50382c0583c039404003840006c0700d01280d601c0b000c203014040f000c500303012000e4154000b81440d910b06104400144071115058038203000500695040d00300e200070f4a40201003110748503840300360401400b401114a5105c201c50441008100807482c1d8108420000315002420300007a10135080c00c0034410100c3c459801580940ba0000541c20060880b48844039205080c00400841026000c5c08040200400025059500303400004000a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295236384 1250 295235134 295235147
    0x705060906061806190807140a150e13090c0311010206091e07050d1211070f030b060a080a0506040b012306090402120103030806040b010825110706050d0f06060906 72
    0x2c41c041c1c01000c40c2201c0701c00704905061a6042000c0a4124050401c06200040210081720208a070101d80c03840c0741c0301002503031504000c429424484000c610710325599600f420ce503000b1035000e90900510320320789011001c00c41035010403200a002e001c05025a94400502c0a1245c0e9a0744000e007400d4550012440d0000744048465070103104c0c501c0c0116060319294800c07203003a44151900c0c9945098208060f2500d20349a00801066111030b800700007080344042000200d036040200c0f0f01c0541c5500010507100010758108804901c211072440c001c02c000050910701c114003d944011943e621103400c200020b42c24101107000c90340002002105140440080210201c003e20040c80c002c00740b071400300c800400760f10690105070082c00f045404e040500418500803000d2030f0030440d5140115506600194050b58441d4070031003807541c02e003100d00648800500c00d802c90122008182c3d610f43c01402540200c1114441c1c3e03003880f10001e001d005901600c42684c0b56611840007440c10080d080712034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295237634 1250 295236384 295236391
    0x10090506040f151104080606010201090506012c04030f08070f0c1e2a090b1309060b0402041815080a0209090c04020403030c02030c09150f0310020a0507050609060618 73
    0x210400088000e4005040b48240310b5200304c2142907070b44403454407441c1424a1030041c0030b50b0669041001c8100096408104203054407991000702c0c01250794108410344030b00c402407004007203d14810a00c02030582042d41031014220300d69405001d5507401e00101c468030300c01c0e545517010519004901d400145003102d40f0901c4020160b481c42419940d46a40010807060f20740b51440311002414440310702580704000000d408113400c180030103207681c03010034548000a40c10b510015503a550810400245401841c1c148a0040055482c0c2d52565482c8898082c4805980442032824042654580b640c500c440129038000303010300101100b940074020f03241e5008022106900900080c809242d64501c09070000c2d5021340d607101c024500394418589048030708400e1601c100002c0c0104000000c24200c1d00c0d02c2c002042e02e07141c84000702640441d2520f22040c80980c0602d001155032003446502c82c0141040ba0701603801c548440d11000038280d200c000540c4c02c1d5410500d20b030000c900744408030b540c81d6007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295238884 1250 295237634 295237643
    0x706030c020c0a1509090204030c150e0a0605030a06090b06030606030c1204050601180b030709021803070b090a0501050a0807030507090806190b031207200a080105070210090506040f 80
    0x94011030100090880c0303d41e80009554482c40c1040a94140e4030002240c041c1000c0d00301180341c981140c61780c05100b00a4400d4410148a06000e20482440f4954180d5003c0001c1c200180040e00c88101400c0c0d60800c50300080b0081c5441400111044240a440c05034000644290700c1d51705c503402400990343c0010080c1892540802140c15800d807a2150103102d280640c01038003040d418641900381803592079800030754040c281844410303190b40c0415444200d0780444d00059030350b80c5200b04008410320708803440380d05008034540081c203a006040105100041102e0300260581c84900543d142d00840806800050113500000c1c81240661f02c0f107504003005080041c00c465903022030501d0035904448165010303001000040709000140541d1654080480161245d01c0120302400091f0103072540241810b44684061106944070842c190f14082001e410795850340c0d1142540d0703001e00700c2030341e9010061040f43c81a5000e40c1052050003075007039004d8098401a211602c49541d071100d015010346 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295240134 1250 295238884 295238893
    0xf0402040209060d02041a040501080708060301060906060840020d15140711030909041502040f060e01020c010e04050a060810060e010e040309030b07021c030509010f0b030706030c02 80
    0x1010f5070740c0101615030b12420f00b0000da80c0710300307000ca10014040c0f54801c1e05203a00302840144800c0e0b0b00018003030792081d42468200e609540c0e10000030b0142c950380c1c5c40100528680350006c5a0107501c21150b910038001c0c10412503e403002441c081c5070b5a04150b50300c100d00c0c1c000c41c4e0408170090203128032658040c00104501c0c1209141e8881143d804418281019103075a100c0300d19884a4500107059070040d000d08011241518182c450350700c0e48601c0303000e103216244000024041013201d0300011100558000d045458907120010741c040000d56024507004104c107900400d51540c400034a40b0000041039441d840e00450340e105001c043d007009003400c1d81c1e264903a00f000c01e502c034041214042e1051414000701c3c5203450000000c02007101038000c002607135010b40030800803e80007911070003120341c000468840d5030381c0c66400720300307050700076200212154070158101021903143e0007132401148804000c1000300c81c009480c804035041416095099041000c0401089009038000460300303009005a5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295241384 1250 295240134 295240147
    0x50d0512030a0c030b03010605010e01030c020304030f0c0f140607060209040902030115090b0306010e04030e19090f0c020303090c060c1525082e0509100e070e090f04020402 76
    0x10a40d604200c40c0d10350266a07403608802d40c41e40c58000c0d1050010140c00800c495402d080001b403010410300010b9061540320b04558000a108104440045420840c0d0340d03054045403074903070f40510062080d824003800342e030030101c0d03c009190803c4c40400d8005011074503110ba80d03907035403000c0e412070624640c0c05559004094096142806103c0c2004240f2001ca22a5401d01080b2800c4803d80f440940c003035030201c070041c800c06502d081d0843c2c010b030f050b0400306403401400d00001c0111407401d00c0d17004c13281c0c5e016200182c80b002d01c1d0402c5500b00200c41c070510201c0e9910004030381d24041142c4005540d0720502c0440c96038281000140034454101c000c0d51000c01181d0744407a0f070030700152800c0b110410494002d100a41c448251108041c40514011005007011095442c8131040007400940b1800e1403600614482e100301131002c01080007800f40300451604032072440300d440c40c1307118411074402c40368005101035208021032503069200800b025016194001d1609010030b00500c1260010340c00c0148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295242634 1250 295241384 295241413
    0xe0f0a0905090c040f0c08010308090a03050f030c0d0305070522090e0a02040f1103150406030b090a0314030105101b05070e040c06080c0912120301260609030301050d05 74
    0x101880b80036280000c110080c82c0c1028402100d0b48078411200d55450450b04e003041c01c4d800022241101d4105030030360341340c40c2c0040008443e1700850380000e2203031080c001d10034210040070001c0d000d04803244d001d8800d90741182da010741c243c1e081224604c0001e40304100700d4240800c941920481d403007020040150705500d502025003211100400e50881d9440361500e1700842c03600c7d008002500003408401d21402400841d20315403400094103483c600c03891146c07000604c0d15182d0004001f150410506020390401c0c2d1101626201541810780010b1a40c0010030074059501d001c0780d0403a10003030074101501d00c0c003010444605501c5d0340901030601000c4900750104004000490203401c00c000c64240c1c43c10203240c82402e0341c40c164040c100707004502d070030070800e40c1d4000183c41101105035400d20080e0700402e1410b060a0001750400b01c612004000868862011410004189110030020044992044119645100445000800e54420001802141048160b030a1031501c82d4080303c101c540b4a210 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295243884 1250 295242634 295242641
    0xa030207051614040e07060905121207030806091005060d0905160806010617040f0b070c060617010c1b030c0c0902030c0d0515010c0623010b09010e0a060e0f0a09 71
    0x4400340205203c100030496282c1442015555403c1c08020a5081d2601801620044940c481c0038230a686130440a080217100380110038002c0720920344207545560034035010303021201c10b0300c845000c3ca07200030025404030701c0c85a406064a1000b00007604010322000301c08050900150102c0300b034001d030781c9160b600001403101c000280c8960f4000c0e10180d0b041c4a40240111007110700403207624095000d2001060104680b44400c5422140250095682d06d5054500b482c0c1c05400400c000d107407100004800d81020241c0081c0d5014400900144d20480d4040f034030038050110340d50304000c0158400c00000e000f051042e110702c1c81011484c800a42d504194012078000f104e01400c0300c0c10009034000050321b18494141d004002900b041102a40070f40024945811500020b01055680158205070403201c94080d030a40505991204950f844040454494000300c1105010405c437280840c144e181c424880d10030307951a43e8925880d20b211404001e0098080303c001500070305d544c40b000c60f00c40814003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295245134 1250 295243884 295243889
    0x160201181b0f120201030e1b01120b21070522090606050d030c030906090312140d0c030609050a0b0315070507080703020618030307090b07060f052403030306060a0302070516 76
    0x108a41180c0f103d600014041d1240f1a58030815a0804101480041d0800f11411010b550030f00c3c008010007007100000e0000e209901c3e0540c4d100d140b605146e01401c11070300c250350020340b05a0940d164603a640051103e10b651500543c0b0301c10381c20a0140c2d20011255000c595918013508000c28425501c0000c02c1c48400302c81800c0e800103202c00740200a00d9003005c80b40b00203040c541382a80c103144c80d42c6c442c1580081c607000c6460400a0b441e41c81d41d503010320347c0141c580f41d048060301081400101100600145814481d9245150402000850000c0c1d1032080009421000d07014001a9100508000c00100014610414000c0a00050008c0b0f903840000d801e40910a400402242c03d014500c401d8900c6401490840c0754810010010940d5100450303104582d6104801500c90f4640d203010b402078003648101010f101e14007010480d000d00011805162100da0511103442c03c84800241916880704589140e00840c0400c50403800620036402440024003c1c0245c801c4085180c0301d0012840066 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295246384 1250 295245134 295245149
    0x10e150a0908060702060103080d05060102010b1504030b242b111206220309090e0c010801120308010b0315031f0c080f011a0f0a0206160201181b0f 65
    0x500144000b507010402c05400c4400c0340003e0482c1d40c51550350000b1803082500d8502060385410118540741d000350000300824100800c1e0b80050310b814003210250350018442503a50307181c00c40110b0003607450102c1c03180c0d03100312490400510040000c2130044903070f00c91b0654801c51a04200b1883c40c500001800006030740715610310356040d01c40c0020450106040043c04510350402400d002500c04030b01001458940b406880e020b5079400c500381175410000315400000b2042c109183c070800300c480810520344901c000d0b01c81c036a65980321408081c46001ca40002004030798020014803d11071554055980000d02c1c8010344602151140401c0c200210503000e011900c3c03010403044150840c0d4002d1040141c2c4a10304004140340c20000d14141400610440c1c50f204202d00c4031206c03190401e000c0310900081c508810b595061030300d400035540c8000f240c3d80c0c0b403401c1003038240d102200d1041c0110042c1d1240c3c2040e01044220a49030450302d004411040340006090030703000245855a40403a40c000c0079032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295247634 1250 295246384 295246397
    0x510050705071101050a0915270e01170a150e010903020606030c240c01091a09070f030b0708100801140117010203190b03012007020a060302090d02010e150a 69
    0x2480d10f10341c0c20700c80301400c2d414400107001c2181150f6104401c6803c403804180032a80b0300c11418400e8030a0f4010300084a1000150016140b070154a00a940d040781c555802c031b885141e0780d403032a5400100c0203814100594100c0078450000c10011900c00b03845142413032000800710013180d0064210f601c080d02c200d015800a0040106a2809001601e002d1506550810070074a08202c1c00c010951441002c1c0603012003c10310080d200002d6000d20070040d40700840f44400480c190340c42008850480d440714840c1f00300800807071840841010b05040782c2d440f6140d410a500c80c850181c4404100800c0315072401c0200c04001141c8109000380c0d0560165007141c0348040d41000341ca00a076101d94006d0344c00307031ba004206001c83c14a00c8002c604185d40e800f04001402e00c801000a0b001d03010182c01085680e000454008044580400414186200311290442c00756a84c1d42038082e406a514507950000302074402c00051750080340c0b01c0300110001003038104d8215000e0784110807504041c56003000a9003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295248884 1250 295247634 295247647
    0x70201050106020106060509061c021c0501080d0504031e02041e0b120c13060b03040c0503010b01030b0f01050a03020c101b02030c101109030a030f0207090b06040b070510050705 78
    0x1028420a4058152440207204290404001074047d04c40c006800d40514000900c3c0c0e10701d22010007a0301c504840700401955500d210fa9640700c4080320064041c7c172507a181200028035000000340c15648460306842d4036050602c3c544600074401030301e6039181401840709480c0001a961072281d13502d101aa0001d2444044550b10038008896500480d5805140800c8a01c08892000528940c1d8102d0855905095040a118210242c03007241c2c88010b0b400f0000c018441000241103001c000d03140e01b80c000b000020450001182503d200194007600003800a00c95500755208400074030741d4085034140540790a10b00c00350030b40761000c451012085143e5a05480000041c10003034211500e0640c4004c5040c8052100007544410f00445240007041d07903456081c17022079500d002e4504810300141611008038032410b000c5c1c010a02e140310034006000f015400308885109124504400d00c002e80741d94206414907600c040203900441040d00e0314441c1c07554040381984103000d000d00c940159500c00745c5420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295250134 1250 295248884 295248887
    0x204090b0d08030114030a060e3f0309120705151b09130603060f0c081014090402042012310303180c03020307052b030e1807 55
    0xc50003089244240084142400400c0d2410242d034152101003445405085c8401c0c0060b04d04001104024001c2d810319042801001d404070b0269107080c4c25007451061841524041e03400c00803114100c142d40c1d014441b030590b1881c074100c040c4d0780c04000c4004071400302282d007950200c1138000c80800c484660004841c030404074140b03503d007500034868203050483d082402c03090040c50300640030f0700f5000c0c030f202c2c0280c40d608201d1a0800d030002c0d600020100910407d0b40741d6900680461000900407805180c046190806410310410494407054a80c0c038520b60b1980c1004040d000180c4141e921640740c4a4080202e1046d01000c1000c06460a007540d541d070f03407039040e0559928014542028520300d1094001d05902d1803410b42c0c141c07441090ba554240045190682c0100304c403002075220751003445401000c0044414400702528021011900300b01c0d40d0390100aa001e460301e010300703c88000300c00b03c840c040e240c805613011090301ca42030414150000c1c001264080881c82c644141035080b56040c042c40c0c0703 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295251384 1250 295250134 295250141
    0x1080919081b0f01111617071a071d0d080306120613030806030705100e012a0201020c04020f070201210c03021c3305310b0a09050603150a020409 64
    0x1c288416040ca00035840010f0030861082026141807a000187c52550001038220341031035602c14440c001040000c4a0100c0010013220000003254000c1c1c442e01e8a0100c0ca90552038003203008004100c992400d544200e42e58202500040e000042d003544a803a24005005462103506103402a8004c1501800e00501c019009480d0a000f5001040c082c0244d0300e035010a404a4480c038100b09110801e000c00485440c0030301c020480303040c8050103034038003445400c42045043c54000da084a100104d01c508001c100e1064640900000c041080200d0065000718602407540c5495078660380d115910706c008200303950145143e000000d0f4006520361700c2143c40400d40c40034403210300c020400c1c2150704080107010400510600c00840c090050100e81217429100080600005080140d28001c1c40a400c0c5c0c1e0701d641c0c0030340d40000d184103516601c0e0911441c400c6100c1804010300d03440e211880e04407201d008040180a06825029100104000d1340400c54058001e10b00c41c038006966500e07200d40300007207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295252634 1250 295251384 295251401
    0xb030717040b1b0c0628020f120c07050106030501060e09010203071d06090a0b030403020f031305040f0608010c09140f0d020402030907030f14010b01080919081b0f01 73
    0x395000c040034007001c1005816859400110b0702149511503815001d85105406000c000828034401d5108000102d007059081182c01140010814500d41201000505a00404a50f10039070b460511074074500364404034000d600700d010708114501e80b0210f0385515003511090b400554003603440b250b00300303e0789103555100d55012214070021400c0d42001c06004014050b0240007100da040c0036203d01d00340380e030b801c4116a04080002c000c001255034441c2c0101d9107410848054000d030040800c217200220b07001c0704695005008504403201704e400c01041000a0407225001002250740c0d0300d012803654801d1161840440e201c1d110002075624080700040c04c1010385038980e02950540c44800d1040e00c41c9110004246d50455001d81c0b250340704082207141c00d625034805001aa00d80107840148a00c60b40b420380034545080007400818421001581c858106030f41c45010b5500c59070300001000440101d00001522a5075180c0c03030a04084a591100591400e01420a80150800354401d841c24440c1610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295253884 1250 295252634 295252667
    0x702060604060b0a1d040905150a02162618030d392406090603111e0a091d060421020c060d0902031504051015030602040b0307 56
    0x880d070f04060411a00380503010010003445044500c5c02807000d4180302c10000d01e540a001005158100e062407540c42102100d080c0c0200300c11404280640c203103008540300b503651100c04a2050340381d0b540c0c550000402200f41003402c0501881d5004c01d0b080b5070300030a60303080395180e0300e0036001080042500302140e10340e000b0180100118204014861012540c4850300700c10340581800080c040d8910015200e503000400300000081076166000b581071017850300c6d0140e000c041002d1174071000520104d80b80d40c00041c2039885c8075440d0307024900c0c2040b01400c3c1c0280c541d403016283d5580708040350020b40150400b030845a101d01250300315129a145541c845540d07030006106500303080e190040c4100c407181d0312010072074414004441c072a008100300418101d010700f0729503540000400305001021100300881c400d001c2ca80144802c001e003110038070f00981d040b41c0074020616441000701d0091207415411800c050b01c00d0000000700700248003030402840c40c1e4010782e940c1c0c940600014540d00a07441d8091 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295255134 1250 295253884 295253891
    0x602060a0507021213050303030a0c080a090b0f090a120801090e070b040312090b030a06090c020c1e01030e0304080102040305190c030303020a05160f1112101a030a0b0702060604 78
    0x80d034079800195402100300c01018070303a64001c5c485103c6081c01580c0c020940511000041c45011049a40a01c1c02c0c0c030304955554640792281c1c1e4018054803028070014040e90320000101d8541340081540d140c008070408121440304802d80d68141000c64808035132404109208010005001ca0740203034421200c00300080c14505040a00082c1030b8041c0f4000549000c000300c090500640c000c40500000e48100754040d6128601140060090325003402000c11081c00d0200c02c040c003d0002502180300000201010480c0304c540e641c0da02d143d403009984e40e04254841000c11142c0e4810700c0200058402900050b07900c03800c40c2460b40c60b041100341d24900783c0141c8132000c404904403114400030340e80c2c18039015a480c140c00c1d00032602406420b52403191014850668010007900b030b428054143c1c41a064101203030781c150b00f0406221020b0700d0142c1c06411060310403c1c0c100007580400c441c143e41602000e00c030800140071a10704888024115140707011201848903035134042050aa0200084074240f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295256384 1250 295255134 295255141
    0x40e0c010c15140a0e0d030209011b0507120f050c0a0b16050106181a0108011202041d01022101050906010f030e0a080c0a0b010b0403051c02100906060602060a05 71
    0x1c0603402944000392019481260b4500d2611032a0029414035007001607011190414510140c01054007140081e65413092035181c4c034215001e8020360b0104e0340d0507166088164230040e4032881002c1c01800482d07850181860204041580150b001710070303030182d07552403c4c10b8811b2820b98981400c107901c103882050780b444204941000c00044074030300c0d0340d558042940c0d01341900e000784c0544001c1c2c1201211641e04011111060b20310742c440507009101c40c540300000b00d42800191100b00083c0030b0a00180c5503c88140c1c0541000d0300500d00f00c291000c00c84200301c00248065007280c0001041c160900c2c0c40314400240ea05014402d50f001d0001180c1101483c1001d40010f40300c90440d04601050685500140c4c809210601c82c5020480d042800d031076480a070030401c69102c001d080000c541080c034410010401c3c140c4542650160b0f903200e0010514144034151311008030040c5408001141300741070528900400b031780503140585200d1400418102d007001000790401c00300030580703007040c1c2ca401c040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295257634 1250 295256384 295256387
    0x80903120c070c080a3002060106030b0f04140402090108010b06030610020a0c0f1502190311030706110409061401120c050918060901080f07030b1003120806040e0c01 73
    0x800d070000301809950769614128a00003804400607400820240240307045101405a9617168009010384644490700c240c40d0011b4003100d0048110305500141d0214005110444c000e0380001039400c001001c0c600304101210000302601d01c0100017142081f00c0c0401d001c21410200350319405000010000d0041d461250041422030000405040c455010403950f00801402400b825881030342210352060007135102c074661031403848bd034403d030701117440003815908c4c4451011811442e109200c100c0403510880a0b1001c4440004409912016010070007022000462611035401441c10720710340f080d1035501c0c11807004201c51550780044180c22a04403400c495030307400030501401072042d9600013600b80132000c0455450151034855904520382c001043d50031000d40c60801c0c8100d84c02c803108045683c1f1040c3c401c1e00c03200007150000065015950a10000c0c40a10342e15502c41d903d8019035100d40d990340c949a824055050280b0081400b42040c0b04179820a80603500340c050303d4000400c01070218500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295258884 1250 295257634 295257667
    0xb030708060c0307080c04031509020906040605090a0e0304051002010c09210b180307080c012f0d0b0418020f241612180e010e06040b01020a0503040f0501080903 71
    0x2004007084011000186c2039a60b0b0001d84000d1604205058084001c58a510000300701d0178001381d03c500390040c0061024a05800340e9070980d50701802c10790306521040102006031205c03441c0a4400d010070310011400741c03902401483d403681c91387e0012941c0b00701c001001d0203108083d0009440d00c3c1c0d2a400d0700c00d0300301c1500c0040300e400d039000c180e080302e40e81e0341c0201520000d4605048081b0f40000180c4030140314108000c1c222080c4101c0c020451002506058036501e2407015259602401081000007210700c0b44001e010480f03072040002c50821007543c009421600040a02419039100600c400300b9401c3c04200042c1110040d10002c001100010003194150800c600000c01e1840001304030603103040d042288280030354030506520300c00c0d1040b180600785202c00e40d078000c210345a81c88002200e02840f09854100c8511a031018415152602408040c00f4401e040506510a6030441000507804100500c0100020b004106055051000041881c4000323444151702e43e0052200411602100c1b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295260134 1250 295258884 295258891
    0x801090c090f0506070f0b13060501050907020c13060503060a0c110d0e060d110c03071a060904060b18010e061306050f0f1504090f050703141f08010f0b030708060c03 73
    0x313035800d031540110b01c0c0c191040600810010300545400007840000141221800245803017200203000c0c982c6c940302407100b00031088920b003005034445902c1100c00d040c507030240e04a91050100c00b0039a55200e10120b441c0820613036164107442d6451a0a004e207030303807010b0381c00340e410302c1384c0064019076104131801031040300e190092030300c40c0200240c0f00841c0c940f0303a03201a13440310149000685807080c0a19182d240d402c0100166052580c0e20002513000f59001c0c2c1c0f003071282030010102000c42d2a240c807003000400d5010300403a081030446019195115801ea005802000d02040158092038260240541680e00c622111082c0303040c0b44040c40180c0d80d0300240c0c601c18001b541c03070b2800d01900c840007402815003602e802da0020740000b00407a41943c0c5410041c180c10812000b40301d81d40b40c0060480403100140c1d1401044404040402c40c1e8031486d540040301101100255034801e600e500e100740c00c460308040c3c1d21282c1c40c0d4402d8240d2980c2403c1c8007035401001d1203c090441c40c03802c10f8921001e4031004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295261384 1250 295260134 295260139
    0x31f210210020f010920010512010909140610050102010e0a0206030f06041506020609160b18042403140a0819050708120406060f0501020d08150904030801090c090f05 73
    0x500e00e614009100f0440a864004440001c3c810004c2d6414204c892852511401010050f10381c0d56001c0395000d03c0c00c59401185c9501d030260301d41e01c0d107841c0c803004bc20f811100300ca84121488e4000d100322010000b0a005180b4004030714005441e060001e800c580b0341c0e0902800350f8105054240141c1c0c2d07110107480d407008a039402a00f1550303903040060b00070a80b85c0c0510b012060070702400300305940e00080c40da1241040c0e100b1100c516480400b0030030540501c0c45019000d000c200328074540885850014040420060f20100e4604444111203100b4100908142c10507007601c00100140400c1c2c50150501c0603904000d890b107200151220645442403440c130044c24030b4074000301d400c003501c10300490320761a410120b89500e03020030a001e00e44581d4242c0f400e580d07844c02d0480102d034010b407414000040b03541c144c000300004a5921410b540000c0300821145505000280180c0144c54034540703184118480d0703483c800c0d2503042409000c2110001840301c020400104401d000785075000d940d290554808 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295262634 1250 295261384 295261399
    0x5030106150c06200c12070c030305090406030b090309031209090403230310050f040c0203090f0a18050402090705070c0302220f0203010f050d050703020402160503031f2102 76
    0x107403c2543c09050f0306035242a5010518841c1210300e0380e44000b0b0203030f8000c0364003501c03039000310200e90780d0b414045d084000c1c4c440200304008200080c0900010543d10f00c0181020580070740d2500c81e0b20345524101d4110a41d0741000810042600e000d0100c2c07840018804d9845041508800c0481d2164000810003014000110106841c10003411045001c80b4202e60590f50303245050070502c1c2074800c02e84505401404003440340c81c01072400c0d006400107000076500840c1082c030541d040000e980d00c0310302c070150131004248010850071524807400081181c583c1000c42d0a042ca441171101ca044010144410864144151000140f42664460840740c044800f280f03500c2891001d2441d400a0f018110085442c1101510545140790040c0d07040b030fa02c08038040140c0c3c1c0e8400905c1100b4451802c000c00b640c100035028401483c1c030b40d01804102d440c0c468040103c0241d81d0382c03646154025290390440c1030440034001c0f9014071103a0a100900340d070540302c5c2c000b64007400c100388101c4109400240704100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295263884 1250 295262634 295262657
    0x1a01080f1503070b07031206060206090a0b1005030f0a0b01060504080a060504020103020d05070e1207030b06040c1103040612050a141602012d060b0405031002070c15050d060503010615 81
    0x1010483d01c40035000616207182da544203403030081e00d03110103241c040c018030f401d000001603140e00105800340326141c0c02014001c1560140e5882100d2540240010201048101e001ca12a10b0401c2212180c0408900600d0032411754100010503140503030200d01008408c000501601e50003044d0108841c3e446800420592910710041c1c0203405222008140280b03800d04002400b17038401c0102500c4041074a45940003500c010229490344000d01002d0082c04d050400b085050609601600445103142b400300302c19980b225240b415544560700c040f0001d01c0d8000200d80c03006040c4035054005410f5441004050b103a80300c0d030030380e85200800d0040c404698480e10003d560007900205860748252060128149080602048245951001c590068035009021440000001c03c0343c06a440050050000d282e20040b01e0001e584100b500311101504040d001030240e0600391001041615900c2da47d031a500702c942c41c001101c003941d00480c401ea042c54410400801c1c881c2070440000d401d0704d0420b510300b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295265134 1250 295263884 295263889
    0x5070b0a0c0b040602090109090203240a090e0f0106060201140a0c1e0314060406211b090207050d02010b2101020426061305030405090403110a061a01080f15 69
    0x1c85004000d806500c4000400c403c00c51240d000b44075904003601c8036200540c45400c80d03001c078082281c4e11038480d40c0542509543c0c0215441c010382c4c00000a0503014041d40301ea0710682651140200a880c590001c0d0100850140070700400010344081d04c006c01c46042500709007928845c0c084c0c150f98005a4566400c10085c0c481c3c0540c0041c8043e0340d0345140107814a00c8010000c0c16101448840d5a901101242143c5000d0207040210740c4c0c1b0801c1d03914898065040b00701c11025004045901ca8820241c4444600c04c12000000030300d010303280140c40b1603942c242141081c1c0c1c01200a801c5900d40410700095030381d089440c50364888019210104260540b6007180203201e1604060180250700c0100e01c1d41841e020070071104c0020a905803251a106c4070481c0b508002d540780000c1a6800034032045c80365040111403554024002c0c681403030008041d28440e42403c8010400b5900039480724460180030f0020042080c3d80e11007881c1030f44c420b290501c02c50200100140c40c1685554010202403040d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295266384 1250 295265134 295265147
    0xf1303080406110712020d120b0630040f0b09010e070603020f0c010603050a0c0503030a091421071a0a02100b0402191205010e06013905060f1305070b0a 67
    0x201d900c401700501940c60110041d607121010341074200002c00d80000c13050400c506000340c030710405014002c0342c205205103210511029000d01001d080ba40309100c1500b040c0b01a0032118059030085607280d0542000b030030900c8410000800000c9640e04100006800e031000103032000484959240043e1540b80c6514192058480c0d12030748a5a9801c1c1100481842004540341c07030a03e02c1000100341141e9203405164507170290106c0d02010441d1840200103541c2012822466040b00030a0a550200c043d082c0d1951001415120754040e0301146062011404100100c1d5101140310401405c120010000035a5130082c0080307000e280d41c8a900d0051540c503160180c0b134410325000e90200d20070402040081c10380d0341c0410302044c5507050000000300d244400c50000d000d01810f035070303800b880c2d04038000719004c50500c905600310122800140054100c07441c0440408035104401030b001600300032031710300c04851016010304007040708035488900040c3c00098800c01c031044400c0b40ca441c1c20450800740c501 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295267634 1250 295266384 295266397
    0xc020f040c0509030105060f0d0b10030b010303021f0e28390302010c1e060501062106080319090504051003060e0604020f041e0905060f130308040611 66
    0xc5810300614000140d0070402420807038000350000c0080f0f0b5540410000e148140b0755072a41c02824954405000c0b0710b110f014030b80e02c081c5400c09540090f81e0390b1394011010000341c0c02900143c0082c1070a0900d03407401041020606150402404a009002c00c000d40310b8075a02817110324413250000010110308503001c103648054109070314009810440140e950f2103070801d200381e007001a1002d04001c01c0c070182c03120b4000380d90f010380d1072012a10056644045080607140e0700e8041c4048003a45c1d00c005040c50040714040c2100e03a4441d80c540154559440b070f01080440c20b0032069003024014452004004180ca8190b055480e03038214000300514183d5041800c1e821480d08241414100b010703003c80c400120007164814a010442c41660421540d00c0e0401039400941c415400040310f0b9403886c06801078129030301c05280140d021102900c0800031202503201c201d416412407410011805e0301c0c03030b40c419446500b02000d0003906406950080c50402c00030030080c110356071015400300b15104c0c841039444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295268884 1250 295267634 295267639
    0x60f060810022b05220512090118030602041811072409080702182a0d1805010b0904170d09020607030201140105060705120d02070818030c040506100c020f 68
    0x105940c2002d010f0010746012078a4501c0f01c9110b140074030460881292100e4a503412001a0502420300c0404240c1c6501c8030030814108404c010602c0c00e40a07050343d1020003140f04000040ea583d18100c40c1c3e10510b00c605481c080454a8400c8040965100c0780444000071b6002c5c10030409018120311202440540c0b10400c0e03d628904104c0b01c04103e0444001c04002c1c2c022070704814007600c03030621081c0f12003040300c07503040c1a20349201800c02c0400d0b100411601c40c18000c1514204500b0017094401c1307680e00c003e0361781600c090706007040500000f84111070840f801036518200c24a400e446000c080030060b0308140d20f40c0400124042d411113168014810641e004045555400f01030030000d0107801d851162601c440c48200002039a80781042c02c482d085070780400a0580b92040c81e880d018a03070041151280e1359502040403000003081c1c04c0003808541008081403003800440740603d4075080313a615640340164580828841301d40d483c00802d501c0c008840c03800703160348075081c40841e0660013051001c94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295270134 1250 295268884 295268947
    0x18070614070204112104062a11011d0a06060608070f1d090406090210081302040e030903061003110105030c0d1802090a060603051605040e0a02190804060f06081002 72
    0x2020202d4060110301a41c002d40c401c3c003207105c501d0101280b50b1400c8d0303025501522a82c1c10a06c2c2103001d101021101010301c0300020350708240c84032856140d524814640310a41051201100f004514420304015280c6442c1c0b000e030f245080c400181a0055010941e0b050101245990032008000c2c254441d0309240a041100b00e418240b41100160039218000c900c5209042d040c10002449201254030440f100700361183c400b0520780902c4000c2c0710700340317103c4030301c0c082000502c01c00e031810042140a94040c02800350032500e18181143c0d40311501c910b69040110410901c40209042c100742c82c260070410788001081041c0c41010340d43c45184580094000d9207807020802414119446642140e005840502456440503d683c901d6402340d80002c004c04c4051000b8029241882c0c0f03110307407008012000510748401040c0d0326240b0761420782c121380007074005c000700000c00c5402d0180100300340742c400c0e040c490141000841c2d900c500086100c010401d03400302d0120902c04001c5031242140c8001e00018 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295271384 1250 295270134 295270177
    0x50c070f0f060e030a08030a020a0309020a08071a040e060f2404080d0c0209040b0601090305120a1d0109090c091703030901060614030a051b031807061407020411 71
    0x1540600680c81018080780140b003481c030050130040703100b04001c0d6001d40314518513030b601c01d0b0500003074112807814410141c0d0b6107910740041e214413a01c00013821107400101226803030210b0b110400012028010084603080c802003107502204c034410358010740c00311441601d007180d103404a601d00424032007142d00318000c0700c0c582031103c031410000d001782c617038100555159000c2000140c0b80d5400e580c0009401401c03000000300400c0000e51082d420000524041c500580d80b85c8a40c0c0c5072211900c1c06040070700d800502840e03003541003803215040c1c40780d407a90710350041076120029050751034610400c40e1460311649841c0c003403071140c404030014140344d2a100c1300c1d07800701805082d0740f90012511840d00350329025021038003501403c0011100c424400c0740318030b5950b41841c510090000030f4044080340960006107130035030800a01440c401d02c0721030448003070380310000c10320b920304842a8060010304c420f204a80311a0302d0200d00b110034058044c3c5000c80d9401c40c003801c1c1c0d041d610519061407002e01e802e0040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295272634 1250 295271384 295271399
    0xf0f020d080a0305011404110414040e06091b1e01120b030708010603051203190c02030d09030f080c0f0409020c030d060f1406030f0402040504051c0e012706050c070f 73
    0x1550513500102c0c010403280d51b00300c00344411203400d8898104003803070a10040208821401c1030b25055800900041204400c2c1060645030100036180903201c0c2c3c100507900c0c4040e49080084104020b4220f550542c0ba0b000c623260302a0040ea0b9482480c1000402c0c800e0141d00262a000802c002d4005021501070b6950751504074001d141a00086510340903071000300e080b0100000989014600100201100c400708103515001040b4524082d015070000740012540c00d481803282e480001d020761501805442106d10044c03015100818560011000380301050282c000142902d05031581070000680d100b000045007481c60141e4020301460303d00707104c8040b40040107108004116a07120a00b0403c90380d81008010f040d00084501300c144002a034001405864139030003440d0841c0c0540c05407803a1421901a00d0800503c000003031000c1080c01d42d080c0e2680d41e02140075007240d05405440408016821380c41c022442c49407003600104500401e59588807403040c0700400060510000c0d4000c110740d42c404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295273884 1250 295272634 295272641
    0x906041809020907050c0609030414220203010308070b0714030a090204110309030c100204061209030c060f0614030307050307022107030302070501091403120a09030209011d070c0f0f020d080a03 85
    0x30300391640600d1010230300e070481c0013084d0b030103441c0c1610b106032540b60104140807024180001c00d01030840685c100525100d40c51004601031b601400c0ea4070307502d20f541d00b030000c000f100103400d101c10401d06034240c042410b020300c25650810400c0070701054040e0140001009820901184a40b0703040010501c01390800c004000c00310100000300b59036014440300c400c12704a008907c50b910201d509510380e01c1060009a0280c000c01d0b00c40d0408039140e01207a11220100c0b0402c1d80d1109046544003402d014521200c080c0400c03800b400ca0007146818210303a1055168010400000d004c1e80d41021070409601810800c00d00e803035015030860361601e6481c10002c0d51561184900c40c0418040c20004c9a0300c01c0116441e402c408015005140760b0062020040c8140d0000042d00200800c00d2004001661080403444c0285540d4007542001c1c050004400d150441c060010002d020b80800000700081803500406012038102d0ba010700402070500201d08442071880b0b0040c00c1c0303440001e1405e0030039010392 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295275134 1250 295273884 295273897
    0x100302040e01050f071b020103020f0c010203130201020c040605150c07051509041b02030a0e210c0a06081b030703090209070f1e0e1c0206040b0d0b0402090604180902090705 76
    0x6440013100e403505041550305107811321008400d00640011040554066002802c1810440c81d903245801544540c6600b203800c01d9548902c400ba0301e0080780c0c01d41d81c0c10803842c41100e104072020400140b4020020310b0b00307400541064030512020441082001040c00301000030314003d0b2445030007582c0b61515000561010585a100301d103042c20b809481000110301d160f0302803c03078005524003010b18201380e070001e4a408803a988001c1110f00b00080030306400051800500940c02080c04201c01000c00c0a007170b44c3c6400100c200640c00003000b83c062401100c0c2c00d851384501007520303903980703903004214050200e02401075000030303025042c441c5140e07001c10036921150440ea98480b400310380c5a10706461000c010000c02c00141e14000f00c1c407092070003842c0f00801c0140d0810326030003800c06c2d81c0070413007a400a600c04840b6101c0030981c100f00d42a14003e07810f003000d003242e00318980166440001c0c0c160040340a210704014040244414003010340d0705c105045500108032005610700381c00000d00b243d0211 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295276384 1250 295275134 295275151
    0x40614040803120405100b061b0c10030c031a01090501080702070504020403082107020d0e13050406020912070b07060902121606021005130803040f060516110a0b01090203100302040e0105 82
    0xd1501b511a42c84501c5a07500b40036008216500e44a00a0380f441c0c208401600e1103003541c090980500c41ea6602d010b0544041006918041070000c00700038041c00710380080802810340401140ea0316240d03079118030a003050b5902400c2c007220586505004914020954106541080c03002401200348000c0724007410090001d6503841c034804169500c005d451400603950840541d0100100c030603034034041c0c209090325550161803021109c020101d000c050b9a810380f015192150300050090301030070f010b542c0ca108100d02d580148013851604c15440c2c024401c50101400140d0b41c1c220580c219036800105088210851044581030071080250324611000351141401500c9050b1460f40b1100c11070184038400c00340b00c003000081c2d4140d80c440c3ca5079a8070041003161262000800c3d80c0000e01c09200300c1d4044e1051305840b0b100190218806010751098419091080d4441085c120001da000f170760150644003502d10260300c03a2150904140d100c5155000254840d003018120032100c030055111601c0340307410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295277634 1250 295276384 295276393
    0x703020309280e090a0512180105190305070302071a060a120221151e0105010801080d030c11030a020c090a050c0d0b01020703230114010b040614040803120405 70
    0x4030441c04019030302c03805a00320300c5003410340c104203050400314519440360f000801c0d0b51624040b642c6040c1030812203c00034982c0c20000c289440350180131701000f03840c0c10080c244149002a4420102d4500e40149070050815440360005655144242c040c3c580f5554030486841820000c07070002c003200030003102c5032400750240680c00510312000c0344810441e02e07006050413900326070707114a6010681d4103402c2510980b0442c0d49821450040101046c4034542c0351440c481c04500b1005407007040c99069001c2410001000c00500071243c000c990045030451314100021034039590300083e82d0005003000074400031b0102242061880da004900681c42010032100c0303080b540d454140000440d030003a25240c2c400c00303003170000381680c0c0080e03404000509030500440d076407aa980d0355025039046c03840072140744010001000c24610b6000340210109800e100081c15859030401d010700b00c26001e07510889040180c2072458946102001040310003800142d410392b03a0360f960340c01e010031070076609031800c03101c40c841c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295278884 1250 295277634 295277659
    0x10201050105100302090d0c0f061215060e010207080f07060801090c0504030f060204050a1205010507090311010c0609080309010e101b050705011503032a0f081e0703020309 76
    0x41031050606070358009040340280254107404800a400c42c1075060342000d041011200450140d80103c0020302c44802ca60130224108000213007101148110546d4580c01d142070320001d4012520a2002c0d40e1540c50507544611a8800407450301d011a408840a809011913244000e5004100e46c01602c070306403220a0030b80d13a601e034807008035101840c41400040080c030061002551200401c1e6001c0d0103048090700342030320b400000d10b4684d0141e2020316020004c4250501304403003030180765404100f5081202c80070349540c480320381900c54805403504100c000c0c10b0300c03010070189901000407981c0060026480749003003041030f802000b041103140c03901e00c070b0060610000314a50050807004407101c160701800300000c6000707441d1900300b5001141c40b55203820310540503501d003041c4c8000075402a510101c9440c0c5c03229203071143c40c1070114800e0800d6660301045001c111800d041c850615030154607580d454805500003406003801701030700a29010001340c03c0081c10383c000050551a9400c4455003000c49 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295280134 1250 295278884 295278887
    0x50f010b0105120403030c11070807031106130e06010c06020d0923120a030b0303030a0501050a14010c290415050c180f0111031317010501061202030619060c030e01 72
    0x5514480520f88144000100001c0c0b283e00007078520a02d608000c0802c940d00140c1758103240141e003104000d0b03804004200300340a281034540c0281d205c29180d03189400347c41103000c44180154064006a03140d04404030760980d201c0c2c8044818260000301c21900e40e11503d1116000c1c018010041d9402e0403100303401c4a40c58400c44501d29a061041f0041850710303082c4209661a40280064030185541e03100801440e40702800250b00c684403c1c83c000550f5810306080050a8019400c0307102004140d504a10321646c01c60a0a40c02c2504110900307503e40000c9002c40011101c503030201e200302c0c00e56062001300420030b288a0118240d1007402d014030350303480306048850b00a01e02450f000a604001206850401d9111240a030300181350002e90b448500b4100c40c5075901000301808208991081081280c41c103c190030003002c03e11000780f00d41d51510100030304110036284141d924541c0040416165602e06610061038a41e030b400000308682d803010b0250241d451203100707602140165958410b00c0d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 295281384 1250 295280134 295280137
    0x1f020c0607050a0903061e0609021b012708040308040b0c010b090402090705070c0e010803040f0801060303051e040e070c03020c01030c020706110102040e1314010603082b0504050f010b0105 83
    0x1403d0307038507442403600e9510340402800742c6c21142940d0040b81e00c541c2200e1007241c0105405850103503000750340c1b80d2080c60280c5c1c3e0003c0c049544d04090f45400c051000000c040d0743c85070b2070030400d6041802c0c0c1403650700b00f000152050758402400c0c00030005001503e500e17101d004e0300e07442900d40003c02252480405215800b00c0c00c49000398070504401c0040d5200d80108083c2c00c4090080800d0400740d52100350070101c0c0c0700d003a045035006034400b0608006501e04172107210090500d100090000380c0c41c44d0781c00fa10701e000750313500f4020104060340146da00e4008142690b00500c2400320b803010074240088090200c0403a000c085d40107004e481140319981d4040d02550043c2e00e01e035030080140500c0c1c075108540a00c1140c0c007405e450754080200241d00b03005109241d01030200c9050080c000c84440c41c040a102c00100c4031007a8990501c01c080000c91240f0040c0c0305181d2180e50801d05000201f140f402c8020121404142e0701d91801342070000340b200009418201c104864001c201d58280600151400d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 295282634 1250 295281384 295281397
    0x4050709060308030103080f09040905010501152109170f03040204050a0c080703230412110708030a0c0309030204050a14011d040807051501170d0309051e1f020c060705 74
    0x710303c00c10040000800380c02c0140031288000110a051001c8240010140d480c003050690742c6a4684005101c5a0080c0c180c841c0c0500306030a01e185e103a030360040110f0030000305001d00f050703040d46e40300c02c00b050210f200c4416a41c2c0b461a0325070381c0d44d425001150f540c2600181c3e01a400303645814000f40700c40c03010780b00309040710398151941c2603107558030320702140900400e400c441c804035921a41c6a07000e82444a105000328030412180c41543d684a80040581d400c1002c8150564800c40c0c0801c0029004021500d010042c2e1030040e4030404141415640d80e40a540008d41003480d28042280900d0385070302103c00392a4a020100f203d0741e90385840080400b02c402c80046c081a688042070005940e10028211035114400303503030303083d504106955091a42603024480c2c8891114140c4407216051043c120f15080c10700301040060000c0e01c0d41d80c0d69085401c3d0403040015000c0c2c800ca1904020041c800d2851840034000c3c100001c0314003298082c1d040f401d0340c0090ba202d22004110b07154001e4090300c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 295283884 1250 295282634 295282643
    0x60304030203033c0403030609020a0507050c06040501090b030601030615030f0f0b030706080603010e010c0c03090801110d0905010b03010608070602060603033f100302090610050a05180a0e040507090603 89
    0x140d441ca13030100307440401400840c1031550352400020300305802d0000c3d095000c1c05032200d544681c05410304900b0180750b546440e128950030803041c00181c0e00302d41c0f01030030741c2e1615000903240e584480058008000a0708034481c544240740c030307030081a82c5c944c000c508456519503041c40180794003543d400540f10b0b10750405e0341c10303003118509010441c82441c0495110a0040004c11810344100f0101d003180d052140c0c0307000190390307e01c13950285034100071104010b00c1540e000708100680c84a000b600c50107450801881191985403100a1250075045118001c000400030881d45035903080e12651460180704000142c0a148009081841c0100a8070114400302d400c4840c1c0c085001e202020800038881c06030081d03550501c01c20318003c0403000c0e40d0b200d84903141040001c0c50a60040100010300242164402d007904138820403640c0c1c0c840180d07100d8a845040035030302c41d0101315a840b0520104d1512030f80201c0e08510000340440d078001b03403e000700c4c002d10941d80ca0540f691810340c2524200d000107407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 295285134 1250 295283884 295283971
    0xb27060c0a0e060307030c081b040302060a23091002121b070e010f0311060c0c0112060b030f0a1503050706051e0c0d08090a110f030a0206030403020303 67
    0x4140c10240e0000742800c0440380303410340e2a90081400a025030300705032180d00010743e542900511782c640210250303402c50003211ba90000c1409180c2649460f21690100901403000401c40e11022402000e90100d44411400c10074400b10b841031400e540e0750064503e440c0b141c0c8040351100081030003c0786c3c1c401107202c1c201d43c55141a09886401c1c0a40611078a6407400d4800d00784005a04031101d96268040c0c030342c1403d140781540c41c500709422045982128a80f00d85010081c00c0c82c48140018101e1840d102801e00202c0c0500802080300100095880b80024080000030030211003201c60b004e82c462050b428080040740000b5411480b00c00c0d031400014020b0f40000400e00c169406100078000d0300800782c405004081500c80d0202d074a8100d050401e605034012031340400559044080260b100c00040010440301c50552226484107224409840c0180c0c400d17401244261401e01c24039807601d8011380f55541c1ea05082c6002580d035402220b00d5a0241c1c01c81a520445101d6110811a400094803048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 295286384 1250 295285134 295285141
    0x5011d180a0b180f0403051c020304020a0e2a1e0c060702070602060106030213050a03060c03062c0c04030605240904033c03090512070b19090804030b2706 68
    0x8502c0100c0500141d0034840b090005030040c180602c00400381c20405503009d6283d0410340b0500403401f642d9000180420307542c104102160448075000c107010802c1e0200b80408050340d0000c84024400d00c0c0c0c8900c4a45d0703000a06d4190744040b00c00420091801100b01c40f142e643c0c4441c200d840303008901501c4010f030032840040205a21036005041500b0740d6002c0300c031100f0f03682d80002e00b0003030140d4400c481c11902c804642110a4040c4900780040150550b011140700e0b2031207200e0342c05084817180c03603050001c160118810490900c05d0b140a164441d504000c1c0d414018508501500e90f41019241c10303030040100b02c2c003030400316200c1d8000c55243e101e21044614444000b450714500c0c41c400050b81c0c0d03242080344228003101a00c1074214409450009188140d420a18280300482d412029850360800020740090304c08a225648411404002d041449508407024090810701d10050111500402d0200038050080c915902a1a50005a82034181c407482408038500c4129602104c070740000000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 295287634 1250 295286384 295286401
    0x303040f05010b221a0307180905070f2405030c07300e030309150306030a0c091406010309030f0806150c0c2805011d180a0b18 56
    0x61000d4244a80d001080030805400802d0f180000324418900500100e9010074200c10184201c0284083d0050401c25229600021a0780d0700028841c0307961140f121101d02800b02e0141d40100207043e8443c0c1070390300041d41d60202a91800880c0900c00e8400c0c0300c01ca01110341c0320f0b1942520020030710383d11014199503810104480582181c04142c0d00000b401406c5040c0c444002205481012800448600d44031989801040c9000c00c104240c020f900401000d400e56840892950308298000301403076403640c41c407000c0fa04001d8a02c000800700c3e07100400114240880d9000100340f0140e00040450980da01801101982d860701c00190100b03640741e050340c004a11603002c0c544d000c4800f504480c0d00f20801c00c0910500d602180b00750f440c6800c035000307a43e09480c058002c200c04100d82460501d4076280b9803112110709120b41311711414070488040d900941964000031100c006c10041c603020750561205411014020304031750b0039561a24048040c502c2d0700c1d120788a244106000e402502d0590f8502c40f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 295288884 1250 295287634 295287653
    0x1d040f020f060f0c1606020d0503040f030212030c280e0904020105091002010b150306010f030e01090c0e0f0711030711040f02071a010b072a0f090204060e12030304 72
    0x280c0c1002d0300704005085180707103c1c02444104002d0004060407040313044408006400398020b1011500040682410380b50300006407a0010f80019410b10b00c54824034081e840c0202070404c044c0c2c02c100110420103d03c1031400035007820080034240041a80d0544011b020850106500c1d80108021509444207400d005070140c0e0b01c240b040c10b10925180300c81e40098190740c545c0c0600d0300142c0d11280100402c0c10000c00e2049108101c0104500b5800c0c0a00003900140c60050340504042d511078540009002c2500503101c0c0d190800380d0940800c3d01c800301000c500f20100e440850b8403207040c010610480c41000351040200345200a5070402c410b541d140101607000d101e0b00ca90058a40c0e001c0110b901252000380a207030300ca560503204818131600c0c251202c000581c04042c11840c00c1c00000301141c1d080300740d038080e0414240c15020b06000140981104880707600304102180c0c4040002c0f03443c0d4013aa00402c1526081d445004044408208004200080082c0c000d0540c005001180c00116900d1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 295290134 1250 295288884 295288909
    0x30804120e1e0f0406120c1212320c0c10091509050a080a030210021306032d060611010605130518060f0115030c020d0f0207030503040f1d040f02 64
    0x300383c100c0d2018024001070a4881c140c1100402c0348000300118100050340103c0001480b0070807085403280f6040e222850122440a00d1605000b544030254400420b850f4004441000d4800e26070811210f031059007006811440c03100d205442040b0500b030301071608000401d00100300c1ea031413a1407941000b01244440440b41601c1c81800300c0298003180a036184110440900080d4000b862404042c0c1402440d011394040f02d9044248100160345d00c10201581c420240c601606000c9404810003880b40040881d0310301691004a00356040d507000328280d04486d04544265030b80a4480303801802c51401c8480a00c2103590002c0c51142520603504290042a80030102500e44071400d850058850f0074090100c0e260041d81500030014865249442c03001a040451860200a440301c3c0e00c0e0f01964034a1207401200c240700061701c0c07411000b4400c000b045c0196501000b5030761a65940c04844084498900500664010b0802103150300070060a805220740e4220480144001540e000e2105824009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 295291384 1250 295290134 295290139
    0x90c03021003110412050c06040f030204090c0b0c010506030105090c13050a0e0a06090501050106030e1e0c19030c080604081602030c0a060c060608030309070504110c0604030804120e1e 81
    0x42498600d61180900500003c0c40303c2107051702c3e214034603e8414282204444c0c81446110b080c4001d0089142590064047e03d40c1030750009004062802c040841c40c0ca80d9210700030200e800580102c2082040d0810b5001e200160028402a110124000d03200d52907440c5260700f016048034a00840f0381d054106a80008076160002426010803d689041400d400e02c2039540540398010b00d01080024460103004003440c0c5001c002c0070a0402d116502c6011074072000b4240841c003030742d40c00e501400b84004101c80400401800610302915440da103000d600d40300076901c000001e0f0001030141c03400705101c0d2260364080240c9140c141e509070380d0801c00d0124401640c0600c5980303c1c048442e161501701002030585501d50800740c1e5010324004059400982068079a44c0051040c000310140004980064550441d80401c2c50312003200d02880c203019007a003045a83c4030f50400d20003415001101c00b13005602500080813444100803090b6112040c00359844c3d08503a00c4090305a40c80401070394800c420000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 295292634 1250 295291384 295291391
    0xe03070609150e0d020a17060112170307020c09150306010e130b190203070e09100803031603090203030403062007030e0909031b03090f03071412071d0a0b04090c03021003 75
    0x5640210701c6c10885031f08030b82a010f10309078082040d8001005490b0040901c45201407407000c1075500c0d000c40c41746006004e260086e021010402e00c50003407020311030320140585804414a00b50f0341e20f1103803107405c003411806030040c20004510b174260840e802c1d100d02540307103e03402600c001c0d58810a08000007002c1d46a100881000410118241c1c0001d6001c0c09140e0b4650915001c00382c00c0051030000035204415400c000001003000807404010707a607018100d03900c2401181c6030003200303401405041070001d506001c00540401001115409100041c0d161b6090217841000501402181d01c141c0d24040c1c0420202c5910244500d000030202d54030101e0b003825a818402c55642c0d1a118281c4000f0544080d00046400801c034140201240700500f400c40c018600e42c0c3ca403100441e03480c90361144550003141c40700305d02c05400c003040202400400905808128040748000341501c02e03481a5008026107060800802030341c502170280c103480581100c02ca00c80036245608001c40c03103400e4406242450784 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 295293884 1250 295292634 295292659
    0xc21020f0609010212060609130b0d05010603060608280807060b040f0902030c01020106031a2203080105190503030307080a1b09050a0f12060f1103070e03070609150e 73
    0x910460740551102e400260f181c24000030100400c03203005003420300030501800301560680c0c400e090154003980b2003900182070380c21000800c3c0c00000040002d0215828100004204240c0f58040f408491001c4140c0d00b040210700d010411064052240111046500e003550021640314401014801c0c8603003c0014290020004501524181815150030035552244101942020700c030000ca003810920003003007030390f0459a0b20044059600c04500000c0c0c0144000b898a402c9103860b01c01e14a0310214180c034074010341c90000c0c180a401d000b614010114240109a40e0380d00c113140c0e07425200020040d44c156a038200d4100c0e182c0c40000e1035200d01ca91103031100a910f25440c846001108417545d0b6601d500313410a028040c20b1030b02c55000704040400001d041010015400d00300804550020700400e459441016480284c07010203c140103000c800010700c2641c68108482540040c2c0c181c3c20340f10718030b1b6035084c145e6155900c2c0c882c400c48001060414015148101410340400d1401001d07000c1e0f502 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 295295134 1250 295293884 295293913
    0x5121504090b0f09010c20100203010b19140a08060f0415140603010e011214030f07030221030109020915031302091311120312040606050f010c2102 65
    0x68012109441c000302d501c042c400014025001150300100c500004d01c07500c00c10b03a43c024891031040c070844204441e025403107003000d03a05105000e00301011b068203645a584a204503110740d03101680ca0400c0054841c01040400e00031031a088002c0c460010ad51b007002000030080d900310400503c6c580e4010f4000c030740c82006540301d12902000c03204500b04c01e55081e007440042203010032a212014412007040c00100910550448494191404003822100581e0249460104084407071580f00281c04003140010f60b03104140007501d51240a6800c88501d1002207218a131804009941a051894200018081d4519940042100be00003410944d0500c0092030b80511541055a8800d13072010200d01000651824207007041c2c00c440e0900200c0b504c040300d507859050310900200079500070103940c81400d100c828144240c50601d01011020030072450700346010350041c40f45004d0310348212018441c0325080c0d441507440325281030380044000c0c120705130a800c40c00c0b2a07020300c40d12011403050056108014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 295296384 1250 295295134 295295141
    0x503130f080c0705090402032107060e011a04090302060711160b040e0f010b0301030f0c080a050a030f02150105130b03160311010302120f1b0403050a0605060108010605121504 77
    0x22070086001c580c070351809224850070700d4500c2d400740f44070348942024071001d681e008c5000c908208147c84900c601401100d009030642c007900e107003c0e0416103083d00403140240103400444c1c11310714100d552114034000e070341080112000404081c0050b4442800a204103000c0c140160042507010220b0750b515020b051349420700500c0d50484480f840000c6410000300840803080c80d0005c04040440b00f02d5030400d156445180014880074010707102a250082c144000700e09210064201e96059503e43c15490802d541d841c1c49407801200010342c2c00520882c032f68404503084100b441c3c8800144016440c010401509042c0900552074490786c0e0038401c0301942d4100505c10481c906102e003001d18500c0c41c00c110900ca18480005810305004104200a2181000859078030003803103000602181c4540b80458115800d00c04d090420711340c005004070038420005000310b0610312072242403286544e10801103844400a2041002003002841179801240c8030360141030303020940e04c0c42808540c04000001e01507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 295297634 1250 295296384 295296413
    0x402040606030911120309131a03070602150c0d0606050c0d0912151103071d0a06050406030509070b0d0212060307030b0f040305190906080708150f03150907050306010f03030f050313 80
    0x5070b603a1b42e13a52720811030b007045c091624103005c50142840c40d180000103074980305540d245009128644000411801f07540c81980c601050300c02c01080410346810028117594014001e015891083d01411000284501558000d95400c3e1081c64801c403996511124090254524010f4242d01d40d002d07103d84d40904005544101095540c5c103e00144803090901c0307103042c8421590280c010382c5000d0043c40d8214080701d0464401c3c0c07600082ca44c0d50749130640d05101454000d1011040c0006405450180c250042c1c48010048400030401d6120b24081580c0c2d00702d5440024000c0da58100042d42e203080e032410300c6503c14000d041541c600321000c940124008202041c45001c5210000c05200f0280d00814081c0d00c80440d0030580401d040070000d1043c50103020500e03500c03481f80000ca8403540e032414001c20340780030482c44180c0c0c900e08040c80d00c161110401d00601f4003034400c40000044800410524804a82d010707201d00680c5a0b044e0011181039000521402c41c100072054100005400c0c0600c100c40c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 295298884 1250 295297634 295297669
    0x20307090c050906070c0611030301081c0c0605090c1219020f031509070f0608250903050a06060510050301140f01090b0705100c02010b0120010b0909060402040606030911120309 78
    0x495034201f6001411000f00010b94904a034011300043c0901c2e400000c500124600b040220107403090b42c0d0000b21040c0e1500301000f8012800c10302806900e070704c0060a010b11701021107071035007450101e191b4956501c2d0b0000d42844005c2905c440c10b805410310241e01000d005001c1c080e1039114125280303400702e105003960504103a50000c4410008100c0361545030001d4109860260307460308282c05404402c04ca801011883c0004201031060524001c1043c0d100450b4042c080d030712100d06505040004044600c100ca0090604500d81d91695106000b00c03416203179405405038009804000384520300c04070140960601c50f580c1c502149004005001c2d08016108800034140880c5010690080e12844070000f02503a0404880c200c2680c0c020300c03040002103001d203a21083c4402620070b54090000001002d800c1035108017408070141020a03034510585c02a9414414940d03140011001c03603940c4600507003c4440f601242e0418904000c003183c5400c0d00707e00316805c003c004d0300000d0015400701c20204 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 295300134 1250 295298884 295298903
    0x90402030a14070e040b010516021023040f0f05030a030c0203100501080a051b030d0302030406062402280b04020a09020c1005010f05150f0f04062604020307090c05090607 75
    0x1559182a010341b8559031003e00c0c0003410198500b03003603051030140e004001d1241e49501040400a4462070383c2a55941100094003040c0c82150584c0c003642d0700600404074940074188001c101c06403100700410458078003600a20040380e180c4c40858040ca00920308a81c14040c0c1014002c20541500505000e420148080c11500400d403501c0f91a148105071021200c2c01082d550821a9030041003a4000d144181001341c0d40e82d80c0e5203001e00040c074068203d400341407030060038104c0f680d80000300074401601ca5002c071107100c100403004d03100f070310203485881d4072000c2030441c50340000705a14060f81c1c020f0b1016100c13000700c6854040c07130401d07a0800c2045039801e0780019203880c001051402114010300c403c0441c42d080b6800c120100d07040d01d2070005031650a01001564409026262080310701d40281580c8158a803500d5505c0209035545400c08402c0c140d40501c1c0d43e0800320f400403a0140a0f91f4020010b0844501d015182d0000d89000800001804030900034140c554598a0051240910413596030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 295301384 1250 295300134 295300157
    0x10510023406030b0f030a050d0e01020a020a06180b04270b03060f0901060f08060609061f08010e01240e0d02060d0e06011e05010e1c050c091308090402030a1407 71
    0x7103880100019040c6c4241c0c0843c0ba68004114007040149c00d0307a006103481c03031403500b111006030301d44024464001d400500780c03000000c02942c0082e01e141c00c0e4400340c0c403281085a50359901c491501460040c03034400c031200d2000d4115040780501d501d40c042e142140200341340b1080b000003820420100c4031041d04036240020407080c442c083c0304207000740446024801820b0700b071504040d5650001003009004402240100300d250382c4100d41c0720000c0c54100b130b0441a1000e1640001c0003050300303118403200080350720004203002d1704c5440145480313000004002000044114119075212843d0940c0350001810020034001d1b880f04402021244054000410740708546c1f08454a018016880505400300d108404583c00703408560b8402116401d00c1c1460034880660700040c1d40c412010103070400005041050004c115004c9800c03048258226419004e65441c0346091410312500720005000f00003c03c400611351801e40d01030341e0420b44081e4006446813070004541c400e118242c40240c00b2401d003c206 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 295302634 1250 295301384 295301389
    0xc190c17010605040e030c03031902131206050f1302010309030e031204050901060201050103020a2702160303060b043014030310060e09041113020a0e09010510023406030b 75
    0x3401c81c0740b402480210710b02100031f2000c581701c3c04050580c50407200d401841a052043c0d640655603d95a086034040b11596076864103410848850022079405003448002024102072101c141d02c994015404041c5e4151140d004400500095404805000242154540c652420049082d02c89414401e20307a4550030001000500c10050344600308685c100700040c40143c40e05540401111119020300b048004207180c11241c00400703200c8050107600c04180741045180d8003040e48180c034003d071410087c041d00c0d1015044940304500414402c4500c1145811a078402094418005c4813042c20061402c41c0917a1030301c00c1402e41c049010a564008420300000c00c0500c0801c2c0020f00070740c141480389400c03501c0450100f840c001c001130704103005840c009070709803a5404050748090074120110b6032080565006400d403d80d0714002c5000761130150001c141c1c2d045c10007600440285540007041141c01010582c05020002d058500381010390303c041c1302070303203000d0000d24000d00502d80f00455802e805005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 295303884 1250 295302634 295302641
    0x180f0a050615010c14030d1119020f06160314040303020712031a041e11250206070b060a030c060504150f0804110a08030708030403030506060c190c1701060504 70
    0x100d502c8aa660000c0000760b80c00c20761250b01941d00ca480e8640140c0c94101d44c0703046005a50042c1e541c1c03400d01426010320b021a000801101182d10700e0340c028074007404000c9941b104001844080b942c0318102044511029002002098072146008900042050203000382e00609580c1100800d4020036070004110b424420012202868a002c101c0c00305429001c0b402c4030f01901c006070145644845140030f050101d80a080555000340040c4406510300c0f030f036a420f0790700158003010001174105411034002a840110b200c034680050482d400d098003501c42444844010b030085901031f401080020008540b052407800400298840356112460040c86c80e042e000075956032010080042d40c809403441c4c111190f2900b1503040b055444540b2500300214060281c950010f40c540d00c40442c0301c10802c025040290b109600ca50340610040e11079205106190145a404800c2c50304250f5485105040244a08174020b0240720459042940c419194202c90305080400c0f040e03944800b01230001d810f2900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 295305134 1250 295303884 295303891
    0xc0309040c0f05030c07110d03020703120302070c05130603021c020108150303071b0b040305060603070b040e04030c0611031806061014130305030a0f081f03020405180f0a0506 77
    0x7000742e820500340780000c0981c80014501c0a8006006c6203403001c0c04034115900d8140403000d803a442c00708040d4200030f90303140011300c0121540c9a02e00c06403440c06200340207481d5525400101034002504203410030150150318003c2c203495035510080000035a43c0c80c554240009401071101c007030001706000040c920f84008003c4091101020740019042e00d00004071454103401c0540c05c0740c0301e800c40a0344814004142e02818181c01d01050109c01d0103004150140034050480444030a60750f21b0414041c3c3e8016841500e0036030000d00001404680507506200e0858443c45c0c0000390319041d02d11421f0030360410b99204d1980240ca040d409101001000340c550003502c1100d40e40e04c5050002d000034040318400404071444030f40030412050082d002c44040010756031010542c1d0322070b03800340310091500c06882c070b09a0004034840e0114a8070740d0403200310b00d4642ca84140c00c01c0b5a90440d000e00018207806481e5911000641c80c03d02d0740e00d50140400104a640c030400303000344c100c144c105a880c0080c040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 295306384 1250 295305134 295305137
    0xb0a0605030a030e0f0a0f062105010305030a1202040b0f07050f011a040e0c0a080c150a0e010f051b01290a03030e060c01020a020703020109080309181b0c0309040c 72
    0x140a65070121380c04c50b644002807041181c88002512201c40414803921071507000d0241d4400c45480852695040b52003444551044984954070700d175070000080c2500c0c0c082c48054690f0300108001c5002d18450318401c018904c07005e1000d0b20300703a0358900240d1320740c1c441c200c4400074040220303044040200a01c4101c1018030604001d00850800041050052801501d054490f40d40d80d4450a400d420074807d440406500400000301b280e903521803151600d6041d1104c9110341d0300480a40407410360403094550800d0155107840c5000c40320300064494040038a260410310405211095851042225042c2407601107400440c01d0010070b401e58000c40d200010240d0110210f6889401c0394542603030311000c40350107144c03080c20b901c8400041171607841045610311881d400001e04a42c4503400042c01c00460b4800e80e10035507159034860300644c03240500c84480350b01100445404030140d000076040c641081e18111b480d008129044000c1e0055400a1110307010f980001c00ca80204c0d01d010310074803c03160601d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 295307634 1250 295306384 295306393
    0x31506060203120a1a0913170a0206011802160c1401033b0f0606090f01030506070c020303090307032a0305190c090c020c040e030a1b060b030601030b0a060503 70
    0xba0f00558402000041815100c155103448011300f110042491400e07149001d0401d456906154020410030f820400c0190384208003907000045290130002142c59507406540a000142d0a040200841d412052913a0070782035024020b42802d030000180c01352181d8800c180019085140c1b401924058118034445030604d0314101e003122000d100d0011101040700b0304070014440b10090080c02d0100000f0190075156480782c849590052200054042d02410088942080d00c0d0358840d141010324009000c024115000000443d9045020760f00e6a00c1d401e10040559040c010550082880c200b0f240d0f0090b25105044441180d400c10305c000aa86041d07903201d50001c02c9420340e1541683d8030600014010a40c10800301913090164400048000e0000c3c4039003440442d2074904000d58410022003000d20036450107a280030011400801c603080313000280c1b0b90a80899482d26178483ca0002e00200740d86645d25203c040d1120313034081c80580e029510a0480381c840d030400000c80012104a508203034086e500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 295308884 1250 295307634 295307647
    0x1e0d0e0306130f020312030c073c0c030b150f030111071704120b25020d050c24010329060d0501020904090b1e040b0402101107031506060203 62
    0x100c1c018580003a0304102400343e06600c0d032000c00c0c80c1070703982c4a80900d40c030008024840766081c0c54000f45001401003640c401400ea0903400b400c00f44a2020702010801089019261001d400b03501010000b0301400d0031141c9940d494a60075400c041c200c0c3c00003001148200c900144d8540080940c6c061074041d0000c100e030644440030b1207000e00c1000000742602245500c03070700408485d02d0840d000707002000814110f0074040c0c9046440d164042e1900c2141c04900b140b403e042d4030155025808059450703008200301a560138040d41c1e00c1d840744510511a000c1c465030b0246420789080012103c40012142c110780e9891345c1001d40000040c1d075035080384440203d00c0d0404200c1052131003074008001b2149500780038914903250f80244901d070744140d0007500f44201d02c1d0a00101e40741c10380c881c08243e1020807100250300d410480518086400518080e086004140507013000028204004154203040041d00c81d40041c1c01d190180c02e600c01c45640364402c40030307020110709018a4000f403407140000d43c01e118 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 295310134 1250 295308884 295308901
    0x8070f02070503071e030602070602120c2107110106030b070912080306060f0d1803080a061d0606040e01030f02150c0c1201020f041e062105091e0d0e0306 68
    0xa05172080d84042ca941c51441c22098103034580941c019984244115613529441c40c009001c0d4021440040200d052500003607004501b1078101c81848408010313540c140281203194001c07000d0b01400351001c0081d080d80001444d10300f4850000918022600000c1d60703e00180c00409400203604a00c00303000e10000e04100250708941565040700c01221410f848600c042155416805400120f4000303a040c2100ca10001c410224902040d50103503030340031440d551f0b0103401070070b80b00140310700f44d2088500001c150615140000141d08200010320140c50117079202d0800a01c0d500a800584050308114441002c6141a01014070824000090b00382403241000f081c2d9103507070000d410240034041103130400305555000c0d8110742c020300040710320703070344440d2141903410103110a4500e054440400c0c6001050039070245d00546c002000550029000348032640c03800d009490090440e50f5240f0420f00b060010003547c10b0b8607401086510f00500c1e0b500c10b04103000740400410035040380207400020500101e003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 295311384 1250 295310134 295310143
    0x306061c0605130602120601030f020418180501091202010b01020a0c0506070c030c090b040614151608040608060f090402150a09050603010b1e0906030f0402010c06050708070f02070503 81
    0x907410090005441e624a21111820722901c0c0005080501c0080d40700c1134143c1d04210f050140c0700a0381e0422401042184000c201d22413409000c0e00b490032071083e03061408840e0400140c0350261140001a61001d542d510300391a410003003101c0d03005091000440e049e0b070910820700004424801040b100e00d003074803180d551a0f10f902071140103040014440040c06201e5580800455010082c030544503078500e0000010f01401401510803030074400300046040c1c07991040072000c640149981c0c8a07091505030200983e010010038080900e8281d00d0101064118010f00014041e036198095203107009002c000d040900032040f80e00c074521920502c40580c40c0c0c1c1c4007840600207020f80c03203a40c40784034510a8400d61841d5100c5540914004008102ca42200e005010404081c41606024140004a0341c602d802016480ca0300840b09000281c071040d92055400e03003150041c11b05030b442e08240d0320368030140ca070101c2d20380020608003400e201500b540b048d042c4190102e00e00c042c141d290306020020b03444 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 295312634 1250 295311384 295311439
    0x601030b0708061f0c0f0b07090b041508090f0607020c040509010221072007030302210901050f09030a0c0e010f03050c09060a08060f070f0503070f030f0f020d0902030606 75
    0x70128000704c0616840c095050784100540106054008803641d02d488101c04004542c4400040c2c912440081c080c50210165020385841405510300920041ca0468004138020300c0b101c500e2203031100071405070a09001e20b50190703000707034050005801d1141c00e10040d140003a0001e00c003a84108440c0155030b00110740c440e9500a40c004040d4142c44804044440384492030003603966101501c400300207000002286021288240c00707944010140ca442d580340145014651a00d4003c02c0000840540c8910000c284400c0d03440d15003410020301a01003440d00685410480c1c0840035420180032907803015010f60300404490001400050965407010340354203140c8801806001064007244e8240c0d194140b80c0003412111046400514040d0000001c0030780c281c03a0702d4080b8035003081038411507110750101c81c4907410750703141c403904007034091011401040d0304c05848401c255610b2180380c080f1103d000801038000e016802003802c003994010103003011000b5001612036988800d000c50106980f030700c140c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 295313884 1250 295312634 295312669
    0x60a0e040b010e03070602010203160206011a030901060306020c03070312020a020a0209040c090903050a0e031b1014040b09041112180c131a0d17090607050d020601030b070806 77
    0x8141d492500107a64508250940541c980100d90f008601035034154043d61240c000c209101100c1c440080081c2c4c3c903202c007801019035900101c01c0f50036443c5c0d400401103400c100c11200025907255640c0b0344100700e030001219a18a0b410000d440341c24550b00c045e07401810040320a00b18500301d50b04034081c0d0b49581c84c0320000d02401c89080003400b40186802c01100400381340d030051005600c6841d0041496010051f80c501107158401580503070300300054550090701e092056844061a104200651751920038000b004110140d90070710311410b03841c405003000301814022151030b510403400300001daa040b910380000469084c0403c201d1840c000380510f0f0400c0b680038144c00301040e10010b40341801000314545411410550350345003003031941d42c4081c00e0b21075008000012000c44c4000c20400303103030004002d0410804a070001881440e1130004102800b4018803161409080755284d90074844008060405038014000400602136541c2c6131640c07164a0f031902c081e1310305e0100c5c0064104855000d0345030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 295315134 1250 295313884 295313891
    0xd11060f0f061c140601050114040608040206030a0f060f05030f0115140109031b050418030804110415080a0c0b0c0d050d180b071b020108150a0e0901060f05060a0e04 73
    0x50342e82d1800c4800200c3d207034008030b0f034940781c51800020a40c0c840c000e1040702c0c00160f1420703802ca451420300c002d560030b0310b03516a1503a460381c56070307000c01145810180001070540c0d41da00d080e86809803107100303440c0102142103c48980c50b103404105414015a40e8a46015034100b0018424540070680c0c800140c80022428404903205100101c42c0441c0a4000030582c3c6110042810a4060000d401c01110003c440510010f001080908a100c4910b04014041040c0c1004035000590394141d5482155018000250100301e00440b60440c4d001c1d40c0c032007151034100781044002e1040364541d44018248840c0072a1900d0351005c030003681d031043c1c0020107040040c04560404900030681003528138480310003510906601e01d0500d030b4400103054034032001140d46081c110040c0310a8120307081090760141c64100c1c05a84290b500d66400c2c02c41e8504640c071a00140004c20316045591019018451220001130b006040481c1b0002001d103940002c3e128a000b4482e80425507030001c60001c02840955011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 295316384 1250 295315134 295315159
    0x103020d0501020c0607030e01060b070305070b06030c030a0f02040b010905030d0311090604180506010f0c0f14031201030c06210e0c060a03020d150f260d11060f0f06 73
    0xd5009018980c1100000d0040d00c0c00d000c80c003903042e08801600c000c23000c001c0002903075842c3e021039648107440008010400901110000c14000c10700e40303910220140039900c141c2c60f20000a802d10b44d200308122203210b0740c01c1050055041c0fa109103000742900382004000b4600b0800000d941c3c0800c181e5200425454960b60b11524080c2019a68070001c050407250315640c9482d6104540200c07370800c00499881d00000600e150f2040f12413040f10400c035203031014103051607142c09440c0d030200082940c20f0040901c0166400c00200000c08080e90004002142c65045103040746108040350b00c11401c000155001a40b900d02031986001c5401c6c40082c0081c80407040b01d503007400c3c084000c08040d440000452417400e9190590014032200000300340c2005254040084050890014014038000148861051005541040106407454221aa60448540001001480d04150003100b000180107803202c800030400800c21250000641c0c0b0140045143c10600d4a15002000344007500c107250b5507460 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 295317634 1250 295316384 295316393
    0x604060f0e07030b1008061305011a0c0304030c0f18061d0601031b030510050105130302190e01090b0f0d350c0610060c0b06090a0b0d0506041e0b0103020d 68
    0xc1e02c1c03592000b4044c01e045204440d0003900441003140c7c014080c5040301d510202c0e40c2424407d40e4140c0d4a02c0c40c1c041100c100c80e41a40da500d801c91400c600cd1031000704000b00215143c0f81c0e0300d4009003051814402914204044603080354008402c4502003414030030144a01655042120f41182040100410320303950040100c1c09050a400c2a07012004099000c1c00312a1385600801e106014111074601c4a07030b070354801183d00384181c00740d8040480841030203000510b069481c40c900f18070b1003a251841680ca6146001010303100782c2c081601c644d514040a011400c00c0ca00c0e109007094100d589a954001ca5218010480f018141721440c52890a201d41380341840c010031302ca4600382087c4599200d0508120417599440c055418070100003031071000062003071103150b14000e015800900d5a40039150300052105040d405449828050340700d90119025403500445403a0480c0142c00420341c6017068280341ca0300d503228102c08030420500000c074502003072500420604507030b03058030880261020760a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 295318884 1250 295317634 295317641
    0x6090807120618030807030c090810020a020f030406020106080606060403110f030304090f020309011b0c120c121e14070f0f060207140c030d090501031d070b0703080604060f0e0703 79
    0x40840003200e88483c003418990300c1500d4501c00d6409071406c1000c191030350000d442c001154400c00d92540c0c0007000366803a0480345d8014003a00c200600440d8120341001210380d046030050340140006079510b02041001d205e040280c2500000c003541e12900e0541035454030b0f00010002002e0500410030401c091080340c80c00c00c00c4030f0007801d40c00301c1007002c540e20301d16040280d4070a6a615803658217001c1103161078460000210407914142d16540c001039020340e1410010320035510080c090100355103011003c03d42c1d8640098808400750f035103541d0084a404460304030b05404c0d0704407007004a0441c52010005204040f0707002e40741c0003040c203030b41034029103400c41e040c42c0349003402040580089202030411101c034058103000710220b4207442109001c98145641c4101c82c144400002e207890108110a500a620141c91000c118042c500c608109070110303840c1801d00e1344181c0c01d550b0001a0a030034140c1c4404069000501107405229092500400c0b440e51000d901a0488804040c03000c5081c05000c0e030f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 295320134 1250 295318884 295318901
    0xc030c0f11070f090f110405031e010605060a0c03030c020703020f011b0f050a05100b03030a0c0f060e0f0706031407050a09030c1d0901020309070b0d0f11040609060908071206 77
    0x2040d83c14850b48410720329000d041c1005101c1d44050420b01c1d400328000002059409940c07014004ac50740450250102902c001800e01d1122195615400800c69481d004000c20001006459210718844c2610340201110b003841120021508224010320060b56900801c0e1203900c001d20b030840d100d248008040e601c0342e09048000300f10440f01070800042000101e5450842c81c02003099031040c850a040e20002d40e88101603256050b0070401c4001849402125100c001e140104042e510640c026580e1104a80390b01c8080344541d40002401a6080c0042028030054561403605010a00c4089a11100c191000e00075509220002c0382721100720b88203050103001035030003c04008500755034281030041c24001200403186140d03440005068500d05000300c0380201d00900080105074980300e0b05d1003894002e00c1100c00020b44480c81c1c841500c1203030003030241c0c01c1a01c0c85502d603128079002d07016154035082d038041010f10a06000c01c010510300403403080102d43c5448030710044c4401c5450440010000c01c2c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 295321384 1250 295320134 295320149
    0x1a09030c07090b01020f070b030a050703141906050a080604060f021c05090d3f0e010b0906090705190c02090a0c030b030303151504090504080d0c030c0f1107 69
    0x190300c00515160207420180f0b0001c1e007a02a50400c1d1518034900c3d840c2c015078021a5907103001000418618042c2c1e600140d800016443e00155040e0707101d4884100e4482031f102040030b4004000405140f85179486640300804049410720001460841899290903000b4000341100d80d0b6041701d086034044640448900b0903a542620b40c0400826201c03000410060701c1243c070350321031240000140f900480c0440802c60880c80e00000e10403844969864140d08123803064000d4840c8000a10040c5c41c41c0150259001c18000121b0466820024071042c41c0e001407442e0301c5103900d1001d00c50865040400c8440043d0b4020103000340500525003500c25414a440094110002e9020000c8807883d40e8821846000e1503542400381c81c880c81d0030544d0b43c0c00180c4900e1400309021500114920b84600d03e2212605400001d900b842c2e540d0800c041214402c440039502c1d50800108008a0040e5102c0c4001d180518202001b64044d0024001c0c69204141040024000c00142c403130840c92082100304000c2050303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 295322634 1250 295321384 295321393
    0x30504050a0c0609031505061c030201141302010e0303091f0509060a0801061805092a0d050402010f2f030c0d02010b0103140f07030b0604090903030203070f03091a09030c 75
    0x2907550084c50300d100e903c03040c3d5414089100110100545d40a101d0090400038a41c4c40d03810b49000a0880b6048805002c80642d0758807c074205e0b503400ca140341140300d628142071000f442e03442e03030001400341086082401e201e5001001007400503901e000880103840160b1482e0b481c082c0000b0400c0d00c2d28482c503001690700c81030100c2c031401c20341e902c588031310306881d002c0d0345800a850141319808002e44142c01170303640c021454800105165007041c0312604c2403480c2105090584011082d00150f40d005108030302c0a103486004120641d60041da04a503420358500c1c0400d0320400e100028031140344013201c1100c501c1304c1039514961030402002903c0600d26401e064402c10140301401900070070500400501003424078000080300f00030144000d1007a4541d43e1980c1041d07464410480c001d184540750300d64001d406020103d0040300c248030b800d091900c6503c0041c1e9a00300500068a001c620482000416042c040c0081c005031900c403803107603490084030506100341c55124106086020304500d10b0440d104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 295323741 1107 295322634 295322639
    0x21140a0f1502070c09051f1818020301020a020f120703080609040501060b0c030301060e040b031504030e19150908190611070605040506090f0d030504050a0c 69
    0x800340784018a010b280d99036200c03141d0341603040640d48660791420030803402e56070442c9001c1d50000b80f4a80030b1080c03070301d07003001010710681300a60700360f030b840e10343d1000d1004400d07045112003079000300299154240d2100007582c0381c0c68420168110311070072910f18100302168080310803031a09079642000303941d103d105010a081e000f5000311402d41d80d07080c0004046c40c460700a040300d148400069660395140c1680184110f13030340c1d0354082c4204e1821021544a50380044e5500400d1040b021000c03060751203080585200103d40c0e55a50000701110454030070680310440101560304004078011480c00303082c1c003290301241500034842c4c982d010307446506c8403011061014001521420b800308541000c12900074160b00990412a0000e403244144800c104052102a5002c0a800d0040c919007040464180e600d0103402d8514003459a10000305050000c24040700c02415006285202c59a9 = true := by decide +kernel

theorem cover : BRFrame.Cov 295143884 295323741 := by
  have h0 := BRFrame.cov_init 295143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 295143884 ≤ n) (h2 : n < 295323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
