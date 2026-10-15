-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:35:45.773982+00:00
-- url     : https://prove2.me/submissions/d12c8055-d820-4493-a0a7-988144ad0c8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 738129496 ≤ n < 738309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 738130746 1250 738129496 738129521
    0x70305121008060a0c08070c02030313060302040807061803140f2a0418020105070c0f03030302040609060507020901052205090a020102070e1b1305060a030603060506040e0a0f06 78
    0x912060104126000c01d1010545a82005895540d2508080081218030303030700c0f072140842d090740c000540d554090f245d0100c0c402c8c0050f0a403032810210034102c1030501c0e01a00b00c2c00209901160a1000302c004102000c0a8131135420145500d071940122900d840e0018170004101078000074180039120030034095a07426120b43c40465041c60b55404602030900b08085c6a5200b5a54120300c00740c46142c2401554054032607016000d400d14410340046400da480842c0545000c403104200107030310a04856841d00850107594016182c2d13003402c100412125181d07001b0000c0180074084400981d54100207681101c50498070000d0f4145804202c54807000524001d0504c680b91904120440002140405509200342d00769440aa12107003000702e0131f04155401840031911625444100c461a0300074100c1030b011186600441c1e40c0c41c800181d04d5400b51303650a00203501c81604004112041c080c8a42120081301c082c4200440081c5195903001c0761180038102440d800030b203030180701c1a9488808100035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 738131996 1250 738130746 738130777
    0xf0109150c060e010612060c05070b04140d08160c02030c0a0315050c040b16060914010906060e0c0f030c1e0318160306092109140f010212070305 64
    0x116a000d4101a4a00d00640b10b25040612804404074180303e8901038410403551004c0c0c10f4010b8441000810340c1d10315400038000100f20301c0c8080b41c2103240041c4907e01c40c00c12404030071850009907040080010300300040c01303a400f080c410903a0520180962900f158941205030f2885400020b1805491700301898014081e41d5010061184061140c110940150814003068483e00f14000861185104643d001c071024400700400c4009203802ca015240110302c0811007207480d0f110020400640075084416a42d54004002000058003840c401082101d0440849180ac2074441c90144242c0f1b40e505444800040020142d8020000b82c42d4410104d40402e601c141285081040941c8255a20700a002d07040300507140980001421201c0c0d500b801d94070310b01c000e10355600e550250403040c20840b40c44060040c001d480074100c00d103416800400345c1d2140c0840f403802d45428001c04e04104454095038100100700450b90700000c2c50306060205c403060981d980d04904003103038036000e0b02000352071605 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 738133246 1250 738131996 738132029
    0x50d022505103011070c03140c090f0601080709030803011512060324090c03020d081902100b0d0b070f050c030a02030702010f05070b1602010b0402040e011518050f0109 74
    0x210464012a00740c0d0702481d04120b00806001044d500740109240142000403c1d00107000084d802e07403070700c01d402c1c0351242160401c003442c8000554801d400c0300c806003100400b0040012a690041080c2d070001c54901784107000c9425a110403020744814050300d252086844003000350f1520450340d64003c000c2e03254080100d10303203d14004104030580c560024000b0b195421503c1000070501c10450390940c000501e041c12481d607070a000c0c581380321032800d94031081c042c041c81c42d10b4800458040d440340c14550191500b60f0304031108004403024200000d01031002c40c540c040c002040108116005070480c10701d2181e14845000480e82d1b0700c00c200b034280b41400082640c03e02d554000014021840c400d0700c90070805003603078004481c103025140d80648081d500c100030031503040b592040056030705081d200100e03140c42003502050a07a4440da100019030b1140c0001048465010f410100c070284540c9404201043e03c0c400e2aa05400c4900a151050000302d00c4082940c2c02a48204020071a0650035158030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 738134496 1250 738133246 738133307
    0xe0f120a050f0f030a020703170c0d080105030105100311120109021f090b030702030702040c0e150403050d051201092309061f1d100f03050d02250510 66
    0x280c611904840c02440b45081d0f6500108002c030603501018203640c001d241c100e241d900e03450a48072800c901515428020000d40103900c4003484044040100d03926000000d5240c107040c98211071006041414816054200340001070341c030302c40207100040484004c2030001034440c0700750040ca4032610096010301c050641a50510f88180c1c0d00c0c0c00e400d86034840c3c007a10703695809002d001c1e1004071034001c0180c10401c8554014074056200c030410100034540012288001804588050402c041802e041800403038108200301c0100140041c40000c1e1074413906090311503050070420a018003e26a41c6600c2d045001080c61b03e10350580d6002c4801c2c00c10260074180141141d0b143c0d0815500303031182d80c10400800140c8603e03122014215024822800b20a41000c0d08158400c08042c10b0340d03041c2000c010b80087d10190302800140a5070040c0003401c441c01030184040e2404600c1c1250b4140b5891210b4100c030600c00c021941c01c11903206480801035606280c00c2220f10850300400074620008184d40440c40 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 738135746 1250 738134496 738134503
    0x301080a030e0103050f0103200405010915080c0607020d03050c03030c121f062d0509090a050108030304152417060f060607050a06020304030327030e0f120a05 70
    0x140070740c0341d0000c0006060011401d0f100100c50304100000c08000401c0002d2940c0e9200c280341200011208500c1e40c0310000405440c020303484a025a501d8803010081044070010b850000c2100710002c1030042c400c8404034035103019650001c0e00c9501d041c0040403d0600400440b441d0140c59030569542e072030440982d01c0c890700170000b03000310390341054006a4019205644488503400d01d03440300c81000c0c54500126040919004404c090301c008041c00380c0c0b801d00d507200591184c042e0340c440c2a100d050b4101442050b4070018034106050341060010003040744048201c81e0410f40003c00401c1c03078502e80e1031000c05840f01a095205600e2488401404980703c0307007000d4250b03036004403259130303c04512440039070307990301a1103a0340e000f040c10011076242c0c0b43c120b0041000d42d1251003a03d2103210940c0303d80e42241c1040340c05801280d26039054280c4070b808604c0c2344121070380020324040091540e4800400c0300842d07001c42c0b070154058000000741d655520a100468484240880c2c00f940c00a01c1d05544 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 738136996 1250 738135746 738135763
    0x61202040e0709090f0c090c021b030a08070623041106210901050708010602030a081311033007030203030402040b0a05041107050c100f18030b010b090310020a0c080f0c03030108 78
    0x10b406c21002d102040c04072003802000111801c1781d0007000340010140300035141c95414817000c1c0e8588942d2064100044006014100c4c550007990000303070015107a41400512940300c01c0b65422564604100030000701072101d1480d4200054400356110000f41c1761901012426000388810704003180304000b81010150810362003102c9958490070140d9072110140e07500d0103005400790205071074400042220b001d10300c81c0301000c1d0066582000310000100880c0c20009078102e0a1380031050b4400d2600700c24419001c80c200e600d203c074000c03481c00da0603440080d241d00000cad00082c803682d241c0f01c0c189426a0b0340b0805101410b80140300300041e602e01c80c0002c072954801c8601715554060a0311201c0c444c504070303c61031184903550b11100b190300391515040310388603124184500159070154012002c1100450700c01d01030109481c07025030b5203850b54101840c0000004070b201d11607004201d00406643d01000e4500385941c4000550b0312036000300540c051900450b0341c00300d1b4a200c040300003e03a1010009003010b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 738138246 1250 738136996 738137003
    0xb1f020c010302040b0d0203060303041203090906060207120b19112115060d1b0905011e0504051c061109091b030c090d1a011701061202040e0709090f 66
    0x1080e62110900540c26400307035120300440c00c1424001e0b210035244503001950f2040005065178a499112035010808807003110094000130040c00007480031030300c244600d40c00b5045e03d000400c0c219145ca084071840b080d59480003011100c0740408103040400894002900100182007480212070706c44a24115800680350008507040d4241440c6100107003520380c0c5c0c000e51880c0301f40b240c000304100030311a0681c07003c400794100e1541c2e0403104009001c5488001144600e41c0d550b03a42c03d618000006106090016030140c0144048070040c0c0c18a4008003220221141079441029400c030f10807200000740a50003010b0411b41c1048180d002e418034001c02810300b8842120b411403291107500000205004c0c00d141e0900b2100f0802c08039150744520b0f0301400740c200d00280940d40ea0a4541c1d540039502c41e112160b0f88011404400600210031104000452030200c1d030000c103c25403074000d804441e1914101c019010f01c1d42e94000c0c0760404410300015003c2c01400d01d00b40000c450502e80f003d0490559001038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 738139496 1250 738138246 738138253
    0xd09021f0e09090a0f24020405040b0f0a1511060a0e061012150f0c0c0b090c150c0703080301060c050d0f050a140c0a0b0603010c0c03020706030f0b1f02 67
    0x30880c0b908001907406186900700400161340c1654403800104001801900d2910780940081c40d05842950b0510400c0c82c401005611107103070105200c01d56500060285c4035401d801522041e6844241072a421a01c41e9a95042c0035070495000790391380021003552166a0251004211840f200380e046510419000c904807000c903030382c20204540c6203078580200d0803540844120440440e401c0010420742c0c02e108c4800261049250108a04444c0540d20039001718071040c11550900c50200001580a80300002a04903009002b000540000301c50002c0d00c0701c2e020105800d0080c0a0801420317014641c0321402035520350b12940f01428001001c40101c40c244200060740e0f44c42c0348a08503280ca140300d01d869090170507040c444195000e00340f140300a08942402e005801090508201d20a80c05000320000a25801c01105050a440100c6905018403018002000000e0b6001400500300c40d504d00c1c000a041e2070002c078000c06080310041c0c1d5903002e40ea040080740340010840c1500007286054088 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 738140746 1250 738139496 738139517
    0x533120f1501051c110711210d05030406090b01120b100e0f06030114160809010b03060609090f010c0806040c0e01140901030608031210090603080a050d09021f 70
    0x115044205041001c0b40007031001e20440741008000000d540140d034580901103803114981070741030b6254001c00030607580c4003401d07403058046042c5034038000805600c4114009003243d4101603150380d400c4d202d50714010010000005424000554086244945c0c400034030000781d40d68099030500d0b08c045000541d440e4003d40089081d0820420813001181c446080d02c0b5040d41d900b0301c0108919200500303044c1c265403100c2e000c0181d035070700150b050f10904440800034074202940304001d212340c2c0010441983c41e85094030000c080e039800149a40c0c8120212007030911507940d59401818a84201c0800c20250708004c2c5021280b508003906511a140c160b5003008004a550021282c200b0a6249c281c089041e030b100b2040d10110050080c0a141410304020500d9540d80c12001d00d135600c001c620020f1008808240540349503500f80f0302c4002e0100c01c9041c01207c2c21a02d54210902c148001542401030029089003c036400e50401006150020082186040700c242c0724007903202c0522841002500c0d0040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 738141996 1250 738140746 738140761
    0xa0e0108120c0c0108061801030308160e0609040c11010203070302040518040c1a0c060108061e0c1c060b0703030e06280218030a06090210090533120f 66
    0x142c500c0c102d0361800401150010400640e09003402502c0d10f40c00c1a00c140015000780c5a103000b0a0081d482075950b644103140081c2541800c0b00c4243d050000c02ca01044000c00320740d1940180c0e211030b00100c84c00070b400078074004140d69008501c1c5a0f200c49500100403c41d005070140c0c040e1040360002e031500320700c00d050701015480440f1300300e600424203440014103026110020220f20fa4203511440703102d142031060460245030240981c02010254800c20400c1000f0222450550030050720000e40c4100d82041500e0100700e0192100c00b6000c081c0d402c02280000c002604500010000008180c0e42e46c00c150070024054204400c1a030854442c07840816400c0850b410500c25400e50414100e80641d13009015070041d6101005c9041c4499a0701026600c95409000302c1c84a031748244800140110035106200c034094905184205201d0310b120204095200c1d4480610100340d4459404400071300542d8450018a6895402d90070030305c0403c481e0b0303411071703405170a50184543e900b07808620350b01c811 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 738143246 1250 738141996 738142033
    0x70308040609050f0612040813030506040c17030a0804020301151d221106130f06110114070f020a080f040302130501051005031003050607091403010b0a15020c0a0e0108 74
    0x244e40d02e80001c0c04002c0c0149152501e15840d80003071051600910704025003143d403250b003246802c103464507000901404100810200d08000601c4074610341045007462054680d00d80c0101d0407540c0902c40000005011590207512940000c103220340f617034a0b25511403590282504204404d80204112400801c400d054540c0008800c4656608284c1000404d0703a100003070849031808068014005101d00d100d003815449103075014020044034585090b291100080141d024808400400c2c2d150144000c0010040d0001301d600c108141003408100602c03401c02c070b2424074008005415007002003280e07000c4580180080084900884920007504012690790080703038002c1c0f00c0d107548600320070011543c0900500103194801c0c0b407810184201c0d070b80ca03103804d802c0c40030440b4420000707500c095051010301e01003d0322000320841a8020000d802440022070480e18040c083e5207048507a1410880d0164801c100728060b04502411109105665041301400720380203014a403110300546030103400c0b488101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 738144496 1250 738143246 738143269
    0x6080601020f3409090303140a0c020604140a0b0a0510060e0319020a1211040c080f04031d0d0501140702030304080f030a0e063402101d07030804060905 67
    0x3542c4050b4036036812a0044a8990714103d00c2d0310300d603c40039000601800d00d01c2641c130701354060780300802c80307901c414444204030100a00300d481d02da10f000100040194005506503000d42d100394a038000940405030189005090b14004107500301e40010407000121980100e4003035101070307404100d002e440340d03002d0780c0b4880d200301c681d9056440309500036101d00d00c0d60303941a403042c0094a00f800182c0c854242201c0402d202005998082180a0340e0150307003458480c52203840c449141181d06820310b86030882d03a6000c05400613041021000081e6240d00d445d225a016801d80203010000c4104c661420901a060f1340151001440c1842d0025800354008002c480c403e80e03220b90700c14500140049401d040c0d400142400170320907501c41d1048002c041c1000194041c1204043c01c002d00000550348151942100c101130a140c210702d0201849180c000400000601d05101e0104203201115500180c6000d02c0d406c200241c82540c00020600c115000284187c3c0c41c01da03a404036058a4038184440200f80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 738145746 1250 738144496 738144523
    0x902040803030a09021503150a0512031801111905070e0105150d110a030b0a0605090d0b130c0b0301030c0503160324020d0204090b090f18100606080601020f 69
    0x3000092000365260703119460440c07004000e001504005150b60354a50011030365032034a01c00808942319280b420711002c000070181241c12030168060b409000d0303124000e078403220401c8540103403c80610fa0054250022400308582218a44a03641048026208074500e007959580100000420121000390141303044e1640030f0605044e040400011261560000d4503071f0401729070b50705071401760075803020060503001c0b4103690207d103001e000001c0000b20005035002000380704007003151102d103803220754003c101260800038442d01035840d82d81d00b005040302144010400e21030540003069a1101d1f80255040e00d0090b0588080c20707498005041d66450792601c00010842c1c207a2041000944044150070301d903108459100720100380603400340c1a80c01110705081025000309050000040c2d40c410b0540005045500012034284000112407200025180100b030400c250150f42c20000d0811000d89030003030907001005031966800c3c000700185c1085ea0803034010301605000c102c401000090b0500c410a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 738146996 1250 738145746 738145753
    0x3080a2a0b18060112030c0503030c0a030c210908070b0c030405100c0203120c0c0106180e0601050a05061e0a03090b0601050c070e060102010b13020c0105100312030203130209090a0c09020408 84
    0x1c22000306017040441c44110108081d0480120000d0820300c003443c052211400003c0d02c4084164000c3c0540d10030031078407410084050101059040310444841c41e2400580c00015601450b0520503658403c0107000307441c8800501c184420002058000d5104a000c0c0c4203941c0788659072191b503019940078000e814011382c800d114802c032900d10b000520784c001803400041c62130900d080127120f0a503012940980341c0d0001428140689141e81e006001803221f010740038081d55810a00020441c84103809510300403030000c40d0342020000913143d8005200400e4a1032030b00d030100404006e020784400c4004480e02c2c24910007041081d4080d10030344c1c84152000e0090310055040160902440710018809411503481e609030200c0c68441e104642003a0118045c00341c1d583c02d80074000c9080d540003520714201c11a80c44020004150200c0d10b42110820504d001360b038980f41d00d00c40d40080c02038041302a5100708880309000c1c01f000009449000284200c4402001c07941da280140c0880c01244100751140d013 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738148246 1250 738146996 738146999
    0x12050a030813060e0f010f020f0d18200a120f02010e030123090d0c020105041710020408031c05130f1b0b0a030609060f03080a2a0b180601 61
    0x28041d580ea182d104000c00441d040261098031410b054440c034455a0304150000c9407040d605400c00c1c003a04d803190044800c150728200c0c2e40d4802c040399116861a4044103503036401c111200d030500c02c031340c80005500300c500c0c1c2c01341c081480c0d00f15010000c8811118441d00c1095000200407a584181186140e042800f1482500240d001911858032030550300d6859565002c84800e040d0020b44404014a200e4580f181c0b141760803000706d407a04542c004401f0074440803006040c0180c4c2d010040742d0640300d15056040e103601c1d00341080c0d458401d8481d0302c000c6050000c0340218600e4400005008503540361a500302401c42034101d040101e65043e148407190b4000403503880d0100b1500ca045004086c0b1900d08103440c034240040320400d52141d9000706103001400228001e10316450301417000038004415080000500d4951101c65030003240c800100010808a071090405000b40b141082141c0f8500c00340302010022441c8030b0a100102d50201d0b81d0002c0c1c42c0200c2d1840d1a103030403501500d0181d000600c0640d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 738149496 1250 738148246 738148253
    0x3020f0108040c0e0c07030306090b060318030c0d03140f040209010510050d020d090212060c04060f0e0a06050d14060307140303190804170a170a021e04030c12050a 72
    0x20000400030344032443d40800008030a104040b1a901c900c00354072000e038961180345401419203030349903c08009181003c01c0c280300340e501c0034101da402c04000c420b040480484540d45a00710700800714507907083c0c0580078000c00b2040e0543c01c4080d030345075202c00f03110b000c1e0b8641c10b1020341e920741502c0c041d41201b1000014410350605c200324980d4000d640c18800d0416907042650420380c1d002811049100c0e440303010b0380e004c5050402612105104d008003425203440c200400b000382c0d0083e885800104400c2c021200b01007801941d500005100180100380300584511001d42540d20445858458500d000c2d194040b00310b0440c8164040c02d00280580707201d03443c1c4050605441e03503500d06923038940001c00054600d000342540040c10b1030782ca81c494090038906403c106280325907141c4c001100001c03c000c800035150303028898101c058400c84035501da0383c4889030480c0086c01203852a07200625418005600c244500c0042c000700c03441101d41460003521142209040381403440c0003000c2d86e20900c60390001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 738150746 1250 738149496 738149507
    0x906011706160f02010f2f12040b1506070c0305070b09060405060c19110f0114070204090804080a05011407050a050703051606060905040510151809140615090103020f01 74
    0x1150b8842c400400c15400d4080006c044410b01d90210440d44007192072800145400c200c1180c5240c0008030003400e00c0c0e0b2003002c0000c04071000b08010001c4460600040c044071004420315900e900c05005261200583c0c07410954001060005442e50b1007103520005100300300e8001ca60001c0001b034aa6402d00b0315000c10702000ba000602d203000310b40a2420400008108d2020284445004003010304244400c00305000c0e03d040c21440c85410000d10410015444880030b0403100702d01c0c4d06803030016a03010181440341c0b05001e1a084070509005066040003440350542184158011400c864516030b25810300c10344280c0300d64042500400c0c0b0502a41010901030405401c1c44039007018060a102c1807542c60350200d41168101064031981c0e04140004c0c00030400c6810b1243e00c80300410811007001c682c842e100c071083e0344168114040c240103e1070800819410184980364001f040726040c01060503a2a150401119952003100c0034044d1289a803410503507040c120303034000d04550000c41001004455 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 738151996 1250 738150746 738150767
    0x11505090a200a030b0a1a03040c05100e0f09010e180c0411040801180804290408070312140a0f02010912090f050a05060a0c140105090601170616 64
    0x4485a64440081c1100c1e0a9080d240d064240811050355508000b0f001070102c0d112503141602500d01028244071500005520a820342c0518801c0c035226a502d141c406a0030780c1903002203402c003403414904102c50317130800d0007181081c808444d1501c041c3c4e280740900840b41002d1044401c4602c51201041702c00e10092807104406000c407041c0c4140d107a413140820103540000c000c80c04894400101044604003e1080b8002c810a071122011135002d0f07501c40c01c8031405140a05130100d004402d41030304007202940d503244141e0300700102c2501c4a5440a001d40c4848a9103c01d4550102c0311304c1c69254584100200080101609050b03401e015800c401141c240d81d0310300c01c1c1d1065658403a103080125590300ca81c90904241659015007060421200003500207083c1c0c131090103081650003d0109036648015100d0004c0d0034a02500050840d061030795440c0c2c81180f03201c082d946800144030b00c100e00820b1041c183c411001f41d02810f070400d0224640d8840b0308640c81103120380900601da250501c2050b1420 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 738153246 1250 738151996 738152011
    0xe220201091a2710050306010c0f0f030801050907171825090e190c1e1526061f020309030d020d210f06080105040501060801150509 58
    0x245070503200c0880007070280144800c041242c40c08504080307560301c07801200b05401c80510a007000020043c01044468004408400510402000248646c1d115010691503950044113088640305141440180302e480101f00358006003a00f8004140b03070800402c03481c02040d0f07513624081c0100541c000480c091001a0895529200004012142d60000c01c405086890380c00301e00b22040c41d00b80390400c0102090741c030025205082000d600b4115201088a0070b40c2c2d4440d510703c8000310007614154481c16017a0b000840680c0c10740098843c041c9801c00d212090350380b460006d0381c511350740140541d00c0d0b013030340c501101c0b042058041800c4c00d920030795945900842d018043c0c1c66002c0e0b0a21410718071030090000b2000590020810b40300600e41041004084030301070001e010031803152a8020a00c100681d818682c55540342c0301003040300441c1d4001c0c41c0d81425a5000c000c403940319520300780a00b1054801350b13925030801102042e240d1040c842c001079201c2d40320031564005d00c0c11042c403031122001060b58 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 738154496 1250 738153246 738153257
    0x60c0f0f0a030b0d06150f0f062703034e0f02040909170f03070c080d05070509120606101b0204180317060906040b060c0d11070e220201 60
    0x1c030f039911030780c56040206104a8006c81c0759401c0c854207007070310700c2243d100d00d4031010f070640300704003403e46100c4200950301189042d180072102d07580d012208010101c0005200c15101c0310010034107a01c2104120900c4040201c1d81c0403044100040300b03c280071041044107070340300c5025602e40845000e407000324a4181c15001c14000d441245240480c3c10941c00422410f48030030559003017180e202d40b58181100c1c0d00e01c206050000720942c864550000801c00744c12720607003251301c0c800c0c0410700e41a904404c904035020b101c58680807030005c02c2d50704501a0a030250960000d01c4c0040c01b8042500ca1040d8401742903603940c542221b82c1100c40f9440c0d0012125403c803210306540141e1541d01034518101b400782d4041203c04c43d075150080194052542000f001410702c400d01c00746646843ca12500079204403800b00314502c010340081e8040c42034512031680e51280c0075080d508541c2003801d01c118880f240c0145c4010380d0b9221002001008122a1640c6d5100149071030f41c00c82080140310b03c402401072420 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 738155746 1250 738154496 738154511
    0x20c15040312230a0213081212040f0507180513050a1106070605010b040e0705040303020d1202040e070315050d080708211302090105010908300f0705060c0f0f0a03 72
    0x202c25010310f00740e0303d0010558000801c0011403415000820040407800e0060400e50b5071558074505034065551030440c007541090200d828402224914030085801c5003d54030102c0d91100c86107201a155a9000c040e2402c2100041c005840c00a403980941d80140140c04c00c00075680d02c1000c0c451100c0419503001c041882042d020a0300c5208541c040c00402c101250744034100415492030000042182041000402c81880000d50110300340c086000326041030110312707030f046000d80040d002e240c01c1090a0500d1400300703d039550b80f54000b403861070109201001041d803180140301240f0320541c805481d05c0e004200520000e0980001091141c403002e0400c08546078151303d51014140036100e0310581216403141c00b00350324007102c01500404007400c1c000c00c0185403114446e22500409090310f8842c40703912071901a40c41c1040203100e4030340724103500e6980b02c0d80aa0488001e800c054400c3d100c0384201070000d802418a0011205600b1210043c1410120141d68480756580081c01d01e0303081684035400d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 738156996 1250 738155746 738155801
    0x4050a0e0f16210905150115030c050f0c15010f080705061803070312030f14040f023012120112140102130311010f050d02070311060a020c15040312 65
    0x2814002c83d040c100d00440d040303046052040c9014104094194000b940d8001040380000a541e105000d00050801142d292180e050035191401000c0c00d0200aa4000070308400c00000403c0018158030100c20700400382e40c0360800000c8080362409610070343d5202003070034030080c0f52610123000003000100a0381c42610001010904101c40d581c81100c180f0000300f181d4000c1c0d5058000d84402740a02e074020002c090002e0a803c0c1c084d000548068200d4040041c164155110b00ca0301011124500b504580f400000f40034000001e100304080306014090b21014a49040000e82280c500c4150281c0c440b001d6401c3c640000c8101414650880c1d000c101d00d007240c0038101c0280094681c1c11828110710048070f01c0c5040100101e14585420350402c64070f00b004003649034000701a550b524400d00300c0161144418a425034040703d054544250600c038010800c00814415001030001e60190010b8915225402c070780164202000e4074028003144a803404c00c1a0340080c0c1c0e00c03590383c03003000c3c1c0c48007070800e100e454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 738158246 1250 738156996 738157037
    0x702211b0f0d032a030801090b19080709150302090c091f0f09050108060904151806020919061b031403070c060e240603030405060d0204050a0e0f16 65
    0x100e01059888508213694004202044071110074015464200704060b03500600c0c0c840d050280e81000c0d641e803a00c1141039195426010f486102c0600c840c50815140c00d40681e407540d2134824008c0c01ca08000101c4080300004030f00301c040302e5000e880c0c54100c0c2c80c1c542c11506188c1260003842c2e000429070018007915156000040900e40b82501c400c1100240514002c0c250800c03500b00d00e0500102005000e855210804c2c030650003030700070711603000304441a203100002d030a21003d0403034001101a02d00080c090154000c150401c400c4602102048115000b2071401d0350714810540800c803280f00c46034001810307001c00321510b03105e0701c0c4c1401c40c0b8240b030100c003090350819100c000006900071302540070410280301d849540c2a060005218008410000c3c0666841e6003030f000440307540c2c040114040791010000d41c4e02030440104641e803160050102d000082d0441d108040c4a050040400180902030007107980c01043c8915541d0a03c0c1d40d88201c04100000c1c0b40d960300304020100b11000c1c02c0c2c01c100c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 738159496 1250 738158246 738158269
    0x406020910090608060d0b071409030a080d05101a0c011b12050c0309030d09020d0605010e09010c09030b07050c0a02150705120c0a15110f0702211b0f 66
    0x586a026810f801c3c00c0000385008402449a40502990304c2040c02181001060302d13441070440c036162290709403200ba0070f000d40c02030041040d0184210101c080402681b240a003840d1403110004018503550201c42d4102c6641501c0750031610f4003003900315510010104024042d801b1050008601b9400c01d00f00b400031204030030101000130f07003004c901f0f5034481114003452390442141000301b400c40c00c000001741d441307201e50004505031b01e1b6504440c070b0031174a03005405007049402090070482580d4402074200121000c4601c0d2080e940781c01c400ba91031300e0107a41e080059079003210b041852030b074480d0410f6420383d001c8244e940032449800300351001030351142016039004000518142e1200d2040c0303030a5240c0102ca0490070f07400c0c841031120f0700000382e0000350241c0a0742c000c20000e2883c00b84c01c0000b002401d50813105901181c0c0001c3c400f03004d15a600c0280070003072003a1a09080c9100c21111303080e2080541d0700140d03054111086e079007074034038000226960a41d030003401c1c0c4403412003240002d090107560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 738160746 1250 738159496 738159529
    0x150a030c090b09060a050d03031b05030103150c09050405190f020c010e0f0a06090c0b0304050a11030102091f11190203060108161503060b07061e02130b0304060209 72
    0x1100070700403140c0d18069104440300507501c018160a001d8002641000316024003070040500051034020f142c42500a08200d011250800f030b0404e140600041460b40240421780700351104405420f01c902076071040c00daaa032996555519894248010400904005040d02903c1c0c418804e014518105c188101c84441d0141500180c2c1c7e14101501c0301c0c2075071020707a488080c5400140c1d070300000c1500841c140078001c4d4802d2001880c0f030228900860600c0d41c54100340c81e00100030040000704640051442240d50148880f200280c110400301070a07031007812f0017240c03c02e02021000411040c07000408143e504507040110300071600725110384c58440092203000c4600103c218180a500f4240031850141c040c01010380340300001d141400d50301c10740910070040341e82c9486090740c038810b2081e0302503400f401c10549002c1c2d8980103410043d001d0401c6400003500180c02c0c1c01d0810030041c95208469101c80c0f0854408513072443c0200c00304181e000104107a8556800708a860701c0d40c1d6030040700300b00300501c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 738161996 1250 738160746 738160763
    0x121e04030b09060117070305030708030604060e0106050705011b053a0209190506072901030302030307020105010801020a0905040209151b0f010522050a05062701180308150a03 77
    0xd410200e175a40070414503840406e41004038144007080011080301c074a1600454842d03a20f4030380e04081070040282e94070030420701001d00700101d0500d510100030001e25029400070311482d00e2280c0c50728100d0745403529450204208001860900441d07910200150306074000c855840600004c404100c130884070100b0426650000ba1007807a86000440e140304d0707200070071300c021449081101088603481000c4c00a0080f481c00c10300303002c00d0000c81d000908002030009884d145541d480c03902039521b030015211140554200300c004106013805101744c07002403115139245800d052070102030100030b610415100360884d640c4801b01c1440c81510000300f00c200e00f05c1034162103010006071540d0500070700540040c0c4d50703410075050194488000702910102440c00311380803100421803a18030715182c0c5a00d4000c0c010300a81042115903000781030b2088000750201a6010784180103401e0034204e8107085074651611800d4400003010921500b48182d0203080c0c000520305a09144000440210b5550b00440b070410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 738163246 1250 738161996 738161999
    0x60d0f0f0b150a0e0402030c0d0c150804021815060714070b090a230603090c0d051c020304030f2301060b0712030207230a060615020f121e04030b090601 67
    0x2400c0f01e08034002e0480ea0000213a500303240c2c3c00a0384400c3c034151401d11400158000d20180314600b01c0b0034006140301ca0005022000003a0064400217044070243d2142030221440b031154442d01c08654800c88007852180118904082000810740000c001658400b100c141004400c00c4100242c10162103003200d440c3e10340499a007004003034000f07500321407220001d9144081400d0306840411020000442e0000d0300c81e691f42e012039140c040e0644c0000d0f80290907540c2d01c0d0031b1107004100e929441010204248004040700803c3c0c0c0d80c0d00c070714840200520002c02c65400030071884000d9494840c0e03140324150309890000a66400d5420640114050a00000380842042010302011b0a009910700342541403242507183c1d140142002c140da40e5403148008031071507070480c051014920850b070109080194030b8650310340c2c410400884d0500c0015109001c3c20345410300000421001e80f41c0c4090b4400c0c54491b071360407811b03111490514220500e01042c000440096030551941b40300f031541800600c0e040d07 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 738164496 1250 738163246 738163249
    0x10050306160f030f020c060a0912020a08030c0a0c0c0f090b041b0e0f040f0209150304150e0304090504120f05160308040f1209080105090303060d0f0f0b15 68
    0x110016081000034412000101c2a07a5000003480e02441c1003401c000801c161220074200c0a0b2080003d01041c0d40500c0040154014556025411240c010354101510701e140a900ba640c1e50030458000d005100244002009000203400918050307650f460f080c1c0b003580080c3e0301c480300d403509030f00301d1540300d10030400c18003110306180304880918500710343c144810394405400100d46a00b84911000300003d01c9c1d80b11280f901c403040d10005e840c070043c0082140071a0400548025002143c40030300c204d150601d0841140d040d1402d6034001c5c1d4000c94001718050002c4c1064005281043c404141d502007440700040129151107400d00c5207001e441504d44110005000501c0c6440c000d0442c000d0203403d208005034411131003d9040403560604100c80c4035195428031140e05a074045d8014104402110441c14056029207010b04561061002b88030b161a0014003644a010454031a40c1000100b804000810201c00891010303a000e0300110603008041c0c1c49001202c00200da00b000030b4507006855040302d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 738165746 1250 738164496 738164503
    0x101a1608030a0f060f0509280c09140109120302010603050109110f010c080d1d030a02030933220e2208030f04080c0706020a0309091517030d05100503 66
    0x1c540203c41c1040101e00303040b40c0c101035620601405c0c0c01200d40304001100010890114550740c0400c0007400030a070070b050001d82c060800500f5100024991110000e9840004030711a441039130145c58001941b07080c90841ca4101410700b006904641d2280e00000c00708a0030310904050034000c0406d004849002c406000407030034500a40f504010482c8412004110084241c40103001a80400319880c140f189035814000b4481020b45494000041c0c5104100c1d00000103021062090307a10803080d019903c1c03401400a62084082240c89032a5032050301940b500b40103000801c9440d810b10003c0c040300700c1444100304203400c994001c3c04020280600d8075144407d800d40031000e0001940081c105581d213000a00020301103103500302003400800d080100c0c41c1c0c20381c1c800d206604102c80701c032a80d65170003e6030b89031b8a0505401081d2101000b0440c802d4034007400c1e00a07074003180c0701803020346000001501c1036100030301986030b80024414070b0005043ca0013030500842d1500300d503d020604001c1003505 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 738166996 1250 738165746 738165761
    0x2b0521040b070813290c0c0d081306020d140f090f0d021b0609030a08090a120f15060b0705010905060c12070c02060d0c020d17101a1608030a 62
    0x10f1069000800650200c40e40013034415030382c030000105014064409054001c4080f0030040300c040580800c0186040030794000e0621101c4e100200e8031016140c01c41a1855181035845c068000100852580824031940040122011f46440081c5141c0e54484600418909603411036610004100713000f010f01e410018010700020020207840008249007000c0d541c0c0c82588110450214500510200c6a8482d0165984094007a0984495042902e00f9400b940e00c03a02e0428800d07491840d01241c0c103950981e00c0701e5402d0323000c0d101c01001ca0b800e440d0399001c403e036480c41c42d454607260b810116080c0c19201c0074014452048001040030081443c04a0820700d004110316404001406040039200b404000c00c2e80040035030812104000741c07800851440d12a0f41705041a0f5070400c0300220072a940090300304406421641da6902e00c5411b4002c2c8903042a0903903c0138600c0c02481014441d08000340f1030380e4020b19a1001e180c2c607080c4910486120440140010703241c08501000b00304034000280100b00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 738168246 1250 738166996 738167011
    0x6120f020a120f0b0409050a0501051006120f0b03010f0920090105010f03020f12012103052a250b03010312030b0303070f0c0f082b0521040b 62
    0x182000038602000740700900700c4815111081d101c001c0c22000340c0c219400b031120008040e1007400110800d00380300d23a441180b1882200c0640c60a00042c5500021803112020340e81c01e9902c0c1c020f904000584140070740307104440564090744c0c172603050000740d909103c0c041c12801599404140215a42042e911854500744130700c21a40d00c02000444c15512032502c03e040d18001d080214850f500034400700c009004e81000e41c21000b60001d4240180380c13429031064101c0d04445d141c41842c244409041d00d64041e03180b80140890380c01d0201c0f040031025903416595114a030101c904c000e0703174545031651a2500200e4080410162640303030441c0e0303000340302c4403170701404800c1521441c0d5450341c0d0303501a03001c06801044081690314030400d1010703076040c002c90f100e2980010a80402482034242580b81d10302e1072154641612a4071000144902c0c081100c624040c080e00c00703821350000d440c2400705050520f02981003000010407134550000d81a051400c082c8400504d4600c05141600d0047e1940502900fa070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 738169496 1250 738168246 738168251
    0x4051c080a0c0311040512070b1303110f030c09181002121006080a021303050a2d03080112080f0301060807020714030a020d0c080a060f2f0f040f06120f 67
    0x9001d1030501e001140c041ba00151032214104005c08105070819456800c021300403800064642014032007450f58000381d0740a4540031116400480800c40483d007500f503055010340100640500928040014540c803084010b240b00340c0804d40e9101905003401c150f844d002e05540400c4030068034400030131045e444800e4509229050303060500180040c01c0c002d00711240c0c0380e0001295410b041c2e6010580004640c820f00721000b440c2180341105900c0d10a400c80791616800e0b401a4400741e080540c1d8071265505511200c02070b0342400c5a4038180c03c002c40f0160b41c1204200004080464040021070081c4550382d0384040505041200a0511303210303911036003400e105644e40200641d00441c03110b00e210707030440c5d605802010310715144241407944e6100084500401c0e880fa41488000d4100d00710f0b00840c910104040c032410305482c0148141a5031031007089c007d03000d01c11904a0020010030100c0b9030700020905203a5030311303540c4101b928a134002d9000100e0f0051450b811120714010224280c4000005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 738170746 1250 738169496 738169511
    0x30409061d16030207120c052802010e0301091b03050601050402041d0727051207060903080c1518010516050d090f08070b010f17100504051c080a0c03 66
    0x6a00c00518058244000c82d60801214507540d4000d90407540c403103a100b51080341801041c20301410201001b8003c0d0303100d0103a4411151554969487c1450718140c41c0102c3d0441101c64004560341d040708150550190360b0750000c0b03004510080c914198100c0d2558034440114154500242031010682c4540c0c0541c0c0140414024400300c004488003010301e110500d030b0f00b50340700702d0119103c1c0511000721406440015030303e000640c44510000503560309035480341d80c0180040e0000e035114841c3c89498000340c580802400040c00003002800b0803540c000840305c01400d00440c01e020a40240e0303450300c0803d101011041d0443c420701841e0740c0304e8602c0c0440c0e182d2036600c14000d802071141800c020006542e40000901b040040402003070895000b5844c0d6456800c02e1501707801c4060203000388902d440c0310003800200f182014042e00c070030b00f0501002d0146d0042000b404409060f0107041160b030390054560005804012602d24241c40106a0743c0040c40c2c189002800101c0318211000301c04c16040404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 738171996 1250 738170746 738170789
    0xf090f0c08120313030c0b0103051c0e060301091d030a0f080a1b1101060b0c010c09050607030906030f090602030915150901231905090601091d040302120c03040906 72
    0x60702d80c8221034a00e09502d11300c481c030f42190020a2004001e01d220b401100120500c813000409030030556480302e103c0c0d09500205401c1c2d9410340c0022000c4d610400c200014065400b40c2e07000b4003100554031640d07a4110030b409410a0841d0003100105000546440d0389811141c2d0051900d600f16589810802041c2490410b1016142c96420483c06110001d03c9030006c0000940c800310090407038091503a110382407420128041d0203600110000114218004200c0385000d00840b2219a490703141c3c0c1c442645082c0707081e40a004148000a40d8581c1e03550814042401800118454071059001e404e40001f0f20b009410001c0c00509209412100d6840801d481d495254400d41503581503800850b484080340600f10039000316660311078000a013240c1240c0340b20340e03c8205100356001159070700c5c1039540b110700454103c10b1a10401d568040e070800001500724408400a40040c060303c16140350300b80301541c421080c1d00019100e9000e40c03002070304029002591141c54041c25800100e00ca21030340300780 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 738173246 1250 738171996 738172033
    0x10051b031602030c10060810052415040b070c14130e0703060c02030c07080c0f12010b0603070c05060f0c09090a0b0306040b010e0702121902010f090f0c08 68
    0xc05260204812411080009000f0001c1e02c0552500b002281e441130b44845549000d040c4500c00c0a400b031041e480c25003159201c90140750701c100c82c506071180c0d00307076840e01c0c1d40503080a50188007500614000c00c05400404468003c00c0074110801c400c035074803c118900b52013001d00e20b41c450000180c0c000c000c001950388800915140c60202d000c0424000720390b0440c58181082d90784020203645c07a040000d89003540201c0546080800641510501035981020740d0300c9003404003c0c2540402d0417113140c0d581c0d03e04842a0003103c06c1c5000005011035001001c129194419034140700403c801525480812004100c041d50040d03686400300031908100944461501800f816240303c4c2d080800010a1020320340e1207200d00c0100181150300c21b040c03070b01b0b086000344000e000300d0303030300b4501d041c0003175621130002958141442035600f045140c02c602c00044040130701c1c8400c61a00719500c501c0000d4030b000c1705004582e00e480c01014500e1302c0358003d103072001c000d00709544151100d0f00001820200b410f60070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 738174496 1250 738173246 738173251
    0x7020703080412021c051c0504050307180e06101514090f130f050a0507020d14030703020c03041517130b15031c1b08030a0c020102130810051b03 64
    0x40301596060034044c800500d110484642204c40600301500500a02100186440d4030004601404600d0400c1d80c0080b2000c0c403d90244d0b50301903011403000c002510f0a2600c50a45000984000843c048035034400d0341408015900d001201110700c0007488084080030012001000e1030601d005210401a0341851070302801254034400e074204c5810048584640810b001c4d49043c4002c10824021034204000040005554480d89d0390324260004032458000a2440910074850311103520b201454170301480385601c018150030403d40c090081d48070044007000904007034035644400d81006014498014604072042e005580307055034080911040600d01006900e40076082003400840b42d851445420140504102c0c071501842080201c1c0176501035142803110405595545401c00140b1102030203c0c407003982c44c0600340d103d041020602c00300303080d88030082481042c0000b40c00c1081c0440d48801001079903200c44c580b40c0001d141c0c092800030b01d106056005800c810040108000e1064541d42030000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 738175746 1250 738174496 738174509
    0x6070f03020a1704020a0b0d2711130f0629130603090602070c1805091b1903050f03030f070c1e06090b16030e0d0203070b151504050306070207030804 66
    0x3d4003050554440f03201d5a03014055001c01070b07694409030700d0343c0e60091258190068540f90003007122041501110701c0b0092051b0000401c5118002d40820000c0c04040e60b460840026914000c03c4880c0c82140180002005c1544054031542d00000b00d80c4d10801820800c410a0700040002240382641c41258a05550261400050720b00304c0d031801c9002845841c82c042c08003004050002001c290704e000310010a1042c000501071501c03507400b590341d00c564041e40c0c4000780250342903121f02c1d130030302c0c480825200150746061880c0a65030f44945090040400d048551030f0400410418104841030aa541090b00e40c60003031022002e546828170048052412020a10850112142807100d50b0300500300c00c0740c02100e0a0418144405007046500c82c089403500440c2c2000d10b11040f045010410850581003034002d1450300d02c007550758418040b4001d100903e030038807a41c601d860581b11040001d243c5112504001c1d69641031100701450210700804410447d80201802e100003849082510200e416 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 738176996 1250 738175746 738175787
    0x190f0b070f05150108011b0801090209030a0c0b2a0606131b180803090904020f01050c10150e07021b01020f030f03011a130605031302030f06070f03020a 67
    0x240351600305410a10340d0030290981c420820f10011007807001c20100d040301c80300c1008101d2005442450b05401040007900804900c1c8100100a86c60300c0350010030ba120030003400d0320900c00040c0e6603c082c44c69941c2101e44603041c0414620300c0030381045409820000081c070b4a002c0480590750703c507130fa101e004201c40c3c001c00c03030740241c1100c4101369084200c4c458910044509403410001d002880d44034407917044c2000700e000c4000003c4484010045884440020703150200303aa84035001c2c003807040c00755990705040050810000c5011a0140402540c0c1310000c00003080105606841c44400c007e1900505222032130f2005205070309800290312150a0580c1c82c414000403541c03c0141d00b8200d5541d81c9423081d01001070403521408210000398182e81d8003000b8030090264105988246028020200c540f400c0c58040030b004a07030042d409150b10541244410b002580d0590100b41080c500050032000c60b440340d8140410b1a811220305199101a0b140450800c002172000428096059445661510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 738178246 1250 738176996 738177007
    0x703030f0b030d08191401032303031e070e031c03060f0e011701052733220308090709050f07020106080a1a070e100509190f0b 56
    0x1065410072105000c00405855801c0340f41d010240c031810049030881202d60783c401a0a0f081141c9104d80c441004913595600341980c210342e1504001e41e1014024446815082804086a9010030066108000c0c81d00d00d4205545400c049102401c000743c400390074000c581d00280d0b401c4d240020b11990364000311140c000618041d6130706400600c420b030012880403040c2c003408a0b00100700340308181254501366040d07021343d6440040380e08071a402c2d50080011f6040003a81040c0410415035406d0340469041030394103c6112900c882e41c801c2c1d2800c44417800303c0302400c070040c5010400c082907a0004842e4100d80181841c0c01c070602c103075030403980010280301c03004000c54025101008100c0140003080000c02503400c00b00b81412034400111a400015030a052000c9869000030441c0715103554001040d03040d04807280b009090310400144a0400c001400b40b00720080d5545040030001031006496565503140900280540102d9290200e11b00c595011801c0004020f000c150b04c0441d10400c0c60140c542 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 738179496 1250 738178246 738178271
    0x50f030a20031f090c1e0e0904060902010809010c080a020a05090d030203031609030503190e040c0908160e0402100c08031e07170c0a030902030f0a0b0c030c070303 72
    0xa00c54101d00c603600304010080040d065a00600c021030218030074214500f0668541094003940c1d1622215400100506060401001300c9080c1a0380d690003418800d90031045100822403a1804a50961345943c4400082040d035030040452174020107110024001952010b038094a62200600700140d020381c0042d103030510a114000380d40040c0001003140030036000e5410003d549400646049029110180200f0310050140008204076540400a5401d026429040c4179041c182c40c06a0814821200c3c3d00c5a0346590b1442854030018907a1280303d1110f050424081c9880c1402d5100054440550340074400c11a00b00f00c2ca45d405a411164107031101240c2c14201d400e0740c81c0d108014002c0c2008800c2c40114608542089110102101c051000e641c0740070381216810019082d40300b12102400105400d00b49030b60081501c02024140440c0a181c0d0380d0100381707008001c0c24594070135000009108100030305404401c3d00880c00c10001d0742181450704003003d0500c5150801014141e031007801d218807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 738180746 1250 738179496 738179531
    0x906050331020306040803010f0e01030308061003110c0106170115090203130b0103050a02010f030209010c020d0503041a0903010c0c0201050a05090103090c030506070e04150b031b03090703050d050f030a 89
    0x907641d003e4142e074840c1c201441d060420b90000c0c010300b44441d03010721012481e208180e40b0f242c1240d4041c0d4403440350fa120304003170200c41104800004200341e01c900c00d150307940c00a0002003501004000000440c80c0c03030a843d44480e416808484140c5905042d09110310407111031150b41524040b40006950381c581301c14403d15580c020b00c2c0281105001c00c000400e000700810080401c070b000f81c82d03040903054518822401c80c4174900ca410301264034006043c002d03041c071703106489826100707104a9250648400c0507028090100e003652007411000100040207081c20f000309281038006041c500f2a1104ca5800a031040c0240d034a01c1c0c0800c01d02240500440c1e2080d041202819040041d803c103c07612820000c0d100e0704221010004141e5410159074141880d10a001500900901e00d0304002d0804542c03201690001e04080c00508651038500c20995505000b507016454030002402c023070f481e40c0b07845418010741070b84034000d00c041400440e080494501c200c036800348050304002060070340708a40c00407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 738181996 1250 738180746 738180841
    0x507060f0e010e07060f050f1c060504020d1a0303090a03030f140706020405040b0f03062706100602120703091a070609151a030d0c050312070507020109060503 70
    0xc0942c240840c01d0311160004c5000c0301911102d03a26900b003001458403e44082c4115408006510010005144100003240d600703000340c032101c14045102551040010b0030b2360010042d070f0300c516075540900c004024400c40c983c00c01102c00c2e0081c42c1043c540c900003901d241d000d480702400b402102103040201038881d6401504401e00d0b414000c1e100c020368180342000b07402c0703401082c1c0100d1816203003030841e29262010701100c6070010014045940c0d0701c031700d07160102004005130034081040e203003100c41c40070280300d0244203a0b8120301080c020b510386000240740c05144240806104404c12500f000309520510303100c1a00d04108162440c0180d0180800d00c130700c51200301a20551a02981e070080060b00944012001c00e03003142845481a0785105181c1c200d4007103040c03039241d07001c032000600c5203015408200c181030080d07040e00e08001540f904640d007018222046400924005088021580c215000401130203079440e01d00c1c00d5180c1405d9a00c00411840d20071509400c3c56000e025200f00002c07880381 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 738183246 1250 738181996 738182021
    0x204051801030209060d051207050601030c0b1810020703080d0f05010b030c2520100306050d1121030301180c0e09180d0203030103150216030e04060e0115080603010c0507060f 77
    0x5035209c505060650b200d420a000c101d4140d030f418100014142c0c09102aa03401ca0b4003000c000105400b240304100c0402462689001903010710f000000c00300d04080c0140032400340c000b001080307200c11051004100d4005810030786130800d0501c03d1000c6120140c081e506498504851550349100c9414000c0f140310340d0350001840c0518050b040788082e00000d40103141110141c034080c4c02e40518500c02da00b03076001b44c02001c1c2c00180c154036900c0840c10b40ba1484001c224082e1610a03a084041904203100c07400350300018050340000010000896402800300310701c003168400704001e110101c001000301a07400031080c407981081022884001c2400c941d892030398640011580c03001c042001c0a9242d41092205684900c140c3c0072a030400b180600807289130968280c501c0303d0a00312a5025100826184c50458100344d881030082420b201544643d07020306800031a140c503d002481000705103600003440c01340280d040c40c0c0c61100142d088801d923281c480e84402d001c62015049104640109222030011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 738184496 1250 738183246 738183283
    0x11090402031f050f1027030b0717040807080307020c0310270302070509040c081209120a0201050a03020706090f0305120123010e0d0c090204051801030209060d05 71
    0x14140441d900c2c0a40c1030b90000410281d041c3e81c03101000100c0302000742d201d070130800500c000c5040c20b01c80c9a80060721400262880da841c0c0b072002c00c04d09019503a41088500300c80041c24489025000010003013415940c2c070303060000c0c1c80e142d9100780d10b60240860003042440040041416a802031120400c0c19074041e048038400e040c800c001c080641404054109624903011506100364440500300007069016001001c0780c510b02018440650001030080c3c40c980901200400c91980038804212030429400903540c0b50310a01c42001040e5840410f80c1420754800c0b841140181d03041780c00c0d00d1102400c3d040040c1c8440290030031070054200d800c0001c12070310780701d900036080581190240c1040c015182140310181c0c0c07903080e00600702d86c1c0710914000041c20307070825005a600c01c0c003800da82000082d043c802d060036956a0004103880d181c20800003160049000e0116003400381403030600c0207210004074159495600400c800301c001801444c0034a0785071034614103000041058082c4840100500c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 738185746 1250 738184496 738184501
    0x1020c010c1e080306040e010b0906010e0307030b0901150501030b130f020403140616020714090414030a0905150a080c090f031e010b010c2a0b0703120501050d151109040203 76
    0x480c00c0fa80300300e134206c0c400d5280549081d11168144a4240074075000b0f030a80307030359449900054030310071144031889605126002011000540d000a054041c0e180040081081130040a01c0c4209031010341001e810186441d40e00040c55035501045420384040e140c0004a00f186010390303001920035500081c20a2441c01340f0708258132070000798148225584482030001148501c0304036298a818418030551424812850f03010b407030034000068110f8400c000d00300c1e2120a45041e1411a002017107542c020400070310081025003840d0340b0185880c1040040305240840118000c1c164510203050341005840100300c10b040c2c0c0d2245114004140b00c01001c0769103103403d5080003940300f0b0242c61460302035400e0007403660655014044820240380d1020031081d2560400c030401c52402c41c5410102c00d01c2e0444c0c900007500c0309141c4010300006000b5920b400b248030070b18076400182c681c107900840c0140901c1e820341c2c003c07030b298882c0c1201c00a05c4c0840460050020b41100929006d21200d466129100105 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 738186996 1250 738185746 738185753
    0x1404030302070f0e0c18010509100309050616050d0e0109080f0a11030f03070507060b040509100516021c091d0604141b0c0111160c0807030201020c010c1e 68
    0x81c0b02d03003101c8103400c441548a484806030301c5186001d481650a000c001d105810b00d00f200c3c1c00260b1a030750010301d4510309015a1000041000e1030300740070800407a03030b9810b1410500c1828403042c4e901007010076411007081882da40060080c429003554619035581c400307801812000a400c007212882d089440d29032204171807400301009501822445000c15604407548140c82130101c1a10840000341003685c2c110350780e00200741c40380da11550003200c2c0142e550458070b01e6070740e45100e02400341064070b00800d42c01035001100703403c45102801ca1451a900c0c20145414113500081c3c07180982c0300c2000c0c07580a540c0070403090f02c1030070550f0400d0315440c802058905e103000900f105144500011107040c48034421000c0e10300100f20058400303e50820315103a01d1208108088020020f11900100000d8030074078a01c0000400d0700001050428503808081000a0058014076040684550005401c80601e10b0f0700103507031002c003000d459041c4001d281035501032000030001c41000c2e0b101c002482400307005524 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 738188246 1250 738186996 738187003
    0x10b0408070f03020d0b0402060c060a051602070806010b09060c010c0c03091d04021207030c09050f0708010b0702041a0409110112090c1a090d0b07030c26071404030302 74
    0x1034108a8030400d40005050000710010310101d036006007805070843c041780c45a4a2003240140242d8001ca01002200744011082054030b100b4a440340d0001082c0c10501440f0107080c034070007400c00440d40035403010f00001402160781411100ba0610555480741140c1c0803442c2800b858510b030340c207540781a4000307c00c02d4100092402103803003951100013090721402400c02c1001c088140141000000340040c00508003500a10f40d00d044050891f0030141d5a681d4560f030008850f0402c58000e51240c0900961025415203030f034100f2154204030070b09604000c008403603030195a8020f0f124648a0f00200c11038a005178042c415144050030a004d800d015050040c001d4201151886c00107043c5030a0206803042403041c00c000c0e80d400018480d1803440c0c00c2c40001c08c000056400c0c9071402040260011300e6941010741c42c07040780315400700035241c581100090704a81c02c43c4014014001284041881401c80303480d0100300909a00030076025440d500021115208070300c030302a1840d41d001402009054001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 738189496 1250 738188246 738188249
    0x90504230a0203120c061305031b0a060605030105010b0711010e041416110d11010212100806060406051503180d0201020408010608010e0706120b0a0f030b0603011103071d0603010b04 80
    0x1d030103e0702513880003e10941c0c188036032001040d407030b0040030124804c050707012200d084141c01003003240e007090007610860041320079403821800d441c1c0c0700001a10400c66103010391402008200c008100d80c0d0b141004000007840350316002881360614168910b61680201c4045502c007a01038401c1200e5a0941602c0007030040030383e09070b2100400310380042000c500c40d950a0006014040141c2883c041a01055400300303424064110345540034080800d4603e00c01c51031034440d0030803502d03041c1a11b16003d0b085041c2940540300034015402c0c2182400591981c0b455418040841883d0a40d03d6440e900101110140c4001913140c2c0d0181072040e0b24181d6054000d003041c1c400c0c2074001c10566981b21109400c9503da0400d950194005100070403c0500078146007408100501020824a141900048031108071360013114411281e00414024060842c1010f030b80701905600030410622130b02e41c050500c0c04000c00703010400c24260b1031510518400e4400410544020344101d4503541c460500d862740d508103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 738190746 1250 738189496 738189499
    0x250801050103150320010507120903021c030207260714030c0a03021809030f070c1a1e030601030f02030c031506040e0a02030c0412030804200a090504230a02 69
    0x1804100b050142160603e00100c03036016400520454940c03034003404456034000482c2c1444414410000860a10503d0820a620b5956841e107441e09510400030180c00118401e50700c68181088600040d400150690a032480400c101d103449190101c407a80e45c1040d441809028001d0350000039641140807021602c4038021401e50b4400702d28141070080901091001075401224240700084240c0c4c1403142c0b6801000d101d0a40340b070103054032503a8549901c4801d007110b00d020b041c0010026041903400b01403034812042d171070510348a8403020300010403080704504c0d000640000040740c0300e41e000703505c207000d02641940d0a549900c0c152031300e04101d40003116200904105002c00900c145410001c48050b180c4291031080355454520780701d0025040100413192480040101190b030410f00190201c0d101e10030f5903400318600e000e00e4195640103600e001016450440d1500141c1c5985504401c0b00351009120000b80c1790f07540342402040089400380700e5450303454010000201e007101050250301c0500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 738191996 1250 738190746 738190751
    0x60603080c0d1b0503030609040f020918070b0910030b01090504060b0910050a02060411180a0905161820070503120f160f0908060a021e09060a08250801050103 70
    0xf202035401902d00f20140024155001000014418034003407040780d0b0018001d041d900d440c0c0a165000c1b458280060390b4041c5450414428004541c03c01c0045001030b103120910790b41040b880d24007096001001802c80000e0507214400b201c0c0a0744120100c1d40140402002402603d984150102d2140e110501a9014694031034001c650a401081212901c1940798000c0c0715a540315143c4103014584c80a800768080c0c1c1040070040004c0d0007414141c05000320210010b0082d80d985032403494484090841600079014135002c11030310034881d00000000c461000c0c08501180f50341001c5070000b10322810f60440c0c06004c2101403d005001000e4682c0a000704d40b003a200e40c070b4520400c918840c04440c07a030300c060400498039404074400e904061512469003031405409880700340742c41c10140d0440f040445250b020401c00740b045d407500b1141c0443c050007020745140c2a00ca00216049115000208080c040008049a8808582002c1c0c2c80c00c084034007050065440c4108000300410001e00c1101d002a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 738193246 1250 738191996 738192017
    0xd020409053007020102030405120a0501021c0b01020703030e010f05130f1805040f060e0f100c030b0f0a090c110a08040e06040218240c0d09060207081207060603080c0d 74
    0x600040454160f983c0580086080034640f030100f29075160364000742d01150043c01d4110000503424000f6212040300ca00c0040d4030340f110010030000b01e900d8036092a046512440c01040401d030821126601d02e84280f81c0207286000c40303a0203881c80d12403540803030741071811a0f4001640c030000c58094402d8400340b115041240040050000580c2c1043d6005041c1034440b404100000b00c255005402c00032031403059503214400343c2e20540c10000e0b5541e6204003070b6282c0c3e0b12501540da05120304c040040046801146203d10070000c2410004030380609a1001c3d95100b000c030189010352129410020000c040300d008454900c0c001c0c4185d04584034444400794020082041c41c0f41034029111000c11a880c0340e2090301c048000c000200640c64405034a034202d000030203020350620801010300c0488080145410885001c00070082142d5501400071904000340074004484081815249082c1c000300054440c085400c00c2c0d402000c250784000e2140c2d0000940d28148440030614507807141e0309460781d501c0030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 738194496 1250 738193246 738193333
    0xc1204150e060c160611180405070207030807111807020d0e04050112030f050d0f051b030403020312070905090403031b03200717070305270d020d02040905 68
    0x7442d003075540d0a030340c18050005001e030030843d00200d915a40101d502254a00900c4801d080f641c0c0030b10002e00c070340f00c1c81c149078110394203190007050b810004910003000394a1540c3ca8407501070280c204001c22400401c040e4003d00d03a600340700303c80c451034144010078607820620f602950301c00021030707002c02061031010a50268603207482010304035042e541080c2581902640e08441c900c0b030881880d0b040c44000e011030103448040d0300ca4180d215071444000240ba0034120310701409040d900d0041d240401d002c204200000b80d010056801c001400c001e441015180c114041d1480c12035904104d80048403501048141903060308111008444070b010218141a003100c201d0a03506803519038800c15400d440001c210700700c0c01c0018948580101c115170704d00c41d0034100080c0141c0c03022900703400044002c5030817144c02d07007000044080f4480301015140328103050383c04983c050f8100d040192098420201003025901c95400c0404000d5006040d90440c4911160860f00444001c841d0046108007080300443c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 738195746 1250 738194496 738194503
    0x307060c0807050a030203090f07080c0906030a171e07060204030204140103051c021e03031e060a091d100c02070902130905070c060c020c09091f02030c1204150e 71
    0x6600507a0b43c00707240041c11a000d402030350000d02409458894011000100c400510034100a44500c00144c103c0d00562010081802030203042c05100b80c1048a080b40000c0320100309200c242440c0d0521601c80303080007448900000065411090444002a0b400400507154000c0c000d403803080f1000c101810000480c054900824080203100e6031000e40c40c40e02100681c1a0160050101e2040f9401c4a0400c41e14540c80f0600303020800a607070000c010301007919420300000800420f4000c4101440c50300400107418480e49109140c641c540d5140002040c1e172000b10551032a0f13076001d04584003100f00440400003013210600b14001170045400105070840d042c000c541801610016800583e41000300c02d10040c00041c1a80050201b055080070000b40d60780501600f400f8160040e001c90710f40c203010301c003001000501c425000c0d0042d50000c1000c5860321494440072a140800503100ea55481072000070f4440c1d43d40d29000850000200020000882218210140000c00500071100050101c0742c0c5c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 738196996 1250 738195746 738195751
    0x110322020d060f090206040e04030f0206090d050313060509060105032a041d07090c0815060a0c0305041e1a040303171e090a05120f090d060e0d020307060c08 69
    0x140408600008000b0600680244440903e41c1c8030009001180340d0000b44907a12031340c0900d58050054003048103143d0050351051811032a4000741101b46020302540392203240240041040c0300300880896035051510480c15107095201c6000c00c03a07414517002d95030391501c1c2442850320074070034101900070501085005580040515903141d00c2c1103c1c0208000140145e034194015020700c23400c0e00c000c0003008010620080421400000d1301c20200034000b4400380c001000403602c01e01c11443c54640c2e440d10380c2298a54215880c0c502d0421030549000c803030500c160f0748040034907040a0581040b401c803020386001103503910504d01c0e13000300b003080d07030074006000740c1c400a0081135908110891441400e413080b0760101b200c00824420a6017407921070702c8a02d007510a1031165202c04190020080704000e542124440e04003050300341114242e529041d03100380700340136000c4d01002000d2801c0103001e4022030110b0307000d4000e6582280d04800000d540b0342000c00161a414100064554101d015951290 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 738198246 1250 738196996 738196999
    0xa030f05100b0403172803110304020607140a240b0a031a13060501060e0f01110705130617010b090a06050a09050408120117010f0b3111032202 63
    0x900b00380c5540c0b184401c0440c05c485000b00a0410810300741c11114045100000149aa00d0300703c2d40190031400804031503440c50381004190701082880003682da40c41c103813904c150780b2003981c069407a0700340b03951030400030b590341d0003011041c4100e4424000791242c1d03c6800c082c070f040e103010440140136004001203820148401303413628103150820000141c52002055000c0c07580a040c0c03600c2c0c529692a00c00702d0384268050400901c10a00840040c6480e24490042d00c0c801d281c181c2d400028150b4454a482c45403284170b01c135087d6078024440d52200b07604480020b00541240d00d0003201c8035401076001c0c01c0d0010b107007807140e642d010004220f440305104240a03210301504084406050020107801071001034820707a40d0500c00c0c04100801f0700c04c0700c0001c0c085d1460041c00b920082e0b41e90480d50948013160b03080300209041082500044d102c1043c3e09260409560300f10a41c501000c00400341e08201c11940c40d5036900740180c1403405060b1000860040d50f08144e038422408041c103911601560941c0c00030f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 738199496 1250 738198246 738198269
    0x14090a0302040b1503250f020627060114150f030402011409060a09030201120605030c1003022205031b0f010309110a080105060306060d2105040504020a030f0510 71
    0x24005428654400305a000024044490030000c01c0b02413682c9404c212004408403113200490041407080035500c100403007440c14003c0c00106940d0b0302035144e10700107101080c100f1070408400e528a400d0411141095545000e5918a584a00000c070307401103c50002400707103440c8a03031041601c44100072100d000c650b1407416421070315039500440310305840e00385c0030ba0400000d02c804a095a203920041506450a1703d603400075034a540b0003d8811084600c02801b81458075104110315240032484241c03080080325045885840300e94140c000380900e01020a1907198103050766545d14680d400d24040d250102c049500310703d01100b40101c0b411140c3c02c85604440070082e03141c541d5000b43c0ac50600381d4031522108000700340000104404000650202041d40c1d103980600c2a0741c1028484240c00c4072042d100304206003101e4491240c100900b04610842c40001000000d0461069064401078240100107655407600110020007400c00300320011011458000400c3c0041d02c0800408e08592511014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 738200746 1250 738199496 738199499
    0x4090c0224060a0b040608040203061b0f09040216120909050c0d05070e040c02250e0c0705010204030f0c05090a0b030615030c0901091b030621030c02030f0d14090a 72
    0x20420801c8040c0a594021404480120780000400003400182500c2d54a11049141c14010980340c00380180182000c502e02c9201508102084021035260070302c0140400d90342c20750707100403030020b104156180c080b05403070b0380c041000c02000b03483c0406038005550700d51035100d45550f0540c044480503100382400420030080311034140b200d604034aa01001d2410004000507200000c07800303880729001c882d001604408001400c4c0000c1010656400c184004524410740c20132244180d41d250182c04e50580c00c80214a000820209404403070145a019581c24498185890014118891b60085901c039040040c00100c1c0c00e0510b22035240d0014000b00188111f403a800010b041040b070107195940c05005000b140300068030f41301c0c040e40c000e10824000050800c0800e40040c0d07541d1284901204040c1000f0081007030304030400100400d240c4c4044085224501c1c3e14003561600c40316900290107020704040303403041013004214440c01e080d150700c8607140c0008001c1042210f205014083e607000100303410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 738201996 1250 738200746 738200803
    0x3031302040b121c02070b120708180a03121a03060402010806130e070504230105132a08130519061e0609060605030105091501050904090804090c02 65
    0x201400c101a00c00f06501410120880c1040c80f14000100024020800c12a006034100000c1c002044140c5041d402c0034402c052001d0380303002c0544494100501c0c20007140030000c000c948040b0000c1c910046540045083ca4041e0130446803049907649113203400748010980c807094156034062079004001d495943d072268015111224040c09094001c61704a1680ca807142d214402c000500c1081c0c0004d01c6040d244c64200015038134420101441d480c48256070040b02801c00700c0380c0781502e1b401c0300c2c01c0869a65460a0070020000c020301c800303000580702d8040c442d601440c1507030714010089603151041991400c41e50307035040007003d50040a940c05140040700c04403040c019803606078440c03440400d09080c6107030030035254a0980c102110641e40d8040030803101129101742e000400c00e0781084e80c155071400300001c001c03171002801c0c40d00324807429180c4402070784903c045840301c40000300108090309060401c440c0907001805100c080038a41021701051600001c0d40c00b0082c501c01442511040700703400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 738203246 1250 738201996 738202001
    0x10140c031b0c010e0105010f09060e0109020c120412141c0e030102070212060f090d050712140315090a111603020c130207051510060e01021501090b010206090303130204 74
    0x540c000031854240b255640d182420b015044181d0a80000442c0035410425043c994492039400011345614010081040008618605044855000d001a01c420281034171a04111992070003580890000402054a8290000681c00d203409070151074a103944107103880e0381e100904900345042030350101c1c0300c2031280e1103002c3c0740b1000340000e0005805c04800c1d90105039a80c0501e1403180040d0000c4040000858004054550000001004120340c9040c5d0001178034500c100800a800f404c040c035540c5a03da40548403120151090045940d580d1802c140b8421800c244c400d00c1307074810601d000100d00d0350b4480307010b09500c0d0f45003811040d1810009400c4a0350000b0764003400c41c19401a071888507110340d03032480603a00a0200d01c0d40580d4843c0b4038a4030300d0401c101da0500700c1d9545444024003026070106d080c00d000f920f0322810705803400d00545005070302e08030305440c20003c1141d03c540041030803075580e080f5052080080e022944140c0300c02c20380341c2d200c1c002200c1d004200e5542403241e1001d0701d01038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 738204496 1250 738203246 738203281
    0xa050a05100e040c02010b032b050a032a0f020a0b0a0b180a0203040210020a12030c020c0915010e0d030806061605010f050f07020c01020619061710140c03 68
    0x241001000c001101001c1804e40b0000380700b0034003507556003101c00d166080900150700364004050810b000c20100d500c07000c21103107002e450002004001304845038440e000f64092442581107440e4001110081c850051400c90303503c00c1d080000d1030303080c50350980c9800091101101540302a506245660350301d0b0f080020143c4c0c6440d03607031102d441d28030180392100716008580101101c44000d60303a403400317006000301c0340320005004e01158040c4c50031001042820f0400094203d03645000700301007401314030480c40c207854034040a520511810910002c013601e40989800a94203880b40400310405038200712402c3c001110240220340c40c0781c002003452500e132004200000b007905160b01104000d4449500b120382c001c039400b11440d55070040c4507124001d072074410b42c000c20a1000705088103034070703000030345862026018a45141d660341c0c1c10180c4880c50b0300b0920140c90741e404440c82c06144030000304d903543c1c00b81c03103807d0883d0b107401c16048094011403049032091840301c001a1860712100c0515101c0c0424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 738205746 1250 738204496 738204529
    0x20f0f0c10030b06070501021e04060e0f041d06100b04080a0303020a0210050103083609220c14060405011409010221070c0512060115050d0603060f0b0a050a05 70
    0x360000383c1c0c81d40d0781e500041e15280b40250001622010f4030031464040301c0c01000c492601c01b03001d100402c810340c1d020b0070001d010301040d18813842d0400342c0d81c0810080d11103807070801d5104e120344007016515200040c01c1f034482c00040c2d41111610b44d07910741281d00c1e442540a084480d030030031040003001c41d000750000c0030317050010320445031403151030110002201e8081c1c100b141d9400300007a1010701004903030703500810403c02042844800b00318031200b030b500d044100c403000e0181d0020f00000e8000072030b500c664030044856008116020350280341121181d0154015002110031115030755142c1e04012003a00d05640060310b5142c040c00008494444d1900a01162411449941020070300b00d95458030b41c080c640c0c0340700401e584030304151030046c1c0ca64001da00014000c0c8444c04030804010700000d00300b41190642003010301e0b902c1e19114119094855550310360942d6007090800010001c20381d00c4501d007040354401c00c000f100b02c031000700a460402c504c1096440401c5030410302031803078405a03143e40340c401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 738206996 1250 738205746 738205751
    0xd0b190b0708070b1810051911090418020307080a0203060c031f06050a0e0301151e0b070c09180c030b090304030501090f0201030c0801032f0603090d020f0f0c1003 72
    0x5039540c1c030000030500311420171000c0660442803c9280040100401a0112200178001894804900c400c10f840d00c0d113000b581c058540b0390000c5c0410740034044902100340a8001d0143c0700146403030180c1c0c1034108000301d00a118290300003c1c90a000314101c44880d6008000e018a40c0b1070f480d1399011900702a21225070103e0081819000103000c0555000402198841320340710701034410042c280314401d04005029034101020400d019510340361030015606401f98020a01424203150800c204d401e800c00040c40000060085c24007601c5c14904044030810b05080c01950440454145082c1c00210024031040000c0028800a0003054420354052000401c803800c01e0342d0703600c905007500c1c0d108100350723100207a042008066507414001c181c038007801c500b071156007540b4541c1c03442070f024200500e484841400c50601007183c507800c500016075a80c0241155200d0030401d5902d80c8500703640401da4054410103500c3d07500030001141c52041e00c480301c4040c04608011409100701240b03150365034002c050303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 738208246 1250 738206996 738207007
    0x13030f05070602090d140106090b060403021003060f030c08070b0a1704033b0a06120f02040e0a0209030d1e0815062d070f03030c03090c08030d0b190b0708 68
    0x4480e14100c21400d4000d1490325540741b40351a140e82164400d0308909091414034240d0030701760b1205d4040714100d940c151034a03494411640d6040700100010b40140c1d5801107241e400000b80f00c01c00c912181600c0c0c001c42540e070544e47c5d07803048190340c0c480c9500402c0842c0d05031615041002c4122032503584980241020300b0902d1800d83c8450b0450031560301c0e410170000c0081490301c000744401c1c1c00d071080b0b07009071949a815410325201425413900302d92140b5040c4d40303c9481c0000c95400b601541e00a2140d18070244150030400d0313030030019401002000780a031040721260301d0094811a464049101450040311032000002801c807001100180104105481504141d90030344496008000c6c02c8202e542d503c0c4160010a5640300c41880c00b0510004d4240034001e45020924003002620140c0d0306040004290b200214103a004d000f07030080141040031001400074000902000605c500100c000d42002007603080710400000041e011405018004a524140070000d900001084441d008056460030308 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 738209496 1250 738208246 738208249
    0x613080607050c0712020a030206030403120908040315060b0415110a050102041509060f0509030a051501060e04060e010303030b0312070c0e06031f0b22060e13030f0507060209 77
    0x4241e8180d00000d00000315048001000d000c0003025020041c600903a080742c0b80c002810076003442c003000c1d1003583c0001c04102014011103c03ca0718281410b401e1250f103001c0c0c1499000c41c2c0051005484411802820828010b02d03485400203440560701d4aa00b41818000305020b89139400800340284400906111007400e420850700340054864400580d42d1400e181060020a0003610800d00b031090807441400b019403c50050042148646401521000a0000a886c0101c0844040c201e8003415662a030005480310480341603030030380c0d02c90340103100719001404216403244c41600503124101d801403000922036008403650340001030464005070802501901c2e25841000e00310382e01d00c00598100722008491990b503600610403805048500f021003000c510340708001a8058407942c4d503851210b80384d81c03101e005955913040020410034203000940520020300e218042c0c3c6010380c0c401e0780059908854805140e0f103507a819174a61409030f02c024800d5400340c00c00c80301216000d80030b115000c9103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 738210746 1250 738209496 738209503
    0x4030f020309150316020604030509040c0c150c0207120807110d1e06060504051e06060c070311040f06060504090504021f1d010806010e0f0402040305060f070329061308 74
    0x70360304205502c40d81c078202020b15402510791180c0d61790554200f9410080426003000c10394620040607140494500c803041c40c01c8a00070610080180004c080401184441030a50701c0b4049034245502103481107620392810403403032203503080000c2043e0001c03c54a80050b603100c445000017600500480101340059841c0c4070310041c14918600b08200900308101446014003030304c0003d21080da1b040020b81094404401c04c04c01d5120040c20a10703504001c01c039681c64000889001c449500f064a5a0340c0d124034112000400c6440214455400c004000040348264407540c004c07518503031a0541b6203031a1500c2c00010b041c0040059a01c0301005040807040d0040e0f18082c0c81c00381d120350310111b50380305210200c0422684210000e04200c040401c01c42c860340c00140110031000300b119110302030070514002402910603a040140103001da041801382c3d07a1001511540140d02545003400100010190f642580e03690814440395503003410003880e110704010b070041c102013401ca0320014200f525001c0c031524 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 738211996 1250 738210746 738210769
    0xf0c01021e070b1509060603041104050901092010111207060b030d14090f03010b0d0f0507081203130305190509191409070c0f050706080106020c0904030f020309 71
    0x7500d000030040d00b0003407028686503210401d00041280d158000020032000c90000700124050304c400404681440301d9070500702c0480400500c2482a4030b403258442d03008e081d03071110484d83d641d80c10140c001d00c0d050024081d04610f50150460b602c64807030850844440310341940c0503030b050080000010500700031800901030a400b902001c22441ea116080c5441c005820001c00300700301028001110610015003182e03807000301100d4004903540c000300040e00400420b0b21903a44425036002c41010000304041100d0068042d0040e1a5003d42d5500c09644a50081a840204100800020352041d80c919610750900b030003850034030b04285030a10060780303004842c00c006001c11000314603035000b0301d484807140b000d1040d02032038040032910704200c003501c070250b081b05280700b156a00009044680709030b0300e44800d07903006000c00001141c0c40c1401922601a03004a900007101940045007903400016010300300c45020b003a0380220f58864504550809a01c1c01040850204002d040002e40d00c0208100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 738213246 1250 738211996 738212047
    0xc0918011d0a0207030e040c020106090608070509010b07032c06070b0f0a090b0123030d1110050124020f0d021014160318020a03050a030201060603110f0c0102 70
    0x3000180d1140300004480080103181c2e058010002d140010350321a84c900ca8200b03080d1000b082c945544081a07015100300d03000f40400e50f1405d9000502164001114002c954058686680c166226101180030380300b0600050003007000c0200b08a20088502c150300242503030349480b001c241c8217010004003507505c801ea080d59410901404d2220640041141d260011600001004148540c1da145203410205105000c4800c1e01c005410b5011074000c880d40d20744544c001c0680e1040a000103024058242040d4442107500c6580326a164440140c45902e069565280c080500c20030406401c104c0740a60504081c214011011001031190080184101c50390f03a41e0084c190004440d00c40d04212443d07018403081154080c024040c910500d80e1001d203218000d45008584104504035151018800b04d0000350480c01c41c410001c11310201082252042e0310035030082c000f481d44e88000300c01f81e40e1f448201024180e41080742c040303940c0c003060080915020410016061180d9000010341c9003030ac5903810f4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 738214496 1250 738213246 738213269
    0x2070e1602010624110f01060806100e010506042904060309050c04060308030f0403090302061603031a06091003090615030c0905090a0f0f02030d0e270c091801 70
    0x2500c1c0c082c000e20303000d001c0c2a030f1500707024000c008a0100c10400d46148506012510860849415042c45103010084400c402403008a940701c0d0b0780e50f46c810040b203108440c10201c44002c02c880d4a680c00090484d40d004000030300307150401c4260310030011284240c00ca6520f841415040c5c00c828400a00000c001035100044e20b40c20604000c0d080c40c1d220081d45102d40e2504000740000340b031a900352a0841d40450445c4441d80c1e80d40707015184901184c0002e5844100032030308540c1180c1012420568070322071354050203000500c0c1c21002c203111150394600d5000c0014045080c55042c0f580a80264840c1c3e031030702003442c01c540e442d40d8046a103085a1140c0d10303142c15000340207000040e54208020002c6c00d030204901d24141202e181c60305120394008080c140035150308014000e611207100741c0a500203041e19a144250300c000f40200d824240b1050040c14800c00c442003202004240d4040e03141c14004a50080e681c0d0382c000d448591169100d580d11405071108985e0700c008114106000c0c0c100140c80707 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 738215746 1250 738214496 738214531
    0x111c110307020a091d01151e030501020c03040f12030801140a0e130b0709030b0f18030d0b19060c020904050a08030103050a030306050411070b2707030c09140c030702070e 75
    0x2c5c1c5031056021040e072810b44e0500904544401210205000701c5415000a07084458070f400002465585503101400d1980003250304640ca13000880188200d81d5011104000142c2d2108030f01c0d6082c005da43c002c2c0c007281407400108a103229003284a55001d40040010003016110300d510b1445041c00c2d280c0d10002502502450b00b0005103005040c3c0000003402e02ca034100b40303140c0c1c3d694020140103008000c020112000301314400d10700c000d044202d02403e4180c0380c4804492040d0001400e503850700a00c5400481da03680321002c2410b280c0e00a0320300954900d0840d2610b0b03001e03c0003000003c0c0003181c45200342414070021075400320146020314030640203001e1400c068180182500c4087c3c100340d04c03c92403ea03040c0c240e00d106400700c40040ea8000700b4040e1950f665407541741c0c1c841010100150b0300c1c3d0111440c50520380302203003550a07240301e842103180b0aa29440c01d84201c1c4c0c9803030314401c80c4400700b4011455041e082d01c05035074090103a204640030a0344400c16045a000309544555045c60b00001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 738216996 1250 738215746 738215771
    0xd030516030506100c02060f03010e0906063c030604050706260106030c03200a17131e020406030f0b18030f16020d080703111c110307020a09 62
    0x511410801507071505104034140003002440c040c1c4144107031002d00c159143d00324215201c14055a00d0341c090110b1042e1203603900c1c06002007051084904450b80d0088400003130b0a45444a2030807405402006000121a0700c0f40000e2903c0300300307000c1c2c80010494000215410764040000c64415842403015110359440c05c030000e02028003074880a00390803040554031641306200303144181141d40f0780ca0b01145000030b41d5015401003a44500c0c0c91401c0e581c0d0602c680480c44840010500d004056640600031721707100c00401141c107400c0d5150700d0706c03d00007806400440d220300c07440c07043c07040c0340ca00080d07009101e80d00060443e03c09071300460f0745001d400c4012007481800d0000503440940e10150804090803130260ba40c403407007007415051140902080c005029403200c0030460000f5809010444500064244081113030000b1008800180b8000c01502d0038040202e0420791004008041054210219034299038011140305889210b00c000d00841002d0381d00e01c480c620082c10701d4030300010406030052 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 738218246 1250 738216996 738217021
    0x20c0f07080109050c0136060e0d021809070e01180b0105030f0712140a09110a0b07060906240e0106090e0103020d03140304030e0102060717180f0d0305 67
    0x18409640303649020000c5010580214034610703080700c2441c203044010700b0074245c41d148041c2c41c500281c48004048050047e155925044029030324642c85800003103d03030004024883c5c0541c0f100940051500f403120003510521454640c10010703040688103601d07152680701c000032209a00c48800703605941151035450b4068030450001139028a4400c0c60362030041050300d16508090011020042040c1c108010101240e20107402e00c445140495130324144481110081c004580c402c2c4e4092070608200c211074503003425804101c5003408041418401e0316100d0900400b5002e07016913129860b0100300c40c2040c42100b000145108041d40c02c9015410280d1000c64008142c1010342444401c11090080181c813020301c9044070741c12500e80c0010100303460200c038100d01141a0010200c1c0210502c001c0540014001c800200280d088503829a542941200c0307074000741610080014003100451850690f01c00d8800392400c8100443e80c00c2c0e40c914203518688a810141d1500090f540c030140511004c008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 738219496 1250 738218246 738218249
    0xd090e0a0509060f041e05070f08030705060a0c020a1e030f02010c05040302061e04030b0a05132307050307081f060803190c08070f050d030c0e150706020c0f07 70
    0x420400c41442c000044903900d0201801e089103000715040014200280030300d41c84450140003e460022503141d2605035583c4c90300e40103c01a10701c07907480125201e2000401c0e80d140d143c00800920554403440050b80080c00c00000c09003c41c002c4008200c0444d039414800840340911941c000301c00c89640c1001003841440b0f5204d40211390610760480c1806901c40251015240c04442c800e80c1e59801c2c146039030498820f14403a4140f080082000414010303682181807152000311000d00280e510302d00b055000900004000f009401c2402407101c00719101c210403d014841c0100b11552140c5074000240741c62090743c809205039001138988072095070403030705488608001c134509008642c10100d545483c3c1c00307621440a200c010700403142c08200d100e00101c0094513040030800da520202410103940640003c1019a07061140840191200f8441c0c4076030304000106982d407081e80030f80c0d0000c0100c031702d4803031403d2420b40720280305c0f24000c20440d200400e021401100103120760568030016031f050211300d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 738220746 1250 738219496 738219511
    0x20606100917160f05030f1c030f020903070308030a060812071209120606030b0f190b01021212010305161d0a091a060306100311150c0d090e 62
    0x5101240603079002080c0d90180d0b0340e281c04000314542092001032401803c01d0070844002900d400000b440a14403007407105940e000c1c1d00f81d07030071601000109661402c0881c011020000d00b0548154050f200794040072441740c81d014091704d0001c10000280c40c0070f050f0f07001500c2d02c1c40000240900080a441000001c150303a034050a41c51a01544070681c50003000e030050409810f20344030401c164030030140c0d0800740c00101d044d200a50000e0400c100203005c140401c031110044200801c20320516a02c10510411812070300c50883c2e007007140000b000c1d01b55040420705500c20304440c00b420500e04001740c07454080101d13810900d5891401c04500e800410400381e4020415030f07005000d11500c03589040390300600d010b10400192641550a0018105800058255407030440d1850400d4022842c881c01410300300c044030104d4803074125441e4030b0313681844000c1900e40110020032207401e00035004901124207114807420324020040c41d07400c04c40f0100b005000a41184414401ca9030380c0c0e2580c0d0f070031186 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 738221996 1250 738220746 738220759
    0x30b040513030801092c160b03060306190b04020a08100506030106050307030b0d0b0f0f06010306080d180915030605010b0306010813020a0302120c09010b07020a06180302031c020606 80
    0x2150302d010f07142d040180104a0840e803a450122401039101d21410070400105080140030050102e802c3d8590390250070300c62690045413400900038441206907402100f005020700803545548051158540011104a10440d1a07100041c880d61307651024000c01c02041d00c920a0034600800c0000112125400080c450070040c401880703640d5221043c1c1c0c0c3e100585090004a40005030000707000c00c500d8200080141c0c20310401c00c60700481d1402014090311100701540010b4548100660603076007a4000c50300c0030380c00b8507003c40c2c20502c582551001c00c0107510012100588410b000010340d0401918485000c0140c0c1040040243d90f11699005018a025481c10b60406500080c41000301405060b800800d200d508003d44da40d41020a00660380100a1480e01010240c031540b152203c100d214841c6205800000d400c1c0d00b03031400c95110b1580104010b5000d4280401500c440c1c0780000507a03600b20700d2640201c0180c03420800c0b410551045400c00c046071000f541e0091030400d005080500a40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 738223246 1250 738221996 738222031
    0x417070504060f0e04140a030c060e060f1b040e0406020712031e050601031d3a11031b0c13090c05061c0501030b01080d0546030b0405 59
    0x6a4281e0001c05130707a00700c40160080d4440f8108180202c9003222010690b0140c0700c1010201a04210180c141074802d8009201c05588032a45944640040701e0f0801585c0c4403400058064100d071140c81c1040d011429143d007003945402000c1861041203030202c40d0035500080314414041d50501c10203203050b41d40b8040c48918800b04003403c002d80741d02c0051001d5500c5a010500581c042c0c1c01c1012001d42c1d12685e00704581084034025074451907501d4002644c92641c00330510904403001807a101c6e0106442102401c5d6090700c03c13a03504074804a02d81042c003050051401c04030740c40390303000845482c040042010000d42c00422004016050705415118900028040041d518130584d904603202101e0050700c0700c107260410401b030000381600c00031543ca00000031080140310758259050301c1c51034044071902c0407200828cd0343d501c500100524000c900d20045c00c2c01c84c490f0201150410010207020030504021a80e194011020628100100303484001c140e400341018892181c0c032040c100281c00445 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 738224496 1250 738223246 738223259
    0x2104061410150e0933030a0f060b0a090e1e0a0b040309050a0e04061a0303041211041d12041a0d021b0f0c030102030105010f0503090a08041707050406 66
    0x105a540701d4940058110a20118001c1c0103500d9502c0c00c040140c1404091701d40f401c0041c1481800e04400210b41c0c4106040020460f102820080720b040013074020000200240c0315046d40031040748048500340c1e180c4100c01030f1034407402c07542401040c814202144410b60303508820300740069841800b031a5540c240c0880d0072100d00207040800706030404850031440c0c447e03017000c503982022900515002210210000380c142105007400344158040c920400001c0c0140c00104241d02e840d41c0f4595166109010a00010402d8400e0001407841902070001445582c0c000c0b405440c05130144548452504c208c0c0720900c4000d000d0748089103260001e0902d09800e160212100e041060b420805080c00441d11701064a410350403103802069a44400070a0807000c0c40150f6206060a40c0e05254040c48007240c40e682414000c0d03d040e10816100c0007040b0081500840c4c0d550401002c55010380b0038581c0c5c8001042c00c1600610242030800e40102c0d00d0410034444900c0c00c003890344030a02651401e84200402d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 738225746 1250 738224496 738224521
    0x215091504141c0e1806060405090a0b090703240503100e03072a0e15040209011b060507140408070b2d13050f0307061421040614 57
    0x803682c0040980000d001101003070349803050f1020b031500c00701412038028034040d80002c51007060050842c0c0303944401180c01c1000f00c510f03100b40d035201d4221009110038802480c200b0401548403a48800c0001d5103d18000060791070107040d034074100401d45d00d182c4642c680204c01da040c008202c4101c030b002051171802022990352444083c0243c1c0301c95079840c817070b1312103142030049070529600980350095030030110600c5150342d007040d4001c00061705884800525528036040f0141700700442a40305101101d600c042c00065813044144504005100b8580200c807290034800d900d80902541000851b4036180f00e024101400007041c2c0762400300e09110401204000003200016206801800da4803108403c0314120795110801c100340c9041c04a50340c1c0503914604002400d408148034851406182c0e4400500008000034000680c140d004514244400c5005c0c20b5103001e402a410703d500d1a05000240c00050101e000c0b4400207030800500c240f02c01d200b10350081008030941c0c088061010705018110110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 738226996 1250 738225746 738225751
    0x118110306090a050a090512032e0311011709060117011802240c0309010906030e03070210050c0703141005060117070210061206110f0703050309030d0c02150915 71
    0x183c54a0358001001c14202d500702c103021590200803586002030071071400311741d60001c03151503980440700e40a080c0d00c40d1803200b207503060341118070500203118115100e002c44200c101103070506016032522084180b04008201d41d1041b4140c030060015075043c41e001c0007580c00c0c001564587c3c0c1e030600080192045041c1c0c0d00b88c950ba6812912144081d6803007101b08442342030300d016140a440d011817070b5400c41c0343c04001800940b00982e10b014500e42c4591003a4203c3d90012200c0040340c0c01030040b600181802c04001e9400c03c030a007016800c0126002445103840c0c104e0f00100c4680c9008855403000f440208088590511100c000780060718040d40001c2810050003075100c6240303480c101240c0098003d20010203030303141c40082400b030f107900e03020100340c83c2d00d09042c1207072a180303170049001e01e08050328143d410340300300c401c0c1c0750b031030180b554908850a400103020210709000c10403512504840038480c04804a2064018000e840c100c1804038800321302c0184002c0940d00122284a500e8601449096 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 738228246 1250 738226996 738227011
    0x906100e0a0e030703050a17100b0919080109020102100605031515031b010806011d010309050f07062f0a020108220507360b18011811030609 62
    0x11240da80088000c007070b160107600003402c2e010000703121080c158044000d0425800c1510313208954000800105c1c11010116541e40c07105600c0076050000809450060030032a01c010080c0e101c1c00c0d01039a2101c206450b80d03000942503952104044115601800b01140416900d071041102d10715010109484105a001c0b82d01c13111908800641c0425a000302c400c031007e4003408035000a441c0781011040003440e01000b03408500084000b40131980310b00c0811a41c41c2c42c03040c880449078400d00054003c2c111741e600c00c07950b901807d901780c0c021050810065000b0806940c8400480050460f03540b00404ce544120b04401e00b1105a500300c4c4c5400a0342c900d19036030a19100c500c940ea03c116510001c003030203942d42541a1104400d405004c80000d8500c1511003400008140700c400207008003403042109840f19007070301d10000340d004502c410341c49011102c8000d0003892030b0000d50072102a09034070903044002c0300101c0b078252036504080c1d803142100c0403034818006403071410003c0015420010007040c44 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 738229496 1250 738228246 738228269
    0x914060f0d0f06021818090c3003120108160e180d0201050604110901140c0703080a0f090603050f1f0b041211030a030917010204051201090308090610 66
    0x900c10440b52004042489070084011501c858900d6a04200f002841c81814861403002c44201e0380f41080700d24060050340c58030300400500703465200303101000e20428003421540c40030380000c81580000c510b0070034208841001455484402e01d003001510103040c0c00600340c950141207000c240c010750345542415144002d071000348a950329800000741c8004c1c03850200705030151420100d200f9805402c00d40c043c810403038041c010001441d000480500031410703010300041c168010f42040c180300100500f40402d640003a928501d80f00e40758030340c007640007940c1c1070b0004804501000d965035004e035640014101f28a000d020710709107407040600000000c0d12114031071581820584d008064002404024071101c00c00c5c0d900c9e0750380c03113030048501414640b003520030310385140348210140ba000c105030800940c16118611101d0521805071031b82d144940800c900c07503500708000b142e0765542c41c5c1101c046100304000403802c0076881c0b5000b84006000b62240906a000707030148041c1d241000011f0050744d2100c14103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 738230746 1250 738229496 738229519
    0x10501170d14210406060e060f010e130e070314120301171c0215060306040f150212130615080706030b03010212131b05090a0203150a06090914060f 65
    0x482c20b507032045859540c0b0004a80040729804080344841c1c9104c1c5001d40d004001440c2e0390101c0745c0650204a66441e8004a04545100651300801e00c4589003a00641558a04109408480d0031120325100d00d004641c4045000c1042060749034a94102c250b0310710140900303060f4018000f803280010b00070302010003503284060780844070800c2203018111683d40003075076489501002944034116003240c1415a45c0d01740010707400e818005038807409140c2c0440c503040980250380700c1e201c010b5140000c0b806290740070803101e808200302002d0980190140c00507090b8038250b82c0303011012520800207124900c2c02e800000c00940c0000f056003021942103090100e801461500000d009205900c01100303082c0a103028403950480d0036900e007080c14032503410008015044c90703041408410314814164000030880c0010844021a006140c0014071841e928400f009034030005441c0350056008140082c644c1001080980040e00030302c0700601840640e151141400c40c0450b0a1148408906009040d292076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 738231996 1250 738230746 738230777
    0x60f06031e020a150536011404060c0c08060a05060112090c03080a03090c15140c1914060702010903020d0e06070f080f030a0207060f063f0501020408010501170d 71
    0x84440100300f283c03aa54001c180b4846562404100f2006d0f982c800056408800d940e501600c07014480d044289107507410b1a1400d8021138501494141c22200f6008008000800460401126000d5104014017203041d180110004252000400000c4607280c1008188808162466204400d0720b40082040c2c0d030351842590203401514079880020000104590000383c2003940741000c4400302d5440d40d40d043c4060f401803005019000b444112081a0403500400705488036804802c800c45218111800c007100049001c4d90625004070341610150b5160710070742c0201a418022001a103406050054510800f90b003c00c11030300900500422102000c1c1c041d0080c0068101502d80d1400400301c0e403a07032450700d840a0006074001d180121481400c00940c1036040415004280644046020102d4440b44428801026207038040c540c110106480c298100c4440d4000d5044d1b029034040d4002581d1070b4641014103003100c0050b8088420b848840d1b01e6900c60030380200308840c5907611490020440001206c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 738233246 1250 738231996 738232007
    0xe0d1e06020c0d020601140607080d05040326060a0b130e1504110d0507050f07290718050a03030e06070314070c0305210a0f0c060f06031e020a15 64
    0x40c030308012031060f10965075030983e001941d02d044c0c07903408210511882c5120140308a60242e2240184500c07000e22a481c1007104650101d0750040c0249011a0311111951502050441700c10428032042d02d05000c12204d420413071f80080090410341002407410b800c42222814111150003401086800364000c02c182034142e4806c02d125000c01003040000c07841c0004503829592240c204000440d090000291005010b0002d441000b03402409042c42d080c0c6c0dc1d40d400301c0c406002c0c400c0b107043d8440c80380301800403900c0b04c0f080e0703209800f19180ca0003180d6540c1d11180700010980d011070b00c40e20501c5814800250301c1700c00c114000c0004e65115480365800d150548054100342802441004e0205103030f0305000780c4444044c2101d02840603108140b0780390f0800008102683c1750706401c030000b00f0051290170b03c07034084d070242490a45000030380c1000e01e50340c80068901ca1914014803a4898401740f081c04400252080e40d81c12104521110701c0040d03001c500644018810808040e4440e030780d40e1950350198 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 738234496 1250 738233246 738233257
    0x2208030d0b1807030b10081021061113080a23030412050a11240f130305030d050601090311040203040204060e070305091e07030803060409050a0c060e0d1e0602 70
    0x1800420041d03d4407050003801011203070719461140002202225615000710121401840050b0390141607504212204000c003035910804201c1c1030035001d007603003c14003912404022081d2034192503511412410240345142603a00700e281d1517005182c4202c00503041288000425080c3e45200207060106459282140201c4e440381854a1104c82490100540490761603007003440b0712441d01b4040486010311038072500000a60030899075800221640111100151000d00f200d03110203450f10014448410300000c040d4004c444950021071000043d098038000c40358041030a10340b18441c2c9207991510100c2e90301518400380995030002c003203000d54071940c000d40701803c2071403000813282c14001c0c4028010181111440614000d8020f005c0070800c450310381100c1d04400200420f404c03419a11207000302e61014009917481550345800070001034003400a50010b81c01445003041c003e18298016000c1e01e4160700062217120780e2200b0b000000c0001c80d908065030812010040b46c1540e515000c03000b4400c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 738235746 1250 738234496 738234529
    0x12100302090405031309020406080a090203101409100e0a060b1824010806060a1b02100c06110a0c14010605060c070503010e060c1207020705090703022208030d0b 71
    0x900708100034040d0000080016440441d400c0071429540c0e800d000490082d40644000035a44502280300c0c584181c0281d0f008038002030580342a58084150f6400311200c0c080d00b981c2c088290030802042420034000c0c181e000420000030300c0300b0482500c900340c40e11510352000304140d42d6007810b400c26403950000c510001c00c4a0f07102e22520300f0721064802c001032000c001d00426043c86982131446500c1032a5090060402403c068102400c600056070940700d6500003000c100e42103a158000340e41c0d00c0d0812400d0000e40d464040c201d03030b06800d1860650780040300f60b902c460420442001e000da80840c0011520703800c1f0f214500b81c425407162581c0503280591020b50302c00008103405c0c80b02e8001207007882c1107400860007000380075503828129499400854540000001c00e024a03440d084144d14050360010070707441901c0342d182d00c8100107207100700c054030f205000030f60106000718212207010351920815041c80020004600c2c103042203688ac03241580821001341c43e4001e014960b1074055105815124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 738236996 1250 738235746 738235759
    0x103150e0106141e03060a092f13060b030106030e101a01020f06010b041205100c1d030a0f170f0415030c260c0f12090c1512100302 58
    0x140c2e410700d051803246078440607102e00c0440c5201c080080462050004c620809000713001d1031743d41e40345c0f140b0003031088002c1510300c0b40502017003481121541200d001d800c0320310310031a0b136518002d6003400002c1245c00030360340c280d52403c44207018920150084d82d0442d800c6140204034201d400344081d042031400441544003e04040c01c002c000d15030004030302c840700c20a0742191254502e04c0e0185540e0031080c865a2920f24040009004c80240c2c460204000ea00407003c941c1000b4071005203004032051000d00a0010368100411211082c0f0104064a800c1045004000a060644644201c6050254014a0311846042000c0c43c00c0140003035486c3c00100710341c0662202d075940e04a4003009402000403001a01e803070003002403540220000d848482c0b150801c060450108010b01d101110b000c0c00449503e1024802c9669014011006010b00640c010303056516083c040081854400e041800c0c9109964080402401840d400e040d0365000a0ba0b11002940b42c46022640004007902d81011b5082030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 738238246 1250 738236996 738236999
    0xb040210110a140d050a0e04020915030709140d120309030311040b030a050603160308090301020f0c010b0a09020c03180a0302090702071e0b0d2313020102010b180103150e0106 77
    0x610f201c00c4000701c01c1001c00e0f41c45000e021074048031940704803104680440d65076107001c0003e0034203a01030b280102000c0c00ca80d445203180c0e4003241440d0800c0341c01c080016403200c000d005016000c02403aa00c503005407120801040141e4074807003112104003000c000c241c0e94100890034035110703070032001010035504282c966031500c0d580603a03000e90003103072205011400c020214049080004101e03c9580500d80c40c03005450840e624410554442500983c0c50340d000c2c400d81024189610050000c400c0600001a90950075000e11207024142d0340310180281c410310080360b45100101c1201c0c004810391040d10036040322038001a2801d007050304041d4110300c0305801c20007541c2c1c0001d44401030315900b04485445601c050004032a6410394080c0640b0140240080701502641d40c008480e03245840b180c031803400c0c08a040e04010b00c102116640c01c405100040442903507020b10a020660b402070300c1d8440c8111411286c01d40c0b01c038040c840100300d18140c001e81085034403c1e900c02c0006190f140000d0001d039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 738239496 1250 738238246 738238253
    0xe01051e1602041d0c09090a23010612060c0e1e0d05030c15010803161e1406010f090e030307050715020a0e0f012c0a0f0e0a11070b040210110a 63
    0x18141307609841c000d102d0405010214544010441c2c8a00c42810007005000071540e1042c04500ba40b40000300302c0b00d4070f0030a04d500d03401d0038001c079400380210600444019509003400c50555288001440a100c1920340807801e5844030940c1d1020395007214801040340e924a0085880424503c030040d10600021501c501e403030380e002c40c000c000a01980100c6900b0798071104840e40340c0c8101e00c40142400c45082c0010000b980403001001140908103586034007d401e61101c20722a84066449411900030301c006003c1c0c05003000d0a0001390400c03d07402c00c0038110264280d9642e00c40a0442410710801140700000c002041308403110000344418259118007500d08040c1c5410840030049100e0183d280384902554891003c680780b000c0440a050007900710101049414403e00c0354154004038482d030041074890450000300020312070907003030040d03901c1c00202401c00c854800581c2c41085004200d09d03004201c0c2102840d4215070111100d80070444030032801d40d21100005407940e0603021301c1c82c03c034052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 738240746 1250 738239496 738239531
    0x11070506030c09040c050c03121b0a020d02060a1a1509220f020c100c12020408060a11040609030b0618090307053306060d05090a030e01051e160204 65
    0x43ca8802c3e6428811000403d6054640d03004506c0c08a240e0b81c4144081d1906140403010260004880c020004188803c1c84c02c14180e80e005c400385101580c0460702520407240d04210702c41d8406060b4804200b85030110204030303c0f80b070090084500c6111045240c81c0e0030300c00708048845e450001031030b41142c0350700480c214601b01032414502207050b240a51800741103070207008540c074070008400944a510700b6041828020300c03e40d801c02081110900c0e00340c181002d03a20050019008001c0100745c02d15011204205803070049640b054120b20902003000741c00c0e040490001a294406407031030407075a0340d9003c207010035402c409600b03250900405011244c90040001c180b407902039400d941140c3c01180041800880c04c0c01d2401e940007140425002d5141c01140c010340010300200941c0c6082c0e507a900e51400d60340d040d102e1300a1908405044000c02d908035060b422400800c0c24014105a0451062106101e420f1a40d4503014000a0b50700300003007180c1e00052906a0040c820000c3e0701c42c550007280c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 738241996 1250 738240746 738240757
    0x9020c0c0607150506060702130e0a080d09052b08070e10090302031e07121a04030206010807090c0909090204020c0a050303011403060c07140a14060a0f0c02060711070506030c 77
    0x18403600e003a005c0344035428200115603140307401070032103c0380d01c4100c91840c1c010071840310340300031a020f01300702040040e506000410410003051808100c882c640c1c100141409440a03403100d244181d645220f0b90840f04e8146102d1241103400e00c0d01c0c481d50381c82e200b03451003422107245980c0209110b4030700c1d80007030700b01c038029068030700a40481d40e0b401442002001054118450700680e5402843d0030030031513510746551a4440c0c03050900c04005202001540c20100c1e0586040b80907801040c0180325a103001c01103e001005200c50520654245110103440840180602c000c07107a01c600002056490700d404454401d4501421103c0700a1541070854030703500280074401d030340215010074010510700010854090825400c1007882c0a030503948039009043c05840c51030319070260601007004100f000031165461100d920107400d2a140c100442030441d4980c0040126042ca171100190b0516800500070380d00c6986d0b8180820010404000b091408405a015a0381320074000200800303201094003425 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 738243246 1250 738241996 738242033
    0xa050a0314030907170a080f0a08070206190c0c0b040507090e0705060f070c031a07030b040501060c0b04080f0c01020405040c0219150f0203010801020720010909020c0c0607 76
    0x40100c2180400040610041da000090fa50001c0ca0603c0f086036014603010a0b000260215440c3d0100b81c1d507039822940014002c080c0784000030400350360590b048002c103a4029502d1000d001c0c2484c011303071103002d00072004411b807410725500c5510300c5200f4001c00062000b81d0f0060b42002061801c4d142c078a41d00e103124040d10340a5420440740d03c2c00031100281040594034000c00f42400c1880a240605141d0040a8141d0301000e082030008003003000c0361591101a081c1503002852480c01010183c29600901090b0740142cac9032070f004103d2681d0003200383c00c0c0b195009109000d030b600e4505018042d03020714426207400030b43c0001c0c3c000e00c2c845d0560041c41214004e8a043c0f000440040c41a61140340c0c034210101e00300074614111000945102084011851000e00001c186030034071101012600240c0150b80300380c1d8002240d9003845044c01001880c2070202c032144000c8100b41c00004c00f03665207882004011078002c24001610030040c042c01080c0702010304219180d00361810422004070740c00302c124 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 738244496 1250 738243246 738243257
    0x3030702121603050c1608030a0206071e08060d080a030902031e120a030f021c0b040603020a060e010507051c080f1005120c09010605130605090d0f020d050a050a03 72
    0x600d460046401503a1442c0c6590080d854a4180341d14180d13155070140004190314052115203410303403c00e1884240c0a00381c60002151110308500d8040d24080002e040007082c0000088a1108070342019150030f0481c2062412588549410000c12111240340a006000060100d02080150f03819400725003514001c8007120004421030000c5081c0300481e82d502001a0443d90140d94448001c8004082a0915250014843c25401d5540c0c00301c1c2c101c1178403840170b02820201041001298040c0700844082118100001072a5900080e02460903108100c24003118185540b000d078082d40c181c5100c15049000d94041c101c40060440d01c03030300302d09a0000804c45800c01304400d06041208a8400d203400c2c0c0704131b10b030340341080100702038120201c10192143c85115040d00840d112650030318020505501c80644650100003808510809038000004000c801d00c400442544d4141d140905140c0110405240c10024000304840600032003026180f4480c2c0b4018004010700003071001400c0380a40e41c4d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 738245746 1250 738244496 738244513
    0x7030201110a0204110a0306062c1504030b0712020901020c0f0111060a1407110a030e040615020a12170103020607020f0d052812030c050c0109060603060c03020703050f030403020a1403030702 84
    0x1d8ad041150030b0b080b039000c2014000c20841200380500d40d0000028003c14040e03040e80c851070464800c0d40960022a064001c4400f8800041c1e0001c4419440f10708940d010350902c030755500003d66809c800401d036841010406004040d0340d00681488413401c0815056070080d1406030690005440f4200480d242c01994500148400c0e2140c1a40d03450b00c2c040034080d00034103403984c50031104d50301408807856205640e400002014110010440810744e0b00f038002d03002c8014a800d00008c1810491a644240104542540c0b80d040d00340c15401e0545c1c2c1e048440b191076000c40c1c0082869488400c130440d40102c942080d030000e102c4009220350f0fa101109000001c4101c20960034400c2420300fa0004144407140d41038040d9990194204224401d81d0b483c002c3d040030007040c0d1103403e58101c0e07401a80c4139666204240b042c03001901402449074283c1c03c05615000680d5401000c500c1a2815242d40000210115007014402c2c000c04240f95040b1a4158500244030b0740316403203900c10389000d0094490003c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 738246996 1250 738245746 738245759
    0x309020a050f0904260301091b0201110909130c061701091a0634031e21090203030d05091516030b0117130302061807030201110a0204110a0306 63
    0x506580d200d0019003503100a8541e41e880c0f04440d2040552014003030340071707048100c3c0b060306807014500801c0c40b501c000c41c11210f404440c0c0f5141100300030003000c59043c48502100210010700b1100b50500c143c8000034079903a00300e41c4c9000c00444400043c090340111000250540c2e20415050045542c500a20141d90743c1d40c680b80c1c00c5540300030f24401d841003080306402051410f44050030040d03591054103c0071104a44480c0c10301300c00d0214009040001441c3c4d4401c2c51341c061240b00101c907100400d034140f1840c2110140c0a09000c0c0c00c4050306104c055145040c0c480d05800181c040340c3e0180c122034855619880329800f510341103804651500c18a07400200300d0804031061802844225005503140c80350b11802c07400303080047c410906000c04000448504106400000e2003424078400400264400d49002810000c001c0c010304c030f00c820384020314008090301140c0d074800c40740e0900745458407083e900540c50911000d001d01a50151900b8520052000070744010422071807240d6003000440e85400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 738248246 1250 738246996 738247009
    0x306070309121d040c03020c0f19020607050304180605011b0b010e1008070b120708010e13060f020c0c0f01091d0901020f130e070503090a0b0612030a0309020a05 71
    0x600980780d2200881402c084074041c0c0002070a00d0000440444803440c1503000c101a200d81c107807400c0010f9400100411115002c1c4101d09607541c052020f48400304080140751142001540080c2c40b5001c0010182d040040800c00c69008000f031091070503103200c3e000c411100404171485070b180450582c0130b041405029110381450984c0e4080c4001c41140d0810b58514030a510041c41a1301c058050032011880e540200f000c10010010300200700d5880b5960f036420405540003070110b00030700445030014042180d0840056901c10740b450416400440e05041100107441d42c001c04e42c04103480042d00380c50302d42010a000d166803500b5101c07000e0700d000c03400044468403200d2107122001094903100c078214a0400e207006400c0640c080c005400d1816800c4081a030340d11545070b40c62440041601009098440c1144640c0034005082c03403406d51516106481e100e47d2038800040c804840000000d42030380c3c0324603482e007014021b4000c403a12074100003005402400f03012001e0340b00300052100000d10f4035062 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 738249496 1250 738248246 738248261
    0x290a06030302160b030a0506040f0207060f06140607080f0712080610020606010527060a080108010b0a03020d03080901060b031e0907050d0b091924090b0112170a0e03060703 76
    0x215542d185031b50f501c4040004180184c803882d40719845181380311880040340043d140650107284009003d020480e000d001b150010741c825180c68483e485101d0b2076a8921050300c00258101c0c04880d170300c10b0742d428078011902c2030090007804c0d2002502480030069000210714400e850582d804c044403d04220300342e80d981c10896400780000d0b820000130701c400d00d07004101c1084075040301410f0307100903070301c00003641c00d4100034600400a0418070040207511424010849101030aa910300007407402c1d500461280d040000014047c0100034022890002c800d6101400410480f054103031130741490b8511078119588a51114080c100f60000300348920f4022030183e0450740c00400400000380f82d82e550303c1f24072900508a006d80c0c01030906920010420103525107400c0e1003042000c418852404100300c0714003200111901e1280341510307110009481d01d211030b0655030314984500b0310540a2074410783c401e40d04a4807070750100c40400c0188a06412171706114030984214142e405503540c4980440c21590036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 738250746 1250 738249496 738249509
    0x603020306060f1207060c1208010302011407020d0b0702030d061a0301151701120b010b0a140c070512062203080106030b060702030f0d02011a090103290a0603030216 73
    0x80d0300800c185180540048101c000c000e0701c8440d040490184c298204860b41e8020070124100600200c2000725210004145011500340441c0c1541550002000803208102003620f18100140d154150350380c85034041802035105514840c1703031400c1c002c000e4880e00000c9280c1140e904002000c100003c40152600c00c5201d1070f802c240c15a864240896140e05440302400103006285014440b40c40c501c6c0d2a007806004520304807035005040e0b140900e96050141d2103072040c4401841f98000075680907094005000d40c140d501c54aa07c60911607504003507682c0d000076030210154a03040e81090000c5281071284e5a1003140052081c05642002408603110600800046004005001007400f9500240c1041300141070365007401540e5000c40e1138103500d00340b00306c0c403a40030460b104005982402a42c10a6060400d9800c582e10403202040c400352060000400703e44100102012884a0540d61f84d500150019000c8403401c10010001c0205120b02094005000e254640c0202007448000802141e08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 738251996 1250 738250746 738250753
    0x2010503060d02060c0712030909060b180a12030c14010506060a030924141f0614070b010f031e0309060804020d080301090b04061d04080a1707120e0106030203 70
    0x4491042002c00b242902040764040d10030701c404015070404000d41e20280005450441502400382005070000c88190301c4059410309102c020320040380750300250307190388229581d10848403240d4400284e05c043c035900b001002e01c00e01e41d288414160701007855a4003a0051071810307880d036804100382e0b00f6118215041900282e0400c01c82e242039100b81d02c810b003080e009486440e4504c081003911007410712655604608591a64001c0c5d002007580c485c4070703030040c65402a03203800c072a5280c0b040b240d580040c441c0c4000d200c08070380d2521090101742c1c00c13a02c1c890f500c0000c0035082d40c1c40b40941c81001c0308034041550010440641c4c0d5807404090300384411181d806464002c8218074043c4102c48410303008004a030004030b54858080004e4a03840a5806010405c401280403154201404110380325540143d012041541010400110900c1c50581050304641c0c41642c402010100350384192a091541c2a6a07a009080001003580110079107500c2d03881e0002400154010400d241c281c810501000c0e50542 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 738253246 1250 738251996 738252001
    0x390a050703120203090d18090c080a0c09081906201207020d120f140a0f0e120d020919090b09010b1801031a09040f03020d050a0905221509061202010503 67
    0xe005681c85147c0320071a01e260341c48682c9842d070b01e80961349446006404134501d031007405051002401120651181441c10701c0382180b40103030307440c0d980742e144146103002e4036048108800c0c010241c1101524010740c1c030b41031310f0102c0c02c0030030802140d0245d1011b5408a1440d0042801d052002c2461410801640d68503c0e8a014028440f0000c2034100e070840461680c94107509903600740840420b1251041c20000505840c02120300780130b840f00400340000c290090249120480d001e00e040d620710360031a0348010b8450a4000c0802c40910038900f10700c1c2c14041c605800690b014441d04521002202501d18241c6a66100b4030014180900154407100c602680c1200750a540309920003102c550302c41034150400340c00b10005c80c2007030b1000d40d4296143e18040c04401c080c90703010424503820030b24601e8142d14103004260018441d2403036000321489082c2a84004c0720190346248980c804030740c0c19100700000c050081c41e1a1841101e031240d600703002d06081001410400c880740402000350182c5420380356a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 738254496 1250 738253246 738253273
    0x30d060609290712030b040c03020406050f0309160806190207051522050c1018060f0905060a1860120203390a05070312020309 56
    0x120002c00890400020901c90032011841d0491062200754564a000800082850030312003507035840e00c061801d060040100b081040d510500b203c24134000800410380369150898081e00740a00850100b102c00444640802c1c00720000c15864000c10901103005022440080010141c0c0210340014019800101c04500c01c400d881e50026807000c1c050400880e900346640d00c0c001c068580241c11703120ba0313114040e07600803030900e44e44030041d444180c10940c0d407004c1811003181203040030780035000070404104140034040713001e0304042c00a800e00818894440ca55454000e0a40e880307030b941c4440008030801c00149030f14001100c56200c0c0145074403500d0480c00340403021101c0300d40b1000a1954000920f0001034100b06240d509041e249510081064455036000100341902021101101d0341c03041060101c0e0036241c1c40601f82c0354105450305d01c2006081d11340e140d15041008403544070b844001440e0701030103a000006240480c03003078565094000118044900b240012036610304140c1c003a800100c0c44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 738255746 1250 738254496 738254549
    0x30a120503071107060201020711090606031f05031902270c090307051207060206070509090109050406090f032015071112040f0e010e06030c010827030d060609 70
    0x100041d401d0241e0321401010f800307032401102c0e0784050010303507004c130b6440100308102c00720450211b41100c1000c001d040c040006102d07440b018141c0114032004651000c040c2e84650000002010001c0c00c3c0c92881111071144070601418071002c034481e114845944010b0301c2c0c0500c501182140e170540350490f0303a031395844000c40d84c1e004009143e03052180620018050ba214095000c0308480840504440d40c40e1500207480c0c604060501f505000007444420f90380d0721481a01e60440702074100c0401c1e15111307400c0110003170003614401b49c11005842070340418550810039407460a01020085120702140030301c0306480e11000c0303000242c50040b070000301c1d0345a84910002420030f142c1101341d800c0c04130f0301c603443c00240d401603115402c019501c03041007041e001062a91801003a55090592187c82c01030700181e10390300c0700c250940c144114000842d840400c039000d03032101e945405030141c4514005921051b6690480300045005504100780894020300c03c81e00a011a20300720203140e60000d83e0b40301980c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 738256996 1250 738255746 738255751
    0x12150c020717010e070609080a411908180109080718050114060304030311040f1202030c1815041104060e0112112a0a140c030a120503 59
    0x3148201e2a000c10074000c1e10800d480120300100000402a00e102d0429042160540c80441845500e500412a2003004504641120b912500004103900800c05070080701d4882c84080c000c006146d40c08101221599204c0c0c0400703091481120303600d1180e941403d50340d50401c1001003618400780169034100001459294041c201414980d00190f00d840c0541d10b0105680c0c000324143c134034100c41c4407603a17000b48181809441d005201440c0f00c0d68441c0811030300d11020348000c0c205030356003101803510b43c0c025040e0703809851800c0c80c03000360542d144940030800d48440003c2e0703c00c0c0160301c9000d045180001d003200e1560700c0c07003054600d256508405070304500d0b42c58030190f40154a9040c40102641c60324000c1001c0c009648440b888401c6100c0010801c420300310790070580c41d00c7d000992418801d00000d030703071215843d00002d0424200c03001266480c0040b091130600580b0480c4001000c01011b2410f500003038140c0e008581c1461014810542d0310034003010082c004031200404060718605c2503000b5503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 738258246 1250 738256996 738257021
    0xb09092e09060228050405011d0a05061306080c03090c010807120f05070e030708030f0d061e030326071b301e050715050f0f011215 58
    0xc52100c2034a42c601070f83d010a155003c00607038800c00d91900e0580d038000620840052400600700303402c2c60000f03440018001400b5a030100900c54202550f03444070022005130202030440c3d510b07410030700c5680080f00491f020341400b0815000020340c00480c5c030001d0381c1c8079410034001804540c2c00c0f0001501da0704c10180441d8100700410207600c06442d070718052000d8200300c4803800141c0b03240c40c40004040034814000b5500c6904001c0b810000a031000040d208403c0c200c00800c0d030703103030000942600101066400004161540d000340100c0084116499080f01e0107522000140c1b59174495503003458001440c031000c078014550114041d68419580820380d424070700001e88242038543c8616200c0b8480c07105c034103026481449042c14140034540c580201807060708011000074241000c20952103042800c1d6001c010021487c281408040e900344070100e030118104100504000845200b001e10460740a111600d04030000104103680e46034100315242c010000240742180d03440f0072806000d50041c00c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 738259496 1250 738258246 738258251
    0x100806060604301101080c0901020a02090c131409060a060912020607020d060b011103120105091e0112030f0908190206041d1005030d1e090f0303030b09092e 69
    0xe44008081c1d444003822034010300d035880100c0d2000c40014031001001f090007000102c00d00c01e1501c103136000100c40d640164115205411660741c0100030348039008010308103945c4e21061200086082100b461a40249002c0d5201081da40e2580140264000c1502c076020018002610402130700209141413040c00744020302082c58000e05800040c09146108421389040340d40e0030700c1c1501903803c400403030b007022401000385042181d040200750303401c001480b6050060000900140042c0c0d640c03c102c800c00058110780c19119615030213455030481e4a840103c020a4100d4000c2c180d090064a1600458a0010041c0255103c140046580c100010001c0340c1015061001060039145066040c50071403441c1d071750a5851502c4110710000d07403621781c0854000d070401003010320f6883d880036144280136100d450304c030a2507003400b40803500d50a056028030f08451031104040100740c2e040c2c0096a81c0c002c1141d519499480350180d030340d21000000b18440c8a440702900a659124039107002107207004419400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 738260746 1250 738259496 738259559
    0x1707030b06040905060a050103180609050f06130314190c0201020c04050c071e0c05010c0c24020105181c0c020603040c0e011502060f131703100806060604 68
    0x4940d56811903000b41c4050f907141d2040107000d0038025042d00081009103030034420080340741000008004c4000b40940195190400711090100800034182c00c403a0302401c070b5a140c40d0803e0701007403040104004900044c2c2d0404060407130f40808041c0d500c0c2a0b41140850f040e001d100c01e0586140520301c40c01c9055000f80900d460340390b0381718407503035200e900300c6c0300d440d5036032848c2d40b030800c1d541c90b035041e84203101002070000c1030301040c0c0240012041d40c0080c2028103071b013191400c00c650081e07143c0d07000d038901c45290403000c200c0c1c0b1402d4041c8004005160000d20198403086010000286084080d4240e9400746400c00e043e146403c0f841e0700140d04074104a020406150085800d541c41154140c0d01151145800c00240c1c4041c0b060350b00400d140005400070209000001392207800c09001022408507039000305100c41010b0103007041d6a039001e542fa40c800104800d1000c0b054104841e407030382c1250000f00002e1104c002007811441850000c0c2190315280c2404105502c40d50354054214124102600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 738261996 1250 738260746 738260749
    0x151e0b0d05010603030914010320030601120606120b011b02010e0607060204080d11031303080d063c08030405240304030203070c3003030b0628020c011707030b 70
    0x1154041c5000341d403112046030401c030ba03a150102280e4082410540b403d2040444140c2d200c2c6010700d005010036507642cbd280c4038580100c851000d4000034038440791426100042841c1c01040c80903010110b460244110088000190740c241c9094103a1450180b403c00c80c04015071046a40b42c0f88a040103186504000080d00c44034200c1c0c1098010100c1030744005001c02c0d10389d810050360548040440015490714070221640c0002201900c00100341150100306146c5082040d00804094643e00b00c82c007a1450030500b080007107400403600181c03074610040020406c80000c0750074100342d46201004500e40303450301c000d0050040c0004d5200c0300c24000042a401004da28a00842c0500e00075801143c682d0041d0401d807000d078140d0b034400c92002c460b811210054140010002d010100352611410040005d800d05501402c1481589584148000740000d0700d80300d082c401101c0c1c4a1050101e1f403148401c030105a0b62000c81d050400e0214182d981d409850003022981d0b00e5100c079891502103400c2002c0030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 738263246 1250 738261996 738262001
    0x50102160c0e0c070321020d090b04020f03061501050c0a020d0b090f060f01140409121115010e0c0309072105300c1e010603151e0b0d0501 61
    0x20200c1e101140c03030004000ca0081e215800b60400103d803421440c10030381d030354003a100700e0502d00203a0401d0703103210140c0c0c1c44d41c81c65810745050096144007840305142502e4400010030045800300c2c410f24903c0148201030a00281e2144104441c44a0701c008401060040d10316800030310030384500b84103030200007005881d40c1401900c01403043d2014140c80c203103c5046400c0c80b40d40307150124594018001c1214603440b08040c11704450010144c0080c544000b00802c000c2c4c10b07801e00103405034280e0399060007039950200622040072914415581040300209000340762a80070b1040c846c0310800d000102d04d815980400540e00440e24078103c030b80c1180c6e80c1e244810019010304e100c0d52061414914041408400d00440134565900c9502c05c2c94250700d2041c460318001c0260b850341d81c8141c08503812085030341c100222690310a81d6110f241030410300107000c901801503400100c50b00502c0b19011751110307800b8095000f800c11082040c80c141d00355650b1900080bd0050302003035005880ca00301101013102031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 738264496 1250 738263246 738263287
    0x1e0f030302030a080a02032502010f060b03010906092f0c06070c030f0318030315170d030b030703110d030c23011b050d0b04061806030c14060a0309050102 68
    0x81d0061915411020070151a22500a0414006900410400081d02c8c880c0c0400702c075004550981d4002c0441006040b8010310020344040001845c00c90007250032a60180554100c9204007001d010319038071184014280e619900000c0f00b0403540114101e00d803032086e5003003000508960620703400c00d88101001d07490641c0079200314001c0703003200d20b84505040d030140411103106070b0b600f8188210300c04803803044090340410750701604140d40d61204603030f081c0b6020304e0980140000c001412000d101c000400b6180c02c070100ea0000400e2504500c00c002d401c5c0422341d54101c94000f04e07102c600d4503600c41800a50780c00d202d0704800704010520060002003204000038107030841a0b40a54560000750007840c00c450a070006501100c03c84142c840070700c0c1cac1c048100d0b1101e8401c60300108001c000c020214010301441c3c2c014400c032141405a101308107209500040459004030a5020029075528440055480d00c00059802140c2040120b040f41d000350420b403001403081d000140fa1110710401407a2400c0c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 738265746 1250 738264496 738264503
    0x42304180803040b010b04051809010e07030803090d020106060f0f0c020607080910030e10230c1213020a030b1512010f110901171909030e01030e0c06041e0f03 70
    0x10081c0004c4c00313041340803140035203031042d807292070182010300182c80d66a900310001031b00d03080940054181c550a40014a10064840071501c0803074480c686585d2540085a00c56028819655a0300c03c40d841401035104a0701c90b501d50340a0810300b1a002c80c0d031a145410180c0512050600440c01a11424000e2003407a001d42c0310542c55103641403c0110030602540c90300101428030030f11041800300814000c1c6204011900000c0c045580d8940c101600e0696030203201e2600c1d50070400115285010040c0b120011006804846540d00d000080040555180103504601035810901c006082d074501d481c3c008541c140890780c944040070021700c4020b024080d420b00782e512500103c104c1c0e2801e00601945c0d00101d5400ba0800384000002000c0d0b1078a4281074031202c0301c0e1804152289101c0f100c0d00c8004107030502c00d00c90100941005408800351002244c0060724288128441c5503010a04d54400280205030500e00b9240606585039a00d0341031960340c910001d008001100100c1d407102600440c031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 738266996 1250 738265746 738265763
    0x1b09050106031d0d050d06030b01030303020703020d02060126250602010c1d0411190305060f03210f0f0d0506100503040807030f0c2010020304230418 66
    0x10100020181c80450f0f0884080703a88681d0318940346400410302c903041010758038105880354182d9081c200906800c0d480500444801e0001100381641a001000b03498002c0c1c01729003110300c007044201d903161024031807030504029000d0f25030206075102c2800c02071040c458045615141244614110900301d8255401590031002000c210580d020300407000c0544842c141461440c03915903c40b80c480c000304950704e01c265a03c0482400142410b420746000114112211450684280300a0300400e0283c3c0d0103403080040c0d410904180c6070005221030070700113075101503a00d424514802415500803a80429424038148102c400d5407880c54050440c4d4201da58020509042803001d00461540c001400010040c0c100104004204040111009a40d051812140e61107101c4000c0780c0307820030010001c004145554089006822a1889c20810241201e54a40d03402da00d2109aa90384568400c10300c0542840d540041c1c0c1d0240107614504149000d00042120b40b5890308070100110b280c81c0031181c032003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 738268246 1250 738266996 738266999
    0x1b0c0f0c150c170a0e46090209010507031d191514160609060608060a060509191d0d05040608011d0114040b13060302040b0a211b090501 60
    0x4054001000c3d5080ca40042c40c001c0c45a01c001c04601d0030b408000d00685090071859071302c00d1031904902a1036007080715107940001c072868524855000a402014020303e42034081007244140c801c40e83d000105031a41860008996016510041040c168590201c0c0c64504100c140d200c1540780d090620b12050007008050030300c08003403040b951400004040000b0182c00900d0724940c0811a6201d240101c0242200032292510f00007408007070300001d141c6030504e940007512407000a0050f004200a4400b0710005d601d5509100845000300d6503a40d03416245d02c030f08408880254018907540500b00700088000c046c6080640c64090507007a02400a000060304101980d880301c880d501401c030398190380084809980d84500000010300512000700d44003841c0c1706242e078460380489509500070b005107158071001210f50004041900c030583c000c074101748600042d407034250b0040301034403003021070603410b0070307240300b800f01b0021411100302c0e02d0700964842c43c85011041001c000042a02c810003183c2503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 738269496 1250 738268246 738268253
    0x10e061302010806031e0123010605120a110d090506151e03030417060609070807050301090b01020309041a10080402090c091513170a0515060a03020603040b04061b0c0f0c150c 77
    0x2400310310740341410148d001006000c3c1d030358040e04585089407598030440380c0e41c841031090001402141c418034030300c00002400920138041c6412060040e4041d5060f20956980c400c01004456540c40501d07074003180c82d0b03010b924590400b482d1001405001f030708685c02c0c541c0300d100541c02d2001600780380c011588400204191440c02c1c2c070959600a003503103001c680500b032801d8040c0c0b44d4041070041d1013032907494110031103459208105507840860014014040d0130b0b90410403244410040b488240138812903900b0b80c00fa14042c2641c0ca000b554050022503143c0d9039041e10b0000b80d000358658a070b00c0304181800c0821144844081c00c200344070b40e2580c007281d44c6800f80c05d503c240320304034a000c4203030401140c2c4000b00d880841c0010031020324010030401c40e66003100050f94110f980c0c00c020352003c0044140320a000e809241588900e02c140340400c445006802001080e40e036030210f40700054000e804000015102048288070300b803140d100700c03010300d0715441c901d80c2c007191801c0311100041d0041e5014050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 738270746 1250 738269496 738269531
    0xa0212010605160f0f050d080901050106020a030c0210020a0b040c06033207090b0703020303090c011107150c06090302061f14010e0307030611040305010e061302010806031e01 77
    0x1801c541c18400c2c81c182c00020a0328000030388550144c20255a41c0c20321041c064110700b85004564008240c0d000e010300303010050702c015426140d00045610740000130524a0002070554a6150103480320291000310380e08004411038031880440450060b040c484001406000045009500c500b00070030702ca9062080c0103045800c00060041c40c2408490660072000d1000314140034000480f0414035a90345045090700d40d41d0b4980c4c070a0092240c00200341c4145a408030241d8010010304081d100c0c2c9801000044400d1800ca071255403254110075010011103c079078229603840c91841c100b070f41c2400307001d80310527045846034103054001d07030881710030010550800b1018000c40036070310700ea405203a03080c00e0113180300040b03422815040c001661441451035504001c41c0000b15444281032003a503807400c032002882e82241c03100b100c196003401311081c100c00307000c1a920b2241c00c1c0005005032001035034004554000010300a982c00d40911081d8400440b242c00b08110103005901c004200030784481011045e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 738271996 1250 738270746 738270749
    0x20609010501030809040c09170a06060803090927120315010c120e0301020c0a11100822080c070b04061403090a0b1801090309050901090b0f040e0c06030a021201 71
    0x201649081d0043c00050500c209899010300280d44c0060010b40d880800d4030310f14004e400641410800003c9014400300020341e801c40c8910031001800520350340e0829a589005080c0516440200080041d10100914031142544e404203048045440c1010600e07a00302290080010110a0004100072034030403050312540d50701200703183c51281001c86480740ca1000706946840f0f02001900c041ca04691317a001d4058880c105180c405403016607007249400e0f10380102501260380121010807184007001e010f12825480741e055500c0300c6019418001066628508403030088507e41c005025520400008101d02000f800143c7c1c901c5036143d040a80203403103212030a20004039071808000300078500078042000e100c455881009190301b9151032048840740250100003c076150b03c1c1c52080e006040d4090f10324801c0780c0e0260b49040307190340c803640b500c0306492565070101d40010380400d10501d1420503510000e1014511000c3e641e040641e040045e115601c159803403c041900460601e060b0030700c5440150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 738273246 1250 738271996 738272011
    0x3120504090c1806050901051314030c03060907120c1212020f0c0d080307211b030504050a030c020a0f080a0203010b0609010f140418020d05150a05091806160206 71
    0x3030703984a003480041d203080524000c400805c400407904500c281d01600503207440704001c4014801c0e054413080130380603c01c800d4400310b120b4880c07042d0780711803404c000c6200b0b801403000c0c002038540b01e410300c0c140131050950a003080b40c40300340c1000e0000340c481200520361000c03803260522036000c80715840028030300103090118400c16003006c0c481116580e9011040c0c0650359000c00c4480c0c0705e0760341c0c900945404014904c1c41e0604196130f5078045803503106a202041288800041c1c440c0d001407403400710101c80781210010801e0b40201031401c0840c1c0508800d1044610040c13006688a0300c4010320030300ca600396803000096038005010482146801e0040c5807030444d060321541c1c14030300100c00007880050381c02e001c0b409001c18400526418148002110302400a09021800d0120540c0301c0d40001e5000414003083e00e0f10301000714410048081c19580c00901c001c10303100400342001c003000300840004d420507481c140e0101d04110700da031040c85694403441a04002492940c580031005e401d160b4002d2110 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 738274496 1250 738273246 738273257
    0x40b0117100b030109080a090303020706081311150a0e0906101e031b0801061d031c0e0a03080301061719020c010f1e20030c0901020703120504090c 65
    0x102604034006040c079034a903500200490200d1501012a0042101d6400601484c60004a004009400000040887e807080c0e088401c9550381e800101d516290035212403201091020300306020a01c2400a0f440820005000390320605058441441c41d905c683c0240f80030607051691040d407450000c080c3c5034401d0094841184505420000400c031074210800000200c00c8030f040c050344581300760302518030a1a0b082c0d11100c20002c01a0180c5054007d02c6403c00060455980000406000285400181015004049480d40a1100e11074115016601000c001100400c4a490b81c1c6136010000118010f20000d0364a5051000c020100b8401101c3c00700707080741d09030521020045600809108041203580182c81c1e207441d0754079901401000d8407513a10b0b941003a00300d010320003902640200f84003400b0010005100c4240000e030583e144a03a0191001e00c060000a851a800ca4000d100c0004148140c0750403a8582d62104900225640d100d00011401f03c0c05004c904d620b485030002c00911400d24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 738275746 1250 738274496 738274529
    0xe09090120071110020a050d0e0906010219060c12060f1e2d091514040b03300c060a0c080402090402010c052d070b030105060301030b0c0702090906040b01 68
    0xc4401c603001c0c480103a80201e440100d400340140c0309100021509034090155039600740e0400c4001d100071010307272500e8495101c4001060a43d800020081034113132202c1580210700c0c4064440a0041c58090701407001c0c001c20b44000d80314000740384035400240601d10281d801403401c10302401d50000e5141140b101744803111005200d0a07042402c92070a11041c0c0000b503840c900309201c00250a005980200e020314100300821003d0000b030050302060b14069171182841030001e1080006940c3d000001d02e4050704104441030b5450350a031a45825070102a0414141d070702c0c800b05003181e03580803003070041042c1c1118052010800b003d01540f44260030a1900c0811030070107800141c02c01d00042d00080c1481520030420040000c140314107a40d9641040c10106803000c80c0c2d140310080714019080300c1c0d044c026180041040c000d00d205482c180c07040581043e044d03a0079655503442800014001c0e81d01e51905021410040c0d880c0c505145c4035148030b00150500d42003902d000306049006030403d0151400240c41c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 738276996 1250 738275746 738275753
    0x10b07020a1a0702060d05060906010203270307030516060e060703080c130906060c0302010501091a060a1e09030b0906040803150f18010f150f0309030e0909012007 72
    0x111406461118121400a03030240240c1d071020b1045403c001d4000801244405459000341d201d1441800c0c1581c00402555a1034012a141d01c18006009078400d440d606c2c0030300843e075004401d807041c0030143c11100700300e880e511140d140000342c00c007601916461b500140b001076840003505250381404e83c2d41d24142103032030b9006089000020076441e000f06e00412089841c81c8024180b50040008100c01c1182c1615000002c240e108814026009036083ca400011590020300c1114910000c010302010f0a11503e8108000c550110181c8820050b000c42c05502c98144190700031048845502c803407174414903500c0c010305d184500030160307a29a0081020000031034141d404407035000302e4402060a141c1c0038900011407548041150301c1d0031680c0350850f03515010f00b05164605840c030301d1001543c0c2a46d9480021324120003c2503d40004c2c0003070585080c0300d8041e0300b080440500c42c2c100400c034400c10710041035001c035003220310b0441c1e6034480c0380070040c2454030300d00b0000001c0c800d40c00500d8401940ca = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 738278246 1250 738276996 738277009
    0x231510080d0311190c3008091203060303042403110c1510080a060f1d0c010c030e1f030b0f01090509042f0a060507050a060b04180c0e010b0702 63
    0x210101100040202c4c1a12152140f01c0780070380e00343d000c1125014000240142c141c0b00350002000018240006580340200380500e58451003454840000c042d504d0301d401506da601c0c5c001401a0790503201c28080810001107103840d244c2034810407400000e080c854201e0080580708a070816140c101000c2001c0f004c03003500842c80d040040402100d02c4030540b10480340b40b4444500b9400308032240a009001000c0203015000840700e804401c0b82440028804800d05407200d22540c0f07504410b902c000c2d8800955400f0f0a44008814000c1c1040301519100340c020440b03010f80012402141c0240c48402568260907219100030a6000d480300608420682d0001e06500303034a02600e48105003100000301040304034040c81032840300b64401c000030291b4600c02100e4410b540c6488621840c43c462020402c24400c0c4161194584c00800070207807580c0c56212400103055400d040d54006403180501c0d0300380e0038188001001181b042d40301e0001c0d2403620000c15505034040e00001030422007040002c02698464 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 738279496 1250 738278246 738278257
    0x1303050d0504031b0b100f0806070c020a09050103030c06050a0b0a050f04090c060909060506071110030b1512010e04020d0206030726060f010c231510080d0311 70
    0x10503000495884606080c2c0f40d50381d080780201c00107002000c4100c01c0100740e9004900541c101052000c0d0551159192040c3c0b41e1039020300c10b900e034403110000d10510b00c5440d510542500103808000116203440c0002d060f190f00340c10680204178a4030b01902040303039074804c207580250440c000308040510000050703043c641c0303882a580700e8003600d5607607009541c481e8012140184e01803066110b142c0e4988024040c04000d11804c00791314275140340021181410b0048880c030541c000a00b5202c0d41e400380070080201415181001010303981d90b9209003d888100b00d040071500006405c03512150101d9100a40301070581000e0441d010082c00d0000607221690200c0901d03074102c0748241c0340d40c0c5401c0100c0c0c6c0130b40315402c0b1112894a040c5500010b149412045000f89015511301505100c6c03a401901c80040d0a030008109a0b04507a002d100010000140c0c0020408003060301c07010703507c0000062865030280c5036083d40512290b810490030f01e080060040c40c4145041c00e1000501c400c0149041d030240 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 738280746 1250 738279496 738279517
    0x604050705280e18070e0c400f12121205101802070b0c030604090204050a020a0f0c0b04030f090b0c010509250902070204021204031106130305 63
    0x3000a01030706040707a8200126000c000004400b0310541d0b46106040068054550540d00681d040b0420084a0045007100554040140301161a181c0340c250000d10362101d08034904040c82d44200414200c8081c507a90b96101c00d504e907105640342115207034805042258045045060b09003810420140700c0c0903000142c0750000401d80b40244e804009407443c95040707440c03d40081c940410000b55602ca000d2400c2969003c1552502158020955100300c0c0308a40024240c0c0c44030302c002940b0340c0b1404c0001d690107903015102103070602c030540c04078043d02d005a4000956070340201e6140d40c0320b0360045101600000c9032a000520740456151600c0da2900944003408005403503440500c070343c0c0214014001000710790345141d9030b80049400980240303010f035584003981c055065005140c0c0c001220404506156080c0c82000c0d51420030400001e6212501c201d070082c0c0c0903c6420281001480c0d10f47c4507500a44078041400c0c01403640340e0500c0e1008042e091444017034410040441e40c0304003030781e084182 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 738281996 1250 738280746 738280759
    0x9070e1008100e0f061602120301060507110a0b070305041e030f060507020109080304050f07140310050a0b060705060406050c030c04050d141c031802010e06032508090c030604050705 80
    0x119003420f03d06103103484211010502c62102480503039078002550803c05041542030394070b08600d20041d003045100a105000c000344081c0a070601007950a07a000c100020028469030300c141d0b845d1001d24140d007110300d05902081c008102082051040f800790340034207180c4401815a42c0c00c40d51103144407444038030007a19a590729000140518000d40c00b445415030801c40741d64581c6894a0900d96401aa000303081039401026000144010450181190800000c3c082d000c0d204818110308000c15000313001507900d545891582ea196280d03400104140e500030400707440c282c9400d090200a450300078003500031000d010000c110410410409950a840c802c540a402682d0700c3d0901d406140103410900007107010714441c4d6100016039008001c1111003c0e10b091210003041310782c0c0d00c481000c8110190100b041455510350b5490030600450344080041d010100c00c038140e48030480a180060907650101c0c5101060012080003000001044d074000c0b07005242901d01603581c0b0341c4510700f6200da54007616 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 738283246 1250 738281996 738282011
    0x30b07081b0d020c010f0501030b01051e060307180605091f1e030e1203010e010e1f0602100605040b2b0212060f010509010305030f090409060509070e100810 69
    0x2500800205001a124406151201d512160310302c02944000100300081d8a0074507080701c0101079015003412603400c07081248032a8640f9003441854013001914030301c203042c4801c5104807a0b6a500c0554000e9015585980060b07004c2180c65400a90680010081c010140240202c669500304940f8130010910725602e00032883e44400d681150085024020a616071020000d220794544d000b00703803945024089502c500300040352051188000c0c00741d03003d800000c60050009038000e0341716070380108114082c421011054052428000455040311005800003c074110110415000d41c50142c10100d50805c10103440c0070008084a0340314000700311074490a0421011300e1002c90f00784041a0300a071100c82416040c0c1010742d2105400c49440d20a1000a0004a064242201d009041e207a100c0e004601c1d220b8906e209002c203400030000c150344107444124a9000420b039008481c001c003a0385006041c11410200004c0c14050004c00703201048005079820440c4110014540c0b50a80390620f0000704113 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 738284496 1250 738283246 738283261
    0x605010609080723030a0b040c05060a1b03020c030706030c0201050f15090a020f0426010c051b03070f060506090702010e03090402090612090607020f011503080307031b050a110106030b0708 83
    0x184c11810055a05004020810061080c1c00300c0b00c5200d01d11a00d0048500364480c000c100490007000c41d8107000640411301c1807402011885185401c0e806401150203070011280000e28001c1c0540150001a44881c81000e901e5024024079412440007078001c95130303140c010711600c451860607080314440c004000c046003da2400c0d82c1151814140582c1055440c1d4a0302c250b903c2a00344103400300800800381c0340c1d11a942c00103100f441d003100310715603a051800301c240031070220294506407003114600080001d4000103142c00d007512507540c07140700c3c00f01c0c041c80c0010821440b104020503110559042c1039841e000010080101c0719103c008540058948e540400030480b140a00107048071255001c8050118a640004a031031292005a00326030b0018440640c950988210640500c24081d0800c0188009200c54010707682c000c426140005881401811034a10801200328510115030006402d034851036202c00741614498001d002441800d1569895020100c8028070b0b004c100001d210116010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 738285746 1250 738284496 738284549
    0x12030b0312070b1b0d061403160b0d020c0d0c050c030607020d200a030804050d05070206091324050f0405010f0b0c1204060e131a06030c131206050106090807 69
    0x3610895004684803020911768000030041401135101422200207810814640040d0b11180e0844007517281d03002903d0541310265682142e81801101c5400748100ca1888004005010005c1820ba0b50302c1601c50440c02c149080048426020b4065004075041021564000401e191905400e1509500c005508034200761807a120580d0030b0714900850003000240360f408101240224013420a035100b580703c040c0d059505218021000b0b400607401d201044c114648030500c1c0f2440100c44101040398a1003003103510b03c2c5402402c440e000f007184c501c2d080c841424124039031405000d050301c00300308550400c0e021450001807031003801d60502e80041e11107461103042c402402c0b07822072000a140c50710f071100d10140050095040c40381c002c8624401840b030703840781401200414511010404110b050400a20446900c002c0005210400c1002046036412420081900503d00d48509021100303a170310f0801c058840691100040124854080c01050804100e90301140e14020f0103d40d60402c02150098 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 738286996 1250 738285746 738285781
    0x20a0f021002011103100f061e03051b03182104051504051203030906070c120e150a03020d0b010807080c090d2003010c080903040501050d0902030a12030b0312070b 72
    0x49132400481440404040b000043c8103407080c4001044549803034440490301070745200c0c82000506840100400c1481c040e501060b0010b81c07005034088034400d400c0c004031996000303480081052868021040380b1020078004003001c00d900c811581202d80e10400429100d0240c0e008403841120107003099803100540c1000c660080001600702d121a50381c0003845506da0b00101c846039418080d10002840c150300c03582e08100310131b621680444016208040803204603d01281e030725004241c2001410080e20b6160242982c0d0b00c5175034000d07a94800b01e1002c0341c19240e207904440d041c0401d0340180584c1580080201c2ea20083c6c0c182400d849043ca03c00251955510b1343c40070b044001441046000c1800c0c0261185d44842c0a40081c003030b8003c056421210151700715003001e4140c0007844140703c41e611a4008090f100010240030464005507000241894102328040390fa110300350503003a40c81505405030380800700084028240c840069001c1300d00300d01c28070790000c24082a02c40018001c0280307042d00c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 738288246 1250 738286996 738287021
    0xc0a03020f060c1f060e0402181b0d02040618080a140c090406060303111b010e04061703031905070504170313060503190e100207020a030609030e040c020a0f02100201 73
    0x40b24107031032004100c00307135030021000c0201c6401c0c00c20210710b0301c2429980500030380d0302803c190101d9085059407490000003915604101c0a02441c503c90300d0500806448000f00f000c0005940c1c928190016200c282da056a408012161210070050f4140114940c500346411800000c11103100510044c100002c401300355a0108070a400e100034480d89901070b0b0192442130300c0d00c2414140c40c94200e5a204138100070740301d28180c502c03240902c5521882c616410108046c0000c41c003e502c5403003c0b0a2490f0304084001598004402c2048200484545605085056001304460b00b02980001e043e07224074004c0c030005682e148041a010b034820021505000c15410410540c1034444030010002c1e0310580322520380112207040070200451034030448013440c0f094070003040c001c50f80da1013140103500302400030b036405081c4640c00408035000c0d001e009103551180d034070000750601e09000c0004541260541101719803008980700002030403120394a451a40454403080c0d0025904003c07400340c1301002411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 738289496 1250 738288246 738288253
    0x60c051905060406060608160e0a1a03060103150b03160504240210021303020d02040603080a020102030601030f06030209060f04110a1e03050c03040609110a080d0e030c0a03020f060c 80
    0x150140326000c03440c2c0e0701661003010144605941c070041101e040b40140d0b00d00e10344030304e1200c0d03040d085405100e202d4a0340c000031b0505550559507980303e10344800280000c0c0d0000d0400001c112403503915106440d00202c03c041e1740c0b0b40c1c4504002011000340802010040c1401645101e956480c9c06503090301c00034032109100b052449003140c0b142040d4189802000098400c44c2c101c26540581c50082d200541030800500103a41d2a540811a820900c50700513a080350303459202102042c4106e0051a02c280190005a0b50782081d2000504903407940c03c04c2c00d001850b20b00c0600059945d9101c180d080750003104e4842c415852140003800410084444508030000045c403014904c1c4c0114103d001c242000c00010080107840009030140c43c001c1350480c1050b0002c200041c000786490788070059030340c040c4590000d0030300018041080f08001e03810601c544e510050701c0002081d8092815000c19805502034102401ca00001c40e1515400307000c002d21070041860f0707c001c151100710542d05000303022000c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 738290746 1250 738289496 738289543
    0x40b0409020909101215090c0807170604080306010305040302071e030c050a06020a1401020705150609070e03121b0321071b0204020a1707020304061b020a060c05 71
    0x1280c0095010124041c02061040c0010300040410600c8000320380c0c0782d401c0840c040d00142d40e800502a014000030050503514245607020403c064a240003034007440703004117a070318200954642d0041c8a00d1100302c00342e00400c10040090541400c0c0e070b802c02404e00f00800c03291a94603050707081c82d0564000044014042c003840c5040740c500b140310012280640f034518001900c3c4c1c000e0040088160054402580c004482e110005100340d4500401060f1b840005003401400d994044c100264140b0b00d07042c40e8151410300c41149012040a6000b40131400c0800400c3d21800100e5129504900021560f40c00421b072100f1201440030745006600405040d6940c404080020592107141b41e011881c0c070780007020015602d40d010f885034034407400003045040403121071542040b01941c4840d0716042003051310100c0f40300b0700e41c070003103224000c040d990003840d121424400c1c0100902820102c0041c1721f890004000d0250b15600520340658851f071406039141c131043c1c1491b03464485e0002180c80300e400045c40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 738291996 1250 738290746 738290759
    0x80c0a050c15070c060c170f0316110c06030c0c01290a06080408180d050105180a02013905010c0e01090b0327010903120c05030f010911040b04 63
    0x1d0001008078100c4440c0844904a00d107814a07004400c8002e00d80c4c0c0919109114181c0107200c9214085d21a60403403004070203030a107081658100704030810a9580100c2402026140c80d171010244045034500100c4440e20b0384510395540403113006d03d13400399030000041170010368418101c07516198240000d0043c403107c02c4198201010501c0ca082902c10201c010300d2051904900d41e404603807241e5202c0720746880700c2d2600382041d44a0b0807032202062002c0c1c90550700303844002040c0700743c40c00742c0b00020751031404101c90301c3d500b00c0074000e501540e0000800000181c0c1c02c108079003000c20024240c5400600e612a4a9551139041e9801c0600f45181c42803100800805401c92208a40315a8440004605840040d1503042d4140140c9035500020300005500d814900100700d2180b2104040001a1281074070290860b03100300310a0300002d00c58100380040001038040d131841100549804c52562030b020090b0b04d020309042c002c1c007100ea030b100d40120a000c90900140c5000e058001441ca689654611 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 738293246 1250 738291996 738292003
    0x201031d0c0a090606020607080a0f11091503060612040c052e08100306020c0106030c0b07060b0312030708041730010f060507030215040521160609080c0a05 69
    0x19407162003030007404808950380300c2c075004c0c00c022100e4640041c003158980450680301150018840140c2c1d655550114404d030301140102d207000b071100c62140f03999401b14418000014000342000b00800010030501c2050346900080300e8075040034405020f1a501c89140c00c480c080c1c0d1b01e40c8200d0748550341404a80c0342c030344c01001001020301e030210b40511f00150a5001c0d22610b00490307411404008112040000c20a160014002c411405000242c1151603940740f50500c0919003051603600c201042040400149100f0303442e10310350490080c951214103c1d02240782d8440200707140c080000e0f0300003103002c110402110f11450090000110344800100c0c451241c102c0505243c0d500d681549903643c4508000100d503503042c1c50901f100f503d0001c1c2000c2c400c0e1016446031404500b184141201054004505003625024034441c00280800c05060725041d001d4100200c1c0c1d41300d21380c004009610351019610b0000c02c01d10341c0110003242c0705501d42400e5495000d845600d50050141882c3d0008101c00407 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 738294496 1250 738293246 738293263
    0x906060201020415110a0215070b09011e11031b040902030c0304200109091e0609060e0c1602090a06030609060608010c1403010b09150a0309060b0105030c030a090201031d 75
    0x800c1007a880320100d04d044039005688110719026800c402c01160150800d041101003003030751424618035040203659582a03888040f161012145d42d036203410310120510208103109443c0910741401001c103000c103980c096100c050091140c05a02800e244e900f0b52000c0281c0d0010840b5040864680c9080d541c40386a90f4001c58040f580000301a1400f610b28880070140130300380c401a507410200f03509209030003004240da20500807030803543c1104404200041e00074000940580400826003070329104101c0c01701c0c1005800c520b0320f11410303c01240e020300c4424008910b540c04652451040e12586e0080c00201115040501494101071410b02840f2a0380c11000880b00910020042411840803c03509090008081e410f0590200010041404810701400d43c80c0002031040c144000114141c100300d078405100c840229403034102042c140641c0c0e102c0d400104c0428209a8a585003486400b400c0d03200040056402c0c41c4c3d50000c59043d644030b98040c0d1100b4040408030039020080d203070910341e6019034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 738295746 1250 738294496 738294509
    0x903030b0a0605161b080c09011409041113051302090a06060509120c031f0c02030a09090c0c141501080a120c0503090d0b060906120607050702010909060602010204 72
    0x184040e0300c4240c00c022061508903103050351054100b4001c0034240c1103c2c40e070444140c82145c2c0010b00a583c86a01c03d4080c0f004200103801024809048070900c9803140d0145d000303881000c04a104420325031500180d540e0301c207038070049804503881441c00007001c44404030041d8600501d403038100124481c6000411307000078000c5a16400076500c0c440340c0d001383e41540c01101c002500600c400721950401d6002b042c121a0b0749026500191000b00c007180c40c1004032848001c50180c00c0111521800042c0729a85000c011031024501d0f100c4070b10b0b00542171149510505000703964a81c100321046d0700c510410b60420750322050201b81c408481b040315990b80003a103861010444807500020b8074030400a00514040d92000084124000002082d01c0180d603580341510b16000030482101c0b141d072441c55a000480c40f0300340034507031402c00c1c805026900304d0041801c0d01547e480030312001ca2031000144168407003410f14000307070340c2c0c02c4520040703802c0040c9a0143c0003884c10008082140c0e0307019000350095604 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 738296996 1250 738295746 738295751
    0x306280507051c0b13110403080f090a09060f0b0d0b090c0a090e040b0c0a02030403050a080703030e0d0c060e0f030c060109050714030109090204020705190b090106080c06030604060803030109090303 87
    0x60040e091084400914038141d001c188299035880113007040e00141840c46ca11902c0c1d6003010f50341c0c0c031080341503440b00b1000e40441500107503160203850680d0882d0003400b61220200540c80c1800c0c2410304000440c01030006400011074160700d040f5554018140700800908803c1050414402803655030304a01045d40105007403002c085014a0000030f2580b099400c40c01402003a00c0f003155800c01c40c0e110806070000c6001c208000f00c0800c1c010440031a1192144d00502ea5030101820010210380b0515011140c0790860314001040c55030200c01545040d420040004174000390303400c01d5280804104800e03100d4040401e81003490310307021408504880d140c00b418400c950714200d0071118131074003621030b500308101070006011080340d84d0701404007548050070052904041d0749540c0e1411581c568414070b502c00214551081010304031a8a80016803903009020b0b250805401039140c0c4104410540694004070000d40c0c1503485400a0303006055410a0300d40d1780d61035006c0e140189c0f000fa041600803e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 738298246 1250 738296996 738297037
    0xf0d050d1101020a09120f1a090606060415081f0303090e0a0b01020a080f0f12070f02060907031b15080a06060905010e090402010c02060a031e050105030628050705 72
    0x1038043c02201e01e48945551101a21800e080108170407082024066505c441c2118544001680304c1c0b0b210101c2d15103e0301c03020030610345981c1d200c0c9407801c0104104c1c0900300a000400044c120034090100380703416424a280180d43d00c0901c00310701e60055075131158802ca201400801c0c190880341942c00c0d140c407038003002c0d140c1e55049c0b1608181c0d20504001d50040e488160b0390b0001c038500788040d01a4604500d0094603041507610400116080104059508500e00d01841031907504a01c0c0f0043c448200d0010f020f1138503240361042d40300d40e040d01c00034010010070862400151401ca8420300500200c05070302009103221040288ad0b41c0c41110380d00000c9107070600200d013060140c01c0a104603035050307640c0b020249003103091058440020304201d052040e082510390050f41c0e0ba2000d040b84440907500000e0b2000031034181e41c0035042d01d058045105162000510054402090f01c6600c203035003841200f10f821890000110b032910b011006810b0a1800c030600000130341c401c0042403019888d080441054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 738299496 1250 738298246 738298277
    0x10206010f030c0512030f0d0b0108060907140c0c0d0507060906020f0a061109041a130207080412050f0d1e05030906190e1603022b03030b0f0d050d 65
    0x41049000c050610310714003d0400041c604104280e0f26192180d0a403414075006240d14200c0780c115240c0d01808944030480e01c03005580c0300180715031080088178400400d04084d407001d4004201d00039203103d9084001341d00c100c40340b000c00480d201c07000050000c80004001c1d042c510342303a1940d406a4070018001503000103003944001140c40b2481000c201070440b031503041e500c0300d0040103050b42000002c10300380111065695a0310504e0100040140000340c1881d0980400007188101c2c0079a00304035105000c40004204500203583c16a82c8500c92140d249505003406803501d00e10a092172500d204041c00044001c1d403040c0d0201c0381d41c00303640b9a4400d281c1c081d00191900e000440e55007031168000c0000908990040d01100e0704030039040c20000e45529240351442c213006405100380c000003ea20401c104605010703810b01d002403900745001e0703140802c880c40d0181c5507400140243c101510748500d81d00340e58650b11418070044008080785003038006c51503e01d4980e40d03003802480209002e2221040700c3d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 738300746 1250 738299496 738299519
    0x20f1803010624051e0304030c15060303021506010c0f060902130c0e041e140f09030708070f020402160b16030612020d1506120501060603020703080604090203150a020901020601 78
    0xf40800d4503810500e0040510443d11a0010913080d600c0700c201d07200b120504c07080030008500460182c3e480c03a8500906040c014040c1801c0310740c0d0411a490a081000404d6012964035001401c140340745050b0b4a440c4012030300c0100054000d4024000400018100442640031001c00e620a55010250380c55003019003040390540544030380030a050180601d802e1070580d0107140f6901c400d07901810303000c00c00c030101803c82d1010418540c450500509100c0ca8000d071400980c1e10600000046142c1121603551200e0740c041c5800042c007003c1c4880c01c060465965070156141013020b152040c81c8400c3c1d906020000100545101140241a81c06843ca1501c03a008040031f40b01922500744865601c4d03800c1c000040c50030340d0706480b05008802c8100e43c00c0080c0c0030f050b009100c40002c5a8031140c1d41d050060843e100799104000345481040024002a0820030349030b4000000c45000400c002d0b1800428103100780080c0303042c00d449040c4108008820560b0246c44d109a007a82100c4d203d03a22040da5412 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 738301996 1250 738300746 738300779
    0x307050a050f040f181e050325021302030123061c02070602040303020c030f1605010503090a050d0810140604050d0c1d06040c05091e0301020f18030106 67
    0x8001100000500c51401c0004400c15802c502400c00a410b40000b4481c42c00c880710700340b0140c0034294800e09001804254101070410202d0150012501d007410b0340d5050f41c038400c007404156513198500d116031012107419a0302c54213540141130082e04c1e294000c2044d009502c2402500c0340702c0c80c0c1c0c6215051448007240101c0d10f042001d0042440d0000d80e009400e17a01040403d2010001e03002c009600001d07032180080d000961194008200344002e801c20103060410152110045a10800e2101110035001d42ca01048272400e00304036659846800580b41040d40b2048040e009105211400782c000c1e51000000d4452103004902e0403016846070300000c03503840454455a40100240310910141c5032591a82c0324443c400c807043c0c0c080a40e2a20f1043c1e2807942d6040710b204c5178074100104500c81c01c10303000700008180e0301c0c40c0c81403410360540c00140080700c0c96031560410b2a0300788030303455058800354111b81805041001c0c440d201c94106405407848000c140f00240070b54246500001d2741e1041c0c108551 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 738303246 1250 738301996 738301999
    0xf090124170c12180c1c0213020904060b0c0d1b020409050c04051503060c03150901030506092b0f0908100603150504080f030604141602150907060c1103070f080c030705 74
    0x40c5c01d0800b00104450b10001c0340000181e1a060200000143e0303c0f511018503c4d16039030409a210b00d440001c2104130354056101d81c552040410190420380320220303050100c06903904000c8600440040407908001418600175000f900c4e140750481440400101d5400204040702e0500080d6140b121070100c1c0c030b180c0f50f02c19405500c0140442d05070f84c0c018000c0d66011500300d04403818500c10100051884030f0a03442a11706420860a100094800340850005882910960b50f507007807030003070505c0f450303504c0301d11020400856110725007400c1d110f52041c80003010403004440354072464445840050420744000ca50100941341494a1948140070389032290f80c10411150400290f0074109000d0341c00141300c4c52384a41c2d50740f81022613008910040f801501c034038500090441901c04040d16202100721503a44c1c00c480c0204100c3c04810000d210303c1036540303d03c5c00c00000105071134140f2500a110303001c554540200300012504584030300d100380490351104211000921100c050545410301c50180740d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 738304496 1250 738303246 738303253
    0x203190c111b060d060f090f0501030b04150b040c0f080117190804030606030303240f2105150610140d1d01090b060f090124170c1218 59
    0x49000092000441c80381c1000c1c203c0391501500e000d43d0300031146503810544000d0140902844110060300c00c4007444001400208060b5040d83c43e500000c4000510080004044000781044895207810000b51a00007400a00550a000d08080c10012040901800107507288000040000034041c0b0840c582c028074010703200400707c0a2078160600966001582c543c03038104000070014000e845008019402941d000404111611440c41c4070f1050620fa0800c21211a0f014010108001010001c4420050b0028801c0e04102c000c0320010078940c40290540c0203482d080180c1100380554544180821182c4c000c642840d041c05841083c511050000ea80d00c2c14002e25450600603481803002ca80441d11800241c105d07a0b8030390b420356403108000c80384ca0340701c030052007403d0405c4140400b40c440211440502581017000c5103903e14002d13441500102009100449005c2c000d80c03110388448a01c1d12401424904850300014561000d403803501040015000100c03900c4240e4104000304420304082c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 738305746 1250 738304496 738304513
    0xa0501080711120a0306080c010e0910050307170111250c090e07080c0a060e09060d0803010602032208060a050702010e161508220809040203190c11 65
    0x11106a140100304a060103250310340c422021404000005804244100c069601e01c01144c0040540305d4650282c4c0700703540901007564a5a800003600c891030101138481b0342403951800c0300d800d065941d56100385d804d401500c8010682c3d203100d0000e2a04160080024054003060080703510040c4180041c9103540c035081d031051203c10207013501078640280103901d0b07200c00355145e51200c4100d8545016003041a80080780070420408103014107240d265040320060720040c0303058009003105100101240c894502040000d4890351040d804500741500206401e407290f8640e00e000c0e66035804581c010480c401e281008071070400003410b48505589408005c0d20301500d559540d03d014100c0580741200b99502d80d0000c010300241007200069441d40c2c2d0042c203039950304e8170600300139420f0000c4031035003004651802c1000041002021500b0201c604d00d086881e50018201080d0030300503282015030090001007401580d210061050341d111403130b0081000f00b04042c0100340d62182411251240b150804280c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 738306996 1250 738305746 738305749
    0x1505010e041e030c020603011221050d0f060b16060b060403020a03081303060516032007080a0302040e0a061502060708060d110a030629010504051e040603060b011d0a05 74
    0x8032200b14403d00304120202c4040d4005146500300340c01013010203091303026020074000b00818407440b001b441f20044038405900034008009201d140e1003544e080c0e803110507000050905500820040001e40c05194841c1900f1071100080c103000c03201902c076030f8208901c091092a05c0012101120b81c0101560811840c1d40d4500c070003500456942504454070741d4002020038a6800343d148260742402860103180b95054024046441031842041d46005001c0c00d0302c072140d1010b00701c1e04595080002c05860300b10451048010b80b017107800203d002c4004030f09200a15a80d50840303000c0e90100509006024180141247e90b400226541d9001448440100e81103040c0ba00070981341902810440d82c10f08013003030115044140982c02103459a0350b0b0030300c020140107200020a03001d0007100d101c001e04415400002c0c024000e0340641c51040c04402c00380790614071103182690f50b83c64042c0052000a94a04091001309158010300c1d000c986110210030303003002040380c000c0383c100b80240795a03485800c150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 738308246 1250 738306996 738307043
    0x302030f15030a02010c08120108060a180c21051b130c090e310c1203270503011d0705060a081b041d010f06170a0b15071505010e04 58
    0x2e016a8002c00801000403411908c0c446503002c0c2c0080d100070011414648440400c444080711400003201030180300c940003403030300701020088644080c1140051143d080f800b68640c01842d800618520460502c0c1ea581d00c030280380801c40c500120f81000d0000b6120b43d02d007042d244200d5011001a401507824852480410b21981c1c20400481a41e512841044000c25000c034580090405801c00c4142110811090b07080103405022000d203012100740042d074010b49414840c0041e03d18581c01c4041403400d0b0202d204005004103c004d000780310160605454030008240380641d00b0447c01010804202400c0c09030881d0500ca2265888040c1a078820610084100b214040500100c6041100003541610b508ec090200070f075410512805501d001e1405031030440b680c1c003203000d10401808954840380e58104655000c1400c050201e0004101c00008a6a01c1d210035010321002d4081030f41018402401c0302c3d0300801040840402c40d5980301c4240d004d640da02241c0051401c1e950080c102d0440c42041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 738309352 1106 738308246 738308267
    0x4020403110411090a0e2203050c07090605060a0c0c26010e011812090807170c0303041a0c0703061b0206072d0c060c0302030f15030a0201 61
    0x140c085041d184a42c0f00b1061b50300e40e26400200d2200c00ba140d88075480d40250007410202040c0e10300580303030340c0002003105440d1040d11000b08500303460707218400c1a104003c1c420f07800c0c144100e82c101d442c1d841d0304500715100924910000388606291a0050a0702441c810213002014030740e00b65400c60b2812203030303220b060381041d903540c90314007038040713900c1c115038005010092a0701c1c0d0070802e55100030b0310352240315503100d48030000404260b070841088021086c08142c40e46190405c0400d5501d010318010704a00c98800040c40a206074285c0040040414210075100c2d402c1d602e0b242c0000322441000b507008039580d03001512206030750500003584e000f101800e01c820074150529900200d100c5481d019510101c001410030035650007400c62009860f44aa01807040c030308041d000602940096814858002115001ca0941c1c0050004440e080300701030001e0902a40e19001164003c900 = true := by decide +kernel

theorem cover : BRFrame.Cov 738129496 738309352 := by
  have h0 := BRFrame.cov_init 738129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 738129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 738129496 ≤ n) (h2 : n < 738309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
