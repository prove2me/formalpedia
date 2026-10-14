-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:03:26.12786+00:00
-- url     : https://prove2.me/submissions/5529ef5a-0983-4679-a2eb-65af11a23ed7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 190287769 ≤ n < 190467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 190289019 1250 190287769 190287791
    0x1806090406032406150e3a02031c0f05070606050a090207050d030b03030a08130f0b010f06020105040f02121903020105150d020f012303010e012105061315 68
    0xb4201014007006402811320800098003114a12900202609a12810209030400d401c0c80303d940c0e1841041c40d5503402880904007500c490f8141c8858003001c0304070300c0c2050f4a0a005151038924003101ca48040001000780c400403d5004000b07070813a807201d150851340c80f1054105600502001d8005130760050504c00001007500d442c3c0c0c0100349240c89202940c0e801d030340300103054080f126940ca04076003540041100d400450b100d00c444a0b0b110240c1405007100c00200d40301c000c0690245a400c640d141c03029001488030308420022080140258030082c071681c60145d40e2b0014004a03800b009001c0c80000007402c620010500445981c401c420700504840e15a80c1002406428103868002d40920311900703550050a06250041c5d200d07030080c00c641e462141010045441240090914481c1844100d0507146101003034001c60007070554034510641941044000300b81c880f000602104c2c0380c1c00c1030744a5400641c010528552042c1c6919448101e00d184e401c040c0309a00780c000e030713900050349424003041c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 190290269 1250 190289019 190289063
    0x615030f0114060f090f040308100b030a150503070513050402030309090901200f0304170d0606080103020f011e03110f0304060905071e1205010905060c0a0311180609040603 76
    0x481400115103c0c4c419001c044280480c054080d249400602d0300d00c000a400310380121034186e0440300a071080d0310b00c182d031415000c005420944000da04030352107518940c840203801000c01c0103030130124050039002c4e150600141c01c4018003011040340c280c8850001d010b55074180261001b8090142100000389820714840340240707103544500d03646081c902c5411603421075950642d5491701035003901c946107848035100e0107000701c04034100c8101a075007040902c0d5014094010000148120b0f2180070095056204018103640c03950109810800707110001581c420b001400d6086400320390400181c101404d087c006854462880c600d09011800002c0c0401c0000c01e520842105d07016200383c410403510b5201d03000d085520140302824407403500b03c092042412054200000740c3c8148000120801c96550300ba003040310444010000356804905101c015400d802280d8451782c04d03400d1686401c4410b80e01146050401c88014081d41000c5140003039a12680e0103d4003954000c0f085c1a0340b8a00c4c181c40d84 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 190291519 1250 190290269 190290271
    0x140708070c09050f0402060901110c131e0b01090b071104090f030f020a05030301060f090f15020d09080d030902040b0d060501060e01030e1c260114060307020615030f0114 75
    0x81c940324070f0840040c0308100e510019034060381d0700070035051429103c4801142c1e1780d40d1608540e11140035003003524181e0b030b0712404455400c1103c5040820031820072030041c0c98948034403c0350442e4500705a078100303090380d000c0000301c20703180f440207617988860340c9007000306010b10206c16060304603280ca114902840001400c3c0d080480c82965003d0803011030311000c90712100010320040143e807041c0010f00c940360050152043c8440c00e85091014603699a030710110035a50359103c00043c0189400545075140d0510003414049000d0800140d480e140c6005580e54580103911035080503aa260304008640d1103070050102c1c090018003e06c620a02ca05107080206000e102e92004284480025902035020717009080c0c050b24040007500d0f1a00102038001540d8201013862000c2080300100d4003c0e9010880b80d20105404a8010750102c0d030515840000d0000350400f143e1085c0300500070032441550000720241c2c484000d00301c00301d000400303001003403034181d08076520b66042d4200781360020b00010b010841 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 190292769 1250 190291519 190291529
    0x201210513140c0a170102220509011203120b0607060f0f0c17010b0f0f07030206010e010b040803091003110f03041a040807120509040501030b09010609020301080a0201140708070c 79
    0x220401440207591980c941c003043d08650400d12a80303080001e90441030300c10350703001300b81000546008010011403038085001c14654240e0981c4520504c5a8105454050301410082c044010040844d40300070341145800010121240d0700d4400408507911a0360556011541c028010b00008540403c24070180c4a0b40010542d29840c000071405c0c1c46100786250140800315000111540c0d091003e000001c1c3d00480110042440800c034002d40700c40d005009100c030398000e0340034000710b50400e503131032400c501e041e880142220f034140130500205c02e000c411544561000c842c00c1c0c01c04c5440050680c00780107a984c10b000b004c48049500f040483d18440258840c51040714100583e40294a20710941d40b82594094800542030221400242803c1105280c018176400c085051a08890005003583da01341c00480c2c400f0034840078840c0c0620240286005449034480550542d0704040445540740b407249000780c100040680b001c403205183d101124804e5412200b490740c4c50000d41004035042c000c600c65 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 190294019 1250 190292769 190292783
    0x40e0414010603020907030509060703060605120c040e0c120c0f09040903091e090e0111040b0a1b060e2a010c060609110705070807030203070e060f090a0507030c08060d0201210513 79
    0x12f1071562081c8540c0342541e0054462504203641c10008007400c1400400780d142c044000c1002146150319040610700c14040b05801719522242c0c102004200040603050380318100e401e0010694024101c0b0a607600400103031400200510a801e044406000a5214542c47c04501c90200900c9003849401c006441c05980706005610448038158200c0305010300080e4040780c103000610004907200b00603c03074600e641c07400e80d01000c0c2c1c804c2070b0350003140700f2502240c6095031949060140c903018050168120354070003140320351031814442902c03510b41c3d80b001c0070304001d2010148000c000066000c00043c10081c101000031140c1c3c080560801d5008000540c0d045c4160100020a4000024240e041c1e95020b8042c2c43d68520b04805003502c0340c009407179180e00140c000c04403205038490101440c400d80d014072004c41e142c10540e00203411240051015010007030780c4401c1000c2c64540c034281c80c1c00c03180d080c07801e01e00d05003542d07440d009a0015004442025401d200030b201540380c81c01c80d1000040e0051314 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 190295269 1250 190294019 190294021
    0x509010b090f01030b130614011a0306030c060a030e060a0e0708071406090a031b050f04060503060c0f1207050405131e0b190e100b040e041401060302090703050906 72
    0xc2046812001100c4240c1031450b200b0040c80064104036000c1d402c080310b901521801da00715503460040c1c6100c40d04070662030300c064004000980c8400c189220503440b01d20f42a2440c28075101103502c1e1805007180c54010600001c00b00d0f123091203944140380c20700b562400d42d1984c2c1026102c80780500300c103403021209449810302c0801e05480220700b20048030080c0d0f03010504100d20b5000d0001c00c0e000b0001e441c1e8098580c00000001c580d64482c681041c00b000041404c88505101c1005000f418010300c85000318a048405d000d01d4070000341c51074200d00c40b100555265540001d4111080c85454207a4250840311424400c03040d40200c054820307030794212120007203845402d0264080b01c015034043c0d03110007040c1c0440f041c40c490a600c18521100d02900c400031a40e481c2c00f14460704940395000345007103040d00f41049601c0d001c4154040140544001d41460f061400355903ca0000340900064460b07a0079800156428a003540100001c40d80a45005811b1420601c040c3c0209002c9945c0700585c0241c2c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 190296519 1250 190295269 190295291
    0x10501050901030e19050102090915370e18030f0f1b030f0a030b030a0b04020603180d0507030215040201050a081e0703050403020d0908032b0207050703021e0d110402090405040501050901 82
    0x1112f00d0f4002c030304c05401146040395800c05480310703244a04441e043d0001100c1240003011440c507001c0050080308138800034a0410f03664001c09207003a03001d440441d400038840362003404080c07022501030080620720b10b6102c00180604048407981c0310161744061000090100e10280c0c4a005458011a151800c020100d10041415102c1401801c01000c89580600240c0140341200285412403980e40b29442d04c8a50240b50500d01207000f02ca1b140418004034084080550411503403a007490501e05010103401c1960000c0d125024804991040c440c4080003c4c3d0540b514980e0703e400c1c041c2400002c1e1032800c00c100d01900074101a83e00b5030050048042c010011802809000100c1e07141600442c43e1140c09443e010a1b1849020060340e98140034803600c00c42e2070b050010340186030041d4094900c203840d41c0304004821941c6401c610350b079822980000e240740d8800c1c42d12490b154004d0481c24074002c4100010340244980d050807a0310500d0f11050006124055001c1c510890340c40c0000c000314031000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 190297769 1250 190296519 190296541
    0xc07031209091802040207061407030e07050402070c050d0f06110306091e07030f0609091202070611030a03020a09080613060608120f16020d030305040b07030203010501050901030e190501020909 85
    0x220822070145000000f08000504056005111850060000180e000c14041840703c145e8001c0e24a200081c2c1c440b0105800c2142c00e102800080c4012070b0704500c0c0000c0d542c0d4207140542c052169500c40d840b40060401030103101000c0e0044c5c5a03100000308080800c0074030700c0109400540b40c45026000220010b54503035410030381c4001000d5003070002c0c00b940d65000b2085000d803101084820b40340e070b210f82d400140070302140108120244201d0680c0c69149140c1c070300901d0000181d00400c2007007a01c070400304280c0d4000c030441d00c2c2d0080d1850302503914080d0b44070681d034008403980024103e2288004110900b140104140700040c411358040c4455a507030742006a0380c1c14010310b00d000c1d03050304000400c000c0d50800d00810300d066180310f07008071400894000a40c4001248402cac0c0200e91240204010014103169003a44a41581421801d5504190000b8210700851a00c01c0c10715940b0301c0e2040d0503541c2080640b60301100c20303038041b40302d11562074400d01070b4200c80e036014052100f01000c41e0103030b880 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 190299019 1250 190297769 190297781
    0x303040b3106051f031104230c0a02011b030c0f030b030c0d0512070f0308060a0f0504050a0623010201060e0f16030f05040f0b0708070f140c0703120909 67
    0x3452400c0707a00011920388600410014203038001202841c0a1012000d4050344600c00440c0a901e001d200540351000740f10558029640d008074285c1121b0b801c40303801d54500e0710b1681080a4134140d54880c5035030042a0f00404802c2d081c0341da156025007140b0002d90741504070076500301c002d54803180507041c802c6007901901c10651042d58142c02030004000a0b0503ca105509440c0c0180107c54664440e10008805a0300149007900d92070002e44d80300e803d040e0000034146d049242641c50100091910310640801942c90051034851900d400100303561003000d4015070007400c04c6803105e0090b00c40c000c03466a25400c2c4d500202d409542011030006580942501007441010295000e08141d80c6111034400c44a2180319101d041c59969038400c509404580b06d0184a14441c03540c00702e18056500b4000f4801070f004005904209140e0f040080055002e00d20b48001d060900785a1071204c0f102c24003103064010080c400c00103204d003200020a110201800f40201c1e2560f071241c400d641d459101c1c0b0001d07151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 190300269 1250 190299019 190299091
    0x8070206191116150504051201050f0f01030507060503040212010c052101050616020d0609111f020a020108071709061b03010803070809130203090703020301050601020a0302061609080303040b 84
    0x541c02c404020200c0200002024404e0070300c2e2645c540380c1c071400080c10fa14940a041c042e00ea661b001009002c80f00c0348034003500001c0d0018040a2585140c0d2020341d04c102c0d601440040090120100b030031510b800c07100c0402000303808020300010100c100c0003405500901d015148214580c0085030000d440400ca40341070b02e40107801203203001010340a40c0140710b403490301240c0281e0001c01900104406105461b805031003110000b4921622008104440030780c84000300070119010389401030140c0004000c80405d9080c00d00c014503558000702501c5902d240c4042000028029041044034100414128801d240e4400b00306508000040001d43e45d00003400f59100d41d80c420403079000828a00c001038109910020131001900d04000700d1401a60000d403505146607000031010b02c114642805041d90000302840144520f0540d901c00a68482000c1c2c0514041564400da0100c4e0b41d1081e00c01c41e01926400085950341d050a14207031400b20b03001c40b0b00040380c0030300306c03840d41c0b0762803210102c40c1c200c0c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 190301519 1250 190300269 190300303
    0x270f011b0320010b040f020301060804020f03120d150807210501060909030c050124030b060a05090c041a12010315090210030b090a05160804080702061911 68
    0x20000c9805106104080d080d000e111000040e4a0400c4541c0940c000202e40e1100224810784180700b4401a81d4000c2c140c003207028018001070003070036032250390158441d0b0116504c038440350002000c00e003007103200311410b4100b0a000941c032003070031074030f030001142415101d070f40e40c40c3d86941c0d00b91507889070058000c02c01e0b14103c50b0300480300240b5400d490f103000e901400001484682e240d0610781168220801140811288049141401070130310a1014541042102113400904100e2441c51000349010060040c8110400300708a51505075502c0080c00c07001e0710022440c140940c8418480e0418460079461400d0007030541840c1c03c03d6001c9c1c884110003881c04648503402d559036041091000c0d202e01ca0407994940006003d640c5d46440c240d00c241107901d00103180407030070051041e800c00061420401504000c1404488286006940e1080c00d00380f501c2d41880e19a441c2415a6100e4440040d502070008500704031100c940700d42003002d1241540b02c1918007082074a0762519000024040c0f2000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 190302769 1250 190301519 190301537
    0x71e210e011a1f201e0607090e070c03020a080406090e0a0e0c0405060d020a09020a03060b03130209041502030a0b0109080d02060a0b01050d050f071808030a050a0e0402270f01 77
    0x20f0702940c0446450248100700c4c41c1804c101484952802c05401c920207107142440d01501035102d420701155800038524604207a03140d007046103060341c90310044c1c00c01003080754004580c020b06209000b0a28403550181c0c04a0740da542e100001000c1005a0191800c02640040450000445031007030485140412002e4082d41c9160300410008110007803000c4d801c1741c0c0709014600140d592017075100203030a030701c14010b0715490000001400c0b59101d40005c07603084001c00511074040c0106184004490b4100d0342e1b004540e881e46071075222441d039016040190350001c0107000c5a0405038000c0c42d10741c20280c1e603480915507502c030b42e95922802121004090b81050001c100c22640c180c06c520340381001810300915003080742e142c50041f1102100e020014030442024442610742c40384541507400010390250000500300034807a601d0784100c0b40210140500040c3d440c480c0c501072489800e02201c010411522000611580314250308840103c04c0054107180c200d4070186480700d10303550141c0040e582e40d484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 190304019 1250 190302769 190302829
    0x305190302121606021c0507110706020c15031506030108010c020d051612270e09060105060a030b0d020a09090512040f0e0402030c1c0b071e210e011a 66
    0xb5409a2010500c06c001c900b400b084400b0240183c901501c0c251f5140e20001503c4083c107820045543c00410031034000e20042d9015560300f4024400114007500e8030399513038461600b02c00c80c46114502c06a0081c0303000c0000110880d06601090010321b041d0207848003d240c01d50220344910400c1c032110307a0345012000c00404943c001140c9541c81c1c1040c03c1c0350000b041c6601406d032803a0008006980148a103c03002e00c20887c45498030f58000861900900744d5504100c0051403d01a1080ca42e040607550004d940095840000c04010180c002d04602c0f0241e8641412201030064504241d92501c5540000c3d081c1c42d450314103d8080703c0360b240803844604d00b855200c020103000640144e0780342c800c0141100055903100b00c1c85010745200c2019032000a050300c2c086008480007000d807400d0240d00900002242c10003004450000b603140741516825801500b0380b60082004144080500e1801c540004c406205600c1406001d116041c1504131000e081c0070080f50422000c8850240707200c101400031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 190305269 1250 190304019 190304021
    0x191e08070b0a0513270e0106030308060904061e02180f0f040b060f03010b12070305070903020418170a0306050a05030d0c020114160314030f0115090305190302121606 73
    0x14400c0c091194041d540b59036410a540c600b00c540c0e05c07107524503000c01124011540c00d02c610000c0705545170080c0209803030f54501504841000740701d5809855200001400c10a00d50301c1b050201001d0007044c4070038020500d00c04001c5d0408000c0341c6141c0c6c03080c0e103181d809103440c6042460314100103001c903064503201c0c01440302801c00c501c070032508024240030103440c40b07414801860191800c05441c2c0c1d103a90708060800d00301c50025000c0d0b01850300d80000d11084a034407411840c20380e074055030003040111044040d4140c0d07070040b070000780030003800701e501c8480b00341034030300074a5450b40035a0140710180e103910800801035031902c5510303071551000c0c902e44070b400d00414512a04bd8014104400c1811011442040304d80c4000c0052660541d00c0108000305a0450f503840c403140383c1b1042c11070443c036101e5810011100f042c0981408221010201200107100d50101030103140e00609561b0105001c0c61490881c00b41031404401600903c40c0d8054403054031401e56800c3c1c142e92500c100f9003001c07034039800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 190306519 1250 190305269 190305277
    0x10c0506041403040f080f010615090b09010c0501091101020615010909181a040204060603111e0c0304090605090c030702062410020d140f090906191e08070b0a05 71
    0x7510b40c0014840050104860041c90000346000c2d000f61048000d0b01040d1030868019800140641c051445246411940310040d03209071400102c0859032100c1c0c80c00142e0b54404082c034010115800d00400104108900c1520a0b01c0360081e0200e40e500e4071350f465030645d001200350b54a0300044d0314203000c001d0f8920740e4208041464070003941e08642602d035100c40d2108e1400d0400d66038040600c0742444214103003445004010f000e20324080003071408044205c4030700c1c4260030f20442810030084050405c800c4032800c6900d0b6440190449aa035a600d02e2031002a01c4940705080c4103000710800100d48000f03803402c4030b04c2001194043d007034603a00d8081c003915000d110300c103460070b031200c01c01d50080d503855840c901001011300ea0018090246154002000e01e8841d0103c10302c008001e10001c81880203841c2aa010402d00316203108655942c0070111381540303000c4141038003040c142c142c00100c181003000d544541c00700c80c020011045868044659490f1001d2090704840b481c10000882c001e84a04054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 190307769 1250 190306519 190306553
    0x609061003020d0b181024081f1d010b0c070501140d290d170901030b0619140304030c0305033303010f140a05100e0403050a0e010c050604 61
    0x10304032001402180712400484032510220400c2c5c81446540c0c1c41c001c2c00d9200901e00c5420340842e030100440c3d85820940092001c0d4103010102c00480c481100d0760720702c00c03002c003004d0300c08404d0641d07078569211318690b0204145000060311800030030580200b2041b00c02803803c481c010080e507854040115411000d040c105110300c101841018050f8074036024010307110402820303001814201001003202145007410aa109422000700c890000c0c03000d03003281c00f00e0345140010b603898030b41d41c03801a8042c0c44102100e81e4011030001d22401d01420880f481001065990350f008001000e0300384052081c0310948005e0049196000c0d500d0001e071140b0010f541c03040c1c103186145101c210860300b5008070219890030704541124540902c0300c5003400d1064403900e407180502404980078014180e54000000740080f410301c0e0715a80010580700e0078041c010000d01e0280301d11803e9203400c0c20010f00507003040080000041d03442c54010195031182c503280102e242c2100c094141603d86546880c180000340c105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 190309019 1250 190307769 190307771
    0x606140405101b0308100e0403120c0c020303040e0108072c060609040218130c120e030c03040b070317010803030f0405011d0a0b0109050108030315010c0204050c120609061003020d 79
    0xc3c0d603884682d0400039507460b502c41d440e55120341c108901c3d80e010304256a0014aa071581010030000804c1d031003a031400600102580004008070903800c11500401100000ba41600c80000c00250045480118034102c3e00008241e4082c642c640110b0208002c8a40b5509400300807080a5940c4583c103800c80c03a00000b00412130340c5080d00980120381030344c0001154100c6140301ba0031403a411f003440d520f070a80154040c40c007044020710720007014014200d0300002d040c1d060303075549003001c401c10100101c0c1c1c02c0c1102c01c0102ca840f070703642d0700d21031a15902640040700001c03480107041c00e03808a080b0050341030352001c3e0041c43c02e641d1860b132003200e907030360042080d28190f4903810000d092580c3c0600d00d2000300310083c054442004203041011003a001030b4441c88025140c240100000e080100070b807504205002c81d03400d442c0e05140700403a000800c401d030283d0300a2400051115400b0b02100410040b9001c20026030300b59114020085480b20842d0f1040d0407808001e602c88000c3d01c203500810191802c4030b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 190310269 1250 190309019 190309037
    0x7020703020d210e030a06180206030c0301080f0a02010503041e120314090a0201020a0f0510060b090f040c12021b060108010c021c0c080c0c0301110d060614040510 72
    0x21080c01c40300005541d0201c030101c4407400f090100f01c46010025041c1080a2442440070101c1c3d900c8146802c0500541d5a4a900b860021003041303a000005400510307003522410100440749260b802845004035500c02c50949400d86034001c07800c03d00e12601619110f04690704c51b141c1c0f00407085080d0700040b0b45032007a403000b00084c45441682c020090f4580d00020802e041c03421207080800060303c40745069105c2c64020780143e900103800342980e5801222811059840d00e4410720709010340a03600380d41c50404d0340c0443c804140e0805021710810450300c080394240c1c40403d20080703c10322382c05940005c411400300034414600750010109030721174102c290000c3d20040d010358107101003030304603060341e9450b0310106141d40e90401440642811040b0250004058808042c0903000a05e07401030581c84003007255030b22500188030882c0012005802030001038036181200d0f503107500071144498024035044000c25054030814645551031995040701e80381609140c2040142800c0561380c0e010000300c84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 190311519 1250 190310269 190310273
    0x9060e1908040b1819150e0d29090d0f0807090b0c0307060609050109050903030106020c010c0206040806070c03110f0705040209030c10081021021212070c0e0c0403051507020703 78
    0x28000400d00c0700030600080c00e17a090080120007504540745600420201c41f26031a400d80e9040c0044a00c1e0313901044428120403403a281c162600400d9110710545031400781001032072500828198140b9140380d0b21909881030b0140144d036210015514440000c800301c1082c003024058030005d00c10384440303900b22800e01010390344003010703101c00c0d40002e100b00303458000410400103c1e00665421201f284090b604540c18024020360380c00d1012600390401c04110001402d545544003200c004d010000c040c0d803502c2c0707810f02000e414a03510203400c030000745c0c4040a582c0c10020100b11034442110200c05030083c1460541000085d40240301300580c54068041c8440c402c2c2d8803080c43d0b181c155030503151b104403841c02110301803050b051030f4000b0384c561030303e44c000c806c050303150a442e6003889504850219a078036907980c9607480c10024910181d1455000502e48050243c070100c240c0c1110040c0782500c800d940d41458141d494066844010455409030504503100d010703d0303113030951080803841203481c1580c2c2c903 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 190312769 1250 190311519 190311529
    0x1e081504020a1e050a0203070f1a090a0201020c040605010e0d05011b0206010306060e06010507060e0c0901272c0f010c0306030605090705091303020a020409060e1908040b18 76
    0x4030392101c0c049141c0e8040f0b10100320201543c1016202907041060900e0803101c4081d40702e200303071400100300c10506150318041180b0035500c1440301d41c5001c1008040d00e880816140c0c1d0709044581a0702601c03c1d03000d003641a16150080c0360035284182c0d69100140071340c0043c0854000f08000c00c907065501c850300307a2801d99070000c13a41c0c581004c0d0340c01840300f54074508214040f03800f0b0350010800d000e5400708214035a6049800c07987c051381d1050b000500300014540c03040c200300300a4482940201d0f040000200f811035002d941c84040d00e01d04298500c48031144190040b00e4010030304a04181c81c2d4115803c0098901c444040e071b000380001a43c0d10f4189100e4010708446600c90039502003070f510310b420301c00c4c441303180701e4640c0c0100c1240080c0302c001d08104c00100340c8840102004060040700480c8020180f003446211402d990241062000c03030307460310340080940152032510f0114892020b03400c1c4400e01d2641d1400901d0742281d4603910b4103080040d419002d5002503451559814407060381501c0b601c031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 190314019 1250 190312769 190312777
    0x525140d09111002060c03010b090d12030203060f0409020a140a0e010605030109050a0c080105100903060f0207050d0f05030c030a1113030507050a0f050909150a02030a0501061e08150402 82
    0xb094030646103940410301046582c0c48019101d10440d40108100215904060103d034159504020010b8980042d07070005007842c0c141d03d800a00c0c42410304400c00c0301daa090f40145005280172500c07001544030b0f240600003114148072020b948681ca41d24100452402d400e202e400c2150082c0200c0740c00354071185400c0070340c3c0007a40310400013500040100006850341c4a81c0d60001d8950506001003628400020b02d01101802450702c21502a961030f81050b01410900d4010340d4041c80604c05018034511020094000b09025180350203064000a2418882e001900c1c1882c159200c0784e045860b602150740d45034000400480511303540d400b00403000034298001e407414481511280e0030305030039880c10504000e50355100030b004040c51402030100070541c045440c1540d00c15a036030300e0142c0d200c0b00341c0b51030004441c0344510b141c81000d003400641001d41e00114812120000184141e03640c4190442c3c1002c41c0e54114145241c011100c4407017603129150b4550050501110604049030000c0018103d1348 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 190315269 1250 190314019 190314023
    0x105041203120b060304050c010e0301020c0f100b090603070905090a021e01030b03061905250c0c12030c110a0b13030309050f0d1202010912120525140d09 68
    0x5a0003041056001090058411800f829030f6140c0c11030400350303505c40d41c400750050280d040c81a426400141900c0960641d10803070701036400c8401c2000002d8071581c4135151805090102d60400035861803030304289105a00a95001c1d0040c0b003214681035a05004240c042c10100b0310b030003030003161800360fa6165210f605008520b0741c2c416001c0030010004d070403603200c00d011f107000e600504104025420124a540014604c030301020403566031711440d099100d007078190042c4411030344125181d003490b4006240702e210b910405460fc0320544a00400910010413400103000400c40c3c040d8000165001c8082080100d0141100403416151120b2044941140c49070100b00180207100300300b4507520096100c01840b0603114802d50141c00f8000c141c00403a64800603041c84100303a88607801901c00d41c48070a0083d004a0700b0310200d40d50322401080c0140800451841d1410003011503840d4803009a07100360b06010030000c4041a212001c151481032074001d908503141c2c0240190010081a0b00581d4803842c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 190316519 1250 190315269 190315277
    0x60605030307030909051005090112030c050105160f1103030412030b0307060809010b040203090c040e0a0b0106020d080106030c021b010309021201201201051507060e100c021b0f0105041203 83
    0x60309103005c050403180c0c000c0c5a00240390803003c0401468941c04000c90560f0340b00c01002c10749031842d007419201450482c0d002006c541c602010010b0302c607130914036140d007050141c2c0c855503008445a821545204891404040c0e90400c01c08200003440c003140401c41d5000b00e040200d48454468006410401c01e680020081140503040008514080c0700360055031104440440c11814108030480e034034099203180c0d40c01a40d43d145503290400e03040103410f102590103003071000d85684a250094071840400079281c0071030600400031400d02c2c0280219009072105600401c90420b010854201c0d40c00c1c4080841e05040d03640c4040c5001d61500341c9881c400120b0100003154041003144d1490320301c4150ba80c860120441030024171131000e0708000541c1102c200f251505080e10b10b540007452a88551400100b849241251490858002040f24807082000800801599901a109a031920780240b15000465034948482100340703041c0c0071500c200745040c902142002d4031941ca40c0d401a09118042d0085 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 190317769 1250 190316519 190316537
    0x20d21140106020f07030312020d02041a1c1a01080709050a09060302100305011206200711010306150f05131a07150902060a0f030b1306140904170706060503030703 72
    0x501d40401c0001500c00e0184d00410010345142c500030840861102610100760700000e840c00182002d070169001f515000660007005151f015284e1020740c021130350304600307000b00030400040b00043d1148000076183c101c04266261010001142c01c144020310f1141400301560012030240c4030301c002840501003c0c140054850300714010446c1c2109091003881c00c050030080140a000746468448212591210b00800c01015481084400384114584031910050108045003402100d095034070313a0100a032070810509446d800b0141e007280c1d11500060209240302541c01c1010700c200300400c0351076400c0e501c02c00419180c0c5018030000e0f1801c1c0041c40a44008103003042807001800c0d241128020011007013081c41c010f40d01080c424028010400280a41c030013442c50302d6402034200d02e9850b00c009200700c1c40f1036171400341da10040c0380c0c6000e1041755074150400740e006410640d24803400b13242c020690b210034121808980c4541e511100003100d40e44e8840c000002c0c580c07800c0000d801030a100b07448242c80 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 190319019 1250 190317769 190317779
    0x402040f0315241d061f05070204090b0103020f030705060901050904270314090102070e0604240f080c030a020907050c0304060815030a21050f04090f05060102030a020d211401 77
    0x792522181c50311200d0416405100d001c0d1b0702c807800c0e050a000d4404445d003000342c40c41000e1395139016582010f900107041a00700810814201007040c16039100300e039800c0250759100180740da10b0620b4020590408001c00c00607602398014409451405402000490b82185201055401c018a030303036900c0b001004d0b94502070406401c0b180188800d582c03520b0a83c02c11000c400000e41d0f078074151086089800c4a400070a46035141d680203a20f00c2c2c1e407200d081c21200c001c4611001d401031090311075200104c03211030b000b0603102404a002d2610b00c1c0001c5c0240309000d42c90302080b4181c1c0000e8150703028000704100e403840700c2c402800a04002d10a5894000091511520105516a591800340d1203038101d00740400000e40e01c5062300ca10030301030700560f08019841c140141c901d8410b000800d664034201040014240100350001030143d2104002449681c843c0801079030340c0d009148c400030160704641c0c9440c14051241c40314418140384a4880c0c00c2d12408190010116034a81c038040c072090b940d00005100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 190320269 1250 190319019 190319039
    0x10207020a1d0103020105070303021209100608030f0711010c02150c012706050a06050604030507090f0204080d0c15050708090f071a0d020708270402040f031524 71
    0x1802e5039021040c0006100c642d00300c1182050000034148034002c90035030203161103136042d504204900124030902e030030182c4080c0e03696940c1c3c4221401480c20000b010401c0795011050311041d05071040078500300170b11a079484507400c0308070301d0f240e0403c45620028805603450080000030111300d50030746c40c0e90310380c006915401d5505840c220b018603110303007010f240384010140703450300c05580001c000039550301d4400c0344034080d00055000c2e5620100104000c4148880425002e0441354034000c100500003110705102d00b6801188a50b4003250000d00b1459509401016031074040d6200c1d81c181c0c10061152130038032084402c15201c0b1000100e0b031108029460b0000c00490510406120040078414980307803080000580052101205a8000c144014881116010340d2000d41d8410703a0b030754072250300ba50b040403554003210380949059108480b8010718101442280c050310742c03001c0749c0e03481c007421500d80c1c0c40782011160040802996407185150348524180014100600c00c10540e980c00e1329000c0205 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 190321519 1250 190320269 190320289
    0x70c0905010e06012c06031810060f0e0406020706060909120309051e0705040c02010507140708040b180405070201020c0d050c06071808030a031b020a1a0903090d0501020702 76
    0x910380c0031802d000e001060703030030092045001043c2d0716419420291001400300a82c148820240c00c204017005100300220355041841681c511881299030320900b21003400161035240c804d03c000c124400500740040c010b074041c1e081d441402900003520b00586075403044120740392030340a0b46405daa19a071310703010404000c08003968a0700340d1609101040c038917142e80c0d4940f10090880c40b1000f400500400c00c407842030055500402c001002007115a02c02a4040e0181c041203428500103101c0c0c000c0130451600003000e5840c02504410824205030038400800b0b82644407085401840814001c507510680d9240142841038005600240e2a007920006080c03404441c80d0140c002d110341480711078508840051910b0b03100c951072510f09108080d5490400311000150040300c11030200046440205030103030003000b88591441d038190aa04880b80040380c03910004040100f40000317a6014040c050b800369091074020f80b0120a8034513010382140002c10644a1290845069401160180c1945409a420 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 190322769 1250 190321519 190321529
    0x70c1e06031a0114090f030102031303020106060804030801031101030603050115080d0507051b0d02030f071401051c091e0c0f05040e0a0b19050424060612020711030102070c090501 79
    0x115440049180028001550501c0413000e40003011414020654414618200d04000a4001c40d03403414001103141e188112940d003907000d90b0070120f000403801d1250b2190361050790941e0301e5031120307401c542ea1600310745000510641050340310100400402c00070f10450161980008040c2c030260315100303421b07040200c031403820000e0100c180a001b0100c1c80c0403500c1c400c0da12070360820141000a640c00603800111251001c1d4042c840c10280c50b01e1110009030322426600c04002400844451500440b01d0380320305003100d800000c00c11480e00202c0041c0c1c200c8050300c0c2c4144010600307040360034510711074400c002d031050b54a1601314100300402003004a440700904800d0702c0c14807450094080d819600e18080c0c07801041d000c070f17503000102c101e0850401e080079448400340c240403e08042c10070800b440d00324048180341001c0380306940800781e1944204011a107241e08c07120322003000e80c0211002500400c5090303440da040a603550b419543c0038401058801d114843c4151064240b800d46421600140c02c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 190324019 1250 190322769 190322801
    0x5120a050a090804080a2a1e0b0c06041a1501030b150f040501110109080913060f0e1e06030714131d0d0503010302060306090a090c0b0c010c020a0209070302070c1e0603 74
    0x1d100087e00442c1500f0042c1d4a04014a519145640140f020203038110343c80320002500101d1450031000020515600541c0511440029009c40c0300310301a000da41650009041e00740801500e41e04d5009400c200309040f0010144000001d00c1107080089900148031405080c8000a0501066800101d5814030b81034110082201d019684c1d551042449002038492041e000b00840b0394405c02150003000c05003484045031007515540d119240c0c0050826a0b64400302c03695025040c02e161440344542d4424000100207064007441c0a43d0700780c0001d124218241c00c2244004078000c00c4105006201e03101c411104c03040c0d0030b01c8201c0380281c01c246200b8a2901004010001040580c7e5544103680e0003201c2128030403030750b841c0d001c0b0380e00060002d05001002c030145040001781d4402c2e040e02601018106500900182404a0040340c0700c80800c000254004a501c1c00300304460311075400b5240e114440c501040410343c50341c407415800c945140c8a075030381d105951028083c1c0e6525024606140c00b40c0e020f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 190325269 1250 190324019 190324073
    0x521090f0a020d0b09070b0c0a020103051f05100314090a02010806031c030209011b060506090109060b0d022d09040f020405010c17090a0b0d060605120a050a090804080a 74
    0x30000c0c400f80c410000160400c060400451031401c0184001d000526a84551680d110b0440c411503458441008099005c00e1820001642102c000500446200291141040c80c1c070300b40f4042181e0400c0b009403180405940c0c14852f03443c0c050025034a8000c0c41202e0003020b1940941c070004009400003026907000340c004844c400300410307800980e94a0442c0c5400c001da01c4180000040380c0509241c80e150842800c410034043c18050700c2e5011a00811098071130080c40e82c0c81c0c03503d20302910f0cc20b02c00c0c81a030081c00c12803010f24480c42d50150400214014505220145840c40b44400072405c04e10641d6000e0005680b441e9498988035482040e101d0710025420070746490000381500015003c0070b8104940501c0005086110341d0403210000c000401c0c0f403452030b498501441c03843d08104080300000d807a0030008030341c040c060030503035240540410301c0c143d45907a0207040c0000790002034810b203042615860528006081d141c01390024014400003428503800038141640940700710400e0001682200e0707 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 190326519 1250 190325269 190325273
    0x1c020717060a1a090708130f08090f0103021e45030106050d120c0602030a09050709050108031614030316120b060a03090c0e040c05030f031305040c0521090f0a 70
    0x4c4400da5000005040503441982c0311040d182030380b22985401462000c3c4160820200099403002e411030450135a078074203102424038010360491041707260003144056806000301040d100c1c50010800284600c0410752000660207a4050140ba83c6000c3c4040c1490543c00fa1202d40d4203071401e012504046000b4001d2074a020003107540490085009404c41c100050503c2c441030040c81e101701115444141156070346004032440d002844055000c81d62801602c100048130003d901402e4140c590107400303140380c00d040382d001e05000b503031600045991040003403450001c1c550500c0a1807054168144e1a203040c10340f0800104000300240d03c04ac10b49150108080c13447c2c83d0801912010a00707420000f5002c4600d0400a10484295015442948a500c204810041100010300c100c0b02d0950845521150000909841c1d0283c04c0d8140366100c0f040b503041080c0d01c0e05030411a540301280c2442c0785009412280040d9516244901c02c0c0030024000030721100b10703020081043d10080c590050444c643c030603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 190327769 1250 190326519 190326529
    0xc0504290901110109140705030f0a0803070507031b0b0604060909030e0105090102190c051206010b0913111605060112150b04110a0801091d1c020717060a1a 69
    0x10140709040100503500d584082000750f1211103002c0e0004c00d022041000c1e1200c8903a41c151600415000e400341a00301c0d4032060000031805500c0d40e20010b080d04550302c5140031900c54104400540400c1b02c2c41100a10810b24082c0f8084402d00460034104646030034028002a10300315881100d5092401800001207640100801c040340002d1070001c0d580e8207881d00403032800e0190009005005034483c440000c10000d481e0100407a9404d44480b40104d60307081e0030b0390300c554091003606002e407010019400c040c50244001c03143c815654000160202120009035038903000080141990120843e11400340b00d003c01030540181118004000d070092580d43d03000000e00b40b0010788010f41d4640090b20b00310741e2a85c1240c08483c0341628800d803105150b02004003040800e10500030710b03520f4001c200700c0c1550265521a685c4145000400c2d4410005000200242524072004214010740102083c081c1082c0034200000e08504014541c40c1451007000b8110382940c0c1512182003014800317500d05480d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 190329019 1250 190327769 190327777
    0x110304140613090c1b1e030e100e030c040204060f05030a060b0406020604111e060f070210200c090105010815031c0908010204060e0d0f0f0b090f0f031804020405040c050429 76
    0x42242921000c0e8031f0f064a1021101040c2c03175000021000c40854640e2100d04441001c034120119001c0b0101c000501c0200e20850040390000b444030480c28045d00c0c0034000842d00180000c0313000550716920a0300004c142c0060b001500140c00c58800e00c028400062050006448101c8801c4028411181300304888000246610702603000400c0e400c02101c040010f6a0f0980d40191000365141901c201c01052102d1041c14076580c85a0180110030003600042c09490000c07003d0a02001c507403d100042d02e075494001c003408255520b407400c103001614140500215081164682e2090b010350a030082e0001017a9044044280c2c410301041000036403180301c0120341082a580d20031030910b41c1c2040c0c50b00389203250004d400160000040000c1003020701600c0d01c42c801c980c0030341719010000e052998171015644020441513000740301003c404400c0004d12140028028801490141e41d41c000c1750944514414440200380c1c0420100103005016040f03041d6034a11103c0c030740000000c803c2c040b42c02d0103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 190330269 1250 190329019 190329053
    0xb07110f0708070909030221120108010209010c060203040519111011030a0309020a030602042705060306150307050d15500a0608010606110304140613090c1b 69
    0xc5c0311030514042c14000d000130560703020240c041d4101c0f40d0881c2d04144243d4031200000c80c0c0d9052449c00000c0190042c400d440c07602c1c80594034448503c4254940c0c2019401c0074206072464091f9401e03a601c146031000c840c072102c521a11031b0b214158880c01c10403038084040001001071040d1039100c1c0c0210b140210840d24035555908001a201c500c031b0000c2204502035801c001e001c58800100070034503d010180f442443c0e1014040c83c651102c0b94480d11040d15000c1d155a42c01d90710107400b01d854514180e000039006007018040390700704e503a5070000400c0c031591000240c8007028841142088251103001d00400e00100ca03022030400982081c0b2681550b14035900d00c01701c02810003036641c10406800003880c8928100441c0541420204003520003000c440c8101b498542c40c15000080d114040d2191076440b8500d14055414507140004c0c0000c0d51414201c0c03e5880002041048545600303034500c0c0d00500003504000511583d00d48002e001303c1d81da50000d07101c03003d81e60201d500041d5610308a0310025 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 190331519 1250 190330269 190330271
    0x1020a02060f0a092406060302090f0f13091103150c03040303020f0d0903110606100e09041401020705031308031e13030203010e010906060e0f04020d08070b07110f07080709 76
    0x294480304410300030700e0700d51300003040c05a1007100b5408000c1160442010350540f100200300c500c5e42d0b408154128815006401e8024009048a9001d8a4044804d003030034000a03226880c45030000440c01e04540b14440211100d1404a4050103141400c00000d083c103030f012501823495040000f016800381c00024002010584c000515903921174002064801c52043d61506114841c1c030752078042c201c08079090703140c545481032030000381e1685001e80450014101035168401440314000a218824074002c10070b45a1076280441000c0039482403009002c4d42c0e0040002e192030f070400048038071444516a004500681c0144288054594000b01c2030188103003503482e5541e1180b26500c4004013248560002e0b42c15442c111800301c2c0c954040d0003040d42c082c443c0c4810000700703071542c81d041c0080350160340a911020140c0005401810004040c110550280c0e12550a01210b603813001020f10084414100080308440c05005103c800c00051703003141400000b0306a03c908091145a44408510610000c030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 190332769 1250 190331519 190331521
    0xc040e07020319080403020d1403060f0d0507030f12030204180c1e0503070e01020303130308130b0103080a090504091a070c0203011b09050d20131404031101020a02060f 74
    0x2802042200d062481c0b03020f00482c84001c030100942080ca08507030542c054080d001810060f14492940c585585018207021411034444c402404030b240d580400c0241c005204122441c08980104160402181300d9401d6000113a403074a80359800760a01101c1e503080c14010310060100500d0082d04031010400d9400018141c5500d600841d40e004008c0c1854044c00c0140c200c60041c9907101e001148244084d4440c0e8541882c250300490780d80c841103810544449081c3c40043c0001c1c420740d040358200301141f901ca03070400c8407a102c4004400003a8411602000002002c0e8010364002e17142c440180000c860030060318003651681d076441526140c04012607070202002441e16402002403590841d00030b070007040121914440c0c0c60034506050050008a4200c1100003680c2c6010320250790b81075481001c1a9480303000c000740810080c42c4903c07403a4040d000314150340c000c801d20b104120610030741085d2800142410700f4082e022203078a4034240312a034010071514501c2c640016031580c00070a900c01d41105 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 190334019 1250 190332769 190332781
    0x4060504060b040203070e31020f0c0303130303050c030f061021060509060616170405040e010f06060305091506040b0301180308010b1206040903030e060c070606050301050c040e 78
    0x4154903402d89920602c003006021219130b004819402800303042d101c070300224010545c1c010300301901c6200c0d04a01c0c22940d035450402d81464025010310b0401400752170412040c00c2c5c00c1070a40c0c200300c401061100341c00045c0c80074564140200e42d00203441c02401071540c14912030700e1802c1200184000d0040341c0141005907180e02c42d00005a042440f44c13101c43c842104006800302616440c402c041c03044140c0000b203000c500d002d1007180d4000c040c240f5541c52000b00c1d0b948911a0510580a018094005000000b0b981d2100d002e0224201060000000e2140d1945910022108150000c034105442c0504102d00e80e81e00061029120110140030031503a90340200040240920184150309942803180c0b9a070700c00c541c1100380710028405c1c0c961044684e04c5020b0242d25004410300a00d580b0340b401c0102d04681842d0384400741950082c500400c0c0e07d905800003500c0c11b14241d800485140c0e0008041090102a10900010b444203c00030300290030280c0700c080d00c1c2c0c00b44d40074050084103940d001c184 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 190335269 1250 190334019 190334021
    0x18050105010905070f112a03011a0634060e190302070902090406031703012301120903020a0210020f010b180f0c160b06120102070203120c07180e0705010906080406050406 75
    0x48900b0841c47e5407003410f0f0f2040425112003020500c0710700130760078010b00c0c907100540f4800404207510041c16440c1445c012441031006080300d00000384c54882c184051a200c20303c001c441c03082e818096000481c0100700f40101078a045070300c80320151210a01028100060342c04142da5040311031260f000341e260348a00f000100200080c1e48006c4c481002e00258004054103000903504950041c041110b00d00d8141c4403001159203815a9a400541704c3ca00a0014441c15406852481e000b031046076110410355010600e8250740f40445030160380b182203511704c641c10901070b5081d54a07090302d81081c01001035040c0c58400c140541000c138000c1c00030002602c041240d005507070f0102901c90b00d0034004c0c1d11031309000f0810041130390900d0158002c0c0c6100c00c3e41820500880b0b02031603020340100307045142942e05038000d4001e14000d042c503029450340085c8149038065091940400d40200041303102d000300c1400d00d0003500c5e5000c5da044c000b03445020426150082e403e2a80141c011502142d95983c03032901030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 190336519 1250 190335269 190335283
    0x9050d030e070e130b01060206071704030c120801030b0c120103060e0102160c09110304020f10270f080601060807080402010e0907020307031101110405010c0203010e0118050105010905070f11 84
    0x1940458003d0410800a1060461a14582c0100e14204242e40c82d900201c1c0c546030110303840804241481d2200b81e032044120350040c0d00038064030700f91980d12103036a65034004040d9000490b0020ba44e2200500502092144042d0456211003625145ca400c10015190460051101030b281c00d0b030780c1c6002c500d2604290112011300802a61801061489180a0f080340c0b505009503041d46284c0034820000300c4010003103c1c0a1a002030040d00410401400c00c100e0a02c4182c0d014100142c07202c80c00e0002c401c82c0200e0003446036024000d14282c0c1088090f440100159002ca242ca40c0404010440300741c00940c41034000d0300c9442d100c070761603440f800140c0304051042a942e800030740680810000c07a0380440036120341031080e034400442a1949072110f007a2041090701405005080004200d035600503610322803018409800410903401c2c400909017150250b050032010515200001b9040081c00c2c468540500003c100c1002941400803008003143d442860b100203200c902c54440301500001c000032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 190337769 1250 190336519 190336529
    0x30d0c11030a031d030303130f11040609060314061e100b03010311090709300b0a0209090928020613060201201809180f01050402010801080109050d030e07 68
    0x100c000b40c01901c0d00a2542061600c05603409400148050407031030040200d9014015400d907110780a18584c42e0401441c20201c4c044805043d03000e01200980c6840c02524001d05201c40c0004200349107051038811501070790304460181d0848020401c055164002400c840c0901c4400480d20799500c04103208403082a80101003c8140480000100100309100800c044002d4807001001e8507141c8007600d003d2054020809864005103d00e60f980c2c142030544e03027003486161554610310555895040e041da0056411000c000c0c1c0000728406981000108a50044040340c0180070207000d07002c0d0003120304c03420b04588849140c450301300f00641d80e414082d10b1075810504102c120159403038030042c1c001c2030444102502c025201034854800e10305403040d00c54401c0340c44400011111840d04000c00d6940041c10054010054501446101d50030481c000050b64442d000040e2420325000242c800d0310140e120150b82c0e03040800c0c410028401045080300180706003000b0800c10240505039041440640103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 190339019 1250 190337769 190337773
    0x4121101090b181627061205010b120601290a030902010f0504060509130e07080a020f0d020102100f060503011a0a1e170a02060f091806030d0c1103 65
    0x214400b4010050040c5010b403680c81c0d440340408003401c0226446240c0d00c40c0e40c21480c0329001d0200403010208070381c510f00da1019440442100030006404003182d00756003107034201200c1c408190040001c2480341c02d0541804880070540410030490160b51003405005107030207240705c004100072030400100d5020110000b28080d40d1504140c0303400800914040e002a40040c1e943c0c110b1440003401007085900b0780c2c5060341d0b540e01c0c0603140402d00040a1035010081007e40c0c1c3c4500e1241454028054903020300b2101018100c007541c40e004010704070680c60344040c8158a03030b42c1480d00603a00043c2c0c0f0343d80007803081d90204000c00c0c9140c021000307140c241d00054240d402c1c40d8190f001c2116030346200141000440f03a14030358030303210105000b0703401407010030240e2014000c0003800100c07604400d07034140721694011500002c0082e408140d6980008540c003100020118480b402480c0041283c2c1500800310125490b500d000c1300000d0b5980425a030110900101d11101c90034803240b03440d40b0f50010b4024003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 190340269 1250 190339019 190339031
    0x30d0902031005160905010e0a060804260406090f0b04030605100e01151706010804151118010e0916140c011109090106080907050103020a0e03010903020c010212030f04121101 77
    0xc13003403000721900c0e11100000341d01d01c81c012030030f036001d8a052020036034003410920000f800c0a4094400640103030003a1a03070185000410310b0220b0803240428a1002c580e4003d4445203448009000c401c0950460250054030a1042c0505c800031402d450032070780c0220b40412580c580700c03003000200301c143d04040c00c0101d042001041e030001a4a161804149903590f0104403460307070150500745001605c03101e00080c100d1000c0f4000c134a0390700350706000260b0f01c1c90008940c41501d80c0510142d000074031355000c00303201011045c480d60b00301c0103940102030140c901012a01e013075459002e10004c1d1902800620410540710309400e6500d9040d10078408010000b01310026070204000112b030403090708581300305d00500003c2841841142101e0150150800810646003850b0045d0041e4111032041d1041212010340103007195001d0040b50718031402a0080c281d84c000c0b075000241000380d445d0300d102091a0030401c1c4504102c40811040d4401d0704916070300004030a46c3c03000c680c10100c00d407401c015982486c2e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 190341519 1250 190340269 190340281
    0x352a070803090a120506070507140106060804031b03020c04020f0c03030103060207060b03070614210f0f0109110f07020312070b0f060a0602030a11010b03100f06060207030203030d0902031005 84
    0x300a280040d403c503003080e040b55403034121154a03108910018002d41012001c11034041c0241c019004042c8243c1c503200e901e00d6042a42400c494082d4002c0000604600c00d0009140d0011400d900c12803107082a8001480c5070344001c0d50711904c810340240642e0b070000e8000d40030480b800685c0c0b02c3d00c00120540740d5079652420048c029400840c0140c41981c949481c19001d4500020310f0070031140740791241e02861101caa1614029002501245405540110107140e00c00725070b0400c80c403442c4010641107085c206a0224810807505070001c1009600d4001e00c2007040c0386600c1034039949034000c0c884568031001840401c0c1803c20000d011480070700c7c0802c80004100750700031250303c00d80304000354400c1540da0740c0400080d00c14620580001d83c2080001d219440c1c4550415145c42003902c0c004030b400038994010074501502c2da0314101e9410b5880b15a0182101107000d61780082039248014a011411600000c1e00e034410300210711006940c0b14100003c544080c00000001d05908900b000940383c16 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 190342769 1250 190341519 190341523
    0x60d050f0307081b03040518040c03060c050a080f1e06031606051b010618020702041d1e0703230f010501060306060206072c010507020d352a0708 64
    0x130b0014040300f41c244c03440c22000104e0003c02d6400303e84d4010040c3c0801d0071f03003004900c2c0401000d00240c41e21b0441c0107020003c00d540d80a4000d003401c56a9035103940d8922020020504c0101520f145c281419020500007074804230201c40d0f000b6040003106604a4441c000064504400354403030300c041e51803a10001400941010207001c2d850381c1305030381480704000c40914900721039030b038047d10350144c00714903010210002c00d80c0500000380c805040004c4440424580b41c070a502003c01400142e4889401c8110b40d900e2036800640440380000109422070131644c03002c0c59050f05405541c400120308403c00c1c0140e0302000720070f0b00806040000c014650711400003c010302034038010755001d0b1080002140f045071243c0300c0c4c1c11a083ea12550162864150518440e4a00c001026070741001010300012016a0b92540440103540c82121421000f00b40155400a16840380109002c140301603003800400c1c203100400c0b2014041e0410450705513a0a5002c605d140704071344490102e40e440b40744400320780e00c100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 190344019 1250 190342769 190342777
    0xe030a1b021215070302070b0114040b03010f0f060812030a02030405070f030c050901080d0801140406030b10050307080f0a030320160611132c1311060a08060d050f030708 75
    0x21120001011303a10001c0a506900c510300000f0305281516004204000c40b0f60f40541d103440d0018408211280300340002802c0d00c8010098142090751340050b5514800d02d03100300001010900702424038212130301181c0c0001d000c010310310052140c00000050400006000d02c030040d180001d840d0a8564690610342e8026110740202405442c3e0340002280aaa000428505643c25540e8040c22a820b200d8402c012400c08161160000d44900b00400052642c0c7c1c14548601e1304031402003840ca10309800c1518140b000d90225042c0d801055850804560100d804413400e0307014200480c0041c40d01040d85c00440321200b2aa14020022034007682c1c4040c01c04651034103a01400c0d05010603505031108003000c0c0719100031f25403001c2002404000c074440c120201d90f14040443c6107a81ca100303561102010040007161341081d0303984450050320812070044022031a511003070310750354201011f200b006084200c000d041244505440003228081103010440da0302d00340900004e136515101640b61000240d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 190345269 1250 190344019 190344043
    0x50f030c060f0f13080c010e030306030d050a0906210c0804020315010f1820041e03020a090e0a050d0e040617030a080a0b06040f090f0e030a1b0212 65
    0xa00ca000c26590786000c00041c1c00303030000005590f50368443c0003c0390001c130032550048850b654140900c0803801d80038402c800c82c404501000c0c1d0384d40d1070190200360403c440703400541d05110b01407110b918921740c086801000e481c84c46c100700c001d8080150200c441c410705a04103400343c6040c03150300701c00140c0c0310329118000c3d4030071703411601131903000031040341012024018a9030301a603000d420404500401580c1c121540244000038071700150584085021400d81c03644d0001d1040010201315800004600503002118004a03003132081c196070003c1d0040190340724a01601d516505001c0448005200c040e41042c0d0000071107008200409005d4072200944d01d94512880c6021400100b2411501c00b0682c259810b1000e18508001d00c001074a10345805000c45003201d07506e546146880e29510020006010300107915510140b80c40310b18015120143c404581860070301241c1245042c0c00001c0d100e00f1882410040b81d0140d120940400303240703081802940c0101082e00030700901c0780100741107203048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 190346519 1250 190345269 190345273
    0x2040302090f010320060c0607090602060f06060405150d09030e0f0402040e040209180604081e0a0909050903090d0602040303020f0f06010302040b0111010e010e07140303040e070c050f030c 83
    0x1603545119014070380d03024403004c0c1c01e40e00c010092401034000b81c605102c5c010b40003400981400e0b1000c01451503c00108c03146004200c640e0001d05c5041e80400c03c07d0b92020b40c150030000180340c2080443c1460059200b458000c8001150016803003503200e09866035082c0c0810108040380b1075007001402030b0400b0350a580100542501c072940390a040c000c0320300303580004400000c680c441d03a0174460f0041000300090030226481c2c0701d06031014024031400d8019030140c1101a01d6403541d0030621078466980c081d240740310b013080081c82182600a202c0d10101c480c00c440c0000c4681d40e00b240182144500303c25213501c229000100c80401002e03901a0041c0da00a9080740c082d0240b09a03202c0d606e00d01144083c1c0e9640c0301b0801000103240940001480d20411326202c00ca10080d40006425103042162710141c9035180c412800c007543c010050740001700f40c41c07941507446c030f036500011075102c1c4524041e1200520070302c4002105140a540e0a4003c540e001040310b012402c001c1d40c460b100e07000080900c00314 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 190347769 1250 190346519 190346521
    0xb100f06030605031905030f19020106090c020d0807051b010221100315020f030a09110910030615050607051b0f0a05010509010c060516021e031c0b060304060204030209 74
    0x32034402d11881054400280c01040c01c00c170011105810801e00d102c1c11150f40c4003c03c800c000d814144805000700d204001500c5102516801000e42940c0711600007040f510321304401d158a289d13001031241c03072004107806c15410030745640d90101e50358401e8110540c1c1c0c98160710a07140d2041415070040498840c00d51005007094031a80d84020b841e501940d1a058041c0e902c42c040c800300c0c9010403040c032006080c1c030006241c019a4003101f04c8d1030f042260f01d905000e0f5980100d90a110724008810f0041c1c004032102d00f1540380c1030080403020310a030300000e403140b0350341c9040a0902000000301300240000030071003902c0710a0340ca030550f903801c141e003442400194280c400130901d082420b140094840f0080120341540e00b0080111740b142c1005c40100d0401c40b947d002c280105660b03104403070054072601e2582c000107060110280c6070440c1c0c0c0d0802c1c904c04180c00d05200b030001e4044241d03100c1140b82c207184c41030f05440000b00c10140070f400b89000d6020000006110411409500900440c0e00c299411601 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 190349019 1250 190347769 190347779
    0xe06010c061a210c01110c040c110d0c0314090109030206031f0602030301050a05060309010f0e011506080606030109050c13060f0e010203070218101d07020609071a0a03090b100f 78
    0x1d20086481c800c4040d4024008101c2c0c1d0b60065240a43c11b03804401280d080c0000200044c00360f511100030040800e1034180e000c2c80d07107407091000c0403455115040c03210040074159001855007640340710001c0e01290200740c840041e841040c0140c0116001404561642040d4140006540461741001c0351900c0d0110006041ca00210030750f4103d4500900344064940381100748011644028040d51180d56201081c140304180e610403140d81c0840c400000901e08081c007100c10310420540c0090080c40300c1c40e4104215650f5000490303042d914111800f140d541c50351030000005001d0b41148446405260401161555201e500e50346109269983c80d00d0003684400166201e209803039001e908501030040e580741100d41701c0780c625007000c2e1b0341c03541072801340d941d4081d15a41140d468000c085015000203010005504220030b0b500040f8180151881c01d20709681c1c04586800b000b00440705100c040381101c1002d003c2c6c1e20992606409c00718003102480e1444003c416503149001d604210501e0100200e6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 190350269 1250 190349019 190349059
    0x10e01080703120302040b0c0f01052a070623060301060f030308070e1c0605010317040e040f0305120403200105090d03020d09080f07031101090209010e06010c061a 72
    0x1049519020103002000d0035612540d1882a07031010001c18517400300030009100d01c845000740401c84003400544446590481c1150a48002a007a0901c203400c0804c000200107200b6000244171a000030b02503500ea8103032170303d040034060440740c80841081550700f02140391000d19046105107400c4000704402525002e0401400d150780c08003400090f0400000343c1121f0180e01080e00c0508000c0240607500c070400304e540301525020b503049404940380c01c0104200007914062000c1d9201710442e15050a082c00b0310501403410040010b401e041ca0115103105040c01581110b00308041e000031101545000d08000d410800e20440750a0000e040391846110b03000188034082c01056500e001d00700d81c00c1a248120080d401c9160390903401c030303507442d0600001081c4600500ca0b4100290390152150000c0c14007a111310801d8540b600c1990400c200c1340c0050303880241075415150410080003990b2a4000100c0304810a05002041e151802c1c11045c0315200d15816562101c0b02100c80b03520192110741940 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 190351519 1250 190350269 190350271
    0xb040606050a0818160e0108030405010e01120b0925080919050309122508071a071b050f010201361a15090402090a020f0c010204140306010e 62
    0x100000d400740403110440c2d10406640e0380050440c1d000031004800b080d501c4c0e08203a04681c01d6141c0c46108082005054100c852182c0140040030145092600d07000c0007030028004c0000a90420802c01904031800c4080d5201c41c840d541c014004881ca85000440800070982c004445280c413400890300800651140b9585442009200d02034919500f0b43c2c40480c0a04c1040c85045405010920500d00142c807250210204280808010083d0f403042c01c0e10f441512182d040942e8105001080601c0002000074101007160010540381803184503001000005008007203009046107401d4031010a41030700d03002c502c0c0c2030302d008840c0b040030303032140400580c03c0359030701050480e607039a001c00c010082035000b0703110740300240740041a806003103425540c40180341e03a48444403110030880d00510130072004d00c9520b41851035060340d0410407802c103500007035003131103000704910444e940000e43e02d40108190705c281c03200030309544025926070303890741c507410a0040041c04140c040d1056030300015201030150006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 190352769 1250 190351519 190351529
    0x1905090a060f0c090b03060301060b0309070e060102060403080c0d060302040906090501050601180302090c0712180b071a09072315040e011406090901120311060628090c050408010b0406 81
    0x24200c481c503203285d0086903000141500d9240d565442c2c001900360005000b5445900f98070050290141130480100010002501c401c1c110347c400d400b00030000e0b0300200e0380e503000100300e01810344544105000e00060241a00000d4001d400d00200604110403030300920348030342c443d030000d0006540c1c003c0110f601002c0700755100e981403900002040541002c52005800ca401403050b2441c001c0c468441c900030006005440c80085c580d400c40c840b14a490200030301c01303050080c0249191000b40e0f102c5004114400098004d05014a0041140c150701040480c000f041c4000038a8800b01000d5030060107113141a1607103003c0c5480c1d144900e4042050700c00c13141070780c0e1004080305159080ca0130301d4618190300c102a40e0040c10401070921141e4071048918000d1508203000400000345280c010900c50100c04003015660150040c015281c0d510f0000b12a00a8110103450451840c00005406903605500011803d40360049000c00a68040014001e039a40700300244444c0480800307203c00c0b0744880c415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 190354019 1250 190352769 190352777
    0x11220501020c0307120f0c12060e06040830070509090108030c0d050a110102040e1e06101803080d0605010207060914041a030f0d02160308030a051905090a060f0c 71
    0x205200d01758242c07503100e20590040320500c51210650b9507500c1c807480319070400c180600b40c3c0c540e6801001007a00400202c1e001c1c0c00b003e4400d0742425074440000d402106a407840071340d520000740c030464811108101070140c0124401041d4100000c002c0c0881d4081240345004600b28400414101d0000085550086460b00105085400c20b4011200d90b00003a203e101001100f00020001c28824006032000d0310422060402c50b01b010301007150000d010718940100d900d5001c04000b296600c0d0800c050041420b428042c0c207100c40700401100214084e08020000c1c20003290a18101a4603401030041c1c0340e080e001c4407801c4d6146c1405451418446c440c40001c41c40f8015601078504042c5c009440004002044145841040d8000303400d1000d40c484d0103041c1d034444184020010f50400490410004e0044030b0380d102421078903400f41e94840203206c004155200d0011030f20408080103c4d207020ba16240c030800803410700c440c0280e15004160400c0e21440c1c03c045070f8284500c100c4c460580401802c9d22 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 190355269 1250 190354019 190354033
    0x102070305070b28020d0806040b0f042003090105010f0503070f061b02040203070c1104150504151502030909071b11061e04030204151206050a11220501020c03 70
    0x5030100d5000091803010011280c48200d040501340f0304000c4070359400e8001d0442c00d040d4550040080c1c0000304118802e80c01c000c03200c05152640c1103103545400c4259004126a240446c918031007140c10345801150003000010841407a80660001d41690508040055599503900400d640d40c6a540200e0b0742104c1150300804c1010300403296500760360b145070610041d0100c03c1d00010101c3e0411100c070700100740d50384001004c00c031810841c0070300303a2000c803070401004c0c000d010000140b0303146001e41802103a03200807003160412030300e00c240000c0c40c002c98044074050a000e4000c0d2a50001c102d8640500c160728081000513000d06000e66031403100c410200700e02c04844c2c58812600d4102603043e81c011600300402c1b01818201c4010b46000200c0340c44203540c1d0361451041c0400c0703038021004c3c84c281c0030455500b4003003c1500d141c100131031504840b01180e142c0fa004c1400004000700f18490500c000001800c0c0124a000d00b00c01d6506120306154003003e0355618010398071101071920803503047c4c02c200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 190356519 1250 190355269 190355279
    0x2041a0a02062208030c0a020f03040617060d080f0406080907030f1b1503061d04050d08041106040e09100543030207020910030f02060a0c060f0608010605010207030507 74
    0x10210381d01e8103482d00146503003580d0f40c0c0c4039516a030b8010b441369505181e0004400d9040342d0104251440d440c00382c0e00540c500340c0703041d5009019021402c0030540411001000c6411b81c5d5600948600c456040500d4654695403a94a040640c0c01441b56801180c41403000a0311400f010508000b1643c200c0c04030903080e1b080385d4403454100100d120843c1240a29040070841d150034412460007002c607500c0000780709042190201d0351188401c0d02d88241402c0c0420007001031fa0120f10050041014203001499850302d151210b0868504402107822080128001544050882c1c04a00a141c0c58081e84c42d80d0700300c0303030f12407050381e40444181c3c80e480e0213036200103444485089081c01860030a0030b5008520000810b1600900340000f4a60010381c01081150551030420450780d00702003000c0a19051b545542d842d907000400c81407020744034840116141365828026030301c550549601403003c1124440b0000800700400250003110117075844d0a40104e105d50000900b40140e0390054000d24a80e0320f08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 190357769 1250 190356519 190356541
    0xa120c050c100209063a0506031203040c1e15030609050114100e010302130e100602030c0601051c0615090b06041809060b030a0302030a080708040809040903020304050d0602041a0a0206 81
    0x17101a0704030303200100150b01000c80d288483c106c04a07a204d00046418142038040620b4510800d030029003100341001440300080c0b00802c03240807900c4840c4008020b80c0034031820460040143d10600082821100000713400380e25a20134000d5901c100d004101e40d076211403003041c41d00c90400100340c1001c3d000700c0d19a8071600070901d0414103601454017518018060340654209a02503010030b03d2000d07444244881000c0071031440c4082c0c01544000c6080092183c9440e42d1607406200c1d260299204a0391411885000c1c14055005904000103010320f40c1b040c4000d00b00402984070341081c8501d018007403041071a0540845044820364801c0301d2855084441001c01404a18000c494076542d8441a01d4a03031000c2c450a41210702940156884240b032a1018041c000000d0211082046903002c2100240c079a909507099840c05982c00a18140f652030264507520440d044a075110000115420030800190010010b0310300701200880402c0c12007040a9240c0690400719015811000000f000d459403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 190359019 1250 190357769 190357807
    0x30e041802030322090f0f0b0607030906052208030903010605030118140a06090503071506060c0f03110304170f0309010c02090702030717041706100603020a120c050c10020906 77
    0x488884039549070b6175031054022119030000a011403520754075641851030319403013101540030302170714190700d13220090f60020034001340d502500092001c08104502c40c210b03007002e60321901c5c0c040c04000c0300d0a80c461074601ea40c0c0d0483d4849038071a41c00c29202040a08041c066550314814240e840c0b41c00c80041e0b51010050703000e8028201191251941d01404211640503c0c0942802003000d5981d40100d401d048044000d04000590a41c1c2402c10800120b5403140e024880240c020003800a41c0d071680c80d0890b440301008030020124400400c1c00700d04a40c0e40c071224034510110500b100d80c0b0320170b03402c0c020307803070340a49050700d404120300034146400f5051007003a003607001140b881641d01d0030526035140d080d248611100c18a10032404a4180300001a002060b03800d5540e9000420701c61510003209a045682e030700a0310101500071a140d01c490380614800001c04e80383c085c2c1480b00003180c0500500e160003070701021419118242d0156140c620f50f00c2180d0800705c0107040185445200300c90a000d20761 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 190360269 1250 190359019 190359067
    0x70303050a0e0f0406090903170405060c030406090f0804051207150e031002130e072d17010e040606150903020d02210105010509070e030a2d030e0418020303 69
    0xb000c83c01e5601165034510410001c3c2029032400a043c0845d414001c01c010398420a40b4018869441807101181c0300044e02680072500c850025a25603a501d8410050a41c0c441c00804a0780c4011030a010444480043c02c2512000d48440700d045500d1226640d6940303051041540f510040403448101030711601c0789031024580a000c4030313044c0807407145050407031b0300000791a100c0c641700c04e1003407000340d528079401c41d0001da1900c0e040c0000c101c40b170a9191038404807845180c1614100d20310900da40c0c090205011801c15000c85000c1d150b070349081000894004840448040c0c3c50700c0b8000c54250072031920085103032355035518020300d0741c00c6500740301588500c150141d034440c10585c0c070501c490412100102c1440c50f10800070816514001c1803140300c000142000080c000c0380f15a0300d40640340001e07480d0701070b5042140740340c5000c0c400f10b1010040035040d401a64001c180c46591040c903401122450741e4060503181080a1501200010740e00305100744000d505400c2041009070000850b41082540c1d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 190361519 1250 190360269 190360279
    0x209060d1406010f091d0615150d090606080d1b03170c07020109290f0405030d0507120905131e0c02010c0207050a150507050f07032003070303050a0e 66
    0x10701d182103070a00e032260990000d4208031403040280003100032401800390700e0020070244446400c0302c6540c1a12100002e1117502080040c3c1a030750459916540c083c00c1c4141c4541119a440c01b520441c2d03009030500c95801d9030100c2c21b0850000b101070000039032180c003856540e211203803000c0c0080f824040c581200000c1d401c00c42207035040380340440c1b103910007405180c1e507202c1569034025510000d40308a0803980311101700381c460071251b64280489aa081c075004140904a41d4600d1190010301050260b034016a030140b0035100d480c403a464010b0010007845028000c2100302078903840085410412034050356412070540f610440d074030740303950300410b082c4e514007030070444911110401e08080340c0e031030102400144e440700c03142c422442d01071003404042c00b4262428240c0d1802e00a088176201a006500820040c3c00a52341040c018103200c080c1765414428140d50140b1342c4c90801d088412507494100540d0944920301d8021b6180018508040704d0340741c1c807090b003000c0c50444150340d07859488074465041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 190362769 1250 190361519 190361543
    0x8070207030c0e0601030e0106050604050d02040905010203070801030203150105100302030a090f03021b09010302030307020f150d0f0b01020610140a0f180c0c0f0f0201050702040e010c02060c070209060d 89
    0x1c05252284016100381d0703c0080c450301d810b5000400f03a40d83c460300d200440c0d00d843e00038403040d00c2d40001c5074207640b1305030740d90748906109101140041003c41c0c4090201d510210601882581c80b40400b41201d0084040303884588000300d49860b0403e0a21901e0b5101361081010010b0901940103184d10001000e400200758125482c0c2e6446800412000c4005030045080c5000411048107480c030101002d0740c420100d5030440d804240c0d01d10591001a22842c41e4080f980d159a90b004d5000d003407104c003080742585032010060000050001002e074015680d042003c95121544001243c600c1a503100c001d10011500d440000c0230003001d40c1c9400d0340c101709507140128840071a082d9650042207880342c3c1090015070360000004a40308901c2071004c0024404050f008964140b071007090198102079028540b07070752480107035541e108187c4000c0d042070516130607000c070301010342c0240c000307040360f800351800c542c2c0302c1d1000003091241d0b8100960bc000c020300400e406043c000c0d8141101da12408182c4c80c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 190364019 1250 190362769 190362773
    0xa09080c031c060602010612140c0a06030608010f14241c05060714040b0903010207060c05031509100303050d0e01051024050a03020c011b0504060314010e06010807020703 75
    0x5680c42605420300c204a650301e080314504062240340d0007000130340300810085040c848105c0c01035000b07110140c8840c2480015a82010050000004164000f0712840342182c0d20000900039040381c1c858149076500e050030280701d100982c080e5499822500911410310f40c2d82c01895035030039260032038801e003010501110f0040b54594200ea070881c0d59002e00c080451361110f141c85880e00707000400b02e008100390342c08284003010194040ea0180d500100d66651035880340170201e8024081d0380c1010703284a040403010b1949541210080d40100c4070116010501d14000d03052285101d801d943c02d40001c19000010000700c0c0c4150050140000c010b500400d02800c4121000c0c03e488054031504000d4180311010480c55203500721000c01903411280e000c000d0100101c01a116000703840d030b0102450b4002070101002c05003944602e58030744c1c0d44601141a200701500050964109002d03801c0480d00d07048003240c80460780c00e1114122011250384a0040c1d0303400b00111a0040c3c05807640d002e62144005c0400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 190365269 1250 190364019 190364023
    0x60f06090103061a0301181b080a12030908040314060603160b221508010909030f0c0516030318080304080307060b12010905030a0e0d020109170f0f0309040608070e0a09080c 76
    0x4a04d00f03031800001047e145042c0a51180010b0010300100000d8500812095202150b200000764104220a001482c4274005801502101c480203252181c0000c1c04420407500ea20400301035030542088070740603501c035024580d84001e490324000500c09040c504108910200700200005030341c80711902030481d00840420b10705a40c075044003a0713122030340d0484603200740d04c00c50003401800208400e0103c400551006480414250000c0c2d0800032401030b5042030020070020f03d6600401343c04000601039480c10001d00c1010000b40520b042001850005444000041076505407a804005907281105940e40c02004040c0d490905402c00c86603041440c45400a20401f51424020805103540d00c0345188010060508130341c1192040c0d4900c440400541d0b80624114161000207504240342c0e0b41801010389000d00c003c900200603c90f00351040d0101e01c021000d0f203101c0c0c4042d94280003503911003420540300c0780c040c01504510310300040014001c44443e084001500c2c05038040f01d1901e503007494214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 190366519 1250 190365269 190365281
    0xa02150a020405010f080705040b07060e0a0b06010e030c0102060f06042009010912050d0309061b0903150608150c04181a03010c0504090e0f07060c0302060f06090103061a0301 77
    0xc048a030301140030015560888400c1071180c0b400c1c0382040c8070b86400300015086000714080c01590314030100b10101000b4043e80300f00c0381c6c0705294017110300700000c0e481e1180300480100c030020b000803e6045400824180080c1c0c810300710f03005801a05540d40d820801000e888002402c20b40d019480341e4001c1c908802d281e084e0b6051001e44030781965613144d014005400c182051b40301daa220854428484081030010074a0103034038446290200d04580582001310280c01401c00d111209000c104801035507603001007965040320312400c505e6100e11200f8a000c2d04881c21481858920307080180404d03526400788a00c141c0c0442402246818141c455041651800034544487c602a0795100c0c801420301c2002074400e080d01080340203004c898000391004003e03000728031540003014ac9581410005c00c0d000c0c0211480c0303802440444a04503512440180780407816a416001b50003a20080b800440d91407441d00e02c2043c014009002a03403030b654400d030040c072454119540c00780c1c904d00d41d202e0399502070042c9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 190367769 1250 190366519 190366531
    0x50114010602060906091c03020c071a04240801050d030908070303050325020d120615090e0705040e01050f12070b0c0c09010f03060b13020324011b0204020a0215 71
    0x41080c0c4c54101120707842c2c250050310344c8246034042005014081d200c43d00180803502c49250160b1a5107180010342d1500c4000d402010250301c035a40a60a659800c40c080c0080314005540c40360303001c0505900a410748068102d00d03000400000051090307003000f06172201d006100f403a05e140d001d5544d01e451410021940c0040340081c1c4000144041c0d044000151108501c0e403072011042200d4081c0080d54440840750003070144403200c4000c0f0701d820402d5200d100146101a0030fa40104040040100a10035070b01035619040108008140058891801e071000e50305050306040743c6900b48000c001c00821030014403a40442c0c00b135140d203001e00d028443c41005100358080c9544509448060311b05004000f07143c0c034002c03003087d00100a01c50b61070308200d0840e0380286002a2403041a000b20761040601400745102034000000c3c000300803c540e0140d225501d000b003803500324044400044904a0f00b10400110503e8910091320151406900400c41d003140c0c0e00447d800d00d1072030007082140f02d60440b01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 190369019 1250 190367769 190367773
    0x3120a06031709010819020903120703090b1201060c112106061516060615180e0610030b0609040c0e0a060305060607080f2a0d08011a0304050114010602 67
    0x410020421140b6070308101d0b141c6000d800e828141140300003860100300401d400c80c00071810460300e05629007681100d08503880a810360ba84005c0f100b800210560020b01c1c2100020f00c00301c000115a03a8030700c251000100358007020340459284c03500440d05400e202e101640e000c99182da80c2c1240f503644903038803071445900d04640003007682800100340c1440c0c5c0c02010103000304402c6003400403180541c01124520076000101c1c81c070014082c1005001001c1c42d03046280302034041081c1c05116a00040c07110300d081800347c13030b00c2c06407038454000c15429070b029030f00b082e040102554040f02050007a00050360260020344018101506000042c0a81e580d80b00803d010940d01c406501050a0040c040b40c040c1c4402d00b0148018141000400d01a104007407015100d42008103590302810750749821a0b0002d90540361040002c000c011030042e010f038810300700c01011304c10348085140b40ba0160003864100c44141021031505116010709400c2a40010000c039041d55079900c100c200702c0e4980039603602070001e940c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 190370269 1250 190369019 190369031
    0x50d020a06230304050c0405070305070e1509041d0d0203041220030d0e040f02030405060408030709030c09060501020c09010803030105130204080a03020309030d02010e0a02100314090c040c0905090a0c0203120a 92
    0x1070004503234002c2d00040030542031204004138590401c403c01c1d9000002c0d00e41c0782c0d10504045051000f4001c800c003d50f4040e041049280c1c00344420035115070694180c00680d17a46024822080c0c0c0c0c0c0348502d100c0d44a41d0b0b10149440c0000c1150642c861031440409003503950490303400c0c400a81402c1c0e61089a10118600705440c84003420030f403280e2900c504c4030120071441c0d42059202d40c2d5403840c000b40000c00903d800800624401e1080701c80300011039002d02c1171070815071114032840141c000c9000702401441050421649841c24600c424101c3c1c0000010b1451079003007905006e091a101480c40c041300383c00f00b000060240c002c000100385170b402607004d5601c4619050425003400e4405101404583c10040303240b0741c0541c00700d0b800251a504442d02c0224020912050300030b031010340c990500e40d40388402080011038001c64030a02c844012682000b01580c40a810307105841030780101900588031000082c0c00d180303154130040c010005401128100462501010581c85044405428050300c0710 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 190371519 1250 190370269 190370293
    0x18030302131d2d0103200415140f1c03080c040602070e1509070221040b1b011116120e010804060c090b0d021201050d020a0623030405 59
    0x41c0038030026101d010200850303103440010b50701c4190030141c1034100c81520380e000035403011920038000700d180002c0703090f403102981c1d07034285403003c00210200c00c144014083c54410031480c09108281300c0402000000c8a5075003404400350000b11a01c06490704a20009040001603444005500c90746d985655501d80c01102c902c0c00a0105802070712200d22010140011303c21150041407030b201303071002c8904001c02035582d02c07043e1600901d0300e80b40d03580002d807400a00c103100350701041300c0100032505030130702d920145000541c2c6187d12891159003648241801054840c4050700481c5950b4500d000001c00e40005420320740311244d00c205c50181d216001c01031010208042e05e2014580c52005080c10818541c9107000078214500060004000382c0e41c50482114890082c00700f10050f103014411580c07104065101e181c001d60005042e004072400e0a4000030701840d15a030054906540a0520741205d86006429200e803081c25485000582c0e4403030203110b9a40f0800090361045025a0050280c05228 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 190372769 1250 190371519 190371547
    0x100c020303280f05150f100e0a0518150303040609050d0503070501180c050a03110904061104060507110307050d080f040b0a0c06051302060f090102010b0405070c0308130201020a140118030302 84
    0x8174490b030044e640112141050340d00c43d080c103032075450181006803904005000190903a1055000302d58444d0700c0e0001c0702c6032071031512080b134450009080c800903402000020140e50f4011172082d103001400d201e406200c50b041c9181c00d1801d4a11610480741025050b40d162030960303645801d400d03001c4620740101740074000780706520001071000b0780d440c408560660300c5013070480200c030709000e020300b1156020074104040c40c1c1c84007143c000308882c40d5440e0b90311540001d12507030102500740c843d1413400a6210103841c001c61140c048a80003001e203081400c495550146580081c424407078a48014400000c015000038001c10801c611550b803880000300c10703d0002d04886001d003810144126030400d007001a12420300300c6400c0403590b003c5540754030740d401c0102e02404034070151a40150822050000d00e036001000002960312039103644500e44d1381d600040300e40707038001c40300640142e001c00301441c003040c44038240c04850b201d2100003080102d849210201c000803808011000250300080e1070110281c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 190374019 1250 190372769 190372801
    0x20403060b090a14010e060f09011806170604030c03021501031101091706190b0a09050405010b060a17040c0b0c060106020715020304090c0e0a0e09100c020303280f05 73
    0xc8103c2086081655008400065014041c0f88034514a8001046e903c1c0e44100155000840041c03000c499581c541d0b0050707500461001c00c1c100014203182d8046034400030311140200d40b0452000800c807594440e2821034a0380d4003420154198000d403010340004803842d0b68180d02035401001c512110405240c00108041c525921035140f06101951005800074085080358000d002e0003003a42e1280c0c5444200002003c2021106074441400440002c440303910b82c10a501c150b0042c0000c0204404210601180b8456810040c0000d401c400d1160802c441c240012a04030b0301a005c2500c50036210616408154004c02c0540c4856002c1e400401c120342e410030101c0040c0004c0c11003260441c649440195581c020f40c0141e04005846915030005144a081da02881004c020720b038510032039a1300414521311005645140c01e07806542c0840348481c1103405100391100c40c07540111703d1176550142500c0341054144c0300220f01d500115000c01c0f001c0040c0105050040f180e00d0004160601c598203501a00c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 190375269 1250 190374019 190374031
    0x210d0503130209180d090915050102151f030b040506011e090207060209061b0709060f0b0901110607090603051620030706140910060506030a0c02030d020403060b09 72
    0x6010400c011522001c00040c03925140e0590f0703812959210403403902c1c0c00c1c0103082c0080c0791a01c21304268104103a0311404110484041c41ea04001c0c0000ea5034600c00902c5003401018007581c0040c04c00701c40b200c8131284083d8803d40c15544a81c8245081d40450086840c41c0c1c010f42c0c4c1001d440d020b01040c49028003903580140050081c46100040e0b46d0450032415026100354156a64045010310522100d0f4049a4003070000500079669407204640000c0d400c02c04c5074401c0b940380300710740d00403500d000036214020980d500c0209003900280b5200d50103103a0741c003010140c1c1c1008420740841030001800c010301c0740251002d0301d95079109410a40300404644008000080309241c1105d51922503400418403c1c0c503c050704205030101045001091451140900c000d018030f00c0c040072205074040b14100780d400b80441000b80c54000400e41c103494295022401603992190041020030220141c0c2d03841304d00080b41900689040c403421403e62000c0b60450351080d207096803911406480d0b494040b43c0180d000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 190376519 1250 190375269 190375277
    0x2112050a1205061302070615080304170303010605030a0c02010b031f0c0201020405090a050702071205060a0b0301050402101107030803160305062b080418060503010501050d03051606020405210d 85
    0xc64a9800100c00313040c0d400e4901c045550018144042c80b80c19004900c3c003420012049500300e64640806030707264070601c1035000c200c12211042681190100c1100d041351415a02c0c107082d5250052035100500180a847e401c0d03660f140c0100080b6107080c0640c65690b6104d6900900c0724145054440940d6420165041164410442480070b41d0300d40c0070742504502041e030005520780d00c9040c140d1800980390400b280e0000780c0203a400030400000b840b1480345e0b545050078040e100811080c142030f1041981c000390310400180103103556622500401411200140880d611184c0c0da484190455105844110081c4401059280300c560107001e155003240c0142c07180c1c0001031001e10850018a6511030b03a0582080540661081c0f14110056401800d5080c1000301030082c1c403905140102107600c0383c04e00950a14000040b02e07d4601000f880c01030705500c84078640898000c84200c0000a0f00c422590300c0e41c244404038154441300d5408480700340c04451007000c0145600101d00c1c0c2100c0c08400e10800c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 190377769 1250 190376519 190376521
    0xc11010c050a06152105070906030210030f0f0c020a0c050108040819051c0c02061602030f090307030f0b0708010b040315020304020d05010f0b010e06030f012112050a1205 75
    0x108005800500b464004a00096480c10108103a59801250348400510413140038140140e0192108800380e0038031500840b61a180e80300c10030303002e0382e10611010390b000c221641e605000781d000381c0089070122802d40001640310175401e803074030440b11005840e01c0140c2c0078601250800c000410004003411003401c7c0012585400d6540700114800d00d030310003642c00e080c0c034a042c100600560940700d28003100e01041100640340090700d0028007403082d4403c014410280443c100c0710505200c2160b200f030a50280d40341807990448071020381d00010b0f00d55018411000008080382c0781c075240c1000c151282182280c542400e000087c050301d010707040007644480030001080000e1060030911a1100d000350050b03225561400090003818a50b50050519403c0c401a001c0381308607540f1150005400b601c440450044000c1889228041100d07000300b40d0718018010300c034031f210100c920055000500d00c12103810065640c2c10100d003503400d0059010441c045011801960003003250100040144010422 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 190379019 1250 190377769 190377773
    0x732100e0301051e1b070519060b1e10020c10020706140a0207030b06010201090212071805040213110f0a020705120d02100513060e0c030d02030309070506090607120c11010c 76
    0x8640c0c0c010b1711340c0020410700345241150050140c1540c591a07046429181c4111492040d02051010040105c0d2818500701c01e0b42424034007004842d00d1035400540d1131804e0035024041c030207100b000b02c00c594103521612480540540d290b01042c070007901281d024104403480e00314050004d10300340400c1060310703c040c08120907a96000400c9011681c100030508000d4423600c00507030061180c0080030350010b00e840d650302d45a41002640e00c04507200d4144c91800700c88012000d408960095074000e41c031070303400c1d07454070741e506029040040e801c010b03056810720701000340400000d9a07010502110168009002c1001240303010885210400d2600b006441071440c9500003e40b207640e4207920101150350350000c14030410f046011100c120341c1c00203041006503210040160303107130b8a80c9103180c401d124506500d00c2c410310120603a4000d100c400000c282e41030800040103c00c0d00300d6042103400c24401e0020b4004141c8001d08400c0703041e001d441d07050104005003010100c4040702101141403107000c1d440c20f80 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 190380269 1250 190379019 190379071
    0x40c080708070c03111c080601090b030412091706150901180e030405040204060504030b0a09050d030e01111b0606030708030a0e04020d020a0504170732100e030105 72
    0x5032080d0030b481c00d01010001c3d441d080c1d8418081640c290b801c4c0c4078292820004103890048200d00c8991501c0f440101e6841c640119810083c6000742c0c05c02c60000c0c00400d00164401c060b20b04c0b0356481d030401d20800e80e160b0002c40d400b1039040300d41512a500003024400c1c2c0d2b1031041070841e06a50706440c0d80c1803641c105541d1017519052080001c00056484106079040403081c4150343c06440010415541c0f00d603101c400400c150440d000a90b001c1000a0100c1e4014040c0e03c103802c405030f444000341060003100c407400d50040100780340e261920354030f904c03040d10520030b024000c0030502d85010200c200203940e5091207281c0003004003000e010303501100050051030f03000000da030260780a40c44c1c01c0c08464414004a4040d000300007951030341c603001144a110302c0350402c2c00350041d40c2002d51181c5232a00e43d181d06680d107041ca44101140c0200c030050f0944146140791000c031000c907540c001d20252101d00d20208003a14a01000240000c0740303000040150700d428064650440395100380310107100c000d644602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 190381519 1250 190380269 190380271
    0x2c19020702120624091501050d14130c0909030c03050f160f0b13030e120a0204140118090803070c06020909090607120516050a21050709050108070c06020f0d050406020702040c080708 80
    0x1810f1040116520303100d105141c0022004981c0100c1850450800c1c480c0c4d840009840e54bc111841020b413400412664640c2c441d088642c0c0e05a07458010040181c2c17815100750303001e0580c80a51240030081d00c0078146d10030b000c00ca0310920682451002c40d100c0e04101c1410000500043c01c1b0032611000c0d80046a4010218051104201d8900e91080900e86c840c038a882e200c820001d40103814203468040c42580c0e0602075048a1481c40140440c641c001c020500310f480c50310000305104400e00100d04079522840d10640054840e150040c0352610007000100071324811909141c09074080310410111944c0051009074901c0b0001007803000f420075060000c403c081c000c00700303801c20a0114003914410321500c0c49203102c001c00884803009071700c441e4402c4094417040721b5000c045412000002002d51188486a108048a41e81c1c00c3c036644c01591440081d60080f504520300c80300c10306c11031656241610039a03000c2c510658005a44211510500c820780f00c8420840081c8081d90041001c441e4002d070701d003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 190382769 1250 190381519 190381561
    0x2101080606090414010605030609010912050f03070e01030b0325060302090d080a1e0c0b0105060c1902010e03010204081605060306090a021c062c1902070212062409 72
    0x80f10182d8810040b07801410164040348d0b05119440a010b8940010b40c00281c159014070042160301d605044162a10320502203420591b100810000e68440c2c801c90501552041c14540407c4010401c00000d01d84116403100e80fa118540703000440d41c80740300c81c079120000e120505055041ca80544001207000c03000000181112a000038007100c042e00c10f06112881041e40c4170001c01c2100152001000c3d07440203a01280c1e44030000c0e001041614100c0142d80343c440b2800020130902070030480081e020000041c007281032210309400c1c020203590a001420141c0911402001c1603540e54001c006807141c0c41d1303c0305001d100200148201915460700701a030007107414402503a601c501d545202588503040c00d0b014040307482c11902096014060b2001c3e14064420b01c1c180403802d044544030402400191500c100c41e0402d0180301e15507104d250090402d05000420032030380d41104241c0302e42483c03800c40b2007985014050078403030980c0c2d55180c0c03241241e070015500c4ea40a40f5103410340c465800101225 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 190384019 1250 190382769 190382783
    0xa0203070f020c060f030a14040b0901060803030c0a18030501061d010906030b0c0708070804030c030b07030c08180a06060e040c0906030507050f0d050d0e0102010c0804080d09030207090221010806060904 89
    0x40b261f501540004000d141264804201071030503003003c3c98000c00540300c0881c0c9500300340c0005680c100010a03240101481c0b50121300c0c10483d070a0949100300000010f401c0c41c1c421120000100300c082c0701303050080203842c482e000c900d0183c00d00720360103aa05800203882d00c3e01e800320901c0401c103404110399120511305038850b510742d45070400b01114060306400404200700060040100a03800d00c128040f00e204030356601c40c0307403107402c401e0701601d00b40307950140040c0c056000070f425030f05c6068408403001e4529050355010030464441d07000ba500560000d0141200520601c4100101030400e03d00074001c0b4041040780c14295550b4540380e1110744030303243c4140007840305040556100e001805503164041e084800c0c098030b40ba00a400e099a22080740d0140d46000d610040c454000e1400c03500c5140e101811a143c03580c114a104020241d02006904603c41e420f000304166645100a24003c00301065140c18988100c91a135201d1005030842c3c5080c0c3c00607010310031070351103e1040a400c0782c0d00c184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 190385269 1250 190384019 190384021
    0xf0e1e06120132090a081c090c290409050a020c0d02012405220204030507060519110a02210307030e1305040812090a02090a0203070f020c060f03 64
    0x50000c1c28500307140304555180c44109040b0300510000c001c3c828220b0300d09940c00c544002e0600d10301142c215082000d54001e81c0c5410001800d403030082140e0110703088458140c6200c07082c10700480f620300404589040180c5c5042c09403400030888800c032512895000743e03242d404004100d10701e00403803145101a80e01d40300820079111103501900c4d100070580c41210f05100d61640001e002c2d1008040f14010380c01500d0003000001c02c407044410944801900304400f46054110482d4250413544114055070b17428800800054010301040e402020140d44183d1190005180000a00301480c99170080c0804402d1111454002144a111298045078410380c0100031100c0d01450b2590f03200070000501001810808050700400320200b01c950696211641900d600059403c4500030b440290000c5810701c0300c03001c2402018415a07100009005032854101658003081c220380040c2c0d404a89a44c022080100240e440021740303903403820500c0102045140d0704089145445000110980168000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 190386519 1250 190385269 190385281
    0xa0923040c0b0a030b01030f0c02030a050706060e16020c0105090f0d020a150504080705060408070519050d0b0601030c020a0b01151709010207021c0309090b030c03010903030203010f0e1e 82
    0x44250703802000300300b4405654854104005006180e03801800c0c2c0030a2074810b01e104803107414861a01c1d84007003500114a84044000c0c00d65581d084104200d50700b54480c6000301e9100b90b03451103540141103642c0030090500080b0400303030502e105d200400303040000900c01d603500399070b941c001c1164104042d5000d4411250a002085c81e829458001c50b40101880b080308510580c0800240110ba404c0d0054850301c4d500d85081010b00c1c41240b15050a6a100d00310a000d14070780ba0203400201461501c04008840e0381d4400704080c40424101a181c00c69598204019940c0500501802c0c0c80c042c03001d05010425651101c4103c0d8042c00780081c09544007100300c21160013140000b01350703404140310702c10a24202008602075804104128024001f00a10202140307000b03508c8030400da41a02d9072070000341481d5208004240490040f607041c0708a0603040c01c11303107080c41000c4040f0300a603805a81da43c142a41450306603081d52004010580f0351003000480c29807044100e80245450929003180e032205 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 190387769 1250 190386519 190386533
    0x4050a150b03010614030708011a0402091f051b01050403171503012a14091e090a0615110a080702190603020307021b06191412060a092304 61
    0x501e401603059031a240022520300051820020140000c85c11982803a0711081202d0070ba54100c8843c1614540800345c410f141d15198000c1c0c85240d001038550600c020f641142140070201d1200c3c01404120002401c2024280840411020b9900b00d0000d0095003032a0380c006107081d170002c02d10703102c95414402080d8170000880b412056840c0040091004500b0441c0d08415208010003c0c2c0c0c001c1054110000c1c618052000f5000c14802220058203040d000002d00011000ea00c03413905840d2034130782d111a05a84d45034415070040600c100009070301c0e42800c5d030faa0300c05030880350410b0501002d0380948030701440000d2114082c40d030044641d52516210320229101c041d10941d0584600810785000c1180340e81340e400342d403103102036038204c500801019080140300307900c6810458102400f04104287c541c40d2254921150596290801d103440c00c041c044000c4e41c01c2841210032071000b00b4207001c224a1310141c03500140034114420000c9020146228007041005810641004075640010303060100c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 190389019 1250 190387769 190387781
    0x607030e1908030316030606081b041508090f0c0604030f0203030706060308030f0106140f03090f060106020d02070f1410110d03060509070e03070b0c071805060a0e04050a15 76
    0x2008081c1c0c01480d11108500c3c1c0b20340045500c0300d101d09410b08005c0c40c4e0b920070300540c0c04039055921410240d4403401144090000b103803007041c00c03a2608002c0060000100c003000000100150b454581c6030070300e0740f103203401c284000184032003d40c02a140240540d46140443d000c40b0351240d5941e000054a101107401c60040b19005071500b89400300020500110b06d0007503205417491018040b15a88550b001c0d650449210302c84210424107002c00348400c002e1000440e009a810340860b0411003c11000500e0300009800c01030040e0041ca5418414a0b01004000d01401506005c111050309001030007100c0e4900021092061000415060707116000b1009015001004c070705950148103100750140181000d4810180281120360001c1d1415126034400707000707410002c014044240c078091001c05150043c0788444058042d0b00c100052003c02d84081441081404202042c64a000030802060040943c082448110700a0801c40000e10100300d0820480c2e0210342d0284e004001c4240c0d00041503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 190390269 1250 190389019 190389049
    0x30b0301141003020a0902040b030c070807020d03020c01030c08090d0302070206070804120b06040902030624030a0f0605060a14220509070e0115021c05130306020306031b0607030e 79
    0x492000b44404107840e06214002d032802900c103240b0702c954815980089104910401a441000740085503000c40740c0700050041a0050901d01e003031040540000b40c0702e950300c80f011400741e440103074929001d50300760080b80118880341c2800d43c030310301d010302300c658a485030580003404042d4009a207400311b6480e0001d80e4440c9070002c031111744032030b254806004030460040080c0c44500c001c60005413180740ca80102d03401c00754060040d00007501d41204260701c0410740e0405c04041400400300706001d480800c4580d81c0c0c180552108600c07500281848400c0b02d8000c1e00460280380202401d000d900100c3d1200f000004080e9403070911010b102d0804410b03180840c0c0d40340038140c14102403004100c00040c0700e0050720307111072282000707999036040d0742c6c5841803c0701000b0150b00109003100d403521913016114204500b60800d6440c100c540051000c1c3c01c80c180d0421940303550b001c030a0040d0303403e0810000d01d021111031001c00b40c5242820000300980100c00c8000d04200701150440c200b1703281d030300001c21100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 190391519 1250 190390269 190390301
    0x60603070507120f030f0c0c0308090c030a0303090b0f06011e0504090603150f1a091302060a020303420d06111804060f170c06030708010303080a06060f030b0301 71
    0x203903020b00100f0782000c144d55180020309113241024074500380d21403880200c5654844941000207658155010000240100b8050183d800c00c441d20382c805006161000307100e9940028034903c58039200e2440b44005e0704071502c075441101082103d9800c070700c16889801c121403c0c07030301140750302800702d8043c803440e0031905001c3d0404000000308083d4084c51401019881018880b110550060342c0c1203400b0001c0358201c00001107103407201414070050041c0c2100e100c1941c14114000d58000c500d065015424070303030060340000200662080b4144103078a05103181760b04900301c8034100406202a4410034818201c0b0302d8180c2e80c1d03412599a15000c540d00d5684840c1c240080e092070300700940650403039011028800d502da12403600310b180c1446000c0580d0340c02c3d000d0750403450030041c1004402962690030903240c8101900d90503a55607a001030b522801150355007071025815458000c001240107071072100041d00741442401500c0c2c10419010041c100b929001481107210000a40034142d00c00c0c11740b40d24 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 190392769 1250 190391519 190391543
    0x5060106080a09020a0b0306010809011509021b010903052107020c010e030a02091006030c030b061e130308041401021506091b0403120e120601030201182705150306060603070507 78
    0x1814246c0c059481240c1c01d0300d0b0503c1c40c1d0b80d103810203802ea6020071281d40704001c4095007801908060360161000585a4100e001d2241c040c030102d0703086805416046c0c0100d61301003040014014090300a070501c081d1b165550905042c24a8042c2d52000d410031042d05000d01c1c0c40d4110b000b501d04100002071160000e004d0903460800d0520b0b410030b0100342c028800003030704000b00302e2030702c600030b01a9145100001c0c0c01c5c00d1411000c40075000380001420f522080700c0303004011107046641d5405003480a14040d00001d0340e51890a40c404103104006c401c1103056401c00ca0324403d85c1c0075010301c0b0540c001c509450700985e43c3d0302d0002d070100d65082d0040d841004000407401001380291004051094901506c8642009003410100a030329103501c00e441c640c03036004100510055206050215248180010720041203894102c100c1d0b008001d40f10f404090620007114803c0d1b05082e01070150810303110340c650a180403812010903112240201194054807000002c141494441c508959001c1d0b088440c1c2460 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 190394019 1250 190392769 190392779
    0x5030a030f1d0a06050408040503030a030204050901050405040803131110020a0203010515090403030b19080c0102070e060f010c081909080d0207060e0d0201090b040b040e0108070305060106080a09020a 88
    0x80ca01400d01030900303071404040c407404014102c4016448403000d4010107000100743c3e07426000d010001e0086404090a001c0003810351000c1014005600441e14007507141c0c1d09110510007a103605a126621960600041c4008078841d8800c0720380240c170504101420342c1c058140b10b0807100c0c40c010b80c075030409410629100145d40c04101c006101e80b08030024040354880c07066890300a4151048240d000301014003107030019001c1c0d48200d82150002c0d008500c4e214891039419451388050344000290b0b00110200c01c499a030621140f0007030400b00e030b0384078051f00b0034402003020f0030681d0038914180300c5103d0f003400510100341d0694204801c20081e49070740c800e00c55002421090b035485244414411194002c1805c1d002083e4201a01c0e499565809594180001c015445030980d105a0502c020000b01181a000b40c5000340050304503941101c3d600c42c6040100c0806c150140d001c440160804103046c000030300b0114501e4111801494140441c0c1c03542a155030040c480110000d5200500440c0051 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 190395269 1250 190394019 190394021
    0x307030215070e100216090b1e03120a03090c090e0d0305090d0e0a0302040204031a090a0807020d08160804050109060e0f0103020319140103030807050c0c06030a02070804080a0c08031201030f0f05030a03 89
    0x10348c001c419112554002c0c000383d403041030782500c0100c05a141d08140c2c0364200911235100500742d80406458041a211041e494115048040e90030002865890704040d00a010003084050b035801d0440c0b80801845ca81420040d03102e0000411160802052504640c16940c032114038101442d0001c108540c0c417075480c60443c070f0780b503814020308041200e10800030b9441d03c00440c0010b01c26402a50750380c0340415a0f403c04c2030740e0003001c0c01124600c0040c840340d11040115041010388030711900150380d4031824000050180c1d0210741c002c1080004c074100348001a22000000b8941034401e0801580343d07120f000e04000504c94607406103180ca07190820384200d03002c111140904823802030320703206441d8598080440e090b2103100605141907000c0c03d441c0141d414200000c5034459490580107040c020265a903508a50051740216400d0388200f4640c42400250f403414002401c2d0b00000f54581418243d03181181001480007400e5844541340c50000e101446482c82d803055800700a40350f44048402000e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 190396519 1250 190395269 190395281
    0x20403020a0f032402070b130209060a290705160501080c0f0313051e010b10020a15050a0207020603010b030a15180f02070b01080307030215070e10021609 68
    0x80e100d04400480081d03400070300041c807003c1d0380e0040900e071050070003080705000c4866640c20a000d9141e08010b0800030490241c10a8002d00e001000041c101505004000b003145014040078891000d1040c10044202c5000704c41a01c440308400d0900443e03130400c21003440303029040c0040c01c1c6026440d0120900e515007441d00b41600c009032280c60454548406161146c020412000302d100800c00200d07024130821000d90b001648140c00300e419922880c240d141c203001140308424140c0c0c1d12803a07200007a10b4018040a582415407008207174240b819207440e10007680300204d000f602c0743d031040410030240c2c40341c0480f5003040c0c018200ca684c9503590700d6080038607401201e42d51078061501071291030000000e10040111545052480e840c1d0a8030f118040c010081c0a551020f402d600700115000943c42c442c4040c001c0091324082c1d034468a190402a061490f89085180d080c691041006090758000c403040908901c01d980c1c20303802131040fa0082e403524400c100c0c0e501810000d901c0008030248150416 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 190397769 1250 190396519 190396523
    0xe19120b0a050702010207030f031808131703030603191104020a0504081e06013c08060901020a0c1203021201082a0f01050c03070c2408041106030702030408030d020403 74
    0x4000b01d0359014400c900302c2c0601d0343c0003030015800b0b1802c80d04452281e04407040100c190040000c408980b50b40b0881598828035070520045a056810000391003000045509c43c00014091491480c1010000b900c44028051104010010403503400601150803007801ca803901c00b43c030440d580d6203104000b40c0075801c41d10900c1e0451082c1c2c444401002250080780008080c500010310140c1d00348004484045040001d10404900419280070081710f034030202d0842540d2404000f40703c609206285091a00060000c04240e0042107000300e055480300c2c0b000803540d08241410300401e01408200d005e41b04601d4603c0e803103500d420020031200b5000c00e40d8410492200d60b074841d00030003071850405035000e80c1d004650003500843d00940a50080000304019041101074034070f0030740030356248403880381180c000d2610080400d240203605c00f00c50701c0c0c2d40919980c030304103240300740f500703a540c04140c6840c042454020140400800e51a45c020400d45000d0041482030f642c9400008441c0c000941281c841 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 190399019 1250 190397769 190397771
    0x1212021303111c030e030a02060706020d0b0a18090204020d020703020c01350907030b1e1008061501051306051c110f0a090302060a0e030714010e19120b0a 68
    0x10b803192800000d050380e00846203c6007a00044551400d46190541d4401d40d6018042c000c08600180e41e030b000144030052150000580b071f02e10341103403d000c03281c60760050b6016024144041c085164980d614108200b0350401c007140e00d001074404100a03020b00911445014000b15140c010140c02248280c1c1583e000c0e1f89103030b1066030512040c0c07109901c0d002d004c8101e00c08100e0030b84280703107911441a0300941e242c00302c17101282e40c1d84d110502c0c5001202c0f14894041203100c0907000503401c400d02500056551070410b5024145a4a9500d0f403070080d01610000c808444600c0c4a0390080c1c003991400084900201e80700703a55103034044c1080e408208003946090b04a40800981074070740c46252942541140c9182c00c120307004c24143c00c41c0d0700c000628010f011345d813000040140d0f42ca100400328a6146d42c5c0e4264840c4500702414649005d0760410300c6c1b8505203000e01031950341d221a19900541c011039044032401c094901c480c00d90070494001412000710501080248010380e41c103e40104600c2c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 190400269 1250 190399019 190399043
    0x60c02010c020c011209021c0305030115020c0f041802090a0605040e150403080403030f1805010c03050108060705070f0c090209090a060b0906071505040309050f010e06071212021303 80
    0x108076142c483c0c080701d55012030400410b000314074503203912900d020b5202400600e04501103841c09841405d1040d402c82c0010700020061003082d0a101c01c185109030390340000c01e1035941c4540002e2010942c1c100d4075014a03510241054101c0f0744503190412160050819299401d0610154000c4c00d0f0034081c01c0c0c081d60a044288a0390035002502c5008100c00f4069030005481f16981240c00401c0500240c00301512601d150b441c4e88024420b20200c1d5424140b102c0180e01c0d00c0c9401b500b0740794607840f0a800e00d4a003000410a40c40081006a40081e0302d14004c1d58614041ca000319154a6003074003e018a06200000704418080342e000307001c01902202c20b241d1b00da0b5810080c80c150b80c1c85000d08001e41c0c5040c0054115414584050029030388900422034000c0305d00f1600c4411514111021750004414032000c01407402e001e05003241d43c0301c003883c0103406490603030301150891103840002408140044c401590b19486096103c04144600703409640d038440c203403004200341410380026520444003203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 190401519 1250 190400269 190400291
    0x708072f0705060712051b0f070e0a0e12091203030109020307111f0b0f12072d0b1605100b0a06030204060804110406050a0f0e0108030c07090e01060f03060c0201 71
    0xf0166410143d0103118560184036106088645030044030002c00d81841c00399826216020070301c520100054048010070401d89040740707a100e1040301410354003c144c90190020702d03202004c24505100b0322101c0b21907a941103100e010800740b500b06039000d1b82c070780000f00c000314202042d5002180208420f81d21b03102d43e042c0d40c2c0007164172081c1d95a20003501d600d001c0c902084048494001c0c0c2080a4010030364a03210344898082528544903035a4680c90390000581800404580080014407600001340c1c1d00e402c0826000d02c8000f42045d0140c00300103140440c40e80c115501544402d9800307a441815244408200c00008003d011a04aa00d101d0701d0700c5900032070042d12078400c2e2821580d02d55504036094440341ca0301c080e5182d003540403640080d01d072035000c1101d480344160783c0300038440c4800c1404160300d0f2120b501e03011203068000b0802a003080200b2142848001800d0003520006080000c0c0306049900c020f004140641c490503c14014090000c288070199000300c88241f0035400900c01e0b8a604 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 190402769 1250 190401519 190401529
    0x17011406011701030605070912031e0306050d030c150e1b09150402071a090d11160312020f070314060906060913030302041a04050a06050702090708072f0705 69
    0x680005200b01ca0b140c01000070071031540246401500c9424101806900d400005a486088600c02d03004180e0202080c03099240d500d0a00107000388510302000400e0034030b400280c2803802440003070200300303001c4c8187c418446c05841c40f100405c0c200f2410400c1d19030186400707403248107006010100c6041c6860078011401c0c0340e4610340c81090720307010196002180c0c00422000b5008207400b5984c1c1d540c000c20002e05400c00c40e1407180560f00010060100d8aa01c40008020807281c1880da101034002d8103441140c01c10001d41f100c1580c3e88100710100ca0100e00b802240b500d541014052014405c8110002c240401d103003203218110741032304c00da81c61035031244001640c841d0182d0720f40741c00540380400148144019042000e0702882864003500d425600d00040c0303040c1001d0129141ca21000240030401c47c6007008a5000804860500741e01340f000075000600c050b2001030840c014041c003000000c040510400403029400c0321241e446000c14040115050040885400b5440e00d100e1940041014030744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 190404019 1250 190402769 190402787
    0x9060f01060809060a0207140d0e1915030507120c050306120c010c08090d061401050f0d0812101206090510110405060a0216090b130203090a0209060a1701140601 71
    0x2120f0001c004c82c2c1c035003e2000d4020340c00340c1000d90b88020017050196400509101c000603803003680d5038030400e00000d102002070095030030081c43c490303888460f402c00c50302030100902d50940400d0b080009641d60b51032030695080c1d00b0003a00013505423806248140994010016500070102078a0100e048410748d00a00d41c0d8951443c020303070206040b403041d2000242c08000a009104010f01710241c0600b507552100f040d54561100501001400001405903050000241010303a074100d0b00b454031031065851301c4500e8402c941041a6021094001494241c2205821001401582d0710744641010b5030170b1034002000800401c440e14000d000b00c4c40003541181c0198041c0c0380d04000050b203024908401c006841d4085d03000003040d40951f00e030045000c641d41d041100100821500840c1c0030760b0103010840c54410391700c08039690901c1803081c80002d4100156a4202da0b905580401d0980c540350002603101c41c4a5200340c04003034020303620310907005064104100c5018202c030704000c00d4854800556490791 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 190405269 1250 190404019 190404031
    0x150503091f021902030903010e0a0b040b04020f06071a100f0501120f050705070c05011d040506040f0203090106030308061203030f1306020d0902031b031c03020c030309060f010608 79
    0x30041d00c2409030745815204040e0300d181d81c100700518011290b004010100121a64080545c1000c15041000c0c1020302030900e1000101014120039001c0365910303e02c690001e44094590740f001000641103481d07a0300809403c0c4801040651241d060b854a9a50000c0e44510007042040280c0480c240c1c612010900c4207545181d8205d81807a030400004582c03481c52066102c12880d180c2c03407514103e20881c802c1030700a501a56440341d60f410b00d03051441c8200e60980c407841c10044104401d80c516000f864100c04c221004584c00700d042e0303c50758000ba0140040e42426a050761002080c05132030340055200314112b038441c0e01d450540e603590000300054941c0c01410714859410800010306a40d43c20b10005500092045203400b8007000c544400080743c000740c1e10313400d44958500b82d0b20305500d81000380320000c2d80c4a644c1072080b241242c000c41d840d018050000130141f455171802214a0303001c7d8040d14036983cac4040880e903c901d01000ba15070303180d2041e2040100d4458200012601c41c0c8651b03a4a80710b00c3d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 190406519 1250 190405269 190405273
    0x10e04060b160609020d12020d09060f030f140718051c02061b0a03030203011809150e03040e0a23090307030f0c02061902010f0b0a05130605030a0c15050309 69
    0x2004886858102e40d4401088400310303a50510040180eaa804003659114082c032540003070b03d41d5500340a483e007806102d180050061400c81004043e902c11000600ca105030f2901103070803610500b9090141c18030b0018010020707104010003a80903482404040545122074ec0b848000b9580c0041c000b28281c84408a00c42009140c824009820808014102c40c0c03806002d140c9441402d00c451400e007840d0100440000c1c0d00000108001414403403150080d048441c0c04002844581e0b0710328165809500320800300a80368400803001136014810f440081c00d10600203c0f0610300070bd40f5138010a6040c0c81320440404103600180d4030b202c0d04c212240304c0d00359100214503014803510141d95007985010140204017040c0c00d60001a20b800016080c44800076000c00c8000002200103030075152210040b641c11490800b2191665403103424a030308407401039441ca00c070107440c0a0030a000e400b00703030400c581511402d8688020000c901d5403200483d2980600b40040b00c4040d40100c49612091b504000c40d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 190407769 1250 190406519 190406527
    0xe0a060b030a05031b0714180c04050a03030302070b10061d030709090302030318030a09090e03071407081605090117010b1c03080f0c0a0804050313030f02010e04060b 73
    0x216290310200005000408903503080855a5840d40b650b0300c034074a07600020003695500c50004c4010410070780600343d05000481d02d40c038a030001c119000040414505e00ca0665000b051010240308100c6025110180011844940328200500030390310060003215a8240f4400141c040c0c1c40c503481000c1a12029903600e0305421500c000819500e180340d54442d0304d07000b103c400042c09d0245100e2200c1017440ba030065501c0303207050310515030900022030514010b90020881d01c0750076039100300c024098606101300010304480d0409070528501403144018001a9812816820410006055000c44460904a07802e071031508520070304040c0306204058106004100601084618000000550071980d0000400c440c0c1c100c0002c0840400b105d0702000800d01c480504181907010000701c2d8032103031a070514000790130184180e00b603e1243c030304280100803501002c127003081020710849540f024080c81800c0c150b0b8603402c1081c2224104042240400c103200c00e1074140341464000c00e0102e42784520b0942c10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 190409019 1250 190407769 190407773
    0x90607020c060a03060e010e0a0e1506040906201c020702060a0507020424060e041b140c0f010f05010801140610031103090705040b0603090619060b16060f0e0a 70
    0x120b900004201c0341816100c81c000303d0f51007403100011f4020075100b007414500307003400c20301401201d0198410840e5078108082481e441011105201d8001c001a100040e40352130b0750614038001d18021440f0b141e1554005d03e005503030402d501c040c0000628080440c00650024103a0004074403035544005e40101d418000e08000074041d0740036103484c0d4009440446c01485003800c00c042c0c0c1400d15900f0b03403154034001c014800c182e40302816100c1c400003501c041294a003c021035001c17401540d040a810860803000941222441d00140c400000304042201c3c100c17240f601030b8038080c1001300561940940390a0000070801d40502421035082d402281040c0c182c4c503610144110302c00002c01102c00e042d00d800e64501000b007003400551007150544054001c85062204210503a4041184184149000d10a0140a40d03020640325045000760000281042403503a803200508000e5100700360514001c03c8208220303803411002c8244500c81c000810480581e00380e101c0450703240e440b40c54038990003c100440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 190410269 1250 190409019 190409029
    0x19080a020415091b0810120f080f0c010b040c0e010c0b0711030406210905073605060a0e01270e0d0f111203060f0409120c0b090607020c 60
    0x141c460300b00c00e1280c48050f140e000070016100c800c00440100100d4221110a1030b0b846503505400195180b2500907803850840500c4044003020000750203641c45191030703030821003841c0c201c0c0c050f481340481a41d10382c02c1c2030f8040c50080ca180089a4026420320101d0300d04213100f000742ea24450b40507125622540b02c10740381c608050f02d00070519810f000340300801003060181000600010842d650350004c07004101000385441403e043c0c201d07a00c0c00c0c140130381040003c502041000c152681c000444d403c8000d00d011070b45842139101a001300c54900c0498130300d42990fa0f0380290384644000c1c0c81030315003d540e03810320312001e20b801d204100b80484030021420165460a284000f40c07240c082c404182c1003e0741d1160390a240194103584003003038225604101043d00010321034000e40000c00500702e029505680440d0a00c030042c04980708107201411800345a032603074882068190840c40345c00290f002500301400c0c2e80c00c07a000540f41240c0b0f0fa000101d10a00001c1d01c14440c1116030f0190581d80c0d484410f110b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 190411519 1250 190410269 190410281
    0x702190602090d0c09020a020c1203071704030b15090f04032c060301270902030c0402091f08011a04030215030c19030605270705091309050c19080a0204 67
    0xa6800032000718040046000040a2000f600203217000613912400c004010340351030700c40b602c124040c0c500440d004c0051000442034890440d00507503d42e1060b001c0b0591003109224a410041041d0342c4003081c8006030101c1c01c2c2110300b84000340d4600074140c55000c1030078400c203404c403002000907000000c40382405258040d00c1d502c81826000140600d40044001006a0000d80101081444880341d60070306003d81490309035019640340c020130480c002a004a40c840d40706031076140c0501d80000d52443e140d21145103030b0f06048021034402569a408000003441e601081c0314103211100401c21041107040d11404880403240d004041d405029186448910103800040003080f68407810321408804840d05403201d5800c104079500090032a06200400500754209204c842e1000d50043c03860b080805000480c9402000303a0a0503903c940c0c1e0707140018241d00f034010002280c0c2d82400d810504100300011b43d58a698030843e0304901c00c1010404003151440140700c0d0821580c40f49444102608003039000c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 190412769 1250 190411519 190411537
    0xb180f030f06041505010e070909020a110102120402011202040f050d05010b0a030c150503010b090d0611041e08010504031209050c090f040507060302031314010209030619050702190602 81
    0x244003074201d0032003201d040001c22a0140c0d250881034940c150040e0352885014058290442c01ea481401d00320402401100303113000c5d003190310b40e0004200203168014a00380c0d42c40720505001355629031141c00c081c94a0038086e501280440c40a45081480841c5c40c000d03582696540404001054501010420480a040d6041d40c82d5541c070564010551104a02c68010310b0107003a01c415000d15141f48564505500c0e420501001001d00050102c81510707000ca80d1800c43c1100d88156400082c203000c1c00602c05200100084000050001002e0176800600c840c860001d841c4141d50540d511200740c00d85400326401000a003564042c2c00600c0c040e640003511032030040b070403030380c500005c40080303a1403010a681140030034200074100302c200501000500041c00d2503141c19821410100208a00c0a4488074010a4401306000000b00c0c84030940c15a0078803c0001c04031152420103011000880141440342211141480c0c000b540890000400e20803004150b50160181c1c041a29160000c0d0400c0d458 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 190414019 1250 190412769 190412773
    0x9011a0f07021f0206280915051e18030708130e01060e030606030705011e141b0d02010c050405010c020f0909010b030d17062808010f060b180f03 64
    0x203881c05a2030703001803040964020000c102c1c8074901c2c1c0c400640340c034030010710807030792404c11a46020002c500300d076010341260020100400c03800d0007442d051001c24880c020408596142104010708002038054001d50004080c26049444c1c41d14103842c84404001e280800050f8410050034001545800c0200324207020700d060301c5a070a8a40315920740c0e0b2103082e07201d038001840302001c080751071a09000464201d8012002004031302c0c6850b00181c40f280030f0a0307042595113521000c0e4141f580c060b0030788520404201440907514071545040c000c00c00c15264404030239104060b06618464014410311101640342d89507107040625250045900300d10b2803c1c22a048980b8128070911a114081004d0140051800100707912034208285880c1c02d100007500420070501c5510504030740000c0b42c1194000405891070700650001e18000c01c03108042440e000010450900300007904801035100000f0413512030018060560358020440d00c030f00884000c502400c442c59210380c082c0c54208980184081d014003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 190415269 1250 190414019 190414027
    0xc090602060c0703080c0c030d090b06090603070302060903010b030703060914070e0a02030c0705030a08070e031203040b0603010603021806011e1b0203010e12033106020c0a0f0f030305010509011a0f 87
    0x41f9140c10754122900100c10341c0c1d240d103680c00405c40c010601c01c0d0b101c4001e441d042900d01c1d02ca400650341e00494800a0700414002403507070750b80d840c00e40065042040150885003401c4e52468008000c041010003a10120341400708884007490200d25a000c86020180c240501d88881d01d947e0300035071000d8021405a4400c0200030000780c402e002520400840f501c500403e86080740020b0030920300c141740d5a1107904002419100c400c8907205030303604240c00501d000c01c15030b40e07000407070300600b00340d00f001c0c3d4880002d21103c242d0750f28041189118070020383e5010421900f000a0b0b211555a90300c03040f020a850000221b0402190041c2c091400d00050010842c559034682a5080120740341c0344141e041800000c0000c0c1c550741c4c0b812410a218003140010404007544280340b9113180160005103c1d0340c00258010f40c512042009260841e04292108d00c1c60b003c83c984a0544081d480c4200c0109003058000241713464810300440c102c1e0780018110104926290151002c0d52000c1c0210016400c02c6c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 190416519 1250 190415269 190415287
    0x906070b0702030d090308060307090e0304030308100807080d0311130e062d1c080306010c06020f0a08040308100302030c15041e031a060d0618150c090602060c0703080c 74
    0x201410150900035190240123060020074076042c0b00c544d412204030740c0d0a040480c900d60034000211401c503605840c0084082e00c48282c0c502e004c2242d50702a090034413401c2c8010407011400314840c0c0300e210003501e0170040c0d41205806141c1502481e02c5e54801480c4290081004441c000c004503445039009140e00284441059010203501c1c0010495500d0103917154000c1641c10300c00041c0000d1410580d6200840d80150307541c004c00d1000410940c10006c07407184000421040b90165036100000484040c2c80c1e041c443ca008084003422038041d00002c0c01c1340301203034019000c9003500d000e403900503000e4010110200e0900c100360f40d14000e201304e00304041000242512154079202d01e04141c11500300400b6156050013015412460340c486011403003c0c0a000c096030781d000c280004140c0c015070105031401d01090241180742c19a8020300006108010101c40c514141c0c429070840c0300c40c0d100c89500c192103440c202d0b500d141c111a04440e050b0300f0400c00e400b085c0601c1d1240c5d03018616200182ca800c503e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 190417769 1250 190416519 190416521
    0xf0204050a0608070e041e02060412110418030f0f1b0503030402030f030f0301120c0905100510020a0218130812040c14130b131a0301050c0906070b0702030d 69
    0x841d480004682d56840034803038039805015840003454000304040050400ea251b0a44112060340c00304079044090b40c1b440c0454641c3e0050390700421056120200b40c3c82c9a0500800500c84001054401d0b441c040318001d940a00e08100d600407a00755032903410141010380182e5001d90841d103543c0512003202e13542c90f2140450450a2501440391000c0c589900705403062514003c007698990320507800502c20706240b4220383c0301341d82c11664008900d04645200b0306040d4500401c50300402c3e00c103814002002411032652441008a4805450200d8100d990b040c00301c5e100c20340044020b51158924a01240c80000c2c074400c0da401c2600c03018221115400d0381c1d141d000552111411820103483c600c200010320481c0540030005191f00d03014000010420000991040e40030b84a61000c1070307544103034600702c0d21583c0ca1035410f02c0e8100401c02203d824000311030745106503c02c1c0c0e1807196080c08000b035076020b00c2405075410684060b040c1414121240d80c0e62050307140c000c101b00b085110904ca0112901e002d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 190419019 1250 190417769 190417771
    0x10030b0406180e0109020319060f020c030a020d05040f05040506031603030f02011a10031a091302030c18010324050403050304060b0102071a1803010606020105060a0e040b070c0f020405 81
    0x19411000d00c4280381c0362400c042e00c410300141e0415034075214170f040258030046480c42d0034182c201c0c2d0f140803c0c2c88503e003544c01400100406045284003182d20000003500100600820545400b26181c80c0e05a1000319198481c6000f21510510305039010040740c2801d4010540082008040d541c003000f140c40e54060307181e145e07441071b40001d030711405c54070050b81c081c46500d1840400c00000164009118041104801c411185034105aa01d58844118074080c4600f40070b40d401c0146541d4031800c10305140406181e11050980c0b00c0d01824144000519020f180c090b14421040e442c24a40c0e07103503441d800010301c2c10b82c0d0300001000783d030000d4022903030f000e105940c0302d10300c00d403100e40e140e0820b82080400c42d1091001c1d076040d940885814085803260028180c05601585078aa0f03650b68208100a00307202c0c0300701e070540c040d801c2c140c000ca510340c1c0640200f4400d10003654007600329652070345e4103c5030040644d0003a0080b0100301c08652000e1060f40d412020344d001c2c0049400011066002c1400c13030350 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 190420269 1250 190419019 190419029
    0x4030f0602071e020102190213062c0f011e031703190228090b0f0d0b0102060c0a05070816050a0c0501110616020703050f0106290910030b0406 63
    0x58001941400c0120750312040080610302c041c3c1c401104034540c0040c2d07451001b02e441c00c0640e403110903400c0443d030342c8804071501051214409d110030f9650b003d180c04400e82845c208404c1c80c080d5104030b81010800541039108810504c100402a480c6c5500e06040b03020290080800042410002c0b0100b0302090109e100300c07052440c200e13901e19081480044043c500400043d0541c010400440e141e0886102c038a0441c21030401208035502d81c10068030302640701e0f84594101c0130041500421014400054007940003404c07030502910800c0001262110402c1b5840c128403441800030401851040c030290074071030300c250340151802010764040000d0f0303882ea2070111210342c00003a00030b08205117180e070000144003e092030a40a60007045c00e41e2148801001d2900700408140d601c00460300c2040420015074000042d12000e0300050360090107050741c0c0c0105c42c2c00015200b03541488641c8a03151300c1c0c400002c0e04d0f0a5090084841c100b003900070b0400a064101622110204900ea855208200080c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 190421519 1250 190420269 190420271
    0x2c030a0926060702071a0412030327080c061501050d020304030302090607120306080105070e0f1c050a110f060307030213050a090b010201110405060906031e070e010e030a05030f0f04030f06 83
    0x1d031800502440307894800d400108181c0b01400100507420741d140600112301d0345230601041c980c080c010804407848040d8440c4e40c1890401c04954188020b82000780f200049113829a04541d84401a010b641c40b25075420034002030003044980707851349059010719002071180c6005850711a001000540e140c10248044d074610310000b5624840e01c0d01482000018100d900017402280b500c2ca1002e07218000b486030007070045031103114500d401e0340c1c4c0080f8611151034008485612080f0b030b0801541d508040c94040b00c0d5640d0009000d0300901d00950180320184001b000203240d596030002c204c0c040d40181c171481024600903100800d25542d108074500250400c40c0c5d0000743c400000e000242500c03401c641202050b10200400d11141d12028102c820900c4c1c01e58115540707807142c88114405111100e2000c484800c3c0c030062011140c3d000b0324080c15581c0c242d903502c0640700b4840030140c84005184005011351300803c0b80c66012115003014005034107444940c10b06160b6a5151012048800f000c126600c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 190422769 1250 190421519 190421533
    0x120f0c1e051216110f071404020706050a050103141912020a0b0a0e010b0d050a0210020a1e0303050c09090117030f07050601090c1809020f070203012c030a0926060702 73
    0x10300d81c0306844083c422100802880d8010071603c01d5a00d070720547c0218851143d100c05250007a485580446069961180041280c0e141c411401d40042c0000e01048840311f40c4142c22400104001034034020310342805092048080c49a55803074a110108030500c001e5002d440d0005006c110103590141c422088484080b40f8079041c800c01a0071a41d0031442207200d5840c4413030b2000455000584401c07032030b505981503401100f0800b000e914061040100420100780100c01120603843c443c403041c845407294409010301d440d5080c52200c280a00c1100755005156140100701803510001d42160304088407055a203030104421081c1c50700da01c002c00541e81903001c0001000781c00382034403c3c4a4a0421846c104c1c0001c204c882d20a01203032514807601ca04642c005c02d038000c2005421045580040d8018020001c440a90307d40304010303000f0311240c03441c180d03010425076550800030044800c01515903464101c250308106130b004552001c001c41c0c000b115406522400c0b0390008009075070260304585c00030845 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 190424019 1250 190422769 190422811
    0xe1009030e0103090b0612150916140609090406020d2316020a08130906030308060108062715040e07080f0a15020a030e030307120f0c1e0512 62
    0x74015050181504241c40d08124070702040e10890943d41241d01214468001d074460f00d403191501c0d42410a402541d102d2100340807920000188a00c01c004c03158094481e2180c0d104c8170b2501c4d44004001c601c0e04488200f00c2281075250250710701e82c5c004d111311b02c010f0820302080c0c1100221240e60000807584d820810342d4503542282c8048259010000300341000c9034068140c0001d413181e5144000800c070703007004100030600b501100581e002910041c201007042d140e690500800103e0241d44681c003062420000c10403908000b044c002261600b029500f40c2030150300c1840c001d041000700750100540c40da120322001c0e81d030b8901424900c500e1900082400e40d0800d90b225041186480c13044030749070700820380c9400107400803500040c07a0b5600c600040e101e1400840540292032584003d01c01404008208107006800170070104484000070410009403003154908000c980710340300600003048030609a820811520042d50803680c1003481c120f4102400c142d10860003240030366441c1d00c1c0024034400001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 190425269 1250 190424019 190424027
    0x215010b0c060a050c220b0d231014012a030207081605041a030706080a06050d0b060603060d060c0201050402092202090a11040b0c070b07240e100903 66
    0x2d040b00f2500303070800c00e6042c101003020a0307104051410b5643d46074200aa046c006420020704001c1c600100481ea448855041c100c0040c0a00340107a074040c035003201e209440740d500c1010503101d0078080300030400403420440e01c03000c1ea141c911800750420641c1800c0c0344d29052041d000b0303076070314116500e5003005480c5468041d0401ca081d40003040f459200204640340e60034001101e6085450580d0005a00c0f04140321401d540b00032200c0701ca4141c0302e81c1500145450b849100c291007003032019010000c9640341d034200104892031102c040c00d244a01e001007641c40c07034100e0046401242c001d00251800240780d5a50090f0354981c07521102507590f42c0b0400c800d6060418031150304c1400088041c0101c00428052102c0c000c480002034090011400020340401c4140e02040382c3c8000c5284403034541e0b070380706005003040e401980d1a10071341c010a80001289001d90058400d1203074060b513650090740301c80918282c0541944903040000d078580d1002d460120040c002d02080e03500c1103001049c20b112a043c0a4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 190426519 1250 190425269 190425271
    0x30606120115080c0f01020303070516020a0803030907051c03120213030c0b04030507060c08030415020f070b011a031b090102070302090c0915091c0807021c0b090d0e0d030215010b0c06 81
    0x5c1d041d90800c0003040303215070780b0408035481e042941c0844040c080e454004102c84013000d41007000c03240b0001050000041d00050700004642e01100e55100c0c0d100c4050084148140008004002c296842c90a000300c84498014008101000c03000c0454035a9070744400483d242c0591040707140c00c00014050041c0b0600b48400c078007514140c01d00e403111503516901c04516110081000c2c2c04807441c0c7c018040280c01d00e4046a0070030100c00801912507201e4101a610743da0203204d070082c40410038514040c19080c480560744666210030b840d0000000300c546020300c55000c00e40040c118022028040300507074580c0c11710340c014000403041c2515241d02c032090008010b02c1240f0f02003140c0e014007020005a84110305414408a840044cd25013000741c0f030540040c2c050f00c00005d601004c0151148051885030444580141c0288001c0c0e01030307192402c2c142c0d202e181110780400028410541040682400708140c500c0074407a1040381d080b0103041c5034040c46405c2c02e0304100c200c0c00c8001500116002d04120311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 190427769 1250 190426519 190426549
    0x2031b0310170307020a0519091a030f2d0c041104091508120a0527100e03070501052a0c0103140907050405180a05030712080402030606120115080c 65
    0x150f00c3c0c0302c6545c00050448060340b007110700c50048100000c00c1070b2102c4040d80c000705550b174070500000e8034000d00701c8100c1082000e0035010703100f81e8400403800ca000194154039022046076070600c00210038443c0030490310420f050241ea01c01d00c0404620780c1c0302e03841a5080f0441c1410116260f504020303916040d191f8203841030824003055403003400381d40d0010a804c440c4400b401a40340d50f42caa002d801b036607940210340c9403000c0218080700403103461145c9404440010011100840014849242074818600c0280c01c82c0d0994444182400702d540210001c007801c1c0d00105042c10450710a410314103c0c06901c2d05c400416800144110885507014014180707903560303c0400159915000210340c1c1c0e03503101482a03620407a164004100302d012609840c07001914036205480d030600f0b15041507a900d0340300110455289140031046035425102d0080c9500440d8001e02501e0340e038903160708010340007000ea5a10380495680f03083c28040030300c400c280c50004040d0000a804450a000108030f1241c20005007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 190429019 1250 190427769 190427773
    0x40501050406180b010b0c0c0607060c02010b01181401031820181605130e010501080a06030807030804111e0907050a02100903050909040f0b0604020a0c0602031b031017 74
    0xb6003c00590036001050560704055540c649034100f08540501d0503881c04a00358004000040c0321045c0825070b0400e040101058000780000b00c091801120703c6030a0f10030900c2c556520a0303090200842c403010640707540005140100e00640c0303000650810001440b412141c880320501c40e05e440c0c2501d400190501e0340202c440c40603401d00d005e56011075480042070981c0480031948100581401001520502d0010304c004134041511401240d403101001c0c051240071801c002c00094090085d40180c00569500c886102c4c148055507405031015600039008a031b1154540d41e0b106001e4941007000001c849606040e03540001c000070901c00000f40c0945500100300040194000464001440b8000140c14034800510710007d41001c4074240a80d070980ba80c0106e44030188802d200804180017030090094580303078025101e400400c800c070710034081f46002250304003c2031804115581c5c003443d402040c10361400300d0803a0310840f01681d948105e031300e2944017000e0743c420302c440d040c0c80c0c50780510b1180401c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 190430269 1250 190429019 190429061
    0x1150501050f0421050105280209010c02060304031101021908090c0904032006070807020c0d0521070206030705030708090105060918030d06080d020f03090901030f1a040501050406 79
    0x9600c009611542c000d40d91070303062103d190032550040004d008804d0350020020001410710100303ca5280b010380c030304103a0080b00c200090502241a1007180c0600c00161100341032884c1c030b40c0c28404250030040c003d9062200d12980d9008441e8280020049803140c03558041d0503441d5004054440b81c0b02a0868106501045101669031114565142c1280d014144171b11041242c0d071400e140c003400181002500e0241109100d075040e00f0854550140d21103130250342c0c0c1801c01c1c000380300c03042884000c00b40c41d50f0302402e500e910740340c20701d2080e020303c202125040e031528106802290140d407003520410f0001310004100401030368424040c1d500f00c0c103010000c1c012402c0420000e039140c01d0103003051600071124194a20940010030885000321191a410301811307589130455611600c01c580c09038058014030407094102c81e400700441d0b0f00d15000803e5940c00d40d0a544a840fa0001045801c4070783c01c1d01400400c5030460701c5080300d44507911600021400340b812b0315000040d40c19480c802006000100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 190431519 1250 190430269 190430287
    0x80901150b07020d02220b090c1806031914100e0c18040612030903050d030e060103080c0307150204091109010c200a06020307050706080c0d090c05040e0115050105 72
    0x1604581c0b80c10303012110b8400c01d81c42c3e800059110f0200b0301e104030140001c420101d075140d42e640c01403030240300304807400c0010380e4400d101c030602c1d4420b4066a4000401c9103080004900e0111b01035074004860025045281d130410701e00034200c940013424204503810220401140c845650b0700b9001400c1080711504947c1010791564099001d1030b24003002001c1906001c102507103d0758806001000003e5420340d54022a08003c0e004901501060f212030060f6494656261f02900030031103103811803401002d050b0710390388170152960001c003a040f001e03000c10000d800c0031070601522000004d241c010016900d502d081d042404072510b4444003a039140052284280c1603802840c0f040c10642c201e0003135070310890031285d05100e032610100c3e5541d010380010070115a007a80000500b04030303846407040302c100c207440e142c0030303680d890003103c1c0320400760070410141e00038102e150030801c0110700c65500084243d444200203002d886d005982c950304d030380d0f44442c48011008003111440041c0800e003841481e144040d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 190432769 1250 190431519 190431539
    0x6040609060f0507021806010206070305150607021f1e08010303141e03071106061801120809030109060212130309090c0203070f0b040c061e030e100c08090115 70
    0x24880d020038804611101400e02e401181141d05281d070050110494032500916520845816204a4014400c00000801e86030083c032507503001d440d210131390304c1c0148000c4041110580c080344040360000c910340300440e030000b82100d02e0000212071380c480c01030040049d8480c0c0d01c1220b04008410030040c600c1c00400110b50000c0300b04600c81148a005c56503142140c01017113842c0240b4000c5004484004104000c103a0312101e032440c040142001d441c40e64aa40d41003051050110701e201e003800b00100700401240002901d8104410702c1001c03201d040107102d400103421220070380c8007605d81c65000100151013502c1082b426900c142101401540009561002050011903000e942c11700e039074420301c0980e85030080080d14170721940003201050303c001d64a030241c05070b141a0790407550010b0340300c804208a4010352000c141a51702c001039031b0002543c65801ca0141994100c00a090b006602001c2c448025a01801266000f6070b26003c1c0ca6082c81820b060071548441004a49000c0d200801d01040c022 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 190434019 1250 190432769 190432787
    0x70206010605090405070c020d0305030a060801050105150c0f01090b04020406081f02090303071e1407060f0e3c040b0d06050402040b0909100501060806090f090f0a0c050906060406 79
    0x810713900010340780d4510320b050b90380c91002c0344082d41c050201d036842e4080590101c02140300784101042401419551b148003401e075007080c0240759100095001c203400c24006803029264202c010b0080b690b010700640174007030031501071003005d071020f5460104100550805010785001807408100130078819007410309450840c2084203828044079000a00e5605c903a404006030307042e007a0049443c800550f08000d80c1c120054884d40210340703040c1e049986040c5e680000c0b4452080310160b44655603001000d8000300c61211903190b486600950300700791203070a8040c44241241c0c0c100c3c21181d09801e200d456404039128403081075154413a909204d20515107486032140340c0d05442c1c0c07203400854103440e24400180502560065260098010020095109400138590b114242c0342401005966225001260b50000481c0c0c0e8541180e00c0e1004220b8040c0d28140140d070000044050700d820132810400c580c28100030710300942d10440c2d0140107006a103400c03800307141c010f402241c0080c5820b02e401809403c00ea5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 190435269 1250 190434019 190434037
    0xb1306060215220302031905071104051003110409120f0806040b010906050c010216080406080f01030807020910150302070c0f060f2d11102702010315060c0308070206010605 76
    0x20300400480130940200159012140340030110b200c000c0b060309005249030081034003035a080c01d12a1962180d0705203440790f90b00421090312204411821030311151011a00070f41040d0f0070550b6049421302050a48240380380a009030781e104024450b010340000c040701005130415101d2454040d520550360b0b003040c0142c04517203450800c26160b090a607000c900a024600c3c2e0741581c00701003105441008009030003882501c04644600c44940c4502c083d450285000b400000e10500c1c1c1005410007625102030701544c464666105036003c903480704841070b400d40384512603402003a0041480c20403c0703441c0c42c3c0070b00a4841020301e410010325200c07004001c00c0b40c403483c02062010b502190f41e4042400035110451180c0026181c044c0d01e000d12009006034003200020b00c10b405250790b900391509090040b14070601e418000611884200340313212810b42034090307089050669411001110409074003621004200305c1d240d48a03864045c0c00d0103452414010702e02e10464015100500c401030f004420b88400030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 190436519 1250 190435269 190435321
    0xa02031515040510030f1107170406051c1514040b09040203030d09020d080a0909050f13030513180204050a0b0c191104020c1e1f09060b1306060215 65
    0x1080009174000c0c04c000e085414094245983d054001084000501c0700b14424251a104950f400e10000a540554001c0b81e0010700d00f00007469001d400440c03103c00c40d0701c5141780007400c010400f03c0b0b04d44c10441c9a0004243c811500c01e4642c00d0302d0544100e0800c0f04050320410742502e0a035000075101d1181100c0002150340d241c101a00355140e88140904556005a0580d9101800c41000d0f0641240344200710b5607900740000602c1448000081a01901c41c003c00f03542c515003240e03000c0d1160303080004041031010141030001008046145005c92111100d00010382e5076003010f0a003c4041d100741c0102074400710800407140402030020307240c8080401d050303501c42d101c945454241c0300d00041c1e20f001a030041c00410403400c0c0d810b000c180302d0705004500681350540c00c0381c0c0d51002c1c0c6580c80d08104501c56545c0703243c0207a00075555003101040f2071041c6000201c002841002072408001d41003800c10030350307840c00e0601585404002d804d04025140c0108030003860051003004107200e050070022010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 190437769 1250 190436519 190436539
    0x1f08240a0902070c0501090305060a1a2812230106090207080903060f0601020a03050912030712080106030203060901050409021207270e0d08100e0a020315150405 71
    0x808044151101440001400c080c0c403590340d49246000b03500000403c1d2940c2d010a40c0005007503004500c80c0f0104c0e54080d000c0c100560306c1340c0c0350100802a17260002c015000c0d1408800840e500c1c440000f002205407070705600c19604240c00300504000c9a00042c06015202d100100441e9104008400c20b00c40b4021800051750181000b9015029952280d0011400461600d0801c864907028002146042d81220204d550301d0360360442042c81503901d140560085d005020100744142e0042c520703901d014140d503070040300350012545141e00020003a94000001c4070151807a03640050b8403030042040d031806504600b4080001215060180b10313542c49203070385140360303000c40d20760111a0440701300d824191381030316584203010800c501d012240c04009618041c3d4004140c0b04038420f00c0320a007401c1d0014400c1484e0590309035070340d48014210499602a004001400d0000300c000d4900c101100140581c80c0d05120030680103245680c00f41034407640030005040e180400c00c40546085960448640f090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 190439019 1250 190437769 190437811
    0x30f10060807060c1b030516051c080a0f020a02090423060919020d15020a02010e16170712030e0915100e04151d0c040305120901031b0305061f08 64
    0x10103241d50000300140280004101808d600c501d04a0482d402540d42005102d0500e000e0307490105007200042401e441400f000c4107207481840c50581a1134680101d031f41c290b50b08e400151031700070111811103251707030f403462a191500401600a031542c00300304004c2005080c00c03132000da240c42c0002d0020054254050302c0030103541e1400c03034801e403660b08180c0c8184106410b003401006544504004009903080644011023018000340d100041441d0a0b201440b481c2044403207039040034038074501102c0c0c1c0f144500c0815440c2e072210401c0c001d50f200781ca422030a50f08100c284003002e03d000b4100810307528111001007103130300c81c0b00ba0300d1100e4846150120b518644040000c0040002e00c101000c807070100080443e02500000e0141c1c2803180070341501c503003070341c580501040b030388180e000040c281d802010200200b032201101130035100c1c005040105202e04060310346103928200f00314400001e515070046c4000c0d400e0a002c1d80c824503403815922060480c03040009041d644000d450710f56100071904001d05 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 190440269 1250 190439019 190439063
    0x1404050a020d09031205060f061204020607050607030b0f120a0b07020f10050906060f03030d09020103091208061306080d11030405040606080103060516090509040f02030f10060807060c 81
    0x2c00c050704000420050000d401d00a2600062914030b01d40d003854400820060b00e000d0454449154000b4003c0d4607054400081181c1c0f02009402242c02c03480c140550070026009002c028851a069070380069049203c00800070310f41c50704a881c0e40100d10020752b5400c40c40f00420000c9455070000c18101c0035407105a003c925049103651940309a020f44040041658540e801c110f004441802c21144c071138880303000300820744a00100c4654540d1041000202c0013641e500070705416401418009991070683c1c46084403521034410301c8000804c9841040040d282c00000c01c860006500070401c5080e0a01291540d610301900c1c1140500101c8241e0b42d62188041040300c001d0300300035009106155452002514080b82030000b200e5a0741050001501241c55100c080f500012594503810f100f0704d084207000b84048054001d450401d4a0482e03100076032800c108510f0b030900020018261021390315030850803200c00390089181d60300300040803c4034070742c0b0515240c18690040c5d80142c2d9400e01d100200307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 190441519 1250 190440269 190440277
    0x1020703080f041a0301060207120c050405040f020117061320070b07020712030905090a02090a270902100f0c0c09020901030b060304031d03030706050a0c020f071404050a02 76
    0x100301c081d001524849069003840900111620006030010042c1c1101e01001c040c042402403500592051304108070389100c2c400305540b840e005041840c1d9817900e902c046820344d80201c5099402440c2c4c0b003880011941d0110b4002d40c0001308260680b0181400c000240000e4050342c00c10031200d03161320403001510302403203280b19801c0345c03011255520480c52921b110711403c01c4540710054000d885c0001200e407542c007030110f40740c0c0e0b0580e1a809514209003c001e500b03100500072864035a800d120f404c2c900d464421342c54001d82020340c1000b01f40d0081400401c032107102003482c0c4480e58103100e884030050f0ac031280468403c911509000700d05581d0070008480c5a6035018000e0004c0c013104400041401c81d940c01071658520aa03014800f10340d941d010300003030b44030655008000130910381c120134074000d181d0510200360400509892405c1d01503198032054402c06e640701d4910320b9803078511005640e010440ca03415542028080c000036881d183c401074214007d064500d00903925807001600d03000c0654112 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 190442769 1250 190441519 190441523
    0x29010203180906012d0207050303130b0307030b03010f090c0609080c0f0f18010e1305062e03052506050301090c0207121406070905030d0309020a05032e05010513020901020703 77
    0x5142542000e0300c41c10701e0745c0291540004d4001c1240c08202030402200304c985d800b07172902c108100c0f5850143c4d00080f82d44001c00d10801c0503680c58559902d580c1c28096505440d900304070110b1511003500b030031804071368264890303020301c0203225003000120b078081103c898000080381c0b050310030f004400125804149084d00c90364410f41c1d803285824002080c0302036a05a4000076500044c036950142e031002d445645584c050040da110310f00042402d2905070701c0c00303c601d20f00c0c4a402e0412107204048100c020785500101c500d071700541034409059081070103d0b408a040001c4c03007882e40b46484805055403106004104035161200200d9581034000c00c2958001c0444007100200341d412410312805092040017800c04d80c0c02020082760400d84500c045009444004002e008410300341d200036402011303400c000326080110751000080998044c00444a0390440d800841c0c0220f80d82400d410720031110001d48800113203810011722054462010b0042105034040f1b0040ea07500c0420b0050f483c2c0b414541c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 190444019 1250 190442769 190442807
    0x3010b040906090504020906100c140106170312070c080c0d0306050102060601020607140918090f100c02070b0304060e10020c010b0406030f0b070504092901020318090601 75
    0x159006008020001c5444092041240d503455142e410103481c42524060b500280e0b200c0460258a09203078066555481810b0000c0100f4107969808107802008000c040d40740d40d02d160030818450500b050795000310001c0c010b5480d00180741d03072001028101800042c01c12030303a0319654040004281c21540c145009000311303102c500400c200100540040d00070380d4010300511004c0384a550001034034074001d45003034441d040410307848042002540c001009680e03210384281d640518440b09407a04070702403410040031705003d00f4629159880e220b00c00c41740741042450006d816000a0340072620b803007500d080040995590f181c03410704078054041042104410700480c500e001c140c81c15a8010001c503000d010007030000d14a51010041102c80703d00c0f000d0801d9005103898000544403545055001d01941041818a13481b10b07170f0b0800320b4540000030168900104070001100c0505d040280b2004024402945004202d000032400c00046080040c006c0c004a03000c11216070240c02d151020705c41360342c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 190445269 1250 190444019 190444021
    0xc090a0807090515090907090b0f120c01020f060f010509151305060f101b1e030203030402130c120e0309041416030b03030a1d120d0e01030c0c14011103 67
    0x6121402081e082d15051590207494890091307a040c1000102d224140201c042c0420502d8511910042d10300c00d0034055200004041c20502a524604031702440a0950000c3c035442c84044006450716a04842903181c40d40150704004201c200b036500c0340d040d94826034203544240c84d905030b00a55000e09480c0184d0001403405c981d65802120344c030080c0728400848a00082c0480354083c013401d01e8402c40d00500043c0580c000155000002c410900114810014036a01c40321500c6040071034003031160100c0041c0c0000060200b1b48c54405808141060340b41020443d41c00881805050b00110f814500d88039900c80c1c17042d4101640030b0080c1d0b070421070080d1090080c00401d482142400342c048030b0b42d000c0d0012424824030818800e10506510310300280046150400001c01070b580343c038090031868858103014010980035203400c16000314000f000001001c00303070505e08025142c038038841c000d24100341c43c0101310208254052000c400480d00b03d0120702c00d10310719514a50140ca09581c80c0441f04034000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 190446519 1250 190445269 190445279
    0x40608010c090506040f03030e0f0301140405010b09060d1b09021603030608031218100c03020c150601140f040527070306181815020408160503060c090a0807 69
    0x34001040d03a860a54801c9001a1500e04124030f60045006d40401c07103184240520010703008080065003841c0c020090916404150300080c03c0d240c400c1124030310120306005110410409016085051000f2202120b051600318003040c840707851160042c220f4502069184001400648400c015010b0600159580c1d90f665414440200401ca000c0700040d1800d00c002a110710040140e8080880d00a640303d55034032000c00296510740141c620b221107014a1001c07442c00003151041409402040e14003603120700121141504000d01881a070225240401c1003208c1603034040104028080b120902646034900881801c11134040c075041070381c200e180c1140019001d80500207a20f0b230b00c0381e16045190203a0321134000f1015600035100d42a5030b80586581440f80340085d4000311071541d60440b54900d0360355640c5415202d001504440c6111942c00101400500418083c00d0050105103042080441c50503020958801000b800c1103c40030b4045082200c5540304034036500208000700848810549503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 190447769 1250 190446519 190446521
    0x305070f110a0803030c04120302120c01050a060801090302060417042d240f030905060a1508030406050f030703060312090e070e060904050a0f020706020301081522020102070504060801 81
    0x140c0161242c1522840003c120780c00104891180750807120082c10310340740448603d42d036010428200c0c02d40c000c2c1d503071510200810740d000d005401035400004c00c1d94142021400110743d040d4000000c50390524842030042074000812031740050348100c10400501e4030041c100c1860080350004070381c210ac020319040c0c24280c141cbc0c2d1510041b05030b8440e448080c3d51201251865214218031528190326415012210b500405425001011600780800c81c600507079181c07800d140045400103802035031030740216440d801c80100710000d441000010f528003420300c10094024090381c90006143c5000100040c07040384a50060401140d1084203a29080c820000c0641031f075246001d020050718444002882030351280010303003962a0081c04803440c201c440782c2400081c10700202000902600c1d000710720183c88061005051060240400580f2541084131b00c9060801481031b02010030f8040c1d041c403413074020904104065404100c8100c006481038070042c1e0500d10341c1c1c1d10440c1c0c4a40b9041c40050b4036001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 190449019 1250 190447769 190447793
    0x30403120605040c0c47090c0a0b0d0f050a0e070609050f0909011404030206190615050a030b060a0f090911040509040f080a05040602010c090602030322050706091e0b030703090305070f 81
    0x80c4407010300151f9518081a0396001c4140307c06601c41444030082102008000003404070b40c059420114800100c48100d23001d444042d80e050007215519600c0000e00c2e6821321114020702124070b800030035107142800240d880405030144901c40c1d1000c10120350008803d50055440c0358107502c0d616000d2600b800d000e502d5802c121810b8040c03110b0320140c90002c0c01d042c031514050782c00181164010341c0418000f1555500421481c805159581100000c11f6949502030b00882c00140d441c61a00e9503080c000409903803565000c0120b5604080d40d903500b807010304050740c2c191041600d0b44002d950f6a4103040e00c01c44440342d8080d00c3c1100016105201a074071800400603140d240d0001c0c8100b4a1481d8100c40d40d100074031401340140c000340040354001070312000b00c40b070b030019840712405082141e884184c100b4001d948040e000c510036140802030418550301071140000703584208900b45203001450800c6210007002d840815039590041e03001c2601450640382c1140d00319055054100081c5405005410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 190450269 1250 190449019 190449143
    0x503060a05040b0f01050a14040e1605040c0206130f1b03150e241018020705060916060c020639010b030307020f15030403120605040c0c 60
    0x148500080c8a41c4a101a040d040701d0002c2c051f000820719202c502503000c1c1c0201c10a075402502e80ba141100c0f4401001100c0c07100804107030300030110340f4050812040b81e03011810003040d074100c40100404005410f091007101a00a5100503005020f8030302040fa0380300800500001401001c404030034003211550002a0f01c100b408d040210180070742107203540d0701500304a2110751a40041b03512003451003011140c0c000c40c889141c040c1c4640c464090110158120143d00500c650100303046003400810005150041d80500140007035003036942e80000340080304c3c0a04400d00004a0b42041191a0001121054268503a503c203420511003004805103100810001d03d440c44205480d15110040c403401c206103c0c010f00442c500000d0790300340440001161040d6138413920400006020200c0e000096218074440da5810001041940e050811511340c1d410840c00b4516200607005210b41110540340d100b0303001001503400c00340300750840c0103845459600d0070b01800c4080e2106000011481d03084082d407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 190451519 1250 190450269 190450283
    0x90f06100603150509071404050604031a060901080607052b1d01060501050d1104120302070602010e0604020603010303050912071e0519060804080c0304030b060120071503060503060a0504 82
    0x107100b4a500200303c0040c002d01c0d07031201e403520200342500e0041e840d64051410907030070241001e58410000e24250050b034025600c000700c507586400d4808180c1c201607400ba03402c880102141d418440c10315500c1e42d004001130709010001501c4044840c400d41030326000c54841c00700751090008003240102401c007020104508082d80d075440c560440040c01800b0680d501a501c441c1019600b041e61800390a00d0150414201810000403510600038034880c64554000e0b001040d2582c9003c2c2c0003800c58070f01007049921604400c050000694885046904403601460701503100c80c40c40e80044c61800300c002c0340a050303105d50170340000e146828000c40522039201c00c03c0103051075a2141405501032a200d003a0b01c00328814441400454001e10301d04d90018012881c0c0b81c1011a102030080c919030087d00103485e186146401c100ba075682c0204042040c0017140d4540750510340580c1510354034025030091000210024610b40c0715144640e2024000f45002000c48840d030034000c0c2c200e00200001ea60a903195 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 190452769 1250 190451519 190451531
    0x40504050c1b152724070e090c07030e03161802070807030302030417030a140106020a030c141204031101090602121c020c03030a06090b040b1503090f06100603 70
    0x11881c9182080b58092030041d0b940e5407060302c0044e9000d084001402d900340c107001e501c0040d04000243c0f40e16a07510104180355040c440c0003c08401c020000020080c0400d0003e0007610707000c2010740c002c1540203255032192030350700e401d072a81116200007071b0301407055072201500b101151a0381c0c4100c0c0ca002c058400340340d102204080036880b5211020f80744000030010200004c2c07007070b80110380c098028420710486100048d0310519030352081d40e010030b140d40c907484045000d00b4416869801010b041c002031500030003c0d80c000d010241040c40c00382005240401c413a40c102018442091740c0f51907031000c1ca65668481c030301980c5c64044d42040c680012040200070420320300008000421507440407086007082c803c00b440c43c0c03401000fa207980300155028027080b5071900007000954015408044003040709410001840d0890b0042a00203201c0d40c10705a800c01c540d280e107007100c036450720086441a600ea41d10b041c4e203403034020030079180601c600c529000c0001481c004034600c01079030644da41c28801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 190454019 1250 190452769 190452817
    0x206040606080a110907110706030b04050c09011e120c0512010501080106021509030d0c1d09060a03060b030f03071b05101710050901080d080f01030f080708040504050c 74
    0x2075541d003c1c40c014000c2c4e540c0d000d90384031803034011012a84007283e8546080b400180ea000503051500a038049000300340c407030000c0000d5140c1402070b241e000303003060f41e081d040c00740513030000300602510501b454080d03244c442c6110005104840c00100d0510100003844528100c142c000e086a1001c02a060170b590744400208856125180c100c0c100d60155005007004c0c030214090b10001140503107040e4032844200719554908082d40643c4a08101c291900c0c0d0080001c1d441c3c2603041d016840303005110f00e140b10304004040c4c1d1060401000d6a41102d40040d0b010003020209180047c1e2400e020110f1201048031010415003c844080f442d5441200c0c10b6156590010320000545030308580011840c5080368002e0f809800302140e511401c2800a4190030b036868012a078814000cbe08602e0098101c09001d80b0015004036490380c02601c0c500b80b84601d50303d540c91700070f645100c41000401c2014005501020300200c07405840240c003000307004104d1803c1c070380403215640e441400c0c8002004190050028 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 190455269 1250 190454019 190454023
    0x180106020606091305150a18031d0109120501051e04030c030f0c0c080708010e2803050f0f0a0e06130b1b01050a0902030c09091005060a03050607020604060608 70
    0x10496015400410064961500b0080820f100030461801c01c0361001009003ca0000c001020802c45900455032650400d90341007400c0d141c400c0348014810707000341c80070000250b0140c0c0c0c2c950005030420391503403626034100049038080b096501003401e5800d902d024409001040d80010f001c2c99110740780b00f001e001d200074242c0d1030308c00445014002c0703221295610003190045001d100503521502d0007540c238409030341d02c600000c0c005810540e0a940601c405000d4410240314150044c00c0680003003000c01c030b40c0d00c0d018800c07104540b143c5079a002d082c42da6008240c0140151307a48c2c500c0e0890340c607032206900c800d0b1501c85d401841d010380008045031144512403d00b902142c3c040269900032600d001d08007104a10503038080003040a50006804260107607500a100b024010744014001103282e01943c0101440c203080c1a08451040e6060001c0c400310100000d1250900543d000020a1543e1000e00040c3c180c0074a500142c600d0050404200d00180e01084291150f031203058200070f1a516115000e03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 190456519 1250 190455269 190455271
    0x4090309090e1006240c03090918020409030801080d0c020a0315020f0a0201090b07090302090a091b140a051504120f0206040602250b0a0503040f17070606140603040206130b0a0c0218 80
    0x80c7c04956240c105100403402500506041300440360801444115a80811300701c40d01c0d00e0f000d800194001005110740c05061204074401415840c24829440c000d40000b844038140340310003803000701d251020480410040d01941c1030b071a842940c107a200c000d02070b0301078007819401c038007103407820072160008805901070341104060f2034001c0c003610019620036011600916000005460200c080c100ba28041d081da0045180030b000104d50441601d00e103c011701c9000740309900481d10400542d04206400c8041c0c0c0151030440e10042c00c82c003440903050070412404441000040d410003000640410580e0300024941200c091030b005000100d600400a034948821a02420302020800c000181626105001564100c0c0c0600003070444141e05542d604a2940325007020000c200740070071000284030f120b104110040045204409102803101c0c00204188130042000b8410700780031a01021458045203c000500f1400b03410f180d4030b05030094042c0c400400100f04910407640000f0303045c0c071031014007911 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 190457769 1250 190456519 190456523
    0x109060f03020a0905090a0b01020c030f0319050c0d210e071823090f0a0b0c1b0114060312090f0d0f06020f0a080604090309090e1006240c 61
    0xd0011140c44903021000307503001c035540320104820300c0d801007070941e12000703424000d607802c840029030322000307a0001e0704003410384548074407039006070f5441000184040122140b02c074480301c2d103550f001000c220640340c9005901030141c2d58030540d201d0b40483d0360024103c440924a01050082c140355000710701054134407151403c0c03038927000590304111802030702c0300e002000d11980d040400c0c0e11444503405640720340c2c0c00c442d0110249010b400c1c400624000e000b001c038111440d07405442c001000e41c503590361924015010518030500001c0300042c4002c08110724488c090484002c1c0030000711400e4040176190103480440c030900801025003d5200c403602150039500d005001d2550552201041003079100c50300200b526202a88410a000125070b0b20040180148200c2203680700d40c9d4564008045840003840c0b2801a89080080000b0941200d203040c210b4a018001041408541401c03e0400b1100251000464104403000c504180c2282400c4210000c141400300001c07819141162481707031300800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 190459019 1250 190457769 190457777
    0x4021509130c0c02040218040b1806010503070c08070b040b1e0a090c0e10060e0a08030d0e07091509240317040e040b0604050108070b0d050402030c0d031d010906 71
    0x41025050300c1c0360007281000c030260410240c010303042d40101c0c0684c1e0003443d88201500c400030038100c05203490720490f241e12034241e0b6500241d800381400a0303000c0c00050800d81c1444070110008045522980b480e21210780d200d00c3c40758449000e8504018a007005840c00c48050040c980024544500c44407000c202020301e915405040e214803d01000230704000b00240d4148600c192701007825040070101d640200ca0308118881c01300d01c1c040d0014050b0315400842e51090940700340c104480a0b0020035945040b480038400540040c607684040e00e0800c0c140d0010080504003c0c83e030090001c2c1d40600f1003111140d0b2001d11010002203204400790050307540340d1070305c261650801e00110b00c0d03202c0002c00101501456901d441c4e100c151302251500100c80c12505064820100a5681042d00610340181091130003801e5560400c1070361106030280b410b04021681d40d07240020305555040200204461025106049503005802c00030503042401d6451030940c1c80c01a08050154030034003400c1c003103401302d541e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 190460269 1250 190459019 190459039
    0x903080c13030b090304050316061107030305030f0a0b040c05041e0e19150b18151c0f0c020303042303090907021501060f0f0203070b01030b06030a060e0604021509 72
    0xc0c5483c40d5000107000011a48018030011540392010001d103448041006100b182d4146801001401034000000602d101c0e08443c90070400207800401b0f50b50046250b200140080d51080208801041403a086a51040c104014815403640000c000c0081d03985c10440200760b03062244069000410911604c652200309500046640d036082910000e02e0724801c0012409030320f03201c608900811150084980302d032002440c640c1030f0048800c20a50350200b51390700e24030007101110f0b400c02c42c0640c20700c02c01003407608100b0360807003680c680c0300320082c0d205100c0422030040b070444d00030354940003114201c1c0d000c9410700a1002041c5501d24003030801d00054001d610300980030040c40360381c01c0302400380029031240c0c10240c80d8800b01e500c2e159011304559a0381003424542c0c081c00908210002d8821001c0d504104910030215452101903030640c4d030402a650f00d10745138040880e1500301d0168015003000d203443c0b10090a0003010a000d4000e6000320349a071504030300c00e00d5a0318a40b02d245252603000d141d400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 190461519 1250 190460269 190460273
    0x105190e011502030d0f15050429151303020117100b0904180311070b0903210f041206061706070804020118060203070606080102070c0b030411130903080c1303 70
    0x1610b020380b4a14902c19603040070031801c207090955840b07013405820a42c4a1400c1c1e0010303c40da000a100801c4121f0b418044448000303041446643c0054610407501010380c00361030561104000c009000d184490099510415a18250300959440c00100c0c006182c01d8100e0b98290328081d0040e00a201c01942440c3e15482e09920000381d902c18107465400c152196030f040c0714540302d6800c00111901a0b02c40a180e80e89611f01d041c189031042d0030000d20200300740b014030141e40300020086e00117074800c000a2610f060840c0540480d00801040c02a664000200440e003a450380d0b549241c1d462007800b042c0140398842386020100c11500b4030208041d070011000441c150b00c2200000c0c0c00600604010b84507904540c1d540454291760740042015910000c1e0090030455036104480003880079400841c1000041c1da01d01120b6400c0e03205040b05100007101040c01d200303001d030740702e64200307030080030100070031441c802a00240849000980214098a0026a18401d1501102c035445880708170020300606607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 190462769 1250 190461519 190461539
    0x312030703090f0525120215040801050c18010906121e11180d080708070501020f070c030b0906040b01051311120907060504120b060d0203150105190e01 67
    0x100000304241e21811940c000c6110005901c3c00b080c000c002070101d52400308040b00040070440302d404024844490101b14910305100340d086a6a4100c0e0703200e1800240403242071060040b0782102c103442d4a040180311080341d1030b2000300318240440d8003194110300c1e04401034031003409511a0101044d030b201420b003c000300c036502440288540349605480044485446011201400e0a50b2847c50002400f80a84807001322906103628ac100d0f40865010710315a140b40d8a8003c1c3c84005000000200b000400c20000b03405481c2c100c0000314140742c03103050500b0244041300040c0b00a8501c81d40c540041982d03c500400c006103d2904001004030503440d10342800780444030003015888156494408143c85a900401812011034407000f61100c0e0800c85080c9007003160940c802c0090160812007000341d4140c0540007105290410210803c036603a01002c02d24070011910000e516018040c12030381c40210080545040e902c080c1c903101c0c641c1810303081144243c40d060050705201c3c02e0180040010382c0c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 190464019 1250 190462769 190462771
    0x10b0d0f020706090302010501090e03040b0a2006070206010e07020f0d050f0f0f04050a051f180e09060f011a0f0702010e0d050a050d03021c0e160602060603100605031203 75
    0x10340320300145060540d40700c4a08a46600d40d0850060f5180d2004000307000f0540111000c40309550051460145007408180c80c41c4134102040050003400c00035482d00024940350300303c0d1141b424080d14114030300f101c0c009498400034010260300d000403101084803d0b00c0091850001d4480e2401408050440701c0280c03101c1d00008061003c3c44010004a51480200406004540c68001001e510345080c103040051003400b0b504078030300588410310040c0313182d004914001d140c901c0a04002201013200d90500c9050180c940009003402e05000a1050040f00011010b20500500e110f04111766250814140b4521031120044002d210600445020f50b41090040c000c0340d01c141801403400c0340440115101c07800101040c0c6042d0000004482031000034070000700300441c9886c0441c540b6070002c060002c4507200020402000380d880c14650720490080020345031424405482000841c0d03a0440295903000132503089000340a180702501201d011801181c0c03c2ea8402400f41004e00f0724144c0c0c1c00c0c51504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 190465269 1250 190464019 190464041
    0x909060f0a1a03040c080a0b0109200a0c050d030e0a03050d0b0a080d0e01140f0a0e21120327030904020403060207021918020c0109080415080c03010b0d 67
    0x10080e60009002c20300584400441d403010140b69101c1c5002e0a14410308a500c0d0301c5007885801c40c10340310b0b00292482d001c55054400c030391800941001402001ca42440c416011105141070006c0c0c1c1038000b07074020140a40007441082210803400c00c40d001101070340c1d0140c000b4000da601841c9200c001078024001341042c047c003810005007869404000400c100001d600000580d00301140180096500016007150b5410030b00344032525110001042540344600c2d402000440707004241001300754030850105d1100d5800800404403402c1104880c0b864001000c42540e40744100c200445402c4407410035648074004001c03a41c0803175101c840040b440c4030304090300300840d400b007004440455035032440500042c5005110060b107991003407060203035031000d0601d50a500c1608150800400229056403815032003d0000942c03035818080d0740d20301420075680010b05080d40418041074104a124400800441c2030756a42c51a40345c1020300603042c442800b90615502c820401100780300d00340c2d00301c03904400d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 190466519 1250 190465269 190465279
    0x5180d050c01120f2408010b10050705010905330402030c1c0c03030918021c020f0412120306050904050a0303051513050a0b0604051e1f030903140909060f 68
    0x1080024200086400e81e5100218201da81e12485d051113505600d15809400e03004020004a80b101c4006918490b002c1440c030104200001c070b280401c0000e4000394155903001080719440d48007114207070702681107518150f002c1c03651070801c40885820307242c4d05805250042c000d4286d26025605010f1028540c500300a08801101520b000003030004010b84010360290791860491810882c0b2480007410a00e000940d560050101c011180c1101e0b0f58140400c000c480e0041c4d413905580d00d420701e90700a540c000d01600b800d1158581c14010030100b20317038003103120b40e40030050292601c0070006442c3d02078801500b140c1c002c09080002900a41c46150054421225824001c48500006e0381c0343c00d40700904400161200248080b601090003400325030300007165843d080c141000b0106426141420000100c800001c40f40000ea85039900407802008108200d04103a0000c02c0006d00a040014011000104001c110840c4500b03008107071210300d617005007031400b9916a5000c00c0306058200001c15440303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 190467625 1106 190466519 190466531
    0xf0c03120a060e0a090c080708010f0c0201090b04080c03070212010b090f010b0f2a03120709050d060f0e01020a030911030106141c0c0605180d050c0112 67
    0xf00d0420b00001d05c0d6065820b101404002e2648242c546020b0480d02040c68501900302011100c403000c01032201c80302003030049080300c20f1034a0150040038020046800903012500810094450760200c030309051071900000e580f2081100114000c2e95032300c0c0358401d68200075100b00e60280340b202214401350700d8498581070a01c180c02851803103401c002100e0131000d01041d460450b03103c283c144481d840e1400341d885c554962069565400c4004070f0780000d20716034428151002640c0b40500103222503c1907a8610000c0c21f0031440101c0c00584510925181c2c0d4000d101420440c1c0c40c80d6400f080c1401c550500213012141034044a000340d060010a00013130059100360842c4400c00c7d2484902041005500e01e121121040018080d500003c8001103682c1e01001502c400c5142c03840d1550410042d4003080341d0750320310900050142d00034403401c040560081c8010482c07035544840100303079 = true := by decide +kernel

theorem cover : BRFrame.Cov 190287769 190467625 := by
  have h0 := BRFrame.cov_init 190287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 190287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 190287769 ≤ n) (h2 : n < 190467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
