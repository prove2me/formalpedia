-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0572
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:30:33.807986+00:00
-- url     : https://prove2.me/submissions/2bf289f3-8cac-4801-825b-deaf87e6e315

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 102697841 ≤ n < 102877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 102699091 1250 102697841 102697883
    0x70f0804020a051503010305060a090302030d240603050612010209010f0513030605010b07030f0519181e06180f0302010804050c03010c03020304020f01031a040c02150405030903061b0405060304 85
    0x45a0310403084d000c044010400c110b0204405031340100458424082c1c1585230780c1c041e550b4091210840700c0b9a0311114101102c8003a1648a50441d5070f40c004001d40395034446001d0014013041e10030303a000d098904051003030712b0350500803191403150603074844406250418086a15070042800300c10001c0c0381550000229617a0300a00b07000e08140c8803080e03500e01180c5800340101911810403001d0000500c6040d5844c9050020403030b10080e00d0500b41000712110303105449001c034507040300020205040902044008801035482039600c41e0301c0340c150028401403007400c2c8480c0c501c502c401d000d40c5a0000d00c01075101d10034a80d0401d105004607207862001c600004d0a441e2036030302c102d00281d404030401003540f0b000e03240354403008400c0c01c00b0008021101c010040b10700080440c0c5004a80301c85d0300c0403442d482084000c1003809400140303903481c1080e15046491342d1120050328403a114101c00304000c0110711481017000b07845500d4440c5400d282000384625504020421b0310402c150340044440140c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 102700341 1250 102699091 102699109
    0x180b06070302060106180f14060c0616020c010809072d03060c081f0b0a0912080d0c0813151103190e0a0b0c1e0a0f0206010b03070f0804020a05 63
    0x100c41d401500c1c03d0760501000510110030f07008451000801700300204100c10310000b02c1420b4680c00d061a26558500b000400e0b4644202c51040c0283d1081c203041100c0ca10200f00d009007040019400e80340702000f1080111482e010548240c42e0f40d4110701c1c000c0149141a083c1e101c44010581414402072281c0f002d4070340501c00640c402d603511034494010f00c0b41250b200403a9540f114004088113441e2210200d02e007141d600030b01a032450013400041d40d40300a8015000f9900406001c4502c00800da05442c0c002c001780c0200b05646680fa04254440041c607004544042c414000b0500b0f901940d02a9143d0505c0d8404230400051075560b904808410310814200841c410003120a4a0540205091a200486d90503c7e050708050304421030780d0002404075041140c2040c100103c0e1500d8200b1a01c481414012039020304c40c0c0340310001540782c2e44682150044454802d02d0b025200710340e0761100e83d407207103104c00c55000000440f10011500d003640920f03181034101c0d0000c2e148030b41840d222008075a03c0300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 102701591 1250 102700341 102700343
    0x9130b0a05010608070302070f0f0213060605120a0501030b28050906060112021309091e030c12030c1b061e0911030c0a05060a11190b07021501180b0607 67
    0x2900c5070014000540c100c2807058011440c0e1408500e00209500e80464440d01044018481e00c44042e90a00b03641d40d0108040420301005800c11031580c2d9032802801d680e00c600b0070001011000700000d1084800c40c0b00e583d048a402c1480745030b4903641c809400151032001041505000c00f450902ea111801901c2110300c50364040d802001c00c0d00700000007600c0e18050980154542d8010407000c05119154200350007103424075031010403c40003501d40b51401c0301100780441c84d180c035100192400d055006d555140341c0c40c020020040e158128480407029a903880c00034030702294580441200c2025084c2d04452054024800020400308020544541c0c164508a030440541ca40720b842c018015103174078141e01150110010720b90a500500452041c69861003541d10507000884c204c100386000700401172183d03022606503003240f07040d010795001203095110700340d0f001041c1e880000c20f0b6600004200c500c40d1154410010941e1901280d10b0b001260340236025001a200c00c0030280503241c07031024042d0f82e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 102702841 1250 102701591 102701611
    0x3080d1814060f0c0406030e030409020a03021e040803030708090c0904030f030c030621051002121b070f0b0a0608060108070303170403140901030605130f110703080609130b 76
    0x11004211410710b4480094640041ea60f2070105009442020340c08441c219082402c01003620000d51130820305600960307111609860000808116140d416402440046080300300152104e40c0000395062500031406045100d503c04c20220716454003800e038a992010307401003207071540c03000070b0003003000400161001c801103400c0079091034075543c25020301151000c0d40e143c20000310340f61100007411401c074410541028604540a803090140511400c044000d070903100790b60700c00501c0d42c050140c003000c5038400070030245840c2121465940c90101c1c0c4c21035400c882c008114005645882244110241c480c100701c41c1d48003400a860301d0244034940c000c00f00103004d8200b55103181800741c202c5244500078020314509074208000070703030408044145100b0b215040d9850300904c0005030003d25250b009154820341c03406058074900305542181a810b460280c0034801a244040320120500610300000c0c01310f159a80005c10505100e05281c0d40b10290b0b000514081c24151109000400c042d01d00c2c100f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 102704091 1250 102702841 102702863
    0x40603140a110607030e0d05030f0a0918060b1b0313090e010606030b030a060c0201020909011404060819020904020310050f010305070b0708040b2d0c1204080703080d18 74
    0xb807211024101c601000c0581d4201c0c50a103141d64000c0900138600c52542c0701d40b099074101400d118042003950603000c0e11100d200d83c0d501000501420280c402d00c82c44864800090b0503480800d0b00d0301440c1c00b1100801c1c0303160304041c129801e86c844904040c00c0c01025210500031071400e101210f00d030900610f001000000c0d002c1c4200d10039401d6554a40002040c5410300d2403078469034500044900050350415400608143c80c0c4808078003912888044a0f80102031400200d4581401c0042c5012204200c0702041a1955801072035150707000c0e0101c4006044040b2480b0000d82003952409500520040c00d0f40d0b288094028540204d44042c1e403001021000c21005004202080004401412141da01d2904006c1140c2e2004000d10942c045c020402c00089000d0300081e141016441104072135039851036041280040501d050340044820381903520502d60114443c1c09031340c081341c1c1070782c2034900501565400c544903450598840c403503a9904075910301c54206e00340d014441480c03031248100d00b1950 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 102705341 1250 102704091 102704093
    0xe0402031302090109020306060306060a020106080604080a020d0e030304050d020a03020307060e1207030206030606071a0a051603060b0d050408040e0c090f1c030e0a0306020c0102090909070303050a030902040603140a 95
    0xb4110160000161716204000744040c541e1340340152a070110381141c8183c1d076200319200403030141106038031900e06485007405020400c68080003070079071034446508940140400003012203403030841a9684ea01604100001c0c07001d402c00403520081e4a00103000160800d5496000c00e2920708282d00040000b035201d0302c80005440d00d40038900001c0a6040180401030030340e000110f0501c0040c00d00da20803d000110345040082076500620800382c20300018070300e8500a0001d074003030301003203500d045942e181d015500c080d94000e204140c02d4a402c074204508295002c10804000d2202500c1030394050028000040c41602c484421442010021045a00c03048180180300c82c43c03105511031031040d040a049051007a500d0707901e0041a6805140440c181108400400c03405280707504090001400002c076414580302c150000c03e080c0310241c407409005d603168414251106080d000090000300100102d00c03580e446900700540f51400200001551035403651901e00c080541c0302e21700c020b070304a80c003404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 102706591 1250 102705341 102705349
    0x711030d0f060506040e0c031b0a020d02010e070f0e071b0507090b010314130305270f011107030b060a050d03021b0406120b090a0b040c0e07090609090c0e0402031302 73
    0x1400606040c1c44c918107050a0000d50040c81000400d074429886010001496940000007241d4145240010a981d204030408000f51540b000040c01e101641c01c00740f00e4000c40f20002105805c0750000801d00c01f40c542081c110035282240503000703408010742000d6070700c443da104600320b03a0705621660003071035101c4c50304038004140c5003540706081c14545000c0c880b850b4900380c00301d040e600c20b10381c80c1c24415a1010346015640e42c084c10000f80f003541d01c14024012090000403041c0c03060041161880d107002444401181e07a81d803090b452821a420641c001c200044452106642042c0020310390382c0180d440d50080f0310f40401c01c040550050744600e0301d5541c200f00001c01c1e01c440c0042a07a05111082c140101d0748020929418000e0059081500040104805004507003003c2c5c0d0040070b00c01c85040900303103404485254060042c034507002a01060100c2e00503501c481c00c076095600d841c0602403030294400000c0c003c00305c0c40b1051000c008010865030703590780700840c4110100c500174a94080c681c0180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 102707841 1250 102706591 102706601
    0xd021e0307172d03042907110105010b04260c060a03050708070305010521030706020403060204060206010603050f16020309090103150c03020705150601050f0a09180c0c0b0711030d0f 80
    0x14402e1681841400d80d500850300d4116a442074010b0031040f103400c14a0700076401008824045104a1001014881d105600003c1c05040c1191235000703101ca80d884001c401034900c01d62040f5841e20402811110510601c100d589010002c41001c3e100310307003254801f0030140d038055101000001d5582c401c01c04c40982100720301e40c04c2003052500300400d6041601062040e14026400c3c014200503030926844410100200c0f06000c0d03210009545036980e0745000c0e0080d4116000c0e11015004460010032100e04c41c0c403404e403251442084524460301d803214501102d4030444420011400200011501d81d290b040e603590007107101c0d4009152901140802d0400c0352a5a1080030030103004000c2c1c00049000010403201c001032548808840b2744031040140d0791f502c51007244503030303590300403d0711003000340c10103200000c81d080740014211001841c030701141180c5d0341e100d0000125400c1003003940490a1011034070b034005078900780756205207182d0545c107166421803414071070815162410180d400f0500c4c000c1f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 102709091 1250 102707841 102707887
    0x1106160f0b0f04050a170c01020c010b09070c0c030609060f02070b0105030111041a0a0912050c03010510030b040f0602270348060a050703110d021e030717 68
    0xb8030405400d00b40d4030a1703110100c50802420b20302100b042074603589101c50440f0034844456000f15512280c0000c50b5001c1c103903107a003449c41a0f4038074000881103130040198003922684803d80480890650380e03040c0040c15101d00542d02e150f91001d2540d8081414401060f05078003a5015071071a41c0b401c810103003550400c4a100150120520042003010310032050400d001d040149040c1c1c03110240303981107801078400da01030103500c0800d8003180c041c8080030a50b4511041c05034001d0201d96680d21400c40075005900c40149005024000203000c540e030070811030005441007401600d000c80c05185074190140d140c00d40030202ea1b04d00d400401034a81000303034905402d640a020741039083c4541e8030a145440b9a0001d4020001c0312202c90101d080074888060005c0d0b00411480e2504803800f0010003a4100d03403000c80228415040300004214005008091000554001e01c01002900c070860038001442c08841c882d84000d001d6000042c0501250032140c3c104003510076103070800003221040342c1c006040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 102710341 1250 102709091 102709111
    0x2206120e0f1b0f0910090b010c020f0603040302210405090906070c12050d0609020d0b0a030c0b090f09010b07030815010219050a14010b01030608010212041106160f0b 73
    0x1c0c0000c64040c040740a4070390700e8090102c036491160100c003140c0d580654001c25580410500100500b071000c200d184400e03501100410000c032568140191000001c002010b5400b00060403240004e1804200441d44030384240f066803120360b0300d600c2102c4090514020442a088086000c0c400350a10102e100d41c491082c1008082c0c0f0f0900d5400030702549000da0b405400c0b4000c1c00b283c460300ca03001d20115a08071400c1c030804c1110709d03503403110000290091094135005d581880c00d60031a524016014405483c1c00406484040e45080c0c0704420070390060850176001880480788407c1503403000203c6008014554041d0f41d1210149001418007000a01000c2d41c1c00541850000342e980c00038809030b0b406900c03c440321005049040561629514030300c0144032040ba040515440401074200c0062001d0030380b010300142c0e803200d00640c241e0044003c0c600e8034002a4001038003003018809040314098020340160301d054001d6a1080c840035250b20181d524150414580c0100003000303490b9944502810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 102711591 1250 102710341 102710353
    0x708010f060e15060c100510060c02090a0213090e07030b0606030405030304030c030309020405151c11040506190906230108040609020102031303030801150f050304082206120e 77
    0x2204581002c0090306450202c00980d0300b0030718545078401100c25004010b4121502015090010f00281600311007415960089050005903103001e000d0480708940e008246185959411042d100250040e903a1100d00f520511400500300340709106503451510b0410241c0314090440c01d01d81510300019150074090ba40400402000c25004000e507500309525141815149045080031009003182c4040650301034a40741c1480154400da800030705080c1c0303090390180406003040501d0702110925920251001c1c030741050900341c80c50036902c11980000000c0803c50354001c04184001144881d81000007a69034600e010b1010034490070f41c180301400c0903180d1240074490f0100003005114090b0000f40501c1e180e000c0c84045a00074002d030f541c84050f61030703407042c029942d04009044000038850b400d41140707030b16124403d407881903e00c00d10117000c54440c945141c035180d980c07030029440b8400003221440e2102c00c25001300c001a6514000340300950300d03504100ca88034981c004607030341c804c1039002c543c0c00300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 102712841 1250 102711591 102711599
    0x1e01020309130b060c06012d0303030509070b04080105190b06040e101d09070f03021804022e1d010206040311010e07120318030c0909060e010c022b0e151b0708010f06 73
    0x13448c610402d9a600d860040b035103480e000b00c1545040b2664200c00300190012501243d40b400c1580680d00c103110703400b44450002040311503101102d449600d42d580040b4200008e01c030710303032404c0c41c003035000000d15000d5109590340c0d15a0455080004c503a450359400300e6000e00407100c03010489140941442e014200c4400d10310b50014104d44c0750307000380301801544c00000070b0a640e0b4054020440b450f9410170f20500074050301404210300c40c00c1c60007030f0200d41015001c0390318803811101c0c1e040304881138000301140c2c1c42e05c1e101500d0b5a01000402c600300c3d900c506e00190210000d008080c0148000d100030081c00c240d526014201908151110100e0018100108040f90042c0350700e03c00c071680305000080752081800c21740c0183c1400c000407c5a51700f0180d00205099001a80410340d03111480c5800f041c034610240d046000d0b9840c5d100c10300007011098580f4051400c80b1a1024034941500c155240c407103d03025118510301c802840b604035402005003003003c10800e018032200404a131001304111418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 102714091 1250 102712841 102712919
    0xc150e03060f071e02030d06060f03060f05150702060d02040905100b0c06010b0f0c060415050f01030b0103060203060a1e03020111010c050d02071a04111e01020309130b060c0601 78
    0x50300707007901044000702c104d810100c0c000d0080702d40c05600302e8800d002e0a502c0f44400f42181c00441e041100103840d01100103420950a00b10005441d801029074903c0c0da0703003501d244015085908142e9012204101000c02d054061008000901039075001241c0d0345005020740b214aa110303805120300c450204424050101c01040c02410740710b0703000009490301c2520508000c903020302c01040b41d66116503024131080c407406010240380302100c0b140a1042c1d91301d28102e0b02c0f000341c2c20311008000303c40510052000607025005503501074009410b05a1040d540e10405084c00883c40b0710020384503070644103109559000490440b2a20110024082103034540320041c00c51060002d0920ba150b408a410f4040201404059040030051242104541070a0901605a1542208261041c11031035012a41c85412420b01407003060141c0140d828418028103000c00b42c581c01840520860f80d0300008034540e03907940003500c1c0c1c210000005140325810240d2420b0390400f14a0300044056280490341e1056103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 102715341 1250 102714091 102714107
    0xf090b03011d10050c040f03140c04020a02061303170109020d0b01111e10020307091401020105040803044701050904020307031412070807021003270c150e03060f07 72
    0x141e0300000a119521640407174054066a00983c8201c42c80400000c280030400801414071001142a100000011010002203229043c98007000d80c00c2071000403a40754408000808060090801825003600011751341d504030001d8100e940855030100c2e0040361407000e032050700340c162780c00e08103c00c90040f82010a541c0b5131891520b8001611030102d0302d084644188201c0e441802d64000c10354070790030440b0014100c4a510b000300c11a001c180c18004010b5072050240034040c0303401c59681461a01c85450700180941124140c4205049905100100790380a007004030110700302000daa0f00214007404101c940d0307001a80440c2c482c1c01048140400750b0f802003803000441e6840502d0360101070307101d81d48a040c10480755103540340410101d07051080c801c08000410209100301c90400c0e0445004100f601210800c050880b0300301100d6800305403000d1800b00313104000c1d0140c40003041e259504c1000403034800400ca01c1100007200c84603d2101030401f00050f0b42c102e203200c0c200303e4481c03410f408014640c2c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 102716591 1250 102715341 102715363
    0x1030614061c0603031e090605040905180d050a090509040b060105070507030f08070218090a11131104050405010e0103110d1a0a1a0103021303060f02040f090b03011d 73
    0x1da0004144400c0716800d01d256049400300982806041d07940d09010381040b85074814220b0b0215102d00308078400c1d100e405200141c1b1400e45645003040d0401d80c4c544001c050040001c0c004c400308010010114008102d64004030700d26940b0a540c2e02034a02000780300d440d03107134001c0340144078400904c400282111115540300c1020319009071a8202c5040c014541555980090140482c0c01401014000b04400030300105000b5a0604c0c80b40582d4081c1154032401110b0100725500041d5401c0d001441d1040380c0c00d08807074001d0206c08101c1c00b101b401c10803600000b11080c80402c00040c204803604050040da0b0040c0f4452000300c000350300d541c58030040e805449101601c9101d41080c0c0b81c0400002d400c00d159100080450340401703140c446219401880d4403002d42101c1010080100b041c2e40c403d000b00d07200c444094143c1912030307280d5503e41000d08680c05240342490b8088c0302c0494040141700f0424000d01f0040c1d000b05510f244d010030305084400404441e004e800603a80350400c00318001626003019 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 102717841 1250 102716591 102716599
    0xf05030a0209040b0a1502010b060702100e03010f02041202130b01050a0503040203070902030702030c0708062211040203280c0507020d230304091b020a03080709050a0e07030b01030614 81
    0x50b0303581c000080c003c104041c0c00a0f07000d5880351000c11000c910340d41d80100380b00150020082c041d8810b08204260285e01e03c001e6024441045240030301707111f07035181140307200c018001140c0281d020040c0c03400d82e0025006a100b0403640343c01d081c20340c90a126520441d90f01c401080181c1c0d803420740001c1076449840c259205002000000c80d00b1500c0c01c022280003061852011500c0381822a03000303480f540301c0c81c2d030385503203201d105030206001e40c011560780d0144440440700e01058207104807008014281c0803003071380c9045010041c0b030216129800110b04c074030303e6084a4010740507201036881c0441400901c550902d4a00029050ba103078000c7c04841841d6012a50f1281381d403d04d140603101000700380c2d881c80c0060040050a805040c0c004084c10a80341c22050900c00300700e0014078190003024190000d00181c0c810184c6402003802121065002261480c050030300d2501c1c0d1000c21018895a486014481c0100d802c1050555051050b0b03454240240b030103001992500000309400c84400d4201e51003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 102719091 1250 102717841 102717847
    0x10308121009050406050402120f030910030e060f06130b0906040b04090203013b10021b070e011401030b0a061206090509030706060501110a111305100609060f05030a02 74
    0x1c411000e20308000030940c0900c180882d10b0a03203402e43c090241500d081780640d0b040f020468400101041c0b1110b07001801340294209441b0703408101e080710284078100d0600d40d40b03440b08400c0e42d0040c01003a2081c07102038410980c508010003030010825a4202100100e03103460341902c007955440c944180c01210440d00441c45d201a03100050007060180d50095242d80380c8016000d40381041c40180340c030780d502d07041c090a00440c0328040c0d801c000c210b40307003800c501d0700400c4600521002070f5015210201054000d800c841009071415490100140c00c404000100c0100410000711208080d8040c0102860f06102014040c00450145d1215009200c1802001c0e00101c01c01ca1440d4020401030003144024026410556003c0740c690388607580070f49845040010108155008010410600000b00010a140d02058403501c200400c048801940281c90070309070f00810f1420b00500f1b0242c0303c000506c0041034600390f00680019020340c0301c0c50a200e1b119404451680e00a019654003136410100580c2e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102720341 1250 102719091 102719101
    0xc1c080f190201090201020c040902030618070f0b0d0c0908030304060e01020d0f0218030a020904170708070605090d090f21080a020601061205060607121e0f02060a0501030812 77
    0x140da000e0407140700354114a4004140001e5415002102e0450003070b001c6e540c070352400401f4842a02e401c00d0020350075510203000308801a0f4524078468494810758107551115840c0c03402201c0c4184035a00649070031801050103034803071072140b0a24842c5000e605244a0040ca0500f0481d264000204080d000c00c1d038078a56514206000e40403035290308200d100800618444070240002504601e890b9944000c3d080c0c510300782030400141c800e04603500203100e01440ea40350381d68105500c048042074902c2c4107041c400c0301c001541da00083c0001c1840307070402060604d004c3d42100d181281c0060807401304407010000b000340b018803030340010a5a1550f05d030394030100001f203a1003069044950b00104200c500060b65078000b9400728106040e01d029030f81c0d030b03507030100800440401d8038000e44096920400400082d400101000d09c5211703500ca89007095100c40d42c1c12140940200b003420740e5140800d00c2c45002a000b141d0600489501c4040c0d4281041694115107422456006603480142440c8121700452 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102721591 1250 102720341 102720367
    0x2100c0201020f0105010f0e100b0717040b040603060305100b0105030a1d0d080f07020a11010e01120e03190503040506060103090f050303010f0603060504090b06090718090c020c1c08 80
    0x1100fa1000d200900c41540d4860b0020100c4000348690f600d4103d801021808a1162210007000c940e6071002203428a0025121881e120f0001e9040084000d41040001502424200a40000c0105031800500b4502d503040c064104070a402c2c085071131610700b0302020000c0c1c0e001030030380390000840a00003804a81000241c0031350295450341450728810b89141d030102c6070744030281c2841640d40400d20b07803003900c2c2c3e581d080e80d403009149401400e00440034603c0a00b035100b05821191500c0514181003034020f507481c004100c940b2204406465000054074103031142c11560050341d07a02841c60000d20b10700d81519540c5e01e56201038005410961103054160504c9803890240201c82d40250a981d500c3d40d48031010020b9000794442d44002c41d044c0307400000d07035280502c1040603031380e00401d102096581e10010050150801880e04040c040280c1e146001440c0103a604000b030880701270006022000050043d08c0c000b00c04500750700c00c00103100c2c245200d00364082e1800055030300c42803050f1a4006c2607105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102722841 1250 102721591 102721603
    0x30a06050a090905190503030a020706110c0a030207050a05150a0201060503160504060609061e020f030d020405090c040305030a1419020607090512150406110a0f0314010302100c020102 81
    0x205500507030008010881c00a00d03409080c8540c4108111601101d80402000c61401e5001c0c002d40b80d908180000307810340b4020727002000954816000090f0704040c48200382042d401542c515641a4000d4109800301a010040140903045c103c0301142441c1c60100000c5400c50a020f4161401d4400318200990340d000350005d074007401006050300c048420240e040c1403c01707440e00c40c96102e01d0402c03a00203581030041214800f40d54180c0c3d82c09040c0c0740c2140051402c4502d0580f0101144541030004040d0724040c80034250030550010050f039560700c0c0c48100260b084005d001c2c602d100000704003c0000400000440d010b010203030500c40010303902900600454080c103031072036136202c55841c22003030311036030100d9084c4c03052425468607813485446105004130b19482c62401611075000d0070400c4500f018404400342c1c454840c6002280d410030381461207009421807103440c800b040100401d503c1d80c0341c15000d505d014410001441e0106d40c50f41c0c00185941340308124010612164a03010000d5920900070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102724091 1250 102722841 102722849
    0x110402070606031b0b030f061002160801020d0b060c15090115030b070f1403070e0a151106070e010c06050601121505030d0c0f030807020307170d0f02091005030a06 72
    0x10040340765207041031104c1c24040c03035214114420003100803c01020100a030382c02040300c1e80425446a03200070500180c2040407814009621492041508900d403061545015054030700c0056142c1d075441c0c1c0c40205845c0080d40c0d030744c031608061244a82e92040000d4a5030340e103010b09207071601390b00d41c26010303030040603001081c4030304100b102004418030201140c100c0c0500b07110b54810085010740c1c00111101200003c0224420000300081100b192003a54440303215000103040c2480982e072600b00c40c80701c0c2c802c42440004075089403103c403510368080c46450742c061510304040001d002c40c01d00003000d00112003030080c1100d03a2240031030701c0c1d64400c02c01003401c00c00f2220104401042072030681d0344660180305940c0700e4410044001e02e218820540080104d900c4030840c20541f0440d45c0136a0452001000714046106c144100b80205111000c00c80340031381c444001640d600161003414041c5ca06492800c4c2c0440e0040000441a850b04c01660840c0c42c1f2511342140c40b519001c010710094011a80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102725341 1250 102724091 102724103
    0x60c0a0309031b0818040b1f03020d09050106060201050115050307081023091f0504090f021903051002180d060608070306020310050f0a090b0d0c0305031c051311040207 74
    0x5403001c04c02c02c0420080c688015091202695001d07143d00700019900a00b04030385c2c205502c400e2106003c80c2130f145031043c50400e03080150400542c16082c0302201c07140368050340c840c1e445d03003070070400c55030203100d00ba01408400005500b54069010050314902c0054164420020b0902c00520a0700ca2018101f0161484d00c04aa4026420501200015421146540c4103440d90300c04100c00c1d2101182d031000030907040c0707016902d01d07207400200700041038000810340c3c0e0007984000000059607150b00100310a050450f10b69019410b50611a140000e00004105900c1c4100300d2410482c01d0015454001a401c9440f0580d0390b00f80d00d17001d006000342d5403081103184620207000c010007800d50059442002740d50a14098240d55008101c0215000b030f40d00c54000084581c2400182c1154205d08855980038100001300a0a903854411021031680700341c480340c00115090490100c40c6211824440380c41800380100c1c100035160248898000c0c100512444a190503850702c7d440300d406460746250401 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102726591 1250 102725341 102725387
    0x30f030b0909030a031104050a0302090901060308030103080a030c03110306040902120d2109020108010524040609030204050708071d03070b04090203010612021305060714061f08060c0a030903 84
    0x8001580e0360454001c0101090805103034544244222064a0881d40700030a80d09c0c007030b0302d95004d124001102030850101d81d52103c902001041c500310007176009604c0358800b07540c3c0f41ca07002002012140d041600d4402c05007000c00c0c50b00145a03810a0303e811480440c2e002801500510000780d40301d58804020031b41c3d005a125081039181c2048075400702100300401d0115082c42000380d07004841c006200240400c81c50001030000c0d0034403151030004000e10b51140050b080182203051841d40041e4058000100305201c20b0046003801d000e42a0080075508114001d4108200c019141503514203810350b01d00958411410a55810424800101000543e190340d0b1512003642d50b000c0c0d4000d010740c2c40170824400c43c20b009287e007442141c001c0c10411840c00c00d4030713061404021050380300355000e44081160b0201c200921030140140c0380180c0c80c1c1c111080c00d503d240d60031002114429440101c241d0841020011a903441a00700c1e18043c4445c580001d00c050341d45800e07295000f00c1981d2100c240410 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102727841 1250 102726591 102726601
    0x1b060c0a300c2a0b011a0408070f030303110c070608061305010905060f030609210403061a2103180301060815100e01060507030f030b030102070c05150403030c030f030b09 75
    0x129042c5200e81c102503810318051071030442100e0042d83d405100400c860000e01c01040200100d14003640008003090403030349807d5841200c540f80849980000401c904586010820180c1600c100c1060703e4941070b4460820003080c00e07058030784419108001c103022060000941c0e030342d642c030701103088038500a600b00441c1d41c580300440018202160300c1c031b00030801e14600d11090315000460310700c00c052207001006040c502d280400401361380000080070114050001100040c25406007040003411b40107482504e103ca201080b8203000c42d605a4201e4030071440c02c040d0701b420080101e410840c00a00c80d180800c4201c0d010a0040065903c141a14000c04031000034481c0d5402c4018000c5090701c141d0403001d602c0d251203d1080c6400e106000114130104010000a4054038421383c0902c0c03a0304002900d02e40d50350100742603901801c0c0481e030300c1c0408042800301c0e01c0d00b042c0c0c261485010b40f8503c1d06047c1541d82c050080030003201c4c0a1300348503420710440100c6129800287e41c1c014050700d049224141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102729091 1250 102727841 102727847
    0xe0a0c120c2a0c080f0d0c020f130e010c0302090303040b0708040b1606050601090609060c0302011506020f120a08060919091a07030c090b070501020409021b060c0a300c 74
    0xa0400e00f180d1030720303101a0000f40240c00148210036444030601800c54040007100986040704401822a045043c0c0c03d600e4445664001020a1901000d1004501010714005450855040c4006c540a0610500180d503894400100b51002d544052914136038030440741c00d051203140180d034480c07151200e00150400a0602c5611401d0b250351266038184145d850701d00055508200c2d50058500185c000c52040200ca403241d0980d440c014000e000015000340340111400b01b8120b29004000541c0c40600c42c2c105040c42000500d00c43e01411101d1400c1240c1c49000504800b0040e04082c400c44000001c101540303051742e04060788a00440c81004021000c1c5400c100c1555003540072140343c0340203000a4462400b90042d2600c07240c3e0b99071900850390412032101031f03a8020120682e015982448040365014541c03000b070140c003044160461a40001d0030500d80b400030000c1000f0541681404149900c44d0002c000040a100c2089040c04107420181100b401015561098503914204070300a4543c80d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102730341 1250 102729091 102729167
    0xa11070510090203070603050112030c1a0403080601020d030908040b03060102160e0f01050d0f0602030a09170309120a080705070819080103050609030405010804060b150d05010e0a0c120c 82
    0x110079001d03203885e2555400180c003107031401d1242003241a040d48080000a104048060000d403213803078400b10b01030b4004c5101241440894049010860810602c00c0640e010403800c1c000340c00524017402007001607601c80f5250700981c4950b41d802000840071541603802840f56001184208c00620801d5030350ba0b0390110174020603170b102080c9881000c00400c080c1041c9040c0da5000f038100c050001008501e61340e9400941c001041e04040b1969521403400041c10f00024094460154507919202d080040c5158208903840651407940c2030100250250142c0007201d03243d20001c80e041c5288c0395034403800c00c40c0c1c480c400c29042071103010a8254041d1800d401c2a40c56040e41e005400301c82081d612514155035038800c80c00f8640c081992100000c00240c0160042014800058030000c141120703041c0c4909035420001c0640a000d0700c1f400144071040001c030860740c0c06404078a0070f00c03030f00240460241c51740140c1041820b003d038984003a0701c030140c054882c410f884040030100c2c1e000440c04030256003600c5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102731591 1250 102730341 102730343
    0x2040504051e01020307090b0421060f0e010203090c030a02011d0301110a030504030e1207050d050c0913111509280609031103010204030201091710020d050708090a0305030a1107051009 81
    0x25a04a50100381501940162801d465840c1c0000082c8408a060ac1c115400b4500003111170b03680300c0b01103146042d064080da01f243e0b104080003680320700b40354584030304003100003500c1d42c0698001c2d01c0240250380c0c054500489508540c0c2070078440c1c080e2a0100e03001d4071141008207040c11001031444813030f66066201c83e00c914000e41c1c5030003072800c542c0100005800c030b94207003007041e40c402c410038041c5d1300c0c114401c01003941c4698221001c03000848085101e580c0100d07a091540ea030409445010f0080704070b103d05c0206401c03134050480c80d040300c490466900451902c1d601846801c40e803c01941f13412003108800800800f089103e2030740d82d06008103089054013044501400c01c0c20510b105003414000c2d0b600b50703a8140c44480d24681000d01c251811344411b1070700710540c450b158031fa829110082c0b004060b00d5841240102d0740f40341c01100640040c074003518070f041c5503000b24148070201e13070311009a0343c1048046001069070760741d0701120400d40c010110041c0041c0140c003195005104c0d42d920a076401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102732841 1250 102731591 102731597
    0x303010311120109080910030f0e010504140f06010e0a0e010e03030601030c0e0904020409081323061c0222080a050f0a0c05010f14070606030201080a0207020a0302040504051e01020307 81
    0x25816002c001ea0907201c43d910700030500902406000040d2810145003100e2013410f2600040031b1643c8111041642e00344004010165540d1042c04280b20f80804240001a12170b00105500c147d041034a80e0b80b400e0512841c0c52400d25100411150740d4180c01c504901c82440000780142e40d241402903031654410f4402d42c0c0401e141074604403929000e6000c50199807001444005507030f5a5030280b001900004000301c55040b0200710040c448000e03010044040d0450035049000d04462200d00e803036020b42040082d00c640c0c81440b4030f5001000c11009180b200840290268440120804015217944445156656110f60f51404100a40006441c5504900070302c00c640380194944a81611001450806080344510006c00c1c00b055018420606050095160041e03054483c20307041440c2c0d070001d030400c84100303884890401c155a03000320507035007080040004510302091640050520510f511009000b1030b02d03440000c091160501c08844011310300c5801e1442d000840003160300030740c800c507044804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102734091 1250 102732841 102732859
    0x408030a09060510180e1905011b020a02040612050c0f0f12030c0d1107061d0402040303030209090105090601090e060d1209080f06010605040915050301110702010306121a0c09030303010311 83
    0x440d003160300549408103050300c06014071f89221110101c141420344400d4805649500510203038146106031031a0962103503004e07120180780ea00c10003041d0b801c5940320060640b00c06c440348020540c08100741c480c140b0101c1c2d8442c041c030149004100020b180400503540810382c0035048494040200081206009010076a0b084030716030b07002a03c2404402003a000706138080042840f059006a4105207045100740380c0c805980b0311000054183e034030603003080340026000301e1440c0c440d04003112054090700c011540c0c10240d1400d000000c003c00300070710451440301814000300d28140c84404c0c0a0011030317000000c410103d5403011002d06030410314860006540f00d504000030508001188140c140c0b500c6a5500385081c0c0752501040142403032101e07507520121440400034182d03609101e040c8194100c282120707207581250002404452003540044500c0c11101e040900280f06544801c09071079030386060f01d181ea2620744083c3d0302c0e4014001400d805200000c000700c103000c0d20b2052000f81140455038429 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102735341 1250 102734091 102734129
    0x702010e0a0b071b0905040f02040c021c0e061909030203070801110d020c012c0c010504120803040302070e040503040e0c12070e0303120a0e010e0f03030408030a09060510 75
    0x2888141803144450050080c0708240006420207090342c100c240e401d0b0403814060700c3c5e4200404540c000e40f001c580a403210000141103003402d0050001000142c000790000051001c0003034540003404007080c041001d00300e801940c075660714098840c0500050f2211211030502072000e4041680c4d4002688607100c2c1900004031282e05001b01c180000d02903040c00d080501280c480000f03908a00300c07a8900e075482e8021500894154201000d4130101c24855401a04100c05220705202e402c144403030410900b0401030100000144a0025695104000d660750b5035541c00d0482c10007820b90414400301c040401800244400003018000340d440381c1340100c00f03d4940100029051054020803402c00a580000030380540c02450380070310307221014064078502205800d00200c00701c5c044070050f41440d03844c0300d003a10001c0240718420028018038010503807000c0c1c5150740e944d2070100a2000f0502c100010001d4007001d029082502c0710f80d4806014803044c20f1007182c40145c4822801414000158240d0102c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102736591 1250 102735341 102735349
    0x90703050f0307080f0f0d0e01090b0703060302010e060f0c030f130501031404061d0a14010e030405130e01090204022706030c0d09060216120e060f030601082a0702010e 74
    0x1501c0e82c4c2d120003580c2c41c186110200880b2900880000b0704d0803e400d1022940d540c0c0c46024407c1c2c0032210500000d03000c0042d00d446c40980c18064140d6042603d40001031005076000343c18565001030444009845841600742d4100a12410014048034000442c80300c071091464006000f582201030a1196a0364940d00118115403c00301180e0700c2c2600440400c021403260390011400c02055030b640e074901465464114580200c910f411078150660640c41070609900380b2400348054083d5001e549821300d0000080c00c0c40c04030641d1803801030340c3d85401c1107a00380250302c004282607025105544820640306036100c8940050441801160040580101454000112403150050b050018206014115003000404021600311100c5a0070814401541c2c580e02d8852001403090030306000c0d4110009004010a8800002e01d000320001d014204d01400b9500075660b10203030038640510165030308040c030b420300502254410392401d030140096414403841401014440e00030380b1202c64221201c4144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102737841 1250 102736591 102736597
    0x12090e0a0b06180d0501020406090f4a070324080d031503020a030501050105120f0a02010e01170702010b0f0d08161a09060103021003050402090c0a020102040b03090703050f03 77
    0xe070b020750100194003409103080900204a007014100c012161000c0d512542240d000c0c0c5c0000b00418141d01c0108190b040515a0801070200810000014021a14403d40c110120340c9450200004420076850420403428214907000e00700039140702504206902800525203d901e025030a80107480c000e40c002e004030031040c01c840ea520010191540500c5c0304600408841d20045883c906000d0000090b90320905400c0c09940502d00004665241c08104444071a10303200c900c019800903581605a41000b103245201c035502820300800e208403040040341c0e000d903038811070213003070f44071800340040c181d8154400b81d0210400d49000700e201014500300100022070a00c024241d0b03c00308401600c1c1c0345242d0551100724403e015a1440c0e42d031300d20441070306080440e813074116603005100410961514628080c1a071b00581404c024604294000c0340007050000e144051010380020041f0b245071003541214004c1040c024900d0300ca00348080c820340c558010784402d44481c480d495428007450004011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102739091 1250 102737841 102737861
    0x3360201030b010c03090e09010209030a110f0d030c0210051204210203090a090e0307020d060207030207051c0b0402060c030d09020f0414010e0402011b080304061a030307020d02060712090e0a 84
    0x381d41c00c6d2803030404900c1c001c07007004120401c155000c0c04401c0064400300320742e500c180d1181e810220b620382c2650920416003041c5000d2481100c2205052003c42d07000f82511090341d0b01179905903080c0495503001c2d100d40c8a6500e200800751980400c000038002c11501041d4003100107100c015503070081c444c0880c0d0b40c1c01b5030198182c0c0a05800d104016510203a40700071220441c10007540d00317140842e000121940080002550700c103800184000c00c2660504c1608081c203070803647d558840d08c000041e000700c6141104001c0150317a18201080030742d0741d6801550158003440049039079558071280020f024001d011070482c01b07101c1071031031074400b8075050040c0c2c2150010042103841070382c81d11003c05c1714070300007910980c14410722600c1103501248042c0001d80c014022402c050b540e040c030740340107400c507156004101c03054400020100e003650307000b000b15164150101d0300b038103506d0301d640002290381c40f600ca40100780002144201d122250051318003c1121300025003800039507210b0340700006881107494 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102740341 1250 102739091 102739097
    0x5150103022104060e030309060f090706120b04110412030e0306070f14090a061d0a030203030d0f060e0406090b0c030124020f070f05040f0e03030703360201030b010c03 74
    0x1c1601141d20070300b1640d03010740961800300b5228403d08041e4195441a1391240841e0010810004640d02e0f00c0700346500580d13030f02c006010303083c80d0100003852050903c1c2c2e0004e1481e140d0a40270700ba903440350414811088040021035840d95aa1308800100b005490110040b8001a180c1e030814900030603403030b11902094542884203078200c0011100000c00c004100c0d5002c106005440187c1c6402000310090302580c0c43c0c441601f4506c8042404005407100c50314421608000706000603200842640c3d04801d0302200420042800c00404000e00002d0300a07010118035541040140f2150341c103c074220718015024520310b5102d0001e0103076184001d016002502c1c10b0004203031b40501c1000e9681540c80d83c01e10580301140700e113032009401c0c060143e20904176196290000e0049141c64860020039183c0c0d42c10802076052100480f6449000041201c2c1c1815a140c40c954246d01c61500c0144e0414017290f15000c40e818180d03a49002d01170b0f180b00070390000e40307040c040400b2540070306212004150161 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102741591 1250 102740341 102740377
    0x40b0105040e120703080609061f1103071704062604080d02090303031005030706030c020c06070602040b07050d1d0102190c05032b020c011b0201030207150515010302 73
    0x401840081c141d000c0480b9650b10034420314102841007500500341a610990b541800c608164080203c2c0c01c0000e41854801d003482081036410301000c40d4441480c00300c41c2030405030803892007081804c602035400007401c500f80402074200d200d0302003002003054510985801170007000e11901da15580c40f807190652031000410300818040342100c40a8209510050000b40c50400e100c0d011034250340080e1100100b600d4080c80500151600348141c2d0f015108910b410005128298002591290a018494064207000a254003800748070340481e40074048210010365100c40500d087d990b16152101c0180c0080d20074010703c1141c00090400c04c042100c144c0c003d01412104d0178624648000346001101c0c0d42141c0d590024003502c0c180034041e207561404070302c407a20f402c8074442c42e80f00d01800900c0d201190040c4140d01211f0b80c1040943d0101402c011540741c02c41c6052005800a210706200036100380b01c10b2082500112040c2c10680c421000641c001100611900055060b40120148504080800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102742841 1250 102741591 102741599
    0xc0905010f150503090102071e02040b0303030606072901061206061d0f1f050405190e1306090638281706040b090d080c07051c0201020a0215040b01 65
    0xf80d028541040c4103100051508940340d54441c06600c03422103010100185607003070810341c0f4042c41544c0020340f0943c059851854036400023202807007050030003024840b08c8140d411400c98044d400386010094103004102e19610340002034106c690800700034210358140710000c030380b0078440c60782c200b083e071b41e04c1e0701700150b05407034504005c0c0560b00c000c52590020145441c855250002c1102890310035125110a5a59030504090040440f0028400f414442d12080c080002c1000c0c0700b0429409400c2d1360307000004c1007541c0342c080068024070790060070060400b81d00d0354840c041c0c16001181c040d10340d00c140152900d03001180806c8500b46018036442000010920700701c000f0880c501c08103501c0b452034220480d03110440400030082d03442c1e140c100341e4480402c010070842c070814600e40015000004007016125480020108480280f101142c44008100f6800b04001009128007440c070f25450300314540c030a140024001c0d002005c1001c0180f05110160280b00c2000301081c0c001e6030405d81c050066805c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102744091 1250 102742841 102742847
    0x30304030b0c0c010c03230105060d0509100c020c0f0909060a020d060b0301090b011404030503090d0602040509071101050a0b1e01020c150d060b0f0304020d020f0d0c0905010f15 78
    0x1006286070340c400300c10443e85034820380c203101ea602600ca0a032400646210b03090a041c0e0301b0100c1da112181d01d00700c6400103001d91b94a1707030203968481c208030201150a41d1905030b510304114001c0103013819181000c0232220410f40200342c4d00441c10040c2c44d100340c00100c81041000ba02d20903a050300c0c0d20b410540100c0c5401d84c51740c0040140e030441c02404140540e0316440d130400307544241d10812a19945407103001856911190b1005661943e1407150b04180c11603c3d40c070307207a2048400c554490404102003c0400c103160301a5401400004c0c510038080c90010310150482d0030b421a24040c135403a100000b10385410b2449080c4003c2409402d030783c02c00b040d200246070180e03880500d10381544122005a46c2ca5a00c1d9000c2040400508240541f03840301082070400352030030340d00b1071260b44100f03000b800c4400340b4450030350b540039804480001c0a03600302c0c00401c2d0b0403c0c0c04440c03540c02004c1c0500d04000d0052845803c8119000d80500304000d03aa5500d20003d055020300900550701c402080001031948 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102745341 1250 102744091 102744113
    0xb041a0a0f110304120302061b040e0a02071b03050609010c321207020a03092403020310030b090102070b1e0105060307020f010504060c02061605030c0705151f060e03030403 76
    0x440700c403c583c40d103502c0c0c1e80184860704007000f049005900c50070070000e140124000c8070341c40502d81d56036142407a0902c509514040001030081d00604e9000c1040c80034441b040407044a410103a0700041d06003600c0c4d06101d500c403442282d40101d19805c001310401d03100e200342d92030070324084407246240c60690802c2e0b11280911790564000c0210030144030524140e04101d445a0068001743c004180e00c0700d075844c000c0c0503038425511490541c1c02803044483c04800c2c1c4411303004001c00c0d03442e0050b40c0b0f54840c107402e0340300041c0d500040e00f50001c130000c2140805d0154000c0030000c1c09111190280d50f100c41e1049102522450010420241040104494107141c0c01644d00403580d40113451031a481d440e005c03401c41d0821101981c01c5521a6400102e10380c060040c141c005040e040e6018481c4e0101402500c0752001500c020104540001c81000307000e41070103030352000e102040c2440d10301c0c01c04000c0a02058411820407a411582c02c50000780d10f4000c1c441c1e01100b4038040e01a5050a18682700d54400071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102746591 1250 102745341 102745367
    0x1734020d0c1104180206040f081203160e04090b0702011a12030405100210050c04061413050f1212070c06020601030b0411010318060608010615230906040b041a0a0f 72
    0x12030741010b0b407005035a11b2000d840500080126050321a207000152490140301100c48000760204205220101400421200c401d0380035040c40d4610a2404002c10300910b044400a04200504411302c0702072171f410b4003c50342560091201d04038400b0361400304001c2100a00d04084c83e984200070401050038400303101402d01140d40182c0300d0401e00a12000c7c00d4400844003101c40840020b81805600d4006010410105140d0310386401c02d02a5080c0d0071045183e402880e100381024000036091340c2d640c120010b42400e0308025036030000883c0003a0303040340d0002c000c100d48000c02108003041481c80003821904907034115000ea20a0744458035003c0d0954000070031701d410591107044481ca071030303034200503000c0991068000180305464111104d0865049422030a140004003007072039070307407503220003041c03d0074480403182c3c031040140500c150000d104101106802c0080800c00150200440c0050800c45840d0134101d05840751284086003548101440c0101250754124503120492040c001a440c41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102747841 1250 102746591 102746621
    0x1030c020f06150d0804030303140a0b01020c0925030e0c01020109080a05030a09140309030d0206070c02190e01150305090303070801120302120f04030614071734020d0c1104 76
    0x9409580c0b110b401d00e500a400035404251980194010714010424040e4410020748042003042004cd0000303440707840403491144183c4203c3c0c042440d0342400045250805000440c0c1012882c4206003d00a801c803e0459081c80c001c08480f21810350041c0115130303545a02410144c5003070511641a98260000741c0616502a500e8140c900001e642041c104c03119181700e0300071900c4058100030185048150601581150040405c4c009980d03040b2912124091707044502d0071300b040d0459004043c2919079030200c4d0a110740f940001981850f61a107180d10b02103ea5410304c216039410310050355038407060b6a4140088c0403a001001114160100405058403c2c8155002c0d4070302a008036030f86800c03079541d14100340800102001046024030514081021184d03420109185c50440506145d2035011a07020200307413440050700000d034480300040c01150060301d8402d088a484002c640480c4007000f400f01600c10301840c0308032680511040c40c1d40f140d20856107071650081c00c0511003e469071030005124 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102749091 1250 102747841 102747859
    0x30e03010908220f0902121e161205011401140a0c080c010207020901030b091b1e0307120503120f2404110d050f011505040509060f0405090c01030c020f0615 69
    0xa08142103034200504d2041c0c8090380b20248814490210310b409440c0c40c43e8100314003501920084c01400807940010121b0b20420303488004841628812b1012041c003110900d800000300c4c510000e080060349880082c7d031011403800b01048620014896440808003080c4d01c0461440040e01c990001e01c43d402440c800981005010b5004c229030610a820803115410744104000c000d0f40104410742d201e00d0601c030340744011400b64021480400303030701841170080341500b40001c0e59a1000c20810000305100101d0f02109001d90801c0b50704d80d00042c52152442459078085040722110152040c01001c9200d618480c25691040024408030100798450b041901c440f01a8807101018002c6c01080040e0300c40481c16107071186480d040725505800240b1420020b5480c1c120740c580c40304c141e4064640c241c5d403816250720350000141007001d1881c3c03101d42c06403d010402c031800c003021a00000010f070a81302032042000c0d008082c0d85900000b840c032800360b4802e00c0002d8080d10400c084829410020b400104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102750341 1250 102749091 102749099
    0x305010509060405210409090f02060d0902180106081303140a0207090b150301030605090a060903050c06160c080310050409080304030e010c0c030809010e090108010603030e0301090822 81
    0x4295141107078907041e2070b0080e404200c00d01074144007540007080012840d60f15021404000c024a009500031511400c0d500c1900c8000c0004502c0500b100320740042106440703200a81060014004845040340500c00801803042e003c5540341c0d041d8142c40c516103812406a98800e0214400403482c2030690070000d4010108150f02d650380000e1040d03402c5a8040d141c580e08260b00c0200b0341d0810300659011340d01c01e040d904403100c180000c2c1e90550354001d40c0441c540c3c803545901460444c8030000a032403140381c09000010183c128000b003403125904000e0392190760b520404e03070740e000c881400d20307078042906817030024001768030303078000b594082d42900904c0030075600c85010034104d80d200401110024030000070f00040c10f0700080403051056091030128031504080e596196401d401d0b10005000c00e1001ca84100340744e004114202c51418080c0510005680d50309940e8040e0526110a90220b15a054540c3c0c060078103002d03141810303400c9030b5981c5c589020160031000c010b80c0c4070344104406560000100d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102751591 1250 102750341 102750343
    0xf15090c0c06010807050a120f02060a030b1e010e0402090a03080406030c11030f0906030c07060905160b0306030c010809100905071a09090105040f020403020303031303180815040602040305 83
    0xe00403280040e0007501c030742411915618024060f00540c44a0b4450541048165680a104821340c1d0400100c1a047c403007601e000395100c41d1443d00250b0140d0003103400003a0683c560b00a0301258421502d0320f4014118403030041404a295801900140000b80303031000c9030030b194000381100f40010f050340115941c0e036107650a8a0b005034209400007903d030b4058a07540c6a0007100800d100c400b11014628088051071101a5446419a40b6005210110001d0410f8850400707032402260021001c1c40748034040e180c000c1e140d1000e0b0401e41d12005100d9000310741c4051405c00c1c0c174440c40c00a00102070742c180000042d10f0020700202203904500c44c0d0310184d100d001580c0200001c3c10b1154004050241c00c00341409000034000302039603d010024000001c9a984030580d260450b081520000740c80c582d4004400f000e80708903000070350544000028004950382d140d8070fa515071400790b500c8503100d28841da40120b440c0914400c00321030364000d02e00c000c54007000c5040150428403a860061034aa41ca541e15 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102752841 1250 102751591 102751609
    0x50d081504110705070806010f0303030c03020906071a09010207110402070206090315040b060d120305090c120a020307050609090403030b04090c09090201021006211b08060109060902030408030f15 86
    0x150182c21408200102040010054400640042d101611903136042c44d01110404100384005400c060703d66940303030300c040d001c1c0c0c0c100c0d90f108501511960341c900650814015540001491896251034080000c0384508180b081c0c1d120f2942c448051005565180704000283d0030004090340d001d130041201201e25601001038580403040803a40180900d4281001034440c00000c10b0280039030f04103541400040c58110520b0940b11003801c00080a0700c078880e51350310b00540300100302d4004880055488290070b000680d8160907100301c0c12580b88540701c10a10083e40140340c44117400482d10408180000c0c005d4002c48507440000d040000c8407aaa134648003130000d0309131300640300e0035501c0b0254003e43d43d05202c29014000701d90000d0000070321f00140c0d149000d10106a240c41c1040907603c907070400c2003001441e101c0c0b94982014018403620382e5500e40d2200c030284107481d41c403490400300050203402d6000303991085801544039415540c4034078410304428401043d6807443e07403100310f010b40a50786003011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102754091 1250 102752841 102752861
    0x302120f0d11010506010302070209060112060b0307020f061b090d030e0d061d010506010f23030414190503070320120301090b030115061809020d0209150304050d081504 74
    0x30b04082040200095821580c02400680c10180100004001b42e2506001a9005002803808108500c2d55441c0035004110b180c00240083c2c00000500551903400665415280b0441d0181c4495031a40c4080502e4585040c80007280c143c018480c41b1000c0c5080040c04000d2400707410803100349585140056040d024001080319060f42e10092582001d916010030001d005128000f0401070904a0020f40080318030b405183c1004110002c903541c4994464000c3d001c1c0f0702c20842142c4a0500f031800040e450241c4c000b6120320300c500944445111044440c903c00703030741c121002d1440c101450301d00320f40d90006580351045004400e02d18103400007003080007000e0301110090140d201c2d41820194810b440100301058480c1c0e0422441450341809100b50303400b00c1c0c2140c1045185404c00844180368002d041c2e10a01d2114404074402e001d0046036001000149022121011044004038240c0c100380403d440190169210741d548000d4540690b07546034104800d8460300d8002201d4000090540388100c3c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102755341 1250 102754091 102754097
    0xb03070504090b0409020d0204020904090b0f060117070f050904091a0603010506010507020604150c0209090c030c060a021504050106090903050706060e0f0f04020d020916090b0408070302120f0d 85
    0x501040007542c14881c1005800c000c076001d0040f1441500044c45e02c0c503000c0d4000c1d100c1e03035002a003c4203030340d140e521504800340e0008a4101c01d103040c0003214484001140c5150110b12500c001440121051240078070500701a12800030a1aa441080340c1c9604174100b820b410a40e904650004207031031010201740c010361020740c0d941c00e01e040c00a0500b5035101030120380c140708081c400c0200581c2c52038261410740e001200301c00850180c02c0c6084074080041c26019402109040901c18008804221842351920640456000c8484a41444228130840e151000180c02480400314508000440c0540180c0241d00100f015512940c0c0c20313084869100782100420f030b0024208007040082d0040c0f0300200320121070f4000c540b414441000440c00004e050035140c4e00030200143c119034452181458a80c0c0192060145c1d18200241c18400f1b0001944840401d00f18000000c01400410442c4c0c2a6500c80002d44540c070b15690034480b003501c0da008100190b0262410300c1e0744c101030400404403018895a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102756591 1250 102755341 102755347
    0x9010308030403030e0d0e1309060e1b060304020904030c0c090f060e100308040317120106030204091b0917010f0e0a17070314030a20190806030c0603100b030705 71
    0x200d001350458030315548140040d0010f00380024215045080042032580555203801102c442550010041c0451b200c02800c481c038101c40d000f40e94a002a0803014207420b440040c80b140e01010400c41c0a0001b160000d40c06a000c3c80041d00288c421025060118492001040029210400b0704140c4d14002c0001140d5a550350080110038211500c040e003040940700c031084800d003103455044240c4900e000241064061445014100900c1000c0b17414401c04000202865619042c00070040c1d48284035590490b800e00001e5140c1864810552220700c03e981c807100d0842d072500c002680d034040309611110b5507540c1d07030704a00494234041c0113854019004030098409481689041503420410040c081e081c0351042c032001e000641c02c0540341101018a044103901d0740e032201c3c0450b001d404104071200121032400c1d00d500801c0000c1c006000d08038060030401d02504203000044410610403110158580d02c00e1906450300d051040080da04234262800d40c030b51131503e4070301c44002c83d4015505100020700c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102757841 1250 102756591 102756593
    0xa050318060306031209030f030a02030406030b010302120103021003020705010212090f030304050d0507020a0305030a0c11030f250e010f05031b03100c120c0c060507090303050a0804050c090103080304 88
    0x440103828418003110781d40d0030360030500007007640c9000c4500600a600c1c80000c11058980d0f04100b10304040000e00e0031203940d8110000c00940701e40191240750007180c1440c0c00b04000758000e0094a104001c07803019003400f0381c40c640812070b908036000c2500c1e052550030005800840c0c82800240f103400c03c00860100c950620400007860b003000c0c80c404c0400d9400a20070310000074804074080e81582074500d081d40c5c59402e207000051100c61903a2000700300380b1000940040e581e0308505031040316401441d43d1000d042c000020303d03440742d904540b00c1c0500d400a1a5282075103107048007280304086088460307c404e130741342c00c5490741e005c5003038001d00b0b894007100004011900c2c0c100800714206031210f500003d8440c3c1c44003c01d0750707020b50800520130180c0350045184144e00c542510040e02103802e0007840003212242024240e04c16101003518007604200014440031701805d0458101d90b810b507038039450822044011600c805014004446502079003a108065940c2c49603041d01960062820940e03034102 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102759091 1250 102757841 102757867
    0x1513030b01060201090b0f060a15031a06041206051005030102040f090f090b0403080601030905101a0604050603060d110619020c010905010e04020a2309090f010b030402150c0a0503 79
    0x142e01400840e070402c81032800142c40c810880f40c006000c0904d8030a070f03880d2003000505035241504800d8007003d41e44d010b0003031140d26070448840a00741c07085051025031600d007884840d200f14000c80c0814103550300130340300013411940300d56030010b001c4e50800c540e40d840d040003d003640d2007540140300b503038410071051090800ca4421241004001c1d50200a03420f03541c0c0d40c0e940d00040062003e41402095000150940d0283c1c00040c512a4404142c818508100007140d00405021003000b851031420060b51140342001004c50b001d0b141c1c003c1480d81196100710401500301042c1600720361a1404506034500303511590040d08030402d10300d454005246520400a01d0072040b1160241004840030342002603036006928100030a2040d1000769a0340002982540c00f4020514051807817004451070380e0880031b00b07602030540100708a44225907612407030b40bd40f10048082c0690000300508102060051601c2185040b201500c0042c0c2070500180500c0300303080c11600882a80c0d9604002500c0e584180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102760341 1250 102759091 102759113
    0x30f0e03210c060a150b091c050607090f031104090203120c011a030613060f2a0f022b090518091006080307060209180a0c020712030c03030b151303 65
    0x714003044501725028488580c070150303116009000d400000c44400c640c65040f0103003042c03918445101078000441c41d01f1951075400f29108030018456150202d08107210881e0304044035009008446a0f02800c41008000d011070b4030202d038544607004651460040c400080c00040140100008020040c180c0c042d8541c110f540c4664860b4005e0401c001310302c00d94183c0010010340000c00041e800c018091540000c204074002d00b068058026482e03003d0004c0480b8460044038160b0302c410f40c501c0440b00680e0784108500c225070b409202c40303541894401c9101000c1c00404140c2c500916500c4e83d50010400050704041d004090000c10810840030842c20055083c6d4103511240812506140c0f00209850b4011741e4001009070360006010030055030786000680358880350691200fa035050102d003250041c40280072000c00344c090030000181104552650001064058031840e05200895400320001c0880658007a48000c2a138000490300034007001501034420500380c440e280a083d8240904071031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102761591 1250 102760341 102760351
    0x190506010609060e010f030504030e0307030804031e02090426030c180a0612090503090405130302010b0103090b0109020d11040602010c09210f050321010918030f0e03210c06 76
    0x4141d04030b51002d9039a01405186c4400d2a0740760008964480785421110a1104149654140308808000c002e0018410052080b24828000516006662102403940c003624400295010100d000002c01043d0f602c410808240119020740741d4280800075104401d40054034803000d51800484d9643c3d0351000034052004240003120706a4405140400040401500d5503407944119151340d05041000700800a80c0c3c2c0000380240244024500f90b40020a003e544c000b00307400640c2421884102540a4810801c03041d400c40c4042c02c51303030b0805241340701a40c46814080d00042e070b1032000d0304424101300080c0c400303400302d1340c00071038428603000740240707801410f40004803403040380d100103a55000c0400c18210f00030b912110745103070080d682c241942580582110002a42d070030302c81d0318070f40c030084942c024140c0d820b0480c200500552040860840000c002000b4086800074042090b2107002d054582c1080500408540c44c107001810082501190034040491202002c01e140d48852030a00140d42c0c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102762841 1250 102761591 102761597
    0x102191d030a05030421060504050c092802030c070b0403020609010624030e070308031015020606011d0a080a050f0114091005070504031a0405010f02070503120919050601060906 78
    0x71203480e19029104e2017944170302400b110107204070310400c110900d101030600741c010008000344d14050134040d4481200e8030f5400e10400170030300050003130443c0440123900c43c602013011041594407885010300130b5101600b49071000d4820311612000801d1000c00a1085200e42e01414039414841c1602e800c1d92030b075410514400b24084040105001c021a0011448450385004241139808a44041c200701c0c00d90006407601c0307000010400e07607032881c014120848950004442c2100a1044201e8507039005039540c500044501e1042f11441c01041a8007028076801440c0201440e51003840c2c078034000003000200c60541003040c12461011080c8250380000130400c401c81982e15010804903100c1c2c0003a51512400d503030350000300b25001d03c81c0058901842c0c0c040b000403c581080e550304183e075081101c080b500c07903081c02010b441c407043c54000d0710f00c8954050019070038140032400c0c4491959009002d0b0909100da40c41c8100381026001c0c0a020740760140000d0801d950421500400c800c0464001c030f400c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102764091 1250 102762841 102762853
    0x302030c0d02030a08070c030803072102072402091003150501081608070e33130b03130210121b14090f0a14041409030304030c050102191d03 62
    0x50f8501242c04035030150300a02150b661070503464180007030b01640c3c00150100802004200c403440e00000d160300030149404181050030000550070007a8400c0c0d8000410300f002e0500c0070070750300c2d0f2500000c10b00d0016801000d801d0028120100b48001640001800082d171260414810031060340d100c41d01500e801e180110113403400e902e01650402c2800b4410301000a900005030310540300b29028011003100400116200b0850205c07079822084045e035000c0142c1c11020fa8841080164085842c0d00d01c00850f0700300820f240810144450300300400e80c20050400348031410050740e40040740c99980c0d1403500c1d00e5052158240c0304104940503c45e840d0000b02400c440c1d01c1c581c42e0060f040d41c3c0c0c600c0041c0c440d031365111000808154042e0751444280d40011580d50b010401041c2d015545030406015101000f4980c4050340600352610160303180380c6540c104002040c040b901ca14a0a2420b5000e10005032800307207100b80710000d41c02a01071a000080e120300a040c6d0b041c4540300c401501075021801410 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102765341 1250 102764091 102764093
    0x13021c0e03120f09070518010503060907060f20010204091b0e010e0609040b3a0f1209030803090105010f0b1c05061c06020d05010b040f03030305071110060302030c0d 73
    0x51080e0b4064104400102100f00040c4115020000305019100c0a0a00f010307804550420310103c00d820302410f4800d01803100062042c400c0007a000e001c461659031180e03503043c09201c0607100f140501104641e040704a413030030f91078080e0900040c4020408620001060004034642d02040500e00c0c0b000e6080100b0002442c17940d070b030300000e41d0001c500b04542403a03540e4803a40004009140302d0f0328854001e00c04206000c400700c07080d00b40f401c100588841c0103590300580103a0366000b200d0a140280a6400415050042226080d14291390351550400c0900c1c1912501c0309101c80e0012100c0c4202070b91110300500c1182e40d042e0700c00005007440c03117800382824000d907000c07055005001490800640c6d42e40006a495031801d0115404a0135081c00161090740b41c1030400207035000612105e100b9041c00000038604c43c0d600300f160125580c18400b060480c0c1996821400342601801c09410042e034660a0400c6032024000c081c1c500b18a0038000424600d0740c8181410440482d1203240b084d280ea0031060 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102766591 1250 102765341 102765367
    0x60c05160605061309050114090a0305040306020a05040b270117040f020a1805090105060a08070e07021c055235071104020913021c0e03 60
    0x4400258008070104665a445010a9112182000200c640d904114010040c0b05e010750045100c420454039001560350780c2c4940580c0d420304443c00900149040104001050041e030281007610320303600e8441c0c5001d9596208440b01d03041242003120316010103040318040e6a0851051142810a0908002421140c15038021405000303101404801b1520a4007045603114603290340501440004c1410b86a4554603003802000b040302e02d0743d01980b8010215002d4a40307241d02d4021190601c00905c19181020401040980c01900d21000d52081c200401c11041847d200552461404d81e1480d40b149403681c01040c0540340145960800300204c000c101c201910070180004842442d2003072126040c5001c990314992034204405401c1c8a01001e091001c00d0004142440803007100a4154104468001070240c0d8490100300505490043c50031800a0410b6006400b1032200241807100144182c031444007a60f0155111040d640e285940904200300d0700d100e14080201c4602c019824022200295 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102767841 1250 102766591 102766627
    0xe06010f06172404240e0a05040b041209081c0e0d08090105070c0e0f01030203060f0906070804020d0609060203060411190e150406030b120d0207150207090501080a060c05 75
    0xf55054400301101c40305900e0355082103032041c100c0c00f505076070300c0110b0785014440d0710315008131000c810420012a07540318550040ca4040ca8214001d0001a1642d9032080400010303443c0c030105001c018500040e85060611480d10b1004090002c03490121400000a001c01d0b0301540c9030f44284045144003010a5242c0c0584440361403c0c00c1190b80e0f080c5a0421a0513000a5804030100041c40c00400034007103100a40d09048078800d038101e402c180c85070106d02e10861800c484140080c0d1052000881f030610983c8402d401a00241c005c1903199010b4560341c042c2c0740b01850582d00c45400106005550030513102c0c0940da43d01410300c040c14040340440207405203041c82c40540410064070319005080e074500e00880090007003110040d940d2551560040c001d02082905144103264001c0d201c01880e4010951011072210365020b44505800d002804801900c1100181d00714400d004012501034098400c0b28080d1007420018000c0304100e10f06501901d40d590f1075141000030910086142d0602a402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102769091 1250 102767841 102767881
    0x11211030a0b0c0f09040e0304050f012307060209030a0f051b0607061d0a0b010315021213031e030e07051009090c02030d020708090a050603090307060207060e06010f0617 75
    0x525079071300c803000411426020300e80e01268414a41240701411600000081c0115074050341c200445043c0c40006648407403000000e400c0c2c810101608020180051000f044036030f1144000509200052000c80c0c504101c0c41c00031118105220302d1032040c0310080003414007800d44210804c0d100340540020841a024000008092030b4503001d895414000d5503071865200f55410086a130050598184030103d40400e00c802e940f800c900c002d5001001c0d50600032600c1c0c11080600015182d241c2c4001c1d10303d1220030903825002c00c100c1c0448004000c02c082c2125440034401d5901050340d80d80021468100703070490340410710469507003c0111195400401131403c4400b030400025080c4403954042e4110311900b0814030380c2c2c4e48001804410000c1d4031014100040b400d407585140c16840d401445014801900c001459038070602c0b42c00e000803041d4004044282c403414000c07c20b04412540380d450000700303811501c12a046420306104e01c0358042891183c1c00340761000c0e03a540e8100308116814541030760ba0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102770341 1250 102769091 102769111
    0x606030925030f030903031403012102040b0415050f061216270e07020114060613080109051f05040c03030f050c0d09050406060201050402091f0e011211030a0b 70
    0x801207108254040495004540003a0003118401d42d0b45002807100c08980011404a10503002d03091030140c81c41c05417410781d04008100400f00b000d1000b64a900e40760303002c0403a40142c444048011030b454902a5001482e50310042e10151420b050030044c000740e41c803650600a034000c0c801181031030f000700071081d0080164542c0410000501d0300480d00300c4441140b50030080002c0102488040071124440300b280d580030382074030594448020480c2620302440310641842c42d88000b10344240f40c9180182088902000c8c6084159036078020785003901c00c24941500d45801034117154003d8000b41503207048900b00800100601e20303059842640328400b80c00b015003040105c1861407010b40c000d900702c680b180c5036181103590008070200002e15080c058000e0b10b000d1400d0280c00920f17a4014014603001e0344c4e008101c121103585013021408603240d100d60342d440c0d0204090340000c803214800c1c0a113000e04140703691040c0300486c1d41000050355400c1c60a2900035406801802c001c0b0b2034000000b83c10500c107032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102771591 1250 102770341 102770383
    0x15091b0905100312021c0f08090f10051f08060f0105090f130f0204052401020a0812070201020405060c210406020a020f04020d1a03011506050304060209010302131d06060309 76
    0x11380403440c00f0901d90341900c00d00388051542603900e82182c0c0003614104642d6a800e41c2d583c82e030240c242c882046108020041d0b218001320704481a054001d664801c01100800c400d00041d011018900701c10369001c50102c5c0c2140080c854012800510280904010303aa83c18903410b2100382070700312900003081280d81e05d0031545007004010a0a4007440e420340c00400502603402d10120000401d02c1641e085c62f08074162264403001035002185152107203401c00301d29400c00c200f0000107502440000c1c5140e086560800002c0390aa54400140104c8140e280040c5020407200c1c09144003558185403c0500c00d0080c441004142d6000840e10300345503050710200b0313014a1761008a0043d0056001003440c00d8103010f400012903030f41062103003a80301c0840c0284085005040c0d140c0241e0200c2c001d0f2000103070100001004540603400905801906160044c80c2004030403001c600649113030424044041c014180480c19001c040c030250700288100d0701c0310b145040094406580d6188101c00d80808400d01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102772841 1250 102771591 102771623
    0xc140a030204020301030b070f080c250515010906050109050a2d061d1c0209090f011815060807050f060702030105070f090602010603080304030c15091b09051003 71
    0x1a810801103070702030025522940c4919240d155004100d400c1c500107920a0307911042c3c00d1141d44024006d00ba07405d01039280249074116480c014107040c4000c02420b44a00746900000e50030401040003035074508d030301d460039410004858240c46959204e281048480c6600b8480c0b5601d586549044400221015088040c1e6100103160030602c4101c456468812078000102250807006880705801c1c21041d0100760110301040101190740e84a805d0084a043c8082100600b80740981da504081c07194102c1e00c2500358011043d081d01c140088032004039441500c2c090800c000083d8001500e20410b0040c8206806d00a420b950341e0018401c20b032007058019280c0507140c80b040c040b1a03015801500900c071500e01810007515a140c821003260000b4081040014036510600c208002d41e68070a507440d01d036844a40b0111780c140c1d0304800642e0f9040d4043d41780344020a03107102e80c0c26014441c0000c40b41e0700010300c404240c1108194005d8401609002c00c001302620041c0d03100342034aa0102d11900030002d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102774091 1250 102772841 102772849
    0xc1b080f03040e01090209010e040f02030601020d0302040f0b03060d0f050a12112802060c0105010e180a0305030c0d1a10111903020c0a0e2502100c111204080105010b070c14 76
    0x2040b052745411074504906400340708031a170011445103100782c00319241282420310440407807080e4428910a42050304052052070400e0b00295003000004024500c0c9503410f40310200c0180404404035600d91101c04030300b080100c80e84075900091001c2c1410313034012418042443d118044071a10f10300107000c10200e95804185200414105a0040c2409858082c40c521040c02403000703001d40c11076920004002010350b41881c440d500756501c00070242900d0303c00e40d9001d075aa03801c00b0300405a451414410442442501d120f000d12000c050104010722404820902c0700d504644d010071b00401900307441c80c0da1080e20020b0f0000c24008083d5840c696800c590500b28103021100b4034140d4085c05035240003c00c0c2d807016440500030640701d071100a00f0713503016901c070880701d001c060076001682100c41088660703080d036809412a042c007818501d041c17401d182070380d038201590541f0303c203011040440c040c80504000d00c1420b014111000c251850842e642c0c890200740c0d08c4c944200144001175121b03041d100c0d16 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102775341 1250 102774091 102774107
    0x110d0302120f090a09090f060908040e040501090b060105190c02120708160909020a0501030203090a020a120b0901060302152805070605070807080c0702010c1b080f03040e0109020901 80
    0x4581d905042d01d552002c0318401e400d6100001841c81080400408508410540325941d4503a901400c48080c0a1156039240c01410824106480b50070b400d000005071200c00321800c030300c41d502c01e00000a03804064982804c044801400782c03030400c00e0610400314056802000c444401c07140c1c0c149460401581d00c009000e1313603100c80c1220200c0c000c500380018802c80006000011640b080708819010340c0710748071001203441d031002c00782d4070401c07000b020042c44d4020740c015600700d03401400756044d46080d40c0200c0c40a10082d4080002c1d1020005580c041c00591002c0d00e801a000d07200a000052071a000600000059000c138401c0d840001003511121520801c403515006061203018000316504c400600380c2d401c099015a620350601001440c400d21076000c03548101103644030f00e116503e40c1a81300d070302d80d0402e44040741800480c8808001064100300d00c01010003107240140c200c242040c50701c50034048140300b450100e41c010302003886464900d0300c10f281959a00c060041e121701c551700c0104c0b0035076 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102776591 1250 102775341 102775363
    0x60a020d0b04020712090b0c0312040614010803031905040c15050c070305060601170f01060323010b0910050703020a120e0d060501060306150c021203091207060807030504110d0302 79
    0xb40c8002074036810401e030640c2008840a031358480d0000750340d5070081071030203100303000c1c0d451120f81041220001d05490643c06036081405004006a81d500c5404004055402070300851500d07400401041000030345840d00c00c0c840135402806000504003a512000d6900040c051181200c0300200c1c0c07220907d100344140c42220303824008481781681e9078141546c58a000344e603030303900003803244c5640074403011208030304c500840300300009481076803038000101e000340354100041020b03481050000340509030100a40c1d010341a0000c015903286d0850b4200400c020106040800b4402c003070240d100803d030003043c060700d8640c1090b00d810b81c030049807908546920420b49032540c048200d400d01c00c00e00003150b001a05035201d81e00d0802c12140c40e9066020b00c2d4520001d190001160303000140014180b00107a40701ea020a40100d038108901100010000f03a08140030310700c640e1260008108250340711144541001761414108200c0c02c20f070300c07400881415900c00501800c414840682018820071107103d01f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102777841 1250 102776591 102776599
    0xe060103120201051608061009170c0a0518011208190c03020607020c10051e040b07030305060d08030115020f0303090705030616081f0302041104081905060a020d0b 72
    0x540e124900740d210003482004110043d844c0400282c60450329811503c282c54040d2943c040d42e944003800c000001d0f070044400c1013000051000042d050144c03c40500584003580003605007012a102800f0307035030815900491044181090f0700a10704440c55242c1c0c1590454030400c1d44031100790406500a1046010182d510520960752194040d030013510000514420740c25200d09031a440d004076034580712086006e40c0140f910134401c14a90040d001000003090103010080c14030700c0c1c8180600c0303035002075200716840040050b181d800c040d418414254040e6044810588402c425201c90443d40014000c1411740c1c422109140074042c000c000c1101070b140207804490b62450044556921400720344209400f03072040b80042074103c0071001400304503c0690350b8000950fa0390182c9002402500c00028514506001000c00580c13190302990803460030350702109035910300e40bc400c2464820b41854030304070030300819492000100089580c942015090a02580760400c02c1069030003800300258060f44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102779091 1250 102777841 102777853
    0x1b111207030c0b030703051006020d0c03030b030a05030306091008030d0e0c09011815050d081e07030201060e1302030a0b09030d060e0402041b050d0522060e0615010e130e 75
    0x500b0f04080042d48980c078541d5041c03040f502d40044112894030203018500150f001042e506000d548a445c0010402c0c0c00307482e0215080d61004003182c1030140e252410740749a0400010000c00e820b00c0c40616810903090001c008010f450890703096140d02548940030b4080e91100180400c9c03040412403400c0c42e502c000c024800c41d5a50b03008a6410101c0d007031003400710a040040e08140d03100810051411070b172001d02641820289a0345a400e240d00900031940403185409900e00d15110042c0580503640c841c3d00002017041c01d10004d4001401700521000f007418101ca0a4001038501107018212240d201004107055199150f00c282140540e2104069407403500d80005030511007a00d40328050350080c0c404002d20704950305050019240814a40d000c20302c2002541d08200d804e910071030b48007403108100004510140c0c1070b030b12075010307654090382c0881e04c442d1290036924040c420281c12080d94040d0782e580012400018040c0341080585903c20780e4a4108504c900e025070b000720a42003464029039013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102780341 1250 102779091 102779099
    0xf0d021204113304090f0e0c010e0105090d0804030503040b031e0403052b0c030f050703050c120402040b060a0203030703060f0501020d11070b07030804121d09041b080c011b111207030c 81
    0x1b00504020010f04100d100c0c01082c1c012550249840b02000001a0b640302e02d000c0c87e54003440301d52000401c08442c03101e400c0000001003035013400903101400c080c480755541d90403e030b5240f50b000c840f0301040c581c015502a0174000003d421004075040034410300a48001d040340d983c1c00b00c00000f51359605082003810651805c2109901d5440040352107140380c6c1c100000d0f110340f9011001c03a50100e910054038002008187e4801c1d403422000c0c0e500c988010004030b0140d20726008a0010f8000b5110781015074404000e02801d55098000c00010700060045259140d02d0480000e54401d0644110350034840c0080e00c6810004040c01000090a51400626035602c3d403450003c00c00312085405541854070f8a0f91840c00324441e504904801040040070409814007800700300170040f01a1088850950b020030b81e8102c1c2c402c000040e0000d24100014000454003440058207100e004030100c400900006166000103a02c0807400d5002402a6039007640740e11280c450b1032606000781c00c050a503101c5088001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102781591 1250 102780341 102780371
    0xb0d060b01030e010615020f0606090106050c0c0a0902030a051312050703090b040806040c1a071202150a0203090d030908030a0b22020901110a02010206040204020f0d02120411330409 80
    0x302107143c1702d81c00c0741c2300d80600000362070b11124182c80c815480181d060042000f5845240508030b60401e02e0291641c1d4040384d000500c942c070095001d0b180490300030007003020702040c912501ea807011102c07a54025440325640c0701c07095006a0403082c02070010129401d0107040c03003207401ca0060180d14882c00d5441c1e44424045544603011142240e900031403200c04654102c49416051241080e2105e0034280742c02545d0701c0141c0b5103104035840846c41075041c15074140310529001409400511030050780c03402e0200300310703013010680c0c0195414142064410303000101442c00f101c0d030140b490b15000507001c400100180e88041d0500010040c45000b40d02102164041e90050116036000d0301c501092500c001c88140d10340d0154040a40582c100000040141c2025001418800e803a9001e540c03400c214000391030100c1e003141c855606404074410402c410400c540c2c92190741400100c8011403034030140c4901c1c0e1070750810500c001c40303d041c049040001405600342a5005482008020b00044010355121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102782841 1250 102781591 102781619
    0x20c0f011401080a170d0b03010f29090609070309050f06010608010509090a0b070302090a090b1801050a030618080c150a1505040e070e040c090f0b0d060b01030e0106 73
    0x100101c9030304100005a00c0d50020307100c4001c0e41c1c4600741040c88403440b070442c4495004103c882d039000f51504d10300c060750358080c821205002100b0070001241040c00c0d004100e00c0d05041d8100c9080c0c01d05407401b2120391783e00003038281d02010441d80b100050b0b0f00d00070f048025044884000b09607102d80b100a4a8001000c14007034141c51075070342c0b0b079140d80c0c1c1d8a20030460300c60019030700c108450b0403000e0010b001c03074a0b40110643c40001828054035081d055400300e903c8280d590720003030b10a130342e51546c14401d1401c0740d070050f8802181c90410501d941004001520940715120050102e41e0740c0c0c140000f00502d03081c05094031904140260744400300300310340c10781701c60740e10716a1402c0c0d42c0c0715000207160740c0031485112109007208802a64a60409081c44000c05c0c030000c011a0034420000002130090b800b0400510071407154119074211480c240c2580203a0301c0b02004403030a03906003055002c881e03c680704008545c42d0441000300d001c1000c440140d00811440e1114403140d401c061300456031401c42040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102784091 1250 102782841 102782861
    0x5041716030803180a080d09020d0212010e0105010909050c0d170d0f1b0503130507030210020c01090609230f1f0f02060105030c01050a050d02030f0a0b030316031101020c0f01 77
    0x603655015001e4440c1e6145c030304000c03000782809400d00101200201c01d0b84690b08543c8042e090301190307000c607000116a1180c4070408a11a91541e01100000070b080c02a18018542e580c014410450141d030340c0c6032141882002203000340062041507040c002008006002d025660b4000d9641e50040b801c0c05c00500001200ca115840c00c140c0b0302c80300a000f06000348940156a80e070503040d0340b205029141986442c060948807071103a0800800566110001c0c0701950500f60020b0820740320b404005070002903c1d512030780c28490303180010451480c0c040400300034904d01c01c2603100c00d04e07910300c001007114141c0f54000350080c0661061910403541002c1c6090000081c1d1162607100c06d070000304a9580000b4086c803a09504940480030003540107101a00303005100307081c11400c0828011220b0200e0700229140c1c90948220024070804090314403c88064041c160041c51800d166041400380c64200c0d00c00c01000c201007020f4510600b0340a42c1982d4900e245401510540c03894410103038003178204441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102785341 1250 102784091 102784111
    0x10021c15050a211103030408030309010204170d0915050f0c211309050a18030207031203050115140d060902031906031a0907030b0403080a050a020a05041716030803 72
    0x60120f0110328040300f5a805035641404083c902001d90b550840040840f900f07540c26200500012075006014805588118a00000140c6407850007542c0131180c1c1442c43c0c1405c158002c0312810390300c564004456000d0318808059400f800401600466507403007a910540200d01c40400d24007040040400c8100c10594988c0302c199460010702084c0010388114101c1080c425035840040001d0041504207641c000b40c01d00b0001609642c40003000e00f01c940c00324046005800001e0280b00b08400d00b03640e100c10300650f02d000c100641c18042c0301501080d00d00a1003080c07080f146204007141907400c0441e0340c0e941c0110006d101655071111800041d4101b9225900701800560f2681401c03190751150380100c2e5000035a5840402c88000115114940a0300340b02e458090f000c4040041440b200701c4034003480c400d6441d1300309031403c4500201280c0025160b41d8480e40100240071a403540b006c291429203400119142001c86c80c0d119680c80d001c0b0807190504045e40a190001c20300c0b10f48000f441c0b003486801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102786591 1250 102785341 102785359
    0x20d14060705090303070b0402030a08070c0f060e100309050f010219020c15040509101e1404150501180f06020309120606010917010b180702010b040b0310021c1505 72
    0x300c1c050380d160281000c0e507605503105200c0b0714042603100e0300440c0c0090001d020b0384c6422040351111549035011200558150f0140c0004000340c814600d090f00c02040c0500c0c060b00c80c01101000120760882820300d8070304060300d440305882400302c00d2143c022411403000085540354081e1250800d00120f0704a8540136000e02c1400c0310032800c140303a00c40c007000d04a408491070981042d041050046000d01540490303400c0b100d000c540040c08019001c8040841c521158109140c118240b6151501a090038040e46c2003061070903810308000900fa05803002400d00c0000105c80e03529015203d82682d0141d1800c0c864904001510fa0700400105281134098076208206610541d803c0d99902042d148180040d00040e0100700e80b5400500c1d49904040e01d1001150340c0c404900001c0c02d0422980b40c02d03140d00000c000f0300c108107809104541c500c030000d44041c00300c40503980c0040d449440140c3c641414517000030f401d143c03440c0d03005c0080da0350305104001048203121846000600560328040e181c003801101c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102787841 1250 102786591 102786601
    0x180908091201060501030e03090d0b130f05150105040b030a0213090206070b01030b010605030c0a0c11040203070207050103060807060203030f0a1d0604020a09060b0315061303030e0a050105030106022503020d1406 93
    0x1000325803003421f01401c40c5858010319030713402484500041811080344c60700340c6180000f520324040b00511301d0285000b4003542c2c500e00c2c07000c3d42548042d1d10080c804c51a00c040c0f0003403a10007007a81000a90121482d4150600044902d40035280d8804000e51101c40010342d98100f0aa00e46c80c04e040c0ca0041c03104c041c1680e2110001c1c1ea0600c41910020016001407143c07803406072160174480d42c2203214cc1c444900300000b00780850103a800c01d440104c050b0b042650300340950350303043c401c2d0f2000780705030b600070800c0906e0103202075100d2001a1001460b000d0307240011b5940c0c0391fa50000310b80041c042c0d000507000c4040210765925040c040d14100c3c0310710b0b8406000200c501aa004074000c4e606000213651840c1c4510441130740d0700b00320404140d0040301c184260003250807540744090046000c2d46601401c079002c8820030810401c0c5400c102d044c8038041c00140252640024220325205101141d6501c0400c00d03407174030481c0b5500f9400207500421083c040307803c1109044119a6004865045901070b03150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102789091 1250 102787841 102787843
    0x60608030703020a120509060f090f030c060f03060f0d050307140a0b060d031107090b01030609060b03060d061e021803120f0a0e041d0f07180908091201060501030e 72
    0x504080580141e00c402641d4000c5551700ca10f50454100d00e080886c03510b00d415001c0342c480d800100c00e05640342c02c0800c2c20025400c004418104141c4114090416900410001581d070300407401c200c17202610102c00600c50361210605401b4066000707103421a002c1252074030380d81c1c81c3d10000301100c0400b0f0200751441015070000d130700ca01c200d5019030500a1656200144910b420013000241d0800c440c005824000080074807242001d17100f58900492201103590014003555616071080031800e10340307502017011310000e2050382d800400880d08130a1850301424500c02801a441620780c50102c07644803521442e000750f00034180c1c00d0b80d4008600304802c02034105030301c038480507040041c411010049440d915100d0001018a10700740d051180d800185800810211381c074542070840c450440c500ca040e59040100700303080c070207004d040c01402e20508006880c00e032303d91022164000d55898564140070066100b00340e5541c08001782260540740524072030345001c3c22052007405d000c40d1400b07201a0403210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102790341 1250 102789091 102789097
    0x6060812070c051018060807090b180616150f11030708010504020d1d030408060f1311060c160f050d2004090b010909050d0801060f0c03020313080a06060803 69
    0x50084640203049280c1414403d2501d0f81083d21030800c0020a45080d44805d400381a801030038141e0742c0d1790b48910701050040c1885a81d50409440c154041c090300042c0340c0300715001c4481c21000c1d03502c5601c070403544281803110218890300401c0b041000684d00c0810511b03505c002d01440c0c1d0200e060011140742403824405100540749000041c0307500b0700500c91070a1030340040c1b1041c10316150015181c0c44c0070b84246000c41903d0443c1301640c100040070807120b00c0801180e80c03c90441620074515040811141100390301c101e100a02120348032001d048159104010307240c2181d130940035a042c8102c1c400709040c0314629400741c2d00101c2c030911b07170105050800581080c1d40030341c01030b62a0081c2442071180d0f000701c1c00c08030120754001e803140c240c42c00080482c2409802001050b5010030b2004d030305c6c42d200d806c0c8000d0041000402c40c2e40380041065a038048500c0e900d0300060b08210b502480c2a080490031403103401610031088400d5080068031402c0003c07031554060042d18200300032501c490110b61070b0300c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102791591 1250 102790341 102790343
    0x1c02040303020c1e060403031707020316031103040e090f0d0f0c0b04020f1203031509101511010203010f0905010801090f080c0c090a1b0923010905030304030606081207 74
    0x41d22069a001d15810304400003d40043d500304c244040120034000200e041d441908101d000a8010701e8003808071192142194005495002a504052003200c10441d62203600300050200180181403030b410354800c2c000c0790060854801a0101c1d03180244000355900c02158050803a4810490340e580d00501c5504000c0b0502000d43e10f0b4008800c003a01c5403d0407000c0500233a9000100300d02c03986084c1d8a18000e0b42c141c20950000d56141e10704009800c8070540581e25817030140d4414810000345010f85180c020030340b120a0000410190100d03001c444a091801001280b588000000319408100c1c4580ba8119000404207100700c0c0e0720703652440e0980d414684c00500c02411900c0200c0000d603402c02810000d15101d00301c4415100d094001000e040d0145d6042c0841a901c608a81542e1200382014207051214206070007030601e0001c0468101e42e21030031070641100c410391a0646c2e0303071141c00c00030000e000c0101100e8565403282003e000518540c0319000c6148921510105242ca600d42554109 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102792841 1250 102791591 102791593
    0x114030a09020f03030a030b011e09090c020a0f080306040c03060b09010c293309060d0503030f010e060d120e062506050a0207050703140a0b0109021c0204030302 71
    0x164032440c4150028003094141280e0141440300c6143c000e03101040905a011281d03a00400c4c05846c030301c009080d8518001800880e900e6403000d00010a4200802c54110b94a00740000f509610b0b500d012424086810001441002034074009400d10600758040e50080400301c4081040ba80606016000c841c198412450104014403e4000760342c000c1c0b03d020302c010301500d00328144034688600780000036a81d1990000c135803d81e00a0141e03009901d60351442c4050a0002040c0c1c0b03600d103c6d1440100454102814420040c060000754952540b6420017245940407007103e480341001040e08002900900407420400e8440001541c0c5151401d441079003070b07800042c000c045011800084986038941180d080e0050400c2003081000190003980c01c0c0c58055803a00000710300d40500e450780a42c3c00c080c245081c2c0c00d00601002c008102c0106207901141ea000880103410031020440505080100c0c001800c0a521080001001d0009070001c000c480d6000d1070740f4850045000a0350201d004074000a001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102794091 1250 102792841 102792847
    0x7051b030106060215060d14010204031a010302030613080409140406051506030c030403031e0212010b040f05040f09080a0f02060c0708030f0601091502030c01051008031c0f06170c0114 81
    0xa03505e0022000c0c1e81000c0c025241c4d40f0361011079140c440081c4030038001802282c0d40010100f05005101e410342075070301d82d154030400c0c482d40346400003965040c000c3c0902e80119944190842000301f140c0440d401000090303000c0c440038611950028003400100c41c2907503600d041c01e00203001e1780354400c80340080100003883e040c21a02c03150350070280754000410441c24165500500c085d800c42090900c441e13042d141c9405603030342042c180440841001a803101c1c0e1901c07401e1005000c154000d0541c038017980e4003518000b840c583c025100030003910509501501050700004e0b6540b283c1d6000b40c0d4991103542680849140c0c0d04d48411140030b51049501c064a400742c2800420480018100040d4110805240c49503105481e00f0729030036003044d807110a03409a0300c0012a1507140400b130280940c49846030319030100c03003071404189030b03200d00c55066240381d039202c0725000210700341c000d61241c6d00002c4410410031010761150400303c988452400040444c0c03282d0f00c00e074861584520111540185880d9425003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102795341 1250 102794091 102794113
    0x9050303070515090f011505030f070e1302030c060406030510060c0b060f0301090b01080304080d080c0a1b20040b040506030a06050709050301050901021b2e06090207051b0301060602 80
    0x4031680014014010a018446451720b016000b4004d200e9890328070030030101400d1a1504151501e5600b0103081d00c950044081001583d1800440075480706505184a465090303030701c0000e00780b800d00307940c4541c44507001c1004200540d00d0b40c01184214806500500895202e22064030286086480144003000100006950f4100003000c4905084090300100304000700b80d4a503480d0702000d0300a07080355400460b08001405080050780714140071800d1045003810f110025801c14412181000b017804001001001040d840036a440d1440b900000204d0560100d43c40c0312101c800103840c0e0511440c140700c1113405e07902d450310030b05000c3c0c10000c0042201c90495034468014007402005202440749074000051162801c0c01821b210300e944a00069a6450135000310440441640000742d85502000d0030b810040010490401420100c00c001e002c5807154418110107040705800c00328820340003080d0f0804100e40055070461b4030013600b000c00c620301d920700281400c03500603102e050300580c00400d07124 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102796591 1250 102795341 102795373
    0x10f020f060403200a061e0e07151803050d08010b16110301060803070f0c0807030804030602280f03060e06030c0d02060705031909150806040507030e0708030a090503030705 76
    0x2842d40581014040c030300b501c500d208507040950441c821341d02147c854580f06214008681410345641e54072400300018070f000e41d002039a4012a002d00f4802038400380c2c1e201001d500444800d4111424102010f0100340caa20303065844100c40003101000c1540c003c00841c030690918103640c0424a80221025481d605455000d80000c0c45094141c055507200004650782c001030009014290244401020272074071131401d11180c1d102540040c00c81d41000c403062000030100c508443c1200d400950151f125150012085008040c1c5c07000b05081030001d038500c4d000f0581128440b44040f0054408200f800d41c2d6422940800c03104981e903980c9034000400f11060f61915403d080000c1c0d0020700068102101c41c0d03103613807669124040449203074454144103108541e00c02440005008911306c09500034244443c082c146810190210348a00e40b01c10000d13a950744254400740000d00d1120440780130756500c5d03640c2a00c070307400169101c000500980d404100c034100001119a032507840401000481110b610b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102797841 1250 102796591 102796607
    0x5010b07110406152c2818050108010b040b0a0501051606050c0405030d0507021008070c0204150f050a050a050d03140301090c030e0d08041214031005010f020f060403 73
    0x2050b070240d910003004c00e15540316211324000c00c0f1252501050b40254a4401800d411086240d50b201e0145510300c1440d52101400002121400110100c10a030b000100d0485480103400908074420030440c0c10402c1661782c1c01aa0403900103070002c220b41c1c500c040070700040c2c1d410084e40316085180040c04201c9c0d54030403401825044d00034200c0010ba25076a40e1004281c8209682c05128100c0c0401d0501c81d070300d070900c04d40034a240c45060080c6050f01c29404603480122883c004003e11628400041c1c1c1c480c05401c82e400d04a40c010401c2090003610080c04514082034059900a0010005d0100d00c600f044810301e4280c60008124910043c0790604000d040c0d14164012400c1001e1a2414600583c2c41d0300654040c0c001d006001c1117040152100608032619211034019990001c842014502d402120440e00f154000c168415181001c11094170b0801c01000019080c000000070406031100482d03910042d5a0240c0c1c8184e100321001a0803030f6030303071403080000c01503401650218000900940f00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102799091 1250 102797841 102797873
    0x180601050f040b040305030405030d0203030403091a071a0108061003020a1406040f090501060e0f1f020f0a0b0103050d0816081906030602030a14070c0809030f0d0f08010905010b07 79
    0x1c403403038252142c0320005250080c2d0720440e42039001260521280c80c0504c42c40140d04c0d5241300079411440c003902c1c01000c5d00f84a1041d40c92480841e180702c50b151285504a4020b9030300911031410b1914519404030890b8000d2007140b1a602401c4041500c400001003414200d90300204031180c0d10742000703155801d50440b075140981c062010840081c6010119030190f00a09403e100021103624096001c4c0c1840070340250b551081008010401160b91030078039240e002c8030381012102c0c01024440d0282d141160a0b03465081900c50030040504002945d10b103076041e44d20031001c3d524803010814043e100e80c40161075521215800d111010000c502c5042c41030761160b580003001103100c02d494040d400b285e10f250030544041d80c00204000b0200c2d058000c3c000c071a01003400c0d441281c03401d4100184050105040240101d800280b02c0050341c0e0200100038580f082d840c19078000d0714000f1809840c1542801c240408114450000030391020f00344039060403200e8990b0014076102c413959411892500804e0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102800341 1250 102799091 102799117
    0x50109020a120b0f10020d090506090d0813090e0109020307050405090d0c0515070e010e01110c010e1504060305010302010807080103050a08030901150807050f031c03110d0f090303050618060105 85
    0xc0324811541d17542c00b00000788001500901100300702908000c2035950303150001805100c0070080c0a800b500c0d2078404000042d004640c6a4442080910050100c1825400051401c0c101640005075003010341c050000117108408403100d0607900c03018041590001c55900c4101d4002070325007480c080c01184a00c054030310035401c4c0c0740054011440b441445c18242c0300d03074001903480d111882507960801700d035800c541424240b0b0840000301c0ca401c1550b5044031903290341000300388030340e081050301c072022400c0f0000704ca200e441e508d0340d0300e5000c0180108002d22040e1700151040000ca82814028035119050b00c3d0400c01400303080b034094a4020b003175030014150000d15940c17128201c2d81c604500c00050094140714000d0050785181c40c08000c8100b0000000038030941201e00e880d030a00d00ca41c0681d207111161410086018480300300c40103400c0c06414003100030f2074144100050500025803120a62034402d440401060303c4a1040c06000709041d86c07841261601c0d4408511f0380e45c0201c010f4141546554 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102801591 1250 102800341 102800359
    0x13020307090c020c121501061d03010f05041106120406020a0e0310050105030f030a050d0e1c090609240305042a030b0106110604060b040b090f0406050109020a120b 72
    0x1c1c8450003100c41d40d202c02401604a1001c0c1c44040ca045100e120000d82000c00030004203690400c42c10b9468018815030003441080c15400400c200c00c0001104400c0005008018075005005000090030007101e08441070815620341802c145417180641c4d40118049444e02d200e03036901c1e075410000b90f005100d9030040c0a8903850310320b1156000c20a030f04134070b00990b0000c02c1e65458030043c545407100819251100f50000d00c020280c0c1640042070741e00005000c50041050401c001026040c05910091300c2c6c1e841211800280e0b016401c01038990848680c0e0317880382d5141c0d903103101404481429903002d1103c80c060301d4072124102e1003504450f82141c003481c581540244207009a081c40042181d0f868400c207800601002403110b54410746005102c45e040c0003990565484040b0345031040100000e104940d1602079181c41d0f1266840385001003c05415204181404c074a01140d10000300c07012904642020004500c4c1445030085d07032182d50481c0c03202d200e6444600001000760680c0041203400c0b2103d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102802841 1250 102801591 102801599
    0x60c0512030613020408010207060b06031603050c0424080c040f03060b0f0301050106020a050c03160605070602122707050303030106030b2202031006140301120311010c0504080c01031413020307 85
    0x1504c01000103003c80000140d554041c2d00d40202a10710040c19a0703c0345909008101c5a48581da102901c81d9146280c005030340e0f640c41000040307074000c54100c1c10120205010311800d10a01800c88445900a03484040300b40e500c6610301031301071141e80142c41344544041c108100054840c2c10054242e40003c11040c00c0e0682c4401080c00c54909a00403001640700701c04802c02e0150034020a00109000e9000d011501905010f4429131911841007400f040400940c00c020311140c0c0c0c1c1601d40e01c0c14001045032607401d04900e0300d03c2c41a080011800d16001c00d66203424400c0002480f1411942e0181c05142036038a0701710154014080780800541000200402480d050f4034040e40e400340003500c070310058890609403808058961181c120006000c0034038940c00c20540b482003564112600390001401c00289407800300c070600560000044076600300303501292865044809801981c0c00b800c00c03521401c0c4103600450070f480309030b20611754094800000c1201c6198440c04034444a0000c0c040340c640780d41e6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102804091 1250 102802841 102802879
    0x4150e031905041802030c0703140c030c011d0f060a0e030c0a050d1403190c1b030c0b091902040207030c02030303130507050114090f04060b04060810060c05120306 72
    0x1d2200d40300040c0d40081c2c18003048108080b00c44090131111021400d40c81d0a0341018035912445002500340071144402c58031045413034044401000da01d0003603e480d0004440014041d1005281708010b010154070303100f00c01203001941110203060400100b10070340f65525400f001b05818034428515000401044500c44c06c1000f0b01000148034a0050525000303c8900516001882c80e82e00031a040410612108080d4001c651041c200007080004032140b20f02070a40d044206007803040f0501c99850b070300c007040c541c101030240400e40c081c904140c455564901d00544510508141c180780f208000f9010000d0f0405501804030b02d4070905210003c0040703078000038a542c00486190320340c05c14180340d8034204031703081c8001030080000b0700b03211702e5444141e54907030720303a0051605060003034292100c1c8801135901c5402c06802020303100001030350745441d0074000300001e204489101c181e1212aa002071100d10503800c1880b0315811402500703040c058400f02c1100c640c00039100c2c1da07003d450b0090b10340318181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102805341 1250 102804091 102804127
    0x29160e09180d080a050a0204060903110a0f080606040e010501050a14030f01050f1e070801031506030c060e01020f06010503061306290405090106181e0f1d0604150e03 73
    0x641a01c071003c00e49005000780003a19001001003c41c84d00503c0100050385d00080007401340c0c3d41c040c50640120740c184012400c030700c14561103184401505413000941200208515006010079507083c450070003282c0401c0e00b41c85080c4100c41d048403003030200700290b50b424182030b00e000f01c00500b03407400003410500482c01c0d104107075204030390b4444440078800780d0300404070010181642441c0c52003071407521440c06404800141301c0a0311407184044041a000380395800308000c0c6900c041040e41c147d4648000404c512001000c450245c480d808075040107003800520075041300c40003001081280d60311002c0d044100303041c81e41100c041d0b4650303240b54080311140a51076270502c02c071011003051805c1081007201340c0ea8080d0119107141d142410502403000c4042da03500718a40c404c0c1c404502c601c0303595510741410740b0001080110900e00884075882c40c04a400000d41401780e520066080c1d4043194005032100c40940d8000d00000751180408118036103900b114140401520a89003003000c0e4000e0104090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102806591 1250 102805341 102805363
    0xe03011505090f01030b010b09030a0b0109021305060405060301060f020a060e060402040c05031003020f01020a1b1a34080703091503020c0703080d0929160e0918 71
    0x381100c18180102d05008061a074001260070042c3c8107545941c89004848106025072501c141e400650350a02d80c904001c03000e001d035440f141c00c1c0010f681d03422590000b074015480310030310030300500d10004952401394259070a031400100340c40e15503440c000d4290b503042c1d07000c01d03548198024100030001140f143d109141c000e10360500644101e00c3c051041108407031002080d9802d111050041c4941405c411302c000003982d6040e603982200c0e20301800140c2c034010742c800f0018004a480c0902c41c4804462501c20400c40d107000000221641c0d14508100d018001c810042521466908400ca210b42a0b01180305000c2001d68403411554882d440d80a041e600000054001c1800200200000700440030707a02040302403490300b1418460b0403844d990b182c010920000e031039444003003070b8482d40040c1e41e8030010342194031000c0c03c543c10b220309a1026558810340c2443c580040c111001407400700c0301da4540c08140c040341d079420302c60040315810404c0070030001d00b0050714910110b880c803109100811400b0604 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102807841 1250 102806591 102806621
    0x603020616020103180506040f02120d030204140105041203030f1b03022d041a040b2206020606010c060921090905090a0f1202031e1206011404150e0301 67
    0x6070900e000140c00c0d60134141c60360414680c818441800f0401c04100039030041d9225410800701000c500000e41020301080c1140c0e40e40c011011a0002ca40e0113034018411220041c0840580d02d0301440150340710300a5200741c0d0800b2200c9590400081d01c294403a150020000c100040d807108001d0a02d401c10840000360000301e03500003451000c8000782c2d022181c40b00300844200740054084405050a80160320440c49880e015034001e01e0a608410192406007100302e542684881c20220881481e803500e00812100800b02c0c071020881d5440801c2040c800c0300c041c1c403203114008096645200521750103000351380d100d00d40d0048104842c004c003503212074410942d480400180c00c1641c807104840000d0188042a07100c03d90400014540c1804204400e4011000f484c55648080c0281c1c1548200308001c03941e4514082550205081c00c0064000e0f54100115071605954ac44015250359402500d110007402060008010120070a4025401c003145854070003050400080828250740b110f80c0c0356090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102809091 1250 102807841 102807877
    0x1803040902030f060d0302071401020c15040515030c0702060901030e011e0c02010b030a0b040221150601020a032712060c02120307050406140906130e06010903051203040606030206 79
    0x440340035043c22604880115414140e1844983d40030755513602a100d13142081000400e038400c00c6c2e000303000c8184459009082c1421383c14040c000705a2540c0540a11442070091400003000c140c15102928859000790410a03e8291503030200070b140c1d00260001410991111900d614414080c000c00250114281c80d5084280c40d003900d034801d0341d1a6200b40c1c411a03141100b0203600b80d4000582101041d003203c040b07051a01d4134008581c03068600800b6501142c401e0100365640ca0300082c0c0d500b600c00060320000032a4403604012600c68011301001303800141030400e40313500e071422140318510183d8200a403a540c1651910f00c04c079020030100050340c820b5901c4030410310341a014410300c0035203412011810f00e507141c900720240040c05a030091604000304010b071448010341840031190695070041c880f40d103030440010b02c00070030111030068100c1202c0d020007040315940907144160540c1d81c040041c0810000e00d11000c21643c200500075604140c03030700000400758036031200800074000f1148440103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102810341 1250 102809091 102809101
    0x20705010f0c030b011409040911060403080306010e010807020c300a0c0e0121020a030807080c01060b1335060108160f05010804050c100f020601050a0b03010e180304090203 76
    0x4a402e00b8920506003c0d0503140e004003c06d40108941d040c3d501154002400360060500036001e80000203003d4010000140c00f1080c009440040d5101d50400d80e80c020500c00b102c4011146040280c80600160b80860014162890080071480e404003c030508007000000e16100c03150308442c0d00c003000c407080d08514035040078480503695907009052034100760761b015454229914030030490203852254003003040d440c0303404542c0c0303d500300d800454018600356141c22260804481c00d5022a08031203c561810b840003a116000744151180030340e400942c04800c40c60a5880546440b80e081801881e01d0740340c407050781c001c40d03031ba800c0c55990703554500620034cd60400c50000e240c65440f01522960003c105410850564880c00a005a903030038070f002005903d9600c0c01c1072821800030b403415440301c403040c804160140c0c80258075071250f409030300f29015642d0ba441800000d0303c3d00c2c01400080d60b130400040c01041d03141811103070061280d4400843c40e43e8950041805e41c1c10940006414a030000300f846 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102811591 1250 102810341 102810347
    0x41103011a041a030d050d09080d050612070302030606060a0c140307050d081333050a0f0e0715020304080708160602010c120b01030207080d050f0f071b06020705010f0c 74
    0x80c43c110f0280311a82580c801c0000000c2c5da0340002c1d4150410072800141100300c01d0503980081986036405088507488401103d64880500002c4400c90f00903441c0246482c0407480004003102101e030050081e0107a52200820311040354006064117050242042c1400c0c0010040c850a1030710074403000245d43c42c0c010a180487c00c04030440103000401c0340103c240a000a00d25207050007a547c00403800c1e01855590307510760345040d804c80d4030784020b840d001c00c8000b0b10006c54104600c82d6001e08010444d04d54681b0004046465450360050710380e00440c1c050115000d2000d800d0351480c03041c0112420141d8817503c291500f10b90303401c0b41d1000d030030417074020744007070000c14803000a00541c0c0028804038002000080004444c54800c4a03440c0d151918480c0d640d001e81e04440c4c0340754000d004076695052503416200681000d403002c103006640600061000701d40500c040f40074811503552101039100042d585c0079490032b480c0c002d030b918075401c10102001500074401c00100a03120382c40800c04529048c030107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102812841 1250 102811591 102811601
    0x1504050913031b03051207030e060405070501110111030103110a030203060a0b0306010510020d0f030209040f02090a0603180308040201021c180801051b1c09050304090609140f041103011a04 83
    0xc0c104100b61410000298200c5e05440c4030381c400c13202d03007901655002c80450141030103900251190081c1c01c01d00c402e01030041040001d6031000e80340c84041800c8400114200c4144039120801c16806100510004d03041c1041e20102d520010b2402118035180d0300003c2c1028010340e8640300c015034403100850b140c1400e020841c01000101c6202441d4240004069182c00c8184241030802081000881c10640640d0507241242805082004200c500c1801e0344029400100f200c0d102c1e401c16000004c549200e405003e00b21440340c0361051640f0981d5400f17590301000036108a043d40036240c800d0313650030068503110007255601d41c0c42c0015054854420000740c0d416821010070781c2d0400d410403100080544810300c10b0340500711059a20401031142e01c19492a0100f504601401c0c0308904080c008000003500541d000e04404220542d0340da41d800044865040b40c0180200c00035000490b010710035054180d1007805040c640e02070b855000002804c5a811004524a02d20714582800140c03d00e4810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102814091 1250 102812841 102812867
    0xf030606050603160302030406240602010f1a01080405010f09121704050714030a0501090804050a08071206021602130c0f0801030b01030803071206080a020114070b06150405091303 79
    0x40d46145042c608140c01135110040c070101c0516030000b000c10104103482d40b20003802e1640e0607900c00d4070450040400888440341c0f050400541c00c11035010102000d61048076506250509040304800c100001590030031002001030b1042e546e07840c3c0c2e9280d6408240203e81c01d84d07118200045040d080460094001c140c40287c0d5010301400c2010880003c8000070f0100940c0c64511032000388010010000b890008500d40080042d42442c40c00710800044d040070300f00365401240d0800047e5200c0104070365030301661042000700f02c462840071010650b541e00914909d208082038116000c03d60300414000c1880d00d82e20050a5034444980042076400301000108020303510b0710b0546540b65803203908000b40180000352503044008041240c19019403c4031b0002800480107100850792054102c4d00c4003041c18040c0e000c12604a0240d6884a036801220940765018032030ba20329446c1e103002d000300d8010342c54811303203107c0c020400812290b507040c03180f0b0320420742e0401941400c3c0c460302d0024541010000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102815341 1250 102814091 102814099
    0x40e010f210b06060f09030312040506090609120f04031a010f0603020c120d020c150114330f07061d07030c0b0d0204050418060c02030408120c0102130f03060605 71
    0x88400285414201c40d00040304903442900e03001ca004213031705940316101c502640740c4000580320300c60341021009548114000d4059448541d101042681c540380101c501c40707136940080400f40e8404210030041c103003000d001a40340382041d03101d031b980c1240c0002400440c803103d028031004100358001164224041c041d640b038203600b072125650300c1650b80c10304140c5502c0d900c40c000c65142000101541565002c0c034140003140c10000210203410403284003802a01c8031041414850340b41c50500079289215101449107040e8034039140c017101e51140b1800005501c0601c010000d800322840a04060202140100f03000281c00c50301c01c0c003c100c0d40b000314040f51500d4021510400101d800d4002c543c084800000c44d00c0d50b40d08440c0c11500c000d2003103030060340d4418030b4a115031000803a0754000d1f0101c2881032100f048a501300d000c041c2e07502d001d41e10884071030340d000f503c007841403010300070207002111800c0c0e002505010038100e03441d0320040590406e683d681c080d0b20080003402128002d001c02040159 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102816591 1250 102815341 102815399
    0x41b091e11070206030c0f16050601080a0209012d08151005100c0c030204020f030910050105031209120102030108011b1d1c05010603030302030a060609080705040908040e010f 77
    0x445041141c2c024200080d02c50b850100010780440580400c07100303800c54444c02035503034091166802000c05441c107010340d0316120702c00c0080b034000c00001d681d005082d0002c044501d103a00c1c0a0344840c0c0845900780601907580006416204401d4400d800342c090145a40030b440c5034490445100415003009109140b0740050b6103080140d51111203210345000041d1074401c60035031035414400741550455000a40081c40000c0c442002180305010350b0240702d4003410703120366052810340032054030320a004003581500202480280d0103013100041c082080c002d4804c152100348400210708980099029007650794603a1a01c8652441da000c50a1401603035043c96203c0310000103411006400b1b0781c49090103003848126a42040c0007002c2410800c0b5800002444040e03181d00e40140607420540f0a0081c8034202400840c0d00c40c09100000c098444050041c11001e1810f8208405040d03000c8003a40d00c0401080089030600102e038945d406406000ba00e1841280750020702e03524004281d1120b800c41104c0303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102817841 1250 102816591 102816611
    0x5180111030c0a05030c0c030c0606090705090306220510051b040807050d0c090507120b0a080622050a03050406080a0209011b03031107030e030705030303130605041b091e 75
    0x1d039007618203406091401548a41d20461b4840300c0d8402c8001c4001e0030b11003c9111100e1038000645207101d2041a903600f422500c1e02d00e4291010f0191241e1558960024800110b40354081140c60b40e00c1e42c95030144020014460320383c01c1c1070240445000c241c141d2614208014101c40b007201850031080038074401e10b86440d050200d074850b6030b01d0003000d118018020081c414000c400000b079020700042c242c04c00550034081c41c0506100c02c000c1c0341c080000c2c10b00c0075840306854400e00710301c1101d01081c054080ea54441c252581c002d017001001c5030740d5948061404000c50320030068000554840c5d1030750b42d03a90f414864080c2009a00a112030041c500407c094110b50342c1c404100031b2088014206111044610714042d4050124515090756442d0b01040f10814941c0c0505030000162054043d54066901c903000d2640301d04c412030300361401c2c6d50b10302d492900103600b13a407240d5441402200102c1e120119400d510400450070f6000704059500c6a03141354070301d19444520710410f040c1c682c041102600c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102819091 1250 102817841 102817861
    0x601020c0603161806020c1f0912150207050322051503100801050a060515070309031b09020f030a0b030a020a05100504090c020106080d140702060703120518011103 72
    0x401010f5040303041c00700074000d075036a01403200c0418a00d4031410070740f07540340c46200003035440800201c194829030244003151410410142d4401c1400c601380d54004455040240360703c501c85aa00d81145c0e0310075442410410003d07a44007500b58235204002955440300300038422684a00c030003600c0d840c0513075130000800240e500ca0b031032440244214801607440c1d60794030500d6110740400d5406055254241001c000d04000280e00480a0b40e6007191101303040520154070034024010000d00a0208110b98001c1c0082000401c00750540400b0742407000c40316464881e204103070b0300300c0f024041d0808004004e1101580c654005c209007148203400504506d68150001031015103a03200321070003000a10a000060f03441b490881c0c01070405840c050140214030329000b8020f040c11701c03e04125024031801400364500c12003c00304074040424000c2d08126a68082021030350005d0800c400784210034024905244260103414400d0b14183d890690001c00c020f0740c50f003561561070051400400810802103aa54 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 102820341 1250 102819091 102819097
    0x15020c0606090601050d0e0c031207170304020307030f0302150604021218010603170c070f0b0d1a130b15210a0905101b03090206190e060f070501050601020c06 70
    0x70210b581010703070b488440041c0c92a12031884031045817801d101003000852030010341e0300c0400206030202d425800c48907617200e40354050341000030540b681091583c480380c1c0c1258091500b10b0300043c03e40703162039601da65101081030001c400f02d0140c1c10854102030381508000d14a07034030442c2905c0541c60305401c0989811b124800610b400100700300404030340341543c0250310940207141d00004040d8160749003a0000c4064120761101c0d20503200d241004100c04c0d5254088404a51102c50400e00f08558038100300d0240510441304010942c0c001804000703542c4150990006002a0200085078a02541848200101d13001d05130002101048030b119500c40c0c0c035044400e100d05809407690303d51a00b41c040c0d00a0484c15401401c3e84c0703d01c480000c04810301c0d52181008022170780340f80800d1255400140c098070752070300303020f0360042051290b42d01c03c500070080803103040a01d2800c001502500d1f000910903400250040e41c0007140444c1801c2000401d200c0d064214000340003d00d4082d00c0000000c041d44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 102821591 1250 102820341 102820351
    0x506010c1104091401020c070e0c0c06040b090313060f0f05090109030305030603030721020c0406030201050706020a09050613030618021c0809040c26010e07180f080a15020c06 77
    0x103580b01d00c80f03024089840e801c0c0080c8560381000b0b55171600a08101a41c1d50010b0240c5040d8032401008500d01941000440c0d141014602c040d00f4135683d103881e40368100800500506042c0010011090250083e8180c50045c002c01c0c0c880c04891010800000e007000d003860300350014000c2c1004044400d03a00280003504480d45854605da0300c1d03036000301190640c042c1240041200281000002c600a00031034988002010303542160340c0700c0321203c100300603220755200190210b5010403013100030941d990000c00600e001802d002c4d030380c1360762540070071394035800320240001c81d01405000744104a1540100004a1115585c229154445da00000c80f5101003c50803141c01c1c070400c000d0010444240309842900c0c0300200708002804070490b02600c0a925542c204445840c91020f100801110f400d241e8103840c2c08034240d90103642e03a50000c0d115146508000c00000a4245002a07500d07a000c4501001d0280c1034050258601c1900d0300d1560507080740e11859420f030060102c800f4401c03000526503440 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 102822841 1250 102821591 102821599
    0x8071701051e060406080609130f15021315020d02060105030606040e070e040c1a07050a0b18030d0228020d031a04050a0509060105040e0a140f060405060a0506010c11 73
    0x142c02e440820300d800c42102c03111150801c402150008046810800d1603100c2d00301607035500c0455849000900e16015020001800d4030001903901010400304607010680c01d1304c0364001440c00c40200b608510800003a400200b0031110312069000b02d0740d040c030a00e0509052400107004a505110000791218401090355000b160f45c0d00103510100300810107500100009400c07103a1508141c04c1100d0507210f503003e0301e450203c1d40d03e602440c519805084658441d00400507040b402e482c0d540308005684d001e407115040022507090070041e00c0e0b0a20042580100307000300160f4411901d11040c1c0d0fd030007a1030811954003802d1a41080060700456074a501211501d80011043d0300c1a09038400301c6203421100360824601001c1202c94109039000e0350241c19440e0468419a03038030400c200c1542c1d4450940c15144e0444080440001c0541c0c1180c151810010166250300d508001440e1800400701c5e42605d55912040600001120521950760408002e00e02458042003d46071100e65410051000b40a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 102824091 1250 102822841 102822859
    0x103020d0c031502040303180803070209040503090406090f050a0b010206070c0510060b0702040f06260304030503031e010608040b011e03020a120b1003022101090b04030305070807170105 82
    0x1008550000c001c0a103900c40c003a1240c0e140c128401c2d8000b5000340c001100801c410040504128443c0701c851000c442d480c0c40251314140440d420301140031009001242c0d513110a011005407a55140a010040c0030f40290000d8180e400440c000150f8001400b02c0c0e001c5881c0041c1c010039a6400319241d5070280032400c10710790181a40c41d15526002d8804100d2241501c0c28070301040318074920008020300d6000301c4050101c143c02451010444c0c0051140407641416404905003444101c51500c030b20118080680e400c160f07070f070b844803811230b81704640c6400380202c480c0d122403d984c5102c08650240600d440c2022070351800b40e844604000041c0156600c0c600c8031020514035503000d1504002440d800746c00c07c6603d558901c2414008202440c007107035844801d80018204040b0500c41c8022290000d21481140103800001401d012b0480e61002c0d2139503c482a65010509248006010f1407080d9000640e42c82c0c2500c0088c034147c0040e02d041c1c00c101d64100d1606181c6540c1004c141941c00845980f86 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 102825341 1250 102824091 102824093
    0xd02090c0c010c050409050702060c0d0e1f021201080609030a03090618122d0e060d0207080d063809091503010e0319050912010906090201030e070e0103020d 69
    0x4150300401c410002290b0a00400101e5141d2080280c03040b51100c910a21154907036503800e9840f03950844801c0000d44c800c0c01044a0190740e504010843e04405d02928001c102c4ad035500201e00c1c0c01411414501600000e0040c140c258a0781c03030302c0c01030615001801c02402c06854454503803103140c42e40000c0544880d60321040c02615807127003108030a0000b082081201520346140100c07050320100380880d6403549200180084840e04086041d08481404c0c890f01d172000e01503d52011590341950082814840c507407a040e0b0b644000d110742e40c042c0312800d80f23a8180100d82d00a84030260007054410649840010f00c401d505d000c0e4600e074941214140e00c0a00300000840024090401481da00042a0b400c0c011030103a06014081500b50590081c030030308110328040d41d03403031007001d5a12101a0050803441500c41c8076001921001200030728400c4840180200c050035140150303401e4603c650b503080c8440840d0307010310a40f40007240c0d9401421140d490300050400b507140500c0003078010048640a04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 102826591 1250 102825341 102825361
    0x133050609040b120d020d030606020a0f05010605060d0906050709030b0a1a04020708070507060212030712060504020f03060405010f0b0702010507050f030408150702060f0c070c0b04060f0801140d0209 88
    0x3d0001da4044c0541c0c11103189815940d6a858030300042c5800740c010803e6484045104e40100e00a036250b43c1c00914014a069540c03c880c451041010307500c40d5a99980401c02e9a2034100070810320f52010070102e09221b450814004076000903003090144181084100001011400e0a41e0301c02000d0900056007001c9941042c25035003848102a400340c0300007030000c1040801c901800203e40104112420580c4400003643e40c0c90b00030202059400084c000101494803424116624004503940411459034440125090740c01840c5071340318800e004170400c00e2905040c8580d0380113186880809000a00d08020030906105083d006810004001602001d00000308848060a00d164040300d03900c80e516110b4a85541100e21151042c108100208508a1002440500480d20070508040f2a22a40340c0010154000b9604803850000d0010004042441c0400781c002401240c4403000501e2003600d0090244805030820420000a000c9405154650100d60750810781e0513034104245450764940d00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 102827841 1250 102826591 102826601
    0x30720010b03030301060903060614010e1e03030403030c060b04060609120503040513020304050f12030f06190603060512211e030403170a0507020a1205040b0c013305060904 76
    0x403601840004000a0000d90242500d4101e80c0205010480c1c5078596a008407624484bd600d28001070032505200c42c00c1c50281d5a680101140116000c0990006000300382150800d42c410780200301100d5041c01409240c5c002c1c402c0c000380c06c071810048a400c00001500402003402120b00100c0e0349000c0e201048002c1045601601009103031181400458002d88069402105c0c1220700e409104d4035047e03000c2c40092441018070b0080051402c594608007403030b04210780100f0b5254810314003150720442e01c003602c4270078010b0210f035500810b1160810051145600c45490804090380c402c1c0114500308412050920707650b4030b10b02c001e40d0703a854100380313044603840c41c00f540c00f01c03404001052004268110b01c803030811000603a041c599036a01d00b5620030440d0340484d8141c4c00368000c0c00c84100012415480115020302c1424240c0c10682c4803005445940c01c4400c10001aa540e1440902c028142c0410000c4c803015100d25007003045050b501511090b40d5612409d0f01603200458284820794894003d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 102829091 1250 102827841 102827861
    0x30a0b040611040807120c0e0705030a0b060d09030816050c0a080307031104060302090316050916030221100524070501060905040b040b0907050120010e15040b070503072001 76
    0x315410070740c41c0e102c26499600c1707001b0f040301d5070007101c0000140301c0c5e0004003a6200e82c115484807400c5030398513044507005c4d0080581c01d42d0300141c00c111140703003819507101d03c0d20f056009990f00d0f01140340811b4004070242c14070703e0754414080207101500b05004006800601140e000940035201d4656540c02d42c0500110943d0100452000c40c01040d035607419406800414400c40c2250f00107017244403008501c20090203116003192035240080d082c505031a031100d01c82c0e82c3c14a401072603c880510b409050b2405001030035a0441441d09004504070b00c00104009410304a82d03603542e8404002e0313042c00c01e40082c9031183e000c12003c03800c1c00a00c0b20a610410003446022010b100501c3c06103014080203404503012500000f019020031421030002401d44181d40040c2c640355043c903149050fa09001002c1d1420f100d040d0740b901900d03140d0905c2400242031043c40e0203802200742c18186007140301e00000822660800c1424400c00c8140c95001c0381c1c00c80444020100b00001c030301c54102c014090104c0d00070f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 102830341 1250 102829091 102829093
    0x10306181d061f05010806010c08030402190f0611030306090610020708060403050a020d091a0d02070f0f02030d030b01140c01150806180307020f0415080105010308030a0506030a0b0406110408 84
    0x40105265890010640f1030381420002d4102c2e903103500c01541d290f101510024002203440b481940040d980d01c0c025034020f80003e2084406180c0140c403030070038125581022061012600003003200d0741c0c00c44403080d02400080301450540c504000454840c4030b0050909120302d82d10403100c40f10a000b4408640a407522000340d440c1840c00c2d050141090b03104842c0d501c018420704003c09121031154403074405803020035500c202e00019419101da21030700603100c07464081e9820004400050160400003195900c6054064001e001d580101420061010800e0040c0350520240d058075a0348505070022040b5000074180e1100c0300e0282c107900429050320700c401040102e1601241c00c1e06c0019000c0d00c00c851100c6010300007800300b00180d0300c0c1c0c050b03004000e421030b4518040650740e2409402615150780312411f0130071807503a100758031420341c1c5c402c0e0700658103940b000041c000e00c092180038039075001d4000c2e402418034014540d518032050303000600c050081c40e0356083d401c1c078000120040f02d00074400c080c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 102831591 1250 102830341 102830353
    0x3031909230601031106070201080106080c091c0c050d0b06011b020316050307090603050309060708090a0306200f0703110106050d050c0901080d140d060e150f010306181d 75
    0x1c40c1290740daa00a02081d50714100c0720701c15180074a07011003101c45d4158103a488104a9107800300941d81207001506440c07100006000d0901c544d01e03901078601e42c040c841d20200e4080c060b01c2c00c0c1038424542507048107020302d5031034a510000c9420505072640282d028a0030304008050b000072044641e808080003545030103006c4414580100002800055410890036140e900341e80d01c211800300c60f0b89200c001d20580092102c05100d1801c1030142c0242c90166800c1d5241a032010001025401943c00441d05d00741e4580345126031005400048507801c1180c3d130f030b4900d8007400240020050044460083c2040f20a82117403024080a410043c0180005002140c1100300741c64010b40321001214100e000380c4030a400081d8040000a41080c14419905c1d850710110507241c918000354004001d00c0e000d41c0e16030300f00084100184061500c2403408500401e2018055410814001d19048001d4101401c0100a0110060f1003002d0f6155044103200003504110765015810807901008034004640215 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 102832841 1250 102831591 102831653
    0xc080d09051507030203060f010e061e0a020609070b041413020f07060b06070b060607030201020423030d030b06300103110a1a0403060905030c0106230303031909 71
    0x280082c0d10400414008080740e603070680403000c0f40000c0314516841441210800c8465000300740b00625244050a42454082c0c820000700c000f0242521400046500003075070703001c41d0b5040c84407a41040c0744d4030291151915001107109140070301c0c014403840b034882025400c1075956040815400c9503074a4010340d00e8048000c003004098101020648104e1b061290f02c4600c0d10b412801c60314100e620032845580351700d404c01032025681207260202c0540d0350030803002c1050043c501541110305c0d041c04050b1035152030082407509058400c40d0350000c1c10b003010003600c5180c0e0b4400c02d0b100c0b000c1701200c12411080d03020610348040b2003c400d001c41d26591040c0040b06000700e60244a2042e4070980c3d01c4080290b5890031901e0517240203a8606c44a002800f0074400550f2603041100341074020790840f13040003440030410b800c6603495800040c14245084c40c81c209d2404451440b07001241c128040d40c21450032500c4512036520b600022850b0b280d07500c40030001c001e040c41d000f5a00c5007510f540a031030503400b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 102834091 1250 102832841 102832843
    0xc0f010606020d0e0405060a060f020a0501050420100f030b03030d050f0105010314010f0302220c020d030e0102040f03060b011701060509030c040603020117071e02060f060409030f0c080d0905 84
    0x241c00f000700004811140012450909000d80f43c040c0402812040c8190316041c1c08541031091501128214010304013014003145090141c1ca0040b8051000240d00305801103800b00c8012500304640e00540040718400e00c01c0360807107070145200c1c0c1d1504010a1110740500000e0944c801c500540380b1451070a01070017841c800615009043e103000b038804102c1103c8501c08001d0540091244000e800181c0b2424001400d24104040825480040b420710841008040c5001d40300003643d44401a44008000c21140d5410300429103004007000c002c40c40c05080003201e40012082c1d0001800f116242c0358a190706910603203d040c03a21300009030300881075844a034001c00a46c403804c40c01d0712a108070ba80c410783c03520303252080d40308032036058644081400265424840d0110014050401d1254860702140b02440c00300c0300005040e0b255010748003d2400c1e61200d0141100681528003ca00d440c4000000942010702c01082e20000e080c101d402c80103d1a0601081c4030368040c009429043c141800200a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 102835341 1250 102834091 102834103
    0xc0513020418020c10020901230304020306220b06030307060c0c0614240301060801020a0507020a0e13031107080d0e010f080613020c030f03100806101a0c0f01060602 73
    0x1c0301c0081d189a800004001c800344e000d03441c2002d4441d0080c28401d651614158000c0c04407450604100d2035500180c094422120800c448051a004c3c0000070031003107107010300c240c0341d00c8504401016090302040b410101c00d078200d414000c00c0903221783c0208020380d404100360f4080e254807603020b100880c0550303c005c2101011140440b90700741852140b0040c03c541165484c440c140d050b0602c018586407900420000c03420401081d0103540c0c400d40403810740c90038001014400c00c40d8889540c0c80c4403174030511581800715031000c00b0503802d11041c86094001c40c1d00d5516256050702d004803116000400140c1003805c3c55015984500c9203900c61009140c01102e003003512303042600c514030b40c030702030748003d5907d03032801c46002d540410304080c3c42e42c5109496015155902c0e000741103c0c1851880c1307200280ca580280c48644c0401201d07042007111240411041754041003041e1040d11451805c1e00c0030401112200820110280101e02d4604120040002c01c00b01c82a00b1b000748440c82d6900c0020351230f01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 102836591 1250 102835341 102835349
    0x1407021903170c120a0c0203100b0a0503071505070c1d0f0c0313060f06030f0b010e07051e0304020409020d140c0604051e01030902060c0606010e010c1104090c05130204 74
    0xb00c48441e00707040842152054601c040300d54409000522203c10100249601903490b400c28011034094440c0940c50400c10103000c0c001c2100c0c00030b96410307107800b00540043c1983c03290388a0f600c003050620120003002c801045071101c42c141252141c08519140f070720b8080a800c41901a568041c0e4900c4011500c944940540c1e440300400300f9948500d5601c00091004807951007510108588010002c0d0a582c01808202480c010010325140c50350384803403690034401c0c81541c441540000503c1041c00040000340c0007007580c104a1314003000d41000085244000b010020f1102c2c01000150564035103400c201c445650003001020320b5080f501e410044920301d0054441c1e58403c1d6480038600341030440c1241c05030790000b040080d255044228040070090a50811410140c0340c0381c804006890300e00180074801d091401070700c0b0b0740c40e210b40010900550581c0090400c043c810400c00030400641600507449429100803840c524141410945e06800c0d51002c0e4105000c0c80070307441a6001c0383e020300195 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 102837841 1250 102836591 102836603
    0xc03060f04090b04120519020303010f050103060501140c10020705150105010f02070b0c010e0105040305120907030308150f030d021005090a03020304180609020406080603101a011407021903 83
    0x2410380e080c10311044664568008064281400209001c601170210f458070369455031801a280441440d80d251000391142c03418809a40007100600c070318800306c4d003020301800e001c3c80d0400c21946441d0009001000442a041680c1e100291240300300380140f04c40d60700d019842006642e20b6242e4540f2541d0b480000e07071603020026000d03002165540c0b05400300c405405096000b000214201710b4a401c003548103608200e4035650390000d80d08a400c0c00c0c080c15110358000d8482540700c08501d89142950b4400034054045a0081e04042c80040e41102100d070b00b004449540c041070160020120b082c43d13005601550307043c803803008104210790b400074940740c4c8001c04543c144055194540b942d9628010044010051b0300203000501540c519842900180d24062002244855a40020401301c3c2d009401980002d0b007210100005802c0400c103051100c60310580c1042000c150120499078543c0c681e00160400c200121846801030941003a80d200c5a002400541d01d296551a0401d178100a4482100c01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 102839091 1250 102837841 102837859
    0x41d04140a03021f06030c0303090f09050106050a140903070b0c0d091202010806031c02100509030310140301062105070b03040302060103110117191b0905040b0406030206030c0306 79
    0x4144041460314140b82e040c0c000340b6041c0d4040f4041000c440342d41d4501502c05940d11000800b0401c15003070701d0b0055020744c85101a403410f150140c0c0300c03a4502e8000f00005030500004001c0c0540c4841264515034080c644401e09929140c0890100d12503a410154184105280814501c4007400108003502d0148216600a80381e05400e89490117580704480501091620307000c09075020b0f48080b81e000e500201034030609010301625500201c004814100141d01901404070f05440c00c0c4075064012011400542c10340c40d2075490480d002006024500400e080481003041c0e42c1c41c00d40041000d4119284641c8110246000e0404182400304080d030300f5204810380041c2c52208a0216805a0382550181000d0fa085864141200102030000350400c070491000d03907000a040c03043d007070048010060340c2002c111841414000c1c1c1c1c1d01d4500b9a0548200d86201c81c6015802c024101c0032240c06031030104407084001700150040c00564406908041c0010030894159000b5008610800c011111008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 102840341 1250 102839091 102839123
    0x115050a0807140409050109020307060c02010905090c03240a1d0f04020d060e0304030b1303020601050f030d0809010b04020c0a1b0510030e2a0111010e06070804050102041d04 77
    0xe0b84801622400a0780d402615480005081c9608441d80d603d00400010403072105a40c0401e28240550340660002040f400c0c04200b1980d0080e043c40040408907012240c50600c083c2c0341701c1c94031010305200041e00c1006010503840c58449428103201d0402803c84154969440151030041422000403d00c807164030001340260151406d031034019070700500144105091596010010240c003420fa00c0c6a2206010001c00a640c1500c4ca07440fa110320700d0341050030445403401915140307044c3c000302d00c6500a00384003941d9071070000b10311800da40e1510340729600d40c0b1807242c601e00511041500c1c0790014000510242141d00025540400707910900c180410000200003441e070f000103a000e51a40b042000d038030031040c244280c00291071815101d05855001c08013004a0361040c4070545111008100e4020605240d0703005039045840080d640005d01100340f00316082c40c1c44031002013805083c404c410001c138090040940c10b85010302040b41d408684040c0400b103000d4610350031201101d807201201d940d03617 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 102841591 1250 102840341 102840343
    0x703050d090314060106020303010522060b09040e0a030212090409050d0512010816061d0909010515220c020f01110909130c0b1e030408071b060c080d09050115050a08 73
    0x6040310b01d180c1c00f0303500727603401c1008115000b600801808144079440344405010b008a114600080001440e45560b4080075424481500d0000380140003036000308001101081c0c0105900841c040714401d03541d6504180000240109001d41001d006407060300d4502d08465040801840e0320762810000c104181c4e41c0f0b81c80e90750307100422010104000380c0054200070243c0a0300d400d05642d070b0b840d8020404200320501007000074a04860403d2103a454000b8410545043c1c419401d2040080c2c400e41404200300c0d404660307403201850062103031581d5032148101c1c00c0c400d20022414080703050090042035005018000c41c0d40040028601c01e030209800b242c0002038900c2c487c5840b6520107035554001c0d2074040314080d10b4200b02d8000c1c0c500702c078030788000000c500613070001d500c5184180c81040c0c0b1800a130030040e500f07030350540100204011102090150035000401c440b4030a40c00707010340d40e8554131958454007600d480c6100034101c0d801d040d4040c56090282103510280c41043d42c03001c440c15901c0380c0307031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 102842841 1250 102841591 102841603
    0x90b01030e0d021f0608100b0a05010309020a05060306010509130506090f010320010207050409060203100f12080706021605060603100c050a0513120b0f100f0605030601020703050d090314 82
    0x106000d40c1c00100c1c4044140c4283c0c056130381e00c0008600c00540503584c2d080329418030507500c06054100fa5101004000c80c03815020700400b41c002880c0c2000b0404050b80452401d0005010b0b80d0700c140f001200180700d40e8400e204407a00e0410140013a280d003003140b1141c0d00a42000c1c0c902c0380c4901007000007e003100401c000e80d541229000040c103080e000516032480240800816814114080e40c0004140f90f00c4a003e8445014800c41c80140c1e0380c035000c0038031075124203aa0869050307641200300800070b001007911140035242c0c10007105940e508851620500911508080c403071410100c60b03854061200102d1410301c201015001c0d9881d10f81c0302c2c502c6200b200c60110b00600131480c140b05044011f8459405130004e40e50300c0032980c800540318000030100d440d174584101d88120b8001c0030494070300b01010320301d07821000c042e0100e0303103e9061500c03000c404103040c06080200000400007032a1f581c801c1002c08025500b01003554110f1140603c001c16655190100b0b88040d030b46c0700c205080d54440010b074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 102844091 1250 102842841 102842863
    0x9050118170a0c08031e0106020307110402030705040b030c0720040c0e011d0303090303070602090a06020c01020c060703170a0606030b030303040b04350301090e01050405280606090b01030e 83
    0x80c203004224959924082178001803da10031600c0210344140b60448048110783c0a0802500119150b42c040c0c60140da81b642420041c502450050042c0700da200d401205440644441c07081c030940303071f5462903450f0503203006015002e0724401c03220072100154040c8044580c20030703009a1b01400701c3c4064070f078280d0ba0b45440d030418600082e264041068a802503822242d0483e4000701500d00c2c0c2540400002d1468200b4001520015400204c1c3e0056107040b100c8003009100c0e43c005008070b9100340d00007039114244440c540c3e000740d5002070708804052080150042c0b240041420f184241000d08178040217180e540200d401003403030421240c103e40f41c0001607902c43d692020050490703036120741c1d800404014103801d1900015542d6401d03000ca0500340d01508440e81320281c81d0303030ad0758541400c3c3c205030385031251041c2069141600b84400700300701060103052081c034960b4010a1403100d00c1840706210805c03a02804840c0f9000c0003144820103900302d102c0d0000309036010301600c152905d007980c44101c6180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 102845341 1250 102844091 102844097
    0xf05010b072a1805010510020601030803010911090607030309030909020708030115110616020d0c0b06010c080c07060206010509010b0c060a0504031209141c1b020409050118170a 78
    0x1142d418501c0402e15461006400301110744001c0350b60343c0d4041902016402440701c110b460f0300c010300c0241415690703908030742904d100070b112552458481d5a00703440180204203a0584860100c00c02075022404c8841909000d009565941c0d85c0d0300f401002001524070880c00100d05080000e0a0780c1140256880c07160044203aa00c2e5910744001204003801d500000c130140200d40a008180480501c4242d04c40c11001c2c40300030840c01521002070501e03460702100c1042c010221807503400300346903c1038217500400c2800c110f90100e41d00d0810700524042e10800c28818810090049034440c2d021031881c0c12200f0a0b20804040c1e6242c000701240c601072511709018550050b0300084241c44039030042070b006402410656004c00c040c02c80350094800f9010140c0e41c013100340480d4060348004010081c88442c92609598080c142440c0042503002d4107080083c1c018100c01003030b015555903600450341c5980c41002042410f100300f0241000348481c00d01a40c1c82d500d9098410414000c81341104d00e00400c0395 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 102846591 1250 102845341 102845363
    0x10504050f011b21020c1906030e0703020603090d1407050a0201050a0306030203030301030f050f0d0e01110f0f06070f0903020102060106030e1c0210060911070602030c0c0109060f05010b07 83
    0x4651042503a10a03243c401e018665100105554800a103c0c10004141d841801d48554402902e003000b114002d601a081d402448401c10301443c0c0d6010035169a031030040b51980d40044c20310b00d4003120f5000030354072907000414402680000219610f101c991903e40884501600c00c4024190043d22005402600a403803079400543c4141f0041640c5441401c00190311030302d07500820300d0340c1c209030004c035580c14030800704e40b060100802c445001440f0100040403400c842d440300600c03070310b00c50f00e00d1810f100c07c650103402d0229040c0300545520594804036200308103010107003923130b401c42a288080450820700c0d00c40855441580f90780c05994040e0001c00c117503481d08004400510091644224a00400c14018591080d0740d60440018059034024203071821201c070f00c1f0b822a4019800000803900d0f00018140e2440c0140988d4129074002d600161130369541c0300e411a9500c41d04013001015464003205e10100403180d0320a00f1401c0900307004000980c4c035040c18200e54800c8d19409001840d0034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 102847841 1250 102846591 102846619
    0x80c060301031112010f0c080a0213031731050303030408030f0c0c0f0a030e0a0509130c0e0f0a051008030d1104050402040b071e0803070c06090b0a02070b0601050405 73
    0x390301c03120607005020340003001c07040184c0c62181c21541000d90314030b02d05071a44a101c501ca9840091681c205486860840c0342c980c210060050220492100806da0382e591050b00101d440c50100f41c2d5038203111f20b484031490340c0c000011201400e01c0c02075490301080b00c05801103140c2c00c00000b502d10542c0e0140d015031a6854410038410103000043c00720340d1454042010b1100144d041c00303c0458444204000c00d00c1241d20f1901405150020030614000d501c0110200101d54036000034a412941e1440e03685030303040e0242400c10004803140c00500a80a00c1428412003421b455600d0384a51060b04007042a83c0f220301c2c00020002d1107108440e070b00d038024800c00c1100c00c0164032401e052a59a201203142c944e03244042803d0360415440500f01c61004a00e1909215030703001c41c00010070b6440a4465113290710307612117046e4000500b42c082003140b13400d114401c000305a80840d4009400410444551606440e00806035111407030885480740f0b004040390595002c2c3c0190380039503d004141c0c6041c036101c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 102849091 1250 102847841 102847853
    0xb030c160804030c080d140a0207090225030507060b0d020907081906060e03100b150c070929040605060d090507120323030705030a0c050c1506010207080c06030103 72
    0x4156010390703004408000020014042d0228540200242c0028001c4006007010240c100c01248200c030301409000c11045001640c08106402aa40d0601700181c880b04031074009407054000000b201c251041402801d4107043d00032000d0320f584e81c07280c14240001c105070000c1c40408041c10784020f40015000c0d006c680583c2c000c3c96010346c0a07017800b810042d0303041050303211015140c850b0f000c1004034442e4aa2040a400e01b48070740707090f036483d01c0c106100d210001004941061281e2084144800d0042407112103590248003480050659200500c001c17080300c80300d00110403504100c915050b08548007000d0354103007802200d04580000b02814140380c4200312100103048007001c1154640500180400c0b0070400800c0d2140311402651a0713000c40001700b83c1e400c420000f00582e6101c280c2c0600800010300d50003400c4139448840c05c0000326440204090503150b500800e0160301940c080c00c1030800c0c08902003040386210310b500340c1c01c8400c03640d42c4288050f02c40c0481045035400510800052000c500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 102850341 1250 102849091 102849127
    0x50103201e0d02030105070906020d0908100504020105160c1d070f0305151c02041d0703110429040b2704020a05030d09150e01020c010c060209150309070b030c 70
    0xc042e108071526881c65000a00310741c412101ca0001c10f6040340140043c5904103c1d540c0e00b49103500749502c1d5075081807080f60362030800102811070b080d1035200003001c59100f80250380d40d0916405610345032039158941015840000d006042c10034150451030b070200b1440c4034225000d40d449480f02224110414021400303480c004000d401b00c4c11010701880c0d40c64440300403403084010090085414200b003881004240c50081202400d00c807044202c8035100140070035610100c80e40202070711364030182000483d01804a50880441001d0701c00043c049449101c01104140342c41150f0800211030408208010090304500b040c1c8201c092103180401c0320081124140c00500080100c02c410799140002803904d11201282c40001d03481ca5020007124000201a051810079824140c90990001d80000d50b00c044011000d81005a198566024031000f076040f81c110410244c0980d1f6500b80a0781d103032181d41d0060b1b9605007e0722400400060f1640d60106803030007100e01040c150b1038a60001c442c656850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 102851591 1250 102850341 102850399
    0x40218010e01051c0617010209100503130b070305070201060602061302090606070c06180608040b07231801020708010c08130606050d06050f090a050d0302280305010320 74
    0x801c04120000d00341c1c03410780300407a00c41c00d0b001000c58454101141c0182031446061a00071b6030b80140502100365072080310404140c03449103081e41e02c9948101103403000c0c2c0b41c00c0c0f20180070414550b05109032182d064004a1062880d50000d000880d40c80f02c0807691903030b00715110302401028111108c01403500e0308000e904180002e2900381450302988a00030344007441e0b0b10000200780d40d5000c95080c021041c4405008010170f0a16042d80c1ca45521400c1c69640000d01000030172441e120b507a005003250b03282905c51000a0140d05889843c0c0c1c1e907a090010002c0741d4254003500c02c00c07100240402e01405a040c1a070b1190340c414206455080040007040c02d92581201c0c41d0f6140c2001180944a22107450b50b62401418003042d48e0801c90fa13120301114028080c3c01c56608514074800102d600042c4540e245040c070301d80184e849401e40d4110b80d0700001d91301d10740c0b100c0008006040103503600d0f0300194140c074003484046001ea119510b511181d01c44888256400a0a00080c0e0328100034151200143e4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 102852841 1250 102851591 102851597
    0x80619150e060a031d01050c07030c15060605040609081b01111f021206040212070e03011512171c050a1d060108070909031b080903060c0d0506040218010e01 69
    0x1c415408001070741500080c1c2c03001e000a03601c520b4107400341c1071481c181e124000ca080080206090614a000d85486118009070500c80304039150000c020020702c007000d040060580030480e4176241c440080441e4418841c8900040c0500741c080742108010030503118014602c1c0c4942010f802600056070b82050344091403c1d07078054100310001c0030658100003100c210365034600581c3c514122840224a030805003002c1c1c007540c8140049060803e280c002c55401403800e0070401100c8040c0c200090140140c2c05040300300500381007001924441800101c5092486000d42c15000d0010300010f0446004640c1e80c0e458500035000340c0324455a04c0d51210b80c03c8082c0b00300200b200104e4542c11000c2c80004148907420b580414010020382d84140f0030000a0715108109001c80c06868400030801002c207038550010030441603481c41080314103403c40e214070700c01a0139295140742c40289400a900041e45002c030060074040041c8051a0600c01c43d42c42c080b06a400100240a8500446400b1221a078480c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 102854091 1250 102852841 102852857
    0x414030a020729120a060b1c1d120306040606080402090f0c040911071202010606050403080c03161412120403030b1210090516080a03050703020c04090b04020108061915 74
    0x43c200d2528000e0028141c24002d400850034419008012210a507001050105041c060f1152102050300745142c00510500080794150313401407041920304580304240c01c0c601c0f40800e540c9507000000003451003441d0880341003007055a1004195581581158000d40c00109180094100120728803496000091003800600b8203032203120801c100c40c805040305c1c59070035000c1082003c00c130080b480c05000071190310003840160300e0040081c2681c0201c1c00020300c006004103000c00c1c410010016540c40703452050b034005400d16542072002100c420125a000e00340100b401892240b10b2640032900c5a1841e030000c0006a601c40d10210002c1c90420803841d4800cac1d51042c0c16044d00001c02c07149041c440c54040c0014a5501c6141003481c08500658400340400c1d582c00030044040041000413601d0780500700741d40da03070000b03103400ca061042c11810b003030740300b0314090800d0207001594851511680c400e8071802c10b5911002c0c100124840d40c00c807111100e051201060103550040001b28854103010b0a0800c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 102855341 1250 102854091 102854159
    0x150801140f01050d14010b2205060a0507020301091a0f010911090d030201090f060507030f06031106210a050a06080606031e1e100b01050705060a0504030504080a0b0414030a0207 78
    0x40305910a0b44441f10111011070017103200c02412020641c444000c48501c41ca491a01c00490541d000d0320406005000012410700c096450039007005001580c858094507840f00242045000c86200780e441021543c02d42c00085400d903510704c510030600140301c1c2a141048031441c10010721070f17040c0604070119500e034001d010003e14440c0c5140b5895103c2c440202e03862820117801021951a032a001364100c0c2009410800324681c9540c02802d2001501d0244d81e0f00041c200a0240c3d541d40614140d0543d01c450400080b003805903c400e00070b1004110a001040d583c0b000315640b0f183c155030141d4160490741490300d04a14007842c2c2e141a510b42d000762038960f01d2240000c0c040c242004450740458110104030f00d204002441440c1c54087e003402c000d810103600e6101c440e0b0302ea00c002c041c80103d0341e0707800201e014180213905441c024800b0b0004c850200a00c1d140400c140f09055074211803100c01c8a00782100904007005070344c150040d65004100e01450200c00d81014000381040000795040900152 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 102856591 1250 102855341 102855371
    0x90804080109060b040e0d0c02060d0e0a050f070f1d04052103040506130c090203060f15090f011b030c1b1203090f0b03070e01030e0601150801140f01050d 68
    0x200342d28003c001c00102901d040c0d00b440180c550041c694403c3e40c1011402c0c50f101c179000840302024940503104a5200c061010300c140042445081021071481840f041404000000910b94212800b44058440040e941c3e44200b106090074018440700781c0b09612907608200c40e00c0700d116030260150701245d5003030850740b141d488040b02d10b07184841f1204001081009205080099035040340700020810102d9109451350301c00100c841c0208120641c0000115801e030b40e58940b50498490000c9c0000b00c4c00003500380b5910a0303400324511500400b124406c0e120598090700c0c1070228014419a5a0340344041c40d5011590a0001981140da010610000a111010b454000f501070300a50700418204d0229080c00b9040040543c024220380107104021710400c80c1c080180ea4104289007807040080040b80c0040e0301408821004049a206d2040001040d803c1d1810407100034900703031180707030450744c0715070b4860024240c1203074080d000841d182004000d54031500c020114001c1d000340000d40780315010b2a074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 102857841 1250 102856591 102856601
    0x9010c080d090b100308300f01080c100203090d03050706021306080c2505100903030b010f0216030b071715090f0402010806190b040f09060b1305040908040801 70
    0x9000301e0b82c03020310b0300802a40c9620346400c41640c0340e41320806482d55407000325510400c84038062000e42c1c0300266045c0709a88a202001000c2404c00e2107840c50305007100008000240700b454031522508031110068107122100407509100380d4003541c0f0f810005014860844c0c1c0740b10084041040410440c8041402c0344050b0050002907075a09440070b1400c28001c082601c040c14484402e58104000d101d5101c00c1c4030914076a030007122403143d00680b88d0030140d00300145550714a20300360425444408041c7d00d5400009048801d0f00c0e0b010303c440c8083c0089988080c0c0d92900c001400034880c00b4004111043e0440e41d002c05146003509800c0c007802143c00d0040b07000e540030114a44a1916040c0300e24050f07403259409450314206a140f413825800003400124081e10941c01030070b003541a9515031030064980c10140504280450344c035503a400c06008082c0b0780d03219040070585081c00100e00c800502e021980400e0005d03403803412141c00e1004120040c030920303204a59001c0308000004203ca000e01070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 102859091 1250 102857841 102857857
    0xc0f01051003030221090d0804050d1110050c12030a060f030b061c1a0a1104140306070810150302070b0405012408100e0708061312030c0e0609010c08 66
    0x4040c10305451458041d00c5d2814512490540d455403010f019100d04803001074400c401d0040310307003950001e06818090541c1c4543c0e0801c42e000500c1070741940500031032030582004000159003440c141071760600c00b250705024807802d070710440d00240c0400848800341740156030000d89004000840d25650b40341444607642640c01291000c50600820005180c480c40c203052000c2c55903000300c02c0241d40d41e15072a040c40b101d480552540241404030f0b403680d03125400b079002001c6011489035a00d448401c3c4000c9a041080c40f184070380309440c00200170b14410281c03140a01c075842c0490f8006400d00709140070f171600e0040c0f22410103600b807080300c006c1400c5030081170050340607000002d000d1560181109103030031a07032a111380141161078100201c000010300814280c4030b0110000325518a640564245102c5174004603044c03040005201d0701055591084400511580300f6180256042c2c01c1036040d280310520803008175a8070040d01400d410520300401ea081343c14034003101d20f1003656449000300d070070440b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 102860341 1250 102859091 102859111
    0x307200307030b1807180c021f2a0903030c030507080403030306080c030106030b0a091407030c0512010509060103020f0303070b070203041805010e0408070c1706060108070e10050c0f0105 82
    0x50291303004464440f0700310344641c0c1d00035000e03103800d0080d060005080180c600c0950b41d603e112045046109101c0b440f0204c00840300d021401000140d00c0010317000c9050200465039081e1200f20f075a540d43e9030008080e078410380351100094a19141a11004003448003a0240030041101600152484005101452290b240042c10a0410200130310703110b200043c1c940603a14105091010400c0320490a40c440300c40030010031300d0445071030000c030034094525a1090b144240e0001208000c1700c06103000c00c1d680203a0300800b1004000c0c24032030a986090760030b0310081c1c1000c0018401750400111110b100d400150481c3e10704005940d0380001e8410456203030005820105090108610f00e07040c1102c80040c080081c002941042c0da0317112a0f44001e40020003400d000a400000c100a50181900401000a8070210003050b07480391134817444219103650002ea1352000064989004100b081e0711110b01400c80382c991603c18100340c07032a070b204075148681c6204035139500c0e602680c00d00829101d003103088 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 102861591 1250 102860341 102860363
    0x5221d0109121709060f07090909050105010e0c160f03050705030307110601050d15051e0a02030a0b041103070c0204020c010614040c020f1f0603020612060307060201020c030720030703 81
    0x180e0020310520205643c0e000e1040318400f8040707461400503d5980251080c40e0740d032511b0f29401c5050b108801a58400d802e028281001103060002c10350141c2d04031a07880040b05025030f21503031000074038480ca258240b520341c180510440400c41d82e0394150001842410701c40e2408440d61109c900d9604103d5003500020038015031041c01a9050143c00c0c01444140c841d045803407569551128000e01030714107501c504d903035000010032480303440001407207500200c0308244007410000007403070281d0700884210110900340000c0d285142400c2c4a08600030440614050a5444000c8110b81c1c0300400403041e64456000d004506403400c00f03100392001012500300f524840c1403c6404e10082c3c5101201c0c80040d500032000210032b00c030740490a000c41035030f00e04000d29208a02907030b1500500c8240c001941003400407035945030300c1c4011514940207001c21030403540100e640300300c00ca00780c0c496458010950303002800110005a451500d01510269070b20f404403035004444027280c588015075005403400e071441 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 102862841 1250 102861591 102861623
    0x913090c06030c090314030415020f0c010f05091003320f06090103080d0f0203010b03090115062001060302090c030612010b01020c0918010507020706030605221d0109 73
    0x580c1090001c0407281014020b0780304140b00070307107421510302c8080c2090700018115890f002c41030048030040e000b005511031408490307001c002e580d8100044c03006440e100340116080e0320740c050903014128007107170390320340b454800700d8000d2101c1145800c0680e0140340e2140f01651803440e0391154860002c0f00d0140c801c5480304503d00880380c20788041c2c80c0c1d2440303250260510419880c1d004280d41585d8018080695070b10f1403440c0100148844c0c403005420920200010a0011341440250b009071404402800941c41201d00d08c8030400062003480e012074075544000c80c024018054480e0a550078900024405a49402181e582c00048a50301d203404000010803072540b4120341140d0f1003420b403200800c803290b00741c40046d58500f100541648507142280000d006c0741c0007003000c010440e03a0301000307000c94242800003079940c0c40580150720110303003400c101140c0ba041c1004c0d030400c4031117100072022920712084074650013009404602c41005154041c10400c40c1424054090900c0c49042028800124 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 102864091 1250 102862841 102862853
    0x712020c03010b040b0a030308060118032105030702070603150f030507060305011211010815220e03090a030210052110060302160605100f080106090f050402030d03020c03091309 78
    0xc07641da150b21136440c005c507200b80b40d21460f40c0c1e01c090b82e42c0b50600d244103440707041c0140d0b51610b041d00070310340c10404801c0201c1084855290401d4900217840d0381d0f106250803010540b4540001c8070b034400180e0218401b001064443d4006494400e40c81c2201189652104410300121441303400646050340034480c100f2580d941407084600500092519a1080c845641c03051940341006500310304000034403022800365022542c1100500340c0043c1420700c1d1168605400f40d200380b119603880c0940745005102c502c01c1300b002c411500c00b441c0040250170a6030175642003010580e1b0090301d05041010030720011881580e411101c10200c8890000d040c00781c0b80481d4412010321481d00180105070062010100d2498100c000303021103944680003082643d6602c5042034460500d912001c6032140b1204001082c0070103510103000e0300e0b0b1426003030000c18a1000400300380d420a076002501540145807004030144254064201030340300c4426079141c00556000150a0041c030031030301104682e912030751020401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 102865341 1250 102864091 102864101
    0x3090c06040302220b06070b070e010305011a0310170601031e0201050a0c020f04020a0507050105090111040510090803071a0f0606030606091c0f1709031f020712020c0301 75
    0x501100c100d0300e0903041d6804100b41401c2c0080d0300c0704030085207000310031109450b001a82906406402184c0316a110300301340001c08009c0c0d0b034039808035058054030a040e500c40e00131103043e220152400540101455056a0258170003810302c104480c1c5e80001080c9403010300740598403900c012005044070350550420900c141c0b0151000c01c1c0398000380400c03d0040c2d81100c20b0758440400342c1045002c014290012030200b000f0064560b5200d03100244060382150000041d02c04140514000c0003680d8a10306201d00301c03141c44002081000c8140020030651515003942c1c2c0c80e0700075a14008120710382d1020100e24503080203008462026140c2d5100044442084001e64030003000c4403104007a00380600460384610001e86018007640000992980c1e51700c8040070301c00090306420580d800070b101800c04845880d00301200f103401b0310328501c1e00b0080704901410341c1c03a030300340003405010044000d0288411920300e0300a000c0910f9008d02c5880045141d840540301100703a56000703450010130100425007191 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 102866591 1250 102865341 102865363
    0x90b13061406030a0b2d030708030304020411040906080a29010303050c0102091801030204150605030703021303150606090b0a1d0109030b0103051c05030606090d03110a0303020309 79
    0x689404420841c04001400a40d100502990101e549031205407441c030191a2007400d0300c0e000843d000c80414031803c080c66600ca801d1021949040381240b440405494a84a01c00d4041030781c001c0c40410b01500c1e05030300401c0030486603076010b86015a540341c0402500e80643c00301c81d86401c404210400d0104100050009403084900650700010701c01480300b0b2400180009010040d010510b4220b040003581101d9080d0802016403004001d02224504040d0090204030300035828903514800200c01145040140c803615129641596a00b1408500a4005550105071100c0442000001c600c0d42c2480c50a40140c1c08008a103103424120043c24456580d481203003000da040240000c01c90303220700016104441d0721100003002444a0040310012266000504000f03481c200000c1040300004504090f0081000d040c0100c040500b81a0ba4030700007107401c02c0d00300e441044580802d01e00000c030b9506691207820709020b1500b200c3e40c0e440c5846442801100406d50003c288030000c0e000300030740c404032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 102867841 1250 102866591 102866629
    0x90306010611061503150c130f05030f0a030206010e041104180c0e070c0b0901021306120b01050403020f0906040e19060b03070b0a05030a1107030f030b01140406050c0c0406090b 78
    0x103803072004c0071079920306843d6566440300c030385400466900040002211900c85d0b080184407061512400b03400800038680c400d02e8464402c00f0b41403045480041119846103800d500a05082d0f860301c0310300000308100400c1200c56048000083e440703961648034092981c4901a018020103000f403904499030545a00500500b860b0030042003802c2c1c0c0d00021200400764081d20036801d41e04d840c40043c0c0a4001c81c002c00000200040f8040342859202e081e205504000035000e002d846013900042d00c0790311039800003030740007102012014241e050100509800940181c400240c0d02080b1680a04015006c0f00c007a4a5854040d80c0e40c1c28840760307000740342203054101c3c00303400702d146031450a802d41c1c420304040300140710011000801c80e2515521480c52211a40c0110340c1d01d8075140fa0040c40404140e030000c01003403a0000791402c551280e182c1010350410007007420704d441e0410358152103030303000f800e2203002c24891594000203503160f03800f4020051561180104110520608100158103480500b60718 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 102869091 1250 102867841 102867871
    0x3060b0414091213080706050c1b03030d1d0a08040504060602030903030a0c020d08030405010510080c03070302060c0705060d093c021201050f071b020a0e07030209030601061106 78
    0x11016000c82c8040043c410301103810380d90a20050b0700b4840000b55846003509008070500001d125070040020000c101b03000d000e075081200b842d801d100341040101c00241d010790003400301c0c81460165900004014a030020031010100c400e00d0818903040d00d542c001c0721200381c042001c00c2281024060300c00a02080d0001d541003c5203c4040381d902e0180301d0414080001c10b072190010b6454510045d000300e6005000c0650340e150a04140e4060681920980469100480d00050701d103000b146902c00c09100501602e005407031502000b01d99003050314080b82e50b000d01480050315560380001072096800940b000f20b0030400ea814000c10b200c000703404ca030f0b04400f88010380109480070240b21083c0004003800207004141c2d02d0011a1146040c100305500355840d000900285951300d00e8064422003155403180354200800c44c082c0110184450000d420280001c8184400800e44a83d0b41d44400c90f40742c01800d0840c5840028035100707080c0e001d00007003030342c1c5c0032260390780c000a00100c0da00185008075580c0e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 102870341 1250 102869091 102869101
    0x3030b180a0b06040806070c03080f0402030a150f060303090f0501090605040326030a05040c060e062a01020406081603050f0a0e010e010606170f0f0c0c120403060b0414 74
    0x10800801014049010394400c2e210020399904800e42d0041c0c0021401c542c03041ca401d40000e48440700c4484150085005940000c015101c3d12100c103105039405000f0b000c0b490703003903595000110320030b011010b0203513140e078642c2d004038285110b580011402560b074400e0040c50560428043c0945420081c10070903001c00034080300e900102141d085a51101c2d40440c00d1104818501800b202020050078401d80001480054011600610302850164250213119641d9010642c4c4800c2e511740030a40040c002e010711810180041d118843c401d004410402403481c05a1005007241e00070b070452000701e000c0c1400c0c0107110318007800340703855105141007c201508212284c1c0307020b108004c1042d5040c0c2d854400400d1811070a400c00c040908282c402070140e00c0e00c0f16009000e041943c1030b04c805004000d40055887c0d01190083c40c0110000f4a0041c10380d2252a202e0300c80380e000310441c2c50f4502c22010355080718051900103000840c0030f00000154085200100000e65014019103c01182404e0030303c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 102871591 1250 102870341 102870379
    0xa0e090d0c05011803090509070921051504030c2616020105070209010b2502180402180108031201050d170a030905010f02030405010b100c1719020a03030b 68
    0xa0942240c1c0c1003121002400c0d10303040e409041c0109131034820101d81d6100c50700f0503411560080503154120380103106983c5052003210103003510304c90b41580c0704c1040f90309100c020f4111100d100107809103065580501c150340403440c0f400400d44048001500d08983c040600c001c0340411920900c0030514070b00140c089260000c0c2030b0007044e90300d4001015106160045a006101312000030398050070010b440e40e941c00c0c02440c203821041624480c0c920814038415211000c51400300041c0c0c0c02040c0c2c0e0300c00d03a03c4511560300c40768010800c0360450040e031403805500012401c0103000b002da8800955440c07989409200d03044d80c0607400140a1020a028840000c100c161000e5501007041c2655840d140840c50072030181811960103042d652800d8204016650243c00651166004000a001c070b5903404082c0070306045081c01c1c5000007044104004005003500d8140401710685043d803606121042d40c504100441c04e2003d0805079005c03d18035800c2540501442c1040401207600c0d04201a0000d850 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 102872841 1250 102871591 102871603
    0x103050f19082215020c0907020c0604180608030309060702070b0903030d050703020409060308070c06110303070503042910050108190902060f0f03040c0503010c09051207080115050a0e09 82
    0x3806007030f0203075400c0c02d6141c0b0808003450010032650320081c2030320301a980c0280d1140b0004181078040c18542c0700151440c1d00010f64007407240d002130201407030180703803e0310b6514070825200034806081e1a02c000080e500801c01c06076000e01090000744c0070504042001a2500c0302641c44020f141c4400d01c8080341c1c5940210540f00a0000518082120364918070128020710a0340c00c4100d4461038503c01105202d040405040c2551007103500f00000c1e5107030701013910328040d20100b82d451503104100103040244200c002c0c4d03402610841c10302010b000400d042e0000040c13812000e9407803424040c10441d4198148403080c0040000307082a4446007400c42c0390b00080b0003007041031001c041c0c0380c0340f0410440d1903c87c121340c0d11412012503030303403900c0d0030b42c080480c1ca0340160703800d03264018010350201d981d140610500c078204499441d580111440c00c420721014003008482d110b03560295a034000760445007030082e1800e800d0071071030f00d0b01601e08000c204405512550803902840c0f404404100d8203030000954 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 102874091 1250 102872841 102872857
    0x30607140702041508100f0e0a021c0b040b240f01030b0a0b03010f0509010b040f03172107110604020f090402060d020d060302040605040b1810030b0103050f1908 71
    0x307070744003020300104000d030038030056119051158aa001034038800104804602450b004420311400000440e000150340b03882e19060310756001000c0e110010b01d007032186241840c003803100d841140d45060700c0344140c00400321010303034500c44404200801c4100100303600d10401030702c4804021119600012030350002e4402c140e00d06241d90307100d001003180d1f0341d82c000d00300601050107560343d40d6845080d506141e010b20b00c2064040d0768190300109034042d00070191800e41d01200300c60840310b4a1074440301076450300b02c05c014051040801203048540a403001d1103405a4020002c19840d051031f0800070800f040e42d45030f0810603049203050000594403403210760040a8100c030003000644660002070742c07620071000742f560304030720006d00840703201e080c0c0d0021000c4900031035040040c56910010703c010b4032000100e09611002c01040c00b040000340004484d00460981120f1410585942e256581c4c068284c0050761181d0048400c0d107015441044460440d00304c10ba42d400803c0340ca40d0b5200030313901400380 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 102875341 1250 102874091 102874127
    0x6050a0809032b0b060d0608010e1207060b060405060c01060f06032007020102010b1008040b010b0f030f0a0e0d051201050a03020a0e0603010f05010e041407080a0f060b0405071d030607 81
    0x2261900c202150044c04003030100400c4a55640c0030000480001c02047c0310350b04495007440d0041004141c00b0401c419134508000440f8600045e980d100001041e03000c044651001051002251070307201c900c06800c02905074000001c01900b0308003a192445010b921180800d400d00040f80e400b1003021008410906803030002c262103040c94801070740504124951290441c00c00c100b4080741950104c000d60080340100341781d600c05d90300c40b900b202003442240c207004081c000c104041414038400903013195010120440014103824004544d40c10241c05e20002400100040f83c5044004d085c041500d00404088484103041d600c0c50340855800002403266045907040100051a036803020340029440e96003c0d00100050f607140c10b030030b200d903501c1900d040d1106250040d284880b024000380802c21b58903140300504969120380d0311011001c003055401c907050354990348012642c1d165401454060403880d12076500030110401c14072824005a40e10030311951200c402d00501e80d0f007010403440740390408a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 102876591 1250 102875341 102875407
    0x50c040b0312070f082a010c0e190503010e030a0201060b040f1a070c09020d0b01080103030e1207171c020706050702040b2d10020a02030c040c0210020406050a080903 73
    0x30601130106618035202034803607880014440d00804510800700c024030128808007505501c4001c11900708c401047c00b020124a26041101c15840c1c00100268100154a40c040d003458480340461b094400501200c4520303407005c24406045a02800713440080e1002401c25402e2a280281e01080650f03030340b099003200c3c040d079200b0110103180c0200b03c1e20180d41000500d035466540c1d00d104002540705442045030f541c80c09400f4845036204040300e504881e00f5503110f00d0b04403103020410000744d41c20100703900e0500c520180010b021840000d00d40c04220850007a001d03240c40244805181c10400c1c0c040421134110007402d0000c1e0360008280c030851134051710009000030007180422035003c4102d908041100c0c9994140465050b040e00500b0120000e880c401580d00b110003059030b9a1500c524000e5054000342c0d881c0343c450400c1d50007860100c06500c12114104800e904180490303109410010001e000000c26210301074100c22410b8012074880c000718541342c081402204c40402100c3c444091401c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 102877697 1106 102876591 102876593
    0x40b09060a03030302090102010e01090c05310504020d1407060e100c0212190b010e100501020d2001020a0810051503070c0302070e07020a050c040b031207 68
    0x1d8401c104840c2140d40940194006c00c129a04540d80d0708152000d81c8024011440c0c0b15000c2c44110400d142054140841c461480c69059005805003e200b006c1080f01c0d0000c07000d80501d185d001403151a54800112501c0d003400000d481c03030030030b029020009200880c2d090121365694a50300d082d0344076a07041c0880c4070312540d41e94001c1102e0503041c0b005410280740101c41c0208280540e50860685000c022801016640a44d1004c04080c0180301c0e008880084a800000d030242c202c0016103883d000071754581c01482044100449603501c4050201e80d41e1012030041d60180003551520b4003c100140410b108a5106c1d4080702550000103070740c2001c4103e10412080440001d14664412b4400c4e41c0440c11742504034214400c2901c00039a02d041355070280d005a24940c043c1000714000d00f021482e0241c1e01c01e41610480c03920345003002a580000c0c9425000c1000f0455035100d40c01c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 102697841 102877697 := by
  have h0 := BRFrame.cov_init 102697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 102697841 ≤ n) (h2 : n < 102877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
