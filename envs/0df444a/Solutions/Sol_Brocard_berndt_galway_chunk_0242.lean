-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0242
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:41:45.558455+00:00
-- url     : https://prove2.me/submissions/84d5f550-3a8d-4908-921b-c0cd9bd6a9e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 43345328 ≤ n < 43525184 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 43346578 1250 43345328 43345369
    0x6030714010c050106180b010813060b0a08150a061a04090c090308030c03070e060906070314130b0417010c08010603090201090902032701060f140a030b090304030c080703150902 78
    0x21b034804c50311a4104071902002c0d0a10000700c0080c01121408012600c0d44410401c064000000c100541d00121200e07502070300d9030202503107420f001d510b0701c4513004851094030301000800145004e184141d0340544401c4250b0080703c4402e240702011805140142c0000c41e5658120f02004d5001d60078180095030303c80c0c0304036101e1410902103895a00308a03a01c20125040451101c2075180c01c3c0211405468024465420f050040d10704484001c011814003032000342c100440f81241040e051441e00901e15a00400d0b07a6505181aa00d010200d0701401c020310fa044c031031510b11203900580189c0c10b41c0c5852400003107480403400102c4261400350b06c03c1140e588004284082002c0c0300000301000380354070304c0203020f182c1d141c0e802901300d030703014866100407600e03403442441b040803c1c002d4006040303001026020b030240c6075180d4003890305c1c0170b681051041c1c1c4009020402c00a1501d1000c0c024261040a4400300707156807103170743d070550700d907064001841e650307038001821950b405849102a1000f900d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 43347828 1250 43346578 43346591
    0x1e1a040906080a1a01031709030f0f07052b140a021305071805150c01020705030c070501180803040603020306040e0d030203190203040c03030309030c0614010504050f06030714010c0501 81
    0x2200b58a60407140f1055407200700601e01100b640d01005540790403258022001e940348a000c0d0107802a81c0c000c1e07011a6071501920702c02c02e12002d400c00062070740d10a8100030308083e0b4941810403000e10111b0406800c1e0b41b900d80194890400b01c08559918260011480b007101c805060101d4148944400025401075100840743e0307200c2d14030790210b48030ba907844d1100c6a101501800e01076120030944981ca42c07085850140011701e10180c000385c00361810000016090014036560039003940c00194100c5415030101070308000c0d943c2d0200c22031024101101e404070045040c001001e469108500840c1c00381074000002c50700f291615802001d81c1032508081c0e41280c1c0361508024080d600039250600c3e6030031042c041082103900c80c401c5900480d400b02104046a1031940c0030b0b4090500030750181c0c2030000c1104080086003050150340d1901074a0001c3d8022503041900b00801c452001d040844143c0243d0208096a140000c9501c1078601608150425070000401252004144240180035509042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 43349078 1250 43347828 43347839
    0x209130f050a0c05030c240403060e01090611120f040201050c0a0302060703061403030405100302090a06080415020304050c01080417040b030603010c0c020108040609080d060b090405011e1a040906 86
    0x294a550b45882041d80f18070301c541c2c400405948810805026a015941030300044000c040d0b0301610140f03030301207000d45007055a130740c03145e000b26078111041031801c0c1d440707102d40070401840344030710740c102651421510304002030785400303084020000301044007500c1c0210105042da030181d015901e484250741e00302c5103c202280740003501c4110039034081000c6810400c0c0840c0605039402040705000010303004504140c03800d000c201803540700100c444241603080041c5a2141c03143d0314400040c0c0020b0301c0f42612400c0c0781c0b811034403d004801e00200054418400c0c0301c0043c4001c1002c810b80c079401d1801d5206d81d00c86082075100d54005080e803201b0301c0d600042c0000c006003000c02070352103007004070002c001c606030800c0c0a45882d508048000c3c0010780c0300d800580086e205500001c40d280c05010254184407601c1101c5003190700d03540100c4164140460ba83d2040d2030030340a40b41c050412200c0c00341208030315851505100c0168000c4071030304600706d0700c1d00b1940703250481903800500700301e1014098030760b460 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 43350328 1250 43349078 43349083
    0x1002070b13390608090a08031005030a050d080a050c0405040207060e0303010906060e030307080a0507030504030f03090e1503030306010e010c021806010f020102040503030307030f0209181f0506070209130f05 91
    0x1102c0e900301c480c001000107002d4003500742e00344181c840701c010f04110b0b001c036560f4030000c0c0d2004056502602600c03001290301d8804005c40103035640701c0d2008100c1141c80b07003006007459100524152040b0f040c0010030841d084c01000b95400c6400c00ea130096164081071400501030401e41107d9011803001000002d100b002680001084411300c2d200c8019580d2840145505e902c07803c0b00c09004640d00f008401c4500f44a94010310049000c1e00c0c006041645070303690341d8004000d40c20300b500010180001888001d8240d840d00d81c120008014440000c07003000e0101c0d849010041140d81442902c9116442c1a4081c10b0001c60456004080c40f84c4240c600b41700d20b100110a55007140001d13207891240c8003081c014800c071400c0e035100070300550441e5100e0303c0c00c40103014022006804540c0070322912480b0b841e207802d12901c0000c0085004010700d400007807030340c1001461001001104502604210399200c0300115012143c05950100700303a660862012868031604c0001400c8102034000c11082c040702 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 43351578 1250 43350328 43350413
    0x302090405090c040e0c0603011703191701051008010905070e03070305031e0307020a110406090e060103110d020105040306050a0e031b0601050a060e040504060609020d020c1002070b13 81
    0x210380070000d41e82140d5176256200000340009030400710410050051120120107100302c000120300b207a1919803540c071016900300c0101414004070b03202a2a10844005200c54a809000c0685880401d02100280240450b0701031182429241d5100c020031039031441f601181941c01c8001c1c2c200c8242030b03075030f2802b150380354814070b0315440481020b1614035020450b01e04490084d803155000389060f29054462142c079003289194241e0255803140e0020314039840b40601d0460201d542c0181c005589582440c51500d8080c2c050644100341030490780c00140c1c2c01070140c4080e280c218500148690350084100000c25a04500d0403035031001107240e0803418501418109a450345505541e0301c1d1360b031041072000c4245607005610101b0401c082240c070340e040503805070380e10078064080803412503511200e03d400caa120815503100d1603000225000d0a1404020210030006002c2d411482c00d01c098807100059840a031540c03d18110f140207080070700419006441003403032194812140000038161040c90f0418 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 43352828 1250 43351578 43351603
    0xf0209031f0c0804020a1404021b0c0108060916030203040c0302030a05071404050105060304060213050a1401110607050a050a020106090c032a0e1002070f0303180f06140901030209040509 82
    0x700340550403032902c0f911038240202d50251051103402e00380392400c2402c41601c2c96160b0443c0e403e00404004400c6003080b81c0031010080d0240600c003404000061600c400100b640b03002e0b030051010f00080f05505008804030b405039140060b00d9840e2440d207914084541c2d80701a40c144580480c00003800400302d1783c00101c4d8802171036142c826696005010649000340b040a0384000c0620000c1c011811580051020741c0420107010205600c1740001110707802c0f0340e04109456024032002c080c0341d5070003442c002252040c0c0c20043c419031070314803402071051085e03250303000030043d02240c000e0640e0f00035004200600080d250a100740204010003c0082000806080c10714503042010440150700e03203600c1d00e0449d400d030745d440d030010703c01424000940000d900640c1144503840c03000400310039000c1003c0c00340d40301e41d13030780c030900007622103080f240503410740100c3c003044004401046096000401503000c0c1d071a403202981c032800305000680c02400341000d0247c00504000400802050200d0038001a04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 43354078 1250 43352828 43352831
    0x30219050601260604020105071b090506011d0a05010c0c03080301060e0a090507080a0209150d050a06050102070806061516030f02120703051605010608151005120a060f0209031f 78
    0x440c4440c4142c004409002e003c564000c08007081c05944590001c102850007500b085500c140011100340100206034007050758507070364005025881da4058940d0345501100ca5045040f2101e100008183c003003988100d0b030500c2401c9400c80104801c002c0441d00035604445542e80f2036943d04400f4003c8840c4142e124171509661102080c00302d42440340038055545551018819a41c11003600d0096110b11440d9038040c500013440a210328501005051400c50101e01240e2810607c064500760b418641045040d5001000203100703074500010210340c010f0f41101e1040e0341c20071050410b03103070b0702c40d03c801c99103e003142d003002a09160300041d480901104550855503580b24140c0300c400e01e40a44100240001d00420038440503050100c402556180114000a41c2c6513850403c00d180c020b01d1503802007045502001c000c4880d400038440c0c0001c24064410781c100400d40b07040b171074031030b0202440100541d5a135000031800440540c1901c03007000003d01152011b402d01558803404850301c1d1b908440700c9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 43355328 1250 43354078 43354109
    0xd090b0f04050c0d03180305010906150e0c03070c0f1101020d050406020307020415090903080411010302162006040f080106080c01020a0b090a08160b0603010902030712030219050601 80
    0x5038a80380641d22850700940074245000280c01007102940722507100390100040d032000d02e2402040b4000301d600561040b070001803004982d25004047d039020560681c020002e0384030400001400d000d109a0082a40c02d890740d032659803e1050725078468445010301000d0a2040140404c44d5911800c016000c00760225a0800702c0101e048072544035034007480380107810a100003401030509030041140b500040007400402526400c6620031101c0000d81070340042d0f103130710a010600c0320780301d00708180714030a103015072400546001d9802a4030f0000c00007007113080c03110b8101041c0c0c20700001084c412030004050607036a5542d00e410814820a50080050b039500e0032000140010300025418404030303043e000703042c98140da40c64003540401c4c002c0034040c5501803003541000050388500245000500c01d081c3c03507203680305802c1c500114a40100030341d003c0e0380741502200c00b43e80c00150038400c030f0b080c3d0800c00e1542280d070328049050110310b401185804070441c4031482002808039245040e81d4031000b042c10038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 43356578 1250 43355328 43355341
    0x1406010f170f0c0607030c0803091c05030103020303030f0903070605090618010506030a060c1206030503040609050415031202010e100605100c0f0602031b070303050118110409020903010b060d090b 86
    0x465042c1e90b801da4480d44181e148221904125000d0042280a070410488409054403007000d01d5108803460031040d0001410240e14032074400820b50100301602c0d0042c21136056901083c1d40e44000341130b42564000d0003000030140340d010822195003a9019409110500b402d0705410354850b42543c5010040b1160702030000300400c14450740d8420b4400500411681e070b0580c86030002420501950703400c0000c3c007010310000003e94020640114031510080d503881d464140c00401c09075040d00490702c10380c03d15112101c20141c0e00b101d1000d698104140c1c0700340080040e02071303004013182c1c0c1c8012464080d41d031050b03c454800f5800003040301c40c1651181d0000490f52022100c142c1d11810003001207200b820340c074011a0313084d400745a111064070303503101656454081c5021290410f0f801140069100c60040c80b600004040c141f140f4001c0081c288150b20759900c001616000c0c41c01044011a8080b540798902d5a007500402404180070380003e50b00ca444050030f8001c1c0c5542c4001b0782d081070100b00131418 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 43357828 1250 43356578 43356583
    0x5030109020a03060b04090209040c05030d0503010501021e030c0a0605010e010602010b030d0f091a07031e05070b0406150b0703020c09161803050106141306080c0d1406010f17 77
    0xd045900400c0b80d4003050565588900a210641016130841d54034000880180c40304401c80d40111302906204412924100c1054079001011007810100070041c03004012590f000039070141d4044154040c00300c4008505551865809010000841441850041010b11055910150580d180900c4810050381ca66406038240e50709000d1480d016449112081ca0591091100c44d00403100b82c9030030b40341c8a40d1401c40b41c8011074030b0904945040c6000070b9074020540c000c41b042c4440190100111802007529001500e180104a4080d0816039001c0000d001c1221a80c03003101d0401c464600e60344520740780c51084c01260480380085001d4480c40c090b81c066450705d81400c0d4481d0800e0900d070115101001400c407005600e2540030b503007007004950302000141082c01030b600039080310000a82d0540c220310400800031181942d4102c004e1424109016580000c144900032407030a481990311003d45240440f81c03a0a86040d0900318040c1c60000b041482002c0518400c0340c0b1004901800c2c0c9110500032038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 43359078 1250 43357828 43357841
    0x60e0702070b1305040207081207080402010e04020705031201060207030c0e06130b0418030f030b0a0e070302030601020a051504030f030209091b0702180105150406020601052b060b0109050301 84
    0x35a12030202041014268030081070140003101141100c0b60340e0b800840c0507a0041c240807121941c001c140d541d9903400c205c001d9548a201881c1521250600d90000b8190380d00a00d081030040d0b400044030400e104003081141e141c0d9014004585543d0f0392600c0094035134405000495040403541d10000d02e001c00c0506160240500030544101c94500d101c03403038018017a4440080d041074840e07012400c0d8401c107810341c4100a001e600d4180d50030300a0746006080320090250644181503008007440400c5100b5207143d803080c039074100160740761100c0d00144d281c440e46a600901a01c2110440d4200c076289050180c0114400d464403842c0c0c00e103c6c1019026401040c03c904d400503400c00001d01e07284100c6011480d19100070800a1600100743c003c2039812030402052450084510010002810300080070002103143c0c5070010704080c00c000c402519582e0620a00c2d21500c88a101011003880a281700c284c1d00c0040c0d1183c40200001386001b001804403503000c14081018075100080c00d00f010700030103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43360328 1250 43359078 43359091
    0x7031103120c030d090c0801051003060501050103060605031305011d0a06050a11120402010302041806030b0603060c0403030e010513090f111309090f0209010305060a050c070b0105211b010201060e 86
    0x1035013000d040d1a1160010a07803010142c4912440c0345c00001ca040c8284902c82c0100e84c0b1601c5001503604605191060340c43c10b1388010304151400100700110707036201080d00e803c4040200f8060901c0090b0030100d0240442040800d0201041c045280d20f091001800c004900d1080505000b00c0d6034821240040f5882145107051401c0d04000000a80343c081910940c058070504006040640341e0421240907407208810041d01075441c401801032012072141c2551145c022001441e0b04d14181610b540f0a026501c0000c040c000d00c2c0c08070345140c1e030084055803100d55a80410380c02056542c01080f0280141007510603403103241803c0c0b01c9041150314100c03010010b009104400c6685170900b0240203100b0201d05a8141d0403492802c00165210b514440c0218002d000030403003810180500d401311500600000240c0348100320341c50024a860024904442040341d424148604a21842c0c0000000d4903441003540101b00d48500a40b8414440340300e011001e038001c000311034840c04000000c9200351603c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43361578 1250 43360328 43360333
    0x111012060f06080a0c170a14060f0a0e0901020409140f0601170c1305030a0b090d080105090c0706090f06150f0308090d0305070f081e130911090307031103120c 70
    0x11036000c0d40d60009120810186450601031881a01d5009116000d48403021a583c0396852440c01e8850a808c1c1c03904090222240109049401d00040303c0900038401c20b03e100503090002100884290b050b40d0041c4203400741030007a03514517000e0001d168811140d0a0500c040e01c00071030000e51050000b144003011080a0307240d152030341140804541c200007940c003040c07081d10201058036102031010116040c41a50350100504000800b1800d024980c500c00c0200300c044001040243e55120402c0d81280340c235550a55142504d04104010b410039400c00750500f11444242400c0080d40d6100c8661a21501070341d109090301c0e8481130114a459210143c6040d03424071040d08289008844a00458400d0074220700e8880c0650380c0241c1083d11050036258580c0119200c01500340c440c100c04201c8001440c42c914040002408a003601a24040c1250700b135651410001c1400c401030468125101c018110b40055a980c0303880d000c1204d00380c426501900504c0400140595030905465010b100b9601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43362828 1250 43361578 43361581
    0xa0b04061d04030e0316180b060a1b0809040e0d08130b0f090a0210051309091e11040609020403020f0405091b13060e0a0e0606010219111012060f0608 66
    0x20100c65540ea210382c8540e00d402001d44090706d40032030310704c56401070a0b020803000041c0848420304044651a420542c0909410130514084540c003c0104407100b441500002c20600c0604000501e0f004000882e90454075100140e40862000280d40354900304c1581c440c101039590200c640080c01904400800441065004c69010380c40c00c5251644802d5580880d1340148058000842e140d4440c8050004514002071010001220f02000030241c40350010a010380051079885242802c650400900507080445256040081e4000c1034070791070a0080c428480c880d140d040180003544544412807040d14640a402c559042a008144c03156044901401a4941d54102c1c3d074024103407080d030305a010041c1d14841300c01c030441e8810f00016224030f1510001a18001d02880304071016410142030580c0301c6401c00401d6070f40090a0340b0b40c04d44032010700f0311043c01c602d03080d402205080c5039150300c019807413001c5103950f0780500c1e8000e0304c038200c4a0501c1899501c02038902002440d005810000300e03140d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43364078 1250 43362828 43362833
    0xc0f0307030b060a0e12070521010f050c0a110d0507030f0207081209211e030c03040e0f070311180105070f08130e04020a170c030a030203040f06080f0a090f05060a0b04061d04 77
    0x9480320809c502100110316120314605801c1150001c9038084041080072501008541d8000203c0d141e001005000300541000c0c04000f9000340221000241088054190080524402e00c25900201140c5089644500020804860701d40001c19124001d19214850340baaa000c0e0300b908450002d5044060070500208a221541003280040311500c284020460401100780c2000144000c04c441110b141036400c200600102104001d440300b03080605200b25100c0702c0261900301c401c84d451f1111108444000940140c405d40500341000e0030842c007590741101488074400060a410450503092181c140e1600b0504103842001c0c0c4000e50051355045003844120b610380680c0d014208024202c032030300003407100000d107408130f00c200072030060300003244c100400d0309208a00c1c40500300b60301381000b00e403138030703628034910700c7c1d00180f5101040b629100c040051006441140000642001c2500c00c245041c40e120000b03014980300d41802240f814a000512500c04155030102030320318000c8510b16200c030b4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43365328 1250 43364078 43364119
    0x40b0f09031501080105060a091407031e0906020301060e010903110904020d060207030914040b1e0409080c01060f0b0301050919061203020105100e0c0f0307030b060a0e120705 77
    0xca51554151150300c00c4410401941d02da0030b802400d2181c004030b0f00f4905101071062105103075105076985070400440b8291801515103050b4080e0452800040100c403021a5140700340717240715240300491030049004107010b026001075040c1c0340f40d900d900b1415403882c001111591907910000e00344c0b60f0b48a00070410b40c0b40150740c10b600140024040310712040540c03030b500202d80c040c0344114040380020031b0070000030043d800c0854501e0000c4404001440710080820840560040c41d005054a000e004482036030f43d84d8010381d04140c00565150300c440305c102c200c0d40284503d0250054122507442c00140980c1a90308590603102c010300f403051543c803004c1d0049200d0710082e4600000320b49030714012940024944042a041c0e0003079002051904000c0030400b954010780e00015240a126001c104404040d03a080314404032802404d207581c0e0390b440300102c0082c045002d510b640001e0018203001942c2c0e001461100281e401ca0b485001c0b140031603041640c071005440350700d0300b100b030020701d420001c02da0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43366578 1250 43365328 43365337
    0x4090911032e0b010905060a0305090c01030203100b0306040908030112170f040b070302070510031a03030304020a050607050c041a0429041d0d0c1b060c0f1a0412110102040b0f 77
    0x45c14008045a12440092055000302c42c064000a54590411070b00503c03c001880c40395000b803e045140d403d20f00c41c23007030751000e550298001c00040000400c1071501c0f00c0c4c2c081180c0a41000700340f81c070707541c6918502c1d8458040040a603020403d0b216850644d000810469102403a500030481c54640b4010b4003200d00c3e0084041541940501d04000895403507400022041031401c2e41c000550303000340d1100109800d60421040e0003507206200b00001070b01d402e10034905881045408588840c03983c5081e9242c040741412454200c1d0400700856110140414040401c1408440078030032201c41c1c140201d5001842407140f01c11060b804070550450505a010803002ca00c1000c422406400940e003082c0f0b0072a200f400040010140a500418490244101d602c861440348020baa8071b841d000000b80900c541c1c200242103140d030003150741d040121440020064030a40401c40d0b50078503281c24070182e25818122408081141880f81c0c503405401842220140c50301240b80303a09104a401505246400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43367828 1250 43366578 43366601
    0x70509040b16032702120a060e10020f09010503100803120604180f0206030a02120f010914040804030201120605030d0305070207080106051c0606050303070501020c01200304020d0302010204090911032e 88
    0x70100781c3c2181c030355024001c0351003250040c400070550341800d5082701d18004082c1c0010750110f105000901428a6020884440400910301075460742ca40107101d804840080d40f1503401c43c8000109244603d5001070784c01d210340030480d420071003480e4031005403469420b0110000d02c4102c17964503050051608001030340e00110804001814420025040d81c0e1091054880c2e0441c1c290140040165a0b098041d407075003059420010011380c10207603503141c40d6000c1c81c04028144a010410440480404c2c2d005200420006080f81c200321444900a40108425107014006000d801c00200c0c040703805000c0c0d00304482c0064a6444401c1c0c9101103d9500099001c04903044c0d80c4509c400605507504001429189009900040e901e000c0d00340024210380502501109034144a0909143c0d02d510f141540c1d071142d01034490302d840364100d140c100e00a200d5500500f4501c3c1c40d084000e41402021420010030b00000d400300c90140c1482c0441c0705500042250400300c0c1c2042441c5d6000814054115414068 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43369078 1250 43367828 43367839
    0x7030518070303090302030c040c0503071103070b19050610050711040f09080a090e0c03010b0c2a0306010e0402090415090b2d0405030f0c070509040b16032702 70
    0x35000100c0301c0c10444030742d00a900240d041c00050003036190500c48101c5c00842182c04110b1251180005801800003c00300c00902ca401440062250320a20840d50301542c0400f10075030074a0800c2c0a030748032122005c0d5003482186003400007040e6042025503121160b00a4655504000d41542e13044000c401ea02c030100d400540310161251994920300543c08090700c0340d401c1503102c0500c110014524026540300c0c0b4010a407038014408983c0c003440850b03055904190f42c159460452040044c946294032085c41c80c042c082003050880e17420001081c185500080782131321803903641d8903401c18800e03900ba40c0103035224100303c0101d0001400c20300426518500c96201296007210340c1c0f209a6002400c88541340b030311820031004064020200700b02800114828211259030030592035180d603074021003510b011503001c0080d4043e00c02c10204010002084001c00c2102d03103161524010402e00b40580ba54a4009482c440c4e0100d0719029004000510500301e022000b00d4204010401113000600b900f0b90300b00c7d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43370328 1250 43369078 43369111
    0x1012020703030209012a0308060d0c080607020c0d0804051908060a02090909060709031205091903020a060f0c0b0a0e030c0606120c01080a0b0307081e0607080f070305 73
    0x45424005401458000d0710016110506440013528215000d14014015508a003950b0400d01b081d00c184c542c1c6d9900361502e02410b030740c0c01000c03e100d09480034018000d244400800039007150005881d512801c003aa0a50f680030b28500c0922803014034058005103075070f0080c0420301003820001029104105206040e01301181c3d00c00345242060801d542101d9503036000070b5071222905000350075a4215440000801952402c030700010020060760000030000154038a10a81d0240320360282d4000b03000041207908160500c0003d140302d507170701d807108034003031007410400144c128002e000382e090309002605c03110050030b00c6541b54071612000521800045584009802d040c210403c090010352000d5001030081d4103001c8100032000041041e000115400078400b4a402c0c1d80c4080d40c6900324064020102d000340c100c000081c01c0060a40210342c07288190317086058a604500d07000001960071030207a82041c0c0300c0070001c445400f011141d00c400c600ca40030214404901c25805035512401c00c8004100a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43371578 1250 43370328 43370357
    0xa0518072628030e1005030609060f03010c0519020c010203030703020c010204030b040b0a0608190201180308030906100e0106050708160605010f0305010605030307020a03170c03070b07110109050c10 87
    0x1030b10066400c00c00301c80c8216902004054121808068101c1d0848241d440312000350f40c0280207110040106004107560301c089049501d4030280800b050100400a00c020b24141100130300d1500f05c419200d881c0d00c2c003c81d080c1c1c0316a0022803407005c0c2c008180e0185196a403214030540c0694010050b81c1015982000008041151240d515000d01e20400030240da03402c00041007001d9415070341040783d058002c1c0301d2110740900b040b411031000366828281006e840c0703c108c011640050040e4000341404d140041008480d140c085259882408a404031104e003d4440b02480050442400b807040403450400c10b45000c01d0000002d41684c0c403844074600c00d903128503a1a001600c400381d004c98000086d00c44280308000080c0283d1020300300c1980114140b4045800265040d070a174840500904100d91046019516100484e5032042c1030344212070340e541c0c551402c040c18500071203e0070001160000d141040000602440c1e1103103411800420070254042c082203d21324040006600740001200032070385 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43372828 1250 43371578 43371613
    0xd1707080409110903010b09070e1c050d030203180109020f040207052e0b0414041209080303130308090c13020c160f05040c0c260708030a05180726 65
    0x48010b41c2c10f8154807a41110705040c01c0d142d01da10024030807240390341040050b9078402d100d00b81c048011603031003003001312105c8d05904400076000d025009000e0390114101c1241c258004500032622401c000e0881e544483c041c034202c42e01c4070b0b002540b00300f041e80d02c0300c018903142d00900a180e0165081c1c43d407201700c0b1187e07520315624401c61890072021041031001448007507c076903041c4000644c0e00348000b5868011005401200800c020540428100540d03a02440b45040401400245007165600d007016601200c043c0000001100040c50307a4000807620030700813580032920300b03014208902c6038020440190180d04100f01c004514070884128495401d0360814441c010a03587c41c0d154800b038204070500003a21a001a84400d1004616220000036000141540c81034100e01c0602d9000742122311045603131160b190060401c2c0e0020007441a14402948214040c0010200c02190280035662141e1030b0502c51088058441c11b51614580f041c04403040005503090714400d40d201100c0011200c0ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43374078 1250 43372828 43372841
    0x14040e01030605060a17070f0b0c100c03020c030d0b0406090209060316030b03030d050f0703020a021c05040504061404050108010e030a200604050d080105030a021507030c02090a020a08060d1707080409 88
    0x8078030f80c071005007006851115030319400a2711340d855242c1d141c1445030481c81d540741d80c0c070140d544a141c2e0354003a01480b0317446507054448006075542541d641344254041400545801200716200da481c04800083c420703c00e1081b141d40c0d150207012141196240d0f04612070190524a0040a05440301e0300c4120a640c00d100030542d1060490b0b0010791801d003c00c05403051000107040605141c0704120700408150001011390013114036521191060010540c00c84190007150300490b00320303040410101c1c4440210300084040f40e01542d00b000913a0340c8038806801c0e00c00040404000360020480510130030320644034504d0400b110f00503080c41c44003a2040502c1c14034211001e8619030051010f01e001c0f0b5070f00900c594010081140100b40c241c9036900000c110901c1c1d400e01000f12040051900e0406004080e00c1989a800810401503440c008141c140a98045084080082c01180000d4582c0c0750400035201006d40200e41042c0d0f000301110b11804981c4181401c2c1d071001c100788400251464903000d5103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43375328 1250 43374078 43374119
    0xc0302040c02030c01051b1615050109090203010b0a06050405060a090302120705030d05040303090902031f180b010804050a020d050f010603060b0906060304030e01030f0605030111030714040e01030605060a 90
    0x3d599030101e0b0b40d0414211580030380104180350b20325801e1188400c81e07074145c42142c4c09915001d50152114601440178422100c0850169401d01000054000d559444010103500031b500a001090301c180070881402c8542c000c0034041441448103028504000006d8140100b8071b0030040d800f40d03101c2d000036600d10300e21107144455610151040c030040c2020b1115108504903820320605107829503070b0107070210606028025006a01000080c1d00801c065000000c0c00e403240200141c054442da171f100440070188104d11515810502800301c55446001c030648915009405440c0d0f0085590030401008030182d0155100e01c44c51000d04042c1a083c41900c4c0218410700c000500d02c1050301c148074807183c0c000d199910a54041c01044081b907084003d03204807038024031300002c41c4000100981c00a2140c1e400542d007641c83c1c03401c141080d4200200940c000c8030540c40d290b18500c2c408590000902c42c80c0100c0400560304001000002e660f6041641c2009000705120300d62922640c1c044030216111444 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43376578 1250 43375328 43375333
    0x31209060f0204050406050d1707030c08070506070305060d0c0e0c04030209150906040c050318030f0c031201170d181701020315091302060d090c060801090c08150d0c0302040c02 78
    0x10004c81c5803501c1740d040100001e03580d0342c0124040e501c4801804841c41083c089089000030003008140c41600d0516040d03500420890300c070240c0c1c1c1002603403a80d0498010010030301d49000300742c80d860070b91048a0f650340e000160881550814000f034241420180c5803880002d010700000c0700680c0e441a8540c440c40f83c03001003d100c0c0d80043d04100c10414003520f0030340614a001d600202ca141d0210449512502c9881541101528291000c4c43c0d8070580a80c01400c440215105a0103680070004103000403107101031143d9640c80350442030401500c8440781000746d1040010361445c03070207003082d80103802000c484105016600c62007607803114141545040940d50010030040000c00c95540c107119410151650b001503e003c205480c0f0040304080d0192003440d01150b5045002ca1942000405650100c0308202041e903030940984998001c1c0030311407049050045d08840c1522413118075100d44c422200c44540c400c0d900050040c0341d50341c04802e0360540c00010003c40540c9480c0942801102c043d0300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43377828 1250 43376578 43376587
    0xc0907020a030909020306012a0209090109030206011703031801020717040303120e030d0207060b030d021507020a0308010918020301090c050f0d0f02062d0403030305010819031209060f02 82
    0xb03004080c24070980016200510620600020380d030b0040480c0b9a2818403004864107a400780d4007614590340e040002075100e02902d0412848039419004141494400d408480c5140d17251280c0042150401c10b00030a40e44c018800280410080c102c0807055028103000107251203c16200d8215031403074141050284100001c0400070580d1009543c8020006000100f0501c1d0300c0c000311507100c5c0310b44003115818a40210b50300c010300c440380c0c0c042492000c0080032100300015212002c0c2d01e4000240342003000780308090016141c0d500204000702c0f0140c3c0341d0f48000c881e80c00e0001000081070354450b24011545090b01880060b242440303940f0a49002d0140d4100b850318000c10040c08008500229000e400c14041d040e000800c0d0440b03400c411075040303c43c0c9440d644600349402d540d1050b080341d05484646114410310942c000c0c0018802d80b40a650207101680e01c5100c0a41d44d90038100010341200410442c0c000845d00c11103282d0f005401503240400c44501c261503017810317a406880c492416690014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43379078 1250 43377828 43377833
    0xa0b120a0f20030d050a030f020304050c01090e041109070c2004060602030403020a0b0f0c0a06050105010e010305070f0f1e050903010e01060b07060b0d060203010806040309080c03100e0c0907020a 86
    0x11101d110560a8800c4403004940030300444e40780e603010000413040c02004a40c4a0209002e504003051082d021442103480745064107015681c0c412081c4c003540825400c0c100400c000e5040c0882030301c5103400802c5c0ca00304064403010302c40c10f8138004241608000015020400040c0300b01c00f001c403506082c841403080710f41c0f80400c002c100d81c039590141055502c100010001619030307181020031500708111580d151249940b28030030601c02c41410000314003801c2e086400300421640198140c0e00b0aa8a82448102400054086a2058801e03a0114900c2544c9154062140c041c406618000e03141900e004da14402007200c000413101c61084c08220041003195242c1424484c044000d86e9002c0240a145e1800112030158480e540015180b203480308c41440e145d031178000c01e0900b0581d01850071982e075a500c2c1e0006490308000d40b000c41c0000c00560380001c1640002039800702060005020f4250b89125654420040004920603800c500803419000125070b01e800b0254492052900034081c032031800d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43380328 1250 43379078 43379093
    0x1107050c03070806090a080c0307080a0f020105010504090b04060209010e060a02010603110301060b03070807050c060a1a0a0302010e01050d14091522031115010303030204080d090e0a0b120a0f 84
    0x19080f88055901100800ca405400083c2162003d070708110056901d00e000303181a81144034800001d0221400003c603c102e26034840c00701c4965580940c0208082c1e620740d07003000191102c4240c050113842800000c40d0100e001035008101e00c0b0414100720561149100114070390703401c034900180140c1d540d90001c00034082c840600813000e280c100c000300411410400c5c0403015001c054040c038108200d88000400782802030084540a0604c101280c42300d00e40b44005402816081c1081c6012003050316001126042509005059030360503180c1c01215050440116910341222000c4505070b030703e88000c81c4000c802420341ea801420a10051301e00b8418480020b140e0804c081c0a08601c451454444c04201d90f02040700c800f039681c1454400c284403c9003c50919000d0200b03400e800c10845078000004060301a401001100c00c3d04007520b1040c1d000c070760162142070f1288036085540701000001000240b0980c00b02c0d165540041c04840303030b190b0740d00d80645845c08000045a00040b2001c0120034490321 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43381578 1250 43380328 43380343
    0x304050a061107140a030602030a02030a06140307090c0306030f060212061806010503062d030c010e01080a020c0313080f0c04050402010f11012d0c031104181107050c03 74
    0x15051022482c0780c007071005696510540b10301a2844a030f07043c0380c00141c0d070b616102001550001c00039512801c0ca001d03010b000354400d440d0f94a26a01e000d000060758500c8901c1c56002800c024007800c550383c6081aa000901200c902000405648800c08400521070049114104c5c0c001d840040e11901c0080b00381165600242c041c0e0310070030a03a20400380305121061300c0d075482582840c006450f134a60001040c104028102d0100213036910110490390114088120941880d00b01c0c11101451040320042d01d01d0346000d8002030000307c400d0000740610b41103070000c00310381c0800800c0381d14110031a8100b40c0040501d4001d01c4a0b504140700f00045554204150401000c00703d81c10025070070030390300181c00280041c0d01c500c00e000340c5244030540e020003940810045406064201414825840d09510f54500c4403001800700b8a0a5108082c5620074441c0030402e03441381d20418501810103420900329011622009540ca8941c0c50f03018a50005a002d45840c0f07105038000c1890114150425081101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43382828 1250 43381578 43381589
    0x2030f01050d02030706050d020708040303020a05120c0316020303040504020403051005090115050d020a0905010b070c08010b0108040f0c050a030809120d02030a0f0e06030906070f050c0a03030b041d0304050a 91
    0xb0804594003da5804900641251220309080750f40d1244000844041d004040c405441948007080002c20b041d0003044118566118400303403141b2140344a21160791303010711040540781b42e005000e0400426241c00303005214074001021070b828295154005410390384260402c6505811401448401101c5e0b4000c0c01d0b00030756446c1c02800049102c804040b0005a14801c15200301c20f1503442c0425515603d24440187c02100390510556071507140303080c00d0740c2c0030ba94100c401a801d501c00145450040c4903000301d08905039030b46800c58030b482d183c54044181d500700c10784070079030910400109580c542594000852003001c006480700e000e0780c00c000411002005002140e0420b8a40c040c03665800720480340d1100960030b1480741e880301c1c403404030b5100c42d000f5003050300514000b0501c00c00000001d42c3d2842781c40301c0c1d550785d402e200c01c4140403035013806030000030b288a901000c02603000a00a81010340d0740ca40141c00003c89200c0031a14000081609240721041c0e000001c1c00e00460600300300381b2001c1d18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43384078 1250 43382828 43382839
    0x406110c010c020405070315030809101d060306150a0309060f0515061e12040b13120f050d090f05010509070e0a0506060f1c0b010905031c1209050102030f0105 70
    0x96000042c0c01c1c8211100020b00c155074940c0003802c0d26000390b21515a44100d88104a14181c0346d152500140d070140e1046449141c50030b5008103601d1050940040c00d01501220f41e4440044c2018000160400340800f90301602c48101000c5044000010b000e9100031968045612034140c18284100c0303448400502d09a41401c08000850788852403c515488080d0b44c41c40e55042c80c0301c230343d0200034442c5014494800001580c00c0484051002c91401107003e00a02411a02c5041d1030158407007200800422140740500501c0e0b800d801801d8140302820300d402c0c814500308007240d40d402202c241c140100c601510202503602480702c248903035903002c4002c0c0c00a00e903542c100159a00103c1004001c40c69464072000014441c0e1500b00a4500e1000a482095113400307143e0002906080c0c403401200d410340c0340982041b055885181400300302d507806800361850080b00f03c410b41e150100136100e442441a40b50211009400038403401d400140580c00058490629038000012590103911142c480e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43385328 1250 43384078 43384093
    0x90303190f050a05160507050a0e10080304030b150103090c0b0309061605040504110c0607091509050f0f030a140304062312090c0d060e010c031509090c0f0902040611 73
    0x265003020483c0d17100c9005c41c811000b0990b283c0380c22480d0041a812098001002c0000014113aa524016500814141c02c041c60300d40e8a400d41c103170341c9024520020304600659004210b4019041a420100d00e20600d4086408081c1d503c544890b441954880300c2c80d040000100b12418009002c2140c010751384040f640b0345a100000c0040c0503000314001e617449590f44a03091000f03015141d04031419050a002550200e1400100c09000301d070f132503c17071081c0b018089451108014402c4005800350f810050a248004500d8000e00c00005860008141c1511034140440085000c60384681c50b41440743d0021959203081c880001e24801c0d40c0350018131310000046220300000c1c4000c0981d5221030001030804080da81d2070308010302c5c050079800401d820164400c41c840520a40360820301c042c1d2820402400b100c81c85900031821942180040b507407601c034141007401020003a400c07210806025810520304207442d5065101d107041c0903172001ea00240d001078204145900021032088120048001d03100340e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43386578 1250 43385328 43385347
    0xa060509061903050111090109080c0a06210504150c03090c06030915050403021e0303100510020127030201050105060c030301030809010903060e010e100b03030d050705090303190f05 80
    0x89014207500e12403941c0d2011031038141540b69008000f107410000a10400d441c0a20f074885542c81f4940030384c0043c8031040c2c0401c20140c001003028030030f00301030010700e00c8910300b007401c44106015511580380d2521150b0b091440700114002e850003140201d23900d4100142880081040340d40d0b01418600380760401c42000085001101d11400300c81d9517040c04074030341149260081605c14040b20303007000070303140c00188410f0690014010507080c40304502c5e465006980700f50b90303a89002c119510000240500024807650034111600307208211940008a030034090541c884c02c200745081440c0d440b07803090b41005424190309014150060005850032840c0c400500760341a00c84c801400041c0000c1800200409140d1084c0750520080da08000d08000c1c03008951540c9000c0c0150081052081c403905002c018003060602c501c2000320401001145424140640c44014040042040050003c1440161084d1700e003800240501c0c29404800c4600c1d43c51326101a0811004142c000108501403048607013 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43387828 1250 43386578 43386589
    0xc09120503030c03070201241503020301080a030f030e070e0a140403020a260705061b0a120b030703080c061e0f0f09100f060503060a020a0c08070602070b040b0604050a0605 76
    0x200700c154003c03c6592590b8140080e800742215400c03c0720032600c0c071108210b11550310401d54086d551020b100c140e09005a0004a0980c0020300441c6d640390408221140028001d04207400d000e059030030040b8880404194040c20543c49602076100d0580c44000c0001d103040d43d126040c00c034000050402c0c614182500e00a550b4882c10300020807612030424150b0040080500e0808a1504070340d0142e0703202c4091400c141c65010070f542038440d019040781a000c07039680381015103211703c1407592091708068520001c0800f800c02c0850581e01741c0a0504003002142d000070040a641c02007070000d000d2414000001c10781c4030000d001c04041a1401e40038040500003105c400d98000c0c0040e500c80c41151104080c882c1400804800204c0141ca000c400340726820494010034201d46044060f00c0c603039075916101c14203074410218280c0009003002e480c0380004020b200074107c29406850018208078140d0f4030750590034420b071401d88403054603900b000524581409030070b070300102103e02448401d2501c0c0c042030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43389078 1250 43387828 43387831
    0x71101050309010b0907050a1106060f041d01060b13060e1f1115150d0b0412090b0a0305160c020a05010305131b0512060c0d0203060103020912010c0912050303 70
    0x181040360020200705180340c250081c40d000c860042040c5001c0c18840c4c0090200d5012086860106028072500b500c1c601d0040303042842003201401c2c1642c1406080c0c02c000c02030807a42002d00380f0301d104078041a44902c0034851840a404840c01290741c4200c03140e40100f90045550007842000140c0c01403003200d86030701e00c84107102c03c2d483c20807400b50b80505d41c098030041e507120700e0041684074201c26009440c006590081c021b03d887c40c005200700c42210309100032040c11520142c92000205c0110b000a83c520381ca10030881240e01d003c050701070300d40c802d1100c00e5100c01e0b13102000a8480040c008400895260303401c000c0e0039403c00b082d0925083c1e0110b04000141d00c03d0701d06050785e0f80c00285149842403100d1910715403104a181c540440380202c0118010f260240c10b0084c0300103800900300d4103001070b41500601d01345071064100030350b03000124082c2d4001001381d810980c09105081103925441d02050009500c400080b400010140d0000c01c10724443e80040c50204803031460134041400841100e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43390328 1250 43389078 43389113
    0xd06063c0b1c02070605060f0102070303020a0809010c080a03050708010e04020d0201030b060405040906050108010b06031e041704080c010815010903030507141507020c010203070b010513090605010b0d1107 90
    0x9521640301c0400b400440712070580c00301503280001078410400c00554806840340000700c415a4a45480e0401260b0b11605408001c0150340300401e6040400c1115003e00b5014805241800c4046010398407200b031034110f5802400465203800034090019003281e821405400003c08030100c504c0d05030002603000001d0103007c1d06156450070402555110b2900322406004042c005101c00d0b4950319144008203000d20440640c4c0d440c04220110900d0140c0840c0d01400d150000c036882d80948220203a9007183c09403044464040b00b40d415103854040300c010704000c042d1440500889040c0740009040c1c080c0c0200300c1d90b8555000710003104281e070050117000541e5054901583c440c0c81c14940b68101505424001420344659a0072004080c0c00c4008a0300c02e0030030340d0a0342c42caa40c590005aa407405840c0c0000d020003a4400140118180504400a00c401c01c0b4004951a42282c50b2507085a0080e00700e102011000549030b81051070a0041802c40710045118514000a641701c161070246404000c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43391578 1250 43390328 43390349
    0x506060f0d110a1d0405040c030813080d03020a0e010234090f0903020706050c0c01080721060815010e01050d0c0b041401030f05070903020f0d06063c 66
    0x19081401e249038405821800c6950510f66991900034015114110222060443c504864540b62680c14030b0f00aa5000b41d030301200e111f5000b41159580405904180c0c0640302d510016100080c0010003044006d441c19071a40300143d480054207002410303a0403680c4114190740c0039000310000c0105511001010310901d003113100d42c410680e0302107a60b490050b800101018101056822070f00d129a201c48810752007502200c80e02680c0b414103642e14099450130407104d40003104c9807691540a4810980d001c0014030b0110128859003894401103180c1140420348159506400c0c0302c500020030418000324943c0361401840d614203e0786002c001ca05000f41030050b20440c8801c0d01b0000900e000a0240138070044a944940e01c1d00c01c4640e1020500000b1750000e41812a400b0b01c544007807140600595503030307030340002107429a000e01040300902804a904802c0c280b4110002c16070714030482c4007070322a0380541992100006100c01d0745d00080700e91070304400041501e0280c805a000280c00454603101c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43392828 1250 43391578 43391587
    0x213050604060305060a020a1b031205040f020402130e090c09040f05070f0306020d06060c020619090503010e0f010b0405090a030c05070e0a0f06060801080d1209020a180b01030506060f 81
    0x400c025002c150700003411032150f9800d01c00c03038003007a030040d00781841c5039076822a07001401c4100c5442050640d40103004542d80c880d88480e17102064010680c07050080d44d00c0d0006102d1036010070103d90007143d00000741a00248180b15040f010051940c220030407400814500007840c2c0003866014015000a200c452031000e440308200003400285c00a00c01509900380180e90b90031301c0006588041e046000305458a8004030300c09000e402c850700b0365500501094100b000715450140200d145804950030b010220300300090598003401803581030540700d8041d00c218400300b00300c2030070340e80c85840d8140f24a0a0000304054008001a085070b000c3d0540f4103400c1400103803c0481c14494990040c1c0030a031002d07801c01040500a40003698440020031040029030341d5548200c1d1542070070f0048600c1130f00500329104842d0b00c143e42c0d0a024a0400310002a81c1d11590300084490405038065034035400045038107030602025114041c5c0000c428202030090b490690f0006040c4d1056040c0407809100c00308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43394078 1250 43392828 43392841
    0x3030c040905100e0403080a0e19030e030c040c09060206180c0907032a0206090a0506010b0c010e06040f0209010b04080304060309030c05060702030d0606090e070507050a050303041a06030a021305 86
    0x1c040001040d03010f14001380ba083c1030800804405003141d64200840c00e0400050400000103010a0300c9030031041321529400195904a542c00750a540c429030511802e174901c41146c0c1e552094200c5000251200c60301e8600d03180e806400c10340b005040082100380701401c00116040810f958907044130482d110304556840c04010740050804030300740e10003416100d00031604001d12203c102c2901b005030f02155101e59804062031307641c080031900180f040c0c12080040011184002c083c01c00c8030b0b901c0c800030400303480300c3e19500c1c5007c41c100c400380e81d11002c0d68844015070604501c01805440341c5151285018289031143e503032403007607109890030166141c3c410170500d481004802501603200040c0c0b4049d0914902c001d540740c03c60002e4a08803850a400080c0990140607160104d6000010300c100c0b507521030300c003519a5003000e071040d1680e004181a40b000901c0610040d48114400e0110750001501c140b080200f100e001000180a54484e840c00c2000d0b0ba5002c10628607800040c41c04100340d80d4030b5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43395328 1250 43394078 43394101
    0x70f0605070305070b0907090b09061f0903050604050d1421070c0b07120b0a08150402030f0607020708070b04061706150403080c06100e16020106050d06090605010803030c040905 78
    0x2000030341030b40f00100c24400407440100305031f401c80e841c0e08010700400030202c040001c4041c003a00c56a0b8010300d4401c440c105c2c1c1030000031078400706100b030610084a5a5a40300c03942820300c02c8070b040b01c01d1b80080c0240841542c108500c00000a16203070b0b07940c280384041c400482d0b00e07c050780c83c0a8000c1507010000e591280300c0c2c00c065202070b0380300030305050b07504240c40080c000048005099844500b0403120f04102e050051200c5e0460740c240009080900031500d0403101d042e0301520690700750040921404200f101000300b02c0c0180c1d2954003c0c0f01c0c7d41d24051000e401c00c0040e401c03420805100b04003c106042c0e01000900c0d80680d94142138000ba00c60340000b4001c120702d100700440c03a038030100380002400070080140181c28040000c2c0c2d8801c2c1d86900c00c100c610403041c06910304440303461010929900120840505800281c000020220344400008031896203d620480310682c9402c440000c0004034001d0b140180300c218011800c0d030038000b20710649400b80d402180b05041d5500c0000d404901c56 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43396578 1250 43395328 43395337
    0x409021002010b1005090d020d06020c0613030f08100b0c070e01121a01050d0b090703061a040f050912090105040f09060312080402031e0c18090f070f0605070305 71
    0x914451104410380c101030301a182c61850184140d00d100c410518a0703004100b00d41042d100145590f1400301c00b03600700712841303803860025209158280410045128100007141c054503034072070100c0c41d015845c9401880c0310800e1070450104980f035400d00030105846a982026260782c1c0c540740c2c4d1036000c48640c262030003d465001c1c04070130403908000250301d000388001c50f021038011802c8142c503a01d00b40350344284c0b52081c41600d03004840c3d10350720340108078443c1c410317600031480400792007609030350752244070070341e24100208261494841c0c40304481c1c0ca014400c846a071241110184407600c0c3c840c500a85440403400251100000019124007607031186048070054280156050065601e403a28180100b201c0d0104072402d8110030b140004240c0209080c3c0e2249074010020310404821402c1c8820001c000e590301100c80c440d00c20030415990b1109100100614007881c030900f00d2500303003003103032401844507490043c80d0450700c404c1c008421403501c2c440580c2d00500b0321540e5034000d4601100c1c14440c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43397828 1250 43396578 43396583
    0x8060f06090a03080a0207120b010302010507081204030807110607020a0314040f0e1b1306051b0a0605040507050a0b0301030f080405090109091208060d020d14030a020c04050108030c0307110409 85
    0x4140481000700d080c4c081e0492442680c00c6a000549441c0181862992004081d1110390300c0f400401c0190f10450042c018184aa0085410b00c0e0b5529081440110161412008141050100252030703a00100c1206404901c1009000604020705c000c0e44400340e490001d400c00001050b41d07510b9121400c111002425405480500156506000280390006944800c1440302090240d07044900d504207855909500030654805946008000d4525a1001e580418004030403113240c1e441c46414842400154040e150104070351809261035800c20645401a911400c00c2002c02c0c000315100301d0650f8103403580800c51260200c110b0402c0b45030b40c02650b115a5200105400201b03a604040c3c01660743e15100d11030380c040c001400340c020f0340d8001c0708403152a0080c81a481d400058a4810707038264000e0b020329a091070b440302100082e400c0d40d100b181b000c40940c0c09010301604a003080d00c20f0301d0043c00440080c60618140e02d00d240e071240301e14103018010403540c041c0c0324620f81e1143d00c0100042d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43399078 1250 43397828 43397839
    0x506060708030f04110d03260903030c03061f0c030905190608040614090d0201051b07150902041a0910050d020108090c100309030f0c050d031e0609050f0a020a08060f0609 75
    0x702d440c5402404412101a030070b9500e25407800c2c0400b43c582c6089064010210707100032b541140d9400c418865207801c001c02e103552285980d410141c02020002c8007609c0e0b14480c0d581c6000e8000103040c00b814159091340580e0044103890240180d4100080021007910520300e0710706000d450b1410070001601800701c01c03001d02600001444405c10001801006414003a0001c1c04240c0e42d40300c404075000c80e1800404c2081604000d0980002d800e04602c1020003100b14000170300100c1600031408850750061995042440171a1032515868101202540071510458000501e800d02010403902d0b80d8440009040c04a204045085240c05120030a4510f1016040d030840c0460044010081d10083d102074011400c2e0080e84c00d0824801c03410305101e29004002015080e80d0741034110000c00a10000220185044000c2c200748803450040b4002032032012000f0400c6d04003c180075010120140c24801030760700c1001103440440d00300103c203a11103400c540c00c5c5801c2420002041c2c1038810036200f540e002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43400328 1250 43399078 43399099
    0x305030c06060310020304020306070f030e01050a020306011227150906020901090503010905120a0e0307030804080105010f031113020d020304060603140307080f09060912030d0506060708030f0411 86
    0x1680c0010391544034040071001c440341c008412850708201c1c0301c26940a509a0452070000d0222800307450400414000380c80c0020f603466400301c1140c01c441d01550030540030f5400100b400700139a405111000c905000840030170404600800000030751440e071a2404076800503162400074401070301c82100404100440c140508101860254025800444881c0c0403454800000c110750505100b54000240e0001c000d1000c0103008940c00b14682040a10300700b0480b401c0000403490320240007940096124128003501c1d141004200c07420740307405811503000030004410070004141c0c1141814401d00d020b8555664100030300070043d02900c12418841c0c001c50000040c0800c0240d541c0c05501101d0040d036403107058401284003076460344143e40d0090080c1c41300344030f044841c0243c0b00040002840c010106490a030301e0000ac06d69070700e80603008441d02d800203d10101900c1c2c440c040c0649c0864202c0b0301900e0700440396985003160101400c90080515640002410080c00c0c040580410900030a903170f840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43401578 1250 43400328 43400347
    0x602120f01030201140a0f08190e070306110c100b0d0c0e0a0b0405010b0a0810030b010b070b0a020a0c0602031f0803090a090504050c010c17031e150109060c0c030503 73
    0x10400030700c003c80c0001d20b01c29000c844111003000740c80a504040e521321000a125030402c031461640a000075081c0ba220741040940707040b00e0305c1044010440072003e0f004881c6142802d2040721454481043c1803001048100118180414500a81101d1201c00a011a010701c0861241d41c64400c1c0140404000240802c800340503051991169003035030014852407020b2001e100641d0003c0c8101e00992000707100b01c45000c0c0c00380418a80c0320016903141401c036035132901da410301c0d00b10071303800312441c800e0006503601886041d5105a502604044055260110400e802005101144000b0745515800310215440c2d8003034007c0c0107070110000305a1000d290b220b041c03690300c1c2d6100c14440f0380b0940c400c40c0300180000c00b501850b48929000809009500e0004e0010340758110b1100e011501c1e004d2030308403007500340f181d200914003c000c4070f00e1a1140f104000580d8601400c0540101d900764164400c6807003d070b91020341c28003a0340750761034121190459440d0082d4150b00c5608010504d0002040c0d403e074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43402828 1250 43401578 43401601
    0x311010c090915060f0309020409050604140d030b0a0b030702010b030109060c020d091802090a03080a030606030b010c0c06031e0204030609020109050a03050d03021e0d0b09161209060212 82
    0xc1c0c0390120000c1200541426018001d0b0070240724010100d145c0041c62041140242c0c01581207030b0010b400802d62002c60340c0e40fa41002c81c1102c007281c0341e00415052650101c3c013080000a1b4107540e0504114030700c83c0c4400101341c0d003410710031410a05400400203810314409e4000c424003610180090080c4241c52074402c000e04a4001a0340c0140310b141465000207101d1070f0110119102da0640c00d144423221882000607500a4036095040701c030700000000050b00c400020050756000da600058694140f50b001001d50b00a01c0e0a94100100501c182000c40e81005100d4100c607101d00740000c803640d100408030062884080340488480c4085800800c0c44001c1c0c01400d8003500c00d90321440415100c60401080d2007090001411030351100c0c0c6442002402a4001d00a26200402d440640e20303041c86425240d6200d242c0c000d06240d11502007000700d0070208035050f00641415140b6090054203540202001c3e00354140310350981e140c1948000f0302c08c50768101c440c0994100c00409507881c0c00711603500d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43404078 1250 43402828 43402847
    0x7030e011a100306050121021e0c011104140108180a06020c0c040c0207030818061b100b010f03051003080301060809060105060405090a09021203190e040507020a0f0311010c 76
    0x6004001540d1000b810a110744070310802c3e640c0507100c150701105420081c01c5403908180c603104080b0f0f070811030a81d0421941540c40c000c1041d019010380d81e440c071039071080e0940380b4140d01c0a507007071380520051061220000741403071403040070711b803181c443e649002c0d10f11494001e0710310040d2907000e403100b00341c1807202c150005d0000c904070204441600000c038041c0002c40b20003d004100581010009100240300d0100401440ca10407011030180040d090000b16240d0041c01c082446490350702d0ba000000c0410320500300c0f480128842001440208000600104168035006003010755510010307901e0302d1950341c00009940c205040c4d035100d6844180150018105642e4411030344901c1c0c0000455141260880e019560f007e009990580c9484400f03101408520408992020248002925000042000d0010100c092140c0e1001020352180a445c012406120718083ca0a20303082003010313600002d6483c1c2699025540c0c45240308607042c03c07130707074240c82e43c01003081542404185050681d200c580d84 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43405328 1250 43404078 43404131
    0x6060f1404050a0b062106030f06010b03041b120510050c03130606030f0311060903040602030403080f0c0115050414010308030711031c1b02010c080c031b03090618070806010b0307030e01 82
    0x1c0301980ca94404050f40c984807270b041650298044030051107003c40c10000b030758109102c3c101d2804c03c1010340e00d00c00440e81440d04005103070190a80d403070f03040c040104508062203101c401c0c00c0006041c000c0a207e040d00c00142042d1100108103144420450300d030340080c000303507041124010f10011618008004648000f1207050a05c20702012807490070002c001c50f0220741041d001185004e1a59407080150340106041e14490b41040c072400b00f0512082c003034820302c034401c105041440d81c140710401c022100b100c046140400f1300d40c07005100080c22403044a030060020308100b0320564803031642a103184660000303600c0400100c0a00700c551850b40e00b10303001d8003250710307240c001c3d200022400324204d407007030100c00002464140110f0f00d9204180c00a5030040504000030390001c1101c0351500b220350065400d50b445920400c00c1003042d60203044c0120b0781c82e8512026000851800440381d594071010701558042001c00004103500e580030380d10508070045400000d2002e80c0c09410502031484210402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43406578 1250 43405328 43405387
    0x1206010b04051504060e0d0c050303130608070e0102191e06060f05040b030a060b010509041a0a0906050102060c18090f090f0303071b021206010e010306060f1404050a0b06 75
    0x24080c003c04450140c0d0103841d00d41da1031004a0f58008100001002202c84c1a98000e2841d1808655500c042c0f0042c4600c400350f5080e01c844c2072030b007032004001d0000280081b042000c50781a8402684c0d01107515164620203500e4003094a92504110f03854804021401744207480d4040400200645600a4021220380c003607100e1000707950b1400c1c001940c4110020355855000104c00318001003217640900941e0106142035030400c001540820704440c24000320440c2c01c1c4000c80440c060f8600405044040c0000c04014002d0600e4140042e65498014211030303100310f00810405650750030b10845000d089001800400c8506200d8440740c090030382641d048951780071300c004400c944480082128008d07001943d9800b02c0c0611001180e42d03000c0d80400881c1d108104411641c4046010021b0354042c00407400c0d8501254910706c0c01000300c50440c0e004108440b6403080c208102c0302b05056204c481d03001034602080369603403401404c008003c082c03c0030b9480305000c2000100e80038110340824815801186 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43407828 1250 43406578 43406599
    0xf080c040504030c080d14070210050115090b03090109020d0b01081902030c0d0302010b030102070b07080f0c090f040b09150a0b0405030d110708010c02100f020a120b1206010b0405 79
    0xd100c203403041202d0140214516440803000105444010942c2080c002e400003586812071011224001069a1400c0140e110300b00c140c070f000703c0500c15540104580380b10000c0110b00340300f002d0000c900303078411051524004000150310010a40206050541c005c01d00c840007000b0389001030710000300380603c0c0700511444618146a2414030091842107400800414403400036000300b040080d08400210110754803002e045440d0f4a0174006481c2c1180f01c4c10035001140341001e030007041c010b0b005209484c0d04e40c11806100c50490035000b25544050140c804100304005e20000c500500498034580b13800c95502020407404407413030080c4e07003040c00c0204c502500c1a6500e80624616001c0e900450768190446400c09115500400c1024905034001c1d00b49c40c5650b585015150868280d0800134000da004444001c038511424883c0219852840000710309112840304010000701418020300b40d031550303c101143c0035540f842d2151210011080480d001c640e1120b00c1da0103150068411103002d2955000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43409078 1250 43407828 43407853
    0x3070806040c090b0a03060e040c0302010f050a0c26030a0b040e0102090f09040201030b0d0305040e0a06030b4011090103081608040e01080a14010605030c010809030d060f08 76
    0x502c03011110260786890469043c050f10f10300741c1c0e001322a25414142d40e850000f88161900141901c114052500c4140035403850002501c030b0780701c2c0134148007044420090000400c0d0040056558250051101d48000c0c100f8060a061151040204210b590700441040040f01858000c08200081500c0600400d1200d00e043c0f400d034090900f089901403400b19a0a03030600b031000400d43e2080c0145000b00f0301208a00c046204d01c680c1820580c0003490001c2c00340141428201c4080e0445180c0100b0440d151850300c1e03410078054040c20741181946d0700003c1c400614100c4006990906590080c0f020107000d2002d142071041d0f040104035a2045c0a41d99030016250681c80d0174126174100586038581403955004048c840c022400449070b10005002c080741400600c07481c280606020790080803450314a00301f01c0003200c089841202c91340c0c10300406119a45011800c03038032015083c00d0000307440d12840d40305401c42c082c1c140742c0000c142c5085800564110301d80400412942d015040d81c403028a902c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43410328 1250 43409078 43409081
    0x7061112060a153213030303060e060607080c0c0415030b060306010807060f0306080303040605181f020726070b16050313110904060e011107110603060a030c0b0307080604 75
    0x43e850000031600c40011803000c104001907083e40c5015145400d0346a1030740a40881d43d5800100c2c04c0c404600c3ca0b0325045c000c0540501c103a0000c0c0030b80e0340f10554945480d10002e03144d8030400e000204080c03008100951000d0b4108a0308082000003131003440700b01d400304400c18008185200507984001108007003000c0e0f00b004600c543c180c80040001d480c04c1801c0c114250b0f8110404030001e030415540341000604204127001540c0124407d07100458942014942000404007551711102c2a421220751001c0c640032103101d001807160340c20f102584521681c00c02580314220076100b9104030070500780020072400c0c018010443c851103a04058400e0303c0300c4420100d00e040d0801c105000c030785c0810218018219000008080c2c40c0302d42c0d0780c200c52000007404259000e4094a086400c40e0311380b141c0a540d00001e0250304082c1c00b0449003242040c599407110100101048042802880000701180c1640c031030300403047c00303550410b04824400e90384004010140d40300b101e00c14001402c903c0440c1c0c146c0703400d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43411578 1250 43410328 43410359
    0xd05030d241e0f080c090a0c020705041d120705060c030709031509062a020c010518120f030c010f0b0303220807060207090b030a0201080a0207061112060a 68
    0x19840c02030261420000e810554036503122000b00d0003030400d10005810705514481e800603010304805001000f84003400d200390340c2c1c805000e0a0640b410310304641c2d081c0d6400070790607084aa0456022404c00410684421144c106071114a000d000321402d022552654100401900344500100c0784607645134801095a804182c07180c60001e2005541080130805409000070324501407080019001043c1e502c050032110194071084d1864440304162841170403014030590411020b0019095880c0400c0c0003c145118400c14000d00d9940b4071400501501c44440002c28100110202c0e14990082c10002d96240c000c8180900c0710740c2000455a0581c440b401103020740c1038081d00441c1001c00c6094000403ca1811001811104003100c000402c1da4040180303000410b52900a4240d940c280668241a00c3c5009c004c607002e41c1c0248014070050740c1c07105006a0107261050016104c400d1468400c4c0a132100c01e0000c0c1c030b83c130800300d5041901e0082c40420350141c502202e02c03d41c6581d441116610280340e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43412828 1250 43411578 43411631
    0x5060f040209060307121e0b030c010207060e010c06020d0501030507090516080402010c1b120501050907050603010b0c0c0303040603140a0e12070201180603020a0809030c03040b16020d05030d 84
    0x1424804174844d5802988544400110306002041d840104843d2103c60381c540e41724000f2494496854907158101480410f480003401c0c0301601480c1d06080020303000d001051904da0401071407192560900000d0fa040e143c05c9010003005000550392401c10700d9543d81280208803510f85807030082a808154008000ca400c00541c580140c141c2e05d13500150749000c0341400c103544074110400b016110712200c0d502c08000c0c001000741a011803413282015401c482c00140b0030348030ba81c00340109000f01d60303905054070b04440e0b120320005c0c0c0d00c40208182d1400e012240c488d2941501c008034002c11000d415402010100c61903450112941e550410309200780c031000461904039400501d004031744039255500825a03c1c1c018102003079550442906004145499444440083c0d4007041e50b00c4566442980aa00119194021414505030300c103501d40381c0c440c0e442103120030180002c40141e42412a003508807469002480416000d8003802c1480c0c0307036448030003040401c902e0301d11020140c0c1d09551507656104d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43414078 1250 43412828 43412839
    0xa140306010e130501060803041a07021e1503090604030e060909040201050906070c0e04030906090e010e0a06080109050106060f05070c050f0109120809090105010801060c060c09050604030605060f040209 89
    0x246021866042c0e0078000d00f00100d6000e480c0188000300300c09001c3d48000740301d658029a03580303240000030344480f0814260092202d0b0700300280b9015946241e4012f8180c161048004001c0d101c0c9400605009d50216101c99034040104c2040910400451114425402074452000c10032406007007104502ca00110540d01c45141404a00954441c0c005481c00403405400a07140500d9074480c0e0040c0305856004400d100a000d041004150303001c3c0301d00c4024061420454149410840f00020184050003440424900400000c00b4880950403074001460400000c0000302043d042c580d01a00b00d90007030f100442c4414140143d00c2c3d20a0301261038164006e0941c60781c0340d05000803c05c039400c0090009040010710f101c01704108150980b826581d6100c0d4021541e01c4030500c082c00040344050348407030305011443e03004004407904506140d040e55441078ac0003490000c142000da95110062b00b026400c4000800c000c402c025081e4030480c041c02c811559450302020400402017a032140d03801094005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43415328 1250 43414078 43414081
    0xc0111060f06060409020409021315050315030106030611030709060f02030403020409020409080307051903091505060d080318010f0b011e020c0d21020105040519080708030f060a140306 81
    0x520104100c2038001a000703100d107113003c0e55401101c069070842e4000f0f000347e690000f0041c85061029034684020310071000c107284c1f51002c40c0303406441350100410340b80c8031480d04110402e02d56020750042001d540c2c03140d400c10660b280e03441130a909800c22640320000c12079565020400c1070203056840c20a1015034000d500c2c050441d400d02026102c406412a00f040e04d461201c000104540040d6201d0256a0303a041c0d03e0f51102081103d5a548030001001803600e015842d4010031444450614200145840854a9200c0d04041181c00c11109405004004080180a0a0880089904092807400000b440309420003072000044034082040240400e807060441d15180310550030f102203000c0d050061b180700b4000100407940d65001c0b100300f25107070003030290711580c149a4041603804803441c2d403008012603d07095848541c0c0c2d1890141001114001ca041c0104128040003200c1256034003001d0140c0701d042a00c03605588210a4800c00e2182900c1d45000c102d26207613a00d504a0358800800600f920b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43416578 1250 43415328 43415341
    0x27030606031902012105041a0c090105070515012309010803160312050702010902090702060f0402240705030408010608031603050f04080a03020c03190c0e09030705060703050106020c011106 83
    0x189000c00402c034107003c4124156803911480c2c5109a000c45c00c0307600d002c80c0a14062802844002040018403207040c40301c2c2c2480600c940000c1944c105100c2800c00726901e0185080052804000244180d0303101074842c0041144116608084c01400702c0307603003208410100030304000c0320420901607808507510a03c448881030344d0404c290809940242807044184000703140b4002540c1085a41a015070345030306180c400c50505007422a4031003164405480c050034401c050022000c405170001c0c0c441c0e9009200c0d0801c001040801d4600960700e20724043e80c42095203000c42d00d0750014481c2c1c3c40346501c3c00c400060855404012103001d100ba95000261000050341d05603001d800442c560701440c00180400300e5402d5080015070035560003074000b0b0007080320441c10503182210007218400760030a0a0700b01c0c000104803444410030f440c0100084641d0750340d101c4895240d402445c00242041c425003003440303941500756120b181603030203560030b44082c41c503800700664000e0480d00c401e41c0903074801c01c0018007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43417828 1250 43416578 43416613
    0x706090305040e0702030301030c06030c021c05040504060f0806010902030c070807050c060f07060c0f0e0f0d02091f080a11010309230318041107080d060504022703060603 75
    0x81562280c1002800d1a0b2550141801c00b4802c64400c0f0141e031000005100384060380044400901035850140300c070700c01000000351100110031200102c41000f2010001142c01241074401416002c1c00c10010255208ca14140604051051100740c1c09060008a00c4007014000c4911890440050f90301d00002136480407908d41c80304905680d01d000341c0c01c50340c810f0356460009101520707096405a494003030508202d0210b804a44444c03080c8503236849001c1d0000d4100d04001c0d1100022518040d103080084040b505220b00050f0080d88a4180000c00c40d5001c0080d079840000b0b90513100200b040ca454208032590380700354044c09002480c2c61402452190312a41050140300d05c58020002c004107042c4040507204c0200c2c41100c11034001081d41099184182410070144d1011502030008d0191040081d096104070075001e0520382000840100480c442e0700005c005040203041103550300f0070041c0003038800070011307280311034245000d09060451400103000b84c010240103024110300e03e40c1512a55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43419078 1250 43417828 43417841
    0x3031b07050703020a0e09010c110606131d0a0506010b0405010e06030601020114090601410102031905040509010b0c060c030601020f070e060a060503040b13111002010b04050c07080706 81
    0x7502031161000100058440d10b2120700201042c0000c0703141800c1c440101c03030035550000c01d40c0302003003107036820030211250000b19550406001d8800031084101038064030090401d0481346080d4004146150a1402c400180425007900500c2602d08590321801e45003428030880c405c02d400181240d4101c0d4440c50100019074000c0c3d8140000039403985481c480c0404404110f41840d880e400c070300700402400c12145d5000c0702034540d8600d039140036040d500541e8550081c40c0b8600e452980c01d1484000396034020022680d454086244a480d0455583d00082007a4001e000d41c2c2d003c0c00c0c07010000622001c1e003d0548030f0100100020701040c1e84e4104c40c03626503400040c180c50440c0b164010003442e4140c24044003028201450b001c461610b492024000203821540c028410004104208008508140c140641207840c812402c0100c41c0c5908180d03400c0784100041a07030000c07089000300c11031030f0154400c00826005031401e000594804081c4401070090450213091001c0c1007140400240d072036800789 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43420328 1250 43419078 43419083
    0x606020f03030118060e130605010f2103090f080105010305010c0f0f0c0201120911100206071709070504060e0906061e0103050a1805060103030315060e06030a0e030c0a0303060803031b07 82
    0x10010386d5210f055081e40c01c01e403480c0c0b004001486604050240d280111070140001c41d90307503400c89160501d80504890171100a4020b0040111b0a0f820544203803090b10040c60800f8000c0819500d400700b16000303000a10044542c0c0d881e100c03500c000c5a0003022020309048058503100c00d4148801c106a440c81c848401c201e040000000c0700464820700c9100308600240184100e0380744503001421300074154104c1800038159071040c000c102801e68003000b0307075180640c0d124449075151580d001712031074141c0caa0090b651003800d100001c82c0e4448481d03c42031203004d04004680c0d00d0f403110300030301c8803001030328240030f5140562507140300455003c2e4100c503408c003459a00002c2e9041d82e04140c880d41401010b03044070b46400410040040c10351600901c8290700340c0d440320f842c10314a4820083d11ba4882d140c5a58040d01c00030000621a012076407000140302411700940360340740aa01c000a444842040d0f084010074941f141c0441d0f1460000700b601e1140c0156a01c0ca180403240c040220800c0d002402c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43421578 1250 43420328 43420331
    0x2010c03090b040605130f03020604120c09050a020d0b0a0806010b0f0c0f0d0206010b042304020d0f0605010f020703050709020c030c030f04030b011211120a051902040606020f03030118 81
    0x1d030741c005030004000074100f03580d81795100c41e4248584405001785601c601e000040704101880540c2e598011902103401d484c1c0414003581d203500c2c0c101c441c0c2000d948940b914614010401114480e079800038905c0803104402000b9019403102048084416400354003019030010005003e0f407014a40142050210114150708080d90f802c90030f480d060101b550814213130480c2da24540c401d501003002c00d02406000d20a10300389811700c0300d4035031011107111014111284040101c03815840702d5044412030003035004240a0100ca0a40410291a580c03003901c1c0090200543c0269861000c0b540000b80c99214010700711651402d01580d000c1d400910320300b0355900040005d11030b0050100028241c41000318801515503140d810501203010050740151082d410310744503140011a1800e21170350802c0111602c0c101d188086480300c0c40c02c550414004e010b40f00b40c0082064041c821020100d03c1442110140319040e02c400c02248c60b0f082d04030600c11f01d5030040c801403020b4403550000310b2002106100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43422828 1250 43421578 43421597
    0xd0f03050601141b120307020a020d151802030d020a05070e0c161a01051e01082203030b031014070c03050f030109020c070e0106050405120c060705030a020d0e010c02010c03 76
    0x3010f03020341e00003054900d50800000841008000900c035400710542034840090651130540406912680100c2000384240c6070946c150081116014004454190321b80301041100e80c60900c82c000080480c0003a44a0300c615000401d004d031002606003400c3c1d034040042e2482c80d01e044039190032413070043e0100031240000d02400364050003074114000950301845c101610504108040b42ca403203010307040a030103080c07034000c0048040503d03400c41ca40c1040c01e10b840030031640c508004a139844051072080221100c605003a0041c180c0c10307008015800030460641d420080400e40320803ca03008075450444694807080000d00b014004d840b940d030381c01d0103420840d04e00103440c5002d000c2e40e80300f6082074030f60707503030204036041454810882d1802611071201b0020712344d41002c074041c0181c011403258602c50980d8107030002e2052000e000b00d1282035800b800340d41e21104540703082d9449400c6007003d40014480c0003248018203101e403800719103010701a155000c1c840d485800440e102d44464005800303002c1d13240c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43424078 1250 43422828 43422857
    0x608010203060d1509020301050c07110f09040b060d080f0904060e010e0403050a0c05060a0603050c010c320106060918020406090b09060c060903030a0e031206010f0c0c03030905120d0f03050601 85
    0x396846866019041590703040c89203004233031140c042030510302603110048841e045031140d540c0d1913040780e000840d180e041c0c1c0d186000110345040300316004044007004502d02a0202222003d41940e40040340e0134041d00703441c0d0420800d03000b13007482125030881c010004600420b010f000140a00246450000b00e6204207490303d600d440d05c25078035519025503514007001449414404851000e6003440c0c0119040c0d150b85400c0c1400765019100b01326401511428000078400c40c013640807072060301e402448083d607500b07c040c080003480d00c1132042e081ca2070031351a07058400c248200d40680d0074580740c04503020309105008000d9041141c001e45c1041c010071540c080c0e52000c1280c544100203003001160360b841e210101c075058881c8000c1542580e8003e101403d908040d10081981c40902880d0003840c00d06428401c40e5249040c2d000070300100e01c2443d003c018503a0205076030003030340d40588200390902d1400d24220703a00c924240c1d0040005100c941c913090494841e070045c90301b0550524040b04240c02e43c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43425328 1250 43424078 43424081
    0xc07030605011409010b120f090a02040e030d0b030718090204020706020d05060f03071409090a0b0c0903070e010503061b0c010f020306040c0c0203030703030e011506030c02010608010203060d1509020301 89
    0x20f0b08505512845890644894a40203003004c1c050550100c4d26810400318054524a050001d4034a00010801400141e404001001952041a0001c10901c01049a19120703500da500080e8454505401e0100454a50038001454001c644446243d40010201100102c00a00919108980c800d03002c0003d140420b01c1030001e44800c065202e8001000e0801004120b01c04491444040c00fa0f0072a040c10030040e102c180401c0c00c0230200b42d03002e980c00e035a614010f0b400c0207402c98008000b0034100051200c42c031411703c0a00141d070340941c2220302c000d0722401c101c1008002407152030340c0740c0c0c0481c002070b00032444405050440c221508009062400c00f12045003076030441010a00c0d003a0303010040050925060040c03038a481c10604140810f00081c0e0046900c0e40304070980a02031540740d001c0342d45c101000b5402510383d4072880014034062601c8003c000c01500180303030508015800c060002c15240c9061080b24010803004107840b9036000b0541c2c444103100d0700d070003150507040da540c1d40d8000584c50a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43426578 1250 43425328 43425331
    0x807080c030c1308060609010e06060403080304050a020d0c06080921070317011401080604052a210405010e07180c0215010f0312030b01020a0201051602030706021606030e0709020c07030605 83
    0x13040038185618103103081c003c1002c41688103240341d80510342031010725128082110b0589801102e8a84c0d20795490908a00d45948400c0003174200b20528079480501541c001260f050356034030750701c0391015210410840c0d034034a01c54090003048900c0e0100c04a0443c0c00c48020003080d4803a060031015000060a16280300009034460388410690202000240d80c0c0900c14684c0008129820011410181200c203e07081d4411000c1d0910b148605100030299240405d403080c045002c0c41c1403240800002c0d00389580002514100d45560070030500300d003038007800b0644800351016107007041c420006030a00003001d8161040900700354020440300748681159403103201d028048118071085414a9440c0641c426a80c0c041070004052138804035442c0345c0c0c0c0c02328010080395024a04a5100c107035106040c00030003500300c0005c1d410300c500c21000500c00d4002c41d9080010f60b00c40c035003410955481005034103690003424042580d030400d10301480480180d5010b0004000b81f01c080342c494070703260f541d81001c5500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43427828 1250 43426578 43426589
    0x911161a0702030c1006030515130b0405071503020702180c040803030a0917210a110a1205180601090e0102091507020427060b03010e030f0315010807080c030c13 71
    0xf0002d06003080f20002c1140d07482000c0300311420401e040c596243d4a4844803640084400615a200803c5243d64849243c403601904809040d070242014984a0782d104103500c80d4108942000c0000403003980a4402d46264507005800340b40104c0014600310400d98008014900440091201080d050020400b035171240d0b0310319400140007131050800f81da02503e01010702001203400c0104441c00c0c0101c81c84150400001d000710140c50300c2e20040d01024103a0311002c41c010900100381c8075003682e80720b0340b40342043c03150150402041e2039020708985840440301c0e0701c4820b98011030042080b0813030381c0e21919603418032000043c241201c540020f8101d000d003d25904000a000c1141d105624051207140d50100600c4e504082e071102015428091160182020345150340c5c0e84280041078400790009101c031403106041e20707525050500c001400303820035100301c0700c2d000c040000802d5075405094941c0c01880705403115210f82d51044800b07102030740b00804180031085e0510070000c2c40080d200100c4060b04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43429078 1250 43427828 43427833
    0x20c011802131b05030601021e06060112061a030a06081c020706050a09050d140303190e0c031c03060302100c1505160c060207021512010911161a0702 66
    0x41640100b0041a9464030600c40440c0b074141401070003039046580c9210368500741410781c1c036581d4200040c1d05041d070b11071100740c00000030000841403080204050b845080240c0740e9504060b00440c1ca0011188107010300008098150702262034050408050350340944400070105001c1c0e1104201c90501c845450800441000c2e07156904501d5014460100a0300c3d851405a06010300141e004040f24054490f403401151070400b103a080c08110b80b980070010300c0c0c44080701e599042c00746040c4071202d90030145001035481c1100d203408019000c50703004284030f0020000c00018014006089000b11059003440174556500d100100684503501072110300c0700c00781c40d8190312400030b00f0422250960300c03003084485840d00713081004100503801a00644071103846e00b551301143c64030380b43d0000c0c8a0b070f500295200310f00082052901c5c5071000104640840705035035101c0c59a0790304071802900c44d007429000a60100780890303040d6018004180d07441074014840554409000040300c08440b8090740d0300d20068 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43430328 1250 43429078 43429121
    0x2012092211040806070804020a05010f0c12110c03060c0703050c100c021005010503210a0e0301050c040305010b06030403051606141f12050709020a091e05010207060e0306060112020c01 81
    0x7400504c1041d6000e515410504c4607071800b07600245080d42107000b0141408134905d007503082c05200c0c210301c00900f903000022909001c0e84120140c107002c8902510141480b030202410540d06000c81c1107070280745040740340c40c20f02070305039410340d40b54005a041ca0001d00c2000c103070228240c01401241c2900044ea00039044080c2103224420a41d94160052030080d4040c0c200c0301113041c4200d42c3c45c002c203210310307920b2900d600d4004812640040c0240440781e0660a1100340580c0c6100320b001070040702d109200030000c1001103c2880f903180411100907000c50000c3c0008248aa240c40b00722103040d10403440040c1c43c001c00c40c0c6410f042070b42540c00e00ba8281941c00ca40e8031041c42125842e000d0560550f294181d54503a03030703036640d40300700c00d0064404503034000c1003600710180280c1c1000080e044007101c0126400300d180849501c18114400c140c0184036070b040c005480b90207200240030a1601801414540d0364140041d0788400f6140b41c1100d855500b0040d2038200c103800c0c4034004151854010101c000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43431578 1250 43430328 43430339
    0xc0c03041d0c030606090103151e080114070c0f06090f06050405060702030309190c030c0303050c0d0e0a0312090e1504060e0c120403050c0a03201209221104 69
    0x540050041403058010014000075070f80d9103081c0d0b11b641d40c2c03d03e000304030344c01c00080800c10100e00e540084004141170340c1c000da40d07800100c0300c2800c0d04d000710000c210004006c0d000780300e4100140e910802040d05400000081083c8403070100e013090003820f01081c2107000341c0c0d903e5060900c0c40002d54105581d1000c0c00100041400b1031074000880e03200a50039070030500c4100e0303240d00300c03071848401d894040f8042e0001c001010201030700031134100b42003038151696801c0140480d4082034418895026100160a4160240182c00e40101c8040e2410b20300600719502c580040b58040c0414003030013400c00000811541c2c02c00c200d442051300101482c203a814180030710064070010707040b40b03c107641361104200004034034105642e1180301c8034507000f9041e21203013400e03a064450124107081500440a011081c980c02c8214050700103901a030681400d150010b103141c580d035203c001c1802e80002000242e480307181034204001540a08100001d001800020007011a1441d0072180030701100450108003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43432828 1250 43431578 43431629
    0x70201020f070b0a0c020d0b0106020115060306150804080c0f030d060603061d040c1203030510050105032404111309060609030506070c0f060c08010806010902040317030c0c0304 78
    0x1000074220041160300c2c100034001c2441e0040c66042001c010382601c1700001c3d550340d41c0b18504425081030714000c0340d5850f400c00902030700f1200d210103480f038000b020000d4928070034401c0b44110760301e100901b440e0350004502141c08000c0600280d500c46000c0c007140018000038003481d102c00c00080d00075583c6942803988030095070704a40c048004c0c5441e100302009120400003a2440b0030031208501030041c0e0303c03440d000b103c0c80c20542150503103100c0070500c03008054240d0301041c0201300d10301c882950b0555070070045030688000c4841c0c23280c12200c2210300c002030005207907207541000f0081010854080c02e42100d01d481e04042c00e038400b0320312002003c02098003d4440c04001d4152480c0098285086407109550340700064101410000d00300b0b4200306100fa1104242003050340300f00188050300281350b0040107200f082c003e00c602405600700014005c10303d403088600316a84003180c04070300c141c000c89040c419040205801603d920410a09948040c01d1000f4006404641d8200040f000719010b502c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43434078 1250 43432828 43432843
    0x50105070908100b01170a02031b0702010e01110c0d050106031a0402010c0816020411031e07020a02090c1b0d0f021209040209041409010c0318020f060f1c0207020102 73
    0x1400e0200071003061009410100f00c035040341c3c04040000c607580181c140101c4104402c0829201d140b010034090000c40c00c030030380086010301541d42d00c0042c3c1084103401800d03280b2800c05c0081c00300e0404005046554007840c14040609558825070b0440701e000800f1619690342c100b01101c10b65540d04040c400c100d4002d00c41340c00c49004440743c11007440d241e4000382454580001c0602810360106102041c43d00c2c02d00c0c244089503001c6c0041c0302100541e05c6450340c6400a40c1ca44450142000203803022145002e80759125a00c2540101042c68268091041826015011081001003005050059044001102d07440c941810041c19440c2903607500904922041c280e03c0115000350802404141380d0f4000d0b5280410100c42c01a071300c25181c00000d004203516009040c19140440801c0010380066100108030041034600740032040041c0040d81c5010b5103424000e60290701003900c0407882c1400c2c0b001d05031203091680124a072841241d1042501c0368001c0c0e101c118030340c00241c00300444d681442107a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43435328 1250 43434078 43434091
    0x504062001051501031b0203030f04080c030d02070b060d0b0114060405040c02030a0f05030108030a030e0f0d020106080c0405130605060d08041e0506130b030c07080409050105040501170703031d03010c0c050105 92
    0xb0306d180b2250800a440340b00140040c01e90a09600209003807010070000c03101100c3c0600d040745e644203001690a0080c1d0480c1d80295419004c0b64005078030703030501402c0000381c0c0d40c3c0800d070640039030b0802c9402c050444809800359000f101c02d00011500780c03210302ca0882902180e8004540b6907407065001000c1d05010300c660000c2000c00e1004202000001007500d540826605020500c40c1000003c00e18041c00702040c040b8038800c450740440d942d0380650040e0281d5900a060b121600522020301007541c00a859021014400300915030111b406540455000036004200d0103c81c082a01c50180c030783c0003500b0101c406071000101110a036043d2840c04001c002c04d440700c50918440c804608016205840b40d40703078040d80000043d482d02c1c5804201c0380f03034940c032034a0719494507100d691050040c0024002c0388e004500d02400440da01903000e00220640080c01c0040100500b150b401703e40390b00d60910390301c082184081144109a41c21b0244080c4001140d995410740340b5181001303401e40c0e1001c0c020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43436578 1250 43435328 43435361
    0x911010c050d121b080103030905030705010203042306030406060906170a0303050613020c01050108060121110d06050903070501050c0c073f05010b04020a050406200105150103 77
    0x310002500104800407031820504101c2c1410521245180142c04810340b260202c2c041540400b07041500121494140c901a0792208400d40d29001070540d80c80f46401118003680c0140800c0040b0b14002c0d41701c5100b039501801c05080380103201c0c08128180c000f554101e510a0300c604041c07000c0c0b1468424400205041204000a07400f0003c031951641885c0d00c2c05000c141e15080082e0035925070000080c89440e110400b10343d125952610740f8001d000070302484c4903d008100c0000364060403121003100c40603e92020008089403a80ea02c80025103074006c0d02e030040c24002c52900841c050b8031966200d0000c04c0007a43e90342600340380c8213003124001407000c000140140a13443c2d8940d40060400705603590a40240d540420540d10041f06442c81803000a203914424001010034014076000203100744500d009000c3c1e4401c0500b04004d0f0700801403241c0005100b4042045600d01c504c419122041c480c6181070104005da108960a58200700c0d51000d1845003044c442d4459641351052001c0703104641103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43437828 1250 43436578 43436597
    0xa1517060904020409020102010b091006030605030a0201140a0e0d030f021e0d05090402070c08070612060303050a08040809040c0509130216020f0a080601081f0507080604110904060306091101 84
    0x181002a010300060301507662400ca02085900035400b003105400b00a0492f030481c5085100240002179900600c40041d080440000d25400d0014141000b40d5050b142c00c2e450303c1e6490003240c1c03107030010000c0c2d008000c00100300387c8a075111031b10044106402a580e0f075040914140d40680340225030895040714400181a005842401062550000b1014035246942e170b141800014064020307005d014000c0d03d000800090110400a410f100701c41c525110105100c1100d560601140e60398030026001c00c4041007094030980c0b05940c50741d44544620381c22030030b0038080400720703003100e404500101c0420300001d90126685080034078001c220301c00380b5065190a03000900a0508000c52800038001c041c8100c0c180d040b0390b200d80040026041060403507090f0340e91100c0c160390325031115080c04085030401140d08104507460103040cec882c100035110500325888090511004055500c0d11540340c400c280040c4a16564071b000d01070007540584030124290000c0d08001d80107100d04100281032054650 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43439078 1250 43437828 43437841
    0x71b08100b060a0e01050a020102070c0b040f0501020d0e0409020d05161e03032106030b07020a031e080f0402040e030d0f0e01020705060c09030703060f0905070501020718020c07050a1517 82
    0x3000d510b80130f40a20b001501d4000903070003030780640609440142a40d40e1440045400000070010380b0848040d0400b01c4d290720b5542005a0b2a15034001c00304c000030f4000d00d0075024a052a8004910503072000d010300000701d049840c0c40341024462808201c545405a134100030213045d250b84a0000550001740a000d1840c568010300304884081c1d4844441c2044498550000721a5100e038008680252010072140f400300d8000307446aa1070034040b00491079441e00c566201815500740c0340c19031041e40b1000690b1b00e47c0200b429003081d0040003281d00940710300049031503010500c0a801030104540021810300030a8850609440d90081028802da2050040c4004288000b602c99000007158000326a07031528480400e040c2400d9030006005a8248005800340d64455880503172070710b0140d41610105e0351102c004a0719140c440c0b095260703a00803400384100041c4198001c052410f50001103484c5565100d01141400850303911075403542c0300520b00305c59041d4001c0a009003943c00601a11020316154 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43440328 1250 43439078 43439087
    0x90a030f0219031b0c0f030c060302040f0e09160602010c021c080f1005180103060b0d0507060e010203040302040903081602010c051c091a090c0a05060f071b08100b060a 74
    0x1400b50411800d0811030a1130803010042c8141c1c59001141750400700e84504e083d82a04100f480103c0b128402070200182140c820701c29102a0ba01101c1c9402c09513140081240b94035501a000d070210380282110a440034414504d58001843c1300c0c0c0000c03640820b5080040d05050320440c0c454003100c03401030380b840c0d080d0388105080e40c1b012100c41c401c801610740110310f00c10000182c221300d030011840c1d8840d200c400300f0810708034126441410144028000385060221082501000400300e6000082c18030003140541041c50403203c061048070305240d600c0e00003400341e610800f4203034049080303032003809070040101080345000355690000780040781b032481c00107000d03124004882a002d404203088581c9034055800242c08181c000d02080000a50350501040f101c2d01950f0501180c801c140e40c0781101d09100140b102110001012107090004020442825500c1030004441c40a1840e28108105c110240d00d50b01070145000207013075030070003145103804941e1318000b00fa10600c07081c400110b030340394031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43441578 1250 43440328 43440373
    0xd09060323040813060e04060b090a03060b01050f0403060b040e0f0d08040201120c020f010c0f0801090f02070503030406020304020a050904020f1e03010603030e130c05120915090a030f02 82
    0x2206042001070780c0d03d0500000c03a01a00501c042c485004140000d44554889411442d103c0c0440d030812125036a940c1182143c404d4000d0070340c10074607d91040002c100d0359840800c208506060a5240641051070007115500641040728400c1d81c41a04584508040c800d0800c0d0011401c010b054880c00c1c940500c1d0b46030101d007000c1e020400660001000c40e4842e02030b17120040e02c1001c05001800c0c41c0030000e07403900d42014010405618103007048921611454a1000089054403034110720703400d04120300b01421054003041c2d03806400300840400107000700020741c455805200016240c1c101481008140703950340d80803d100700f04202c01c0c003016070785e41e80d21032030075040c1262407041d5a00170700c40d0b02d01c040d5054011a5815480d0410000605400c0100c3c4d2010070000c58240301144030b107040000807030340c0484210000410605c030306500c10780076140007908420003100300d40b00d84220220348401c0d601c04a17845041600104455810180c00040111540419001500c80d8204076828500321500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43442828 1250 43441578 43441631
    0x40c060e0a0306090201030b1008060f0402030c04050405090a12020d090905041e02010903021e0a0f0807031506030204020d06030b0a1413021f020303010305070806010305030403030507060b090103050d090603 91
    0x313a0f03d141c0d20440e8060b0f80002428140038011402040407090058204a02115254000c0151004ca0b80192801c1c4c800c0701d11500c44945028101410302060000400300108928990310441c0c000b0f00200c0c000300c200c11200c40e0301d035009001c5101002d00040041020354001e21105040800303200000f00c1c8041381d2403080e03981107624001c04070305000484810310180d01c0030f500107481103080f454065140c0314409000038144c1d4500c16040c1e603104c0b10100841d0074802c0040607001484244006074504c2e030141d00240200c00b01090490b2a81c0000e000c90744141880003045590b048100f04018540000c10b03400041420100300005142c1448540c15070010101c0d03014843c140005030840d070f9440b022103207040c4c926540180c0d8000c000c5c0041e66030740c400c2c00207560ba4071500300c00162500e80010601d060301e901c81c01542c14030346980c0d030a0b43c0300c1e017141c0e100300c48241e120701030b40c1040d0319114a5240250300500c02041c420303014a1004e440000c00341c000d601054100040d0050400d40c5102c07d451801 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43444078 1250 43442828 43442831
    0x140601030c05071202030309010c080105180603030f03071206060201090506071103040f080a0c0f03030e0105030c0d020a030902040b0f0f0d0201090812030907060905090411040b0612040c060e0a0306 87
    0xc203520040715503128043c0c0007806494507040784010183d00202951003010360000801c10b40f864a6410ba448942c00d204469004007074000880e06900c9240b502d540010300901105d040000442110f8599082103401c50b000070317414140c441c004000c50141000508542c0020884000c458498544030240108036030140031803010346800c0791808100301e03001401a403c0e951104c60301ca030311140e11000c481074166034528a0b1030f00802c2208c089488107040740d50580342d41544070f002d5001551240c000500d11502000c0602c000110b0a8450009100e03000751550001884000f1b841040b00b16000106294001c41d1188200b503095140c140f00944500030485281d40000620310040b2070550482d0029085400760031032503001d201303080f009513000701c505030161000c103503c0b001c04480251452141907840910f11002c0f42c003060460f0748140c007110010308041150152040403411079071214010800d140d16400400c000d011100e1801c00250010b80307481e15900d07881d1000103014603207030b010190000c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43445328 1250 43444078 43444091
    0xa060e070807140708090f030706021b0a050a08060709140a0605070203160e0f0106030902130b0312040f08010b030615090c070606031211060601080a0e0f0703060507020d0314060103 80
    0x45008001c01200520390104040e5143d4080c903082c00540c000458403400b84032040f042c0c91f514600804c0e8007003a0748540d4010003005d04915200b42c00c1c030000e01d14246c0c0000b4142008201ba4854401d4540a020440c006089071f007030080001f0030056050b070095401c3e0213a075003141655946c0d10754620031610280f410b2522a2840d000090400040001c44080d92050140c0021403500e10300c0d442d4461a400c180201150303a0301da4060382074401c8680c0c025070040c80710101c865210f13007583c003285400b003000d000c940301e004140032040c1145d030080d0070903241c1e207040380d4040003190700c02d01584c1c4104005502901d2107042581107400d040d00b42178049841400c0c5d2000180801c00e0301801c5d60380f4640c21000a11400d543c0741028510030742e100440b000001e080c50b0302c0d41900000090514010501070391503a41594803090440e008001c0c4a0421945015208409101004c20050840070718001c040c0018903082c8100085c0c6004032211176001814101810200701c040c203054100d92100c000e0078007084a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43446578 1250 43445328 43445341
    0x207060e031c020d020d0806060904110d0908090f0a080705060c030d06031101030c02010c0c06020a0504080307060b040e1203070e060c01020a080f060f060403060c0c0b09150a060e0708 81
    0x10b02d0240c0840c16030507403441c2040c000c010b900092808a1031265001da1703200760300a03242200c042008660340e13500180300b0000744441e03042562140c07580400003000306042858403041a0191003c60600ba0761800000c50340444900d05400c1942d40742d01c0032920403160038500314100c3c0d1600707041d200e035034410480401d2942c40c10b0780500c12601c42c2c0b25440002c20140b6180c0c640304520040500e00f050000c0c0c500b64280b400340740140306000340b544040e180d20083c8040c5544410182d44413a506c03008001081c4000101c0407400c20192115601c104401f181e28a404030500c001c80b80c82d00f074020580e40c40408040900c0d100b19080300d8001105107800340e0a09203030b0011854600c00c00241401d5580300003461000c20340c0c8004a00d008680700e94034000c09031240e00410401d50381c03041a0990000c41040304000150155010805441d15030400702d1b00d00e00035444c0d80020010860706c0e88200c5e0010a544c450b038800d003840b039a9104580003403c00500303041030505010b00c600100084140000007010440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43447828 1250 43446578 43446583
    0x5070302091c1a07050316050405150702030c010201020708071b030804030b1504021306030510030803090609060615040302010f0c050f0304180c021f090506040b010501020d030902010207060e03 85
    0x41c0c404050001c507160400c2098500c46416190030a543e9984403080740b001c0c00895640f0309014035000e603601c86c215190503880202c00b100d0030b00d400080c00810000080c1a80750f45a07690911140b065490341c581040780107060401c4802051181164410000c0d0000240076100ba00c4810b5003100c8199084030789800300f1403d0342c3c001e4002610f00c00c0b0200d000001c00030f0303403607840d4801e0300c00d00e1100c45201280d81c2407009078003030002140600c600d0b000061026512035409681c1c80801d80304084800c40d501d485150b034507442541c20070440e0300004104080c0400c00c000300c80e0080c00580c1c914400290100d0080c40d58090740c0070003070402081890500045109000c0c0d141610740100941d0040b00d4200b140607503e50003842200c800c1d2801c0303a0f00306442011845110042c101c150068500c4041c400d4070741c424111000102c0315041c5d550300218001c070b07104000051040d842015000c18139418040003a24003604074180000700743c00c00d1030040044c1d9010545000b201c1d0360f81040100f581420001a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43449078 1250 43447828 43447837
    0x212070b0f130b160f02010614060c1005090a02030f060705030411030c10020106060e01020613140f0102070305130b070c06120b090a0b0f010903050c010c0204020712020a1407030b040605070302 85
    0x401c4003031a04144107070010040c0c2051013003004c0c0d40305d82040d030b203840c90282d09803000c0b8403401905261032002c079180c0c1c0c00c20000604590061784182d80b03c00e03040506420403120241c03109065039000044800c11410100442102c45c0300e00402800540b5002500900d82c0c440108020441041030702410001e4408104202201c0f00003005501440c1150600900030603441c41500c0c0050301180c0b10b00358550001c50300030b004002044901030910001d40300c4d04000c640016004100c2d124a0003520b400d03480a1002d4050780384282c0c2c41e01d80e50b11130b4000d1640e0800c52500b001c2403810003001807400140c410b030041d000302d50003801c000480c07107848003008001b803484030001ea0300035004100b0440b050784c407a40501c00038481210407541031501c40004581c5400a030200034130300d52010303403118925801100b1040200d40300510140c98490b040e030360640718541e29001700f00981d011024940800040d8036084001c0d840c5080142005413031901c0b680c01011000e0310141c0320682d500d020036003c603c04d40445 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43450328 1250 43449078 43449083
    0x819110408010c080603011803020a08070302070f0621020306060d0c050409150305100e0304170304120b0a0c020c0d061503060203040b01060f050909041101020f19030212070b0f13 79
    0x3c2020803824200640348101c1150818030039460080d9147c2c04429501e0140d41040d055401011140749c107994501243c0d00441d801d60039889400d60005030304030010401e070b024044035611003201c40380b0112021074a000c44484059101d0042c020012942c0f540f900346c0300510000b0b44040380354440c011040da014400c43e00300252040c1480302c48200c0c3c0f1301d20f541c250100ca100724101d0703201141184a20080b5180d0300726207066504104000c0006145000180260320310076810f0703900d029500c070024440d15019120403180160603000b080184403903442103460b0880f450024103010908800010f40e0a46081c100820b155581c501d01c0c40d1812100140320003550303114900b155a800d040c2030103090000244503134400620001243c488051050050b1400d9040203021170040c0c0d19565240b5000088440ca12411440745810382d01207850108501080e1414071520080e41c90740c2402c0007400c0101c2c0300400c0c26040c1d0100104400100d050241035402080b80e50201320300d4803845400c41d070078560391402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43451578 1250 43450328 43450331
    0x71401020a030e070f1a0d0f020d050103020424060f02030408070308032e0509150901090506100513050918060c0405090a090b0f070201060905040b06040c081911040801 74
    0x241c0c003080e42c16901c03041c1c0264540003101e0704181c4d100d114000c401840e01903200305690500350743c0382030190a0054003402d1071817140803d50b10b0040140404a800644241c07a180340c44400400950515105030300707034910010b1103514110420341c20700f100d4002a20a900401c02c0c142c2e03118900c5032003030056030045d10000c3c06880c0c03841c1d60303410f290106070020ba58146242a00c00141e6144121b0040e10084884580004005d41460301c1c04000b0303c2c031402000c003d0410640001c1d200e082d80d03802403007806010300c030078001503504144090144542d0070041707400c14400c0070440e94604441110a510440b1421168200256120041b010710714001d50b44800d1580b0030001070207142c2414002500a486060710030100507500da06074203060b1140003001604060040001c500f409141802e070340c0c8c0c0106240000316480f0782d501462011904101c406503501c03d089014020285402d01038094a1007180c5455003280c108035104c1220005005890301c070103940d8150004030744240500340c5008003000d600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43452828 1250 43451578 43451587
    0x20324030f0312070f0503150d060f020c010c080a020f07060509031603030204090c0912030305180d080910150b03040501060b030109020a021608100203040507051c0515040f0807140102 81
    0x5002c440f0809640b0a00803c2c44540d426070b01d20302c644190782c03140c9605020003c14990407000d0022646c43c070102a0340b190b80b04c0c111603111501d02e00051141c3c0b0400000000e00721209807001380f000101400790140b5500412141d00004c000a0030341d185181c1008002912303891b40500c29286200382c1d650210949040e0240c3c409042d05035003e0412900098024080d0f2061480200c0388800113000d5509205084003042000c61700ca9400b01d40d0000380683d141282c0f80c400f209043c84d149102d426840000c00007000c00c00f048105204070b040354511800705109a458030100140f481d0028028400d4851022001070107004094002000504014241036501d503110303801200030b50700400161002d44942100b1000d00d80007a0014022140c410002d010406980c0c1301420103544064010303140751080240102d01541c0c2d00b0715401444102070b44030117035030140303141c61803d011034048d0700076060000a042001040300520019030107a032181031603550300c1440c0740c070040030414484200b00f10341c070214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43454078 1250 43452828 43452847
    0x30602130503010c120606050a08010b0c160f08011107050c1e040612030e030a05060a0f02090907030207140a020102030a080a090507030c05040614060a0e12121903020324030f03 78
    0x440348805d0000351311050141c140c440006988a1180e0364141c40080d10640c010404260b40c41c000d042d00b44424000c3d5287c03407440050304002c2d02c2c01604420862070381244100200c01003441080141d150751544a401d00f4040e80f04c9584483c404040b09000c1c0e81e1307180701d0b600807030000184540b450a0080c0104401c9480300c03248200b07001007840071004500070000024803071034002490712180e81c1c010000c2c40c50740c0c2c421002e00e01400444c04500a41038090001d18916a80c41051512070a01c5a038016202d0405042222003403106003d05403081d00303d00340e04009070340e01000312900700e074203404e0900140e12030600001c0100b003c40c42c064214060242d01108001d10811000200d0b207040710107205280c0c4995080c000c5142e101120355108a0420440102074040d036141c0d074090130010035800b0f0030400d4015407420b095444140030b001c00c00000320f21050710390640801d200b2100305e103821400c61601100b5209039202030b21450100d036107921640c83d072913903003041071a00e04a641000d0b652182a0b12 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43455328 1250 43454078 43454087
    0x201210e0d17061f020307020904050d0206010f0e01090507110f1b01020f15061f050405040c080423010f09030c0606080a0c030b0c130b0909010e0709030602130503010c 74
    0x40d01d40600140e40415051100d01c03114103420302400009000c00744010a240854501e002e86480c21819804207002d850050780c0c803a80c0c0c80d40300e00e000f0703400340810360b8099074028181341050708440c40300e1011070030a0025032401d12226040d50051440007405444078401564100c410340c8500030310b4810b00c01c451705960f80115003401e414000350007084400c0000c03801aa03c8046ca003101140c203600502811111036840220305402003c00f400d8041c0c01e078031a0300c4c80c0b10700c02038503004800810400902000705040c50b104a2580080914150ba464101941e48440718a04402d451002280b4449040541352080d0700040b014101040d082086416528018250480e400019540b0503d4104002541700300494500040d960107081038055600310f9a40c0e6008030f00142000c04d06401c144a00d6800790301201480010705002000341c0d41740c6200c3c0c41005000e143c140c00400410190340284841190800d0a03641925400035016131140002c00c0301c10000f00b91603000641c50740c2060b10329070806400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43456578 1250 43455328 43455343
    0xa030510050601031a041a030303010e01031202071503091103030310091406090601080a020c010507090e0702010b01020d0f0201021210030203060928030c0c0e01080f0111070201210e 80
    0x440d0014000d980c0c030741c80190704541141107060510080303c1c400c84070341d00d09580304004690b659100d03507615101c1400403e142d074109803c100004154500188140080e80b5000140358001d48010b210a508110407080f8009c1024000010b1584411f4250108064000c00800120b0f01408a90300e915118210840c2c2d103400d44140380d0314900e4091101100505500460300c80d41d406072592043d41c0300d4400444015100030b0030488056401c0c001c40a2416003030240500411103503403003906041c1130006c00d541381c042c0600818150780c90031081d000e15903008640c8035144845c908001414101c20b540603800781c13180350b48081403080000c0412079205100010701c02582e00031f40850b0f0107a42d0b0000c0265580d8155441620000d05003164a03000110b0390000298151007458100c030505d40b00d43e40d1460400164010505c0315040c000140080c0800f00410040010b450000b8030418601c8100e4080d0fa01c04c43d44c0180c100814001401c080804202121071506400401040003170200c109240c2c48115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43457828 1250 43456578 43456603
    0x403080601120603020603010b0906120a0516030b0a0509071205010e01080f07060c02090a06050306040b06100903022404120609060b06090906130b040e03040305070e0106020607110304050a0305 85
    0x107503102c1c01510518500c500f206880e4050440707482c603400d00d1a1520b103600710058540c0d005100300501410b200c03803500020700840711038901140d1801c2c43d4180e0324441c6030401c02c8404051411080e610310796901401d6404441c025a4000c0d8903403100e0804640c0c1040605220518608103000095110070340b0307070098102d58010061310680309005648a8440c1580d100c0c4600243c2030100560243c40c0c14000c02ea0000000200003030b5560b0388102090810000b143c060324440403400400442d404d003136a02250950040c03030011009411903001500380740c104000c000d20003490814503000b1207408821540505140031454592240c0303480c001000d0010840e08130f6040b8200b0328004402e05110007641e40f00180280b038200195035850a111050070014900c584458903050f402205403580e2140050b031a101c5009150340da42503041103445c2610582c090341021801e140100101780d800310704160000910b01d440d0f801131000380300684c83c5000c2c5030485980011100d0000040020020300b40c0740f001e9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43459078 1250 43457828 43457837
    0x70f0507050909030d050a1b02100b0603010602070b0c0c040e0d02070902030f010302010c0c0911040e0105100e09430207060f23040308030f09031303031b06050403080601 75
    0x26110010b001c0d10301010358400303449603c1400780750600d02c2c9507040b6603071001c050100011005081115003468400502294015030070688007450038440d45d001e0003130550740540d995441c5526080b402981c4981d40e10a01c0c155035400301e022a0300030303010301030000481c2e00200103008039085640d5281e05d80303000c0706490025100f503550014008803c1d0081d2449080061600e0440360300e940c00655540800711801c4a0481d440030000c40c01c0056485185003281b05c6c0400c41e6229401c15451220101068100034850340d82d02c401070304a55440001c50740c2016040e2190302641e01c50b0f0004d0721020300c00d51601900d10201c0091107616105040840c550400c85440b40d0360f0700480108107036100d4507180925000603101444444049004010101c2031403440b00c0c200f203c10699400701c405030341041e0000c440d150f000000384540740240034ac1c1c0582200b49100950f00e030041c0f4807016040c03040c01c1d10004003480091690403610800d14100b001c1100d81081d0b05000502d8545001025000d0440c1d809000c103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43460328 1250 43459078 43459093
    0x60105042018090702150403120e07081c0302070b010504110c010507020a0b071e141b0f06010503060c0414010c0f05071a0c032505030a090e06090402060a030c030e03070f05 76
    0x135440000d00000140c109003020340316456a0700d0171510900e07070f40301e5090016280d000b0485100c0b03003040800020700700c0001a10106500e0304101c0062030a4000c110201401402030360302117030006c0e024504440003100d000a002000c9414044980114130851a0700e501e002c00b04581c8a401145207840c4520441008c9145e40d1703000e07016140e02e075001c0850b0036040c04074480e80f03d0315802206450058403144440508104011180c03c203154800c11004d14190050703038407400c45004c20001c66000d40000c5020309064030300070550900c240910703c83c07070703880c00c96414800c0e8407a401240f0345100325800008141700142642001541c4200c2031155824059081558038200d508070801c0d10151201c25014600c0c1c440b1003150383d100106005000e01114a01003d0040010010002001800c640f0f854007104145000440c0880c45401444a40903503d100100310041c0c0d911411140031309424200040c83c00c400071b008400032324000110f14403e220000c0c022007440980700c1518100b500c61011281c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 43461578 1250 43460328 43460341
    0x2090610020604120302040f0f030c06080c0d02090d020402041d0a0606020c1201060f27090201090e070e060c010905120a05032202060a0906020c010c020306010504201809 75
    0x201018020450041e004040440d0005044071303050100d107003162402508050b00d0366040d0592005503071011941c40012241001000040d22824004000c281410b10300b42c5011003846ca45403184d1a210404c00c2d0b80007a084030035507182c5010101c010b401800854a60b9211001c051002041590b9282c4100b03a840004c1d0b40c0f06601c0c02400c0607182e295020b800c5490720755091100110780300d4401e40142d52210000b2880c140b070031104000030201440d00c26031002c407000c0b0b64456408005007200e1407904011480b80540d1b0450341200803201258040030b400c0e51103040803120711752840c85103948031400064403082e000054000030240740c020703c241d4a9035110803000d80003034416080808085801400054040302084110300d010700701c0680e94080802403a0b00040c0c5941c05159290003040c0880d206001c0c80f9810000348d80480001c0c2800d02007548107400181da81d4005205540c841c80e2540004c1100e09541744800030f40c04590458651509070300c0465190040ca100c04607070181d42014001001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 43462828 1250 43461578 43461589
    0x80c15010503010b030d0905190509070503190507020d050a0201020c0a03091703031905061c0308010608131703070207050a0b040e220605060f030d0c0b0c0403032007120b0103020906 80
    0x16001c5507500c2e010300c4942303400c2c2408100d1812075018601b810091500080d81d0f1a014000b9110703010658456030740b0702d0580d40c180c00c01c21202188940c41403a100c100520f06800244034010707000c450412986502020800302e0192207404440101401250300003010550032031341001c1901d84000007107400b200140405907590000b01e0381b1148200740344175513000384031840c3d1145800c442c0141a04548800c07409004da042562900c041300051003c00c010040d4561103004140c01c01c1046401c409511156118401c0100c5018002c969441c400804940268020002c90f0020503026001924156464032550181c0d009441440c11100d21000020512a00d100028000d886026095085580d2035100d40000b800d00500f400d400610740da4203403d450b5400c102001100d8071a03500c440010080e03250404040101410442404500340428400030341c10482900c0601154452220010136000c40e0034030303190060b0f03c1402032180914640e428001851600c5040e40c0c000e80b07041c055501e40078140719 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 43464078 1250 43462828 43462843
    0x2091011011a130903180f15080f0609060102160308040e010801020309030f0702010e0402040e150102030f04140607080c100509071203030c0908070b0a08060901050913080c15010503010b03 83
    0x990001d00d9603c0008010080e6121800f424080d02e8002d0306200c2940485041040302d400410a048028400b00035222401c603801040031401d146c2452181444070003c811120098103840c1b06003040e1000444592003085110b1941c51801020b0451036628100f880c59a070150094444080c40140082440041402103a000303120b254000c5140034024612034446810000c2d08904100c2034100c20f0700f1541c0c4034000b81010b00044000c00e140ca00706051311080d0303a00c503520240d0554000380106003c85a001040da4102c440d990022080343c1d8078007001070118400c10344020891000410b4100c034502d80000c0c0130000080703042082005803034801105569284a214000c4400e00e02384810000034401e030031021481e185030610403401601d80d9916400e04800e500300c3e04620001090418501d0380c0b10000580184080c0c0d01c00449504000106034040d4004041170790b86d040880c070718420804004201c68141b440360065800002c1c80d81c004d0a5594000c0c40f034103100790300f001001101c900d40440c2d5003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 43465328 1250 43464078 43464131
    0x1501080303040201080c040e1501030f060501050f1b2b0e0d1403210907050105040e01030204020708070c030302010c090b0a02070608070c0203010905100608120d050a0209101101 78
    0x55040da942c075401101c09860040c91901d640d08240b00014420201d00c9215005040842846c0010947c103000101111154207580c1c40c142e0400e2020015a6000800c13a010801a8a41656200d19a129a4500030a01084807660340b081d445040359500154149514582d14110b21070b001d6403030740d24100d82d01c8150801203940806050040d00004000042e07182d211450b00d03080e0b90600c400380306103e003100400035544c04040c0000b010400c0200080c0580b40c0644000d00700b1904160401222305412501408001d000d0365000070302d5004d0120f4a0305640c6030075445120001e042d5240d1400074064220039640324081004180701081c403400000035266000203a42c020040d40345005421210207002400210502040c1e00110300075803030a0040c084c149006000401c000d40b246a00303e0f08a96003075210800070342207003c0034102c846820040b00c1a1030120034011a05440700c48400380248542c11241d940314695105038414070381c204581c0740380d0b294144000c0195441d4041c0d108680c41e41f00b00721 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 43466578 1250 43465328 43465333
    0x120903010b06030f07030c0c0f03021c03110702060304030216141e0f01030b130f02090909070503061303120608011d0c010e280807090e010c05041221030c02150108 72
    0x903042c5e51090340719000c5600310f807418916040842d100d600091074400f1051700103820100d9170148079407140c00d8641c041c0740e06203030070420b840800441c00254013a841c8000d00c25080080031400b0f1501c00c0142c1d181e030060300740c50f10303184656070301801c010314202c80c00042c0912079100c041c0e4801e00c5035130010010781501814110141d40705200440041c410165050360148010000e41c803001c010344682c0b9406444c03910010b039204a2042001065003005042407151344c4040414481c6840214a03a0380280b02413a0556002c48a8502650313040c0e0f2001602014a00d844170016440b881500156a241041542040a00301024003d612040075402c5280401c48003008100e003400c148060601035074880c40c00c562803071b000040300d1403903000e258010042a03106030700c103002441c15031148054030740b101d034001c011046c203d20300601540214803410084403203203503110317041c031156603034550341d04440d070b004204400000003002c5c009090840c0050018414042070b081d00d11201c198041c140e9009400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 43467828 1250 43466578 43466581
    0x5010303120203060d060e010b040b09280204080a20010801050f061b0304090b011e0806060d02091306060306080303010506040302190305011509140f0103060c030608120903010b06030f 81
    0x2510002c1c0d4000741a143c0c101610f100c8403004030700c4620401308490343c50b10010801d007854008004c01c0c4c5a00e6503039688a680240705008840b4103010511113a981504515015002d480c200e150090044d90b00000d03090196074290810885101140e11380780303a04040c9011005814001114840d900340150ba0b00081c804956100c2e514145003c0c051040c40309241410b004800340010f4110b4001e07a0024040c00c0c1c803078503012003541e0048a89104207014085240c031840541c440200307984d101500203402000c0001d042c1c0c100400540445600d44d802a142301c04144e204443c02c8003d103410310850f0700003490f069001c210301d02c000c82103070b04031880240224140b50458003000002803001400c040b21444100c03001000440038000e041e07040d403080c2d20f9140a2490130100106a9865002540e10b1075040c07010000710708941500c0c079041d640c0040001400c0e445050095009040701c1d00070341030f24441d181c50444101414401808212030560003404008066001e102d014001030f103c42280158550 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 43469078 1250 43467828 43467857
    0x402150d0906060605071716060f05040303050606030f0105090402150711030712030203030615070c080307110d05060f09010e030c07051005070302120d0219050c011d250803041d070305010303 84
    0x2800340c10728408d00c2490010044035961050112243c09440398611750311348080005050700361195503807049050b60101d2840c54502c110507400c18050003028402e8620101040c00e54482003201d03e040c1c031442c0219942d81d15181000d03078843d03000385000c0384640700c0c1690104221004140191487e80e15800650071b42c0c40d000100103203504403040383c84e24041c05020306c102080070181c44000a240c2030010b5542c50407142802540303070b018450f00c83d024180020140e0000760000440d01c2c0d1120f036101c1091140d0b02d503850000d0140140d840c803290702d03200105419040c00d0f030102c3c0e9142100d50442e40e207244034907416420768250080a0001e00035070031840821494420400040000070403c2d4401840d04c00c02c0b0307510301031000c1d413144042c00040c40440d443c00b4a550134032648043c08045410007a0035000300710503a60f05c940c542845100010040700854a11903d040c3d00700282ca4440160380c0c55540781d01480303042d54011081405146030180c080b56036103000744102816070f60180e81d251007040658 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 43470328 1250 43469078 43469123
    0xf0702030f0d0506040912090e060a0f03030806030f030307030b0307080d020715090806010902070209063f01050103030215150f060a0c0f1b0812030601080402150d090606060507 78
    0x700085d802139120140000059006000c812071120705072110b1104900b0700c552030300d461000a11560107501001d80a00c1540800c05040045175458505200643d44d00c1010a00301860003007031300d5461001009101070fa54250b080400030341c0090782141c581c1d43d03486104a40c1c0d40d4040f0401809a000210180403146103412180c0102c056170916424059882c0595494031400342d10040800f54003150030300444c903108121075000342c022640042d00c1070307a210383c0c00d030002c00c08000745041c0c56280c500c0c0b8441140c0400610305900710880200305942c1e6a0401a440d21410311031041e03641ca0720b07400a034080f031100140c0300d101203000d483c3e20303458001d01013030250550203200b080b0f042c01aa040250001060f80c03c403603c5a5126010030f02c6901c00f1301e05003848101d10f90f001800945c01c400350000c14040200700b030b02c0d0300020074a41000c507611140040303481d2401703080706040c400038001010203060481d034110903c0c16100e100200112561131200300c40500440c200284921560940701c504600b14 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 43471578 1250 43470328 43470331
    0x20f04150c080403150609021e0901030603080c06090d02060709060c030c050115030501060f030203060f1b0d0203060f01030605030d0c050106051908190b040b0406020f0703080f0702030f0d05 84
    0x5a041a007040d211585880141d9000f81c2c1c8100c0c3d54840080340c418407128240140740052100103015030030100402500c1003000056002c03004c040b1400300b02c281c0f282e84030350000002036400010f40761b681e60f00941c21710388400007140c95458500ca0000c21004907880021000c0c0301340e0465a8000d10642400c00407035584140c03880507000c100e90301560b000440c0085c401d242060a0384c6464405140c6145040c40c207552541d07105d03094001e00618100007503100441c009030701c2482060402e03c50780d100d48483c1000120782c48503c0524101142c280040c4125500460141508035480c100302c7d01c40600460a0381c600780121601030300300d807024900840c080e00072000250303c614000b2400076141da000c140c05c10f035910f0a00079420307615030082003080320038401d84c440e048012040081805650702e504200003c0030b803004000c072020100181c1030102942c1034881c890241080d0f03a40d02d410508001300a440141d484655401d41c030380118203e24000030031540607003001161f847c01c2504482d62000240030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 43472828 1250 43471578 43471619
    0x180213090f1e0b0105010809031e040801090309090e0102030c1209151303080108010213151403010306060305060702010504050c0402092103030915010605250b04050102040513020f04 80
    0x18640311110015110002c02e101c01841c0e50080c04200c881d0341401d4050450682c00b46052101c0181401403100f004011203981110804441c1c04c1d044000d84000d05501c504d074003007890f5510300b020314420994031400340402c03241d6040c0c00307201100c1d200040e1800c0f03200c1580d01046001e01048060b0020034070701e1000d640600410266000c1c06c0c85051a015110000c0f621070202e04c011040160406820482017400341210400031400c21400c43c0491022510728000e442c589020401b40b8030000c0c3c440c154030540c485a01c48842d481e540c1d2032a040c07014010720f000403942ca01524001804882c8140301d454031850304980248410641801400001e60001c04560780002c1c041d603181c5c641600e52020f079440640d0303d20080d550385c901076916034248182600150004c000040c01000542d80c000151000702c00a00600d4031040700c82d0134100e00c8140c12210040801190604000501006502600880d4001e032400c0308100001c54505049200e002000c5004031818401801030700442c060440840c42d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 43474078 1250 43472828 43472843
    0x1080606090409030305010510030203060d110a09290414041104060518041e080702060d0f050406060e130314030403090b161b0503100b01030f0608060a18021309 71
    0x80785001103000d443e802d01060b40480d848030300400240c00c0a0111040603010703450110b007581090400500b44032581180078007510b00c00079001c0415950640301800a20800760304101d46c9554541400340d194107500b0f00101085d04800d601040d00300350141c2c4105003005400500310b41d655543c1d83c80f82803078043e9415009960341c5804a00d50312542c20b5100880d100198003c07403840c0514003007601c00700008003000180350345060080064009016129050b90441c2d03480e45600081c103154000b08a8003140c00c00941c03c1c5410f01003031026981c0f000b0705403030302c01000d4480355a40950288550461583c000c000506d0248034115894012001d55000740c46403404451080d075407202c42411783c00a401404424025802000801c9042400f4070406000207500882c0d0300c1c50600000e4039030314488036186c5105d44441070451140e1181e8400c8418841c0b14004201c05615001001d58540003114a6114185010182605100a4450a90034941c010034014224400901e4600034220071042202c600303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 43475328 1250 43474078 43474087
    0xc070305070e06041e0c05390c030a030e030a0c03031107080303010609140a0305031b10110d0207050a05030f13210f1502030c030402010f0c0309120507090e030a020d0e030c01080606 80
    0x10381042c60103d640c8903519000b900c2314130f0425080081d90804821591154070642d89041d0030b803400318038444c0342601030500300d80074503241020034104820103900030204070a45c5004001c041d0010320790840319100d0401c50b10000d441e150201d40d244401e00848001c110080700c00c124000384100080028400034105508150343d03036840340c1c0346400201004400420307019480007024000c00142c24044041301051081c800c4c050b8000b0400d100c1c018140404980000c1c112041c414100064008240d0010031a035480d880e01208484a130480100240710800020340041c000000206d800c80c21900d81405111b842d41c0c1b5a50284540c0390b03020101c801007140c00030244440f0340e910156114100d5140019a640380620004110300121300e000803c0c040560355403000719520441c2401561421031001010481508010389010166840581c240c3d05003546a0f090b10300220152000c14003580072902c03030880040b420740742421113071800e0b90180c0c444020b41c0c0c1c9a41c41410095041100a80b480c3e240 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 43476578 1250 43475328 43475347
    0x40933050a0522050903090111031903050411130506010f14160519030306090507081003080306030a081303020f100503040602030c160506070e04061208070201050c070305070e06041e0c05 82
    0x113403142290301c103140c2d0b00041410941541c203c2c0c40c00d100501050091860006d150704000e41188601008400f016a92030000e400c00100303015001d0256801841106e03800820520f10014100440b00d09002940d54001c5400043c06590003060312808094041d0402220540602000c6080d84040d1924170843d00c6c0a1a200078510092000c1406941c01282c3d035802d19000e9000d440c07010742800200301040307042000d020040030b404030580c1c0c1c3c0f0101c0140d0b651108070010340750000101000e04001310001d4600d4540c81660605803c4a10940303210f107000f80d81004200c0c1c0074607010300440c003080c820400070700012501e9004550040d206100c0d2401c04000d00b040718111006510304440f04d51102c1c06000c855034204041c0200d0507401c071001d120b460b042641050b2941100c1800600e809000b00f0300a04680c015820342d840c0e443c8040843d0006a40c03070910342e9440c00b19202e05851110007102040d020b0429000b2a80454042150030000580c114014402002640102070400c1418481c0070b55 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 43477828 1250 43476578 43476581
    0x306020918070801060201060b03010602100b01030e0d08150d020d030f0318080a140f04090b040204050d0c09050c07020f010806131109030613020a06050f040933050a0522 75
    0x20b2109981da460785604107a030280c03c4410981080061030307424001040107036030016109900b01c61402000c185400f20fa00160040e044180d0198070300e0040320b103011940d650000070544904e040000100d00f0700c1c50030007484103208074120040e411280070580880464002c0d4407040b5854058980000d130b510041750300c1d082001405804544500000a103085407aa03c240810f042c2e840c940d481c540380c0340356110759001521482c8170308030040e5110003041c1180d035160341c1030b01c006100c0500800f021441c03d03c1d10443c9000240101030100f0700d800d01045040369024141c46225a0182c01466200307070b180c0064550b442d000b490950301100e1240b028207030070054001c0c0b0300d590b80c445252948070005030013090b040c040000c0c95045d58200c05c9100d100940da4500e00d41007154101e050203661944107000f10381081c4140e41043c1036080c180740c03810701910002c124036201070039409a007040d9441c0c080180220404141701307107580140713203030400c1c0541e03d05010054890b87e0010041d1310441c030030845040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 43479078 1250 43477828 43477831
    0xa030302073c0302120d0b150a09050d0629040b1503010902092103040312030902030c060307030b1e0a0e010317030c0c060f040c0b070209010306020918 67
    0x14002500440d10808108000c510b00b4091904109805584001d00c2500c0249002c2448286040040c0c410b4210926000340301340034941c0d2040d2056913845030f40c865440041c010060015024101c1d80c02d80c0310606202a054544400e010364070044402c0c940010402d000b110900241d405035910042540c2c034071032084840c10140c3c0c40302e43d6111000081da040000701c40c0c014140700d01411012071021041901c0004490644200036001030721120103001040800304a00940c3c518181c5c810706e05200240c000001d04200d034170608000400c007003240d004a00b0760301444d000079050f502c01080c050383c07441c00354007559204040380f40000312800078000148408074907400000801d6400d000704c91040c05e200325400c0103030105080e504e010794551703641e01948060303800ca00782e1032090110105161802c003d048451404c1140202e441c079007419a950010424152012280c11030154800201d080381d003002e403803440790010000c000603843c60303c880c0065400081d5140c0e02000807003a400d400302c42061070704d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 43480328 1250 43479078 43479083
    0x40c0e0d0c03060c020d080402060313080403080c01050a0207021c02190b0301080106060c0b07030507050904060303020606090603121e040f0308030103050f03090f101404090c021605010e150c0a 85
    0x104400c910710f00302030085902e840d9a2a0071034000b44490030000350032034010341d000755055031096643d948800002003250348a85004044100000c1c0c00024800440040c2003000b03180e200070007968031043d078208101d1141c20030080d04400c00710b1109411101d402004d01d150342c0040c1c004c80258100c010003040c2a031058200c1080ca00300030005000e034800902c00d100262010b4200000704020544501c600800010000000c26464400189a0a02c2070701034540f11440070b401800010344a140c00780d102d10342224003030300420719100040c80300d1600090000700301c0300042e2014a01030340036000303004c041200b0300190031002040100103035030440c00650f10000c5000e400c00035101d504514050f1308003c1622050350340d40d8000c0c44a07c005540b00d81c00d003011107001320383c00980001c41741801e4450301c03000501041c101a01007000140c1c180c558015801c0c0c608140c0c29122800105040e10044544a002e5a400100e6520140f202400d01003035403450000a11141803c01e200311080a10b40203140204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 43481578 1250 43480328 43480343
    0x30905060d02121308030c07030309120302040603150303050a030b0307080a050303010e010f0308030a0e10091101090911180303040f080d09090b030a03140403020411090916020a02040c0e0d 83
    0x9070551640010f000e6004003203e9000c0440401c25150b124070b501018040f01034034140001c0110815009a01141c9a04e501c1940c5089602c140000680250441d10600300441c2c1031010303503240441031200c0c0074242c990540b203080c14130440c90030480c000e103080720400d90148103500010591013810404009000d01c901c00444e641e6060004c825071010069100b11325601400100340000781c6528160307036106000b100001140c218021b240c525014000c2800c80c03440b171400d0011014040141b860080d100802e880d4028101d0303403480341c1d070111122002d040840321010302c2443d44610380c00c801c0703a80010004007201d0516450760b01c486a0a450340e03000c3c43c40d660204410910395a080643c420062419103001c002006c24840400d0b1609940c402c0202080700b03001040c0c0716104d424055501468010303204001c418064540c144007580001c0c2c145108071680000168404041c1030100028000740e400317081451038035828000603052182050040c054610000382a540329071070f040f61014040c008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 43482828 1250 43481578 43481587
    0x2103090f061006320304020406050d050c0a1e0314070e01080609060a0603020105070b1906230603070c0b10090f0203060a09050702030a050304050c090702030a020f010513030309030905060d02 84
    0x20160210841015681e131410320342006049600c084442042c0e101407a880a9030b803507480703200140003070550381c001c55030205d0100205c8040c03103400249107005070019103c1ca0052038a90b080c012481c210145409624503003000c007800012902a003a442806030b0700c04480c802525901010440741090f00000d002d41d00181c01c02c00221420092640c000e28001c100300f0081e415900020302620401501030518411140800c1c03002c102460081c002d6013503034004001d000e0316004072700c941d0300d484d1402c801d034510080401055860245d040360b0141c0c07015140d03210000c0180c2d807802e0108a004003541c2041a841e100040c02004500805008203840600140d50f480c1510801c0303001c83c1c05030402e903c104d240c01c1c1007101b125000012150f01040900700142c6030740e00c0c1d107095072a20105099254100d02c3e013000384400142c0000250081806507002d4070742d64089800b00741e00b01e820449807900c0c00d601c000381100100b03000e40d00c0005018000e29015042d9a10740c0046541a0f11804030074120ba13a0014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 43484078 1250 43482828 43482839
    0x50304120509060a0e1504090204060207050a2105010b090f2a0306010507050705040c03020304021f0207060f020a020307080f010e150408130e01091b022103090f0610 73
    0x810804034061410481d00300554180030500303d01882c4415010300104081ea29803540c1c0300b400b501034000d540c0c429190780e680c580c26210b0207508a0300c00e034005481080c0010030a85401415801592000607100205500442c801c01c0f000300c1c60303a81030307505560b6003c4a8129840700403015204000d6400010480e0030120031400148404448030ba4413800303051007090760a0300a42c100c942002003480d20342e031500340500701380381459801c1d03214680c420320f00003160303c46075019000703180320728000c8500580319102d008500703528400034414100140c21096060000b6401000102c82503181841110b42c450441d6000c203140503130541289149a0000f03071402501c40b0240203481d00d0405a20280880d10050120741100da000034100518078000401c1429000c0951140100106582d4244101651791103004100078400e40b610032000203007000070400302c2400003030f03104c5410031811851080170b00700940c540241d401c09030a502aa0103554510b21100c1c90800000b0700600e000c1c811200800d2034403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 43485328 1250 43484078 43484093
    0x108011508040201030507050c010603050705010908070803030105011d040f0504050d0e180403020307080d02130506071a04060204081f0e06060307060309110d110a05030313050d06020415050304 85
    0x140d110040094103881410640c9500c00c02440c2c01950a003000710b0991520003080d6602c1c052660600700540ca81140001071000004040b030480d0400e0b22744d8150f19443d5070300c248c0c990f08140148079040c0d00820041105501c41c240c02103801146520b18a55044d402c4005026a401039092a0714940c40e2401c2c481441418070548480301114104005003200140219421003901d05002c3d0b280000e140015003810300a00443c1c445a030312140c2d099070398807409030150017500000700d02d1036008030300d203404180b07801d040d0116a062500020902e4070010028a00c118003131000704121140c2c1c0d000d100000d0742c0d510411100c0d6401c1c8030640043c0d640d00c80c0c42000d4041390203c9072075828550012003840003a45003c6204da050303901e1480c020030f42d50040e0500d0840d0803540016190802c000e18101d1003406002e045a022411040f00c50140c85917a07030082503542d0185610001001580e2841003040d450004000c95441c1c3c4514000f50419941e025504107005085401e00c010a01c000200020005074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 43486578 1250 43485328 43485331
    0x30804060605120a0209090307050607080906330109030204020a02031806071e0303020405030a0305030609070e030d1b02040c0806090a02030112060b042004090606020109082b09050604020108 84
    0x10380f074400c100101c440c0050f60321580c014019015070881400f03d05070240c01e008544d032007a0800126112800c10440051034484c08a03440707070890081c0c0340030400d0403c0a0a44d00840107034400e011448024100310314014110603001d081c10300c1201c507400001a2100d00240c1403005070394014644a400200051441d0801e90582c42e00c2040c0c1000b510000484102880c400c8113800600c10f0746050f428070b0190020b01c0381350465941440f905010104040d0300c100113511903e015100130206456480741a504030780d84000059040d001150300d02d010f248540c99041c010540000700c1e40704840c003900402c088600d01d008190000d01e00030f080180300d042085081742c0040400d80b08618561515074442000303900e44000805442d2079400f08000c83d540c503040780019a00c1c1c4864a4024a2099400d10156002d807080190060504e03400140d418010301ca803a21498000e01218541a400c1619200419518070360000d065900082046043c4aa110300c01c0341c031b4441d0004000600346400058500c150 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 43487828 1250 43486578 43486589
    0xf0708060610020a080706090c0b0d0b01030b0910050108060301060b0c06011502030403050705011b02041803030f1103062b0309080c060315101e0201061715011e120308040606 77
    0x201c8407820001407124001c8894061f0030900020303c2d00c4152503c00b590081681c45040c0c40e4402048880041800354000d80721800241c9080045040b60800e025503ca4100c4a04048079483d4104000950140c460f456004100600000e15262100b055015a4101c4020504a0f034016001406460110f0b6a072002d100510700065052918594802c0d5403800c3c5401100c0c100603080d0505100d22180403240c5009590083c07017030010fa0345650602a0b4546248002c2e40045d0400c4440c0104494a104d6540d030300d800700082078503503600c0f5014000340859904034144c1d401c03000311002107206282c10780f00c2d1080b482a51151400c0c1c2c070708140f152601c1c2d411248a8070862003001802000c0352101c4e1a00805c0d0300130343e4103507189944040c040d00c0284100d6a0354507041c0550904a4a0325419407041c1c05450304005444180d4245549690b9503100c61024101c194060b04010300011907885200302c041301009518005080c0c48610204440781c1c40300c4100c001ca000c900902c02003021038000d42c4041e25 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 43489078 1250 43487828 43487833
    0x705040615030e030403140309040614060d0b06070609050619020a0e010e0406050301060b07061112061c050a03050406080609090c04090c0b03090c0102100e0604140f070806061002 79
    0x1410504600084081c594020040c550fa42e8450042d10f40c1c01c1c41641d0003035402101d4822140b541845640d2290b000040c054840c0c3d240080101e80d0404400d05040c1c00d8002030082070030180045001d4004100d003022941c1cac0240c040c880d00c0001021402100c4201340710b5006000d03c0d00b032102c5441e061000d420740340e10b07496005010494850717600c406001c2e07143d0b50900c4e02c00e00c152888404100146080d0304569059402c0000c08241c9d43c0c500401014030500c41c42c006c100005010720409241d00031001d04881707281c00f0358041441031038034a100903d90700001d000b0415140ea5941d40a1401c40030501c2100800c2012a08102103500840c4d03440d88910305881d1910f651078004441ea440e140c0000d0001c0c401c9503100d0030f070700c24011808807400c003801c031410046940b4141b00b40c80030366403141c001c03219005101c2c084000d18000020b001c0c4801e00f00c0340030000c2ca0aa1034036941c04000c000327549080c2c202482103d0500c040c2c40410440b8a0041070040003030320540c103007441880000c0b507628540c8000c0d503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 43490328 1250 43489078 43489091
    0x90303010602120723010501150201090f0615080706030507091401080708150a0902130b0708040b0d0b0301050711070b070302030708031003150c0201050a05010821130f08070504 78
    0x1142c02007100105810003040741035461155103041049081c644e0794410540302031100c004a08181503119a040e5200c000f04c0c00801500004124240c4031211401040c00c2d60440700100042c04640040b080c40c440401074100712901c903024581303004803d900403000a40c80d4070601c081c40790080010806440a0310826025103484400640300e11000380400c1c040040d1140068410b51094801c1c1281c54401070000703c2c4103950300c0109010350080c000c41040d20364a1200010030025910448217900c2d0f014040b20706140c034002c040315203a00b02c2c45043c41c1041d262270000c03405603800c1c03189521544103601d52040c0390054805842c03401e0200d400450700c0401c10014100070903000419616003d5110902e15030381e0f540c000400d0340e04005940001c0103140003160085010b440340e0410188002c0c1c1e58000c100ca90703140002e02d001d541082c41401495000408a01d0481c040d034017981440405c145805480c251142c0a0030f811070303269600c00e03200d43c0c980364000d10000d04240195001040201c078140301d070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 43491578 1250 43490328 43490339
    0xa060e010e071e0e0a12050d050901020d030e0c0406180e010501060c061d0304080f0f03030103020f091b030c0903010b030303070806120708031305030c0a0608070f050c0105070c03020609030301 85
    0x40c0c00204020400f20b81000b4100382d40544188000c1c00e8010000d00311840290380d5030050040b10412410440700b070b000782c6035141d500c24850001e03200a004141d00814248581405c00d4000b064000d5003078180b801085400d80726521540224401800d0803140386001801001e401d000302c9003400d80c45495039052900401c00194840b10000e00590007042c00120403060444800990319010840b02182c0404500000c4150010600070814040307202039500c110160044242ca80c03000340002035000321910b416036801d0822051940d80000341d00035031000703021070025030100c641045031442442c0e8000100500c1c0d600702070142b842c00b00780c298000c6045081036039018107130500c001c0100380111012203245542c5642005850010021401501d03600c1c0111881d401017082d1300e000703540c0a03118142e1079402606200410703000311026503444d812941c841c0c000031942c0688901c101000c00400740014041130000f0302c42c0501440079601c0d00781c1266298900603080000c003d01c409400e80040c0010040d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 43492828 1250 43491578 43491587
    0x70507261b07060905040b040609051302010912020108071d03120a030e06060d060b0315090a1709030a15020405060408010509160803030105090c0f12040c050409080f0c01020906030a060e010e07 85
    0x1c0e194121b6010511003210004280200501d40c00b2008050400007800301c14160500750007000790003079075000403254642d020152540c0d04000020300180042c0c002550045c4109012612104488464191041460b000070328041c84028001c0201c00700040c0300320055090b00c124180240c24101a14603841c01c0340004402e1160107202a1450740c8802070b1400650341400900d50000d00d040d50700283d802c000884541d214803101c0c2c00c403660700101c0b81c801e02001d110016210501d500900405500081d9a42c2d20641003440c0c410079145c3e9020f0201041c21368510000d000903200810000485103071a00703145150a012a8070b54100500b01882070184200100c101ca05468090750a140c444e207910203c0c601e079200e01d0307003180031600020982c041121f1828145d640228000c4c1000c0d0b036156100c0003004211500141c00030200382c01080b00c944d95010300405015401040c07000142041d6590021401941c4100c42d40c20341d1540e1844140b2001c142100e60f00d014202080d9868820701d403200b000342 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 43494078 1250 43492828 43492847
    0x6021504080702030c09100302030c060705030d1a0a030602130504060f140102070e130b060906100c0206040801090302030c060a02070201050a050318010f020c0f03070209070507261b0706 82
    0x4020403070009000095440400c802001004098100042c52500940345035001f043d600089100b805500061101d625005d0140c40803541c1000c05149080800703040c000040c81107c1c500c2005514400030244c50381e60b004540c0000314040c00d00583c1d1408108442c0c0c01c0c56001e80c120300e11813850301c6418401e031404482d5503401c0e644040108000144190010303440c040b6903510403d101c3d14a101004124000041c0c8030345031911170346000005072100342c01c124100c50102c1d500360300000900c0140c541ca6100d040010003203400600310341c1c0390544804a803070a452120805901680c00000c00c0840408104a00ba51000c020b003400c60400704a81d0008025210b60f50301a010050040080f03145040920080e80e10000c0120003017150f5840002a00040e40100d41c0c07000d89402594841c490418011080701c40c0c003540106401e41596a10a058505800c00d0105480200d507041d00c007201c4000c0100320800f8030101940c43c0341c030380a1401810402850050401e0702070313041008100686034002c1e60b4070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 43495328 1250 43494078 43494083
    0x150303050a0203040906060c03030b031f090f0b040b0708010b030f07080c0c0d0806040f1503020105280201050f0106050c061812160c1a0403020f010504090c0e030706021504 76
    0x150340c405610070708a00c1c0d4019a00b001c0811854800009800e0fa007044138151468441e8800740100390b40c4030109521224443c40d1403000c00c241c8240106d50380ba013640900600c40c810440348541c00e0b250380303551245000440d811075240f0062000d1183c05a0800b900b1401808074034112455850120782541c00c924011300003105024130b88c0c002c070300030090301305c00e40c0c0c0e00d40501d1046130031a98040c40028140c40c42950224001c614000c0c0012100c81c80e400f40c000c8120101c82e0541580b4515401142c4582c800c0300c0f00303480c06010815000d1681c12805000c0c403100031743d90000c151401c103034619001440b0180d0100d010b0000030820400500c1c3c0220302598402211440141052415113000341000c1845035040309c0301d10002240c06030014204c9281c03041c40d0003640980e00340e41e03c1d100480e0314a011224882c0701c00005000402c018607020301e04407a441410302d811801e003651105110140d920081108004c41c0b48a01c0702e5049040411108006116620040c130304a80440d071081115540174201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 43496578 1250 43495328 43495337
    0x8120712080a0e0a030314010602030405010215060f0d08030103060f09150908041502030d0b0301021c09020f090a051608060d0f050a1e030306080303010f0e06030a0503031504050a150303 82
    0x2400d404415070090302110020b41c140c4e5103803400c51900800502c0146107403500b0030b54100010407450302c000140d1382625010780040c104100ca103540c041c01100020b1240760700100c40c21905a00d80c131192070390b1701d01c0c510076081c007034503941146401c40c240c031421002c2c81c1d405071811100034080f03102c1c1074100300c45c0d107407400f40095140a03170704000b04e06108541210b40e9440405405812166000005002d82c0d40248010405015007004250030b030310410b506a82c030605240c0034240300302520340c4148003080c40103052040c407034400b2011400e942012038184107800e0b0307201c0421194140c0e5a1450344034220300d20701118140f810400090f8806c0d844200070b03042e00018000202002030401882030140c0e0400f1602c111003031418441101c4405c14002140000d00303140e000100d444000090700e05079000003a84401d6a401c14400055072030006103c0c40e4180324914143c401b103001400258050303404c4000501c00038200b07030144800d8071781c00f402c91501c07a8039100c400350706e91984410b488290307507040c0b41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 43497828 1250 43496578 43496581
    0x602360312030a0203090a0203030f0d0510060503160e040f050702010b01080c161b0306060303021009031e020a0605010806180c0f0405100f121719110703080d0203010812071208 78
    0x6c0e29444c0c9406580002d4262000141d8507403605032047c00b6040311030f040d04043c8a6603545118945146d5074502c260000300304140f0108003a40181143c41c2c07490310080c87c200c0190329644000805032004950b442039500d90721418000312550a0040c640041c0003030905c0002c43c106030440d50350a1145100420000f02c40240e02400c0110764622071f4511803403c1d5049011644a040580080041d4401200503100d25451960034034064020111002d030142c4a8030f441520784084400000010748148007140500c04215000a030a842803c2c081c0c08444010b00b80f82c07030004160051842102820249a482000800501e5898214011604a0a9501103204d40340c07801d1500c1002402e40100651100304c81c0301044000424884000781405418440e803802c402164400301b91140d14426144a5210800c420070709024014001d0058108004c8074061a034030b8550301c08035000641c12030412500040100280b0384200302c50024102c2c0c08200f60714044103030317451400b4605a40501e2082c40034400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 43499078 1250 43497828 43497841
    0x10b0a03020f03100203040c06020f0f0d0f05070807120e0414010306020a0e03030307210e06040b0c0415080103060605010e060d051009020703020c0307080706020a0303090602360312030a0203 84
    0xc0304e24002084c4400c01d54886c01e2901d0414803809482c0101001449941c0d1242100701c00062800c9908011001509502c42266012500c8407180c4d4102c4080c00b204002000008107400010402076010340030a40d5020100c090082c4500000f0143c02c0c4120b041c03402c0300d080c50178035069503411250700181c01aa03500d00d12106aa0001000380c04c2c80c0d041c0404420040100d0b00a605580708103401400c84901d400c1a0142c0c008440e05601d0b01c201a0303000c040010005240461000d411603118050a4100796032980011154220b001c4840000b840e040010010040396004207c06000e0900f4450025902c1001040c1340c0c0c0030711141c2800c03140d11080401c4004000042e410007030b20045500703542d070340c7d01404c1c081c1d682e4a0110b6003078040e1040000c0050074000114510054400d9913028111141c2c690b05c1c1180a0130002a05680040e820041c0140b500210020045410381c8030000d000e4030b4000b03480c84c5520320f02400c1d540b4026080200035081e1a6040030440e030b4400496440181ca0f500d595 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 43500328 1250 43499078 43499083
    0xc021011100509010e01090503040603050f0f0c0d09020604080a0b06040608030f0a0e040606031a180a0207030201060f0303020c1f0e0d05010e0111040f05040608030f0a1116030b0603010b0a03020f03 87
    0x34a0172100d03529090303146050040100c010402d030703181e40d10b06000c1c0392241121030303510640444d411080002c1c00e2003c0b51502c0513130401803d0313015020201060310f82d82500064600c2e031040d8060703401603002c54100402c20040703202403035000d074003180d0811429117000e40c0142c8034842d013207001220160010b42d40c082076000e040040d9440e080170b442000580c1c0c071004003a00a04d0a000c051456a513494820703041c5260515801d5405a400c01000300d103038a4400d8100d01a400c0032604400355500c44001294500d030250304480254080c1e40182010040a018051280c00305120840051034480d004100310782c02811200041105807128031518580e406c240d4014049220a14806d500303150245006480c02000352051340c0710402510a46a600d204000c11a46a07100d490300d10341051000a5040801001522581d000350515803107602c003890000b42401380607070303182c0b003a034681c481c0c1131080c004481c99550340b15034140d0007000038240b40070005242162500c0300074403d000c1a62807400c0341d1000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 43501578 1250 43500328 43500341
    0x141c080f0703020c0405090c010c030e01051e04031707110607030903060f05010303021608060105042304050a05060601030b010806040e010609020a050405030d0c03170c040b03070c02101110050901 86
    0x100c00410341c0314240c500e030081d16401d143c00750500c102e0422004c203020003070100340750418180503152a9412000c9544c10703035010113000d240f581480014051661400204c180399185400f01112656981d8154500f94511490f540f010702c08050382400180d0000300002c1c48200380c100d0440b00e840d2140ba4600d82140c1800c0c4940005002e02c2c14503848070441066504102e061328400c0c0c00b40c5034072105009440682c501d41c4e1280c0c000300e40c42080100602e0030264490446034040c406003114101d910300c82074418541c2541e044401d54815107060091100a21119800503c00d1a051195081d1100000c28007000030308418030079591f07401031b1001c015007540804003c081810b02551161403c040140c000d401c82c1c03089602130700880b1901c81d1100d120b8003801030141d50545448121a450b004042c1907800d0007441c0c0605c1f980b00b008003007141031003e409103125041b2507a800440c5d880501c144a5030442100c903e070700b4410001200401c046010458a0101e600c1c50300c005100c1ea11101040d000d07011707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 43502828 1250 43501578 43501597
    0x30b0609040f0504050705040c0e120a020d0302150604020304020a03060b211e030306010801030f062301050301181509051203010e09061005060406030908091207050109141c08 77
    0x781200c880c82d48229074010714400c0c0d0080081d211000c2c0d50708284010780b4481c025610024013600280d010501c1c02c1c40140300e800c00c011048958240399030b40441c0a1a1500c6001e501603404200440d0014003c0450740c0d13400b80c0107480030350035070629501040e01c3c1505404000e22590305d90501803083d880300742c0c81894100d40e440603207c1101184280c6510340c800e2858901c02c00c82091410303008032000100301d070301595069440c54a05d03803850b00c5d00c00d8803080c0f01200f02e41d00741e103847c1c42c0103290124001c004540c05070b03110f603c60254940410103085820006410003a020b03515031200100d40b8248c1c5840c506814204c0100d12228289070260174000000c0d680d0549080c04000850b20400700300c0068400d5140c00125400e5031107070300300c3c1072508426124480d4005001c110911620b4403c2d0000000e242c4549405814a0380c074400080c18518851951120b03035002000070031481d80e12540c00310081c0030b84480c0c030280d41c0e0310901281c3c1030086030742c40740200d0303070508200001c0005120440d20348a4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 43504078 1250 43502828 43502831
    0x240b0405040f02130902030618010e0105010804080c060a1508060403020604080d180503030a06060c0b0c0714010903110d0c020a0b0c07030506130b18060712200d1409030a030b060904 80
    0x26145c5400c88025001903803581d006061141c5101d0082142240990580d00620030003406c41e03280200440780102d00407c1116401c4007403240c60702460003000118083c500304c01c00400c010722022808820342c0981c0d03010314400e52040c000c0c400402d4022829a420681008139244d0719035074105210050080b0f038401420340d000407070107101408004030155000d104804001d20180d50b80782400c46030920705040190035082c215001c101c4952406000305046841007401240001a1441481c2155407424003503021404203000c81500d900c00f4005c41030744054506051a6180094000c20b4680805020b07603046e02e40e000580030600b580070000540190b034400c00700d42c000c0c50410320b0314200c103542480132601c605600010421100c4d1000c4400300e058080c0000342000c0c6d039003250031030361211481d840d08040c1e03680c0d0b5080790014005044881c5034000140700181e580214a074440d08549108002c0c0c11029412400d1041004012044807054030951402007a0110f0b004002071003031040004140c0e00c113 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 43505328 1250 43504078 43504117
    0x902041b02030d1103060307090e0c0a15080c0a090504020c0a0c030f11060703050703030b122d030405010c02091906090903080601030b0102030910020a0501050109240b0405040f02 79
    0x4903400002010052100a801d020752813000b034080304640025941716500d03070008034040c003070100c0592020702070014510484500101c01c2010440c0310b403d40c2c10910080448a03901d00569811880854124840f80d200900d84807034410b004282c0c0285000380c07031240d5000070f190007822004004c050b00c51038005803400c42d00d590fa8940612181d034031707070400c5070310304400c0d03080e41e44070324052007640d0312150952030301407500d140780c0c2d000c4000348540480580d0041c03143d4021740c00003800b0000d0070804070b00580c84a29034032103019007030289200441e48082a42c010001880244d0744408085503d46d8159400c4507540c96010000100c1d01444a81d013102514022000400c59119000074240500039100d824582d1507540045083e20741c0070b904039015910802c9001041c0c141642035440a800c1c603c10703a454480b56581780c60a444003a80403261740e903200c52403401e51280d240b40d030305401403030b42c001d842c0c1c174900e402d0035007071a80101d1080b01d11a541e5803148180a6415804a42c20442d0381c901c0103080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 43506578 1250 43505328 43505381
    0xd0c03090e0a020301030c0e0103020d061d010e1605120c09040c1a12090303040c05150c0a080909010806090a03051608190909090b0a110c0703060c080f0408090103090204 75
    0x207410910059400c07c0c5c0c83c020000d204200154450f058035000f42c160181412540c6524000e80740040b18000c01044180740000c14281c01c0c802c81000c0c4680002030700c2018000e0522140c108110f8001c1841580c0c5002c0b0080307a0a030001d080598443d09403030143c02a17a032400e1a103601d6501e940142c0800882141400382c3d0590703080101078481405c0e000312095250350848640d24001124000d04000c840b600c2031020303282ca1054000700159400c00b451900e21000da43c50306011081504448184010034600000d1030250f81d540d02402880c0300500c810318010415645d22001040003800703001000400000500300480e1683e1001d070482101c650760411440c00d0007041001e08040d00000b26000f0780401c41e141d0301d0040e80103480c0c20610852040c0c83d800c02e0721004265142101c40e001408014084049100748040c1c001107004020000f1584140f44e400340280b1002070481400c046007030700b00b100207100341040d1400381000f842e001074461554400b141c000c04585405034207030000000305049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 43507828 1250 43506578 43506581
    0x40e0903031f0605090111010609020409060302100f02031909030b0106020f0609060105030d3f0b010806010c0b0402010e04050901020c0f03040303050301050105031005040203070e01031b020d0c03090e0a 89
    0x1c2401c2d2071410074070b031110040407054180a01031840028810407003904651b20818141080301104400060001d0b03440200108a9005912512141c0d448000c01c000350300d81428012020750060404000f4260209402500c1380300708009445014042c0524043d02071107155003401556200b0450380b200d584946000e961f45080242035105840f8140006108090201c0c0d01d6048078409802082401251001a90340740359124100d13481e4448040ba1401001c000c0d43d51808104180082100c440b01c1c8828050681e070b600a400703410321007420180b2507980d03448050100382c1500301008503116103662004998040341019003a92043c01d10703051200c0340d881035009002e0720141400b01c5406043c40f01c512a140c0c013840c0300103000708000340b004000c1c65000703200456000c40290400c0c1c001a8032200001c007241c00c00c3c4c601800040704207850380041c3d40c0510991f045e1040d4002c0400f54180c0c601e8009583e9400055000704114901c20481c00300b41c0551000000341041465035026071070301a05600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 43509078 1250 43507828 43507831
    0x30b06030c0109030c06050705030c0601060c021005120f0403020f01090c1706010f0b0309070306060f09050f0f0403140903010501090b0f060309030a031119020c010e0307080601090b0303040e090303 87
    0x500c2030061860701c6141e90b01800b081012681e028a48515082c0b81c1502a6165009100150b0b0203000c2082038100440c01400b2250107481a92141c804504540c014003409401b43c00041c02488400c0000e1f0740c0f0031511441c1d00781d20083c0707920114410fa54a140807410003244090340c2c000e540c2028198020011414941c1e001d40e1415820810388241031217030150b03248020b04c0b45440e44c1800a40c18000c12103403000941d840f11011080700c00a07030741c9030307a09001c40c5c01030b502c00b050103a80c50741c090050301210700805400c8030040030084ca072824290b4214503e007201030801008d10540b54182401320f07140b802030311070400005002300415a51088014050884890140d100f40c032881007036112840d01d041664001d1142d034008500340055000145c0040c00c6000c041c83c8214410b010040b654030320840f5103005007203e80c0c080c0c04601d1880c0000b51451681c260024400d820100c0240b00b094800075416046540300d200c00708001d000d01012a0451085400c01d0600d0f00002e400c10071203020020086 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 43510328 1250 43509078 43509091
    0xd212018030115030f020f030a0507030501060e0c1903150f18050702030f0315010e0405161202040803070809060d020a09080c0102030a0c0b070306210512180616050601030b 76
    0x2d10110001d50140e0450fa4001c0c00700416543c11041303c2c0000d030800342c40e030040f00b17000901250300c40c1e103007034403064030b030904507401100d83c0ea4483c0700600140504c0c0c203099400c0102e40415a0a004014070341460301816402000c0030566102c4a52541c1440b41803410020003440007280003d5454044140801404152488400c0d041c80003080c0450320003c00c8507031001c9409142c90564482c9050b201809113641040c3e03041200341c4030003210b159940d100d0240100c506400040700d100000a010305046449203803c140305105000030051104080110782d03100b540804456074815031580001d516000e902040031403e480481c070002c000723800801380e400743c1d14802e04880b002c8100400484c1c0d01d1080c030020344001001d513005040000d203881c2c907281e0440628180840c026840301c0200625007107a041103520390b802640f4031814070100b40042c0301a07840c4052914030340b0500d007000018859003503409501640e0001071040030100c08080403400039038400166940781d42c0d6400d01c00040340d400e8408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 43511578 1250 43510328 43510331
    0x504050106051b12030f101802071e030212090102070801060801050402090f04050a030e0301020c01151508040503030606090a080d18080d0e040507090302030a080301080d2120180301 80
    0x3c868403500000c5014a02c10708080b02451541e809243c1d03482d000c000b03410403840d80e49544e40420311000030031805507444540c0c40d00603141c02c2076041100380359240c900080c42d4004110301e508003182e0701092070a86042d440c41d44c81c0d07952160400407858840158441c0c20154030700040440d1206041d000a8001e50007210340290ba80c031030440d0300341d1020b0250340080007688000314000019010781103d0100c008014001820107000001032130035200000c00300d04482070050720a100c1c0c40311020014a02c499541380140003450190b680650fa4807000e03100c544a44004202c0709040da40780c0c103107003000d0030b84407040c1e40c900c4a02d158050101c5520300091402c0c0041402c010840600004908003907080503034540c01c01d40c2d50141840010071014040c082003024001001c00980c078200407945440e445035645558940c50003080f242010455040342040001071038424528444c0c03495402840607119200042d04120000c9160354400820015141100e0200b00d0100c9040140000088244140c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 43512828 1250 43511578 43511617
    0xf030f02061009051302040212041e0201171008030408031806090f010f1806020606090a150e070203133507030305161a04030f02060103030806011206050405010605 72
    0x140d0300c0300812a03a07012120101c1c0310401c4041202d40129400000b4172a00c000ba01e8003580106080c0e03844103a64286600003407050104001c00f0318604a1220340070850310300c030400141d0000381040b1a0262449506a00c02e01040e1210a60070b105001000c00748100d0703030399076900e902c07450301c1ea000000904004568504040483d092040440da4513100007400288125194801592005c10804401c02040320203100c6501e507003004040d0340301610054000b44550300e401c0042041000008002104039800c00451a084041150890040d02e0700144c0d101e401d039440030003ca1441c0103900b480c000c03482d0001c10000b015000845943c203803448660b0081c014400b1a40301a04214196000301d44540c410001000030a10407000f40c001640203503402e003510101601c4514600180085121800905100f440201608440040441c01a40c0050080f42d0b145403000380c130111008090720f040c4010103520780559440c1741d0002d8082c2000600c1003249503191500200035402100000f030003c40c104d80b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 43514078 1250 43512828 43512857
    0x18070906020a0b4507050402040302060304030c03020c09040b190903050a050a03020d02030f01061b0b0112060e1f110c03074701151416020d0f03 64
    0x1801034030280d049400340303019440b683c0104000408800700c00702c841000b80c0340c4413500100e5001c4c8100c10310384c06070000c90302d250705204a42010041d510481c491441000204010380700d0206403a482505401d00141d5220740b401d050342441c2005407503d51080c00c0d0010030081000c2d48a015018000b45501c03e20101441014802160b034015806404500180034942000748100014400400e4500e0058103080b072043c0c0d0740050340c10640315610441c5e00000140845548540a05204481141807800c04a815199040401ea044c09482555001002881d091001581041c210f240340d020442d44000c0d03051240002c04031034100341d000380500b401040c048080c050803d5440242c040ca014600d0280c4a6481c2d40440c513154100c11013500780c0c07043c42d0750800780d4115402c0c02d19107001000b8611ba41e1034050068181da05030020031481e440f421b00b41c000075030710107a054250301801004584d500a0125802090308100000a511088104a580400150641101c2c00341d1080c0c0301d40201c00c1500 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 43515328 1250 43514078 43514083
    0x20403060c020c180606040504050f0f070c1220030a08090d090806060603040311060a02040f060f05030a050603071203020c04050106030e030f0a090b03091e03030105130506040b1807090602 83
    0x70703011a503000d2074018402c44c03071440a504094020701d0003480d10b80742c9551803011409640e8200d516800304540700d0100201c1c0c12403000180c0c2e1140300d5203494030f0700c070945645090403002100310701e20030030807441031021326412030790501c240b02c100230720880c0d4803441d22801c000c0813100211103411090082c49402c001c042c0c01403100d03905990ba0340010b000c056850006101081d0030040055042140292040940d082c090002900038055a000981d40c2c44c00c01007141d030313040c02c154400f4040010000089008690003400d40743c000354500000305064541c1c000180c035113000c5400c4545581c84240ca0581096000210341c41c2e079800640c2d05004a1307980c0d400039811103041e031140500300c0d042048000640d200d075030010309d14040c42e800d20040894940d00c0100da1b507081114810702ca41e00101104100644040041c00c2c0414442e00131031443d81410003140c1400c0e6659a51201c0c00c0d05c0700d020a1481d5103d0b08040704036074019046601c600070018a102403800c0a54245011031100f01002c9031300d6201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 43516578 1250 43515328 43515343
    0x1d010903120612030503040503090a1d0f0f0106030506030c0405011e0506090d0b070201060812070203061503070501050d020d11070b2a0901031806020a020c120a0206090d0b0a020403060c02 83
    0x10024680f04920040d00d064501d540003e20890b000c0c0402c000b07110240d594214150064070340d407584407040c51041d019040c5500340c0504030061561518040144540f1502401c5042d80c48510f00400e507511a400424509048510b43c42e0740941010f0005c184401c001414114000302d4110711b000e026900c0c0f050103100e200b030242880d005810305650f44042802d0004e415001022480001030302651000d0180c00d200030403c00a0380000d00050380c106603d010030245800035a200e01c445d100c0040000069661101d0f4814541880b5010030070400441c036a50541d400203d4001e0240b1240c0c1d50541d00c00500d03800a4003c031643d81c130110104903065000b2032094070455407400c098003031012448200311a41c0000310103904140d103905101000641031010b4404080c450400961600a600070190401007a45c62490007a03008041100c02200c000406600068041e1103941d13130340b1744800114104c0c0031043e0b405440c8003140030602c030551001c0d500900403207014890405c002c0380a84412a02d4059 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 43517828 1250 43516578 43516589
    0xa110d0506070e1c17090d05010212011d1513060b1b120304050a022101090b0712090c03020409060209150a020c0a030206030f0c1b01050f010e0f070807031d0109031206 74
    0x2100c181d55070085174100c0051008100c018800d4a200702d19030340e89400d99102030100c0584c03012100040049401c0340d41001748030804549011500c4c503040303840d60840b07158100c2052043c5460020786078400140d9003e480907204d00940c2e03d0381e60744146d01120202c14904444441c0d0301c035802e08082d000c030410064034000c590007005862940c019400300724078410345450843c180001c22495200600302413141d16240c5101d50240401450300d1000a00b40f40c3c0a8054000654103041c03004000460000840c3e041da5030450300011301c4a0f0600705100240078076100d1a8004103840c01401032201c81c00003400d203070f050a07401c992243c1c074a5000c0c800181c030342e484025000703071003030000c0b40300340c0720300c10308607500080c05955982044820400c001451942c813591000c2d50355070b00107100d11403440440542c05002c040310f90018505082c126445d038000007c041604010080300411031481c8242c005581911076401112419004510034a00a01e44c204084020a80c1b60320800c042c031905000720340c107c45 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 43519078 1250 43517828 43517843
    0x106030c09050405030409090302101410030b04080919080d030606050306040b03011b0507020f09060102031209210c190c0b0d0f0e030301080f06090a110d0506070e1c 73
    0xa1410503000082d00c009882141d00d400180400b2410700b9040c0305030722030107010703038010800b52a00204180c2150f1b01c80c00c1c2c454a4801b8401009000107407000712004503a03004a040f145592203040c108800d0142c4801c43d030b0300050040c407170b0000c0c803044165030056a4101d000d03526801c00400054085403031602c00c1b1700210b90144002003692a0503031025100754400350001c54001058440e481d1007529450465020801c04101801942058554a11400c805403082d03452810400c0010796280110901d44030703006929400511030800074802d0541c171222545403844841042c41c0c05441e540c1000c80c0350340380c07803280c00c288a10303541803094500d100729009840d8900060400400c0904c0780d10015051001c152030f201d079400018000d11420091107050806513850b941481d82032707820100342032a203031010b0744110103104503030101040f540300c80c56104040d42048955000031170641074441c04054500d0245000300441560442090361000350210b4440d0030240815461080c1500d0802e000b0702000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 43520328 1250 43519078 43519103
    0x90201110105040b04030e0102030c0d0f03150e130515160e01021501050603090c0a0909031e140304021305040c090c09030506010b0d0b030f0109020f04110901120e010c08090f010603 80
    0x613005601c100c80c2c01e901807041c5c0e86003500e260418ce00e40880c1c4051f00c00002e00f20454152520380c1882440e0b8900d840300300040100d494803000701c000010181000c0c103e1040312801c0300800000304004442a050546d20340740781d241103054a40c40b519180400300100e008850302502661001c03070304c0c42d4500d041c0003107004264240800c1c4030300c9800c0102400007502c258503504a03542ea80548040040501e0742c400f00d01d0401c02c0c40d00621145112500000910044101920403600100c81166072400311800d1f42e100d545d9400052003003c14170041840e46460301d410b11090042c86980c510582d40004402e00c4140440142191032159a10000d440b40e006200107014100407180240846540024045241c11140700000d00700058115000741da6075542c0744550841c2000032000d203020504903410086003810a1410300c482c42100109070401412045110310410603600094401d14041d0080140502c8c03400e0190040d6001d030381c07440051040c40450303404240b05014400c1540e50040300400c15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 43521578 1250 43520328 43520333
    0x3071e0c1202070504180203070806070203070f11090c1b12090613031a010303121a060c150118050c070201090302010c0302210315040902030601060c0204061503090201110105040b04 80
    0x101c254006001180070b030150020303d582d00e034080e8451703511100610328103042d081d04c10140f4001088e80300d242241c000d00201f21906802205030f40b082c2e50054035843e00c0720928030700141c0d0304070080d48084c0d0101c0c481c014012030800b0040a4071b40340040302e8088070400103450304a82d480c110411320b051051000c204490040c201031000e040d5000c40010702030b024544960703030003012507484540282c071810b8480040040c140e20500744d6035009080601003016101540b00043c145441c0c280d02405403000140d41d0500d9882000100c1102c040ea40d01c000706542c41c0c800d1244815040c40043e860b01c2c0c1083d01003050603407904d04039000194161a440d04071441d5030300546170803850340016400d50007503002404041c403801179844461184151130700d5036071900c1c4071002c0300b00600c0c80760503004900e080000801600c0009050b4151913441c10102c20b00d24075880001d02a0106401160703c0718654100c072024503400d034204000c0d01e4401d07290760520540300382d90f250880c0d00444005d4003440c00400030501 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 43522828 1250 43521578 43521593
    0xf01110c0f0703080a11030c010c05070515010b0304030305180604080d1a0a03060504020a1205070303140a080a0209030f0a060509060708160302030406020f0a0801030203061008030d0c0c020d060203071e0c 90
    0x1b680070b80c0c00540381091080c11846d421a2030540021010440000300001004002c0c00602405211140b11032102c0d41803c040b000d1030700000340018245650743c000719110015160031041c181039520b044a02502d081d2403c00c403143c02035600c0041711810610303400c0d8400c0e030740903098103100340180c84000c01c0d6246031600340c0502303005001039801031000440030a030001036140503003025014000030b04c01d0b140b075454010303c01c02d40d00c103400303121203000e0040056090b8050348491700302c010b40c44d0250f01c1e115a04000f80c10031883c91071442a62080c802c15004200c0c40341c102502ca07021f40c20946d002c90791000c205813103010040340c41124520100f01d03080c0b0308500039405183c20500a000c0142044000400342480390700498500c4041541a0010411440d04004941e44445203074000c038005850240c083e40d4a001b8254000505074499100d502c03081d21138890143c44030b40003410a40d02d001c039410101c000398020b654140c000303813800500030600d54680001c0b00401540c2d503101c004140845c0c94101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 43524078 1250 43522828 43522847
    0x30010c0c061107080f0403120e0f04051005060a110c040506011209080702120f0c0618010c020303130618080109020d060506040608030301060908010515010e01110f01110c0f0703080a 80
    0x425086043c403800c40415032902c0030301031780f40e681c110059603030f800d5007455140110000301c1041040f4884102920640340c40f2440700444034243c81c00700f1540c4a00c0040e140408080c0c110903044207000c42ea1144c1994401d096408088108040e107020011650030b02c816504c007200c030180810f0042c80e000320400c05a501c020403c138001c055407424a1501e500040c1000b202c9000512310758008010250b00c240f080c030200002003011100302e481d01206d400d00198805a0000041c14000605000015511306104444079141056184031a00d0b07194880503161407883d6900710042070118001080302c0e203052003541c1c0c42d02d80040800f10503000b0b41d9030301c40c0a000e00030406078000d40c8500001070719160400141d80039248503242c4030802401c0106850031500d00a1400340e090b4407080003e10030344d070020030081041d802803030041030f01001206410b03d0b245400e00018150742ca80800540c8001d503001c06171045154039010345d56188130546045540b5007040c00054000102000603a81d454041e401c1c1d01e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 43525184 1106 43524078 43524101
    0x1412010b0109120510021b0f07051e0607150e10020405060d050c0c0607090e010b1c05060a0902030405010911060307020c13090230010c0c06 62
    0x340303802d0061280755111003032403c0c08014010140640351034000084019941d8100d0307803c01a1304c6450743ca1100040d4050070003401c0019202264140480e01c00900e000014018400004207070141c2c00c800c6036110300b04211441c005094400e0b0403a0254203914001010801c5016460400c40e00850a4559520410042c4610b940d20810b98400e50802c036400070365951703003071480b8205200308154005103109903820040156400100350381521080c20040550780d0741ca1462281d03c1c002e1a024a010903000311681207030203081e1740403a0740424000d002016480c3c1c1e0310440412039100796815201d41e51510643c2c410300c90280c00f15605000c05403800c0d2b01d14507040d00020f4540c0400d0301c07110f1003110350b810318982141982d0002e104a41e00249000c491034002140006072141080741642603402200d68864000410f2091611045454440c010300c0c0540e6038a160050000d007460 = true := by decide +kernel

theorem cover : BRFrame.Cov 43345328 43525184 := by
  have h0 := BRFrame.cov_init 43345328
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43345328 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 43345328 ≤ n) (h2 : n < 43525184) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
