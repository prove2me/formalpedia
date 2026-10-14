-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3335
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:34.443947+00:00
-- url     : https://prove2.me/submissions/2383021d-d59c-4582-86c0-8c871505a522

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 599640287 ≤ n < 599820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 599641537 1250 599640287 599640319
    0x5010c2c03030d020d020706151509030308040b09240a0e0304080c0609010909020309060103140105100311010903020415150c0506070305040804080303070f0e01050a080c030403031d0c 81
    0xc1242403038115031642c01448000065515540103011403240318000500d40002ea903944001d9400700b5a607500080c3c0a20b40801223907440c1455401c2800c01d41c50401a042d05556028124900180002e0a0641318500160810008010585011008141c0284210b1011140c1c2e000101c08644940301035040c05600032281c00d00200341c400741c98456014100d105074907814041d21f50016401c450400901c01e01c001040e10061004500840409014002641c190700348070a810485080104483c1e25080400c07880300c9014075084181c030303800a08001e001c02c10400480708001c8a4202079072052801020130800d002e03400008003240c000c4071280ca8408810541501c15410b44000a400c0d80c2100002480c0b0f035200364040e6910a200c1c6000c10b00b080c0c5c0311240c0914641080b11031402048000f01d014003107a42040100c401d10b0b40034a0002e14008a040303004100702d002805a4070003401c080007080416000390020642c0d01140350720382115680e103003a4150388180d5040c1e0306000d900296461080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 599642787 1250 599641537 599641607
    0x9010e160b030a02030a02040f030507081b0108190e030a0203091e06041e03080a050d1a0303040b0702040b09090d09080d0f08060109050a06051b06040f15020705010c 73
    0x494010711080780c00c2d6519402d03c0400303940001c11000c501c40e030800c80130a00c41c0d8803840b100041c50040c0010100039040071191460080e140340c150201c0c03461144000c61984c3d2103042150311a0b0303540707041d002d503080203074000010b03240360724640342513004c00b00c1c4810a0a900001404100e1000c0710050045202035100c1d60200721000c00450f00104200414080c48103117529030700361604107543d08417400e9641d8407203a150380c2101c2da6690001d4400039007a80750324070b5405500c0c0d51a0500c540c1c11645031803680025664401e900c902d041c007006c0418406c003990354950010b0000400904000000d281500005481b10341c203150311004200c800701c003c10902000610061140000d45030b20158000100061304c1c0400d000703001904000344003030080740c113844d440340c404010403d60700d80989a169080501100042b4a00c4400c503d0b440310003000089100c004c01c02e610103030000100d414200300700d00c0c040c1c0644540c02c0c007d031240d03080242c0300041031380c400f20b503440a0440c0c1d0041402d06506a01d8009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 599644037 1250 599642787 599642789
    0xd0e1806060a0f1404060c030809010506030c12100908030103020a06080402010203091e0d080a0917100c050d09080301030326060906030f071403070e0f0708190509010e16 75
    0x2030000030901203003001500035110000c0f400e165080c030b5100032404010044040d071040d0008030000b24408264400c064020860f10740014801000740054902030010035618810032061700d20402d012204101c1440b000c2c0054200480032200504c001e40fa5400c0c400d40c55402848201d000359443c810000382c0520940e901c6004540c168051450020800c0800c20400b9103842502d940100390b0001100c284d5450b0244a030440c40b442240762035000d4a40040e018007089e0380314410905000c000c1070b0074040080b418042858041500140d0700c1e0301000c0840340c6020b2041c040e031241c2d14050a400034000c01d5009035040303030310a5690825459207001da11000f50035161351a501caa4105020848616002c00b08560100014044031105007031251310350b1801d003140d80101070382c1caa04142103102c0e0805000c0c04000c2c1c6511100c005d00b0741031a4030924558080100383c8000c124440001c1100340c1045041d55030303100303080072042c009030401500d094020090300b2071f84c4d03100348280850b400480b124444054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 599645287 1250 599644037 599644039
    0x41706070914060a0306090f0603030f0e0a0e090a170403060f0b1f1b0b010e18061504200a2307061505190905010807050f1002010e0d0e1806 62
    0x640c02d400220240081038100c14040302c2810349070040440c2a0701e151085440c0500100e0020035154558240079058102c500542e1080000300401400d0fa511100080012902421000e10300d59441244040c11719480400080c004c0f281c4045440c2c03002076083c0944281c82c001c0008100c9110052001d03401c5a0003400b1854001c10303c401c10221444820965110142d032906101d1031103182d07040038110303000c081a012108611000c005001075104a50303915800303c8220413404a00c088403100070386d2014002e05492010348203401401e0291126089000d880c0556040041503524220180d50030303420401d030400018074072100101c81c3c5901c140b0a40b00c02081c200038145440c280341c40355405852181410405000400000900d640361402000c1015044014096459040c64506807e0302c906900410003544140030600259a81040018400e6012a982c48200f210b942e0140d015000142d801c0780c0d00c0c01681c4410000d80e030050605220a04200c50a40c0820300c001801100c07d0000e0300c800f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 599646537 1250 599645287 599645309
    0x140307050d0f0e0d03021e1005060f0a0e13020a38091009031502030906130b070507150c030e0c0109030c1a04030b0403021c020a020d02190503030417060709 69
    0x1c0c0a044c414003154001e402031046d5402002c8070394141d0100c007200c644448440d8003032103035030f0aa100f80e48503030f0790007020032294002c00c1c0101c400001c042c80114000c00d017103031401001040c4c1045400300729118403603024080212180d40d07569241c224505001861107004074808048400d5112001c465030380003010300c103103420900c20f9014010b613940c20b48080810f00c0090301010000c0fa5210b020860520f44805c405a540d29040c1d103120b050440240c4095110304040f65400700007480c2d012034540c00a418070b0300603210a1300b42003000b45c80200300030007504145811660070035641c0c90b81003a0a850314201c00c80d4040e00c000c800440342c5154504c4041c00005138014140401c1c2d480084d80074a1604910342141425160307261071811040c1a80d040b000340e070144042c581e0441c2d000c188000700120f41e0001d085180c03040d0f00130486100d0702100091245043ca40c40c007404081c5078503044c01922000d130881c2d884e00c0e00c820070221002000007038140c80303100380000600d070588107200e42ea0640e1864600303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 599647787 1250 599646537 599646557
    0x60b0621061216150e0622061404090c1e030903090815060f0d0203070e06090a060305030a12150b1b070609090c050f030c1b010209011704020409140307050d0f 70
    0x1041e0a108800d940c80002c05c1009a9a111203503203050142034485166010448142c07411802c08010b5035866110380e0138070400404541802172400705a0302141c0740c07418049144211686e08032040c0342070164030751500c00b4180380148c10540c0b40e8001c3d02518440d40350104041d0f102e191150740c640c618038100900c059504009101c5040c8111000384a00000e040107d0040007540040d003000407640014606148007401c001c0c1c00d00d00142310303540080c002c500407c1540e0464036001c0e103034450030101009106e80960f284038409ea266001d410301e0502c01d50022003151302c031a10326a03e0fa000010105c0c44a010103001a00c5a40109031201203a0607a01e0700002d052805161201601d6408403200038130000307000c0b42100c180b084005521078215040b006a80d8040b44040003050505d800c00c0107041c0c0e10500010004c2c1c0d8108240b00001c1000701040940c030b558a1000601400c440714000309400c0c8254151143e020700003010f05249403041013522661241c0d0071085400b803900140c0e410001d400e041d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 599649037 1250 599647787 599647799
    0x1508060907120507030c0602160605040506090402071401020c0a060f060f050114040e0c090102010c080405191106040b0306090106020604030905060d0f290307030807060b0621061216 80
    0x10340115428031440946a02c55540e0700c41b0440b00101d5171202c2c015821812000c0302802c082e404401c083c00c1541001c90801d410400418518000c1300f000711301031580000c002c82813142840c0e04103150700c0c004000f903594254410002c0d441c6d141b4680116a00b034208021549222003078000c2c002640c024614582d803c0e8038081c01112210300740b1404214841003000003085502e40d00d19558403418003505140c0c2c0d42c80203400020b08450043c2196820041d9850900000038400305500c01c049544800c40c47d0075103680e080508080b43d444421661011000500040c060380f0310001d103220780000c0355915a1070b80e0300d00c81641c8505e82181d0040000b04511003d00030792a142c0090103651400070000203c14004134401c2080300c44110000b445a800c2c45400040e000c01c9186010b4403000a038098000c552659903410b10902903801c00034000354640b0070380c00381c9071070307510560301507003400c010018011001d03880310200e2203820b031001c074004e031442d10f620b03907112500160300c852024000100201d00c41c500700f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 599650287 1250 599649037 599649059
    0x2060d051305070f0e090f0d030e2a01080907060206060415120b090111040620030f03040b010e1617100503070801050a050708010b0a140403060501091508060907 71
    0x8180101c8070401d06507407408500708100c600c1c080e08990484220b4203042241c00d030301c101d0000b0100c2a49034019111003000010200f4800d0700b40c3c4090602003000c4107150640360500381c130505401c248250280f049031510001e00c04081c40d41c0801c1e01c43c140345440d5070035443d40342c0c980c40c0a26800741c0d1040c004111203041c2540060510000918203030750b0107485403149030102001c0c10301942c1b003428800a11104207000e2181e00d80200a803005240740900d090405445030b507880040e180e140303c4a03c02c202c1c250a003441110810844c1d407070043c0d564603080c40d080c5001c840070700a03006a48203400008101d40364445d4608000da045482c0d1205403407287e0000099020300510011003501c1c2c40d030000405880401404020300386207000881d552030120303e40c0045a1000704030b0420000ea42004205144090040700d80141c402d21307000d40100080780c4d1009444c46603a1004240038500000040c000382554042ca003407000051011821950b10204030360303940d0703040c0d40d0200241c101c0b520800801c0c045c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 599651537 1250 599650287 599650291
    0x80f0a23120f070e0405040807030f02070f052101020c070305010c09180203040c030b090f0118020d03080405010e100605030d08060a050d1406070203040e0108060f0f0603031b0705130902060d05 85
    0x91820850020001020030186c0d0801ea40450b4601000b150080c10190040198000310501344001d1106901d003880c5c03c0e00346a4180b140c1401000c080b0440e017284041c0c08003601541140e08000d41d0b8810bc202ca002e552000780e0700c03056607035519060949030301c4c0d449003128008035881c0790304032445142c002103008003e40c0003800072a8240d5200c2400400250743c43c0e13400344902c8110028014280b00446001d09481c81030303000c092240042d818000040c3d03100841246100c1c0c05203030403070203680c4600e0b1160050000d2003c2e003c2511444182802803d9241c0110040c1d4100b03506807244069802ca05554156090700c0c05544054030744ea041c4401d06008070702c400c00340d015004e90100c02c1e8030840c20b107080040954034400142c100042c24003500b2054480c0c00d00400c0050010107440c90203850075040b010020300700c407c0c440015004030b0745c190b034104192101080e000600a00079941e04846a986519030310032140a6980442804543c00d058411681a1074014042d213152a0402d24040300030000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 599652787 1250 599651537 599651551
    0x2210c0606060c0c0310020307031103010b0a080907030507350a0813050607080408010e070311010302030a240f06030204032006040f0306020315060f07020d080f0a23120f 75
    0x303a004d0a40703c84e541000722007600e20002800503a07030700340600028141c4000d9080691292410401040f142041c00112400f207000391500c2c46550701c0d110f4129041c03049551000d00b940c4038644c0040b83c103140380c400300031442487d280868030084110142810241c0200105200c03500900026800b1524450080c040d004402d083d801c1c40c503031588001441900a018107850b00400840c090080c0902480307105101403596004081003859a40c0301da088a244000315410940c0110205949003820740200f201c3c030b480d541406161500c010001c8100d101148140c0400c0508043c0000c0d100f4064821070b000d07a40c01400e044940011401d9200c81062031000302a003008041100041845405007500084c502c40c410160360381c00c103178180800586544402c64810301041140d810071405400c101c030307903450f13068136032408840c0e682c202807100c2d001c0d84180310185000001c0a00316568020100360410660a2210007401d0710790f03064491a002c0c00030300b403024000340d4011901020081c40309941c0448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 599654037 1250 599652787 599652793
    0x10503060f190606030f150b03150a180f0c0305070f08191104140307050f040e0c040513140c01170c040b0f03041a06090a18080a02210c0606060c 64
    0xc85408411a000360307100a0002e55070b641c9181d54506c184c0540291240b0061080041c1c41c06c107600300c680741c0b1003c3d003204804580d440f00940345880384000034004006210001a81c0162400d4003400f820304904400f07140ba24080012022a009210b590700807042603440310b200d545103034400d072155003000e040c41859002c82991341d607070200b040c0910052402080c8589458130b01c0d02c0c0b0181188080c11210328440d40100307406000c6130301c5414100d09401d078215004280c2000742403400f03080000405001d6005802d180070072204e01259003056880c2c0388129800805445030400e81d81e26000e007540c0c16400241812044c11800c270807a0036440d00306640c020071514080d528400c180b10390f44002e50b26032030443d002c8200000d000c903c0c1582518080c0044254900349880380000700d451a0003010104215914511682c01444003180f580150344d209107065030740d68a10340701969807000c0c401d449002c40c611846241c101c400c1d00040e18180a940340003002543c0b40ca808008040c0c01c41e1451180b644 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 599655287 1250 599654037 599654071
    0xf1009030302120c073c06140708061002010204050609010807171f091517011401030f0212030a02060708181006060906020c0d200d0c06030b0108010503060f 69
    0x22078580c0080f4000d950780740c5010707a101d407145010805060500c10a803440d40d034000c9108206c212070010003106a014821811030b03c4841d1500800601c11004100300710001c042c10032002c16005401c40340200406c48401c0034407005000103d00741d02c41c5004864003c4818000700e5050350050031101d4002c44039040c1a51040c4080721404000b145c216850f804c10205200030464501c2d90007100805001450014401c51143c03c9036000b00111603c148013100080525081c0315107002e50014255840001e5482e03440d503941e040001074078408030000e900c500038113145d88034541070000440300c030104544c000c0c04656807200020384920000500300c2d4003221a0502c2e03a41040d105004125541c0a0840005038030350030520b00812401e000d030005415540146100200f035030b5240c18001c201a80030f240390451420240007614003252107100a50480e41c111100000c10000f041000300795800e69a0400c1380340141e00044900741001e10600707405404c800040360100545501440e03002d80b00c420402226 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 599656537 1250 599655287 599655307
    0x102041502062202010806090a060504020f0409060603090314071e08030403090e3303150915010f0b07060e0706091d0c0f130305010204030602030103140f1009030302 73
    0x100d80210091030050b00070702c0801c82ca511501c2403001c0f88403482101460b400c0560380c0007904d2090f010340024403c1c6000700003e400301747c071904006d01524000c0c10643d03d41340d48107059444da401c280118605141454408981715210f48903c11034a50141d8540003000690081c02d0b81030f9010390025180307800407695a90f4540600f2440c11002c900c91a0190756a1500f420018a8054280c10990f441280c9100380089009840c0709a40e81c0400302400c040d4040d14400314074202141e000c035894140c0100c0060010001072260a940300d140800103032041990340450120b081242401071076483c411130740c0c060007022000c41c058001503104660001b00e4450034aa103901d0540d4650151001842460381030106040c01107a00c1422002e104d000d01c000d0801c0c0100380a80c1c0541346d14416501d6012a000e45c2d4001d03100700900003560403070021541d580c0c903410040c001e50b2003400140c2e05a07540001401c006200068900c005901d5040608000c140c0880c0340400380110100a40400d90240000042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 599657787 1250 599656537 599656559
    0x314120705030610020601080c120f0604060921120b0402070609060c12050c07020f010203070f06141303020c2202040b030103021030060e0a0501061805011b05010204 73
    0x14102036110140c42c1c1ca4035404212811910041d11001c41d00200010000c034440011082e1145108446940c407001000c181e582c601000a520310045101e00c0c0240010301c94543c1c01040c429020b0070395100800303041d00035000105e050800c0800056100e041c66000491a54041c0d000164020400362529905403a5241981c01120060b6061036888405450715600000715520fa9001c040084c09545450000c41d4468010030704040d0040408071070344141a84240304031900c3c15030003c1501556070b5181402c40003003145d8000c5141e203e0f0404003080c0d284009800e0400155416030061002220710000e12860300743e1280c01d810040015a04c4c00c400a810340090b0003d00030040c901d544a40c551300420178020030308031100e414880300c42c0550304021917008000e40c45024a081c0402c41942e0261840010503195000a0528003481c05200c0c000701c141d00a01c2c12a0820798581024854801c05425501890711402c0d0100d4001c426200302c02000c5105030a034103029600040c240b540d52201422 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 599659037 1250 599657787 599657791
    0xb330405030a1a06010c080417030f0307091d010510030b0a260d0305060306040f0206120106030b093603040b04080604030318080a120902031b040614010c031412 71
    0x1003e105081c03814080743c01e81d014035030b40001c0034601415103018a0316035201522880c0242051040b0503540d800022004004980c51003800c0004241c0c0d82c60700d00c1c0d00174910310641c0030f01511842550311180f0320040800c2040c2c1a0ba4000b07104603090420101e0030780c010a551001a50815003054002a050509160354005107904020540c19482c8400c41141070a10401d9400141032618040c04050740b0005009503016030301c20000d07111418180001a103900880340381c000c120703006000100b012903042d00040b0440a05072408040c03611140400e201092081419201e1070720034a100000c03070880b010074020000c61a800f901d00c1d00e500c0302a4203409a21903006004070f0741c4000c0901003050b5051080c90400701890054000003036075942c86010034031808101c401000049404c00c20140302c0c03540101c8090354002c040740e80001e07164910070030380000513443e544128034100f40010002c5010541e2400700d94169503d02883c1c0c03070303030360700307507501444641c50081d41c0c0700521605040b02402003540d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 599660287 1250 599659037 599659043
    0xf0d0b22062d0303050d15090e010b0d031215030212030a08090c010207060507021c03020f010e030309060f130b0703050103020a08010e0d120e0118060b330405030a 72
    0x3081d0981000040a00041030010402d00c082140d4948004400008004015240e142c54215583d101d0038012401034940c0c22a02103403100040380010314110a0b600c0700e17101c8001c4070002d0000d01c49050800000050f00d42c0c0c084c0204a000255100c031402991011424102d4240c03424580ea4a83d0040344524460008080180d8400603042081d980c05c028043d03441000c8000030b1040c1c084100c0000c1d1a95440c1c45000140500411071900715038031402c1d071140c803544480c0840c0c1d91340382c0d40c20000e65500005102c078009500c1e04820742441c2c0c1001c0102c1c1d2288801c40000c200036129041c52080380d030401030112800c503450a26601c0003072030f4100200d0042d400c41d500452554191b004004000040d5030049405070716103c4082d491240100b03003261404044d050100c1420902c8454501070039841c44081615460b154811740124a0481160721003409604204590507420040c0985807031803041144504d2080700d6030038200703c0c02281c2245036841e8016120706003030361880400c1c50b08007420421 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 599661537 1250 599660287 599660291
    0x90c07050102070f1a09150a060801091a070e031b010c051020030403120e070b040308030a140f0f09100c05030a1b09060c02280e0c0f0d0b22 62
    0x418103000609100f51602d50408612545d50709000501c9590342c0c640000200c0e503083d20000003490200340b503201e0402404804001d20160055240c101d40800c00c8100e904000625003000c100c17544d00c01e5045986081c0040c00501c101050180400d0b00810304644641c10010310030f0260380020740c144402e01220700c1c0640081a0380c0e40c080300c92001d80664007160803200000b40100300200342c0c000c1c048654010074900000781d581d000000a410008290001400501c001500104101241c030080d031049600c3c11003040008299406146928000e80e014a510704941e000b01d0207204614455070303001f1130040c9c125488801c90010240030f903801056040c0118038040100300c605002401a080e00619003403d500e9030145191020f0070054983c0216800c000700d0700e0648046407a190446095009107a0303050307643c0303804800201c6612060740140001c8051000210741440d0b144015580c010b5505d00a0038246035041082c10020701550194542c8229009080350500780b00001d5043c000c11117a0b00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 599662787 1250 599661537 599661563
    0x14060412080714030907171b03030315012318011b080301180e07180b01020a0209070f0306080303090c01120b0a060507020301020909180d0e03030d0903090b040906090b0907080402090c0705010207 86
    0x1440c1c2319150300160740750081d0000c1080003000103616103ca188803400b42091240140780e0340000544011020440c480d42c80d00150003015985880f01488940c4800d03624407010800200310f81e401e00500141c000c01c114803c2c0014050801e03540b43c62082060358050006130080d081000383d10782206540000840d21000c0c0c0c5d80a85820785010781d2644103400c0c002049200e030720b54089a0500340080481d010401c0c03025141c0c5207036100f074004800925019086a40364102107032500d4464424250181c00f0888001040b039490f0307554020407800050007008074442510b01607082d511a80300d01c00c00c83c1c0c0f40d58204034014107540e605408a000d01d02c248545000b031243c03510094a8034003454000c4c2d051001400322030702c0a0350004202c685031713011440085001145032070281d03400c907441d4012a142010200f00807810740c1007584408200d03505040103220181080051000110064504070001488400050b015003000c607829a044024032003094074052146c0c0340c0c0c60032a0499403003141d1a05140360 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 599664037 1250 599662787 599662813
    0x60804020109051c06020a050f030f06121c0c020609190315021606020a0320090306070314072118113106031406041208071403090717 59
    0x11a0043c0c0002c1e5803044044a140d6440c9803003c2641e000101243c0d0001000b081148c420300690701c03119480310395192a030074a000311110a2600b150b0240c026403820042d5805904006a000107590340e019250b0b5901181c07903011034090a5146040e40c20000801c00403545072580c40200e00d030914440c410350441030547c9014001b15050148201d8801e00500c91410b600102003071000f803403940a0001070b615080000e0036000352420010303140d02c0c1d00080014011201a0038000c08540c0030031004d0354866a908101a002c65401c3c00308900c0c007001c1000000c075914018a1501400100614141c200402c00204002a65a1a50f040c0c0c01508200d00c101e04000c0240a40381247c2d0b012145000c80c1c0004101007040111408261031221200e04003143c41c03245142d0000c400303103800c10a8460308032203000885aa4440c01d5808850954a032605a49801d01c101401030160880740e4904074008a00d801d0144150000b800641050003600c1d0000740d10310030800c2013215100c2c80d030040e2100c0300d544a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 599665287 1250 599664037 599664047
    0x30b01031b050a030b0d021906030b09070e09040203150a021e0306010c2003060708150a0e010b0a02010f02070c0302030d02031201120f120908010e0c090c090d0c0608040201 76
    0x1501c081d5440302102890904660000161006081d6510703000968001c14070000350104840100a50083d40d0313182d0b10080801c850550809554031910140039810304d0030284500200c003160b4260000f520503110300058507003c600315802c98001403c880411070203040c041c401d00c100341e651010b41ca600040c403041c926109100c401c64614130a00c000d0841c544200080c11120400c900201030b242880bca0808145007103107125032408004c1c0440b0070070319240d44007a1030400c050391100c0840e80a40e080241500c0c0010268003a1102100d51140c540d10300758691146401c00700003e001c0d1b548031070307643c400680d0500c0644a094010407081031207918500605003810880c0207400300f19081048180100b000303510b400c50440782c0101249084410714209aa1130321040200280381c0a0485030421286a200281c0c070203940300c0c1002040072182860400360781c1c411080074260010000c0001032848841c01000d04002e41015182c0f14030451103903138442800616800080210303801c071043c0000d5580c0304e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 599666537 1250 599665287 599665301
    0xe2806051503090601150c0819030b06070201020a1401060509040b040b0106020601140d11090f1501031a040c03180602070b010b031512070f120506090606063007030b0103 75
    0x41e5291600d142800b110003900c4503814001c5c8141c1c03e07030303212600f1034041c4901c0d00c00700d15540203e54244c440300e00c2404d0000022607090004e0009050a20201e503c1c600b03a01104d80966058006209204860707546002c150311100e03662400d9503aa0700001076544900203e988220b10564503d006481d00e0300c1c181e101000182c0140c0d04650200700140140e4a000c8850140f01ea01111444503070101e5180021b0201c42c5400c1c03d64018154134140101008101541c6003c0d504400301d2402c3c1c94820070044080344c03141c4400341d8401a085a4100c083d0400b03a1044500044030b140c045100002c807200359991404010085800340c1d0300151391800c0c085003502803805401440c440078998106181c404c01e100c0244045e191044240c420003090f2000308011101c01000c5a0040024031030760380044111407540c95605841c98010040011103d41003c60924070405005040350300b09a0a0301d900304288a409510803104800d2030108100c4896048040b84070310020b503004244100381800050036240c507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 599667787 1250 599666537 599666569
    0x20301030618030f052802010b010e040209030c0918060106050c07060f0c20090c13050409020a150507150c11060408030106050a0e0a03051c180e280605 67
    0x21240a000001350f0109051046149901c1c1031500c403010a5400b0b0301012a501c41441032502d25511800542d4040d0000010000262a032070804920f501c180000c4c0d104468606a041d0004e400f003d00c98036082004e0754120551041060554012010352840c0403c2030b0001d0010607804542203d10036000c00100f0301801540c42c05400c4840e1080c0c004d40100d080503c002d1650081c00f00c92000d62003c4410603018038001071101c450703400e105c0c114526544c00705201404507584000045000c0c1054040c007115644e014010a118600d4404179409581e03514a4040802200b0030003031000c96143c00070799000c204025000100e50103044009000231030301107800030b0a0b421410400c000f280c24002564110380090a0040c1c5d50030000c1801c41d049000b503003007294444520980803050240000381c4480036602980c01c00c0842c00f44d42c90546007900390114100b0300303040c1ea00d01400091440c510303841c0c1001003499003411340c50b182a0b484002904000d01e40c164665500c05c100090710f07100d500302c1e1581003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 599669037 1250 599667787 599667821
    0xc07030f23060103030f1803030906110606060301060c0f060504150b10020d05220308031501020334060e060a06090209090a0c050c03120601080a0606020a0303091b090203010306 78
    0x440084140c0d00e880051201805009031190b02406e124003403000a8040302920424003c1641c0300d140180c2141e0346070207044002080c0651a9808400029006000e104000d01302e034150780c030782103086a41c400990400c03115003003012041c000050782d074040d0b20b0065104642d85000c0c012120030140468802c0d030380041c4111208000c0890f00e80c5c01003400c0851168a1800c2c5a45200c1d000303103158440d10b9039545021044d05c81c81c0000510a2101c003a500600340b00f26840e40030741c444401265240102e1107a01d05800c0c400c00305100c0c1d980002e030305034002c4250710000040403240f6202c11045441c5004055aa070b08428200041c541041c1700b030380b000c0c04503080111300380040301c00801d200d03031402407074640c0380c3d641c840a103203c0c94000d070140c401c840c0c40c00d07003141d50b61800343c00320102c403110a444450210329004045150510107005500c1501c04035802020790074800d450413405001008415240c0300421083c103100071882e5510035014002403000560b9075459840c000007101c1481d001c101f41c4d52 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 599670287 1250 599669037 599669093
    0x30f06010e040209010e19080307080306130b061b150c070b0a1107290c07030e0303032e03060e010204031a060a0510020f03030f01030201110604050d050705030c07030f 74
    0x10303030444400c40e035500065441c1c10182001c400c68205c2c03401d123908001600e204c0400c25208100d03868000b5846500300340c07036005440750305801003000e6644040401c0d91040342030140308500701154501140002907502190303007100325200e203c413040c0800e4442007040c400000b2080b050105194041d5044040a001003000f03010700303090034a541c018843c009000d00d00c0d07104000449124888035120360780f507042c0d03840c8840c02c083c2001101e41d0f0003484210049144a00c241120b03190210503a4451100304c80f9102a1380a0801441c3c0740c66030b020020413000305240008400704209100b008546080c180c0010303611811350a05c6a41c07044009030744100008101e0400c181a19014141800c8613416102c01528420707058082e801d00781c180075900035500c030220420101c000f8612040b8105c074002e0300c421900170420111503846180444028040b903001000740140e03d4410381c020a1380310701803403d5030708001c0210005400e280041d481900c1ca0702058030040180b1a1002040b07180502c02c42d0a000d02c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 599671537 1250 599670287 599670289
    0x15080609160909020105070c0605030910020307020a15150f0627090b2128030c120e060315190609060e040204030204020c1c020a022b08030f06010e040209 68
    0x1c82401d0184003442038a4600d400c0840e4011001c1c1c079000b5034400d02a14090703449500082243c0c00403607203500c89204d0740d108508c1d06d42051003203d0040950f036014048100880d1102d40038840c0b0048002c00c6942c0c0c0d03000c0c6820041801118401030300300c001600c90300d14a4200000c0505840450b100c0c038554003003501c202606000c3d1151000c8a62910000c40d064000100040405200500000694082500e0300e454100003013510000d01344200c039425a410020510741020400d14503008000c94241c4030100701040924003110422503003403420744c200e1255070700410340341e405c15030b0704103080041c3c244030840714640700100e1521240183e5245c034070f1030f01c0c0950080c5500c0b4540b10742428071107620704c44a40c580361501102c000d0358025005646d14950f1074003080d55442100a0302003502814220306128520208104451540040c441e4114403601080880151000c1ca0507825000301c40d5108400101141c020f54070070440103121003880d251440c009800c1001d0301030550310840c0304200451072 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 599672787 1250 599671537 599671573
    0xf0c040612060c0311070c05130501120b182a010203160b0a02040f06050309012406110c03070f0f0501081902160b0c090a0e0114060a05090415080609 66
    0x1075941102000c107003020040000d500414010241181c40400051240140904600701e0301c200ca00a0319040091030035040c04508a50080c09512403007102000850040f400300d80441e40c101d02e8252040580c00405210306180040d80c010591904002c0002804180e03a01003510410210038005140f4042407052202022400c1c128010811061b600201d0a403a003180c4c1a00c01800100c0800155641c0b5028060056001115030781d85035824890f0003400105443c044a41c400b5403030070b103026030300d0500b401503900d41302e1003008640c10f110710b801c2442d06640030018500148085c40c09134902904018641c1d0080c01141c11140c180548a4140610854040701d241d0340000000c1006032146504422044031184e42500030300241c3d550301c1845100c1d4801c0004150082080352040286640c50480c5903507928248030303281000e05d02100d2803259042150081c0341c6c956151900c2807501d02c14400150499200600e4103100a244520a000c1d41c081004902c0c3c1107104500280404001d44644141e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 599674037 1250 599672787 599672819
    0x90e0a02010815090a0921050d18170307120c080601110c04060e01050406050d020609190305031602011b0c0519090f0c090b0c06040201080c04170f0c0406 68
    0x810800c8400c0000c01c01c1c10360318040f491265006003800c10074100f6901c00000780201040545007140b40c25074450044905011890b181c1c034141d210141410340c04007186c80144140c41c2000d4039028055032290004001da518090405900100303d5187c0c1060f6500801b101800003400c09160b1a1503002034030785400c9442e42e0350044092800003084803400b4100303406d10b424080381942240c01e104000c106000e003a01380c1d90503624203071410043c540c0d40d1400c1110070480d200d00690005000c106d00440c1c1e09040308a84030020400f2481c100203540ca41d2142c0c69a804400f0511460100e040d0540441d80e000822417580b1030700852110b4500040e0b1140703048005a8819184120081c1450a014011400c2204010b0115020802c031082181140b01c01034050201c0c1c074000500c202d80c006c5030185000003607d882e42c8030700c0c0c000e1500e6521580159140300300a4003424002c613041c00002070f0100380b03841c145500c8041034086c00b414004250998a400c0c0b011403500e10441c10700800780520300340908440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 599675287 1250 599674037 599674039
    0x50a05090a0801020a1e09050d06111902010b10080a0b03030405030a0506150405010509070c15150e060402040305030a051e0708070c05040e030d09060209030703081c1a120115060e0307090e0a02 85
    0xa8001d0405203810340c01400e0f051001c0c154800081401c0450b00ce940c04011200200354009001147d140010480400440d20000000c907040001003031046081e0b61284070250400340c101c9140944880002346490b507000030440d1150310582c20050b200210314104060740f881035405200c5541400d00140701e82da00203080208008031002038400740070500c40300500c2060000e1081003540161600105442624080c8811aa0007030703002ca0b40604080c402c440850340c20001031030901a1740c0604480760351040a1040c00c000790303d4048909210036400900c0700a1090024507a43c0300306140209a610983c2e2025114510388060305452030004012030300061482200040c00601c0d51404a000740500d41126401d449450704c007008002d000c60003458a000d120030f8107005100548070341801e070380701d01c11b0420302400381405541c968242a6080c15051000c14000328504401c520300100c604215884a00010f003140091000c03820107020200140010750710500540804200003591440850002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 599676537 1250 599675287 599675299
    0x2071a040c171612020a1518090c0216051f0c081303050615010906051b100203060f0a080307170c0304060c11100807050a05090a0801020a1e0905 64
    0x501040001c00c904405482000001480308038442c12996480300d0f15401c07400000801c070700218080559021182401d54010889400103050090b1143e0a074102c1202509111142000d81d0482c02c1c604105d802406400b000040c0541c0940c0c802071505810381c0055840d108602000c0c0003684601c1c20103002e803141e400400c00f109011302001c0b10040c0300c038003004c0d05424011a805004140d20010801120300030f070220307901d41d04c0c0c02000d8400d1000c075620160101d811703054104800740c0500084d008040a440d079011910b0314641c440f6051100540e91b08200b071354004200680e038038191a007180000c605850340c0071a6410002c0140c0d8911940e40301501182d0f407043c0011001041070704680c48200c0e804103032902e56946100143c85812443e20407901c0c0015082d444980703003461007216806c2000b61380c9081c015140e1100942d12580002a030074100700c01005501016201d2211840c01000650001603803405038040082c6a10226a114a1f005042030311100c6050761001100c4181d42040b030362 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 599677787 1250 599676537 599676541
    0x6010f12020f04091b020706080c03010608220311060a0c050d051f03030305060f0906060a0f030b031501080106150804060e010f0f0b040c0e0d26120a0f02071a 70
    0x7001c0d05034056903001380c144500381100100f4100700c1d41c170f289413103240d80c1c0c08030364101da11303920255440401110310500f815030600040018510400711543c1007404d41d60105404c1079450580d6040031403002c0705401040c014801d0031050703c0b00700301700baa001c6203ca0041001240c1084000c0a0303100b18100012404e407a140132981c042146114800d139506002071385240c2503580c0c41d01a0107400102c80b00b900c10f02901c0c042c13600d10305101c4210780c85400001c04407031a0001040d026a01c9102c0c402825040640e121000600c64404100c46802c00501d543d0f0510b042d0f14001c4024256111900072071404003170381540840b03903078110f00040d4001d1b500210201752036100c100030b00c2c01810100505943c580c1440c0c101410200180d000d07030700b00b034002e239014081100880300c00c0d100400e4401d50541c10440c103640c07042c0444e0b1221010079020006034140035000c01d44041c0704000703030083c0d03980300160116441404100301d0680325007110240d18107015410a08141c544242c64401c01100124900e54840 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 599679037 1250 599677787 599677807
    0x6030c0901060807030e1501030f03120c0507020f04060e060108130c0902071407050a05120a062c0703050a0206030a02281101060509010b16050f0c040506010f1202 72
    0x450010a00a02054803541e0369640003000c05074155004c40100e841c10750145100c4402081403000f844901c2c2400c02c0907403960752800104001000300f1380c10050010340303040007214680102842140c07207030b80b440d0710740c4024010015100c4040c407007203105619080c010031001c3c0098001d107034415800d08010219030b8902c9811181d542203d400140060000030010543c1803403a800342c900780b8000c036103001c0d840d500d602c20141ea440307050041e43d0740a068940100101d2402e51120b5151010407000d440d81011165990419a101103a0204603c944150f40c2070448030818020748104840b031005184640c9142c072019182c41c030080000e40580c0c400000989054140d030100c0f41d4407200c0d4264103c42c1c509181030f00c8a600541424480000c4041e05008070603141402501c00f40d0764024411400c0b6482c2000f07038559035201d0350b00c0710000460786400c9808554240a034051190340e00d0042d007210003403441044201c03100240031505000c0740c0e81c1c210b50342c2544000f085216502a0000507a104610340c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 599680287 1250 599679037 599679043
    0x905070e100b0c0c1203310e280f02070c06080c19050a0c020d0c03062d02090a0b0414032b18180204150203030c0d05041a010e040201021b01020d080603 67
    0x116040104041d1f80e03002c0b5040314031080130903502c00c00f007805422040f62104001c47d1102401c1c0c030310200c494036010b14074190040f40960a03400c1c01168030001142e4068640078416600300038020b031303048465504200100c1b40c1244070590300c0b28211b200c0c140382c89018810188003a8a82c88000708026004c10301c0c7c81164006c1c4000003050341c000749162040301c4c8a20b09002c040d9907601007280c0840c00d0020785001801c2c1180c091101071820a10041c1c0c0c03216441c580c00081d041043c0080e40542c103c44002502d070341a000a1000e480c181c110001c420302d0072400d15180103d2103c000b0400c0100ca05088000b4584045480d10f01d4034516204078040608a8951174030070701c941004c14002d400b0100c000c81c0c0d82d5158000c1045640d051424805c55104e0341c0142e1b102d0000301c0300007890395810010400b03083e2455000c50340c41840740c0c0d4070161812158805417905442604a55030341e0031a84140f0040d1360f010090b4280c608000c0708440851200840000d490700301c402000428000c14501090703003036400b8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 599681537 1250 599680287 599680297
    0x5030703090602030c0903010b04060f0e0a0f141e0705070308040212030c03130f0303050405130e0610060e10051b0a0206032a070f11040905070e100b0c0c1203 70
    0x1010b800d5469060602030380c10310b075201003401c610039844c021804450323007086c1c00303070004480c249a0350561444c40c000740c06001d501c008003c0311300a55110310015026071030b40300d045118070261003001d849161a16a4200161031100400542e1510204016449501104031590640d040c6498600d40e00c0b20b10210384100e43c2120100b0040c040030a111000c05000000b414007070401c495103040050b540c0303e548050b096103000243c0040c000300820320140c10b020701803a441660100c3d001070b0310408030064a081c020140c0300c0e0407543d520039034104a85070b4028691800410b0403903029600e046140b5004d061031150780e0790b0700310200c0b40010001000000b0704c841034000341c024011680e83d2611484100410040f4045081701a07000c0300388502c1e03c125001943c401079800038003150000c205465500d44581c0c2461541e9000780c540d002c3c0c0e40000c1050100030024880e220780e05c4e145060260707900d511540c40b82c000c84903136507007400b609142e400d000038030010f41481500c051240da030354845007900b10720038 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 599682787 1250 599681537 599681543
    0x4080f090429011704020d0204020f07060513030809031201150221030609130506040f0f0f12021b030c0d260903010612110405091c03060e0610050403030503070309 72
    0x4140c121641288a038100070030b8001d0340e95030851240602a1102e01c0c0066501a4003d4a58030b001001810180d00130314610004100107420020260307110015600104d80e070781c00315046900c4000c101a041a061074010440102440c00c103280c902c8070f0703030501505111304480804a4084c03580e40381c0c000d110b152600840300385020f504608203404583e45034030959645001d100b04100180800034030441940174954000040e1800c3d071241d031140340c0e05000c800415a22601004444c0e800900500b0255041c6407044008001540c945c010290070400340d00c0603d4002000c204041c0b0391960080f50b40c011030201195027980180450605810406070100152020220389a80364020240e00018080d0007000710024031040d5214a1001006005c13904001c10740c0c4001e40751042140f034036400080d40081c100c000c40d110480502141070303c01c580b601455002c01d9442d0014000200b02200c01903110009031110440c0c5401008020420301c0b0303078480507040040100216000e54860740012414a030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 599684037 1250 599682787 599682821
    0x17070206131506092708040b0c030405040f0903030b040e030919090e0327090c030415020a120e060705030403050d090f0b06030c040b0307060f023c0604080f0904 71
    0x522825a10014502009105e02009012a42d160000d4403405503541315540301b1503413400c10385002c4080032580c10015001140c0d000c240008521501e9a22400d03190480201d00465a4403c5040103001c441c41c1d0140b00303001d9030410102100100000045071080328041c0c400240d1040ca84020598841c1030380c00c20f034101d0b810004804100b0b1000006018840e04550307007a075020823100c0c111783d10030f00c410b101c0c0d0b600716004000158181200e83c000e50780c050301175003056020740600d0f07040004036400300d0307603810204030000907000d94000f151043c002e1210f0000010205414012805001070100810003010400002a000c540140e56001403125952101340c1c800301c0c1e0b81500c2d10381c8010360700f2640c0500034402d48007401580d107084e003d2501c2c0c56002601900d06507050610486054003c0c01c18030056100b001d040e98030703480c40c2c13446c02c4034601e64036800c548a202e001504105805903800d0181040d034081c1081c0b202042034581210688030103400095504d4490501240240a6070f4216500103d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 599685287 1250 599684037 599684039
    0x406050a032306030f0c030c060d0209040f1a0105091f0c1203050a0c021c0806030a0b09010207050606060c07050d17031f06030207030206060d030c05070f0617070206131506 76
    0x11550101c40b602840003201170b2140308484100c40c540da06a031441603941a0701401d00c103070450a000d0000c1508041c000005490882080b000c030701503c440d00d184404495807002d8040c8040d0091390840c00400d824a006458201c0074000642007480031032070310007080109009a611540100550406194000c0384440c07003241c0000c001d0000d107000c40f00d4049840c01c140400202074070210f9092800300b0a5902441c1c805440d03801154544e8000b000b46426124070400c035004103107030300d01040c840c1020381c001603030f901000c1c03403c2d50070107002801d4580510700900c0602c00c00200410390105032002030712261144200d07820070704084514a0090808484000305201c080d1640c0840a0501220001d00e80801c941e48c10701242284195075010303005030482c4011800700d03d40449440c100c41c0c0603203401d10764403865803240d50908805078010301c000503010740c0c1000450741080c840d18900500d003054000c68940701d003010307441c3e240040003105642504c1800030100300004804807009400400200f02107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 599686537 1250 599685287 599685341
    0x100b03012a030507030e0a060515120309190e01030611070206190306210b1009060b0c060604090809060901022a18042301110a200703080406050a03 65
    0x85240301c00c200002418180014240380c003c0c050012200492402092640d0b4180c48801c010030020301070301f101c440c002380c0c0200b040e903500401d028080c06800156543e443c0a40401c140740020720b841c1d070000c1540d40c030100f00a01005a140d070449400c00c10200b0000030740190030000c1d1150441c001c0d44604041074492041401441e40e40c0399030510b4030f040201c1e58550200c0252503e0394198000200e061404840004000f6076800c2e800c46502c0c0405c02c0070945171420081a02c4050704a110901d40114a04080000c10480c294008038196400c00c5042000e0300c502115100c1c2d2204907024241c00070b4440056407080201d049104203403a54040c1016048052007100d000c6000784c04e00c23a002803090b262410462a90050103980c0c23003540d64159201c11126102141410050403025550f00c28080c0a8440c00c44020301d8810841d603036100c4540d00c071500d0245a1a0b5400c41c5414549c4039142c28170004035042c0407a800c4d1a46402d0a98070389004c4001140030703196614240c0700c9020595071072969 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 599687787 1250 599686537 599686601
    0x9160908031201031a010b0a0c060b1804120e0a150e120102040603060e060607030e01020a050f160801021801080a0f0603060f0507181203091d04140d02100b0301 71
    0x10f0f6485400c030394521340d6170009103d48000082c01340441a0070104001650280100340c40e5039130728412000803c031511800c0010b0f0302c401c1060354509607655114100020001d00960042509626040800929a0b03a03804070f01106118017920b034482ea5a4208120864060814281400401485810080d0b030a5000d40e02035003141c800d8101007401c0c41d5021445130500b60180d8447c1802a0200342000d480c0d13102101c12143c4000d0182c1503005170301c1c0d4280482c0d0207000c5003070342036528002403044604209124207001000e50280712903034410b00c8030104000580d01101c0000c6001d2030403000c0c03620342c1000403000700352506288403014038140001041081c030307800c280004140d00c0c404120355078070070905035804404000d011a10014100d010b00c9038030284042c40c2d08e050700038549400c0203901c8050200141c5810402c0769013a1454004000800c4144145046034a0b0888003a00041140d4207002c0c1d9185000f100e02305a00d6120190314000e40c40940c091f5200300484058407c2d20310100200c201 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 599689037 1250 599687787 599687789
    0x20d1e03022503030c08030a1b0804020a0f0e0a0e100c030e060c03060d0803130b071110150b0c0c0d03180e07120207020a0305070b04091a09160908031201 68
    0xc88440b041201c01482c00d00b007085841225055291205882c0b01c50350742900e0740d0300c0141000e0225940720202c01e2604905446901031000640b5001920700b8613004020303150301d15a00040b91494200400d01c03511180002e425080360445001080c104601d14015042211801c0c120b4055490010450490356158018410100070700094031a80d4035215144a41d5100880710036411030612075500e4001015000210f50151041f070300010401c0c082e5451034244401502c41d88002100c44942055260081c026418101c010130760030414030f81c1004010f03603010b51a00c6a01e0306160040f84050350300c00148510101e04000074010901c8481a1802a00041040120080d0b00909800115a0002d9200d20901a000c180c480103400c40c044151070002e58031000d4100d0f0001407000380040001d9080082d10080c04010700000d8a407400d081484046401414002c0b540d5206050021656262030000c95001050010f411341e03030484006007038883d03140d19803103030003948070001e621001c0e6403080050764 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 599690287 1250 599689037 599689063
    0x609070f0c230a1109061507050114010b070201030e010b1c0c05030d031b020f0c130b040c080105030c06040f060f05040314030316020120160b04140115080a020d1e0302 74
    0x60130200300002030085915007104c5154110f0405c0000841c60301d082c1014080551240d00082000ba41c04235050012641c2a03100c3c1c2034211000c62900215030f010b0240400b18a0361400130000c1c00700101c0021761504518103030301c10b200300c043d446c5c02c24401c8494404000e031402808440d003c601d40000280182000109608120708c1120f005450610100f8403907401c0e1629001003408040c11801c0010068451942c6606c4070380d5481a6400c0d52140d01601010341400c1d00d800a15600d0b1105142c2020000001c03184181400c000610620780d001200d20181c4600e85043c1d86100c0c0d440c3d03001d0f00d0310300c00c81c1c00c0500ba803c0340d00e106814440b4000700651044c0d1480c07503c003604005081d020703400ea0f0070200c115152500211241000b0355401e00c040c0808800900d501900c002441c0c030340c000e50400645003501c40800c100b03000301e0002e0090092284c4145141c0c5aa084103141609040c1c88400500000f449061030400d07010a10002083c2c207601644100c940c401c4020b12860042c1d6a0210740b210380b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 599691537 1250 599690287 599690303
    0x50a030e090f011509120c0306050c090d060203040203010b031606090501030e0d030c0203040914100503060f01060f03060e0705030f011e1208220e0609070f0c230a 72
    0x8541401d1440c0010b000380c64144294400e030342040c8144107000038800b0b1070800c00440420000741c0030380b941400300da098001c903a40c41e8040d046081150944100a0075081904c90401c070300f80e03403a1100221140b4458100c040140c4a803100d20000c2d015100010504d50701d4854801341e890720009030042c1c0700840f0842e49032001c00b83d50300c000650507210f103800c450030a90410102a824a402900117901d540500d10549203082e4036000304404903a400910b95100800500030862900340c0c1d840c070340c030103804104c00405a52404140e501e03001c2d48140210000c001c001c034110007005001760002030281c0200341050301185480c04006100c3d400c200d0b03481546068400000030101140103a5520441c6100201c81c01103080081c0181c5400103401c0840c0ca5070020030624808100350a511410914058800b410345458030402100380c04015004a01c01c1003000240025030350860840c2c400700e0a6820403803c0004a0705184445545a40c07840007400300303052001c00d04903030100d080c5c10020311850300c1d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 599692787 1250 599691537 599691557
    0xc030d0203402301050414150a0306060306120507060f03020d020403080c0d08060306150a031401021c050106020604060b190306020c010e0c03030a05070c090606051809240609030109050a03 83
    0x480c0b030f0385800c0003280490307820401401802107603446100560301c081c2c80780d01b52003a00301083c4920392025800c030001a640e031505210590f4140691402420000c4ca1005051751a0701e41d9900c50300c1900c00c28041c003103c203074816500b40c02501500d858016038202151203503503a0a0401041d4003505021029008131307454400900c1c0941c4805001d0000034000304516681e0500e074511048020031426030104032404000000365460800b0405d1049100000d40c9502d055441710710040c050103070310780c1028106030043c4101d6600180c15030344030b9044039010416130712050200310320600608000888014448000c0284030310b81e001000346901d608020031014203540b10140e143c082c10000554140c10821000582c54442d0018111039400b40d01a02100c0d80d40e6415901110103541c40b01020841c04610741510b04107104002c0041031b410340c0c04e107120f80b070401c00348003035281511051414042100d07805070241d11100280d4891400c0030b0300030410000d05017051581c508600c803003200010441d0f01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 599694037 1250 599692787 599692829
    0x103060512060a0507030e0708070e091b1003020d05071d0d0309030b07020102040e090a0210110c2107031104050603011107060b2704050c030d020340 66
    0x8080701c0305146680641240d85620030600302030200900300b8005c00d07880c1d4807180b0903004207000b96002031060304000e01d080b0f481e29202d00740c82c0c1300c000c1120045400500609000030074841c0b441c50801002c80300c003d9203803500071f000c1e4000d00481c42d019640034038010402031940d401240100d0b0101489044a460007281c0041080800003441c0c024000b8065070001c000140e803807030105801c540207000240c209a01c40a48448514080b00d9007010f661003c805001582007170300086078050103030700c2d02c41c0d48802ca40c07a080c0c0c0d5496001c180c5030700607015200c54000914000301d0300241d0a01c03003004c0d200e41c6c5559090020b03070300020b504110b100300d107001d0110300d45180503c26038009d6821511501c0c14880b107a200d100040c144411000e0b0001490032800a1005258510308000004506041d050307080508006d40f9141d41200d2140c06944412441507485400006841c84188801c2c01c0c9000503018090007103070301c0c055072003690002d00f900c2280c000380d250f00c0341050207403218002582540c5035001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 599695287 1250 599694037 599694049
    0x8041e0506091e070320120703060c23071a0c090102010e0601030f1412041d06030d050d0f06050a090e060a0b0604090e210301090608070f0e101a04030201030605 71
    0x5110102c3d15403080e181000001c00a01107803402101c4074141580b0103242e4004103100c5031740300a500c1c040d60008042482004803074070401941c00342a282c0406d2106480303010300c041d0700450381e0703040d4001c401240708400c0084100d0300e25440900c5900b800b0f894101251500c3e4950010034a50f405542440c00540400800043d40c1d41245d030008642401f040d070945800321031014076031002001e802032800d26000e203889a0014801405a501d604003c105461440e024008000c0c00c22031081d0042d1040d00d884c15402026102d20302c100c4500041c40c545600414030081106038001608030828210000750b0002e503500c0070802400ca6002c4c0c0329643c0d1808200c200300d81e034041e0900d80c07041003030005100c0c55029a001810308115081210320840382c0840c20720103600004504804880e0000040c001581c103030181030028205100204089403d1403010303209000f1170301400001910040000c0c901407001d000390b03801003001802d00c2d04c8045044000c2210341c0d0090005134040f90820000041c42c0c1054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 599696537 1250 599695287 599695333
    0xc0304020418051f021c091415010e090d020a0605270d020f0312070e04060914011401020703150b0109030c0e01030507050904200a17030408060c0909010608041e050609 74
    0xf8601030007120313003110046c1000301400c05c0142c4192502d03003c0c03204070324410860342d0044401c0a184041e1503140c100f21034030b0100014800c400070307007007a8030b41d4091a4000a01e60315903a0b0186012485684401200030b03d003042100301040e80d0f5a0421410301c0350000310716004190704503800d45900e050107103207080da244140480c440c0e14014003000070303159503c101c0040788454002000451855601d075484002d40b0f5045048070a00465000108100d008580c141088180c0038000f03070103554a9503c0340c4a8422030a441610072544907134034088143c2c4031304001c001071036000b0482000340342c540300343d20300b103040c2400200c500c0e100e6640c1c0420503143c0b014010780300386e600044824030614981000e500c0c5c0f00c10708250903000704202c8008254040c3c00c407042000d0300c4007a03004503191480d14105074544032002d80110700724a400c000c0301d4a20780b180c43d5064103503822410020215191440c1016002d07076601d40501131200c0000c0c03441c04001c00814864040d8500030100c0307440107845140f0302c03122001d03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 599697787 1250 599696537 599696557
    0xf020d050609061c060204030b01081b03060705070b091e100614060a0f0210020301121104150e070e0d1515060801270207030e0117010b030c0304020418051f02 70
    0x3100415044c0d41c3d4814240c42c041442810050305241d907a503200c4000e94020381091003160055200d403021000306040d00868a501240180042c1c105884090440c3c4a8004040d1054500701c000517042c45080200341100040c600c03200204200242c4810f40310454a02c000360518104040000c5c403205410284448580c003d11052404250350020f56280307948944003401c2d03003e10700700c80c07204012a101950081400042c1d0f180781580d5440c0c40c102d1003a2104401d07100f00d00d0700c8488404a84040089804d81e002c6180306510754030764080503500300a048404c0b5501452001d621010043d0120314044485100d540034018084100e031000000340085c0203113030004111f40300400030001344000c1d00f101c0740d4a0702e50703001c0e10507800321100f0180c0e0320023501030300820545143d034020f6503408041c2810444d000c01090703000754140703c410145844007400d8000c2c81c6801101003000d55841d64400c41c01c814215241440050a80c9819600d420030000701244044940c040051034542e103008403500028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 599699037 1250 599697787 599697799
    0xe070816060801080c0f09131703060a0603200f0c0604061a0111060f1b03010b0c06010f0b1602060f070b01060807211109090702100612020609220f020d05060906 71
    0x100e1b0400d00008100c0246540e500541520070000424035001042c507900c3c00045485540345492018401003410b00d60004c401c05180030412141d00c0b5101c0e18203012900780344605540d40f84a1074801200340100a000c00f0075001c2d81c801e00041101d940d100c0300c040e1102110703041e210032008006641400c100e02caa42ca181c0c121030001101002171003112340d800390040c08506850450500d141120f50006d81160060842c000780e0002c0910040183c4c500408601084901c00381c103201941c0442c1c062141e40710070145112040b141155110030956040b4038240700e1880c0c841200c0e0500304000d0900b80701e4207012440010106107090b1040350580040a40252261155003030036500d03030b00525008208000314001840001c0c01655460f140c40c3c01800e01c0d83c0204490144903400004546072a44000c0743c0d1000700c801d4500507243c5130242c3e000d600c01120b013080c0c1d040c0302042c0100780080314003155000600e48914808046400da0240c18122441001008180e45101c01e1040402003a038103280c2c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 599700287 1250 599699037 599699059
    0x2010f02071e15060b09031504050a14070e07050a03110a1b1112030406030e03131e08032b0e03090907030b0303070b0f0a05190e070816060801080c 65
    0x40102803144801d5116007140809019045003d03811500c29401000284000081122003854200031010072001c180000340b24a00313060390740c15501d1310420002000a09400c5500b900c001e4180304082c020700c021403c20302d00d403411490040c00d6034015401c03440070a180034544201c1898060070340d07111602d2a2030701510440c6021000354a80e40e460700859042140044000c0c1c00d0f1140c0c0c40741c00000440e18000c50301e8a09160740a41580d0f880380ea0024507500910041c441311498006620446211100e040c2500854401d59034070551960440070444c4030004800c0d80c08252404400b00c0401d080c1070b02403000d21001c52980640d42c9000c4d804403140e1062000c51078078030307000440d144c001255040010b03c4201480100c1d041d60400c0c441074071610140010442d200d8016075007140d004212401c104543c3c98500001065402040c8074221145c1e07032200780c1e000302d0004021031005890b00c178007121081c107001d6030b501151000902a440005501d40000540b20000140e590503c0c00000c6c0540048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 599701537 1250 599700287 599700323
    0x21908010f2f21090d0201020921190c091a0a0e0603240a050c0702090f0c0723010e0d0e04051909030f03050601050403030c120c0803010b070302010f0207 68
    0x2040496102c208001c0042100800b01c041c6025008440e940c10242c600c0113141c041d600e00d0604401e44124815079004102030100b80d96000200008010241c034009000402405801e10304420340600c19004006501d80105010381c81e500a8120391000205000e0005030301c214241d60260a5405a000014840148280300f6640e03d40e40d840500502165003002d44084020f03e80501450b8074020100c0341014880100c0140c018198032000b04003105140c22019408030b121420001c5c200c01c140c039007410114a044400c4811a0051074000401d048445400500c0034091100e000c003c0e1042c4d071800c01c2d0303010340c0000030071044800b0040d912030440c0000041e0a00c0301400c401440500b60301c008c44e1240a100c040d03803041c6c2c0740b038034000c1c0d581d000800081a000303412280003804e0740c1e052044c10300c01007001a40c050030b03125001da44000b10f0012070101410545501c081000004d040c17480100002c5610001d074230207018201d00940c02440030a440300408007c0784203201018248081d180504005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 599702787 1250 599701537 599701601
    0x50708071103100b0312030f040209151513080c0109030b070c12270b0f0c0c120604030e04060e071d060409060f0807060503070c0f021908010f 63
    0x800e00034000701042892000c0024100000e00d814115895aa8500c00070f0300d040800845e81d0b071781c042c42c1489155041100541c645003070003c10003032092110400180c0449480f0000841c205000707041030a02840080130113035650000003c0e84980e1404080000320544c00241901c0c0c004010313195102c0880c01c6441b003c0500000426401c24032106160a5002822240003042c1050312641d55441c0aa00440c0302e0540d0648003241405052070a001401b42507400b400b10780b0b02c1c007030758800b40751303118520315413141441e400303010b00c507404072001c400e03025032040200c2ca907441244a55504408641003400300b1080311200d000da0020ba050f64800564954059890000c0352044030030800341e14940340d40098075961081d085520001d031590402c0100c0241d403034a103400381550380f02809485042c0f500041441c04018036030740c10400481142c02c140040e041c0710300e40a64024080c802c1c1c0400c1e05120035a141c8143c41900b465619240044c80e60141e41d00c10076220550318948a0039000f03015983e001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 599704037 1250 599702787 599702797
    0xb030304120f0f150905010f0903050a0e012a0215070b180f060a0e0d020a0b0402220204030302070e0702010c09171204240212271002010e01061401050708 68
    0x94222044200202107420610107130800c2d50b4403000428580c07090f04c1c14501f5240d28450aa00d15410210700200080d08002941e1400303003946414203508801c140103c600b2010b000d41c1d400c14218080619800781080303010701501d14002d0b03521010802d101c40c04240d95100b80304019010384820030100f504040d44600814078038000c6030480b01e4074400d0202c001d0502e82c090303860b0b0150907901c0c1c42d41c130240f00c8103201080341c40035a400903103c484015101e41e0308ad110002c000a218440c218164113034031202005044241400c001e003103480d16100d290180d42c5420078003c442e401591383c13002030706240c07050250351800c0c446942d03010655480d201810340c4200d09148541c800e030080700070201c80c0b040b41d0000b6100a007150081c040704250205101c1170029200b103544011034209000c6034550074009000c8840300103640000e00070641b00d0040300c0341560501031195030b101e0308204640e4801581500704441c08c640741002005403030303510348003486031503180249503020402c1403040f400414800000741c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 599705287 1250 599704037 599704043
    0x103080715060308030a0f0507050705100b03030c100501060813021309231e01020a08241c030833032d060907060e28180b030304120f 59
    0x41900c2d0340301c0d5201a5030fa013084550003400b694640c040c041c04e13942405900d800c00c82c6814400e1503e82542c131202e4644401600da10003280e2036402e4440c0c1903c08108507400c0c0e959140503912540d440b01190b00240c0300030300c00d0320300091b103280208030a400f00c42c0d0426003a80d801042802c0720a6801c00d040083e0500d03140507204d0b0706040311100b2032144400c2c140038400040002500c012251303040079008422150440c00d059a1042c001e800c001b0f60401050364000e8079180e030700c003090032408210105001d02c1994050700503400b0740e49150001669900c160704d080c800d03100c6543e40c0c1e803040440780d12040e00c0445c85480c11070601281c4c40000c0b03403501035400444050706440500000000d803d0b07412824078055009030080d501c100c1e030030705001e214076900a10084c01601c20f0710b1401100030900c2f80c99521040c4181d00c444101c0c2e00220000c059040d41840009100c0710003560341c0c00680000c2c0180050400035802c02d04035a01602c0e000c021542a2109010290b00c924440d441d00d4118141d460301c12 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 599706537 1250 599705287 599705291
    0x10501031e05090c060d0e06010b0304031704170d052202090c1608161502040f0311130c02070501020d03110d0e0a0f1506060f0e01081005060403080d0606080103080715 74
    0xa1349132500c69400405066a05450125004250341281440c20354143c1c0044000a021710900c4006a80102c2501d9505464420401e45444908050481000140c00d81c4600040080ca0050700c901c40d03003145220b1068042041c404c0404400040d4241e001a80000c1d40040040d00181c00c100a1102800c110a40220441564261560380d40c2d210750107981c8100f100041111203008224030101d0b0340e80c03440c0c0108000d50410b444e000510120341041d0000401c2c65a4004034003070180c84c0c80107070030540120341c4414044c1d00c003240030203516606103004185c014001c100c21110b44034064040c603040019121800303803a02c03191040b020000d1100c00d031040a180104015074010680c194040c048860003030340515098155202a6800c464a0764407660034440d00406500c80c00350030481c41060f881c001c0c280b00c880755440d0304040980c00203e800c800d900600104002c01032141d13100c0681202d200170704080080e181c03165004d48548509102c014030104041006000040400318040c411810617000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 599707787 1250 599706537 599706553
    0x110a05101e0905031201051207090b01030b03011a030c0607030e0607020607200a09060b030f0408160f02100504050604060c050a0c090504060609022a12040e0f010501031e0509 77
    0x801082c1d80d020101030343e00303601c00300710081e070030358000700d51801007204944003d28803038200500c0d40c942080344180c6000682d034484542c5540d0082d046480684030040007003041d204142e251126a844182a16010344aa98450381003800d140c011104010f415480d11f02040d0000300400140d0fa019640c100c3e040403007400080d002400481c0074111707104070860013650400190003400340d22140b982c07059a1039030802408001201101048030f4003c0c80f5081091f00d6030751581016900d41c400d44205001a1403100042c0c4140016030b0b20200e451031089858000e0f640c042072003110309010b107000d2107a0005081200304a80c03070041c549211072911540a44045000030385404042e6021940910009034444080108102d501c3c8200000791a0589085003404041041261403003142284200358000844007000082020804902288081e0307903182d681e1364231078040c00364038035054440d02400c254410010527958001d002d6015107031500e1041c2180d0b003542200c5c2002600c3c0141400042d4090851 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 599709037 1250 599707787 599707841
    0x90c030309191208030f071701052e0c050c10020613030207030515160306080d030f15030f0b010f08030d111c1a18010e0714031501110a0510 62
    0x20500f0414000e4990030b0326894079a050041102c4d00070440000c1021035042c112110594184a6043d00c00668100c03c010304640768a24555030380040c140000c0220409c560f0041d91301001030f890b441c1c808c0055038034465068083c0300c050700f030141035540580c0101d400942c40f8502c510300d03620001e000b841215400b41c3c1da83c468030705100d98a0350311100300c0284010805017034164181c0744103547c0e50303190802115141800e80750300c030711070385172110b040644400c40761091901c903401180b00c48810a2502c1410356483c6492000c03498894001c03501140c2003400040c8500006400100b00c83e180e0003c1d51514400800540090004445100c0400000d0017811004100d56000c1008010301c3d07200041c0f0038200460030340c0c10036103030140345120704c0d0070140c000c503450740d0b40101604456884c000c2041d2912488401d4030003c50f140c95071052400040100700000080d514002c1130f603942a06c40b1044046609501900c1718201d003030140c030300d80c0040c880b00b09c0c10801d9840580000d42006003261650f071000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 599710287 1250 599709037 599709059
    0x31501080a0c050121050705120a060905130804030b0c0c010e06071d0f1c0b1f170a0b0a0e19050c040b0a060305070e040212040b090c03030919 63
    0x80c210350801e52103441c1907010402e1058254002d06000d007005d4545c91040e5098416004140919080b51503c40e00855940d42c010350948803031503130306c107009442440d04075259002404507224910000d400c11021a44844030f60581c8a01036070040c41d4945043d0030340d101c6950100020f40030040b00302080140c5c1c2000c060078480c0c0141d2482c108080c004c18100004020300a95a10b44004010a81441c2d00160396807056070381028450240d40da41400d6400d414000a91400c4070030244c200c41109041242d165a0031075400c4d4170502ea40704990001c4e841d580c110402c51805043c80542d80d00240800002c150804002d0354031280f19040450500840f041c21403e00814814172111080c640020700100302c0c0c1802548036140003600c0c104203040003031000415804e0780340b055500f41079841000c40d1300644508103140102c44c015100b59a02d0070b50003543c4030f105004079010f95070f91040344081080204045060030401e140100214100001c1508000c45484070319041080000c00d0000010641110 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 599711537 1250 599710287 599710289
    0x919030f0f09180c11240a150f03170a09050402072301090501240501110102130b0c010b030a1110020a14030403020108150d1e0c030813091103040b06031501 69
    0x800000c0340840b401c0c2c01c05460300550044a020981103068500d621029841c6c1010402000d0b20a46480703880741e00300c6030b00821142c0c0c2c55203005004120089000040014050105c0b4410040e180000030320381402d4012f801014007840c00505241c1c8100300c0e0385840c0d0068406980038001c0c8602c0e80c0f40190643e0b101018045100110f07944624484081c8a020720500c442c0390300c0400d03400701800ba034051501045443e4001c481c1440001c50340345000404c25030541c0c4a0f55040c0746102000380d219080c25005800000b01100d8660a00e07030052514200801d0202005500c1703422460340c040c2040400461800040d091030440c417030080d00c0c2c030200e40365184448054140350003840d56541540001881010000d264a20f01c0d074204038074000c0398581500ca0780c450b94200d800e44130703483c00040d10401420598000078142c03c108441c04403e200c40c400c0100f05540c00311b200803078059074503450340c010b071035040c040480d9a00060001501060061660f0707580240c004040d81c039000328140502c034031442c003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 599712787 1250 599711537 599711579
    0xc0c0d020c120f0c0d050a0614040204110901020a030509151308011107050a02090402011b0c06021e07151418040b04020325180305060919030f0f09 65
    0x12035010032007142054101c402c0b0811100d40a040009102c520040d551400740701c4240c012012840940184882805185403031640843c05118102004140d443c00c018160f07400d81c410740c60030f001050031002440c100d5694030b4060f00030342001610340d10240c8064000d0303443d82c0d4122915594501c00c800c0e8042c01050140c0f0503130305002c1c06038108540a030844415211044a0400801440000c01c000250130340d90b0541c12246030582c3c4c0d940d0310040318910324400c04141c07146a100c080004004c1c03880401d81c1551340b590300325081150b2105140300c030141e45180320310050300b003802c0078044840a00300c5c0b1808002d00d4100004070f416142c13400d40c2d20380e0010648200004040c000740e03141d840c0c6070041c4000d501c4120f50540c2181800055803803201000c80e000c440812038001110001405244003000350074405000d01b960075a0390408a4494508444e030b0420380c0501c107004102a100e03004803e07d13154141d6a101c114400802c02a01d480b4420000d42090082d90301c000200d04860125490790030b05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 599714037 1250 599712787 599712793
    0xb03090106050609030a17040f090e210d0f180309030c06050f0414040905030309010b1f020d050d0b2106060a03020f060a1b0303050115020d05120c0c0d02 68
    0x1912450060840e49503400142c8218420840c00702c05540000e80100071680061032404006407000043d4428800c66000c102d40c440000760004044495a0040000c10641020f840d002d55440700040030b0026801c1018003648828098941350690f01d83c840d5860380d040c140c00050580c0c000c10304a86548071081c0840004c1d4001c1021300c10045901c140c5030050072503050042c140260000807443c140518080c2481c030a16280c0c81c1076844c1c0d0b564003d003981c5a0443e0540b6603a00f05585428040d113485101980921090001c036112691310000305001d03614107a0262203140dc0c1c0f01c1e0101c41036407003441003040803902d403454011250380e0384406905480c003441d0101d0443d81030341d40090420f20003e0600b4862040003000f00b0168450403801b40081c01c04807007040d51040301000a036104400700030f09280400101444104164140d07000078140d6022a4070784150000c81c4204a0b07403540351110000005400307100d80d1450303011b00d40c42c840d00070014040d10743c10442c80768201c3c1d2901c4402058200107034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 599715287 1250 599714037 599714041
    0x1030b1e01020d030c02060c0a03141504060f2d0e01080a06060e070e06030a0f060902030708060d2f120106140102010908030f060613061e05030411190f0b03 69
    0x741c0c0400c001c400162483c142400a0044101c010391290801048488400383c000b40e5028118425403004605114100300541541018905079295010b0710707014134040c600d440b0010801d9103001081c14110f1340030001c600340761084040b82008000001e48802c000f102d88080c04191805810002c5003c0d05100d002080c050004e4180142500c084e580070b500e25585403000d0003001c03036001030707020481305040c0c0d40a0b58036102c000c0690000c000301007049807224a04400440c0c1150b00b030700118000e06081d0b594600075254502045180e8003020001030030606107107004415003100c3c0c001040c8006002c4030485c03440a1600200761604246200ca00813070b5511b00082c40b24500e2611090324160080c070003044406034983e034980c0984000f501c8003150810000020701541c0c0e8803c00c80f007400f03801d024850482c40d0303074a0025040d14642002c0f10090740041c0321076a00103106000340d0340f04036000310195205110220a00100e01c000d82410b05c00f062900b2404a582800c01e0341680040a40130041680d80c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 599716537 1250 599715287 599715289
    0x204090803070f09050103090809120f0109050a05010b040c080a05060102030922060f080a03180f0b03040b0c160605061503180712080f180d0f1110020d0e01030b1e 72
    0xd260130381c00580c180340c5041e0441000c1203c0105440e007401c0265100101100f64100623450803151207484403540d820043d03500200040455100300d02c0d0f00c034a009009403613440b030070441030745c1d50180601c0000d0350300d200242451040e03810880c0c0022040c01543e11b4108075034041008e510003200303980c4e4801410002d07100c01c0001031203041c00500044a80154207803c1415141d01d62894100141c100080800e804001401803108040100961004c07000c4480da240601007c541040358103551295449000800b80340343c0908079001c20b0301d02c1c51640601c0b01159107101c020310000c0d10701d60700041004e20b80e100c091401e200850048000008516024080b10002e518083c1c983d004116030a061a0303110001811040640f024104031103500303500c2c0c440c0185804410014070030030a50001c80f0006517418468014030f4942014001c1281482010300b150501240520714442c02005910500015a4036131003400082c0305880149800302e0302504410010f100403050218003007807410215003103892 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 599717787 1250 599716537 599716547
    0x703091e0315090308070c050705060307020706200a0308090a061a030d1103121905010f1a0a020715030908030901050f07091d190c081609050303070f0204090803070f 73
    0x5010140c1d42c140681030b140d660082c0b60034005031039a82840001c209090402005010b440050309000c3d000d0394032440c00110096445403075100e400c0c04121442c003a2006040600c070690004101800213101c1d200403545c0480d00752800401d07900d030f24051042c0307c0c0000303403040c050348c03100500052815103488845400c150400829664007c02e00c49655145440004040140d40402d00c51404503103850b42d80c00d10b001c0403201342c0b15141418500c0c180000c0b13891940d0304e510a0599218100b110a032a2154544460a108480790300c030142c0e00034041000700300c407142c503c088909a0b915000ca01c0000341d0740e448502d6001038815122070f075110350802030b0200311041c110b81d001070f0500e8500a42850840700c0b40e006030104115030030300840307800010800d01d8403103594180840e9401081000c1802d0040050078020180c403040c07405000f01c000c07811f4a82c42080e00c1000e8660083c00f951a102d000c0e51100780c040c40940b0200c1c1c006840f40b004901080b07646000d18451041c0c0e880c3c03291804605500100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 599719037 1250 599717787 599717813
    0x30a141204140c0316090203060a180903020d0c0f060b130606030506030d090f03080c1207060903171e0402030a0503120f0c03011d15150a020f071202060703091e03 72
    0x402944848075515200b4176007003c035021a4020300c40180d60f41c071900c01040496449420a10001c0042041030402c00c41c0e0360b01001ca01c9000c4da00740c80940f81e0780b4078101c2e03c007400340c1005002d01101403016808514240d0020715500c2e402001c488941ca8250981000d403a501d0b03110802095450f0b00704403c0782400d02c50030a64040a243c41e040c0103003070841e071900c1c0d80748600002d0942c1c500416004054031b410081010b0a001601c01c1645131801c0340b809a025289005049001410800c9418000b0002443c01402880401e4003022101140c603901070342550000e0041e41e00d407041e1b0b41041c01148040c00205440c0b030b540c800400350361800ca50f250040b284060000c0ca00c1c030b401000100549448032909444a80c0340d01842e210984420090740300a24080003010b500c10f4485400d0118180980700404000c0100d070242c4444040286410f62038907003a1041c10045620454400d00626003200240300c118481c0c20720305101501c1d1280d00c0c47e0041480180305010311504005c1c4140300010760708072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 599720287 1250 599719037 599719039
    0x30115121e051f02090a0b04081b031e070b03040804050907020d020d0503040f0212061e0609010b1c02040e04061a0d0b06060904320405030a141204140c 67
    0xd4407509540c1c2c1c030107555820180031208480345599001a4921050701100c003034003401010100c0c810789400d507036001c950261159a00320710402031000e6209600d01100884210b00401030701e0700811014407114202c20010001d42c103805003190214910b130b1503501070360040f1b01030300c9000c3e1241d0070803060100311750700a4564400d650140d008083e1040c0c0c0020300135201c2209103030464403511030b89007120b25402803d40095101c2c81c520038903819150f00003a680c0c803c800c0d0b00004500c0c1102200b414200798001d5580c9a00714403900e0041c0030340c01e48000106007588508018468000c0100740c42000ca820907048940c020340100144000d0041c54001e0741106c42c0344010044000400c0400503c40c800700c158014600c0c8401800114260f60303440568241c40d40180081c4400180c10115503a000551200c00070020310300e29203000c522203c01e40d150312481c0d1103002035140c180c2c1d4141c15201c0030509890400c00340010004d41365241001f10305c42d0b01452166072566403d6441c0c1c1501414450b40003641 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 599721537 1250 599720287 599720333
    0x13061209150b21100510030c33020a0506060d0c030206160206040305010605030c01090b09150d060f0e10031203020702130c020309030d030c02121e07240b060306060903011512 77
    0x381f0210703c0b01c840410403503050821891050800070031840144003030180000d0b9a140031268a8007003500852b10145c254030034010ba034a0b0b55511001c2050f40301c00c07544080c0c24040c030303000d00344014100140101454075081140580c0c80d0840e50014400b50b00a41040781c03543d444603000c019a0400b00900d603240c1c28242009460b4500301a050186401018042c6216070705603e82e442010741d0a400300c42c075280040109200541c2c45d4000140c40407044d104003880514403600086844e040403050714142c0303a02503d0300c3d41d12862100128040d401400b0b099a0100a8502103c00301c134051180800c101d0440e0040d41d2202850b1040605188030340030034606250504c0241210998003081140e10740c401024a44d49550b1005c0003d04614448681c01c0b91204000a160741481a078400442c0f455050351004001c020054105400360789400705059004402400416050320f0b10401a04103040d01800005820000c1d610540300d03080e283d0321402c450210000a0801c1c402c1c0400c2d64800300d0818080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 599722787 1250 599721537 599721539
    0xf2001031103071805041b2a200d1505240d1a0a05040212010207050a0f061803050901020c0a0e04020603180313061209150b21100510 59
    0x80072005101c000e1500c000c0180740d0a02d042c0510400b600c2d1000782070090300c208101030420b9009404012140320b460046001014241d481c601c50015405071440b040c00a1240548031341e8406403807800044900c01c50700b09411208150382c4850200103100e034003a1200440701e0100d590400d00701c480252140c0700c155041c0c3d040c1c10035000703d451a070101100c1a21219105129810f02c14a41040c51007283d104002820070300004101907084140554004c0b104904103000b05100385080b8864000c00030301c25040385001e8008646640c2c2c2c0600100d00900020410090704111405000c034050f0003103000c91004200700c0400d5038100a940c00303000c0c081e00d032441814101501d21074507020040c0300038031a44001001915840099240039038284815046075201c0780c01c44040c1e00a0009402190002440010180d80fa01407134000c0400c0341d508018a13841140c0c00303a030003002520b2840e5000d901300700c4d54401080314801e0000d01c0307800404070a028180460044a410381601c0b4064040c0700080c2100d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 599724037 1250 599722787 599722811
    0x109050a020315010f020c0405180c010f080a022b06030c0b090105090d060e0d020a0201030c0e100c080408070b1908060603070522090203160504061b0804030f200103 73
    0x50050010f0340c00d0a00710380314400580100d113460425590b8a420509040c2445800144aa10b601114420009031500d45e0b52010044511000278041800010040700214112280542c01042c60106900102e15000700d1700c0040a104209514400392040d5102410808c1c8030b00704800c0006041c1c041303580d0340707000f01150000b0164040d49010520078411240c601c000c02900d94042451080346405031281d5001455001e51100010101a4046400e01e11022142c500c17074140c0090151004000d480c0d000c03508001164a00314580d001c4803000c10402000c100c0301001c02c44400101003588110750750f0156901c01a82c94070165801c4024481c0c031009205641d0b803103409076644000d0720b282250b143c0d044051000000b82190740580c2c040c83e03071708001040005040d00114864400006065810b203842e0100303c41c2c6101b14810b10340024111404141c014070002d4004520f1070240301801d0400c0d46940354010340d80510582100e44004040b41480095042800c0300c152803400d080c01c103d4618600 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 599725287 1250 599724037 599724061
    0x120b031903140d0e0709050a02040f030f0302160b0d150b1c02070c06120e0706080109021308120c060a060e01141f0e1801081209010c06140109050a0203 67
    0x40c0101404041c4504524201c00c0e1429100195220001030061100040300030362500454002c44180c03a040900003540151103000311004c0f11117802c0072160891440c6c031801d01c103d00a00c022411401450040a221a1481c40a4002d4540a109143d58612484400040b00d01649901500d105550350402c040c00d512010748585e586d01ea031042450080c120310300c000038464030a009000b0b4a0712180494400d601214144008a2800c82000b8007101d1800035540d070b40c071074403c84c0c0002c0d50300c1006010381603541e00940a4401d0074040805c07225281d2100764100b1035048a01e40380680042500c100010f0100146038000303d14501c00c00400e42081800d05041c0e2050244020760082988445131640b103140c0e50010702c11200341500019012420000c0841c090100c140d4032030041042e41b1400820b403041458100e1b05040000d20071002c40c80055103039034000c0015641444810210300000c10f15034003c2c16101e040c030060701191981400003510407140040d142c185070610510400085000d52 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 599726537 1250 599725287 599725333
    0x72015060405092b0809010902130c05070c030f03143c03100807060e09191b030c1205070f110102090402070b010905010e0403020a030c021f120b03 65
    0x541e000b08440e5140c06005141000b009440384509008055500c418528031401420311010f503641d68045458924106090320080100a913101c940c1e03040101b16002e45610100128030542081da08080d417648640f103400080361700559500c418800c100013050381c0810309901d00003560380d981d400c101400d60030495100300c60925401008000e00c00118800303895005010707001507261101d640380b80c210401c0d0007249142c450706407144034503580461320a0003554030040f024405010101d980c0d0351810904449204104200b400f659189200d05111092652034850b1311020384000c20900310f1144001d043c8841006803814980c5804184100c441e031080c0c0c1070341c400e50580360001905c00e02c8809a40248165681642d0080c0300080e01001c211751241054100e03000c074603080000381c1e40d401403142c05450484000340160800c1c0704c0800001d01a00301c001c1aa800030b4042d0f0b6620800c4440d601d0381c0c0122215410114440384403c0b10316896038015001c3c040c100790050550f240d0100e410a90000d81 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 599727787 1250 599726537 599726539
    0x31502070506040b0910020c0f070b0c0c010518040c08090c0301051e10080304060306050102070803030c030610020f2406030a030f0f0221090a121115090907201506 72
    0x213010820300c1c202000728100d6019000011583d40303641c00c0343c207a501c103810780d4007030f0503405030850000b06c0d070702000d042d1003241c11003002808540d0b22010044031968810348000601c1007504921b440705403118440d51548450b01d48941c9a1810714059440c0361401070140e591081c1e05240c20072000212409050011042c0400d91940684605000da4510700c0305402104040c8030214000911640c5038000d4000c0312001c0e000c4d251407a403680200c944911080ba5440c1c00c1040800120f091307410070300c84105264003980b0580b010001608405810001c1c20802c1a51160b00b0b00710403940694800030b1039402c00030440082c0042044d65030007030141c19000d811081480f610801510701140280015040400f5082011012100c1d090b0700551581102c03003400e00400103284040b403510f0b05590b0010225400449000b000300040b010050b40c0c3c0120b50f51000c942e0810b000281090721420704c41c9001d140641c1b54994101e100c0410b1301014500901c50f45415400341e146c0c1c800ca450300b256856003000d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 599729037 1250 599727787 599727803
    0x141603050d0f0e030a0314060f061c0c12060509070c0b27030301060f110a0213090b0411100f20190303021c2d061a0403150207050604 59
    0x12075140d41c0c801070041c5440c0c0001c00e802d02110300c8019402000500301d050068400704042e6030150029200c0309402c45110342c03c00700c4d10f4a129224900100988004116030140510202ba642510802d940c0420900804240107488003802418030f0302680019140c180c64903169841c252a0003025680d0318800a044118140e020691901e144048010301960454003056191070741052240e0341c0c3c1c03003441040b0000c0d90844490b1135151184078140c140f030340c01c3e400505540f5025001c008000810f141c480c500541c6d5a5019030010320000c0e82c00384564091903412000300902010305c942c401c0300e44503030010096903050403840d0310342008003141405d0429884044c8503c00b903020383d15200e02ea0481e17144070204c21464608066041c0c00030a05032443ca9110780038003104c1c400b0b90b000d4134607000c031080c1c2c1e120307003218401c01c030b080d80d03501040e09803045406c0420f00d81c0c1d55403012403070354466010402600308002010300502128002c4144941300c0b2501c214036040b21078071003a8035510090700c000c094079 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 599730287 1250 599729037 599729047
    0x2a0d0b010e030c13150b0d18030504061404050904080904060503160306020d0e1606030e0d142a071d0c090111120a08270705061308030a0305060114160305 68
    0x365004170181e030004c01c6000c3d80e040d01c0301e41040751504264001801740703060041c00b22189081e901d56210003a407648402d070178203082c40d0003611241c90340b4a8880c02020140800545952040020783c0102d0040905035600d165000611041d901c0b00d03040b07603009601146400030561481c1c3d21400480390480e10061700c41e403010030308001500d0310744890aa07a101e41444042c0d03000c0c050228408840c0203032020040c4034003132811261035131030421a181c08501000400300110014000409540004d500700c040e07052501680901800d20034161801c541e80034403010f0101c640d074064804040c5a80b82003450342c519000000007806c1c802d502060341046903040325081c50301390402c40d0941031030081400030b440d12603028006080000c00c2b100b110418840e0a4100044e848110b13240c050311207160054440103090106014883e8400701c03a60303001000000001502040a20203080e030801c141d940401c41d400c01c82c00040035510074158481202800308901141a403c04881d0301300c071035160030401d40354 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 599731537 1250 599730287 599730319
    0x2d070c060204090204170618030a0309061d0f0106080604050706050c0a06090602120a0905060a180b0405010525082403010213061814092a0d0b010e030c 67
    0x29014941c0503203d0240041400315484483c2550700302c00e24403010454084e075031009040c860342c99a007203c0c92000d0300304020032015103129400080c3c42d103014120100346601060140c1d1445600240d85004942040e451450302000a0060f440100141001401241083c1e02c8903030721450244114024010009021420002d062106081e40781e0441d1040000361003030f003845e20107548000300c0c5034917543c41000001d016201503c00c8400051300040284850b640783c2481400800c040540090000381204c880e0001031110f4046510031840748002084500308031003001101c030417400c2c2440800d82c5000c0141405a40900e02d00d40c421000b00c031181c9848158640031012050030003000d83c255000040c1c2c400f00c0300207581b4540c219007a5550301124003298480303000b02c004103401007000003016003441d04020301d0315142043d04000c2c5610034600c0d1894070006030b1511451040302e42d0060101007400000d0b03814074030940a920704203003481c100e850180000070f501c40b948050392a1003422503410040709 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 599732787 1250 599731537 599731541
    0xf0a030b030303070e030c0603070c2013090501061224060f03050309090604060807090207140703050d020c10090501050d1b0c0615050306010b0a0203071a2d070c06 72
    0xc818014050ba0f50701d05010f01d00410446400e280c5a010744240d01d44020503080200c2101e2044480395240743d0303607003142da55942000d07160388a840c0c0301100c082c2c1121041d981d12200709040c0005110000380380070b070501e8041d00752030b040d500c140030100c0c40701403640101d00d4803401c074440900d801d20f54800300000440300900800c06500002e2802c40c0054000c0200311000000300b04044045034404040d503039450811041c0d51050003111129000001c0c00c200d002c030107070054001c45110381c0c196100a141402900d103014550750081c2d4131035110350a0500c517141c043c8441549140140c502c6415023100e04c0d8090204851403154504101c00000c1c45481c85203554460144071014080d500303c20002d004c8000c14040d18020300b900c01901e002d8414004041700d2140b801100d101901405c4660720f484403c0001e50091215034003540010400440003030041c0030303000040482c00d481c1c1c0e01281401000201d140c82000c0d2141c004c500c816261341340a121b40524507500003a24034001c0f00c468454079003680 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 599734037 1250 599732787 599732801
    0x904170309070e0a06061b02030c040e10050c041d0403170402010e040f020310240513031202150c16080306060f0c0c041103070909050c120f07030e120f0a03 69
    0xc0c900764041804104c0b9005d401c1881101c3c03c43c0c0d21490b04c1d0010034880d00740840301d04e0340250306d54040092403080d404c00c1c4d00304031003a02300313401070320040254000c0c840143e541c1114140c452900004007070142a85050703e04080d40d150124002943c60306540c064009101317110888040344e942d42c00036003103a00c501c40141d02920302400510581000d00e05410194000380d422062007841d41001007240d0f00281c5003c48042c442c0c40c0605140c031040740050352954482c0d00c80001c41c1c0c031306c1c90002c000318654200c4049001d070180e0007081100c1c800c1010305001c0740050403032114041c080110311003c44452240c0d00402e80c0000500d540c0e03880c1d8500050452150320701c625040d0401060480000b6004100e003004110305841c1840070b890080b041030701c02c1c0f004a850f140802c1d0f8401c42401702646176403140b13900000c1e00008504c2d10042601603004454203d0f1000d88204081d010058201ea050040b14680280342004000a1188640e0442540105001d074071000c60040b0b081c074615842a04250 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 599735287 1250 599734037 599734049
    0x5120402190b0c010b0a080c130506010c020d0503030114040209090601120b0409030323010320040902040e0c12120f1c0501081e15070318080a090e06090417030907 72
    0x15503d07030300381580f140a0701c404500148140d0f942e43c400211400082010b03158420300a10000500c0c0f4000161030003081c016007200d041200880c800380060710351500300f50000b4000c50040d51650725080c24002c142c0d0501c031b00c440c002d42c0180003041054454400c0d15801540c00d007042662446400741001c01400e401940340d0748981081c0343c1c3c10a064050b800654104803d12203840740700c4410a43c007901c80300a1100600380c1ea051001e64405003a1354014805590000348046100d00554001070305942800d206410660011040c1d03109030314000840150090040001c0d02078480d0307603800390407a8000c21514400201700094119440740301481b80401121401c141000996115006036986281c4800c04c0d02501e803100d84d5180e04400001540e840b040031322011500385644a000807009850900314542c1d080310490342040008507454044c0c0800f42c0a1780d20605487d02e004c40c1c000e1100c0004d04500e008480020070b01010500085e0704a0103030a50103c01a074945070b025a10385090880c0e4410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 599736537 1250 599735287 599735309
    0x9130f090b18060a050c0a111507090e06100210020703120c09081645050610030e03042d08010518010b0f1504090e0a060501060512040219 61
    0x20600c164400c02200110b45260111483c2c0d5442c0d8a0100c00c660060300c1001c1c20f45402c2c02400001803040c164148022012004e40300320351184c00c2c40110000040d9242d10201c0c0d0a24002c1c0300090b10f949a1070383c400d07000c8a0381c046510300014080d4036a001018617003d01d130780010794002410b0003110614003980c8040c0d005c0006600e0b40c0c0c40140140d0722400b0700d4084d409600d0b100c1e500b0382c00000c2c40b1001e440ca800010f0305400d100301001c0588500b003070a0b540002021f064134403108a4120b12114461017410008141d616100040214018841c0e50120a0501d0100c1340600480d000055609690401500d0700100c250800000345800c0740a0100c00403004e8100b02054601d03040d0815030007054445c440284111251100f0b900b40d070001003400e50040e5400950030031034039029460500301080140300a182588800c480700039214041d1882c00664040100c040400c11184182070040c01e00f031400a0804442c044011050400075101903c00c5801d02d8007100b0070014510040000c1101d0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 599737787 1250 599736537 599736541
    0x1060302060c070302031e06190908030a0c090b0c0606120c0310021201050909151021050f0708030a0c020a0513140708060d031b020d21020309130f090b 67
    0x1810b83d403a0f0160000f00e0107400383c040b00c104d43c24131685508102071010740c0540000c1c3d891580b8011a08280c1107810025901d03405410003080c204c000030350213800600c2d40441c20300f04008010780762058503484000028020019160503880104903030350800c00880c1d400007060724800129182a103001402940b50085d0302030204401081d500078003020003111a24580d50b0785e10410001e0440040f180d07070203950407141440d00c4c3e041e84891004c0d40030312200462038100c0d848a25110b000e40c0c00e414038040c0d10b0f000281c0340d0b0905c28200302d0700c1217030501c20000701000703030610414036224051024088180084071414134119590100000040c000107818800c7d404009120000a00505d03a000640328401e10003051407248900801e80c416000a4546008100310340c0c0c0c00c880a8108201c0c5840003050402c4020040c1c4c0e80441d0300303441c07a01907a1035100515a41c00300e44070300c031b1207090b004055600c20040b946580d21004141d03200d005540100190051814201c140a000740710002015000b5603c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 599739037 1250 599737787 599737807
    0xa03081b01060801060b120613180b06040506010e12030d0c091809020603060d021507051e0106350703200103050112060207030507051006030201030c02031c0e0106030206 75
    0x88039284004a610080c050345546030001c03401c0326543e000f51880540304104c1e031400e80f0b81d80c1c0701c41d0740c000c4070180130040522860080030040324030011030601e41000c914800028024281c1c070f060323000f02084408000a052000018005403121140341d0301601450100c204d16400500c00e0790b24844020009100d1840403400041641c01140512941180c1d1407074140040b8046115000750356034060912403454544804000c2d04902e6048100c1c0d010409010354461506064050101c0d94482d01c01880c1c03045422800c2245140c10a448a076203a16190f0f08104800d640106c034010700343c10410712601c0c070400450891000c1c061030b144145030f128459000040000c006c0c2120403500354000c1d813002c505850401101500c0c005c0c802c0010000c054070008010030b119500410b6460711a0030a613183c50b0007a51454204016805012503880d501d860170001e65030180075040e003104040c4080c628000d5000c42d0140070518640c2103010441c1d440d40c0840c0c021b2402d5000e803000d103800400107034881c04034036 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 599740287 1250 599739037 599739067
    0x309031416021305070914040e100617030309100504021f08100b0c12180a031401050a02090603190608101505060f04060e0d0b0c0318030c0309040b0a0308 68
    0x500101d000f03865807440322030501084e201e982e00400d510740e10304d06c0e120f1410340e01540203070786a4209035100f035403000e00104407201040810004620004007160091030220b000644480c540040b594681040040100136240401c07156000443e6440000b0107440d81c0c00400d91050444c1c00249404076007045c8202581e400140152040c04d02080c40c0103850307142c1a038030605002d00701000105500100c40c0c91808255034002c0d0203800101e01d1001045282c0c60300042c1024240d0780184c42d100080d25002d00c07015020f0060720303441a1002d030150301d40f14070a40401d010b0310000b410708c003600c1d610b0543c103152001c094004000601c0b1010442c0ca418100303c2090008200c00c1d00150024074110718002114100f510540358019a1007881c1c0381001e290950559030074409440440e0300c15503810b142000942c01e203009074001d030071142a160309d920340040c400020302481c80061315550b00c18042c11000080020440b01443d10030350700482c10a44850100b80d07a003485410080c8030203004104030800c4020a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 599741537 1250 599740287 599740327
    0x100f060302071713210c060810051c0303180506090c09060a0e16030f0612060e0a150b03030405060d02030619050607120e030a050c030c04060b03040303090314 70
    0x2000d040c031180c8a80f045054141c40350074485030316820720410410109584120010b0480381070440d5110b5000b40e81d50f031001e110083d0700700c4004030384e191040c440e401404d4030400e800340c4003e8a162015500648140c1c404d40d81582000701055110700249002c4100b201905080c140e000085981e18103061600c0c98448403900c0f20a4000c40440740002c180c2d20b84070b8014004c0f149804070000d2581c880100000003408950002014940c0710f00c107851810035179109580040041c01040d481200d4149000c005449107148000485d034803c00d00500401e50440d00a80c2801e424840011a40909004642140190343c849030b488080486c44120081c100e400540c41900100d68000400c800c0c4c5222003562030050003419004602030003c540069802d5200035554038080c1441c1d201d5140c41000030b0300d0f00186280482e21500950b40107500c50600304049001a0030448091002e0b81c10a22108a540402040a0304040e183c0c46030301c0c14903000340d895074201480c411189076100c031540000b01c003080714 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 599742787 1250 599741537 599741543
    0x50106030c0e24030405070e0f040c060201140604020903070e04060b0f011b0b041106070516090b060f0a0905090f16170402010e130606110615090f100f06030207 71
    0x58020b560310b140342100c070703c054400d0b6501041110300b510046039200b98000a204803407030b128041303011a15004081ca018403501d0b0084001c8564501440d201c1d0803501c0d5540400203580c14042c0c0303801d48050014100380e02c00415540141c840c002440000d1520b9020b030701c1855001409001c0c802481582d402a150074003040c3d0380105072080030401180c805569241c0c1c0110b407001664400002003c2d04981500300c0c2c001c0f601150486039010000707840d40d00200c0100d40590295501c0540302c004458090024811048100810151740000c600d40303215140c82c1250891000858508143c0a00302c0100a020301410b034107028075040ba0400f038800c00075600c2d8208032010084084101e4461000b9840362003060407040c0036503c560f4010b68000c10088900c5602c0440451140e1050f1003d2240100510171642c56100c8038070300d040201d0610002404920210a603007a5413038090700c0d000c0456404c490031182c2d000c995668800500c040d482d1035005000b40750f01d8240b0025016506401900c080c44c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 599744037 1250 599742787 599742797
    0xc0309031b130b0301110301060806030c01030b0315100f15021203040f060903031116030801120b37020a030f1401050d030c1e150e03030c0f0d050106030c 68
    0x3501803440300c90058104841544a602d10310441000d4505400c811101c070f80c05000429103141d031100704189034009801c10310004a15070100045442c0c20807044107603032420309003004803040b50404651107441c140440aa0b01b00d484d03002c503100c044804d042e00c0041404060002c1e150351583c0c020403184e18142c0e402d01c018445c0c074030849554600d55080341d0040c1c1e0b20000701c03110b1900d1940c6040107040e84200c02d4082c155030f2140c000c2a040360030003c200c1403040000800144000b46030140c0704150680203440c1c412000e0300c80000140c2405001d030781102c512040d000500455140141450b08698000e05001c0d007031620401c0d9510b4103802501c02011395031030910056112040c40340c00c66000318030550b2110031110040045040ca002ca0181081c001c2c40c21048611580d1154502141c250303c81e1030050300c540112000f0300c58008134a1402c1d0252030028000c0b82e80c0310020741e1307480c00b0141900606160010b4030101d0061090304407820542000002d220541e503880c07001c0d004040c0c1e13140d0500425 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 599745287 1250 599744037 599744053
    0xf0619090c0503040c080105190b01050c07090605150414010c1e08210601020a06020d061a03160f0c061503021f120204030302250e09030a1d0306060d020103110c030903 74
    0x2842c10f000c0c0910030101c4204c0101c071044c1022499002c0c14ac0e4420740c030b05201c401c02200c0780c20b103003d01001e00944a074284c0403501a241c082800201044e054940030520001c0c08184025480580340101e011001d20304600094140d00b004a40d4200c1d004e000e815100a4403101d4081003c0b41019140e600e4103010402c00e50605038566000c0540308440d0390780141c2180c031817000021401d83c003400420040420029080b91118040c9e0105040d000410144603008020088451403955004400d03662a2602502890350700101a040c0520b4510051104c0d407a600350341c8025400a141d0001150000c04c1d04091400030380c490059084042e4076003001070300854a032802c11005000701c0703044a5061b4014049041d0006400072103081d101012075030491468400140310003907042c4507010b0000b200240d070f515094120007800c1d5142c428410801000b520000c4c00c65a0740100f2190b501c480d082d07a205042426520049000f002100c0615503030420101e03410022030400000741032080e0099080303500e40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 599746537 1250 599745287 599745299
    0x6090616111503061207080f010902030606010e0a0e04020d0812040b1b040e180f0d1205040c03112206180e0c01181d1e0f0619090c0503040c 62
    0x921041403000e000b0040410201c0c5050a0844100043c000082c00f628050340d1125007503800d200d0803c4140300300d07a44418404007075141c1403000c10b07040b0a09080c0050b01030b185801040100d80644035001d182000c6c440003405540b250188500c0865000f5400c0783d84a0041820300d500030320955082e6a03500f0f00d00000f94040a0602c1c2c02c3c54820010705034181010b03e030482844080c3c000900150305070f1100003018031b480c1d0041007191a641140c2c0c000e010100310a0000510018441d4081e0040d10b083c0003d01000c80c0b020032080f82900e401961070903400c003156010600e084560031600f011861240b80c40d09000e40c40d42c2c04507058910a1204803003d181d214003c800b43c4511110150031500402c800d0341c115801110031034150401d22240500013940c0f00843d84c0350300011440085000f202070100083c29001000100020b44a410b001d0183c1c00d00901c8100200c2d0300920490003143c2003202e842c071140c94106224000d0403950380c20300180c0340040c0000c0c003641082e03408840705440711801240e1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 599747787 1250 599746537 599746549
    0x4060212070c1e02150a020d021b0d030509180405010501050a080313050f1201050c0a140a020d0e01090b04090f0506011d0609040f18020a0506180409020609061611 72
    0x4a2900981080e400841200da440c283d440c0307801c02240c2c0700d04800c01c0c2100f09072400c0050050b454458020f00380165001e50041c1c10301c881d100c081060003105005850301d40d80c481a406255540602c0d00301c3e25242c100340864681e6402d154904500e5401380d08001c1000300c150810340c1641c1003a110304041d141e07100c544075070360301840c03003c1ca05002e145141440141044001103d10480007440c004081c0c0042d0303419421124207940488641d040050040340b12038105003000d0080d81c0020384035241c5070070110000d44406901e207254040000e15542a40f1903031203410300308007801c5010754943e80c813179450065070007d181035101a032180f402c060010f0440e43c0160300014103000c05148060198842c5803c10900d6440000110341c45031341c811001200c9451880358050303070788803035142c000440b000c1e004001007180d9541c0502d00c41e000400c910354400b44400c01e81d24005e14181c4000c2880b842c180f0014402d8040e845049802c11404503a1082c01c80c465441c58014a01032400d0845440800c418044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 599749037 1250 599747787 599747807
    0xe0c010f02030a0507110315041a0f060102150a110406020a060606031b031e0c020c19060e0603040203030717070b010801050708041506050a06020327092202090406021207 75
    0xc0480c0c4d01388a52004120f80e00084184294010103458828980c0404952141000d82e002c2d01d408070214010074020170710050302c1d070700618401c3d0171246620f40640003e664242c1b05a00486200320403020035003200342500104d040102d0010400d0300c55482d200001e40d524000701003680c645080000005600340a48903000001d0b40c4030301c0300c6003d032996031025405044031601c148104002541d42c03400e8112288240c4030072180aa000e480d8812125040283c1003003411000c08080c110030004010f210b8101120a40c5c0e00d00c191820707a120303581c0f0700009041d40510b44010b8800310003202c1030f02c800c01c910002030240c10703c210010800c1da6243c6105a00300c41048a600c004502a2408075000c290b1270825801000c2d0248800302d101611140400d00407900b0b0b81c021009a44041290f00b10102c40801103110384450380b02103660f001c6500b0028003403020240044a019114200701c40700d20000c4d10340800c0054000d05107022904041c0303402d400a5201d102082c5290741420041107005104d509070b20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 599750287 1250 599749037 599749057
    0x212100f1107080a1d0d0804030311060907090e0a0c0627051806060904060b18180610090f140f0d050601030212031b010509011803170a020c010e0c010f0203 69
    0x207400c0c940d124200b0740d00c401c0341c415404200c0991384a50380043e0f50302000c06c1c9201d8400c0ba002c40d00d0b54613501e00034140180000c54020541c0064041085020001900c04101c54083c600401c5912103052050300b000308140000c1c1044490300c8000c108290000002032500c075680101c0c51403042046405a541121401242e03402682c001815403240c200c0d504044c0c001000405252400d0340c4040050103d4030968028040c880c1e011a08485060344600c003036428070000c1d140090000b4030720310140d00a0000510051040d20703c48180400c0340d10602081010302881103032400d8041e103880b400381d55400c0340740d4803502c20300f8010103e890743e0500540564582d0341c840014412a4219030800604c07100c21002d01007944010300801800c000081c092441000d03081000040e00e09200182c1c9080d130b003c00b1406180a4880b1060800195011003069800b4000d119840c0b4136131694a46080030b8815140328443e150308100700d11156070408101d00038400c400b62110090b41c070a00b40241c0e00c03802002062 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 599751537 1250 599750287 599750303
    0x1703010e01060e0f10030605150f07060207061b111e06130302010b032d03070302030a030903182705070c030e040b0303070803010f240c0212100f1107 66
    0x4010b424000e0800500400d002006004441507082c0412001140f210079440040d07200c0e04104503600340322041c1c40342450798803852890548605003a420910501c0e02c0100901c0c0d001414008bc840c5590203000c01024401c00d1001c0c1107680c0340c0050400f070440400030101e01034034850305011007401181c1c20650100b0400751606a40c0c03048900d48151f0707550415000e55481c0c1c0c0400c1c0c0959402d0040ca0b03600340c540f20004180b1411480e0400d820742c03040f50340c50111351007001550f020980010640710030000503d0017140d601d5062400701c400707000902d031907143c5a0f6148004602241c030800d2050544075031841c58504421030111180980d80259541c1d00072604c402108000f1034441e001c0b03020781c0d02c03000d44040389111111011034910350210500f80d5040305c011006008203044294032000600e08c4034050021011030140354028420070171200414000c1880c001d00440d02c41511001d003505002c4e00340e95000c0300210b25440584140141c0b001054a0100d404000519400984010507045150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 599752787 1250 599751537 599751539
    0xa080306060d060803130506090f04090f050d02071e060c02240d0b0f0907091203030207050313030507060509090a021b0a050d3207140a080a030c0302031308090d1407031703010e01 79
    0x41c80b004051100084d90044c282040d0dc01c013040042141c1d890001d401e81c001c0920601d442c401101621035403200f01c01e10707600c0540400c0020307448444080304070b4044032407104d4001c40f00001400d075405140551041c0e4008100b55000b060b140e4004030001c0000d5400b18001d40c99001009013105080740e0806c04a150344202303004100c0ca80750345001103413180c1030040c82e000d16912400c0c40d40c0c000103c01410f40c520240240100242804050300030511418514181001a800584420f10003424407400030f40c0407036200e01801988900b220410002ca0949600345024142075823a0500300c442440861108440342c00200c1007110402c0604440d070245114007032915402e02d45035800510706462241801d92034041d503000c01e005088102d48154090340e07482c0002803020301594401004001814414020001c103c0300c00e1381281c07a12548a01041e580382c18050002c3c02c1d070818804041c280c20103451503042c030b5000008620080c0c030f0007100340d50114040070041c4901440b003401a0440020a440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 599754037 1250 599752787 599752789
    0x111c1704050d051b0604061a030a0b0718090c08060103180f020d020102070518040203060a14040f020a0902161509150c1407120807110a080306060d060803130506090f 73
    0xc3c00391150080e060f0000c0c06180c004403840c0000c240c8040ea890b80da54511103c5230006a115520341c450b05030003608480c401900d900c0c07615280205404103111130385040300e40c0c003c0c090f060b11f8041c2590400800012100c40c10040400d0b0b002c896007030109180100c407084580600c3d482c840400e03805105004c8554065091010780e03540e04204a0540c4950702000c1095504e41020240c15440c0581d2503149242c14010075240c2030014010705100d910f40b00803504929210680d007a4050340100a41030820b06a2010410058080d40003840f007a01c0440c1c190040044081010030030b500070418203100c1e0340351031101000c039011984000d182c40103441a0b10a000e80d9a0480308261490f41400304003034020300c42c08a60340d4003050040320118080d010003810350b5089454180c1020392880c1c814032801282c800c00340d84460960002d0404040400010482e6480b84d085580e0584211405c4c44019900c044080ea603800c04110000e1542c032051001c1400d00f410401e80c0c8282c60000e00e02007160741e80030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 599755287 1250 599754037 599754047
    0x1107021504080d050a02010c03050103021008070210050c07061a0a1806080706030c032003010611190f051203060a050d02120a12021e030d0b01111c1704050d 69
    0x4035095a14841404005200b150601124251800030f0700c501e69115000c5800a00711107012109100b418581001407026031510786a000707a0109500342810541c82d850401d070324002c1a084442909030501c02081601203421014065062003000e040c44589042142c1654541c240307805144c0105450303000b0419007030800700000e80070907240d4001412039203c9d00344034208180c641101001c640c031080c44176105941449151400100400c10b0340c0c0f5500071107040b20041c401071107020308000b2000ca02969018003840001c4209103c0100a03842051624080c2c80b0040d031110140c40501031b50b50300e0014030400c1c1d400c41e40b16010040c8441407a5013410100540f0704540038040c3d81042c4180c0d0030300c11039a010014006d500d4000c81d007048a0294043c0000d00c0c00250700b12018440340c440501080d00070001050710051200010042039043d40e0380b004940c0c03e9a61407500300f00c0c0c41800020010012003885680d040e08403a81e030355105c030f0160b0201c98060001500c0c0104107a10019050101d24810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 599756537 1250 599755287 599755309
    0x11a0a080312130b0c090906090f0f072705030106060807050313030e03011d010f02040303020a120309170a17041a090c06040806060a080607051615020c0d08060301110702 75
    0x108050307070f143c3c1041da111072a2502d003c4550301900d0200041c034206524003c40b1031944100c0440b102c00d814a0400304071103020101410006007074040070080b448880c060820300e00700f500f141007419480700204402c3d01801d1076038840c507402175180540101d0b449215001c4a07100d1005a05e402d8070f5500c403800d1070900c4060568080d81017104101d00c81c10a90340a0160076079021101100103186002c280081d421030b18000b030003040483c8100400c20000f60007183e68028140c010042c00c0014101e10000c1e006800d4615004041c24403800006030400c030320038080c100004090351000940490801c2d10100c8040550700a041c031170042c80b9492402c86028682c40c1e200c80349000b914030f1880c0b088041101030708113810850558200750300300710b4513003032200c02c010080030900c0051006082c4220041d003640305444160540c0c0b1020108074040c844071460212007100a10001c544d20200204c52035142c9006000c0705001640b26400724055141c14000d1080c4440324500d02864020140e007040801000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 599757787 1250 599756537 599756551
    0x11160b06182e150302031609050d1e0c030b04060f1802090a1b0903050c040c140a050910120e0a03080a240305012705070501051c090302011a0a080312 66
    0x4280104140c0f02d84019100d1044860320b0260300c908080e45200e42180445001d0020003240d204100201d64407694824025a0001140c1c00c00d120a1100c0400e48441103038054607a1021040001c03c2090041d00e140c8600e0140008200070141001c820013540c01c10001c545101c9070381c412880c0985050f8109a811041c2d0072000074890202c0d241e0540a640300400c00b0700481d00b601c004009028050020700341d00300d811a410000980004070190055906100d41d05000c40045100c207806800350b412500b801e07070001c00001554141000041840c221514603201080c18254410301c0340c0c60014280300e502e5815290021280d40ba02030500041042e40002402110080c8604401d112040720700c40143d8091400451010710702c01148604600614841a905000c3d00c102c1000c100301090880c10b0b6082480c0c00c80c2d4034010021102050044461403900341860301d602d11003010380541c04400c0c1c1c040c005455940c4801d901d020490b40f85040d20415501e600108640c0301411101800d03582e00c002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 599759037 1250 599757787 599757871
    0x302030d0e060c1507030f020415050a050d0612060f021801030b010e1c0b0106090b1e070b0a0609110f0706091403030a06090f0e03070611160b0618 65
    0x10f00002d480c1c21445480c048a0150f107409100c1d469a250203580d10000c0130303c400707514080c40c00390724010120f90b1407208070410a010030950f900e140f0402c1100d00b541e55210301480443c0c0c9a18414404103507203032080702c00038600070081240064034001c5d40e0120f40450b100351604c50600e80150080c2140b030800301e040040d40301500c0c8865449864107040465050401c122111951820340149607060700040e080c8045404208190000c1d60200c3d0382008400c5ea2082c1c0b1200360709403507106801004001044807800302c041140003011540010b0071035210a10030301544014003400000b074843e291141c13003540010400034000c594143c01034200c00e40310303121441540c44000021411600103884d46034000f0385440301080103290b24081d01000180d01641000345114000b0784550b40c6c45400300082119403101020102c0194030401c1d80c0d00f01c01040c01302a2806402d20380300b8800c0208072151b61294180d0003422521611049105110701c003458905282c1c58000c030504041e1000500791480120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 599760287 1250 599759037 599759047
    0x804030806061e090f09100314011524091404110d051602010c0806060414121b01080109061a1b0307240c05091512041208100302030d0e06 61
    0xa80200001c0070031200030f10419446020b40c00c1040034603003203240d9240c89031094005010028450b81400170880c1da120381c0703090209031503008603401f50000d242650802c59512000007a003200341d040c170041c00ca0803000920740071020f41e03800362000310b00c1d8084c6000740f04401c0c401202500709035001c86009628844d000b4100000d00b50647e042e6a022100009205000e03d8940c003460740900400401070f41c10300b04401c052805201261f0710740118400d40e80a8010b40002014540340c0c5944500710080250a40c0c0f804002ca11100070703003000c0d4480d0b090000d01d078440001102c20351440782005a400080300401400c404001c011b40a42240d00c07042c0e0408807020200760649000c00c001c100651190ba0a180d11156403446203d04140e180d559005076810031240c0580d003640300c421107101c1d0004852041c060004845012024000c080359032080b442940144020305c458112801100c6d101a03440d2125a81c0740425003060080328400290103910020076240a00e0055008004e0004c015000f07500301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 599761537 1250 599760287 599760307
    0x9031e04030602040909150c0212091801060306140a030c0302061e03043c02041e06080304080105061e04020a1106040c062007030b0a061e051f080403080606 69
    0x30703803060344034840240d65041b2001c100884294400050001542c0c10040074010030300203500c80704840c089040070000010f07018003c0c0c2d02d41c0f03607001c0b01c6403004400d04450368442e00c0203001451039014000c3c49503484250b0603035510b4070541c0d407070607030740e101044402c0545941e01f0300c40300f9000b00316004400e8150076140c00c81020303d00050351285010380e40100484c200b081b01400c035020403502c5100903c2c11032840201001107101306000d0940d059900090300088140940c01014580e158009070a081200c0010004400400b50003640c4070380000308030540342c000c00c024801c07000000400b44070b80304a0810103980f5241d800f0346044000d03810645005850301e030165090140c203c50440e01c0700000034050040c00da21400c941071140d0300c0780480780d100501c080e00542e01c006c0d03827100901420141000401d914180c0e040300004200a00d001104802c105a100080c0300c035a020b100c0c01613251f00c0c091407c0c21040c02e8064140b1120352200c805e40d4030741341c0301180c5010000304100e801c003070100140c01507 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 599762787 1250 599761537 599761541
    0x6121502070809030a292a0c03180a0e04020109060509030309040c030c1d1e030f0102030412180f060c03170109060e0105030609031234021509031e040306 68
    0x1205100c0c0c10313140050b040c9805006a603040040041400e100c146d41000031100810300109044041010303194140c4400011541d0941710b82000c080b0030740401b0401d80070a8045400c0008908400c4514507170b031a07141c0b50140240e810446010b8000b0300e212000700074560081c1d004240020000c0d09586c40d0500700e0011805644901c41c02d107002a42d14051000d44560082a0121500f055461f01540d0306c0d50f0000104030481c00300f150841c2c01d0300d0241c40c0495690070880f034804080200002e5440b8906030034400c03a22006c80c031184000c0b501c400c0602d5182d01d2032102e00c40c10380d0f41340000c54440b1810047c3c2104d20050200080341172010170211410691802c0c00e40500810003c0300210300181001030740080c101c0181c1c03010b80246d08c075030280038010700c021040e02c004840303034403070b1030351542e0780500070610745118480381510b40c000c440d10604694565800500c01840d1602200c0301075502c4100c91824803001c9400b400203400c00c1c482c04a003545440001c03a03e4042d62640700381020345985940301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 599764037 1250 599762787 599762803
    0x60306040b1f0302061b0f0d20070e0c070302060108060f04170c0109060b040f09080708210c0d051e06060306040906062d030f06090812040b0603010612150207080903 73
    0x1c94400034072607401d1b031078808102c140d1448172082c000e072540e02194500580103a103001403094410304d10582020a8070010403101006008400300500a4202001d01e080140d010480980050050100114400c08005811402880780301d41d08640380d51180c655020621300b50071644480761040283e140303400c009002c3ea8458030b004440003e1403083d0401040704584c894108aa4a40c1c2000d00020208070351000b074541d495004140d8507a580c01c000341d0070041c1c908405900200401c02010300c40c0e040c00f00806045500c1c00c0c107204010300e4850240340d81280301d5540000c0c0307904640000281b840c1c106030b8080c40d00980301400106800465a0301c1800303550750740d0804502c00f003010415070a400b04c84090200001c00070b035406003c090035a19003048044403450701904264564050000f0400003c0403034041c12240c0c00800081e04152070525a00c42040d60341a100350b00301200820701041c1c40180100450340071401c40c01290302ea602e0031010350003003002904d49000c18000442d450700e007880068 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 599765287 1250 599764037 599764057
    0x106080c160303110a17090c01120c0201060815010602010507080606070609030e0433030317060d060603030206150603240a0302041e0507140403141c050909060306040b1f030206 78
    0x100c000f40b0b01b40c0034013102240091442c1441d81c81119140c103540d0300401500408030000e40c0102d0000103030035050307015080d07590013000640310b0008140c4445e19100001c1d411394019030f00034002e0b81c070b4844040354400e5040e03951560003982000080002882135110702c8000340b0074101a60603040541c000f40c211801c103415050421083c1c0110700b614609020715400652a003505a94101d007035880c010150b04680c0d1459115292120100f102940ca84043c000010350085007400340d55180c4c03500a440e1502030b10070fa242440a01404000341ca050002e491045603040c5010a01c480010341c5010813007542d100c116045943c0c040d020015072910f0103a105120300c44100c000ca803100c44031116084410003424801001140c0a2411768041e0031012202140d4200e40e40c4440d804840c00b02908083d18071903051035440070f0b02c180b030210581200280007600750440d00c8021558401d428541c880d0000c41d00200050b07040000580c04400d0118100c02e18201c034410074040f1500c0b0342c0411402d5222910030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 599766537 1250 599765287 599765297
    0xc0801020406090806040c051212030103120806041b0c06020f0301032603010806070f020f10151403061b04080d05031503010b0906090702010b060304080a080106080c160303110a 78
    0x5101d0b240c3c11480c40c3c401016600d004242918103903c482c003104601e402440d1090001c60050103044100700140c05000c0c0d0514029a40e9503980c0c5040030702d01c8002403101d0702051751000010440c1c981032154588081140da174822940c404000101c40120712582c08070703601a802d001401c0b1103403030400a14061840303600385800004000b8244d181d2251092040202d46908000501c10300300007003130380c80e080415800d010a04c4107107a00180c0c2046400104004e0500c070b00c130b0844400c0b9030240c2103200d002c481030000b0203005071200c1030032034a915485d9503036415510040200302d00105400b092280b00d0703440c041e0581071a0f101c2d000c00f402d0a229110541c0000c1010041c00280c0c04e203102d03030300380d83c80c5d088008100304032800e00420022000200602c1c030a10354140064009030003900042032020004204550b2458a803900c214190880070700400050301c100008100a400f07501e5442c00f8101c0951070904102c0242d407103d0311010301c4a421402c043d00d50100302c00c01c24180020b400b1082041d214 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 599767787 1250 599766537 599766539
    0x6050c240f0606070f0f080d0c0c02010e040905071502070b0301030b071d0306161b0803160503010501080109021c020409050612010204150e0406030f030c05150606041806030c08010204 81
    0x10800610300007409903842050b0400c904c03000101102e00c6056a680d01c000c040306050a01c0c2003119050282001c8803503510f00702a01c110300a640715054aa00f14401d1300e42040060a040a01046514040e8018101e40c010801884461900c20113043d0b031b00792905c101e0701c2107074680380c1c80f0f541d03600281e1003100c0c00070380e01701408038068008048400c0d00199070700d40c0c105814944e0010ba501d1401810001d09030114241d034010729845140402c1d00c1004003c00c40d0703080c104500d00840d0740c2c0d00c21100b02c80c00c034518140740c2c00c0c80c1d4810b100f105d0481d24160b40b400040d03400d220400000354446050b000b10204c3c071200d01c000080003800070703000070032080c4800a8549424414081030300110001e0301c80b01c4e44100001d000003000180c0903c00190946040040035200c580807070020300c0240c00203016840319400fa08201540010360000031441003003991412400d6142d00c2401d401c083d18240c3e440b090900080c004800d0704d41c400305d503884040f44040381d004d503280c480c1e121021164108901d0b076500018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 599769037 1250 599767787 599767801
    0xd0b13020a06022a0a0b071a2a070c031212050c0301050103142205070513050907060807080c07050118050f01150b0702060c10020d060f0509090706050c24 68
    0x2c4840c0c1d4001103088031401450310710b0010f80c06003524040c085c1d1345400806c7d131000348103000b04003054142401051101905001845c04910400c0a02c00010304d9200103454041d113080360f090320001030f8040c1b0040d001c40d04550340c800b089884003072000104140d01012508100300c902031303a40145111046c203039483d41840c00050544e845280310001205544092200e00f09907a03100e05844a441030600b42184c176145042c60510070706c1c0d07204542c040a8101424815443c0742d102602070b40b658003c8400d190f40e01d01c03050f12845d100329842d801244138440040c0c0c0400842000f0407141d4420000000d507000c80440034481e5030072030403003075406070b00100b040180b4a0091081c9040400321200c001c0400d460404081c45912480c00c00901440c40440c0102034910100014145544c2d101025501c810b284d11801004006030b129658801c00384107030008140c1016110300303001c0c40e03040000d000b029080c0030301620544c0c402c20032030001e441903056240700c2c0c04401d528100c60002c0d107102c02c40300e400d0001e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 599770287 1250 599769037 599769073
    0x90c0906030207030801140d24060f030503090405100806040f030f0527010207082a041e1a0a0f080601050109230d0209151008060d0b13020a0602 64
    0x280100d001e0501c1001030f100802c0c0c0010b00c2c14110b401400701a030710040d4040110b6081c0845001c010000040000d2480e1001000c01a2402036105148c0401c4000c4e40c42c802050b0340011440040c4c1142c10030041d018450402d0341210b98043d6440580040c0c0390759981100c2d14000b42200d00762410806442164101980404031644003412841c00604254465005210710004541c5900c0710001720740c2a050103034001d001c04002800f40303034261404411060111881030b000700d91601c0401c05280b079000f180746130900c29070300d4a094415010302d05600c10181a40205042c2e40c2d0540403940c4000090700036952506640081e02010341c503c6c0030203242c00551b601e07161060708102d050210010041c44100317821140d00d001c034414120410075600c040800701d0b07040850801c001c0e400290b02001c000c40c0148501c140d0645542c181c42044201c504600200c034462000e03901c07944d0002c01c014184e0041520491820b42107401c0c0151118802055030001d502d07080c0c1a8480b00150300170700c101c100b802100d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 599771537 1250 599770287 599770289
    0x20f130b07030201050a0225021206010602100c0305040305030604020d090c0909020301060911030c0d1514030f1501090906060e041b06050412080309010e010608010e070b0f070f05120301090c09 85
    0xb04066007009101c0c8500c10307580e032200003032385a094840003642080d0342c0c1e032000a5610080c040c0075070302103503103d100003915040081c6030075a460b41000c00c6420550b100b442110711860301592201d0070764942c0d404100203036010340407203d000da44920100c004281445842c90013462101d41c002000070080c0f0506007954426402038040c540303000c007c0a0302880b05421603901c00b2842c40070740e03601c2441203103080040c9811503802050001c01e40d0b010940c0c0168800d00b00072000120704031003102ea8482c040343d90b1002d07c5220b00b1410a40c000c0100400a1203420800d1140d2090001142154494041c41c08040040701c00b40c81c0b03052042c105040c414251030b50360b400b8040e180340051509040c205070040307001c020000148000800800511004000c1d071181c402e9040c0c440c000d111282d0380d101400c1c0a0088010800080d00805200040e0000c2001c212134001c500010118242265500e40812400c0841020750302c0340102001c100700e0541d881c00540c00303429026070000e080151907500401680305 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 599772787 1250 599771537 599771551
    0x4090e0307080a03020f04090c050733020c010e031c06050603220f050607090f060f02190201091205060109050105010f120c022d0606030106060909020f130b0703020105 74
    0x10429440441c1140c0210352044a150601599542c85903154043c5840b1302c0d44441403142c49e240d001114968440e00800700c2c1402100030582103030301800792a900c00910032403041d5100540d50102103241203a000790029074200000000e8503140c0e14806c03411a4402c9201009110890490701503102e44c9210708000341000361401821443c01e107007000d40040214031800c001c00d4084104004000d031030802c50007441e83c013205032a09403d040c41d018110040501031050504410720300070440703e20500131b08041c00856030051000350f100e251b54408110035030005034100180e128010545500d00070035a101e070352085005008540c50059013900729070068206a0410082c100791650b41540196140c41d0208030a900140c01010000161324101a40c5884018800c003840354440340d0800341d111900b04049002960030300e58459003007500300c42d4030340250000700c1c051010a1104030300541c09800c80821180002d4030381581c000145000c6a000c0c0d0001402103000a201c00c20540e0a01641d6003240c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 599774037 1250 599772787 599772793
    0xe0618010b0a1e15020102030601094106030718081506090a0b0405090304062006270a0f1203051b0c120a030e2a0108090f100204090e 59
    0x100401c00102c0c0382907148601d4a441c039056064100c850180c0c184840189180c10110084510b01c80019000c0d4004940c0607000c919041c200081c0c0804140542c45050005010b000b00c0216524944c052400d02e00c040e03860b42044541c58885075100e6000860080282c0d072110102088118161620b520407030300030482c140c01606880c80c03080d810100d2642c10880c1203880010a80d90a0610bd008280d00284981e0190422050080c1c50343e01000070419580c0742c2d9500c0c01e000c020a00039190dc000802468001540488000340e00c50892018245080d64111010035401c508209150304d480045082941c0308403540010000b003150644401998040900f01807010346050b407608045600c811506110300200005c80780440310b0180420f0300a540401e84594544203007070700040081c0b60701d160424480c4145189104400c0e86c501c140ca002d9088480240c0c40c1d4608000110b54540000e448040c452246d613150b0110040d003071043c2c01000051000041e200ca1406c4500c600f950640c04417000c580d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 599775287 1250 599774037 599774051
    0x203060912070609020f0310020301170318010f090305070b0307110d200102070c090203060f060f03072d020f1e12090f0a0f0315020c0d0f02100e061801 67
    0xe4000700a48804681002e00065400030a0001c141522550030346e9a9040c003a603c0c02400042030b42d0f015605a541d8501d03400c1d50340014400c0686d884c80303400c4062001d040300b4200c040b025807060b10103c2900390f903450b204800560705c6d82d42c1460400c0030f4003d801650004001c04c14155441285400d09413100390081115148e138903000b5103040400d414030a103103c0328404005104200350111441d440e40600b5010300d80e50740300101c030020340094031464815820001191070a2820800343d03510b8550780b00442e480c54480c0f42090700c1d1110b0701820001d0f0540103045901301d80a11440d0a000b8811036005483c2290201c1600d50900a05800107040083c0f90501c4180110b4006846040c2c1403800710510b40d11942c0a0000700341481d51440700e42c3c0141c0140d4085810000d01100da42128458420418814100c400d410140e01940c20a0035041d8858540001c0ba60301c50350510800c1e9146c1c1c010b032000c00106502e0001911980604542e4070340c8808180055402580902007200030071400800c904 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 599776537 1250 599775287 599775313
    0x60f04151103040f0309120602070614010e011206110f0706111c0510030f0318060509130b012703140a030915022404060b030d0e01050a02010e070f0302030609 70
    0x20b010140015100c0001041c125007011b001c1c80110000c0c25002c549444048014908100a54840e01040700e80501305560b06000380001d9514906030360311803110721044e0f801c082021400f1810b44406980e0303103454102803404002000010120009129070f65561038104c2e00301102942c451400c41041c81c81d007044030541c1005066107802000d20130020201c0d603a1110800301e6903620b010740002d01402c0e8048401400c160b040610300c40e03181c1c04a60700020702076940005031854000e583e00e50741c020304408400000c2c21103d0b84244040c00d070504003424113003400117100090940c0d001c200c01c07200c010742900b4400d10148046a0104494841c000c0c1200c444079a0020a510352600c142185615500117100d8901e0003808045206203454505c14100742010610908001060b1029100c05203401c4c54130140342000303d003c2d03007004501d403901040d04142c034004403016408a2042000c6559411030792803594001d1148a0040481182d00b0710064254010907080c81c1d000b802442150381302ca0000c0f050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 599777787 1250 599776537 599776571
    0x15041d01180b01030902030303011e090603110603090a1a0a0e03070515060612041511190f030e150703140708060f010306240e060901090314010e060f0415 68
    0x2075540c50034404507000003001c00503005000c14000003503142c00301200208104440c0c01d03040300340c04c4002d8041c44569940310700e0041211510302010b8a56108030002e4405400c24000a41c0c1042c405811244501100d894100d030f040c50880148042c2e0010005001c5003c00301d01440654070b0008001d180340c0b80e619501d40e80c1d07032000b51008060b19000703040000d1184d6100826581c007c007500d9002d0360303035103001d00e003024440806085a1041e0761402d005001c00e00041c2d4162400242c0a15181d55001c90070b44041e42c5a2191041800405444000d140300c2c4103028490049081c1d480d484000803414001d8010342550080e04035a00e0541c0e03420200000700e90f0000c150b907002001900c000f0892003500e0300407030140099401c107104d207105d8450202c481410511444803440815074134070002da010101041410311507041c6507400100000e805001280403c0c081146e145c048100002d00b80c002100181c0c202501110019070100808081200f48a0801c07200e20760402c0060b400c0140002e58955006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 599779037 1250 599777787 599777819
    0xa200a05040506210109021e010f0305061f02060f0a050f160c1a040b0a0c0906050f070b0403020d030b2709010e01180201120b010c020d03090515041d01 67
    0x48100d0b1100d000c50071a0300c804c0011050135190400107000040102100360180011010483c0035800c6070f28062807884c0c814005140c0010161744100711440b00c12811400383c0400380940d0381c0f005000325010308107032010b0441c61701e00005401030010b41c41c0403603580303000c400014100520541081d080007a581101940c65900c500c200e492548045800c2d10112108851410b00805136040300301c801c0540741c002e8901030f01ca40d10076034180c841503075646542020340b04014800b801140c120f81e410f1120360f02030000742c108100000b810b68100246034076003980d041d20076202030303015802c2508004521681802103000c204001c0e9050305003c00b403212030540c9109280300001070004030303402140503081d0a4002e01c44503c0d1010080c01811480d6503442c5041c0301d40321040380070074005a40f8401d5070035035014060b02484141c5424030f000000d502803000daa64124022010400305000c0400d1030358070b80c041c64082c1078542003125151410485402d10f429224a484084540441d00400002e82203070b551038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 599780287 1250 599779037 599779039
    0xd0c090b19091a0f0708121003050f010b060423031b1203120a050604020909070e01181203081f08010903032702041d070b0a02060f191112090a200a05 66
    0x40d40c030442418001b5043c044c00c0183c1c41031031091030034000040501508070701540d004006503400c440845800a00303c03900c0380c2d045074104400b44004c202140458021181085d0584586401880c0302c60010f070a016042d0441500c0ca210602c420b5040d0801c00c00e03040411036490000d51808102d1050140382107002412110303000d1303c500c0000ca454443e0307011b0700c0e2051009441c2003074504100401801404141402d00d0020388901581c3d608114418100c00440f102c00f081e041600300503171400c5403100c0d00185076a111024002c00e00350302014136081000201005000066107010f9403600030162f881c1e40f11040c0e013407141a1404042c20754000010401c0c66030449001510000c600700c1c4002800d2900c3c60698540100840012900d110400a0440074669400d550750303681c90381c004032005003003941c200403041c0c40704100401c035100691012402c0d4544800045c1490b00c3d000ca00152410202c40c00c210a410906840b401c010104030040c00c51140d488411505844450210718410010f00c111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 599781537 1250 599780287 599780317
    0x1b080112083415050601140912010b030601030c081005011d060a0f060818010e03040312031b02031b060702030d021e07080304050706020c060d0c090b19091a 69
    0x1081454145203820310003190252840b00c02458142404550003400750100d40030542080c0014406610480780c031025080600c14513030603c400481072100c0040030200070410782d0340c1c0c0d0b50100d0480d54200701040c000c6226028040c0e41500381141c42e030030162080d0b0944507581c00e200040c040840050301122a890943d0801100d036039840d00019500c41040e4001c0300c180389942d001149095000104034411038016040c09540c0441e8580c09080318454003040010340c00070b0000f40001562103c1b010006801403070046180402850528a50301501000700c2c0940e1002a200c001260150421210294620040c01145c50140c502a4a07446180e0b0413207251940029a100326100403042c1c00b01d1740f01c0700d03030703e154480000d85019182e075032050381c00303a42d1807050b81000288240b000482e201200005800d15090062410303100c0b003d40100c01d5041c00740418076001040d40084c210142c0f80001400074031048a009160303010b80030300c501c0d0f0090401103800103108054010b8580448a0f110100c1002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 599782787 1250 599781537 599781577
    0x102070317100e01151815122405010215100b0f0c0d05091504033201050702011d06010506030609040819020c0a060216150903061b08011208 62
    0xb260b10804059000003054031146400460180560490a0f5000695488400001c400780d020480d0350060303071150344482c4841c5044a80818801c9607000c00c4d400c0320b00e0001c070762015014002c0076820011003006175126842e0404202c20b6034100301c041c0100c0001c0800000e0303810070310301b05d03030308007495000d100701034180081c100b00080d5504040303540440004042c0d504c1c2182403600103240c0d0b40203902c4c2612952030b441d8004d14441c414021501140d41c86690504803003030f0301e1980385445002450309403140e80c502010300150031003030003030301d11804103980002040d1581803003062010790342d02c800c06031540c8500f0041c0100d882d090210380d00140225804d00f0207641e28a00042d0b24032a11029004c2484003481c6c500724183c000070a0036441e102261054122515004126943c0445013408507414a40840811802c1c40080620342d04030020b1400400843d04c90301c0703400907640302d4104203403074130000701c0f00c1c140903a80400028090710500d00ca1030f407a001170340c683c04400d00420241c1118200300d400d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 599784037 1250 599782787 599782801
    0xc17340e040e0c09070203181003140708010905160203070b0405030403050a0f0507170a020436050c100804030513030b04060519020a02031206030c0901030b10080102070317 76
    0x2040e03680c80024000d11501140d401c6282c0c8070345112144078010003039100800c001034008010303120b00812107000e401c2070010250402c110b00940907215000e142d5503204440424501c41e8669110314003580b00c000241d42340c04481001c9500007444c01081c0b60031000c215006543c0442118282c80c0c1003100c990b455240c07414064154400c03544024428456426007004001c100000184658050700541c0c850590b5002442e0400c0000e8405001c1c81d00070207000b02c014542070f0b2007080d040341d90030001c1c03e01000d5440d0301322030100c0c410710103112124808400b85c10000100903221103d003050350680f0b41107503031502c060060351000d800181401070114541c1d00894040105000441e04061240e800d070400f42081c1c0300600003510075035480f41200c0b1003268198440d008581d0729018644c021840d02c4520351601149100180005506001d6842190b00aa803804500c07070207940501c80702d80d0f81d424610042c9079040800d5103c0c96050b40144a0800070a40102c0034003004001002c101c03884c0e0307643d03003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 599785287 1250 599784037 599784047
    0x50f0612070c05060a0c0f0807180801200a020309012102040314060f09060c0d0b0901091b18090f180303020405040b0d0506010b1c0c1734 61
    0x160340304520a00314000c02003400d51269072081040d00035400c1d034a00d0749072103100d14140c031340400050001c1648aa00d014000d8480d601e802c0d4402040d140c0200300009601a02c4901c50fa13984c04240b0340d03915111350306858001600350250f5a424403280768680310004102030341700d002e02400d030ba0600200c00d03220301180e840d0842d410a80d40e034001007155034544038680005901040080d21001d1310614001603262031000107524040c101d5400201496503440100e81c0c1580d1000c540d00d070b00d943d00d03500e01211a0b202d2000042c0640307000200480d41c40c118410107041003442030b007140104075030b03e41055000070780d24021005694a0b00f0000c142c200e456030171800603107182c6030202101081c03034102000345a4150701a04c2900d204480502005c1c480104000f60b034240b0480107003a642004004120402c0a58010300200c0e0544d050306186000d01c000d894221204040010041800301c45c2c2d60003000301a4440b198083c405044408194002012008520500c00364070b0f4040d82c4d8400041a0541c014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 599786537 1250 599785287 599785297
    0x120a0c090908042408010806040f0b061801152c10110a0c03060b030705060306040f09080a03090b06010309050a1407090f0e1509061f09090b0906090115050f06 70
    0x11042d19849620707440e032500c0301e40c421302128600140310f107400854004ca0201b8031600441c1c0006d80c03091005d4481e10b45a02543c0013405d80b651050048003c40022202249010700903c0c0c140c2881c810420b01e0344000d80844c2c0d000410b040b51400108280d2854441807075040d02590041c0d45c0d0031001411030034161050b4002c0c0c1c130424a0340c401c401c01c240030486107280d40d40a692180030f003800580300c40070a2507070b100c40310300986911074802d2000801904040d40a0714007080052000b03d619001901ca01ca165404000c03501c000075160f001c00010b0000101c00c2942180f820b10701001000c1a580307419031105210f090080ca4400800c82075031030340504004c0c2720040c02513400100b008114640d5954020301003810303081000c0c010314040c903d041c040c2d85611031080803403101814483d940c001c00c5046010403502050000c40040c039000c00c0b215407a2061540d80ca125042c242283d042a01c02c1d14034048000b404008940e04154410b1a450000c00740e40381120015501c089181a10000081c070a020b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 599787787 1250 599786537 599786549
    0x5040b0f0d0b01090503032b020f0a0801050a0609051011061602010b04050f06090a060306020a050703021e121621320a1707020c120a0c09090804 64
    0x100c0c0a40032615000028810441182020030880d4080710055440300c07001d10803d070f03054006100802400f64289580400101c03201c101401070441c2c09000c0301260000d1454002c09000816000030341600088081d0141c2030032500410100c0c034080c0014126520b5018407402902c6542d00414118011001d40700540c0c6010300741e942d145070400e6a0600002c0444182c130066082c5032180c801ca08041c0309480c051181c2c6001900c10390750390801d1041609000d400104c400b50b681c070002001c10840c1c405450552119030360f05958002d0360800a14101182092180d08910002150513080000800c409018040c00303c040d2500d2842903900528841014054038401400d12403003010804150103049d20b04840c1c42e803103800c501c0c100d0310704014000000b51822802c0c640c0903421241001d40050010907000e858410510442c41541001210041e1440c001580c07020100c58840d182c4406c2000110340188002c04d0060040c2e114203075161880d00c10a145559907611050030b00c1010000c03030f070181407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 599789037 1250 599787787 599787809
    0xc0c040b06091807020d1d2101060b040e180a03081008060f040c06080c0406030216061a100309030504031101020f060f09060c12042406060905030d020f0d050a0504 72
    0x3c071596003c000c158086a01c40010f0041d60511007000d4040c0040103100d404101d0039400c084000010301c00604030000d008004c00352865030390004104240142e4018180084009032110718144e6030b400d200300c0c05480c401d1108050190628002c1001880c1e000d064bc0500e410380c13440e1107035070000c1a644107a070001012406203008200b8440d4070340b15918050b40c401c49030040c0040c3d42d00400c6030161400d4a01c101c2c1c400d0304100401000740b113034016280810201c0c2050f40040c1c055a6003100b10f9608000500007a0000d21081101c1d00e450010f4815260b000d0900784941c1a01d40c0e4003c0c640e01c540e01009040318000d460018080c0d101b00b00d4480055102411680039082c00034000e466103404941d071383c0961207403200260400f104070b402c0c0c0d604902a131541207915100c0d6952866004d9085480402c003d86111504009025900402d8003c0103e5120f0704074160a003401e05040c1070141b42d100c01554016001c615240303d0014000003045103038902652101283d400884040c4103580c0715003001c1c9 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 599790287 1250 599789037 599789059
    0x30b0a0b0d0e1005070f12021309090b09060105220b030f0304080705010507120305070e0a0906060909060e0c0313020612010e0f040314070c03051915020c0c040b0609 73
    0x250702c03481c06050300b030003122642010203400724142c03442226500c000801c110036510400d400f030f011800c3e059080e8040035040a1114600b90025070071603104181403600da02c2e01005000004401c83e400c84144009400303c3d606117804501524249441d03404030107100d035028038116143c0d5200041c1841c0c0103050720802d10400032030765940d8100d405054482d015207100003904c3c0d8060b00c210f54503030317510044140c000c102030b080544c0101001000780c01448860035024250f075450107a000040d10300d1072800580c141c00c000780103000c9480c6401070110f03d4984a020b000c2e03d058118460780c442c040100b0665250b44004561101e855480c800941043d030100720782c108000d80303e508505903510320140750072310b50354034680010003d010b881c040c021034890f903104440410b000c40100507036070156010240c45030740e03662150305c1c6c007400d40160036690703480811410070031010042e0700a0856014000354201001c208003251982e0600c04414440c541d05da50b0000d4a859403000d544600c80c0040080c0c42d24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 599791537 1250 599790287 599790307
    0x5120408070c0e01050310020a2007060906051e0901200c0907020d09032003070801060905011a030105010c020a030b15040b03071d0a1b020a020f0f030d030b0a0b 71
    0x80d800c0000111800310780c8850100f840c12030680a0340c101c44005006000817130070554400000c1d40300c98460010448a0421030380343d000180c229002055081000b407401c0c500e00740004006580c2500034000b004810400e2040c1c0b150740c1c2201c84240c503100d40d0b69a03518a00c84005941c2c000020307110b264009400e11520350601c0011070088070034003064403001020750f9240000c07a00c03040b041260b9008168051018004030b00c0c107421180720a03501d184070245030107502000900d002c070f4139400102e03d40c0d124001480072109901809006000b44404000400b5520311408054001405441e0402c00003903100c10642d9607039070b0060011070b0400403602c0141040813114010900c03805c5040d0050781440030b810201d00340080c961088408070002c040d5003041c00002110556009040c1a100c5503c40a280c40040c84038a65000d481540f500144910825031040c0848070703507080142071180342620444d81803510302086000c00f01801c0d01c3c001030803641030710001d541080c66400c00000020080b49040c10 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 599792787 1250 599791537 599791553
    0xc051e090910080c0607020105070b09010b04090b1b0406090e270a2003190501020c0d0c0b0601030507091401090b04080c0405010b0901020a0318051e180106081303051204 75
    0x103541c804815955134030204014042248100c0030000d0001e802080f201001c50760004d8043c2e08104190004561690302500107000e0340d00c2d20500f540c4c40b00c00f0030b0502c0724031030042d16844050415071a505040a242075000b80404440344100c1f90050403c80000d8100043c407001661540c0101c1001c650100c41103000903034464601c48102c1e0702e40c038994510070126005003412040100c4c010300800b6040c04400140040c107103604400c0f1115074003403040c4102c090040c00050f200c220141d0707500002d85c001d42000c440c140d1010b028107050505d03000c2407121059100301e12406541c42d0604005000c82228012551030b9041d501c450031504000c43c003c40c3c18a000301e00c049444a0032503040c8426600c48444d00c00521501e02c40c1800740c0d20820b04a000a40a0b64004203841c0c600c2e801900d40c05c0c0c0c1c42c0b0104580c026600c40c800c00000620b03090001500d4103c941150b0b50801008a49096041100141010801070160718048000e00c803c2e0040610030411510038081030300108007103013410f00e00388074 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 599794037 1250 599792787 599792789
    0x6010f09050601020715050c070f0e06271501050910030b0a050f0303070f0221010207060e060405210d1d010b060304030504030305030a110a021509010c051e090910 72
    0x140d0500300410302c10340c40002c4e41c009464182588080081e50314409486a51020740d03801640e0041c4500011070004040c1060300030440225401c0c02031802c2410403c407041030101d448100119006070164150904140945c070681c07029a1072411001a0016034281c02080d17240b0b40d01c00b5080e01809946a850380002200031340030344600342070b40d03207500c1006029800c0c201001d402d0342c4240112404a120701c4510301d505400030301814422007018016030b400d01c4a0b030790343d903055a4001070048200009449000586003c09014001d0380c00c0c9643e415071101c848500c0740c803200c85a84c00c030b5080f00b01d940e01294081d001141003003058908051641000911b09502e001b00c0d5460134000c100d10b810a04200c0784900c0d4181e880d20302d454215501510b82d07410141062007503a5940411f5112002440001c009140d051b070000d205c0085100e1701088800c030010400105a41408810540b40d50000151840603800c0c0a010a0030700520310800628000c21110079030050b075601c1849100e50a405041c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 599795287 1250 599794037 599794049
    0xf130c12061a030a0302062e080a1203050118050406020c0102040f0512030403081207030f09060212250e0303370201110a0c0c090510051924020109020306010f 70
    0x1c07280c2d81034401c0503200c1084030401340243e006140000c1c0f081040700c0380813084c40701910844008107110f414508903160340d90030048155016203010700078000b100013803061741c0211b85024407640d0304002c1c1803007003010792151a40c0301c82d8a03400441d040013040d030140c5070003800c020021522a81d0b60944840108000d00c0742c240540c1e0b980c100b1003038202d0044100c5040d241c00041161420442c0d9003215a040001488642015038400c03000d11003807102e0083c6148103000381300158551901d80740315000b00c4000741c01040f0780744903040711940344d25041394208003070046030a105521010f41c0012900710322609110040580c49401c4030b02c1804481912044a81d1054049908401c481c0384140d08031a001428221254400d00c0940c120521030007441000c2072040b007404510f650f60300009000d030b900030f0b1109008044513400500007424059040b2841a010443c98580c2900c1d1083c811281e000d6100c441c3c15107a0905a0b428405000350800c11140d40d016085841541c2c0d5403403601614500c0340202c1d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 599796537 1250 599795287 599795321
    0xe030a09080102030c16050f06040809030d1814061201030305280c080f13061e08100e090a0b07080f010501031b050315040501031103070e0f130c1206 66
    0x100d6030361014801d40e0710441004c4c0a90f0701e8010000100380c2c11b0600302e002100c003481003030341200b42510305022060040b40310f09007450b10b401d12041094103100850900204104e8204104000c04410034007840c2101c040c0035a0001c00802c0201080440c4a05e034404a240010440000205540880104a080355401d50155000c800c2503185110b1042d08800c0c500050a4042035400300304500014803050303804024451a0034150740c011a0064290340c015400b05803003403071015071210201c10b100c1443c81e85181c401300b2072800b02290040c00c01e45004200d50030781c2c1e05000030001030080001006c06074020300600d10901e031000d00103180d00310454502c05005040800014154080d0082a454040b04480b070018850244000c980a4000030459014900403106461203911648074440c007860040c420440e032007002806142c81c01d522035001f902d4000c5420708002080429202250b0860702c02202c0380b040214500b04040440e01a401a0181008040c0c01c201005860740c814008004901d0300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 599797787 1250 599796537 599796539
    0x70219290103050705040c1e031506030c20030f04150e06030708041205091c020301050c0301080a060b03030d0c12050907060f08040204090b09060117070b090405040c090e030a09 78
    0x1031000c0d2800c28480180300d5480a00b0500092070300d80c01c08500c0490300d1515001160b54802c03114400c00741c40d18030201103982d44038444900035084420b1005000542018004140507200040849a000f0000002d01d0212100112010418001c55000c010303481c81080e184c40e1039001c0300600042e010b0504011400071606064542441000d4038800c8900d510741500d00d50340c41c0c0300c508510302600c403c0000c2040c200300c407100ba81e5401da240e00300b000d40c04811032240b400c01e02c1030600b142c0010700b8400c035484090004000d1044002000503281c0d42c03007080031820781e1400020a10b1406606100a20182450351600a065000c24803030205000e2004c1404142c032039203081915034020f801000300080000c0660a4101d0050098540003480138100081480b0b158890441891007901d00d40220740200004104014101843c00389030140c500160801c5441c041010702584078017141640130b651202c00190034000da00348c0c1003004101152081c4032000c44580f00986035403200300007101145039030304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 599799037 1250 599797787 599797853
    0x1112030a02062a0d0b120d0e03010b03071a1c0905100902090106110a0804080610080601080303060411121f06020307080d0e1c02010c0e0303190305070219 68
    0x707001c62900c4031420311102da190f9018614550001420003012074640700b5408007625250007800600c090407000e040154852074008240e00d4000308441d100703a04080c04020301d42e40120309202240c0d500c03c5c400518020243c4514868011f2400c3d4201c0000818511080030b6500c0d040a264244114103413540c40303000c18000022110840b4000e07411020810050000c1401055000c1c04100c0c44021150341c1005640c0d40709265116030841d18040d00042c00740261800200d086030050704102c800361042c1d60601c11003e94a000040000380b08580b21620701c0083d09400c411038040002e0b480480304140341602001000c0403905154444410741e40e54000303840ea1003c0203440299502000c8103140400b00300868006e0300d04149140060302403038800c00d040c44e020b016440300c1071100d83c0000c5124051100090900014201101d00a810400426180010008062001c6195070600040588415a04034504904401c2c2e0801180c6039060320401d008554000fa044034400344c101ca205412404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 599800287 1250 599799037 599799061
    0x30090c0509071d01050f221d0a05060a05040e07050111030412021e090709030506011d040308220506090601090603051b220f05010e070f08041112030a0206 68
    0x650490004030000030343c10348281c080d0070007111030b00149012400c040c0b004003c10322650000a40c050f0134590b14101c500c41c410302d080c1c035100a15000d802e00d0303c050300c2c1071803182c05e4640080003036a034035950341c0c0082c400341c0c0c03459065005000040c00401a0180284480341d4407555030140c140850301c140b55510509800004960694154212035540c41d82540d00303000544d1900040f5800c00c68800a0f9640b0759146c0a4140d842030f2016030710f00725000c2c40d604159042001c103030007405092250040420f84000c60814994001d030741403a1000385680d413060242140d440c03d11034000540c51801a82e030511200088007070040500e070080d0f5020b6680c541641d0112000ca01c4001d255422007a140e5400100052540c02e04400207001b05c0003812035031807140c82000300070518009181d40d072000c00b10322030b9480c030846015207120b800820107030400050181c0f600d4070521054080102c800d00040c00c0010301e007041d402c4020054080062002e44103e100d07140d0300f0000a5031b0061250704005075111802c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 599801537 1250 599800287 599800291
    0x17090d110f0c22050c07060b0409080711041d0a05060a150e0c090d06062301080105120c0907090303020d2303091903020616081630090c0509 62
    0x40090054042c0c003414020103801d83d00900b01d01c4907084a000d051035038240602480303281a812102c0c0e0741d8003149030107412100200002c80c0608d02c4e040c030300000104542c6c1202c00c8035401240c0706402d20414070000300507000e44110f404861001c0f036406401200009032141d100f5206200340ca40c0d0355900341c3c114080300c0081585040441c1c0041e0100905080c0c20342d620740046490b0b802c5407401e4010800b00d42c00b400b28900481e0280d545000811011036070800b0340c070780c045840a1202034146c1c03d030f000030010a4117009191003021000b09545804004010380718848002400055082c43d01000c0601104114801900580103140d81403880da0720401008010301c02c0b10100c4900c1c090465840302a41d0001803104c0402d00c141c0b0724200c0140120b40b1000003061080c3e00510051400c50300c000c0e500700351104500c1c00d02880b502030200d01206c0d070700f82000b100c0f01c40c5807155048209140301807140c00603200040d1046180c048139415118203030010303502d4600855403008940e5440c42441000030003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 599802787 1250 599801537 599801563
    0x51c02031b0a080d050a080a0b010f0f0903051510300609050f010f0c0203070c051216030b07030507050c0c0d030504081f05010503030c030f0a17090d11 67
    0x8103401504504212280400c141c0d403010382031000a948900034585001c64034003680e008a10041500c40c43d0a6102140c65403049803e0418000e600d6a007002070031003100582001d040c81810114174241034840d5140c100155081000c60b006101d52802c03103110490180c504601001e04850b0100e603c3c19040300051500c0301d031005401050100300f890001030720383d01904548540c2c403580240301040c400c1103014040d00e11100000b501d038261401e128100c440040a900554200313020001c00b080d03401e80e20b081155029101d003080e100d0a8443c40c2d00f81074000d00b8030300305000c64440100900040c9601da03841494240c80c01c111b10703182c681c016200360080c06801c015540c40800c050340981401d815104100e0700c24242281496150703600181012003070140c0d600c040382d0380c0905484183c05401143d00405040e8090740c9003244600b049a128030031064403507484480040c0c021416807003200c48030001d00c0c4110b0145510f0400d03d00c041c2d22003010111180c0001c5c142007822039054804500d00c01400f03c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 599804037 1250 599802787 599802793
    0x6090305120309030904020a030b0906330c070f080111040308031302030a060f020d1505280b0f040e07030b13180f0605010e07030903020c01030b040902120106051c0203 74
    0x141c00c40c81d02030340e440280900d640d40418450b18581da00c95001030208018507850101c2c0d160340003070521581e400002c2c1018420180902241d480c864007031280c0b01000072000d401c1085070141c1c0c0410800303110760760001c1c00c94454407400140e800c424400183c15544120000d00c10040d03042140d141c00c0c020303400064640e0b401040031a0060b00c008014454040c40501614450410742d00c3c0c2c0400c03a0203021803c0541d03600011211100c5415102c0c21a0a442805c1d80318103060410010440c61003502d0300200b0340c190a82c452903428410902124010400b481c0c515036135024a0302c41c1d440940152184441052aa80100b0180ca0007400b1701c01d500e80340641048120325a60f100003000d004400c4820100c0d80121000b000410409001c0030300d11405600045203a5240c008070b001601d0004108030101880c0940f1103002076030124003c1d030005400d00c0d004c0352642181000400800100b02c000307600000c1100603852050040d0003440445404850740207800c802c1d6207080d10618034110b00290702d60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 599805287 1250 599804037 599804053
    0x12031e0c03031303031b11010b09090c101707120c0201091502030a06030204060f0303170702250b031602010b1509090a0902150c061302010e12160e0a0606090305 71
    0x329070803841c01125000c2c1c030b40807031a006004d00640a10f07038921034a0300012480007d070700030075409000f54404a01d044d20003004038030b4a08401d40c0c0b2850051081d500c100210b002440521344500c06100c29804084107100d10b070308100a0140500b1404a03d01c50f0841c10280b06500907801881861041a04902664082814000500000e40c4010f01c1201c0950b51114044096102c520030709001d400004a20721300706040d0b0401074994480e46208a606c0218401003000103940820031564420070305020400441e03010020409108082d0040f85203a01c01004100c00030f440380d011240c80283e960003c000d030a0140c0c060090140320a40c980c06070000400602c2d909003008050164420342c40d000001c5e241e80f9a40c0090402107000049601e0041d001c540380c0c0040c0303001d02400703400c6244440e100307401c6546a80040d00030380d012001c80707200300882940341c502c45600380000403040000000900b03a0a494040d1035094150030780c1c002c1511490a24080303207850052002c0815280c020004002e08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 599806537 1250 599805287 599805301
    0x1b0103141303090b070305040f1a1803071701020910110d1d0a0605070b0a0513060906110d0c0215010e010b0a0309020a06091e0513020706020912031e0c0303 69
    0x241c90000c1c000c42c10040c0100700000c0310090000038001c09440b0784c0c1c910baa21407a000c04448000041d030401000200009183d00107010504100c0b216084d09013944003da103010800241880490343c060510038050600c803044009066000b031000110440c1d003040e482e0750301c4404884e00741700c210004400f9400081d89082290054002049020ba05100741113000d1180b00071a900c000a0350103c8045000070074910300f00b0581985056002990600810043c9800f1780c1c00300c18050b101201030f0070b0303550304c8a4802c20f11990b0342044c000c14280c1c101080d500c003c483c062000921113241c05000600641d03c0070000a03480b08000382c100c44009103080c01603420702182048551041020100b410351341c807900001600e4903411403008081545235003078400c0c03800303442002900d882601c103180780c0d8104506002e903942e40031302c0110049492a0050f240c81441c0f0f4444000e204070051142d00400d17420801c1e030f1201002000300304c0c00022150506464402503071001840c0582d80005003550410b000043c05 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 599807787 1250 599806537 599806561
    0xf0c030d051b0a0b091912030203060105090d0809010306090515190f06030c0e040c0807030209011b0b1f080706080402040f0e07050307150905060c07171b010314 71
    0x407103202030548006515a25150524009202c20201c60060304c036801c00403101c074184600140b42d900c250351011800d5a90f500c441465007038a81c460b040c10f502202185459100b2400c0e28882c100c0582810f15020507800c116000d0340056202c0c90000e403c003540400c030351059000341401408200c102400b02203000301045400d200000b000807902c159902e00003000111218420300610540e100058036258560000b03110384040c1c902140101d0408251940c0da5030b1000805034000600d180060f00d0b0481c810040381e45004d1070f0716000320406034510240500205003a0140102c0c4038100318402c0c1c90101240b8640c111980c45008240d801c40c100401960b40501031075544140300500024041c855951814100c442501c02a41c00e90300c815414052418100f003004081c08030080b01c0c5810011034400142008081e004d070600071440400e031240c02c1e890800528000c1c2c1186a10104061410401140e584842400824491100c0320b03142180354060310880b003030303200d014400c45020741d0751000000c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 599809037 1250 599807787 599807797
    0x17061c1707021e0906010824030c0a06030608011d03120403020a06090f050c03060c0d0902040b030d020d0909021201120201090e011517092a0301021b0f0c030d05 71
    0x1000c500c100441401030790340200d14a42101840380035014240c40906200303003128020440da061120070428044403610b220b014004e10803281c03501070707108126000400c0c1014a0000c0181d00503100c01c5003c66100e400d50001070907107006000822800300503901c2000320703620042940045801c100090051503241780394003a07010780240110340c542c0c02e980d9941000c590407141c0a440021702c1818a01c10004c00384000003980c0c1c405c80080c0b50600b01141500510300c83c40b11a940400c0c0e03030350507440440d00e407500401c00440004084e640446500040651101c0d204111100003481c81c3ca0003260130300340303842548e1840340149a0b0450316800c1583c09040604c0d221000ea040c04260030340051030617582421103002c0d009111030410038419140b4054480741c01e030013441450041c0ba00c1001120348000409040b03620300d5130601054039042380c9045c41e50380c5084002c00e41550000441142040503c26450740d03910b1404c0880340412601c842050311880362140150741600403c030002d200600c5070020f40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 599810287 1250 599809037 599809073
    0xe0603071a1608030a09020907020c03030306040c140d0204051f08060d2a2c060d0309090f09030e09130b1b030f070219050706081005090717061c 64
    0x2d0300c07500c210b86400390950000c40d11110420349500d5808114180098034580155150004100032606040082c0d180d020003482d00e80100e81d81c81c00a00030078850710407507007212a0703150b09564400c0300903610b030040d61260013014090030030b10000410844285904051100c6543d03202143e580b91901003041c200c1c51003006440d910b200e0711001c40815003400d500340c003070402c1e01041410b86180400c54080c1003140c0181c0d000e00e1001203d604a103000502e012607000e00d04840092a80d512898141e901528907005814071914180c100c4d50001c80c10360150724807a02940b01c592400c540d040800c294000d04903109800da18000807005d000a011104032900300c800b44250512240f04040d80c1c1d032842c3c10450705c0e00314910103c0f0622404c55014841c43c161203205004a0701c51000e103440f01d030b595202902c01c20040007803503000509032107d035221580c084e241c01000c3c07540500f00750341c0c010901000320302c0c4050329108a8010480510f00b08500b140c3d0b0200040116540420341e0b08c0d42c8510310413038003c40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 599811537 1250 599810287 599810317
    0xf0403080603122d0a18050a0b0f0901030e031b12030702100f0e0f030d1a0d030e030307020d0f02030106090606021b0d0b010608041e080708070512130e0603071a 71
    0x20010904c500090030864205550318100340a140d100c680074004240e004502a54482c80107011003070b000000c48862010000d510f076070b00c1d081700c0300480c001c040d008444c6041d40000f042400007068a594007403159065207089800c5d900310220300110a2006072018400750b881190944000c0300c2c81d80098012400e0784a00003041041d24080c00d0a0480003803494034141c00000d1544000c4d6841d12510503030741100c003c11070f910034000d008502131000700c1740080d062004842d8080c54540e0100100c0c1c0750281d01400d20341015000707140030489000150003ca200c0d508000020910484500c45c810407103640764002c01d414808440c081068540c100101e603048241d0359045804107070a01c045500900c0b46903215042c510302418016200c1a407500700149402d0214480b001140700350b01900c900940200c5103607501c0f202031409924151240040800043d0003140044200040f100940d044900c807031801e0445580711010036854030424061001404a80d1a03840d0151a2010242c400d8030110714403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 599812787 1250 599811537 599811607
    0x120117070801021914040501020a0803150604030c0603290d0203010603082b02070f150207051c030609060b1b1006080705040c0219080d090b0f040308060312 69
    0x9a50b007640c0c4040481601e0500c50303002c02625640c00f441c0e42801c00c0a0a0413641080e08000000b92100c2482030090b15500010000c00d6940c840080001758084008020039a02d590340d1404609480e00d0744202c1c00420301d0000c035100b03d40142c3c01000c12407202c8840c00c00e5000010300401480784800d00c4140d0b01990384610100025444000a01c400c2c820030100c0440504102004002014000c0000061500501001c0c00250204076030b42c0003203034018800042504409a04002400340000160140c8102511031010b0200411b06002c44102a80c00f400055140c1c0d1501d802d4415078800c0410404040001040104c07040c01405501a4104256005528000340c03800a0700c4054000d44229000740c1c10800403481c091049495200c200c0c0081e046040c5690740450100346d182c6006410204002450404132880e940701c42e11541c2d10540000007820301c00b001c11030729030003124110086600000030403010b00d070002c1e642150300880c103c1c092414002040c0150b501d4441034001445a440d0b500e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 599814037 1250 599812787 599812799
    0x2041a0909070e070f0f03050c16030801170705031b0109050907110610050303030a0b06091302040e01080601230a2607090b01050d021309020714010b010512011707 72
    0x29001e0040c1081c038020003106003040c100400018018040c103085c80340729104003000076082130390344001c8040c50800094035560080040042e201e0038114004a1960900500c01c15402c83e0141d4181c4100000a49001c20f20050581d0340e0301d1a070040700d50507130110980d0001c2810007100c180400030180b404504c010f80c0c50020030b00c030540940b4448081041c0503811002044104207684c0c3c020f2910a4802d9010301c1e00300400e0700c0388400b510b00f1000340d480d440c2d840c92644500049966803c0d0207440c402c1c1d00c01c0032030030880c000c2d04036000e8514048180390000440c4000080d1590603505d07012511400c4102041c54107507a080e160701060382201103030340d000410301080c01903052200caa400813655408003801041d820624180c00c003402241c07030315492000d266840f400350341011115520059845401c800d10032107000180c0e000c41e640c640001000720400c22000002030f88800641c0c001d1000100c0c041c0151031901803510242c0c1d44284c4800104648107110400270312440100c17003502d6580e07840c2c1c0c2b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 599815287 1250 599814037 599814049
    0x2090306040c1409060a0b031b0406051b0f0d110106081b031606020705010c0515040602120c070b060f01051e03012c0406051f030f110906090402041a 66
    0x301c0580b904545054100005030341d070080c1414280c403c03914a4001d250080000e480a5403034010f607a80c00740e021000640c2c041007020003101c1040020aa1915113555180040450744005489144040e40c034840e02e64610300011703a41c1c00c800550001c2c00030818801c0d0100c840c03411958a2a000303640303a51000801a03801d10840c1d02e209400e410020742007039200140f6117488600d2000d40600e5082c00c41c2041219404079025080e00d90034a00407001d91201d09115181c00f5400c0d080403030098445061004201d4a40c0c000c1880111000e4586c00c56918095000d0740ea0054400c007a04e1a510b420000d000b80c40e01158403c02d50505050050520199020201d40300031205621096050000300610840101c02d07144003507030303103514945980740340800440514106d010340300820f120f0b11000420804410a0110184810301b880b040880e01d95030b0030310004072403040c08255024004507008849031306019100b5407054201a02c0c50795551142d07821b00008100549070f0b140c07100c0c1c0c203281800c02940c0d84 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 599816537 1250 599815287 599815291
    0xf050f0f0708070c0806041a151009030525060f0f1407050105270c1c0309322d010201110f070606090e0a030e060409020a02101521020402090306 64
    0x40001c100a00d030620382396040070022060318104850341c004215404103c80a8068500c44c1510004105521188161040e6840e1781008240740505660302404044010401c1c0d004900c0f000c0c0500919903a4000f6030725501003103180d20000c0c50760000441d100b07008038116101c001e84148824900f001649810782182c105849410441c194540c00c9059461501840c6590104040150866812030800204400c0c0001524140c800206400c0820f060181618400409404c200e42d00c2c80040c054020750407031907290f110300c004d8000c070200c42040d04004508000c0403681a2018901e01d03a039240e440c004200c00f550060440d901d5030700c80108a42200060f107022a0070103401916040d4602d050303001c1e9401368000012541c50103210380b100c102c00040d2220744c542c141c140071009210040100340d0b18461b07600020411800001c005200c0c6900144400c007410391918200440101e000c0006205110740c0b10310b08402111b034460040d06e10555040e800b0503440100014070744a00c0c140420300340402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 599817787 1250 599816537 599816549
    0x705040e070e132304080409051303031503020d3306051c030903120e150702100806220f2f070206040e04151b0f050f0f0708070c 57
    0x2014040007860304162000403403c25029005010001010368070750890048000365000104075580800c050105400032100a07200c610024007662403c4c480b8003101c1180d091046000a03c2d04252000ba01503015070720003602c0e0b00820b20328400569407254160620f185000c0c10a500e9400380802100d082002d0800e21a2001280414003525010405c024424446d0310488507121400f040000a13600000031415681c0c007040580441c21801000c540c02c500e5070380980e402c038410400c0c051380d81840c18040c0040520840d84d00041c40203200d01211100410b9500e41d03001404940803080b03008444c1c4150b0541d500c502d80000c1e50440b60308414060303850440781d22080050f2915015003031500340d41030a40e0128001c9000785406016408120984150300c10044103102c080c0118042060383e0180c290041c1c04a4400c0c45801c851100075081044005180804541c10700d003406016401641503c0d90800043c92880c244032600444540c10750100e0b80c02c9480100400000001922412600000c1c0039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 599819037 1250 599817787 599817797
    0x9010e040504032316030c08130e01030605010626070e1302070b1308040302010c15020d1532060c0601080c0418020603060424090207110603040512030705040e07 71
    0x100c03291a0a0f04803040303d2000400401c00c101c400401640026000217055051800380340c802018107000056024122829a02240710b440024a00c8150400241038a024a2042005982c0d030f50003a550740710342c01701c0410646102400041c1c0c0c01d2650b021294000484c2c01c085007840c00382c20000b029886100590300c40e1990106500f4248000d09542d9a401110384201c881051070396140e80d0b0080c011840000d04003c0e000320b010003009008c142150341c8501c40d841c1552141c49041024010741941760140754410400741001510307400d4080040024510941046161484407403882c07884035030010400d400c41001c000601e005041004018009c02112014142e210320f04001c20054a800d07041c020b211a4080c820f42d005030740d4030381c01c90b42c002c1c0f81140c0005411241c0b246184000707800d03032040855441011800521640141c0040144901c184091404c8003a16000c2207060300042d10701404c59400340082d40d52106030700700116006a014202107007865039541d0b00b0341400a0890700100011303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 599820143 1106 599819037 599819057
    0x30423250902030702030a0f0201110d110f2d03070f0e0307031502120a060e070f02100c0914030d05030a1d030708070c090207080f09010e04050403 65
    0x12a00307a00941d00c901e0403207000707510382d042121280c000c03540720029400c4c000d1043c1708900c0d26034101641c00b0306110404001d400184004bd0440e224180304100500c003985212000e402c40c40c0c8560340c0241c400c405a8500185848151081490380406109018134250066829401c041151410034040c13140a40002d250515035032016080161400c03428030307040125001440d13828a1003904408c40d8035101501d8044030480d10a40f410343c0941c001180070b5034480c0d042c2504e800d081f13104542c02d0b50402c00c14042150280c900540200d00006810002c102c1102951031141c10110003030b11640b480e20f0000307405880001d0106261554505d10014480e14010809501c041c0850031281c503000780749481c2e0a2035011503c2600d00c54840c0c00009503021b19802220703401c1d40d000310482e0401e083c1c0d200306440d6802041c05039042c40f41451651109403a24031640703120350700070782c1e031440e80e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 599640287 599820143 := by
  have h0 := BRFrame.cov_init 599640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 599640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 599640287 ≤ n) (h2 : n < 599820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
