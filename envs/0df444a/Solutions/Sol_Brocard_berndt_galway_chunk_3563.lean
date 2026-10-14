-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3563
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:01:26.39367+00:00
-- url     : https://prove2.me/submissions/401c1902-b93d-4754-bccd-e42b488bee28

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 640647482 ≤ n < 640827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 640648732 1250 640647482 640647487
    0x804030506040602030412030e3708031b091e03101b020f01050c160305130f1a12040303020f07050f0a1406240423040c05010504030317130503 63
    0x3000151340c0254429446109000541c13120b2200440842e03030300c04945001e0350311941c04034404a80d000c4550821500030004031407004141001d044108103007900445100c074010007401481c0c580507502ea850400084081d07800c0001140c005041302e000420700342c50115914107004240d0310b045c02038044d005503800d420300510819442c040603541d904440c1b8401405826a8510110010301440380914041004142040101c2c14111051b45031510201c0a208042081c0111126490480001460701c1500096030901d852403e10b0f810004a00042c6200c00c02c10400562050741111150841d400d860016190907003951060403074410810040c045100d2030401c0c00e445007001500d51586403260104001d95540489119a22241620398030130030f064800c143c030035510001d0b80000080300010030104110075094402d5010b588040410045141090100b10a0000090343e60700105402e02c4c01c1460140385880080002c4038408421303052040c0705021848842001984003801a0000c0c15240e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 640649982 1250 640648732 640648741
    0x504030c0201020105060f01120e2e0605060a02030d0e0c04020f0414060304020a030b06010507060c17010608011a030603030403050f07030b060303160303091a070e130b010f0c0804030506 82
    0x3080c265a03000120700660815001070303007501741241e22411048041c0c41d000507400c15070420342d01034101132503001c00f28442c2c20800015680300c03402510a0801766490090300c000d0002e08642035030510340001d4000c050401010015541c000100e072a0b14000c0640040c0f40700c50310340b50505001c801d006a40c1e1040c000725a508204504d0030040c070444103a82001e43c6003403180d1080c0300c1c6501085a000e0b510403440442040401c10700441c443d03103c40140341c480c0c0780aa0558a10045941628400c00000c80100d105e68507805152042d03800340c9001d05180b51150b24082d810740140310a00c4000c0c00e05600400030848584003001a180519800300554184106044120750b44100c10701c01a114110104003048140c240801110004040c01c2510300075100f05032001e801420340ca0303c0032641c0d40c42c00044041214020140140a540180c0e42c40300c42d030343e40001300300e45071303494070010501c6030300d0303c11000788580e0456040b100300b41070390500e041c2100e16410315103014000c540c0064081d0162000b0003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 640651232 1250 640649982 640649987
    0x90108010204170705030a1b030c0b040302031e1b01090509010611060a020f0415120c02071703090d020f0310020a020d0f0507020a05090a06090207150c14041e0504050403 75
    0x284182c40c1c40910421800d1403c1041541d9440c061085603050380040d0301c100e001c650750000094154280d40c0e02441070503540e5507424107060031940140c034580b101103401d00c01c501d024418101640044007000000a4400c843d003a19204a40d04460323440c2003030300160345140d01441c808001040c004184003481d69541d81c0c058020400044249040e028a20024400b05254402c0e18541813180c01c1c0c8604040c106061601c070000d8141d9881c1c14001207a000c0d144800082c020b109843c5125409800c2c030a180440081c0010383c0000116140c1d001448000301c00d1300e1f1200800b00d615012150340e03450f9140d620110342010340c07901c03000e28403d000141c2140c2590300002c4020750280299148152151098800c0303681d401458030003980940e43c10703020000382c5040c2d100b044c1c000b40c141500080c1c40f95541c42510413a800900300301c0304c07490484648904c01409119040900c42c440c01e241544000501c5040180e03c80c42c0100e204e550252483d440c0c1005910316220080c0001030800c004d5800d240c00e01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 640652482 1250 640651232 640651237
    0xb0903030f0a0209120a230f15070c02040903030e0106050f1f1b0b040506010e070f0c02060c010f0b090c0301030b040b040f0c14100302160303090813170d021f020306030c0901080102 80
    0x441e40c445c805404000c4500f0010b4901901c0b9001e1009c0c00c041c4004000ca214070460280988042107041c40140025960714416403041c40c0c0f2035200014003840848402d0b00359101944154890811a01c02d10810340b16000146203200c202c0090150103800d00c8400d4914404510020900d640c8038210001013000c03480c085402203005134200c600607071f40c0b09404281400c0c2200d0340c00c0020301005407000546c2c0910b03110100e50384010000c41c1064210700030ba40c21100035000c0211665140c8240100340d092010b00700f42c10025402d480d61a540c10b540301c0e407100d2003024000402089030303400090280004100d101020036400400300d1080c0741e85100d00c0c80c6401100d0f03007041c0304200090031825907900a20840e043c3c0750030488900c80c81c00d00c50b241a002401141c00680c0c0303810007005520000d00c00c41001c0d001600080358002449121000030500c1c020180590105540c05411501040202c44007501c0e90103c0300c680150ba01d035504070201e810320a502c1449908201c0320b030004a0f003480f06402 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 640653732 1250 640652482 640652513
    0x60103030311030c160f142107050a032001090609021207080d0e0111070b03010807080312060f03010b1e12190f03180803070b0903030f0a0209120a 65
    0x600b8030a0301e48501d4804072500c425156030003418001c021200350407002403000840c2601603002d48071034078182d84591a00d400c0c0700e421600940c0200e82c1d00c40152440d01364841c0d400c01e103203a14608202003661455501d1004603005010b100c100c208140036060400c5100180c540e205000744a84c240c586800030140a400c50103c2c03060829950304e54451500090307545c00c0316524002004800c01500c020f40d40b00d000051601d041007003000d2114004141005000011f000b10404581d0765071400c0001da00300700712034101803101c0c0c10030010a89034058103090a40c00c12001c03590381e0f8901c440000005d0040983e22100c4d03030002d4403200e030301c503c8809240300010007403025a40e0300720001c503032070000d6111062909500510000d040054001c5030050f0030b0703065840c0c841d042a00c50708041e0ba80c1c002c1c0b901e00c1d99220540701c0d0b03c0010f00400f0003103180146504035400d030005504500f0700c50b54035008160b0090003140f13815404201000c190795540165026900b400040e00c0d82c00115090007001c0044600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 640654982 1250 640653732 640653737
    0x19060b030105150309151506070b01030c050d0305300f01170a0f060b0d0c030c0816140d06112206112503080a030509010f06050307050f04020d0e06010303 68
    0x40c0c080f507940d07440110f074031444001d0080c010003000210001c0c2988809001c190b044020440001e0464495100411983c0d009016007031180d851441d003285480365a8203c9405100d0030110f0400181c1c11005965404500d0010079481340203000d08400b090000301080900c280d0904140030038001502820780c117840954205201115000c2c1104d0399940c0c0701e450003080c40d0342c40b5450f40003180c5194000082e58038000c10308018190252034500f138100c800d8205481c00c01000c04100480101000706808103901b10b10350b0014245441c001d8040b0380c115103603d40c054050b501e000010070030301d80e0182402641c1007160030307243e03806c90400b82c8035007640c100210740340c0210340d10200c0e01d54054155141da008180c4000d04008589104185030820061202164241c00d5000400000c0044010303040301c4410350b4000a140c680790207100d00f5124072040ba550f03160f14101081c0410b0320702183d68801d864081c0c40807070f003160010010038002c1c031961100c004a03a203446460034001300c0c017148a034101c90003036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 640656232 1250 640654982 640654999
    0x4050106110d02210d090c0e150d1a0912030106030c0201060b0405030309130212072f06010603020f1c0b0a080c060405090405030c100617121219060b030105 69
    0x40305a0303503800004d0ba810702090b4207080040300072144000030000c10703560b1100452070b10000e590340480801c0720342043c090618140b040100488042d0170000c4014011240060300502944913103045c500c0d11003aa0b0101c000320070003d407000b04100300f0342c0e1500c2c5581e4107030341ea00d40c0d680200800824140c4040d00c015400d207a00014201c1120040e5015500000e01561401c0d8503001006035164454281d20f0400b1380910000000b0010010500d110f0003158480e000e84000074401d80365042c0104080362440602c2c1c03445030113143c0e4001115819180b56040069035401048004031041c003e0844110404002840e044c0c18003026800404150b070054030707c141c086880318005074980080002e05508860103000c200114a0040841a001401401503034988000000e8150078424051400c00c5456107488041040e00c15040c005041841b80002400e0300c0300340814a80e41e68400c82d40d80845440182001c1b40c00800c02d001c2d0300700900e140c8141000160fa458038100e4842d04240710722403199a40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 640657482 1250 640656232 640656253
    0x10905101a0d15050403120903050901110d140a0509030109140105011a0a120b33120c0d110c070f0605030103030539010905010501060302091f05090405010611 70
    0x1001001e1540b0394402060030400400b0a8030310000c01c4010015030822400d4074010403c0303107451282074440d078040d039141651442c6180014112905503030001d0002e600035000040c40d203900c04c00802c070305071000e81040e07584c0300380f220300b112103016100308181d0651904020790108405066400814403040d002408280c1e86d440552780d0150540450f40350b14041000b149090070300c900e40c1940d56444400c0000b40032032494003c0f038a084070705000c04074846036080b4054001000c2107000d4400e0060805194980016481c503051046405014884010b0022035074080c000c0382500042041e2400c88100354a030b20b110260781c4c0e03803050705224001602c42c03203100110302a4880e0080300d05882d0103480352841c10504002c02c102c2451032200d01c6048241004010f52442c072002c0c00c44180904400000c100300c0090f04000e821100180c4c004800d161041040300441d423a01040140070300c02c441c42e0090684021402035070340c0e2080181541c0c1c4145004004100a6005003041d8509101c10b01200c600115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 640658732 1250 640657482 640657489
    0x60f150d0507180626010e250c030302160f050d090f030804060f02120d0e070f0f0e071209030908150106080126010c0e090a0b0603150102010905101a 66
    0x581d5404070f0400a0a86411300c6000e0141044416000d01c544107003003000c94018964601744001e81000f1000144c200a01160076400c403100b0300359046c62845400e140082036000341c0130409220380182803503008100b0245601c0100246001d0b10340002440045c039820b80707080d0380c80380c0c0203204041c00301e10ba030341000c80d2043d000c2c08400244c0c0d5120302000d10700740c1412000d540600b01d4903040c03811031099400e0020841c1c42100a000f1616000401086443d21207400038102011900801020704800d40308001007801110708c101103924500303400c1c55580390b03e0402c07140d030100b444985121605190204003003603400185801241c5d801c00a542c0b01c030200103410380d04680207200b0000022214001444181c9403401810306034a0030030140702d11009040300301d60969121507083e0300441c40501e800c0107a0700301070650a40c070405095080005036145000250140409004941050004054007160740d0003580b02c503032200e400204589982c1c00c1c0c400c0580151010450f44207090000d001d490380c2034203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 640659982 1250 640658732 640658747
    0x60409240b0723030702030a150c030509061812040e1504020a0e010f020a1a0103060506010203071a06040b040e010504030306060c02011b030e090702010204060216031a060f150d0507 80
    0x340c0c02031a01d001c0c403186807084030a2540f04625850140404c011000040e501084007503c3d162059107500000c00070504640d08482d210a001014036003400704100c12481d001c5111644112160070b204015900e40c0f80041c5014007044040380d244100060209a220000c0303011441252401c0c201082250b002e014407040e4001c01407001d0100c0c0203070780380801030f40c01115445807244041c4101c58240c0c0940d148c8011b4220070b600c1003604110035030014824413030603014043d0301c00c000b80011840d02841c0e9131010649051203c034058a500c1800c003103620756569401c00040004020014030103d985a11114000c2206840440c00b03e8a030a0000440760300500b6a2010650140c540398000f4480302e0701c0c2c103480d02050204031700300300d42161ba039071071546c41c9201036020b030b800b0740d000688403400c01c40e02910b41101501c9078801517034100c1041000076032904403401d00d0301c0210600321140e22a07501103500a6240c141c0c0c20b901547c42d1581199403400c1c240a0f1800040c000c0d000d2102c1d88400344151000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 640661232 1250 640659982 640659997
    0x1f1d0105030d0f2c060412060e0109020102032715130e060121020f07080717031303030b03070b210a0207080406110f2d12030105010c02060409240b 65
    0x2032000103180d0000044888250300c0f103c0c0c4d64a01554180741c81c400143c03594043e030002c60707c490002c1008024000c1c1c0d8810341200300d0b00840200190f4240f500040c2d42c0b4007440b0381004824101c80703801e403101c2440f9004406031480c05410810041a001c085c0c1c0f800b0f40148c0801242e484a2050020f981000e03090101d004100684440c1d82d60000d04d0315140c1d4000c0701003000341b1019000c05c02840840080401011041c1c01407109a071101d82030b28258016803040e00c00b10305d100c2428000e001d80c52040b0b001240046915040c0041c100c1d40000c0420b00f004003a1740a0031440714080351541c0c01d00f01401c1402d042ea00b040620b01c405030340310b90601d003c1b0700810902919212040c0424481d95001d80550300f030104051044441d0740c1e00071140785207000fa2120b80440301d15907402e85c0e0401c520b03010a50301610150381c405000804566194a45607000502ca12070400480300c4155095444550072107016200414080c01650318105032030080c3c407420302805240307090383c050001c0d61040d00015210b25 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 640662482 1250 640661232 640661237
    0x61e0f131d1e06010e04090210170c04031e031b03030c02010e060907050f0a120503090906040b03060f0601090b03010b04170703080702102709150303081f1d0105030d0f 74
    0x300d444140044a050700c101c14107a030425640c203c480096074800281c000d002780c65030b030303800c0c04800040700c02c011407400034001014201d030600042c00055041d00480d0034030920002042071042c010b080c101c69883c0040c50b100b000019481040d81450f5140d04a2100ca5010360001d00c50200c2040c07000355550012070740c0c098103400c0030000348014030b040c06003941501402001da82c2055140c03814150841f07440042210503510019101c01c41e410040c03003061380b00508a41c104150042500882e4490ba001011058143c0900c40014070b0740e03014509041c003511500c03c0103900e960b141c0c18403e250703070b00038003038440c007180402d1640409000000341c0809803036000d500d1a007040c1d410380c00c0c4607803c0c6011168009000c07040030882407421b0f6480350040055500a8000d560034a8a0396110844903015004244400a8501400801d80107001c060b081490124000c1514804001e0010075036817541000d0400c1c401c100c510b0402e0210901c08505a540403403d03138000c0d180b844c0040d90760300b0407207503250302 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 640663732 1250 640662482 640662541
    0x20d0e06040e070302220f0b0f0306040f180302150906091506011e020c1806100e0f09100e07030911100207180911061e0f131d 56
    0xb00c000c04802c00d801c620306040240c1030082d02603400311030100e03940c403124282d02103260401501014940880c020900c100c0725502e02241303110007080920006200a00a076242c4601606d032040d0b550085003141404031040c0d40407960b40c80c00030340354116034840e2104000100301149441401044a82c004d00000000b081200342085c05e104c416000100340c00d0501807a0901504103400c180c03402008250305901400300704410508009041041000710040c0b1030f5040c04209a43d01d805111515801890a0200680c140140000d0f02412481507180d04082604c0900400c40800c5023454251b55403008241c11696035031a0880854107681d070080d0802d42003801c0007407e801d000300008410b0819105407042c21751a444581c00f03810503984030140540da66a11001440788120100b0a4420126a0035150007002103a40480c000d1b001d10b07c8014400c0005d05007141a89131007203810032100c69402140710390b510803a54100c0b50002c2c0c44c2c40c002c94020000120b10580d40500303644541e075605401d20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 640664982 1250 640663732 640663739
    0xf070c0f140604150e0f0d0c060f020c010203061302160f080c011508010c030207080901051b060c1b0a02210102040f09050411030a03021f0603080a0f020d0e0604 71
    0x24010344a220a070780d004024260340540c01da040c00b40c54031460150007007042c800301045018007291501c0c0c84081103504118180c101080c008211440d400c4000d1070540311008503402c05a008240000200c090740e8400140d6410110043d00a944507417405c03101c01d1141502101c42e00168455441c81d140340703118200606001134811850400800e029000d01800e000250010070300710350b50b00c03400005c869803851042102550901540c440d0024914055042030420303518500d1a028412051741400004510741c00e40c40010ba00b4040d015603400c04407001c82c189102102800d60001c041541d58910118526514800004400c015180d003d88100b000d07040248078a607007805650903420a9540030000019001d49a40308000508902c000014450520b45040055900c0300c0d9100ca020380c0241101c480825004656070340104ca50791803d91a480d04100400018130094200420400010404000250f030009141e9642841c940031038803610004a02519039041454031958460801c00060 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 640666232 1250 640664982 640664993
    0x2031602060a110a0506041415010b03090109170a03060f120210050c151909081e0403080703050a030f060521150c19090f031211061e0f070c 62
    0x10b1240c010b580c80c01807055402141c0c024281240e010050320241d014005110034007a0711a500f04140880100a04409511042018440c441442100c2010310f02000080344801d0030f400c0000c045a000006521034401842d0880c8203820107521031000a10b020b2002c03440207141c805840564941c41d0380c00060101a42c01c00c44a103107800000000c021040c4243c0d1203c084c01c0011010541001000f114649400782403804c445078503108038840d06007022102d201182001c800c6505081e08010038210740c4040e8842c24106105075800144406030004650040c154401d010305214a110740d020300612103c44541c4098031260301403a0750114958101c1c840d091100844241740006010507514440c0140c00ca0028a50049a02c00344280000800315020341a20940b1a4840c03900e083c04c000c0170381000d517240c159410341c2c04024000407032036940401040c082d0540c3c400b00c03019001205e0162420300320207484181c821031125182d20b00e98012402800c1c0c080301461040610b5a0340c020480055241d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 640667482 1250 640666232 640666237
    0x20a0e040e01061a0c210304020d0f0206030c0a03050601021b0d020f130b03160806010311030319020c12031c11041d0601110607021f0605060d060608070203160206 72
    0x710071081d07584180015210203100d4542d51080541401161600a180400780c2062500607080c1400f40712988003400080c2c9101c1034941103078040e1020200001c19142038040d002c000b00000e503120070048200505000c0140080802d20000da400780070a80b40c22006a9030740c0801c03642c41c80441c0c0840a004802d0800c040c1030682503000901030450380180e880400c0c121100040250354060f15040e2543d5107050030041c10007600100380050503024030301380009480d2041804002c20b041ea102100c0c0565503420402d603000ca07001f400c0d90984010103960065620900611610302034640700c070306004450b0001c0184d44010200301d000032433006001e06190014550344c00000800316041c00086105520314000d460040650000358030345041620014100c407500481c5075032254001020032540d9903010a811018a110300300b54030a400a44403603402400030394200607080700300401c50751880452500100122981030f1100e10954035100303802c0b41c592190007800358440b492500c5680040c24000c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 640668732 1250 640667482 640667501
    0x423090109152c1b07020108070507021932090403021623091e0709090c21022506151d070503070f08040f021903060f020a0e04 56
    0x900d415255100c00304030303607184a2804829941042420246141c0c031070711111035080348900644245110344e03403402c00300900c20840000e04002d07400010a95050059055844099004018051941001600142180442c0304020000c8101ca5082805100c41c00039040c070713000d4202451414001c55000e0020304800540304408500c995101c40d10348003105a0382101030b01407000d02e400340d6144c0340400f9012600790502c1603c281c40c18424011200810030300c0204003811000320300c2c1c4503a500740080e550140c903640705100340750030540208a60740c0c0c000b626080c0c409504811074580d8503803074000c201328016140c12801d07070b07030b014088010440c00882204a0281c41034801040320181c02e07044494402c0c0ea0390241c60300d82001d5041114001d101e842d001c0e488922468480d003103141012000f80344500c9204920140408240400c0c1400000800714030b0140d0040c0c003084198545040a038940035003440107540640c03404031404076000c001e0084032500d9115603582415079500f01d013008010504011b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 640669982 1250 640668732 640668761
    0x40603090c05060c030a080705041203030b0112020301080f120a080105060705010e10020d0e1f0b0a12030c0302061806070522080c01020c0f0a03080f12040501020423090109 76
    0xc00080c46075100030090101c4c0601001070f644860700703110083c1c0364400c090826014010107020502c4160307146486070f001c02d601803034003050a030700c00740060320b52a1030380d149110141d000000121300b42c8400114409098081c2e81113403d41800680184558050651035000041c000030041100d4a054030181140600510001804440c009941c41c589040110890001070700441c07200407048a5100e4031248000000207040780c2201d00301c00100202c0e440e01003011580d03075406001c904c0d464030a000409043d0050806940e1112030401410755013a010044005100384e40005a581ca1029006410000140000c102a40b10310600380c0d419003006020300300c0c0b20150340c42da1304103a1a9040b035030000c0603c8400b0b02090b500301c2000a080c00500d10000d03003e29541804032141e034a403400f0160441c0d4000c0041034650022400030544c83c03082d40d045241074a00801400180a010b41c0104101d910801c0c100c220381002792409458042c44004e5144d2040b07100700100150240c0b0341003130130b0310003a0b00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 640671232 1250 640669982 640670003
    0x403050c0106080105040b0105010201050f0a18080d0518070e072105040308010825050f01030e07061e0806010f0305060f1009230a060c020d020603040803041a0c04060309 75
    0x103440303084071000d9110f0050791391201c05000502c00400c001305d025150a100030700c4185007494400c40002030213084691081c0e0b6603d803600b407a0fa68403800c9582e085d03110880550350320054403000e025107015940c000e0f40c0e90700c40030a0354804800041c410105c5000c1c3d0307902c0000d40e840d180d0640340164070f80003c079940c4d0001d6003c1c9154000520646101e01c0c0b103504c94840d80d506122007070380380038200501400106000000e500790b422000c11035604980c003c840c40000c1c40d081e9001200602000f1805020a10640c440411140d0300441c2d610b10780394810600b003c40c403d018404498180341030b940c95012901c9030b14000d203841c1c0301e90060340d0b01032400391881082e06048800300d849030a0141c04000004e03544c1c0301c24401e00a14a401005244442c000d8108054230040000c1d1015010300c02c0c18284440320680e082192982200034035000d40007001d01e0344901d0641440030312a40f040710100d0368039401945120103000403c074454060a2040c480a0030311703003000b03026001000354160540d00760040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 640672482 1250 640671232 640671247
    0x60c03070309140a2f1302040306050112061a0936240610050304050c06030a020a0e010c0b15010e0306040615060f0807080a020714030901090f0e0a05040305 69
    0x100b140d41c40500c00100042c0010201800c020345c001408076005024001e8036140c00050080b070048100340350008549040e0b09604581525000344520303840100043d050400002d90b602c0d04401034542540034a009112401001480700250305c00c1803d07680e44404288040f41d44200340418002040c42c00503001c41004000e004011281440c4000441c029844016440f8030001c1c0b060440c0b00c884802c86c4480a5418110001000105a0140001000808400035084c0141000f80d480f06060140c9a0f554a00340005000e02030342c821070600c0085400c08503036203125482104103111990700200f40039602d442d002801c0c210074400c8810780e4100000589038280c1580c0610070b803402607204013000544d119900c0e0110404030415403084080c8a610f000080e040d94025074295406503040c58007501a41c1d0300e0312804021b00903018060040d808010589171107e20000080c0242c4000362100680150766a58100d03a4000c580038003401e88100c60003040c1e41c141540c0006420034407030308049040035030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 640673732 1250 640672482 640672493
    0xb0a0519021011030601110a020f060306010203041d06091501020a08090103020c1902090f040f030f0c05030a020f013905041d0415050402010203030f06150703051909030302060c03070309 82
    0x20740342c80f982d91400000070f0104641c1c002600809102a05002e054000084d80009840364811030840d80202000400601c05a1080c002c41d0007400c0900408034a280d0781c0c071000b6184030800c540581c028121000400c60144405065444994050b4010002c0d030303a584d41e50743c0703064010032011414142c0038403010032204018403185401a0456034a100c28003c0c60040104a80c1c0c05007542004130103540c1403102086050b889421003942605100010483e0150202d5102c40100d00107055408086800c9490a50115040048003440c20080c0060b0191800c10b106034124003480800d0100c0b642480590080311210044506150b8204203082540d150280005807018518440a4030748490812041103c4144440c6140104a40402c0b4500c2c0a44c0040d6507840060195403140402304001411951000c15061440340d00001d92500e404241c603001c0c102c0d400140ca0841d100580745002801c0c54030a84c0c02c2c0007120b4259008084644510480503078a0340003420503000c05459002d03580102c1d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 640674982 1250 640673732 640673741
    0x100b031c140a020a1101090b0708030402060f0301090504110103050114130f0509150708010b04030f0501060305030a0513080c060f0a0318030c0620180f0907020a0b010b0a05190210 79
    0x2c40d03900030b081e103100300b031512132510b171100c0142c20705016a2241c01d00c448072100e01911403140d4407000311940c039101c2d400001d56500416140544d581c00003c008203ca0384c198221300c2c0201e00c1081c2d178001001c101c0e001902624400d02a4000b00704440c0103503600351801d800291109401510000360074551118043d05888044803803071030303981c004440d8400305031340410215408005031403c01c00f203504190070144a842548006010100d0058180d4203005d429449400210740c00070450350750300c00e012400b0f40765800410580e00e03004480540001c01d454003003110b04024200801c21860000d25401003205600301c20300c004209903490600808118403d5880e129490207074039a0f9218000d1482c0440c10b445810440150000301d1840b00281030300c17a0070641e641245940c203040c80d403544c1c60300852100c0c031003a4010b991100390315051000d940d8020880301c5409019800c0440130382c1c2c0380e11445c0e03200e10408010350f0000380c1c1007000c070103a0507060450400f00b00c140d01c1034914014980d101d502c240c2c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 640676232 1250 640674982 640674997
    0x1020d0e0d0623012312030d050a0e150603031204050f030403030302120c0705100506030307020d060b0a1e060f1704110102060604060b0d020a230408100b031c14 71
    0xd0904491214012980c01e10f0070b03005101d407206241c5911201d440c040c4d416402502c07968011610308000d9909154184180d40c0c01a02c800000c02c000e1400c95039083c0034100014041c00b00c0e01030403da04403e5209030482c02c1c8108000350042d0320340200f40c14031001d981e40081040e90507000c0c130402c4d200301c403000303200034001103000760b03809a154600d000540c0c108400140074100a6002080700134000380020851004800d000400010f19a4402c00441d08500c40c455000703500c18001c0707040f0800c20490b03a00c074030821601aa0313440c21036034407140c054445501d103290503a002c00d09441c042103d5403003110720b50120611444c10012080040d04c0c100a42c840a690480b000030b40345001888a503410018503a1048044609000c600d1a2000e0310102c0c0c400d1465008000340c0005a04042030b00441d001e81d400c07010341a0030018070044c0d00303c002d680d810600488203540200c01900d140591180a00112010300801074034202c2c24800c100c030101c107201211a8280a580500a00c084207040040c05c180c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 640677482 1250 640676232 640676261
    0x6230c0d030b01080703090b1314030a0c0b150a09020a091a031e06010f031d030c0601060e0609060904200406020d11030307090e04051603060c0e03070501020d0e0d06 73
    0x10040182c00244c40100d00502c2c240400d0315010b001000f00b9088180543c20103030300303015106a8542410100103142c0a20000c07071482c0f00000320040c02c50f40c048003d004081c041c00c51110076448480b0240380c2c02203101c04442d401080d06005028910313030b90380140704054550034410201076a4400d0981254142515040007100103c10000074600304509482c10301a02858035403d494408000f81000300140038003004c1540d50020382211783c9011325044010000b280881c4e442c1c08075032100585d207030001d00a403070018040300e1600e49030341000400d4581152000704000d0800e4144424800101034403100c0b6076004142000d0340510320200f40042c07001d0451940940b82605003600d002d003410280815102503684100100005182c1c404400c40c15111460b00381001500c49003047e503d800c403852000c00c03203650203c500004121042c1c2c05288049a10b440c2c81c050800b80c5001c060300d85d001d0384521030150300500f0152000d03500c034808603c90103a00902c0420040c0040d140c10049440105900c0c18 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 640678732 1250 640677482 640677491
    0xa060f110708211519301b06020d050c031b1504080409060e1302040902180903030a0b100f122c060606211305060709051906230c0d03 59
    0x880e040c20001d018907040902c602180492a203681c88545207003001c0700d035240031850307031001c1c0c1070034420404400c02c50b400442010441400c1c7c3c101800c808182d02c5404c000d40701d1181602c2c4220b0040c1c013134540502c001800386003404080e5600076042180c2654000280c011162503614110780342c1d503014069805528826141c600300718a000840320941c01c82040d050b290802c0020700c507030007064483c00341d40c1541c02140943c901d1020540a502200340030100740441410810026000009184601403208040c03200144032020311200e43e2044c0050701c00204998030340a00305008103c400c0c00f0441c20000090b800341c400355030351280201452003803c456104c8000042115080108903007003001110a54a00902261408060034800706c0002003410140002284a4455540300302042c0e004002d440c1e503817514400c010a60a940d0044030b00c104000510310148119040d107000c251407054452150006040c82c1c1c5140784660100c0c1c009001808200405c4001e0302071140c0400b802c566100441c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 640679982 1250 640678732 640678771
    0x3020103091a04030c1203020708040b0f19030207060b120a240f0b0a050909031c150e0603060703050c1206030c060f040609080109021c02030114090a060f11070821 72
    0x31b40d035400d1179001c00f0405005100e0100860300740c10132242110300b24098141c1c0c8a0b41031103110403d000d400c1c0148030b48110b810800090302e805800a2041c81c0c0f10300310400100511004000c070b0b04403c5141d14100d90f00c48007200c000101213515010b000311000001d10040703081003100d40c0607104070900404850340c4518040c0b1480c20400607a4014200840f0400c07068039225010540c1c90045d114281c1e103010514400b01c41d50321982d4810402000109001c400741501d40f40450011351003560441c0c003d00c990000210710034400e02c00c8900458401000520340314050402d106120b10140007607a15008079200154940e0701e403001000c91001c50903001d0f846030301e007402c00303040c015041d40b15240d01e90400c0c0c16038005a44005075138210800007800817190420500100c0d00426007a21542d4040419009200212030001810b14025119100c2404082141e111603015580b41d0002110360f681d003880340e40d00080b000e001030403558042082c01e810b00640c0b6000403030101400d44906d00400c404c070026a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 640681232 1250 640679982 640679993
    0x180e0106090f0b030603151308031003020f0d02010206150a05090a15080307030e01080a0f050405070521060402091911030402010908010c0e280e0f070c080403020103091a04030c 78
    0x201c1c001d0440540160461902c000821f4a5407000ba030755080c04144a0000381d1714001c601e0300ca19071b084d00040d0450701c070301d0052001e01e0048518003003039100d01d6029240800b140362040480c2d103a035506901910f41c688950540340d5480405525840e400a240d88011946884d200d078114400c660610010400744130360141854180c03800d40100310950002c014560100350020040030042c0c00030b20307000c0910381c0d0b606601c1000f454805100043c3c2820001030009000e03000400c00d007655400c0381c400342d0082c00700210301c403410385000f08503503c0d40003400010b0151a20500c3c540c0e115826086101d06a440c1001e4441261211642600100000700c148415540e01450307200142000301c00801c0030002d12200540398a1230008628420001010003240500f41814614030081c4c01c0005600001d440c4d0303040440c0e01604441c3c07003a9141c1a440010350003031140d41280d102c140c020389014941421500110b01904990b10252411070301ca2050b21512410b000310113215600036a07500f0740ca00c10503e0328 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 640682482 1250 640681232 640681259
    0x110120100c090602070b0a090b0c010608120c07050405130503040e091c02060f0604110c010605150406050a030c02070f0602100f0b0f040b0d0218190219180e010609 72
    0x26507081005508050007071130b030001526010740b0700c00d90010307031100c000550481d86814680c1000322908004200c1d4001c45005401450594038950140c450460035034a101c4194082e098184115a000c038404001d28185980040e070490001c0a04817001380158485c54519070040e4420100f550448040241e8920144405a01c070a44100344501210b034401d4029902d10000d07004242069049000c1840e655469000c850111861240341e5110720145071203500804d5030340b0a40d8001c090701c090344103002c0c041074111010b480301ca466090a01d2020310086009018108074001035210300040401c0b80349465081c10000e0040f6401048801160151201954100d51500c1401410407070100080d40c3c0c0d02080840c0c0366401c0c1e4000880c590040c0000d03121a81d1494046c0d00141c1250940c02c01d42c0c9401c02940c482e084010410550f20030114628040307128514007420309020944441c52190300c100c030303041c100f40c10714020040459299850f001c01e440b0280e219101244480ca410004029230400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 640683732 1250 640682482 640682501
    0xc0403081b062d07120e030417011803120b06070f020f0f100e030106180605011d100305041a090609070515090d0309081b130c0c11012010 61
    0x901c2c0300c40280e82e5a000c10b0311030049402030f001105500000b004107103e5500e1004040298205000d0515a883c509480b54028016200030010024035000c7c00c80050141e4182400b8040384220300c0e090307079202224081134800d81414220b803103007450100d40e99510f02405605000351410300b101c1503144100150000003003107503800347c0540d11404c0e07800c0d42d4041d45030304411524200003404402e02d0000900518280d0005403600090207180c0c00c041899610440654070280c0380c031031450f04e070031890100401c060380602c2e070301c1a20502d070601080d21036003000d03400c40e00c50120b21007004203405c407400c6c4000040b51080d42650091007040a2160200069401000282c0e1000b10f008104802801c3c0751040369060350003086492030303031820548200303055002440c1100c262a4002a0360814402c1e0b215803031a00c511890003181801048010391041e101d0940031030702ca007040c50046580700c210a110450026040c0001e6012820a00740e50407000700442d034102000c0e0651511150710501113441044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 640684982 1250 640683732 640683751
    0x307080d091809050703080f09030307140708060f01060e04090506040f03120c090302100c020306010b090108161d03010e070b0d05010b030f13020f0604030501020c0709180303050c0403081b06 84
    0x405404113101282e51000e90390460b04242e9180d400b00100c005902c90b610540360035210018094060281c2900340c038030405186410748510507990480c0703980c1c3c1c0600340e42e204014113214004204960190301a060141c102030800725440e14136032105428020112030555440a010781088101075105d0030789019481d0b80300003004558400f1100400c1d410107070100a004143c80e05100b18458081c400d005941540201203c0e450342c1c551451400c43d800080000d8040ba5002006c60703d104c4040c440102c0307988480c2d60356000780d5411024560324952034050203815560710031201034464018000040a030804440a503034600d55404140112081681314040100c0c05006001004105425503508040401d00085603040c5600000b1004101e4441c2c0d01c2e485000001c000041142c190003a000b4544550150b80003981d4a000d1031064428003200780c00d810b2080000e11000901135400719400205c0e03001030509040e03c07503071032036410b40c841c001e60942c46010384c5020180784c100f006444d50007001071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 640686232 1250 640684982 640684991
    0x903030203180f0a0b10050d03020d12050106080412210e0c040209210304080312060405100e16020f0a051e0304050109031106191119020612060307080d0918 69
    0x3d040b41e840d40b60000e401000401301c08042406007400000749400742c000101071150107107091402940e95101a090f21000c5000110f0101a0f001d07503101d45412140ca07500c44c01e00903665036484a03070800c441401c0c04140540007803030403035184295000d404550581d401c0010803507903000345d03203203803411240301c3c144518010031084009032520340034048034010f040c2c0394602420340c28660604502550b00905110b20001c0f0303030200b054900704026400340c80c081d1020825038480188260041400c3d0040c039018500c030402141c804034513181070f203c59034901e02c1130719000c001c10300d004c07030800038843e10a40cae01c3e60210074075804942a07102840c84014810004616040c03400c00064034a50141c030000e800355103004943c00c0c0c03a0311240201d4030035065031501706d0003401a181c009840800c0900c40341c0e0750f5105442032100c0e00070003030119480c0d0680083c0824204000c1010900f00d20340e0041046030140105000003822410410035060401c56503103981040e00d003080c0100600a034540315620106091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 640687482 1250 640686232 640686253
    0x10608070e19091107080f030f0105030610050f0609090c0403060c020609123a05130f140703080d02042108090907030612060506031002030402062704090303020318 72
    0x34942c014200c0322150000b00c1c90304441e05814101d4003a160020301246000075104414030010b5008620031f09450008251603621502490b0359204211400055200d0071403090041d80342c0b83c444803003404002400c182c40c20200d80d000c200000016240c1c145050000319051080280d2801100c1d4040381a2008203490319148100c070390303500241446a10100741c0055601400003003a00ea5080306440045900001c418032481c44c889208464035846001741341101090ba030380d18542e804403440c2e801c030001c01003907102510b400506110f06401d040d01841144000000229208068160050346003c0140c03202e20349105d20140f01c6a144490303414a242100440019643c0c4041d01c041a000761b85102142d9540302041c0c0040c101c5401c80c0090b081d00c0c10296003000300b02e410487c071800060781035035000381180741703103006901054800a41c488014003d8801c44030006003405185982030240810b240300031404a4120b6a13820070550000e03400104100030a00c03001d1044448480c808020a07607440e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 640688732 1250 640687482 640687519
    0x50604020a1706130203091606110a0809030705040e0a1401060e07081008071509090903170a020910050415020d0518040204090e01060302031e0a02040908070506010608070e 76
    0x402c00181d40d81e00c1620400300d201034030390000c41d00041014400441d601c1c20115130b02c81c1e40320b07022041e0160b008590070b0085425403283c01200c0d19070b0641c600500741c2113a5551070f021075400c4189079035010300c1a0600002d481d07650380219004114481c02410f03016180d41004403000c10f60074003820890781030a50401c8090000c0170307582d902c0100381c50116103070b40341c0050840000100350300011651180034400308101c62040c4c403540181549880d50300d0f425990707603008025548481c41c060080b40340c910b0500c4120880c00d41c07660340452005c10051402c80501d000485540b0380c2000300300004d40118050000703035194212061141e0441c00141300340d8614540041c118450190008072074990089042d00a071995015a009407004e2402481400004c0541a008080d9440280d01c00d104031004040c4941807a82003035082110640070f05940d809980a001c0581540c0604480f040000c001c0e80d80070503400c0c44030502a0807113545007400c600302500001c18202d80f001c1704a1040c41c0040007140b1244 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 640689982 1250 640688732 640688747
    0x1b08030706051341031b0a05120d0501050405062d060f1e0a14070314070b040c171b03030c03030408030a1505220f0609050a050604020a 60
    0x5521031008a0b055607004aa00c2410710302c9480100440ba41c82400700344d01019141c007003e04146015000f8864445030911650804814061039060300204294204500b100c50b00e40034105817070046848240083e51501d1420a40040e0a414110041030440e280c5007903000d11401024102c1d41480281041c0c1c000500424900000f9100c4030100031500b018000c9080408054081c010280b58940d24200c51404456000c0c50720401250b11104040417406002800d40b403e00109940340d65441e10701c0d501c001c001d03612883d0241d042c000e0198a0400b0960720b60010009030303228482826481c00c05213480c200c0850603030003542041194982032391001100143c0c0346070313a2000c1a00f03402032008002c0840d04610411202c004580030002c01c200c10711459000441c001ca005003010000050301922951200d41d0030700465520210060078025075444a40d001ca001741aa03050000348841c402c2c8a01084440550101c1c1d4030a0300e80003040501160f038441c0a521607403e981c05d42c50300300c2c080d40051468 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 640691232 1250 640689982 640689997
    0x60f03020f09180d0c151404060509070902070303090209010503120f031005030607090e070e01050a0509130c020a200d02100c0c0e151509040209010309050312041b0803 74
    0x140030b0000010090450003040d5000c080c804010740300140010480100071a10300003060b40d201d071650005034403d106034812071003107a650400d5556140c8556070754102504014040111600c9080404200c00e00c0c544001d040c058425100060203d083d40b05200034088140e000031701c281c0203441303604e1404d84840111044401c10800d00c42d40c0381c7c1d4003100341034924205d8000341c1e09886204100208035801000750804d80707544100100107659151070840f0318402080c8841d000401c107105524415000708050151804000c0141c65680c03408081d44044503100040c110042e4881d01101c03090000e19a003000044200c0b0046200203c0c0c1e00010036000381c0d12810080c05228030140710901180b103088021045540039140e4001c00b0342c1d84c0000c1d2280b06041e40c010302d450340c4403607042e05603103005141c6010845c00f1380300c0d1a04007488501084000d400801c030032418180c46000c00000103000b440209595a0041e00c109020709007400c4c4001c10109640d440f001c9603c0800092004d85400010365003003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 640692482 1250 640691232 640691239
    0x81008060703180605130b0109060303020c09090c130c0311071106031b19080702030a09090b12060a0c020601080f0303011202010e040903200a0c0b070c0f0b070303060f03020f 77
    0x3208000c6000000983c02d40c140505950715000038402d08001ea00381d0300035514080c41e600c00550341c031078503070800711070451000401592107045201000d0400c00f003116803000c002019280010040703008a0442905102c001d0145179960901503030581d014425200b15826503400c079400c01156680307010540074107904c901d10646000c07000a03011a030000c1c0c85440380780402c0d10b05450701c0c40142000480701342181c0180c0403600c500002203c0314400400d440d0817081580d0b4601b107a92412405500400100d04426080a01e1a84d031107188602003154502428910600107280c0303e042030000d08000c0180c010011035000030325031903190000041520f056170f8016110140604803440140d80c444410404181c1090900c94030b003040c140c210702e0a02c260341124600020b501150348449840351018003004101d4500c074101400f007a984c120180c070130a80304802185955440321481e0388511040e03481141c13202c1000a01c44201541802004000c007200b42c1c81c0720780b040c02c0d035001030101695810b0300ca00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 640693732 1250 640692482 640692491
    0x715050f030c1e040306060510080a05100518100b0406090b25030815040213030f08090d0b0414070f050607170a0c020f150304080706020702041506081008060703 71
    0x2982c0e080c1c08112451990005004039403074000c507074142400c1d001440144d0707150b8500100060340e405d013800030030f22201150791980401d68075407100c10002c190280015020325100c01000c81c0c01e89a802510501c0d207048840000140307800c4080108803880340d041b070700f9440b509010411101e0303000040d0509803000103148a480d10034010144182201c80020340b00e4540b50004028285a04003241c1c0c2e00441c1551304d030501c60400031042c0030592040c0301186002009400040021407604d6100840041c40b4030b440c145030003403400010ba04500040001c1d40c81840000038802007000c026042030442e03881c1f07005481c2d1030785402c5034000060564420305001d04800100381c4200b040080078070b07003501500783c00643c0312484000024a442c0c10101e040380554000035001c0080d18201d2200b5401c1d40304003402030715681d12a40c40800380e4120000854101e0303000d020010060703587d1300030180266201c1001034111480d069005000c00d601611148801d40448000c0c4044100400c01c40c1e44052941004076 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 640694982 1250 640693732 640693741
    0x2030c0603041e030c0b06101e1701170f0a08041527080111072d06061d0705071a0606130f05210307110d05010c020a050715050f03 58
    0x642800f003401c0c02c2100d0316100d208074820160405c042103e060b0060848400c540c2d503034020302049110030311002001c55220001d0740a08000c40a020080f0301061410f03401d1003802001050403c042130b088414202e1070a00001d00c001010000342c40440c0c100301c010001501540c9424016100e0340c0075010744480d201030b1804486000f001401c00c44003080440001c40d880d00540c441001c00780d405404150350030000742e0200d040542050b00d4180c1d03001000c0d18a410781400c0d04c444100c407010794110b5410300e075070329010214a1034410b0701c00400c0030750110000e180319120880280302000f0114001c1c49001d01c00007011640c00c41c40c410049c000c0d007803c04030640340c110004015005010303a50305140d45030700010941346020300140c03003101d40540e00a012000344000c0000b03003080207000850140d009100b0346000c03e04464004003130050240c03001d84800c440d41c0324207003545c2c440581080941d011400c0002080000c01079030008100386480030b4494801e007a0010990b118a00140c00050404130119 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 640696232 1250 640694982 640694993
    0x1b0f09010e0d050d0905030d08150103060308041e06050403050a0201030f181a060301020c0d0f0c1403070308061507060509011515030f050f0a1a0402160506060d02030c060304 77
    0x4450001c0140420084515890101d50310301310304407800c00085010341c0018941c00c0011350f182070a00282c03500710213a95884c812810121528404904140c1c07902400804038500e880208040e14005078a90b44064903a60302c0d075000c14042c0d00c000308000d8104410004244e0129296501d00c2c0c3c24070780440d60303030303180d010701c2000e4140d1088150401906007034117004c004194154500841d944640010181d540200305401c0b400cc0134401010380e0010900740c04140d1203051000302e0b80380c0d81c0c24060028456915103601c8a507141c07101c814580e0000540006141d00303e180a503019a0446490709440341d114007058050003601001800c6944900c0450321488080d0810051003c541c03100c890901d176100060040074030f12a0318400828500107610710010703454000d85200c0c00030150710300c125072501c4d13940b500102540c282501d50002103591240099656000030892000300031a81003c4180e1414030300c0c1005809058a84140400400200140c030b020072406e1107030340101c840985a0b610b5003400c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 640697482 1250 640696232 640696247
    0x60f06121a150a021609020918060d0b0403021212010e100302060d0b0f03010203280504020f0105070212010c03050601030c03090537030302070c0e0906190e01061205061b0f0901 78
    0x901c03405e041d50540110703c1a0349035001d84800002291700242c4551072801510004409648646d0021b185e0612080825803020b01c0170703000740c0300380304580381210001e0151400350803195001e080340e411034004010072055000e030705401500012240c14814a10b41c001010b51241d0859844080e0f1118501c140c140d071200014001e521014000307569a20340100551401c1c14505414040c10003074080d43c10112445100e200c1c4507941c0070348280c040e00c1ca048019aa170780c004c0b6500f241d000400c110f001e00c15280038000c8079084c801c561800705281c1000000034066a1810645008140c80e10407410082000041c07102642c680c00e601c40341600a24035444a42500080180345245000447e0441015850381c0144450340c01900b80e08051916030001511038041500e03028202d500407004135410139014001954028407003600090004c400c0c5001d01d003591a02e40c0410307031107120403c440c2d050210600c800b1741c0c040d400c0d0341e80582c100101740851b401805200000d0440020102d4a20000d900600e038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 640698732 1250 640697482 640697503
    0x1030b07031e09350f0904020c0606010e0105073503040506070806060901080a0b0622080d080f010306020c0a0f0b24030307030302030a060f06121a150a02 68
    0x100954180d101d040c00780241c12412150f650200321140283c00c800a404420440c02c10713944403a24a86801914050304200101565000c00f001905401d98aa10080c05400da0120180c041d6150641c005030080018512890502404101100c0005d061034029610b1584090040f40d815030103440030100e008091400c400000400820f21091141c00550300d4480d030101d42c5e07a24a5603680605002c1c8902079174610f5404506080c001c11641c5406401c01208200b0290200382030400f002c0410000e049038084004106130001e0b0280a54802401003803064041401c0c40c44c44c030b06000001122004051101802141d404500e1a14054041c404051490380261228041038000d01340304403020029104c0710440e11410308010360074440c060500c1e0030307032400601450400c5c2080d01c0a8002e507000514042c2051758469001c86c03400301c8529170602601590340e84c4000e24102c0c0881000b212109200c0f00450b501c039500307501c403a940300c4000310300581070420b282c1d480d01a0454164a0045140c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 640699982 1250 640698732 640698761
    0x5130507030c0e1317161709120102040305071710050709150305010308090409050129030d0816030903030e011d070e1b0307260103030e1801030b0703 66
    0x300009100c502e0b40302d101500d160250060f00e0b80c4038035000038040800d180c002000d082511040034040c40c0040e0180803480da0040441c0045d40066403201040a0010a030540c030304000700f1418a02e007000c20000e0703e8000914004c40c545411030b2251035840c0344d503114040030081f100b04400c400100070300103003211142d029018401400c01c108060040642401008402048080d0052a8503ca4002c0c28100d0360881d241500e00901442407001900f080442900e083d900c07031840341b40e184654042405201ea03202801207984a03200d04160514460800748401c00c40560148082d2045110703c12904490f28103000550002ea46002d0f400f0300101d00011020354a865101104240c00c8144c0904031015003050701c3d1030301d1712508450703042041994038608904440c01091801000301000707580006450800c004d038001d410030085644c6003000002c20010f90340c1d400400805800c9010346180d001c1c2110401d495100c8610202c854803414800985038030828004140814081e0317204c040c000c1141d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 640701232 1250 640699982 640699993
    0x30a080c550c14031c080c07083f060118171005010b0a05190324091d0303070806040e030c0f070f03020a14210f0d050906040504051305 60
    0x1810088000a490b100c1d00d600c03ca540034070001c607807402103800b24000c0c600d070010343d400c1c1d0311510007100c81013001001c00341119000c1144001160380400501042c800881011511030180142139901e1074008111560480e070f1007036140305405106004175031188080c86e001d0042028051803079003102e402c0d40720900000e0341c0c101c00201c148001c60760100c0c00040160601059030f854080484621a10100c440003030002d1100352411012280168050303c0c2c1898089500b0715644241410f0344010b45080b9808010810204510442c500070081e02800030982e8070600042c07017148603101d11008001100f00401c407030002e011f40d82c40340c1c0f000000303170003400c11240c655011000380d41d40c40210000141c0c0d240720f2041b0000c0c0c419009054a01a654040c080c44100ea14025020000c040400c1142d58040e0001c1c200d203a40c14a042d40d05401040b000c4014041d2407a070a600a082c054804040c030200700c010084c1e948107407070f80d104030313400c0314000c2da40007403a90380303040800d802c0c1103444400600d2070055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 640702482 1250 640701232 640701403
    0xb030a03031802060a3b0904020d05030a09060201060506030c0702060c10051306060806011d070201180c05091303090512100905060f10030309150e030a080c 69
    0xc44e0194505112036a0600c12011402d05403204460301081d5101d090320007006c01500314180b10300c000d900039201400e6001002016075410f421a00165103400020b01890020000c44d942400790500074102a121603203541007010112841c2e1044910190051400081e42600084104001750040d00705810400150400d84e8a0305810310381c825041d1401403c0200105040d5804074401d8100d6400074100a13810340d82d1020313085d0b101c0c0b00030030078000d555075515240f400b0303821340380c0c044081485001c80c201a141400104042010007805100603190761022110020341c1280704041664002c4035284a42c4420240385481d116400144021907810844030f03104100b00061628012121800da81041d41d0710580d01d000c0340c0205100140024074443c0c030800c03c4400a041940000700d69240c081103546a04020038902202440100c3d41d050000a00700c4120ba01400514501c3c1590a00c0580004d041c50880740303140526000c0100066512850581010950700c082c05075550f0701030880311501a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 640703732 1250 640702482 640702487
    0x80903010c020c15090a0909080705160e090c01080406200d0906050117060402010e04060503060f041104060302132f090312190f02120f13090b030a03031802060a 71
    0x1401c540380d40c01203036a80c500c0d04c815280407043d01c001500150030311820520b03118604028003c12003059031030044c100400c90100c0d00030320011055040c0d0101410050f4540840610751010041906420b074000074000c15003070383c0c4451481d400070741000c008207081c40022903500c004440c656000290500020f030144038603030140c0182070528001d480401142c3c0ea2051100c1036240d5508500049401c02e0000900540c0070381840003100f88050800a0000d869034082490801d050310500f14140b002400c0004006800d82c9800501c042924248500b038079560100300745169a004692040b901c900741d90750b10f000300c4d8140989406030320304c0400f802d51541004e9002a48a0070056009008140c400e005421f00142121607500d4a00010981346201200889180c011400b0000447c000d00044142030744540d4007814110205c0358010355107100003254010110540d908c450342c0030341000354411b8261340104030702d640240c16060100d12010000355880000c04c2d1068001c3d800200841e4006203980d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 640704982 1250 640703732 640703743
    0x180603050c04140c0d020906040311030c040e12030c0c0a14240a090303090204050a02090f1005031b0408070905060315040c0b090d080703080f070503010605040909080903010c02 78
    0x240a141036418480c0a40e09200c00e8a928421804003038850300040f5134206100c0004105070b0030f414500608050713a41e80041c180d40c1c0b10b90300030b4600c3d40114002c0070043c40d00707000212002c0d504460800082a00449003516152230f0121600d1092010002a0380003680380f0460340c0014003c400c0e15007020716443c1910142100c090815207600c28090300002d0400c20401d21141103150282e03108940d5210b0603903070301900c541e200440400d500d880800780140c51300d010f510302420381034502603100c1818005114401c280812070310700c01d860040a032940d0079004400c032904044d07404181c404086854400081c58400c5911140e03d5114030300000801c1c00040d804180100000c0702035402c60702c40c04207002ca03152000e0b2005003041c0e030303c91010000c0c03c4a000040803450400f0305102b4018407035884000194101501c19070205116004000c4440c1000f000c8642c010031504002d4213550400c1002881f030300560081d07101d17031503a400e201c4081c0024002903d40c0071000400030b01c001d40d0100002520340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 640706232 1250 640704982 640704989
    0x60d05010f1d0105010206011703130906140402031e040311120315300115240206090601090908070206180103181a130c030b06010807050a020604030e0a1806 69
    0xb000ba03400c40004031105104124102d80050380106003a90030400c403c5801200c0b00b0507018144000c20030081088200905a4000c040210b80022514035180740e01c44410b00c51241d140c8079610420030410040c00c0700001b0000000d5880071000c541e920362a0a80705501e41c810038841d41d01c0380d40405010058a64000d40c800c01080002d001002b135144103001001901c9801c0f0b03400031403085025050f80d0b0713a20042583e42c208100000c1351041d40c0c5100d00c1d144000d10303088186480204040401a0103551000201200e400d10052200b85001c2d5040760711100c06004d00b0240e03035260443e40d414003043c0400c0d16001600100071030f980b8101c4003014001c212403001e05501017030415004001070558445400201900220040003030103034035502c4885114010b0103080c070000340c407070420007082c60382502c040a548a050040e0160070403c001401d0400001c01d028100401040502001076010440725042507050500d40000340c1244002105043c0581129101445101a03500080102d41051084 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 640707482 1250 640706232 640706249
    0x4030f0218161e0c12180308071703060a090f020f0a05030402030c0a08030d0e0709020c06010311190605090135060d0302030a0f02030c10141503100b060d05010f 71
    0x4143c4041e00d1030440e64050346010101d41140d01a401040c4440b20110840c502840c00c0ba07190189205a510500d556030000c0c0c40c5500042102020030008002e00600c42451600e0142189098000540319440b04d00448208a4583c60910704100c4c603a01503518a040001e035440e211800e8000003440303504100e41c264400e1243c20711141482c02d0a00b80e60043e500203102851400d041c1c41205800380464140300710841c46245000601c1c4981c5101609a084062020b0007841d4514148a15921002e20136a88140080d00d08001c9980c04905940c080382c0150424030b4032408031200517142c1c400300072000c203041003001d214801552004080e00701640340e2810361144985441007071290b12646200300401503803040020f92100342c0500040c441360000742c41100e01d021080316030f40c4d003008561500000090740f6205464183e1500c5400e03554001010bd001300c0080f00980c0c00280c0c0d501e116501c00940b6aa11500480280c44120444280ba00c6404c42071000d56075840c102984940c4c14420700c3e80 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 640708732 1250 640707482 640707497
    0xb0f07030c0e06090f0d080c100209010e04090203010221090f120414211501120314090402090402120114061201031e0b15030f0109020604030f021816 66
    0x524501078455006030280c076aa0b40d0a01c190000d00f03000140d8080001c07541d000c0c48800300058940d460701002804c140c802d181484e12062a1000b0a10b4003d80c2034440b0443d42c0103001d100250799100c01800315100c0200d90208945900f400442e00a1140040b000440340540d00c0300c80b48100b01c50703602030040d0a002c0071158090030000960391141c1d104060701081081c00c1004001c19001166400100d000c01443c402140c06e5050803142a2a400c2c00c451b81136400400e04115000c2c0d2950380c450040840c05070080c090b000554005001c0401840910070204000c10008a59110703541591424032000d441156514590342c8481c1c085d420911611103075651880c0b4242d02c07420322101784c40c0321500c0d5061084640c0d0840d0369100002c15240d5100700c0c1c407a00c11000c580845c19009485000e8070307800d0b000c02c40001e02e06052606141c10380d00c2c41285070b810540c0260060300c0b02c0341107404072904650750740001840e1b0302c00180f561010b117070348903800001d41c0140002e507601e0500c03503030780900d59844010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 640709982 1250 640708732 640708741
    0xc042409050f06030c07030e030d02070501020d11031b0708030414040606111c0311120636040503040504090c060305100518060325170111040510020709090b0f 70
    0x955120354202c54100d00140007107000301080384080c11110f803190600c07017144542c10000c241b030480d01c00e079030000503808540104507950301801910750108040c0382207049240e4031300030f5640d24402c5400c0380320703001002d0010700e112840620441004d00902d40540307688075911180d00d0f0890400b80f41540c131482c1342140000d80300c1d000e000760a1410100c0b00140003048a150f80c0601e064000b81001c500b1b05440316143c808284e1001d00a0110301201a03805283e418060241301c0080005c00018040c100c0c0b41003c171503000c0341000c0070025071040d8401110a0b964602d090b130b040d40140d40c002900301d0700700b180c60820414288000001c0d254543c0c1d040107581e40707103101e02094901070b120310b54003c416038000c5203805041c041c6241d0f10442c05000c440720710480003007a285001c600340c02c0390440000018240720180724102e1806505007540000d0043c2c6c92030007506045072199110351441815030400d0884c165000740079800003418581001c010705030440c00c0c1070741c9100b81100c000138000045000034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 640711232 1250 640709982 640709989
    0x1609020301141c0b0f1501021222050904061b020d051204031b05060a0c090302030d050307111c0f03020309120c032503020708190b0c04240905 63
    0x40e4100d404494021078004007000901004020203500526115008019880070944480c18a030003000c4614000c0010314002080d02104410120b00c2411904603601900c40301d401c00064480191a1441d001ca00e560b1980c025090f0703600c3d0354042c58022500308100400d0041d20b5214100710400140d5a8082c5000120103c0e1a0783c6407542c148007103001488401ca01a0301907a400c0d900900c40c1c10882c49040e595442100b25003c021001c80301c0b40e1021007000302c80b1101d07000300e1003900c40608107141c006082d68002a20303214000c52500800401100217195148605410a294840341066031101040d07900910907400010091502264158440c104842d00c80d00c2103d1081c1000700c05040c00d211811030701c00585e800020511044e200c18841c00d040107100d0341c100c01c1007022507100200342e03400901c3d000e410801541d2014209401c00280034408221312240b000005a000511822564030904540c0d40d502858100200b00c40741d60041d40906100800d401d0388410035511150400c41d13590081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 640712482 1250 640711232 640711237
    0x8010e070308180103021c0618020403050709090503120414120a170408091c0c0b0a080106030b0315070f090806102c0c0316030207030c0b0a06050303040602160902 72
    0x1002e11404125031882116080c1c0c071214880e0051402525101580602c1041c8603501d51120180b150b480d4030811103115000700c400038442038440c0940c02c2525540f200780d02d800712403003080092034440d05c00701c041000900c00c850040710404000200c904007410a58070b41c84107a10b0504081c4111440520100204400c2d01c44600340341e0749100c030011160308000e078007400c050011201030a040c4900603190313444440054540b01c034503100d9070501456040c0481c6441c2d0b29405001d40380001c10028451a5101d075065040d6802c0d828041001010b0a0201c0d190003014403525112a084030144544960b104e038480c03204c2041640c8154440d80c0b40c10048d034584005407810748072606083e00030004000a00340100c0d841000705005140324034903ca800401c0b41e01114007407038640c0004200300d8400140a0504034280461408609000056502038107920940c60064a010180c2c0300140d900c0040d60007440240501406403501d0345d80d42c40c40659100440102c5502c041001c000c081981e044034400d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 640713732 1250 640712482 640712489
    0x14151e0c0313030e0a0801020f0903100b1f110d030c080708061c0512040618150206010b090f10030c110a020a2603180907020a0b060405280608010e07 66
    0xb580340c0007808681c3c064942488440b04076800c0749048100142e500c0d030a2002c0c003000c0c840c080580c0e80e0f03000700408050800315800d00750040f0b40e280003645609030301d540c0c3c09220585c070403001c1c0f408a00c400794010707261425490745d2408513101324103a2500681d410b0700603001c0c0c08429142d415540d100d0400995100c40308450f2141c0000c039500070019031501804080014601070810b8508d982c00262040340e01d03074031980280e804203041d07040a80005031014045401032100e46c16079480c031008024000d403100410301c5507030460700300411014013398481e001480c3c0000024102c5001c00c028050250191160b0071810012940d00c02c21200301100c0821081360882e8000d0800319140e06113001c070b40c0081003041441c04c280241449500030014100000c0c0808446050030b40205000e020400500d490001c1c060421074000c0d214510000f003884600c2508000304a901113115920b8401c10010711307085001513a4000e80450150044103c0e130380c00780c010356140000a01c008102115100c0d5100020320 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 640714982 1250 640713732 640713751
    0x80f070e2214130b0c0a0e04020403060b120f0c010804020a051c0215040311130902030a0b0916081e0c03190b070203090913030e09090607110d020a14151e0c03 70
    0x2c1c004460060080c1b64000441c2803546001c03c4000224080744c000307400448201d07076114009184d615001c030f128a8403941c0440101060200d001c1c0c010340760380c03490000e20f06001381c032030200d001c665880c07191401a01004d0f1210101a5481e080f210000310243c0c4240d008014010301105050946030444090340d80000c4007403118400c5000b030001c0d880719a881131100580d07480d03403c00141d170140045201c40b80104020072450800c07888040c20b00702e4686a5540700c00f0103100c05c1142070300101c6e001202c1d024400141d6803561020211a09050f451510340f507040c0034070f1816841c051540c1400c0740c0801e000341402089a81c40031002c5c0d0307803807207018403242d40082c8010000b03026424540c242d000c000e101e850702808100100b00440c804110507207086a140d0020b4003004003070b69001140781c10f0052440000e02225140e410041e441304170722200036003902050700100c0008102008010900c0c501c40002d44d80074a020f1000c00c147d1041c1c0704000c400c10000101003200d108880042d00d01455222 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 640716232 1250 640714982 640715003
    0x8040201022a1009140d1a0c07210e06130b0c010204170105010f031b030b240306010b091315080c010801080a111c0f06051006080f070e221413 63
    0xb04200404074a0790748080711044041f8940c030045803850800f00b0b000e0441082083d480d501c0c02d152041c482004140c91100e1341000d41e52804001d503210080d8213640c402514185c2d076a803100d4204582d05041c2e0b400148402000098000074060158010800c0b00d02481e0100b106240514805081c3d40c400e2081079078981c00c009043c4049100e0390081070003c4403900c55102160395981c0c8101c890042100c040507001010f0410340d00000c00344985501180044014010b40d6052410310080380c060700c01894082c0ca40c40c8040a0880c4a0340d1007007100119800c1445000ca690303401142d40c44045030011070015510300d000250004002481001031030b40032405294a820a8081c00a10340c68808114811001d01d040200496080087c0d85902070048601168038a850400620301022581c01002000f000c03c08004285040c640b0158001c422440e0860503100d800300051006070b01c541c01e180491210810310400f01d10a68404220b40d5030040c5140381c10340d5681442c052000d52038002421000301e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 640717482 1250 640716232 640716269
    0x504060b1e041509060305060603061e010302040302041d0727110f033402030f0c010e030a030f05130f0b07090f030b0a0e011b08040201022a1009 64
    0x1142a800d065035034a45030620741d8503203d0070041001c0c4850800841c00802c010b1103241da050290035070111081e40c10b10304c1d50070000081080d0100401304004200c00c0e0130a450301036032180c3c045400841c0c0007041403084524182407844541f108865034021032043c0380002500050794820362001d4030910410745520f40907462070070040d00580119002e2035500304440d0141d03201c0c1d800910b0080080c8804002d04c180c804820b01401100d6452003c1c0300941541e47c11044d83d40002291180440d40300300c0d0384c4600c020034005001d40aa00e02204548c0000b04107a006c0d203034503602030841d401400c54140a20b46075601e18400354807254802030030384145a03811801185030a05295082622490803800250340c54000440140c20707a00200c4461507401d050000041d02c60180c2122510404002c20420800205485625400362105824455010005415a8003d025603154452040c1908940e0301d401388401c8a01410507030010310900303440181c140428450100349040d5440b61030101d0301d6224 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 640718732 1250 640717482 640717507
    0x8040b0c040e0106120c18050418050f25030b01030b04050708100c080609130f030c02060310090e0f0d110c0d050706121b030203091e06010f0504060b 66
    0x10080c0300040524040000007424503121444038001c0030240c0d11785008001c0005403509540940034900100465072481c4100d00004c03905440889070101d0300021655602c0780c180d64440070800300900710b80241c0c2c6400c01d141502003880100d040e080002d648007000c514084182000490001402103140c1400600000b01c00d0309240c0e4009028008031040030350b039100070515001071034242941d4a911601024106500400d01c184c0100c1c0071aa80310040c68070f5800c403950f0481100c8040d200e01301508440301031602038846e4000c256005040e5079940d00e400400724034040124425003020741d01e0080c1c2400301c007a01244d004c001c0445030f000b802040e485c81340121181074507100e114615003d200403100481e0f50300d81d11200028410b0020f407025901d004c001a1008055001550b90181850b00d9100f803c0c003200f00b1802c0181c80b9003001a181d0310344c40c9900346400d104c0441182e1050081090705540c4000180030390407110b644440705182030703c500900c0180c0c0d04034410210701e80d40038403024691b8003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 640719982 1250 640718732 640718753
    0xb0421090306050901021308070501090803090f04090f0501051003140c01080624070f1202070b04030602070f021309060b0609060904090219171606271206020c0c030109030804 77
    0x40c2c1d075134005414074040c201c07828050321a40d03014101d0b9a10242c001c020395600f1600f42801010300102450a080c11100400c1c141c00c44900d034144641d03a40d6028108100d86050b000d801c0d1074100e0000c01907031812140303200c1c032106940005c2d190020364081142d007410f000a000050620180d40c1c602c0b19450710002d020070f148001c40070103100c04100d5403945d040b00b6a1070140040728002c160111b6115458141209034040001d0444e00715000040140304019011040700e0450703500000050b43c03603502d82883c62107040790a500030340c0074152043d0700348105801d812041c12030b80200001c204030f031001c404103c028032405d85082d4008800b413224074494603099004080050000d40b003414080664074804c03488500c40c0d0807482500c10109030380c011100041044a5174445920346030007580d420810064a00c0264421070307101c10b03040c1c0320000048414107120780c004207000201388412850314503080002c0d401c80d800c0158203100d0f440d600c3d145403a050042103851074154070340d1600ca494607250840c800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 640721232 1250 640719982 640719991
    0x1e0509010b0303070f02040c08040804171006150e0306190b0402120702030a02070608040c0902031f0902040612060e07050d0908040f080607021c0f090806040b042109030605 76
    0x55681d1040c0403100c0c2c50074001481414417600d0b180130003442d24030401c01100e0000030440108598103080000040000e0100c4059841d0501c2d81030421021880c034070f00e00321640381030007000c40c101000000d10b24450143c0719032048580d00c54480e403100d2041459641c04084072241c030b5943e05444d1039402e02c12540e0014031400c0380038002514040e0104d8040001ea03c0544d00e09005900c00a02c0c41505030b41030101d100a00f8040c81c00c4807070303802c290300c680410740d096020f031000483d800004200d2180c081e443c2484d11400100400d600740b9552140301e0300075000b1b489440c0c080f400100c0748610324440c900c03605c2e09646038030410300d2013520341c11001c880c5034001d0100d07410038541c1c60a40c200410380da10042d2009000c81c91100308041d0800072860704181c000f4140005651200d4402c1640c40d61250180443c6071003440c0c055008000c10004031a040400d0340524240c0c060300c414031041c46803a2100d148110b009810026000c90701441c928851500e0320b90701d00004030680818400900c081e005142c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 640722482 1250 640721232 640721251
    0x7050d0f27090c0c0b090105090a1e05120d0b150a050c1009050d110f0705120a061a030705010c0809040207020d120801091503031b21020c131e05 64
    0x14107403280042c004452000e02c80d1070200700c4000042c070400428041150b80801c41c8002400241811003c4035584e502c03035070004200048000014074281007903250f490340307039405c00e0440d0302c100764510035980a5413004070394146040c14101c00003441d0609010b08000f58036065034aa28207140940d0888250b044003180d481135014200c0c00f809007100c3c50194140690065003d40240a1200c0d00540103010350b481c0107810f6042558220340c150b201007042c0084400c1526094103491940300342c40e0600682c0301008050318900700c02000d208100200304000d07a0410f400315014581c48000544800b120410000c0074007100b04400c2c010350800303030003903c0110710141032a0300340380740d03a6941c0403050180320404000480ca2401001583c846001e502e0084200030000d02020f419a01c00400344219080d000c4a007040c078014000070805980038941801900305000c11503955818030017500d81b0303044a1803074461a40d9100702001c08449218240201510b0000805080c1003500c0c508050070b001070081d682c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 640723732 1250 640722482 640722557
    0x1030605100e150307060306120f0303020d020c0a0210020c0a060f05071502181f03021e2808220f06060602010b1201060b040317190507050d0f 63
    0x120302d0220003480c1d004094100c0c40a0100c400841898500646070340900d04050501504205d03203021024800120740d0020b25103a9038840504043c0c01900c10340800400203440001c80041d50784003c0b4070248120310840741e107201400c1c1c1d0482240d81e41c3c10b4004507580034840501c01c01c00d8a0088609607880801420800d041419a844007103032070b0a28000212201e80014080c038512040520011070100c0803152840c1a00b0340c17036824001c0c2003046c0c00d4881499400140480d2040014615100030703c21044002d81d074031110020071242e00311043c038455400310205441040d503401065418424103004e104015600a1883d4815610014400a640841c0c40642e0350b80856540e01811010701304540001c900e102000090000d01c4010249440761039142005c02c0c007109240d501240e0450f50030030400d81050180e40c0d0b10440a204400701e035001c0b203090804540d446074220b0080c2481d64010425500f03811481c880c00d42c0c03010701c0603131044c000035280302e0314020100008001c024811301c001d19460 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 640724982 1250 640723732 640723739
    0x60f0c110a030f1112100207170409021207020c030c1513080f55050a140f06010b0d02040e0a390c211805030d05030103060510 56
    0xa09115064000760b840701c03d0084000d06200c0701c0f0b625003030541e1040e40c80000c10b5a802d010a910380510200041c0c15a03000640c40003800760f6403840705d8200480c109600d50351a50b801240c4025807101ca4581d9400c044031002640c22400462507141e44500a00070b0035007542010704104204001d0700c08690499024002c0240482c96404000003819a28004044802c40007680c20f10704254411418003800d81d000c10f0b40040c9001c3c80300324204481501c1e002c05c0e0203848035a105403410a2004081841c1392941041080c8000050828000350050000444001801940f55101c10480d00c0c0c0201d50742c00303440100542c584000003002200108040141030685540030001c02c140d05136106035a454440c08281c3c007000101042140615041c0c0015082d0120501d07061a0030210300c4811041c80030310300000b02400000c0d96003c4a84810741c04501c032112080c0340207003e02044110040101607000d402140c0c500300020303e019a040c903515802c1c02d5a10316502d000251030014101059207802c9030340013 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 640726232 1250 640724982 640724989
    0x702060d020c0a0605130233070819030b0f100e030f0a020a120b01060f1704051f050123120a150507030b0a051009080d09050301060b04060f0c11 64
    0xa082d00b030111400380107000114100b96050340c03006480c4041828000c0748583c0180d076440210b200340d404243c040307002039000543e4849016840a00b022005c80700265500030406058000c020b0070700d030b110001000c41c200320710407022104080c11264000807488601c802c0d80c81e1881d000050743d02c8500c1d20140248280c1d0100b8204000884004495400a80180114600301d200e41002c3d00b00c190000d000c0c004641c07110300101e1418031a1006022548682e100d51034800c01180900c0e4402e42d2a20080d070810b440d1403a030302c0020b0081110520fa00114000d40c4551501489040b640c3e2041d02d849422050303900022100e1010b105107500032115a40b088801109009600351180940154501d416072040101c051700c2005200c83c0800d880c0c40c0e05070600740e80e10302e46401968020f0350341171079280f800c0300190745005281d009019103105040c1c04036030141d441000c81040d54402c0d00240400d0f9581c60341d011280c0600d0082c000401c0f0281545030f86148659041600caa0081414107112a10030021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 640727482 1250 640726232 640726237
    0xf0c05010b121608031207081005030714010f031b03020901051314091e0f0a0f14060a0e010b040614040909080d0e0d0e0108090c0405131103031c020702060d02 70
    0x280c0480f074108120125010022940d00d600400300300001c1c1d45080c000411b16005643c00400b4401030120790804201d42030101c0c24050301901d0080c0442d5101c035207800303e04251000105040c0d0001b03035004800c15209209000b0030021004024284030034190240341540a50400011141000014840300c05041440c4006a00402a1640011149000364248540000e0081080340000031100d0001c1075201a4221564042440c42c0390f030986454403036580c0003611040e56903003441420220050111304140c0d80070f134041d40c0111003d0f28001c0e901c6013610406102481580c2e003c0c10705010410155000e01d58130107088e0364200034503103483d8992420000b2aa041c4000b55854600480c1059400d08940f0500e800c001c10480107086640c485000140f841d04c00010710340c100000320b804110310440822002002800080c0203100c1c3d80b4003001024aa1041c80900740d4901c02142d580c0000d50401204555249114404118440e508600c400c4041c1d404140100d8000c00701b00121710050195201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 640728732 1250 640727482 640727509
    0x61d01110a0215090d0813060c08180708030d020702271f05131d0d050c010c0306050618030c04050a140109060b0d09021903031206060801060f0c05010b 67
    0x114181c07140280346000f4980350f0b0007240700c010004818180101440c0000300c20706200310130b25101d00c00d95a2004203240e01036466400420403804d0112100340e5641011010b40f01704498480d000c20007002c06031069603140740d4443e07000e03980c00801540800034001d8000308003641c00035003022115003008000b1400e00000c4148079045204403800d005680341d80000c0e140600d451115011a6642840b00140e1203003070718905d150006a5a441c81000c8100074082740000007140c1003611150080501d025120343c3c40300000403100e500e40100c505e5a40e000f4070903030013030780c00252565081c0305080e5030101042d103c1c0c0194030f6140c03050030800c2c01242e840c2c1c092240320300340041011070100030100117030b8640d039010b801081c040ca040c00341c280303d98542c50b416142125a0047e0114800343c1c4c07030001c115031030b49001e40b03407044915104020081c90303005145c105001200c2d04040040a540e00012a0903440030300600001441c0030700b4402101d403142d5003040c840b60144000003020b034652070010303840d1442c046 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 640729982 1250 640728732 640728761
    0xb010b0315030102130b07171306030f0c090b1e131806030b060d080f04081c260405010b0306070f03060b0f070813030b040b0609010803090d061d01 65
    0x1003101c03004854910308000c0300150000d40c101860000d06440301611070056201680010410009200c0150b00d0340207111404a0785035a07030f13007052240f40c40d4958180220300c0468200714034000303203192134452010080700e15031700c034014a400d0040e442550380c4201c1200b507215400d079540b219120700c00801802010421003c0c56030751880c00c0d4100346050501000300c010107180c60810004a00c0308071300e15034419403c4681800016aa25080500c0e024030200c1100812000c1000702e40c0ea40c001507030040215144c1d0b038607540030907502021a035641468100b0003580032074140c4510380255640303030329800510800000c04c2040610300482d01c0d1000407a040c0000901460400001903054407542004e8880001200d1400100100c0e0001f20302c1020001000d004000803900610014446000302941d41300c07003003119509040c1001890958181e68451040c030001000150310000001140e8003158090005804000d00f61584002001e09071040d81280c04110b0300048111401c5c0b0440c110100f521 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 640731232 1250 640729982 640729987
    0x10b0d1d1b01080f160f03020c0708060a1d1005060a051f030606030606091403011b0914060301050f010e0118030c03110303070305041404021c0c080c030c250b010b 72
    0xa0001042c040000d0001c4d0b0f0351030994014450100410345100300000307640d08007980704481e500000c030f0080c403450341c5c0c0440501854101140401000c55064000c0740440300510440511018440ca158030410b092075590b03100d801c1d01202022243c008586c0b251000301200e420070342c1c80300031460340301c00003002d0401300301d04c0902540101d41511036600070300803900d810000c040c03c0c200e01800c030848a01500032400000100300715156803d411001c000f0001982138900945440b10151030310406004444407140101c8651102c0d082003810b680c121070b00101103040322500700b401958400c181a10443c100001c0405070300300b640c0300014400c0154802c44624403000e103103040805200ba03060600341d111340c02c10000c260209038041c0691701521090040f000300e644a10380040c000b4460b14ad00040110540500d40e180b04440d07500c81c540d4032905446080c500d035910885100107110032a190075a500f011300c04101c003000d40d0039510300701c810041140c2c070000c00c0075100c0c541c5141c026404200b0002c0c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 640732482 1250 640731232 640731283
    0x15090302040207240c17040807060e0601030c0506070b0109050406290109050405010302090610030f0f060510080708130507050312041a1207110c130203010617010b0d1d 74
    0x204100141c4414000c0005c0000441c01c560050102d2414020f0f503a8000030080401c1c24800c0c042c080710380d15a488002000804021a030309600d42609200c240c03080d0781042000582c1d404c1c01005c403004540d00c4040000d00303a003000070040061001030404c0c0c030050781d100d024902d58449044087c405000300501045102030103c001880d0b20145e811880c0228101001040140c0307803180500d8009604031011031580102e081c0881c005d02c18100800c580c1e40c10704d0300c1c8000007050759220f1001d40d1015205201c40303d034040300680e4045002c0d980324001406641c001031800f0b80d00804101c03028803d00c141d41506641d90002403034034003048481303103140b00b000800b000b0724110814048003034440d00410504085102050803403201e4010000307010f00c8859400d86e90110028020802003040c02001c41d00401c9152100a000f90030901441020038405018050701145401c003203812100c086e035126203088412641c038000750404048c080800403d92041c2104803000348140308881990381c005844050b003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 640733732 1250 640732482 640732523
    0x10b1909061205030f03090f070303090512060f06060c0321222103110a0801080705030a1e0807080715050105060702030a02120309102f0715090302040207 68
    0x4059006090300072440380b41000244021045c4c075441e1291074019a20307551455441030402c0c08021105500c1c0c02a000c000c002c00d500f114a000c00d075442580c0700252840071054060356034100380c44014981d9144c1c000a159803804400808105212006580c00c000c5104642d8068181c841c290181110910381000f0103000580803542c82e0100e002c0300904d408045403241030f19905680444080c0c2c40381b01c3d40031a41d190094010615500d008900f06503a030031140001014981d0a009081c040d006070100060700d4030700051846405034005040ca101d0980a5420200d0280c502c941110401030600c4041d0105407000c0280c42030038026022154000300103801c1404840381600103510608041c03040c10003503100024600c26140c0d040e280c8281c1d40120324a414914014511043c1c2c1c401c0c506140d5501c0d00343c0c400c022100c0d01c15400300702c13003040005034031240c031402d210ba801d00401d52189030200a00d80741c580c00c0a009010b1800e0090590b0f4a0b40c0124050782e0000d007080e2105840f606922000d0031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 640734982 1250 640733732 640733741
    0x2100212040210030b06250206030910060501110712140a1b0b070c090f06350f031e04210308071d1002031303030807180e010b0a02010b1909 62
    0xc40504e82080350300715000020b0f07868001c04c07100352022500070742151203054088100d01c1c1ea164004000c10344034940b10704080d507030788403500c4d40440c400d0800600140e1075020302c1c241c3c8640440b25004d016207a04085100001c0301d58a401500e1203810b1801952810f03000b4080641c03120f0044411103070ba8410200d485031921102e42c002508100e0812555011980e103064003000c1d034480200100704200d040041802400d00c50300803180c0320900b140c084e0364040305e03294810b07041d211007602004810056402da40d11042d00002a440da6001084403a0380500030311401d005500c420411181485d03141d000c00385000b00b80c40c80d0840e40500741845081496004030010781c2c024068905041c0780860b0451540041c07240320100c40c020a03042c41c144400c58001e000b61114084941084031460b82e480c10b00618000055031182c0c00f092403181c49065102c4003800a405440c01000110700503441c000720041164480003a05d0119543c400d03051096031380c0c0c5030344e4800142207001a07080f0385041181003c1240c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 640736232 1250 640734982 640735009
    0xd060b0a081008120702030a050706080603010b0603041509020111030304050115080606030705011b082706160308040201051c050709080f1c030e060f01030b0606091807021002120402 80
    0x450342041086100702c0042d61200c5900200030860710f85c0950310100e8903001900c4401043c0380503800700480c0959108507624841c2e10114000e1210321080b401344903051000381c0c1c014203100c210020101c0e000c0d60795088510200d10624100d2189014a810603041d07810039681121a0b945980420000300d003e0340880e805001c82c000501003a0038558000382d610107891080d1070610900100c0e031031202017002c207001d40301a0003600b500e94a18900101c40310b00c9c4001200c0040480307001045034040d08000068070321003c18040c151381c1c4013001d41c900350340076400184100c0c1009000c001800700c981c0c2c2c2080c1024050030812000c15981071000025144411b40c1e000036070b003580411840c4154400005440405d4502050501043c03007107100c044000d00a1b1041c000070740d2045009000c540081010745504880c020261501310380c444404110051003051040c0f5440501c5039110421041c4030900543c00540c64012126041004c21044013a6000b03405450828000e02d0200805d50030220106500e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 640737482 1250 640736232 640736251
    0x120b040c0804060905010617030d150609210f061d06160809030403060c050309161406092107030308090f030a080411091918030e01030b04020d060b0a08 67
    0x16861501030081c0030310070040c0041c0125446444000c107110007135009070084c0080031035000c0482440b4007501c2d900d511083d002c0da41c03540f800030340c054084082d11182042e2221699400d00c0340c0d10f0026a50080c08080100c1502c3c1c48007500e007400010034030140c07042490711030400404d804104502884a160003290b041080b030304400104407203001c0c03046400795002880d0402610325140d01c0c062134518007803600001d040c280340c820080ca8503030b0008055841003200c0304c2203409007003941040744003a0070396104000c200d803907210055059103455000381400b000027400e218180f100a01c0003440504d403840340b12a881c1c202e0042031040c1940108100d5001c80440010000d0380c0050309229601d10440240808201c441004a0304100f0840324203405000000e0102e14941812000c03070740d03188061000d1900702e03854110b404c80009075013500c034a01c1d150152a40d1000d813101000541c0540081c01c0034641c40f5508204042c54040e1074070402010f0556510b840341c549101ca00080c14500300905416403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 640738732 1250 640737482 640737491
    0x1201090f0507050910110a0302012c1506010c061514030105090607030c180303021b010c02010804020105030c04030818040e1629030703090309150c0b06061603120b04 73
    0x454001d011603007020425103041216544080e0304a8246ca13020302110403501503a840e00d400d0550540260f00e0602d1585c803101c04814a0504038401c1c0c801c4950510340640102c03414260b4050000d0b95140e010070181010003500031550b440b94101c4a10304d8510910161915060003404200045030301400d02c142e00807c043c0c1041c0d0100303607641070010080000c042e11516502c0c62184a81c0680714400c00c2d02c451080e0307a80d224a0040e4071241d0841010790749205c178000d8141c0780d601c507484000c405c07501070310b0301006503e50f9001141c00d58001080304600382d0040200000041000004000801000741410080200c1c082000107503046200d12044c02c1d84041840d0b8983d001d2150480201c0e11001520000d4142000719110030800c0309295820350368001c0100229690140c10154901c0d1213681c0316502c0350303100c0d9225042e041c100100e4000041c440c0481c200019840c419007030300504010009420613803907040c00400e5032134400d0304400181c01c5801c80c0d0b44010b801e00a448103408125018030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 640739982 1250 640738732 640738741
    0xa0f0507020115120b040f0204060803070803250c230f0a060b04090c092309011505090c0d2f0d05060a03020d02010e04060317132315040b1201090f05 66
    0x100d6a40c005000904203c0d0300c02101f10841d50b4982c440030044c5442c0c4240c039112041401c107041183c2040304c48040380725440c100c03008420981415a41000440c0d1581c5404540ea82c0302c460100c0c10842801c42c1c01440d80300301c00c50345141040103002540c011170042840450394a03009061f150f8000d0114011403d00c410840010103400040c0251000c4110000c6d41076452400203525190607101ca150038912803040c803c040b201904102810709010715403881955840e024400111800c0321500d042d403100b80130514800b40706801008048450711003901036565280449213031011040d207040742c0030100040b102480c0c0c282d03006642d0f21030011a0b003082d07a03900d0b64000c1144a101352034028108088402118119911a071100010f5600320300d03a9042c110305074900a00e030b50f01424900120103910f801c0043c010510b03a4050146001606140704403071140b805000250031888110b00369003009000115003084100050260780b80e441c1440d0100794541706d003800445010b00f100140706401e060411 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 640741232 1250 640739982 640739993
    0x11d0721020d020d030201201206030c0109060c1104140702060903040305070909021207030c0504240509040c0306020c100f1514060c03030103051e0a03090e0a0f050702011512 77
    0x141042c0b42c056400a20703a5140d890100d00400104810721402013440c0901407007070380210007400d0155017940c4001980c2c0c4840c020560381e060380340d01c45400128801c1003489031074450251220403c2c81a0410b03001240404009015a600b0445140040d1054800c001505a0400100390070040d4180554078150558a5483d01e0300018003400ca013154540000d03030110b440c1d840ca411601520301007600d980c0b0344c403481c0c44017030038031284a050f00c00d5080000c0701e465048118000094200a80100c02da1249448140b208060740200142c1c1c907125090000800715030389000030041e049801c4003030a5000351025640f02242d5103c410041003038940044030035041e000b9079400050306d0208103206d10070040100001c64501c9000c0c42d60185000200c000002c01800040300c0e0043e0001c1c0c0b240c2c000c0c1d01299481c0954460500c0300140014001d01010001d0851020009411038242000820807480070b0320b81c6810399000355190300c0140e42d0385210900c00c01e844c940c400f028015426025070b036004142c80d1b4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 640742482 1250 640741232 640741249
    0x40209012103030b121005010915050a0e0c2206021e031204140d0507150e060403030b0102010b0d030c0611031303050d02210f1b1605011d072102 64
    0x103040c0f554500c5903c04581e50320650050600d092070464448091452031100503103428485d201e80c1908101c203042d0403000498001d020b0310b802409500d040c40c42c1c0017081c65a41000750030a401400708008624801c03851004501d50600307a80301d00d146c00d5292402c0245400e0750754401d05440c0960802035003041030b0210443c1c8040a900c0140286c40c0c841c0d04010162805041410201d84074200c40c0c4040190802c010301031643c042e0b003802d98a503002c0c1034082d05680b00b02d585010755805c02000034001900a60250448000c188000038420030024046402c1c500304003010703000309d203200308200c042011a0050075240030038031350002e0860902400c1031884403002c410040500a0104200181580700c1e0305880b840c4010030202e41c2c2c2ca1070b4841200300b0340c61080e00c80c1340a68800300002002507070206801e240301e800880005140c40903404180322a030083e8a401c44840d502c84540700ca504540d040e005280c04030000103020010302d0030a403da40000042e55020b1500803034080e0201680e100b212 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 640743732 1250 640742482 640742549
    0x1202010b061215220b040204030c230d08040e1806161110050603070f120609020f0909160f030b060907120507020a0c05030a0b0c0f040305011404020901 67
    0x41400c2c4035103485044000b0310840c920740e203070480003140003c0c22050600e0500000010810010020610305605010680c800c50102500110b0202c00c20429060b012140d4500424686400800302d80c012001510003c2130041c141e5200360702003028040501341001c0e00382c01540d901c2801c01c1300d0560f501201d4449200801c21600403807070f4210712002501034003400d4210030607e016251000261906c070b9000300300070703202103020340319858000c191303e40b0b205180d10075585060400d4140f400d82d580c2e2030700544180d00b0101e8214090b100301403995180c402c0082c0c080c003902d00207010702c000048168501159030758804c40740c400107080204042036070301e00b01d9038010345d060b525801c21380d964040984080d0011825440054581001c000249502060300403185110318840c49a165030b4100305036862507500400f50140c3d2615010405450f9240c008101c0e407c22001d605007880d54030384495084414041100d0103050484040004603d8000720007405404814a5004110003a10b20341320702c40c04200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 640744982 1250 640743732 640743757
    0x3090c03141212010e130308190e0d0806120309150f070c0e0403080c03070503130c18140a38150a11120a050f0f07050a1202010b06 58
    0x100c114401003414010305828001110409075a1000c0ea03000740f4000000f40701d02c1c16144844804201a4504d15400000d0b158155840480703a0301c0d00d2881001118110381014000e0340e54040c0c1c0b00110109010381100c04205459203da641b80460038040345822101c0380454541003082031403d240d0711400e0f0000d5101c844c1c811a6100c8481e0202030006100d1001c002d0030071050200b0010302e42c424a10841c2c8524429a1798842a80f0b4102c2c0c1c054041c0000c1d51940007140081c000151003401c0d10200b0b680c100e0003198480b00c0681e4424034407121901c80071500c03808545400090849002c030b00d500079002101414108040c1c1022100940c10003214255100140606642c8010782c80c641c05407002c3d5540003c25041c0598610030785071300154030001941c0c000ca4541c000326001c404000c2450400d24024552945ca84040804203c45030f91084010a540c44000d11203d42c001e1507441c040e00407284140e0043c45071540a04003c41e2820039202c258046a0614900b030125450b045c0a5400120000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 640746232 1250 640744982 640745003
    0x203040204060801020f04060e0906090105100c120302041a0405010f0c05010f1e050a061a0d02040b03040c050a140d140a1a0a0c02033406090b040605010603090c03 72
    0x2840041c025101030342c80120f6560004c140050400d50f05c900a204499282e16108901c19034102840300c1c0081c21164203500c01425801004981011500c14052405615201c0a050750301d0742c07018514100c000b800b00003c1d6020906000328600c21491a01c3c4182d1304117400d0400b031030400002d00784602d0310550010840410380c1207042240941200c02014645a03090100f4011440c50200000c0c1080e01d00144600380001708091008502c0b44009586410300c8070700300032011601500a680c802070045070034079420080050100b0714a000341d40994403a990030380c0c080745440204141c4158507000107488071204544c170002c3e40c3e00c8040081045602c4000184400d0346038103610f0620940c01806810030540c9440e440343c0001104010f0711540444c03104105a0340500405c981d07900440030880c00c08103000c032100c4a01020782055070281070211900c1c0710144140e941c0c50003550008402180d41504000034003003005120700038180544074918003041114180d803120090703d043c0703101c0a0b2160080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 640747482 1250 640746232 640746241
    0x50403050c10180608062803030503090a020a0e090124211208060306240d051f020c060610020c130f090506092b030c09030b090c031b010507060203 65
    0x503d1500e400d06500400d0300009699004050031580085501911815101060035003a181401d10340c6018910031188000341030071682c05998541c400380642a0512a01d646d000069550603000c401401a100c41442c0c01c0c2041044242500c0c0303026800900380d079032400e85103070000b1101c060b002210054828008885c58110040202078000e00001c0c08445c05c269216070b1050308040d1042c01102c0036021130310036035a000c02e04110000801c08548021800b8103034110185095040325217824060340c1950200c00e01290840031003062086110f00c00780d00880d059890368001e202031540032009940b040310849641c80000d4036031a0051300a441460180d00d0038100362210381c48510840814202003051580c0fa09003581e8490307044514034154890814007000c841140841c40424984140c09400c0031001c80809501404044004c0010004643d000001090040d2407203409010601d0152250115403824182000040d64559666007140800b5414503648a0201c584103134000302c1c0140c69844 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 640748732 1250 640747482 640747487
    0x30d05091801060c0c081b0103050a021201170105150904080714060108010209150901050f280e010f0c0b0a02090f2707030603080a05070501090605040c0501020706050403050c10 78
    0xc144608140300701107000046021604100507001c40350148404030403e903030344e04a42d540c5824141d4040140f440c01041d071049075001360062030304804c0120015003011100260302001b8202641b085078a8a840c0b041714110301e40a12456420158690314140718542450100d406060003070710040c840580011140d091015001c50141034a0101050b6400303960341d98070b8103010750002c0d1400e0344141c4146407180e58145a020031150540d1060710780c94206079141d0140f141c0c5800c5021850040015000300c003a503000a280c441e0803007201507c4465140700003000040c4418401520f8005020366041e4000c041800341c0c90705c0b68030005070400541c0d1080703050045800122651030b02600a0803090b81d220100d031200c0049a0843e1072a0741120640e507510b4001c80540349240300180c0a00d03070810024000a1052009008482c000d01c00400c2041d802c0c0e60705811600100c0f4250781c100d01c070003c244025a414081760009010a2900c6400e060854031803689403034681c0e084922a000c030b0320b0403020460 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 640749982 1250 640748732 640748749
    0x10b0a020f0a0b0109060e0610030b010903061416110a02040b0109171e06130b06010e19050f031609090f05060c040501030507210911060c07140906030d0509 69
    0x20208802c0e292004154642142912000c3c0a003806542c180300b404204503800b041c0d9a03200e10401071030041c010300c0095080c0e0007800341602c0e55040020b02c20012000c01c4050051102c1140545460f20061604a20700034030f03041c02c81400310402500524204101e0400210096000c4d012180042d010810000594440343c0642c4112401c1c50300d462070191706407002c600d42d403c9080f02c400c10707003804200c404101c0d240c000444003c1030120101c21807034013254404400da644000181070100c2d803c0943d100041100800240c00d01240390010710500403428400401d601e0081c040c0c00418181a003501d10802008540c000c4408041d42c800c2050306001844600e04c4480740c02c141078841a05020840354030b41d40c0140641c2d80400c0c02d00c0701090229100300c2d0104c540340c0c4108002d00720341100740705640c081c0c281f6034800d85d8140014801810140e440100601c03510b440080248413013840c140980c012103244000040c441c540c0001000307415140420f081110141c0c81c070303100390754907490740c0006c1060 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 640751232 1250 640749982 640750003
    0x809071a0309060717012d0b0a0f02070605090405060402070206031003050c0d12120b03030408283302040603050f0f100b090d080705010203220803010b0a02 69
    0x21202a003582000303036060007140900514003e440c40d0b0741d95150251226854440c0100c41011042e004001c105105440000c80800041c103a440501c0c0c84109034034403e116810001c40ba09000445a55058000219200740e00b002d0014286a900d400c1c4090a5409104841d50190340c486001a0543d541c683c1100c00280d4002e00c0191a4140021543c05030034090004503594414800003614901d04014444039503903200324015a8000304080813034009450750781c40403001d502c07000f4480d501d503401c1c00a80050700100300108406038900140d40400702d44401203281c294000e280c150003203081090005803951601c1e00420f900342000220049507880e4040300f4003043e01c0801c000c140e00b40e0540212f030242e00906c02c00200303901c5d07541c5280d0018106443c00341c01461000420030202180384060f201b819030003020504851143e44503103005511001c0211800d0f540001001a01008640000750f412010a040d1000f40d042d5500d00c2d04c030744818087c0755001140400d40d806564400c2110203540c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 640752482 1250 640751232 640751249
    0x1d03131701203a0f0e1f0b13050402100509030a110301090b040803070f0e0310050603070e150109080c0a140d0507030c0608013f0203010f1a040c09030f0206071a01140a0303020a03080907 82
    0xa17400540410300003407002b5942248240c02030381002180c94818025248a0740005025100045aaa83d403903040c1411054954042d5204c1c0d00c041d001c41d40500042c0e210724020424182d98ac508070100420f04c4816031074840a0001c0c0b000b5140d45034130005441c8099400e0282d0009150f2103000001e460804950b100b200120a4a01082101e507405600921101820b0300d610043c41d4858100c10303212000c224155401021380306081100c003034040143c0d00f04460142c070f41003005100703880311400c5c60b0898006179010b028002d020480b0a41c0b101e45d1600400310411000c0f1040701c801640000240e100c042c611030400e500c00309900358114840c40391030b4554014002c10402002e00441000350150203400d00058051403e01c2034213042c10301a42c10904070a0740d030703141002e0443e41c44198007108140d043c1c0e0040e00502115002a05048551030401c074031041081240d1f14001203400200003503243d060103840300200420000ba000075441526681c141030062066484130742c45450845658001c0d03d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 640753732 1250 640752482 640752499
    0x120302030403120801051c08040803070503030103050606060408030d05060a090603060f050a0b2101090c24021507031d03131701203a0f0e1f0b 63
    0x4158001009004072031080700c01004900600314140c1d00c0c403c3c03d20895800600c000054160400040059a901031103038547c10b090545560005240d60013401088441e6800040140184503003046080d9004001b100c45926040c2080300781a240e0041500c00c4d1608e94854020034416a03c6c1050390300589103280c403c103c030076503d080c0503026015031080002550b1900000c200540400c0c0544d0b03020000160020310250003c4504d0640500801e07109d0030203544e41c1520b000001c900741c02010013403418151951031400c0c500d840320192001c1c040240250340c482203408800401d1035810b56400051402c00103000c0e1000e1603c82c550000180100702c650000003030182106e91750000810544803000303c0c94024070283c0d81814202c0712803800c004c012824106560120040410040c50900742004810f0078004410000c0b02d9000d2044510000003401d42c420011351346500c4c4211030f6040c01201040c000c0d00710030320050303840d01240900015030680c0a4170111030200e590300540340166004d8031041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 640754982 1250 640753732 640753769
    0xf0d0b090c0a052817090c0609130204030b04050607081e22141f0b0d06180605010303080a110306090105010f112512050c090a06080f06160f05030f10 66
    0x500502080d06005e20072104d09000c45c804000c00a8170854141014008034030303011700c2004002080394200d550031841d030b0b000c100c00320020390f014002c00d000340d200f80028460b504000c0c1018200280040501500c03541d00105035109192022001e40c0080140380c0c28588034141c3d00306a03100b1145802c01400101d490a40f4a85103030703001500c1c2c1c80081520100d20941c1c4010b08450060b1040c10b03603c9c1e0740c00b0207400e0a10012649550206038040944034901d20100782d607960351419101d0983c0b065011805103020010b5200d4903009454407003000c0c8180516600e8464000f40e09820107008490400c4005000654400e0089070f2090710100100c0440d2003245100e0b100c0c41003400c0307003840d543c140c0358030400c0013030b520100395402c00c407440e40f19028121450a01080c40344c40301000300101d251688884000030702900500c6400e20b56100f8001810139490000107410b000014010f281040003540d000c04000e01c0c7d0f0160540781c009540101c070341c00780d444403810715000c40ca01d50810b4440006a84294 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 640756232 1250 640754982 640754987
    0xc06090c0801320c130602010b0103180b240303040e0105030c1207060e0310060306020706050f0709051203132d12150608030f0d0b090c0a0528 63
    0x15011030708400000e201c10f20a00d186160950f072260108129030f045114842e000740141e00e140c550090203d402107040c03560b008402c03840303400d55500a4003d81d555146040ca076503814040d2a10b207540c0507a9080d58034050395a1022171150040c03201000600844030485110b1125180301c003110001000c072a00c59032140000c01f03240f102803080d00d21a00c03c0d08203d0f440b81c107203d0f0f1100900101000500001c03403030080195611520000b6a56042c0584003840400c01001c0c400c0c54043c41c02003400680b960820714091040b520040c2544241e403c04808000030254440485400d4610558a103000340308014030755841c60203480c40300b00d00481c03070050100d80305266030038040300b91150f40e02d2a81c104525092801d80ca80b00c2d03026100b00c1d04020301c501e6000c00c42e030350300700354201e280e01100250740e6650b641c1286c1107800004038202c0e000390010b049402d5401d6030103003804101e022a0720340c8007400e01700c02d20800e61144017484418000e012442800c1c00d21101c2d10545001418003400840c00e4140000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 640757482 1250 640756232 640756253
    0x50a03201809220c0b190e0a0503070612020f040308270d0b06060d1b03060b0301260708060108010c0f0c0b0f0c0f0d0b090108030f16030c0609 63
    0x440440040c604804598500541c100340541d0a0303c0303a00b0707540d44000d800055482169801614031600c0484000340300c40308a030040c83c40344d039020a180712180008400800000e13924a2a510800d10780c2014841e9030b5001c2200c2c1d04072000e604010400000000741527010b40220380c489000c100c40490b000041c000c0b04002890f07550303149641301c05202c200c84011403a81c244202302c15040031400100c000040e8200c40426007200c0d00400c000d0510210100c000e0546840da0324444031812005260701c40c2039014042c901c090b058021440c0e04660614210a04411440080b241e03a07a42c5155044080d48050090030082c01d18241580c40f5076846480c0f0b580a0450724200c1000100d0b0240001250340c42400c1c06403a85500c8500100386858201c41d82141748006803044050741e6042004c5595103420307500814101c00d0001004ca4045500744c20400351035816400041103400820401e00342c10b00d00d504691590010700e04200c2044540d080480f0312202480b401491039240050090502c002c2a65 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 640758732 1250 640757482 640757497
    0x20c0c0301200703081305010e07030210050c0c0405100b0406080403200c0f1908240c0403030c060b040204060e030d050405061b010e12120705070c0501050a0320 71
    0x1e001032981c1030a82d050003045030200b001004024002d80c00042d1241680701d0300002640b003001c003a04043c0c0c590900311103155502c2c1d131180e84a50001c00c21400c144000c600b0b0b005032818a01d080041c65410140c45928508025101d0365075240050010070201102d600a00700c0814110345680d16808041d000110644043e80403801c46004c04140424042c100c2054000141c05072400c40d07403036014041e014084051240e03011122106401a441c6582071074002801e410008022402c15211000b060159201980c50181b05043c208118641e08000b03c900312a410700c2d0102030544941442001815071406965105000060024000b680700746040c80081045040e140b44c200300c4d4a0a036003a105901c5080c0d00702d0010711120b090300c0000009030400006400c0041201610143c0c1241442c40c3c03015540c1e42c410380851901d81c04140401100d51241e020308000e86004015101c002101010b849264108140058040d14480c440e400511030311350364000c48085143e420300020160b030050030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 640759982 1250 640758732 640758739
    0x17040812070807020708010207020a0b03281a0321030c071b0314010c08060127030305070c06020d0e04020a0e12030915130e0c0f0a09050909061e060112020c0c 70
    0x30000705040303d042c0308527140664000c00c17601c142403404a0720f1711303181c000030310000b4581013403d003c0078081e02c00e403c00d0350500c824000000354090741c01d520121000304c2d01e0400780254031059100c055081e004900308800700203100c5817a00c0c2d5894005059161048940045c07032185010750805034552f000034550140d9110380c0c0c404c000c2a8814610900722004001031000040c8040040394465020305500005600e0103085140442c90251100b403005103294030032000030f04009455403c1c010100140d90183c40d40d40302a25001c04000c00050106204030035644c411540090740e05004d03406042c2d641e403581c501404114140281c5041e541c0c0300d03040350901900681003400c1d04081c00029a040f15141c1400c10900803031541411941e4656100080004800c50f0040144681070300403140034001d1407402d030b9520041213040c07405100038284054403012459108a0910079192000d0201c2028107006041c080e0740b030380d1800f0040b114410410400003426200141a401594001c90200701074103055 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 640761232 1250 640759982 640759993
    0xc070501080a0504120516080301120209010e04052a0d0b010321021f060506070f051b010c0b060120011506020a0f0303020c010603080c060403020705040c1704081207080702 76
    0xb912a4400d484084500808022420310b4204030280580003418070761130005810482021195030740802da134000e811031694551999494011882c4c02098280541b110310019206820169101c40e40d0b04221200c610300303500d0509080c5000000448039000b03d01d4001c1c2040030129450402e114008401e000540b034500301f1070119852040049261600952560b004007103600d401120030b240e55180c0e03510b401105454840004542c0d580d200508100c03401242a40341c020030514045181249441e0b0300a400c908050190800740e0300025900041904070800da00340d0b41d1080012200b50704615046800c0100000c081c42c450b0070150310201004500c44001c0c113081351180c0052303a0350040c02400420100c240452440064805e8020713182300d00c41d010010a250785c5035514440540c2104c4034000301c13a03000e0700800c401c3c5a81000600003d00090300d08202d040c0300104010f283da44280c4641022610301d1000c6030400c1841021900c06d00500c5d8a065098140741400038044031059941c8401071042c0d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 640762482 1250 640761232 640761241
    0x7030b13121d06040f050f0604080312190c080103061e2909151207051003020a030f06050a0b09130507030e0706080903071401020d09080915030c040902090d080c07050108 75
    0x700c421903056179000001005080d15080400092140341104a0f40114040c40300084064081029200003852203204401a10308403c03182c03840102d51416038082e508010220300f0b600d8101e4402ca05581e00301e607000c141c1c40a842000800344502d90341c280d26941c030380980c12103000d10048004d803960368003c1d155078082e0b07804410810242401e44030212030704803099220f24585050300d68450b040340c203101560941607642c80041c4000b4850110307200440d400003842040d4550512611700c10034401c3c00100681410000811850301003401000940c030710010344a5115a6807446024401c800d00d0b070140118500401c0050280c10f0f04003400c0040e06c14400081042400b9010300303445086014001c43c14180303980c40e1003a00c8070b1642e40e1403440355401c000702c840c0300b2124094501c600c1d00a10307600f90b5840c00c1609020200410603102c0801d10790a00034070814081c40310850b0126540c4080150321140920300084c03400011000003030110000007032808007441e0100b800b808450098a03000b00d41d03070303a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 640763732 1250 640762482 640762489
    0x3100504050f060103150335120106110102090a030c0306110f120a06080307030914011d090a0b09100e160507060c021609020c06090703030207030b13121d 68
    0xd042d601d200481059500140d410b52182d40841c0501d202c042d61080d07241d40c0c90b00ca00d00803074520340c1c541d080f800c0c02c000c00b41c01d42c004d00010003071112070164200d031500a000084d0b243d24081800343c0820040008421920302d2000d4042d51001c02000f001c40401907540e07c1e01c3c81c07820f6018401200c444d0304026802010b4003039101502c0000c0411108146000e00c2e0400700c110404004082420b1255501001b24000000300090b151152094466002ca142813100d900c122483c20b110960400c598000c0505915200c66808102c01c08261103080b0141c450b071036184040c103848a015178100040100300007140c1c5101c2c42c010304482c03c0c4941c1500c90b8940070b0501c460039511021620100e01304010500000c1d069034030842c0c681e00365106039103c158941c402c000341c1ba00c080d44942d1482d43c0214101036402d40a10a8a4016415500402440740385a40c003a40f503041c40d11014003000c0085c0b0004017840d21700c4c0c0d59034504030b9000300d4250325a1516100a00024440c00c89205450a08a2414150304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 640764982 1250 640763732 640763741
    0x2030d0c030507080c12030103030f030f05071b05013215060702092e0303030e210d090515071d130915060e040209100e01050d0503190503100504 64
    0x2074040da40c90b0710f041915201c21203030341d100c807a5a940354071540f0308012609501c072000d0341c0a513100341d0308d8014800da042401000d07148401040165545850144042c2580041a002c100001c032003645984040908090b401803800924000c00d0314041840207030310007001c1c10000c00348096025410700c16103e4103201c03040c0320b015401064202c0d2042242001518000d80c3e001d50082031443d590301c224281160003030b503e00f48000748a45486001506108050b018000c0b080d800124034000c4c040030b00d004400c000c210301500c84031859001c0003e00c4961412458000300105074101044914810766180c0304880e880c0704441c1c101c0001c0c240760b031006031183c01420141e00c0020003041100460034000003c0c005096940007242d5543c10610f1151401c0000d0242d14001e0803180460905031515006000d0b9005000b0036501c1d10102007e414040c821081404034107490707043c1e0f00c0d802418941e14101c0d00d14880c05125110307460700c0c0c8020f140c240c0c0d03101d0015813086110320030f00038020390381d8414482945c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 640766232 1250 640764982 640765007
    0xe0610031703160e031c0824090708040c1d10080610030308070c02040e030306030606010c0b040609080427060b16060c210209030d0e01081602030c030d020702030d 72
    0x1908181c3d41e1020591080d441081094030003400d50b5841841c0d503102440b42c035031350858079010840d040104040140d1f01511400c1e04030b03030f5402413403100911900003201010010550f0061048000c0803e0501007070003507100190010842c103aa6900c6a44402c00210703504031203a0020300001c0b580810200030100302c11340520700810b95401d10b142150f80550b05200000e26103810000035401c02e00c00340e5158081c0e074102040031005196213003000000c0c0741c10141c000b0710b89814000c0305100c0c100014401400184e009800130340c005140c0082d850450103910980d408480c801c2004070007200e0150f80124824206031007400c003000081d43d00d00e40c00c0f0003801420740801d0413500b00d103c400c0c00708940d070f0002c0c80342030a00d141c400d00008114a0a40d100081518254041c80d80810903600600301000611844803ca040003000d881c0c3d040002404840000c10410f8507100d03401111124a000b041501c555080c0e000590380c0f500c3c01654914005d40042109920a01c0380c1001d500010340500c03461501c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 640767482 1250 640766232 640766251
    0x108010b090a090b2e0902180306010302060304060c0527030f0601050a060305060f101106010501090b0708071b090e1903080c0a020304180204290414040e0610031703 73
    0x45a65151082d00e00200b4048120400307100345d000c100d04243d00c0c50308040174040745d00740140c840c0c40414001001800340d28600e07010350311800040c80035982d038074150b170707841f56000780003007841110860121000e005001c012000002d0120407240032026220340310f0210321058003158418144418bd56540701428030031507400000039070052001300d109801503940405c000e030504006da1900300201b105400700b860f40600180c02e4a10700344031840107014450060500740307808881c0d141489004001c1e03205e01c2c08024010a070002e04581008808400711001c4480e50101250b80e9075589604800760980b00800c1a007402a01c1111511203207181803003000541580e0b90021360781d50984000c0460703000119580079884140400100c4000d07626049240c1401103e001da1154a40000c20b08444544c128200c5940d100c5040c003c4018032013801e4030201d8802060030083c02c2100b10210300140107031400692a40220005c200407260344003180c2048a108031340108140440d5400015507002c01d5481006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 640768732 1250 640767482 640767503
    0x51905060313021c0506010f090203071403040312050f1801151203020f0709020a030c0201090312050c0d060e1608150d0311030a0804050f0c09040b1302090108010b090a09 75
    0xc00c000354600030b40d103052000d80b90343c1c0f2001c1d90140314a062403c40e44d0488055000f6030041c810480440e4805e0014043e031081981541800350300503080c45110961800c4480c0044009402d061140f01c6440703051b203003c0c0c420805030800c0c2e020205045400c9503490030017042c000e6140c0c0380030b2052054106010b160080300d40154148102c01002c1d045092060b000c61040002403c0510b400740400c500804506c40016601e076800c001c05402d484c011001c0800356403403c0810300c00300b9048420000701002c0b00c280000c05035110010328206e8001e0608803022145404804200020407905240c01440c0065807680d03200c5001d84220360284080b6641e2024824001801c0d01500342141c0d012001ca1103030800b890724400d048106455500400c0320007000900d028244400d022003070000e03105014807200901800c070b0b8864081a1a824080c00040014940c603001846020045840d44d940c45e500501034180ca595411540d40038100d80700d061384c440c0501101003400c60406114500913145d00c04080710 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 640769982 1250 640768732 640768741
    0x30414062805100503030a02070303030b18180f0a0b1909020d060b0112020a080709150207120f060e1b0d03170604090606060f0201150b0f0c03040e010902040519050603 74
    0x2001e002c015021010380c202284010500307035403d001900d00030310b507580103003020303465030800074191030a500341c4a00403032881030920b01003048402d00ca580000c121081540d0100c1c1c0c0c00c1032618140e0200400107136401384001c14400c00040c02001030243c6a620140300800360b011603803000f00d03505440c000358031030809507042c40090015004000300c100141080030760420b80e442c450080c2e9110f01c00040000e5005000c11455a030070180c0b01000e40b1181258062003c84414080e44d2940140118039018810354130300c0d410048014450700040c1d030300c5901880081100032119558880c0140c6400402e5900354000c031443c10308101100352250503558841d00034044950340c6855010243ca8507400980710500741d40407580074004c40d03001380b0b220303560f980c1e003041100c1d8000c1c2140c020001034204544010010070101940d40f0075a258030301410b00b00ca9035100d0080803140746100f80d5100c03134001c08180f00001039a00f0207070301400845e50191294240d9020050780a00c014009001d015404042840400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 640771232 1250 640769982 640770061
    0x40b010e09040503120f0a0f0e1009020307030507060504062d0e0f040905030d111305060a050c07090f0b09070f140702060706091101020613020d11040203041406 71
    0xc42c0c0003800303001540d181041c1200300c01c0505900b16aa035004009000c01c1c4150000f144c402c52405d5003440b9820040d4610340f02c100c5480d1a20741400341042ba4640300b940c0d082d560b080c400c134001194045d0071648429662000a0042d80041c410800410301c3c0c20000c1e0b41001e22803600300060a100d0400c45039103000107030107480c0d0184105131a50000101000b14485451f01d12a250906028000460721342a0406005041e641e450080505c0494140715000401e800c2050100586004030b03840c5448011210048460b40190b0b0f02503c8188601000040e940c2007075030011103a801004010301074804180140042410143e61200015007006000030040b842250101e00200a810280c1e10307261144d00000c0c1e40d900142420b03103040b96503a000008200c1c580065465204d4280041e1180d0f140c44503d0440300c0c450b680000c1c0c0a4501015020100140383c4040030320310382c000703004640b0780c105810804c42c601034070000c00f8500c0c421000462415030b000c1400c0042510030b4220301440c0039118890 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 640772482 1250 640771232 640771249
    0x50f0406031d0d020f0d030e07030b0604320703092102010b0d03080f010801051b0307020a170c0f01060803071b030807080705120f030f13120914040b010e 68
    0x7000b12000c0d0403140c40352900710901c44011044141d034001c110907540d03200303407a0912204441ca50149403800e42c403d98207590200d4554202c0341c12030400e04030b90b0741d04c50205000d03244420251032800c0a99180354042c0161514031010440c01c10b01d132600f10f41d5550825000c41d505054080e00b03007900b54030503542c02d4843d0920303070b9880f01c0688008a183e04910001c10078000711200110041790b00c00e4100000f0a041c1100240103107180d000a01c071504007000c0e90003045c008981d442030310030000000541114020446590081e0f84081600b18018660002c5520ba402000113030039140100b01001a40a070140210000d4a40c55070145150045503520050350011140f0101030005030703407a000005ca80d004000d07015150040c4e018543e1001c00340307003190524841e00300b25140d07010140301014401d11403106a84e8030a8031500d042c0016115021490110707000301e10003c10550354a800200c500f94410008000c8825480d0100d4885003244100b10079100350352a4980000c101c4101140145001c0701d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 640773732 1250 640772482 640772501
    0xf070605030606070f1a0c0c01050a060605040e0703020c06010f03060506011701050609150a0201060602160e06220c030b2b03081e0108010603030e030c150c0106090f0b03060601050f040603 83
    0x8903000c070b41e1800240f40c00a0982141c50381d202a6000c9003940b08c1d150300780074842c1d003d0750154042000908158001c0c003d03004034080c40305000003842c0010001b41c06541203030990000b044c119290703583c0d07402c156a046142d90000700d0310541000042192713035005607191003092130600d25070801c503820705041c4a5690429040c40d6848a40010080110060000180000c041d2070b400415098240701020707107080708003260b80901d010721035800c00100b0b129950f10b60f000705d01218a4404011200c00b8140f1a800013050000450701d48480c1000ca5501588842841e80c800d9030309a0b4642d00d040780c106e9140c000b0302c14070a0001074402c81080060310038840280d0000d40c0b5000e10418030303030002c1600c0c50450260070401442e2764446040c424160400c0300c2e040b45c6001140149000e004940101e5084114000c034004580004200e80c54007030002e421040140c6406402040000c9076104003074060310000111900900804012a00b1540300d1790403542d44041d1400f0503403406144c0541100181521003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 640774982 1250 640773732 640773743
    0x218070c0618020109151d210c0f032107050304031403040306060b0306011d01090504020706090611030405030318010b10110606030d120f060b07050f070605030606070f 74
    0x42640001c00600ca04a4400080220008a0045480050134a04240d040001004404c117800c0100a170300c10500c034400e8010350040b81340b0607801da002c03c03080c1d00704440b8985d180c0d9a42818a6609030002801c0503044822101d000300f41480c02c00741600c60101c00405803482e0201d038841504030b2003400041c0340d034038810300459103066620784550349804803a60031040313039400c0001c080052104a0244a000c1c0002c03294aa15500b4240000380c940c0c094201c0250b843c80b02540220680da0080310303010024003020380305542c0c5100c28a011001420280c40c102e0f091072500c081e1588240c3c1e8001680c0c0f28950103c01036207143c4a40703a241c03102c000300485600543d0740352080d198881e140d604900030100c900c2e88491880805030700b60340b0304000700285214000c0d80084100700050b41e1017002c1c881c00030600396000034030b400301c01d50100240ca529000010310901c0002d00342c00700500003441e40704498000341510021074458408072928801030780d01a900003414082e07907000c610642c209540051185 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 640776232 1250 640774982 640774997
    0x1807050906060d06080a050d0201020405090f090106080601060c210f2007090207051009022206090207052a060304021215161805030703081b0a0f11040207021807 71
    0x8401241914959000445c1a03001000300d00c00b08402004610301c0c20f00a40000d506040c10000803800562000f0452010451100301042d03480c00c2c00e41c09100a011901c09544081da12540064008919220700311403014140c0d00c0303030400d01c0c20b907442a4180025680d4511000f415000100d40141c48a5490440c06661044500e2281070402000e001812002c1b005a10764407035040c60350400902d0700800b440301d0704288484006a589409081e0854860a10b40c090031300d10310443c1c4010b20b51034103c024040d10026612040c404c0000740003881c51a00d2400078030080440040c201d04801e800c2403950014420300200c2e00520300f0003441d0203003d40130780c11604007804192110010301c10669106032101c5554900280c40e40c2c6c860545c2c44c1080988600005123407138100840d58035207042c400a0205500840d00c040b100d1782c0309001c280c803030380030303c040700c18440d0356017000202c1c900c0d200011523400980e034900002d02d04085c02512413081d00180000000354403850354013549170004100713000b0020342c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 640777482 1250 640776232 640776247
    0x21020f0a08060a1e0e0a1a090c13030b180708070b1e0d06080d02071809032d08060f010c0303110904060803030609010909051902010c0c090f05180705090606 69
    0x5000c441d01c030341391089491100c0d52814080b1a1400400351002c0c1e1010b003005482c080780c607030010140032180b0701600c6020141d0340f800d42c2540c10340106580443c01c0c0742090000000d100000d007280b03008130f000180040d50f000380c058900303030b0f2000944107800391038024403010080326441101414800114810740a8020311050140d0f80c01e900000840701c0ca01e907644001e00000008020508024007280000c2008600342070a080151021701c503036410b03881d240e0000c903003010700c10b01d062018034030f41c0c98881e2070b03064802ca130680c0780c10008007801c03002a01c48000121503182c0210641c6c401e0006031550800c00019850441c09002501c1c8034100c2c120b41000036103000d07200ca01c1580000d21101c400f954480c14001d08001e01600c040c0c0c803280c00300341000a00808a2001303ea010700c44080c072640000c01884510061b500083d07804406410481000710000b0a0030040d085005a25482501089561b81e90f92010a040290403205c060395404000c5c00d1069003400034040b90400401080c981c201100b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 640778732 1250 640777482 640777499
    0x203100603350f130e09070509220311010b030a0305070803090c0613030605100f17070306020307080403031d071e091505010f1110020313050105040321020f0a08060a 73
    0x180c03c000e455100c009035500810703040c000000058045d080414440d8200441e4980c0d44441e14010b140c4070b07880c060040350030740310300060190304070300d055001164685c0e050501800c0e600c3d030312148041950034661800c003a4500484d810707400b40e82c961a02400c00d100b80d100d000c49508010702e07030381c1039200b8410088025540c00014204409060f11502c081c05d042d458001d0075518041c1083e810021074200c01c3c40071a40e002611025160302140020030400102c0c1520316000c1079034070240c4480e02c004180802c066000800e64440c9000f501c0a110301c00e20b10990400ca40c9910200f0300c1d440e000603070b007480741c400e11b00341d284103000e0f005003a14001900e0b00080001c44114a10003844103d11400030012540c102022600c2c2c0303a01c44c144a2544a401c001003a02c42d1070300040c0850480d0b00100150701041c910b124181410780210080009203407070301e8003030121502100b04032582d04280d5201c0c81100d600c0c2c0202d07125100c51030b80441c14000c0c0c84006943c6000040d141c20360051000c600440c00c0d07030303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 640779982 1250 640778732 640778737
    0x41202180103081e030f0402060702060409020406030b0a05060c0d11070b0c0a0c0e010b1602041d151602070e042103051b0712121512020310060335 65
    0x1401202244d80e50507040040a840c43c00d00151864105424001c205124089000099002e901a2400ea540e04401e10000c2c2c01403040303070000691140b006c1004550564540d12030000540c081e200c0600c0e86884004001450203040e6010055503c0241000f00341031003512141403541000c401c64203002c1c1c40e850071100d03e801c502c403400030591000b6041414410300722041c1000305003008400300c8550402c0d08140750752040e60058200014800c01c0d04046403140d520000c40601d0b180c1c40e10701000b100382013040c1c81c0d0b100320880050110400006c07911924801d0346014500155400520080f483d2042c1d103031a1a100600c20f580c5000c4c000c1035542492410700201807468000c1e90005040e00e000d41422212080d66121030412000903c031010004074a081c120030b41c80200e040409000c030300c0d440000d000c0c00140020282e00010f803c000603500c00c07000300c0ba4400c544203d05558805600004110440d8072610002d0403503141442aa41886810403007140c2050041229048001e94031061103030f03e9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 640781232 1250 640779982 640779989
    0x220906060e0301060e0712020c070e16080a0c171003050a032303191e06080c012c010f110114010512060f070f0c290a020f0412021801 59
    0x1070700c1100504014542031003140090f00c082400c60340c1e1401d001c170b0001c04606841c0c104107880e40d400202907485c07400400c025002410060714185003490300b5500f411060188076805004110400701080d50482c4a010350340e030b1076131281d0355002400000c0b6800d49015a01410703400704400300c014007001003003090100b100410b00a40701c2181d07203008104e40c5486020103a01540c0c4010080c014400a00748030380701000c1940382c0040215490101403005000b0741070030b41c006481c83c0e00d44100081c481c0000306d010710300c52800b41c0300c000700003442c04e107074000800d040794010303000e01c9481001400f20360060717204071119602c600d03100b01c548200044607801c40700d691480c070002e0708000300100003603e40300c812001c881d070500c0d0107001903051035001e800c0040b0002e4211800d12103046c1c008401300d803240503031410868008420740c0c01011171610680e00c407060818061541001c4d4800074403611214022500c1107150400301500c0c281ca03100044082d44000c02c000c0360b000c10f07000d1116020700d80d481c0c0500d018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 640782482 1250 640781232 640781237
    0x9010e090c1e0901020c04230108010f0c0306050604120c030c0305060414030a02061611120a181203180b030f010e15010c0f0c08031b010b010c0822090606 68
    0x49050550b0210881c0d00d00d14182e1944100c01c01c101482a6400b01d411043c0714001d49010a003007505501c11800c0e4150014096030f03071400c0400001c0d031403d054001c15881c074084041000003101c4a101141550600d0140c150020010441004000c244c4800f60801034018140e1814154907a03031450020b601d46c2d8000d4a80d41c1c407100c01d110a000c0900005900a8035450045241841d5044042d40f603904c004c225054440c05945550005070240743c0308502042e5079801c1d103100c3c15200c80c1040d001d42107555480005014003402410b90f00702c001300b0205980c6c910914542d41200d40d501110150060a81d04282e40c80000b0005240b289860207180100c0881200c041298100b1800c0054858000c03c075001407101e0420b0148a40d030080161481c8a40101f403000c2c02e41c40d0307402d0800c15000c40d5842500701d0302c0000b401d02c5241980c43d058035018012000280010280c80004541c410340446002ccc0030011704022000301020410000c0f5072030307004a107000c201c050f5601c200008441c51079110202 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 640783732 1250 640782482 640782487
    0x140a05090f0406060813081b03042904090e1906020319021c020d0e0a0f05060105041109061303020604060512160e01050a0207030b04150c0212030c09010e090c 70
    0x4940c03520700002484440305507000c200c51440e00304002c081d80c202900c0c0c2075549840307403004030500007100100c82c0c46040345007419003688031b901d841594a61151050403500e80d4018140255042030f800b000b540c0e03410b0885200e09150030601050300522080c01014514403494a45480b849040707256200703418000c104c0140c5900e80358041c1041c0304c20096240300b80d288100b00440e0301c0c02c18000c0d134940008010b40300688651094440314001c0c502c0401c610464880d4410100401c0b035901e42d076485240c420000d0f219543d036a04144001d41c0c2a440c8444826803041c0000005420064080d0030709101148070b0a1501d0780c0c94000c0303131032984190850310000d2000120007040d003191f4513495400000c00310141c0302c0e4154040c03004044148d035444403410024005170700110380d8420007102000e10f030414209007a80c10186040501c0003180300790444400e05000151490301d00218a010000c0403041c0d841e49165a02135010880e5440303141c07020305105d5101c40881d8142c661119940c82600001c083c1039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 640784982 1250 640783732 640783747
    0x90a122a03110a150903020a0602030907080f010b031e030910020d09170616170109060608070c030f11030d0614040b0a081018050a0b0403120603110907140a05 70
    0x3001d107401c42003640d00700d520a5a403000043c1000c4c0c80100d40b40c0c02c00304001910800c0c1e240c12410407a1881c0d014281c00d0010040c4090004003189034003c40304007604941d02c5061120100d07090f690101001c5034141c11806961191030070340d540e1003203203114440540e4075000340c010026500040c40307480000142c1c0405440017001e074100c04071070094152542140000341030010000d548800c010a400003180c0c0450340b001d0b010340101100303180b610f01c80003204402e60310b4240c05c400410f1036101c1c140c00600c0d0710021881443c01034580300034203601555480c00c0c40540341c00688000c480c1e0b480341c0c4160300c001c1203c80754508082c429640540000b01240e110300c94aa000c0200351155080f526201d8824410b040000300c10000c1c201d41c1c9000314243c00b02d4030b068000c00700d91701c0c09450b0001a1007805400501002c00c10140c100321700c1148281c507034a40c0d07101d0349242001210902d0000914040d156080c114803031070075080043c0c0c88034991030400078000505260a00c00e801082800001c0f800120313014 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 640786232 1250 640784982 640784987
    0x120a03091a040b1b01090203102414040506011101020a090315050c0d0e0109080f120a02032809060629090a03020d031e09080f010203090a122a03 64
    0x41641c1034603a541894100b0303c11100502c106120051941400600350709040003e4129051072900181a12450302e25038461070003810200d40043d00d003c080c2c00c0a4006000518400c5080e103514601181e8000205801c0c0002010060441c60500004e0003003003c016409000030808040290340e610300c51407652411181100d1511500c00790142008104148008030030b042c0c07013a8038031001c03001c01e45001d65600d160043c4840d182c007410100c000114005190400002030034820002848001c1d1a580c102e6228120700041d110b2000007400c1044142803281e81d40302080390341500d10340c0002ea04c286030b034a082c200c61256014030103c0d10350711000000f800b9140b6900205203181c2d914980b030003008900150300301301c40d400028800c0c2f903080c07030f5002414070681ca0403100d400990000c0d258240001800b4140300d50900c61419288591440300d02016010300a907801109850003e010f10080741d130b02d10f001e0383c0a03080001e040004011146035038002c08030700c400e1054184d0203204280003190900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 640787482 1250 640786232 640786259
    0xa0c08030d0501090c0827010c0806130e060606130509040308010303020610030b04030c060f050a02041502010603080f090d06140709080607080414030d1d01060f031a06120a0309 78
    0x1d8084c2d1881d06100e126895000107038503900c10039400076800301c100c55040c0d07030040030f20340305c180c0549620b465061411160071201180c0544022554140d80d40f2817241c082c800d81e1000e064420454211a01090650034807401600091400000340c10700541c607030b804102d081004a6040d800a040080104180b6406111640d0050003a14400fa51903085803a00c40d65044003900080410407a09102e0042c041140d128101d28914a81d05100c40d041504201010750414041c5d150504d0034030141d044114014070a107000c40341d200d200213042110f50400040c1c680c00c00d00301260004e10800c1c0c10350028215202d590b103036000c0100c17040d086080081c0700500c0c01c521030300096040d42c07001081c400e240da0059107031940a503101c0039007a01d00c800b05414030b00b140600204582240c0c00c00c1e003c01d494140c041c2c40c003012505107400030030515540706140c082d81100707032001818544603002c40c0b0b4030344000900140c0c0d0007140a442c0b04200907400300080d02d0314026420a50000f11070010074001100010f00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 640788732 1250 640787482 640787489
    0x90f05041a0f040201120e060a090213090c09020d0207020a120b010b0901021b03030919081209011d0109180b03101e02070203160303020f0d0c030c0308090a0c08030d0501 75
    0xd8035489031034101d4801c100c64202620117030501034602000360000344583c001d00307032901002050340d4803170501c40315003409050745190480c03280420a1075248000550b119049a0981051104035550328203d9181e00a6019000e841c4200381c080100001503101c01d81d84100034000c00075060564250707800c00301c1c50000c1c1a002151139200400180166a03030000d0f100401003020f0030344500c5403030100c00003403942c4595076070141c010004840f040814140b03d44050110307500d400c10b464002100400b002c11512641c00d4650100da5104000e009411444a4030488004181080305003a512102c40301d0103050701611203500d0644900c0640070300d0900388030480a03620503040a2112440d04e9002090400a14107aa03080940c042a4a07007950b0302008080050314042800c04c400740d0721b03070030000c1d1205501318009a040c03140d0801c820b080707403103012518000307038040d41d4251200c0e6151750100e400c0013010b03254240c03620409d5200700110300b80313240b500001c01041009550703c420344c0b070b028810b542c5d0591 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 640789982 1250 640788732 640788773
    0x30409110a08010902030721020901110c0a0608040f08031302031e060c160f0803160c0b0c030c0d0c0518010219080a05040e0c1b06060a140109090f0504 67
    0x70011084507046401a819101400409030320707643c80e60000c8514415131580c0783c1d458490765414510002c00c40e4000c044000080c1d1702c280b10400c2d801d498035070310380c1545185900240d09150400c8994490303800306401504c6410340031100c21240d1110ba640d0f0300280d40500102c4c2048010308218a010006070102c107109502c07504003000c0c41074040761030740c0c3d00916408a024000420700d20004024602c400d065a200740c040765154118100100d954001311640005c42d40301c19100300320030b8040c0d140303c001a64440d03886a2156140303254011640c1004d044540c104100303000d201c0601c2164002c408100c0c1ca01c0d07171350a0f11044208118543c0780b0b00140120305640000a01c01e400c200304a00317a02c84150050045a41c4100c800000c4441c1d01c9240e0041191907040c1c000e2002600790f00c0010041d04010550002006048140d2141c64100c00e035400d07588000d64039000c010480d443c40c0e12810031201410b200f40859950b000000680e5100107150201969810800c020042c1d019070b0208900c4080c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 640791232 1250 640789982 640789987
    0x305010c090617011809080d020405090903040e040f0c0305010c17011a0304110303041d01090b0a060215060f0613030b1501050406050306030307060204080f0f010e0a03030e07080a0503040911 84
    0x101c1d8203241103c0c06019041a0fa41c06050866130405190009800d05600055207652100c5510301c03107000b9081030044511881070000070542d142000000d99082e160103640e40700c041c0c1c0355503644001411402d8011211212144800400b06c0c0c405c0c0700740e440b41d600d103441700345400c8101d03864844004c40503040045d005203000c40f11290003038035809a070340c01503100d04800701d20041400000d10710300540d88032222250184209229010700030703030030b18100d42e4444030500c003c020060404c2203a00d05ea008450050b4409043c0c0000c0c0c03207488000d40d030800c0b405403e04c2e013903864040101d451507000341c44c00540c10306010400c004021041081e95800768440414540d01d00300c0c0c5c400246140304500c2810100301c4c2c00700108a41d40d40c18002c440001e030b8010f000310341c2c499a03034503001d48955819040c1b003031790300440d8020314901c901070240004580d00d030406008039414030381d03055004002c0c08035590240d1150000c0465500401c10445880718041c4005540f00c80c504848001030b1541c00d00024a5100306 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 640792482 1250 640791232 640791257
    0x150405090f0c01050f0409020a200c090a0f06090e0d09050f09070507050f071202030d0f050319020f031503060112052a0d0309050a050a12030806190305010c0906 71
    0x120b0004022002407800980c2d0b2580b1419030b0240c1d000d15080340c40c1042c800a0300ca6429500840a14000312041e50400c41c01d40c040c4603039645842d2203040d056040341c11000050ba0815490340f0043c00c0741044007001a80d42d4980140008460402014544580c443d0551503900354100d21450010441210440911050380c404101e007003001501c8801030060101f0b45c0300800c5414000c0c1d24504135403004035030406a03101449102c0e02001413081c0d01a01541511960b100d2085900c80d07500b003699200c5514517118881000000f07a289009400c009600384004101401035500842c011090020f465543d0321014080500303041d4184e2010101c240941c01070b00c000340c00031074030360011884120601e8500c0d01c4000140c9050500e003800707070fa000c3d645a21610030141c0004040c0250b0b9000d44150303e45985440030702144842a0090624002d015800301e40080d1040c11020f81c07040d8050181d10898501c0851003003403404581086400da515010740c40d48641d0301c402e10354001c1620b8908000031000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 640793732 1250 640792482 640792513
    0x90c0f040e0c0f031e03070b070f080105060c0a0c0b0d14010602060402060721120b06090d060903090506030c03150405071b110a032628120515040509 66
    0x9180c0e42d40a07000d000080c914540d000c0c0300c001000f01c2d85c0040c0420000d0f094100d00d48980c0101c074103c801d5240e03100400c070100d10800b1250f855400c180c8a0701c10503401c12041102e030760020b50102016106918000c00001c0001411600801c010080b0700d032160701071400788041d1008161140190600b0000402c8403640c006415500541c040e150306585200500b40031004207901c03803803410b44400d05c101030311009038002040c03001915a42004c00c9800d00e0ba00410034241318040c00c642d8001030000048012401035840b030300c01c0500c02e082404181e561200820825007040341c81013041d0001004201c0c41d002c00908a240d2120211420406451710030406040440705541402c0042ca606001004000124407036143c81e0100a0210b0407407642c9140043e01026401c07489841d04601e21842e002c045032442c2a24458082010f020210307840541000150180c00101001085030301803070451010801d20460303008180c40f5003000a100810340c00d20081d15005801d0801036400201030900814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 640794982 1250 640793732 640793743
    0x5060307030b0c0d141015021e0102090a03051005090712231603023f0a060606030c0e09040b06130b0406060c03081806010504180b090c0f040e 63
    0xb54440110612501c601003403c41c54001e4040c00403801345009002a03d01d030304140c0281c82503081441c400d4000303803644282100d28885c681004007583c0301d07896050425106404030102d6042c204001420810118006991740510754020780341e07904220704813111145240141940242014020035850b442c3c4110007510303201030007001c3c000b44440400c02d0100400c5100385641c0038007103c100c1e01c440f00e01c5155402c80d42102c0c40108d21502d800d8071917500c030010416040c40d03007600908500550142c0c460103410b8203495490b086400b0b000f80300003500010740511070310001e40042ea90000700810042c001500d500440043c00b481020788004010005543e10105503001a041c1c074460b080284100c50600a442c00d240f8a80e030090030101c01141aa50104c080103242c4d002c0c1d070300c00c100b50301e611281c562040030300b0407031600036000180180440c1c10190400d866990f5a01703106806606261200d42800c0000c0d10400d0040d004025882403524040b10385d08000541220100486c04640031456a100b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 640796232 1250 640794982 640794989
    0x807120f050a022206050f060306040b01110601060302190c2307030803041424010e10150306060305060a050915011b11042901201e0d0305060307 64
    0x20141064003000c01030103011800109901030300801d03100d0351954a1019003498904904491480c1c2900090a440d004034032400f4400302500552071502c039603090001400b5501c10141c14081540c04814001000704070b0f06008090b80e9a0040e11080d8a03011115001810301500f0700304031420b0b4403013020070203484002c610181c020420f210240c061014550400040e40d001810b0701c0d401000b08001d1283da402da04941d1000d41003510008415411740605081071100880e48900f03583d0014801c441c441868150808600207841c254940da8000454901821808100009844a0b401c101d040d806018043d0000b40488880041c103003010003094480a0041c0f002004060507400601c15034000d4a2028541c0701907001390700600404c2c1008911200140c49190180e0310b045001c51904e0043d036180c6110003c078041400328559107100450315000002c480c008a00c541c40e4074000980030400100001d00f543e070500c03a44800c800440c40d400c02d0404e40784402494141401c2100544e004074080064 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 640797482 1250 640796232 640796243
    0xd0908030d0f0617030714060f0408070305040306020a020f01110319020d020702100816030b150702010e0405180c0d03091e0807180f090b011815140307080712 70
    0x402c10071016000601810361042d0610481c0c0c0c950107006210100081840343d000d40030310006204080c01046e40c40750102d400d802d4400c3d070100400c0c000740030340008100381d500034581a0306281e180c1d150417049a204810f02c00269000c0d0268503034440c03080c0a410b400c1c92685820341c1c1980740401c15228182903205190441030b03400980e1074618015581030362a0705402074a0030002002410011b000341005440c003c0340c010f12020041c0d00607110380201d00c10907202400f15584055010507003401074101c10000c90500043c0200407900380c440781301d8140324081c3d60541010f0b07011751000c40c5060082c0700d0005801280c803c4e816202081c0c114452400300ca0302035074009060450070914850f00720135030300410090b0168074800211003022412450700344a03a020100610411911001c044804030310380185403400c1c540040100345001e10404103d001d01c0c91004c40c008100300800e04c04280507030031403c00c03541000700300c02c04e1f42410846900a4103842005040c1c0a0520790362004400100200030712 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 640798732 1250 640797482 640797491
    0x180603060e42070503180105010602070b03190f0510060806030a0209180102270d0c1404020c0703150c020708070e0c1902010e0c030d050304082b020a020d0908030d 72
    0x805800140b0050b072441104900c902c2903041200005103203500c10b0710000c281c0b46c0b41d401c01d050410418426541203810603001800d02500d8010000c001c0e410003009062400140842c1c1c91020f40345004041441452142c0014107107000e141c12585426282c12407403c0102d144100704507600c000443d4450960111200e62095032001c61512068403000d644d50503650002c65213076141d95800220768600f5401d60f8250402d482408148050103003c0360b0080c0000086810801404094621060030401c0c05400940303800c0003a1111803034040149d1045600c1c3c143e1810102110082d4407820410315180e202400d0220b01e40301d06590b80d8142c50046804400c1c40c05d0104610200880444240700100110b2010407003113200040e0082045000c0b40d8098006c5850341100c6107000729082e100c8001c540c44281c2541c840da19000030300e030000089114903030000b803801800c180c811080c42a5409031a0780c0981c1d41c40941e10004d04082d26501e10805009010030706024804000c820383d40b0246e0181c90004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 640799982 1250 640798732 640798813
    0x30f010209091f08120a0f1704030f0905040905071401050c0307030509190602010e10020a051e0d020c0a030e0402071a07020109120522121b180603060e 67
    0x10200da45030f8801d0741a4803964401d19803122074400a09011030564540ca0f21800c844103090b588a48c210052517100d0403a44000740020b40204091350825440c0c0c03030400c1c120340c3c640d0003041c12660140c00607901c41d40444010010848018500341d0440001e1034507078182500c0082165881c006c03880c006003807080c04203143d20300e9103400340e880d40c0c4015000104840b130b5503110406802861110b40404850044491104100e6040e0080741e1444940369102464211040c05110340e40110907090290300d4000c00030100d000d8414005023070786890070720180061401f280b60142c16060f5a4a0701c5006600621154005c10304020031089240440d00c028142c0760b854030012401894565030007040042c0091007120555403140148c00c56440448001d0080601c545440b4100d140621503202c450113072903c2c20000031065003150340c0c85400c96075030101c0395483d40c080d00e2001c98404240300405545260800038004140158900311103104003074590031600f5116100119a282010707003640c0f41406001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 640801232 1250 640799982 640800031
    0x10b06040f1809020d060f0506010201090201090521010c0306050a12020a061b0b0f150409050a030e1801060206100b0306010206150f0a1205061806130303180c05030f01020909 77
    0x1010004e43c0109050b0030a01a0b1510000400032607030001121490840081d00e00c1d4014494240495016110090000e10340300401010030060a803000d072040d00d00140080054007405001c0008040361408100a03040900384081141e0544c0034a825400d54001c1d05c01503180ea00e884130564100d440c01280386510800031500d40d01e03488100a1001040c00200850110000134039405642d0a110107602d08a090082105442c5407601c064041e41100c442000024041d00c3c0b010340c0e4030310250142c00950043c5a920401c40340981c42000540c2015040040396480123010030050080e00399503038114204080000d40d00d0300014198a07900030510140c51080d502d0034200240414002c080e0620580c551001041009204004841d14410381003c102070496088841c000074905000921442c0d80b072071002510f2a01c200002d50a060741c1d01500c03540413a0141049071090301408010001d81c2c91b201c141803900e408103000d4143c0780d01c180b00c0c030100e5658084516400c40801e4000700015a81410f00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 640802482 1250 640801232 640801241
    0x12040308060105072901140303042303030a0305010812071511041203050d0506030c030a030507032006070216050a03080c07050d0312050106090b09060c210c010b06040f18 75
    0x18000000e0012020403140c905c034081c0500103901002544503076030301e80d0b0b04090310100701d103031990540040c00b06002c0500b100411090780b00703028a4001c10402c40801090465002d902880c002a4a9900500c0051001c10000d05140c106400da40c0c03800c01039458655000e10002c200c18042c0361a1100d075410100c140040c0c90280040d9410241074626524010f00700798010600009201e061034001503403482c0200e420440043d001e0090568000035070350849681e845103504038113003c1441c02d104d89980454081e40e24100c8041d00401540c00e00001c040c3c1b400310002000400d413150f100c41407219495800311031080f0795000c07440c20f031207032420200700381801c0b456005203810811000d80e12091550200302c140d0280340d0108108200d9894100c00c840d8141e1600800003001e100708202c10b8a4241100103110500c0b0080568414184040c441e40102c5170100781000307207180125056811101c20300c60129410700c121640e52a040c54100401300220381803243c080c0d0443c1013030100c45846441e420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 640803732 1250 640802482 640802497
    0xd020301020d061809030509090a0603120e01020c0306090c010f030905160f090902090106110102070c0824040203060a090c0b0a02160503010b0d140307020904060605031212040308060105 82
    0x954a40c2d0410403030200403d0b0034810483c410300b42006141d4410841d115426195800d40e40c1c50b0715186000090220004000e0111428184d070380b0000008122190510250740d031099843c40e0000c40b01900092500c00d00c014080d00c20340000c02800b0740544005400e030388008081c2011680380244c0702e01500103001c6400044d04034011218000b14511744074100109450440d40c2450704681c0318034005040b20b040d03c00003500300044d140103001da103016180400d980d03940c1900140c50600796542d504e05541695218100542c0803515030512001042d2603400020b110103d454401d1500b5000260b03290006407001240590701c407840414800c07040c4011000e4642d5420440d070300d03076410500a40e210544102c8000c02e4074149404205850113012f0030300c0c450b000404d500d400802179107442c146a00c04059055040c0f001f044000010703111000e80507c243d02a41000844c14908001d15080410245d55400f40c40b8080290000507a00201c2c03081d08103030145800a034031707650030b00140c038079200d03010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 640804982 1250 640803732 640803739
    0x2041d06042105040e0c07020a170a020108090309030606040e03190207180b03100f0e0a0303020d0c0504050105070b100e010801020309010c09080c1e18240a0302040b0d02 75
    0x40005220595110b40c0860003409004144030680703080c01c803075034012400b92001540c440d101051008240c10090030300c2500081c1a03849156841412450224101414100a401030301252003076680201481ea4410b036400c000d145084440030000b80c603440010b01d40c0b032007207a4031f49245a0051042060351502c003000b009110020000100181d5544014452617650f0ba0303060329488100000ca0242c194800350260050070954000e6030b0000140105031070081900d5580c4248683e1040c0030840d10391100d0081d10010781d80c600c011944030507140a10380c00014043c04000070411030f41d001d41200c60141c1c118803074903d41d80b500c0000c98801c104651060503500110b10010804c008190b001714091202030000f0090321a10b01019684141d4521034440b070740c0c00c41d0300c01c08a2030070206da101c0c480c40e9030304000c840c404410800145000e0704980502050000d580b0800900340207500c20144442ca006502c40c85105032000068500090340c00024080c50321200c56560585810310510749459005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 640806232 1250 640804982 640804993
    0xd0b10320906160510061508180d0c06060b0a0503130f08030106120b090105150a020705030f031905040e0a0c020f010c1d09060a14120106090b01090501031802041d 72
    0x80868000c1c140d410300a441c4ca0248920101042c2024400c8001311101300f103000a4010302c0744011b440c0042d0080080d5903400400c014510950f000b0301c0145400c6551383c6640c0e42000c91824a0002c542498000c0600120b0800401c2034440e000400c0d0381c1d000000c80c0200d45480d5084c030742015114120310004100c600d005c800800c4007504041038000003080240c003080000b0103441000744a845c28414950816010b0300b00c01c000088041c001c1820a1580c0111010329a8420109246c00c44030b221440c5207420200e180020284000c400e0a418042803403c14140b80c10200c06040809024244941c682c4c3e540c006e1101c244c0c028800005514081130080000d250700b80005801b20406510044011000c0c0042c51810f190503036155000f03e41c01341424403181e04002e0560841680b448045a0040000c0342d042404c641c240140c2000e000c03c044042000c0c5042d20014181424540142707042c1401c0012030103405112095109041d50102e030b0128650444403074410341c224155103001103a0146 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 640807482 1250 640806232 640806247
    0x7021f03090209090c090402040506011b0506040210110c0d0c05030313030c050307270908130f0905040321021c05100602030a02071e09020d0b10320906 67
    0x256106081c218001d46000610765144c2d035020f43c580060100459014200d032020502504099110541c0190181040703590082d0744c90000500b800b0300e40d411101c44d0f21000800c401c608007042e540f40488810304102000a1001c0011500c0d52600584a4001c0701c00307078800e0040c0544a1842d000808028068030344e200554141600303403500c00d00050340c204024890000c4d86013400202c0408480d8890704041d0745290303103001d41100f014000b441d00181502d80420030003091745d003001803488515002154610310f1030303c40c1000a4034500d500c6425158a030a0400020a402c03640b11040e802c402804031714a05000d01b00e0320028002c0d9510070340d10311840170340403429030480e501c0a400b82164004205034155110012603407031140515900040c1c03c035031070030030001da80500e080d10111031440c40140001c2d110042c0000b01e80040d0400600241c0744c907070204c40d60074142070141c0d1076122450b0216900c4030140143c18010508420803900c2039030a01c1307140000d039070312054541d011b2005102590703a050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 640808732 1250 640807482 640807487
    0x305151e0c2a0c0603221a19050609040209010905190c0f0810030206120a06030605161107150e0102070515071b120602030408070b0703060816140607021f 68
    0x42c0040010103a2144074502c1c0000d140000c15248252294440000f0080d148402210f0748002c20300100c642c0041c2e03210002502e049424418401c0000c131980001a000381c100c1c4005840d0003901403401035001c801400f0150302d900741098152400e041021074942c603071490078451000c0700700900d05403e1030050085121030307200f510030164042c1c3d640d400141d41c07541541344041c0d6401c0d1000944c0018108420907408045800680c0c0c00540c550b000141140e4980300c01003500c4c81207c540a00d044013500c0c5030b14032070300703e041c2001070318030300f0024a02182046481281d16103040300d8542800b0f1101c2604034540c0c404c00c4200c0140c1006001104c44002001101480703400000044480505c1c0c0c00314141815901585002141d001c2042c000c01079403543c407440000d500107481542e41c2c0d0700c10844c07400407506d01e0a16a000d25a9030b035000410524002106051142c41d900d004890b80204901f0410404500001551454100c4da61030740c910302407000404014011580c90355240006c0d0081202a8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 640809982 1250 640808732 640808797
    0xe01030b0f04110a0f05030907030f150203150a0b0a1403090c0319030e060a020706050a051218010b040b1e121c0e0d050d0c03121103010305151e0c 65
    0x1407064541c175062608005042d1842d000440e5054419808400f04201140c4030142d201c90b1140200c0544034442c450300c0450341030341d004a9420754a00c18010460004c1e090036104600140000d03d0002d04003038500c01e004220885010500c021084003001140b02e003041403102c00d035550001000c84044048004841804881c01d40c01500441d901d01c0b4020010705007041206e14040d0998080c01d0160f08020051700d59410000c10401086428080b26101840c3e240000b0302400c09500c6080520b80043c02203425200c0741c050a50250341080c62000c82e544504000d850345684100e40d1a0350740031001b01007010711425035480d0390300d8810080b0402454629025420f0110040e6a54004e0041000180100c05040b124000c0c00f0307902069a5000807442600800c900d03512919014410a0b02e00b2146003d40b240c03031110003210900000100100101004a0440c040305900006403601d08426000d5400d0000c610154002d1407403c0003d000d08000700840d5681640c04001e504801c10103040c1c5c00664 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 640811232 1250 640809982 640809997
    0x1e04091a012103080a1404050a06050a110702060714120403030e150d0c020c04020a05040801060e0f060904030e0301052509030c05040f090203010c0c0b10060e01030b0f0411 76
    0x410034000401c010502c040b1406856a00e21110500d2400c96075046403d040010102c409241d55100a20f0080b0180014580901e0240c0001c0c4180102400c00304101c0310050500d030804c3d843c0003d0b059007601c8480685031640c0c2c040b14071075103540350390420b98010100540a204240140c0b541c075004040301e600030303006480c000e030f6560319460040c200b40080c0c20381e20801070116507018018400711251540090034594101d1040c2c1c2c1c4401051800300c1c0903a041350b0692004a400030605100140c4248603880092030200401c08841c00c0c80c141e044980b840c00303001c06000b48521800281814000c0d803a030721100c6001303130080001e4a440301c000e0800386544111091301940310300031407110510444d80e0310182c941181c03481c200289800300700310050400d0009900c0840e2140d0300000135a0b400c1c4280000700340701d9100c070103185a1798a021800b2800040103d28400035080e42442041d84c05008210010000c0c01c1c001410302058002501e10340002503841e51240c209425010640001400b9140a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 640812482 1250 640811232 640811273
    0x1401020d15080613061802030f011b090f030b130c0308121609061107030b1e06060a1e03061502010c0f410f040807090203151e0409 58
    0x112920b03030740041d8a41c0c00540e074a4030b821250039600804524a540b00150740d074000e000b08100310245501190810549032000996030b59140d00c035407804410002480c84d07030800da103002c11260b41000b40821260125000c050300c0c680032540040c5169145044150078140c1140b410340d0169543e00e0b04402e1350f840000f4907801845900c008c07a000380c80e00903010085400d152189043d850400c00110366203048403403505540c0c40303200c50010101e685820098041c0034100403000c500154071442c03100c10300c0003402007070189408011514086038441c0c001d0003510741c07260001c6642c54079440211f02800070b90308100c3c44900d4400c02503103034680550000b0f04402040d21082107401e0045016a0003009220380c1c4c1d4084502c0325540303590034a05456501d58078107006543d032150b4400748504083ea401001c40811030680010707040c844040d040100000504c4800400c0d49549002c4440111401c031205140e402503001c000b03004282e12802154222040e0060420002448941000300c1402c1d00f03601a2181c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 640813732 1250 640812482 640812521
    0xc0616030e060301050f1219060209030606011112030a151403121e390601052d0a08030a09211205070804050306070903140c1c1401020d 60
    0x7803820060705481c1204c0005216080040940342807003010902e0130341d0b81006010f803410307580c68400700c00301c03941406000704001600c8401003018140f030054003511942c140005103406018070321000034101c5061540d40d42d40d40e00c80c3c03a081144006004c06007010007641680680208a0307000d13851001c0c095040441c119554011218441c0601d40b10712400140c148400c90810098142040024021610300f900c82a1180441c41442c140e40e440800803500072840d844030900700784034104161800b6080c11184c4000c0300c40d0765108400700c0e0b801c540245000ca440e09400031003980e030b1500310800400e40340060307a0740e6540300d90004040901e140190103051030b061b4152a9520700700e2034400e2049a115406190100e42200265955009a002201c1120013000f010a45407024031200340224011b44a4442a50452501c7c0c038444288802c114100e03481100c45a05e190340307e001e41d4041201807010202e40225504189a802d0300c0c91034150030035270000941d80e102488640c01081c41103d00b220545 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 640814982 1250 640813732 640813757
    0x30708071208010b09060c030912070e1605030402010804150c05032d131b0b0912030a02120f040b1b0115030b0a0203180a2f06030a0e0c061603 63
    0xb00d0b070031001c1c0107241049400f4000d2000600703282008000c0c408003441200d00b0007000c640061402205000d600026401580c020004066014001d0313130000031030441000d5909862000502d103010040c0081d04102c2c19402050a000c0703109034104d0b04144489041c001d00c01c03250340140c00c552050341ca0440c920144840300340d158040410b4031726440c201864020303951b101c0c94010341340845142d20980e060b040020401450303640f00c581030b90040c50454061616802e40c4c00400106aa03154800e5800741c02c200402c0c207400e80e011030314031100d40f01e00814030b4a40c4084600030803640a203801220030203a0015618031041013034001201e0b8601030000902c41c00407800350002d007008892000405454120003c1010104150051540589010342000c5441c4058840500d44000a0425118078100301884104040c02014244440712502e41d0042c4000d45400450000d11008080c82d440c946d43c0c0003204c0f074046c03040c80950481c42004003803645a5a010744282204c0802403411000b00c1c1c134007030002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 640816232 1250 640814982 640814987
    0x30607020d0c080a03110c210906030601081f12110301060e0703090503091804030e06090a0302040f02070b01170714010519024201080c061305030307080712 69
    0xa4106007030b900d221031845030f503031888010741007030701c1e1071040c15120070f01d41d050403164070042c140f07540495000307045a11400e10400780340402c0c0300b2800b00d1158104030140103601c4440c1241e420180c2071801da0700300eaa400d914030b0000c2c45020240f402690507417400050601013441c0b0000d241d8047c840406030441a01d040501300c0e20f49200c4c0d08a41c840140001e800381c0d02961119030f8041c081e500707403458105c02000140d840c1038400c07038441c0c043e420b000a010a05a020b00c1c0e40d401100705541d443d241500c00000104402c640d488000d2050b40c9a012200c4404400e8040d2170740304d580690255655615902440800d012041e42c0c415540f19190001550045c1044d50003041c0078103849161404103800e644441e1411142411000d5100d200504020001141c0c0e000407018028040308040c120b641c1c603891400c0700b45c241c464041c40c039104014408514007051305a009401200c610b42c1e07800b215403941c012503820768400c5506000c00715542c41031140c408010260584511100c0300000c0502105 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 640817482 1250 640816232 640816243
    0x5090a021303030c083006181501030603020312030610080114101106072003030108070b0c0a140105070801090e1f0e031614061506250303050603060702 67
    0x81038801d0078094001c001007802403000c2d85115000e1401c0d01d1900603c5400b55415091400c81000410464180166048480e000d840d4005e0001c44280c9490f010394140f14aa6410142070103202d60090418080960b0181d8002d40003140d014043d110620103e00c1031003026041124214054806050783c0c010300c03446101c00c1c5050305c003100c1050000ba0002d4040c8000260050380d02da0a0100003400c24004a904000d481e01c681603035540da0300030040c07036400d5403010140d02091a22950051005000001c0b000c15074505803440c500007261a03850b028030391440c1c161000b0000d41041010034102e00594010f41096204842c0c5464806590340d891066008079503070f0000107041ca0300300421001101c40d124142070708182d040c010104000002d11255411075202d110b83c0c403000b8560344040300800c0f80c400c2c19411758200c1600a8440d40c40d1102841601c0400c10ba05a4440d0070000341d11580b001c3e1145641a441c400c0c0450341030000290303d0054024075041e140c480c801c0c07003020000f40403a8400180c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 640818732 1250 640817482 640817497
    0xe0108040b15040216110f01050a0e0d060207020a03062702030c09180106180c0306050136091d0d0540060f02061e0405010609021305090a02 62
    0x14815401e95030782c0720944003500c5121080d94407070b4080040401c410350311800300300d107035001d96841700048005204000720007440745001c80c180301d428414010103a4010322550910001070f82c54a403210041d00e4110020f10800e400250310a48200c000304c2484031740c0c1c0c0551a000d2075136981c884000d4129420505802003908020341c1940100b042d60700d9801d00d0300040d0703001b1600d1260a511040c82070a00c0c0d0a41d00d42e9080444049420004d190f070951007800f540030200a00c0c1010403050781850002446150f4001c3c2c1480341407100701048040180820a0450381a5081145a007698079808000c02410303a41e64003404600c0030700564404140042064024a09543c0380e084c9000864a021203170401c0b1580010000b6180110021055814641143c20a511050040005800d04602400c00409281074408551080f0b04107e0f655404015000900e1784041c4107981c82d40c1d0340d01d885400340c49036400900d21103002244444941105085400c1911002c40e690b0441d41c2e10566010104d010700035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 640819982 1250 640818732 640818743
    0x90c03021e090a08010501061d0d020906060307050732070f0909020a03050f010902010f0903032f16050f030105040b01050405091e1c05070b0a020310030c0806070e010804 75
    0x140c00c1d4065400200209866500681030300e00142e0f0b100c080a003103440c02d038400f10114080799503d5000240b04141d01a405070116010089040b45030041074a030300c001000b8034000d600000210762482c1c0540300b030700d20041d48180d02d03a0364040e1400c24841d5001d0140da1351044802c0d08000680303444404100b0100f541e107142174000c401d514000a580c0640420081640c1024a08202201190b014061400003400d0003001203a49000740c03000401b002105804001000703500002440042c0d4001c030212090301d4104031072541c00b8421402845401b1500343c40d98031600c00c0d01d980381c1c00075402d01001821540d0848403404901012418503080e200111340017011045000010300903460181d01c1550001507003002c441e51080b07582c502c010180c11040b40c20201c1da000000c211000540d8560340c00075400345150080c2441095510074010300300103030004161f20340120000b0002c01c0c003048800021600007246030f02c02507030748206646416042d694030000a80460019003a9401001154059540326 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 640821232 1250 640819982 640820017
    0x30e0108090102210703021e090a0b0a0c030309030504090c08010e0709060903171903020405090c04120609031112040e010509090304030f06060321111c08090703080f04090c0302 78
    0xa406813214100000d0031641415400c1c4041c0c6880c1d000c8942e01603070841c00d001141e984507180e03410011030382e080307600c90a03142c4c03410040300100b240d100700b0040029625082c08911422603140603503050056802803203000f46007030b4a024029030f22000340c0d4121410100c149902e515810000c80d007501d0940100b001080400208000181c102003035821401c80344603001741001640700c0300b0700726080843c1c00540040e402160900c107074a0302040321030b003280c50b843c001490249841201e800342080002e0141042d43c1d92461681450300503400381d56004510750944821700e400014215003600180208054585210700100d45424032456035402140c2800065040600c0c40c0d030b45035100340740030104480240e1507247c00070001c0c0d060010101401c004d410580002001890000d102420700070a6001c6a0f10002491459500079500804850070034600814a69203102035989080e496500003814108001496180b000c910702c00380c826110040011311851300c4c0713003400310168000d0422910144814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 640822482 1250 640821232 640821277
    0x3090c093312020f062a070609060e1309050102031923010e25030c18030206040b0a0e0d050d0f020303010515160f060c0905061207050c0f0109030e0108090102 70
    0x903030800d03541240003c04403450f10300595203e06d21070024406400c24144284451000301070240200301c05080f091130b045418038178110340208420140d090b030038010414203251101107485a0072105800360444000d650380c0c2085d41080d01225402d801c0101c00c10b2914080058868116189060140c00b52900400c103900303000400081c4440544440c001c803416851540008400d08901c00d0a050303c3d881c00100d040a94102810010303102c0700300602040000d5061006035102e0041e1803d0b980071251007600d94610100681d15041c0c0c40460507800504c400b441d1040040009421122031100d50300d4520300340403103000b0f80e45c900081c010150300c0480c140605180744240000303014100003009a00c0079805e20b507111a00a0500180c01390340d019110861504000d0300701c0013581c01003d05441c50f80c549038040039000c003084000360024040050000d5058503446040050400000351311000b08030100346440c1c0946103400c4034140d01e0200d40b0003800151200010f02c00d83d0b00c5969683c40f8000d0f02e541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 640823732 1250 640822482 640822489
    0x1211030c090303161a0718031b0819110604030335091509030a0905091005211e0a0b0c0415030f050610020d03090c09331202 55
    0x1140d84055050320007072040c000d07000603511050440c0c81c0260000807024010700317000000d100008101106111050810748813411010140f1030441340c112000d000543e81c030070446010354030700c3d901014203071040c2e1300d4100701c00d10b055904c00003451195500701c22104944062050300d000d544006000708005d000c2d039881c4040d000011010300e00b00600b080c02d0003020042032648041c02501c4e0600c0b40e5015a40701c41d44500021802500190b8a000643c188490348400403c1c00380c250041500400d44080415020504c902c4c0c19400307060000c000d005d031466419600c1d004584a80e840070031074492182e0350100510300020705401186054041c01e013400301071b1550141e2510180034442488010080001c2440c0303042c22001e6400040e6402042c0075400d0140c59065a0b4003810040c41561602e03060a129600083e034400840c07164280800d10a2050501c101c2c0c1d502c0d6540082038a905002c081d488012420001d2482501e441c08440311f26641d4514200c04039100380a91501400e014070082c0241c035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 640824982 1250 640823732 640823737
    0x80c0a08150f04080403170703080f16030207053d05040f08070c080610030b0c0309150a06030f030c02030105150603070c05100617060108010c021b040b0306010608071211030c 77
    0x2809131034600c1c50181c0d207555400c0c0040d050707400703003195400101d58102015400b0000e946c110024020900803414094100030030344514122040c03d240c1d0005801e4208401031299006507542c405402102150030941c1c0c0148a4040c42c40700c00f591950306840b414440e180c42074500842d008400708440c000241d03242c102d540e000c0c0006032480150050000740d418010019288189007007003000c0380107072071031801556084025002e080901c50078820002c0707044002801d84503030050083c0b01c0905844d541e01c500c000b06026040030708403070b60103140d1130103060300000003030321551080d03000300300e00da90f04801d50340614101c4105a1307012400f080440e465030300c10404210024091400d17900c0051a414850089601c076038804c40d024103900d15a0440c511082c00013500503c3d4504c0280806050094002d480700c005080d2182d45002030074a003003591300d40740d11685030320b1009001c0382c5481d61180e1008d0301c050022120308001032548615040a1840303801030500310148220134500759107130509000b8054 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 640826232 1250 640824982 640824991
    0x61f021b0d0c06030b031006030b150d050303010e01030308010e040203120a03020d0f060312050a0e04230a060812040605090f3613020306040213020c07080c0a08150f 73
    0x28071001d200c0004520311402100007400f03240c5001034541c0c200b00a043c00d00321410140c9400c02e14148040001c01c0400244990000c03100c80c0242c140c0b00443d00048401c00b926001400d103105c048004514004040e010707a05070ba000b0b48485d2881c0c3ea0350143e80041c2401110000e40603000008001d42200300e8801610889055050140c240701d08203940c101210130318440710a24039100c03c4100248600c002662800050030b26182d8540103810a0103011003002c1e2040501403070b0b9541003110351205034045018004d40e0340c40e11100c54113201c3d0f5148090001c0340540c151a0041e114009402e4907050220b030115040b50f2502c070b040c040c00c00c04000311481d440188a03004000c242147c41099400e900c440c000b00810b010380000ba607040c40036810b5108000300500311245203c011a40944e60000d000c540c031070740c112a0489075020702e05035840030b030082c0701c90904c25200300711703004c603110501145840040301c090718103030a900d81d513914865841800e1b80441012503020004588500484048030340e21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 640827338 1106 640826232 640826239
    0x20a0206031501021002070602070201090f180509030f041e120f0b0403120204080109021c170c0102090a030c1409070801060e01180608061f021b 64
    0x114403001d4480c01200407020003004a580c400c04c40003d01017034140c0c0c103545031252854690040c2d040b100049020400018000c01c0c0718401c48502030440b408000c080d0021907007244070700020a8060505001c500080140101c2d00041f2801000208104003680c4000e141c034079103180e01941260420745450943e0b01c81c20f000709a844255520003500020854100d466900c0c00707460320341e400894808900d0010800180c0624103602006030f1a0094031a9404425050700c0e0340c5c080d100d002c000808581c14044c0481d0312080b210f02501840c00030703400061810000400040824001c0e600885210170401d405000384151104260100901607030802c0150918480c054042e40050062004120b1080d90208480c0c1c17140403405421544040104042e945501004041070803c607a200d001c0c2c03c1c0400240c560f80104244039051781c45660203032004c03005901c01114140e1406144591 = true := by decide +kernel

theorem cover : BRFrame.Cov 640647482 640827338 := by
  have h0 := BRFrame.cov_init 640647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 640647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 640647482 ≤ n) (h2 : n < 640827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
