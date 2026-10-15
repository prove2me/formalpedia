-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:35.397517+00:00
-- url     : https://prove2.me/submissions/0a6f3fb2-6194-452f-a167-d128bfa51d47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 758273381 ≤ n < 758453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 758274631 1250 758273381 758273387
    0x100e01050f06090f06040b041a040606090f0e1329010506030f0703090302010e0105100509010902070c05060a09080601090207031b05100903030b1905210606060c0109060c0e03070e010e07 82
    0x6508217a00030700200d010303070078440007a003601d40011540d1060300f0450424001c3d8580382c070030302000f0126400c0801030a4a444d40b024401c01c0079101d01c14074001c14200180c0014082428064a00ea0009485201e0311040351520301000c440303880d1fa0360810034200081118034054007070707a00c24038140ca0241d0240d40c440c1c00032400b415404900f10155901c0d24005240c3d00350a0244030700c10300102d25904601c0d45080f04010100074103a00a0b011548100304140104604400c00416160203548a942e55000800201d4044250ba03208034400d006003800811003e0543d00244046030203076580500c0345801081c1101000c0d182c02000741543c0c855050301d9216a501c0d080035100e00e0181c1400a242c000310340c08550100b00c81c98019403120740703a9000b4005450102c541005400b02e01e80f240e40c44100d00b08400d1396401c40545136074440c0d40042004091208250890000f50b0351000d414408099100000781c40540c1c15400d0174401d02034100081071910710702004c0d074100e40500c409000303151541e0309c0a03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 758275881 1250 758274631 758274661
    0xe03070f0b0a1b030c05360913020123030f0f0601020c010806100909090c05030f06010f060c0212030c1c0302070218040606030f0b0604050f04030c120201060503100e01050f0609 78
    0x5006101c0140040c7c100201c00d02001c401e08100e1a244011401009818030110034100800038401d00902e07061202c101c0410000500041e03080c01d08201c40c18042482031908070340000e0310200c0110001c10003402c94064000c240c0102410707a000c181c19180c400040e42c5034a810a01c141c00500070500240840c0740084d02400340f4501424513100341502c808650041c0c130302044060780c030300303030070b903008000d642020028448009001005800654184070028241c110280700c4c541c00c1140807440542903580310922915240c07407810440ea17494600742c1020340c48140c0b1034092040d00d00000600340d1858001d0003101e00c5194000c1258000156240300f811030702c4070140c400e840650b600c58000c00003030354003960f000d030300d90003910308003a00c4c80d040042009440005080586941904d014030001a4024850301c0305560301150110605184850803401006150701042d40f61080260b41c3d4440a025031210803084801d50080c01165506070f440042000b054414903086041c83c4006104a1404025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 758277131 1250 758275881 758275901
    0x3091c020d03120f0f0e07060908070909050c060412120311040b03040611160c051e01050a121503030314070e01050c031e030906131101050d0e03070f0b0a1b03 70
    0xc0c002e6030130120207040b503030303040d07100303000f65a90f00722801031032900b008034000500755890b003d9803180c1000c1c0a5604c50031648940500305854040803010000c043c042815403c0c80580b050340c43e2030703640307540c1c04a0001100d02640c80c01940c01c91160300174800d00400301900ba113815580c1c9032520f4541c4044081d400104140c64259480e40e0710040181040300401400320000382a50b03010403d41407400440360254806d43c4507040100b814040082900d8600c44210700c24200300e6290f6403440001e580111030022840392103071400010141c014480b179650401d4a00a503010003030320300800340c82104184145c507040017044603207003601740c95031003407000784400200b040c142d0f070414000c102c141d20200601c046840e1100c034040200604203108015040c0e124080881ca607101d000c25448002c03c141405800f1340c10031100280110100c00e4980140010200c540e003201e03954400f600381010000111803040721407012210100b40810218042d80b01042420820310b1100080b8150540003440e4842c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 758278381 1250 758277131 758277167
    0xf070f020c060d1e020702011e170103080d1112130819050301090f0b0d030e1203040b0901030507020a050c0d061b030e100227031e03091c020d03 64
    0x4081c00072a103070304000c1e00d400500f080010544591005041e060100c5000a50003000d106114900150382d0202d541c0c846410b4900301c1910b03d200d401002c48a040244003010510140c4c1c0d00004104880900200002031180c0030400c40801c2140440b492442052401035140b16110080b8282c406128000c0406d0351296010a241c0158036142d080700c0320701c411003000480e6000c40100800101c6004102090400c40c6081201c9503903c800102c203a40000401340401c810311814492548901c040c0c0c0c44500380d914100e07503d690362081c004045900c01020180020b0501c1c3c00f00b641035000140705500700b94400003812a20030220240000c07101d84100c10b070744454640c24142280e20403603000b020454030a540c08114412012a450320340300c0c0f2100700342100e5204018208040c1d44100e000c030622420010814080401403000030b01d00183c1c40c0e00702c1100fa9070712120003041c20000004180111041d50342190b161039611520f00071003c607840182d007040c10080014002840385c5031010704001460 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 758279631 1250 758278381 758278393
    0x9040b0a021303030801330e0a080708250f03060f090f1103070b1603140f12010312030c170423010f050a051303121107080307030509060f070f02 64
    0x90241482c1c0011607009502007117074035005001411004100341043c0c0803421030080340c040310030365440c4000e90744070302c2c0020020304080e40c1c580e541d01e440b110030040002c10222503009440c1c00b00c444d207a00d1a140340c1c241e50315100d030307080c024500c80e00300030390807a000360004074060340c07440e05c2d204041c003c801c1040030300e1079461450000049170358440340411402448014030981c03040e41414a002c401d60008840d200091000d031800d141030040c040b018603494504846236508000303d28185010384140400d40c0c1d000401d01c80c80f4040c1c448c0c14141200e00134440c400c41145a051300741c04a4900950100001d01410200400903a940c141a0740040c400c0140d01e00c41908011044225818140700080d03e0f51107481d00700c0044224001c050308080031941c10415820550704d811101c5824180013400d201e5011204030504030154400c40400c003014900c3c660718035152805490b10f81c821165034000ca0314003801301d00e50010010b0740f039102d014107402043d40340d01c503030406860100c0110b07010401c61240d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 758280881 1250 758279631 758279647
    0x10030503040e0721050402041a031c0203190203130614040b09300705120a030804051203040320010513080306150d0509060c160b070509060a0e0114040509040b0a02 72
    0x840c00c024982084c4100040f0303414584100003d90782020300c05000880403289810081d580410031503054080d4504038000352a59050903415401400f83d0310040390420322130402c440390080018441c448142e001c6400030385d21001b098030300c000c00c03a0160301c103100c00303004c00c0c802000c0510081c0005d02000b050740b0b0300000d002d199580401408110b005543c000d41c10a2381c500c400800000025107000c80d00c01c1030200302c80c1d880941e2a61030801c003608110305480402d06000c4240450340c0c0350070a0b080e050341e680c902424080c121007068034070040800510b040d000705039071040c403400c0c4c0650850711800e010315a032038580102c0c4d900702602696010045004654034008108000c0818401d5004013198500c3c0c114100381c140400107103c0d60005400300100c0c602504c81110100c04903611030744128641d143d10000311054011400102e8001d0000200c02d400c0d41d0b04aa1080c3d0f40d400241d039071151100d082c407100d40280c01244540e68010755924040b0300004d40503020550300c00c0321b40b08014201041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 758282131 1250 758280881 758280917
    0x1205090f04151811030c0a030e0703120206150105030a1e140406060f08150907050d0b0405010c0e010c06090203010b1915020d0504091e05160810030503040e07 70
    0x8000b0700c0d0001040c0c40000700802140c0c40e0750101e400360280820412240c2d503c8158000c1e2200034002c0c0300d40710000800c10040d5010354020f039030212010048400b00350b02d038030384a00980050441074025204203000511404000a82206094010781d03400b4110b40329080e00001824100780f400f0903002c8245121201c0003254401e4580003c00301407580c145040c1801c0400845400c1e0b0408080d26540c1e180603c0300c1c0030001006c1d0080c101445290500e9660181042e041c40d03000d070007481d0700418070b14080c0c041c00041900c150140380608000c0000c002d00000980d100d41c440c03030f0441e002c10015481d800101d1450381c8050700e024000750012410242410001d094229904a1b1680110700c840c018405c20b80740081c03280602c540350005141615400d440a8028012403180b4015241c8400c0900702440d10840e40d0342c960004000144400e040c41c020610071040d80018040c00640c04100103170390840080c110b4030460350000043c503d05400e0410300e200c6000001d1401c401d104012a44d02e0395180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 758283381 1250 758282131 758282141
    0x6270b0702010e120a030b06031612061203030b190305060115110d021e06041a04060b1915180e09030f040906031a060a09020c0a02060c010917071205090f04 69
    0xa04c102c40c030355400300c0b4000075084400380000940224000d0003000a0300c0008001801206581e0030300003514504000c11102030545a005000c1e078103040e00d60301e0100340d01900f2034000000700b103170301c50400300241c1c072501003000082c8005810b40c1c0c883c07070042081c0c800d81ca0107180341c1301040c50065480c4120030580c42c07a207200009034800580c4601140800c64080da41c000c500c0c078184901610b0542083c1d01d61810045525105210a800038004a01000341b01e07072008414040203002100090800100403c1e144414421514140d071210310b1040c40c0c0d07110700c4000462440500710229228205107290303d1703056005084250a2008004658014401c00064001008a0400400e4140c2103203071a9406510000d84012061401c8090000c1540c0f0204001c1c150b0740d0518005031502c4039110400d14041a1040182d08880300140301a81c1c581c2c190000c52126010310b40d0000c1c0b070081d0380103014082c4119540079000341400103605610500c940010054444010560600790b003540c000102160 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 758284631 1250 758283381 758283403
    0xf1c021504030c0f0305011d06010302131b030f0c090e0a02030604110715060501050408030703080a0204050d0f0209010e09030d0b0105091e040c0e060d110d0207050a06270b0702010e 80
    0x200f84d4a000c02c02c011090056042804030340342072026280800b4401a0340c3c08042c08000c0c803481041007080a03403520b50340880c0240400e0500e49081c484030020280040c98012125280d0a0502c030160880b1800380e00c080007101c1405074080503035520200c40800a4002402d03aa85c46a00d9400441c01846042e002d050703d28020841803c5e550703e400591070484095900c00c9051001c1840104414840032007a0703020039401d401d0035102650344070182d000a10994004a5000d0f06001c2100140500005440102803080d0380b42c2502d030340c85049404038280c00b20b0700d05100303902c1000440d4010b183d035005900c00704c4060404508101c280300008084204240c42c2c080290450f0f20003d0445c50540180d854452090426171101c6c401d0001007411441005482c0503095150a1119003001d122400c03a4418042d100c0210349404151420a8403804c0a40303050b91640d040c440142451200340401d1400c56030090f484071164481940c030b0048112004000d0f0040d9540c50400c07000c81103050101858007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 758285881 1250 758284631 758284649
    0x3030b0f0a0b190306030803010b070302011416020118080415091d090c09100b130330050f03010e090a0605070906020d0c08030a09020d0f110f1c021504030c 69
    0x3c0341c014428408082c3c0480141c02054100501000414a14012641540c5070600b54695503000c6040a902500e071a402034540080c825041081e0a0041c02000c62805030960080c080b04000300382010b02880c4564010345040c80c100400c02c24140b0003e440000c9881c0c0341080a187ca5460007840003d501400e00480038208510812458240500c05407038152000c403406c11003400c20398501c1000000c203008030b60540b540080e40d0340310071040d1820034000b540d11035490306d00060b103844000205400030300b6516038404c00d800d41207001c1c0d0017036083d500c22014400006085a10f00084241c00000251100c07000d0b009a20315a00440c4040c0200c034841d4030a502c0d280c0d1001c1c5080b10080c038010b0703044440001c01c92021480400034540382700316a0820f00780d0320b01051403045800003880c1e41c60100c40041442d10440300201c00c200139078106503006d0208603083c03da4602c2c80414040311022040c44a1048a020f100100041c85d02d0446a81464100f030505400c140c1c8a558032903440c507098201e401c403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 758287131 1250 758285881 758285887
    0x6110304231c1a160f05030601021509030409060509131101090308070c0513090b06040509150709050306060a05010c06090c09090c0509090703030f050a02030f0414030c01020c0d03030b0f0a0b 84
    0xc64007090982c1a0003068594404c203405841042c004c0603c1c416803c03540400c400040403e901d60f01c01c2103450000d12030071955100f03d0800b20101a42e03503005100e01d601381810180001400d01c0d10508a80c850210119111010b00d103541d184260310650b11070240c18044116001b2020450941c0940b10303086c45031070a2325100d400d1504129904800c00202c41c06242408417101c0080c6800c004e01d42c101e40c0541d008240781d150360510a04100840201c100c458800d40c04011401e64410605011150705805460607a01e444080c070200102c0c501a0a010031480b884240005159078880c2d66400c2c0285001c1e1040358a600600080d40d025070016603407020f910300e05100903e040310049800070b40b0100104481469694040c0140040d4450318090050115110417001e00a20880e1040528200104e9949445031000103072400e800820601a200e04205103072154000100343c1c0d0000c100030080c1c0004200d40c2d0b421805031039000006600250010301941c213540741d00e1510005816a0560161 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 758288381 1250 758287131 758287163
    0x51201080c09090106140f0409021503011a0712110a24060b0403021f030f090309291605030405090703050f16050406030e0309030d0906110304231c 65
    0xb60841c0041c2040e000399160030f40070071070b890307040b0204002d821041c0e4804096190040000300100380424000e508115821000c603200603184000758180c032480960002c0000d10340c030b0341c1e8006014821000b031111f00313496042482c081c0540b15840b40500c5000803242081116501d180c224100b46110040440b2a650300f100a440c1d1809118060302e00399221504186c6107400107000c85100549200c400252141c2c2c1428640c0319030845c00c2132400d81282484880b0072031400034460f503050710035072a4480070403407425004078029000184c1d8024a451090801c0c1c803c1c8040141803440380401ca03118801084001100e44039405c03050f101e00040d403030018103031412000000c10801d00030680e007581f01840d11044100b907000419501991003030728001415241f02c000e018614498440582d60620400388084011644041c03108140c5016035a6a10380d1162103034045d5885c011401680c0722031070031003002501c4440c501800080d4000084c904400c03c81e02460a41902080b00c000741c64202156003108 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 758289631 1250 758288381 758288389
    0x30f1005180f19030909111801050a1d0607020306010801050907060c080f030a09320a020102072d080703030e0901052103190c050705010e090a0903051201080c 70
    0x644501e082102404503424002d80a40c1c581483c000c0031483c07121031100e02c50078503100d079613035402078040d81da002c0180e0074540c3c002c1181500301054800d4070b050807100484041d4070036416143e1201ca0703038988400307201c0105079181114450050309074010406020410150fa4100540c60003080c1d503100002d801c2c1010b2005509011584e0051801e10102d4240704000071440c0d401c0710300c01070320501d415403a0340300c0c2082c0304044e102d000c101030007226107140014171220301c403203144400c0241107407a80312811501c29403a4a5840744100607015811400d400c0081e50b9614690411040c14080541d45281656060b520b9445564000304010383c4118401d00c10180c1042440140e07110485d210a01980b5080020b0801165000441c00180722600c100d801c44004106031082d000015030120b509454018005084800c0c0070070544282c03140c0080043c0c2540502d654810100014061407129601d100506001e007038104002c504002c8104800c139000846103480a029010107030180000c1c182102c204 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 758290881 1250 758289631 758289661
    0xe2a21031305180c071203110703180501090f050411070606061106061504090b120f0102070b180a0215090a0b030403020d0e06031f0302040603030c170412020f030f1005 74
    0xf284141c5040014013040b03842c04001c0c0c5441c65400031048400089000701100900041e600c8002e6030140403031054101a0820034a40210107202d030910612a07981c1c004448840707441c4580c090710450040e0138003080c01e05401040e20110103030032041c941440e50341c0d240c0c02c8520b00e5003c07400140740404408244c14003441007941049085030050748105c49071820880f00d100f18425070b201c0655401e420344482d00c4864180d80d00030710041c203441c61107029000c0d00d800b0b0b5102600444403d00350f640003814644020300b08484e4119640c0050040703100a07401d1160301c0f603000150490b4044144031003440c41d9a000c015030060f05030300b00c00c03030749030b040c5850b000c0c2c40c00f0800d895034024401840c240c0d000c181c4800c02501d500408855410841400415125007114166040a03420a0400001000703261f00841e2400411b440b03468000000d11140207180301d28000d5002d4803240780440900d80b405480e06891000ca5036100505440d0011190340d0024038000902074100440e0391034104109800c2410905 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 758292131 1250 758290881 758290909
    0x1a060d060b030c07020126150f09040507051003111e220e060913031206030b0c031005030303011a0d021b0c10020f0303010b0c0c0904060e2a21031305 66
    0x200c9082507444c21410010b981c1f0051004040302c441000034045503555195011f44403002030034403c20b504142c1000d0762110603078000c2a0148001007003c0d020a40304e44501110ba02e08a80c0d11030400143c4181403900308a04004401250030a102c0b842d4a01c00c01340858100c5200c90002e490072914194000c0c03401c080c01400548244e05902c200039071007803c00b45698100f80d052811b03500c1a003900e0903490080c142c9810240100c0c416804020307176034096500460260895540f402402d030b0391071080640d684824003a41c1144c400000404e890a103103200906040b031041c1030003606080000c0c2c020940094105501556540030b04484801070400f10040d41104201d0320140600901070440281e9910040c4640050702100050582102d43c00f841000c0c0d51580042c0304000710b04040c00d010010708022101c204c02c0c0d01600f0560400e580e62045000200c00c0f943c1803e5001c0f04100042111881d040000404000201c07000b01039801828070040c034189000130340c80d050040c02d00c010711141e0700705050 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 758293381 1250 758292131 758292167
    0x1802120a090b0a0509010213080105041a07050a0509040204090507030f06050f220b030a0803010905010b0316050c0a15090c0f0509040f0606030c271a060d060b030c070201 75
    0x40e62008940d01c107242caa8044840840400c807a200c00460324024030810b0848050410340d0340012034910710641041e401140665081e1032032000e100d044221150040c2c5400001c200b00300085600e05d40680082c00d81464007c00040c1016510045002030305c204440303a000080d514a400e0002d00d8051180034040c00741074404500400d04000421000207411800a00350000b8030000100300406800c260010328000c0d013502c02040040c03070f000321650001e0050504040c00c000000c10010400c000b500d00c280e1120045a03040c0304c50380800d8807150b00c8140b070341545004140080b0b022a4441d01c0c1485109504000050080f2007801c040301364500580180110000e241c03c2004555030340910b0035085a00845810801c649624103400242000e078001450300070080d80000304d00526809461001d1400303030408220010091071402100c801d45103880402e5a0400300c1d9005083c072101074100203182e000300050300c80e140d00300700c0d415400890741e488c940c0c40001990b07400c5581c00410f480914080c48 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 758294631 1250 758293381 758293391
    0x30c030d0501082407052508041a190e030f16051c050a0602091813110906090705032e05011e14071a180606030309060d151802120a 58
    0x1113002d125038640a80745008125000c500c201c07180b941d0758600000c0c034142d20aa038030491454600f40d0483e40103032250842841c42c0d00c014001c29040c42046542c5072043c01655041000740c0b80c002d45000c1000e40780036805118262899202403002c000e0208a09100118080d0180c80c000c02c00c110b101403807007128011600345450900048000600c0350005500100260310342042d030000c46d0003041c0b0b040d0704011203851402031011742d000750496500c801e802003040c200201c10f41c00502054690640e006c41d00700ca1400006070350325224002546d08a42c0c096190005400b0011446e0400480d400300407031140ea050104101560300900f0b2200c50545030380c0014504000e046002d4a01a0f0360740941d07000e8000007491500b0459102d03045142d5107210050442e031401d00303a5030200714054a200841541c4254400b081d220b05e800406da680e00540242214581040d4040400103410300740d801c02c404581c00d100104541450885c0d84190240b4814010780310020101010407640010300800003403480c3c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 758295881 1250 758294631 758294683
    0xf1a01090311120a0b150f04060e070c03020304050406030b0a2a031a0901090905100b2218120305130807030503060a0b04080c01030b060f160302030c030d050108 71
    0x10403201030b450200310b07003001d6440b0b401201581082140f5500038100c020400030030102da4190240020100381c1900c8044100840714240011289140034091242007540001018584034079502c0790703000c1c40b070b205981c185960b8070003080070384d8540e420440e51000c198080054909a030b100d2f2901880c122000b040c941c500d16500450409038420304402090388034040c24800c0c044d00e04242c00851005880c49043c0c4d03a60351040c0c2c000300324500c0b0882d4940218121801101c281c0d00500d082d060005001030360721031030348480d0490390000e8030209010548170042c0303820445110f00343c0c015042c01841588500e984485008044030b41c01031a002080d0540002a40840e20f03d209441c040c544c141810350b41c03900c0b010001034009500380c0c4119224400001c002c200c112000c07070303410061035003a00c0c14005a040c050810555001d55196080c4d007a1051003118010354880b20084040d90007170040d81d00d050300d1918038504560141140c0418551110700400244904024a5945014241c22180c0c25000c03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 758297131 1250 758295881 758295893
    0xb07091e03020f0d05070e1303020d030605013501061809140103021002010b030a03031b0804110f0109182c1c02070b040e0402010215100b07150f1a010903 68
    0x40043c11030084041d00a044100042001703000050710700300c04424003a123031500d054246003030b042d50110700500034044119541d500901908050350303016150800424403c2e00318008078081242441f00d50148400d1051401d14040c42903406020070344d54202503516003002400c690022688000311540c60000c1d403800c12501d80b01c600b07064a90445401031038054800f002ca002d03044220541d0781c1809030b10164810983c050344207500400100e00345002c90100c45005540150341200d01400c40b16100d25061814035182c241d228400c00141840481c560b250b00a841003a60b404259280b440d568400300e0a0600161064010302c034416219000c62034031000089880b040c0718030005da910140034440b4480386000340040000350005000c020740303890307581c074402034640d4050b20107034054001d400860a42e8070f4402e4080d8410410045c10100051502c9a070500b03d0b844401c1c02e8528182d1081e01d100350b040c090061804407015124081050500d801c14064120241240f0fa814408101010000911 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 758298381 1250 758297131 758297149
    0x31403041d04020d0b07170a0b092707090920010f0309020f0d031e0e15070f0c030b09010f0c091205071710060803040308040308030709030b07091e0302 67
    0x41c2075203508050310350b407000c0b403054a001c1c2002010804d24604100344c03645e020300c07100340074510901400c0640d1138001504084482d5104010380054094001901c40c401c240c41d03440c400da03161032085144002e81d03036030303141040082d40020350016140c545600900060f00001040c1601c21200254410501e800290102c10440015410705880d560f1141c1590b40740340384008402406801c0c2107a403070706860010304542c0016008401044202d40907202c5510a0000700c544240c007900c0c0059183d00311251120350b800c160011a40c00305081c110000003100e88101384000d6208507000105418110080d60a641c2c0180080340000c0c0781170580902c8643c41b07080c11045800d005590302d921405070501909200e03158001c07050020040001d0080f170840060081031036058044c081004c41d4032003020a4483c41144000760082c1418007051002c51282310045400411a0615800c01035403542e4a81c1c0c03a180840d41000407480a6000700854a54244500300703002400c0811a40300e821980016181e00f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 758299631 1250 758298381 758298419
    0x14070806091c090e13020a0302090901150e060906060c420c0906070507091404031709030307122c0c0d150b010c0812011505071203020901030f05010f03140304 70
    0x312070106540031b6480e11132080001d1600035148030224074182c20505e002c3c24030101461782030342160030002180003840910b540a403400074071884c181d40350001000f0480c1c0004152440c18098011090600501f44c05504040c21014040008448011600e010803228440300d41486900b50000c0002841128048038501c0100f00c9085440c1e40d60b03800c0003850300c2520f401410520b881c22a01440e281044903066204522965a80031030049d010440100100c0c2a1000007445c1d00034008219003502600c0012256a0320101c0026450b0840e1180911860000b001036641c0d6050142813803c1e410a06c00481a44070a584c1c0488480169450b04454041d402d82301010702c0d07507490078044c1a840352144440980c1c1103c01e0781d41301c6c010b84c2104420700c0b03000c0c82088040c0c00100305441002d4001d0095480c150b4101a0b00d45551090403000d0700a54813245049040594414621094403281d00c1000d0190480c2d42d0644240f90851820345101d4030f4000f01500d85500601080101d11740c11500e43d4860 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 758300881 1250 758299631 758299651
    0x9030a0905151303060614010c17070f1a091002070c05060906040e091b10020d0c0c0f0f1e0b07031404050901030809040f05070c14070806091c090e 65
    0x80c0146150b101e10700a0400e008140b0380501000001d000399a0826402da5090f0142c510009000d80c0064420b041303030b2080107011028107540c144080c544070b0050030345540190480101e0184590f21110510b0880d54210f4500d40d5007800e0141e001e0b810026803040300d00c0d1403002c42c50171708140c40d841c000008501c0b82c0f91107035000158400840d1150800e0703a000b0880200c06c072400c0c3c00e10080c100c0d141c81070305039504900a000e500e04412403801401e20400070200e50060080f55402c1401100c030f10000b0700c2c3c156046402d1850029441031040340c00e4004007802c0046054090801c6a1001032141d141001d81d0045c00c0140244144840c11084801c00e40c0d240c100900c168124000000243c0241c0c0d0249500c158903100001c1403041e0b03800140b074811822102003011130032140e10a01290310a0303c5120000f0080c014600000721180c8046011030344240483c2c0707a140da05d52095150041c11500b0940b00e40224107001071401600d008009045100e050200000f400c00e0344021101a000305940e0384 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 758302131 1250 758300881 758300899
    0x20f0a0305010e01140613090603080414030d0504121403032a0a0f08071103070c0918120c02030f061303091d0606030402040e0d021b03010b09040305030606040918020909030a0905 79
    0x348524505108004200008c02404403c0c0e6900f810907280d0428410505541040005031015250110b100d40d5600204c1c0c0f601420f2508040f0a1041c000c4a40700440e2468100c14141d081004e081014500c95006004030480d05406401c8a2034000d050322100c9020b42024000250516002000c00400c2d90042c40d22486554401c0c0080795144c2d030b240d900101030f02000640308148110318041005540c0440010302c5101614142d9885410740b0f0440504061241115a1006403056560303074070180c00101111044c0c40c40c6464581080002d80b00701104040300007000c8100340e085413098006000240d171f1021249800200c152141100400303c61044600100150441d41d482d40201130114a074000c5803a07440700c0d503001940d180d030412024480c0c070792180c040c1ea1803841c050064202c50070b000382c0300c07001c6500d680d90166a00c2d040a030145034800c030180400b19405c00c01e0300c545840b501e004c1440301450801801800078001c0c01034028407543e0002c00181071120340002c0742c501204c00c00e070380f0f942d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 758303381 1250 758302131 758302147
    0x20309031b150a120b09090703120c0209090a020109060503040c0509071710050901080705030a060510051e1005090306130311010c0302030916050a0603110706020f0a0305010e011406 80
    0x303035407018120408940e00000c60343e55410f6520603400000c0c0d01d0110741c20448900f851040010034901110404070940c44840c0600014001c4d040a0000420604103044441e29550002d00d1190f0111a950b41c1540040c3c040e0040d9070707110092000900c2c00b03003011031640c10a500c03004950069400707414020314208001c1002c0a00c0741500d13400425003d680c1070b1490606500c850445011440390340d20403c151310010403080d1703010510380b08172500200200200300c0d10f540c515025140c01000354103001c4c120440000c140e2030b2400c2d088051596542610030240a0208010782d10a01c6081402040b5050007881115240090200d40029002151a400001e00c0c982119082007504007082d055003845900f00425405401440c003601d007640a07038106030800500000d82d60344da44101a4030094031001002141d01030303800042501c803e6800c0601d04015501c0da141682e01c111100b8a409200280004000f03074140314035805003d03c08030252240d45440540400084a410305a00c190390020b6044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 758304631 1250 758303381 758303389
    0x10c11040204121b0617270a140f03070605090a12111504020603150d1407050f04090302030a050a0210090305040e06040b1e0409060513170906041202011205010b0c0d020309031b 78
    0x20010f02c0d147d12038507901c3c0b40214610b94070390580f50030894001c43e003407003641e041e00d1010840c41d05220101000703600301a41600c070790001e440c000c0e007004154000d502e00880860291001e4003144082c5484640b40c24140f036042c03a19000e4a10b041c1c00b040555030081c4030060791044d04580c0c03c40d00303414900521107481c00c0002e400030f0043d44010070810f000308444c10880000714905080341e074201c600c00480540c05e420b000c02e43e0b121100040041e0420441080f00501450140c80a83c3c03c1c1c0c4100d401010b50f900410b003c55080000690200b080440d0821110b010308185075031107072060b41c06102e82c000e19008980c1c4a4000320a85050f000c404c02407160a48403079000c040c41617045102840141052001900f05203480541138800079104e400c01c04610007581d040300c00b0701c4009001c40b850603140c4410345103009401c8004030b04014a80f9100701d11034440b8082c20707010300701c40051680da030708520040b1840d0040202912065410030b000540303850b134000c0f5000c10348408803c404900c0d50a114001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 758305881 1250 758304631 758304661
    0x305091507030f1e14040b0103021512010b1306030c142101030b040203061e0403050d02040801020a09080f0f030708130b04030f020f0a0e06010c11040204121b0617 72
    0x4000350b901d0900c0e5000b2880c4d131000000140ba9010350208440100150b8940d00040101e4001c3c00301070fa4107004000505140141084170044811494100441007010680707804003030740042e2884101280807414403144540c024000d00c1641000c2082134511200906820700400910340103102c0854403c01003281c10b05200650014032030101c22541e100d16103066010820b80d0168040d00c58003000074200010110540101c0c0300f45603580a43da52281d6040b507140d40002c00507085150244400104d01b41c00340081e060740c1189488141c800f80c103100300380f880c010a0a80c00401c4d030344400103c09190201000311400309804c03042d0382c0c2d40c42e00c00d001e40304070b0480b0030707840b5510f1004001000802d201c113280510fa200e610840300300500d2200c6200700500080343c0e000c1e40c81c000b6480b0010518130760084200114041c07180712035624503048503000608a800c19030051402c4000d0020110812180b04003003c1d40d0070078244041495424203d000700b0300c4140b00e1494400f0303601a00407451030b61449100b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 758307131 1250 758305881 758305901
    0x10203100f150e150f0c12090913030c082802030f0d18020d05100b060901080c0a020f0601140301050a05011a0c0304080307081803060402151812010c020d030509150703 74
    0xc103a5540d000115038560a520044c0c410a540c000c0300d07c03405519445170701f1284280d07001081d0600980300c7e4042b4079100b50204000f01c0610201c11705240c0066200d0000c0c000b004d01c1a46690401b4040c4800500800d40030041c0c5421900208040c10800f0111804e0b03985d0078417600350000c0d08070520150301500c2c10106101941c00200b400000c0304001d400901610f50f466920418440a24540180100e9004001c1e480b80820741d1000043c1781201d01001500d020a4948121840019240d040c541403500a8000c8110b00e001d451401080781024040e490300701d000305104108642c5000b509041d524491031030300f82441c4000030042035038038041042d00c002d000544103403a82c07240340b442c005a00743c0c41000c840b13507240c0b03541481420030301e00481c8181c0300f1900580352101c545140045406550712068281ca080c00007a00c1000d51034889000020140b003094000144400c030340d00c0003a10740380180c1035003c1050b040008008200c034000ca800c4110361585401c2c04665282c4940550142100041c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 758308381 1250 758307131 758307169
    0x2a030512090106081902010e040c05070210030b10020312010b0310090507050403020f01021c03020306040216060e2e02030a0e0102070c170c01050708070501021902010203100f150e 79
    0x184064201d0642c40a0308480ca1041143c0000c260580305025802021070007034041064039448603164100f940142004070782d907160443c50032030f031580000e00704c548042c02c0c0030000307a0703645a0000340e013003071205401c0380c1071030f0300007107040614044142c0c03401c102c140140c0310891808004101c0e0703a4074160f41c0002600610308140414074104c04014100c2d0071610040c2d10486030805040d04650001c10700710304890030071030705008050b080d010540183d40050221508180d00700010045034940c2c615109455201e141c010440c0c1c0305000f01030307103022844624003400f83c8079a61440141580c03c07901461454000d403001d61030350394039a40c060080002c030800d0913913540001802d104001c0d10300c20500036039501c1085c45035020860050341d40d680f041000300b540480c00401c2584085000e29019100d92072194001518202d04850118118000007070b503070700036179000b10612483c800d122141d01c0141042e083c0b0181c1052508440d03e00c3c00880c00100d006011850200ca4056100d5a00c4405110001c40d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 758309631 1250 758308381 758308417
    0x20108011a1b010e070e090d05070b06040b0f0d060209150f031602100c0c02030f0303090d050903010b06041205010c031823070b1b0109021f02010b090114040c2a0305 73
    0x207006503404007107c4030840c50203102114403000380168203840c5100d0b04404607000c142d0f205014000146101000580e008400d0b00c0803030002c1d607a04409092039842180096115010f41050096480d03840c10314600e00d800500000814010b81c0040d01e038030044d401240b00b030b25400c080342a41000b94541d06146154208003061949a402c8a9202026842941101c10111641601c5612170100350340f003c03460b802403424007000c24070603009440b035564000c000144a40500c400a5415441940710203079415120303501005100e000c3c031484042a225003000c0c0220654501f42d040c02d6912004014000300c0075104e40c072980074800310030440948408048034106522a415810150440700e03040c1c1c084007003034441c15840c40040c015200f2380759020b00400640261500520043c04c2144022000c40d90f84884900081d03555580e2140281440b4000c06d4400120798144401e0700d480340811130034484001607441c10307141d126907040c242d200b0a40c0180c5010400385802c5606100d20b10159084869403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 758310881 1250 758309631 758309639
    0x150406150f05091e011710061e08030a02060402012d0e0a0f360203070903020a0b030f0115110a051b2d010c1e020108011a1b010e07 58
    0x780c003603441982c0d41100d031100150f89040d0100d150b2150140c0e682c11500180004208200b400101c0780c541d424802c080e50410700c50800000200c480c5584030003152800d04d888018003d503004641c101811441004d140780c2000260b000e9560840603000030f042050030000c0c1c2e071a146990291000724568540d00b01c0140b107180500a00c1c40c8040300d0810f03c500d000c104000b800c11044016281104e03038020000004c0300b40c0310500b114043c02c81050125000c256050001611881d2004504c11040da44856841d2030560060103c162426000b01c44540700c01c1081c0b007501c009010196044400004c0e20052884c81140c044a070240804010806841a0303400b80080080115003060900c1040860004003103082c01009029800c2a60041000c00e100c10040320400440540e0000401c040c10a0324406a4555454109881411411003500c030407504400440d80d00054190040500804c90030407a40310b09540001031180c802d03100702042d030b001001d01d051082074000b903082d8002c80059030000c0359a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758312131 1250 758310881 758310899
    0x80910050d050f04020f0a060c08030a090c0b030109051501120b0102030f072103090b04080c0c12030d0c180504050402040b15032508010303110a080c01021213030215040615 76
    0x84e28201d10901c001180d650481c00e1a03505441268040d0f9140244168581c44001841d84041c200c0f2125941318000740000c02c07800e524980050000d2551250340303601d480f0201080b650f0180000780041c944a51001d580e03a4070000403910031b0115040001c03100380c5880180d00e18418070440100210001c0391350414460440d50004d0090042d0420301909844a14102c00b113800251004200b5440c0001203804203004402601c1d02c441c03181c044900300b00301170f00060381001088502000507480040c0c1301c80700c070709103000d008030706a12420b108035105000d81c14003001003268041c1d03d00581c0d9510000d4155a1550401230071060040c02d034900c8140c140301d1000c141d41c03007111b092000803c101020b904030300102d01c1d480c0044005542d00441d0b40d0942e5000c03078064042154810440c4103a014180202d1038400c01803105e510754000041c0c2e51001c00c0f060010b1001d00074064100303035000840c1c01021070303004030310940d00302c0464143c807807560f0311441d00c0340081241208400c0650704942e8007042e841c80d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 758313381 1250 758312131 758312161
    0x901031e0b0109050901150c06020403020a2408150409150f060305071208030109090206070b15100825090b0403030801030c0b130b0a0210150314060103080910050d05 73
    0x2800c3ea40d101580c0c2c2c440c02407200d101001c1c89603044101c0060303c1c806246204102d0000818803132a40545855541c3e0001544803001d41c00051510040c2c0005902e154840c0c5080c00e03c5c00881e04185031a482c00c5510f905c581c040003803030580515140c0c06040708010706103400c42040020500304001803150008948002c2929002c1141d10b44030752500841c4d0340b0055103035041c2e82503125421a01e9070303013001d8100000d441c5e40807007207030030181c00e1210307100052800d08000d02c01c004640241d8840b144107003c0200c1c003046401050b0500010609001e03c00c20084040c82c66089100c0464800c4100040102e50802e4a0340c4150385ca4240032070007004040d8025103850480b0702a0100c803140c640c03540b051210070b10903141c100315500c07070000080001481031409400310105a0055a04064100701c9031070a03201e00742d0800101c08e004400038001c02003114124006040003000070403440d8150f43d074405d194854903120300d20038241c5480400645102c0ca040f50f4910a50100c203210074148001800c3c8025 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 758314631 1250 758313381 758313401
    0x8010603050330060103020a03020c0a150f0207080f0304030207030506010e07021006140d05014802060103060b0d060c02011e1512060605040204080d180510050901031e 74
    0x204003c19a2408103030790202d500e0340c00310040c41640d8a80c07a200b006400950050191a040c9034003400120083d08050044021440c0142d44201081c054a80001c0c100c50b08a050b44614070710500c480400302e0300c4007003914401030590390016540d4581d8101030b441c010740d540c001003040c4210000801c05071500703403400e401010f854084428500c0d562107480b09850760b82c020b14a654903520b210700c401e4030302408900c450328010000010340710810011203904103002c900f44511650801e00d07400341020402c02c1d016a44800c0d000c01800038421139070082d1540030621019140e41d03150780c030010150f1348050366009840e9000030208030f015005070010340680840072062714005040003c0210848081c0503200050b8551100080c490703040c0865003224401c1d9480640701d0316600c0c0c1010495464a100030400340c500c01c00281000311381400010301600341105d4100600c041301c101045a43c8036442c40500d00c400c1d600701036032640c201c030004070000c245640713240c0401500039070541c0d011007180e8080a001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 758315881 1250 758314631 758314657
    0x60f070c0303170a0b100302031f060323040b0610020309031f0e1507030c020f0102040602061906150804050c090a0b030c01081915030813050a0801090b0406020a0504080106030503 79
    0xf6aa02000c0c10116440300117900e402409201151860314460b0b801960f00c0007501103900400d042081600351590401e030030080200340e8404401c40c0c0c45030300c0018107061440782e69032011a40303840c0d903034078405031405441680aa0402e10041d94000c0c003d106403104183d002d400c03100181d00540b0101480e441c540480b98100e4a44107201d51141e2004c1200c89803070b800455140c1981c1c07030750788040b001071030424101002c5000308042c1264142080c001080140100d40c020070f0142820084a142d8640b0a11400d5600f46022020803080066103582c000500729810100d4081c0e6803030078031508200701e0140c5140d10040c80802c00c4116a001d5000c0250b2050990864510981d5500150345584060320150f82c00c0b080d007001c1d44260001074001c0744802003007001e245003050b66070360f441c003480d0086000034540c41ca0084061019040c0844400010400b1400a000082080e00c5040c144a0045d00252030303c0e4001410b101c03101c3c05601280e00400000e8002c02810750b0742d0030400e4890700310861f44055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 758317131 1250 758315881 758315927
    0x9150b070b1b0a0804020f0406030f2109180f0212100906120b0a0e0a0b0906010905060a0b1801140a0512060109050306070e04140108010504020a0e0c09060f070c0303 73
    0x40340b0303103001515030104550f11400407a4a03103400300a844460394660395030080e01c80702c0110001d60b10088218001344034601c048140d4504246004201ca00301807130000f0030494040c20040c004824001d00e41c1e4480003170f0005410350700c01c0804c2c4080d12401124407203108000c030501a11040c45070110040341c0e041141008101e0300c90741e800400c06c0b03140401901c50241e0b00b0100f104410207611103003540195504551300040103a95903040b200e0104e8001043c1d400000040081e103001d401392035807082c01240c0743c41c141400c001955446020702c2031582c0e00812030100d4140303264080c81c03143c604669140b81e01078661041000c02817190b48020342414111141501103003a65014100c03102c140d60001700648456904c1001c22038200c160750310b0341da6000c0d4aa01001d00c8075800c000c2080d010b010508000325039460310303006000041120b0f510441e814100d180811800e00c4047d41540e450103811600960303100d104000450081c01035520141c52402030000000806800c0303440d070320403149100e1400c54 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 758318381 1250 758317131 758317171
    0x60922060f020a1e02030a050708090a15050c060108070501120b0f03070b0d060e0f0601270303030e150103030518040b031009030809010c05090607060e010c0f030e0c0a09150b070b 79
    0x6103038001d42c10a4004102300b40950000a001c0001400302d000001d48401905a9662550074400c003c1406001c04140c0c0000d440d01816400d010007809000031000410400f807420340020300741c2d403410341c010703460b240d032140d040e4850b550700d0140001c1007100804440610f40c49110503071035540300800da0011585011000140800c414035110300c00c00740880e00d10495036032500117603141c044950030440002e04060b406450b254405100f44040c5003e41c1d00022181c0010001c01e00c2c21f00a000d80e5014121130400400000c0d51000c1101c014140005202503111180350214014200d081c0086030705000d259200b00300c1480c03940c00381100354081c0d5209140c640b40c07115001c0c200e80741d100c40040050020004080142030140041041d02d208141c0000c1441d45110640d00712038008551030f00081d207440d00360503440da05d8005e00d810070b04044007412100e1100e80014044540700c2c82a00852510f130018062983c0c0e252014000070207450b904a5a03421240c13401c1401c2c02001c5800310b04111500445030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 758319631 1250 758318381 758318383
    0x91518011410051c0b01030f060b0108190b061c0e0d050c0c010e13020304030c0302100b0913020301060b310e0f060307170c09060922060f020a1e02 65
    0x1d40141e02001600c00e826003840c0c14007400f805280e040e8402034500305044130020398404801da008500070000c90035144503e103070180681c0d10084e030883c1000100c0040c4801a410044004420507205400042c1d03d03500e0f001040c400d000b41110f003040e01c1c0b288800da1400c0c038540d0b000303020b02444080c00da554039441c0f0070307054405006403024140198000c2400c4c44581d40034a01e2040300c010003c15440300c4d054450031503c16a4403c840c03c400050304000e480c0c08140c0c0400100004864000c018007040030b540000c21000400142401c1066030341000007400e548003944410040c0802202c2d4540c0d614004083e015001e803440038207a074180700300603000d4005944240001c25500510359001482d00c40c0a2130000342d51014100c0c0c2c0e4940907020b00050b8003109041c076540c90144810103403c0e0103600104002c00e150300201130074018454001000800886118042c0381e60785103500b140442e81c42420309000030450400864001c4d880011409400c0b42c1092492f00d0110082e180c001d640b04182c0012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 758320881 1250 758319631 758319671
    0x11190902220816092a020d0306060914010302030c070b01030c171507050714010c0309210215190c0503041407140d03030e030412050607080613020309151801 69
    0x3c55a0404441c4240004811504195400340c90041c025403641190052011142c1c900700c140405030340000035040109130140590700003801141004a031484c0380152a842025001807098100359000002a00aa01c584299102c80390458016205981c6038600014140d82c28003a1200241514844241400d400108411990040d00d030110690319403400540355034002c1d0608030b4000003018048044c030102441034102400c0c059401050510480c1014100d48542203004182c0880c204440021716400258002ca01000101ea240301560f406d03490641007180041300013000c03424000703032900341030b44031001d076015601901144034031692000c240780e0f0318941c511805818010344207141116150000d0300e407080501a08003c181d414211031aa411544240c002c07401c04601c4401200074031004001d0b05a006000b81800502803c01074001550078060200e0400304580000020b041c03154180720901d115a1154000416401c0407100452202075180800b907c40d880c00303a010800046071840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 758322131 1250 758320881 758320903
    0xb060108090d05183c040b090c030c07060c09060f020f060403080a0204170303042f1908100e52061706040603111909022208 55
    0x20540b40a80020324030750b481c0d80c01220664806060036802001c0469008100042e803024840c5d00002e4902c9002412501030500c0c40a02851400c043c1e4035090321003400301600448901d500945030f59a521032403009201d442c0001385103e05040002041c03a07041540030040d100c858503480500c030040c0800f2640c500541c603d20055a00c61000310340400d000d017140700d80044c61440054a40307038443c8001d11042103100b03140400c0390b10002c04c020030701407103c2648045142e41d6038510002c10354500d03803003d0706c40c440008034403580298111218a030301807500f0600801082082c0d815002c1d03802034a4008110590700c1603818011005009500e003201529102070071b0782619600c11050301800340c0300102c00c03501c00240400180018000c003007010545102d0003031545a5420f0ac1401c103510443c1c103803c0c805403510380241c0c02d0040a000250050650b0703450780a00b075a88281384e0b49401c1c01c0b02180d503482d0f0b004500c6580b00140c10400000c205c0202c00000c8030783e000310009196505501a038890010301d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 758323381 1250 758322131 758322137
    0xf07291608072006040c06051207030519050a0b09010509010b16050f1e121804020922060e0c07032a021903110405041214160b060108090d 61
    0x50280c9414000c4510350b030041c12600d8020f1010720024100300000124a01400e036660112041104214802182c40050301d407515240f0309080b881440140d030048050300d0841071649480010350380100d4031101803010f0421850603c039030300f80204110000c2c81141e00b428020b0900c1c000200d61070511001d894125001003510a140400454406561141310391040702c2a00400000d42400c44082140c44824584400c1d50101c8a18000e1007524080d0782c141d14010203841130005008400c5a218481100d040558000d81da503140c000004600c400743c00580e00095003c42c91080d84038041e13a110f14203407800d02e520840d041c3c540304150780803030141c0800140002c40c4007a00111203000310150307c18a07140c4203400c3c01035040c95400180054541032a031161038411840030020710a444206244071a01070341e08004504180e214480601c1c2c445003030700140b01400b294100e0300222201200c50f100760b90a0403070401e90239458034900c5000c0076544540014114030100742860301c0802c4c22005602541c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 758324631 1250 758323381 758323411
    0x150c110c190b03010305010203010611010e150a0e070e102301050c030f210f0f070f1101180c0618051512040506010602060c090901090509030f0729 65
    0x10070880c4022050803414100c403411400001c03005000790246002e14030400000d80c580d0304220f4020709543d00710071003c107140e06010009149400c08221400d544180815800140d41c4110f9004040c141c66980501c45214030980014690246084140529804101510040d40e1401701040382010b0181d02100125402c0400010b50300500003400460b42000a0301d0400500e5202003050f6040503400000c0360400c20110610100440ca080703510004a00c0c0710310807420612010503800b00018868030902c80700c000a514400c0c01010616075018090000707120342c025440010400002241d0200c462000016010a6450061000e001044e01d003541000807185070000304110203002c0b222000301c0901c1004a07480e00207051805501c241e0241008003103651601d480245001001050906e0851050224046982c2d0b10b018840c11101c58900c00b14940e02c1e04628141180b00f04540c180640c0b00015120003000b4a515401d0303082c01140c80110a4001c01550f40410036500310360401c144102030b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 758325881 1250 758324631 758324653
    0x3061a100c26091c050607020303041509150f021608040509090c06250b0705030f01151b1e051c05030408160f0c0b0c060c1303020d110d150c11 63
    0x70844030780c2d04c103041041041c600840d0343c440c581480d0003039448200681000080106100f840b6919106001c120340080001081030f84403030340d1000010b0b9280ca0000d403103500c0220303d500181c058882440c52114002c9000c4d8030392a080c0c0d1a50312070301c50b540c010b030990310001d60000380104100d10000b1000d455036150450820100740749106518010840c04280b492801c04180b2103078050b4802e0200b61203055480c10b060800d00c0005405a201c0c0c4e8130458121480742c021035003c84c00f115920200c1610300702607900c81c98060160007c08204540c131402c2416002c040c040009030380f9207071380c462924a0a101d1042502183c061004807000340441408215448031028159a0464200d0240000c074601c00510794030901001060b601c01084004007080000c5116402d0200135007003102c200d051850300894041d03030480303003443d4400688688011304602080c0400c555807503000316001005400904841d00d004065100c9061016091624021405205030f01030400900e8149583c001840110a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 758327131 1250 758325881 758325889
    0x3110102031b03072327010207120804080615120c010801181506030f0b0103022106060c120717160b1305030403120311040f03061a100c2609 62
    0x4060304a00402c40e0b5482000c1092206101815066218078940c9949410301461030b10300c1c46d0125000c988144605032614900c3c1c0e00000d80303500302da9241c425201903030361301e080820140c0181e9200a681c2d000d09402c10029103013444040d20352020840d05119442c448a07001651000342d83c501d24082800c660042c00140b034a141c020791070004c050000b161030240882864100c80c000e921100110307403a828014000a860302850036080360030310742141044000f20307441e03850740303d44c1d40a0f220101d1004017045054903181c0c1182c0c1080382c00e1003210310028502c164040b03540c7c803421040d10ba941c490148481d104a5080c01c885c107040094a0019041d0340c55151b01c000100d0140825081d42c8540d80c14400013002400a44021030240140c030000300ea032100080d050f100c103070010190741e40b0200024000007443e40c440c0406d494000c44006842d40400b148030002e4201d00311825804940030107038280b810351000b110b901c0c292017801d21b40e4402ca042401d542c4943e00501580362450410700600d0100c0c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 758328381 1250 758327131 758327137
    0x150c07030b190c020d091409040f031b080702040f020c06160e0d0503040e0f010305100b0604050904050c0f0f10031119120b0f06091e190303110102031b 67
    0x8041004040881a110103950072103200120f00c20158000c0c405c99082c40341c01079903401c0104954a0a2409200b940c00040c015010050000301000414420b45050500c5081ca40c03a40384803100314007841800c5414008850f8124100491040703040014043c969003640c02600c941c03a0b400001012107440755144508681c024001d1101082101710440c80b095031441d80546201d030041e80a10f654034144410010080d034020a544160001c2c03e00400015000084902008020100c0050109055400101175100c1ea500c00369000b89020284002e120380480c0e40720501800300e4405100c00d00550611100f600f003041001d40c0720801a107000007840c001d0700700346d42254882c00e450b072a000305071550010140c816640e4600007540c02d140281c0d40c0c0d46c10305c0f0790307242d10204659001509409100080051080840311030091a14401c84464180c10500c1a41042c030003c00c0080d101c010305c841c000c42d2032000d20099001032103440300058982070603c2101c1c0102c6c00e00007100842e9a0314003000089074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 758329631 1250 758328381 758328391
    0x1401030201300b01020c0409080406050c1606050a0e01080705030117010603060207060903140c0304092403051b01090e181501060806270106110307080711150c07030b 73
    0x5079608008140002da9000d0340d92484040c000190790114080024544a224001580501d142110040c04601c0c814107440440d152407504660385c0a00c131508a08182c400b0294410184030098046074454000d0068016207041c1d9840c214a80c110b24011038036601c2c00d40d07008000c241c08200502401020304103807861840c5040c00070490542e240d64820407030303002c4e40c0151401560740c24050100342c0e12041806445803200521818075480648094a078862880341d40e07401c40d91520310312207001c40c6407440e4802c440300310043d914442d601d0030002d07154100b03402550011071610030648070640c02107440e1002d603003888812888e982d998050075180c041448007003000740e01c92030410b09404607010503414080e00c517598a04070f01d410320500340b06001c803200e99509002d607004807220300740e48031a0030070754110f4060f450030940700000f158426095100d021000707094600006140f505211074081405004034007602c015100c0038040c00d4442080c00340c1c6800b101c0031f800c0a441040880c3e0080d82668000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 758330881 1250 758329631 758329667
    0xa20030703081e190608060c0306030d0c051c0306030f060e010f0e0a0b0915041214030402060a0309020a0506070b0f010f03031b060f020c1516090506030a092307091401030201 77
    0x1940e1551505443e056044400748c02820f000010483e80f42002d10201084582d80d080041c400700d00ca41c1c4403901c2e00403042104000710104031a080c6ca440c0300c0d070410320003903800045009843c0e0182c28003502070145081c1e495110341c203100e04187c02c14402d10603104000010800303040c11305800d03550515006000b4042d003050748100d90300340d24903a440b07040c858010b504c03e030103101c45895008406050041034550310803001c50306004010240e00d43d2030844540104906d40044c3c43c3c402e520000d10a400e81d07401940c2c00c0b0102160301e6041000020015024000041081485a0341c070840a55403a5603400014001034000ca2194042ea0748607a802090030310884001c29005507510592040382c105805400f02d952088101c800c1182c003900c240c3e03400030b0b000070120700c0d00d0984413006025440d040c82464085c4400200103800440c5c80d61003110681d5008220f0803000040e10100486404040b0324030b02c040c01150400564541315104540e10828103001d00407840c1e10f190015900881410021609 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 758332131 1250 758330881 758330891
    0x40c0e010b1c140c040911030106092601110d0501051c080a0516030306050f090f07110a0b0906070212040612020c0a0516091d03030a020a20030703081e19 68
    0x400350042d612440c01240d24a445c3c0e0303e055180402d42c1c0b103011803003007200c8040005000316907000300320b401074884640154482900c41698003000c903210003000b4046528203108003620403103003401041950840c47d42807243d640c03140c3c108003c0c0d580070401c4180780c00881c060340e40050581e002401e401040e81c100b55042c85001503107209240e0412004a0020703070b032440148058540501f0040035000c007911000f10030301c1d090051254004019001c4420700a82010207441081e080100710b0780c5542c00219414107040c0002a644d40c2c030300581d60302026000c2c1070b04611140c450142a60219542d6950b107074000c0b000c02800000940c44103012552034080c2c070318050007040e41000490300c0c0300060f1802811080c40c0002450445102070980030305450b1907024a500c001000082c0d0750003d40c200230040e0741d40c1c540b0000392001b00c40c00450002c4140c844007010b44840d80031004d8000c490081d12860b605913500392191000360304403550041d0a0707409d0b00210359018001100c070340050200000000e9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 758333381 1250 758332131 758332151
    0x309041e06240e1f08041a100306020f0412050c0909150106030506130509150702070303080406050a151202090a0912080709211b050a0b0c071508040c0e010b1c 70
    0x600510555030380001301d03076110240070403c00111005032018004601f54031050805113a11552021f1174072025129540224400090509a10440300203000c0003da0703045180040c41d00d1074603483c0012049200702c2502c03002411000020a0003000e950b054041c0d9141a82014029001070101801244d002407010035500603c881134411207000340c00750402400000c00050440da8000c0006000c1411900400410400030340c020450b0740d0819401a404038540d551004050f005120309000004183c0e8105400508401c078818880301c500d00031740d051607541e6105e6008034103840766a180204103640c20034001030b0041c41850100e40049491400c5900c2d10360792030040781d801080c0c2c0b800da036545809840b124200401e180001c0f220010900602c03e0242c07800c00007541e08440380c03084035408440080c0c011443e85041c401c0102400309908115100f04040710010907294040390111340182c01e042000c1003012414080504072400b883c076841c5800782c0e15010070318541c0c4000c0d100312a141c41e281015 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 758334631 1250 758333381 758333419
    0x7030e0123010501023d021b07080c012a0f0b150a030b07030506131b0224070507110307030c17010e030a120902030a290c09010c050309041e06240e 65
    0x8041c0223000c214003603020854002950900d4020352004080341d100800700f1070030703076002042021082c60812002d200e0b4006009600b011030007080740201034801c0100035400300500500324034003c00c908504400d4100c901c5051003009021800090030440d40340e00000d0906203e5000782c0d61081000d480490742c0c05004605005444901e0480c1006001841e1505043ca40c10840c010312428081c40340b030040e9680c0900d07030340c014038003514160400c0400a04002441725002501d0b41c03283d00a000c43e44d51986d80d04040c4942450340c01900c80140c0c0025920b1042941401024440100d03000a18603021030080b05035404401107681c00c0740f95403144510320140e9030078498540c00502905800b410100000b00d0407100410f48118011820801424400c054400c001500d50002e800e0a00c0320003401c41c1d007840d82c95030040850703d41c0c1c402d00b048408694042c0e0b10390400b42c040f003c090244a0161111440c2264844003401d04800c0c090b41c1e04a44900c600c1250644d6030464040d040d840e45486001c110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 758335881 1250 758334631 758334637
    0xb040206070c03050f011413020f030f1c11010209011e0909090b0411010906020a12030905030d0b01020d11101d0d020c0910030809010807030e0123010501023d02 71
    0x1e44d1a60801c021003124100c0a01132101c0c1802581d00300710b990310b401c0f450050400e0b55941c4c040d0240c1e80340110703040f8035101008080030a00c480700450301011078000120a1540d40545540001036001c0d0704090241414020340e421014140c485c02e5040524400c3e01010b4044103980d1010010703400d0000903201c88500c111081c407405003800030100d10341414003240341c8042035601410816245002c00c40503031b0114000212550148080800240c880c0007100a80f862100c040c045010004110404020580c40b180014000b03809680789018185019542130701450100280c41d04030402c00440e051895004c1d8020300080d4650081594600d07551310300e0001d642d400d4002690103515140074510780030504075840207042d500d41c24810709580e10802c243c01404a8541444640f40c04100d81d180039810442071286071000800849400d601501c40040e0048000307400c41801c40008a003a5101040d803040072440303c43c0700404140010b1008544120071044003100d4040841f520240c41654001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 758337131 1250 758335881 758335883
    0x510020102090f011707050906251a0c0409110d020f031009061d1e0702071701060e04030507170406170603010c360902040f0e130b040206070c03 64
    0x40c2c80c0e4101a080c00100b802d4406100c1c1070012403c41010380c0c0031481e80c0f076940000e02c1d1500301c1d00d90744282d0114502e40662000030f0705000e5540c03074000c011f03801c100e0940d0b5014040d48024401c286401e0340950510000d4800c4141b84d5001c020601c0850815040641d8015124040342d15003200194175101b01d81002c13840311091000041480b13a40c410002d031010103011044c6041203007a140020000c100840341400854018807170b8005640a6440c10000c10301c40b00c02c04e80000c40d03103448840251a404940100e01c50400c1020800b42d00d000c0503c1140b058170000c02d40c500894645440079112608604000c6620500902510914942c0c55002d08002c084544a0300d982c2c2404850441c2940002001907009030301d4514640000341d808092441c10b02240505403014840c20f502c014501303d200305550f000c152041800264040c016802841207071803800c20440074035280e403032143d036400050720b1014840d2401c400050220390b4090106400500c020841e51600e081695014013007519948 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 758338381 1250 758337131 758337133
    0xe100207080733020304060c020607141e0105061e0a08010e030a0908010504020904021e030604080a0306061103030103063305030106050102010207080d0f0905100c0f1b110604051002 80
    0x429981c240803c08501d00b032030b25a0501420107407500610081da0303409280310310000c02c441c0441003025502d0380022282c00a41001d000501052034000180e42c0b100e01c1c0d001c5510040e10154804c282e514103204503802100b00616151240300c0b00c0c0b06ca20400740941040c00d502900d807040000340490240b04a002c4038040d10b0103182c80d00f504102c06018441c8541c0f140d54264100410000180d842c1c4188a9005604403a52a01b500d207a2040f08000000366810703a40511030101800107114041014094039055583e0034003201e6280d040858104007a94049440740d8000d00040c000124142c100140c002a2107815010a03952005a42e80720380c4c1000340c1001d6908804c1c0d0a01c2141820701a15001d81000c0c0002e40c50040b156136146201d204401c4450405075465844802244064204d004450307044400c0b5090b000903075246400800d0101c503108041081d0484461900d409800c2c90f1130103a03d20500280c02085640710304807c00000c55850358840c0e001c00c40483d29644031400c841b043c500c2030b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 758339631 1250 758338381 758338409
    0x4061a1e160201020c011d220c030203011e0e0106080403020a06090305030702010c020304060c03050c0c0607150c1b06090303140c0711040e120c03041a0d0b040c0e1002070807 77
    0x8000a82401001c040090402c40c1359880d11301152070303101803221403000556600d4040f03123001000000004104001c040a40d007040300c184038459254001d5030584e40b1240318079030001c582d581c4402640095210b55907690302c1c600010490389008108640e4024000e0040d00c03416001e590740d810840f012603a040380800c401205020855509102e0982e44250301d00045181c43e08041c0d010346145101c550040400c10002500d0310161014059029408000342107a52a45010b192a51104620b2050030501d2843e00200c504078600c40c3e41c00301c0f61081c40c40d103140154525500d071700d00034000d201025400d150301c070840f03990800e011542c2d10384500a9500c41c0c40d103508091a150b2400503d40e82d0403481541055601034420501092044103441071007145075581810510f418298016548802c8255041012840c5140045001817165880180080101401160401003181c5954685800190a460006140342450000c05186503880c1c012207103010740d5401708070300c0c101954102c1a80c0000784 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 758340881 1250 758339631 758339633
    0x1b21020114040507140103020f0a02070320210a0f03030e071202180414010606020d090504090b0a050c120a021b2103131a060f04061a1e16 61
    0xa1080c001c904030000300d184040d061548465648241c0c0f4003401c8030035155510481046c0c0e0080e4101c90358040c1c00624680c6130740d001c441c003a458620902c4141c9441c21440300c1040440852501894010710081c02420001a0180344040300d01c035180141e20036104482c89a00400d0800f96601d84180c840d64002c00d200c08046080742c18801e00703501c040003100d414000c2000699811a040c00c0c0c804445d00ca00f0515500c80c148054994414100d00c044c5e54a00100412841e0b80030a18118004658035012922039640c0103200844942480c0540004490404030b80c546540340c0081d6088408110894180498510410001c1c90140c071601511580020000c1d00424441e1106000c1c2c151030000d407012100800c0c1140380a0350030204080603000002c002031001846180360b0503440c3d00820502c900c50b440070316400e084d01c000e0b510f50b88180103060341d5144a262501803181920f801c0b0030b00300700b000110305004460760410300b0034115a6125452500d4210701c0e01011b00840c1101c0f080207241c4801c6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 758342131 1250 758340881 758340883
    0x301060207300c05130c05091320030103060614011d040b18040c140603040303051b0714100204050f0d0501090b0420090c121b030a1a040e06071b2102 66
    0x1091101041190428200186d400d4002060700d600c0002564101800c00c546214400281880440c0321903210752002202030901c12000914140ca1195100700308968503880045074a807503020859000500070f1000c10700100e0443d0400d00c00442c05080030420a1154000404030440b241c042d051500350142000705005c4d8221b070081c010f100c10444507000c540110003003916848000c0016003407584960201e42185594400300c18880120881d072a00c6032032034070700100d00a25a4141139044d115184110078111082e08c222412110300078001a10402074034284807811038000340c01e0b205550703220400300200d00b078121010320440c818862080043c1203007240e40506800d00e101d5038080d54180c820410100f0b40c24040300e03400035a06590740307501c4e650707507898480c2c10280440a03101c601c800310602142e4005604407010345001c0343d0410b103000c28042c05010440e030f05001c006100c0d6210700c0110b202a4003442c41200010040d034820b20030002d05440b00f500c0b01c001c1e023a1038070014404159149080f54 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 758343381 1250 758342131 758342149
    0x7050f06090d140d1412010303050c120d020a1d1f0306080a0507081221040f05010c020f0d08040209010e0712061418130803070e0d0b06010e060301060207300c05 71
    0xc03500910700c0c06e0041044410001d0303901400004e06100b8002184a00880100901d0440c520048031096460008400d4000a900544d0781d10b00400c015010351807868441a440300e0101101610700c805400840200c45034080182541d00141581d03140007040c800b02c00e0002c2d0700750601038401011410300e850705141c41c0900100000070300c290240212550000b2603002540c0c0307290303400e01c81d075440d403113a08003111f54504000c00100258a0301e001c0d4018582c011600d00064029981a14002548002d0a40380d111080b10003c1d03100246c0780050201d002226200d40e040800c07440c240f1001019201c0540c00c903007a0390400820f850800080c205e0a2400c4c0e07010f071403800e00d051559900ea05004940c01e50340c1c10303900300040c4512004400240c040d84144802140d60f170f00202801c0381d00d500740c1003042016070180d61580c009003c240516800d4144181200e048926550007400003d14216a156030418804081030309080120844c0d80b15010003084101038034002c80400c0003851500f020080131034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 758344631 1250 758343381 758343407
    0x70f030c05091e01090803120406020a210e010510080a0204090c181b09122406030c05040615080112110a08010f06150509061602040606080405010e07050f06090d140d 73
    0x7d8005c01204803401017002e589a0000c1d40241e003d86c030380d80c00c0344055410342800403186003101040000404240e045400120300c405030b14000300000c1c0c985400e01c001c110b4060282c803041e41d20014031100182040c3c0d1002420791700807501e000015454540c08120b2400d003401000543d5180e01209000703d4400348032411312070103070a2480360f40785441c4e40c00c00c0b19413051a000c3c00c0d840008050300240b0701000f00e04622060100c104005082d00c0e40b86c0150490250b000f00c0e40a18909900800d1502803284a802050001d071a4011070f80c0c80c0884502081646050031580c5000c0c0400203031150721b608a146000d490600000b143c210301078840c49040712074560182d01c180c00805424a0390300e42020440d10740010a88070700ea0b0320f485448402d503e4202da02402908503242c03c034005001a407003040301d80a00e200d03400901030449560740443e0341c2c0c215801400e510104883e45482e092819200502e416a8003509002003442503440300d00d40f10b0908080005250010f200c41101a54042850f001c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 758345881 1250 758344631 758344633
    0x100809070909240605030f0a140703030503040f080717030406150b0a050a020a0c08030a0f03020906030609070318060c0207090e030f07050a0c030c030218070f030c05091e010908 78
    0x1002c02d44a8040982d0441c624007034000080c0203040388070155030021405000040c2c00c0741c1098040300185655104e5941d41660310b842c0c0480c1d8040c0384240407414000f01c03601907641030706580725900c0301050340344511000c8030310071b1040094000040ba006a0302400d820f0074090581c0300c3c80e260a101054846aa1540c90401c0d0038500910038034420805a421140d0946031071030300d07059081c4007030345060003041e07010b1301500b8043c1001603c004000002c4c1000d0b4865554411032240580066040e4090101c08650110041c00085c040d424102c0c40281c8c881da0b14600490701d4140c840030f60340080c10400040c2d4405443c3da44105105804024410042400766020044c0c0c611007000b4607107038000e001c0d0100e2980070014850b020312408010001c1151740086200300d2882c2d80b80b40080340c400f1340b0b220481c001d801c0304074600b02c0104800d44c00d500c1080c4580302c2072400c1c2d120300c504070010b00484241d2001d2142c2840071031420340324045540d4013070064460f0441c507004440b0000d004805942c0c42200c0c0d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 758347131 1250 758345881 758345891
    0x9061b030e1b03070512030406200309300a0507081204090e2104050a0f06020c090c1309020331080c0a120302090f120316060b1008090709 61
    0x90711000604107074551101c2c51160200d0254034002070604c01158019544106140407000d07071108088000c00c1140c030251a500300814007106040001616404c174005a900b0602c9100c0f81410304925002403404840403580f4540d5450001e0082115892412503050307100820400c1000010020f44014042130402000810740074096014548910b00a6111468503070340503ca0007002080104909601d4000304d013070301042d02c001100d45800512400c0c2c41040d400c080001c00400d1492400180d0f4161703406803004114900034001c174020090714442200400b00701c81804001001d4541002c0c180c40140580c0c1c0b03040203a803c1c00341500e800e0155032070482c0c03550a000242d0081d000812641e500040c445d403140b1030b5115072410082c600e040684581c0c204869041c40c640d06174010040703100c0844944195035410000c0c0034802d469550300307101640c010040c21030b01c00c0e1300740300780c5c0d0545e40700d540302050603041400400c0c10342842c141682d0200380400b00307104a044060010b06c0140c0480801000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 758348381 1250 758347131 758347151
    0x807051f0b0a27090204020f03070f021b0d0605100306060b09130213030b0c09190e09162106020d05011805060a0b0703020a12080a1512021207080109061b03 69
    0x1019404500120380f203641c0d59038200c045484503010707258680c6526481d581c0343e1400200107812500c540120600501904510440051074032003003981500014080368142d0626540c0c0e00d00524014081c080b11600f007480000000e0120301404010740107169400c2c0e12283d090084c450001c2000f1513111840740180580b01c80bc03840c0d130a200301104c2c0c10401c0c040060300d805600003858803c003507a1130340180c001c1c0c0c844180c0b121b0b0351000c041265178407040e0024650b6a000c02ca9110303010240e510210700701c00d00080201410601030540060046c4c0408044140c02e07565000499000e00c4800030001d407900010030140f1041a0340581e903080c03520007406146000c0c00080e0000440e4004c03200c164001140c9403003032520030800030321000d030302078074040744800b07a1000600050011910744d40500e080441e42500642c0c0c2c02450000c5a0b01c031505504860480c0c0e017000784281010100c3e07070181c8904500090021800d01a0b41020390082a001a100804210094549900035110310526044c003110ba1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 758349631 1250 758348381 758348429
    0xf05010513020f120c18030309090a1e1a01020c010f0806090403140304051f09030c080c16060c030909060e04030e0303091003020306090a050105030a0807051f0b0a 72
    0x2044031901448010307590030104803049840c1c01050040c2104c1c508400802800c50b010348002c0c0300340b2030f8091002009080050802d560380c810301c000d564008502c00046480c401c3d490b0010070319032031030040b0010701440203000a001c8500070380c04c00c1c03540c0e4444420b5100d03c3d41c0500840710300701402e19006101403203244010344a000c01401c2c3d10b004205050029041c94483e502901c800300d0503585007540c03420541046d035562a521034a4074607000380b40320351010f810114411005103a5140d180c030a011000d580301e02e00b10f604985000b6a00b40100788054183c0d64081002c00090b20880c0c580c0301e4205101d08004000501540019541134501241485003c10070040654020b92502d01060507028680200c0d041d80202d52545401142c5100c2d00028a5015005540328035800e0382c189440c0c1d510380040000b5a40b080c400e50750150030404a800225034940c0091a1903130141c030840e69900c0c125000c00c9030075900d420100125513a42d0034103a042c3c0c0383c0b201280c00140712080e80032650501040b944c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 758350881 1250 758349631 758349649
    0x230609010602120903071d0a0b0108060312030c0d29031626240a05042a050d03211118360702010203070f12090c17010f050105 56
    0x903c25802d00821420407a0b03404009240191118070b4045d1010000c00c40ca10300c00360801d4030f90001c45801c00c410140c095200d84156807044100800904110002d44000c0e00582c1c0090038070f43c0601010001620b40301010b02030408c000310144e45503002c5010708903080700490742610744184a6000000c0045041c004143ca000c19190a103800f00c10120014035050401e89088040100c00d00071000c040b5010a0b4100d4020390720300c41143c0003049940c58000c00b10440e5012103004005075020b80c4070001c11520348a00c1c0a86d208100003422071251101d0000300b07000d1900e130f070440c0000c9005041c0020101e030b02d001c6e103100302c16141044c4801000d5098a608900901040c0440302c6242174a907030980d40e40e00c5002803e810b100640702800c450b003900c5c20580400e00d4202d000302e484454082401c1610500c2141d11400d01950b40368040303002c20710200c481c45040c04c80f030000140c69140310380102d8120301443c0024000d04500140e5490511009401d4500d54405100318900d840b00401982c0c60301d1550f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 758352131 1250 758350881 758350903
    0x70801060c0b060f01020a060e0f0c03071211011709100b03030c0d0e04090602134b17010903020715020705060a0201111801021b280504230609010602 66
    0xc4c0700d0b1896081c1d80100c1c0b91180854028040320304040d81c03aa0f0740480854001d803990351290a541a18040009240e624a0a4820303810790913000384501e40032448129039205440d805143c159000301070001c0d201d517142c400382e5400010360000c6542c070480c400503106006c0d4142080d800ba50030064007450780c81c0c40304050407140090283c05046441d05a0791940101504c50380f2504c115260541364000c5441a1443d02540002000d4198016403409008651454030f0361004090f104900c2014215500c1d1500610025400d11031000c01154031624250000c402c07000420000405883c9030500a2804505910034114000305e03c1e0202d04d20382c0e000c601c031001d88074187e0380303d50740b2011074078100e005240c91120304080401c0810f1018446205da0301030b844105099086a04e04605000703550701d20308090a2903640500d0866080e184c580a0481c8800b4842c05104144c2e0301300c0d41c0328042410355030849c0030f4400345c0c0b17000c2055000d0210b241c0f1149401420580e44841d003581001000b0b9a00c0f4800d006e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 758353381 1250 758352131 758352139
    0x240c0e0603071d0d20030102070c180605151305100e0913050703050307030906030c050a0f022a09160f18080304151209051c0504050414070801060c0b06 67
    0x2031160072655864440b28280803000d00b004810050a003443c05d031034034130108090b860720b0301040c00580c1442c0c1402901c0540c0e07040b40c241300040c1d103420b4002d1745c110340812019503e2a200c2c580003c1c01d5407039403458015407190001d001d6035600b00c0780011041e4800c40e00414811742a82e202c4a501c00d90140c500d441408041d5520032171520f801141140034a000d0000412505c182500482000004000380c08154442e03104d4444d030a0311500c0075001e0f01e07070b03481030140001c0302400307204d2200b84103080b100c202c0c3c80c880c0141c0d1001d0160200014008a03203a4034201c0012154004900f1802c007115015030190318520b5144054242501c001d0005003041e22007410003200340c942c00c80401e448203140004040c01000c8a82c2c90f9a900701c44d8280701940d20380400840e000c54142d03034205580e0701405101c80c0d80305028100344000340020000c0318032000015030030003400303003c0451903881d04d106442c0303021404003104005180c940f5000f0001c0d0f4050b0414400c100591408100150040032030b00d0700944125 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 758354631 1250 758353381 758353397
    0x5091b060f04090c0f020609030a0206151314060f030105130807051501090921080604020a0201060f0b0c0c0d0f0602072a0503011524020a240c0e060307 67
    0x1500101c1240502d4210018103450401048a400c1c1c00803883c945030a9103800307640440e55000340d01c54403802100e045c2d40c0560000c00005244218500d0a00403d800c01007541c00001140849a0f0403240003d407401044090181070103c11319020000c0c1d101c02c0300441c000d01c92031614818040781c144140500404448003ca20f500402c002803042400c21603440c4480c118641e03440e9280e0b40606401582590a20601e103414843c0124400d841c102003030098480d042c0d25203410003840001d51103410681c0442d5a1004046600030414a6100003070902d20105074990201402d40350401010703040342480b941d03040d107040000840d44200414842d40240c80161030f076005051013012204090890240c0150b50081a00d500c1c400162075425103000760000c0002400c10160607914001c5130140c0b8524400da90425042480e11440b0101103844901c1a1a02410f05685041c0b02840401c0c02000348501c0610351000c002c0d0500c1b4402000101d4648101c00c008528041807180c80083c02c0542000041c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 758355881 1250 758354631 758354647
    0x118090c21020603040507050a0e0411100302250510020901090b09150403031805061c0b032104090c0318021201060b031006030b09091e1515030105091b06 68
    0x111200d8580140101360749181501e40b49032101a03e02400e44941600c802c04900c42c6454100940300b954022400000c1041c96800c210038840c0da035404100305030b0200680e403001c84c41c030500100042861042030030000300307616110b4102954003100b44040c03403051000c1103440c3e900c203d2000403a03030100301003580c800507140400d00f0030415104450725041c0000c0c0002c1055401460203d0313005e03113034a411a9040e2107200b004441e11441ca1a100c1002c0481151010843c032030740400300540c402000ca40701d0b9818104150380c11a070301c82070a00c42f400b012600700f050441901420b14080c2062404021060901c00100c616050482000c2c2c040c802f1341c2924500a0025032022014101c104ca0a076100c1c034140103003800849171405100006410005200721600342000858050754442e400b4001c440d0000035040701c810754968401606100e0000380a401e4400d4025060040482c005280402801e8509040c01d4810280c50140c040c6d004511051001001c913003c450310380d404a03601545e580381 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 758357131 1250 758355881 758355929
    0xe0403050c06010b030910060e180705031e06070c0f0f14060a02041802040e0606030c04120c05120c0d1202030403020a09050103030801050a0b070609031e080118090c 73
    0xc1d11260318462094100100d10040410b000d144607101040c02c54900803117000d520f070152006442a80744d51040c0070081005224400075482c03801000718103c039000740e0b68000080c03900c201e00c10345010700d0740001811305080c0300500030564000b410b810810716000069075004100c2850001c050014800d194801040190f149441929a40c452007190014280342501000079400340c880c2c1c10000304500d01d18054990140280c0d42141e0f03082d42823520300d41c0c42c4420720036640c1c0014000c2415210402c004166500c0710420910100c1c007031500c80c5c1e021418007003882807465558183d100643c0c0410005400790b52541d10f11403090390301801100040f945541d0903440e5019039000250303c059188070220340510150311090403179002c0d07580c50256986c0c83e014001c00000a00039010300359010030643d070110302c60341c014800c603e02c640350600c2107406072502ca0f01c2e4082115001000a681140100031070048180600030101882e4410407981c43c2580d1101485080c0d031180100260b08203141000b0060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 758358381 1250 758357131 758357137
    0x131e0305191103010c080703061a030c0f09030a0602030603011d030d0e1f0f1a0604060e0d1403070302060a0b030c22020f030702101407030216061802091608010e040305 74
    0x2c054001e0000d8500007001406842045400800081c90b2000014846207403110300c282001c805420b0302e1642c3c84d07888058403160310890385100101020091f80d8860b031000c10140c02614003034030300181c032802d00004260035202c00c41103850700d1001d0030301c1003a0400004411180162480700c00054450a0400818207020840300c07203a00c81d0006e0382d040c02451485400c40408078485890400c04501070321403000b514442d580d030b0290086001e2100b44011802680c60b1108050002e0548042c20000d58805d41c444010700b021503240d8001152040c1003517010000701e88c206200702c0c1d003400300c1000c250200c2d40c1c458080881c1c0b40320704821010120078002820280711a0010282d056540c1c40c1803800848895000343c400500604c92001c0503200d0042c070344924154940d407003080f20140c1d1070f140ba044020790006004085c640241e2a1040700103a264419003502d50007005c80c0c4100d1000754010013102d0305005144000340f86c8a0b000002c01a548000e445041d5404003800d03040503111030800316a240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 758359631 1250 758358381 758358413
    0x110d020d0b03060717100e01060809030d090822181a1003020712020c060409021b0d030b010f14160510090b0f2a0a0e0402131e030519 59
    0x4003c00050010060780003013142446682000c8407100c07500c2d410b450b028140080d00ca55030342c0302c4003040180600742c80750340d0031500306481c14116410718030300813a0030085031a113020481e0b00c0c00c2c0c002891418207101544506e2021403100c3d1203102c0d039240554050042030f6008584800307540c0e80c446408140380005400c0504040a440c10041185400e009002544220030039a2900071101c2540480d82c40022081da1114018110390700f003d20b081c95800294100c00c0200c034903000114a60f00e80700004101d0b9868ac1c0803680c0c0e020600c0e101c1c80c9c00151034030340d400c0700030020030203201d01c1d0070840309034442100c0a810844401c2801d46002e070820900b00719009528804d0345007001000004c1c4080780d41c059000e00c4040c071240c0f0458849810000c400d40b041d40e81c6c820482045081c04403200030441c00340402060900b400d07609541000b00190480c0d009010205102c82000030612410811710020740541407100d030300d0b01e1755a056440741903a54800400c0040700b0801c900034041049800b4000c91424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 758360881 1250 758359631 758359633
    0xe01080a180501061d01170d0807110604051608010c020c193602071a0c040b122502060c2107021e07150507020303071e1104110d020d0b03 61
    0xb580300c2020451417403074001d542c0c03c06112000085910145801c02075100414240141000120005d05440c9040010802c43c1804015405014004c0c000d02613140700700c0c8100054507500c404000ea584d6407003000e41186078607030324082d400b0710003940000342001c40c0c98040303414586a03410b80e1890f01c20800d03141c00590705500171200154105002c2620f034800084002e00814111104d04240f6049000f1400085c000740c0c442c0072201036030f44100364101d8121a1000c0342c18a40381d21605c5031103581d4007889201040040400804c4030044048000000c00414904001c0700004885030096880360043c0002500350000589101005156502d400351416201d401d50450300d0328a034003030740750301c1c5d41200984c01c07240135550f90800004c0880c860056845012a04010002280040301c05401c405400c0760548010001c0901140038000f0710011980000d140b10f052203e64034082c0d00319103030700010718000c0342020010341c180401c50b0306a0700048201c900040e1036402d00e000040c042d0405802041e09 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 758362131 1250 758360881 758360891
    0x70801060f0c050712050a06050609070905130b0616050c031204061209051005060306070c0b01210f0c0303120207030807050913060806100b0711010f0c050d021c0e01080a180501 78
    0x20806c0200c0c0a400c5c060181c1400c00c0030b40d880d141400700b50041151460002076500300140280d107402001d00740c0145c0301100010f00180c04001207000c40d840380034034401d50391143c615901089010007040219000580c0a800b1030b00f0ba43c610014580241e0007003000f4488203c40314110384035030341d0001c802e44d41c0107001c031008110074403c01401000140c40c0d0074001d00030395001512090040d180c0e504255808150080c9aa1900742d02d2441c0b480000640c541c007000d10321000700032a50f400440c0107050b002e240d88036000e914516001e441400520041c0003964014807d00e00465000030741642c4c000214201181d44001d000009110000b0301c841490700c840c6020004104240c0000b4030511030401c03104194125034503004114101d0081410040101a2503443d042c229441600b440030140985e003403400031030f009691600c1c144900103040394010781c0600508000c01c030811051000706040360801c4069495048002020000010100f6101d40c1d05c03030b54540031005e0b49050411285030808000c200f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 758363381 1250 758362131 758362133
    0x6041511150f10060c02031209030705090a05010807080d050405010f090801020a210e1b0402070b01080d020606100804140717101b02100b04020702040203010605070506070801060f0c050712 83
    0x2441503003650a141411407800f07021031414083c0e0381e18508181c004008142d1300304107480030501a40710220007030f00350092110004031902c0d61040c090040c01c1640c00030403d5070600d981c072450314140e6031041c0429400844c003844800c7d000401c95003505d1003031034884c10042d0b540740c09a68240c03040d4080703107943d803001a0465040354046200c2164841d8101250400881c0b102458180c0311030a42e1402e117900501c56400316449041a43c402c0c480010b8000350600b81c0703585661034001001d901500d01038003d90180b0452950500855510000c21294400c040105400c01800c031000100010418021240308041c3c104040003020001c03c0645020902a070b00c076203066881d030903200d0840b0000303400c045402d40c6240b500401d058141800b58020300b078042000c0002c40c0600710448071150060340c20800036000d0b0b101e500045010b000c0580390b007646e420350303403030b050746401c100a040008000d40e40005020300b6070702c100c0d040c05044003490000316001542c1801c1e401c0500c03a44c48003881030041d02c1890 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 758364631 1250 758363381 758363401
    0xb0a03020916140c0c1809100203130503040602150c04030c03060203040201030f050a0b01090f060f08040f06090b1f08030906090423040c0611030910021005180c0604151115 76
    0x7507011442651b549444401320901200b1010094034210314075080b1510a003c8003680f03501070b40d440705103400141c2020350b1903190a41542d1160304184016040398210344404502506842e800c0f1303802188051502d4910348800b5407841050100401d0242c000021400b9607100b6000502d8203560030404200030300308151100f0040600e0381c081408501030247c00220345150b40c90090803102031f42c0301e005c690450481e0485ea070030310040040b1820304031100c200c40814014420207502070312405054409061049980d4208600c0e01020a01728a4107070b0103228088004c801e840000038103481054990765a640010058501040080445040c1d5617916802403820b1083c0c501a070300030040c0121030360300c400d8111501c1407c41c8038030005500800a00d441c07400d0250152035460101d10589800e130303804065110980320180c0709840c4400d181b40810301a40e50600000d00350700070441e8403620f4546400301e507031020b00f0381c0c0548805021382e840d6442c030b0400c42403045100b4003445c076801794110302d0142801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 758365881 1250 758364631 758364643
    0x230a091740140a05030c100315090e03090a120f081602180f0c1207140d0c0c02011107031106030c1204031106060d08090904061b050d0b0a03020916140c 67
    0x41440f4074601000021641004100001504030150205480c048101402d030041e203202101940c01880030000010300900c94400c0c1850b24046802450b40c3c3d171004020019070541c180c0040c80e4541c80310418100089400a80c1c1100c181c0c4601c80f141c9030130103a03801c104a1180000040e405c41d420000707040800001940c1a03220301803a010140e02c3e0b40754143c07114060300071190104d003440c0e0f142c1d0109280344d0141d00c1c07a0402c008543c060751328140141801e8001e0310280c14001c03010440d5116035004541e0044050880c400e000740c02400103501e10744642500e800760080c8203020362000004601340340e11601c02c03200d08580e03c48000406082919004000c21506006200540524004945140740040da0020318581020815040a02c0d0702d0401c1080c10014008960059907081c00000c000f03008a400d2110000e651122511910045001c00c2035034210303601d152150034181401e000581e1542400ea410040c2c05110300b903411031148040d1a2000e12201e40d401e980c80c082030310802a400080c003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 758367131 1250 758365881 758365919
    0x80702030409111e0c0d120902060d0b010f030c020c04090204021306020a030306120206040302040e010e0d0f02151017070e0109022106090a230a091740 67
    0x101090341c0c500c0c1300158a14013610448021300c0d0401421400394620564011400280300d00f00011807031259030004a0325401041e80b00e045a03100c141b0303011a03680000005c400f440d014201401031040154009440c2c0013070f00b107070358030880d6070f22000c00654585a041d81c41e03c0c040c140ba00396001ea1600301c0a036443c050b884d4101d000a0601030b01254482c14900e02210b803950140c505401d06065a003000058080d04440c503103070703650b2908a200701400c100100381c00c4050341d0300e66800c004c2d1130131402410441c00489000d030030020501809030f100014020503044070310f0702046046201041c410b0f80c2c1051083c0e4404a19111356030000b04940240c0e50003000c0b24402d0707020703980d10b0720700804420070303500001c58a0710707400f4406800140005440c0d0300b04402c00e1242c5420f000001c00c0342182c12203110300680345034200c00d070b41e44a280e08010410038001d215002d500c1c803150030300100800c041c04817511031400d0101d0312248500b07240b12042c2840e005020b000348402e0140c9058035864190580c10b0280c0d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 758368381 1250 758367131 758367157
    0x3090303061c0f0b0619090203061023090303040b0a0305010513050405060f0603070504050406050a0608060c190924031b080a1a03030703050301060e0a0e0708070203040911 76
    0x2d82c04880701c0e21000b59814003544180d00c25203042d0582c0701c0076400503000b482c80c0d030400c0000150050b4584002c803d28046c2c66180b10040e03d9062050070710490118081940050104070312200c0400c80090384c2d512280c50f0f82c1d0000540e16102480445e0860041350f00c800890603001c96040305254150300242e044e2801560303242040b000070003c143c16283c0542d0040c059400032800f003000d0804204500713078004405021500c0d082c0d5200085422180c00300d03419201c480d902c41c148904825680038031001080050003c002c030342003103920403072284114035686858481104c90761808a0142007410024280d15161800030008011150408541c2076241c1d0700003480c1400d2410f8121545d8180e05015440f56203506080d03a03402c8030400244141c7c0f07194911480405050314013698100010700b0502c0c401c1d50b823140c8a500d481c1014001074004900301d0310a806070b032020300c2215843c8090540c0030b0000d161103101e07522804000d0b420351040b034100c0c00707115085c43d8103107405003c520014104c007030300381c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 758369631 1250 758368381 758368399
    0xc0a051213170703050a0807090f03080d0506060a090612181b06020d090302061605010213170106050609190308040b1201090218090702190b010e070c12110a02060309030306 76
    0x40b004074840d90300020b0115a05000380703640a4403851540381d00c608281851200d0390345503004207500d1029540100c03000c1c800094402c0d9441142e01410341c0064003603401c181840b80680d000b8000702c025008000130040c0d00e103403110302d141542d0010400c0c0b0014030b020340440f0205003050405001c21b10200005660481e200081c0d03c0d20004000d40e03400c403e40e4548829a040d9401c0050b903501c064000b0701c092000100d52400f0400c00e100800f800000c0301404511249890310400c2c6034443e2400320200c0b6454100204096150302003100c807840400c03079809043d842045a8402400313440c1e0009000f02d40e01007070104080c400c03080144640301c07420452095582c1e0b01c030307a010142d02c1002c0002170300c9200c24411144604104500300d4001c640c07030045e02c200348611422481c00061a503c103035568070310310340104403003148421115000f04407440c14000c441e170141c40f2806540300f9040c1c05010000000c519803021401030005094155004245660743e05144110356031308d810a64a41f8410b00f9a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 758370881 1250 758369631 758369663
    0xc18100521040302211b0d09080c030a0f05012310050405090a0201140c010203100303030b040b01080f2701050103030806030a0f171603120b040209090c0a051213 71
    0x4918540300b00d40c5580284a00030300c408902607200a090001e01c0a0702e8284600d0045c1c940010700d6003540d8084000410410074034100040154855602c0b400480d002170700c0d40c00003500e0210304503d28907001342d018060381e2654504640103011100150f000144031442285103501800395090107080d640d202c2c00c000c50344038420801200d905072410103490740800981801540510144401001e1007080b41e82840f2440002c2800c0ea80200c44030b4021120b140c106000b0190948280040004190380c1046034980503c0040c150a0001d40005010004440051a2036031a5400c00111410642d400c3c110030060201c400d010700f0b400c2c0401c8011400800c0000c256040001f030070300040750020030f5a0846001500d039000f110300340d10300c84464821304000700c0c800c00c0d0410591400c424883d584032504031600d00c801408480c05408407a11a60041205003034942d03980c8405074012440050f615583c000115095419215030004491b8064803001040801545c88508140c2103004500e00380c0c8407251 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 758372131 1250 758370881 758370937
    0xd0e04050a1a13090c06020d02070f0b0a11010608030a080f01080c1f0903080a0c050d080c040902030c0921010e0c061b0c13020a091403060c181005 65
    0x201e10394000d08000c100702e10030824909408504009190a00009401c1c07800b174403598011801c40e044003016902c80c1c0c400481440d030400c0b61500428405150800260501d5aa90400e01c90b04200804000001d180441a40c00a6200328010301034001240d50320301b030418018084031001c4030114103240b1980d00000341c441000c47e281022450040070441442c0c1141c0c04003100f000d8090704401044072030540800003030340d40401400d50160549404004c4d0407149070252600c280c0c02950820002c103035062080305805d210558003a203414540268803661500f0403c507442c020740c0f07021a40008109005a520000a40e0001c1d4403207052001b4480341ea11002c20942d1900902245a0001e408029070f400f181c00c0c88100c2c01e0443c0100083c0c0300002c51240014451050030001c00140d56030018130320015503003020340000240601a40d03040050340d5000000e0300d0301c80082030070940c07600c00a54001012904052040c0554000301a52410703204000300506c0c030341140b0302d03060045400302042e00b20011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 758373381 1250 758372131 758372141
    0x50c0f07080a02040b040b0a0b0c0f0a150506030c0901060f050c010c0314010b1e0309010e0616021b10030b012102090f0d0c06030c020a0f0f050706080108060109050c04080d0e04050a 80
    0x10000d842c108023245040e90451241d40711407030b0405117000d40404d400702102e0605c106035583e400b501d07d924400f040803841c4800c9400140080d4400c0e44152501419a280c200345181110510300306100e060400303000c15101440303502c2c04260b05518040c80301540075015030011a40080e41307850009513a0325040b40b81c00034440d195071009000c04000054000d00c500c14020b5903c00c1000001091000c03240915500d0088103468004040708541032007003007241d0410814620000c40740658244602e003034040b495150031200c1c90401c042d1502c007400301a034000c8040500e807840400c00c0c9001010050600d800a4000c1c01140c3c0c450443da020100d22490651080c81400b80c20040240c940c80c640300d8181c0050651003043c070194064009003201003803594850408040c0034400299000d2810b28103141824502c2d003040c810b01c00c2d90f030010300110380002895415501401e200240980b038040b82008140030340d40c011078040c400e6408040c07403035900c603400320681d020944c0d05000a480707141450b015a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 758374631 1250 758373381 758373401
    0x1401240807091401110a03030f0c02010c17130c03031e0305010302131a0a0e15041119021002031e15010c0f08090607080c0f0105040c06050c0f07080a02040b04 70
    0x201050300512141601290700c3c40e074140141440c07035a0486a0307100c00e042410061041c0c0110b642c032110304000c0c032840c1c0140d0000c1e20107840200003910302c0d82c81c051b00300103180b4607082e408080500014260f48203d401842c1d40f5410036407401c2c1403940c03440c000700343c281a406401164980c074134040c0b1300d20380240541c6060703a0f070041ca15604428042c40e101d000304114174a50340b081c04000003442c01030306c4200180000d0090003200304940e02d0f1a158584076078070710031910780c0a02e1500a14078002c0c40808140c1e4144000c039a84442040b0035540304903c0e2517850b040c140007007840041070100080144140d8016000c502000355038560710002d40c4100c005014480a012800003003144002512055058049a01c20b404071410030310711101040c0643c200d0607044480d000002444e419040e03041201d00703240c4103c04000d00051401d0394034400d01d036050388140e1081c4040401c0711011180244018480e03144042c0440310000d90302c60b9900d0fa1400140810f90050f8a4000d03581d00c01c1c10b0601450000c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 758375881 1250 758374631 758374637
    0x40e030d0b011b02010c050c210111090d0b100b0d0e010b15030c0d0e0102040e1e010b04140f04090b010f0501081e060d0b0a0c080c0a140d1401240807 66
    0x20f14041d80054940030b0400004850a009080a10340340744c1e22480000c0c0401c90315020074101c2c01680c11002d084984a0b004901900024417803800310395036081e401100940c1c010305c501c8041d00d600044c0c0e00319007800d820a82c1c1d5482e01041a407115040c9510079100d00144030000d100324603c003800d0101c18454080c042100c0c2008100140c2c41120707050007080b0f02071620780000b0b40760f18160215403ca80064010700c005081890070300c00151045c004821600d02941450101c80d454402d021002d845148500e4040018640c1c0041c841e40c0c614080384811707080940240702d614a203140c4000011b40034018104040f50801c408501c40d44503c51017440780091346803044003204169071403c034105009200ca03030320600e20420389001540d2509011700940707140340302041e04603450b00301610f004001010004108000e21250500640c070401c21210100308010840d0780c2d4940e10300c044040c01802c1c81148200300b0b4172000145802c0b403103881c914a1110000c00805041d82c8020445d840304040d1511000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 758377131 1250 758375881 758375927
    0x18042105070b0703020c070e0405011406090c0a0e0d02060c01090312020903210f07030503071b030c061a1008242b0b0a05090f01180f05010209040e030d0b01 69
    0x1d814043e030300400c4011624800c40380342c1da48d02d095096854000300c0c0c0c100c2e42030b512034001c2c201c0307600364025a542203241102c45084500d05000302c10618000c000504c810004907000900300ca4560044103a00a81c024050b07556a906c11520140608000c0c4012400510488080c032038012484c0300351031422800034040d0000c0302107030604c6945091044441000d080c410020301e184500000024148188039803552a103d140c6600d002d0144020316548c1074010305024200c0d400243c0c02074883c001d49510140014219036661030b1501015981c0035a1508134482c20140110203412110780c1d4031034203e409618040156842c40c00c024030070030ba40c4564110504c0e012100041410307a0b20403010001d000d0000d14600b400d501e5076106400290f408081c265611000d01500c00003e2280c4029440f00c0700090140f004030f08401102c2005000c006403519805c030360428100a800c1d01110710b80a4024001d11410001c0d0010729126444418a2001d1519005000f00c3c594014409004400c6801c105004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 758378381 1250 758377131 758377141
    0x150618030f020411030f0a0c0512041209090e0106031b05150d0e030a0f020c010c0503030a02090a031505010e09061b09191e08070b031518042105070b 66
    0x303076580d4200340c1240c0c020745500c01e621088a002014512940d8009541e281504008801d00300700c071180400d0008000082188010b400c000c5069150400d45c05100c030211103524010071202403078150000e101060502803080e44110054000c48290ba0141c09500440e00c40600320f928401d40510415400100d109000c0720920f803220042c16030b0f807035581c00202d10110309000b02411030f440300445e00c001c582d040c01040c140307070350402c252a800c85003824102d01085e62601c07030b0340d03590100402d03a1049640000c0d02a000f81c5841e140c01e00156800004054425840c80c800c9014020034020b80d400180d900001a0f000b032000a1320f18011070409026a400781d402c150501c204e42d00402c541900704101c1043d4140c3c0e050030120807801000c00290500b001d2003401031281808205502518541e445400203020720342000d01207941180003004101d40018108000c6440d0060602c42288180300805c204000d01075071780c4041040c0300e1810380c0344944200c103000580c0c05024116003d001d003121940010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 758379631 1250 758378381 758378393
    0x906210206090d0f121403070e040e031201031401270303050a1e0c030e0c0906090603150a0630020d05030f04120b0f060105030c03070e120115061803 66
    0x6084501030040300450285480d800d1310701100c840100d400100005e407402c080c560084025100c048508120f6280d41002580200565094041c00d40f00d681c2e01c03c8411045a410002c4543c0080d004500c0784040d81e4074180218103820030714403842c07075500b0094004000780380c2c0842c1d50118017840141e568640f070f041d1412001484000c00c0d8102e0b482c2d88200301e0a107185020461078240c80d0f48480490405030001c4001e00340c52900416038000c0d80504c0080010340c0c3c441070402e0f40540c0684040740180e40d00d80010f881d0480b62084e29803004070450920907620700c0341c0c200c41c7c03d03118103040414445c0c2401318032002180e10f40f943c0407076443c84080c40070010720b0314064004050b030003503080300e040803085604000d440c0d2080d40620086a4095080410004103c0005a10840d4034600b48480e00d00a400a8028407006207420001a40000040d24035030184a000d150880083e1403a44011041c41c4400c3c003d08041d15000d142c0031920b040040e80c1441800c41449500c1d07003a0601c1a941d1540d07a4071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 758380881 1250 758379631 758379637
    0x20303010b0318011e0905010b06030c12090a022d0907050313031716030e031201051504030b130501140601020309060f04120804030c080a050c060c010b09010803040906210206 77
    0x14103d5480303145c03c0e00107118040728210b01d1400d0440010ba450190318000d421906186285400781e1030074010803154403050301c10b59200e0030444000039040c1d6070350210681003503841203000790f0088070303008100076041c00041c0501c10408101500b6014011400410102c5641100d684c40002e80800004101c0f0620070003580355103201781042e03218401c88000321544420111551040024940c014081c4982c0c5401f640250445803c007540c43d00c0d00801d1030941c680014010203002c0c42c41d80c942009100c80c010f040b50700458000901c036145040100407031680c15542c01040c0c82541c01c1130a030004901c40e1441903402564160010f610740807000f01030003040e030020401051040030a100008000018000403c01c052082600540e00c0c0d09501d090b0980642a0b0040c0d4042d07030000700100002403001900170f100a00890b01280c030362000f552124051b264590720a50015000000000ca4100c00009030054410300201445003070389940036603282041c0c840c10000503031300440070a0050b042003001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 758382131 1250 758380881 758380921
    0x3090f03210c181205070302221b0806010809061f08030318011125060f090b090f0d05220503120703081b1b1c03060f06020303010b03 59
    0x1c00c8404502294419088800e400000004202c800600306038410800c001c48020b445000c220311303081c100c01d849140da0703050036010003400341c0a0b0080c903240b0903e843c1a0301c0c58007904a13409005890200b000004030400c000c0f2079002083d45980030440d5580070b92042442003c0980040c249651032640d03401c410305813004100a0b8005441010880c081c003400114403800c40480100355001100d05020300711960340c07400c1c2400c0d60080c0001c2c5900400003441d6035103c3c2c82420015102c02203402c0c505c00520036640d07564011031400321044104000018994420101842070340d01c18541841380300c2e00d80405412410008000704860703c1041060251209600d01c0d144e07211600341d480781c0200380340c21400c021100209802080d07441c1015802003105030b1004800c05151a5050b0000e080c030380718050f081140c140c01032001d49208040400b0410941c199020500320a01714140d1a00030707005124038014100d04134000640414002d000000302c5e4105d841c0c18400510b960f440002e41c918150031851 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 758383381 1250 758382131 758382167
    0x4080a02010c032021030103031409030313030302010504030e0301051005210d0503011e06080103030e0d06060605040e09070b0f13180204061704051e030f03040f05070603090f03 78
    0x1038000700e0142000780300c0003402d40c8004003188014401c05e84e00060b84d084200e42c0980c0104010300c00260f000d10004404041401940d03101c038051000207045020724030b030070341ca080d500607000002e0680c1500000d00450098a8621a18101c9810305090b40d100f182d03000e41c469042c0208214a0410241c004052001940070844444c6100401424142d240409100040c1c0100c014443c08484441c1040038403450011100c3c4145007a0b0041e0003030700e051001070184041c0c10704003142d540f51520403601c1c0940c04078040001d907894042c041c0850b00140507654000c000c42001406051001a851040e24040c104a604110380740490303402d65407144000c03566014040100240768040c0d840700c0703855000d1802000d88c550741030200080901502d10b0b0310413580c06050b02407001140001c03c0718564200309001c0320030681c00c00c6c02c0d264510b00c43c0405801c3c40d000004108402d0011941c1403000c00c44c420f00980c1d07010399031004e044040c0c1c0c00422000d40420442030128001074014907840f140054407007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 758384631 1250 758383381 758383397
    0x30105150c060c1902011503020d031709030d0c0503010b070f050a05121908060904060e0705060d0c0e09040c0509360613030c111f11011104080a02010c03 68
    0x40c05081c10860b041e514605900008940303a0401d506810440c10a0303900751001f0040000030f800d180024540390b10003e4010003d454072801894404e0807520f0510718000450b8105080c6007a8030f9549901010281503034601c4c0c4810503030082d108508480c1210310001c44681480c0301c2c0d40390441c60426003182120a071082515000000ea818814902114000c1240c039844081c48030f40c042d00121005003840821a5503c100401c0c0d03903450501c0c40c0c02c5038001d80001842800c014050b89041c0141d04070a603c104041840c09400e0016000382420f58110365886c59105800011700055104c10f031002003c4100c2200c041c040c0e130924042c5a80e2048880d28104c600b00100d5102a407606c8a481d80c0e686402130030b42e03102c00c0b44201041541d400042d686040070480c42c45480040101e20711000091942c2c040c0d10b066640741c1d0360007501d00d20301d410508805600c0407140d200038145445050602505509181322020310400300b000391400c03522000060b01d880c840359401120340c0c9407540c0d411014450b1030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 758385881 1250 758384631 758384647
    0x2070f080a11060c060708060f0d08131a180112060e040606050f131d070b0d06050f150d09080309240c2208030d1d0106030803010515 59
    0x544011801040040098110240103042200150482c1d4900e2800341100300708014407001c0004440707520261901d81820039442c2c180c00101c0241454001a034070002c0b40200e1418440104000d24651031402c07007034420280d03184004003040745101c0c0b82e85844c4d04140944e070845004585a60040c1d00c0c1454000b00b01000a04010222512a00004040c030954003c1104001291054001900040b1782400300e18804100180d01c20031998400054035880340c100091885101c50302540801c41d003000d03120035944034003003803003150000c50602c9085d40c00c0c0300001600d4281000c1780040342c5009030003920400b4070203a200b80c0550045040c1d1f4100c07543c0d01c000c1702c0414070707a60185000e81e001001070090000444010012440d1a0b24000c0c1c50f41c0d103c006006001a0000440e02d10781182803c0c200c0740d414011a10003407000c9c9500c1900726010006840088003a558080000c0c50502100701442c10510b010140c00c9035501c1c000280510305c10001405503180c11008080c825400002c124030304100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 758387131 1250 758385881 758385899
    0xa05150a150603061401022a0f040c17130213020a1b051b010206010b0711030a0f0501140c0a0f0e0625060c1e1b0b2809080414010207 59
    0x41d07030744044006581d0300740502411901240782c001d950000d00c01070402c3c1c200c100c4640d5800c7e45659000b41b55050243c99035a4a0f195210800342c0d481d0014001c01120703000400180c0400c0e8518080003580941c41d000504240341c4000d10402641c02a009290024620144600941c0114500c00c00c2c81800e03203204000881d440e81c0b103440c3c180300300050041c1c041907036504220110b00400c01ca040d90030101c018040c44040509032000b450b0840402c01030401140f000c40e0419901d5a070142c90450801d95840900174150001c1c4000201003005c10f56640d142e9030802c075140034000e2000d00003280b50740d041800038420b02500c0703609080207064601c6d00700000381c0120484146518000e00070b0f8850036580500c0080d1260341c41c207000c1820010b0344421020030b101d804824903080344041c0488a0b03c012403004100d4403802e2215448400700000342020300c113003c000d40ca1000c11700100c90400780c0500b04d451701402040081503000d600c13241482c2c10007030785889280c1400340260452003000400201240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 758388381 1250 758387131 758387171
    0xe1203040b070e120a06060603060e37090b1302060a0f0311070507080c030601080a080309010204090e0c15272e0e01031e0207020a0e0709060e030a05150a 68
    0x19400074025201d440c03a0034800d0307aaa80d23020005040c0350800401c01881c011f1515503000e000013001e802401c50407015803100b03004005001000011b4441d40e06c0301c13610181d1001102d0303405188682010768589149011204200341c001750040400c3c008400074a0088000c000800c2d00b42c03e01003a030503009101036811750403869081c2c80603032044c401000902c0e01440799032180e00043d0060801503041c280c00c60b550b01441da100402510b00080000c92004007035041d54081c1c048010709001007403004018070b64803460480d0031131007005114800e0140e182d80b20100e5110b03442c0c4012010310f0311500300d15414100e082e0742000e9000220840758a0440a031003050251105000303800c000d600550640c0104103814040480781031618080200340a00368140301080880b02c3c0c910050b96a400b0780c8081040846130750f2041c1d602814200911851075044402c070810740d40a0703662642029644020103039522450314002e001c0c0d801070f0403000109440c581c0c10360f03440380c0050004200515035504c0310301028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 758389631 1250 758388381 758388409
    0x3150e0f0a0308090d0504170c03010603080702040b010e011b030e04050906090609060c0f0921011e022104020d08040602011509020a0f0f020a240e1203040b070e 71
    0x41c100d40c000208154200314000e4201d02d500c0020407102c248940090400c1c4140d004820340b240640d00c0d0107000c42c40800c403860034008050028443d242d581d00d8510307a42d4100000491080c2d085c81d40455107540324003603800014034140d40b4084007c107a0428104010402d03031058040041058440b100c07501c80380240c81c05000c00c1c0004014038a4211b080314248134010707001c48030300c2d0452400d000c0d074820704a040c1c40d265141c2840a07a0344000a0b4001110f04002c28509108196489050000c4401c191300c4140040701170304103070f6816802c0326180b0b812486000c00380c988440381080300c040c1305907001c01c055034081c1c40544031401d0705409894514071b6420a6000d41c3c0181e443d81c00b0108081070500720040140100e40d0b06504010b10740f040a000f000b0100c48440802c568111001940d030b00c01c000c501c2021380c00500801c6950b802c06031403200341c403500d10204581e90414100d010790311400280302d8503d00b50058401c1c00c42c0c40342d42ea81c00c8000005071448081001d42034454421340da400c10150541 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 758390881 1250 758389631 758389633
    0x1110f0316051c050a0807030e0a0507091b020709020306010e060c0105012c04060504030203220510020d0903060207150f05040314090a0515040902030f0103052503150e0f 75
    0x81c0c00502d8898a808002c2c402001c03205249055408a5904101502c400c0d540038100658507545082d4101d005254005036440d142c818406580180b040205980c0140c48056100b030001c603124503960103c5404000181005a1200800b080000c006501946c0c00c20340514124900e0000d0308002400c5412500d02e4601595482c00100300c0805030341e45200d001421030041000001d424418089a20ac00400180065071170b5400101014402d00c01c0381c000c0080007182c00c55204400781906503142c114001c00d801001c6103201c02c5012400091800c10540345940c035034403104e00b560703241c2001c1d4001900440e0349110643c6060789104060080e4907510140060001d1585000d0034010b03c82d001c8941140b0500e0b0b1b0030015130001c0e0b1aa02c00c442c1c00d0758002e03107907044480f080c8410610a84070390341c04006220f10100600500e2400000101c1c12240110f084564509890342000400550b8503009a1030f914117030010800100d090100b040030300b0103901c2c005a03003048411510b05004038000d0041c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 758392131 1250 758390881 758390917
    0x90301020406050a17041106090d14010b04061e170703080a05180f3f01060e090102030c030703180c08030d060b0f0d090c030c18060e070c0201110f03 66
    0x722588030040b08408034017802d00c000c144c105500d0300ca0500003190a01402110005007070030250b2920a08019101e41c82048041c9121101f0f0400d4020481009914407071030404000245070400344a2060b11126810810480c440c80d0610a01861352040041e1105001d5800e00201240c662009400a210aa04d07250354480c4100207084586081c034203500d120310444e140c6d01420751500b40b203400981c441110200c2c5140900422180d43ca80e42d241c1c040c3c0451014800c400712508107401080850380c00c11810102c948410f41c2043c00d0f400111881c0c00450740500c00100c404e4071a0300810002d208040c50004482c80d00d490b039154131002d039084914168400245415401100d201d070f5001441c210300c010b82481da01e19404034162050000c141a01c5484d00401003c4c010603800c880c00039039111800b00415941d44000c4520714120b007079401482494044006440c5175180041d521401050b59002900c804035030054a0f13154905400d008203114900407088140000c0005000b2041c5a0704000c075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 758393381 1250 758392131 758392147
    0x2071106030615030f010e0108010e070e070201181209061d010804030504051002011a010504030c03170f0a020715090617180f0604060b040c1b0602070c0306150501090b090607050309030102040605 86
    0x4001c0b841a44a0021a850000c490008100c084cc1d41e00940e03054400c00020364407030203c12405000045030140c400784114071406c003086184400c103c49000a501c405041e29914541901c480c41802e440250301244608401c45070340c8601480355009220f8181203007059107540228900c000500c1a00000d031703658400c15016014080303114080e120091a01c0c82c030305820369503289a2485d081c403006025103100710303512801003120000c0c0e078480040390000607205c5020300b02c000d560304110310a801d030f1b904520313494019440c481d08919003917035810740b01c0484440080200364216440103028054200e02d501c09040ac03518188200c0762031040d407000405030303418182008400c440080310568411440d00307401040058100c0d9007810041805d0085180100380303400c044002c0d210303280008040d00480320000c003c0007042d9000300c4c0c4580b110b011280800341c6078001560054a98003c0c5900e001e800c0c0400354aa2401c1030007050705074481c0c0d06407824034103402c000c6802d980060b001a0085034000c50611 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 758394631 1250 758393381 758393399
    0x5031506040b07032609030d02090424090501050409020f011d060a030b011b0c15120204120b0a11031906081e062401270f170102071106030615030f01 66
    0x20400c0316076800c5d0a04007032107032550b40d105291078400f4030354000c01c81c00820b070746a44c0080b00c1d421b0743d2010034140c142450a0442000c03058003c074644c0601d84000843c00d803c15110342004154040d14001060408070b0042d195406240182440a011a203500c8020707203a0a000d84040c041c2070310302003240280c020016100c03800c040b0310041d00c4a00171150101042e443d141b400100c07505003024010594248004440011301c46000406c4640001000103150004240724800c050244a4044076900c072003c101c2f00f6240c503216441e450980a002280c6510380a00c0008040c02018900081b0140e484000034100200810840c9210007000c0200c01c16520921182c1c1d0f01401d040d4245500c4910401d241e090380c00c00d809414104484840c12013414100c1c0402c008209082c0c070589070001d6902d900c0c420440c041d6000300d41366500018187d40034140d0500a40e40b206601ca102003680d41003045c10301540e5000101b08035441b10301c03403541030910b000502c01035009403a10403107005a503040887d00d0f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 758395881 1250 758394631 758394677
    0x20906210f151012050a0605010b0d05090a030e010f0c0b04061b1b08090103020d410103110a030b0c090301060f0b030a1a151201051005031506040b0703 67
    0x1604900c00650204000c00c24030b0f044a03020f840d0107081c0360f500c03c040ca081c910303e001d1605500506441c40c5c2000894501100c0c0d025100340d41030050103002603a16038030801d884003032102e8001e003c1605d02c00c070b100b4550b000b4124103800303410b9481d00070701182c2c0d2070700c9010171600161025584155101a40c0300c1c0d0001d4903042c5011190a4200381001340c2406001e107069003a100c40180140a01044520460b803007601140d0304e1030419402803040340348032803c031900d00360610343d440700e5540044409914044213082484041511111a4090780c0c80e5448155541c5e2480151381d61002e50300b04c0200c00903600d607010340e000318416090151240c016030103040c21035009410000640c1c14001c410002cac008907500320f0703512000629010810b50846885440c0c2c80c0291030840d03a211707051034550500d484c03007a00608242c1400052643c00c50341ea9405101c190b103c011400000500308100160800c07070301d003040554080c0c01400d10b5203041d96503030140403d81c21103402103002441503200340d00b401c4802840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 758397131 1250 758395881 758395903
    0xe0402030c15030a0f0b040903020606030c03010c050a03050901061716120c060f022a1f1e02071509090e010501270b1c0506070801080307020906210f 66
    0x181c80b80640d465841c520060000a00d84452076444040005c40204d558224181c11003002d03009014880c11031801940f19601142e0140c049e02c50110380804e0703071805014041001c047e0f501c0d020320b869068107045000e0240240541059900c0300400106c0404041000702d142c04403001034800071080c0700030300b1000c0c1001e5110b10340c440000300301305001c115209030031400c07217a0508280d034401000c8003041e410008128410803903401c52124600b802c1600da400c460036a1001c49081c84444990b031102a504d040300240c0d6000100b5001c001c400d00c215400c0740c030910b10300178011030f6883d580c0ca18a80700126061640c003070020f0104081003080c1c201c0360040d07410601c00c12000340410360401890004c0340886c2070007070207103071404c510f0182248485d6000651140000d01001c40d0069012410000c08900b048102e40c0c0c0d00c03540c0e002405141c81a0f000b50b06031103000014511f002529001c105600002900040d8881c1828018940b840000c01d0014031036003214002e80403182c044040d00d414041d071518 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 758398381 1250 758397131 758397139
    0xc01020d0f02060c07060e1f0c0c0f080a091509030303110a1d04020d05090c1c030804030c03120f060915030305070b090a05031b0106410a0e0402030c 66
    0xc92046550040f0700140c1c010100070350151617100c10304015000d40455540309519004400c4144080d40c00305440d1070074a02e000c0c2091000c2200e51000712203226100384003902c1c1040c9a0030440024011078001c1606009a144c20103000707469024030202ea401c0d00c3c580f0400300308983c208100300740d0107000b81c0b00000711800000d4140250b103100038003090b81c804960310000d07540058690181c0e4039507056403400c41c1865001c2000d403a020b10036668a00b0b2030383c92140b1941c412150380441000151445101950582d9103004545540d50140c6502903040412404d0000d6095a070800132220300c50400403005030000420380f9407500b0845021280c0070300500310341445142003400841c2c0c01001b12042168451000901503481d948240e017400403040000b081400005003040d658003a2b090070b010594442d00003049020b03500d52903403604142c03c5038011599110455104400900040c0b440049210072801a80071483e000c0041c40741070031074101c015014100010303c000d40c24104821703c41414161 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 758399631 1250 758398381 758398397
    0x18120c0a150e07050103290a080a03200609070b07030221070308091b01050c010b04140117011a040902030f0d03020a0306050f18041a041a0618062803050c01020d 71
    0x28078000840c80055607c402407d10760701c1114068176a512070b40003d00081003a102d4420685c507005090f00c10034031000f48203031540400043c00342004a000c03400780840c0401000c681749891014100340d00035a03000d41c02c1d802000780301007a0b04400340056103c3c0380341b04050340d40e5503510f150160040b80302404184266101740904500b944024010590401c001d0034440d8a4110f50740c011409408482941a0480d05001c50950104411621541691484c0140c0303000d0000301020302c2d00325912003480b90054149611b00d07003002e0070650b00c882c40140c006400c1e10101000b5007007213850020400b12003c00658000303503200405034144030700005041d0440e881c1c0c56209132000050141c041d0032460100000802c404101080005400d6140b9055041907800103890103060902c248080301c040d14001810441c0011900d2820032603070102880d1440010b91507440b1142407051045107802c2139029507009101181d045610205074400562052000f400769115081c0020304000d4019869000d2003519 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 758400881 1250 758399631 758399651
    0x16060f0f0b190312210e0706020d030207050303040f020d0b011410030b0603040305030c040e130b06010201140415020c12030103051606230d020a0e030618120c0a150e07050103 77
    0x80c9105a81c98221442c1c170464085030740101081049001c44101080c03890203141010000c008210b50f4112442902520468907415100b9826403045800c020250b030002c2001030f0024821070624041c4074000781c01c00b841144565185c44101800380c000b80e04141100d04110028079102d04998070801c07040ca001d00258a104004c00c03007038040603100900340500400020b00c220102d0b401d540041c141094031525a0800c030561000c5814054030940d111500c88000541650050055007500d49400c800c40b078080d07480d40c60700d0b55103a40b240c1544c220389800300480b880100d010491980c6803e40403508540e29455807428a00e01016140110000c41d0b91000400c00150000820303c0444003220036448004d84081c3e0f50f0825100d94124074281501c0442c0004249900000da4804c1c1d410030b03003c5a0700c5407258003103109642d0b0328040b0203d183c3e2081c6039020400e80398a014103001c0e14264110344030000c00b50382e518444c0e0b150030740c0c207004c0c0c40d41c50100304260801084010700418081c01c0c02c03c400012 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 758402131 1250 758400881 758400893
    0x30403031a062104020f0a060504030606090c0203031308270f0108071e0c170c010c09050a05010e040b0a080a0b1e01050f0f0a060e090a02040b16060f0f0b1903 70
    0x41c070102110f01050340e0000c1e055440314440d04601001c010070a00134582c40303641c040d0094000380070507036040345001000b0684080900c134451070001c55400841c1556a0803001c0382052640304401c44119401303006040265401c03030f034000308035124918001034080c101b20038041021041600b05041000c0300d4248441103400042c000c2d19280c0011883d0000740c00070ba42611241505000141001040c941c0d660700c20f44180090000504540001d1140c2c880c01d11080310051443c0c0120781d84040c502a0411482d8010815902d0804000d04040f90b0380a0210005038844100c1c1e1008409400c00c2d000e80c02041140c03000190702032040d411f001c000e5030400b6580c64860005000311030280c0c0b608112840d00da80da03110b103407441d9840248109030b0280c0b07a8400402c00066500040d00500014010800300e0981b402581d0a8030000700200742000020303491a9400c80ca07201c41603901540d42c420f00c05089030103010b05460f500001c8804200250003100780f024440560782d203903500c0300c1114401c1c00019a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 758403381 1250 758402131 758402167
    0x30a0f0e011406190b04170607080106022d1b010f020105010f05130b0910060f0e090403050a1b08030402010f0302070c0b090f0a0923010e01060c1403030403031a06 72
    0x8410780d080c1c0d41421001d444c1c2c030310014507900034031440c400200b40042c1107039180b1040c1d50b10340003a034181d42c00741d112140d043d02c0001c0280200d40241e0006444803103606805c40c10300d8040c000b43e11620a007110406801800d14418900c080d56100485040c0d0345103580014070300b640c1c000d192000f0003440d8900038400d0320741c0342c1501604d441009501c0100d880411103402c50003000400401c195050706200c2120001d8071050f100c1d00c004a500314039540522070240702d488009100143c80ea468547d00d956044900380d10003084501803001c12044440341003941100040b42034840c1c0e940c00e50f40c0c00e20303000142c05c1c256503841c2031007010700400c0344500140d120340310f450031900c100c0344080d210300801002401e4054511040c540100300c041380029488071139040250007282011819000040c003c5002d08070550902480c10704d1a090030040280318822405510445c0c094040400000341018402d030441c0d00988040e03001a44030004503004107090a41041004c40885030689440000c00130004400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 758404631 1250 758403381 758403391
    0xf020a0e0127111201030c09140f071116030302060604180611040504140a0e012309030706050f190e120904060302030706051206091b0a090308030a0f0e0114 69
    0x1122034010000c00440c0c120012841900340749641398100c101111031050001d101c2660b5040d02c165001644100070b00c921404141d034032250030001c0d5108081040001c001904010030040c1c08602d2041c0c451003405001100c0f0b8454556018091450600925051001e8402c5106501c0c10a401c5203a0200c0b42c01855195813020001c2400b429031809110503002d59848143c004d4200420390f8690410340c44017520403041b100e010050800130008440c200c408000200c40c403a1400150040200801990b650f4000607100483c2c0c81c0c6040303543c0b02010340360195000400c0000386028044424482e001c5400e0b00310100f0340270800da0011210003030f03842480e513400c440d40040000b61540d035901c0d6a00914013a68000e02107540456071084014004d81c410340b40100043c5100b004102d03140341060070f00340100f007000280342c0361040403085840c0e0342c1d02c03c2c1040702c113006901d040000050711410186120b059009000a81c00c5444540c20007641e44c5a03441c0c02d000e924013484000394002c80c0c4004c076084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 758405881 1250 758404631 758404679
    0xb0a0c1b120f06110a020a1403070b0f10120311150712020904060f0f0f06140d0506010c02181e011d041401090b1e070c0206250f020a0e01 61
    0x2100341407600003000440100d0702e1142d8001008017a09070000348032400e1f1441260203940d02c00c80d92071880d440303020b18080203010688120218103040c15500a0f20341002c00408801c401c155110401c03480110401c004801090400d0000d00d02500c0130301c00000344000b050034640340c1f4941090010440960140a4444154040b071150f1150f01c131544058041e00010301240d4520307403152055800065640700304200181143d002150a03482607000e414104100f012950410141781c0d9807030040c0034002c0c142c1d410805001c42c85e00150f45c860300b040306014030040241c1d900f03062200c510000c1c07079170101c1030b44c0d620346030130004111a80110104014252412101c0134403070300c80307240c003020320400501401c1040d030808098200f0311102c400e11500400907150020004407440c0e420201c02201200ca600200c0c05191000c000750505c0c100405001211140d030707030002a0789401c5501203070588002901d810a000d4220004c6081c6040e2003405800384941c01c002540c035052444100c0ca200748642841 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 758407131 1250 758405881 758405903
    0xe0709031e03120e01180602042d050d022205090106050f03030d090309080703150c1409130f020417060a050f07050a120f02030a0b0604230a0b0a0c1b12 67
    0x1151300294400014a402c002c01031203400f4032401c01c03001035000340c000ca1000c1950005401c030540c034000d2060525200171480402d03070628003020011038860702a01641c00800280c0240904201400a80d110403ca0f810008150030a55012400c6402a41202e03008140210054141ea40c000055a60703043c0c01d20008251040b2030314007101c140d180b55011015500c9910720205c1005440046c401501414110401a01000c1001240c10000b002c80d054411b0204002e20000c60a0040050b0141d0164580210b25014400e40c2c00c022640142d100c9003c1040b00030310b04000b0902800100d03084018101c0a100500303005446042c1010003800381424011300142400007036001d01c403840c80819040408000c0760010b082510065482110011f1215107481c41c112100c0c42c046090301c00740c54000d02019080c4800e05034403900c3d400b044042c260301001c558000a45154404001c0c2044116990303410301e0321a0501d8240c030140c0c100c0c01c00e131441c0340c1404030a114858440e10f2200b41c0582003109961 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 758408381 1250 758407131 758407151
    0x90623071707030503150303030606040618150504210b0c0715051e0702010501030b011205190c1701060b090f1201050411030f010e0a0602130e0709031e0312 69
    0x1100c001c41441d1141d85100102d0000709060b0000c01842c42040e2400004401505410030180c50344011200e440c1d20820502003408018410440e1801070030003440d10391340207038441140c2c0064040000c0c503680060f500080500a00850006200c5845003100d013901d40c01c507041e52059520304005220b0352410030041150303018026024000245441504410089400d20041824044100c5000001c0f8005a5408155030714414403c590480342c00008008469080054102000071080f0b41500d00d44900352440c41081021816a030312503200d030031040250f52400300807484004054203500c000fa4546801048540180001c44e1082c0104803084242c1e40700c1140021100b450201d0650001d40c642410442001106080f00d0131044044040322075000c81d10400500f40c440c4802003e0769a009001044000b9480390040c100c00070031540b40100403900c4980e01980d072001112200c000801061041040c0f01c0040410440c0c1c228402e026282c0c1451070701c024080821610410b2440e40c1d0360003a8003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 758409631 1250 758408381 758408393
    0x10e0114011d2202030c07120509091b04080f010614180106030504020111060901092a03140111031315021801140c100e1504030903032109030201090309062307 70
    0xd0f4180d058a5421916410200c50310103194011402c111780b0307990303001e544583d20340c040d0059425019008103200d0003982d03010523050a6000480101075000f8050101081d4064284060a41c0c099440000031b0914a000000040341da0000520b038000d1602003240d0b1400d914190645056801c90700f008603032600c0307620049403180c84020500b17001d40201c8092225408040d0415500d850082401051441012074008021000f01108031101181c0c45401c100181e0440c00d920700180e52440000b420103c0d601c04490070b03500444025001c40c50b011500810048001c0135000c501d10009011401c101070f083d080d03400c141da518410390602800e07800400d2580b09040c11502140642c0080da403803000003403007074400350408403290120350044c00155204100c1d82d6a13245e10032074240d5a2084800d1071910151031000592000c82c24a400000d40402c248515006840c440e510039400047d0186050a00601e203d400e03402030420040203d142d4181000c20030f21007100205400c100a90320281c0e0320f024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 758410881 1250 758409631 758409679
    0x5011107090216021e040f110a0c14030c070f0f030c050d020a030204061509050306060f060a0c0507031202010c0306050307171c080103173f010e0114011d 68
    0xc0d800348030601c00c44d080d907095000182c0342507811350741403220f170100c1352501090fa0b280344041c2010300300609c800c40401c0d02c901150003056001e6848800f00841040c81b480c1598868100e000c1c0c260b10411040180d9401c2404240060503003800041d52682150749003c0c0c03402c0c60340f0686102d651001d0b5001c2c291358440c508400115802042044030342d6550000c05c0c8030760304074151030012030b281100010f02402d001c644a40b00e1640107100421118002d410840355400c120001c4082000c003058506c000b54081001d48081c5d8001d210010604980105c02425201040d00740c00416042140c01c020a1700c0001c1d6590a648840c2c55100d01a0142c0c16001d06c1c04061085180b0340307450201d440420740e500412074905032030190000712103500030055036a50710321412000d031114a00d04031a02d450746a2020f020144802c110524030441c8602111a4007010000c0c1c105401800b5a040100b0450304c2070032014075200400e09103240c401003c1087c0c00b55040801c210503024028005642c0107000d640540c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 758412131 1250 758410881 758410883
    0x2120c13050619060f180315110d020301300b01060f0210060b1b0604050a06150905040302010507020c100e060711060a03090506280b0103060b0c010207020a05011107090216 76
    0xf00e9001c82e83c0e905401494501c0c54441700000c90000c0804d4212040c02c40f502c08281c03900a00302d0b51400d2680d04d201001080c2840652800744c0b0705200100c2600043c0c00114001d0001c42c1c81896181c9541c40c24084000300c002c43e00c509002c045244500003845108090304454060030302d4002e05182000c00da080026401d90645000d240c04070100741c50318005c1c0500901c00000c0070400d01c400784a00b40c240d840800b9580030b0150340c40350807640300160706034200241a0b11a420105052070b51003e101c0140c075070a03102180540d444e0810861210f40c10407004648003012a040140082656400351503609410561401800c0000e9540244031620030020800c01d009400140d40c1e035440d00d40180204264402103400d401503601041000c59038031202481810020545403c441a1191035070013080e08842c040e06140d1640e400285140c00b650140c010050850005642c0d483c0910411102424640009050011100c100d4010020010b20341013a101c00704c000581e2001e03031021a2843c500e03441c9e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 758413381 1250 758412131 758412169
    0x60b0403051011300901020a0206010b0702010e040609020a1218063207111c20011a09010b04120f061b09262104030b040f02120c130506 60
    0xc00d080e14404800858503004103c04c00558441e203600b59054240d01c0317841c00c00001648014014014046044018803049205040c44da8070005100081415200181c1c4291019540447c11401d00307030300011020132260881d03800f003210b00d20030568401d000d02d00d1440680a5035940c0d00c0949104980703164242d074440049885c08130001c082c3c0020041c004203c411200182c030f8270798141501c0000088150b01c42c0e1519400d50035250094908407124903416034a24451280400c0d1403e00103802c2c0b01b05c540741c031428100300b46810845010320001d400182e00020f2540c40400081140c3e440c41441148115400529200442c20074240140a0b043c043d190240701e4440d09042c50020703070002e00035011213502c0d5400c0005000354002d02c1d075100300070707c0320342e2465004200c0703186160110070380044484a14800b40c82c00d043e229192002485800c039001c13134130315174850540d40661818a1250700080c0343d40d00185400d91200001c03a003002809110b4052880e118030114002d40c1c1c50082d0441507004240c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 758414631 1250 758413381 758413417
    0x60302090613270506031c18060809010c0503090601092319050718030330020d050903072001050f0d0605041a011707030e120d060b0403051011 63
    0x80e048a5900710044542c404043c0e02148003850b40c02c50041d9445108010090507070f034188144c5000100032505440002c11880c2540604082014003172480a00001c3e540c24a05240c0300d5055403c480d1200c4603882440310030b000700512078400251050564003002800306a0303951040c1d510850100448187c0e41c10a0100c0402024059110803400b655691080030300160712401c406540708089111868200030381800c0a00100c0d01844c42040d1050101c3e410024480144e606c0c520300c4055214600144e0303400042610082c4100c1c0201034200041c40302951601c0ca0030ba450054040f03000104098518403100022242da000740c0960303507000c10701a00255500820329150004040600502c0d108a00d441d0826201d941440d5103207401a0f410784541d23800703420103004510b00a400502d21410140c4490801d036545105100200e64007201d81c54607a02c1c2c00344110600140d6000c1e800014a007007061104101080c80055290b249200d5003100040801c040c13071440c82030b0311480c18640c5040c1248 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 758415881 1250 758414631 758414639
    0x5150a0903080c07032c03070b0c0607020d022107060911040f06060e1201090203070e0702060c1801050913051302150a0905190513020405040507030c0801060302090613 74
    0x590058400c052181e52080b070b01e80c0d034021000050b4080c0d0b04d0301400007580c4910050045050745000c030a0105051040c901102502c40000e03e00300a07030300104114007000c40e5103040490104400c94210700d00313001600041d4030002c80203590300e81c0c20322520040c2c2802503003000b00e01c800304210386c01c2541112080c008c421003400d145021041408c05036000354a41703021410038a016101d072000352515aa500c1e030002660388104041020b60580e01a184c0d5600d1001400507581084074100400d40d40c148140725280559010303040c07290080041b00c15000800c45a900c01c070805042e541074420034285036032140c0b440004503000c6008002c0c40380706a0300e000244200d038404c688a050349148200e40318408000021140b200078020101c5441c0410f10521080c013461070645540b040d10340501c040c44801a0b91600082da10001c035229460701160300140c20303c810300b064000c29034400140d0505215081c2c4440c1c0090007080b0507c610400c250380840e807800159075140803150030b2480b10080300072107519 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 758417131 1250 758415881 758415901
    0x70605010b0304031205010e0a0b03150a05101401050702130b2e0203130504090f05010207030e0a05061219021b0c090f01180902040b030f16170c06070515 68
    0x403d07141903002c40c04007400034411807500c4c041c4d01d06071006508001100d44030321014101500b0711076041c0f80c4c140920246c00c00c1c2d080c40010018410504004080342c0740c20300317540c19111003039035420050540d041d041011207107036080030841c0c800303590580340b445c404034000003594000d103043c1001642c421b0f8103137899031f030512103015a06441c10315060070100418048000785d990b885004440c528081007501304000310301d850381c4426001da000380145000c00c49150f40d01400ca80c4003010031070201d40d03403002090039030800c0116040900800d0320090310744144840c011181060080030841715842c4245a072200d0380a0390182c403108480041c1113082442d5506200f920341d08541503444c0510700c48000030b2441040c000d0b805040300c642648134034448034241104005000e00715000c4c0e81040d180c0054452580b402c1046001225000780944200f0324400e40411b2702d0800350303008604c00344003a0184082d10341d0104461540020460381503070f48400f10b24100d41842e1016804101303608045d0104085000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 758418381 1250 758417131 758417137
    0xf120c07021f020d0905030604060213030506071713020319141207150204030c030f03050f0714060c0a052203050105180d051c0203060414090318040b011b08070605010b 74
    0xc2c0e580a40e061180c001e00e0441e422011445443d80c035074090408100407444641c006c00002d06d260140407209070320394071087e1030710303400356034050005e031041e40d4081c0b074081d0144109402c800b881099446040c030303d40010380d540303084003041c1c28900c58803000c010810bc0152021100c45505c81c0070350303c002501c0e081100d142c1d0007041059420325039084c688080030071582700312000d8907441600164020300b503450703030400c08044100403000e01008101c0078540400301d4028004091060380c5415400c03c200c2c00071810310724080e080400c0188180504114240c0040076560916807000d80b403210300c0d10340c0301d002c60300800d030364009030280d407810007404541103146000310100c11a02d411203103461000281250a40700d90382502c2c071100714041c49220114184c0d0001d640240c4007c20224081845054081000005a814000c00da1000540d0b111016142030345803003401d4100c40800040030142c001a02052203880400403080036616003200700806981544c0569400100400c055a10358034410134682c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 758419631 1250 758418381 758418439
    0x100f080c03010b0409020102030f130905010f090b03070b0409020d06050622080d020d03020307050910050405030c0609311401030b06100f141209030a0809030f120c0702 74
    0x2d428141c1490301410b01d4004d40051580c10780c01503183c42038017405516030b07401400e0114070803001084001016007283c02950701a110114082c1342c00e9151100c450211140041158002c2c0c2240d00100310b1200b1400a440440e5500500960b0320480500f2340d0f002803a45800441d80088041460076004800c0540315001038000020f00100070348503a0865590795030041034a0040c0d00100c460721030f851007074004c3c2d85c103c40142130050030f288480c070010f900c40300c0c3c1d0140c400000303002040811a40c43c08200091141d1010741d44c0c0c5107004180c0c0041100460f111801e0310490f1a0903505042c0d901c14542c00b90f0362468628002c12044c00280901051400300b0301c004e0f10103074070f1800440c0300746c40c07d088140004481900c454102124840341031324422624070f1507002280c3c05203c81c075814410346013014400d40c141d4001e580d80d62072102c80509484d0300548262400c1d0720a200e221102510b0000302c0700034441100280303000d40d0341c0d000f01701694810301e140250000083e2002c51207a406403078240d0b40701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 758420881 1250 758419631 758419633
    0x1413050604031b0f0e22051c020c0a180b0117010b040603060518160513061101060816090b0a03021005030f0a27050a0b16030f051608100f080c03 64
    0x14a81c0e07150340e80c1c1801003038080e500700451740c4000714085a031a14080420f010308160451440f1849440b12400c0c40e4003000f984000500c100314105d15036030b05200022401c881260707030303154403810a4548100840101d400b17800660740ca4100207007aa01400e56a400e05105064620007581c48021800e0301d40c102e441020082820020007040b0392a208030b400c0351034611049070400701d039560300c14440d4402403a2100b00902c4410031040303554513503074031f070000107458180c8403140900d00c1c4407081c2d404c6a2065001c0d82558001d440d1103620100ba4919210854890b420701081c80701549c0c00050004c51140d00007507006000305d00c45c40c140c90700140170314030402280c140b00a50360754910810094032824106200301800400d004a12070440d512820846800342d4100c404003511550b0b0b030447e04409544051011780000034032440194940078120015916600c148a2801c203081c4c20010b0030134140030403051064190006d2980d69610380d0050007004003102d5485099920748149840d00c2c5084609402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 758422131 1250 758420881 758420933
    0x60c1e120210020f0304081602040f061a0906040b13092d140712020702100201061521110705070e060a080304050612060102070e15090a0507141305060403 68
    0x480030b0030307100355007508821001903441d42d590f41d59106540d034011005e454450a51140d0080540c8462052a90070340c50316030005902030800284600c108c001002c0b02c040000c0c1001080c106480300da040e9412190031b240c2180c2ca81001200d2540f42442503000b01a905181c84502907445801412101154200c1401440760202e46040e41050b20038651480c03200101200204203004d21440c07140c01d0b41c48940702c00504240290740050342044419440200507910f54609110407221503045c4030401049060940140904018120240c600c81d641c0401082c0c1c0d41190520059030607088816195026095980254851000480800007990314502540e01060301007002d610000440301910b10003084141400800f050141c084840280114110300136490002aa090b10f4140d05001d41c01591032101145000c80902c0160f0f030340103081d0444141800144400740350070196192050301d0300742d003e9035207107100399900300780c45c6840d404141c10082c0050000103002e6807403030080d003040c441c0d40c490301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 758423381 1250 758422131 758422153
    0x231614040b0d0b0703091a0108251e08030a0306140609130f0b130501050102060c0702091504110406080603010f0c1d030c060a0e0306100807060c1e1202 67
    0x80300d007445012504910701d40e10320b1000c03a45080c00b281e4003a8141c94041100701d45541d40080d04110782e642848034030740003001803140358802d00c5542e4012440c000030310140310a02c030750b40480310218420403040c80d00520a0313500d440b00381d2050070050116401129660507038040002d008209601c180c864002000001e54043d180030b804843c2005001081d51000a5100301010010503d03a80700001d0305a82d041e20704019101d02c580340b039003a041c00c00b00140c19807416001905010b002010341c201d480b0304100f41001031760703546030042c0c110a000b070141c01804c548a021800502120100282840000c6030014110754007051640c800c080c164000d00144166007100d500384d400ba4200d080203d8440043d0a040700ea0320a0740c4101080020b00320703020041c044011410a034082c0040c0000038042600400bc182001c00c0103036004403000c2c1d0740d00c1d0031074640100d00b519031009005000030005800c18103c02d00c91424080e500300c1c950800c9060706a1118540b100c4549212000800076002d1442d45030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 758424631 1250 758423381 758423389
    0x102010b0604081f021e0a0311040b032403030301080a0233030405010213120308060307030b070309030905090f0f1b0702120f0a030302090a050418231614 68
    0x40e080b184202c0c02042208400c000041c00d10780a100301c2003d15a007407201e00c46e40c81140103480316400340301a145942e0141004018155514014920b0500604000c1004044203500480782c0c08920400360400510340c2a10341030031200c0f01c0e1103640e4144004000070030b03041ca0201e48100403d00c2140c540000d942a8201030794956204810500811090320002000072244002142d026204200052070081581603a0100388029040f0740c80720302c4080c060303504141c1c03c4484203410110403401402100c2c41d650702c1d00000640100801d00301170315159151701b0113000700107004c00350800a10075001c500d85403014410014084400f590301c0d007107510204c0d10b03c42d2462001c04508605c0c003407071490600d180e000d102c0101903500190781a8812801c00c500801814010142c4c564840e580159032400e44404200c909010f50708040c2c462454140082c02d80282102910405544050b4005821004c84010b03000c0c2c420041554174203000e03c5001c424109190500501510b10320b0b030440d151002824280 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 758425881 1250 758424631 758424637
    0x10f090b06010c03050c010f020d0515090103021c020d060e1c090608190e06160207081b1807020105041a060612040503090d050708100b090f100e04110102010b06 71
    0x140058908001041e06948204000400940642401c030f2822a00100c824219205420002080356003c10482240001409120380050003017014088083ea031400040d007054040c403000344603900902030281e030b0b00d585584d5004155001000c18414103803c0c144140501600c040c0040e00d030092000c1090901c0e0b003581344000d4104150703540000c0504101e415500540c014000303d41e1440d032201d40078031429640c0a101000054140600043d04028502151241c005541c4a0554100110a00a001000480b42030b01d5240c01d8600a122040001084c2d4034208271001e507860000d94010845169015004039015520900c0014040030084401e1100c20405407811079019108128516040709103104941d0007a01480650780303440a0400000c441c0312900c90200c4264115020400c40180188805000b04450050500504410a000071081140140100c00d1481000c01280b0107048900840001c0d2010101a03102c604203400c0c044008040e400c001070041d8203140301a0307502d06020050b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 758427131 1250 758425881 758425883
    0x50907080a05060130200a26030a02030d0f06050d0f15020a05030c03041b120318050a03120201020d090b09010b01110c01050c2803020f06010524090d14010f09 70
    0x510340351560745581b015010356540c50a14010211045039091964030b0703c0c0110002e00c0c00400c000a08014136180145803071850400d46544e80041c01454840d6030003204a07010311542c0d0700c000484c000841200b20080c0800c6d007015411030f185204c0300080065950031009070a010300402c520102100303884d402a4811490a440064000c0c00460301010b07a0001854201e8456190f0400d8a2094024018540d5040e480704e440e0014842a10082c140c0008064000c0c9148480d1003006506140c04680740c0d00c3c1c04e22005101000c42c481d2200014802e60603225200303d05081031040290b54100034440e55415103540356954a4a441d0100700d6000d00600c41680d0341c0d100103819140c1e03400c001515203400c80b0502c2e041c180244040d40c3c800460310a01d0494903050031803000640500e604000386012080059110594480001800710b5a03504c0344826007000ca00e01807003040051420803990b24080c2c3d10b030194100d0514030981c070411441c2032407207441003130420003042442411f8042500b07841080703034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 758428381 1250 758427131 758427209
    0x3030a060f170c0904030e0d0803070e0103020301030c031e0510020d0609050915100f080312010632160c030605090a030504090b06090306071d01081603050907080a050601 75
    0x100e110070300e05040d80c1803035001e4007030f0502000301101c060120b0020780b907242d809c5442d01400400c000001d0f0700b2203400c25841c0001c2c641181103606698138404100d006020150211400005280704000307941c1c6054a02a07200058900308618505110003035082840044001824040081000d440394030a480c4a000b40c04000d00e481d2040048a02e0b00f4040904822084903100201080d42c1e11440703500001040da20700110b5494070414110179030010181c200c070b400c1204000d803294240f00074100150b02d1209070000c034035860302c803a14200e0480c41020407c8100c20804c071070150a00c440503290b04112401203c051044c0d60f80c090407103403905078203040100410000d01041c0500b03000b603445941100d801804951500c0344000c002494100105c4003d000a64940848456807144c0c041d5054122300c282021001030511003100c00c0209004080c4c0c10416030b0f220700141d1550401c004060050044409460304000c280c1000c584400c0240600c21650810801c00d491074010102290307500c015401d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 758429631 1250 758428381 758428393
    0xf080606180714040506040605070b0a050705070b06180408090108180d030b03070302150706061512021303080c0d0207080d020c060711130603020f01030c050306041d03030a060f17 79
    0x400c2528104808812000e040f10140008241501c13a00020b1014140c551103003501c42e111464003c1201a0042200080b41d0508003030101c02c0c0e410600f5214810ba1002c504c2896aa510000c43c0c5c1640310043d25103510350005007072009101503c401130500d22402c2e602c14510390341e05907041101d1240d4004440607030380701d11000074100c0c1c460f070300402c00d5090050644075038542e2500040d829949041445040030700c005054010810b4a00c00c90b00281200e8940400d00ca2800303101030812891050301201154001a192101703060b105c0c90a00030b541c5c040981600d402c28024015600c0014000902c058410464049000340b400610644080c81c60340c01411444012403e02106e40c200174011503440c141075690141c26034032501c0c001a002020b44000a24900c0d6004204014046894542c14589820006510291b008080300d0744560190b4002c1014a0007896602c44d0034440000501c4601010040c0804039240703422883c00c0360560303644062050345030400c456102c0b10444406981d603021f5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 758430881 1250 758429631 758429641
    0x20f01270203070b030703020c160e1b070b160e190306020a3506010e091506270103140c0a031d100f110405030a0602070206130f08060618 61
    0x30416140c07018007a1042076980307402e00e0141d41c109030744a401003500492a15042001045111518886802c10105c602d240020f8046654009000507402c00004072a92981100703c0c021542c00036401052071f1010b24145840c80d0704c3c0030103403407140d0015648610168291400030890344201901881e100300451035665160000c0d84402448004c2c440d602842079620340606154030448a0850000c400b01a61005880d004040050500d418400040b81c2c0092030384410700c0c0d01c2d500500c500d650b4200481102c000030820700a5683d4514241c02c1084143d08032820300b201e11640c004d081e00c0600c6110130134640507521030005ca515010070041481004600c502c81c5e003014030441c3d000e0301c807001c0c000007440d465410036035004885006240c41d0b00e1072152004c414415650242c0c0ca03800f0050a050038000000d0b01e544541a02030225600031412505654a01d02280d0070750010661000f50540e855100c182000c200c0c3c89585803500072540016a18180841180201007100403141550b583e8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 758432131 1250 758430881 758430941
    0x1e090a0c1a1204140d02030c012a0e130c0c020f0307080a15150902070516060f080c04050405160206060904211233080a021012060e07020f01 62
    0x100800a035440a4810341c1c80020413014405000b00b00c60036400741d41e4840c0800140e6080d2404148640c0f0001196109000c940c0e4003592079514901d05407a000213640303036a90004415541800c0c1810086140034112140309030015001860306100b944c3c540050540002050f071180c0d018428001a508901d5406001512902041d0f48020124400083d01d1061096400707404200e600100b40c000e0f8002900d405100701005405045c0741e81c40701141c0a0b50500c03000a00b4060510140300510a14401207074900b4403600c1030341c2c05054050801c212030318000340340071002010607280b280580070f21004589c440c10100b014910a0342c100c401c40e141020198410030803080c5c001031100070480e14080a001f40d01942c09040f00551700c44044d42c01c0030140c00040840d0414440f8440074400c051041082035110100d0b040c402d8a80480721902010200202602d0840b81c901d000c1030040d00d800301c045000c0004181083c000c0c00c1560072150140c0400100d582200c4400d0303510040c00481d8a2144003401c1c5c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 758433381 1250 758432131 758432167
    0xf0703020f120a0c09141b090d0c0801090f02120102040b040b0304050c040e010b10020601080a03050313080d0207110f031f090c03060506090714040902031e090a0c1a 73
    0x90081140c400203c580c40b00781100c20107801500e65103071a20041c032048a132481210390005600d01c60000c0d0b042e000140b85215200d005072a50065661000d10414800d5070400071000300051002800b10300c14612f088403407905d445404900c00c0781c040c110114040414401d43c0c040c0c030700301600c451070a030406088010941004008880c0d5200714001e900143d152802050304500001d030004c5540341000040003868010104002c00b154030020040105490019080c11500e4141c14110380e42d84034499880f0114007035400140a8850014103501c141c1803903030040840d240519554801c810f114070400c00900140c400055040d840b85024194000d00d9044280c00301c1159880083c000038070346d95400d00c0704100c0d481580d000340d0310410041300341400d001e034692118140c50102d0380c0d40402c058841c418010781c055103601c01c4c0c2c0400003030341c10700c00007841008100303a014020100c0c1c034110030301c15900c40000300e089450300c00a80001480c0407021214003400c3c0411100d650910b590000c0c4840011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 758434631 1250 758433381 758433409
    0x2010f080702070315091211060601020d0c0f0309081c03141608100f09060906081515210d020c030f0309040b040204090606080a0c0507030e010f17180f0703020f 71
    0x46d655003440e800103c444411040341c00c4a0b4a404803640c111203002410210020a21415504034110040c450b0360300a41685c0f495622459204250080b421b007110380c21202d802c507220a110382d08800c0c1c0c0103900307992400101c0303c56640920289090302a50030400c1340580d00440c04001d803500c060343c9103001b15000c5500115611a030034066079601ca02840041c015400078442e6075484000b03210b4007805016140103071500e9001031942c100c0340c0b091a442124001c14040034040c1d070740c200e1802179580742002507a2002c0741081c2d210411a0900345031b2160301c0c40c1a004054803074414101010f00340802d031240381c0c100702d8005c1c60401400c3c05c2840041c004400361158055400c00c4042442c00e07240c450140600015925a0000d00d400080c8030121826a5868000c1c01014800540020f0b130007a400902282c00303180088896007203c01c00c6c4e400044c2a40078502140c4000304002000742e048105c40312074010300301142c082d14a66001c094649845020203500b1079035400c3d03004290b05100036131020031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 758435881 1250 758434631 758434673
    0x40212012004080610060c020607050111030f06031c091719030201090b07080c03040f020609030609010c140c0c010804080412080301180212060918010e0a02010f0807020703 76
    0x180564400400d0071214000090104040800d00f030080e03500401c960303544240500c410601042c24801d0250420080c6c00e4024801d18000510b0410002e00707401184050344c18601d681d449040c03580c6118241d0740c00701c5a181c0a841203880802c00e0003001030610608603095103554070000d040038245000980d407052200050310070512030103201100b070807032406201d000b5070000a94007810700d040b0150300b0010301207104002d10b08042c82002051141100c5c3c21a5100684844410461010030170358042c445469074036000320410021124010742045988513001d503a00c440d0700407500500d68960083e4449030041c0c7c0c0c04414010f490754011030762281c010703029090050034199550320000b461104604100c0e01c45601000410844c080c2c1c4c604d107541c10001c3e800560602c200c07174000030005200101100e2041c1c1c0c1c10800314104004c000e000041d0150710100a101040b086004180d807407002c05002ca00140040d000300c0e00d418861400385006101a5000c0e04060789151981020300c030001e580080e50f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 758437131 1250 758435881 758435891
    0x15030c0f0609180108060a0b01082203031d0706020c03030f0304021903200102010501060314070f0e1002032205010c1401060f06031b050412080f130b22030b04021201 73
    0x3d405030b0030718142d0083c00c084004002d1850f080b000d26080d81c1925030340324188407069041c41142c500e00c0d1b4040180c4d0106042540400030f450804030080c0030715550080e403500c040040801c2c5c0c11804076001098558276001c40340c002d102c41c42416a41e1181c2400301980c40414004680189030111a580e85a0f083d41c0034444800d4407502c0d1400020110004400c410420700c4002c0c4855130280900d40c010941c42c1010000d541c4002006002c50200804d032400700000980c0b074544103406000c440c0038005c0041e12113041d0a0f84050040e43e030754015000110381f541c2c50f04d00c581401d074800540900343c0380d040e0340d0003c01070115a034030005001c031040c940c03080c0e540b699404104002160f00038401000c00d954003140004400c03000141040f02d8006400402c24100400d01c280040359902ca852a5400b0621035641d60307508640990034003881c180f6404c2441503030000980d840b0110301400380013420194030941c0074a2140c0b04003c03054584402090001448001005854402e200300000511400040380c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 758438381 1250 758437131 758437159
    0x51602121e03040e06030307030c060e0a0c0b0403060b0406031a19092d240b0409032f06040305030a0213060807030c030e0303132915030c0f0609 64
    0x1100308200800308550b400814208031004c281c002e4103400c050103078007540c540102030728000c00112003040040d000503110181c3c0c81d001c1a041100046440d0004450362000b512040420240d910030722054500c14201007114419240078420841241d90080082c1c9202d61482014042d200703005040c040407403109a26003000750a180205d0078414031602c03400d5034020280c0005210000707114501207680c000c0c4a5080009158644800442d000c0001c072002c009010640c088054640300380103a801038148031003070040681004e1a50500000c42803400034161020302c1d43c40301851400c1840d5440e5201a01060104c2e0140000b1500511854000740c50402008a840340d4a07110758402400210741004119805034144a4540407402900d401e11154002d0062184d0342e01000d0081207400c0301c0348004208100d00e214690040c2101c1c2002d50580700c801e0100302d4142c450440d0b0390701d070301c1c40c230500114600c0c03801240c1b4071950f43e4000c2c04c6102003c848020f111007500220309890b00103d070559100303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 758439631 1250 758438381 758438413
    0x80307120e1e071d0105090106020c10080c040b04080c041b0c0308180f061803040503070b090a1805060a0b090303070f1e080c0d090f0e0a1103071205010605160212 72
    0x6004c03501213441001a41d4176040c103001040e0700581c004811504a915541d01070340c0e6440040c030440b01540780c414210f440d941c1e00b1201d14400c9601815030078030700103000200f9400201c2c52600c0b107801114100151019044240c00d900c80188034140029130b0501404c0019005850560700300b03a68030100542018040740151400a4001050109a0140c01008036041181c1c4601d4840d4050038082d40c2014500340220381e07500143e02402c8041d42d00400d848049481c0e0015481c02400e00040079054801960078a0700101404da502c24064514400003054030441034003107980c0144050021481c010383c1d9240d28500001d121401c8903104000310307031446201c0300300d800000d8560145564681c0ca5401c841c5051500d2004010402485581c0d40304010b1517580c0d161040441d10000c492841554500210300000c003240ad1540b1540880030003400301041d40808464481e10000b04200034690b00c544044d1001d000c0c00001c0c00400b030444a0881c010b0038030b0180c00794180e507410125442c4125010880c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 758440881 1250 758439631 758439659
    0xc090c14041e05010509031905280c05010f1b11031204050a0f060917010b0a03080a230d0e03070b0708061f020309120a020d080307120e1e07 62
    0x5400080040100041540c0340150382c500078542420064940349860004c00d4449452803909030750b10200000c3c007824131000344091480150b604121602c03405d0600e030b6100f00403c5528065605010741c08000c0340039400740074a41c0e0030b0b0f4040d440e959800400c0c440385280710002c1040440b8000504440f004958401300320111b40311070740c1501c0c19105c80c2003e081c40088981907000c900a0403072581c00300b000e260090358020540d50000030b20705e4844014501e8902403c2031910003600080b00031000801d002d41100600b00310704a554444003054641020814080303481c042440d14000e0403c0b61103094101903020b02c12400302e003810b99003480419190700020503c00c84910f0085071071001001440c1c5803180c1107141e002c0d800d40c1400d10648000030020b5881c022668560b001c4d0480550104c1140410820720202c280d0090011120380714620304107425404c15182c000100711000403140000ca203901805114980c150028400014258103890710400030761000700795402000302c0847ca0740700c00304d00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 758442131 1250 758440881 758440889
    0x903020f06040c180605150703050c060f01051206160509130f020408010e030307051206040f02070f060501140d02190f0b13050103021215031c110d0c0c090c1404 71
    0x141000103443c0c0b00384c41000791580c031013202c08940307440340a101542e43d001070150210b92091034a07468011074a001e80b03141c80780c2030211003603200700c00400006000e8466554140c440030307202100c5801c038031401140d80301e03c1540e061103411148141c159405100e0b0014003402200100f08040e9811000ba1220403a11200d2406052640000d414440c101e024040d14201031220300c011460b40c80c2c03501000b89580548015030b201404602c000c40d072240c0c2eaa4000907000d1101c2541190380d40528500241c0d000c03c41c01003202d000d4100030001540422015081c0b40070203000e4260240118160308001450526090300d4540d10400c81022904400c2000154040c00c9655406a42c0710345000702c1c80d0450710541e20080c10940104004450348400103000c4d5080305090698410303c00124000a04048049072400c500e40828200c03101c4440d40039100d42c50130725920051340c07010243d03035900311003e4290040c0500040700043c020000500268030120800d08a0318100307600b440140c07182805c0b40d106500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 758443381 1250 758442131 758442143
    0x509100f0e0d0c150e0a0605160e031b010c020406030b0108030c011a06090409060e010c170a06050d150e030412060b0328020105040504090b160302090109090903020f0604 75
    0x1440780804038041001041400c21420004100d0707000b591000c1d489540148401800e6483e0b8080f2602802c4c1001002c418651185040c085840c00b080030f200b20100240c9200c002039105d0318542d0031418042200c2d005800c00f00080d40400c0000c0e0019201d40380301e0f140403600242c1e900000008224a03240e418080c1c00d042c0069039a0741c9166030708a007503500e0062030a200420140703140c212591000c04070b64158006890104031642c0b20300f04500102881d8090031801e500f0f050720b6480c2980e02905444411100302180911078407081000c0701140e902d80034040e0000c2d031005120022810b020714520080c4880540420301d010a5400c150954101d45c1c00b101c001038900c860802001094050091000300a134000c00780c00003251004c8440c1d842649036501c090048101c40400d41e486101210064903001c1c1084c0b04240e0356280c55245440201c400c0010440000b85002c0700521900807502c44440c1607450012013030409508600420815508030309510030244010781e0764209001d00ea102d0341c0119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 758444631 1250 758443381 758443391
    0x4060b09160f18080d1e1d0d06020c01060b030703140c0d0207210507030306080a230c090114031513080a0c14010e061b03041101020c130b041109130509100f 69
    0x20400030b000d514025410810b001c8801d440b401c80c011f505400e50462141159000612001810300000034031a41c01e0b01c651550078600080754919680d001540140703ca03642c00c100c54040d00a507003038608070070b45400a4507001003006003503800c601d80103004083d00454807000d00a0364003c086450408075a00400440c0307001c121036043c1034240c403502c801062000003070319a040c01ea6a6204244440f0014161b414541e25004891110304000340c1c148840e019041c142c80f56100c203c652440381c800e0145510902c03c2002e02d21110f4802c904c0c69004e4501000030310050845a5940d0342c450308444001c404001444148902041d0450810304800d2803d90002401c0c5801003041d5060001c01051000c86841d003001100380080c1c1d035411243e0040c2c0210b240c5507401c444800403414444004200c66011400034080000321059a0040c003032040d045500304035103110766007050002c2c040c0d203d1203a40070582a80c407a50540b03440e0081980f01035410f0a42c0c40c01030521005c402111040340394102c3c059915 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 758445881 1250 758444631 758444657
    0x1051204030806010e0409050606040e01060f17061b0307030b190b1903050106020c1e1f081015030b2101090201020f390904060b09160f18080d 63
    0x18205d540404010317201448103180ca900c1e0140e0f82e8902606082c0103030b588454aa98585080d4411406081303440c001da00c08a0750741d004002c03c0220031070364000a002d140041041725240304103130031118503941c40b0070342035640300e490680040c039441180e141c0141420040d5072800e0f06509145000c0e200340c002a949a11031012001c68100d0704541c1c04050514040c010300005400051060140208441450402c402140c5180b1511b009038801900a801c1d410f565050703454500b180100c0a0450b687d5644566910030041d00c3da0005110760020722145c4002b40d030005110360084510680042c082c0c2012205007005050440704861007a0703c16552072100d50210341c2d06008035007003034600030005c0440c05c17070180355101170140e031040c0008a00c0080d010140c0c030140010300c000c0c00c164018065034551520b4240341000c0e00c0d07180046482a81781900144202d42504a00b200116081da10308800000450003910095150b568400b0440c4040c072001805000c204a004008410303592a00100811 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 758447131 1250 758445881 758445887
    0x308040804031a091b03060c0f0405090c0901110c0619031d010c171015120504030915050a080117010f0905031e03092d0102031e0108070305060f060105120403080601 73
    0x6800b43c09844944170207155000d9036001078842d81100740d1444441e5243c251070210101841039910190304004050100f2000011110190207420401e80303680100c03189000c400c039190024400066070040c01840201800d1101000d400c1c1c1c50183d03800c00140c069200360f40180c040c03103071844036400eaa450b0081480e405501035031440941c44070302100442d0742081c10424143c4041402042c55100441034080c13003c0744140d01c0720805a00d050020010317401d05040091400300c060151940c441482100f1f054024810303803c0703600021312941d0b410240e0b420f00400600c5c4810000340d07085c42c2e40d00c4200c1761944030301d42d2187c581c01340c0c0b00c0c0004503540c10302c0d040b40d1403000482500c4035102c400103108000103160046021409900d8001940c1189001d0204882c1c06401c41e44900485610100421010a644005400c514008603a02c00d03126a65003903950b689220034000104582c00c40c5011075107620080c0c8150780c100c641414028140107400e890740c00020340813034050b4009802c15007030200c0395030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 758448381 1250 758447131 758447143
    0x120706031506091502031c0e1207050a02190812031005010306050d110a0b0f120606130e0603030909100e0105030a120503060103111603080c0c06040308040804031a09 73
    0x7448100c01c03100ca502d4200c01611104003442000300b80c1c2004400210214801d10071a07503440f002030b4281580031200160f8200400c00710010302e00a100e0401907103000e14040d41904d5480e6131000041c440c03014584d0900c9403c44003030008104190343d0385d0010900070800e2104000d241907061b06551649001160851110300c01d600150515240120600103512039910800880d03402400c1036019019040210300300142941c0701d101c2d0b450700801c10700c0448505000402c0c4034012070b46440b00d141c840d001000000c3c0f00b421010865104020000c124984d244425298003400003004d480c20401c2c00310214800d2042207440c15110b0303564010600185422401c2c560241c2819002081a101c01b0303903540e8412280d0900c403c00740500400040c034141c0c400e4100b40900f0b000049082c1e2038401c1c03108600c00c0354089400440c0407400f03440002e9071001c0f0420582c0e4030005000002c0c0703015144d0741c0341902c040802400a0742e10340010007010000c51710a40701503c0246c04003200030f070185070176003503507081c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 758449631 1250 758448381 758448401
    0x60605130518010308180301090f030f02150a0c0302090301050f040b0915070e03010209131505041b0318080a08070905061207120905190209060316140f12070603 71
    0x2c1084044607000036150000035040d40d51040c00c05035203040d402c075400000202d5492840d895800d080c0344000700008183d114040e5071181e00c40c0000000181400c0c0c0e164850b500744a9841002c8a0003e9803555051300074041170b803a00d050044c07904c4550000b003403d48808454007041005000d0a000401c41070041c4241c0c09500280640007940c00f6108000c030307200000e0669000c1002c0190101d0701503400394120383e0b028900505d038000200a0101100c080c202200000c2c884079181100095542061700815140180319046d00d000c410340c0007810b03401041c0c10b00d071103080d0340035095049c00051101e00043c0b0341c06059849240803494101c0b03004103420850782045005041c14005040007280519002d9040707140d6042584500b1a40c100c0c620081808080150040c481c5082103000081d95089142001d402554092030035992070090540c1e030180816400d03d0300062240c10002e4600183c04014015001444100103126004c00118941d0202850140980001500f0011150544117910840c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 758450881 1250 758449631 758449639
    0x1505040c080f06060f010905090a060905160e04111b030c0c060a02030702090636060d020a03030e0604030606170d0318170403240608030f070813090606051305 70
    0x240b58203000407600d614000d040a4010285140080e03010703070080b41c2e24005480c0c06804400c0d1b502e040ca0002028108512400017a28680b20100d10601e40400800c544281d00342c4802071000c00c84821700005003100c9450183c1c642d4240007140d014070304442031410090070700c001141c40e01c00c0302c15841d0030700c50088802440b41008101d81c07040c00340c000c400d641e0842e80481d850f4a11f03a680c0c4010444650200b82402d110070102c3c25141c912165503410380c40307414101d01c5072000d180d030381030103102c00300e00484c0010b035000640c0d440420001780704608501074294040c080c207040c995030740e171028140d99654205007003103403984c02c2a00c440751007005038070300c5149240360600480002800032903603400707283e401a040c07610380100b403045000182d04039001540e00440f0102d00d0001c2e20241c003204030380e96800c41041b0b170030100700046200000003a161044120034203d40340c081c82d03540b0406140e1040901035034100c4655000148401c0d1403190304010722f61521004d68801c0a484030038501850f54003e0b0303104e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 758452131 1250 758450881 758450893
    0xa1e0c0b06090601020715050a0206090c18090102090612010503060a09080301120201050720030f071d220302010b1504080d0804140718060b030f150d1505040c08 71
    0x440e1010380800d80168055400d02155225140103d0400429400110020750b2150420707010f02d034000e00900e1070718030503800e491a588515444545a24048481c5640644c07603400c28070b1030320311121020350400c001c00001480d00d15410b010602e00d421a907010302074a00e45200400003410140182da034800600181017041422503a11007606d8001030041415201a0400301d400f10390148040703c0d0841d1b00b10000e240d030380002d01c1074a003a201100350320714000c3c054119010582c1d100010500c040d1003400009003042926184081500c5030001c10340132144042c4202000103c80015001c20501d00a50010034028104011700949030f02d124042c0c8180c0600b04403c0240b00804036000c003e9500c1464203051640301e0f8100501801c950110089030741c0100e10b0005008500c61880381204080843c050048590b0b510560303003e4041200d41e0588800b04800140200142e40005104800010032100d0201450380b00c00305138440e030803081702866907100c09101c1408150000c0d44000d0000d2401409 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 758453237 1106 758452131 758452133
    0x8070501020d0b010c0507090908070b0703051501020c01080610091d04020112020c250b181504050102100e1c030f0605030f0c1908030a1e0c 62
    0x2d660380c50408210004c0d4001d003015101c03d900140580220761404860a01030820820300b181c2c20786c02000f20178001142085c0b480d00600c0d080c0d90008040c5000000c0458447d42502490705543c080c0b40e4801d45a81c0c0510b1440c0c3c040d20551714030305402c58000d400d0315420400e82003a0110450480c0b090907004200011a200d24002d03a030b581c050320104802c80c41240b18080d04060650002501c080344042200c854200c20040032030351684107a96814858081c1c1c100c1810130341c0c07a40c00364500c41c107580761281c0f050305001200c070012803420b403070500080e40c2d80c20781c510342816060315141c800c89400b1003440101526448440b502c40700d4208850010010046480c2d00007046261000c0030607142400140701282d4101031008110100140f41080300c0c290000d451088c00d0032101c00003040801d82800940b1089240d07480e01010f002e0200aa6803800b040360f0a030300100117850b04000 = true := by decide +kernel

theorem cover : BRFrame.Cov 758273381 758453237 := by
  have h0 := BRFrame.cov_init 758273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 758273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 758273381 ≤ n) (h2 : n < 758453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
