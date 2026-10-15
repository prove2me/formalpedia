-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:18:33.931477+00:00
-- url     : https://prove2.me/submissions/f7e2a27a-e410-4b2e-878a-1e0e97cc0961

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 720323741 ≤ n < 720503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720324991 1250 720323741 720323753
    0xd15090f121706040207030210050c0a03060803070203032b090f020f0415030201080c090607050d170705041a1b07060305061c0f03030e060705030406050a05010b07021e06070f 77
    0xd4824244030801040c0c2e112001407120b4028101401183c010400c1300c105802006158501076410000340428a03102c01440d1141c2c100c6404040040d05243c1d0001d1200008001c40d404a9000b50196242400c203040c2106421180c504018070040c50041000c05040c03940b1174003216070721a4603030310300c082010b0041055680c611803d25120b1031034019014417441c80c0c4641c181c1141d40c2820b00c10b005a581031010405802500c440c40d410000020391502009808a00000d117800180c95842c5000e015608003482c48800b02c4107140840c00401040c0114402461400c0b401d1500558040c504a620741004c0013105606604440302e50004070280400d64144c00742d039138000415940480c400e141e85035a000c45446420010b001c038901103c010040c107209402c00a4440c5003142100d81c1820040c0008085900441c0c060318042d10b840081a00e4100d140a15412141d04010141c00d1010f682c08020040e116807403c10300320f006041d1480c01c00d4075090080c15060307010300c40d10010302c2070600b007507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 720326241 1250 720324991 720325013
    0x3010612060b2d0f0702030114060a0317090d030f0807020d1b061b08090d2313031704050406050607051e0304081b010e030a08090d15090f 61
    0x182400505104041c4001880e001c140c81101c4401c1000030307600e030f01c0d805684508000038075070078501c06030009481c200161a18020140c0d540700703600810400c0900c540890240c070303050312031035401352400c5020404103006410242c880c04203004e03010715103540706000400f208140c5c0c0c0100c011410418810038840d4000d40706a5112344140040c01200c6113404c1e008118800f1400d00030325004143c00900305103c500d80c0710106c04071800b092010010800c01e0f0241aa5504985144d400e01c0740d40081040c10703100c1c0710300228030302c3e000c030341300510880100100086070001070b4180c904814200340000072070b20700c412047c1d05c00c0c1400b900d25511030511040c070080c0c450940055010b4042040303464002200010444080000c80e120342a0794001e108000b81548100d60054001c0e104190400401518544070412044001d888842030f52400c1d600340354031850104809044c0d40400c0c40300c10524245068120031540c42190f000c501400d6101012044581c01001034a03282040410002041240015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 720327491 1250 720326241 720326267
    0x181803031303030c020705060a030c140703030203091612030f0c0204060905100f1401030507110f0c130c120b12010e06010e1008030a0e04020409050711070f08030d020c1f02030106 79
    0x25110380c40c18100031901c0e0740f04002c900010103654000207000f00b071041d8040250a6093342c0c005987d004075081c001c020750000da8040d103203030050701c0646071407411004464040300c03101105141c80c09400e032010ba50081c196200d110501030b503a0401c0b80141d44a00c00d10001d00b42c1000c00050a0078001d103006c038460346980005a00841d814010b005040c10f980805149000910307011031107946040080781c00d00e5030b0421084043c803170140d1050850001003880d1f80c0e014800c1e54107080c0c101c407090806040d1104141101c02182aa00928146c66142d80000e0000e0901030404105442c0606805007140d00000141c03007103820440c0140040740107020101d4000c9c40208184d0f06441c10203100944910a964880f8107002c1202410403072a03d590701524010000102d042003240b521400c05044005414404210387c01603010118001c401619481c0c251001c200045040001c250000c0c4005d5001800045991044c481400c240c8000c0070a658200c039405040961a0b51400802405070118180703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 720328741 1250 720327491 720327493
    0x40506070908012306030307020904081c0b060d1a060c0105090c0a1508040215030a020d1d0309091504090f060b040c140d0e0f0a051b181803031303030c02 68
    0x4442e40011000074480d4440b190303403246136096229080003030314601c102c040081d00820503104020502410034050404916064004075004040c0d2040a0482d42c070000c0440d40441c06104155805110382d2003141d0412803009200307810300751000020300c07a404c03080001c0001da440c1c2040094405041c072400800d40707410783d07603e60f005003014a00201700c07410604203404c10207440002015580d07a2007126079551120a0f00715a64182242548040d61000603105a000e051001007803004444a88200721800b0031000b450030a1001020000900006000402c40c2d03860600c4000281c0c2c2e540c403989a0462040700d04078850107031458400161842d0300350840c0b19514020312075802c0754105090402c1042010041d640d5065040b15440041c445010052501c2c4514803903441742c1900050301250042c025400c80d442101c41c081c0046482107041a01c640005511800c6820f01048118090304040b6181c2400b101070301c8541d90070303e9a0030031680e6021000d48801e4035001d042e090b10681000045900c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 720329991 1250 720328741 720328751
    0x170d0e040b0d02121002180f0a0305100903091505040513020310060c0503070c03030906171605070c0b16120c0b0609060a05060f1306050304050706031802060304050607090801 77
    0x80025118502c1d80d58081d001d2009028a4030300300109000703903001c0800000c411921801086841603001ca0711807d400e0240108002e060800d252128a090440754041e00901c0c12000380f12600b40030f0b2400c0d8400b1014407022030720101d07180c0003040031889491481e940b456141c600c1c0104019201c1207403405103100c14410401d00c6001e00301061244181d64450038402180f460340e180c920320750701ca001d0001d41600341114003c010941e2100c145000c44010f41e95520700719008000f000b10420303099840a52148100c201040424014030107090304a0081c8408c450f00f690700c11403121103074490a075083ca5000340300000004c0007074400c2156000c055910b00700902075490703915403081c1071001c1e01c0144586c1c514030015032546e0340c010320745000d010042d21030340c5c0300c40031002080d0b20340d0000984081c030361900301d00125071503104000741c034861a0000c0c01409010b190090031740c0180300104004010342d008680341409a140c2c10003c601882c4940001c0c0210710f0011401455030500380c0015a20364100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 720331241 1250 720329991 720330011
    0xb0102070605070b15130f050414010209010207031106220306180f0f1403040806090c150f0a02100903050c011103100329180d0801030803040615170d0e04 68
    0x2941e0410350010780b00b0041754464440000207828a03221620800d1128103080c004003000b01e40d90441c07801280714148440500d08075402c007a090780606a806801681300700c17400c00201b80ca1445c58005940c0c00342c01c02d80391900d182c0c1d02d207900c03609400c0700032400e440000080040020500c070b00c4890303400141549a042003142e686c0741030007500d200003521209004410b0402c1c8401c1c0c0c04c0c0040094482e108803640c0d55665030100d51152411180d51108d400303621924041401d049812820310b0000c0340c001868001c41c20301316800f80d006007544000f18400e40300341072080c0c00c2c01d204601c0c2c558000e45900f6114440c0e8006107007542d00d8603a0405032004184140080c241d02e00b122482500d5000201c2204110031410714803d0702c0003c4034035080d000c29a4103200760115180410164031282c6803e0300c0183c41d0340788090712102001e12004014210410010780441d080358080c21402183d03c13011500660381c1e01082821404000300d00303029030001c00544030456000554a0090078064500f80020320700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 720332491 1250 720331241 720331253
    0x6081801111c06050402031509060f06030c0c010e1b040c17150f1305041502070317070c1a0106020c030f100c090b1603030c0809060412050f030108010b010207060507 73
    0xa909902c4402c40380b0110000c0c0424140d070000030142c60003400454903482c0243d2582500e001300306080f8001c00c0c0f0500420300c00e04103549400120103010b4034051450f2241110003400b40c3c440010381d000c0e55a02c1c40c3e403001506050041c0d01000e40101c6000e0619203003102040211401c005e441001d004503500dc81b01101d0701c10120a500c40080c0070000840609003000c59541380514207680e50149141624034500d6145901c00ca004500440640101d495000c58142c202d1003076003409800305131505071a03083c4030300480d001980078501e450301d15900310303096990901c0302555082c1c4908256041e4014021785604101b11101d00504030000c240c060f1405580c0d42d254880380010038659601e503800e250f15917004482e490014041242c20030b03512030340407500000444040c10308400083c10211b041d0440b134469102c0343d0182c10414054410740d03c5540ea8101622400050442841001c0c800464400c840e84080c500074000040045042c020040c002410310702c403a0402024400180222008112 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 720333741 1250 720332491 720332497
    0x503180613050609150f030103060e07030b28020315030c03010c0813050312010f03050c0405070e090a0e01150f0f0b0703110705041802010e010521150a0608180111 72
    0x4420390f012952512003501003000e04001c0312944142d0f04000a00c000c0b4002c0010080d8100c80c01510304000c0081319503581511807800b44409002d041000c00032860311903400c0c40d198060782205044601e104d605000703032400c0c0c0c0c01c115641e280116141000c0c41083c2000d01c04148c948a041340200300910414001034104800600300403983c56926007118104401042152010f04071340102e580d1660750b42945400907071090204540318000c0446040560800c0d0286500039011511024141980c400038400100401050054466110301c00c400c0e040d403007845050310420b8222a0381c8035a6051000075400040158445070184850380000c1102420b01c1042c0c59034a80d2502d0400360254000c054a03140180c69001613912508d451041042160a040615800c0b4404c2e00d420b40d07140c110300d00544080c0a82d00c5214502e40d18040040024002030030071941c0003010300140d204050420002c00c00b40d1000760440310100342c0400903c4800e15054042d0b075200c1c42804024005110300300242c1103240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 720334991 1250 720333741 720333749
    0x30102040b04090e03040f032105161e060c030f05060d2a050a0e16020c011e0c0f050610140109140619021c0c0519031107030503180613 60
    0x240c1e5404c0b0040c24040078030468004040c207240489500c0e44a090004081d080c5100c6c1c02595940e4940d0505424022800e4495050a4159900702405180c03a0003240840f51504000340142c6014540c00142c1306218181303000e22140d5000410000c0e46240350201c400c0500300c184100489402100026004050014911921a5020090062180c1c240c0060b07031103800c4a80d1000000001003012210392011074824580586044111107a594080e610b66404011050000712034030468441409180805d4000440e1845c1244d20380c609034a41c1340c09000100f10444040d0800000c1c090110702410845006d404a64001003a10915800280143c1642c0c8100f201f607075422090498642e070344905840c46919508400740c843ca141030402512030b0f0310028580321410300000c5030804d4a01c24483c4440c1541d008000780352200c2c00705040b400072032284104404101e00e4041c081a100b005005030b100541c444e0004603112600c101009039a0303840d2a1556009035020b200513680395800e030100204507 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 720336241 1250 720334991 720335009
    0x50d0f0e04150b16050a12030f090201020606011d060c0d03050108150a0f090b09010506010305150d0809060405060d0903030b01030e0a11040222030b011703041707051c0c05030102040b04 82
    0x40a10f01d0044202d000c0740700d0007800c0c1b400349501000a1204501c074018004082c1d82c0d0410050f04514440700444410180c06030050b448000020303d29400380305403809901c0310b181240c00e0030309028009030603540030400c980e4040c1c10441c41103000d1609801030b0350140c403108001d4400c401d07007000d070402c41e964000c000c0c0e1009911040340c02191400e980c8802201d0340c118012406502d4420341060203800180c402c5030020340b0380340014030080c1c001c201c582c44100300140f982c000b0050715120342d1041e400040340380e40d0251003000006100d5865030020615090a60381c0030a203030100b4203000d411200500c813400c1c141400c25407014001080071915089066210402d44124059540131900902034101d1a1035981010344c41d1807040b4400303a8050046a1203500300c06040e07030301c80428030441e113105052510594001c0c00180200b030f4010b0780314190562090116a9403595400014940110000c00c3c107000e034074009000410701c030241c030000025240076030083d443e0130725001003502c9030b100d180f04070040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 720337491 1250 720336241 720336247
    0x6020303070509060d090b04050615060a0c0c0b0309070305060c090612070c0b390910020f1204082104090b0a030204060303030c121a0904020d050d0f0e04150b 70
    0x1080d940d130010745400a440b0a0200800a181d182030000c910042d5030070340d442e11a070310006901c201100c2d000300d03600310003074401800c00002c10f0081d90120104003089803070282d81e10002c5a01212400654415814440108546441c605246090540141c0400c1e0010020807407a504d644501c421105181010001042d85135107101c02101c010348484401421004c2c09420b2101d801060102440010b203075603140030382e40301d1800c82400c402e00300e410494516607007400351359004c2c9000c5558100702403081c0140c910542581e0b4a1038100f802d050b00d02c030b0100d00e002c5070500c11468200100b2410607243c0b400d41c0e46141103110154854050391051b1803e81e42c03107031442c41030f545408001c43e00a540c0684144011a201d00c0e003e80074120160741c940014060520747c6c04c0b0b03400e403801007128100320403a03421060480c0302c09100c217842000f00300f40e0308490200c0301540003035001c104409140401d0f650f03a18000c0e00d0310600401c040c1d48040424899400d2440640d103208804504004541611025560f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 720338741 1250 720337491 720337507
    0x702100e190b042c040510060b120408070804120516060513140d0203030d1b260711030304030908120c060f0604090c03050c36071107180c09060203030705 68
    0x31384000c0c5030300341e81d0482c14510510040010000c2c4880d81f140ea1a8018046141c80b1b19205c0410b000b4200042072881a04c004600030078000c41c010421140030ba10940d00d0303d5141d6210003d8450405021105584109500c0903005620030091016111615002d4541486200c188001d01e1031360103074580310740441c0c841031050342d41c014101c41d480750f01405481d1200d85a200c0100105010f000031108401081c02030a5042d02c90001c03151b602003c0040c070392007210403501c4a0041d160007000d203800d000307504501c689152020030185105500c640d540c4410182406140c40c00c0503000880c01d4103190042c08880440c20740030511039840f0030489054051740d550b100008004c0d1000d828003500781d0070741c05400710900c400410500c00300242941c5104a0601e0020f001f94100e801c0b8200505046025070003071029000c2c03c034000d030410342c1c91622a0301070910b040b2a60601107140d10202c4c215000c0001072509048a02594401d140789060001076030f442e09901035141d00c4020450010000d00103500c42d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 720339991 1250 720338741 720338789
    0x1a010c03110f1005161110050714040905060f09270a020a1d060a031212110c0304031a0106020d0507030320041e03031d060702100e190b04 61
    0x105002d04880704580800301010041d500520701034a2805015200041850710385010b00750b40184070203440c0c000c1c038018030040d400c0e4005205c094401e8040115024490344200c9080f0041c002a0064804c00212030030712000b001001e100b2601c0c83c40c0243c405404000b510b15604100c40100c078003100412000d451448000c07410a50b03406802580210012008100d804000e0019800c0100f07070446018607849500401002c0b070401e2000402088190404130b172100e1090481061b11441c03000040b84140c0905400141504501c0c840002076002140400078000e880c3c1c0f400c204085a540d0740c08030b03075040000003500c48551005c0c1a0178071034001000340c1003511030f45c002c440101c000b200001d246d024644d030098203507103c0e102e809883c2c01c1c0b500741d01c031541184020300c2c0102c03a40f64540404088240c42c001100d04051201c0039400b0b00d0501c20f580158036507108e030303c4580c0d07001c0c2d984d652007014450411403e00c000c0d00c920441d918581c5014490b282c0203800b2901910000c0f17180302140c6e501c0240031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 720341241 1250 720339991 720340003
    0x90105190503011503170f0304060209130915200d020f0d0e010b010801061d10090f140a0e0c0403060207140a0c0f1a071112030403080c011a010c0311 66
    0x709415610708022016084428400c0300140c074841e90556031504002c60100040340508003e003118203208001150001c7c6840e40240348509001d000049261a0f68800d1000c03102000802d45010050aa61680c0181c0500c2b5000e00100c500e00030b903006000384022886c03140154031804041690015000340c8155400066404040d00004184000d14158120902034001414810b0109503084008511140200101040007004036800c00060140d4020031030f80c3c1c03121020350414840346000100310160a10b066201a2404040a00e42914100c06102d0319585550240942c2c2041200713000d100210202202d0859402030009a1181c21b9800c2601c2c01500c620380f000001d1080140c1302c01040040b550b07407011100012100010b03070355100b603a241140c00b001d6200f85260340400203a4002180d00c06c50004e4550083c000c04020720009032840c0c6136a12581003070751f00040218045000e00001d02a80800c14420101c0e80c0010040100103003108603c0c60f0028140600080c031062045010450 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 720342491 1250 720341241 720341249
    0x219030803090c030106050418030804030905030a08131512091716020909010507021203040c090606050408010b0103020a140919061701050f0a1a0f0328060509010519 73
    0x426074905001c0d01c0c0981c1e80440010071800381d400c000c1c0015551034544034a01c200f40b031110201303a620300c80e650f0440f10804024412001c0c8864241d0115080d10100000845148070720551981c8291280300c4a0038002d5503071103001d60f080051071007007070107a011144030a408407604001c40c40074010721344041c0c0d014000340070f603d11500111707851240c01ca1540c000d441050081c0d40c0d102040d1140c0c0c20903400d8070000c841038805070b44030b0f000700104610344800856009025210b00300d08280c4800c8102c0c00e0310380d01e81c030040004401081c01e200d8040700b880313139030700102c42400e045203070024000000e402412090000400c581c804194400c2a031581c01207645964003480544462645904001d0001d05003c17440c007005000d581d0000c9084d050541e550002c100d001003603e0003151500a8a40d940c19254007200c1801c58140459002c280c800d002030350098010882c00988c96204000c82c280c00e90400840400036410000c0822541e110842030070706562040d100d03d482e9020100407000011107541c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 720343741 1250 720342491 720342503
    0x30f0e0a0c0f121b051801090510030809010509010c0606140a1203080f0a0b0d0302011509050f0f040f120c12050a0c0210030e03030a05010e07080906070e041d010c0f020f0307021903 80
    0x8948801c6c4040450340c10303599040384c20855500c907d0103c43c0030124a0000400642c01041981465800355025120380c7c4030525083c000c0d58142d036241e600b62003841c2e08c400e0b03000795a4144100304d0321741410f880015141503020001341c500c0a441c01010440003600d01420840b00e18040788a6810075000000030300c501500e0804a14202d180c024028000f070054100000d142d400d010a45803078a01526018010034407065090340c484400901c0c00d0030026200322200c10800c0070080c0003541c18001c007401d1109540710155400c400e420806c6d00125a00301d0311040000801401c4e2072160030008010300c01da0141d401014180c0b203000180c004144205000c1000c4c8000b0040242002c10707500114140e408805c50035021340c94100050342c0803201a510411a600032000081c044e0b0b10400d1500d21044c801080031900040d21002d01d800100940403440880c0d44500c00300c550150409040300013030358a03100424070b1f5100ea5641c25107074080c108000b44185048000b0071802d03640000c20a024541250b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 720344991 1250 720343741 720343759
    0x30105040c060201050c040b0702061303020a12050c040e0d0809031b010e1002030412030e011409010506031608070501050d0e010501120b0106030603031707030f0e0a0c0f121b05 78
    0x8248001403210701d2041100560903c5c002031030285c03081e8250760840e03504406050400b10194208200ca07040000c003800c0c600400e9800002590791000d2020041c0b094540410804296040c4241000c004895246c0240c2c1092441300003a0310000b20b1940b240e40c14945841c0c540c94041c0580c0c1588201c0601000f001c1c07010700c14804691065110440b4440000112611a86040042d00607400101e074040e00d50089000c40c4000c9a0094200307002100109000084811503043ca00f010080300752120410f680d07407030301000140d050400c41c20081c4076809560b80086480c16241c0d50356540e05009503070401c84040b1b90340074280c000e600300d08644801a0005d0040b90b07124025a0400c01c511a0b0951761040b5101c00000d48900034442c190640703400d940e03115549080c40036a020310a0001c1c014104040d43c038207500140c500c0611507580e1040c013000141084449a007804d68501e5901d41284607407040c001400c0140302242442c10300c80f0f6510101c0c100800d030f0700f290300000220142d4002c642108400c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 720346241 1250 720344991 720344993
    0x90609130e16050405151c0609030509040518060604090302070f0b0928030809120d03050a0e151f0b030f040b090a0c1403030d02070c03020a0602032502060903010504 73
    0x8146000c40c2d00707040155800460355203040006480c0300f500c0d0000c6085505858000504210381500c0c240e0742110304280180c41e056886204584100702c0c06c0d80060400b1407040203e00d000e004803030b00b041e100100c04140f410790f41c0c4110380b19000070388020300c41c1e130ba104030900815000780300780001440c000c2c41c03c2c250b4546d110901d1800c1d0380b185564074880c14060003101c0c42c1010382c143d00301c0c4003103915101900c02400d554400455601012429a2203802c0d42c80b08a2086030800008150061540e404103050070401110415a951702143c5907081c0c05c03607511007400c101440c00b12640f103c3d24001c00c9150f1540004089281003498110042096000080002a4400305030f01c9000d90320440d40d0840ba0b90740e440d12a1744030903642c02c0050650050a40400043c6260030004007800001001d481c501000e250811040f640f047d0001c0ba1288d1400100f041546004191000101002d0004c0d514044440c4c2407007007410a480240d5440060244102047d912500e060300c90280740600200514106 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 720347491 1250 720346241 720346243
    0x21b070b07110108070c0305280f021903020307020f0a1a03090709180b070e060c0a02120102040b1204050a142a061206030a020406030c060306060311090609130e 71
    0x107100030b486000d40000c904600d0351040107101c0c4101035507540c0003554040d560303040f075641d48000400c2d04100744441395191055440d40e02000000d040c1e44510780700309040d110180c2440c2640541100c220580081070010940100860b11150780c120743c0341500c11404d000065017a5116002141c50100310941100c40101e8440114021141e25040300c403059550485034042d03441010710112301080c00001180003810003820960403030214102291001d1130240880d0850f00604046000d59000340b0004040d414a402c582a0800b8290000d503e031a0404100f180743c0c0c821003404400340301c9030388000340600c581172107600d16082c1c1c0703c6500e06252058001441c0e86801e818203084940c00c28222585209081895244102c0380180c005400c0085070480d490405400510302c07a0903001e074010200c0165910320401c0c01652003010441c080900346800201140d0300d0303400c0350062501d84056070403403401d043d040d1440780004643e00c40d0b48900ca03038081103c1064682c1017000725420701000540f1100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 720348741 1250 720347491 720347497
    0x25020c09100b0c0d0e030c0a0b0904090212030a03050a06050d02010c0c080d051b070e0a0209031c030c110105041a0c13230d0206071407080703060b0a061809021b070b 73
    0x2845da42c0700382c1040c0040070103860341d40d030400c0154011120310b001c00c00001d079007001c0c00b68003030300a0000602c0030040e004038040c003a10000e110442c0e000040c0c4800d80c50f03014410329410944101c8100100e03410500030030390145007c0030103418040315000300744c2004000c40c2108007425902c0c0a48004103207491000d802d070b802c40540586100b100c03441081d110702d00000d1890441d00f282d210310046840e904131900007075200f4048250103003d10183c0760a440741c02240f411380c16580d070303800043c60701400000803c60030740329070340c85010b906000501000ca181c0d4900e29840d1440e0302201400c1761103c0c2503c0c401c0d4803030101404003c003e41100081d42543c8094400a0144200342812400800c0400c0140c40d1420701c900079070000c018081d40c40440c07a040540103a00e901c5904486941d47c940100074a0248146d00c1190700c580c031440d0000d440d080c14030b4400002c1c411810f103000c401c0420421000c4c41b5169000d000401980860080b400e81d032a07291031503842c0d02030002c2c0e0751903548540703490029038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 720349991 1250 720348741 720348763
    0x212010501090909051e03040807081510030b0a050703140a0b090907030b040803040c080a0c062a030e0a150e090f0606040b07031e0825020c09100b0c 66
    0x4142c084001450751841c0120f21400da4001c1c05000e0300040c412030f1580030100d55450441506c020f000200380000208002e00142803032900806c5d42200c501440003110030001c04030030120415090800c0003403110b0001507000400c0001c041940e90394003030100c0c014600d42c00068001c0440e101032103003100065012981201040e2140340196071420b20781e5036103070540e11000301b1042c2ca40d00001d022903a250081c540083c402e03500c400e15595600c1940780303002041a800c1c0c0340b144221a080000c40d400624124501810030410600301c0e06007000c551001c4014103024050082c0c0da50200b99959441e14800c0c050004007521200c05540104014564200ca8035480d004040580c04207110001c178003a0184501c01c0149010300d4103080c02c2c103841c0103800ca0902101803014245d07403041c103080d5141c0810f01484099581c0319a9151070a80c62000d010003141c484461100f4040018641c0e030b0118021030180802d4403802d80681b11841e482900c80300c0c684c041081e900d03011410000d800c2e0003041d803000d25 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 720351241 1250 720349991 720349997
    0x120606070c0311090919030e03030d090c09050115050f090f090a0c03050a020403020303040b070501090b0a1a010806030c0d17070809100e0102030a03050406090209041101030c081e0402130212010501 87
    0x940c1c1c0c0e0030b0340c55540c2d05103d28105401d000045100000381c403234048200215405410750381400b113101881401c0c2e0301c5d801c100311946804803c0a010107895480b40300e00524450b24000e00e0440d0500024105100d80260030a44000000740300d00030782c4440d200d0303190207071014002c2c98051404003494001008502d08600009080001007554500c6c0c074025241641c0d00203010b145000e00d484108885503003c42c7c0101c2e055500c0e5481000428540c0841a20034000b91401142070304084400582d01003500324400d050117010418041507440003d460400a0400d44040031030040710309107a004162030b0140316148010000d036203400c00c9002000740040d6a0103440703001c10148244401c1e41c03d840303540e10b0f03140160310510180f0341d40307446a003000d50014058940000c1502c11500401c654100c00c680584100c040d9003003000e01c9582c103100740300340b41483d8640241d26080951100010051203280307411444400c0010405665665620307081c8104031840271559060740c01c030084a0400e00f44285408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 720352491 1250 720351241 720351259
    0x31603080a031811101e05040311030604111c02030f010e010501050603070816031b080103021014030a0c0203120a060312031406040e0106051305010f090e03120606070c0311 76
    0x15100c8041c414612040c3e100f0b43d410700100c0114240400b100541006204205041144c0c6c0002000000036030310302c2c85035a0f00e840c2e0b11400d509190086102580b00c09011b50720610410021071060a48800103005c12101d404902c129810700110b100300789000030307500d0b000380d130f111210b6144150700c940c1041ca120402484107030f0b0b035403003004410b010840300c440100305450001030041d02007101c8004a0350007400c0000d90f082c10804548045c01d40c2ca2214004134100303130010310a40c6800c01ca000c07020030140ca08180100c141009403002d134080034000174034041d103540d034074a000c1c0e0090042d25000340c14600c181c452498144550f1002e8a094801601c16201c07018a042c80144a8007907010b4941c0c413110a0301c521b8540800380b000901c850b06d40d40085540c1e843d0086103990b01d5459054014011080109195042c10f066071441007240d80300d864540e140c06070404040c0c0c0040140d40d40001d07821051225555a6800300d8000c1c811341d14010483d02002130007004206005020f902c0e940300990f0700302d02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 720353741 1250 720352491 720352511
    0x9060f110309010b06031e0604090b13110a0501142a060703050c0901091e18020406030501050d050a02090a0f0f0204061227080433021506040902031603080a03 70
    0x603840c407043c0c5031003424242c400d12041010000c247e100c2c0c0c01ca04003030000074899846854400340c080d410389458043d00542c5864000303000d0b501c0a4001c00c00310855003240f90349d2400c40080c1a440310020161248540032a000b40c034540f01851401030403e0035120522400b05070f207586030b16034104036020340c08a85400e0124100850040540d00d003040183c50344141141058223107005c010441c0f245004001030b150003c100900d03407104050b003110141101580341c5040600c060b081d0f800503000030f80681c002122481c0407810005140030065010740304290180c80350043d100c0a0401ca40764041c2c5241820003d41c003040d410740c020030884045c3da4a82c0e40d10503070150300909031416200c00070240242c194020a00092000004142d40d220f295002d1800340d445043c0880304d01c200201e60300e5a840094030b4415526030a1003e11641c00c10b101074141001412100c3c0d141001c0a0320090007070759241089400c54404004000a0240c55042845950b03520f252100080e4080d4000c040000d041880b608 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 720354991 1250 720353741 720353749
    0x17030c07050d0e01120e030d090c06111603032a0804030606050d050c13021b0d09080708062701090f02040b0f010819090b01030f0203011d060a09060f110309010b 71
    0x8100702d0310581d038600208000c4058540a001b0303481511480d400104a20006a0700e50f108100e02188101940c0c09003524007500900080b032080b900c0340080c1c03c00071100d0044281c0003254070649915013409404003101a00c101460200c0600e40d00c0000910300580e800d05c080e104c060305c02c49200d6102400229110020702413241e0503540c00034042d50002e0303441c252510748250701002c5521080001030030700381704202c0a00c140c034500d021000745800c5402154400d5901002500207803094600402683e8a041003d03541c81c80006c00c200707940d040c040190b25500c3e020382c0381e02c910a410f88000b801148000e00b48003d50f5200d8820484c89a80380c245200b9503810032903445565410140c4a09000b650341940208501c00414490000e09035510040c50002c0c00d01d4030418003850040d0030094140d10144107141c2150102e400361a01491392012400c88040e00042c0c01d544640c1144010840031007919200000d06a03007040210110300304054441204c0e0a0009075108011302c0340280101b40b400d42c240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 720356241 1250 720354991 720355007
    0x2280b0a09031706030c04150311010c050304091e1a0405100810021b0312090c1f050a02420c1b1513050f0d051617030c07050d 56
    0x1404240900f400800700400e50000301d62001d40078080d034440b600b80100080840d8207000307140b407520042003018002c4c02034824854112240a0074010a441c0142e282c0f180ea03070003244181d40c0060703100d03048000740310b10201d10503105e909100d6051010416035012144040e80701d14885002c0d5250000160444809801c080e080350842c00142050803034100800019520201c04d660280741082603c0341c0f0854200014040001e840aa05100d81810a20f603418541c101c0b8241e44100000d1080d03020380c030402243e6207814032080c113006a5a1400302010b80c101030116813420020481d000b0100701140302d00c1040c0803240300da080c2d042080c0c00c400503060080301c1c041e19a039164490610841286080454020032a90994421203110090244401210880031682216a010700c0e0030344c0400c1200c2000150803101400028002d680301d00d80380102680100803060038002a000384180901c0792380340e402100d100800400c61742d685011442d034803041d40a4141107425100303118071000c00a125042c2c1c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 720357491 1250 720356241 720356243
    0x708190e010806090a0c02250815010806070e04150305061008060c0901050f0712200a0b04030e0f043e0d1a030105070309020a05060405091602280b0a09 67
    0x4101526108030010080c80d032414818158882c4104003c10380143d540f207101c070703600d0390b0450b000e01a041c0181ca6003400c10078280ac4009649070340042c05992404120b1071b6001d511490103110750707181240000c01030708101a0903d4110340c09000407007800004244030344954010050064589e6071841250380d82c102c221000e480d2008140081c3c00c45600c82c2009050041038460040d013080c56981f00da420841c044201003011445180426090700b00c48500c20341801740324030240021819940312009a9880200300078100000e1300641c4c0556030f40e07186603901c0003074090000c00900e54040480c1c0c02d0f20351007050840d82c81014824200303100150020010740c3c81c40342d0b0b00711403e04140240d02400b82c2400c14000800715454050071010303880c00d00c01d0174814003140d82d02281052890040c009000c04903041140900c10800c003c0c8401c2c1c54040d121a004410740025800c020088030040741000c3c000c07608602501e07404000d0038406c917981c107140d19400b4001c01c680480c94071295400021620010387c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 720358741 1250 720357491 720357499
    0x1a030f16030f2306091605090a0c031b051b070f0b07231c050c0304170a0602030c0d060e011a070501060b0a1205010807030309030b04080708190e010806 67
    0x602400041c1c1040403220581d0302c60307028900d0368540941007420360b0143d48103500f902d40c8110200090318600700300454503031345550406c03a190340c2454003095102c18001c0c1507149458031030410550440c882e074805000003109102c2100400070710742000b401036028404c2260444135900b414500820081000c01c1119a18110340044600d011400f401d107810400c025120210601e000c5140701c20314840000401199601905240002095088940540e1805001008014407140307621036400402c6805a446482c04001d1070903d01070308628005005a004021600100c203202c1043c00c0d1102810050748040c0c6c1c10f010a64130703101c5441e01d91a00340304c2c4403944501060203051154682000300003450182c0c0000c00c0f12a100c1c3c1c204d149503840b090043c00010f1134010b85241d03030b5482c0c0c403603203016060b0600a06407251075070b20020010f00c0240800391400200c000807504001c002400c50300c126620041194540e0021081b401c003600300d4420380750210b60326100342c400c0740d8410940c492085170010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 720359991 1250 720358741 720358783
    0xc030426030a110a050d090501110d0f050708070203150403170c0a03020315100f110c131e090308010e0129090a0b1b0f0a0c0603110d1a030f 62
    0x10b0421100500c00c982c062106000790001e00011034401e1090807114a82c50316051a114034020004144010306680301482e900701c4244a000c0300d07400541c6003204840b6203003440e01c071809030400407840d1061000095052040d007400b0318840e0200040641300340d009072190f0a81d8040110725100081d0115035242c048001004000c50060003980a5908103141c92540508400900d02069240ba00d2031482c2d40425007074001101000d6002c1c281c0069030380c0040140c10a0b00c003190109003050080c0440007601034803915412942d114101c0c00d03401004040c00d081c8411041800c010306102001c0c0a010b2200300e0740400801c0000c40001801580d068000282c0901d40c108035816100d0303004003148507070026081d0000250801c546014103a458602039000e40700d003690b101e1840c9440d42021414600e0380181240401040001c1844411503070342c0d00300400c08002070034422241d4450018600c01c81442c2c4008010304034110b001004200c0416400c440c441600801c00c141c0d51088001c08000d0700ca034403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 720361241 1250 720359991 720360007
    0x70815310206070c0909030c1202150c3106140309030d0f020903010212220302070b0d1506031401050f061c020408030309060412090b0d0b0d02060c03042603 69
    0x24030081c500f990261458450302d40c0c0341c094240030703218140b0381a80015010f140050503c00c0480802c0d9178080c680c0010071442c4000c00444580e414018400700c0400c002040c2e0132541c000316003041c00a120030351443c2c0d1070341d580344032100644032403800351348000ba680c81140405041494204c9002e0124100150300f404842d540300009410441c0400181607001c4c000d50111751000d0015080c43c00c01c0c4007400e1090310303041c104100c0009140e40f05100d580030860900010940101c0e040701590f000c039800513075070041101c80c00080c0410032200ca005601d0180b000440d1581940080c107800381c41071040c4480c0c0d13652010840801c0e40d000b03205034003020400190401071010181000d6480c1d51b18409820a0ba03038400c158215001102d0421041d04080d042104001406d429020040c0c40d605010317200c1410034805607054000c4000f040d103541d90300c2c500f034007803a983e091942c0c14440d801442d40c0e82d07603641105416129009482030700d9010215800381400b030380341c52401000901c0140300460501e888 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 720362491 1250 720361241 720361249
    0x1b0603010620070f090b010314100608090705150406031505030705061c0203040b0603060a0501140d110a0801020c0c0103091a1018020301050a0b0a0207170708153102 73
    0x3103041910b603071190340c2e00015948a0407003110000d081030400028805403172800502620100320b03003035929649900c100701c00c8440c0c20407141e05864a51504100994481a555103010003a800842d4068110300150440161800040041c1d0310a03507010310100011031b0f140040c10703805010b00c550603003200409100c242002405130280c502ca190481c4008400000000100da02c20748040c2d400100040410986041c1088140c0d01300d200f0700003c00040d032520340c0c2030640816206080340f0807400301110703100740702500420040d4603100620102606545494040c000d40c0700c4100107003240190b101d5072626600a2042540b841c2d00007d09900d0381609141d40301a0741c5009000a10343e4100c800302164003401c2d0980f00080001c2210016035039414901003003e540c0d859404520b20545c01c01555200315400318024040b204141030000701250f024201600b0181550003c10562003200040960f6403841c10f03180d40035441e07030009212146501c030342c000078420316010b480d140402881c00c28001428 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 720363741 1250 720362491 720362537
    0xc0c0e070c1b031703010b040905270f06060409020f090a02041802120f0c090d110607230307020a03080d0f06080606280302040906021b1b06030106 65
    0x5a28503040300702892654031a00c0031018400c0300a10859010390a00411040000595482041c12040380c119032400d140c0c4011840f5600800c1c520355107035030110300002107017001c240c030819507400701c100c0301094000115501d8900154a0721248142c10108420b030030309101d01a2940d4000d000560580709030300030301c1240517018241e0304d111942040b000a01100c01c1e4064644090b00c4c0001503500c8059142d044001640940f0224400070b01400707201e0b49111040440302c60b1001034401e5408c02d01d050a2200c04a04149030007608041c0001e90a03080220754800b2102210351045409988106000403903a207000704600250080d0000d8001e0020880800241034514007402000c680c0c40301c500b00074020389510b0f90100726180e10001c103000c4941b030850582c060035140e0b007012071001c0d40490301c40c001845442c0304c0079005540e2101640b05100203a01103416804002e50444880416040d815607940030010780007014908114202e9824584001200d0488003640d440d02d025001c03680e803100f0303140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 720364991 1250 720363741 720363751
    0x81f0c0516020f03010c20010203071d040e16050406090603050c0108090c03150a0b0f1c0503070f0b011502060c310602011b3e0f0c040b010c0c0e 64
    0x100f0780a4414035242e0f001d0051400b640115640c0a40c161841d8400400c104c01e07207034900d1260790050040003011580320f42a034004841c0011084030400c01c0b00041002003d1a480421030790080b0120305109240811800003115400d0b10200007641e40d40413143e088408900006046800c102a500f90b42d40c803404802d500403074803105850130040304000080ca03101c41c7c1c20801d541d8684003810800c0020503842903003221401669410b491400c0c6030000f41040175107211405c206001002d4010a00c902041565540b59112190359140344070b40c202088840740034403c11222060320300d00d2590541c4086042d03801018800145810144110001d88510340b00741210000412109081d40e0640d0407140d10754000d149039000001c02500c4030240840e405c0f00f004055091007500302818609008441c0f04840c4180740117003000c030b415502280034040180e0380e0145089480340007003242c861030300400c0002c1c00c0c400072034040001ca05414010344000c44c480d600a0400c03110428100800e03010411425840 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 720366241 1250 720364991 720364999
    0xc09040506031c0206070f0f0206072006010f080d091206020d020906070b010503060c1201090213080d080f060a030b240d030806030c040e0607050a09050406081f0c051602 75
    0x9040016810003000300108140006a000805118140d80c024101400c0243c0510f0070250000c2400b601030b4ae03484000d0b0001080003003440a03502d181d45616104c1d203102e0382240c01d80d94596074070700141c0d0121829020b44010f03805004100c2ca525806600c00c036040f100c000c9100d4a02c00700c1c60320742d07500030b4101903035586403140c08020803011a80e07580010003000c0e1003143d203441d241d41082c1c10705140c0203004010000138403041182803041c418003045036046424010015a4800c0c0942c241a0215010360040c000d03449824040b031031443d0448820380c4038082032544400595901010820101c049120240209031290040350000c0c44c404100c0091146005c040c41d0517003410408a20307070f003c01d00420340000c0d5954007400390a02e000e0002d4040140b0884092180d010f0640700c9035211513010f44081d00707100002941c242c415008010510041000030001c20240b584e81c00c4a6442d2801d4103980c05946e100098030020590300d510643c1c09254040c0d507024100f42804601e1440140c09990990388 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 720367491 1250 720366241 720366253
    0x241915080f1b3006040605031504050120040303180b070b04020a170705040e010e15090a050a030807110a11010f030b15041a0301030218040602071a070905090c0904050603 75
    0x46409800303030305002d2080c49800c8030f6240b41c0700c501e80b50a84018161a00c00d074140802000242d400040d03c0d25484845003a1010688891524034010b00002c6009418004000b0081e21445816006001106e0003074582000038041d42e180c030036040c1c82d507014548e00410300340410f0000c900d590907208d51240c40901040103443e21504165140c00b4a1401482c003680948003c0c081e60400340a60280c10000300001e119010503100250307140c0d08950300f144291100a40000c004030410840820030719008010344e2814006401c000780b0040040781da0030041808440c51100f1008001802811150850051194442400d00440700441c0f010100010142c83d1050000581d564240c0040900100003c0642e910300d00b0b42d03034404082c0c03030803101e450903001803004102507200e500200d03100d40401150720341c066032245000402800f82d0f190250000c5d500f01118144030b98460180c902402558032006880c80c3e0300c108101c9580400c90b080c150030709040c0014000707401e10307820183c1c1005009041d550 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 720368741 1250 720367491 720367507
    0x1309020916030f15090e07051c05070315050a0b06030402011e031e0204060207050901030c180905160806091b04050a0e120a03060b0403020108241915080f1b 69
    0x1060303504a00c15a030900706003d1041003a0744a1b48105006045850f01529007036107080300140445000b03803909c140c8410701c81010b5041240030b0201d200a154010b007180300703d24401c0020001404111071a8941031301d0050303070340c09900c0e00000b0b8a20a950503500c03489000b0a000c0c8000b54002010103000a0589402c807901d0410802d0807070f40c040c9031400000603250391610700020315184441c0d02581c0903041c8000140041500884038805590700a4618040006080904002005141c401130310b00c0c0540b01d8212629480c4442200855180500b12951601c400640303680310000f1007e00d241c2441c404240340441e04054010320343c00a0718003000982515800c0700a0f0400524003d4405c05100c0010b002009603094130444000e0082000c03200e0810b07045074006800c0540142c5103030b050741c600c00e101e001030b000d401c07018130052203026080b4203440180c0c44c9141c920152034084c440240404074000d00d0702520464942e4440c120405685075103444404000c0c0001c410113000b80009407040200407 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 720369991 1250 720368741 720368771
    0x10c110d03110f06100509010f140303040902040b0903010506011806030902060706091a0a14071d0406080109140102070209041b0b04060507140c10051312050c130902091603 76
    0xd103c2c8048007015048528103581c44141d1051140c00c035900c2019150010710103130710761551407001d80d544500b4101112840c403000a1541c000d950012104d03600000380811071100c0e0501070507070303e04103900a00042c0c80e4100191b0f200300d20b0454000824440c16420400a44241c01000b6814006040c05160800d103840701d01c280d0f6800c40e0181d0305c40041f100043c246850100c0f14a0f03015015032003c02401905071180c00113050041c0c03544040003880d0300610315040c465844035a801c100100100f0441d07907a8800e07103001c1c081629040c1c0f0141d12020b8488000c55041c003c958200340d00070100e1040380d41320358903500000342c22031800c000e80842c2d402c0400c00400e990020406080303103482d03541e00e41c0164a003160301d1840c40d009000031904403102884060300c440305040721800b51070a0071600d0b074005d0b42040e02c14103140e500200c4c0c440504800700040c081e01185000c0c00000c103880c0c1d0360000088200c8803059a0400900a400c0400940010301e2010680354141c8118213514020503016000401c403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 720371241 1250 720369991 720370003
    0x901031b051e0d0e0106030b10030c0608062107050f01050310030b0705120103050106180c0801090518030d0c03051f03020f0f100810080705010507080705010e030706020711010c110d0311 82
    0x141d8031390f9511342040c410b00000b0709079154000000360303410016500315610405400c94031b104041c140320144010403443d590703d04000158907107000400c003802c00c00c01e01c0e4690b41c105510965000f558400320030031070b55209508803407160101c201c40309103603483d41d620800848001401d590802c0340610000c031000d40d045403040d00940c001d10000c2a03603414030b010403003c80440428115940e25056190844a8001c03441904581c5102070000340341d030710a8202c801c512480f962860030380c040020040d240d03811603480241050300c15a01042195500c04184603070000306a4000c0803952061030401c018a80044042180c07403014080341e403440302007008034415035601d00202c00030803d40380410035282e00040d024002010365074003d1641a10f04000600380b4480c00300054a4500e00003030307202c00c0c0030702504030605c2a2039100480742d1350021410464000c1d0044c102c2242c602103030040c808090340c031445c5c1085a040e00040400c1d07441000d4010031100a2031420114144030060f0000c00602d0418010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 720372491 1250 720371241 720371261
    0x103060207050c2205060a080a05010501081e0304141c05012306012a0c081f050403050f031b04120614010b0f1803060c0901031b051e0d 60
    0x9078442032940380c841d040001d480f40c2c15005148201c40541c44200e0b070b5445400d8400c04c15000503843e2220341c042400e404480e002146248119400341040183c1540030904031821070342501c05860407a200590301548e41100101d00340d105003c01c2c0b0086034a4082013070312490081c2480341c8020409881000d200000400341c40d943d642d05a8110b420a0b004070864041e03440c503619100c0307403070705400280c41102c1d0110060714440c0340280450482c4ca99082c103a00403600100074100709a501c0b064255190510303204c0046426000b04404070035800c6000d00d078055030785902d0349401d14025050f40070554000500e481600caa00080e034564100301e0b10001d00180280d4559051881c00c141000d000b556120303c0781304003c10000004110b01114042a5140d4044080304030b541c402c5c503400e030310781500d44440d11a03500d80502d40a000440d44020018001254217803824460141140c81d1400403155400004c0302040302040400902503a004a4003060200c901c000ca0030510610256421600c4900c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 720373741 1250 720372491 720372503
    0x1522030b060f09040203060c0a17040c03050f06070915020a140115080f030702060906120f07080c1e0f070c0b070b3d030827040c020c0607020a030b0103 67
    0x1e2006504140c0b500b4414188141ea0740f0030b46061030790201c0e540e2000106611420800820f0306040c082c8078400403a59515102c5408066003010308111030050541c1c80101c419100e0620448405040401c22901c281d42e00d8480780d51180c40c00203980000d28040404404500920300c1c044001100c0f40400001e20005400028125000c520348400c59138454002400ca039000c600da00b54168000811200501e6064a80b903849410090100d00300e400313440032f01922140c081d010000c010324000c107820310490360b50b41c07070141d245c4411504240a01c200c0304d00180490324141c0c507900d0420000c005100c5000318900c441d140042d5a03c0b40e4403d10381c9500580709202c40007a4150074403031056070054004810100e0000f0074100308032203035920a2140140c10555181c03e1000c001464180c00ba100116004070441c0d954142002c50328501c2c01c00345d0111060089141101c0044e4140341c498601c035008641c0003008481d0041c010802660040303181240d101d00707031080101c001003070440014000c61260b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 720374991 1250 720373741 720373763
    0x20609090907090b0102010b030705041d1005150429031c0c1211060f19050405011e0b0a03081e0a02070315050417280c03090b0405152203 61
    0x300d0043c1958072a40025046a05040f901d0000b503401283c440d0856034216400220b144c012400900d01d8043c0d0001e0420a0007207010f0010724403c150001c500c200f910440703042d1090045230410086800e000e4a03140700d040d12800c1d0183c500800142203001030401000c0b0351482c2c0c00580b0580c20017589400e00000110b071107490740204082c0362002d000d22805800c1c85040300d44591012951550002c00c5030b20445000030116610003003a03140d070340b0740c3e50f44d9000c2440765140c14204940a8001c3c1c0504880560903c03084405a07080c6210b800a40345008140c403e03468516259034903150041c1c1c0ca00d280c0605401641b402d0242001c0040c121200ca94000d4105549142014a5003459603148601e6003418003040100080712007020400b08106144100d4442020191b9806905031040803110300d50066001c02012540000c102d49405102e544e609801507107804031034001d40660301c100c0d60840071038030b0403d120f049014040c013165180024214140d40441c01e6218a00c0100e174003c0e5a41c45542e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 720376241 1250 720374991 720374999
    0xe0124050a080607020d05030a0b0301020301090b090f0903091002010b040c0f08070e0102070335090a050105040b0d0c0c1a180c0114160c0e071b03020d0c020609090907 74
    0x20118040c002d019a40103800a40341c032080103134031074200699450402c400007000039014407035030b400b41d4601d1f0000340003107459686860001004011510a031482400000002038600c9103503c0d05d00d1107142c0341d4cc081c5007800b440d1000c0c080130a100000300410340d5220f1458000d103407154841d120910000d59601c914a03d50480043c21b000c501415841c04c004d11807040510341d90700000d401c03080360361007a0b003001a482d40b070b8205070041c0d80554514100e030040208002c0b42d00c0074000507019240e0225050134885640e007005641500c100d202d11005000f06201c3c500100400c0d074440751003c84903042080300c0c09829601c0110340d0190b080952104280101030000c0d01d646607541c100307010483c4009000d80e0b4041070010704043c80c0c0171440544200001110340b42c83d0005421070b400c00758803510618510340c070383d001208002c9003190f181d00003801a4080e4084903000510004405400d50007801190b11494011a9800341c585000d0342c001d8010071030b450f00f580b60361400780d102e041440082c1c6a02828 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 720377491 1250 720376241 720376249
    0x81204030b0606071709120102030a0507030b0a140d050c0a06050c0730080408010207080904050a0603031709071703031b040513270312051b0702040e012405 69
    0x80503000c0d030b02403c401d000324030004d10048241d44084100040485d280e00d02000051400001034214442d0b035400070040c0601c0408540096010311400c1e20103000b00215034040c400151810b101e07074002074056844962407800e000300e2412020740540c1c25242102011070101b900704000d680300740b000400001c1c0c0d000c10b4880600601010b010460383c00c10038400302d81260001e90f60b41c885d000100140c0c0c03131695000c12807101d04840050121000035901d9003c281006030720790b002041203c4c091424040001e9441d4000d00ca410181c80d41911000450b43c2402103c1480b228005c0482c9058410200301080440104030b112084038912070080d50f6034076124000405841c1000c00e02c40001d4400e2100b0702841c0c2d9240c0d010500c1d50f1088000041c0e1032101080e100414010300001c40c0702040303071011842851362040c00341041000416092002d03032105d68520280015900710801032910900030301d0010b2900d50801400480e00400100c1c0e0000141d40e84400613002c03541140035800211010052818 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 720378741 1250 720377491 720377513
    0xc040e07031a0106450302120d090f2702130e090d02010b011209031403070801030302060708060a031101020312090d020d0503060307120212101e021602090a020408120403 75
    0x50780c69442d00d42801810400c80b40d404c8070714810038145c01d4070300c02c0c04680c0080c480d4a074021030f0001c0000c1c1441d100c010065458501e05448200001c502807404181d00082c0402da00031500c0b08148400c40440b443c007092000c50498600510aa408100126105000303020b074101409007034889112a0070507070007043c46d0201c0d1107448000d40e4103142d0184e00384c0c1c0c1c02807024003000d680c42c01d01203a080c0043c0742c00c807810b1a10080710075000728044144029a0b5010728590305803803007a0201c60698540010039100001e0490702c080c1c0c031000400c001c0c0005124903040d41415034040c011641404141b96449810b580c0840301980c4035803101c03100708000c1c0e07810000100c5183c964100f00380b65047c4580401e0b00d4120034042e04507513085030051403045448000040c1034030340c03c0005851001d005c001c109030160451a0340e00340e508503a114400f012010520803a82003042c2c084508800300800d60910149160003018201c0c5154240300019076080180b2104041207043d03a1215076550440c075042070290 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 720379991 1250 720378741 720378767
    0xd0b01060216050118030314120f1e010e010510090e19062123030a0f02010c1b14070b0a0203070203060f130b1906061e0206090c040e07031a0106 64
    0xc5854400b1700c0c0b503076800340c0300540340c141c07500c8030301d85030881d0100c111485034200703440c01d03d10040104499a6852071456004907050740d00d0a81c841c43c8001ea0781d003487c000b80690b416100001004025518281d1a182d040480b581403a122060740c54100340d00743d15003103c40c440c18405658055484107824030034030001e4500b0148412180e641d0845111510074401c100515404040d0072006000d030803080d105200e899003108489c0d691090520081002c11000b800c64090360920340076100c464040c00032038640c10054030041103042c00030b4942e95001401d2808c1e0155601030582c01086a050001c010140050184c0013541e031002c40d4414035203080703c010300c00090107d10100b80090b5810f0510203a41e242c0d0030004560b40c50315105c1003800d150301c6d0014043e800c245060400100326400900951358890f181d80381c0c0c3c003da0030302d80d000d03a1a583c2c102e942a90ba5001000c62154901c1d0540c480900d040a01c01154010750311383e9611594402d41d080c0200381020100010801c80d036200348110510 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 720381241 1250 720379991 720379997
    0x40504061a041e1211032803030e070b03190501080c011b02040615052a120703030f020d050103060f0b060405011b1502131208030103020103180f0b06100503040512090d0b010602160501 81
    0x20200c1103a010391f244440001c001e01705030301d074103039140302003000c01820b0b014000c41ca240903600d04000002c54080b4064190b81443c06050600026210001040c100c09006060f1542ca40c0444841100081d10310290300403640300b5640c0314049114001c80809054540e0140c5405548104e001001000c0b9841e0300c100c101d070b200400d4020120050003241c0805030300b4a0f4040750b6100d40721803405070054900010340c49402403000c546101e104035aa001a4101ea01035041040301d211881e060505444c004d0008a4204030108020481075100c0c49041541e822042d19a4021500341e03070703030382e000c80008110f03400b10305802048004441c00c0243c0300038014081071003c101300254599a00f10a03020510019040c10782d100301b440300ca03c10360785100c0c000e10b0b400300348540001500e10b000d03285150700361031050103090a40c14400846000b00116030259410000410f020500c82610380859031021400d56041441e146013100000d041e81030b5107010f002d59402a10b0f00c400070410506124440390300c89410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 720382491 1250 720381241 720381283
    0x13080d11120f1309020c0309040e03030f041401140a020706111e0a27090501050f03030405044709011413061208040504061a041e121103 60
    0x1111003400b00e409140000b002079481c1c00c00011034103001046030f4480f44a25000041c0308100003008002844030460480d07003001309282c1e601c405581c03070002711000040d0a4024003c90085040d44401081c41c142000c00410340c01d00c6402c0085000310b0a4502594440e004160701c41084010301485442c0b010b450a80e60030302c08104ad5440e00700d01c0e103000e01c88100c0380c00212102c0141c41044404d000d406c06400301c00319085002101d1003c0301e11442409080c034540000800e07180b4010f03441c84a0810014004e50a150400c820840244039420741c1c50912404c2010400b041c050030510800b000e03204101514030740e103052500c240d0890320440840d10510110005220141c0c00d07003090140c804081d1405039200403458080c0c0000d1a258100000e00060358a2040070048508001d100382e840a40b01072184035078540000303501c42140300150308070100c00d01091110100104455021a0044c90001e078055602c0c41c01c1d40c0882c035141402d507074038010072140c00002e00f400c1202c00c203080341103032103242 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 720383741 1250 720382491 720382513
    0x2030303072a03020a0308071b0213090624050108070f0c02190f050a12030804030c080d090819081501121b03200a020304091113080d11 60
    0x612031100801c440280aa03007070700035890110200c002d85100c0080240c11030508454200a5510004004120001441c0200142c03003d849078100c2050000c0150400088980c076508020040216080d62116982d60b4101d007008a00c1c24000c03070f0700001c1c041c002a0340c42503180444030140c3d032643c1c00c9181400166000d0140d12540070440c240e203042c15151040d40e80c0308900c0002d4010f490301d07001030941c03c070800e0b0125080307481c41103820072100d045521802640c0e484080d00359100a003031016010424490028021a014003241031070303644140001880c10160082c1a02196234036102566074540110f86079600b02c001c190702d100d00840f0f90400300c0651412034507090740103040544c01030400640d180c800c820347d0702c0390b000340c020700c275940a00514507000404018003d010f403060320001c200090001e85030003600d00d002c450b4103807420350103146454204800000030781389403240c8a421810401444145a0a02c140d2030050240c1d03201a20101b02c40e000d004042c501280b904081542000c09005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 720384991 1250 720383741 720383743
    0x309140603011401210615080405030f0306030f0109060506131505040b01050903011b0e0d0308060423040609020f030d0c02090405011803050a03140c032712180405040203 75
    0x24110b86000e840b82d00710381c4110004842000300e00c44030800c1c3e90100010303c92030243e20f410010665104107d802074001103c00d08403600f1509aa025006806c200440f481101c0680019035001c0d02c06011502d9182010b400d090171111121015141d140e42c52051002900c1c001c01d4882c3c600071024014841003241000308104040a403003514400c0340e6422910842d64041d1042d9454000c000703000300018440c880d00d1614145495030f251000030714480c0079014034941542d20302d25041d015a1452802e54421061000401980701c40040c3c5c03405a00d001d060f08110700b40e01c0740c400c6104000100e01200302e817040c00320300020302c01c3d03061003500416111803549a000304107044403501102c0013400e40d01c030b0381404c500500c0e0010440410380c50440b58a0181034018004080c42e10742958100306951449551860840042d030760601c807090200080350110542c04043c041a0f652900c625900c1c0311001c0000340f51000181e004080200c0100706910751a0707080c80c1c60307811b07580c2c1503505001b00e140c690300003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 720386241 1250 720384991 720384997
    0x50120090d03030f142502070e09070b1c0606091a07111807171005100207080313080c03030307020607110a1205030a15050609060d110409020703091406 67
    0x245006038001c81e4604281407094002007000b031a5000f042048900424984034074100132110402800c220701c1500100400000c00c5083c0321746a6805041aa4104000042407038005002d0030964821201e002c5841580343c030080039207040480c2d24109940720180c06d10300741c4a4542c089406d000142d85c0030480c803402c2022010030040083c082d10340c1d0b03010138509580440502403000f90801d03000c15610404031214520345014a40649843c110300510304c0e4207060406040b035070130f800395848680811942c240301e42c40303200320502401078400542e00e8803413031440c2d60000c0410505001c05114104000d1a09012602c86000c05030701641c554a0030010180d500d12001d080075003080610000c3c102804401e000502d05168807480b00b030024486070100424030342082e510705108900d07001e9001c01d0401100e603d44110380f00a4011814170050400700200c0e508581c0d00202c11070340303418503021440400001000548a42e0300c0060307e8507020f003001400080d00c0c2c0c000041001c4495032400d0560748400035 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 720387491 1250 720386241 720386257
    0x150603031106100b0a05070c0906031e0f0f020d0b090c21070b031b0c010221190f060906170d180302100e04050a050108060903070803060907110d0309050120 69
    0x1900c4ea2081174013401c072042d1041c032070301411046444002003103070b0065070400300840740076a0901480343d0703e0303074121389800c2d008100062044810407102000a29180742c940d81c01400289030481c0a074007610b0750a0103480444440d0815005071002c0540c0e4500010b11605210501c2c4003103981840041142c1c0d5103c0340340c002ca41c0d03c20000310000f43d05518030005040001d03600d04400d5258602030300800c2c00307900a07070070800c42116403100e103454420003000050300c03600705001841c21180f0b000e40f40b20000c203030b0038030065225a190030001c01c4564444c000c2d00c004014414800048442c0361100c80d00b0419403002074030401c00141c20020348a000011690190383d01100c080c02c5100120f41c0c10344494004020302d94002d414802009141032031540070f10304036911141540c03440d540e035014154480c85583c000800daa40140081051814035030002c9610100c17034109402150f10714205a8a440c084540040000f91685405000c1150038010703840654200d0100c0c020411006810010078021500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 720388741 1250 720387491 720387509
    0x60b16020f0303071416050f13050a06120b04060b09040201170a1b050c160602100b130e0d020d020607090302040c02010f0608070512030f0f03040f15060303110610 72
    0x7074844698003807089540241d806140e001071400c04000241d144c600110403800680391000002a00f0f04003025400060000288888880103090450038020031b000f42c409000245c0d00c4c0300200e840300e0208c0e0000c4130306019040b05212894145401300640d00592411401030001c0002d020060b608420740d408016441c1c1910406c41d5565460b00c001440014000c2003c0c0c1503443c0a100080c0c0c01c41c1c02040c41c80002d038140c86003a603030065031060000d040d11070440180d10a0f02004074007210303a884a0300382e1100030304413003c01034030040e89001c0d074200581692164000800311140c254042001e0304903c141400544128a003503030016280e003180b03202c06030049480385400350109100b035101c50000201c4d00d81c01c01071a80c40311201903495005000340f50159540701c84c011403409001042c0c0310612800d040c4140f40071250710a602c19600003420440d28182c00502c0c1d90001003114240c031480c220800b000149681c91410020080f1001c00d00301302490308803205100000d4800014082907508803c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 720389991 1250 720388741 720388759
    0xa0b16080304030224040302060601080421031806060f0e06011b14010c2c031c141222030e041a0901080f0f060903070201080703060b07060501050301060b1602 70
    0x800c00f6801d084d14140ca000c240d800e01701c652402a03070444500c60040380242c1c00c9403403036640e0b04019030f0955010b07180588504c085198411a0303026804d88400400801d240c04a208842c4004010780000a41401c8620b1601d0b843d00307109000c00205184006c2c01800c1f9001c040d4104940082c00550903803810304103c0c5551440f000030f0220018003046990300c800001c201e4a41e014a000b05010401c030364120a20110b604c1503249100300610725000090000c0182074100151010080da180c00308004a0034021003071609481c00715490050030b88090210001601c034074103016451103100b01008412001e040030000703100426030102c064080000c4c1036030001290220b200c0802ca0803c0300d60304045d4440500000440caa2001040c40310480000300222100030718038016068503102c08480f00481a4006c1c000b040266214002e8940c0184160030000751464544c2540d0302c884e4030290064801d50707110750042009003003d00c910742c0101507280c50701e0309060742c81301103c404124200f0040e1092480c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 720391241 1250 720389991 720389993
    0xa0305070c0206160b070903050601150c1202012a0e120102250b060d0302150a060b040305161a2704181b0e01091802030f0c0a0b16080304 61
    0x8190007401a50010001511001e8580381c0000e042180c0d002241d80308501804101c1c090701801254040d2980403000c3c1141d0380c00d040344100c224541130f0581d010091040c1d00c0b4000310710318004140c02200140c4c004510340031180814402425a04c800640650400010910341940180c880540c240b089554000f020301101059001e4080c9210000b8400540d41c81d200040405412209100b48210030f80c0d101c95581c1010840010351151001d40980c101400c402540c0b5140c0e03806c5648100c060a0000304c1c41c0c2c80d0b41c6032071403540207900102c90650102d00400c85005003003d010300202806150070038024281e150030304150082444c08031403135095040d0549003400c5c850b500200d105005d4810480c0c1c0f031801d90300c14040c02100406a81c00b00000f981142540b042c080248152465404410013603460030080c0002000745039188403406960100010040c0e03001e120b40402528040700506640e0a140100400010158040e9403d00000c100030900320340203c14280704aa00700c1300c040d860341d5171 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 720392491 1250 720391241 720391247
    0x140a0812042105070308010f030f0206070f060912200d12110a030b15030f040b090f1204140303090f061e0c03040303080f1e06150c0d0206060d080a030507 68
    0x902d60300c03007505a0403009005103241e8080301800c85030b03009588041e01c50346d0f01d0640c1c80192456000181c04058404042d10241c02c150000b00142c600c14a41420a54800c0d00c070a011074610040841d40c2d0340c800030800b10455401884101c1880c80c50911122082031640c0296407040c0c0b8403055001d01c550b1811000c14100c1c40c3e4001451002c1600e0055555040b0307031401002442401d120350f01c12418004840c648401a00650b4402c0511000c0d482c0c1c0c6e40c455484440754520700900702e00f5140300c0d01c0050a441c40091121394070142000d620191124141412445040c50482c1518080d078002e2040021940d81d081410030b5006050314916660b000001074540e4000031080c0118405a001600c1c0311249000170080040b039000340c6c0c600355039442e03000d40d04510900c16980c5c10f80410302c0300341d40007840104e01c071101c1d0002d00043c1003166410100201c040316810501c18034005401000040040c0798040c440d05902c85012110000e4103a065514002d06006900c00e1004041c1c0d180700082072940 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 720393741 1250 720392491 720392513
    0x30b0c070c0905010602010e0601060f080402040b03031b060604090b01092310060201060b070b06040c030b120a02030c150703030b061303060f1103060d020d1703010f03140a081204 79
    0x242110360340c14080d882d200c0740c4015020038816a0010362070850000084400810390740c1c140c0f100343c1e40b896010011a81c044034a241c002d00142d038090303992030300790016580c100004d000b850022031424100e402c101440c5d41c104103000b000c180c041c50814039544005040300d00d40c2c4c1e06640c800c140000703001c4502107621003086404c0d00307801081044001804189603d14023080200c0c0e030306074000e0081e0754a030105594180140c04005007134480c1d03040811800d207000c1c2c000346851007080c50001800c0301e85c80b0000e14141c1a01600c541d094000b8442d600031750030140414004003509035040c42d50307103020556050180c8207264004d41090798074000480b007a42d8410489041d1a420340c0c2d03007414142c030b906110004104008441c030080b4604540201c0c034200010550b132141034011b280c070041c1c4203660280080d500c034000d0100d502c410501c0340d0700d49103515003000c0e502a2090f01d0003606040d080d482e08190f250704903d482d901c41d90150150380005507001044461800a14002d03a0b0640c450349001201d003d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 720394991 1250 720393741 720393743
    0xa150b0d03360b0a020a02060a0905090a051b030709030b07030203010905060a0f051905060d0e21070201032c06060f0415091d01060b0403150213030b0c07 68
    0x1100a8000000d0591240c076000b101c40882800d80e6468842d10348804101118140204500410000c10807000d0010009000340300300500685194080590003d001d039071002c00d81070003240c2411000e00c880d050640e0955807110031071380c0404c1503042c040d51024884a2406412102810001c00174035003d208495000080d170f0700107640259800c0c02c03140580a0741017401140211881c00f40003511510786650140c04403407610003a10040707420001840b902c201c0c030b1203a5130031079045501c00141d01c2e11000b004062016448400203030b04900e011560f41031044c0030780300140b50a40c82c50740c40004a1000202c030300242c1d0909000500c4406280340d485504940420012910b000301c210340480c01d40801d41307a11848c0110b4000000c100d1110800048078040c0c161624507001e406e005209031a031a9000c10164001e5100305048009400c82040c20346001d0b800c09a0610808201042044030007041000c100c00810002c1d030410307100c103402c01001c82c900e02c000380481c600c607000300312050420402c5a900c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 720396241 1250 720394991 720394999
    0x110303070803092a01080403080c040503120c061b1c0e032d1c050703090807030c0203010506040209030a11040209040606080402090a06032406091803090b0406020a150b 74
    0x20f0b241c0009196101c020f59440c1e040c0d07442c0100340c0342075076281c02200b603245620161191540d54845450848010304000c1110b0a072400c01c10000c180b5036010480c104942c3c410724045c90f985c01c1e20f008010304042c400b03010100c00b8409115040d1410a4403000d4800914089000c1507070070585144100140070410b14070055404009480100707140d5060800301041c40c1d41d141400d03482d9842014200d584034140e0415524907103042044c2d00a440e84c3c0145810011520300824802c0c0151201405613112020490100303601240303c1d011070400f8024141d01c00c404980460402c14000c01080e00e92400b208001c05070704044100300c4c05580c50b0f5041d00d1090340054003c11040c1c0c0c81c2ca9014141c003100380d034141d10400c51200040c45241c40d44c05500d058980c030043e03103820580502c41141c418403508818240c10313a1076000c00300e043c0c51580300710f002071980b008241090040d00c1c00c005c4c1030521184c024a9a10340f04000611582d500000c07503281c1164480d40c0490401c10012241004101e0306400640c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 720397491 1250 720396241 720396247
    0x16031418010b13240b0a08041a0915010909080a0c0611040b09011b05250b0d0203012d06050a0e04051503100902011b02060706110a1103161103030708 66
    0x9a0002d600c24108405a8911900c03140507124920b811502d01c0d21844003003641c10070203001c89611a002c1d164000c1e1227210040d0f560240d0000510014804452171002540600701580410582151481c010a24500108401d00480e1902c41c014801c00780c440b420b01041d40582030030040d41c0d62111100f201c41c003455070346650300c81484180580c00341ea4610b000520304090010149200d0205c1064250301c41c1c020800902480c0d11002c00d0b0f220003110090f11004002c0020b0142c694100601802901400060b030784d6042401464444014600d5611b041010358140c423104480d4036503890642e0781c0c40c140140c459800b19012100c1d14184981660400d04100a110322511410010481008201c098402d070001003410a802c5500081c00640002d039100749401d800f030000260015141e0010703004601e4043c1544030700b415508043c0c503e61110100083c0070101e0380d400100018940300b4440030710f2409848021802400554003400303402074000810403081a5001c0045800c0d0b554000a0b26807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 720398741 1250 720397491 720397519
    0x70e0a1a0d15081621030507080703180b09150310080109050102030601090b0c1515030624040c02060a02030c07120c110f132c030316031418010b 64
    0x30040603200c0c0c01c02c3c0380b240040d4041c00e0b1400103088426a255030f010110448410010404280c5d4200019420b00c0710402004000c00d40e008018681903000fa1940000302c0801c5c040c40f03992140c0f41d800110191406c0c400512075a4824480365000d0341c8640160741c4944134940301c0380b12900c40307902c172042d00c0d0b1a00c500e0404110042d00034503c0343c8000d0b02c03500606561842c8a01491007596001d010300d41243c4a80314200c8841440b1f10b400484000c8404011200c110100c1d10f09081035402414078031855041054403545c10090040b0b400058405010f04114400c0207507072000c1c00350100844030b4003c000a02024001c030266200c42e5009082249040d00020380070308400c4a00740213036500c20800c0010036581c00e10074581d00b8800805041c2021b00740b10704900200500c810b03442109204c280305803100309420190001701a6a103002d01031543c9042c5284e80750f00c5101c45000b4a0241428400341012850043d0300882d8888641c0358008054955170020030700400030103013030035440810428904 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 720399991 1250 720398741 720398771
    0x70c060b030f15060303070206041a13090f050108030a020c04271208010522020a110105071d03010b100807050f130303030b040905060c0d09020306070c0506070e0a1a0d 74
    0x1900b80341c4a00511078070f1303111101450f440c0d100c0c1001c00b030340000d02003204004040c1040b110030780c45422804014107108000410210320b1079258040720081c0d44038840e034030105901d440b0305401020074900030362810034a914065107465504080ba03200d15036a0000a0f40c00c40420070400902e0700060100c0c801d842d261905180e10300c0099401c0c030001e00700074000300d01420040e011007003441086d91607803018904042c125020354022099a01000303980c1000005a070300074082c4a0007002c9544821005442c201010083e0f41041800507100760304080c581031941d2203103404000d5070300300e51401c0402ca640307996054406115428440524440001d04030b85c001769807100030f20a8a1099506004040c6d401c000c000507075a5441c400307003168014030081003041c07554030002d0010b261224808642400a500020304200381250b01c0c10110700924480002c03c641840116031007001d0307040c050000d8841101003040c070005401224100f550460070700360f1410308602650504a184801071204202c800c07400c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 720401241 1250 720399991 720400003
    0x150a0210230f0103050303041709030d0302041a0906040504180f2102030c0d0509040902271e1306020d051503010e012703050f1206030c010801030201020303070c060b030f 75
    0x19003403029080300442c0c41d11049101140c100d03500180218190b49980d00c5003c1410002100c0f003505d03003c00c00141c411610280100c010070b0215450041c1c40d0352800615103941905510701c00010002044507900940c0c4000c180c1d4280c6109580c0041c02100075140c2e10ba0309001f102001d000d4075000b2200a0800001440c1c03402c055016000307128102c8a01c0e2800d07030342c0b4095030510402c2c40c1c00c612204156244100b01800300c401000704007290b807400d05e40200300c410b00b4546000f034810820131070040c5414190358850307030410940035012072114142d99407560000800390006d6115030800206009001c0c90340c05541c1c030030648110400107410b06514201760381f4881300c50b850007075082200b41440610103116954072001c00208100c1c10515506030242103103240e40b803c42c00e010b01403128204401858010380708882040b100ea40750344c10600200346c944580072400e0b030f041280180040c40146da020082d01c0d003000040c1070041c00d8010901d000d5000d03146114000c1d42620a14004003010b000000349 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 720402491 1250 720401241 720401291
    0x409060b0702010f0f0203040f23010f120c03140a0f14060a060e130e0a050111030c16050c13020901031803020c010c15020d060311010c02150a0210 65
    0x1000055036825503200315029400000c0d0114503800c046881290068194851200e10f920540f0b04d400d0700c4054005250b041c0c4d41002e0701c3e030440900e40681404000b075400c0760824003400e00514541c4080c400608240c4e400c90071401441e291011036006c0e030b02035003252855011610101d2010701e0841c030120000c050700307144250340c681010b1505002007070611086008103000390021450508250f01078450b0000484500c0d0401c540c2c8090202c0800b071803103101b0b228a0b1a1000c0c00111480b818560309491309600d450094860400c144010491030340d040703400716000b0110003000b501c2507003086424500d401019681001d4080d25030a0f18040c40d90050100d918241c804005544070035041410f65603030701c10001c0160313100306004007841d800b69280d40c084610540b2042d00000c2601c19020990300040450280261102410f0040017084140b203090f80e4001e203031a900c2440b26400180b46c2810801da580990600068104542c0d84203000000d980c1109480600c5840c0b080c00030f00c0036081e000d1350 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 720403741 1250 720402491 720402509
    0x20c03041d18031b12030f0f071e0c0201030b0a06030c110111030403030b03031b150109050f0103080d0207050106290406171e07031a040b01090311010c1704 69
    0xc0051000c42c0d20990380710100300b08200642c10020341c2c060b0350000b100c3e0014030129a10071601d00c01c9034901c60301c00070342c401d01d4500030403207403402c100b05072100025000e480c00e4103000c0811140da00700d6103c119400103540c1030f4580a0818201d9000507001417001356101500181da111000c03c01c02d40617007181c1e104007c240c2d43c1c8540000c207080072600300c4044841070980104104082008240f085c0c01c514512000101500e180100307000b00c55202c440340200c11105c1c0e070041007445001e00c40080149004080c13181080c419450305441308411503805003c018124100421480c9030105c1541c10f666200c1c0c0c0c450020800207850300011500c40a081c1e812484811100240421100c0f07030205440480da25526180c010b210040410410b507400100702954005000c3c54038201500040703040340c0904001d0314001200c1d0441004044c58407134005025010f6428422021311690340448600d00312504440800c0742408074100484050517000700241002203103051442085405100034400c840d0001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 720404991 1250 720403741 720403799
    0x607060516030902010519090f090603150506180903040f0801050603010f0608030a0804020414041a1f030212011404080a020607080112021905040f0204030201110705030619020c0304 80
    0x40c0341281510303d0440002e000400500c00d15010304540450b01e203c00900f820720b200540d444044d41d1102c00c81e544c0c0300300080b5071111420418130030103814501803a899808184040d15000c004103040f0b020b81601c00c1109542c0400040c42c4003001c2c001d0381c014180302c048d008078855440030342c28080c04043ea4020301c00d500c0c14030345040d007108034840e441c11180c00300081c50600602d28000d40d5000c0c001402660400c1d1079103d03501480b400f01002a06c01e07131144001d803038900315041e00300c840700400a0408080c000e02110a14440000a02000403241e0454080c030045185880035400f44c03171620020080300050209200400007c54040e0401d83c0300c80d402c803001a99000c034201c0301e503030003071050710f0603a00c03243c05000150030104049100415950051031505641c3d0011404490b0340c40e41c989240c590100d0103004660303000c000256042000740003842d08506110009803031b80310140018540240b0b806520018aa4940541d1070255000c2c0589403200d41e120841c036100c3c2a240e4200032076030700c80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 720406241 1250 720404991 720405031
    0x9060905060c0705010809010b100f03180201050904020f12010b120903041208160233040302090f090f0a0c090506011b0305130302130c03182f06070605 67
    0x20107403540c928182c001844414034103c01520303100e00141420302c840d502c912614409440d040c8111080c00d18a0345c940c658940c0300b5000601301d03500508242c200c40300d40c144100143c6c0e81303c4241d445030b040444005944020265100c0140d01c88c614a018419074004000a54a130458024040305014040d4040e095544d40d40c0c1d25440344aa0700400c3d80140b02c1c00c00c24000701b40350700c01400e8001c40180c008018043e5540014612109000b00114520702010f810500d24a800c140f148042c1e201601040c00e050456000030303410580141100d06c1c10396544001041030004004039030070184100141c410203d29800c0155283d01540101e052290a0201007882d95120740c000000909440200403c50186681c04403925070101081541d4100380c3d00b40800540e954503d55094400c1c40308000442c086d08040140540c1c100c0d010b44640104840a840301144081c0d5040440076200000211080c60210303c003030503013a0003000c15070480c0b00420f10b401040201d90100f401000001e2442400d0003032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 720407491 1250 720406241 720406249
    0xf0c0501020d080103170a2703060e12070b0c040b07060213050108130314190c06050601030209130c0903060c0c050c031f050901020c0d231e18030d09060905 69
    0x4288401030000320322040c1c019888446d48040c100c02c1c0c00c54504040b904206c00c1280703419440080c3c042c5075898020304200200149071040280800a02c00901010b4418611000356802240e0025140040c030000040100501c5011a0050505c81300b00c5602c2d0102820410001c2d00429042e200e80117003000c2c0403d6540c09600c0f924844c8000b4545014240096942112112000e01450403208424040c40074103500c0800c03840c144001c5a034030080d00d04c8680c20408103462029040d035051520402042d05240c1b22886240c4004120ba0b00c00708050b03040c0203007125207191680c40034240300c2c40d18038688220340c0c0c0300014201c041c3c052000c03518030302608400c01d40c031028299420380e1100b55001c4440041002da4002d954020f41040006040c42c0c0c0d4081c0c00742c100000c0740100b1001803020400300401401c014400c0484042c1180d000f4180403120b07208135004a006036000300f070b818000c109554102c2d405000800c034110068103a908003044541d0281c0410307550b0040300086405c0450120301424 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 720408741 1250 720407491 720407507
    0x3180507080a060e06220f06062702190513030b0106050309060a05060603060d0201030b03030c0105040c0905130204020d021c0e150405030a2001091a060402090321070f0c0501020d 79
    0x1c4502051112502c0d1400c415940d00c0c50110100c0e800d01a401f49a0301180c028490340000f8a0758100103c642d50108010030900401188000710140c41446115000060300000d00c4d40e03550a800d05650360702260003030000c2e144003039000400c04078130350001040240d40701d8044d6010b81d00660440d282c540300c21100c00203460003100c0071900481c040c000580e2038504903982011050060400180102006021070300316030014200f0125a9125410b100030840c0300c4070318030000c000350302d001c03c25401c0811125101e04c001d000040e200b607401080c1544210b0305d84d4100e5000840c0074001d4445080321106030300c060122030880d00b042d8011860f035405100c110354900c03845554000051403401801c00c500340d98980c1080071407860204100e203494500300b001d200b8500128013440b080203030048405d18800c4452001046c0a0107a0700501c049605600c0001c0c4110342e05130240d10030440020138041d2071900307024100000d40034204141c928400d0114421b544d5040e01c00c2a0b080e00d43c41c9407030202c1525000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 720409991 1250 720408741 720408751
    0x4090b040b03120d060815041a07020a1b0b13060806030307020a0b030a020906030408030907050f1305061224010902090604030303240602160e070203040603180507080a060e06 77
    0x60800d004040c0a03d0f544401440c031011030b202c00141054954180310324103002c0a08142429010200b80010b0040c410001d0892702d0141540d50b445142c031400080d151071814000405445a10380c2003a602c2d000881910050a03000703d9994a030987d00700ba00d880101c0d144100b1000c00d54100c0412190b04000c400c40d6005500a00050f40ca9441d014200803a03a100500c071104856082c0100c0110717580c0c1c0c1c001503014a0058103a42d440f070405214450034200158440e6210702c000d982070741815226105c051804584d01c12000030305a5134503002c1030f485046200860100c0c042c22180c0380b003c150802e861030b031b540c2c0d0761740c0b084206a0301c58500e0400c901c1f40150f4258072402c24001000040d00c01d41211500c5001c407454407900c1e10b400110480208003580120026800800300900c0c08024060488001e0141b060b03805c1d42c46c00c18207030194503807046000f50010551104d4a102c1fa00c05d200d1000d161241d0701500711034210381d640300b02d5078a80c0200a82100e0240c104001c03020301520014590303010b5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 720411241 1250 720409991 720409993
    0x140402041a010c0813050402133f0c1703220302030a021e042d05071b03051918080c01090e06040b03060f061315050d14030a0504090b040b03 62
    0x15860940700d130b4082e0342000500c8034020328200c02c082101e80741c1d400036100307038008040e80d1b0059500308010520780a503000c8410782008100c2c40d0a40e080704000c150100854010181800d017058142060b0f0040089a0081c0768883d2030b241900070036000c008001e1105120044100400480008000204140b240f002952690000b2690800352404901c020b03170380036081c00d00c900883c5a000c00f080a0783c4030103038940d280907841e081650060300404a080f00f4590812420800c500d000381015100c0301c6010740c15014554501c038840e08150082040380c3e503114140e040c80550b41024a0000d2501c1c050070308400a26800c060001804c181c0083d0314100d80c10141c40c0c408030981032a9a00707070340d0b5000130449a80170340c4980c500041c42e28144040c0740950405400140d2501d0004e081c4800609804401e008041c58449400342b0750400300403600030f485013152000300000050506000610044454100c07502002842c00c0d6055003110080081700d502c0d039418440d11403103000300301c103d50252142c82d0701 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 720412491 1250 720411241 720411257
    0x5070807020a180e010e030d0c090f09090b070201091703191a100906051c0612060b01091a040909020d1b03111002060f0c0f040807050406080609121c140402041a01 72
    0x140410540156500301d085241c40c2c800182c0cbc640b48880002d4166200007903140d6502c8155080c003000c0400c0c142c0c881d01900091010404a030745d80c08402c2e00c070000030700520b4004800728840c40800042540c0801e0a101c003807200e111082014a0102d00c9420543c1c0b00c0d40f8904170219085000b8060601100d00c19110b4600b09801c4104641102400344000c40d03141e90740f20030108007920b240401851080c06040d001490041800014100c1140d82d0010341000103c14003205c080541c1c0c0044900b580e1000300041004c801901c04901c40d0640d9050052003840c01d003010380c1c3c2d0b0403400700e4050201c0740168502d48615500f101880744056a40600c0c4005811900c0000d40c0440c000100382d4010307111840b003a243c01c081121241e0f458000d600804910740100b141045140b0305070203028091310068014010310f00b030605031241c0e00d0780c1000085444460100c0c0380100c2060fa81402c010902a00f80c040c401c0390380613850808481ca0445003244030301e00d051000381c0008402c1c1c003010001e80741030b10781c101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 720413741 1250 720412491 720412507
    0x3060114060d050a110c0d080907150302070c0b030f2d01030b04030e09070f0306051219140a030314090a0c0b091f091703030708010605070807020a180e010e03 70
    0x1002e4080100012540f40d150400c0b85d0054183d0001440c00a00c0200546418502d040380108030700c8d001340c020081980111402d028800700074820140c00ca809080050341c8500a02c3c140f1818092179001600c2618040200000c20100c54403ca20030800911600086036141c0b071100da40150240011448100030001030000030a65840c29400c01d020742440e20340010f5200004c5d10b101c07422206200043c400a0b000b50311181c160161038040e00d802c82d41000c1c00701c06900e046949221803c11440c404804840f06801d205c03a5400d2032011000000070b595920095060190203858102c1a014180d460f04000400020f8046040424958803100210740300d86040510310103a004600c04541c0300c03128941d0071500301521002d158440c0c0c00e58a401d08110719044007034003665004039211505400401c01c00c01c54035800148941074451504015845400b2418030046900074100001d421442d03500b800710707901c00450000106000002c0050011543c0a458282a2606550910124bd0080c49400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 720414991 1250 720413741 720413767
    0xe01091e0b0c010e0a03051e030405030706151203031e09050706050d0b04090b07170103080307080705070f0b0414150412021525050c101d011104050306011406 70
    0x491461010004075400700490443c90030245811012804520006614200502c484000708d201c0142c03400c62a04506d055218991240f1817804002c0400c2d070784040d00c0c1c0400450100c000081c02d40044083c4191096280c06030040c00307690b800c8112000e5842c0100e1640303e05000f0340004a51103005403500714900101500c958100700704500c0341645070012020691550300c44c1c007000e903008a800307140c503052034072001d0012080d851841000103070b00130040c80400c2e0740400300c0382c00a40c02e181092a5586034903003141c0e00e00076003000034900952040b5010034003d80f0f01321180a1401203050400c5a0501003079159140810009006002e030000005030124640d4034a0b00030840850041d602003042c46414044c850b07104680f00c4a2000454003800080c406009000700d5100079414601d107400058a2440d680380c2032076510b1034109485010405802c0800a912505c4400c080001d11406000000000c4550821301030307035002c1d01c1034030700001d0300010502850307032942ca0240880e031070140d00d03041c48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 720416241 1250 720414991 720414997
    0x305030705011104060c02100932010206070206040b0415051519060e040b04110f041703091f03091403040303021513030c11060307050304110109030809130b0a03030e01091e0b 77
    0x502800f00400c80090b1401c08054ac5071914408201c80781810720b82e0841414030b40000500f411704540c0700204100245400242c819001a00410600c080d55140d140c100039850b04000070003801410481480701c401100c0c0c2004140240850b03032940b5203000c0344100e03d0218050320680d0300049200fa81031045081540c824042240c0140005c2000420980440c8982e84030401502040000250402400710803038a024848840180550318040d14003000403100148642208001c000880d00751018600075444401501c1e40007940820401110041c0d81d01c942092000390b0150003481c0c10b007200c504800381c0c4203115400380345038043d0003825502c046640390900e400840e108241c082c240485903035120050b40c85001660b076082c0e03403031426103000051804646c413014103210560341c0c03e200050054040c2c800344502500d078004031000b030005000151001d0980b03c1d40140b1000004000d1503440745403400101003c1e21070007070141d070303c4140c0310201c0b071801410303101400710240074000c0403209001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 720417491 1250 720416241 720416269
    0xf0d09090e19080301031505010b030406020928080c0306090706052b0b040b030307020901030b100509040f0b070503070507020d0227040209010f05032d06010305030705011104060c02 80
    0x4a810b0401c80000d550200509450b06a0780000040010000c04c103603c4200b5507802280102401154500100f01940b0701001c0c20041c451a0082601807040d151800f40001045000030007244245900d02e00000401140c05544124040c0c10240e41c3d0f030b424009070907801000e0131401407410504d4518121501e410100a0a07001800481420542881e18a201c00500450303840000c2144000d0100002c4038086500c2c68000e4200340b11000141e0b5804042504490308807000001a96402c1f000c905032181c1500166481240c0380b040c403033840a0008081d00592084101c02c0003916400c1c3c8c01d56060208551000001c1c40030030400c0014148082603044880c4003902c04142d00101900544903003500341e0b1044602001a0b042100f076240428181c0c0c01040b02c44178000c034450602002c291101c403903190780502c0103601d03214142e0071210003200003009a4aa8192078455850389801ca490b80d00440095801d5070822828881d502c00d107000f20b81c22108a500c07041b0100c206a4284a04440000b0f1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 720418741 1250 720417491 720417493
    0x509030a02040c0e090f0910060b032404060b03040b09060f041e0b0112030f0e36040311070f050906090a0e0138012715030501080f0d09090e 62
    0xc991300541c4c8440d048180200da000f4500001c620f040b01c0e0b0701e842c0110201c0d0b000c080f1811320804000344090601201e40282d501050b0344207440c0007041c18041c82004001d120f401901c2c201000500240d03500c0514043e9105110001d50b03501e42e071490b540d64400030b446042e14048146c0105001489600c140c10a48210f03e210a41170b0459881e46203440c04242c0c080713444003c00646080c20075a101429000340c6200741841c0b519250801d000c581d480c0700c641d03540005c0b40300f46550420500c0c86595507105520300c04030702210504d010f03c0e00414060108012440340d1281c808003041084041070020107540f806010311030180d03610803c1004581014060540b0f0369603a40e1600c40043c8207024899180742d910080780480441c90a20b0345248186483c060020501e045a41440360b03032168550840c1a070b00c0e128010903051100c001340d84441681d21524100944030406c4400a1705070f00214101c0d001c00b019101d104d01c1e150245a00e0b010840450000909815014004449507622000c607481c6010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 720419991 1250 720418741 720418757
    0xb1e0c010b0301020406030c081f05010c02190b040501081303050a080403230406020f01050c090d0507090c0e0a21020103020a031e1410060c0206031e0f09010b010509030a02040c 78
    0x100403d007280d00c0b40c2c0151000a4640c65009051a0003034001d0342c0003282e0309040c0d0b101d022110b200704000e2426000d142d0401124040c0e003825562803201030300c001c10420948141e041e40c1c401e611411944184180c5010540220004000810b03641d40062981c1e0140c4444d4038000c00c0600840e07004c007008204800340303e078205480c5007140e68001c00b520700c0c91111115954580c1890401791401200350f00030b400e030740c0c1030004100d1036a00380c405503101c421042d1480e40c4d2000301c0d8500320781060f01c0354124020a0703140020403c821540705034621440401580e22079496502d80d4003451410036102c0340000c4910303448440b02e0041d40319900810031440d052400141ea010800490380c00d0600030f0100914a0340c43c0c420f00300c920712640c460250040c45002c07580821502d00040030301b4a048101d0080c5c41010088002030340c1854100c0b66425400407908a4502da01d8840400107843c00306642480c06c5620b404e21701c0700300d5406a03088540400c0004c0080442c0350103a82000060401d0514100c00c02c001c0b8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 720421241 1250 720419991 720420011
    0x501030608120d0902270106080c2703010212100303030f020f160212070305100e010e06010303120b12100f0b01050405040e030d1d0105070903020109090c090f0902130b1e0c01 77
    0x20902c00841c0c400980c01c2c406d8075407400d000142008400f0700040d040038410130010b0504600c41000410908003210154000c22070700c00040d0084c041c01b210411840c607007400f0030102001c0d882e40801542d06c2520304000081c00004910201d0158071600d503041e8000700b00010004100441000c80e0710f200030300d000f1418282500042c200039140c1d10443c0d80c2e0b8020703c0307103a03e68030040c0201403008003050001c2201100c14003446a5504040c4800b405010001280c941c0d40c0b461900402c3e00800054494020700345800070301907039070072240c0700840f01902e0402c0e084c0c01103055000d04180e071541692070760b007002d04210801c40109220584d0400c036200c10050500b0141d464000c51000040c0c2c8664045440511040c2e2825240c00038000b00403c0101d03001400103030b80100040050359440b0030001210420300c1425103450b9401c0d0000d03816110300800c0040d1881c2903400034068051a1908030b0f441580e50000315600e4016900e803403c041d220202880000822803003d04200c180300c0b00085101510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 720422491 1250 720421241 720421279
    0x60a090606180b03040b040b091032070509060a23070b0c04060c0b040204091b2916050a0c0308130501020a030c060b0a0515040501030608120d0902 65
    0x1070381c05180070520500000142c0488501c019008050b620ba200d855450940c1d110f045449008000a141012100109001480401107079101721b200305010807260a401e451190201524842d00c401000d0358822007982d0300c400b00c080b07402580152074050800860100704100350b00300e03032100d80800c88519000340c0452001540c03000190303160340169507182100d046c034655044008061180f490700c1000104201e56102a1007594240c1113010341c2c1064440c2c0c40001c0141008000c0640b00030a003030380e603580615226200340210b401c60b0203a03520f802210480c00310040014129400c0b107040601a05000740030000044254034807920640d48285095619101c80444542050390b020b880030804084c803019607203140380a03010074001403005044d0740c9e400621100e03030507500610345604c0f80c415007040e407030303881c501c3c00545030080c52062242c3e0f13507450b5a285600644141400242414400648103101042611f0b131a850414568907203001404a000502685d21040344c0000340700c8008011307801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 720423741 1250 720422491 720422501
    0x515070225091104030f1e050a15060f0e06060a030e0f0a020306130b151c030804050111030c1b071d0609060f0604090e010e03031e0a140a0203060a09 66
    0xa00d500441602818502d0782c0049a01114001a801200300410300216070403012211080364410300c0d00d0f000e0704041c82d41085ca2603618400078018070910352210100310b542610402c00618a180400040e036031075800031840c44161140100c2d180f01003001c5099410031f1401044201e0540c1408991004000141c42c50019111211f44260b00120050800c518041c07140c2500901b1190020b21013034129101c48001e003c010709280d005034a002e9103000d17241c841d066220714508044042921100e0581030203031009038121380807034041d4a8000f4801b0034042e1501580c0c0200611054507041544c10b20043e200401401c480841602c00e61400180003007611108029002c1140003c030f0310340c204001400900c0b400075044a103d200408084442910342c40155411101003520225080c54a94111401000791020301c1540b8000003003000b11b0011410403d20400c0c2c900080c2d480c841e51544001001c49049020340ca0603c1d000c403010404210b400d80245803c40001414074140b2070313a820840c0104c034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 720424991 1250 720423741 720423793
    0xb09040507030c0e060f04240605040807120506040f030903170406020c04090503090f010e0a081f0c080708040201110d1d0609030303060d15020d02121305150702 71
    0x1d403240c803050040284840000c030041c040c4e01c1c4041c201e4100b10f400100385c0e0041001303d074002c0d981c0c1d401c01c8010b117041d20300c12003a441035a010b021065840e000014410380c0300b4001e00c221840341c0400006c0b0130480c1c1c084d0101e20b030342010141417580c0710b035504c110244841140a404001140c0c0c00800800c1c3d000c40f10f4610440c00250140e070321440d2400182c1001c006669080c03042c0d1a01c0030000c0850300210882d0704146040701e103c03466502d05001a01c455441c00c02240c0c000ba040400070a0208002070003001c1c8802c02908000300c2007030642e51031b00b07984000840d0070028066202060446010340703011a0400e105040c01d900f40d5a482110b81d141001c80000000081c9503403c003a5101c900341c94082c10b4030078042d5030003850100050042a9648009480a8051090400c038201481400d03200f40b0380030401030200b95500c0d0b92000e5038801030740281c0c00d00c003546c040e10703004580040b281c0c444014141d5031040180c94080c4460b6210110807074020080015400740071a42d028040c41c03444000095 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 720426241 1250 720424991 720424993
    0xc0408060a05070f020f120c010e0102070807050c190e0402040f02070b1f030b0c09030a02030a050102030610170a0b13090b0910020a050d0207030207030c080303060405150d060f0b090405 82
    0x181c50f10f980018091484184801d09540000e00903440080700070a9030746400e000302030142d80d6012400d50003801400c1030041c55546510100d545010418801c0041150600480444045801103810006105065544ca1032810700d001000c0001e00c0c032084d0080c1e407041c00100009103212007003003400c0582e0b0140c08202c400c42c403140200030b5039040000120346030a0012280d0b440c85810344e13548240e2040080c042e4180420081401e2189a508124002d155a4041d069449004640c87e025021750810f54a09100349003194a142c4a40d03c11101d0300e10140750808040c07445d40f00c0b05101002860b0f1010104d410504411881894660900448048910500030f001d070034a0311550f040d0a01140e4110003440a0042090f05013a075800003d45201c0b0186e80001a41c4001900d4140c0c034001c100e0348002d0074030500880000d04260080301661154006885c14046995000141c4100b00c0300c25800560100c1024915808100075a0152049000f408400512103d800c1d0008104010486046540e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 720427491 1250 720426241 720426251
    0xe07030b010e1902210411150d0b010c020f06030603010f060b0d1107230304050a0b0301170d120b06040e250e0306010b03040f1203060812040315050c0408060a 70
    0x50f04950415940c1c108868082c114144071558079460b68101400588206014040d00480d091159002e900e50304c3c180000c189440303030324000c0d449a4071508182810340b125460131404185039400b50600f1751100d60b004003036100e040c02c5502000015000030300565027666030303102e19000500c0d9031303c0384001a00000754402d489010b14ac0b00f4030169075407202c05540c000b00038440c00000a0710171581c220707044600c54240c2da88800011003980f55004951109620080d48540000e640d1440c900946c142e4114175445009600d0720141ea56072000c902c01808000341e16116488411038507076000740c4840c03000420061805030343c1c0ea064802c1401c1920021400c02c00080d0007049400b0f000707046150442c983c1013206070f03c80c2441c0040d0300d40c50144200346014a000001030100580c403a420b001650b88190190500d5180000c020000c04050186103203a210301c51441010f8080c0030240c0b4101c0340d010141e440480c3c0d011140101410020304848031051301400b020400140030300c203040c4509020300b40090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 720428741 1250 720427491 720427501
    0x4091b080c03010e0106291e07060605030309030607030b12100203090c0a23010c0605100503060606040b1e090603010b0901031407020a0605090f070608010906091b030e07030b010e 79
    0x10031202d002c030000c4050382c50201b0401c04c00040000000540d43d00e550500c00082200701152401d2140b4141a1a1186c0c140041007040c00250b01604599010320b030104201a215018180d483c03240741c03141c0307515a11000004400324400c3e04001a07084010b03061720310b0108080741448c9040104002040703100d80102c200043c061041140d0040440100d40d4154094544000d1098940310318400340c500340c4406186010326401740081d403c0c50755110104218901c2d12480c200303039000079030164520a01400340450440e16000c820303502940c8282886620f4010b40c00c1c20390850440181f079200c2d140c0030a0102c05110380e5010043c0d8028400c24041c7c035034a110300030004040f6084003140c41c50b00c00000d0103100b4a2680001ca01200d03d6000e07000045a4540003a013514010b40100b00038400e07c90020045581355204900a040b00c04185052040303903214100340068402c44407248141c105101115130a80d44030f50022607004034160159000e06850f40c440744060142600101d98004903681400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 720429991 1250 720428741 720428743
    0x2319022b170f0a050c030f03041101080912041e09141609060905010e01030609020a11100605012709051315110418060b0304050f072304091b080c03 65
    0x144800103030960710709018032508441c0740c0289650300b810800c1c0440c007000c1d203403400c0081347d030440c1614032807a84070700e0580b41a1038018500e803c42c2c0e00180f802008100810b070006a10844040d5031040d4030f0400c0d083c0a0240c40c903001c0080c00c0340050101030307000039422030780b0710861103d803a00c281c4e0952145080e5041c2481c130703482c1c4070f068ac0400101d80c4040100d0b562140411043c4e4000f4070b0690303141400040120080c04044d00000f00103071000a5a0b00043d81041416003101a900c058030b546000c01c1e9443c4c000c407400d62260601044c034610080f00c002c1c0e069024002c00d1440304840c40360b00d0fa2165480003c45604494198030620106543c0c1c3c01c0c000520004110b1162403607081c0311042d68811008441c1c0190320421030b10354455a08081c08150680040d03001c1c090300760055441c0d1500e4140303d0350f04e5459003901c100324010f501c00482d5100703020703488010750a030f4000d0358480100c6040c188001030082070f10580312403120900d00e000500700c200501008050000c0108004610030b0105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 720431241 1250 720429991 720430013
    0x30507080a0e0102061509043801150503040f0b070513030309030b010b1801141c2003040308010608070309020409030c05060c160204020c0a02100c2319022b 69
    0x4102246c00340c54581030307071358a6080303195202d40e114400762980320206200013001c880c2050710a4026000301000340d1003102c00c0848c00e04949003400c03a141c039400800350139030780b512050303401801e030380250030350710340410424000c0c0c5403c110340f85411458410400089140007400fa0011000139250440c100107218804001c94050000004001d1804081d8034400a10713464540909050011005140c182c0302441801e0b600407030f000020801d000392030100707200010500d03080c1e84c00c000803412a070784102c4d88585054078800d41c0e0580321000b9603401c1443c03e4502401c0181003504154881002c0001030311503011345c0d00352034460f07101e0701c8185981c0e2130700909261000300086d0341d004052014441080040004103411601501c00580d07030043b40d1151804c0043c6c501d00a904803d844403458420383d0b2224202994600400152a501c0140d0602414008030400b85150940c000e00c000204c0191900003010070700d2000300320008150411403401d5541c0c0720038040c0100210f028000c041481001d03200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 720432491 1250 720431241 720431251
    0x11060a090f080a150e1c0e030d0e090106020a03050a080408040f1520191a0702030a0906020a0c032301180212070e0c0a1403010b0903010b0103050f0112030507080a0e010206 76
    0x1c14024005160345d96a41c1300d2103615003042810f0003040f04404e42d0300400040040340005415107a800c985003001030070328101c540040303001c0c4032528000034140784049071164441c0d40c950f444a14088016a0844620501620540300e000d010000000c40c2d8a01c03c056000a1100340e80c42c1c01030350b00c1e06202625440422010501c2900710780001c2c0b0302680040303401c114810040c1c0301c1e801c40144a0030903200c0342e008100519000300c030340004c4c40306c02e83e000006420302d40d1041c1d90313109072280c84440403070316034601482c0201840944003081c00060200584404280c1481c0e203203203a9042d15507103c13800e480f40140400c118801407001c240960a000020302105a20b003001000c155245c0b01c142d40303035590001d120050107040850068403023841585c5001e804500301c405a5100e5071031300c2c02c1c500b01d80e12881c800c40c46503282c018900e800e54041d0143c3c5224100c0c841c00000960319005100014041c2e180b0201c0030004100101c00020b042d0784060000c0141a9660425002141d00068a451000b0f05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 720433741 1250 720432491 720432533
    0x6120510051c020a030c05130c0801050105030c070c030615050312040902031008070b0d1b0903030f0908070311040e190305071703070810090911060a090f080a 70
    0x40021920a0000d02012204180c4a40c2408014140da0328002a21448020f42c08580f583c000000c1c01742c41c10000e0203076081146c20401940911060404403040c8490324408079060708010812980076501559001c80c49911007403900c40c8983d600071000c0445c0e00100c0305c55a907020b80c0b241c403610b100e070b814010742419001040103d401d0714400303407103020340d100705800f80b90000b0001c1c00103501000034000410107101203901103900c40300d1502c51600821900507146151038000c4107800011a900e0300048983d44500d55028115141194030100203214202400040c2c100001c20840420154001b1405403540b0012190514100001c0d265080c160302c00e250700c5500503a40350030511085445550341030400c1551180c2d41c1c03801c2e00300804405c82d159a2410007004010140350002c0c2d4243c40740311001e8506c00c00c44e89179030303981c41151a02c1c01d0150011444600055043c20711400400078603801d41880d03d40030f90780b03080711f84000341c003034124098640140200c8000c105080b030500c195042c0340c031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 720434991 1250 720433741 720433751
    0xe1b030102270a0b04060305090118020f2103120a0e0303040302070611070b0a110601060f12090510020408100e0606010c1e060c0201090b180307080a05040f0f0612 72
    0x8101d034001d00104490255255500480c1c04507a0754a003203c07500146400d46141d500e03142e0f80d08003e0010101140c04625035400d0108605207070f1540403256090541c0202480d06003c022002c0c000320380f0014240e03448030303d1005c94075880365400b000545180030315115050042d2900351483d0069038001e403609009031b8810f00c18000001e80204900055404903d030101d0400324910f117080c03900d120b540c840d49000e0b40000c0e691401e6a88901031110700041306003100d0040c1d9035640104c90491492422100240d01c800a41c018041f8940294a800e03002e54203d80c405014004050102da00c558000c0c49642d000252203032181107203001c3c041c0d0440024015000354605400041d18510030380742d000780210085440103007001c000d0b42e0049041758100d141003004ca8000f0314064001c0002c3c08042d40c1c0d1240500021305042c401b0310b6584a81d0825501135402d01788203a448030340c1030b00031000702e00900005120110782d409110507801c000301060008440c1c480c0c900340000d0801d610001c213881c101c504003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 720436241 1250 720434991 720435007
    0x1e0b030f0d0503010b0d020910030203072007060c0602040e2503050c03070c080715060906120f02060a140c06010e010803180f040f0f090c0e040b0615040302040e1b030102 75
    0x21060340e04403034406203450b46d59400d00300050000c1c4102c0e0340c15548007501e041030500301d5906601841c4640d09a440c0c0c024111408205801b03c00e00e01e0351040038542c0304501c14480d0510540c0c491400602ca040007505090b201e04403449071100890700c030a002c40d289440301807800c0c00c0d04004650710030b05040801590400080c8448107201c0141a40240501040e071a0208038503081204c00f200c5c2c000400740b5000422100c0c003000380c5550712034010003034105500400c420403e04a00c0d80c1c180d03484030045501c2c00f1240e003440781d16001041d0100500151505902c503110312a0001c0c400304982d400a410b00d9814000440504074040c1c00c442d03419401030202c0b5040d61051203098140110483c1c0f9407a08502040025000e0704c24109688542401c00e2043d00015060340c0100d0050344c0300b0100007140a8a4400509156108880241040c12144082984bc1c180038600c4201c119000380003510303050b243d0b00400e0541c3c48030301442032290b00001505400762944c10f0310080324441240298900202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 720437491 1250 720436241 720436247
    0x9070206070c020a03062901050a1d031603030c02010207150c24020408010603120f0903110d0803090f01060b030106090314010f1d160308040e0702011e0b030f0d 71
    0x402007140d020700000603928810b42d40c1e680340d010000c2da0700003402c0c02020181c1001b0000000c440d401001c011a0302100c10102e0340c015000e4078005100c80d52404905480004d029500f0380c822405250075001c2d0301041420000c0c80868031003d9402502e0f0690568480e1000a00d4103045501c20800360501081140405a104803e0fa82c240d401c40c0101d0200020380410700c0b1090b0901a64013001840010005216807041d000001224014140d00d0b0b1814500202a200640510b28800000701410010700c000b41094000009043c3c000e0103204000d0400c0e99600390681c4151040032507170b4042c40320f460900009000312005850030f80310329419945007803005800c080c01808024803c1e15500500f8000b00780035440421100483d100600002c02c4084904071440040003580c1c3c1c00d400f8040c2e9a00004010304a000d00712940310f401103250600d00040c000c61002c000c1d0500b0215502c030101c0030740c907240d0960181d8058907400e000064601119003014905200043c000c04582c10000c8903028040d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 720438741 1250 720437491 720437503
    0x604050d030e01090f12140c030601060516120c060507020f06070c05011506051e04050303040311131d190f020d1704030b0601032301180f020d02090f090702 69
    0x54541000b1115a80300001611021225000400f1140c00d14100151407600445a030b01c040f07000b440c2040030100002c20791a2500c91074090b5603059841b1030010880e0b03504c00d034001c003c540762680701c0d680c650500340d4503000c4824103d1181c02c00240c4c20079804090015911509400659900042002507142a042900d03004010218010300a2000f107000078080290420f80d00c54070404004504280c41e440c0151080d0000014042010140a000d140300c0c41c081045600b81d40005000394106403556172998080b00c3d11200a40e040000f09501040085842c021204124058070041049001d4500d60a10f032079a07400030544294413440c09800403d140d0b2403622450754068411100c02170b40ca0030085060461081c1203000804009000803d100b01210540d0241c14240d03014007080020b088402404440114100e00e160444c100401150210301a8090555404100420a60800c0c0040f1040340c0110744450ba2054000031805058a4003c0d40ca4005039411500c189190034a0324000395912 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 720439991 1250 720438741 720438743
    0x7060f03020c0c1c02091e01050306071b030509030604051b010c0308010b03150303071101030c0c020303030a050601260118111801030f0f1509023912180604050d 71
    0x2c3c02000e10f548035075894404c0302d60440c4c3c000d048840f031070400c0d640640002d0080504810001c03003110011916190215502d4058803a6a4450040480b00f4005040c000042d40d003c030f0510400b00719420094030240034440c402c0d8000c40240c001040c0204c0d58061007600003245504120700444030000080d0890709060641e401000182d8881c1d850254018016120220081d8148004100c00042003807840e203460f010002a6402d0180340d84040c0e090790403000e0840c00961581003440052100c82240e0710441d4885414504851b004180340d20b0800e681c4040015201100c11620050201701241150494294041c1d00208031540304014909910b0140f00a0180901030340743e805a43c0340c1c403c1c0c0003140c2e0015125020000f072441c1e445480000c00400e90040038035010f01000040c100401e109541505942100c9500c40d00446031540e0048124884020381c2880c0359480364690080800441a19204507100c00b40d5400e03125049141c2d04540ca0012442180300700828000d646500031102d900c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 720441241 1250 720439991 720439999
    0x3030207050a0501060b0d0e0706122c0a170f0f0f0403061a0108071e0f020a08040e06010809010b130b27190203060a0608091005010807060f03020c0c 66
    0x503505494010304004111a01400075820114007140a401d00d90040a510501103402c1000080c003882d03682e280c04a5100700c0022440701d1440503001d80854000d81002400000d0003e142a8091581e031034a10703003450394040320f9100f29021303010881d40003003080c40e070380c8104410350030000010042012403003880310354a941d80010804900846080d8140c4028590121080c4031003144ca804145030a802004002d00042d40000805c20041c003d104c07540032110208400152690000015141136520400c110111700c5864804008242079601410160030301c1d921012007400c2c010001400544003400b500c1d0310744d02d400c0b40184107548417900d14026503aa080040343c140d004000140700c0f1203601950783d580480010101800c040782042c028031030160018044521a1405034003000ca0008a440907044804014180120b901502c0599880201c2d0340480310403490400c0c082d01620400e070f0260909038000c040501c50650040010844094903240c21404e08001c2003145581d00c03000f0500fa802 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 720442491 1250 720441241 720441247
    0x216061b020c0f0603061005041a07030905090f010b210a090309080d05030114010309020303070311010609090510053313020c1b040605061215030a0218060d1e050708010b0d030302 79
    0x181f5005100b030f24014040c6107103900c2c0b187c0140298408030703401280c0440005681003808109440c240b50402d004449948804e18030340e003015050183e41d4001c1408000103480e450407401c083d01c02007d090712070600d80c400450094004d1134064400402030b000201c04c1e801480340188c0c8185e001007034a0454401e161210801600000141c5c020003100b480603405001c0080e000b0b060581000d602440034480ac0700030810107589140c114112404014002c00030b4102d80c041c42000380c81c80d00181d8102d03440b10000c0010700e0900705950761038007199040ba5040c8a012040c04041c1c0350040000d0300070f84031322106610304041c01c030011380c60301d6441d80d001c0075480c07008580710030070386039070340a400600000b80107942e68030f03581d4801c480082c40c00c90340800040c004410301e202500303000c204c5001d074981c0135011041a40c01c00b010001d200d04020b180d5504600031044000c0841c00104403d0080c4401310004d04200c0f50a080c007604102964100104c941c0c1001a009405d882d04681c0208041c3c0615005031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 720443741 1250 720442491 720442519
    0x30304060f0b06040e071d01050403030503151c030e030109080919090203100f0807080c060d0b040218090901060e07050a090902131502060c09040216061b020c0f060306 74
    0x9102124403540c0001000c1000304040d55141c0c0d170540500c1d280c0c3c494140c1120003c2d0f0260194a00d404c280d400610144002c00000f4020000b0755004040045032140416040d400308501e400b400b504a079020b00604000700906400406c0300600e103100750300a0202c040c440e00c8805c0b4602c81c4c0e17400e4078000c40300358043c8201c0c141c0c8444030740003070015008251740d00d0520955044c0c2c443c1c07040c00360b03212004040c0400113801c280001e008040f42c2091014000c440170040800c042900070101d08130748903403108038500403580d55200a250015a11300800d03c100c1a06060042104000f0407403491603240c000e051000002203c400350303000f02e46162441d0740d126042c8080b10781390815030040050303a001099800d42c982c8841044016554101d031100c2100041d5001280d4403003050724618141e10b810400b07c0c0380c5091640041801c240d10300365400940604c0d503502400c8070040400148400f110313000b1200e051f91b061051400341042140d6031144406c12000040300c40c80301420980c450414000c00e10 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 720444991 1250 720443741 720443771
    0xd08070317180c0d020a090b0604090c02070306050a020c12031806040c050f010221251109060307260703050703030804030f030c0503040f02030106210605011703030406 74
    0x19050021110840c00781c142000c03820560145680c41040601601d050f800c054207010001c034a00c0c5800908070860689803103844030044c03202c48200c58100d001004045503000343c0e03000e441d40840301c9a000b03220b50317442c60410704111000a0310749241303180108508428002d00040c00081da9412202c4680d498030740c0362400c0c081e1400e40e41d1b02c0c0301c640075203008c00c424084420844400c8950544400101c84440300049072144050300385001e04c890100900b55000c1b40c0400541303200c07e60314900311003410100711088612500351303100b00c5401e02e40180ca504c2d141021141560840819001014018286070307000c1d0301132464084007090422040014850580f041200c4801580c1060680d501c0035205d003001090054101c13015804141440c3c1d054800512911544020720b0050b90350038110f407035a50700c03040120001d140680e4999207401010030142800f558105a036440810b46a2102d1050710b0a4815200d050780a200c02c00084512011105001300480303a020790310003000907030121000c0400c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 720446241 1250 720444991 720445007
    0xb030105010509010e0a1a0d0b091e10091a040c0306120b0c04170304030b09060f0f04051c03150b03060f0105070c030b01060c020301050603060601050412050304080d2601050d080703 80
    0x3210440001001543c001c84039001002460007230300040c0301041c51041840200c040a4502c040041d802e0300c5002c1800c035405161940001e5a002c1e14400385903120004001c0e52100d955055181022018002e580d1038280315030b001d003000300c0c00c051049a2401e003828111010080000e0058070505000560b5441d03400b045901820320900042c1c1683c4280700d1071b541c1c94006000031500c3d2440310003c1200c107580024054400d1004411311926a03030b07110040c0c00c2c90b0a01400031501c9100b0301504101742d0f42c04412a01212409650004d41505048a0b4407290440d80e0f1080150341c8041003440307440d0f21403240d014018142030912039940c4103d4030f002031800c0c0030360340080c0080c00f1040002c18895032110420050764000c800a20168440c44101a26203005580c01408182d08000411072080b800000b151224026810341e0300300b80c0d0f202042410401c020f4a0040000c01c0302c00e0302c04010722811030005041214941d0000c0d203605240c0419401d0490309006007005001007402c0041520074070700c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 720447491 1250 720446241 720446249
    0xc1d0d02150a02010603080a0503190204030c090207060e010614101d0d020109030c08160b1201030215070c0b0702030d02061b130302031605030d0314040b090a0b010b040608010b030105010509010e0a 87
    0x700c42c0d0303a0300000c80010b000e40c20075180d01ca02e040100c0bd418124204c0360082d1004e990300b10301d101000c13600e0a00410002d512900013120100c2c0c560102c041d80000c2849a10000c0000c10003509112181074100205074402d00c000c0340c14420500d035012000019401c0d581c0d1010f1080e030b41614140504d00042c1c5400b4880d40c80141078020800300490707072600101e10510900000e400103164141ca50710580c45a024000000406004400040000d4500750000c40c000c1c3ca0300300c6d181454000a42c072152501d00f019005551300c50700000304c8004509042149000114161001e04864200407808008941114019007486c08020490001001c0b01c0300150340110b50040803181c02e05004820016031411a1149034464065215440c1c4498021301030305980c2e4100c01034520310303580c0316074030340c440950007a1200e485445010055400170b200d84011601a100c200c40c8980ca4500d0000700800c0d0903816000003010207410f000400c4a070b40c100c401d983c0c00b00070900b48018003108200126039481c09582c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 720448741 1250 720447491 720447503
    0x40504051b0705010204060201111c09020111010f020301081b0916200a110910030b1005030109031d03070509070804050c0603070906110a030c14100c1d0d02150a02010603 75
    0x1400b03a041180550007041165603540007400303603054000f82402c10307000e099001250400001c00c520050303091580701c1c010103441414071521081c030a11540c1e08403030000202014241c3d0010041c0002c00e801c014408021507503d9071800c80c0600d2a002c9228400003901003401108050f030742416150051070700320990850350942a140c0d50003020499070f02c04031104180c1d140c10051103410441c2c1031100354140b1684030340c0a0318021501d942e03640741d55840c00800e600d91245814001169030b0354203004102c0c01d28080c1d0389031014540c00c2c40319440c80304805400d9602c40d07809014100050713203502d2203035544982d090400d510301d0b940714103185060841141c122a44064004104208075400c900c00030240c2c0c0555a07103614010f003000c8060740d160390045c5c0180206102e504c0140014000c148042c000c1c50031202540c8017a20700110f0b0a0541d18440303c2400841e444c2c1c2c26082d0b010120f10800d50b0041ca040380d004c001e428168012071a042c956001804030743c80009081001c447c001d401c66401554889 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 720449991 1250 720448741 720448747
    0x6121504050f042901050d03030e0d23131502010f110301180501080a06090c080a111f0c41071e15030b0603130203070614040504051b 59
    0x92030420000310101d0f0100c41e40300321211610340a04010754000c065200d00d0500d02d00c5a420102000300d1a29800c604a0405855443d0010f41030320900040c0504802601c406401806880d2140d41903130402d100064034585c1407084126134039140c00030200711400098030100009044504034054503414926168840c2042210180d1952410082d8100d49d6400c4010f001c102c035076070060041e10800e20400d0040d51103086614003041e101d6009a021600c01c5091140f2103541c1c0c0707045030030040c60b51802c0e41c0600210100c49001d0070401c0024104075150443c445401e00c3c0c1a0001e415106c4a10014040d00251424035816880310341c040804030059100300807189054010410881d03240b00340391070450161202c00924016405030640200051403419210315041c403004c40d00501c205404602055102d00c0c10100c12384511000354001c22010084550000c201e00515103890703081c0d40b014003081010b0f00e1a9803a041ca9006031410703100c080740c020600f03407980b841f140d942035000140c54104001c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 720451241 1250 720449991 720450001
    0x3020a140a0806030c01030b1509011e0203130911070b091204170f060105010c080c070939050d05151002060106020c030d0807210c0908070b090612150405 68
    0x882c400c00e100302e504400301e903140d01c010700045098a0000c10b820f6009440040c240c210031503820090405d0100c10301d00100704054908698142440b0009082c0240e000010a20440202410981c000d003041c0c041c00c0c00101d000400c5071319648609000070340f000307000501145064400f40500c0c461500c50034800361b207603a1600081c2d090191108007900c214842c4e4440d01a07034090100d9014104d42c0d05845007110a108d907200c50341c09511425807040f9600a001c400704e540420361142d49071f0f0041200f21010a5141b110000c44034401d0310703100080c0046561342e4000c20035408000c0300c040740074818000c03449813140c4034000441d54101c9442540490788422000150340d002400703d040b982c0d19401c8039407404849040c5500e0b082844a00400038480b1400074045c03e000d248147e0000c280915041400180c091040c01200c0c2d00ca80904000340b250708040180180c20080807000e0403070501c40a242210610002e50503215100032043c0300607881d80000c0c1c1070026218045045540a0020300842c80c00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 720452491 1250 720451241 720451247
    0x331104090501090e0d050a12050711062809020103020f0a08190908070303020c0a05070b04290405011422150c0b012115021b12090103020a140a 63
    0x900409805a01c0c0000010b00081180514004000100b01500d248040352400325038a030700c100c8422060050280210144801d40c2c41118820b0919642c4c908103500780c4103411b41042806000d4000256011248a803000303801d00182c00102c84034840007812440520060740a07001d80301e042810140042244003950340c0020103a846113901307107100e803050145101a5800c9844200c0c0180801c1814840500024003c1d402000e040711034030119154801c41c0c0c2d4456140c46816000085c07a61004a030030840e01400c0c0041d10004424900803000c240342c0910b20384580e009621480f81000b51000c80c0d00203002c5040211030851084440c1040c2e44500c00440c1e010030002441a1400b9059441d0803c000ea4402d5000000044d80040425501c1c2d1804c004101d034450301c9240100440080810f59002074405105a00d000448410160701c51012440410002e402c1808403580c60300a440281304500c0030030304031490395030309081c0142c440301c41307003012203440360007003e942400240099070360707041c0d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 720453741 1250 720452491 720452497
    0xd0e03031302040b010c050c060304060b0d060c0e1c080a05040f0f15093204140603010b0303040305030403171c0b0424120807050316050d020a3311 65
    0x3009031420700c030361841e81300111640100002c004e0203a81090380350b0b5030985020401503810074021900802c0c54400312001882624040030100c2e04140c0d1a40c85c511480d800c50003180760f2507400c8904500c0566404108000740080c164000c144010006290082600610903107000e4040340740001a115101e2103d206150410700030701440102440c0c0d2250200c3c4260390035021f1f200c24030348030007082181c0e01255418020210103200315158011800d0b00c0340d15a880342160031501c6c44064000d5003002000d00d82158000c401c4580070b5042000144081040001250100c940c8002144c0c00e80e08203007140c03446405504500203651680440b02009040180c12a0440c81e03000c90b4208201e8005045484e01010105084155010240f50801c281c264a40008440f54095191035107054039558503282958494061000d84129410665080c03010401156207008400d000811441d00d0a484280c000c03000074110308030424284814503008882a610024080240581804419240c141080041e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 720454991 1250 720453741 720453743
    0xc070606090c0e010509150307170105040506100525031d0108040c090f0b0409051e0303060102072c09030a020c011701031101170403030501180e070b0d0e030313 71
    0x3400c00402240e8039507103108491010301161100d40540c00400010342d00c0c0e8000a51042e884518062980c2403196484021881010665296040b121020400aa007880103030401c43c01a440c1404002e040e0715852601c00c501021402c01c25250407002e9020b4000303003050100c007411202d0b100441c0c410503411044900c501e400b02c100d007840600010b4011654042c0498003c0c00e250841070080002410680c008085551344010100b02a0074000200f000c0e02e8812801704d030558400841a0740c0d4820700d91002d034041100101440c61801c102c40002e64500c0540100c40c606251000f20240c901c000090702c04c00b01c3c5044414113141c1c0307041801e1a4403904040c0044000d400f40790701da000150700c5401106801550b24002420903421501e4000300f10030b104e02e4503070610616054011040040f00c560501c5180700395800325166041c0003450310450080d54904180a04021101803640400310300c1c1416200e1614405856002c0d0707181c944090702021007008898040002404203c0395a1010300403c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 720456241 1250 720454991 720455003
    0x7080d02013602040c02030c1b0108010b03070c0206030a06120501090b22060b030120040f0b031302010c110a0801060302030706080103081204021f05120609091002210c07 75
    0x38603520b801241d40c0c00382100032514540b1000c1d030b00c03030061400c0e40c4801750300031052049a08011903800c000e4a0721f0340d02c1c902c0c4d9410f0803414400b044550781c441c28603405407420b1405281036040c40300025080702103036032000b445020080000f03080c1b00003c1c1d01040c014010070131144410300140c10440d009000780c030003d540c00b6140e10700251780c003c5880c031415600480c404082c4406d0030b035a03d0b1080105000300c642a0716540300d020a1040120f40b0080c0d5503140404450580c0d514135100c010041c60b5071545c040c29102c14140300f00b00030250314403008a50f4076028200480a0a9240703080f15001c520f400c030241e4801300a41020620503015072010b0300344c034425000c030784030740d0703152074040d1040300c42403100a1029808200440411292203a80c60704144058252480c00c580192409022402980c1c400c00080f004201c84075a2a0003440c0b46030404016141d003505824a13418564450201004000100e6000140000400c1c249010f0000741841c5421122403400e080c07440111580c0221020f49030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 720457491 1250 720456241 720456281
    0x9031d0103021c020c0a020a06080f070801030f0609020f0603100504110c2a13020a02210306040b0f0904030203040509090105010e16050d050c0c10060e0a09020307080d0201 76
    0x3035001c1c0c821215007a000d0011075070300c0c080461004000c2c0d0701540c140c1d0928054901c2100040c1c54207081d00d00a0816a1200e0b070342403030305c01d000c00303403844006200004000c0105c1c01000031403411804d0411083d04598041082486400411707200460107022540100340041044020080c09440b0b400740d030401c81b014000d07a1000c6400c00b0309402007001c08007294001c825400c442000c1c0344481c82030340060b0307d50103016103042000101e800110500040c013031900002e080401ca5814401105c4c00200080801c864508103154042e181c04000c00381c03401aaa9092000110b5a82c403401c0c40540c00d004000b0006490b003454005e440e0703000b620441d07014450781c40110b03002d902d06001c0d05041e100e03401d4410303100341d403054440d600380e0824110190910104010b55800302002d4080c56219030194015680da407a00c5480c120702d8941403446076040d40345800030034040a0014100d058010a00f0f10002c512901d4a0002030300306503440c0e21a050034400e017150240c00607010f40007001c3c00c0984c40e40f00e8003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 720458741 1250 720457491 720457547
    0x609051203130b03090703062307170c030603120708040e34030216140c19050f21010b041811010c061b111c080a0c0507060903 56
    0x5902c0c0103402424642000051080c0880341e803100c09550f11034050700c1110840c964035100c034001c03a1400c000c0510881e40382c540505030144140a0160880250301d000c04010710010520307900b504015140c410a010000003040c4107550812050100c0c850851270076a8410301407410307810700d9005105005800c0e000c4400a40e4101605400d0043e01c1c06011652021a10140010a0504200f8142c0b000e05609002002c440c0742c1c3c0350448000640f05000d419080d0003a622000d1030849031207010b0740300e40444800006500600040c20302120010303203940b01e0340001ca00000b075540c1c024200c0707604041c0c81c9201c0002150015048030500540684080003245413603040300c011816000c030060030a00b4007100d180c40c05d5114001030301c0d4440c0110000610300c412120ba2031141d000e43c44004002807030b10040070189640900c0800c50b0590002c0c0e079041c0c0480c00034005018000003d107200d00103659481409421802003003250b02641d4000d0f4204020b02c1e0514000e042c8038440d40091104041d01d0398046 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 720459991 1250 720458741 720458743
    0xf0d0315090501060c0f020613171507020c0108131b0603050702121c0e061302010809070807050d1b09020318011424060a020a15200304050f0706090512 67
    0x40c3c1038501c1580c2d440c45c01440c5440d100020700326110101d030401402c0051600080f4583c80e1000a041c200c40060108031f4032411451500306000d9402c4404285007040c425015000114a6040c070030070b00b00b03d820741d0758090001200301984440941800342002e801003070207c441032904c09a51268508200d16155084103d0780d03503441c0e542d100c181140420449841c0d942015440804024615020402043d8600c8003801c08406803400c020310683d4503d4001150f80004000758000c0c1460020210645030542190f9103c0141c401c01c0c1c0224200c12400043c0310803007e070b40390704000c9504480e80f925076a4400100030740c0104c814801d010710b1100034984440040c09000c15003402c107504528503031541e400d100f030420741e2040b03060300405291741c41c03544644030314010700401c0300c0a8001d000348424500b4a110100746090510002c03514000c070790700c1d11026041c200c0a100582c16011501e9555516016203403d80c03032030224205118401001072000d40c40f101070010f4540a9440c24482510700000c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 720461241 1250 720459991 720460001
    0x71203050f03150a0e090c0d0c06031d0703050a030f02010921180308031b03010e0c090604030204140a061d1306020405130203060a0e010320030f0d031509 68
    0x400103501009103010054400001e150080c900d0324400080704001000101d1900b0554450900c0850200401c851040305224207840a0410f94a0300c4000d50180d032299024010350140307005055854503c03181c50b108181c55640001040760894604540700c0c1095070361188110800c400080709080c07200402031040c0150700101c2e42c01540401d54854809410342449a0320320700d0710800201d09048546640248441c10065004000c2e4940d00c3c1030001e041c05001c0403603001001c030408100300400c0b0940240410306d50003d152502c09807100c4042c0006002481107510180d8410708101040b4654020105c201c6d00900c2d0044040062a0303031481d90408242e400003240019000d2403000544000c0e500c90304000a511640005203055110000034111003103c81080700385650101c1004150700304032400313001414503250740f504a989941c0d6059a180384c580d920601c9070301c000070208415101000102d0b141c140081c141d498000300c0200c01002400c02c0000345148119200d400a01003541d8811 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 720462491 1250 720461241 720461243
    0x51b07051c0807020909100f0e1c0909020d09060905100f0c0f050d0f020c07061d100302160c1202040f0b01050702091009020f191812030c0b0a05090712 67
    0xc0e50400c3c0044c0c0800004100080015601c0d02440060030302540d020301c180440d0115150380068200400c0326000e14080114040e070060741c0908241c40c000981214055044825000003d03907a0b00505214102030811103000410076410040780c1400c10070042088141682240c1b401c20005400a4901069846840d698008291707040c0c00d102926116900415400600e410080360265498129004903030100103c4061600403035014801d041d48581c0000680e01051480310344281075100060320500b28886540915a001940c0c0c81000c003110406a0007a410030320140410750380300702d64800c003a11400704903c0b076031510300d06e40c80c9200b00381b203403400480e01a550301d400c000c40d590078004e1550019001c45809094a0720000e1083e40714001006003001c2c3c0016a81c480142303e61110f01c1d000c4002c490010322000c100707040d01c10381c03242d2190011100c0ca030720117880400717443c1400d603401100c404014041c601c000b403c101c0c00840f01e0b0001c9001c2d440c07a0045410b2240d9405415400003c0c0081c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 720463741 1250 720462491 720462503
    0xa030204030b0f04020f040c0c020604030f030f05030f0a1802030a0b0a0e01151202030f0105011e170a110a050901031a060603040b06210303091b040902150a051b07051c 74
    0x8031b184160704265010945109480c00d04e0740325001c84d071b000a04680c00c1917108494541e50340c1240b1080650180300c0f01041a45130401504508002e60190101030008187e84107151350360f2440ca414100c5003e4285906d074014040d180b10711461b0a001e40014000c86d55066850b0404044010341201446030541c1c1f400b000c240a1407403070500c0040404072030661400e83c2e1603c00c41c40c161105007020300c1454020700740c01000ca076100e080002c1032482002c0390751181d244c1e0200c02e0005d045100d00130415115080c3c0c00360301d8082041d2a0301c00108090700980250750455403010010040004820b00100d500c00341c25000f20a541d41c030010003010384011a001000118184c0216984d41803c0048000041b090000e49100007980c01030310340b81d03410403501c0705843c0d840b01020b25006852010b00c4610041c4c1510b051048030081d40101e04a40c044032000700341c940000401081c485d20400503200703106c0356103030707480e84035520441e00f00e6a51680e401110710841c2e0107070f043e4034400740c100035150310554015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 720464991 1250 720463741 720463759
    0x14040503062403030a0309031d01081504020409110705300c0709090f022d01050d27120206010e0a0207030e191707030320030c030a030204030b0f0402 66
    0x202e4480303140300264103a160982c504802c03010380d5040c400340c201d142c1295000110307054103040080181034065030405400848410201075170741e02030700e900e51180041100c440c414082c40b000c10002d12480d44040195844c1141e40c2400000e501c00404000b406a021160f50b181c140c100328200040180b02c03000e402121a10311850542d031070024012500903207040e503400b5941c0e0301d03640090380c0f442001214010104082d1800710b25004090f40c014905030405044d081201000035044440c0700101d00d81070013800f003022440c4c0d444582200d0702c15501034045c181c4a041d8041e40140c074103803141e4121400c04481c2d40d2404807502c00107072241207441a05020750551030360b000d208020350044205804208008a440e0441d4441d40b903100440248800c08617000380c07030004089450100c40302036500c503820024013080441d0713100d081608146505a06072103c15500c0e400c1920b1441000c4540e00c00707000101c0c03081c501c2901070340601b08603401040025099500c80c040c1c503a1003182254001d501c011a9 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 720466241 1250 720464991 720465001
    0x8012307051209070531060f300b040302060c0c06060f0414010303050306030d030209210a151a0f0307090c0507020d0f050c180a0b010c020d121404050306 68
    0x2c000210341200c105025900202d4544011506208500d02d141e40000118403001d943d10302d40c00701240f800f03400d0300c404000490502096240c0d00c0040d11415000c1e0421141620326035a14007504020f1554100803610540411710b00304680240880b401d03005170242100042440c40c0c42c50846101090040103042e040d81c42008100c0200080440c80760856941d8400a25285c01c5c0c0c2240e902950090b00c41503141c3c81c00c58101850194894842030816005000f18405502c0b1003003402045242c03445140151050801401c0c40d0241600010b4958615071800001c1c3d444140d020f03890034035800440704190200101480081101c9603105038066001c0c0764200306c40322159005080b40c9006140c00341ca031080c04c0d0000317026003500040640c1d050a55500440c01c210341002000c100500580d01c1c051051101a041c00244400504900e501a01c50f1440322039a803040d2895504150700038030b00c0c50f0746c1d0002e0511400848040d40312101181c03107841c05200b02303500c030344c03d840480358001c0041c0340541e19 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 720467491 1250 720466241 720466267
    0x506040b04140615030c03010204030c140402070506070e01080f1303031a13060504050106021204180b0423070504151d0301020705060f0f01150f0e06040801230705 72
    0x8000c1050781d84116994070b02d40845030038000d4034040c00464514809141c141c00c201810550800145486613204210400c00104c2c0740035444215101540c0402c103010400d00410083e226008008005005040c1080754103600718401c00c0400c0c40c2030780d81c0740c03072943d802c00c10810010040d59030714114a1000042d40000f8820742085111000f00c0e0560b0954500b01000b04400d104211101d2358040d86483d0180304509092050b18010300951000f030420701c1d0041c0d000c5a0ba8801c500072049108401d4202d03018600c2507410400d5842c0000d04208550782e82d01d8622010441d5842401640840c40000318001522407020348003541c25400200f104200d004905449480e00342c481c0c2c0a0344a17103200440d036107035000e00c090700c285402400684030318540301078001c4521030001c0410f100355040c1001444502000208120320403154206104114400001038a940480a00d13140d80b00c0e1000034003080c903400641050904010b900140240c0f1010605462400c0b00102c42034000100c00b489204120340c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 720468741 1250 720467491 720467513
    0x71403060a03062d06050d0f1406010b0c1908161412070519150e1608030a020c12030306010804150e010218040902130c032d0b03030304050604 63
    0x100042072400c03030303554030380c0ca000544003006a4141e0310302c1800340f0f010f01c81c603414800300311013a840b5004001480c100030000c0c1d250503c8840c0600501000c2243c101080003070031070200420168801c0702c082c1e40e920110071301d05034020b0b08041142e0180c40040f00c154290540039680540e444912141840e10006112203e040041c2060390320611010079018520014010f401034114000d241580d03804171420072605e0305800c050300d07054610760102e04c0c1000c510003040714030103482c202d007001c111001d0038240103203402102d021000d0100621000000c811100000400303001c902902690b40510100c010010000b4064510b281d07650410800100326600c0741e0040c950043c406c442181c02c054410841c0000c40d6044d82015500d82e500244801c040781d844000342280400444061041a125038007142042e2100e0762080141621041007904145c042d8000c002d42c040c050200c82c04420004000d54841ca96051184c0f42e014606000102d01d418088122841280c1040081449864607030707030b03414621 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 720469991 1250 720468741 720468751
    0x30315030319030f140a0203090601050907080622020a020d080c07030905120319030c020c0d050a030e03011118040c0c0209070e0612040f0b061002070501120204090207080403150203071403 83
    0x41e503541c0110001209417581500814000b000141c0300c0c03400400f80c034500f46040c0c10071441203401c801046a503a600c0081c4541c00501520300b2103015800901c120814480c0d0640143c50f00c1c0040340066441e0782c0041d4041c0ca486480d07803075602c1a2035203250302c2c402d441100400303030005014500034000c500f0802d10090001c0342e00c800300c1e45400400300341e10080c41c8003143c140c00000c0e00c0c1e40304c044ca144c2c0d04205580544100b2540300d007115020380d0f6010f41d0340300303984c100034140020a0b001101c01d960130351284180e4401200c0955451b102ea041c10b40842d8103640045200301e10300205400180e1040741c10400059000c0c01d40340302c03601c4200007641d4041032014034541c060ba0030004c04226508991515024038460442c0340c029491070310300a400d00b074005001d14002c0007a15919071100b0b900041c8001190070a08043c540206d540003140082e20403908107031185800000c14608200b0700500602c2201e005180c0141c500c2c1c400c0420805912041d01c1c02c1002030350000c0750303140b41081c5000643d040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 720471241 1250 720469991 720470021
    0x703060b0c1b0a0e07120b0109060e040c0c02091305010518031209030f040b090301051506041a07080408060f1506070201210501061e0c120e06040e010803031503031903 74
    0xd07907a01d0741200030a404486420018070740c002c3d1403600840e14040d500040e042420004842401c14000409902f40118501d100341d0316100030341c48190040340c002c0d4a051300034054014616042e01102ca540001440c00c032600d43c0f8150001d101610684030000c3c58000d00000395240240c5078a03c3c408912000e003105115001c204003034480d0209e40b000a1006100200c0d40d15140d922410805003114402410001202503800c4444c080d0750340c80045606490307104020b48078900000d00790480c24060f107600141946000580030903c040b001555520034480b4070100c020f2559041142c000c0f80e070b1003000e41a005041480000e005600440001000300b050002c4000f0004143d001c25055820a03441035010504903800320400034a906440d050680150a0500740c00c0c2c400c1d42c03200c855490724501c1000f0409801f030214180d980c0d440440307004100303450f06840740b0350b199040c07180c80c2d07801580c50240c4900c2208001c0c4250a011081d1194840e90b01c02020300d00c3c40c1c00f0429405001881201494 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 720472491 1250 720471241 720471259
    0x303011214010501180f020901080609090f060c300f2815052b23161a090103051b0a02030706050f0103150c020106030209010b030703060b0c1b 63
    0x8070100074400c080c024506912250400f69058000004450510310b40d40c2c00705004020280003a600902980e8010500383c5000f101355840e1015142000002208820301d80208800d100c1c40109803c0504101280d160300c3c00e42201d40d41e220190b140003040d0b60000c2580885001070301c440780c94100e1682c8250a01841d0561140c0c005640c0d42941a0009054036280da9040c400714100c5c11641010113482c050b00c45902d551809021070002401001c410020741c00d030344c2001d604015001007801000301500f040882c1c0c014010200b03d0b1524045418102c03020211340f000a4002001804d100c001510800510b15201c2440e0046000e450003c00340d00200315880c0b220040014104014001300d0140d0f40a0343c0c85800e13a151440c280e410141c002c64500359080300500116144628000040e02110400943d49508d0603042c0d001d041c10f5071019610031170400002422030000c000451040c80940c0d810440d03a615021006075a00031511101d01c564401d151540d044040e8980d600e100c1c4a004206e011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 720473741 1250 720472491 720472523
    0x3020717070b09010b03030306010e060c010f020c0f1002030f0406090f0804090c080603030421030e0306010303090314070f060513090e0102090111300d0501090b12060103020303030112 81
    0x40303500821088440c5a02c000030010648420300c500c12104008030007031842e6041030340000f0550300c43c02808a124084c00268449464001d600401d60301c10f0f010380554a8104182c0307101d0300c5034610040c1050728000d03a000502a148644200c83c42401074100f00d60494450f03844081c0103120554084801065544142000c03800100190005005e10000403c0090310320034018601a4003070071040c020390060005101d21103025441d92841000d42c0142d0040b00d00070306040301c10a0b60030b0a100d030503002c3c100010050550200071802924003d0380c5091150a202081e20303610080c030310a07042c60485400701444082d226100510306c0000112107822035036107500c0944110b444580109031710b0780d40028107035425600145070200d10214000a86036a200842c14088035181680c1d0340d02107141880321030180c08030354070103545907181231340020881c40d0f0712643c3c0d880050400c1503089219121201040e40342010015115041c0c07617010b800b450860b40380c841c1c1080048000703103084400d1703584c1038540c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 720474991 1250 720473741 720473783
    0x1030914031b15070f050f0f0706060509060d03030c05220510020714040c090e04061508070503100c05040509040c050a090212181c080105090a05040f03030207 70
    0x200034210380c5016540e0b40111500b121001e00d48140c65034015000050007041289003200860780c403803868249010000b1a03800102c54074401c11030500c205500200c1e2034602c1822000160030014440c00040007007584400c01c1000540f4110390190b40188042c00b4040080c4c8a80c0100380c0e0500c0c181421401c20441098070500c3c05000064160407540f041001c11607803802441d00703500305800340007070030080741003103641c0481035800c440c41402903417104114030000344034040b10002003a2a001011003824286002c6001e0b2000740b08015294030840c0c0c0215000c01e02180300c00032188010018410b00c41e0101c2030034040c0903c80745200c00e00c0703401e010000d55a104ca010580c8076038411010a00c0c0141040308000a500761078000301c1c2158414410101c61642041c0b441c0e400030500070503007038204508448146002201d1420301002401040b4120201d0703007000a0340c1c1a030303508032080d0180341d070b4080b0020201e0390111409001020000301000101c0d0199008290490044c418a40c21000c1c10f1001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 720476241 1250 720474991 720475013
    0x1a0103060521160e040b010509040b040b100e0c090f0103020a02030409051005040c0f080f0f13150e0a1406090606060f0f0a1e1403270f16090b010815010309 69
    0x201300c91202d200e0400081012074007400340500011154039500b4146070325103085001000708018181c041000c082081e0030071042d1418018001c40c1355016a51909070b60407101030f0841100203020b4000c5494083c40c560081c000e036240140c036580194201031820b05850b000c0c18000e400d080d80c1c60b00403003011800c0e032940d02a4560842c2103403981190141d0f00314004007285401400d04085900d00424050480b1076090155000080a0120506443c59080c041141d0514500c0103403040d1820180c005184800704141011501507a0302c04500a28200055294442195050030f190040d80000e142d070324029020348000e07007a0f05401424202c501e50b003048107601101d2060081911030343d0084004141042d14030306840149040e803414000420045c0940c0405054804046000341c50040d090340d0000c066100380460208603036140003412107194903102107018405180240700004a00c14105000c0e0030703010581a901c400855a644150b8007445074030f90a024105600c420184011a08500203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 720477491 1250 720476241 720476249
    0x406030809010f09150804020f1e030c010c0c2c100504050c07170c160308040e0106020f0c01140403050a210c050c0d020d02060408011a010306052116 66
    0x120307649100c84800034008a05604407801007010540c41481002c1c000d2883d98440031280c00c0c28902c03502c3d50320001301312031705940d1055007043c00d80001a0020714032460103c0c815105030180c0740c5452440004580b449040c60015145141d0008208049002c45050220442810707407107100701c90f0001c1c58092461820381d802000002c0c240020b02c4189028400d258200c44401c8030280707800300d141d0301c24190000540d04401d04650100d80d2100d00101400200b140550504d90030382c0058691511140310f4009004503820f081c480000455414000560844040ca03ca8001c2043e885240300450b404071a6410407a18108248400000110301708140b1111138030650484890590401454545e01642401301d000c02014503260f40224001092f2070a00760810703214000c0c19002030001c00c200b01905140250008030014001601c0d14040d8808104107041480042c09000301c6401103050b680b89004455005905402d40c240b031801200000c2d0080e00107006440a071150004100003031449980 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 720478741 1250 720477491 720477503
    0x305031305030105010f030f120e0d05150a020408070312170901020307021b100c020d1e060605040b0a050105030a0f020d0b0123040e04050102040e18010c022b090302040603 76
    0x201840079290038080c460141402c200401c0000b440c503150610044c41c11100580621049584040b1152282908a01c00c40e000f40419403554a546000c5550701b00c0700082c0b850701c3c00c0005c00308403074188078022507048901610040690381c0c11501c6000c9641c0202c4803a01c144580f0010004000001407240c0d8800d90f0940001030316450581d0b1b002c1d052028035411a03900b00304900303500b106907407000c009502c51f400750b180000300036010b4404108040306100002d404049800b0110009001214041941a110f00e009000e40c1d0b41d035a040c002501c0e600c1e404240d02c43c11800007485594822009141d00c03e502800c04036018005900040c00c90f80041d10100a164403403034002c8940d40c021300c882002c941d0400d807a100d4040500030b04d0000b07002c0c90007a14030340207900c03000c90244802501a540904a400c90840711800c01500c50981240e030042c01003401e50070070030100c030f4840c00450900303440030000c0c0c8685c1d180401c100740c0d034046050419010041c0005c5c0d00012016844a01c10700000c0c6200324 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 720479991 1250 720478741 720478777
    0xa0212063a0506100f09022b020a0914010804020f0d0b04032721050a0c180e190b060d4b060f06050909061909031704030504030503 58
    0x20074003e062080090841060300c807002001c00c501804401c0b880100c4410307010050300d4110351102c40f0801940382600905054044000380c0120100398012300c684185130b2111101250740d122000742070801e148116001c280760701d0000380503041141384901d0200008160490500d4244e40341c6110000c00d0764140d0002d903819601c481c11b8402c102803148606003003802410b007140b505a1042682450f0050840156840100c0ba020801c0c1002404585540140c030210301030b44a40b16444122810354642e800203042c091600380c0c4010100301c5048940380c4d20400006c89c1016200c031060300c10b0140c07074681c0240303000b03459101161002020a113080752455520300c6004000300000150074031100343d0703044801c1382101c0c0c2a003a01170520112040c1c0d481040403030f05215a00d0288020804d680c0b20980290303080040102c1703107030041840da119085880e00007002d9480ca0300e090080f03806c0418010042000540c040c1c8011921940c442e50051080c80d001d0700e81070302c9a4540e821908070036103e20200d9008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 720481241 1250 720479991 720479993
    0x5090109081e060c1314011e03050a0b06040501021e0f0307051605010e03060a0903050906070305070309140d0209060301090807080c0f1f05090c030d02150a0212063a 73
    0x9103c0d0940000140c26814100b036291007413586031010302d01c079500c0c0c4d01c00e49204460140e4000d0020f1060100c1448a4068981e1382000190250a084510300c8441d4500509950f241ca80709003910103403035040e401031140e901c1200d401d9505844814100380c0d1031181800384401d8100400084c5400e91061014280b9556006240380100c03000d41c0090341403204100003d40c090328002881544050300032070104100034241819200c80c49540c203c0354101500084420030f042d080301c003c0851a03c2540c40f20103156030b03500ea5440d41d490300c000c0035500c10718074201407001d40340c01e54005d40c028000400000340c2074413540e02c1c7e600707503401031740100c5502101150094040e90203001c00c40d0f040d80014080e180c0c000700c950200401e03500d00c207100d6400d03554403004101044810450643c10010250031548200100c60300a03654400020700c1d90b46003c00440010314001460098407010070b1022004d0310141c44501c100120710596104c0003121503c40350b000220310701b2002c072304401c0280c8220302001e0040c01d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 720482491 1250 720481241 720481243
    0x30103171819051801060e1c02100f0f08010806060d02030c0402030f0610031b110f0d231c11070807110103050609061f02030f04140316120305090109081e 68
    0x82e041d0481004c225000401509412400003e1402c0c0c00303c444044d058400c18025851080300c040281d0040e034540710b890600c0d41c104041070364441d866142ca6804c484149812103000c80240614141038020001150560922413048001c17944002c0640d551041c001000c40d049801c11030703c9425200710741040c44190b0400340e60459002180380380c18040da5540400c12041d0b4a201c0d5440010490200c030080d140701e0b021300c9030303414240f410001d40b1481d14140034010b0444203c2d4900d087d44000b03d24140c8802000c010880310b004c85d054843d103424040354269100208030041c1d682201340001c001d4040080d1090004001e500e1050b2540440c1c03d03c0381d4001000c903140140aa402640004c0070310070150f8881502e0b07000001c4095007100c120748869070490543c000c1c00d441d501c481001180210700301103205030400f04150154229000d10300101c03441c0c5031540c92482250460003d88114001180c45080101404041814030948050780e41c002e686c940035000000100b0341c844c0401d80c2c0650b40c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 720483741 1250 720482491 720482509
    0xf04092303041e03060b010f08041104020f0c060402010f020106060c021203040807060f0813020d06050402060f121e04080d0506041805010507142104050c0603092103010317181905 79
    0x6c20300c0d003841c00102103200900310b8400503001825064851407030504a0391160110fa001c4d4a1100500341c030f681c03482440507034400060728100d000c100c1d2801ca169240e032052140c24202c4030980d85049000d0b8294090000d41d20040e0407010441c00b08200c081004c003030800941d4002c100c2d9903152130302251032660081c1004406410031800c7c0f0804d66684000da0345100900910b2608000e0000b4151282d20000d401031150603140302c80302502140b0741e003000d00e003499014810700c401140b05441302d20122a11803d0603049500425213401440800401600c43e400703654001c0001e0400200b410202009680c40d03030f115001219182c2d1200c041000455000780d0001e03409486003002c50918a040440c05a0081c40f0040c1c2028600302000140900c03034200b00c0e4408501c009400035070340e810f1864003d034450101c8000410001c2d03400150180301c895881c21641285d03001189080000c846000054180d40490201601807a6240740c07284555142c5600c7c801007265078800d4503400e4980810310007800f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 720484991 1250 720483741 720483761
    0x8040f15050304152409050c0f030705031b0d02030109140402030d0c050304180213060c02031e0f010c1d0a0311011b0f0807020f04092303041e0306 65
    0x8201141101441e8225007601c0d00142d2145032600d118036107507443d80007442c1c0c0000d1000000d41405c894070b07042d886440d1800c15118000014070165460454540d0342d0b1091054054a01c94108001740045208401558100c00d601a000e1b1100582443d0381441381c1101c195045003a50000041040c0d58452280003004a00e07400051520714050300025100c0e1104190041030081d00c412440c204001802110b0103403181ea108402c480681c4240a8020b40003052104a410034030500414400d020b080300b015001d03402002051050442c030714058845414140a2650744216003c2d00b1030440280507010003164035541e541d565103103c80750300140511b941e0559000d03905108003840400c941942e03050200800b0700300240141c6540c442c5081410b03071803030007501e910000e00d0032000b040244001012040e000b10b40a82102c2c081c0b02c02c100484180ca03c000b0240303650b29040c00b800040f1240041d540d02c02080a90307041030790790310030186030740000071100d85080700d1000140104541480703030501e50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 720486241 1250 720484991 720485009
    0x3050105010216090507030f022205240d060909050a050c060705100c090308070b06041103090a020d03020c0406091b050a091a0f0f070209010e1608090a0b0408040f 72
    0xc4840702d00c0040425040c041d98884d19101c45c00941403d00030f40002441c1c03c0d00c098219558003000e001d60050038400e5410a44420908100080310300d024441512102540002c03600c0728070760000b08541e2540301690b001c269907141c5a00140c803460310f01c2045031140c000c1c00549040d0030346151040c01c0405000005100d1701d818841c2c0d50100e6000114080c451100b143d00080d402405402035031000c0055000400e00c1d900068210108a181c12500b401410150b500b0300c51402c0c049111801d600085810055079441141036002604e001c03440400c0780e600900507070b0b130020310071800700302a00c400ba080b00303500e0781c6ca442019429070f6003c500880d02010714644181408035440005244490b64481e494000d0101c40482006047c0c03001250086104003800960b03e168580010302e203500001e4023030f4420000d03000001464403200c0c2015114000200e42c0843c0101803143c01d40e02458080c0c0120031070710810100c48000788003841900d0041e4000c00c1e089440c1d038507240a50a44544d075810580417 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 720487491 1250 720486241 720486253
    0x3180b0408031b16060207031e081c0908030c04061b050d0810150f0e030f030a20010608010b090c0711010828050702010f050114120f010905030a030501050102 70
    0x201c1d03008000e80701d881009001914110031078200162602c40b90000c104195a64503000255a5800042003422644a150280402d8050410040c0301007107100c40940020020032400442546140d05031124407803c41c40055042150349400300c04d03070800c4601c42f074001e500040510004d5002060382c20380b0036804042814401c12a5180394496001105a44c14000781c3c20100701000030306051200505146d0381c402108001a11008164041e005600000f00300d5154901c141401c001c1410909030800e100254a001c10200c1e084400101d0300c0701d804c49a50a4440490f1074200a024010041c002000041400c0b0003510030000c0581c4045c03c900040311040000d0070006000700c0c4007250b003903000d0800e100c1c103030341d02c100c05030035a04001c0d08021a109144503248901c90035510490044200c3c0d80200b01540040301124201c1d0400e00600b140042542039440d00751a1012944107080b0942c02a10801005140384030b095580c80d400880d00c0d40c00104103c0302c0e10f60f0511483d80140740034801004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 720488741 1250 720487491 720487499
    0x50111011a1504030803040c05010306060f021b03034812030c070609030c110a14090402030c0a030302010506090f16030902060910110106080c0108070e0301110703180b04 75
    0x103010024141100d0040c2c81c5103940d81848100329043d0f500668118030182e61b60b160a280c0f82c0b4289565000c0c190200c2d18040000c10500d100300100c5011502c0d42d001082180c900345c45036034890ba402c50740740d0340c14842007290503d48480005c120041d450015002001c0c10814010031502d040d00600507601c602c064840c0c80002c580c00103001e5075914080c1c40c030030740e42c0e00c0f0600e16150501c107444018040781c0c10000c0c400c00f00341c1d201c1100b0340454010100c0c40da91651700020004800d44512031034040029000c0d06400900d00740100d2504240f008040342c0074600390901141d1810000c3e4010340c050b0755508101306107030408094031644010b84034110549464100c01d444180d10003880c1c10420541c1c0c03080300400b151203080c01c407006164000c05d941c2d0725201c4110020004130410421403c03c0d4201400000c4000001801d844612816150032016617541c40c8120703950590518216410b640710342d1640b050f01300e01030041c01c10030b0096498405008003e0b200c00c03886005507101000001c81000104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 720489991 1250 720488741 720488771
    0x51008011d100e1012081306030c05070b060a090507050c0d05070b0c0d1d030a030b10020c0d08040306020f09010e09060102190206040902040905180d020a02041e09050705011101 78
    0x4010389081c0680d01003a52200b9002c120166016000540d0f900d4200c5c0500c014020050054580c0b2004550815a40360b1030320411403d8401c80480d03280401c8040c040740b400141588030f403503800390000e48034112095079003940f2000c2d81e40980f2244003240001030700b460402d04c1070101c02c265982707034240140b6082c000c0c2d44c0c2c1e190358003004015045d40304000c500c0846000035030b08050020a40171401c81d80890342d5007841512a4408000c001c040b80c40c10703d030a0b080f07007810160741400c12041d40213015003011071802e101d01a4601d0702c080f95500c00402010000171781d940302611032600c110004079100c43c3c4000006d0080300320038581d507100b441c054080200c2a81e000441030860182e0b200c0000c801c852510100d0b2017801a604421080c60011030081030042566004a00c5100861603c0031030407a0780c14001e4031b45418918500c016003004c11148050704141d0007010340100f15180e02a44084600800000c2b81c0c00394004448a0304120340402507036900440b11215481c048000f0083c1001202c920 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 720491241 1250 720489991 720490021
    0x6010f0e190902040606020102030709050103232d011d041230200414040b01050d0504050a151a0f01031e0e07060816110106051008011d 60
    0xc0c5800c8a14118031140559541d000860302d20350290041c81880d072202e8019010f50001c55800000540c08280040c2c198440d00030f401c840c10704a5085106001448000c07a0b0120300217252842070100c049808034081c0880780c406100799280c80b050b031103550410012907103050108900c526101ca0800901c0b0100b03d01010640c0240801d00b44808801128128101850948410300f4121444002e95049220503900b0000b080c0071404404441c150003148504a0342c0500d014840d0f003080945100355003030030300d0350080903442c505040450030b0414144014056480c101e90441da590000c0c0415004c000044158401d1030a42c100140b00038110720b41b5480c00080d8003a1800d2040e201d004648285034029402a0b078024603035000c010701c910100c620342000d04146490144544544040000e5081c402ca2400303001d808880c00c0305c1d240c2c0038800740407103801d014040071000c84c0d580d460b00090b00d41d907100f101c4203440107280c03030b003d41c50740c5080340c20111040032010449502024800f040b030715188100030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 720492491 1250 720491241 720491251
    0x170d0906142208030f0409050601020102040f140406120302010b0907030b100503040f1a090714010804032d0c020306060d110d061e060e280e010e0a0602040302010206010f0e 76
    0x74000c54070710880b01240510103580880d0081c0400206400b400c000c0070003c0040d5402150b061080340c4440d00128200e2007107108082c005603080a040c0807480c40048814011500208003003a440d8561400c510401030f100c03000c801603995452042c5941c01d100501d0ec0e4051141e0508004e2480c1880104000c01e00a54a0314208500000018100110f8401d8a91059042034140090111056003041541802d40e010090303032050103400101003500800c04001100181c1d508541a29281d9068a40c40081c400088000021610030b103948d000b020b1204d000c000c03803aa501c0013000000c1c0149410064007410fa02d020720005582740c404620036582440d403208054440302c0064505040400003429603a03d2042c2001d40443c1c0b030b4681d11134540044091f501e401c0305d030041c16141c4081c000b46103500e521100b03060103060000e40d5041c24160b40503a0714000034000200e16030b0060380c0140e06001c2055005c442c4150f01040610641d44d04200d03032030151594042c9540000d0901c1a0500e903000c6c0102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 720493741 1250 720492491 720492517
    0x30506030c041805150613092001020a05010c0210320717010f0f060509150c0c0405040f0c23190b1207080604021806090a170d090614 59
    0x403003100e0f42c550f001002c11009030044c0942d0203001340d1034401c280503402501c0c11440b40000e8040c13011800b9851041600075230b40201c2303144070a949032480c2e400711580080803d0544c000c1e01240c2010407020b001d0500301c0c581c02d0380501480c80441180c0b00440d255014000c079072480e841450701c82c20000443e040800002c0192030070041e42c82030412210f5003000c0c10a2410500c40d04000521000f181c3c0e01c030025500380c84031100c520f80c0c03110011981405420003042c2e000e0180c25018448550003c020906502e1540c10b035540519604041000c0d00c02c03d540848103400a50b040c003091001d82c813050304c0904410742540e00c60303849040120f003607200400005445010301304120444041543d00600c000d1000d040c0d115294050501c8030181c1e21000c03214540032642000019210f854540b0803107031202c080c0407103c999010044c0921030117400c11075030030b500008580004160454682000080c0307030300721030061880d2a1440001450203c0d142d009805118104a1600e100108101500c0d04c41c3c07154a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 720494991 1250 720493741 720493751
    0x1115040b0a021303060204030213020a0c030e0406090c090302030c09010f1a120a0b01030b19090f06090e100e1f0c021c0e01091410050a1e1707030506030c04 69
    0xd1075040003885584500b000c3c20100100010400c1499009081264001c440030f44c040c006901c0030301c0507072007024280800107124904010009014044590740b510001e080081d086031500d049038112011013650402180384031408004610b01000400301c004025100f010640d4503245a203c00071040d401207059a8966030886810340c0107180c141e41001980b407240780014101181c068004081180039140080d0410103e021141860854051941251800f250703885113021684401001461a1070145940390440000c1c06e1000c0c1c01400c5100c4001d00c0a003101040d400302940c21101380b402103a0043e00500b955103c0c0741100b00707410702c244c040d0842c00302d078080c40c4000482c181000b080c4100020103070013000e0303102c1d1030b884003804011050030b0302d0340d084280d2242e41d43c103c4008151000c2d540b1009000086200b40c1c441c0340035054850b00390921f81d4000f509803681c0e40e203d81c000c50595000943c0c3d200d4030038500114400007a000f0075941020000380c02c000c1d001c2601c1d0104801010f0107240c5034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 720496241 1250 720494991 720495001
    0x3070f030207020a0608150306040209070c0807020d05160807080703170c01050103080c010e010b10030917040e15041506030c14040e040c08030c1b0a0801020c0c011115040b 76
    0x1076012608601da00074a03091200b900c1d02006050064103881400301390201004200f95401e00090f00380c080d0b0380062410100da80c0d2207a0440d01450404030888485c0d00c10320003c4c00680740c840da14040140f0400181035514a86801100e60b423120b0360051140d80c0c400c0500300114a40851018280c981003070f8041116128000111850721540540007030300d6103801d0000042c001c041000c1d0070054016402070048982c0700405500780d815100300303c0c0d88480808810300700380c1e000340c3c8440e258078456888200a15000580004980c00c0b0b40c0c40700601420140810000c055001004c10706030b0301c1190308200810406a00904054042c040c4105140c0c1c0c8414001c4018002c00518050030803444035903658503101c6112080b10801558100d40e1101030b110003044407000031003a69a680d031440001c182940700311640d00c4880201c03034030403608058040804202004280002c1c44100d9110f0004c00380114010001045000788004032281074200e2100c801d029004941e2003500301ea0030800c64540d44e195 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 720497491 1250 720496241 720496247
    0x1030c0b0d09150b0a0b040f05270403030f0c0305070f08040c080a030c05010e0a021c03170c130605130b0f251203050c030a24090b0906030a030503070f 67
    0x14031000030f0b0002046032030342c0400c03600c260081200c24200b40c480c41600b590f200d03118402070140c0e000e90800c50344905814030641c1011054181c50215595a440001c0724411080201003001d0f1401c1e00029210300c04c101c9541c0b0fa9002c0c264030480701c1d250400c03142c642260001d200d143c044021501304500c0300041001e0060440c4024041d000d0142941c0d903205c001d180180080044403001c541e03d5080c40903000d1486d00c04500980b0640d00a001c00c205070945c4002c0740c001d4070305443c044040c4688880051881032030038625610801c040c0d03581750307a00c85444020040643d2258001d004011040041d81c01c840800c6807602d04840c03d03558074070f4580140011070f843c10f0040c00c000b174050341c01210120080444020341c00584500803401040d038140c0c0d0300c0c0100c040e608219032041c9603400800204103101d60b00d500c0644e1035410b0200c00502d022010b400c0345c2c1380400c00c2c3c1c0094007068a4500400540c580404c140343c01010072001800c5003c52690050181e000042128051201c090303040561540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 720498741 1250 720497491 720497501
    0x31b060b031f0608071512020c100605040e0714060714190308090712080c19050d030b12070905090a080a0203120703090b060603061201050c0307020606030601030c0b0d 74
    0x14010195420900d189014020100d040300301c0b81011802c1c44800150050301050041c140c034600c0c071261b58860300000040c0d80b50320006580c44003141d420030034068401014009100100d00c440000b00d003191400b001c00090360f00b420f244800c3c940044800f040326413a29088400c0810058400a4442015007000913a002124518401901032444004905540030702440c03800d40c860348a003aa2500c9800c202030760381020303006000c0a500c05400100109084034060105d1016540840d02d01d11161103100003404403185045505510180ca01c070740b819054050110f00d550260340c0000c285281009042e0345114602c1100645503407840400c0c803405040c01841301a0350420341490381e41041076030003556640150302c02e50410203a074012560b040c0c4680640c0da107954006440c000c2c180c50f80000c1103a82da0014000340c4d030151035100400709000c42070150912460f0341c5004291285004040a410108000c008501ca0b41010005200103407602080740140c0361501c41e01d94403850900e03000c1000740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 720499991 1250 720498741 720498761
    0xc02040b1801090504030809060103110607060b1c0605070e0d0b090a05030a180f050303071419030207030b071713050a0c120309090507020c090c090423090a031b06 72
    0x204030034002081c8240f80340c010500a40c401e54030f1686a550300d402d042d4031a0420700005290303514140070141d0354070303203900604019800740c640010070f038940200090454869100d2080c42001c00040401030281c24030034140e0120640c20300701d17204040500060300000c100c01004052841c49000f2940032a0104001185160700c241140d55071805014041d04003080080442d602c400c5040010a0a444442600f8100e075000b074011800e00106558040b14625804010b030000c0c07280034078481100e0090710400c01c40500a4000e4a100c41c15428451072241d0b000f4014401c4c0002956910001c1e0b03220800903074000580302640e89200b05902d0202c0c101f00c44403030050309030784520b08081001c0c1d08440d50101c41e02c2c030903140c0b806890350341c103560303015204200d40c080050f0300031900c00011810701d100020380c8645102d01d168900400500020704443d020348040c012004141403d41015602c02d0503542c101100c10300410100e901c5980041402418406a02c0e00c0302a0300072000800101d0340040000d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 720501241 1250 720499991 720500029
    0x40e01060b07140c0a06050a0c0f0b0703061d070903030c0c0b03041103060708040201020601141203120f0702011503060914010518010b01030e0607080415050c13080c010c02040b 78
    0x1040e0506248540962640540c00700303005074005030000b4501400468106c2c1c14035181e07070b410141e00010070365005401c060207481c58245a10b581c00003c10034202e0500c50b03040d94400288590a100c41d103100080d0400404004104c95000d00407080c1d040500001125454681090250340740d107000c2800060551100d0250200403003408100401c001d02c40400210540440d007103942c0c0c42e1000c84440c6000c3d0b81c0a4052703004000103201243c03500d14841c10314070010f428a0415114619800d16560000600030302400b810028406410700c6103260035045107191000780041d404d04014280324042d07510004100c580e8410942c802c01c134503580c55010841c2c09d82c00070011882d10810081261028160003441940380030b2840781c15600078400c540c203071201c0c40e00a05a41d42e84c45000c0c0d4a0000c0940251083d03006d040080404102034051644940103485030191550b02c00c8111000e8003101e904208003e800010292410307076442010030722581c0d0111004110030f1004d1000c41c08601c1c802a01d1401d07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 720502491 1250 720501241 720501247
    0x21b01021b090717070e010305060103020306012705060c01020304060605030f07152606010225032619080105010309030e0d0201200a15090b040803060a0f0612060b04080c040e01060b 80
    0x2c5e00e400c9814070030304000a032400d2219942c0c500c011000c9110803140a8082103481101c00880008081c40ba506c10301000c10100c0b4494541000640315003051280e18400c1e034000003007100708803183c052032000702029401082d032240c2c094a500e40307660690040c140349010900c08400320705e204220300100421110050300b20160701504004446c02c048039600d0140c4104401092004603110140c0b843c4400301031202d86403400c0d81e468801c5c507400e020300001200781040e0200312014010000f00502e400c4558040c0080c258a0000303403c52105038002c5060616001d03d00000c280c00515a000c62001180d8604a8601501c01aa4020140610300e0b003107101e1042c407000781c80b1000422044040c050b56000101d05108100c03c0159442010001c040c9803212004c100011400c2c4007460f080400100002140358030b5000850000c0500e61045c000075028551741c0e5418042442088040e2400ea20600c0c5014102940307142d80303014148620380500d0380c96071186080b00c401e5101001400c0000da50030342e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 720503597 1106 720502491 720502501
    0xf09090307080301080d110109020d0f05070812220503070303140f0a030b01030e0a1e15050c0c07240825021b01021b090717 55
    0x4198442400200c0009912030040c40c042d00c00c20004141181d4000b0000b07100d1000c0110041c1d05900d001f0202c1c02507151151200090358000161740b064695615195152044e50703401520300b402918404440141d50030001c0c800540c24400e0504500095804810900f89c0d6104041d819481130104200103801424101c010346544262242890302201c041e0a803980078941c404000b9940f10324003c0306613054814043e0404184004250303036030701a038528108115810369400f0940082c03000808000600344c91618078855091306204500744200e00c04110740000b0201007060040110100b4404000c1d1541c0004600a001c01c609015000038103446594001c0c01ca42c078001411850351a00e070b541c050400b61280c050ba4010000d400081076010901505020081d04540010000c90007a0000ba11a8000d9244c1111070243c1500c56140c1074076019807003e5402c131010b0403036007008 = true := by decide +kernel

theorem cover : BRFrame.Cov 720323741 720503597 := by
  have h0 := BRFrame.cov_init 720323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 720323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 720323741 ≤ n) (h2 : n < 720503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
