-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:24:41.326664+00:00
-- url     : https://prove2.me/submissions/97027e2c-d680-4e82-a1c7-5d101a83be0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 420323741 ≤ n < 420503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 420324991 1250 420323741 420323747
    0x8090d260612070909031d0a03080a020111040807030c05100e040b01051209010506011803020a0e04140a0f0c060503060303180406090c110f0a120c0614090303040b010b0316 76
    0x5401c00001000c66200008100089140500507440b50000d95180c11801c070515410440720644100310900104850281c003002440c040308600000b4075401000c030b4a801624400d5001740b4aa6081c13401141d9030329100c01a861b52064144001c890a84516078007040310305100205612002c0c0903100c1043c0340b0382c20402c04c0301408a01c4141e81c10848180030f021105622103001034082c4810400009140c2400b00005102e00304940074040c030203100c40c60820060b241c10410383d04840155400b2005074445140110220000d20103203503451103800021420b00000c3c5401c510914030900c0d850102c507688880581e002c0c0012219550315030420b10403211a010501040303200900c0003000001c005480d101810219100c0c070103064005181500746006c1040f003008083c0103c00e88000800d4944001d1342d400e5011040740d44600104401c0d00a00b101b00a400d8100480142c0482d008203d00c1c50650082d84d9030360011076043e02c81104650000462805100c00c0f64060011050340040c401808a016 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 420326241 1250 420324991 420325067
    0x60503010e07060e0114071b0b04080705060d020d15060216050a050d020d080a110c0a0e2a070305030403030b0a03210e13021c0c0c11060d0c08090d 65
    0x4c50510a840c2d590054040c403034001401e805105228681150403441c100d00f0003002950400310a4100800c0300340510400082c5071411500125070555031030080080c500083e01980c00c0070015542000b240c0a80041c40d00504026101c06070300700d4000f8182e0000c040b2000003580b1505410000c0590240f0603410451914200d460024242c9541815107070340e0a80e140e88100c400c0800141c1515450041510510001040c2d9000310b407001074045c00c1c04c0d030000601034094510f070120420091499009113056000030003501242c0041900c0e03003000d04001c0c20582c0103c908a0001f841c0c103400742502d01c1c103000c4100544e6000200036942940c400541c0f2054124090030030700b4401900900402960343c0003040390340710f960510140c0c41c0c03040400070303001100c60fa000b1407642c5810074403440841d60348088000c941c5034024480c880c02a4502c1d001c02c1d003034425501e0340e90f001c50803c80c12411403900128514025100d01c000c6500380740c82403200700e03a10391103501c10200c00f070342d00c604030024400940380c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 420327491 1250 420326241 420326267
    0x150201061503140105010f02030c0f1e1b0607230c0103060519150306080f030c1623010c0807060614010e09150114030709031b080d0f09120605010306060503010e0706 73
    0x101ca141c41c400b04ad149150a40c0d90b015401c01c0d07840180c000260200046000007081011f074024102894803c4501d091025a01030b0940980d070301091220621041c80d40390018003410004510383c09511258094861440c20312280c0443e09104000410f400d1603c400c080c641c2500d83c02c19042e40c24560640c81445900403400c003050b484800c00304000744244011503020710301c2001190340d08215507016080c00c45800d0200308035110308004200200d1020140f16030a130000e05a22841d500000050342c2c0c000d1100c5015040e803001003034500c1048090341c8200e0940e0000c007a03e005150201d001116404880c6600d66080700c41c034408a50401a40b05841100d004141811200d01c0541031121501c2d0b04200e0f40c81c40083c22103103080040c0714103c3c400310303000f205e00c10b6207000c2503090454881c2d5402c084c01c4000100000041c41070307a4180b007606000d02802542d4030300b04684030103003444400b403c42030000340d821528100000402e0f1505200301c3c1000e0780c0c1394000d000100d18091040e503000c01c80c41d038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 420328741 1250 420327491 420327493
    0x409020406051201020705100b1806061240060b1f0503040b01051906050705010b1908120301030b01180e0d12180506010b0d06150201061503140105010f02 68
    0x80c042400e940c2c2d24040801c6540f4a400180c0b129000d003012032811190449078401d162030250b00c00000d8541c41f00e40c401030048842041c82030703110200400c44901c1800f541e90203042559040c40b2440004c001126a20403820b40401150000703455018040313440629403800080403031100000245080e0840d0325907610040c603042d006004c99420000324001c2e0314000002810000c100001c100d0903080310381c05007500391003485441c0c0c001d40b0007030303841070b4140139940034804080f45001c01c01409402c4030234840390180c940410018950390098070001107004111071802401d0600755581802015030341203e41210603400d40d6480d010301000e4042c1020131541345d060b1605005840710804005140038078400381c1c4c0310650450b2140640c8101c9029a1001d007a480032065103c0c04100300240481c15207500c104410b03514112003402c18010120756221402025841100d039100340c0e0103610501c12252000300b5000c007074144107001c500701d82110100895140c1d02500502c000e51045c90050f0755050303280 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 420329991 1250 420328741 420328751
    0x80c04060315030f0309051807080a0504081e090a1e03110612040b01090b03060f0c09030a020d050d030b030703030f2115060906030c08011a090a080f061005090604090204 75
    0x18958007104d8003441401d90200301850b90400071420711a604680810b0504904170ba1424640b000500101c0003411a41c649030305c1703030082802d001c48001100c6069841c1c4040c4a14038404002610445d0081d6160920401d03d0460018107132181520390340602004185802ea101d05503030794020b1807204141e0707840d0000c00520114440d00c0d8111030140c0500d0050085600561405420030191010a00854003070307003184050141140300b000e174180e080b0402c1c41c03001d522101041c01023440c004400b040603500400200c041c40c207100002c11aa01e101003240e9040c0155074141c010705648140314440140082c80d2030452200c0c2d5071003002c3c5003400c5c00c142d00c038900041a040d91041c0075290094403007034140014110030090380742c1142407107004041c9400e0921178501030410103818084148120743c14045c1043d29035002d940460101c0c1d0329030381e009018240250b101c08241c0d5680c00c040241c030541d8404c140204204a43c10039020040301c42c001c00d09001507443c1d01c1400054941c086042740c0003034640c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 420331241 1250 420329991 420329993
    0xf021504030903080c0a0c051e0108041e0809040507090b0a1202041211041a010c060b0411030705030a060e1303110705030d030b15192d0c12080c0406031503 69
    0x1071801040707108010f0000b8100709406d418001d40058003544a00d21078881c214103000100420080700300d1103242400d02e41482c2d82c49040080726582e4161900f00b4002c102d4142c2c1c401c000406010f0820101c1c00d95081180b0b80d074001081c1c4503058180503da0380b070700b028031040031031742e01c00d00070034482c0d0300205009810556510302c00c4140310301a440c112940441215804128101340c4200c540505a5205546903518000c002814101b401d2101801c6152035000b40300c02501d80340c000b230303c0701c90342c60100350350340e152441005089400c192942c2460b181802d01c00102441c880c0701241c0540086800600c102082d40d6050b074a44056885000741405201c01c00503590b078003030114480a68890301d001c039400604901300540195280c9000e05400824800322802010180011030456030b10b04042a00622220b4005106040e403600c41061404180702035010691240c0c0707240c0d44511814243c000d40c615641c003a02c1d284412510b00d000c0070000d001c20401d00c0c4c880c0e040340c2c0e24401500d6500c104142c03070b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 420332491 1250 420331241 420331253
    0x150e120f070b04230105060906010c0203071a030402130902060307110f0a03020f10090c05090402062511011b1704030803090706091a0315011106070309060506010f021504030903 78
    0x2044a09540350305205060381301038020003444400802e00500200a01c1c60448005081ca99002c0e01c1c1e2810000110b00150841d02c0400c040d0703001e010000380020142c0142c014041084c3d00482d0202e0043e18241c2200b07640303144900600300d50303a030b0040242e0b040d59580c1c0d03000ca5032010101410482880780854040b01c2c404140000e18405000782d02820047c1c16110348280741c03030004100385c2e0080b0328018060002c180d401c0954007e4420840755410f980d201e6000143d40ca004510320284100f00caa14030030002c049852004c01014800d000300d0700c003030598400646650100701c400304039002c005419000081c060002c4001c04e410112442030409850fa220392809800454546105620034041401a41d8008100b427004000d2841401350b0180660710b282107502015141000c2c17040d40d00741d422640da0084003c030942c3c07203150003164100c1c6001078005014290311070081d125107281c00042100b0354851002c0080c107500316002041141d07943e0000402c425802002a810400c04035008400500c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 420333741 1250 420332491 420332513
    0x6030204380d1202030903030a030b04050c07150b13090305071a010b0d1e110a03060506031e06060d0203163902010c06020c0109150e120f07 62
    0x15032188000d03018080315681d42075551a01e12580750458008014040d40d40700000c011102c0c0d800004114104440c0509030b186000d4074001607490b0001007440c40e00d0760f5140d0702000310000300710343c180515122a01c40c41c0c001d204091018003400126500150703007080c20f801c0b0f0b401555014280b654041c010301c0002046403c5100c0c2100040c200140410a02c11410a1003e00818490120140b5450880b141c010b0f4818580ea0840c1152248181070601d52900d04811040f030360078100b40704107604000040760740d50200d002000441e02e03041c40451241000c0c01620301c503001c08a403520704140b6045c0000c0400b40c0090506c0e500410812690801d10050300146010350310b80306070360302c40c0c12074403002600040d00d151402c0c0803100300c044600c44401d611f42081d03030100611608040110070713500048a01d2030300b0000103820240006000001c6520540c8034881d400d004844450381c1641419180091700c540c450000031960001440c0084030114a004081082100c1240e0349010195501d80c41c02c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 420334991 1250 420333741 420333761
    0x150f0403261302090c090105092803120f0305150103090c09150602070614070b060d170318030f040504020a111006032003060117030705010203150301060f0305120d06030204 76
    0x150b0000c0c0b018046003405071603150050b4548240d6801c0940b0080024028042c81890304e100710f00e00703450064060002c40d4030440ca003d00085040b1841c0d12410880384d10740f80c0344020360008400641145182e031291080c40c0c020580d6900303616600420ba0011006080410b0707064175542144040016444403a208400007110020f0080c19524503040002c0c2c14661a64006014004980d40e200c28a110030300481c0c103038540c800c59092458480034049044010850303001000c0c8000042e252107400d0054000e14800c44484614030036080010030140e40341d0250200940c1a11307014041441107250075006020030b00603e20b0704e401d1145000c0e46692600240c900b490911136500c050910610540c1d95031142003111030b22680380c2c11603903140403d40c0c1d05014424031012031101e0140780b4581c00b00b0b0044540c1140c00c1070083d51a81818241108207240380004c45100f903107050300000312250340c4a400c0c41225000760142c050081100300d040402c3e0300c440c00c0469520390381e1030080010791f91071188140c0c01c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 420336241 1250 420334991 420335011
    0x203060a15080c1e180f030d09091a0405070c0203160305100f1119080601090b1c0e0d08010e090a0b070809030409050f0a050a2708040314030c150f040326 68
    0x603400b4001b80110a00b4180200d030103a0032910010807030300d400901c0001282c21101d00001c800100500e03c858501c9042c0d0126441414401400803295022045115a80c0200c0c10b40e18906400451120036440c1840010450381245140441404e42c0c1e40c00914407070340002e00031629004071100d000e1107502902d00d40c805c0714103140403182103d522044003a0b00035001c1c2080c80c1980e04000845a10b030041c1d05140c510703003241003010380c110050b1b6082000040610011a6140b0315040d00c081c106403000d0191600301d0340303520b000070442c0400081100919403c8900d00c40a5125054122600c440040214146220401000824020910500c2e2062030750f8a14100c503810580501000e0b40c1d03028222806403410010308081100c40920520840c0515800382d00394201c0f1440c3c161814052039001070300702a10111041401e840101c003d055031040f00b0b0a8a07104c40d280350a112a071070098400300c14005000000a0001c0d0080144810540383d0301030008560300f41410703050203000100e54032000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 420337491 1250 420336241 420336277
    0x30a02030a1b0e0105180601020a080301090f0b03030a0c170c16170a02012c060a0302070213051315020c060a0204140d02030c062b0203060a15080c1e 66
    0x103520014079202000e802c02d08a00c4090b1351511000500c44040d114204826600c8400450f0441e030080003801c5400781e1080c5925260741e5070701000c8006160848407902c82d00d0900121702901c1c40c0100c122a0704418079241c00c9129102c80e01c0c0d40e008000c1500400742829010494103481080401079030001a046801401810b4104108041210341c150603008841d480f46107001d0041c1c0e040388075102c9561030441c0c4c03020000c02c0c030200001d013240c0c00303490075400c1400042c2190420350716400404c2c002e0b0090b14001200200046618201d500c01c031419020105084d41c080002002002010505010311501600701151702e0042410302e0410354041102a50008007002641103016250780341d140125003002c040c0107140c0129840e2000c1030001441485c000400d400203455980701d44080d110013000e0b4509441d942e078480d000039032060382c0861041510620000703103246820402003071220680e82d001c0c66078640c8180003070b460b0040e81c08024a00040700500c41d201c1025005041561107040316901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 420338741 1250 420337491 420337523
    0x1b090e0d1106060108070e030a06090b041205070519020402120a050105010e0312090402031317090a090612170d18060c0e01020a1101210e010f0209010e010e030a02030a 74
    0x1c06120038014030241508540100005a0f1300a48856404500c60030030f2511307906c00c08000303410042e8940d0020301c501e181203d490244070b0740364081b0f03205034411b082c0c2c070303c010442e644141c6050040003002130550f03002001220100074000c3c407482c01644090800750908409680d02c84050b0801c403002c46026940f04010480c0e580e00508072040b410702507001e01100c0c0c1c64140c81e03070042d2091010541c000ca0300080803414480c900d24004d21441c1c0c000060a411146802a00060741d120b807224510070100d81001040b0440a0300c1580d082b104c5046000c280d005050b52100c080307810007c454000002c09100d44801c0741c50740d009415007044950501101701a0500d020003c03600c000c9540c4040100c0001210309698001648185840e0002001c912120316030004076030305100464800782c0303941c4002e1382e00c490000503004950010b0624000340000c1041c60340d064100e0042c400d0322130010381c065951440c40d5004114900e000c3c000038040d141c01c0780094012a00e0070751403200440710104c403e81c0c584 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 420339991 1250 420338741 420338747
    0xc03031b0f1a0c0a0e120c10081005100504210209010b09270f0901150e06210606010e0414011706090d1e02160303090f0e0103020d1b090e0d 62
    0x5500c60003d442c0c890420035078102c0140ba614800c60500d00030140c0d900c0c10b035085c4008202401600c1710080a220742c0b017540810003059214280e48001001000c487d0108191800c854210080d50f410340d81d0314242460545203000041d44c03200c0c0c00e05101c0d0b25510b02ca01580792519014040d01b000495161384144000a124400c0321610f1200414002c2c1004400d44550380e420782c5410006400f4001001d455801a103401042e038103100100c910481000000e0b450341b180482440381d4001c9450417800429207890300129020b80004543c541c01c1800080c820f0360095820407015800980006089200c010340c2d010703000400c4c1c2013440c040c0b445440181c0c08141c20401103034401c000a0162400c0c0400e034001a0604094001004804402c40c000d00c00b017901c01c0195500f45251003020b24149a680c0c10701900f550b40301d0280d200d24500002d004200f5101c04050035040f40e03805810010f015880d619a13491010343e1848004142c00301d0341000803070401a00030541e0044854010301182d050582c80a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 420341241 1250 420339991 420340043
    0x705010e010e0c090402060301060c0311030c0a15091110030204030c090b04060b040b04030803060105220501120b010806060a03091a090d0c21090803040602150105010503040c03031b0f 81
    0x21512a0044104100047c0c6034041541e0451f02a030401d8558010302e4030b0305803000c11008280040c2440042a280b188620004220090b103018022003011004031031a84c6003911b02042018105200c3d4a072011f00505010019014605103842d0060a041e129503825150801c260321802c03906888544140b224503051103071800800c0c185103080c0c41c3c149000110b24140c0141c0c031020b041c200e0007200051090b4010400c84504007a8080101d42508221420712404d5038507004060000341e4a4800c03860b8012144030350034020340c058681036026601e050401000360300038100030040503210441d110006815014041c20940603c0170103400d441c2120226240c0703c09160190104402081c44202013403910a9030380c4c0100d1801706000000346409001d03100446683d2104030180300004001580541c04074030f102a0041d02503119015980c0c90e0011100f41c001914068040c0681010401c00a4060a030041e8850780680080c1031100081d120014582c0004c401030b40c049443ca424030001100d207603d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 420342491 1250 420341241 420341263
    0x90903230a0909020703050708070623090703151409100c0507030c1b0b0c030a030b04050903041e08030403080a030506010207240302121302120f0318060705010e010e 73
    0x1041c00c0a40040e001080899584200100300360b00040f500107041c861012144117607000702009541d0a0b003440c1201c014001c0c8a140320842040c1500802501101c03140d0b14001c4001d140104120740c1962240034030b0203954072801c4c5a050382c0707030b0740008141001281207101d100c02c4806800c40034071405501d000d65081003120000c10000b00000000240c010b500e007040030747c207c1d0000807480429043d00e4400703e8542c104440d95100803800c80b1860200000404c402c600a94003401484c41d0981400241c0c0e0f4107640050107a0408c1c0800d000581c4107241e80c03500302107150900180582c2d500b15580c210b60083d081941c001a00140310001590180622600041c003803008141d040c0c5040350200b01c44c511085501c0a0b44c00356806030114501c60f4054451000303512194071b940c0d00304002c035140001c1c03004d41d0882c002c00c1502c001c060304603000b14825000764a0b80001e54030300100c4001c94651703010101d400c50341c000c409001b06c5000c0340091155540c07a007170031400041c001554900162070100e100386 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 420343741 1250 420342491 420342557
    0x90715050a0f0302030705090d0b07090e0c0d0b190602032a120901020a0b1e0709080307030e0a180f15030f120201060308070b01050108070c020d0b040c090903 70
    0x816011110780c0501207032a039000b50710780140c0701d4403040740c221494890480030307036403002d5040484014410f1540e0041d00911658030340841055542103003481030f102c110b6400700c1d1502c080c40100d46d8442160070035190050000c210212617442d1650403600700b9a150421401031780040344540c02c004413280780050412460b00303d15081c065030401c2543d201d58a0003440803c400103e245011a40204681d103215030340718800000780d150020b40c042c0c2e40c4180310300b1040c581352a5008644c0b110300445421040d41c1008000e541f5102d0241c40c04d40b6001c54660002d50014401400014022070044808101c503c4018001c2185500b01d00d1410644656212449103911140d9003000054070011031800d0f81c2da80b011014000c000031000c10b0340100100c0c0d2000d056280005844001c004541d46824140e41c026207810005843d043c004540a181c00c00300250000240c03136454000c581d050701e0320360340f051107080342c403102c0c07521441c604064aa0414040b404100c0e041c10a44c2c18048580107203010401c405 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 420344991 1250 420343741 420343747
    0x50402030a0f03110d180f0303080a090c090e0d02010b0406050a2c0108030a02011104180504060b12010902091302101d0a0b1801111e01021209071505 66
    0x6000691114114030300204540500b90240302014014010348025062200541c0e0036283d9440d005030010f4510200110030100c404030104010329610151001e4030707010f41d00c403510f5030f6444e80c11800422840c001030f10402046030001071442407d010700a00c070486900648180301c0752240290a483d02002120310450600300203000e00d4032140c074540111415401c4410a0324484055004650845404100c0303941e004800403c9039980003008000302e4120740d0081107040041510315403180914088c0710094505100c00041c00341543c0c2060341c0242c0030b00030009584800784005511240c10701805004ca9444490803419032803c2c1c1031040d841104e8182100308207d666000800301c100e2801362000380200780701e4a00c000d2407500403811100c04d01070841e469640e140c0dc1c625500b0303000301d0000507500708140b44c0003584d54807500c0c44140c04a0600018040c0044125a50b145186c01c4103410240c0e42d800d0000c80c038183c0c09a00703114000e0362408060b02e0204d08001e10950581c804000b26024130000f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 420346241 1250 420344991 420344993
    0x90603140c28080109080c0d030e0a0f030216141206090604080a1b03050d06150207030210030221040302121201062307120909111602010e060c0607030506040504 71
    0x1811204904240c406038010034a10030b600e0200720000e040c0c100e03079120340c42d0428132402c0060140090140c1d41d041c50417034902007a0ba040440640d0000300c907040d43c1e90403107654400040d81d0071805034044d6101f40140e514030120940c0001041440f58400302c0501000c035148249410316000130094140f17808058556450011811581d40c03001900c0240750710000648000c00a00c0780e4080107059640701802086d50905003001411134100c0c00e18820541d00d048400907070700e440441ca44801200da500503045051842d000c1014042c03040302420107054080108000030904002003840204000c02da42d11203081500b002450060080381d005200742041103035810b01440091041d0454403030346060080100302d100311850b1b6400401c1c04040c000b80102e686ca00300450350f5210414180907507540745800d640c40741c98034203503140450450000b0000300700c015208100760b07003112500790040c1040c4200340b4944003c6105035000341401d840d15044941886100ea034980103141d0000d00c12141071005e4101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 420347491 1250 420346241 420346249
    0x17030403021e03120d0c090f0e240a0f0806060402030705071506171e0706050a080c0415080f06010305040b010909021306090c020613171b0304090603140c 68
    0x1616400560b1036121100b004910f03a0108540489500ea9401c050340b10b4010320804c0c0702812002c000d41011450820001c2070303505841030744404584040240c0401d9440e15070281c0500c15584208102c0000b203c840a01c46031201035540e401001d82c0750316006030078030340400641050405031074144982e00410600c0300c0264850299041d254205103400c81d817210b1a10881c00610361988825402000038140c0c03541c4c1e0001107100202c0014043d12004804c8a011441d40c9542090042002003582403280c40041c078410070a06a0011321020100c0c134181d240c20b600c0c80d40515108403400090b528800300400e100f041915107030000400c0c2418462410307e42c0c5d42c2c5401c0b4005000d95140c9903560036a5a040d90355840c00d4100c9400c40c01420170900b511a00010080c0c606c404a040c00345c4584000b04400c07948507841214000d4001081100e515200310000c141d9502542d600b440c051041e5030414600c490500040008149682c0d0014910346145454207008403a40700d8040b450b08403200b02001a01c2e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 420348741 1250 420347491 420347509
    0x111030f0a050d1410170a031e03060f0e100b0a0e01030b040b0904050607091d150a1e0608010b19080615070b041e0c05091b12011703040302 62
    0xc05080050311412180b030300034024a2400c0c80461615030800600105c4019501150165622280c10488050140c1400b5a40d00ca01000080c0040d01c01c940003080710034a0311404820100d40e16010490980d036168a076058a11900461000180c90090040410108040c01c000b02010120141400c0608501600342c12412210a06140d120100071007180e440d0b511040308100300402041090411b0b0601d95a1010100e9144c0045030a581c0e01150400744e24074143c0742e03900d01203900900303951031000d80d0310307541c0c1049040b640150b100c80f0085128644551304804014070343c20410081c52922000078006074040c0e1101e04410300422801100b80c07080340d850103182c050b03424200103580320000412040001d28411103108000890031008000005c10207500560054034012818080c8006c0c5042c00c4290b084000e000c00c0d800c4804010f0350070402e000f030380e00c00e02c489a06800c9807100ba407940601d610030080c0701c1c20228030000620006900c900010a0700084000440c105402d55011400300c031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 420349991 1250 420348741 420348757
    0x9061203071502040b03090a02010806030a020a0918020d1104060b0705061810060303081608010f030b06010c060606020a0221071202210703140a0b06040207030309021005090111030f 80
    0x1d121510218506440c0c0c045a000348540c1c11019500c2c6401f51101340c036038181280490000e00c404004c290989800107800c0c8035590000c005a10240ca0b06004100429204842d0060b80c24482048000340e40d03040c19503420701d80035400080d05081c90303134200001c482d2603401540c004203050003103401040c00060300c07070362054642c14106182c0c1d07200b2103207501e8084800c58213101e90342086000300416501c06240740c001c2c0c0088480100113980382d0342c26907040c03600740200010300d50910000c10200341083d00301034110034107040814611200344c0b220f106544007500607201603480100130b031085007454001d400c0c10010b1995203c2905100c121140d4840d07a01d40300b40d401e242114518582035640f00e0703400c405135200001940d20300301411030116494645520003501c1c030440104041d4100c01010030050201c0d035110111705403070390315281008025006040103500301599000d0703140058490000b03102920110391543c0d41c5a001c0303c000188801031440a07a48030f03802c18003040c4000b480c0d010680f02c0394 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 420351241 1250 420349991 420350003
    0x1121e1505130b19050f0c0703050a0e090c0c151005010e01020c030703140f0a020604060f1e0305161d0108041515091103060a0302060d090803150906120307 69
    0x16114400c404401080d8840050032407002e1006220b151508224070010131668040240107950b00c181e21031400f5030301140d1031180440c0c00c0060314000703442a1300503c801015030409180c4410810040f034003105085030a07036091040004c44131804001080244a05a000300c544400ba15010100b8807803079496128141c10700c01c04e50b0450030140e00900904190940c050700b152481030783c030305014012030088590381400d0b0042030b80c0580f40100205034000e040d6000b0340124078092a08200300c610350300e0001c03858200071041000000303414100100c0180c40815a03070203c0c1506120354414001d0815031010410303c007007a02603003c1103c2c021410180000700342002901c84d071305c1c1c0c1071010300f958021245003812480c21040603040a4550407a01c166240390703808111117041ca01002d0a184420f03180b85607c0340d0a001c0400c018079181d8000d0000c407080810109410301a0703501c15000307800656006400545220614a1506000110503801103044512844c40464a54003589a21540c503024040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 420352491 1250 420351241 420351251
    0x180207020f3003090109050102060705030705090609040207060b13020c0709020f090a061d01030c021009050c0301020d020403060e1204150905100e040e06090d0e04060b0301121e15 79
    0x446580c0c41c030001c80101d800d0408214001c0800500d43c0382c1d44400f0030039000c5403c00801203201c0d440044e100384900581c0d11581e180d1707121600b003a91507030020785016034002003c010301c2034691a0b40c005092154440c81c40407441203802c000f048002858014038100452040c003034040c01e4a00080c01c84220341d010b440c01607507081508408050f520641c0308060f08106e41190010302c0541c000f25899454180c247c0b1140b01600e1140110141c400d40c0402c800107a00c458500104c030001a13116000c060b108100311101d60120340e0110307003a40c2211503009095640400c0400500010b0302980c1103039070242000d41542c0d9500b50702c8e0b030500d0145000c0c0a040d0704070031511045807030217440c0304406000014034503004c0d800d5074240100520107000101e4000c6040c52144c00610000042860081c000e10014141040c0e881030708440000f642c680640d8040d4680f000091400080d00085000c2c1a00c25a06441d01206040141c07100014490318480791540800038800b0454001c016448181004000b0030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 420353741 1250 420352491 420352519
    0x80c1b0307020a0305101a0d0b060109030c141e1f0908010f1a09070807050a120f020901090b190503060f040e0609010e01110d02070c080a050304180207020f 69
    0x300d14012024000d400141e9100c01000f403100000720313600c00350008501804400407540000c109081d0441d01c482e002807104400d00700056040181c660b21640600d0001c4916650f61601400348076254018111039a1040004d044c81c106815410f6061008103554040301c40200b0200e000080207444950000304061664540140b0412440c0014910a00240103806c96a8050f40091040c80781c02e950b00e02240c0704182890408181d800d124043d01d031a0400c02d541c0c0c00800361003a80c40800c408081260030485a02101114410301040c2c107000580140c541c280840090040b008581218035200c9041c450386510074154008100088110302d001c940303a440342e0001c02c8544078107006465105080c0307000c8040405c00004e00c1445001c81d00000d00c900c420140d8000e00320303242001050070b0f4080410259035400c0e1a9002800c4103031081c803074200441c1c2e030780251074246030b0011402c0390b1603040040d00b0000c030003140d111035210403104201145171005550004004455000c500360081550b0f4072504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 420354991 1250 420353741 420353743
    0x20160e0709030c030c23181506031501020606010809070501030b010e03010207052b08010b1812030d2306040b010201060b1b120c03030703240303170601080c1b 70
    0x140046611016107110941c50380ba01d480b40701e030540142e01010904240f80103035044c002d440e40202c82e0003d080c210004654170920326103035800a049500600011308c42c1da0881d00c032140214410441008409401c1380e8401c0024144180942442e04105c1c400c410b0001d9480040f50203001c45209080c009884100400180c07008040d5900607030385540701080e22300500c100072402d011443c000720101a5500b070703100e241d058010000e60002000801c40300040c024030405c9401800d1441c840150028811111000105002a000d80a810a800200300503104214500400781c4101d01a01c550003464658000040380c0304008003454400c83d00d1700145502c0782d000798000300280840810055560034450400034041c2c8003281214110720a03c4030020301c6034403200540d104024050b01851640d118081c04801a00c1905d0080072002001c0014241c940780d403180380300c000e41c820340300d106942c441c040c3c90305001500202400e05220b68070040244246007071003184c44054081640000800011040b5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 420356241 1250 420354991 420355007
    0x30516021801030320070602150a0f02030c0d050702012a0c080409061706042a210506090c0609010c0302010b121e0c150901030209040c20160e07 64
    0x241e0911501e4030020062560004a070020848400d440c040002000380c03205540c0c00c5a4030652005800260154032006c020034411600040341e0700020500c4c1d101d0728505e401720780c0141d07191040030000241060041d8201d000d6075130700c1040d90000300400113144406800e07107104007005d48440c2000c5a41c0c4d01c0414040d03a881c4060303e030440b03520364980c1d441d142800c0041600b03000700c0c0030254200002409042000405900c00c42d400110340c00b00042d14034131a406d00218851040c1e948034001030110b6190742a00d061004040040061800401e490420b2420440090440c214940100382703c42e119440d03280c12100c0c45902031825400b2422a0b0a04900420700849a070ba84024008921840f18000040009009100ca09005080711000240903950007601744503e421100c9603001e01d81c1241254003401c0f20072018140545043c5180d00001c04031500680303c0d4000c10802901ca500c10501d00c0030300d03580040504018040d02d51580740c20982d0840d50310881078508200030006803503610620715 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 420357491 1250 420356241 420356269
    0x50601032301060f1403060c0a05070c0e0a020a080a02180f030f01051303022a012607080103050601230d031808100c0e180a1d030903010b01030903051602 68
    0x801c0450f0b04c07803210341d0403000c1c18070900d001001514814141850041001c038020040c02661313901c0c3c041c0112003540d40381c20105080e91000700940e030000350402c1c4801c840b4401c1000c0c0000598a1168005c060300414010709128092481130101d2072454281200440c0180c400321055075036050220b000138582089026460034550800e03080c80018802020801280c038881e800b5541f24005105002810400802c1711030b2040c07400c00c1e1551105c0d400b41408280313104900740400c3d4412001c071007076540c000080c0daa0b00300240c60705004109001062000f00c3c05002d210b0407080c109960b40104481d86c00c40c41c03124601c903654100b42e41c002c02d4020f0407561203000380700714480304099503010030310b407201ca40c01510359049043c003c6075080d80d84100c4050041c5040100814102c0300034030900c5e94000d000400258000e551107400000c00c07036180f10080a0741c0450001181e44000d000d00b4142510424000e081c1032604007582d84001a42207820341e20300850308900340d0b0340e030718071800010003401042c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 420358741 1250 420357491 420357493
    0x2040b040e0109050a050f0c09010b090301061d07020f0c0f13060e01030b090f0d0c150e0609010b0a0b03011a0f0d0203070f0e0904150f06050a060201060e0a06030506010323 76
    0x20f40d00302000004602c4142444c004ca040da140582078100aa03200c2d1280358040c1c1e4407480c100014041072008201402c5413000c09800055001e440710709140c1030b10b42044103040701c040081c040040c0744d0b504112640e20700d141032004e80702440c0241d0101c0c02446c5088100e80c403405041c820740f1311034811079005600500c40044060402d507074030f0901d01c10142007581ea0900034000e182c3c412090200c00240b44068070a50b560308034008807a61500d070312001b5400c1180c1416607d40c2c100780f090b0303c0b00700302c96805590314500003c0c00d0b1850108008003003000d580715038001ca805000412082d41c038004002006486440e2595481c1d400c15041c452610036200d042ea0b03601d2000c41030000f8268842a001051501601c52071420b44180040010002e41182c0040410f07041c0b049007400e020302c03600320500141703101d500817900f15110000075103040204c1d00b0040043c6c6d542c40f0200007031244070f881582c2100f074019040081d181162645911014140006001079003001044201c014080386a010036416001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420359991 1250 420358741 420358751
    0x510170c070501090206040617150310051e0702030301060f23070c030b0403080402090105010201021204021018080a0b10290f0c062a18120f01060801050106051602040b040e01 77
    0x2da009c1d000848404403c45008003005c0003901c081c0c40410301802050004000380840c0b49075032030078005000b0007000c40c401d00d07100151884035500c54082ea14010b829980185031a981081001020341131000100b8003002208850f402144180c482c02c10240d03810190440e5460340d5905100c44004d805620080c080b64480c41000285603112041500803882243d8141041c2d99880049090303000f41840e003c5080c0004020034018584005610504845030a251040d9001c500c0400d0002c21194442606038000018041c1080942c41209030f10005a1408511032401c0400405d010440920301403851002c0c1c440c1c500d202503065040c2d56070381420702d010030782e14058a50110307241c0c1070070f5402e000d10720480180010451700300d4201d510f607965900c10190400c00d24010010341842d14600554100c41052240b0000110912001e03880421040000c07602500d40b041d16821207805038001c50802505000b1406d801e156407080c0f5901c10f0701190003240ea034000d840058014100079070101c0c00c0b90720305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420361241 1250 420359991 420359999
    0x60a091a04150c1a152e050d0c17070c170301060c0c09020913051306090f0c08120a030b01022811061201060804050a02190510170c07050109020604 65
    0x2025894520f94407030b80c400c5442540155020300110310170b031602032695000741501005410018040f0b0180d1a0303035088000d4003030500d02c20000c1c842d15118603c0000d000002e031040200302c5401401100d50283c50f01d080221910b80884c05c290001804030010000b0041c0f10a0030702c003003042c424078020a1442072540e41d580daa1409010246146000c441d042240e50340010031021300d1080e00d8402038041d005400422102003c0c0f8000c1c1801080600f04440c7c102c6040c011800c01c1c0300d0219810711684440c100c10401d0305100c07040d0a807030b9010440561011052684c002c5c1420280d890803d03041c00c2c0442d189070140c005034244205409d007648000b00f4a5907407038402403503c003440b1400d4000d4180303140241517072041c065644581c80109002240c0080104101c0e481030b00d0596200e80203a054030304464507680029040307103805602090303941c11007130103201600e050061030081d07544074100904460030000480c01c2400e401000c122100d400032410205001080d00280b41a6a00502c40d030340e940e8807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420362491 1250 420361241 420361247
    0x50603041212140f0f100b0a020106080106062c03100504020d0f0b100e040804050105030603030f120f0a0c090302040b120307050601080c1e06070f06050406060501020606060a091a0415 81
    0x101e070b005240b8180741c00850302d801c21000420340908116010311b8001424480d2030b8440c3d5000303c1e09502190350303442d40000c41701c0081c0301f0b1401900349603a811030205d100452020f0002028034849440d46507030f981d40c500075034000030b212850084002c0007096a550f1400002c660804650019181d10350320600e400800525024046c403418540b4110039000340c07640700740d69041400701c0e00148048400c10040c4545c1d80148043c540c010002000c880c07a200d0300800c010696089442480010494841446414003010a502d50311070040c1900700464104030310004c01c0e8110511010340115610600c842c426211710030105000d24101003226901d11441c9007a5944500034030481100b8003400103082201e203800068445131003c4404c10103070008030442005619481811304071031101d0340e0a950000104240903180c0f10300c0c05a0000601c03285840b0000e0704104000f44940e104400c10000800055003240c101c00540d488452030455504800e07100b80c1051045070806820026482105050340358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420363741 1250 420362491 420362531
    0x301120f0f021e010807030c05040308180604030303090c0902030609040f0201051e0405180f0a1e180501320c07050601030f11030703032114011511030301050603041212 74
    0x68283da840f03a01e0f5482c6d500c110120b880350412540042d00812040002c034242c1d00192031140704002e94070030140c9502000500030b0340158003c4002c651504404070501204000050003003040c42425899807811100090302503a0050006006050b4081500c055900c10000d5070115903080c030305241801c2c030300d245407801a007003881170714860104103c0c490034005400c0c5c0558001c1580b00307010074245d250a00158064030038681d0240c00c60900c110f014000b490b590085941c0030722034040208070190182001030a4170400c4038110a88143e50905e4110001c40211400081d01c00c440303625141c0d00d90b00c6502e4158842c6081c0a8441e201d51000031080c000740c2c41859219510454026440c0c008513024161136004504c0050042420350038a034603181043d41074410701c1103204500050300c0e40f41c0d00c48005144001e8203c100c14001e4401841505a088006041c840c1c046078000d50a5601d04070000790300d1721009100416001091140c1000240201d002000c064810031f01407154400c43c40c01050109 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420364991 1250 420363741 420363799
    0x1b030902030601081c081503071d0a0e0705060702010905150c0607020a020f0909030d2901050f030402220c02240915060d0b19060b0301120f0f02 64
    0x30246074000180b010002a00380307140c1e40b500c071100caa285082e005c00d44803803000030407511160b00582111130b500d17030707090014902030240300000344011303460410241e82070100200a9040540361903182c10500304001184000c541c02101c02c0303030703a0f00f50a100480b4084040c0c2d1045800c003550405042000c0141030107820101c0b4402c00f103c26039518481e0490703071500f40710300c041c0d00940e00d1a080344450a100d43e0702e5901c0400c610440b07151041080b588c904450381101c050004c031505682c0f000c60220001c1100701080c1e402d1a1150070030605509081007444050070007881640c00c01c07200c499040b00e8602c00c0441c10350322402040303124603034400a911041050761401ca2049668040380381c001201000c10f0085010a0041200d080c0f0119a016603010160410341d1100180103103c00150900c2d0f00580300d200f40e040c03104400002e441c441c6094404a8000440b40c20b02400140103903400007043e42c610a070011613058103154182444414030048a001030741041c03995000680400c08241040410703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420366241 1250 420364991 420364993
    0x30c040317030c03041b0b160606050d150203060a0f17160e0a0b010509031b0f0301020309250306020a0f1205060105041e05030708060f010f0f09020d1b03090203 71
    0x4402080720314900303403104552641040105002040106000503884110b88010a4441c50078030740380c0418082540007104401c000f541100b1181c01001001e0050380c0051500342c9110117144625911044510307400780007001c1480e400b000244060b03075a40c410f0300c020900100b4000d0a10b4464000640074900b0710b07074806052080d03e03140008078070803401d0321003105d058410b06003a684600c04e0718000f80c42d43c24401810003006214200107070768103010901e00c00c030f804407031000c2c928104414803807031000b42040c0600c80d03403051041050004002c540d48400310200b031010f10500400c4910702c00440e40e1a000074040310320100ba0403404039004280c44081220300e03150b811a8120803902d4500351041102c0b254000340d414002080350703000d003184102c01d035070b40c3e40002d0758069110f001207032070490954031200039a4400e400b880f40141111500e41c0c050301000030135003c094103010300c113036105805100b5051900d43c0010342d250445135681c800790707000040340312a00604002c90001006016511410f03482 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420367491 1250 420366241 420366263
    0xd060b0310090b0a03020a050103151e0501020f0f06071803171b07081f0e121902210a020114100513090b04080f070b0c0a0806090403020c040f02040506030c0403 71
    0xb4078140513804101c1354000c0003400c07514107000045010300034000c682e000c1d002e0054804104910990f0031104c03828003d2005091341e80c40c0000080c50101c000c800c0e041c86800c80790342d016840c03501280541d8030041382c1c10304040100b424004584075500c0c503440500190101d1521807401580d44006011000f050340c51a40420740400c0513940342c1c0043d110720443e07075114a0168442210b407803000ca000200c126000110354000c0d4003032a003020f010181884500c00d0026102c0240d0000c0d10404019000d01d20007001085403002000101584103805c000c8000008034001c0a170328802d400c103c0007040c100d0b0752244241040360303981203401483e0040500c05c00c010580403000540383c3c861026030a03080b02c1e40c80c000f61a66100c6840c6e6a01080c62001e49140810125000c40c40e02603a07540039600c0c0002072130b6980100c4d40c0c0241b0380e40d0050030540c4139409520602c400b0990000c1c450074030420445c1e00040b2402d0001c1000024401c3e0751010303800110101c00c10101c400c02501501c02c40b4051002404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420368741 1250 420367491 420367511
    0xe1b07060b09090c1f11010f0903030501120c0e04150914060c0703120b0d0c0f0e0a02041805101e03020307080f031b01021608091003060612020d060b031009 69
    0x61a0f4801c068910380156800030084891500500c4602e51001a4104130144a040515840c00e44102074100c0c03c8c20f0b1b480f0b40504081560520403e40140120007120345038044d20343d1900800c1c4d07018030501a0b814038840c0860103001d900d0f002200b0709584900c080103900d030285040410b80e40d01d080d121015003c1e007c0001c2d002d010703450407101c40c1c40d81544ca405c1c0d84154549068010071040340004e0300f180c1c100c0220301c0000c40d001d901e20701030b08140340043c00d0035143c0401701308044001815000b080d030041c0320400202a01c0000d04070038004101740880d2a95421403a0b48030f150003580001c0510004810070103028135400701e11001d0300e00030740c05d9480880e280c04842c2e0fa11035135540070408a41c0104401e142d80c50013500700088a40384d032300c005403400068002110603007007040070a4600b20800503020b20985804c1150241c1c400c81400d05000440c03400740d000e45000d040101e40406035800080079012454181d0064020b044a614000e0302c0e42002d0491a02c0452030340100c51050b0324041c240c0e0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420369991 1250 420368741 420368743
    0x203090c1318020d0f0c1d01140d12120c050d150312080901090b0109020a030c0908030f090319050c01110a02060405130e0601090f11130e1b07060b0909 67
    0x82c0c4030140c000e0030042210919424404a0101c0303120944400030b4100d10640001e820341100350042c25480518408511840001c440b0707914180e0001402201581c00d9401d10380320480302010150300092003a440c40d81259081e03890300e485500039440c0c0f44c42e02c00d24050607500007018190341800c800081156043e042ea140200c41c505000107807007040b0044201a44600c01c00c0e0040d0b20111420010500c0c80740c030796130102d5010302a00160304158021803500c4407554503104206003c9110310740041050700d001035240d02d80c451036480b001e40d1600002c03c28800c0d01d0411143e84690062203240a0845c410b01345070b030301c1d0140895514009101f03840000d440ba4000504a65110780003000c40703181c903142c60704101801d00c1213640c0b980c1640e01d5000e80c40301d40c0c3d02800a01d00034440e410000c80c100c0e0340803003140211140b0300070104080c00301303006928003407803841c20100654001004640701b5860b025021340f03070406000381c202a4080000b82ca0001c208864104402c811001e660400540d19011100f03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420371241 1250 420369991 420370001
    0xe030c15150402310311010309030f050309030c030408011d03131809020306070c0209070f0203030c07030e030a03090815090d0305041b170c01032903100203090c13 72
    0x41c46203200210400c003150714243c0c1c020700e5000d070305604c410f85103d110300c01008651500d110301090520040410030600c0603284002c0e5040c4000d03c0c003085141801d0340e01410b009080d00c40340040100c08030021307403480c5003001190031039216841244e844658402c0500c5c0a0300301549030403015140a90303038100700c0e10000240c1d00074076002c011040c001c3d0304000ea003086000d581000c6001068490210703401680303060ac942e0740030712015950214090440d006001201d50301804040070454249800c242c02540442030b030f60484902fa000c10b9542c5040d00b000c0781c000c400c00301c0a640c50701074184e81208040c2c00c040703034130308a45d0024241d031800540e0381007240380140201c40b030100d83e0b041900040307100d511941c88654454440c00581c0c81c101140040381842d4180d41d040600441c000d00344001c0086402c22880051391424a810b0201410b5000c81c08988548001c0c2c0e86852410201c5e414030f10381d0244000074901c03071100406c544034903107400c4450355034444881a501691401101c001c040801d4054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420372491 1250 420371241 420371251
    0x10e03090a0b09060904090b0618010f05060306060d1437020d15080d0314070509090414060712140103111203040e0c0304050f070f140d05010e030c15 66
    0xc2071401610700340700a00a548800040356010a00f008217401c99602c03072083c1513605010b60407010b900e1403c4024000307a0b40403800e0b0800101424001005104d19042d24601900d0342601c4854494517220003042040c0a85003c8400480c1480741201001e18405c42d2284900c2415840e9900104040c40303d0a038001549101c07803500f40c003400c1c030b0f01c09000260002c0810000359100050b19000d100044614058903030001c000a41109680906403545809a030038000c980311807245a500307108002410703a100d6074803041d0080300d0910010b803e00410414401030010300d00b09490191406500c000e240708092440e481c011440c1144000c013109224561905880d07001c010580041c804c2070030030403201c0c440c1403a460341d131008000206502c1e00b51030b41240581910203466440307040602c0c4c101e051003040c0a140c801a0b015010401044003150b00382411100c000720842c1c00c00070b031b800c0451a101d1840070003074004d60038484c0c95a400040003008100040e03248069591426140302442880784060b90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420373741 1250 420372491 420372499
    0xc0c09071d060c1011031801020c07140102070e010b03010e01080606030a1b120807140a0b040303090606050d03021011280314091f1b0f050c1509010e0309 68
    0x302400242046001030052004070780c21100141d0060403100c05689101c494100d4150011050000c1828080118805501e5090080d420b003060b00035940e940ba0f4150cc9007000c4d00b03811410000859000f0701090010700340c00b240b00d035000c0d0303190786a109203540280304141c0100e1054000190040000c44c00c14040d0300020054404900c96460708d00c1110f80501d0489011510301d007000a03211a610f200306040761254070059101d0b401ca08200c40010f100400d0b41001e50400780354480060085641903910a616080003d02c010b52802d20b080180600d07004960450f50307400700c4806264000881d003074000e00b860002d0060540164240c6020b005182000d903045010f8181d0b003c00680c80c2c00c2404424030300e49000a56900011524008a40d06550704e20b11500048240f84039041c0d82900c01010403150007052241c604030300c0c080c202200d0182d4401c0c0412655802d000680c9209400316071091548104560003203010b00c4542c0280c00050307402c02c00ca58a0880e42482d444004000e1b0380032050010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420374991 1250 420373741 420373787
    0x906100206040201140d020a02010b0f030601031505151825020c0d06020f07140d090308090603060a05060a0e281e090f0b03010b04060b04050d03050c030c0c0907 71
    0x143c01925501000188294040b03418448810000c4240c40a0034201080794004190301d80e4403801d01c150000b2940306070303000c1d0b04400018800b050880d01500b51070a40c0480002d8240e4588030703540200e0590039207a41d48000300f00602c5140402001841d40661408203c030351081d0145450244280044c204000140e0482124150380e840e2a0705007901d0640109001340c81d00c5c40d00c01c4040240d03801801c08a032000c00310000c01b18040c0e400c0001840e52216801d050030b845056464003908c40c0121310b60f292041400000103000c03502c6030039a440042c81d002d40055201c02c141d00f40901414084080b660090344070052a00c5120402e00c0f610070b5044c05002880a403908007030743c0c498803524041084d10002540140043c01e45402e10402c8500c10400c0c80000e180f51400d0b041600b5601c40c450898800d03411700809204c200c13141c0080b1403c80b107040b6003044111645103400e958600504d0a400600d000100e225244c060001c03403003807003205088a010206584056080d143d400c081c2e86414980100c007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420376241 1250 420374991 420374993
    0x90106050d020915040f0801050c0720030a0305190206041a0618090105040b0105030a030f080a0b0a140a060c111005040504050a0605040f0902030c0f04060302090103030c02090610020604 82
    0x600040064107600e081c00b616084500004c110006048410300d40f0352040000c08000c1d07000740702d58032006054818000d0085007000c0588161500070702901030001c1000b10380c24102c22510a00760444644081c094a0401120381406402034020120404081e07100c5009103004078404901d0700d01c2258401d902c909a40241c02c0401d8068800601464002c4104900d820604045482d00c52240610000102c0c691500c2d1401052a80e0107910070381c007950010500a0000750816402000807042e45401c2d001070399104508006132035100400c0c1d4200100840200b10860300082080d0b9003c020740d0240c896983d1140110f41100c03050601404420121181c40124a0724030402080403810b442d00c9810552960001011110150f41c11032440b6034420781040a814580910a031860707401c0010003c0344420740120f621460240c03038849c45455140340d1510340342c1e40c50340103101070358003d03060000340d6031a403401910340071103018140d00c11440c980001b40c0750b16045001c3c0300346900d282e01910b12900c0e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420377491 1250 420376241 420376247
    0x20304031a0411030a0b040618050303040b04080d02040b04140d032106050414100b3a020a020f21070204051305061f0503160b030702010e07060309021e090106 70
    0x14004903480c007695444010319139000c101990402d400362440480e282450b1410b2004c9580c16170346269044c0c6e0150365040480d4000c425698000d401818803015035503280b41c0424103100d02990824101e01c040380100300b03400120060001d80700078003202d501224046c0c2c200120201e81c10001400a0014480044c10f44c01080c10041c8801d0b00860100307aa584420001c2c041da0b0300c1d909000390714003590040003c800c0300004100001c0801d0401c0503d00482c1c140500701c910888a1803070b1040c4010b2004410921064100d40b2141120f10310844d1581d40c0c429000b52034120010089440d48210400e0500c01d001c5e81c428003005130b0603850380c245040750795824400074103001400010400030703010001001c03c1c8148900c0e0b114400c0d9a0020079000300400034a2400b18054020038000c0e8400408a041c0102e03401c1c00760213940000f0b034515183c4e0341e031690480c0500301c040502c2c9a00e01030203200040a542540008220302d01c00c0b960071065402c0a80b07240700c042040d0264551000900b0f004000d1180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420378741 1250 420377491 420377543
    0xc040501050c0a021c05010b0d05340e071d030703030c05030d060314070b0f07030e0a18020a09090207051c180308070302060709030506060f01030204090c08100602030403 75
    0x320540039943c40c00c209400141900703001c001440c1090325404140e00c01c101007840340c0310340c0307100441d100001c1e50310315124940c0d1044141c2290740c00c403510361040021260449017841601c0040021030b403180ea11410b032004009000d0714200c011490100051100c51140580c1c01c11104002e40100115855a14101d8046e0035101041c0c071a400100f0103903664440500a20f000f450007042640580342850480c1460541a50f01040350b2040c140310602d414a505001c84400c1905803a0042ea05104070700042c1d514202540900000d12896080301e85007020b503009418000f00075160071030b4542c1e55401500903407142c140002c115400c82e41d0294034042e002140302c07050303580503d00080440c8108541c0401d00865070001d9641c1c1e00f000c118003040590402105602003407078075025210394510703076800e5a50034000c2c1003188203548003c01c40189900c85e9041d20300400d8550024022100307142c901424090003601c8038817003d107211a0100d00d1707d000004403004c07254042d102600000d00440c1c0d90b05051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420379991 1250 420378741 420378757
    0x9081009080f07030309110f090f060f0d0624030201480209010611070303030506031f140615120615070c090b0301050106080106260127050c04050105 66
    0xa00510a01c0041c2d00018007401c00b080c444c3e20005542c04c1d0504258004608010b4840d00c6455205403460280c2c0380d0080d8144c2000d02001c91461545a103800140882c01d60b000030745c1c2000c8041c3c5c41c1c40502050b50054504014401004c000c00144a000400144414040a400300e841100c10b10b001001340040103010303a480104401200303d210071007000031041091100040f100c03006240b000d529220b0716681c0105804e00300a42940c01d01c801d101e8440300f40e84805024540c3da00001061034806115940d059245010719221740084280078600804441000c10515400c80c4009103040c01d0114203000810440740100c0d041c9040c0250f101e085002c010245508800741624088880c900340d0701800e101d620501b1001c41e110f04103d07224084403411a07200d0b100380e0500004104a5070400525419500c00785400c1060030349a801c0710304000c5091551007080d0007002d0000a00546c00400c1c121000c1001c0c5032a0290041050481c00b96101a100144403400400c400c200942c0102c005083c1c007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420381241 1250 420379991 420380003
    0x1060b07080a090302060a022118151e0a0806040506031c09030f0803010618060903020d14100c02120903060708060307090f0b040b0334090501120308060109081009 72
    0x200713880b68042116504100315600241c0c4c010f48155045030071050f10031650003035140e01c5030b06004c0103100e91100b50002c01c111074020205111080e800c0c0010800f1030710200c04885050012060f04108400907500c0369031420001089540410014546800b072640120401001404c804511065901200200b0031640d400d1000307268002002440e508648085c40d1b0241c01d54903202d40c98110013420160000f048000020003044050050603088003840c9e040d690140c0d600c19400c0c00304e00e0070003e0800001384104891180d0380700d0603000103043c1c00081ca002c00c0d40e070a4840315030a41a14a03980c0c000c1141d0300e54190040c8000a030f5451151161030f40c880070090440380d440395140c0405007200c4e581d54090151584a54600240b030415020f81d2900c040b0a40080085448100c40c3d84002210118001e0242d01d00d540d1001c44454185507031006420030001c2042607581d030b01000b06004203540f2089000c0b40516002812660181640508541200001d082241c84a5840a00405120500705d42c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420382491 1250 420381241 420381257
    0x5040509031b06010306050c0309120f0919030203010f02040509060616140706020618060a0f020f220b0a0c1b03140c040e070f17070b0a050d0c0201060b07080a 70
    0x4a006001d4000380800d11980142c0f003194198100b8500340c0e6002000100c86030700820502099100000385100100e80c03941c089525a49005c1811500384224504d550784410146040c0000d144101c4e81002142d1084008006041c881c00103541170780981d21449600c5072032840010700a0800f900280107a49440702400500007441c0d841c10300c88112442d440800d68051502803010580410145401402c02038000310341c0034010b410f00d60740d101e00a00750a100c0c1c5e01c5403140d40c24406141c0507641d1007000800c985440c0c0e0b03d11249003180304400780420101c41c08030b030800100001d007913080324210390165842000c8400700c1c0d180c08030082c2c0003084290203070480c41b80c0000491016245283c0900480014000b05104082004240c0c0e001c010304000d10303041580d0401059039220b400000301c80c240f00c600c00c440131030103482c00e0414185a104188020b00001d401241c40e500400810030300e102200c04202c159180c0d10100d0032500103005d8030300364100400030a800315661001a151107030641ca00010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420383741 1250 420382491 420382507
    0x302010e0f06040308130501051236010e0118080a0503100515042402190204150b130b0403030c0201050c010906090302010b0406050d1104020a27031401150504050903 73
    0x30303554440c0d801540e983c0d00106d8100581c2c4c5048a000c0000d280034601141042039412001b5035040e009450001076a40903512790304a0100e40482c0c421010350404421441400d010086001e0141550844e0603540307000c29410000c2d005401a5401d940c01014007801c003241e020f000d0362242d00c040d2070301c03202900d000c400041c0c030b41c5d442c4518000710f21495040c035110342c42d2080709202c2101002e88900d0008008a000b002c1c1580000c0090300700d64003401c5101d140c20f03240003040c024901c2c1e090501c0300c0c584143c004202c3c0d2040704028060b0001d08091800141d656501001c518050b03800000e000172420048000958818006410620442000000c0b440f23103683c0c0346421101b0440081780580d444040d49200d9113060301c6108001c000503181c03111040b007940c0d1000040d40071424118482ca40c041500c0301c0b00781c41400101c3c0c039949521034180c08680c41510300d44020845200c12100e21b08480c07104007032810180240034281c0b6804140e0310707110742000100800340030000d0500c8220f21090201c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420384991 1250 420383741 420383749
    0x405030318122d0903103201241704080d0504050604021903150203101a1c0b09071d03030a1d030106050607060902031c1706040e070302010e0f 63
    0x4003c2c00200d0441000303250100c2c440c820000500f00702c840c0005820700240d07569407004100b04021110614000070b060a0003080d0510760001c18203010f00c11162030140c12018510600c41d0350680e00e103800700303860000401c0032004508040a50803800500858a03035000c9004001000d0b42041c07254020909280211400c03404468040310300b981c40e13511070000d000550416041a54015100070b59011007281075442d54000f500345030504170710407603001000592100c8606908800f07011940910460240c2d44058801290031000d074038010380500c0c01600780c1c0708035140702c0d40100c1e480c080c18a00d03903550307004000e0703a500500b46002d03520240c40c143c2c01c8043c1d5405100408055000352548201d0701e010070344060740041c0d081e24003030103070b80760003801d0040b65035020036112416071024000c149001b0920102e81400064548100208404180d124415801100c5030130301c2001c90310880c203603a0300c1d04100410795a510460880a0f00101d800f480135512440101d0700d402030140c0070b94000c050301c1c0082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420386241 1250 420384991 420384997
    0x109031703061002010204060203070f14060702060901050705040e01030b0613060b1b070503030724110306010e0406030312020a140a0507020a06080c030a0203040f020907020f070e040503031812 85
    0x50000d500208000c080c1c50401c00c9090414442e1000710b042034104035019550348111349000c2d00c04e50074175115504028952005181d143c4406090f580c140c1094680a544e480c015190b0000f503509010005012a03c150709550071a404041c440e8800e91868480b0080f107000900400e8001d603501a010926440c18000d4200420b44130f10403665030100c40d0804052074240b8500e16500741c1240400b000660b42c00416114400e400c0803519403110140c0742122010341204401036551070a00f51404e92880c080405544640c90070303213505500c4880300d010001201d400c0d001c02004030f800c1d4041c0c602800555409401f8400542c14260365041d80c0c2c4621080b55080402e002002840006402c011410030360f01030001080d003401c5c61034603030a11031980c02003800000d0000000e144d003c0002428095120f0840c04d00c5500540944401d00344000c00946a002c140c0050089129006002440c10505407101c1c0c801c9810402075803e40e21109074581000e21141c450036164800e001c03c100b4a2032400c002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420387491 1250 420386241 420386273
    0x209040b06031501081b030313061205011401170903070b0112030f111c03021908010806010503030f1801090506031608240f0301180b040b010e07050414010903 70
    0x20310655031030118205803070151080c00d40341402c0018801041048000611101c00540302c504840c0e149400201003440c60068810000c8a0301c079035500010901e81003003580c50f170008039400600003a84c807000301e103000e9207910803d580012007000c0030503070031042c9005e165008540301003924a42000b035100e10601e0741081e0406045045407400d44800c02d500149024001b80c1320741400050741940c0c68400340c5603e901a0748114940c0700303c2ca101d80302072080e8110740d04000000f10b054405030301e00c407004007800e509015214451240f00004120303460b00005070f829480c0c0d5089041e280101001d20440c60701d980c40c8500b414498003403004502d07035589201a6201d10001400c2e85c0030000c80c50ba004101240c084c141260320460824003d41248007142441b407e22030646202000c3ea40301070111b401044031b04000020a40c82d43c2806007040240910b250241e806284802030076600d42c44214440c000c15214640407450801c0200050180d42425480144050500b01041c5917203440b6884203400d0150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420388741 1250 420387491 420387503
    0x120c11060a0608060103120c060e010207140c030c06090418080a090f0506040e092a1206130b0a020c0115030b0f0103030801090e010b1002031306030504080702040513020904 76
    0x120092121500300310441d401000404148003032498050140e464100c1800094944000f00c6100c0b0034881c0200d2402035101c0e401035080011843c9000524000c2d04450800c030351100b46400c080082c0c1000040c1b50804007030050280c010001050f04100041d440b80d122543c109451311080c039420301181200d002c280c1d0168403140d95a55400800808c0c004081e004481e00e24400901407025480e040c09407009d5a00440c84481a51a40100307207140091801d01100c06049400ca01c61245d81b9030f02c0360600c0c001055400244410f2416013450b210f441c12620b40038107000c001707080350100300303003030034072070300241d0140005281400c0343e2009400c3d588a1a00d00c1d82410001c0d03002c00420055044199000045a010900c07550540c1c0d001403143d28184a031889551f143d00e0302070060407084d07010034104203004290075184084450082e440360084480070000c01d21074840003800d40d009000700741c420303a88401490b140036400e500b007000901000e4056404c1d500305108500041e10b4600c00307140202d00440e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420389991 1250 420388741 420388757
    0x180a112e0e210a020a1a0403060e010e011b0207270c211b020109050a0303022b0e01060b04030305040e1306090c08101509090203120f0909070c03020a0201030507120c 73
    0x4014802100d90300d46c0f110807043c040e0481425030b6603d032803c3d54140c3c3c0d80404003141301441c0111290141c000d0801c0743e03026520386440d14034841c5c005203080d51100990780964156694030425906d0f2600f10308419002040d0420301d1180c41e0794242d22100011556041c099040300310040d0120b0b0003503900c2c072403401082c0d07034101c500140810507001c071120500c60700c0288104040c4c0e54980741c81300c1601d1002030905802080001120003054881c50000194003144200700c2e00320403044001e4010340d5503010f19540303040303c04240218a14111015a9019110980303000d20b0064200c180010007419494540d500c01a608009011805644807890180c0622100c03682030000399030404003154425100c1c1c0e4500018089134440b400c4e1042c08030351000000282d117040d5400880c0c20a240010109000503001a0b843c02800d45a8040d041244055400356003030340c3d4444050362003038040c60300900942e01c41e02400005602c6034102e5a84285249006052034403c02c0a100903210840b2120340416904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420391241 1250 420389991 420389993
    0x30106030b2d04020f0c0a020901050111030a111c030f0507031503060b06070807121704210905040609090318030f0209180a112e0e210a 60
    0x6008150020204403400903140b0390700e0b40b801042a4007901c421018004018201d070b0240d50b2903056819501031081d405998600c242219a1540a8420100d100343c1003c0300100d4654402c01c03003403801507000c00041d841d00040304010744400306040e07104844c6205082c0d01c440d10b88002c2c19400160400c1d81c40200e180ca9240e4403c1d029a1001403801c01014548881801e000b084407228804490b00003400003080068038000ca44c192041c0340c03024110310000205070b820001c400602c0c1100b01110b94507040122a5200e901416860039140139205003030340e01e200c1c018180c0c1100e0300001c400c0213041c0036507400d6480001c141511074070341c400030341c90769030b1443c803410715422400c200382c1000401e03444180c00d130859440701c1c1030984901d8042c1c0110510750015203001ea14284001981f12180101c803110b5842e4a020003d04a06a00c2a405001d014044422256011684400c024020035120000944040c0200c81c0500c00c44c1e50719500008996400c1054004030b500741c004400f07034401404090804d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420392491 1250 420391241 420391247
    0x70308391314040c140d0b01020a06230705030606030414011b1806230310230f0306040c06140d05012d0315092f0907020f0705060c010603050303010803030106 70
    0x200e00481400e0244445585c4e00c02d94100b400c903840c0b00e0300a03400140c00015940101c1c40d0100100c1c1c010700c40c502c1c013003c0f15102c04042c0c05000088465172000240382e51200f40840761030009951003504001c00380f021900050b0b4600950510306000c400004081041180110703400d03c02d0000000800c02d0700d1040582100704000c1c04001d030a040c00c0003040170001c0e2480c04004c0c0100e40d41100c11003008070100d2403040c918aea00c0702c0140f031045403481c02e07140030f6001c2c0c0d40b4250900d80300a1040b261071920101d5030401140440c03280b034100d000c0040303142c80e041e400d4400040010120350030403400c014135401800c3ca48182c5010300404030000c4040e030b04002240000c40380142c480c06a01204900410005554000f4001155444003010500d10800d14100d00032035002c648440780031b4050b52007881500c1544c02d014100200c202e403440d00b50f4580003001da8036150014404040c0da00844814032903814044000c01080085800010b86903903640c5540e402e5400a070030800480d04000010091154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420393741 1250 420392491 420392501
    0x11120708070e0d0c15020c060c0106050307120b040605150402070f0606050303030103200105090d030203120c0903032704092003031306030f060314010207030839131404 74
    0x54554410074255500e0711424180075105505c808400e80000301039140c0b0a011410b405034016254546901140440364080c1801d8007620b03002c2d02c10040e001440785480103031104100c0d0040940800d507207454030f91601410008041001c00f0111101030341b0240c0781d0b80b005004071030289188014044c41c41c03134000255091544042e109038014001880420b200c924062035006c2100d01c80d0410125450041e02c4c02d004d1650201c0d40203c6490820052640110041c44943e1a030a846d00131542c44604c852b4103405940901601640280a501c10034194698091101200c02d1002c3c000c2000c07120010701912454001205c0d40340c6402e80540300300c032a0040302c2d490600100c010714184005c031010074250302d00e184640d808054482110802001c4982c2c04000a1034101d01543c0c0320a0040c18524080e500800d82140007581e648002140c5040c611b901060180450103402c00301440c142c0e244520001c601104001c030601001400202d541c0c4ca04200000c180d402040c0c90760714080c10400085070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420394991 1250 420393741 420393767
    0x41206060b07050303190605030d03050a150f15050702060d060e13050a1101050d09030504170c0901090203041b03050c15030907030201182601061203050a031112070807 74
    0x2020310640d00043e00220940e07030301c000035841c000040a0500c0380a0040c3c20240e110f145c1502409500b0404594950080345c49080050300501c547d0500c00c0d4980c2da003d96030302c21000d040180440c01e0042d100c0c0b034141c01591459910f450b60a1100c213400080b515402622852440c0380d44110402c200c446030661558000d180c40c40d1061101415240c550f00c511840303800a01207030303a1b102c810702175031b0043c000c0d00c03044403000c8820070820300c040c0307000780c100d60042c014040c500030620030601c1000c2001410480950020300400b0f12a40303040b06a902940000e00220350010021030082e0362541e0398000040250701a40081c01262680001d0207010f05171000c20700c14010080040200e50000002c2007022664280b0700b44200300c0184c04400340b02c1c12035820000114181c00305584040200b441d40245e80d1074000000c100e615901e08585940304132503040140484c1050140400b820f01a5100c982c0e809100c3e00214601000c00d05044030f44042101c682000c145801c0a00645aa0280700c0c42092 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420396241 1250 420394991 420395009
    0x2330906040f110d0501020c010e160b12060a080a03030b091b16060b0a120c08060910090c0b0304060c0306081212040809101214070c080d1104120606 66
    0xe04254540706410482d045001c1d2042000c06100c5683c0d07159045030100c12600000210340b603036484000c0303030301070102078203806401e12442c11005455506c40304480110744200d0309080c42d040d44000b1601e000d0400a110701d61201032800002080082030211107002d0f40f0940e0001001c00f6008200070203104090301403140382114005048168251800f181c1030710f0114001034003150818504038015054910340550006844807001410854243c00d00030a10f100f0f69140d985191140242641d0b00d804844101956104174980350700c101c1c20f81c0c001c103441e500400c0c145071a1515020300c203c040e841941c04440040d9516402076100740d240c480e20f409030080c034028010302520050310206031300400b1a0503462050503004102080341c1d0800b00c0780c44150143c030080c1180b03a02e403c0640812010100441c4960030031001c0141c03500d00c100254440da90700c0c0c460038462020354031181882c0d00000b01a000c5542d403401341f419003102c4400600014030641d07054007035411807842d00302c095541c2980148a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420397491 1250 420396241 420396253
    0x1f080c0306100c02151605011d06070f0e180a0f110d0b04060512010b030d02010504030c03050f13081f140601080613020c010f0b0f030606010f023309 66
    0x410b40e00c0c00402d4158403428a84108414100e00008100c041034500c2496942130000d40c0d0610b942124040740c19160146000300304041550744010400d00c060314084130203800041c00516410b02588203410010360614048860b40c42040200307403002006040034940d017508070200252429107029140b01030032859810302c9050030010f1400d40c14016480c50703e40752501e5500051894139241d00c070600034180100203c1c180389181902c0c1740240a94540310b8080c0c004da030b4409201d58014082c29006a80c1551034550703075a51500e0803541350300300d08100d4522440401c108441101000fa04c0340242c11400003801203a900b840480280c0c0810320707160030303d5505210381c5600d142e6401b04200c1e4414402e0a090390076980d084001064039407101a80005180b01017010541c541c01540074195120300c04004218202c200710400c05030300341c00e60140d6815800a80020803035446151020302c00845401110712040c0724a138400e4003502d50b80440b80c1d030581101c1a0742d002e40c82c4082003e130010005d1020306a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420398741 1250 420397491 420397501
    0x30f1b03091515130c0201020d06030c0510140304030302070206070506160e0d050304140406080d090609050a0510110f0a050a051005010b160c030f0f0203100506060702040506030c1f080c03 83
    0x1248000b5008400820303903100402005c6034003e4044640d0101d29210030055030b1f80300e00d00701154100a00cd001c0c010304560503144410390041140c1c155201c05412040d08668840c3c1d0102c020354419501260000030610841c00003a41c10031409000d40101e1482d07400b016a456002070003042190764003031291070000075850114070301104071800c1d580c0e4082030140c1c00229070301040103000b00e9800403113140300c3d42a5140520340d0100c442c500f40ca07019502c28560070396810800052145c10300441c0e0307001c0a01c9050020041c050007007218266049803e031043c840d41d00e100c403410924030200c20786207a04060300b503a04000d401c0c000ea001c5407400c01e508114a50504910407994000e40c030104205611448040e4188022048184000d69011015403a00441407800d4182d402d05c9040c103e01920070007c03802d545c015980581403258401500f580d08001d43da4082001924001d81241d8050007004a030f14a5900c0300413010b110100c0400c113402070303661901c03001048000010b04585c040c070810f00c02c2c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420399991 1250 420398741 420398749
    0xc030a2304090509070321081501050405010305040f020301020d021c0e07061202040305033f19090b07020c030d0305040506061302121f0503060c030f1b03091515 71
    0x50685000c12030010f00c5548140c1820b02e4204a60005020000003840700200e2041800f9030380010460383e591120303280c582c8100c40c1c42d022aa0b05943e070101c0c2045c0014800713544254403507a4003501039450f040c604025a00801d00320390289050000c40768001400355144c000800c0300542e4a0402c8008006032070100804030f442e469540208410083c03900e54801340c5038807a4044c2c03005175803c04203981e030360702c034000d10010703c1d400800304107030280d0072031800c0c0032480440381e541d0b1600154048075a10560741c0b1051501c111050142030040c0ba9540c811180c08a5a40300c506480341407240c004041a90700380042501d84117510500300c041508060410000800200f08141c2000060701d0802c5001401c0f41044040e01a0710891406120300004201c0d01d04a43d0040e0350481180a19480c1220744841c1415101e0b071b41100c2c05c0c0c1c0c0e23451041021a00e1510521100c1d60f202141d06180400d0007044c001410b000c0c0d200380c503e82e1003a40900303d59080c03440414103840d0040024003800714450302400110f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420401241 1250 420399991 420399997
    0x30c08040203120a0c050d0f08090607090b2a0102090f061e09012606040e030909060625240c0f0305060f0a0602030d0b06070c0902031b0c030a23 64
    0x200f18280114160030402c1c01400e14000180d40442526100f078118400104001d045160080008110102142c1e8141c8041840307030007004599610200c0605048580f11954044901812503021800818014051f540051a40e0315203c1d0300142e5034128450400003011024445240b241800700001a810000c94a2840c4014102004c464452100070b0050b1b801d0400440310941703441e00d42100c00070034164100c00d58450801103804004609009100b15070320302400200c1070b0012848004100c103858240f010704200d0745025000c24210500943c4034056044191040303480c06401c036038681d1924810102d0f981e0f0040c0c0400d0401440e0f1b1a0540100803014901400c014107686002240e45030b103841903021b0a500300030b02000f11080d91510002c4da2642b001170841c00da58608013142400d4500b00e0704640303503540c0009400e40c030941003055010082d0300c00b038480580040c1c4040800c000c4803c51001d0035140318a034003e1a03c03510a460043d207135154011595403000340110500c0220f441c21000e0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420402491 1250 420401241 420401263
    0xb0406030c1e110607090524040815150915040b0301090b091b09010f051201141302090906060619030e031b07060905010c060b060702180601030c08040203 68
    0x401e030450085000d03210602c41c112001c00304000c00c01203800880d005100d07031030500c40c15011941e01e9913034000122440001e600819500c1452501c501c1e480011000b8a40c4070f18000038003c914169403081e4036450172004183d680c085450f40305c1041540c50303a034100700050440503a201c0181e413510f00520f880c001d80134074030148150b603075604a10842e2425800003407899440648000c030303070409803016603903a44c00e43c02280c032034000796110a00a05003146001c0c12a0034810100740824100401c00c05506d0307901409100a660b1954804441038031800c3c501e00032a80e0020407443c0e40c01c14014060b24135001000190180e0240052041d6900e41e601250301c00100d07829180045001c8032000c4020f001000c1810440348400300d01d2107043d001c2e03200b556081400b5081150074003a520b442c113036502c002038440e1502081d404158900880c4064000809285004001901e0080c1c80d80c0040d980c0750980700c00400d41500842001400d5030184540702c1043c60905241c0703101d160640c000303584c1e12a0841 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420403741 1250 420402491 420402497
    0x1060503011a070b0910150807030611190503060901081609020d0e030d061d160c0f02060d051b070c170712080d0606030203040218070905040e1c090b0406 68
    0x242600c21030b40c980181c8000f20341c020041c210b43d0401c58980d50b550069084c0e100e003c10320f40340301c50175140343d1084140101c035038002c0a05030300c83c03450310380c10700510480a52000c80d5008005580c440c0300c1120940c0302d280150b484507a01c0b801d082c8140009000142c12800b16a40410007191800040b001ca00c0c040382d410200141c0d644180080c404040c2c4404201071541d4030011803403003c5a031300d5030084c20940c0c42d2750341d09803100039442140d00c26507003050340c043e42e62104040c1400038451107418100b001038060403281a0000c107035030107d281940940094201903503640244407650640441310b0b840554a5248941400d10a4031030040e050450b10600580840041c0b0403140030205010f242c008003008108650325820500b0300e4811980b01d05940c18506152138804603205000780f0075203000d66000ba14007a01c103102c5807280b82c208440500f0103401d000340014006100d0f5075070b002c0e0950b09420310001e004080d06246109000c103a5022044091120071481405103114076020f036012903100c1d20f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420404991 1250 420403741 420403769
    0x14040507230f0a020f0c100518040902090f06121b010503040c0504150305061e0f270a020405060a0e0f10030c0e0601021510062a030918050106050301 66
    0x11840c4066100c2c0c016031030a490030204005a04680228081c01482c02000039204040300341c008002126600091200109405008410b52850715582441400801610015645c0c072640c0020310b54850458000e00c69082e420200046820000da1101a2400b00e10042185d10148144201c1d28402e40103528104040400040c06001014103c200140f1010b00104a180114045250f8819540c0810340d018070841002c41d90402c89001034079a0380114581c0f00300e5a03119540b446111100260007110001d42c2c601d4001012840003030180031001d4a02d0050002c5034040c410b0006071080101500c4c4203942c2c80030100182440740302000c0c0e00808908034607401d581c5c0d05030380c804281704a070809080041c1d0751402180d25210250154002c8100740c08035a034903d4050310800f8001d02c1210000e01d05101d8540c100f2000e4010803059000b0001c0723882044440281880c03407550b85485d480e098000a00c0703140e04000c10303074041090405041081c07006202c03640c100700c1c0182440c40188541140c0213914 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420406241 1250 420404991 420405047
    0xd0207020d0b0403020607180e0c0a120c09050f090112020d0311060f1509060a0302240d0c08010617041e12030b01030c021501030f030c050a050714040507 68
    0xc90800380460b80e00c9500400741d410507080080d6681011112880460750342620680740d00c940000600c200c1c0c902058000f45656805414807041d0800380341c1406201c03605c0903d542d580d0250003a110204407035516a41c44038036110801030102c40040c1b565005101102c0180642c1305070783e902404554055540b5462070809240032500c4001108072508180a201c041c80441404d040c2c2881c0a11301040603030a4000c950400c00100f1030302075864ae540019800300810042c1080e82d584180740310034094186040b01100b041c0304907a40003c6101d028207684a20300420540c00546d210b0261065140c07484020119198001190601500242c04e000403818214520103448825812180c0d02c88a500c491802e00580580603118803401c032400b1a041290594030b01d440010751411600c405444003009034a1500c8400d0030030124807050b410068a40340c0c0202003041080b03800c205a114a004001e41e0b8a8403407111441c030310019000d403040c0d05080910100300c2c0d00401006a100d0640e00c00b0b0b6080c905 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420407491 1250 420406241 420406249
    0x101809050c04050a1502010f0b030d030e070b04080f07060905150d091703040b01062c04110a0908070b0702150a17070908061303050a0c03020c0301050406091b05060d020702 76
    0x2c552165502a41c02130002c00d0b4101c00c0f995130b040c0c00d4160b400070310200200c02500b4040d104003285003034055014400101210b486904010780c01d003000019106810344508004a4540c001d800c22041ea60100075010341d4003804000c051300800952034100309043c00e000000703505030141c02d6031008071200882c4400c0000c1c525404080040c1d880003810080342460070540303880c0d81084400381c41d0700410300000140035000303907842103030705080d00942c020090b021140602c0205501a00360b402540d0744080304440e40daa00c00034140800a13407512030102c0d00c0c2400040c0780c041180c102e00c0e50b002003071000c0801600c600c0a55604551511240d80d22107a90100459400c0500682424011a0030007400035090300305054078240c8000700d0680f02255184101455040048000100014010001e20f000c2520900c0780d0a03082d4824070643c3c418140800000b42981d40c142c4058494550f10040e610801c8580e8584036100c3c8100945d040c0503034038000c00202140145c242c1d564800b900081c0c46404c540e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420408741 1250 420407491 420407497
    0x20c0a0201050d021603170f0c0a030c0201060b04030f1202010c050d05070c0c0306050709050904080706050613060303030203160e0d0b0604020903070308090415030c050d060e150402101809050c 85
    0x141d41072031031603900d0f050047c00c101041c03001e00c6440c801c1e8404031b40d10705040c3e155140b1803180c0d50001ca01d004e030b009070210014450003481400319540d60700046800807103240284010341c000c40000c8840300b010f040c1001008040f864900c1176a00d400806c01080c0d40110644d6084400c2079000103099035503810980f03c0009515008051000e0a103011041008690190740100c40550341d0000c4140c4400030301415240a85000e050f1410501c20726000403001d40000d984804044c02d1580303821b007951841001c0c0c50b11600100e01007a00402000002c1d03400444844c1a50078504d403100070702011710085000e1000c14240a4141c0b114a000070b14076407940c1e0101c0704400700150440c3c18543d982c4c106010a03401003d5a584107600b018605004c1203a1a55100f00341c0ea0003076595440300f458030041100090103060110384070742d03d134000b404c0c0d008000d000ba0f00e40c0b000d540101c000c8500e803510401c100140d42602000c14450458010000041c070308490300c003510380c800340c009030f0364541601d0200c144c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420409991 1250 420408741 420408757
    0x90d2a031209050a0b0a110304060203040f200f06093d0908010c110d1b150b09010602032a0c030303100f0e190903120c09080709020c0a0201050d02 65
    0x2070402c0d89100c10031a00050424103c0e002c0d220040c1c2585440f400d840c2035030020340310000391170400d01c081801b10303000360b00658015100c0c00c2c0d9000c1658487d52132030039500d8901e4180d0001c80c108000c580d80ca0a0550f8103000c401c1040320039a20f4400d4840004039140c22a0341145488010017103019140c1d0180440745c0d1150360660300d50401107041c40ea0042c101c0060740074003240c55003001000c0e841680520003208944e075411003e04140d41101204517104d44242c81e8545504010649290204421503076800c20a204d0001c049200a030400c2444043d1606030b03c49011584208403110041c1402454980a4403801e640c120354194921a810318083c0d00300c0c000ba506000002c1402424010151014111050b03800d40c46901951100303880045075045411510140c000d00030050703040e00e17651103450418845d06102400780d02a02105007192828213045000c04c441c3c01080c00394140c104000340c01820408415854403425424403500c130000c0c841c0081c11f016000c07580e29507803150b50701030b54001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420411241 1250 420409991 420410027
    0x607140c061903060e090a0305031e0a050a0e0f03220902030108030306120d0e0f0d0c090b0118050a050607031110061d06010c031404030204020f03090d2a03 69
    0xa0b02a8010a201c0340c1c200441020119140c4400010340c0f0341141401440348006001034038050142e40c400380c0705940001d01c99014502c1c104945008103060110040c014003030840c0014091401e841c426085a10201d4403503459400000c40341994100001210100d409200e00b016511000c4600503a06881c59041040801c1c0040004291818000080e5215003011520071084000031101c4680320b52411a2076400640c2d4040150241d061a400d4940c0c108070241c040e400f035465a44520000e15216001804459101c4003052165030f07100825000000b810b4240c00a143c0c030b00000100c0c009814401c0501401001c604a41854003491418480c1e69448040d52202c171030b103288600c01440280104420f01844503489902c0c134602c0d84400e8401c0c44180c507611000415904c0c2942c0c4035640002080304881704020120050f1a60700180151115001da100e4403401c01f000c44601b409100d1801c41d0800518a4080000c1020041c02107051031680802845524450500700c9040348010000402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420412491 1250 420411241 420411247
    0x1060e0f19090906020904060b040803040b1b190b0a02161709090702060f180606010309050106051c0606050904030c110f04090b0f0708270c0a030b04060f0b0607140c06 74
    0x500c41c945d00149080c40007205c040000c40e40750380c0c02d1303c20340c0218090f2a5040d0300510050007801c00da280140315225500e0803103048882c0c0c000e115440c0c44a05040d0b01d6000c1c0464102804100302d1001158004c0035444041d800c00c0b0703c1840e285240d005648019100004851f00140c00d004028110b032000798014111700401d16211401075503510b4250b885209440442002408a0700c140c203110020071041d0002d003400341c49001c011006441420703001d070781d155640d100c0080c0c665030300c8001b090300d09014600602e410340d0340c1c2003d030100c1d00103600650142d09040e040100081e0301c02034a800456000c407081410085d0000031401a940e50300f03010390060b280401030740600258203005482041828401041941d0b150012510780c507054414000d003501401400c0c001071032218102d0064440c50040340e40898000000400550407903005895844e10301701440280100c600034405004603859090001c1d4001d040419423611850002404022910000c0d8511000c140240000c11500801b980c4e1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420413741 1250 420412491 420412493
    0x30a050d020f0712110c0a15140c01240602070510030b03060a0e0c010207050109211221090f020402070203160902090111061603020f0d0204081501060e0f190909 71
    0x10704c118205403110081001543c030f6254400700091180e668001c06460698490f141094020b030880040e204442032000c00500e810b200303004580502402860080007117401d0200c5082480a60b05084001d001002000414051903030000b41c102700700d40c4256031136a5041c0e1103c2c4100c0041ca003151506615002b00c0090040003070085d080640502c07204401d880d0f1085100d070059954100c01d1203102e000c914030200c100b02c1442060f84680d22030520007184607101d2110390b11121914807442c10140401c13003d040f9040350300307071041e115200c1d1000c0e10010003410480e038898906c030f902180381c02849a6000a0034008546040c815201c80031100e007a00d040b00364582880c803010350440c101e018000350262003c807084880005125010f2603240c3c08950710b165000da41200a5408540004402c850800049600340c42c1c5100a000410342400074162090b8110ba051403081c1040e03020104204142c00e1541e0281e039044591140b4210490340e40103190750444180c00b1058496000d00784036071526000d84 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420414991 1250 420413741 420413753
    0x111c08090a0f12030501050402130e0a020906070515070503010f05061c050a09031103040b09060c03070f0b0a1109211f05040c05041415240d1508030a050d020f07 71
    0x20140f0040e10103100c40da0701c820500049011300300c00e06c0410004241c0400545514148040d000003900c00c02516046890010506d50303030040d08121680c0d03201086024145032401c0c503141d0880305a2400b41c0c91545000b02d5005c0000c114060340c3d104a0000441c0c00340b008009013003002d081d401c0f041c01c1c8494500701000100a05c040c80341600407507440018400314031404800c031000e44522400850400402c0810b102d080d0f0020040c002c0309110810442000c10022208103000c188103030015a0980703030050f4060f007628500b00982c036004805101c00d02c80c1d0b5035011b079601c000000c10346803580f645804428092501c01c0364000c51010f1030071600c805d06c0c0c050b41074110314461401082c3d013a01c00c0d55990700b070104803800d00200301518801c04001c24444004003818410142c4003c28004400c0c4412160034000080024131002c802d000050301e80950105000c0c0c0e45402003d1107854070924a42482d142d00d030b03c1280300141c208140064074804070b84a41d41034800500b20382c500152500d500d841e1507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420416241 1250 420414991 420415013
    0x1a1207050d0507090605120604060b0c0601150216050f0406180603020f03060903030f090a020a120201110d02060109090303060b160b3103050c011506111c08090a0f 72
    0x18007516418100080c0c5580d01900c0a0b904440155a829142908903d401c110702e200c05054a07612503203c500000c2e40c003016602400814180324003411495141c10000109032510b25031810554022129a10b0b083c3c0c400c1c45004100d0b04199181c00c0224482d40002e001440c990308900000c0f26810300f0410445255444181134920998101100b410a0010140c0e15141201c070301c1e491380c0c4100002642c110785010140d401c403050108540000303145030300062007501e05820264200c50807110380400d42d03a114030359446012400c4082c0010203500c1c00d000751154014041d013035503a900c0c0d0082c81d0030103201764882e40050214070344144c3c454641c100c0c145003803c0400c10980f81e82425070b01280c4802c4072060320104030502101c50249003241007070707442900600560207409114083c407140810030300a00450248418040c0e802c004942000c001070040b0f030710780707400b8400c42e4040c0c2c4040c00200a00d80d484048010f5030700340f1008942e1400040d5160002e52080104150940307901442080214001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420417491 1250 420416241 420416257
    0x60f1002071a032505070506010603230402010f050c0a020406030503030603061b16330c050708221a040602010c031a040b240d05010801020c0303011a120705 69
    0x180c40c0b40000c4038501d07445400255502c03020040840061846841c910721101d4031180903090603800c007411611040d040100992140b008280c03180703003e03403080315040581c03a0708296204850b00282030a800080030a0403081030002840030025150345007034002c000155443e07038000c0041c82542d0701e0b850306c99240d8000351401030185c41464003013101d9011100c41c0109600c3c3d4520040c0c20712400c100745400c980d071031140c1a00e0740d020182003d1218000454404180e211a003440a00d8840380c3c0c17450000c642c0d01c10704038020020140442000141036030300b11200e5544100800400782005d8240080601e100c0e408020f01d0701424480b5040d164485000d002240c403150020410001601001d40a03030b07200071100c1c1c001c254059003883c444e10b8141c0c401001c10801401d85029420700e00c00c40001403510b042110100c24003c6025800d44c103c1e80a068098100c1c08000d600700620044501e42d6400180121901290552502401d01c800e460a4410401101c240141a400c0c5408007030101d5015840c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420418741 1250 420417491 420417509
    0x306090209090a020d0b0601051207030c020f032d04050406180509150406022a031b010b062506020f0405040c0c020907052208070602100908030f060f100207 69
    0x20014202c48000314110000380d4004d80b0038840280d1542e54004611402458513040c04414401d04201413401c1d042d00344914a6a20001058465528064070b030007403c0050705900d0b44100680c80c00c8103088002900121040d13035002c0400c45a1482a610f00c1c0650303040946c019141500028a0326044041e00c4940c1c1e00c0c420703042140d91285100706441c2c1086260f4920001078020108000400c960300400f0001d03582340036036183c0140d03070480c0c00050b8843c41e14012036602c0414061200450400c5024201803249c00810002d130724a00441c4090027a2440024018040d00c8030958031046030031441c2031268442d208542e11000d41c06000f215170024002d4902a6240c01000e0906a004454620003140c006048580039a507428080b10941e00c40c040503000309495130058114100c42c5100100a010014094403001c2c0c10040c00031302d842008440c40090505024440c004200b80600312a08000021640d035255a502c03c0412402034809c0c0740039400c58024001c2113100f640c0452a08180d41e9522 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420419991 1250 420418741 420418759
    0x4050105100b070201050403030521010602030a030f0506030604030c05030f070605010f05040e06040605070e0a0801020711090118020304230106080d11100506010c1208070e01050a05070b0402041503060902 90
    0x81c040640c03e01810400a001c12400c02c03007400424001c0740940b090480b4a4481c031001d0652400c0454034034000c2e0300203405640003040c00040d140e00340c010350004a00d2003108001902c0c200c00041d40d59903004d070028003803103d1016030f4070038041c00b402212141104401c1c4ca942e112070b51316000700144801d2160400003480aa00030882d03141c54016001c0384104500203103116122500c440c8001c22024190f04103002001c407846c0010b03116001c50a0080881500060f104c80c400e040c0800c0100c810603074548200960b0005128030101722050386e415241300c0b100140c882c0e450340707020702015070310303580da442c905100f078040018141d0150810800e803406032055070014048164155280c42d000784541000380c001000150350f20380940e003c250f101c401498443c02028450304c541400703002810342c07540056562401c00980640100c0c408680302420b18040b45440d400f4800205a4044c10fa00200110354603030201c3c007550703200e4203c00301081840894940c00d130742d60f103040002002007000480c05a1100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420421241 1250 420419991 420419999
    0x20307050d0209040311070f03030c150b090415020d110d0e0303061516020913061506050d200d0603021e091612060e1f0b0a050d020706050405010510 66
    0x44007440c1c0003940c06440750069460b40c2e40c0641e030050100b4a035240c1c9100304000051150401070000380214003c2d00c0f409401d0a9608000381801c103408a4117040034241201942140c8401d0401a401500314801d8280c480503075026001922440707a44501c810b003400100150a03902d1001012078400032002000038054101005859000481e05103600408180850304110001401031a6884003008510005441035001a07685803058a0040001200505820402c0f11070301c82c1031642844408400112032824000800503c500c003122012a922800d10b5000d0365076403c00004102c15100206440e05500c074200c00042c5000c1c84140d01c1040107050020f50500044002c1e2000000680350821319952607154134030050700b101c42c0004000d114000c402391203480b445007001038843d5a8501c0480e00344006508011451083c81d90f2001c10181402c0100b401c0000403280041c00c07909081d07803104520703101000240a1544040d200314184030130041088819403145101c4c6008046003c141c0f511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420422491 1250 420421241 420421249
    0x12020d020c0a1802090405010f1d060d030c02121507020c0418120212121603020a020d08060a0806181204060e0906150705060a0e030a0207181103011202030705 70
    0x1031101c0d480d0308440000014000d80c60a19030501400202d08005460000610080340444038264400e51005840d18024050b02310b0700c8107506c154064034441c540c2a0300300100000d0303070103c0840c001020b00103070042000454035000c0e44081c0309180d45059a03180c100c00503440780d101000b1070340d0200601480b0203943c0e262034103101b01d000300346c0311424025a565071507840d407074001c0d412035442044d071182c92300202405a0440040c68034040c2494500024181400100403850f01c11341c5034800d0500502044c040340390700042c0302d6956403051602c0911512500d01141060509030403110365030142d00200030780e0640050b442c0707604000381801c03100306a5814480849a02590207180c000440003200907240d0301d45200320343d4010314028140090411070340d040018507840b034202290641c000d0400c2003100c00b0944207240c184616a00514540655018025111003080c0101060340c40e00b540035104407000d0740e2041410403070601c400341da45c6d40c545040e840b4008804500728032038814000c1c04203c9040c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420423741 1250 420422491 420422503
    0x105041211010c021c1704081804090f024c09030b041401020906120f01051f23161b0b0307050306181f090b01020304030b19060312020d02 61
    0x401c0c1d406485c88180560b42c5c0566584003d550f0020002c00c80898008620030349030040c0120311410b40303182e070b1700102030000060380962901c0d80d115070300e40043c69020421440159461aa040300d19924034014460309161002d0001c1310151f04088040c80d0f170010040044010800d0001e01011107209008101c04540503825800300514800b0300304080303000642c0f00500781c05151f40d040f001508250507900400e4041e0400302e07003560218581410b0125070b02c00d9608a50162400740c81c0340d00d404a80c007020420018450815004003d000512030f00c1740340e49848280d5140040040c01ca03600d0a00c010888141800b00b9015140c16940c2500c0141104c1500c5400c0c2c1104c900d11038081c00c56980c40015145038000814464000d9071a803261208018006070b00b5101d5000b44031382c000d040555211041801100f50020240585040e400c02841d0ba000402d94045a5002d404480196552150042041c1d64a42c0241e007182c200702d07022041003101c0300c404a0031850390f0f00b01c038442c804892080365628 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420424991 1250 420423741 420423761
    0x121c05090102072114030709060e010806010504060c03090918050d0314012d18060906050603010b07020109030f0501020306010e01081e1314010213050306070e091008010504121101 79
    0x1c1051901950100c0020700142401c0300d450408140d11501c107078800c0c030305e50700071038240d000112003400070300c881c90308240111712814080c40c0c8812940f50010020302544241e000740d40a1214412124041604c2941d01c1c0001d0b111210040c003004003081100d4070883c0101c6070484540c000c010040003050720a200742400c208402c0c10300919a40383c040003624604a51050504484000403030420381e00203210340d01c0040c203000744c0c03426018866030382c208200d071241d030082e8802509100c0f0402450b43c48406076415100352105607990303007409100580e600441130b40300800084150b405141401019400b842c485c08083e20780448070a034600045a450a04643c4220000401e013070302055650f21020599104402d1008903211a40030345402903988408005500c15a400142c2c0404a40d2905110380040c0800d6000300b4150800c1080600880d440c190304601986580001944403451140c2c10801042c800008015604203803c03d4031a0038980000080440c012031a018900001445142408 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420426241 1250 420424991 420425003
    0xf07062709020d0902041d0115061e031d060702060601080424380603040c0e04020a030f03030b01090503070f05040e0c090c21010b0f0705121c0509010207 68
    0x742000c00000c000d410034109800da075991031104c800140c4a6200b0443c0746c0644d181e000d525014901e50043c00e451a1711421080504803400401001d030304070707582a01c501d80e01542424509820740c8214018101a52010041ca10010896004030f00100d68240200e02a90958245030b80e42c90040d02c0000059500070002e0708d01100e00c9410306900c00c5561820545828003061300142d0010141c042c040300c80030b050b080300c890390005402644002810120000643d840ca0441c5482c3d266007028041910a070302101950300f00140c01c540c0ca03401d054004c0c640c0020b0800c1912040e0074003e0003860b1115420740402c40307540c1d011465240015241003140c1510342070300281030508090001810b842240c002c00761003040402010b0b42d5444040600c81c103100f0440c0c0f625401d5440100c1c03540301c010090b0341090b060100040c000504e07c00d0444006220041203141e82d03035042e140c140e25080c07120010f000110404030381c102c0d48960f14803000c410500016401c0c020368540c401910300301d00c5011030041407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420427491 1250 420426241 420426317
    0x80403140a1407030917150109050915040c050a0e0105010f0903080f0a03021306030c08070503070806010807050d0e07091109030309091f03060b010f0f022d0f0706 72
    0x20020000091501d28880e180040e206035480310800d180d90014040000f69801041440e84c01c1c0c11328400048c018020240c0a101070304200c98142d40ba4018039071401d229104400008007400752080041c0e00410000d0700b0781344001d5440e40b841d42448020302855000805081104030104c0c4103201180649400ca8a20343c41d205a1441442d0507600240d0b0141c141034091081620303404101007401d0050259403800714510340743c0300b070060480030010010004d0220500610010507804212aa030041080c03d09030000d844503501a24240114401c40c2a0340b4102401011202408108442110440581032050a0701100340380045c0c0194400d80b42c1651041c0300030345c0d40f85403d111861b0002203078021241d00360500700b142e0486100541050710041d4482c5510f144a5910103c5c6111907034091a100d00c042c500402c009441c0c004028180780c2c210742c0300c03882428103050402ca0840340c0850741c040341c40c1a0f06008030192100701c1e92080001203412002d0540e44000c042c8014a41c120b26210041c034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420428741 1250 420427491 420427517
    0x21080c060a0b092a250602040801051f0b0a0512090a052e0203070306030209010e2203051602040e0a030905120102090105160521070209070e130b150307080403140a 72
    0x11050b003082512540c10224010140403411703183c034249104a00034600581d40e80d003445003480c00d5a001a05840c0c00000006c00c080c81d51115410203c190b0b8941210035944174044101240d15009105640c8a0400d070a8244049010001880c3e21000d215000b550851a140c0c181d490414000700c0b40e416a040e014009100609201c0d4000c55204155050000d5455140e0300890082e02e000d0f0440f02c4041c403e0b005000325941c0c00032810892820a603201c0000060943e0024002d01070380e07414400085071149004210350759504581c100d03512410899172441c015090050860485129030b0380600c0b0101c001601d41d50040c000c540c54400180c484038a03050042089090038080490705031400c0c00303585007201d0400c0700010501903150b80c8098540d22050f4600400c04d0394032003e450882400580d0540c1d03201e47d2107010640005c0318164100050029921020641a815416814415110000070402c84517008002140240d0203940c403615240200a400340c101c0c03081c1c04180300407a480b095809 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420429991 1250 420428741 420428821
    0xf050906250f0312060909030c03050a0c06180221150a110a030c030c0804050c01120e0607030e07120c12150f0204051921080c060a0b09 60
    0x707507000602480003491801d031103502c4210b4031a00c00703c001030207003507095455040742e00030500904036402c02003021080030381c1c0c017406102d0320500c01814400040740310f150080c02800500700b8142c20100c1031003600c0300c400300b081c001003107103004038828402d404090710320048210035400c80469681c010f001d8007500341c22941284a00070700c40c518841c2c82d02c50191600011a015188556460301e0210301c1c01805070014041c2c0b080d800361a070411480b40c041002084001501c143c41d42c2d0203083c0b0b001010b51005000c07001d80500001e4542c0c074842c040034800403c0e8103500640b0b40150160076510f4203529403040454400e80484003810039400540e0502800f800c0d501310f0b0440c544540032581c00f801343c4152035400e0320030b500459010f0a90110301008103051150746101c44444007282e0b01e900500b80b10b400c2d040ca0090000c0480c003902041c1001b42040340d008203c1d4501016603045400501d008100c072f4000c0c02e09c0c2d061b01401100d100001c50601c903407040c82c41141d001c0c400c41c034122220940c0005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420431241 1250 420429991 420430027
    0x2802150924120613020c0105040201111507032418140c0304110105091c020a0602010608030d150b120108010f0e10052208030907050303070213050402030723010f050906 74
    0x49030b84900800d00182130006144000c0042400740000841c082c82c0c036000150030700080c03040d100182c2c0c019844503604000314141d940e6000f01103040000d43d05d8074035004030302e96580019143e0f003518000d100201c0c019644501594180302403240910612100c1441800d10100c20307a0442c0e5004000c2c8041030020340c201881040254062400f2400e01c0c0040e80012070440402020710324210000e8500c006606080d100341024040703900081c400a40b50080340f59481c803500000000e0540da03001552141c80204d841c05006000101c02c181e2642c2d03202000f1460204288030f4003806618010310224444c403240148030b14640901c2c060622884a514403030040c0034002e02c2c1d0808640b0099a112510035144c01e662005406044800e441f0325040094030724001d00340e085544203500900c03260780165500c14107003501039a00c0303d0116854489101007440d000081d0040301441d0183d8020b2030812413540141e000418003607030b40c6005801d5890f425100d5101d01c016854005404208a03a01e0f40440d00311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420432491 1250 420431241 420431251
    0x5121305030a0f170c03041202070f0b0c01021308030a0207060c02060301060e12010606271215180303020c1005010b190210111e03010503280215092412 67
    0x80181d040c0042d131200c81028408903176011981c0701c0802400140002000d84107559142800203020781418071441450403a11031003120f02d1000000345403280e2030307029019100420000c0e01d142900580394148207841360000003040006100d40040003940611800701c4652042d0050542c1e4a544d08081c1c0071601c3c944440c4030103411050200d001c208903e401d1042100600d055911841d280811060803044002601022420041011014072401481820340b000c202c4c3d121a05c5c620808558500002a213400404510b0500344e0780c15032410b2640540090107001c2800060311003050500c041d0504032a4280541c03020f8000a00c0070813002981c0001000402d0340a00460380000000c5000c0001e0355854009003400850103e03504628288125a110515219600c02c0d811581090040f9075604101122551840c9041d40030702d04807000030350078103288c40d0041d110308094800c2d03012049899000c8414640a20240e62040c03c102808004a101041030003c51901e030a001901c80c3d5812000a01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420433741 1250 420432491 420432497
    0x41805060d050604050d11010509060c0901020a0f03020c0103230a020c070305011a030c0904030c0b041e0b01060e100c2904150546090305121305030a0f 67
    0x100316404100b08200d49842180714400401d40601d070130100400d15505106540090703818541806100b071004213006901001000081d5110034203800100c0c9484200e05d07018026043d071140040070b042d800300e0311007966002a2004d21030915499820400c2078070090030700d03882100c8440842c0140c4190f4000740100c07004801110922038880d00d4003030031a107261000008203007030344191644130306044c414603502010480725100180f034991005024044003034401440d2402c040009000c0000004214074a54465001c100b441d11152901d281d04400a0292201107001c0c1440c080044c604414501c1e4490901d03a42c4101c12405507540000140c000c0000c0ba41d017000c080200000c144050340381d184528080d40c0c62035021205038070302c0c030304642014111018040d034171019000480000c2884002c002c1001c2c0d80769072080c031010204e000d140181542c1800c0303035050060010505038481c002d049481003050710b01090380ca654541c1284001c00c080014110742080c00580307680c90084a019120690b02d003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420434991 1250 420433741 420433759
    0x5032a09061302040b03060f0301060b0f0d0f1415040b03070911040803070507090b01030b060f071103030309010c090f15111f050703140f0105040905010b03060a0507080a0204180506 80
    0x81c4041a81c1107170700503000c5440b02204000041c80c00c00a01c1c400294158001c000d40340c1050f01940449c81035050b003000107000081c018140803825442165446161032040055800450003203010010980380780369030303004000c0700741024601031280000c1c02c00300030000c110741031401c03040e40040c0c0082950007055420034800010140420f00c000c040541c40741c0081c00b00c8501b40905c444c102c0700c07104406810075150644003003143c1c0360042103c41071003407800040e84a184070300d0600300391108494956014000803040c40700a401c15004142031001e20307141d2002c00390300d401046044006902c90044c8503c0c0c42c8446d00f8542d802294100b0501c20404151540f54650520300001c440c4054118294996070b60104100244d051017445074074040c01c882d810180c1003e070059811004c060003054429940e424400f400c02c2030075840702d02c0c60007016041c0c034424a0071001140c001c00d021940e1501044220001401101e0a80708840603110254501e06500b050042c03903400401d0010480f5030003003210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420436241 1250 420434991 420435019
    0x9060c0c122105030c031308133f112e080105040911090702010906060b0306090f09031909050d050c030c010c0206040b090607170405032a0906 63
    0x8144012160700031074021080709819584100d00c0b404410040c0d04118040c014003403900403104c1100d4202c680c044d803a03000092141080f88841c440c42c224080000d00c04240002e00481d4003070b8950550040340c01780640c8a110515028003001612a80354000b014000c1c00307000190348000f036241007200509841c0ea0740c00390700038001c810448950084070300541c041c400340005c0c1d444461b890150030140c406000c860010343d43c201d8640f000b10959889081010005a0341d2072003540b11440058100605000b42d5a6840580ea542c1d4410344420f4010088400015603241e100701050f0300540e0050011450000c40b022003000d03840c9021001003c002a003800000c00781c2c0c88401e40d0030114000c102038030103180c0b01e808043c80d203010510294180301d07120301c041016a07955816102101c2004105030b54481c10003000030050320038644020304808a81d07a106002c204c40300094030540c0c0c000e070b0444e0601c00c000d120050320401c0700e402c100340000400024503c0c1c1d05003e00c0c41e6800220180416a0802c80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420437491 1250 420436241 420436259
    0xc0b0f18030a080f18150a150b07020a090507120b0607120f0e10021002090307050d030903050c060702132a0c020102120403050d05071e0c0905100609060c0c 69
    0x3010410300000c030345074144107120552041054024000740c1c00c0d45071200c940500f1300c6e00c40c0c03401484000903005110014510707007040e0304408002c0c01039503103a1100c079803501c0592440307410010080e03019802000c0003080c003000502c1910302a0885445101c6420740b05c05036100035081e408070311904001e060001a00080410640d00c01059203615104050300320340e00b00501d00000410054401c140306d0b51321407040d0750003055940d1301c001825809603072010b00c800402d2410000764003190300030b05055102c1d014903900a2100c020740b40314106071074068070400200082c3d40682c2c00040e600c02011880f070b19540049038002c4030a0076815041d01c0601c200214400300b945c909420040204000d80d0000f8119a03041c81560440e509501c5520308003421500c2d0340c1d130744054184980e41400f400060210910001400c000c081a00600c4038140d17804080c6020b1040e000203100f20061b00e0b0030040032882144041038040162001640d40411262804d001190b44500701c0000341c40110300781c0301c04100a40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420438741 1250 420437491 420437497
    0x5030703110f01092003070e040303290a12030309020901090c0207120b0a05041a04051605060901080a02030720060412050a0804121e08090106060c0b0f1803 69
    0x4040d865000142a8500e4030a0a1031005071500e02d02c0e9151042001c0080d010040041031101d01d03182180aa0500c000030a00e4030310700ea04001e1315055154100b000709a4507070044820040c07660036111072500c1410140145c10a501c4105a2094001300140901000740b0401d11541d80a031038007044403407503a00420100700d000e0704072810954807080006817054040100b4002040c50000070f06813034880d512050002e40016040b940d0306511200402c0034070140d003803191000c030119001c1001504040c07a12036030350341744250a038005900810000420303140c050b060f11100b80b0103071119112681c4038040305009510050540b010b104802d1300f01c00580c400340b20b02428000300c000040020342081c1c1411001c890000d1411010400f00b0031401401c41c2d0b1107610a81c005070300205c151844008440240c4504281c003903605924034110140c21a50399100e4107050151080c9802004580e0711180c04840f5481d15070710150250911001184503a00c0c01100e09030b0119036100d0104007120030b5100340d0b080d64 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420439991 1250 420438741 420438743
    0x615160c03140c0a0e060a05120d09120302030d1d0106030506040204050c09030a030327201f080612060108030310140f1009091d1c02120703020109050307 68
    0x2451488080c020890440c604048040b0418001e15a180315000000e03604d00090161041d2142200c010442e203445030707090340f0050440107000008485c15040345a9499801291100003d1502c02c4001040c3c1c042d102c00c0504d250701980036514000b4464982006007441e07031203000d00c02d550490112a00b62003881740b803016510800103019a4105401008180c0d03001400c0f10300c5040d0308201c15042e80e038000802c4a40c80c1e031301d414085045800304a490422083d040d40c110000c040c0f4000140070804c0b015110031050507265401c0301c905c8403590920a289425960707001001442050019100740100e01c0e80340d100c40e00401440c00c40601804141c00d00c1000c4e403003400030358404801d11840d5982e11003084050819061070b52000b6101000145000a40810711400350004003e051150382c4a4440100076020116050000804c540e2170364400d03041082c200e40050280300d00d1144102e0320358070050201070081d4002c000e01012880c6c0720002c1da01c94482101907640e84c0d20740c24000780c814409003082d9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420441241 1250 420439991 420440003
    0x60a0905031c1103090102071e0504050a061701111b030d0e01020909280c030920011205040f080c10060909030f0e011d03150a0b18040b061516 63
    0x501c00b040003034a401203070304008002e500148144000340e40c2c0000c294045412240801c0b40400e440c4003042c81c001d210f5040700c1d0704613046c9010494003e00319040101160704209500c0782c03000d903901c5030908032924080980b51800d410851b040300c1030b0b0340013150325455061205807440d1015040d100f204503949206aa410b1b03940206a9510502d42204140c1e40301580c884d641d140b6038101135140ba06082038601100c42e042e611032030540340303501c240c2c00010040c0c1e010101019200d071080e41d000e0407a00c680483e078000360f2903102c2c076030031082036000f00b6029651106a03500c5c40701c00e0346e966810b15000a41860706612544030000c4885840340102e0f0010103204400040200c1a03050040c0b1034030003501076805000130551008c1003664051314200500000c4d101c44d070280124003000a082620351030101d903424401c00107002c4044001e40c4209428001241c0760001ca1248003601c0007111800c0310003402d140054000140c01e814280800d010b00c00c0382140f0649000d0403610880d1448410803410703288 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420442491 1250 420441241 420441283
    0xe06030c03151506030c030109020d020405060c0106090c0c0c1401140301060f12020a080609060a0504090302010b0414041a07021507020604030206180309060c030d060e16090e0402060a090503 84
    0x4985040500240110043d5403142c90344c03074221b40b0707003036544010720814010a80c00a03200c81d2070455036060f81c02030000100740c990b0b142c20f00310140e8040c0c40c0c1401014101441d003200850301d20b02400102c680c2c3c9038001005207545207800d0503014442000d05a85040c4100002e0030702c50384455000640c040c2565441d402c003256003800c0010004a1031030f409240043c0704002c21003041f50011842503010000305d480d11220f9541101041d09071015903c41508141031107509420950190070030100c2c6c010030303607080160030004c0110000c01d41e802d0314003810341d001e010302c00c0504038045c0c10030590211a60044801d03c80019201c0050280c4c01c5603c0310050304610140410194140401604014040c40c1040c000400c1d00420351a8403542001070700c687c03000107aa010b0220284180ca0500c1c041080070081c4e1a13640d40c100c40407844c1143c1000707494403690400381c1641e0160b088101500c58641004010f03645540c280000fa0748000c260307105000e035a400000c4c1ca9501044503090306031841f41d0b1090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420443741 1250 420442491 420442501
    0x3050901061212030e03090d060c0c0c06091e0e010506070305040305030a030230010b161209170a0f020d05010f0e0f0c37080d030614030d090e06030c0315 68
    0x41105e0b0f400d003000d0081c1d001044503109958861840580c3c0c0e9420080014128a40c05400e07a84114208070091441112400000300c043e00030380740a04946520010914000c025030403602c00c1b8901b0b00074540d092245d6030040c0918103254000c1c1c2002807090174610300c0d044c0c4036201c2074070f075400c1000700d840041d400098020300c3d2141e01d507000780c0000ca10160174503645401468552041070501401100d944017050034074000c07100342000030103503800c1228415462072081c0010038110981c010310110181c0c4462404542500190000e0125002a01e4038103007000d990030050385081480e0251040c0d0b40780c120390410b4081c2845100d80f0482910010309076400c1c407005550801144601c605e100e029240020350b41c5480c4031a1000341c2004400c29201c03c0c01506050782d110f001c1c070760000e906501c03645030035200b40c43d010342c401d805403003024594201104110040554484c2e800d16140c0014a42c110108009286003501d03d0b0082c100500355118a03840c04042850310103a81038003c24200c1f0081884 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420444991 1250 420443741 420443747
    0x170307140f0a0b010614030f1b09120106080c01020a05061609090c03090c230409080c0708030d050109020a02030a0c0303020c150f070206060603070f0c08210105120c0103050901061212 81
    0x4505120100d016425494000b410f1800140010142100005000c09c02c1484101d010201c03220b40740c00078541c2024008480c002070091413540100705103071003080d98a1419600015001c20807da0000c0140a550340d48070119541c1300402980100b40820b20001040401250048003048001540c000901520f24244450a584a640a2203a84200c400a011030120028400c0c44082059030003054004207032610385100e21520070707001c1490003121004200034078007200510f0a54030000c002c1c4082d90700c840501040740300d090035480142c0c4c010094410054010041c11210034004e0400504210340e0007010760420750241c3c103081c04070b02c05000300543c0d1903003000000c1d000314040c402841d151500c000416000e00c4080e02a0092000c50400640950321540101c03070f600d80c0c441256030703c0341c2c0070615800110303403000b003040d038007400510000c203003410440110304a41c1c1d90b20340105040b00c0034400544c003d090252000c015552140400300d00c5015514107221054407506000e0b203004030118000b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420446241 1250 420444991 420445007
    0xa0308031e011a09190b030c0403060b090105010f0c050f0d0e0117040203060117122106040902010206010510030f15080d03141602150403080709170307140f0a0b0106 73
    0x480001c1c80841c5082d500070000300c064608001060700d292101e50404801001403145650206ca80650004100030580c81d108001c0c1044a21540081c0102080c4104004c1c80910034000c5500045038500e0314178109115500003d9440d010f40b05442c039143c10500401d0a25140020b11000b003148000d4000d815644900350000d9032407034a241a895013000d50020392209030611030f043c0d00e2051690003000301d810038025480c2510b0440411a52910084c1060500803014102e010026a8103000540e640c1400d0081e0800140c1c1640a040b490b0b08110801141c40e540c56408070800d50386007007101881445105508030006500c246500741444c1c5401c0925108a444c0c00c0001c0508150800212900f000840ea40224045c1203480b03003200141c00491070100780740c030a0401031007000c0511091541089105008040e107030348802a040e2600501d00c1c000e400401c9507203480d4420085040499a4101c5000c8103255000a44100020720300c8441e141a240c0c0c081501d8001c40c0000400440d038010440b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420447491 1250 420446241 420446249
    0x109050301020f0f0c030f0301090501030c0e06090105091e10030b16080a090312140f0703021e0a0e0a06021c110318150d0603290103110a0308031e01 66
    0x2549800f10322262444a4081d000d030304280c0074000f107904140000c090098400e80320103904002c0e1690b94503607090700a41000e10050f2807140b01c0c1b90011540201c20740a49204010180c82c658140e440d10b42030001c4034900070100310300c03404c009000b42c2c9422409543e0034022560030710320003501c5041d810314aa9a040c05440604000c417412003c040b00c3e508050f003103078044241d1100003a00c071030780d00f81500c126124204e04a4101c0c82c5c40b0421262841401405002d10324182c0c54030301c0c0e540c85150603400ca10482c503902d00c001d070542e0f09100c0413410070402410480c2c801d140c1070000005032404184000c4a580200c030140c2c0042083d072408189000c0040c86000c02d0b071030007140600d030300003030107885e84504030000185840d181115461511441464070040143d55880c030ba8a03118100598010030180c04101e402e42200d0002c04400030000507201200030000390714a01a034070310303581e01a0320b01440e065070381c00a008c40350020104407440f000d54480c2e080d0381c40101720005000744c04903800605800c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420448741 1250 420447491 420447493
    0x30105090f1308031b04081c02010b03190f0b091e010902011e110d12050105030102070804120c0b0d060518010f061206030203030403030f02100504120c06020c011a01090503 76
    0x30032001d00c2d9581c0141c1c9030150080000741c4d483d1908803a81085814008102c0b0f445003001500085d0148006a4040403d500660800180d248840100d080e1140d810019a155001140020450141c030240f881d050303200319821440400c4594079000044000c6482400741d41100c032940100701e54008907114080314400081003401460350000c4c0138240d218001c81c40c11168200e050118034020801120300d40f0541701201c81c4e01504840c000c1480c169aa08035486504000000807541014001c2c2d854203540b000c1c00904090a21003801c6035080c084006440c0c00d200110300041e03a0807081c0040c03a10b8040741402080030b60801007809044c2c005070316000b00c00d030342c0c03c0010864419241d810100381c564510700303240c0011404120174054600340e00302035818000000d00100b0141c215501c9284103081d82c0a80305c491260208280445034115400b6040e40c1c42e003012205c0513441350700740c001c0051140000600308010001d01c142150741c3c0800721041c0c40300d4009a00b00c01d6030820b100c0c600070b00c4120 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420449991 1250 420448741 420448771
    0x6050120030415020f01240e01080309010302090d08070f1703040f080904060b0d050109050c0403050a030507020d080d090b010504090309030b0606091306050a120b24100503010509 79
    0x1140d1140e03207119500c80d1885061504002000b014801d00c80c01380440e2511009000b40383c41c0441d03a040300b200da81c15607803541c0c0d1000303000101552541402e6048602000180d0709200e10000154085c0d0700440e05c42e030b03126045e0400240000d111902601842c1c2c01407c1c120a2280e0524001c1290008003000c00200c0409204003c0001d50030f003056030f2003990100c61152201d0990002c1400303461540c100010505c0042400000e1880c643d000c1c0d81250062030b41400039490341601000148680c0c00054110b810002502001c01e000d9401000310a101500c031024041160311110069040711025032125500ca0001d1001e0200c10070945014000407542004202855900540182d285100040000e4000d200003140d50342c4140580342d030b446c4080c000200110143c4410001040140902c03807242c002240c011071a141c0c05121860b4655201d240d0004135260980744c0c5410307580d01502c14590151082c4004115200c803040607201c0482500c03215106e505140030005205030040c1054030a1080f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420451241 1250 420449991 420450047
    0x1406160503091b060904020f03040b0a0c0f030911060f122d0a02071202061b0a0512060a05040e0705012c0d030e0301090b01080c01080106020d030209060d0e01060501 73
    0x8038003002ca4502c2d40250701c04003083c1402190503406554000e50740144081003225041880c84011440f81d4441c0304010242d03580c1110340360072100544115400a00d5031403a00304d50030300951102054070f01407900d41ca0302000407400540c4903405221840c240c0c00c80403902003182d6010010b0309400000e84078900f1094503110780c01ca00340040f2400c0402441d2502000b00e0018421541282c40c40e40e000543c82030186100c60010b50313034882c10761301c0032500ba021580b90170701401d0040c19188425580c0d982c640c9010032903030030700c104004d000d000d40381d001810000000c2c5d40d607568402ca06030746c000034002c0c00c9468034000000d84920003000320356100c6001c58100081805c0c04018209910004032140300c011185c40c20101c4082c0c016070301d16500341d803030242c2c10030907c014aa54181210541022034240482c000c0044603020f00a104500259102211a020742802900507100d008000361803581003100800410050302d90414980c0c1003655240030900c510750740010b01034280101cbc604540101e02e29 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420452491 1250 420451241 420451243
    0x21061e170c030d030c11060c1e1207030b1206010806100f15050a0203070813030b06030f0601090b030a050a06020c0c01050c070501030507030f0203042a0806010e040f140616050309 79
    0x100d48611000c1603981c1010001c5d40b4001c1a401c640101100100e62241c50a10703070701646c0781c2c04002d0090029440741c1c603c1010b24400400c5514018120f80d5407130f807940301e241c802c0d1b028001840754036500070461850607d0340101041494000c0031800700614240c01c4c464100408100c1a40003004450800002800b4001c0301e800003001509280c9001550380412003400ca040d406403180c024403601c8000356444400710300684003000d60380500d040703000301c1d11141d0400d5039603542e2240321303402500318900402256880d03502c940d8244902406451441720665100c50030001180f80840340c1640c0402c2443c0201010012050003030800e003805c0e8901140c2c2110340e40d40700710a2103180d0416495100060040784247c0110464007a030034401e6459082a15001d40c032101049640c1d0070080940203540350101d254100a0104e50010026044a90070321000d02206000104285c40782008031a00400054010b10100500800782001e8a03407401d0050681104070360500545007001802e005002e038203a8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420453741 1250 420452491 420452503
    0xd0f03060803041719111e130b011e05030f07080f010e06010c060603210e06040306050c0c0f1e01201c0f02090906030d21061e170c03 59
    0x700c20380d00c0c288a03201401d40b11703182440e0384da81001c0203041a440c1c0b070200003825030400c610100480c3e101210601404000300207006c1240d000741d0040c140d1121001c805015803012000e0181854031000c3c250780c0e403048a6140150a2200c800984000104590790704248605500202d503403a0201d02401c100100075090107043c0982140b009420010642a0307010f200c103a82c0c415800b1f40f090100707554904110001055201c4031000c424030301d4102c40c00c05842060304946000f1300419aa08150461b2a0703000101801091b41e000180204141e04001d4003c000c1110001d00d840d008095509442490000081d03d031405904660306095803e14082e9032055841e44943c0c1994000d9100c0d06082803030000c074030b906144052030900d015800c50301104540c00510719082e081d24000c0c01a02c0b08024507a0318003150b5a1000011b0310710422030441c025070012400c039200c1002000c10f105d615104107002c00562029040c045249010042003441000e5121344030100c20700028100443c2c044000c680c40702 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420454991 1250 420453741 420453749
    0xf0a050108040b070c1209090f050423070306150f06140d111b010e0c0a0807030209070522140f01090510020a06061811030108030d09150903020d0f0306080304 70
    0x9454000150785900c101d01140445810448050100c0d031a508040c7c00380e03513640030303865295007040b1a021224000c0e0082c1c0c0d00841d4807150071110401c1d1408900c6444442110034405801001d40000c041005401341c1051142500740403d00d43e0310f0200b61079400e0f0030b039074080c80c02d00c15110009a82c9050000588450720112440815401c000261489043c40344410380060780910441290b111641540603041880107001142c41d84d00e5003a0401240c400c00e4850f49085a00c4418140010701b05100f8054200d009418824100a8140721142e1140c16031a1030b0902d000012004025801180840e00f000280c15903c00240e40203200000f03201a003036000d628090040d48000000d241d200300042403485401090400150340c0700e43c1a5114540d0004d201c05030182051500000c4103903490482e8102c0d4041d20045203050042e1800f1805002c0d808019201491150b588a098920500800101c0e0344284e0290a51f4808520080c10501503610540d041624104003405034090000450f0161 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420456241 1250 420454991 420455003
    0x100308040b03151003240f09020a0201060302060f0901021e19022115092b05090a120c080f031c0207290f060a03020f0102070504060f050f0a05010804 66
    0x96540b100c003c54281d5440f24215000090045907040035541a0f220480d0003114916a003814008420380f809007486130300a10812601c0248104000741c895030041c40d80300341c28000491015a250001100c1f9041018000140e2800113209842582e05105840c10326103141034000e20007810b440429907a1101a61400a0a007130070500030541d590344a0044048440e0550b54195410b01140c103a2500000e2903105a100280f40105900b0030000c111900103400c6035280950200c40030580d0b075010410000700d542444002c01101d4499290114590b01a013102005807456a580b85841442030307030154483c14240d00451400c0b00c450002104940102100051411000d900305600e080248500b00e4000d00c1a1140c2c01ca02c0325552810001d2000461a00c000e01c0b01e503a070741740f01e100850100300c0310541d000c08420002e100619008616003007081040c0f04a582103a124030100d01121000d030003428030b81003002810440d034a082055407140203802d85d802e003442c600c0e1100203407840c42d0240000b040303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420457491 1250 420456241 420456247
    0x80702010e04060b0408010b090402181b0403060b03061302102106060c0201080a050601020a1211060708060a0504110d050612010f02120109050708071d060c0c0405100308040b 77
    0x1960310441d064501400001d104020160399245052401e0384544100300340b95082c000400c01e5440d00038503ea20451b0058441d0414402046c240031601000278a6072103925a408003480141d42000d019001441c86608001200c0e54030320201498140700804102c4d1101c910600080180c81d44507040021a01c103040412403c52090b01c0d941e40e062094240c80f9880b8602040040e034581c4c440c0d40c00d1245130003070701d5404c0301da22606034031425528201c0301b45000d07a006150360800034103118081c3c0c1d0300102500c1c1064014100503c0340f03051601c00e03510140011407202c180803452034236480500007401c2c210303010050700000b59070055060051030790025138581c0c1e0f0000503a444d26003840c894200d03800364008111035003814109400a400c11101101c2c0782c90040004070b043c05081c03180714045d07422500e0383c0030b440d0b0300c40800303c1d1120344500c00c403140c585605074421619224040a0000c00d80010302921000422009120450b50024024a0164400441040410080800c507801d41c0c0300d0100e129a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420458741 1250 420457491 420457493
    0x120613150603021e040b0a0b0403080a03020702030a05010b0f04091505090708070603050a06050a050f10030e01150306140f0a0c0314070338060304050f030408100f06120807 76
    0x10401c9030300183d0054600c407003410706212040714050014800f124101300e82c1824800f030000d0b401c1c442c0510142441d0400080c00401c4205002d4101840e40e4074001d4074001c2290b020178182609000110b54a81d103425600001f4984ac41141c0c0c1d07000700581e000c100c0340010b622003a00c44c140d0075440303501003070b038403008514010020b00c0010041c02188003101e9036aa51000d0041c0148011a0804003007450b1031408a440e03d025480c0c5e2080350401040b0346000c01203081080340d0a03045900e20010305030360b4241142244028028140e00a4029410064031891400c0c00c1081c0d0f0f844500711010701032604100400d01c0d00c1c1c042c0b483e0f0020032400000410525100040c7c00500240c2804600c4812000800410740d03815080035141d0300710a51054140c10111000d10703d85040c030142104c5026000341000c0f002e00b040b0026640c0302c1e00480c22504840c8070300c24560700359070098000384415080310400550b61070441c040d404826098100400082d4a003641100718540e086500405640c8001a440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420459991 1250 420458741 420458783
    0xf01021305092a0310090b09010905270c03100c08070c2906010f090303081b0f030f0f0108070b030a0903021501181518051314030405120613 62
    0xc03001c404507901d164665400861030300407500200c0d84500c094154185c0070901e0410340c00342c80b003034040242504030140d00748040e46001d07080091401450343d6215842c00881450510401c100f154a00c0c081c003111040c100902d03007801100c5843c51140d038144101d0b84599a4000407595101f503c51800305800310461a20642c0003404181c0c0140d5120110a280c10802083e401c150181800344c07200c080e240740c500d00a940c142090302c0b01801244084001400d1501c5249001c0c400e8003401008a1901c03110040081752900191010001c02c0024002c01c0722415074410001e01401f407000051140602e802240d61087c4001000700c2c10044d00c510340b08040500800c483c011440700001d0035182581c580d0309482c1c0041d650110310040d81d081c04220003c035451525040180da007001c0c0003070900050440c031800a428084c1c142d1040c8103940340c04001003142548800e0340142c06502540e80c0740d02e82800c002e03101d40900040081a04080c060081340f840094909a02c40e03440303514103600060480a00d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 420461241 1250 420459991 420460021
    0xb010501110f0a030e1804120f05040e040b040b0f04050304030f060f0c210c020304090b060f070605060a0f12060902010212040f210215090423090f0102130509 70
    0x200d1043c890051050105600803204200710801520015190858014441d8000c1c0040c0c0d806446186c03203008414070144600e84a14407411581007191030681d8034042c4c4c07070303100e80221025640344140320f0a01c002c001c03c100016810a141200400103400c2c241c4445442e41304030310000b8420703e040d081e48401c1000b69004101c58128038034042007030050315080584580880c441e07035020200031080d2031890755240e04c20700042e40c58642c0250308290903d880c41c8010140c1040203079000d4418080c0964a2020000820806225803008205810007106016140321aa0011000509001c0086c011102240d100b20155904000081030818643c0010b0f820718464400000e0307484000103012401c40c3c81138000604540210f661860820b46200042d840e1100c98000290301800d80c500105407210450090006414000e10000b141d405944415000100185074000d04000c01020001c030004e00b480145075500d0090002d6141c640842c0903202501202c1c000c0c24400c08080d0040303050302d04000c0b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 420462491 1250 420461241 420461263
    0x8120601091508071107080a2303130311060306090f0a14011502070e0c040e180604060b090703051b1308010507020304030c0b0a021203090a0609030f1b0b01050111 72
    0x140d119020b107401d00040010070100e0b079010224480740f2000400e4200019994221091040600000141a1748918002c90740c605240524507002c03d881d41418428002480800360002c5000b18040ca07500e840f40c0c180e00e11100e000e1182c4c1007442004541d84481c2000c5500004201c17041c2c0c595500c0e422814014a0080110507460380c1d010008101c1a0b032800e60521041995001c45040b00c0d680d10140001603c11144805100c0c024001044050101400c2c10380000d00400503075030801902a1051071b0103011a005c3c0c4605031200303c0c41009050500c600b5400c1002c0f8901408517242c095424054121600d00c9c1c450030300400681c0c0c07030550000c03039284800343c00750400a010b1401d04240013540d80d04035000a07201c004101d940040e0b550070a03c103d80494805402600c850183d13804400116000244401258020030b070000001a00c48d01c21004011312a444400502009410091240703c3d80c0c00110103141c0e284060f18085154800c01034110b400900c0c042441031900300f5080d04115800300b03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 420463741 1250 420462491 420462509
    0xa08270709050a02271c080406080618090a0605241e03060c09150304050c01050a0c210306171506040b12070302091308160201180e1b070812060109 65
    0xc0102d0a41400003489404601b181d52402d420b809035002c41040340341c050000c04090003048104036860040d12a00c0c0c1c010401004807150320115540100d074040211000001034021032007000800c41303103209aa801481d031032080349922001030440c00704201004040307841840c01c4420030501c460742c4031424000d40c201809464007824100740720342142c0c0017400c400b441342166200341e2110040303504c20313070307100d02d41280c02030004046480c010340b40340e1b00442c000c00030020500385503804204075842031750809040c0e810305411428040c40080440d81142c008440e01c010000c80b143d0181000100880004030011000343c0c203459580000d40105003c0340c1264100c0f0040410100142c1c01154940c1220f0007691000c1140d9214003c110310003409000040410b14180039a1440724400e2003100130003441030601042000394619170103a000b10756440460200d0301102000700500c2c071206000300321000f0080c9a42410415510800c0304c0c0240c80c0b000c440d0000c030b0313800200103a00c1074000c8070040140c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 420464991 1250 420463741 420463777
    0x9021e090f180d02060a0e010902130f020f04060804110301180305030c16120f05040b121315020c0106081c140723060609040c0501050f0c030a08270709050a02 70
    0x902c1c040d44482c41118034a1146d07203018448017003200107000e9800c807203a005100d00b21000101c942d14004002500c41d10b040300380e083c80070000e101d03803040050001c0d00d8036407140005071038540780510702c000e0a44540e6010783d06000741d4280003c000d419992500e585412b0680d01e81d50780c5400075000d070142510078002400c0302e5000c01c0a209032800d544846240303e81d40c00040c030b00c8214050314140f20710b205100864074200302c000d500c1c84e00840c1c4d5030342088126030001b01d8144651614860700310f0b183e8404c000345600040403001c014007446008020500b1002401c00702c15403138044c54115003800e81040600102c1011340340d81103040d5040718141580081ba02002c9840c407600c05500d12142100d0389d01030f00c07d00c070200d001440c015100070700c01c035070001c0e02091140c1010700444080d002404040264903080c072148003041400c0c4003400301d01c42140d841c02030764a03045140c0e014080d5403a4009072069091401a0703000c4801084000903184580300102705600c030802002d00a200301d0061104c00d503040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 420466241 1250 420464991 420465013
    0xe030a060612031d100f020a06140105030d020f0a030c020a0b0c0d03050a02130b0a03021615060b030f040611040b120a0b030c010c020d020103061809021e090f18 71
    0x9411042c2d032141c041d90b24181074407031003c078500d000403543c410143d1000d011075a8140c02c03482140c02010921140c41a0744040721166198000c1c0e0f0441a0030010082e8000018070842c00c7c00c10040c90f00191a02c020041d802c01001c0958880c01a102d024042010000c071520564a901aa50b001001d200721195038402c404c0080649603000c2138a42c4c000a1f04120101d0b0342803541d4001e884c03403a41035800020005141c04800081c0798040c070303909404e1507024001174103e24400d00b0001c031410702822941c6920a40000c0b003030106c400941020346d214006000b44004c00c0740480c0e003581d0140d404240040c840c000c0c40200c1c6128011507100c0080034400048603034001c201301c0e42940c028480e61001317000c070070410403c00d61100c0702820000c0c0020301070307101c800c0036141c0300c0d041400060041c1400220261510704e6030f0060011803400700e0355a526034200504504104188003840c00c2a0505401d0030200c420000340300d64070103010300710303e0469000490200340981c81032407000c0e038101040f51042010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 420467491 1250 420466241 420466259
    0x4021c09020405100b090d03030b0d1104050a050c042309070e010306080c01171b04060504060e0105070809130e1905100603050c131401140f0a0501020d0e030a0606 72
    0x180d04049010b1420100400c2c840400d060350070042d640c2e5a24503d041c0150300d0f0a00840c081d082c2c5068042580700c019250300c90719014a40b6428030b0050401201280340802400140d600181c64448010b1503c002c005880040d48107440503148403400160708603178903403502d1118001c003004540d8420444814001c59540240c25000c01e12804e072030500c199980e03a0082502c1d010140c458601050001a000340443e1580d07000b00e40c040019540b47c10780c4050291080001d411681000000c540300180900c20b5680050140341001804d180040c41d040c2d40d56030b810b03640c1c01000500d13030044851121221856205422101c600705403a0100c408058901d188000c0c0072040705021b031142e0103030000c0c0100b500b0720b43c0074140541c1c0c1c2120040024420030024845514090140c0b994016a580d2220028070f01100c4464002c0c044c031046117079103614050400801400411413184120209a01088183d8011400402c29a1705081c11b1048403a5100400d04041c030881c3c001f8105c44c6002408614041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 420468741 1250 420467491 420467501
    0x2010e060a0e1507080a1d0a06050f010b04180203190e030d06090e190507330203070b0105040209210714010507200604030b25030b18040204021c 64
    0x1121003243c4002d42140603c020706941a03c4072000560701d0320005000d40a01c0d00310640740048241c2d4482c280d0401d40c40070f0b040c10011201120303030603100c81c2407050203004040e0207405800203100592905241a01d803c043c14001d95149504a0700480011180321094102c8072451410080500c080e103110100b0540f25801049040062458944046005102c9201d1000400302d0b540080015001d000901c0c06034044850341101c492041d00380100d040207104880441c20300c00015140003c80d03051092082050302011a0b10456000b0301000c00400c10314800241100e034180d070016500c15080000c609440c506000c251644500e51019004071900000c150781100c8844d0a202801039058004403224400d120300601003401d5080d2080300030310342140070301060f00300070289031600d941da43d102d0004103406c4030200e511204078102c184118011100026040c442440c003003105004403000030b004540320510302c0c024803080b440000e04648450741190800c0c3c2c2d050303440101c40e5200700505400b0300 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 420469991 1250 420468741 420468761
    0x1090c0906060f0c080903490512060a08032205090105030703080c0c10271d042d0c1d070806010210050c0c2b0c0302010e060a 56
    0xc0e241c010300055451040c40c10040e41d01c0d0b2503441c16411801341e2220601c3c0e801645800ba030500035450301038001c0024074000307100c031001081c0009031618282106085d00d4403070012100c02c503564085000c000c945c0842142c030b207801c0c042c0b48903820362280c50105202c0f100ca900020341501c00001e40c000d900d619010840f05114104401c1c400c016150b90510101310300a1143e030390954810501071000408000181004001c0e00040717480260781000010180c08001c4540340c08100d1038645042ea142199031482c2c010340d0000c042c41c3c00e441c40e0050280e0992802641a55141626000708007000010150034040c1d03034081000c2030044080c0300304000c079031a01d50f2040768440c00504000402042260024401c2010200511f04d107907100c45095401a4008180a0441c0038050388441100b0345031041c103018244c81400151038582280c1c00601d02603c00c0005008a401640c12030050203116214941030315480c0340c48a4001024030b800d034003408040d40c0c41d200074042c030010400002d8240d813109640d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 420471241 1250 420469991 420470009
    0x10806121204120506011406070f0501230103230c010f050403060f020a020d180302010e010e0306150f01050301030f080f0c191a090601061d041b0305060102060c0702150c01090c 78
    0xe03647c0304484407055400002468214100303000800100d000b070300448400c02e019500105650722007903070ba1212480c028941100078041c000040c020310400c41d4001200e044011003c7d460140011032071540c403658001124104031144800ca54030034401d5099800541c2c0c40101440500d2a011484020350445442c0d40d0040c40340200f1840020300c9001450703915501c00c45440f100d642590011208183d1758410103041c004c44002920054904010300c9114400903e94140f403850842d0030840103529000159040040500060003c644041e0752402c0d02c80d403100010307545003840b004085060044003640b040e00d010704d1200d04141d8004545407250140700f6080b41015011100d00c2400c0040700761400106079110000501419010302000b524800300d50400d4007041e40c00070000360036a66500c99840c0c00d011840000560b054040c000c03190803a07424005010140340020a01802d4001c20382c01030311500d1a03030f00a01ca9048280e0803141440c080000a01206020713061118940c15a0302c144c1641e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 420472491 1250 420471241 420471253
    0xb070206090706140a090b0c06010f0609051305132a05060307050909180f010b19060f0305100302100c02130e03040909020609040204031b06020c0108061212041205 72
    0x160207808160300b000c3c0c400c180c50b401c00c40006407501041c1d5030001e803c00c801388442d10b41e0224500506402610780c6005100c014010f96040646c2c0c00c030301010903032010081c48807842051007a640c039140b01c0c0004031000100050755a8030202e92030030810318084061300429060704d0b164a984038a01600142c1c0000d440c070200b2650351a004e200c0c1a03c8215100c2c000168144544107151903d2001c6980081b10101e2404001c001c1e91030090070318038404110b008580d0b5880450303059041100310056002c81003100f01100034903140c000752000e1006030b060b00c20507603544e001600e03d2200f449544060741d0040d00c9550340c40b481c080040d000001050099102e43c03080c407038085054401d40a1032510a020030040c504161a01c00f00300040c18181d60308a81c80301d0140004107070380c0c8035440600001e60091030003030403010108416250711900c642100c0d00b190880e00b00240c0c40d90700004042d800078025a03804c20b00150300101c2504200c03501000c0e040b42d19001800246000032400c3e40858580035009a0745 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 420473741 1250 420472491 420472501
    0x150e0f010c0c030c140a0b090d030f11070f15060605030f09070f060f090812071b0b070b090307240b04050105150c030f0d15080a030c02040507050708070b070206 71
    0x96010400e000c014002800c00134a20002040040080119103501c81122000c0a10307682c5c1040e070000442e420702541c0d01032000380c000650300d401107400b0040d08040070040c0d4600100012114800c0e40b00c09808a08643e80000802080406900011000940070051243c89010040c5035a000380c4000d174283c21414003054030501c0c0440d20804840395035201c0103a2501e40309003500c01c0d171442455442441603d01c00011990750a2150034005001d007408580d95455501e0000012000d013007040c544000680303002e00501c1c05201c215a003c5400000701e0079165540c5607014918411140002c2515464002c1c40c3c00d8035150100c200d1a00c0c0081009001d2a50000180000c58209105103980200340032100d0f02962050001410b26072090001c0d07d15020b1180a0710016920020f1307d00f1845d03540b4105840302d00030084202d009000041c01270b2202c00326544009046004250b0302a204176999000303d0b02c2705000340308132003545500c0480f41c0d0720b9040c0c2d41002c1d140010110307103400240c064480029 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 420474991 1250 420473741 420473747
    0xc030a24080d0e04140403080a020d090506041e0804050d0606050607060b21070b0d18050d0807030c050304021915030207051c0c06020d060315020706060b040602030f0304150e0f010c 80
    0x28402081c1c208280717604d65443d1400c442d0b642025012100c0240d08108558001c81e0700e005004c0e0550068000305400e041a260518046040003d442c0362029080141d80005280404850031a4011540250212021b0070800007e08030b40c0e101d50380c0320000042c9070040040e590400200500101c451000c4014101100341c1106010522261241c114640c14400000b402c4003400c0d0a4003880780c002070302d19150b4413400c100501050166403d40c4090080c001c902c0d0f01c15011a0700031660701d400e00001c0340c401e101400e01d00001d03100034812411140c112005260031a041001044400000540000401c40c060b00a502c001419105d0340196101113800b084105d0303032a210000e0a40d105110003540d511900d0007900880c0c983d818540d2981000004180c2201c001400d1240c1300400680da01540e01c2e2107001c940c59540007001481003840300b01300701d070f40202c00e441040368105038040d40c80c0e44520307040d1200e6a180d80b951020350f1074403020001003000014900722822400c0020030464841000c15 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 420476241 1250 420474991 420475001
    0x20c030c1c060b030a0308043e01021002040605040303090f050f0d050c0901090e0c03010c0806041d0313030b130b0606070311060901020c0c090c030a24080d0e04 71
    0xe2900014050303400180541c2540a10110a004000014202c000c040000382080f070101e00960003e4000028401071040788203107510440302c1421480841291284041400704101010074a10f4806817011095640240802615400b1103403046550b6070300c40c03a0180803600725004c1a00000d4050001103040c105022085043d56001000d0b042500c01e10b80401001714a00c0301c01301d915000d03140c0c5680c1aa11520149800f900441c81c000c1402c1603403a100c5840e2402d054460b510a030f0400358000885c0d9044289150842c40c2a2404034113a085040740c0e49034002c403210059641e100c00144015854000120407054900c40c812085580d10f82c04412155602c1164002d01180a02c50100e00d01e49080402091101d02c40d0078042d40848000c1d9005e8104501110a60640d0b5000500100034402c00d204103951481d040769000404d050101e042a142d0000a16000d1080d598034880414480001c00b1921400100c041d44010700303454039100354403420307818202c1001c20003030240035101d85450702803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 420477491 1250 420476241 420476263
    0x105030c030f090f0109050d030e0102030f07030c020a020d120807050408030a0c1113060e010909051905010b06030405011b03021801080c0f07061e110307030e16080d020c03 76
    0x506080d600d500c00c0c5014034001c00b415411551081c44e03403c1d07a41901c28000c07100150f00a101078200780642d918080c055034410010410f00d40d104008010703100440b4503049400c140039140000c1c102100c480164a00700c40164065842a5111400001c2014040010078429070365520313424980c5500354182e0700e900072400344800c540c00900100a440384201811041c1c2d0340202c064041c0401610040740ea040318244d40300711882c1d00d0700b00501c1980e404540741c2d070050040040401c000c181d6a01c031140c94815001c61100352034481003105003400000d401102080303000403c0c7c0c5540b402c280c60958001c007100c001814072401641100c1003114007030b10075208000354000d50080305410840044490200081901d59004414030584411740c0b031344d8020706031152241c003000407240f0b20f6051084801d01c44000c0e404e049030902901165010004041c5e035007051160601146000160f070f680760900450030007556441810180001d100321002413258036010081d000c0c1c42076050018285619928001d0b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 420478741 1250 420477491 420477511
    0xf0102030a080c0310170606030706050a0e01110102040f2d03170a02010f0c020312060d02150307030b041e0e070e0106050c1009060e070b0c0703020607021309031d010503 75
    0x10020303c030034010200566010640101041c0d5542d114014602c0d11740e0050860b000c5176010300200182c80c1010000d4101404c0d99040a07401d003075985400400c800c07000310200b1304104491703203480203c800940580300130f010180f5005002907110300c00c9413074050607071186140c0d038255160f110030300c0110b4100394003da030b401c51001b42c01f01c07000391142000356100b034150303c0c11036603103034406003d2110703034400c400314481282c0c007940c0e44422441681d0710402d00a00960b20465648030b4242c0103a84000034084a000400006034980c0e4488105400608084054542050030080e41c0781c14040d060000714111f039000b44040265a9008007859500d4009004415035204030100501c01d45001e1005004201d9074482104c0d0122072000d401c00560341c0862080710303000d844550100706080305000d018068054948260b00b42100404441d983e8003061101a00444000030084d00350b4a500c410b001d03142d20000010320281c0003a15000f040c180c0800b52540d59201002d45100c102d40c8103a040f280500c20402c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 420479991 1250 420478741 420478757
    0x30709060e011707080105030709110403030e12030f04030213020304050a11030f16030c0608070c0312180b071d18060f030d0f0f030908030403030c091e050f0102030a 73
    0x50301500c4054460812506100780c03506500354016259290030f20400c0c4644c0d49040f25454901810f02d88100b90300b12645041c20610102010a05842542c003101c4d01450000108005080803480111002c03100102a00000034841c44c86103e2400502c2140d100303951188200740c884a200003280829074004007640c0180c141c0b803020601480e5a0b40a0200043c143e5100400e900d41141ca0022400c000c0141203954170303030800500c42400b60002c000d10582c242590180340601008040c10203050707008040c001c800403540440b010340d40c0984060200c13221300130400390f0305040ca40c040d810f045a084000a0400380c0030314031030f5498600210b40a40c05000046d900c24807504c0c122801d10000e2070284c01180780c2a441d51260f4003008444600045070701d418102442c5020b009024106510404080c07500b461034030000102030504417540207805140000b54011801d001b21382c01e0a040e444002c0e4600c0761043c0c1c1000b0294480440300700c0f1811a1002c00d484188001603880b8040d00248901085900c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 420481241 1250 420479991 420479999
    0x30705010905030a2006041e090504080d0207030509060c1501080c0112021c090804090b10080a1d0f01020c061302181b03160f1701090b030102120408070b010b030709 73
    0x480101c650424005d801140c01140300808541c03660001d070300c80e82e031000710030030160b001007a203108036030151003014030911140c909a119544c040c80740b4a1b0810145600103a2201850b106106403923840c007008203090380e42c0b844021041d9860612001810501e024803000142c441700000e44061402410303111030306001c565400b410000c3d0004e21606074120b848150203096070609214284030b07a48500c8041303071510300f030030350b508100c502000c8000e019038229a003600ca0785422404170342c0d000d6010040170621510041204a442c48022108009482061500d003034041064004e4139400c5104411a0065070759201901c3d190780310b030038000c0d41000e4280e6580141c030300904d0384240d10580020308032102450203c2c141455510072940b02d1150701d084200704203a01c3d4040111414a103552038402903110510044c025207800600c11458002e03503d000e404081c0c2c4081d016a0350040170441c0d4142e803881c0c24207003024035a01c07542c0211100d81242c0c0012402200b0320054038025800f580e2a85040c07404c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 420482491 1250 420481241 420481253
    0x5031801330504140906090f0a020d02180c0a020c03071505130e0c0414040b03060106030e07080a0803010801151202040c03180c05040e0106140609040623030705010905030a 76
    0x940807410003400c01c424012034182c0f070f0343c01000c611510b54070540c0e419140c8291440c0c01c0070340c060700c6503e02d50412140d0b010020000910b00310020b80440d16030004032194400142103402046102c00380815000810150407800350140c03191014030340a64428003004e408040d200d00c0c4501610440301d8144203d00b20a500c2100035000380141d41140d40390f8281c40308180c201c440001c0722000e4003110005414441040d05010745c0300d02c10000e4505201c45441c900000e6180c10050042c141007683d221440700340340320104400c1000b08404400e8401c06801c606109083d40d2090041455560078032080c50018015080c00300200e4000c0202c56140d8030396a400c1002800465101c00c0400d9281d80f400032049001c6400320303407054840d01c18400010320f010700b4132040d06c041694190f0107901d00101007051607540500440c19900440c2c040380d40d4072001c800540240030980080707820302141110866072001000100a001c18101e0840d107425640d4801120320404600a103901900613903210341c00030b24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 420483741 1250 420482491 420482561
    0x905090a02011b0f0f050708060115093201031b02070321050a030c05071208040b0a050115230c060403090e28090b0907030201090807060e01050705030c070605031801 73
    0x8407540644182980e1480c1c0c8e14548102038019141001c10740040c90043c50308000c80c58010305100340c4510000c1c4e000303801082000003030314040d2220511042c900b0703210303031103039200c164440c40d6036070102403880440100942d44c0c407180c04225010802a1001c20001640c03140c0302c1d01c401c506a44a0b490030200000840c0988000003204007401400e016480018000c0b260032800c00ca815940c9007130510b081c3c1059084601c014003118071031840d2000510a000090307003032507002c00303003800c01c030f1080f100c00240c2a14026100c000b01c0040f520100c0d01900008003ca5807070b0146000741d81d02d1450355201c0026034003d08056440000b498061240a43e0703446e41da003144140f040c0310302c9000a00b081c10f5111400a800200c40b900c030390b504039907414400c647c0c2000019000e0104032005002e003a00740a005012401160885170500a001c9043c07010050100100ea040c05100c3c800d0710744040c2c0c0d0b201c1c0075056070400c0c1d174180c200c041c207003420402244052180301c1c040c20248944280988218404100c95a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 420484991 1250 420483741 420483743
    0xf0610110c06070303020705100b0a0510090f030c080d050a0e101b1113060305151f08070303030b0627010221190c0804030213060905090a02011b0f0f 66
    0x40030706a0101d90a650701406000010700076140540d441010b4038243d81070001c2181d0540c1c10501d007039081e10b40307611061460001e891055070394207101180d000050f101c03101c165104500c1e00c80c2200c004402c1184610031041291001c030b04a61a0002418041c1d6140c02100c01b800b002582c444040c80c0c1f075141440070403100c49114204a600b4480c840311300c1e00c55049131441a115401c1c10000381e642c80c100005a0362600401640402203d810b5564040d00d98241c7c6161426203072800c40804d0300c1e4404500c10b2080c030003800c0c000ca4907407a52540c40584031aa107110a0300400e260401c04002410702000300d580044a003c191482201d154202c800004a8007020790304501c5401d1400da07138140700d400c066803a40c9c52030050355161076130901e6031504c6c0c5200d282d0003020424110340e401c000400308000c0d034003a81d604a0b507500910000182c034000a0405600c50a40d82d0708040902100203008140d60800e64004e81c1c46408071841340d4810f0b0400c49580400401445403210a00302040342c0300b540031489 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 420486241 1250 420484991 420484993
    0xd050a060302030a1406011d04060509070f0f031704050603060909010b1201061505040605030705090d0c060509011806120504021c0b2d0115180b0d050f061011 70
    0x101d450350007091601481050803100d481a260350b0550610b010480305004100a0034803030316040510381810502c100150004101e151102d01166004400303003c1e60002e041c4082a601d07249a0780c0c0d4060f4482d8401c0d01c41510910b04080b045212120804115016203030701a048528548411081c4000e00e40014400783e515560380304c0d40001941c413041c2c52600e04e8188070000c02c400d401e2403009c40c02a400013100000f800000c01082220f2078100069a86c04242c5060554807820b140c0d001c80c0700c03034070a81070040003a5208040840d07903d0f0080c0c040c00840500b0b98070801c1070503822941c00580c000780e008078808580000185a070102ca50341155503c24405081e03282d130007046081202c41c00c000c0c0310040315010020300c1040b1f503805069800700c0401424900300c0048182804204900170418000c4014416840c01e1000321540204006020305803a8010480c02c1992620340308901c2d040141d400c590142000040b40c0f0642d03040000d20300601c0007d1441c907446000400907036054848401481407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 420487491 1250 420486241 420486251
    0xb090121020c010906060824070c0b0c120a060b1e04170a0209092a2d15040b04050f0a1a0306120d0e101701031211120d050a 55
    0x24600c50026101802468001051440107440c0100c165501c0340c1101916502145102400c0001101c0304250f0302c007442c02c112019200e5160803501c0101610000e0185144901440304400e90390009110004141c0c1104e1001c0c2c5500150a00340c0c1d8140c85000041402400010260111941e00c0340c5404e00300c8000d079280554034000c220020300844c904150700d0300444056011f6040109429501c4104800642007451100c40c0c21814415002c1c40a81113240c1d20b202d480340e549841e03000c1c0b41c05c0c0c00000003400a580042c4540070b2007503994000c2d82c1c020010100170a03494611082a6800e41d100700391071906183c108020300200120700d503012036100f40900000114045617000111405c04513201d1076a0700d243c400148805103e81d820700d40c9040c0e1085240c401e80b10b03070000340d00112078070489200c13800c0c99030303414100e808242140803e80e414008400000806c000c032801e04469804948400d001d1103482d4251a0701c401004600d4940d03540100700000002c1413076030005901c102c9607180050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 420488741 1250 420487491 420487547
    0x20a060e03070915050a170303070806040f0911030715020309060f160501021e0705100905010f0e030c060a060b07060e10050109090c0b030108030f1e210901060b0901 73
    0x15102d107500304009844c042c04050102e81004d00480000c2c2030120071884051812004131582d07448010030550400c502140031401c01e40e07594101c94a02c0099542c2801112468140204408158450320b840303032242000009403c1000c10000b0001520360700a141056010301c14810341c2d034040440038900c0d03842080040d1190716101021603281d80502c0c00140c0700d4001d8155452202c0e414003032503500302e0b000c2c80050700103100010307108a04040110003081a030442d1800e5409041ca505030b8204150425001400444000000c3e201c020011030803500d403911050251411280d2600034000c3c007180030401900410180d41050302e41c040c041c404c4402c0c503001250790070b00302c0b00c00303030014404030351540f0000041c001d0702c82600010302a03d00610340303503500d0461116528416462480900344012079411400c03004100d041e0480c408045240740e4031038061031010526500e100203024500082c00c04103a59900501c0340d001602c43c1c101d491841d181880006541c403880d020240c3e003c0c2d13141110601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 420489991 1250 420488741 420488759
    0x30b180304061805030705062b020a0c02040f050106090e04030207090c0507031107081009050a080d022502010e0411161112061b072105030a05060607020a060e0307 72
    0x105425910343c03504210040c2e80c0d0301400d035150300c4a48242d21114080c0519600c010403240f003809004100c1040c400703500710580303030310507290801d951240c800f090070a0381d01c0d0840180142c4910031541007080c005081c246070220b030350038091500060400c60702405a2441e1448181d00f0901030f00480d440165502e40e000241d595a1160720f0000744089825400c00d60000c0c0d0b600c4020203124064040142032100e603039a601140d5004000701a1108c02d041c1c1482000d003c41c2d0003076a00301c0e28555a51140e540c03040d01a501200c0119000c803d604106480581c1b215030802c895903050b5500000480803004220182201c0d0314807241c40401082490611405000d00e403030818030070b00703015959a407800c2c01c10403200078400c605031803900480c0400c0303105c11b0039207400800310000b00425a201e400b541850b06048a0f078030000e500c483c2000c1d0740f030161070f900500618800d84403888107000c1661580d00f0311207203000b4080000d402c034402150a00a5a01608a103038001034003030200c030003242d9944026 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 420491241 1250 420489991 420489997
    0x30f020312010f1502150609070302040b030a1a0904050607030504060b09040516080316140106030b100e0606182806031406060a0203070303090c090603050303101509030b1803 77
    0x19100c1e48882e000804c40604040b140ea9000300d0140086c015a81d035244203035403600700042019100f503c81500280c407160082d416100501111030740f0070303182c1c07030300803c0040102401800640300300081c00c190741c110310f00488a94402c950250103020141c445003025406407501a00881d80c1c50380f07403403028181da2034800600781320ba800369004110081041c100f441c06800d00350402892500100106004d8040d000514408268801c909003130780700307103100b03098014100b50304000d0450200d201803043e018506248481a00c100c104030301000e071200d900f00800b038402c001d001d40580c203040d20160a240780054101291240f0401b00648103c002c2d0784569200d500d68100d0404030b82d03580c0c44541038115148a041d80034205a07003240c0350005411010703580340243c2000070300305034032800302408224104680000030280a24103004a0780c032880c3c4151031b03400840300003c10b14004040010078040c6200309060812850f00c0358000c3c141161a03072600b240000341882e001410106101440403410001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 420492491 1250 420491241 420491249
    0x9020603070203030f0c1305010503040507090e10060803070308010512070302040e0f060a060b07022106071d0415090207050307020909030703020607090303172d0114120a030f02031201 81
    0xf96039280b410745411800c54030050086401210103000c01904c1d64120820707401580d0b02420580c0d1203590b186007843c03400100c0d8006428090400360600c0360003100260402c01090040401d008058560710001e64038020107030060000f81c1e022004009509001246440d0a081082030f85c900c10340365000700c0d05940400c074403403980d588907240c104400380c3c00740011508500c1e90707982440484e02d0b10343ca00059000d44040030384150b6180300d84101c0600340d40100105241403009880c1145460200503000003900e0482c01c070300080440143e401031800b03108203002111000d403141c600c1810008107a0003500800000ca41d544130410912025a4400041500c2044030400840c0da4021a04d4002e0400308003402c684103120b004030302880003c3e000040c0c84e020b003400c05111080703030341d4901c081035030200109103241c03c000035180c1d00010302090700b05042c1078903074001e90442050810010f015854046640c407962580207002e50f08002032040c0d03001c400386006403040707a0030044044414407403000c082e80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 420493741 1250 420492491 420492493
    0xe01090b0601031404110108250909110a081504090f080301142b030c020d140105181902210705010201060b3a020409020c06090109030203160303090206030702 70
    0x400c01c40250380c140550b1800d0164003c148516003896503550380510503896a4034140090303000011112910711140048560003566141c401c0c4d007a0040161814103203014240c0541d0620280304540d08100086030030b001ca46540c0e50a6a03920340d01002d201041c40034000c0d5201da10f039810500494480c54000034200d024261003940c0f94500030b0b103585005803545c46075001d88112500305e101c2d10110000c8122880580081c41850580e07450b04840580c0d9030320303000354040704502d4000240041c400c2e6613800c2400c95002005035031550b0b4915400c1d5005141559015801310f0318034401c1c0004080c1d40c4131000e1014003810140c58002c215501c0b40e107040070030106558802e0500b04069031f4240030b400300421140000c140f8040700d515007009004101480c890902c0356401170310440483d9000c880d5141410004110b441c2c1d521500c0b0200a03500584544100b80300752000304d809550188076080505038160011840c0840440c8807456000c45010150b0a040e070f1605010096101e11009500c5008140c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 420494991 1250 420493741 420493763
    0x8062107050a06020a02030303070e0409060e0609012a11070503010507110d140d200a0908060c0406170a0603050d121d0c04020c03090a06211b05030a0e0109 69
    0x1c81440a0210b443d849041158050341d03080c00940c6010017261303080708240c40c0c5003501d0784816000c24054030a003800100000e10340010944080c10200791a8001c1e00d03d01d000f4403480e80d00d441e050501c0f1050640d21088010308030048403445000f0500d49414050308025a400b2a40c0c1e01d00003070840e2821241180810300c3d82400b0761807000107000302040c0c603107141071007a21340d82c65840c0300c80140100b40e50707480000c0d5241291111076031440c45034446001d041100301d584451044008003501128030a40003544101004145402a02e20940d000e881c07c0e56510a0790900c124041c1c0d010020203401070034015682c0302c0c0440424828002030b076040015440d2007890700c60f0080c2001c111b810b03254010b0207603041c144000c020904082505103040b0b0b01150701503190a41d8400d2142107220f080f41a507440b03d40071000041558004045d03501c04042581c078030010500003500c2c84169200142030180d002401c401c0003031030310b008501841d08160583e41c009480e00c009903903d8211840703404140c0c1c0c010141c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 420496241 1250 420494991 420494999
    0x608032b06150f171513050a0b0a0e0609161803061506300f0603050d03060b030c0409090f061e0e010225060902060301060c02032a0108062107 63
    0x140f4503810032580784ca4070072101c0c0b000e0107a1070f60660018205120100300010141c0b80340d40c522802e0b09040220140411042c103204500400609803800040d01076400b214000071013502c220f4200d8803520001c0c1008246695800290a00d040f540300b14005110b83c443c01d104400000c1c1c2802d001451140314000760a07820800d850b441c1c4d0089034440c00401504aa5400031a008196a42120b02042d141042d95081494900014000e1940140950f07403410f80c000050003070000f8540c0001007191420821151101410205403004a4030061100d400704410401071100358011900036020b9181d22500350650741d244000e4404848500c0c0c01400740541e05252032000c0d104030700c0c03c071686600851800c180000080d03441a03696170b01c03410b1265010346010074040301d5040503040a500820069a941c0c4580c07010b80322243c00c1406074007900c070743c060300440c0d0800d20241d050382602c00e80c000800700500000440d402d5000520041e04004200204044802403443d0140750754409009031248900b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 420497491 1250 420496241 420496247
    0x110301180f0605130e0c06070302070f05030712171603121b1403060a05030d02070614030f01030f0219080c01020624150405100806130608032b0615 65
    0x301c8840802050301d4044100059600c03a000307056200403415001c07890182c011034180c00c1104940145400c6880058014101580800e000041c0d5a01d5841f00780410f88690525513101c2c1a80200c1c3e540c5540010703501e011603ca000080d4116064a41491610740b100119034000f548c0a402240481c0c1c10258404141040d80145046c6015407100c012159200034402482100c02c0554424043c4001010410589800003c00090540682290150004a00025601c0c0c42a20540d00000e4201032645000a1400704480c0130310302d0400520050b9085446901e4031940e4148102d0348021030f800c82c0703c441458002094000c146000c09401310000b008006030a1600090400310014804201620300b11007411500718007140540b00d51a04015458860078a44903c1d000554442903100c080c280e0560300c02c00c0d151160b2000d6601600903025034902406503a868001c0140c550002c0c0404146140c500d035040303113440304007294203403101c0c00120f003202200c4480c1c200c2820f4458038012a081950 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 420498741 1250 420497491 420497501
    0xc152101031406250306030215071202060103120e0f090f161701030308070c080c071517010311010c0b010807090b0306090a120908061609050117060402030a11030118 73
    0x12070500034203200c0c030300601d2421030311000310300402443c0140c40383c13103011038403a07070210026603030162000b80030b0b11030b070364140c20707180c03c2000103c400d607540e216001511480881c040f4100c0741e11246803400d020148400350b5005040c081c1b400c0d04442d1070b1160005540c6c540300654011101c20006068606006425485030b441c0e1030261014000d440c1030307101c100d44440020b00d0441390189000308481d00c400008890000c0080805882c2c0540403500c240a04ca0102e401c0c0c1c11141054590360f00c0c01b0003040b082c0c17801c014001030000a4880c030710040020480010003041465814504100d101c00d590b42e40c406080c40070f070400d0300c10b58021074040c8a9100c091180d46061102100102811301d420240d881c1d5510f444000140a0001501034114003070248041c80080c20328441940c3c0180313011102c118114505941203c0018454040090700e94021042013020788035100301c10390107a4030f260a000107540b002d440b454a45a840740070490307800301d0700302071400b03805070f0b4001141c4131000c4d503105410340f0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 420499991 1250 420498741 420498773
    0x90b010b0906030105060a050712051206010801050612090c0d0609121b0312090b0103050610060305010605041712030c030a0f051e100510260105030c15210103 70
    0x640800c904901e6a03501415a811682c0c22510680d66442100c1d0860f10b50191240007801c0310f00d20441201c007213802801030150100e100055040d01c1d5039100045429200030703c2180c1d00a4001c209000c48a01218020b580c03040c03406044070750808400f804504240003101003074410310768400f4100100060604a00c0d103820883c5000140b2200580409220003145080102844103804100058540c00d81025412942042c00444a9a135030304210b515414215440b10104d910440b0103d07000b40a8032400f4180d900c42d40c1c8103402c00c7e040091082950000300748650040c41203084c0f4500c815201002580324400001c02d5a89904002800c08143c60002206900203818a000c01041d914034592681e46c0b105003001300409901c403443c50154030441c0340c00454004500381500f40d0499008034402c0d6844044980c0b48160044058002d601104280181179054018201f00d103040d02c0d250b0f03506054050341401c0310b454903200003c1c503e100d0f11030312044080c40c104840100144068007192007400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 420501241 1250 420499991 420500009
    0x60201061202010e060706060506070c0509070f050a140d06171b09060d08090301050709080c0402070209010b07030909022a0a050601030209090307021e040c090b0901050d0f0c03090b01 81
    0x440c1c91640068000702c83c0600ba41d00540c00428884180320207900f04c8001001c0c080c0c034455640e10305081040c200822070007801d005070750031804074901c2441291003004040e200d0b0b8841c0c0c00c00080c0481219451610035059050803414041120920b20f81e215030001000c00c0400c00d15641418031a1500700190b4456183c074410644200980700c1d1900080d47d540080100c51180e0303042d5491401c4a501d0042c40101601980b800040280303454110300480107444808089a134641c49103c10003003030348030f1504c00a42102422004200030032030b031005800224881c0c01c00f03004107a00d50070118220b805c104a2800054480c040320940581289280108000004003400c40c8142d1354448564404040c40002e014500d8500028010314044c815a210700350700030003100b1075466220003a40c070080000e5400d4401c0b85424041c2c40303401c1c015015a0200c07154201418200300114006640c2c40e000752188160b03854884251081c2c0008522034030520250545000810642e181840000700300160482c4100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 420502491 1250 420501241 420501269
    0x20910021f050711010c0e01031107150c1b20120606100e0a1e0905010f12020315040302030304050d0806030a2405040c14010203090d060e0a02100906020106 69
    0x4060103150303034100700380480038042003603250468110ba09071403030140b1032129480c11101086440e48003003242d0203060240da09004014840c40d54007070a01c222000186945928000f08070a82c00035040780304403d410303080804e440d00d64003842000c0c00030404012102a038109035075602d03521021161441090341592034200c000840035015544070009060984a40d003400302d05007159218203003144191101030001040c1a54412070908001924401d040d44005c05a0000c15a25168800c19048495003040c0040c054906100315174041c0301c0d54000e07038042c00f480c40e070203002440920005020341d20a41c0156070700d00e81810424146510b608510702000020f800344038895800164503042d032604421340f001c0d0340044600c0482c8400b8481d055030102c03070602c002c000038000c15000380000c951000300c0c8012204807000049072603100300c0040592142158081001040d15907209038080708001c0c0440c0c0000a103600010b0341e0a481d0b031040c1001030000d900a00040c0d60a000b00d4005240301040d2682c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 420503597 1106 420502491 420502513
    0x15030c0603062303030703120207120806010f030c09150207080f010207020307060903080406050f070204060806090f010603050d08190203040501090b0105030312010b0a0c0b090102091002 82
    0x40854080c07802c626580c481000903215a400c024051450102169800c2c0c42540c0c8d01d03060124020307401d2218000041e07220303021501a003050340704c246035407900d0000100011114880e590405040680c1200400c4d00b0802c440f05560003031041c8080d030700862000300d103485001c0d48242c503a07201f00170024504501c10b600400400c1d009030140d4042e6a225078003136903001c0c41440300405a0b60100400c00072a44246c0141040703130b0011014a00e8103c040e00000c007a64441e030003a4041c0c0e0420710611038031000070002044940090f600130700c0002d246440c0c4923225107242c001002840b44400002e03092441d0100245916405048110f441381060b00f0036134000d0100c21000c41e4000d6038100003040501c1c000098414404000065000d107a08116840481c0c0c0c000c084da10301400b40042820b03000812541c42c0324440d031036107000162503961603404c101303010100180d0a400d542200d98018 = true := by decide +kernel

theorem cover : BRFrame.Cov 420323741 420503597 := by
  have h0 := BRFrame.cov_init 420323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 420323741 ≤ n) (h2 : n < 420503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
