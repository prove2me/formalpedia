-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:18:31.347868+00:00
-- url     : https://prove2.me/submissions/05f356ab-658b-458c-9d4a-92d078a48b97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 61330938 ≤ n < 61510794 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 61332188 1250 61330938 61330963
    0x809010e0d05030a0902090108031803060705030606030411041b090602010c1b06091205040305061803072312070b0c07030c06150b040e090d021f0e0a17030a06060309082704020c 78
    0x80c01c01d2f078128140350000d075443c4142030729035955040d916941c041c020a50001f400032502000c1a900301c40d12602d80b48640041c0b2800c042d04000e00071a5440040c240701c030365400210031a41444044240c0580204044a40c017070b0094105000300b41c203007010002003820340001001000c510102c55100d81e401006013003681d01801c15140326880b150300c80d0003040d040010310001500148001001f0071107540c0c812011511541d13020303410004840c1c28900300840741d0f101450141001c40e0000030721000318180d80c0d1051810b0f081c03500c0c0c0301e00c2c0c1c0c07809024040c5442000b071090b40c480120038100001040d00c54014860143c40303548131515400c1c4041e030710004994403030790340c400c09130700244140c400204e0714003d19142c1001e602c490010405000a44010b401b420054031400b018103001600520110a1284c10400c40f5922030030f003680c8500641c0d04580c040006c140c20865042c022030003240072142e40018494043c1c460484000c21011505201010f6503440f600c00304a14a100704040341ca00202c0c3c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 61333438 1250 61332188 61332217
    0xf0e0f010c020a0f030c141c0e04050108030403240f06141504150215040f02011d061c2319090b060d050307060203160809010e0d05030a090209010803 66
    0x30440765040b650785801ca0303070241c000c1140d0801c41011a00400c2450480ca002c0d4030300703203000035101c2001c6141034240c180791032840352100f1b80034014a91060040541c068222006c3c0517030f51500d590f5950ba40120701014100c44d203c0320700015000741e44028968a550144000c4c05041040240400201040e2142c0200001c0b1414624241e10b00314601c20950540c012031282040d082c6280340301400c07007064064082d4401c00c03440c0c18148007440841482030744504144100f000742c6100040264602c4010f8070070300c0b60041001003c0383d03901c405030380c400c000100c03584801c0e0282c610000c000d0200c0010356017899400c1044240003246c000b171418890039050103100703c5201040900c1003280d10b000c501070101207041001c520b5034076089960704011801041240d04103819900d400c2c0c101e910503662108000c01039801d240050341c0100200340d0006c020f0008100786210942034a40f10704902d04108204280040003a400c40460b5010700304203a005060b0104070341c0c41d5010345170b40740e01c101081e26014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 61334688 1250 61333438 61333451
    0x609150903090307150504090501090608010e03040b03040305070f02060a02070905090a020319020f06161101050306030c330309011104030201090e0a021e0304021801120f060f0e0f01 80
    0x340c0c00004032007480300c000e001406183d1074250001d607450000041c000c100041000000341d504528000d89010b04111000016400d01e00801142113075440242070206800c00d010410440501c0c0c01686da1164240c10450780ea03c2c1940380100d0b00318010300e0005d50140c0080341c50300c011580055602c00340d408481c0104070940b2000395069440038600002545948401c0c283c074124032481c03040c00c00c1c1c02e2000c0d01d046510007650300040c04a8018213150040014481480c0c03090000e80b044c0d4004029080c2080f901c0c60a064021130740340c5003407509140c040c0c1034882204400d100c07141034981d45182c5c0c5448644116001c01c0d102c82c960f078016100c030301c1c8660804440401c4503504c2800c450440c0d0307050711610302c481c0c075104a0742c60703014004040203080c0e41d00f8055aa6036110785909021580048015607540e40f83c0b03881040704105821141c009014031901c0103100001c40b9402d0b903201c0941080c50b0520b20b07030003490803c000d0803080708440d003050700b400c03415504180700081d804c494100c90300091000c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 61335938 1250 61334688 61334701
    0x20316020106050f2205070c11060a0801090902010c05061302180c040e0a061d0915010803030a1a0301022109010c05030a0c020c0a380921060915 64
    0x2e80d07071140039142d0302000c1c40a034200249440f42c0c10000c0442099803c9420000c1d009520302201c0302129100f01040c012602c0303004000c01e411b1585109401100d90754200b40884000402541c014013800c450956504407080030340e03003e000c0180d040b9034401c0480e82d00c4c1c58040ba0150244560017400c038040c49000070042d04451420541d01d11440c00b0815140c1420303e05032402490715000740000d50303e182d50b00300105800e040341c0255070f615140d522303480c44a4101446214505218001000c804108010052042d00c0020003100c1d0007540e4214085040501034001681e44031520b6500c0768190702c0020409550428404083d40c144009400c80c030701507a40d03d00d036030b099a0b0144516000200200002140868564031840c0c00242510440d0130300b1003040042880d042294004001c1c0000540d40b00384d1032072010350404003240300c0071100f083d040380460b814041070040048281c880c4040b82d4541c6c02071003c2400444480103403000300e030b0140c10481020340d05c1d4050503070300411340007264002552 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 61337188 1250 61335938 61335941
    0x15090207020d2a0602030301060e0607110f01090906090906050603060705091909090302060a050c09090411010302070f0c15090501020c010807050d060b030a0606030605010807140702040c02010203160201 89
    0x20345035006001c000b08035402c1c0d603804450724101100e1060a040b00308025035005404480300d409483c054006503602d504108000d0014005d00c0d140d503201740010802080003c030512000440ca40007581d101404028100040c0d50381400340c2c21120700a4540500007a001e003440c0c102c3e441c514012841007040b500c525082c103464400468441010400404c885a507505000100c00362008110f0310804580392110304440642c1e50022003580143e001ca001c0c44880e8809200d400e822405070700c41e840c6050207481c0270444030100103101400806034580580b140d64042d4048a0314260300605840040d0427605e0902c7c0b0501e401c2c0a540c2028008554045845010355000c0003a00c1e0140c004000740700000004446101001b041d12041040034042c0d1066a030050003248050b180a140d0540c80b40380c0000c0100c1103a20301d50000c400c260819100700456600040d100e500400d003441c0030700250040902c0320310070744115000290802d1070a42400c001c0c41e410b40c00765003e414503a1304c20600c050303008400c13130 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 61338438 1250 61337188 61337197
    0x3091b0308030411030703021011010b0a12030e0d05010207080a141c0209030f191502120105060706060e16080a05010b0906070302010f0e0c09090708070302040911030a0303150902 79
    0x4207000c00400100d0f012525010440e103480300000c040742c42c2240c036680800c0400d404210200301017426002020203049084c042c03c0c031440c406950158501d460304600080c0c49040030400340a114012008030140d407507050140b01c1803508040255510492854441620b61001302c0c0c0c0c1000514020b41410200c41110488ae400410012481c0f1004454880c210007036004880d00d03985407041c1d1941c10003200c0c05001141078440000402e4818174134a0030140200c4198261104e5101c0c41009254030030192100b440d415500107580040d2542103a00d030003001040b19420444807691010300700181400311055a180c80d40c41961043e03440e840300d0b1103036400e80d0700a00481100f10014401c42c1c0d40c50410350054128617002e4800414410641c9022030300b1200b07000740004a0f90007100c0d071110542010710141e40c010380940d0003049524a8003041940300d16103800000e01c59905c41c1d4012090141428101c00c4403003008040e1041c80a25150250050640d09101103041000880c002034003000761003910f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 61339688 1250 61338438 61338443
    0x6210c0f0409180209041b060503040c0e041703090303060109090e06062218030f020f0606011209060e070503071a070b040501020f040b03060901050a03050a1506051003091b03 77
    0x38102030411042e0405451110b103580b01040c0b44820702005a42e5a84002e0f0003240191000311000d4090040b950224040e034000303405000c410002c0c0030014480602100885071000c5050010b900e86241080010070082104a803540000c4180400244088001c5000d0300d0241c887c230f003140e0343d658296420381f480d01720a800380303402160002e0818107081c03041c1c821446502c5041c250002038001034004440804041520405501e10700700c0426070031103002c0e642da000c0c0e80010440340000701070080c2c9e681002442c850402244003c1c1407a62002d981101014540c03240b0280a84401c520010341e40e140c1c2c6100e2907109110f585400125100302041144012510140030392070a650703511a1004058054400c440075036080001e007001c007054901420142c190703001240d55a050100c1046216601a0440d41c4100d41c45c41080002410000f120441e4992040d00410704a006002c05030080a440c2d010039003042e2070710140280c280c4d1591041116a02c60405410719415500000450140c0ca0000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 61340938 1250 61339688 61339717
    0x1020f0a03030f0b120a03030b040b030a0303020304112b0213020c1c14040501030b0307030215030103110f0f0103091b060e0a1a0304140106080703060509060601020109020609040207020a030206210c 87
    0x6c0000300b031085c2c110f50038180340540003044103211a0003280c41c0240180f410340020750b011050000b0403a46105e0242404401c4451813891100108580c032114290112420034100c0800b00a0454903800b0524406003101e0310304546400d446000c0d01d883d03c05841c4445080307840300307204480e01806440401140d140c0c4d014003d00341703810a4015001404000c1545505220785000000140d0710044075080380d4102c0104a03499525519102c01c403101481c041520803100601d156000340c480345a603c0709070009180104409400742040d982c2d90402d1850000c1c058401000031517842c1c1c01c511210001d0400b0380d000000076a80b0014603810800155280480c3c000401c086030116021002400d141a211000000d1045d9aa2003180c5090750540c030440c0c1032a1900e042000e00b03601400340303903880781003070009200c2c24045a00165451280580b440d124a50200f00c080654558500b00809076501401d2560748015581c0e410342c2d0842c000c1c42d01c103030550b803240010702410955015114400d990780f41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 61342188 1250 61340938 61340953
    0xa0302030301090e0705090a1e0b010824040f02091504030f0f1515061d0d0b0c040302030703051501150801060c060e030a120b040209130b01020f0a03030f0b12 70
    0xf0f154000d40364002c18041c03580305070380c404981d42e1345a50002c0c1c003a260654001440c000729070ba24248151a01c2d4255140e245085c03410000740e600702c20b0240d4003041003810046410a15020490709040c41c800086d005450b240342d6601d480c00c65401094003050440f203859100d600b000d0b82000300d100794080108030b4080e00902c000028000e8400043c0c1c644180e42d00f440c04800c2c6a824000c6600440c9800c4140102160400500f03822003041d0005104180600c15540202c00101d006429000d400900d000940b80010b00f03c102d1050985000e56070080a40390110f590f801e00c29035130100100d2a01d8603010a400004000b800342c074203494150280e8551a84c00c0c1c3c60b100096800840035030094800382d40383c2400c2941c21100340300912000020b80c072100c0ca0141c2c50742540080780c200d5100750340101e104000001c1c140d076544000038072076100c5680c08a1f2103184000101d00f044104a100d10092103107001e88000c140d00368000700700f1246030310b004010981021007000a00f0711096804840c507001250b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 61343438 1250 61342188 61342199
    0x10e0d23040e040f0503030702010b0901120b0f04020f03030a050d0e060906070e010905090f07031415060f0d0501180c02071a180603070906140309120c0a021f0807020a0302030301 79
    0xc000b1940305010389041500110f2a0300c1c0e80d41168001c8604e60300503507440b83c3c2c6420502d400345900f4007404070001c0304842c031401d13030351105e94800000c0d11502641400c071001400315504c400c0c59410902014050b04d4503401c0c111000b0307050ba0003045010081c9420314401d50600395001130039030320804081000b0645910384c0081a035014094403101e0b810041103003030104141e200e5a0040c0c3c0220b0258441403118900220000c040f506020103c030b0140d202c00c0c040c00010000d080040c0240b4000301d07112a41c58003c141031426500c19102140707880e904100000640b0503c0500401c480e920501e82441071030785200d01242c1725400d0340101c00704c2040c0d9619a42d4120551800b0340208540d020703100380b003e1001c20009200350012549103002620800060042c81e074814001040000f81401281c2541003020003da11580900d503405460840850085100c40f0100081d070150350b0080c203e190745000c1c860400248203240460031000c41d8030180412522440003550f400303c990140c2c06107041d6424103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 61344688 1250 61343438 61343459
    0x10b0f010c3c0302010510050a050f041508030304031e080a05040f150c12050c030115090f080c01080f0f060906060d050a060306050c070305120601050705010e0d2304 73
    0x141000c14030009490a00d00d02c4200c060816680440028503111440800c1e1400030700707480000b0074046510308400420849500e48410716002c1d500d0842d0b000d2004407200380850000e101040802002e0031401400007038014001c4000c50042c0d00036510420cd084007142d40318200d482c48030100c00011680400180860400d5000f140c1040c4150308000701d0769083d80383c0c407036103003901940ba400c40d07660ac40350003000f80e400c8040e2400c13890100d6001d0205180030800700060380014032075150703412801c4050247c094850070344840a004d04d402d81e00d4009403500746007951118621116404242c100c80801e120107609040c03d40f254900400b40421039441c1070521059170009095103401c10014840c00e00902018010584250f01e0102c0000d070580c6181003d0041d1400a0300440843d00c04100c5000803a034488222a00d18213049200c604584400c1c0041b20380e403186101c081c04c10352801700c2d0b0101110b408503040b85083e08070350382c0681e400118641c00710b00181400305410b01c000200010411410394 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 61345938 1250 61344688 61344713
    0xc030705070f0204050f0601030f111603031401150909050105031f0b030a060203090d09050306040f0c030b01062706050412050705060c0601060206011409011e050a0603020c010b0f010c 81
    0x41c2c40350b0400c0c401d150b0b010400351030003941e0b4440f60126060400c801303541e26210354031100c10a070000307008003400301035030b4006481040842006c2c1c0b040c084084c400c1c14020f80061145040040720b00c80742e9a550503816184501000080e40081d06110780050342da0603038098541a110000c01615044007411802002c05801c410200d203040c0e03d07481045040d42e01444450304180c011100584e40e842e101106509203015070130300c84107002101a091049860005d074032903200342e100c864103a9170201030604407000d0600b54401818404003a0002c07603010740c4400102d103250161040c5c040c40d59270f50503d00c2c240784414002c0000254050100b0081d80b00c8291442d84600d00610644681d680c030b89011075200d84c0441d440e014268008001048116410488903004000400070769165001100000d0202e120600c1000e0061981021060f405004012102c00803c001050b5111700380d650a8046c0294200c0c50010226511380440803159040424054120704416540e0040c00d005070f5030783c05240690b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 61347188 1250 61345938 61345943
    0xb010608060420040807091b0809010902040914060601090602032a0a0507050a06050301030f080a0e040c0e040b01050309100c051b03070606050613060302030702030c0601150905090c03070507 84
    0x40711106003400e408594509070b207034800f642c4101e0380d903401e004400e0715141e02a070058a206150a80007500400c041c5052100c641040c90106001e031203400050780034103540c80c0065401450100003c0c10050b001d01600754186100d02601c2860396504010344880c0c17140d04c9480c0241e0000c2100b03c1c0c0785c4070904000400b80c00341c6a030803075018410700b00382451b041c0105003c40b2243e00442c4140000e1824840d803030b0041c000c2d440d24610719030441e552400482800c04004041850104050480601031054507000000181040042002c1c1c1c0c0c000611a110742c0041170702075450528943c1c0c0d00d5226000b103034450000c1c0380050841e800074804030001000b0400000080060910941100c001141c202d82c0c0300d010301c40000d40d00d40007141408012108503900c0144034035810030030120848407403e00401140c03628200140c4a0f5502407082c1c1c1184182000c2c6805409044008144d11440c0020405d800a032075075907004050f110824006000b109645c807410445060001036041446000113000003032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 61348438 1250 61347188 61347191
    0x7031407120f18080301240509130f0f0f0e0a02010c02090405011401030f05070906051003090203070f0f08070b0a0c0b0402030c0904080a110111040e040602091008010608060d0b0106080604 83
    0x1080454288003c54103420b040340c1c48000000108281c058a081802e1805400a50054034903549a4040c0c10742c8690074440e40210344a54145144610a500a903a51005035800b40b1540000382004402400d05070170007820107203080d4244908a03000520501d1851781a155503c429800d502044a201c070020300c03c954542d00c52141d18107071200324140900851189245d10000c284900d442810407501e074000c90311061901c03200b0002603540e0800201e01c075030b6608001860104500100c4c1c02d02c440c4c0d4000f0150300200f41c030000703043d054043c1108101d580100544401c3c40d100d07011100d20344900c0b5030a1001032082a81240410402d000854200d44000c0882c0d1401d14008041200010122001ea1340d1f40000310310492a580c00c520701c1c0c100c0d84000e41c000c200880000c58242c0c0640664001d000ea4001c542000908104c0d1070360486002c0d150062100804001e0880020085082401214002801d440c0032401780d05000c0d041120b05039100b810a096a0308000040701e040744000c0c00f403503005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 61349688 1250 61348438 61348451
    0x14040620091c06020a0503090d1d04090302160b0d0b0a03030903150e0d0519022d0309060706020c07091812051612090503150a0203100e090607031407120f 68
    0x20f40da81c402040c00e5040b644480d5160324040d04500c2c200f10501d2468420701219100d012071401303d9884071441864222030004042402c0d060880c1b4044039800b002910103500000801c0c10508440030b4044620901d03010702c0324103400b07814000c408005100040214003600d10a0001905a4a000310f04240500001448140380440140340c410940014400b0a0000926000d503081800c444a500c402900041021b400e640c25080004404043e5441c41400d69207840690160306000300c1d090030310010849900d0f00d1450500c44005d41c441080a00d880c4940c48001a0211b4640241c440c0d000525408543d03004960b00cbd24195200306c04103c00800c10101b10704008015152400641c1c00d0107000a00852011a003000d8290741c1190002d40c42607024802020203102c1208842c0d90000c0040390150b1070762076000030100001115000195050000002c0118403080002c24900c6400c29941c01d00c21030301c11004000c3d1503d0250750702c2c4001819048840640a1203802c01358500103000c0c000074a1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 61350938 1250 61349688 61349693
    0x30309080f030c070204050601020a03020d0503060307030807061416050702060f0403080304060b13020f04090b03031207050d050123090402011b03030203040204150503060114010c0614040620091c 86
    0x707641c01250300100c07000700442c00c041541018895075601800c02e00040400e0b200390b48005e5a2000b031902442d04101b4000000340040e1028400600111761250b0002d0300c03a1110f10306100940510f17800303610510011400518001c4095581c0303031074070805071280382c07405015800f800065402072450707002c04041040004002400000254031440c05030030300041c00000c41e4200904010400e03120307a400381c010b002919202403654102d4040719800c060000d00c1e0f60000021a08500804074120341e0900d41a040209a6800c54018166458401020800c603a2220050145200c060300001b500418118014443c1e05100410542203401410004000d03403101801c1c1d05083e81c2d9220031000a500071042c00300310304003401641e0448440200e0015541d04040100360340b000d0510400140342c4140c1c0050100384d00a540c900e402035000714003407001041c0108600707a154400e0705d04840580c44c1a40741002d04480040b9408071062461485140c00d81c031108001c4c40ca45401c02c11016072085800d120300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 61352188 1250 61350938 61350967
    0x9010204120302010e0c0121050a090206070b041a010609170f011109010813050604020d03030f0c080103021201060b0307051b030c010c0908010501030b0c1c0507020601081605090403030908 83
    0x4401d100350700100705c21444140d43d900748080440c5503418090420a040c2e690000101a281301910340e500000f05035035160720a80c007408082d4006074000d500020f00a0500081449285c8218095542100780b1500d140d003480000c1c009218420008600c2c01062103003604d80903071000100070306000c0b41c802c2028003941900b11011917450034400c4200146100d11545c0001040d80d0104001b0329000300d503240d07a1103090319940000c100922608410040c40c003018081e5201d800388001d842001c004881d40a035010300112400e02059228615200140a950310305004030f40039501d103c04460b0454a450400b40c8030b83d00002c20079070070001c41901d4292000410805000e440780d03120004222a18400006000c100103500300d0f062070b034140001400483e40089501d030b00300ca2180c02c1943d66201c00e840c00f060407041128499003080c180001c1c44441d55000071068141d80004080d18146441030658001c05100341c4a02a003141140c0700150209003c0d0348a01d01440c080e500341442d0503054802040d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 61353438 1250 61352188 61352219
    0x12030c0c0f1b040c18090501060212130603090309120f0308060904030c060507020a0203010504150e1c050901090b0309011a1c0f0602040e0c0a02010c050711040518030c01140a060b0301060809010204 87
    0x2988190754600401c09d0b5981008043d034015441400030b440d00028482c180b900c012580203100526444d103020204242c442c507040c1006000442109048016074a00022101d03048401039000550700c0d0301150140c940300039083d00955040e120203800181954550740540b00092010096004060505d00540c9003030203901d108502c01c0301c40c1035840d15a0401001100c0b400b03a106441d41e40f09480b00700610000310100800003403030f81082038a4000241c0100c41d0340c0384940000003480e0b000300070700841980541260060000270707040b11005e42c10180900541e552841000200340c4415260000403814901c207818049008902c058949500d8101c050000b1030203035002045c1e0507002804140c0e065086c802e44002c59810701d426882d00803c2d40321060f82562011a0ba80704640c0d800110700c0c4030405215942d41401d06078241e94a9940c8518000d00a19481c0300c010f061250200000354a071119204100580e00e50706800c600710b0342041e104032800c050040001100f50b60822010607080c60903030b42035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 61354688 1250 61353438 61353449
    0x60e0f061917130201021509010b040e0d02010506120307110301090f050a1e121d12010204050f040b0303031f1e1d0c04060c030212030c0c0f1b040c18 66
    0x3400e01c0e40c100c8422414080b4010031858003003400042050050383e001c00d0600300114140384900d42a01c41001803801004007041403544035181205150440c200881c02e03000c2515503030001c000c00c1d5554010311850708a6204440181d8004000c4d400010707518200390b0170020401f800001c0e003100c1a549400c5054041c0d081a103081d80084104810404004124440c82c00b1483c1e041a042560b0382c1c2c1d08191040b1403c1040c288010050081020b140c41482000d81e0032004080400032107280d00480e000750300c43d000f5180241181c4040b0030090400780a01c000000d80980258a17540e60100e20204a40400180c2c070913440761044001a0b02000100d03404680d8040c1d404e140c1d8823498961011482c04002c004c1d07002e142891020000040b030882d098030122101ca082003040d8003803501d0124100502d0f00140e0f41c4450011041c0320a111910000e02442c0d810b0100311000920000070450b40c81c040311001a2418030300001c05a01c5091039000581110075a0034515800ea0345000f02c0541d400e10398006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 61355938 1250 61354688 61354697
    0x9150207120201020c07061d0a0609060905040b030303060906011e0302031603181514090109121805010e1305072118021203040f080304030209060a060e0f0619 70
    0x10380c1403050404001040103000d000071490007040f8030006445020070300c1440240704401001d00e18078a40b030b1141022000008046c44209612410b024000e80854050b00c0009821040080b81505041c8640d00f03010310000d000b18255600c41080007009000204000e04000343d903c00807102d08800742001c00050740c2c5440260300c0345032844c10980a00c050342c0c031000c20141000c0c00c4010030400703105100311a9405c4440803100b0003107940c0b4000034044403000003c405500800b040078844040d84030180300740c41420110081c59503803004541c00010318070282c280309901881040300d58040d207a10b1081c160050f00c00941c07040741981010031142c04a8500b40840d4214100e4006d0307000030852552a038140320303402c010341030b01440014114814102c0007030283d80820410b04201104005a80043c100011882000e41e01e0704207464403504070344000c0b401400140f021031258030744011441c050322255600c01d10204040380811002e0260090910b0700920204444c102e505d0011949608418513a04c6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 61357188 1250 61355938 61355947
    0x30a0b06040b0d0506042a0e0604061808010203040c0b0a120204030f02090604020a020309010804060608010603120306060302040e0718031b180902010806132703021506130c03091502 80
    0x200c2d07000d4444c0100a18807a6140181d82e20444181c0743c200c880540d00c495401b1000d904070782054440c0e0f6130760f00c0c510751700280c00b1400099555000e050a11803501d8101c20300705a903038902029090740030a0340d00600740c424802060060183c000042c10f42c07004546001d10f00d0100d00a0b25108980c0706800c2a10f201607006260008e5003440e0304000c0e0000c0c0c09803403c501d004e01c0724900944a000f0700c0e1803d8100040c84010400744526a009503001c0d0000000070042c0c00c0c1e03249000710100004100440c0480d00700342c800904036001e07100752002c0718922224640240e80780e0600f1107038005000940750505010b00c2020010135480810b0803401c13054114541017180c24080907640c6103c00e03554922809050446090050b40d100c1c100980211055918020b41340c1c14030310702000340122021114045891016801484502e0045030010314020740940d60040395540b42c104013690211080d54002c0701d44554014140c54540c000c20211440303241c0003035060b400350389841c03144003404070b0038124540104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 61358438 1250 61357188 61357207
    0x501030b120d03230109050106180e071214010608240a03030806130c020c2815020102040b0309030403021009030309030f0606080d030c09080d08010308030a0b06040b 73
    0x108a441000044074103468800340000015940c000106040e03041507161041c4d40194000219201c40d852601c40d03a001c882e60311508000010442407186a00280140000240301020281101d06513000d0b11140c03050380c0e4510106603502c520381d108203290203a41d41d001c1e0008400007400d8038042c004030758554000f8200300079200c0030503108a2201810441c02010340880356035004068046079031500b0038408641c0d0390400104414130601a541d402420700c0100d803503041d80882e0765508100200c0e00b00405205902d0500403020304100e440b5484000718000380300340610713003046030908009840050301d481e40b9000b070344060b038000b80c60101d020741c40440c0c24403c514000540c80c40c21900e03460490f5220f891610000d000500300d101c05000c80c41c2400b40e000a00c40642c00442c058803680044550361a64011300600514004030142c0c00a814004086000000072070381290090050b42d4018840c1d08548500000740d20160030700410541d56012101c1c07548550020700003c100351646640c8404000c1c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 61359688 1250 61358438 61358441
    0x402180a0605032509090503090607050a020103050f0613050405010b030f06040b01090522050a0812090d09320d0b0a0e1903050c0c040f0f0f0902180c070f0309050103 73
    0x658456044401a213050140250540581000c03940c0711480800d0725030450a07c00d003144101982c840d044840060980c1c1071110000e244048a403007a601004984e54070780002d0040e00023070703402661042508416500ad0301e41c0e41c004c0f580060282000003035820940b8002840c042c002d504071700341608200108001e21130190305071401051002004d22051038903000c40220002c46101703010b0740c0f89200103030b0f0042c00410800424140c0d40908042d0b9240c241081c000d110403003c4035031490a208200700c101072a8801c0c11864102e407234080003211141c1e400b00740c0900c40f03008a030100c10703504001e01405c6d00315918221054a12405540c1d41d8209003410b403400f500780da540804800c400d034822104e461704442e201400f040c4c0c194142c50100e89030f0304418205414603461030403050b405030500b01041300300d66030341d4001101c400341c080003040106031a901020948591082c0070b903000340c030508501c012505000302c40e40c2c000010882c0a14020760b95407801d10360380b01d900307040e4002500010240041e5805 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61360938 1250 61359688 61359703
    0x3021e041502061303080601050705071d06030d03090c05060f09040624020d140c0114090c010f0201060e0a020a0c150f050619030618020a0b0c060606040b0306090402180a060503 78
    0x10b08401040a0000345c8015052050203030109042000009085051200611101e400780c0546900700406000341020422003400c2034031403520038054041219004c50280c400e298a1170b502503120031040f850101081603d4203c00348081c1c489800304401d4099a445110700c80140119802400082c501704c0585120703421580348100655001c0105020140d401400c3e039010221040c41365903803020780c0151341d030252400c080a030240d507034154140116807401040c200a955400c0c1da507005201104c01d8102c0c207991144c410380c03032500c0704280419140c0903140c00802d072031416801c0c8505445016605c880d00002d0001100c01c207036a6500e601c05080c201c60003041d03000380702150624841020240380e011038610a00c00103103450b5580c46d40c20400640800c11045041d00107001065995440c00d485259a1006500801130700455002410601d003c80a960030348103c000703014116034920060010340300e4080c0041e1b81c0902c07481d600300044400b035240544640e6002c00e002c42c3e214a04814545404130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61362188 1250 61360938 61360951
    0x30f0b0c0a0c020f0103020d0903020a0204111309020901020c1309060b0901031e06110403050714030102040810020d1107050309030606042f0706060e0f0604020909040303021e04150206 81
    0x3004109140c0d0742c02020007280540403111283d440b030034400142e00070b00c2140d14403030846080540e03ca0916130082540080d55009550070b10205524060144252040e800c81d107003c5180300c0c80510038031170994082c00c1d07072000c180100c0d890502604c0000d0b94140481e640054003507124070703003403003000058018640102030030380f4408041d505541d0f446040084840318ad0001d508034107502d4043c891150445140002032003420342d56507440c0d0816940341c0f21036009290381c5000d1208240d40c035003014400c584c00c55000c440540700449815405401952142c00d004403a01d8440002d5148044402c2c02800c0c1280f1403002181d890380114107150810704002c240600c11441c041880c030b1410392104150603101c441445c14402c10346503d0b00348165000d2544041c00b0a031400701d01040351980c41614500070159100544c02560765002000b003607110344a01c042c3c1010848006c500008d001c0c1e005403418000181c1990080c044030180054590400d038030450360551562140d119080d01444130b15041134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61363438 1250 61362188 61362211
    0x51917040308030601120b10051b0f0309100e0310020d05060315150102011407020a0b090a0314090105070219050a050108010b0a14160605040b0601020a03020c0402030a09050601030f0b 81
    0x1451902c602415000051103d410b00c21000f210000d0003e00d640501201e00d8000e0500102e5280c0580040c1590010000d0803c1807a003c400c20141c44000113580d00b008030b0350740081d403070140440f050040c81140041e003001071140c0618548815981409408081d65054400586440550154070141d03000a1f060364042e4001d040300d00c07a400c140c255142d134070005288409118410150040340103000407241c82e11020f03c80000d1042c4a60301240040c01d50b0700800080c211503c40d86800745c1c8400c0c0300340c00100812124050500c04251203c040e1000d2081410003d05000098012038002d41c802c07220400001013911302402180b801c0d68650010b49402e1030226140d41c1091030b40c00d841e1003401c200000f803054003051001c14007099400c483d000c0501c0d41800c410300c1d4041c13401c0005801c0540c4c049460402e400002601d951000420b1901160154001c2140e8200c00013403100070f60029201000a83e281c28905000c14010072003140207502c03403900c1407404100780c103100c0802d0101601e00b100301e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61364688 1250 61363438 61363447
    0x50717031003080f0d02030103080c0d020d0507020d0201090e0a09051006080c1302071a0703060b070206031609050d0503040e060d03020604031202040e190b0906010c140a051917 78
    0x304034008040142c80c0c0c003001e5903948220401c00810140100c00d40350b0b08240c0000004820000d49802070100d04031040c08031104841c00c54026a1940407403009400040c8003030003928090b02d4000840b802950040c10030002c4161100340b11301040340210380d09089a521900110108002044490303c4036141c44803c004131070603d5001625031316552400792007030680070000395845441e40e040740c242c90740c000070340100c2c0c281035420210301d28411980c0c000400d281c0000000d0680d4030504945e051a4010f0029140d80e403180a4403000c2031107000346400f007005050012a41307482e0150a00105400b0364025600c5528100c3d1100566400401c00c038000d0340b0445600340042e40008170303681c20a41c94103103069940021856580280100d0380806021801c05d4144200e1607500c207809447c130003034000f0500c4190b4509090003c180b000351040b40c009454205164081000440c0040482c0c01e5181510358446464441d1440d05142003190958040d45000800030801c0340d204055403088480030860a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61365938 1250 61364688 61364701
    0x81005060318031c060b0901050412151104030c0807030834030905010215040506130515010603051f0b0d0b01050706092405090303010605070312060605071703 70
    0x41144105405444080081009030510140510890703410408030b03521045989141412802c41d002032812542c6814008160b0000ca8003c40c1c074032240684506181c03500e041001d0840c1500d400064802484e0700b0800701221316107000759148507000700c48258445082d0705041011021039400b2105c15031018504200040a210545a0226509001c42078002c1868901d507400e0320495100f06202d4848260039081541000d400c000b42ea60070307400c5030781145c00301600316003440040e60003078255440349000882ca01e04010a58064a204505544820f049040c0190750010700381c0000c000700e5282c07000c0041040000c58000890580b5091105d5041d16100d0011280e1046401c00c0321007039200c010120310707a4060303821601c080d036000e182000b15007000e0801c0e81e00c5040f0340001240110b08a40000c0a98a41c1d020307442c0249001e401851441e468003e040c0c2d400e41c01018120305105800020910380d4643e071044100908041d01e800ea0b9900092070100c02410640159050407001481440700 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61367188 1250 61365938 61365961
    0x909190e06060312071b061815020a15060504021206010212030c0322080309011e02040f090b04150905060906010c0b040201140d06061d01090803180f0604030b04030e0108 75
    0x2401c1341080c0e00c140d03035034000e041c550750005c034007048414008500100003907034a5201d40000195543c0c80d80e0004166110040e40710400032a2405100680c090007440c8042044500501c0208482d80d00c0010300944d550046020b9802c44810590380ba4900c01c100b00140d601030121102c0420005816840c601d860b603011042c1e4003004d005441821130580c40c04030064011514291925000360b01c142d1686808140c0c103000c0c0001c020000c041a0381d040043c070701d540b803074000e8406451941030340d07442043c281040d44000b4480340050990103621660a0b16445c010820580c01402d401800411145050401c1c4803000e003028203094108442c421000001c5401411500c0e002542407800c2d001d1010b503082064181e004980c24130001c10301e4454006a40c0e41c01001086903600c0e042100d400c80710780c001c01581c031402c00340b08194446c3c0041200145225000c03015420b4050001c10040f020360603d0003094064001d9041280e207580e041e0b040c070081c550001a4095105002d181caa50b00d440d00465415 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61368438 1250 61367188 61367203
    0x10e092e0b09030d020705010c080702060d020f130b0f1e0403020d03120c0e0a1203020a05010f0e06100305030306150f0703031d010506030705040908090306040b060a0801060806071101020909190e060603 89
    0x30072800ac045102c1c3e045641c0c61080311540304640ca0155240d00d0884201d40c0580c0c0801c41c64a48800041400221300f4444001d841d2620800c1003180d0030000110b40030500c0450000300d1901c1b0795401c000c007000603aa1018000f1a05000369180f90000d040b807035134101282c0030560000103016032079555031115611100c151080e02d120b205e68500b03e910900d000d070700c3c0201b0000300410b25400e00140800c01095a8000c80032041400115442920707400d1007001d16803524003018240c0d400800001e082400c0114400d2000c0c07202051a92401040c0310707502080c5d400c0010110700003600c0d603040f410f0810342d41e0030308e02001c00300d0402041130303041400019588207403600c92107010f6500c5114480620a01e9000d5401c100c1e00a410f03525145081c0c6055240c80e00111100c600c680305a80010030310703080521500e004d55022500520080d19241c200380c0e0350082e40c00b2101055902082001c84940320070480d107002e20040f000751950030388856a800f0a85025100c81c0c040b0f54000801c010704d554000075000e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61369688 1250 61368438 61368443
    0x31005040c200d090501111902010c0c06020c04050105180601030f0609230903040305071e080f0d020c040b030307080c010b060a0507030e010e092e0b09030d020705010c 74
    0x103480c80d910002030310307100b0880300081d04507010102e01c1c0301c900e070300800c800c641c0074030590307810508940758001550040100c1040c0000c0380e11840c5442d901715941100d81c00c1450050422814400407503541c1c503405180d9030002001600400442c2100741407a002c0c19000d01411690003070302070842c032007100d8050701c0104010b042680701d9035050001c14081d403121004d402d11400c288202c0016040c0700e0146010002d01464882a21001643c0020040142c4080e43c0d4071201911105241c90420503140d0f08641c0d00c01c195002c11000013505480c00c03c50341d000180c80001408040c0070600f8007a0030011b50a041c60300590401000c00c009a4001c005c80f054142d1040800c3d8035000700e0305206005114500c45160821000110010111b4010740a45000c510995940c645040300c0001121003440960500340c01c00f000703070007250003000c82d40307071480307030a03010f0000c2042ea1030300940d00300a5060030354405003401c40c00040c40c62050501f0300c08008c111110f400100250707403070071000a1032011400b901 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61370938 1250 61369688 61369691
    0x60801080307030f03110414090703150b0d020f0c010e070b191404050301050f04060f02040f0905060d17070c0b0a02030412060204080a03030501090b010f0e06070215190f0503100504 80
    0x701414280251b100c0f11498464200103610b0f1501c03002502d000c501c01043d00d6102e8008440042c03222440390003520011902c500c0241186440c000141a480d00301400e0320303250075001d0291200c13030080300d0050028102e0482c00820a2501082d1003030a01d0100d0f04600c1c28000100070680300701c00c40c0120304401019600d0700404090307410b41121403034000ca81019506508100511802c406004071050040d402032908020710a25028005c00324031a611030103043c8903405004100c1c0d0b1166030302141c0e200201800c0c0029041407943c41c2180e204210104161000340401c0321024461104d03005406080c200740580d2400b420040c029559019030304c12045070f1007000b21028200103980d01541c00915103e030807a0394140607440c02a01400302402440d203034a103080c0104c2041d40c840c201501400181351c4514070034551000500100b03901c45141030340c210350326138500c00072000d03942c0c01004607810001a1035046080403000908031110903031100304100c418010300001b2012a20b02c0021078008550 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61372188 1250 61370938 61370957
    0x17070e03070305070e060a1203080402010c020d06112a06010b03041506090b1005030f04020108090c030a120e1905040507091502160807030803010513060510020304030c06080108030703 81
    0x207868068681c100908a000d407603000030350050075501c50f50044004480d000d513100c1d113801600380c04411307408001c3c0c001560b28000ca0050750190030400305950024244a05c00c48907502c5070030031740b840c000d880e000c41c00e00040d42c0244112400c021807034151240b82d03149010f01c1d0440006e0b45e03590b0103001c0c2440c2034400201107002c00000804030300c420b40711941d042c0182692100d500e0003d101004480e809910420100d1600c2c5104100b201d00c51b02c105402d07080103454540044502400c000c1c49809280320320b0144186a40d410022441824403d1401e11044030314428010902c0c00b00c0d112080c00b8101c560440c00c42100300340055016120140c4002032690750760350342100e00c1301242d4000040202600400b000169002c198005681480e618031501030342d070345002c40d580c1e8040307103c0600101d400b40018071203403400001d580102060081c0204a0301e4445001031003940820700882c0c0035920002e000c1041190b04030b404402844541444000e540c07420800e40d403203200380300c4000c0030445100e0303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61373438 1250 61372188 61372217
    0x601020a0515100b0703120b0102070503100f0e0604020d030c020d02041127060a03020c0f07060c060b150d0b22020a020105090d020d080901020d050c040e06011707 72
    0x324201e4110045035100c041005444003841000d4840c0355160600c9103002c500d445504044808865165075186100d0b801052210300511318003d0303582c1140203008000a583c0e4040150034494038410000003035441c00089900d086445807090802c49030031001c10000583d0f1800e000c01505a01400c1c401d883d08143c0c400610b0040320000000d500c90701c2e02840030004040c00024180d800052074103500111412010301c0c41c6001e6a1070081d91001d410444440c11a00c20f4001c2c100b614584800c8540491005020b14106009a0400000a16401e113042e083c00910b00074021100000d603051580802c500301d00c03042c5489003000d803216041c1c940078000d40d1074468030030b00c0a40009201001410200c4503020030042d40c0500d18000066082c4008161195030104c0c079090052011f40060681d040802000d50f4840d000810510440d50b0900000d01d03484054042e80e44110012440195250306204200840c13a50141c605c80c10440d207109a1540c0c4100030041d0398001045007481e06030036048a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61374688 1250 61373438 61373443
    0x209040b150307140c061003020f010c11060f0d02040e060117010501020613020d0605090d0e190522020c010903030e01050f040219080a08092701060509040207140604030e01031505040203060102 85
    0xa40454450b46c0100084078140610b41c1c4240d9100311140c488244014004682070310852601504900d103681d0081c00e03514016009040380c603001c03c000d504044c0302d5241c50b01240c000e54403001d14001c03c001007042d00c1d03900c4000050080041c0c045102c083d414400003c0d038584008010044010b0105c200034255501d190501c0966030b4080c0c014002c03464400d500e0f940b2007401d5001d00000c41c2e03107803010154518002c0c11a54080c2d011180a0a085140004001c4440c8007104142c1c000c1186030000300c91110107000900e0303074251a0002158030b40b6541344c0103003101c290b50f100700d05071391404042c004050340d6000095003264040314400300c038161178040e02c04030313000c03952119180344983c4510300204450306014022100e07003143c008440300802e1020542d00301c4100421003014070030070010b00030103028001a00130070300013900040c10f0103110703a00d0803007407007411401c2410740c1c0c004010002010742c0100311100b011001e1805100400c41c0009503c40865030380100d80c0b1503500800000c506034401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61375938 1250 61374688 61374697
    0x160e0105090421020106031509050303040206030a090507030c0e01090b0105071103010b1003091506031502160b18010c02030405031506030109020603010b1309180f0c03080408010209040b15030714 86
    0x4400d0f44948103801c4800c041d00030804d902c000c42c1c440796940c079200d42d06141d038412007800c0c64021003e107255a8856007001010b0303000501c0400281c0d500c41182000c00c034200072a6014603c108013444986007000740d0301c4c101000503402044c41c14180501b51000b643e000c800e80e940c0c0d5170b2198440e140c00c605100024054121081155000256000d200700080c0e0725810940d04a8050954011001c113800200c4003920312500015051225800800c0000e2541e903009121406600d0120010000302d9528041600c6050b14220091071414410701c240090078414118000030600056103403c1c608404030b41c81e65409444802c1300322400c0002038140d1000e400c8a640380d940200181c3d07072903031200e030040360f2a0000f040c8008004d51001011400c00c40620401040c0303154101e51a007102100ea64440b60031903501c0c011a81c03c118200000f0000704124040d00190030448005038507480c101080c03008403201e2104441c4154641015045c5000380c1c84c045030780101c0940750070319205006042c0711905118 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61377188 1250 61375938 61375973
    0x813030b07090f0801050702030304031d03120909100f05010309060f110a090b030f010302090415050702010501061b120e0a0305031903050a1b031a04060e0603160e01050904 76
    0x655001c2100495120081d00d0540e6154041035100b1500c840d049400c840044880101580c410030200340480e0140c00c107241c3c2505510b110f124210300e403001107800c00f010010008059000801d82080c81d01c4c000c2c4000b030303021000e0014200c19914101c10900c0303003000c40c410340b03041c140e44c2c04903a018891107801a8044e500d101c02c041c0320b0762211101d071034a01d602a040d00c40004150460208403d003c2d10203ea0140c0312101c03104010740d08540030020324500150044501900501510040c15003078000c0b6841501c0c150000a555850000080c204020b5080b5000e047c08080c1c50081c009040b010b00201c4020880c5020020403410002117141c5034819080a40580320102c1d82c80e00124010a0012102c10b00c2d680501650b00c0b580052403d44007041c0211100348010142d80f11064843c0d4000c641040c0604010141030507008042001c9074400d0f004007060240741350404c031f000d080400043e8460123180b44100a6945020350528000030103000d0365105020420104042c0f000300c804800f518034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61378438 1250 61377188 61377203
    0x1303020301050f0103030215070207051c0204090308150d080304120201091703010312030c0c030e0307090e0313120f0609080d020f03090601090e071202041508030409050603061003081303 82
    0x2c01522028800c3c8007440100c0c0148134107005402a08900c443c160b001d00d51680040c41ca190600301007148561401203802d10000c10104082c0c003613510780c06107240d010f0094072840c2850030a1144a00b92041c2c41a43c41d0064401003084800505034404596025030405410b50101340310f80313012405081412405085010a509540c228403607c4000b14100e07071203042000c442008880e000e505645100700440d01081040043d1008680501c100d11064013005054603001d1361604400000c46081c42d441c80026071000c2146c801c44010f0014000240140c0784080200c40c0f29945e402c82960a0710100031700d20307512031502c0010402940c003030342c2c1c0444030043c06644038aa40b407003824254108a900620601c111000011390740b02a209011004d00d001024289640c2880300325100c0089060b41280c0107503a954581c1f1f40f003844c1004460282c0314000141d944e4600d004d40318016541c010340910b00c680c10442c144010905901000d004480d84419034945403d2111500c00c1c2c1341d401c580c005003820 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61379688 1250 61378438 61378441
    0xa02090403020f0f0718091703070e0411070f1407180203040218160509060c1207020306150904030e010e100305010f0b0301080303070819230603010504031202130302030105 76
    0x1607004074084582280143c221800d00e07603691410340d507803800d0b403040c08079544582d503240c0c0000c09940c004480081c0110350090780101500c405412680c01110b44100094546041703118920b40740c020b410035081084030082c104000c0d030301c0789070925600c00c1c0d00030700e03104401c0702c40f40b40b2250922142c0002c104201005029000344041071002e5402210100e1003000c404110750081c6286035500c0e80906581e00c01b45800180045040d81d02d17601c0f031200903a21641c1441000c0f4042c03c108044a5401070510040d0740b6028248145454880c000d0304403501085400300c00c1d84152501805143d0054145c600090400302e0000180c5504a00c6406030f9000b2103400424802940c040e00818126403e29444010150381c1d00c0d0b0441040c0400c1c020004150130400101e10660701c03540b04140c101030324017000340b403400e035240d0f400b0b085a00180d030480c01145074070094940e00301a0a00968040030550080c440c5107020307036000f0290000c0d00781c40c2d00c0f410340c00300301e40f500240000b000d0b0000d03550280003041179 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61380938 1250 61379688 61379693
    0x109030c0603020711040e06150a05030717060601020307030c02040f060b160212010c0207140105040e04050606010206060d110103091410020d0e070f060f14040909020a080706120209030a020904 85
    0xf0303504c00712007511045d52148a490040c103052094001e54040ea4001e131481e9100e22806651240404800036800000d030351010441d03076020700c241c500401018080034404220200d00500345600180b055065400030300060021075007102006054030742c101c0e8001100800d051034080180328a40011154507030114200891942244c0e0345400c4a000b20350070003c0c006500ea48500360b500400f12040141c02a8100700882041c110641004d0101418143e0600780c0b24840b8680300700c8112000d5545034004000d0100d50358050020380d810400a0f505140c5c00e19160310745a02c03c58149000c1810141d580b00c2d0f45041c0850b4091500d55045540151040402041e94043c041d4126240740b00c072981c0b900031040403006001403d04102e548585498403940e10b808001d4a21004524000082c416a1030a40c255007182400400182c2003c3e074001a00c6900760041c4140004d0300c0d0445007840d4003900041c00000d8005460f0502c80e08044c0f00076981c0c42045004c241031004880c402508465020140000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61382188 1250 61380938 61380941
    0x40e07090b0705030a03061e0302040504020a05060307021c0f0f051605010e0a03030b09090604020114070605041a0f190f09171b0106180b010203070b04030e030f1c030b0109030c0603 80
    0x1140d005d642c0900905440c2c103040d2441c00124690625a0702440300d0800040c03c007030300b21a510600080140e9202e958400c04074220380e02c210350840051b00050305003140d07044081c4000701004010715142d80d903034002090140211920130b404600703000021982084241002240c4d140e01c562080013408050260304c0307401d43d10000c000f8100d010a0400c4940a441d0818102c0184190410f0005210036103481c3c00558803199000c50980d111b080800402001c00c0560040c20300841c0b0071712032005842e10440d9602400b441c083c0006103480c1c0e0301d00600103c150080da110880b01c030031031000a8004001c10b440d04c002d1641c2000188001178422000d17024440709409840007401c0d03211028041c81058826508880e89070260384240c440040100d8880500d07684030f01d10030401801103d06d40315203522420440c1004030780840002d007070100381340c40900f02840034094158040000b040d00401540d143c0da00025081541020103686821550640c0e1154040d80010358108056421054072510001c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61383438 1250 61382188 61382197
    0x230f030d03060f0e04080702190e0903090f011b0201110717010c0206060a15050d0908190f0201090c03020904020307030b07020a0620120c0d062706060203040e07090b070503 76
    0x20309070080c0c060006004013010380f0310348aa03500c089010b16241072075082181d80400807003000015207240402013228210406540e00401e00d200003546c0b55102c8500304242da0246480b0349040003182d88115456812044070b04409a50900b032003145d919440f00410304d01032082e4040c1d807500e140e95060b96880c50043d48015448a84c81d4207564482d5190014403088078000d00c9600d1842559003081c44a06200b0700203031004090149001c42c0303000310b03500c880f2200e402030200c07407541d1742c0040d08900c03000b904211843e81c41403090002b440024520f441d828903a16141c80b000c2d01440c0e80300c1c0002c1c1159014000303c406154804500013032400c0100e4000d503600042d0000700d84051901a4400f06a04075040d80c90a46c1c01e0140c40a00c0d005503400744001000d00984aa0500310701402002aa02114010f1a0180221107000d01e81c0500840401541c6001e00300741c070b080285400810300038694080110381c1541c11540d10031583d178442803411a004030306039200c50f6a610002c2454002c0090110041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61384688 1250 61383438 61383449
    0x16080915070203030708090103090f0516090b0604030b1e0112050f011b0c0309030204060b12010f0b04050603090f0601030f0302061e0601030e0102070213020c06090106230f030d0306 80
    0x105035142159030104803620030310001a40c1030340284944400a48504018441a001031501141d00c08159569140b00f000c1c41e40704a07800e412010b10082001880b60920004050905052110b4411040400c043d880b5600024007000000d0000404420400121034424040c84000d02200c1d0b0391260395840d91880d1540880d040e0044801240b0f51180500075001c0c060030400c2c1d41405041301c2c00050340c0f0307801c2c40c08d01242440701081001025031344030710a820040c2074050203a5a036045c0815000d040400503000030001d03030050716040c007486800c0019102903a13002c2c0e4803140c3c0c2e0b44172100100c0c94060b44c02d030070020364401c0800100c20445000000c04c0c010b4440c0d02200d04580328001401c00000032071400c0d02c20040c000b00000d605612030b400590a400300100018070307200454006ca500d260442254208454001441c2ea629940030002c0c03c0d40038440c5402049650b0820208411000001340d201c0783c5483c11115080e83d035071314001c1c480c460302401012925460307401000070f030191807d8401c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61385938 1250 61384688 61384699
    0xc0a0e0a0f030b270d0806120111030702010c030213140a03060e0307030f02032b060f08160f08100f0f02070b060a05040b150a09050a0f08010b1c02120102160809 71
    0x1101c03160860010141100104413000c0c064519003080101c40d05540105901c0d07101c110013440c03d881e56000c1c455081a0f0010413178242c0c0d246060203000c2e003540d50303007080041010b104210821403100010b210a080e80c20f07000d00c1d0001c070300b040400203000480a0300040e051b2803a020702c01c50354400000003402424401d40382c100903003107000010703a22409225100048141506110ba450404041520380c801c0b100d00030000e905034540051413842c2450f5040110300f58044025a41c104001d07401d07a0008100340f00581030f00a051810701521216601d01c502d03001070719000d842d2552402e6400c200b10640d00507804540328481c0707080c207040002042d1a590301038012800d021540c1c1c245402070b001a8175028000409038604110300781c45941c000806001001100040030400d41d171100711580082c41c0c1071409240e240d040003182e608450641010034440e0f401d04020306102200b1410344042d09404580d0818080744050f41240684640c0100384022100701b50141c080000c0c0030054500c4880540f203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61387188 1250 61385938 61385971
    0x90c06030e01050c040509040605041401020d0603150e030a0f050913090605060405010f0e190507020708011b200106211407031e050c0303040308040305010b090c0a0e0a0f030b 77
    0x740b01c1341e1403103035004041c0c000c081e00c00003c01003040f0340c00c80da03082445038801482209d07800c0740300750880c0c128a0a0140b060740f00c010070810b201e6961001c00542e91880c004000100c003448070150380f84211000d203000c0c0072082c4d200840a0b0b0251090707074150070019080c0440200600c00800c000d00c0e490004645031860400030803d1810640300341070603134080c10004694903040c00100e03050080001d0030302c01109007485010b07030198814094203001c0c00540d0003d004a500b403d80c1142944c072516202d0080040c2400b00c10300d0075520502240c0000e41e4001e0420800401c1c1c502d15002d001641c009180c3c298017480703282c01c10b0004811411255001e022120040700384850869240d041c1480058440416502d0b079074043c4066401e0695450304c9103086401008a410120341507400c250300030394201c0004503040003442406e010f20820b110003180c8065813464401100c01803400f803411540e0400a000880c0e080a03101d400d03a0300040d014910040795503540c0e0b85486000080c048a540400f0340c074400707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61388438 1250 61387188 61387201
    0xa050a0603150f0f021b1009020a0b0f070b090d030608070b030c030c07050604110a080a0308010308030a15030c030302010e031305150d0905010504020f030312011503090c06030e0105 80
    0x30508040c0e0340c1c0b0402000360b06007000e82000103000c28004650016550307a220440c91a241d1005000500e05844c65011900548030210308040b520b041c282602403e03d9507640040c4c0d503230540c2c0c00c191560080d469865040c850780c0c1e04810302903c00e0080c000c1c1d10796000c1c8041c0c00320008000c209820503907400d100030381c3c540c41160b0316852a48200e6012260a202280760f0b80f16172405598000c40035010903042900c180c031000d00d0410162070955804801915840c1581030000003440505940c100404000709560b90081000700d0510018081c48008000704d1140c40a54000c600a00e1810340c00e0101d60b900da080c00803040c9041d110440166280036000003100401006031062180181c3c046403806140000780302c60b10861141c138501c0c5660402c1181081d14161089101d6140510f000140300c3c42c144c414009a403116101c0c4600c00c1c1c2c0b0030311030001d0045500580034199801200100e2107e4081d140a5003d041c1802c0018540340c0401170110300c003940340d4020b10519180d0740c000c0c825521090b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61389688 1250 61388438 61388441
    0x30607180b0a11120307031b08060d02010207090e0c100813170702040203010e09010c02010b130e0f06130b06060a140702010e09160908010209060313080906120a050a 73
    0x290a0340350111924804010240d9158068000d01d05207080800b00c2441003888541004195001c01d41400b0300070040c0142c03954076108094a0701584980c1d082184025440030f0550a00200703000d1044d140013240700c0440e4400e110b15001418010780901402e07249011141c0c8902c16000d0241c050a0980030303204034180b2850840b03000720050758003544103100ca0b8450700d4400d00380385d44071920030501700300c2e000c016212840290300902e503900014041c0e082c011051401d5504130390b50802103a0600d901340c040795403064a01c542c103915441000401005606a00381001c000c22254401401124204842a880904c0803929030b8820f2001c00d40d5680c03104d0400101c0d004a0b58800001182641c030903d60300224002001802c0c0141032102c2c103980101c0015140340403c1350380c1c84500b02404119000e6940051009000d0007200d00258149590328010508a00004080c5440c80010030259410b00c003406040365501c0c0000743c0380994030f06020060140300602a680340000c90310f400009408034545 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61390938 1250 61389688 61389707
    0x30b030c01080c030916090903020c0405070509010c0c0f030809030f0703030f08071205090d0f0806240403082d070302060c0309030c01060906050a2103080a0905030c070302030607 79
    0x140c46400e043d4440c02005906900001c043d0100c03072080a851200b19041c00001100500a4079404116040039240007401d1140d204c440b140110300f010144908960801c055500d10382d020300c0c021499031030908204520324071560014403136860800000c014085104000d1003265015411110180303081c00c405503588540f407001800007483d44110421152084a915820000c10314001070f04030030041d6034804490003503521064590111044040a580060f00103000c07501d01e080c020f0322840c050380450380f114410303419606529440c2100580c0540b9080c1942c014641000302140c940c405201410501010a101b0329201141c03903100044c040326150498440c19819800303001c854403907070410220b070341010b41307500b885000602010480c88800d1150800900a0b0b500214000e4030740400d020700700c2041d070007088a10240c1020081a98074001c0328111851b81071905840c5aa64400d5020080c0101d80300244680000103854525950000d50001983e0084041c0c40e00358691200660310300f80c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61392188 1250 61390938 61390963
    0x30905121c030e0607080a05090c06040302040f060b030c0c070b0415030504111302040f080d2c1309030f030b0d0b0c07080403032304050d0605071101020c01020a030b03 74
    0x1000c1001003240240040c1c449140c0682070115803400407045031800d00c0c030126000380c0017515010800001400fa030145e02e400000890180c1031145100e00031944a10540c00043e00658651160005291040d03011400804400070515140d0810400c0c3e0301c00e5034011100e05456204103840030036020074990860b01114039045900409141c001c200b03030b0241400038016a10780c040c1c4000b2003c552180d0b107400f1590a0041001661142040d00c0c4894100081c2c000400e41d902ca5081c41c0d034055008000c00e445007840301c510178403148c00702e17034240e0040d200012003035080384031f550320313142804059004903480d14429201e005900703900b058200c08869502404950004040d403041d0040b691550500c1e8214082d084814a82141c9844103046540f10354012400a401050401a10316070b441c040318200c407680c2c094501d0649000c000411115240e14080c1c0601c2d511408900d8040c01011103111a0260800035904c80986005150003500450001c01c082414660350420b1032a021410425109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61393438 1250 61392188 61392193
    0xe011b1e0803100611070b04030b0a0b030f0c03011b020a152c0105070c0b130224120114090a0b01030e0a12030b060c03030f130602070c0312081918020411030403090512 74
    0x2031441e11101d4162b04060f10381801590ba400183d800ca450500900c0d10840f0f0010040240d8561a8249401c5031111800d0950046c40490780d00e4642d607010400700d031903a400030b040c1200507411007108402001c22214244092044425105400003600c0300300400000000081209982e50b280540740f8071099280201080b52181c0000d0326244c94180b05008540054030690104144468840b00801003131100e020780340b4049a80d100c03901c802041030707000d007143c12071980782c1e0590301c3d011448044001e007562101c5501c910210809034420303032046d414241400e00301c1c0c1402c0f149041c003584078203d80c10fa80c1c0000e8101080d400c0d003810804c3c100c800032041240150f2450792103940381c898410340900203980303242c0500e40d500701103070290014050250041800064003403461602000000503140c0400a002410742000303540c010b0380024600c05254080e0220310100c01101c050b0300c050300c2440c02540280740408542c00410b0020195110394441e80340c10760f8580c1c07604100101c4480040c802e4070b1a6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61394688 1250 61393438 61393447
    0x809011a0118090513020301050c0c0a060b040b090406050a0f02040b09090a06050d06060609060c0b07030b03030c010c02060613060b030121080a02030306010e011b1e0803100611070b 80
    0x254400c10007518496034200c104040d8940f6450f0000540350259500c01e0700b860407041e00010762800703105a41d04002e004201b41d185c541040582d6455058500024001543d203100098079901c5940010182220007012403101e441c0511b0300c0c0c4000c007000c0d940e80700c14500d000d9108004414901c03c44e41501d1042420030b0900c01103000700084803200411249110340c44001c00074003030f1108040024a14407518000c034115003000001400c1c0c00d1194044810002c03030001c0c05010580f11280c498218100d89400720b450700120010a2442c401e40c807024055619020440c0d041340d60101740705020f070700102c81d0070710308440d806900e8007951106c0c0203070100303e0000c000403c26004104011840d00555151400c002d0000303031214092904902d501c10302580000041014642e4020020070400e8002d0801c1c004810103a00004903154080d04000e0500303034058503030f6240b55192080400c019600400c82a40c91403d4401073340201c045100f9407011807020962814808800704000c4143c0d400003040a041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61395938 1250 61394688 61394741
    0x507060906060f080a15050403050405061308060709030b060d0308011512020a03060306050a05090601121b060e0901060503010e150d150b0a080604121421010303080901 74
    0x6103403100d4112907003a511400010790101181c456001001280003410300ca0328282400c50f8031004514140700a00d00d0700d010000026001803c2c0d070300790b4505540003500d0355940c0045800200d850342000080b4400c000801040d29030003000001600d1050041103255162402030102c0d07070f0320a0788001c02080c8000e00502c80402c103800c001401c20110314000342048203451501c0226884010882e0000b522500d0600a02415000361031f000000003104101a01d00b49843c6502e0388018000c214042110781608400e1010a030103459400c090701c0d042e504001da440314003800c2c4515102c8100d010328045070000840b41d004a0650b8100c03100f51458104903902c0e40040c0308120308072440c40307a10940d40599800402d0b40e04001c1c121030400310300d00080e218107420410014010310760002a65074070200c10800001c2d00c0e000280d00caa051810120f03001c10100c5600d0300c141c000e10205c00181104403240c1c0755140f00f01492581207900a4984203e40e859040703045003a80c00e1309801c1e0355400710300e102d8200d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61397188 1250 61395938 61395941
    0xf0906010f090b04030c0f060c030f05090f1504050906060313030327030905030f0a02031c030b0603070203091003021611041d01050402131506080405070e070206070201150501050706 80
    0x20500039403502d0b040c0681c444607102c0440c1c02075003040d140c10b4401d1000340301411080050300090031380c40c10898503404056800400b4007103003210910400401080c100315903145ca10002c0e8200b500205002800803401c9994620b58005104440c03041040501250007410300307000322070080a82d40a1151150020b44041e0060300204001c0001816100c02c030b58003107410180340940300d038400c0ea075589040f49848209840c081c02480340000540100e20150016a80000d24008400644580c42c2e03161000400c20b900904c0340c2820290011800420400c0305607011008203030701c2c241240c10107076042c1d5200007203049000320000b042658000c0380660001c20302c20320900c2030700f0100400c0031407139651903480001b9040704086080300c140c0d142d10a004c00c5180c02040d842c244108030b002007060f23400c006244d4070358503182c1c031445090040040203e400e0040a00000024203201e1030001181d080125000b59581000c40e4990015403038990041c956040c0808440201c6105a440d1381c03c014481d118a070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61398438 1250 61397188 61397207
    0xc0f010b041a0a1a0d0216050c01080123030304050a0b0301030317040209040201030b030c04020406020706020705101403090106120809040f050408030c0f07300806010914040b0a030803150f090601 86
    0x11025006000d0b0440c09034090001705407988442001e20003103882488d049140018200754681070040200040c05182c20b240c0c40a400d5500c04441000d95504410201e82148181d400c4250480380d017540110351411104001c504032071190340d5220842e407034501400031502095030b002354080c00540100303015600c03940015002442c0201a609940681c1c0c1c0041c049a00c1680803001503080760204000e02901404100d0007060103803001c400c040c080c201d000340a090f00314446803a4400100c00b040000740309601c910702078500d058802c80390310f510782056840c54100c0642c043c40b440c1044030070314003c0c0d014001c6900603580b10500c0c40c00d40d20340c80da030380e44190000f10607007840120034414000800d111000c0c00c4000c0d1821300c041a0000701145100c15180700d00b2000d00c0034404400240328540c0d901030400c00850b1109002404090311540000e0040c210400000c2c2d80300601000200a1107601002940555001600d101002174141c0c10301018045521215034001850380c00034469500071b08205 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61399688 1250 61398438 61398479
    0xf0f0c24080a1d07060e01020a0210080702030705030408151609090c03110d05010806060a030b040b0403050408010c0807030b0a0506030f10030b040602070c05040e19030201020c0f010b041a0a 84
    0x100b22420b40c1c18041c01d0360303e060300b9401020380c401401040400d40011002035000c800b0b00c00341c081011a60003003000050b902e41e1044c20005958009001c161007401900c4010b5401029243e4503940c0300c0d134007981d071140c80c07040001500032a00402c088140800703400c02c94061580320304428900d0301c80103000501c0c0c1c0600c04c900b4940c0f940303204100c0006807030041840c158902d20008455061401c01c61802e0f1000f0156030140050701d605201007030446049a9106a115481088039901d6103400c540500465004030350544c02c11003112140e5402caa80725111304540e5500f00820072468040010b000d030544a4590001800c0000c01d03859100c4911300c9900500210646000725a41d135202c0510040071102951b90f140e0200d200410480c4079074686004000c200c80a200010348034400684030303000c02165000c0c40f05030400f0a01018000c0d0103803603001c1550010b03030386180c8014170f613140603200b403510b100d00c1036181c10040c2001411148040b4400400030342103440150030324001418803030700c0b01400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61400938 1250 61399688 61399691
    0x80c120a051f0801090c050a0302030a06020a2006041103011b05070f020607300e010302070312051602010624050705010b09040f0b0a060501051606090f0f0c24080a 72
    0xc80c0c41d002c070300b10010401041040000107602d0440d00340520540c0c000d030403003880344030580c4041000d60360000e4028a4540c00660060b5551195841030314004444c0180505d0300300b03903841c101ca01070380114620b8443da000b424150001301c0740008140c00c07200d4a100340380f001d20320394003030055991143c400742c40543d100e1b1480000c031245540001b41540c000d142c00710340d414250302200701c1c0e01c8044601d01c0140d00b14000340d06800d40004002030018081c41d0783c1c4038101a07010550be414148106000801350000d01d904005504180e5040500316100203003000240d030030140d0018510b2400050b40d6016501c42102140e00324004c036003120180e0000d00d003520551b40391a60080340f540c824110b103000e60300c42c00d001003c840307061070000f44400e001441040d2072454090100b203d030342c00c101190f5000807400105c03000c0360864900328000740349000303014048031280d46401003040012214006c5060082a02c28603040d174543c02d24510104130180140c58151110410444501070100c0076041007401c0360 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61402188 1250 61400938 61400971
    0xe0d141803070e1006020f0a0c0308030a09060c030e1e0c06030402010909050c0a03061203020a1106160b040b100b040b071104020d060509060303041d060d020904060b01080c120a05 79
    0x94288405800d40742c4000e54103080c2d00800c605c2e03030104a4200c030400d068000e0318040f0000d03100c20703800b40e03840d11000c0d00f69400000042c4008045a2041c2c02c4154003c0b03003000090302e8100010000d0216400d581120310584203504101a00d1407600850b070000b0780300900c48442d01c07030300380502904040d104074148020114042024040d60044900c568400107000345c51300d4020400400f5105240e01540200e4008000f0034007007940480e400c08a1508000035000809030a008601c00b48200f101d80200c640da581003001c100304c1c01e0b0f01403e02850003410244100d4807054000b01b1401e6240c8200c0f42da0b144200420041400c002002d418501d000752805007407401482c0c08541039a003c0140011002e0713403004c0501403890a0410213800c841c00354003c60400d421300d04a01f0008881556940f028000340c40000d0341d580d50240c05a0103194040c01c074a00c0c0f402c2c180b034190003804211501c1d80c00308072190000f404100c0d801082d9036806102c2c540c604015103030011a107004000c007901551250a03000f2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61403438 1250 61402188 61402199
    0x90c0c0b012d0303080615040803070b1014030607030b0a051f030e0105010b0a0c0602071205040e011a03060907030e0d18050d0f080a020c0d060e0d14180307 69
    0x466600070000b9680c4500d03540b01e00005034010b81c01041082c52404a07425050010a03480002140d1026040e0348001c8040800f03003900d951805140e001c52510b1000182003410000c14507035242c0a498911807440003d900d50312640f40900421140e01e0b0503612100c00a08203610907013180601600240c4009a1075403a6008114048500101c0158030b4801000c500411170b0301d480b85000c03500720100200801d50601c4400c1000d4445c08a0307500070004003003040002d004c40c582c11030398003a034002ca5885d4040c09642d000b9000390001c5c8500070401c5003050002445404e8a4030f480b840c031012840c42d900d0b556425003000350006025086400f01540c0b82100001d4180400c2503100b1090180c85560b40100b10402c001408519500f016016080c480081c000152403c080e10015030350041c0c81d82d49600c0d50800c1285020311001c5420390200005103da024801141d1052260031545000d842d4141d0a1010540b030b541011203131400000f0040003c003046c01c031046000a40c8001c01010788801940d9034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61404688 1250 61403438 61403453
    0x50a1d0a030303050106020d1829181212070602030a0207050f0c0a050d15110d060612050606030f0c09120307080301050102060115270513140a0b0a090c0c 68
    0x141c10840110781d440c001440340e00d40410030002e0b1000e0b6890b08180c482041400000c8000040c4a0220f00741d00140c2c08107994041c1010080002c000c00b041d094071a404120000e582c5d10000501e580100e03117503032144100c00740204a1009100c0c00001642c5004141d607245402544002c102c98091a0f0900555002034814482d00c95401841802450f650354101c1c1040070001c0543d0000d0f1140001200c0f180004010060a440c20301e80010001003108111014110f41d2080504800c1610726202e07002c252303103420004440340fa0b50005410461707951600b050204912050710701c0c0f01c070108164009036480d8010781c0182222040030708015400d4070f10710721880c0303140c100384000c450b5443c0100050115581c1003141c18010040ca51900f250811a00c40141c61548041d0001b0820b03001c00020b02142400e0111000c010701c2d01610000351007000d100044003c0c242d45908041c030b001e42402042c00e0b030805003e06e6400010080c51852031034a010554402810402001400d03c50050724010100e00c030f8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61405938 1250 61404688 61404709
    0xe0403090603063003022503050d05030c030a090213021612050f0706050403090f06030c110f0d0e030a08040b0307020601080307081603020703050d120f0c050a1d 71
    0xe40300d040036242050300c0074090710020742207a40d6070f054140d0006001c091181112100f80c00e202c1348200d00c404c0b0303400c00701e040040b1080040c1c4001130b03880c41016600031030110001128003a500361a1580c2861034100d52510042c3c60342d04070090140b0200e8104019035100110384ca2004100390b00847c0010900d200781c0c1c02682c0c0042e5014400b50402d01803010300c004110030401b15140252810400c08032007000340c080c805010f4012952000090100f501580e0b8000183c803641c080c0669580d52403500402408481c89680f0000f400881c01d408645800030f4081500c00000026110f0403400b244111602d44405010781e03032521620444c04046041c02004002130072014003110340c1c83c64079420281c5002e0701a40105074542c4104540c00c0410a060709852180c03a9264981040315814101246071950303030740010342107005907242c0564403030b084440a0b1000d0b0000d141440254000e2400c0e02c101c0d2000145100400c0b820460314100921451860801c40c2100701c144160000110105031b1030700b030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61407188 1250 61405938 61405943
    0x3180d030b0307080102030402032518090515010303050a05070606120c050a08070b190e030f03040f0602030309030711060f0a021f02030907030b0601020c060c15090a0506011404060e04 81
    0x352145051810b040510042d07018200d410020b518600706a404a9540c491041c25003e0051180c0b400800c40900d054070b20707008041c0f082c500f02c3d00480c00080d103001082e002d281250103200324455001132400c01000035040b01d400d40c840340c1c10441d403002c1c00c0c4d455a012005c110b840c140c1e038200105802e03104004500ac5603010b030100303221a500f4030080c80180b0309540c000d0b008a82c0145010084c41161100b2103c9030038540e141c1d8084c810035842d0550381740c5124882143c0c940a90030203142601d0000000c5c10458003000144005580d4401042c1e80f24030054800b825181c1040004034045824840c5804030103c2c0601043c1c9014003400140609800820301100141c02c02c5d40000d442c0340c881c114210030170300703048002c5103103040010040c1c1c2d40718501d21009080b24400000030305240e00912840030400b02c0071784501d0f0345140054416480b4901d0516625603c031101e400700d651020001420b070000d6a100e0000c04c0d0f26424406803500201c18452031581c40b03038842d00b012070309a0492440b45d010780c0c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61408438 1250 61407188 61407191
    0xa020c011805120c0c060a170f0405010b04020f03130f02180403030614010c060b19030501050108060106020606090103030311040302040204090f050a180f0212011e05090106061403180d03 82
    0x140703032400394100a6440034480b0100400d1100d010480c0001c02e040d0202c0c0d41c1180c61513500d2561003000e450880e003807961003c00d980302d102005040c10300d404007144594440e400070002404c44008010480c00b8000c01d9181100302480002c1507503170741c0c05000100c140102d550b2284510142c1c00140d2422440d4104c031060a04078003800205501750043c0e1000e00903201c01080c503100c045000800010340c03444054985a140c20110f21252034880044d800041c03c16101c6210640724100240600000c0c07085030f100d44101c4000140c0d6a20114000307005110007404122144d10390b0310214003400711403d0303400226108010000059945100420081464110100300c984ca80d4000034101c80c401400103841d5820080c1d000b00d40704124520a5045038022802c140e284841d00202e036124503040c100180a40ca0045c90780501260b51100400c00002e8000500042d50b8618a032403d0f41c01c1c0744a03c030042002d045050402201c9000074661240c1c0c064054a9560342a016a62900912480560100703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61409688 1250 61408438 61408481
    0x3060e01092f01090e07080403090e0108070305160f23061c050f0601080106050c010603050a0602040e13020d0305071a070f090e1005010c0201020313030303150e06010801030b0a020c01 81
    0x20b10340000c000008074400d08140040b1484e10101e4842030200421130803c001d0a01e000070b0403d405600c450018280b4001c00c2c3c0015a120001c0d03565030700c0e150205581e10b01c581c0c115090300030713a007103400c0058500114828007910b15240c10a042034078080c607010301502c84804080000e0721030601900d4401c24180080e0a00780680b45000c04840c00034000702802c4c80039508101c039a0360040d0385141142c03418a4900d07507800261024038014001a08014002d00030141083c091007125000f03041a106198488400c0d43c481d40c100c1801c0c0301b141007000307400c0782c00e50b80010040390080003c0c00025008000d600c3c500c41c104408248081320072518003000c181e80c1c0c4d613550310b1198080140d0340030f0848007030107900e141000c10340d00727400c6c940d0392040c1d0341006240143e02e01103920034010307510303118020010700036030725140d14019002d402c8040720030100303006010002030340030a013030045800341c201a11010000d0f42991545140400001d01c101520381c1c00b0400600c07254401d10450160708940c001809c801d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61410938 1250 61409688 61409753
    0x20d05030f2b0b03060601080603011503120311030103030c02060306040605122b0504050405150901030b0601120b09060103050c0f070503250b0718090c051305091003060e0109 77
    0x442151141401c10285400c0450f0040d8070005038143d0028005d080140f09580c4c3c14001a0143c070320300b120003201c1540c91100000704207405070314072481701c41d946060101c1918040410313007601003444043c1c0002c41a07805035001d410328034002c60700081c000e4030219929031180007260b00340c0d00d654090704c42548070b142c45d42013078608003000c54810f0603903400d03010135007040e4600100107000e18001c0e14803071a40c1d0341c04a68280030700b030041e0b40c6014002c1e01c1088a036940e41884120300100f12007050100d103255040c0002145140714050340400c00510f4885561941e4004500404009003410004182080103100f603442c1c000c041c01c0004d01c04e070011940c80b2052001841b4000c098143d0b16a454451403035540000c41d03410360550300198a00d00031040d400d0300b220a2001c00d01540c01400628541095a0704680d481030003070540c0f442c0c3c404c0b900c1032147c1d0780050240c02041202c500301404c408c0c000a0001031001c1d009200021810400400e01c0011516243d92803006410022b11685016821110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61412188 1250 61410938 61410997
    0x417030118050c21091c12051b0712020a0507080325050a02090a0f23070f08060114070c0621090302060f040f05161a0412020d05030f 59
    0x28008050080542080d404c24003400d480094400030200c41c07140c00b070004202820401000802c050100050102d0655442000d800c0c03d10360800d0b01c550070305020000709c8503c500141203c1801100741c41e2450490640c482407a4071a11085031f02c00c42c0504a40c84000c100100002c001801880c0061551800c80c968080c1100c00003031880b50404c00643c00303083c046440800c1302d681081e0103503400501c50b50307131116020050032804004c0c41c0b01031402d10405014150302c4008110b0641e010607102861f180c486c02500d8902d00070440b0400110f5800c00540603500c42c41d101010448680540f50800c404c42d03a51210011075604a0b400007400b481c6101039030041008140405038900f2000c001045040d10300949800c401001c9000300d206040108080129412222990350307000015070704114071407006000103d02d0f61003181e0001d1a040400c0348441c034581c04590854042100001690365140d0030310441c541a95015166404144043c1c400b45007200d00030544411134140034010610051054003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61413438 1250 61412188 61412191
    0xd050a020c01030510031e14010b090106020303060d120c050624010908100216050303090105090c04020a020a110102030c031b0106241409120102090a060807090b03041703011805 78
    0x1410141401c0c11712240b8524843c20000396900108481d910840840f44a28400c2d075180004094243d10140b1104a0718190701000321044c04540003080ca07641c40e442203a0305d02060755082d40c40105002d8103000203240a045800100e080d041c02e800c80e415648a241c10302c1e80884d464040d00d03400f051901c000b9000729411015040e424200b900b000c034205000d2981c0d90031b0005940d00000d900240d407581140c49500211045a401021242d40340b03000002640640f03000d03100c240d503d10904034042032600d05402a501c10100c40c2d8001c1440f000c2503107e0454820482d0754141c10360204004800085000340010700040049403154000640405086402c480e9968130200000490840704e0350072400c0c6510403c034100307461800702043d400420951090b840742c1c0d90444d0380719180d441030380c0303013940706401030015503c00701c5183c0da00680e103100544907520101e9080001502c207070024081d03454910051234025008240b290503409011283c0000d5600a8104820741e420aa6000c00882410700a25 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61414688 1250 61413438 61413463
    0x8030f0601050703050a0e010201150b0c0714030d0e0411070f1a010b0d0203271006080303010501080f09010e06040c0312090b030c07030e0306040b040b0c070f030e01110d050a02 78
    0x50303e41505614020801d0191021440420102d20b115200c540c1c401d40002900d01c1c0341441c007c2c0715698800c4540040d0b4000401183c55016001001481d9105d404031845020f80260182c0064400c44008580c8003034a194003036801903a9000709503482030348202400c01c481c410f403000405103465003001d000583c0407160f4600c5160403000140898001e01007a0b4030352000381d03400540c81c0e448901c441c815911035800441802c0384c860040d40303900080011003011103d02a803081060f1074550001c10b03141e02c02409a58082104440803c0040290590349a44100f2610000868122000409061000a407015140c1e0300007510240284400c1c1c404440c000e101508100400500d00715800850f400018024000d481c40411500249406020000c0c2d48240040544041d494149450080000c06075820f940307000d8400002a440140a4212840c450300040139100303154441d902200c0302100b03400070318100b11801c100020020342c20042c0794644031954854544511034508000d00c1d013a10203411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61415938 1250 61414688 61414697
    0x2040e1501143405010c09050a050402090904020105250f170307080f07020f0708010603030f1b1b2601050709030f170f0301060201090b010501030c05090405060a09020708030f0601 79
    0x9200383c040c1c4000c20841c0480074400e100321440c6405260070000ca03981d00c09009542010072040109500941d140192801140c0c4410362a42312400d00049004400e0b54a80041007800410301541c0070f403000c0c00c42855140b01c0c04100d000d40c052080b0820801a0007280c0540c0c58401c050100821040c00301c005052820185046203007000c1c0041040d08040c00e0142140030380fa001c19800e510034490005c81c04031034411140d40c540e403903d01c00e00900540c441507001594446401d000c080c440c0d840c2d1455540d080c25008090b142c1070f124020303809441c11204840140e02100003401c9081054618291250580000356003000c8100550a4443c002e00a500700400c2c0502840001e0540c8101c2031020303040315040c41c0c0c190070101181d10b00d202d01e0131140d900b140040000103095074150000c03900c29124103481040c0742d030f23203600560039904404041c05c003048050085d0030707182c2815131203d03900220043c01003070000e40c0d8580442c200d80c00b400d020b440c110000130400c1000c210389400c60390409001c3ca030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61417188 1250 61415938 61415947
    0x307121b05010c02030c0d02060c0706110706050a020304090b0303040909080912070f0b0904020909010b042c0718031b05090c03040b04030c0c1a0c1b10050a0302040e150114 76
    0x7030b40741c40006e02100c0c451b11212003640b0541d2036140036100e000c0c002c001101c0700b4075140d10004d8800400402c40c4a02d034840c803e004140c1078031402c145e901044554005604007401c0c05601c0c00074024040409030075100510001031525002d000e00490310b1700960300750750b80e01c1300c09040c05802040d0310311401c484e46c400e078020080d1310038038100082150661000d064880700480e001a0192161804a50340032010000219410558400600c2110b0703510310900c071034024800703c4800d03080308149914070581c42e54001901d254014454050303011110042c3e050f102c0c1d140c0d03950400b41108100f00c0500441c91401c10300c21411710859007500111900150f904519041d65140303407240d8020001401c000780120a01c0170082d0060482d00642547d80409001c00c1040c1e074441441e40000c0c2c503079030a600c01e5486002c880041020710b4041910094520b22203003200e8003041d0f880d9400b650340c0c1401c043d420030000500d1701e5415900c034001c2c40c602300c2c076060166130380d000100250682001091110007c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61418438 1250 61417188 61417193
    0x1020f040e190c0e1c02010e130209030d080603150105090105010f0203120a0e120c03030c1e04060507060b0f030a0b190e010f0c0f0816050f0307080108011a011403060307121b05010c 80
    0xf98503007840c9011210161031140130070300e09c0040d00641c4d6407103030580700c2c8500c074980700c50b0082c5c1c03001e12511058045444006c1183c0300c802c00e5107420f200300f0350042071100c0180420b510591107451030114600443e40307400c2c1e0f02002030700d24072011104c10440e65a16950740b076540f00284503221000c110200380e0f80c00d00317148080450305d074440500050000c00c8005034940240500855031800c025094007140d4031190740d098050314a600c00c0300102c8015103450058042031500034444035000c0300103001403840c98260380c2d0f00c42c01e40801030085614a10300210742848847e0b80d004081c007003110f4000200e00504090085002d948441d00ea010a10203661000c200c3c4d103500c403100329803101201301d403409200700408007035a451140307191a21200000004120f601508044e040e0b04940e9504003c11400d100c60300400d0900080050b0b035800919034000e1602e034401c2c44000746410440040c290f4200903911500410b0a001800003110524a01c0040034050f5000030b4510f002480c0a09081c051140b25a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61419688 1250 61418438 61418447
    0x6070e0a09020708040e040507170106030318080c010305040519032001020306010f05070305091c0507050604080a0605060a0e10140f060f070f1401020c01050901020f040e190c0e1c0201 81
    0x1402146010304521000402340300701082a0402002032581008a0340e4075000b0860191845000c01c4c0c02041150030b0383d076001c480b285056021550904061720102070440c004402620005d402500e0234401e220b4000161801d407100703d82101c0c800c0d102d1080c540410265099130741d29102480d880e50b4070500802203a40d800c0103440024480310310700150745a8041c80c05a5403401000502c580241c0b080c43c1c1918084101c05a01e0031080c052001c40d1400c50b07545007000b600e03220b54020b8414903042800d415001030313526004540c0156005140101460711140410480d900481d4021004c3c00c0c3c00104016514402182e11403002003600c0300c1070315540c55400705d002c6110700e8407801d00010700001c0d10801c0c0f003440b0181414041e070000d8100c284582c01150707039000c0e402c2100000341c176510f0030f0080b4805c0d0205100f21030340610420360041c101032030729001000f0b03480014104084140a2004142e1950030303031062240d84500342d00d4035250310b2248024804c0d100c0303c0700e508291103800c500440340540e810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61420938 1250 61419688 61419697
    0x504030c030818010212040218060f1905040216030906030c02210904090602040f1d040b06030f030705070603050603030c1507020a0f0609050c01080f070503070e0306070e0a09020708 80
    0x40c10810150384601e449841100d102103e920700f25440820100d05145403400c401c1e00a90007210405040c0141c1e080c0800400c2d8180c9407594800e201088500850814002070300d160913140c040d44078555611400709007039074400f05403140c2440416103004109504510b01c14064601884c0030410392035100000303592940ca02c18140361700040605500144880300003141e650030005803051044840070b01c0c05801170f40050040c0c0a143d41c0c070b40d40200d030000f5440c1910101e203403a8032411640340c546031200010450301820840d054003400d207501113101001c0005150151184000780707025403070204014100d40000d0820340c0b19810401a240c074045000408a1501040e10803070348a68550b000203a20f06180c4040c010b00c0c801c80385013a04244030540d80f10604141c022402d48081c1d118070001182e910340d084605410005865011030103043c0304c0c001031640102103040440c1582c60301c9000910f031200856807a00081d040b201840a142004541c01c0f004104081c015810b10245a4514045004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61422188 1250 61420938 61420943
    0x30b06010813110114070609030f1d06030103020d0501060e071101060e0f04060506040b030d02030c060106050c07033c060e120904051906060f090506091c0c0302150705100504030c 79
    0x284004090080c0c04c600e004c446c481e42e4410001c001e03421035841c02405450340c1c04e10101c081041d80c5240c1c001038603501041c40246000820581c5140c3c250b03802c0002001400c40d0a4800b03660341c884c01720b00412000d00369801170810f5150030b00960f41c81c1d10224250b9016400c40707000c0250380014044880101c440c80c0385c1290b031000300032403550b03181808a0001d100710b516480c2c0c0740c07250b01101c0e40e0700b40c1c000c4002c0c107885031841c00380d894a0ba2034900543d218800d029240345950302c803810802c08114890210140e01d8020010301024000480c1103004890004c80292107801646032148100300780c0f40b02d02d0016030459030241ca02041141c11100641c028985414011510780c000201d41501b04074544084042040007046400d07141c07440101820201c00d07501d00421708805000c80c0c00d103480000d032107a90070700400c0c0301107007620642c196110980d0444200e8040025400c0840143d81e0004003c40804d80300d00b1280e29144281442458012111000c01c50a0b02d0001403001103a4818040c031059074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61423438 1250 61422188 61422197
    0x3080c100605060a0e330d060909030912030912060212060901140609040902030f0105010e10032003031c050613061203050901020313060206010515210619030b060108131101 76
    0x308020600035001070a0500012815441284140e84486c0e003c06080c00900b0032801b0480207448045d500211841000050040b61211004112009a4809160380e551180c42d1004426640c1c00d0141907003010034800303c82040e00481e44070000c0700d1101e54181d0241003100c40d04c00c95454140d000e00540000071416019000000d0003070842c1d00e03180c0044034078560103400c071a5182981e004041c020700007030040d210308070411070118040c0300341c12840ca403d0b644c00002043c000301041d810305000c440e0326504150940010300001024100b00c00c401e0319445080c0d03001181d90300e8200b041080d1030348118510051645400b1060141c26600d44440421540c9030400c03030303a1525003030010b0349180510103200310030141089000c00c00e19404100380b412a102038030172030b031032407a1040010110b00030b07800d04045200e41401d1002d00c0d8006d000743c1ca40c004001405440242d10701902490540405030026540004e108080c80f00079640b03e2030b03013944401a0ba404009c840e145503558800143c05100560410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61424688 1250 61423438 61423459
    0x111c021305060f1305010c05100203130213140702010e0a1704030c0f060806010507110d0c08010c0806030c031504060207030302040506030103030e01020d030c0f0c06020403080c100605060a0e 84
    0x3420508180094480102120303100c00906038006000e5000003c0342c030030045401d00c00601c0354090800c19101c650310201809014034002983c00080d04001c100158540d2202c0690700540c40c2c227820024002400e02004c02d01401640c225000408082d0000e41160314001d1004144070000c2010840180c1c00700200081000c4103c40110303a00803a00060015200c5060004010030183c0b43d6800300c601ca41c484411554800c0015680c07070040500140c41269815915402480c0181060b032002d032003503940f02403513030312a60114211031170301c106840410004000d02181d854104024101c4040c2200102071041ca48080c7c0868907801030b0006004a070003191200c200f50007038041d60080d020143c020740d200d603901c0c240103141c10784d000310382800f41c000c050160408910901070502d03900c0040e02c2d0641c0c1c010030807108541840c50200150381480c0e00b03010200006840400a1040c0c0a11704000c1205004899068040350b00300c0c0c0c03145124080403c01021510b0b007010101500136400c84800004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61425938 1250 61424688 61424707
    0x110703080309010b0910080c040228020a06050703060501020c0a05150a03020c031303150509060606070305090a030506010807060503041a19050103080a2007120f1b09111c02 76
    0x5801c11013401603022684204201c04886401329550450311035008407506140f00d0703c2400100d1060a4407241000000416001c04040d40761218440d00518412186100e4480c0c4480c000c50300152408030001e03484540c108402d40e4100710100d01e40000b05e584080305807a210003d00c910507030310004c044410b0003050040000e0b00039410f0b5080714100b001500c1d40c6588807000843c038130410303020441c6c010741c1308014114810b81d076220b40b600c940b40d403e004001d07586034841000056009800b086040100c1003041c0c4007240c58503404c0784003c500c0341004020315410101e641d4242156608980b08100c018401c000c0440c00c41180e40890030300c862110102616194800c411500b41036122404480c20500000300308500310008161001250781c41606003900042c0c0c1e0403d802c002c0400090039800350700280800b41d2800124511140b15141c0101c2065180d90f0781030701620f9405d150340009242a200304032010741406031341440402c031002c0318500001c640707403a044144122048940c0a60100b00043d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61427188 1250 61425938 61425941
    0x5060d0c02190c0603060603180204050c0702040609020a0f080408091005041d090105160c0215211b040510080601020304090f050a0c020304030b01030f050c0405040602030403080711070308030901 86
    0x40d65a80ea044145092480f42000b241c2003645100c0c9000180c0303090000a40a8420721980c03c060704010807560040102e90204005010041d0440c84482c0080001e00016035681c40b45030014154000c0c00358994001007800383c10100c55402c020240b2001c002000b000402040854042d444205d9425a07130306402e45003210340d802160040070101c812040c4180c4d803420b8125280340b045902e00000d00007070740d90816950942c1c043da10300c0804140004503041c01807406005180e00345d044103503580c6c00d0420031701244441d1028040c0c2e0071201c0120740c0621045074400e8820004000d030344c04000b80703480d2801005c110000d4204504000b000300c00c60115145a00c00d208803801084102014044850a242407600400c0c00703030f0341030824030b15000071709401500200a0f5800c0300c1d001038270480960319688860009000031141240c2d54007580720307842c0d02c656481c81101c1c0501d000300001038492606180107000c0c1c4002411500500c8200302d41d01d84681d0b00002c40300301362a40f0071545500c94444000d00360 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61428438 1250 61427188 61427203
    0x80109021602060307030f061a040611030903120a0206071403070c0318090b1305160c060b04150303180f06030e031b1f020903030703030c0507060f0204090e060105060d0c02 76
    0x203603c808004240070840da40f503000800e05d61881c545c200300040d50f81308515030741d04c491008591b40c036405020822a96015481003592016034005480c41d0002c81800607080604401b40e0480041c3d000c40c4411041d40c3c1001060303440f040c28106503194130b182800032503181c000108908100101b0300e00030402c05100303010400c1000c4a5522480001340c40320300c034502619550380498060030400000c4058102030307000c1c681c0603807240c0c451a0080f0480303440031281c4001105083daa42c43d10f0341c041d0042e9845a11446041c0340017502d07417102040c00d6150003001175000140883c8500d190342014002c40c1803100c0390700103c0f443c03400c0c0024603440c13606200b401d41c040c1c03000c1c0c80310003a100b111f0007009200202e01d64030b0a80e0618000c0000030207c902d000200c0c01a4600150150300078003131840003034042e50200103540a18140107040c6205559000309407541c1c4609400c0443d00424200180b800600411343c020440030b0242c0800d41c1408003054150040f00700c2c040c6905d44420944802c00e00030300590f0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61429688 1250 61428438 61428443
    0x80a021504060b010e040b0a05040917040e061005090901051003090807080306010e010207080a03140d0515030c010504120b0606070f05010b031009022107050a08010b040b010c02010801090216 84
    0x10102450907041c0b0750010008001c0c00d41c00b00f6902c1800030080d10303040c815131060040040c10003440c07900340818003005180543c021a02c18440344603d030100c050400103000108940806180c41d0305e004802d20808240020307459061100a00124515a030303099090b9054540a60b180358400d201203000302d000d458002c2029003000740014000060101d454002d520500c000c0e00c403c0e00c0300740e42600490361060070340319038141c94200050542c0080e2180060764082c0f007802200c03a0070141d039041c4481c110b45041e01c661145180e07000b0596070390306050041c1b5180c40400d092107801c1603e4075504290118491900420b03110030a0001286640e0f01c60035500c1141e007001c0c88910380c142e0351500034007c00301010142e01c00d10440c00c3c01d1440c031519001d00b001350b50303004c0e05050144403444101c08042d901480c0d80d16550007203000201313075511990f003036000070b00344040007182540d1314100b8481101c031140c0c4010b04102d1241188800350343c0200c14141141c60300000140c0d07501c03107164600c41c400342c40c0100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61430938 1250 61429688 61429723
    0x4030b0703052802040504050106090e0703020307030902130b1201020a20030c061e0901060620011b020706031104120f060e0304030c03051c0e0105070f0203030d090c08030c0703080a02 81
    0x343c00c40c041660161040d28000e6408000c0d50741c03913000aaa00d0051440b0340c03000441c030900080da100b0300c603030041c50f0000301341d050106540101e5400901d8a010f140103040003d5500d0810300000c1c42c1c0003860030003507144030008500d4090302c1e06c001000075000b92004015084142c041500e0440c00f00115403640000d1800d507000390420110204c0c0c0440341620400c210003445d000305000c101d042c03040e0421a47d13651560018082d9080d2500280c9400a11515007550f0380c440407901c081082c40704040400a5234040d280090900c4030180840c0c0714826103400010701440300b031100e40d1401152034400d5400c4035040a1100c034610307000014040b000418100741c00085000001c1141013184101a81d200b1400c2e0782440380c40d03281045500f5864110000001e0b5464880806540608001c00d195805241d6840015106e1740100746540c0c4588020320030280e403001c000c8c0c1170011102000d0702070882c200c05186030a12000c4d1180d903403604c901015111940008001a000f40204280c41d000011000b8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61432188 1250 61430938 61431001
    0x120703050c030f030a0e0d0303090209070e10031a010503100f060503070e04050f070e0607051b01080108073510140105010c03050403060903030b030a060b031204030b070305 76
    0x38510340758010185418020f10440607034200200e804000e0b50290046039403000d800d100310804001501d1355802040d0240b565aa00031310150303c8481030584100f04940703c1e07082000866042c004103101195000b4205481c0c404500f110800c88100494a00d0342460728075100d0710b500c60303520545200780d405000380700c01c5040b0000d440c9400102841c401d032003a4403071020310700103031040c001504c108890b1404000141070005071031038000c02042d0103020018111500f050100e0b03507124900310076450760710b6060013841c080022035030380300c5091030151071150040d001451600018a5044040d840035120b400545000b04001000500300a10480c82200880b42502c030720001c1d0700700900a2480660812651800115280d405485800d17405603141e0b075014070b003501e541c4848005201c20602141050b850b942d013560705903020404000440d008001c00201e03240f07100c042501d0000354010300b401c108c00500003000401e802e0860359500410b5403e010410b940d81910b40d22103104441d866031084500180d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61433438 1250 61432188 61432193
    0x10203161101080c0c03030f0c040807031a06030304030f0f052b080c040605040b0918011d0907050607150e030c0102070506011a0406050703181403011d1b120703 71
    0x5400c58076500c01e8039155642d4403050b64081c550321888441d07484e140c0c01007001c40c1d040f00211017103d0348002c40c82c504905050300c4042c03007070500d641944140c41d9260f000c8201c461511320106032a400c44011130045141034030715a501d10b02170a02c610040d14507900a0340c44030038041e05000c90b4100c885d14070200d001c50f05408002c400055990003000002803601c0d0300203070000c50140101c1e0281e900719241c6500f0585001c1c21408203070702c5540f415030000c448014100f03e102301c0b40d07038950291440500740e0041060080b071944000f0300050003003000703511040c410480c50310b4030012500e6803070304107601c5003141200510b51400f41480c003174800304a10001440f401c0e5010194081c040c3d041c49481641d6550f60384045a0041f50a80c0c1d982c8a00140204420000540150001d2880380c1c407034105924130540496040449003001c1e80941c11b000903411792240300303150038424110120b110303911440e016200844900c0d542c010301903840031031f030011030b4844c42190b8403140c2080303822240d4030840d014681c0301c0c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61434688 1250 61433438 61433453
    0x2090403050d050603060405061f150905031002030106092130170601210908190c0314090f09100302031e060a0b01110a0303050907090b0a0e0601020316 67
    0x41140d02110b514150104440c3e1602050b024041d94015008108544804000404d10040c00041d40b02c45030030701400146030b40c0d100b5103401180245803103214030607180000741420300072071074a00e450351481080103000d02600600b02e4170a46082101c004c20207400104010f00c800032202015094040d420500c1e911a001c01509200006143c61911036018060005440d1620440e55441803040d40d8400550399500c0f07840030404444048951040e444880c0400d101110380c0c40c2030a5551a0b00010f6040119500c0c0440034158207452403c0340c00001142c40c0104a04415000d60700d240c080003c004240faa9940c01d0340200c180001c00c8c02440f0b0510900001034048140f200b03e02034041e14a62100c2c40034203040c0e840180c0300b081d002c1c11041d80c5c0c040c0440003e0100f1483c50b41070001d614010284044100700501007244251000035440c1444100140f0f00140d541c0240f0342241081d8140013070b81c0707540c061007086846a0101d064961900c800503411405030400030508a51b103003104206110342c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61435938 1250 61434688 61434697
    0x50606120304050603010b0901020114040b0619050303071719030603120809030d180b091f06050d031b17030a11030420181008010b101e03090209040305 67
    0x45a40d1003068054812a540301d000d20b10980313601c040240010001200c1c1c080007003102c200144000101c0811601c3c041d02201c3c426641900c207801943d003000351908100c0e2124140c03150800309107074190b1402000aa0303910581800400030001680081c0f031a0072200300f1386019108020124940304503032600180185990301c0251907122015182c03402450054801e0303030140f60210701031440c103a5880000c502400c5203080403c0309207038500c480350100745c0d0301d13040707901803d0103802030a03d00c42041500d851009181e540189500c2c91b204082001d07541c1c0340100400e1640c18140340c0c0e03400804203030549201001400c05400c10b044140790705140007c42008520941d0b010000300f020310307035541481c41030340412240204480341c8034403104415a0070010f0102c2d0000020461450f121300e1400c00303230601c04140d070f0411100f540104d05104180c428020b440e00110b056428401151400000404a04e052822280c020116044a080d110b201c2e400c05112103401500012090401d887e000700b10760301 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61437188 1250 61435938 61435951
    0x1202010309050d030c1202030103030f08100302030106030809121c030c020c030f0c180106080402040207050c0d03030e011a0303040b090d0804080a0312051603020c0102071505010f0f0e0705031806040506 89
    0x115000c10100030030b80d1003609d0590750545d46006c0000e001e110140c50380c000151541c8034616540c440000180c8c0c0034050000074503c501007090b11514103406110403521000c0811030b540d005078041802c6805207801c0c86804100d84c4ca0081001905a0410303401c00910728bc8050f00342c0035440038030005007070000b840c030554501640c00c40c0c0f030840d5102c0c070f50240c40828090000001c503440081400b500e441d4029124490203041518042000440040d00d0a0460001107011079150014054035160070311940c0d290314445000b141d140c0070184006500c900c1507000e503a01c3c061012980c20f5440d190307a05400d8001d941b000d01c860796251144112540c44d600e20301c08800195040b24103082c00841b5004060040104e8600c040010240007000d8010307400401c50145250f41c02d0002e4000302c1c0c41c071402e0310f14241c5000000030b075039414041d0582c10b00d03a030381c0c20007071141c4074001d810031900780301ca41001c3e8022000c0c641603171640c64071520802d84200c02c1c4004e58151103048140400e12502281c114000c03c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61438438 1250 61437188 61437197
    0xe19021c0c0e0f090f0319030e010c0804110f09060603071e110610080a030f180f050a0e070807030c0c06050a0209032b080c0409050108061e010f1202010309050d030c 73
    0x550f040d0300356995100585d12003d540c3c005026100703050000c0340c1901c10103000b0b800c000c00c42007074031005e150848540c0000000064201c400b800b0502010b840c0411140320190790008006062a0104007200d0b40544028041d040000001d42030902c40c250341c03400c0303044900a84025002d241d100902c03e40290480f502d050240202091600303a40e0222030084500c00c5c4040e200b11065a101681c82d4010341d6840300600c1020103c5000c41230b0116840b00103042542030110400e0708040a004050f030650f0404106000c4200030f0040e05034002c1e040366842101c0b4034000c600110300710400c031411461303443c00030071090a01d030a1120030005a000340003a104142c04490a600102164000703c49008241201e00200b0180c0310041500c40e40072581d10680100c1541c0c9031964540014041714402d90201c041d903002141403184a40c5150003030100c4038841e2214481030350510f041d11540303040768031036440c841c00c001064408590182e0807100717220750494196000403080c240007070080c0042c03820010018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61439688 1250 61438438 61438441
    0x806090706030b010801030602031f0801020c100504020105120a09080f091207050916090302030a0501060302010f0914011101090b010807050a0f0e0604020703090b0705010204030201030e19021c0c0e0f 88
    0x240e129100e03c07007103840165078180b40c59203107031110b01c02540003a02c4144000b20808419511003280c0c00d12000518900000681d1603440300d00041c140105640c030003004034240320910000d82e80c000c042e00c165101d80c25400100d5100c203800d000c014411202c00810340e04011542c1703001c0260b07071009000010000d4400d1281c001410186548401141c0155684064403002044001602e24101d2b006c95019080090f02540c0300e4000a14140c0e040c40110742c980c0d1119414011564003e0494003109118101044414100310040d217001c0c0030402104c0c10018620b8052070740355000d401c00c01c142d980024501e0b410356140c0000340d4480310079014032030148040200005804040f18003d5040b03590718841c0940e01c2c0c85035002c000103580640825001c107c10414082043c03c100402014a50305c00d0b000103a076103155200150998020f1071441d15a5000402180c0d10800c00640840c1c2469048034440361044014406800060404601410a120344800400c3d080700e0403140d107004540c0350132070000a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61440938 1250 61439688 61439699
    0x806010e101203140912030f0a03140118110417010b0f060c03182202030f130201020607030b0a09090807050f0102041a0f040e07020309010e0907091703040e0108060907 74
    0x140301001c0b000900040f0a41403c0d00c412581c003003e440c1003c40141040d40214814a0091a5410240c1800d140b41c1d070000e118807440741c03d03200e10b1500c01c411440c1c8030040d624265014441e003080b1042070202039168282e050f20701d01d0725000c075005001414200c021828000b01201e00811803e010640540d200013499101c520703150040d1211f012021005615003070800c1e2004100d485101481600800841c0444084213500290720f910f00202180040c4c80e450f1225043d01e00503c090005005204410b2030240540d0740032941c654024194140030960b50003020100c0c032071404c1da42c01481d0f202d10b041881c1d4100600c400042504601071b00880f14494a00c12016080380b2a40c810040f40042c2071070103000620072039002e01600b1281884880c10142e41e010300381c0000343e0446011b40180c10001c0e12201644e0044203043e959101078810490361b127003904014180171454003416440061400048034801810003ca402900c210325011b1050750352040c005503212002e40c1c450702280150fa40110f80c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61442188 1250 61440938 61440959
    0x409060911030c06040b070606090e060702060c0f0703030510090f0b0102010f0203060d02010c0f020405070f080f0108100f151e150203040e0402010e040c1e0207050f010e03070806010e10 82
    0x200c0d80c0f00103100f180707042d107000482d010b241e01c0100c0841d03065440b0100000c44040c00d01c15403460b654a8400b1300024034110340001d04002d4004c080c2c00e100d42041c4102e06840100509440216034903003800a01900c48186908000d8243c0d802926a2420701c00303403524032100c603080307440c0884003038000303201048100c80c5050590004076040e07600101508220030166100703c120400050140002d10011001a004541038800403114140800c10b800c001c0c11107941c3c4551640c1d07200120001200013941030420150306c5d600035038041d0242940307500358250f030020309034055030009400903020f1420f103a0700c001c0541081d0880c0e03c10200700c0340a81c0e000600380303560600880650b4855004c2c1d4079207800e16102c0901c0820141c02603041219540e109046900c4a20506010b0b19168542480c1105454121100344e119440d110085412001040210f03031900e44a48030300301e109003003d10f1218100c40c08646083e10305c1d405402c4510a0307000004002c6200e0070441e000d42020110102e2182d12900d0f03122 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61443438 1250 61442188 61442203
    0x7050111030a03051e090303100b070b040b090c0d05071a0f120a09050607020109050f010b0904020d0201050f12090705010306030308060d06061208030f010e090d03020d0b040906091103 81
    0x118903082001001e00c0b1a00c40e0740202c0d88080b0121007512240c1040e1000c0b2042c101c11501003816620000c00d1000d005500d5a00100900c914030140303141400326640c000c101100544018174040003440842c0603000d041c007030711412040250140504100900701241e0714103070340c0314028003000400f1420b24074502e10001ca614901840c04460714018020541e030343c06000080007000c00c00e586030a1200041c005101c0765003d0341180d8004101184642045800c0090701c65041e11203a24101039007401e030b10713000c04803a07003e03804440142c1d0001040c001030700c031b07442614100181070400190080102a044072118010642070382203418682e1078000643c2210707540d01014000c1049100001d00c1803409200e40c1854502c140300105e0840d64815144c5108044448101e6480b072003c0200042005603881480c010640c204d120b501d641440540a522002d003052000200364000941c0448803009401950646501600070803125019042500080c40c00c40703001c580c15041d120381034020f80340c00603a08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61444688 1250 61443438 61443467
    0x70305030703050904020f0d1a010e03070b0304060b030106030309030b0c04030308060d0203010b220e07030b070f0903020312070203010e0d08070e0d06110c060a02120c03130c0f08070501 82
    0xc500d04912600e00303450a41003d102c65078401d40800c400e18641c0c40072006040034481120002c912061400000c081306200541250b0400c0080080318806640c006100c0d0120340c1140c1d0382a0340d9448038280706d4060900480c2c4541c00d5800d2490000c00c144d8804440c4084038014001014281c4480121054a00c603601c0054006110304002c41d4051610040d91a0000e2000380000f42160201000c01d0741c000161207038510030301c04030243c40040c2004d0b0041e0400707100060090b021090031aa24a903159901414203001c004403141c400c060b0038011011000a0b5400604132200c1100c90700c1c5444a9074040b0600b01d0003035003072085c0034082d80f1002a140140004a4031440c156548120f002ca41808c603009095500159500700580441c40740d208050381d089607400040d90f03454a800b0640d20740803000c1c002d00d00d02441040b00f03004988400034550f400105007a170f5250750742c07a2440300034900c00c00400e010700642e410100004881e090341d10120221890b84040da2001561741006480b82e0700c948052 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61445938 1250 61444688 61444693
    0x1b0312021c0c0212031c050a0c02010b06040915080f0607140304022103070b09060403020106080712060f0e0d180602210708040b030103060f05010b03040201050d09030e030d030203040b09070305 85
    0x210303001840c0c40d102d225808250001140e0501c4071000415070700d05008071b240b031000e99848061001380100742c0500040c40e412400203004245054001c43c0300c9100c0c5100d4a1b4400380e6510869501c540004050801400b00c50119258040c0c1303c81c003151100d50945801c4041020701d94001318001c0c00c081a40c0c45a82c004006400e13940c0c2342160126070005451343c030f2a06000402006c000201c00c10056405541d1100040003070345000d00e0040c5c00c50304550800129607002000c2041601060a801101d4950004001c10120034441105c006410a1050146a405403080b0440d8580d42714010901580c1654441c10406540e000f00f40e856a01a0051000d4050f0700520f0084151148e002028681e200c0ca52591502e5521303102c03c0305a030401e8004403020394546070300c014036803014004c0b28090520000c40c18030354106580040c3c624881c0302d8802243c40c0d2580d102005241c01076402d601c21403409000d030740900c4070440000b00250310454040f992580072601003411000300003000d0058941c030000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61447188 1250 61445938 61445957
    0xa030203030d0c11190b060301091205070203030712210e0a140307020405010b0d060905070e0d060b060f0d051803072006070308071209050c010302071b0312021c 71
    0x4a0402500c4041071000600c414222000d113044800c21484c0d00c60300c01c20044451114031840d00c14800040501001d00c00c0e03052800810105915045480c0e211401e41007065485c0d115102190039405001009416113028881c2401c40742d41080c6510350518000304031008000d0312480940842c0d01c6422010700b1503020014240020380290701500440655904803420038180d0740c0040c099600c04d03004100320240c00b2a601010702c03054060782d4050003a5682c01d1243d4500600c00914504598500910401150350100c080c014141d1014100810180440d95130b40140740740010f1552040050200980c60b000002d8542021000e200344072860140c085c515120b0161100d09401d0f890b801008008042221002c400d0756481d002840114401e4480c1000d52030302d028003408080003c003204111600700721a00000507001b080c4002c00d03542c00d0800503100c2e000d5042131040440d20044000c01d4890304000031040c4403403070719030a08050140e400c80313510440d20610559900403c1d100f231808103c1600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61448438 1250 61447188 61447207
    0x30501090b19052404030602190302070203120703051b010b010212090f04240303020a0308061806040e1609020405090603120403020f2b02100207080a0b06040209060408030901030b0a03020303 84
    0x543c03805035500950a4a03104800007a84c2c3d445940558402c1b2078007540064071080c9122000080e642c101d030715003001c41c00c1c81c40c244c0205e5161507070402e01c5a100400000e1074010035000c0c0094603041e10b580d4034007019488194009900a060308803080d0f01600c00d000882d80d07002c6a1030112900c030080504510782860000080c08064000010312032040c110444040340d03820910001440258001d500810082c0c8035420043c1c01d225011707240a000c5c08404100c08420b900760b030040350700035501365400120503195403142424403000d00c0344055130320243c000005000f900e80d0040d0080e50030445542005444280400d41d80300c1924400d00c040c0b11040c0800c001501d02010103030341440000e00000340e0804258000e80c84002e554455510300500c00c03428106505204108007548500c5000070b1501b01c0c00c00515581e81c170003281d001030160580d0b10014406855540503a00340b441d001e4095074507240c540900545a0301f10542482c00039207000e40482051819081e40f03021250041d001e14603060915 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61449688 1250 61448438 61448449
    0x115080c03030c100c0207051504060806060a020312070306120b040c0b0a1407080904020d021c05090a0f02030703020306040309090b0118090903020c1c0c08030901020601060c05120406030501090b1905 88
    0x10180d8401b51300440340e00041588991294400b461445812240e4681c00d00b400603009036005086140189002d014181140760000101c90444820360303460026a07071259822000703030401383c0017000c1e4109250348030f6080040c0c4051041c0114444c03000c00100c90313220000c204c2c032030095442c0180090707001b204100024a41400900c4e4042c0190485807034001c1d20b4011030140c0c0d10880e12804441c0c2d00060b58050307070b02100c0f0b003400780140c0048140424104030f803503255214140d041c041c0100201d8005c84085681c03c100c044015503018098880a14040c20060080307007031881540ca2050504000381000c0d07128022480f24bc0c83d41b042410b19481c1064035400c028440001d0450662003021190440740c2e466040b600040740030b503049500140e80d0b52402c400101001c0d0303c00380403039209105000442c2c0e0041901c506444d0140b80c44022118113092451a08801550f82041c601d4002004075400394184c1140e4103982c5491824007804000a060003120041407140c0310518904800034011403815 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61450938 1250 61449688 61449701
    0x1c03050c030f0f3111030c01050307180f080105060102240103080739051c06020307170403020c09070203030f0f06010e060d0212070c0b0606030c07050115080c03030c10 74
    0xb41c040d003030b00300318400300c002c049040030b580081c0f5969850300f851040150b003150040c0c41c0e05041d40030b0000b047c000c00000e40707035000140c494010b200b51481001c1c011601007007960020400401d40f6201c403562004150700801c0141e0304140140581a840103064280c5500207140b0b03914440e042c14160300e5521404c01c650880c520445007050982c0c070010025094120281440d00c41d00e511049800e03035120302d5244240c9683c00707a03002c0c00d1450b003011a0480b0780e90107181001d41009025907a651040310490300d480b00051100c0d01241d0700820f0005256001800c0808010190303120300e415103414200b0390b6203010444020100d81c00300400950310360900582940c11010605220003c110560000396060300920800c4082c2d91340800d4503c410720081c203030030340c00ca00c20307040542c2d03003120319110940400801081c460280e10300001140c055910101150040d039000002080041170601c07010849210300d00c2140380f580310b02e28503510b4925000c4111a00050702e07500502c0050841e0700100080d050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61452188 1250 61450938 61450951
    0x602041d09060a0f02040e04110301200d0207030e0d03050d050105040b0d03120b06070501150f03021c08070b01140f03030f0a11030c0304030302070f0b130509181c03050c030f0f 78
    0x102800b001440b0480747d50f001d40514031640d508180d0304010400c0c5030031500180006002030035000404100e01c2210b00860303403e0042014050b8ad03540c1d6a0405441042c601504146c10604045c99001419072020191070f00380070004091140d07981c0c6da820030041e203076003101403a444601c0e10034980c002030140700c00c40380c086405030010840c29103a000165035500460740c10f84a0344d441d40ca100b11044001e07007890340a070251840d911a89400c58021507124580c400b04030810000244482090005020507203510942c001003420180d0784070f03d05200308411903040307d800b81c0003a07410344881d4540030098500c003064030f00406060010144040718002000d03000c0c4030040c0020022000e000c04140010f101441c004c0e0000c144662070042807a400100c980d020083c3d46101388440c2c811001c001c1802030454004440345140380c1c450781c004070078a29001890240600c9091a1050205024591556000d0098900300b10540d142400014544004c50355640e1200e1010000749000d550ba03142c8a82000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61453438 1250 61452188 61452191
    0x609061c0905070b0c010e010c050f0c010609091416030209160c020d06060303090b0903030304080c030d0c020106140603090606010f051902070302090604020715020a030e010203040602041d09060a0f 87
    0x12182ca48504100b10303600a007500003400580c4001c4410240248440d004e0310390005c00410808a600600038016238514074505c84000550405044094100786c020b0506814100001010f61410380013079a007038022415203025206030f0300c00e6a0000410300c4102c0f60080c010b100107076603070100110003440904002060010012810000d40c44031005044c1b80780c400e800001e4803078110b0601825921b840c2d07000d449109800c00c00451540c0340442500d410917403248805840754004107503d4214040d10101c100c50750f1070031030b45002c803590540103d021202c1181104003481e65580500c00c20344011140c15038594442c0d804907489510440904010380303146c2c17801c0360030050401c00c403070142040c03600d56600691160400f0b10640c03808800f460b40008080301c0851400503070b0b681d001d110001c8010740700c5d01d40742e01141d010300843c040e400000080ca40d80c070085640e031501c0e2038450020340181c050703031150502c0e000018420480400546000340d00c014010102545ea00701610045d103c03039a40301a110703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61454688 1250 61453438 61453451
    0xb07110a03051c090804050414010b07030c11060c07180c0e060a050f0706090b070c03020c0409212a05060c0304020604050d0b161b11042c010b0609061c 67
    0x750214401e84c010305114040740342c2c0d92458081003105a403040e010706104000d125004020750000750b4100c480e82980340c1010b5140002070708000100034064004140c020000007111040d50310045211016a20001c400d20481010700c1c00780320486d066150a00041240003001e41c030341c2c1c5040c0c1c2c090800314200345000c1c1d107040761044034110b150b04659001c40351103442e0003a8400f0845006a05640b01100345400d8405c06000c2c0c400a586400364100c60f07029950381c825042c103000f228144801040d00300e0340c011003076000101c002032400701a030310502d1108440c00d4900c00503130301a05010b441680c200006041a4031443c1c1c4041890380081c000302e9209000300800142c949079139201040d41405091840143e00c0c0a511b0204888044140300040101d00065080e460b400402c400b141260401c0d4400fa841c080c00e004a0000e042a01c082803103403050300c6226103400032020441148000480c000d10120f485142406007074062912115403008051005d007010098030140c0d403000d004d030b0039000b0070407 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61455938 1250 61454688 61454737
    0x17090901080f0304181d0a03021b01090b0307020705090907061b0203120d060f031406060d12030902040b030102070506100b04080c040c1b050102040617040b06040e030408190b07110a0305 82
    0x15984c046c002c81180e00050f110006041d0103006c1411200454000026204c0070000001c1c240303122800344a140b10000303c003081e00d4610811483c1c0150a0140112415051022105540b86901d10402000800c03100721700c450010410320240909602030b00410502004850320f200035009508403c101654500000030000340386442400154064403081030454904c0ca56281056070041442e4066807103002d405000921144450b11041c02c11720f00060003111900c0010003401c0b2860302c1a034103600204006040c02004950a80602900d1000d840220344d1307440c07400380c103000b98480c00740e094100d81d5040303079030307040a401c4003984298070b03c2c10700c0081140340c45201d1000700705001600c3d143c0d070200b002e2201079000240074031100364207031035000c0d145880d68422180b00c0c0c000b0304803400340c0d486a003041d10049081040e10701a200301390584103c05800c118803403000205110076106000c0c140b0203e46414000c0360505000d240d80c101030400da401c992810755440d4440300303030103c00c00914a40d4682 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61457188 1250 61455938 61455971
    0xa05070905070f0c020102070e060105040509010b090414070203030f0c0405040c0207060207120807061a0904050102030a14060904030f1202040620030307020d11070317090901080f030418 82
    0x5030041000c0020350307041240005003102007031404601404078140c409070240c0c0e00040c1031001c46142031004aa15620140103c035280980d41c44150464905400400c5240d806409046589410b56013008842d4001740710841c40801074031640013680040001c40d01010003c121603a20802c0c1b0000180740603900c402060840c1d420782541801608041014005c49905011840040604095241d991203894459040f40d00c9074920040c01130356038180b211400b801c844031070904a80010031003030040c90301c0e08040c0d003c4e5000701c85520480d840e180c070100b00690426400e90280501416071905030b5103d9400782c402825a00603501840303805c00102d049088180002e1001d42075584d2403074142150701c001000450031501d074401ca1904184204803146a00155488108084e46083c050b1800190491803d0007495040909441200b160709403103000c0d2180100701451054a844215a9840c00940d8a81000480d9180310303400070001003144550144000c02940594100040e410141030103145 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61458438 1250 61457188 61457203
    0x403120c02030d02030307020d0806030721060b0114070f020d08040909030905030a080f0f04090501091a030c0f060a090e041407061817010f0603080903160b0304080304050a05 77
    0x400508040c00d0351045040601256100c0110f5000660843c02c10103000380d111403134540103400700601400060703200c1e542041060300801c1c942901400803d1440703204040710941803015500581800143d1600b94803d00040f0420481d55092900300621a81c6030000c440d03000c90141e90140208200c1c001084299004100808404c5400145040d413440c0141c492034490f88154480e400c00b14a0342c0c0440c0c00d407021281d080b55100c0070740350b541c4030b88500905039000741c0e0801c0310a18a01030000c0392940d442d50081500001c110100d083d01c400d00e00405690310005102181c116030340501c0c0c0c40560411074003820711400141002c4002a0f00d40c41030404d4450100c901b600d885403484c3c0e00c58a6900f05002d40c00252103589003506a60203200b000e40d600301080c0c0301d040542c0c0318121090300450800c1d4007802a402d01c543c020701800b0703a03c1c10002c0703240d04003102d5184a03020705690100900320201e900000c43c0d0212080714110b950b503071148852a00000c00a4486000304100d60001590512095 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61459688 1250 61458438 61458473
    0x140a0b090706020d02010509070911040905091b040b1008070e12060403030b0306070c03080408210106030e010b150304080903060703140106111f020906160203100507050301030f0501020403 83
    0x1e108052510303a0092412142c41401000d59150034240040010b010445205454500d0300100c2c103084000448030382c80c03255a11001402e494442880200c0b8008210180c0900f05020982d6840b4110800c2008541071007401c1903103c4e000728246d440320350181c01442c0d032091040c14031580f81d881500c040f94251800300d05420281d0444010001055054070548052500650080816241001c40500301d140107000242c00d00c0a62000182005110011111082c4040c020450026041720511090741c1c028090980440c0c10b00040ca500d1160501c00c1d00c48800780140701d400e900340386411140b02c07a480a001075840b401c04214181d0030b5201000180e00070920740d600000c031044111181c03c0070160680010042005130300e03514000d801700146542c103580c00c041482d407500740783c0f60341803000344105100290454400306004000230981a85030aa4900941c20388500d10180040c01085407411640070780884c40600043c00441c511015802c03905200e03100061400f920b0b0f4581015000303094016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 61460938 1250 61459688 61459693
    0x30d0e040c03020705030a210606030902090105060f091909020309060103061a06030106050a03090606080a0309090c0818030c01060f03060e0a032c0916020706021603140a0b09 77
    0x6510180c281403080c184a600c81d8a0114203210103aa0303440e403039108550390741d8108014510707984010001441c031142d14281c0003004006065960307001a000d09049482070744074100d01800080c046c200007045642d203084828040e844c00d2048420011505a0019503040480402d040032420425902c000c50140501d54001c0045600d90716003901601c80c3d065031101d501a01100088040e04c40d001501c0c150742460a00c1501c410512a0440040c800c50b00c0190080303042c5100040ca0070004565405254040d07074034501960b8079110a9019100c8650450f800140d0740c0340000c414070143d02c0e9040049400070150b91400300d21182441c05d55841e908294000700050b00c0030810800a03100701d00c0202504000303050400c11940b4003804840d040c1030308220300030b034024000d00303014001090505e440da0000e281300034600380300808030704074010100e5003000340c411484045511400010480006030030300548415180c15603403801004d0023800000043e512484010100003402001001e204803000c100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 61462188 1250 61460938 61460957
    0xa0b090705030f0a0804030204020a0c0c090f150305061512060705030a0b0118030206031b031302090612030d111b2b05030411030c060a030203100b27040b030d 70
    0x8141c28450392000c5000280c1c407840b001320010742030100742d40480790101c41c0183c68140154080e103c50f10303414001020340e40c201e40041028940c541c0328810f07860b14044200074145c4400c1c0c00003800491800040c00c56032114001404840c100703107046854240141c000314132502d001c81c44a10f02442621000003140000c01000341002e0710303102d845405042440d200340038500c1c90359549a01d00180c00080e0007200000005000a44074040a0100c0000c007448169a0301c0c08010414004858840480c400ca43c0301011035460703e02a2045100840503102940c54115500400c03002031403500402805540c2c20b20100e4205140c81d440c203c0c1e0324000d40040d0180c54a14110074810405007240700103542010484090b0696100040ea03600a50080c800f03e5401050070000c0d1900051200d210b5004a0020b4140304195060f0050360080b118251444400c58445c00d100c0010b010311555040b800c0498445d1944000c0c40780d582d203071240c41c003410002d1088070342d0b4040703401c0c00340115070000412102780 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 61463438 1250 61462188 61462199
    0x3060901090b060604030816050321010504050903190503070207050d030c060c02010e07030303020d0209030730020108040206070c15181a090d080904090b01090b030f0d030e0a0b0907 80
    0x10b140c83d80060700300c1d1220b150900316525a1024007400d0035007001d4500b10580c1c40108401001222504a81c0c40c580b55081589a121018400b0302405120300950604001c0b503c100000000c0c0e0718000700c82e02070b00b1034014034504200e4240e003000b0103100c1140f05101000440d500c0d0041101d5045009070b07240e04140d68130381000815910311340343c09400c580c903005038101e0100d00450f100069a500d8940503a540c680401c0c2240680144080917071300d402482c03000600560000f2000b400607000450750680380c90312503504c000e00362101c907010380402c4a910001c2c0040c03600b440244440361062108000c01926101e100e5a401c3e4140d034000d02080000d43c242002c807042c0d846500c024161560482003010408411103118014025464000c03d0304081c058200150802500d4400d840034008001c80b020034205018040420301c05d4203400c0d840d195050f5a5401c0100b00c01701009000c0c002007066814200302140148905104552240503010041001491100c0154001e0042c41c8c020710340340d400e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 61464688 1250 61463438 61463453
    0x4031205041a1503061503070e0a0605030f01050411061b0f16140604090203041e0f110f09010e0c1b0303040303050601090e0f060f0607120e040905030301031707020306090109 77
    0x10708440f070420001d815004040e0307000079129600c8404032000ca081400e40f000413a1511029411084140000c0c104100400d0580ea11001c21994101c007102d920440c41c2240d94220707007041e64050b05602c8200c101c0d07405400c0000080c003c1d0b458510210710144210303850786003009850100544c4942100f8050481c4022200d844000341c6201803e02881d030b40358100262030b9124034400c0c442095000f10005040c803a0445582c01c1c02d4145810300500b00c5104e10381100341c080d480701e0849002542e83e0403c0c080c4d091154044200da200503000c03a01036401d000c0f400800d003100410b00011031100b04100c1c0101c420000081c106540044000e50b02c03401d180c540902038a0307006110318100039450804000405903221b0690700300410401072440354803108003080b080d600c00751116030001400203d013410050004801c0038000d00c15540c0320180c002e0482044169214804050001da01c00e00060000c1664240b8407070034502d4640c41107151500f66804241800710490340b007107190350741e0b080100600542 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 61465938 1250 61464688 61464691
    0x180303050108150105150c07031202010609020301060c150e030d05040203010c0309050a0308060d0b0403080f060405060a0504050a0230060d030f0305060d08040b0a0905030c150304031205041a 84
    0xb8006048150004000310030800300500c216442881d01d8040030030002042000c6404800081c400e550300e440d220304220031980b00200107000150310345900000c81c2c42c0385209903416107107295584445003502d5101c2040d26074008507030003c0c541d03580d0f0078454281403c02c000c0049407003208001c1510700c0c0500405003103c0c01e05003518141424800d145e0000361020408418080e454240000240c03518000f0400a03109128000c2c83c941040302800240341c2c2141c0100d200d00c002c03101d2503050f40c3d44c000a1005941c01030307503229005023465005101c14503280d00240d40c02800d1100050500000400d40b0700020b42a540c01c004440d9107964110070b00416500c1560b12403016a64201d000800e580e005046291850714a4100761b0390b800031512541c0c0340050b01c1e00f0513401c801324541f1251182103100082d0701c9151040003141110600041c0ca05010900d007004560051034441d64440224980e080b07544010400c40400011448100c055001071040c0d500417401340320705070601500c020440c8402c040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 61467188 1250 61465938 61465949
    0x9010e010218040f020403020d081303230f0109021f030b090c070308010608130b070203070f050f0c01080108030a0f020a0c03030305060907051303060c0c02030316172104020109091803030501 84
    0x401c421f00168680c0c03109840d0b160b5009850540c0c03210402d4000300844850707040100301e041002c0303812080504456190120043d0b034410b0324501c4c0820a5000d0803580413003402904a80c803140607100080916203490b12034504c501b4042500030140c0001200c180044480c841d1501003c5031000c14150f2069500340500704600304500e443c100b103140c00a8004030401d00401c1440c1110004407084c0c4240240d80001d50320441c10612a00c0714500341e61610020b1500e00200c0c42404c0c034105041d881031880604071900440035614100c1188402c8940011500b40c0c001940b19020403200010300e000c5242c0d0086009550014540c1485420071000b80c4000d0150030401c00113000341905a42642c10b0442140d034004070002e0400a422815115103030046e030080d606000100f4500f01403951181d0780c081240c85254032403085900414031040e6800f42e8038643c004031900031070b02c00c4180d0300941b6041c3c11600504000c411103a0f01e05c0c1102c01d03035242c8130180ba0b484440344078180401d0b406005440c090203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 61468438 1250 61467188 61467191
    0xf0e04180f141f0b0406080312041b140f030c12010606090f0602030a08040c050a14030709020a050414010e04020c010b0a080705061c02040302040504080a0206090d0c0b09010e010218040f 82
    0x11111480701d4090b03c85040c101100b40d0380c650b810344195880c0c2c0e11400c000d0010409031303900d510445c2070b010b41c441c604550544091030b059a0100c012024110b01505a0701c010301034800328030052003440310200e4601403a58041c0f0a030548503400f6581e05d0000100b5072805030010883c7c500300940108881c5041c1d100038102000640c06104864001c003c1e0340040c10070340b81c600003e40e0b1340d007041040e0812585c00035800226a640124103105200b030100c1540409800f110101076071442c4020807442800c98071000504180810320141d40b03808941d026a550524002054207078000008042b0b03446517101c1760103a951061410550300785001c01000400d0094003906c4814908800300d0001d129007900c8094405000b210f64007240134643c150b40146801400401080c1740a01d01403131240d028a02800240c880c14001076074a0034001742c24440c4c0500d5581e0011941070b9540e407954001e10240151401e55210344100301a1082440900721780a9003886a00ca240f90000501040366242804550b205 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 61469688 1250 61468438 61468453
    0x100b030c0c21090909120a09050a0e070e060703020307050102030f04053a030f0204090b01080a02031e0c09130605180405030f0c070905070c020a050d02010f0e04180f14 74
    0x540d011003030303d2440d01c0c00d454007002945d0303081090341031054400708400d1251002ca00d0284085d80b104108040e140e064481c020b205807241c07044120360b0022180a000106920001059070405101a0250900c60b0046030b0821a551713550509a0704101e9101c5c203000c07404d4040106008080206845c180701070020b0140c0603080b40342e2078482000040038501c628080080c19100c90b0710961101551800d01001191219105c20200d000303060041140c0b4005115a00801c0303054100c1c1c803ca900484042d514072248150b000008242080003c000b085001011300460140703407205103140040c400d1503640010309034241010007500401d609104100d00003200704200000301c0c0001261450b000303005007240c5400c1081c6110385440e80c2900308007035690808050000302500950401c41880c400c90380300c42c2c000c0c2c40b5400d119680740701803000390000d00200800f2440c680920000c854824003c0c4c40459800d2802401401562501000302c4001c1540c0701140e06000a4003054200d5518a03400350915 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 61470938 1250 61469688 61469743
    0x21061f0605030415020a02070803040b030103030305091f0b131e0e0d08010e0603030423030706050910030b010e040903110c03011b14070b01090507030b0306060315100b030c0c 77
    0x1c030b00c4800020700d13401c0d030010385200064003c02c007882c02000000c0071070769100c0d1220714421450300284012404641000003080e4840c1d00441c98030301c0d0044082e4040b0a151080700c401d00545410030b074440e0400f81d10300141c0c0c113041e89409801040240b00d40740341250031400c0c041408446840c5080015a00011681b041c1d20361700680440c1150010203c1911a0b00d850001a003584601c1e885100d00c1740000c1c904110480066503c00c5540e08118291080329540d100705880354410342c2a00d0380e2050081280d81900d80c0240c2c00071010740010701d890724081074a00d0105085542040054011511703119040c1c42c529020842c547d2031490580003409102480c4150b2880d1a10404e0b081060025481200f4211440201954011600802100401d50351b07203c595009000584172040024100f0034104410308000416500694002d0000d003000d44d944a00e15801c05406010a2210010900e001650410070030155000780c01c0c0d00b103155a502c0d100b10200c4d240000d50b00f60140b0044490103218803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 61472188 1250 61470938 61470953
    0x7051e070b040911042103020f0c060301090f0f0608150c090906060304060b0904120210090809060c0a050307050d0815030a02040f09050d05030105010f1106010521061f06050304 78
    0x22a00804000f0070b10034404c5802d10013901035034000003213285d030040c5a03100c01800168101c900038020f80982c4e126500c1080c84503110314802d18011340200003080104140d800950000c20001c418040000e01c0003440201030041d0f030041d41c00501581c1c00148907032400343d0004101500301102d2540545807a400340041156403400820780303881041c01000150a02c88250054581440000c00f0102d55180602d000310700f18201c4481c40c001442003035807280420b00da44c450a90b0603504443c01600340f080c404100a00c0d5407000e01642e80d14042c00155800048003080940080b030311801c041c0a50302400e0350014a002c5004086120204e0040c000400c2070700c2c08101440c03c0c54042d00c1c00b150303228031460356902404268200612600c40c200e10140c0841c3e00001450595100b607032080b4441d030640e0412142c04800c058160f04a4000342d004001ca454100c41c3e500000e07511601100450340031443d15800c1900450310031842a508501d240c0d82482607511550150186041042c01d42c00d00762114032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 61473438 1250 61472188 61472197
    0x50103020f16080712020303070207140a09090606060f050a0903120c120c05060603010212180a080c0a0606150c020d08131d090a02010c030507080d0207051e070b 71
    0x14141a80000d2800c6002070340000ca50240c900b0200215415400740b51507000707070303104420980d690400c241015460a1020045034000c6003030345d004161036070800f191060040c03503082195901040f140000121260031b4000c00b00d045014036400662285031200150000395035a0f01a0200135042100d20072040e000f010000640e40c0020030b050346040c0180c0181c0f0030801004002d0708000340122094056903021400800ca20f01c90010750f02c1d5502c84000b45420307801a0482100844c02d0907000400c110a1615800302e1101e11030200e0700b20105a840d150481c0d4407045503400c06400407154001404954056240103000e4400d40160b04082e60034020845c54262200030700c1514100d47c2c0c00e0900c50a0300586916825011400341e0140d43c1c0d60080003900300e002c2070b540c40a41c054002614041022464443e01a01a119650042c500d81d0301110160312200c41160100e009104070441c1e08200c0c8041e203603607841280240040c44000d44500c4080358040358400f59507000000c2403000c81d42640984 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 61474688 1250 61473438 61473449
    0xf0319020a0501080103020112050a0f02120603010b1c0209040602070605100e0c040f15030e030309150901051e0c042403200a030902010903050d090320061602040e06040510110c07 79
    0x80b8bc4d290038450b10b02400c0e0240e40d084566001080b841b000003144240c0030b00031641240204000204481440585d480e5021840c8441c04100714031030140c2401180140c3c070900c00d1000620f850f0a543d1840100d0341c090314000d1048052400502c80c503c00e401416030400d4625080c0360074140390054101468a160081a0350b640405034842940d50082e00500b4001c080081038030744038540022140e60300e5242640c2d5400318221840480c0300700c0018401c6030702440d034003042040124404180300714161009044030114050070040040c80481d40c502901545e85640c0450b0080d0413412002801c1c0d6002c2c907900e010000c0c40020b4203480c2d49001c004c07201d4801b03a41c280802c12074183d000684030400d07558800380250003000307038040c0749550181400d01074038460750401c11f617540c000d1501030050900d62142500458200f041c0700e03060115551718070781c041c4018004109104595280f50500c1e0050390125a90380c000007a4800408090084201c84266400c00c02e04010840300100e9958880e842003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 61475938 1250 61474688 61474691
    0x9010915180b010b091302090d020405061c030503010501120c08040b0a020c030c0709140103050307061a060c062202030606100201110711100503040b04110f0319020a0501080103020112 81
    0xc65029114200c814808540100220080c3d680d510200f450750391007000b0051055910000c12911051244291244000050124002814950309010090002400040d800103c2003a20487e82e1620740da0440903500c40e554254a81d4074000c0050442a0210b120301c00302c0742048002c01605903c02c50140e401a007090b050702d00c9868021001009100d0340c8031100b4107020014158800d250000760040c1190304401c01005421804806407840c03060030b0200510b1034204100c01e0022500d5500208070541d45501000c6044115400151081d0b2101103902c401c1d030004020400030300c1880c6101d89240300c4d0300c44d8021a0301469030000341ca0304402000725100e4200c03240035014862013588902502c20840c60011782e035802d58145a16404523080a45206201609003020090701c100103490090b50310490950240e200c5503102d401136440c402440e60010b80f1210311003900d80d000c01c0804646130013003040003118806801031080c507040940023641404913107801040183d9200c9801030f03000c50b00c03060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 61477188 1250 61475938 61475951
    0xf0e060a0e1506090307060e03070e0403020706211407030e010b0a030303021803120309070f0501080a020c10111c02090603040b0a09050d030e010f060b09040b0a0f03060209030609010915 82
    0x180240144c405881d01751061600204690381c01002c0c41e041d40d481181181c01160b615915070424940480c0c0080060f08180c9003000444c0c0980540303641e8071458a4030880391003403504003034100c99032266001c1d4500d000505100c5140c0e0184540a200d140c00402407080d803034850041403803038440388002010154000740f0b460a14030381d20403d519980005040e0b4050b241d00421a0314290010741e442001401100320000303070341c80600c00013030072100113852700321199840c501c0c100000e4210382c5149646024140090b4071880d0184a00c001d1401c000703ca864586925074850131420034055007062082e4030400c074288181c1d4401c001c4e0790b0b001d540040020841d81c0c982d031014004c0d203801a0020940d2040742608158190141c2042a03920b1100e002080321002180c03242003550800d01c16070402c87e40410002290b81007035001107001c002c0151842a540b5602e10902c0016222a44150b420a0307000c00c1e903120b50702c1d043c400243c01098041c001d100383d6120303481c1d85450002c00d0781c526808035a1070030b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 61478438 1250 61477188 61477231
    0x5060321070c0504060e061002010b150f0c1608010c02030309030706020310121203140f06040c050903030409020c0d180e04060906051e0618010e060a0f0f0e060a0e 72
    0x421102c003502e000741003444419641c40e84192001c00c01e43d00c540c807504001c426103035554414440d5108000d0002e1042240003112615a5015800300324003414290040091000c01c500410085690099a034044000c040c50072080e50308440d40c0000320000c64008200388501d40000000b6078075110380080d80169280c882c849843c4030422a80d101e142030220415101043c80000510140300240b00c0e1000d0182ca1000c0340060040c0c4411200c0c804100b44c3c01010070100d0600344d100924400890070050700d00102c0d40c1c00603107103400907401444601e4000400d00c5c4010414000e084024a140c100341904010318407400c0b441c234442d4082c5c44c0d2107000c1480044c0c113100450704203112241c0c00080400581c24440c68a00c581189010800e490b4840c0d00e0110741c0c3c2c0d003070981a01040540180d484c2c00580d080016103000243c010700313840d0b03101403a100041041300e40340c611a0010107504804a00b07042c80c2005403000380c200104014810051800101f125004a17180c40d03620a0a1340200d640c0c1c3c41205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 61479688 1250 61478438 61478453
    0x10e07050705070603050f06040204050319051009050304050a080c01020703110d0605040605160806061c06030c0b0d06060905061210030c18050112051c0c0609060507030506032107 79
    0x5007001c2d29501c2030760760000700a501544024001c5218400c001440d80d2001d09101c10382c0319511031140c0503800756504a00a004900000400718801c40c01e5883c1c0340c030b0000c001d0080c1c0710341d20300907116604006820056031404540f000c008210341c00203460008040030001c2d40303440c198031000c2c002d00e4903c44211142d0340c0b42d46448a0907680107a04025505050070b00000800301100c040f001604030200c0e2400150003416214459103004007003514000d452a5a0b07030000c0300800a50040903201c01c0040005141444010f000d04010b5007580e80720303110008180240d03078142c0d1011051000240d028062501c0341811215600700107200c8490300c1c2c0b281c115090030300c00c2940c03003c1d06220a0890209640b01d0540c0d06e151100100f4074180207990301c400a1110280c03070040002c150b6406003e200003000343e00425002d000c90b40742000310503031407a61070b0203003076509008003110050303a103004111900d90940304150304080203800518408400700070001506c0d41c031071070342850030708085101c01c20440c86 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 61480938 1250 61479688 61479697
    0x306050c0c010b012307020d0b0103060e060f0f010909050c0301050106030b010908120415050c03130f060206040b010b0c0f0a05010204050405010b0f0306040903030209030a03021b04060b03010e0705 87
    0x4008101514001099003500e41100c0e00242580d402c1c600542080e43c42442c0d9900035150b61944101a2180c4040e4080154015a001c980051003902e101010400c480305080c005e501411000c07405a481d40091810b0042c002d0101e440301005609004410030006030182c15100317800d200180800150910510b0000040b01060b413640c2004000301d5070540c16008641144030a0300d81000c2a92110304c401d80f1004c40d080181208a4248010400b038000c0030b07130380704001d0780b2402d1542c030385805000728a04582c06101100d0120980d00d034100500301126145078011712036440585401d091640d551625900306206880c50000c0c04202e41305540300a00c0100c170300000301c404071051141145000c6010b50403600c1031900c02c51401000058040c070503021240000a000c5445140d5560382c2c0400c0f0080040ba84154101913091010040b81e480800c100e20505000342c000304522155035948a607101141501c60f0301443c00e2102c00c102116501741500c2c1075a000600c2100e03195114102150240035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 61482188 1250 61480938 61480943
    0xd0605090c091503190602070206030f010305151e090705100c11060913090c092301090b0109060c021f050a0f030b09040f02010e040c1106060306040f020d05010603 72
    0x282a052240c4440d0020341da40034070800350394441c51940ca04803e032480e558114006901600300f500800100c84100d20900c0100c0c1c4030718801401c0c041660003040a43c0c01c2114500c103c208000014024080100070100070740d02101c00da001c0e2803901011040540e810982010306019481c0702080b1400c0b0144804400b41002515002043c0900b1034010082410007009482c0f565603000e00366100c0c100401103800311000503124112002c0e00c547e0800042c5200322054460782c820705000720780101c1b03a002e0b00805980800200d4001c1351002080a03240c00107904c858000351810a940e20180d80010304007044541e24149100c410300300d4008542c0c1c40b000481035040e0f907908540c0c0c03841c45640000140c01e0028070355885660a000851055045425040043d544001014000b07800148100d03104031101d40b041c5002c0a101d41d016000c101901c803240901000328503082c0c070314070440c2000c2104540c0120124000d003600c0c203054407400d08095900030082e00038040e6200b1700041c05400d4010800566 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 61483438 1250 61482188 61482191
    0x203070510020c01110a03020601050d05160605070b0a05011a0c0102041503090507080a08040314010e10020c0d03061202010302071a040c050901060c0b2205030310170604030c020f0d06 81
    0x20780c0c03008025250115002401d0210b1036000045002200008400c030710194140c00501d85a42000d041042d42c003020441260b8510501984440c4180f00c014242c0003018541c54850301c0310014a02090207070402418a150507207400010426000c1ca840b40300c207039035240c42920b907551207007030926806841590440c204091001c0800c0d0503440e030551141031594014020b6030300e05526440d00c90344402c809000039210781c00609c000e00200708103000c000c1d03400c5002c02c00043d05001c14100386040500c10355000211950114a1500301c0300c061200d020741c070441e454200700b00c0341000c035901c5080b88290702c080e04155000c00d03401e040248030203104c0201080300d10345c80d00381d01d0700e85440c60380689140030f50b500414200c00001080e9001c1e03d10307003403110760101c0306400f50f50366844004251010b44504d224903501d4145250081071060005502a4008003402c04010b41802d821341d105000b189103e02e031540c03000040001195021080300c0c0354660460706041c0c0d07030882000040880f0756403007000d05200e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 61484688 1250 61483438 61483459
    0x30c0d110304210512040305030702011808101e020a0c08030402010e1305010504061a18010203160c090c050406020709020a0315080303090c0604050d02060702030109050613030e030c0609010c02030705 88
    0x180780003a09114261040084039107170034041c50b14030141c5c09107200090980c0d00902c04040150301442c0c0c1c0d90306003e8076145003919580e48529180c505681d1702c03400901682d8440d003a805402004503100000c1500810540c0b40c807040d907100500e543c01003031020300441c07000300c0070804583c0319213840202040003c0000206041540061008080c04c0c070601d403040f480c00f50002116921140f8404142110144080c10f014100a0f4081010f820b41900313030450100b00b140388017080c3c1310304240c481c00d4082d00c20042204d04010898040b030b145001c80c80c06001d003d1008100340c0380c3c00500101500d11103031015803a002041c41c103901504200b01c021035200c1c084000401d1201000010f03521070200141200c140342c0702c040c280405445070340142600104406401c402504082c0001d00c5001d10150002400c00002d4507441c3c1803140959107100704001032022101407650011860709a40b008030041d10000011500040c00e41c031038000403e05010300440641305655081c09240000c210140914541 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 61485938 1250 61484688 61484729
    0x4081201080f192001030e0111130e010806010312030908072d0b010b1c050f06120105010803160204090606030605180609190f0c0b0301060f02030c0d110304 69
    0x12103000c03a1002c1290300c500d08200884410120300d803001c458122200c04240c6000340c0c0c034980034404904101d8141501c8100b22400c06009101b5036844090700541140c8581409507401c0c03200e000c0d07034008a10366180000500411002003a4035044079441920030f85c008201490a40c0a807601c004081c0510388007040080500000750039500302c111640800c2014480f03029400c42d144100c1d104050800e0090000500c0441228401044041010900350341c01da030300121010260341d000c03924035000c0c0c0071305802c0c0709003410304041009070960120002e00480d03041076a415503e000341c0500701340c03003400c4500c0c403001c0d901c440c0d010081e1140c10610a011294581c10818090308040e06c28600b2880120324130750003c04003089003801598100c01820f040381c0d040114a6203a50703c40f1082e5220b00c40c203000d2300c0000390f000f404880181248148180c5940c0751150103060408940c0000096401c104001c038044080420030424441084c02c20043c815064045180355000e980c21018000c41e0100f9803041c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 61487188 1250 61485938 61485943
    0x6210b07080402270f060603070c02010f210204030204060501050705100902010903140705090a09080f0d1415040510060c0b0a0e0708030c0c0f010f030f020904050712050f0c0406080408120108 84
    0x42020400070f401c2098442e2400d01680b480308527500d03000581c24a401c00700540c0f00e070a941231040340520300003444d06011803101c0c1c45081d0503488800c8455000030b04004504080c018a4010720003400c00c5401c19125403640c580740c1c1c080c0a007260b00243e403401e17542c04580c01340c014003004c0c5802c68042c0b4682c418011125030b40d030001e03000349071080b102c890015500312070900942c0c98841e0b00070701075030802205010020598002d00d003402d221903100d0008a412050102c81140302700001a102d800c8003c01c5024041116406800900741c1540a4414400f65801402a19503950f00030414031a44c0d5522400c4002004002a0b045030350003007041c00103c0300c0e4000080e00e00041080b0a5680d413020070020484428403c02049000c1142031020b14200d90199006525039031910704c0242c94021424005400c0340d10031107040c0045104021030304001280b5100d0b01c0d0340420707002840546810102860b80300d41c06207220700410800e0010000b810044003005503074003d05428001c18042d61983c09098 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 61488438 1250 61487188 61487191
    0xa050d0518010e0607090303080604091406010e010b030606160f060f06030c05030f190c03020913110301050609011512060e0405100203070e040207081303030306210b0708040227 78
    0x3520360800389014119000841e040380514820b403240c18030306d0320f50780c0c055881d10350090103290700c680d032038038404040b03002c184410500644c40d10140c0840d604218061940240c113802c107c41303802c01481045101d8942d5001c80d0032104012a140e01c0c1c00c0c42c1e52511080c402c003480001000303582401509003e008003500008103591140040d080c1c180c0e01d600c00d1503a036881c02c0480042d030750701c0041c079040b12a40b83c0e00c2801119026001e1010308548a4012034660b0314165610009500010700342e0042c030200e080a4802c40b0411070007403020781003050006541c590103000b40010036200e03a55000302c0901032111070080e070040c1c40090025550351100c3e0411000103c5040d20705008001780c0240381001c1b84200d9210b40400d0702e480c170300541494240002904104000c0b184c19500f04540d00c407a05000a203c00114480d075130118070941001c01c40441d0f030055400c903002d020340c3c003140040010006d01120354040114a4502401c0d40d9a000241d088030744088000c900e000c0001e000c1e00310071a11003056 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 61489688 1250 61488438 61488481
    0xe010f0605091905071413090c0e0121060801050108030702090705030103170a0c080c0c041a0108010b130302060a0c020f0a030f03030e070b0408071a030f04080a050d05 74
    0x200306066444041c4401402c0c1120200c000885407190010540e071154800c0743c01c14030528285a03403085600c1c2840081c0d101e02141400e9804c2a001007007250524000c040400886103000100c1080080029005c400c1200396495800000e80f54550b644103907901c500300421000e0000d0200e542c1d40c2440d5900c962064109a0180f8a004001805c43d40690f0441e0304880c1e1141241d0304043d5484107030070f42c9070030815080040041200c0300760042201d0030040c0c107000300d40324040e2010403107890401c0708954000015012400c9550843c2d0121781e000781c4014112040030740001e641c1c142c0c0c2c0444081c005203d4200960000b0040303181032a90740d11280b08505148207940221401d090b4a0812440c2c03007041c48010700f0700d94045568400030744207801c56101243c0c040110350b0401d031200d06204054125400010540c0d0014008000c54000c0314224034030070719004401841c50418081d200b0034840000c0c0b024007400740000342c0b03c2034144940c0c202d885804603104d00704250f0500035003090200d140581705 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 61490938 1250 61489688 61489691
    0x1305090f120403120810031403070212010509070f18050a09020a030b010e1f120311191a060a0506250b15010e011215080a05030403030f08060a0303030504060209040e010f 75
    0xc030004c6074064400c040c0655481d50b503088441d407440e42c940f02c0010b0400131102c083d0000340071000041e260711909415440c0810300105a500d0302100c198601403060384030010001c400d2030100320000c0c2d94002822441541d940200b07407035a4010009024044000700250000001c46000091098032030703019068400e0500d00d0246601c0d1380410000754040d202d891641020341e81010031581d840c0b9134001301524072905080b20200740300140d5a040c41305030984043c82e0007210005408000144c64400030901c5074081603d00da0401c2004140c21510b24050070740100c1c0300007506220070a441e2000340349080c00d150003410001c040c1ca000540000284e8041c0240c0d6500207441c20030313601408a01000b000182e540400e40490040d17400b015056100c3d0007000c01580010201c0e140c2405d11000384054022401190340b207246190040510b542e2918140400c8a030605000c110b03a0303680004000c483e05441e0118141d220b40c1420b40080c4580313010244c0c014075000c00441d5452041d0824516074112620 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 61492188 1250 61490938 61490963
    0x1a03010f090b01020606060a0e092701061d071e02160b090f010509040603060f0e0c03071203080c0c0303040606090c171801182a051305090f120403 65
    0x110303070180c4109544040c0540c00502c0024003601344030300a00f202140074680348000900c12804245965026110310341c60100480500541c90b1000003440d540c144407000803c107040c42c042417020507241032000e5540030203101000c84c140510516109a80581c0d2001210030f507650f16201175914203403c54050414031201d10000fa40b1280c01054407140003024010f400d00b05402001100c030756120180307142e4020380e101c0d004000300c0c040344551454503940300d90001e00c5050315082140b50030050600b041c800c1c0e116840a1050701702101c4410031031a03045c24810038546540143d4000c5000729801e46c20b42d44800320410040c0320180e040300c030889564110402001001d82c0f8201c4d4034030501c0145e128003505503008200c0340701507140c080080e00a0440001224442080380300d4069030126025600d000c1401804181d041142034554445902c441d03030103c9141c545070120341e4808546500c000d071039954100242c03604200340b0021101000b06825603d170131109549001e9a03030454007045c0c03405040b101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 61493438 1250 61492188 61492199
    0x1d010e0c0108070203090f06040801060b040504113a09030e0a0b030105010207031104090602070305130602032712030c030406090b040605041710060b0408060a090201081605041a03010f 81
    0x202c907400b031901680550700e0202c0900a1010100c2c5410415810510030000000d0109082c400c5801030000c042c0c0f400d40c1d803072034881041306072413050f01d101989800c20000c01a81c11211882480c01c403040b1000401842021740150041964040c1c0e441c08560903c04070108040e800200004618000c65001c2e0540e52a0302850a16004c00d00919001d40c4c0a000d00b40003040b04140a1034a0440040011401c03412a9982d03409036009910110045480850807804081041e10100058041480114280b21000c13845903030154141861a43d00020144280c20a4442d00c3c4410801c4080d03070200c0c0e0351200d001c01e50558940c040d2140c44c0c0016419100828152040c0044404882255a61038101420407141c81c58888030b09514603020711070700341c80038046110380c0607050081800e004016210b52918016504298009182a8016250414944c0144c0c1c0200c14550805420000e05030f00000e1081d00f500e251041c1e0b000500307045e42c0c20080f009005500c03c02103060782d580020030075803a40d80740d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 61494688 1250 61493438 61493447
    0x80a0902030d050c1014040c06020d020a020105180d08031906030f02042706090605060d03081f1205010504030f0503040b07050306041d06010501030c050f03010e0a1d010e0c01 77
    0x25850b0b0415001da420041c4502c014246020b69001618000040008440c04a841281030000d044100034100010300050300b90b09030042c0707540d0000d022182400440207480ba150354000905203d404a40c0000b0705051000d404407442016003400c04a03419803d209006810071141056054040020701c03003840d5403030040b042200d07486014955904295420000038041d1a030f5040d43e580344c4c220042440403d0040010b030054011880092905a103042074010740341c0080c8490700071600c0038551000242d001001d260302542001c0403c80c81095041ea6513020f4000e50720450680e01c10103202014010f041d840b03d80540d100343ca45040d4103048900550b00d5010896001e01740000c20703c005a01907016400942c0e01c400d00030000201e101801d02000c8000c000d4440c0070a00f03902c404010320007940c040c401c0c940501101c1c02c1c50350610600e09540c12191105000d54a01c05000602042c41c4142d650840698034124000002520000c1f04640b4000c1524040c040340c10310403992030b2a0627502a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 61495938 1250 61494688 61494701
    0x9060a060210020c01020909041a071b0f020f06040609170c03150405010603171306030506030c010c05010b0603090d0305011a03070f020703020303040603062309010e070306150503040201080a 84
    0x354001c0d01c9030302a030500520007500548020421075400300100343c3c2d1540e41084403842075119008808000c402d0180224045500401c0001070104d103000c3d009101c2c200c5007000700c04540c000f0440801601c0f0740f01017002c1c0309510900d9500400301050200e04030307410668520a40782d00ea141c0d440d032160500101540c0d04060740c0041d4040e0040c00d0b241c0710442c54000c074a58018003a50000c00d00540d40e1359222104184140c580703a5002000c0703150700b409060700394081e00408503881d0038406401c20500080e12101c902d00401d0620410160100c1044403c0d003040b0360540303000f0a581e8803890038921b40b03600c81d2055401e0000080c90322001003507802c82c969030700c9ca91070b2140051509542d150007040e87c0c41d802c08203490041d4411803c0002c0186d500f00002c0c03014090543d40800c9031460b00c010b00081ca0240300780c40800b10301034190314580e902d50f0b0209a044400c60310801c8143e456440d801d90045c42182c100190304010980d051800c56082801103010f217100380d0b1208003950300c0c05071683c2201d58 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 61497188 1250 61495938 61495949
    0x415180b0f0309122701030501050102120d0e060a020c0d0c0807080306010e090403110f0f060403050a11010903390209060103020c0601080616050c0606060703121a09060a 75
    0xc0c24020103110025440155030700100410440c1c8026080360001c038070603080120504051101c1c8030074503e503c000074401d5040200d00303003800d00407541041c0001c2d444240601c0b406031010b00105800c248588150000b5609072650402c4d144207080408400002e98412604681c1500c520a10015a00d2240101c0c0c00c00d9a005003200c2d00f0b00e012550780d843d444c3d10150455042200d0840001c8150743c40c5825280598030903102c00c00c03c1c4000d8950942001d1104000010f56045051008856040800c07604c0d8000da152915580c0d610326140140c8d40c20300c040d00f40e81a25071801400d50209030304843c54051a11854294070900800344683e03003071000281c00c00c00d808e03203ca403074508014149898002e4012205040141c149141a11014a005401d0f4000030060340400184007040b0301c2d900c81000c04000318500305d4a045004c1840d40d03601c40002c0c1450b401080c0c0041e1303900916200f01c1128a0b25031901906010019180c0701824808180c400128030034150a40032800500d8200c1601e000c0305d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 61498438 1250 61497188 61497209
    0x30915020d0e01090504050f091204140415080307050f0c060301060c030c0201120e011d0303040804030f0302030403060218030709020c07030b060a080604030206070314040209010e060411041518 85
    0x101010750403508807103450320040c180f0468039004078042e0748a0090510843d0390310210501c61400300e00291800e800100700040882013080f00380100180700d1400ca80c0c07a00c041e5804511074419261860110f000350380402a94040411030307804015020440095002d0402c0448000252640410001d44000c0c4503d8001c100d81e43d40315000030f405142c84101c841c3c01414110b403d042c0c85007048042da034240f030031050543d5441c610304103040c54200c81940010714200066044d85815074440e600351003a400094030401200c50f9210070944200111009540d0108096480b162203504070b0401080307040e07a05100c0e000d900760208140c1c0503407017507a03a40c640c0f1354010071610f0718545a4030302d064000381046070442040340c00030a40c102c0403c441d40c0280c1c0300f40d00505103481c024100608548020a41d8020310311200140009643d850794041e040d500b0540355041d5940b1031000290080000124044500c203012900245090403504615000822512412a0440c0707841500182c89094043d058512 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 61499688 1250 61498438 61498453
    0xf01050103051009020c0a14010204050603040b0a1808070b090607020304350d0f08041112030712020106050f0303130b09031501151205071d0d1e03091502 68
    0x80d0300c260452070300400031105080d25203490311050703000c4c0e03440084440c07655846081315004000040d1400844024075200071420700b13040100060180c0310203800508512110004581030500300c2d40603803036010036444c1c000100d44a82c40c05c004107412500054070310841f07460004951040118039644500c0955016600d003a04002c4c0e0415042c3c0b500d43d031a018204205004c20000610f80826903000114100401810012072801007180041d0302903070f820803050304141720000300001c0162440f02d500304c408038955191084580c0c610301610300c2c0a0140c0840307040c2e00240076019446031040d540d0a0707414007001a03c0100381a88d03849086a01d04806a907001c1c100309542800002d001c034800000c0603100d2000704980c032064550070a0f004800c1e070720740c5401e50122090308600c0c0d252440c0c9608005010a00e812a00506408510200c0c011300c000c0b406031280441d43d0365001382140c0790b8044400b04405400021110ba121216042103010035040000890121202c03400310b80c00d8a1140d008080e00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 61500938 1250 61499688 61499699
    0x2107230d02031e012c060105010f02030a0302031905100f1a0301091d0d08060906010e0904030c0c090e010203061201050112030c020103062102032e0203060f0a08030304030f03050f01 80
    0x48180c03d48120b0b55a9803001c42448000c00024002c0c400da03a07040c000780480c105003660400b0410b9000c1c41c1400310000000c2c841540110a480001c3c21b43e050043c0c40c0c0e9101c480c925291281d00c40385e249518944800c2140d82c0d11401c41110980e08895002c0221039103403040000049981950003078000304c00e10040081d034444d80c104840410160510442c0701100100c0d05142900d182c1036030b0040340c0d0034010070003242400d401d0b4a501060034a40b4803803000f03110000c01e402e80070140010b0100082e00b407103a002e100c001501800107003d10380c2c040010460581040c0d00075041610001e1284414880141040c0c2050150300c0c160b80d024900c1c0007200313503141d8080c0c90101949404030306060700c402c80040d09115003080d007142c40f82214000c03104c100044c030401d42050400c81e039180b01c0e0001c4035025040311000c0c1c10343d0492035040d00b1005941c0d403500d10000b06035400b11110180d00500824011801c1803000c006580202d2180d129064040000e0380d0175003d880c812a0b0100c0400000c4004214 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 61502188 1250 61500938 61500973
    0x3020307060c0e13150b160b0f13141c0f090509060f120f0318010e01020706200c060310030314030105060d05040204180506060a09110403022107230d0203 68
    0x69159a40050b00e030000d0b603403000103146d0b030065003140381341d050701c800440705110341c00c0d098960001d078840840c12036180882070715100c0c0c20108005800d1042c12590445511000c00901404c020b1403c03290600e500c0d4158010403c81c0101c09800018400041c001400d051000c566801090018940c801203061101131001c91081156001e4591040c6001c09403028420300c000d05442a5101308051100c200304009000c0c44030300c1641d24119840300000300303c0b2075840801007130b0040c0c8404c0001210400444102c0c9003600700c145075503004000000380840407140c4010b0780c0442e03120b51102508407050340507400359808240700740c0350001c41c10040860004525400705a02500c020000035603446400b81452048420010854059200c007040c00751628111481000500c884041030140304204403004040780181d1000a004428804085002c0c2c9900122508004130a030115100a85c1c7e0b01003207940503030380b10010b410300000800c0310212400d00039101c0408540250090180d03c200056145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 61503438 1250 61502188 61502201
    0x30405012a023009060708031609120b0a05070e060310090b0102030406020d050307170405010504060b0409210c0506131101090503030909190c0315050a030c12030201020d060303020307060c0e13 85
    0x2a4030179010406100090245030145018203d101004182d2110000b00903215229980000a601c500c503000c20001800e8044415841400148045040e440c0c0820564139914803000c0c159210345c001c810407a04140703c116074401c45108a400f40034100d02c42d40161313140e00ca14007030078006030400d81c00000d881c0d01504c001c6030008581c0c64000c2030352055685000c80e01009580440d80c0d07035156410b11080c00030700d000311821614202da04011000407503450210034207146090703212500005985076240f500498000c00744a4104094030001d141900d1f4601d41101500422a41d6510b503100310a581e5201312020415070b48041c00462800c3c0f0801d040004005004040b040c034100010104031100d54580680915140e0640340850121545040522110019004640a007d280d0420004140d1a4510b0403c0300c03e150145031600300d0600307040303000e4410108a0705440d82049000010942e00200521000d03001d20800c1014401e94002224082000440d2075440000390f80005c1c0ca503d500e91242 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 61504688 1250 61503438 61503457
    0xe070507120e0a06230301080a02010e0402191107090c0e060d0e0106080102040e01150f1107051908010c1809020a0207051e030d020a02060f030405012a0230 69
    0x1140040320b10b00010a00d0f8200d800250024085066900d80e410110700b681508000d403042881c199810032280b00e40d18440d07500080d041000d90344e010001512180c2c11195100501030344002c04282031580070b810b0300c1501da08031000d4442c4035030000300004184503a890045041e40c0d01d0102c001c0389420080a81c111341c1614210640d60680d21000504c24414880148901c0b400540c403645403890320300f480c1c00141d010300b03002000d42c4861800e1591011150000228508180d180c00d4940e22110b85441c0054108540041111824005401c40b01441c0000c030b605840c003e100040301d51070f0848460b40e40c486c1c60f440c081d45109003881520a260007070205880d4030f1040f604960303503600004507241031004802c101313214642c03411000c0b800c0070b0200f0100180f5900003049069000d901003001c600c1200c1400c17020703584c00b00114042000030740087c107400116240c0001c030403040c42c035020844100510380030090302c1180184001003200601301000000724a03c10b03400d64200c10390000c01c070303840070064 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 61505938 1250 61504688 61504697
    0x2040b060904151502120a0309170315040e011505091305011401050103140408071b081e010e070303080609090f0d020c04060e040f020d05010608010c08040209010e07050712 76
    0xc0700340030b407524441d0814400f075160305110b40e20b15002000c10030a00400707086045401040141135625407a4040350350003c550300d00001d110311642048010440344980251108200106000f540166505101c410f01c40849080200e482580303015400c0302c3c0304458200000b1036000c410007440c505440e070581c0c409181440c01070350b02c9041e9269070866096607a900030300d6000c44014000d5580c90312480c41010281d500200369420203842d10000350150050042140313444042e0781d407200c60003928080003080c1036403c98282841c040c2040300c0300703001582d40515541c640b020301c041240c00000d0b50012650140c50318407903503c818044c4441000c008000d42c89a1013642c204051189040000a10171400e50b03000d84000f010744410803081c2d501c294030405209460005100100e012101c86190b507a07811103050032289180d00c0d040b4050708a5500c200d52a519144d52003c0d010f42008241c1d00c500d208440380d03495a83ca44c014140c615406a0342100014010310141c00000e400704141007900207031303060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 61507188 1250 61505938 61505947
    0x1b06010e0f04020f040e010e0105160315120f020a0e1f050f06032e060306081b04020a12020409060f0801050405060c13051c0b09121801120e0604020310020f03010302040b06 76
    0xb1642503a07807112000c0c0449c0e5407001000b4100340b0201c00c50601403282c0c41c060002c0381100c1c8045480c03460724011042d46a0f4403510381c4041044800c20010798960107004100150b503110790300700510504580840d8020803145003e00c203c07420300400010340e10020a01819004aa01030107260b40000708284107500b01c1c03206421500d0010b5503881e07041c0c0c11180414100c0390401e0002003e50b581c1d0f901a540c1075212a03034845100340200e1000400440650f8010b0300c03128041c00840d480e0603010a0603200c2d610014010941c070003071344c015105640e85145441d003596030f01c100403401c81c1c0013110090071079044000410103810003000105815000403411030055625240002d21802174203003038a00c4840c0071740c0c440c0100311200d00e0250340901600040c12160091640e0503411b8410340d04601d1240b2120a00040c260b07000d0b8640803001c80844808106d07003608104416680c082c166030aa10900c075614103640140510700840b0b0088685040090550346507500307002c00f4050940403558070400600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 61508438 1250 61507188 61507211
    0x51b0d090b07060612060c120507080c0306060d050108031e03010506071103100501080a0308090c030606040203070302130305011d0615190b0a0315050a030302060117030c031b06010e0f04020f04 85
    0x1101e182c5c1d62400f409000400ca04620005001350441c03821640d409401c12041000b2a078012030800d5000e82044407081d500c0c1c0c4c903203000618511651178080d20241c6844004034144400001a186442140004109402102400107000c0c08240302d010740c0301c01d040014100286103c0c0354000000c00160071603507100041c3d0f42c10400d550098105814a03031140001030149640050b1058002c440840580080c00c2050003003901c0f44001080540203c1d0008041010184a5030403107080f59844020459110f44903d0f2582c080c000c03142c460180281e104000342e40500003c40c94a0054000001220b8072038200014003240210b0101e10f1714445109200c001012442c100040c0455001540c00168440150b414401080d0454008500548135034000b0310020b138000440700d040d03d0407007482d221690541c0254602d1841598040381c464040814911540c0d25107542140003a0203001c2940c82e1030380c1303c0a698400940403a1420041039140c1c02140142c00c00051204240c84042c102142c00480718 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 61509688 1250 61508438 61508459
    0x902120303070f03140f040b07020c0409030c050706141903110703110f0c06090603090708150702010606020d210f062c0609041707050a03051b0d090b070606 69
    0x850700d080228a0180d000f8000c40c1c0c0c184141a2400c0100000007400e040400c1d81800380d00009200419640c100000710380210300070001d0840100000b0b00c14450b1008038038005040241e40c52080300c1600c0b52a10115100d4010780d150708503980c04011090409405110454100f03480d00260341c00c1c10741c0e42c0307203081d85950458002d042c09802500c07110b0751b03031040d806914a84011121151380302d80100b0004101540c801084800c01003007150800d1b00c80d101d07920858240402c6a0050150788149444801606a59051548650700c2d5070020400746a60700b005984400304240601d00040726022028036121000304201d000c0e800c1c402002480c20300548102e41114030700c4d006014400d441c0c00b90402c001d5580c14440301d40340795506d100c15450610401041001c0c01c00b500007040004140d103c80042e41c90302042c3c500c043d800c03030704860782400f0505002c6e150358010480344480261001d1203112416001800000b451116074408100614108094803035411121044401c19141d16000561074400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 61510794 1106 61509688 61509691
    0x308030c0c0d110c01210617070e040b1303030212070908070f0e01050931060b0609010c030e030304050406081b180c16060e07080c0607080d0902120303 67
    0x140b040c00c000c0f00100250b100b41a1a01c07000040c5940c08c098000c4201d40d460041c0c900ca16250412000d0780c900c12540600002ca032540420300510101e0143c0150747d00915005040c004111071a002c242e1083d1150800604400d078180000c03903040c000f0324000c003106642c1044803071400301d10b29501d20303052103201d10071104d540c009201035040d01352040400e0b6076038480500008da40c1d541000c000291010a48040340b40000b9980e0a0520400311091804146c40f44140210309a82c1201d005403480000c58040c0003d200002c1c1503100e80c0910000350810901820000c2c0858449403501501440002c0c0725400076510140c90405c890030b401d4000742850f142070b40d40d540c1d4042c92825140c10f0325006040038601822500c00c0d85000c2a9941038940305819108000310580030841c540c0601c0b13802a05103007007007200b00a0a11540e101044007480604048612420306007001e085400 = true := by decide +kernel

theorem cover : BRFrame.Cov 61330938 61510794 := by
  have h0 := BRFrame.cov_init 61330938
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61330938 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 61330938 ≤ n) (h2 : n < 61510794) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
