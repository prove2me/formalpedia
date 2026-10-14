-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0742
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:31:55.503012+00:00
-- url     : https://prove2.me/submissions/73f9d919-033e-41ad-b81f-99886e883a44

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133273381 ≤ n < 133453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133274631 1250 133273381 133273453
    0x30f030709090527071406070302120f030103020a0e0610030e070b040e06041401060203032a0d020a080f01140d06061203050c010b1f110a0203010f020702040501090e0d11 75
    0x105000c504078401d448140900d52010008000c4c68881d401c00c200307291b0b0b0072603105480b01c50a01302a4201b54468540031500c007070010740408944904000743d410f0700d00a50700ea0800f40c2e05d40e400404104015140380342e1140490b01000c00240c402d03080340c0310005220050b183c4c0d05580d11112003250304640c00804104100108012050800c2d00c5000781d1044005110351595240c5000070b522844003918040303103400c25901c04401d800da00381ca80254000c0744184503a48041c0301c5800d80081d0085924900041c803102c01080c828928810094140c81c2e923180b003401c4071041001000032108100f5070072141680c8603180054600d44d041d101c2a01035002e034450a80c0d5030300c00f4124a084032018800b4a110340c0c105155451009281d0305441090502348c200342c1420740309a076080d8600042c0c074400030741c10b60902d0b03180d40c200c002540240c1440d910950702808035917240c84001080d80d1341280d00359540d9000760018015107220703080f022032200e0a9000e41300d8001e001031402d0034028180c400b41c1c0100a0380 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133275881 1250 133274631 133274671
    0x111010c0e150a050702060c0313270e0d03020c010f060909050f06010e07030c020c0a0602160b03040203250f0306020a090918020f0118151b05030f0307090905 70
    0xc07a8611100c58030b400d200d140040591001d8903501403558040e000708008110300006020800440c1c550b0308030a4001f4184a544101c2d40e15804041d550701d4001c201d005550880b40400350280c1c800c030005100140c008014404811030094110171081c103065901c03070400d8001010103129183c0074000700c2c44003240482060409600e8078802d040c682c3c51960040004110f00402c601c040f41d00a841450702040301207000c3c000b24585040f0304e50195124403104030000f042500058522100c40c3c401e100c01029513a51581924507004c112000b9405400200342104848010300d51403002c0c405422200d08829100c69241000c1101c94000b1160b150740000ea00c04000c4d04070320f400d07008144d840300070301204c54a44124a0b40b8610303014000d00411000c10981c080360300400500b041c035584881c44941695840307010301c007120456000c03840483d080c078542c40304080c000c0010000742e51f0450011403500c000300d44049001d91009024004203d55400b001c118220107024140c003c612000d4401c00103900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133277131 1250 133275881 133275889
    0x110609010c060219200a06050a02270406140d0605221b0b0301060e120f010e060103020913020306010e1504021204020a140a050112090602041724010509060111010c0e 73
    0x141e205405008621401725801480340054a440c3c119408280450300351541c0841038068068581c0b0268100145603042d003e000c840541c2c4009494225001e10400340e4808440814800d1001450303000f41d1000340f0072004c02d1f41904000e802c8119840c035010003001d541c90310310351600e44000444805412421009860384d8801500002d0190159164515450312101400e40d008154040c3c1c028181c0213035910703003000280442081914200003d10046801d80c0c803140c1c0740c1c1c1c4240000c0303108134000c2c0e02182d078202c803072040b4000700750b80130780181340b507900f448480c0070b403280c006181d400c0304c01c0740652400254036103001400b42000b130240c0f0780d480d0b03003820320410003181495004203a04003010300d9080155a0350060310011a0070030300380140e004841c0b40c0140041c00c10000d002c0e1006000160011300703090044085001c03041c804050300c010030095443c050754004400325220800031100f0042c8800e1500c116a81d0b080354050500148480c407460b542c41c2510f108440c9080882e000b01c0c241007260070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133278381 1250 133277131 133277147
    0x304060c21081602030406121805010203130510050603031b0703051603060515030c100306030807082109060402010f020c03060f0a060605121302010c050a080414030a110609010c060219 81
    0xf030707140040d50815041c82401001010000700540442d500e42c291040740d5400d07184204d25032600107000391740e64603001c8101308840202c420100d0301c03841505c0514811500702d1103040d000e040010301035460040b092018000c00c00c4070201c0000c09000c0c040000000a01c200802c01985140c09200324070103166040200450384014034080400e403405210032075544d00442c26850003d0700300c61665203191f10010490040500342c0000301803e070b0010b0100c0501503c00c010f000e030354860000390b07020b0445040b1041c034200b40c1a111100c15038407880c0800d0041d800790030020008017641c8100d0b49801e0183c00002c6c40c10400760364074844041003d05010b0068050301a0601402c00e50511928100e100c0300c140711a000b0041041d0100310a840100085a00c42d40140d0b03101900141119800c1e81642404240d40d446407180c061200c42c03810b0700c0455424042214000c00c0c0d084000e000300d09460a00b03001643c0e004004803410000040d15680000d141c1303102800d40c0301d400305441c0041c6444094003804c3d0107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133279631 1250 133278381 133278421
    0x50f03120402011b0308010314031605010207050607050f040e1302130c0915021c050f0408010204050a0e01050d02090604020d02040806040b0708010b0d020d02040914270304060c2108 80
    0xc1200b4511382c000c01c0e04442228112036000503143c40c48210820356504600a404145d031501450507404014007505401401c81c05019400741c403c140c03140c030b40075552031140501401d00ca020a01c401c00230041800b01041c6c0c8403200c015141e484070010b90000f0301d107142c200c0c450341290f5640c0e1103446105d944419404041c101d10b469005d4448004917000c2d694034140210540a044400079074000c0ca8811000c1c1c03804031080340f0350591a2a101c4a609011350400d0058500a681c0d404c0f00180f55041d4403002412540084d01e85410002e00380c0a02122550040a407600b00f90200040c44101d03d141c4000c000400070380015080351f0030545442005642b011f0b020302d040141c4a401030008070041021030390300c0100d00d840144d55034a12a4110b000c4c1c01140d101600e0603140812041001c401c540420380b14483c00000144850100c2038070348454425a1500c0405a10a00051082c140900d50303135206030f401454001c00000e603044004000c1d488030101100018403c0090118040542c581c5611403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 133280881 1250 133279631 133279667
    0x6050405010515090307030b070f02060a0203061e03120c0f0c030604031b0309030b010314010513030e01050f04050603090a0209070e180403120f02031504140a0207050f0312040201 79
    0x103545404000790100c2c043e0140d079a4009400200d10205550400180c030045900c00e42000340d615018601030030501c0e41d01100c2015001d01000a40b8425046c07084134801c20000b04944000d05420b21070703643d0401d0a80980d501489910407004008202c1c4001d81004a00d02004100034140c110519003401c5414202c80e000b40e01420622001a40091103803690200c0c1030b4114021034401d043c11248000c040e4805480100c40400200a1120b40905030b07024104540003840240c0301c0052034444840d0000003e800030720350a142a0007036200320010150b030380340381c0d460a04054031000001c0981d072041d91800d140c1d0f8000340f0b40f10304500302021210b62240741030410345840c50f5200e0202e4028079611344500100c20241002070308150180100071200c22040000300180d1754011b11503002980156030282d1181501503c0d40018a4540509104405050b400511a483d40c55622002c0c1d0004e69084409019a40c1d420b80103c604001420070345411560064142c1040d0001618403c0b0440f810100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 133282131 1250 133280881 133280891
    0x21f0c020d140301050d050a1203021305010203130b090d080d06030525090c03110a020a0b0a09080909060616110a1a09130209040627020301121b151101060504 70
    0x3040c2c0101543d0441d00c0944500040032107074500941000d0001d840149070082180030f40d02e5242d410f40c0901000c03a618154024040d88400040e60349000d62b080ca01c80d03d107841c00c024064616100c010f00360301d05003c0c2c0380014000130f03039840d60a580c01c0415107071146940c481040040c0201040f50ac1c81103001c05001400304c4515082080d010359150040c0302c0c5154035903403038140d000d1281c1c1c002404072000003119600c0e2a4960002512054050401e1300e903000c4290105040c0a1207100d04550980d105400526152044090108130300c4000c2c94540e108000307100401509156102c041045403045007081c002480510030009010019000a541c1613210700005104132596021130ba000201181ca1485095940b44140040e2041c40030b126000340c24410b0009629000c014003c1072070f5001c031138030031058500e00048402c0340070911802d02d04461041d8003c021800c0b40000800001c3c12314840410680c69500081c0d000501e601c8070400100d007043c03400700500f020b11610024280886040c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 133283381 1250 133282131 133282157
    0x2d0e010f021903240b070c050105180904050705030d081812031302040902100e090a091214070804150210050903031f120f0507060e010906050a021f0c020d 68
    0x340b1581d8105402e401d01d9582c2190034950300c8640240c240c0031820220583c01d07079856007200f5207580c0280c03170f08503002030000d00042400e6001c3c40680f000b0000d05034400c10300c0321916042113091007000e401911b280c0a0041d020400c0c1c0c4041c080c8505131040c0c0e4a80b66900c0c14011099402001c807100468816000030400e100727054840c41c1202c0e04009403000d00c40106001d400054018550008001e500040907001201c1603900300f0202c0704007060448103007100e541c0d10140a01a20202c0b035009104040701da400656a9018103286450403007007030183c0e42041800da07a80405607000c3c0d00301540075401444e10008030381e8104150b48800442200600a50501c4ca1159640e40400b41084910b0035040d105e41c0c05e0100b082540340e00600c1e030301903900152421810310b2401290195001d0f11640034858000c10b081d40508400e1142d0b000694071910810325041c022038032a0000300784a403c6010300c000140d0a50b10101e01324881348126040040c2060208402900e4241404582400e00c00b12002d114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 133284631 1250 133283381 133283407
    0x10c02060d0603051608660901052106090a0210030e06010902090402070b011202090105030f03041a07060c11101a0607031106070e030d09050907032d0e010f02 70
    0x510007460f42030f0300c1200c0425030b03d10441d81904620710740090005580801003061f5920300d2552a00c021102000c0c94a0b104004258102a001c049941c201c501500104414202280200110741d49944010010000024001c0c24030030240d601c40800d178800c464401c1036140000440314a60000c0c20208405e0500c4c910041d00d0706d43c14410350603020381c0444c0261072501c0c0ca80464000641c0015211210368580c0b11402d03c15a291000340e000d5a014000031405040002d4030100d592a480300460801d40b0b00322400180880300c800120110000b4041d000000700079002d0005140c2c0c813516400c130029583c0d5005440d01401c80020b129039418010461000b00c0c40c00070643c035900c2d00761102d599596090030140c2e01a100c90700c800c0d080f8801c000c20803080f80d80c4461032804c2070108070140e517100c961300c1e44201c404207c0c078082d29500087d10008100454025407002d80401c0d03c5c0c2a000d115400000541d140321500381803007030040340d180c00c000305021400307200722858400c10500450400c440d4201d21 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 133285881 1250 133284631 133284643
    0x120201020c15040b0a02010f06080309011706010c0b070527010c080918010e01030501060b040303090506030415110d051e0601080403020c130b09060d020618010c02060d0603051608 79
    0x524010100303041060700b1120002c00302d4018000240060b9501d1001d990020b000b400101017900c03680b4035081003c40c481030080304803280f00344140c0d50150501c0010395850302001016108a05001d5010030410028031440141c612920b02615600d44501c50200000c21500000d01012042e07168007440344040d0781c0000458544c660060344242c1c0307494105000c1030408102181490491000400005034030060340080385c143d038405c0009100580c3c1e9290070907514010b038040200414031030081802030b030500e4000783d58071038028107054000300003020401044030800520091820400904003408061301c0c003a0640003510301d00940d4033710000f605202b40791080a07005a0401400c034010400b03143c401c20540c011107100030500b07003110300002040b0004180c500301c2e60340192126000180189041b02030410382e06d8003d00010f15000b2205c2d400c11940041c10711103070510801e10f00900150329444080c1c0000510741030000345250070341c1801d034035201070014a001c640400207003c1c40088400710344 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 133287131 1250 133285881 133285903
    0x80f031c02090d0b071d0a0909080f0409051012080d02030402010c02040606090f0f0e160504031e02040f020a090303050d060b0d05060f06040303052d03040c0e1003050c060c1501090204090612020102 87
    0x100280d145e40f141b8000c0722b14820240340d030040400200340400c080c005130f440f640c0100811701c41405481d6889860500485078000e029000340c1d400c0c0a80801c1c1001500215441441450306280200d450760001c1e040702c1460300540009200e1130400e0022540c2803c030000542098200242440e00e0542041d840c4100200100c01c0c101c0c0070126081c03d18040c2c1d00790f8014541c4a64450b1070403c0c400b41e00d014244088800341e1107541401d81082c0206402c1c130842d43c00c1c0307049507580d40742d26040d0384040c1e0b100e0340220074107c01d036903607100d00150600c1d02001800f440348200a000c1014140502080014428a4203262080c0d90030001007000030340101c220391886680490185c05910001c3e410034880c44003c00d031900a080000400040004442d52032041e07640c1c140c040501900d034940d0589201400b800000d00c642d0000180c90080d152160140901108042c120380020001403942c0c00354440c00c0c0e0025103510b80100d410320480409024120240c56032104c10b0712002d545400003580c03242d030646 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 133288381 1250 133287131 133287149
    0x30e0a020d0807080a0201020a02100207120e13022d1c05100e0103030e0901090501150507060605121b0907080402040506040e0105070c0c080f031c02090d0b071d0a 72
    0x3031030802c0507002c2a2501c25070010903e540381d05c1d0034a8081e020b9480901c50078018040c0440520348001a482503580090700b0805100d114082c1d8030042d60f009099216a0b580712081e00e480a0380c00c00940010300f041c1149d11115400c9440b010051901992110007504480000f03114031208015196a4200124407694000c541512001e40c401800c00c1d50717410040340701d82c4c1c1000220605400214404802a00340c2d04a40d0340d030798400a030300480c4c0c028010400100c41c0c0070044c0c001c1d103200710040c00340c0c5030180a0015506654a00107010300401032039004254200d0100d01e59401c80e07000c6c1c55149400141c4400686240c1100010140080200700070710035552540403581c0ca4980703921030040351103110020401070400e41806495010b881604840a850b21400400d00400204030200584103810055091204441e02c880003403a508000d10b0300a80e00b4171100d034403960b0300030901c0c00b690b0113480f00501504100000070001c8441ca210782c1e55000c02c03403a40c4021a03c80e82001b10494009034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 133289631 1250 133288381 133288399
    0x6021f05010e06100318030923090601200105040c060807090608061c05010f020c010b0a0806160c08030f010f060503100608090c0d0804050a15020a02010f05040503151501030e0a02 79
    0x1300d8141c0081400d052007040e50f8400d181c0403010140c010080300d080d03901260b0400705100c110490124486084000c032a00070f003891004c980f4550041c100701c0811310a10000b0b08003840c45030302039405c48208407420349a07401c01c1801008050b400050a40c0c009026161858903a1b0a201028002c208040c054900556868640f1040c003044503100307480b4168403070001d0251150102450000e508500c0842d40e0551902040d41810701e8800444030494800101910880d0b0301c400c0b20f00d80460907a002c11050200c1109501c00250000000318400c1901444a1415506250008a1589041d00444244070040040c0071007882140312000031520140ba0800c01c40d03652440c030504106074240801d130800d030664418020440c1141c06030040e5081640c01d007428569900c60728070703820741411045000da00500b00080242d4030a40c44a00d241a4609240d403400340d407607010031b160066913412420f01c446020148989d810701350014102c90b000034a41031180407000e000785511744090803130080c480c0004d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 133290881 1250 133289631 133289659
    0x50c0c071503110a030603020f0a0810020f0729060d03051b0f030403060f0b0103021e03130f0303140c0306030304181d07030501060b1806030601020f0706021f05010e06 74
    0x9801c910480000041560703210700014002174003508460104900c00c540103c0a03070400d00303043c0998422652078100900780d203034045010a0080d8000598140e2810007003000f080860b1002500e0b0800c100150349000d00a41031200340380c800c8002600c0240300305601d2403108042944a420707102c60103122808150460440401640703064910403103500c4a00000c40d0000a001c61030b0310001c61007043c601d042c4030507280003004400724840d42c020342d121502c64041c1d80c6600d52091001c0d550040314030517840404092a00d607468a0310b1003001c110000303615041101290003216291036040058500950300714202600040c1d101e0207a4001c0054042c0304125000b08080141c0180820303000b60250300030200d03088000710740c58a1007400b09a43d29820400c0000700c14980800312072070085503089451030a0f10090800c8400e91000c1d00080c110b200340886005d00300001d10003070b4000c01484d0000d1107c00c814456281009000011b88510b83d86444010030440b00340c10162540014211a83d14010342e003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 133292131 1250 133290881 133290887
    0x60d020108180106140405100803030c0a0309170d0c09140103090201030b0d0302030c0f03030c0d0506030a0209100503010b060310120516030303050105130b010210110c06040602090103050c0c0715 86
    0x1407010511010f600700100050b1030151030b41e07600034000d0f050320140899907440350a943c00310000c0c81200d04c15072080002a005e01404c0d40039104200b050314001c142203509488401500320394440b6050801400034143d40c11140902c94078101c200340e8100903a02e0b81c40e00d0700508800c21032409540c11b254645503481c00316886584204001e000091012944642d0740c2002590b0340c0104010a000d80310f020b020008000c000801e891240f90b40041913482c10001c2180d0002800b80034103c80e4151245466840050303840018991080f00081e102c000c166241008142c250352881c810706002d00c80400900403400c922000142c20359180304a100031107582c514040c5d103081198010556510360b0044040109035168100c0b074101c61049070140661004042c82104132a075880d40c0c20f0150348032003903402c80c1e4000c03074120700d00800c20f0000c1e80e805c14144c1141c240c18408115070480d2150780c000fa10188a44e058032815811400040440d82416100c000c0d00d44e9651b100e0080e021503045011102c03100c40e02c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 133293381 1250 133292131 133292161
    0x3080c091207030f0209130c03171603180f030b010b030405070b0d060504050c0301060c0308060f03340b07080708090406060c15050c040b030a0f02030115080f060d020108 75
    0x9500e03800c8410b0150380e03080445000300356040480c0300d0340c00340c40481c15540e0fa0101c4807014541080b44480300e0391940d5551020b4003012111020000418800052081d08041fa030303511a030b010b5260020700f05050b00c04522100941e803c2080c15000042c0c040c00442c03851003034141901c2c0e803440c0c200e030381c3d484505005142001d21351100a0030311001132039000204107031300070344120340c401d81c1c080c071072038840d0300e4500d010f4002405400d00160f058240100424894654039800071409080180b07002a50008242407030300c082a545840c1060500b103003c5c040c02109a17003c107043c50201200d0301410040711000c58818030501400c09000412403c0502900200301d40341c4000040041042540d41d44010b003038110060020342e2070410000c156014540340307006092242140440c1c46160506095141443c0e030000390a4104175640e0b082e400000c100f442c03000758040c007012044c44141d903003199001840d00000624a11b803c810000500c4129110742c9190503400386d0900701500700b03039201004520340306 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 133294631 1250 133293381 133293409
    0x1080105160c080910090906050405150108153c010c0209090c06120402030c090408090103150b04060201140106020f03030c180a0b030702010b030303010e010b03190203250c03080c09 80
    0x1480705401c5132400c5400140b1b48007144d507070132000d101c015521030401c03044540c101d6171544101e031101ea03110340640c89000c5c10356000520344210600078000f00080358080b5507600707021a07042d0229403840488608840740da44a10380b0341c1d0b6024005202003000070085510164000e016000303440204d002030300240291110110302a20f00f94440b503003900500c03601c000c295010381c001d0003206500d5405082800c5110321071500002000d28000b600c100440080100c0a12110741175910702000c07902510250003040200110760011903402c0035020b43e0b1403440b82c103074429400c0d50f01c441e0014904141c0442526401001000c039141c4a209055106605038a0b0844055010b414400c01080c44980c0002440c01811283e0081088000c11003c0c140c0d40c4c4003e00840103041019401000119104d0000715408001e400e0214070301c003800c040f42000d07600248d83c41c408040c00704180ea0300300d45441c01d1000d030b251041e00d007442c1031038025103019000100292070340f00ca10000140542d075580b50081c80d4140a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 133295881 1250 133294631 133294639
    0x1121a0607081213020109141807030906050a060e010e1605090a2711090306040b04050109021002011406041b030c050f0406030917030f1609032901080105160c0809 72
    0x44d240810b640c8a0000300d07a403040b8081907140a0101d0724290300c601d05102c41401510b603101c08140d5004408208000030144410507403504501c800040701c6004460043c124003001060007130078911030049030f01d0305030090065080f01d0343c200186001808071a08a00c00f503424902e80d602c1003900030800c15031144d00103410b4040e070f03101450904032101c00425050b00c012007040204c910414902c24071441021001903050b400000807a0200301d5040100b5002407080f00001400c00c00ca6000c990818440c1c689440540d6481d416000b1389140800c01c10340c080c0080300e00300038081c01d0075544080d5040e2210550100756445076001e0100340240b0880c0c84141013051080d48481e5140e1006010700400001140e690b145042a2014008807200750307401144401ca140000f99208848a00031003000b410003420080ad0040c000041044219510725060440c054400a8810f45111562503001039111840d0340e85000100300111800c090b101c0c200e00010f1400c40050400c80c24910450b0080c85055948 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 133297131 1250 133295881 133295917
    0x10302100e0d0b04021c0b09100204061d03010f1401060219030c061d03040b0d06050d1205071a0a0b210c0d140613050f0102070213020d020c0a050102030601121a060708 74
    0x2480a003030a1fa5100741d40140071104291910707941d65069000300e00c20742020440000d0001101c0c41250110740c03411401a000190000c1100420400d555100103c003200003001d200500c9042e60510031400e000c44214020b02c400c800301c1e540200b04506030180500042c0d500e590401311601d074040c004040444030740c2101d48494417150079540b180c5c0b1844000001070320f40003001440d410700d50030f50403159801003680c141320004c90106071180e82c00808126218500c44208404108031080a180140c40003400010ba490000c0c01b03002620000880540b803d404070540546d05000026080885040c241c0320b04510014a240020f10243e08210309500ea0181404006c1d00b00c41010f07101100d0350080c0d0480b1484034030380c0403850803407142c180d01079000700707038031a00032101525500105804040c60f000149000c00c9003103403034102084250201d4031650000180708166911212000f4149140b4100300701000000b02c00f00000d45440c0402030007480041208014486000e0079240c40c0c64164000d540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 133298381 1250 133297131 133297133
    0x1205040b0319094107060318080a09090f0b0a14060f1207090f0614161a01031110050417072601050703050c1e0c070b03010302100e0d0b04021c 63
    0x81d0401c6140c40302c4407007443d00800c0b0304100c2007096014001e00041c001d0100182031080481c040c10101868913212802d1203500303000100030300c00400414425603201c0d80c51600f003c101d40151440480c64de4210350601c10704100d159500c00c4047c0031149400320055007500204041a4035000b00b0b081080000c00200c3d06000d260203d58046208080d950780300c06400380c81d500a19807038205801040b00003031414442d02d12080c680c600800158680449500300f5045946c1c410780d60307200340010b11560043ca400108100410300c00078100c0c1803401c60328001071010810000341140200d10601c0d01d441807440303c0c802001c500b07210000140600050034503507400e290913051a012a145070503041ea42c0b80c03100260b07101e4428844c05020300c8488441e2440c003244144100c000b4001030000601102c0700300855450507004100b49801400d1803182030fa102d6256004200b601030031a4100014802e4080845c0c0c482d503a4617600a2103e544000128100c0d100d9001055051a554400c07003170308005600303650 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 133299631 1250 133298381 133298423
    0x206161707050c0a060c0305030109051f140901061103090405060d02120604150203060901120611030108070602120304050a030c0807171b010b06030a0207080d06060c1205040b031909 80
    0x445480400e03561080260340d45d1a044070388050401c80640041c905000502c07070702c0103170380083d078015411840010404201095154102216602c03014030384800002403003850411748080c0b0300500281c104002681240150f00d0b8030b0b481040c101c03600c03440d41d80f000030782075a440c85141c040840d0040c2c000d4010b840c28140c1e40b5900e16058500b9240316180001000c400704250007103911130607001e412020240d291450020980300c41880840e04603843e099148210301c24540130714028084200100f00c62843c4c80c101074242000f103030b10b00c00e844408000f00000320350000b60700300f031040e031500d844001000b0500300364040d4007030380318001c0410b0581100448035191020182c03001c2404540e1510350100100041c501702d854200c44590014000e0001510710800c3e070b80030301080e50291581c0d030b15044081013000c04480304d0380c01c0356000c2240c5600c9201482103c1d082820a10068103206141c2801d02000140500005106040b419070424101d04011072039040102440c0d4070150b16055445080021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 133300881 1250 133299631 133299643
    0x30510020a0215090a06051e0f061201090b0c0a050c011107030905040b030c040b0409020307030b09120c070306020d0f0207140d02010c08060d02030106030c0e07120603020616170705 80
    0x200511440544204000610300c1c040d004d11504002021030112036900c140c05414024500244500d1100b4164903c16550884601c55258550809114900203003080340b80406400f07114440d0b89031103102000541e507007024580011803a25407a454046246080358a449a4440a501f03035007807018500b40c2000d11400f51517100d1180d12a440700540390703070601046a074141c0c9074980c140d100107041155804c0541c072100c4803050190000c81c03412480e40120389062000e51084076444508810005104000c1c00711500c012090f100b06841c02408022031541c800007800003400e02540010700200141c03955100080d90312010304255251f500a041c2000320500c0039540c1401801844600001e191062107154882d00b580c1e203c141450311114144100702d100914100d8040d9601d0201002095940c074810001b415140d041401078540135100906541c101c15030b4403001d5081c0340061005a5491042d56500d540c1e40c443da0b00d50b40154205540d6021040c50448904600043c5c29000d000001c124 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 133302131 1250 133300881 133300897
    0xe031b0d0c030309180b10140405030d09080c18040b060310240608010b0703050306030709050c03070207060c0f0b0403030f0204080a0219050603010e0702030c0d030203060f0102150a0c050403051002 87
    0x4040004600d0035403030503100c050041551021f00d40740c403d03d1a0307000d0702c1e021124001c1c0d549001c3c1841d84850120703140100402031640031581e422020014a241081140c0340d1541c2503c900011070b030302a84060f2070840142c030040c552542d550000704c04e0b44040103983d4450a180c04113003e230709074000405545401940e2810301461606001141c024051203041c5c1c102d07104400c003640303000e8480d28101e0b0203400141c04968103001d048000030b01c2158900035640180f10b05050b4580d241080e000107483c100440e8042c109005c2c11068060228030360407084500705410030401c4c41ca9946a26080b8010900300e80d144101c03500c0490301080301a800196501e04d14801e403001ca0040e100c211800000000034455181d1004041006201d01c4011600580d00400d06004a0f81030103003114109082c00c070b0140a030000660301104004040c9070102081240c1d10003070002d004a071701050441803039128000d104074a01d5880b0078006911920840849005682000a48203120642003440010358010b103c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 133303381 1250 133302131 133302149
    0x20a030f060f061d060109061d010e060a030b120105160302030705090306010e01080714030a110307030b0112020414070806011d060c0703031425030302070219030203010c0e031b0d0c030309 83
    0x400a01103501422007c1c0595520780c44650348280d03070f10b101401c1d003d282c00300c0714104110101d41b801c0d00d84030440600040c1d082c544001c42c607d440d4100f0301841e454401000300050703040c81d052100904512010070074111044c94003580e241d0b0f40e801c0070748540c41401c0da40c5416100303550002502c01040e8106034141d4818209842402c1e6540c4400c000d200801a5007940c507400c180001e000094003440384010444014080e00c0090307503661559800258240d01c02c59641040300301007400c615161040054040c2100e003880114180904020301240008140d1410310090555494610f418062501000d02c00207103110740e510000c2c0382c100d0b166140351004030007044901401402c1498980d0a43c0d000f407481c46280b220701c510081c41211412481d4800b541455402c01c079640144c0c03111341010000c1e02f0110030b0002c00c1c0707196106160840b0701c0c56000f5404c114100d2410480c036900070840560b03921248511442ca508200006542c4080d0710600070a1007000b45400010076401100c40c40c22108518 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 133304631 1250 133303381 133303439
    0xb0103060510060912020a15031a04091a0a020d09060e010501080109080f0a090b160308010f050a0b0d0e0a03080f010506030103080d0c020703050304091e0207020a030f060f06 77
    0x6402c00041e01054002c41000c94403040083c001503050300400b0050300e000410052105a403000245c2d00c2e25100740e09500042e84800c0e00e170070049440c0d1000394030000181d070100000407981c4c0340d00c41c440035000429100c42542c0d9000c00c0d4120400c5d0191640c26104d41030801a45c0d01e60705d0721400800042000c4400c0303500303140000800940611441d086685c1000c200352805100c0d8248a4007035118002c804244480c0070350200300b03d10000c1c0506910400008412040c550b81c0c00e0260009505030f014500c150750110082c80907445d1070700000c040740c8007a40141d0f12549145520809040d613440d200d0882c0c401c1403400801e150f4085e04403802041250110741050340c8801c14050780c3e101c240070150800c0c1d030401c9200384030030f00c0c1c1d405220748442501c10b44115036102d580b0541164059401980c05c55100d0900c4500440201c0c4076075880d0518003421480c2c458141e0104030400224440034000074000005503060100c01c1c0c01c0025070380001a01089002c0d00c59640c20f00e40c00340640d6044101c0064 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 133305881 1250 133304631 133304641
    0x18061e031101050f070c03080a120b1c020406120b01030b0705070201020c011b050d050414030f120a1808030a0311160b060d051027030c06021305030a0b01030605 71
    0x506510680380c0012408200303540c0032005541c0d551118103140346089042080102180d0301c00945030166104002c0b0301d948840c03002d0010100440008130100c000c1c901445820940d85004030b429100b801c00e00d0025404003140000b070010b1925610031084856802444410402156180b0341601c0c490250081c654590000c2100c450080c100c0081c00740c0e0014410700074030742c05024045080c01070f40280b08140c50441e0307180d500307002c5103000d020003081000c1400e1103c41c8240410304030704074040c1d0041a1010032020312680d101d030080c142c4071101d030000498250b110320500c9400c407820791006401007640d980303e002c03907030300d510103011240000d160422102e01400c00030201c60b512061080c0c0c41540f5050703621050a4504060490b070351101030412010000754040c03100800320300c0c01c4a030000d400e415a00303240c1940001921580801c184d980c00102c002900f020b070401519030130040c0142ca40443e42090101c80040b900010f5041c420011504104241f251440381641d11074031080c009a120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 133307131 1250 133305881 133305929
    0x20c060717010e040807060603051b030609010e0307060518061302010923040e07120506090606060a0c0b07020a0f05030910050f18060904050f09060603030a0f12061806 74
    0x100b801503441c03406000d801300d408a4011006010110b025070b400048484e0b80740e503070710b14050554941c514190341f080000d03e580c0c9000c1c405141c0c040904002845a0450100c1503070f00c1c1c0c4142c007001007090b680c45000c40e0300601000440881111a00d04403107050404410020391300e80800400c900060036030720085902c4110034404119401620b100ca11640d00b044100800307002c01210308030040c0300d055000030b84021071583c900c481c0c600a2000d09418246902c4950600300c000304400d000745001c110410019034005166160540c010310b02c0360b1240c0301d42004a041520700711000c3e00c580b41c400000c000f1311a0100c020507481c0400c0710300c5464606215015035890107011091003d41c00207125080350965511403e120b400c2c4020400c0346400000400201101d00030b03940d101201c08900304002801608000c91600302c0340850003181043e42c072a50007001107032017803000c00c200003010180d0721025416801c0740014000c03000d00c02c107101d5402d270000401880b0603c511500d414100c0658410307030311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 133308381 1250 133307131 133307177
    0x9030501050c0901120209040b0a060909050901020304050d0c140a1202010b120304120501020d0e0a03020d031407140c0f010c020d0c15110403050304080309041d06070819020c0607 79
    0x70b01a100c1c2180181c417003a003c4029003148000980023500c400c6180100d9441174003140c081c20854403100703810f84c00d0820800032901d000b040c06286030310420520020400005041030b0f0a4601d11b01141a90001e00d00a00180c0d07442f403804401d44a40d0460300200042c03114440d400403041d038020084030052200700005004801812016a0000c01040c4800650802c82e00301040c06440050324020314506020300300c035880d0740803105030b4000300e40100030141d0501203490001c0306440c0034401450280e40400310044040c00d0300c01800001030213149110381c07150aa5042546000a8501050034001018040c01a00c1d200a00601581003d0b42c601400355022551041d00000e901c0800d03100b1030610401460001044070710980140000400998108001d00107403141c0300145407244841b60902040d141f148200d1401b04004c404104200400001d10a5000c41c036440d144c034191f141c0b21130700c40c04400b8000083d280039000003804030800600158240c01a8110303178440a94034201c0348150102c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 133309631 1250 133308381 133308397
    0x8160e09010e0a06080a050106050907081e060a0e070c030311131505040803040609060906031803030903030213090501030210030c021203150603130b1f050409081909030501050c 78
    0x10038644014000003681885031507020740c1601e80001c1c10b54440c0205880d00c1c42c4020215001ea450382414040e0342072200c00300760001100d06003840c072170501c0c00b41101d20000d211403080907100482e00207625540d800c0c0c4003900030070b0010000a00c9060a0000900002042c0001e401007410903a01c0b410010300003003202c24440c2000c90728060103082030800e4020214200a900404c00180000718070030205100600081282d45c032650041803404002420312119903104c0c2040c14503250081e1035500d040c82e2841c1e031540c0d00d4500007a9845139031500382c00900880040022042c1085030109500c03d6a03403140b8180d0780200c8030200c1900381760900720161101c2400010043c0c0281c8458410860041c0186400c4402c01d40481e0070309032100041a0b9a81003101d81c1000d84200365000424801341c540d9490300440c0e02091140050110f69100752402c40350301c03074940620f5940c3c4034402404801c2c0245e80c1c0120201c4101207d901c10740100814128a900084d0781d65440c3c5408150350b01c0242d41225100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 133310881 1250 133309631 133309639
    0x306060703050304020d0b010602160801200307090f08010b01140c07150e10030605040e010603030f1b050726010209090402010507030201020c012a0e030307060b0d06060608160e 78
    0x40103081e501100d20f50000b910032030300b11030860026400070385072160940c0a40700580c01807120300071061030001005107030744c04245a40d00d8451101c201403d00200141c1c010681400c0640e01d07118080115611101644400048020740f1404140c0f6130044d08444c0d511842641c07040760221884801d80064855007003c4291640300540401c640e1310f205c03480800e5030450f41050880c2040e581d01090a415900d9402400203079101010b01107850540f14214641c864040200070b07140c115075010300b15812040322482400803035540ba151010034080c215541d15405400d03030b81c16075540e50b0b6540b01c01c0034442211a040e12000b0600406501c1403090303803052500240100b0700b039201c0d6001515541d0016a080e011950200001921040709005407100395049c040021301c904110039040d4804441240401d080054050419820350b500006550710780d42c003c140010360040a00008031800c4202c50300400710742c14044002506900816544d2050303a0603a4521040008040110b50080f0122501c540c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 133312131 1250 133310881 133310887
    0xc0807061b020d02060d02031e010b07020918160b0c01140c0301030605070521090d02070602100f021b0106030b060604030506072a0803011d01050102030d0f060302060703180506030606 81
    0x15141c4120049140f40c0050b003011315180c0d10390450300990b40300f1120b40081508070501c06810302941c42a0a00604610040c03609180040c1c0c0041c41c0543c02921036a682442c0603208402040280850107281040780c140003140c655420001c00641c210043c24411035180c0303400c090390f4044001c0030b039100d40110000c0074a560f0841e07907144014000076000c4800c2040c2805084110100d15244079003510003a0162090342c5481d9010b03610300301b140d403026021900104010004550005091038901d01490700100f4903000c4070030354400034050344008510341d582e00d0702080b10040d010344c000c9068034045d01c08910169140c00601c641d40c031441c400100240c1c80a13000602051140701640e03000180c03000205022445c0e403c0340c6440404028050b01c031400d001004104a0440403c03030b801710f80644d400380035658500000030b500c9005442c60084984c0e100d80207003580211640c016000380d0360040c61036440d0942810000c1070b50705068a1008080b0700014085a00c0c50f1400540e44602001068545 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 133313381 1250 133312131 133312133
    0x903030d0c1205011d0604230402060f0f0406320d140c09010810080a03050c0a1a07030b030a050c0d020a05030706030e1903050703140d05040c0807061b 67
    0x200410341e2000c101e04110800e0700d0b80b40d0140c000d00641d802409a41140003c079080c0507002d000e0b11002810346881a440c15084401500d21a01c8101c1c100103a04c5103d03810383d44a0020a01904c0b1700704561280310000580c00284181600103041560780942d1080c880902095031102d1007020919031030015410119190580b0304c002c03000b40010040c0c1702011a0804082190b00580c600c141c801004403c1302050301005543c3c44090150b00c0440f03d000c1d001c85615000066441c0e0010038406000c0142c0044c2410321110704000304001b41d40e02c144103201d802d18500082408034419034000001a0625020b4070061a00066501d01650090302501c0040300703040c10022a016800c070100e821040944002900d41c0c1c0070b0064500918891b01c3c04111442e00c44c0300d003403c10100101185200c2d01c50004000032039840b03c290350926a05003001d081034650704000800d00c1c02005416100325040004000400c1400d803144001c8407820710459009548500702a500403004154650400f82b040c0c203010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 133314631 1250 133313381 133313407
    0x130c08060603060f2805160c1e0201050c06070206270d0e04090209040f06050c07030801121e14071d0c0a03060503030f04081509030a0e0f030f010f050705090303 71
    0x1a00b141610605c8022004540c1c0100003403a041640c2e4400e0320354a01c200b1405200580800d0130440c09403518021011880c1c1d5181218400b010481c1d0281104609540459000341e04407403080141c0012030383c1e80c1c80d05400c02907480c601214100750090007003055000b905490700c40e5014407122100504881c44d10400101c921420710481c1c568815220039104002da151103100c030b80618007400364001300800c9410203038280c4902609a820701a010060301001c00c0e803002c15181500c888100074019080581800390888001c80c5040600c01407030b0340950700b0000c4c0700c110034081d40540c9060f40e44956070b501e00300f080040000c2000d400d10060b100000c845482083c002c1000240034100003664580300d40100c0d245410036084241442000101032000136000c20034040d400c01c00c0800521545401c00d441a00ca00840c0702040074407100e1500b0450030340d1524885400b442025003100c1047c4906900b06000e840c2c9071903100c2c94280740c04042030303105101d442101c83d0520003a0046140048041200d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 133315881 1250 133314631 133314661
    0x102160c05040f02182b0303050906011e090b0112050702010203060f0301020405100804022b060b1f031e0c020d080a0b0f2806050703110a0b1b0c06130c0806060306 72
    0xd2030302aa40e40311418080d490404186506c18080d0b58006002c0c83d18071401c925040e010b03080701e18101000c05501c9000f1450300002c1d4140e5400c0003020a211902d4401681d8005403110021040343c14401000f9140e941507000c0d510900c4101c0b81c0704450010801854200d02c510f00500d40c002c01f100480000c0d0501a0381e400f9001403000e41f40c44285100300444003104100307040c642c040348034007400c0350040c0b110a00603c100b00c601251801d84c00b82c0e600909544003180400100181a218050648401134103190032050b000c3c071400038801006403203402034030750030080c020802049000020441c2c044d41032145206014016100b00025502c031001c005810014122800c03944060500103420b122410b0120401030400d900c4d2a625280d132031030060710000401c80e00303201c164003411a00c804200340c0c400c480e0700214015622400b0550b4284104882c0c481c2d00402d94040c4030300b205010307180340340003050712165004440c4a0a2552920700b89500c642c0143c07421a8540c0c84000030070743c2040702a00b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 133317131 1250 133315881 133315909
    0x40e0303061c08070c060f09080c0d05010f0606080a14060d030e030715020703030809011e020a02010f09150c050c030a030203130b07080a1802150c0102160c05040f0218 74
    0xd55034184055950306034a13800a10115407403010700b4030810072550002e040360030501031400c000c0c0d02d0509180c4110356404c1c1c000c6000c0e21508480144e003083c00000c1d03006200c0e683c0450340c1070081c1922072101801c151f40c01e4900f031030105e03d0301d1420340e10b440701d401116020303040081009401c0030311514119200c00d00050171541c507000315040003403a2150360300740b100480300540242010901e14100940782030340c01000d45041d6414007500700e68190704050018a03940d0840c43c016100c3c0d0084004034018000310b500d00c015140b82000344014081507140700703100c1c141401c506020410889400310307880e00403c401c0070099032080c003074120094002c1c0c01866024402e00d0079028699590344903072200b002d0540e00c2c5408601f03041c0a020144860b401544242c010080d00040070003001d90105a90807007640c081800c0500210f211100f00400b07404840d030210041042c40c12100301d600f09400c2403001c0d8420184107a16100000340c070703a01a07000340c8412078030000d03082e101c206050b0148240d03180601c00c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 133318381 1250 133317131 133317169
    0x507031e090b0703090305060f07020c01300b041a010813060906090303140f06030d200106081c020106050a0e0402010306030b090c0109050904080a050c010f060e070e040e030306 78
    0x1c001c5844034041c0054241c0320300a41c1d072080784a146051560600601404414010700001d04109546800050302d110078142841c0130307102d0203a060703c00c038025042541c0d0317102c0100c504445c522111800f80c10900800e00c040303c0c200001108420b944a2012881e02c440b07000c20641030000b02840380c01c1c40070014950041e0000f00c0d22103400d941d080225000b84200b03c0c0071965812144085d071200c900590340c411900300c001d5449041010001e550b8182c28130800003004120303491890300581c10b01a240400d44490000c0c0003040e124100d942d16851344255100360f65100d0f510140d20540305008490440301c01510740b140003414998805200a4001d10a80c1070546680c000030000e030300c2309141d6100301c0e400005031481f100d46400041200b241540054862002041480003080c441e408584444684e8100309948012800145003d8150320354074030308080c03030600005880795450702094031440c000d58450302002c0600f001c120032a030a11401805651082c0001034150508072031300e20005c01004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 133319631 1250 133318381 133318397
    0xc030907050a0e073e100c09060215010501120c02010e15060a0803030c030f0711030706062d05120c0a0f05010807080f0f060a050409061b0507031e 65
    0x4010400e002d0040d0f10420b40d2100031020480255400410301c04001c540c2140c3d01c2c800070b45001d01c600c070012407180100d210418040e00700355070402008204428000c1c00303030034046c0c4200c004c006441466244500c0000d801407258801140342920880760503200c0584691444040c4810300400500551200300113540d40d502040c0010303041002610407004070404880e2061502d501449070604c03035a800358455920500038046210f44003025a54000911540340e002135803500c1003264000200b2040c2132a90100098607000d02516805c050159444105c200d44045081c4c1c40020092120002140942d59009801c2c001c2c2e00d0455600100c0c000c5003000c541c403403690380300000d4030075030180e1020742404ca02d038204001558104031000d80c0801c0300d080224042c5400f041c0e80098400c01880d1000c401c00060025010b90382d0031a4507400f400b40940b00304421012032030040000c12a8050b036a202000c5601c0c841c401c60710490448114691682d00d50190041000395007034901000c90014003031050312 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 133320881 1250 133319631 133319639
    0xa05090d0809151207180815040201090801060602060f06060405060d05060103051e0403030c0e0a08031c14040605040c090507082a07030806040207021c150b091518090a020909150c030907 82
    0x8014500320403203040e1500c034007409c16100150550302680e01c46001e90341004010031401d600030880c00d42c803e082d80c088211540d140b0000410a00c00d60b0041580401c1c08101c4030a100001d84c003d6100b40801e8030200590340755088064500903a0030792098100a01d500040e001a20a8010582c3e81c002c0c0d060600c00c507440b040c000340d046201038005460603800401d00307a91a01582c10888041000500100060b2800c144100c10309a001070014145a84803008107007004421031510000303203008107081007d070804002c0102100002d030307403041000a0820751521411049c5440d800c08540f41a00b503407402042c0e075026103600c10018800c80c1e01c203609200040141e200c00301903420000d0140302c0b220340d0301410b103010700d1041c0400b9040f0a0a6252019103003c640300e40307000681080c0b0f0021030445c2440c02c2000520a0300041082ca05420100024000301090002e8600516031017225041126503400c000300e80d4810000312800c245c4d80d65a0081002090018011604503034454103580b40c0c940c039 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 133322131 1250 133320881 133320883
    0x110106090608100f020c0703031103040e07270501020c040c110d11070e090304090515150c19020604060804020102070909081309090f080a05090d08091512071808 71
    0x402c0d88000203c0e0040c0691000d040340034402e054105544200443c00c00c03100f01c0d140350b99180180001024031603080040b00c2d0100c420002d640080544042c41000c600d4952802455015000200c4a400c05488003892082411801c0c520030360301c0603401801d6070170a110400000d0074040d24600148a03140d00c044907030340820b0040c2c00e4042400e4407202d003901010040c0300e18007030a030741c080924070f90144180440004044119802ca800c002c0d00401c15885840300100340c04043c0c20303800d900242015030025008507041c0501035401c044801c0c1d5422514a500c0300d40c20004441000754020701c05c10061140b41c0c011b14495400c40d0061044031181511a021081107a401d5501036a10b19404105201060310f80d000c910080c0440b80c4041c403040c01155100d8403c2c4884480040c0250b602080d10300c051881402560080f010051a80540d05410b0404040d140d010011250091100c10708000304c1d104110100c400740b2668841d002c00940e02c4900480c0c00b220030a9080f040c20781d05070400107003064 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 133323381 1250 133322131 133322141
    0x13b0f030307050d09120507051003020f03070e0f010903030c12020c060c06220209040b0601050904022209060e0a02070f02040f1418031803030c07032003010216020111010609 77
    0x3c450401404d840c00a002c0203040a219640290414080c102d030040006a01050080c11150107a400070072107481004182c005e03000d04c0c3c951000c41c24003c42004000d945c03100381400703a150180e4244041e0b101100c01151084813600025012580b188941c01c00103da812540c80b0481d05881502c51240c000c1001800b144d00038503000800d544a8420321040c00c10b80d140c0413020610340a1402d2031200c0540c049001e00c0310080c030152107244841c0c00110143d01680889102c0e2200520456940003001e980703000e080610744001c4080030a203800030403081c1540c0b03d1a4240c0382c0540c0400000d54800300044040d42c0462821a98120300700c1c0c03090f005171240c1c0a0303024070402006010801000b4442d414101100042c00c0700141c80f80c11401402d10355000c0100e400c0c03801d40360340d01081c0e00ca880c40803c3c0f9501c11032800704494854504000180042c1c2040300e0241c01d00d03114491080d49448041500382c0c010344001c00ca1081b0405580c8005600620004c40744c49908000440d030107503a8040f5008581b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 133324631 1250 133323381 133323383
    0x1140a14070c031e0515011503020d140c13050312220308160201030f090803010527010b0406020708010b0105090d0f02030f01020307020c03060411060f120a0902013b0f030307 77
    0x40014804404000b03084c032040003012441b03d001d048a601d00a0b506140e4401080c90805142d070000300c00782001b146402c040545082d5510350411410110001a442da101252980e00499115400705191402090355804801c00351850b9040107001d00080c0090409078031004178040e000e81c400800140c0381c4000d8540488040d4030749448089900014090310320500c42088405e05d0003014400203071012080d2810748109450b10f9402e100a84c48004291b546150405110700842d00005290b80b080e8004200307403240b5030300b40c0710002e90b0b6941941c26075001c0040d01c0d01141080c001a0b0041c201808014402405403020b4041112113401207424804060300b040c485c4d0350000304000d0815010491499100400d4006003030601e4542c9030107000151a08a003445500000750380304201624030140c0b00f0084500d1500c04042c20b02050280007880c4c0303001c0803030100e840a85290050810462075086001c414140014071074982e00c1030150503582c124000358031101540f00c1500c00c0c1c8040000d49011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 133325881 1250 133324631 133324673
    0x50a09080106080a2d11150d020406030e070602030706050601140a0903030e180a05040f0b010e0f0a0608060f040507090c090504050a020703021209041b0c0201140a14070c03 76
    0xa822410705028a2040240030030300c106040d98401c5e408034240a00062040d048039052100240c0e40c00000d0340c00c464040144c0741e1220200300310030200150b0340248119805c54408102c00241284d04a46811075403144a015800c14000400071844a0b08010381c060814508034030010307111514002c194124480d1000000c00b440380510070950405900c4c004041c040341c1a4110041c039451113401900010200c2105076290f50115040041941ca244145a4040c800710007542e120902c503001c000c401c452040da0000413102162200c2c0c09445075100755680c0300c02600c0305a480c0d030b201180ca200049c10403070b0b49104240000400d00130354440d001600b002d69489503069442c00e000c100a032100078201814aa10404c424800240c0000c3d000940c00c0b07038501d50070b4456020900140c000d001c0000c8074800c003091015841e10580d07000072000b803024803d8030307106d0440c082d081504c04503002c0d1802c0040400c25a240d040da40404c8580600f500e24419550014803d032a55640004900131b00400180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 133327131 1250 133325881 133325893
    0x711010b06070302031b010203130318031a070e090402060909040f0503030c04091b05070f1110030b0405090f1b060c01020a0509181501031a0d0b150301050c070201050a0908010608 79
    0x2003400400306d00516001c038074020b5046041c0340e9141c5509170722001d002018400c0f902c180400d209080703081d8100940d0007082c8010907540d041181505c141088401200040688049146915100d101d85000d107070080c3c110313810b040c00203050052a45000d041515110384c542c0c02d2000180701000154480c40410340b081d6207541c40c04101e4803c2d5406e8101c03107030203018440080440280c0c031009899005070400d42c00e03c1c1d540814203004105030010b84080380c0125407541c150070b48503099008000b41da036059904121683c0c070503030700a44a02c107030702c11505290819a07030200001070036145840500d800030211071619406044240c22a80050100c8011130408144403080f813a0401c840505024851044800780c9420750240700e08401c0e6502141c189075440380130361040980007986107080c5101402c5030319a0000d40c00c0c0304004400031a00f4010340003e50724503403814181809214040d0182c2c080040c01c0508540c01580c00b504070307600b41f40420103903d8000500e4030f424010100102041005800f03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 133328381 1250 133327131 133327147
    0x40f02180702010b0a050105070503030c0318030406030c1409090a11250c051206060d06060e09060a0b0301021e0a0e100c051204062c190503060f0f0711010b0607030203 74
    0x5076022070381d1b00c080e0602606000e1400491004400c590340442080d0700d06031b595032050344080e030829801104520a1002040109910390140d0140580700301c1e0f0340b00d035092034130f45440440c581d10a618026070008078207008078109007855009007090000e4000841d0818032a4910b0000b820000080d1484d65a0a10004418003c40305110340c041c04091300c51a508084200ea81c55132000301400a501032070a1079560707820300c5032a600107005800c0c0400d00e100d803030030b00b006915035602082c2c401520f66458a43d249050b89014422518250300d0080c2c1c840c0880c0560080710115080b00150b50244503550716640415520881010407403503a030b44801e01c4450180c04c10f5071808110680d07201034240300304403e0003425044030205090703a0280005007407158209504075400166040b11316082000001c0c010a02200c1800c00002d0300c1e426002c980040c1c0d107101c5181c54000381510a202107101c8100820261031080341c00d56508481c0e00c00128500200a01003441548500d40950058001080c841 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 133329631 1250 133328381 133328389
    0x311070506100e070207140a120b19180f02131506030e0316021011100e16060c0209090a1205031f0302030d03090c08030705150901090b040f02180702010b 68
    0x3406081c14011844c0c034042e01c0280d5204058082e0703481e020480f20040400f6a6041500c00c060007081140488191452802420861060302d0300d400302c0344555260120005140b0802c000c0c203006444044000ca003036225031182c403598600680e00490207005188500000c1d0203100c00150070b8030303235189042e49003140040c1250041154880c458104000303245c1e00c260449075044205030110340441c101c03100c440050300c0a88051250500b1070280070760505402520b0b90204841c108031600341c40c41501c84004030103030941d13030303000b01c2010810900c514005070400014040d8012001d40c2241c1403440e030398440500e603191407514140050800403c012640d003904407042c03a0b45980e220f1445016055500007900e07a5402603002c0f082503a01e011800502410a882d1001800341c20103803a41c3d04c855042071a1114504102001108956800b00300017000510078004119041040c0511075281c42e602e80f00004c8601d007040e6403013800769041d1110390b81c1080c600e40c01002250000140c203000c1030184 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 133330881 1250 133329631 133329661
    0x15161e090f0608010302030c0f0f04061401090806220f08030a1a040e0d0503070210110d06061d010509121b030d05070512070201030e07030305070c0b07110f010311070506 75
    0x84010000c007480101700685000a030114809402c681e240030b040030180220b51100f03841c90407954024188400014682100354041e81814003c1c0d0f01c0c0c482e100e4942611390ba0304c1a0546000415800c7c03040c1d290380d182109088400580d109a08208108820740c444805a42054038100320080d82d4007001c10704000020b040072080c00c0290380900600660b85d030215252a21714541c017043c80030010000342d01503c00d1040b03903440e5034040c000304402045940107100e10740107080e111032018607050000c40e00c80d024841169444107011640a0200c2c6803000444241d040b1340500394101a240d0344014000401b4010f0346a01000c124203400722408050800d85011941c040c03803000d100c404c21820020500215200061850070140150790741d045100481c000c03d040f01041d811800746000200802d58020018010203000389201c40c0b02d2601d40c07401c8411445040c030b0043c01421400070f0303c0c049060084404603201414140050811071b013a15107142948903540440c3c49403c901d040001e42e103000008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 133332131 1250 133330881 133330889
    0x90d0306050303070b06150720040e1923100c030209100c0809040204030317060406120b040c0503030c0109060f0c0503190e0d091715161e090f 63
    0x24001185001c02194076881450750140c01030b441140011aa521800c0034810340001d1f01084994a200c1820900440000c004030b094206184108181c01803400d8080c0100c5240c90b6009407604400c0310003048a807034a1503001f22030102c00c0c0c04080020000c0e5034607415809204a0103002000c281411100407110344400500625105028951003501c54211618903403000d1f0030708808032600341c1020f04070790041c1416564800c0c0005004030030540c1c001d16410310604950700303903035072612020108401e4916500407100c0c10405215038101045d601d800207a0400c0c09041c103c4002c50300c5a0110381150f20910303010706103a4644840004101840c41100c0d00c44101800070042c0c0a6034220003015488050031681d10088012030703140311060741d5440400c1c64a0b20404070762500d003d907240039011184e540328031504c803425807180312162200425280e85081c030780048a0343d20703603030703c4120f59081c500d03071501800b04280e541e03145044c04402c41403e45403038500e032201040c651600c805141d040b211504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 133333381 1250 133332131 133332137
    0x7050c0d030918060b0f09010504120c030c09050c030f04020f030d05041502011401140a090501180f0b01020a060c02070e010308041e0f05040f0b0423011203120c050405060a0305090d 80
    0x40c20040d05d00204141e0302034030311704020155074131085001201d0b42e0007613420000c000b0716a10425001c0040c2a00e4440c204c0388103c1d0b42c20441991400c60000701c43c003c4070b074548211820000680007403a170b801025441440103050350030098118010034a000c900400410100d68001801c2c0700140100300c1a20b00e0b2138051009104801103250603104c00320701072003800040d41215255070140d5a80340100b0018000c0541c04204545c2d40d000b0451060f001011980c00ea2861b2031940c1d100c600d250700440d01c07692410380003440501050b54850780140303004ae0b0040118081c921010840701c8019030031a0085004004d000c1e01c940c2002001e800014003608a140b03c40440d040810419030100321000485104132000207a1a1a40d0b0105010740788043c01d1a600500e032410045002c64403108100c0313841165594207140340e807140d640ea402c10514040140c040313048064202c0d502c201d80e1700079070001002440d000f403d01d03a440700407981c079412000721007010984450030000002410855001c040e80146 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 133334631 1250 133333381 133333391
    0x9020708120a0e060604061d0a091a070f091202120c0307080f010501080d020a0303050705040506070f050f0c060f0c070915060f0203030601051918061d060414010507050c0d030918 79
    0x1b400174000c2c599448e4005031045007900010420041544040d90481d0041445000b03952400039846e1005001c070b40b41000b0030010181e40c2c0329548a8031022040c0c035005a10159185029020007154041c80e541d00d03c12842040c240c01c107240c509200103001082800c00506035100c907613203404d080d6401600b0404480d4890b0b0394201c0307080e07800500c000c0800d0300350600117400c4d11028412507851095802003034101d0000075001080011004100140f03d001d42c0913a0a611505040983ca0310390101509902000c20700178a04020700381d0b17009203140c040c607100301c6039207a50350308000b015076503d00000581c82007020307020071a80c1c0d000518490b40450b00e101851561404d43c00107070007801000f02070300844000848038820580946040741e400980502d000100c03640c0c9004c014030744071030998040e40342d903080780181e401400c00030192001e5504e411240e8825451181c01150b02c0e0b000030354141e03110300c6124499240c68440020380000e01d4029590940300b00d040ca40551043c400c5100c101704a02e01e80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 133335881 1250 133334631 133334639
    0x20406090207110d1109041a0f0f1006090b1b0a0b0609090a0f0605150d150e010501031a070513030c0521060402010809030417010c08010503070305030409020708120a0e06060406 78
    0x20a9100c0d1320700c81202e06c0740c00ca031903606024070603040a80c0124035440443c0f003841103003603520246521038a44200030489554130401c80401c0254148603610105521103420301c01510950003074202d0b6288500a03020a40710144a24034051100c0710580788425800e043c410f00742040014554403002020041c030002c801507403445c1c0140e00740321000d40301a90b98408140e03178642424a00f020620020301c12000c4d5641828118806804503140045c000c0c545280080e040030103020741c03070480350000052041488099480002e00800800c000c08008082203c1a681c6100c5100800070f180100907031070420f8103007414020071802d0700c04001002400c0040d40c81d54804001102035200e98203103010607040d01c441e0b0300f01d031035070203241c100725142043d01d250b090051105511051030021260b44d1000d1a99880c0103154982c9400d010182890b00700700002d000805481e0000c214042c896100d00340361009001c66919200001e940704c01ba11525881d9101005104100d503e8020400301d038100412450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 133337131 1250 133335881 133335893
    0x203190309030b1305030a030e19021804060e0a060204080106050604030807060b03030d090605060301050c03071d060f1204060b0f030706140c0601030302160608100501030f0603020406090207110d 86
    0x510004068010620010b852440450102c04d8607a03404002c17a03840780a0107030702034007402c481045080745100f10702000802c20388910804203916009010040b41e9641050300b0b84844400420035a0407603252900e60901010401c0f4410905004100050300c5070304000c2e005081d14296405a03104074810311007440032482030001c881c1166440140025000e000c407000c20300358080c13219060401d5252106007810701c803250304440c1c89428120000c11007a56101c044119500041d0703045400143e40000080940a02c14900e04a41f18028900c030f05020583ca40d0507056404440807603207101c00d0000713010070441d1600400009102c203e449811036441800030942d244100c0c0309403001c1200c00008a00b400015108940c9058a1001550102d41e1241806551040942081800540150300c0003e54a1242c3c000c540112039884202140ea0300c1c02004402402c40085225400e69565030b00100503511882a5002818004005a01d03403445042414a100e1181022401440307a800c0b18000a10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 133338381 1250 133337131 133337147
    0x9030a090b180105180a0b070606050402040605220b030424050417070f060513030206070806030d030b0f03070303020f0705031c0507030903062a0509010c02060901050c070e0402031903 81
    0x140030b180030350b116001190302d41c14114817103603140d030040a00000070a075146c03000014440715010308018000300d9039039414002203202d1445001d00045c07042c002480c0d10f00b4202c0120380c2c0c40000a500385802500c9007540c1d1010340c4240c400303d541300202141c0d880b003400106084002030280a108024524007511081e07001040741908150074040054101c0821040107980304425800c107808020525101ca044449084101c900398054401e40000403210f520800015114200280c09443c04c0d041030602500600503002086610002c1c01c002c1000382c2d1820060500114020b17401000414040c6e8152810001503801050103a0080000d103800b903003200c10151444801858581d80c0c0c0c041c1410111544003a641008261509205264114414a042c4a01c1e417408008418a8030066400191103511400001d540810507060002000d854001d0140c00442c40c1810810301d4500810078050500420390410503000e07500381c0170302007981003c03c0010051615003114185158540c3c0780a80801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 133339631 1250 133338381 133338427
    0x201030c09090501170606100c0b0612030a030c1e0518030a0f03030203070f030b0306191b0c0c060201050907090905070905151318060f0b0909030a090b 67
    0x240d120845220054440d803000c07801445000010000395071225949000051020310200091040c0c4011451514203800c201a1030802d6482c0c90003c01c00503581e4510b0610014042a400400b01340c0c4624038810500041c0f4500420f568002851284000050040501200000f4403030303414001800d407440d084401c56800c1e01030302c45404008401c4800086c070381007243c8001411000003103a80d00406400d500a1802115035403201040080412400c90444409050684d0306138030480c041092410b99060f151200f00b030903540407400c440581c1c501425010349500e0700d00000d01003248101070014000d007220203045580b0003881203040000c110740c3d40d11030b2400399a0b0038035504d01e050300402c40100110030040402090500032880c001c090000c4520042c2c440601800b2034254110030300c1c1103072103000004c01d0440040c1d22100031075180c40380282003030004541074903a00c4000c0e01c8c003542c80410306c07886091050002c40da04c00d050000100200080c1e8402251682d051207070a0240d0301054154010b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 133340881 1250 133339631 133339637
    0x213020409141810020309160b04030b070c02010906050306010e0402030112060b030a030c0201110304270b120303011a07150203041e03140c0307140705010201060501020f030a0302090303130b0304030f08060d0201 93
    0x1c0c1d07d038480d80a00f0b010303003003200141c01c51520000040b0885810040c1084030300a6801c11000e80e80c60605036544a80e54000030b00044001d581032001b00c0c014030241d60480c2040c0362000e1000460404102280d01c207030084500c80741e0200c038400802005000e42c502c0624290702a00e040d50040e5009000da15180c64000d05000003000c00e000d90300c0c1d042055400620216589040e8182400031341980022400c00d66100c5600b00f81500d56541064002128034250310801103285a00c0d0002c400c0d50300740040302484030600100000008182100540e18986446400c0169241000d150002a004040c04e03240306500460400c20003007500840006103161040014503a903201008402c2d00b944100b040c003d0141f101c0100c034030180c55000031030509440342a0000c0210075201c00041e659056400e1804580ea070040103413000d55480703074000c1e18400308080d04681c04c02502c0f90554030074140c103400c1038824510100070441819400444d102c02846a03041260b02c2e42400310110b103801a1402c0042c1c14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 133342131 1250 133340881 133340887
    0x90305070501080c0910021e0a1518051b040c050901020a060b040608030d141e0a0b0103091a0105030c0315010504020702122a040c08130305160b09070b090a030f021302040914181002 80
    0x381c482f40741202008a6011041d500c40081c501ca0f42c61410a5000f840b0f40154509030501c20000e029200302d925001c0c0580007020341d00d60035947c810287c60040402d6411545441000620510401c05000103400090002c0307540104120250820980186804030103103100e00c2000012020500180d0061440130002c1920415a401070b40504a605002030921611410103100c0034034240445040e42d02c114161811842000209552400150003103042c0c9840d0030010026454660300030076141d44050300f00601000e600b040da0703084c960710070315802c044c4025a5042030040e40440414602403000c440400641d00c0402009100b854010881e5440d103503000c0801003414082d60990b10100900d0303a13440b881e9852850099003a545c26154413000b031013a40300204544800a09407080c0c1c803c050400c07a1642d2450b110490043d440f0042643c026062580e10080001c45000500140100c03d074085459081600b020101c01001805e81103000c60f031600c8079030b4685001ca86460080d180c0c203805a2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 133343381 1250 133342131 133342151
    0x60f0324090f0323030108030702100807020d0e13020c030301090c0c0312051503060106050901110307020904020105070f0503030f16030c1b1b08010504050d090305070501080c0910021e0a15 83
    0x51020141000402c4c1d01d01d020000182141000004040c01c40c0f081d00c0c03103908004655410383c1d55001c25510700015811124480442c40d229115a41181030010040340b51b48101030298000c82c0c0c001c2024140741e800010052020070a80d0150200b41030003458010b021900d90348005180b940103545414029844d070011582c0507002140d65000e00c2c1004040e44c5155940d0300018040c1c2d444200120301041e04001e1441048401005540358690080d085c03034840c4c0d1f103503401107075a640310700e50480c1c2c0d1031a61214080414401c20155105010701c0340465107a040400310207080c80041040d140406d41000800c0f0b0703805a000d4000504041880500150003445291082403c1e85140b1840000d540001c4002104001504510f008600800a9405a040d01442101d04540900010f00700d503000c10300c10055548940c401c1b55000003210032181c28180e0010004800410010401e070043c0e00441d01c1044007a4003c041c4426148100020700b004045683c5840c0030000e0a0f903c50921540c07034660403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 133344631 1250 133343381 133343417
    0xe1b09030a06140703140108030708070302030d050103030f080906091507140c030318030304030507120306032004060b04060e1005090d08120601050708071401060f0324090f03 77
    0x1c07a00e40e01c070790140010350500101d00200328049400b50006802c183e2402a1026103d0b846030580340004061841d020300394507000740c0c990140100302c085101c2080858020710662084c140030354440d90700c004181c0c140d480b00078020400a045030038542c100f9402d0211030440054007400704101e0001710001a0788a0000382c6002402000102d0303c9000003842c0410000040b009611641003800c3ea42c0320a40e0305442182d581c0000c07034005021036410420a000f260241c08000c040740914a00421019126507400c940204600100703210f0810407000440706107003501401e07019122021815003082e103003081c0100b2054140350600e0099000007540e09140307101c1c0c0b04845230300c003001e0030502017443c0c030345801d550651101d030640008030f10140119500c0d40c45903080340d0895411000700e9050a07220f80310701d042c0486a034000d008642d40c5090000d9925080c2070910010350040001040c6401d001c82c50361400242e040c0604155841d200d581c000188030741c90a140c0c2c0c95010301c1c0c2056147c4101d0420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 133345881 1250 133344631 133344643
    0x30c02160305060906090708150a0204090f051501080601020c12010603050d0503011806060504051c14101409030f0a0504050307030c170d08010b070501020f070f0c0e1b0903 76
    0x1222401080300408801e00034005829030080500c0130481ea1180ea070080305544552050203800c11540081c48442e450a0b521850560800c282030801803038140d41d8059042180c0c03c01840484541e1140104144000000b01d00060550300b070902e02928940b600000391511400d0380d00b14802c4115a101c0000c41000b540050059a40001110541c407c0e80c01d002c0d05681091081c0000702903c6035005010007641c0c01098112402a2030781410075041900f0460581504030754074040d602c4404504000c11520390000c803094464802400d1220315240420095078400c944c0c2d00c1d0580301c48002c2c0f003100e0a000040319581701c14003200b19102d5204c41e2040b10544119441141c0c1841400004401d21041d0842e03d0f007100c203003000e20341c003190001c0c041035200c50b90a4103900200d80004010408905035034001c0c102c0d50701c44d4000514041100c0d9001c5580c3c0c0200400b9680880100d140d0010032015040c450003908050300910041d1401c081c0d044880d105109030f603418801d01048802030b80c1c40030024 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 133347131 1250 133345881 133345903
    0x604060c0f0b0a050415110f0a0507052a0a0e010603090302030403060501060513151d0303070209010b0c0d1d0d2d06060b04060203091c0c0e0402012d030c02 69
    0x2036034549051207502000a458155416552545101081c819050152055000c80c0c1d030742c8140c25081c03403103007898234949800204600d42801410800c0780d001031001d10121040c40d4005035a007a0040e940070344100c901180c2d4985501409a10b082802125444188141100c00501d40410002c0440c9001c81c11400b8603071008252508210020880a4000c8041d02c65840808016080710380c0d2542c4c3e240f2109076a10b64140031400d003130040300302c071542c00c10040c07860000a002c0324070f021001c2d07000c070390000c1090b48030300d84402d000b156134426010180102100102d45280c4043c440c12806d10070380b040f003840d034900340c8541c012114200c20400c0046064840742d001f11101c0d412070b050380452241b031850174002111440d00d020030125403a45a031003524280c8046070300441c2030000c090300b809450000c0b110406051b15544c02484c0010f8980817885c800b41039a2010000c0c2402c280c4009008144c80380a0340111034480803216814141248460b00c1c0010306180c00b04a44801c00820382c00d204178660 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 133348381 1250 133347131 133347143
    0xe0f070e014a06041404030e01111203041203020702150306190905042307121401050702100501050301060506030c1602150918010602030406050315041505030c040603020604060c0f 79
    0x468001d4142d038118407070b0042c4856844032196a03c0c081040b0440340070200d10501c8403800004580407074480c03004800b0701030043c10203649509015006600d015160820b0f441420b100104110030014050908070702c08100c0d0405600300300c0700c1d90000b50b070142480c04d07800368000c004c800549296502045407221f044a03c00540301281c8131841400030701422541690310401646040e510f4041c1d54041280186200b00904080350903d0f060040750400c040741a0340e03030407500b0415001c4c0c074401c3c89124003c8400360010a450500c1c4c0024100382c9005038040c6100340d241c00402c004a848130400c980e40000b081c614a41e480180c40040080d10039400d04c0039401c440b800116489822140008003484502101d08456000b03909000c0d81a4100900840005070800c3c8000c006c114001d6015581082c421a81a4001d00c401c0020408507a5160206d040b001c0d0001c0c0100018103061008094440e803e0f281880058110b8000c18a18400c0303101c0e0608121091660109100b800201e003107401e64020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 133349631 1250 133348381 133348469
    0x510030b04050a0606110c0a05130b10170a0501061202070f0f0b180102030103110f0109080d020105010e060d0f1106040b120912031009051306050a0e0f070e01 70
    0x261000d0020203003805064040f640e1b9658014001000003480715620b28004d10920400c0c3c1428144585000748040c60300850f40c5444903110160740b07800081c0311440442c0d544480760401210a150002d50103000003100c00d18140040c000c40c7e90001c8000120510a100940d8034282490b00000c521900c66015191541602e0303010f0410901c0384400d0701485c0042c20265000f003c0d864030500f01e10003840010724070001d00391941850309254058000903401410142d140b160303035581c4e1504010010760765100603552a0700500074048e400401581024090b110201044c0507681d4880c900c03010220050540c030700b102401c1074541c0c0c03030f1001c07940504070380d0310b0140e19615051501a2101c0058594202030300070000901051013404096911807443c2c000041401e91810700c440c0c0042c03601410000d00d40311220b00b0000440e40b01c0c022507025408000c000030700305100c08103c509104020b2100c20285d04044004c02c1100c1c1d03160032241c1910a8843c41030341c030700403014000c140b000b4400c0814500d2980b403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 133350881 1250 133349631 133349641
    0xd0309080d0c02030c03010209090a0b060403120f02010501060905030c010822060e0706020d1d04060b120a15050d060e030c0a0309090c030603020604260601170c0303130510030b0405 80
    0x2803405000a4400e501721540780b44400c042500f80e0240280041d00440c0c11000625507103042d800070702e5210300141081d40b074035459460b034030b00c00c039001059500403482c3c030000c240c0c0d590380c24407034030f401000c0300d150824441d400e000010752a0881042c4007810800b4001c0070504e240e040d00c0c1c0440c42c101981c1702118a0140a19000000d0440c081012a040c003c02000207404c40c0041038012a00b07056075290001c0c61404020030010340136050515811540d04c14001c00da072181103009000400700f0030a00e0106180c250302b003c017175545801d8803c01c0d00008200800403500c88a1001e61200c0c0d0110700856000891102d86180d0b01580041000b24032400480d007044c590000307a0710040e20b040368014048641d610f5019429a14107110094014808010401440810049110503050035040b0b001c580700d995001c0d1480c05100b0781105031601c0c8811300740d40845a0420803d03070082030680155051000d40060010001d4081c400c05004602000120b90998401d41c001c000c507201c02041041a4208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 133352131 1250 133350881 133350887
    0x7060203062d0111060105010206130303060302030601030f0b06030c01050910030b0d030807020601060315060309060216060507110a050a06051305010203090312061815010c02060c01020306011b0b060d0309080d 92
    0x3010301c02c180410480d001d101441038020038154182da170127800401140e1520b004048075141f0211068081658801c40840165006d000030b90003940900a0381c146103c0302d0a000009600140c20148030358801e1030151640e90300082603490200e0100d98100d4644400d41059000e803c1902001c3e0b444000d03603015008041d000001c841c0a900c00e5800c40d00b41e6a200c040036401ca91f24540100545650b44004100d074501c05c0d0001064182720300800740c1844a10341e0018140d4050302030803075140307440d601040b040c940e004515180102c07128009000324045915159164840c0780340107440c49407141c5c0010103840b50303002801c1010794010021566442c1c40d40301d07951242c210003141c101d624480c8002c0b555a02d000c1e2040c1c2141c18105510758015203800c0440100d804100c001607060142e25160134015980301e10182c0700041c10400050798030314210300010b043e503080604420a407002000400003007111800095131000e41616070190800180c102075424110b181d04c0301020748210400014080d0b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 133353381 1250 133352131 133352209
    0x80a110318010606090806040b1e040c05040b0a03020a0b2a031201060801180c0219110406051c06020a0c02040203090d0909020c1908090301050f071d060706020306 72
    0x300a0000f000510385544040318000307094030a2402175407001c00070801040c44511202d410810310101d000f0f440400d2001120515030480b070550b4040c0c1c14807070030042d5040034020001400400c46070224213500319800210010707524001c00c50a04404960b038404012042c485c00c07924008000c80683c06074989030766540d05da1081103401900044a0000282d103070007140c0780381c140c945003004e01c5c840c1103078114103000a002c084800720442c4154064114284507035030041c200140103501d00c1804001c8082400309841c85984114065500300c0120042d6034090702c1c1c1c41c0034a0345c0c400b90260703458040f041e080340c548120490180d4894400000d114445100007a550200c208548454a146079503e61000882c09003c5a16032107400c200030010110042089410740c0a204404260516034000042401c459040312203580410100e028400056084615010060b20405010307007404079180c085245805100b500900482d0044085482952003500c20100b141a0314000780d02d520314183c00d59078000e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 133354631 1250 133353381 133353421
    0x6150e0d08040b0d18120503090c1002030c0f060702071a040e0f01080f0f07090c11030712020f0a02030d03050406091208160c0506010b09060708030906240a0501080a1103 75
    0x54a0985c0104982640120a08606070001c44c1c54680c03031900c40c03040d1081d9000405107240c81c0121501407020703a0343d404003240440004d03401075444440381c1d5005071400507000c522a1955020304204200c20790b00003404000c0e030b070f05c82c0002e0102854203c1840203d0045810181e030074801c21040000000c1500c91640c100c2c1c2a41080342c042c02407030303115643c403031704240081c0e0b00d80c3e001a40280130480d8250465102292585000340e074800034406a5411500301c15401c80b00700c0720041000950940c10401c0c131000300b20070000340480e50b8050b0f00280e03079003080340b14500916441e40005002d0240d994403032080a50414420102520222401000342c5030031125041550f0000c840d40e41c40324451180190819808802042c2c26402c085400e200e03900071242840d4054000c01c211000103900501550280c54032400031700030b0782000c11801e241c00b08580d41d82c2c92007440c03401440ca415034400c5496002c803007083c02c080d469522511008400380c980140180d8080200005200c400740f18072003600d05070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 133355881 1250 133354631 133354657
    0x212030c01020c1f200a090513090302071a0711060c0d09051e030615120d0f0206070309050d080405120403110a120b04080a18030506090601080106150e0d08040b 71
    0x4488120100713088500d0020040c0b0816107140d4202d00984100c80240503429040c01e080010703640d2600003940200065510210880d202e1000034100740d01003120a01802d078200019100c40e4180503195858080c084002d00240d80300941881103480d0a4220748460301e44400360785c46007450501c043d00d03241c1c1070302c29180201401403500a0800c0710340c02015a4010007005041d82c2d4071240540301d01101c41c40801584154603c0c1d035903400314810820312502ca26039031224603900c45580406810420010b08001c141810640080002140440d50f407800a800e4200034180e40c9171414020301e444024100d00301010750026001c010302803440300c00d2031030001c120307245008281c0341c080f10340786001912001049407001c3c1c00480c000034148000746c030051040303180c02e62a028450b012644c40a01552040e074560f00b00c102400116403040c0400b5025007140c10081c00914036014072550a120421008002c008202410b40c02030303a0707650300024880ba0040341c1c690b02c85488006040855000885000c00c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 133357131 1250 133355881 133355923
    0x40803030f07020d0e0f151b190f020d17040609140409020a150c050102070b0702010b030f0c0f01050f040b090a08010c0c0204020d090501050a0f0f060b03040212030c01020c 76
    0x40c40d1000a128420a00e07913030f0303045c4441d559030701030001e06526102141d50000c1e80708071840485100c2c10240000f0000746401e01380300d011250345e0a041c102d01c00c00d402140e81070883d012022a400902040c607081c0d050300c20206a40340d81c14042008200958000307144080010005030003584868024290b402980d46010320a800c00d00b000b044610078503009404c80c02c0c15008102d8031030400000c2c0b45402d05414042c004220640da5035013203030300540c0b08444040343e207000d02c03014940c24402d40143c81c005034018003a6146800d400313580c83c0300ea24213440c400d51048401e840305910500c2555051101000c407103031641d40390200204a50000240c00d40928000c5c6400603800d4814010111003007420380720389007841a40d40178000694080c030000c04003651994071000c00113a003441014451001e0550004042e1700d113568000594400c1c01d10f0030541800e01e4014041c40c0da0720401c59401503030441d0b20b0180f00a650701080d066014920385110705d0b510104445581000101c1c1c20006c140e400310000700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 133358381 1250 133357131 133357141
    0x9040c140a2303120c0a0b070503092e06090c020606060f090103090f02060a0201050a15050105030c090a1e15030507050306040e100c030e061e070302130b040803030f 73
    0xc0c011007180b2481c0c640c0c00c0420035989201c01118094188a040602036402d08541c0640307210740740d40504241c01055010f82e06500c14082c06c0c910803a0030841e20b1070202c4c82c608281821039039640f006100d682c100002804d480151800342c0da44c17496416841d1209100c600c2d86c0d03906050040c1840c15400026000f07120001d029480c0c0b1030308035410034105c140018108288440110000c06810a04484162000d840000560354000140c1801c804990000c00c1600e0805240340c280c40c03036441141d01c0800000e100303100b0780c0e8006003500d9218042c1d025494954542200040105405e40d1106e40d000e441130344141318102d0a07050031415141c0c109129006803001080031012101c04035410360008a09101240355072070b150700846144003895040300d24a40c1d034041035004030b03620b0f2000c0e40c0200e9600c44540340d042009014055006400c5102a11071030650200300c0c1800c44024100c8082590000301000210318010194000e08400002d003600c483e1588500c0f9502d0b4001d0700c00003040260180024 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 133359631 1250 133358381 133358389
    0x11070c0506030403080f270d09060306080d080a060504150312020c0d0b0405010e070801060f0e070905010c0501061802030a1a1309030201141510080f04020d050a0209040c14 76
    0x24040c80d0300d83d44281702540e494000c68250440030784442c200c81c9102d40e0928205003811610207240158102a044040c04020050001d680c598805c006040c20130304100000c800214942c28901c0311400d0462070f40e034075140700c0c0d4001c02e201d030001c690080c036088940b01201400080b01b030950344940303080c00c5074405c0e00300c2c02e0365a44403031400342b507000011030070b214001101c000b00d40307810921a40011454110440307106082150076000030282d41e54900b810000b02c0c22001c0390700010403030480c12846a08000a00501c1c002048c02014144a0346075a103004110302580131000074400f91035080306032044001404c001c1d50058900306100750030030500080864603d148501600402800703210500340c00d144910181c1011007040c1c00f555600d0481c2d00c618402940c80a1051906840080301c0e403a00c4030070403110590121040c8100100c590811071750303400c40c010264026404485480d46607100e451b00c00d203817140500d0b0081d041100384007803004000c092941103003601d10362984550b0f2210004140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133360881 1250 133359631 133359637
    0x6190207050607050c03070203012a050309031207021006030f0317151003020d15030512031506070f0822080a0305070807050a0b010b031006030e030d0b03010f11070c0506 75
    0xd01150400b101044003036010b54001e040d00002e0740d00303a034100388098000900711179234844004100d0908091201495014040e80c85045140342007550550a00781c2460b40e07640a0b690b2810010555000403610150080010104142298a050021640780e282607031010310ba4010450205012010300f0294852581c98648124000d2680c07214842e40c005c1084100c0a020b03101100f41030b401c000100c94611180503600c02903450000300f0701080d01e0f502d4091329001c030620315a14028014828003090000e4499248021601103030160b0b2583c401d03042c012240c6a0708107000301905030010309032603981d443c41c124109111030316000f240801c0d61000199181c0c4408075000b4000345080113a40c0004c0c444401400906005104507040d54003280e0740c00030302c1c030401c0e0041500f240e0007104102c20003051114034400350065282c140024514030004c182e03031340100c0d901602101c0d2143c45e21000c035202584041c010520f05601480450701c0040e03215071b03075409484103888400030b544002c90141841001c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133362131 1250 133360881 133360883
    0x8060105120a02010806040f0606020606151314030304171c05030c0904050c0412050a1b050108010b03090127050105160c081c050408030124050d15030501090506190207 74
    0xa42401000340c3d00440e0b004500a00181d40a5a03420381100300001520501000d00100d8000300b0b4681170100400070310b040b00c3c014208140c4d004201100d0f0b03100055200304215040301000c05034070036001c40060b00b54065074011180c481e4030346070090320010001070030204034132000c08a1144030b600008201e42612049501e68002c441c10480c0e6052410a40d0000307901483d206c0e000c0d030801d500c440100420b4240c071783c0e045d905640503660401c1800342080011540304401200c1c81c52031454400064a1100144038403003801c0000300000e41e034100c00390002d8400100403014200812810200c011030741d40c02c058152000e41c40c000006842082d442c0c28034170201d01c541c9844d403801d00c251340ca03183c0c0340d40120110801850701500400c81900d4501a0794080c600c1280b01544a604040c0d0302d0f03c0c02c000c0c1404503010340e41c11103403803101580c214040350305009689130b0120b1116101822805400d8030f40d0b0004207550329121011086c82000b00d070f01401031143c62144800b4100d403200c201d04ac3c1c015514 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133363381 1250 133362131 133362133
    0x9030c150402091303090b1303020301050717091504020f0301090203121905090d140f0601030c090506010e0d0605090a0206120702010e0a2112020d0f050c0a051803070506070c0806010512 82
    0x3d10804111a01400340c8c41800740c020101d1176125404203003554010344404001c15031111703c035449052060921941700010400402c40062200740340040c1d400701400284c01040c0e101d0140d01d45072000c0d01b0202000e03070007030100d034448400100745030842c0d4029840788004143c010300000303100f84100200c40054000404010101361213448022461400c6417007082c043c89950200000700005001d09402036025903050303203c1a2030001048107460005168604002c207400800c40555248052034852a8006400046c2d5540e0701401e28a0110720101c081e5100710045a1ba5015800054a803481400c0541c003d0010748030102035590b0300c80f00c4444c0104a48031102049450074644c0701030842d21850380c5842012408180242c0049038081500544015141c50250140c0403041c040c503508181001c5545242c1800380070000d1040c0200303407a44038002804020a50f03165402c01c50382c006001c00500440e40c0707100d185050040c1c00824403440b01e050103864000505d03450411915200001d80744 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133364631 1250 133363381 133363397
    0x3020102060412050408120405130203070507060905010e030c01050603070e0c030403080406061208071416050d06091403131203270807060509040b0a120b09030c150402091303 77
    0x40e075002c00301c060200b00a01000405d001c00100c1000c100108042c0710046500c0996990a180904c080c0b008103c0c0740e940f0581c01001031050881d4442d0071201c026410580000b18114103280141c09808080310340b080c1c5200c0404e98844590040d4003860007680b00f00c0c11210b02c0d0303941d0060007501d02300840c0c2d0300520180274070010700070a0060b000942c1c07082c03182d240080c80f00d07102c1e10045001540b280054410072400b2412404021003041c201c1c843d540c0707280c000c00031201d0380240c40915900f14044e240c00381421030f00d982d003088055000b03040702c00d81c02140c030050340301c80448072540c07500001c03107004460b4507001000030035007141110648071030741540d81c241c40b10f905208101d08103100002468003a00218a00003079807082840018060603543c1d85d265607d030000010402625600c00300035105a04076203007040b006000442c00c2103165441130700c41c800c559072480000d0030b600601001002a0041c0c800c54031b103410400740901c3c841c1d44225031111003030b103c009495032828071004004005c15504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133365881 1250 133364631 133364633
    0x70f0302150405041104150806100f030e0102030f040c0b030f0402062b0c03060e0903090907050409140402011205040b04020f0a0302060408030d0516080703110409140103050610030201020604 84
    0x41d0040c880d40600141c0720500d001e80d1070f00403400315040725140c0060b0020126042c4845220018007000511140c85e0100260030010b0006400c0760103ca403407014400c03030482d5a00814004d420410aa0340e00c60b0086484c0d181c1000c03401e810340c02c11101100c2e0244c401c907011401c0030350501034038003622903030f05811840d50301d41d400d02805602c0740c56000340c0c1403260300c000784031401c43d800c030407501e809180c41c0460a0050300c60040c05481701e540010304c00403048010070600c10000410b881041208540440725901c84403015035580c426a041945043c3c24400c074009004641140280a28400e83c0c0d01c181681425190404445003940d004081e52204000b290161405000317040d02c6030750081030701c040c07075a403503002030b5280d40140e1010300103410100301c0300542c60881c410240d00c00c1007020320000264003002c006005030002445441419503c110300c00060007030805440140000040810400b61110580401900240702c00c5842c7c0c0704042c001211611544140001c803981a00180b40035210703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133367131 1250 133365881 133365889
    0xf09080606010e0612150906010f0c0219050a06020304030c1d0402040c031e1a0d02090c030c091002010e0c27041103030a08040507050607030f0503070c02040c030f050603070f0302 79
    0x114150f56200b002404108004022404814018055602a0b88071440c41000340170840000400c0349041c00547c0301d13040c105c42e8004201d014625070480300a25480c85010b0b44180d0b10600fa04070319000550204040b414540010080c01a2405851100003ca40c4c4204a9158100444c0c014070268441008a0010b081541220b40d803c1da80b4103010a41a028640c108400001912546501a210010000410381802100040090680d400400e104168000c2140303803501a201860851000000035000c09020050b2007124070010881035020940240003806442503408442e528000c03004095131502c0c201c031440c41000101c0c0a441c0450404001d1410050001801550301c80e40040b403080c9260783c14001810068800d4a440c0c020f800c06040580c40d00d803150f0010f90180c00c080142d20302080c0c000722040b02c00851860440d41c1c9030b035000000c64a907600350000940290620180e413045641580000300c08000880d801c100568400d8101561040d4520603ca90b121403441d0900150070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133368381 1250 133367131 133367147
    0x20a060516140c0f010f0b090105030d0203120414030d0905060a200c0c060c030a090909030813030215010602030d0c0905130c050415261620030412030f0908060601 72
    0x94400f0950b11004c1030009484d0075504540d850892030303541d550000509250040040e405031406034000c04008504030302c065a01d00c60000d1070041000204001400c02035104142d00702103401c0300a8039103031031429130b80d03a026049505003242c0c42d0247d40d002802400f440c3c841c044e40318041e500d101c180d45820801450310755128813090107403030080c00c9410b0b080f601c910f8010b119812081004507969060358000070030009441e004000850300300020a07001c80c2d809102c040d0042c1d5050350081c112141440c05a03e4222050140e200001000d000001c0b06c54000c80900440c440024052289082000086a071214540146c0381c0c002d5098407041c0c0070607103075808000c2c0440a0f041840c546074072482880c8482d01080c4410000480707280141405a143c00e026071040000b01f940004503040c482c008491001004109204120300a29401450315184021014030207044044e00c1e9603d8680b040550100b540728000c2c3e01023901d558083d000944214045811110458060f14081d01c6020044074420307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133369631 1250 133368381 133368397
    0x150809060f0406050c090a120c05100518040b100c060614090c0a03022a190b040f03031b0e0a060c05070b1303020a0905040303110a1413090903020a06051614 69
    0x380081c031101322141c03126921200984008c0e60440b000c40f42c6032034000708144650304000d00030803044013030701c80007a0420107449168910031030460142d40b100340480d00a141d60f1a000c0d6018015591100d02290000704d1944214000d640074043c0680390b108002203e5540410319402504c01800120070381c1e401805045140350038079000d031400500468004502031414120580902c4000c18100300a904102c20315150142064464008103d912408281800244054280b4490a08160826200c3c1e07100407901a02c80740b01c0300321011514001004000f25088581c00380d1400d04010030450b0007100c00e0b400b0b00307500800070104542040100986500300e0358103111039940c56040070005950f03074042030f0080c2c008880001054602801d0043c01e17074100148070034008404003d5603031041c2d072144c80c01c0b00b24400112071569a400d04411019030040a40c80500356a2418200310101a800700349510058020b86051105441d501000818203c01d080e06002144d00524103480440c8a440035140701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133370881 1250 133369631 133369651
    0x30a0b040b01031a09100e09100609052202010e0411070309090504020913050307150c02100e0705240c07051005030105030714010c1209080d0908030d050c0f04150809060f040605 78
    0x942d965690045180c101740d94107103a0f90071510127400d00405034400c440c01002c80d0035040c0428109102c0402507030010300400c08401c2d0311803002e0815640540d440c81d5818401400400844c600140c0501c0143c10244084000400c40308e40060f4464460294a014580080c050300c1d06441300135250340d48548841d01115940414404600487c4004401e44000800b96001043c0d080c62901c0090800124001c00303840c046c81d00041c000440c60021b041015284145c8014007410200f074450a1203207132609035401d90803000200304005150208030001258001d42d62091f40403460078060f01c040c0070901500d901a408030004200d01c6000c1e0615030459501810204c0a0104984403252944005041e000200d06035000400000c001040701051681720b51501081f1981000384c03140c2c03240719883e1003445550b107481c04280c3c00910b10303044074070205c126445540d855503202150111802e8010020010540c3c840010740960408943d00380700702c2c2e40c480307004442ea0307456480c00000c000180c0b00c5201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133372131 1250 133370881 133370911
    0x1a030606030a05190c0306090608030c060708090a0501020c01020403020a1d0a1a120c091003080f0705010b060307030b19050609120f0a050a170408060103170f030a0b040b01031a09 79
    0x700d56004d10504071080f03606e0750080307502c5040100d01c8003552086d40c0650f02d10b80c4104034440c0780c0b21011030a42e80280300c0349422400303522280d21061400241c01d102804d15440040e003050140d5056004008680c0309030b9100311140d50b51540006003076500c00f0009075000028000442c20303242684041c0c061603426045045003440c2d02c010030a117800c4a150f0524175800003407103141c3da2501c461440d902015070038400300240d044d0355440b441c0340100300014404600100d1144c041060a4006092000c40640040d44038549408028090140a2100f5000d0951703002920006094030003000181c0e880a4105031030114801c0c1444401d41007528500010b010340c030111882c4590070721850181034000c900411060440f824082a407510842c000c44179001d080004004407000070442c181182c0d00004620840a07545442c80e14070300c20142d01c1c69808200104200740c49549038010242202c0c10b503010400070510344010340880b240795101c03101018007111000b5440c6840e450306070b405112051100b01c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133373381 1250 133372131 133372171
    0x504030306120f0606140604030615120b0f070c17090a1707050102060907030209010b031f0b040303020c030706120207020607050f0a020102060f010f030f03180306061a030606030a05 80
    0x1010034002c00300b112107403541c007294000e03c4000e0207141d002e0081401d02462200050000440a106622000740746035225041100c2d1344c170840050030020251048a228450041c1c605807142e00011500c42811540300804580801d111b48610640e184d440403643c100c0040c0c40081a00300e820481c03005501c11092400455009902c49031452008224401011503d04090029040c188010280c00a40d4458501080980d0b501e90740c0d54110fa84c82105aaa0394031500340c0d00d4101c030080d4140342d4141415a0002a01210140c000c004a80c0070b5400d803894031b21a4030801d51070b1302e043c5c800c49000a05001c805000980c855005281c4503100406142c503000c601e5032a40c0c06c4c1003031000345041e590403802c0d41e8015560140300b130a50244a91980785440d40c1000651981d0034268000942021601041c103030405000d404103c3c00d500d41d0200041c5201d66038503008010300701900810600404040c155114402c012041e02c4c05410000e00c00d0341950b075001d400600402c0000c0540c044046480c040304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133374631 1250 133373381 133373399
    0xb12010b181503061305150d1b0303021506060a0206241503040b011a07080a05041e06020d0e010801120c0506030406060905060a0305062716031101020706120504030306 74
    0x501c640030b1400143c0c9070320b00003080000070b90014218080007070500040040d05030f020100e0f041840c0040f5041c8102070b40310309010101d41c1140040c050280010039011061640000d104d00500c409240d0040040d59610140140d0303000d443e0401d40903038458008580000c0e009140c02c01e00440858854000c44010000540f15010380e0742c070906a0340001003071200f40001001ca06014002e54503403250800e4001c1c1c10503405c1d12503407202900740d4401048001c1d001c4c2c4148200c130b00920303100d0241460400c0f0070038600e803518624410b01000d80f107040340b14440300303000704400043c202c0141c460103443c1c0c0ca0840c000413035040e400401c5603041300d00003002ca00da0b81e50300043c5005038080c11002400034108002e1008450700940360f10322940b0004020000100d0000302140e0041228010080c2c40b0381d0f081c0071580070360300b12340c5620f614010200d0700603401041c14000360803203000e00b4101d5125640000103903250b000c580034410009583d108892104040f54100b290030034803a141c006080c0c0c0e82d0303031011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133375881 1250 133374631 133374649
    0x90f200d0602040e06010306030c0603050a090209181b0f12070b040b0a0f080c0313050106030b0108010e01050a0501030519110301021917010608060d051203040614010b12010b18 78
    0x1c94040d94046400d0004038001d8040c03a030711000c01c0c00c0c2005810f08580b980001d4036040d00c105420982c6420020307400044039000009001d0303010b0075a840900f01143c0c603008440c040102c00411340710300700c205890680200c48120000d4409041d103900700001c441030000c4045040d4404049105864000030300d1003518000b44000c1c00101702051301c6031044200180010600b403400800c12100d6020700c881da2884038104c0e608103465444881c4041210b01d40307680900310551002d440e80150704000185c481e0706400810f40004060020442c0e40e403801c0181d002c550303083c0006003050340118442012900008a28a007980c002c2078003404d03580140c0700007401da074400032242c21200004107545402981056041981000d01c040c01c6201d9810300b02d0041c090040241a5449522144451001c1c84800c1c00700070200c0c040e007540e042d900e180504101d405032900d11080c030036020300040002032560480040d104401c0585881025503440c0c0b140c482d0840d0882401250001188010207901c0e5039200c0308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133377131 1250 133375881 133375883
    0x11040b0d02070f23030a140c16090b130203160c0c080a080702090906060d061e0609050105030c0303040602100209040e060f09060c130e0c130306091203090f200d 71
    0x4520705441154001840c03803048041c50f0103c1c1d170b0050041082441d080101008030084015400342c5543c2c06d005000e1910440e03a03d4001001d844031408542d03c0e0a40c0c0104c24421000d407211400358038007050601c00c9200450700007284045805403c4150340c4542c4246241074055903500d18040e40341c180c00c50801c5008681201c015800103908030450900300076280d4010b10002c042e020500c1c000020a4441c00e01104c0102015600c8030800640100d15500158601c80d0790000c10005880b00c505000800c02030089500c00e200324020301134545000002c4400790b841a5015110856030310038108060741040b4800c1c1d43c866100c502d18180300f4420041c00e0701c11b07a58020301e01c001d8203050050500f0f00c4405410000ca00707204216140f40c2e40315081d568000c0325841980102c59a0f00d54510b41c25601842241d040620001d400010501400c5e401030b0140d5805a00100c582001d064012f030110350685100501450003950020041444c01200104041048200c01050145540000c40180900740 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133378381 1250 133377131 133377143
    0x70e060f0c10091e0204020d06090510050301050405032223010e01030506030a1403040801090c0603050106020d080414010f020316180b03010e13051501080c010311040b0d02070f 78
    0x14001d0039000700b00000040d011015008000640742da49070725880404100305800b00c4000072100504648541d07040303078a41d81880c83c2c10004552128892406040165001d100700248050080b40628042c031030b1500590b4801d005614243c0c401c0404845840d80c40300710300380030322201c400048400030f120404000100260079850740d1220b0314009046041205251410146060108150707920000740e903c1e111600100a60417403692404e40e207155100700c0c0c1210409500302003094040082000c40c7c0815540607480030320060380c0b00e010480c1c1d01c2c0043c0c5040030024040c00081404110a00070001c2c15445120000c80d00c3c850300240403044c1d0b40b00351464141e108004605101b80c0d60b20698084110304580d240e000c140d031422449049900042c02182d80009200c00840c44400c540843c481480d40d1100030707a20346203110140c0a945071024860803e041c060303144035103003c3d8468450707103203440c1e000a0507505050500000324503503006600380c1c12440c1c0c1e00b000440d021a4100d00c000e582244030314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133379631 1250 133378381 133378387
    0x27151203031503110f0d02181803090d0303090203010b0d23070e062106010803030f09010504030f03020a0507020607050c210604030e01050721030608070605070803070e060f 76
    0x32800400321410140b0340000000c905600780700042c10320f125070381010b0b000c86280c044401100002400340e901600c3c025803011402140c0c0c10050080740711170344103000e208440814411142240b80d102e00c038544550342d2200ca054002c0d070000c0d0007035200c3c0e1100c074009400003641e1101e074400f241444021140c00d03103100c2d02c906124400e2460940d260900c415130a40035256192a0000513a0500380181125104840e5041e1104032000240c0c643e5a031104050708079102d5503074820000f0f403654000d83e85540341c0c0340600300265122405010b100d0059a056a0718202050b54841c01c60080d001050354500b005010000c0d080941e542ca4003078030741036011320040c1c0b50441500302001100a010180c4c4540c0858010380d481d500320010800c1c59203d5014182245411400380c0100c400c2c0c800d42600614080003401c402142c00b80c407104d845400070b510b8404115503511081038541c0d4520503c55000011420407900300040c8101028641105903800c000c0c40d80520040040e40c95007000403100f201c101c006c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133380881 1250 133379631 133379633
    0x50403032f03220501050c060103080d14070c0b01050a05030a060c1e031a0f06030a0b0a0902070317090619020d1503080c07060801051809100614010e0604271512 71
    0x50200300011302090801034078000c2804a059201c210520024040000201d640651640d994000c907103428110f4030540381d1442c082c440a42110212202900c0034524000045120f0501203846001e55800400410040c1001c2ea5000701070510885082c0c1000703004056221303042c801c0421070060580c50b480102c2c10703007400351500b02034002901c1d000b4401c106580461025484800440750407680781107000c9820003940c0302041d001810740c0d0240c291941b000030300b0018581e11894504881c0c20012800c4c5254660140c2e00c1d980700070030748072085020703451441e906455030b40ba8020100c11038802004500b000200280807071000c85540240c0b03030000c00044400310302c0e0b001e0081c40003902a80c10548655414034000c14004210030302500f6040081c0c070003080b0301040401c0481c2400046000910003d03413030f8001d020ba8654104c0d45c540c08540c02c01244030031407030598103940568000c0e00810b524010000c3d05c501c0c04040444441003641da60741c0c0c00012200c40d811519018002081c44080582070f5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133382131 1250 133380881 133380937
    0xf040902090c1c1815060b030f0406050601020601051e0a03080301030c0f0b04030c0501030504030c0f05030405030c030c032e05040b0f0c0a020a0201120222030b0601050403032f03 79
    0x80c0303c45880d01d0716000341003640000e4907402044140c2c00c10404051251119140d400501080e00401080380c00030040054121150b10714074403ea1281c5001e0145807103000c0160398804080c020164051401155483c00c2c1079040004090b8a800500a40c081a5a912004200e6000b0b800988400d0783e03041c0305001d107507024240302e801021071070000c928151031503c4044100c030380340c0900d504058688012a003410320a4140500c144d40040000034600c6070752500311380e03ea00611526009001e4004146400d1501141040e000c40e4090050600a07241c80345903100414a00c5e00c8044604001c2c01815400c905417141030311440c1720300b0f0a00d400341030005c01c000886000800b0041d169404210300c207840b07a408202c17440c4035642170a24050b030317518242a1001030300502034030046801c98401400401070b04040c1e03507022203006030b06945894403488011903641c4581d000c0030340442e0040e05003c0c40407a4020220541c01d418070003600d1040710885020381142d008030b6800c2000341094440c007000b10f0b2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133383381 1250 133382131 133382167
    0xe010903090806100b0c01090c091406090403090302010c1112010e060601021f0b01170408030103021c0807200d030509041a03031c140a0507021c0e010c02060f0309060103060b0901060c020f040902090c 88
    0x342140d03041813b140030b42c1c001f04211190b0000a0401074050240301c10490500e07441c2c11074400092900e280300c0641c6041500a0100d0400000b0901c00e55000c1460b65001290b94440344e010001c048566460407004030b4060180c0795061410041070110314070084c00c2c022410390080c0d108242c1182e481d491801085054140f10005042e005802042c420018002d14125062103600408481e0340e407000c05515003503584980c0200d070704580c04016202c05c159028006003005601210100a8001d06145002401401c02c0b6515010751041042e4601c1c00301c0c04030748a113403c0c9106000304514a0004055040100555100c04145c2e1200140048142c06002c807289083c0c008161920b0b002003e41c00518001c0104203840c140b1100d040d40009640762803003200c200b4140c0103421652030800e500140c0d03403803009100a9a890f8542820014207140003445d140c1200c8103580c0d0104e441410740c00700003861005000d00e95016645011000043e2103080740903104040d40b0510305d8840340c010107030140c420 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133384631 1250 133383381 133383391
    0x30c0905010e070806010c080309030c011d030417070911040509061008150105091e0a06050f0915160b0114010e030d0e0109090e010903090806100b0c01090c0914 71
    0x941020014400d1011200c0690360000440c544000f09488031001a5005942140c02910310300d0000200410301d140000200b00c8100d488000300890b038801944c92040024140d07800c42d03a80c00410042003681007403400300c0c1916120409403002c1c42c4d5110040c508950b0080c440003108074011a0801503450050109030f4094419100390721900e14145c80101074000007080745d425001c4020600e00b00c5d9100d00c094078900e00e03000d044802442e8801680c46005001d10700c13014030030910f010001c90321a02c600d013a20070100b01c5006160034064008100640d46004070840100400144099400d0b070741c002460485040c09030558403508e50605040f071101700c03505814a81807016080700c5044588000030600f00011031442c10050404c400c0780104c4445c10242d100c030720391900304200704181940643c04521118425100d840d4001d642c0c2e010701e0386036001203c5249483c508045e0401544903404000c0040e00d80f0b03807000041c0d44040f55a15240341c110340d0400041c40303990700d809207000c60950b020540c003c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133385881 1250 133384631 133384649
    0x50702030f04120b280f0e0a0c0806130827060a030b0102010b0a0b03010504090f051e0d03090b060918030c0a060f0612120e0d12090902091014070b010609030c 70
    0x11800e540301c003c6084032130007020403030303524142d0074103006d1240e000941074200030303041d280b0804a90400130340c080203502a44141d4010a404503e941255204810005030310090541c242000c100c0c41007510511b009582c84080e000c1a00316801395100c1c4001c0c41c41410347c2e01c001400c55010000282142c0803511070034041c100101040c051180c0038002e990450300210b40100741400e003842c0401004948441c000e040f84619581a0142d0181007420104410340a00300c400301d80e00d401044047d2808203d01800c0c0021502c041949402d100010581c05481c0340102402ea08241c5541c61666101102c584055000380c00790a0422169024030031045140e03141c148181801c001c90960b20b10481d450091101d000d007110244064043c821b985d04201c001000403030306001030300b8800c24200000e0304c207030001450484042068a0588260740700500007810a8020130400305041d280703241e440844c1d0b80603080510592000a00380e08842d406091107a61b8045003a246182040b8450b00e65040300410b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133387131 1250 133385881 133385911
    0x1050f010c0609110901080d14070b0f130210020717070308030c130509011203020c0109140118030c08030c0f1203040803130605011e27050702030f04120b 68
    0x1680c0c0008070440c1550054400a0401e00614213240c45901c5402c0701e6805c03c8504000003490403003ca1014030340130460726603c0b05000907901d002d28501c1100c00062452000780d0104400e2098413180c2940100760014880794644d80d80c000a11340010b900e14400160b0101030180400c02c03880b2a1503005d0200d181c01046502c1c2940d55402d800c0c08028410b6640c0b0b880030130010b4125000c002c04500600010f41100343d0355031950b012440e5141c0e00041a0058407d460041c0340b194801d001010031203011400510100380003000448101d540c011209020040450703010011400c50b031408401050340384019541d880202d64854140007400c1e4520344180c00002c2a00d4420b166101201d5105500c008240d5696480b07603c412114221900050901441c140020410f20841c0743d1000c80783c2c100c43c001b10f00c00c680c2c2d1035100c2401843d14084d02040c0000010000194001350440c9400407580d0040d05e05100c1c10f02000c3c43c039904107501542c42c0c060001ca689003401150a50550800111030342c03011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133388381 1250 133387131 133387159
    0x1418030306130c0909020a09150c050706030c0309050f0703030809060f070305180102070c0504110c250536060609010c0501020405030a08070b0a0603022d0904080a03050105 76
    0xd4180d00340400e034840729072036030b18030f8005500c901c44060160071114011520740c01d00903c01000c049550052400c1c40c107804000d403030381e0f6000b0071145081550104c02001518103118080b00034112a10400307081c1a20384861b00700082007400b0030003000c0c0480c0003d00003180780d814001d003440005407080300d9982002090140c10107048c02c01a80c45801803d0202340d507120150140c40c82e141d0104441d00703c0d4030109018040144800584084074003c8030148002c00501840389040c1c4038805158400340d001541c203103c1c0e09501900c12040e0f0952420240240e9560030116903150070680400d04040c0b00a0444c1c0c4441e40c05144021038181d103030100e0a050718000005c61254440c01c0d89403418066050303945020403009404403805854041d0a81d4550740b070615010300540c201c02400c4940ca840c0c4000102c40705c40901c1028200c0380c009244010544550701100c0080300f09100c15201d0104061f00000f41d6103421040364080d5100d03480c0241d5501c5411001803c4a5041e009148600c00c0d00c82c100c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133389631 1250 133388381 133388389
    0x512030304060504081201030303051603060501020d08060d05060705030901050a02180d050a0611072307030803181b10080106020c04230411010212090108180307061418030306 77
    0x103a40182d2110b800125038a5a0a0900b040c2c0104040000255109000442016419004180110200300303078003c11007901d901c02d0713059401c40c0c0141c074010b0b845590b1080815204072601074200001414042891a00f6111142051801c4803000041040082800606d550901c03520b80c7c004040001103060149000b803503543d4000b80501a480b0707045510818060240502c105040950b111800b0421a00c9802407803016401451041d0781d41d4214102407030101d588201030b00c40749200100685580d0381980c0e10786650f1341024040c0501e000c5070340381e0182118000c020b91240d000c1c20010701c40c4070400d41c000304010802820544010001c0c01d0004200c00c030740018842c1202142201c0100b0818041c101105070b10a11100341220102c0d00300034841884502c14441414000c00c0c3d0a5910310305585a05040c10b1285282003030003d402500007840714030845c0447d424117180b50f001c2e246070810350b8580310191940c6400200100d0804010303c00e414004c1c00100f03000000b01000b850440ca0700304001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133390881 1250 133389631 133389637
    0xc02090106031a0d0503090d060b010e0109030507050105030421020102090f100804080f0d14060901062307020d0f0b0603011d030904020c0106050a0312030c0507050c10021207140601051203 83
    0x1c980240300e154244c0c010000244103951411101401c1003030345403810b05201001e00038010403140440c00441c00c405455208001a1003642c2c2c00000804031540f811004440c6907000410a994201441d100b010f003190b190522070303000b00703855400941c90b208460b00f0004980e1a0b1a4050311030310041a48462094100000580c403e810414240e00c4104801030101c1c036200d814081012146401290342d8814a0322064501424003a103c1840a03031321550282d45c4118602c05c2640302505107100110042c1d03510005161152001c1c049400074145940d8030f450400354524202c900612002c00c000300c1d42005d100c1d00e51507548034140311017906119603105840c2c4c4940b4400a0285400140000780c4480c00d400107002400c0190141c09403654904101140101e13a05902d400641003104040300141324109590110350090041c1c02100030b00410043c0441c1284110410343c040c955035078860304054400b5040075405041440c901c41c4d0754640d10380c02d01c88141c00c150300c00c0120b0110104660000002c1e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133392131 1250 133390881 133390931
    0x30c07061d010305191e050708040201020616021204081b010e130509010905120d0506030610090f1401090e07050402040b070b10030819021b09070e0d120c0209010603 73
    0x1000030161201d0b6002c00104c170070858000c403598201100031225080c40702190400303143d100070403c850b4a4240044503040300540d8080d0043e03100d8804542200100c01102c40070400c0c03401212250000e81e0802c0000303802c154400c6002d07800c05503080b01043d0741c1022a4480d80002d20704090781c11081d0000541010b642600441903580c0d4100194280340701350700004185801200301d034622494802d000c04154019151595604e08060100300c15040000c1c0711070043d8003820600468504004402c4010320010310791072641a00c510280c80c140881900081c081d01e0110000300351403d1704c801c203d1400b08075501c1280603d10420003009009000001c0d140d40d80c0d80280390303080c00c1d02c2d0354503150404049900060b01030b10740014003621022a04000319020445502541d0b1050104000d1a90f104150000340c1e4103c840b403000502420f1164100c00ca01d0600240789202030a43c07510703680e8031072159910b5200072804011303203070007585440080c050052540c0c2c9814005180d4200c003201c150381100203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133393381 1250 133392131 133392137
    0x30c03330e0106170633090a02071a0115080f060f031c0503060909030a020a0305090103151503050903070f0b130605090714030111191103040305030c07061d01 70
    0x1c0c410a081e42904040c0041c0b02e0301406252486500d100c5a484081c291b51480100c1042c184e540c00d68201c815126440606c1c0c45120003030f0741c9084060124213180200300401300c1c2c1e400c03c0302400140303611001c3c04071074100342c0c113a100303940c10405058084460a0f103000d09005041081200803214400c5403544460140c074800340419007080424985400030844410300c2d080611100c0f415540b0030080c1d03101d07000071210480f05850b40c001071900d80c4a608040d0006803c130128070008240148024540031b0b50625000440c0684880041100485604078030203544c0801c01200a0b42d506025030f44d0046880405946010929a1a441c000c0d4018a0042004a29100061703c142641c46da4251554204805010324a0b0074a811600c0345914002c020404155254844071400e05109006520356460011b41ca009058200c0105110180120008000180b4080041081c0c103001820045100d07000941c0c90b204242d010030304080941d00b0040c100002c441450702c3c0b04502120201c0d00240030f007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133394631 1250 133393381 133393391
    0x703020d030207150c0201030f050103030c110a09021c05090616270b13090203100b130503030a0207060206280203060f040e0708011a060703050c1501030c0333 70
    0x407070264101960b0f42e01c00c00880840c000e00c1146641c000e110005210b200b680c0801101d007200140d0801c0f41e10a010140000d0b514044503000281c007410000515103004080c240d0340c2d070b91910f1a806a80c080003001020700300030385801c091441c0742d0082c02d8111680300054003007850410312644804280c0c030f243d0820010810803101d44149a40b0008000710f0020100098a503140c40da01c8030540d001341c841624501038007000089501080c03080d86d016003411403100301c000c1d2403e001c0340300d20b40243c0c100a1640e800d004c00040d96590400c000c0c40703111120380240001601e0914080d0802d880100aa00f49042c480da0022024005040f5030f01c607406c034031a0058580d201c0e5400b0500002c1e8a0f80052740243c03074207643c00d000303010000d09d54045a041c00700900c00f01e18000700f40f540c5004c4008a503604507900744007400c0041c0c061030103000240700b060200c0316101544078004142d84406c0e8015200c49130650420b00600c0040c40814003500411400100b074055030011005100da1041c2c00a0307902d42e592 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133395881 1250 133394631 133394633
    0x90212010902011e051608040501110c1c060f091b06050403080f0706090c0e1b0c0705012a0c03020a060206060a1a070c03060b0103150b030c0a09030506070c03030b01030e0703020d 79
    0x1c2040d20706c4480703c00c1d01000900c240d40f804010591281c011a4040740296000d101072210000c0c1040c4100343c090700e03594115112580d0082c80100403d4201d603140d4880034126440000c903c50444518000c841d0442980000f0200b0a014041034000307104001c0100310610104000e0412116011000304816076140320300e00301003000b0149074000401180100b08006400605044441d0054490306400124212005545817091142d00c021050a40041100308484e600030884401044140007100f100c0002d004081054003601110440740e4411100b401e00035400c1224078080542901e0004107030303a050104c0010307501c000a11881e0120490342c1d106000461255054440169100001032901a00c03442c01201409200000a00086c9403800b84c10148800400241c2240d02c10703040c3ca8a1a20b0f1210b400d4480d50001c80b4840601c080e2500000004070300700500392184810750784a0309145410314000702620040900300741003500b440706548080c08041070f038404a950403101c2d541580c4107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133397131 1250 133395881 133395887
    0x304030c060f02071a06030a05060a020d1e020a17071e0306080a06051b0304080a0f2f0106090515060702041404140f0120030a11030901090212010902011e 68
    0x242c0e00c04407480d240081040020480550b9800a014442441071800c1c3d99400d41850b0f69031040a1000c1d00f1548800d0128020003100d83c02000c07007924008002c070760b600054906070362014110b0544c0e100c0a600251302e0080b81e62002e800054032100b510050000d00b03244100410700140c078808041041620095031501c903009601c103100030440c4406a49000d6000c1c2400001020102c6000b0140205000c850311103050b45130491744215401034505082107110f480c11210070520441c1d030014009104034611010704540900007201140841da103c5404101140ca0300359465a40b140c240b05017084240720b501c0c2200092910700b40701c281d410503181c0b1914000180901203118000303068414003c1440203001c00c00b4a0352009070900012a000b003003000b0061401c9615914000398144001b0003410240c016080003990444102200030488907400080e091141d44103482c0d0003403d03990b03901e1600c214101090340c0c54092010340001c0100010b5900040d00da0030000d40c800c071540d803003102d00c0307041180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133398381 1250 133397131 133397141
    0x302061b0715062601061a1605070f0902030108011d030901050c03220305060f070206010501110c090108030a1b11190801090303050612010c09051020071a040b0304030c06 75
    0x50708a812404101100800d1601349800d4824030b65080010100f000041806034078800c0d801000c000307103441219204c04100c8072000d02c080710280106a000960fa10095048102410508400603a02c1d40f5110301c480c01c4841040f05004801d880030710140d5001008425181103c0080c03d000b540d0702031405206085220742d070480c5821040c42802400b2014244890b17606a900c11030440c0d460362984699245400d40031106a030060b07001c030740140441d51007100509400d8010000b2550214402000a00744e41001d8002c8801a4804190855220b034061078a914003008903039280c088003504c0d129504101540001c0c02c0c000c001049202180c0301038440c4010080030b00200030400500c1c640340017006000c0517100e003032281c8200b60b911a0740c45810711030580f4a180c19290026094a01400d202c100e250447c4950280300d240034910740e08500300510300150701085e00140640c1c50404486081c1c0d160990213491844409000500c200110401141d030419014107000c0e0700c8640c40e1408001400e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133399631 1250 133398381 133398389
    0x70f0315410109050613091104051f080c07150b0607020d050d0917030901030e030d0c020105160203030c250f0302060612010510050d050f010c0504030302061b071506 73
    0x2848400c01c0104610701c0100c030200707a0909036200d5400c16501c00400800780074200309030484101d0120104510200c513031001e001003078810201d5062681e524001a60700c41c49001031850440200906003400398054205603001d8403521096003002c41d02d40f251103084401d00c810030b5500d640c0b10010a01a0340701800c0e40e010b541c0c003c21442d8000424680390b911000c0f152260300c00700781028008541c041c031041c0000b00410341034004504182003c001180902103040740d40340b503030004201030322001c4140c1c000c1214198058001080c02c0c00d00c084044041d509501d00c000841d0010300a004500940360704031084d9254040440900c1ca00c00005c0e12102607620100502006c105c0000404058000c214180320703146c1201c1700301c0314407040300c1c5541c242c6408441f840c1c2c4450703128a05005070300e4113000624000380243c04581c03124a07008131150031511443d0700c0301c021690201d410010954100b214a51000340305030080d500d1b500301800d81100d4040c1e0701c0c000340106442280c0421496482d80b0580c014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133400881 1250 133399631 133399709
    0x20a0204090c0f06110105060102060112200613030b150a0303081b030103061e0605030c0d03090e040305030402090a0e0c010e04150b03010603060603020c060105010c020d0b0405010203070f0315 85
    0x30b503540c04005d050340310140c01c801065400c11001400a6001041c8541290000343c00300c7d003100101d0380d9050000f030681c400100c04c4d00e107200c0540c5190725400090440307004c4028201c0c20795419410001c410510082144807281c505244045294591009e864101c03a81030904d44c1c030f561510001015136042101c1040c071010070101c00002880043d40049844090f017529581d0120400000c0205449007401000c0c0c01d603101a05d0100f00c1c1c14060100c400701b41c002c2c03600d113242645450424000640c161025400990003206000c1545007095015402490a403002c00005902d106465200c040c414101da05015440c210341c201a211a0450031000e042401c02e80310701034440e80103110135003003801407100017403420901251903400707442150394004141c0010f0480368a480011945240c8448080b6008030700501c200300062184407401d40100e109800168491410605c018011051056600e04240c2800c00000c00d4513421000b43c016180390a80c0410101e00c410002425100b14003c00d07200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133402131 1250 133400881 133400909
    0x3140304030506150405011e0e07020c0d14012405011d060706090b1b090d050111041202040b0f1c0203010e0a0b06030105010e010506161b06170610020a0204090c 71
    0x321000c401c81c4c800842040301c0030440350340c85204035441c0500309840f4220a40516038144031810741c0807400c5500810301d10444801200000108464070482e07441201c00c9280d00c0034200202c9002e018440c00381c0c2d26820001e4410040c0c56440c10400c40034801d040c14421040000e524400011700c0320780d10488040c0c5881d41d546528505140104400a810b47d407454100b0f02240d00c0341e00c0034101841044000d0b0005061401c88803c1000f000c8090038112201d41d628085c080010042c02d02610041c0601100d21025a442d801840b091319001d006040c41068010303031090456480003903098038038842c85041484089507201083c010007032450042440d1040159400070031401c240d007544145400d400034041d42c0d0346d4200c00d1001c801c081c010701b58003603000c0c0304181d4004040300511880314043c40700c1c0d0308040c210040810300d00400e5000380001401c0d20380c48400000741005160f41151007550480034101c070342d61000f500c6a54805000348900c0d1122a00000e00018200b2600540742e45005151 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133403381 1250 133402131 133402141
    0x51206150c0c01021c02151909120207060e130c03090605010b0d0b09040b0403270e0105040b0d0b07030e0313171506010503042405040302030a03060801020301030c03140304030506 79
    0x350b102c1e1a40440c0b401032040d0f841484910303244112240010840d6002820b185070704500d074200c84040240400e10740007250b0317401d081580d52402407140240c06a083d012010b05004002410401550030002c2800300404040350141ca132174881c24500d100f200d034006100c2803c1c8a0441c003501402c1c0018048608210011561110101c002c020784020361004000d1450142d081c064900340840300070300b1114801d800074010900500e440b04244c88080d62104115455040640a201660b0040c0c5810034041006204a040621404801035012944003041c00d10a698885122000501c114201030312604240d501420810a0b100800703803009000241a841764070700c5c644241d050055a2040c49481c11000c100807511080d140a008103965051540da03d5403640304442d002d080004034580e040c0f007900c010803900c030701c207142c0114440c1d4043e41d9122840d00000301910790a4000c0b05499104000400000e044941450212548144010008050015a1815400389a002800c00d008000c2004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133404631 1250 133403381 133403383
    0x91f0c0614090709110d0518010501090b01110f07061d060d0225030c0803070c0f050a02010206070314013807062306090a060503070801050901060e07051206150c 71
    0x82c0c4100007441c11103089598031a5290161541d50750280c2103140c00300541c0c109070589402050784240001c1c505800f00d84000d610320f0840d0000d0b40014400c0f03640303c00c5141c7e10361f44100b040703840800030310040c010720401200d076507180c0b2411b11a5405000168070901c06041c4040c1c00b01c0144c0a00418050701c136601041d0000c080c0d48100800384103081c82c00e10b0081208042600b0a04141e015a51303101c0c110a00e50f6030b4030940d4005003000081c0a101519800010003d0f441200641c1c0300300040d00310720310b581c0300282c030342072000d49001e05060524084d541140c034588400d030304440380aa4038000c0c001c03603210303c803031000c9012000400205a500f1b407800900e803d00000d09290784143d10410000841991015044101144404e4000d9444003c50b03103034a04000842d4010b00d152030001600c6a8800c0028071748107040c1d000c48842d94481d010070043c003200b8400c100c02401c420801e03044919184000070120321401040380004c24030200801c0e130381c2c0c5861040070b50856060b4092956080018009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133405881 1250 133404631 133404671
    0xf040c03051501050c0303041506030605010909060b010807021f1407080106020c1008070509030f01021b07050411040302090903131202030d092102030a050a14070b091f0c06 76
    0x701500e0301941403000b2948100e0844403030b03018503c059801d40d1601e80e50480802d85540300c40d2080c54462402201242c0e40d481418000c0400c80c400044040c014a040c1c820f0740c481c1c000c00f40c14803004908001c0e4554000c90800f903145d85942c1c10103801c1e521001d9a1000f4052040b850302d25050100810402c50f0308408014140c1e4165022100c080344060108880950031a40d0800050100d46c0428510750060000c1d00092400a09603602464200c003c030b42260448d15060b14030f51000140c20101400500030f92003e49000d840512940300c910820141c03511461000a0050521100140002400307005039840c0390120400d85c1081556005102c003488071606069100e80035810b141808640a13880200880b5030b101c2080c03000c41411082812071510f4001c00f1381c0c140c05144d001c20b000450520569040c0d074401c26285000d0040c0882552501c1425040085143d404024071042962911541031030300e00050040380000d0044031041b46c07a0302860900818a40c14542a080c0701c000815071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133407131 1250 133405881 133405891
    0x50105100602070e0702071404140a02090406080102040515130e0c07060c1110110903070f0e090f030d050a090219090506010216030f06060e01090603050d050306030c0f0f040c0305 79
    0x80b50010f41e141d400007809514207890403070150b031144004108a6409403140c005100c4d0060000550b01d03020300c1c505124000448115003030743d42c001924000742c581031003208094400d82c0002c500f4181040041f854507610505030035082c0741c01050200d03007640c14a440002138903404d071185031541800d0042052941000d0400c5882d40d003400f91020f0818400c03a03588003c807216400414101100680c0e81c1c0c0200045080d60b0700d4000b042000d400580ca0800c003460060107045a061303040c500d8904a01c1c415070000d4800b000542043c034541101c99400026aa405440700d08001b8864852082040c01400300705002900300345030440c41d80701c614490800b002121110b1f402400f255503002e00490b120500764001e2003111038841c0090021036040c1d070761540c409100740c00002300c01f0380780c0780c8000711400240c1c000b03911141c0362102482000818400040000418100b142c198107060380025108d070309031050540034482c6c010a6181c00e40c0c411110070301c002e8000d0030401100c0c0d0003c0000340a0310040350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133408381 1250 133407131 133407133
    0x30a050303070e09061e060f0a020f12070c030809060d06060206040210030506060708030c0d0213150c0803191b0302090913030c1b05030d080906150a051c050105100602 74
    0x10342400b40c0d040000b11103100b078000078681c186c0c10f803c0307900020303000c0461801603410140601003046c50840e000000e1841549540051203040c074a0b241e510329184080740500e2148005121a40c005801d0402000a69900c22421911000031002007000e50150420b0300910508186001550640109409010b0b40c002d8a0351307180020f0750202030703040e6001584d1041c0c201d40c00f0807044002c0360301c0c100a980c00c07030149950985820f000c680004144d80001e80c14070344800700366034204034180081c01c001c1c401f00310740d08068644e0040c076150380c00b031404020009d180e106c5075840c02003080c1900d40d002c1c1902c5c814600200b0014508100003d0003034000c480900e001e0084d1340049000250f440309006035256150383c40c3c41294010b50b45500c03000d01d961045150650f10800b011820350390512551145500c5ea079250141498094130091510501a00070703204041303c0007494905032500407030f030003d07110140d55441c1e40c4200c0000380c0707202011f42c050180c443c2d46028184403288032010711030300440e11030b94 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133409631 1250 133408381 133408397
    0x6060305011e0806150a080f16060e09010b0702010e0d0c05030114090a060e070f030b101203120506010c1703091e0703030c02060903030a030506040e03090307090203040809030a05030307 82
    0x61480c80c2d90200d40c001c6480e1503008030001410b0b100c41e1400c2a08861019054045103982c80300282d20380441c5481e0758001c0d0b000351041c41c81c10f5010801d0007000b003526140a03004c03000c10001140300b0401c1030088441240000459606590184040da001118040d100125400c0b85041201480c0b00c140180792003942821442c0030709a44a41d2080c3c06210450007600c140e4140d56034141c010a50450640c1c258041c00c007000a03050f0609500c00300440c016560781505191030108804071010746c0d0006d81c3c01d5021442c0030b4000c60f0307004243d9003845400cac0c6e000160360703114040142ca003c80e03903c500910090000c00707014000710001c1c0103507011b82c2c02c03041214a110000b20250101100a81c40030109600c40e55042022034807400840b03090038005040b041c509020040807d0566000744034410201e0b840300c09010b15410036105410fa0010a60080c40c10300f00d2850001e07880e40100d110b961282c580102c0494180440c44007243c907a14030003022104500070900d010b41d140e800884014010400803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133410881 1250 133409631 133409669
    0x30a03091511041206140109021207080c0910090504020c16120209040f0204020412030806010e0105040b12090309060a020604051513030815090a0911121f0209040606030501 76
    0x16000305000c000b1000c400701d0915080030b1640215088500044d240c0c103803036000c1103883c06100b902c601d003e0110402c3c096558560015014030303010000d0041d0080202d46001c00c04180403480036102070020844100d0810020004e040390100705603000154401d1000403a15010316000568094001820410046290351061011a282207168000c0d401542c2c9000080003c1d046050040c40f0b2880104014100390b1510b2112800c03026500c1d046002c2440300090044a40c0c0112102c811301d1824a0003500c2c103414400d54101600964001c019041c00500114110b050288155814400b02610b081d4403031314a0440256074210a0324252168041c00400a0702c000c00c481800d0302c00e28068a42d02d00f505481c1d5421a0318203801048003c0d54440c032000c500480e510502c0580c015400100c01045242003400e0011803019002003080c410b4814030404011004040fa0040b81c641510040c0044041a0110980a031007003900d031661081c9401404501c2e10f8241d4003050680f01082102c2c0314039880303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133412131 1250 133410881 133410923
    0x6120605030123010b0a212903192d29010603020712110c0a080c030c01030504020a0302040b150a02060106091403120f1b0102041d01140120030a0309 66
    0x1454560400905007c00b050030b9000021101103000051b200300050610442401a00210145660440c0e14200302a42400c2e4a801c106800380104150a409071000442d501c40c2501e5034240c81c0c041c60305041c24200c0110141c1c501492801c20b4002c1c0701140e402011094035810503441480f100048a5803800124010f4407038401e481d01c00d640511f40d441c1c49580c1c000141d0703508274a15528206841880003920054403095182001440500c0041c0307038409180040500b80003210417454101441d080800c40035a070345c00b0f485070440c0e40640700055440745190215001c100e03000401c490030140000c0104001c2d6000490318100e070b0a56842a49007921080040d20403240c40e11a0f5615070300070504030104860b4400181008005000d2161800070424120803d001c2e0120aa9070503940c086010440c8444000110071030054400c0580c00c4d943c14500100f9081400d06240c03410000000c202d614105681074107407140c48221030460351964482903008016000301041158a010003101c0c0d01e2030010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133413381 1250 133412131 133412137
    0x40c09060801062d0c0b0105100c12020f06040f020103110c030d1d070803180105160605060117040f12021c1d1512010b070c06120605030123010b 64
    0x12a55a800000b03920b4010f045501e0802c911074052642081180c80071500340280082407400c1c00c0f912039400311500c90a00780b1b218241640194001c6000411244d41581d01c00c2500d80d03640c0d4000600c05010948080c00c030f240c03203d02d0340c0401107445040c0510042c0f0451460544155200366814032001d048260150211300800c403505050760300c00d0122040380030303094001800c10741d00c00901404030304200030003900c1e0000d580e1144078550000120307140c228813895000f504000323080c00e00d036150044410508020800c0c6c20b001034803896450001c16070030381c4518404911300c00c00c05810038450401e0304011899000300702d030031140028102d01101e1100e00210b0520812017900211b00010044031800b501c002080d400205110303150b03050041e80e150341e071003120150000104142030702c030b20002060003012071044e003061442d60401c1c08000000b40003030388148240c03141c9141c50b43c9c001c02d140009201a22321a0403483e07040d420030581d4500144024407000d47c050490b1082503e903683d925885007544 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133414631 1250 133413381 133413389
    0xa03050f12041b081212070c081c140106050a0c030207030c0e06091608061009030c14100903020f1c0b15100c05060735040c06051c1109060c0c040c09 66
    0x1800000596002c01c81c1887c1d009a040c188040c4030515680e81c600740e07601c141c0d0001d000c0410104451605e020901c207009101b070000442c2562541030035005403050041000c94020400c20301035980400d403080c015031004652106860000d542c440c0c2a603520908202e417060b0040c003c10f40003444040304501802e117104081e8a4109807500e503030040c403245481801c00003082c000c070600d00100191001e03031444002d10070a1800c0951041180400c04940d0001d0041323000c2000c1000e0a2000d0303600d41c400b82003044021142d030890009400d01021082103088405021018600c080102ca41ca203405080c08000c0d0865540d40021071a0030117a5540d0280200505a603104500250509001d101024100c0d070449008500f02d541100d040c000d1604410740a100d1180c1c1c4505020030442c0922450b8003800300c9040c59801c0c158aa60f12079401004207001581c1b481c1c803075441585041c105030444000e6100903112554594041c0c0c6031555035944056107500452420f00307407128103480303806000d06076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133415881 1250 133414631 133414663
    0x11030a0c06050901060503060c0c070f060210050a0e10050f0109060f03060c05071b03020f0d0b0f4803010303020a031d18060915030a03050f12041b08 66
    0xc084a844400081c60014007035000d1390f50f00d8501046a5038100705980c854500200708594403810080b42c0f500344aa95070005c807851301c0c40300060003540d8002c60b40103011901182d0000380c9603143c804940c003414072402c0346015405180c02464444005411451242d04500c91400e0307180d03620a02c080880e0340a12800344030144141c2d0510028010b0f40003125020004d1402500b4141c40340c54003200f1803030b0642440300c500c40300700d02041113051008415251110480ba5000d0700160764aa032004988018421260b0400300000541c034004505c903188100003854001c02a0040d90b00120000200d080c4c3c0b21119400d140301c007001e1b19002250407a810b80c0c1d41a030180501c03c2a41d0750a69201c8141d480e54510034001e81421001a1120000b00e0000c030802401d00303002d800c0041c207124003040054000d034071650070092034031500d44000a071806d103154035140c125611900d41100c40030500907055400910280e1000780300c01d10002000380000b940300c1c250f0323a1904541c0c0702c0103240d590f1810140000780d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133417131 1250 133415881 133415897
    0x1203010b0a0302070f0803100e070806010c0f02010c0501110406080c190c17070b0406051e1302030319020a0201091409040807021c03080a0b01110312071101020d02070311030a 77
    0x1442d2294002e0400c0c03c4c4900720107a0022681d9568252542084660300040020b4140c10004040184c4541d9000f01060030440403d040c0315000034140b440c40500942040036040c1d81d41c0031079100d065905210342d0080000c1011440392142640e40d03510500c10b4800141450000c110421030318400c440c5101d14400c0b2000880d51403d0068501e1042400b0540d02c4c100c0c011020708000412074001c040e0a84102110381d100d142514002c01150001b0340a686030304002300c4000a0b501d03804160580101d840c0c4056800c56902d480004c0c0f0b03506c46d20100700c902c0300c0705030b0031665490340004480304018400d0300c500409039180c0c00b400c41c0c039000b000c8130650302030365500c00301700411083e0004010240c0054101c2c68565100544800e030030104a4049001841f0301080024150843c460003031050070920707041035142d00641c9108d03a607025803812120710400714004601c4007402907e62a0301c10700140020364441d14840f0f1284020b400c10300096003c40c10a140a08071030a020048805420300b640350110303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133418381 1250 133417131 133417147
    0x1403150903040308070602040e010e0420120102041e050d081c0209040507020705130606020604080c010605030601030807030f0e011e140d02030108010f020405010203030a1802060a111203010b 84
    0x1801020140034140540420080440840d000c0401400340364015480941d44620740b04501d440c0c013505a10201c0b4a040441c144000249692846100c541860a00204811241c80022840c03030101021044070761000a0015150b01d040c4100700d83c400d2000151a01e0995600501c44101145040203125003002c0158040021090394608403000d040031b0b0042c200b039500404103080795020381e492005030344010010400d625100d4000024400b00d04000d2003190f1600030082e58480c80030344010a400702c0407030001c08600c0250b01c188010000102191060f503500d043c0340907203501c50241035002813103040d160100e06015003420300120304107a5030354054118016807daa40380f188039040040040b004100002c4640b6071000e07004044000c103006a90b5490180c1e51380c04c6030441280c1050f494014001040160b8010040da9403100308154003144010401444890024464100a61012001c1220882c081d88403003c01100c2c5040d0b422641310440c03490000344d550000344a00405140e04103c401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133419631 1250 133418381 133418413
    0x60f02060f0405030d05010905060a050402040b0409091a010608091b150304211107050a0e060d051903050a0318050d0309110a06020109032a060908120a0204050a1403 73
    0x1d42c440e00440c152414a10000d40420a840c001c0c1c2c03288503690f40310750a000a134984002070300300404046a08518080c41c01d06405441d00a52043c240015a500403d000b4402107007074100612460880e25030075580c44030ba028100304d200b034038000c0c094440c501c0346041b40c070070b6030920900480d0020181e440c4601d5040c041c2055920003032040741e008034074030718954407494050340c6400d41d4416170712040c1204944416031840e0031210350125200b2030644c40c04001c24103250030100d4001c207059401120760308060401c9840e11a42074400c103102400140202c040c0366006000c0c100e0f00181ea030f802d1240b803100f081010f2180700042000f6115070440c10b0340010403030180d80080d15051050321411400c0210354006216401d1a511900140c0d440e000f0070410141e0002d54107641f003408180948850b510359810b8035680604090082c02e059880d07030250b080c000c90100b959992103014444249038a4404a000b019410602c91280203000c04000414003a01a044828500d01e014004140d8030b50b05060710 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133420881 1250 133419631 133419661
    0xe091504060e0106080c030c030102180f060f0f040302010e03030c060c0a0903050f060108010522030c06060b1804060911030402060a030b0306090102040303021204081906060b180a060f0206 83
    0x115100e65a90b18490340215080c040d110040584502505800035424180350405070402c94440c0709905c100180e050700c0440b144070004043c400c0c2ca0351036603848200041400787c440d10300740203042c920111756200c4200300c1c5002001500e00c00e985490780540030905041d6a030069500d040341641101000035040c0c490b02010307141d005018948031b01407540d01d8940f030742085401100c040c060340051005100a401c2401030325004403d81c0c1445850011911090049954a1100170b00f00040e8080c0c0c40300384505600301c2c20141c4113040d0b800d6030b02c0342400d002c02c2001400500c011b0040e410510f0001d855819845106400300040c4100c1d41741d5a02c0303600300000f680c0a00b0441090554500140d0010340301041528480c40042c400140d03110300f1800c0280c03800740d880000c4041030008020610019001041070104240991070304048100c01e880c000001d4181e81d08001407038400803e084103c07240c480c145107019401696144003888c0c5400c41100c1242214280708050303442040031590300c4003402c041c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133422131 1250 133420881 133420883
    0x60c1202070506070e040f06030b04050c01090602150a020f0406020a0213061d06120102031905010e0c040303081b0f1b01061a030a0e060c0a031407120f06030804060504030c0e091504 80
    0x80010707e184200c0703409045400d160820340f02481540208030812070200a205c88001003420602180b502e0061300075a6040c0503444506803104c08404280c800c003198042e17450041501c50b07920b4655482c0c117402580c0b0311003800c0992040c51480590404a803070740c440c1c081036a02c014013228000d44030f41b0f81074a00060142016400002040030b02d2079440c800e20103907007d406006c07c1c010510042a00c0c00090f110103070030100e4007005070f0043c05211a100d02c101d404480d81410070706110780d104c800c1100e20303413141180700706d015400180074140710000d040140b80c5021051583e81490320303c02012805c1324414002c2c80510700b1a400c003081903144160155178842c00035903020a0b01d68607003249600b072101c1038903003210aa0010540c0400c1603014060040441c1c074213000030f4102d1400c09002450100101c00d02e42a0a40d602c61300300940d80103402c5000510f400c02d0010380d0b84c99a80d5001001a4000d10040d14011407985000c54010207000d506401990144000e20071081241498020100041c00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133423381 1250 133422131 133422139
    0x610060503010b1e0705160b1c05060f04091104060e0c09040e030c010f090b01060c0f12020a0f0b01031a04080a050d06170f0601050d0503070609050316060c1202070506070e 76
    0x5110780141314944003d0042c075104402034807001c1d10200801410090f16000700032508001d026008469a5000c080c07a00b0202c880750224140d1114404142d1802c0c01001036500282803038140c1c000d12921207000401420705a6040010560301c456404e051941600c1c11002c0078001c1149a420345400e400080c01c020580013902e1034856103008140c00c440d5a406c0311100251034207425002d03c41c6001e4014010700e07642c242841100c2c0d065455510708014020024045811402454202c500c00c1140c8048503a11001744041c01c0004d04002414400c01d103c1142c180c003840085c103942100780d060242c081d0307601001d040d045c001203000c103039503613044809a00c000950368640021840c0301d50f00c02c0b1000d02d00b03400280c80003480c410314160030400f0580205019013520900e410003c2c00c00000c46074400c0e0041c44c00500030801d498070906600c03540c0000c00040303500324205410300200707600192181c08291510a04114600703800010390003100c4000d403803904444000356040b401880841c40c4408010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133424631 1250 133423381 133423417
    0x50607020613060804020f040608031215120c030106080703020916030f02030c0a0e0906010e0402070c05041e06080c090103061802120f07140901050d06140a0e0610060503010b 77
    0x800060105102c5911900000b0341d4003050100b5802c0042e0860403001058034140001800d28000c03696a00c40e1901c0c1c0842c01c0246000a58201e000c050001e034040802401c00d00101c0d407100786140e88107050400360b442075103041c0c1c0028901c0030000720402204c4d406804c0244583c0c414904101004045c07041100341074407000428071202d440e1009501c142038202d0740e50380303640001c40000c1c150040d100045005100d0751040c041e442c0e03005052a0010301c0700302d41c090b90310280303031604e20242c030b0450f440313a074100e03040c410080c00b00604440d003641141401c1341c041000c9503681150740d03900d0640c1152190410200001480403c140750042450114120401440800c913035001c9040c401d0784080a40d026006844604441c040510403a4000e0109480c0c0e000c180700d2010001d40142d1061140e01e11851400304103004111460f0490307000d00080306112000c80c40e1a030030722809401104c2d604580b034001c00f80022032200030f9201480a1302c00780d90310319085070301b454001d002540c0550a100003205100d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133425881 1250 133424631 133424647
    0x302120a02030405221d03041205120301060903050d09050105090907021606081f0b09060a1205090c100512040209060a0e190c0c032a020d11010f0e01090506070206 72
    0x80f98981c415a0180039800001c179400c21241c007100c02c1e6080030221440f001c035020700395040001c00e450582d5000068041d040441d0700d0702c030b0b18103031a204203480040c17408400003440c40d4100090a04aa0194050b1024680e071244111070030b024a01074640414001c5c01002c60b10f0401e24925640a1918011610340d80000346c031005280391249e00032000511900100084100440c0d4005440101c402d80c4100081c100803d1400303900400540500510000c02d0480c5182e1207903c0e8500ba04149070800c1005041c0b07019419200c00000c00311a019410207424058072030300c140222780c0c544001c0b0440110301d44841e0308102144401804c203e42c00000d4040111b10025843c461a010384600c0c80c0036040010001c42c4601030f600310340c072a841407083c0c5031188404250010300c8001302205002d190b00510b41c11001b10720014196100180d00050810600b034100040c0078840e051819098807402404071401108032201146c480308140080c0303011004010906041000e0a99248010000c508103520 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133427131 1250 133425881 133425889
    0x2040207061b030e010605010c0b0408130f05040b0d020d0f0c0503030d020705010605010903020a0315060f090509010501050901080d05030405010b040c020d080a15061101060b04061206050306040302120a02030405 93
    0x42030010b03440c0141d00e0061200158241c818070210400c400002e000040c5000e002a04041c0503c00290a1001c40c0d40004d0801c6003140c1261a4011446420040651142d5501d440b40c000da005060160386443c140640a103481c0c61100801e9500600c0715410b080203a4801054600f103000c101ca80d2022000c01144030756003440540b4070100300c680010303200d11080c20002d094a00d2079020ba410701c40c000b4818005a201c0421610944c1e41050429007410341c100c2c0403600510850b03101070000d4090010101c1c42d40041d0300124005d00180c00240a0341e43c941c01000072003030007803065081690040d0009008540150095940240544000200170040700042001d8400c0c1240c9580140c004400c1a090145c0010309a60402410801005000030b0400c400700801c4d540d000d00d0040c03220385d8a000720300c0d90b403d4001402038160004815102d0399170300805804502305502c80c10310f0f242003140216150030005202485242c2650061030704940c03030003801d24140e1004c100441107000800010895440b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133428381 1250 133427131 133427141
    0x1302011112070c0909080304231c020114060f010f050702120303040b010801090807031409040e0303060103061a032214150a02070b0403080703061806030c060809060703090204020706 80
    0xc0c081c21881d42d20301203803508203030b00c0840740c0016203454134080105010804010959074000d40c04a0205405891030f40e103100340094800c41c511082c4900c403503c1207500b80544010302c0c4888150004d20800000300c444540f160303022945960007613164800840c0c00c0d803003140c901510780d01c2d9041583c600901390700454108490140c3e01c4070294400800d0004002220181500514031074008002e054029501c1d0092031040440107420440900e603480d101c0d12000d001c4990b1008010b01c10003421851440301c030345a8000300c804030f0110f071030036900143d80d4012031003075030311041c0c190920f03842c690311030a10711110403094120369440c003050b03505c11000419184841341400d60400003046082308080394044400002054415900c3c01440014000303102142c403640c00a5040c103010750603540b408411030040040c1c1d48100740d403103003840c828000c1040b1a4804001d4a0080608145c5191602e0040d60000f03401c0d03600e0354980c2c2c45000050369140c401c0d4801c01e9101d200400c050f2500d51141c0301c840c1616 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133429631 1250 133428381 133428403
    0x50d02041703070b060d0b01030b0c0408010c0c03031a030a1401110a02160b19030f0e03070c03110d031b06020702130f0f0c090905040218070809150c0313020111 71
    0x94000240b0000380f1201c06084c913800308040325075006071140350359490030080701880000e00d00a482c001080da102040410744026086140007040b50700c804203001030006005010550200345404841c800581d801c0c41d0200048401030010200e400e00c0c0c1c1c1e00c846001d200320a640510f950795068442da040900d00082000c01d000c0c0d4003d10351000c00142c41c041038a0554440640b01d5420844070b90000381b500b10000440d281d42c200014000b070710315684030240150450619940c0400240201008800040c48007a240030700700098848200b402402094a030304000039001c40d8280350900c1c8030320f03500c41c6503540042c824007000d811b00020794003003103174440c00d880502915602c603689401076031894450b28115409208051040410511700900303180100d00880503286e40f580c0024046d034655641022050002141e0720a140c600302178003c0c00007800380e80003411030040c1c400c40190107106030001400340307440c1001c03585582ca0700000000e0700512620200c0c1400b030000c0b00008103100a111005500c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133430881 1250 133429631 133429633
    0x40203010e060c040303030c020a020d0303020304061104090c03060e0606040314030c1501051e13020f0715090209180706120e010f02030901060803180f180712050604051501050d020417 81
    0x384d07007985400740603a0241a90380c02198403200100c1c0240c0c1c0d0f421090403816406080050f541e480b00c2c01c3c00c9020f056042e000b64412040050001402c03240c80e40004035038207190740c0800c41c440d00e0b10381170500c0d544280c5005034414810b200a101250310b07104951030710414581264075010362702c1c5201d07007032034082282c0981181c9c9402c010003040c107010420243e6031103034201034155101131100140c44c3d070380310b10180030303890380d0107e0450103d0801070100c4050b150002188800440d0310a4004050080584c04034050700d001c401048410510200c0c0340040398001e005005883e041007022150f801c6140e110010554455080d00c00b6001c00384110710f0503c029030000b607130302e14100380441e082d110759900680f1640d000700b007800610018604401001c400498641e00300200c1040000c0c422600d110039282d9500496043c080d40b260010003010308110314034428800c650f01d902c00c000494500301c9959141001c840c0700c040d801e40c880c2c8010844040304030303001400d2640b203203400c845000d494010314030f00d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133432131 1250 133430881 133430887
    0x20d230d0509041a0a180902040e0109050d1103030402060307050904020705061b070c050603040c0e01060e09150d1202031e0403020910060f05070c030602030a090b0f0c070308040203010e060c 84
    0x2032810075004002c51102100c0d070784c021003104200440c8051902c0d01c030380400d6180689000807203091981000040a80080081c415a0407540350a40203152800040b940e501c47c0d030340c0d0f0b401c2d2280504458241d10f070f030030b40107503055030740e0354003800500d40c03000307001c041000720420440301140c0d80c901c041d04c0c0c614002c000401c182e25080d02c080010640240901c0c0a03000709120010003d00010429003c0d02e405940c42912a1540c1c50f041c100c480594002c40340d07036801c0c00c0001c239075503601c1100f82801c00b5085400044070340764150410000f000160340b958100400e246950013045407030845441c52991392040300d14200d480701c180c196403103101c41e00a03503080300083d0410640c606071406039003284d2400a40d0b00c0540c40e044018000140c08800c0100b4418080341600c14030502c1c0a2100040d60030040955881c031700b10400c500106034110b02250700e01c041d031000c1098100388070b450501c0303001f80b0000b0501d0190540c809551220000f08226415901e9000d071406144081c0032290240354138001d03480e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133433381 1250 133432131 133432147
    0x1020d021c0c150b0a09020f04030f140307050607090f0b0703030203100f15031b020c090903041d070f020109020109060e0d0507030f020a060f05040605030c09090108030c1504020d230d05 82
    0x95840103a1b0b10551002d8014048814071684150448003201d600409544d20718030b0754942000403403100080795205000c007203034003414408003140841c400d4225a54a05859480301e01c01901d59200380605805990140030b2240000c0c041e600860300904400c1d00c2080c1c0340e6071084400808080c681186031003829801c21692101d0b01406a14610740e5441d010600d03100000230000e540700c80013244030f4424401080842c605040030b108880141c82c8854054441c42e5462402804101c1e090324804001103502c13800c0c048c07084c41031041c02c004e039505070f40d0420081c0c40c0c04d008442011780240395661001d40d0100000000d07004100003801144150741c0055880458010411080b41550010b418840300600845a55902000f228103441e1f943c20041e450380c0302e40790709041038020921000c2e005249140007290044002002c0d01c14079440508a800003048204500384495040c3e0740207400a23510900040041d00d90780f061f1086032204203000f4444c0181d50b1200d45860303420034214010502c001a03100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133434631 1250 133433381 133433389
    0x2011506110705040209100e01052101050a121110030609020715050c030903040e0a061520011811010311131d060d14010b030d0207090b01020d021c0c150b 68
    0x10b0000c3c0412a011410030413000089000b044181ea4210b04105030540b0003092680503c0594080d4091281d00301c00d030858a000820b8103807000c3c0101440b5003041d04000a040c4440c690021a65900c68110302c0c07a1a804400c1c0501c8010f041103002c01e045d107621006c240705140384050000d00d070051815281c00005219064102c075406440c40c010100100b042052098000040f031701200c0303100c80740d1314081d034416542038024841c039007110b00440715241035106401e43c04068001070082ca41a0301034003480e040d0685088400311910010751255120040c00403a12110607586180810305001c00d400c80e401c0c0518102da0b100c3ca0309150030042c0f000c03090001700304108003003c8800c0a907401c4400360030120b00089406040103401001c21b046002c5040c10700b00c003900800d041003400341c02c464070a03101c00b001030744581940c0520102d1070700c0e2101d0406158030010700307003150035001d0700900104101c022652100041185894052204d5110780300000f82c07080e4003c0701c000c00320f60710004803455800104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133435881 1250 133434631 133434643
    0x60f0c06011e08070b130b0408010e160614030a06150210060803030402151b01020a26010506090d05120301030809130b060313031202030405150702060103030206070f0201150611 78
    0x155101d482c01d04020700841c0f9000030301c10b05641c010041d40346c507888100441c44a95409401261210f03001040000b103240d4150024a221840e440c180c6806044009003040d0284051041c03500151440542c100082c01c980019500300c0483c1c6800f0600356255520025604071000e900c40042e400303412050b45100040c880c9101500f0316034041d504e14101f035000290f550180d81522181c038140003402310300015414042000300c0c4401e82c02551102d208802c01361034000383c04004a440d503000400a542d854403910b0300d5060b83c1c0020505030034400306200b813022100541c0d408880510a94001700303145104040558021842440b085656403042010300181002e03259540c4c00ea54202101a500d0317640d0f001c10790b5403201d0741d10001d002d1940e140c1400c861407081c0a0300350214500c00018801813000c081000e170744203444407119940a850b4a8001c81e642d400074400900141c100d8408540410f1103031720f61848500051002080d41c41d9035003800054889a68800d070042501c0c007001a4202c081401300c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133437131 1250 133435881 133435919
    0x20118120807110c0909210913060b04030f050a2001120c020604200a0902030a1103010e0703090c1e140d020a0b091504090903080a29060f0c0601 64
    0x20300743c40070044051550740c02c1600307059200303044005c0082d0441608000007080801101c07045221543c0c01400440942c0c01025070500130310385200c44890303039802030240b6001c40b01ca2048441c03401e455605c0c0c07501d4041204004883c2d40c02600d11040200e00200d107500504400f0360a5480b0341c50000e0009810300d800205900076441c201903201c3e81c110b801046007980703c0e400645031644030b9920303440180d502e0212640150712507a80400800c40d4030080d40513501c16200103800b00f20a0341c400070040d11900007480b80c1054424000001011036200e508100c441c01e10445001c0005521502c6a04458800811104c2c5603503911400700000608030814140141c0c00781c1e44d20900003029004241d00070402c0c05884244480010407141c0e80d05c400040c4508051032142054031191540355a0019001408054001881d13070000b01c0c659044520600d050021000c07500107421164840e5000b40520310720500348c3c066000e11924a62020010082c02503200e10320140c42d4543c10302403002c00050800709 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133438381 1250 133437131 133437137
    0x9020405010e01080603060403180b0f070c120b040f050715050702030607090f0b130503010c020d020c0a0608161e0c0605010e040209190603060903080105100809030a0c03020118120807 81
    0x70f1244541b00810407642094061406030b41056144200c0c00e0350300d40d2580701e01c0103110001003000c011005c2078060186148a0311000190a170f890000c40c8102c1d11150b80640340c0b404a5000c2800214901d03c41814984564203032104959600c80034980c84120071040400b14800081a0341140f806001031684a0b4030f41c140f03962101d0400c0514070903042a4014103080b8500040c64007003c444080203d4010000100244500542c1c3d007002500c503643e80180402510890480600310701e007050b0400f041d40e2490340d4200c2d0540d903401c6004801c0307441d9001802402003140c80484c2a50a04c080940c0d07452080d142c16004041500c0c00d0300c11241c05902440c0200d15540910005a46540d8616080700c1c40041d903921b04030b080c44a840003080194001407103d0b280800c0c1104058100c5803c5040b42c00031140301082041c0b40d40155803071103040343c030507801d500100480b01002780543c4090780703014064400050100c0000340800c10301e0b81c0104050b64141c0c8034580340400c00ba400520250f0200c8140703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133439631 1250 133438381 133438397
    0x1140f0a030503160503040e0108030903100516050901050c0109060e07170d181205011a040c02100c0c1401060f0b0705030a0c1e12080105030a0b041e020a09020405010e01 75
    0x1d00e4240c0c0f0b90164903e12400000383c2d246807024000e00f0000d03a00075103c05441b403602541c2d14011143d580e03100e041e03d0750281c01450742ea008200c03a5881a58460f03007640c0000c5001990199040b9001c1d8042c00f142e034140181840440c1e140502485103032120f600c0348074001101c0300b2501409141120540c40700041256a482100c100c401c0802e941b07071415a141081c100080c801380c04071141100300d400000b20269400ba801c5e00f8814150481030081c1512042d144460300302005003c1521440c2201501584c4003c0c0340c00400902580902c01c004400d03d0f2003100a040d503911032425201c0c070907102891b80e45a40d800d2000d01440405400181444903049141000341c4e51503d80301e01600c0c180c14148286005031805000c01c080e100d10030720001141c00440300c003440c90003c40c61700c0c1d145d50150000d0b0084002044c9814000350083e031154000b00910300590340c07942c4180c1c00150580316000007052030b102d41e100503116074030700700c0161407070b03003002348e05d907400d0500040070140c400740020b040280003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133440881 1250 133439631 133439633
    0x903020d020409050613061d070b0306040b030f160f05030c0d140307030c06110405011e120c020105040311061306020c0f010e03030a0c05070c0306091b08012c0303010e07020a080301140f0a03 84
    0x1c0c00e0044400300c5150603103d53303e2000203002050003a641e0354060080d0000c00001d024081401c00354003003409800c10046494035446104c1132058000c0d070b6019401090615841c1ca491521004d40910448522a0705071003001000e00319000b04400b1800f00e038189801c103040040b14055021114075031102320307060600d4000001c010982c115070b03400760b10300410350165000344180b2002c2e00b440c0d40e1a80521140001c490002c0c02400308582c140c0000d0700c044000101c000c8040f9841380902c0c4080110640442940c40d0000254060708041744944510325400741d0001081c09420f011040c000055a1245405046401911000c01069040040401004d000101400d05000650390004400502078005280082d048581c0c540d40c04c044c1314140380c0004010005400100790701b109a90403041d80913044200d481800c1003a200b40c1141d0b042440140200c0320f40c441203a50211300c80c412a8200c0b4240d8848907115032080c3c0040c84450180880c903000b90070403400000c00c400050355070034155480c1d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133442131 1250 133440881 133440883
    0x50108250c050a02030303040c05180603030d021308070905010612020406051207031404080d06050d0b0703090f0b040804051e0108010e060109030209160807050304030903020d020409050613061d 85
    0x40c503030340034060040d9030000c64103002080003c002e0700303a03001e4105c9a4a08040c10a400c039600f040c456036101d80c40c804003580d9044500700050b409107001900071418003150001d010081d400c21101e56184507108200042d803440704010540003050341c07200005081d410148000d0004c001903841c1840300303004020400407141e224044428248042c11703200e81580310080110302908030441c1c01581640d01000b40420700c15000024211089580d4041145641d100244140c004c0504005499841d03d80002800765000c1c1e00200c1d5801c1c841c0c0300b110400c0240381d070b076907801c0d54007998241e60465003c81d00f80003505002055181e815a001c12402c102c00c00400020600300050040d8071246a0a00c04509140d00902d80e80300135560080c02c001d8a49009540250050240c912050015a01038042440c0034001c10890f806682c15a6414807610b0664090082c0100c0d00c0d0001c980040c1d5500100000ca202030180c0c5005101012480013000410304005041d0b0344003094100982c0d0b004c8409200c0020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133443381 1250 133442131 133442191
    0x1050105030d12110d0c020c030d0201150b07020312070303020919080607120b0d0501050f0a02030105060a0503090c0603070c050606010503010b0405130e0111040906150f1107090c09050108 83
    0x24401c03c0401c02d1090024003003014084c00711441e03d06410107041803035450300800d820801000c240c04172020110000c000b01e0a0342c6810006640140400505010000404000b4101c2074009011130301401d803284140e03a0b150744001815000a540800c1d1000507103403408102c002e41809040f0110b2850510220948901018180130240301203006a81d0070341d42c01e03030845000840001d20003074040c501030504a0290400b19441e011040c5904d00150501415100b90b03810385801511180c1070902c010760031385050380040d000348858030458503102583e81d10b01c001540300360701e2542e420703001103507510300341c0c2c90604007030282c0d41072001c10f20052003c0c1c44071100380c3d012220304807060089820140c0c50100103080316001401203501740004401c09004001c000c000300da0310f0020400615507518156115150046084400030307a2000e10508000d01c981e2540090010309421340c0c07059550340c4804802c0f64a481e6941020580b000420404ca6803c107400580c000303580400c200c7c03088090540940024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133444631 1250 133443381 133443407
    0x20109020913060b0603010603021210080a0305030417040f0311091911090904060506010813020f040b1906020d02010f1802100c05010f020315040e0c04180b0112020301050105030d 79
    0x1209103442c4000707008141e0015680c04a024003c25541e5031580030040280d070040000c12100e610710301c0400e950385003030041c1c4022650f815001e090300390700700d81e4200c40690000d04280d569406804111348070048280040c80208040c2800f10a040d01d507203001c0d102c4034000b9060314030606002c000c101c2d500c14050854003294003140ca0011f0f1070211001a91101c2c025400d02d240c212500004200c200041c982c0050700a4400b621550b506584080c80c0e04680841c0c03600c025000000e020b101400e504164000866142004120700218242d846c0340134000d00072984400d00603030010304102d80442d02841483c004017100c007403e1001e850014100304002425250083c0500745884243c2121485240c9503054290702a009201c01d00b9140c1000010390400d40302c8484029640c5d071908030a161501c03401c1d1841070b003207002e130815100340b008200040030110110344280c11600304150004070351f034280902800480c6400c0074110000d00501d400c40300c1c1600854000d42c86560352020154015503006001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133445881 1250 133444631 133444651
    0xa050f0d090c060c170d1103090a1103071505030a021c06061d0618060c030d0903172806150305100f080303040803090106090e0309040c090f09020f07080a08090105070201090209 78
    0x15078004083d400040c44a16504900b402e4040127210007240045082a0294001c840740c180c40d0801c5010141c0740c5a0522502c683c10041104902d030641c007403000f80d9880780030040018180441c1d11042003601c018590001a500e076036090a020035030708881c00d00d6040d80447c20a1800c0d11440c1d0100d4094803c48801491400201400c44829030b10002143c0000300c80e441a00c3e00ca48501e1042c001400e14440100e0204d500403804020350711250042c03600c61810419100e01e604181100c101341c40c11400900301a081c1c5400d004150030f596042d00d454907a00c959400181031805426866800f075040c0c100580018001e9002c000c034000003c1560b400c06d40140080d59203441b61146540140703059030211580a080480c101070509000c80585040d6200351400d02c00407010210803900c101c41c9002d0b10391800004802032003000d496030b01620340703a07241140e914a0812a03440c2e081783c94100c000d20100048040c01007210740442801440c0d00001180024054480a0f074001940404000e21034010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133447131 1250 133445881 133445887
    0x5101e050f120c160510050705070b070e030f0607021605030106050306010312180b120a051b0901020a0605100611060103030206060d05011401030602030a06060c0803010b0a050f0d090c060c17 84
    0x3c50b500c800880d044c246070210402966000c528002e5105c10001d83e03e454100c0c03801000030b0000b4002e034129045580e03c00487c00650341d608200780e40310075644150582512614181840418080058a024555a80041042050072612815451041c0d00824040d9040074000c000c951000a00181501d51044980c1d0484140110884030741071030000c100e201c6044541e00080c0c4200200c000c1c40b070b1118260303400c6030030f0342c4001c00c08099030000d07070b2800241040b1840c1821142402006000e04410500c15102ca01c10103440c1c13076083d07860a0341e40302154200700034104001a007129041e280c4029402c0940100c0d071440d2000b070f46462008195070f000d91400010002080b02c01e51103510100058006d04140c0d507100d05115000390400c40c0c2d54428586402c2d00410403d015410100c0b900d80c1c01900103186a00b452000c44c0650060b0080c50306206042c090203240101003000384c100c031a0942000904100e050800c5400380d076560340300c01e09103d0000c007000041040c040c000c0f000320900b5100c1170b503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133448381 1250 133447131 133447141
    0x91e03030d1107080a0306030b0c0304350310080c010c050304050d06110705060a060f03051b030313030f15021c0b010e100512071b0b070905101e050f12 67
    0x1c2d80744034440780240600d000040003904180c16078060001c0d00e020b900814900d07542d41d107040140340b1042d10085e0012031910f03000c12640311003840c0d0450940c4065980c010500c0c00341c00204641d0400d44001c2280811140c05000355102040304000707000702407038217800307208440d120151030b4440c41c000c0301d000d01c003642282d4050210300c0d0024241250200e641325510038550402d0750720b0b0102030303545202c1c003428840002644003200e50711009890f00140a072000005e150159203c100348507100d5901400140000300301d10859440d181c0065000702490302c502022860954500103d1352101c400c081c0c07044c010341072340c00443d02480e02d04210701d0034002560103114005942c4180340106443d80090002c1294524650180203404420270980702ca61054443c900c1c01d8454461603600ca032291800b0940c1f48001c6800407ca0540202150a083d804140c071071004c1241c100654500e100850100180e26040600d0b401032100c040000345006401c01004846021407442080c4640048112181c0410f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133449631 1250 133448381 133448411
    0x40e06011e05030901060f080d0c06060504110703030b0a120f03210b1903030c1b030b0708070813021c0c05060a0207060801060206060a0e071211091e03030d 69
    0x7084411000c1031595480d416801c0040c0b40c3e40c03040b01c401906500340100000c01d214030503a000181c03000345000d00364040c0300318411070307070b0416088003554410340710800040c40c2e0300c80c0c0c440d0065810503509450703a40e2946003405000d0b5040398945601a80c4410420030000040e080ca000409600403001300340080b860808032030310540004041c0c502000744140d18882440c0e540305001195040e51511b40b825958032090340090407520010b0b000c101d29402c1c00780010444481e80b8200345114003d5000305445c1d4036520705030382e8116040c0f40400e00b22420321508642100b80c140d80600c51400c84d140300c50440e8007103502440c002e194030b1135080300c1000850030000c203c900c01c0054140600307119180c0301d420304025682d40551013040c01048400c0008550b85102284a500c5903e01030b00d0500c0e000d02c2e0210725805044010543c004002d082100c0c9030704045a4059004803003041c1a0301038072041c4500c2000341501c000c03100d1001c0c00d0103001d4034011544000c41a81d040c080c1e50100011940c460384072403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133450881 1250 133449631 133449647
    0x20030406080402031c081906030c06050c070b0310060e030c0a0302100909050907240206060f010507061d0106092a1701060201060e0c03011410140706050411030111040e0601 76
    0x115900d0150b07041c0e8026080e40c000701003031007110141e202010048a01c254131f4201c40e0302d400080d000000c401c1d0140049400344008080e071122030011036039140e95036035041c10a9002075501400e80b4201d11010085240c0c025480307440c1c0178046018007440c032080b40001c0c945100d2480024080c200c050002804c0c0c3e0300400580004020110703052101349040d0706940c3d00d17115039000f090710b140111750f009484040d5039003401c4200003054004120a4a44070b040240112003030100b28100720040000d81e0000d0600c6c0103001d0a0b1142c02c429400d08002d21000b1402d603000c2c0c2d04422201c0e45040140e0740701c0106020a615050400000e24040340b49406007184c080d482136024104454160307000040090f81584038104454500584000f40e45814501010300d101c04c2c89481b040384002d1683e07910a00c0e1015505030100958104806032008484c1c20b03101ca030300004410307100300d0f0b501d004010920a2030071031140d10b14001ca00030050b000c0c1d410001d0388603014501400440c4015440022a5079008402c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133452131 1250 133450881 133450903
    0x4090201090b04170f0609060c070615080d170c0403080903010b0a031202070501022103190c0c030206060d020a170c06030f150f0105030c0d020702060c010209012003040608040203 79
    0x140b9503c54450b0124014481d0300e07a52100ca0740708000c6651518907012501a014040d07000c0030b0032180e200e902c00219150800c0d80191120b0703944061140950490f51a540d0040040c00c3c007601020700080300107409802c2d0101c41e56902e0501c40304002c01d203c070a00844081e250300c041c02989910203200402e00400020200b50f800c0041c40c130011082c009251044100c1100d02e500325900151151300498485031411000c2c081070041014a6500640c510061640800c81d8000705180d110001507840a40343c40c817042c1004505809041e405040d8148100f80c0c0c80341c000e41e9140140d084650201d00644201d03c1108440e61801815558000040c0304c4581c0c0d05400420050f00c0c0e081c001c0c00506842000d50302d00031603000b81070144940c2d0400c903288151000d0140c554605665800046000551114031034468030b41d13080103002c0050369040e01800d0030103086000103813a00000b100240003550620b40034901108a800190f02005001088a081d200285485092500c80c0e00c080392a01e01c032681 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133453237 1106 133452131 133452149
    0x609140d121817030604140c03011e080102070305030f060d0201020606100c051c030b061603030b15190305010b070309030b13150506030127020409020109 68
    0x40b0902c0009400d03003802c148a042659a440c1c0501001c245002100010041c070150f8102803290040c007410011541d0700301c1c103200d040c0c61824001442260b850b8882c0c105a13a804c411002c400c40300500d1240029510340c0380740d2901402941044451040790744051001444a1610440c01c404240e0181c0150010351201c2c81400910300340702d980b440c04d00c658a0030180000e0410040340a07401072208500840c6101280000c1c196200210a584624000e2020020390744a0309000305803140e05080025220758803801140021104051600c0560404250011148000c00619060744104c0d5400c01081e2f89903444450580200140074002501c4942e041c4002684422419003107810100403c482401d6960f904a950f03040703480d2008845d45480c24401a400d003401450b00c01c0d03240b2080130b100c3c0c0b500280180340b181e81e00000648515122006041964050140305024000b011 = true := by decide +kernel

theorem cover : BRFrame.Cov 133273381 133453237 := by
  have h0 := BRFrame.cov_init 133273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133273381 ≤ n) (h2 : n < 133453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
