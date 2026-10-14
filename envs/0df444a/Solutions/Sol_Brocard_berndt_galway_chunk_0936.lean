-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0936
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:08:50.660805+00:00
-- url     : https://prove2.me/submissions/1fd8a7b0-d9fe-4aa1-bf90-9dbb828c29ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 168165467 ≤ n < 168345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 168166717 1250 168165467 168165469
    0x10902040c0801050d12020a1202061812090405040212030f0a09080c0a03030507050705030f10060f060903020d050f06070c0204180b0c0a0309020406060522081005130606140f 77
    0x1a40b54142d40c000f03428900002e500f50784403080d29001c00301200460162514020000b60505d001503080c41d540d038002c0040b8240407a5104070310104420240c00c0d54403040d00c8030803107140102561032901c011680001d0565660000c10000f0686072000c07003040c0800a4031160305001d0801815220300c056942c00d0034281c8034070704140d03600e47c0602042d45c80b1901d10400c10000303110360010321030700b8407480a6401c0c80d9605d2010900e09586400e400601e0b8010103030800d0500d90500c00c090003410030f412440d08051a00c0c0b4050042034060101900800c2901030100500508108005403074a0341412141d003894205802042c0055001c0128425401d02120704014803443c41408a02500300c0b0411401c1e884450701e00c80c056101d4400705080c1a264440e0038007607612440b41c01e000340003545a4998602a032000484030b94007010203100148000c1c14203006038000000c41c118042c000c00400512a12030460800391820f11003c014406810710201140c0d008007100c00204d801c2047d1080004440188 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 168167967 1250 168166717 168166727
    0x50a09090209010c060f0e01050f011a0306100f02030f1602120307050d121d010207110307060f120603060e100c03022115090718090e0c010815040e010902040c 70
    0x890943c005900c100100d030120300a07a000ca200364090940000c1c903050034100e11429030303034101c0703812260502603401041030407c01140040000101c00031685146008800927001c00d00d000740e442c0400c0b00411848141e80d001708102c404004040302016151004c2ea9245101905003400c01c034090000c1518014480c0e00001c16070749007580c4500a0325141c001990211040342101ca0141200e82e22010800d0308141c50315800384800107810300250340c484260920320032620b600c0080d607000c0d50001400704081c1e41d00002541e0019064a401e14445000b0b1030030002a1549402c003500a502d00080030400d0400060200300030402c00f03500f80044041400103804034010140030741e4603030102c038220518101b82001c900b584002d035400c803002004d65420204224420072079000d00816041c80e460440304860840d004001e0070148001c0c00b01910181400d41c0315260100110f040c080c2500209440f20054403130b0104d4100e0160040107044032070100140a40041601640541c1c50002c482040c28410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 168169217 1250 168167967 168167977
    0xf020403050606011404090c0e030d0c0c27020d090323120621030304030e0a0b0406050901200307020418020a0e070e040603060615080106080619080303010303050a090902 75
    0x10101a01c455511500199004c061401400381d07141006c00c40820010b099120b40d015100040d03441515030043e09007854500410710444a062040360030844001602c01c203400d509841505016080c15500c0c2d80d0014580320501000031546800800d900300c00506903800641c80c14040c2d560a007907080c0c440404000040e02450303d00c0034500c1000059140c0d1244c1280c0703a00540081c00e40d01042d007621166591103846c494014441e60000003c1c00300341540120012000340045805448891911a54603154890343c403e0106001c03010800182681c01450412001803545843c0040301908002140e00c0b50b2154100300d01c04e40c5060280546000d00c04140007605034041c0040441a050104d200c45000e4001c09460812000200400c110f440300d0107242c005621400010032843d0401c61240d21820241180740108011030340104a01c0341c1c080011500100d0698070304503450f0084c0c0c8a488603030190f40106021f0703c00000008201765100e0003c1c0070f0400c2c075507900421140c48113626810391090b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 168170467 1250 168169217 168169223
    0xf0c040603020705070f0f1502030301050d0f02010e0d0308010609060c050312090703200901050d051c050904150806010f0e0622090f061b090b0702030304080f0a0302010f020403 78
    0x522090103400e00941c0100040350158044411540c2d450019400040c00e90308a10000464030204100d0001400d20150400384580080c509640c182000b041c4202030a007005411314110107441800d590040010f959480700240c540410841d4908001d41b00a0302807140100090380d005001444078403c11a4106503588200070750f1030b0080c0d100500c1f0039148050010710b814047d92600100040d100c03401200c514140d207400b4002041181c04009917444141d201038025400c1c58a507800250380828200f12403800038000040c1c41c00120804c99082c05000741b084e401c10f1500e54082112156200808201e80c1301d0000c0ba03d59a1b29855403e42014036442015656a03403080440d02501e0131103a400240d82200c0f44881a1400491b070390410b8540882d41034610401803092001480380c9401040c02c4401e01c0602d00013504a801c000900c1c3c110b01c0d200340164004049410f03011035500b0f00c121001000d114085800300c2031003050305074a40c9400c0ca4200d000d5840e081264441c45020300a0307604590b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 168171717 1250 168170467 168170491
    0x7110d020303010e1b04153c0e06180f010212030a0c0302090406150906050c0c0111010b040905150702010507120e0709050108010f0e01050907050d03030e12030406050f 74
    0x1103030030101c03100c00c2c40240c00c0a5640b190403070100403c2c0c8009014000500c002c2c462002d12500014015060107140c000e1a00d03030150000c4500d030000081d4603900411044a2042300007011000300c03c942883d10442c2483c2d12403000640e9905045190900d10141c0034211042c0b00040200310040e41d071a2620034481d48145011f02c002180ea90322a4041c04154007141409440c010b91040090f04448280d00070000c0d40040c0c600204e00b140d48020090b01810702401c0c050b01d4400500b480581d101c5040e51268100301241240030710381c0000b90000b10401101030018081c0c180c942ca005611071500303020034840101040001207006105001d02030082181c0d840350000e041020394802c014000150b40120300c2d220785c80001584007080e1140c00c6c02082040e00000d070081c005900315043d0b410305003940c41142e0410301482800080401d0110840310120b4050314820601e28040d4098599181210003c3c0500051500f01440c58001180314501c01d903010059586d071012140e01c125010380d1007801e414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 168172967 1250 168171717 168171719
    0x10f0501060c051506092a0403080703110d0e0f0105120901050601110d0503060d1a1807060509060a0509011202030c0301032a170709020408070504110712120207020d0b07110d02030301 81
    0x1f901003010f070451a03000800c00c9109a1203042000500d0b841039208458965000507040141940f224050810b048a003014146480004000500c440e0071044214440c003d10b41c14180350741e010f002183d080341c80c0d4607403542c00c9142480000c1d0003020100c82090114510340d0000034401800300f0034000805e4a5100e5600f0341d02e0700d4050214403101c09400b180d01c2c020000703001301c051007490304070382c0318000800c001c04840380702c0c3c1995400d0403001d40c040028020705106418080d600c00040c0d4198000030701d0b1840e144d14181004030741c0211540262640c452002003030010b00c0605400840c140c034055400784500d11600d101030b000304860381c5100100c45d28030260901807000b002e0348611039014218111003100f501d40c00e40c0300803a4480da005401642c0512070030402420140603298824000c04543c5050007003544450300001541c02030201080004051a040701801c1d03415240c07941c1d000340c40b114040c44e080c5051078442e5070035100d440209a50020703050348041d00055012820f00168050760442e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 168174217 1250 168172967 168172981
    0xf060801030b04031b0c03030f0903050619110a0e0301050105010809030315040b13050f0f040c06050c03040f0b07060b0a120b060f0301050705031e070e0d05010f0501060c05150609 79
    0x42c001030011030800c19080010310912105138a8981580d00400c0f0182c0380900e0b51801603d204400701c4600306020421100300042000481c40d5507000c45000c22600b03d0790824400c140051403010304c1c0010820001c0342401e80765601c04003054030b03400b050b002048a40d0300c49006503861001150314040560040000a42c42609420030000f504009030000c264078981a00041198003000e1074501d616070b94504105030720314207000017034008543c540c06a00b141410b446100102203640100d4090010000d080b203900f000070800ca8000f86448032440c030030f160b203546c00156207601140c3d080c0c030102c0c1090002c03d950300c0c0040c0c0700341c00c50b1422010980c04030346554a002000000604150740401c840039004030703584007030045601c541c081e03580c3c0c40d60b81d10701345901d09421034406c40c16540340b82454080042e0795402150300703507400300c3c211a002c4d016440c528115000d08881044400c0c01418040001001c0c0d0300521303025004d80c49041500c11382e00f64449004688201181e846912440c0500401d42c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 168175467 1250 168174217 168174233
    0x61f1a0c0a0b0a0209090109140711100606050d0b030d09050d020109050d08031906060e210106060e010e030f0c0f0303040906030807140607020a02012001060902040303090f06080103 80
    0x880c00e2201911401c000030303141c00c0590721003200c03d028020740000300c0048611700406600d000d041100010046880c2403040284060801020039061040465103a0070480b010002c0443c00b01c18486c2c00e00007203450303600c01011a003100c060444400e0030030205007481e15001c1806040038030b0030b50354549200c2c030302801c122148003809001e0303041c48031003600801c41d40c0300c04003918640360003000c00e00d950341015404003d848000d80502c4409a140c203500b4000c1d60b1380030304461880c1c88122054690601c40203811f40c0c50140150056003150701e88000082e00719000910403502071400d884580c412125107091544035000c04001d03004075005a80d0100551031700f41080443c40c0e42c06802c60b801d01e9102c518450494100e42c00a4450720008a01401000040c40a40010203840c402900a0b4104514003139551605c02c40028144a440d42c1010a41b0b40d14080ca8808100404000d106c0240d455140d40020340c402d0005400013100c1c3c01002c5841501d904514089a500e44d541290503031940d15051b030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 168176717 1250 168175467 168175477
    0xc0b0711060c0306060c0307050609060615030703091509060c09090207080f13030b04050604110409150506030313030f0512090307170114070e0f04050903070206030907030203030309061f1a 83
    0x140c808001d1041586e1204200050078034144a20010301207802e00c10703000740c50f01e80020080d0f44034441150310041048691403c0e01d40140c4a801c02042100451070011400364040170302c46650740c03400c00c28905010380c03a0020010540c00d506c800310a1529030160006a10441501400840c8204040144050100b004006007000d4000030b1440d10346070380e1142c5c41d410f0306075015116507101005000900180100d0052204c0b0115010041c40c2c0c16035035140c038041da400704640d40c0fa0b0b540303100090407500c01340200d41d217490580c0004114561203240c4000e0603980010103980c0340c41808040350032100d041c8102d400c03c8030001c00078164146880707500c40400d840040146425500c9034049000d45030a240c03454012a03035511500b01d44d54000d420b00030b80440d540034441c03245052106100c10801c0c048202c2d01a60f8040da04107650340d446070b0845203420900c1d03100a41500c0300000f0407010020101e902400b03a14103160724a0f1221400400d6101000d540c02007803040075040b00c1c0800c41c0d00c04600140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 168177967 1250 168176717 168176719
    0x4030807114201061b0c1e03150c02060f101509080d0908010b031c0c020a080f010b03070806090709020a02010e010f020a092c180604030c0b0711060c0306 68
    0x441030700044076100e0300c41a4802ea058680900407001032006a420060520701c5105c0c40151325000d14032504e99510446a6109414210b01300307102907098001000c104102640e0848000fa9146484216800080c02000c036044c0040c001c1c41c4c04903499005403901c450142d5400c1400c601c146d81803409200c0f86c42502d041c801c1c140a0300d0140090020320900c80785508803a9503c505044903d810401401d480120b00034030711907004440620001003583c541c0341c110154610700040c010710148045480b07030700c45400805142c071440701c0b0240054415040071100e15005c0d01038400c020794900d000765881005076500d14035071700080002e0081d405554080c02880380c09100205111440714080b07401c660343e500500414070340000d00340e1100e0307030081000002080d600e010404908100d24031010a0001200c3d054840d1002c20082403851400d80c0039444080030350800c0d40c070a818140390140c4000401c07401213869041a10008001a0051424034030320828000986805d550b6550031504585c0024415 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 168179217 1250 168177967 168178033
    0x108090a060603050a1703090d1b060203041506080304030302030a1d0904030e03060c09060301090b0a0b030a200306010e040509010e1501081006060c0602031b120403080711 76
    0x51000304141c2e0041100960243c0060048203110781026a180001450700759118501001030001120000800301035002c00c07450940300c1c89c42800f210110a0341d050101401e81800881448140300114407620601c1c0503220040020701d40c0d6850040d01e030b0240d4400500503820921201c61400d020301100c04c5902407007090320110f50100340019000360003d43c0c0c182c000600d040c03090702d450700f410031035a908071400400c010f05003142100012001c1c070050007401d000fa80c4075201186141c581c006803a01a07c0700000c4103840f071a03c8070784900105440380080d00e0120007510007002555803182106e002d154180d55140c04004040244009072078054650802e5641c0c8588840c6030380014481c869000d080d1070060035455141451140c50080d0f241c04c1e21700d07000e00c0c00c0d004100310358000001800c1564007600142e1a82e944007000e2450343c00c0340b100701044660001d0040d100f641c001c28094402ca20907107030500e0a80b00c01c0700469806013041c0260005074040602c80052402c101d0f2000002d040c61014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168180467 1250 168179217 168179233
    0x50a12060f060507030e0109050a350a110618060319020a02010f0e0607051e0903011a090708101a041206020a0206010b09131d0708160509090c010809 66
    0x346401c00c592540800001071010641c0000c05601c40e00c1c20360350400900e0a804c40300c1c100400100c11200714420443c810522048918450f80c00704043d90455054010190000d130302d42d841207840b0700b6052000c03a181e41c80790007580164a440c0c1d0548071402e03503a1090380c403d04c00110512541341d002501c40011010170b0f620714010b07c1c046000400700842160700202d0741810b092038a40c291506240d0700c00d0302e80c01c800100500203501c4001c0d106503c0d80e4001d003041945510703540c3c00c16442200742d941e402d9424800d0b91446240541e4005e0308000003034130550340d50740d20b0f000121a0310809540c008d42d403058141040180100c032030000f01000103594802c92a00380e440030384903200d2030200c0003101c140350049204d4602a03014041c444c014580b00d140540f4185490000413120740c401600d02c10481d0780c80f05004e40b804c0c2040000600d8010342c6c0c044481480c4c56144555a1350390300f084060480448a801003030f241408002030b4040e41c03481c8020112042c20f0030054a07034608c02040751405105045c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168181717 1250 168180467 168180479
    0x41e050f0109050106050a0b0315060a090801060605131502070303110c0402030a0f060f080a0f0c0509041b050f0d080a03020f16051c02060403030b0109180b03060a0b01050a1206 78
    0x82014040d0b4450f4000041c082d00e00401e10504020540c000c00140d8424001c01c43d00c40a02c03c2c01c601008401c4a1003a03a40c18038440903528040035801511980d80b9216020a00329000b8004007103041541900c0303803520355103d9007203800340c1201d81c021005800080007040001c1c012001280700030340480582c1c1190f20108003060403600121180303006240c88a8a50004800e148102400342422003a02c51185062800095886901c414002c2c504404918118240403d00c007801d0050040203022205034201828114000d41985142d00f80310024420300044600c1c016111a480d550080c6c95140380205503101d281d555000b0031403003001d268003048212182c04a4400034000c040d20001c142002000c40d044c036503d80f10440418400800c980b11424841ca5000541d16600582c14034001c02c10080c10401200c4d0240785030b10500a001d0402e00700b0a07039010f10b405c010803100d419004c4500310341e901c542000564501030343c41408a40d040065041d981e100d10590b0140040c40100860f071700766142 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168182967 1250 168181717 168181721
    0xf030204150305060f01081e100b07140606040b15030c0405060406171509040807061b0528050301030b250f020c04060302031c030f020313050d020105041e050f01 71
    0x407080d500081c0e9501c00b0040d1614003241548410301c0280780084c0d4601c0c0004800b01e07541200054080c59075003100c0080c41d50071003003460801508a04040c135465507501d14084983c0700799400c2d0450140500e030001611030070240301e400c900e08801010102c0181c00c00314000700380d0384054503181705044104408a09070f203508000300014492035a9240f402c202000c06020049405000c140c500d2890041281c0b581d6108080e4940180d000205a0f81d20122840c080c00180245614800b804219130903200460790064003a0a41e41c1583c100140404000904104010200c80000b0040707001400140040303140c44030303c182d00585c20809041c50314012036405001031001d04414000800072041000240d5040c400401004015142402401e01310360010b5296250b2000d81491004101111401144290015440c0e100912401c6640e4142003a0582d4440c005210a40f0b0620a080da082c060324414426188200c1e0000f200418181c00440c07061400d0034503004c10703682c034491022075140c2c1042c28 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168184217 1250 168182967 168182999
    0xe0a0b010b0c030c15070216080d0e031009150b010809100507140409060609050306060d03030e0120040801061719020f0910140109120f170f070201020c060703020a02010f030204 78
    0x240345d92148615201800030700c0c2600804840031240010356007048100d1001501c0c030350805460800c600c14600d00c0000c64500a03c0781d82c204907942c1824021000d0200c0402c4100002038220002c0c03000400301030056415050a4404801540c03144a1000b205002644820303049491480d03c0300721340880441c2c0e04400d80060f0406205541c2e5000100180c82d003108005000707040a90142c0100d25081c0001101c2d40c0c2c0c0214042d040c541c440001d58001c0305c00b03600281c1c90b06804080204540301064400e213194004c1c2c052940e6039881c154021a40b0708183c2401c140f05200c81d00103090341010f5644002e0425482d5000704d0304440c1d04508100c20750f5403200fa05115043d02d01420b0b8a076850160500300021038080103034180b000315101445481c2c111499610310302c1d044540303040710380140d181c83c0f01d400d0802420801c3d07014007c14403440301e00c126401420301c58000d034202c50310989040100880c0d071160702d000401607444100d0983c015402420130350107a00d52401c005003030a0780e510840d8580449 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168185467 1250 168184217 168184243
    0xf030c09040501060908061f09060305031b0303010308030411010509060c010c030515010f0e0d0519030801060306150f030b0a09060501120606200c03100504060e0a0b010b0c030c 78
    0x1041041507400c00d03100312401015a441d240400c20b280184d0b254540f02c0207008541403042061400c040b204140c03a11400400d6582c40801203180d0380d091280e03d82e008540c0341590f51500d484441501c00f00002903d041e20713023002d00c1600e10344443d9941c0740250a0072001ca814050207200b5407240755118005050036580000010035600d0500d807004048400c0102909140e0302200c041d10300f40d0340c1c0400c1841e0a066681010701400f81c400001a0122a442c03900070503500c82c2e803401f01c0e601a002c08640030920300c00d8851405c2d03a6200d42040d001e0b2401d40c020b080d00040b00a5480360314911845080d01c44580c11f00300001e00100b410082842006903800540c13540e038880382d00300141d50388010303204a42d4901403c100816030909000405080d0451600d141c0502c20203d0101e07054007c2c030440310038110040499011340c6100c4490300282004481c11303101549015502500a0f6010480900c807951010080003d682410101c00b4141c100460880342c52005014a0b02408810003030000c207105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168186717 1250 168185467 168185491
    0x7051c0f0c0c02211c1b03050403051603080d020706090c080304050f0415121a0a05060103110a0e010f03090605010b07020301110a0c080703032301050102010b010309170d020f03 78
    0x7007076006001e50090800710441d00813400c00c042c07204404011800d154040c0c03915140c0c9441511600044481c100a446200d81003e00c03100d4001c10180c0000c0244120380c882c80c1690203080c1c440e00b0400ba20402444046d20840c020800c8140d5419660300401d00c0d1480352400065206075501c40c20740d2800680c2040741640c0c8001801d04c000d10f0300c0510002e076031341c0481c0c041c41510203592034103e07c41c030719102c0d402c082c3c01c03008250010405aa041440304054415500540f4545902c800010308026540c09000c03d281c80d802e14601c80008044400e02d800a0b02c680d2001c1400500445100407460740000415980c0c585c01c0001800c0ca02400d0300902d4104180c549075151401010f00f140d00101c55241c15040400129001d260807416200d503c0e1f4000074010385a03001170400b030300648001403d07400c4296651203001341c101c074100c01d881c0c103a0301d081c0c2c000c2211903500380040d02200c03030415000e08246558074090032440c0d200c42c000c220a0342c0e4090054203000900011401c250030941d000c00441c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168187967 1250 168186717 168186737
    0xc110d05031f0e07020c090a11070b13050a0b0105150a051b031c0b03010b0105090d0b0603030f0406320d05041104141503030a0503010b0a0c050d050c060a0507051c0f0c 74
    0x847d03c80d040981052000f0800c200780182d40070103140911510100610a024100014180c0d20101e103445810603003203000d0701c10050359031806030100c2c182405618882c0c0a0540007240d000c40c90002c2d2000402a80ca64918244040f948110142107940c441419032204120102c0022a00c0307904c41d9204c81e10301c4000c10004d0925041500b03660203c88258100300c0b051040b44101e80d60744401c203000340d800510082482d121100801d08501c1061030040c003500c0c3c002800a4142c0c0d112440c1d180a40c4141c024107210380070030314460402110070a6180c0301080520007400d0540b8960f004030f4006215110307940e1080701c0800441e058135101300f242e200203540b1004002c074226440f4a020712044045000c0d5207401c9a200e005840e5000602452007040c0c8003007912907250340103030b01840c403890b0007004488410400c018002d046078440d0300310090070b00820000c500e81c918180a0b030343c021509030b10741a08141c601007003c0004821070f00c03a034440d240c80320000c1c1d011503aa881400744988265942160748 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168189217 1250 168187967 168187969
    0xf040f080f0c1203060604120602040f0e04021816031104050910050109090c020303041205122e0e06010806010504090e060601110a1a090102070804090c110d05031f0e07020c 76
    0x210942403c0921091410020041c15588420858042e103000c0b003400c910795545410004005d0080e9048624502c40380d40c00490140c50540c46580710b54400c5801c1c3d00300c2510030442044007241a1815111100000f0a80e0719072400b98100c0c9908400c25850141019640d4001840042d0f00341d40146450700d2200c001d001950340100600081d066005003071003030b00c0c42c040d4025580d00c001480581030340d040312041400e240c426011500904100c9003c5565070404400c0031000a81d010703044650081c404111644d0000340d0612001110602800f00780305a40300780065a0702e01c0000d003002d0420104000c04501c00401d441620306044000e40100a5403508200141405891a6041e030499001400d004005214800e40c0e1400401d1481c004150303841e042c900b20301a0081d0400144a0309010038040740c1044568048064246541e8031450000408800d40384c540e441c0f00403031800660100002055030454586910b01031418102070784603e43c0d6003a9003c4524419100080140c0000f5101125 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168190467 1250 168189217 168189223
    0x91a09101508151308030a020405060712020705010e0d060513080c070503060a0e0c0103151203050d140105030a0605100504090308060a15091707080102040e1902030f0f040f080f0c 79
    0x20403e106107034070070303420281c1c120ba076108103070306004011980000008080c41411f030166001008090300e015101c101c1450b1140c6100c94005c049401132151b0000040c0c5580308001c2446500c4010741034150907082034651002a00008104d120008114100c007000a075840300107011800c2c0746800b80852038203000415041c500094030742c9020f1410401405400d80b408100180002d409080000c5d00c1d04081d640c20214460f6a400500060004203100040c580c00400030203d0740b4030044200a5200c0001e1907030680c400c2809010f070141c3c8525903010001d0a0b45c1e03c540e0704000f0f0350001c022003d80e100002000c0c3c5140074070403800982200240003160a00c81c250780041c09207502d89080d40d98450320020101c5c1501e06c603030741c5031660030b940403d000c441c2840301c400649010300096640e240c0301d0f01c50f400300c46410b854424501b42000340c2c00303035405002e1090744d00602044100309070945641c41c02c1400024090300030782e0400543c200e0b4900190350302d0002c02d950880c8032001c5403039107030310303c22541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168191717 1250 168190467 168190483
    0x50a03031a090a090515070e0103060b0f1e0c03030106090602010b010e310203070513060507260c011e0b03060103020f090712020427091a09101508 65
    0x222114082501d40050703550050126030095207075400003001507003402c0036450814407202aa10360034803001403040040c0d1041c1c1c1940792190a0300c042c0003841d030300d003244000c3d445404103000807000140700b000751070350706600b003440300342242d46040e03007040503e000c410306540c005c2e44900082081c200b810003004e6028010355031418424240465035070702c3d00001c102c0304040451544010540d40100b9402c0e9045908000c1103c403010300119220b24041e81d0180003030740503035a102c4c1d08035000391f000514184079000300c2d0303210b6600078039814122404031019861a0102c2000800c555018403103510491003d201d80507441c031001040d003c0b81010301a02c403084509200001e030003500103030b00600158071036600010020b00c06440c202c12581d1178020469010030b202120543da9030000400180a0300107022480c251241100b0a4901203200400364007103803074441c8018000009030301c90310311100b440c840c440c2c0e00142d20019038800d4500d40612074102c59101d86445048190b1034001d020b51042042425 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168192967 1250 168191717 168191741
    0xe062107080706031527050c0715050108120301270207140601050a080a02011407050304050d050a02091608040311030405060a0809060105030708061f0b07200402030c0703030b060f07050a0303 84
    0x12110482241d41c46c0c25101c2c4100f40403d074030f511038004c5110706000f407040b02c0782e1940111401021444440208001d48070070703c03800503640f282044084031110f18200b107a04031140083c481040340e001901007140e480d590818514150343c03d02c81075001c00c0e42c4040485100b03800201508866040c03004100120400f60010b8019520242400340180d0f007000c545540d100e05240320340e8a03a03815203402031840c8280e410042d0082134101452003000b00000b0101c0d0418421508180da96840060003400c03502005001c03000180c03040040b46c003280c000c2c82d81e00182074000007640d140903140c9000c18029031260003014002581d0004000c0c1181e0140819409888100c02070010207191803040703541d400d80a00580380745010000c49070359400c00b4904090051052200c01074a510390750800701c002d10110401d110700c003103d40c46084602c0c5072034400c891080c405e8011640c02d28142e03071001c800400e6900c003d5a0480420021090150042d00280030503030b1180d0020b203403c4040341780050503140c844e5151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168194217 1250 168192967 168192989
    0x30c14010b13110f0306210604110f09040201050309100606120e03040302031f02070f06020901021b0102070b13050603041103240117030909100501090e0621070807060315 75
    0x8078801021a004c5440a504401c0d40903225160840000c1d038000102450105410444c0710b49801d0030b6001c19064402d030700852800715055804400e000d56a8402000c560703011403c080040c0040d030199001c2c41c3c11035001c03c00c840700410021690b00445071300780c00602c0401c010800495504130207000784280480f000f0051401d061659020a558805042212041420b50300410303140040d80d5055401ea0394000f294590040c60f5810110020350000c100346005008480c0481403080cce00385070414085c00180e00400a8519159044074581c020702c00640343c641d0300c5403002403960b8404c006903000e03d005034480158070034030400301842c080d811058210b507450003035000744000485044041c11540d40603003044e0480c0d4416107541c114490740e41195440201039040c041e1410061001c58190340f001e803030ba120301a0b11030760040e6015604440596114030300380c40301d000c483c1c400e02000b500035040c40220b0340f110351506812420000d80d5001600003c1c0d503081c10424020032001c51500521a40c110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168195467 1250 168194217 168194231
    0x30c01090803090d0f050706200d0f03050a29030706020f0c1512100305010501050d020d0809030705031f0b010c150903120e01090c051503040f030c14010b13 69
    0x720649034010144860b108a030310811540500c40c8512040420030b0b0310a003038588203500d030300d8050141c0390a0400c030f03210010b51440c000c0d02080c0010307003140c2d4041180c5607603032140504d28048000d0b103802017610015944401089500b1061074501110156024401d080b16407200070074140381a21560100c01150300103004c4c000d11000c00704138840610310030342c1c003801c2132034002c0395640380c034030a5501141185020208010100c03040d0341e109016240705000038030159036584100704400141d01c0c4041d40c81116030b0803850000300810700400c880302000e0141c5101c641e0765400a42001c400c0280b80c10448080e8046050200c1c0302e10540d403460740c00b404c1c203a801c0320f680d40300c5580b11406100b06080080c1c0c1d0322800000d160003070303c1000c10004540001d100304080d02c2d08190182141400840f010506440d02048a250603400d101a820505079101e0959540c0d03180c800c81a045050b0903003d0040c90426400869050340c444240c54120400106084900354141709110f40b00b9041118107a1034180 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168196717 1250 168195467 168195479
    0x40606051902210a0207180b01030606030b0307090510080f0d031811090403090902040602070f0807030209042306100510020606031e1002040602070f060309080a081302030d0905030c0109 82
    0x49244a03a600c00e0312662a01c00b1394a081e45800f902c0c1e040000512089141391072282e000c0d0f001811070980030781e800d0000075650682038003038401c1c40c00d8103076050300107007400e2001050b00d6002c9a4031880d40c1513110f241320303070300c0300744604210b421a404803c60b00031144102d8519058001e030080840c220901c1c1110512548800305030010070811144101880743c0824203052281e414000034044001c0215901d80d920301001e952003806218600d00901c120a0001d6101004595002200d030060300458065a4581e03c00c0c2890a0034003008600251003400030204050800c005841081034500840b134660400c000c2048200301c070b0400c001194002010001c19880100b11080c0d10120300010784860189807400b542000f08100e01c003640e035440807400245c0140c0c005005c20841310708502503905036071184c030300300d00780d907141100545101c808000200240b0702c60008182d00c01c00a601c000c80f1007505600090800100f60200782c0080c44c6000305010615040c04034103000340c02400c1042020b4a8a2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168197967 1250 168196717 168196753
    0x924040302010302070204021b0606040e07080a08090102030c01061d2206151a04030308100303021203060112090f052a041109030d111209090610030b040606051902 72
    0x300000741019004603001c1c0131901c5540548070305262041c0c0003c1c0e50341640c940380d42d60f9902210340754400d0b41001499803038480042580d0065400ca0f1015006000e1241c0390395919034810506c2d20704500c02001030a4a400b028490304025111403280f1000d02e40300340c2c221500c0304030081d1440d048209240d800041d8403003803008072020716503c0b0702c02240140300d01070941e03000a810781c003a500c004040f540d20080258800000d0046d079201c1e0701c0703103d01500d030481f0fa614a01214040100564040e8181500708060302c005194003078414500040a00310300b002c4c210039140c8100301103a0500e003010a101c03c00205005c4641122a42c10505003051303c101e0400c0d015440e0030400a000e6a91005c0030764001c10701c1421980d22620140c103c8142d403219003002003200c1c044242c0d84140c1d0080100c130940c0d65488401700d929407600140781401c82c0d11840c0030491955042c05182d02410b58034102c292064840c0c1c05513038000c00c07190701c80e162a010703c0c03101c40780d00480c0380b80003100310340145410003210300c13640d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168199217 1250 168197967 168197969
    0x1903060803090d08160302010510090e030a0503090c060a02031206010509010504031401111315142221061a06270402040e010501021501080c040e010b15092404 70
    0x8032040100f100702c0c0d0500040b80d02c1000d04c4100911a070004517828150150040d500a0403151019101c25580e2041c510480c0d0307014101c03000941041080f081580e100d00d0145400c0344000094698450118001891940c080c109072030140c0c00224400e501340d214680c0059020342d0a08019107000c0044000928500c910f020003440d61610401e241c9803d0400d42c0464401100250000d59406202051504080c0c00c0c0c420784e01d100001c008500000c61040c0b80201c002e030381d0f10496a0038a11700d00420446041d05441078005c07880703c40d80000d003140c041060104044000c569144e0301e084182094002d40d0191142614600d218904900e91030301c0700700840e01c5201c401200484c01c07008403182244c1c4032429000c1c0551003800498003041c542c0940010138103c40e8242c089588035036100f0b0b5400c5400c0e2091250400f075401154040e01c1c0c1303003043d401c1003100440344400090301a07050000100c00030211440010444400329296565080c0314101d06060707620704032411000c03845e50bc2000c002d4816 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168200467 1250 168199217 168199219
    0x1519050303040504090503090406090b1f050304030e031c030e07060507020604031e210f02010b0f041d06040803161403071d13091101030204030f1407080601060302190306080309 78
    0x1945c91a6414807130140240c54003040c008100b40242c83d9103035202d4010f4000c91000610800d2001360402c0d6459000020014122054030741e64219521030720280e0f40e4800f929030064260081c42c212a008440b1030503040c0003a102624002182c0d01042050391401106422003003e00c01c0c2000118050b965450907141200d0b0301201c0003d064880200002c04520064002015400380700e818410302c40181e0010303071039101280c0d00c80c4a145080d401c00c078261400707000065007110920040154904068115007101e164121680343c12802c1c0d005681c3c40c1c1072003101c0c1a41c2d90140882030144484415686502c907212524200540c8002a18480d400344009030900050181c05209043d010101409500d5100380c001e0400307410710030f5080c03140b01401044100311022000041190640d43c00791081c3c0c0c0549800070a1408051040d903218100c071509008080031510520200299141c1c0812607140a80715a54003d0f880d2443d2500802101003503491400034141010700c14440d9900002c285e400c4128 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168201717 1250 168200467 168200471
    0x1107090c0519050904051014150903030a030204031208010e0c032203030b01080c13030303020f0f031018091505060a1703040f0806041a0a020c061519050303040504 72
    0x4814602a1803900c600c0318503010002448031046070083e040f8002d898032220580d001d00040c1c0e01c81601c003200c5046800340710044101462090000c1c1030485481c0d41d4141c60001341807900781c0d01c030002440c5402010320f250000740c00150610030030103d0640201102040e09001d000d03941400c84a0b4000c3d0002402e4254290002c0300040750b4101d4180c0407640c0140802a1040c1c0c66507509004001c2c0c071460b02c000c1d011649407004284025000000c8602d14040082d000d2551811a64120040d51001c50306140c03050040c46401c0880f03a140d00114040c0300006001d403401440c1510500500c110f001382e034888245000803003030118100c03124105001c46001c00020301e5544980000c0c9004d840768002111181003514200080840040188161201ba001c00b421080d40c03105400d9540d002210010314065007001c20040003e01e8510168104058403c050704000d88034104034034161044030300020741c0401c00380501943c02e124100c01080003805101000060030500460750304d110f944103080c0519 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168202967 1250 168201717 168201731
    0x60c0318030209010e01170601050f1306030204051503060702011b0f1101060f080f030c0d14040314060403030b06090f010e0301060e0a0902041107050d03020306120a0f0605010501110709 82
    0x3031090160002840e030050034100c182d61128150340c1c80d1035090107100c800e02c51012145040709400a61141228802000c142101c0b210209201d403100141a905144a44483c40072005a9441c098140301d254071180c49860b22001c40101440c1c402d0152a65041d649000c10f0700c001c403505da1003803607065141e50030f103c4081e00608000310f41d807410404000340c0c0c80d443c01034040782c0203107032207150002c89480c0341c01c0302e2620440355251a101d22801c46400c40f1540030514208806003d0000b80300c040001110041c145030f41e80d01e41d0840c1002c0301c00e0704001500b0520400c010140c040c459002c441c842030300c0090030601040046003400810b00c0049050104d1054005940c2e07400b50004030181400034050350301c0b81090218403003c0c0a42c500224070403808c21003d16034032041901aa41001d07081130042c4461200440b003a4001d50015000c20341140c00c485855014078420840402418860030b01d06046120b2806c1590403290183c000340e0400003200400c0c00d01c0c4900042080c11346200001c002884 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168204217 1250 168202967 168202997
    0x3011509051305010305060c0f03010311030109050a03020102130603060305060711011104060206100e22080f0703020607230d0f0209090108030301080609010612030c050109080d0222060c03 83
    0x5021903100340c2d402180b4004400052841d50091812244214112051503c40c807112403100d0003440440301180000784010000b1640035400201480c0c0094000214211943ca55074100340c100e45056015039000260000683c1840084ca0001c00f068541000b61310304564825448541c040c0c020302c1040101131101300483e1083d80301640800b00f021300c3d981d403542d40302070203900c80004507005480c00c1e44244000603902c81c52034121f4031401d4656049003554982041c4c11045204440301130382c4145080c03001d100c549842c2c00041811500a4004144618041c540201044041c0707491992109490b03075950030048000090300c00c0304840700c00100d03183e2500c0340d01c80300a0054a4505600417814000003403016408001103050b08e858400b52585642c0700c006c0903080e178450384912248080310032005000329100b000c1d4250800c0c46240081040101900c80724519005040202403030780c3d000844442d500b01300b0510403078002e10580c1c501c0407103181c50005031400e00002c00c0a001d01003024522640c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168205467 1250 168204217 168204227
    0x20a032006040f0e060306040302061810060303030b0f0307211401020703080906070302400e0108010c0201050103050307060908070f0503090a082e0e010509030918040305030115 78
    0x442401074076040e1203950710a0440b8451100340324150091107002c0c0441e5680c200070809a20685d05500107091a440b100c589402c04410303441c5480960054000103103c4d01d046001e004000c40c065034011550500e200704000d100d46402c202180b207584008800c00102c0810001e0010070b0300345031000c220421150412148a003502c1502800c154400a00d00c000c1540104d0018041d05413442220295900d115068007284506c400101c0c0e10100c40d02107034002c0f14800c4a4001c45001f04035566000680403044805203405600105c030b4042000c4014084031a092044100002041c4000d0040354556101c81e900d92155240c003801082c1c03200d40300340c10b01c03480f0b004071084150310440e0411a4811820820303200e400600391644180d65035030000070780102c00501c64581c2c441c00824405c009920a640741592061700b45885610742d140d0200c1d8485020a01c6818816240d5201459440c00840e080144c4042d2100c683d0b011010703504144000300e07510105690648849000107001004da00c1c4d020b50b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168206717 1250 168205467 168205523
    0x10f030c12090605150607050705060703030b0405100806060105040f050d0303020715021e09060a03050403030627110c03040605070807081615020c12090d0c030812060607020a03 78
    0x40d50320b0428211600b0403215900c00752040c10b4506072589802e0b02001040000d00c02c202000c1e04c00d0b440135000313004030b182010060110314428140050048001d1012a0589100700c0342041001e801200402440f0014000c0c5940300c20b00340381003440c060901e422000b00c0445ca0185901801c5582e04c0e0408260007581202d2185410a80003c44402003c004d20302a500450803601c54138201620445d80e81842e006451688000402e0a8105020290124024507009009408141e00c078a80000d22881403003d460404103190140c40321006000410f2050321419039405085100402480b010074501209070741c00d8910a06e8a560b0340ca10600b00072045000c3c4280203800c0e1140000c100d0800e1500c80005103401d84a5039200d054804502c1605040b03003d58000f4800581101c419058002802c0340204046d010051192000364980d80354621400903030380007110005030000d5a8405040387c005c05c0f0794440022100e9514013040741c4d003c108555500d11000740612804c1407107400641003120429 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168207967 1250 168206717 168206747
    0x10c0b0921040f0603060605070b0a0b0a0609030b0c040f032603010b04050102150906190f0513050708010603050c060d1404110f03070b040b0703020a29010e0402010f030c 75
    0x103800d41d120652180040c0d4450b119185520b420310b48002040d0f4000e0060800300c82c0c1580761035007400425190900030500041034a051a5a1020360542d1640c404040b04080c000300d41e07521540c0303400e5281c22207001e00060000c0000c4401400100310106008a001c8117903940001c07000001c80302806c07082c3c0e40050f540101c00c9648804030000c80c0020b10000a0000c480c8264226a2040d44480860b010400192490065034002c140000c0c980041d10b10b4103483c001d03e0100c00500c0120030300c0100200c0e1000c0d6440840d81da5808145002d10000b00030394409024180000c100007882c507a18907603640e1240c00c1c102e004000102d0b0b501ca952050b540001c2c000d984001038001c00c0e152a00d4425041c1c69090130f400c1c030540d016000f039200d031b003000690310742034945e003052a0703280a0910b503200003141c0110701c4c12011881050790241c005001040d984001d02c4643d40c2240050151200e00711048c40160000d0441200c41e00c204400f40c4e0380005070310300384600ca0038005940711301a981120300c041e1202d004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168209217 1250 168207967 168208003
    0x1050403080f0610230c2505090709060c080d05100303090f0b0405040b04061e0311060c060a090323070501051006050406031e0603060203060a080309010c0b09 70
    0x2105140e0004425840b4402c006080b002c180d0750281000300030060000302c0c0c07002510b40c00071601d025811070580215200040711440c10704510014035440c0c10000c01c00f0300301000d03100d01c036064559241040e4002401c3d00701d661240d50701d4590b10040c00c104584c8036400c00c21003005d010f1800d0010f03103400c440c7d00c102540f1080c8003e10340b501901074118070610040380015410b400024500e41486007c0064690442015141c41c3c03600b000c00020341216001c2640c0140d42e41d034001840c00303501007001a1140c2c1890f0b0201903900d1800d1410207210403d40b003070301940c03040041460100d8086492039000c80719010004104030507040486003402100b00b180c8000e203250103201d001000c0b44014106c0035220790000e2002d6a61140b407064558074510456001c24814071060007202d001c1d81203000700603500c0d14081c8040c4030440a050698480350b0041d51581e9000041c400326003441e02e642000b034a58000114906503240700000d02a007118540544040c1940d0080b883c408404d001103980003014503131f2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168210467 1250 168209217 168209221
    0x28020307020307030f0503060123041d0a0605040b090601051e0c030d0f090b010302011103190504090b0406031104090c1a2a06010905060303070218100501030e1e0f0105 74
    0x1010b5503a902c02c100607008a060780e48010002842502280e114100603950484003590320751140c07600c44529a210b002400092101041100c0c682d807480d02d60003201521300c5450300788044440111561754014900403410308814124a44500e040b090b0802c2080c1780056883d00025010100c000c2d0340c02c040e4402800000700e4016404000020f0700000c42541010030140c5041d00111007152040b9900400c40c1b001040104003641c00703802800b00b066800804e40349040e243d50014810104508140b40100f00c01190034012070700c00d4400d04203080000d84003089031904640300d0407800340d280c10741e40d80700d43d460310960000c000301c0585a000500b801c01110007200f480040c032005a8204020105050076100094803280e0000e08801d9005581d16015040a90a140081c005007800400040d0140720800030400143c9600401c412442192000205242410000c41d80c00d003106070700450405040020030050f40710081a184802940305003d15452182c01040c103051081080c9682e5003940381c042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168211717 1250 168210467 168210481
    0x904020f0d05030a180e0609070c0b0103030810060806150a051314040b0a180b0f100201050a0e01020717030a180f05011d1b0609030f1e03040608280203 67
    0x13914640034191202407102103000720400a0104610810f0540b03464440800c805090031030032190080314900e44107584c45001c0e1101002a10203a0085000840c076108120360080340320290300c003030712151505840600380b035400121510055000d042c1881b200240c0c021a1500031812154040b010040d0807c00c0c0c0e0f56680c084e035052550045103030282d8148004181d6038a894078448090b105d00c80c001c01c10764186030809100900c80c0c084c041c1d4000c1060341410581b070380e0307103000c054444095600104c1c840ca80400601c0503111011400d0440742e0050241f01c000440c0c04540c1e25156001d2291180c480d0390300102c0c0b401400c5400030100700010701400c10010f01103850100360b032203401600240300501d115802c0c0040d405030032500b8101a00174a0a00301280c6030020031360400c15000340b8250400308041e00090510055003004000c951010341e4049848141400a11300740a44c000513608003403803c14081c18000300200000f44100161003c0e845101c91184048913029451004546918101c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168212967 1250 168211717 168211723
    0x405011e0804321c0e060414060405060d0905071a0706090503040f120b01050303040608010b070515090102070303050f01050d03180909080306011b0c0504020f1902010b120a050c0904020f0d05 84
    0x50100e07042d134041441c2e0b2402c01e002d2010702507442030150a03d4901881c10680820001a00c10390544c4400c0401c00050103940381c20103002c00049040002483e00045d01d01f142c604081a445410711083e41074884040480d58000d5070002c1d9000071010031040c840c3e1a110f1306522558004401c180070a44020441240710929080c1903440b803031000f0031698841041566031700a034400c100000b81000014020410742d24051301d009446502114440114801500305200701150a130f9842c0c0e601103000800d041c0c0c54000d894000741c0148101005504180111f0700500c110f41019060268050040866540c1c2d8210a0000c04640600f0440c0000d203240c01c0007994401e46a40d400030301081a04200b10500d00c400c404060340c0038051f07008851510341480301035001031404107050b240c00e100c40b030741000b0b091014040e07451803a4000120390701d1503420002408030f000312013070150b482034424600240e800120300341000c000f00c9031030001c4c0d51107100050b1070f0f00040e81c400390415882e0b120642008000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168214217 1250 168212967 168212983
    0xd231b090a03200315011410020a0209151008011503020c0f0303090d030c030209030c10120608071d150f06043f0203070b090105040314030405011e080432 68
    0x314241d5140f9017a45040c14500b82c400c0c01220013180301007002440500c0d00e1041000700348030500513102c40035407c1d000140e180204890315659007030512064000c070b143c43c41a944001c01142080d80f07165040c002280b4081091140d48414582c3c00140c0e41140c0208009500b0900f204404807aa03e151a43c3c58a03200d842400f8184080707401e101c03c0d5440c0701d0190098a50240000c3d0042c15911a040300b00700c8451040035070030b41030103554010360400380301500484004e0010007009021041c5003254440110030100112400403407401d06000a0a034801903815250108803545844403282c2c10002e016842998000d0000b94a801103001d0902141011028107404940c0581100c00c02010110000141100000e500d504a100d09019100680014042802042c50403601f40b0751640d41d0020720305000e458a000543c0702141c10001c0e50381c40900140000e003200701c040c101042e1440040d001c071038042d00040261126249402e010410711860150348500340a50b500b03031202c50507515480b0808 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168215467 1250 168214217 168214219
    0x50c01020d0c080904050c090604120c0f2303030d0920010f0c23190b0a0605060712030b0303030a1e020408030a0f0306050301020d231b090a0320 64
    0x104000441c01d40c1c0640d0100b1401900070402c2ca00e80440401000b005001c020404042c15101740440d003850348511000e08054048036144085008680c2031895903e001707548a1003c00e816144140306c0c07085400070f10b480d449401c84404081d8002030300028294014154030071885c600e041d800d5400e002c50a00701d69400600d041003820541c00e40d4004440000c1c0141c00d2102049000d0a1100001e11044900348541c24940c4072803140e07859804001c0c01c0254601c40f03655102c1d0101114818000024502500f0500c0c50b4410000c0070305d000041100b600410340c0c041c201d2107140840c501034030301a401080c2086001415603942c0e10f80300801000400c003112000c481840207141c3c4050070b03040e034404c65099400707101c002c60030f040841c50101c0d10150302003900402c1644820b40000d064a0900240030411703200940400c00c007514044c10602d49030110030000307030051540b0a0241c5000555111a030594820740140d0340c0300480004070740782c908541c5c002040d002c0a01a805010141c0d000c081c0c8403c14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168216717 1250 168215467 168215473
    0xf16052b031b05031615051b070c03140a17091503190f051506070c120302101401061407030e150c060c0a02160e060f010c1406100603020408060402041a030a050c0102 73
    0x7040420b010803900105d5041d000340c23054000e007403603412040c0007402c2d00c0c51041944942c1c40c0c0d00ca039140704442c02914004025540145590010042d01080c01040d00c0048214142844075650000f06950706442d1075640104002010a10912901241d002c48841210051001d50385103a0440020102110b68014124440c00c40380c1b401e140400458a0194220980010190400b4442d074540031608004034190701c00e03050044840c48403802441d82d4003888518450196140080203441003c5d903400e02021403508010040000c2d81004400301c0400003030311600ba07015800f850448113481560780c910220f00c103801c20000000841c500030b1a0041070f0f5402d4402d940c80449070120700c82d0043c011103c21200300300004045041c542a0203000140515092000c9152078907a80303040002083c02c0c40590f00000204520310a000041a0080c03082c1d00d800c614062504800a4541300003600080c451074130390100000d06001d000910740b402c100107064600c03007661450300590380c0d20001d0f951400340c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168217967 1250 168216717 168216743
    0x705101803050d020306010915110d09030323040503011a0f04020403020319020103020d0204030f0308011a180d1e14010207030903140f16052b031b050316 68
    0x5005452030820956040e101d160404070400d550310084d420080029040080180002030b145101d0301c02022904015102c1040100401c00058240b40c140c1c07070104140401da5500300000380c1e001170b407201d000e465640d5070008052600c480c0c1b1040c0c440c40d40013551560030480300704000040c0da1500c120050040701d8680701801c1490a21003030b40035a11011b981a00100141408080c005058040061052400501d0084410300a03000ca030040d03003040d503000103c0340c120401c00d50082d880e1805002420b1720185000304a0300c0c4600c49201e4812214460101142c00070381e691078072030650840d41e03803003044518804c001000342016203008032000d503070700059600d410300300070703410b1007200e105a4041d80c4610340541151900b031000440400c01c1e004a02c110510b1420401d002d01c940030729005403c50201e9807078545000c02c400c0c031482c1c001c00042204500e0a40c0c01540c6d52400201d039199060812161080d680600c02c400340034040c0300a00580400200d0903030074801880c10b09003c6200d0901c0405503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168219217 1250 168217967 168217991
    0x203100e0f07080a120203040519140405151e18160302040f0303050a051308060105010f2606130612060c08060a05040f020f04080c0a060807050a0f1202070510 70
    0x1030081d0f120f02105600121240808511030781408141c4120130b004403032030284e81341e001c2020100480e909042c1c84c80ba4103001c3c4a1105543c00d07003548101d007107400340502d003400c01014240208403100c4030301c00e151132001d0100146400010404c001c3e0300610100e080e501c614a09004040d0858012030700350007420414505078004d2086e907040c2c1c3c500408002e901402c543d0191560390202401000b4000180300d07861480c03004110b1040a0081c4001034612035152a00143c04004007281407404e1110a24003040554a070080c0d43e0507840ca030b2501c19425480d50303004200301ca103030b08440109241c00c05801040c000a81006204414031440d800c004205401c841184c2404007601c145600822202c4108410310f4070b038108004c219844080145000c0c0a828003070b440f0703030180e8880d440b0f640020350700e42851f103890300f1140d0040400741070840f841e11b080140100107202e503010000500c0000c00f224000d140c403842c006100806d0600d4119070320f0b502820240c0d533642d50818550103040c2004000300c84 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168220467 1250 168219217 168219223
    0x9031a0414070f06030f09050d0309030201060614030408030601030b030f070e0618150310020a0c0606050303040302130903021603030c1704060207030f06141009050109360203100e0f 80
    0x111501c0410100f900c41c10038604a0150251078100b42140f038550781c0203408200c1c1401001c030000220340317002512400134035000c2c0c29543d10b5070201d000c5c0301c504099500e50b02a1201120ba102d40c0c420701d00e0342d583e528000140c00608000035100d03058801d018a034600018005101e009460400302c92580c999110300c00c118161003001c551950051100004c90655503e4615131520804018185c41035810801110f000703d8015400e074030700059160560301c0501845110f0b0201a00f41070340558079180c01d680225094017207126440f21250303540c05820040c5071091101d100c0840320b0000f01c04005a41e424020b000018201050b02e006164264440081c40e03590103c80890791503402410f10035103542c88410307121a1150040da40c1680707400e90b610f1405500d4124902c81c107628084040c18505088200d8116041604030505141c03074201c0c030380303125400d080408500e420081c0003d44d8642154410554104162200075090321451031003140d064071710740042c2c41850300081194a0f140c40ea1440a51b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168221717 1250 168220467 168220469
    0x30b1e090111091908030a05090405010f0305060606070c120b010611010e062a0301060507031101090b0402040b03011d1f1e11190201060f06020109020a09050709031a041407 76
    0xd040b180800841c3d405003803070350240b4049202c244d6155549540d80742c820f411030307020510040001c0c0d800201c0002c10705c0d09110b0310f409006280740092125003540e8540f03a44c0d42003c1d190911a0700081101001c019215a01c3c4d00500200d219141c2e030400a8601100d0071a000c3c0241d00108000382403400c61041c0500c52455215082c3c8000d000c0d5448000007940084550700c0106031204481c4034001e4400b20f000c008500a20703603a40d0302596240242401032680600803501502e0f44d040c40c8003031001c81d1440007032703a40080d011180000c0f1030800350b000070700601c201c41100060621441150590030004a00080aa1152801000c44019203041d80c01200d41d000545c58079800710030901c0440c0e00040d84008016410518150701e0030300314041132100076022142903c0181e454040c288107440c00402d40e0001045280000d104954840e40011840f4095004003a04155180d000038070aa100d40780e840b00554010103000c80c0102c000c000c00910440c1210240c5080810201d0502006000a44c1e68 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168222967 1250 168221717 168221741
    0x201080a2d0b19050a060c05070603050c0c0a0f0b0a0204030305041406120103050708011a030606040e011107030e0a05100206071d12030c010f0b010e011206030b1e0901 74
    0x800900700d2450744410909000c8007211045a5a490706141601c90f6420442c01407000e40281d00d069103008100907080040d90081e170b00308041e50241c1c0d00020300001d40b800c1920524100841d240e944d1080512080c041d400d036200030381c401c01c120341c1c0c04e00c80c0c003040403018203000c0c0c40302c8101e0381e8071801078005903c903d00c4020700103101088108403450340d07844405d8807981c004141d245030013203040c1c034540c40312801e03001601d10380c0010a041010756003d200e0034407034080c260b43d200600c07238078040001d40368000102064041c80d15894001c0c214482980302a030b603e0401410180c846031a814001d2080440d41409805082441004100e0385001650f484100c2c0c9564010702d12940e44403011103200d104461002c505401c0c1e050700c0c04c01c3e84c0e104091720700501051802592034210049a60342590bc005184024203407030104082590390388047c0b001d40600c001c2c20940400303a03038008100020202d41d803025043d62039200c1404210944400d04003086201c034101030000751240b00b031007800c0341c075200b000c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168224217 1250 168222967 168223001
    0x20f0309060405010e0f0303030414060604090f021210060b0c163804031a0f04030503060d03090e04080a0f210b03010e010e0f0d0c050a0b190903020a0201080a 70
    0x403c1a07600ca040034050b030101c0a00748103259074001010926542050b241207402c943d5525a5060312401046a903900080489051001c8142c5032a48900c81d9040e69002e402412075414444204404200242c404494181e04200c0745946040b909d1180c2c000540300d000794004e0a20b150b5000601c40720303c2c019034004200c00e00500c0301c9405d129580d560038a0b80b1002c2400090100382c2030250350313806000218004c90404507170920180c9103040d21000107003091030f05590102404007103075010050b00d6105206450718140c140042c101999050050340c09030f08000001e2040008020300500a03001100154440c40c40e100d0282c2c10580e50400366050700040301d8980e907940e4a80004ea90003507000d0035000fa00004113401da4448980c00e5800c10340000c080340d404441d80342ca006104018044040038146001104484d8030f554a6443c5da1070068041c00911003076002c41d0302c4209860040481a2040c40c0c104135904551402032740710714206000b80d020443c5800040d0f880c64460280301961504a800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168225467 1250 168224217 168224219
    0xe06010507020d060903030209130c170601091a0a020105090328170a06050a1a030a02130e0108060a05010f030201020a1b0f03080306040e0a0209010909151b020f03090604 75
    0x111030310342288005030707030080c00c403550031000c507020340b107544043e80c040d5038056500c40140c005c0c070400c1140c411a0407525031030a544603407442d5000180420000d4082240d040d0b644034200100c6d05601030b03401c2010311220001304404415403150080000c2c0b49a50028409a034809450300d07168041e02ca000d03c02407410080c40c0c86d104036209113000ca808464105001001d01c01c03081c0b080e500600b100c0f54050300759202424130803403078513084400080a843c00500054080c54070585041d000251803015825004516650000504440d00002e08546010a5081d45e9900c0c1916a1000166214001503107044004a0300c000c0c034201d404c0c02d40790182c0061141c080c035961182120a080c01c0039a00317a0050010108100c5000301c5000d00441c080d5105640b242424030400040704c0100301480f02c15444405254010384070040032031704440c030701c1000003000d00030380c14294642c0620709040d14016117001d603115000703962282e890b40d6000c8a9401c684907100c03417180701030352841070018480d44170001b808 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168226717 1250 168225467 168225469
    0x2060619030f120c06020a020c121b0613030204090516050d0c0b130f141203030f04020d05070518150d0b18100e03040e13110906041b0e0a0b03010e06 66
    0x86286802e0f251900f002c0c2082c01c0d498040882c2c0204101e40c0c0140c1240b8640c100c03628003001c0c02022032170010080c1c2000800441020311172800c441e104d500454020500c90944123072044543e0007160081d0040c040b0340510f181407500c1c0c40241c00d00507040c1303030340c2030000c80c1a041c024440e1040503404a0028181c07801c00303c2c1c060f4180c1191607000c1c3c51450951000c10300d6003001400340000e11682c3d09107024044560100f1801e105256103070034455100348208100c1c5803c1d032861030b80190301560041c2e428005808d120341441801d0b0809500308914440101c2498030201d5442e100c0c1074035217040030803a4108002c100c10303128401c1001d004092207001003142c100010080910b020289000c0b80c4011008400d1039055821408441d00d039034201040c20020014500181c0c0d0340310403105401d1445031080c0d940e484007210035000b0300d8003512b9900b0000e2019151540000d58070740c607199164000480d02c0314007c240525500c0030341d02412000000003003000441d27096a050741c082c0c003402050b03955194 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168227967 1250 168226717 168226733
    0xe0c04060c0f020a0b190516110d08070f140105191d0f15090609030a030504030309080c06090d03090f0b15190602010606140901140409060602060619030f 68
    0x10205848a90b1a6194040160b441d110020020500f040d101c40d2610480d032148644400140980d90a01078100b00e0038840808441034007040d01c0e4041c40c0d00c92520b414001203195241460f400402c5440c2c00a200300031700c010034000c2d22100c0c1c4100c2c0c04150101180745024280d0310140c8803d20030040c6490b0442009450341c02000d5920300ac03c03041000912280009490194500c0004040c2e40081e0300e1003003102102d1441d5580100d00500818503400c024000c1c0765244a4040c21008165445012a003018441d070030034914a80c005280fa83c640c03ca00c030381592a5402034487d55200e206061000503858042c0c021009400d4108104219654617a104c01e000c010000f40240d010003094807200059944010352240c100400c1202d0200e40740c102100a401c503490b64101000344550240f8840d5103440d40d104440c10000c1c02e05c0c20300c420700030206943c82d0b68000c2d600b04541d0b40f03003400c801142c803c0e4000307131151081d00201ca02c41e42484038014100e20942d554040030308600d40d201810702c0490414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168229217 1250 168227967 168227987
    0x60703081902040306050613060503060403030c0203040b040605193906020a080708010f050a230a09020903070909020f0607050c0307260114060112020d06030b0708010e0c0406 77
    0xc55400071020066100c03080c101c0e0700a0b00111031040e641c6042c40780d9400c0000e00b44a00d0482481e0070401d2506081c00a66102030040c0000c08051f00d400300b48480520034810346005100d183d034280c6c1c446854070030240c080c2d003186e0501c0c8204064940440c51440c401c48160712001240074556604280300800030322901004060740725814032400c0c1e902d0004800744003c00e00011250f0703626025040c902d04c010903244040e44140407240070031406000030b40e5141e01d031101325200000413220007a1114400b842c13040c110208075521003020600020184501e40040c10520003c40c1610001d584445124084441d07114002c0e41016038101500041c5c207118004142c91070050003100c82c40d007002c20000e4600101500030b44c1d40202071001c0c061a20329604043c2030202c0810b0000e0002c525021b418910064004001904100c291501c01081c83c100764125a88154000c10900c441610380c2450540400305036a4100003e801800000e43c000a40381104d0040800c035060301d14040c41e00c0b0040751a6115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168230467 1250 168229217 168229231
    0x30f051005121f090c06020604020315070c0b04060518030418050601090911120601030509061512011415030a0c030b2e0501080a0b1503070201060b030f010503160506070308 76
    0x1e070541c2c40f201480704074001c18400c1c40c0c00ca404594048a403400d6100800746078031a8095620880274040140e81c0402e495180d084200a0510542e854880880310703003001c0d220161030a81d000e0b0601c020300803140c0009109548001c1c0d41c10002c4550b2000550300d2146102c0c40e0152440e0070741c01074140e6060b420207501b101d0145840b0383d45503220301a070001c507503409030505d21015000505210b460060f1040650200090a040015280100040d9122007000701484a0030701c004441d81090b41d201031031805801100b038000c000501c0340c0c0c462405001b40655040595145000d00d4514520300080c0d02c01401c3d6200c0c021480051841d6200b070545800a82a2150b28030200391115140030b248103126204030302140e100d000b2520b09000548902d00c084d10001d80f00d401c09007c007400c1e440d0300300c544010702c006442241c0d495a07080340490041010390040410a64000705200040c140e121040d81a1b420403800e50b04080c07038001d090b1000c0081442100d0300103c080c016407011a0058074801d902c400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168231717 1250 168230467 168230473
    0x280c120f170c0c06090c01080c0406050319061518050306090307330c0905011409010503040807080c0a110414010e0a0b101d0d0309030b100509040c0501030f05100512 73
    0x190203c1d542d0910004a6a518083d8072901c102c4483d0343c0c0c8151210381000c0004075151070507050010061540c40000c1c469607000c0c0e1035405001c0081a1584158001c0003480800c1d4001e1210741002800b4070403500e041350301c2110030a004146460003062460040c002c4000852800c40142d4465403019071482000380d801c02800b590408070400420342181c580000c0e0300000300d5040200c40580750035040d0700107030304015850f01c1c064000c0301300c18111280c81c4801d08000e5240c0c0e859240c401c0540c41015130040c180280840c1c0010344090004000e81e540d8031642d05042407081c0351f0705000c2142c00307140c80031020764502801003000b001c10549150b00503a103194085440b0810714003094450b41c040c2e06000c006040061303070100768040502d41c1301c0d0f6002d049030442550501e81d14000c5c41c00348103002c09460340078a2000700b800016000c01c441f000301005400c0c0b00307071450581040180144140b03d0381703003c04e040c04a00c1503003000e54482e00d445041300440000e20350341400706000001e000752440c40c100344 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168232967 1250 168231717 168231727
    0x801051e0403230f0406080a0507020304050d0f0c08160b070309150e090108060603011a060405011b35032a0409050901090c06090806010902280c120f170c 68
    0x188000080a8018051304038a555910702940100001c4005140d1100e5034584028806103d80c08400c4504980341100c04c90108103d40c1021000c501a68500400c0d4144200300000c131400045029444014a00080d5210030365400308449544602d40c00100002c0a81405000902000507400c104030414540030200820078400f00d0351100017a0010b20207036014004200c058582401401a6801030214103034900d0445000b103049030003107010309814080200c060b0500c1007a440524945184c00c4145c2002212151198100850b500d40070f014400800c912001c00443c4900300303c80c00350802c0c803200c1250a030305c003a0f003901224a4940154180000b0000083c0e1036403540585802024914000920000c1071300d050187e8100f194000c41c01d2003483c000802c801348010864604441030341901590304d0300600344215800780c05c01d01c04400000c000d0300d40c0560590002d64030704081d05c0b50580ea01811540c0034141c071410007074820307c0001800403968402c41840742401a410214042070103086c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168234217 1250 168232967 168233027
    0x1b020d080c0303150a14060d0b220608010606090e041203020d02041403061003150507021c020303100e01121e0b010e07020d05040e0a020c070515040801051e0403 71
    0x1980f00362250400928031a040140501c2d0039010040142602c0758941240202c10300840c010f4000d07012080810703661165400f985440304160b162802514500b28a07850000b058150001c003800d01030840e0725803800602090b40c0e4042e601000680389070a11140403030781c2c0c40d45c415151940701d11080040680910004203840f00c0c0e4009000a44214031081d400029044281803a080303000b0501c00c03c011541c403042002c500c41400842000c00c07010400702d03555a9030b6070140d1915501c3c2c40c00a15940c4401040541c1543c007002450240c9200c29400038007a0391000898070018080c000c401a014900c1e0a1000140d12000300c10140c1200340320030380c00100c00d41c50f801030700d160076031104010628210400c14034a0f410f00214118440e01d0034a20f003010309004d0046040200145104085680003600710b0b06040204a000d008140003000302c0e5401b030003011480c2e201d4101e88101c102960038480400c0401511586264042c0d000c01400881a80d072501d04848101c000c03c0d04030380308101400100c0070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168235467 1250 168234217 168234223
    0x30e03090f0904030c0b0115030b091e0c0f0f04050909010b09062e1e020105090d110a0b0703020c070506030103150506120109030c030f020d0906121410030309061b020d080c 76
    0x3048c1c600016500310804400240903500c000042c1c0d8842c2160904110340340a091009450880764095050007a40d200102e40046103c0c03c00e404e441108046658019000b801c80184203507a42512962416102c04c50741c82c1c26a4888940e032540f00081000043d450f0901250ba1a40c403026407000440c0e24852801e41a510a507542889000503042400c0c0100030341c0c404107901f46058540300070441c515140070355589654400304214100b0880301c8000070703c02c00c20040c0613a0303290400e41c002054200a01c0150003980a1a80604c040c007410708001001d00d803480075281203071b8005040c2800c0c903100c001d041008090003004640d00030140507a01107a00720034850020401d10030384802186103c141800788c00c07000d992003d4000c5511120382005150361241c030010803940c039410180c0058950b200a0b2028010030320900d0080003441e020003004c207204900940440f802612010303e21502e59404880030307041541900c020741950040c010040c1803c002c0e40c2c1d40c040c040c001080c20018140c4299003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168236717 1250 168235467 168235469
    0x1a06090c090a0f0803040302100c0825051b01090801230a0e0706030510050f0f0f0f03010e06010509070203160f050a06020d0f0b0303092b08040f06030e03090f0904030c0b01 76
    0x220744c000706d000e108500707040261281c1c000d07123410546400400c2c4d0b035641d03403a40300d950fa4280f808100300c002c0d442c00c2505081c010340c4407035108040e6601e013500c0c0e40110200c141000007013130004201084c00200c440c0c040c4a00c4d5210200a803016428540382c01c1354254101c00a0500c22160380d948810161404040c03141c00083d01143c2e4001c40e080c204840b81c00c20540c2242c1046206100402e010613166480c40110001c8090580301c880f50503d25000080301d004810003d1601542003c41c8005601004581136059503811200160543c41d2028120303628000c240c6a12102c03400d40620202007007504100903880c6110b0400c039401c030b032105d913901d40c2030b80c11562518030002e807600c045c8007201c0103034010f540301c00405030001c1d8240741c01040018005c0302d400f41210103100511802e4171758002c039002003100c00c0703402c00060396030340707a0310034111501d01054891040005d207046030380c4c80c00d080d0100840b10310041c01003ca1015680c03400410940390fa02510403014044d80305249800903080b506658 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168237967 1250 168236717 168236729
    0x303110a1b0e0a11040537030212031303020d06020c0304090e0f0f0718020f03010b091e0619200c0406120807110102030c191a06090c090a0f 62
    0x80d01c00d0300c0c00042080c400300161401c40044d0901e1208611000d8071026034084810803549016003100da40390054002c1c030205d02d5554100070851940e607062151080303810072079209413004017002045440c515180d000f40125002150440c000802c094036007480b0354001f4a0003040c0c01807070102c110030120720350340c0b180d4006071000e902d9014400107001b040c80070100c148256400342002c402182c00864a510990040401020600e0000a40c450f81d07941604c04e07000c00ea4248543d2541c64195030364007604480364483c4140c1000f828040c0812003400286840f180c05072a0900300f10780382030b030402c0061004d400c40d0301304000003c0010f040d64108a45180409101000c3c2580c40c0103031003400165a03903a004404058500e2004d1400201a0000c071540700d900310b8403418091040301c0040b82184114843d1040c14800e2014030640c4843d59003800400d14469140c196004461071000009600202d4449601601c1040050440c812480c0104804100100214005619000c0b4200e080c0c06d260010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168239217 1250 168237967 168238013
    0x80705011704030206070809011d0304030b01051005180d020301090c0f0f05060f09030f0706030f1b02100f0b1210050705040305070312030605090a0b01020d0f02070303110a 76
    0x20446540c10081189050700803104031205490b154801035070343d82c07020700b5002c204512103000403000e01d029800141d408004040c0748140f1000340c00d4250341c0760032030300041e14440d81007800002c0c00d03d0180344c020701040c40c6440d05401c1c103c60642c094084d01d0001c01840d044500e140241c030040c2d90078491040054403400040c0300b03680c10154a015520381b03c2d081588081004101408a6910300c0203550300d5480f02400c43e80d9a13141d440100e4105886565641018032481c1d001142c6070790107800a03400300d048008100405074400b001c40d003142e482c0c80c1808001d030f0081020340300c401d00303d500301c14402a403154001c00e0b03225031000403980049911000d60040d400690f601c1f128ac1a030781c05800d40008052170707d18146070540c3c4840e0b44404091000900e5245800010180c1e01e0180c0c10403401044000c0100b8a64600404e52402505110b944280180144884001d41501034420121002d400c0e07402048941d040d60f0303003500c00300810f003844075442c0f02d03e0001c1400582905000140d0341442c0720b10f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168240467 1250 168239217 168239219
    0x10905010509030a021906150b03160e010e040209030a0510020a081f050915030304030c08010b04050408161a04230c030d2a0506090c09040b01050405041a010807 71
    0x290031201c001d04825070a40040045241c00360340046c130341e6070326502c0301041204070406180a600500303400c8848103d03c5101e450014a0841c81c1002e1440344070500c6034009a0007a403c001c0b150340010104581c0810342210a00701141825805408109400b80031140600019141c6918005c10300703448103e043c1c0c000918404140d40301d00441e410035812045140030a10880191844c0126402050b000d2414200003845004101421410700c29018068076510b58407402d0080540c00300b030144008a43c02c01401117142c2c2894420144610b8014040701e080980c0d010b2142038801d428003007034440d820b2901014142d810300c0c00101c0d0144d40305129140b150300010508480c1c411181c10101d4407500000c0e603041241d180804c00c07100c020000d00c0c040221109040224501c9041c06c443c05039001d0080e8081000c0010014115001e007442c003040f903846101356810016040c1003100c000708040000d000402103420690040c980061040000c0c1486460481240c241c090099000903566413046034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168241717 1250 168240467 168240473
    0xd151a040f0905091c020d080708060a140307050414010819080a05030402012d1d0f120c09090106050406121a1801060602031e0a0909020702010905120109 68
    0x9042898895404080d080c54079101d07041081c00180d200342041e164071240024140d01c014090070391a560003000309240040300050082d0383d440818400700c0231031a04800b0030499030140c1c84c0e0500c00c013401410041c1044c20550440007840c130a00d1015010300c03401c0000304a1347d80f2401440d041d1074001c24084425898990520300c0d1001d054103002031055070181e01404910b88038111140b01c0391a04029690f9269440101c454002c104d011001c0d000080f00381880016505100701c1034518255110740354290a000b02c1007041001c1121a60f001c00d001000d071820b03041c11110b40003501040000d45025240b04c4020035200102240c0561030703a50341d45403d000b6490070b40b1401000c3c1820b40c2c20358582c0000b65480040d1005541507084110a01c08001a8206424120058010b142c00020f05c94030399940d4020b540c3c2d07080840e10900c0e840c800c501c208103038400b00c0191814401556a429411407805004c44000e500c640c0007070781004420a40480d05480d0103c0c2440861540400010f01c20702c0380c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168242967 1250 168241717 168241739
    0x4060b0a02011e2007080702040207060504050d0305062116080706080705040302060702040506370803071214070501060b031618090c0c0f030c020102070b071e080d15 73
    0x40f0100d68414500580300c3c032010f081081c00360b0110006134050740d5810305410184403500500c0f1009500a00002c0c0b041c0400c540b980240b80658450f500f10ba804c100c8140c016002e41d18100c0f03102c0d41041541c019160403060341d0404030701940060f000c0c0c8804110648004000840c1c0342c004907240d9100800c10000c00b03600c0f22006910940c82d10f0302d181800e00395800900309210790000a0b104540b900080340955880c0340310a00c1d06003086007003448140700324046582106151100030b100300201903000840d00c1001c401c444140d80c3c85075580d803500c4c0500b40c050703503103001c09000340e500c40d00184405400950b003486400e0203010400c1c0001d0b243d180522286001000d10b1426500b044008680b405400002c18280c0060b1601c0d52000300d1241c104100848204100e48c501500c000f088c0c51081081c540c10a000110440c000c2e4245c0e03c2203070b00d80031500c0d01c0384100c81c1d00411200001e44c0e96840c810500e800100c10703600c560402d500d130010324088582a244000000c00701c0400c240410410f07801300c0f07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168244217 1250 168242967 168243011
    0x1e270804091a0109090c0e010c02420915070f0f050a11040b0307030b07030f110a0e030d090e0c0903030c070906051203031501030b060a02060108010c09050d0f0204060b0a0201 77
    0xc0c0301071001b000700084c020413128240300d04506200c0c201728510215078071650014015801110005030a28454030f240040808032017001000401201c0d030340e01e400882004a61001102501d4200c6010610241d00e42d15480304c103040e521102110032000c00242070030b03424000c8074060b20003003811f40d0180c1800f6100c11441b050081c4128940108038006440204003d0116078020680704065074407010103a01a0042580080c403017441c03e039001ea0310840d918090b20103103800d0369074614851002418581e032414442540404210014420040307000701a444a601c803079007001c1541483c0c100320109181d50040032400310700e07400520007408511801e1240c0340007003400300d0b030100302231890341407241d02c0f48400340c91134a05035000019000305901a030020210b9220207000c1d96078070540001c0c02900c845080c01640900d500b443c204c2081c1902c100c4102d810350b00020054410b400d6950703207202c81484076050480c0c2068403031000140c80d107078940251503022081e400200d01d0140308505075a0600324 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168245467 1250 168244217 168244229
    0xd05031909090b0f010c03141b07150504030b090c10020c0102010e0313060509040e070f06030b01080411061b030c0a03260c0313080403061e270804091a0109 69
    0x3a0609003c995070380c0722101560001c00b800e00c00680c080e02c0c2003c4404106541c3c0005002a0004200b0407401c141030031900d10024100a440c4996168110100b1f85c2407214046000100280000c0c40802c83c0f44900d40e82103012041181c02c5054240040340c69502c4201c0004056045403e41d00c84558080c01061a00a030100c00b85141030040c1044000f08030082c040c200400034041422042c80c1c03140c0d4004d11080300c0042c1165802d995072a0600300c41c04090082400003420030450700425401940e03054095944054001c1141e0050700522001e03800c404030a0990001303409a5450659041c002001d00000503c090b0000409c50f00300070f07000482901c904588079500030515029440608145500904d0a602180d5651203c840b0090662281d2401030168080060300200b0001580c0c0444d01c0c0c0038005255078140c0d00c0c01c2e1103880c21076034419141c00700b08505c81c509071115460300401070004c1d072140845600707090310b0f140c0141c1200c0b5624041040c03580313546110411581c01110807001001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168246717 1250 168245467 168245471
    0x90403120f0c20070506161b031106031e010807081516030507110114010f05010e090609060406080102190e0a080a020609011710061e0c020f0d0503190909 68
    0x103080d020082025540c102c0b2103d0040c1d0720407250718035000501ca44c5008140061219446059540d41104a0f07240722800722001081c003009042003240030804042226000200008205c2c1e4013001d000039a4002045c0b000d22842820b020005155504841ea01a100c2c107002040c1c0ca506201c1c00a285c01d41281c00c1030f411004030020040160009144518001800d14000c962525800411f65040f41e064408000c43d500b019190710001079910300180c12a003540c40c034144e0960340d5500565446100703031700076508480590f00164140c18901940c640003003000d807001840507a6881c10b1422178001c00070300484a1900011039400c5988240010420700040b15201d40039498100d205030780b10180d240083c02043c001c0b4200c07085a0140501c200a201c501c25554a145448059080301c1e105a0180c900407400e54990b40000d24020400d040b0014600d803901014203a0540030481c2c0b10a13010100c903031011071980c0100024105002510000e8000c6160302c0080f4600b00025100480b25080031614038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168247967 1250 168246717 168246731
    0x3080108070b090f0d1e0c050909030316121a04050f0903040306050a090c090504050d090f0b0903010207080a080411041e020705010603020a0b0c0106290f040302090403120f 76
    0x6054841195040e080803100c4d00815003400c800305104103043d51005d0001581c0f401c0c5000640210031807803100780e1056004112060300ca50412180c54026207240ca0a64004c0c0300007800303207400707190000540d54142000c0031014541c0001e002034500b1071540741103d50048010607c0c40c1003601415401c1300c6140c240002038500301c480d0941d41e024a1101030a6141c90758085040c07410750f54041040380d508038041540d04e54407080900040d1205a40c22103081c0316010203450b038148504500070582d00c861411201c40e510b088050162500401c0006034155400c01c407c00000e64014002c000e20107443d11500c24610345414080c048100341c00c4114040d50800701d40c0c1692011103894004042422000141c8500e0142001c80c010001038000a400200c180004104110064040d00b2509106030080c080311341c44200e80501e0f00702051080c0c0c410b080e1214020b03210070305400070b03191203000c1ca08901d0500e9a03d4000401400e0103580c281e01050101c0010102141640940001850b241e60140040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168249217 1250 168247967 168247979
    0x9030215041a04030905041b1b11010c0804050406030303140717070c140a05011b0203090312160506150f0402070203121c0e0303060109120b01032009040c030308010807 74
    0x44070704030424141d030058006404c1500a445110103410050404c215104040400781d002e00340c1086400080350200902006000612030072030840b43e407000b0500145411080195944181344070200e980f00300501000c100d9031113500c509001180603640208031988201014101c4d604e002d480c2c9001c10580b05000144040350075070301c0750000d03442c1ca0514506030240c00c200ba80c1c3c00102000312964058006010280708054010f40e0801040403100310604600c1300c8144d0f501c1c8501c2d95030b503170560840c0001e0b007007aa1111024050b111200c20790014603080c3d40d0756803810254211110440d40d042c050b020240b80c200791800422000043d0340461504e03043da000a136551075104030714204003400080810100e50a10506a001114140700b03120000c2c000300c4403030301c940007252550f00080803a100000d244890f800580d105d01d8204400d10801d07400c64544200d084011802c01180c0700c130700d001d030340d8840c0c0340c8038011341c0b0843c040c2a5240c4403509625008215038010b0b4058101580400414010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168250467 1250 168249217 168249233
    0xc0f09010305070e13021008010f06111902011b050109030f030218040c030e010e07050411071203051e07080415020405060d021b011e0606031404020f03120d0903021504 74
    0x5039280e0b01003130f840540c0c0f655030b0368844056074013000b504811402c0e0b00d60350554005031154140e9500b100c801544a848600445084146443c1406c443d80002c0d05906069a06001c0a0f030365401031400c0f890f50495a0f502d40d8801d90901c10444aaa55503880502855404002c0707039982e1401d45820751030842c5440d00701e0000e50f40e04100c0303803090765982c50003011b10340039510580e1141c20100092081040d4000850380341c00e070a125041c0240d0500d802c01c40113000550480d009d95a02520140440011036012401850010403012448485850b2a80d921181d003034540d104602c5907544040a1520303140008030001520101809140144020300040d998401034412400d14043e0058540d0318100e90f140c20403041c02c03425200e0b9480c2040348000000224601081910110414070450351f9400d411000c82d90500b05440d00d002c1108007040061800f4841501c10180c0141261140380910042c5007081d4040300503120003070b41c1c61500404258040c005482d0307004012968021038a001d40fa0804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168251717 1250 168250467 168250469
    0x601080103060507021f06140a060507030503180a080705100621300f020703050307020103050406200901020c0d0b010302060a0908060406330b09030a080c0c0f0901030507 75
    0x410380f144005080c251081102c076448003440340700702d0202d00b0303911074120090825015940007a4030441c50036074241080381c0b07000f040700c46550f2903a2406260f030f10100c80e203800262620031070722407140700005140c8003000456806406454410f130b983c0c0d2031f880c1407031520202022440c415810720000708641c80210b1010b050303159484038105c050059500d014100c988002e0302a11a4558045003104017020710340200c00345a4841e11104c600780922442641d48000c0c0f0321000f8500c0d4002c11100d0f0055202e0382005030401d21445c00803d50b1114544d00306012604009400720130781000c50440101d6904000e0300c5061882034074035840381950b5407551a00d8900c14000030340100030000300c0c1c084581c400c40f203010081c09004280c6a207030030503141c104040c082c0d4001c00c02084094400c0d605045d1070340b84201c062000440c0c2c00d40041494520700003810f1300151505a0706024001c001c8c804076a20000401c5c0903000325004d04903030700c008010007001506070000603024886880060002420010b5020 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168252967 1250 168251717 168251723
    0x4230a060f0e03010203090f0d0507080a0c02150304030e0a0b0408060c0c2b0909060501120e2418030a0c0303180f030f080f16030b130e03070c06080601080103 70
    0x5040392550681c16108950348080d0950103604c00010000c401d0404904114000303406419203a42e422503800440f9640a0154083c1c083d0b20200003580c0814051000305e1300c0a071015011a0420500c0c41044925400459098004c20360320f072148681c3e480c2800301c25003d0188400080d041900b0002c509556490003000c46a43d0a000100c00660203c10452100c07014a400301c568840e0b42e440c403842403140b414050b1180810400f03100031822462500511007a074070180d40720000401140b00c080f0281009088014950044404228048082d06182e1100f102044002800da0500042c45400c107100125002900c0d002032000b0b81005034850081d020842d05894041000d003c036002c80070f503c0301441030060480b010000071408164210004d5010145a900d405105640d250108900c130f2204a0303a0050481c4031041d1100c4840c0a64030424003e17902800380a5400c0340321000380c044030020420400d0980c00459501e08010906070b0700300140c40185068041c0d0f06000740041c02030301c1d06002c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168254217 1250 168252967 168252977
    0x1020a0812090d021603030e240d0c050301060c120309060f020406090902040f0512070807120308070f020c04022209020c1006180f0219081008060402060a0e030a05011104230a06 78
    0xd19641d903a40c10071118800c49d407203054a10300b04020300e80010303584420700c0c038441d080c103068158007160b008409403412a10340d601c0341c0d10507426650701d00100b4629000070006269942442d040820f03603521406180c0b0030342d040d006a5a17400c012004d08411403690000b50b17800d004000511a010400c0a00c1b0b08881d0165038804031040042d00503810401260064141e502c906d1500003107200031110a0300d8924000c0d2144810341d298001c003111a925800910800f5074080c6031300d03040380d080590042c40c1c1d810382c0140ba6000c940031800925088002a072009031403d40215080742c0b02401440002c0d40844428410011685000842c0c0c0c034035800042d0786010180d0b5400987c410100c641c04480d03030005201b4008814462500015100c1034040c0d900044045512300d0110760304000043e010f01841c0c00400e00c90410782c2031001120f820a1940f205a054080c040c040000107409010f01c001040e01032690a885038141904038500f00541c02e00c505502036507904080b0640c0315020400c0c01c0d60064034003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168255467 1250 168254217 168254237
    0x9100504080f030403020102091809070302010f03090209010e090601150c03050901051c060905090703110907020703051005010e061017090304050d050a0203120a05120601020a0812090d02160303 85
    0x1040e80c0c09040c10034400408004101310070994103600825201d00d0807103c41030f951710700b07001042c15950120fa98804a500425040c80998000c040000800b0003619001c0344600440e80800c2150100381d100105000f0700c181030001c025800d100407400b52944807020022440b45904c000c083c9800c001c400b40c01c2c4038000a58032902d0344101d04640d004440700481c00800b4603540c00801c000c004030701c144000306142501040003401301107181ca0842e90081c01c10084081c900b010451403a502034024015480b50310000000200705200801280d4a944000a690741c54041049002c000c010280c5100f0341c03820350902d04540d084000705007802c2d400c007204041d603541c0744003162031071040d03800c03a03a07120310301c0c1e101541005800245028100e10a4003500c040c41f51184036100702d40100c18000d0003180741481130380c0d0041d8102c0400380e40000b0500c1100c10806903a11031029035405060f0a400e503129900403c0f51801c0100140030840d0424402043c012201c01c56000c0c050246000041c100300714411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168256717 1250 168255467 168255473
    0x117060a030605150a09181104020702150309070f030803190f180203010e01090f120e04050403030614010e03030418020708040f030339240501170609100504 69
    0x1206001075503104000b0005030800001010644821010a42c81000107020200e0b640317038107000d896000e014110b2a00c88800855079026200c06088150303d0700264207110304800b50341c07000344542d0425a0551440c7c0c0c0c9040c110501c030f08180050300f106440c11030050301040065103040c220783d84102d0014000f6803289441c4007040180072501d030969202400e018001103a482110b102c10041482207000300050040b0304001030a07141182c00141842c0748644c408408580300702c070342180d210014a0081c488220340000542220f4040e502540041d546d0881400f1a00000721031003440b8030709080400501c191040000e03540d204074010f00050880d189404018108135405540145900a00e02c03500d503900d415401090810030b20042c5c000810751390020160342c0e00034a81d407280c00d1100c0711440b0703421610b5408044150800c05e003240e020302c682001d0095505103403481c01c00840c05903c04a03440d4506a43c001240e07080710700411254020809000b40c401000441c0b0758100b1408001013241c2c2d0b2141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168257967 1250 168256717 168256729
    0x90b040b0f0903210405030706140a0e0105130308041508190213030203030d0e0d0c03021207030e1c0501050901140a0c14040803090301110703020619060909050303090c01020c011706 80
    0x4020313440215070a42054a034020402400503994203904842401c0d948100031500c40481003540c4102400412208404601c2503280398161003060400f14a844d0a2032002c1d00307496440e44c41901c081d00007103000c0c05822640400074019650900d415121801e045c4102c0511644441d09145a16400079021410400c0300d034095000750340007000e403601c07110a00403d42c01b80111580714861350140b107030381da03201c14081ca001c030401607015401800650604280c038101a40003140540c14400308040c6901c1e555100003180e00b022088812100b05d414040c5051425102c02a042d02c071540d0601c00d4103c40c00910b440c92640c002c0d1040e6002c55030028683d0159000340302d44400e4516254002400f26040a0010080c070040b10103070000c1046172003000d22422a0f0080e00f4008006030000c0c000310300d0114103408100d241c2200500d00103096030365021054100e44070204129540d0704080100050801d0610012007600800c0c00a050200b04220000b0b06601100105020a031000c2000c50300544031b603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168259217 1250 168257967 168257983
    0x607080402122409060108120319050106030b010908030313170f03040302030c15010f0e18011503051203010b03061002190c2c07031e0f050106090b040b0f0903 70
    0x2040c3d50322510401ca500c05082c600c80c000309814400300c40401c400c1003002803002d0407510b41c100078000f00d407419141518941c0c405490707a01c03084032680c04261124901d218090003012035071000116042004001340c2040c07242e500041c0190414010400040302c80f0100680090388241d100340050300822001c0c3c068080c0391400c40c002d000100402c02003640000c014013406000c0400c41d540c0c103014550480c806031090040307440c1070032501801c1156040740b040541c3c10040900b00249031107800348005003114100d44412038a46221401003060081c1032100c0849140c480d40d14500d10360401c02020351610001d8285070003007c1e81130348a44034030320074450210764400100c242964491a41055150581030b030003448180302404120344580000c090014072012404888250f80b030756001c6042c0d0040120f510038580648201481100c1140d4510414598030b47c04080000c245d414114000c09540c001c0d049080d000380100010b0054081000941c1c1c0e81c1d03d0008981680c803150440800c0c1010b4003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168260467 1250 168259217 168259249
    0x3060105060d0906090803190905030a03020318120a090f05060414062104030e060306030703030e0f03030712020105100b0d0902061b01060306050a060509010b0f0c070806060f01030506030607080402 87
    0x50141703c2000c111101000351b018917141d400300b46440c43e000c5140000c03034100b80001442d6074402c100342c0d03a200d8041c0d00551340c00b0040c49100f8036101d03c5c2000c52800c180c1d064860400419001540c01c560070342000515014001070854404414101004500c05205e5400384403980b0082411010a5a1b5410211603980c92080402c2e81080030816510182c01026107084010500703030300d14040c003401c1200c00c1c0c0348200030040c0184115403079520140c4040c0e1840040036003000700c10402c0001034070108024510188502c045503201001e413400213003140d0000e0300880c10b026520104014000440c81500c0002c1c2c650b14000400c40143c0c070001d0f0b258443c1c01c00c01104003401c00c00d1401480019401042200e0040300284802da0310103d5003411180070380581c550000c1410014858500706401801b16035400d940018601000400c01d00e140c480c49500200c05903002a0400000c0c4c1480406100814003e003800d0210b400c1c507200290701c4c0c400050801c01080202c200083c15540c800d0b00c6460798680c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168261717 1250 168260467 168260471
    0x3100f030c050406060516140712111c0b0c0306010507020d0b1906050a030f05030d050412020f070b030601050c0111030903210603030f033106150503060105060d0906 73
    0x40d49280c542240301051181903c01c0d0701d070040009207640504215041480e1071800b004e4180c5481c1da40d01542043e805240f400361040d031002250182e60605000c610500800500c0039603c5080c1c10410140741049001d41641d00340d1000c0800a0310304d4000c0c40d0890303036941d03225840790741701001241c060182e0b0700080e501c601d2000d050300900c07000100c0c59001e414000550607a0441a84c820004c0d90024424582c002e4407410040003c19486840311004070f204a003603034649a00003500805a6100740d81c2522160340440d51100406c0d010003100b007007450000060240302d8584081e010103408000c1c44541808000078040118440039840b241208038003083d543c0d164103101002030f0352038102d0784032355031004800300284e488842c81384031191080b400140154905108050851119080609142c5041c58507050307144101e40c20001c1039243c0441c0f00d00d0304030b413982c407401c1030816540c05998802e11145051001c1c800f94501182c0c0c00c3c1980c10a40e02c01e0782e6400c81d0001040140075880700548064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168262967 1250 168261717 168261719
    0x130803010e180d020d050a05040302090a0608060a091a06030c030d03050a0b060412020621041208060607020a05060a020a350a1215180b2103040b03100f 67
    0x600c1180c156026080048a4500021501d06100c3c0d43e002c50303180d07020240c3e00031800707910140d102e2002020600d60340d14005003415540d5011881072402174035048411a200e42062003a43d600b0448544d000c40c4071281440510b00a49920b8030400b803080c004505000c880b00041e240c4d40381005020700090740501100c051b0402c00000600a0500381d810780c501e00d0500e9032412852030045e082d82d0560b103d070000c06074081600e4bc200002c0360b100e200d944440384146403203041100c82c03104c6200d21850207000342c2c24003071826940051100c103008201e540309010178010346025844812420003941d0301600c900b035607404405002d914140d44000b0040942201d0b090000d1000d00c0140019088004508007404d111040b00360355459000d022175510000d403151058000400f9203030454030604200340506030085895008104481d40840c40c480e0302c4c2c0391200b81902c158101403034201d802c031300169000d02d0441410b075001078591103184151000e50f000400803d100541100d01d40000f0f09000540079041c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168264217 1250 168262967 168262979
    0x6031302120105091902060d0c0c050f030405010206010b031302010806120709060e060301020421080d06091d030901020a030c11100c030201050c131502011b0c050c040608031213080301 81
    0x1e00030484102a090150103403c3c007000f00f12171070240c08158020700d074504154100c5000802412202c1c000c000704401d942c00e14000c10018046164100548009542e5441c109000a031a000040e030090389007010400400c174044e8148114071802d29424603100c02940c139100f0000d0211100704403185000d0040c0b540c0003030802c40d00e5000a040312080009800e40d551030104050803401a0704c5901209075a04400c80070b4501c1d611100d4981ca84110b84003414421010380b01c40c00c8424a402a6a4455540211071505014101e003210300360706400086140840141c0002d403210040308000381403152031007580307041241c4000400f0101c0307005001580f1030b100000c2c0013007a2000386101a8051f501c2d00340411449a2080121102619070b2884181c006144c06140000300036102003404c00c5559030404c424200c04c01c20b817103031856407103a070310709420b120365040c0319040500701d04956101d84c0c94450200449000442074415414943d01400c0c0c0c10390b600c0d500d140300380b42074940007000494004000300c0c42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168265467 1250 168264217 168264221
    0x609030e120d080901051303080405030f0403030801170a0c06051b060a02070212010b030606010c031205070201020c070504090506060603060a0b0307080f01090e1203100803071214120105060313021201 88
    0x918280b9540d20401515040d48090807a4402d0345c1004d10b402602183c0000b22740940e07402504248260b045920b445440b40d50001607810640040f000148014010040349a504119101288640015000012544e03440b800b0b58000f07841604107114000c90245900040710400b0640e0018400c1580c14914022400f08000c2d4080d0104921503490701e65a0104981c05200320b40c5801c2002d0700801460311038800555030314031410011020414884140d06a00c451809158012203036500090380301d0111525550411040d074011900a500e811210008074100003003c42c0c10080945401d552610b602002c45c02504494004000c95580001407050241d031001c44503105c1c0c0c00e2400500440c0c2d88400c801c500740c0700f40f00006c0c02c2c07070b50103000761085114440000b942c2101d03070140e1700b4400690701d8030b0007419500218020380d032450042d9082446035401c200b280300d03425416030b2001e04d4a044003a41c0403080906010355406100088009943c041402080d81c100d990000d20352003040d0f03058512280 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168266717 1250 168265467 168265483
    0x403060207061d0a080d0b03030a0e030c10050d05100b030c0a03200724090f02030106171018060504060209031614090619030c030302010b15070609030e12 68
    0x1500c80c80d1820403088000c0c3c0c400c85490386003a4101401c02c1d5800d90f02c8441030340e00301100900303080303070755140482c1c0999040000307019040d920740320440d0360408802094100603021407068040e00030110f180d03101e144d00c041124096403448400044507120189400c10b050015000030f040700f1030000178401d030200c291000d0000d0311400c3d54144564414029032891114103280e14041d000410300410300020890600b055031f49490f119050740c82c901d21502c20050f41c11000050702c0c0d201ca05901001581420b020f0000038021405001e003209003041d950595a000000b024103a080d41c0354101004940344903039405083c4c0e00a14280420704003800c21074020350103014214403078851040802c00410400c00c0000c11039003003402c2140c824804406009001d00c0c014001540324054904250559100380044006580501c502e541c1d1141035280103400c56540300d103494411101c010b2003440b130b5031072070040341c1019a0120000c0346522461400340c070030020f90f004040c1d204004264004c406940042e140d6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168267967 1250 168266717 168266723
    0x40303081519030602030402181008120408060712111314040c0212070812010e0f071403010611010b09011e060e0603040b071e020705010e1c0b0a060b0403060207 71
    0x40704440303000e01088078a01c0403864070700c1448440312081010854aa026540c0300d40080c006044900c15201ca41000202c00c0311544034080c20b010003801465010005c014200b01c8051020f0718080c01c1003503460752000010003550800414420f078800b0148145c01503103a450060307041e2515444c101c048414040b0700d500403810302c05400042d02005160500945080c581903401401011103c0c001e21051984140020380c1c40280c104290030300d40c200040e00034020007646203040305c14100404400c04000028040c8010440c3c4800500b407004100d00844e8110b842d242048a812449900018007501d104000c076640003841900000e1030f0308040d1201c040740030100a0800700703036441d080165020802550502e42096080c4005800508403007000c540106040c1000c08102d2440058241e640e106440c8800040e0841c0c64108510358004020210000044544c0445007000801406c4c1541d05020050004808034020424001d500d500102c09004120340d665910b0307840381415400b0794040c0d9411 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168269217 1250 168267967 168267991
    0x4050f101803030309031101090309090b0f130b120304060e0423090c09180307062d02040302090a0c020312041113060f0f03020102120705100609050a06060513030308180304030308 79
    0x100901f41c0c4188101251664991103110f90380d802c0000440040910301846e680110903690303114040d590700441c0049481d048803000c07809400a109100c00a03503914042800340d4801e000502c86260400c184d841c074040291400200303001c012000c5441c00c01c1c50b2001c40c3d549d100e403c060001081c8085035000180c1002e503000203407519030703443c042001400c00fa80c408031074000340041c2d4002070081e040036040ca0044801c100102e0881001c0e05140790606210780c0003183d001130204114140b120003140c2c00812014200f203400d07040c804c0a500c030710401c514800d10070070440c001010031908810071102400c010f400300c0352106802e000303003000304118091200341d9400e00600086640ca00c0c2c8440c0280d80d4182d001c0d00f005050310880070820b4020b41411101405492018094014144140c2e801014640e00114490070702860000c00c40f0010b4000f441000020440345200d0001c2c00c4e00601201e03418507210b4102c0d80c90450101d2200030550b14020603020015002050640c4402c4047c0690303106001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168270467 1250 168269217 168269237
    0x9080c010f0b030c150c031b0d030b0901050105030705090301110a0c0507170a030c060e1912030b060414041808030702070f0303200102090d060608010f0204050f10180303030903 78
    0x10190b490081c4c4c000b15610200143c00603e91404a0340a4088254002c04480c180124002d12022a00844d20710b0301c0243e01084040c8040340c2c0c0750103045d81880d0250b8000c0c0c0075504050009201c4c3c0b00040150091107c0000c4025482c3c8003540b211180061003459240c5070000000010a020b4660409841b00c1c86100e0b00030903c1003081600c01400c81c0310800510300e0302c0c00c9503400d41d036030b1a00c14401e540c0541e442c1e0304040300f04411303c041240440f4003801d80744205582d00c2d1400740306403200c40020400d4031f0095882c03899111a01202e06a03600002c024185110200c0001e001e46074155460b144449040310f480b08008400c1c02660203407800b50250b400154403015030740018141440050009140050340410310001b060b58112034958100c005071400702c050022540c0c0d198a0101104c0e010307030f0741a0400403c82c085c0f2138010000344c1031009501c0c152414000500401108928a10455540c540340e60750b0341c000d400d060a1424049504c1c4c68542c0d0780d060182c01800c524030240c01140315080d07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168271717 1250 168270467 168270469
    0x40f080601050d021017130204110a090b180d06020c070b03090312040606080d08040b010918061a090103051c032c0c0a08030310060e01020307060f09080c010f0b 71
    0x58994140c800c054214840001a5005c201c41a40c095100405000300c002c0303c144002c1d8403e010030b100e400841c0096140550a01c180310480b00854240002030000b0b010310040c00d580034003400d04417180b4059254445201d44154203140c00030200e2258044100d00e2080f0400805030040c00d00e064600e410741740d0441d03030740704c0741903d92204441120f007540003000902d4107040000c00c001c7d003140c0551000541e980d140c518003441d12107182c040d10f0100e070b9110100400c04c6450300081d0f0241103c07281c140310a03205100c010000410101c00104095102c5401a02c2028201801490741070300914504040d40c1d86d0030010707100c4441d4402c4500581550000c00c1d5003030301a0140c4e009070170070300140100b0150003214401e0200c00e10001000280a01040740c2c5080e9594030500340a00000341c090340d5030f41000d80c980c0c2d048407440e600c6001840040d401380c3d1aa6a00401030f10251038201c00301240c1407250200d680010b1210311001400d6020102b503000e1b1414055210707440c0440d840c4070800541400d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168272967 1250 168271717 168271723
    0x602060108120304020a0902130b28031512080c070b0a031a090a020702181602070f0b031f09060605071a0f060d0302030f0703030905100203090705010c02031c020102040f08 76
    0x2c4c0d020b074114022140401100410754018004800200812001a03413501c0e5095620f51011140410b640e403020039011140110000340c5902e25640e0408014990400e04a00f48030000d034840d18106003401031001050000200403162103019210989507402d489482503161500010072100000e0301d440c0105010124013210781070720410047c850780c6150b80c0d0040c40c0020317500403030080340c1041c9101ca8600034800c04103005401004c11580303c3d1700e032454040c002481c1c100c2503400f404420403922310401260f0242030440750020400100d11103604039249800810070490f50016502034036042c4000b44040d4410b01038507801d4410408100507900d10180400c51140c2a9411440031485030085030442c80c140d105006482d1007401502d09024800c5001c1540da0840c1c54140c010030f0b11295644100b00c2c080c0034102c84282082001c40c210b0074020b0002c4e64944050103000d0611542c0140c903c1907640411002d0203603803069840640c00d44540f0402800703508188580310340c1101503032000c41d0581c408 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168274217 1250 168272967 168272971
    0x708030903030418090f03091a030c0d020304140303040503180118060e0102240103030306060512060d08070203100b030c010224070e09010e2205210c0706020601081203 74
    0x1070041d424603040c10040006400103490f070b800a00e668000040000e1641c00c4a0301c041400703921a4a001c610f40159200c034600304030483e0056403000c00800268040e19805c1d111050f0b0301d00320060b100c1e601c52030010012580303000e0041040c8808820042042000401061a001084014590041d103403006407805105e17507001002119072000b050203100e00c24113041017401e03014811103c102ca00c440941000b559104d481c1d24000740280010b2045c190540181c9004240d5460918900f9030a10784056101d0b8028000522035104075000708140442c190945400b660010140c0d840d218101d148032004204008100d8000c0c02a81200c0f8003943c00850283c040020a006000c0300020382d81d041d0503a8400200075400b07100b80c102c42180c060315407010060103030015441c0c001103420082080c15450f140400f00e004008004011b1400161000c0750700307044101b02c0008050b41119540400a00d40030303050801855103d500b034005000341d40020614101c0b50084140d07458a9805a10b241d080e2000f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168275467 1250 168274217 168274219
    0x150f0a0f0614010309030e060705010f050f100b0705070506210f01060c110604030c06091d011a0304150e0c0f03070305030a052b090b060909060c0901020307050f030c07080309 77
    0x44000c1c2c0074800c0d4000d030400c0c5001071007840d0003185082524001802d580212000343c65580d035842c040f109155880c4603d0350030410b0240d42010500e0302c00c20104106204e406101001c0700d000c03e80104000e0b0412400b40501001422240c031120300366031006035845052003040a20b4219000304105c1c1c551320681505991555661482c1482a5214084c008181c219803541104003044000b0103d03003a03a2810b03016200558840c1881443d100c501d90f00b4002031380c0460f44100790040104080c03088601c031203d52202002c2450303201e9444c0d0901d2815218006000b070030f02401c0c0001c05d2a696008100c120484c0002c54407901c112000c1824191f941e400c90000404583c01040039001c268080c02c00780c13145201c0040341c07103901c45005000c1c0300c12040c843d010034200ea403036030911010000080809588001c2c180c0300380d646464250100781d0b5840c4081c05070a104200014031480c0d9910074000c070b41c12117410904651114104852980d84c950001c0c0c03121105008005000c90200c0010084880c4008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168276717 1250 168275467 168275489
    0xf060d0308060f012601030b0a0506060702100513031203060b0c06070c150606020d03050702010c0f0e0f0909030406020c1903150e0613020102160323150f0a0f06 71
    0xa1142c00380910026003811460520003001c0f11a807074105c1d1400d054007020040d1440701560b503d18075241d000c8050140000340500c0c2440e01b080466150031041d9000142c0407503229154020592060b00e079841402000306206440100c048103100c991182144100d02980c0d04100c402d95501c1440301c1c0c1e0240440e4294690071020118405a204200600c0a68080d680080320b600c800f0211504803a030300e600460142e0840001301c40c0c16a010300c122036020581e400203000c1c0d80b60001000700801c03000510a000c3c84504404004981c0f1842c1c072030440050301400301c2c041e074107143c4159503aa8006100c0c0d01c2c011700c50035080034040d051110303840284110604402a200b030440da5040d8000051003240c04c500b59641c038110f000d08504100e07881c0100c1c1c056441d0303031141ca080d00009007060030000108541e40c0d4000401c1000500244400d2586810401d100c0d20b84150501c0c1030b401e09030b0350054603030f805100105020701d10f551009030070700460020104010900301c940381407090310024480c5e000001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168277967 1250 168276717 168276721
    0x150e0d0807060b03030d0c02070e0105090a050714120411121b03030f0403030f02070623090604030b0103120809210a1e0903051e070b0c0102091005030f060d0308 71
    0x258050024001c02441400302080300760701c0301c01203481c50f0024858405e4454990000a102c00e03014041100502821554405250b0416010070200d400c0900304610281da40c00c0003800417440f0306443c401484c22600f005036103540c10340781034520900944082d580d1503c1c0107075003400e520b0910b00814003c4100005420080d03200b18442c10005034010000e81c00d03000400c0044200004000200007451280d21911255500c484d0001d140c11041e80010060040c2644000c4206052900c45e4190782c4050340b045644940090100d030b454051540f0042c4400080b0740040700700070345a00c0c40001c0001d59030700d4540c26601c00d200c4564801d40c84001c0c2548001c42007041103600c4484004042c980c140e4100031188854104070041c44c840c9840c0f4500005803150340c24410010203000510400c900050016230030042c1002050302d0307510300d218280b04420300040040765103070290140d440d01000140206d004404035803014001e40c2c4200c501800300030324000055035034500851103000803501030740d40c62015 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168279217 1250 168277967 168277973
    0x2130819030c0c09020409020c0105070806031b0a12140f0109030f201020091509011202040f03210e040f110c03070c0518060103020310050402070c150e0d 68
    0x2030b5119080a440c4a12031840204510b0920700040005213090100180c1d1010700005e41402c54001921070410003880c00e050000700d83d0001070340e150111200402e00d0001c0e14443c0050400700140d40040032a4040751408400d00007515842c1170523000000c00e0342d000034486030684c2d08950040d0300c0240803c003140482140b45e489980307042d4003054049600030a4681e04100d451416100104603000341303495125401441c5070401e0046014000501c0140c20040c0e042c001403042c55481d903030a0040c070700118801045a00c1080c80d443c0340710504408642d1662030310070f2080300e02103500050f40d10022184029115105001190024448aa454101032a2307840c0c01c010140c0ae20510f0300c4407150319408142c4041c9011f10041004c60089001965942e126241201c00001150700c0b0071321031550f2405c0004952a000070480c4d0100c002d107001683c0c0c1c0d50f440c03d4041a107205400640c0c21a00c0070070504200400b020fa00f0b010b54002401c0b0105055086004541c20300b45103c03015000a4202951400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168280467 1250 168279217 168279227
    0x706140907060315081e0c010c1104090f0f200604062c040e031804060602030a05070c170307060f020307050406030b030307060513140703020114210108010213081903 73
    0x2000b0382c0c3c0540190856440d4101c1d0f181c0780700d0720031151194014110406400c001000594030480c828227010b2004001500c54905840c80000c40f140181c0c0c60f005030104104d01c51413424612a40400c5a20501e065410402c05c00c00c000307075107500c030350010207000344192608030140c0f03003112190b1f9a0000c1c001540003890080c1c0794081d0280b030b1140582500041d00703941e180a269800702030100219190f0300114208081c0300182d00d0017600507450104140300840d4003104444040c80c1500f0a10303692481c5d407410460790f4405603c00204090030282005410360007000910034140240000d22000c6e81c1c098200c012071105484950125070100010040580a501315850701d12000741940d0401d1a1529a101503400c103e4184520b1345104042d4800c00c0041c1e0348907022094000c005001190460b40042c04082800820f91a6460081005080441c030448031880440503041c100310307a565500e9041c0e010b50094000722000c0600c41801040c6074038005807541a071030840c01c0b00a1003000076141078503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 168281717 1250 168280467 168280481
    0x6060b030c0d0b130e03270303091c120306060f030614120a17040807060806060a050c0a0f0302010e0106080118031821020103053405070b0c07061409070603 69
    0x60062859a881d007442c000c107104e1700c0280480c2601459990012840b206103101c0c0e043c0302040c00744003034401481942c0340042500c4200009a801100e40a103419004c9400400524001d01080900140e9a0080e0b8941c01c9603007118003584413520480c400d2a070075810340d0322600030500301030621011000c0342d05c0c0c900d030321148030350000b41521005c0030740e9200c40c1c03111101c1000820301c07030000060800c1241020004203000b090f0300d00c0d045203182040300c00500c040c0700750f5030b104080200c00705584c0c1989005001006100e5800400d24450b03141d103240180c06041c4407030f041c2c803055181c10800030f00d170f410600a070005110101c0401c3c0b00c0f0061541c09490411403110304030360f107400b0341c2c00c0460401d1080044454200f100e8014204007001440010241c030300040040700080002d81c044025000b21085652072003c0380000b4214910000c0302c00c035101d00a1013009012034410000303002c07070b8003540700044c001e0728001d4405001c3c031070410300240c406100c00d503151280c0b03a0004404100b200e03c2540404 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 168282967 1250 168281717 168281719
    0x32a1c0b04023a0507060807020d0804020105120915010f06020c0405090f0a0317070f0f270603022104050303040b040204090804030303020a0e0f0a0b0d0b04090b0406060b030c0d0b 79
    0xa010ba003c241c0e802d41902400e0070700442240628401001805400c01c2844028045854038600624010b10000d480303242490312002401550f2002c07400716805030040c0d0360000e401000d450164a40700003004d5445842d5000c4200750110740f000461b85010200842e8240ca03000d40051402003a0403060000501d40140340301c0c00c0c1c0c00f445803480e00140061100ca500c0714001e40d02c610044402140240e01080f000d00440c00340f11038800f00c0c4602c1500308100403280c40050400039100e041031202c9408a000010300341c2d011a0450307038049201e42c0c0550260050451421000b648454200c0c0d00c00c0603004151400f510b02c0d0700500004001641d20021640e04c9440a040420100310319518080b00d6000754000701c005c80d070040b6004a81c158080414280c1203003c6035854030418071480031956414060060350004480010000e020034415001b50081080240081155019174100001411401e8404444c1c8504003c1d000800390040c2041d24026011150810318203181900703680020410b101c011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 168284217 1250 168282967 168283009
    0xe04060f0e04030f090311130608011b090f05090105060304110303032d0103020604060c081b0304180504080405060a0c14010c030b03030c030a030b032a1c0b0402 71
    0x41818841026410300412580c0c010201074242454050301c04c41c00042c01804001d007070b0600f040445c400355202c0c038260600390346d80740c6030b0b1113200c40c01000303802140c00180c029030911000c02080e507a0441070f4484540656120340c4000d403248040700c04074205100e072644c0204408018030203807030301200944d0003a00c82e0100c4000e00038081d01203403c40d001191001c40100b0012079003440c16290300c100303400070b0701100c041c80d17115070640c1d001401c02d002da40034907010080007482410070000200b0403100721041034909286511107900d86035642c0d84c02402264203525151201d04480409800381d140100da200030b42c02d05141c180014003040b600440c809008009100c0414800305e03003100400071092100074004103202066100107000e8850304040e090090380100610441408040103a403500c21003403030089014802c07040081c0c64100d41c1c01c00406860401c0d0210f0b080c44480e402240920b0350300359101e204034101052880c4c42d803440c1c80030180c400002c420000700189040c04000303c1d070a050b5840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 168285467 1250 168284217 168284219
    0x50a061815051b060a0e190b130501050c13060206090307030e0f04020d090b090d120903170703021201050105070f0f0c0f090207140105060109090b0109030b090c04110c030a0e0406 79
    0xc00302c9001c000c1d05004000d42000c4c007030042041c801d0045c0c0400039203030b0000f001c0045040d000704980c8032120034050501651b81010032045d25101c1e100c2208950440000d2003142803034181d1891a90140b0407003003024240c0c0000103909030000c180c5a104180c1d550195003000010346041e0b8031085441480d95000d0101040801295254809040c00c4015054002042002e83c1b41200100d072001c1c18945656200100c0642c41c00e9000d1070348540402c8103030340810046c0c40c80c03500b600c1d400c400901c42d0003c0c0c400700e000c015143c0d40c503501900b21101c040b400c40d11580d903120700641d05403042c081d020300704400c4004403d0104201e0b40d0540700040c8207401c4c140c011a6520300a0100c0080c64000b8070720280c001803020b09101401e01e00303034440d0465400801c010b081000010385400399504c90300d60901d40300e81803100d0507801280f03114000c540241c84008039141c5601501d4440003005030080c425071400d4a03a9541c0301088040c0c4000c2c02c2140300451a0104401090341c600f0041c100f4a5482512440c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 168286717 1250 168285467 168285487
    0x9060d020a030e0c030c0618040204030c06020f060604091106030403090e1f0b03010f031211011109042004060528050c0d050f03010b0708070b070207050a06181505 72
    0x20007020815140c2c1c1c1c000030342e034404600141c10a9580520701d842544000009400340c0c1d1003400f12505c0c21080000c021114805101003000383c0256800540312010440c0c002982540105150915020b94815144189d0390881000b0440340480e0b0085c1610040030b258451505200c001150003a0090074555a074580d54500511344440c00c407519003141000c40c400c2c1171218240742040014101070b00381c480c02e640c18882c3c1c0d103400c20700301d03c0301520740c080408203039071480e00039442043e09106070402405011040309007031209501003190f95000d103140210b60840681d03007596086000da0507189032441c4c0b620340401101c00b500800047c907400c2c00c00e9542d80540d040c0c5a0025143c9510b151290354654030301d03070407550400050085003018080308104000302201c4140c02c90b13054400b02107046444da2860300b04030b012805201001052040d0807000d11884980010304d00045503c00c441000c003054840100719656181f803101000c0311106c0c03a0080c403a500e0b0030b4445058882e01d42c41d0917400c26046603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 168287967 1250 168286717 168286721
    0x6140304030c20010906050f0717040e04061506050304020d020f01030b0d0506100806040c05010c06090f06140c090a050f0f100e04051003030e010827011a030703120509060d 76
    0x20041410203c904458101c9942c01c50002c04c010001810118140b414800042000c1c0c412528010100c3c0c0c03021021007988a48001680c026200520342040a80790900c0c1c0500181164281514180894080051258810130460744907950280980d88203140c1c03036007032101e4107107511021418991580702c280400c0d00d44000d201c034840c6c0600000e1156003006605001600880d41180c4400d400030400c001c0403030b0513880440e04480007881c1002107800c02d403e01100401c040c00b001000b81035450003a009009064200300b80b0340d03040702000459510b0325081034085d4804c01030400e80110071644200442c0c076011042c91110301c1c2c06008400850250720024280b6203031080c0560201d46042840c41c2d031420184030365a80f18180120029681d400c6403005000b42c9040c0c018141005103d20000360300089181d8071a2903884800120480070000703044c020b0107032a00c0074807900c580f4005090316495203800240c0c04110f0f500031300c03c50090890508201ca07903034403440140b030b0804d404000c0184990703014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 168289217 1250 168287967 168287993
    0xc0409020d260a0302090f0102060106090b03190207030c0506010b0307201207050d0305090d09030602180a0b1c060302060a0f050c061302010f03060b0306010e12010e0309150406140304030c 83
    0x11303540107030303100304000030803141200c000315150440d4016070042c8032040c0c00480c2d00040c1c0b0810007200b5141d03920002c00300e24015003605c03d100751a002040038070805070440018400c140c0302c0d03416540180e881c0e01803000f460108642c003400061003880440440e0801e00e03100000b412000d0203480d41c182c10246008a5540701d075208540315806956241c1420380c0c144191508458008050500d2203c11100101454083e00000e049140e000440103007800c81a22034100204001c1e04121103c0c0d40e9400010064011801c080d42c4203001d402e0b0404880c030a81300e80d05c00c0d2a0b00808041c1003c5040b072088451151016400c0d05001007044002020982000900d12580849032014454031061000402040244335440189801c0100500c00441103070296030341b004081ca0442e46110398040010385000e0100381107940340d460004848441a4088001c041294040c0c83d001d030206404000d00542d8452441550001207160b180410303000350140c0155003182c042e10300703001046c400740c42d00030444000d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 168290467 1250 168289217 168289237
    0x801202b090c030203060f070e12011812031107020303040306110d02030a0b1e130e0c0607260403030903080304060221091006050109181119020c0409020d26 69
    0x42c003404004602d41000040c0e0301c2549525400040c0c10984801740480c49504820b0303104409240c181d4101c60003d6010709510030240b09021507004c680c5c107000d0850a09400711500080c1003514088000841d002102e4581d54060020b614051460322900000c244e0801c2d6403000040c104651480b40c0d040340003550160b1324003c0002100e00203203080001c00c180d031281e080109140c9030b4680459035281e0a2004400040e032501040910000755103900f01842c8280703032580003d0103c0c45800b0300c41c41050020204001101c8520380281c05082010b441c0102e2000030001841c404080c0700246400014542262040d0700141c140940189241d00203001040c84001c017802580070407110200800840c80010039804041102d1070500000030445011400b4100c1c0c1c051400741400481482580441d81e0a602540d0464403440c2d000000381c10356000c41404c000510840007821584e00e000d1044500d07003a030003442642600899580e03e0510361441014152410b90340801d2421403007040b0060034843c0c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 168291717 1250 168290467 168290483
    0x50a0e06120312100f062d02011806150b0306030d1103190302030709230f150a02062508060d020d12030f050109090b0402150c07060503010801202b09 66
    0xc00c02c680a9070740045a0301c1b020800c1000000b541c032003600070003401e2121141b03514440307800c04001403c1c2c1c050964070302185031020034031045106024850744240000c0401c403204819040d03480c4043c440310300040c0d9129a150b04034070590380c10b043c010803540541e05003150660341071450070764a0080c1c02d0221584d0901081e0004200300940343c0c0200d081028014800341d180070022000c0640f04650f002003100b5003d02d6807408007007010354480184040d480c5d01004146e6581c25a10402902d5000565050a1803141110744404110032402c86800c50035041c0c0d0340c11503d64401041101001032114103076003140300c1e4000c5201249030390480d581c0014041d240803420700005900b680803075005134040d0440c03034a0080110300103260131030903641003038045589000d11460900c2c400698468041e0403141c0d8811614001442c2d40c010001d903040f600a8002007083d4480148803000c84000302c40742c48485070082100740c0c038100300c0141c0c0d105403180c003010084070b0503003810307004c0110782c81c628042d0f810300c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 168292967 1250 168291717 168291719
    0x50c09010603051e01030507050f010e0a0305011b020606130515090108070618120f03050f2106040b0108010611030c2b14070201030f0207020405040605040c050a0e0612031210 77
    0x1004a84c240e2002c2d0b00400b0411503940c07541e20350f283c075013800b80181441503900001450f0305a11500c0c1c0c50194281c0109100f010980d01c2c50080d008001490740880904010618560b0f210b0020076920312801000e032014002050040b804001000f006014220440e19501c4030355040d1244091680a031084100038024681010000ba1010000120301d40300301c07012650a210540e0b00d0012804e056901c113031410400d202720b203800c0d84c4600130b40b6003500d64118003040401da41c00c00c80d080240712440038845d01c01551138140520083e1030703904044034041040c190040005500c1226028a0f102401042d40d062150340503510303052041c1110455003444201c01d44040a101109511070380b401c082c10801c1d144403c00d1460002d038041c0030300c040c0c10305a0300c07081504000c41640403102c10f40c1d8014030411151500e03145c50002084151000c0c0c80201201c0004511404e0000741c0c0002d0b1226110340031996a10b14007000700c001c40c0d1604541c03407400248140010412101212402044003150a00e181 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 168294217 1250 168292967 168292981
    0x6020d0e070803130312050c10050a38030c1008011503020403120522060f0801050a0807050d0609060905030309011401050f0402090102120d0e070b07050d0804050c0901060305 77
    0x201805410500d800d40007041401d4030505203000e0401206c5c0d01002c6400b20300b900907020755a034000e4000700c100c9409502044103621885501c018030811044004100e0140818030700304915880c3c3c09400034203004c0500201c1d5a2456100e41624400000e0031614180741c0380b400b18242840111041c40403415490062000e8844d070083d00500c08102d20301141082e2031900c0d01039101441c1c1e00a80300307004001480300d103901c10200b58040c2044c0c24100e84090300395100d600400cc1015442801c0003c0da85400100b0189000000c3c10b0440700d02c17500512915007045c080005503014810119030481d50b5080100010b01d490094202d254020030146440c0d20703041c101d1a083d0b44203011007030404401035005021300d0384c03502c002140400d03080d90b0040c0c8402c0c5180c0140d2420448068072010301c01c0100325204032507100d0300080258040c150a54019680d42d8000c0101ea001c0c01c0002040c41e0041d40300c60f42d040e481103414543c0a802142241c111654220100d0700d1a0403c1e00b108002075114410000d41d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 168295467 1250 168294217 168294223
    0x50d0515060c0a030306080a08070201110703050a140f0c130b0612090703150504030f0503040303024305250b0403030314090c010e040507270617040803010e04030c06020d0e 76
    0x1821244050120280030703580b0302c2c9440c410103800074140719102e3760190204404010792400f5503072100440310707102d505003404059000180c200c0d28242c8540c2500301441c0d01c011500c0034911002908a030ba0b0003501f05107103001751a042c01090b0304180280106043c0c40807151140303000d031817040f016005842c1141000d811240014601271105e81c203184c18000000c2e4003803001000c290403460300c2502d03511149003c0700680f061103050054a542100e8008a45407d0309101078901641203a421014418040c1c500303070612400360140c150740101d0107103140d8a211402003020242c02c5010030015079101c1d507919410342c12580060300020354072407507501d120340a20101508501d40c480103004ea046444d000803c90ba001c031100c54080c07078485010841c3c55001d0201624142500441460303902e011481c151112241d40c403c03100040c0700703542802d01d584070503a9500d0145400c04d003007501c1c41c1e01300f81c1c65032260840075004500b00022661004041201c80c800381022450800020070083e002c032680c030386 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 168296717 1250 168295467 168295469
    0x1c0b04060e0f060906152107030c09090906020903060406020d0b0a08100c0201020408070b0705102708070c27020a050703030e01090803010609030b0901020703050d0515060c0a030306 80
    0x200c000c0340c04140050b0440406482d41e01c0720049503a2106595103901003501c0b04142c8034502006800847d4030242503106d40c64450035407640f401c014140d5941d980c0c0850640f021240703000042004007000f44147c4080790809a003450141102510304030300310012038a080e0301241c040c0c0b01107601040000c2506028000c100349080200e480600307490030903411545030501421500100795403010440720704da000b03405845c0242114030544040698580c241609607010305403c940718064403c059000c0c400034030808040e4410f0300c204c00c42e8044540c0c0034a501030707075104041d62041c1d41400144001400650302101a00c10750444083c4c080403171514041d500350440d04110054018800f00c843c466101083d103002d1501443c005c10320340c1311452114010041100c02802d0540d0000001c00c1e01508644104120303842000b007000950783c1c40c0c032228201c0c0502074006000a0041201c10311690454024982002d4100321041d904050600000c425a1120204000b19041940244103240d01031003008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 168297967 1250 168296717 168296729
    0xa080328060b0901030506040603060c02010b010810141c061503050d090b0d150312030b01020601080706140c15180f241305060c09040b061603050903031c0b0406 71
    0x80501c500b04031410744140151000281015981c0c000100d01d42d0b034503049000110b401110800960b410b03810001c2c06007142c203051a010640090200c0c001d2681c181220080396809608101e035601b81c0c3c81000016035012424440441080900b003010a0345403103064004051602a51580e0b442d600d406403c10003068009414841ea520702001090700f000222154106d039100005090428045102d041a1690300b024105d040300c5504400d07680e8041e4060481c0d49426001c840031680c6c2c034410b0596401150268100185a540c07401d8007021042c40a403c10024440a41e40d40c021600060b4010703100c200c441c01c0220714000303e41e4103c18014007140003401070103000f400c0c01403000b00e1300384403212100403840e24240070a030000c0c2c5000b451460082c2520750140954580381004460310750241c00c9411000d101e07a00d441002c1e0050311301141111524001c020001c0c230725070b55503101038605400c090750442e003601040105c00c040114001907000c50119031035000841c5000e02050004a61071381d0005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 168299217 1250 168297967 168297971
    0x61b2a09090b01050111011103090a0b06090c45090912030c0f07020a0e010302181302041508030a0804050f030306010203180105091807021b010912050a080328 70
    0x500c000c00c01c195102d506589081c2450190002442115401001159802e07c00c81d90040305005160300701217020a50103000c0d18a48180c2d0719410f080060800d000e50302044103880410003d59600312418048030b0100620b1103c0b0901168089400d041c2c00c0c500c0d4110020b03100260042e1000c2c5443d85505030484010001040b413003141000200e6148009401000c01c1c200c08035842032807101401c12a21030507070190100c07108540e103a1070b09654600030b000c1288605043c40d11507050140301010701d8070404070982601641c8216800788401490250f14003200ca40130b144c404140309404000910141d461541d8544203441d150501c54200740f11b480440700584c004000703101080c3e0f400000d0303a50540001c08a0f00c00d8189503801030718180304400c40c182d00301056880d54101c0701251000e880c031aa041c0c1d000e581869001d20000200d054000c5842c038042041d0200511806410003180f01c4024804c4048810710328103500c941c90142c0003225048240090107074207038043e20819000e20301b007007540601 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 168300467 1250 168299217 168299231
    0x105011b0b070c0b01181527021308061812030c2a030c16050a0b0f0405030a0303061502070515130801090f0c0806190c0201090c03060507031a0307061b2a09 69
    0x2142c045c4104240340100e60400070350f001c230301411541c101c0307801d034440320380c11400580d46217030040d280e075412204203441c5a901e0705041109240411007a031905a40d0070300914658424145500b1a040386101003211480440203c0680301c008142c51820356a03013004540700d11440c1c0304240f40241c082e0035901d0705100c0540811941d181d540910050360541c698aa40716020140000340d03900450340040d40c54070a004001d03040c10707007590080d02502d2460060441c408035000090740c0c0c40016214282e0008a2080180c409521160140c80c2207052002c901c200e982e964a030403425999480c200780e60303084040c1103040030800055512001000c410024094074507000005003400b07840d0110350011107480d5008140c1c054803c1d40101044c40c0c0c004000700c1c01540364280300f402410300310b60f0350b40480c1c035048446070a000d500400d00031742c14005005001c8141807171011030b60f00b10300d600d64250007881c2507038110004c1d031000c081c40d21800040d0001d4010000c5074040c0d6540310780560008800c80e14010b1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 168301717 1250 168300467 168300479
    0x9060b0c070b03060d05070f0501080a0b130c09080102120a14010806040b0709080a1203051308040b07170705010e0c0402070b07140d020417060105011b0b070c0b011815 74
    0x90041c08440e445089252030b55103e030041044000840030040c0640248800820840700c480407031016607500781d0320500f440d07494040000880340b4404810364000026070805003802059003150707010070914a80070011550341e84d0381d80d007a0b801600007082c104040c0400c100c980c8010703209413034900c007015034030300025450072200ca5100c030000703400504100f0000001910440c0100301c0c510091100c081240d0481c00701c1d08001703035a840b0a015250002c1e00301000301310340c03051082c5440c288503002681203151500c1c058040c002e41c0d01211084444007540030000803051030460142c210b4a0140d400881c000c007882c00d6890070584581b00743c1d0b02c80c500c10300c85c080c042400c07002c5595010901c0d00707250f49240c03402c1c1d005079030501459000403d45400000c002c10400c0ca6901004440c1c0d0700041142d200d039803144019a61002491b02490705030100c00c0080c00403c100084554110145050541220040341c032500f1031000240c004a0b0f004a084141d4215030406102d03075001012041111441541001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 168302967 1250 168301717 168301723
    0x40803040906090b0121090203150f090114010602071707080618160b0403080d060b1308010e060601020d0f0e0307030606080c0111030a0c1103070f030c09060b09120c04050406050109060b0c 83
    0x1061482c20342da00e07d0340000f1074a0422060f102100c070b02c503010f412403625456540e8050800c860050a40d4200140f090700c1c3c178500c1d2407203070680707607182c01919240b410b00b510070000d1001c81200602601c1114000110ba000500a10b4064907008400c848516442c0002d14585a012903400150450b041400c00c5103019880954050320380c03040050f9920203000361002c0281206030000111000700061070813a000d0040c0c450001c032001a0000d12115000c080800e03103c2c0821101613016030810180c40809500ca03091083e141c4a035814100c4a003c01d2801103458030301c0030f420448240e41c1d1000103000b813003410412000300f0321092038030908002c0e1456480b1785074040c1c410b890044c000400882020407040b01e082c042101c00140440c1c48803540c4a0f0100040000d40c882590000c13640100031410310014006c41d0155100d0034240b610b0000d20001303204204450144116141c055658119180d60b900c1c02030900643c0203440205040d4144003a0700300b00d0b0b2259200400300007081003e280109404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 168304217 1250 168302967 168303017
    0x21b0313060f0e0f0f100e0301060918030c02010908030d06060801080f07031b09050a0902040b06130e0c0c060907060f05071106070c0305030309030309010c030b090402100302040803040906090b01 86
    0xd651000c00080c8000109412458101400b0b500c031300c11010b003102c002e0f40642c180007078490231070007486226940c148103402c07070b0f0704007a0303800d00303c4003451401c0c011a00402910f09268410700d0650041136a90800608542014900c1d49106071103800401000da84913142501400300c134406029050034000c21590345000c03600c030013400e080840900c007039420300314881c820081076444803c0c0030a1415407007100041c02030f804100e11442c41c000d200d8000d810698251600780b07030b4240400c1030380782c1808001030081c080242000160581040041c074140410702c00c250284200c40c005248060810708040d006801e00c81a40c4104802400030302c0c0450104011180e100c1016204e80f40d90703a4007410700100030309090300040e125100001c1403111f6450b001006511900015000700008120700904400355401c40d02055880b003012404107015240200c205400e21545003001031900341d43d0602581507070004c0e403000800399900c80782048a42d2840c00344204154003480c040d44d140801c00080c900d41e00e90 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 168305467 1250 168304217 168304219
    0xa090501090620010f0c03020d060605130b07050a02060d0b010206091c0e03031608070302070e0408071101021e0f0c032811090a060923010612021b0313060f0e 70
    0x1501d030f001ca5002940110b0340281c5402007070122280c40c0344080c000c0d41c400405410803d140c02800030b203040c400c00a0394040304c0c151a200d000b0a1401e88005850303040f401054480f1b000d0205443c0040c0c0e1510010300b080e160406011a25410520000e800d00c94010b120765800d400a0060059507015051103680b0181c042c24400d0707080d6000f40109103580111001604a04068081e000078007606501601080f44203a0890320007d0701d585601540f01d109032002080d15100b0b000140020703d84801044102006104503104001c1040040000700220100480f260b006401c868140190610181c03160b800c05900401500881d5101d440d81d00c1c0148881c4070300c0440313804c0c1c1d1104000949500700702d0b0b040020700b80c1c00a4104140440000d040701c2c460250a00e1602c07002e003650030501c015800a03500c03041c43c0750f4411380c6080700c19201090f61141c0f61500c0e6600304550212494503007a2018082e26681c0256203e100520b4403220139800da0304054248202c0581b20400694444025204c00c90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 168306717 1250 168305467 168305507
    0xa06050f0d0605090c0318010b01050405040b03011e1d0102190807090801051608091501030204050a06120f03020d17070e0a210309050d1a060d12050a0905010906 71
    0x9062070407000140b03030b65041103a005a110043c0455804001e0145001c2c8020030040319512507000c604500700c0d1050011180490010f100410a030718250380308101c0a84050000301d5444006540c5a955a80c040910035616980740d540300035a0103000c6101d0b1a9003000002180703008804e529510b600085940c4040400800400203081a8441e502010090039000f000748560704051600d040c5000e04528458002264000003480203c03001a85c074044d400d508442681a034296020710002c1c003c024080090661522800220703503503180030950b0796a00499090056031811301c2e0080c02c103003407031924608001c6001102892075003011324050300526541841c100b040c1011000c0f803800c19803507000d10a18000f45035410004034490560200c42c2c0d209603142a045034660007044080e01e00c071480a0042d40c8541d5074810000d45101800e904087d000b40740340b941e01603e03501c5030102c1d8800461800082c20200300b20a403503400c00c0504000d05400d00f8a00c078110704202c001030505c0c090180b5002502 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 168307967 1250 168306717 168306727
    0x302090604031104060b0c070e070f0f03150506070c030210030e0303070c02030a0c0321030c0219050a0525120f11011107060203040611150601051809100806060a06050f 74
    0x55500d5000000806c8003000c0d207600d03843c810741c41c41e84641482c0b042020030740348540051031705480b41c0500c0405103e2030300c40a882d18031150089006010050552035188242d4402042d25511031001e81221403141c01040d5070380d820740c0706104409000c1c150000605061095008481c1000300c10789502c00c1e014a44001c0321241030002a00d0302d1200c4402400c203402019000c018050840d4802e201d805010f4169000d01c084044221700b11200303110f901c0010381003101d80d01880a008040308054500690480e1801340564588a04102000701941c42c40e1b011142810f40007102e1005c0c46004001c0f0403d080d0000301a40c4403034041a98510009088041407050031300240e0180c03818a00010204e0111640c40d6160031000e5600c2d80716024140114560480d8502034442c00207441d1341c1c02d00300600c040d1072130319240015209070700075880c103280795410200911101d445484500348510401c480a91030f00c0c0c038203c082c0d4140840901503500034007240200380700c140e8000f421188400d50443d4031603554 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 168309217 1250 168307967 168307969
    0x715021c020d1b0606030605010503010e060408160c0503010c0905091e04020f0111010e0102040501030b040b0d0803060d05030a050403060c03090f1407090e060609070f020730050a1203020906040311 87
    0x10f0001020014203031880d011003c402d0140690003607040e54000d40080010115142c03a4030780c0c5420032500106140030411028009000d0000449425841098168a801d4035800001d0035645202c641c0c4001400c110400c10040c600103084d10341105460b50703e2100303014489040b0414150040000c2c4c06141e2107582811240d00c100343d01c0f14014401002042001e4040740b00034040d40c81841844e00103820f01085503401d01e068440d40701d144100071701d060b044031000d5444405030b400040805510010b2140a030001c128280b004025003c003d44d90203940764210b1601108440b080350a082c1014a00201c2c80f00103490b00c511440982d400038804d10822791090001c5192040d15088002c815040058040c40080f001501e24058541120074100130303643d40c4000c030b0302d2846900312180160b1041c28108000446020300d241a40600490b1844040b8a00b2811105000f00706003280c85a01082d0b0000a001144039141d1985a40d8030341545040c41480000e0010700541c080036140d00c0312890b11042e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 168310467 1250 168309217 168309257
    0x3030210020a1215060f1b060c02030918100e0f06040e030405040c03060f150903030804030c0b16020114060d0314040f03030512010b0a05190e030715021c020d 70
    0x700b101480c40c2031015441680c03041304034640911034040030403c1103c002104900451040300d1080e5003c1e1500b980800070385800c000340c503016031500150b02080080412030313110303841d18100d080e03c100740303900d11f50500c408980140320301c2e640580325003c030307180c20f208500300301d46a910740110040b02d020424082d03800195095120769885698000d2400d030320380c0083c6401d500300c1c00485507002c0c0300c011050f9030b030a200d01c01120010401c0700054124182400080d0003100380c01c1d0400c0c02441c01103104c1d600c0755101c01c0c0c124020359551700c482c04000160f1035196424058020210480c2030f1564035810258046003d0001a88009042c0003908100303e107940c0c440000d5500802c8518081c09105542e03080190480d401900040e188940040012511000303400c104c807401070b0303550344141c605200c18041240480c0c072500caa00410040e0340c90000c495904016070350260626401c485100c00d42c2c5100130380740144041030b90030300701d82040c415105035801054558424225051400c3d648411030f0791401c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 168311717 1250 168310467 168310487
    0x170309060d3305010e0a0302010804120309080301090911100e0d03020f1b03070f050d060902041b021609050103080f0309070906030f0c0b070b04080a0c05010f0509150103030210020a 80
    0x144020320041d514124800b00440041142c0081c0c03035400c190741140f000e2040795441e60201038081045d000100b40001d030401811846e01c0c14601e000503400c03240d0b03034030b040c0164401e9200221081c1c07207020950a0103d044080c5002c0f50b0210759030300400c1e110410180042005c0070030b603446030780c6900e0100103240c002c0c4102450304070400c083e12428050b21200a41d11103500d0b940a000384a0110040340c0b102c5080340c0d460980b01d0003405005c80c2a80c0340c2d102c43c0a081c2000040380c2150711003090b2911103050703600460138034086030040c018118101408020064480e402030f04044c9c01c01d00104041a498412076185142c0141042c2eaa81d983e000824a003a202e42d0154002c4c41c503008000092102286040b090180b207409404005036a030444c00b142c0303024021024100c08190342c0403a001030a2030000b0070851883d0309111a941c440c2c0e8a540b801c440c81a0020710301141c4903000c10227844814002140300d00c0a401441e001c65043d134400075910440c40c0b681c0341c1e4096000075066a814007030b1040320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 168312967 1250 168311717 168311771
    0xb0a0203070804030605040b090a1502091c060f05090d050702091005090106081015121a030106120203010e01200711150d0605060a0f030b190807170309060d 69
    0x90f60f81c0303950341380c95001440b007200c082e9020070488010682039900443d104664940200050214108a108440080d03100402d0b01368080203070702070303070058540e00e022401c0310600036240018650006800c01041c1c0704002c052040701d400402a1459698101c1d054400180d0181c1c0c0c00d4640f0382d504d4807500c00001c03d44e0001c0b540038030035500008060350311424661042e9401d014541200d50380711004200241e802c03003620f0108100016030130002010743d212681c40304440c1115040103d815001c217003110404e804c00829039100781401000c0d400c0900502d424410800001c0013003c031180302c5c4044c80005ea00c00004904c10001e04101405101c20000070b01030700090410000400ca103282d081d941d030002002e012454100080020039140c050141d4a07550b410761100803c080702d0b648214004c000e81d80c0d4807544032a900c21404403080e03014040d50041c0c41c2c40d07001002118100040c00400601c01080c55299510800104c40603072142c00c290f4105100c05900454014a04c1550710540c1c14058004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 168314217 1250 168312967 168312983
    0x10b0406081203060a1226030609010608040510060803090f120d05180310050402010305060f0102060c130b04080a05160f18090f03080610050702090c09010c0501180c0e100b0a020307 80
    0x14109011540c01d505204222810603425004007c138007040d001e000c2140e016611280003030042250501030389807554400e00c25810b603540c00140007400e20481d440c07178000e480c05502c04a85040c0c503040030703541044020340c1250002c2164014519599a89072900164410400089102c0f29101d11102018844000050641b180c0300d211204407030050400321001e03800039043c8000b154103030404000c00750351160181d018000035902c440c42d801d0b5540c410b0414680c54032484100141035060300c0040d10181c266980070780840c0308107082003454480b80544000c243c2d03c02c908104880080f00c070034041100e0482e65884940c0c824991910000d1211740e50141411008505401c10158406500781c4150700441348084001d900d100708455074060101c000b900030f00c44c074010a075007022100c00340241c05014905518031038025502c9509444040c40400b03c0310322030140c040100303e0641c5008000d03029044c00c98105182c08030345c24200f64054440c02d40c03001d8002518140d06403007030080f28081c45c0c01c8021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 168315467 1250 168314217 168314249
    0x3010603090320100f150519050a080f1608030405011b0503030a0e06090118020616120305011a030c070f03030f020c0618010209060a1d13050702010b0406081203060a 73
    0x70441e11403030541030000e061440e0400c500303c540030031b110310481204002c5551807070900340000d01c0300035207070f090304030500e0307100d404c00040c0c26a1000501030141c41d800025241d4590800c500303620700380f00141c410100f4407048105015001000040c0d03400ca82007480c040c9101800800c9c0d098140311044d0011b48680000000c100048401e0340011481222001c1100c9590f507407040030074202d418040d4820311301c0308892081d202610303003100584001c01c815540821418800d035a01086c40360f51041440102c0e440384010011500b502101110340400f40464502d145096400084c2c10710070220300601c03681d0700300c1c02881450b100c1e40c045807030083c40302c500310354030902c0045056446004a410300a15000c10300c124071621418026110309003070107040f81c1d041c0080d44105883e418110f400c1034800b4a00615403d819950302c41080041011140c5d0004e00c9040c4404000d081d1540100890300030303402e08204128200c000901054100902c0c0ca100d900c03901c50800091084070190b005580000c100c180c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 168316717 1250 168315467 168315527
    0x3906030b0f190b090a08030c060a0f0902010807050d060b0d091104060303090510020c030a120f0f20010f020a0906080f0613180c030c050a0b040b030106030903 70
    0x320000c490401150385841ca0050340d81001110b442d500c10107500070590710000c00c242c0340414090104014010030701c2c40240d4a50140310300d55001440c0c00e142e83d40c4206c0502c96038003854410b9001c4484540030a004502c81500083c110440281a6500304078000452420009981e8404001342140c070038002c3e9240c04005403503015060f80c400954254001078140e0301d03140b074644900e1046035459155001040d10f40b6040240d0210400c2c120303400e40c0500420000259001d000c0402c007680720b0243c4203250f4003482e0006168040882118081c0444101074801164020082240c1c914203483c0400c0b0b00d1075400315550241001c200d6000007180081201d0005541242c0c00c041980c03a00d50ba09600340e80d40151900c0b02c950b041d5500382d00041c440c049c03820282c28681250801181030900c58110407007565031906007c2050780281c0720081c010780148554548088044010b00c40300c03113810700b81400d041c0c7c03041d6248418400c0c07805240e0350b1515002090700036083e0b00004620102d295100e40c0040b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 168317967 1250 168316717 168316721
    0x9050109030e0a14032515050310050f01080a0c030905060108031b03041404050709050613060e011701090b0d0b01170c06040b0a0e0a1707030b060d390603 68
    0x840c859105021500c8007040300b09100da0840041c2d44024018000030310880400181a241c280b6901c0c0f60030304100d8046800c0d0180c18007d56040080d6032003541e40d2a111407155041c81d400c0d0411885041e0074100e0001d07984e441400d03690001c03a031090010700e001c01814140c0007042050b90041c07203802541c000150704a00480a030180c020310b0002880d24500c00c1072078a0f00c03032241d07000f0a5100d880c00d084201c810f04282e44141d81c0514241000440a0389520020710b2070303000b0350b0800c0d075030180110041c484264090060150808282044590701014002a00c4807850500481041c4c40d521804080c00b6660504649603540c2c100c0301800303080d612200d00305280344c00781a0001e40361003020015402030500350200d50807260003201302410310036410821903604019855882c2e11088100f4082882c040540003124120baa01c8018426140385140042c01c07a171000707100a01c0f483d40005a100030a54046054441c0101000d10760245451030150403410640306003400c000d044c0500010070019010703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 168319217 1250 168317967 168317987
    0xd020f0111160b03100806011a0307051e0c010e01200d020904051311030304060f08060103150b0403020a091112070309050a14060f070905060703050405030a03030203100f0503030a0809010905010903 87
    0x5d910b030070180507200d132501691a0800c1c810404007413440c01e41061414a4200a182c1040700c07450320a1a19410034034014a9107100ca09405202d030000131200d400c102c003485129240340c90000240b01702602c0c0d6115a10b140d140d110707007641c02c40e00058100c0010046904640d010300000700100058145a00e145101100034082114064007181215105141c000700303950880e000756031070041d008801076003100d80c0b000142285050640328600ea02c422441e828002015010400704152268550300400950418540c007500140e4034100d0031401405040c411100d100b0b07404051b440d0707145c9035084100c2c02441c185001034007078065102008208110303582e249086910081c1101d049407510b0700e00c00c0d41990250b5003400032a00383d4108101c641031990141061501a0505074106541c500c0400c1c00d080304100c00f20006170f4000208148410400a14806807080091200c00305040c0383c04039540c0e110704d01d03041d003d00181c140011003e80003500941041d03680807000740003217615031402a00c41625 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 168320467 1250 168319217 168319231
    0x3020c06100503120a0e1513050604261f05060405090105160311090303040b1306050c07030303020702040b21060603030702091602011407050307030b0d020f0111160b03 74
    0x2500301060320948030107180019a00000c0250007544000c00406055500a20454090190342c090350600303035842561006500d00840000303030780ca103c1d280140c0a005a2a0422403081e10f05000a00407125007860300318070090614420800740025a0a40740f030140c1c00c07502101401c0303e2824000d48090542c120900558090314103121316200c02c1c400500b80c1700121031b04007010310400342c440c418900c00c1d004105003080e00b0b01100e141500070743c082419035101c1d4000080714040044c030380e420541c4044501005042d00d04d8014204040316032042d8445083e071001408140e000b04a074015903589a00505d07500000410b6050040c0c0d07410b104040561690000ca8214001d0800207035240c1004021180e495500801500465480142c03050124040202020440d0b5030b403c100e131211980703580d08038060350380780e10f460fa00ca1a01c6203004080ea800021000e009604854194005841e09035810100b5602400e0031507040c4680e0609034074009008550b0890540c0c4450002141e014481c0118040d00c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 168321717 1250 168320467 168320473
    0x70509040f050103021e13020c060f060117040b0601030f020a030c09090e1e0309060301260d170417040909170901020307200a06200c0a09090303020d0c03020c 70
    0x1103181c0101c811500c09100103504941014548441003951426110b909003008254411040a9400c0704049820848401507c0c1d8014418060030114600311168062000d1802079142c0000b040070400550000c0c01c0208090080741c0400d043ea800703500b041036003c015100c11911241d081d00d004016250641e8030002041c03141c0310100c0c2c100060700400c44d5440c54040144518083c409503441400c00382040081c0740e010610581310242e480400641c0248032074800d6511420b06003407901d41007000c43c402c07030000d079120300c2c84044940d401900d05101c00f4202c011008481d039550420000042c00c100808460000000300410885865880b0301d51035801200340700d41c407030400c900041c81c504c14000024056072003030002d003000401c608800a029280e250086042142e40702c042202d940f25500f010700403400d1040440d1010000f001403003001c1740b0307034001040c0c4c14075041d020030101101401251032440e00c1e2241c41e020325000340c0480f41e00007040d003410400b4912900009000707401c202012500e41c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 168322967 1250 168321717 168321731
    0x350a0b13060b09040201143103030210051014010c060603051c05090d0204021c09030c1202011a010e01021204080714010206160513150c020301061703190306080607050904 75
    0x100740301081071310440d07041e1180c0000c4c019280d001d58842d04080c0d030a21141b607120343c100480d0700340d071742d2001280441c0c20394100301d103811071074040c0c00c09082c01002c03070b422440d000c10007000c003400300b0071039044403a0444802020390b40000100d90703202d2a2000504150705000c800010400000b40c0000064003601e07125100101d850380445e114821016055070194482c41c500015241607401007a200c03016603440d01c040d01420f000141520903001095000c2404600600144001101d40c0028044248001c015181488807aa40d0074202c500249040002c02180019240d000304466400081220340ca90344507a941c084143d52010070780140010000141c000d00040d50000944902410b81003609a1607101d42500c100c0781600040d01451070080040c80006e07842d019021130709e40002c25651242c00e40783d40d0b03005150a480482d481088160007603410f0242003032020098480c03000802000103651014104228054400c680205105001b20030501031103540290084c41040e44c182c4043c000c0d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 168324217 1250 168322967 168322969
    0x18010e010803090a0e060a150203090102011104030f110112061202100203041805040204060506042c0702070501030b030c100801090e121b0f060a0b030601350a0b13060b 74
    0x80c000c40c244150013103440f0100380b09040c019526107a00500181c14584095a604a010444112034950202681001501d80e109580c20302070700b007500180700059443c00e49581e6030391004010100f0064042e0300306409100d00c0360301c154840c01c0c0700b0300c21b910144025511018070045144e4069004c80c420414621040300660011082e10100e03520412244558440e0126134400b808000740100d0b0710681d02d8074080768650303800e005000900050600f2445101d1644008414204408000e010300c20300b4504104515a0026090051310b0080c030300881c40c141c1716070100c1d2400c01001c01246e170000700d2804890705640d12885181c120b5211620038441242d2100040e0f407984220707452061001c004011040741422004d11100403c2c2c18002100c3c00b1840703049400d42040d1050f0b48580c481c540301c000110251804119450240c1044440c40e000500b40d800740807018810002d90030765503101c90740720341d20500040c4114041641c219845040c50315040b50000545c5113900c1003207410a00d04121880d003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 168325467 1250 168324217 168324223
    0x30106091103270a080a02011503020a0605160b0a1e05070215040f05011a01090504060f0501031508030708091002060f0c0d0b0406030f2d08071118010e0108 69
    0x180c640d60141080c91925690140c0c40400c000a940d40110628040c2c2d035008203d00304100c1107a02e004e41086a114030902d80e000f0f0940d05098074140f01d2400500040c005603440c0720f26001122000d0505641d0b03515248103040c014042041f000c1c2041d1403034000c020504030541c11904010004046945400e8044404032040710420b507480304c0140d02040c0c040600030b1411291903000783c001c3e4070110240310030355511402d44001d5603000241c0b00c98158106480d51700084182c0283c24112010300032603040401d4003004e05c5441c07042504254803184901000244892070401900d06001500d613203404605051815500100c0141e014142e2902c100011503c00f0038217600a81030140a00c40a403110b0001340056000450b0084056503108140c105a035140d204c1c143c011442130b5100c3d082d811450525945410b010907aa50b58513040501404803a5000b100b000380c540d51003001ca41e200c010a06011101020314180280c100c51040e10407111415034244290482d9400b02403982e03d0b03a2243c03101a1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 168326717 1250 168325467 168325481
    0xe0601080f100e0612060403020115090c12050a02040807060206010e10080a1b09060f0306050702030405060f0d090c18110f2d12010305061005010f0c0204092003010609 74
    0x2c05400c0c501414452000b42c51983c1e81c00c200014407900120b950554a00e04003081924200d01603035407401d20043d14905103141000504048404010b016411000030300f131082084500301045988200180701c91045c0d50540c0c0240c038140084070595600c03608040c0d5106428040c03606060804d1000400109050031618169298a80600281082d640c1c544410b001200c1c444608034418180101c4c003070600e03110344002061060301c40d031543c030314605000d0102e80c40940030000b190130420050005444c1c920450346c0305460390718607590310800118140001c141001c0d00824411100c00006211a401d03290a00d00058100080280b0002d05004d02c5007445140c1c403042200c1c0b000d10110394003012151840a50091400c15000d26940000545c11541d00c4444020300085c110f400610502204201c00d95100851000009041e420b0200103403076490070340d030000f003000842da52072411034440f50003442c0440c1d4000f400002800394542c8420043c140000e130f040c0650700e4850300190102042c05020 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 168327967 1250 168326717 168326731
    0x12020607060c120507170a02030f04020d0f08030a0b0418021c0f05100c1107050303070f1b0303030b040b040504021f0c08030a0203060109080c0127050a0e0601080f 72
    0x1031518805a5881c0003030281400c0e0303401803066621100301038455a0280c2403041c045030f40c0740d01403402c01c1e224101c040c18025090041062051040007a40ea4002c4403103130300150100c0c0c42c103049080078648500e014410410041800380040300b40420201c594019294007001210140030044001900c4002c1a8000801960049138015060138a141c0544050441d81c06110313640f50823419522a0340c90b04c00d207031148015295a070400e07404142d034800e0208001c50603401c0600f41441c13802c3d000955034001c090003e0044a034410030902040512802c20021081c12982c4000c1d11360350f414007400404151034082c1c042e609100400d140c61402d807240f244074680c01801e448407020410181e15006000c1c0310544140242c0742c0080002c105004003562145040c42c1000d030f0349251006c00101490415440f002c1c50754840ca0710780b05180c1c1c010203040300c03402840c00c445407410715105a001640142d58801034000342130440111301d401303450300783d984201c0d42130321440d55540301c52016001c00e0a080b1011b03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 168329217 1250 168327967 168327979
    0x4031a0603060702100b01090f03080706051b0316050c0a0b01090f0e030f0703230c10020a0e040903140a11011d07060807030b0a0e060307090b031b03150f0703061202 73
    0x265607545c41d60301800b10150189814850317583c648100607105a0076030401e0704c50321404a8035008103c2c19008041d40b2000d1050954400c3d95003000300c2056000142542a00c049032410100d02c841c0300b038040c2d58800c4100d070b0445101c6489424008880c08003030044012041c10101c0306003440e42d6a0103507041004007040214039240c0740343e000a0980e040084c0441c1000154046424465038103c0003003201d119452810b0307581e10794183e92070310303040c003d00c1c9442da110b0050085402080d0060410654082c080d00c01044252140c0307001c5807400407114130002e4202c03001c81c0390b1030610340c4903101390102030080d0b0013084080400c600b8503080081746032560348030341d010b04410f0150328850b401583d0400344030b01340072035104100070026802400c076800c030b102c68440c2d24041198510b801c00c0110003e1000c46400c01007038415902080e156103086c0140801103294a81900140d1410005072143c030020740f4444629007002d19900381c5181049d5400e40000c1e04206c1c0120340400007110002c41184e0007040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 168330467 1250 168329217 168329233
    0x315150309070b090406150206180601060822050102040b070b060904230118142e0207020f1002010608120c0a0311031308060601120209030307080f070804031a0603060702 75
    0x840f00182c0c0000000c03604543c030742000040c0001e2110301d80784210b466801030010340c138041024122641c52500c001e40c041e444800100300494010810340c0d00000c8200312074400a01040c01400450a001d40081c02907100160004401e6031410180c51002e00c82d286012042d02c4190400180c0c078810380c1c001d0048040ca80d5034251604491140c1c030000c3c0c0c40c0c07000110781e00102c5064000040070032041038035a02100c04400b541a03806000d009601c00051150415070000600301040f20807040507a008110790001f060015982e0b0107040340d03038210008200005a152030840280a0052449810314a2050b00321000b000700f0030100740c900c10303001c1c00c00804800d200da40707044485d0440e019105049000402c241400b2000311120b040240c040c0348018903140c1861000144004030f0b058440c0182841407060490300c0e0b502108640300ec7e0b400040c5181c0386e80c401107110741588030344d980051040d42c00103400400c0014400701400b043c40400180c4272039130b680e00d090503107480040300c040700181c0202c44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 168331717 1250 168330467 168330479
    0x81801090f122606010c0c0314070603050a1506110c0423100303080a051806090a0506090703110405060a05061801020c12030a0f09180b03071d01031e020402031515030907 75
    0x90584146004140c005951548ca48500003480311030072088002d500642c1c002d00807203030103018864001c10700100c200000c10150a44049903507241c021202000304c0c10300b00305449507040000240c0360100800030089015084000c10101710210075400e401078a9100080c082240410000b003140d415882c0d400d480d5480203040d2004201c014580001203601e0010b00510044c20803032644200e00d07003001440094094100b0618145c0000d06407005580075020070310001c0e00b5514007014001e81030b00c02082584543d00042c0c6050400d401242c1c00c074902190108032403444c01144021040300f86c0a69501c46085414802c40d0941c1c0c00d060001503108106401c85940b16024080303101d802c61820009040d1038248840350f2041c280f0300b80e4082c1d03440f00d500c2151841e007031000c0e1008103142c044004142c0000703503c500344c0420500c8081d141e0002c8449800380c004007442c0c0050041c1d80204115940c2c90180b0034480c40202c04c82d01c140c060344203d0041201c031207020b01185d0142d81507500170041185845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 168332967 1250 168331717 168331727
    0x9060e010b0306040b090a0b04050a0318050a031506090509030d180b01050607030905030f030d1107231603060c0305061e040b01030209030a050606011e081801090f12260601 76
    0xa0f11000300c907c2540d044002081100c07108600462041c00608407060581c1070003814596020052a40c1c2c104078481017010f99079134035030344003225806221122000b642e10043c02c028070883d4008144c03a400d201c1000310442022008226081d0160320400c46000b181d6101c2045070f699445c001c1c280c161030310051181e0b00e4403001402030a480382c0b400101ca00c0c0c541c00404c2c1051154800d03044243c0c800320708002030003005d000700c8a03d50051034a4500301328041d2140c14a4040007100e00d42420488084084180400e0110000103408000c00d01407440d80e9143c00700050545c2160304000038985008183c0519004c0b0030324418a031078000d90210945a04100310003440e400c1b054a0500d80d0800c011440c1c0c9c1c400b882050f01d80e50081c1c001c0e0040b89815000034005441400d10781c265141c1c0340c20341c80880f61308410019000710515104065644252038900c0c010101d009018001c201e070000f0200400c440503803003240300c1226580b002d980030b600200d00e99480102084501c48803607580005501075200d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 168334217 1250 168332967 168332971
    0x30e0111030c0c1c0204111308030309030d200a090321020a0803070e04140403030b0d03050301030303051320010e0102150c07030e0a0308030114010f020c0d05030f0a0309060e010b0306040b 83
    0x20010202841c0c01340d600080c00c8403000810404810408240c600045620001c0ca40051846101440c514a03002591644a208079082c01030300540c6d07010811700e105a8144822980006a1245542d641c5006006010700c035003448202c4075130034040202d101d8550010880030f40c21381d558004118202d00d0b0340c0e80c0111600700404c00410030030b010354040762954542c0155540141060309500d4a0b05050500905a03200300b00e810740644041d24500002070f501c401140c0c110780d05440c0000c2c260300ca108600030a00e0607150081c00c8180600014a1044403080d00351540c040262103240d500940c2e17030016a10b58051000f6280003844d0b041c0043d0f0a280c100d0001c7c01460b00c03a00d000002d5204000c0007074041d20182e0010342d2950030100040c050080c1810030354060b81c0c0e090a0080320403003030401c000d5566a12000042c010002c58240c2c008002d004c0099030419003103654115255452804018000c000c005e4003031b5151410411000c461000612485600b01c0d0701402800441e6a03503103a0325120f500c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 168335467 1250 168334217 168334249
    0xc0411030601140c070b130602010209130c02190503030a06050109050307060311070c06050705010605090121020f10021609020304230307020402030c04031b0f090b010e0904030e0111030c0c 83
    0x104106003045520b041c0000c101511b18a4052900c030b91030340d908403111302c18540002082da881040000b0b410b94a8000682002501c2d030360100b0070350b1842104030309043c00c1286403058840c030244c11100b0031401001640c0304038001001000520794070401110f00504510030140c15070003070f29090055611070340101307805203280c0104034a0b1040c5561000b408801c1c550140e000210003083c0c2c2400c00c1002e005101c01130000300e542c2840c0b5410409004400f4884640070038445403414017000c11502e603241000102d24004001c0c4000c2080d201d00603445030703618006111b2042070f0f0000800c6401c228400e4900923a001102414074007a50200c041c00d07018030160b01c0005200501170500103039158002144a1040c0c007102c0380c0c580d85140380003080f200b10030852078040d003058413050201d100f050041c2001c0760740c59036003c100c04045000584001180c400c0458010150742d00700800d1580003009205034880a80e030f0340c441d071046070703000d181c982c0500c8140510b240c001c0082140e0b1441d00161403115800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 168336717 1250 168335467 168335507
    0x4030804020909010614010e0406050909030423010e01050d2301170105090a0f02060f0f0405092401051602030601031208100332010f0e07080304030b0408031b04170c0411030601 78
    0x12f100d600045c1e075494100c1e007801d415807000806008900380141d24440b5111400981c0024080303a80c0046c1118032001740d00c3c2d04115012485520381001030304101c007007190b9420405102045085009404602401599000f6107100d0030f000004030144507081c0320740c40342006094212041d9682c010400044041130382d0003c014407206012200c3d48006040c202c84040e5055640d6203084240302c8500801051207402c110040480c4130b03645d1424007180d044030000d2038803c6c0e6880c0010a0750800800c8020040e425202d10400842003040010118042e62050f03151800340da50b54008000504100f070000400220003542001005444142e2000366025625060170896441c5101e9508445411a036412419102c0c0701d2034021490900140c8054000d0b4409103141600b50303158550012030161005140e000c2c00000101c0c00c2c0500598a8506010a41c48e40d65030b0b95030300c441c018488031300341000c4018010707080709030000c2c54a8403415049043c0d0f0f004c442c2c116900c4400550b070300c01854402c03119a00e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 168337967 1250 168336717 168336719
    0xc031b1d01050c030a0201050403090b09010816230309100501081005060310180c05030f0c130b0402040e010e010509060d0206030402010e041b030615270e04030804020909010614010e0406 82
    0x40000c4c07000c0d00c20344002d03034000240380c0341604004140c12560307440901d0140f010401000d0710399014120b25406124004150880e1004c2501116244000001c5a1409002101c42410748030710754015809030748048125920181700d003528208035a400c2c4034103201680201710b06034040049404c02035100d88024181c800030b9030042c080d80d0a44406402c12808821b203c48540100800b0f010030402a2100b94020400c400c200a0810341d00c1c0711004079103218800144002d000e00f5003c1d00b001c08007510240065440c2d41e81c0305120074024000b03004801c662680e24001240302e0070244502441103d0003040030071588a66000e0003c55400504182d041021a22407504070761564020920300040c01c0b501038881003070f1000f00908480850704001c840642008008541661280040780c07203010703000b1050011804091201100d26040d0b01036010b60503400100170600d0341010860388110300a03a0008050b6480c4a409404c030b44042c015031607280000c400c4003516500c01d40c4010a00d0901402c001650b0f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 168339217 1250 168337967 168337987
    0x71203050f0304060b01020d0201111b0309120d02100b03190f06050f0618040c0302060f0714070906080604030c0312060306020c010f141b03070905130c031b1d0105 72
    0xa0b0b0b20440c0c0c10350f4155168030401413a542c0c1049420700116052008210028000030300156500c60780030882d41c0410f040100e103909003000d000b142c1240700000c1c005110000b90306101d07a00d81d0810faa032103025024264040ea14052640200881850b008010349020188001103545c4d44104031000d03280c0401d51041000001c1d441e114450080044a059480501d4254100400d8820100c151040c2e100307040c05000025070070b1408102a42e50444460307484804907050320743e690040d800c01400d41c0f500012101c00009001c40c116060382c0038040c0a0004545449140d41c1c3c0b80c80c1642c005001804d8a40c0f03c0d07001c64441c0c0104410546c1c81400800e0f8250b40b0740b202d0050360491009424140d540c0d03501340503524118032030304007040d01d2101ca22001c0d140c90803050520585055903100549000030002e035141c0e101d44030b0500030b09401088100b0207000144034100409a411034180403a140c001c03038403a80300041680a904010036501c525505001700200c29803156030150003814031505015040803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 168340467 1250 168339217 168339247
    0x20d0c200d05010905010f1a0913020d060915020f090108070201061505030609011e03080a030207020a03050c090a1b03020706060b0703120f020307200c030607030f06050303090307120305 82
    0x8042e010380008901944241059405c641c660003a20143d00d1602400c0d02001c0360030b030720440e61000d044407110741c40d6440981020065851600c001d5000b454440140100032282d4801400c2c54020300d521002181402200c01c202d101d0355000c0c0c04007030b00a016886040d1310234814158414101d1002196640e62003904a8030300b940c0e54500d4020032808010018070b4100145114010000c0217a94540700b10540341c20305000e02103000251100d6400925162004e0080d0125040f095010302194a03013039030703420180d03116140040c07100d101c0c458000c007140b00c402c120b00489012203030b400511010075004500a800950026501f1100184c9600d030000714020241d018007403a0b4000e8480e42c031506030195407807003140c40d03041c00c3c40701562040c0180114079500155500154441c0d0302001d0b840c61804c0c03105407406200c040a650300d8854502006003040c5c1c10382004480b00040c60040c0403060b1a00201a20790069644050705030303010b81002c000344007118000c40590b034040d08025150003001403c0325a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 168341717 1250 168340467 168340489
    0x1803030702010e10020f0406080c0c07060c0302011d0601050f04090606060504060906050310030b04020402090310020a02150610080c0d0f021b15040210020106090f1a01020d0c20 78
    0x101503591201c0002c12404248000c0c100781168050071407500c0040c10040c2220302480c0100c10401c141c8900140c1c501c6084404c0b81c1c82f01c464002210305440d41c4e844010a60410140c0c120019400e20111030104c0d84002045000c4903c100c000d808030341c0c02c00301072000081055603455809078880c0805404940c03207100e4400a840580c0c0c50a55450500502820000b096400881081020010007400d00808a40134003580d07400b803030052036504d80d80000f4000e400781d1a2216410b01561103410f001c41c0c02e6900810a5031400d070207840e04985040380844020780e0417101d054011900401d20703580144034000503a0712690880605041001e020320450880704a05c807100001c60b4006030480c52076007400006c40d00b150034100200104603480303414404940001d40024060300c0c04210400c441c0d4000e401050280c010524100301c41d0318081084000b503e1050101400d01d40b018080c61070652000c103069100b501c491300e400301c3d08441d950b140303c4600f94035070b4801188000c0740b502031050359911440d06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 168342967 1250 168341717 168341731
    0x140c13050403083405041e03020a0801020703080f090114070203120c03150f030102040803070b0a0506060f0703050d0b1201090501050906070207050d06020904090b2d0f180303 77
    0x140303440c0500d805040300704003800c500204010390010511141520700e000b078a50310007040b4007540f018196000c0e6560301a54010300d407150102c075010703184102d907a01c1080480e40200d5001c98000da80356030305801c0b4812407901800045050700041c0504860265694100441c0703400081d10389500e03088004211029211000160800284000204100310529402c403080032405491070a000c1800107031034040540140c001c0d010800004115542941a031340104038610a8075540c100d545002000b06170308030391000106281c000810140c0c203112054501030795404521500d031100c42d807420740e0300703800025005a00c0e0303454594441c40d580310000c0312a440500b45001080d1890f00349042401d485000b00388203800d5100c081086200c540c0054028100c40041d20503814884160800c200684289034101c1e03001030030a0b9203042003100e0722712160300c80c10060740004c0e8001ca1780d0021800e42402c8090f8260040244000b00380e1040301c0507c0f0582200040e80020071601c200031490b810350300304072565 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 168344217 1250 168342967 168342971
    0x70c030512030103150c0e0f011707050c0f240c1312031d0102030306060d0f0e0a0510050403050909070c171306050301030218090a211416140c13 64
    0x40082180c2c5200030f494555007036000b41b04280d6001401407400d180000e80505c43e000c03607030746412aa4011040f00090494860b0408102e252a00700503105511203902d2800c60310511411102070900811300642c078854802d514030080a1640b180c0c5c54000c00600200114401041700c04c0d81c5071211b5103414000d190700b50203444a210700342005030210001040301d88182044130702c00602aa8040112030f40580e048070000c2d00d07042603010b95002407411b100d110b0080d03803409250200241000580c04107852140c0203e074103080c0aa034120060310020b90b001008108d00780020811482c042c5100d6501684030314102401e6422601d070680041d034004421040c617040000e501d0300340d43c02520264042c140a052551071949541c0c040b80e00400441c2c001e030342c0043c940380440d042da0001d0160b4480b160300000e0ba254102d031541c02c00a8a000c3ca2030089000c40d0080800d00e0014040e001501c13942c80414044202410080c0c0f200424003020808c1c2207018041c215401d50300d981c03010440f0100c45036400c0c0c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 168345323 1106 168344217 168344219
    0xe06010506030a0207050a08120c0a02070303030f1b080103060c030902031c020c0a06030c03050f0c09131d01060527070c150203040b06010306090b010509010302070c0305120301 78
    0xc020040d005041110085c230942d07074050302c0c16101884889001e40c4800c0507403011f82c46184000340160300720100c2000880d0180d80201c0d00079400d440049649503800c11814550980f4140460118444c40011320511009100300644422507040820100440d5000030340e9640511a40c41000700901c5500156180b0030303c80740b03820700b0020f0301c000380440d2500c030042e000d002040340f10030000b403030b1a0008140554884010703006004042c20f039482c11400505000880d0016140b8101e0143c45140f29030510b1418070242d1074000c481400000c040b403c0c002040900a880c024841c0031001000482c003030b07080c180c1c20980cac016186043c042c000703d40e1890014411148440c0d4440a544080100014421064180307803180100f42c1e0200031040e10f84406400701c8115440c502c0c0000d03028000c84400b540603900900f016030060000102c010fa582d038920345000103000d5002444400880 = true := by decide +kernel

theorem cover : BRFrame.Cov 168165467 168345323 := by
  have h0 := BRFrame.cov_init 168165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 168165467 ≤ n) (h2 : n < 168345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
