-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0038
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:30:19.968487+00:00
-- url     : https://prove2.me/submissions/bf0ee0a0-5521-4170-9471-5949cc87a395

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 6654683 ≤ n < 6834539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 6655933 1250 6654683 6654737
    0x31707030606020304051512100906050319030305060102010e06070e01020105360703050703030804050606010908060606130f12120201020903030a0e03010b04050405010209030d0509060904150306060303 89
    0x2801c01003103050490181d0340c1e01803441428400e1842c540070a03180010603090315540720344c109a14081c0d01b405244840302034414000c40307400c42d180c10780c001034502d0001a070482c1d030a444100d524501e041038800b1000303028010400e50656403249443c2103404010040507101e141c1c0c83d6074004401900740002401d489026060702140700c00816400b07900c00c241c805003001070207402d02611818504030704440c00c0111641c0068054060541c000081c10380020041348902c0c440c80607036441d65624001075802c480c0038040d404207540004001075280c05d002000f404d9601410745254402c542d1022a40ca80441981001c0780046840a0190812000300d018480c030791000e000950070601a030011035924044c2c011210300300320307150504600540742035004070711800018006104628090a00b03501079801440064040d118060011402600c00d4080e901c9030f0030300810360382c50400d03074000b08401340800403100c0e05030391502c240c0000000d00c18482c81c0003c51017511109003402e41d1580c280f5031220285 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 6657183 1250 6655933 6655937
    0x3110f01062301020f03030a0902010f030207050d05090301020409020c0d0e0a0305030d1a060a020109030e04060302060f07060605061603080c040e0a0f0209130906180b0c0306180103031707 83
    0x8184080300001c203800d205180608400100e072002d0000403850507080c01005500e5010000c140011541d8640040307840d18005e0700c9168040f802c0107012001c0740702c1d11101034160780001c50400030303081c800c400404007440010005420243c4414281040740d10001d24400c0780e90001e54900803507504090303600c441300411160031220754078540b5416142e1207600a02c80540e9501c22034070300006114041d28101c208060303c000e8a48920041c0a80209450b20003600881c20f424584c262507e014090f01e02503d80c0900f5a1307082c05001d0111110607040a07030201c0e06a52951800b05043e1035110203803490b6444481d0310750042076a420003070301107500a0036034810301004000030f2002c0fa11210702250855400e00d400501c3c29121a09000240a080f07000ca03484029a14110781c08100381d00b1460f2403070b002e444200f0024a50f003000c00c042024030070008143c07a03038050009152031910306c06158007000140c611041c130800c400e069a45040260070440104a4001c80008852100c00310780364001d4140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 6658433 1250 6657183 6657191
    0xe12100f050f01080d081501030f050f04021219060b030c040903090e010b070305090d03090510030e0114060109030206030a0b060d02030f090a030206130816060501060f0e01050405130e0a03110f01 86
    0x40517000f0040500140402441800c2940c51407443e4442d034050400302002130820001820020a10140e114054a09a10071200e400d4110f601c800007041c490100c4408a000f1844006940e1300c8401a0490165036685400348001240340d90b00ea1340515420310740710795940020f8509180740744000c4401070b0002c01c5d0740030341840144000f0350001c04540b00610121003680c2100242c3c80c0850f140e05003504060b403c2a0001c0c90815019055004042c2c1c141c2c015000f030280d054581101808400c04491032400101c0c0203070100050f0900400075908a810200e0114150715114040390056218045050b041a8000200003020702070107501034102d10010042c00c180020340c1c40080d42d40c4009003140219000710342da141d00300122441106d0b800303000b50701854003021003030400c0d0700284402d00c119000308206911305000d041c40b940c446861100c0584541c0d003040c0c20b0100341300c0031040450b40309803502d80c0c1781d1a90002410400c9810401486030380c550804002d154001c6043c00e0709540d404061381c1c18 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 6659683 1250 6658433 6658453
    0xc120a020102030714100606031e051603020a02070b0403050a060e030a09030204020901032c010b060a080403030b010e0414060310060803070f02012006070f09060e12100f050f0108 79
    0x2c088110391000d50088454242e0800e4844100d046c20b1048200015692a1150020304950550891850007407240d01556810101c0380d80303581520000c07200084d1b5599400d601c05045402580901145105c51040b2030065440350659041a4460740054a855200401460400c4a28040c030959205070354091800c28002c0e03040030b080c8110f6408024130458002c200c0d220580d11076402040310300c1c6034a5001c103201132600380c0d030030862404d002040541c1d401c0000e51406400c003002120b14030318996940000300d030b681d038800700c0080c0340d2544802d04014000ca182d1481b0307a40c6018018003c031000d10000001c0c10030b082090715014441042180803820700300300300100345001c0180c0d01007680200042220118a02c0120b40500307400660440410b43c619070525084030000e00103200b41000d4692007409a240c102c1030380c200c2100d20800000841c03003441c44000d03041921018080e50a0841221003030a1480b4440f8241c071026401030881981c0d6504201c40d12040c0c42070280145031402c058060006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6660933 1250 6659683 6659687
    0x5040503030306041a1905040509060906070e010e1206070f02010e0703020d1703010b03010603060501050f04030318030602030702010f15030203060f100306110a0806040e19050a050d020c120a0201 86
    0x5010904c01c070741d605010004076003031028103449038070014111070340d0061008001089006070300407a80254a0719000034196080050214080c400880007400e5981d40e40008a640c00d101c0c58005040141c481c00c186d06030b40300d42d122521136500f44009400d1610b40030800500800034401100210780c1002880c0c4400900410a101640d80664405041081c6170038008507045804104990941000000184007d0402d01442c1618102d54080c04120b0b9038100455142c001c40941ca0701841c000c12042000030b0041c041280c109405c4001c154400381c0d039803a020100e800031035a820250751a180e00c3c03940c4000a12803055401a142c000380d180703a095801207550b403503006250088110090001c1000c40801017803640065030300420a009500380746404128a4200304c810801180102c00410300c20700d02409984003070240310700206807000c0000d03c56003100c0300c01e02d400e070782d64014065600081142070010040c21850354001381805181003060080c00d807200085011180c200d908a240142e03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 6662183 1250 6660933 6660937
    0x18010b0603070311120103030504030209100303050f0c100504050c2103030703020307090801020d06031502070f020112090812010503070f060906050703030b030f060403030b10080c03040606050a060804120504050303 94
    0x20740c1c034001450301d00120011440c1d105c0c0541d5180851180e80c000420107a000c0000c0c01500c1c800d640e140507a03160b02c000501c24501c180001408500288038408030300c0482009000e051081c0f40c115854083c41001500894100713070303002c2e0fa01d5000000c240701c0700c1c03c00940e4503c80c40c1018500903402611009515140d0001400400806030000080748032140701e6a6110058541c1100855441c110341d842d0000078113080c4012034003080d00941010300b1842920a88a6881d00301d082c01c48001e9403a40110340a120311104825610341d07410003080440d201e103016140c00c140300d066500302c0d541030800b09850290300da40070034944403102c08113114250340021983c0845a284c10502c0d100d110f11b1078160b000c3c20000c6d440982510407031150400e40600090007600a0780291010030080c001c0c002882034040b5105c100e1000300e220310380803900282900001395030140c000c0314001740382c54880f070010344022600c1d40180300259180c41404207106542036040c41031481410f010389824a4140401e44038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 6663433 1250 6662183 6662191
    0x6030309090a0c0903120906030605100e010c0501061d09070503030c071202010e06030f070305010b090d0213090501090305120a05041a0702010905010c0f0e060a0801030b090307020a0b0318010b0603 87
    0x10703540b43d06400030800e0203902a100507560003880e1041012240c003000380861814403c0000103800c08400003110704101c01d503105945090395034600e602450b68019100c2d00c00300c003005c884540da40d800006019020000f2040302c0d4841000030f101d1400d103003510500d0710050303410842c8a9002000703031401c0f9050000d08081141c4005642e44a03114450006036840c0e00700b0500b207a0440400000c02a07607207139030b030042c92140307925403000c0040c0e980300c4010488174098041d0140c2c002c892542e0160142c98946021650034800c04008203018666036104c40c20f40b043d001084001c0342001c544404521910078209600c200b503a1020021443c058455031042030b040014102aa40244003046a03036200790041d924981d00b040003409114003240005100384c9582c41044000703505020701c411580b6045003100c9280c0256078505416900b1626102002c42018051030004d1108102034070041c1c5400034000d0003000c85910803601c92502111000c10b4418288083d645a40f40201c0d410040d522501a02e1308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 6664683 1250 6663433 6663451
    0x30705060316030207060c120c020601030302060a0e0309060f030f0f060f01080c070506010f050a0909050309150418050a0f0203040c030308060109080f060105041d0a030f030603120908060603030909 87
    0x25440751030b109500070300c581800549150b052900e002d54007a080700028803c01d0305040e040200180014049132203800a002c01401030304040085100021070360400786d10350903640140c92501d01172100148999002d0501614241004020000780040040070147d200c64003500b010003514090001450304074149441a05008103040800d64448030ba80c260341a83e5440b100311030842d6110b82d14040384028510500780f1404c040740020648030110700030f8600d00b07603102008504060f540410800401641c14421000e031006000001d50142c0c14101c0131005455942c0009860400d1302e10f0b042507900c0e40c08040c02c0b860040043c03000180d030400c00070302142e80500c0d10511649a16004941d15856503202d030145201c1c40440611042000c142c1c14101c50089408001c40810300240c0919a00300355502c0d4400e0b0040441c0d0004030b030050440043c001c01d140303400075015403a0790329036018480d001a4680003035518042070041d450200086a0070100440045042c4068100090f0020a0040c09280c1d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 6665933 1250 6664683 6664711
    0xe070e04020a05040e04060902040e01020a02100b060909010f060206070309030e01141e0c0f07030203070b0a1206060309060b060412060b0402070204020f0307090905060117090708060a0b010801050307050603 91
    0x119243c8550165005821052000c02031400d007805c181c005403c0700d600176403190340f9241c14407001c00814070072a014400241c024004c495080780000b40202414400a5048002044011482da440d107003a6406000c0d206071403540141800c50091401c0d0004180d0b0080c545054500703800300382c11114003046c0b860240b0b0f180f03040300007030301e80301520b0300980ca01159140c1e00b0715a440c513004800c60103451100002d00c111003c0031028000240c0e40c40c840c0c800a50907411402c0300b2302a80e0f0f01304008107a000136a041201c0c4010300107001d50222212940081e0009550324000c100b004801c1c025a0001d21048606078142402c02180d651219003904004100e542d440400000301d8a4607010f462456800400454860089920612040d442120b0940c00144c49103000300d0341541920500c0d0082506039103a01d02902c802403500080080034081752214880d44200003040682040b5240c420848580081043d9041030009040a0010380003144243c21064003844582c407410300303070f0340d01950148000c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 6667183 1250 6665933 6665947
    0x80c0106050301020a1d04060506040e070e03030318150412030b04060f0f03021f02070302060706020c070b040609061704020d0305220e0105030a0f03050a0212120106090e070e0402 79
    0x5005000e564006905940082004a4441d400006003030400440c080001340640c1c004041004403001030164652004060005010b10b400380a18541d101e581402c1c110041c9401400084c60740e082200c0d503441c5013442c180c100507034403c00d105031500060303c454008000c0c00c0c136a80d12018448220700031010903595400700340c0c0b941d4468000400520044080a40311512401c00301411140d0380400e9004110003801e0a0760340e4aa00e5801e2404c17501c60317000d08074030b504550811920742d00508050b15010380034014011030342c4003400ba0000800a026000d07075203600d0400042c2c01c0104c9035100e402070041c0c070b000c0160560502d86000e49d200340d04a5800600103454601990640100d00b004102d00002c11070360328031408469080300c10343d0030380060000203030380e207004044d03903210081c000030b200d842c40e00000e0000a00480285c402101540140d808486608441c101c9030380043c0729030030b60060980010041248c001c00800040d110a003101c188030314101c0c9018280e09984440c190185900140302 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 6668433 1250 6667183 6667207
    0x117070903021302090301052202060a0c02031005060f030f0c0607030314010e0108010b0603010803071103100e06060405090a020607030f050418091203050709050d02030c0d0305030a05090601030c0308 88
    0x203101440d80204190682c072407209600e402034200c072561501a44ca4040410b9070184840240320303030050500681070114516600707129690704410f00080500c001447c1c03c000603076080c0031318031040030999800a42450f02c071040008000090000138000d80150b61040903841c804160040b00200680c0d07016900d40d86440c0460040c4038010358207180541309400460a40e201400942c1294030340c2000340b0103803815100300300c091301c000e1040c06c6055001300300c9400010395500b42146134010003800c0e11390b10340301c10914109882040442d40c155820903010884180f81602c5556040316540c00200b03c084403907030100d0400d20a5220103001e008074402d0340955107106d107040301c020786030121003c0d548100006107540504000e02d0100c2c0c0380304280595a800e43d00c03900c1024460300c000c1c2d56100041d4503040c240180b45408810603070b0140a0341d07c408109440b0700441c9240300d840f030760f20329542c1c0c40c03c1c00e1f00300103d50303014090040903007000c00104041008041c801c015280c004d00e46a81d1026540d4034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 6669683 1250 6668433 6668447
    0xe061e060705010903020d0f14030a09050a02030613020411090603130606090603110111010c08010b0d0204030c060513060201060e040206030a0b030607090f0605030402030304060e150304120906030b011707 90
    0x40507503080076070744c6040543c0410041d420810340d442d404892000b09505032404e4a444c0603001c0c44c804240f000581d403030202d40010b040303a03000e030b0145c89111035183c0200c0c4c104074003202c03107010074110301c1282011030800380324040510071a18282c0703040c42701003000500144400390407512007250144080d0184449540150010861690100038103680c84c5800c400c00300701c40796041e001c20506451031060380818001c020303034460103a44403040c0360300b030074840b005540002c9400500e49900740408000501400d0500c0050803040e00e8098032075266100e244004042a0800021641040030400004e071407030f0443c540043d4101c40c000d0b16a580e42c03060704010848454099494811201803201300c1d40c01000603000d40e84e02c0c040b454442c0e9103510701500d26100680700250594410001040600d216003522010408010480d00c90000c0c0c02c02403016a4105440640b800000c0b4010182c0441d04509081d00a014a00701400700d0340b00d000010384552051000c8548450f601c00014007a01e12a0361 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 6670933 1250 6669683 6669697
    0x4030f03110f0109030f05030609010e0901150b0d06060f020a0f080c1c030b01020a0f02090c090303030a020408060a0501062712030c02030712050601061409040204030302030a090e061e06 82
    0x10803030701900e0511502d180a0140300c441907004c6900420080c3c0628410001c581c4103000152150180f40d19083c2d43c8411118001e0000c0625540c403100c0315802000c1d151a00c0050400603520b0ba11489440020021504190322a0303041c404150005003903242c01040000966800c034035540d14a26442c10803100307502c2240c0d5040f085004882e00300404014600d4542c021071500d94017001001550001641d0780d10101002a1148444100300c1005182c203034080f540c40211140c1103810048980042895504140c9012440c1a0045014018010100f201c0756100d2a034503c140403d5140600290840c0c50088683c60001e082c2000c0110480310b030308046000b040c440107030380c04400150a004210000805049110380034100300041c089031b042a26101d42500070014040703a03480c040040d00c1e154200e803889280e000050005c2c510517a01c034806000118020340141d80e035001000c1004140c1d2400b07070080301c8190b81a205001043d1605881003888444c00c2122440114507403000440c54020300c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 6672183 1250 6670933 6670967
    0x30907060e1302040b0a1206060518030c0a0303050d0e010501140f04110a0c02030f0102030103080a050a0201090209010f0305011401030302100b0301021209070e090a02131107140106080c04020f04030f03 89
    0x1400040103034815009200b801e09665442c00050255506c1f107082c2d0300c00e807140000181c070502108540204c1c100441000da4001000c8508201181010550101040d80203a0100d03001081201001d1020702500c060641c88a008000c83c0d070601003400d070081c8a200c40240620101d02605d07565883d182c1c4000307402d0120709035150310b4180910008203001d0002e04220b0003801624a0395040745014000d40e4143c9070b00c4840b4a0820019200484c2e0079000f1040801c02c6649802c0640e003da1160440180a081e10740400c0d02c070a070450400d1400d450504980102c40345c0890010008039a022410710300c1c04c0b10484010501d041002c0c0040d02a020304030404003408244001e005011000140c00710032074940f071320300e10f0480e41c4924160b500c1b41e1011202039017003061801140c1042c0c100c0e5001d001d101e04590449410481e0070b4a4400c45c03407210f05490b0300e590b0740d910300074000100200200135003a042101d06510704926545a0b480d14001c5100050103420380d1010f400405004260b20214683c0407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 6673433 1250 6672183 6672187
    0x304080c1005010501030605031203011403190f030905090f0106081801050c09010f0206040309050402071707030903020406170a0605131a010302010e010c050a031112040f0e0606030907060e1302 85
    0x45059100140b50a11565011916014001840b410046603c94105400d80081360560b841c05004035920b01541114a50600440501d020444c4614500000d02401407181000ca2115494050305404441d04034610461180c801c0020b41c40c181d10800c2c0c1595001d14082205480d2555003c407407501d0801048140d500341401c00280c0109403000e40341410003607a07034203081d0392001801e030b0f201d0748155000740014264400a00c25410180c0007811414882d007401811040000d025001d2078104035000c4001403082d46041055140901407030010705052000e0b00c0312043c1081c83c1641e201c000f030304014201522a0300007401c4034132130150050155001101c26101c2544900800481402400700301e0201e20701d81070810195200304c2c01000c40a62010050100500d203072410769003423828221081d141d03c101044122148400c0c0b000d440100f0b00d010701c0b03000d400e042032011818164024041405503209008201440d900000c0803070440e08a4148032412001d5000421004024a00101030082c00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 6674683 1250 6673433 6673453
    0xb0102100e060a0f02090d060b010203160b09010608030301050f01110705030303040c03050708010204061b0f0c0801060509010801050603061f0b03071d0d020102070b0904021902010207020108100303020a03050304080c 95
    0x86442407103400e50070820004d40310300b4180c9200300e00a080b600c41d0002c201600c0c072000150540e01c5124085014011241400540c541104c2c44814000040794040ba105080c000500d0302402a04040c004d05070240d811903042c80e0201c1d45440d42c058200c4e0400c03822001c0500341c0c65051081202070400501a00d07a03a14103800c0118040f0040d220480f500d00c61010001000c0c0c00c18400e40d01500c0450340c0d6403081300c0c070000702071503824001803064400c0b92090019200154520506d8002400141c00104200c1e20f050704014600e0380c164040d20099060400f004482d5130b02040f0300741d200c0c4103280c06100034141c0c107a4100d070b215040d80003441d590701c1c00000d22000b00e4010300040d91b481c547c0508640302c00d0300e0b10b007444025801154000e016a100440500484185002401e44544080c1c001428011260816414020301501c142c0244c1d40c0040c0c01342c190759004811661002440c81c00d10105851950008d5981491000150400c40040702080030041c83c0341c01c582c0e020100108540240e51 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 6675933 1250 6674683 6674711
    0x1401030b0603070f0303090b0304080903070807051302070218070903080307021e0f12030601111005011d040506010e0a0f02070302060601020f070b1204050c06070605150904020906040b010210 84
    0x20544030705100303224495001070000100d24440701036942c1540c0d4014141e181680100c042c1d00701a0084642c1803007030280c3e910549041104800428404000784905840d080a02080b00b400780201841036004004901c09602d40b6228131881081340c50580307a0556843c0c2d4101d80c02c071601e401c02030890b04000300b809003c0e40d000030b5200c0900180e400b0703c00b00340d203408801e541d142401c1e024041d50b030b08070051841c800e131100720207541d000c0b50604012414810180b8a03d00340544a81d40c18109580d0300018040d06204901c0040380c682c41e00304090322421310342c40351540c2e640305110b1022a012510b000820103446a0043c0c22062072001d400d41d140d410750301e80a9110700c01161010300510454036440300c1010b00240f208111811034100600e0010b50f0305280171a03000c018404d542d00d210301c1000d5040d649a880c000c0c6111401407400140c90f080000442d80e040103c901c44030b04c200c8800040c080940e5400d00841c4d040030703007200d000441d21002d1005070f0821070354a48106c482c51400884c603039401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 6677183 1250 6675933 6675953
    0xa0b0603010c0903120815060d060f0b070c0306050c04030f0807050606040203070e0103051512071418070302030417180301050a0e060106080702070e10080c0301060b1606140103 78
    0x6004500a02c09030301c006000f115180f2a6100150529000d0300070704504030b001e403607400c0e00250f819104207044014803020441da6071161000810311956200c2c108031001e107640d4018090701c0e64030390940c035003c0141c8680c0d40c04603640c00060b00782503664021440b03100000003101c2c025644894601c903105401d0904103142d0b00700d0001601c080c00382900240651400d07100b02c9119003403640300c410180c4000700c01100140300c001c0c502494030b520300740285d24540d00d405803d00724000703c1e030050038450306201d04421020b4001040d20700445c41401d43c403055000b40b405040e8070980034079006849917a04d0803c2d240b0344450314441c0003035020020350101d140c0110340e4260003c01c0d013079009001030b4640010150449400041c5075005030410b030014411140325695094100c40c85104032441e0985550410f0b04190702612008014803204400300444102407042030710301d000403030007003098600d40091100584540780d0075003038541552144030100034156028070021132110598841d07540e141e11b4030b21301d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 6678433 1250 6677183 6677191
    0x40f020a03050a0921020c04050c070309060c0807060b0f150a170105090a090302030d05070309020a06050307090b0f070b090607091203051207030204120b010302100302090109050d02040b030a0b 85
    0x40e0078640016800f0b0464000d503a01154440c04012203d500c5050b0014440140914402140212060f100007603586003d024090030700d4607480d6a82c0d0001d413034098500c141f0f0768400030500200b5140e460118001e4010342e09140d401000200f07028010000103901080101503290b80403003000d009a0300001c0304006030203624080e0700ca060803103006035045e0301080424421607a10400c000c0010b020100c0b20b80244000c03d20a004490800c681d0b4008a0140c41003110488002581e500442c819072400d5010140100001d060061071130420500040995400b4000c002100c0f80020b0071628002400044508550304a0076100071409d200c0305076900c2e00000d0341c904d8001810b03007602041410503600c82140c0c0d940e0540f034903881d0081414035449002001403000043c1035080c0000500045007483c1d0b20344e450b101d52900b000c40e6040d4030411112419503900c100406205000244459802200801c207640003180d40d840c0c0b00149100003030150450000203078040c0a0b4140303200410000403440ca002e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 6679683 1250 6678433 6678437
    0x60d080c0f0607030b0a031104090b0405100506040e0d03050402030705060703020708010c05130e06010903060903050a02100b0f0613090e03030901060b0901090608040f0501050c0a030612081b010605040f020a 91
    0x3551103110b02101945e0b0340d80c0105622a41102d420400115143d88400d85000003500104202d8000d840d40803c881c022142035403150048000c543c034400c8280301f01e03540720008850802c12034164219040d62003a40d007807200c00345172761440450b0666600700414401072000070440e581d02d0002c1c0c60025181c0c03100e4444c2100541c202020384081c03600480960f040c058549001410b01c519100c0b10112070000680000d040c0094180040046070460040c4031100f8003946844e941d5401022000b40740000004103c03030740910f0066641450754816014010281040303035000d0b11009003000c61860200d0590180020a28003e8647c81341c0b800030000d5407040e02680000c00100e56103400399a110300c02ca40d090b6000407500340d01071140394004d0039404d8106008100030761000351945c0ea000d084031016600b40c48070350f0000c00d01c405400e03070600904000c3c1400c0008808200b503165280309090140c1c92101014205070005a14100006d42c020f10043c0f100030014030400e2005042c0307070000e511109140c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 6680933 1250 6679683 6679693
    0x703020405090108190b1b041706100510030f150602010501030209010b041805090c100801050411070c0b0c0a12050702040c030b0306040201030b03070b0301090609180f0803060d080c0f 81
    0x13444480105004901c0c910b242c03031150040c0850b81d640c0303181c0074000308000c200c4803009004000044005000d800545044013181c204085e81d5101a85400b10050500c650050000030901c003a40301c00405074206c0140741004142480c1024852000d4042800c0e01240425101d200090103541504040d0480e402520408841c0c2d803101c910034000d00c0303140928000e080a0b41c0714040c00341e130303258060f03580305501800382d40100f0680d40020300300074501c155180004032a0001840f541c58a40300750030030340118040e5145445041d56035000c0350f40c80c03803284411400020800305000e0300240111030900d944078206031002a800c2101502c1c580181d402a0700580c546950614804d010344101a50128010020401d540c0d66500460140a070344c4040b680501440030009103007500c6034051406000c20003800300c1d0703207414550070703804585140c1c800d19440c0a0440a10010550340541d6100050f004170002d95241d840c580031076031a140c45c2d80004e25000e400201842800b0000c20b440d0300404000d800d0720 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 6682183 1250 6680933 6680939
    0xb0402040e0f06040f0201050903060f060109050402040302010801031101050f040b0d050a050906130201031118040c05030105090a02031302060301080d08010f15180f0303020d030b01021f020d0902030607030204050901 95
    0x1564510441e480107006030701000200f400314407029001c0c5c80252051604503c1d080c1c002c030200341010b800784c40000002080c181444003070340c1c005104401800e0305840440c18245940c0000b410800103200290803141c20701c5180300941d00c1a401c071280c00e140288220b90742c1e942e40c0304a501c00e0340070300d40103030a00e4501004180c02d0200c1d8000c0d07a00880642d030060081c1c0e00c0e228600c20640440d0401207050594480e40c080c44a580200540610b4200c203c04200d010848404c1c04156070300e00e440395040140c01c0005100300c1d0b03655803516030480c00746440140c40740d4840d0030340c44000741c11010296005402000000d604040050110f00300101d99542c900e459130380b94584101180a802070300d01500784010003000045c440c913480000101c50703000c2c1450840e0364008403008852550410f400580085003060101c03a018016140d22600c2071000b04040100013070200308803100d107082c442206400007422618407906410081c811038000b0b00b03440150805d8400a030095005100e498061443e01c4000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 6683433 1250 6682183 6682211
    0x403030b0a03080307030b01031d010c0801080a030f0503090705041a0f0f0f0402070f020414010503150702070b09040e2a03030705062712040906080c030706050d0603020d0b040204 79
    0x10000300c1e54081041815034030303803c0d01a0050481c22050b24101a035030469000900c8000ca10f03d01014ac0c90400024447c8005100618491050b0441c0a056002141000000303500001d1807010310f099180081d140d458448aaa08200c1e60f54030040d03000381040e44049030420710801101c50350b5012103004948200f55000d00c40b4680201549550200c0584028039050900360010301004e441400c000354035074607550005040b9513490f6100c000b80c00040005005504082280140d580340c40c0812050364503152900a555001c60700442a81100c0817518800645a580140d09541c1f08042a5680a411042b112907481401c00c1e5242d803225810ba00c0d4041c07420040700301c80700c02d50040040c04461303680180c4041d6140d246084020031010401460403c50420b02003020221005c0e030308180d580740390001c51300c15a1345a030000285900044030703000051340e00240c040e08854290500a817268076202d150402803460b5440650407400da0b0844108009980c008a0700c680d02c00c6030304210340f00f02d01020f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 6684683 1250 6683433 6683449
    0x1312081201030c0f060f020706080c070503040905070f020a0c0323060901150b09030a020d050f06090c030105010e0106050702090406020d020a030912080c030c0f04050d060b1807090e0c040902040e0403030b 90
    0xc0c103001f6070003400050100740e1280a003564415942d015041c5484425611203240d44d1180d8400310311a9500c400380081140c2c011150407102e0707c1440140324100040d2642c0f031101d1003c0c40300801400c02e6100446007180000e40080d04010020182c465503c1c14181c554041d12101b0a01450f00181220211b20300480310141c41c00e03550090010f20b240b03039040c2e0903c44030350b85406082d40c2600c03519591459003031042144030711030601c1202411668a2500c141801e585040e0004500000d21100520840c2d60050a541c0d100d41c04071050754460f281c40c100100240701c1d00e03110700040740c00001c0d00000f41e42c15070060140b4038130440701d44104441440e4203c452007001c0e111201c0c03590003003000c00c00d085149406401428252110b01c0c0c64a07655000050a100b401c203401c507919501d4403d404803524108044c04007074030301b684c0607202034501040002c2c0521001c1c0500000c528400001c10740c60302900d800d4801608080030110b5076580c0350035a000056030b04035000c500090800c0001c1c2440e0401c140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 6685933 1250 6684683 6684707
    0x3010e030a140408030705030406030b0301050c0307050702010c050601080d110106050105040501050f13090608060a0c021c17130b070525030201020706050406061701021312081201030c0f06 83
    0x1950070414580400c444000c511a03403030701035480612000c80e01000c240700a12125224000039652540b03485406410b48a80c070780c030f441c8030740d14080800004504603000c40354810043d14049a4a082c1440140d42c1402c0542c8090020f1140c00004981c0e40400102d030142314102d40c881321200c02c1882c0d00740e0300380e440ca1700689001541c1880108920f501a0b405801542c803844542401d1002481048803111581d601c0052042c0d142c030010040c400040c04001e411001900040c480c0500700440a0758070868101c00048a240070f14844150038400e46072a007880254100110003402c00b250074680485480798180da60001010101705024012002c603048514240d8107038120421802200310900c0002c4d4040e400c1d0b5400b0407212001a040384103291049108620009080d41040381404940d4005c1a81003c260310410561a105042c07a015000300e442c196940c888802843c904601207000b800d9904408008600010081000148459050751004800b1950050b9134681c111116403940f0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 6687183 1250 6685933 6685961
    0xf0f05100b0a050d030c05030f0a0e1002010c0212030a06081002071b03030206070c030306090905150a0b0f0609010905060703050903190308040b060a080a03050304050607051e07150203240301 84
    0x11080d1380000f801005c101021901903c1601d042c1a01c00f540c0b0307081c5a0000460780c0c0004e0002c03100354610318040d64403940c10240e61008003d21000b040000c2d40e035aa0505019150b114080005a000d41d003540141026000000640c2c0c0d410b00c4240205010350400301048815845c90b964085c082101440da0354112505036000303103683d4079181c006407060064440160105901e444c808a420001c60251300f0031f05104900070094150011a00c07440c950001e00490655820000c2d004034550340c2c072056040020003201d869960304005d000580d40e1405076800a0740040000c55483c0505400101034890340c5419400d40315207a0301e421000c0d64502c40180018003155555000c6000715031424030155110a000d030101c840705880b4080301d0f04e003851188040f00015800000c10080204c240300e8650020300f14100f05060054001880201141e140000704d60004085640c505000a20402503850104a04115038900303111078080b00c0300003c4225505489400144c00402e030405100f101c443c00000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 6688433 1250 6687183 6687199
    0x905070c0605090312070c0201030e0319031d010c0503010305070509010b07060905151906080f07030b04030201021c061d04030e1009030203010c110607051201030206070f0f05100b0a05 81
    0x6944460081c0400b4144601e280700c01e02c401c0c400ba54130700c810b01b80903032502d03190b40c06042c0061000500740c4c0c0111f5170010346c9030014002000000840407485200003054103011400080c000030503c8044a048038114141d82086078500300681c00c400190b043c1ca00030002c0d540c40546800510038a000c0a22980c00600e034100015000f04c0c89a41c08100759901c160241c440703068240f48811071148003034620864081500d0340170b01050343c0758801e5030300138003520b8040c144102d0101e403459101e000511002c1d081d40c1c041d00c0040c1c01c0601c01c1d4121441c0d1296a1040e07a48000c4007029036000300420302600e00d46541d010034880881d8401141a03118a605555a4110300952014000903a0b801640c0c2801d02c00d1a0708080010703074084c000d10b40702c2031040d0b44004501000c0c1d0799072860680050034120034000c0070032841001501042e040da0640743c056606982e00c4805181403802101c40050182403164258011020441b021401d00e0b040080e110302889864262010030050600b00e10032644d0058032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 6689683 1250 6688433 6688457
    0x100902090105040b0f03060901020307030c1103031f0807080307020406060203070b0c0901020f10090303050708010f0b090f100c050705011803020909030702030d0f02100905030306040e0c03070b090901090507 91
    0x80354114120090300a090900c1c640491801b00f4078055080d00d040510365008010814074590600c103440441c00c0c01d20f402d4288074000082c040d02d920003d00a0444105400c60b0106102c00c0500454010290301c2c040760a038540c2d942c0703026180c0d00a410101c0c80360707003800000110180f00000381c2d0000c980004c13a40d0541d40300c1c030070800c0b19540008621415805115411251030358107000b20364900040910101d5031020a240041c11114002c006406000040006010340090341c0c0043c0c06881d02c000503030b41d48802c00c0000038a49103e50005561001075000303501e44159000130500181c51044007154041c40c5c44000641d130203441c4001c441f0280b400000c080000d0314041d4a01a0801e014805882c9009140e80220341000e030309095040129489500a01a1aa04201958580c0100001044407454a60714603450313101c00391905200395169a0424641070091091104403d001011104129958104132030b8981003404010b1142201c00000183c0d540640901442030440350381e400c1c09440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 6690933 1250 6689683 6689689
    0x301080c04090c0909080910050a0c030809010615020a0605070203040501141303140318030604030804020f0a09020406030b0406050a030c0614040f0e0105091f1202180a02030603100902090105 84
    0x140c11005807103c0352020300000740780c540c5115242c21103000f1590141d450404c0414003040d002c003040028104181004084682980300091407c070551610749507480f80c4038110018058000741d0000c00150344400c03008a1360780d0b0000b40519410744103030000d104640e00c1c10426602d030b0141e13205e81800710300c0320350380d01203110140740c01090703d0704112400d42a032641b80d45a81e0100407020003520755552000403004083c07801001c405a6000e0b0440040001d481c003603400502540d0041c00086c025044000c165000b5a140b95140d030240091410031502c555a0b6030000740a0091043c0803400781386460000700c0c150400b5104001641c1c0c22a4488420f103240070012503144011901c01c5814071002e100200e0141c040000f104014445031500c1040e6506140c20450004000b50240c500da2002d66500e010211f082c3e0a82c104070f41c4200709140000500e8004a2581c013000c003c4c006074440b2744001c101d04c03998254060360280b10700740c08070381c450700f200c07034902003121000c0401a5200814200400c0549 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 6692183 1250 6690933 6690941
    0x102011a060705030d05070302040303020609010b060f03060d140610081501030803180d050d0c030912120b0303030405010504030f020604030e040c030b040c090e0606070803010308090f03070308030105010906050301080c04 97
    0x38443e038100d0746488601d080140c00c4842c196000b800090300041c040060590410645801468400c000c102c0310f107092002a14500c5601512080070384080005000c6683c3d4800303500b109074101150419070340c03102c0740c09600c810301161381242a141d03061020840140000307a40c1601c1c0001c09501c0d04507425900c0301740e002c6d08018031140d11214510340f02001000d05001e501584503190300d849440c2e9a01410300415124100c0e031440415103004110300102d040440003071049440c60038002c140524130b03480030020f000c41012007a0941700000500081080c1540642e00c194020f0340c800400c0f42c0300e040200c1e11000300741c80140c0003529405178208140341550011040410038200011100d684801203400e0b20519a12035010481005080240900313850420350300041c1107a00307501d08840b0b9690001c082c001804083c0c06654042260b40c0c8544421141003041c100003811900015600c3c0b401d820309510034080c6d280003038000100010107a00a0741928142c8000300c000c4c0400c003c004003804028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 6693433 1250 6692183 6692197
    0x306040603081204050105060402090619051b0a050d03090b01171e0c0307060f020a0807021302040f0311060403110d050a0803011203030b030609030304020d050f03030c07020108060102011a06 84
    0x1256803a0400000280c80c0b4008140d28101140e44002c0741c60039041a90844100414130b0f80100c1c010003001c43c4590380e00e812034118001d000031450310032000750000c40d0907000e0f11790451101001c0003a1014403407400144940307100d104408841001c0c0c04c4210880a44030780d200d0040c0a13086032001880544611074980c610201c2080480364515605102d00c0364090700011101d01a401040e0a8249402c0600041c00580090b0500200f03004401c04029903400c0303111390140c541000456100e08554441c50f40ca41080c0e03104205645641d190030905440700d105101c122603201c010140c00b0103904004045e01d040f6504002c03c2405010454140b03d84034401d0241164280034401c220f000080340c150146028080812440700030152924024046400f001e6070f840c0700364010001c2240412000003266803090303060301c2e01c44100d101850300c00e00e400c6030f40d010a0001d00020040080030041400a07203201ca000766a001d8246c1c9618005900700c888125088518821011902409080030002080d003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 6694683 1250 6693433 6693439
    0x1b03081204050307050a290c0d1104030f080405030d030605030c011407020a06030e1207080a03022101030602030f060405070206071805041806140903041401030204030602070b010e010b0703050304080306 89
    0x40e00001d55211410300206e16005c03225120600c414100f403c698512148501c0400d8031400c4507800c1249000300d19020f0340541c52400c40d2a140c415540101070400e4900443c0d1000c40e500068143c0d04d00f554240c2c2050081c81e001c0d12810349044107141c400d000b0b02040710b00143c050100c00d000d10004403002c1222802c04050040100b2607000143c8075003000900a014903903000902d1011900b0003401c1c9014019004c501d410305120790404248800121200400d084c140184c0d100d000c0c50b58001d1a56a070b00700080b402e00d03108000401c4c40141c0d001140305c0c02c0c100591005c1641c80d00208003c407113060340d900340140e2103400007c8040d8000e48188950074140184001415070b10340c00201039030218110004510030403c03080d000c01c003840c0515880c0a10131344101455103000141da0b13640380140d110740781c100f403200b090008582e4000c0d0f049501440c0c10600640d6100d00f5410108141c460a10038034903a9880701c400040c81d00b810a044c2c1e815140d15980707071851603d039501c60306d085401c09014a0342c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 6695933 1250 6694683 6694687
    0x30b0402070f060902033a02070803030106030e0105010501051c0b010e03070f0306050601020307021c06140c0a02070614040302090a0f05010e0a0b010206010f060c060b04050c04031b030812040503 86
    0x2000c02e6204510340b070510302c140c10201d140a424810b16003402080381002c400025a040c84018510345900007008142012041c5915849220012440c6c07102c0c41d44041784d1070200100220b10241c0c103800150510314100000d0202c0d03640c440044032036200b049005011503d0081c1750303044204190300a200f0b1600d051408005525500b40041d060030601c1e800550410040c41081040000c03a024056005800340095800c10345036401182141200c50b1a503040b01d42d20344540c604011066008450000340310580b0112840c3c40148400725030f004030140c0026208040000400704e00c200d444000c4809290005030900703142d9400c5c4501504003030610410a6180c41c07401214080300d02c602802040d094403850301ca03050084044040f87c40301a2000d0442d00040d006000b841c0080389010100c506c3ca11384801408410b05041c00100701c1e0b181c6043c5d00905100c140710500c1100e0f07000e4010780b406007030300c09a09140c0390201030702c0240c6840b008000400900141445d401000b145651180c0102c060724 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 6697183 1250 6695933 6695947
    0x201120b030703020a06020d090b030f01032a030f02011701060207050f06040308071211010509030901080703020c120d06080622030207030503030c07060b01020604021e030a080c0105040308060d0f03030b0402 91
    0x2c00c0c403171036504041d0050b880745480c003907038952154824000f48031180059241d130a04881c4000101414080980142880c0d00c0941d0094201c5d10002c5080e80c6511161400503142d142840a4803035418060340014150f00d1b600d0380f030601c1820014100e45454004001c02d40c5031000b07108a01e40c01c3c551082c1d00c18814480000403d500c003005200062140074181491001000301070415040052400c11a80c03408040014403403002048650040c030900303102081c1d80d1744c1c8000300c0c007900c5002003054039030060300c0b803203640240d1440c0680589429850305010281d11080c000d0b942d020215031010a48034240064031815a005210000580c060f1040c0c030f007959200d803a81d40c556070003541c1c0e00d03840100000c0d1003030500c1080d110314092080240b014207001d00306a00054541031117405800c24a00030800e40c14441d660401c1818015648004202d46401e01d192205000340021542940400d95500000c0d040e071038140454910240d02004440e1a1045514120001d140d02e003440c94001d68200155 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 6698433 1250 6697183 6697189
    0x90c040507050d06080c0301150e0103060518010c091403160e040507030c0f03030e090c0a110102130e0402040507030e0607030203100b0301080307020a0906050105090906030a02090903070605010605070201120b03070302 96
    0x200000e4070150004140641b2104285421502602c80c0000d412610800c2030210100c0d003019281140e80040700801c55032101210b80c81c80d01010001d840b01c540c60040380c4900c0715040701c000001c0702d02c0761440290304089102855125021898891000c1c07860913000d101107c104040d044d0003d000e1012988441d4495841c00a001d000d500241d128241c40704d01007040661009101a0408003910500b030340d4106402661500d00134081d82c0024029544062050501c00b541664000c03c000340c2d601203102d558001c40e11038850700346ea003640202d050000140c262800790180c0220341881200401c01683d0b090780880c000d410140110480711098100061880c00d107201840c0a4090311004c4e6a0f01c0b0854410850112819030107104e07241d04004080010fa0f8100d81a9141c40300160390209881d60340c080002d0030040c891800079400210901400309803800000a801001d114141c1004140d032a00c1e0300b0740c1c241c01030380e00080c0081c01c1000304410720016a000000783d903002404880e175031601c035800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 6699683 1250 6698433 6698441
    0xc07060507080c1e0c01020102040b12190515090a060b0306060d020706060b0a0305070f0818010204080303012403020c190201210c020d030203060303041401050d090b06010905010503090c040507050d 87
    0x1031040012a81005150000304c1445664403c1000f40000c610b05441c1803001c1085006d503419202100c504176001400b2800380c0100d00e021a044160108901d00d41010f1140600310f1541469000d0400ca1001549400c01817049205880042600d24103560300c5404019044e4498064090260703024400d8000046450017006c000d0031485007855268083c0080080403900010004410004146079134190b861300300c4001604203071079800c2041340001050324980a4400c503844031400e417000100002c0c44c0504081480d803001d01c10752034145c40c848106021030aa0040305060303113440d000341c40b4114180c59001c003603103a81c070703c103050450102444070703100038840c440c9c1c484003403120f500c8a40030f4000b9541400b0441c10400c0b1410114114204000426038030b01542c0034101c180d0224044041070344e030060301618108800d000090000301054030b48103052100541d105c50200e011244c000c1034540c080c0e401c0c0d911810112005081103001a03013040040c1030060b00500a001c000c00c8103803920050390007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 6700933 1250 6699683 6699703
    0x50706020a0206010e060f0918031201080304050102011103070806010c020d120804022403010302061e031501030b06031e04030509120304080c030d0f080601030605060706050601090603020c07060507080c 89
    0x684010745c90000304a200703c0c0018035072071003014801e210b8061969180140c6d0b402c4014403a64070440d900145200b4503520480036005a03604807200002412240040103006965080e4002d20a880141400208500050724020046002c0744005100e9520030a0020b1010740001c0c600e1803c1e110a44a0070815800100400c0009141404200a42c24250520414407901c0c1c00840e04040d6107401c000007500041c0802031181c08000b8038070f24451802c10209072034081e05800d29507641000440c11014418a4010601180c1415100542441c222055901ca400c0030071002108198110300b41d4440da000401c01c6040c0030040c01401a2034480c40d0f0814070503613a507402150f88a080190035850040109081d0740300740d0221601101c51940010011042161800d0403640382d218140142d028140a030007031a000940800d81d01d051242c2500564081c50080c0c951403480f64940d10200d00342d00c00e54000403141d40c000c00003004454807a00c000d283c001e0082d50020304005012a666061404e201 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 6702183 1250 6700933 6700937
    0x90f06030510050a0f0b070203030d110307020609150403030903030e010f0603020406080303041a070903211b080406050c0109060204080303010806010b0903060f0705130602010518070f05040903050706020a 90
    0x40810514a10201e40e8802602d41184c1c11a0018038068011200500f980586141c400020420724119242042560303030030301400c42c082c0b05951800d8004200d6410440d2000c00611482c0041050b000002c5221400080500369003520340d52503403010b4010b40701c60700d012020036544245008640e0030a210700e805d402415800842c01d207181d130040005488039a000f000c0c1741c1d0000c1050000003142c140221000d01040014402d43d41d070344010030f0f50454080da102030160010309459004042041c0280c814078015900c510300c03e0151f110149090701c400e01300090601d2401c0205000071400340b0003905003001c8407400402c07070b010150342d46c0050360869407000609600100060190361014403096000d0002d05500e41e080501c07090019a5410000d4208900041c0c03081c00f0900540c0709500700c400d001e80c2c8070010210b990f43c0c0d80000b4003d00701144e2a80c0c0807502c682c41002410400b24040d0201d88402030105007080c1010100310081020305000c509200c03040010100141c03042c00501742c80340c419 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 6703433 1250 6702183 6702191
    0x21030c0f010c0f0206090304060e060d0507030c0914030a0201080c0d02070c08010b190302060703090b030403021006050604080a0b0a02071209080606060708070f0203030d0207110a06020d0906080403090f0603 91
    0x3000b4090a04000c20500c00c055400213010403101c040c0001c1a18125070781d03450103000c003000b44404504140708500c6034800c440d00f400101700c005030309a085519400f079203990b0352a03183c1c0c3e2544180c151000c0500f075140d04d500703e214010007642c4a42c20054201500441403885c181c1c45085100486c0c3c8413402c115401a6080402c0040510a10920119041c143c84106103103518110341d541488035408002e204100110f11a0141031084c0d504001909000c420155241031604000e0b5958441d11841c164030350801202080f0303030800310103960803202410024512110a07a480c00003c840c02421003000350b50034030224001c00c000c170310840b00552103038640340700e0703a0304041c0c110341420002401540541d000f0844034000802c0d4108a40c02150086075018003103405200007030540c89600c03200f0400720b001050035410f10101012101002004844a2900a58400e02a030300c80640346400001700302281001c002143c05002c1450340107201c0c0c580030005546030070182d40d6082c295008000060f5407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 6704683 1250 6703433 6703451
    0x90606170108060c0316050d0501060507020415060212160c060f030c0c020f0906030c0a090f0f0504020108040f0305070c03030509010315080c13060902040e09060c03010521030c0f01 80
    0x100480a400b404011002d0840c915080c451a5281e11001d802e50301546104400104100c0c420005d0b500c106c841340206202d1541e45c4c100041180d0060403060344a186042c01c0e0a001b503210644060440d4441c0d0007401d01ca001d44c00c44001c0c141c100c0140c0f03146840036001c1c05070008100018000107020562948581b203092500b0080c04c0781c0301b502410040c0182c00d20100d01580e03441c20b080c06070402c125080300c055034407040400d050001340a8002e0700292664804651410703541c00c90200460707030010421402483c50041400ea400a81d0042d000ca8201c0c004500494581d4681c944651300a0030004d14081d10784c1d0b00c41c06410303003680c0306a00041001c80c04107030300d40e40760140e420400c1740840d4080115042010481c0c540b40501c076040d109400c01c82c00100c0003815504044003d10000354115159680d07284903080582c411076401e20b140c082c040001e00c4c81d600c040705490589002034450400050302245030f0445820030b0415041030b200c10b00c45100e98183c00c0001c0820090404004211155 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 6705933 1250 6704683 6704717
    0xc070503030a2106060e040e01020903070303090801111201050f010c0f030206010e0f060a1e080102040906030c06050f090108180a050a02090601020a08030609101502010603110607020108040605060a090606 90
    0x20307542212400ca070b800c00504100460340580004400c6c00100c900040c0300c001c10300c2e114020312806038032507011b0240344000420b06810100013400c884415009100c42d002c6020002c07414803807050009003102800d0014820b0382043e80a2010300201030500582e1031030291074002c9021401002103005078809001030100390442c44080d40c000e1059120395889062400010301034281d213008444002500242d524061780c03801070010b0003010b456008564454a44c00c030500940b0305d038002543c0c00075a00c4e1000903180c1c411011940c0912480d074009003014001401100c5030360010380840c2c0d00c856404e52400050b0b03803d20466014030b1254000707000e21344440c81441009034008181a066412030408040828040c100700c2b42c0c401e00c110b41d0756200d43d0750003040b0b650310800741c0c201000b40c03000c0c692850441c50b015070101050307a004200c2c441d807659004040000c0362082100080c0011a00c0000c140003504503040541c0041008182d22034403921602a0001c40b40140d10140004030300001c03140f110b078 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 6707183 1250 6705933 6705977
    0x10917010603050a0c090c080103050303040201030c02120f180609060a1d040f0906050a020307090509061305040803090c0303040513090212010c0203040501080604020301080d0507050703080a0306080c04050402090106050c070503030a 102
    0x5405090072230081d071564440980347d0000500190602d500c81c44800c80d030a20030f014030400b89005081c0c47d034403281d488240d01026001254000c10b40c03968004100b806142c01c030f09840101c40d0041070340745040780e0010110b820088a50042e00e6629007400c400740b507551203010398044414400c0001501e003031326081c20403e503400a03086004651041090105036a4054168000e0b13a805443c80300c816103c940201340d40703040544091030342c5031030030007030104015034440214040c40050341180d58440240e030030140c0b00d125a01c50b656010343c1011b0141c4a40800e5000341034014001800880c5003c10ae400c6c0500f9100310204280060700005010300c015a0000c001e0385e0401001c0d00c0442c1550f04004081d0703500c005103003e81c1d0500c140030500c0d0080003410031019016540c0258956118455403c004d4040c24803809150b00900400100c0703000c9050030b2250512454006103041c0722a460408143d0f110303840343c3c4d0128064040c602d800b003100d440802c014409041c00d9a03c80807010034201c0326201c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 6708433 1250 6707183 6707201
    0xc1707031d010c02060d0c02031b01020306030d09050901210c0902031609030b04080702060d0608060f01060201091208070e040216020f06030408040302040c09030b070908010c0905010917010603050a0c09 89
    0x4080b90f004401c1c00740e2200000c3e6241d8120302d080001e410486000c0a9245010791a0210312600e2056003172004c0c1041900518001d0b1000d80071110080300464003540c8070300c0c160041d1600032018600410000c05080220000410400040028510103403168221a141500041c4003950000203000715408981c1c12103201248a244c200322807801c42c0d988804415002d00043c8c11440c02080310b00c00c1d540d58204480c401054202c04211050780d9250145e26540112088807501c0000c5000249403030041c05500607039548480b10300c00c11100b46105903170758080074003a0001c00881110045503522644020000d0300c1e480940c042070a0600e2041120414107200f01a004040c103105101c009805801510300792135045902140e107085000701107850007500c0e030020344107012400c10b000360290046900b10588140760003d1128440e00c490580e0640054407e06000811402c000c007d1145c1c40700c3ca400303d1000d0200049116030362912882d24001c02108155002d403c020000c10061641d40300340b60385 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 6709683 1250 6708433 6708437
    0x30c02060603030c10020703051204060605030105070c210504050a090b0a080a1a0601030207020d14010b06040f050d060204080304080303090705010201060f05010302031005090a0c0206060906030309010c1707031d01 94
    0x5041e132460b440b9a00c441120342e020803040e4010a1480405014105030b816500100f1000807007442c1a044c04005001c0c24460305000c1d503e014007264005224881064005030084500d9110401c0c4442040341c0b0000b0044c184108501030101050139a249014180142a2518040380c902102030404c80d5120315540306401d00e900c0f81e48040005510002c01c016001f9414004580580d00c43c001a0060b22400100a41c4800c400000c0750401001d2521040d001003890300801c0010022001c2c4101840b850261408001046004000c10b1502d2480b0011a5200b2100903003840c0e42d5296542c40d42d040743d0000c00031600080300308199904204200d0b0001c00d000d2000b40a21031505a421401c101180101c034100f5800100040441208184c00c10003000040d200b10030904c4c0c94500781004202d0111408010300401000c80d186290605205000b810010702840c50000510b005681c1e40c080e000301141d40821940c444802ca03140b031000341c20010700941b20018400c00c07803219025042c48840c2d4042c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 6710933 1250 6709683 6709687
    0x7030e070b09010906050c0f030f03040605070903170901050d020414011106190b030102090a0902030114040207110103090c08060f010323060c0901090f030602040e0f010602030d020711030d030c0206060303 90
    0xc5507a48100c50004a580b1414203d0b80c48411080203408c10702d40040c0019144000605c1820064203080114070540c011502007004e603d844d942254001d001d40b1020b4003114800044207001c10700b07100101740e6001305042c0240740058007188142642c2095200b940303524074101d6080715a58100d0323043c00c02c035110b51000c1d000d07500c0c12a014110b80382051801500c0266070710b1311080320303407000d60444900030001801e50030102da50703d0002d0041c0d0f20074002d180c000d014111005015003064002d840700240e01120303903045445000c0044004141101003a9000844000005584607081c0000b034051a582c83c04003401d581142484400143d5400c800010048240c589901d1290046105070b00061000c020580d5444140012200c21215030000361008407034200003c1041b08a6001300100e86030042c040503640e0b1491540b01d0024800d11805003d41c10800140140d043c50b81e005110061098407501c1c0c007a8801c0f00840e1a015402c08001d001c00d80d03800d951701d03406404100e02a4000800c41c0158 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 6712183 1250 6710933 6710947
    0x30602040503191a06220507020706090303050702061e0403050a0b070c0f020d0302030d020c0102190305100306050a090b010603050f0a0e0d05031801050403050a0905030304060801031101030e0607030e070b 90
    0x121480c0c03200994980d04c01004041500c540d01d1103000d6400031603405042c82d91908005083c1c0c0240001d807580800b41c4191640061201e0046090004503500350f00c609081200c1d0b0f4080c812194004c100b2810a04103e00a210307040c1d100b44050800355004000038801d181c01071031319681951000c1e02d25014000b8a42b00310300020b030601c50ba00036043d810794034900038486924083e03145004d071b41700900e925400441d56000710a41540900550003221303030030004041e88900d06034100c0e03030140d90100d04007280b0314051022071403070741003941c00c141c4124002032440c0b26901e900100000a8020000180d00e4100740112640070f25006a0000309040d0100045078074100c9050303441855110034800e104c4003000190f00d0b000043d03100009402d264009008900e0281b070010f010f0340c4070803044000314103111030210b0f9500700002607400303a880703030f85a114599080d07444640c20090030b401401c0c101a190003480d102c0e03440901010b80100c5c101e44000c920341240c0b04c0c4184c20101030741c00050101c03000384829 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 6713433 1250 6712183 6712193
    0x308011d07050702030a140115090212010e07020c0a0b0306010e04060501050a1d030604050c1008070e0111010b03010c0e040b0414062107060206040303050a0216030305091603060204050319 83
    0x100e8002000c2d040c00d607581c24240c8082801d0114185015080c0819038940c0c0e01594011b42104040307911b84400c0b0740c0000d450351190002c90051480140c040c544e0600103100300085140416080143d90045507001d911910024910072540d40140c91024030100a100840d6000b03803054207040001c945c248425801c1000082c411b000f20807142003000799400f00070b0b042002e141ca640541c1003015059622500e000e0a00302d54600800540c45d000340d445100c4460424440c401035806404643e03030780c0030421101d00045400d1161580001c803c1d550715826401e080e5400d114280340c1964544601251a4540040100301c071704580146d8003440c18200904c43e903101410000358022812584000e02c052189140c03809030300c0d030745031006541c0301701403000c200240c00185c8284640d00c02d40e01400150f0341d45098600364050380044201c08640380308044000382c025040b040d40802c260341111540d1070001e0303102d40f80d40e02c00d600940d00700341c0c00101480a82030600c40d05003080705000001d070460b0078550707030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 6714683 1250 6713433 6713489
    0xd0201020c040c050f0301080307021002060403080112060e1b03070501031806050a020c030304060203160e01050703030c020309040609020c01050610050318030405060a0305070306080609030f1303020a080a030801 93
    0x4500c070383c1c0d40d08040e00703040b4050810f95081200c208085c1d6241c3da110340700140d9030741c00072409a216048005059003414800a011442641c1c0359982051030703441c185500340c3c05d4641102c12145203071901403040405400300148030b0f8200960344d503601c0f2114072500341400d2081c141c020718101420804021982216100800c4407280d201500181a948440485009006003c0c821400d408000140024048181c01845c0650b24900c6038485148843c4015111119a520081e022401c14418400428040d5000c3c05050700e075801507034074201001c0d0024003181d01c550031400200e60f0105800704000000d202c1e00381c2c03004044d11090050000180c0180841c00000c03d8482c59000c40b10b8065601002481564011314000d403840f51919a80d01c2c000d40508021180f4000103803601e80000340c1d00400080742c2d0301030324400780518a001441007aa1900b0752000000b82c020803c07040c800401621a15030901c001c0800f0805030404c4042460010601c43d0103030700c08655110750030040d81e003158020032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 6715933 1250 6714683 6714703
    0x602030a08040503040e010605030406050f010f06050904060f0605130803161401060e0a0603120806010e040209010201090209040308040b070806030d05030403030b130501060f0206090703140a05010e03180d020102 93
    0x901c049a903580b0301e000c80ca54421600013101800e806000082c25030b0300180614040d5218042c1801565107005c40300350307001024441d01d003102010303130300030007070140100e00409011101500c007289103034a46100c51540001075110000055002a0181c3c882104000007405014088080c61616081c491841c901c00c03000300e000780c4031048181c684d041d0b4040035440003000b410245903411943c0340c48042d85004004501c800d5400c0e000d1201274511151060b0070b518030482058442440540d0310f103050000a41042500d141076640c2d032039809000d60703102d00c09103108a00c40e655a81440ca05440c11420310880a401c1c4002e00202e2024800240e03000b10302c02100c0e8a0038949583c0300c0e9201c0c10101e001d401841d20164000000c0d0560a4007000250031540c16640c503034881b001c2280170103004a0743c0302c00890b180700c1a0341002c04240700160529103080b2030003540d034040701c02d5a6199140c9030b003150301d100065481603000040e4821042c12040c5d5403c03888000b181c1100404c6001d0300041c0d240d400b100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 6717183 1250 6715933 6715937
    0x1a030d08060a03060608010902010f05030f04080c0c0303040909030f080c030c031e0403030e0106061d0906031c08010303080708040f1211030a051206040513080a020a080c150105010201060602030a 86
    0x440050116200c0b0b007160401103410a0042c031885543e00f50650090070b100d171050780050500d6240c0801c60780550210303400b0360030080d8031401c03583c4c0e00d40b60784030940c100c2841c1622a02601d0b0030b10141c0d99081002c1e00281043c80000684544980fa0141109206040c1c000a1002c90400c2104105503002502d52040407040840d42d80d503104403000f590108100700300c5403810700350420712050643c103a010b60f104045907002000815183c7c0c1041d40c8054425003e05011600780c0141e0100d400d10352101500100d010301200c050000c088851048644060310900c001040300e00100241640016555008046428600c0136400d0588450015240844010300546030712014001d540d40320340000d044a0f1700c41801e6a860354060040201298011820000e1f6807001a0100e416464644203036802003405223040b1154101d941c2d40c2c20910303041450003e00f580100c1d4651001f080d0302c0c800030242d1061400c0039001d009900b001a000019040c1c100c14110380c9050018840c160b000011070701710300154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 6718433 1250 6717183 6717197
    0x20303010b03150406060e010306080f070306090606030b0420060a12050915010618090209030a02100302091c02040e0109020a050d080c0111040602070b0c0304030303050411040908030a1a030d 84
    0x5222000f5142d16920219a0010701d4808006506a48100200000c603801d903000c6c0308580c2c0e10305e1800e95070354003075040c0c810307942140404000240c1c5036482007040510640001c98002c0c0d60362103081c50785a084500755004250300244180200d110700b281c0e0000e0f5800c444183c100b050030080240010351440300809403650380c10104030003800030011800a907010000d500d50540e150a030041210801c84c03010f070f80400d1100004070303a0403d03034002e481102d200500102101080340c0c080040003ca092148000c3c180d080210700d000382c440600b0740005108407100605842d1644c410b0008581510b15224032b181d1400e0746010050b503a841d644012500e048070324090350b84441c28400007a103d03420301201c41d0340c07820054000741817848005d0310807100c1176020340d51010b0f51402074500c00d00c174601c0d0503829600204800c0c00000c1c001c0e80200e0b0801e000740605200ea01e9604007143c01c980c0c00e4081504d05030004010807141e071030107006254500d61031116480c0c03030210400100e6990143d82000e08103210348 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6719683 1250 6718433 6718441
    0x20a0f0f0509041b0602010e0f1209040507120905150601020303070c0222051303080105030d0203030c1e0703110c01090b0412111003050402090703110a27030503030a15030201020303010b03 83
    0x4030000609600410004d040006960744400f9001744003000181005e03002e890100d03a2801000305510f031072446144045807500a4441c108801050b006003c14103012600c12421542640d42c4206c001e424404c1c80107104034281041c0070070040d00000d00681c1154020000c0003119a4041e1907000d081d5070548001e600317402c1e1100321118a2060921000341146400d042003406040c1e90003551095000c0d4071070300e103182d0300c9505054843c5005191070b40964020408120180007042c02800e07904032440c00001c28036011155900c031540000000c0d000908501203078035540c4801d10003041d001000f428411110351804c110104180214410300040301d01c1e0750100c005014403002c0b104101c450040c152a08015151000b500410b81520141c1c041c0b043d890015402d0b41c0a4030802d140c010300111401c0c14416010390442c0d0b07e032451540010424400e203050040800594042d1002d07500c1040a55200d15101e007a0f001100c250b20701118002040d00030400160741c0100c1140d0548450001d120340d42d0365 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6720933 1250 6719683 6719693
    0x1f0306090c1709010203130b040204060b030405031305010503061c0503070209040f030e01020a030503040b040c0503060a06050112060308071b0f06120b03071a0a020a0606060507020a0f0f050904 85
    0xa90303010448040c10803a40045960740080441d921801c07680003402c80da19141605404c03400101d9130320306d03c46d410381460000300340341c440782e41d5105100a10110728240c860320b010b0507541061340c0c1212280d00101d02c14600b01c8451072410701800c400e10308541145800d000240850000004503854290040055070901500b403044422117a0013824004013801c040ca0314864503041e60350190006a800c0c0c1d105070445d84003040360b0007a0313505580d80300d085440e5519010b00c0000b02501c01c6800d0403c251000a55440c240669480340c00600700c00030303590340f03007074000340c600ba40c000b60007038220745407001c14000a0096010303030301c0032500400c0c1c41400301c1d610903d00d00076500541007000c09820921000dd0b40030b41c413171141c0a0072a0401418894a481d1005050341d80d0340d00e004e2070b0700e02e42050442c4a013034142200a032985101900c100e03004084582c0341c44086074125003040300010700000b61034042d4144154058000e203020004404c031103180ca211070a5074032044c02200d200b03419000220301441 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6722183 1250 6720933 6720941
    0xf09050c101106040804061803030914030a02040504081806030105031b01090902040305060a0b01031a100302070204090b060102070b040303080c0307030905010e070303090b090303040504020901020307050708100510051f03 97
    0xc1400c41103d0460401d810000e40030f402510030b0360002821aa85a0403034820702499201700c96050f11000e6440c2d0800c80c65804051161100307036050320400040300b01580e100d01415000324090720303000ba51601549403103080c0d03d41020031607000d82e808000410483c3c50025500380b0088907101915540598500122120b03040c55001c1c25002d0700101d4007106000010581c00e0003848440002c1080095040066054500b10241d00da641007190800c1d02c0c140c140308402801c021480d1a0040c0f0704082a400142101d8210f0415502a0200d034104030403940c040000d0320291a1680d0541d0405103190b50041607480014900107c680d4044003103204240a0342000041d01d82c050000d119040c4000c00c0c00d41d17034000b0761009400050083d200080c03502c032104111405254060051480c00303050109100107503110003501c81c114442006048003040d0140322940142611001400300601d6500c0c0c003805440d0042c20392681e1098140e002c0101da52000188221051110100c016041413030788142d0040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6723433 1250 6722183 6722207
    0x2130902060c100b0a030f0209060103110c06091203040b01060309020607120f0e0a050a05040207020a0902030c03010602010b010e01090501110a05030309030405011d01021905010603081206040f09050c10 89
    0x1038002c40e0b0038814400c0821008060b40d011101000600781c0c0c0403c014a0b0000c41c03001604540408010768054200103044e00da100310107050210f144403002c001c42d0603035808412940071580104040c40100041404201286034061048600f1800c158540c40007801c81841404141030355041d00384215110038041c1e9030141d070030049585d8100401440900048117043c5044000f5901e50344180e8640350214071041a0380d03003d0038060019090805000080d4800b0205076070018164500040001e600d00045100e11800d41a481d180c1d49030043c00b1742998145140c0d141031200c02ea01d0854940d070b1044e01042102c500b46040c400408011000f58101545d03250058054000001086072800b03000000384129a02030b0b0350488c882c42102c1d108140d64900214850050708400f0464002807003515400d50079070b008034000244281d890740c2d4580c55902c900d80b0a44004003402c00c0004500d0180324140411030182c4c810b00050300c40e40d0b9566280c1e46061030007889441913081918003648107012942c10307 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6724683 1250 6723433 6723439
    0x105060d061e0603050603060424020f0705071a040308031603090b040309050f06040f0e090f0607020604030e040b1005030a091e020a0602030c030405060f0c010207030c02030610030f02130902 84
    0x103108402141c020751038103409580f020038105800304840d400d0000c0c0280c031494020076130210320003540a101120070b0103001d000d084940c00340a41c41950703003404010102240b1403030060440c0c034608900032142125980d0b804c0010141030104101203543d030000c90303074000d1098118030b0034102c85074030170713001043d40c8000542182d4a1804000400d038020704400d054540403948042c3c0003402404024a03407145006e0900f052540ca00308101c0074030380545030b60300300c580034003074032809140c00c003880d46003030811a44440164002c005100515400400005920b42c080d10144181c185c0c0d4000f2a01c102c0014034903c04000c40000001c0190200754440c0f01169400101c1ea942030301013040d05100402d0703954003613121b2030700070000107002400001154135064100002d10f08091420342000b207980c20440450b0380500301007010758601d1000788000d1a90a2080c0c0b00e00f4400910750042c103143c0078006044200341c0d02e50350360600c086a05860920550340e0b04484480c1048198180030b8041c001d00d085c002c0d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6725933 1250 6724683 6724709
    0xf120903060e06010504050109090203032a0303070f0f0c0b071808010603080306030f010204030b010b0708040b040e040606050a0b0f030405010902030601030807060c030b06030f0702010e07080106030308010e0402090105060d06 99
    0x20b50050202d00d02e8121074040300c0620050341ca481980007100e1440038020341c0342d8404c0004141c80c1c0011003610b803138000b452010030b0100180c2128142075a000700d8801c0d0009100031215503070160004240b603180d03002454184580303100790780c0354007030b0580140c194000d100c5000300c12844079101010314406020302a00034090b15580e4a403003012500b060b50407900c00c0c0140840105145814400e881c00c42e5002401c86071282d1800081c2201c1e0ba1100000782c031500400c2001180c00c8031100c1c018001041200310400c0145050b06111003192110340109106114243c0d04000720b00014054812107c0f10f118900e86d691500d1030b141c1d00600804000075010b010f440b000105120003440500305e124003410060146c410040c1d8110100d40c942c0c00c41560241051011071060a85c003c00c083c1d012225000001b0040c0e071079007450745482d403641e0050705a0fa4480701d00380100356101c500c180c0100040d2030f610352141010341c001805811705002d65800707060003040308421172010fa0070100041240d500c07042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6727183 1250 6725933 6725951
    0x60209120304060302070c140a030215070209010e0402013f0b030a050106050114040b0a0c080d050c0405030d02030319020f0708130f1508040201030f060b030a0c0e030a0f12090306 79
    0x1d00070307410100f801d456000c503000d030008040301d205223501e00382c00300104a40b03000381c03e55003044a1507491100f1003044600500c007403801610b0f081e1440d40649000411a100c030718103840014007087d000e003061702504842c60341c4040100e400c100340301401007214014007545061043c40c04002d000d401c00b030aa0520850b0020001e2140c190300603015610284e035814020600b1319004100d500c240e1145840044007049982580c920514160440511030040d40e494990230f02e260500341d6000791100300440c2400a0200207a10f004c0256401054860000d1400d40c60702c250244042403c546243c454980c0015031155040c01400468403143d90001e94251580003402c0c1ca10550354060180e0b1740355214181d40400c0c41d0805404080c2c4c224640c5d81c85040700d90b00c6500440180411000c107480c0e46031600c0d404207000349a08061031068401c4500021544060a001801c507a8101c21103406a00680d56403808940c01c508082c0c070319a00100960890000a40100e8240c802c0e540f0150660349810b00e07075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6728433 1250 6727183 6727187
    0x2040509120d02120108070b0a03150308030a050a0b01030b0901030b091203070801080d0903081804020910030902030105010e0c071202031201080109020a050102010b010c06110702060a0908010507090b0706020912030406 96
    0x41c04413261060001c001c6a81c0f42c40c1d4240d5902a540511211300c0300c144080d102e458400d030090b018a520300c0e40c0032041e0541c0c076a2004580d030402d941e482c000356103c07000c002060502d4031071407070360120910341404814010400b08000d48010300014007030341c83c3c120014804880c100311450003181c0d205040b030347e80d10b00940700802400f801e0107100c0341c034018800049402071080c00d022050326040b2100a181c031000007101c204a0b4600a00303aa000b82c0c0030701682d003042c1e039188610802c04520707480c081015103441c41018210f403416000302600030800f03014170480072201310666010a901ca4070304295000c80c0042a451405502107011410000c5400450b000006410036140036200b0f651030394403a5240d500680c265403c540ba4035002070440f18044000c1a042c0d0813000b081558402c6484c5001e00d01e03004030fa040d6000030034580200702c1c0f0003c2004800024440c03950300c1403da2400400c0c6500789103100070300d0303c19200050038164001c1022043d03581c450502d80215114003048a03a40d9a586c0b0740 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6729683 1250 6728433 6728437
    0xe040308010602060c0901081306020406020307020411040f0303080703060816050108090706020c060a0e0a030b0412050f07082104060c020c041505090405190507180b030a02040509120d02 82
    0x41180062400000081c100d40000303245805400010f034a5070501d145407004452840000f01004240c1c01c00309115804265548010b0014003d50342c00703155074800500510080e10900d050b01c0121020801080103034050010343e00064a0341441c100c980380d20303400310840c050581604007041600907020242000e40302c600350743d004c40c0d000703882d0510542d64200d072607078458005100f0382e80036800000500146150140c003c00412242d82004c0301000c00d4034010440040881d00101e886d410b24400340400c2c000300564203c0d0300c592134941185804500308080c0003502072148010308561000c10300b048080039149441a045045d0050040e251406007070000c060090b80d00c0c10000b5024540d480715480c1028001c0e110314a4031941404101441d240a000d459003001f40295502d005000c140001812a43d02c141c1c08107004d413000345160303800d1202c1c1241c0c0078155000a0856490080400c0b416103020442c0a10250122000074080c0e0714071001d542044504482c001c440c010000e0038003005001540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6730933 1250 6729683 6729691
    0x10606030501050f01021b130e06160905060307020d0c020607060507080f09010603240b0607050102040f0501030504150507050903100e0d08010303021528050f0c09060904021e03010e 80
    0x82c2404c0c20700502001a03031140310380d00903086c1c0803250703000c141050705103143c03102c1040c02160b0000400c03041c14003440d03003848002e40e50303050410209400d03004203503803201d40d40e0b0240c201120150b180d07040c40900603595060340b20a01050010403541103007550780c3c810964a869422a00902040ca85907034010940201154000d14800291003c00c8082c83e0500c24181502c2d4012030340d01a041d5a0000304007000504c3c1c0c44140071359256003010489031520805000c0b04c9206070b0000d42c403507050101c1280940006d4001904041c540350400000c1245105c8002c2405081e14001507262900c441c1201c0612880300b420385c00d4450303540703811808083c8ad4400342e078240402c4242c804c0d000f458081107418400070b110150041e440340c407070043c2c0c13007010300c07000313030700800d00012044401a402c014041c0040e80b10b03199486040c0d07550104000305918006003540105000c0e00a45401c0051001500d5030080403401c6006640c085503103101048106030f128558035203028403a8803581e41d1b02d44940040700c115 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6732183 1250 6730933 6730939
    0x190305010803030c0a0513090612060c08070c110a030b0c0705070f06020319030603050607030608010b011404090209060f03131202060f0103030e1c061b02030c070302060304020105040801060603050105 88
    0x1d10301e90100c00c0c0c034041d400b4a6102464070401c18800c0b20690041450340d4a00b9071058000114000c803403041d4001031071101050340c0c0c0705c00541464011164800c2c0c031101441031100800180d9035021864bc00c10070740c0300c0160350300b49000c000420407072641e5800052040c500350092007200e0000074003034200d2900c01c0b000c40e03810350307100c000501e1071203001d11411016038000d02444440900411039504401ca103071400040c3c899490b1902840c2a1041e125034000c603076541801c0c840b05e103080c0551303240003d003801c00b482000980d13864480c0e00d00c624403500188a5000c07802102075502d0382c0c2151182500020002c0d22400c04242c0032006645400c01200d0714581040c45185560012500901c504070001035070754543e2841c3ca060741c94401900b0703a0f0f588045841c503540100a001089850450302690b000940c2d101c1a441c800446030300700401d84c0035517005110350303c84080300040741410b03254141c8101d0b40b80d4580e03100582d0f103400781b40c116800039408c24a01090042d81680981e040390030071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6733433 1250 6732183 6732191
    0x20f221508071707050603130b0103060504030905040903080a02030702010605030a14160b07020603060604030210030c02070803070b15040603020a060c0203070506070b06040504030e040626070602030d090501060b1903 95
    0x1d240103590b00300b0103c0400d03078030381058604101c1c5144c180003541d4800503014075910b03403000380e5550f0100d41d84241c2040307135199034903800d0000345548032282102410043c0d808102100076510301401c41900200a040802d40000000705128400c5d013088004040103402c03140c01c0c0d025450310300c103a08650810003c2c00c0c42040580950344900d980e9880803954010040740c0b424155800b4000103910050820303030060020800000141c4810720030724415000d81c0c0c0d00081049084100078242401c50341300c0750307031030344180411004981220301c141d400201007070380981800a1540414050141c6070f0002e135120b003154800054150704040d0082c009482102541c2210f030b140c1d82003207224010007401912031120340000810a0406901454015001c0d0412002c10f80f2854005800d5603d2a040062015004140705d402c82e00030381e00703100c1040c184201a005050411100a40d02d02615180001a0340c0b078411401c14001c0c00e50011010f000b540520780d5030740510b4018101d208800384a200c000900c0c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6734683 1250 6733433 6733439
    0xd0b0108101107030c0201020a0f0b090606010906021509010615090608070504120b0402030c041806060503030702060307140f040603020306090a090302030a050f0d060e06030d020307020f22150807 86
    0x520300c11a41100385410b5000d041040507141217a0030848488124103511824011902181e01514112080c51142c882040c0600d490112030781003490150544e0b05020310454103000e880c0e000b10f0440d007400d901e0006c00750300f80d0315950030a016250581c0034841e45901611525003030360b8084c0822042c0c0d150b5490341310300e0361203001c0100c0d03051040d0720864800311902c1010350002090006100d030001e000800306d8001d00381d8100003c0885249170205840c10b44510325000401c4400e02980b001410220041c504212480d00421080e210040410b420040c02c040203020443d91101501e041c0d003c0e4100f000d445584400010740250b02c15501207108003211800100e0301205405074020503581580518248851350105460b2504189034680c40c141c4203109041000d041481448001c1c00380440c2c1300a85d003042d800f8942015410003002046420821076280036841d0f4500444032880f080e22840441d0311030560800011383c1c114550344005003803c01d0000e20315840800c100980b18035106407002c46079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6735933 1250 6734683 6734713
    0x20d020a0203060c03040809091801060801021806030403020a05060a0510050d03020d11030705030c0706030b06030906150612040605160504140609010201090804090606030f0501061209050c0d0b0108 87
    0x38046000070340c50350100001400b1012200702658002d803003120000d00300b00840b0f00003041040202da5030803404803551418030f4025001d0240340d0007044104000c40c40e003008007501d402c005e42e4a100c42030055400101050405200f00080000150807005441d07040c00c3c00100c0401908c015a81810300c2e00410201082c20300d000c0c109404640d515070010800c00b02c1c0002c0a860300140d00100801d070b80001c0c407100380030501c280002e08401e0303101005061003504084001c6c04036030040280310b014103400d10030440d020781e000504079044126140078000b05039606000038030324454080d0040c1c03200d00d00024001002840e81250380074600003400900241c04a40d000c03a154011403182d002e09820b0024605035070304000d0014409064103200110702c54a054072840c600754000d92183d80d02c2540c9010422115903d4891200740c10075110040c05203500d0114000c1504421880a01015590785805c40820004024401183e44090042c20310008071303081c04980510b091040080c10b002d170601840c6114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6737183 1250 6735933 6735943
    0x7020d080903010c0f0e010305040c120312060902070f06020f13090203040201090e060a0303140c0a050f1b0105030402040b01030e01050c1c05040203070b0705010905100b100e03030315040b0604080d020d02 90
    0x11411b6a00c0107806200840118041d02004c1c0c415a0008203070640440c14090300d1041d0f840701d90003511105444010b403040202100d40583c05540b00c1c1d4414420100000c600c40840b041858000c503015888011701003014001d8412180c490744900d0034800002034940c0160091442036000b40c80781c0410664801d050369018a049a4941d4000480c3c1c005000003400343c0c8a50b44118015141d160030038119018051400d2040c410941ea55031004038501341c2e10008000840e1000000020080c0076441e27440040c0c1030b800094002482180c45090300c002a074401c0e4017201418285900070f004a0518a0349a01c107070748843d880c00d40d6161250300d450b40824140c0a03640c02694050001d04400e0f00c0c009441040350400c082c02c460f29500e524115001c540e0421401e10040d1101d803001071010041f404000c104103011200301e05000503414a00481c0c1d40100c2a2544012661400c50019201a0006000300003040d0380d2507002c41c011401080302d803400600c1000416040e000c035242090b880740e0030303643c0d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6738433 1250 6737183 6737207
    0x4050a050c0412050705060a081012050a030509030c03011401050a06080c0a0c0510090501150503060702060106051806030c03010504060e0f0c0d0207050f0c030706030e060a020a0507020d080903010c 87
    0x6a03500704020800660524443d5088901400545101c241c80320005107042d800000340100258641c414041e440022019442c001d00c900740c00011001080d0383c4550701c03691080c2000d418080c1c04114110320b80c40c09d0140301d45001e8010020040400c0301302e1805d2000070207000b400d01450804c000802c03000d000c1c104060285842c0029182082213001007200d4032048041c0450342800f89a00000b40c2c40010b0007100c0040348110004600c90300d0400c600080361400d40e100910a5010780300f0300c4292900807480d5815a407051419540c1e62011100000c48100417114003a00710200000300400103460002543c1038803400c60301441099901d005c00c1150344400d80b5154568102407000c251040d64000085c050f04080c0030015003000c2c0161506410720104000121258005000301400ba2030144882c00180586082c00c10172380f4984c00710380c5d945030001862405115800903030800d049000310145c0c2c1010f60300504488240c5041d14090806401581d0514001c0d03003400103030715120340510414590 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6739683 1250 6738433 6738451
    0x405060a0e07210812090705030114070509040e03040b07050f010b03010204050303121003080c010228020a030e12010501080708070501050a0f0e120102030c131409042306040f0204050a05 82
    0x20031610748844144003d074564101c0714450100a40d04440b52050100c901c60780c4400040d240141c602028582590b200d041140c15602501d01004500b6403c141038034a078041c02d41e00098408800c4002e60702e503201c0c0d50810340b8104001321703120080060000303525007407420250085c0001e002e00030034075080c1d000d540191989070308140f000c85140c861181030190701c00308a104501c0080d0b501d0312a0f6105500c0030802042da46d400007000a0400c2010310101034150150100d0101e155602600940f00ca042c8200101048104105058255540d00f1150000d1011b50b008200e41d503501c4140a588401903c562000c030f000d03685001900750300a009545c8852059121442441d1445100311082c03020190200d0f030021040d1106032500000748083c52007001450221503507190498800c1072410030b154000072002c01220300e5040340362503408030340303400991060200e0a11020b02403c0c000c0180180c0803c101403180300d080105000c5000d1800c480c542c000d4400b04071340d4940b0fa4800060710011140400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6740933 1250 6739683 6739709
    0xa050603010e0c0a090302040603060204030317010803090402180402191b0c060305060102010e070b040501090905160c26030103060c0302031005010518030111030105031504050d23030405060a0e07 86
    0x7140e120100013806080072074985146041d445c0d50028040703900641064480d5607020505204154114019001c200303c94004001a58581300c6195a0382c81004107143c040e54010400c0340080e0350424150b07404550090003035488803604513841d0384010038400220005111310984c4403604074010300b03c9490303941001c1000d040328102681074001d080090803090441d9610610f129121f07605009420241034020181c2e56500e190030001407034200103401400c0d601d40790a09124115264110140d0745040a080103103501003541020403c46044030940380c01c40300d4120015500c1041c4000543c1039034880d140400c0765240d6413101300e040340402c03112104410144c0c0e80034491580500068400c4004a044640080c0c1c02a00400c0c02e4410792611140e04880120041c4240c0c0707401e000c244803400f00d03202c0711075080c941900c4541c1e40320303d8103050105206c1803110400303054001040e81820741850000e0701e540d03401c04e8949a076a42d03408a81c4d01098602d80750810a600202090b03030421a42d490708044 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6742183 1250 6740933 6740941
    0x60c06010302091b0d0c0f11060f0408040806010602070501021b030d18080106180b01020d0504030303091502030906040203010501170d03020c16030f030201180b130501061a07020a050603010e 84
    0x40f1200101804242c0c0c40c1d40f0324a81200e100c07103042c0c01000f10801040b03010508100040b4098008003c0c0a050800d100c0340d404203000701440015890b901c4031101001c58019155070801d25203034841c0d42c101014078040d1a00104a15400040c0380c011980203034200e40711a40d10700b00c0081110448903c0780d6040d04120700400e0f010b482004030300c840549055009880d95610300086084405a41c002065010388400c890041c140703500c1a40383c040c2c820700280c2400040f06000614070300c60790200400307166aa075804003d00507a54483c001620825008550300d043c07801c1c00c0da9031032034102c5049119608107000401c102d01142c0c2d00c501010070f05002003030000742680c0e00f0360294106041949451141c005040143da0450042d0030045005507a8603100548906000b400d5a0480354441045464152280b00080148211990004009035003290241052800034050a03643e0700c040c1844030f20120251700f5481d20801080c003d0b10803074540408654401c24400c46001c248200741c0c004203100002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6743433 1250 6742183 6742189
    0x201050319050106020a03021005010303050405150408010501030c09150503120a0e04050f040c0f15050c0109050a0c0504140103210903120507060b040504051b03010612110a05060c06010302 83
    0x6590407040c00441c000404103118018400c80300240e21250042e0710060100052507010310601c00d6402c080401440310b9810740c3c4000c2c10314840c520680f030003001400255035800c082d60060710702802c1e42100134010740d607407400d0031002d40e5801e004080c0014507100158600b0329143c0130141c2100d0300500a82010200200f0350032003904180500c405104405c0000c00066550303109081c42102902080740c0c403800c060a00607000f02080d0030510311001c038007a061241882c0c41040450f041c0d80e03460440e60341c419508113940901545540140f061150043d144104082a040d1b00300f1341d041560204031b2030301000386000c60440700b8480980340040c20082c4c61007010352030404040c0a000342c01c048890b265250f450a0118611000403000100c0128600c420484503001e4034555a038115024402030501e5115580ca0f62040900d041d81c112000700e4884c6e440d01c0a41003540104068142602060081e0404120301d00c11422494410b50a0503000704080c0b5040044c0c511350320452004040d61380c00d6500f4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6744683 1250 6743433 6743437
    0x105062d040314010e01050709060206060d0212010c020703060c0e060301030206030405070302060403060506040b011409040f0e030a1706010212070b04060b04090305070c060906020a110a030c080f151003020105 92
    0xd5810031260410021020440c0141c0c44003140b10f412000080c0b150086100d03d00315032021705204104400794004101c2c04d0b50005844d6048002120841c0754005680300251f080003503010104125400c010303030020b501e0b80100e01403049a010303240901001000c40340031244c000c3c418028a034861390600c010310142c10508080c0d644140300b04103e91590341c0b41e07000900716401c55841150450b85070803c018103801e090081c01c001036400c0c2400320100248600f400c2e83c0707000b080700c0c9500659550030125140006904400341c09010707002034035079805600800503c1100345603480590600c0c003801080c0e40b940300141d040344210545484a08000c05903031010307100360010300191107440c0c42c0e4034441c1c01540c90780701d460a001d01c20703191907644402030314104280c07441030350044041c01158201080020b801140800c4a1a88024502c45044806002071648800c0360809000d4404250740428045000980c0040f00f0014a04071480c2440b103a100d1603d0380001c40d9015810070402070204019401400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6745933 1250 6744683 6744757
    0x9020604030203030c1006090513061509060602030705060c090a030f030306080d0306090c030b060d0c03060b030a05010e01080106050609041a04050a020306040b010203030f0f0402150a0512010506 86
    0x40c0ca000e9898000a1640d0402c4180d00c1c400d4200b46c0c6007803017801c500c0c4601401060a00014440c500d000b503400a114a52100c0241c0442d8450b0621450f072594010032070f0140160720420860f003922401e00a44d6034201017000c440034131412020410816081c030669107040310003000d80c44942e00715540c00b0501070341c0720811011b06882d0280070414010501a0340c180303007095034000908600c2c0000300d4099410310780021051628000e81036840d6201e0508840b0100703001c02c00400c3e448840d11b401c4005000301d620a44603154003005006c0d22072150703040181258624204c04002e079803210f000a0880d4124800c0da41d101c1d10411960b1480e04058100a1400300700c0548400c10382004408942940c2040300d0f03800822b0f90000800440745854454481100c4081c4010b50551400718012648800c8c00360500d030707a05d92034400140455441c03c0c1c2d9402860f0380076291a0319901c0310700018095170481400111304031f00001c0080b8413400e000082d0380d24412141c882e0705149124814808034285000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6747183 1250 6745933 6745939
    0x601030212030c120a1d030604020105090307030206161406010f031203110703020f0106090606080105090c04080307050a02040506180406050603010617060a06090605130c051213030206011509090902 87
    0x4820f805003002d040c000364030030100c0e125900e55582442c010040420801c080c0081e0031504d584035841154a0003e15654401d50a003000c5960341614400203140201d154402175100c1000101e15283c0c103400c070250032107280314034040360100f0111008a1340380e0b8024041c08900f541520000c101148040c000b255000040d81000a450444030702c6802c0c00764001304064000d80c2c00a00303010701000e0244140001050030724802c02840e400c0c080000d2100d24103110355442464000301003403030790000c0400c4030020201042100d40c0d420300c515189864842900d02a44036500e0300001030071500b0b144500c0703005402d008840180710350782c0380e07241001880e025103241e815660750030700420188621841d003488103142100a0041e031410360b9a0350192189500910901820110100500c3d00c885110790800c05200402151840c2141411640750140c112400110150304051002c00166217890600d4680039030f003581c549070789602030401d440000340346080004030280303020000340c01c140e8001a01e1310320007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6748433 1250 6747183 6747187
    0x30e0402070b01060804030801080303060f0105070c0b0a0c05010507050f1204110a080106031b06050a0507050a0b0103060e010507141801020304080102030703020306030601151707050903010603030815040905060103021203 97
    0x342d1240380a45000760090004516000d0501c410f054000002034010034801d402180f5520703058000c200b8290880c88000d0500c000481c5500030810070100002c0600900c60000e602c0c1c00e00b42900074a0040e550f2025038065107003078046070129201d00111071304186545d01c940e282408a0b1060107101000810a03160702003480f070000d80507034031194208000e0402d0000822003a045007230407120b040c2c01216001d40301c64150000c003c00b80e003150944080704441e040264950354241081400d00c0c2c10b210b001021805020008800c111440e4045003504061100030441560303440390580300c0452a2050174041c200a005c44001b0111000e00424824010b00c152410256a103c0322400d9030000c0e40c0100c04240c000c0308000d0380b070504110071070041c100048240500400048050659240200051000d50503e4000754115000e40125161824040c0081040c19501d0400400c0201c2c20b903080554486401650b506514090103130611054110003d0300391039203940c0c20007401c3e956004411105000c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6749683 1250 6748433 6748447
    0x9080301060e0f100f030e0c0310052502030d0501080105060f040b0301060801180203060702070e0106050a030e0a030c02091302060d0207110a030c05010206280911030316061401030b04030e0402 85
    0x842c080140e042003e038540c004c0300444180058140c40c84c03103246a1f165423200706c624140d66000590908014440f4000140540300e8141000c05080842000c0990f507031042c0d010b1682980c000024000301704104000c02ca2270340ca80d400903081e40d805440b040d921004550402d400341c42c180d40286401c0c88014000603415039104203580c00c1d501a011528040c3c014800360134250300313080c0542039110750b1910140c12900c0c04c00c0d03070060401006000b0441009004034524006a000380d2050010f00c0e140c01c11601c0409451400401960701030004900600300c2802140048010b400022026640106041d0400856003c0000290003109040c1c404400100d009030b0541c550720200d402950140d0305481340c517820304001a00c0c2c00f50150408008100319600079079480c041c4c140315941178500c6c18000c0340c036001900740340e20012002400c05606000c000750401824040000c440000c5119000a01182100d425580d5004109200140c5038101580014000a115200c17801c09003c00510060400c90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6750933 1250 6749683 6749689
    0x40e0f0a06021305040203060105030703051b0705010e01060605030705070803060301140c030a0b010c020105222303010b0301020403050d1b051204031109060319030507080d090c080109080301060e0f 87
    0x103100010790316103900140600d00081040c070014041c00c8191415441e40c1444030000305030707100080610081541c4c94000c42e00b0b20356500440300c0d120300ba11074000e0b1541e0311800d00d02e0007030031445444001c40d8a80400061070b68041d4050307a01c56001516041e0070000c05031540040c7d50300040c0050381c10755a4403031021855010083c00c9010b804554000d070b40340d2800003045022a42c40201e20707418003420009404c0140c1c0e104003103503203681d6000114040c0c030303a0182a0f10250183c0c1c0e0040311051610414010200440e072050541c0d1601c114000d003d6a44e00c04c1c01e1600303e104900000e00907402c01846480b6842c081c600d190035240c802c903541c00710500161541070800c10100301e180c8500b84001020018001140381e0b10160800841d44450141461000280e840c40103011025801080d0a000c505150045013a00d80850304034855a075942c07040d0b1400401041c04410843da80c044890000c00d407410144566015980d02401c02c52542c3d00304802520382240e280b600d50361010900f43e03034618a403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6752183 1250 6750933 6750943
    0x3060b03010602070e07080f040f03110105090309030106050901030b040305090307031704030201080c030f270105040507080d0f0207140409120c03080a02070506150406080f0303010e01060906050306040e0f 90
    0x201d42c59000e4801142011005420800e001c1c00c200104040c0c41c3c2405a1aa0380c5214550401da1098102c2608200d91034280e981c910b42180a540315440c060170001c2c0b10310040010035590304200c0080203c3d0340ca42e4108070318540d0a00004d803601e00048009000240900300030940b40d000182119506607881d669260728400301d541c8040e03403a5010a0420455030810021608484001d45150541c60140d007071000804000b0280c104865085180b2000d9800d030200d034180d10079a4400034801c0f0715141c02d141d41d40320800e2013000c07054401c90a01010803441600301212800040d4043c0c840103140408a000c9448107088059019030b4510020001443c01c9078141d05510003521000f044455038200605880001001c150340c0e94010405000018004217400303030b01808010404030f5414030304002c0380c0140300c1750b0000c424600c5143d9400e20f81c210004040d40c100e80e0039544032482a0b803694011211949188108008a0340c10b2010070b64031724058200000c02c10b40d51040791302800d440c41c3e8980c0340c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6753433 1250 6752183 6752189
    0x9080904020a0e060f070308010f0302010c0609060f150f0504151505040e090616020115050103020d020d020703020714013e0327030606030705240301030303020a030b0406060203040b0a03060b0301 86
    0x1000000075030004048d000b0345242e0040c100c000d8445802c504d540c0000c2d0080c40545801007034142c0e5440000c4c2007111a5210016181030010100540e0f84543e242006c41c0440f40a071002d45148030100007128030707142c0103c1c94040380190401d12024907010b078961000058801042c28402c06000100b411001068a0340c410a1228020b15090401d00c04e40d4001c0c204d030f00440400c69041455900c80c05140030700c590100d44080c80c0060342e600d90348080b1802801250710111219000003041e005165000803604103440c06a08071001d00200500190350801d40c0507110080d0008001c5401e021108040d501c41102641c007520104141070000304a007181d000786044081401030703440305c1180801461000048550070781c01420a410320030300090340d4400c40e03c41c0e00e2090050740303614200700c000c0f4400388407446007a84407540c80b942c4a00c1c3c00f4001c0c1d0080f04e1558000780c50417010780c410380341c1340c0500e104940321138001e50718081c10820454425800a5980b80c18181caa8800080c0004014020340c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6754683 1250 6753433 6753457
    0xa0e01090308010302011e02030f0901020307050a030e03060f01080c06030402041503060e0f01060806010b031b0708030601030b100c060209010c051203040201020115060509060a0e1e03010605030109080904020a0e06 94
    0x10b030740c1036200140144a04a00f0321910b400a40121021240c0001c02c4405108410001c651515000c3c40100c0c80c1d403250b190f00400d1030040007400401c164005112003945401103041e2456550b0389801e91501c10000d10400900340d011905500c6541801d800664000c1e00150007c103000c10300c2130b1300f00300b820705507441115041e56600004100000900c0f02e0b275100c0542500034400076180c40b40c0716039142d4060050748414100040030805081c00108801d110120340b0060540751001e50403c00a250000c40b1030744c2c0440d00302002035440b0320b0004850a10600c840d06d580f00884010b403900b40082d00103a1009060141000031080415000c0002000d2060031000082d680c0c40d03d80300081c2921045080001410100d11040c40318541020568808400c1503a55039240c200c0d4940468604401d0b00b540c80d00280514070726a00c101c4040c0c0c107003003454406c1c1c00a12032147e4400c01c2c107089520499000d0010041400030702164542500285016002c2d403070700f0540a80d0381d10004401c1e40c02188503500c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6755933 1250 6754683 6754697
    0x9050402031f0602240c09090a0c0207120302061302120102040f0302030f07051005030603010207060f050601030b01090605120c040503070803070501050f010513020706240501030b060406090e0a0e010903 89
    0x4110010348109501601c0307a4405000950650300c5100441c10003840d08640c40345c5c684000518013000a010354044840c014071901c0141071070a030090080240070340110040c002d04101203451041d03500150f5450364103600400541e0307101841702081c8015998126444a02da54264010b504240058806045240341840b02c191441c41058a842c5040c0c03801c40c0c82c2d40059804000940d50000c2c0c10344000071a04081d41d40b507840d600060f00900c01c07654004c0810340b034680246400b6081e80d001034072980081e01e04102c8100c1035401512121482e129160000382c082013624660190011400c2d0001c407141d100c941469140c0300080d04104003a0807089041c0c0c004207554091140034014550442200c0058424a506090120b001c004c1443c0c030311038002c0d07000110300082046540c8080c600205e0151200868009851812240c8500f40309590001e8100040e0f20f64900d003040440e01159081d4448814591a1001d00c544d42d4400a00d4081c4190351002506a000001c0c040c1d00320051095403aa2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6757183 1250 6755933 6755971
    0xb030106180b0a031e03050c060f0402090a1401050409020402070503300609010302041a0409080a020106080105060604050f0d0501020a030204030b0121060510050a03060c02011103130807030905040203 88
    0x804464040400603c90000740004001107401c20248203c86111805003a005010380c1c2020b5a00348034044c448129807046801301b0100d8010034030342d45d0042e803085911580302e441e40814074040d907900300c01c03e0084181031001003055140680c0601003581c4060409802c00602e40c40342800c41d0050fa202000360388641107404104205502000d5003100c100791100e083c1d08000740030a0008005000081c01543d582040050391064884000791300d00006000380004001460190002e8204440c400059070800f0808145244180586446030b00060241400c09203050300704044c1264580a10350807098203800d03000490384c02e0000f08500400354402680d40c0c1e01e545822800b4040580c0f000c08200081c0492051180c50a045084c1c02c940007c030118040d10745540c04d94510a0a5000c15803108c100140001040340c10b2b0070041e000340c505d4000b080051500d46412070140b001721891402100e4818034500065001c00180c042c81d0b00a2804104107a03c0c1e102050403a80103540351000c840c400307651a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6758433 1250 6757183 6757229
    0x30a060603050c0108010b0f04090f0905010f0c020c010309020f060a03020f040b040503120301030302060708040c08030703020c031b210705060a050c0106080d09030602030a0207050105040309080d020604020619030b030106 97
    0xaa401803060642c00e503e8021004080c101c0d49c002e0307001d03038810039855254000344054950007640f03407207030071000070811100e03410918002040700e5800440076001e000c0180c02a58080d128094040d60050030301e803c052101010000641d001510300810305500740b1510096000b01c401410140000281499580b81408205031404045a20a01a03e0020001800041d03404240940c0041c0745040260080d103440c505401c41800942144c070480c0302c00b0510206240d80046c0103110190250305844d01504020824605601115000e942229a09951003103c40310700d8402c416502e281d0094a03032480d01c07280042c01c00da21150385038002882c003140800d00310700b0a05c00c03c4018a002401040303035400110010300703074580f01d110143c12294007000143c00e004543c1c044860703141d8000000c0140385814540604070704054010240b032032141e11b80c8912180d000080080c0240d800400c1281005070203814808802000240d1004140d01c5d0a0f038001c0641b402d00404000d0154000200340d90703881c2c1040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6759683 1250 6758433 6758447
    0x160302060604020a0e0906030715050403020405010806010b0f0a03020408010c120c08010513020a05090a03030305010e09060105010e06090102010e070b0301060e030105150103020307020a202107060e030a060603050c01 95
    0x51248241d20400c11075500b20b40060b0404040070007520101000e03074507d00013a003040070300e511600c020340c02e500a0021081d442170052040c0c070300c212010405641c0f2814101c0d507030102406004000c0c0c00400c0600c0740c0407285009008005140d24015160a840325000c0d4213455546000c4404685480c2508190060a0241600403441403904040a61500d0b00040c0345a417860041c0b1125070340041c1700e02883c3c0c0701c2c0c0308580a050000c1d005100c010b55034a0f00900034002440f03030498030200350002c6580028085443e40c100c030b00580d41c880703484198104200c8954060341045066640e1404580c60103103052100314000d10a00020644075890458040c03d50b0044c0201c45210364075100c10083c00c41002c01200c0c0c00c0403c207203001a280d90721480d00380e1800c04100000b41041c68100542216549010812002c0b4542510075902940c00c081c5500c00b5400c600110105a4100500520449101c0c0d141c070910310130000d04880003c8601e86440045402d01d80043e00c03181c006096051181d40c01c100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6760933 1250 6759683 6759691
    0xa0803150d0f060b0f01080601090b030a1103090604050d0503040503090f0a21030315030203030316020c0a0803070c120b0402040507020c060703050304020909070e070e01020106030204020a020d03060603110d051b16030206 97
    0x2021f070b0f485d10700200024041ca2003030082d00c40c174035804008503015005941c030486c1d9104010b009a5564108100482e0713a13544111070850343c602c503406c041b480e1984140d041e42d00482e4003c0042d400c080001c0100304a00c03103100d10b65a0852981c0380700052240034980c600782c4401328107024000bc1260703800c004013a02c9400004149184940f0313002c000503140001245d40c04044400514104c08010a0884c00c00c80004e2490754040201080803403c5a008401030140301c0c80340140e2002c1e030341e807191001607080b0705100290070040200c00042c05814107400c500d40c80200c2d40305403071480203808000390301604105e034143c2c0040c50100411086052a0342856040301c0c0d200c0c010b084442c64070624a03441d0400808220405c2030a01d0180d245900035000302e0040c550050080d5282c406200d030095590706900d2141c00041d04000e00024941d00900c0703840d481c02c0207c0d584514004403980c1031005008058030385041d2446052030b845500f050180a0303c01c008080c490309507003071344600f0700919080c4c01070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6762183 1250 6760933 6760937
    0x121401050a0302060304080d110c010509010c050301090c0c1b080c0a12031d0d0f1101080601050f07030c15020406140c060609041103060103050313080a0803150d0f060b0f01 76
    0x5120325a01e1403410421a6030468110343e596865241664060255146549256007416100701850640740d024004611b0a00001c0146e90b6803c000142070700e007015100300100b04100010b01c02200540c000181c0f0b031505d41424100c81203981c0d24a500b00384803c0e500d2030b610280c240d0a0000240c14000d400220300120b440008190402e4a07030205554a01401000d010700740d01e107000c00304c4a14031522481000101054130089580c28a11129803407180c048484001100d4202010741c0900d040d14016030701079440a040607888a58803222b9400001c4c26402c3c008a14a00c00005100c2d51103000700e04800c450144e01d031881c12001900060914010394203070081442000c4800d070001500e1039000300100c1d03020380c2a4031076040c045d400c400282006901406054000f2062110000080c140240720506400b0b00c650350390303085030b02c862011100a10183c001c01c00b081a40c40a07c0e44544250b02c02003000940201c40c0e542c840700b003402c101c0e040b11500c2d03c501210b591340c03802020700c5003019800c1c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6763433 1250 6762183 6762221
    0x20d0b03010209031203060a030b0403020a0b0603010903020c120309150a020705010c110f04140405010510150c0b1b0a020c0a09021206040504080d0903020703022103030c0901180612 80
    0x300c0c000ba84440350300c14117040b00b810110006500d50f80c0c0c0036014006580005140380c6504007418001d498020411050301c1d40d18206d8042581401c05105000115400d903002d0301c5059084001c01120840b035041004040c4814081d0f08415900c40b50310300180303101100e040b5071310b1041c0e10340a4140582d0b90321460510000b000c1745000301d0803140e180304200d20b01b1111840c039410040005802440700a801641d0341140c44c04020403c441540710a000300d01d90313646003080c0c565400810918560b42d402c408000b5406488440005031569281600b041140300c40a40048900000c070360942c1040c81d03080016480121014100d0526101480140ca20750b5400c0d460b200000d0125180f03c0c9001d4980740c021559080000e041c0900c01c415a8502240c800050040a156060007507403070140380000c0e8070031200d8902684080314610100501d0b02e0300c2101540c110f65070700d41026040c2e08142c0440b41400b950761200c03040351500c0c4901c0350245c055503c809000300002c0f0030540407507480081304140400c070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6764683 1250 6763433 6763447
    0x50714011b0203070c09021213060f0203010303050d0e0d120906090b070206010303080105091506130302090c0d0e030c06011203020304260607030902010503130309030204020d0608060903040e0403050306031f020d0b030102 97
    0x11442195510449c80d203811180e082d40c0c0d10b020b0000300200d07504004181e2001c0004010598018004e042c0308c0e41800b020f128108041c2040c50301d9010034400e071004148010388240035000c407a0000c2c4081801120001034140d003c1d1944050b0300400c075800c0005800510062003010340001c00c007405842e0030380300c82107a8a40100e90100e540d04000003144510f1000c11021100c40b02c04001c05c01860303010305480818200507001251f1500a110380040840c00d04cdc0d14041d25090000c240c80b07294070758000406559103046c50f0300e03400c100842016400c50008100100c1d11500700445000107000c102d190440074007545944d54288100a40140c6c01c05040c45000000b41c0ea1102c2681d81000124102c0d06000d40240b40a884e85217032507000a4026001080d02c004815155024404840c20001503c00540d40d40c1802c54903403059018942c00165058003040102c0d10400c0999440341c0060b0450b02d1f0b003400401080700c0800702402c62510300da00001c0085188c080760140342c1046000f54020360070058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6765933 1250 6764683 6764707
    0x60709060903030804230304050f0306041e05150403050a0905030d021c03090501060905010509100b030112031202030f0103020f0402070302070b16020d06021201120201050714011b0203070c0902 85
    0x1e072001804112026000c130b41070001110041241c841040c81c0f050680c2e481740a81500ca400a00c215441215004032996950401040c00c41c40350394807400a10032407a0311407210704004130510007901d0f14071a445408000404210085000300d0098890301e4403a10141c0c402000742205e50031960003074003c581c903190440d07000a07800c01c03807082d41d0a03070700700f611801613044006003106038000e4919820020b000a90010541c0200e050710306c1640d48003096a40c5001d90140000d552099440c1544108010070410302c0b248040259148a0b00e041760103d210300d81e01d02c040ea04240c0310890f4500d42d1100400442c58011118600c002081d913055007804481e0710060340382c051500c69285070301d03400203c5001d4484040000206954014100c800054287c01d010000b500910719842e03000003084004200700824080200d101c660503540c451504a03550745090000300c000f1841c034055900e815401ca480180c1c005088089066507000b50740b42c400c00e0401c00150900743e40b00c580054410060700300020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6767183 1250 6765933 6765947
    0x130803070804050c1908010b06130e04060b0904060509100506060a031802040c120c0309021e04060b040b0c06060f18040f0503040902030601030e06010e07270603020c06070906 77
    0xd14504000d810307a551401c1c11401c4c2038a100200345e0100740c076820340301081c1010b107005c400e9902c0400208004030941d4207100c0284900e00040901d1481c0960803c01c10b02d001090b00c0e44144981d9020030030f0880040440c100030010349085441d1500c600030001ca200c01040340c4040500c4a48041c003140c10044085035003841f070684070300d04040e101c00000d44d88c44140d50500a0072a406070007000200f0701d07080010814070190114100707060410310300e018254441e0040700d030007036002005540000700103038080044842404603503400503224400080c0344807514000e40010415003402590320f0105000c05810b25000500643c0b0540060a10080544417202240e02c3c80b109291244919162424590f4000c40b0540c0c00401c0b030b200c00100440d071410250003840c02210284c8045c8004c10120507840d444003424040d200c00300d9606000501c400b0b00c2003400f198100c40014440c00841c8001c2c080344d514400b203412040200e070700001d84d24804001000000c0d0300c000c840c600000c0b601e0409000401c14 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6768433 1250 6767183 6767191
    0xf010504020a12020d080703200303010303120c030e070902090a050d05070e090307120f080601020a030f03021602040515011103040f050f0103020c0114010e07050a21020708030a05040b130803 84
    0x3d451815900011911140044038070035030088200d0b516034500e0b00d00103080d42c400b81541c02c0d4030b41c1c1074008820340703010000c240e905890781500c9501c2c0081d200c800304801454200340321020161202c00b2010750800510040024001190000d0f80c0d03003000405110301c64141c0e50249018510b20b00002c0040780004c544e40d030035100019921103d0303464a801c160300d540140c280190005411160344d03003110340c0054404901c2401ca8998400301c0e590503005988803201100c018010030700c00c1d0300b01444140709a0043c05414848110f200103581150040b5044407000c0380c0c203201c0c60f40c203000040d0b855178001c407000c2c5d03e0051490082d481c0904080d040100d101d030343d1013418041c5140c909960441e81c003a40545c0c05400301d690081100141007400701c400c00d042840f4800188030340201069031244140e044600d55004d584441104402030ba80c842a42c078025443c02441e240e00b03001c8500001c05800095008003042c02c004100c508050820302000d500c007920101505c1c15110203800054014000d80c0e40c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6769683 1250 6768433 6768449
    0x2040b0406051804020a05011d0108040212010906060e0a02070503040303030f02040e04060203070f0e0a0e100305060f070f030b010e0d02040e060a1406040501050603010308030c04080706050c0f010504020a 90
    0x190220910104014141070740115521141400715240020909208244150b008036a040d50b41a500c10055a41d00074410034014014401c83c0411400d500410300070750880c1c80a080d2041100401c4031190031980c0900c3d080796003948804041003044414518942c001c180d0a2003103280220307941d0351030b87e81d200303d1000078145501c80b0032011902d002c650541d002003041d55420105847c0c00c0c680306000303510490b0110041049084d511400ca40314542203d58240f000e0021014241041507021a0040040c000e040031410020044000341050100700d00070034080c040c7d2003d505060724064915a988001e4400300b5107003c40c2003015070f0340007483c40e12816040c1c0e1302e41e076080801d00214020b4905901031010911941c824081c8424060f40443d0340c000d407803201c1d902191103210030041030746d00c03e1081c594003450500c0148080f40d801c05c001e6810000b04003d640c50035903101e55490420f0302640c070890100b40d0218140d04039101c20310114000e142c91b1700007080185065070014000701d140740142c02d8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6770933 1250 6769683 6769691
    0x609140705120a090807060506010f03060b1602030f0d0215010605030903040b090103150609050f030a02031011040f0612060806090a03030b0406080304030b0a0b0603070c060221070207030b01050d0f0204 89
    0x84a0f1510303031100a250744c10a680959518840c101080501000d480e60350004175118000c4040314400d11801c81a40da02422075450016a810303403652128401b00d040e42d242c022110f1441150100f0014800000b8003500504480c02445082c1c0d001030505900007014800c003001000240540070041303e090b204280300707507a224a522001280140b603204040400849809000715586412040e580115001101c60b08510505034041c140c991588880c000e4155003e0100c4684420007908425110f44031042e00c00d052560b1a500c480800050703034820350100d8a055485d9502c2d0100b0700030300b00034201d1440103285e942040c982c0503542d01c64121014040607520700700d0140503929900324070000c044a100300c0352520340b82d040480c41c03100e0030364442010600d8807024500c0e030704020050341d10030b140307940303075410040b50a0b20f9a201960215525140700800d01913021182c4160f00310392809024170ba80208002c5095190140b48000b041e0800b51003210a03020718400102c10b101600310490707042d40d001c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6772183 1250 6770933 6770941
    0x3070605130f0302011407020705030a11040905030a030e06220228060306080c04051b0304060603140309090f0105060702061804020c0a061103040305070609020109080102030703060914070512 84
    0x319152002000c02044100c12100300b10a1640c1500140302a2864400c45565606c490205a03a640154031030141c15400a40b920000720b001051030170040c0707001402c00716a060743c5580f228150b520051001020030341d503502e038110004c0200081c0da0300c9442c6401500341c002900031804002c2c0c4202c0e900a20510001451b8a03c034001030b99140b4a41e10300700300304d0903d01e48910010300038080e00e0160071031911a40e450610645844c0c01524061405400c9142e60420501101c6407179a000803c01d58503d80c44480010016248070201031035050a04d001d940c50340080e000308622480b002d400340f540e030b0001c03000500180da9410210ba10069040317a910b542c0360152400910880340240c5099409880460703504110f04010030301e0101544140c0c410003000e5020042210307140402d6601400060341440860700040003507201152403070050602c1c0104076a120005820399004582e040300194441100300510412401201e122140010060f4403c0c83c20360001080c46c0900c0e41c88856203405003001c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6773433 1250 6772183 6772201
    0x5090904080d090605070e011b0305040e0403020a020307090b01080a060602070b070f06050708060114130308090d020904060b030d03020403080304111f03021b01050402180703020f07050703022103070605 89
    0x1102220f031320400504c894030b00880080c2100c03010346003207030109141c00303074484841020901d4200c5050345621603d0800c0d05020540d038240b50010f1085080d4401d080e021400742c0c1c2c003005a8401804040c20104001c0300d00390005103070407005060304070168180f5a0030b200b0941c011a400080d20303180c0c14181c0d1100c071103080c04000c410600e000506214540801e1142d0240c1c00400f01740b2684003071b21889003d4100140125051150310004071485555000520000b0703455002003003102001080d801241d8903c1e00001ca1003d0b003a0b604850603652882e1201150034240040c40d01510305050441c1010302e1611018098440104003e00300102c000d8000c4603035a650880440c0700d0500c0100c1c410410040801070003c0d880b60300c00d181011011101c070701200005000b400d1040d54003900c840b80340d600c0d2460107960700c000600500306150b000c0c450000c0c3c0946140c090000c80b40240001c01201e4a10b0040c48110014800360560f01c1100700f40c40100300400000f180ca8199108030000b81c1e6548003018 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6774683 1250 6773433 6773441
    0x306060f020a0618060e0303040b07170105010c0c0b03090606040b0a030506060f150c01020d060f0810090302071509140301050606030f0603030708030705071b180b06040504090b010608010605090904080d 89
    0x2008010343d203082406ea41041002010b58490307403052400703a11545a65000399041000001946a080b80c010700500295204503180619144110006180b003070b201e00c80f60040d038004a078610510740c0210108000c0b850980034151b1441c00607a103420388541580c0751035444000042c2014000d40a074600882240c40d0192145d09440c50030f407106440e403040642280c042c1d400610304454050a20030081a02815195490300710782c1120000c28150103074050b00130103000c0000090307041d4000c6a0000418001880d03803c000c0c603074241d0350421010708007011149921000d0400c240240c1c900006c02c00c2680b1480c0c2207a070030000c080e51604050350ba1302d000034034502c5000002800007030044103210b40c940e040301c0504426407160b01c403c288500061540c40c8034030071921801011140301c0030f000c402001d00d0f60044111281c0a40042e14094644020805884601000300c45190035200108119907100074554090180d51500030700d03182181e80042c2103280007074800b804212000890320f070322414540c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6775933 1250 6774683 6774731
    0x8070b03061302041d100605030a180606080d020f030a02060402130605030a0b040b06010e03030910200604030f03050408040612020912061605030408070b1008060c09010306060f020a06 81
    0x40c042d5903c3d6118448071403074501d00a0304405c0e884404001c0348501d40b03d00313a0b0200351105a039600382183d658803a40c2001d0030602410142c0702c1002078040010982c54000d07980908401d00061a400030802c10092900c0752682840c2020340040c0702c2d40c3c50459000c280305800680464020301c60509502040780100441c0d88002d906220301e4403074a0422010401e103502c00d0303026259a000540d150001580c0d80c2c103d5800d03250340364004211007001da107403c00d1885c0400a01c0d14241c00c0002c00346c4a91000402e038012014a10b5101078104010103038010901440d8058072704d018066400c1c44d940f1108140181e005d41e4042c042c0c1122401c035002c4e82541690340c00c0c4030040800c1244008501d2040e128001503c00103401100701c0e071160101070040007180d00403548601c4e11443d0000e1034407401454540682404680d000a000c0001d000e9001c110307041c02080340f1004650f0304c183c070030009011601c4581c400400d0100003a0034082c0d20380c000c14001000f60f04a10040740080c4110003880701c0680d212 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6777183 1250 6775933 6775969
    0x1050409050f0106110d02060601030f0212010308070605090a1e11030109060c020c03031206040203060d0f030908010506010806032e02070f0b0105060403050d110102070f030206060112050108070b0306 88
    0x1a08010400c2e00c1c61800504841c6203840b00000b4080c41c0d000d640d00c401900040e03001603800240881c84c1795103c1c5d805200780c86000d480c0182410741c00004103a0f00031082c0c2c010f8400601c085843e00900c0400c0c0705050f001030b400b20042c01011050340d00c40b02040d0750005002c491503041d07448401031002a2400c940c000c0307c0107008010804092510a0080c0354012102c030040c4a81d0b950040c09040003c21030f4004800e0780303244201540c0740c0781044003943c0001c0140f81c004801e02e2107031700090140f0400862140c400e4407600c09903400c0c42555401c4030301c024159410851110140f2050317031004524118076945480107821003d80d0303003804507610281000420f43c0b4902c000b4404007440101c0d046070740380303500c502401c048990740e034403c1041ca40114000905282c000308004000305010302c984c0020402c070030b0005414100c090f1030340c2d0f0b002c640006e000c1d00960080307000c10449690281c02540d15202969040002d5410003440c556603410320b0007a030100c0358000004c950161b5405511800c0c4110039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6778433 1250 6777183 6777191
    0x7030c0305030703090e060a09020705010209040204060503090f030a08060d0501060302030303100906050306042a050904110f030d081b040803030108070513020a020c010305040f1709100504050d0b0601050409 91
    0x40e1400e10703900d610881d01513000816040c004218403040340151402041d0003024400030302d0a00300154029480543c045400399401c00144000e61524006080103101d41d860b074544a1404c00002c80c109003800003021440d0300100000d1600b150010740301a0016029a00804840e03103e1804600500352030304007a505100110420500914101c185016100300c84403d111250ba50405e0550704c0e40140c0300108064840740c1c9401c403d00d4460305100301d0b17500c400841c045181d6500c1c0490450201600c054070442912440254039041030340ca0414010360503401480150110440240000c40103025002c0c50040360000514a081140603103000d0045401940d90320359407003202d5a6600c81510900f4080d1050903109000c0c44194425030300b00a259801600326450b84100440050100070b1003141c580180b44880c030702241070380c18004103d15540c0c0900c2e07514801c0d01d04005106000c0075075134082060400c014040384d101c80180002495001c2c2d95401c25450303004c0140c0c0c40c1d0090360807514210b0302d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6779683 1250 6778433 6778439
    0x403030e1009050607020705090c0307050a090902030c0403020418170c010902091005040c020304030b04030810031e0302190507030206031e0a0501030c0b040e070c060f09030810050604080d1107030c 87
    0x121303800b0b028a516408544126958100307010303121a04481a00c1944d000f0b00010782c94a01840046c003c040a515028003200d03107518400e4200e0b0800c1d28140b542c044040340c02c1c01142060f01c101824030906000c41c11a80c8040e0b80c0e845103c00c03030300a05096905010550034924802500030a074540e078010403000c4d03646030031610150b04646900c6224802e41c10081c9402c003990002c0211010b076600710440308480d0341ca546055441c4030020340b1420105481c10800000300700c0000c0010303001518072a840243c151981402803401700316000b43e80c64031480c10348440c0010380000f0100f007160742c10340e14261070390b0760354544155035a0380c0351620143c0c3e5800410020b00102a60050b81a04d00c5014105503c039190340541089006a015070103c002d010401301c0c40c01c81c000e00181007001d10440010480c58441c94020b4280d6031020b000b1408102c2d65414020042c0c030140000c005424180c8010381414a0001300e61f0341c9040c492100814010810318410604800303000750409117801c0014402910741d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6780933 1250 6779683 6779693
    0x90807090509060a050402010c0305180607120e190302040f0f11070b01080a02060301060c02190605040e060301020705031e0705070b0703020c090603070611010f05180706020d02060403030e1009 85
    0x402c441c0c80350715004035000900800311900c00c5501440d010307075a050a00410360b5042d116584115441400c04500c3c0982030a2540c231500100b0039180b1030078408032041c070812009000080c1e0349200500c511b4001c000840221880203144080302c1d0110340104410303410050807002803034802040c02040d0300785032240000180541c01445254840e03080c00c890350380c0e2218066242c1c00441c0000390310140410040103602d1040f81c40007401400101080e1301c003000c0750240c0805002503400795001c1600450104200b1018156070f5600c01e00c241d00952800700b41c1d07030301c0e1ba449107d1202e9400301c3c2c080450382000c1028912050b5510158000c0495a505031200f080d10499004002d00b20010f10802d0a08490b81c10410710300380c000d000141c0101003441c200081625690500d00c41e40525668540fa00c45400c1d620b03004041c041ca40004004c1300100d01c900c402802c0c4521900100c081d0340c00032800440b0319034001041c80e031058252400048080c0d2004c0810300b04030207504076680980c208101101402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6782183 1250 6780933 6780941
    0x40504110a090f030f06020901030b041b030b15030c0c0a050712110f10030e0c0316050102060f04120c0c0504020316080108190b040f0c0305060402010305010603020c06070c020109080709 82
    0x200c0380e0b40340c8002d01580c1d52594446800240401411341100b0382c540c000141d121303001380c0a00d1205050106109820364007040c126102c011601c204801441080c4401c00e0b010702c100740c105001511034449203a0308036000f100702d1001400041201c00001b4500302d42c400e05000e4508840e5010056a080c0e82e0348100f1010741003c0706006681c0c0d04a5004200021b291004039001d0101018029960403c2607042c00e6008088107400c00f01c10340246403900b07155690070300050000c100017095488560742420002440c004004002803081341ca20b030b0600020403070304c58594503540401c4c03a1842492416103070460b60301c40d40764409504a070000c41401140d14011200780d1180000d691662010382c0c1c0e41c0d80c119900d0819a10524107001650104408242c0070700b809944540982e101d804400c48607580e00350700c0e808580c429035258105d4000e100456a040c0642c600402d010320b025810200c11100d469181d9001800c40f00a00584400200859002e013443c14000d082c610705865a140c0d44030b02c090058 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6783433 1250 6782183 6782197
    0x414070302040806220b0709120506010806090c090103060c050403080a080a1104050a03020405041112030307030f020301050f010f0207030b070309030909091121010203190f060302090604020f04050411 88
    0x103000d444c0c0007500800b100e40007001945165a1420a403d2003900d903d002401e01a1100c0d08102c0040340200305402d45950039984a88610f0040c000ca626004402d030510306d02600140d0030390041201a155070b40c80024031815070b60004070029443c649000241d0721407240da8002840c03c0310101c0d03c0c0101e030b03421800840c8641c0c010181440a0440201a200644103038080d403a4403440c1c6500c20710241c01c081d40443d9101d880b900e180318034040c031000020404010040b030103205a00002c100545650302d4000c0811000d07103140103500b10350406002030901c2110b000c03284e04001c5240c6448030f07124802c0202c40700031034215178800190b00309000000d000d480000741c150041401560002800c00d207902c074070402a60030051700b494130041a001c219841c0041d000843d50043c00fa0000c5031031000a00c0294012280d100000f907200c4026215001a42c12030080d140d8014600282000940c680d0420340e036209000304e50043e40c8050701902200540071301c4d00240c0c1c02501e4030b0702c0b05220030131440040c00f0b1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6784683 1250 6783433 6783449
    0x4120b0402010f0c080409020c190c05100507020a050d05011404050610050102150105060703110609010203040c050306040b0a0b06040f0b04030201021c0507020d02060403060c0804060b0301020c1902041407030204 93
    0x81841c00f075005903030302070340450700802500c41000100140340c084c1d800340941d207540000307580c0c0780400c640580d0038409084901f9030790010f07090010000d5242c031070400b001007100c034140b45007003854036000600200003901c02c480c01800b039001000101b1030294400f800105542840602e0360801d41091a500c102c11100c81661400994012696600008413405c1c42c158a41090301c0301d81c201000e0102c65001203134100c060103115184442c51f00010f002180c0318034500000161246024184180214800d5010302d0082e0801c505100c08248149170f1503a00504c0c03040041100d12010000c249140720b9a40003241d07581c0410f001140c2070341c80d08020000c99000b603007103401c0c048585221070040369400f241c44010a800300080d0005050003000d078640c940c0000e10850a10b50749450315000e46941c0c0c0182c1000072000007c000820a02e4411280c0035042034008509000602541c160b866007203004812070308404103000d40c00c40d6125004200790860891405109040c06400074010390003038056819 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6785933 1250 6784683 6784697
    0x402220305070503030903191a0405060a05010b120a0b060903010906020912010c0804030e011809020318030405031b06040302031c030f11040504020703120c020a03120b150a020304120b040201 84
    0x40c113440e0000c20784c1c1c1d5410004003d4461024800d201c003900b55041c040490b540b0304058085010701000e85102441103000e500a072199182c0080d0031b8048038416044200c601c0b40a10030402e02c00700f4404c0842e408011b2000004201e07910fa800282940078100da49645903091003a5041005101c2d000380001c640305031000c241501c40440c2542c2079600c04140f0a0000307005400040c042031180180201d005018106090b000d00b00060700c3c483c608154115541361500041030040700312078038546940350020880074605080c14400002d80365800800100032580200ca5060340d00d43d80d28003180d0086034024210b0b11a10400d44c0c0c81444d55051082240c00f0900d000e00340c68840003140112002074030b00509840c505810582000000d4220140940030858640e82d1100841e0040c030440c001c0d00c40d00c5d001481d88e50f40c50f15004181d0340c00340034410032a9040c00c141117050b407200c41c1c8070841000c411111a40365840f02c0000c034030314000d542c0240402d002d02600703141030107180b242d40d500a034000c0e07039200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6787183 1250 6785933 6785939
    0x31b05031e01200304150209040606030626030405010e0105040f03060c1205010b030105010c050c031b040c0504050901120201051603080a060603090f08090102160b031005010f020a0b0402040222030507 88
    0x81c0f05000c1d0802c90440d030504100240000d5604d1803220b00703034210050014100958203012070215903d903000346012036524030301800465402240180c196529000940d5118806402c0c04d840e401113210303250600c0112108144242e00480c25140a0820020741c58045a580e04000015000e056080380204207102d4081c032030b40c0c00c0340c003400b0306a404c80c2d0841880c60f480c010044410180404080e034950040e14004080c0d69070502c17821040c806003035400c80c00c40c42070208000c111564001488180b01081004006d0b5445001c0c4450440c2e50034401c64100403401c1c00180c81717510529100c1c11001c40050703c000101500412524042d513400401041641d48a8800780c044a0100c131003c0d09a000e4100e8100020303028200501100c44180b054130318449850946e0415141c81e074004400e190804000c11040c0103050502c44024a001d10345100742101d5040c0107920b0310402c00b4060540460440005c0541d01c40d40c04980200360440410207a03000380a0300d0104a1000e0b000488290040e05000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6788433 1250 6787183 6787211
    0x9050102030406020a030f0c05190308070f0c020d03020304030804060c05101e05091006080102090414010e0a020304060209120a0201020106050307061d030703021002060114030d09031b05031e01 85
    0x1a070160f5a068004100d50345694506890b42c00a49048100b00714000d0b072594005402440071b0504403102444101c10074a0619024002e460300608002c01c1120256444d15801d40c441061040386405440f0300c202440e2a080803400c0d80701301e403c00340803080c00150008400703a00c80c001500f0140218141c0c1c0500380200c9110003038a1440c0484102c1e200444001d02595041d64003042c0c100b07021388221100021000484416540ba59100c6135843c4d601103036039001800d044c09503403108007411101003130560518240d40a020b0000d060303411f400d580400020700300a2141e0441c5c040c2d41b00202080c0041c2d034812851551202508400ca0055090031800112414006241005e480072500c03107510441703d41a1142440044600b01c03949449500c20010160711400c1c0340d414141c1c1130354050850b41d8107080c4000700118900c00c1c070034000e522031030380345820907403041250065a5100444c0075640358a100d14040c140070542000e90300d40550f00b031603102000000c1c40c80503122000d230028850182c0302040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6789683 1250 6788433 6788437
    0x360a050d122009011e020c040b03060402150307030207050106120210030621020411070b10060906050a0e030109020a0e0703060503010b130c02070902031005010909021303060b03030f03160905010203 87
    0x240200c2c140c0d801601c1d09214080400381054000601d0004140a80b0104c0c0d18074170410028900c0158009400395012402d06010785000c440381a0b000382118101035002c1031401d0400744402040c2c580200108452512070b40440c0e0300c10350801c0003030010a8440c85203100e03400500000f20720401035490315040c1709010b4010f10b000c0b148950481d62003a41e24196505036562081400ca900507070340c4550b0b404204e494800b500710180240b42c48001c1e4540f45040c1c0c00880ea044d001003050252415040100b07540c40422030b104000b0910384540380d481004040790240c00801d00095100140500c00700d03004150050704e604c280810341d4240002d9035104141801c90b1060700d4038075046680501114602ea040e50400240c0071817070b00c100e41043d036a8882803412a08241c890850600c02502c04004d15a0f0181c140c3c00581020781c0700310b00e04941142d542c140307001c4c1440002c045a88a800ca002c65076810310560715006907014000340c0e43e107010752030544022400240440440c0c0c83d400d01244135480042 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6790933 1250 6789683 6789701
    0x15060809060906040809010504030b0c0301031103060c0a0315091802040501050a030b0f1e0117072c0403050910020105010503060f06090403110c0d03050a0305010e360a050d12 77
    0x4080c1080d81c640d40c51740e5500350f1040d4003260510804200c00800100320a4000d440380c2c1c0c520207225100e506615007595000356041e41584a40e0006040c00785800008044a0b00003072141000220051980008507046009078403e01070302e498190703140f2640c0401180d00d1861403003110108516030b200c004026140d4000c0c00701400303050031500010340c000c1894030840c0e0070000d0010400c910040d409640c912152090300000110355008600300d0807102c04000d0280070303000640318903200c0d403840c0c0a44030f220310305882c902d520b201400b40484c0a15004000f1111a41d034007070949d00c0260490b610290280c1020700c40c9900a1280c040040c8980041c9170324a40034000051401310340d0740b00e5840c121030315200d0b0390004496010f0031055014540e01c01e001184020b100b51035094a5050641020301102c00582c882c8400e0000b46042003d4410001e008102104c030f40740c0350821039102c90884030100d061003e40100d2600c0303559030103410f0180008255040759015541e18100310300c0f4007108816110b0b004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6792183 1250 6790933 6790951
    0x203010b04050402071b03230105010e040f1a0a15080a020105070b0a0605061b0c03010c020d0c051002040902040f080f0a0b0601051c06061d090a0203191506080906 72
    0x1000a10082c42c00d5001403600d24011600b14903421440e40301c444008240758400c07110101080f100681031054074aa0f650b0348c00c000d4008100d15850100c4800d10007500910041c502020000500d00300079110360300285290030f49400490038904041c0681c014100c0c0c81500710304031a0202d000401c40400208200c00e140d0694444d41410942d86e0b842c602000080e0103807080701d8441e03101040c0ca40342d003000703010020958030007041c102c954181600d0070719403642c0748940070380d0514580c1c2d4035003031b0001940250483c25107410901d800c8175041143c00e2803403182c88514087c1c000580001c2c0b004013034014006841c00382c501e0440250b03807070303881039a0303082602000301e8960405c1d40720340e0100b001d00140303a0f031000c01030511611307003140c14071200d6031400b50814084443d96030766401c2c44501c2d848a0002c0d00c40c60061454a013026041c0700084032a44014224461241c0000000382c4a070180d152003403131081903110900485c802d04081c15803100d41405224001007000001801c00100007903d540079030484 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6793433 1250 6792183 6792187
    0x908010207170304020a03050a0b1602060405060415020c03030406020903160f0504020703050405030a03080405010b010e090f090c03030d02030618010b03150609060409090c0608010602030a031a060d050a050108010203010b 97
    0x10141000e4a0b400044c4281d81c401065007001000c1041804001c4155204072410341c45d27031605d821000e102150b03d03024082190b100300c0400c80040c0000481907007141d0451109003000c2d000c0703d06500031740b00714280314240d4003000c03003407104003d0540c0103002154800c13030545a1440c1002010f080c0c00626104400c90344a25030400c01c4241001c0d801050114043d1612928040d124000b091418042c0c0d00e0840014808004000a01030b0a03c80c0741c4e0009000d00e04001c05d044500300043c0c00e00e601801c0445549516404168014010031014001178005402d603a1a00580c2482c20000d4104407001d501507004020500511400410000d06980300703512030505640f07840062a40c2c44111801c120340100d0100022005030343c60300301800003801030f0400826404003c1c0780070402458180e116605201d500c074018015982c011043e280c1d01d280e0b82c5800191041069903c4203e0a6046649604403c0000d0750302c08151590300041d11607880a10705001d5a40c5e140c40441c201c1c03000348a41c070a0780200b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6794683 1250 6793433 6793463
    0x100b06030103030f0306031217060907020a030302090d05061006080705031012060902121e0102070209041419060525020d03020f0d051008060a02090102060114120601080105070908010207 82
    0x5800c04c0c03150f11219280002d03400d0b03265a2aaa11040701a9000d07001c40d00f48803694801010400e24243e0040007038070f040d905030800e2403010395a40c4582000606050b0081001001c81e01c1e0030481d44c0c1e0003a0801c04603000e130700701000c440048403004c7c02840d00007103402c000261040e020f003080328000c0c170401c0c0b80d6105c91850401198181103196a00701d8180d80c0700c1c0080030151f82e80b1a000341e0004122070191441280710442104111030120300c1010a0740113000b15005a0f85600c02c01d030b40070f43c203c0560108a0070b50750a10341850702d441c40000f000c4e003070003d00c4001d105c0c0c264420b0388190941c0a41b8000400c0b19800c074080da54803004404d0040c1d002a07180a412071280e005002460b042d204d403a820a00c60101c014152441207840d00801a110101000f14403402c00601b5040024120110302c0c09000c180001e4884005000b01840c00024091100b41c6485400c2c1c41d5a44040000944a655840300d1002d4041c000654003100015140100807408540610031a007200b0351041c190701c100c8075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6795933 1250 6794683 6794687
    0x80a2601030807061d0d020309040e06010b030f09030409020a050405010f110703030e03010b1206040b281107020d030305040212030a1b0204020c0303040602030103031b020108060409050313031103100b0603010303 93
    0x3400c003080001c0c1101c021703801c105643c200011000d0070070a0300556152180d9000b40300c1100e8182042c01401c0d4406001045004003800840b80c00401841e80e10000355510000c15140d4425503128a0303801d4400102240c1c0d655118000d4030640d02c00340d0b200d140240001008442c800d5404042ca40107030400b40b410000a8024880c0c42100c0402070300105070000f0745000600c2424501000e114560070502c100020020001049580060440100c81c07240408540c200000c0c0740003c55044e10694841400b4451054007040d102581d60040c1008440340240c81c1c020042c00040c1c0e0201c2c049c000718103845003988008410303640c407114a0703a18400c1c80d014224035440d503a0020081031360015420070044100b51401c2c00194801c90103000c002d6569407662030014991032142084003410000100b803800184e038804900390300070400300d401240004039404c05e6821845061500c2682040d280340010400500710030782d00c0c1040040341550845840d411403081035522000c0c40f10f43c0820100010700000e8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6797183 1250 6795933 6795941
    0x306040c020f0304030615060309030203040b07021306120303050601080618041109040c0f050102011103070309060f020a0c03020c04020c2808120a0e0706050307050f07080a260103080706 82
    0x8035544102c1d0035082260350654110340c4650400c0d52900d80303a00380c044003644214a000018480c0d441c0402c41345415440082d128000c81c0501400028000303645400c0d07541382c41048030a00401034023004081d0ba0313143e000280c4032500381e044021038140400180598007940449104403806050310181403105038100d100214000c00072034406441000c0e1800035221880c0c00c62013544140c6c0c9030400725061182e00c1c3c851401035401241107a0400310b0030303540c5541c004107480d01700805040c041268107403480c040010701800e50011044520100303102810035440000d2020b410b0090b001e49544010400034801a8844e00401401583c010800c0030400300e0030b603d00b5140d00e04050076620002e4920380d2015466408001280e00444000c001d01c07904401c144900ca0000b500140100541d620b0001c01401e1070000030192824004081030300350300744c10910116000719a001c2e0026a0311541042c000d0844c1713079009406000c0c0c4640524101001c442c10303112078142e0760080e44032070401c125a40d4210180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6798433 1250 6797183 6797201
    0x1c0c230c010906020307020703020109080703170a020a02040c030b01030c0302040f03020f010c060903030903120905070e06150c03040e09070b04180609050403020c01020d0f090302100903050307060209031002030705030604 97
    0x25969078011070080f0741c82c1e00c082c60180e001e503806802d00e0b920b1400010403500d000c0d00007680940141200300b000505506941003d144040e900580302c0055650590529028600280d00181840c0c00c0041a69050f032141e82400803d0301d082200700345006085040380075600032011000300201c014000b51403c8031071002406030501d41015080142d6485034280e4500010072000b080e12080c5010806402c041e030340c032150f10144010042010242c859a0350b40c240351081d800844001008100d240e00c0b48810106000590511306989030307900c1c00c116983e0344c06842806051034076440420249500861600101d0ba09411040c2c1000c2c02d0a804a80c007099040b03078541100e691701000a1801d00602903a44214003a4028007030031092030002a003002d0684400f042041541c0b40b0486607a9081032801040e680c05a0300c5000c40c0769440004e480d034520541021302244004034900702044401d400800f036007030b019010f49900f00320f44403490003030f80410799149c0049001840045c503a410160700003085 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6799683 1250 6798433 6798457
    0xc0f060405061201030b010509160806030304050d150c020a08070602030c13031103010b040501060207030b06060403050f060a0b01050304030813050c0402040611010b0a0b0403020d03020c04021c0c23 87
    0x5856901c900003000780e0b0081c1c04a40c06403142c0d00c010000c0c00b10540c082801404150b903550b40381d240c5010320019115410752200c040c09503450101e800c2d41c900b002620040e100c040d20700086099507040c82c0f40d9903a00c8026403c1d8540c1804000303c0f000c1e2001c41c0c0350244a0b400a0604d04040c0783d941d586020b90001010300b0f6542c1401e125030aa00440070300300c60021802140c0c01102c2061000516007540c1c07200c03003107500542c10b02004100c50303a8009580030032a500404442441d0701d816000a04503c9154805001442101d20104c1c5886001c180c0d54007407a098070b01000030400718001541c940c04116030150118103280d0000d2035014003420b4400300d05100703105403400e600700c5000040407a0010b0f041100010002c02610740110707000d20440414a804035040144c0700d00d03000a40c9100d11070303030000134050001c1e10f03110310425000b04428140720070010300564841907110b081070403490104e10b001c5005810090b01c000410301914007044102c0e040040d10346603407a00098840680e0001c0f442c921 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6800933 1250 6799683 6799687
    0xb01230d060b040b090609071103090a080601060206010801060e1801090506091006050409110d02060c01060b030a0f0b0108070f020703020603010b0711030715080703060e0f0a050108010605030c0f06 87
    0x8240d6800c032080025038410840041e03041c50700700c2480211030a01503140e000c1c0350700c3c100340040d950765482c0540c4d0099840c03601c8040702040340f88442c19401052946504401d80740c02c041203007500800c03e541a65200d508441d0309a03030340d83e020741c01e8581714410101954100700114240581c080300c41c0c285d01d03e901d80003142d60081c1d070b030310b0601e000400c40300e5012a400c05e481a031841480740c01a10300421044070244075641191321118201c0d4003102015101c1c0d803035880c02c1e608540b65107064510035070000e8000c010300c69468031141c15581c0700b1142c0355009407800c0b0070f8200044407480340c01000d01041c2d684e02c0c1103540da01d50645030340180c0a040410743c807440307100200607a58100154040c0c9400c0e103e85840d001c0c2803804c0e0016106203911031f44203411429062242c03030307e460b070b484001071100d18200500e0f440c2c145042c1e0042105030024042d540c00340f006c0000401d260031003140100e0209070108482c0ea61562118221421401341135403641000b247c06d0902d2414402400010130006c00440c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6802183 1250 6800933 6800999
    0x1050903030a080105030105090f0c04020d090b0103030507020f06161205040801020c0102070519080f0f09040509010b10110d0305041b0807090509030a050306061615060509060d0b01 80
    0x92554020084400000d40e00f14018401414280103242d0840005001408a20b548918450b160b103c001059806154041441c03004048c00d84c104401e210b82005c2c1d0302d4801e58690a000b011a88285000d80c081c41d11045a459a801c1ca001115074420028002d840105001c0d501c4080b010300000210003007182c10701001c100e01a080c401405013800e10000181d4456441ca403003800c10040381101e4113038080811400001c603030352038120b0f2003041c044c4122607641c400c0820030480318054040d21070b0300305207840200f00c52501d055105981c0d0302c1c0c00700e40d81d01d100710440c0001c4480102a6180100907000174403c40b660900a030001600144544800300700c4c46420b035844405d00d41242d001185641c4218020403d80400348a0a030300001c0300c801842c030303021082c18064040c0c0300150409019210002d0603a502d48a1141040c8907180c0c13240e00c8a0b010f9013200740e5000648128000e080c0b04482e4100465001d151460f0340d1400b065206640b2480c0f60310f00f200c2041d411900e0305e864000c48417030700080c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6803433 1250 6802183 6802189
    0x60309010f02030a061802040602120f0c0706030c080901060501050412020301090b07021501060e0904170702090403050c010c030e0604030f0207030b0405010906060504020705070b0307090f030c030303050708040305040e06010509 100
    0x9144100b404501c006255850b01b005110f260036440e042d04001c5204110030301c00540c1c0407480d5210344030b00c2007496544042400003d800c51140d4010081d05002c2d4900120784d0a130701d0740042c0c94814495a4081d0981c0740c1010b042c0c01c80302c035072007154080760302040f0401103a038070308001e240143d00003000011000070369150004000000c560001c01038200d83e002e01c81d089501d41400c1d0240c100b03072a101c50900100c0d0003240c4540c07000740010300b9100c400c445201c50711145904491100e030b400b03004041345003001d14001d0156040280200078a5080c5004042c60600c2441034410312400c02000302075a803031755101903511800c0783c06200110b000781c40c1c1c04000b00d01c83c0780250707004e0b40c0b103100001100541c5046c200c080700d0450308000d01c260300420100012840c0041c16800f41e030b140b00051541ca4072411010b49030403000b6809503e5a0803103c6001050000500300700c02103038020b89003848076642d1800300f2503100c0b80031640280450320501007489140300508840764008018180545002e00c04400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6804683 1250 6803433 6803437
    0xd0204030b06210604031404030501020c0a05010605060a020604060e010b120c010912050d080907050a06020f010c02030f03130602090916030e0f10050907171014040b06060309010f02 80
    0x252580081c140c188021030070156502c881500c440405940035004102c0340e603850b075102500150400c40300400f01d6038000546400c8138001c43d80100219994510a20801d4688103161030661311941303400800100c9007400011103480d0000d6074050b1405603903076a039038030047c802032000f66159075a540307014581d600d58032440c840451880b002403034840c0f8070600040500700710382c101420b03a40741c28081c400080d0000941d001031041508244589955a20301d05142c2017699218640c01541004002913854000c1800303551420703400001d00c00300b0b5010307000fa1b03901d100364204600348020400c0011084402e0b5090450301a21405016240501050005080090a4910f010349031114a5800181501481200c0301c8400e07000152050780030381a02c0549800c1c0c241d00001000c0e454400080e90a8401d00244026001011418113040c2803110656a00c8202d50121100342e40b406400200000c09522242d1041d54000d10038409960b590302071044507003001d49406100d641720b40b0b0002c1790841c2400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6805933 1250 6804683 6804689
    0x20d0216030c1104090c1401110d0e03060108070509010501050a020f0102040b0301050306090604020108070e01090503031303050f1f09020112061403010c0c081602031006060806010914010f0806060d0204 89
    0x142e008032030007030b038200154594556004a40301ea4a40003503040000c04841da40c00480310700c2400100e64131420001030b910103420f004918050300400c15215030351034100300c0c0a04000310540442d0300e60303a00d41c00010764408190055640c850303100001040550700c02d100501c80803211f4810350b014100c041c00c40c1400c6ea081500410b04007000030006121a00f0104881c1e075102032100010107850800d0b40018140c0207019043c8010041c0040340d524859002e80203040c02440c0c060100c0c0d64a90703c451551017104400c1c08111190b02565000840c0310300c0001e000202212041040350b40c43d104440f02c07070010b016040c0201e05000c213041e4a00d44440d281d00c1010300400c01d000d071003602032400d101003500b12182140c580e030034031016008400c0400d000c142981e01503498858000c02c45442d600000c1e103016108030f100013001c2e040a0010031125800026036026460a032143c4240d10307160b02514492007480500c503070004260703201114007141702d01e0200b41c005001074186441e080401c1148010790340a50 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6807183 1250 6805933 6805937
    0x709021215010302030f070503180a0602030709080a03021c030e010203071107090c080109090606030f0f020108060f0303120a020c010903180f0503030304060509010b100e0a0b03090c0103020d021603 87
    0x802a0302852240d05200e4030704246011072561a04e1804d50f5001c0e400685904108500032002480c110034514094403c2030000003201c0308054145864000380d07200716500d5001035124000020f0040d030020340c4440e85035158001c0c013070b8102d034a041d50182280140c075000406403100f0611045500a00c000c42c01484aa602c07840d00f404080c0e8807900d01211944020104d03403504041c80d540035840a080390544039200300100c4c03d070042d810310801030f0015801c080c0c400000b10b10104100711900161408452003a00c2d2840266200c10411039202c6480340500d4254100308080032002d00841003440c1d005a800f1b40040c10002042402400c4074603012046012580d10f80340e0b0207402801416003402014240a000304190821010a0310ba00020784024459500c0b60049000d000080d0071001d520138010302401030401d00c80000921230b10282110714001e84048002080e2140b48404503445a241240186038841200380110002e505c142903540c01603600740f280700300611501c541c1c00702d403070700907 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6808433 1250 6807183 6807217
    0x30402180c09010306063e030a0504031505061c0302070308040f03060b04051302090702070308030a0b09070e030309010c0c030204020408030306091806060d030513060503011401030203010503120c070902 89
    0x414005130031034009070012401d000040c00018401c102600d86020b80c1a00d40056141c8071410017044052040882588011800003148a05026511030b000c2c1049a02038860b0203002c0250f103400300101c41003580c036940c10840c444a04107540c0740c207452040d0301c3d61082c81190400c99486d00c40e03c05503000381c2c018044515144404105000c910b0003070304032101c0d089800b04010f0400f0884a64002c19015000f40229048000160064000e204d400001e50300104510f0b83ca1030602060801000300f00c0c0340320300ca0421080494a030510a40c01082c510a020f801145002034160042d2030a01c04840101d4102828000100040e1143d001800040ca00301000316101d040000801151410041c8a1805219108080000b43c800003404035003000c41a00c42c0006814079007003c4405100d00d41001d089050521b000080050f0311800031070403104da00c2052003404104d88011010707484203108940e03043d404040305a1a1101000003000110170700030846124a664858030800d07030300902c0c2585c50348071030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6809683 1250 6808433 6808447
    0x6070207080606060307180801020a0c0c120f0206030c0c16090513030206010b090402251119051507020a03050616030504031b080405150304021201150605030402180c 73
    0x400911001d0300745200502864030302400801c00c6800300030456010810700e0701c0c50a86001e62205c840c005046034070700a40d900c400e144005032407c0d2000c1c2d82212819918400000e000c9010b506d030444441d4000510802c011040c1c080041d20340000c0c25030a00e525040003601600c0d40e0400400c0940b103000701c13003050441c0c0350140c00300468400404049a0090a83d1034100080e40481c50301d0542c0c8085120507211402c0d036010030000e01480005c000038500704d40d881d4904a040d00d0000c0c201500c01d01421041107034410501030a803034400e4526000d80d402510034000c6140c0035010040b8820306141e818100036654000804012040d8030a0360a82c00000074401078500741400ca003007600c0e16003424005401c0c41e6500a001031a5404614158144a40c03540304005040044800901004002d500c2c241c0f5102900c507440d030301c1a50101e1003a89800504220560306019515105c036140c0c0c45412142c2c80c03d00260380c0c0c0d90008004a03031002c00c1480d400c0798146a80000e0380101a100355054907040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6810933 1250 6809683 6809687
    0x30e0703140c03030708121003020a0303020a0c06020d020a0b0912030f01060906080408030106030b030f01020f0c06010504060308160804050409060608060901090507050f041b03090203150106020d05090607050d020607 95
    0x10845500350182d08100170001c003045403c011940320004004140c01561380ea000c5c482c03a948a0b90300700a44c8100c00003000014158002410021140a01030300c0b0680750b42c0700030503a40c44980403510005600196102008644008889540010608241c8800c0038600807100c405900032203200e0300c03002980005100d481c1d03004842e100a0285070074926998103154031828011b010512801041548560704400261000e100c040d00080f200002552154007803000491030342c121030340c2c1e20603520403200001020f00e814010041141e4020100c03900d000410580d0090000c14000d060f59412402c000025a03a181d500c0348607441130061000041b1705050203001400e00c0c4c0040e0181003d6810019000045100030a1440031140211504c0b07680241d0031010401030316800070b41d0700034113441e44c00650401e81c042d001054928400c0b029143c5901440c18001440e00083c050000113030301c03688052450382e00440c01059030010041025007030003081c0d610309207002d500141c07160068002c44c0c14826250b07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6812183 1250 6810933 6810943
    0x135010c0f0302032a1c0606020d0903020901030b0601020307050708060105130504021008070e06030108010504021f0e060304030306080a03020c040e0102040302030c0609010c05240703020301060c02040c030e070314 94
    0x100301403074190700d0b60820a0140c1c40c3e200200034541d40a00c00d400d2824083d1703811a080380c07000103003614507060308182c2d15000001008075228002c00b50003542504066203105000020640754001d011800341e90031a220000c021070000d02c0c880c190b110801c8240003143d0200700b03240081603031070020415507044c9000e202800301a0021454060b04003000d01005a64049603c10000030510300340308a42c2d240c15040380c2080e258001030350030482c00800469552419041144182c0c0203949940044424003800b84810401c03101c101e00241500d004060185040c0b030045401034024038010860319180c80086003403106184044025a11207200e020280c101400b0381000114440002c5050502c3c540110741c5441d603c2c100280300703072340c005444401d50b80035039500980300341c001044803602d03078020360414015922501c900003c00e00c15000980c4262180c0203c0b8140c070031540e01c285488045a00b8000a05a01d090320018540c03540c50500c4885000c009030401140200b0848584544032030306c2038100b13 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6813433 1250 6812183 6812207
    0x5090109020720031005040219030c0f060e03061501050706050c030a0509030a020c010c0c090606050a020606030a0c0e0604091e0218040c050105070f02040603060c0201050901050405060135010c 85
    0x481034103900c0107084d500400e1104c150481c0050214007944e6510010342e038805070600301c00a102022001105002c800304401096840010002d611551558003d0f1350350013022404651507401140020340032041c41c4000c1e035010f6418103200d4101001036482c1e4040e648100c401202719407000c000c0140740b80d1140120364010000d80091840c0c015007040003500ca6196002d0380d03050200190010b000c00c40340c202e408000385a48001000801d0b11030b4001040e0394043c000d41001486841c0200d01e1174030f00400c016045aa00420340c0050600d004420700340c2e28802000d01b94456515280c00d0041980407103140080000d0001c0300c0303074110141c4104090301102c10345142250050300108030008031905401020340d407003400c18507154240f525011a40c0d4148000094000b410309000004100301a000b001e00e2042d41c1c0c0080c04a035490f0000c0303508071001118043c10720b60040c001080a000b001d50846104510352281c800542da003030001420401140040000341d80d55a00340d80903540e44120383e003070340d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6814683 1250 6813433 6813473
    0x2210a0b061908070902090f030a03020307021e030c0907020307050109110a06020303010b03060f031002040305030901030b0301020a080105040c020c03150106030c02030f0a1d0d060501030507050a080a0602090a050901090207 98
    0x1080e05100740584d542020307001c2d00ca06160f002034150665580c034000c21a520600500300c039003007161480c00075266040443c04078080c0d080f041510729008251425001c030300c0310140040500904040030081c2080b40500082c1c01d501007004aa130102c1c1c000e0007440c0340c40303004180c84c0001c40b1020702800001c1c8010762010086400600045c0081c10314501201e0b0803110884003d0b1100c00d801c0000382c100018208400005880005c00101b080301c08400b6041d4000240ca0800480c034820060600313030f1186c40c030b0b5000000c1a00e00180050b1400781c0c02040c2da0707081b910449507014600d1020072310308494090800e074820064801040f001d42d15002e2100248594400b450070010074820088460042010f0748007880748020301c040042440c10301001440500501c1c5500b452a41d040c2180181003e000a8665025500c8041064280800713000c0417155080014403605150740c90b94002500002c82c090360141040000041c01c1c0c0e2468043c502800410f180180da40320386180c90f41440c220b803944a59 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6815933 1250 6814683 6814729
    0x11401090e060103060b01020705030f07060e04060302090402090a061203020a060e0a03080c03071824030507021e0102210f0708010f030201030504060b040f020c1605090402210a0b06 80
    0xe0780400450040d044903400500400c032280680c0040c2d0402415402c125058400e2242e0070040d014001008403c031205629003031440380240c014441900d03074034000a508400c513400440c0041c180381e0700340c95000f4814440016001c0d280c1203002482e002c99a816001640000c0d140c2c0300b03100c880c0c8504503002c20b0a00007402c0202407039070060803001008003000a140300200016422600840d034005185540d106158116519804401d0040d200e000175140b0302e4103c460a030488500a20a050107003d454005085500801e00014969102842041515502801003242440a01c03081c1a440555040581003c1c6025400c0060301d41000740701404020405004110b20100c408074141901d4080c45c0101e020f64990070002c000c0c1c0703e0b000c00c80c0d40061401c2c50680018000d0740c0584030143c400030542d081c2a0f00c0189164568000c0d000712503100d005070000c24018640640700b4100e409510312920b1807420102c00803402c003940c5800c03c0daa5140703c4e0b41041200d203040f0032581c5101a005102023 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6817183 1250 6815933 6815951
    0x4020d06081014040312090203060a0e0c0111030f0d02090909010506150f07030305090c0a0e0106020d03051605070510060902070611030f0f0a090507031b0503030301060c020114091201140109 84
    0x4040b8201410185c1448602c0007242d44901c1140c011148080d0050110381241c18000404001440380c00e00c460440c0c00f4503241d01e43d040d03118001818a4031b465100035400d05102e00e100810315404120340d18403141d801c01030034100791500c2040920809a003000001c0e9072a02070300740240020403c001118400c07040003841505403a070002d84072500d40506d00050300790340b0328405a140c10401c0c49010741c486e019040000e90421003120301410703203100d0360950301850f010000c00d400307581058813a41c3c440681405494149403003503010b029114000c8044960040103175000c1012140907400500f215500004c0301010300801d8081c0820000446100300d14500e80031021500440b80038003880c40c11141300c030100d21800403680003200e01c00e40100030741d100039640c2d240000b98418980900c0901c200c030401d000541c0c0ca80402900e0490741c841d20b42110368a120b60044400011017014654001c406100d0051aa203410140360560151440001401e50300c0250380070348003405a001010b028180042c00f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6818433 1250 6817183 6817211
    0xa08010f0605040b031308070f03020d02010209090c03040206040b0a02030c0706080f06040e03040b0f03090708070302060f0f040b040b0904050a060b040902070c05040509030301060e1503011806030204020d060810 93
    0x89084800844403152651600d007000340c1b0918503850003410342a000f142034010300003940806c0200d54440e800f00c8414207511801a400d0f405005151136002c00c01000061003c9110300c004d40e401031006110170f16040c2c03680018901c5810046003000180d00118000100b40d4003080b0b100b010300524109506689088140e4004019000300100d000300d4841e200d50080c43c4c01003043d500603002d01d407401a1200102042d09040d500111200e590a01c180c180000e0306850204035902038076005000b041c94400300b1400000c0a81c803a00c140640b80b94108800200d002c0c1c0b1001500180c032180b4101641c61400c0d20810050b40c6018001002440c40d003141004030b111440c003114215000044096143e05803804e000b000908a54000c130382090400c410070041341c2000c0010350696950751100f62402003200207100a080c4040041255120108014010005028035481d2103459960000ca147c42d200d6000c181640c00c20203080700119101c1038240030090b020301412044034440b100401800d80200c01d6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6819683 1250 6818433 6818437
    0x807090f140609040603140d08010905040506131401060303080405010e07051e04060302042307020307030509040209030a0c0803030114030a02030703020103020c0307060e030306150c0c040c02070306110a08010f0605 94
    0x24a9200e60000210f090003500c1d0707a0080001950030880d008003c1c8056280c8a460b600c82031118000101d07504004141c5078024454a401190401300503c440d54803550f4595001c10001400d82e506250340000e80e14000c4240a004041c6200391343d40000b500f0a480e209094484044c01407032035070000710041c031060f10b61803202c192850041c0d82e42d0188551190204005050503000030750014200080b0007a9644d10355003240c11407024104000995135450800c0307859002e0a14001d0004a0800842c3e50914040c1c02520a0034030003070640c3c0b801e40442e9940d150060280d070000301103800100040048000d1174807101c1d50030805402034010b0804950020340c0750140c3e400000c5c14160701080d241036011041040c0c42c0d040da80303c0410030a505180206a903213801c2202d501e4490840d15202c032403c100c3c01d605454035215210000d00c030680d60a410080a054050841401c5101d4002c000002c06c1040c02040b9550200320300035550346018505c002c0030340f081600a4000300b02210f404000155001d82 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 6820933 1250 6819683 6819719
    0x1090308070806060c10090311070e0103030305180a050d0e030706050d09051504060e0c010e180403050d0f020d0606050301050105040303050a0302090a0303030c0e0108090a03120209100807090f 85
    0x1a0881d41da90300c3d4000107941e8054a0040d102c0c51161003c05440801107502421025002c0d480d500075094100c0402a9202e6041c0220300c03040b20b1b078000400001e40039800503900106541c0135543c406050604591400c3d466500580d46ca500ca40c80c43c50a442d000400ca040d068401e4001e40710345820604054040d1054150300410300780c0c0d03510110280030080c41443d005c2c08440100410b1800d090504c107024040b050303003c211500580c201080c1660181e01400051900604440c2c540140c100711859100d00081054083c040c00b0010540000c0c040d1156032501c03850040016100d02400e6440012111140c218500b840001c20052065a8100c4143da0440f5410300c0c16580c0c0e10307503008048010f4080e90a00540181000300048101a0141c000307100c16806956450301c540070080c01190060340549802c200c0340c100305041c0011030700c1541c904040c181d0984001d031070048003001040881340c0700e00b00c40001035000e60902942c240c3c4200c06800400000707212a80c55410991070101000b9400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 6822183 1250 6820933 6820937
    0x11a040506070609050114010e090d1b020d0605071106060301020405030613030c0803040803010311030606010f030903030b060309060912030402032806050901020405040c03020c0601090c050408031c0506030109030807 95
    0x320b810010401c03150445410190b01600902035020040d01d4041010800e019800200480c0381c0054040000008d20034403d103e9a0b8030340c46d0855460320440c080d034545200c16030b0022510491180400d0721400790030f008803996a02c54030384002c48a1980c0c01c00c240503209900c281d004020400031070fa000078402d5007080d601c20310160501c0785407400f51906403810300300810b041c07800710401c000c1c09034001c09503040720300490104299580800c1015200c41089410302d020907560214064024030030790154409e00e210317040008140c0848000107040b9081200c2c917140641c002c0d410000c42900c180716440075405204440341c02c50903e640003079114101302440b2045029410000c0000ca10003009405c901174100b0420804c2d4103180f01014040e60290144902807030802500220341440703071085482421202d406080b5603400c050610f80600741c080703508001c1100600c00841c2c40300080c0001c00302030015800c8010401100c007490802c3e51002002c8a100364076084516001c80d0300900041e500942c1d034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 6823433 1250 6822183 6822187
    0x3150f010303050c10090b2e0303031505030304030c060201140705030103020603040c0306090b01080606190b0c0703080f0301030203160e04020f04181406280c0201090f1109011a040506 81
    0x401c0c0082c585154903178001303452400c202101080c0558569141d000c0c0c079190307054000085001c40b80480c01202d5926031021107401c14420000300744240e00c404086060103401441c0300e86d0341c41c00240366800982040d00e00707083c031080402842d60244200e140e08414a0783c429000d1501c0d6a01403c1408140300180c018035000000404010710448441c01450303103c00c0c100318010f07650401090b208000d010b20701c964860000898101d00d404400c00c03041e100380d002b16564003400c003140780a0580113011040400d11804101100003101c6e01c0c05000500f50314000140c0700e6246004143c0781c5401210741811103182e0100c203206400c503500c2030660007501a1200d41c056030208010338000c1484881d0f500c0c02503802c154120030880c40c105e04807801715280040360041d441d042c421004c0c200680c000384a0412000d2910005002d0369003010b03150010500000580346020303221700c0d920706134142c401c0350790126a612044072450034003506400341c022200344c0b0480f0200700c030a04e4081c1c41740d8010300340b1070480 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 6824683 1250 6823433 6823447
    0x306050d0318030b010b031504110a0e030703050a03020a0c050108060f01080619080312060414041b12060e0f0114010501180302130203060112090203122a03030603150f01030305 78
    0x2d180750400056500c070f03112050560b519030180c40c0d9070300280c0d0040d44040130140b882e021840d081c01070045400785c0c1c041c4c051500c2c2c0002c8054801990703400900d901401020f0001011030000d0001c10503042c001d030003805005146103090700c181111070b00441d041c480300b042480200c0d03e403a150054402c0b400e0034080040e4642c00c00240c00540e45440c0c050355200014404030303100360040702070180c0c20000c8140083e42c0e101e0900304426a02c5400980490842240001c4c0105545100b6054100d000d8400300700007a84400c0141c0a618442c0004e490780c0d070f200c4003d0100f41d5000c120000010b04008020032802700c0d0868211300e0744606100b03490401075a0326072500c078250130301c0c078038002154001d02e240612110b070304031417010f50400c40301c00703001c242c401c0d1040c00043c8644c052448050b030300801034400d4120040c80030280e6048654051043e168071507180741956540d015054000040c030008685a03c3c007071040501c1c280021481c540c15002c00e00901c11041040c03182181902c1c2d050400700d4591070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 6825933 1250 6824683 6824717
    0x903020c04050a021801080606030406020702011103070b10080c0102070b13170105060109060507080405090408091003050412020d080c0d0209060f09090a02091008040201030b120c0405070306050d03 87
    0x2140c0c0c681103a00502d09020301c40d0104866005051a03076004580e80100d451200065443c14000c50b21543c01410810004002400c2c580c01050154070504001c20810b0075204402c5c0755400c440000c588002c2285c00340603510300b00c920b4810040c1020401408500c21040c0000e407503000300e2050600d50131009c5000c01c004400a1300790b801074040015182d400c0300007a00c00030301809055aa160216112410118140e88103d00315080e494029101c030b807429241c0000d00140300c50080058a10000901100c030b00e44e69400d010745114049541d000c40d6604007404d11a0f40001e941840d1010b6620200503001055004900d15a0101d60040e03001c0d2514119002da1019110b00c400d4a58000301c0000d0903501d01500101402005038151303280c08090382d4000e640802c9110380d000300d0703500000c2d2a1840482502c20b202159000344185000b2440d0b000c2c2d400860000318010000d081c50346c11403030250f000d505007031040d180c0c40241c80c9000e10101d843c1c07201144104021200140410143c4445208445 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 6827183 1250 6825933 6825943
    0xf03030f060b0c0105160203030106020d050309010902120f010e03090a03060509070902040f1a120a0203040f0510020409050a0501030308010302090a02040e0106080109380d0f030503060102061609050103090302 92
    0x3102d100c0035034403042040300e180280300888200c0c040031115a00311107014400001ea0f4141c0f0344903001084079a603045410340d0240c000500c41d00d2259254412f000c01a1a011180c80804000700010100c80c1c802103152425110300071144030041e0310920043d4000e0307403000c1c0020200c0e1342000d400260394850301c0c0018100034030b5810841400e4000940050000d0300300412000321004209840600c00c13803107100d2003040c4607420003080e4400001c3c01185c0c80c00603550045401a00c691440018441c43c0c0ea00c2c18202240010031f040e11030b0b8040b070f041100001c140940c6a102c10548001c102942c1117a170301502d04541030001030701a980504c00915150310303030f6045038094010312150140c0740d07039a604018000c94090243e40e00d001d044c00956400068100140b1501001251060b0110755a0080e98a411a50100542e40c40401900e036440400c000314000500d940c001e5403030711780e03a04d02140061316007100035003000d80c400c00c80d42c180c800302544039070344130207503202440d0100740a8500d040480c908 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 6828433 1250 6827183 6827189
    0xf0509060f04080a0503040303170103030903111f02030a0e040b030703030305040f0f0501060f080102030f070e0112021306090f06020613020d12080406050106020f03070212070b070f060501050603040f03030f06 92
    0xf500c1824110014042c001002c5c2044900c641e69008600ca1425011114030b9420b200080210300017200900000d51000d9030f5602c1101d0107403140d02d0001c01c80600851003221901000d001d60030000305100c80039031009103030350b403800c0a84040c011105000c020030380e16201c030721001c1c080503511700c04601003107d00394a4030611034018291010500c1e9609003a03000304924070840d5600702c4211070008105106009482c0b1441c4000c4000306540d0341c1d10030966280d0015840d590420054056904c1c83e03800070320240c8000f901c02c8962000c918100301d40500400e1458104150402101c2c2c1c040081c503034000b4849a00c5400f2010384c07100381940d0b20116000030040b480041134043c50180b14242c10742c1c44120b06104600404c1d051040b6669218140d07201d0340ca1041c000102d070070404c80b99000d410420020700f003c0c640b444c1140c8070640c0d030300902c407181d030000c030004c0314940e0489500005010f62405142d01408080390307a03a00c3d40c1042e95542d850704d03604e5071000b4241500c0301c03408401522254418001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 6829683 1250 6828433 6828449
    0x307060b060f030f01060905040908090111030c0d0201020301150309050607050d0902040204170d09050a0509090f03030108160801110d090c0302030d031508010501030201051e0d09030504150f0509060f04 89
    0x40c4e04041d12a00d81204c400d01851002030f0510000140c2850301d0300a80b03240c640c22115543c034240c9064011200c031001e5010380400d40c0700802014103000f0b002c0100011041076540016200d504180861058500c9600380104141c2440441d102045010607295009100c0381440b9984890f41c40454024010f104c0c1c000c2d60003403020a0025035210201030280802e0382d0081074130301090741400180d440703034118040e07036410921080051007141003019050307400000a4044070a0304141c081003d1a65200742c00156440d003180c080004100c0352000d86078017a0420b4402441282e4070b00c0804082409484c030703c5c2009035243c007008420700c0025500f0030003568000e410313998401401d00010f405054282c4803181c038542600c00003e0803510622030541a0380c0c0c143e42d014070344811100c0c540c031104091800241060b8003041501030b040e081d480340e4462140b294480382e444624003a000c8d0484080034604c81305000075901c4503402280d0110480383e680d102100e40586400032030f4108c0c1040d020315001401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 6830933 1250 6829683 6829687
    0x70b180402040b04060e121207031101060f0f0b0a02060a0b010e04050405010209180103080f09060412030c0b0c030f0a0c02100906050906060102070608070509041128030e0307060b060f 81
    0xe1000e5000001380144c5440d42c8698401d030a403131090105150909000c81000d8014034a00034605000c2002485590701031b2414001031403040e01024210381a44c1d000b079a01e070081c50820070147c4560304008005002400c040303410f10090120103501c0714001082e0600f0280c0d184070340c0040c0d0b80240a000041c1c88040c104000515080c90614000e62150300c01c18844c407580103030329aa0503018000c25050303a0748a49080c0c2000307190b116071085500154100e03980a102440081507840c6a8480740072414003a85d81c2c039030070640609040d00e01060261400c080c004040080081c1c0e0070085c1c4009810907401d0b000001c80140c004d404a0514201284a00206051070482c06c18001d10790071460080203510103030340f651b071654801a640d8110354803c0b140811000c00000d2383c101e020741e0151030b03200005400814440300c0d0040200c5180d005040c04a281e461034002a0080704400310001003010103810100841140d079800e8540ea800b5040000700300719140d02170340c5095101c002c1035030b90418443c0d80840e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 6832183 1250 6830933 6830939
    0x50705010504030e0418020d021003020903060a0f0b0406050d030e01031b030510050315040b0a060306020a020a050c040608070b0d020d0501080f01050c030606040306180503030a0903080f0702070b18040204 90
    0x624482c2484c410303511842c2070441c0c8000045640050020781d46c2d00501c0d900c400342c0c656082c00740601e2050004000d1650a0080b00802e80b000d20003a0b02c07400b69040000fa07030b14240701c2d81c6c00072a003400030458025450b10b081440306841f0346000039180794040c1807031841d42c0c00c00030040b0040c009490148902c01481101101c5154254021601601c103503c542e0350000d44900616656100d080c540c1c83e0034210143c042004102c4400c0025005458002c000c00c44941fa9118201613034800400c1c20016030100c01034806101040c040c151025400312401c0c0301103480c05469643e901e0050003800242c0c4000a1110341c40e134031b10390486d1001c41480704144202e46e505da05113500d40d10101800420f40d42444001084441004101c903c188c4004081d00c0c00e1600319200c60300280309003001d10f2004280703040280003040c0100082e51040c5e50141c4003007964001450002c00721800a030030609603110801c02e120b11150049140c1040d070302440c036031035140d07074195540504142005d007100ea04584005004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 6833433 1250 6832183 6832187
    0x20618060c0f060112170a0302070602070b06011e02030a0509030106050a080609070b0405090c090103020c01050a05091204030206070305090102070b030c130b0702220f02030c040603060e0906070c0305070501050403 94
    0xc551500302e09042c0c034020b0380e03500204400042c400500420303c91850000d42500c0e00c2d068040c1c0240a500c0c0303001404e2100707a07980ea404030b9010304000d60f40d0398035010801609690180c0c001c610f0710030b40340140c80000c2106401a50703034012030700e003141840800301d0100d4468900754000c000074400140308002d041d9844e4420b58a6240548240c50a801070032000f02d6070035a020200c5044860180c0071802c1c0340e850700f000f03442580140b9031250401d40c082005e258050300c00d00481d402864000e900241c5418001d05441c603104042c0003c0c2c0201c0e00500c4100b0240e41d0340d000f502da606c2c0d01803c24503660444800104c1c02c0c50240d40121a04610100a004a4582d0000940918010a004480e5560f06d40318461440e002d101c0c0000c3d130107451081403185070880300079201c40c10010460040f4551841c6000082030742c00c22148a44605004181008280d44c1401528000c0c40000720000c4241002a041905c5035401800f5209012014802004040c031030740440d00503940040007004241030078540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 6834539 1106 6833433 6833443
    0x30c020103090b0718050a06050d1d0604030503040b1005030a0f050115030302150c0301030201120b0109051804140303070215060303040306060305100f090c03020618060c 75
    0x80100140301c1c071240c213005042a440d170701605100b41d101603000300825071129125030b00f42c60040207080d4200080700c10a10742683c011a4049020b9007011003032000103000401885500100b20603d80d01c4805140940d21582d03840304203440343c2d107012030035400c14014160b041c1c008040c0300c0f000460310480134440c00c4c4620008255111416901c50038880aa4026009038001005007541d201040b5002584000c441d01002c1c00d65055800080500700041c080f401c40c20395035182c40c06640c0c0291114402014000e02d11540c221110441e400001c400742e4080303d600d00c01d21140e0402c14408803da03481084950b0042080c207030704100c604842c840161020303806010802c0003002080507800361401660041004100310b49500d408102191924580301c2802d92a200c183c0001440410a6008494048600743e1302c0c0c01c0701a5000c40110030041d0700982c01080090b0800c00072a020030 = true := by decide +kernel

theorem cover : BRFrame.Cov 6654683 6834539 := by
  have h0 := BRFrame.cov_init 6654683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6654683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 6654683 ≤ n) (h2 : n < 6834539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
