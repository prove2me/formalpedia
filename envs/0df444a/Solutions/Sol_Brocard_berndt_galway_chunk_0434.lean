-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:47:16.745995+00:00
-- url     : https://prove2.me/submissions/3398c21d-73a3-41a4-b954-05860aa51be4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 77877699 ≤ n < 78057555 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 77878949 1250 77877699 77877727
    0x7050604061e0c170a0204030c140901050a1a0f090904110a091103150a08060106030f0f0605030a0201110c1903200303040b0c010204030c080a0303050106030e1b0a03020303 76
    0x1590082c0200740412000044010704190b4020101550100f00c40301c002c20b0403070300e600c0b0900e80e201d00b8480d0013500c0c05d6513940c0d0351000c41030700d603011000a8000241c08001850700900c2580180342c2100c80204040c1445880c01050b085e060450b10341b900c0000f044141390001d681510020b020080c0002e0303581c0f4050900b01c00d46014070000e5849041c1e0700300042100c100500c00c03011680b25505200b420b41d5504074458410703956109225500a0007900002907070032040103924060700700c2d0f59003c14030039641400c12069803208050000c81902344a4144006e44000842032400d54091801d4000716103521501e508002c81280136603003101520b80c64065003d441c03803458045034414941d1000050340e0101203050071440550742c0d44c2c1908204410001d10403000042d000400c141c0000600d019540e0351042e1148041d98400140c0d038000480110516802d803041030b006000904043c403d880700202e1031600c814288412640038058400c0184c81524ac5c4c04003480596405800c480e620710b55608141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 77880199 1250 77878949 77878961
    0xb030402030c030708120d0914071a160303050a060b0a03020901020c040504081209101a131103011502030d051806090309030a03121506110714061602060705060406 72
    0x180c060b2003485600c207158100044c01070215506503001c2c01280600c110140c0755540100500100365840b10300a0700800c19202c2d8400388818208010541d46151051003141c0303020681d9858000001444000d0080300d019102d904d4403681803600150030303074408a01d44020221500074920000f0b010840308410b980503402809000b100342c0881e4801000c1e4010002501c10490340108200c0003804982925070807503c007903130030030f10310001da64103440b00c13440e400c0484007090701000300300c918900b150b005400c250b4400a0003605c51881031102c050360303003284103140c4010720519215a041c824000d40c1c80d4400d0007603440070041e60100348068108041080024040000461294014000494030b4840000111001c03140d004d8003030300e103519503034900350f40354040d005480c40803544a40603c070082410221620181040d03460f2040205282c035004e42c43c09016402161002c0c10110450040e556180161911303602d070214220524552440410214050960001e1091241e01e040c0f1040008a030002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 77881449 1250 77880199 77880203
    0x100c021c0504140303040b07030e1f0210050106110703020105090a030501090606051008071407020f03060a0f05060f03150a090807060207021302030708040605071e09050a05040e070b07030c0c0b0304 87
    0x1c1283d001e00400c0585920980c45001c010710300030401c010009001d0241c03864170304401010021001b2013000d2607414640542000380060300104019202615980b05071070260269140c1940c2c045c0d10b902020f660381c0501c3c00042e050000205251000f030f41c6803880003014603441380091094104030f00d8140003400043c01402d1081c8100c00c05404003a1042521764480c0a60b81d80e49101100140c07444441d07980a114240c0c0c02002d407104003d00c6440030070016024a1307068000094605d403c0001c5412108050a0a8841c0d0f10384000c01050750b8001516403218440b81195085507201d10020301d00503c94070a00800c00c0d00085080c84c284640795016002c900c1c000e4800098000c030a818150417484102c400c00003040e00310001c500410040d40c0201da00080d9418000b07107400c181c01d5608041702190200900050342c08809011909200c10600c008010942c4c0034040907107980714041c2c955500d8050301040d10f84c04941d10050500c40c2c0c1140c4800c2d81c0020f403400c1d0710354640f030940796154011202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 77882699 1250 77881449 77881469
    0xe190905100503030708040b030a02091f0f0206091e0c0d12030606050405010815120f07061706100f052a190507050f0102120a08070207090e100c021c0504 68
    0x60740f81404001c81d9021a84440303170900e45814040441d156810142810f107041c0d03402d120000b110b440c0e903083d50507004803820041011403072000c0001c1c01402545e102c00c1c00c542020050101480c0e002543c21001030b46400030500d000c8140400c0c0e441c160a1000182d4046040b591960038080c41440c03422035040c00395018040300c1d40750340040e641482584034190000c1e80f03990001b8480c282e408984045c0c00f40003420b00a00c1d01500032080c0c03a2942d080d40070b14194100d954208480c68101500003001e41d0111341c0c070354440c070701200003600141c0b560345a1014400e1440100007450f20903421224401d101c90864031500e48005280030b00d038000c9004080c000d1086c01c003065130031034200003080503040e80040102801c80c01d2100748502d140384400354a0640c41210b1129001c0095003010b80f59244043d500c043c0785140c0300070002d00e418895840f56030078a01d00440c00800000102d8112030312105250042505c20303014000300e00c1d000c000c404128400d682035020945440d88040100115030242d50 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 77883949 1250 77882699 77882731
    0x2030a0b18010606090506070f241503050607050c070e0c03010f0803090a0501050d020d05040506040209070f0206010303032309060610030c0206161103040b09011407120e190905 78
    0x44507801c8076183c3c040e20000c9451700c1010810743c03400c90002d0284500c240041c00c5001c82698031554502801c5030008200d10544113800b000030805e11540e00c0f807807090030742118414507540700d058a03282c000c0d161108103c0c0001c0d140c21807140c10880c0900034000d1020030403240c0341c1418403000c0380d0003e00407880d200941e02c0780000c04034070000c25643e03100d0700105040205403034540150b0326584800f0754140c280c2d80900082c0c22800741c03031003064404c50089025013041d1074144100000100d0003841e29003400503062807071110560003d186415250326042c0000e107107121107660801b10302510510070701010204204403400c2804940c2e0340c0640000d1760728229400708241c003a000e99510368030240069020700002106121510315801d0008040d06101c1e017103c0380c08100074210340c450380104240c2007002801e40d1455030700c15111031030704030341c0c1c042c00b410130b800ca94681c10302441c1d68125508201030020b5100b4169600d05490081c086040b50400307020b50707035400c40c00241600700ca078807049101081c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 77885199 1250 77883949 77883991
    0x70209011403030a032004140f041401120303110703030e060906060d03031a280608010f1502101506022416050c071211100e04020901050702030a0b 65
    0x400201c4540140070714103014074070700200d000b0b1101c3d01d81c48840c804408070f56016400654000c10290000481400b0b4002c0307401c09024403d0030400146029901d01044512080d4500f0701c0306041d2084007a404a04010600701200607124503a901008428000745010425415030f10030310382c13080c200b030584801e60303103101d4200d413623000843d040b64001484100780400288682d01c5840c0c044031490b52a814902a00c0100e1001c84250741c2c2043d0f100303541914480b8521343d420445008254926000059606242008000000510480d000d8000c0d07080705401440c000d005103d000348407440100064400d180714002240114801e45c0c0c054025810440a6031a41c0070f6074070894000090350886030f403500701c40102c80c3c0c101c6048050402000b403240c00b06100d0140300c0c100017020a8401c0d407064a00b20700304403544d01c44a0241b01d224100f035140500001d500b06140c01200c0d10212001611070071134000580c0c5a02c40c0403002036060003141000410800e440102030300172940c0f920850800c044072 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 77886449 1250 77885199 77885219
    0x5100801140118080d0302070507120804180f1e0c0c0b061002070806090303060a0503030702030a08090103020c03030109060e13030804020d0204110307020d121103180106120302010207020901 84
    0x20300480440d00341c031481d01e0110b540600c6072040700044040e41c94120070f554080c298203004016a106000035000240e000a020003001031001408040000543c01c03443c07692000407500ca1031090717810410010f410908000c055900c0200c00d0f2485501c144401c0401c03a00c541021201244800407031807610701081180c034071545c00900419448400c020450f161041008401940e00255400718031800c000807650f00320070b02c0080d00a0032184015a102d080c070408000146406070442c0303010b80c1c8240007890240e81c0014400034001d800c00070b4183e13150504d00040b0302034801d0428907040c5100c00800010480d6035030340f1143c101c6540402d802d07407545410001c080c0c00914840082c00140c140c002284c05443d20310802003400c2d10041002488070f066000784160351f00100c42e00d202580211940c411a0340c0c100410f40302da081c50302c204000501d0480c459515601018010980d256200c02c2c00c0c0008a0303003507000c000500f0340940b07406003400711071400a010b0361100c10124010340740580001450045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 77887699 1250 77886449 77886451
    0x20a09090e010c09120c080307060510050907050a031d0a0804030210080c04030b06040b0d0b040203060a061a0906041a07030908010605061801030b0901170106151e030b19051008 78
    0x3d1035940e421081d00e005005184c80c2e2108005440d41c010148000840303001c03c100401c01d8501c00c0401240900d4045e80c0c40703650111661000e402403907039208004119a220048070200b90041c00c0c0000d0b4520342c84403600e03c00304055090b00ca64410750300380000b40006503018104503442202d403614031461015040b01d594800360f41c0b5103215841400140b000420641905a00410262000445582000c00207410720b0301c08400783d807030119100a103c02d50a0500c400b603031150141c003081c00b41e0761800011145024102807103402a01011503106c0e82562100c0441c1c0003010318000c4100c0004056041c0200caa0044000702d003c50701c1c001c00060031140600400048820080070f881c207041c0b042040d010698428140760381015902d6281c0d6110769a02030156004e000a501e8188009074903841280c03c4480542141e1405008910599406030f84800c405058030741181400c0000e01000c3d01c1070300a0300c0c040d141c180e8490007620035001e50300b41d140300603811254100c600341c1c0c4069103000c041e200307008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 77888949 1250 77887699 77887721
    0xc07080f0f0c060f04030209070c020402030408041d06030607030b010203190f021e0a03030c4103160f020a061407090504020703140c030408030409050a05100e010909080d020a09090e01 81
    0x1303000d000404c054544043d01d5079000c83c0500b448025040c00303500040c01c0380d2044504450b0090003007024429030340c1e80324494010a007140100042410f011000a80e07440004000d00201621007000402a910900507110280030311004109003c7d20010040c00d02c0e160303459401e0042c401c006221b00c210350f401e640e03c440708010001911441d40181c80441c040c001d43c07400c3c08144801c610009000b209000340c14011a1010b1035400ba64582c10b0503000220307100c02d407442800c0c1c07201348240501c0810303240c4400e6180d0312600b089005000407150a80c00c10740410000340c60107292829140e0701c10000003460b407185400e65601d040c0310f500d9401700700c2207004045010f0009002d841c01c213040690170704020111510b80c5000c5070b0400c2c0d560000b00b45940d010340c114800c2c050700d50307040c414809c0c6c490090310742001c01c07029440c508074108004402003a50510420210f1500c8600442c24080801e044031a20290400c0a640d02c146011024095a1b418801d2030200c510b844800f0040795818030030f14143c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 77890199 1250 77888949 77888977
    0x8010515041806140d0c030b0a091b0603201207020c0d2108011d0406060b04060e0a09090506070c06020706060e06010807030218010c060b0316090e0106050f060c07080f0f0c06 77
    0x350868658922020000700a41c003980d2b074070128800401c0c1803484900c00700800c091092160b42c100b0780000e0659488420892800122100d13000e000c0c25880191001070759a03804015081d621704100700d140c481440001608001c409401c4400d1100140300245032940010404108810090003102c0c00c0b8000d1040141881c1384070010820b6210b034a440c250082e014220104a080d00e03000c5a1030264020f9000401251718641c154400d0300f80001850010500c1c02710403c90b9140d1030311611f440302d40040c01d000c1040100d0803580100409135040c0e1b00e11980000e403c201c01e544400c02000c0d41d1100341c4600d404124004005a00244a40216010001c542c40061040710424005483d19541c101d01120410f1726034007801c0706620108524400940d4425400707071224907048690044074445420032203a40d0415409100c55207610400c0e400c200026140242da44500e038058a0400031a034010400c3c9000380d04440c42ea603080000c43c005641120419905000350001c10000745100d03100c0c90300301c20 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 77891449 1250 77890199 77890223
    0x510050c0304021c03110d030e071208070308070507060f0905010f0c020c0111030c06090c190302090105060f190816020a020a090c09090203040303060e01140108010515041806140d 79
    0x1210002216940003171080c2441c0300303202840c036001418408406070040000c0d42e10082c440d007001c41001040c0040482e0114060410307151303200c0a4192007213031405400d005e00c01d000708072094491400c0320b100341c0c7c001070204500f400c203240310005404061f8042e51550b0809542c00d03464041c0344038010030040c05030004d00c00003c000b07006440d02c2e00c0d02c0704400043c1c00305201348051560b09001840c8114085000380900c01016070801034007401c000100c210340c10a2210900050f1110a03c181c1075960840b483c5446002200310300b407891103030010410314040111005403e280c1c014084c41e0041e40312241c210081010144120f03510801c88038040d41c0104100810040807440d64010310361038a46140110f43d494540c401079080e6070055400f2000a540c88a04110035442425980c0c054103000b4801044d201841e030000301000d606000d018448d00b50b044580340c001c0d015004079001451040e04440900d0003002c40e0200904082c4640420b07141c0081080410785406104080740d80d03442034543c152 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 77892699 1250 77891449 77891479
    0xf170106030e010e06010801091208010815040609020301020a03090b01050f0307090203060d0506040305040609060807021c021c0801090b090403080a09030207030f0f05070603061d06060d05040510050c030402 91
    0x5890007902001007035680f04440ea00d0107009005d15400703043c4210020079010210324184924414008000040105078001445248400b00e816540e039422481041c80c02d4485044c9840180701c0140c00941c10340c0f0000d02800301c19050340041e10118000e0070400d00c00c0c1e1f40c0e9010301c0300303541456005681c5a0000c203010710000650798065038003d240a002e07440a039a440d030300c0e40d1402e10300352030940119101007420403000d80d01c080144041d260f1352501e001d080c1000200a569030304041081140a45040705201e4180d100b00404003071659200c1000c0401080004007a010100038025281c105041c811003120703900300442c4141c0190f6042d0ba406659541d024018002440180c10460841c0110200000850403074040c02d41080d0040d48115003011692800d64501607480e4411010705090000410010000d5074140c5020355030740110280c20799800b40010b14074440e01801b1401e183c03621060106204000a1240241020403802c0000b9201d088203000d0500003220000e6010800c0015490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 77893949 1250 77892699 77892701
    0x130626012706060b122d0609040f06020a0302090102011a010c02121204150f080906010b0d0f0c020f1911130b0918010b060702060d0e030c03040f060f17010603 70
    0x8205004000020f401a2609500c06150f440380149400f0f110b188414446104802e6901c1c1600300701c0105494000e06180b0055060400d00408861041a01000003401e005c1040b91040340d155000a04541d515003152002d0b00941000341014019031a01e17564084810003d4000000303042c050715080718021443d070030091600079100071403045000f42d0820403a803e030b00d00d0141c005811a02c880b6038482a1441c4c0c01456140036100c41810030220f00300b40200c48201240707590555011801c1d00c4da891001050400103003883d0000c0e08400c40c900141014078560118440c8104550031083d00c1d80c2d2104c000c52070140403240780c070250405200b0500f01000d4901401c18146189814201041c42e04036100000c0e4444c00840b07060350030b016004080c4d9010780d002e104020707034610200d8105003003410130b070040743c1c207401500e0020034210390398802d9041074202041619000860441140d58079925888a40f440007007030300c00e00c40810361424201c1c00103070040380c3c030160b0349204078901046070b0718081c8124 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 77895199 1250 77893949 77894021
    0x1020f070e07051201120b1303080105011101140c070311030a090b0a030605100c02090903040e0f070e09010305030703020c0a060e040b060904060909020a0503010b0105070b0613062601 81
    0x8000d002c0100810792004601035131300c9008005c141952030140f1110700f05045021402448400c910510660242c00203811400c100e0540c2d500f0701e401188a944c41c60064010b000b80035065065070241f40030048840000740050414611a43d5101c071000c030603d482c00d59a000f44041200807840c0310100303209021a04015040c8280c0e149404145d480c0c0d5503000c21144001440290005640407102d9001c0d400c00034035080c1c201240b000110320302880c200240d1088040907040c0c22440c91254003040301c080c41941ca0a00000e001001c089032035035286016650707075100036405c50150181061581d103610301140e950080751002e80340c03010110003800401000340078801c805a400385090003400090786a51160501038440280d001030140007a004204a059580d80940e2183e0b052009888507641e001050300c0e01a50701802c7c011142c0c940c1c5001030382600c18050a20120341c603104c00000c0280ea21007080c512a085030090403407900d28484540e090b42e1945800e44d48200060015244250721684a8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 77896449 1250 77895199 77895211
    0x6070503040302100e060402100f020703020d0602071a040507080106050109030209040c15030b090a0b1516022d0909340602060915090a020f120d090f0501020f070e 72
    0x244e2076090421030b80004407103001084240725400b00d81013200710308101c16140c03842d0b00c07142000e5601040700d4000a69a49241c04024043d080c00f0340d00c0b804001c540d4040e01d0925601c941003118400c803c04403400c40c803608170390580e12881843da001840da9010302c2060240c80042e9900301d0241c2c1141c090080b00800900b00325030401200c04000b8450307900c04e61540c0402d51582e00403400c600c2040811004800240c0036180d11441d10461010540d42c0f03031a06030b1744a01132100251180b40071901e400745000e1060010390040b07440c544000900e400c0c3c19503441c010300c09000440c0c869410009005150301c04507070014440e40040301202c00143c14100032a1f070141c1000740e000b401ca08102d10b212080c00355522107400f503030049041c014002e4081c445e500103110710418031602c40ca005202166a494201400b03400f03010210ba11428940304c0d40455035a0741c0d20501100d00c0340ea1700d80c0b001842c11a0a10078420340742030410740801c1640c40032413003d00062981009001260410220001407a00a046 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 77897699 1250 77896449 77896453
    0x1407020f060a1e0e1002120306040e190605010504051303020c090603010608030c10110c0c06130308071202011b09090506190e07030c050403080d050c0c0a0507090f0e06070503040302 80
    0x854903000046000d140a4a03136584031410342040091000c450b20f911441c1080d50402842c60020341c00d03110540b68004400c80340481c00908513640c0e1401e1648100d08100e055203604880b0081c080242c000038120b0701d00761002c0065a075101100d11510403007120040040e00110780c02e1201d454201416504a0340080000407400e580300040f502c1e5130b02880304e91269030000980f000c01c0144505c02c55500c000860030040c5040544040d8580728141d0710301c4a840740e41c0c0411008401022410f038000a5540002c3c00e44d59084182028030010300e5079072440f8019820100c48a880d100034a1580082145a80360280800d0030f041c045409801d005003481d0b044440000a040b104100392011001080c0c034410700440b50800c24802020b5606100d2000c2c18818200020000282c1c0d0f80103c5441c20011a000903154884101c4c403481c1d0301ca02000c100c01d501c40c00c401e200510074081010070888918581c10005844410340c51425a80348400c011403541001000031540ea018900070341d03209210b841 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 77898949 1250 77897699 77897717
    0x30708060301022a06060f010909050403030b04050103030c0c0b16020402091302030708010e10050a0b0c0a05010204171005090d0804080c0604030c120c120c050309090106030504031407020f060a 85
    0x100101d5203800c010302d10111404507044c4030b268088140441d0307400c0300094a0310405105280d00107882e15034144511981650b403000000d0a0500c66440601010302c010810f208039603503420010314410b45050280c8040103140b40004503610240102c48240c0400f0f00e1088100c100364080200941050310710f1604001c10402440700a0744902c02903108414a8903901002e50401c8000d1144a0000b4005100100044130034025a5140d0014a04903402e555911f5134441402140508005112074000c000f90300100300410402c01c00c12007125078526410031138120000c1d042981d816a8019505080c40350090190b004455106520140d402406080b060b0700d05401e0721802071400004540590000c0d1001e4400d030100013102100c15801e0506145c522000c600c1c0d625891105500007401e5030500810801c18400c004051056035a82e100080400f0410b40e91640c000c0c001c5c1800b200d0840c005007040034181905040c40701601e003000d401030510050300700d500080c041c0d21342c0100b038aa028403c22031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77900199 1250 77898949 77898967
    0x60f04051614010507080d050c030906010e010b0d1a120601061106010f0302010c0c0b0d05010905060102010b0109170c030109120905032e0f090302010b0f04140c030406061805010807090c020303070806030102 91
    0xc000c0502070040ba820b92a81c3c1e2400e102064100340301033b0030000e0513864403801003000711132010075a051180030541c00540202031b078844013050065140126003060141c4200e546804001c62023604980560700c1c0e803c05107450740107071510340741c0034000d80200e100140800d1000d5441850240c0c00c00b842a800c80000300c3d154a0a400300d500259954900181c803800180000b503210300031142c0080e001e0000f88091800100080e0900d07415004030300c0a403402c103416003810b200400132400ca10300d006d0000c100d9201c0504042480301d40002030348010400d002d00c001280d040002c0c000e88802891100004400011540304401390140600403c4843e00c1d152010318069180c03260801a074487d0700000b41200e070b50024003205440c81c41000d4400c0e0710788090055140001244264441078504802741d07030740d44903e00a4020142030b000920a030074020f41407500c02c0503a0740b002d410303103401c1000c982d44295a08040d5043d50300518102005030000c0c00421283c2c0d001d901480e0300010010000f50a1000d54 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77901449 1250 77900199 77900201
    0x1103071709150c33060301020f0f03091504170c010615030f050a0605060a0302031f060807021c05180d05032706090603040b0414060f04051614010507080d 68
    0xc803002141c800281c8200440d50030000584803071542145901c0034580d28413201c0207031032240600c41121102d000002d240307070350a5041780d00c40c008610a20b0b460b0005031403003206c550011100c43c581445802484140e10215030346591055a0080d00010600f504c2080d0300c406400407a2448219034951202145070860812a503412071070302c1e900041e01221103049c003001d4545c080d190b0307a6180c0c9089424849619000c045502848440c01d001d41c0c0d030345038a10f0200c1750b0207640c0d001d130050100f041e0300030030320a5025904a0140303145500303c1d440709822200081c45011000b0561010490410440020029041c4124020400200300980c051101e07101d250441e801881d0312841c2e080c445440c20002450502c0f502800001502c80b2401c0c004684040b0340716100c082e0000d440b640035440042c042004008840c02094410b00940e51541042c20803480c3d09902590100c403140202c0f00e11040e1006074124280444245d80c50807407003441540010740301544000400c2d12180010003c01c0741103551 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77902699 1250 77901449 77901469
    0x303180308070807030b1c0807020d06050105120309010207030b060f1002030d150302030c0925030501030303050901051303053006010207060203030c03010509060a030b07020c010806011103071709 86
    0x198654150710301d014440207140840044c03250051526281401c94640c90f481c8100d985c0500540c5a09144a00e9003030410301402040402907100384181004010002c1076000030b4125602950740c1c3c03558081c5041c19503107a010b050140c1d40141d000040400114230f6000b0130581080020b403058103d0840e050100311460340140c104c0b0701581c00000c1003040d54003184584180d90495440441c0d0340b03400d550000c1e032210500c1c41d14038426051000483c080f811645003544081c88041c0d0210018111040050080c0809100036008030b864003000641c0c24a040c001c3c5031003180d4902282d10550304540c0d00f079440343c010005a01c2c02071280709490525454012030702c14983d00c480ba143c5500d15014000a00d081e03015002901190000e1061040c122510029039042d07400403030301c01c2180c1e510000884e02415080d440500500010001d2000940e004500035000b44420390302c51145a95402c010740f1403c1c200540903240c4d40c003c00c401d00204140407402e010308107080d12550b24041203a4002004054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77903949 1250 77902699 77902703
    0x15020a0e18070906050406081b04120c090606050c100e0f100624090603020a140406080403030f0c02100902040605040e03030702010f2c0c09010f1406120c07030318 72
    0x4003005002c02c160b045010000103150a00d489441c044c240740d401070419401070f09603820014040000081070341c02c417040d18082c10308166206046100c60402d01421240c07842403005d51803070034101040340c83c0710b00c1c11107a144d030224004000e41c0309035100364802001c0d090103401c01c500401590307500406090100b0700341c3c042d1040d00801c2c0c0c1c600705400d40c0d940c03030340d07203180300414566005051181a4000701240c1c1155002c0c10016201c0c491000142c801d41c40510038610515800907000c0750040e00048000d001d6800307580c08014cc0003803041f4400440326020303036003000740c2d0024848603e2641d9a422540700d039071000e0408240f1599a0380400e09942802c00416040d03000801006045c9909102d18844006091020701041844118018070a0703c075182c1c4d1003074048010100c1c1c141d03100401c03034088040c1024090340900c2d0b035030b6202d5106d0301380b460041c000d110122506207059441d14000ba01d514100b5030144150307640f2090b070315100c1603002c800704405164a9540c04001d100307644001840707540c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77905199 1250 77903949 77903989
    0x90e070c020910180207050703141002030711010c030603020603010b0a050715060312020d0c0f0224030108070b0408030313020a03050102120a2403150e0604050309030d0c15020a0e 79
    0x3d400c090031048040c0c8000c00b90091144107200200c042400040e18008130b03a007041c010242c443c4000c60b2030b0708141c10829030f0010305000000b48400d075980103442c016003400e030300c00800c80720480c040d0860a803012844040c0d4030a10500051001032422802494007900c2ea0805610f0140e40759141410300f0b0004140a01d00e82d5181c10400c00c0c03244608008451599074405040c1e844803140002d4003145125202804a01d2002c62103030441d1903c600c500c3c403c2c01c00090500e14000c01e03c2d14944c0550090140040e1805082e40000c1e06280314001e0320244d42941010310300390740d50004207481046503d801680e015036103100c0000440e40c00c0c401041c0c40070350788101211901e05078180340140c44058940d80b0014110312101c0340c41e60807603170b4580d040c1c83e03200ca000e0503440d1520401034082c14a041c03544a0f2802070005101c20804000001c0078100c0c030980a54000b04154402a542118170a10240c07000c690880000e003100c1c125030042c803024032142000304ca00b500000100d1548031609604c1a451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77906449 1250 77905199 77905231
    0x51510110109020406080703030206010f1203030b0f030f16080d1e050f0a030603111c14070807060207030c0b12010603020d20030f010e060f010507020d0807030801091407090e070c0209 81
    0x419030600a0301ccc050300034021100b841900d080c800c844c4501227524003800300350369803440c030055035500904840010401411240c1c04000108604c0c0c0f107505600520340100702c1645e000401170804114040a1107450b11140100a05000391100520b04210514100001041181868078052018181c20025907800054217400c61800398150042640102d20401102c2c2c0d100032440d140c10a00e1040b1603002c800e980c828003030b0340001458003440e034000140c80d0140600c0030849660020340303101101d01500703400080e00e656a107401303000e21504e96201d04890f444801030150038001d400a110507d00094000b03040c0284610325680341c0241c4400014280000090002c2514078650f41809403e0300c0f62680ca090500d8400944841c82c440c1505045c40804110032095644d0042c04005803034110060550b11041d52900600301c0409001d107001a0745408071000000501d8400248103040c3d640b28260000c3c1441040d91101c0c02c02010081001600022940180c80700301d1183c0c040c6a06a17201020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77907699 1250 77906449 77906453
    0x30a050319081b0301090b0f040509010e0c060306010f050f040806010e0603011409030a0c0804030b040501020a120c080604020f0c0f011b051804050903120705070303051510110109020406080703 85
    0x140c0301015000c03100f070291420b144030018401e807080300c1c1103500034400011900481c074007007001148c9070540e80b43d109180c0820031204500640095528803941d909403104041c0d40410071080d0301090301c050340000c01c0e0030040c55040d409400117004851103481c00d20706042c0d5400b0400c0c94580300b41c1005200400180503c25113040234040c40d400d0703150302c21641d620b524290340003a550f8081c1c48200010440c8895000c010b20416800b11406190841c100004d18501420924082d622101c007040024090b4030190113200114031415152506641e00c02d511601c5140c10000a03400403998900e4041c0e080000e400c98481c00c21204091407601000487c0d00c0c110320101c04001d060500301001400307c2000111b400007212807c074640c92100304c0380000d8540320044003030f140d0f0050f40c0b031f00d18030540e10500f84807290f50000003405400e40b00e40c0d2705000c00ea0301d0318100041010044010b0b5048000b40a02c034103600d00070540310034280d03200c00000842110039000501030701e0055002400580040c602401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77908949 1250 77907699 77907707
    0x30313030f1205071a07050403050105090604030806120303010501030f021909090f11091009030503030703090b060f0d0f02041b0c060501050108040503120a110c061602010c1d030a050319 82
    0x424102c6a00b411428009603482c3c000700010080d200e00c400049000008100d02d00500640e0040c5800c80b008000d01c1c64410445659100f09580583c0070903110000500f01e1300d0107500b40f1109a501c1c0000c0c500356464200150054032207000280c08031034080c00710000c0458040b549c040c1035240356444113020b51601c1807007403c95800600c841d01e1582080c130001a0b1244110490303d00d0042550b140c20301504851003201c4007140ea0300000c2050100006000351503515810500390076000d4411020181c492800f00101403210b640d00701e800101444000d07001c18600701e088442d890000d0700102d1081d900090060b00c0312a5547c40c98045040d0030b45280900005100b4140540020700f8400c2c424145500e40713076074a00807003180006a50788440020b0200c0703c584c00c10304661455901d031540381e650b40b410140d2280c07022250f00000d201803a040300161841401000b065150a842c0c3e190004001c103e601088044203003640e40510442494200180c1c0820041802c110b038024100d401c4112410010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77910199 1250 77908949 77908973
    0x30f050307020111030306100c05030c0f100606020c0108010608040f02060409092306010302060307030605030105190b040629090607050109030f02030a1707020a021201050603010b060301031a06030313030f 90
    0x50221741c010700810003140c540d441091540c0d107003410000d0003035205142c0b89185102d040800010340c045c0503450045081c0c0002c0c0904003070034031070090010503103a040880c0d95105c0b140f03150b40002c1032100104100c03405800300d641c00ca405170741d0a1560682d683c0205070940d00039407180d0108c642e911454002d020850070320340b0002d042500c4000602c4440003c032681c0380c80600003e88103400003c08190ba02e40241c4c4031400400d0003030028041e0b0310f0a0382d00c40e41c0840fa40c040c1c5c44946810241c1c102000c2c50301c0d02c2044180e0b082c3c0301292804040004080c90000e148103068240c8071001c22000500350380300000b0300f020901c0340d1f0000c20409100d2900424a01da2502c2500640d4401c0c85444078068014147d0086912100c440c01066510844103d2501d4407107007000e034100e8144154026680b5064220354071440080c0c000340911010001405502e10003440090018080820b4030030012604146503500300100034102ca0510381201c2c0c12440b1800d0903031007103880f591800352417820007080800813 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77911449 1250 77910199 77910227
    0x1110d0f050405030711180c03060405070807080c161e05010606090b0306010305040f02270105030a02030c04020a0e1305060a0b0307120b1504060203030f09010225020a030f0503070201 81
    0x34801c07800c01d950b6a40d568010708000400000003940c0b4921641c80d11051540d01511100c41507034241851540c00500d640151801ea002d51705020008030010300a003545402140301d0342c1c40111355039070100442940d0b04042e0820381c10034918606000415110754452800d04041e40c0c01c40300c40c40003803134141e0840340a40c1c482013f01c1802081041046a644107581d801082801c0219040da51440c08245450580300020b500c80921f8041d003451030901148910080d01016807004966282c40825642d00a0380c100254194000300c1204400d040c140c0260600d06414186640000c103020005400c0900d00c100030358200b81c1d0b41041000d1031404a46220013002c1e41140e030791030f41c14195001000e00c100c20303140100c1e003519104080c036261103010071244184004034074103441e86c3c0c5403c0025125030055134403003044a08400451a5000e044c4210340000344084c00f50981c1e09a4000c100410990311501660300c0504280008040754800101141c3c09204501175075540c0400e10001d000110f5002d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77912699 1250 77911449 77911451
    0x102040611070e070f0309021c05010203040210031109400c050a0e090618090304030c3305040b0a170f0f06040b0429181614090301110d0f 61
    0xd000c141e85c1c01200340c80b1071018601c2c010071101d00c6400444e5002207841d072098040c05510030070381d05001e010750103180103c0c42100c06103a0100c1904003101600d42c2400551140003041040241e03d180942001b01845268400c0d40e08080d98245042c2c10075801c2250028009180e82e5140d000c0500c5206080004886050072814003043c200000d1200110981c0306000e0078501d004640c1c542c3d52942d01088601402030007007024034041d140907072280c009200444a040503030704081001c90b80019a1060040880110010107541100400d034000032a020801444410400818001e00900061814207050b444200c081d188802107001c1c1d00400810704040010380505125100d82c4c420032441e08408201c0b004141d540071040000c0c01801d05020215020485816001110350000020482440304495207682c8140311481103060510803a925244144204140008180034004055036041194400c1c0d0500301c03040082400c441c44c41200c3c02c60744001080840b80680b950080301004540808 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77913949 1250 77912699 77912701
    0x30a0809070b0307031d0604060b03010605090411010e2404031109061008070504050603040f05010c05031005100909380109090b040212040b040201080c07030f0807030e0102040611070e 81
    0x70041070f01000c0e0101041644400010a00e0f03400d68000890642510040d00c004c1d052614002006085484401d4001d508101c40014145085100e8520481c3c1090951903c00254001101e00034001d11050f544800c401456081611203000e4014040c4100d00419596500b90b081004000a1001800d4400e40e2000304000c0c840d110200141c07200c4d2203a041207007103a11740d614261003601035504416046039000c0100020b0104941506c1c0045006500030003202101e404201e44605c4200c641c01030302002608100650308118991030412403051800740e02c45a1109090380641d107100c45940000c40c038504051309814501c00800d4081c04001c0200b041903007000d000a094035130540f060010141c0d490300340501c0c81e251b41e01200c1c1c4a00074049400e00c146882d150140002e002a601a070010f0311030704c0000c0300c00340d4078022a6025074150300d40305d038147c01c40d140440361803000402c1c1004254540074140c0180500f400948060541900ca0400303801d1650100d526011803035200c0542807070124 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77915199 1250 77913949 77913959
    0xe100225030e0108070e0411040f060306030218071418030106050f0117060a05150d0b0105040b0405061c05011706100b0a0503041a0112030305060909031b0c040e030a080907 76
    0x4102d100c9804803c0c00d00d40c0f801e566000c0151011000d003040f154100d0b0030006419840940d000c0104255040440c80403c04d40d12903c040303003103428500000b5040342c40a0007103040400400c0b1010340c400030707901d4a0900d109004541c0e0020f41c01c05a1182240c10042d0702d1102c1d80d00e001c0c081c0202800080e200d00750191000c400080048140108038007441000801084c41600e80a0154000d484040e09a070003102c0305d800b5007440c039802030310710810062030270590400641c03051084904032244260210708090404040014540c44940700261100400090f25200d144a005103802003c641041040c1d00b032102400030304044006004a802e031075061005d02c00c04168809680c600021407a2481c1c40f6030b036030301d40740c400205845100060690000000181c5a41c0d45290404081c4603980601c0103440310403d21407240001e4919100c5500107010701e4404d80c0e0524600c05907404100c00300ca084091160100b0100c849016881c0429000050072440040d00521803681040c61a801001080c1c500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77916449 1250 77915199 77915207
    0x610080702060606160219081c050403020402030c130e09070501020307082506060305010204090f020903070501080a020f03011211030a0506010308090604030b070e240d0f0e10022503 80
    0x300140c0c0f04031030214180790400705507101e41c5d803681d6014010b038240400700540780520300d540d80301b111418890b6050300c0e551030400340c0b01180703a1080c640f20281820f00710b0703080201a41004080000c6903c09000d0900500c440301d400c01e00815840290113480d081c00703000e050070140160810342c1503600801804000840203030455000c000a0704400d0401c58408039030496103255120054441c6080000102c01d020046d0300500403950748240401014840c0f46101003079019903c0350300d5054200c01410071242d409100c4642e8040068000140b40ca0009800c5010315002a0081072100c00c000c0004010410003e02100021000300d004001b90012541d074195101814003004241c02c10101d0091072541307031042600c0c084c503071000d00c7c100076107800d110080480440c1d940d5a40709444e21100000c3c218001d84900c0d05107100740c50b01c0c2c0c0c82e01240e40c1c507040280c820f01040c04405599000e00f110046018800b004070070002d1b1748056900ca988580b80700b04038000800748814840c2d5034042d40002500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77917699 1250 77916449 77916451
    0x5040e0103020d11120f01060608090d08070905100909050604020408070b0d02090904110901240e06070209040b04060f050606070b040c0509070c03081b071b08030a08061008070206 79
    0xc110344001e00302c0f1642c500004189201d510240e08200e01c0c00542c03c90310804104c1c0c0c0804403401c40200011682c0b074008569420f004e036103030144c0341c01c0342c5542584540b0802d003040d400030b1941840c0908583e01c2021400c0c1d0400441110b001507005030091008401c64080d40d5004101110154241070421080c641c0f01c2c0c8032440b03a404070080014400890580b190166450110000c12240261500e824940030007408080708601c114200710001c2102c0c10108100050031004047c400000b40e050701d0107852807800c7c040425030004080c441100107946030708001c1c4c8030740c1c8540b180e60840e080a02e00142174800c2c44107001800ea0505041110f15124031060754080e507004549150952920f0030454180e90090304a1900301d1408000c111115400c0f8041b00501071103a034800c845540c03980030b98894954040743d98450400d08110503004155403030783c51100483c0c2e0310342581e40255118130341c6207141d1084040d0320128041c0c90822140345000000c0c1c0c962003405041603c41c0b4a01140000d460ba10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77918949 1250 77917699 77917703
    0x8060403170403030f15030506072c1c060c12060e24040501080c0102100203091209060d060f14040e060a110904020403051005060a080307060f0e03030406060509010605040e0103 78
    0x41c1e41030015040c503100f50000a283c41c6101d0301003200e0010141c41c103102200358042034820344260000320700410f218801200309000d48002c40d00c0710380040049001d80246c001c0c04c0540c404021400b041c821405150a0003407035215480002c1d03043c6110300041c2608401700a40383c0707000d142072400c02a05004800c50740d03000c6042001810078042030b545004003a10443d00347d58100b450030001259500700080d00d200c2e064026000c0307402c2500e80c0c803441e00580c4801c543c83c031030540042030f6800e00c1050440c054040c0b01801807100c2d0614100d40c0c040c2c000c450b2a0340c080e00d640041c90004000c1c60316228000c9001c55030a032003e2080b1804048502e50b50140640740b020a59910782144903900412000d5410307e01000300195a16503807801c10a079104010b00d5030181c03942c64100410414034003910030300d048032014006107040505541b1303240000d007001d2039800f00f0991203411810303501c070b414001180308078850080020800c0c20001400002c51050300240c05103c010001030040362032160000303044075 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77920199 1250 77918949 77918987
    0xb0d020d020c03070b07090b07051e010b1009050f040203160c06021c05040605090102040608180304030212151812130e0408120a020708030c0d0617031308060403 71
    0x2000d6041400074032400461080b81d0001060050410034011082c2d0f006403403540c0c2e5008201d0302d4400040091203102c00080032640407040c070011000003200048500c8036608000a031441c01480440da1055400540b0380001d001420103101074070302916203d10440c02900c1c00c41c150700c0c0c5a154440c0c2c1d0030b21260003c0c1840a1450100100011070b0103ca040800407049403080000102d00784000d01010b1380c044034081e0800b4001240000140b01741c0f001c403102591014034070740b1612061024031840316003544840c00b04000200c0940c0350815543c1c03001030560700422200c10711000d200301c09074001e001e88490750f2140d0307041c0d08407030b2000901c1c00090981900050340d5080c0504504030701d500662203030600045450402051290040140c40d842d4013240c600313503540c0d40b4003601404a100710740000f0b1100c0401c0c004a111080b520f00948064500d00c0360000320262100c0c1d0382ca4040c812240003100980c000100140400b650103801001401520028141805d155801030400400c000e0020890703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77921449 1250 77920199 77920207
    0xd0615030204021903050c070807030c0c031a1503010603030e1201020c012c030c06070302032701020a0e03071203051312050703020406320f130212060a0b0d02 70
    0x6141848508402154000d200310760703410b040072203485560220030080c80801d10380707070000d1010000c032400c0322403035984460303034a01d0203607180d4080e504a00205025220304004810201c000341c545045402c9005114040c00788510f046007007a00580b1042e03000c0da0107641440003c20000380c10400b505180c0600310303500342800801846080c024002d01250b07040943c01d104040003240020aa80c99040b03519060403a00c034842c1131003466403485500ca411003280c1c0a03070001081c00e8404e902440d00f0100c2003020030100c0c031240c64103007100c40b4000107100059500243c90700350982c2166400c20541800e8000d05007803032034010310f04001000d11602809022000414060480ca02c40704e00d00a0802c0b025540404240313420290390718190360008032700884ca0a031010462000e211402d40c08171801c0301c0404510308140507000040d04a00174940c0e041182540709901c0703079a03880e40341c03107024804110050715007041901c151040080604064040c140010090200c28030140440b0b010441d40b02003d40e903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77922699 1250 77921449 77921471
    0xe150a0603020a05130e060907020d050d0c0903080d15050a0303090b1b0706020c0a0603020c06070f020c1e040f02070515040f170c07061e03050a020d02031602010e0109020d06 77
    0x345c2c4960041d001c1601449840400c403003100a6074507014007001d81d011030700c5960791441aa900e00105480b4408650203102824010303140307410516016240d4540360001d207640350f41c2c0400c5a004598840011500c560b000030f2544004020140142411221203101d507285840281c0031410f54004d000350b40c0c41c001040024510b030f01071001c00e40c031682c13003c981c5001d40c0e6050003512004ca0041d1640724000d102000200c1900c2802552041c0180364054451382d10b07840c0055801c0042c44400b4003c1d4001e454000200f9508c0d441050090300483d0707050460101c0241c00c200803200158aa0740c5c2c0540706002c7c0c040072443c00501901c0c030194145505029440c1c904201440d1650848010088040102d24900e40612a13001c3d0507a07911300c03421250b10303030385845003035a80307040d40341b605115852424801c0009911036080150446c4407200300503c0c00c0d41c01200541030364801c03a1003941a00c140003a00000950910a9400c281c10500080000c04029400103880c150b1060000d1302064841c490000c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77923949 1250 77922699 77922707
    0x10e0d140703080c0f0622050111040b04050a050303040f03080c10110904050a090b0c400b0a050702100509030607030501080d080c030a050c0d060308040e150a0603020a 74
    0x4500103900c400c84009940e24a4a01190f510802c3d0f40304242c0100d459102e000c0c1c0001501ea80204103184500180312100e1040d0000840c40381c02c00d685a6495040004d121030074080248064074100034240c3d0780c0c2e402d0505000ca8282d26920550082c2d204000401c10b0316005050349043c0e9904c9803200b0b40d65055400414680000f04c6002020f0606e00f842003184501113100a055000046d0703000e10a555869810b0002c880366005d0140529291100090110b004900202205600040c0022034204d1001450740c03c03107001c1e510180000501480496070300600501c01d80144047c0400500c1e081c0d02c02c400511034099440000c0c0201694104140118003502c10786a0ba10000f03002c8a0702c40c036040000501402003803050300c019001e103562010061b4401d00142e480350b074a010200f07107103031600801c8800401008040086103036082c0400c03005d01e00c2c1401004015801003040d1b40c2c4981c141444040503e40140c0150a41d8007181080d0307480c0e131100d03440e44046030b400317090041c1c846012038000c4e6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77925199 1250 77923949 77923973
    0x31e0705030406020a110f0f0f040207050105040c030308101809060605040f1a03030a17060103061d01030516080a020405040303110c010906140907090c140705150601030b010e0d 78
    0x9065000c040b0700420700d50390003d16860417074080c0074800c4917028007200b03020440c0c10114101d500a540b00c900310181c1d00b0300800e100e590300c0002d0001854030140d903d40300d00b140d030300b0f640c2222000c2c1001d07000c01c203041d03010b045241c108034501022800b2501e0901303000c0c03d14041c02031601d62035458a62000a001c19548504014940548140034011051610200070301115060081c10781c1d00c00071140841c100003042c1d030b50700c401315124400019142c0640d8241c80000601c1d6504041d04c590000c212144084560880c034996844038000341d504514045080c2a03d440c007050908a46103410444003000041c4642d00c0d41d0151030001d429100d60901f18041c29a0200c0a4a110000589908100fa0541c08511442c1c003809042109060034000348041c1341c0160703112a4071754016801800500001c0d8055801e25541e07043c00b000003400307101c0c802466080b0030b20036101900038590801007110804a015800002460300308100c40381b030307070010344014602c0030800e0041944c080d44500b00070f03500c0c20074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77926449 1250 77925199 77925203
    0x60411040b19050405060a03020306030a050102070f030219110909120307020a1502090603060613030210030506120f0601060e120f0c01090608090c09070509100f09080609031e07 78
    0x119521600c9040351091548501c44100880e80c00d0b14000400c14850400e4800752400100814605807031501d044010390405440943c2c035000728545000069402d10041100a1040e81d4950a41442d0b05001c0e040c46800c01c14800035911580c0c034440050ba210341c2001d0071400448282d026078840c2e641c1203207030280b1100c00e40c11080000040c025001d40000c0c2d140d01c01e80c4100240e01680c1090781c500400e078080d8408882d00b14a081c000b103106441c100300507041200310b44c01c69500b400c0c0c0d030750005103107105016400c10100307665030306202290501180381c624144000d8000d1600c3c13081348e1840341e070b1442d052048908004058080145aa40303004c200c1c0c5c4041030b02c4003140d04c032040d11b41d02103072501d0001e0301d4240460744105001a91078000d40700c00b44900b004101414181d180c07003003403203a5020018030741000c0250802100d24140e0345c0800017840401c1da651380f407451070100f0101030a8811550004c1c0c1c4264000f208103c039180c8000700f00d50704d030a00080445020490f541245c02c0601034a400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77927699 1250 77926449 77926481
    0x70201090b010e060a0b1e0901120501030b04110d02010e01110c03031207090509071707170f0601090816050409020607170a0e0d0302030901080c1620040b0d0b0604 72
    0x10b4920707030384003500380203500032502d83e0340086c0da400508180388200d11380030102e03032075402d01e0103803201400018111402041c10518024041c0003804000c0707070300136041100d403841d100c414401807091081d070b60041d01000b074414100034080ca03000a81005141341c0245d04112001099130b5502d0820f000d01c5101c29400303821680c4441400d5103659400310200e03150700002d8014040001c0903d01640c3d482c5c0a4078990703c3e28800904949408007000f02c0007050a0b0034404004092010040d46009480c801c030050032a1903042d0030010001040c03e2810707448640d8940c845450030340041c000050140c21241d00311000200e201c89803010540501038114003a01c55002d101110841102e0400107104002d1265070f40740d115600c010400410425403400940180e105000d242d9295008160641c1c101114585072428001e40304656143e4084101c02110342000040400c0446004141e419000d000e04403018032002c0000d002240040c001c04e00e01405d0130740c59501240c22900c5a074000404841c4440c0c03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77928949 1250 77927699 77927701
    0x305280b0406030f14060402060f070c12030f020114060f06070203010906020f04030c0605190f02010b120d080606030103020306070c0f08030403170a060b0301120c0b0703091a0406090e070201090b 86
    0x504d40d0142200d400f0555001c00c40c00140d500e41340300030807600e00c02d40d402072415080c09050410b0b010b55400111048503d0070710400045600c101034286029410720039542c40c5803840401d2802406d5812040c141010b840b15142441501d03601c0c003d400c61040d1044d1303117054845504e070000901400c0c0c040e601030170041c40041c000004003179980c020b10a41e4020b10f040c44a0039580c0c4c0c42200e81d441401240300241b220419544600b500c40c02c444a10607001d44004070305c004508002800640b00da0145280c0d540c000088449401d42224400303600a108031166415580b6640109880341001840ea1003003083c40c03001d80c07082102041c0e00c4450030341c000b034505e034070f074541440c0c06040f0726055040983c910b1850f40004211148038081c0c007059905040105056904e0101c40344000381e400c01d01243c07865100940400c048100700007810041d0302958481e0130552905075404085040f02540f607030341520803c001d1140c0d940000352202255408000780c070140d503078424200e0040c00c140c2d400800081082d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77930199 1250 77928949 77928953
    0x30a0c051006030309080f060910050604091203020a030606051c050c0403200f030609070e0601050c03030a060e070c050307150b130608010c02030c0c0609010201090507080f07060305280b040603 85
    0x20380030606440c0440100c2e407100800340c1f242c965030202282c031403100340e10003400000c1c20162504450b402c10806000800e902d90541d841003c01e4910380e41c03420010b07078080f5060a034a54540a818020710b4541000b520b006c441d001d9202d0342200010305440d00946440c0400d51a480650071940155080080306400403040049042d80200740034409100b002217265628162502149482c0107110000082c00613920301007030442e03030b000300408042c1404000d22520500d084240000c622806031940001004d600300210041c107000064100c4080043c51a8640c00050001044035009904460000303411750007480d8450107002900d000981011408242105041054101c1020303140041c00074030540303004500803696801080380d440b085601c01c0d4151011424580000c000b0b940042c0b0001c550701c402e50322414a00b41e600e92051100342d01915000285080034081803025050300d15042c4400c0c00c040201e022105407e050f100c5540d50141205020146280d10040c0303c0e04000d0b10034024180d480c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77931449 1250 77930199 77930207
    0x7140307060e06150d0611092e0c03050d05060a031208070201061403030405010806060c0105090601031202071404050717090a0303060b03010b07031d04060308031602010509030a0c0510060303 84
    0x40c800a0b10b20a2801041d5401081503840c000c906010784011801031094980501030a1300c0c607100d681d4044100280c0055844c5d09a21460715035030306072021032205c0c84030740302401350000340c040000300100031900c1c80002c1c0c0d01c4030484111403409803012809480e03113000a140010303580e100504042a0303440c00160580c111031580d1044c040b640080082e1a07898890303510b0784d017042021a51503001008240401d40c0100800e503080100500b8042c1400400c514482c2107d02c10780e14158103501280040040044910442107101ca031031014044251400c0701395000c00c0b6080a029215a49420010b40700612404c000380241080025100160400c04030070f0361500c18485082d0300183c1045d0020400035240c1080342e049541800707031186850310319101104d1140e040960040044002c11604c0581c1d69140142005140200000e0741d49084c00700e4801450380b0001005420359040000300585a003021060b01c944c0d03215802d01c0310300b02060703140071410302a5407800c44400518203130020040c50b80c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77932699 1250 77931449 77931461
    0x60e040f060e0604031e0507020904080318030a050412050a0605101806080607050f120f0a0c0c030801030809040e0102130801141918051c0f0912080714030706 70
    0x9000100400c602046829403601c000f11001740100700c150655180c60b030f00140300610090f00c0c51418a04020841d80000e505e050162000d640d030f41400300070301c205090400110341c000c524410080d4580480c01e503000d003a6004030301c01e12500300c54804008052100510400d043c10340d212001f0040b500d4003903403500c0c2400450003240d940800b209042c06110040b4400d031001d0300c3c00b4200400b001d45d1801d2040b9005c0e8003800801008800502000a0300e03045a8a13060040041d0f4805095500e0b009a400c0110380b9420181e40422038610b24980102c0d0b000340b04541540c3d0010180c651f110b0680010030007038034100354607841030344c400949a408000e0760b0744403801b40c40d040c030700034006110500d160503100c0409848018607440c8500b020017030b800c12503204426004542202d9100507580c1d4933030300d05000e00f445042e0840c118816410104c50352207a02d090428045081c2000000c0c1001c1049030b840301c10304c000400c2e00c6400182d0600b400030050399107020800300e034202ca40e0380d031181c60400d0140c20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77933949 1250 77932699 77932703
    0x303090b01060f022104030215030403080604060302090f06030102091309050616050a05090a09020f0a1206140f0402040306090f0510060605070602090a03050105100e1506091201060e040f 82
    0x145480c00800c20703a109a01025800c602640200300000400094000d8aa0740c10549010f003002000b0000c01a110702e01180a8042d408098a0301c0389007904025100300c0c00148403500c1123241c10780520060342c0d0700f140c06401c14100d0068091540d43d00d40881d00901c100800c50fa8880d08004020b8140c141941103010462703c03d005562264175011095561480c5207031003400030a5080c03105a2403180704801500c140c01c00100405d10080d5200d40b06003c03a0700501030001103020000b01d0030310041e0080040ca11800300b803074080080703d01c0c02d008d080c80d840c52050118851300488590800740e44c1d96404ac1e501964108804003c103840c45d14200c10012103581c0d080700c844c0500d803103078400d680d00c03482039004480090719611b1600030f603940d810009512813040b690f8407041a00001c40865000d10625100340302008070750030b826040c420441540c101c010101e01d80d40a0f90703610030409440300c0050f14003152080c0e5230074001c100681c540c2409010b1640021008010020030030083c00400740c0b031408168 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77935199 1250 77933949 77933963
    0x90109060608010905060624180108100e0a090201201e030c06071b15020a020c24130905131101020610032d05030903011401030c0302090a0f09030309 66
    0x30303558900c4a400d8039202e040242c01768000707070001401818160f5146980d8802110090750a0140380c5030020150003810b029003c1f03480f51005090343d0750700286031903040303888406d101203500d281884031070951400030080c9d0811920f030b088000459005c1d800b09003a8001103000f480c0e00d07030032203440c184d0340c0c10031286405981f140b8158414110a400b10890b40c0e0001010050003140d520310078166103441aa405041060080f030861704085505900d203055022000320000d85d079820380840017850700140d0b540c2544900da4018180d680c0c1041000300054910800010b980c88104245804400380c07441c0d40402e00e414100b800b0070419500c0858401c2c006440303170012242c0003110300e00482e0349440c1150110074001b4900001c1c004540c1080340d940681d2503a610b182c80f0a40c1e10459801c0301540d1042c121010340c03012502c640b91346400c0c02861034071140e2000034000d035899516264840e40ca1803102074047c40c14013000c2025160103800403100000566010300445103245001002001640c00a03204a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77936449 1250 77935199 77935211
    0x30503032a030c0304170a03090b011a03011203030e1c1b1a0a020d09320d0c0501090602030c090a0605030702031b25060e0405010f030609110909010906 67
    0x700c038610941d041580c40103800c503411a80c858110106940c005003081e00d03810b6480d030300c400ca40d04460004221a0a07103950218091025113400b0341c2415040c1c200c0c00e031a10381c041d050207810024400352811141c8038584c80c400d201c114102a0000c05201d800f40d01039000f04031070300104100e4448103c0c8098101e586003480b25001c0306071503000001d907003030040500da40304410a41701c03044c4629490704080d540781e0042c501121007200d1422107401c120201c0760000c100c9600d00c480c210300003110015030b844200641429072030700c02c019210300b1424544007e1007a070481c00424044250302c20800a0b602040c215568101920582910b4101c0007642d4032506c020b03180412201d201d103090b00d0040c20b09070000e50518030352810480000340024514040ca2058942560f280c21171b102c4c0d100800d20003220014186800d2180082008158919486c000c90805c0c004000b401e40e513503c0c00b0110780c0c01140004070a4410314128480500c8090003951000101043c041030880c19801001850703c104020030007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77937699 1250 77936449 77936491
    0xf0507060806041104140a1509080f07030b220b07030501090c02280614010b0c07080f030406032a021e0105040206090405090f0102030408070b0c03090a110103020c0703050303 77
    0x380c071032912822044d07030030500c0b0030004d06500780016181c19600620306000e041d1114001d1920400d0000d60000150100504011928040c400c00b00980c070080042c1241504640724480d00c0036020b080c00c1590b070034080c06c00584902c14000c1d82900f40e4003000c543c9560506400c000c001d40028040c0704a99450080200c82c510b000084c4500030009109a00c2e207a45a0541412508003c0207070070f07180c41e9283c0444002064091001c01d010300313905032015480c2c020b99200700e4903003d030b95004000d8070b900c40c00c0b20300c103a10400015502203840b42d24000c41c0c03c2c07502d030f4446000340c081c929188110401c20501100e965402091303c1700080d0031010701d410744d0b14100b24554240c1da0b050780d0294100504201a02d6507081503002940d1200c2190212081e4200ea1000503089a00484054940c108089480d60403c045190b10580024000b0062070a41c100540040d86a21040174010401030b607a00c250b2841380d0103030301699461400c00040c0d50409130380307003410390f1a54411240c1c540034510310725540309 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77938949 1250 77937699 77937701
    0x7060f060e090a03021f0906020d02040f08070b0301150e030f0c122806060f0e090c010c03320417060601110307150b0a09020d0b0906030a0308130f050706080604 71
    0x420f0700e4141d4020480341c5e0880701c2d00c0002c0703105100c04050190726108000c000c55014001003848140c0e150700182d46a2402c4480303d400051f60700803182c02c3d0441417003004642402400c2c1c034150364104009181c041c00c1ea000c180c400d4244120550342502601080003244030021500350310340e11040d03403218030807003502845680300c101440658a44a0311254440e801115140482c10341a03c180c6000800365100d024106002c0d49560250300d581031461708000e0700850034003441c40d04000a0801c80e41d2411240d4010307044d413418194005820f403143d03034030042c404400c201680e000c550b00140d4644c0c0c3c03905c034144044100b131141c500b02d40a1240202042c01540f04100000419040401071070810310b1940d00c1c9001c010310f0344080c1d107907651113000701c1d01075940d10f0b400c9070b0061410070401aa01c1121050103029030b00301550341c0740301e00a550100041a10041500c510095251900f80020f036249824082d00c140c110380080e001c00058407112081000026078203080d00c80c6030f201d9803030640d101005c007c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77940199 1250 77938949 77938963
    0x1b03060d0f14010204080f010608010b0108010b0c07030c08030c07050a0f05060307090905070c050c090c1b0f03030f1e01060c1202031606150b0306060702010c0807060f060e09 77
    0x2a0030006059045000c14071100c030360a6070754460050000c1e904111400c0909a8215030400c204d41d80041c2c81074443c8020900ca60401007100800034010340707102400280040710148100c0303010140004000c080d4401c10b02c50340d4040d550000b8002000d548540da101c1e541e0300040650f9440c2e101d4110086100d2a0050101d001c0b46c000440890040d4203150502c180c540010303003004140102144040b0740f50202d4040c40307126180f1540d0f0340300040c455007856807070002c070300e4003d6020302840750a01c65003411807004c80303c00d18400104040d0710b0034156002441d203000f0941510680c00003200388810190034041d001e0184441042c007400915100c02c030003907102003c0c403407500480d05502c1e090f0001a07004070030021044803401620b09000d40640e40d00e8490244440c2180c0159891451402e4941862265000380580d581064114540034010501074801c6e44000b07818000140c06000410405600321050b46611903c00e10079086120a502c01034082d502070038242c0c4600038009041c0c100c00052203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77941449 1250 77940199 77940211
    0x1020d1e0b0f090a0207080d060621020a0915050f0403080c120418051e0a0c031b020c0f0307051302070501061a031b0d0204030b1501031803050a0c0b070203031b03 72
    0xd02920384107004c9009500201080b05c4609003804103424841c41e500c07910005000030b499280340380c0000c060b000c44940807000065603107407060084083c1950b10490b5034080d80c04498550544400345802560035003e10a0b0b1100817207400203012003045840303405030200c0c2809034100e038030841d4081d01d24445405940100d450a2400c103035102c14124958000b550040e00c2c845815140d0308500d01c00840e0300b9421034950b46250340f00d10a182411341e041c0324404a124544807003a5601e54a440001d40799008440494410b402e4243d9500b06981d0611440000b048000c002e007030400b00404052000e9004144159855461702d0b40000c5d6440e00a05c0907201c0042861619282d5501c440707200b00c094030000d105500ea070302c040c0000c0880510500c004e2000e18001c07407525500f46409070301384050510840b205410141040c0903007180440c004844000a980360408a0700e41080d000200d40741101504003610341c0000400340850789030040001c0d8040c40303c0b9642d58002034090002d0803064030080c0d900d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77942699 1250 77941449 77941459
    0xc0307120c02030d18090c0c0507053304121a0601080606030c0c0703080310080f0f031c0b030a0c090506041a0103180203060117060108010504050c0409030201020d1e0b0f 75
    0x5042d00d4140300e000c0703480070035800000e8101050703101d0121b501113030140c0c4540408140101c1109080c81010449507000b082c04868500d4098600d00d12464030410b101159406011105825011900400280c0d030182c00507100c201c091001c2828091040c115a1404103a0011610041101544148040e610440d0080e2202c0d02d107448100010000d68080007406500740681c401c04800640600029401120045540b041301ca080c60019410000c540619081d1a0b21629244940c3e0308048262415130b0001408034600c020020009400303001c00008450303050040202a8003000a0003200381c0c142c0c0c0c2e9000003000950780f41400d02086443c090f001e05502c2010307003076880707456120f5080320044660418500c0f10300d040d05d0380843d00e403030820703040310041511403500f02d540302808220f0700d0300410f080b1000303000710300b4292542c58540407914101400703203440d880311a0600d03000b50126000e00b04511410889035002c260502c0b84810101d100c502190700300002628940791405500c6560100245 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77943949 1250 77942699 77942713
    0xc1201150e060a020a050106060809070509090c010503060a08070608070801171510030803090a110306040f020f01110a060609060b090a151b0305030603060f010e060f01030e030c0307120c0203 84
    0x8100c0360f03030880b960301e5045200e40062000007810a0252500401994841c028241490451a030400c0b54036000300f4000c903000e400704030014000007010502a5020300f4115902d840e100080390351a045a00200014403521000080d26644102d490b8480c0b005641c88099a2340c0340d80383d03001e80440070316030f104080d03105c0602c4001001c2c003000c880b500301604211012289030741c0d658200b0203410445402969412a060582c2480060460801d02150031406480685845d0f541d0840000900c031010780114950000c05050b03034001c140b16440c040c00b0b54203c410151081ca0f089015218a015201c1032a05004c2c00140b180164800d0701c0529500030f2529960908290800c01000c2e040c2c00d0079402c12428140307405444071504078021101303020381d480c0c03682e80c54003405061034500064007840c20083c64000410400300040755090b0000000c41da200120075a00c00100d024040c03190084040380070000c2c040c15102000002004207510580c50780786407091410040e21140303910384010b5015040300c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77945199 1250 77943949 77943977
    0x203090114042304380310050a0911030d090306050a020f070c0317030c03010303211506141201060809100f02180d030905040c0c05060c120115 63
    0x10400000711950010a6080558403041040d1500800850f180402251071400000741081d021701c050308240296925400c00320310050641a02c10415280d104103184000340a9941c1e0a00442840e031110000c140001c0c2130000540e0010212002c0880da00500030b03000c59140c2c02d02140a08100406850b04081c40389103403188000303828014030f900046542002411034811400c005010518045c0c0c0c4160555415071070410701c01152001d119070315610070f000700810340400c0c0c42240c0c10750364103152103403405040e0706c941e803649180070311400d986c2c600f84055a08a0300d0320a440201320381490b900d8004d023050801040215114084000f60411415001400101d01030210b09401005940032640c40200c060000000c481001c003002501a4000450103503072000315480002000003111010030325800c1da80c01a01400e45072060500560302e8416450400e4000c09035401c00350b0304035080d038040307240c5101100c4060380300403655241010310400208081122018181c5c900100d5100d0001e06643c0c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77946449 1250 77945199 77945207
    0x5090c09060d050703020909070618261516020106060804020607060c050d0903020606010f02010e0601030201080a09050604050309120f061f1d1012020102150618130506010504060602030901 83
    0x4040b040d90507108150000006881d42c1003010b2099a603000078051150800100401500391071000d800180180c40742442100303840200107420001480c080c40c0d4074007540440b181025030142c00150b04000001c10000c4220040c84910100e20866000b001701d152204d0059a034510103440c06900031100f0f01180c00060b10035030044980d0001400e0150812803c81c1081d029240910001c400582184041c000c4950f0014246007403841d0f02d0000f40306200c0d050340c1c038030754550051001a041021030030100b01c121405900803d00c0c1c54008090341c08901c1c003801c0040d0b07607078410103009e0300502c10210403c11031000480e6041c08241244040e0800b51900200c0004001c0f50405d00800c103401d40c8000101c000c0c503003014414595801c040c10115140c03800e581484080c85a01c06401040c000b10002c00607079003c90004820f04080307900e43c40759182c00011619002c09801c0007900700d0548802c0c811a4052402d0400c61184100210b031a26a200d00038001925114030900300964010700140c8925070003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77947699 1250 77946449 77946469
    0x5070906140a020319030e0601050d0203030d110c010c0c0c050901030503030a0c05190201141b0a050715061805090a020d1e02190302011805060f0a020102040f0608060405090c0906 79
    0x2c144100d0b4100710310365005529001e800162800825a2540880b002c0c0205001080c0144001c03183d90044190a0b0086034881c03050000d066011680c039400fa12030501c0030001e90b030035211200700800c55441c42e05005806d1841c076507410b5031091180301001982d407410400c03082c1600d50044c0514115103407119084050040ca07119a0300340314050107200c04901010903648042c44456002240c800e000b1020002880000740c104110443c2c010440c480660241c01154881c0029185c483e03500c41082c201040980303101c9d04282000d6041003000a032030a0501c583c1c1080c0c0780d00803020040f035114160010780d2285a810001d41260700d410b04c03240400e828099100100109a401c061040b865900192444400c034005041c00a4500418015564803501d0404940f1001c4040e050f12810800010101c1c0030342d07010881c50000020f0303030142061003034041e1002807613425035015070591600005041c20404407207082c003c40c0340000050b8000030000c0c964040002c003402c000c030244c403007805000310051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77948949 1250 77947699 77947717
    0x3040807080a020a060f050703050906070e01140d02070302010e070f050d02011d0406030605190b0d020904020a0b0a090317121503071d06100906080c031009150501030507090614 78
    0x207002c85400440c11714010050400b03074020740040e4500d4118000b8086800207852071685a000f0010000300603004140201010001d00700000824400c0d110710301c0600c50b40040c0b482c030900208000c8101070301500300420381c512100c00e5411043d12043d002c010400d45108450f484240f50082201650140d4105140c3d501c91040304910801d4000200c0c0070307507000760b100312815030762002000000344900110510303000c60703594140040780d2400300092070003000480180c03103043c921000c5030071541c803111414001d11501d02d0701c42d00d0300303201d840241c20521244801ea58000443d4003400034a090b2170300315480340b0f050031000c1102d40c5550035141c0f44450840b000540500c240c0b035020913140c82900c0c01100d010b029196118462401d8804d21100e2882043c400050100f82442440310503000346840b81d22920742c81d0707420b4903695102d0010302c5250030f81d800901d00c1460002140d046450f944d244100740c0c0c0083e20300340a1902c0305070b412101d0036594407a000006a03203513080078848900d8401004465 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77950199 1250 77948949 77948953
    0xf04030203010207050703021009050f13140f060906310b0a0e0109060f030209010e06040902090702061006022d0a0b070914040212071101060315090c08010203040807080a02 76
    0x5a2a980800d0032a484010183c9007070748100c500300218501039040c5104031400e494541265071810001c80ca0b040000c0e10700b01d10800804074503900e64032159000103000c07015483c2074500b50600c10b40c0100001000d5911500070303801c0c000000e105080140845446d007043d46107c2c82c4000405513000350710300c481c100711000607844503410540da95500310340c000a8410340b0103902687d4580300415040307501544c0660b45109104008201603580c400e004c5044450007940303d1007030742e204c0001900910341139100941c440540d106004109500140d51449898011480d05e000c6032a520140c4c2d4400c01100541c0f0348441c14071100c2c1058141c8005614000e1004040707801d403990b19502e580c0088400c8800354001042d6003000c102c502002c200f0700342c00107020f8800710b113030003590444130108200c0286020140a000d100c500071a2600350300c101e0046400c10304a043c0c0070f602842c001e003d0005004151039080c03c2e10008160141c040c0700301c81c000c40d80410b000d454032501c1e503690f40c01d58000700903007002c0d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77951449 1250 77950199 77950207
    0x8040e0619060203040602010e0f06010612060803030f0114010c17070201050403060608030304120305130206180d06021c0b032d0604060b151314040204181d0604050709020f 76
    0x740044480c1d2001a0034241c01840d100c508201d0000e00b191080e10042074160301034044490700c0c42003c24000c0c1902d040e4035107a05a2144442014050085a484218107101c00000c1010f440d0a80c05000e0503240c038141700040031107422004441c1850a6034014104501e01c0028407802a0402e0003445c0d03451040c10a9401e055603600c0340c004480c0c0e80d034440c40a40d00b0000420040048441c00c0b40d00142e000e050402550030041107001000341c0014000b0b002d07000001c0d01c0b045003480c0c210b1422055400030a0400440102d280c0306010b50000000165a958020b805070203401e20340c0a036425608000e0700a0440320540c091005030303058000e40000c0b2003c4080c0c0751400e00704050141d00c2c07080d801003101080000c4100f0500003c0b03c5600e01c2c02148074408d1220640e0326040542010886d0300003181c4118450f1544001802841181d02c96042c40550210800c1500d605402000c2101c152400f2a1803143c17200100c0c90320340e0002c0710028060703041504184084a802d901901c00d03551141546800c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77952699 1250 77951449 77951479
    0x70b0307180905010303020c090702030f0f070206190e030c0d0f061404050a0b0c09010c020424140a0503030405090c070606050a030302010212010618120218040b0411060708040e06 79
    0x241c540e040702d1040e07601d5100500a044d0100000d00340e0400558603080707540780c8141d00070348a004020b510340e42101c1c0041c036000d08480c00300aa800c1c0b50380041010b030343c0e1400000c01e240c001061200203804a020140c942d5200d140c085104044040040c0c90070a20103a10380e034500b000306034410300b2929113544803000030040c41210a10703032080d0700c140b00a00710aa5035090601c108000140a11181c480c01c100300411a640803c10000c0107030b050364089074082429031148245c1d540308400b0074154a031401d0000f1040d00550b08030340f140b40152100c043c055141d509140e240d214500807580c20607120804540280d901c24001c0c4051405610b001030007503201d0f40000c2c1c0860b0f40350f2090740140e401140144000314800038450040c075090404101c00c5020080500c008a00303031180a0180a04610140542d103403008103c002140a4610342c05614161420184170346082e02d040d41c03a000e43d0801050782d41441c10072103855680083c040c41c101841c0400801e00e10700c0c0240005d030040310b00304408103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77953949 1250 77952699 77952737
    0x61103010f1403061509040614070c020111030408060403050d200304060507030603030e01180b1b16030f11040f0906020301050f0102030f0d02030601090305030d0605010f080603070b0307 82
    0x102804450744001826850718010619005460902c0c0d44207030865014450101007620719003802d0703c2c00313440f00341c103903961414101d0040c1000c00200070650103010800c2100c5600031074021005100741c07541868442e8038051300d5528003a81c01040410380c007400228011074010400b80200c0c019a8002007010b03643d140c16109041c00760152408020004002d1004006007030040d00d5000b10985020400d00e86035850040c0020000d203500381c103102014403503504c0300310440c688102418800ca034090307490101c095684c1491100ca80c3c02c035818010320f42000848004840d42604482d04402100b0b00000291102884480071051950380656241c0078140a200b07a4000d80c0e05050150382c0050703c3350f1601050041402c7c03c0711420f411900100090030085030b440c0291011666003100040e00ca685040050750864030980001d001c5100c0410502c4120000750810816103c007030761486c40820900c1c03c192540c0400760703030311541a0030050080c4907100498002c0d6900a81a00d00121031540e540c0000c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77955199 1250 77953949 77953951
    0x13090c1703270906180708100302120c040606170406020d1811120a0213020901030b0a090e0c040207021c170403050c0a0b07021c020a0f08030c07050102010204080316061103 76
    0x181c01000c034036144210b9142403003481d42e00800c20b40e2000f03401d91030380400d140704034030003001c240501030b2000110301010500422a0051a8003400c580c0300d081302c001480c0c0d510030840740b9580c411401c00790f003c03c0051080c0c1d810540492810903681841c1c5540d0744641c040c1d0402504484215550501c1f28103050307903441c14665640c082c0c0071404d0000340c95014898402c06003100148581d020703130201401a00c50100108100d00d401c040103880300d2000380102c028142051120384c0c4012220b0011507240350300c1d449560024040c808a881071960101440168000e051010b580900c01d0320b00410465158083c02a241380302d1000c0d0344a04a40943c07556841e0000d030410b0700e09130700511401d14a420103c3c03409018104428900e8100000c1da40080c1d255010790070510040c90303102c81210304648a5038403910181c5829103901c07610585800e449a540e820400031b42886125900380081c15500620840d03040d100d104019603e0200440c210310b00350110018101ca000e81c0e0351a41c0c03201c00000d20051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77956449 1250 77955199 77955247
    0x7150203070b130203010b040b10120e060915070305060901090c11160e0f01030809100908030a0302030703150602060a0b01020f0106060f09210303050c090a030302070513090c1703 79
    0x40f20402c6240103050840301321400c0c080c080c030301d42076034003c0a65601d41d0000410070146000d42c403481c580110340024001075240c03050948a481d00b480302d458804254090001c400d882c1010243d90b482004900361982503401b00d410460407001070107034950341d800a5510032414141525410741c403a40452800e42000701c090741d0f960282d041032003440070082d003550b00203500030320f0055507504607100c092052146c441c8031032048031000e400c01c400c1c4e4000e8099000a000040940b07844406150300a0003a510442e900c1000918122000d203400641d21405c0043d600f4aa000700503d80d200e0310000018014804050305511402c00c0b2154520024010a4054081a540c0c072007a13828903039020f03041500c141c00c9144030074106601c1c04903590000304024007207501403502241680b40c1c040a009140308501078240c022241e07110100901d43c000a00104840069070f9078206038a10703003114402c6400c6450300519040e0307880300230000c2d00c4c10409641e0070b90322541c040d01c0c5400000d000003089003150340740d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77957699 1250 77956449 77956471
    0x1614031e071806030b030c0f120102040b03010f05010f02060c0309070b040305030a020c121b060409020c060103020915011d03030c030d060e16020a0609080f0a0504090b010207030507150203070b 85
    0x1c5200000d080d803000c82c0100841c1c1400d2019510401c006501d405101044900602c10728003619002d98940003c1544405000000c541e120345400d0001340c143d01c00d010380709440701da00c0300c0081c05510546164031800788a030701612003038451000c0c1900c50380c00034155800c039126600012698503050381c000c10041d0700c904000c6903121100d038006800c091403005a50300c41c0744000b00102c0742c2e090104011041c5014004a82024110384002070100e00950308031301aa64808183c1d00072505001072141c0c1a01d00072202651955030302c1040800d2602011152800502058a4882414448281c0c60000c0300f0003000d030707410441e00e20300341403454100584c40324400740c8800c0b080001c0c280070010290441d00c207105021090360203844c0a135030350600c0d03103008180540c0d0360a0070050150510035104441c034464401c0c0c0d40c42200e2030b0020842d40190281d42416071a20061400710342c000212a0104e0303501a000d441c1c514608009003802c0d14141d00d030075040d80401c10085002907100740c15984104a20b000d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77958949 1250 77957699 77957717
    0x315040515010b0403030f120f0f0e071409040819080f010f0b03041202012a02100e07180209040507110c011701050d020310020d0b01081614031e07 65
    0x14001c0c81c000c9551a492119a410701c0140100b500030002c0b2000e0700c0e0181030180f078900200e00d040300c0e180e01c5202042001890300041002051582d0000c1c80d4403544640107003c220b45507070750652141d903281308181c8040d0742c0f01001903043c1040340d540c0d035100d07000b03020440c10649001100a14040100c000400055803c1c08024a5001a00407a03014140b042403030711059041034550b5034a880054000360014034400901c210042c800d41009501011540c0f280a406c5d0941c210745000c1c46644030300380c0243c00356011015800000780304000b060381184000308403552400000c0c0c3c00c824001840784035119020040f40c003480d1140d01500340140400d41e02d18a60041c0703084c50a041240320507515042101c01910341d00001c858540050642c0c5040711044013201036840000e14040c601c2102002e82e03400031402c205c2045c0c0f181d001216841d000e803915a0160385000e03c0303000c050f00c480460030210304400c021080c082707100f001442c2e0190b00c80141a000c1c150030031540c580e2050403103802c40050b507451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77960199 1250 77958949 77958953
    0x9060117010b13060302030d090308090103020c0f070b0c0f0c0307030f03050708130501030b010302070320160902040905060303071e030e03060906070e0a030c150216080102042108070b1005031504 86
    0x41c1d00e8030100f52905902c2785045030755045540c401c00f020b050402d80c01240c1400784900520848061140c50b0044600c42940d039846801140c215040b107203642e0046041900c5419008250b40c038212100a0284c0001403c60380c070300c10302c0303510741d03109504008081c841000003c5410004040c840300c215020b007034640c9031500040030350f410080d100781018010701c04600020340010161880035410203012120b903480014041c603084d643d6104144031000240005883c441e590300a0081e03441c0b0400c10f005503039480041c1036803849482d10041940c80040001140404211040d8584602c80e01d05402c01c00c0c1503500280c0340500550740b10075680c10503000d005007a03400c8140c400d04100d0503145640034034a0341d210351785490f40350310a40750842071401500c00342610038007408413900d69902e4103221040d00c0300401c900070b4107d03018000751228130000e4030724104113a4018203403a0341e01c43d00d0280390100310b03502d4080f405400390540304042503007c40811540e03010b010390501c0c03210390700e141c3c0081d02d007038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77961449 1250 77960199 77960203
    0x20703090807180f0b0d1103120a0302030412020d08010e060114040e10170709020c0c09011212030207080d020c0106050a091410080c010516020a0f080d020609060117010b1306030203 80
    0x7004d140000585050f06801c1d6035100c4c03489103000d2035005010b4550504c00100400d0408403000f0702d40c02e4102d0000303060b00202e9007542c051409a40600c1000c2610310a030b100036692107102e100c0c6c41f4081070340b0500400025401c0b4080942c0900189060080410880c0b500941d0342c01640128055180b101d0030480c0032651148100c0041c0050003082014401b040340c40d50b111905800358115454002400e50021501081400c898603000340180c00d256944001035826901108811980640c2c82e41d00c40000300e209000755140c081d04680346610301030b44185201c000b9440141d09549554892074001480c3d500c88420b0401049600b002040c51101741ca155450000010aa1520245544003e0090510020f47e214080e0400e0074900e81c0c4a214007000442440a090000e501092681001c204601001d00000403a504d01003103c0e4031000a01d02030341c944008507003a0380a6803000300108001e038600d0350380071140d503400000003070006032000200b922444c21903481071000341c884000300304508007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77962699 1250 77961449 77961461
    0xd1e0606090f0c0905010318020a0b0309061612180b07050a1404080703030305040c090e0706080c0a0806010806040f06080a11030607020601181b08060901050a0803030a02070309080718 81
    0x10b03050400510401c40e1000d880100f480c002c0d54101076546405280702d035044030074619165002840510030b00da603034030058a90703802111000300c107000b07020104469445207010301c220600a074940c940e0341c4e01d8807003281c401091809a410345149428014802042080e4a03450180840e5a1020340d1104104001341c8080c6504104500341c010802c0100042100461a201920391615011803a61640d0134104680c83c40c0b0341140c07640d186403c1c2d12540840001036182c040311000d80f00ea043c01c0d581c1e407100c14a00e005000d03501c4017081011000405030340c860011103070301c50300c010400900c18401c16041804c0f541701707811800090707010800702000d00030301c0c6140c2d10103110101d00520551403d0310009455040601c03c3c00c0004504c1a440394001c3da00750040418504503c0a1114410301c501d030040029209480007809100818000704190405105c0c4070151201000114a580c0301c40c0c00020080d48204001d4007040b0182c00007160202040c00808010b106c007c412400c0d040240c41c40c0c5d000c480c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77963949 1250 77962699 77962721
    0xf130306060519090b12030a050405100c050a11042711151204030507080705010f0e010209060702010c140105281b0e011103160b0c030103020f0d1e060609 68
    0xf0340d071504240c901460030048007625600200032503000c07400004140d409481e41990f81c058000403442060041e4400040e004461048404212900c10b2030000e41e03400d005102d0282903904842d0100c40801c1803c81e0004003904040c000084000c6081409881080408000079181c00101011003e12240c42110440700f0301c04c581c041281c0481c02c0200c451440b81280c040941c0000340002014140548290f40301250800c0d0b40c0c9658000500d0705074001e040ea013401c444028604101003500e00b03014400e80d4542000039014034a018400d4005482c1d0242c180c1c000c84141c440c082402d84074000a0080a00420b4101625506060b070000b5403281ea80c103540e01410841d00d49188104840352200e10104021150b00f0f20842032070501e0012121840c1481c1e600c80944400503100880500d600e0f401030800b402401d034030545880b00c2e282901984005e100c0658400c40d0455000020f15014038141d90003803065440c204140c40e9036420b03c007a481c0300c0c04c1c2aa6420340d540000c00c6074920358092007156103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77965199 1250 77963949 77963959
    0x705100e30070210020c090f0105100903050d051804141602010b01020a080d1b0810050603040203060604020f04120503070201030c080f040b0a0e011e060f06091a0f1303060605 77
    0x1c0d403040d0031400c06005030794019120700412116940b58034000e000803014800060511041880c140d114018402380c2882168006d0101051000c0018850304030390056a6000c00601100482005c045803540c01c0650708100d9400000c405030410f03030f503074461000300011007007904110346004050f40461410b01540a02964100b03c02d28095aa000c10a0480e043d84006019203842041c442807008102200140c01c0040554008440c46900009a2441205452202400192a0014483c0500051720b00039003541c008404107d440c41c05402078031007043d43c82125414203a89844800240e0301440e000e03a425080011001705550b858000e4610340035860404800505054103550103a02c0e00910190005031507201084c000701140e0094400010b5000003841013144008284014103a101c110508040c902a4000780c2d0003200200a0101d404548440b41281c1c83d01c6465542101141703440f00300d0240c1003028100ca50203090290407a1f00901081000d11411840c05804480607600311622403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77966449 1250 77965199 77965273
    0x1060c0f020103020304032105040b06040c0909050604020c030d021201050a12020d140a03050912010509070329010b0c0f07080a290115090510140705100e 68
    0x108080100c03600480e54207107001662a81c03607050032210166000124210762618907a0004106c5081d0409801140917503464645510b070001008110707094100c03c0301c04601c07840c008020b458800d82c01030798801004ad101601d048078464a079800c60b80850925180d1950204040914015201015015110031b0750041402420000911402d600c400c200901c2990204019410041003a000130301e0080c900c01140d0000c0154a4042c00d41c0e0000719010f40913140310742012005482c14010700d4060394220f80684070203411512580310f40c0b00b81e010190300c481d00c1c1005101c1c2151030790010900904031a1055516000400710382403c181d204240b403a142c1d4003400c01800f5001020401c2d0b1a116804010801026013880b1041500c1d0f185200704441c1c150220b00004003150500c0c204468600c041d9a82e078200c0341c68038208118140c2e50100e500c000390a4848601c0b07039001c2503004018203800350781254000e10350100b1103c2525400d00d05020190488081c021422b00f21000122491110941032401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77967699 1250 77966449 77966453
    0x10e01061d0402070f1b03060506030114010e070203040812040612110405060c0f010501030813170303010b181011010e21070224040f06050c07140109050a080f0601060c 74
    0x1d40e803100000680b10341c0d4005032030000c0020107160607102a07800303489041c2ea0b500c0c4080c8401d03616114402500d0b09410710000a4a614040c410761754107004207602e00d6110790a00014001e02c1000403d0078095102c200808500d06408110811443c2e001851403036840c0d041410040200407a40c1180300d0a074200501d06444c25000000c1d030702510070a0740c5250b165400503a0340d1385001a01034640c481540780c80008010f108a0348018520fa5111325018041c1d20395440030315902c0115055a450580c000340b0050065014142c01405405800300071840c179425500002040140102d00400c0401c00b1703400c88103103015003802408c000d03050300c0d000350210400244041e60780003500c5501c0039444100203150000c5544800030300590106408814132000402c44c00c0c01926442409800103030f00465900094161241e8100c2e0104002d810280203128940549010100b408041d11410300c601032074045119203454150ba030040a00d02c00511a8125500c0ba0f58203040c0706800a104008001040c200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77968949 1250 77967699 77967737
    0x50a0c06030e0717070e01090504060513050303010612020c061006020105090309010507020f011b03081b03012403111216030207030203040e070210110c0606040e1015120b010e0106 79
    0xb080715541c1c054030010300303a8850036a0600305d1942250390820141d0f40003003081c01c0daa620440c0300c0e52090100b009070f6251881952000c01d0807000050403030b4400c000501103a8071911940c5080a000c2c0b40150801c0f81a0100e5070400e50b0840c3c51111403600210100481e81d424041d95070032a200394099460030701e070a00024464411440f0281c040e003140000b10460f0f03441900c030100d0485403620050806241c07464001c00c04c123410394529010004500010300b00c0c01e0290220790494014035880c28017520000da00e1201c1d0726085011005140d51082580d0315501030307100400054179024a054400c0c98490301c186000240001c00008151061210400103900081280c0036038526202c040c000780d4618100300d160004802016468a04100c1d255022881d044054a41c00c034241e0184c440a40d03840c0140001c68941d03290750801584071885000003a805a0f12007080c1d04000c00039800e0840d00c3d122101c942c90200001140d103d50034000420402d0022021140944420f01d010b05184210000c02c2da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77970199 1250 77968949 77968963
    0x100e0f09040203030d06060207030611030f0a0506030a0501020307180e0103020603060d08040f0f0608060102060c0d2a05040815010303172833031707050307050a0c06030e 75
    0x60300400851010805540d010001d5403100c07008a1401d015070740e120030000b074981c01c0c948003c4403800d0030950241c1d00c09030783c7e0050368840d2000c0c81c0f035100107654201d01c14010380b1001d8009600b5004150695010840a00044d032007074001e030310744070240100103040300c6a00c96168000d00c4919000001400140e84190850760880c0c81125083c140300198240712400740703e15440094014480c0100094042c8402c2c10b41040b40c00310380301e194055540400580c1c44007030443c0d003d281d902d401c001d00444d00045600c070000c0030024004084066140041e513489010403020500d0100d0004201007285c130600300309001440d0002d2482c40c00f00c0d45103540c0a0403a0314044103146001c0d41d80f400080d0305085054100400003074074007600b580d403540b4800314002840e0101b407001c448040380c03440e140b0305a02c601210680c41801c02d8101c001030314603200e24115a42c25a03000d488180c0c10070001e40404c2081000d4506039000b200a030202544518281c80717400203aa0019060608041420041d03000c0400d40c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77971449 1250 77970199 77970229
    0x40210080402190f06090801150515040504021303050f120924030a0501080f01060308040b0313020909030c01060603141f05211018060c030906020706020702100e 71
    0xc4038103480314030009200c0403401000a03418860380800192099110340302208541da02d8641306000c5845541035826034070410407040341660310078010403050500c419034222034800c00c005123081070340b0b440000d000d83c3c1c0300c20b030800a900d0b03544406005122050207210440c04e078440041031084140d0405054a0040380e41c098401c00e140a07070040e07103492081003125412500200b85035a840c1c00f0020304020003003800745085a04c510380e02c11900210500c5040c064a03000b2032028101458000c9061069000405081442e0000141400140c68084105004502c07040103140c83d101754071091070840f03066a02900070103060100030810690b8900c90325420140c84040f1080059487c94440e501111a03440701d60000d0000300c0c600b46041d02c4040360080d082c41c17a0103030b515400881203188281ca1101b00141100c1e02d012201400241490f40030340700e0301240f41804115030036240c48100881c0c11480007a510b058000500008615201c038250100010509000400b11081c401043d000d003042d01303403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77972699 1250 77971449 77971457
    0x91707032007031202030a0806030601060c020603090c0d0f1104151401030e030c030901090b0712110109052a04110301050411070f0302010e12120a050a090b0106210203040210 77
    0x84001c0c08288552030146821080c401041c043c5002c00039503030750040d4a22000205007202041c120700e0042045e5040b144180d5425103654107540030890650f2000c7c2c0022030910840c003000880da11a1900c0b1224140079031000c00002c91a4144038013001254940035200da441d0442e080031036004008282c00340d0345000c191010940c1004c005900800c07510801250340e21020074401030300c0c40000700401810700700707036250040f60307a84d0104a0001e000b01711005207081340280c14101818810754000015a5680001040d03000d81c5440342410480c4020700a807041905c000d080c05e0594900364180f1400005950821180c01d009401200c5808180030741e0f482107803503220924042e07400300295807006411074403c032003081c0545070207402011000300c2a16103008803a001da091141e9001074404001111540070174580e103080c200c1004103002008003090960361614480802c6c010550940a003199480e14200e2020449000d0010807118055500d014010010000140c54001ca00110075885081c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77973949 1250 77972699 77972747
    0x8071b110102010212010b03060a0602120a030e070b0d0203010e010501080411010e1503011409010806041a0408070f0606080610030c03080304020a1a0d051003020f120304150309170703 81
    0x40b0701a1103080c0b00741700f080c0344140c00402d20001b00401140076600850700481e8040c3d41d16400d80c0c4031009e03069510f4482a00740190703c903446c00303500104002c0700c51005540b615034440c0c550309517a411290780200320590110051001d05440340c1e445000d405c0c01d00304010945816900c05910070180001d0078104590b4520b030801c00c0e2284540d2401811468441d81e13129078503072143c2e1140001803138850f807246001c1c100000740540045500e03401380c0c1d000715050201040d4545a103d621030040d100b115655010491080071032440d080310b160040c4200008101c403881c280c203040c549000540142000902d0520420008a00c1c4012070704803640201c520340c6960356400041c1c00024103501c1000c210300d80c040103a010304d002400403e10144064400c1000742c44a41e15109503200b1800f000b034109051004040d00351030480701e0b42c519400d40344203d078038117a2904042c03c21100d2180305040802e45a01c0032604100b1141220b4484c2e050103520f990601c000303030300c0c0100400000c030010004890b007a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77975199 1250 77973949 77973983
    0x1d060306040903200a020f0d1a1b070f020405330607020301021b0730050a020418030210021207120209090112020108060a0e0106050903070e010609030308071b 70
    0x1504051600c90104400040c3c00f6400d0581c4e0f4a81c40201c1d07080344148006182e0020510f0a09440040c8070381140182210121440c98090200d402400c0412464a0420400003000c8080c0080075110f2145024484040c00c1d403040c030042ea00040c060318000c0c81113039040c0c4000068440740301c0310f402580140c205481000382c00b0074000d124030704d4080e425500004401c5014100f0040c100c03040070380350084603425603031500d807080420360340e885003101044031795140f0a08110580c0250001c9005801340c5002c032081d640042c0071102c2000c201d00c00781050406420074542c0500801c000c1d1030401c40d00f0352030a00d6031080d6002c102c00080c500010711000b40a000d00407980d50b81518100701004d00803440e1944c69001a001c101c0403890224005054200080d00c0303418048555070071074218400c4010380b40d0800f042541e558008802c0b840e0541320784400000c0d240b402c0d240030b0f402003a241d20741c05c42d104e00b1804d00401c2c2c904010b00c0035052100b00701480303540c64030030710300e02d030450303403c01d0708269004441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77976449 1250 77975199 77975207
    0xc07020a0e0108010e100c0203070201030507030f14070e09130212030d0510090f0207050c04240308040501080c03010f1e030501050708180a0206040b0313080307030b011d060306040903 81
    0x641c1106510003108070010070031800550000e509041d2031421210003c508560000c02e40d4106846c2d030005070401d024001c015400381c0c10403a001002414007195025950b980081216903080181350004012401c0c4030710f080e08400c942603461800d540c00755480c5010521f0f188041c240b104024015800320400040c80b01c010700550f4204c2035002010301044c00d12041c000308046490040484941c50607950140701c03ca28030807180c4040d0b01401415120b250302c02008010310181410301a050704512444034015401d41c02a4091031042c801d43d0b450328100000104901e80003091202944000c00041c0803c801408a610844013601e00d07102083d06101c00742092540740361720040083d802e203c2413141d80c2760045044ca204800e4074131000780c4101c00d1050305581d2034000e03601030b4010340d00300020301c40c6c2c909940c015980206c82042c0e0404c0b0340c41aa8494503550700803105840000c0d52201c20007101e40e07100d012201030340c40050300720320b46688010004800b07100c00781035680300d69601d4126500301801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77977699 1250 77976449 77976469
    0xe011a040b071101030b0d0b1501022d0c010306030f06050c09060a0206040314040f05011b0c060c0605010806010303090501050a0207170a150e0c0105070c120c1401080405060c0702 79
    0x484500d40d51100d1640c50483e003180800005140480c0c102104480d090070140e40079114150020548031040c1c99680307000d0305004482215038114000e43c0b40c3d000107004c0360f0a0026030034070b0b00e15041102d5001041e01c00c0c01c2c1909994a28100b504154080001ca54240d40e202503503a0028800205502e076026004070328400c060742c458200c0404615024440e8002c00c0301841a80251a1071500306001c07031069030148121b01032078202c07844030881400154420071050234241d808007440c0351300c4d403010b441d009010010b039445080001d5103102c800d41008014040c260061202078010300c20f65055030f40c00b9007c2c10a900540c0c1c100080414a001c480d071013008031000900c050100c1004140d04941780f191942101074050300c180c510f0b0300800300b60220b58806c00003000d0514024040c40c42c2c00c0c000448096000b854291044908040042001001c0d08140032040707200d504a58541807034420b42c5880420780c444694140084e1504000110b180410855801155007443c00d9440382c0d14400038021f004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77978949 1250 77977699 77977709
    0x70c051e0a03121d060a110a05060114120703030509060918091b0108010e0105010f1115071b0f0204110d0e0a0c0e1005010f0e0310140705040e011a04 66
    0x1204000c008180216000741c01c40c081c0b0141e6490707590700c5550285215a504c14001c498005004208441032180305252490248030f4100550f08030b40380585905140c41c0d0300382c010004101241d0450803043c90302ea0002341a030b1015a0103080c000f4a0740e18041c050b03004a28a0034056980011902c3c5241d4929940c10301c00034511601130241e04040c0c0c0000d82e1140724039440807000c007209a03600c400350302641041e41203401c0741107890b015a080c407004450100c0314040c0b0500340804141515101d6506011200030f0501d400e01c403940b58601100000d10f44281c03c146000d22440c070300144c02c0420941026003040d82d4050720003041d10b8980e81000020352107008460103030340785800300501c0d41907800b0035540c3c401401182544903035034842e8090404030400703035515030310950304400410080d4040c0f000000400c4440c10320701d03104042d4202080c1422401c0c54030040a0765900800c4001c001140c6040c4c1d000406403914a0526040c801e440f401c1d1081800354040004030315141c1c0a003084d00c0c90417100071341 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77980199 1250 77978949 77978959
    0x70905030d0207090f0207020609040e1912020c0111030d240e010f05040c080103060504050304030c0308090a0605130915030c180e0a020d03050711030f030703020f0102070c051e 78
    0x1a0078507200070f4840205010b0403903810f082c45201c0402c810700b03000361900c940d00145010301c3c0405038020000105229089000305001740d811001240ca00d81103c49022401081040007a880c5400020f0800c9000c0320700a062026810564050300c50000588200101d001d038009200c0580c000131440000c2401400a09203060b02004124074884500b654103d4080305100071100761550200000d417688444030341d0000d2844801000481c00e95003240c0c1d006401038090300e240a40300d4851300c8040446800903941980c00042c60503103428004da07084002c0c07195160080c02c11481100354040c0b101381e0b10a40c07030706603143c48128082d00d84904c018401540c2c00400c2c4140e4942d12413a21000800c04864403108078034003500c001d820700c40812400f1100b580241000301940c6240ea00b0345281e00501d20550f000b90404d0164a403646042001140150320100150f0300c60365603142c000e02c0c1103000b25101481d640140020000104101180c400340c50049484458043d0b1003003010840380c0b00300c0400c640c4070b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77981449 1250 77980199 77980213
    0x2030c03010e01020901030b0a06020a120314040c0611060702070614040f090504170306130203180a150b0d0507290d020a1b02010e04050c07060e060604140903030a020307090503 78
    0xb5200550007045c42d244203883c02c0c03100005044c100700c0305118a20455016812080170000024025a038102080a13142400110406d03065000c171108103007124221280c0c0b4403034400740b003030713903044004511a403c0f050b00030125458103100003520f4005a102e520144880300128201c03810203002aa406883d15140c8294081d60343d514070f80c06000180c80566809000250750301c806c80203a011280324020241c459040f81100b242108002d40c80240080c50305074550000d010f0030700c000d00c007920015010790148011212003010440803114042904c61150640140f0031000803c080b03400412580305406c07200021038900f05d05600f03040c80ca060014140000111030503004941d602401d103411403a99134041d5002010ba85e81041c0c140e488019000c20000201550030b072034603400c1150b101d072850810b54203140040d9074100a840c0803a40850890700000c0c00c1100b241080d2003201c5c0c0f400080c4203444281d09040202030b8481c40090071585c0101d07000400a04154019001d003c000c00c4064101e442d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77982699 1250 77981449 77981471
    0x11070c0b0a1205041209050a060905090a020c0a030201090c0f05012102090909070618080a110a0503070f05100507021309051501080d030506010201050601020c04090c05210d08041a0402030c0301 85
    0x82941ca170760700c1c008a50030040128803400c080602006484840d00c51984050408040102c0000c0041c15813044a400304121030b4031400c140030309050f05210707400100d110065490101c003640f407a0f410081c1d00d000442801c00c071903a40110680071008900d001800c01c5410404010081e01c607400269800500c50002e03c22040400100002280d40a58512402c0081c690085107102075030310841ca8945c0c8009440c03000301d1250240340c01401001000c203590140c0e10804203080a803980d012540d0240750100822030707828203045024880b003d61512514102c0d0507800101059201d01003005401c2d0394408843c2000401c000900c038041c56220402e10719070352010b40d25a900e5000c0c50000000741040081805540140542801004143c001e41040710b140b200744002000002da0075100e00404070340005040d202d4402d400000f082000204484482041085142c04c111052402c2000070b18802c03c00850b190107003007010103001d600714400c1d84e102c600009280101d054501030781940b0309103030108 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77983949 1250 77982699 77982713
    0x2120a0309080f060403090302091315020d0f15030f05100218030d11072702030403020f0f0a0f12030209030d0e040606140a0f05160501050a11070c0b0a120504 70
    0x41141d01102c210f0700f50f10701d14901580c0b03450007501d004010460383c030b006000602d070441d0340c0c80d4000500c442800140480b92101e840b4006c400e03910100e5190300103810703d5520054000c040545030309070418007200d80103a0860100203400d10002d02100480740400e400c1080520031001d80856031071065440d00c0c1c4000d807414500c08540915842403082c00080d941150281c400e08213100d0302d40c0301600c601c510740003030504441c5a1a5400c801703624104285110400940b0145010b1360088c0e0041c868521840c0010340b42001d055401045544403100ba9000502009100c0043c0b41c0d020540b4100c03013541010a5020780100e075080355140c0160075200c59020380c0000900c0c4800b00c215402c0c000326607210f006403407419140040d1040407008002540c2c0d01d60040001c0180401a0b10340700c0c0c80c0c090f01040c01880000e43c800120f4180c5d45507000d002003040e260048c00e00b240c005140c90362920302d1550700c0d2040c01c4068414020403a01c0810303d91222030181e16500f0005510440900c0b0900e86481c0c014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77985199 1250 77983949 77983967
    0x601090e0709050a080a051c0203090415050907020609120d0b1008090606220e1c08040c050901061205090124030512030f13020d02040f0f0f02090607060902120a03 72
    0xd801131401c0e090011381d940700010f5440c0c050b134000c0040c00307008038000380c22a100881134071401c082d48810002d00d03800741c86501c600307203445400341c004005480c01c1c2020082902c0b0301401c85011580038009000510300c0110b500703007a415403460b48941d00c080620100001d040c2d001c1c002d6501c4041054608a01c580080040784202c0b88c10f0700b507a065541d0f9504000c0d0142c0455118241050000f60110f90415968000b0340400b00c0d002c126012852840e060404c50f004031800e0b440094010002d100070841202c110b040500003c4807164100d60500c2e03c01040f800d0042012840652101c011928002d400c0d484400081e460380d007041300e11940c3c180b000c402882e040c8800c075658802d0081002030400c2d028281c5c0e01400c000d4003e8000ba45070034514000c5580010000c0ea40000420b440100503607031032040000b000802c4001180c01601c082003201214403c240f00c48201d8010400d880c8140c0d40c000840b51401d0b4400c0000600305a40c0c004190018820b190000721032241c05010340c14150048905 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77986449 1250 77985199 77985209
    0x609060a020c0616090e011e06090f0506130312020d0807020c06030c1309020307020a030e060306061e22030212060702031e040305070b040e01060309080a0507020d0b16110109050606090601090e0709 87
    0x48c2c42000e03030320302c403c40f20355074a449565824400c00b8410712440c50550018404001015118011280c82e6114502141000f40d0500090380c807136501541d034290408161503124100c4d0000d4a0007600b000080341d039501c0003c041c415009000546400f20b1504110480c000e049034281c119100e1500311800b0b076a40070404c05c00ea0115080103062005d0345010400c0360720841024081d1402c0c0801c0941c40c145980c0454681c014140c000c0c003040c941c20141c14134512400c0080030070038034180d10754014003401c41c0d03850041c841a074010208002c4003580000c00c0340d400c9050910141590058080401428010350f0001001c502403d01d0010303040100c54041c1095404011440d00c8507640c4001c19000c8510000d401070148006100d00001907000d800600f48041c00984240c039844010f84e1615005102100d42d1601d4000d2503460f207405a50010380c00c00d4980d0104001c01c140d199685520f035403a440100364a10804c1000001607050740b103800418020310495220749000c1c20041005020790019000e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77987699 1250 77986449 77986499
    0x2030405011701050f040c0507061401090624180f030c0e060a06021b0609090a0501230108060f061201030606180908030a0f02090a080609060a020c0616090e01 70
    0x200c0203414001c1c5400c0d5041310002000c4904000d0158107010281c1101c1d40140c09000302401350802140f141c0c0504000c1c01e250315082c1c011581001074010843e00603403c0038000d04013904209407001c09903040312607c043c00381000d0030101c0b19440e000701c0c002030b25044034828030070030070300082004246441032042d111162030441069503540c0500101980c10303c40c40005921001b85808846080c0e4203a080035074028005510b0b1242101c041800e0319010380c4c2c0c3c141810390b40c01c01000401c0704503042c50811a00704405144100078003000804440028080390b01c201641d0803402c1c2180d0f6200200c801c02040d4412140080d81e40c1d040050060420744036400429880007040d00c8482c180384a1aa00242d21000c071909580724600e264008115a003e10000627900308180c031a66602c82d0029801419a4401448149000610300782044005401c0ca80000d0060001c07080281c400f007a0554010880301c2607007040020b58008840140b103d50021100c2d40405002141041442000034203420300c181c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77988949 1250 77987699 77987717
    0x181e060f060103110417011805100b041e05061c050f0d02030a05040b030a09080c0106050f040b06070201110c060a030506010215070e220c05092b0b0405010f0603030203040501 77
    0x2006600b902d130100456401001d0410007072000d42d00d2040d14850f9040444000510601c82101000800403c40c2c0f0603901584000800086400305006406030000155000c0c400c6402c030303507460b080398003c0c085a01e5140780c5410020b52107444101c0403501012407a11051603101c468240381d40c030b508080311134081c6c90045209117080c030390001088503454981a6140c070714040c581200a0a680c10280a0303440741600e42d218640404d0040000d084101c900000018040d0b1428041220340c078900480c09000f18180585d030503da603240f10a031048280c083c01c00c0d0820b107480c130076500e003450501e06050782c1c42800404d806c51000c1c0d041e40994810b2000780c0845103000ca1911540c4035211f030442d8114009100210a0610b900b040403000c0020008000c1070040c41d91400d10740070598400c4038888001034804500b00d0071a20b400810f100124010300b00310301401c80b00901440d40ca400030340002e884000d0721310201e01000b070700f50b206409800126004101454a07494001d4072503106200c1c2c2070002d0030404c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77990199 1250 77988949 77988961
    0x2030709090206030609040204090b0c040f0f080c0108060d08040b0901080903090306041704080609010507030c17010b160b07110c0102010e0a172215030c08181e060f 73
    0x120407003041c190010019401c5a03100401c0010b04500203004907002600c443c40c0d14002a00c810016018039000f04110380c9850500c0f550400740503041c0c1c0030111200055030100003c402c00308070b030312100b1020710300081c07180e0b00d80001c20704900002000078040c0c94001000200400910041e01500b0300c00d03a03820345142c036100c0310035607280112007806a0541051020400041600180200c040f40c088440750810740d0301c190860918000300d41c0980d503651107600f000302c103e50512031401d0303080d403c0c00c00d00f2000304a03c881d00a03201d41402004807280c4005022007441e80b41e0110800b0b00c5900c0540d41c8540d20f00f00d040185560140085480144103500c501400c40d801805030a100307142900082000c64101c1d01ea030036110050030b45c01121200708109215602c42c9141c20040c0c1100c400b180c020382140750041c01046640401001ea08161501070000c4009a018041c181c00c01d07545e55180104815002c083c0381042c0305180d041d01204102d45480400c07801c0410100d02c18614944600826a244 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77991449 1250 77990199 77990201
    0x3141302090c120a09140d021e060103150c0e0a03050f07050405090a02010c020f0904051e0607051804270b010504091226010608160f0e010309020402090301020403080702030709 78
    0x81c1c240012000c40103000445181ca154050178029014070504581d5581c2c00140601f00490000303d0030050700002c400011040118000343c4c01c100040c0020180d80d072440d25210403010403c0320141001d03031950013040a0500c80c00c40740e000c4410007009214003690380c0c41c0a5035139203021001d18800b4052148006840c0c903184c860188211040c82c00f81000201940c011900340100c81c0049030b02029482503502651500340d01e00b48542e104100400002d503144102130603102c030484039000240d1090b010065450b0340a420b80f0b0f11148400e10904079180da500000d40500000505d51148080d202e40314101030040c1600a00c07500d0203a40e05001c10f0362035200380410f4a404910252440514120041640780f1a1082c41c080c00181e405244902c1c60003400d5540c014400e0740910001441c0d90244401925401086150000c141c2402a1500c60000c00603010144140140341816582c80300c0f10155110768045800441c0700500131583c56450f8500b080140d0031008069000344a0480c0100710724001d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77992699 1250 77991449 77991457
    0x10e01091404020109060509011404080d09120f03140909091c020304081b0a09090305040e0f13031404031b1d190504080702030109060c2a08070303141302090c 70
    0x1a92801801410a80d09075040d6209230707529030421a04c51603da21500c0302102034800740551070301070007038000d008000814084080c0c000c4980140c500b5075003000240d401500c0d03006180c1c14100300c00440c0c3d031314808800318003442400b01e40003548401048401c58010641e100ac01040d5484403000d039010040c00c90381d900440c018541e0035800004640d4420013601840c00038244020702c2617000a440783c0a440c142c41e84001e084000c18008501800401c05c01e020341580580352204404d4540380414800001041c1c4820160520071501c0100f030010003241300701d4001c1c540110002c405040169180140c42d402c0748560b2000e0740d4000d9a0415016000b10424040e00c0803804070381d4030b810641070b90001420042c00c110f4800c4010041900140c90078014182042d025100000f038040450380054501c013411b200d4125986080030328590806568180071196680103542941c8841003840c0035001044084010714020041c00c2c05c004541c6000352a036040a1300c240c0d060300440e203550042c071403113000d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77993949 1250 77992699 77992703
    0x106061e02060a05090309120a060b0405060f0114130e060a06090f0b03060414090105070e030d02100f06050a0f1505040b0306010c0f0803070c02030106140607031115010e01091404 79
    0xb0380850904001c640069801c043c0fa1400d0740c7c0f60010740d0000480c404003040000c5100d0b040744002c0c0042c00144d01c101d84081105540500c80e52138114000740030300003441c12087c18000d05c0d02c02c90440c0c02000341035a0040c0103420000d40f03e1a00c0d90007807034003410200d400500c115031103d40419070502c603020701d004a0b8071000c0401c030b0203818601c0791007150304020003182d00940d954024801864194003442e0044004500000303542c100848024844005c194103e4069030000403402c00c42503002a508881c500f200c000041c5440b20006c9450207410b041c1c0c401c650000c0055008100131094500381c0d41110490307083c00c13003440105641610b9034020b038480d02e031b0102410700020355554003800c680c12900744034000d920b11400940d6200d0055400503a10200000d6556444c001141801d100d0304018060480700c0ca100c04074010b00240c2d5030304c1031141c0101046103140340d03040441000c1240030b20924001040d2142507840d2060f00e1100c280074810300410078200603200740825000b00900e8016a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77995199 1250 77993949 77993953
    0x6010902090d14100504080c06070c02030c0d03030e03070803180601030f020d0204020d06290705070909140f010b010f0807080f10050d0804050123070b0a090f050106061e02 76
    0x388680303035004032031181407140b2018090341c1c20741142c01c0c1291003091b00c214880d0407030700d4984100d01459403610400600c1f400c2800722507910000540d0300007442c030400701000c4541d4480c1d8035551500320080d10044041008500c4041004400c210501e40914401c0200ca20360509200e40300f040c1940d103441c00e11000e00031000c2a9020f40c0541400000142414000350000d0b14020f01c0031500c80459070030307a0161481c80203c0041440607240301d17900390001817500c0480ea0030720885440d16a25602e813845070006042d95810403004000012404c11030940d000c0c3c054030b1000d0304561a03107011341850200d40c1e0028001804000345c2c07d0140e01828000c1240b0342d41c450b1645d6580c5070401159201400030781041248200c0040e443d550f06c0030f06000c0601c20b0f00e642d034a4a151000140c20070f0007512020341c0c244040d40080300c00714088001c1da030015400c04025002034681c000d000c0c0091040b800080e2440c40f40000e0751080c888150090021070f4019641c102c0341400f880e202c07004a00015103444016 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77996449 1250 77995199 77995219
    0xa08071403150d05101a03030a021905010617010203040309050405070816090911040821160201050706020f0c0c040209030a060905240a0c020a0309150c080d0603050601090209 77
    0x2500c400200d9030007140b00070700840d010301c0150701c0d51440c02034020311445180b926213000c405056403115061484040c207400541c282004060301a495503940c0a00050b680c002120350707410b000c0250040802440702e00c10b01d001c107501c0c0e4818070340030350b004550036804284003000c00505403c152061900c18503060b03442c1405500c4101c445074170302c001000c080c030800108030300100d1179041c81c1c4581140000d0112045641d58a800003c03810800c1c03034030b100480702c08803400e000c0503508040121001c00c0c00030440e8240713810f46440181c4e22805642c0015103994804507907001102c007821f0081400c40c60f808120340c40412401c003004140d100d0104440e40542243c1c0c580e400048054010000a0740b107034003130314120781e40002051150140450030613110070448041c000d0f004200e1241420460b103620213051400e00546001d401c044051055425041c40d845c102e0f00740304c0c41500341c0c1e0409030740244155a40c600340764820000d0f04c6940816901401103000000300395219200b128101c9001400030056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77997699 1250 77996449 77996461
    0x815010501051e031810050603071206140a0b03010b0906100e06090607061409070803030103080304060e010f0b030c01090311040b21011b171605040302030102040b0a08071403 77
    0x190001000c058682c00c0b22103015000c110100061445894a40c000312079941641e000c1e240b406402c030002d01101b62904042c00415100490501e06a5601c01c01d2622400d0186c40d0a40c01040907816048007c650182030011441e801e811410751010120003d05c4072100724005c01400c400c0030b4891561049109924288003409100e00503d0488010700c1c03942080780785000708805900c8150f00300d41181d85c4d03100144000c03a40100694000f0314403030040170301d10300b4640be46a0360300c018000030300f0380480480020f0800100ea044201480c200b03d00a003c030242089065000d40300400c4039500c28050b80c50240c080354441c95110b81201d030000004540341c0224000d110003052111149608540c04103000e02d03d00b1110042d00c0c09d41c80c0502d000013039542070090201d1003902c040842d20200b058881c040515411a0442180c010640c000c4882c8203110b410403e80d418421a403009402d540045000940d440340a070240690300031546412005a5503580101c071b0010b00c1c44419020071b242030005c541 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77998949 1250 77997699 77997707
    0x20a06020105150f01090f0902040e01081f050a020c0a050a02040615090b0c03130314010501091107120207050310050103050c01090303020a030c02030c0411090f01050a0207030b0c120c040e010815010501 89
    0x2604c2c110604240380c0860f02c4040f403050540043c0c101645143e000581040304444032061280104406400307800403c452600641110300003210320420300351a14045102c01c07010b80c3c1269051116081200d245045500e8019250600068242d200b05d10b40b0000050a540c005211503032140590742d20901141003090400403900701e101d83d400603110910000d8151072402c1240b602941c0030301d00300048540b103141d00700d0944005801031041d841c107004a654046401409071003409510020300081c0f13883d0400120301d8440340703610459240c410110415001005507000c03605a0b0b001d0350039201c10101e108010340c1c4060703140c80000d006901c1004540c002c00c1c8501e00e030b100c09038801020f0f5043e2545441c0010160b9003030580c000307040140001c800059140505002d086460207007445420714559540c0607440c1c80e203030b00c07003d49030110480028206107000412600d440c0300780b40080b91039052030040d0844640050091400c03150380d11001140b00c04e00003a1031558000c00300c104a84d140e080c100115 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 78000199 1250 77998949 77998969
    0x30507030c0f0e22020c06040606090605060304020103051929030705030c1203280e0109030c1811070602040302011b0c060e06130311150c030313051c020a020a0602010515 75
    0x1001301d034180610140c8807220380001c0c6200900c80001b054581890f0410385d00700c0d0b440394415500c0c10302d091002c000c0340d1203140c01d0382d50068090800081e41e954100b405000068100c50704118145030585030100104420003d0881084880a05031507501c807005241d43d070145802802d07416442880d40e034100340b425404110f80e400186e010340b03050088240006005e0300301389415190740141681c516203012384c000350118501e0030910f030029686185895015854003180510b0f0b0300046038404200b0700700300640081102c82d40306062503035682c0c244d0810b040290402e0000300e0004903151303260484800d6070001502840e0700080b107648030514101c0d041e20300b49014641c881e0415000c1c410984c01003100d141c2040254051550940044142d000b00210400861701801c00204140040f402c0313004000207076640500214052a040215070a11b40e02d8100001800400440042d540d040e52503404a500d0703840b01d100f40c451700e05040d200c00c4140d003078900488482071042d80c01d0b00206202d15156800c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 78001449 1250 78000199 78000229
    0xd051b011401270501330c0201050f07082101050a0312080406060b1303060c03020f040302090604020f031e1501020a030f090f0308031501050a020601030b071707030507030c0f0e 78
    0x80040c00c050f00401d0040d24000d0f400404900108078100d010619290b002c507110358600c000c1d4840b039566501015200c2e035882c07407020b41001804290303da040094141101c0c020340c0c00040c81da80301c4004100f8080803910042001c81c01e0300300318000150604220441006072a8000000c42c90100c00b0807044648000042044e2601901d8040001c0c0001d4000e000f85a500b0103d164151001e046052400641c0d40780000320301050310411241508210150984003600e504448401e0240c5032900003d001c0d0107003000510340303090f0010601208150080c02c0101501b4000c0c02114156580b11400d1a40b0303500d142e400e40944c00c59520f140c0041c0c443c0c000c1e0820700d4210b00b424141e480d1500e0720621001c217603400c215a500000024000000c0c0c07640003446c00c1e248240b03001807510590050094498806101c0140110b414001044246002c2c2c006401901410000a02d40d132030a400014043c210030b42c0c0305004280b4004286241e54411208050045520b0702c0f03444501b5520401c2c045108a05810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 78002699 1250 78001449 78001499
    0x31b040308030f04020901300812070c0c0e040f0206030a06080d0f1706031f09020415090b090412110307060219140a080106031d0d051b011401 63
    0x404000280c050700954020804041e08580c03a19042c4180080c074001070300496100080012803100c01103c0700f4040240311118034010f40222030524220106000d641010103281100900700a085544a864910894003500c1889545541c0d140b082c20402d00c10f9a000d400d020b844078504015041080003035800c26010740001440542d154289402c00c80c4150500f0002002100803c4420350b1050340c88586540310261080319007410310000369102c44c00c07903051080f6007800029989902c00e40c1c0c00040030070740180050089440316144419a24001c0c01224420380ca80511101182803010fa22403003254081b81c4201e40148222082d6100030900e4401d9113144800c2142000184442c0050601c40004e42403606003000c039514040c00000e080903448550745400d021904401d54803e2103107044456608000a2800074840400e50050003440c03524010300c6000c1c0c1c9011015030210041401141c40b1240e1f00d04416045919400d98041d03240c24407003c030300d0600500803840402d440103011110514 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 78003949 1250 78002699 78002707
    0x7120515040c0c0c0605030114040225030c080c100c020604020d03080c040b13030c0e0403020304060c020f03030a08220203070510030608060709051813170d020f040504110a0203031b 80
    0x1c4c50020440a68110710001403020004204600c2c0004e0020050724003107a0650501624804090590320204642201c880ca204009418140146e0000c3d43c0590010891561000c5110b8010703554101140c100d119285009900c0e410303288040394040c02aa8002c01e2000c1000311398404848641d40a41480790780d10042000107021500ea00049c00304038108076240f4800d43c44c0d802c0c00c201c0d032903242e440520100711071010800000d601104460a95080b81400d0050740c042c1c0c000305a80c82200908150188000035401440310741004170a40b1918501c1030200c480c43c0305400348640d40c1003c04000f0b4140d8010b5005112502c0c06910b18541c034030039071a000500950b980d1010b883c019082e5181c50100d18640000c5c0040c2c05d00c4015407502c0250182d14070f205080800606100310300c0c1840180c402c040038180c034100103000e4403c440b18240e0341c0d9010f6480d010030480d10040350b441446140c2c810341c03070071850140c0d86015100742d8000e0042034000c1c60840e610800c0c10802d80d03a11000851128000304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 78005199 1250 78003949 78003953
    0x30504050c0d05070509090111030103080c03040b030a0e0d1803060e0a1a010303020d23090102010b04020d0e060f010b0f0a12020f0406030f1b0e0102100903020607120515040c0c 78
    0x500360302c1e4601e0083c1c0007080c0451800d000d00c04102c2d800782c41030b28664142980703c421070440d4812241181c5d030180b95a40d0781c4501400c0d56045010796008090441c00000902540e48400d81050880034040415035414205850041d00c1c0e02c42403107a185040001120200041007456219001c141640e83c1035484449055552650003142419201181e01c19540148103240d0b04110010300780003a42800c802d0507200344400d00e01d9642c2c2d81034850b8000300001c1c401500d64401e4029000c18400070b8015507d407000e655480002e0000c004409280d0b1060360700180f111401c401802d41200c56105c40b2500d0f04a1100008040c0c1d0300480001080c06411001c0d1400c081540c401400000c1b01c420b48a43c4071800c2400c0102070b11714070400b48018900782101b4100103000c602d42c0c01035a50f00741c1030070030740d03030b80300100503800d00c031040d0003aa01003880c2068050034035402040540c070a807880c0d038483c280b0032080d5400d20100c071000c1e40c0e480c2a0f10740441003840641460b500030700e5420311071705100c00445030607 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 78006449 1250 78005199 78005209
    0xc090302090a140c0406050d0e01090b04050f0c01021b011107080d031b0f020d030b040e010608010204051c03020601050105030408190309060b0d0809060f0403020604090209130912030504050c 84
    0x142d80d11405190354506100da41e42e030038640980c010101d100111710301840d20030001c00d01d025207201d5155040d90355108138000d482c00d40c000ca1f025540b0081c5800649051306001e03444460404913400b00340924a07948241e98404a00326002c010003a07142c8481600c080300449080030341c107103070102600c200c0304042010001007005481da100e081d039010401a0790411064840c00b1140600710502810081d901030701c0d50040b4007039140c0d041c585000522008200d001402503c561421040554a0900040f90091040d00108203841c015100200000c03000a6004032800700d540010700183c110b013006103d00d6100304002c58000e400740d0166410b001c1c1840074400c0c0c6502c40711043d4080707a5107400640c1003020038000c800c944803040f5025a40c402164413600750078401c0c10326a5108440004040450041c220306581c055500606041e07203558403078864100960118034110321505500c21180d01303800060095070280740d44008040903c80c007510003500a07010141046841707001c0c10195828030b4a0b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 78007699 1250 78006449 78006451
    0xc110301060b0c0c0406060507030c060b1c060b030c060301080d0813020907021b120c0103021c23060301050c0d15030b09030d05180d0f050403020402131701060305100c09030209 78
    0x403c1c4041c00c00080c8084c2004100c641540c0030b181404410700c20413001c2a0003021130402113401c0f200126030030000400146040c807510804410300038160001d80180f240c80e038070180c0b15000507001c81e541c01c8440400c104180c00b00344148440c5038405d00d007110071107215113080c542101084c44245899421035000503154481101d01e600140d010a40f004407140c7d491b8819440e051084e5450054450906103140e214580840046e0600d5000290554103804084159080c0d1128210400087d5006414040a81e403d82d00000d41e4003c0c07100171034207501d01841800e000e03130503044515290071041000b40014000364043c442c1940da82c20000000320710f568011901c91b820060255030303100030880c5814103e810241c80300c2170400602c0c02a890301c0303100141c0c0c10101c508600f0552032400e4111000c5549125503080290418000b251031342c000c2c003983c02404182c0d0b44409031042d4407090f80341c94a00700c5003580700180c50f6030b11501c1140140c01450b80300420809041c5014807899403290085006010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 78008949 1250 78007699 78007717
    0xc0f0602040b030402040c0305071e09030204140610030e0706080a02070b010f1707051809100c0c0c0501020c1e0a030609080c1509070306020a050c160e0106020703030c110301060b 79
    0x10b000810841140340c50703c01e00010000604003007000381804075000740052488241e00f074000a00c0304544440d00d0250b44020b0007143e00403c00d01446174507240c0b01403a16801c2c0c070300c2c60160b24000c43c0c1c008240c2c040d004201d00b11160100800c106807070884119030346d50010340142c100369402c00141c00410050000e40c1e010f044183d488400161500300005800700c80f1401d1600242c200c0042070045946070007986252800d80c41142d52240c60700c51425041064501a506205e491b0016152480b604518500240b90041c075000c002c070341d42c4900680c1c84412580e4140e5002d00000042443d6551030f000203020400c014140600003a140c0c1d0310f480403031351190000d0300c007100b003c00d01c0c400b4100c04001c0f10a03095400300ba02125030400d1003281c0d40d074201070301000340042d8003c100341c035207036110301c09848160310741c8400c480c4422030442c5855115070981c01096041094100081041da0000940324200d0f03034036036180d030f0055a00d80c94008807800e0824145505540726030001078440800030103001805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 78010199 1250 78008949 78008969
    0x110d0227060711040f02091c1502031909050c0607050601090518060403080702161404060f08030a050c03190504090605010e0108040201030507020109170a020106050901030f030c0f060204 82
    0x2401410212080303005518103445050704000300000904800c03444440e20030240c81c0425880c12201108010b405000301254004985000000c1c200172800044a07070343c5d020342e04c0d0381e0703040c1c0e40c486070b004c164032080702c1d080d52003a118203250341008041d030700412045000c0c034140c3d51905001400a02141e1045034243c91f650f00400c0140701c40704462207181d030813a21008101c0035201c410f05103592982002003018040c051400001030034a8000d10280c9400910580c01d41085a101c40c50030380f1602000b20014021450403c0c003084001035498410150f0748404011401c4c881d08003001c03035065100307450846090000b445100d80044003403400c0e070346011458a03415142e504201c0d01004884e9143d000a04111407100840d490b660040113940e04240c0a00c0c01040030717552440c06901400840310300404084000c6400780710581c01d1405404040142e0b0300a008030303541e4008004204d0750070f02001d0249492504540b0020380140c101e040228411850500e980889490b818100d03049075006d00004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 78011449 1250 78010199 78010237
    0x3070f060f0210140708130203030d05190e0c0607080408030c0606010f1e05070f0f050d02070e0105060a0807021002040803040314150a020a02100509030d1404030c06110d02 76
    0x556010300c8070080c08050100200030080c04d4020300c842e082006081c203000e00100c03d001c945894800d11501c0d0391140c0140440741c2c3d8602210119006120455841328001c144901c0803034248100c1c0074490075040c0c11002007046200b0001001100e0740311440071140004104800a203885062014002c02104640a41090301e403840024103100051a40c01c000c0103038600c0081482e451012120f910903210349080c1e03484580c10f182c0401e00c0b200c2c5c204d014000c800f9903200c05040000c00540900090110b90949002a541f480398094481c420300410f540045d080c804609014402c1045503807001c0d0b14411165003000b003c41c1141243e1082d0400041c0d030704006400e2007841110303486110300c21803220080c028007280b20001c410b4500e000d40a42c401c1a0001085a00070780308002540341303084032020402260a245107042e40d80c0d441250440300700350034180e00c0303c40c42c114003644034800c0390952502080381c41740b40da6100c02000141c41c458405074060006100c103144d14805001071a0281c0a51058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 78012699 1250 78011449 78011477
    0xf010501031e0803070f0e03010f09030306121e020303040f0b0316090e061e06120901050604020403030203070311070b031e0609011a070c0512032808070e03070f06 72
    0x6501c0e0340b019868242031800100c400242c0c900700322580840d00d4035002e0030002c94843c08891003c0c0f400075003645903080829154408955502c10495144241c40c1044942e0b0f44440343c0d41154150304000e8070003043c41c03a0040c2807041040300300e81003d200400341d034a4030340c45a0703511464007000e070000d00c3d000ca004010050618250f54100b0b14421681c180b030511309141801450341c0000040c03046000e814141f080c0c0c82080792240c406004014000d141c103466088480c1c02d00c011900440e2498101d600348408034040e801e0502c2198180e03034040e4060b615160032038030f09881d58446c5040a00c042d05c00d602c800a40c240006003c1d40c012841008030701a10038002801030900034003d082d040c42414030a004100d01202c1d540b00042c504000c0c8400341d11440c2d01d0410640ba00b0b901e6000d990071404030151b015400e0008401001e11700192003030740803180c405294000700240c072103c104004c5a8110040798002d40120901c446440c0d000301140d0101c0c0c1c80c0c00711030407070f86041d52207240802c100300403e101c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 78013949 1250 78012699 78012713
    0x90f020c0708030c120702091303030e060703020a14030103020a03020111030403050319020105060f0306011715070201060303080702061509190f02190507050a080901120908090406050f1806010e030f01050103 91
    0x840617a2001d5260a10075a90009041c0c0c4502030415509084002d42c2d010405000b600200d01418a40d803c0c0c0b40279151441001d4069801041d400c00006d500e5001c64080e0340d03547c011349050b81d07005001c0c9030649007545d00640c1c00700031002901300144814040000010700800080c8150072900c2c0045c402241d182802032300b900c001501d558401e05010607400c00944000449604644580c00070a10469003c80f5460403c406d001a4440f0305c20035404104000350150012022a4842d90340c003580c5989400003243c407914203a550003141a0031250300030443c0303890040a9000003900d02c0325008104040e011408955120350b10701c030901e80128040c2503142c00e0403d02c0640c0392182c10311070f1500b6451380c2c42c943c40e95030f6000c00070302c20000800c21032284d910901010441c0e1400c0c000420030382000c0d040401654210b40e038070a10882c14510b011a5034101140c1d0201d0f000405040d8801e0b1a00c509034446500c0e0b0002c02c1c06040006040d4110300c0765804000031820402c84c03000004695046081c40300d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 78015199 1250 78013949 78013963
    0x309030f0809040b1804030e040b120c0a0602030c120702041b03050412020309010206060402030703110c01020c160518040303151d0112022809020304050618070807090f020c0708030c 80
    0x1d10616417004502c61244200b42da159025625140007000c420131880060014024111a1508500405064040c104000544909448048a46481c000e95901040740c0d01d22130500d101d4403580103030040f41000019040a010030501c01403005c00c02c00540325449200d260340700031582c0029215003d020038009424130003d403104031480514a030600d25000070750360f1000a440240200d6001002540b0103200c0c1e84030901d21503a00e81801d035244040003249010f900002c200085074020ba81e401068985200401c5003202c3e00900305654805229038941c0c032010000b0b000368103240d1070f03114040502e09049a03d601410407248800300021074041201c10729031050700402001c500008048015a5404443c070000da103d1030b40c0742e5004e410050462903203000c00d41c070106859001000b8041045008036420b44505207000201200b940c07109840380d580c10840c8500061900f0205043c481d862480c1c0011414407a0050098a032003a41e5095620746507040c7c3c00081160000b042030aa066802d02001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 78016449 1250 78015199 78015221
    0xa021605060313030c050f010509030d0f151e0503030f0a0e0604120215070506040f03030c020c091b0f040303050c0d05120609060103090507091506080f010b070309030f080904 77
    0x1d801e601d42003444401040c0481c40140602091010500070032500304141341071303415100000c3c0010706000c80856540d400c83c0784234100c0a4100502d41c4c0c00c415030b5210b21418102c0b6030b000c114000780341c4800329016149013860400040c28020f40814240c504200505094141c00b08481c0d41e5605801c0017480b44100b40d544a109880c00c000c204459042a0016621181c0490750808404068000f40036144580d80004196010700310410080c03042004424480c1400b0792030a01240c40e00d018100e89071800d8030344040d48100f2460201c1c140d10500720182c1c0e02044150205480c01c0b41e1400d00220030b0300b10741e008500203240000d0111030b01105200420030000e41d81005401d1164450f01d043c03003c00010303e00c1740185400000100d45070701c030f600001d0415801009a40d01c0e0368444400002500c13160a040d641340700c403514001901445608114030030910000784041c640d00384040d4000c00ea021140076010002300880120103d101e2040c800011445a99407994a518035824041580c0c86a012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 78017699 1250 78016449 78016459
    0xf1606050405060703141207210e0d1b0b0f01030c050904080a0c02010903060f15052d030f06090c0f060906180111160e0a050103020109060e060f0a021605 68
    0x402294549000355440c50b42d150130110300401b08000d00703001d1406048440122643ca8509014016030810211024201c41c450000c24442440342c0c0c9009982d1440c8004440b0382c0300d0091307001603902c540e80e001c1d00c0440a1075044400d01c0191035141c24040265010101d020900d00100200001420044010202030f600702c01c0910342501c035224039004080a9000748140c4218400842e0700c1810303084044c40c0c0c401c10412000c000840c00344d000709005200a81909400480400c0d9440c015204903520100c000041da8a040b400c0404481001205441e9400d031107a0480b200b8400000c0c000a8414000c1a0013050840c13103070750030000d54103081a440c13800790404106140590711440129101042007100c0740c0c80c00c900a20040b202a50144100c030302e0b5028080c1c1c2c0d000d189104821143c200c403000c0e488440d050306d8075907420040790403c0c48001d020030b0714800100316080c00741c0c480302c070b034440c00920f450308140201e00c10404950001c155600180c203c008030118001c0d15201000103084250f807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 78018949 1250 78017699 78017707
    0x2090913020607030305100e040f02031b0a0306090503040302030616091a03010b0a02100f020a1d06120c190818010908160804080102040f17010c0e04050402030309030f160605 77
    0xb01c0c0061161150107001c05440e20000b5034542ca01842800080822100d400340c6441d00d810700425600e10350208038440d000f00040c49a05110842407035010480007080c0764805491540c0c1c1d50003c0900203c1101c0b90700091000101683d41440600e115800040707008800300a0f2040c001c00c48141500500170100a21080701103104201c01500d054962420044d652604550740c240c2c030704140d000042407100d09111048620404640142c9649140c5e9222120001503110070f00e1149070124484a401020600c0580f401c101054501c03900205c0c1d440340c01b0307d0031240c81c04409499240b0802d82001c107105200348964403c00f481e03084c40055440000300207403e80ca80da0424140b041501d0b48100c035499000741030910020204940044c0130400c021580e075551002203500c89150340c4102407866200e040801c00c0e0003010b0041c040220010360b50390140b8020f810410000f0300001d40140d806100500070034140340c404010658140c610700700102541604100c41400c10702080e0025001c002c0148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 78020199 1250 78018949 78018953
    0x30f060903070f0525080d08011203030207030512040503030411061314150d05010e06030a170703090e070305011a1e03040f15090314040503060a0e070f03030302090913 74
    0x881a602d000d54005401c050384203240c1001494010010118041030b40741c0c20702c032044000d07020b035404211003180d0140c0d40c080d43c4500069401510034860724149412007220750001911175801004540c2c8241449410b0054001c0681c0c0c618008480032245035000000b03110501803503620b401c3c0704040885d18189000b0100300c505e1803140c1d40d440781c18640c1d0100d140c4040140d94002540c580c6e005c104151a484520400880c000f5113401c3c442c61080c250104081101401d020498a004941101d101030001c40b01c0104165158004c030390a40400511201c081400c00c40c501e2528011486907402040a50400034a840401c1090b00c50703030802402041841c841c10301d5084ca081c0100d980a0095880c1e50b40c2d820702002a655083c030080180c4110034041205000a81c000040385000303030f5426016052010041000744540c2c02120741c903611010001c3c0025030b05800110882d030080c419260740c00c3d0b80f5501072020030707c190005c40102c0d4020030290b40d503007003100741558403041030303041c0001902d502c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 78021449 1250 78020199 78020203
    0x10b040b1806130e030421170d0b0a0909060f0203091f0b09070206040c290919080706030b0907090312090f060c03022103060402070c0e040809030f0609 67
    0x20030a4980541d15000262659541d00e0740e0306903050098030601c1410700500c0e480c1c0e141d601501030044140e0b44c4083d4109541080a402d4079015841580703a29039614200d981c2048c1d4000960405001ea15000da04040307440304815140245110f010100c4c440700302d850300e9000d49481248030720310340c3c0c81401040135103900060b04401d4400c011400000c0b0011134900d290203040c100da881b5070000c9019081c0038845034001070081c800c601802941000c2511014015201544029241816500d900c01c0c1c14071168036400a08850b10b004090244455004a032542519a243d0011640745c0201c04200f1500340c0500864182c807800311200c040300d06d001d00c40030b808180c20f408080c03c05140c1800321080e0500032a1b012018090003031310020f2480d500c0000902d03040300f5880840041c00b0f101c4059202810703416071000081d4994075118256a03540091000a400940040d15a010080c1d00000c803212114005030050f800741c00711554840300c2c5005c1c185400714060388440f03158040001c2114411740 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 78022699 1250 78021449 78021469
    0x10303031a01051e040b031003021201090506181f0e071d0f07110a08031602010b0d11030111031302041b08010e0a020f121501020726031306020d02010b040b 69
    0x8202541841c04200c00c404c001540143e030803a607124003000080c0710040d0700c58070722442101e10031125840c036002c825210500b42c0d040c0130001040795104402103011503003400f000a001400c000c04884000f0200503070242c080d03004451341b9941556800c1c04415400e028031020303019062588034490381c400c10b2415041000402084600c0000116020802044c8a41b54551407109040100d0f40c01c03034001d007007888581d07100740c40c240034405d82d0031003a1401034010701622240b024000c1c02e0028040c3c40d521640c85064864905a034195078660800c807043c0c02444c09580502240080041b0243c0e05105010480c0d06140141c040f901c1130718076950009500c9103440c1d054408602c0e45840584900807180701034080c2c054129084d060200341a4016071441798130302d2051324610702030b80b810070f0360000590310f4000d03c0c000d421401061810705031542d035240040d000c44610080c1107070714201341ca418080c84110b1a412480c0113820808140304c0c0b00d542401104c620380c40403203042007203903001400542d0f2822 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 78023949 1250 78022699 78022717
    0xb041703160305011406030a0c030e070303050a2a022202041e060503090d0c0f0206030106031a04020f0703030b0307271b080601030b0a091806051e040b0a091505010303031a0105 78
    0xf45688200340003c4c82500402f803000d40c445e0454100644900c0c0203031864114041c0b00d000a150007612049158030702c0001c00401c012017030184444076080e0240b0092500e035044a449215000d415010080700a01c010030040a40d5440c114501d07001e40c49405181c074095201504201d03082c81441a0141c010540c81000340ca01d0905202581152921b07032001809000044d41c400004000000e070240c2541001070100c800804600030f958003101000128005c029150805410501c41007001034040d904c034001140c001011210aa54cd60000565980310510b4013150b004025440d11000000c1d40202540201801c13000d9a041c4c2d04141d004104240c000d00035810184c48150f0f01e4650b880309000c0c030015040025061110355a240540032484000300b00840f50289410000382240055000141e8002c400001000c8580c0f2580c0b60000404030250030985107503501c501c07801c005020b090342e50100c044503103400f04880d031450502030100e070b64410007a000d4248075400354070583c0c0e0290844254103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 78025199 1250 78023949 78023951
    0x9050d1a07020a020d1101020c010f0212090609090108010204051f0c12050705070e1902030c090d0c0806040302100507020606090103080a0201020d0e01060311011b0b041703160305011406030a 84
    0x103503401d6412881c003a0702c518060b41040070b0100c0e0fa01403284100f50710135000820b80844026504072001140c9000117204164010f030400705552407612480b0000b0196184000c1c5840e0600701d002d0000354580c10280d0000904c0c0e9800a4200024140782808000c504c00f9181909402d00c03068070041c002c070828131001400c4d005002541420709025409442080360001c045030003480e00c940c03076500b0a02058a0700350151424244c0d0740c92000342030080702c1c42600021402070421590300248a43c1d2140c4031780c216945203a82034049200034081044034841da0280e402840030840343c0f03640f84112080500703004110b400c12010042c1d2034644050180c1140d5004050310360f01c0c2501c4104a00a020340080d1007070303d600308184100d1041e41501b0980999010745000304201c001c000040d951103132841981d003049a1107032807200100f521040000c0e80240039424500d003140b141031103546140e000710b8101d0341d034511a0030349024070b5901d4414180034000350300ca540100301c0d80c0c0000440300e010080444440d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 78026449 1250 78025199 78025201
    0x5070b070309021c12020c330c0307051501050a03030203030708150d03050403021504061b020402070c030303051603050c0702060309160b0c120304020a03060507170a02090109050d1a 80
    0x5446180c1e40050a0340030281130080303c070b841c0c544400008030409074800188180c0221022501c1c001080c2c10445401c0c03007107540940403812044000003d144412070b800c0009000f4482079403802c0c03008000c2c0c030340305001030850040151000000b40300c042e080030307003d00c20000c0180300107500041266000441c40c1000907555031500102c6100c012488035160304500450006010150800090300603248200c61070140c3c540258032139081405940b03c1c2000203a015002e1504880903510f0b01d40320a40090f101503d400c43e02c1c0c5880c400710030385500840000382d132002048058402c00030000c1c0c1400340381c9801d02c1309042c100039042503801280c1c8042c0c8603020000104107680401c009e00d0710140c1c01250a1281d4580c0d4582d00d01c15a088401e051a4a000c2c56942d04402c282107011030348100d6004211090b05800d50310362400621000300b44509001d9000a140250090030f13100c54843c40301400c0140c0d650001c80001001807100b070340b00074012005a000400080c0c94502c1c440169a1004001082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 78027699 1250 78026449 78026453
    0x2040f0b130302060414130c0e27151008060102030a030e24040209012411010209040e010b0111011107060527070e090d090303081f170c0105070b070309 67
    0x401400d580000d44c000c2000174006981a0907000b91034036460119541c00e4003c194103800c2c825610720400040001d007400310051014079100200764210f0303000c118103145201e581d01c5000c61500003070317400c40d101e03190303010100c031040c50b040307440c841260101e107016251400c1110000c0c6d540c0c080d40c24200140750b144e100e004900c40080100001c1d041c039041c640102c0040e440a020544042941e043e802034048100104401c1c0c81340d52014042600000c001c0c40d80030302703042e0172210780780c800190720060354081090440d2075940f0300400001513102c0c000020010743d582c0c00900400b40071088100641d05003822805a5251403007680c550700e030001030114540c1c0d03c0c0e60f40040c0300c40807000740343c1104400e02050450038400040030000e842c5c038030402c1c031215154000142d03650504d00c4400d80c001141c51805000103441420aa0b03008045c40d9401034600860080701160f559130354200300e102d14003c4a0303410b5061410058261003400a080c010701e00451a21560120030b4014003d1080c036481e1803518003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 78028949 1250 78027699 78027727
    0x309050c060306060c01051009140405030415050702090709080f070503061303021501030b04060501050a03050319030b0612040c0e06130b0109030602030411030706050903100b060f07121202040f0b 86
    0x705090710300000c00142c50031205070008c20400e070052101051501094084441038504c1c0036004540110083d41010719288003d0344070b8030001d0011080060500048005849a050050250883d0307166445094102455240f03004045071120b240303907004601c1044a44c40100c2d8081e00000b0034003503103201900c43e0505904d40a04101a880e400511400000c1031000d0000064011842182c0511050740da0344108404100310303010180c1103420400c07032003ea014002c012200e40120764200418685080c100050035134020f18401940140c426041104011a00040d440039010701d8440c02c0c540e0400d80701040440f409010641019940c1c1c41011003180c1c003542d24800250f5000d64295940d00d02844c084c80d90003040c40c0c008d402803140540c0031440c0750054041c0d0707500304d40150003400c501000249a2014040c4450300c29040282005680d2040c07600000500d4182c0c001c0c0200203541414080041841c0d01070a10994401d2050105000720029440020300f206c2d00d04c2d24454407041440e01c140 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 78030199 1250 78028949 78028957
    0x301270f0b01060f020c0301110313110603010605120a0e0705012303040f030807030902061921050f01210809060904140601031a09060d0f0605150a060309050c06030606 74
    0x1074811445200000345440d40000d00030001d03461a4240e689040c05171051500340c80144aa0040c00c03031051001602d07a1884000c902c0070b082c062003540700d80e40603200100d140d540c800e03000300c3c0000300c1c0041d2030050340312500703107940d040300a680007001901c28603001e103a101d084c00d011b282e040001d0340c68014040008450340e100c442140036031b01c42c1c0c0c81c1041d1078442940604000214081034490001581050081c03240c4039446401030700c0c2510300078828003900780c40010381401d1024003100400e200240c03038050110941090b16044001642d040801c503984004034164840c8401080007005072042d800d040d200340c2c1d400359011554039151460a800500306028044d415500f140c68248403000e004a40c00686009600c2138804000071b10840105030ba4040c8003a000c103403c0548000842d0140c1488400d0350302c501c3c059501030205a55658640d07044d20070035240c01c44143e174041c1001503240384c082c040c503000302164182008400707a10f944240e00c034007062003258400c0384d0200014440d0f4891030116 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 78031449 1250 78030199 78030203
    0x7150501060509010f05030708010306020c07081b0301061505070f140303040309030b150f06090f0a090506041d100c1101020d05090708031c09030e04090b040b060301270f 75
    0x5100941e1201e10060040c0c02404015000078424440700011902500449000d00c0b801d681e1a129a030858492030040d41c000d090a09031442602000940d03200c0900000b0b219111241d900c48554040d41c04041c00e440316a0860740c0050900000180f4803074104c1e080f542c0860b8080082c200f82d107c207040061020110081c1c040040c000001080101039000381c00c88240c9200d45902810340e291824616110115000056001400c86080403240e24001016003c081402070a058a01210002003032945415500040310300e6140c0041c44070528082c080e1b065140384199800c00072100c12a071442c4d0710700520800048041e981d50326161018880d4445800c2032251500039999408100d000c940100303811140d4640c13070b02035910f0101e209400402100c0b8544050480482054441b81c2c02e0001082e030002e0490601008a89003040350300c41c1e004181d001c1c0d010b8071101c0400d15040c1031240c04d816008102d14800d903d080d1400000040000403140c07580350480b024a1412954509401c00b44031030040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 78032699 1250 78031449 78031451
    0x150801050109060e031e010507030e07140d0602091504060207080d14030a06030209100f05030303011d070306080115030201030b150414031e0f10020304050714131407030b030304080c0103020715 85
    0x11b003c4a0103054000380d0007107090359070400151030b20a484640300c1341240111450308502d114042404d1410b50441c803a01c502403c0014078001400c0c00040d40700c22003442a0311f8050380490304000c815010702080d4001d12014014158240c10340200914080d12510b20240d00c480c00b00200301035030b80301d42c001c07000345a015020341082c0c00c0080000340e5070001489a00c10b048450000401d580c00d020007034904032503c140c03a00c20301c0255041c0300310346800010421000c240e5681c0d00065400c500b4016040030340407080e90514000d00b9400010299140c0400c802d0084117001c40c030070241e141e250100c500701d80402000705a084410000a4108000203144403070016984840c80d403500408a1030a0382580c0301d008480c4240f424034070302c0040c0c0c0004c0390003804d10380250780c0801115921998000d01c2900c014030b42e61000350b60400c0c00f0300b10b40300c035810700c140100c280081220301c9030180b050704a4000d0840040d030429181082c826a0380e0000202a810141c02041501c00c0081e000441c03000c8501104c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 78033949 1250 78032699 78032743
    0x21206040e03091929090d0212070303030614090403020d03020313080708030a0b0117040b07200c03070603090b04060207060914030c0c0406030b04020f12070906150801050109060e03 80
    0x81ca0782d21415844c00780007500010701541041250605484155951174011300f5400d04d408401046641203611205070780064000c0c4081645000500a460145101c0d03207001079081c0c2419014000141000040303070080b88800203002c082030700003a00d0404d1481d54138000d65241d0307650407130484c0408026001001e80302c0205840042026050107144205000c1d142040011100e8004585101c0c9400e14051072031090404a00401c1c1c1406017070ba4000c1c55424084100c00b99400c1d0360003071034801c01d0003040d20780000398000d4191800b070002500820b03007440c007400414902d88910310046405480208000d41c0007032040e08011160f04070300505900130b2440c000342e100560a9940b2940030307000f01d409500a01e03a100c3d00e20f20b041d00c100c00036a904840c41c9146a9940d5090002865a982d031035548a0302484c4c40400d00002008414003a0411034408100c40340391a0540e6403a5030200041814000e044005000c3e0303990251911044801c18680003106c40071f038a000c01d0901407040748880740d500c0490 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 78035199 1250 78033949 78033979
    0xf0e09130c1208090906060306060403060c02070e0a0212010b09010203040b0d060302060735030402040e10020d060501080c0703050913020c101a03060105010905010e0315011202011101021206040e0309 88
    0x2c00a880800c4c416501410301e595554200100c0b07100c110b8100da80700d0b506000074800b0421a52006e007500c103c50046620a07501c4100103880b00300100e58490406800090300803905030850441e90040c600b075149282004d0700a0000b0752280100d00509019540204005003d00c589411020040d500500303c07681c0c800759814141e0340c0003480140040c55034205055078910b6010310131000040e5950000c1c0b941151109c0d403c000213000d21300c00349500c0e842030015241c44044940b00034480d2084054000500d2460b2a001500c3d0b2a002800e102041038103012600200c0c0c1c00408681800400300d070046811075000c99400000d02a20050710654411100450301507501617024582c03c1201e48081c40d0022043c00c10076580d1a07090117080d00003500c400307041055500802500385111740050540d101d5010541450066201c00d900403030184c00802003000941d60420300e40c1c038252180030000c0d450b00114007040c00f403199010b0301840c02190707140c0c1440c480320b40034400d41300b40c01002800703501c00403051 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 78036449 1250 78035199 78035213
    0x5060a03140f0103050703020f0f040e06070210050606040306090201090b03041b05060c070b030a09060207080a080c07030e0609041d1006140f04091a0c07030f0e09130c12 75
    0xa601100340c24141c4010494030344641c408241281e80c80b0380100200ba04513400d20901d210f001c480143c0284540c03039000215071303030b80c011648000e0b84203006150074649031800030729090501d03145c0c2124910304000e025254484c00100c6040c1c0ea00004081007000381440100c80060159020100c120307004414001000340c05d01202c00f10012041041c180503868070100034091040340c112031810b40c0142c00c01c00c14225820069540300081101c0001c41071030a445507401ea038003281c4101c5105000281320401146c1040d0550f4100990a42c12030071300045580181c8042c41084595100d8040841c4a1019549031741016aa5684561580d041c810074541079035901d1040e490b00c65441400c141002c540400d4003000c0095614000b042c01d54078030118014040103102004042e81c5010480101041080711445801d002e80300f81304100380e60310b89504005000501c50700c621002c0103d640b020304042e584620303009401000600d0001503140c5a451701d6450603802c1d41c001121880401000c50600c522 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 78037699 1250 78036449 78036461
    0x210212060403081005090a0c090b0703080105040c03050c030c03090c0406090926090d020307050a03080a08060402160b07110d1808070501020a080c03040e0109061410050d090c05060a03 81
    0x100303854a003401c1e04c4209071008100d0b43c44c001c1503048011480010340d100f40d160480500e110311780c10710352000c41d104d41484100d80c3c400b0070240c000c6019032004102c03500b4144152901420b41e80341c2040b583c1055101000d00e884003421000016501201060100c001030100c0b012940c8018000c01946a5030349401024046014050362445900001250f4203d60040358581040c90a80c5862400100c0810001c8034400c540040e0782610410070003107019103a401c5400003541c0200001620340c0c04100008142080050001e802940180f000769034030031019011001e507a81c003a051242580d55a83c00b01c6080c0501c400a458510800340c0c8a41c60f150400801603c4010178900350541c10388561740c3c180e0b00c400f44e00c501ca0041e0302100f5460301007190380e800f03070006a41d8801580c0c44e145e80c41c540c08924590a07080421010354504081003a5000c4540101803110191010091703594403013409090750080480d040c04458480b84043d08011040c900c5001408006000980ba0722800c1030082c01401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 78038949 1250 78037699 78037703
    0x2d0c0d0c060212012c04050601090c090801050a0204150302040503030412020d0f0804091d1504050f0616090e04020d020103051801051501020c01021b010c0804080d0e0301180b012102120604 83
    0x102c0400e40542c00e5417a505182c2c85941c2200043c10704c2c0c0d2a00f00c180300180104200f1108002c50b10401141e41c041c00c3c01020701494842c8070150302d460a0400c0040310320136100c00c501c00d25104102c1004075860202c00e80c1d0864000017610320a4201d5070011a503ca04ad8100050802e440c000241041044543c0a00181c0b4968070007000301d42501c0a81c1c0c02d00c24000700c1d240d8440d50101c03070a8035114092003800f0354454864010384280c0601c1c140c034946440c40941e0030001100d4040702e00105950311061640040c0005401d880141c01c0503004581d040320740707140c06810551110009425820301c09006010a0182d030020440c0d4903088031742c0342d060031039034038214014021400c640d001036100003070340c8051180d14250707816014050340056502418860080300c8011007400005005d000030b011803496100c00d074035540e54095800d020507085a40e034081442c0e55588040c10000854510203410341500d04042d8030015814010182c00703010300d41c06000030750040000d003403c54052008a1141e002d54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 78040199 1250 78038949 78038999
    0x302091210110c10052502150f010b03130c17030306120303071b1b08030901020f0d0905040f06030b010303051e160b1005062d0c0d0c06021201 63
    0x11044400d50b005449400c0c14002942d101200e420340710600fa500c0640c2000d00100019081c00e80704000902e409050b010301e102581003503100d0304242d881880e11301e034001001c2c42490f016604000c103140031808090401c002c2c0304600114482040140000200a069600c4000c584841c070748070303865030300c0c2c0c0704843c3c1c2400f480700c016803950315000002c192801821142c4520040001e101c400004904100030b050f200000384015030200c2c03180360b407045c0000c0c200804c00b455031001c180e8000b9103420240c01c5528800d40c0807824549207154044800c4050324800ca50101d40c2d02400c2c003180020300a03542014281c003140c04000410581c02c40000d00c815007888044510003500e008184410380100c0c05180104241030006000141042001591200c0304001400c01140c68002051043c2c03c1a0511061140303c4686c0540617100010030501ca031140310b01070783c54a95082c04540d00e40c80000d00b140d007403020700e030042c0c800c00c0003a4059480c07a031030300100812690f948a02640b0b1000c14122030f40d00c1742c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 78041449 1250 78040199 78040211
    0x3060605480709060b090f060a03020706020406120b0a05011b030c08040e100b07050307020108090307050604062304050c061309090c06030f02070f0210020f01050906010f080604030f030b010302091210 88
    0x442c1c00382d0307080401c02443c804051402c8014010b459108908427802c0550070022440001c41e24405003014100c2940c0c4d0384545800d20044208403a01c44c40c50a10071034001208014682c0d00400e00c481c99404155801c00001041c5003e545000701828000d10b034040c08540420044841003030280326240c05001121004c1c1d86034840b250502c035a100141c4645c004203c6180994011151190401c88031011280340041644a903414038009440c1110b855443d444010b41c4807005002413000d0101060060031036061969813503a40700c004148407402000c010990f03d00112402050000404a07840b044c40350403805d01d016405140b080c05840082458020540100f407054802e40d02d005610000e4500100525001c201040d06024001021442450b8040811003001c1c000c082c01043c43c0b5005010a50510001c00340289454102c02d03000c3d4446402c1102090b84801c1e000c20369106424005180c9000b440120080d100f541d040e907070401041d4006008060f000500740810340c00711102082a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 78042699 1250 78041449 78041459
    0x312070f080c0306010c02010e06030a05010608060613050405040501091a04020108150607030e0a0b04120b070509010f05130312020a120e31050103120306060548070906 74
    0x161600946502d014484144005a01540214058113450340141007481c1031a0100c0c00055041d4021075140c028a6180e2004012558000003e560810070466000e41440d40350001c4006200c424451107119035100d4000c03030184138082d4080201c85412484808100506202940e003020301514201c0c00a045040000e880c48440745420302e417803100801c0546420301948045400b0240b80e007440e5030140d0000741c001070701211000240000d0030f4080980c0c0354210035040113503000d0401401c20b800e0090400582c1c2950303038013481420b60ba40ca6401e009072076103040340c050170402c0d000d900001c0002d4501002780e09010b0b0000b524035620745c8141d0709047c0d580f180320700895410324058603481c3c206071a00c005445a5401c8412810004508071350386000e880c58804260170740301700303030310994603881d1020b03141d0300140d80360107144003802079401c003e8a4017181000320a00c400582007a1005d03c404104040b0114140000f14190703c08000c00c0500350650110502d5100e41482c42001e00c05441d00c0310000f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 78043949 1250 78042699 78042707
    0xf0635011803020d17150102070b0a021f020301080a02060c010609020f0306041a03060129070f031209030503160e0915030712050d05220e0601080c16020f120312070f 73
    0x8881c1c0c0901742e1088607034480140c82404c20340001e2401e130540c002c3c0312003c10f100f04100b02502809029070700600100d45a0010706101c502c4100e00b03440c000740100018410b0840c0007800507455581950f11075503c2c55005240c038014206a0081c0c1c01c45400013480341d50840c1c81401440c01040100c50402420400503402d00c503003004c250880b0b41503000784004026000301800313400c1c01504c0d0740d5110781480c10b10200781a030903404801c040301d00064804204007450b40c02200c00030b80c5c400800c81000001c0280d20040c1a03404010841c0c3d000020988402c05401e124031050404a6006000348490b428947c10484540d44040306050280c4038034000001e40c500d0905035240c2490b04a005000100f1100030f040f9041e50080100101c0110855080030100001400103801040c0d0720842c10614100b200004000d00c0b000b400740140000305200d201c012100c5e48000c004030b80c1c0d040b500d000715030b07291502140f43c4445c110720700302c814003000c43c1e04442c1350103d40c40c01d48260f6031907807050542c65003084156 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 78045199 1250 78043949 78043967
    0x301090e1c030c0e04050c070b0108030301140d06020c060406060302040b0409080d02091c030c03030b04060b0d0905070504140a0506010503040f06050408070f060b0102010f0635011803020d 83
    0x82071151503900e9103806009500c80e40d8428894a4400900703d840401320b03041c1c0720103031401940700000003403410a201c2c401e100070f07015240d40d00c00355156500d4480303500303891041d0700266031103075189001c59030811030345904449a210001c000d50f4068601400d103c1c0c020580b610059024504051400c401803419110b16607425501c42c01140c10080d01c8038440000b900070050141d0000d0340a068082e417120146140c0c440310380300340c0e2001c201404524008060300c8656807814011424800c05010310588001510084c01c0c1030100016410302e030703082c024507014060f44466000303403510034880d94103617030102924400c0180d044184150b4684000441710381c4001c94024008401001e0000c0000e15290041500310f4080c1c030001e414000591141307840c24488001c211a21a5655400b00da1540c083c000c0b0880c080c800c150405c01c2c00d29000400c030184025115400c40c400079a00803d410000441d1086208031001c0000c01001c01684141f000d0a00340d400242c0c050b2144213a00d4505074440c9541d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 78046449 1250 78045199 78045223
    0xc080d020d090612090203030c011b030c090e07030c0207090608070609080312180106030813030201022401140d0f030201090201080114100f0509090a15080105090303010506030603070f06050301090e 87
    0xb14031540303400d180d140020102c128040703138540030410403040303404024000c0200c020608580311918041184000e41237400440040c0c0920124150400c20480d02c548610b9110615082c0461500c080180483c00c181580d000400024075260000c03520450000d069401c8d115035860340d03c117281d25602255528003d1034010803013001c44070000781c2d10702c400b1048c1c0c0080030503000003c00c040d512550341d40d45030341024202e503201581e00c0c1e50030415582c1c10455641442002d0003046c10140c15a5180c10300f041c2c0500416240350f80e0f14000707080c01e0b00c807815003007002c40d003180d6000c3c000c000c1850000d0107000074450a030f00094440c4004180044144180c403910341000b01114841100020140d80d5040c61040500c244030083c00565026203402000512850454000285c0f0000c40d03030000c030181c0040d810602079a031620701048205c00c40002200e05648040350f055460b0341e10b4400292500783c80d0341000d174045d8004007000543d140c0081c095416100c82543c148400d00201e00d0b2143e4078201d140803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 78047699 1250 78046449 78046457
    0xf0e030301140303070f060522020f040b030c061b010c0504180b0609040207050f0f0c0102060103021912030e090109020705150601050903010204080a0204180b07110102070c080d020d0906 82
    0x4010441e1803500710506102d020b011340f8200701c500d44800c00e10b4000707954261410354946c1c0070000021000c036100c01d001c05810194020340f01c1d594007c030b40c00c4014140001d000350303a12607580803265001c02054540360b07130003481b882c0c0c0d039180d661040a515038950000b41d51582001109904c0c0c0d0b014030252015500c95030350030083c400c410200c0134003800c0d0901c403031500b020013041000c0c215125800141480b038041e10080c640c44110031491071500032800803400481e0054425202941e90208a640c11aa01145c10703100700952403002a00c2c92400368081240c1c070503a28040810107403c8a040c042c001000c840f0720882d0380e640d4560101764030070328200070075070341100800c4074801d504802e1150b004039042c0751580c02c001d480c501107822a4410b800031803496120640c54000c500d081c0c000c0c55105801800040c40300c8002d0b46e03035070440030000350600b410b00014042c0361b0f4000e0025410f8581158002e5a130040d600c1e0f840c1c035208d854010003a400030060080f48400c0c51083d00400c0420300301e03849955 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 78048949 1250 78047699 78047701
    0x2120f060c030a020f1b0d0302030106050403080f0c1507020f1c05280903061a06030105010503040f0c060804030f02150105041e0e010b1903050706030b040912020606040f0e0303 78
    0x1201e00081d40014034040c070840d030902082c200010780c1c07070140182895192540e4141070000f004070f4a00f000030850072041500420050103c83d074003030161000c583e40101c000342c54080d141040b46540c0900c00405090b0b109000d024071080c5050110b0034046e40d030640a860f000d16104031280e07200c41a04481004010155240741c081600c00c0c40200a42d408140d00b00d41c141c0a50354403011050811258040060300821007070080c018148602e9114a800481540025a0380001714205000511a0302c0c140080400004c0600840000490540e0f0340580701c0100e1680314240075107000010384094000400001401210314000140d448819420a08110403030b841d20b400c00000d88100324200c01d99004250f442012140c0d07500801300c411011000200340c06215409011809408102d88140000d141c1810004900086500c0c415207100e8034020603400e031741002040c00b5011480c0000c1900d81d10100180d24140d000c1821800380c10226400d0140690240e404029101e1083c00c00e5120b0700108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 78050199 1250 78048949 78048961
    0x5090603090a02030f070f0503010e0c09060604030c08010617030702030616020c1206011e0b0a0f031b0f08070201060e01050f0a080d1d040513030e0f0604060c02120f06 74
    0x1031075108001c6012249404500d5020a0410f210f4010108440c0c0c022042840b603000c4e0350f2001005080d0603002001801001c4000b1640e440b145000790380290010f03c04610740d0703160b0b002110b002d19040400d4500b800d50f1844141c2c02800390307100b4103c1900407001d44a2000c0d1002c8210703441c035030300240202050348070000e401e01e6410a0004802c294850b1110300c07800b9455920707005180384070700b03400791070258034020540c03500785280501300a1030700da0180c060060351440d1741036030480486407034010502c00d1882c42c150010300710302254030444407940d0100c500503903020070f041d0718100c62990b0320206038071440810790032b0310603c0c0030380c0208240740e400500481c103240e0b03042c3d6881b403802025843e070140d03502400703070502011001d82e80004030341c40e881152960003114420400b62064408024a01d0203003001030000c420510020100b0400041c1c1700050f5961521032400c582004000640d150f81d1460003030818625040704a0003282c41034a5006100408140343e4110501c034805486207603190 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 78051449 1250 78050199 78050209
    0xa0e06040b130c030504050705030a0302060412052a100b030a080d15120b0c0715020a0c080a090e010e0f130c08240901060501050d2a0302190305070509 67
    0x31401c00d5040100101031a41a02150007180ca0300312144d20001028202030030300600323004098002500030384c455403c200000b503000070040da0064008007c0c64014220107000c0383c141c881e113070821a80542c0503454525510341c520000b80c2048110707003203480400c41c02170000c4c1540c90840840360b240d0010640c03000401c000c00001d01d91925114000100b55144101801d4860a142c1103503408e4030480c04000b042004220a40f074010741c0c110011414100c0554440300c0360001c0d2109144540e4011506a12444c043d0b030b0424415544161101e482d54100b00001b0200c400d42e110303480c0001810000000d2111040c049940a954000e81d0800d041d0b0f50070f5040c2d4207a1058002c1150b000d034000200080c0701c23109000d511000d0315986a81c1d10b501c10300c25841d040c4103078040e2000038140d14090341042107070303003000031241a4203a125011611106040c04250303004d52035041c414401c12582c054100c4554980e0090210407082d000104d0400c81e8000101c040300c10850385031010440030401245c0c20b10302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 78052699 1250 78051449 78051461
    0x804111017100602280206030108060f0c0f0706091e08310603020304020a09050901020a0e010f090608090a060e0f12030106080606070c09020a0f030c02150c030705090d0c090b0a0e0604 81
    0x1300c5c0c00700c41075100c1c2c2c0c04504903a009074403000044d0003d2050100c1e5021b00000c682d00030b002140300d1400c0c2440c00010507a5442410030051550350703112040020003408082c004041d03c0e00d02c0c41c4410b03910490074080e00d103602007a01d02c1e8841216a22070504d5200421310702000f90440c003013510b000c41c1061002e40c025480a8816640100310460018400a960040360322811030040096291101000044c150400d10a5294103100310320fa448200e09901c142003404440d4145040303030807901c0d1076002600306800514054003075428501410250000002d1780800c0906040c06c44044c040d01c0c1030000302c0ca0100303006682c0003914100120b9113520f800f801401c9501e00984141e00c801ea13031469400f0499210220b01d10128528007038111041d90544101d40b1224402d001a01c4c8081030010505d90520780101400080600403000c05c0e403140c801c100361103c4400207801300c0c40f40505401c08040c0800301d8401d10241030308040c00b850305410300d0120501140d0007403038528229101c00d020007000d451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 78053949 1250 78052699 78052753
    0x30503040e1f1e0506070203100c0302091008040b0c21040303020f03011d01050a05030307030c06020714060103050d0306050105030a0f091509020909010e0c010804111017100602 78
    0x4890714100782102d100c08410000300108900000c035001c5140c0c400b10110026800248124010b10108001d0384010804954240e0800c01c005481002b05c00c090300240140c0a52a40002030700d80d000540c1c40c0c00080301c6000d280641440c880710340d1041d51240e41403042c000b15a0500143c0750300039a0b0401c0008500e5040703031090a026050203042802c00d1251b8000741d0048100303407841c2582c143e8411719032400b180035042c107031640396005082c600466540d1082110080401501003140c0040c400d59906035081c45502a00b002c085401045001395500d40a00090319140141e5900d0840d980c0a44128422280180c50381c90841e907958105200400540000e401d4054556401400085c1c2d41504000c0b4400c3c00c417000510102140180b050b4440b0041c80c02040341c0c9861780d00c1c849141c0c00903015086403801d02c0c20090681d1507203403040f0f903003000703114180e08064120301540301c8035007211407810325100350311104025580b04001a5180d48031407056001580103280903250740258264010b810034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 78055199 1250 78053949 78053971
    0x736091e080915040608090a020f0d08040e07050a080a020c2d060a05160e03070509090f030309060a050a0b0a090c03060f030809040c090b030f0a0f0f05040b060109030503040e 77
    0x2150b40804a8144190b648202508100001d828000b0740d8001c1c3d1416049595000200314100392580070403e0b4070b041c1180e0500ca001949120710402280305e0403603028081d42c8002c0c90b81814202d102030840e400c0b611210f40801c46400024140030b07a07510913659a00d0a200c0207002c1000c804001e20b80c20311440799000d0f5582d40000112805800401211b4020507107104001000d181c00034516800c0c106c80500441000490341c1120355940d400940d8005a44045600006640703c0c003c1c1b040c50300740039a4191000f0301000c007c100c5500c01c08101584107a00b010801d200355568258450215084082c070203501030382c030b141c0601445050f0ba200c103212001505000a599481c0d418000e034910f0168000c460b5a500020103598500b043d02400601585604040c10a10b040c804003003004e00000b048102920b26403000500780a41603041581c01900d007810401020b040384c4c082c0e8020740001c94040d078082e160a00459440d502c9028180d080b03a070010080e508050400b04842c40c1c0c80005040d01101c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 78056449 1250 78055199 78055207
    0x3090f02030f160f06080c030a02070b0403020706090905070206040b040c1a030a060b031006140d0507080405070b030108120325050a0206060a060c060e0736091e08 72
    0x5032000c00020040074142d000500b00890144980784664226030041c00030300300565010009180c1080080f0381140d4074689558030b030741e5410700380c0000703018411001d01030201b00b5060000b0b040d000b2501900340d8509a0b5207036042ca484203400030030780d1810750b05180141d0004000074042540c0a8079260032a100b0381c1c0c5040002c0c0d0340c404100e4040048581c00002d0a80001803040d0310050b881000010f22202101508500c2d201d0700c01045400fa620800c0180245045805803152230041103454100142404000a0030040300043c542c0c802203c044130a485001c002185182d2900141c0e0b04a550340c40040082c01100506140385e6000076003451003401c02c80306140440200c810540100701040c1d5540d0f501d91070498402403810f200986174500845c032801d0240055588401000401d9170030003404030301d041d403007410149440041c3d441f18120800d1500c030001039410074207180241059200d12607a06000c940c4010044443d0958001c1c03003203030510a9060349800180c030f02d68059011310310701414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 78057555 1106 78056449 78056453
    0x90a020d0506091e0403030603050d0e0f0a05030d0c050c030106120203160303080a0c17040602090109061b1e0602030702012a1d04060506070501050601140309030304020103090f 78
    0x1003804c0000a030600d0b00036003210000b143e00208403040c405440c40020000103640154038070941c1c0350748a4010504d0920901c1c02075850040c042c0002c0d4146074400d0f102910160700840d024047c2c5140c0015954086c8030700002422044862034082007144105410091028940c081141c0400301c18000320360b22103a0036900410348a40001d040100300c101350780d003c014828200040500c0c1007000200035564020b0a270322042032700d0315040c503a2620b45c141c61800b42440350f07202e80c4005003415808a1201085a03074210050002c070b10301c4a02c1c60305d820050303078001c882400251f910f901d20462118a44e244202410742c0b00d03034030980403e2490100802400d4070021440c0b24040c400d00b0190142d40b254082c0340100b400402c999a200c5491404d00c2c040e14040b9079a501140c100c4c00c4d9940a0726150b01181d00c140140c001840c61a6079960054004041c504400ea4402080e0314038140 = true := by decide +kernel

theorem cover : BRFrame.Cov 77877699 78057555 := by
  have h0 := BRFrame.cov_init 77877699
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 77877699 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 77877699 ≤ n) (h2 : n < 78057555) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
