-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0037
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:30:01.298506+00:00
-- url     : https://prove2.me/submissions/a35ad740-5528-42e8-a160-650f9392f2ee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 6474827 ≤ n < 6654683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 6476077 1250 6474827 6474829
    0xf010b1804060f06090311010503060d060207021302030117060906010b0f03060a0306060b07060e0304060c0b04020123210708010501050a0c170702030d0c03050d02070c17070e0109060303020d0c02 86
    0x40701c1e2000340800700480020300d9450001805181c1c0900c01511044d02407d41c0b00c1e80d030350148044030320440700100b10740c42028080e95602d00a402a0308243d80003c84001c4500314042c043c40154042e0000b013441c0d5402480f162903880c500000100701f400103030483d01c0104140107201c07080c0c402040745248042d850f9a5840c000c24141c0c03c4035800074000c0c5042440c002134109444004003050f5000f21000d00000c0708411229640384900e10420000030302c141000c2c800700c2d0fa13080c1556045441454058610303401c2d200c00c658520f2100c840702a030020002925000e42c9660514908810707000405040e0615000c6005002520144282818070100294002ca100c1c480d1201c005c0042e030016600c0903241e15004c07410400d03003081c00c04034040e200b0004c02002c028020b013080c0c201e60740e065031b03103a280900c3c5c442d055004e50409a411a09640c3d804000315000070704541a40100f001e22004080451404095008944040e484010044d01e4048280b0100381e0102c0d11980401d81821b0181c24070003684 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 6477327 1250 6476077 6476081
    0xc0c0d02060901030e030f03010902040806070c02030606040504030c0606030c050f0301150302090408130605030105010e09040f02190305010609050a050f0903070f080d020a0905010f02030a050403021002120c03040302090f010b1804 101
    0x4014509002e87c00800802d900c4119409001503032980c030704031009550b40c02020307240300035105400ba506a00050006100707280940000b58414440c0c81d104080c2d410300da4581e4203071509600100c1c4d004095000a03c80d9040204613804161422402400054544515851140f215010180c040d200e90b20000d81801000422a14044415041083d89541c0c0d4000101684c00a005103400070b891044400001c0c0303040041c0724001e60308141301d5100c3d80345075820008a9030380300c60994411031030f091000000c50820321401e001003400c80300106640c90800030282c02c035280100b5201e5506800c2c1c0070f11400c0000001a40c041cbe03a80000c2d81e025004050808003114010380c0001c503407050001540e408003503800300051040321020b03201d001da0038041c0c22042e0b07242d001e600c841c0000220140010409481d080004514801d42401510020000c0000d00000b59000304040d040307550000034100114206001001c1d440400303803841c1c02d441e504210764003404c0d1041c424000f1641c0895aa801c240e030f90350f030b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 6478577 1250 6477327 6477337
    0x150c020a020604080c090105040501030302030904150819060b0303130e04032307150e0307020d06020909011d06010509090f06010e0907020a03030f02070c0506160f06020c0c0d02060901030e03 84
    0x1c2a440e103031555500c003d5904d200c5240d00ba0b000e080721b8400003c1c5420070707006190581e903154002d141455000000d01004200510098643e510349000c0012194418040303094940000010070600119900b0700c0703401d944040e4130350b80c066402000700c0700d20b00c28081381450654514100703211058440d41022200c4540303814140d545200c1c1c0365042c3ca1100c400c40020105140700b501d14440500d4910724a00440e400c031451412a0740080003144c0041c43c02c1660940098031940005043c50201c2d00400c42a0b0001d800403241001c1d90044902501410b40001d64004000d2034950f24110002c004210300c56005070202d8a01c1240101285807a80902100b074400e200191416001e0325010344000c1d5540c1c80300e070302600800d02d04080c81f11b00861a0080720741403034000d204080818501018448a80c0c800340750749030a4255038088000080c080803c07034107030714040e0360056264403002140c5410010040000c0d44a98502940c450060f01c500040d0b4801100900300003480d01d5000c402da500314070036 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 6479827 1250 6478577 6478579
    0xf030a020303070321020a03051602070e1303050708040803090a0e060a0905130605070f030c08060f2709030702010806030c0f06030a0902040906050106031404150513060207030c020319150c020a02 86
    0x10400087d6150b056000c58410b517075200e45d01a40e0087c0d840180d0702c501090007003c0030390b01607a0000384144143c1c1d65134002d95119240003883c03c0120384891502c2d801541202045403c0013a0102d140e1030180d03903140281c81503a02054007810001c00180c01c1e1189489244440c03500c41c00020210ba5121044204880c0c1181040c8018030f01b01c41d004211850501109010030300e4501c020110602c0390225500c60380000d08002040d80c40241013000800701035610b013030405094003a4190505400111501a800100043d511000103100242032114003c150b0380c0240c3c170448500616580c0d4400c005011001910000da0302d40300c5994560150070681c40294000d403e0084240c10000617520190494200303a400308041d90381d80c08a143c4a0405540c0500b40070740c240e40e1400b0024580d441503800c1244000d4201e88034036030360750f1007090341c008080950200b4101c0c150314065080034000c040e016000e400c4024898810b03642d50503150b14401440c6840c8582c0c1f86e852400c194020030180c02c1700350f0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6481077 1250 6479827 6479831
    0xe070311070b060108010b04050604090509031315080f0f0610051e03090712080304110103230405070803040f0e060a0302040603050f010c020c060702011b02100306050f030a020303070321 82
    0x221a00b00840c00e40c81c240d44031400030746581d000003440b090b0309003620243d6000625203031605140c82d0b4414041c01c0040e02440081c001003001c01008040d5440d1000145111204c0300b10039400440003521258004100062020700340c010070a0303030f2a0742d03000d05510800480f9580c0c1851594181190b00c1c1c0202d40c010424488090705100c160000d0300c001d14480c2140c0401c5800c0b103600c41030005107044008c0070003821f018051000c280000c13101d0000c10350304001032400050700c160003001441c40740900305030038008842020501c024843e0a200c45005401c501c401149800d281200822101d103140c4125a0310a10517000301e141941c440900300002c6400802c00e00c00c098507410140d4480c00c1c00310322400b00d517181c680310341040350002c50306902c01c40000713284074103100365a001034405840712040154000021002000103075141c03203010b0f01025050380c0015099040c101480420002e01c0c007600e10075400350f025080140d800200f11030340715a051909038908200c0b8891885010a0307610407440340c0b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 6482327 1250 6481077 6481087
    0x60406080705070c091a0f0402070203030306060d0b0a030b060405070206040503040501030e01020904021b060901060308090d030201020909090c010e0604050904060e160b07030906050c06070e0d05070807080c01050a020303010e070311 102
    0x1019560b44040c11020031247c100170145040c007080224401c03000000d4041e0014000101e0324a00180038151480303a50402180d1580c0020020300740100c2a00100e0707000e140131060086030f0806210705588100f21780000c1c501d90a16485013070f52030089210b182d041503204c4c152050340d0034081d0142d8031001300243c8290344800d0401802e2040310142c0704e0303c40b02489000300051203418140521401c0302d070007000c5c0d40e06d007210301018450a0300240f501903056640070445180c282e120b0401b1148941c032000087c0280b10020760004100e02214405140b003500c0520051203182c5d5610b4072036401543c03110f400580d40c50302d901110b0420700720305140001d034038040c2c10000380034030500000c180c1940719546100b481902c4810954040c021144a42c1040d488034001a880302c1c0141041201210000c06804800c43c49917542450005150003600c41c5811680c420407203100c00f086075050070002400c04904049103071200a617a40014403400d003805622202241c4020b0281d40501101e01807148026aa0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 6483577 1250 6482327 6482351
    0x4020c1006030f1217010504021303050610080d0306060203030f040c080f0a060b0405070c020907030b15090a090c0f1803020607060212010f0609090504020604090c080a0b060406080705070c09 84
    0x304407072400641381079128440200c80248101c003240b080c018100b095400c541d081805000094001c1504d0b0301d46200307001004004500204030301031080705042540d102003424001d4090500e0503441e0450145400c0c654240b1045030044140c1b580000303541c41c54941507681d81010800c01c41c181c1e00021a9014130030040e4074951020070705404c05401210301307002089000c014407003100c0e0102c07010000150151212401480c1200d0501e42100941c40d010400e034640b04001124006903c030200320b4201c0003d244180c9081621000d4002c0c01da001c4104941e44441401900207500c80001c031007001030b0900d540c10407400101c0b84501441d00641b2154691503185040b41c000d51107029980c0c40c000118000046003142d6505140944040307603603148440c1d00d0a010030b00948070141040341d101000f8800030880034a540f041601d404040d554403c61030410300d28036030848040900c0319002d42000c010521003150881001070300902a40303402c0340d907100d0302d017480001c440d1030f500003c080e541041c140f011a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 6484827 1250 6483577 6483593
    0x602040e040b040b01120f06020304060b090c0403020f0904260f030403090303080f040302070b0f070203121312020d030509010201020d06080106080c01030203090c010807090305070305070306110304020a030204020c100603 97
    0x85203100d048220300d80d1b40c81d80101c0440601d40203004048061070160350700001e02d10740145030014880c200c013080703040d14400040c00100049604100118002c50104203618240038201648178082d20a44803900b081e8a541c03000d0660304400c440c4800604103410a207180ca0740c00c03118203031000c501458807800c0c6450003c04a1081c0e20055000a1591003c2949242c038a2039080c042d5038550000c0980c06e141920300c0b941a007140015000720344040c4000030158800740002c540304074200342031640d100440c4818a21ba24516048108001541c5820100586480c0c0c00c409100d9010f0815640356484403004030302911071080410030b00c909040002032010015042602501c5004064134030030703020840114124081100c148030150300c0103079800f0040d405204140d8001c00a80b030041c0c0c005403aa114589401e24562040361164419082041031000c1c910a10492400c1c514044d86036060540020300c4040050001912035070380060941c5c05180d00b007000400c01c0401440034407590343c0d68104645 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 6486077 1250 6484827 6484831
    0x10203070306030212011407080a06081507020706020f100f060512010b010e0f060412080f0301060807080105060a1d130f09050c010219030c020102100e0a02040b06030118090602040e040b 82
    0x40034552000e401503101006000720f40490003442d40c803007800d5452300d60132127442c1009400000b00941c3c5d621b011501e948207104040320750007240b42d0400d95003031a280003450102e555001204540020000340d130700c82008100319180300700c950f10208204100c00742c42001425185d0003168000d85060501d0301900043d009402e03242c009072164271180c3c20443c10700c42c8160303460900c9680300750200000e100c041c0700321007006078035805203000506000100c94840100c1e0300070380107100440c04a000700711005600034026409440251801c0b03003858440b441c041c1c1a00320440b410140c00304002e4600d8900e4507008801c8640c13021402040c044501c007101c141d001420003440544180c0900c10b02c00b5810350000645200100c007450f061080d0b21506d031400c944008881e4401c90441c000c3d00e103001c0c8030107102c0c0901500b0341040c902420116907107104000445d099030220b14020801840100b0a2102e140e803c140900009180800d8515251800700000c2c41030340c0180200010210505c003e00100742c140d24 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 6487327 1250 6486077 6486079
    0x4050717070e04050412120209060412150c1116030308010b0c010e07060306050a050a0e010e070201020c0105070e1003090309140607020303180a08010902060a0e010e150307030c03020f041e03050102030703060302 93
    0x803880c107c4510400301030340b10f041c00d89074012000b00420040041054a42c3c14601d003c0c07041d204080300b1050140095036166007c1100051000030300f1045500284200d400310b50203081c0003800240346070750141c85890148140602c60402185405020b442908100c40b00d61111040e00c4002e501e418000e00101801e000d060b0283c04000c02c081858102054101709484805520b1031441c4c1c60200407003000368000b4a6102195020300042160407001d000d82c50003a50782d81c0362044010140b01c14803541c48007482c4080101401d09070510042500b00719030b441610809096980c0c0642e25a012401d540b141c0d84000703415200003c0d1808000b0285480a181001c084801001d019550005d85080c0d40300c0c680046d40c420010000c980016000b458080400c0e4018140002d4510003d80060000e062503469485c4165001040040c1c25a0500c42e110400745641800c606010305011040800d00030790090441c1002d20000c40c171b540d0042c0700042401540e012001707541e64a04440010f010380398610040b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 6488577 1250 6487327 6487337
    0x90c02060603030d180c030501050609090a03080106080702070302130b0f01050403080909180a0501060e060307080c0f0103020c0316030201200a0c2105090f04050717070e04050412 79
    0x45405440400c0c400d0044a0040045042120301142007005000c07101c5603041d282c00d01c0da04c500c0094002d076503036801140030344c0000a161a02009014414000074011a0706070406920000082d800408082c1034400038603015403140e5621800380d183c00d0f02a00043d50250f100c003420341070b41c1c01d50341012036641002e49081d090409800700547d528022808020704141c824005240c82d410000c1400341e02c8040300440305200403900140c1070920740007803419140350351181028450b4006460f000c44c1c00c10019802404043e2404221030745652070784002e24440d4100342004001a0301c07a405440c1e403494044c0030740c2d60398000740760400c04500f10044c0803030265003042c60f104e03151402c80e42c1d07508801011215051920f42c0ca144100d40e0520942801c44042421000c02511403888000030313640001d180c0c0320076969800345010131040491254801b48903600780300c02c02404a0340182d044010f850055840e0600351200901035510031320810041d600a8030b04000c00003800802260043c48100c035407a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 6489827 1250 6488577 6488591
    0x50307020a0f030506011e050d030302070303060e010b040501031a04020c060108060604060b03060405090106030803090d0305010f080a0f030309300801050901170309090a0605090705180d030201150602030409 91
    0x1008061145620000c4c1090708504010847e0082c102c2d078080084c2000441140c050740c40b400081c071036198440c004da000a1703000c2040d1080503090f114000180103841141c650075850944480540c0c032035401128109601c85c24400c600c2400b1044030030b000d610044c0190f490305007000c1815540c4c0400d01c14840c2d58490300b0042a001d050501c03e007402c7d10547c0070b05a166a844005100141c0070262180740d5941d43caa0700000441d031540003460003528250003500e003041050000505884042e0880100e4000301c074020030424000003803600a19900c06802c403130560641c103060700245440d12016108810003076040d0005c600f54031410984206821013002100c4903014229402c1400f40204c5410480b135030b00621003540c402d80c000468926100031246072003028000f00d20342c2c19056844400081e1507803c103102901d004a88039078054180c0c038015080200f1180300a44510304080418086c00c903aa043c54103043c03003900a420015810784202d11403c1c2d0f9044000d550758000d20a16a8031843c1c024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 6491077 1250 6489827 6489839
    0x601080a11040e060d020409030302030601020c041407080408040f0308030105040c0201090f08030c0c10020a021c050301090902120105040311010c0e0306040213060806010807080d03020a08040f02120a050307020a 93
    0xca410880068144a581450f003400340d40c104891000e44400e03400007000c4407000050303850380560004035100342d6000d44c50382091800a403070320078104c84451181e820310179a1240b024281c0d00407a40541139143c2410790752141d041c401c42d00e1049400140c80d00201070408005e00068600075030487c1c100b5503081003102e0442e14200d0881d01618401046408100c6800002c202c00d14041d60f04002c001c140303145040c0380d0451052616030310320240c0b17141c140c0100700c154015406216400540712100e80040c100458040024218401401a01042a502c0d49440c00390745903010710401c446001c03402008142891b0074080e240340b02142c1000655070800c1c4a0861003803080f88a0303000900007400614864645074200404188004903140d40d05507218000644100f08001903402400c40001034200981414801d83c200003180c0c4d0000181801040b001420581c00030b03030703254841d03080082d048000800d40f0005801030144030309043c0a02ca02291001131000101c010103000d4402c988461559603102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 6492327 1250 6491077 6491081
    0x51203010312080702190609050c0102060910020309070b070b0a0b030d020a0303020c0a0f0c0608010b03060604030201030c021f0204081c0806100201111611150d020703090b040308030601080a 84
    0x400014040440c410481c820540210143c0d50002c020b8019580004070a511400c1411402001910714070b840e13840940c1072040510407042e00f80001c1c4042c1c4201c0c03601c4100f455a070b0140c54486440282e0020019030411800c0c4841c001030034100c0e045a0f9a1511400c3c0090200e000342c4104152070300e090300c40b0b2580c2c0f038005850b445410194014111011580d1800e900a40252078008128040e20b02d881000450b815071a01001d0711900d0311034038003030402c07800408944050700007605002d803c000340040c643d111010765044a03070920300440c0c8245288000c9007819084188040e56503072000c6a01d504654503005402518140c004480f807030300354210441c600382050100312001c80d01030400709040781404294940b403003409000100320b401003443d1a01c034642c000d450420500070384140240412464034810f80d10504111090b442000d42085038260b14800d194040c400168001503840405002c1c006000041183d5008140c40d65600e04001da0154001c981c1c8500203036603600001c0e440a054 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 6493577 1250 6492327 6492329
    0x3120c021506010c030c0c0905041208040309030b0606070506010b09011103040b03011a07050f030d050f04150c140706061706010b090d020111060a0906050106110604120903120203040305120301 85
    0x340c54510740d41c03107840041d10043d5200d181079007040f085042c03510202d903980b20384100a01d1a80c00006451816080164090b40e55502d8203080189441c14040400d500c88040d00560303400c295002143e40760070700040c0c420300c00c1d248020541e001d00000003460f000b480000d4600c03048203890f0b00c05030340495040551a84942d0081c019540c4042c401407000040c880e41c080c0810040d0718400c0d2529071181c6403149003541c00340041031035620014461038620381600800c0e42041c06501c076140c582c2400d6585206110358045950a800e0340d805285481d00d00c43e440c003c82840640701c003241c1e0b560f854204240a0002401440003c48158400d2002c41c5000200039040310305c0d1603c020700301106c1100300400d22004400580c1008000c01c01e0141144041c080b0354002d08820340c0001c0e64100c0c6281c40390680788140d0000f42844100c41011030b60040101e030035980b20f40c0c4540c1d08070f083c070401d0905460100b0380b9000940700102a1046500742a0000020403c1d00c4c0104100c0301d140b01d0014441201d4402 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 6494827 1250 6493577 6493603
    0xe0901020a08130302010b0307090207020f0405040302061f050d050601080f0d0c030c0c0902030705030405010506010e06070201030221100e01091a060c0703021c0b01050d0c0e1509010303120c02 85
    0x240b000010034543c115600070703400511030720021a000501c100001d103840c029070810001c40342e000840104500e4000516441c03c00203440500040c6440d48000e502c0b4000180b445840030200802011001c043c101c1010180c080204400c1d400341c02ca0a042d80d0300c1c5e01c240986075252003035105041603007000203515614520103541d816000c0036107903070440e1040a194021207039210701c01000700710300c44940003031445040c4075030b212902c0c2e25041c24560300750780c0041c0480f0706109680b2110310040c0c0b100b104031030900e0740a080150351130011069201500c040300c07003003001c0240140309201005100b440c0900890b4840f6030450100e9803101c0101c0d04580c49021240b08444d000c01c05c600c11810140f0182601c04041020b54445d07039600d80104e5400c1c070040c184080c00c80c41004112007013204050806004d441c2c04e9580c4420320040e580c50010010680c050302128203540c0c000603250b840110942c84040034007500c020301c1960749140280c00002805810784d0141e081c4030808040314400258035a002034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 6496077 1250 6494827 6494837
    0xe0102040f060f050d0203150102010b0f090c130305010603060c0815010503010306111201030c05010909050c070605060a03060216021c12080711031206030c06120a0b01030b040f05010e0901020a 85
    0x1c034003001514403410300c0c840a010302c20f00f807004580f11780c0e0314806036120b02c4986803020460000700000a00b1100f0380d0240c14802c3c00700307002051039620f4640c500c551100403030b08403c4d907403220ba0a0000c2c5505069100800c25070038690302004200c0d947c6c1100c10810055113901580d82c840800c0301071a00c1911aa107030002e00140010404603401d41c218495206445c1b60551800424000c0b500d00c04000740c006946459a81c5400c0026580c8a03900348001d040012040043d030a0010203c40540714101010300510340340d1020440310b0340c0f6071850a00a40c1c0c014021940d80c03007075000e44280700b49000800d80c410b00081c0303c05990340d4a000680042d540e8004001c0004807040c0340c4c01c0e504003102800c00300c02c10078803224968289508000600d84440000c130f58441ea071400404140c50128840d0074517020f51002e000c40301d81c1d40089414150412002c0d04007160308030000004034020011481103da0180c00c00240c131103842090713030045040e51103815204009a0f1902d500f18247d1003400900c1001403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 6497327 1250 6496077 6496079
    0x406150506040b09060702040b03010911030d02030408070312020c030a0f0b0112030e090406060503030d0204140609061b01090602030c03040c060206070f08060d081309050601020d090302010f0c060f0608010e0102040f 95
    0x172414500402142d44000c20019202c0500b1007c282103645141c42101c60089031050260716243c00c00001503e01e9080c4009c600d0320b4148140280c58941911008000e000b4407460700e000c0d503009019483c0c440101800321642880b190820a094000200b030980340ea001d04c90012910b10300709a001c0e450b1a4150b1640f1940e8100142840b4400c04010001d84889030b640002203041d5805200030502750010440150b1034604046003c0410b800da00b0b42d17a48904030070060404c1544603101555180084441c602ca000740c02403001c6800340c1003042008280a100000b005040e01107080518040c2d40900510b451150710b600d01a070380e810301502c0b0000440c8001e00800714203442083c415a21100c00303007020f001e5865035507881c2001e80002150b000100d403065801d00100030240314203940090244010100c0300718001e4003401d460210702000c1e04000c800b220850320b960003999840701540e4400c1c804c10a821028660340014a00c501445081c2e50924600c0300f0308071014001d40e029149036040420f511 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 6498577 1250 6497327 6497329
    0x6060f1a030405100501060302071b140d05010f020406031a010201050708060418020301050703020c0d0203090a060e030102090d05030307030605010e090c0a020f2e05150f060706050406150506040b09 87
    0x281c1004004544500c558801d9200c01600d030b0007401e0080c8000e40300943c4a01321380c1341003003241c0780404070710f0500c2c1403410082120280120500ca10448242d40705d400250302400c04902401008100b00e410078000180000c17000d40c180c2c400301c5207100b06c058407170320140a00012030a036201969460000350080000c61090301c0d06511022192400010980c000040359001c030b400c0da03000b100e900c1d001c80d0f408903d0401c3c00000b40400880180d541c4040c1d4a003280e26400108105841d0244404003e40c42c4014075140c1ca0960465107020300041018054245030701d003903940d80d0301c201c6004000900780900024030754020070300440100b8005185803c50394400407408a0394203c10b12070021845040b1502d28156010310695061086d41c91503520301c00a00d4a4200b038000c40c4410809180d4a400208074140c42c1400d00c02003e40c10443c3c22265520008001030420300503140050451441c0800703100c100b0080307074066080b01040c142002550f0350b0b19010040c184c0603034030603003803007480030002c034206 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 6499827 1250 6498577 6498629
    0x30909010918170c010605090403020607030f0e0f010903020f0c0307140103060302060309010c09150f030902010203040b120f01090b011d0a09020703081803040501020a030c0203010e010203070c06060f 88
    0x2042c642c01200800030140e20788440c2d00030000901c0011500004201c94040001c0c01840050300742580c801d462800d00d47c0e07000750364040003048c580805640b840c01d90455403035604445081d0100e041181c03048504500071600034210f80030201d0241c400c8559500340100003081c0d110a080004003e005210325240300e4040440b03a2804150425948800200050341c9010140d4010032244000040c2600e05c004040c10b00983d41d003015030306000c0090125002644249049401d100740d250200da05415440103034a1400349404c500300001d40401d0b00d01a0307070410034940748100c0c590303e0f24034481d90b80e8041240403036050202550000c1c107400c0504940d00302102c04888d440101500c2e0106450b0349410103000c0340c209110803000a6108030601900704184014000d09a4000300610302e403e203042c00203544c0d4408100010709100e0031906120030355030300390702600508880c40002d6640c1e24200d10002c052000b68103045654a1a094000c80c1c0015800074903010b441c002551200694226555410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 6501077 1250 6499827 6499841
    0x130f120209090c09010b0d050109050112080706060510030b0405010b0412030516060c080402030c0103060b0313020103140708010f060203040b03010b030405010b030a03050301051206040807020f030a06150302120309090109 97
    0xc40c1c8900700c01c0d841c2c6078460f000c4d0346000700101411191201790041440d4261441030307101041c1641013400506c040b0001c0100901d2499000b0042640c603001442d000026007465484182d001c1d90409482c002160144c0142068500c00c03142044646e8031040000e1040c055805141d06c02000310324036a0000340508024800729040c2520b1080e620560360395101901c0c00c6101040000324200c05000171800c1c108000ea1f05d8002c04d0805015080c105001c10351030307000003060048030a00b880300c000c0035a40264071080044440c110f0142c440c0c5001c1c0360251203007000b80303c1c0da21030090483d400509a807010069909546100450501e140d01c0c0c00900e070216080600180c03103c0d5641e41009000d550108a000402442519456100d40c90304041104004070820401d1064111a0400000440d03420880b11f40342d42c102c3e4038851320400503010919280d0b1816009160030701d403403030807030048400381007000403a482140d84001300b07605003500e41e0322401070005881c1c200c104107005100d0044144c100c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 6502327 1250 6501077 6501091
    0x819030e01140301060302040603060b07030c060203060105090a0f051804121d0d120207050102010908040902030705041505030a050601091215021c050105030705060903030d05090102070605010902130f120209 91
    0x141d02d840d808103251205500c00e0740b261010941c0084d0400c40b05806025035070050281480303032420720f0380703549000d1b00202d40503000400103940000080c580e0380c050f0042d2220024041c0581c440d06448888034800d845482c01040d00c00c01c2540341c00d103d540c1480e007602c2d10840e0b004801c2800f80d4000d4030b00350740c104000c91340814060281c0111040e0740d00c4840348901e005000303950701e00e401d05202d107010741416410f80042d411a414240d1a030045070400c2d01300d504850211000603540d544810044640b40241d07041048803802e54034688081da580107010b5802072000307003410000b80c0c590b54010f64018146c0d02c2540d894101e284030105c0440e0b00341c60041d104101c102c2001d494a0300c1c0d0b8035440c0341100400011107205603500e0051180d0300342004000c025240544003286400510400659a030260300f088412054440c0c00217200400300790141d5444075840b01040c845561a0071800029410a008a1400c00d42c0c4010000f0300e2810030041078203c6014910616440d407850f001e100031860001e100e4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 6503577 1250 6502327 6502337
    0x201020f0c0a03030c020d020a03050904060b1201030b060f0f0f030f030c07030c0e040b0606070c030206040f05010e0a0609140307030f03080103020102070602010209030d030903020c09070809070819030e01 90
    0x4495042540d006100469110300607154464291501030100c40240040904550240d80d0400009400040d25a040307070701410115150000400010301912203a08160b41803417020a03034440c00340407454082d050303901c14004940140c3e101d40c10301c0807030f100000d4800d61002c01c00c0c03070801150908140c1803500d0f0740082c041d5841000000825450743d40211040c00c8241d200b00c0041060188400d18200948100c030480405400c1c1500c50080d103540107004548100e00002e4048104294848107000465020b800541c07220303520880c02001e4141489070f42c0c041401c0c2a0300c06003614001012109803550342e2100c0400c2d40c1044400711244080580c255003510900e03001001240150703002030035161080e81ca1046940c107601c00281440c55a40c480815680140040300c00f550300852802d042141e64903001511003280d0608030310f0241c00c0c0641a810280341d0b414040c040b17a0140c00d0b144204810b90480d00a250784101c01699290034100741201d01d00560f40d5070002034861a824a081c620514103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 6504827 1250 6503577 6503587
    0x40504020c19110307061407030e0109090606020303101202030d051309020f030108250302010c1502031305010b030a030504030204020d1104060f021b060306010f0210110c0111040308070803040201020102 89
    0xb01c00040c91411000396003e005003803040100b49000c00404001c0d01c0e01d49072900e00c000241011250b40d000d840b000a040c411880400f0199174491240305006181a68040c800c940d80c83c04065200c2d07106540c02c64216034203010209810002c1003e80035004c0d0f0240c024a80001c44001c111415044641b000c4450038035400d0001c0d00000d00c1c000340140c210903035000c6070780e94542030701c4510304411805a45452007071400d403110120341000082c402c90381c081c20250000305152a002000d00946d2040c403420138030110a00c0848540000c4184c0d009105400070400c0d100b0010815a0b5400480c5000380000d01c200828801820150050300c0f1403000b0410124004c0c0004107850310301d07001038001c24000343c889156403400b550304000c2ea81011211040c68001c03080305802142d21132100414650500550490710b85402d4400c205026000c1c0c015202005104152404e0520b40c1d40180030302c504070740c20703e0b884107048880789003207404490340001014174140140d03036040300c25007004009a0555600b440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 6506077 1250 6504827 6504853
    0x30f0605100306080d03090c060320030109090c0821070212070308030718050105090603100816080f0102030702030a0c080c100605040e06090318030a0807050a031b0503040504020c 79
    0xc001c904141094901103025400d1842c4286000644100c580816051044803c04200c2c00c900d03090a50b070b0349250216000502001510245501301410030400c0c0c03000000240c400b0141e4005005507114071a03601e4050755400e4001c0c1c2c0c8081c0f06402a40042000c00040c03030516180c0d00504240c2d101804035400784018100306400d04106602c1514140800010002c10b25405805256051030702802e42c2c0d45e890900c0700007840e9000384540b00340141000004a05031080100d2140010b124050450311141c0311094001d0644060384161192441010250302c4107100600a992040341694011810480700350b004a4010144080039a4195810001c81009150134840c19201c201e50b80bd0204460f4605800d000c00c0720700b000c0404c42d10b0380208092021400c07020003110302151038a0030320520405040c00083c24501d41c4040103012900c005081c004101000c6840d08c8102d000340c9490300984821140004140c1220038000d100f900200810720040c5031550142800703001c02001c0310f09101d80c83c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 6507327 1250 6506077 6506089
    0x8010207030203120109060b0304020d030302070b010b0a030c0503041e020a09060602010203220c051e060712170c030c21040510060f05010804080901020c13090b0105010507030807030f0605 83
    0x1460a60058000040d0913003884a889141401040300d40760070403000d880c042ca90b00080c08041c200030b109140f21380281f014944039405640070710350000c10f8584d195035241001003d40d40900131082c040783c1090b40d400170441c02442a00c0c8115000404450300b69403c010ba0030804106520482e40048664000300b00c0d4009441110094001ca400044c0e490030301856400f05040f00d0380d54903640504580b602d000294540100710101d0320152600f425038296100e404504410030341c04d40350003020105a800c10f100c241402401d4041c1d640e180c07049441d500009410b150f0204a80b0f07004103d40400101e403590780c590004141210703070380003150604017154400d060814400e4409079800d43c04241d090324000554441c980042003070440300e100a5241000181c030084004102410080d00494501e0300d40e4000c3c02004025136005200030607058102805030000e0060100c1950341360300d9007001207038650044084aa60540603207810a4594406600b1005001d0350a40000d25585860340000c50380c51b0302c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 6508577 1250 6507327 6507337
    0x31f060305061309051b04110a02010911040903090303050f040306090803040209070305010f0504020c03040509010314060a05060d140a05030f0a03050906060d0210090f03060203150315071107080102 87
    0x203550041034a0030404200056032201809042d803035442d00c01e0103800250001240402c010445c0c1280100c00781c9103000400410302c3da40314400c50176000400c071b50b000e641940039800003841420304c240100800340605c41110383d00080200403401603502800031034007460181c54004049640c4918081d01c2c2d0b650001907034400b4cc401c4400010100a02c0114a04040300c0341d840681407801b00103a40c03501e04400141e01c103a00c1181d00035980014034080c08a410310483d0702500c3c000d01490140e59480c0b50954098a0507181c070b040300c0c0100d4012404503484c0c3c6c01000c1c0501401803050300c0a56458503500c085032001481c0c00da1610550343d0310070008806002611042c1d01c40c1c81559207411001341d0107015504018080502030700440c0800041f561a0002e80300c00c142c0680d00d411072004018000d6655620300c1d005605918007040b80003040141d6900214030a1030141007a0020842d05001c0c1030303486080200320042e40c41b07204d000030340f1544078101c2415607803451412a41410380c0d8100e120300720b9100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 6509827 1250 6508577 6508589
    0x30a0b0105030606040b0f0609010201021e070c0602030a050a0305150a060e010f08101205030c0601030503040501110a0f1e0813050901060807080a1802030d0903030305070e1302031f 80
    0x589401045240707070901c503166125405440500084200c41c0004c1c020000c03d181d29807280d4008582d07140564400d40c1941c2605003100301d099142c0340d1240d21103000c0d030131981040395060303890340002c00c0c014804015100da804c4640c51b42070030b0164000d02640a050020000d08680101200c2036040750f071400603420041066172280c291040242c00018554000114007030240100c180070711061600c9440741d9021180013000d0f04040c4d1140b850402c0c2544101e020152061042200100502c4004402001126000d0302c680034081040c0c82c4058607144a160042d10090960345ea03040407440c02e400550200c14844c600c440150340a40e61002150868035030b28142d442070a2040c403075828110002800360415040500d01440c080100400d02c03030340203014506445d25003948082400c3c40c00061104240d00909070b540e500c401c654000c140c103205200560000c2e04000108500a01030828618542000740004d092002e641c910340340690701c01303002d5407003002e51411000404034102d0800005040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 6511077 1250 6509827 6509843
    0xd0605130c0801020403030212070c051002070609090b031f020d020d050105040e0109050303040f050c090108060405060c0c031b100207080a0201050105010201140402040b010e030d050904110c0303130f02030a 91
    0x44905082035508240d411203020b6a104200905c013080e00002c0c08420104400030b060340d5418580350100c0c1120140c2d1005400803829503241c0400c507004946030042d80e0315070361201e6034159129a0031084e220b500c07541d541c1680002c542900c406281c24006c1d0710031400c0b0300015150248141c901c000700c4e44400b600c01d454503600d0006104030720745400f6800306440d405000788a510680e403141e5440b440060402820142005296010804144011808800004c102c60002d40c3d40700003241d140d60702114216040d014070b4000502c0c0514035000e41d0282410307100114240030810b24110b4501c41031000721185071180003140d2a034180e240c00100a03082c40b440383d282d100e61007554081c3c00c0d1071044e0040d505690500d00481c903960042400142e025070100c1c1d0100300c4051000040c0d1318440318001e016014098081d620700c200b034000e8002c01107004160340401554024006050290080f0300f4402342c40c1e042040802c205080c440d200082c990700404544038000b000354002842d00c1c101d40c2c82212114 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 6512327 1250 6511077 6511111
    0x901020903010e0105010e0c070c03060501060509090601020106080304060f120c0e1320030601030b040c02010203150a0e0a020a09080102070b010501091d0c0a02100203090105090d05041d060d0605 86
    0x82002e000c0c4400c3e60500e04001d01c410750401c800c00d062814020700380e50221401264000074403508440070340041d5003280041055585501c00100158896081c0c18080c03e0800049440d0b94414845c1d03408882016000d1410706040550845071032032144a508200050342190140890f102e103d000c1c12882c2c0c58440b01c207610380110900403c04140819602c1070752500d40d110704100050410b1889c1541020581036030703503440d0700040e0014400b2614542d0400d1602070460912501540214000d02400080c40101201242045600c140b2401811a0703d0481808100e541c1f5043e000781403c4219070a2601c0c0280e102c141c00303401c80c0c0000901380c0e69242440010402542c001521101030800041d007507116a2601012031844a000382000070305440000318401c00a1080c01500002440084159917a0401c040700b1400b90030309442d50300c0e9600402c0c40e0409003e011f8000ca4003110300c22195200e40c004004441700031508001c1c08950420342140c807550006040d4480d1610405038030344e1040c405 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 6513577 1250 6512327 6512329
    0x120a030306081c0c06020f070311060a09020d02041505090a060317030403020c0d060b1518060304020a091808040801020a03050105030106120206070c030507150206060901060c0305030601021509010209 88
    0x95030182d40711020301d0300310f44007074540450801d0030404211510309050401c0300b954608400280300b00315180100c4a004a4520100742d805458811808004000c99909407101060b120444205401c0258004403002e4404010305283e0000690031080c0d80c5400d1020355135601088a05070210f5200b070840d50f4076082403041151b038000240445248210a6085180075900690b651984046040c0b040440013110010054a0741010080c0d0801401101c1d03103124004050350a504000008205020b140d0200b4015041c00350503a84199001441225082d180401100041000c110848030315181070440c0804100d0600c01400140340d000300060f554205134400504550043c0c104c0c03403299040000c10440749041d42041100e82e82c0441307000e40e550200386010081003145a00003400360040550000307800c041c02c0e00741161100c4607001c0e5006a500c8008104c100b080074007a220102e03c1801000d40032074480ca020310742c0808107004548861010102c0c0178114282190b1103406a034002500440d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 6514827 1250 6513577 6513581
    0x60312071407060c0c05041a060f040501020c06030606040b0f091f171b0a0203040f031a070e06030106050904090209010905090f0a0b01050103050606040b0f04030c12050c010807030902120a0303 85
    0x200f0051500341c1c5520015070f100480c3c82c20a01c20316102d0b9882d074400744003000b10039035560790740c840003405181d41c0c001c2c035100347e181c0750024800d441c0580502c0e00b046005007003000c1120b00c11100280000d1909041c0b00801005400020f0f400041c1101440302d1440783d215400075480107241d00b84102442160103000802884a1541091802104200b0321800c065a0101001400341c8507a1882d150b0807034580c01c038550301855114814420b4403100020501040030700001f4001911800481c0e03a980c0e544007034400810350032050303401c108100700402c0302d10320801c06003486040c01000860f05408940002e402c8a1084c1c0042d089199100c09200d0508001c01018036010000780103460a0707161a240d12a0700c1d03d0520803981415203e9001a18541d9808201d601a0840c2072140e5100d5040c0d401040c1c1c079820038002260043c01150000c50740449080d11400401c0c2d02500408084d030058004440045014113060181501c0700050801640c03580400088040754000400621029060042c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 6516077 1250 6514827 6514829
    0x60e010311030d020a0303051305061006020607021212130b040605070801050f01020715050708030405010209031b03030a1d0d03050d1d07030f0c0f060f0f03020408070509060312071407 81
    0x12003944522450180d5130340220302d001041b901810700040d0381c1d4603803034095005440d8842c001c0090081c0001c00c0412043c4143d4402075440302d600312002e07942c03001003e0b0f1380c41004500710840c0e0720003440103113400e401e0284456480200c01a8030054803503c7d81d24003406400030781d822540340e9194003c002ca6141c0c00400e4600604044505007518030402d80042c0d10307107405016908214038160101c12040b4041d01c11560742c0c0381c0c02800300d9581d02e45030074403d00070f401c9805600d10034050a0700000c2d4201c03510b00c248954410040207146070a1001506407600125640d98000dc1c07a50801d02c002079a071041c00e0205c44602949402d03a40d40104511201200c0350440500818682c28280030b014400008641c8142c0b81d1054100501e80c0303003030406002050f07442c1d116030141d0040d0300d40418503a80c0500b0b4644c40980b5910352058030504c4c0703d82035007a80581d003e0190181e1110000300603d00d0604034507504240c014003624042d1007480c0c44050254845542a600a901c0000c8402822000c0020b08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 6517327 1250 6516077 6516079
    0x409111209010b0f0405060a030b06120604030203041401050a0504090e0f0304060306050405060603040506060d17030703090212010e0309010c03030e06090706080f0601020c0103050a0b0a0e06010909060e010302010f050c01060e010311 102
    0x1440c82d1000c0023401d4640f15000c003400c407940b0a00054503c0d1242040790340c0410b05582143c59520349450025aa03030320074010715001c0f405c00d0b50043c000c1d50140c01695060212612500e0800e810200d00200501c0d540404107000d1180350120440402c09000410141005550202d20f81d4104400c1c40305449021700494001c038410406c06c00801e10114010740c101208032154015140c035410300d40f8041d201c540002102145c0003080c8840c80b40c056119000182c8241d511181c00041854400e080301e22400400c81d4a070801c00c41c0b1a019031103507a0b89941c80d840b07820000b0307000c440d202505180810440b85250140e011050a004181c3c000074070b40d070300050040b074094030745c50a02e0000b5107410615140c6410705403640c0100e0703400c0c1c4194211088841000d03145217810f070354807203840c008840700359101c0b40802c0c55854081440001401000c058a00501c400b1005910b03550044590015600703404003045014030004407544028042d038002041c140c041c01815504600302000740181c0c030140700e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 6518577 1250 6517327 6517331
    0x603020d0e070b0a0f02070e0108010506040f140a0b0a081209120d05040603020d020d020c0a020108090d02060f0705070b0f01060e01030204030b060d0c080d02030705060907030201050409111209010b0f04 89
    0x80000f202d0280807100a08064138052000a1602d24140d284c0581d07504007070b43c03604006002048046056001d40c1c8200300c1181c090012881d60044a401c035074400289000c06021000000e80e00d0142c4c1d0492080c2e460054401d9038425542e840c020304150360361b003402c8608a00000d408455140601e0b80031001d0341400041d005000c00c500002e07096100d68401c642c20b041d0045880000c5004550580d81d0076600d20405640d80e608541c521600d0340440340049021540f12008151a4400010708141c040b4290b0011700007030710713a4213410801d504010504800c02c0b4040026200007400445102c1c010406c0c405801080d50400802600d003000038505141094810300c01000869808450036410410a503603500200f10325084c050322245068129150b50700c00c030301d00910384542c008020402c05010300103a900d80d813152402135071210205e1001030300080c01448140301401c01507101c00f15804072609940d180440140340d555001e0401c0b5600b400320395484410b481c10741000050325210600440303003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 6519827 1250 6518577 6518579
    0x5060f060d120203131205010c1103070308040503090a1712030c030c030604060b0c0309011404080c060c03120f010510030b011b14010603110a0603050105010c020108130c0603020d0e07 81
    0x1c103010400c8040041e0482503440b0105180038004e00c100d981d1828250002e45403540c4614042c40d1420210000300c40c00e61804044d0300d036081c801c00001821140302c0025500c8d00d402c0c1d4404803620903000d4400d903180d02042000801c01d5032488c81100040c20030310b06859005031886001400d240b800040440360403810000c10002c030001c2811203501c0f10074400c0e042c4e12611a00c01050041c155608035004140b400207606020b4900000a01440602681c8a00021020b40d00b20400ea000d9440745440f6640207022507189490800040d1041964250451341405a450085150b049054501d107207113401c0344005009034100307180840c15a40887c203040c4250103c420008200602c00c280b02d108078024000c4e0700013007140320404c144030380b94090b00a02401c0e0720f03400d00c40c240c00c01c0407a00030311031100300c8400921580240181812290141c4501307541140c19001980c4500004008907031940300c41443d07100103003604006c1030181409a40068485220030b414000b143c000851b6081180e00c8800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 6521077 1250 6519827 6519829
    0x20306010503060108090a02090405030301050a080a080a050304030c08030c0a0e030129060408030d0b0301060602060702060a0203040804120b04020a05010c0f0807050f030406050c060105010521060102100c0c05060f06 95
    0x2283d0308a0303803e192100c1d1030740d11050814141014207070020751100000c028030050200c000060b606030703041151070310000c560b40c0700708a6885080e214001c01d6410144180400a4044e40107150710500078104004003401950b00e9207a1507004440041c09840041150300034680d04c4640303006103160a42c002c001c5460540c05c0484006040d400001c192106a50054016110802560f005200c907c040725142c00b050bc3d8144040c0110040142c004d41c0303842000070701c1070f01c0002c1050148140e6005084507403a02e00d828401703036000520a840d00b0504003c0081c01030410301c030f05c05441d4064648114241041d1040140c0d00d40381c0c1c1c0c4402c1c104840d07245a4008210782000d280da600c2e6101001590ba040c040c50b04034204507080700c0e20041800003040018a00390002d000300152866101a40c40c2c2d030381c80b800196058080c1d400b00f02e110f15444620070506041c0065004d803c02c0341401114400d6200c000c01e02c3c10399002e14186000210320713800c1030b02001030401030150030910b6110301c8411880d00314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 6522327 1250 6521077 6521087
    0x41104020705030d0903110d09051008220f0b0403030203071202090307051c0506040b010305070b0a0905062d0d0e010203040809011214010906031509050c06071106160b0a02030601 79
    0xa0180100b07155580c807440301b014029034100f58680d007610180c0d141d04e10101c13005080000e0500c601401103200c40e10b6200003034840d034243c0d44580714042514541000f03199000030202c44c240c0d01100e910403da0b9510010813003810149210320301c2980e0150ba2072800684c01080c0100400f0104081c0b4011311008155a802041c048181c81d415074401c0340860035540312800b02c5802c2c0c1d1001d0424081c0c0b00074030051252980341c86050300c0c00740040f00c1c1001e03903030302c104401403240c010380b01c0000d031600c1d60503c1039140040c0184208951b40743e81c003030985000c412140342a5481d050350090508000784421101c2d4450040d42076a1064070021811803074280c441000c0b610440707260714100040b0038468030715215954800308040c850b000302d004a0303607103455056004100c0d5010030744140b0240600a003c03d09507000380416a603002c0013511005c81e5100500060381c000700b40840b04841414400c0c2180d440300c10103044c0066000302d145843d1320b014240f00c070f5625400341192030f2083c010420400c0c0c0741d0f004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 6523577 1250 6522327 6522337
    0x9011503030f05091309083004080702010c120905010215010806040f08070606120201030e010b0d0206030a0b060d14010b040e01030206160503030a060e01060207030c140105090a06050304110402070503 88
    0x50b040141c0d680703003250000303040c41005c1c40c0302060192804400707030140001030b00541141003040031052085e40540100c18040d4010360008001000603100143c00141c0c080b0180c0304651040c1800040d54510355521055100130003d000b00180d01c0c640100a150303030402132074000502e080f1158002c0d506021449841e020002c1001d0981a901e074440c00811003103c0885c1c080320b80003002000081d440711814003400000140c164000f9040000c12405001d040c4100c19035240010010100340b15a5420f209490b000102200081c2d0769507080c40c80152500390051283e214210000249106604030018840344180c01251007234406000600c4142541110141540d40442e580c51700c1d00740b4444503056924114100030b102d0b00000c4203010381c2040b1500f010050b604c00e8980d41e01c0582e01d605089a443e10703544805445045620010044c80441210f410558407040c50150300d041c0c3c001c0b02186004045500c4280050400170801c81400521800160301c510111340542ca0030083d5142e5980c0d078010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 6524827 1250 6523577 6523607
    0x15090b0a0c020703050d051e040503030901080402040605030d0c020307080111030403030209031c0c02030c01080c070803041704080a06050f040201050414030a02210105090102090307060c03050409090b0901150303 93
    0x14071a401c441c118002c00040380155885000c813000003103003860052058010402aa10a00414103002c00343c40c942002d41e42511000340085007810f000c40c004482da4900a00203a8100e681c0c1d42e4082542e45044c082078100e001d0903101c0340c884010b14418103203000040e62014141c0e0340344c00002800d070041c000441e0b07009509880c000da200e400000019082c9880594003500e480c180400c1c000031036400c0512081054001c40586800c0e8409a0048d81c8030b41d4201c4a800b440d0b4000c200f2100000c030f080000d550800c1c00346003101009002810414021360081d08140444c0c0d01c1a80780c2c100308105402034030341c4481b441000b0401802e02d540040d003540a540544850401c146150840a481c100400c107003258004000740350141410075010b0441d400d01000c2c81440d403c0200140c080c54050003214084d1784041c0041500a00d0100101c2d560904d90004404000b0200310000f08075103d40170750a58a805100001110b0414117071086c00c550f461003143c44285001002080402e410032190040700403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 6526077 1250 6524827 6524831
    0xe0909120d020c150603010c0c0201050307050c070902030903030906160206070807020c03010c030b030c040203061507081b010203061816140c03040f0f060903050c0114070501020c01050415090b0a 86
    0x244444a00301034000d03050b0040c50351041d6444c080030a80111045409441c00758020401e8900d40e0100311800c47c000c400180c0800c0d0104080307409148070b00018010054401c0075114001d44500400301070fa4415100c441256001005105981105022064003d44038200f41c56100c0c801b402c01a440d50001401002441005000180454000d0080c4580000028020044403500d810054020410040c50f10700030312448140c0206402e29108403401113500600030091152100702107155980b041e0740813501d030401800801c240d084012a40745417840a80b00140e22442c044041c00f8080d03c000401d00028070000080c01803944200368540030310700030761804915030845140ca0406500ca0318220300c2076440700040010700000030b01c601d082680c03c801002010155a100d0440c1c840c0d42e1800003401c03540010940c500c8941c00360b031110f0203034800b038100241040c0d16030b240e140c00ca030020515400503075100d104100c02c0110700281d8011092818404014034407060710b0f042014940103000c042e00c1a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 6527327 1250 6526077 6526087
    0x1106092512050601061404050102100207021207030804090f050402011d0a0503030a18050301021314011704080a030f0c0909050603070314070f120f020103020a120203010609060e090912 81
    0x121a0310390350000e84440c08101d1036001c894500240d58410911034640012061072240c80446400011a030071a82e05038000c0a9485111024030003e52003418101d0340002c1c09110113191090503c42c102c0110702840130151210700d0020407100fa2011001280002443e210401c00140c4c0c03c8602005954842110440e00d14010004515800d030703650846a898480458200c5000e07510009038600881030380f6220800969840505003030b8042c0280101e80794400c0c0700d09220940210450088400051400110580b1101001201d180702600c05a48440c0c1c0010071002c02900360003500c1c15060041c108010102115000420b06112405198002503c40c8003085e03095a04200748005107421926003c41141d80c4030300d041d6134001e540306114011101c0840024000b0100d41e40c1c02010b9000344c0000d2505103030b43d00440007580100248800e002c2c910310341101258241c4080e50117401c5584900741400e040030b4001d81410303240301e01180b003140d40710100000c415020909400c2c2c107100c641420385070703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 6528577 1250 6527327 6527383
    0x305030603010b090c07020109051807050a0201021210060206070c0c1505090306070305011502060405121c0e010b150c071a070f0303090b0601020307030f05030601030b060d020a110609 81
    0x3d40036900c3c94030383c000e02440510004918460061010034400d0300c44034070107941c400900c1000d80501482c10756448901002031800b50068000705025040c0e44001854500c00020000d00032000b9510150700c14504a003d016580d01040b0845d04043d00b410314400440403a034450342207218a000708400c9080b01000c50722024081d0741a41c92080000301521007520f40801c00800508003449048180138a49819240c01030000c42e080d4082c1d50807070062300903d504c224001845174820a0320822803660300c14840507000d1a84a40011744074000000f0443d40d440108000c442d2521103481004201d0402c01d981d0590000941c100444180300100f42a1800c040c41e812103902505601405da007140041c3d280403d0780c0755028032074035403284812030f8154441d0801269640220240107020524500c0d612403d280140050741e403050f014500440c04800380d00c00300c2c00980203908490401d5402043e149615600408009140c4000c00300800321490001c0a50b65140c550721010204140820b0540c180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 6529827 1250 6528577 6528581
    0x10e010903050105040605041b06080703051305060702010e01060501030b01090314070302060c030406091a0313140304060210060605070b040b150405010b07030f0206010807050909011401060906020c0102010603020607030503060301 101
    0x9540102c02046285450308040014100c11902104c085105030100c2c81051031501143c402e803021550388100d50b0740c0b0b1800c19401070401401c50400d104003d4550300000b0800c100051180c5615030010480070b6078100c0c1c142c250307009504018140340c02d00203002a02d0342c0c410746c044222070304042115200c0c03006000240c204002c603000039402407800605c10b40f141c40008010030403141c00d60f42301400d05a80785003541d0b03c0d4070345114107d51100204041421801e815603500741e950300501d200e20b0740c0d0700c080443d5461544243c0c0004e02580110660391412203141c800c1c48001c006a08100c0c0c0303408141c0c0c2e500b121019008100429803030811000c034000c08032540150440110140c0200800d585441c01d41c4284d0304181c104600013040d250003644100d10202e8001d0485488038020050103050500b0840e20b500002d09002056503500000d0600e10200750501d402020151240c401c9681404402030603d408091202e040d0ba04108041006803103c0007200c0360f164141c1342c540d03142d0720350800081c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 6531077 1250 6529827 6529829
    0x5040602040906030c0f050907050702090402030106090f0b01020705030a12050a0201090213020d050a1512050f030a080106120203010305071a12090706230a08040206120408030103020108010b18010e0109 89
    0x180141c0f5082d03002c020400001c3c01070302614260030003010065964010030070b86078021108040000c00503c01800142829560749400030700c002c001003400c0740c13901c880700d040300c280409038000c1da40c6170305499109580600ca9100a88015406000324121a4945600070072400d8081d10400a00244404405100b90f104540155009128420803080030720060040d42100c16401c00c0180f418010610150040c810983d41180306c020032404a80b8043d4142a041c80c194815074407030040100c0b58401142c14002482e5050303603030300c0d03002c83c83d41010b200400300c4d480b03c01d4510080344100300501c00304a000038120100c0d0703000070007040c0303030955050002140e000d0042540c10000042044c84041840440d100040d104103a666090b201c0382c44041c46a06064081007400098041015849545c4254002a409400940414030300b842941c980000310b0022501550003c030040b0050045603440f2181c6401000c03d00500e80c1000c64046410307200036840716406d814884005100701d403c0c0d009a81c180 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 6532327 1250 6531077 6531089
    0x8070c08040e0411040504110603060f04020c06040b01060f020a060c140a0f1e080105041505030a050a050c010903120c030201060902040801020c010606020105070219020f120109060506040515040504060204 90
    0x180c489650300c41e0002d00800641d400c640c1400c0d402000813140c102445010301c126040104410711003080001d224040c1e002804c2c0701e820080d6054402e16070345031800204028441f802c020011454141401107a049040c0c01c0301e030801c2040202c001d840c55000411407021361708002c00242c3c203600c001041d1107402c41e9000c1800000b0000c203101c5815608403480116201640e00c6072454100b01221255400404000c114041584000141f000e802e1070350105000c4640c90f10502c0540341c84900082c43c241c2d041500311440c2e40940c03500c2c0c0400a0038040c5409049080c28203076460382c2160b45c1d031200c2500300c0c0d681d90104199130b8043c40c2414400d4102d6030081c040401c00310740d92a00c440840303010707601400200c000c0303608044001070090320500c0340611070340f000c1d8050a5090602032a03d04180e60024090380d000d0585508501c19a0b02c442180c02002d4141c4000030381ca10241c41c0c0300307007501c1009000901c150701d002c2c00c105070460701a8040030003000071640015280d40d075151640c02401030303804c55 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 6533577 1250 6532327 6532343
    0x20309030712031a030705010903080d0e120414010c0b060d02150406020a050c0603070e010c06020d0c090603050a0b0a0b0c07030c03110315011818020301050c0d06050901080c0108070c 81
    0x349016500f41d407109070b51841042d040310340c4421503400d01d0b98402407482124001061040100003144006000c0d0040340c2c4039500c04100201600c05003468904000d016a442a000080030410f001c01d060780e5266854007030900c220a01c40d207494280e801130005140d14003d04035444102c003155034102155041a00c1203030a50b4a540d1206002503603024100300840d454814048000e48c44d140041c1600d215004581d03404521050304801110010b01c14041180c8a503000e00168500010b24000c01070706104070b50f1031180151034010003c080e2a00640841358262170100060f0140d01c2d0710702c0140644520300c608903a1503103000a820710b1715016078009480444158808001c0140b2010303c0000341354102d048800c5190401140960780000f882404c6002000542d002c00d6641c05070071000300041d051101c0d0b12901460f4000c0313070030b44404480c5d40c07032a940b0024000300b44c1d031501d102e010b0191000b80d86100b9039604050001d580c52503807000880c10b01c828100002d801c14403031690340e554140c1c00244 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 6534827 1250 6533577 6533603
    0x2603040b03090c120c041103040f02040b18070305060f060c070b03070e03070f050906060301080705010f0519090314010b0904060b120f01020d060e130b090705030a0c05030d0504050a090203090307 86
    0x1165205d5081c50b0030148501d090140308484229408140d074040c58003d1121905000543d082100030140343d0b2640781c101c2c8410003d90070340c948580c1c03481e110b155540c80c00b0a2500c0c00004200d89295000c012600c07030207050083d0007106100080c5001034400001603c4c0e41c0341c42d400015594904801d0226034140314100002c1019046141a00119041a00d0311021a12104100801c0c0d00090040035440e43c03064034200501d43c4a4001c1d5410754055041c00392030078114803048220381800114007400315400020400c10088072095071039400038020000c00041020000007400d103203007d030002d04600c1e11510b040840f695681220800400107104550410100200d002e010b904459400d840003403600b10b0006c1c3c2e202e003c868072885444594a1100807402076a2071200344000500701442502c101140881c50340c60402c82034985500411421b01b150f45000f0030586001410013140003048814002041140c4a164181c41607a920320000f517201e40e19144060720398000c0e401c0c054846004018 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 6536077 1250 6534827 6534859
    0x606040806190f0e010207020a050d0203031e0d02030906040308060a06120203100801050405060a06080d080402040c0309122102090a03150b13060302030606010c2003010908040b042603040b03090c 86
    0xc0200324151007680c883d2715145e83d480c200101d24a00d00e40280d0140c00403c169000740080407641c0e15031070b4584030310074107101001102108a80007200c44002079800f40c002d12062541048400764081030455044074031505021008054003a21200301c0407050300880407901904c0c0e54041d0ba030280000740000c000d64900350038400d90380c1d40142c0d041104d07107180400c089044600130508100b40241512000040e03100d99007444010500c04000904043d0346081c402c00255001100e10043c8603030380c0d6100c020f0000d01c49201c030074820745044598601d2040195004a0310b4100300328003100d8020074181083c007042001c48000d800110318581e400200c0041282c4005541c0e840300050301e0007076048428543c1da26005647c01d00e80030304050892601803000c41c0e284000c0d4106030300c00110203000802c41c140d01d42e82d036071307803e810070b4200c5195010302140c18003402d000c1040ea820800e1814840024180c05601c4c03091307c901c5180100c1500b00310000005103016010024103180704c0f805000c182c2d01d210302034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 6537327 1250 6536077 6536081
    0x30203060907021606050304020409020d03030b0f0604030c05240d05070905030604030c06020c0102040807030807110d080301030303050406020f0c070501080a0911060304020f060307020c01080606040806190f0e01 93
    0x1204188510824008180784603c005501600300c2c64568161407220704050064403145c1008000701d80c8140c55004c02c500503107490020382011071081d1000b0800d00740c0041001401c0b680c2c0f40c00d00380252800e02080001c200d0712080241140c80c1a202103034403074055104103445070181d4a03494160540082c8220b4280d5266001c02e206200703030f03034641e1b8025888404068a03044151130280000d644400a58003080c3c0b10790092040c41080d00c0018507066584a81c42d0814020b80d100740c2d030031000820a0307400e11541e4615001502c200301d4187c2c05003611075a80390202e000c10301002c0c0c00c06985100040c20009980d0480b07600e1010614902d80b40c10b101d0040d50742d03810581c00741a00042c00034000c0f4440d50501c1c0a1040e016600000c1880c080180409000a075040180b0681e488034030081000400d4446200540c0504250b5001e01000002036001400046014000e0f6000b06800c01c401c206c51500400d160750015401035040440c08080004034024254084103122410b1401080b0840c0f40015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 6538577 1250 6537327 6537331
    0xb0618070f020601050907050a0e010203090307030f0b0a090206040b1804050f0703060608130206070c0504050106090801110414130b06030c0c100209060913060f0308030901051b09010f0203120403030203 89
    0x40d4210382d00344c1e80768401d0040b2650141c0701c44010460901c840c41036603000e410052031401d410310480b03007400d0011001900e000c60603030042e11860b840c095180b060210210081d680218006402d0017101601da000c1002c912440c0310300100799170b011070006000312100b4400a400c1c8030042c8103201c18182541007440038001030b0b8498002c01e05c1d0803030018269010f00500c0303108064500707408128002503002e0201a52000e001110001e0360000003150903034461051ba80640400d0342e4800d411070909165508681604032101c0c42404144410003a6803194041496070798000e03502c441c020041c000401c00503024400609901a001004100c2072105150241102400b120211103028a220700420708903c01c06913815000750040140040c03d040c2440404000e404c1e18400180c040d9448001d550944030301c1e0004c03030340540b000050210308a024080e49402100900d84042e00c551002140d851500c14031000e941802410300c2c0c8100030500a0007038600b04030310001c17a2443d40c0b805240c020025401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6539827 1250 6538577 6538607
    0x10f110a030e03010c030c1d01050d050c1b06010b0306010309080c0f031908010503030a050c0f0a1104050705090a05040e01020d05090a030306080d05180a0305030a020c030607050c06040b061807 85
    0xa0001085d40d0184203003d03002c0700808688401c5030701314030004910341c501100d0f000d240c18040100408001401076100b45403040114002d0203440360f4503209060000c6502c0c0030a03044540c000310050010300e8646003125085142402c000440050702c2c0b8188030344e80251103d481c1c10380215080400c1c1c10354040004c0c8071600c1071002510b1580040c0c5020b440d0920700f0302500da0180d0040c1300d84190b01d07005100801e0a00741c11411940d8071189803032072501d0801c90200031101030032803407443c00140c1041c0c021036801410b141030042c2410440d4005c24083c04d0360f40b144511030b903100d1034518021030084d412164011400001400645440400d540d66030107151300c1100000d1406400181480c8007103060490034010307546051400b4103003170000041c030b2030a44403d940121200320000010702c00b08028511245550050205014100c003050b04140004000006109040003185510100892a55070059100c4840c24030360b11003201113050144070041c4207400d001d842d4280302c01d4541100c03004c06c4d0508 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6541077 1250 6539827 6539831
    0xd060e070303080105040204080613030507021207030b070806012c0a0e06030f0307020d030f090e090d0809010506010c1704030605010308040905010b0f03060f030f1213080309030a02010f110a030e0301 88
    0x60f89030b041c1b01c01c03407285108001164002e40301090720051022050280640a03140903810320025400140c03d881d82d00000310b0300c5a218403000c008005100c0c400716409070b074034240b80e02e036841d0100c0041c0c004448400107032050386042010125074201d00402075000640135012849142e2560148008000180da02d01d210b880364452000701d014000084510182e40a448003104080b03075581510300304a5100c0365401d12081ea2400b0a000c2c00942810307101e151504001c0c5011020000d000d4098400500b089420f82d051008110031640c01100c1a01d10b107501100d004030001d81c40385141c826000c1c503013004000324240b078000414445800040c009075180500c040102d644c0c1d03070388241c0d04c9114501c41034445841c2840014a43c1c58060b800041e4071002600b9581302c907600001407800c1140b070301d485a40000c000704190550a5001c03202c100503000790001107181c0b84203840020b81d0f860b010710009040008008801c5441c0303100d10015201240a070084450788c1899247c058021a146030485010f58 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6542327 1250 6541077 6541079
    0x70306060306140303040b070c090f0f050601020606061c0b03060411010809010b01120506061204060501080c03030c1506060d0f090201030c0512010302120a050604050606090f040309140d060e0703030801 89
    0x1490341c030702140304440010011480c06e8170b001d036801c0c1150450701c0c042c0e59986603001c0019184071140030f180500c4400d5640050026661110740007122005445241190700680800119440c0c081c1140d081c1c070402d02c2c07600180c48120880c0800b4008010708146c243c015030707090000304030780c148490310540300980b0350021568500c29503608032516a140907000600013103841c0d084400c1c507403043e9085040581000e14003074070900c820000c8001500c040300e84513601c0e00100030008051082c020119400c60155107800f0300095215902c0c040c0140344a0400c801c80c02080481e0f55030700c2110201990400148040360070380c40341c0c07401000900010f80c007113410000c0c03c82d1454440c1d801c80301c400c40390b00001c103610307401c6809105565819003c0e45215106050300900812010810f05100d9803143c801043d10307160038000c0c8842904007401c0c01c4501e1000e02d0500c40040d800c2130085040c0d40d00745203070008501c202c07000103c0c2411054000780c5510700c0d2503982400fa80d40824240180da0103130702c96592503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6543577 1250 6542327 6542339
    0x60207060203120408070201090902030414070602030406020307080310050d050a050705150d0e070f0b0304020f0d02011e0507080c0105060f03030a020703020411070605011805070302070b010e04050a0506070306060306 95
    0xa00c60820040d0b000076032800000c000401701c5018000842c010f26000c40d00d1610b43c8105012a881a83c0568044c0545d0f440a00c0c50308040084a01500c1c162014500309864100b0113035603401100d00007000880080005107400007000300c260300414005000d0740401c6900e08000c1d403030340202c3d44191468000d000000c01d15042030f808003610301c0310b4241403d283c070b84600003901c0100900c40400005001c0c8050003d203e42582c03c004010b0860b911b45a40d0340c2c101407040040d00704403000c441d8010a480f02403c805030707810a21605648040142d04441146041c3d4200d4451091840003482c50b0004130300305c8414541580f0203842200140d8242c2da1200b94001010343d680901c0c004800182d00c001d030140014200350b003054074800000b0b06228100041603403500c094810981000c594000040b2000740c040d04c5a004180d000b43c517500f4114030f0080c0e5030700ca28420320014010040c50003682d0b0085000c1040401402c1c1c0c1d02900305090300d2590030101801406032140e44100c07000a030900c0004914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6544827 1250 6543577 6543583
    0x60301050f070f0207240206010504060f05101e030e010b010206040203120c0a021008090d050f030403141b07050f0307080d14070803090a17030402010e01030f0902040608070602070602 81
    0x3070303080c0344085081541ca598048500c0300550309030b6411070040c482d0008060b03100c403001080c0075030b040308012010304201600901d030210583c0f0440c8a142000c0080203540d0141c2e961105403801511034214000e00010203640c8900481c005a060310201c5200b01d600e1139265008990000b203d00086c044040703580c004903510b0109603406036040c0c00c144007041521002c8402480c1c0d49800c142a031b50221043d4000a000d4680d9445d400e0101d05030500308109410107211000a840080c03d02d0b90a109a06c84541002d000080c402018402010b01e1101d004402d40140c44443c202400074504460350380c214103440d56020320484d0f000315003800c0d00e00d080703150103d07e540c00c3c0d610042c0200754141400e00221000000ca03084648d9200d0104418400b09508a009600c1402c914000706280320a900d04400c2c074490504cd8440201030034030901c801070b03070f101842c072a09001c2443c01081c0740c0884440d1000030422400300a500034034103880028114000b14805003207818035020380e1111075940100743d031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6546077 1250 6544827 6544831
    0x90606050909060418020d050303090d02030301080309060304020a090f0606020105060111060a090206040302030a03030b0a0603020f0715020c01020d0905100204030c0b030a021c0b040b030d0c1e0804060c0b06030105 94
    0x1920800c804001101c84c00d0a0340114105104a059900a002917070041101008003100030340d030760b0300000200131042804225540c22070310035200031031566241502041d1a1300070054418811007000011030255628a000c101c0a403038100001c04c107070801d50380ca00c40204424031800b00503509200000300b196001d603001c01d000309402c4000d002c2e259280940f100040a5408040b030340303c0c8042c080400582c41c00c100d242c0c8100c1c8070f034400140f000114407c1102c441c2d5a98071440405004022030070030b4488135029900076940c0b140c0d20100b079410b004d0001003e030040d400904001d40c40032a611900e2034050b0007542a1034019025209403a00c542e0203a026441036010103402c00400980401244424400850703200a01490040c106940140315069490031608028461074445c1419821864607125020058078200c009051500e0001c40c060080006d000300509207020383c1c0c0341d20540030146051054011741c40b10042e0f54541d00c4400281020040c40703011340b8200007003000102e1508051041d58 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6547327 1250 6546077 6546079
    0xa020c040b09010605040e06040912020304080114060604030803100801020a0509090a02070f0210030209030a1101111609020a02120406080708010f12060504030e03070e0105120102090a0302040b031507090906060509 94
    0x1030310b40b50811126a2034440c01031322035500290782e100240cac00f045101d000d002d601c48581d40039503070b00c2d4540840182580c07465004401d00c41c29150500c851a0354140448044039800201140c070303550303480e0000c1c50904d410f504c000501d50000603201c0320258031000900702e031101111654056110b404842e4105d028880000780489640102031000d0b02e0800031f90781403041540380261400d040c01c00482d00304010984100ca915620340240c0d10b0079a0015085069600b0f8200245411900303a0700740d0510302d10038824220b030b880d030008044101e03d1081c40a42c04c0c0c04802090650394035500e0800405c1c030201191170b400011000c000124602d00e500c40c0ca8012518403000303442c416126074480e84d00511014004805104100310100d54a0718140702900080c50590702840c0300d0740c902020b2018130072102269040d56407042100c0c0f4025074507241d80105881c1c065400140030594600032034a1b01000d1b85801001c0302c070f00c8081000440c0c2c400d0b00310040c0e0720b0b000e10901c610341e5100390076901401048107007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6548577 1250 6547327 6547337
    0x807030c031115040f0303030e1b0f01020a02040e0606100f0c03080c070b07030902031603030c11060f030109050106030f060503030714030d0c05071109040c060c080405060a020c040b090106 83
    0x3000821801075400b50b071520000d21148240101560f0240b0552156000c1c0300f0180311910200241034152040385031051040d4041c2180c4485100c42281684503007944912a807018800c0c84d6160344204100101d03030390f01400c00c22030624a410080c2c3e440000b103520314032402c5107048001c10613110345940c0004101c2622800c80ca1300295a00742ea1034000240041010300c0180700b000d020419482d603090248825413000102019540149802d0070314110030140e1100b413100082000a50002800901d035411030710311004294540c0005555128880005a00c540080300101c0d6244007644a42d04841d038a850401c16030800342e4807002039074181d2240c00c0c2d01d0b030800e001e00d10200d8424000c0c0e110014419050f0303483d25400302d1400003160f43d00c0000b58001b0390085503000411003203002030301106400315100d120350318003540c0720b2108804a028150400c40e070031032040c1c2000201800e442c09024000c0869845a4007500001d507038519001e213291003a42040c0da00c084505010b00d8040c1640c00503075903 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6549827 1250 6548577 6548579
    0x3040b0c0901090b0a0509041103070906031a0103050603100e0609070626040f14011401090203090d0507060b0307140103050f06010905040c0203090901060801030c0602070803090d051507030608070807030c 90
    0x100c0031907400c180006002d2080030410a547c9035282d204e014400642004032580300c0c185a87c0c000d1140304e00303400440500d0314041c00c841008a00c0c82030010000c2091a000c04e05548410200b41045401804010700714202408001c6501c5d0200728540b08404103811243c48658880c0102d4001e00c1100401907034881c2c0c40000880403800c98200c0340e0290155218110105090fa40d4441d04149a03000e002aa59030b801d4015282c442205103500601901c0300544c2181007001140c0c2e22148007150b820184030002492404002142d0002c14504c0720042c25182030566031141800d00c80d0060a4041c00039250030001041c001d442c400c03880c01040182d58000c005c41c188024000105251a48082544401e100c54120396a44100d01e6019100a5442e8400340d4510300d80703840100d10b2900118155000890180a03081c00041915a050401c03a00034840c00001d05241d400c0c01d0901d410fa45042c2103c8007040320b41078250300b1902c112842c51088070a859035403041642c441e07001c2d0200406440790044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6551077 1250 6549827 6549839
    0x60a0c0f03090305120f091204030b06100c060603050607081f0509060427030e0306010e1b040312030c11070b031305010608030403030e0307050405070507060903030b031203040b0c090109 82
    0x80101941032003810060724012034170192141403001280e2a00040b0b02c80010020b8881c0305001c0001504070101800d13040c141541d80300d0004e9080240410700034110f0070702800b8400e00c00d6040c0c120031504058200072840d142d041c81900c0725000c44003071001c81c03202d0300840ca00422081e00b489810300c4a001016116091004000d04840081c108980c05072721542d4080105041d80006458042d2000c14140d81c80054940546151090f00d0414407170f820201c01081144040840e081d403001d02d050b134181c1408014682003649010710340000d04880c00a5604040c61600348c0e02002e9241d0b880d45802c003111000c1503461350345000d58021075075510310510104001790070b030384041203c0520a10000c200161076011803803039500507900540018811212404881c182070001102801d4151024007491800d00c002900340c2c410040c005140a555007c50f0003414401c0d48081c03c1d00c100103080da02c51010100b81e0390307519002030301d0580798081800041140251400c084a0b070541d81a106c441d80145010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6552327 1250 6551077 6551081
    0x4050405030f1303020a05010504060206010e040602070b0403120506030c01050d02090604090905060a05160503060d02120712060506030f1222030303020703111b041509090b0702060a0c0f03 83
    0x9001210316100c1441040c2056100c000500350000001d03010541007460b5004001c0e0480345070784154103110040200380551135004c01c4440c1074403003508030341e00107489a1401c50000e2140c0c040150905035640240020150301118207282002041802d02c5980c94034010036441e05031400032a808901d04004021007004590082c0401c40401410a406c0950f1070300c141080d500259000ca44075000b90081102d5141c1c540300c2c454010b521140e410f40e1031044100c01402e10702c009040e05109100c0341400f1002c44d52841e08110940c072416003510741c95541c03014948075140350480b045800e80e0801c0c00080043c1000a07141c0001d07100140200010380d2180d14942656205c104120140440814071248000441c1c0740030009610913680180d440c031084c10300602c4035021100c44100c035080b51842048002465003d41c40c80c0724111070005500c03294410b9500303601e285902140303000f03040044a00510050740c1450b481042140c007030301d1440c0c0e164440141182c00b00c920400c080340c00a110515854070907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6553577 1250 6552327 6552331
    0x1223151603020d0f0b01110102031b0705010207060608030a02100506030d1404080303190605010806030c090c0909090a02040506060a080415060b0309010c09050d170306010c0c060504080105010e06030a020405 91
    0x6820300501d00f04000f03981800341c4002001018200c1e480d14040521541d11a82486017070301074000031825030800d503d082c00c020011000f40c0980080206959040c0b040a60407112100d921000811a403540d07140c9240d00c90300a191050302502844440200300020350040754403801e402000360006245013901030304c008601c1c00e04c03014998000e1001141d034610800003180200001c0550020000050190030161895500301904101a20080c04442d440019403441c0d2103030708440341030943ea2044020f54040c0640d015403940003007901c090020411010030054411402554103000700d603200c0050003880c1c03194010410000d50380c00b00042c082400810301050b0310840d00008280540e48003011300113600252400c200a9640d0a03000780f40a0304000924028807094a0075040944070b43c03681004241540da140b40c88120010028a00ba84039415158015034030141740210386031103020040898004d03000710080c541c64440007103400b1904000007442107030001d004000503851030b42408045c00d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6554827 1250 6553577 6553621
    0x510020102070c0602010212100501020a030807020102090a06050904050109060e0103060209030709050708060a0e060d020d060e0a030c0b090c13150504020301080c03072408040804122315 82
    0xc00e00100b8005074030314403140002c005960001d40c9a98010309004d1445501610f00e00b040202c0d2041004940d8011030084c1c0c0342a0582003554440d6281101640603101d9600307040e07804410054082006a003240c054450107505480070885030b07807a41440c404807403040c01801d10790070010004100044103500180110100030b02a203801c0c5070b40d0301c24602a46d4007902c407035000c01d154108009450801000c0c6034003e14001d0b04410060030b068010a0246100480283c000e082d840007840901c2603070340103800740c0d18241d01100c10555060070001c060502c0c06000321074002c81803000c5076040300002450401000300404002c1c10840d1504480018800340c1d1020b265a0360350200003c440d919840958000c080b050f001d092402d269201b05406c00710250000c2c2148080b010740701d424107086070340c0c8410a50103804d1800803501d6a00304a021405140e10440200300c5180540040107409051503660782d4100f03480b1281e601d010764070507031a05190b01c810220f0b6000c0800040101d0b5080013103a09590b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6556077 1250 6554827 6554831
    0x1120f110c0a0b2d100801060603020403051005010f0605220306090308070809070501080403030b130f110313060e03070503070302030403030e03030a080a0510030519020f0a08030403080d0f020c060f0a06060905100201 95
    0x1b17a03a260740b500b510825400b06002c2540441c08000f0f104060100c2100210b80d04010440ea41c109a0201c040d0301c030034041c00302000000715034450440084d01652901d038107001c0c071500c0c0304e0f43d6915000018001e5401c00300c001520303880c04254910b00603602240030751100000340034070703908000044801581c01801941010b44440ca0350100e07869126400c90ba1208091000c1000c1d580c86009005403003880304008450032040041140002c5000c0601030b41c194021004542001c00240309407460080d540050b005000000310300e07040640020041084038440d031074281c4d92101190416032207005882c0018049204540011308a44241d03009590094241c030402d603145803241c58191500789160b442e04110040121503400b5440c15030100001103008071244081039050130a0b01d034882c00740744402000020003088a404800040d080f984107607450349021903c82a4442c04980e4914090314040321001244020410604090203180c0545182c3d4a540304264071f4141844441d50303c0080b0081155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6557327 1250 6556077 6556079
    0x90606030f0507170d0206040206070f0b01090209091302030a02040c260f1008030a08070207050d0803040605060102011104140303090316090b01020c01120f110c0a0b2d10 75
    0xe1600205462500d004100404955080c04a4019058080a8215a145e002855841e81958000341d45d84d40150305841c100e40301d291a00e0000f6901000000051290001400200e0280142d81c058810b05104403415625619440d0021404910581c1c01941540021002c04054101508a150120594585a1000445204004c059201c507550401c60030b8800c00621641007901000e050300034882c1a8907040340d9103800002c82d41c1c6d10608803035070107014007000003a03515402407212000611010f414a11502568500520703183d0044a00300c0b040f6207020040b1b85194814841d00a854031032840440c40e080c24013840f0303681c0301481103145070701d0701c0304002e03000c4261018001c0b07070441c20140c1c1c0071088050522100300d050320300001c0207504544c8050100c103030681e48003011003400c40c0c00040006060300013041e881c0241502d070030f003650341c3c2100007820140700c803002420341221402084000c40d10788030000c010600c500180120f429560000c1000b005000d000201160030403001c0190300102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6558577 1250 6557327 6557333
    0x9020a030204110c06090106050105041e08010603080705060906010e06060c030405030f03030115050f040603020d02070c24030b0a0303050a0c0b040f0201080601030e1b060c0601031104060f0308030a09060603 91
    0x80c8107035091820f1000000b203070301c180c40c08040018540140e00e1100a10969040a000906078003803440303560fa40141008603140c00d100132010140c05405e012000b4000f07180c81341081402d03540013402c01c42d580d102c0c40d800600802d4002c101c0c0b60680d075004c8150781c1e098503800c040100a401c66407134008107010030000000c035640c08001c0001280311642c040c0d0785940c90101d0401c06501c500060300c060010030001c5d40a9142e140d0216000d641d15800c0050b2903150400302c0c0c0c8001d008010780101845043c06012901c00c1401441d000303a03100124902c00c00314030005049080da0726064a40e50071412529042c400a4001c502804000b4410b203407000340f05080c4d0700c03141c80490040d101980c58205809503a0b05550740825550341c000400c0c02c0130310a41994046561703640c0d000d00c80f1244214100b030200c40d444d5640c02c048940e54001d01080b107840e940c582c14095030044108041c24032940c509a400514000841581c00442c1c1e0080445421a035808503242d01805040748200d40e15070b42c0d00804000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6559827 1250 6558577 6558581
    0x20c0102040806040b0405010b06030403050702040207030309020303070f120903020d02100302130e010302030c011d0108041110030506030105100e01060f0909020705060a0507020106081209030708011407020d0903110409020a030204 101
    0xc44c90007480f00b01210309140c1446821101e1035074000740030f50303001c1080002080d0440b044408040d419500181d50784010b0404400600080c00000c0d0b160000041e4013062000020f85c000c00c01c0d0055056841120640c0300c1900e140c465440000d41100b46061014054a032518802e1465811820054039090f44490350240c208240d400500b0310840c0080144290300f4100112980b1100038284100c0c0464140c44884035100100b440c2c5041215600024080161801c0324503000741021f0959080c0740610a40500074000072103810740250310b05400100b2062900050108660700a40b1401559003080300482740e1070300403164582440900800013984170b16038402046060b00600141c030030360500f8004402503c00c042e020808681c1031070030900071120041814a0380d05440a000d6540f03980743c1c80440c1c02d0450300c0e88030304920751a100d0b0038071450f025031423602e1140c0083c0c1d00342c4205103917005069400f04582c0c00040c100110310030440700d036802d00e94400c44010b8001010000014ad4980c00941 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6561077 1250 6559827 6559831
    0x80c030301081b010201020301030308060907030f05070504030b0c0708070803070e060403060207030e01090e07030902030c0901060801060215070503070c021c060221010806070c0c0807060512090102091003020c0102040806 97
    0x1001c3d0348a01c0d620034800200200e900e00040782440290300d15491034400902d8040050121403007180031602003240d030340c0a86c0c010070001422080900981c035081d18041c0a0790030900c016140200b5040000b034551424108540c1d0303403588201080d0410388207481d07296450700000d02013000d0084104440002f540c542c0c0180008600c0780c0000360356030869182c010500750502d5600b070b050109208062001d650104840342c1d11040c1864001842801400000d01e0684840b00d400d4001d5400800032840d41d5002da00d49041c0c0c0d0f40d90b000c03280c3c140343d03003070f0520201d0400304c0d031400000d82c0031720100d04001c1c820702400740e40d140024000c0c00070b900c0d01407001e01c2050300c2c0a800c50700d440c3c0c00200040c50b001003008035108142401c00511141d0702d041c0391141c031203000030f01c003108118036450710343c04102c14029040007800509046070140b41d10b130b0002a040b139018008585101140304002642c81d0414001c40b55180005885162000310605041e0080e41285542d015103540078080411868400c110444c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6562327 1250 6561077 6561089
    0x50609010c0e0405091011040e010305010c0905060a080a051801020d0c0206070c0309090203070314010b0702030c060405030c10030204090c02060a0c05162004020703020102091207050102100504080c030301 90
    0x1000340428502410082d06042e0307080c01a4207203001c00103030130301c0402c05c1060881d0601010645007000003400c0080d03c2150000641da8013080000720030300c541503020310140591a19a04200ea071904100821406110f50217030008001c040043c0d1458082c0e00025002000c600010b42255602c0c5405426600007400b440c10140d03890b1032440c00a681080250b0b00004982042e10040c2081c1d14000c1803014035000301c0032059000000314000354800c4c0d1101a0403902079550504658480c81060076a0303000880c141d01c640318100d81d020b1203181074012582140d00c010010300001d1800c3c2c1c280405c4404001d2840140756080c84001407034003241c007814414451550141902e032401002c0c410482c0e4800d902a401c000c01400003c0103d0303056000d0415050b0054026500105c56042c40f426816400c289140c000d800456130310304040c0c054010707016000341200c241100100f06900c01d17954500750711541e4010ba12945140c04182c0321540480c1d0401c2c0141191460314844800591441e0f0003a40b01e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6563577 1250 6562327 6562331
    0x4050a020d05010b04050117090309060c06161409041a0306070906090b070321020d02070f0605061801050d050f0703050609100203010e040311030c01060303030b0f060720010c05060901 81
    0x1054008501c0e100d480d000d8443d0384001c5080038142800204480d100f0034007180e40a900318003049003e0810425205003480090a13281c0c2e5115200d2056142c0b01c041d19580429140b8000504903a4040d800080328076080e801d900781080140d4040002030510724000c0103045414054051494078180031803449001d19444415a191038081e0080400400d58003072807111800741302200000f680600600f090b4040300381090020b0120402c1c000080c4503903001160807504c0010007004200b1001035482406002d02c0c010080c0341c1d209014804501902e8800d0541101c840d001800645081200098a140207004494964003103031030461400160f0740003030f6803d0b84520308202e04c402080110a0480480640c01e50139945000c0030300d00585400340004040c082c0c071051f99041108208180c1e44c0000140c0005d04c0400d83d0303410051300818881c5155802480004c619820904015046481c0c060380b0808400003009101c40c0c9070070700588510018100201540e00c14003007141048500c1c05405a4800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6564827 1250 6563577 6563587
    0x1801230a090806040203071511030307120c020a0c09051902040f05041512020108060114030f04030e010c0305071401090510020309010c0903021f02030c0f010b040e07120807020a030204050a02 84
    0x203090341030554880c0c045a0f00000c200303c01078801103822811a1003600c100e151819101100780c8014680340801a1113200100401c407603150710091981d0740000c00c210812041070b80841c103e0300c0e0217070b5030070280c001800c001003041125215400f095106002c00c01c003600d18a00794040c407050341e1040c3d005502c0e100c89904240035928040c0b01d080400d03004960310301c807444e02d4501c0d5200342c06c2c3d2051b0041d06000280e400110300d0f90040d4002c1462803904c0c41001d580e442d140c8000341c01a10240e03419400904640c54041f1a540079007840c400d16a056159181090030658481183da801c03c01ca400c8a0b54803041c88200084040115045c1500310701c401503280d10b4120f2a241c00c4032021551141000440c420410150700c40f100042203d40201c210816103e04000050380707507101d41d4440c0030b400d02c60f840d0380140284042d0f00c1200990011101400010440c0c0b4120f9a1491350380500f11204406404443c005501e20005204951002d010003102c3c0d65179400003411200300b181c00c56065034001070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6566077 1250 6564827 6564847
    0x51801032903010501120f06020304030512040302010c020d090b0f0c030405040203010e0a0e0c1503091501060c0c0905010509010611010603020907090509130b060d050c030f0d090b07030203180123 86
    0x1e160140104031b0510040307805648403503404020445d0040c200960000205081c14859411202e003042003a11a2401e4182450000d000b080c9003041e007001030107a046c4e0607440301d00c140c2d400400c03550020b15a07070030f00596035820b54050b0f000310346281d040c1c407003040300140e6625580040d50091881d0905581240f0300140031409a031030001c44c00c0f18640143c100c01d042c5175900b00700003812040c0c0c08502c6807a41e0355406103034076004800141c0031480050400000300942e101c44420721061140c0c0c26a50690740c3c0b1100c503429a2400e009881d0300000c3c450061102c144242a07202076020003c0011a4660307494001c0795802c1015515080040d8101c01d040c011420b180e00703843c0e0024031400f0380b0314a00e005500c482092140180c00984a000d0320311428042c40020464549400c1c401070a9035000190700d10070300d5860043e0f0350804007040d002140000c03800300c041c043d40d20054064000d94500703d0310384501ca44050040785502d0602046552000c00004100d021910380c682c0c0303811903903680c91300d51 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6567327 1250 6566077 6566081
    0x1050c0c120f030114010c050604050304090b09090d080403020a080406090603060806060306010b090d0203030d0e0613030e04020a03020c06160207050d1707030507020d0b010302010314010605180103290301 90
    0x2040325078400701000760000b0204000d044904541030454400000c1e512100100d03035141c41081c2c0680284104020720040c000080018000c59a210000f0000c102215040c45000001100ca8540315084007000c2c1760550302031400507520a1091050703505c006055a203900081d0003640200c2c1c00a5500e0b01c0502600d509445000060400c100052001d80b81250020b0703a80c0c8130502031607800f0f94022501ea081a25243c06c0c0d1b04080b94000d0542ea2a5403103140180000c050103121020300f03115220210724046020020200c0c0c241d05130340c441c00d1100c0b481091001951060351140c042503400c004c10040030354140103190083e030b60b0f03071200c01b418615400e0091400040c2e4204a00c80c0784104010703400504061401c0b02c09014a00c1c1e015103407069818251100d01850780b0181d0040075442c001e208114050070b03018141e078400d0720104410101c4c0c0c00310b403800510034011040032039420040188101a00381d0003240522052501046100100000e03115800911a02c3c2c5c400ca6144800a4020f107428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6568577 1250 6567327 6567343
    0x3050c0306010e04050c010c050705030102040b070209151e06040f0303080402030f0105070e010c06060306021c050a02160303050604060b1309050a05060d0f03031116030e010810150c020301050c0c 86
    0x810440c3c06609254072269111641d509001d41400500300c00301d410010305200c03d000409006000f10349540e910029050b881e0300c4603100b01e100b030404000051152032465a07170442c10002400e580c01c1c007800c1c20548440286007059050740032400340000a150912032000c0d40285100b503030344084a0800380306161501014400010306a4180001c00800551000407224515001d00c0c0951080b42141000002001e8507000545214000a0300d6011000f5884410043d0b001e40c0790704021130780e1206581000c07409100661202c10113071054190200744039412141c0c001000074800590f00c1e83e910340300c8126a1140200300360a00021600300020f400d140310b46135001c00c58800c1880340c1c1c40e000700041d01f4943d419000030803903c020f40641c000c2c54030a0740300e06030402d0f00260581d56648080000c80d56841030210441c00249041c0c482101941b2400105028681c04e0041c07402d070b9400e00001a8001d01c1924171042000301090100c2c026980c01d0046900689550010710b6656151210b01d07810851b003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6569827 1250 6568577 6568589
    0x60a0e011b02010819060315020901020d020a050601121a0411040e12030c1c0c020a0c05030a0b0c0d020705120406020601050d030518041107050106090501061d060a02010209060403050c030601 84
    0x2072a5072800150740c000303950990020300316503200c1c2210030000901d0001c00040e003000d007220084042d0b81c5042103e9600800780010242c0803140140b0f00040b0481c2d5500b00c0507002030607500400300412600c82142d45900507035210b2100503c00c0c6ca0110880701003403204a400307481480b0042030303d10403805c0038800c2002084010f000350029400074009c40ca05032201400406154000041c900c008480002071031501c412004014003c05405000003540c484c843c007002c0e01c0c0304d10045c400003042d10b00005c400080d141c3c00120882c459035507445180035604505134541c041a000c1203180c000640030700001100c11171001c1c0c1039480e10305240c0000c0c44c000c016042140500c00558050001c280c10009036006008114010400c00d107001d40031502170308a4000003440c0c0e00b004500c0078104801074010800703a03114030380100000c2c0e907220021a4140e1071805115000e0300d440e5580c0c040350034020020000400d40c1d00001d80703450088004901c260340154000ea50541205400744060324060060f5401001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6571077 1250 6569827 6569867
    0xb04030206030f041a04050a020108010905010e1609050a09020c0607080603060f04020103150603091104020306010c030e0a0b07080307020c030606010e040b0a05040e0304060e180103030807030b060a0e01 89
    0x2066602260941c070029000d0b1030055030003070024040050b10304501c015000880c40010315070516141250342c0d0381e5821012404503a008001143c40308070344c4181d80c100ca0038207110140544842c00d0880107010303602c88500030803c5000e00480c4a8035078400003802042507801c010303500c200242100f403d040015200c01d04000c1080c0c18003855aa00080041c0c202c0702d40502510305803568801a00104812280d98488106000b070000302207415601614413240602102000034101004000c00c03488125001030124080750200008244914030101c10b070940070f1b007030889240e100c0300388840c03641010800311605d0f00300004014106506105200600c0c0043d00108400c4c1013070400a0306001c00b00318014011035a550103046aa550b402c81000140b0001e80b0800c00242142c500c1d649030f62080c050700004c9801d1811001080c2450b64200031000b01e4820b4800c007076402c564080390151005080d40d0201a202d0b0b802d801c941c2e07241401032a001085460f006a580c80d070800240c504c0d5030504024503141 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6572327 1250 6571077 6571079
    0xa0204060911070305031317030f07020105010f061805090405032110030204020319090308060f090405030f0309160807030c050f090a02030a0e1c09050907050405010c020a05030609010903090b04 85
    0x10b03550009580080c0d615080040c0c90341c2e20b14401c0903002d5180310026050a00501c2d400950021020040d07004941c800d030580500c5e0340d8040264240d4201707204481445107002410031020788034403044500ea0f48444d2201d841242d4850004055490a4500ba0380c1900002004540841072a800c2600855041d00071140d42c581481030150f028802e04c00039014540000004640b03403690722129819409080040000c00c106003402040024100c8440c2e0140122460480441c90904400d9100e61b50040042d80343c4014504500741d20b42002e85062180d12609182d481e01c2d035521042e040162400342c0c0280302051450070700c0900505103504c214002e02019581c1107880c3c13030b58003003a42c3c4203411110140c1e503501d600003410010b00700c60404100900034040e0006014403202030524408816035950f4036a0394880d401c001071403070140c07950004143d04110800c51540154158040c583c0000d2203494501ea80c0c1002c603041c4032040364517900c565906d1a404040541090010016001c00540c0384c2c10a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6573577 1250 6572327 6572351
    0x1090507110c0402070201030b03010f090c051e040f18030c050d0903030c0b09100f1a030303060105030703110f07060f0e0705010203040306020d0219050a1b0f080706060306020307020a02040609 85
    0x301c042c0303144580203540000301c1c20f09590080d00494034401010b0001c102d200b849221032401415545404c891210301c02d44002640d1a00c140e8058074001c2c4c880355031047d10315103010040240350110070700700060b440d1407058580308103074520700c40424000d8079401d520b0f00c4246080390170b01e05040200d60521540da01c0c2030001c268011150a13606520109070705e526103c1c0c0c483c03075140c507101b032440c08070150074030481982030f850b140c1020103010380140e20003c000001100301b5490703001c11140680002c101380009541503100e900540c0d002038002400d030340f4180c15010542c46592042d0010760b83c0c1a124040008014860301c50321030b820000502034911a4203050000b5240e12651101401007a000306000c0c0d0640314540c100c84c44001407075510305050070720120113406608a401c42c0300114210000c070041040440310380d8458654000035040211215955003101c503000800280d9105660705804000140148000c5001350303d01d80090050060910412099400c185c01440ca0141420840b02030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6574827 1250 6573577 6573583
    0x5030604030519090906061106060406050d0f0309090507050a020607080405210408010617070e0c0f0a0e09010806010510020f0309040209120102070303020706050a0b0307150207050301060b030109050711 89
    0xc283d0100c40c44001c1068142003120883c00380d40240385030a19001c8001040c642000901b8030316480101541c80b01d50b40c2d041000110b48940c450b054000792605941030020741c0d219001e401851003070500091558170340c00d40c1d004030b0303804660030381c041000000d021351020303010071815610480c140380403070140c9490381c0d03529110402c82500303079450351590304a041580441026140074214100080040e81e82d5001000751945503809040e40745e01a1074404510403050701061886102c528551900d031000000000380740d5406008003004100e030100d001c6809960b00c07180c1c0d5000f000c2c0c01300281401c1d41402c0c03c00c907440340c2c0080c103001594003901c01000040e502209803141c5e03100840b0010707154a68580800e41301075810317010700215440040c030380b000c164144c1d011b040701c40d0050713104110b50750f58a6510380445c1c0c0b142424940c5944405420040780c0504001c0d00e0407c6243c0c415646030755581c0010030f082d2049a00180509803001c001401410864450164400040d00e4140e07403160300c000480d51 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6576077 1250 6574827 6574837
    0x3011803050903010905060406061401050a020304030803060a0b030411090703090308010e18070303020d080705070206070f06060b0705010504060b090115052107020a050106090203060f1903050703080310050306040305 95
    0x1401004900b085080d5429400038841541100170f803041890706140c000c0c01400180100003521520740d41a0100f54490304c00d88070700c40000d40040d8505411038881d502250802000180e100401d840c0220b000070071540a5400340c4d1051084000c000f85000c00c012600000074080010035107850300300408a80d04c40d00460449240c015040259224142031080310f41c07508030444582c0c07046200000401d6400100110306006941d5113550320b44446e0000c58041c82420b070702940c0883d0038003150000c80c415030440d0410511824000901c181d8070800d585403070700041c48c00d642c140d54034000c02080c001d82d4021303480044022503a91b0115810102607100254460950740100b140105000542c2070300c0c441480164401e4104620480c5400d0100075602e40c000c000c1140d20b542403480000e00d1800a00a8a005078001440312100f1042802404985440350000201c003001520340000816420700c0403c0183d801249117595034034112202c0c1031048075a80c01180264030036420840402e500c181590 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6577327 1250 6576077 6576083
    0x10e0919020702060c1c09060c121101090606060203071712180a0503040f060f020d09050409050312070206010501080c0405091302040b040606091503060503031b070906030c05090105030118 83
    0x607142d031420700100b544c40c000c20700c2c0341c0c140d0b10a0700e03481030088540c2c0c3c4c00120164a02c3d40c0ea015020b80322139048076000c051620040540500603048103030280550046207003d40d0b81c000029036003100e40c0795030040d10515401031001d07030800500e2009004c60140082c030308900c4581c119281c42025900c044209000910081d01502c01900c20f81c1182070601143d1080340d002001c40741c4858560864082540c0e50340314280c0821101214031002600218407400041829164403586524013014440503184440003100c80d40410048459088800c1b840107010303a115500503e1650b04100c0050b200020241c00b18034800c10074442004582d69407200107502c05030524240e40c030651244007080c0500000d07049194010f00308200880c54a5215240c20110ba40c404907141d4030702c441c11001c0d0b0407511280185078150300204070210220a03c1d01c0704400c100070117811281c1c880e66403600c000807180140c000b1140c402c8500d20401c50341c6440c1494501525040b4020410090303050301030342c122600f2034001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6578577 1250 6577327 6577331
    0x10603120302030c161a0f1003060b0a030b0109020309120705030406030c0504090513050111071a040f0b09010c0f08010501020a030e0604050a080105040605070c020901090504050705040614010e0919 87
    0x5001408070ba010741e0102c8400b505d0400503041e042ca02141d43c101d003003010000c0030803100002101013800386500c900604804046440307083c156160440a41a8010050303044855414000000b0f52100d8207503008200d200030058680c10f03d442c40c40c0c1001031810a500742c0303417800c0c8002c401140002c41258200d410509000034903218840d01942c0e0341c0110b500540c4143d2600e401c0020361000c41e0559081e1f0380c4510000c20045640c2c581b031284038015404003400028051201010484004162135003081c0a9040c900d807c4c4883d82c4c46103510343e401c0b070303940e00c10b40d441c1c0c40281c0b14190400402174001100c0e0400102a60600780000e5443c0510040682003181c2a44802503e4952900300c401400020344000c02d0540c80e014000d010780000d6804031800ca242c40c0000e848207100d0030560999131340c0100a150b2a900c1c08402c0d40107010058410354580c00b0306132000809548504c12480202583d1004607100c0000800143c083c08446041c1405101500b08002400c0d00504811068442c04240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6579827 1250 6578577 6578581
    0x3040503100b150406030e0d031107030503040f020909071a04140907030b030709020912010c02030a05030907080d0c120f0e1005070c060e100203040506030a0c0c02030d1805010201060312030203 85
    0x1611103460588083c00100c40000c020903050740c1030708004c82040091040381e99621a08500b01c04407544150201044d100510210000a00c0b9038010f58016015030010781484542d13030009a0480d03004e85080e88160f10940d010070450451403032550a07511983da0040c203052a200403008402c40e07000350944a00d1041c00022800c074001d80c05820310030740180841d0161910790035881d001394408132400f44a10340c00301c4c0d0301498120500039210b810f46075031302850525101030014ac1d56030700080c03c42c0e030241c001d980002c80c4400c001c0142560889003540c2d141d442003c83d0030034034041c1c59200300701c2c0c0400031824111406160040008a040c04040e180e01207101c0c0d4280003140c0368043c5000050800850f060000780f082d03401074048880500848034404141c01169040c3da5074415442941e4002c1018030000b08503601a50015440903051700b010a65080e8560000e404c03e003940c00c1520108810900d544040b2003020701c0203000c0c043c01c0c00200441425902da2880001041a0150400d600000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6581077 1250 6579827 6579829
    0x40204110d050106050406030f09050a06051801020a021c020a02010f05030702010905030f070203070803040e0109050a09080a0c050d03110304140316060603021f0503040209060406150801090605010203040503100b 93
    0x80711240c25000e0790411840d41c40300030060440d070184c45842c0010341800384281c82c6100c03e200c1c17529090780c098010320a803629035032803c002e814020f24400090700654500150f600080c0001c15114185a004d002840f0302c0c0c80c806105c04072054191802c43d80224884001030340c02903031600031031205007070440e120354138040d0482c098980914010010301021503d408018032020207003036658800c07425034080c6a1a03601440c0e40b4001c070301c036a40784111644010000030066074005a00a1801c0c82c0c082202502c81c0c4880343c10340d20801c2c1c1c4038000380884416100384001403010001d0070855240510000300c40440c039100074000034001800c81d051911140c1c0c1d10b142c00300200ca9400040450b45504154941041e000414041c80306900492094040780640d04440c0d52041c0c00e100316855150554569409114a1883c02003625821596030035020031036845030b01c051040c030111030380c2e145440d40c1003800c1c0c101564216403115055501c02d03c010301c084e0b640802d44101841312500005a80c1904c98 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6582327 1250 6581077 6581111
    0x10c0327050f0307030e030708010509030a0c0503040b03010806070e0402030601050403020f04061a03010303030c0e0603151219060605040e03190201091203020705060708010609060302090103140f0f0106030506030303040204 98
    0x81000c29070b0740300003c2c090301010b4120344451007142046080e0b4800d90b540e114014262001155003500c2e5801c104114002103003c0c10440b04694015006c5900746038a800e801c0449610a07041013095a00c94000c005507158072401583d0b0812050310b080d815070410f0000070b40580a940402440303440c50f20300411181d150703030744520020b09070122000c042c0207011022080b41d61080c00207a00090411340034807549405800c403103050410240c02c980c51075913010842e40c1507411441c1d00b2903122895012803140564208410b505d06070a644030700c05044036602d40300c41120303090360045000324142038805032160004003d0f508000d002501180042a009804038010020313040010100c01c031f04010001080d41c1036001e40171207480343c81212a0381e100c520741510344200034440c0400054403450b042c011144070390050002c6000604001c96a0701041500e05034012044072041d6458110000304a490340e070910140d8018481c5c2d0500300701070b04007200405d031240f0004001a00842d12840300c500c800e030f088 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6583577 1250 6582327 6582343
    0xb03010e07062102030c0301031b03050a1103010e01050109020316030b0901090203040218040302010203041104050f0105061c1a0306070503010e0402060901090801020d05070806031603060c030e0a030504050102010c032705 97
    0x401c3c400c41d035038680b08048900d00d400038001500c40e180319051352070480c10954081c10999800030010410b010707640d5900c2c1501d081240c20f498242d501c413000224489402d005080c042e010700100540c90749000c1420300030f2124952526400c06080803224806074850f10030a42c19503191040140e92607907240003148042500e40c0704880d48602c1f003000c100600d981980a140180e105491008101d0041d41c10442a02c100b030b995209003841650041003140307040310040c200a04626801d030042d00c140216002260710010140020503d1000700c68040d02e070a0000a40c824060b040071070455051070804841d40d00300401c000d009035400107000e43e00c0e81c0150f000000401e4600c00075961143d2800590b8043c0c0800d94074a404100740c5400700d8182c3c41c010420060314518040100581c7e0b20b581c8072100038100301c40245050581d5400c4010000c4000e100c6400c456020340c413903544e83d5190400090859000c49480e504142c5840351003030f41d950b4110395900d0303003207141201c40b941100795040850501d00a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6584827 1250 6583577 6583637
    0x31602030c150109050105100203030a0504110a0b040f170304090b0112060b0903070509090c0913080c071406030103030c03080402010306090e07080705060f07020108090a02090103030806040b03010e0706 89
    0x20390309445010742c0c0c03203410b214160707846024240143c0c1d903540c0610040f810324001400c0984c000384002440104598085507103c0d018040302040c101403440441d0f10300c5450741101a0382c0100060901007a0103c10f105401481541020200ca040703d940e8a501d90281e4011144200d03126200618140e2091802840c540a8200d041008580e03815015070143c1c4103141c0b240c084c0c00342c0d880001d060324007030074030724800e025003005400a0740740b11003008003182005052643c07049440c1d010801190084000d0b06081e10110010008a81803880c10715519014a001a1080200704014000250b001d4100c3d50906e031316080410071030f12039100590240109800c0440d015180040c0140881000510501128100c005071441b01d0340b00e03001d02c00c161045138400b150282003001060700652003101c0407039206401c00f0540c1c084e035001b503001928609007a81300f5000078602405101d402d2505105031154580304400811409592124040d00d8030f403544203400502400500385490800310010482c00e6400d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6586077 1250 6584827 6584833
    0xd0f020a0801051c151e020403050f07080109021008180604050106060f020304050a0b13030b0702010518030a091401020304030203010f0509060624090402070b04050706020d0201060b031602030c 85
    0x1101200041c10003800b486075030f22403a0045655205402808440c000c025048582d400d00c807001c4440250160103d0700810880c25144e94a071101c12032144040e001a40c42103010785801c4000c0c203c09890604243c102481e56450304001c0d0b030059640140094240300075040000030b60340c2e404e049100c1c02d4011105084203020722001c000801406520080075111287c0701d000c0f007549907880499490040c0c1c0901504401252402e12401a40c040038140c00c540342149003043c10b8580c3d5441d80803950680784200942e45420520032030110b00c92054400946000046040241040c0300505003119446040c101c840242001380e00e0341d1003442101d018640140c024401480040c0383c0c5002003d007111002202d0154401040c41440d04038000201c004801e10045030800d840410022580d220160550344181d081049500069003e010036220350300402c09088003501d003490103410091411002011a45403034000e02c003d42400c802c2c0c0b42c000b0414440030b41001034540c400c0e4070303604c522440030003144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6587327 1250 6586077 6586087
    0x402060903010c0206090d030e07090f090206070615060302070b07030f110403050601080607080106120c02070f08030d06050111070608100302060304140f01020906040308090109180e010e03030402010c080d0f02 92
    0x742c0006170300e80079005810440e0041c2e9007051084040314108850b00d002904403140404c680004c80e001142c031020418000160789940b075001130060f03030248800f03e4a20f03403945045243d00c1c6c014105240148454101580303071003015a01e220403034070000c148406241e034641c0103240b42d82c071b650b00501c100100100f041d075030f80e83c4070700744103942e00002d2103000c41a00c5800001040d40740b0504034603040341c0c080d84a02d01c00034200b40851020300107490203042180b00e40080040c0b80074a80d591000108410340c007444d519120070400c01c0070746405400c442c2c10300c01650340c01c525000000030030310121390003440d0042071034660b082940444011a440a503219402000344424010509444211080c4200032106c00b0044000c00c98240d00030001842e40c811001d020030000300304442c00400f204801494080040303600c41030301180c00b1075003a03101428595a0034581101c0c3d04240306080100300303054015030561815030300081c5281400040104403000115101d0f00c9003140b42c00c00009421910380543d00c81c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6588577 1250 6587327 6587351
    0xf0c0503071206150b070f03020c0603011403010e0c060d09050703020d0c050a060c081c0209040906020c0c0a03050d030b010507050f1506100e0f0604050a0815010506040e060108040206090301 84
    0x2514504003a51075514084480b110442c0504d003180454280240003030a02000e42c82c0c81503407001c82c00094081d4001c2c012384405a90710b200086029044000c9000400805136081c10b08542048100082e1540120b425610340c1d0748110a803807040212032004140f0681e585040da0070320380d003584000c0d00091141c00e1007041180c1c0700c250109851065500c0010305581c5c3d0390031180324410100c040c0c24201c04010144141c07803031203d101c94070185c0d45400340c603002a140105080303c1240c802030301c91aa0100700560b8190003804140c40311907080f60803081442c11a00d51a40b1040801052421f02d6581d00d0820916401101907402c44c5800c40151841149a007408544464085400e14034081d00032000801502d40f043d41c02503140840c0e95034800c214410410b210a5504460605500902c1400300107240d954240c0440c01818203413000e4585011034140001041106030040c610840d030500c01400501c001010f1603a0000c024039000400b41ca40b800031582d50701c20003400a4040d4204901c0f0018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6589827 1250 6588577 6588599
    0x40915050610140708071106190e04020901090504090609020d0803091c05030406050402030f0304090209090c0a020303040303110702040513050d0810030f020301111201030311010510030f0c050307 86
    0x400c40c000d42d00b41c0680624602d00f100c40748060108415080d605100a001048410b4060b1044910540e443c1c4001003010380020520341104403210344e19500c030320107080342d168003681c1d40d6003401040e5820741c140300007000080d1200342140a82d40c00703a65554069018040d41d901701ca0071003034002e0600c0541d016030742014031259004940e002460f1148050107040145402d00c1010311507482c2c0e9545007940c5895445001030080034000341e038140324100081400342020700040000702080c2c000141c0e1406404184101c4440007403480d0100d40d001c0c0240c2040139008000c036035006030315240000303c0001c1103a0850705c5000d540b03006504203262104100042e00a13002180c0c2c954010800c6840202411808640c0d040c01220705130090b298081c1c04000040c94039200c1c51074a80300400210380c0000d10017086e1840d4000008858035440e1500041060540001540f0b502c040800001e04c01441c00b8154251107451920005100300c01c08401c2005202801c0b52050107400020262811140e540c844044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6591077 1250 6589827 6589831
    0x509250608010e130b10150e040b030a030903170d11030a0506040608120c01180b010f081c050307051b010b0f0405010e01090b0a090501030b01060f020606031b04091505 74
    0x40428488400480c01600c003da000c0d203c0c110710f001aa92180b0503560707041000f4406042010402d103080d4010403001801203183c1e1041c0704658130f02200320703c08801c01c4160f0380c40c1001503021b90840c10002000c41d600c40010016642c00400400c03400050f1000c940d424441c110340d410141e031a02c90130300328110b010b41c011401107040303003014492602c85104001c200c411500c1044c08992120041c120100310243c09040c9120444000043d841225499002004c55a00080f10901c8900f401804045279014041d0094400f07c8010801800c1c140c0078070300300300c0181e0f8010701400808000140e41510550451702d40c10980651506242c861400b090b018010765200c40d0320030740c0f20200107206030070144a518104d4480101c1c03e10036900c1d00d4001c1c030052018088480d00070a50b44004200345d4000d000b500d00a6200c2c2030134038015803500400900503029a80b0b00011500700400b40529a54001609030000900009640160100340000f070000c040340c580060080c0c1550321044910206544024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6592327 1250 6591077 6591089
    0x30c0303040b0f15040b180a020705010522030e0a12060e07050103090807060506040608030403030903030e010504030201020c011101020c1204080106050303070507090e03090a12030306080c010f03050925 89
    0x1040b19250f2640e8035802c11811100c951000e000000122400d01e4190006e00010b04041c014804242c403140b040320035a841100d0350702c1119000140301081060920030541c3c0324201b000c04114440311009030b4050180300003000707000c000749008008180c1c1d41d071054540040889402075030b10894076150440280c4920803482c1c0d0720740221a00010349500034001e03074601d40e0b80002034a01c7c0200c183d035260018240540455002581e17101c01240c202810002403025600035102d0044441c51442c0050035101d2484003141004020300003000143d0f00018034261503902400d1004886005494403402401052039008082c800d015041d030503164094001c000307440c20341000740003081d1100c040c10341d42d02c200440141550f00442c0d082008291644c0900c20020000d42500d2504c01c401c0c4c001408907209410003122010340c003e0300300800d9054441c06c2d005000e000c02070020714103030a00207016210200500d9042c183c4035400600311140500c1011080c00900b024081907500c03201d031070b064500050203a8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6593577 1250 6592327 6592343
    0x50603010e0f0d110a02030a030203030f0106030b060306100c06020412030e031b19080106060f030e010e030306040e0a050f03040303080709080a02040e0a020307090203160503190903020a05030c030304 88
    0x28549400480c1c02c0615819080c002e04428190010480e51910003812124060043c1c002840060703406000001507a40240c4c002c546a00f000c0a0721040c030541a80040c003450328002e001407031a225002500c0d80000c04503108108800b0300c02080d60040b41c0354100901d018400200412120110209402d49a002e55100044e136460b400c00d050313490500082010703058407800c2006000e46444011120031003814000c540b5200e580c0d412040c291203040c1c1003640800c901c42d141c011150350512031002031a0380c2c03400034010036000300391283c0c50b8403001d44403d0140791202000706d21071008210356001f4591081c2120f00e5038421910441d00c9400c1360000320300245200d408207094921a041490a4441240142010355025420040140f00229180c0d0b035500800c0366907405a5402d012450080c9a41e441c0541daa1910824901804101821071000d001060042c0829984182051181d842c5031000020781000c642c1810703407602200d030100410a200c001070b01e030100400400514041c40c4280c0740 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6594827 1250 6593577 6593591
    0x120100e07060908010b060d05090703080a0914041a010806220203010302040507020706080106050306180709030212011404020402091906020307150e0606010807030f020a020a0210050a090308070215070605060301 93
    0x2c1303507081e100c02030380341c641c40402030203404a544002c0c1e111940040c190740c00c132103010395a6521400660001c6181c07401040300404200b0105001c0c0c4507001e001042290100100c0f4030140c40700844100f00c3c0003c1d1704100d1600d00281c40d54984000c2d803020784181072500c2c2442990031030380320069403003408124021800c000203d0119800060480245c070b607151201c241e107a0a00034102c8040d00300400c3d40780e01207040600980403141c3c22800901440c00d5a030740300c00c0181140140304089034440c81c40b044c00e80c5010011106003400703c0c03045410907130440d0301503910700c3c141001034114003044a0000115052100000c0c030f29070000003d01005118160011780c09054030700130380480e01010b0304900c450700860001615036100d401021740c050f00d54240003941405000705103040703070044004180507a1061112005505e0980000400010b00e840c06628001c09054001d0003081d19110042a80c0c2020074000119a144c07120085400004204962120051f04060010740341c255202c40c040d51070a81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6596077 1250 6594827 6594839
    0x504020c1b0604030528060507080f070203030127091e151104060302090102010615020a03110f0304060f09080a0c090e01050106050f07050c03030304060c0801060503060120100e070609 81
    0x6580880f600f00018003146010f0a0b8001d105103d4100e40204500382c60441e1b00c002000e5104080c0564055980c69900e40380003480b4200202c0b0241603402954014401001240c3e032102a0680303a40f0034600300402c962038003641902801146000401580042c80b078598251044c03a0100c14044c000c0301c441164600e04483e10007151b41a821030164144c0810003400114002c4d001001c00100610001410a668030b6051541480401c6902c0c0140c0103c5801b0080c560300c4091a08002201d001a03c3e46100b00022107903a8400e9204140a006041034100b003880d006004050041c00058240e44001f040b03443d003210071100c54003d006405160040c2da507140356051203400c1c103035000d50300c505180902088512400b0f810411040300e25201d01000010162070920182d80202d215440118508440c40006040403005030003000811806000300080d036030744501d0704240d080d40100740b401c007022030082942c105100743c01440785060400b01e0742c3c1c00002c4002240d9044a0b00e03541c8034484503031a12 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6597327 1250 6596077 6596089
    0x30209030d0c08120403050705010606020706020f01060e07210606030c030c05030402010801050f0f0607060b040605091b03040305040e040c080708070308030a02030c040503060f01090b01140d11040504020c1b 91
    0x6800c0070380900c44d06082209449406420038020b080960034600d103aa9440c2c2502d0b440d42000c40140c2100c1010000c150b010423035241c41800c0d1100a110305402c008000e03d8403800149200f0402110034415824a40020b07603410000511100602030151100301c0a40603000f418008d80010380380450301b07042c1c3c070f1040080e030b4007440d4141d40320407a5034a054100260550214000ca502110a4400c41c2150351008000d001440c81900b0100e030800303082c0100720031280f20790f00580c011103901080110303088620a110002c00c1040b0b0213540c5030b07280c41c2422a00360165800146035080b15609010502c510031003100100c4c0c5a40084801c0e858071650340b261603030b81c280b00050800c241440403c035084000e401455010380d14041003820144d4074000a454104166982c020321b000200051041c00c40c54026040588401c0c200140f41c040101d11031443ca2086d040f03403c1d0960758448161104070b9070304088800600c0b0041c41551501c541400319502d034812142100c1c02040c14a0f40000503081c41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6598577 1250 6597327 6597347
    0x605090c040e0703090303020d15030204050c0f04030f050705041107020405010f0602070605070809031501031202010207020913020f060a170114100f0210060e0402031011090f0102100c030209030d 86
    0x4842c1400c11034550f50380c1500600305503070080f818590240304e80350000c4541e105a15003100b102e5400103500c1c0ca540144001c071080078001b40380418041207408980810f00d402ca404407a03105100704501545030400d1814020700b03820042c2d00074100a014a0220041809460058000c4070300b0032860366501c06200c400c000500c42c030005600100343c100310483c080d03000b0b084014005d14406150604040000c0e0404c42d01c070140000d02e0b141d4800500c103100403a03e0f02c21201d01140000c5240030f41075000503080400081c21810400340880c0141c1c1103403101c1203c0110004c0c050201a02c500d08140c000c5c0c12540e0014400d85004440d000020300700c01d0782600c458000402820040e07204d10604411070b20041a8100007040d84600a02d00384800b40d94800c183c01081d4a07544688142005d204150a0289009503014020304040400c051200d40408952161000300c0d10b0349070b9a0b00e0040142c0c1003450b01141d003005103161681c066040e43d0103030020700248108030240c8003139040c044003e40e480241 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6599827 1250 6598577 6598589
    0xf0b03070b090a03050d020706180608010306090204020c0a0b070e0a0f03020d080c070602030a12020307080f0a090203150603011803020d03050a020c1902030106050105040b09090406150303030605090c04 89
    0x10410080011150010003012041005000390780f140d40c8070b03119540340c08144004200140e0000208214503a4015a590b40380050008084445407524900400c41c0d01c040c080905503944d10105ea80c11983d483d4125140300190310159501c1c0141c0c0d041000021070200d40d480b022030503101e40d524880c60110225800d542c13500c3c5511a6041c1590240010444100740c21143c82d2410003282505080800080c40200701c99801195076107607044000700802070116402903410700520900140c00d81001c88180d00585620494600da41c8007500e0700050140c000010f501400f51620030b80030264003141e01849140103074001e06c0f80410219483c14910113908000d801608100600c031000c0d407084e000701e504495000b0015090203d203264041c10300c03128101d11302e91070b500d0100040c01c505003800340c2c0c4010304003406c10a003041c0c41c0c0002c81415101f601217444c13080280d44001410811568000704c0c147c1180613120341c0c0d483e100c0c9800340040040e0300400d40701e4034869000540b941c444600311401d07a10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6601077 1250 6599827 6599833
    0xe12060a0b030106030c1202030d0801230310020d020d0507080601051603030902100c11010201150504051b12040c090902060901081504020c070501030f020705060f0703090203010f0b040f0b03 84
    0x519031081000814507548425032554a4030800030200c1c00d1400c1c503c014001d0031000f0100740342c3c0392041514007400003108505110801004200206c5203ca4038a402d004040c150840390355503d00090520104441d00904e42e0300c0403940d0885c1000d1a03002d841410140740c420011600c450200380c8101008507940f80c001002000300c0004895203201c00c1c94154844e0502044000c034a40c00905d0401c10880301600069a2407442d0050182d000c102c401400001c2c0000c2001d50403c80c44584240781c2c50190300d001d26180c402150304081d00f03501000301499404001c3c0d40b94002c4584070090306405441c20703a181d18007404086000e489a1141d55046940102054584141d85005640d8048024000c070500001035030b40c0101a140d42c0001d000408002d070207001c096040800160483d00710064a0440d10310601c401c0c8000f603400280190446a070b100d240085603907101d000c80191640303210094140d400c2044035042c7c3d07940c0d5008120391540442d410700c40300500074080403c82d0100c00200b035140e8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6602327 1250 6601077 6601081
    0x304080a0c15020a0e01020114060109050d030e10020a02010210110306090411030d020102090102010606090b0706150305010f14060d0203061506070b09060907050d030e0108070c050105100302010e1206 88
    0xc0d00407403120990500c105110b00680001d00c140b401284c1210060070302003240c58800ca0000c0d0ba081c45144242c0c004400c01d80300038205580000d0804089000b0a4019168945400180f40c012803007042c0e4124000e000d1880070394400e50080d11800c800d1070407030261043c400d0020024009014018246594410041c219603a170070400180c40005401035402c40c9020b0440140c0e508c0a00014440c084250009640c2d1201d01000a0855500e030384603404000501d40f06000c0b50820344211007078650000404a80064800c8904d400c184582c0d00091642d0703e40b1044071134104c41500641e1a80044186d00d1069903518414006030f01103151000398541c00180014403141d411401d04034242e5400307009541068811b0f0b40780b401246040d58044516444801007066402003045050007908050b10140c070340b881d559401500030001400e2260510000340f0020b02c0d5076101d0702c0b03c506066040002400203080c030310245100e4492601003680003c000d00d5500119003000d44005102c0004800201229 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6603577 1250 6602327 6602347
    0xc09060c060c0e0303030a060e0105010c030804060b030f0304081b0915010305071b0c03020307060302070f0327140301060b040b07080d0209030703050d1101090b011404110307050403030207050303030408 89
    0x30840c010b04582070180201400f0040e07101040954850703c03800800044c031038204404c1085c5244143d0100341080005144200003d504c0514107422503031110002c10400d142a0000b410421450840001403101080005403114001081c3c680187c4100916425025005c00c0c030240300d0088890b403c132100303020325503102c0d03503c03039804194450071a2800021450b4000b1804803a100040740540d040c401c501800e000398942030055500a0000342402c5181180d15510704040c3d2003c0c0301c01030144507249000d022052080b00144803041c81d071a411804190700c644858001102901c0494040d6103840400705480710709008590a0b15910f04a040c1000025503545903643e000c00f1210f401070303809216600c81d80e2820005000918421000b0f1700c001210b1060050118044000c1c181c0241c0c10000c01e034021031300e58640c041c19281d000d94510603503c03105000c40c0144c11200c0c80c10703048900c000300f00000b43c0c2d405400303402902d03c680d0070703200c089a440d130415030340e408156000340514030200700030124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6604827 1250 6603577 6603581
    0x3050301060f030e0609010903090504050403080610020a0203062d01180b01050405060d060503061509070f0201181101110304080303060603060d05030a0203070c1512020c01060305010e100c09060c06 87
    0x18002c1c0740b4000caa4500a50002400d2020035189510320b6915082110109034000c0c1259028120a17a410011403a040d14011300ba10030140c403642c021707504602c40d469400d01c284141c07003505401a04454250a049451720001809030304400750040c903000404410b000c0b0810f5860481d420041d4807170384840c100e983c000092000c00181d605000c010400000e90361658130150040d101c0824001802c28035020600d824041c1c018280c0e1002c21f2a0750030030929950300024250080b60310715049050014190301a401402c0038154110317a402504000c2c007c000c59528150510503003030342d41900b941c0503030310011f0382d90055000b501038a400910000d9217908020010f598800c500605141c003021950319001c0c115480194560010b070000101c200c20b111003040102c0090200c1740d03a042654680366401412004802c42b40718800344c00141080c00c0709000d41042020350742210007000210f04404c070840d910074400c0c0d0040078090400040140c40c038040c48130309040342c1172922400c040354071550799800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6606077 1250 6604827 6604847
    0x2090604020a1704060c02060108030304080403061104090207060516050a08040f03021e030408011104031101030f02040906090203040b0703050103030807050a090e0a0207020f06091804020312070f1401090305030106 94
    0x200035031240315410000443c00303032034000d5004900009080c81c1c0f40c8802410020b0507000040194010001d104c0000c0910b82210f084907088400003071840c1114841148030311aa60010f00c01600110b5044107000060348018010b138845000c20f540c040300d0780c2040d0380c1e60103400c8403c0c0101d10508001750100707000c0c1c06410002131281c4140c8206240c0111007aa01000b2400701c03000903400070600b40161607003445201e500c4800401503506181c60b5944011200a40a0010f0f040503100e401c00d4482143c00c0d01503402400340e1107001d10400d9103a9880d54000d400848042d106480098007045000703000384a0a03050300e4045e51f6128080d40c1e2464161150f920082241c0b0800c07454480001e480741000385554000c2150040c0542d68250500403c0344006296070317500e21403001040707a600d20b0b40c2c5020b00403031098802e04140201c0d64442c00042d0900d082c0005040540d41c0015200007049000390300080d2091141c1c0c40000c90718005400103089548080006000c54810001400914042c80c4150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6607327 1250 6606077 6606097
    0x180f0f050409150203040b0901060b040b07060f1d0c01090509090304030f03020a0813030308100f05041a030a0303020301181407030e030702030a0309050a17060103080705070308070c0905060402070209060402 91
    0x111041c4083e07843c000c903030040301c00f580c10160100c00d00c00000300a014200052032040c188a040600f4416103003035900c0388a800416040d91420140000e00784d6800001114059010007540c4002890f040340d1146801414a40040c980e030b200400c0e00d2504206c5070307000740148401541094199a15185220682d54040c0c0c254031139540c0350400181e500005000c0c010070400c5480e00c082c0f079454080c0401c403000d031100002080701007043c481a454134040303000300d0700100ca000c034550100326516080c0c2c030340c081145501070003001c580000341078054000310304030341c21026450203081c611007641040300c490800b40701c03010b08104041086503109801006200000405880c80d0070744c2680003d1428240000417000b18250000c20450f914040030b00b20000d11903100204160034a03a000903031109414000180054000b183e010240403041200901855111607040e0b9690039608000044103154031458842e00d00341000910141000d00036aa0115030182100000e81c07a41d204000107074204200078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6608577 1250 6607327 6607343
    0xf03040306090f170406090503150402010f120e010e060105030a08030601140904020304030908060a02160b07020102040f080718020405031f0b040204060c05100908030c0f040e0403180f0f050409 85
    0x403001040d020021645031100404c00b07203a40f40c1c98400042c00246503603100da0b20a40080341416100a102e42050f0761040d42441d00b64894824480265900031030050803586480c40d0100c03143c4000c0055000300840c1402d1001c0390038584e69003040603955546590f0081c202d1500b440420072950082e84c03000048071000880500b0100c41401003803c070f070422103080d000202050020000d0020034842c043c0c0045504005500d030400344030b00c0118040d141c1e440100109000000103070420304c00e5056a015000d00060307000725a03501e40c101075941295002d20700f6030142002c40b15100810301c0c800c8800b11a4090050900d03d208490307402880da0580084e1090282c590b10843c060b80e880748020005000281c4802034200c80d0b42c00c1081c90990b06414100016203003807012404103100ca41941da001105410a540c0d503200302e40204010700582e0300a00303402070b02500344030415130440400b8404040c0c40e00e01e60350155032a0603921402e0f0807445001040880c10401b8011b07410140c00590003d4054622 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6609827 1250 6608577 6608603
    0x2706020906070f03020606040c180506030615030f090f030712050702010e1c06050903030106080408070302010f05010f051306140d0204020712030605090a0c020303070806010c0b07030218030f0304030609 89
    0x81c021482c49000070444c0160050020410b242c985407084003545401c40c030386a0705c508649060f41c2ca50001c14001c00f4401d800100010700380741d40341c1201c11607002542d50041e44030f00700303a80381c01e440400942d80e0441c2e0780590440078524020000a6070030454200b40103140c45500040240c070303d9440407a0a90400208004030401d0ba00d401d41c6c100c03400307805402d08020440417400c1040c1207840280104001e80c10420041091680c000c06880d08150006d480315074070700c4c00d0714003a401000a6400b61843c1420f0074000510140d0b0405001c04071001504d0100d440102c0000e0101103c5440c01142d140c501807000c1c07150300d8246104420806031025100620380803547d03c03a01c2060390120310041c0080e80f00c070307001e011b030b401d0800145030400d05458040c00130650b140c40294807030200070040e20401c003880000868680c030604021041c0d503040f4000c0c61240c184240014080e52000140401c40c503d6000c802480d818000382403d41d24210f00080c41c100f41c11035640e400a02003041c803c0c1c2c1c0b0b24851002c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6611077 1250 6609827 6609833
    0xe060f041e05070801060e041406010f0c0b01031101080601020a020d0b0606071a0105010306080601060f030207020a050405070807020712030813050c060a090501030605040504080304060b0102071e0801270602090607 94
    0xc00c441c020060f989840049600d4440d0041c580b00c4000e0205001d5030a01e1202d9082c20f4910000540161007401c020310020b0780100708403900312012401a241d01e90110000041c024010041030a8650a03610381300396079602801665186084840207400480b021811004561030703604141d0051002401c0078034080c40358484078540c0ca10045200101c842103001040a0740e00761041400500c03c0801401e0158941100640403510f02588a818150005200c0b02155074904581c005403000038400c10060402c6070008103110130490b4a100544605000441c8043c0d00048809a882c1d166543c01542d0380d690b080d00600c840b19110444030b5200302c1050400580c1c2e101c010384001c96030f0755114080b25180800042c10780701650f0083d4015890001880042091002120380c03040d080340000c12043d2500c3c0c0102e241c083c4030b50140d1190340c0121350000e01c4e0701d130060101046800601c024441803582180d807004031075004035154041c0510310801c0c40003da158000e44034900c0d0041c10b00d0705010b4182c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6612327 1250 6611077 6611081
    0x50105010503010b0d05190e01060e0708090d05030604060308040b09090a0e0a02130905010e06040c0e070f2304120203010b040507020a140705030303010e07030c0207030203070b0903010921090e060f041e 89
    0x413241c440603510740c80140006a070bc803243d1a0f04c00002d00d0041a5414982d00264440008840034410050300200141d19615240c0080d030081d80d000345000c0c0c2c0d56548002c5203115800c4040f00b14411b1103048040740344a0818003500f00c5503400e42c07000d400820015400c1192480c0c500c0394059620f52203420441c0414802c1c4108040c1882c0c0001500300340c135162412004100d5160000c1211418241c14044600d5022601071092081400c1c08180420321400710920000c4915005541c1400010003241d0900c1844a076110713144207400901c041480c2c0c0c0100002c1e51021100600160301c9886d07907a0100c1d800c0609144a10f0054040c0d45c461500c2e100401d00f5944241c001180b68100e0105110a0366450700c45c101c120a100c3c40600211400c0d90700090b110051442020310840010811001d26a429071024280343d502c000004825128408588480b07203210780e000c070109001420004000364103103500c40c442c7c88024601c0200340c0b230180400008000c3c00d00e2051150540588000c504060343c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6613577 1250 6612327 6612341
    0x102030108030c0d050c061302220b0102010606030207080708030402060c0a0303050609010905060d020103020309010b040501030c0503010c02030307170a1d01050a05060307030c0308030a020708041404050105010503010b0d0519 99
    0x800007071a52810b03c40a6185402040044d20080280411000c00540d00216440c0e070410844035200ca60f0f110240001134008215600d00300c0c110f0303442c00c0c00c46e0fa080455030000c54021820b80007841016038850303040d422405000c50140c0312090801c19000011300440c003e541c0240700401250400800d0b640b90b61910509000885c00700750703a4010708c016454595446801080c04500030702003417401c00b02084083c06401002818541c0100c0885c2800f2402c2d000b032486844050010031444d079582c1003181200d03a071482458040d5190084601c2c80c5440442100d114404540302e8003028240354510440754880105890f0303031300307a45240c095000d28140b520385c0300b00f44040b0004501030074281c00200480d80080c0083e4801d81c003007a0b0400008003e070603050304407600102d015889a031040080d102074420303508010082c500004001ca11400603103003600541c4d40a64040040d070703032180e00558882c8401c0c091a025a0307070a0000c590003008035008281e1140003a81c0c2030b403c9040307a0003200292252 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6614827 1250 6613577 6613589
    0x90106080f1005100b09040504080d0e0303010f1401020d0f020102090604030b040b0f01060219020a0e0903040303090503010207020d020d05120f04031502070b04020d0c03080d0e3d060801020301 85
    0x114680704840d0006078041d46810050b0250842860703460100710317010a02c42c85421034007440d100c90000c0d05100300d00040d2072600410404c00d11001c40b20840d003a0f02c03070b0710900802040011619010440031031480c0c500602d80c4041c0c008101c4009007100640343c60042d03102020441d90200010800c0d03489000c0031344000e600c1044d100e00c403401d00d450a00e400c1013000b041d8941301c880c1d01004208099001444a1401d0740104412003d601a0b0010900520481d048944815020740a2084824002000f04216402691203583e500d4490040500380e1013523081c0a03500c9400501d603000545440d0310303441d10580c41402150a4003e151070a05081e41001110440342c0350049010024031000076000c60302c4810100b01185880c1ca196030b43c42d1012030240000c6e0040b0f0302840030034200044c1c91288409150403003080f039200c080209440003e040c1c442458816801500911890a4009101c120300b8070302c05040b000c0884013105212102a9094004840f101c0d02c0d15000200d50700c0a20003035020b801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6616077 1250 6614827 6614833
    0xd06060b0f07021206090c01050c0c0301060611160b0702060309031903060503010e0c06030a020306030a06020c0703210804120306050a0306050402040b09010b070602071104020a02060603190305040e090106080f 92
    0x20540100020190144c400c4050368001e8010054500b0f0085035448481409090450320789100e64442840c00c1c10070040c60fa010b62801c40b0124515030003901c1110300c0e21500080b262041032806d2701040044880c495500b000078103011100040c9400e4010b940d010b031800c03003120b00740320a001a03100c051000b181250003280e550039007404241428092201040c0c5603600505d5001c0440c80480c1151000800c09420300341d0101c04100283ea061102c280465000355081d91240c5080c010151181c5040c402169200004540d41c1c0d951038201c8450052032400c1d40714031400d9a070381e8690082c441d100104407010103954500104555a40030921005103004000006aa182ca40705020031140020b184c284600d9004004012103c1500125002158030400250711541c81e0b00e840d444030041c02d5103840d401400411188070282c1e00152007440703050b04030300716075907e94920204100255030070005400600104014484050344030881c0350080e10807800022100d42e174821060074460209442a17040d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6617327 1250 6616077 6616087
    0x30e01020f121e040305060124080702150405011e1a0301050c1801020102070204110a08070503070f03050408090303030103030207080105010b160201030513021302040306140402010e0d06060b0f 85
    0x940c0c10445258654842001095102c2c0e40003800703035650040030740264040758900341008500520801307840003954428100ca249585a50142c3e02c42000104030401c05510805054801ca01c40e10712240900c80701d8024043d0304c1102c2400c43e001110017001606c556494510300701646010080d0101110100c2000182500f6107030440c4c80c40c4201143da0701d203c0d80c1090700740529012000c08903143c160160740099481510500140e01a0250303800184d030207440d041d00f8881114501c0300500f118061079036224401d80c0e03401003c3e00c070b0340811389801c00064003074142091454000d611240c1c1040c000e074107007410038140c80006441e5078426002200142c1002c01c0c200110f42c004d010b141d001d08641003200d414010008040301242c0c00640d00a4105900d500c0402e80041c0e80c1c7c001c481c886070b00589102c12084004800001039401072000f01d07140303898408d207460b400308202422070145505940d0000c0c040254070400050510344141511110b0350b490f800200708a00c90018989840700f1480d9984070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6618577 1250 6617327 6617329
    0x1212060801090209010501050c0f060103061a0d0c09020f04030203030703030b150702030d0f03020c0a03020706020709020c0a03030c050c03040e0403120504210c020901080307060509030403050309090a020c0604030e 94
    0x5501a5442811541e041051100c01a610f4a108905481080c40c0c96a1107018034081b403841c005400a001c20716025000001c0103008aa42000100142c07450f01740314900407400901ca201029040080c04640da010360034840d951007600242003903440000d0250410761a500001d0a5a0020780105c010039a01c001c0032646003003001c0c65000e01942e81c1945410b1020640110b52951035400320340c801c011005040050103402a4145c4201100d02012510b45e03541030301d0069511044c0780a0403015100300704000070640102d0007110100c0f1040c4d00034000c08000d503507090340a401c082041c0014410140b0024401c40d0080001e00300a08003140c1c11809410142806041c100703804480e0000741d41041700300f001103070000320341c0c2c10762104110142e08008000340c41100c5c4115640402035001c1070320b0000040504000001e00a5140904c030200319540301c41030340c2c960764805c610000b42142c206008c912038600d00b4281c032592103031030f105015240c02011015a810000c0441e42140812100300b1078003d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6619827 1250 6618577 6618581
    0x60a08070b090103021b03070b0103110a230303070b0a051e060303071407120b01050415050108010e060406030b0406050f060406050a0302060318010606020601140405060105070615031212 82
    0x10440000503000300c6003000c60196861140500c0315042c1600003071001c0c030a0440c0028545502c4401d001c1d640c43e429180b602d417504034404c1c0b106903035800b41c00400d40340d249061142d0004440c401e409203280e140080c0381c0d85540c0c50001c200f442d410b001c14007a09000c14011f640041c4070344050400080c06182114160001c0c7c1031010249181d501020200030f1103480000c11111015000001c4a84524020344001d141c52142d4114540074001d200f0301c83c00704100b401c98207050700c070200c606210007207a603074903185800d00610440d40081d42500040003131400c03a4040c01c0c0c2040340a030020484685941f20064000c106940840d5180d5176a820005100c00209a40c1e4000d1411501404070070b25041c0040d03401640790001034032a42c1c00102103040011001c6510045104090080c8086a038032003010b0740382c41c002d104040390701020006402140c9404e00c5031074032443c0142c40d1181815400c0d15100010060b84e242c26140c0680040d0110100d02007500c0100c4180e080c3d6142c000340600c0a4540003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6621077 1250 6619827 6619829
    0x150e0607050408100510180e01020a0e0f0303030907060807030f0c090302041a0603070522060201060e0a09080301060804030201150902030a0f0b0d0623090c01090605030f070f030213090203060a 85
    0x1d104e4544014068068681c0e0851030444107070a006480c0c4c0c140c2e15060724010013410850070344543c400200304010942080c01e4119240c0115417020041140b003051503181e00c002c503a8041c6940002d002407244034021000160880c0c018900041c1802c04003005400302c0c0c003500003600100d01c1400040046282c1401034071503d403039800d043c03140507100c08082002800043c0210b424040003207942c2d0441b40d00c80f107407000c14407000c80713090750703825500c400190080c80e2500400d080c00d5004030000701125018012801502c0d4481c0d4180d00d141e103092030441c1e41442c05802101103548648403843c100b188802c100300032b06810000180d03603051034545001103801184260902e10306241c0485400c2e0f442e4442d41030029003041000c10042d607440b00100440044c0c00c01d01c444c0707200c64401e01047c00c000152610200130203032141d070746c0942c883d0b6041e00c4502046810b40c8510708041c0000c0c40700703481a818403500510390300300942000e07840c0003407051941d40d03904042c4000390301000704041840e10301000342c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6622327 1250 6621077 6621103
    0x6030c050f01020a240603080a02011407080610090506030f06030601090e100203040201091d01090c0815151b0a020f01050c060f0411040501030602030a0b0102011503150e0607050408 80
    0x6101d9a030010b91100342100015019941c14913144035008401e929030202184c0041041100c030741c40f441c0846068020292040056107440391017441110041901e5004010302c1d104c00d08a596250100102d90940750f6485081050769a40001c00c0c5d1100d8001d18001c4255a01102043ca064000e25251100503070101c800fa60030214080765503078001c114042502ca201c1c102581c0d81e6114001070300e8030201980954a0001041078104c131103001407810714140c5848110034031a00e403070a10101c500039819103064409110003d200c280c0392904589000b00d012181080b81e0516118100c189148086000301454942020050900310303c3c14074201d01342d0728003d00704107091041085070719980d01002003c022400d414500850244507540d605045943c1c00100107002c1580c583c544070303020f9041a180c040200b41054900e81c3d0700c2d13006015110072080c4500d1112091859a102d061184040707150602d1a11b1381e80041c41d40c560002d0119611401094482540e10381c900000203103080c000c04121 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6623577 1250 6622327 6622339
    0x402300f1009051b0412030201050609010e07030504030c060c0309050f01060e0708070e09040303060501080a0b10050f040f030506010501020f0c090414010f06091b0305040b040210111006030c05 85
    0x144540c008801241030382c0508900080a5035104030245150644050010a0007030200d0002181000001c0400a09100f54006c0c0000e4132071805005a104085c000c018206403540300040b034941c841e81c05258407074001d20b0074a0724030300c0b41d40390b803401c8810f10401c01c030001ea01c0380d41801c14000100100342c0d03807586800081026030702d0810058001500500302d0003c00c030342070012400ca00c0c0301d10140003520f040100040c00506042c134000d002401c0364445d0754041441000020054041c0d4464940c9410000e03101c0c0e0410100e064044030035500c40342014140ba8020b0102082d064031a440750781c043e5100340e004090b42c4d410031002a19100014071032354219072001c002840c003034a4039204590001d40c084c5108a6901601c03600c20702400d09030610f1800c1603c1e1103800508941940c012040c6c4c0d003000000407032002502d420480545504441c05050303115a0404100107041c4106150310400306032901101d00c109901e401800e040c0c101800165a40c3c84800c140288500360b040d41c0700400341241c0b2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6624827 1250 6623577 6623581
    0x5040c140d0807020d020303070503031906090b030705040f02070f08030402030c03030711010c080f13051e011b08190807020105071b02100e03010603080c07050603010f0902090402300f 81
    0x42190b5449034035002402440707aa0030060840d00c3c1001500c0785550700c481038030f4503850408015181824a4452031940f2410f040d00000c04054074130410102d40c0014020340304180c01c1400f4000940f0052445100305a8208a0000850440e240c01c1300058170858000b03549080ca40101490141e10300940c41c46a0810464100040c1c40d038200344242041c04e0a010406d000b05081000d82809502e940c28001e4800142c03407400400c0c000e0104055440807140c03455054520541c0d074614041001c0c00601048010313100e5440019005814903440e4400c02440d407401d41141c1c807034331700c4000c0d251183c00071681c402d080c48041070b02809400c0c5d108010780303424076144403a05401c1882c500b0001010303004803411b043c08501140301e0514110280300c0035009201740303540c03403600003819484500c800400c1c1c010b100b00410f103803410320116412900680e000082032402c022030711000354010704000c1d0b03201d0760030841c130640c011050450089041144044024050b0b00a06400754113074000c040010032120402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6626077 1250 6624827 6624833
    0x140303041415041202090711070909020f0402040b1308030702010e090403020c03011a0301050a0b03030f0f0403050106030b0a0e0d050f07060905030309030c100902030d030e01090605040c140d 84
    0x82560215184050604030149224001c5081c0340002140910380c0c2c1c9000401182d5408401d1403030300750900c241c410a651360394540080b00c0c00400303c511420a81c025400802980e142508144145400104550325141e401c1c8001001c0f0381c02940100111107000c40c1c90402c40311101303080b800a010004c051403800c111903000800500c0c0c0c0240303542c42800d1881c045800d041c801c104c038440411015000304809615920030200d081c1051503d28429800c3c2400200150224018076520301030141c011403d006650b021440079410200208848950500c400030109009000310301c0118000c0d844d601e05030034104001405c0e650000c14842c0950321a0b082c0500c2c441d4041d00320341c404500715108e00c0d12690079141c0f200292040b41006004c911012041c010361080120042c10810b0911084921040c034544107641503661314100694540c0040950350b0400380241c100c070200035020b400004100d201d40e901c0350300b2614140c03030039204484682030a21031000c010500b11001082190300050f1050196 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6627327 1250 6626077 6626083
    0x2070501020c101101110c010b0303090a03080703110d0801050411031b030901060812091002070305060103080a0504080109030207050301050a091e050a080d020d05060a0312141603020609071403 85
    0x1e14154000ca1803005560700300c40c400c4c0e58032150a04058000e01c5500d15078054650590071040d20308005502c1c0918221582ca000400c40c4e0841c1c902801c2d450072240b4548426115401500003942401122081400c8250003440007801e2418652902c21417035041c08148400c88164444143c14641c04100b40b0055244401010f0f8215400c0e4006e20350341c0d07036031704095805018284e0040320684154a540c5242031034010241c181420143d840b10010000500104e03038440651002420b80c0d0807150042c804240c400c002005454100d043c120b281c00d036507280c0c2e282143c00c180c0d4142c0050f00100b10038404c1d8a028040c15400c01980031090044a0300c2d40c41707141021014040c2c807034a0410003003102c0100502070195a02c210780110703035513403070704000e2400351301035840380c0c44000c1d20520323010002e0601d1a004202805503030b00000381c1d0500700310780c407000d868410411038071499281040c402c1a45200441d402841124400d5028107070b2814651b0306103103400525002004403200344102c01e401c03a2400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6628577 1250 6627327 6627343
    0x9040312050406021308031b01020301030c03030516020a0605030403170606090d050a0206070803090d0801141003060b040602010f05090d050a050d020906031003030807030c021903020712060c08070207050102 91
    0x69400a0542c9691a10744000e03c506020201054400f040000d07101710040090100582000c61000b442c820b2900928201d20003400001c24140000000b40042480b030310107405110940d80c0e4004e80c1746150340010b00c00009940c0302c003000880020070001090341c00b02800004e034061030901092401c200c8006002d07401603290641c080c3e4080d050300000c1c00410003408100c1d580103031400e6074401050030a0030007a401112070307e030244030300f144200350315100f000554100c07290000e100311715800f0b41e0100031300c00032000200000c0540b2101c005c501540361200401c0104419000041c41d20b04a80c0c1d1003064410041c0a607846030407020001d0310040d040070072160200c80b549130041e07880a10010000081c00740f41700306904550080100416030005629010030340b4040c2e2901c42c1159560f141c12019500940c19850040c0c2040b0503d00c600062000e408031424447e0050b664040d4690b510701c8011049900c080c1d420545079403501c44019040640c040c1c101c101440904051401c000000c0e50364094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6629827 1250 6628577 6628607
    0x2010c0309211707050301080d02120a050c0109050105150f0103110d020703020304090905030d05010e060109030b07020c040e010203150901031a13200109060e03100e0c0303031003030806090403 85
    0x40340c40c0790721882d44034181e074002c0d000300ca0030240c0060900000c003e00c0e581090285003901e100e04071014030b0207800010512605088480d000c0c0c504480740c00211f41035000002c6c0207405640314840100040e40c00e008080c860520340d00310500540d048800c00450070300d020002818503180c42800195215480100c600c110039984001d0f035a01010f181c224590b00c69035202c0a02075242c03280700c0041020100041a49041655090004d070342c91b404140c143c480240d44582c040307404c041003000042d0021400e654445060f0041c0e40b44000090081425207a580070302c019640d50000c20411200d94520301d44440c40c10641c0c18600e65811655420604100c880da600d40c501450b030006400107002c84160952030b40d10280800282220b0001c501c85409408112030100f081e4243c0452101e10420711814000c100500504001c235031442b90400912680e04400d481d40a0f4000341b510a4404000450003423103100311a600361880d6050090101d003000d4181849150107400b480003103540042c0090925113 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6631077 1250 6629827 6629873
    0x1302090a0e07020c03061302091503030a0e030102040b070c03020a060e03060f0406110406020f010501080c1003020c0c150414030a030504060e01020a060c02030a0305090102040e0c070615030b0702010c0309 90
    0x12203003000c1c4d14000010700555858820a0100700c18910b40328a41101680b0035202c0944640782c40310a44000741158001d141c141d80184443e0000c0da02c2040d40144910001c2c00040c60503480c0c0ea0035170110703440f090301039920341c20540082045044c052078140040045192801c0501102d20029480321409820003d03900d400b04041801e0000c01d070f00565103406512030469a680e6128006511184480030b81e1910794070700301c00000c0c1c812000c990088a00d000801000b4040d010039003e070000c1d0010712180e1030a202d0700310111815211502c0c0c4121100e003914003545c1f0f4525010341c41285041a010705402504030200842c0060f40280c01e071426a211401c0c0203126152201c0100d240c2200c0001c081c10181c141b2604074445500070005004001c00744c0e6040c0030540c0d03a045d0090903480b451042680010441c0000b8a9181c0303510080d0070741c2c034891076000c110346400e842c0c0150301440310342044c4d8a00d182c00f001e00c4001602481018503a500c207080c248a605a2500c0d902c129100103c4c071241c03480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6632327 1250 6631077 6631081
    0x806040206090d0809040c080601030507020d0509040c021906150602070e060d020102010906290d0c03060b010207080109030906080604091a09030f0d060f050111030315041107050a021302090a0e 85
    0x8002d03c2605e200b0320b4040c0042149140641c4010b0480b20161501da0100345040d001c00c40591002c0303450710507888542c40f03061034403d56200307200081080d2041b41c1d0131400707014460391540c4031901056580342d01460000c41c01264038001210700784450f501c10004c0d90300c445020010000e030390004551204040742c111a00016a00051340900070601c0e00510b80b5107030140700c40505c03000b40c41c2090300918402c00311460034240000d102c0b204c040080701400300c101080c0100300185054105100484041c41030740c0c525540d40104c5400e656060310f0840104542c90420301c82d0303640c4185d003190b2107401102c060103d0b003840c0d00c800400700460202040d2400803403000440c00b55080084032001c48a03400306642d2003401c40400d00c000d100701d001e021400b104074030000541d90301c5a041c002400e00f40c0c4020b90b1440e2181500a409540d030840d203160869120142660340041e40c50140c60a01c0c061005400c16020f14410004910113024481c040244107101243c15a00c5000c0740c0401c0c3e500384825281c0366 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6633577 1250 6632327 6632333
    0x12070206041d04050106060201020408060f0a09051504051506100305040606050a0e01150806010203030a1e050c13060906020304061b06050108100c0203090d12090e0705040f0806040206090d 83
    0x2a2041e90800360b50611140e10141091015070703110341c032460207640200301003500d952049090384a644150451030380700b5004500760721500b035202504480e035103100007117603020f59071040d040148a09000e800b580d103020411090002c2402900c2c0b882c440c03541501d078603141040014171502c2c0b80c20061010150f45400140030400c15038080409402c0003016007094665404a0b501c500a00340110089036030302508890301d1600544600c0d000750f03c160090341c2135a0b5001c8050005140c1c1c60002d03a903071510070202600c03000c114400c050140c080c062000d550740842422140760303075800d544500c040200112041002c2940032040d681039071414a0005640c15962002d281407022428003e00340c0b5140c4000010800741c0003450b14900c02d070f00c22041c4074203120722400740d07180e005405004c1d801541c1c2503058400240481c000ca601e0780ca0301d0030061016620340100d844070381d01c1100c103a03000c51000039080c0101030340b1000c0c0c800207180010040c1141c0c07809034080394642c002d07042d809000d024590118810 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6634827 1250 6633577 6633589
    0x6060f0807050a0b03130f0302010204030807060501050108071809020903100f0209010906051c02030402180a150905010f050d02150a08070905060a02071a070c0b040911030702120702 80
    0x10a44850a80062512040200c1d100d0401d4418944200030003680010481c03001015241300303003114000103002c0202515031400303941050070100c0441d5420000800028510b40242056a02842c0c0010381503051030000741c0309030347c050708081c14884840c0310a003040c028044102c055851906c0c001da252a42e420110785400c846003a242d440070b0a003c115030801c0384036030140101c40000d90b20040b03940c0e17549200b500c080c82070301401f001c52000360002d041c2d2500036400840c0c0244c03020300350050004502c0c0004021220640e0100186a25000103044a449030000d58001d040b00c8181044103501d01071450350440d990340710302e6000c0c0700c1020080c4299a9078018408000144180c12550740c840c0030380041c81c4030400c451410114146003c08105401c106003552803488494005040c103509140b003500d030060000c05640082c0804101c00f80004480c006d1080c0101380c4d140081d230711182010f2807002a240402c0303403841a01014010865016130002e000107001081c03040c11541e80e207580c008219 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6636077 1250 6634827 6634829
    0x40b090402150904090c0b0703031803050a05070305040902070b040b070e0607020f03030403020d06050106120605060304171e18030d02060115020106030605151203041202011101090b04120909050f0109090606 91
    0x202c02040c0070000a007c20541c00280601031280e6002c0009424000d030303100c00c1042010001d400a581407040c0c54102e40204c0c01411440e010b0b0a0560a155136152000142e0b8010181251500c075544240010044011000c90300505941041d0302c40310118000703d680c0740954040a840703600c28103c058082d0b1020710440340959005007500210000038140a40600000e2050800140c843c0c885401417a10502c12036099070b000034159407440c1c480e51280313084044c103404c0e20040d29104201c548109080c25449550b1042c104149617111121901030b0149100714044103402504150b04407510309a0220710345056030032540040c40c112980d00e60032401084203030070060030149840c041c400040ea8a042d0f00c40380c82c1c01252503103c0900152401501c0e070140f4801c45040016449100c0010342c06118240c074561900c0000203042c6259403540c10305034a0664081d00e01241c490002d08004c0e500c66955005004190014411400c0c10007850030040e030144500b03a6141d41e91081c8030100589900024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6637327 1250 6636077 6636083
    0x304140d0206090904030203030403020c060403120302090307050604090903020717070509090307050d0c12090303080105011d04060b031909020906010f020f0706050c250b0a0c0c14040b09040215090409 88
    0x1c04c3ca45828500a5a80d9009135415000340c071801c1000e01207440e200d022103066a501040c903c8071601e103a82c0550194111303803101a41801007140104a54650b07002400007868011000b0883c212a414081e00f0810150000c004030b0705a42881c20040800142072402c4410035105404943e41340a0014298000d0a200800c203000760f0310640d00d00c0780c0c4013454417801c40c01620400c0382d002c48800c05a40744412440001d010170134100c0100f0140d0b024881d402c01c0c001d130030b20f000007102003e0400a0100e445039000040c1c0100d000c01404040c030f00c81002c000740b5080c0600200181c81103a0001401c41c680149054100103220700540a114403d002d0304c242140c1c100221381c1380b941c664001804c250050703106050301e882520750036900302c800c5254120361100c55031071003000c103030410300b800901d58055100082030140780346041c0002070a0380c4104c4020714a450704c800c4060f0003001080143c0758002c40c0c0600c280565024040560354500c1400070a50f005640d1940c0c62001c507001c100a0b11841e0405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6638577 1250 6637327 6637339
    0x60a0b0703050706060f090605060309071a070804030b01090b0d0506010902031506070303050f10060e060a05040b0408010501080d0c03020c04240603020304050105010e010303080a0504062a110304140d020609 91
    0x40701c041003486c1c0410f440c1da0300410302040751554140200e90104036000102da600c442c90802060b00d0140c000107402510710398292800c01c85445070000d5900c0750744211340c2011042d004005c43c2c840c1e481820561001100c0204805956403240ca96400301070184200c118bd0000111f41e858007050350001c00740e42c000d0301c00c6844200506000e80246002c840340144911050f0000d13241142d10079a0364103640c0c607600c07851113180421040c081c0396000303904981e0034000d0030040440c001c21200013400082a0310000441c203581082240b50400c44c08413200b60034170800b1008000005d402240003103031000c0641d00010041e1000364240e1480c028401e105c210350724034403000b003078069041d00150f2045005000910031642c0c0c400b081c0c02e0a00091102034002881c84001c102711200780d411007900300c0c0c0100004103601901054440b071a00c401b0703400f0388040602040c0442c03600d4005079403040e103c00302c2c4051400c107850488640507503907803030002910845096495400b199500030603680b07510300c09045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6639827 1250 6638577 6638579
    0x409060603050307020f06090a0b090d0605010e0417070308010608070905100903030e0603090307030c060905072d05010f050901030e01050c0c150405151806091014060a0b070305070606 81
    0x20585a0381301c0761059000d400403809620450030560210b400078000686443e131540d1805851618680001c03c104e6400400100802c011036498002c0300e000e01010441440309007000d1130b20510500d5800c1800050392010300100300480d130400c403040e0440d091070600b07006c0343e0313205e0385c0c00c44001009412040d0300c0942540c150340801c0c0d004a016050320311a850b120580a160004c202c001e00003240c000c02c0c02e520404c000000644203441c61480e280c4100c07404110628281d0390305040c010590000c0b00c90394401325401030f007090b603100c0c00e80d820001440c1d07106610381010002804032040d055003d051050015141c00c1692180d07202e22401300030700000300804d04148680c01c4440e40288460a040c2c494405000c0c0c4126088541a005560010007081c0100d0400c1804004c0c00b070041502c40110304101c4404507400c0280070040c49a40c106000d82100c03d00001040304075138081540044c9410b44508104080d1590b1141c0b20988001c0074209132561440e01d0b08503080d2007840b000800d45420040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 6641077 1250 6639827 6639833
    0x10c02031e031306030e0304060e060c0105011404050705070c05012304080303060411040605070201120603080705010506090106020a020a050402030c041809051009030e0405090106050411030603071703040b090409060603 96
    0xe40a0344a0300f000d90070410750742d400d003203060b111038010840c010f4008000800000c3c0c00b0303101d90601924044d010a0034000785100311400c541c826800203407000d107200f042c09141c3c90203104499020350b203410301d9030401855458100d4102e540e40202d60520011000601107019040082e05264201500565945483d1001d154403a0420b46240d80983c0c1000700142210841d038007950165281540e49900304402600112181c1d42804c060304c1c001c0396140400302c04507901a0003008801e01884c0041603a08010091090700001684100d0854000c65095001a0b840010000843d0022240541c50b5108c0c8030342c22003584100c0e03211b84a101d00481c807400c2c00b246035400048000d4004c401b51042988144090425a000000000c000400c1019907070781c0c5103041e5100c2c0e50843d400c0c0c0000211162650080342c126075030340009012001d8048104020ba01d0200000405401007041d01601e14151003502644c0e80a40c0c010084080d1001c11511660b0700d4540c0901101d503003042060002d5681d0341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 6642327 1250 6641077 6641083
    0x109030306050901050301230c090901030305090a050402041a0c03040819060c080606030402060d090c060504030501050112170703020111040306050106020c0f0a06030b010201090213020a020709110702010c02031e 93
    0x110407603000e8500f5200004030f900e4107101302110444801c0d03540310b0074040414101c510500043c04101300036400d2104610644944607007501940c440d44030141d66100f880d00700482c94409510440c404ca00401c0144114810680e10240720024054881c0c0c540307464212517070560207180c00c0b114091142c00200b401d144800c032181c03009180a05070800100a54010444e46440111119904500200085001818014000c2c1031540c00544001b0318994690303100f00c10000c0d141c1c03014001034030105050041c04400c1c030440307004207000c40d62108a444160751302255500002085079070b03003030041503100900d0700039004841c00c550032034801580e0310340300d00e81903000345820300030000144144d0641c0300707503802c0000114290b41c03030007040d4440c0b45250440c00c40141c2504c0039558115501d03030540034010b885415000c0c03a40c9010307560140c2c8400d035161000f8a00584c90384403601482c1003001e2591010200c00c03c84d04115020329007402c91581c1800886e1400c0d00d80c0700c46c8100c0100c02150034003940d03004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 6643577 1250 6642327 6642329
    0x302030c04020a09080d091a0c070501110f060f0a0c0206010807030b060a0801050a0f0605010206070e060309070b032401050703050708090607050f1b01180b09030a14010608010c0518040b030c030109030306 90
    0xc501c01c1c1800c0d40d1402c8120740c09d0061030300782c40c1182d000c0340d0140715075070260000e80b0702800c41e0310455181d82c1300e12110030b040120a5460782509080d500070712001d04614080c44000034240c2c4001d00c1d1075807501103420340d107070441e1101406080e9504003103003003500c50350b1a56000d004440000d002c20f060034800440105488111151281e03e0107201086035032010031a54000c002680d1603c032005510b400300003c80e0700181010315a4030441c01c00203208200070010b10700c14080043c1041c4a880c071140001c40f094009a00d0340e041040c01c00400f00000d4000e02a10032441e008484103454600c0c2e1030100702c05118290b000392603840b6101c885003250000041c040c0c0b00c090142000200c41840100669401c2d03c004040d204006201d00280300c21045000074081c20207001713044507000c000c0c60300d4880075441002c1d2002c2099441d02c2040c4148032003402805080d04051801510300790382054403c058004040c0200d1040307403141c1030351429940412800055040040080010041c02d1501030300400d91 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 6644827 1250 6643577 6643589
    0xf080403050a0312090b041212110d1103010e010303050c0a0c0905090c04020306100806030a02151207090302010c06050703060b0c0c03060619050108040c0803040306020904150302030c04020a09080d09 88
    0x240c40105501140700b4040c2c45c0007954070290159040d2a02d0399840c0795030070342e03208003400c210543c98a150748019500800600c01d04104465544080510a07076058600d20b0600215032201000100400c114460070141140c0d014039040b51507011407040c843c20701500007800b8151201d40c40c07001c10000040e510003030240d00c4079030850703002005840c1400142d0000700e0b01968000001c8040c1c070f40e0710340a10041036000c40d00030103480d421100c035400141c250b61911905a0042c1002c2070210002100480c455000200c500300391806602d03507400286980046080102807503241d4012400c0c8900075003040010304000c086080d1100340886015644000e451440d61180c410701001c00c0041c2049090307145140405815400c1040c20320b001510042c1c4040c00481c1e20301e091100010305490f080c03000d000618442d000242c0d460049004020945000c0350408148580000d010801a903001511900001d0305903000768496240b0f0301d055896613a5580002000c7c0585c9010700c00c0c190b405641e01c1c080e230344 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 6646077 1250 6644827 6644837
    0x705070f0534050a090902040b030a0303020a020607030905030702060f0909040809011202090904080307050f0c01060501032301180605030a11100503010b0904050604180302010605010e030f07050d0f080403050a03 93
    0x2103451429000d020503c601c3e41c00c800d03042c5090041c0ea03401d4001c200c2a03070020b400886c0c2d0304050b42c0032034540001e04e0020380c002030b8081003803502c0f50760502c0b4494115800d0324043c030423481d040e00c5098480c41145002440344600181c081d9001c10b0b0402502c1600d90020300a20f603501d410f0610042d10b500c85140c0c1030029030010f5400003d031403180300b5600c0d520000340c9200034030340d10384d82d80c1c07800d661018050701d0130b1108c144554024424900018a003610200c00003191140c5018005002c1d104004140844c002d101ea10310b890b1001104642411074261225059065030240716000040c200340d04007640500898050b401400000b60344c8603061101511407100c00c0074144405c4400e40070a0148150b50f66081084442514154210541140340140009000589610240c0407038000315011000360751075000c100a01c2d0303007154041c1c0c82c00034160081c110b5421126030749900c800107030042e40e1148442c0d12840d01032200b00481014a99448015583d0b103644078148555180c16850088000030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 6647327 1250 6646077 6646153
    0x40c030c0b0f0403020d020604030209010b0d060902040506090904020a12030503090601060804030203040b030613020423010509030316110307080f011118010507020d0501020d060302130606080705070f05 89
    0x51100703040301c0c0740c0c1c95080b41e0075003007904541c20084140c03030401059074050414440400541c0d41c04803114000c00b000103125035034a040300c1040c010746800c1d50080764070500c180020031182d2690011034440480441c2d01d80096665480000c2c02d100c100e400c40c54058280d8000303001096040001140143d41d1003085403016a6654030488580b0000c49005005800500041180c0d6041002850308503400502119503000c4050922040340c00c0380e80325201281c50300c0303841d0016074003c403011101201d003860658600612600803d0b96403103071400340140018036803a42801d00403405e1600a1040b001401c1d161501d5681140c5130365010080a05000e43d480c20031751041c10003509080b503094000031404a18407507030604c01520282c000100076a003102000d400b900024000788020200c818000100103945030035030051280c950320b80c2043d811041d00d000024420340b9000550305a01400c2450070690b500614580400d121700e03c150300400911891a02c480902205011800c2c1286102e0290b001c1c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 6648577 1250 6647327 6647339
    0x70c08061b0706020f0d090201030f140c0a090504181e0506040803060303070f080307020c0402040803030105060913090b0402090702010c120c02030c0f06010302090f010b04151205040c030c 83
    0x5140c16240400107601501c070309481581c08a01400030b1034010342005060800344100146242d02498151100360303a0b841c003460440da01841201020b040480c010421150360f00301c540088030000e01807c54170b03070001c0f071000e9466114285d02c1c40504000390043c0080381107058400e00d030012045040321000c48503900c00030300c0a5003041c0780210b50f030058000c100759119a00e0300c2c5081c2d88080c101a800d800300f000f00c0d10101c2d101c01203801c80a07100e80581645c9140401e030003810100e6130b40f0f02034451801004200030310702001050343c3c150751048402075503075203064000400043c0e519020a0100c0e00b00100101841118420f80d445603000303441580896031585012802c035001996010041402881d007401c409507143c0c03041441046034012245004484030700c00740307408914a47c01c2007942c4010014411410911300103034200c00600941000b550404060980c980603d01824001b01180000c0c1c66003107100f070a41c841411000b0300200480e081071b082c0407503648190702042e0f0b01003003050800035103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 6649827 1250 6648577 6648583
    0x5010506070b22050f060a0e0102090a0302040c20010e060c070203030a0f02070f080102090a0f050d0605070507020d051c050306012f160305070909080406080406140705070c08 77
    0x1040d50100b1003545983d500f2207048114240c16114000d062090700c07028001440803c017a400b07041d030900042c4074a00c5c01e0039084040c2c87c6d081a2a810070b1740144480c1690b6210300145a066135412035000c21581091030703044400c0c0c015001c0d00d20044583c1d026000d02c0c1c030810b5210003091002070b800d50358140e48220381c001091041d030f0b00007901a40200f1158000302e2003010006101c0039688152039a01e07940b008a2059000d0b260844074141e50300082900301841c200103058000c02206021000661902001036024100e010018040540b00c60018003480d00c10310803502d58650042a160100b40a4100315684601140207003200000106203052024020015684503450580d02c03821000000000e2107802050030a41c1401d4990701c0c22420130781c650600c0340b01c2003c0560600c0c0207440385981003a030720b08112039100380b1119141c00342074004245c0940071a402e0f40d04600700001103031034a00d0190000d00840041084003c0143e090102540d8480001d26049000c1d00040a0f500e40f00c0c07641e151 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 6651077 1250 6649827 6649837
    0x7060305070c021c0b150901140109030305030a021e030106080708060f0d03030f020c010507021204080613150603030f09080309030d1b0b10030b0a050f0402280905040605010506 78
    0x1021840302c988000c0189040c0c0400240340c01c426030701c2030000559545401d081001540d00c0711101580000214540c1040040e6a0040030904240d0503680d84400010b4030450f101d0001a00f0050000001015609035404991002114a222003000c0b00c0340c0c031003802075400c28016640001c08003804201075038070902826005200c010322100c94a034002c8100203c000040d41e0440030b0588038100489017603a00e201401d14104d01000200300e078030307000d140241803101c550ba801c5003141007400180054400050301640c05407070b0b050001c042c00c1080c01c11011300341d84068074101160805a000c420140d10021001d101900c64541d0000c440d114420541c5900400c0c100320380540c0310701c03071480c0e14074030034210b00c01c5090800300354121b4440151291100b040084030070405615009400704100681000510350050403c40200558144440c0391034100501510192140c0701e04031018100e44403000800c41140240782581e40c0e45940ea581c100d01801c822a01521650325280000515080001c00c0b14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 6652327 1250 6651077 6651091
    0x9050f040c06030b030c040509010204060201050601020613030305150402030a15090908190302040f080109170a0c020906011e02061801020703090303050c030706020a0503090c01140d0e01020f030403090807060305 93
    0x402142c20300408030000d1981d2007600f5814440c412001c0071646841c416907010f0b0a100001680e04c0b03082c07600290946801410083c119403291041081c1c01048604030409030f64503160100b65070b01c4018400b00700c411405c0d0202d80c071510020502180400c5035010758190075029000c001d2182c1e85004440890700c00350b001510000382001410f80f80014541c40d50745002550034014140760b11000c0b441d01448031034000002e2695a441c2081c1445260300440c2071080105c101545028402030000309001c050b594003e0094140201140c1c2d01d80c014224500714100012070300001096062000b03507143c0702a6074580c02a0f0042c120700c2450f10b01070080721001c80c0c0540302c01c900f480c515074040700c19a2180503000d0b0f460105000440014406000074104c0b80030660b1034a40b682000d00c03040341001030700303c00e030b0703041c0100c240902c808102040140d60070300e400d92000044400004107604d000e4454101e03002011840003080100309038008a00005413030152046940305919503806030201d542c2a03842d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 6653577 1250 6652327 6652343
    0x203090c0306071103071410090813090605130b0f1c0b01120c120305040b0a0906080907030203060106050d0f09080403050601060f02030301030f030c0b040b150d1a180303010306050109050f04 84
    0x10440000b007c800c201001011945400000148142100c00a80045800707110000d09082004c6022003030101030701428030300700103417864080023034200f034200c4010440380707522000c03101c4141e940c04441204801020b040344000e51080c940131740741040030301c608941071b803407050010035140851a01031802c154010340c0410340e2420010310300000107c03140e049080103130070840030604040c0280607148000c134039200e50010718184075015044210040500344a988011420005a5030019a1394110f424a04240d130b82d440140a505024020b10015580b903070341425010820801c0e014000c0c41200d000301d003a10103e036242c0f00c0c00c84884180e11400300041e0300500052022030a00d03150079038400d110b8140b04000c0c05007640e0324419074004030740c01e9038084001010400490350482c0ba03c0010a0211264200c04513203a0b5210090070080e8649a82e01040100080c4680c9090746081442c51820040f0394603980c0d81c3c030704500508401d0007203207082030800c0e0200301121226542c2c240207980c80018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 6654683 1106 6653577 6653587
    0x41503060603031d0d0201021f0207080403080408060f041a130b0709050406060e0603130f08071401060905010501050702100909020a03020403020f030307080d0513060203090c0306071103 82
    0xc4c07580111a90303800d940041c1e901240e03000041d085009201c4203401e40103110402030003400c000400701800002e0110034800e0040c068821140c80394203c4403113540320820f03124080e8096134002e000301d00e540c040c180b2030148080041e6101c1c1c035020003442c5c0a42c4980700d06109010035134003400031445080050210742041e005100c041e088901b042c010040055010929500c401040e128061984010309010000c110030a250515040000241c80d0710503410300390500c142e9500500155860b04000060039181809102d040381d40503110070323081145903002c4c0302d807081e00f5040040800061a80c0031801446e113101a00c21031005960040e1038504520510903a99043c04070f8511961040c0803420004001c0421540e0310200120003040c1a1500601c1d030000c0c0500000081a0034004800c02c04c1900c0001110415010700701d044a215881d01c1c50140d45001200242e19a5034000b004 = true := by decide +kernel

theorem cover : BRFrame.Cov 6474827 6654683 := by
  have h0 := BRFrame.cov_init 6474827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6474827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 6474827 ≤ n) (h2 : n < 6654683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
